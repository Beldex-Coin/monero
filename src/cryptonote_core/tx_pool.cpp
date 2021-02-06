// Copyright (c) 2014-2019, The Monero Project
// Copyright (c)      2018, The Beldex Project
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without modification, are
// permitted provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this list of
//    conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright notice, this list
//    of conditions and the following disclaimer in the documentation and/or other
//    materials provided with the distribution.
//
// 3. Neither the name of the copyright holder nor the names of its contributors may be
//    used to endorse or promote products derived from this software without specific
//    prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
// THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
// STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
// THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// Parts of this file are originally copyright (c) 2012-2013 The Cryptonote developers

#include <algorithm>
#include <boost/filesystem.hpp>
#include <unordered_set>
#include <vector>

#include "tx_pool.h"
#include "cryptonote_tx_utils.h"
#include "cryptonote_basic/cryptonote_boost_serialization.h"
#include "cryptonote_core/master_node_list.h"
#include "cryptonote_config.h"
#include "blockchain.h"
#include "blockchain_db/blockchain_db.h"
#include "common/boost_serialization_helper.h"
#include "int-util.h"
#include "misc_language.h"
#include "warnings.h"
#include "common/perf_timer.h"
#include "crypto/hash.h"

#undef BELDEX_DEFAULT_LOG_CATEGORY
#define BELDEX_DEFAULT_LOG_CATEGORY "txpool"

DISABLE_VS_WARNINGS(4244 4345 4503) //'boost::foreach_detail_::or_' : decorated name length exceeded, name was truncated

using namespace crypto;

namespace cryptonote
{
  namespace
  {
    //TODO: constants such as these should at least be in the header,
    //      but probably somewhere more accessible to the rest of the
    //      codebase.  As it stands, it is at best nontrivial to test
    //      whether or not changing these parameters (or adding new)
    //      will work correctly.
    time_t const MIN_RELAY_TIME = (60 * 5); // only start re-relaying transactions after that many seconds
    time_t const MAX_RELAY_TIME = (60 * 60 * 4); // at most that many seconds between resends
    float const ACCEPT_THRESHOLD = 1.0f;

    // a kind of increasing backoff within min/max bounds
    uint64_t get_relay_delay(time_t now, time_t received)
    {
      time_t d = (now - received + MIN_RELAY_TIME) / MIN_RELAY_TIME * MIN_RELAY_TIME;
      if (d > MAX_RELAY_TIME)
        d = MAX_RELAY_TIME;
      return d;
    }

    uint64_t template_accept_threshold(uint64_t amount)
    {
      // XXX: multiplying by ACCEPT_THRESHOLD here was removed because of a need
      // to accept 0 fee transactions correctly. the cast to float / double and
      // back again was causing issues estimating the effect of a zero fee tx
      return amount;
    }

    uint64_t get_transaction_weight_limit(uint8_t version)
    {
      // from v10, bulletproofs, limit a tx to 50% of the minimum block weight
      if (version >= network_version_10_bulletproofs)
        return get_min_block_weight(version) / 2 - CRYPTONOTE_COINBASE_BLOB_RESERVED_SIZE;
      else
        return get_min_block_weight(version) - CRYPTONOTE_COINBASE_BLOB_RESERVED_SIZE;
    }

    // This class is meant to create a batch when none currently exists.
    // If a batch exists, it can't be from another thread, since we can
    // only be called with the txpool lock taken, and it is held during
    // the whole prepare/handle/cleanup incoming block sequence.
    class LockedTXN {
    public:
      LockedTXN(Blockchain &b): m_blockchain(b), m_batch(false), m_active(false) {
        m_batch = m_blockchain.get_db().batch_start();
        m_active = true;
      }
      void commit() { try { if (m_batch && m_active) { m_blockchain.get_db().batch_stop(); m_active = false; } } catch (const std::exception &e) { MWARNING("LockedTXN::commit filtering exception: " << e.what()); } }
      void abort() { try { if (m_batch && m_active) { m_blockchain.get_db().batch_abort(); m_active = false; } } catch (const std::exception &e) { MWARNING("LockedTXN::abort filtering exception: " << e.what()); } }
      ~LockedTXN() { this->abort(); }
    private:
      Blockchain &m_blockchain;
      bool m_batch;
      bool m_active;
    };
  }
  //---------------------------------------------------------------------------------
  //---------------------------------------------------------------------------------
  tx_memory_pool::tx_memory_pool(Blockchain& bchs): m_blockchain(bchs), m_txpool_max_weight(DEFAULT_TXPOOL_MAX_WEIGHT), m_txpool_weight(0), m_cookie(0)
  {

  }
  //---------------------------------------------------------------------------------
  bool tx_memory_pool::have_duplicated_non_standard_tx(transaction const &tx, uint8_t hard_fork_version, master_nodes::master_node_list const &master_node_list) const
  {
    if (tx.type == txtype::standard)
      return false;

    if (tx.type == txtype::state_change)
    {
      tx_extra_master_node_state_change state_change;
      if (!get_master_node_state_change_from_tx_extra(tx.extra, state_change, hard_fork_version))
      {
        MERROR("Could not get master node state change from tx: " << get_transaction_hash(tx) << ", possibly corrupt tx in your blockchain, rejecting malformed state change");
        return false;
      }

      crypto::public_key master_node_to_change;
      auto const quorum_type               = master_nodes::quorum_type::obligations;
      auto const quorum_group              = master_nodes::quorum_group::worker;

      // NOTE: We can fail to resolve a public key if we are popping blocks greater than the number of quorums we store.
      bool const can_resolve_quorum_pubkey = master_node_list.get_quorum_pubkey(quorum_type,
                                                                                 quorum_group,
                                                                                 state_change.block_height,
                                                                                 state_change.master_node_index,
                                                                                 master_node_to_change);

      std::vector<transaction> pool_txs;
      get_transactions(pool_txs);
      for (const transaction& pool_tx : pool_txs)
      {
        if (pool_tx.type != txtype::state_change)
          continue;

        tx_extra_master_node_state_change pool_tx_state_change;
        if (!get_master_node_state_change_from_tx_extra(pool_tx.extra, pool_tx_state_change, hard_fork_version))
        {
          MERROR("Could not get master node state change from tx: " << get_transaction_hash(pool_tx) << ", possibly corrupt tx in the pool");
          continue;
        }

        if (hard_fork_version >= cryptonote::network_version_13_checkpointing)
        {
          crypto::public_key master_node_to_change_in_the_pool;
          bool same_master_node = false;
          if (can_resolve_quorum_pubkey && master_node_list.get_quorum_pubkey(quorum_type, quorum_group, pool_tx_state_change.block_height, pool_tx_state_change.master_node_index, master_node_to_change_in_the_pool))
          {
            same_master_node = (master_node_to_change == master_node_to_change_in_the_pool);
          }
          else
          {
            same_master_node = (state_change == pool_tx_state_change);
          }

          if (same_master_node && pool_tx_state_change.state == state_change.state)
            return true;
        }
        else
        {
          if (state_change == pool_tx_state_change)
            return true;
        }
      }
    }
    else if (tx.type == txtype::key_image_unlock)
    {
      tx_extra_tx_key_image_unlock unlock;
      if (!cryptonote::get_tx_key_image_unlock_from_tx_extra(tx.extra, unlock))
      {
        MERROR("Could not get key image unlock from tx: " << get_transaction_hash(tx) << ", tx to add is possibly invalid, rejecting");
        return true;
      }

      std::vector<transaction> pool_txs;
      get_transactions(pool_txs);
      for (const transaction& pool_tx : pool_txs)
      {
        if (pool_tx.type != tx.type)
          continue;

        tx_extra_tx_key_image_unlock pool_unlock;
        if (!cryptonote::get_tx_key_image_unlock_from_tx_extra(pool_tx.extra, pool_unlock))
        {
          MERROR("Could not get key image unlock from tx: " << get_transaction_hash(tx) << ", possibly corrupt tx in the pool");
          return true;
        }

        if (unlock == pool_unlock)
        {
          LOG_PRINT_L1("New TX: " << get_transaction_hash(tx) << ", has TX: " << get_transaction_hash(pool_tx) << " from the pool that is requesting to unlock the same key image already.");
          return true;
        }
      }

    }
    else
    {
      // NOTE(beldex): This is a developer error. If we come across this in production, be conservative and just reject
      MERROR("Unrecognised transaction type: " << tx.type << " for tx: " <<  get_transaction_hash(tx));
      return true;
    }

    return false;
  }
  //---------------------------------------------------------------------------------
  bool tx_memory_pool::add_tx(transaction &tx, /*const crypto::hash& tx_prefix_hash,*/ const crypto::hash &id, const cryptonote::blobdata &blob, size_t tx_weight, tx_verification_context& tvc, bool kept_by_block, bool relayed, bool do_not_relay, uint8_t version, const master_nodes::master_node_list &master_node_list)
  {
    // this should already be called with that lock, but let's make it explicit for clarity
    CRITICAL_REGION_LOCAL(m_transactions_lock);

    PERF_TIMER(add_tx);
    if (tx.version == txversion::v0)
    {
      // v0 never accepted
      LOG_PRINT_L1("transaction version 0 is invalid");
      tvc.m_verifivation_failed = true;
      return false;
    }

    // we do not accept transactions that timed out before, unless they're
    // kept_by_block
    if (!kept_by_block && m_timed_out_transactions.find(id) != m_timed_out_transactions.end())
    {
      // not clear if we should set that, since verifivation (sic) did not fail before, since
      // the tx was accepted before timing out.
      tvc.m_verifivation_failed = true;
      return false;
    }

    if(!check_inputs_types_supported(tx))
    {
      tvc.m_verifivation_failed = true;
      tvc.m_invalid_input = true;
      return false;
    }

    // fee per kilobyte, size rounded up.
    uint64_t fee;

    if (tx.version == txversion::v1)
    {
      uint64_t inputs_amount = 0;
      if(!get_inputs_money_amount(tx, inputs_amount))
      {
        tvc.m_verifivation_failed = true;
        return false;
      }

      uint64_t outputs_amount = get_outs_money_amount(tx);
      if(outputs_amount > inputs_amount)
      {
        LOG_PRINT_L1("transaction use more money than it has: use " << print_money(outputs_amount) << ", have " << print_money(inputs_amount));
        tvc.m_verifivation_failed = true;
        tvc.m_overspend = true;
        return false;
      }
      else if(outputs_amount == inputs_amount)
      {
        LOG_PRINT_L1("transaction fee is zero: outputs_amount == inputs_amount, rejecting.");
        tvc.m_verifivation_failed = true;
        tvc.m_fee_too_low = true;
        return false;
      }

      fee = inputs_amount - outputs_amount;
    }
    else
    {
      fee = tx.rct_signatures.txnFee;
    }

    if (!kept_by_block && tx.type == txtype::standard && !m_blockchain.check_fee(tx_weight, fee))
    {
      tvc.m_verifivation_failed = true;
      tvc.m_fee_too_low = true;
      return false;
    }

    size_t tx_weight_limit = get_transaction_weight_limit(version);
    if ((!kept_by_block || version >= HF_VERSION_PER_BYTE_FEE) && tx_weight > tx_weight_limit)
    {
      LOG_PRINT_L1("transaction is too heavy: " << tx_weight << " bytes, maximum weight: " << tx_weight_limit);
      tvc.m_verifivation_failed = true;
      tvc.m_too_big = true;
      return false;
    }

    // if the transaction came from a block popped from the chain,
    // don't check if we have its key images as spent.
    // TODO: Investigate why not?
    if(!kept_by_block)
    {
      if(have_tx_keyimges_as_spent(tx))
      {
        mark_double_spend(tx);
        LOG_PRINT_L1("Transaction with id= "<< id << " used already spent key images");
        tvc.m_verifivation_failed = true;
        tvc.m_double_spend = true;
        return false;
      }
      if (have_duplicated_non_standard_tx(tx, version, master_node_list))
      {
        mark_double_spend(tx);
        LOG_PRINT_L1("Transaction with id= "<< id << " already has a duplicate tx for height");
        tvc.m_verifivation_failed = true;
        tvc.m_double_spend = true;
        return false;
      }
    }

    if (!m_blockchain.check_tx_outputs(tx, tvc))
    {
      LOG_PRINT_L1("Transaction with id= "<< id << " has at least one invalid output");
      tvc.m_verifivation_failed = true;
      tvc.m_invalid_output = true;
      return false;
    }

    // assume failure during verification steps until success is certain
    tvc.m_verifivation_failed = true;

    time_t receive_time = time(nullptr);

    crypto::hash max_used_block_id = null_hash;
    uint64_t max_used_block_height = 0;
    cryptonote::txpool_tx_meta_t meta;
    bool ch_inp_res = check_tx_inputs([&tx]()->cryptonote::transaction&{ return tx; }, id, max_used_block_height, max_used_block_id, tvc, kept_by_block);
    const bool non_standard_tx = (tx.type != txtype::standard);
    if(!ch_inp_res)
    {
      // if the transaction was valid before (kept_by_block), then it
      // may become valid again, so ignore the failed inputs check.
      if(kept_by_block)
      {
        meta.weight = tx_weight;
        meta.fee = fee;
        meta.max_used_block_id = null_hash;
        meta.max_used_block_height = 0;
        meta.last_failed_height = 0;
        meta.last_failed_id = null_hash;
        meta.kept_by_block = kept_by_block;
        meta.receive_time = receive_time;
        meta.last_relayed_time = time(NULL);
        meta.relayed = relayed;
        meta.do_not_relay = do_not_relay;
        meta.double_spend_seen = (have_tx_keyimges_as_spent(tx) || have_duplicated_non_standard_tx(tx, version, master_node_list));
        meta.bf_padding = 0;
        memset(meta.padding, 0, sizeof(meta.padding));
        try
        {
          m_parsed_tx_cache.insert(std::make_pair(id, tx));
          CRITICAL_REGION_LOCAL1(m_blockchain);
          LockedTXN lock(m_blockchain);
          m_blockchain.add_txpool_tx(id, blob, meta);
          if (!insert_key_images(tx, id, kept_by_block))
            return false;
          m_txs_by_fee_and_receive_time.emplace(std::tuple<bool, double, std::time_t>(non_standard_tx, fee / (double)tx_weight, receive_time), id);
          lock.commit();
        }
        catch (const std::exception &e)
        {
          MERROR("transaction already exists at inserting in memory pool: " << e.what());
          return false;
        }
        tvc.m_verifivation_impossible = true;
        tvc.m_added_to_pool = true;
      }else
      {
        LOG_PRINT_L1("tx used wrong inputs, rejected");
        tvc.m_verifivation_failed = true;
        tvc.m_invalid_input = true;
        return false;
      }
    }else
    {
      //update transactions container
      meta.weight = tx