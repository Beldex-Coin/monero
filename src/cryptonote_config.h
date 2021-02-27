// Copyright (c) 2014-2019, The Monero Project
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

#pragma once

#include <stdexcept>
#include <string>
#include <string_view>
#include <boost/uuid/uuid.hpp>
#include <stdexcept>
#include <chrono>
#include <array>
#include <ratio>

using namespace std::literals;

#define CRYPTONOTE_MAX_BLOCK_NUMBER                     500000000
#define CRYPTONOTE_MAX_TX_SIZE                          1000000
#define CRYPTONOTE_MAX_TX_PER_BLOCK                     0x10000000
#define CRYPTONOTE_PUBLIC_ADDRESS_TEXTBLOB_VER          0
#define CRYPTONOTE_MINED_MONEY_UNLOCK_WINDOW            60
#define CURRENT_BLOCK_MAJOR_VERSION                     8
#define CURRENT_BLOCK_MINOR_VERSION                     8
#define CRYPTONOTE_BLOCK_FUTURE_TIME_LIMIT_V2           60*10
#define CRYPTONOTE_DEFAULT_TX_SPENDABLE_AGE             10
#define CRYPTONOTE_DEFAULT_TX_MIXIN                     9

#define STAKING_REQUIREMENT_LOCK_BLOCKS_EXCESS          20
#define STAKING_PORTIONS                                UINT64_C(0xfffffffffffffffc)
#define MAX_NUMBER_OF_CONTRIBUTORS                      4
#define MIN_PORTIONS                                    (STAKING_PORTIONS / MAX_NUMBER_OF_CONTRIBUTORS)

static_assert(STAKING_PORTIONS % 12 == 0, "Use a multiple of twelve, so that it divides evenly by two, three, or four contributors.");

#define STAKING_AUTHORIZATION_EXPIRATION_WINDOW         (60*60*24*7*2)  // 2 weeks

#define BLOCKCHAIN_TIMESTAMP_CHECK_WINDOW               11

// For local testnet debug purposes allow shrinking the uptime proof frequency
#ifndef UPTIME_PROOF_BASE_MINUTE
#define UPTIME_PROOF_BASE_MINUTE                        60
#endif

#define UPTIME_PROOF_BUFFER_IN_SECONDS                  (5*60) // The acceptable window of time to accept a peer's uptime proof from its reported timestamp
#define UPTIME_PROOF_FREQUENCY_IN_SECONDS               (60*60)
#define UPTIME_PROOF_MAX_TIME_IN_SECONDS                (UPTIME_PROOF_FREQUENCY_IN_SECONDS * 2 + UPTIME_PROOF_BUFFER_IN_SECONDS)

// MONEY_SUPPLY - total number coins to be generated
#define MONEY_SUPPLY                                    ((uint64_t)(1500000000000000000))
#define EMISSION_SPEED_FACTOR_PER_MINUTE                (28)
#define FINAL_SUBSIDY_PER_MINUTE                        ((uint64_t)500000000) // 3 * pow(10, 7)
#define EMISSION_LINEAR_BASE                            ((uint64_t)(1) << 58)
#define YEARLY_INFLATION_INVERSE                        200 // 0.5% yearly inflation, inverted for integer division
#define EMISSION_SUPPLY_MULTIPLIER                      19
#define EMISSION_SUPPLY_DIVISOR                         10
#define EMISSION_DIVISOR                                2000000

#define CRYPTONOTE_REWARD_BLOCKS_WINDOW                 100
#define CRYPTONOTE_BLOCK_GRANTED_FULL_REWARD_ZONE_V2    600000 //size of block (bytes) after which reward for block calculated using block size
#define CRYPTONOTE_BLOCK_GRANTED_FULL_REWARD_ZONE_V1    20000 //size of block (bytes) after which reward for block calculated using block size - before first fork
#define UPTIME_PROOF_INITIAL_DELAY_SECONDS              (2*UPTIME_PROOF_BASE_MINUTE) // Delay after startup before sending a proof (to allow connections to be established)
#define UPTIME_PROOF_TIMER_SECONDS                      (5*UPTIME_PROOF_BASE_MINUTE) // How often we check whether we need to send an uptime proof
#define UPTIME_PROOF_FREQUENCY_IN_SECONDS               (60*UPTIME_PROOF_BASE_MINUTE) // How often we resend uptime proofs normally (i.e. after we've seen an uptime proof reply from the network)
#define UPTIME_PROOF_MAX_TIME_IN_SECONDS                (UPTIME_PROOF_FREQUENCY_IN_SECONDS * 2 + UPTIME_PROOF_BUFFER_IN_SECONDS) // How long until proofs of other network master nodes are considered expired

#define STORAGE_SERVER_PING_LIFETIME                    UPTIME_PROOF_FREQUENCY_IN_SECONDS
#define LOKINET_PING_LIFETIME                           UPTIME_PROOF_FREQUENCY_IN_SECONDS

#define CRYPTONOTE_BLOCK_GRANTED_FULL_REWARD_ZONE_V5    300000 //size of block (bytes) after which reward for block calculated using block size - second change, from v5
#define CRYPTONOTE_LONG_TERM_BLOCK_WEIGHT_WINDOW_SIZE   100000 // size in blocks of the long term block weight median window
#define CRYPTONOTE_SHORT_TERM_BLOCK_WEIGHT_SURGE_FACTOR 50
#define CRYPTONOTE_COINBASE_BLOB_RESERVED_SIZE          600
#define CRYPTONOTE_DISPLAY_DECIMAL_POINT                9

#define FEE_PER_KB                                      ((uint64_t)2000000000) // 2 BELDEX (= 2 * pow(10, 9))
#define FEE_PER_BYTE                                    ((uint64_t)215)   // Fallback used in wallet if no fee is available from RPC
#define FEE_PER_BYTE_V12                                ((uint64_t)17200) // Higher fee (and fallback) in v12 (only, v13 switches back)
#define FEE_PER_OUTPUT                                  ((uint64_t)20000000) // 0.02 BELDEX per tx output (in addition to the per-byte fee), starting in v13
#define DYNAMIC_FEE_PER_KB_BASE_BLOCK_REWARD            ((uint64_t)10000000000000) // 10 * pow(10,12)
#define DYNAMIC_FEE_PER_KB_BASE_FEE_V5                  ((uint64_t)400000000)
#define DYNAMIC_FEE_REFERENCE_TRANSACTION_WEIGHT        ((uint64_t)3000)
#define DYNAMIC_FEE_REFERENCE_TRANSACTION_WEIGHT_V12    ((uint64_t)240000) // Only v12 (v13 switches back)

constexpr auto TARGET_BLOCK_TIME           = 2min;
constexpr uint64_t DIFFICULTY_WINDOW       = 59;
constexpr uint64_t DIFFICULTY_BLOCKS_COUNT(bool before_hf16)
{
  // NOTE: We used to have a different setup here where,
  // DIFFICULTY_WINDOW       = 60
  // DIFFICULTY_BLOCKS_COUNT = 61
  // next_difficulty_v2's  N = DIFFICULTY_WINDOW - 1
  //
  // And we resized timestamps/difficulties to (N+1) (chopping off the latest timestamp).
  //
  // Now we re-adjust DIFFICULTY_WINDOW to 59. To preserve the old behaviour we
  // add +2. After HF16 we avoid trimming the top block and just add +1.
  //
  // Ideally, we just set DIFFICULTY_BLOCKS_COUNT to DIFFICULTY_WINDOW
  // + 1 for before and after HF16 (having one unified constant) but this
  // requires some more investigation to get it working with pre HF16 blocks and
  // alt chain code without bugs.
  uint64_t result = (before_hf16) ? DIFFICULTY_WINDOW + 2 : DIFFICULTY_WINDOW + 1;
  return result;
}

constexpr uint64_t BLOCKS_EXPECTED_IN_HOURS(int hours) { return (1h / TARGET_BLOCK_TIME) * hours; }
constexpr uint64_t BLOCKS_EXPECTED_IN_DAYS(int days)   { return BLOCKS_EXPECTED_IN_HOURS(24) * days; }
constexpr uint64_t BLOCKS_EXPECTED_IN_YEARS(int years) { return BLOCKS_EXPECTED_IN_DAYS(365) * years; }

#define CRYPTONOTE_LOCKED_TX_ALLOWED_DELTA_SECONDS_V2   TARGET_BLOCK_TIME * CRYPTONOTE_LOCKED_TX_ALLOWED_DELTA_BLOCKS
#define CRYPTONOTE_LOCKED_TX_ALLOWED_DELTA_BLOCKS       1


#define BLOCKS_IDS_SYNCHRONIZING_DEFAULT_COUNT          10000  //by default, blocks ids count in synchronizing
#define BLOCKS_SYNCHRONIZING_DEFAULT_COUNT              100    //by default, blocks count in blocks downloading
#define BLOCKS_SYNCHRONIZING_MAX_COUNT                  2048   //must be a power of 2, greater than 128, equal to SEEDHASH_EPOCH_BLOCKS

#define CRYPTONOTE_MEMPOOL_TX_LIVETIME                    (86400*3) //seconds, three days
#define CRYPTONOTE_MEMPOOL_TX_FROM_ALT_BLOCK_LIVETIME     (86400*7) //seconds, one week

#define MEMPOOL_PRUNE_NON_STANDARD_TX_LIFETIME          (2 * 60 * 60) // seconds, 2 hours
// see src/cryptonote_protocol/levin_notify.cpp
#define CRYPTONOTE_NOISE_MIN_EPOCH                      5      // minutes
#define CRYPTONOTE_NOISE_EPOCH_RANGE                    30     // seconds
#define CRYPTONOTE_NOISE_MIN_DELAY                      10     // seconds
#define CRYPTONOTE_NOISE_DELAY_RANGE                    5      // seconds
#define CRYPTONOTE_NOISE_BYTES                          3*1024 // 3 KiB
#define CRYPTONOTE_NOISE_CHANNELS                       2      // Max outgoing connections per zone used for noise/covert sending

#define CRYPTONOTE_MAX_FRAGMENTS                        20 // ~20 * NOISE_BYTES max payload size for covert/noise send


#define P2P_LOCAL_WHITE_PEERLIST_LIMIT                  1000
#define P2P_LOCAL_GRAY_PEERLIST_LIMIT                   5000

#define P2P_DEFAULT_CONNECTIONS_COUNT_OUT               8
#define P2P_DEFAULT_CONNECTIONS_COUNT_IN                32
#define P2P_DEFAULT_HANDSHAKE_INTERVAL                  60           //secondes
#define P2P_DEFAULT_PACKET_MAX_SIZE                     50000000     //50000000 bytes maximum packet size
#define P2P_DEFAULT_PEERS_IN_HANDSHAKE                  250
#define P2P_DEFAULT_CONNECTION_TIMEOUT                  5000       //5 seconds
#define P2P_DEFAULT_SOCKS_CONNECT_TIMEOUT               45         // seconds
#define P2P_DEFAULT_PING_CONNECTION_TIMEOUT             2000       //2 seconds
#define P2P_DEFAULT_INVOKE_TIMEOUT                      60*2*1000  //2 minutes
#define P2P_DEFAULT_HANDSHAKE_INVOKE_TIMEOUT            5000       //5 seconds
#define P2P_DEFAULT_WHITELIST_CONNECTIONS_PERCENT       70
#define P2P_DEFAULT_ANCHOR_CONNECTIONS_COUNT            2
#define P2P_DEFAULT_SYNC_SEARCH_CONNECTIONS_COUNT       2
#define P2P_DEFAULT_LIMIT_RATE_UP                       2048       // kB/s
#define P2P_DEFAULT_LIMIT_RATE_DOWN                     8192       // kB/s

#define P2P_FAILED_ADDR_FORGET_SECONDS                  (60*60)     //1 hour
#define P2P_IP_BLOCKTIME                                (60*60*24)  //24 hour
#define P2P_IP_FAILS_BEFORE_BLOCK                       10
#define P2P_IDLE_CONNECTION_KILL_INTERVAL               (5*60) //5 minutes

// TODO(doyle): Deprecate after checkpointing hardfork, remove notion of being
// able to sync non-fluffy blocks, keep here so we can still accept blocks
// pre-hardfork
#define P2P_SUPPORT_FLAG_FLUFFY_BLOCKS                  0x01
#define P2P_SUPPORT_FLAGS                               P2P_SUPPORT_FLAG_FLUFFY_BLOCKS

#define ALLOW_DEBUG_COMMANDS

#define CRYPTONOTE_NAME                         "beldex"
#define CRYPTONOTE_POOLDATA_FILENAME            "poolstate.bin"
#define CRYPTONOTE_BLOCKCHAINDATA_FILENAME      "data.mdb"
#define CRYPTONOTE_BLOCKCHAINDATA_LOCK_FILENAME "lock.mdb"
#define P2P_NET_DATA_FILENAME                   "p2pstate.bin"
#define MINER_CONFIG_FILE_NAME                  "miner_conf.json"

#define THREAD_STACK_SIZE                       5 * 1024 * 1024

#define HF_VERSION_PER_BYTE_FEE                 cryptonote::network_version_11_bulletproofs
#define HF_VERSION_SMALLER_BP                   cryptonote::network_version_11_infinite_staking
#define HF_VERSION_LONG_TERM_BLOCK_WEIGHT       cryptonote::network_version_11_infinite_staking
#define HF_VERSION_INCREASE_FEE                 cryptonote::network_version_12_checkpointing
#define HF_VERSION_PER_OUTPUT_FEE               cryptonote::network_version_13_enforce_checkpoints
#define HF_VERSION_ED25519_KEY                  cryptonote::network_version_13_enforce_checkpoints
#define HF_VERSION_FEE_BURNING                  cryptonote::network_version_14_blink
#define HF_VERSION_BLINK                        cryptonote::network_version_14_blink
#define HF_VERSION_MIN_2_OUTPUTS                cryptonote::network_version_16_pulse
#define HF_VERSION_REJECT_SIGS_IN_COINBASE      cryptonote::network_version_16_pulse
#define HF_VERSION_ENFORCE_MIN_AGE              cryptonote::network_version_16_pulse
#define HF_VERSION_EFFECTIVE_SHORT_TERM_MEDIAN_IN_PENALTY cryptonote::network_version_16_pulse
#define HF_VERSION_PULSE cryptonote::network_version_16_pulse
#define HF_VERSION_CLSAG                        cryptonote::network_version_16_pulse

#define PER_KB_FEE_QUANTIZATION_DECIMALS        8

#define HASH_OF_HASHES_STEP                     256

#define DEFAULT_TXPOOL_MAX_WEIGHT               648000000ull // 3 days at 300000, in bytes

#define BULLETPROOF_MAX_OUTPUTS                 16

#define CRYPTONOTE_PRUNING_STRIPE_SIZE          4096 // the smaller, the smoother the increase
#define CRYPTONOTE_PRUNING_LOG_STRIPES          3 // the higher, the more space saved
#define CRYPTONOTE_PRUNING_TIP_BLOCKS           5500 // the smaller, the more space saved
//#define CRYPTONOTE_PRUNING_DEBUG_SPOOF_SEED

// New constants are intended to go here
namespace config
{
  inline constexpr auto DNS_TIMEOUT = 20s;
  inline constexpr uint64_t DEFAULT_FEE_ATOMIC_XMR_PER_KB = 500; // Just a placeholder!  Change me!
  inline constexpr uint8_t FEE_CALCULATION_MAX_RETRIES = 10;
  inline constexpr uint64_t DEFAULT_DUST_THRESHOLD = 2000000000; // 2 * pow(10, 9)
  inline constexpr uint64_t BASE_REWARD_CLAMP_THRESHOLD = 100000000; // pow(10, 8)

  // Maximum allowed stake contribution, as a fraction of the available contribution room.  This
  // should generally be slightly larger than 1.  This is used to disallow large overcontributions
  // which can happen when there are competing stakes submitted at the same time for the same
  // master node.
  using MAXIMUM_ACCEPTABLE_STAKE = std::ratio<101, 100>;

  // Used to estimate the blockchain height from a timestamp, with some grace time.  This can drift
  // slightly over time (because average block time is not typically *exactly*
  // DIFFICULTY_TARGET_V2).
  inline constexpr uint64_t HEIGHT_ESTIMATE_HEIGHT = 582088;
  inline constexpr time_t HEIGHT_ESTIMATE_TIMESTAMP = 1595359932;

  inline constexpr uint64_t CRYPTONOTE_PUBLIC_ADDRESS_BASE58_PREFIX = 0xd1;
  inline constexpr uint64_t CRYPTONOTE_PUBLIC_INTEGRATED_ADDRESS_BASE58_PREFIX = 19;
  inline constexpr uint64_t CRYPTONOTE_PUBLIC_SUBADDRESS_BASE58_PREFIX = 42;
  inline constexpr uint16_t P2P_DEFAULT_PORT = 19090;
  inline constexpr uint16_t RPC_DEFAULT_PORT = 19091;
  inline constexpr uint16_t ZMQ_RPC_DEFAULT_PORT = 19092;
  inline constexpr uint16_t QNET_DEFAULT_PORT = 19093;
  inline constexpr boost::uuids::uuid const NETWORK_ID = { {
        0x12 ,0x30, 0xF1, 0x71 , 0x61, 0x04 , 0x41, 0x61, 0x17, 0x31, 0x00, 0x82, 0x17, 0xA1, 0xB5, 0x90
    } }; // Bender's nightmare
  inline constexpr std::string_view GENESIS_TX = "013c01ff0005978c390224a302c019c844f7141f35bf7f0fc5b02ada055e4ba897557b17ac6ccf88f0a2c09fab030276d443549feee11fe325048eeea083fcb7535312572d255ede1ecb58f84253b480e89226023b7d7c5e6eff4da699393abf12b6e3d04eae7909ae21932520fb3166b8575bb180cab5ee0102e93beb645ce7d5574d6a5ed5d9b8aadec7368342d08a7ca7b342a428353a10df80e497d01202b6e6844c1e9a478d0e4f7f34e455b26077a51f0005357aa19a49ca16eb373f622101f7c2a3a2ed7011b61998b1cd4f45b4d3c1daaa82908a10ca191342297eef1cf8"sv;
  inline constexpr uint32_t GENESIS_NONCE = 11011;

  inline constexpr uint64_t GOVERNANCE_REWARD_INTERVAL_IN_BLOCKS = BLOCKS_EXPECTED_IN_DAYS(7);
  inline constexpr std::array GOVERNANCE_WALLET_ADDRESS =
  {
    "bxcguQiBhYaDW5wAdPLSwRHA6saX1nCEYUF89SPKZfBY1BENdLQWjti59aEtAEgrVZjnCJEVFoCDrG1DCoz2HeeN2pxhxL9xa"sv, // hardfork v7-10
  };

  // Hash domain separators
  inline constexpr std::string_view HASH_KEY_BULLETPROOF_EXPONENT = "bulletproof"sv;
  inline constexpr std::string_view HASH_KEY_RINGDB = "ringdsb\0"sv;
  inline constexpr std::string_view HASH_KEY_SUBADDRESS = "SubAddr\0"sv;
  inline constexpr unsigned char HASH_KEY_ENCRYPTED_PAYMENT_ID = 0x8d;
  inline constexpr unsigned char HASH_KEY_WALLET = 0x8c;
  inline constexpr unsigned char HASH_KEY_WALLET_CACHE = 0x8d;
  inline constexpr unsigned char HASH_KEY_RPC_PAYMENT_NONCE = 0x58;
  inline constexpr unsigned char HASH_KEY_MEMORY = 'k';
  inline constexpr std::string_view HASH_KEY_MULTISIG = "Multisig\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"sv;
  inline constexpr std::string_view HASH_KEY_CLSAG_ROUND = "CLSAG_round"sv;
  inline constexpr std::string_view HASH_KEY_CLSAG_AGG_0 = "CLSAG_agg_0"sv;
  inline constexpr std::string_view HASH_KEY_CLSAG_AGG_1 = "CLSAG_agg_1"sv;

  namespace testnet
  {
    inline constexpr uint64_t HEIGHT_ESTIMATE_HEIGHT = 339767;
    inline constexpr time_t HEIGHT_ESTIMATE_TIMESTAMP = 1595360006;
    inline constexpr uint64_t CRYPTONOTE_PUBLIC_ADDRESS_BASE58_PREFIX = 53;
    inline constexpr uint64_t CRYPTONOTE_PUBLIC_INTEGRATED_ADDRESS_BASE58_PREFIX = 54;
    inline constexpr uint64_t CRYPTONOTE_PUBLIC_SUBADDRESS_BASE58_PREFIX = 63;
    inline constexpr uint16_t P2P_DEFAULT_PORT = 29090;
    inline constexpr uint16_t RPC_DEFAULT_PORT = 29091;
    inline constexpr uint16_t ZMQ_RPC_DEFAULT_PORT = 29092;
    inline constexpr uint16_t QNET_DEFAULT_PORT = 29093;
    inline constexpr boost::uuids::uuid const NETWORK_ID = { {
        0x12 ,0x30, 0xF1, 0x71 , 0x61, 0x04 , 0x41, 0x61, 0x17, 0x31, 0x00, 0x82, 0x17, 0xA1, 0xB6, 0x91
      } }; // Bender's daydream
    inline constexpr std::string_view GENESIS_TX = "023c01ff0001d7c1c4e81402a4b3be74714906edf0d798d22083d36983e80086d62436302684ca5bea0f312b420195937f9cb7005504052c96bf73d65d55f611c141876e5e519cef59fcb041d90872000000000000000000000000000000000000000000000000000000000000000000"sv;
    inline constexpr uint32_t GENESIS_NONCE = 11012;

    inline constexpr uint64_t GOVERNANCE_REWARD_INTERVAL_IN_BLOCKS = 1000;
    inline constexpr std::array GOVERNANCE_WALLET_ADDRESS =
    {
      "9zGqWVYfaWRTroZwwtATfFHKcSby5JYCW8Yvu7gyTeg3ZC5deykauXNNms2J7DiiXxg3RknqkV4EV4UaPGFwc1Y8TkTSWzm"sv,

    };

  }

  namespace devnet
  {
    inline constexpr uint64_t HEIGHT_ESTIMATE_HEIGHT = 0;
    inline constexpr time_t HEIGHT_ESTIMATE_TIMESTAMP = 1597170000;
    inline constexpr uint64_t CRYPTONOTE_PUBLIC_ADDRESS_BASE58_PREFIX = 24; // ~ dV1 .. dV3
    inline constexpr uint64_t CRYPTONOTE_PUBLIC_INTEGRATED_ADDRESS_BASE58_PREFIX = 25; // ~ dVA .. dVC
    inline constexpr uint64_t CRYPTONOTE_PUBLIC_SUBADDRESS_BASE58_PREFIX = 26; // ~dVa .. dVc
    inline constexpr uint16_t P2P_DEFAULT_PORT = 39090;
    inline constexpr uint16_t RPC_DEFAULT_PORT = 39091;
    inline constexpr uint16_t ZMQ_RPC_DEFAULT_PORT = 39092;
    inline constexpr uint16_t QNET_DEFAULT_PORT = 39093;
    inline constexpr boost::uuids::uuid const NETWORK_ID = { {
        0x12 ,0x30, 0xF1, 0x71 , 0x61, 0x04 , 0x41, 0x61, 0x17, 0x31, 0x00, 0x82, 0x17, 0xA1, 0xB7, 0x92
      } };
    inline constexpr std::string_view GENESIS_TX = "023c01ff0001d7c1c4e81402a25ba172ed7bca3b35e0be2f097b743973cf3c26777342032bed1036b19ab7a4420145706ec71eec5d57962c225b0615c172f8429984ec4954ba8b05bdad3f454f0472000000000000000000000000000000000000000000000000000000000000000000"sv;
    inline constexpr uint32_t GENESIS_NONCE = 11013;

    inline constexpr uint64_t GOVERNANCE_REWARD_INTERVAL_IN_BLOCKS = BLOCKS_EXPECTED_IN_DAYS(7);
    inline constexpr std::array GOVERNANCE_WALLET_ADDRESS =
    {
      "59XZKiAFwAKVyWN1CuuyFqMTTFLu9PEjpb3WhXfVuStgdoCZM1MtyJ2C41qijqfbdnY844F3boaW29geb8pT3mfrV9QQSRB"sv, // hardfork v7-9
    };
  }
}

namespace cryptonote
{
  enum network_version
  {
    network_version_7 = 7,
    network_version_8,
    network_version_9_master_nodes, // Proof Of Stake w/ Master Nodes
    network_version_10_bulletproofs, // Bulletproofs, Master Node Grace Registration Period, Batched Governance
    network_version_11_infinite_staking, // Infinite Staking, CN-Turtle
    network_version_12_security_signature,
    network_version_13_pulse, // Checkpointing, Relaxed Deregistration, RandomXL, Beldex Storage Server
    

    network_version_count,
  };

  enum network_type : uint8_t
  {
    MAINNET = 0,
    TESTNET,
    DEVNET,
    FAKECHAIN,
    UNDEFINED = 255
  };

  inline constexpr std::string_view network_type_str(network_type nettype)
  {
    switch(nettype)
    {
      case MAINNET: return "Mainnet"sv;
      case TESTNET: return "Testnet"sv;
      case DEVNET: return "Devnet"sv;
      case FAKECHAIN: return "Fakenet"sv;
      case UNDEFINED: return "Undefined Net"sv;
    }
    return "Unhandled Net"sv;
  }

  struct network_config
  {
    network_type NETWORK_TYPE;
    uint64_t HEIGHT_ESTIMATE_HEIGHT;
    time_t HEIGHT_ESTIMATE_TIMESTAMP;
    uint64_t CRYPTONOTE_PUBLIC_ADDRESS_BASE58_PREFIX;
    uint64_t CRYPTONOTE_PUBLIC_INTEGRATED_ADDRESS_BASE58_PREFIX;
    uint64_t CRYPTONOTE_PUBLIC_SUBADDRESS_BASE58_PREFIX;
    uint16_t P2P_DEFAULT_PORT;
    uint16_t RPC_DEFAULT_PORT;
    uint16_t ZMQ_RPC_DEFAULT_PORT;
    uint16_t QNET_DEFAULT_PORT;
    boost::uuids::uuid NETWORK_ID;
    std::string_view GENESIS_TX;
    uint32_t GENESIS_NONCE;
    uint64_t GOVERNANCE_REWARD_INTERVAL_IN_BLOCKS;
    std::array<std::string_view, 2> GOVERNANCE_WALLET_ADDRESS;

    inline constexpr std::string_view governance_wallet_address(int hard_fork_version) const {
      const auto wallet_switch =
        (NETWORK_TYPE == MAINNET || NETWORK_TYPE == FAKECHAIN)
        ? network_version_11_infinite_staking
        : network_version_10_bulletproofs;
      return GOVERNANCE_WALLET_ADDRESS[hard_fork_version >= wallet_switch ? 1 : 0];
    }
  };
  inline constexpr network_config mainnet_config = {
    MAINNET,
    ::config::HEIGHT_ESTIMATE_HEIGHT,
    ::config::HEIGHT_ESTIMATE_TIMESTAMP,
    ::config::CRYPTONOTE_PUBLIC_ADDRESS_BASE58_PREFIX,
    ::config::CRYPTONOTE_PUBLIC_INTEGRATED_ADDRESS_BASE58_PREFIX,
    ::config::CRYPTONOTE_PUBLIC_SUBADDRESS_BASE58_PREFIX,
    ::config::P2P_DEFAULT_PORT,
    ::config::RPC_DEFAULT_PORT,
    ::config::ZMQ_RPC_DEFAULT_PORT,
    ::config::QNET_DEFAULT_PORT,
    ::config::NETWORK_ID,
    ::config::GENESIS_TX,
    ::config::GENESIS_NONCE,
    ::config::GOVERNANCE_REWARD_INTERVAL_IN_BLOCKS,
    ::config::GOVERNANCE_WALLET_ADDRESS,
  };
  inline constexpr network_config testnet_config = {
    TESTNET,
    ::config::testnet::HEIGHT_ESTIMATE_HEIGHT,
    ::config::testnet::HEIGHT_ESTIMATE_TIMESTAMP,
    ::config::testnet::CRYPTONOTE_PUBLIC_ADDRESS_BASE58_PREFIX,
    ::config::testnet::CRYPTONOTE_PUBLIC_INTEGRATED_ADDRESS_BASE58_PREFIX,
    ::config::testnet::CRYPTONOTE_PUBLIC_SUBADDRESS_BASE58_PREFIX,
    ::config::testnet::P2P_DEFAULT_PORT,
    ::config::testnet::RPC_DEFAULT_PORT,
    ::config::testnet::ZMQ_RPC_DEFAULT_PORT,
    ::config::testnet::QNET_DEFAULT_PORT,
    ::config::testnet::NETWORK_ID,
    ::config::testnet::GENESIS_TX,
    ::config::testnet::GENESIS_NONCE,
    ::config::testnet::GOVERNANCE_REWARD_INTERVAL_IN_BLOCKS,
    ::config::testnet::GOVERNANCE_WALLET_ADDRESS,
  };
  inline constexpr network_config devnet_config = {
    DEVNET,
    ::config::devnet::HEIGHT_ESTIMATE_HEIGHT,
    ::config::devnet::HEIGHT_ESTIMATE_TIMESTAMP,
    ::config::devnet::CRYPTONOTE_PUBLIC_ADDRESS_BASE58_PREFIX,
    ::config::devnet::CRYPTONOTE_PUBLIC_INTEGRATED_ADDRESS_BASE58_PREFIX,
    ::config::devnet::CRYPTONOTE_PUBLIC_SUBADDRESS_BASE58_PREFIX,
    ::config::devnet::P2P_DEFAULT_PORT,
    ::config::devnet::RPC_DEFAULT_PORT,
    ::config::devnet::ZMQ_RPC_DEFAULT_PORT,
    ::config::devnet::QNET_DEFAULT_PORT,
    ::config::devnet::NETWORK_ID,
    ::config::devnet::GENESIS_TX,
    ::config::devnet::GENESIS_NONCE,
    ::config::devnet::GOVERNANCE_REWARD_INTERVAL_IN_BLOCKS,
    ::config::devnet::GOVERNANCE_WALLET_ADDRESS,
  };
  inline constexpr network_config fakenet_config = {
    FAKECHAIN,
    ::config::HEIGHT_ESTIMATE_HEIGHT,
    ::config::HEIGHT_ESTIMATE_TIMESTAMP,
    ::config::CRYPTONOTE_PUBLIC_ADDRESS_BASE58_PREFIX,
    ::config::CRYPTONOTE_PUBLIC_INTEGRATED_ADDRESS_BASE58_PREFIX,
    ::config::CRYPTONOTE_PUBLIC_SUBADDRESS_BASE58_PREFIX,
    ::config::P2P_DEFAULT_PORT,
    ::config::RPC_DEFAULT_PORT,
    ::config::ZMQ_RPC_DEFAULT_PORT,
    ::config::QNET_DEFAULT_PORT,
    ::config::NETWORK_ID,
    ::config::GENESIS_TX,
    ::config::GENESIS_NONCE,
    100, //::config::GOVERNANCE_REWARD_INTERVAL_IN_BLOCKS,
    ::config::GOVERNANCE_WALLET_ADDRESS,
  };

  inline constexpr const network_config& get_config(network_type nettype)
  {
    switch (nettype)
    {
      case MAINNET: return mainnet_config;
      case TESTNET: return testnet_config;
      case DEVNET: return devnet_config;
      case FAKECHAIN: return fakenet_config;
      default: throw std::runtime_error{"Invalid network type"};
    }
  }
}
