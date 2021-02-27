#include "tx_extra.h"

namespace cryptonote {

tx_extra_beldex_name_system tx_extra_beldex_name_system::make_buy(
    lns::generic_owner const& owner,
    lns::generic_owner const* backup_owner,
    lns::mapping_type type,
    const crypto::hash& name_hash,
    const std::string& encrypted_value,
    const crypto::hash& prev_txid)
{
  tx_extra_beldex_name_system result{};
  result.fields = lns::extra_field::buy;
  result.owner = owner;

  if (backup_owner)
    result.backup_owner = *backup_owner;
  else
    result.fields = lns::extra_field::buy_no_backup;

  result.type = type;
  result.name_hash = name_hash;
  result.encrypted_value = encrypted_value;
  result.prev_txid = prev_txid;
  return result;
}

tx_extra_beldex_name_system tx_extra_beldex_name_system::make_renew(
    lns::mapping_type type, crypto::hash const &name_hash, crypto::hash const &prev_txid)
{
  assert(is_beldexnet_type(type) && prev_txid);

  tx_extra_beldex_name_system result{};
  result.fields = lns::extra_field::none;
  result.type = type;
  result.name_hash = name_hash;
  result.prev_txid = prev_txid;
  return result;
}

tx_extra_beldex_name_system tx_extra_beldex_name_system::make_update(
    const lns::generic_signature& signature,
    lns::mapping_type type,
    const crypto::hash& name_hash,
    std::string_view encrypted_value,
    const lns::generic_owner* owner,
    const lns::generic_owner* backup_owner,
    const crypto::hash& prev_txid)
{
  tx_extra_beldex_name_system result{};
  result.signature = signature;
  result.type = type;
  result.name_hash = name_hash;
  result.fields |= lns::extra_field::signature;

  if (encrypted_value.size())
  {
    result.fields |= lns::extra_field::encrypted_value;
    result.encrypted_value = std::string{encrypted_value};
  }

  if (owner)
  {
    result.fields |= lns::extra_field::owner;
    result.owner = *owner;
  }

  if (backup_owner)
  {
    result.fields |= lns::extra_field::backup_owner;
    result.backup_owner = *backup_owner;
  }

  result.prev_txid = prev_txid;
  return result;
}

}
