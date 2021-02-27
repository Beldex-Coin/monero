#include "wallet/api/wallet2_api.h"
#include "wallet/wallet2.h"

#include <string>


namespace Wallet {

class WalletImpl;
class StakeUnlockResultImpl : public StakeUnlockResult
{
public:
    StakeUnlockResultImpl(WalletImpl& w, tools::wallet2::request_stake_unlock_result res);
    StakeUnlockResultImpl();
    ~StakeUnlockResultImpl();

    bool success() override;
    std::string msg() override;
    PendingTransaction* ptx() override;

private:
    WalletImpl& wallet;
    tools::wallet2::request_stake_unlock_result result;
};


}
