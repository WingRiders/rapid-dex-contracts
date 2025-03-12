use cardano/assets.{PolicyId}
use cardano/transaction.{Transaction}
use aiken/builtin

validator validity {
  // * one pool output with one validity token
  // * no pool inputs
  // * 0% <= fees <= 100%
  // * assets are different and sorted
  // * treasuries are 0
  mint(_redeemer: Data, _policy_id: PolicyId, tx: Transaction) {
    // let pool_output = builtin.head_list(tx.outputs)
    // todo @"mint logic goes here"
  }

  else(_) {
    fail
  }
}
