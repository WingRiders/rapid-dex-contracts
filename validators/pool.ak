use cardano/address.{Address, Credential}
use cardano/assets.{AssetName, PolicyId}
use cardano/certificate.{Certificate}
use cardano/governance.{ProposalProcedure, Voter}
use cardano/transaction.{OutputReference, Transaction}

type PoolDatum {
  aPolicyId: PolicyId,
  aAssetName: AssetName,
  bPolicyId: PolicyId,
  bAssetName: AssetName,
  feePoints: Int,
  feeBasis: Int,
  lovelaceFee: Int,
  aTreasury: Int,
  bTreasury: Int,
  treasury: Address,
}

type PoolRedeemer {
  Swap { swapAtoB: Bool }
  AddLiquidity
  WithdrawLiquidity
  ExtractTreasury
}

validator pool {
  // * There are 2 inputs: a pool and a request
  // * There are 2 outputs: a pool and a compensation
  // * The new pool datum's inline
  // * The new pool datum has a validity token
  // * The pool address stays the same
  // * The interaction is applied correctly
  spend(
    _datum: Option<Data>,
    _redeemer: Data,
    _utxo: OutputReference,
    _self: Transaction,
  ) {
    // todo @"spend logic goes here"
  }

  else(_) {
    fail
  }
}
