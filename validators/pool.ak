use aiken/collection/list
use aiken/crypto.{ScriptHash}
use aiken/math.{min}
use cardano/address.{Address, Script, VerificationKey}
use cardano/assets.{AssetName, PolicyId, Value, quantity_of}
use cardano/transaction.{
  InlineDatum, NoDatum, Output, OutputReference, Transaction,
}

type PoolDatum {
  a_policy_id: PolicyId,
  a_asset_name: AssetName,
  b_policy_id: PolicyId,
  b_asset_name: AssetName,
  swap_fee_points: Int,
  protocol_fee_points: Int,
  fee_basis: Int,
  lovelace_fee: Int,
  a_treasury: Int,
  b_treasury: Int,
  treasury: Address,
  shares_asset_name: AssetName,
}

// TODO: figure out how to prevent redeeming shares with a different pool
//       -> share asset name must be unique and set by the minting policy based on a utxo ref
type PoolRedeemer {
  Swap { swap_a_to_b: Bool, provided: Int }
  AddLiquidity { a_add: Int, b_add: Int }
  WithdrawLiquidity { shares_add: Int }
  // REVIEW: allow changing the staking credentials and the treasury address?
  //         have an authority token/key?
  ExtractTreasury
}

const validity_asset_name = "P"

const pool_oil = 2_000_000

const treasury_oil = 2_000_000

const max_share_tokens = 9_223_372_036_854_775_807

// TODO: additional checks for scenarios like min required swaps
validator pool {
  // * There is 1 pool input
  // * There is 1 pool output
  // * The old pool has a validity token
  // * The new pool datum's inline
  // * The new pool has a validity token
  // * The pool address stays the same
  // * The new pool has the correct number of tokens
  //
  // For swaps
  // * The invariant is preserved
  // * The swap fee is collected
  // * The protocol fee is collected
  //
  // TODO: documentation
  // For add liquidity
  // * 
  spend(
    datum: Option<Data>,
    redeemer: Data,
    pool_ref: OutputReference,
    transaction: Transaction,
  ) {
    expect pool_redeemer: PoolRedeemer = redeemer
    expect Some(datum_some) = datum
    expect pool_input_datum: PoolDatum = datum_some
    expect Some(pool_input) =
      list.find(transaction.inputs, fn(i) { i.output_reference == pool_ref })
    let pool_address = pool_input.output.address
    expect Script(pool_hash) = pool_address.payment_credential
    let validity_policy_id = pool_hash
    // One pool input
    expect [_] =
      list.filter(
        transaction.inputs,
        fn(i) { has_script_hash(i.output.address, pool_hash) },
      )
    // One pool output
    expect [pool_output] =
      list.filter(
        transaction.outputs,
        fn(output) { has_script_hash(output.address, pool_hash) },
      )
    // New pool datum is inline
    expect InlineDatum(pool_output_datum_inline) = pool_output.datum
    expect pool_output_datum: PoolDatum = pool_output_datum_inline

    let pool_input_value = pool_input.output.value
    let pool_output_value = pool_output.value
    let is_ada_pool = pool_input_datum.a_policy_id == ""

    let shares_output =
      quantity_of(
        pool_output_value,
        validity_policy_id,
        pool_input_datum.shares_asset_name,
      )
    let ada_output = quantity_of(pool_output_value, "", "")

    let expected_token_count =
      if is_ada_pool {
        4
      } else {
        5
      } - if shares_output == 0 {
        1
      } else {
        0
      }
    and {
      // Address doesn't change
      pool_output.address == pool_address,
      // Validity token is present in the input
      quantity_of(pool_input_value, validity_policy_id, validity_asset_name) == 1,
      // Validity token is preserved in the output
      quantity_of(pool_output_value, validity_policy_id, validity_asset_name) == 1,
      // Asset A, Asset B, Ada if Asset A != Ada, Shares Asset, Validity Asset
      count_tokens(pool_output_value) == expected_token_count,
      // Datum (apart from a/b_treasury) is preserved
      pool_input_datum.a_policy_id == pool_output_datum.a_policy_id,
      pool_input_datum.a_asset_name == pool_output_datum.a_asset_name,
      pool_input_datum.b_policy_id == pool_output_datum.b_policy_id,
      pool_input_datum.b_asset_name == pool_output_datum.b_asset_name,
      pool_input_datum.swap_fee_points == pool_output_datum.swap_fee_points,
      pool_input_datum.protocol_fee_points == pool_output_datum.protocol_fee_points,
      pool_input_datum.fee_basis == pool_output_datum.fee_basis,
      pool_input_datum.lovelace_fee == pool_output_datum.lovelace_fee,
      pool_input_datum.treasury == pool_output_datum.treasury,
      validate_action(
        transaction.outputs,
        is_ada_pool,
        validity_policy_id,
        pool_redeemer,
        pool_input_datum,
        pool_input_value,
        pool_output_datum,
        pool_output_value,
        ada_output,
        shares_output,
      ),
    }
  }

  // * one pool output with one validity token and shares
  // * shares are correctly distributed
  // * no pool inputs
  // * 0% <= fees <= 100%
  // * assets are different and sorted
  // * treasuries are 0
  mint(_redeemer: Data, _policy_id: PolicyId, _tx: Transaction) {
    todo @"mint logic goes here"
  }

  else(_) {
    fail
  }
}

fn validate_action(
  outputs: List<Output>,
  is_ada_pool: Bool,
  validity_policy_id: PolicyId,
  pool_redeemer: PoolRedeemer,
  pool_input_datum: PoolDatum,
  pool_input_value: Value,
  pool_output_datum: PoolDatum,
  pool_output_value: Value,
  ada_output: Int,
  shares_output: Int,
) -> Bool {
  let as_input =
    quantity_of(
      pool_input_value,
      pool_input_datum.a_policy_id,
      pool_input_datum.a_asset_name,
    )
  let bs_input =
    quantity_of(
      pool_input_value,
      pool_input_datum.b_policy_id,
      pool_input_datum.b_asset_name,
    )
  let shares_input =
    quantity_of(
      pool_input_value,
      validity_policy_id,
      pool_input_datum.shares_asset_name,
    )
  let as_output =
    quantity_of(
      pool_output_value,
      pool_input_datum.a_policy_id,
      pool_input_datum.a_asset_name,
    )
  let bs_output =
    quantity_of(
      pool_output_value,
      pool_input_datum.b_policy_id,
      pool_input_datum.b_asset_name,
    )
  let pool_input_a_liquidity =
    if is_ada_pool {
      as_input - pool_oil - pool_input_datum.a_treasury
    } else {
      as_input - pool_input_datum.a_treasury
    }
  let pool_input_b_liquidity = bs_input - pool_input_datum.b_treasury

  when pool_redeemer is {
    Swap { swap_a_to_b, provided } -> {
      let swap_fee =
        div_ceil(
          provided * pool_input_datum.swap_fee_points,
          pool_input_datum.fee_basis,
        )
      let protocol_fee =
        provided * pool_input_datum.protocol_fee_points / pool_input_datum.fee_basis

      let (
        expected_a_liquidity,
        expected_b_liquidity,
        expected_a_treasury,
        expected_b_treasury,
      ) =
        if swap_a_to_b {
          let new_a = pool_input_a_liquidity + provided - protocol_fee
          let new_b =
            div_ceil(
              pool_input_a_liquidity * pool_input_b_liquidity,
              pool_input_a_liquidity + provided - swap_fee - protocol_fee,
            )
          (
            new_a,
            new_b,
            pool_input_datum.a_treasury + protocol_fee,
            pool_input_datum.b_treasury,
          )
        } else {
          let new_a =
            div_ceil(
              pool_input_b_liquidity * pool_input_a_liquidity,
              pool_input_b_liquidity + provided - swap_fee - protocol_fee,
            )
          let new_b = pool_input_b_liquidity + provided - protocol_fee
          (
            new_a,
            new_b,
            pool_input_datum.a_treasury,
            pool_input_datum.b_treasury + protocol_fee,
          )
        }

      let is_treasury_correct = and {
          pool_output_datum.a_treasury == expected_a_treasury,
          pool_output_datum.b_treasury == expected_b_treasury,
        }

      let is_value_correct = {
        let a_ada_asset_check = and {
            as_output == expected_a_liquidity + expected_a_treasury + pool_oil,
            is_ada_pool || ada_output >= pool_oil,
          }

        let b_asset_check =
          bs_output == expected_b_liquidity + expected_b_treasury
        let shares_asset_check = shares_output == shares_input
        and {
          a_ada_asset_check,
          b_asset_check,
          shares_asset_check,
          provided > 0,
        }
      }

      and {
        is_treasury_correct,
        is_value_correct,
      }
    }
    AddLiquidity { a_add, b_add } -> {
      let is_treasury_correct = and {
          pool_output_datum.a_treasury == pool_input_datum.a_treasury,
          pool_output_datum.b_treasury == pool_input_datum.b_treasury,
        }

      let is_value_correct = {
        let shares_total_emitted = max_share_tokens - shares_input
        let shares_earned_from_a = a_add * shares_total_emitted / shares_input
        let shares_earned_from_b = b_add * shares_total_emitted / shares_input
        let shares_earned = min(shares_earned_from_a, shares_earned_from_b)
        let expected_shares_output = shares_input - shares_earned

        let a_ada_asset_check = and {
            as_output == as_input + a_add,
            is_ada_pool || ada_output >= pool_oil,
          }
        let b_asset_check = bs_output == bs_input + b_add
        let shares_asset_check = shares_output == expected_shares_output
        and {
          a_ada_asset_check,
          b_asset_check,
          shares_asset_check,
          a_add > 0,
          b_add > 0,
          shares_earned > 0,
        }
      }
      and {
        is_treasury_correct,
        is_value_correct,
      }
    }
    // TODO: recheck if value calculations are correct and sufficient here and in other branches
    WithdrawLiquidity { shares_add } -> {
      let is_treasury_correct = and {
          pool_output_datum.a_treasury == pool_input_datum.a_treasury,
          pool_output_datum.b_treasury == pool_input_datum.b_treasury,
        }
      let shares_total_emitted = max_share_tokens - shares_input
      let a_remove = shares_add * pool_input_a_liquidity / shares_total_emitted
      let b_remove = shares_add * pool_input_b_liquidity / shares_total_emitted
      let is_value_correct = {
        let expected_shares_output = shares_input + shares_add
        let a_ada_asset_check = and {
            as_output == as_input - a_remove,
            is_ada_pool || ada_output >= pool_oil,
          }
        let b_asset_check = bs_output == bs_input - b_remove
        let shares_asset_check = shares_output == expected_shares_output
        and {
          a_ada_asset_check,
          b_asset_check,
          shares_asset_check,
        }
      }
      and {
        is_treasury_correct,
        is_value_correct,
        shares_add > 0,
        a_remove > 0 || b_remove > 0,
      }
    }
    ExtractTreasury -> {
      let is_treasury_correct = and {
          pool_output_datum.a_treasury == 0,
          pool_output_datum.b_treasury == 0,
        }
      let is_value_correct = {
        let a_ada_asset_check = and {
            as_output == as_input - pool_output_datum.a_treasury,
            is_ada_pool || ada_output >= pool_oil,
          }
        let b_asset_check = bs_output == bs_input - pool_output_datum.b_treasury
        let shares_asset_check = shares_input == shares_output
        and {
          a_ada_asset_check,
          b_asset_check,
          shares_asset_check,
        }
      }
      let is_treasury_output_correct = {
        expect Some(treasury_output) = list.at(outputs, 1)
        let is_address_correct =
          treasury_output.address == pool_input_datum.treasury
        let is_value_correct = {
          let as_treasury =
            quantity_of(
              treasury_output.value,
              pool_input_datum.a_policy_id,
              pool_input_datum.a_asset_name,
            )
          let ada_treasury = quantity_of(treasury_output.value, "", "")
          let bs_treasury =
            quantity_of(
              treasury_output.value,
              pool_input_datum.b_policy_id,
              pool_input_datum.b_asset_name,
            )
          let a_ada_asset_check =
            if is_ada_pool {
              as_treasury >= pool_input_datum.a_treasury + treasury_oil
            } else {
              and {
                as_treasury >= pool_input_datum.a_treasury,
                ada_treasury >= treasury_oil,
              }
            }
          let b_asset_check = bs_treasury >= pool_input_datum.b_treasury
          // If ada pool: ada + token b; otherwise ada + token a + token b
          let token_count_check =
            count_tokens(treasury_output.value) == if is_ada_pool {
              2
            } else {
              3
            }
          and {
            a_ada_asset_check,
            b_asset_check,
            token_count_check,
          }
        }
        let is_datum_correct = treasury_output.datum == NoDatum
        and {
          is_address_correct,
          is_value_correct,
          is_datum_correct,
        }
      }
      and {
        is_treasury_correct,
        is_value_correct,
        pool_input_datum.a_treasury > 0 || pool_input_datum.b_treasury > 0,
        is_treasury_output_correct,
      }
    }
  }
}

fn has_script_hash(address: Address, script_hash: ScriptHash) -> Bool {
  when address.payment_credential is {
    Script(hash) -> script_hash == hash
    VerificationKey(_) -> False
  }
}

fn count_tokens(v: Value) -> Int {
  assets.reduce(v, 0, fn(_, _, _, acc) { acc + 1 })
}

fn div_ceil(a: Int, b: Int) -> Int {
  a / b + if a % b > 0 {
    1
  } else {
    0
  }
}
