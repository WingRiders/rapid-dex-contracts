use aiken/collection/list
use aiken/crypto.{ScriptHash}
use aiken/math.{min}
use aiken/primitive/bytearray
use cardano/address.{Address, Script, VerificationKey}
use cardano/assets.{
  AssetName, PolicyId, Value, ada_policy_id, lovelace_of, quantity_of,
}
use cardano/transaction.{InlineDatum, Output, OutputReference, Transaction}

type PoolDatum {
  a_policy_id: PolicyId,
  a_asset_name: AssetName,
  b_policy_id: PolicyId,
  b_asset_name: AssetName,
  swap_fee_points: Int,
  fee_basis: Int,
  shares_asset_name: AssetName,
}

type PoolRedeemer {
  Swap { swap_a_to_b: Bool, provided: Int }
  AddLiquidity { a_add: Int, b_add: Int }
  WithdrawLiquidity { shares_add: Int }
  Donate
}

const validity_asset_name = "P"

const pool_oil = 2_000_000

const max_share_tokens = 9_223_372_036_854_775_807

// Amount of shares to be burned upon new pool creation.
// The value is the same as in Uniswap v2 [https://uniswap.org/whitepaper.pdf]
const burned_share_tokens = 1_000

// NOTE: if you integrate some other script with this contract,
//       make sure to handle possible double satisfaction attacks;
//       this contract doesn't restrict the number of pool inputs/outputs,
//       only the number of input/output pools
//
validator pool {
  // * There is 1 pool input
  // * There is 1 pool output
  // * The old pool has a validity token
  // * The new pool has a validity token
  // * The new pool datum's inline
  // * The pool address stays the same
  // * The new pool has the correct number of tokens
  // * The pool datum fields stay the same
  //
  // NOTE: the contract doesn't check user compensations directly
  //       but only the pool values;
  //       it is assumed the users take the compensations wherever they choose to
  //       as the pool only offers direct interactions without request intermediaries
  //
  // For swaps
  // * Users gets the fair amount of compensation
  // * The new A/B values are expected on the pool
  // * The new ada is at least pool oil
  // * The number of shares doesn't change
  // * The swap provides at least some tokens
  // * User receives at least some tokens NOTE: increasing the min swap to make it harder to block the pool
  // * The swap fee is collected into the pool value
  //
  // For add liquidity
  // * Users gets the fair amount of compensation in shares
  // * The new pool A/B values include the provided tokens
  // * The new pool ada is at least pool oil
  // * The new pool shares are expected on the pool output value
  // * User provides at least some tokens
  // * User receives at least some shares
  //
  // NOTE: earned shares are determined as min(earned shares from added a, earned shares from added b)
  //       that means it's possible to donate liquidity into the pool.
  //
  // NOTE: provided A and B are taken from the redeemer and are assumed to be fully added into the pool
  //       strict equality is used for the pool value checks
  //
  // For withdraw liquidity
  // * Users gets the fair amount of compensation in a/b tokens
  // * The new pool A/B values don't have the returned tokens
  // * The new pool ada is at least pool oil
  // * The new shares are expected on the pool output value
  // * User provides at least some shares
  // * User receives at least some A and B tokens
  //
  // NOTE: redeemed shares are taken from the redeemer and are assumed to be fully added into the pool
  //       strict equality is used for the pool value checks
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
    let is_ada_pool = pool_input_datum.a_policy_id == ada_policy_id

    let pool_shares_output =
      quantity_of(
        pool_output_value,
        validity_policy_id,
        pool_input_datum.shares_asset_name,
      )
    let pool_ada_output = lovelace_of(pool_output_value)

    let expected_token_count =
      expected_pool_token_count(is_ada_pool, pool_shares_output)
    and {
      // Address doesn't change
      pool_output.address == pool_address,
      // Validity token is present in the input
      quantity_of(pool_input_value, validity_policy_id, validity_asset_name) == 1,
      // Validity token is preserved in the output
      quantity_of(pool_output_value, validity_policy_id, validity_asset_name) == 1,
      // Asset A, Asset B, Ada if Asset A != Ada, Shares Asset, Validity Asset
      count_tokens(pool_output_value) == expected_token_count,
      // Datum is preserved
      pool_input_datum == pool_output_datum,
      validate_action(
        pool_redeemer,
        is_ada_pool,
        validity_policy_id,
        pool_input_datum,
        pool_input_value,
        pool_output_value,
        pool_ada_output,
        pool_shares_output,
      ),
    }
  }

  // NOTE: the contract doesn't check user compensations directly
  //       but only the pool and mint values
  //       it is assumed the users take the compensations wherever they choose to
  //
  // NOTE: the policy mints max shares - burned shares
  //       for more details read https://uniswap.org/whitepaper.pdf section 3.4
  // 
  // * the user gets at least some shares
  // * total emitted shares = sqrt (liquidity a * liquidity b)
  //   => total emitted shares ^ 2 <= liquidity a * liquidity b
  //      (total emitted shares + 1) ^ 2 > liquidity a * liquidity b
  //   total emitted shares are inferred as max shares constant - pool output shares
  // * user gets total emitted shares - burned shares
  // * one output on the pool address with one validity token and shares and correct value
  // * the pool has 1 validity token
  // * the pool has at least pool oil ada
  // * the pool has positive A liquidity (disregarding oil for ada pools)
  // * the pool has positive B liquidity
  // * the pool has the expected number of tokens (a + b + ada if a != ada + shares + validity)
  // * the pool has datum inline
  // * 0% <= swap fee <= 100%
  // * assets are different and sorted, and don't overlap with validity token or shares
  // * two different tokens with the pool policy id are minted
  // * 1 pool validity token is minted
  //   (validity token policy id is pool script hash)
  //   (validity token asset name is a constant)
  // * the output index of the first input (seed) fits into a byte
  // * max share tokens - burned share tokens are minted
  //   (share policy id is pool script hash)
  //   (share asset name is seed's utxo ref's tx id <> output index)
  // * share asset name is constructed from the seed output ref
  // * share asset name is stored in the datum
  mint(_redeemer: Data, policy_id: PolicyId, transaction: Transaction) {
    let pool_hash = policy_id
    // One pool output
    expect [pool_output] =
      list.filter(
        transaction.outputs,
        fn(output) { has_script_hash(output.address, pool_hash) },
      )
    // The pool datum is inline
    expect InlineDatum(pool_output_datum_inline) = pool_output.datum
    expect pool_output_datum: PoolDatum = pool_output_datum_inline

    let are_fees_sensible = and {
        pool_output_datum.swap_fee_points >= 0,
        pool_output_datum.swap_fee_points <= pool_output_datum.fee_basis,
      }

    expect Some(seed) = list.at(transaction.inputs, 0)
    let share_asset_name =
      bytearray.concat(
        seed.output_reference.transaction_id,
        bytearray.from_int_little_endian(seed.output_reference.output_index, 1),
      )

    let are_assets_fine = and {
        if pool_output_datum.a_policy_id == pool_output_datum.b_policy_id {
          bytearray.compare(
            pool_output_datum.a_asset_name,
            pool_output_datum.b_asset_name,
          ) == Less
        } else {
          bytearray.compare(
            pool_output_datum.a_policy_id,
            pool_output_datum.b_policy_id,
          ) == Less
        },
        // Pools trading shares are allowed
        pool_output_datum.a_policy_id != pool_hash || and {
          pool_output_datum.a_asset_name != share_asset_name,
          pool_output_datum.a_asset_name != validity_asset_name,
        },
        pool_output_datum.b_policy_id != pool_hash || and {
          pool_output_datum.b_asset_name != share_asset_name,
          pool_output_datum.b_asset_name != validity_asset_name,
        },
      }

    let is_pool_value_correct = {
      let pool_output_value = pool_output.value

      let token_count = count_tokens(pool_output_value)

      let is_ada_pool = pool_output_datum.a_policy_id == ada_policy_id
      let ada_pool = lovelace_of(pool_output_value)
      let as_liquidity_pool =
        if is_ada_pool {
          ada_pool - pool_oil
        } else {
          quantity_of(
            pool_output_value,
            pool_output_datum.a_policy_id,
            pool_output_datum.a_asset_name,
          )
        }
      let bs_liquidity_pool =
        quantity_of(
          pool_output_value,
          pool_output_datum.b_policy_id,
          pool_output_datum.b_asset_name,
        )
      let shares_pool =
        quantity_of(pool_output_value, pool_hash, share_asset_name)

      let shares_total_emitted = max_share_tokens - shares_pool
      let shares_total_emitted_plus_1 = shares_total_emitted + 1
      let shares_user = shares_total_emitted - burned_share_tokens
      let ab_out = as_liquidity_pool * bs_liquidity_pool
      let is_liquidity_correct = and {
          shares_total_emitted * shares_total_emitted <= ab_out,
          shares_total_emitted_plus_1 * shares_total_emitted_plus_1 > ab_out,
        }

      and {
        is_liquidity_correct,
        as_liquidity_pool > 0,
        bs_liquidity_pool > 0,
        ada_pool >= pool_oil,
        shares_user > 0,
        token_count == expected_pool_token_count(is_ada_pool, shares_pool),
        quantity_of(pool_output_value, pool_hash, validity_asset_name) == 1,
      }
    }

    let is_mint_correct = {
      let mint = transaction.mint
      let minted =
        assets.reduce(
          mint,
          0,
          fn(policy, _, _, acc) {
            if policy == pool_hash {
              acc + 1
            } else {
              acc
            }
          },
        )
      let validity_count = quantity_of(mint, pool_hash, validity_asset_name)
      let share_count = quantity_of(mint, pool_hash, share_asset_name)
      and {
        // pool validity token, share tokens
        minted == 2,
        validity_count == 1,
        share_count == max_share_tokens - burned_share_tokens,
      }
    }

    let is_share_asset_name_stored =
      pool_output_datum.shares_asset_name == share_asset_name

    and {
      are_fees_sensible,
      are_assets_fine,
      is_pool_value_correct,
      is_mint_correct,
      is_share_asset_name_stored,
    }
  }

  else(_) {
    fail
  }
}

fn validate_action(
  pool_redeemer: PoolRedeemer,
  is_ada_pool: Bool,
  validity_policy_id: PolicyId,
  pool_input_datum: PoolDatum,
  pool_input_value: Value,
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
      as_input - pool_oil
    } else {
      as_input
    }
  let pool_input_b_liquidity = bs_input

  when pool_redeemer is {
    Swap { swap_a_to_b, provided } -> {
      let swap_fee =
        div_ceil(
          provided * pool_input_datum.swap_fee_points,
          pool_input_datum.fee_basis,
        )
      let (expected_a_liquidity, expected_b_liquidity, received) =
        if swap_a_to_b {
          let new_a = pool_input_a_liquidity + provided
          let new_b =
            div_ceil(
              pool_input_a_liquidity * pool_input_b_liquidity,
              pool_input_a_liquidity + provided - swap_fee,
            )
          (new_a, new_b, pool_input_b_liquidity - new_b)
        } else {
          let new_a =
            div_ceil(
              pool_input_b_liquidity * pool_input_a_liquidity,
              pool_input_b_liquidity + provided - swap_fee,
            )
          let new_b = pool_input_b_liquidity + provided
          (new_a, new_b, pool_input_a_liquidity - new_a)
        }

      let is_pool_value_correct = {
        let a_ada_asset_check =
          if is_ada_pool {
            as_output == expected_a_liquidity + pool_oil
          } else {
            and {
              as_output == expected_a_liquidity,
              ada_output >= pool_oil,
            }
          }

        let b_asset_check = bs_output == expected_b_liquidity
        let shares_asset_check = shares_output == shares_input
        and {
          a_ada_asset_check,
          b_asset_check,
          shares_asset_check,
        }
      }

      and {
        is_pool_value_correct,
        provided > 0,
        received > 0,
      }
    }

    AddLiquidity { a_add, b_add } -> {
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

    WithdrawLiquidity { shares_add } -> {
      let shares_total_emitted = max_share_tokens - shares_input
      let a_remove = shares_add * pool_input_a_liquidity / shares_total_emitted
      let b_remove = shares_add * pool_input_b_liquidity / shares_total_emitted
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
        shares_add > 0,
        a_remove > 0,
        b_remove > 0,
      }
    }

    Donate -> and {
        ada_output >= lovelace_of(pool_input_value),
        as_output >= as_input,
        bs_output >= bs_input,
        shares_output == shares_input,
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

// Asset A + Asset B + Ada if Asset A != Ada + Shares Asset + Validity Asset
// Shares can potentially be 0.
fn expected_pool_token_count(is_ada_pool: Bool, share_count: Int) -> Int {
  if is_ada_pool {
    4
  } else {
    5
  } - if share_count == 0 {
    1
  } else {
    0
  }
}
