use aiken/collection/list
use aiken/crypto.{ScriptHash, blake2b_256}
use aiken/math.{min}
use aiken/primitive/bytearray
use cardano/address.{Address, Script, VerificationKey}
use cardano/assets.{
  AssetName, PolicyId, Value, ada_policy_id, lovelace_of, quantity_of,
}
use cardano/transaction.{
  InlineDatum, Input, Output, OutputReference, Transaction,
}

type FeeFrom {
  InputToken
  OutputToken
  TokenA
  TokenB
}

type PoolDatum {
  a_policy_id: PolicyId,
  a_asset_name: AssetName,
  b_policy_id: PolicyId,
  b_asset_name: AssetName,
  treasury_a: Int,
  treasury_b: Int,
  fee_from: FeeFrom,
  treasury_authority_policy_id: PolicyId,
  treasury_authority_asset_name: AssetName,
  treasury_fee_points_a_to_b: Int,
  treasury_fee_points_b_to_a: Int,
  swap_fee_points_a_to_b: Int,
  swap_fee_points_b_to_a: Int,
  fee_basis: Int,
  shares_asset_name: AssetName,
}

type PoolRedeemer {
  Swap { swap_a_to_b: Bool, provided: Int }
  AddLiquidity { a_add: Int, b_add: Int, x_swap: Int }
  WithdrawLiquidity { shares_add: Int }
  WithdrawTreasury
  Donate
}

type MintRedeemer {
  seed_ref: OutputReference,
}

const validity_asset_name = "P"

const pool_oil = 2_000_000

const max_share_tokens = 9_223_372_036_854_775_807

// Amount of shares to be burned upon new pool creation.
// The value is the same as in Uniswap v2 [https://uniswap.org/whitepaper.pdf]
const burned_share_tokens = 1_000

// NOTE: if you integrate some other script with this contract,
//       make sure to handle possible double satisfaction attacks;
//       this contract doesn't restrict the number of script inputs/outputs,
//       only the number of input/output pools
//
validator pool {
  // * There is 1 pool input
  // * There is 1 pool output
  // * The old pool has a validity token
  // * The new pool has a validity token
  // * The new pool datum's inline
  // * The new pool doesn't have a reference script
  // * The pool address stays the same
  // * The new pool has the correct number of tokens
  // * The pool datum fields stay the same (apart from maybe treasuries)
  //
  // NOTE: the contract doesn't check user compensations directly
  //       but only the pool values;
  //       it is assumed the users take the compensations wherever they choose to
  //       as the pool only offers direct interactions without request intermediaries
  //
  // For swaps
  // * Users gets the fair amount of compensation
  // * User is able to donate to the pool as part of this action
  // * The new A/B values are expected on the pool
  // * The new ada is at least pool oil
  // * The number of shares doesn't change
  // * The swap provides at least some tokens
  // * User receives at least some tokens NOTE: increasing the min swap makes it harder to block the pool
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
    let pool_policy_id = pool_hash
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
        pool_policy_id,
        pool_input_datum.shares_asset_name,
      )
    let pool_ada_output = lovelace_of(pool_output_value)

    let expected_token_count =
      expected_pool_token_count(is_ada_pool, pool_shares_output)
    and {
      // Address doesn't change
      (pool_output.address == pool_address)?,
      // The new pool doesn't have an inline script
      (pool_output.reference_script == None)?,
      // Validity token is present in the input
      (quantity_of(pool_input_value, pool_policy_id, validity_asset_name) == 1)?,
      // Validity token is preserved in the output
      (quantity_of(pool_output_value, pool_policy_id, validity_asset_name) == 1)?,
      // Asset A, Asset B, Ada if Asset A != Ada, Shares Asset, Validity Asset
      (count_tokens(pool_output_value) == expected_token_count)?,
      validate_action(
        transaction.inputs,
        pool_redeemer,
        is_ada_pool,
        pool_policy_id,
        pool_input_datum,
        pool_output_datum,
        pool_input_value,
        pool_output_value,
        pool_ada_output,
        pool_shares_output,
      )?,
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
  // * the pool doesn't have a reference script
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
  // * seed utxo ref is passed in the redeemer
  // * seed is spent (is included in inputs)
  // * the output index of the seed fits into a byte
  // * max share tokens - burned share tokens are minted
  //   (share policy id is pool script hash)
  //   (share asset name is blake2b_256 [seed's utxo ref's tx id <> output index])
  // * share asset name is constructed from the seed output ref
  // * share asset name is stored in the datum
  // * the initial treasuries are 0
  mint(redeemer: Data, policy_id: PolicyId, transaction: Transaction) {
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

    let are_treasuries_empty = and {
        pool_output_datum.treasury_a == 0,
        pool_output_datum.treasury_b == 0,
      }

    let are_fees_sensible = and {
        pool_output_datum.swap_fee_points_a_to_b >= 0,
        pool_output_datum.swap_fee_points_b_to_a >= 0,
        pool_output_datum.treasury_fee_points_a_to_b >= 0,
        pool_output_datum.treasury_fee_points_b_to_a >= 0,
        pool_output_datum.swap_fee_points_a_to_b + pool_output_datum.treasury_fee_points_a_to_b <= pool_output_datum.fee_basis,
        pool_output_datum.swap_fee_points_b_to_a + pool_output_datum.treasury_fee_points_b_to_a <= pool_output_datum.fee_basis,
      }

    expect mint_redeemer: MintRedeemer = redeemer
    let share_asset_name =
      blake2b_256(
        bytearray.concat(
          mint_redeemer.seed_ref.transaction_id,
          bytearray.from_int_little_endian(
            mint_redeemer.seed_ref.output_index,
            1,
          ),
        ),
      )

    let are_assets_fine = and {
        if pool_output_datum.a_policy_id == pool_output_datum.b_policy_id {
          (bytearray.compare(
            pool_output_datum.a_asset_name,
            pool_output_datum.b_asset_name,
          ) == Less)?
        } else {
          (bytearray.compare(
            pool_output_datum.a_policy_id,
            pool_output_datum.b_policy_id,
          ) == Less)?
        },
        // Pools trading shares are allowed
        (pool_output_datum.a_policy_id != pool_hash)? || and {
          (pool_output_datum.a_asset_name != share_asset_name)?,
          (pool_output_datum.a_asset_name != validity_asset_name)?,
        },
        (pool_output_datum.b_policy_id != pool_hash)? || and {
          (pool_output_datum.b_asset_name != share_asset_name)?,
          (pool_output_datum.b_asset_name != validity_asset_name)?,
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
        is_liquidity_correct?,
        (as_liquidity_pool > 0)?,
        (bs_liquidity_pool > 0)?,
        (ada_pool >= pool_oil)?,
        (shares_user > 0)?,
        (token_count == expected_pool_token_count(is_ada_pool, shares_pool))?,
        (quantity_of(pool_output_value, pool_hash, validity_asset_name) == 1)?,
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
        (minted == 2)?,
        (validity_count == 1)?,
        (share_count == max_share_tokens - burned_share_tokens)?,
      }
    }

    let is_share_asset_name_stored =
      pool_output_datum.shares_asset_name == share_asset_name

    let is_seed_spent =
      list.any(
        transaction.inputs,
        fn(input) {
          and {
            input.output_reference.transaction_id == mint_redeemer.seed_ref.transaction_id,
            input.output_reference.output_index == mint_redeemer.seed_ref.output_index,
          }
        },
      )

    let has_no_reference_script = pool_output.reference_script == None

    and {
      are_fees_sensible?,
      are_treasuries_empty?,
      are_assets_fine?,
      is_pool_value_correct?,
      is_mint_correct?,
      is_share_asset_name_stored?,
      is_seed_spent?,
      has_no_reference_script?,
    }
  }

  else(_) {
    fail
  }
}

fn validate_action(
  inputs: List<Input>,
  pool_redeemer: PoolRedeemer,
  is_ada_pool: Bool,
  pool_policy_id: PolicyId,
  pool_input_datum: PoolDatum,
  pool_output_datum: PoolDatum,
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
      pool_policy_id,
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
    } - pool_input_datum.treasury_a
  let pool_input_b_liquidity = bs_input - pool_input_datum.treasury_b

  when pool_redeemer is {
    Swap { swap_a_to_b, provided } -> {
      let Liquidity {
        expected_a_liquidity,
        expected_b_liquidity,
        received,
        treasury_diff_a,
        treasury_diff_b,
      } =
        new_liquidity(
          pool_input_a_liquidity,
          pool_input_b_liquidity,
          provided,
          swap_a_to_b,
          pool_input_datum,
        )

      let is_pool_value_correct = {
        let a_ada_asset_check =
          if is_ada_pool {
            (as_output >= expected_a_liquidity + pool_oil + pool_output_datum.treasury_a)?
          } else {
            and {
              (as_output >= expected_a_liquidity + pool_output_datum.treasury_a)?,
              (ada_output >= pool_oil)?,
            }
          }

        let b_asset_check =
          bs_output >= expected_b_liquidity + pool_output_datum.treasury_b
        let shares_asset_check = shares_output == shares_input
        and {
          a_ada_asset_check?,
          b_asset_check?,
          shares_asset_check?,
        }
      }

      let datum_check = and {
          are_pool_datums_same_without_treasuries(
            pool_input_datum,
            pool_output_datum,
          ),
          pool_output_datum.treasury_a == pool_input_datum.treasury_a + treasury_diff_a,
          pool_output_datum.treasury_b == pool_input_datum.treasury_b + treasury_diff_b,
        }

      and {
        datum_check?,
        is_pool_value_correct?,
        (provided > 0)?,
        (received > 0)?,
      }
    }

    AddLiquidity { a_add, b_add, x_swap } -> {
      // when one of the a_add or b_add is zero, that's a zap-in
      // zap-ins are mathematically the same as a swap
      // and a balanced add liquidity afterwards
      //
      // the swap portion has to be calculated off-chain,
      // the contract just verifies it
      // the correct swap value produces a subsequent add liquidity
      // with roughly equal shares increase from both tokens
      //
      // the contract calculates the expected shares from swap X
      // and from (swap X - 1) and ensures the given swap X indeed
      // produces rougly equal shares for the user
      //
      // for normal liquidity provision swap X is ignored

      let shares_total_emitted = max_share_tokens - shares_input

      if a_add == 0 {
        // This is a Zap-In with B since a_add == 0,
        // we need to swap some B to get A
        let b_swap = x_swap

        // shares received with the provided intended swap value
        let Liquidity {
          expected_a_liquidity: a_pool_interim,
          expected_b_liquidity: b_pool_interim,
          // a_received is then added as liquidity
          received: a_received,
          treasury_diff_a,
          treasury_diff_b,
        } =
          new_liquidity(
            pool_input_a_liquidity,
            pool_input_b_liquidity,
            b_swap,
            False,
            pool_input_datum,
          )
        let b_add_liquidity = b_add - b_swap
        let shares_earned_from_a =
          a_received * shares_total_emitted / a_pool_interim
        let shares_earned_from_b =
          b_add_liquidity * shares_total_emitted / b_pool_interim

        // shares received if the swap value were -1 from the intended one
        let Liquidity {
          // pool liquidity after swap, before add liquidity
          expected_a_liquidity: a_pool_interim1,
          expected_b_liquidity: b_pool_interim1,
          received: a_received1,
          treasury_diff_a: _,
          treasury_diff_b: _,
        } =
          new_liquidity(
            pool_input_a_liquidity,
            pool_input_b_liquidity,
            b_swap - 1,
            False,
            pool_input_datum,
          )
        let b_add_liquidity1 = b_add - ( b_swap - 1 )
        let shares_earned_from_a1 =
          a_received1 * shares_total_emitted / a_pool_interim1
        let shares_earned_from_b1 =
          b_add_liquidity1 * shares_total_emitted / b_pool_interim1

        let shares_earned = min(shares_earned_from_a, shares_earned_from_b)
        let expected_shares_output = shares_input - shares_earned

        let a_ada_asset_check =
          if is_ada_pool {
            (as_output >= a_pool_interim + a_received + pool_oil + pool_output_datum.treasury_a)?
          } else {
            and {
              (as_output >= a_pool_interim + a_received + pool_output_datum.treasury_a)?,
              (ada_output >= pool_oil)?,
            }
          }
        let b_asset_check =
          bs_output >= b_pool_interim + b_add_liquidity + pool_output_datum.treasury_b
        let shares_asset_check = shares_output == expected_shares_output
        let datum_check = and {
            are_pool_datums_same_without_treasuries(
              pool_input_datum,
              pool_output_datum,
            ),
            pool_output_datum.treasury_a == pool_input_datum.treasury_a + treasury_diff_a,
            pool_output_datum.treasury_b == pool_input_datum.treasury_b + treasury_diff_b,
          }

        and {
          // failing this means you need to swap more
          (shares_earned_from_b <= shares_earned_from_a)?,
          // failing this means you need to swap less
          (shares_earned_from_b1 > shares_earned_from_a1)?,
          // some values don't make sense
          (b_swap > 0)?,
          // some values don't make sense
          (b_swap < b_add)?,
          datum_check?,
          a_ada_asset_check?,
          b_asset_check?,
          shares_asset_check?,
          (b_add > 0)?,
          (shares_earned > 0)?,
        }
      } else if b_add == 0 {
        // This is a Zap-In since b_add == 0,
        // we need to swap some A to get B
        let a_swap = x_swap

        // shares received with the provided intended swap value
        let Liquidity {
          // pool liquidity after swap, before add liquidity
          expected_a_liquidity: a_pool_interim,
          expected_b_liquidity: b_pool_interim,
          // b_received is then added as liquidity
          received: b_received,
          treasury_diff_a,
          treasury_diff_b,
        } =
          new_liquidity(
            pool_input_a_liquidity,
            pool_input_b_liquidity,
            a_swap,
            True,
            pool_input_datum,
          )
        let a_add_liquidity = a_add - a_swap
        let shares_earned_from_a =
          a_add_liquidity * shares_total_emitted / a_pool_interim
        let shares_earned_from_b =
          b_received * shares_total_emitted / b_pool_interim

        // shares received if the swap value were -1 from the intended one
        let Liquidity {
          expected_a_liquidity: a_pool_interim1,
          expected_b_liquidity: b_pool_interim1,
          received: b_received1,
          treasury_diff_a: _,
          treasury_diff_b: _,
        } =
          new_liquidity(
            pool_input_a_liquidity,
            pool_input_b_liquidity,
            a_swap - 1,
            True,
            pool_input_datum,
          )
        let a_add_liquidity1 = a_add - ( a_swap - 1 )
        let shares_earned_from_a1 =
          a_add_liquidity1 * shares_total_emitted / a_pool_interim1
        let shares_earned_from_b1 =
          b_received1 * shares_total_emitted / b_pool_interim1

        let shares_earned = min(shares_earned_from_a, shares_earned_from_b)
        let expected_shares_output = shares_input - shares_earned

        let a_ada_asset_check =
          if is_ada_pool {
            (as_output >= a_pool_interim + pool_oil + pool_output_datum.treasury_a)?
          } else {
            and {
              (as_output >= a_pool_interim + pool_output_datum.treasury_a)?,
              (ada_output >= pool_oil)?,
            }
          }
        let b_asset_check =
          bs_output >= b_pool_interim + b_received + pool_output_datum.treasury_b
        let shares_asset_check = shares_output == expected_shares_output
        let datum_check = and {
            are_pool_datums_same_without_treasuries(
              pool_input_datum,
              pool_output_datum,
            ),
            pool_output_datum.treasury_a == pool_input_datum.treasury_a + treasury_diff_a,
            pool_output_datum.treasury_b == pool_input_datum.treasury_b + treasury_diff_b,
          }

        and {
          // failing this check means you need to swap more
          (shares_earned_from_a <= shares_earned_from_b)?,
          // failing this check means you need to swap less
          (shares_earned_from_a1 > shares_earned_from_b1)?,
          // some values don't make sense
          (a_swap > 0)?,
          // some values don't make sense
          (a_swap < a_add)?,
          datum_check?,
          a_ada_asset_check?,
          b_asset_check?,
          shares_asset_check?,
          (a_add > 0)?,
          (shares_earned > 0)?,
        }
      } else {
        // This is a balanced liquidity provision
        let shares_earned_from_a =
          a_add * shares_total_emitted / pool_input_a_liquidity
        let shares_earned_from_b =
          b_add * shares_total_emitted / pool_input_b_liquidity
        let shares_earned = min(shares_earned_from_a, shares_earned_from_b)
        let expected_shares_output = shares_input - shares_earned

        let a_asset_check = as_output == as_input + a_add
        let b_asset_check = bs_output == bs_input + b_add
        let ada_check = ada_output >= pool_oil
        let shares_asset_check = shares_output == expected_shares_output
        let datum_check = pool_input_datum == pool_output_datum
        and {
          datum_check?,
          a_asset_check?,
          b_asset_check?,
          ada_check?,
          shares_asset_check?,
          (a_add > 0)?,
          (b_add > 0)?,
          (shares_earned > 0)?,
        }
      }
    }

    WithdrawLiquidity { shares_add } -> {
      let shares_total_emitted = max_share_tokens - shares_input
      let a_remove = shares_add * pool_input_a_liquidity / shares_total_emitted
      let b_remove = shares_add * pool_input_b_liquidity / shares_total_emitted
      let expected_shares_output = shares_input + shares_add
      let a_asset_check = as_output == as_input - a_remove
      let ada_check = ada_output >= pool_oil
      let b_asset_check = bs_output == bs_input - b_remove
      let shares_asset_check = shares_output == expected_shares_output
      let datum_check = pool_input_datum == pool_output_datum
      and {
        datum_check?,
        a_asset_check?,
        ada_check?,
        b_asset_check?,
        shares_asset_check?,
        (shares_add > 0)?,
        (a_remove > 0)?,
        (b_remove > 0)?,
      }
    }

    WithdrawTreasury -> {
      let datum_check = and {
          are_pool_datums_same_without_treasuries(
            pool_input_datum,
            pool_output_datum,
          ),
          pool_output_datum.treasury_a == 0,
          pool_output_datum.treasury_b == 0,
        }
      let authority_check =
        list.any(
          inputs,
          fn(input) {
            quantity_of(
              input.output.value,
              pool_input_datum.treasury_authority_policy_id,
              pool_input_datum.treasury_authority_asset_name,
            ) > 0
          },
        )
      let assets_check = {
        let a_assets_check = as_output == as_input - pool_input_datum.treasury_a
        let b_assets_check = bs_output == bs_input - pool_input_datum.treasury_b
        let ada_check = ada_output >= pool_oil
        and {
          a_assets_check,
          b_assets_check,
          ada_check,
        }
      }
      let spam_check =
        pool_input_datum.treasury_a > 0 || pool_input_datum.treasury_b > 0
      and {
        spam_check?,
        datum_check?,
        authority_check?,
        assets_check?,
      }
    }

    Donate -> and {
        (pool_input_datum == pool_output_datum)?,
        (ada_output >= lovelace_of(pool_input_value))?,
        (as_output >= as_input)?,
        (bs_output >= bs_input)?,
        (shares_output == shares_input)?,
      }
  }
}

type Liquidity {
  expected_a_liquidity: Int,
  expected_b_liquidity: Int,
  received: Int,
  treasury_diff_a: Int,
  treasury_diff_b: Int,
}

fn new_liquidity(
  pool_input_a_liquidity: Int,
  pool_input_b_liquidity: Int,
  provided: Int,
  swap_a_to_b: Bool,
  pool_input_datum: PoolDatum,
) -> Liquidity {
  when pool_input_datum.fee_from is {
    InputToken ->
      if swap_a_to_b {
        // fee in a, pay a, get b
        new_liquidity_a_to_b_fee_from_a(
          pool_input_a_liquidity,
          pool_input_b_liquidity,
          provided,
          pool_input_datum.swap_fee_points_a_to_b,
          pool_input_datum.treasury_fee_points_a_to_b,
          pool_input_datum.fee_basis,
        )
      } else {
        // fee in b, pay b, get a
        new_liquidity_b_to_a_fee_from_b(
          pool_input_a_liquidity,
          pool_input_b_liquidity,
          provided,
          pool_input_datum.swap_fee_points_b_to_a,
          pool_input_datum.treasury_fee_points_b_to_a,
          pool_input_datum.fee_basis,
        )
      }
    OutputToken ->
      if swap_a_to_b {
        // fee in b, pay a, get b
        new_liquidity_a_to_b_fee_from_b(
          pool_input_a_liquidity,
          pool_input_b_liquidity,
          provided,
          pool_input_datum.swap_fee_points_a_to_b,
          pool_input_datum.treasury_fee_points_a_to_b,
          pool_input_datum.fee_basis,
        )
      } else {
        // fee in a, pay b, get a
        new_liquidity_b_to_a_fee_from_a(
          pool_input_a_liquidity,
          pool_input_b_liquidity,
          provided,
          pool_input_datum.swap_fee_points_b_to_a,
          pool_input_datum.treasury_fee_points_b_to_a,
          pool_input_datum.fee_basis,
        )
      }
    TokenA ->
      if swap_a_to_b {
        // fee in a, pay a, get b
        new_liquidity_a_to_b_fee_from_a(
          pool_input_a_liquidity,
          pool_input_b_liquidity,
          provided,
          pool_input_datum.swap_fee_points_a_to_b,
          pool_input_datum.treasury_fee_points_a_to_b,
          pool_input_datum.fee_basis,
        )
      } else {
        // fee in a, pay b, get a
        new_liquidity_b_to_a_fee_from_a(
          pool_input_a_liquidity,
          pool_input_b_liquidity,
          provided,
          pool_input_datum.swap_fee_points_b_to_a,
          pool_input_datum.treasury_fee_points_b_to_a,
          pool_input_datum.fee_basis,
        )
      }
    TokenB ->
      if swap_a_to_b {
        // fee in b, pay a, get b
        new_liquidity_a_to_b_fee_from_b(
          pool_input_a_liquidity,
          pool_input_b_liquidity,
          provided,
          pool_input_datum.swap_fee_points_a_to_b,
          pool_input_datum.treasury_fee_points_a_to_b,
          pool_input_datum.fee_basis,
        )
      } else {
        // fee in b, pay b, get a
        new_liquidity_b_to_a_fee_from_b(
          pool_input_a_liquidity,
          pool_input_b_liquidity,
          provided,
          pool_input_datum.swap_fee_points_b_to_a,
          pool_input_datum.treasury_fee_points_b_to_a,
          pool_input_datum.fee_basis,
        )
      }
  }
}

fn new_liquidity_b_to_a_fee_from_a(
  pool_input_a_liquidity: Int,
  pool_input_b_liquidity: Int,
  provided: Int,
  swap_fee_points: Int,
  treasury_fee_points: Int,
  fee_basis: Int,
) -> Liquidity {
  let new_b = pool_input_b_liquidity + provided
  let new_a = div_ceil(pool_input_b_liquidity * pool_input_a_liquidity, new_b)
  let received_plus_fee = pool_input_a_liquidity - new_a
  let swap_fee = div_ceil(received_plus_fee * swap_fee_points, fee_basis)
  let treasury_fee =
    div_ceil(received_plus_fee * treasury_fee_points, fee_basis)
  Liquidity {
    expected_a_liquidity: new_a,
    expected_b_liquidity: new_b,
    received: received_plus_fee - swap_fee - treasury_fee,
    treasury_diff_a: treasury_fee,
    treasury_diff_b: 0,
  }
}

fn new_liquidity_a_to_b_fee_from_b(
  pool_input_a_liquidity: Int,
  pool_input_b_liquidity: Int,
  provided: Int,
  swap_fee_points: Int,
  treasury_fee_points: Int,
  fee_basis: Int,
) -> Liquidity {
  let new_a = pool_input_a_liquidity + provided
  let new_b = div_ceil(pool_input_a_liquidity * pool_input_b_liquidity, new_a)
  let received_plus_fee = pool_input_b_liquidity - new_b
  let swap_fee = div_ceil(received_plus_fee * swap_fee_points, fee_basis)
  let treasury_fee =
    div_ceil(received_plus_fee * treasury_fee_points, fee_basis)
  Liquidity {
    expected_a_liquidity: new_a,
    expected_b_liquidity: new_b,
    received: received_plus_fee - swap_fee - treasury_fee,
    treasury_diff_a: 0,
    treasury_diff_b: treasury_fee,
  }
}

fn new_liquidity_a_to_b_fee_from_a(
  pool_input_a_liquidity: Int,
  pool_input_b_liquidity: Int,
  provided: Int,
  swap_fee_points: Int,
  treasury_fee_points: Int,
  fee_basis: Int,
) -> Liquidity {
  let swap_fee = div_ceil(provided * swap_fee_points, fee_basis)
  let treasury_fee = div_ceil(provided * treasury_fee_points, fee_basis)
  let new_a = pool_input_a_liquidity + provided - treasury_fee
  let new_b =
    div_ceil(pool_input_a_liquidity * pool_input_b_liquidity, new_a - swap_fee)
  Liquidity {
    expected_a_liquidity: new_a,
    expected_b_liquidity: new_b,
    received: pool_input_b_liquidity - new_b,
    treasury_diff_a: treasury_fee,
    treasury_diff_b: 0,
  }
}

fn new_liquidity_b_to_a_fee_from_b(
  pool_input_a_liquidity: Int,
  pool_input_b_liquidity: Int,
  provided: Int,
  swap_fee_points: Int,
  treasury_fee_points: Int,
  fee_basis: Int,
) -> Liquidity {
  let swap_fee = div_ceil(provided * swap_fee_points, fee_basis)
  let treasury_fee = div_ceil(provided * treasury_fee_points, fee_basis)
  let new_b = pool_input_b_liquidity + provided - treasury_fee
  let new_a =
    div_ceil(pool_input_a_liquidity * pool_input_b_liquidity, new_b - swap_fee)
  Liquidity {
    expected_a_liquidity: new_a,
    expected_b_liquidity: new_b,
    received: pool_input_a_liquidity - new_a,
    treasury_diff_a: 0,
    treasury_diff_b: treasury_fee,
  }
}

fn are_pool_datums_same_without_treasuries(in: PoolDatum, out: PoolDatum) {
  let PoolDatum {
    a_policy_id: in_a_policy_id,
    a_asset_name: in_a_asset_name,
    b_policy_id: in_b_policy_id,
    b_asset_name: in_b_asset_name,
    treasury_authority_policy_id: in_treasury_authority_policy_id,
    treasury_authority_asset_name: in_treasury_authority_asset_name,
    treasury_a: _in_treasury_a,
    treasury_b: _in_treasury_b,
    fee_from: in_fee_from,
    treasury_fee_points_a_to_b: in_treasury_fee_points_a_to_b,
    treasury_fee_points_b_to_a: in_treasury_fee_points_b_to_a,
    swap_fee_points_a_to_b: in_swap_fee_points_a_to_b,
    swap_fee_points_b_to_a: in_swap_fee_points_b_to_a,
    fee_basis: in_fee_basis,
    shares_asset_name: in_shares_asset_name,
  } = in

  let PoolDatum {
    a_policy_id: out_a_policy_id,
    a_asset_name: out_a_asset_name,
    b_policy_id: out_b_policy_id,
    b_asset_name: out_b_asset_name,
    treasury_authority_policy_id: out_treasury_authority_policy_id,
    treasury_authority_asset_name: out_treasury_authority_asset_name,
    treasury_a: _out_treasury_a,
    treasury_b: _out_treasury_b,
    fee_from: out_fee_from,
    treasury_fee_points_a_to_b: out_treasury_fee_points_a_to_b,
    treasury_fee_points_b_to_a: out_treasury_fee_points_b_to_a,
    swap_fee_points_a_to_b: out_swap_fee_points_a_to_b,
    swap_fee_points_b_to_a: out_swap_fee_points_b_to_a,
    fee_basis: out_fee_basis,
    shares_asset_name: out_shares_asset_name,
  } = out

  and {
    in_a_policy_id == out_a_policy_id,
    in_a_asset_name == out_a_asset_name,
    in_b_policy_id == out_b_policy_id,
    in_b_asset_name == out_b_asset_name,
    in_fee_from == out_fee_from,
    in_treasury_authority_policy_id == out_treasury_authority_policy_id,
    in_treasury_authority_asset_name == out_treasury_authority_asset_name,
    in_treasury_fee_points_a_to_b == out_treasury_fee_points_a_to_b,
    in_treasury_fee_points_b_to_a == out_treasury_fee_points_b_to_a,
    in_swap_fee_points_a_to_b == out_swap_fee_points_a_to_b,
    in_swap_fee_points_b_to_a == out_swap_fee_points_b_to_a,
    in_fee_basis == out_fee_basis,
    in_shares_asset_name == out_shares_asset_name,
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
