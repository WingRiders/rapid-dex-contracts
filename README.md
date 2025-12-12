# Rapid DEX Contracts

## Building

To build the cotracts you need `aiken v1.1.9`.
You can install it by running `aikup` in the root of the repository.

To build the contracts without the traces run the following command:
```sh
aiken build
```

If you want the traces included run the following command:
```sh
aiken build -t verbose
```

The artifacts in the repository export the contracts with traces.

## Deployment & Testing

There is a unit test suite you can run with the following command:
```sh
aiken check
```

Deployment scripts and further testing instructions are maintained in the [rapid-dex](https://github.com/WingRiders/rapid-dex) repository.

For details on deploying the contract to the Cardano testnet, refer to the [deployment guide](https://github.com/WingRiders/rapid-dex/blob/main/docs/deployment.md).

For running tests, see the [testing guide](https://github.com/WingRiders/rapid-dex/blob/m1-demo/docs/testing.md).
