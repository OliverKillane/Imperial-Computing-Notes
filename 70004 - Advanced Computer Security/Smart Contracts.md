## Definition
A contract (e.g. option contract) written as a program, and stored on the blockchain to be monitored, and executed when conditions are met (e.g. option expiry).

As the contracts are executed in a distributed context, there are some restrictions:
- Deterministic execution (so separate executions are the same)
- Single threaded (usually) to ensure determinism

Execution fees are paid by the contract owner to the contract executor/miner.
- Denial of service discouraged as it is expensive.
- Incentive for miners to provide compute to execute contracts.
- Contract owners can specify how much they are willing to pay for execution (the *gas* to limit costs and the cost per unit of *gas*).
## Gas
The [[Smart Contracts#[Ethereum Virtual Machine](https //ethereum.org/developers/docs/evm)|evm]] defines the gas cost of bytecode instructions.
- A contract can execute until it runs out of the gas it is provisioned (out of gas exception)
When relying on external data structures (e.g. loop over some bag of accounts), the gas needed by a contract is difficult to determine.

*Wallet Griefing* attacks can take advantage of this to force contracts to run out of gas.
## Languages
### [Solidity](https://soliditylang.org/)
A javascript-inspired, turing-complete, statically typed smart contract language.
### [Ethereum Virtual Machine](https://ethereum.org/developers/docs/evm)
A decentralized virtual machine for running contracts (written in the EVM bytecode)
- Can send transactions to the Ethereum network to create new contracts, invoke contract functions, transfer contracts, and transfer ether cryptocurrency.
- The sequence of transactions on the blockchain determines user balances and the state of contracts.
## Attacks
- [A Survey of Ethereum Smart Contract Security: Attacks and Detection | Distributed Ledger Technologies: Research and Practice (acm.org)](https://dl.acm.org/doi/10.1145/3643895)
### DAO
[[TODO]] Serious enough to result in a [[Blockchain Fork]]