## Definition
A blockchain is a decentralised, distributed, public ledger used to store an immutable record of transactions, with each dependent on the last.

Avoids the double spending problem (sending two transactions that independently succeed, but there is not enough capital to cover both).

| Property | Why |
| ---- | ---- |
| [[Non-Reputation]] | The chain is immutable, and records cannot be changed retrospectively without it being obvious/breaking chain |
| [[Auditability]] | All participants can see the chain (distributed integrity) |
| [[Availability]] | The system is distributed, no single node failure can bring down the blockchain |
The main application is cryptocurrency, allowing for unhindered & mostly-unregulated transactions.
- Cannot revert payments
- Mostly anonymous
- No security intermediaries used, can hold own keys
## Consensus
| Type | Users | Description |
| ---- | ---- | ---- |
| Proof of Work | BTC | After a new block is added, it is validated by guessing a hash. It makes it too resource intensive to take over the network, which would be required to fake a transaction. |
| Proof of Stake | ETH | Validators for new blocks are chosen by the number of staked coins they have.  |
| Delegated Proof of Stake | EOS | Smaller nodes delegate their stake to larger nodes to allow then to participate in *Proof of Stake*. |
| Proof of Authority | Quorum | Whitelisted authorities must have a quorum to create new blocks. |
Proof of stake is vulnerable to the [[51% Attack]].