## Definition
Special devices for storing private keys (incl coins - e.g. [[Crypto-Currency]]).
- Secure in hardware (can only perform the required key storage functions)
- airgapped / disconnected, so unavailable for attackers
- many require transaction confirmation by physically pressing a button on the device
- encrypted with a pin, meaning they are unusable when phycially stolen
- can support multiple cryptocurrencies
- software often open source, so can be independently analysed
## Weaknesses
| Type | Description |
| ---- | ---- |
| [[Main-in-the-Middle Attack]] | compromising the connection between the hardware wallet, and the internet connection to the blockchain when the user make transactions. |
| [[Supply Chain Attack]] | Sabotaging supplied components of the wallets (or software), before they are supplied to consumers. |
### Examples
- [Researcher shows how vulnerable Ledger Nano S wallets are to hacking (thenextweb.com)](https://thenextweb.com/news/ledger-nano-s-hack-cryptocurrency)
- https://www.ledger.fr/2018/02/05/man-middle-attack-risk/
