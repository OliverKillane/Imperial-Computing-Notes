## Definition
> *How can Bob be sure he is communicating with Alice?*

| Auth | Description |
| ---- | ---- |
| Client | Server verifies client's ID |
| Server | Client verifies server's ID |
| Mutual | Client & Server Authentication |
The authenticated user is the **principal**.

Can combine the following methods (e.g. chip&pin cards).
### By Knowledge
Users presents some secret information verified by the authenticator.
- Passwords are simple to implement & understand, but can be vulnerable to cracking if small, theft if stored insecurely, or vulnerable if the same password is used for another compromised authentication.
- [[One Time Passcode]]

### By Possessions
- [[One Time Passcode]] cards (generates a new code for each login - example HSBC)
- Smart Card that stores a secret, used in a card reader
- [[Yubikey]]
- [[Browser Cookies]] can contain authentication information.
Relies on the difficulty of forging the device/token/key.
### By Identity
Similar to possession, e.g. [[Biometrics]] 
- [[Biometrics]] can be inaccurate (false positive rate vs false negative rate).

