## iOS Structure

| Component          | Description                                                                         |
| ------------------ | ----------------------------------------------------------------------------------- |
| kernel             | Based on the Mach kernel from Mac OS X                                              |
| Core OS & Services | APIs for files, network, SQLite, POSIX threads, UNIX sockets, and security services |
| Media Layer        | Foundational framework, object oriented collections, file management, network.      |
Implemented in C, Objective-C and swift.

## System Security
Hardware Root of Trust (immutable code in the boot rom) ensures 

| Feature                    | Description                                                                                                                                      |
| -------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------ |
| Secure Boot Chain          | All startup processes are crypto-signed by Apple to ensure integrity. Only after **chain of trust** is verified does the iOS kernel start.       |
| Secure Enclave Coprocessor | A secure crypto-processor (secure boot with encrypted memory) provides cryptographic functions and key storage. Processes fingerprint/face data. |
| Touch ID/Face ID sensors   | Data for authentication kept in secure enclave on device.                                                                                        |
## App Security

| Feature                 | Description                                                                                                                                                                                                                     |
| ----------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Mandatory Code Signing  | All apps must be signed with an apple-issued ID certificate                                                                                                                                                                     |
| Sandboxing              | Each app executes in its own sandbox to prevent access to other application's data. 3rd party apps and the majority of iOS run under a non-privileged *'mobile'* user. Inter-app communication on facilitated through iOS APIs. |
| Entitlements            | Access to user information (e.g. camera, bluetooth, internet) is declared by the app (fixed, and part of the app's signature), some must be dynamically requested (e.g. location).                                              |
| Encryption              | Apps can use iOS APIs to use built-in hardware encryption.                                                                                                                                                                      |
| System Extension Points | Extensions (e.g. 3rd party filter for the camera app) run as their own processes (isolated from the extended application).                                                                                                      |
