## Definition
The changes in virus ([[Malware]]) and antivirus techniques as a result of improvements in the other.
## Stages
### Start
| Virus | Antivirus |
| ---- | ---- |
| When the file is executed, modify other files to infect/include a copy of the virus. | Identify common virus code sequences (signatures), and can to find instances of the sequences in files. |
*Antivirus is bound by the ability to scan files, and the current database of signatures to match.*
### Entry Point Scanning
| Virus | Antivirus |
| ---- | ---- |
| Place at the entry point of a program (or directly reachable from) and make the virus as small as possible to make matching signatures more difficult. | Scan and traverse entry points & code reachable from them to find jumps to virus code |
### Encryption
| Virus | Antivirus |
| ---- | ---- |
| Encrypt the virus's body on disk, and include a decryption routine to unencrypt into memory for execution. can then jump to this code/start of buffer. | Decryption routines (packers) are easy to fingerprint/get signature. |
*Virus needs to use new keys when adding encrypted code to new files*
### Polymorphic
| Virus | Antivirus |
| ---- | ---- |
| Use a mutation engine to generate different encryption/decryption routine pairs that are semantically identical, but are represented differently (so antivirus signatures not effective)  | A custom detection program is used to recognise different engines. |
*Antivirus can use Generic Decryption, where an emulator and signature matching engine is used to emulate and find viruses decrypting themselves. Snapshots of memory/disk at intervals can also be used to find viruses mid-decryption.*
- *Virus can deliberately slow down and make emulation more difficult (e.g. adds sleeps)*
- *Typically both signature-based (scanning) and runtime (emulation-based) techniques are used.*
## False-Positives
It is important for the antivirus not to flag uninfected files as infected
- For the trust of the user
- To avoid damaging the systems they run on.

For example in May 2007 Norton/Symantec mistakenly removed essential OS system files, bricking thousands of PCs.

(Also May 2007) Norton/Symantec falsely detected an executable required for PegasusMail as a Trojan, this included 3 releases of the software.

> *"On the basis that Norton/Symantec has done this for every one of the last three releases of Pegasus Mail, we can only condemn this product as too flawed to use, and recommend in the strongest terms that our users cease using it in favor of alternative, less buggy anti-virus packages"*
> **- PegasusMail**

Users losing the minds here:
- PegasusMail falsely detected as a trojan: [How to contact Symantec?? | PMAIL COMMUNITY](https://community.pmail.com/index.php?u=/topic/273/how-to-contact-symantec)
- Automatic Driver Update bricking motherboards: [Norton 360 killed my pc after update | Norton Community](https://community.norton.com/en/forums/norton-360-killed-my-pc-after-update)
Many other issues have occurred with AntiViruses removing system critical files. 