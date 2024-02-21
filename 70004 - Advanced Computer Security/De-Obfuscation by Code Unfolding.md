## Definition
A [[Dynamic Detection]], rather than transforming the text source of [[Obfuscation|obfuscated code]], a tool uses its own isolated javascript runtime to get a trace of the behaviour of the code.

This behaviour can then be used to fingerprint the malware. Other obfuscations of the same code can have different representations, but will have the same behaviour.

Analogous to [[Virus-Antivirus Co-Evolution|signature detection]].