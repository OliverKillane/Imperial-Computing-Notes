List:
- [Intel Pin Tool](https://www.intel.com/content/www/us/en/developer/articles/tool/pin-a-dynamic-binary-instrumentation-tool.html)
- [CompCert](https://compcert.org/)
- Infer
- [[Coverity]]
- GrammaTech
## Sound and Complete
| Kind | Sets | Description |
| ---- | ---- | ---- |
| **Complete** | $$Real \ Errors \subseteq Reported \ Errors$$ | All real errors are reported. |
| **Sound** | $$Reported \ Errors \subseteq Real \ Errors$$  | No false errors are reported. |
Ideally a tool would be sound and complete, however that problem is usually undecidable or expensive to compute.
- Many tools are *Sound but Incomplete* and attempt to help find bugs, rather than verify a program.