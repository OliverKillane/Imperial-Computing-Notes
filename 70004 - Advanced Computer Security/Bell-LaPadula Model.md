## Definition
A state machine model for access control focusing on [[Confidentiality]].
- **no read up, no write down**

| Policy              | Description                                                              |
| ------------------- | ------------------------------------------------------------------------ |
| Simple Security     | A subject at a given level may not read an object at a higher level.     |
| Star (`*`) Security | A subject at a given level may not write to any object at a lower level. |
| Discretionary       | Use an access matrix to specify the discretionary access control.        |
*[Bell–LaPadula model - Wikipedia](https://en.wikipedia.org/wiki/Bell%E2%80%93LaPadula_model)*
## Attributes
- Focuses on [[Confidentiality]], rather than [[Integrity]] as with the [[Biba Model]]