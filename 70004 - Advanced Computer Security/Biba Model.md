## Definition
A state machine for access control focusing on [[Integrity]].
- **no write up, no read down**

| Property             | Description                                                                         |
| -------------------- | ----------------------------------------------------------------------------------- |
| Simple Integrity     | Subject at a given integrity level must not read data at a lower level.             |
| Star (`*`) Integrity | Subject at a given level on integrity must not write to data at a higher level.     |
| Invocation Property  | A process cannot request higher access, only with subjects at equal or lower level. |
