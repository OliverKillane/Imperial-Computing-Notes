## Definition
Enforced orthogonally to [[Security Enhanced Linux#Type Enforcement]].
```python
f"{user}:{role}:{type}:{security_level}" with 
security_level = f"{sensitivity}:{category labels}"

# For example:
"user_u:user_r:user_t:s0-s2:c1,c4.c8"
```
- Sensitivity labels can instantiate a [[Bell-LaPadula Model]] or [[Biba Model]].
- Category labels are used for isolation (e.g. departments in a company-wide system, users on the system).
## Android
Encodes multiple users using category field:

| User      | Description             |
| --------- | ----------------------- |
| Primary   | Always Running          |
| Secondary | Background and Network  |
| Guest     | Only one user at a time |
Used for managed profiles:
- parental controls (restricted profile)
- company managed profiles (work accounts, samsung KNOX)
revmans