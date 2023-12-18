## Definition
Document Type Definition. Describes rules for checking if an [[XML]] document is well-formed/valid.

| Example |Description |
|-|-|
| `<!DOCTYPE name [...]>` | Declares the root node as being the element `name`|
| `<!ELEMENT name (TYPE)>` | Declare a type of element called `name` that has type `TYPE` |
| `<!ELEMENT parent (child1, child2)>` | Declares an element type `parent`, which always has children `child1` and `child2` |
| `#PCDATA` | The type for parsed character data (strings) | 
## Examples
### Notes
```dtd
<?XML version = “1.0”?>
<!DOCTYPE note[
	<!Element note(to,from,heading,notebody)>
	<!Element to(#PCDATA)>
	<!Element from(#PCDATA)>
	<!Element heading(#PCDATA)>
	<!Element notebody(#PCDATA)> 
]>
```
```xml
<note>
	<to>CS 731</to>
	<from>21456687</from>
	<heading>presentation</heading>
	<notebody>XML introduction</notebody>
</note>
```
- `PCDATA` is parsed character data / strings
