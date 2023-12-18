## Definition
*Binary JSON* / a serialized json format, better for storage and transmission.
## Data Model
Nested objects of unordered key-value pairs, as well as ordered arrays of objects.
- Objects can contain references
- Embedded/nested structure means 1-1 or 1-many relationships can be implemented without joins.
```json
{
	"_id" : "102423", // for mongoDB
	"city": "LONDON",
	"population": 9000000,
	"nation": "UK",
	"council" : {
		"name" : "London Assembly",
		"description": "Manages london or something..."
	},
	"airports" : [
		{
			"name" : "Heathrow",
			"runways" : 2,
		},
		{
			"name" : "Stansted",
			"runways": 1,
		}
	]
}
```
