This project maintains an OWL ontology file conversion for the Langual.org XML thesaurus
Food Source facet data.  The plan is to enable Langual's thesaurus file to be updated over time,
and the owl file to be updated as needed.  VERY BRIEFLY,

The main file to look at is LANGUAL_import.owl.  It is run by 

   > python conversion.py

This program may need a few python modules loaded up.  It can take a number of minutes to generate
if database.json is already established; it will take much longer to run if database.json has been
deleted since it fetches NCBITaxon related information using EOL API.

It generates ontofox-ncbitaxon-spec.txt which one must load into OntoFox in order to get the
full NCBITaxon_import.owl file below

LANGUAL_import.owl imports:
- envo-food-terms.owl (constant file)
- NCBITaxon_import.owl


