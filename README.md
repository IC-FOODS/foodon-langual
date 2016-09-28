This project maintains an OWL ontology file conversion for the Langual.org XML thesaurus
Food Source facet data.  The plan is to enable Langual's thesaurus file to be updated over time,
and the owl file to be updated as needed.  VERY BRIEFLY,

The main file to look at is LANGUAL_import.owl (in Protege or another OWL ontology editor).

LANGUAL_import.owl is generated by the conversion.py program which reads in the LanguaL2014.XML file,
compares its contents to the database.json import control data structure, adds new content and state information
to the json database, and then writes the OWL file as well as an OntoFox compatible ontofox-ncbitaxon-spec.txt 
file which one must load into OntoFox in order to get the companion NCBITaxon_import.owl generated.

   > python conversion.py

This program may need a few python modules loaded up.  It can take a number of minutes to generate
if database.json is already established; it will take much longer to run if database.json has been
deleted since it fetches NCBITaxon related information using the EOL.org API.
