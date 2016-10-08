This project maintains an OWL ontology file conversion for the Langual.org XML thesaurus
Food Source facet data.  The plan is to enable Langual's thesaurus file to be updated over time,
and the owl file to be updated as needed.  

##To view

Briefly, the main file to look at is LANGUAL_import.owl (in Protege or another OWL ontology editor); 
it will import the envo-food-terms.owl and NCBITaxon_import.owl files too.  Use Stanford's free [Protege](http://protege.stanford.edu) ontology editor to load the main file, and browse the Langual hierarchy under the "Classes" tab.

##To regenerate the files

LANGUAL_import.owl is generated by the conversion.py program which reads in the LanguaL2014.XML file,
compares its contents to the database.json import control data structure, adds new content and state information
to the json database, and then writes the OWL file as well as an OntoFox compatible ontofox-ncbitaxon-spec.txt 
file.  

   > python conversion.py
  
This program may need a few python modules loaded up.  It can take a number of minutes to generate
if database.json is already established; it will take much longer to run if database.json has been
deleted since it fetches NCBITaxon related information using the EOL.org API.

To refresh the NCBITaxon_import.owl file, load the .txt file into the http://ontofox.hegroup.org/ form (section 2. data input using local text file) in order to regenerate and download the .owl output.
