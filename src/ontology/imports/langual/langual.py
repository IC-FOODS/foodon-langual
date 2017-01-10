#!/usr/bin/python
# -*- coding: utf-8 -*-

""" 
**************************************************
conversion.py
Author: Damion Dooley

TO RUN: this needs "requests" module.
Running from CONDA environment:
source activate _test

This script uses the LanguaL.org food description thesaurus (published yearly in XML) 
to provide a differential update of a database.json data file.  From this the LANGUAL_import.owl
file is regenerated, and can then be imported into FOODON food ontology.  
It provides many of the facets - food source, cooking method, preservation method, etc. 

Key to the management of the database.json file and subsequent OWL file is that one can 
manually add elements to it which are not overwritten by subsequent LanguaL XML file imports.
Every LanguaL item maps over to any existing FOODON item by way of a hasDbXref: LANGUAL [id]" entry.
The database.json file has entities organized (the key) by LanguaL's FTC id, but entity itself includes the assigned FOODON id so that when it comes time to adjust an existing LANGUAL_import.owl file, entries are located/written out by FOODON ID.  

This script uses FOODON ids in range of 3400000 - 3499999 imported LanguaL terms.  
For now, Langual IDs are being coded in as FOODON_3[ 4 + (facet letter[A-Z] as 2 digit offset [00-12])][9999]

**************************************************
"""
import json
#from pprint import pprint
import optparse
import sys
import os.path
import xml.etree.ElementTree as ET
import codecs
import re
import time
import requests

try: #Python 2.7
    from collections import OrderedDict
except ImportError: # Python 2.6
    from ordereddict import OrderedDict

#FOR LOADING JSON AND PRESERVING ORDERED DICT SORTING. 
try:    
    import simplejson as json
except ImportError: # Python 2.6
    import json


CODE_VERSION = '0.0.4'

def stop_err( msg, exit_code=1 ):
    sys.stderr.write("%s\n" % msg)
    sys.exit(exit_code)

class MyParser(optparse.OptionParser):
    """
    Allows formatted help info.
    """
    def format_epilog(self, formatter):
        return self.epilog


class Langual(object):

    def __init__(self):

        # READ THIS FROM database.json
        self.database_path = './database.json' 
        self.ontology_name = 'langual_import'
        self.database = { #empty case.
            'index': OrderedDict(), 
            'version': 0 
        } 
        self.ontology_index = {}
        #self.foodon_maxid = 3400000  #Foodon Ids for LanguaL entries are currently mapped over from LanguaL ids directly.

        self.counts = {}
        self.has_taxonomy = 0
        self.has_ITIS = 0
        self.no_taxonomy = 0
        self.food_additive = 0
        # The time consuming part is writing the OWL file; can reduce this by skipping lots of entries
        self.owl_test_max_entry =  'Z9999' # 'B1100' # 
        self.output = ''
        self.version = 0
        # Lookup table to convert LanguaL to NCBITaxon codes; typos are: SCISUNFAM, SCITRI,
        self.ranklookup = OrderedDict([('SCIDIV','phylum'), ('SCIPHY','phylum'), ('SCISUBPHY','subphylum'), ( 'SCISUPCLASS','superclass'), ( 'SCICLASS','class'), ( 'SCIINFCLASS','infraclass'), ( 'SCIORD','order'), ( 'SCISUBORD','suborder'), ( 'SCIINFORD','infraorder'), ( 'SCISUPFAM','superfamily'), ( 'SCIFAM','family'), ( 'SCISUBFAM','subfamily'), ( 'SCISUNFAM', 'subfamily'), ( 'SCITRI','tribe'), ( 'SCITRIBE','tribe'), ( 'SCIGEN','genus'), ( 'SCINAM','species'), ( 'SCISYN','species')])
        
        # See full list of www.eol.org data sources at http://eol.org/api/docs/provider_hierarchies; only using ITIS now.
        self.EOL_providers = OrderedDict([('ITIS',903), ('INDEX FUNGORUM',596), ('Fishbase 2004',143), ('NCBI Taxonomy',1172)])
        self.NCBITaxon_lookup = {'ITIS':[],'INDEX FUNGORUM':[] }

        # Text mining regular expressions
        self.re_wikipedia_url = re.compile(r'http://en.wikipedia.org/wiki/(?P<reference>[^]]+)')
        self.re_duplicate_entry = re.compile(r'Duplicate entry of[^[]*\[(?P<id>[^\]]+)\]\*.') # e.g. "Duplicate entry of *CHILEAN CROAKER [B1814]*."
        # "\nEurope: E 230.\nCodex: INS 230."
        self.re_codex = re.compile(r'\nEurope: .*\.')
        self.re_europe = re.compile(r'\nCodex: .*\.')

        # e.g. <SCINAM>Balaenoptera bonaerensis Burmeister, 1867 [FAO ASFIS BFW]
        self.re_taxonomy = re.compile(r'<?(?P<rank>[A-Z]+)>(?P<name>[^\]]+) ?\[((?P<ref>([A-Z]+[0-9]*|2010 FDA Seafood List))|(?P<db>[A-Z 0-9]+) (?P<id>[^\]]+))]')


    def __main__(self, XMLfile, database, ontology):
        """
        Create memory-resident data structure of captured LanguaL items.  Includes:
            - ALL FOOD SOURCE ITEMS, including:
                - animals and plants which have taxonomy.
                - chemical food aditives which get converted to CHEBI ontology references.

        # Each self.database entity has a primary status for its record:
        status:
            'ignore': Do not import this LanguaL item.
            'import': Import as a primary ontology term.
            'deprecated': Import code but mark it as a hasDbArchaicXref:____ of other primary term.
                Arises when LanguaL term ids have been made archaic via merging or deduping.

            ... Descriptor inactivated. The descriptor is a synonym of *RED KINGKLIP [B1859]*.</AI>
            <RELATEDTERM>B2177</RELATEDTERM>

        """
        self.database_path = database
        self.ontology_name = ontology

        if os.path.isfile(self.database_path):
            self.database = self.get_database_JSON(self.database_path)
            self.database['version'] +=1
            # self.version = self.database['version']

        # Uncomment this to update database to latest CHEBI etc ids 
        # for LanguaL entities based on lookup.txt file.
        # Note, if trying to clense bad ontology ids further below, must run this script twice.
        #
        self.updateDatabaseOntologyIds('./lookup.txt')


        
        # Incoming raw XML database file
        tree = ET.parse(XMLfile) 
        root = tree.getroot()

        for child in root.iter('DESCRIPTOR'):
            
            # Place facet characters here to skip them
            category = child.find('FTC').text[0]

            # This isolates Product Types out to a separate database
            if self.ontology_name == 'langual_import':
                if category == 'A': continue
            elif category != 'A': continue

            entity = OrderedDict() # Barebones entity
            #Status ranges:
            #   'ignore' (don't import)
            #   'draft' (no one has looked at it yet, but import it.  All new entries are marked this way) 
            #   'import' (its been looked at)
            entity['status'] = 'draft'  
            entity['is_a'] = OrderedDict()
            entity['xrefs'] = OrderedDict()
            entity['synonyms'] = OrderedDict()

            # The source database's term ID is the one datum that can't be differentially compared to an existing entity value.
            database_id = self.load_attribute(entity, child, 'FTC') # FTC = Food Thesaurus Code ?!

            # Bring in existing entity if any
            if database_id in self.database['index']:
                entity = self.database['index'][database_id]
                # Switch terms that were previously 'draft' to 'import'; If they've been marked ignore already then this won't do anything.
                #if entity['status'] == 'new':
                #   entity['status'] = 'import'

            else:
                entity['database_id'] = database_id 
                self.database['index'][database_id] = entity
                self.load_attribute(entity, child, 'ACTIVE','active')
                entity['active']['import'] = False #Not an attribute that is directly imported
            

            # TERM IN DATABASE MAY BE MULTI-HOMED.  
            # If a parent shouldn't be imported, mark it as 'import' = false in database.
            parent_id = child.find('BT').text
            if parent_id is not None:
                if parent_id in self.database['index']: # Get onto_id of parent if possible.
                    parent_onto_id = self.database['index'][parent_id]['ontology_id']
                else:
                    parent_onto_id = self.get_ontology_id(parent_id)

                self.set_attribute_diff(entity['is_a'], parent_onto_id, parent_id) # not providing a value for this.

                # In LanguaL XML, to describe multi-homed item rather than have <BT> be a more complex broader term list, repeated identical xml records are provided, each having its own <BT>.  In order for simple, clean "changed" status of an entities parts to be maintained, can't have entity go through system twice; but we do need to add to its parents list.            
                (itemId, ItemDelta) = entity['is_a'].iteritems().next() #picks first is_a item.
                #print parent_id, itemId

                if parent_id != ItemDelta['value']: 
                    #Means we've already processed the first item on the list.  
                    #ISSUE: Might not work for successive versions of Langual if XML is reordering presentation of <BT> data.
                    continue


            self.set_attribute_diff(entity['xrefs'], 'LANGUAL', database_id)

            if not entity['status'] in ['ignore', 'deprecated']:
                # LanguaL terms that are ACTIVE=false are by default imported as 'deprecated' 
                # ontology terms so we can still capture their ids for database cross-referencing.  
                # Downgrades LanguaL terms that go form active to inactive. But not reverse.
                if self.load_attribute(entity, child, 'ACTIVE','active') == 'False':
                    entity['status'] = 'deprecated'

                scope_note = child.find('SN').text
                if scope_note and 'DO NOT USE for new indexing' in scope_note:
                    entity['status'] = 'deprecated'

                # Current strategy for handling the NOT KNOWN, NOT APPLICABLE and OTHER codes is to mark them depreciated
                # We can add logical equivalency to more generic NOT KNOWN and OTHER selections later...
                oldLabel = child.find('TERM').text
                if oldLabel[-10:] == ' NOT KNOWN' or oldLabel[-8:] == ' UNKNOWN' or oldLabel[-6:] == ' OTHER' or oldLabel[-15:] == ' NOT APPLICABLE':
                    entity['status'] = 'deprecated'

            # Pre-existing entity status controls whether item revisions are considered.  We skip doing updates on "ignore" items, but depreciated items are still included.
            if entity['status'] == 'ignore': 
                continue

            # Enable any database item to be looked up by its FOODON assigned ontology id (which could be a CHEBI_xxxxx or other id too.)
            # A cleared out ontology id gets reassigned 
            # TEMPORARY CLEANUP :  and ('_' in entity['ontology_id'] and entity['ontology_id'][0:entity['ontology_id'].index('_')] in ['CHEBI_','FOODON_','UBERON_','NCBITaxon','GAZ','ancestro'])
            if 'ontology_id' in entity: 
                ontology_id = entity['ontology_id']
            else:
                ontology_id = self.get_ontology_id(database_id)
                entity['ontology_id'] = ontology_id
            
            self.ontology_index[ontology_id] = entity['database_id']

            # NOTE: LanguaL main file definitions are in english. multi-lingual import add-on is possibility later.
            label = self.load_attribute(entity, child, 'TERM', 'label', 'en')
            comment = child.find('SN').text
            if comment and len(comment) > 0: # not sure why this isn't getting filtered out below.
                self.load_attribute(entity, child, 'SN', 'comment', 'en')

            # LanguaL has some tagged text imbedded within other XML text.
            AI = child.find('AI').text
            if AI is not None:
                self.processEntityAI(child, entity, AI)

            # Don't do any more work for depreciated items
            if entity['status'] == 'deprecated': 
                continue

            self.load_facet_details(entity, child)

            # Do synonyms after load_facet_details so for food ingredients synonyms can be 
            # dropped if they are latin names already covered by hasNarrowSynonym
            self.load_synonyms(entity, child)

                
        # Do bulk fetch of ITIS and INDEX FUNGORUM to NCBITaxon codes
        if self.ontology_name == 'langual_import':
            self.getEOLNCBITaxonData()
            self.writeNCBITaxon_OntoFox_spec()
            self.writeOntoFox_specs()

        print "Updating ", self.database_path
        with (open(self.database_path, 'w')) as output_handle:
            output_handle.write(json.dumps(self.database, sort_keys=False, indent=4, separators=(',', ': ')))

        # Display stats and problem cases the import found
        self.report(XMLfile)

        print "Generating ../" + self.ontology_name + '.owl'
        self.save_ontology_owl()


    def updateDatabaseOntologyIds(self, filename):
        # Replace selected LanguaL ontology ids with their CHEBI/UBERON etc equivalents.
        # If LanguaL id for a given database entity exists in lookup table, replaces it with ontology_id
        # The ontology ids get copied out to an OntoFox import specification file for the given ontology.
        lookup = {}
        with (codecs.open(filename, 'r', 'utf-8')) as input_handle:
            for line in input_handle:
                if len(line) > 5 and line[0] != '#':
                    (id, uri, label) = line.split('\t',2)
                    uri = uri.strip()
                    if len(id) > 0 and len(uri) > 0: lookup[id] = uri 

        for database_id in self.database['index']:
            entity = self.database['index'][database_id]
            
            if entity['database_id'] in lookup:
                new_ontology_id = lookup[entity['database_id']]
                self.ontology_index[new_ontology_id] = entity['database_id']
                old_ontology_id = entity['ontology_id']
                entity['ontology_id'] = new_ontology_id
                print ("replacing ref " + entity['database_id'] + ' with ' + new_ontology_id )
                
                # Remove old id in ontology_index as signal not to honour any is_a references to it
                self.ontology_index.pop(old_ontology_id, None)
                    

    def processEntityAI(self, child, entity, AI):
        # LanguaL encoded html -> markdown italics
        AI = AI.replace('$i$','*').replace('$/i$','*').replace('$br/$','\n').replace('$br /$','\n')

        # FIRST CONVERT Wikipedia references, e.g. [http://en.wikipedia.org/wiki/Roselle_(plant)] references to IAO_0000119 'definition_source'
        wikipedia_ref = re.search(self.re_wikipedia_url, AI)
        if wikipedia_ref:
            self.set_attribute_diff(entity, 'definition_source', 'WIKIPEDIA:' + wikipedia_ref.group('reference'))
            #entity['definition_source'] = 'WIKIPEDIA:' + wikipedia_ref.group('reference')
            AI = re.sub(self.re_wikipedia_url, '', AI)
            AI = AI.replace('[]','').replace('()', '')

        # SOME DUPLICATE ENTRIES EXIST
        duplicate = re.search(self.re_duplicate_entry, AI)
        # E.g "<AI>Duplicate entry of *CHILEAN CROAKER [B1814]*.""
        if duplicate:
            entity['replaced_by'] = duplicate.group('id')
            AI = re.sub(self.re_duplicate_entry, '', AI)

        # "\nEurope: E 230.\nCodex: INS 230." ... are extra references already covered by <SYNONYM> so drop them here
        AI = re.sub(self.re_europe, '', AI)
        AI = re.sub(self.re_codex, '', AI)

        # Get term definition text
        if len(AI) > 0:
            if AI[0] == '<':
                definition = self.load_attribute(entity, AI, '<DICTION>')

                # above definition_source appears never to conflict.
                source = self.load_attribute(entity, AI, '<SOURCE>') 
                if source is not None and source != '':
                    self.set_attribute_diff(entity, 'definition_source', source, 'en')

                self.load_attribute(entity['xrefs'], AI, '<ITIS>', 'ITIS')
                self.load_attribute(entity['xrefs'], AI, '<GRIN>', 'GRIN')
                self.load_attribute(entity['xrefs'], AI, '<MANSFELD>', 'MANSFELD')

            # If no codes, e.g. for "broiler chicken", <AI> will contain only text definition rather than <DICTION>
            else: 
                definition = self.load_attribute(entity, child, 'AI')

            if definition is not None: # can be "None"
                # Now clear out the taxonomic entries found within the definition text, and store it
                self.set_attribute_diff(entity, 'definition', self.re_taxonomy.sub('', definition), 'en')



    # Customized for each ontology import source database.
    def get_ontology_id(self, database_id):
        # First character of LanguaL ontology id is a letter; we convert that to an integer 0-12
        # Yields FOODON_3[40-52][0000-9999]
        # I bet D,I,O missing because they can be confused with digits in printout
        if database_id == '00000':
            return 'FOODON_03400000'
        else:
            offset = 'ABCEFGHJKMNPRZ'.index(database_id[0]) 
            return 'FOODON_03' + str(40+offset) + database_id[1:5]


    def load_attribute(self, entity, content, xmltag, attribute=None, language=None):
        """ 
            Fetch xmltag contents from given content.

            entity = self.database[object]
            content = usually input file xml <DESCRIPTOR> node OR it can be a text string.
            xmltag = xml tag name without brackets
            attribute = name of attribute to save in entity, if any
            language = language of saved attribute

        """
        value = None

        # Have a LanguaL term here.  Features common to all terms:
        if isinstance(content, basestring): # Usually content is an xml parse object but added ability to spot text...
            ptr = content.find(xmltag)
            if ptr > -1:
                value = content[ptr+len(xmltag):].strip()
                # Would fetch everything from tag to beginning of next tag but issue is 
                # some <DICTION> tags have other tags injected in them but no closing tag.
                #Sometimes multiple <DICTION>
                value = value.replace('<DICTION>',r'\n\n')

                # HACK! These are all meant to be one-liners, must strip \n of subsequent text
                if xmltag in ['<MANSFELD>','<GRIN>','<ITIS>']:
                    value = value.split('\n',1)[0]

            else:
                attribute = False

        elif content is not None:
            for value in content.iter(xmltag):    # was FIND 
                if value.text:
                    value = value.text.strip()
                else:
                    value = None  # empty tag
                #break # just get first one?

        if attribute:
            self.set_attribute_diff(entity, attribute, value, language)

        # CURRENTLY NOTHING DONE TO MARK OLD ATTRIBUTES that no longer exist in import file!

        return value


    def set_attribute_diff(self, entity, attribute, value, language = None):
        # All new values assumed to be ok.
        # if value == '': return # We don't set empty tags. PROBLEM: Multiple parents set '' value

        try:
            if not attribute in entity:
                entity[attribute] = OrderedDict()
                entity[attribute] = {
                    'value': value, # Value ready for import
                    'import': True, # False = do not import this attribute
                    'locked': False, # Prevent database import from modifying its value
                    'changed': True # Indicates if changed between between database.json and fresh version value.
                }
                if language is not None:
                    entity[attribute]['language'] = language

            # 'ignore' signals not to accept any values here.
            elif entity[attribute]['value'] != value:  # ADD TEST FOR LANGUAGE CHANGE?
                entity[attribute]['changed'] = True
                if entity[attribute]['locked'] == False:
                    entity[attribute]['value'] = value
                    if language is not None:
                        entity[attribute]['language'] = language
                # could push old values + versions onto a history stack
            else:
                entity[attribute]['changed'] = False

        except Exception as e:
            print "ERROR IN SETTING ATTRIBUTE: ", entity, '\nATTRIBUTE:', attribute, '\nVALUE:', value + '\n', language, str(e)


    def load_synonyms(self, entity, content):
        """
        Convert LanguaL <SYNONYM> entries to ontology hasExactSynonym
        A synonym's language isn't always english.  Database import assumes english, but this can be overriden if entry is locked. This way one can mark some entries as japonese, others as spanish etc.
        """
        for synxml in content.iter('SYNONYM'): 
            # Intercepting International Numbering System for Food Additives (INS) references
            # These are documented in the Codex Alimentarius, http://www.fao.org/fao-who-codexalimentarius/codex-home/en/
            if synxml.text[0:4] == 'INS ': 
                entity['xrefs'].pop('Codex:'+synxml.text,None)
                self.set_attribute_diff(entity['xrefs'], 'Codex:', synxml.text[4:])
                continue

            # https://en.wikipedia.org/wiki/E_number
            # European Food Safety Authority issues these as a subset of Codex codes
            # http://www.food.gov.uk/science/additives/enumberlist#h_7
            if synxml.text[0:2] == 'E ':
                entity['xrefs'].pop('Europe:'+synxml.text,None)
                self.set_attribute_diff(entity['xrefs'], 'Europe:', synxml.text[2:])
                continue

            else:
                # Value could be shoehorned to mark up synonym language/source etc?  
                # Empty '' value is where Broad/Narrow/Exact could go if we could make that decision.
                self.set_attribute_diff(entity['synonyms'], synxml.text, '', 'en') 


    def save_ontology_owl(self):
        """
        Generate langual_import.owl ontology file.

        """
        # DON'T CALL THIS header_langual.owl - the Makefile make reads in subdirectories and will try to parse this, and fail.
        with (open('./template_import_header.txt', 'r')) as input_handle:
            owl_output = input_handle.read()

        # MUST SUBSTITUTE ONTOLOGY NAME
        owl_output = owl_output.replace('ONTOLOGY_NAME',self.ontology_name)

        genid = 1 # counter for anonymous node ids.

        for entityid in self.database['index']:
            entity = self.database['index'][entityid]
            
            if entity['database_id'] > self.owl_test_max_entry: # Quickie output possible to see example output only.
                continue

            if entity['status'] != 'ignore': # pick only items that are not marked "ignore"

                # BEGIN <owl:Class> 


                # Ancestro at moment isn't an OBOFoundry ontology,
                ontology_id = entity['ontology_id']
                foodon = True if ontology_id[0:7] == 'FOODON_' else False

                if ontology_id[0:8] == 'ancestro':
                    ontology_id = 'http://www.ebi.ac.uk/ancestro/' + ontology_id
                else:
                    ontology_id = '&obo;' + ontology_id
                owl_output += '\n\n<owl:Class rdf:about="%s">\n' % ontology_id

                label = entity['label']['value'].replace('>','&gt;').replace('<','&lt;').lower()
                labelLang = self.get_language_tag_owl(entity['label']) 

                # Use alternate label if we're normalizing to another ontology
                labelTag = 'rdfs:label' if foodon else 'obo:IAO_0000118'

                owl_output += '\t<%(tag)s %(language)s>%(label)s</%(tag)s>\n' % { 'label': label, 'language': labelLang, 'tag': labelTag}

                for item in entity['is_a']:
                    # If parent isn't imported (even as an obsolete item), don't make an is_a for it.
                    # (is_a entries can reference non-FoodOn ids).
                    if self.term_import(entity['is_a'], item): 
                        # last check to see if item is still in database:
                        if item in self.ontology_index:
                            if item[0:7] == 'http://':
                                prefix = ''  
                            elif item[0:8] == 'ancestro':
                                prefix = 'http://www.ebi.ac.uk/ancestro/' 
                            else: 
                                prefix = '&obo;'
                            owl_output += '\t<rdfs:subClassOf rdf:resource="%s%s"/>\n' % (prefix, item)


                # LANGUAL IMPORT ANNOTATION
                owl_output += "\t<obo:IAO_0000412>http://langual.org</obo:IAO_0000412>\n"

                if self.term_import(entity, 'definition'):
                    # angled unicode single quotes  <U+0091>, <U+0092> 
                    definition = entity['definition']['value'].replace('&',r'&amp;').replace('>','&gt;').replace('<','&lt;').replace(u'\u0092','"').replace(u'\u0091','"') 
                else:
                    definition = ''

                # If this item is primarily a foodon one, provide full annotation
                if foodon:
                    if definition > '':
                        owl_output += '\t<obo:IAO_0000115 xml:lang="en">%s</obo:IAO_0000115>\n' % definition
                  
                    if self.term_import(entity, 'definition_source'):
                        owl_output += '\t<obo:IAO_0000119>%s</obo:IAO_0000119>\n' % entity['definition_source']['value']

                    # CURATION STATUS
                    if entity['status'] == 'deprecated':
                        owl_output += '\t<owl:deprecated rdf:datatype="&xsd;boolean">true</owl:deprecated>\n'
                        # ready for release
                        owl_output += '\t<obo:IAO_0000114 rdf:resource="&obo;IAO_0000122"/>\n' 

                    # Anything marked as 'draft' status is written as 'requires discussion'
                    elif entity['status'] == 'draft': 
                        owl_output += '\t<obo:IAO_0000114 rdf:resource="&obo;IAO_0000428"/>\n'

                # Langual is adding information to a 3rd party CHEBI/UBERON/ etc. term
                elif definition > '':
                    owl_output += '\t<rdfs:comment xml:lang="en">LanguaL term definition: %s</rdfs:comment>\n' % definition


                if self.term_import(entity, 'comment'):
                    owl_output += '\t<rdfs:comment xml:lang="en">LanguaL curation note: %s</rdfs:comment>\n' % entity['comment']['value']

                if 'replaced_by' in entity: #AnnotationAssertion(<obo:IAO_0100001> <obo:CL_0007015> <obo:CLO_0000018>)
                    replacement = '&obo;' + self.database['index'][entity['replaced_by']]['ontology_id']
                    owl_output += '\t<obo:IAO_0100001 rdf:resource="%s"/>\n' % replacement

                if 'synonyms' in entity:
                    for item in entity['synonyms']:
                        if self.term_import(entity['synonyms'], item):
                            
                            owl_output += '\t<oboInOwl:has%(scope)sSynonym %(language)s>%(phrase)s</oboInOwl:has%(scope)sSynonym>\n' % {
                                'scope': entity['synonyms'][item]['value'].title(), # Exact / Narrow / Broad 
                                'language': self.get_language_tag_owl(entity['synonyms'][item]),
                                'phrase': item.lower() 
                            }

                if 'xrefs' in entity:
                    for item in entity['xrefs']:
                        if self.term_import(entity['xrefs'], item):
                            if item == 'EOL':
                                owl_output += '\t<oboInOwl:hasDbXref>http://eol.org/pages/%s</oboInOwl:hasDbXref>\n' % entity['xrefs'][item]['value']
                            else:
                                owl_output += '\t<oboInOwl:hasDbXref>%s:%s</oboInOwl:hasDbXref>\n' % (item, entity['xrefs'][item]['value'] )


                owl_class_footer = '' # This will hold axioms that have to follow outside <owl:Class>...</owl:Class>

                if 'taxon' in entity:
                    for taxon_rank_name in entity['taxon']:
                        #try
                        (rank, latin_name) = taxon_rank_name.split(':',1)
                        #except Exception as e:
                        #    print taxon_rank_name
                        latin_name = latin_name.replace('&','&amp;')

                        if rank == 'species':
                            synonymTag = 'hasNarrowSynonym' 
                            rankTag = ''
                        else:
                            synonymTag = 'hasBroadSynonym'
                            rankTag = '<taxon:_taxonomic_rank rdf:resource="&obo;NCBITaxon_%s" />\n' % rank

                        # If an NCBITaxon reference exists, let it replace all the others
                        if 'NCBITaxon' in entity['taxon'][taxon_rank_name] and entity['taxon'][taxon_rank_name]['NCBITaxon']['import'] == True:
                            dbid = entity['taxon'][taxon_rank_name]['NCBITaxon']['value']
                            
                            if synonymTag == 'hasNarrowSynonym':
                                owl_output += self.item_food_role(dbid)

                            else:
                                # FUTURE: CHANGE THIS TO SOME OTHER RELATION?
                                # Exact or (usually) BroadSynonym:
                                owl_output += '\t<oboInOwl:%(synonymTag)s rdf:resource="&obo;NCBITaxon_%(dbid)s" />\n' % {'synonymTag': synonymTag, 'dbid': dbid}

                                # Adds NCBITaxon rank annotation to above:
                                if len(rankTag):
                                    owl_class_footer += self.item_taxonomy_annotation(ontology_id, synonymTag, dbid, rankTag)

                        else:

                            owl_output += '\t<oboInOwl:%(synonymTag)s>%(latin_name)s</oboInOwl:%(synonymTag)s>\n' % {'synonymTag': synonymTag, 'latin_name': latin_name}

                            axiom_content = rankTag

                            for database in entity['taxon'][taxon_rank_name]:
                                if database != 'NCBITaxon':
                                    axiom_content += '     <oboInOwl:hasDbXref>%(database)s:%(dbid)s</oboInOwl:hasDbXref>\n' % {'database':database, 'dbid': entity['taxon'][taxon_rank_name][database]['value']}

                            owl_class_footer += self.item_synonym_text_annotation(ontology_id, synonymTag, latin_name, axiom_content)
                            

                owl_output += '</owl:Class>' + owl_class_footer

        owl_output += '</rdf:RDF>'

        print "Saving ../" + self.ontology_name + '.owl'

        with (codecs.open('../' + self.ontology_name + '.owl', 'w', 'utf-8')) as output_handle:
            output_handle.write(owl_output)


    def item_food_role(self, NCBITaxon_id):
        """
        Food source items matched to an ITIS taxon id all have an equivalency: 
            [NCBITaxon item] and 'has role' some food (CHEBI_33290)
        """
        return '''
            <owl:equivalentClass>
                <owl:Class>
                    <owl:intersectionOf>
                        <rdf:List>
                            <rdf:first rdf:resource="&obo;NCBITaxon_%s"/>
                            <rdf:rest>
                                <rdf:List>
                                    <rdf:first>
                                        <owl:Restriction>
                                            <owl:onProperty rdf:resource="&obo;RO_0000087"/>
                                            <owl:someValuesFrom rdf:resource="&obo;CHEBI_33290"/>
                                        </owl:Restriction>
                                    </rdf:first>
                                </rdf:List>
                            </rdf:rest>             
                        </rdf:List>
                    </owl:intersectionOf>
                </owl:Class>
            </owl:equivalentClass> 
        ''' % NCBITaxon_id


    def item_taxonomy_annotation(self, ontology_id, synonymTag, dbid, content):
        return """
        <owl:Axiom>
            <owl:annotatedSource rdf:resource="%(ontology_id)s"/>
            <owl:annotatedProperty rdf:resource="&oboInOwl;%(synonymTag)s"/>
            <owl:annotatedTarget rdf:resource="&obo;NCBITaxon_%(dbid)s" />
            %(content)s
        </owl:Axiom>
        """ % {'ontology_id': ontology_id, 'synonymTag':synonymTag, 'dbid': dbid, 'content':content }

    def item_synonym_text_annotation(self, ontology_id, synonymTag, text, content):
        return """
        <owl:Axiom>
            <owl:annotatedSource rdf:resource="%(ontology_id)s"/>
            <owl:annotatedProperty rdf:resource="&oboInOwl;%(synonymTag)s"/>
            <owl:annotatedTarget>%(text)s</owl:annotatedTarget>
            %(content)s
        </owl:Axiom>
        """ % {'ontology_id': ontology_id, 'synonymTag': synonymTag, 'text': text, 'content':content}


    def term_import(self, entity, term):
        """
        returns boolean test of whether a particular entity attribute exists and should be imported into ontology file.
        """
        return ( (term in entity) and (entity[term]['value'] != None) and entity[term]['import'] == True)


    def get_language_tag(self, entity):
        if 'language' in entity:
            return '@' + entity['language']
        else:
            return ''


    def get_language_tag_owl(self, entity):
        if 'language' in entity:
            return 'xml:lang="' + entity['language'] + '"'
        else:
            return ''

    #************************************************************


    def load_facet_details(self, entity, content):
        """
        Enhance entity with LanguaL facet-specific attributes.  Facet letters D,I,L,O don't exist in LanguaL.
        """ 

        # Stats on count of members of each LanguaL facet, which is first letter of entity id.
        category = entity['database_id'][0]
        if category in self.counts: 
            self.counts[category] += 1 
        else: 
            self.counts[category] = 1


        # A. PRODUCT TYPE [A0361]
        #if category == 'A': 
        #   pass

        # B. FOOD SOURCE [B1564]
        if category == 'B':
            """
            Food Source facet import notes:

                - Includes raw animal, plant, bacteria and fungi ingredients.
                - Most items having taxonomic scientific names.  A lookup of eol.org 
                    taxonomic database reference to NCBI taxonomy name is performed 
                    (alternatly make entries to cover ITIS items?)  
                - Result is an NCBI taxon tree as well as a tree of food source items. 
            """
            self.getFoodSource(entity, content)


        # C. PART OF PLANT OR ANIMAL [C0116]
        #elif category == 'C': 
        #   pass

        # E. PHYSICAL STATE, SHAPE OR FORM [E0113]
        #elif category == 'E': 
        #   pass

        # F. EXTENT OF HEAT TREATMENT [F0011]
        elif category == 'F': 
            pass

        # G. COOKING METHOD [G0002]
        elif category == 'G': 
            pass

        #H. TREATMENT APPLIED [H0111]
        #elif category == 'H': 
        #   pass

        #J. PRESERVATION METHOD [J0107]
        elif category == 'J': 
            pass

        #K. PACKING MEDIUM [K0020]
        elif category == 'K': 
            pass

        #M. CONTAINER OR WRAPPING [M0100]
        elif category == 'M': 
            pass

        #N. FOOD CONTACT SURFACE [N0010]
        #elif category == 'N': 
        #   pass

        #P. CONSUMER GROUP/DIETARY USE/LABEL CLAIM [P0032]
        #elif category == 'P': 
        #   pass

        #R. GEOGRAPHIC PLACES AND REGIONS [R0010]
        #elif category == 'R': 
        #   pass

        #Z. ADJUNCT CHARACTERISTICS OF FOOD [Z0005]
        #elif category == 'Z': 
        #   pass


    def getFoodSource(self, entity, content):
        """
        FIRST: Lookup via ITIS identifier.
        IF NOT AVAILABLE, TRY to get taxonomy via latin synonyms?
        
        "taxon": {
            "family:Terapontidae": {
                "ITIS": {
                    "import": true,
                    "changed": true,
                    "locked": false,
                    "value": "650201"
                }
            },
        """

        taxonomyblob = content.find('AI').text
        if taxonomyblob:

            for line in taxonomyblob.split('\n'):

                # '&#60;(?P<rank>[A-Z]+)&#62;(?P<name>[^[]+) ?\[(?P<db>[A-Z]+) ?(?P<id>[^\]]+)')
                taxonomyobj = re.search(self.re_taxonomy, line)
                if taxonomyobj:

                    if taxonomyobj.group('rank') == 'DICTION':
                        if taxonomyobj.group('name')[0:14].lower() == 'food additive':
                            self.food_additive += 1
                    else:
                        try:
                            taxon_rank = self.ranklookup[taxonomyobj.group('rank')] # family, species, etc...
                            taxon_name = taxon_rank + ':' + taxonomyobj.group('name').strip()
                            if taxonomyobj.group('db'):  # Usually [[db] [id]]
                                taxon_db = taxonomyobj.group('db')
                            else: #sometimes just [[db]]
                                taxon_db = taxonomyobj.group('ref')

                            if taxonomyobj.group('id'):
                                taxon_id = taxonomyobj.group('id')
                            else:
                                taxon_id = ''

                            if 'taxon' not in entity: entity['taxon'] = OrderedDict()
                            if taxon_name not in entity['taxon']: entity['taxon'][taxon_name] = OrderedDict()
                            
                            """ PROBLEM:
                            "FAO ASFIS XXX" triggers changed flag.  2 values below for database cross reference!
                            <DESCRIPTOR>
                            <FTC>B2112</FTC>
                            <TERM lang="en UK">MOLLUSCS</TERM>
                            <BT>B1433</BT>
                            <SN></SN>
                            <AI>&#60;SCIPHY&#62;Mollusca [ITIS 69458]
                            &#60;SCIPHY&#62;Mollusca [FAO ASFIS MOF]
                            &#60;SCIPHY&#62;Mollusca [FAO ASFIS MOL]</AI>
                            """
                            self.set_attribute_diff(entity['taxon'][taxon_name], taxon_db, taxon_id)

                            if entity['database_id'] > self.owl_test_max_entry: # Quickie output possible to see example output only.
                                continue

                            if taxon_db == 'ITIS' or taxon_db == 'INDEX FUNGORUM':
                                # See if we should do a lookup
                                if 'NCBITaxon' in entity['taxon'][taxon_name]: # Already done!
                                    pass

                                else:
                                    #Add to taxonomy bulk job.
                                    self.NCBITaxon_lookup[taxon_db].append((entity, taxon_name, taxon_id))
                                    

                        except Exception as e:

                            print "TAXON CREATION PROBLEM:", line, taxonomyobj, str(e)
                        
        else:
            self.no_taxonomy += 1


    def getEOLNCBITaxonData(self):
        """
        Perform Lookup of NCBI_Taxon data directly from EOL.org via API and ITIS code.

        ITIS (provider id 903) SEARCH TO EOL ID/Batch of IDs:

            http://eol.org/api/search_by_provider/1.0.json?batch=true&id=180722%2C160783&hierarchy_id=903
            http://eol.org/api/search_by_provider/1.0.json?batch=false&id=172431&hierarchy_id=903&cache_ttl=
        Returns:
            [{"180722":[
                {"eol_page_id":328663},
                {"eol_page_link":"eol.org/pages/328663"}
            ]},
            {"160783":[
                {"eol_page_id":8897},
                {"eol_page_link":"eol.org/pages/8897"}]
            }]


        EOL Page to possible NCBITaxon and other taxonomy data:

            http://eol.org/api/pages/1.0.json?batch=true&id=328663&subjects=overview&common_names=true&synonyms=true&taxonomy=true&cache_ttl=&language=en

            [{"328663": {
                "identifier": 328663,
                "scientificName": "Sus scrofa Linnaeus, 1758",
                "richness_score": 400.0,
                "taxonConcepts": [... {
                    "identifier": 51377703,
                    "scientificName": "Sus scrofa",
                    "nameAccordingTo": "NCBI Taxonomy",
                    "canonicalForm": "Sus scrofa",
                    "sourceIdentifier": "9823",
                    "taxonRank": "Species"
                }, {
            
        NOTE ALSO

            FAO ASFIS : http://www.fao.org/fishery/collection/asfis/en

            http://www.itis.gov/web_service.html
            http://www.itis.gov/ITISWebService/jsonservice/getFullRecordFromTSN?tsn=500059
            http://www.itis.gov/ITISWebService/jsonservice/getHierarchyUpFromTSN?tsn=1378

        """

        for eol_provider in self.NCBITaxon_lookup:
            eol_provider_id = self.EOL_providers[eol_provider]
            eol_provider_map = {}
            batch_provider_ids = []
            batch_eol_ids = []
            provider_ncbitaxon_map = {}

        # Do ITIS code to EOL Page mapping.  Requests have to bet batched into groups of 100 ids or HTTP 413 request too long error results.
        for (entity, taxon_name, provider_id) in self.NCBITaxon_lookup[eol_provider]:
            batch_provider_ids.append(provider_id)

        batch_provider_ids = sorted(set(batch_provider_ids))

        while len(batch_provider_ids):
            provider_ids = batch_provider_ids[0:100]
            batch_provider_ids = batch_provider_ids[100:]
            url = "http://eol.org/api/search_by_provider/1.0.json?batch=true&id=%s&hierarchy_id=%s" % (','.join(provider_ids), eol_provider_id)
            eol_data = self.get_jsonparsed_data(url)

            for eol_obj in eol_data:
                for provider_id in eol_obj:
                    eol_fields = eol_obj[provider_id]
                    # e.g. [{u'eol_page_id': 2374}, {u'eol_page_link': u'eol.org/pages/2374'}]
                    eol_page_id = str(eol_fields[0]['eol_page_id'])
                    eol_provider_map[eol_page_id] = provider_id
                    batch_eol_ids.append(eol_page_id)


        # Do EOL to NCBI mapping
        while len(batch_eol_ids):
            eol_ids = batch_eol_ids[0:100]
            batch_eol_ids = batch_eol_ids[100:]
            url = "http://eol.org/api/pages/1.0.json?batch=true&id=%s&subjects=overview&taxonomy=true&cache_ttl=&language=en" % ','.join(eol_ids)
            eol_data = self.get_jsonparsed_data(url) 

            for page_obj in eol_data:
                for eol_page_id in page_obj:
                    provider_id = eol_provider_map[eol_page_id]
                    for taxon_item in page_obj[eol_page_id]['taxonConcepts']:
                        if taxon_item['nameAccordingTo'] == 'NCBI Taxonomy':
                            # track taxon rank as well as identifier so we can spot mismatches
                            # ISSUE: VERIFY: are EOL ranks different from NCBITaxon's ?
                            if 'taxonRank' in taxon_item:
                                rank = taxon_item['taxonRank'].lower()
                            else:
                                rank = ''
                            provider_ncbitaxon_map[provider_id] = (eol_page_id, taxon_item['sourceIdentifier'], rank )

        # ADD EOL page hasDbXref cross reference for valid provider lookup.

        # For our queue, add NCBI entries
        for eol_provider in self.NCBITaxon_lookup:
            for (entity, taxon_name, provider_id) in self.NCBITaxon_lookup[eol_provider]: # provider_id is 'ITIS' etc.
                if provider_id in provider_ncbitaxon_map:
                    (eol_page_id, taxon_id, taxon_rank) = provider_ncbitaxon_map[provider_id]
                    # If NCBI record's rank is different from leading part of taxon name, e.g. "species:pollus pollus"
                    # Then drop entity['taxon'][NCBITaxon] record (if any)
                    # AND drop entity['taxon'][eol_provider]
                    if taxon_rank == '' or taxon_name.split(':',1)[0] == taxon_rank:
                        print "NCBITaxon lookup: ", taxon_id
                        # IF NOT LOCKED???
                        self.set_attribute_diff(entity['taxon'][taxon_name], 'NCBITaxon', taxon_id )
                        # PROBLEM: EOL link will get set by upper and lower bound taxonomy set.
                        self.set_attribute_diff(entity['xrefs'], 'EOL', eol_page_id )
                    else:
                        entity['taxon'][taxon_name]['NCBITaxon']['import'] = False
                        entity['taxon'][taxon_name][eol_provider]['import'] = False

                else:
                    # Signal not to try lookup again
                    entity['taxon'][taxon_name]['NCBITaxon'] = {
                        "import": False,
                        "changed": False,
                        "locked": False,
                        "value": None
                    }


    def writeNCBITaxon_OntoFox_spec(self):

        spec = ''
        for database_id in self.database['index']:
            entity = self.database['index'][database_id]
            if 'taxon' in entity:
                for taxon in entity['taxon']:
                    if 'NCBITaxon' in entity['taxon'][taxon]:
                        taxobj = entity['taxon'][taxon]['NCBITaxon']
                        spec += 'http://purl.obolibrary.org/obo/NCBITaxon_%s # %s\n' % (taxobj['value'], taxon)
        
        with open('./template_ncbitaxon_ontofox.txt', 'r') as handle:
            ontofoxSpec = handle.read()

            index = ontofoxSpec.find('[Top level source term URIs')
            spec = ontofoxSpec[:index] + spec + '\n\n' + ontofoxSpec[index:]
      
            with (codecs.open('../ncbitaxon_ontofox.txt', 'r', 'utf-8')) as read_handle:
                if read_handle.read() != spec:
                    with (codecs.open('../ncbitaxon_ontofox.txt', 'w', 'utf-8')) as output_handle:
                        output_handle.write(spec)


    def writeOntoFox_specs(self):
        """
        Create the OntoFox import specification files, one for each ontology listed below.
        A "template_[ontology]_ontofox.txt" template file is read, and all the ontology codes
        are inserted just before the "[Top level source term URIs ..." section.
        
        ontofoxSpec is a key-value bag containing one OntoFox command string for each ontology.
        """
        # List of ontology prefixes to generate ontofox specification files for:
        ontofoxSpec = {
            'chebi':'',
            'uberon':'',
            'gaz':''}
        ontofoxSpecKeys = ontofoxSpec.keys()

        # For each entity in database, check its ontology_id to see if it references an entity 
        # that needs to be imported.
        for database_id in self.database['index']:
            entity = self.database['index'][database_id]
            if 'ontology_id' in entity:
                ontology_id = entity['ontology_id'].lower()
                for ontology in ontofoxSpecKeys:
                    if ontology_id[0:len(ontology)] == ontology:
                        # Assumes only one label for comment
                        ontofoxSpec[ontology] += 'http://purl.obolibrary.org/obo/%s # %s\n' % (entity['ontology_id'], entity['label']['value'])
        
        for ontology in ontofoxSpecKeys:
            if len(ontofoxSpec[ontology]) > 0:
                output_file = '../' + ontology + '_ontofox.txt'
                with open('template_' + ontology + '_ontofox.txt', 'r') as handle:
                    ontofoxTemplate = handle.read()

                    index = ontofoxTemplate.find('[Top level source term URIs')
                    content = ontofoxTemplate[:index] + ontofoxSpec[ontology] + '\n\n' + ontofoxTemplate[index:]
              
                    with (codecs.open(output_file, 'r', 'utf-8')) as read_handle:
                        if read_handle.read() != content:
                            print ("Generating " + output_file)
                            with (codecs.open(output_file, 'w', 'utf-8')) as output_handle:
                                output_handle.write(content)


    def get_jsonparsed_data(self, url):
        """
        Receive the content of ``url``, parse it as JSON and return the object.

        Parameters
        ----------
        url : str

        Returns
        -------
        dict
        """
        try:
            response = requests.get(url)

        except Exception as e:
            print "ERROR IN SENDING EOL.org request: ", str(e)

        print response.status_code, response.headers['content-type']
        return response.json()


    def report(self, file):
        print
        print "LANGUAL IMPORT of [" + file + ']'
        print "Facet item counts"
        print self.counts               
        print
        print (self.output)


    def get_database_JSON(self, file):
        """
        Load existing JSON representation of import database (created last time OWL ontology was saved)
        Will be updated if database has changed.
        """
        with open(file) as data_file:    
            return json.load(data_file, object_pairs_hook=OrderedDict)


if __name__ == '__main__':

    foodstruct = Langual()
    # Generates main import file:
    foodstruct.__main__('langual2014.xml','./database.json', '../langual_import')
    # Generates LanguaL Facet A Product Type file
    #foodstruct.__main__('langual2014.xml','./langual_facet_a.json', 'product_type_import')
