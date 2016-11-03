#!/usr/bin/python
# -*- coding: utf-8 -*-

""" 
**************************************************
conversion.py
Author: Damion Dooley

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


CODE_VERSION = '0.0.3'

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
        self.ontology_path = './LANGUAL_import'
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


    def __main__(self, file):
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
        if os.path.isfile(self.database_path):
            self.database = self.get_database_JSON(self.database_path)
            self.database['version'] +=1
            # self.version = self.database['version']

        #file_handle = codecs.open(file, "r", "iso-8859-1")
        tree = ET.parse(file) # Incoming raw XML database file
        root = tree.getroot()

        for child in root.iter('DESCRIPTOR'):
            
            # Place facet characters here to skip them
            category = child.find('FTC').text[0]
            if category in 'A':
                continue

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

                # Current strategy for handling the NOT KNOWN and OTHER codes is to mark them depreciated
                # We can add logical equivalency to more generic NOT KNOWN and OTHER selections later...
                oldLabel = child.find('TERM').text
                if oldLabel[-10:] == ' NOT KNOWN' or oldLabel[-6:] == ' OTHER':
                    entity['status'] = 'deprecated'

            # Pre-existing entity status controls whether item revisions are considered.  We skip doing updates on "ignore" items, but depreciated items are still included.
            if entity['status'] == 'ignore': 
                continue

            # Enable any database item to be looked up by its FOODON assigned ontology id (which could be a CHEBI_xxxxx or other id too.)

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

            # Don't do any more work for depreciated items
            if entity['status'] == 'deprecated': 
                continue

            self.load_facet_details(entity, child)

            # Do synonyms after load_facet_details so for food ingredients synonyms can be 
            # dropped if they are latin names already covered by hasNarrowSynonym
            self.load_synonyms(entity, child)

        # 2nd pass: link up as many archaic LanguaL terms as possible to primary entries
        #for database_id in self.database['index']:
        #    entity = self.database['index'][database_id]
        #    if entity['status'] != 'ignore':
        #        # Need to add parent_id label just for OBO output file "is_a ... ! ..." comment
        #        for item in entity['is_a']:
        #            # LOOKUP is ontology_id - need cross reference
        #            if item in self.ontology_index:  # And item not locked or ignore
        #                dbid = self.ontology_index[item]
        #                db_name = self.database['index'][dbid]['label']['value']
        #                entity['is_a'][item]['value'] = db_name
                
        # Do bulk fetch of ITIS and INDEX FUNGORUM to NCBITaxon codes
        self.getEOLNCBITaxonData()

        print "Updating ", self.database_path
        with (open(self.database_path, 'w')) as output_handle:
            output_handle.write(json.dumps(self.database, sort_keys=False, indent=4, separators=(',', ': ')))

        # Display stats and problem cases the import found
        self.report(file)

        self.writeNCBITaxon_OntoFox_spec()

        print "Generating ", self.ontology_path + '.owl'
        self.save_ontology_owl()


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
        Generate LANGUAL_import.owl ontology file.

        """
        with (open('./header.owl', 'r')) as input_handle:
            owl_output = input_handle.read()

        genid = 1 # counter for anonymous node ids.

        for entityid in self.database['index']:
            entity = self.database['index'][entityid]
            
            if entity['database_id'] > self.owl_test_max_entry: # Quickie output possible to see example output only.
                continue

            if entity['status'] != 'ignore': # pick only items that are not marked "ignore"

                # For now accept only first parent as is_a parent
                label = entity['label']['value'].replace('>','&gt;').replace('<','&lt;').lower()
                ontology_id = '&obo;' + entity['ontology_id']

                # BEGIN <owl:Class> 
                owl_class_footer = '' # This will hold axioms that have to follow outside <owl:Class>...</owl:Class>

                owl_output += '\n\n<owl:Class rdf:about="%s">\n' % ontology_id
                owl_output += '\t<rdfs:label %(language)s>%(label)s</rdfs:label>\n' % { 
                    'label': label, 
                    'language': self.get_language_tag_owl(entity['label']) 
                }
                # LANGUAL IMPORT ANNOTATION
                owl_output += "\t<obo:IAO_0000412>http://langual.org</obo:IAO_0000412>\n"

                for item in entity['is_a']:
                    # If parent isn't imported (even as an obsolete item), don't make an is_a for it.
                    # (is_a entries can be ABOUT non LanguaL ids).
                    if self.term_import(entity['is_a'], item): 
                        owl_output += '\t<rdfs:subClassOf rdf:resource="&obo;%s"/>\n' % item

                if self.term_import(entity, 'definition'):
                    definition = entity['definition']['value']  #.replace('"',r'\"').replace('\n',r'\n')
                    owl_output += '\t<obo:IAO_0000115 xml:lang="en">%s</obo:IAO_0000115>\n' % definition.replace('&',r'&amp;').replace('>','&gt;').replace('<','&lt;')
              
                if self.term_import(entity, 'definition_source'):
                    owl_output += '\t<obo:IAO_0000119>%s</obo:IAO_0000119>\n' % entity['definition_source']['value']

                # CURATION STATUS
                if entity['status'] == 'deprecated':
                    owl_output += '\t<owl:deprecated rdf:datatype="&xsd;boolean">true</owl:deprecated>\n'
                    # ready for release
                    owl_output += '\t<obo:IAO_0000114 rdf:resource="&obo;IAO_0000122"/>\n' 
                elif entity['status'] == 'draft': # Anything marked as 'draft' status is written as 'requires discussion'
                    owl_output += '\t<obo:IAO_0000114 rdf:resource="&obo;IAO_0000428"/>\n'

                if self.term_import(entity, 'comment'):
                    owl_output += '\t<rdfs:comment xml:lang="en">LanguaL curator\'s note: %s</rdfs:comment>\n' % entity['comment']['value']

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
                            rankTag = '<taxon:_taxonomic_rank rdf:resource="http://purl.obolibrary.org/obo/NCBITaxon_%s" />' % rank

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

        print "Saving ", self.ontology_path + '.owl'

        with (codecs.open(self.ontology_path + '.owl', 'w', 'utf-8')) as output_handle:
            output_handle.write(owl_output)

    '''
    def item_inheres_in(self, ):

        # Making [food source item] 'inheres in' some [NCBITaxon item]
        # Making [NCBITaxon item] 'is bearer of' some [food source item]


        # Here we say the food entity inheres in a taxonomic entity
        owl_output += '\t<rdfs:subClassOf rdf:nodeID="genid%s"/>\n' % genid
        # ... rdf:nodeID="genid%(genid)s">   rdf:about="%(ontology_id)s">
        
        owl_class_footer += """
            <rdf:Description rdf:nodeID="genid%(genid)s">
                <rdf:type rdf:resource="http://www.w3.org/2002/07/owl#Restriction"/>
                <owl:onProperty rdf:resource="http://purl.obolibrary.org/obo/RO_0000052"/>
                <owl:someValuesFrom rdf:resource="http://purl.obolibrary.org/obo/NCBITaxon_%(dbid)s"/>
            </rdf:Description>

            <rdf:Description rdf:about="http://purl.obolibrary.org/obo/NCBITaxon_%(dbid)s">
                <rdfs:subClassOf rdf:nodeID="genid%(genid2)s"/>
            </rdf:Description>

            <rdf:Description rdf:nodeID="genid%(genid2)s">
                <rdf:type rdf:resource="http://www.w3.org/2002/07/owl#Restriction"/>
                <owl:onProperty rdf:resource="http://purl.obolibrary.org/obo/RO_0000053"/>
                <owl:someValuesFrom rdf:resource="%(ontology_id)s"/>
            </rdf:Description>

            """ % {'genid': genid, 'dbid': dbid, 'genid2': (genid+1), 'ontology_id': ontology_id}
        genid += 2
    '''

    def item_food_role(self, NCBITaxon_id):
        """
        Food source items all have an equivalency: [NCBITaxon item] and 'has role' some food (CHEBI_33290)
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
                                            <owl:onProperty rdf:resource="http://purl.obolibrary.org/obo/RO_0000087"/>
                                            <owl:someValuesFrom rdf:resource="http://purl.obolibrary.org/obo/CHEBI_33290"/>
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
        </owl:Axiom>'
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
            
        spec = """
[URI of the OWL(RDF/XML) output file]
http://purl.obolibrary.org/obo/FOODON/imports/NCBITaxon_import.owl

[Source ontology]
NCBITaxon

[Low level source term URIs]
http://purl.obolibrary.org/obo/NCBITaxon#_taxonomic_rank #taxonomic rank
includeAllChildren

""" + spec + """

[Top level source term URIs and target direct superclass URIs]
http://purl.obolibrary.org/obo/NCBITaxon_2157
subClassOf http://purl.obolibrary.org/obo/OBI_0100026 #OBI:organism
http://purl.obolibrary.org/obo/NCBITaxon_2
subClassOf http://purl.obolibrary.org/obo/OBI_0100026 #OBI:organism
http://purl.obolibrary.org/obo/NCBITaxon_2759
subClassOf http://purl.obolibrary.org/obo/OBI_0100026 #OBI:organism
http://purl.obolibrary.org/obo/NCBITaxon_10239
subClassOf http://purl.obolibrary.org/obo/OBI_0100026 #OBI:organism

[Source term retrieval setting]
includeComputedIntermediates

[Source annotation URIs]
http://www.w3.org/2000/01/rdf-schema#label
#copyTo http://purl.obolibrary.org/obo/IAO_0000111
http://www.geneontology.org/formats/oboInOwl#hasExactSynonym
#mapTo http://purl.obolibrary.org/obo/IAO_0000118 #iao:alternative term
http://purl.obolibrary.org/obo/ncbitaxon#common_name
"""
    
        with (codecs.open('./ontofox_ncbitaxon_spec.txt', 'w', 'utf-8')) as output_handle:
            output_handle.write(spec)


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
            response = requests.get(url) #  + '&key=5662da7aff53b902e6f33c86ae5e00b5f394d1f2'

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
        print "Food source (facet B) stats"
        print " Food additive items: ", self.food_additive
        print " Items with taxonomy: ", self.has_taxonomy
        print "   Items having ITIS: ", self.has_ITIS
        print " Items without taxon: ", self.no_taxonomy

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
    foodstruct.__main__('langual2014.xml')


""" TAXONOMY NOTES

Taxonomy roles in LanguaL VS NCBI (NCBITaxon#_taxonomic_rank , relation: ncbitaxon#has_rank)
LanguaL code                    NCBI_Taxon_
                                superkingdom
               Kingdom          kingdom 
               Subkingdom       subkingdom
               Infrakingdom
               Superdivision    superphylum     * division/phylum merged (Botany division = plant)
SCIDIV         Division         phylum          * division -> phylum in NCBI 
               Subdivision      subphylum
                                
SCIPHY         Phylum           
SCISUBPHY      Subphylum        subphylum
SCISUPCLASS                     superclass 
SCICLASS       Class            class
                                subclass
SCIINFCLASS                     infraclass
               Superorder       superorder
SCIORD         Order            order
SCISUBORD                       suborder
SCIINFORD                       infraorder
                                parvorder
SCISUPFAM                       superfamily
SCIFAM         Family           family
SCISUBFAM                       subfamily
SCITRI                          tribe   
                                subtribe            
SCIGEN         Genus            genus
                                subgenus
SCINAM         Species          species
SCISYN                          species     * synonym!?!
                                subspecies
                                varietas
                                forma
PROBLEM CASES
SCISUNFAM  typo of SCISUBFAM                                
NCBI Also has:

                                species_group
                                species_subgroup

NOTE EOL: http://eol.org/pages/582002/names/synonyms synonyms categorized by preferred, misspelling, authority,  etc. and relate to scientific names.

Example LanguaL record
<DESCRIPTOR>
    <FTC>B1249</FTC>
    <TERM lang="en UK">PAPAYA</TERM>
    <BT>B1024</BT>
    <SN></SN>
    <AI>&#60;SCIFAM&#62;Caricaceae [ITIS 22322]
    &#60;SCINAM&#62;Carica papaya L. [ITIS 22324]
    &#60;SCINAM&#62;Carica papaya L. [GRIN 9147]
    &#60;SCINAM&#62;Carica papaya L. [PLANTS CAPA23]
    &#60;SCINAM&#62;Carica papaya L. [EuroFIR-NETTOX 2007 73]
    &#60;SCINAM&#62;Carica papaya L. [DPNL 2003 8382]
    &#60;MANSFELD&#62;23437</AI>
    <SYNONYMS>
        <SYNONYM>carica papaya</SYNONYM>
        <SYNONYM>hawaiian papaya</SYNONYM>
        <SYNONYM>lechoza</SYNONYM>
        <SYNONYM>melon tree</SYNONYM>
        <SYNONYM>pawpaw</SYNONYM>
    </SYNONYMS>
    <RELATEDTERMS>
    </RELATEDTERMS>
    <CLASSIFICATION>False</CLASSIFICATION>
    <ACTIVE>True</ACTIVE>
    <DATEUPDATED>2011-10-07</DATEUPDATED>
    <DATECREATED>2000-01-01</DATECREATED>
    <UPDATECOMMENT></UPDATECOMMENT>
    <SINGLE>False</SINGLE>

# <SINGLE> appears to be an inconsequential tag.
# ISSUE: Some "lines" in lines_of_text might not be separated by a carriage return, e.g.
    
    <SCINAM>Hapalochlaena maculosa (Hoyle, 1883) [ITIS 556175]<.... > 


PROBLEM CASE - ITIS code is NOT following SCINAME in brackets:
    <SCIFAM>Apiaceae
    <SCINAM>Apium graveolens var. rapaceum (Miller) Gaudin
    <ITIS>530941
    <GRIN>3704
    <MANSFELD>1236

    <DESCRIPTOR>
        <FTC>B1729</FTC>
        <TERM lang="en UK">CELERIAC</TERM>
        <BT>B1018</BT>
        <SN></SN>
        <AI>&#60;SCIFAM&#62;Apiaceae
        &#60;SCINAM&#62;Apium graveolens var. rapaceum (Miller) Gaudin
        &#60;ITIS&#62;530941
        &#60;GRIN&#62;3704
        &#60;MANSFELD&#62;1236</AI>
        <SYNONYMS>
            <SYNONYM>apium graveolens rapaceum</SYNONYM>
            <SYNONYM>celery root</SYNONYM>
        </SYNONYMS>

PROBLEM CASE - solanum dulcamara
<SYNONYMS>
    <SYNONYM>solanum dulcamara</SYNONYM>
</SYNONYMS>
    - no taxonomy but scientific name will return ITIS / EOL / NCBITaxon lookup.

"""