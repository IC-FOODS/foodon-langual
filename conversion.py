#!/usr/bin/python
# -*- coding: utf-8 -*-

""" 
**************************************************
conversion.py
Author: Damion Dooley

This script uses the Langual.org food description thesaurus (published yearly in XML) 
to provide a differential update of a langual.JSON data file.  From this the langual.OWL file
is regenerated, and can then be imported into FOODON food ontology.  
It provides many of the facets - food source, cooking method, preservation method, etc. 

Key to the management of the langual.json file and subsequent OWL file is that one can 
manually add elements to it which are not overwritten by subsequent langual XML file imports.
Every Langual item maps over to any existing FOODON item by way of a hasDbXref: Langual [id]" entry.
The langual.json file has entities organized (the key) by langual_id, but entity itself includes the assigned FOODON id so that when it comes time to adjust an existing langual.OWL file, entries are located/written out by FOODON ID.  

This script assigns FOODON ids in range of 3400000 - 3499999 for any new langual terms that script
allows to be imported into langual.json .  For now, Langual IDs are being coded in as FOODON_3[4+letter as 2 digit offset][9999]

Food Source facet import notes:

	- Includes raw animal, plant, bacteria and fungi ingredients.
	- Most items having taxonomic scientific names.  A lookup of eol.org 
		taxonomic database reference to NCBI taxonomy name is performed 
		(alternatly make entries to cover ITIS items?)  
	- Result is an NCBI taxon tree as well as a tree of food source items. 

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

try: #Python 2.7
	from collections import OrderedDict
except ImportError: # Python 2.6
	from ordereddict import OrderedDict

#FOR LOADING JSON AND PRESERVING ORDERED DICT SORTING. 
try:	
	import simplejson as json
except ImportError: # Python 2.6
    import json

CODE_VERSION = '0.0.2'

def stop_err( msg, exit_code=1 ):
	sys.stderr.write("%s\n" % msg)
	sys.exit(exit_code)

class MyParser(optparse.OptionParser):
	"""
	Allows formatted help info.  From http://stackoverflow.com/questions/1857346/python-optparse-how-to-include-additional-info-in-usage-output.
	"""
	def format_epilog(self, formatter):
		return self.epilog


class Langual(object):

	def __init__(self):

		# READ THIS FROM database.json
		self.database_path = './database.json'
		self.ontology_path = './ontology.obo'
		self.database = { #empty case.
			'index': OrderedDict(), 
			'ontology': OrderedDict(), 
			'version':0 
		} 
		self.foodon_maxid = 3400000

		self.counts = {}
		self.has_taxonomy = 0
		self.has_ITIS = 0
		self.no_taxonomy = 0
		self.food_additive = 0
		self.output = ''
		self.version = 0

		self.re_wikipedia_url = re.compile(r'http://en.wikipedia.org/wiki/(?P<reference>[^])]*)')
		self.re_duplicate_entry = re.compile(r'Duplicate entry of[^[]*\[(?P<id>[^\]]+)\]\*.') # e.g. "Duplicate entry of *CHILEAN CROAKER [B1814]*."


	def __main__(self, file):
		"""
		Create memory-resident data structure of captured Langual items.  Includes:
			- ALL FOOD SOURCE ITEMS, including:
				- animals and plants which have taxonomy.
				- chemical food aditives which get converted to CHEBI ontology references.


		# Each self.langual database entity has a primary status for its record:
		status:
			'ignore': Do not import this langual item.
			'import': Import as a primary ontology term.
			'is_obsolete': Import code but associate it as a hasDbArchaicXref:____ of other primary term.
				Arises when Langual term ids have been made archaic via merging or deduping.
				Algorithm:
				1st pass: ignore archaic terms
				2nd pass: process only archaic terms
					1: find primary term as [X1234] in <AI> content, OR
					2: Find primary term code in <RELATEDTERM>, OR
					3: Search for exact match on LABEL of ACTIVE entry, OR
					4: Assume PARENT is primary term.
					e.g.
					<AI>Duplicate entry of *YELLOWTAIL [B1779]*.
					<AI>Synonym of *CHILEAN PILCHARD [B1847]*</AI>
					... Descriptor inactivated. The descriptor is a synonym of *RED KINGKLIP [B1859]*.</AI>
					<RELATEDTERM>B2177</RELATEDTERM>

		"""
		if os.path.isfile(self.database_path):
			self.database = self.get_database_JSON(self.database_path)
			self.database['version'] +=1
			self.version = self.database['version']

		#file_handle = codecs.open(file, "r", "iso-8859-1")
		tree = ET.parse(file) # Incoming raw XML database file
		root = tree.getroot()

		for child in root.iter('DESCRIPTOR'):
			
			entity = { # Barebones entity
				'status': 'new',
				'is_a':[]
			} 

			# The source database's term ID is the one datum that can't be differentially compared to an existing entity value.
			database_id = self.load_attribute(entity, child, 'FTC') # FTC = Food Thesaurus Code ?!

			# Bring in existing entity if any
			if database_id in self.database['index']:
				entity = self.database['index'][database_id]
				if entity['status'] == 'new':
					entity['status'] = 'import'
			else:
				entity['database_id'] = database_id	
				self.database['index'][database_id] = entity

			if not entity['status'] in ['ignore', 'is_obsolete']:
				# Langual terms that are ACTIVE=false are by default imported as 'is_obsolete' 
				# ontology terms so we can still capture their ids for database cross-referencing.  
				# Downgrades Langual terms that go form active to inactive. But not reverse.
				if self.load_attribute(entity, child, 'ACTIVE','active') == 'False':
					entity['status'] = 'is_obsolete'

				scope_note = child.find('SN').text
				if scope_note and 'DO NOT USE for new indexing' in scope_note:
					entity['status'] = 'is_obsolete'

			# Pre-existing entity status controls whether item revisions are considered.  We skip doing updates on archaic items.
			if entity['status'] == 'ignore': 
				continue

			label = self.load_attribute(entity, child, 'TERM', 'label')

			# ITEM IN DATABASE MAY BE MULTI-HOMED.  As new parent_id is introduced, we need to keep old ones though.
			# Could keep it simple - not really using parent_ids directly.  Could remain a low-level set of ids.
			parent_id = self.load_attribute(entity, child, 'BT', 'parent_id')

			# Langual has some tagged text imbedded within other XML text.
			AI = child.find('AI').text
			if AI is not None:
				# Langual encoded html -> markdown italics
				AI = AI.replace('$i$','*').replace('$/i$','*').replace('$br/$','\n') 

				# FIRST CONVERT [http://en.wikipedia.org/wiki/Roselle_(plant)] references to IAO_0000119 'definition_source'
				wikipedia_ref = re.search(self.re_wikipedia_url, AI)
				if wikipedia_ref:
					entity['definition_source'] = 'WIKIPEDIA:' + wikipedia_ref.group('reference')
					AI = re.sub(self.re_wikipedia_url, '', AI)
					AI = AI.replace('[]','').replace('()', '')

				# SOME DUPLICATE ENTRIES EXIST
				duplicate = re.search(self.re_duplicate_entry, AI)
				# E.g "Duplicate entry of *CHILEAN CROAKER [B1814]*.""
				if duplicate:
					entity['replaced_by'] = duplicate.group('id')
					AI = re.sub(self.re_duplicate_entry, '', AI)

				self.load_attribute(entity, AI, '<DICTION>', 'definition')

			if entity['status'] == 'is_obsolete': 
				continue

			self.load_synonyms(entity, child)

			self.load_facet_details(entity, child)


		# 2nd pass: link up as many archaic langual terms as possible to primary entries
		for entityid in self.database['index']:
			entity = self.database['index'][entityid]
			if entity['status'] != 'ignore':
				ontology_id = self.load_ontology_id(entity)
				self.database['ontology'][ontology_id] = entity


		with (open(self.database_path, 'w')) as output_handle:
			output_handle.write(json.dumps(self.database, sort_keys=False, indent=4, separators=(',', ': ')))

		# Display stats and problem cases the import found
		self.report(file)

		self.save_ontology()


	# Customized for each ontology import source database.
	def load_ontology_id(self, entity):
		database_id = entity['database_id']
		# First character of Langual ontology id is a letter; we convert that to an integer 0-12
		# Yields FOODON_3[40-52][0000-9999]
		# I bet D,I,O missing because they can be confused with digits in printout
		if database_id == '00000':
			entity['ontology_id'] = 'FOODON_3400000'
		else:
			offset = 'ABCEFGHJKMNPRZ'.index(database_id[0]) 
			entity['ontology_id'] = 'FOODON_3' + str(40+offset) + database_id[1:5]
		return entity['ontology_id']


	def load_attribute(self, entity, child, xmltag, attribute=None):

		value = None

		# Have a Langual term here.  Features common to all terms:
		if isinstance(child, basestring): # Usually child is an xml parse object but added ability to spot text...
			ptr = child.find(xmltag)
			if ptr > -1:
				value = child[ptr+len(xmltag):] 
				# Would fetch everything from tag to beginning of next tag but issue is 
				# some <DESCR> tags have other tags injected in them but no closing tag.
			else:
				attribute = False

		elif child is not None:
			for value in child.iter(xmltag):	# was FIND 
				value = value.text

		#print xmltag, value

		if attribute:
			self.set_attribute_diff(entity, attribute, value)
		else:
			pass
			# WHAT TO DO WITH OLD ATTRIBUTES that no longer exist?


		return value


	def set_attribute_diff(self, entity, attribute, value):
		# All new values assumed to be ok.
		if not attribute in entity:
			entity[attribute] = OrderedDict()
			entity[attribute] = {
				'value': value, # Value ready for import
				'import': True, # False = do not import this attribute
				'locked': False, # Prevent database import from modifying its value
				'changed': True # Indicates if changed between between database.json and fresh version value.
			}

		# 'ignore' signals not to accept any values here.
		elif entity[attribute]['value'] != value:
			entity[attribute]['changed'] = True
			if entity[attribute]['locked'] == False:
				entity[attribute]['value'] = value
			# could push old values + versions onto a history stack
		else:
			entity[attribute]['changed'] = False


	def	load_synonyms(self, entity, child):

		entity['synonyms'] = {}
		#FUTURE: organize synonyms by language ?
		for synxml in child.iter('SYNONYM'): 
			if synxml[0:5] == 'INS ': # Intercepting Codex references
				entity['xref'] = 'Codex:' + synxml
			else:
				# Value could be shoehorned to mark up synonym language/source etc? 
				self.set_attribute_diff(entity['synonyms'], synxml.text, 'EXACT') 


	def save_ontology(self):
		# Now generate OWL or OBO ontology input file.
		obo_format = 'ontology: FOODON\n'
		obo_format += 'auto-generated-by:conversion.py\n'
		obo_format += 'date: ' +  time.strftime('%d:%m:%Y')  #dd:MM:yyyy
		obo_format += 'treat-xrefs-as-equivalent: NCBI_taxon\n'

		for entityid in self.database['index']:
			entity = self.database['index'][entityid]
			if entity['status'] != 'ignore':

				# For now accept only first parent as is_a parent
				# pick only items that are not marked "ignore"
				obo_format += '\n\n[Term]\n'
				obo_format += 'id: ' + entity['ontology_id'].replace('_',':') + '\n'
				obo_format += 'name: ' + entity['label']['value'] + '\n'
				obo_format += 'xref: [Langual:' + entity['database_id']
				if 'xref' in entity:
					obo_format += ', entity['xref'] 
				obo_format += ']\n'

				# TAXONOMY counts as xref

				if self.term_import(entity, 'parent_id'):
					parent = self.database['index'][entity['parent_id']['value']]
					parent_name = parent['label']['value']
					parent_id = parent['ontology_id']
					obo_format += 'is_a: ' + parent_id.replace('_',':') +' ! ' + parent_name + '\n'

				if self.term_import(entity, 'definition'):
					obo_format += 'def: "' + entity['definition']['value']
					if 'definition_source' in entity:
						obo_format += ' [' + entity['definition_source'] + ']\n'
					else:
						obo_format += '\n'

				if entity['status'] == 'is_obsolete':
					obo_format += 'is_obsolete: true\n'

				if 'replaced_by' in entity:
					replacement = self.database['index'][entity['replaced_by']]['ontology_id']
					obo_format += 'replaced_by: ' + replacement.replace('_',':') +'\n'

				if 'synonyms' in entity:
					for item in entity['synonyms']:
						if self.term_import(entity['synonyms'], item):
							detail = entity['synonyms'][item]['value']
							obo_format += 'synonym: "%s" %s\n' % detail , type # EXACT / NARROW / BROAD 


			"""
			OBO File Format: http://owlcollab.github.io/oboformat/doc/obo-syntax.html
			# treat-xrefs-as-equivalent
			# id-mapping: part_of OBO_REL:part_of
			"""

		with (codecs.open(self.ontology_path, 'w', 'utf-8')) as output_handle:
			output_handle.write(obo_format)


	def term_import(self, entity, term):
		return term in entity and entity[term]['value'] != None and entity[term]['import'] == True
#************************************************************

	def load_facet_details(self, entity, child):
		"""
		ENHANCE ENTITY WITH FACET-SPECIFIC ATTRIBUTES
		"""	

		# Stats on count of members of each Langual facet, which is first letter of entity id.
		category = entity['database_id'][0]
		if category in self.counts: 
			self.counts[category] += 1 
		else: 
			self.counts[category] = 1


		# A. PRODUCT TYPE [A0361]
		#if category == 'A': 
		#	pass

		# B. FOOD SOURCE [B1564]
		if category == 'B':
			self.getFoodSource(entity, child)

		# C. PART OF PLANT OR ANIMAL [C0116]
		#elif category == 'C': 
		#	pass

		# E. PHYSICAL STATE, SHAPE OR FORM [E0113]
		#elif category == 'E': 
		#	pass

		# F. EXTENT OF HEAT TREATMENT [F0011]
		elif category == 'F': 
			pass

		# G. COOKING METHOD [G0002]
		elif category == 'G': 
			pass

		#H. TREATMENT APPLIED [H0111]
		#elif category == 'H': 
		#	pass

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
		#	pass

		#P. CONSUMER GROUP/DIETARY USE/LABEL CLAIM [P0032]
		#elif category == 'P': 
		#	pass

		#R. GEOGRAPHIC PLACES AND REGIONS [R0010]
		#elif category == 'R': 
		#	pass

		#Z. ADJUNCT CHARACTERISTICS OF FOOD [Z0005]
		#elif category == 'Z': 
		#	pass


	def getFoodSource(self, entity, child):
		"""
		FIRST: trust ITIS identifier.
		IF NOT AVAILABLE, 
			TRY to get a TAXONOMIC HIT VIA SYNONYMS
				MANUALLY SET AUTO-PROCESS FLAGS ('is_obsolete','ignore'), etc.) WHICH GUIDE CURATION OF RESULTS.

		"""

		taxonomy = child.find('AI').text

		if taxonomy:
			taxObj = self.getTaxonomy(taxonomy)
			# Ignoring food additives here.  Long list, but perhaps we should just collect these as cross-references to CHEBI entries?
			if 'DICTION' in taxObj and 'food additive' in taxObj['DICTION'].lower():
				self.food_additive += 1
				# FOR NOW SKIP THESE
				return False

			else:
				self.has_taxonomy += 1
				entity['taxonomy'] = []
				if 'ITIS' in taxObj: 
					self.has_ITIS += 1 #print "TAXONOMY ITIS: ", taxObj['ITIS']
					entity['taxonomy'].append(taxObj['ITIS'])

					
		else:
			self.no_taxonomy += 1
			# + ':' + '|'.join(entity['synonyms'])
			self.output += '		' + str(entity['parent_id']) + '-' + entity['database_id'] + ':' + str(entity['label'])  + '\n'
		
			# Keeping Langual groupings of food.
			return True

		return True


	def getTaxonomy(self, lines_of_text):
		""" 
		Objective is to find THE MOST DETAILED instance of ITIS code - the one associated with "SCINAM" which comes after "SCIFAM" is mentioned (which may have its own ITIS code).
		If there is no ITIS code, then we may have to fallover to looking up SCINAM text, or synonym text, directly in ITIS OR EOL portal.

		Taxonomy roles in Langual:
			Kingdom / Subkingdom / Infrakingdom / Superdivision / Division / Subdivision [Phylum / Subphylum] / Class / Superorder / Order / Family / Genus / Species

		Example Langual record
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
		taxObj = {}
		for line in lines_of_text.split('\n'):
			# SCIINFORD an error?
			for taxlevel in ['SCIGEN','SCIINFCLASS','SCICLASS','SCISUPCLASS','SCIFAM','SCISUPFAM','SCISUBPHY','SCIPHY','SCISUBORD','SCIINFORD','SCIORD','SCIDIV','SCINAM','DICTION']:
				if taxlevel in line: 
					name = line[len(taxlevel)+2:]
					taxObj[taxlevel] = name
					# Match to reference databases that encyclopedia of life knows
					# Also other dbs: GRIN, MANSFELD, NETTOX, PLANTS, , EuroFIR-NETTOX, DPNL
					for db in ['ITIS','INDEX FUNGORUM','FISHBASE']: 

						prefix = '[' + db + ' '
						nameptr = name.find(prefix)
						if nameptr > -1 and db not in taxObj:
							nameptrend = name.find(']',nameptr + len(prefix) )
							taxObj[db] = db + ':' + name[nameptr + len(prefix) : nameptrend] #Note: some dbs have space delimited codes
						
			# If no codes, e.g. for "broiler chicken", <AI> will contain only text definition rather than <DICTION>


		return taxObj


	def getEOLData(self):
		"""
		Perform Lookup of NCBI_Taxon data directly from EOL.org via API and ITIS code.

		eol.org/pages/328663

		ITIS (903) SEARCH TO EOL ID/Batch of IDs:

			http://eol.org/api/search_by_provider/1.0.json?batch=true&id=180722%2C160783&hierarchy_id=903

		Returns:
			[{"180722":[
				{"eol_page_id":328663},
				{"eol_page_link":"eol.org/pages/328663"}
			]},
			{"160783":[
				{"eol_page_id":8897},
				{"eol_page_link":"eol.org/pages/8897"}]
			}]

		http://eol.org/api/docs/provider_hierarchies

			596 : "Index Fungorum"
			903 : "ITIS" SEARCH TO EOL ID/Batch of IDs:
			1172 : "NCBI Taxonomy"

		http://eol.org/api/pages/1.0.json?batch=true&id=328663&subjects=overview&common_names=true&synonyms=true&taxonomy=true&cache_ttl=&language=en

		NOTE ALSO

			http://www.itis.gov/web_service.html
			http://www.itis.gov/ITISWebService/jsonservice/getFullRecordFromTSN?tsn=500059
			http://www.itis.gov/ITISWebService/jsonservice/getFullRecordFromTSN?tsn=202384&jsonp=itis_data
			http://www.itis.gov/ITISWebService/jsonservice/getHierarchyUpFromTSN?tsn=1378

		"""
		pass


	def report(self, file):
		print
		print "LANGUAL IMPORT of [" + file + ']'
		print "Facet item counts"
		print self.counts				
		print
		print "Food source (facet B) stats"
		print "	Food additive items: ", self.food_additive
		print "	Items with taxonomy: ", self.has_taxonomy
		print "	  Items having ITIS: ", self.has_ITIS
		print "	Items without taxon: ", self.no_taxonomy
		print "		parent_id-child_id : name : synonyms"	
		# Getting: UnicodeEncodeError: 'ascii' codec can't encode character u'\xd7' in position 17332: ordinal not in range(128)

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
	foodstruct.__main__('langual2014.utf.xml')


