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
allows to be imported into langual.json

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
import xml.etree.ElementTree as ET

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

		# READ THIS FROM langual.json
		self.langual = {'langual_index': OrderedDict(), 'ontology': OrderedDict() } #empty case.
		self.foodon_maxid = 3400000

		self.counts = {}
		self.has_taxonomy = 0
		self.has_ITIS = 0
		self.no_taxonomy = 0
		self.food_additive = 0
		self.output = ''


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
			'archaic': Import code but associate it as a hasDbArchaicXref:____ of other primary term.
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

		tree = ET.parse(file)
		root = tree.getroot()

		for child in root.iter('DESCRIPTOR'):
			
			entity = {'status': None}

			active = child.find('ACTIVE').text.lower()

			#Only including Langual terms that are ACTIVE=true .
			# HAVE TO DOWNGRADE Langual terms that go form active to inactive????
			if active != 'true':
				continue;

			scope_note = child.find('SN').text
			if scope_note and 'DO NOT USE for new indexing' in scope_note:
				continue

				entity['status'] = 'archaic'

			# Have a Langual term here.  Features common to all terms:
			lid =	child.find('FTC').text # FTC = Food Thesaurus Code ?!
			entity['langual_id'] = lid
			entity['langual_parent_id'] = child.find('BT').text
			entity['rdfs:label'] =		child.find('TERM').text
		
			#Synonyms:
			entity['synonyms'] = []
			for synxml in child.iter('SYNONYM'): #FUTURE: organize synonyms by language
				entity['synonyms'].append(synxml.text)

			# Stats on count of members of each facet
			category = entity['langual_id'][0]
			if category in self.counts: self.counts[category] += 1 
			else: self.counts[category] = 1

			l_import = False

			# A. PRODUCT TYPE [A0361]
			#if category == 'A': 
			#	pass

			# B. FOOD SOURCE [B1564]
			elif category == 'B':
				l_import = self.getFoodSource(entity, child)

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

			if l_import:

				# Determine if item already exists in json data file
				if not lid in self.langual['langual_index']:
					entity['langual_parents'] = [entity['langual_parent_id']]
					self.langual['langual_index'][lid] = entity
					self.langual['ontology']['FOODON_'+ str(self.foodon_maxid)] = entity
					self.foodon_maxid += 1
				else:
					# Within a new database, duplicates arise simply because of multi-homing an item
					# Duplicates appear only to differ by parent_id.
					# print "DUPLICATE", entity

					existing_entity = self.langual['langual_index'][lid]
					existing_entity['langual_parents'].append(entity['langual_parent_id'])

					pass
					# Update existing record
					# Allow for archiving of current record. 
				
		# 2nd pass: link up as many archaic langual terms as possible:
		for child in root.iter('DESCRIPTOR'):
			pass 

		with (open('./langual.json','w')) as output_handle:
			output_handle.write(json.dumps(self.langual,  sort_keys=False, indent=4, separators=(',', ': ')))

		# Display stats and problem cases the import found
		self.report(file)


	def getFoodSource(self, entity, child):
		"""
		FIRST: trust ITIS identifier.
		IF NOT AVAILABLE, 
			TRY to get a TAXONOMIC HIT VIA SYNONYMS
				MANUALLY SET AUTO-PROCESS FLAGS ('archaic','ignore'), etc.) WHICH GUIDE CURATION OF RESULTS.

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

			self.output += '		' + entity['langual_parent_id'] + '-' + entity['langual_id'] + ':' + entity['rdfs:label'] + ':' + '|'.join(entity['synonyms']) + '\n'
		
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
		print self.output


	def getCurrentOntology(self, file):
		"""
		Load existing JSON representation of OWL ontology (created last time OWL ontology was saved)
		Will be updated if LANGUAL database has changed.
		"""
		with open(file) as data_file:    
 			self.struct = json.load(data_file, object_pairs_hook=OrderedDict)


if __name__ == '__main__':

	foodstruct = Langual()
	foodstruct.__main__('langual2014.xml')


