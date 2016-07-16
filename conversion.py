#!/usr/bin/python
# -*- coding: utf-8 -*-
# Author: Damion Dooley
# 
# conversion.py
""" 
Reads Langual.org thesaurus XML file and parses items, extracting: 

	- Items having taxonomic scientific names.  These are all in the Food Source facet.  A lookup of eol.org taxonomic database reference to NCBI taxonomy name is performed (alternatly make entries to cover ITIS items?)  Result is an NCBI taxon tree as well as a tree of food source items. 
	- Items in preservation facet.
	- ?

End product will be OWL ontology file include that contains all the necessary attributes for inclusion into FOODON.

"""
import json
from pprint import pprint
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

#... rulefileobj =  json.load(rules_handle, object_pairs_hook=OrderedDict)


CODE_VERSION = '0.0.1'

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
		pass

	def __main__(self, file):
		"""
		Example record
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
		"""

		langual = {}

		tree = ET.parse(file)
		root = tree.getroot()
		counts = {}
		has_taxonomy = 0
		has_ITIS = 0
		no_taxonomy = 0
		food_additive = 0
		for child in root.iter('DESCRIPTOR'):
			active = child.find('ACTIVE').text

			'term is only kept for backward compatibility. DO NOT USE for new'
			if active.lower() != 'true':
				continue;

			scope_note = child.find('SN').text
			if scope_note and 'term is only kept for backward compatibility. DO NOT USE for new indexing' in scope_note :
				continue;

			code = child.find('FTC')

			# ALL FOOD SOURCE ITEMS, which have taxonomy.

			category = code.text[0]
			# Stats on count of members of each facet


			if category in counts: counts[category] += 1
			else: counts[category] = 1;	

			if category == 'B':
				term = child.find('TERM')
				parent = child.find('BT')
				taxonomy = child.find('AI').text
				synonyms = []
				for synxml in child.iter('SYNONYM'): #FUTURE: organize synonyms by language
					synonyms.append(synxml.text)


				if taxonomy:
					taxObj = self.getTaxonomy(taxonomy)
					# Ignoring food additives here
					if 'DICTION' in taxObj and 'food additive' in taxObj['DICTION'].lower():
						food_additive += 1
						
					else:
						has_taxonomy += 1
						if 'ITIS' in taxObj: 
							has_ITIS += 1 #print "TAXONOMY ITIS: ", taxObj['ITIS']
							#eol.org/pages/328663
							continue
				else:
					no_taxonomy += 1

					print parent.text,'-',code.text, term.text, '|'.join(synonyms)

					

		print "Has taxonomy: ", has_taxonomy, "Has ITIS: ", has_ITIS, "No taxonomy: ", no_taxonomy, "Food additive: ", food_additive
		print counts

		"""
		#with open(file) as data_file:    
 		#	self.struct = json.load(data_file)
		#pass
		# http://www.itis.gov/web_service.html
		# http://www.itis.gov/ITISWebService/jsonservice/getFullRecordFromTSN?tsn=500059
		# http://www.itis.gov/ITISWebService/jsonservice/getFullRecordFromTSN?tsn=202384&jsonp=itis_data
		# http://www.itis.gov/ITISWebService/jsonservice/getHierarchyUpFromTSN?tsn=1378

		# ITIS (903) SEARCH TO EOL ID/Batch of IDs:
		# http://eol.org/api/search_by_provider/1.0.json?batch=true&id=180722%2C160783&hierarchy_id=903
		# Returns:
		# [{"180722":[
			{"eol_page_id":328663},
			{"eol_page_link":"eol.org/pages/328663"}
		]},
		{"160783":[
			{"eol_page_id":8897},
			{"eol_page_link":"eol.org/pages/8897"}]
		}]

		#http://eol.org/api/docs/provider_hierarchies
		596 : "Index Fungorum"
		903 : "ITIS" SEARCH TO EOL ID/Batch of IDs:
		1172 : "NCBI Taxonomy"

		http://eol.org/api/pages/1.0.json?batch=true&id=328663&subjects=overview&common_names=true&synonyms=true&taxonomy=true&cache_ttl=&language=en

		# ISSUE: Some "lines" in lines_of_text might not be separated by a carriage return. <SCINAM>Hapalochlaena maculosa (Hoyle, 1883) [ITIS 556175]<.... > 

		
		PROBLEM CASE:
		TAXONOMY:  <SCIFAM>Apiaceae
		<SCINAM>Apium graveolens var. rapaceum (Miller) Gaudin
		<ITIS>530941
		<GRIN>3704
		<MANSFELD>1236
		B1057 - B1736 SESBANIA agati grandiflora|sesbania grandiflora



		SPICE OR FLAVOR-PRODUCING PLANT [B1179]


		MUSTARD AND CRESS [B4301]
		"""
	def getTaxonomy(self, lines_of_text):
		""" Objective is to find first instance of ITIS code - the most detailed one
		# Kingdom / Subkingdom / Infrakingdom / Superdivision / Division / Subdivision [Phylum / Subphylum] / Class / Superorder / Order / Family / Genus / Species
		"""
		taxObj = {}
		for line in lines_of_text.split('\n'):
			# SCIINFORD an error?
			for taxlevel in ['SCINAM','SCIGEN','SCIINFCLASS','SCICLASS','SCISUPCLASS','SCIFAM','SCISUPFAM','SCISUBPHY','SCIPHY','SCISUBORD','SCIINFORD','SCIORD','SCIDIV','DICTION']:
				if taxlevel in line: 
					name = line[len(taxlevel)+2:]
					taxObj[taxlevel] = name
					# Match to reference databases that encyclopedia of life knows
					for db in ['ITIS','INDEX FUNGORUM','FISHBASE']: # GRIN, MANSFELD, NETTOX, PLANTS, , EuroFIR-NETTOX, DPNL
						prefix = '[' + db + ' '
						nameptr = name.find(prefix)
						if nameptr > -1 and db not in taxObj:
							nameptrend = name.find(']',nameptr + len(prefix) )
							taxObj[db] = name[nameptr + len(prefix) : nameptrend] #Note: some dbs have space delimited codes
						
			# If no codes, e.g. for "broiler chicken", <AI> will contain only text definition rather than <DICTION>


		return taxObj


if __name__ == '__main__':

	genepio = Langual()
	genepio.__main__('langual2014.xml')


