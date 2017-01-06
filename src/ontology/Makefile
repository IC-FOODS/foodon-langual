OBO=http://purl.obolibrary.org/obo
ONT=foodon
BASE=$(OBO)/$(ONT)
SRC=$(ONT)-edit.owl
RELEASEDIR=../..
ROBOT= robot
OWLTOOLS= owltools


all: all_imports $(ONT).owl 
test: all
prepare_release: all 
	cp $(ONT).owl $(RELEASEDIR) &&\
	cp imports/*.owl $(RELEASEDIR)/imports/ &&\
	git add $(RELEASEDIR)/imports/*.owl &&\
	(test -f subsets/*.owl && cp subsets/*.owl $(RELEASEDIR)/subsets && git add $(RELEASEDIR)/subsets/* || echo "no subsets") &&\
	echo "Release files are now in $(RELEASEDIR) - now you should commit, push and make a release on github"

#Annotates foodon.owl ( $(ONT).owl ) file with release
$(ONT).owl: $(SRC)
	$(ROBOT) reduce -i $< -r ELK -s true annotate --xml-entities -V $(BASE)/releases/`date +%Y-%m-%d`/$(ONT).owl -o $@

# ALL OWL imports: chebi efo envo eo gazetteer ncbitaxon obi ro uberon langual
# ALL OntoFox imports: chebi efo envo eo gazetteer ncbitaxon obi ro 
IMPORTS = chebi efo eo ncbitaxon obi ro uberon
IMPORTS_OWL = $(patsubst %, imports/%_import.owl,$(IMPORTS))

# Make this target to regenerate ALL
all_imports: $(IMPORTS_OWL)

# Only fetches .owl if it doesn't exist or if .txt has later timestamp.
imports/%_import.owl: imports/%_ontofox.txt
	curl -s -F file=@imports/$*_ontofox.txt -o $@ http://ontofox.hegroup.org/service.php
	$(ROBOT) reduce -i $@ -r ELK -s true --xml-entities -o $@
	# All annotations are manually curated in the ontology-metadata.owl file
	# Because OWLAPI is erroniously parsing 1 line commented out annotations, make this step last:
	# Error trap the sed command - on Macs we need the '.bak' after -i to avoid a parsing error; while on other linux it fails
	sed -i '.bak' 's/<owl:AnnotationProperty[^>]*\/>/<!-- & -->/; s/<\/owl:AnnotationProperty>/& -->/; s/<owl:AnnotationProperty[^>]*">/<!-- &/;' $@ ||	sed -i 's/<owl:AnnotationProperty[^>]*\/>/<!-- & -->/; s/<\/owl:AnnotationProperty>/& -->/; s/<owl:AnnotationProperty[^>]*">/<!-- &/;' $@


# Use ROBOT, driven entirely by terms lists NOT from source ontology
#imports/%_import.owl: mirror/%.owl imports/%_terms.txt
#	$(ROBOT) extract -i $< -T imports/$*_terms.txt --method BOT -O $(BASE)/$@ -o $@

.PRECIOUS: imports/%_import.owl

# clone remote ontology locally, perfoming some excision of relations and annotations
#mirror/%.owl: $(SRC)
#	$(OWLTOOLS) $(OBO)/$*.owl --remove-annotation-assertions -l -s -d --remove-dangling-annotations  -o $@
#.PRECIOUS: mirror/%.owl

release: $(ONT).owl 
	cp $^ $RELEASEDIR && cp imports/*.owl $RELEASEDIR/imports
