---
layout: ontology_detail
id: foodon
title: foodon
jobs:
  - id: https://travis-ci.org/FoodOntology/foodon
    type: travis-ci
build:
  checkout: git clone https://github.com/FoodOntology/foodon.git
  system: git
  path: "."
contact:
  email: pbuttigi@mpi-bremen.de
  label: Pier Luigi Buttigieg
description: foodon is an ontology which represents food products, preparation techniques, and production.
domain: food, food production, food preparation
homepage: http://foodontology.github.io/foodon/
products:
  - id: foodon.owl
  - id: foodon.obo
dependencies:
 - id: bfo
 - id: ro
 - id: envo
 - id: uberon
 - id: chebi
tracker: https://github.com/FoodOntology/foodon/issues
license:
  url: http://creativecommons.org/licenses/by/3.0/
  label: CC-BY
---

The need to represent knowledge about food is central to many fields including biomedicine and sustainable development. FOODON is a new ontology built to interoperate with the OBO Library and to represent entities which bear a “food role”. It encompasses materials in natural ecosystems and food webs as well as human- centric categorization and handling of food. The latter will be the initial focus of the ontology, and we aim to develop semantics for food safety, food security, the agricultural and animal husbandry practices linked to food production, culinary, nutritional and chemical ingredients and processes. This project is motivated by the recognition that although several resources and standards for indexing food descriptors currently exist, their content and interrelations are not semantically and logically coherent.

The scope of FOODON is ambitious and will require input from multiple domains. FOODON will import or map to material in existing ontologies and standards and will create content to cover gaps in the representation of food-related products and processes. The products of this work are being applied to research and clinical datasets such as those associated with the Canadian Healthy Infant Longitudinal Development (CHILD) study which examines the causal factors of asthma and allergy development in children, and the Integrated Rapid Infectious Disease Analysis (IRIDA) platform for genomic epidemiology and foodborne outbreak investigation.
