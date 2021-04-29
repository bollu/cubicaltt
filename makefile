.PHONY: docco cubical

docco:
	docco *.hs Exp/*
	cd docs && python3 -m http.server

cubical:
	stack build cubical 
	stack exec cubical
