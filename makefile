.PHONY: docco cubical

docco:
	docco *.hs Exp/*

cubical:
	stack build cubical 
	stack exec cubical
