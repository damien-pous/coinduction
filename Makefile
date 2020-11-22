-include Makefile.coq

Makefile.coq: 
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

cleanall:: clean
	rm -f Makefile.coq* depgraph.*

depgraph::
	coqdep *.v -dumpgraph depgraph.dot 1>/dev/null 2>/dev/null
	sed -i 's/\[label=\"\([^"]*\)\"]/[label="\1";URL=".\/html\/cawu.\1.html"]/g' depgraph.dot
	dot depgraph.dot -Tsvg -o depgraph.svg
