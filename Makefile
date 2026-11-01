KNOWNTARGETS := RocqMakefile
KNOWNFILES   := Makefile _RocqProject

.DEFAULT_GOAL := invoke-rocqmakefile

# use the rocq-package option if rocq version supports it
PACKAGE_NAME = rocq-coinduction
ROCQPKG := $(shell if rocq makefile --no-rocq-package-warning -v >/dev/null 2>&1; then echo "--rocq-package $(PACKAGE_NAME) --legacy-support"; fi)

RocqMakefile: Makefile _RocqProject
	$(ROCQBIN)rocq makefile -f _RocqProject $(ROCQPKG) -o RocqMakefile

invoke-rocqmakefile: RocqMakefile
	$(MAKE) --no-print-directory -f RocqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-rocqmakefile $(KNOWNFILES)

cleanall:: clean
	rm -f RocqMakefile* *.d *.log */*.glob */.*.aux */*.vo*

depgraph.dot::
	@echo building dependency graph
	@echo "digraph {" > $@
	@ls -1 theories/*.v | grep -v theories/all |grep -v theories/tests |sed 's#theories/\(.*\)\.v#\1 [URL=".\/html\/Coinduction.\1.html"];#g' >> $@
	@$(ROCQBIN)rocq dep -f _RocqProject -dyndep no \
	| sed -n 's/\.vo.*:.*\.v /->{/p' \
	| grep -v tests \
	| sed 's/[^ ]*rocqworker//g' \
	| sed 's/[^ ]*META[^ ]*//g' \
	| sed 's/\.vo//g' \
	| sed '/^^ *$$/d' \
	| sed 's/[ ]$$/};/g' \
	| sed 's/  */;/g' \
	| sed 's#theories/##g' \
	| sed 's#all.*##g' \
	>> $@;
	@echo "}" >> $@

%.svg: %.dot
	tred $< | dot -Tsvg -o $@

# This should be the last rule, to handle any targets not declared above
%: invoke-rocqmakefile
	@true
