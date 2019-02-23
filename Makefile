ALL_TARGETS :=
STDM_LHS_SOURCES := Stdm.lhs
STDM_LHS_TARGETS := Stdm.hi Stdm.o StdmPrelude.hi StdmPrelude.o

.PHONY: default
default: Stdm.o

$(STDM_LHS_TARGETS): $(STDM_LHS_SOURCES)
	stack ghc $<
ALL_TARGETS += $(STDM_LHS_TARGETS)

.PHONY: clean
clean:
	rm -rf $(ALL_TARGETS)
