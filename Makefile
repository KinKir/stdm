TARGETS :=

.PHONY: default
default: Stdm.o

Stdm.hi Stdm.o: Stdm.lhs
	stack ghc $<
TARGETS += Stdm.hi Stdm.o

.PHONY: clean
clean:
	rm -rf $(TARGETS)
