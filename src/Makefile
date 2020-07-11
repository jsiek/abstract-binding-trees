ROOT = /Users/jsiek/abstract-binding-trees
BUILD_DIR = $(ROOT)/_build/2.6.1/agda

AGDA =	ScopedTuple.agda \
	Var.agda \
	AbstractBindingTree.agda \
	Map.agda \
	GSubst.agda \
	GenericSubstitution.agda \
	Renaming.agda \
	MapFusion.agda \
	Substitution.agda \
	ABTPredicate.agda \
	Fold.agda \
	MapPreserve.agda \
	WellScoped.agda \
	FoldPreserve.agda \
	FoldMapFusion.agda \
	FoldFoldFusion.agda \
	Syntax.agda \
	examples/Lambda.agda \
	examples/Arith.agda \
	examples/BlogTypeSafetyTwoEasy.lagda.md

AGDAI = $(AGDA:%.agda=$(BUILD_DIR)/src/%.agdai)

$(BUILD_DIR)/src/%.agdai: %.agda
	agda $<

all: $(AGDA) $(AGDAI)

clean:
	rm -f $(BUILD_DIR)/src/*.agdai $(BUILD_DIR)/src/examples/*.agdai *~
