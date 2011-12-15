all: TypeSystemSemantics.vo TypeSystemKripkeSemantics.vo ChurchNaturals.vo ChurchBooleans.vo ChurchLists.vo ChurchSyntax.vo ChurchVarSyntax.vo ChurchIdentity.vo ChurchStateAlgebra.vo

.v.vo:
	coqc -impredicative-set $* -dump-glob $*.glob

.SUFFIXES: .v .vo

clean:
	rm -f *.vo *~ .coqdeps *.glob

-include .coqdeps

.coqdeps: *.v
	@coqdep -I . *.v >.coqdeps
