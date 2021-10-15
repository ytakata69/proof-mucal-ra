targets = raToEqnsys.vo
srcs = ltl.v eqnSys.v automata.v raToEqnsys.v
docdir = ./docs
vobjs = $(srcs:.v=.vo)

.PHONY: default all doc clean distclean
%.vo: %.v
	coqc $<

default: $(targets)
all: $(targets)

raToEqnsys.vo: ltl.vo eqnSys.vo automata.vo
automata.vo: ltl.vo eqnSys.vo
eqnSys.vo: ltl.vo

doc: $(vobjs)
	test -d $(docdir) || mkdir $(docdir)
	coqdoc --gallina --utf8 -d $(docdir) $(srcs)

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~

distclean: clean
	$(RM) $(docdir)/*.{html,css}
