#import "main-defs.typ": *

#source(17)
= Algebraic K-Theory <ch:algebraic-k-theory>

The aim of this chapter is to provide a self-contained introduction to
“classical” algebraic $K$-theory, with special emphasis on the $K$-theory of
integral group rings. We shall concentrate here on the Grothendieck group
$K_0 lr((cal(C)))$ of the category $cal(C)$, the Whitehead group $K_1 lr((A))$
of the ring $A$, and the Milnor group $K_2 lr((A))$. In adopting this
nomenclature, we have followed the books on algebraic $K$-theory by Bass
@bib:Bass1968, Milnor @bib:Milnor1971, Swan @bib:Swan1968, and Swan–Evans
@bib:SwanEvans1970, as well as the Battelle Conference Notes (Bass
@bib:Bass1973a–@bib:Bass1973c).

Other authors occasionally use different terminology. In particular, for a
finite group $G$ there is also a “Whitehead group” $op("Wh")(ZZ G)$, discussed
at length in §@sec:whitehead-integral-group-rings. It will be clear from the
context whether the term “Whitehead group” refers to $K_1 lr((ZZ G))$ or
$op("Wh")(ZZ G)$.

We have already encountered, in §@i:ss:grothendieck-groups, the definitions of
the Grothendieck group $G_0 lr((R G))$ and the projective class group
$K_0 lr((R G))$, where $R$ is a commutative ring and $G$ a finite group. After
recalling their definitions in §@ss:grothendieck-frobenius, we relate them to T.
Y. Lam’s axiomatic theory of Frobenius functors. In §@ss:grothendieck-projective
we treat $G_0 lr((A))$ and $K_0 lr((A))$ for an arbitrary ring $A$. As shown in
§@ss:regular-rings, we have $G_0 lr((A)) tilde.equiv K_0 lr((A))$ whenever the
ring $A$ is regular (that is, each f.g. $A$-module has finite homological
dimension). The section ends with a discussion of localization sequences, an
important topic which reappears in §@ss:grothendieck-localization and
§@ss:whitehead-localization.

Section @sec:grothendieck-integral-group-rings is devoted to Swan’s results on
the Grothendieck group $G_0 lr((R G))$, and its calculation by a formula due to
Heller–Reiner when $R$ is a Dedekind domain in an algebraic number field. In
§@sec:whitehead-groups, we treat $K_1 lr((A))$, and begin by showing that the
determinantal version $K_"det" lr((A))$, in §@sec:grothendieck-groups, agrees
with the definition here, namely $K_1 lr((A)) tilde.equiv GL(A) slash GL(A)'$.
After discussing localization sequences, we come to the important concepts of
elementary matrices, Steinberg relations, and stable range. This last concept
plays a central role in §@sec:basic-elements-stable-range, where we give the
Eisenbud–Evans theory of basic elements, which in turn yields Bass’s fundamental
Stable Range Theorem.

In §@sec:mayer-vietoris we give Milnor’s exact sequence of $K$-groups, arising
from a suitable fiber product of rings. This “Mayer–Vietoris sequence” is of the
utmost importance in calculations of $K$-groups. As shown in §@sec:milnor-k2,
under suitable hypotheses it can be extended to the left by $K_2$-groups.

Section @sec:polynomial-k-theory briefly considers the $K$-theory of polynomial
rings and gives Seshadri’s proof of a special case of Serre’s conjecture.
Section @sec:relative-k-theory is a rather technical one on relative $K$-theory,
and its results are fundamental for our discussion of $S K_1$ in
§@ss:sk1-finiteness, as well as for the proof in §@sec:milnor-k2 of Milnor’s
extended Mayer–Vietoris sequence.
#source(18)

Now let $Lambda$ be an order in an algebra $A$, and define $S K_1 lr((Lambda))$
as the kernel of the map $K_1 lr((Lambda)) -> K_1 lr((A))$. In
§@ss:sk1-maximal-orders we give Keating’s formula for $S K_1 lr((Lambda))$ when
$Lambda$ is a maximal order; his proof uses the extended localization sequence
from Quillen’s $K$-theory. Using Keating’s result, and some facts on relative
$K$-theory from §@sec:relative-k-theory, we give a new proof of Bass’ important
theorem that $S K_1 lr((Lambda))$ is finite when $A$ is a f.d. separable algebra
over a global field. The section concludes with a discussion of profinite
groups, in preparation for §@sec:whitehead-integral-group-rings.

Section @sec:whitehead-integral-group-rings gives Wall’s theorems on
$S K_1 lr((R G))$ and the Whitehead group $op("Wh")(R G)$ of an integral group
ring. The most striking result is that when $R$ is the ring of algebraic
integers in a number field, the torsion subgroup of $K_1 lr((R G))$ is precisely
$ ("torsion subgroup of" R^dot) times G^(a b) times S K_1 lr((R G)). $
This may be viewed as a far-reaching generalization of G. Higman’s theorem on
torsion units in $R G$ when $G$ is abelian.

In §@sec:milnor-k2 we give a brief introduction to $K_2$, following the
treatment in Milnor @bib:Milnor1971, and occasionally referring the reader to
that reference for some of the proofs. The section includes a discussion of
“symbols” and their relation to reciprocity laws in number theory. In
§@sec:sk1-integral-group-rings we summarize (without proof) the known results on
$S K_1 lr((R G))$.

As can be seen from the above, we have largely omitted Quillen’s higher
$K$-theory, an important new approach which lies outside the scope of our book.
So too do the connections between algebraic $K$-theory and topology, though we
have listed some references for this subject at the end of the introduction to
Chapter @ch:class-groups. For further reading on these omitted topics, we refer
the reader to the “standard” references on algebraic $K$-theory, namely, Milnor
@bib:Milnor1966, @bib:Milnor1971, Bass @bib:Bass1973a–@bib:Bass1973c, Stein
@bib:Stein1976, @bib:Stein1978, Friedlander–Stein @bib:FriedlanderStein1981,
Dennis @bib:Dennis1982, and Bak @bib:Bak1984. See also the useful books by
McDonald @bib:McDonald1984 and Silvester @bib:Silvester1981.
