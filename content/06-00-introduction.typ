#import "main-defs.typ": *

#source(232)
= Class Groups of Integral Group Rings and Orders <ch:class-groups>

In this chapter we shall define the locally free class group $op("Cl") Lambda$
of an order $Lambda$, with special emphasis on the case $Lambda = ZZ G$, $G$ a
finite group. The class group $op("Cl") ZZ G$ was introduced by Swan
@bib:Swan1960, as the kernel of the rank homomorphism $K_0 lr((ZZ G)) -> ZZ$.
Most of the applications to topology and algebraic number theory, for which we
refer the reader to the references listed at the end of this introduction,
involve the group ring case. Further, most of the detailed calculations of class
groups in §§@sec:class-groups-integral-group-rings–@sec:p-adic-logarithms-taylor
are for this special case.

However, many of the techniques for determining $op("Cl") ZZ G$ depend on
reducing the problem to the calculation of $op("Cl") Lambda$, for various orders
$Lambda$ which are not group rings. For more general orders, $op("Cl") Lambda$
was first studied by Jacobinski @bib:Jacobinski1968b#ed-note[
  The original citation [68] does not distinguish the two 1968 papers.
  @bib:Jacobinski1968b is selected here as a contextual identification: its
  Theorem 2.2 gives the genus and ideal-class formula, and this section later
  explicitly cites [68b] before @th:class-group-reduced-norm-ideles.
] in his fundamental work on genera of lattices. His results were recast by
Fröhlich @bib:Frohlich1975 in terms of ideles, and it is this idele version
which we shall use most often. Fröhlich @bib:Frohlich1976 later reformulated
this approach, obtaining the “Hom formula” for $op("Cl") Lambda$ given in
§@sec:frohlich-hom-description.

This chapter is largely independent of Chapter @ch:algebraic-k-theory, except
that in §@ss:class-group-basic-formulas we derive the basic formulas for class
groups by using the Localization Sequence @th:whitehead-localization-sequence of
algebraic $K$-theory. We shall also need some facts about reduced norms and
their connection with $K_1$, as described in §@sec:sk1-orders.

In §@ss:class-group-basic-formulas, we derive the main formulas for the locally
free class group $op("Cl") Lambda$ of an order $Lambda$ (in a f.d. separable
algebra), and introduce the kernel group $D(Lambda)$ which measures the
discrepancy between $op("Cl") Lambda$ and $op("Cl") Lambda'$, where $Lambda'$ is
a maximal order containing $Lambda$. Since $op("Cl") Lambda'$ is easily
described in practice, much of the effort lies in determining $D(Lambda)$. We
briefly discuss the functorial properties of $op("Cl") Lambda$ and $D(Lambda)$
in §@ss:class-group-functorial-kernel, @ss:class-group-frobenius.

The lengthy §@sec:class-groups-integral-group-rings gives many examples of the
calculation of $op("Cl") ZZ G$ and $D(ZZ G)$, starting with the case in
§@ss:cyclic-squarefree-class-groups where $G$ is cyclic of squarefree order. In
§@ss:cyclic-p-group-class-groups, we treat the much harder case of cyclic
$p$-groups. Metacyclic groups are studied in §@ss:metacyclic-class-groups, while
§@ss:dihedral-quaternion-class-groups is devoted to dihedral and quaternion
groups. The section concludes in §@ss:crossed-product-order-kernel-groups with
the important result, due to Wilson, that $D(Lambda) = 0$ for $Lambda$ a twisted
group ring, or more generally, a crossed-product order.

In §@ss:jacobinski-cancellation we prove the fundamental Jacobinski Cancellation
Theorem, following a new approach by Swan @bib:Swan1980.
#source(233)
Section @sec:frohlich-hom-description is devoted to Fröhlich’s “Hom formula”
$op("Cl") R G$, which plays a key role in Taylor’s calculation of the Swan
subgroup $T(G)$ of $op("Cl") ZZ G$, where $G$ is any $p$-group (see
§@sec:p-adic-logarithms-taylor). The chapter concludes with §@sec:picard-groups
on Picard groups of orders, where one studies invertible two-sided ideals of an
order, rather than locally free one-sided ideals.

The reader will find that some of the calculations in
§@sec:class-groups-integral-group-rings rely heavily on results from algebraic
number theory. Even the special case of calculating $D(ZZ G)$, where $G$ is a
cyclic group of order $p^2$, already leads to difficult questions about
cyclotomic fields (see §@ss:cyclic-p-group-class-groups). On the other hand, the
locally free class group $op("Cl") ZZ G$ (for arbitrary $G$) has important
applications to questions in algebraic number theory, especially those connected
with the existence of normal integral bases (see
@exm:integers-tamely-ramified-extensions and §@ss:normal-integral-bases). For a
systematic treatment of such applications, we refer the reader to the
fundamental works of Fröhlich @bib:Frohlich1983, @bib:Frohlich1984, and to the
references listed therein.

It is beyond the scope of this book to treat the many applications of locally
free class groups to problems in algebraic topology. In the introduction to
Chapter @ch:algebraic-k-theory, we have already listed a number of references in
which algebraic $K$-theory is applied to topological problems. Here, we list
further references, more closely connected with topological applications of
class groups. The authors wish to thank R. Oliver and J. Arnold for helpful
comments.

To begin with, let $X$ be a $C W$-complex with fundamental group $G$. There is a
“Swan–Wall invariant”, with values in $op("Cl") ZZ G$, measuring the obstruction
to $X$ being homotopy equivalent to a finite $C W$-complex. For details, see
Swan @bib:Swan1960b, Wall @bib:Wall1965, @bib:Wall1966.

The above problem is connected with that of determining which finite groups can
act freely on a sphere. For this topic, see Swan @bib:Swan1960b, Thomas
@bib:Thomas1981, Milgram @bib:Milgram1981, @bib:Milgram1982, Madsen
@bib:Madsen1983.

In some topological problems, there is an obstruction taking values in
$op("Cl") lr((ZZ G)) slash T(G)$, where $T(G)$ is the Swan subgroup. In this
connection, see Swan @bib:Swan1960b, Endo–Miyata @bib:Endo1973, Oliver
@bib:Oliver1978.
