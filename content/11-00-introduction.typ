#import "main-defs.typ": *
#import "statements.typ": *

#source(853)
= The Burnside Ring and the Representation Ring of a Finite Group
<ch:representation-rings>

This chapter contains a study of two commutative rings associated with
categories of $G$-modules, in much the same way as the ring $op("ch") G$ of
virtual complex characters arises from the category of f.g. $CC G$-modules.

The first is the _Burnside ring_ $Omega(G)$, which is the commutative ring
consisting of all formal $ZZ$-linear combinations of finite $G$-sets, with
addition defined by taking disjoint unions, and multiplication by cartesian
products. The main results include the construction of a family of homomorphisms
from $Omega(G)$ to $ZZ$ that separate elements of $Omega(G)$, a description of
the set of prime ideals of $Omega(G)$, and an induction theorem due to Conlon,
which is a generalization of the Artin Induction Theorem.

The second is the _representation ring_ $a(R G)$, for a commutative integral
domain $R$. It consists of the formal linear combinations of the isomorphism
classes of f.g. $R G$-modules, with addition defined by taking direct sums, and
multiplication by inner tensor products. The ring $a(R G)$ is sometimes called
the _Green ring_, after J. A. Green~@bib:Green1962b, who studied it in case $R$
is a field of characteristic $p$. The _representation algebra_
$A(k G) = CC times.o_ZZ a(k G)$, for a field $k$, has been examined thoroughly,
and §~@sec:representation-rings contains a survey of some of the high points,
including some new insights by Benson, Carlson, and Parker (see
Benson~@bib:Benson1984a for references and further results).

Let $k$ be part of a $p$-modular system $(K, R, k)$, with $K$ a subfield of
$CC$. In this situation, the $CC$-algebra homomorphisms from $A(k G)$ to $CC$,
called _species_, give a new interpretation of Brauer characters. The idea is
that for each $p'$-element $x in G$, we obtain a species $b_x$, defined by
setting $b_x lr((V)) = phi_V lr((x))$, for each $k G$-module $V$, where $phi_V$
is the Brauer character of $V$. When the group algebra $k G$ is of finite
representation type, the representation algebra $A(k G)$ is semisimple, and the
species separate elements of $A(k G)$. A startling development is that, when the
Sylow $p$-subgroups of $G$ are not cyclic, the algebra $A(k G)$ may have nonzero
nilpotent elements, so the species do not separate elements in general (see
§§~@ss:representation-algebra-semisimplicity,
@ss:representation-algebra-nilpotent-elements). Section
@sec:representation-rings also contains an induction theorem of Conlon, and a
construction of a set of dual elements in $A(k G)$ with respect to certain
bilinear forms, by a nice application of Auslander–Reiten sequences (from
§~@sec:auslander-reiten-sequences).

Representation rings have been applied in topology to the study of the
#source(854)
classifying space $B_G$ of a finite group $G$. The first step in this direction
was taken by Atiyah~@bib:Atiyah1961, who constructed an isomorphism from the
algebra $K^ast lr((B_G))$ (defined by complex vector bundles over $B_G$) to the
completion of the character ring $op("ch") G$ with respect to the topology
defined by the powers of its augmentation ideal. Another result, linking the
stable homotopy of $B_G$ with a suitable completion of the Burnside ring, has
been obtained by G. Carlsson~@bib:Carlsson1984 (see also
Adams–Gunawardena–Miller~@bib:Adams1985).
