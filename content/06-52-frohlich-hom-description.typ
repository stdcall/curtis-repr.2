#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/52-hom-description.typ": *

== The Hom Description of the Class Group <sec:frohlich-hom-description>

The idele-theoretic formulas for the locally free class group $op("Cl") R G$ and
the kernel group $D(R G)$, obtained in §@sec:locally-free-class-groups, are
sometimes inconvenient for certain types of calculations arising from algebraic
number theory. In these calculations, certain arithmetic invariants appear,
associated with complex irreducible characters of $G$. Furthermore, the
functorial properties of $op("Cl") R G$ and $D(R G)$, concerning their behavior
under change of group or change of ground ring, can be described more readily in
terms of the “Hom” version of $op("Cl") R G$ and $D(R G)$, which involves the
ring $op("ch") G$ of virtual complex characters of $G$. This version was first
introduced by Fröhlich @bib:Frohlich1976, and then elaborated in a number of
later articles. For a more detailed discussion of this topic, and especially for
its applications to algebraic number theory, we refer the reader to the
fundamental works of Fröhlich @bib:Frohlich1983, @bib:Frohlich1984. In this
section, we present the rudiments of the theory, which will suffice for our
later applications.

Throughout this section, $G$ denotes a finite group, and $R$ a Dedekind domain
whose quotient field $K$ is an algebraic number field. As usual, $op("Irr") G$
denotes the set of irreducible complex characters of $G$, and $op("ch") G$ the
ring of virtual characters of $G$, that is, the set of $ZZ$-linear combinations
of the characters $zeta in op("Irr") G$. We begin with a brief review of some
standard facts.

*Conjugate Characters.* Let $E$ be a splitting field for $G$ over $K$, chosen so
that $E$ is a finite Galois extension of $K$, with Galois group
$Omega = op("Gal")(E slash K)$. Let $S$ be the integral closure of $R$ in $E$.
Since $E$ is a splitting field for $G$, the group algebra $E G$ is a direct sum
of full matrix algebras over $E$, and every $zeta in op("Irr") G$ is afforded by
an $E$-representation $x in G arrow.r T(x) in GL_n lr((E))$. Let $omega in
Omega$; applying $omega$ to the entries of $T(x)$, we obtain a _conjugate
representation_ $T^omega$ of $G$, affording a _conjugate character_ $zeta^omega$
of $G$. (See §@i:ss:splitting-fields.) Clearly,
$
  zeta^omega lr((x)) = (zeta(x))^omega,
  quad x in G, quad omega in Omega.
$ <eq:galois-conjugate-character-values>
The Galois group $Omega$ acts on the set $op("Irr") G$, and then $op("ch") G$
can be viewed as a right $Omega$-module.

Keeping the above notation, let $y in K G$ and let $zeta in op("Irr") G$. We
define
$ scripts(det)_zeta y = det T(y), quad y in K G, $
where $T$ is a representation affording $zeta$. (The notation here is slightly
different from that used in §@i:ss:transfer-determinant-map.) Note that
$scripts(det)_zeta$ depends only on the character $zeta$,
#source(346)
and not on the choice of the representation $T$ affording $zeta$. Then
$ T(y z) = T(y) T(z) quad "for" y,z in K G, $
and consequently
$
  scripts(det)_zeta lr((y z)) = scripts(det)_zeta lr((y)) dot
  scripts(det)_zeta lr((z))
  quad "for" y,z in K G.
$ <eq:character-determinant-multiplicativity>
Furthermore, from @eq:galois-conjugate-character-values we obtain
$
  scripts(det)_(zeta^omega) y = (scripts(det)_zeta y)^omega
  quad "for" y in K G, quad omega in Omega, quad zeta in op("Irr") G.
$ <eq:character-determinant-galois-equivariance>
It is clear that
$ scripts(det)_zeta y in E^dot quad "for" y in (K G)^dot. $
Furthermore, for each maximal ideal $P$ of $S$, the representation $T$ may be
chosen so that the matrices ${T(x): x in G}$ have entries in $S_P$ (see
@i:cor:modular-representation-integral-form). It follows that for
$y in (R G)^dot$ we have $scripts(det)_zeta y in (S_P)^dot$ for each $P$, and
therefore
$ scripts(det)_zeta y in S^dot quad "for" y in (R G)^dot. $
<eq:integral-character-determinants>
Finally, for $zeta, eta in op("Irr") G$ we have
$
  scripts(det)_(zeta+eta) lr((y)) = scripts(det)_zeta lr((y)) dot
  scripts(det)_eta lr((y))
  quad "for" y in (K G)^dot.
$ <eq:character-determinant-additivity>
It follows that $scripts(det)_zeta lr((y)) in E^dot$ is well-defined for all
virtual characters $zeta in op("ch") G$, and all $y in (K G)^dot$.

*Schur Index.* The following results will be established in §@sec:schur-index,
and some of them have already been proved in §@i:ss:splitting-fields. First,
there is a bijection between the set of orbits of $op("Irr") G$ under the action
of $Omega$, and the set of simple components of the group algebra $K G$. Given
$zeta in op("Irr") G$, let ${zeta_1, dots, zeta_t}$ be its distinct conjugates
under the action of $Omega$, where $zeta_1 = zeta$. Let $B_zeta$ be the simple
component of $K G$ corresponding to the orbit ${zeta_1, dots, zeta_t}$. Then the
center of $B_zeta$ is isomorphic to the field $K(zeta)$ obtained by adjoining to
$K$ all of the character values ${zeta(x): x in G}$. Furthermore, $K(zeta)$ is a
Galois extension of $K$, and $dim_K K(zeta)$ coincides with the number $t$ of
distinct conjugates of $zeta$. The Galois group $op("Gal")(K(zeta) slash K)$
permutes the characters ${zeta_1, dots, zeta_t}$ transitively, and we have
$
  K(zeta) = "subfield of" E "fixed by"
  {omega in Omega: zeta^omega = zeta}.
$

*The Det Homomorphism.* As above, let $E$ be a splitting field for $G$ over $K$,
and let $Omega = op("Gal")(E slash K)$. We have already seen that
$
  scripts(det)_zeta y in E^dot
  quad "for" zeta in op("ch") G "and" y in (K G)^dot.
$
#source(347)
The Det homomorphism assigns to each $y in (K G)^dot$ the function
$ zeta arrow.r scripts(det)_zeta y, quad zeta in op("ch") G. $
Denoting this function by $op("Det") y$, we thus have (by definition)
$
  (op("Det") y)(zeta) = scripts(det)_zeta y
  quad "for" y in (K G)^dot, quad zeta in op("ch") G.
$ <eq:det-homomorphism-character-value>
#idx("Det homomorphism", target: [@eq:det-homomorphism-character-value])
#nidx(
  "$det, op(\"Det\")$",
  "determinant maps",
  target: [@eq:det-homomorphism-character-value],
)
Let us view $E^dot$ and $op("ch") G$ as right $Omega$-modules, and consider the
set $Hom_Omega lr((op("ch") G, E^dot))$. We make this into an abelian
multiplicative group by defining
$
  (f g) zeta = f(zeta) g(zeta)
  quad "for" f,g in Hom_Omega, quad "and" zeta in op("ch") G.
$
It follows at once from @eq:character-determinant-galois-equivariance and
@eq:character-determinant-additivity that
$op("Det") y in Hom_Omega lr((op("ch") G,E^dot))$ for each $y in (K G)^dot$.
Furthermore, the map $y arrow.r op("Det") y$, $y in (K G)^dot$, is a
homomorphism, since for $zeta in op("ch") G$, $y,z in (K G)^dot$,
$
  (op("Det") y z)(zeta) = scripts(det)_zeta lr((y z))
  = scripts(det)_zeta lr((y)) dot scripts(det)_zeta lr((z))
  = (op("Det") y)(zeta) dot (op("Det") z)(zeta).
$
Thus we obtain a homomorphism
$ op("Det"): (K G)^dot -> Hom_Omega lr((op("ch") G,E^dot)), $
<eq:det-homomorphism>
carrying $y in (K G)^dot$ onto $op("Det") y in Hom_Omega$.

In the above discussion, we may replace $K$ by some larger field on which
$Omega$ is assumed to act trivially. For example, let $P$ be a prime of $K$, and
let $K_P$ be the $P$-adic completion of $K$. Set
$ E_P = K_P times.o_K E tilde.equiv product.co_frak(P) E_frak(P), $
where $frak(P)$ ranges over the primes of $E$ above $P$, and $E_frak(P)$ denotes
the $frak(P)$-adic completion of $E$. Let $omega in Omega$ act as
$1 times.o omega$ on $E_P$. Let $zeta in op("Irr") G$ be a character afforded by
the $E$-representation $T$ of $G$ of degree $n$. Extending $T$ linearly to a
representation of $K_P G$, we obtain a ring homomorphism
$ K_P G -> M_n lr((K_P times.o_K E)) = M_n lr((E_P)). $
This yields a homomorphism of groups:
$ T: (K_P G)^dot -> GL_n lr((E_P)) arrow.r^det E_P^dot. $
Just as above, we then obtain a homomorphism
$ op("Det"): (K_P G)^dot -> Hom_Omega lr((op("ch") G,E_P^dot)). $

#source(348)
As in @eq:integral-character-determinants, we note that
$ op("Det"): (R_P G)^dot -> Hom_Omega lr((op("ch") G,S_P^dot)) $
<eq:local-integral-det-homomorphism>
for each maximal ideal $P$ of $R$.

We show next that Det is closely related to the reduced norm map. It is this
relation, in fact, which allows us to recast our previous formulas for
$op("Cl") R G$ and $D(R G)$ in terms of these Hom groups.

#proposition[
  Let $A = K G$, and let $op("nr")$ be the reduced norm map
  $op("nr")_(A slash C)$ from $A$ to its center $C$. Then there is an
  isomorphism
  $ f: C^dot tilde.equiv Hom_Omega lr((op("ch") G,E^dot)) $
  such that the diagram
  #numbered-block[#det-reduced-norm-triangle]
  <eq:det-reduced-norm-triangle>
  is commutative.
] <prop:det-reduced-norm-hom-identification>
#proof[
  In order to get an intuitive feeling for the result, we consider first the
  special case where $E = K$, so now
  $op("Irr") G = op("Irr") K G = {zeta_1, dots, zeta_r}$, say. Then $C^dot$ is a
  direct product of $r$ copies of $K^dot$. On the other hand, the ${zeta_i}$
  form a free $ZZ$-basis of $op("ch") G$, and thus
  $
    Hom(op("ch") G, K^dot) tilde.equiv
    product_(i=1)^r Hom(ZZ, K^dot) tilde.equiv product_(i=1)^r K^dot.
  $
  The desired isomorphism $f$ can then be given as follows: let
  $C = product.co_i C_i$, and let $c = product.co_i c_i$, $c_i in C_i^dot$. Then
  define $f_c$ by
  $ f_c lr((sum a_i zeta_i)) = product c_i^(a_i), quad a_i in ZZ. $
  To verify that $f compose op("nr") = op("Det")$, it suffices to work with
  simple components. Let $A_i$ be a simple component of $A$ with center $C_i$,
  and character $zeta_i$ afforded by a representation $T_i$. By definition of
  the reduced norm, we have
  $
    op("nr") y = det T_i lr((y)) = scripts(det)_(zeta_i) y
    = (op("Det") y)(zeta_i) quad "for" y in A_i^dot.
  $
  If $c_i = op("nr") y$, then $f_c lr((zeta_i)) = c_i$; therefore
  $(f compose op("nr")) y = op("Det") y$, as desired.

  Turning to the general case, let $Omega = op("Gal")(E slash K)$, where $E$ is
  a splitting field for $G$. Let ${zeta_1, dots, zeta_k}$ be a full set of
  representatives of the orbits of $op("Irr") G$ under the
  #source(349)
  action of $Omega$, and identify each field $K(zeta_i)$ with a subfield of $E$.
  We may then write
  $ C = product.co_(i=1)^k C_i, quad "where" C_i = K(zeta_i). $
  If $zeta in op("Irr") G$ is conjugate to $zeta_i$, say $zeta = zeta_i^omega$
  for some $omega in Omega$, then $omega$ induces an automorphism
  $K(zeta_i) tilde.equiv K(zeta)$. We now define a map
  $f: C^dot -> Hom_Omega lr((op("ch") G,E^dot))$ as follows: given
  $c = product.co c_i$, where $c_i in K(zeta_i)^dot$, let $f_c$ be the function
  $
    f_c = product_i f_(c_i), quad "where" cases(
      f_(c_i) lr((zeta_i^omega)) = c_i^omega & quad omega in Omega,
      f_(c_i) lr((zeta)) = 1 & quad "if" zeta != "Ω-conjugate of" zeta_i.
    )
  $
  This defines $f_c lr((zeta))$ for $zeta in op("Irr") G$, and we extend $f_c$
  to a map on $op("ch") G$ by setting
  $
    f_c lr((sum_zeta a_zeta zeta)) = product_zeta f_c lr((zeta))^(a_zeta),
    quad a_zeta in ZZ.
  $
  It is trivial to verify that the map $f: c arrow.r f_c$ is multiplicative, and
  that each $f_c$ is an $Omega$-homomorphism.

  Let us verify that $f$ is an isomorphism. Suppose first that $f_c = 1$, so
  $f_c lr((zeta)) = 1$ for each $zeta in op("Irr") G$; taking $zeta = zeta_i$ we
  obtain $c_i = 1$ for each $i$, so $c = 1$. Secondly, given any
  $g in Hom_Omega lr((op("ch") G,E^dot))$, let $u_i = g(zeta_i) in E^dot$,
  $1 <= i <= k$. If $omega in Omega$ fixes $zeta_i$ then it also fixes $u_i$,
  and therefore $u_i in K(zeta_i)^dot$. Choosing $c = product.co_i u_i$, we
  obtain $f_c = g$, so $f$ is surjective. This proves that $f$ is an
  isomorphism, as desired.

  To prove that diagram @eq:det-reduced-norm-triangle is commutative, it again
  suffices to work with a simple component $A_i$ of $A$ with center $C_i$. Let
  $A_i$ correspond to the $Omega$-orbit of $zeta_i$ in $op("Irr") G$, and let
  $a in A_i^dot$. Define
  $c = op("nr")_(A slash C) a = op("nr")_(A_i slash C_i) a in C_i^dot$. By
  definition of the isomorphism $f$, we have
  $ f_c lr((zeta_i^omega)) = c^omega quad "for" omega in Omega. $
  On the other hand, let $T_i$ be the $E$-representation of $G$ affording
  $zeta_i$. Then
  $
    op("nr")_(A_i slash C_i) a = det T_i lr((a)) = scripts(det)_(zeta_i) lr((a))
  $
  by definition of the reduced norm map. For $omega in Omega$, we obtain
  $
    (op("Det") a)(zeta_i^omega) = scripts(det)_(zeta_i^omega) lr((a))
    = (scripts(det)_(zeta_i) a)^omega = c^omega = f_c lr((zeta_i^omega)),
  $
  that is, Det and $f compose op("nr")$ agree on $a in A_i$. This completes the
  proof of the proposition.
]

The reader will easily verify that the above discussion is independent of the
choice of $E$, as long as $E slash K$ is Galois and $E$ is a splitting field for
$G$. To avoid a choice for $E$, we may instead use the algebraic closure $K^c$
of $K$ as a splitting field for $G$. Of course, $op("Gal")(K^c slash K)$ is
infinite, and it is conceptually somewhat simpler to work with finite Galois
extensions.

#source(350)
Now let $R = "alg. int." lr({K})$, and set
$
  Lambda = R G subset Lambda' subset K G = A,
  quad Lambda' = "maximal" R "-order in" A.
$
As in §@i:ss:ideles-locally-free-class-groups and
§@ss:class-group-basic-formulas, we introduce the idele group
$
  J^* lr((A)) = {(alpha_P) in product_P A_P^dot:
    alpha_P in Lambda_P^dot "a.e."},
$
where $P$ ranges over all primes of $K$, finite and infinite both. (For infinite
$P$, define $R_P = K_P$, $Lambda_P = A_P$, etc.) Analogously, there are idele
groups $J^* lr((C))$ and $J^* lr((E))$, where $C$ is the center of $A$, and $E$
is as above. Define
$
  U^* lr((Lambda)) = product_P Lambda_P^dot
  = "group of unit ideles in" J^* lr((A)),
$
$ tilde(J) lr((A)) = {alpha in J^* lr((A)): op("nr")_(A slash C) alpha = 1}. $
As shown in @th:class-group-all-prime-reduced-norm-ideles and
@eq:class-group-all-prime-idele-quotient, we may express $op("Cl") Lambda$ in
terms of these idele groups, by the formulas
$
  op("Cl") Lambda tilde.equiv
  (J^* lr((A))) / (tilde(J) lr((A)) A^dot U^* lr((Lambda)))
  tilde.equiv (J^* lr((C))) / (C^dot op("nr") U^* lr((Lambda))),
$
where $A^dot$ and $C^dot$ are groups of principal ideles. The second of these
isomorphisms arises by applying $op("nr")_(A slash C)$ to the first formula.

From these isomorphisms and the preceding discussion, we deduce Fröhlich's
@bib:Frohlich1976 formula:

#theorem(name: "Hom Formula for Class Groups")[
  There is an isomorphism
  $
    op("Cl") R G tilde.equiv
    (Hom_Omega lr((op("ch") G,J^* lr((E))))) /
    (Hom_Omega lr((op("ch") G,E^dot)) dot op("Det") U^* lr((R G))).
  $
] <th:frohlich-hom-class-group-formula>
#idx("Class group Cl(Λ)", target: [@th:frohlich-hom-class-group-formula])
#idx("Locally free class group", target: [@th:frohlich-hom-class-group-formula])
#proof[
  The isomorphism $C^dot tilde.equiv Hom_Omega lr((op("ch") G,E^dot))$ extends
  readily to an isomorphism
  $ J^* lr((C)) tilde.equiv Hom_Omega lr((op("ch") G,J^* lr((E)))). $
  In this isomorphism, $op("nr") U^* lr((Lambda))$ maps onto
  $op("Det") U^* lr((Lambda))$ because of the commutative diagram
  @eq:det-reduced-norm-triangle. We note also that
  $
    op("Det") U^* lr((Lambda)) subset.eq
    Hom_Omega lr((op("ch") G,U^* lr((S))))
  $
  by @eq:local-integral-det-homomorphism, where (as above) $S$ is the integral
  closure of $R$ in $E$.
]

If we want to avoid the use of infinite primes of $K$, then in the formula for
$op("Cl") Lambda$ we must replace $C^dot$ by $C^+$, and must then describe the
image of $C^+$ in
#source(351)
$Hom_Omega lr((op("ch") G,E^dot))$. We shall return to this question later. For
the moment, however, we make explicit the connection between locally free ideals
of $Lambda$ and functions from $op("ch") G$ to $J^* lr((E))$.

#corollary[
  Let $M = Lambda alpha$ be a locally free left $Lambda$-ideal, where
  $alpha = (alpha_P) in J^* lr((A))$. In the isomorphism
  @th:frohlich-hom-class-group-formula, the class of $M$ in $op("Cl") Lambda$
  corresponds to the class of the representative function
  $f in Hom_Omega lr((op("ch") G,J^* lr((E))))$, defined by the formula
  $ f(zeta) = (f_P lr((zeta))) in J^* lr((E)), quad "for" zeta in op("Irr") G, $
  where
  $
    f_P lr((zeta)) = scripts(det)_zeta alpha_P in E_P^dot
    quad "for each prime" P "of" K.
  $
] <cor:locally-free-ideal-det-representative>
#proof[
  This is immediate from @eq:det-reduced-norm-triangle.
]

Before discussing the functorial properties of
@th:frohlich-hom-class-group-formula, we give some examples of representative
functions of locally free ideals.

#example(title: [Swan Modules])[
  Let $G$ be a group of order $n$, and define $sigma = sum_(x in G) x in ZZ G$.
  For each $r in ZZ$ relatively prime to $n$, define the _Swan module_
  $ chevron.l r,sigma chevron.r = r ZZ G + sigma ZZ G, $
  a locally free left ideal of $ZZ G$ (see §@sec:swan-subgroup-class-group). Let
  $e = sigma slash n$, a central idempotent of $QQ G$, and define
  $u = 1 - e + r e in QQ G$. As shown in §@sec:swan-subgroup-class-group, we
  have
  $
    chevron.l r,sigma chevron.r tilde.equiv ZZ G beta,
    quad "where" beta = (beta_p), quad "with"
    beta_p = cases(1 & quad p divides.not n, u & quad p divides n,),
  $
  and where we now take $beta_infinity = 1$.

  If $p divides.not n$ or $p = infinity$, we have $beta_p = 1$, and thus
  $f_p lr((zeta)) = 1$ for all $zeta in op("Irr") G$, where $f$ represents
  $chevron.l r,sigma chevron.r$. If $p divides n$, then
  $f_p lr((zeta)) = scripts(det)_zeta u$ for each $zeta$. But $u arrow.r r$ in
  the trivial representation of $G$, while $u arrow.r 1$ in all nontrivial
  irreducible representations of $G$. Therefore if $p divides n$ we have
  $
    f_p lr((zeta)) = cases(
      r & quad zeta = 1, 1 & quad zeta in op("Irr") G\,
      zeta != 1.
    ).
  $
] <exm:swan-module-det-representative>
#idx("Swan module", target: [@exm:swan-module-det-representative])

#example(title: [Integers in Tamely Ramified Extensions])[
  Let $K$ be a finite Galois extension of $QQ$ with Galois group $G$, and let
  $R = "alg. int." lr({K})$. We may view $K$ as a left $QQ G$-module by defining
  $
    lr((sum_(sigma in G) a_sigma sigma)) x = sum a_sigma sigma(x)
    quad "for" x in K, quad a_sigma in QQ.
  $
  #source(352)
  The Normal Basis Theorem (@bib:Reiner1975[MO], Exercise 29.14) asserts that
  $K$ has a normal basis over $QQ$, that is, there exists an $x in K$ such that
  ${sigma(x): sigma in G}$ is a $QQ$-basis of $K$. This is equivalent to the
  assertion that $K$ is free (of rank 1) as $QQ G$-module.

  The corresponding problem for rings of integers is considerably harder (and
  thus more interesting). Clearly $R$ is a $ZZ G$-module, and we say that $R$
  has a _normal integral basis_#idx("Normal integral basis") if
  $R tilde.equiv ZZ G$ or equivalently, $R = plus.o_(sigma in G) ZZ sigma(x)$
  for some $x in R$. By Exercise @i:exc:trace-surjective-galois-projective, if
  $R$ is tamely ramified over $ZZ$, then $R$ is projective as $ZZ G$-module. (In
  this case, $R$ is locally free as left $ZZ G$-module, by Swan's Theorem
  @i:th:swan-projective-group-lattices-locally-free.) Conversely, if $R$ is
  $ZZ G$-projective, then $R$ is tamely ramified over $ZZ$. Thus, in trying to
  decide whether $R$ has a normal integral basis, we need only consider the
  tamely ramified case (see Exercises @i:exc:tame-extension-trace-surjective,
  @i:exc:trace-surjective-galois-projective, and Volume I, page 595, for
  discussion of tame ramification). It is customary to say that “$K$ is tamely
  ramified over $QQ$,” rather than refer to the rings of integers involved.

  Supposing now that $K slash QQ$ is tamely ramified, the $ZZ G$-module $R$ is
  locally free, and thus determines a class $[R]$ in the locally free class
  group $op("Cl") ZZ G$. Denote this class by $U_K$ hereafter. Fröhlich
  @bib:Frohlich1976 used the formula for $op("Cl") ZZ G$ to prove the deep
  result that $U_K in D(ZZ G)$. Taylor @bib:Taylor1980 proved that $U_K$ has
  order 1 or 2, and the latter possibility cannot occur unless the Galois group
  $G$ has an irreducible symplectic#footnote[Defined below.]
  <fn:symplectic-character-defined-below> character; if no such character
  exists, then necessarily $U_K = 0$ and $R$ is $ZZ G$-free. We remark also that
  Taylor and Chase have shown that $tau U_K = U_K$ in $D(ZZ G)$, where $tau$ is
  the automorphism of $D(ZZ G)$ induced by the map $x arrow.r x^(-1)$, $x in G$
  (see §@ss:class-kernel-group-involution). For a systematic treatment of these
  matters, see Fröhlich @bib:Frohlich1983.

  We now state Fröhlich's formula for the function
  $f in Hom_Omega lr((op("ch") G,J^* lr((E))))$ which represents the class
  $U_K in op("Cl") ZZ G$. The formula involves the use of resolvents, which we
  define as follows. For each $a in K$, form the sum
  $ sum_(sigma in G) sigma(a) sigma^(-1) in K G. $
  Let $zeta$ be an irreducible complex character of $G$, afforded by a
  representation $T$ in some splitting field $E$ containing $K$. We define the
  _resolvent_#idx("Resolvent")
  $
    (a bar zeta) = det T lr((sum_(sigma in G) sigma(a) sigma^(-1)))
    = scripts(det)_zeta lr((sum_sigma sigma(a) sigma^(-1))).
  $
  If $K = QQ G dot a$, then $(a bar zeta) in E^dot$ for each
  $zeta in op("Irr") G$. In the same manner, for each rational prime $p$ (or for
  $p = infinity$), we may define a resolvent $(b bar zeta)$ for $b in K_p$,
  where $K_p = QQ_p times.o_QQ K$ and $G = op("Gal")(K slash QQ)$ acts trivially
  on $QQ_p$.

  Still assuming that $K slash QQ$ is tamely ramified, choose $a in K$ such that
  $K = QQ G a$. Further, for each $p$ choose $b_p in R_p$ such that
  $R_p = ZZ_p G b_p$. Then the class of $[R]$ in $op("Cl") ZZ G$ is represented
  by the function $f in Hom_Omega lr((op("ch") G,J^* lr((E))))$ defined by
  $
    f = (f_p), quad "where"
    f_p lr((zeta)) = (b_p bar zeta) dot (a bar zeta)^(-1),
    quad zeta in op("Irr") G.
  $
] <exm:integers-tamely-ramified-extensions>
#idx("Ramification", "tame", target: [@exm:integers-tamely-ramified-extensions])
#idx(
  "Tamely ramified extension",
  target: [@exm:integers-tamely-ramified-extensions],
)

#source(353)
It is this formula which lies at the heart of the above-mentioned theorems
concerning $U_K$. See Fröhlich @bib:Frohlich1983 for details.

The idele groups occurring in @th:frohlich-hom-class-group-formula involve both
finite and infinite primes. One of the main reasons for using infinite primes
stems from the fact that in problems concerning the existence of normal integral
bases, the irreducible symplectic characters of $G$ play a key role (see
@exm:integers-tamely-ramified-extensions). We may define such characters as
follows, anticipating the discussion in
§@sec:unitary-orthogonal-symplectic-modules. Let $B$ be a simple component of
the group algebra $RR G$, affording the real character $eta$. There are three
possibilities:

#enum(
  numbering: "(i)",
  [$B tilde.equiv M_n lr((RR))$. Then $CC times.o_RR B tilde.equiv M_n
    lr((CC))$, and $eta$ is an absolutely irreducible character of $G$
    realizable in $RR$.],
  [$B tilde.equiv M_n lr((CC))$. Then
    $CC times.o_RR B tilde.equiv M_n lr((CC)) plus.o M_n lr((CC))$, and
    $eta = zeta + overline(zeta)$ for some $zeta in op("Irr") G$ which is
    distinct from its complex conjugate $overline(zeta)$, that is, $zeta$ is not
    real-valued.],
  [$B tilde.equiv M_n lr((HH))$, where $HH$ is the skewfield of real
    quaternions, of index 2. Then $CC times.o_RR B tilde.equiv M_(2n)(CC)$, and
    $eta = 2 zeta$ for some real-valued $zeta in op("Irr") G$. The character
    $zeta$ cannot be realized in $RR$, but $2 zeta$ can be realized in $RR$. We
    call $zeta$ an _irreducible symplectic character_ of $G$.],
)
#idx("Symplectic character")

We shall use the above in singling out a subgroup $Hom_Omega^+$ of $Hom_Omega$.
As before, let $Omega = op("Gal")(E slash K)$ where $E$ is a splitting field for
$G$. Let us define
$
  cases(
    Hom_Omega^+ lr((op("ch") G,J^* lr((E)))),
    = brace.l f = (f_P) in Hom_Omega lr((op("ch") G,J^* lr((E)))):
    f_P lr((zeta)) > 0 "for every irreducible",
    "symplectic character" zeta "of" G "and every infinite prime" P "of",
    E "extending a real prime of" K brace.r .
  )
$ <eq:positive-equivariant-hom-group>
#idx("Hom⁺", target: [@eq:positive-equivariant-hom-group])
We claim that
$
  op("Det") U^* lr((Lambda')) = Hom_Omega^+ lr((op("ch") G,U^* lr((S)))),
$
where $Lambda'$ is a maximal order in $K G$ containing $R G$, and where
$S = "alg. int." lr({E})$. It suffices to check the formula
$ op("Det") A_(P_0)^dot = Hom_Omega^+ lr((op("ch") G,E_(P_0)^dot)) $
for every infinite prime $P_0$ of $K$. This is clear from
@eq:det-reduced-norm-triangle when $P_0$ is complex. On the other hand, for
$P_0$ real it suffices to verify the formula for every simple component $B$ of
$A_(P_0)$, and again the result follows from the diagram
#real-component-det-triangle
We leave the details to the reader.

#source(354)
We may now obtain Fröhlich's Hom description of the kernel group $D(Lambda)$,
where $Lambda = R G$.

#theorem[
  In terms of the above notation, we have
  $
    D(Lambda) tilde.equiv
    (Hom_Omega^+ lr((op("ch") G,U^* lr((S))))) /
    (Hom_Omega^+ lr((op("ch") G,S^dot)) dot op("Det") U^* lr((Lambda))).
  $
] <th:frohlich-hom-kernel-group-formula>
#idx("D(Λ)", target: [@th:frohlich-hom-kernel-group-formula])
#proof[
  Let Hom denote $Hom_Omega$, and use @th:frohlich-hom-class-group-formula for
  both $op("Cl") Lambda$ and $op("Cl") Lambda'$. Since
  $op("Det") U^* lr((Lambda')) = Hom^+ lr((op("ch") G,U^* lr((S))))$, we obtain
  $
    D(Lambda) & tilde.equiv
    (Hom(op("ch") G, E^dot) dot Hom^+ lr((op("ch") G,U^* lr((S))))) /
    (Hom(op("ch") G, E^dot) dot op("Det") U^* lr((Lambda))) \
    & tilde.equiv
    (Hom^+ lr((op("ch") G,U^* lr((S))))) /
    (op("Det") U^* lr((Lambda))
    lr({Hom(op("ch") G, E^dot) inter Hom^+ lr((op("ch") G,U^* lr((S))))})).
  $
  Since the intersection in the denominator above is
  $Hom^+ lr((op("ch") G,S^dot))$, the theorem is established.
]

Let us now reformulate the above results on $op("Cl") R G$ and $D(R G)$ in terms
of the idele groups $J(E)$, $U(S)$, etc., which involve only the finite primes
(that is, the maximal ideals of $R$); see @th:class-group-reduced-norm-ideles
and @th:kernel-group-unit-idele-formula. As in the discussion and proof of
@th:class-group-all-prime-reduced-norm-ideles, we obtain the formulas
$
  op("Cl") Lambda tilde.equiv
  (Hom_Omega lr((op("ch") G,J(E)))) /
  (Hom_Omega^+ lr((op("ch") G,E^dot)) dot op("Det") U(Lambda)),
$ <eq:finite-prime-hom-class-group-formula>
$
  D(Lambda) tilde.equiv (Hom_Omega lr((op("ch") G,U(S)))) /
  (op("Det") U(Lambda) dot Hom_Omega^+ lr((op("ch") G,S^dot))).
$ <eq:finite-prime-hom-kernel-group-formula>
Further, the Hom version of @th:kernel-group-finite-prime-formula holds true.
Let $S(Lambda) = {P = "maximal ideal of" R:
  Lambda_P != "maximal" R_P "-order"}$. Then
$
  D(Lambda) tilde.equiv
  (Hom_Omega lr((op("ch") G,product_(P in S(Lambda)) S_P^dot))) /
  (lr({product_(P in S(Lambda)) op("Det") Lambda_P^dot}) dot
  Hom_Omega^+ lr((op("ch") G,S^dot))).
$ <eq:nonmaximal-prime-hom-kernel-group-formula>
In particular, if $G$ is a $p$-group ($p = "prime"$), then
$
  D(Lambda) tilde.equiv
  (Hom_Omega lr((op("ch") G,S_p^dot))) /
  (op("Det")(R_p G)^dot dot Hom_Omega^+ lr((op("ch") G,S^dot))).
$ <eq:p-group-hom-kernel-group-formula>
We now discuss some functorial properties of the Hom formulas for class groups.

#source(355)
#remarks(name: "Change of Group (Induction)")[
  An inclusion of groups $H <= G$ extends to an inclusion $R H subset.eq R G$,
  yielding a “change of rings” map
  $R G times.o_(R H) ast: op("Cl") R H -> op("Cl") R G$. This carries a locally
  free $R H$-module $R H alpha$ (where $alpha in J^* lr((K H))$ is an idele)
  onto the locally free $R G$-module $R G alpha$.

  On the other hand, restriction of operators from $G$ to $H$ gives a map
  $op("ch") G -> op("ch") H$, which induces a map
  $Hom(op("ch") H, dot) -> Hom(op("ch") G, dot)$. Then we obtain a commutative
  diagram
  #hom-group-induction-square
  where the horizontal arrows are the isomorphisms given in
  @th:frohlich-hom-class-group-formula.

  (We remark that a corresponding result holds whenever there is a homomorphism
  $H -> G$ of groups. Indeed, it holds more generally for homomorphisms
  $Lambda -> Lambda'$ of $R$-orders.)

  To prove commutativity, it suffices to verify (after passing to $P$-adic
  completions and changing notation) that the following diagram commutes:
  #det-group-induction-square
  This is a trivial computation, left to the reader.
] <rem:hom-change-of-group-induction>
#idx(
  "Class group",
  "functorial properties",
  target: [@rem:hom-change-of-group-induction],
)

#remarks(name: "Change of Groups (Restriction)")[
  For $H <= G$, each $R G$-module $M$ may be viewed as $R H$-module $M_H$, by
  restriction of operators. Since $R G |_H$ is $R H$-free of rank
  $abs(G ratio H)$, we obtain a homomorphism
  $op("res")_H^G: K_0(R G) -> K_0(R H)$. This commutes with $P$-adic completion,
  and hence induces a map $op("res")_H^G: op("Cl") R G -> op("Cl") R H$ (see
  §@ss:class-group-functorial-kernel).

  Next we observe that the induction homomorphism
  $op("ind")_H^G: op("ch") H -> op("ch") G$ gives rise to a map
  $Hom(op("ch") G, dot) -> Hom(op("ch") H, dot)$. We claim that the diagram
  #hom-group-restriction-square
  commutes, where the horizontal arrows are the isomorphisms
  @th:frohlich-hom-class-group-formula. (Note that this property is peculiar to
  group rings, and need not hold for arbitrary orders.)

  #source(356)
  By @prop:class-group-k1-idele-description, in order to prove the above claim,
  it suffices to verify (after completing and changing notation) that the
  following diagram commutes:
  #det-group-restriction-square
  For this, we need only prove that
  $
    scripts(det)_(mu^G) lr((x)) = scripts(det)_mu lr((op("res") x))
    quad "for" x in (K G)^dot quad "and" mu in op("Irr") H.
  $ <eq:induced-character-determinant-restriction>
  Let $G = union.big_(i=1)^n g_i H$, where $n = abs(G ratio H)$. Then
  $x in (K G)^dot$ corresponds to the element $[K G,x_1]$, where $x_1$ is left
  multiplication on the right $K G$-module $K G$. Let
  $x g_i = sum_j g_j h_(i j)$, $h_(i j) in K H$. Then $op("res") x in GL_n
  lr((K H))$ is the matrix given by
  $ op("res") x = [g_j^(-1) x g_i]_(1 <= i,j <= n), $
  with the understanding that when $g_j^(-1) x g_i$ is expressed as a linear
  combination of group elements, we omit all terms outside of $H$. Now let $M$
  be an $E$-representation of $H$ affording $mu$. Then $mu^G$ is afforded by
  $M^G$, where
  $ M^G lr((x)) = [M(g_j^(-1) x g_i)]_(1 <= i,j <= n), $
  and $M$ vanishes outside $H$. Therefore for $x in (K G)^dot$,
  $
    scripts(det)_(mu^G) lr((x)) = det M^G lr((x))
    = "determinant of the matrix obtained by" \
    "applying" M "to each entry of" op("res") x \
    = scripts(det)_mu lr((op("res") x)).
  $
  This completes the proof. The reader should compare this calculation with that
  given in the proof of @i:prop:induced-character-determinant-transfer. Indeed,
  for $x in G$ (viewed as element of $(K G)^dot$), we have
  $
    scripts(det)_mu lr((op("res") x)) =
    {epsilon_(G arrow.r H)^(mu(1)) lr((x))}
    {scripts(det)_mu V_H^G lr((x))},
  $
  where the underlying transfer class lies in $plus.minus H slash H'$. Our
  formula @eq:induced-character-determinant-restriction is thus a generalization
  of formula @i:prop:induced-character-determinant-transfer(i). (See also the
  proof of @lem:whitehead-trivial-units-frobenius-submodules.)
] <rem:hom-change-of-group-restriction>

#remarks(name: "Change of Ground Ring (Extension)")[
  Let $K'$ be a finite extension of $K$ and $R'$ the integral closure of $R$ in
  $K'$. The inclusion $R G subset R' G$ gives a homomorphism
  $ R' times.o_R ast: op("Cl") R G -> op("Cl") R' G. $
  #source(357)
  Choose the splitting field $E$ so that $E$ is a Galois extension of $K'$, and
  let $Omega' = op("Gal")(E slash K')$. It is easily verified that the following
  diagram commutes:
  #hom-ring-extension-square
  where the horizontal arrows are the isomorphisms
  @th:frohlich-hom-class-group-formula, and the map on Hom's is the canonical
  injection.
] <rem:hom-change-of-ground-ring-extension>

#remarks(name: "Change of Ground Ring (Restriction)")[
  Keep the above notation. Since $R'$ is $R$-projective, $R' G$ is projective as
  $R G$-module, so the restriction map gives a homomorphism
  $K_0(R' G) -> K_0(R G)$. This commutes with completions, and induces a map
  $op("Cl") R' G -> op("Cl") R G$, by identifying these class groups with
  subgroups of $K_0$ as in @eq:class-group-localization-kernel-isomorphism. For
  $M$ a locally free ideal of $R' G$, the element of $K_0(R' G)$ corresponding
  to $[M] in op("Cl") R' G$ is $[M] - [R' G]$; its image in $K_0(R G)$ is then
  $[M |_(R G)] - [R' G |_(R G)]$. In terms of Hom's the restriction map
  $op("Cl") R' G -> op("Cl") R G$ corresponds to a “norm” map from
  $Hom_(Omega')$ to $Hom_Omega$. There is a commutative diagram
  #hom-ring-restriction-square
  with the horizontal arrows the isomorphisms
  @th:frohlich-hom-class-group-formula. Let $f in Hom_(Omega')$ be a
  representative function of $[M] in op("Cl") R' G$, and define
  $ cal(N) f = product_(sigma in Omega slash Omega') sigma f sigma^(-1). $
  The induced restriction homomorphism sends $[M] in op("Cl") R' G$ to
  $[N] in op("Cl") R G$, where $N$ is a locally free $R G$-ideal with
  representative function $cal(N) f$. Equivalently, the stable class of the
  restricted lattice is $[M |_(R G)] = [N] + [R' G |_(R G)] in op("Cl") R G$.
  For details and proof, see Fröhlich @bib:Frohlich1976.
] <rem:hom-change-of-ground-ring-restriction>

We briefly mention _determinantal congruences_, which follow from the Hom
description of the class group. As usual, let $E slash K$ be a Galois extension
with Galois group $Omega$, and let $S = "alg. int." lr({E})$,
$R = "alg. int." lr({K})$. Let $E$ be a splitting field for $G$. Given a
rational prime $p$, let $P$ be a maximal ideal of $R$, and $P'$ of $S$, both
containing $p$. Let $overline(S) = S slash P'$, $overline(ZZ) = ZZ slash p ZZ$.

Given a $S$-representation $T$ of $G$, we may form the
$overline(S)$-representation $overline(T)$ of $G$, by reduction $(mod P')$. By
@i:prop:lattice-reduction-composition-factors, the composition factors of
$overline(T)$ depend only on the character $chi$ of $G$ afforded by $T$. The map
$T arrow.r overline(T)$ gives the Brauer decomposition map
$ d: G_0(E G) -> G_0(overline(S) G) $
#source(358)
(see @i:def:decomposition-map-matrix), and $G_0(E G) tilde.equiv op("ch") G$. By
@i:prop:decomposition-brauer-character-square,
$
  ker d = {zeta in op("ch") G: zeta(x) = 0
    "for each" p "-regular" x in G}.
$
We now prove:

#theorem(name: "Theorem on Determinantal Congruences")[
  Let $p S = product_(i=1)^m P_i^(e_i)$. Then for $a in (S_p G)^dot$ and
  $zeta in ker d$, we have
  $ scripts(det)_zeta a equiv 1 lr((mod product_(i=1)^m P_i)). $
] <th:determinantal-congruences>
#proof[
  It suffices to verify the result after passing to $P_i$-adic completions, so
  changing notation, we now assume $S$ is a complete d.v.r. with maximal ideal
  $P'$. Given $a in (S G)^dot$ and $zeta = phi - psi in ker d$, where $phi,psi$
  are ordinary characters of $G$, we must show that
  $
    scripts(det)_phi a equiv scripts(det)_psi a (mod P'), quad "since"
    scripts(det)_zeta = scripts(det)_phi slash scripts(det)_psi.
  $
  If $T$ affords $phi$ and $U$ affords $psi$, the above congruence becomes
  $ det T(a) equiv det U(a) (mod P'), $
  that is, #named-equation(name: [$(ast)$])[$
    det overline(T) lr((overline(a))) = det overline(U) lr((overline(a)))
    quad "in" overline(S).
  $] <eq:reduced-determinantal-equality>
  But $overline(T) = overline(U)$ in $G_0(overline(S) G)$ because
  $zeta in ker d$, so @eq:reduced-determinantal-equality clearly holds.
]

#exercises-heading

#exercise[
  Let $zeta in op("Irr") G$ and $x in K G$. Prove that
  $scripts(det)_zeta x in K(zeta)$.

  #hint[@exc:character-determinant-in-character-field][
    See proof of @prop:det-reduced-norm-hom-identification.
  ] <hint:character-determinant-in-character-field>
] <exc:character-determinant-in-character-field>

#exercise[
  Let $M$ be a locally free left ideal of $R G$, and $caron(M)$ its
  contragredient (see §@ss:class-kernel-group-involution). If
  $f in Hom(op("ch") G, J^* lr((E)))$ is the representative function of $[M]$
  (see @cor:locally-free-ideal-det-representative), show that $[caron(M)]$ has
  representative function $caron(f)$, where
  $ caron(f)(zeta) = f(caron(zeta))^(-1), quad zeta in op("ch") G, $
  with $caron(zeta)$ defined by $caron(zeta) lr((x)) = zeta(x^(-1))$, $x in G$
  (so $caron(zeta) = "complex conjugate of" zeta$ if $K$ is a number field).
] <exc:contragredient-hom-representative>

#exercise[
  View $op("Cl") R G$ as a $(op("ch") K G)$-module, as in
  @cor:class-kernel-groups-field-frobenius, and let $M,f$ be as above. For
  $xi in op("ch") K G$, let $g$ be the representative function of the class
  $xi[M] in op("Cl") R G$. Prove that
  $ g(zeta) = f(overline(xi) zeta), quad zeta in op("ch") G, $
  where $overline(xi)$ is the complex conjugate of $xi$ (see Ullom
  @bib:Ullom1981).
] <exc:character-action-hom-representative>
