#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/72-modular.typ": *

== Modular Representations of Finite Groups of Lie Type
<sec:modular-lie-type>

=== The Ballard–Lusztig Theorem on Characters of P.I.M.'s
<ss:ballard-lusztig-projective-characters>

Throughout this subsection, $G$ denotes a finite group with a split $B N$-pair
of characteristic $p$. We let $W$ denote the Weyl group of $G$, and $S$ the set
of #source(717) distinguished generators of $W$ (see
§~@ss:split-bn-pair-levi-decomposition). The prime $p$ is sometimes called the
_natural characteristic_ of $G$. Our aim is to present some aspects of the
modular representation theory of $G$, with respect to a $p$-modular system
$(K,R,k)$, such that $char K=0$ and $K$ is sufficiently large relative to $G$.
The first result is a remarkable theorem, proved by Ballard @bib:Ballard1976 and
Lusztig @bib:Lusztig1976 independently, which asserts that the $K$-characters
afforded by P.I.M.'s in $cal(P)(R G)$ are all divisible by the Steinberg
character $"St"_G$, in the ring $"ch" G$ (see also Feit @bib:Feit1976, for a
related result). Our approach follows Broué @bib:Broue1982, and is based on
properties of the duality operation $D_G$ established in
§~@sec:character-duality.

We begin with some properties of the operations $T_(L_I)^G$ and $R_(L_I)^G$, for
$I subset.eq S$, similar to the identity
@i:lem:class-function-induction-product, which states that
$xi dot psi^G=(xi_H dot psi)^G$ for all class functions $xi in "cf"_K G$,
$psi in "cf"_K H$, where $H lt.eq G$. We first require the concept of
_$p'$-sections_, which are the equivalence classes in $G$ defined by the
equivalence relation that puts $x$ equivalent to $x'$, for $x,x' in G$, if and
only if their $p'$-parts are conjugate in $G$.

#lemma[
  Let $mu in "cf"_K G$, and suppose that $mu$ is constant on $p'$-sections. Let
  $I subset.eq S$, and let $P_I=L_I V_I$ be the Levi decomposition of a standard
  parabolic subgroup $P_I$ (see @th:split-bn-parabolic-levi-decomposition). Then
  we have
  $ mu(l v)=mu(l) quad "for all" l in L_I, v in V_I. $
]<lem:prime-to-p-section-parabolic-values>

#proof[
  By @lem:semidirect-p-group-prime-to-p-parts-conjugate, we obtain
  $ (l v)_(p') =_G l_(p'), $
  and the lemma follows.
]

#proposition[
  Let $nu in "cf"_K G$, and assume that $nu$ is constant on $p'$-sections. Then
  the following statements hold, for each subset $I subset.eq S$.
  #case-list(
    numbering: "(i)",
    [#case[
      $T_(L_I)^G lr((chi dot nu))=(T_(L_I)^G chi)(T_(L_I)^G nu)$ for all
      $chi in "cf"_K G$;
    ]<case:section-constant-truncation-product>],
    [#case[
      $R_(L_I)^G lr((xi)) dot nu=R_(L_I)^G lr((xi dot T_(L_I)^G nu))$, for all
      $xi in "cf"_K L_I$.
    ]<case:section-constant-generalized-induction-product>],
  )
]<prop:section-constant-truncation-induction-products>

#proof[
  (i) We have
  $
    T_(L_I)^G nu(l)=abs(V_I)^(-1) sum_(v in V_I) nu(v l)
    quad "for all" l in L_I
  $
  by the definition of truncation
  @def:character-truncation-generalized-induction. Using
  @lem:prime-to-p-section-parabolic-values it follows that $T_(L_I)^G nu=nu$,
  since $nu$ is constant on $p'$-sections. We then obtain
  $
    T_(L_I)^G lr((chi dot nu))(l) & =abs(V_I)^(-1) sum_(v in V_I)
    chi(l v) nu(l v) \
    & =lr([abs(V_I)^(-1) sum_(v in V_I) chi(l v)]) nu(l)
  $
  using @lem:prime-to-p-section-parabolic-values. Since $nu=T_(L_I)^G nu$ by the
  preceding remark, part (i) is proved.

  #source(718)
  For the proof of part (ii), we use the adjointness formula
  @prop:truncation-induction-basic-properties
  (part~@case:truncation-generalized-induction-adjointness), extended to class
  functions. Then, for all $zeta in "Irr" G$, we have
  $
    (R_(L_I)^G lr((xi dot T_(L_I)^G nu)),zeta)_G
    &=(xi dot T_(L_I)^G nu,T_(L_I)^G zeta)_(L_I) \
    &=(xi,T_(L_I)^G overline(nu) T_(L_I)^G zeta)_(L_I),
  $
  where $overline(nu)(x)=nu(x^(-1))$ for $x in G$. Since $overline(nu)$ is also
  constant on $p'$-sections, we have
  $
    T_(L_I)^G overline(nu) dot T_(L_I)^G zeta
    =T_(L_I)^G lr((overline(nu) zeta))
  $
  by part (i). Applying the adjointness formula
  @prop:truncation-induction-basic-properties
  (part~@case:truncation-generalized-induction-adjointness) again, we obtain
  $
    (R_(L_I)^G lr((xi dot T_(L_I)^G nu))
      -(R_(L_I)^G xi) dot nu,zeta)_G=0
  $
  for all $zeta in "Irr" G$, and part (ii) follows, since $"Irr" G$ is a basis
  for $"cf"_K G$. This completes the proof.
]

We shall find it convenient to use the notation $"cf"_K lr((G,G_(p')))$, as in
§~@sec:blocks-group-theory, to denote the set of class functions in $"cf"_K G$
that vanish outside $G_(p')$. We next define the _Brauer lift_ $"Br"_G$, which
is a $K$-homomorphism
$ "Br"_G:"cf"_K lr((G,G_(p'))) arrow.r "cf"_K G $
defined by
$ "Br"_G phi(x)=phi(s) quad "for all" phi in "cf"_K lr((G,G_(p'))), $
<eq:brauer-lift-prime-to-p-part>
where $x in G$, and $s$ is the $p'$-part of $x$. By
@i:th:brauer-lift-virtual-character, $"Br"_G phi in "ch" G$ whenever $phi$ is a
Brauer character, afforded by some $k G$-module. We also define a map
$"Br"_G^*:"cf"_K G arrow.r "cf"_K lr((G,G_(p')))$ by setting
$
  "Br"_G^* mu(x)=cases(
    sum_(u in C_G lr((s))_p) mu(s u) & "if" x=s in G_(p'),
    0 & "if" x in.not G_(p'),
  )
$
<eq:brauer-lift-transpose-p-element-sum>
where $C_G lr((s))_p$ denoted the set of $p$-elements in the centralizer of $s$.
As the notation suggests, we have:

#proposition[
  The maps $"Br"_G$ and $"Br"_G^*$ are transposes of each other with respect to
  the scalar product $(,)_G$.
]<prop:brauer-lift-transpose>

The proof is immediate from the definitions, and is omitted.

Now let $D_G:"cf"_K G arrow.r "cf"_K G$ be the duality operation, defined on
$"ch" G$ by @def:character-duality-operation, and extended by linearity to
$"cf"_K G$. By @th:steinberg-alternating-parabolic-character, the Steinberg
character of $G$ is given by
$ "St"_G=D_G 1_G, $
where $1_G$ is the trivial character of $G$.

#source(719)
#idx("Broué's Theorem")
#theorem(title: [Broué @bib:Broue1982])[
  Let $phi in "cf"_K lr((G,G_(p')))$ and $chi in "cf"_K G$. Then
  #case-list(
    numbering: "(i)",
    [#case[$"Br"_G phi=D_G lr(("St"_G dot phi))$]<case:brauer-lift-duality>],
    [#case[
      $"Br"_G^* chi="St"_G dot D_G chi$.
    ]<case:brauer-lift-transpose-duality>],
  )
]<th:broue-brauer-lift-duality>

#proof[
  (i) For each class function $phi in "cf"_K lr((G,G_(p')))$, $"Br"_G phi$ is
  constant on $p'$-sections, by its definition @eq:brauer-lift-prime-to-p-part.
  We also have
  $ T_(L_I)^G "Br"_G phi="Br"_G phi quad "for all" I subset.eq S, $
  by the proof of @prop:section-constant-truncation-induction-products
  (part~@case:section-constant-truncation-product). It follows that
  $
    R_(L_I)^G T_(L_I)^G lr((chi dot "Br"_G phi))
    &=R_(L_I)^G lr(((T_(L_I)^G chi) dot "Br"_G phi)) \
    &=(R_(L_I)^G T_(L_I)^G chi) "Br"_G phi
  $
  for all $I subset.eq S$ and $chi in "cf"_K G$, by
  @prop:section-constant-truncation-induction-products
  (part~@case:section-constant-truncation-product) and
  @prop:section-constant-truncation-induction-products
  (part~@case:section-constant-generalized-induction-product). Since
  $ D_G chi=sum_(I subset.eq S)(-1)^abs(I) R_(L_I)^G T_(L_I)^G chi, $
  we obtain
  $
    D_G lr((chi dot "Br"_G phi))=(D_G chi) "Br"_G phi,
    quad "for" phi in "cf"_K lr((G,G_(p'))) "and" chi in "cf"_K G.
  $
  Setting $chi=1_G$, the preceding formula becomes
  $ D_G lr(("Br"_G phi))="St"_G "Br"_G phi. $
  Now apply $D_G$ to both sides of this equation. The result is that
  $
    "Br"_G phi=D_G^2 "Br"_G phi
    =D_G lr(("St"_G "Br"_G phi))=D_G lr(("St"_G phi))
  $
  since $D_G^2="id"$ by @th:character-duality-self-adjoint-involution, and
  $"St"_G "Br"_G phi="St"_G dot phi$ using the fact that $"St"_G$ vanishes on
  $p$-irregular elements, by @th:steinberg-character-values-centralizers. This
  completes the proof of part (i).

  (ii) First let $xi in "cf"_K lr((G,G_(p')))$. Then, for all $chi in "cf"_K G$,
  $
    ("Br"_G^* chi,xi) & =(chi,"Br"_G xi)
                        =(chi,D_G lr(("St"_G dot xi))) \
                      & =(D_G chi,"St"_G dot xi)=(D_G chi dot "St"_G,xi)
  $
  using part (i), @prop:brauer-lift-transpose,
  @th:character-duality-self-adjoint-involution, and the fact that $"St"_G$ is
  rational valued by @th:steinberg-character-values-centralizers. On the other
  hand, $"Br"_G^* chi$ and $D_G chi dot "St"_G$ both vanish on $G-G_(p')$, by
  @eq:brauer-lift-transpose-p-element-sum and
  @th:steinberg-character-values-centralizers. It follows that
  $
    ("Br"_G^* chi-D_G chi dot "St"_G,xi)=0
    quad "for all" xi in "Irr" G,
  $
  and hence $"Br"_G^* chi=D_G chi dot "St"_G$, completing the proof.
]

Notice that part (i) of the preceding theorem gives an interesting
interpretation #source(720) of the Brauer lift $"Br"_G phi$. We shall
concentrate on an application of part (ii), which is based on some additional
properties of the Cartan–Brauer triangle
@i:prop:cartan-brauer-commutative-triangle. Let $"Bch" G$ denote the set of
virtual Brauer characters; thus a class function $xi$ belongs to $"Bch" G$ if
and only if $xi$ is a $ZZ$-linear combination of Brauer characters afforded by
$k G$-modules. By @i:prop:decomposition-brauer-character-square, there is a
commutative diagram
#decomposition-square
where the horizontal maps are isomorphisms, $d$ is the decomposition map, and
$d'$ is the restriction map $psi arrow.r lr(psi |)_(G_(p'))$.

We denote by $"Pch" G$ the $ZZ$-module generated by the Brauer characters of the
P.I.M.'s in $cal(P)(k G)$. Then $"Pch" G subset.eq "Bch" G$, and there exists a
commutative diagram
#cartan-square
where $c$ is the Cartan map @i:def:cartan-homomorphism-matrix, $c'$ is the
identity map, and the horizontal maps are isomorphisms.

There is also a commutative diagram
#projective-lift-square
where $e$ is defined by @i:eq:projective-character-map, the horizontal maps are
isomorphisms, and $e'$ is defined as follows. Let $P_1,dots,P_r$ be a basic set
of indecomposable projective $R G$-modules, and let $tau_1,dots,tau_r$ be the
$K$-characters afforded by them.

Let $U_i=overline(P)_i$, for $1 lt.eq i lt.eq r$. Then $U_1,dots,U_r$ is a basic
set of P.I.M.'s in $cal(P)(k G)$. Their Brauer characters
$eta^i:1 lt.eq i lt.eq r$ form a $ZZ$-basis of $"Pch" G$, and we have
$eta^i=lr(tau_i |)_(G_(p'))$, for $1 lt.eq i lt.eq r$. The map $e'$ is defined
on the basis of $"Pch" G$ consisting of the Brauer characters $eta^i$ by the
rule
$ e' eta^i=tau_i, quad 1 lt.eq i lt.eq r. $
<eq:projective-brauer-character-lift>

Using @i:prop:cartan-brauer-commutative-triangle and the preceding remarks, we
obtain a commutative diagram #numbered-block[
  #character-cartan-brauer-triangle
]<eq:character-cartan-brauer-triangle>
which will also be called the _Cartan–Brauer triangle_.

#source(721)
For the rest of the discussion, it will be convenient to regard $"Bch" G$ and
$"Pch" G$ as $ZZ$-submodules of $"cf"_K lr((G,G_(p')))$. We then have:

#proposition[
  Let $eta in "Pch" G$ and $chi in "ch" G$. Then
  $ (eta,d' chi)_G=(e' eta,chi)_G. $
]<prop:projective-character-lift-decomposition-adjointness>

#proof[
  It is sufficient to consider the special case of a basis element $eta^i$ of
  $"Pch" G$, as in @eq:projective-brauer-character-lift, and a basis element
  $zeta^j$ of $"ch" G$, where $zeta^j in "Irr" G$. Then
  $
    (eta^i,d' zeta^j)
    =lr((eta^i, sum_(l=1)^r d_(j l) phi^l))=d_(j i)
  $
  by @i:th:brauer-character-orthogonality-relations(i), while
  $ (e' eta^i,zeta^j)=(tau_i,zeta^j)=d_(j i) $
  by @i:th:projective-characters-supported-p-regular(i). This completes the
  proof.
]

We can now state the main result.

#idx("Ballard-Lusztig Theorem")
#theorem(title: [Ballard @bib:Ballard1976, Lusztig @bib:Lusztig1976])[
  For every virtual projective character $eta in "Pch" G$, we have
  $ eta="St"_G dot mu quad "for some" mu in "ch" G. $
  In other words, $"Pch" G$ is a principal ideal in $"ch" G$ generated by
  $"St"_G$.
]<th:ballard-lusztig-projective-character-divisibility>

#proof[
  By the definition of the maps $d'$ and $"Br"_G$, we have
  $ d' "Br"_G="id" quad "on" "Pch" G. $
  Taking transposes with respect to the scalar product $(,)_G$, and using
  @prop:projective-character-lift-decomposition-adjointness and
  @prop:brauer-lift-transpose, the preceding formula yields
  $ "Br"_G^* e'="id" quad "on" "Pch" G. $
  This implies that the map $"Br"_G^*$ defines a surjection
  $ "Br"_G^*:"ch" G arrow.r "Pch" G. $
  Now let $eta in "Pch" G$. Then
  $ eta="Br"_G^* chi="St"_G dot D_G chi $
  for some $chi in "ch" G$, by @th:broue-brauer-lift-duality and the fact that
  $"Br"_G^*$ is surjective. Moreover, $D_G chi in "ch" G$ whenever
  $chi in "ch" G$. This completes the proof.
]

#source(722)
#remark(numbered: false)[
  By @th:steinberg-character-sign-correspondence and
  @prop:split-bn-pair-order-sylow-steinberg, $"St"_G$ is an irreducible
  character of $G$ whose degree is the $p$-part $abs(G)_p$ of the order of $G$.
  By @prop:defect-zero-block-singletons, $"St"_G$ belongs to a $p$-block of $G$
  of defect zero, and is afforded by an $R G$-lattice $P in cal(P)(R G)$ with
  the property that $overline(P)=P slash frak(p) P$ is a P.I.M. in
  $cal(P)(k G)$, and is also a simple $k G$-module. An explicit construction of
  a primitive idempotent $e in k G$ such that $k G e tilde.equiv overline(P)$
  was given by Steinberg (@bib:Steinberg1956, @bib:Steinberg1957).
]<rem:steinberg-simple-projective-reduction>

=== The Simple $k G$-Modules
<ss:simple-modules-natural-characteristic>

As in §~@ss:ballard-lusztig-projective-characters, $G$ denotes a finite group
with a split $B N$-pair of characteristic $p$, and $k$ a field of characteristic
$p$ that is sufficiently large relative to $G$. Our objective is to classify the
simple $k G$-modules, in the natural characteristic $p$. We shall present a
direct approach to the problem, based on the work of Richen @bib:Richen1969 and
Curtis @bib:Curtis1965, @bib:Curtis1970, and recent contributions involving
modular Hecke algebras by Carter–Lusztig @bib:Carter1976, Sawada
@bib:Sawada1977, Tinberg @bib:Tinberg1979, @bib:Tinberg1980b, Green
@bib:Green1978b, and Cabanes. For related results, see Norton @bib:Norton1979.
In case $G=bold(G)(FF_q)$ is the group of $FF_q$-rational points on a connected
reductive affine algebraic group $bold(G)$, the simple $k G$-modules can also be
classified using the rational characters of a maximal torus of $bold(G)$ (see
Borel @bib:Borel1970 or Steinberg @bib:Steinberg1967).

In spite of these efforts, the problem of calculating the Brauer characters of
the simple $k G$-modules, or even their degrees, remains unsolved at this time.
A conjecture concerning the Brauer characters has been made by Lusztig
@bib:Lusztig1980.

We shall use the notation from §§~@sec:finite-groups-bn-pairs and
@sec:finite-groups-split-bn-pairs. In particular, $B$ denotes a fixed Borel
subgroup of $G$, $U=O_p lr((B))$, and $T=N inter B$. We assume that
$T=inter.big_(n in N) attach(B, tl: n)$, and that $T$ is an abelian $p'$-group
(see @def:split-bn-pair). As usual, $W$ denotes the Weyl group $N/T$, and
$S={s_1,dots,s_l}$ denotes the set of distinguished generators of $W$. Let
$Delta$ be a root system associated with $W$, and $U_alpha:alpha in Delta$ the
corresponding root subgroups of $G$ (see
@prop:split-bn-root-subgroup-properties), ordered so that $U$ is generated by
the root subgroups $U_alpha:alpha in Delta_+$, and the involutions $s_i in S$
are the fundamental reflections with respect to a set of fundamental roots
$Pi={alpha_1,dots,alpha_l}$ in $Delta_+$.

For each subset $I subset.eq S$, $W_I$ denotes the parabolic subgroup of $W$
generated by the reflections belonging to $I$.

#lemma[
  Let $L$ be a simple $k B$-module. Then $dim_k L=1$, and $U$ acts trivially on
  $L$.
]<lem:borel-simple-module-linear>

#proof[
  Since $U=O_p lr((B)) ⊴ B$, the restriction $L_U$ is a semisimple $k U$-module,
  by Clifford's Theorem @i:th:clifford-theorem. Then $U$ acts trivially on $L$
  by @i:th:p-group-algebra-local, since $U$ is a $p$-group and $char k=p$. It
  follows that $L$ is a simple $k(B/U)$-module, and hence $dim L=1$, using the
  facts that $B/U tilde.equiv T$ is an abelian $p'$-group, and $k$ is
  sufficiently large. This completes the proof.
]

#corollary[
  Let $M$ be a simple $k G$-module. Then $"inv"_U M !=0$, and there exists a
  surjection of $k G$-modules $(1_U)^G arrow.r M$.
]<cor:simple-module-unipotent-invariants-quotient>

#proof[
  Let $L$ be a simple $k B$-submodule of $M_B$. Then $U$ acts trivially on $L$,
  #source(723)
  by @lem:borel-simple-module-linear, so $"inv"_U M !=0$. By the Frobenius
  Reciprocity Theorem @i:th:frobenius-reciprocity, we obtain
  $
    "Hom"_(k G)((1_U)^G,M)
    tilde.equiv "Hom"_(k U)(1_U,M) tilde.equiv "inv"_U M !=0,
  $
  and the result follows, since $M$ is a simple $k G$-module.
]

By @cor:simple-module-unipotent-invariants-quotient, every simple $k G$-module
occurs as a composition factor of $(1_U)^G$, so it is natural to classify them
in terms of representation of $"End"_(k G)(1_U)^G$, as in
§~@i:ss:hecke-algebras. We now introduce some of the notation and basic ideas
needed to carry out this plan. Let $k_U$ denote the field $k$, viewed as a
$k U$-module on which $U$ acts trivially. Throughout this subsection, we shall
set
$
  Y=k G times.o_(k U) k_U, quad "and" quad
  E=("End"_(k G) Y)^∘ quad "(opposite ring)."
$
We may identify $Y$ with the induced module $(1_U)^G$, and note that $Y$ is a
cyclic $k G$-module, generated by $1 times.o 1$. The $k$-algebra $E$ is called
the #idx("Modular Hecke algebra")_modular Hecke algebra_, and is taken as a
$k$-algebra of right operators on $Y$, so that $Y$ is a $(k G,E)$-bimodule. In
contrast to §~@i:ss:hecke-algebras, it is no longer true, in this case, that $E$
is a semisimple $k$-algebra.

#proposition[
  #case-list(
    numbering: "(i)",
    [#case[
      A $k$-basis of the modular Hecke algebra $E$ consists of the elements
      $a_n:n in N$, whose action on $Y$ is given by the formulas
      $
        (1 times.o 1) a_n
        =sum_(u in U/(U inter attach(U, tl: n))) u n times.o 1,
        quad (g times.o 1) a_n=g((1 times.o 1) a_n)
      $
      for all $n in N$ and $g in G$, where, as usual,
      $u in U/(U inter attach(U, tl: n))$ means that the sum is taken over a
      cross section of the left cosets $U/(U inter attach(U, tl: n))$.
    ]<case:modular-hecke-double-coset-basis>],
    [#case[
      Let $M$ be an arbitrary f.g. left $k G$-module. Then, if $M!=0$,
      $"inv"_U M !=0$. There exists a left action of $E$ on $"inv"_U M$, given
      by
      $
        a_n m=sum_(u in U/(U inter attach(U, tl: n))) u n m,
        quad m in "inv"_U M,
      $
      for each basis element $a_n$ of $E$ defined in part (i).
    ]<case:modular-hecke-action-unipotent-invariants>],
  )
]<prop:modular-hecke-basis-invariant-action>

#proof[
  (i) The additive structure of $E$ is described by the Frobenius Reciprocity
  Theorem @i:th:frobenius-reciprocity, which asserts that there is an
  isomorphism of $k$-spaces
  $ "End"_(k G) Y tilde.equiv "Hom"_(k U)(k_U,Y). $
  <eq:modular-hecke-frobenius-invariant-identification>
  The elements of $N$ form a cross section of the double cosets
  $U backslash G/U$, by the sharp form of the Bruhat decomposition
  @prop:split-bn-root-subgroup-properties(v). This yields a direct
  decomposition.
  $
    "Hom"_(k U)(k_U,Y) tilde.equiv
    plus.o.big_(n in N) "Hom"_(k U)(k_U,k U n U times.o_(k U) k_U),
  $

  #source(724)
  where the sum is taken over the cross section $N$ of $U backslash G/U$, and
  $k U n U$ denotes the $k$-space generated by the elements of the double coset
  $U n U$. Each subspace $"Hom"_(k U)(k_U,k U n U times.o_(k U) k)$ is
  one-dimensional, and is generated by an element $f_n$ such that
  $
    f_n lr((1))=sum_(u in U/(U inter attach(U, tl: n))) u n times.o 1
    quad "(for each" n in N ")."
  $
  The isomorphism @eq:modular-hecke-frobenius-invariant-identification is
  described explicitly in the proof of the Adjointness Theorem
  @i:th:hom-tensor-adjointness (see also the proof of
  @i:th:frobenius-reciprocity.) Let $a_n in E$ be the element corresponding to
  $f_n$ in @eq:modular-hecke-frobenius-invariant-identification. Then we have
  $
    (1 times.o 1) a_n=sum_(u in U/(U inter attach(U, tl: n))) u n times.o 1,
    quad "for each" n in N,
  $
  by the proof of @i:th:hom-tensor-adjointness. Since $Y$ is a cyclic
  $k G$-module with generator $1 times.o 1$, and each endomorphism $a_n$
  commutes with the action of $k G$, the maps $a_n:n in N$ are uniquely
  determined by their action on $1 times.o 1$, completing the proof of part (i).

  (ii) Since $Y$ is a $(k G,E)$-bimodule, there exists a left action of $E$ on
  $"Hom"_(k G)(Y,M)$ given by composition:
  $
    a dot f=f compose a quad "for" a in E
    quad "and" quad f in "Hom"_(k G)(Y,M),
  $
  for any left $k G$-module $M$. Moreover, there exist isomorphisms of
  $k$-spaces
  $
    "Hom"_(k G)(Y,M) tilde.equiv "Hom"_(k U)(k_U,M_U)
    tilde.equiv "inv"_U M,
  $
  using @i:th:frobenius-reciprocity. It follows that there exists also a left
  action of $E$ on $"inv"_U M$, which is given by
  $
    a_n m=sum_(u in U/(U inter attach(U, tl: n))) u n m,
    quad "for" m in "inv"_U M "and" n in N.
  $
  To verify the last statement, each element $m in "inv"_U M$ corresponds to a
  map $f_m in "Hom"_(k U)(k_U,M_U)$ such that $f_m lr((1))=m$. By the proof of
  @i:th:hom-tensor-adjointness, the map $phi_m in "Hom"_(k G)(Y,M)$
  corresponding to $f_m$ is given by
  $ phi_m lr((g times.o 1))=g m, quad "for" g in G. $
  Then $a_n phi_m$ acts on $1 times.o 1$ according to the rule
  $
    a_n phi_m lr((1 times.o 1))
    &=phi_m compose a_n lr((1 times.o 1))
    =sum_(u in U/(U inter attach(U, tl: n))) phi_m lr((u n times.o 1)) \
    &=sum_(u in U/(U inter attach(U, tl: n))) u n m.
  $
  To finish the proof of (ii), we need only verify that $"inv"_U M !=0$, and
  this is part of @cor:simple-module-unipotent-invariants-quotient.
]

#source(725)
We turn next to the multiplicative structure of the modular Hecke algebra $E$,
after some preliminary discussion. We let $pi$ denote the natural map
$N arrow.r N/T=W$, and use it to define a length function on $N$, setting
$ l(n)=l(pi(n))=l(w) quad "if" pi(n)=w in W, $
where $w arrow.r l(w)$ is the usual length function on the Weyl group $W$. Note
that $l(n)=0$ if and only if $n in T$. In what follows, we shall often set
$U_i=U_(alpha_i)$, for $alpha_i in Pi$, and $U_i^*=U_i-{1}$.
#idx("Modular Hecke algebra")

#lemma[
  (Structure equations in $G$.) Let $n_i in N$ be an element of length one, with
  $pi(n_i)=s_i in S$, for $1 lt.eq i lt.eq l$. Then there exist maps
  $f_i:U_i^* arrow.r U_i^*$, $t_i:U_i^* arrow.r T$, and
  $g_i:U_i^* arrow.r U_i^*$, which depend on the choice of $n_i$, and satisfy
  $
    n_i u n_i=f_i lr((u)) t_i lr((u)) n_i g_i lr((u))
    quad "for all" u in U_i^*.
  $
]<lem:rank-one-root-subgroup-structure-equations>

#proof[
  By @prop:split-bn-root-subgroup-properties(vi),
  $ G_i=U_i T union U_i T n_i U_i $
  is a subgroup of $G$, and clearly has a split $B N$-pair of rank $1$. For each
  element $u in U_i^*$, we have $n_i u n_i in U_i T n_i U_i$, otherwise
  $n_i u n_i in U_i T$ by the Bruhat decomposition of $G_i$, and we contradict
  the fact that $U^- inter B=1$ (see
  @prop:split-bn-root-subgroup-properties(i)). It then follows easily, using the
  Bruhat decomposition in $G_i$, that the maps $f_i$, $t_i$, and $g_i$ exist, as
  stated in the lemma.
]

#proposition[
  The basis elements $a_n:n in N$ of the modular Hecke algebra $E$ are
  multiplied as follows:
  $
    a_t a_n=a_(t n) quad "and" quad a_n a_t=a_(n t)
    quad "for all" n in N,t in T.
  $
  $
    a_(n_i) a_n=a_(n_i n)
    quad "if" l(n_i)=1 quad "and" quad l(n_i n) gt.eq l(n)
  $
  $
    a_(n_i) a_n=sum_(u in U_i^*) a_(t_i lr((u))) a_n
    quad "if" l(n_i)=1 quad "and" quad l(n_i n)<l(n)
  $
  where $t_i lr((u)):u in U_i^*$ are the elements of $T$ determined by the
  structure equations @lem:rank-one-root-subgroup-structure-equations involving
  the element $n_i in N$.
]<prop:modular-hecke-basis-multiplication>

#proof[
  In this proof, and for the rest of this section it will be convenient to use
  the notation
  $ sigma(X)=sum_(x in X) x quad "for" X subset.eq G, $
  <eq:group-algebra-subset-sum>
  where the sum is taken in the group algebra $k G$. We first observe that if
  $n in N$ and $pi(n)=w in W$, then $U inter attach(U, tl: n)=U_(w^(-1))^+$, and
  hence $U_(w^(-1))^-$ is a cross section of #source(726)
  $U/(U inter attach(U, tl: n))$, by
  @prop:split-bn-root-subgroup-properties(ii)). Accordingly we may write
  $ (1 times.o 1) a_n=sigma(U_(w^(-1))^-) n times.o 1 $
  in the equation defining $a_n$, using the notation
  @eq:group-algebra-subset-sum. In particular, we have
  $ (1 times.o 1) a_t=t times.o 1 quad "for" t in T $
  since $pi(t)=1$ and $U_1^-=1$. Now let $n in N$ and $pi(n)=w$. Then we obtain,
  for $t in T$,
  $
    (1 times.o 1) a_t a_n&=(t times.o 1) a_n=t((1 times.o 1) a_n)
    =t sigma(U_(w^(-1))^-) n times.o 1 \
    &=sigma(U_(w^(-1))^-) t n times.o 1=(1 times.o 1) a_(t n),
  $
  using the preceding formulas, and the facts that $a_n$ commutes with the
  action of $k G$, $pi(t n)=pi(n)=w$, and
  $t sigma(U_(w^(-1))^-) t^(-1)=sigma(U_(w^(-1))^-)$ since $T$ normalizes
  $U_(w^(-1))^-$ (see §~@ss:split-bn-pair-levi-decomposition). As in the proof
  of @prop:modular-hecke-basis-invariant-action
  (part~@case:modular-hecke-double-coset-basis), it follows that
  $ a_t a_n=a_(t n) $
  since $Y$ is a cyclic $k G$-module. A similar argument proves that
  $a_n a_t=a_(n t)$.

  Next we assume that $l(n_i)=1$ so $pi(n_i)=s_i in S$, and consider an element
  $n in N$ such that $pi(n)=w$ and $l(s_i w) gt.eq l(w)$. Then we obtain
  $
    (1 times.o 1) a_(n_i) a_n & =(sigma(U_i) n_i times.o 1) a_n
                                =sigma(U_i) n_i sigma(U_(w^(-1))^-) n times.o
                                1 \
                              & =sigma(U_i)
                                sigma(attach(U_(w^(-1))^-, tl: s_i))
                                n_i n times.o 1
                                =sigma(U_(w^(-1) s_i)^-) n_i n times.o 1 \
                              & =(1 times.o 1) a_(n_i n).
  $
  Here we have used the fact that
  $sigma(U_i) sigma(attach(U_(w^(-1))^-, tl: s_i))=sigma(U_(w^(-1) s_i)^-)$,
  since $U_(w^(-1) s_i)^-=U_(alpha_i) attach(U_(w^(-1))^-, tl: s_i)$ and
  $U_(alpha_i) inter attach(U_(w^(-1))^-, tl: s_i)=1$ if $l(s_i w)>l(w)$, by
  @eq:unipotent-inversion-root-step. It follows that $a_(n_i) a_n=a_(n_i n)$,
  proving the second statement in @prop:modular-hecke-basis-multiplication.

  For the proof of the third formula in
  @prop:modular-hecke-basis-multiplication, we first consider $a_(n_i)^2$. We
  have
  $
    (1 times.o 1) a_(n_i)^2 & =sigma(U_i) n_i sigma(U_i) n_i times.o 1 \
                            & =sigma(U_i) n_i^2 times.o 1
                              +sigma(U_i) sum_(u in U_i^*) f_i lr((u)) t_i
                              lr((u)) n_i g_i lr((u))
                              times.o 1 \
                            & =sigma(U_i) sum_(u in U_i^*) t_i lr((u)) n_i
                              times.o 1
                              =(1 times.o 1) sum_(u in U_i^*) a_(t_i lr((u))
                              n_i)
  $
  using the structure equations @lem:rank-one-root-subgroup-structure-equations
  involving $n_i$, and the fact that
  $sigma(U_i) n_i^2 times.o 1=abs(U_i)(n_i^2 times.o 1)=0$ in $k$, since
  $n_i^2 in T$. It follows that
  $ a_(n_i)^2=sum_(u in U_i^*) a_(t_i lr((u)) n_i). $
  Now let $l(n_i)=1$ and assume that $l(n_i n)<l(n)$. Put $n'=n_i n$; then
  $n=n_i^(-1) n'$ and #source(727) $l(n_i^(-1) n') gt.eq l(n')$. Consequently
  $
    a_n=a_(n_i^(-1)) a_(n')=a_(n_i) a_t a_(n'),
    quad "if" n_i^(-1)=n_i t, quad t in T,
  $
  using the preceding results. Multiplication by $a_(n_i)$ yields
  $
    a_(n_i) a_n & =a_(n_i)^2 a_t a_(n')
                  =sum_(u in U_i^*) a_(t_i lr((u))) a_(n_i) a_t a_(n') \
                & =sum_(u in U_i^*) a_(t_i lr((u))) a_(n_i^(-1)) a_(n')
                  =sum_(u in U_i^*) a_(t_i lr((u))) a_n,
  $
  completing the proof.
]

#corollary[
  Let $X$ be a simple $E$-module. Then $dim_k X=1$.
]<cor:modular-hecke-simple-modules-linear>

#proof[
  By @prop:modular-hecke-basis-multiplication, the subalgebra $E_T$ of $E$
  generated by the elements $a_t:t in T$ is isomorphic to the group algebra
  $k T$, which is a commutative split semisimple $k$-algebra, by our assumptions
  on $T$ and $k$. It follows that $lr(X |)_(E_T)$ is a semisimple $E_T$-module,
  and the simple submodules are all one-dimensional. Moreover, if
  $lr(chevron.l x chevron.r)$ is a simple $E_T$-submodule of $lr(X |)_(E_T)$ and
  $n in N$, then $a_n lr(chevron.l x chevron.r)$ is another simple $E_T$-module
  or zero, since $T ⊴ N$ and
  $ a_t a_n=a_(t n)=a_n a_(n^(-1) t n) $
  by @prop:modular-hecke-basis-multiplication. Now let
  $lr(chevron.l x_0 chevron.r)$ be a fixed simple $E_T$-submodule of
  $lr(X |)_(E_T)$, and let $n in N$ be an element of maximal length such that
  $a_n x_0 !=0$. Then $lr(chevron.l a_n x_0 chevron.r)$ is an $E_T$-submodule,
  and it follows from @prop:modular-hecke-basis-multiplication that
  $lr(chevron.l a_n x_0 chevron.r)$ is an $E$-submodule of $X$. Since $X$ is
  simple, we have $X=lr(chevron.l a_n x_0 chevron.r)$. Therefore $dim_k X=1$, as
  required.
]

#proposition[
  Let $M$ be an arbitrary f.g. $k G$-module, and let $lr(chevron.l m chevron.r)$
  be a simple (and hence one-dimensional) $E$-submodule of $"inv"_U M$. Then we
  have
  $ k G m=k U^- m, $
  where $U^-=attach(U, tl: w_0)$ (see §~@ss:split-bn-pair-levi-decomposition).
]<prop:hecke-eigenline-opposite-unipotent-generation>

#proof[
  By @prop:modular-hecke-basis-invariant-action, $"inv"_U M$ is a nonzero
  $E$-module, and its simple $E$-submodules are one-dimensional, by
  @cor:modular-hecke-simple-modules-linear. By
  @prop:modular-hecke-basis-invariant-action
  (part~@case:modular-hecke-action-unipotent-invariants), the action of any
  element $t in T$ on $"inv"_U M$ is the same as the action of the corresponding
  element $a_t in E$. Therefore a simple $E$-submodule
  $lr(chevron.l m chevron.r)$ of $"inv"_U M$ is a $k B$-submodule of $M_B$. The
  result that $k G m=k U^- m$ will follow if we can prove that $n m in k U^- m$
  for all $n in N$, since
  $ G=n_0 G=union.big_(n in N) U^- n B quad "where" pi(n_0)=w_0, $
  by the Bruhat decomposition. We begin with an element $n_i in N$ of length
  $1$. Then #source(728) $a_(n_i) m=mu_i m$ for some $mu_i in k$. On the other
  hand, using @prop:modular-hecke-basis-invariant-action and
  @lem:rank-one-root-subgroup-structure-equations, we obtain
  $
    a_(n_i) m=mu_i m & =n_i m+sum_(u in U_i^*) u n_i m \
                     & =n_i m+sum_(u in U_i^*) n_i^(-1)(n_i u n_i) m \
                     & =n_i m+sum_(u in U_i^*) n_i^(-1) f_i lr((u)) t_i lr((u))
                       n_i g_i lr((u)) m.
  $
  From this it follows that $n_i m in k U_(-alpha_i) m$, since
  $attach(U_i, tl: n_i)=U_(-alpha_i)$. Now let $n in N$ be an element such that
  $l(n)>1$, and write $n=n' n_i$ for some elements $n_i$ and $n'$ with
  $l(n_i)=1$ and $l(n')<l(n)$. By the preceding argument, we have
  $ n m=n' n_i m in n' k U_(-alpha_i) m, $
  and the result follows by induction on $l(n)$, since
  $n' U_(-alpha_i) (n')^(-1) subset.eq U^-$ from the results in
  §~@ss:split-bn-pair-levi-decomposition. This completes the proof.
]

We are ready to begin the classification of the simple $k G$-modules $M$. In the
next result, we shall prove that $"inv"_U M$ is a simple, and hence
one-dimensional, $E$-module. In particular, $"inv"_U M$ is a simple
$k B$-submodule of $M_B$, and affords a linear representation
$chi in "Hom"(B,k^dot)$, where $k^dot$ is the multiplicative group of the field
$k$. By analogy with the representation theory of semisimple algebraic groups or
Chevalley groups (see Steinberg @bib:Steinberg1967 or Borel @bib:Borel1970), we
might expect the simple $k G$-modules $M$ to be determined up to isomorphism by
the homomorphism $chi in "Hom"(B,k^dot)$ afforded by $"inv"_U M$. But this is
not true, in general. For example, the group $S L_2(FF_p)$ has a simple module
of dimension $p$ over an algebraically closed field of characteristic $p$,
corresponding to the Steinberg character (see §~@sec:hecke-algebras-bn-pairs or
§~@i:ss:brauer-character-orthogonality). In this module, and in the trivial
module, the subspaces of fixed points under the action of a Sylow $p$-subgroup
$U$ both afford the trivial representation of the Borel subgroup $B$ containing
$U$, but of course the modules are not isomorphic. The modules are
distinguished, however, by the simple $E$-modules defined by the spaces of fixed
elements under the action of $U$. We shall prove that this situation holds in
the general case, by a method which still preserves some analogy with the
algebraic group case. A different approach, based on the observation that the
modular Hecke algebra $E$ is a quasi-Frobenius algebra, has been given by Green,
Sawada, and Tinberg (see the references at the beginning of
§~@ss:simple-modules-natural-characteristic).

#theorem[
  Let $M$ be a simple $k G$-module. Then $"inv"_U M$ is a simple, and hence
  one-dimensional, $E$-module. Two simple $k G$-modules $M_1$ and $M_2$ are
  isomorphic if and only if there exists an isomorphism of $E$-modules:
  $"inv"_U M_1 tilde.equiv "inv"_U M_2$.
]<th:simple-group-modules-unipotent-invariant-classification>

#proof[
  Let $M$ be a simple $k G$-module, and let $lr(chevron.l m chevron.r)$ be a
  simple $E$-submodule of $"inv"_U M$. Using the fact that $M$ is simple, we
  have $M=k U^- m$, by @prop:hecke-eigenline-opposite-unipotent-generation.
  Since $U$ is a $p$-group, we have $k U^-=k plus.o "rad" k U^-$, and
  $"rad" k U^-$ is generated #source(729) by the elements $u-1:u in U^-$ (see
  @i:th:p-group-algebra-local). Then $M=k m plus.o "rad" k U^- m$, and in order
  to prove the first statement of the theorem, it is enough to show that
  $"rad" k U^- m inter "inv"_U M=0$.

  Assume, to the contrary, that $X="rad" k U^- m inter "inv"_U M !=0$. We shall
  prove that $X$ is an $E$-submodule of $"inv"_U M$. Since $X$ is clearly
  stabilized by the action of $T$, and hence by the elements $a_t:t in T$, $X$
  is an $E$-module if we can prove that $a_(n_i) X
  subset.eq X$ for all elements $n_i in N$ of length $1$. From the action of
  $a_(n_i)$ on $"inv"_U M$, this will follow from the result that
  $sigma(U_i) n_i "rad" k U^- m subset.eq "rad" k U^- m$. Since
  $M=k m+"rad" k U^- m$, it is enough to prove
  $
    sigma(U_i) n_i lr((u-1))m in "rad" k U^- M,
    quad "for all" u in U^- "and" l(n_i)=1.
  $
  <eq:opposite-unipotent-radical-hecke-stability>
  We have $sigma(U_i) n_i m=a_(n_i) m=mu_i m$ for some $mu_i in k$, since
  $lr(chevron.l m chevron.r)$ is an $E$-module. Then for $u in U^-$,
  $
    sigma(U_i) n_i lr((u-1))m
    =sigma(U_i) n_i u m-mu_i m=n_i sigma(U_(-alpha_i)) u m-mu_i m,
  $
  since $n_i^(-1) U_i n_i=U_(-alpha_i)$. For each element $u in U^-$ and
  $u_i in U_(-alpha_i)$, we have
  $ u_i u=v_i u'_i, quad "where" v_i in V_i, quad u'_i in U_(-alpha_i), $
  and $V_i$ is the subgroup of $U^-$ generated by the root subgroups
  $U_(-alpha):alpha in Delta_+,alpha !=alpha_i$. Moreover, the map
  $u_i arrow.r u'_i$, for fixed $u in U^-$, is a permutation of $U_(-alpha_i)$.
  Both of these facts follow from the factorization, with uniqueness of
  expression, $U^-=U_(-alpha_i) V_i=V_i U_(-alpha_i)$ (see
  §~@ss:split-bn-pair-levi-decomposition). Returning to our calculation of
  @eq:opposite-unipotent-radical-hecke-stability, we obtain
  $
    n_i sigma(U_(-alpha_i)) u m-mu_i m
    =sum_(u'_i in U_(-alpha_i)) n_i v_i u'_i m-mu_i m,
  $
  where the $v_i$ are some elements of $V_i$. Upon writing each $v_i=1+(v_i-1)$,
  this expression becomes
  $
    sigma U_i n_i m-mu_i m
    +sum_(v_i) n_i lr((v_i-1))n_i^(-1) n_i u'_i m.
  $
  The first term is zero, while the second is in $"rad" k U^- M$ since
  $n_i V_i n_i^(-1) subset.eq U^-$, by
  @prop:split-bn-root-subgroup-properties(iii). This completes the proof of
  @eq:opposite-unipotent-radical-hecke-stability, and shows that $X$ is an
  $E$-submodule of $"inv"_U M$. Letting $lr(chevron.l m' chevron.r)$ be a simple
  $E$-submodule of $X$, it follows from
  @prop:hecke-eigenline-opposite-unipotent-generation that
  $M=k G m'=k U^- m' subset.eq "rad" k U^- M$, which is impossible since
  $"rad" k U^-$ is a nilpotent ideal in $k U^-$. Thus $X$ must be zero. This
  completes the proof that $"inv"_U M$ is a simple $E$-module.

  Now let $M_1$ and $M_2$ be simple $k G$-modules. If $M_1 tilde.equiv M_2$,
  then it follows easily, using the first part of the proof, that there exists
  an isomorphism of $E$-modules $"inv"_U M_1 tilde.equiv "inv"_U M_2$. For the
  converse, we assume that $"inv"_U M_1 tilde.equiv "inv"_U M_2$ as $E$-modules.
  Let $"inv"_U M_1=lr(chevron.l m_1 chevron.r)$ and
  $"inv"_U M_2=lr(chevron.l m_2 chevron.r)$. Consider the direct sum
  $M=M_1 plus.o M_2$, and let $pi_i$, $i=1,2$, be the resulting projections of
  $k G$-modules. Let $m=m_1+m_2 in M$; then $lr(chevron.l m chevron.r)$ is a
  simple $E$-submodule of $"inv"_U M$

  #source(730)
  that is isomorphic to $lr(chevron.l m_1 chevron.r)$ and
  $lr(chevron.l m_2 chevron.r)$. Then $k G m=k U^- m$ by
  @prop:hecke-eigenline-opposite-unipotent-generation, $pi_i m=m_i$ for $i=1,2$,
  and the projections restrict to surjective $k G$-maps
  $pi_i:k G m arrow.r M_i$, $i=1,2$, because $M_1$ and $M_2$ are simple modules.
  We shall prove that $pi_1:k G m arrow.r M_1$ is an isomorphism. We have
  $ker pi_1 inter k G m subset.eq M_2 inter k G m$, and $M_2 inter k G m$ is
  either $0$ or $M_2$. It follows that $pi_1:k G m arrow.r M_1$ is an
  isomorphism if we can prove that $m_2 in.not M_2 inter k G m$. Suppose, to the
  contrary, that $m_2 in M_2 inter k G m$; then $m_2=xi m+m'$ for $xi in k$ and
  $m' in "rad" k U^- m$. Upon applying $pi_1$ and $pi_2$ to this expression, we
  obtain
  $ 0=xi m_1+pi_1 m' quad "and" quad m_2=xi m_2+pi_2 m', $
  where $pi_1 m' in "rad" k U^- M_1$ and $pi_2 m' in "rad" k U^- M_2$. It
  follows that $xi=0$ and $xi=1$, which is impossible. Thus
  $ker pi_1 inter k G m=0$, and $pi_1:k G m arrow.r M_1$ is an isomorphism.
  Similarly, $pi_2:k G m arrow.r M_2$ is an isomorphism, and
  $M_1 tilde.equiv M_2$ as required.
]

The next step is to construct a basic set of simple $E$-modules, and to prove
that each of them occurs in $"inv"_U M$ for some simple $k G$-module $M$. We
require a few more items of notation and some preliminary remarks. For each $i$,
$1 lt.eq i lt.eq l$, we set
$
  G'_i=lr(chevron.l U_(alpha_i), U_(-alpha_i) chevron.r),
  quad T_i=T inter G'_i,
$
and note that each group $G'_i$ is a subgroup of the group
$G_i=U_(alpha_i) T union U_(alpha_i) T n_i U_(alpha_i)$ discussed earlier, and
is a finite group with a split $B N$-pair of rank $1$. From the proof of
@lem:rank-one-root-subgroup-structure-equations, it is clear that we can choose
in each group $G'_i$ a fixed element $n'_i$ of length $1$, such that
$n'_i in N inter G'_i$ and $pi(n'_i)=s_i in S$. For each such element $n'_i$, we
clearly have
$ (n'_i,T) subset.eq T_i, $
<eq:rank-one-normalizer-torus-commutators>
where $(n'_i,T)$ is the set of commutators ${(n'_i,t),t in T}$. Moreover, the
elements $t'_i lr((u)):u in U_i^*$, defined by the structure equations
@lem:rank-one-root-subgroup-structure-equations involving $n'_i$, belong to the
subgroup $T_i$, for each $i$.

We recall that $E$ is generated by the commutative split semisimple algebra
$E_T=sum_(t in T) k a_t tilde.equiv k T$, and the elements
$a_(n'_i):1 lt.eq i lt.eq l$. We have
$ a_(n'_i)^2=sum_(u in U_i^*) a_(t'_i lr((u))) a_(n'_i) $
<eq:rank-one-hecke-generator-square>
for each $i$, by @prop:modular-hecke-basis-multiplication. For any left
$k G$-module $M$, the left action of $E_T$ on $"inv"_U M$ is the same as the
action of $k T$, by @prop:modular-hecke-basis-invariant-action, and we shall
frequently use this identification.

#proposition[
  Let $chi$ be a linear $k$-representation of $T$, and assume that
  $T_i subset.not.eq ker chi$ for some $i$, $1 lt.eq i lt.eq l$. Then
  $ sum_(u in U_i^*) chi(t'_i lr((u)))=0. $
]<prop:nontrivial-torus-character-structure-sum-zero>

#proof[
  #source(731)
  In this proof, $chi$ also denotes its restriction to $T_i$. Let us set
  $Y_i=k G'_i times.o_(k U_i) k_(U_i)
  tilde.equiv (1_(U_i))^(G'_i)$, and let $E'_i$ denote the modular Hecke algebra
  $("End"_(k G'_i) Y_i)^∘$, acting on $"inv"_(U_i) Y_i$ from the left, so that
  $k T_i$ acts in the same way as $sum_(t in T_i) k a_t$. For any linear
  character $psi$ of $T_i$, let
  $e_psi=abs(T_i)^(-1) sum_(t in T_i) psi(t^(-1))t in k T_i$ be the
  corresponding idempotent. In $"inv"_(U_i) Y_i$, consider the nonzero elements
  $
    m_1=e_chi lr((1 times.o 1)),
    quad m_2=a_(n'_i) e_(hat(chi))(1 times.o 1),
    quad m_0=m_1+c m_2
  $
  where $hat(chi)$ denotes the conjugate character $attach(chi, tl: s_i)$, and
  $c in k$ is an element to be determined later. The elements $m_0$, $m_1$, and
  $m_2$ all afford the linear representation $chi$ of $T_i$. Moreover, using
  @eq:rank-one-hecke-generator-square we obtain
  $ a_(n'_i) m_0=a_(n'_i) m_1+z_chi c m_2, $
  where $z_chi$ denotes the element $sum_(u in U_i^*) chi(t'_i lr((u)))$. Then
  $a_(n'_i) m_0$ and $a_(n'_i) m_1$ afford $hat(chi)$, assuming they are
  different from zero. In any case, it follows that if $chi !=hat(chi)$ then
  $z_chi=0$, proving the result in this case. Now assume that $chi=hat(chi)$,
  and suppose $z_chi !=0$. Then, setting $c=-z_chi^(-1)$, it is clear that
  $lr(chevron.l m_0 chevron.r)$ is a simple $E'_i$-submodule of
  $"inv"_(U_i) Y_i$, affording the linear character $chi$ of $T_i$, and such
  that $a_(n'_i) m_0=0$. Let $M=k G'_i m_0$, and let $tilde(M)$ be the quotient
  of $M$ by a maximal submodule not containing $m_0$. Then $tilde(M)$ is a
  simple $k G'_i$-module, and $lr(chevron.l tilde(m)_0 chevron.r)
  tilde.equiv lr(chevron.l m_0 chevron.r)$ as $E'_i$-modules, where $tilde(m)_0$
  is the image of $m_0$ in $tilde(M)$. By the calculation used in the proof of
  @prop:hecke-eigenline-opposite-unipotent-generation, we obtain
  $
    n'_i tilde(m)_0=-z_chi tilde(m)_0
    quad (mod "rad" k U_(-alpha_i) tilde(m)_0).
  $
  Moreover, $lr(chevron.l n'_i tilde(m)_0 chevron.r)$ is a line fixed by the
  Sylow group $U_(-alpha_i)$ in $G'_i$, and, by
  @th:simple-group-modules-unipotent-invariant-classification, it is the unique
  such line. We have $"rad" k U_(-alpha_i) tilde(m)_0 !=0$, otherwise
  $tilde(M)=lr(chevron.l tilde(m)_0 chevron.r)$ affords a nontrivial linear
  representation of $G'_i$, which is impossible since $G'_i$ is generated by
  $p$-groups. Moreover, $"rad" k U_(-alpha_i) tilde(m)_0$ is stable under the
  action of $k U_(-alpha_i)$, and hence $lr(chevron.l n'_i tilde(m)_0 chevron.r)
  subset.eq "rad" k U_(-alpha_i) tilde(m)_0$. It follows that
  $z_chi tilde(m)_0 in "rad" k U_(-alpha_i) tilde(m)$ which is a contradiction
  if $z_chi !=0$. This completes the proof.
]

#corollary[
  Let $lr(chevron.l m chevron.r)$ be a simple $E$-module, affording the linear
  representation $chi$ of $E_T tilde.equiv k T$. Then the eigenvalues of the
  generators $a_(n'_i)$ of $E$ are given by:
  $ a_(n'_i) m=mu_i m, quad "with" mu_i=0 quad "or" quad -1, $
  and $mu_i=0$ unless $T_i lt.eq ker chi$.
]<cor:modular-hecke-generator-eigenvalues>

#proof[
  Suppose $mu_i !=0$. Then
  $
    mu_i^2 m=a_(n'_i)^2 m
    =sum_(u in U_i^*) hat(chi)(a_(t'_i lr((u)))) mu_i m
  $
  by @eq:rank-one-hecke-generator-square, where $hat(chi)$ corresponds to the
  conjugate character $attach(chi, tl: s_i)$ as in the proof of
  @prop:nontrivial-torus-character-structure-sum-zero. Then $hat(chi)(a_t)=1$
  for all $t in T_i$, by @prop:nontrivial-torus-character-structure-sum-zero,
  and we obtain $mu_i=-1$, as required.
]

#source(732)
#definition[
  Let $lr(chevron.l m chevron.r)$ be a simple $E$-module, affording the linear
  representation $chi$ of $E_T tilde.equiv k T$. Then the data
  $ (chi,mu_1,dots,mu_l), $
  where $a_(n'_i) m=mu_i m$ for each $i$, is called the _weight_ of
  $lr(chevron.l m chevron.r)$.
]<def:modular-hecke-simple-module-weight>
#idx("Weight")

By @cor:modular-hecke-simple-modules-linear, every simple $E$-module is uniquely
determined by its weight. We next prove that every simple $E$-module occurs in
$"inv"_U Y$.

#theorem[
  Let $chi$ be a linear representation of $k T$, and let $mu_1,dots,mu_l$ be
  elements of $k$ satisfying the conditions of
  @cor:modular-hecke-generator-eigenvalues. Then $"inv"_U Y$ contains a simple
  $E$-module of weight $(chi,mu_1,dots,mu_l)$.
]<th:modular-hecke-all-weights-realized>

#proof[
  Let $I$ be the subset of $S$ consisting of the generators $s_i$ such that
  $T_i lt.eq ker chi$ and $mu_i=0$. Using
  @eq:rank-one-normalizer-torus-commutators, it can be proved that there exists
  a set of coset representatives $n_w in N:pi(n_w)=w in W_I$, for the parabolic
  subgroup $W_I lt.eq W$, with the property that for all $w,w' in W_I$, we have
  $ n_w n_(w') n_(w w')^(-1) in ker chi. $
  Let $n_0 in N$ be a representative of the element $w_0$ of maximal length in
  $W$. We then define
  $
    m=sum_(w in W_I) a_(n_w n_0) e_(n_w n_0) lr((chi))(1 times.o 1)
    in "inv"_U Y,
  $
  where for each $w in W_I$, $e_(n_w n_0) lr((chi))$ is a primitive idempotent
  in $k T$ affording the linear character $t arrow.r chi^(w w_0)$, so
  $chi^(w w_0)(t^(w w_0))=chi(t)$, $t in T$. Then $m$ is a nonzero element of
  $"inv"_U Y$ affording the linear character $chi$ of $T$. We shall prove that
  $lr(chevron.l m chevron.r)$ is a simple $E$-module with the required
  properties.

  First consider a generator $s_i in S-I$, and let $w in W_I$. Then
  $l(s_i w)>l(w)$, and hence $l(s_i w w_0)<l(w w_0)$. Using
  @prop:modular-hecke-basis-multiplication, it follows that
  $
    a_(n'_i) a_(n_w n_0) e_(n_w n_0) lr((chi))(1 times.o 1)
    =sum_(u in U_i^*) chi(t'_i lr((u))) a_(n_w n_0)
    e_(n_w n_0) lr((chi))(1 times.o 1).
  $
  Therefore $a_(n'_i) m=mu_i m$ where $mu_i=-1$ or $0$ according as
  $T_i lt.eq ker chi$ or $T_i subset.not.eq ker chi$, using
  @prop:nontrivial-torus-character-structure-sum-zero in the second case.

  Now let $s_i in I$, and choose a cross section $tilde(w)$ of the right cosets
  $lr(chevron.l s_i chevron.r) backslash W_I$, with the property that
  $l(s_i tilde(w))>l(tilde(w))$ for all $tilde(w)$. Then we obtain
  $
    a_(n'_i) a_(n_(tilde(w)) n_0) e_(n_(tilde(w)) n_0) lr((chi))(1 times.o 1)
    =-a_(n_(tilde(w)) n_0) e_(n_(tilde(w)) n_0) lr((chi))(1 times.o 1)
  $
  while
  $
    a_(n'_i) a_(n_(s_i tilde(w)) n_0)
    e_(n_(s_i tilde(w)) n_0) lr((chi))(1 times.o 1)
    =a_(n_(tilde(w)) n_0) e_(n_(tilde(w)) n_0) lr((chi))(1 times.o 1),
  $

  #source(733)
  because of @prop:modular-hecke-basis-multiplication and the choice of the
  coset representatives $n_w:w in W_I$. It follows that, in this case, we have
  $a_(n'_i) m=0$, completing the proof.
]

Combining our results, we have:

#theorem[
  There exists a bijection from the set of isomorphism classes $(M)$ of simple
  $k G$-modules, to the set of isomorphism classes $(lr(chevron.l m chevron.r))$
  of simple $E$-modules. These, in turn, are parametrized by the set of all
  weights ${(chi,mu_1,dots,mu_l)}$ where each $chi$ is a linear character of
  $T$, and the $mu_i$ are chosen arbitrarily from ${0,-1}$, subject to the
  condition that $mu_i !=0$ implies $T_i lt.eq ker chi$.
]<th:natural-characteristic-simple-module-weight-parametrization>

#proof[
  The fact that the simple $E$-modules are parametrized by the set of weights is
  immediate, from @cor:modular-hecke-generator-eigenvalues and
  @th:modular-hecke-all-weights-realized. It is also clear that the
  correspondence $M arrow.r "inv"_U M$ defines an injective map from the set of
  isomorphism classes of simple $k G$-modules to the set of isomorphism classes
  of simple $E$-modules, by
  @th:simple-group-modules-unipotent-invariant-classification. It remains to
  prove that it is surjective. By @th:modular-hecke-all-weights-realized, each
  simple $E$-module is isomorphic to a submodule $lr(chevron.l m chevron.r)$ of
  $"inv"_U Y$. Then the cyclic module $k G m lt.eq Y$ clearly has a simple
  quotient $M$ in which the image of $m$ is different from zero. By
  @th:simple-group-modules-unipotent-invariant-classification, it follows that
  $"inv"_U M tilde.equiv lr(chevron.l m chevron.r)$ as $E$-modules. This
  completes the proof.
]

#corollary[
  The number of isomorphism classes of simple $k G$-modules is exactly
  $sum_(I subset.eq S) abs(T/T_I)$, where, for each subset $I subset.eq S$,
  $T_I=lr(chevron.l T_i:s_i in I chevron.r)$.
]<cor:natural-characteristic-simple-module-count>

#proof[
  Let $(chi,mu_1,dots,mu_l)$ be a weight of a simple $E$-module, and set
  $I={s_i in S:mu_i=-1}$. Then $T_I lt.eq ker chi$. Conversely, for each linear
  representation $chi$ of $T$ such that $T_I lt.eq ker chi$, there exists one
  and only one simple $E$-module of weight $(chi,mu_1,dots,mu_l)$, where
  $mu_i=-1$ if and only if $s_i in I$. Since $T$ is an abelian $p'$-group, and
  $k$ is sufficiently large, the number of linear representations
  $chi:T arrow.r k^dot$ such that $T_I lt.eq ker chi$ is $abs(T/T_I)$, and the
  result follows.
]

#remark(numbered: true)[
  Let $G$ be a universal Chevalley group over the finite field $FF_q$ of
  characteristic $p$, and let $k$ be an extension field of $FF_q$, which is
  sufficiently large relative to $G$. In this case, it is easily checked that
  $ T=product_(i=1)^l T_i quad "(direct product)" $
  and
  $ abs(T_i)=q-1, quad 1 lt.eq i lt.eq l, $
  where $l$ is the rank of the $B N$-pair in $G$ (see Steinberg
  @bib:Steinberg1967). It follows that
  $ sum_(I subset.eq S) abs(T/T_I)=product_(i=1)^l lr((abs(T_i)+1))=q^l. $

  #source(734)
  This gives another proof of the result, due to Steinberg @bib:Steinberg1963,
  that the number of $p'$-classes in $G$ (and hence the number of nonisomorphic
  simple $k G$-modules) is equal to $q^l$.
]<rem:universal-chevalley-simple-module-count>

#remark(numbered: true)[
  Let $P_I$ be a standard parabolic subgroup of $G$, having the Levi
  decomposition $P_I=L_I V_I$ (see @th:split-bn-parabolic-levi-decomposition),
  and let $M$ be a simple $k G$-module. As in the characteristic zero theory,
  presented in §~@sec:cuspidal-characters, it is of interest to study the
  truncation of $M$ at $P_I$, which is the $k L_I$-module $"inv"_(V_I) M$. In
  the natural characteristic, we have the following result, which is stated here
  without proof:
]<rem:natural-characteristic-parabolic-truncation>
#idx("Truncation", target: [@rem:natural-characteristic-parabolic-truncation])

#theorem(title: [Smith @bib:Smith1982])[
  Then truncation $"inv"_(V_I) M$ is a simple $k L_I$-module, for all subsets
  $I subset.eq S$ and simple $k G$-modules $M$.
]<th:smith-simple-module-parabolic-truncation>


