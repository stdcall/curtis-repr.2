#import "main-defs.typ": *
#import "statements.typ": *

== Finite Groups with Split $B N$-Pairs
<sec:finite-groups-split-bn-pairs>

=== The Levi Decomposition
<ss:split-bn-pair-levi-decomposition>

Throughout this section, $p$ denotes a fixed prime number. For a finite group
$H$, we shall use the notation $O_p lr((H))$ to denote the unique maximal normal
$p$-subgroup of $H$.

#definition[
  A finite group $G$ is said to have a _split $B N$-pair of rank $n$ and
  characteristic $p$_ if the following conditions are satisfied:
  #case-list(
    numbering: "(i)",
    [#case[
      $G$ has a $B N$-pair of rank $n$ (see §~@ss:bruhat-decomposition) such
      that
      $ T=inter.big_(x in N) attach(B, tl: x), $
      where $T=B inter N$.
    ] <case:split-bn-torus-intersection>],
    [#case[
      There exists a normal subgroup $U ⊴ B$ such that
      $ B=U ⋊ T quad ("semidirect product"). $
    ] <case:split-bn-borel-semidirect-product>],
    [#case[
      #source(670)
      $U=O_p lr((B))$, and $T$ is an abelian $p'$-group.#footnote[
        Recall that a $p'$-group is a finite group whose order is prime to $p$.
      ]
    ] <case:split-bn-unipotent-radical-torus>],
  )
] <def:split-bn-pair>
#idx("Split BN-pair", target: [@def:split-bn-pair])

#remarks(numbered: false)[
  #case-list(
    numbering: "(a)",
    [#case[
      In the special case where $G$ has a split $B N$-pair of rank $0$, $G$ is
      simply a finite abelian $p'$-group, and we have $G=B=N=T$, and $U=1$.
    ] <case:split-bn-rank-zero>],
    [#case[
      The first condition, that $T=inter attach(B, tl: x)$, can always be
      achieved in a finite group with a $B N$-pair without altering the Borel
      subgroup $B$ or the Weyl group $W$ (see Bourbaki @bib:Bourbaki1968, Ex. 5,
      p. 47).
    ] <case:split-bn-saturated-torus-choice>],
  )
] <rem:split-bn-rank-zero-saturation>

The next result summarizes the properties of finite groups with split
$B N$-pairs, which we shall require throughout the rest of the chapter. We shall
continue to use the conventions introduced in §~@ss:bruhat-decomposition for
groups with $B N$-pairs. In particular, we let $dot(w) in N$ denote a coset
representative of an element $w$ in the Weyl group $W=N slash T$. We shall also
use the two-sided notation for conjugates:
$ attach(A, tl: a)=a A a^(-1), quad A^b=b^(-1) A b, $
and for subsets $A$ normalized by $T$, we shall write
$
  attach(A, tl: w)=attach(A, tl: dot(w)), quad A^w=A^(dot(w)),
  quad "for all" w in W.
$

Some additional notation is needed for finite groups with split $B N$-pairs, as
follows. Let ${G,B,U,N,T}$ be a finite group with a split $B N$-pair, as in
@def:split-bn-pair. By @th:bn-pair-weyl-coxeter-system, the Weyl group $W$ of
$G$ is a finite Coxeter group. By @th:finite-coxeter-geometric-representation,
we may identify $W$ with a finite g.g.r. in some euclidean space, associated
with a root system $Delta$. We may also assume that the set $S$ of distinguished
generators of $W$ is a set of fundamental reflections defined by a fundamental
set of roots $Pi$ in $Delta$. Further, let $Delta_(plus.minus)$ be the positive
and negative roots, respectively, determined by $Pi$, as in
§~@ss:finite-reflection-root-systems, and define $Delta_w^(plus.minus)$,
$w in W$, as in @def:reflection-length-inversions. Let $w_0$ be the unique
element of maximal length in $W$ (see
@th:reflection-length-cancellation-exchange), and let $U^-=U^(w_0)$. For each
$w in W$, set
$ U_w^+=U inter U^w, quad U_w^-=U inter U^(w_0 w). $
Then $U_w^+={u in U:attach(u, tl: dot(w)) in U}$,
$U_w^-={u in U:attach(u, tl: dot(w)) in U^-}$. Note in particular that
$U=U_(w_0)^-$.

Now let $Pi={alpha_1,dots,alpha_n}$ and $S={s_1,dots,s_n}$, where
$s_i=s_(alpha_i)$ for each $i$. We may then define subgroups ${U_(alpha_i)}$ by
the formula
$ U_(alpha_i)=U inter U^(w_0 s_i), quad 1<=i<=n. $
In the next result, a root structure is introduced in $G$, consisting of
subgroups ${U_alpha}$ on which the Weyl group of $G$ acts in the same way that
$W$ acts on the roots in $Delta$.

#source(671)
#proposition[
  Let ${G,B,N,U,T}$ be a finite group with a split $B N$-pair of rank $n$ and
  characteristic $p$, and let $(W,S)$ be the Coxeter system in the Weyl group
  $W$ of $G$, as above. Then the following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[$U^- inter B=1$.] <case:split-bn-opposite-unipotent-disjoint>],
    [#case[
      $U=U_w^- U_w^+$ and $U_w^- inter U_w^+=1$, for all $w in W$.
    ] <case:split-bn-unipotent-inversion-factorization>],
    [#case[
      There exists a bijection $alpha arrow U_alpha$ from the root system
      $Delta$ to the set of conjugates
      ${attach(U_(alpha_i), tl: x):x in N,alpha_i in Pi}$, which extends the map
      $alpha_i arrow U_(alpha_i)$, $alpha_i in Pi$. For all $w in W$ and
      $alpha in Delta$, we have
      $ attach(U_alpha, tl: dot(w))=U_(w(alpha)). $
    ] <case:split-bn-root-group-weyl-action>],
    [#case[
      For each $w in W$, there exists an ordering ${beta_1,beta_2,dots}$ of the
      roots in $Delta_w^-$ such that
      $ U_w^-=U_(beta_1) U_(beta_2) dots, $
      with uniqueness of expression. A similar statement holds for $Delta_w^+$
      and $U_w^+$. In particular, $U_w^(plus.minus)=lr(
        chevron.l U_alpha:
        alpha in Delta_w^(plus.minus) chevron.r
      )$.
    ] <case:split-bn-ordered-root-factorization>],
    [#case[
      (Sharp form of the Bruhat decomposition.) Let ${dot(w)}_(w in W)$ denote a
      fixed cross section of $W=N slash T$. Then
      $ B w B=B w U_w^- quad "for each" w in W. $
      Moreover, $G=union.dot.big_(w in W) B w U_w^-$, and each element of $G$
      can be written uniquely in the form $b dot(w) u$, with $b in B$, $w in W$,
      and $u in U_w^-$, for $dot(w)$ in the fixed cross section of $N slash T$.
    ] <case:split-bn-sharp-bruhat-decomposition>],
    [#case[
      For each $i$, $U_(alpha_i) T union U_(alpha_i) T dot(s)_i U_(alpha_i)$ is
      a subgroup of $G$.
    ] <case:split-bn-rank-one-root-subgroup>],
  )
] <prop:split-bn-root-subgroup-properties>
#idx(
  "Bruhat decomposition",
  target: [@case:split-bn-sharp-bruhat-decomposition],
)

We do not prove @prop:split-bn-root-subgroup-properties here. We shall assume,
in what follows, that all finite groups with split $B N$-pairs satisfy
@prop:split-bn-root-subgroup-properties,
parts~@case:split-bn-opposite-unipotent-disjoint–#(
  [@case:split-bn-rank-one-root-subgroup]
), together with

#case-list(start: 7, numbering: "(i)", [#case[
  *(Commutator Formula)* Let $alpha,beta$ be linearly independent roots.
  Then#footnote[
    For subsets $A,B$ of a group, we let $(A,B)$ denote the set of all
    commutators $(a,b)=a b a^(-1) b^(-1)$, $a in A$, $b in B$.
  ]
  $ (U_alpha,U_beta) subset.eq product U_(i alpha+j beta), $
  where the product is taken (in some order) over the set of all roots which can
  be expressed in the form $i alpha+j beta$, $i,j>0$.
] <case:split-bn-root-commutator-formula>])

#remarks(numbered: false)[
  The statements @prop:split-bn-root-subgroup-properties,
  parts~@case:split-bn-opposite-unipotent-disjoint–#(
    [@case:split-bn-root-commutator-formula]
  ), are standard properties of Chevalley groups and twisted types of Chevalley
  groups (see Chevalley @bib:Chevalley1955, Carter @bib:Carter1972b, and
  Steinberg @bib:Steinberg1967). They also hold for the finite groups $G(FF_q)$,
  consisting of $FF_q$-rational points on a connected reductive affine algebraic
  group defined over
  #source(672)
  $FF_q$ (see Borel–Tits @bib:Borel1965). The statements
  @prop:split-bn-root-subgroup-properties,
  parts~@case:split-bn-opposite-unipotent-disjoint–#(
    [@case:split-bn-rank-one-root-subgroup]
  ), can be proved in an elementary way from the axioms for split $B N$-pairs
  (see Richen @bib:Richen1969). The commutator formula
  @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-root-commutator-formula, can also be proved from the
  axioms, with some exceptions in case $p=2$ that do not occur as Chevalley
  groups (see Fong–Seitz @bib:Fong1973, @bib:Fong1974; Tinberg
  @bib:Tinberg1980a).
] <rem:split-bn-root-properties-scope>

#example(numbered: false)[
  In order to give the reader a better understanding of
  Proposition~@prop:split-bn-root-subgroup-properties, we shall verify
  properties @case:split-bn-opposite-unipotent-disjoint–#(
    [@case:split-bn-root-commutator-formula]
  ) for the finite general linear groups, by methods that are typical of the
  proofs of these facts for Chevalley groups. Some details are omitted.
] <exm:general-linear-root-subgroups-introduction>

#proposition[
  Let $FF_q$ be a finite field of characteristic $p$, and $n$ a positive
  integer. The general linear group $G=GL_(n+1) lr((FF_q))$ has a split
  $B N$-pair of rank $n$ and characteristic $p$, and satisfies the conditions
  stated in Proposition~@prop:split-bn-root-subgroup-properties.
] <prop:general-linear-split-bn-pair>
#proof[
  We keep the notation introduced in the proof of
  Theorem~@th:general-linear-bn-pair, where we showed that $G$ has a $B N$-pair
  of rank $n$. In addition to the groups $B,N$, and $T$ defined previously, let
  $
    U="group of upper unit triangular matrices"
    ={(a_(i j)) in B:a_(i i)=1 "for each" i}
  $
  $ U^-="group of lower unit triangular matrices". $
  Since $char FF_q=p$, $U$ is a $p$-group, $T$ is an abelian $p'$-group, and it
  is easily checked that $B$ is a semidirect product $B=U ⋊ T$. Thus $G$
  satisfies @case:split-bn-borel-semidirect-product and
  @case:split-bn-unipotent-radical-torus of @def:split-bn-pair.

  As in the proof of @th:general-linear-bn-pair, let ${e_1,dots,e_(n+1)}$ be a
  basis for the vector space on which $G$ acts, and let $phi:N arrow S_(n+1)$ be
  the homomorphism defined by setting $phi(x)=sigma in S_(n+1)$, where
  $
    x lr(chevron.l e_i chevron.r)=lr(chevron.l e_(sigma(i)) chevron.r),
    quad 1<=i<=n+1.
  $
  The map $phi$ identifies the Weyl group $N slash T$ of $G$ with $S_(n+1)$,
  since $ker phi=T$. For $1<=i<=n$, let $dot(s)_i$ be the element of $N$ that
  interchanges $e_i$ and $e_(i+1)$ and fixes the other basis vectors. Then
  $phi(dot(s)_i)=(i,i+1)$, so $phi$ identifies the distinguished generators
  ${s_i}$ of $N slash T$ with the transpositions ${(i,i+1)}$.

  Now consider the root system $Delta$ associated with $S_(n+1)$, defined in
  Exercise~@exc:type-a-root-system. Then $Delta$ consists of the vectors
  ${epsilon_i-epsilon_j:i != j,1<=i,j<=n+1}$, in a euclidean space with an
  orthonormal basis given by ${epsilon_1,dots,epsilon_(n+1)}$. The elements of
  $S_(n+1)$ permute the basis vectors ${epsilon_i}$, and hence permute the
  roots. Let
  $
    Pi={alpha_1,dots,alpha_n}, quad "where"
    alpha_i=epsilon_i-epsilon_(i+1), quad 1<=i<=n.
  $
  By Exercise~@exc:type-a-root-system, $Pi$ is a fundamental system in $Delta$,
  and the fundamental reflections ${s_(alpha_i)}_(1<=i<=n)$ can be identified
  with the transpositions ${(i,i+1),1<=i<=n}$ considered above. Let
  $Delta_(plus.minus)$ be the positive (resp. negative) roots in $Delta$ defined
  by the set $Pi$.

  #source(673)
  We now carry over the root system $Delta$ to the finite group $G$ as follows.
  For each root $alpha=epsilon_i-epsilon_j in Delta$, let $U_alpha$ be the
  subgroup of $G$ consisting of all elementary matrices
  $
    x_alpha lr((t))=E_(i j) lr((t))=bold(I)+t bold(e)_(i j),
    quad t in FF_q,
  $
  (see @eq:elementary-matrix-definition). We clearly have
  $
    U=lr(chevron.l U_alpha:alpha in Delta_+ chevron.r)
    quad "and" quad U^-=lr(chevron.l U_alpha:alpha in Delta_- chevron.r).
  $ <eq:general-linear-positive-negative-root-groups>

  The subgroups ${U_alpha}_(alpha in Delta)$ are normalized by $T$ and permuted
  under conjugation by the elements of $N$. An easy calculation shows that if
  $phi(x)=sigma in S_(n+1)$, then
  $ attach(U_alpha, tl: x)=U_(sigma alpha) quad "for all" x in N. $
  Using the isomorphism $N slash T tilde.equiv S_(n+1)$, we can rewrite this
  formula as
  $
    attach(U_alpha, tl: dot(w))=U_(w alpha), quad w in W, quad alpha in Delta.
  $ <eq:general-linear-root-group-conjugation>

  Let $w_0$ be the element of maximal length in $W$. Then $w_0 Delta_+=Delta_-$
  by @th:reflection-length-cancellation-exchange,
  part~@case:longest-reflection-group-element, and it follows that
  $U^-=U^(w_0)$, using @eq:general-linear-positive-negative-root-groups and
  @eq:general-linear-root-group-conjugation. Since $U inter U^-=1$, we have
  $
    inter.big_(x in N) attach(B, tl: x) <= B inter B^(w_0)
    =U T inter U^- T=T,
  $
  proving @def:split-bn-pair, part~@case:split-bn-torus-intersection. We also
  have $B inter U^-=1$, and $U_w^- inter U_w^+=1$ since
  $attach((U_w^- inter U_w^+), tl: w) <= U^- inter U=1$. Another application of
  @eq:general-linear-root-group-conjugation shows that
  $U_(alpha_i)=U inter U^(w_0 s_i)$, $1<=i<=n$, completing the proof of
  @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-root-group-weyl-action.

  We leave it to the reader to check @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-rank-one-root-subgroup, as well as the formula
  $
    (U_alpha,U_beta)=cases(
      1 & "if" alpha+beta in.not Delta,
      U_(alpha+beta) & "if" alpha+beta in Delta,
    )
  $ <eq:general-linear-root-commutators>

  for all roots $alpha,beta$ such that $beta != plus.minus alpha$. This implies
  @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-root-commutator-formula.

  The remaining parts of @prop:split-bn-root-subgroup-properties are proved
  using @eq:general-linear-root-commutators, as follows. First consider the
  structure of $U=U_(w_0)^-$. Let $m=abs(Delta_+)$, and let
  ${beta_1,dots,beta_m}$ be the positive roots arranged in order of increasing
  height (see @def:positive-root-height). Note that if $i<j$, then
  $op("ht")(epsilon_i-epsilon_j)=j-i$. We claim now that
  $ U=U_(beta_1) dots U_(beta_m). $
  For each $i>=0$, let $U_i$ denote the subgroup of $U$ generated by all root
  subgroups ${U_beta:beta in Delta_+,op("ht") beta>=i}$. Then $U_i ⊴ U$ for each
  $i$, by @eq:general-linear-root-commutators. It is now readily shown, using
  @eq:general-linear-root-commutators and decreasing induction on $i$, that for
  each $i>=0$ we have
  $ U_i=U_(beta_j) U_(beta_(j+1)) dots U_(beta_m) $
  #source(674)
  where the notation is chosen so that ${beta_j,dots,beta_m}$ are the positive
  roots of height $>=i$. Setting $i=0$, we obtain the desired result.

  A similar argument shows that for each $w in W$, we have
  $
    U=U_w^- U_w^+,
  $ <eq:general-linear-unipotent-factorization>

  where $U_w^(plus.minus)=lr(
    chevron.l U_alpha:
    alpha in Delta_w^(plus.minus) chevron.r
  )$ as in @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-ordered-root-factorization. The factorization
  @eq:general-linear-unipotent-factorization is proved by showing that
  $ U_i=(U_i inter U_w^-)(U_i inter U_w^+) $
  using decreasing induction on $i$. From
  @eq:general-linear-unipotent-factorization and
  @eq:general-linear-root-group-conjugation, we obtain the alternative
  description
  $ U_w^-=U inter U^(w_0 w), quad U_w^+=U inter U^w. $
  In particular, we have $U_w^+=U_(w_0 w)^-$. The product formula
  $ U_w^-=U_(gamma_1) dots U_(gamma_t), $
  for some ordering of the roots $gamma_i in Delta_w^-$, is proved in the same
  way as for $U$. The uniqueness of expression in the factorization of $U_w^-$
  follows by induction on $l(w)$, since
  $
    U_(w s_i)^-=U_(alpha_i) attach(U_w^-, tl: s_i)
    quad "and" quad U_(alpha_i) inter attach(U_w^-, tl: s_i)=1
    quad "if" l(w s_i)>=l(w).
  $ <eq:unipotent-inversion-root-step>

  This result follows, in turn, from the formula
  $Delta_(w s_i)^-={alpha_i} union.dot s_i lr((Delta_w^-))$ if $l(w s_i)>=l(w)$
  (see the proof of @th:reflection-length-cancellation-exchange,
  part~@case:inversion-simple-reflection-change), and the fact that
  $attach((U_(alpha_i) inter attach(U_w^-, tl: s_i)), tl: s_i)
  <= U_(-alpha_i) inter U_w^- <= U^- inter U=1$.

  It remains to prove @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-sharp-bruhat-decomposition. Since $G$ has a $B N$-pair by
  @th:general-linear-bn-pair, we have
  $ G=union.dot.big_(w in W) B dot(w) B. $
  Now let $w in W$, and consider $B dot(w) B$. Since $B=T U$ and $U=U_w^+ U_w^-$
  by @eq:general-linear-unipotent-factorization, we have
  $ B dot(w) B=B dot(w) T U_w^+ U_w^-=B dot(w) U_w^- $
  since $dot(w) T U_w^+ dot(w)^(-1)<=B$. Now let
  $ g=b dot(w)u=b' dot(w)u' $
  be two expressions of an element $g in B dot(w) B$, with $b,b' in B$ and
  $u,u' in U_w^-$. Then
  $ (b')^(-1)b=dot(w)u' u^(-1) dot(w)^(-1) in B inter U^-=1 $
  by @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-opposite-unipotent-disjoint, and hence $b=b'$, $u=u'$.
  This completes the proof of the proposition.
]

#source(675)
Returning to the general discussion, we have:

#proposition[
  Let $G$ be a finite group with a split $B N$-pair of rank $n$ and
  characteristic $p$. Then the following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[
      $abs(G)=abs(U)abs(T)sum_(w in W) abs(U_w^-)$, where $W$ is the Weyl group
      of $G$.
    ] <case:split-bn-group-order>],
    [#case[$U$ is a Sylow $p$-subgroup of $G$.]
      <case:split-bn-unipotent-sylow>],
    [#case[$O_p lr((G))=1$.] <case:split-bn-p-core-trivial>],
    [#case[
      $upright("St")_G lr((1))=abs(G)_p$, where $upright("St")_G$ is the
      Steinberg character of $G$ (see §~@ss:hecke-sign-steinberg).
    ] <case:split-bn-steinberg-p-part-degree>],
  )
] <prop:split-bn-pair-order-sylow-steinberg>
#idx(
  "Steinberg representation",
  target: [@case:split-bn-steinberg-p-part-degree],
)

The proof is left as an exercise for the reader. Part~@case:split-bn-group-order
is an application of @prop:split-bn-root-subgroup-properties,
part~@case:split-bn-sharp-bruhat-decomposition, and implies
part~@case:split-bn-unipotent-sylow, using the fact that $abs(U_w^-)$ is a power
of $p$ for all $w$, and is $1$ if and only if $w=1$.

#remark(numbered: false)[
  Part~@case:split-bn-p-core-trivial of
  @prop:split-bn-pair-order-sylow-steinberg is the exact counterpart, in finite
  group theory, of the condition that an affine algebraic group $G$ be
  _reductive_, namely $R_u lr((G))=1$, where $R_u lr((G))$ is the unipotent
  radical of $G$ (see Carter @bib:Carter1985).
] <rem:split-bn-reductivity-analogy>

We are now ready to prove the main result of this section.#footnote[
  The reader will find it profitable to compare the proof given below, based on
  @prop:split-bn-root-subgroup-properties, with a proof of the theorem for
  Chevalley groups (see Carter @bib:Carter1972b).
] The statement involves notation introduced earlier in this section and in
§§~@ss:finite-coxeter-parabolic-subgroups and @ss:bn-pair-parabolic-subgroups.
In particular, for $J subset.eq S$, $Delta_J$ denotes the root system associated
with the parabolic subgroup $W_J$ of $W$.

#theorem[
  Let $G$ be a finite group with a split $B N$-pair of characteristic $p$, let
  $(W,S)$ be the Weyl group of $G$, with distinguished generators $S$, and let
  $P_J$ be a standard parabolic subgroup of $G$, for some subset $J$ of $S$.
  Define
  $
    L_J=lr(chevron.l T, U_alpha ":" alpha in Delta_J chevron.r),
    quad V_J=lr(chevron.l U_beta:beta in Delta_+-Delta_(J,+) chevron.r).
  $
  Then we have:
  #case-list(
    numbering: "(i)",
    [#case[$P_J=V_J ⋊ L_J$ (semidirect product).]
      <case:split-parabolic-levi-semidirect-product>],
    [#case[$V_J=O_p lr((P_J))$.] <case:split-parabolic-p-core>],
    [#case[$P_J=N_G lr((V_J))$.] <case:split-parabolic-unipotent-normalizer>],
    [#case[
      $L_J$ is a finite group with a split $B N$-pair of characteristic $p$,
      with Borel subgroup $B inter L_J$, and Weyl group $W_J$.
    ] <case:standard-levi-split-bn-pair>],
  )
] <th:split-bn-parabolic-levi-decomposition>

We first require some additional properties of root systems.

#lemma[
  For $J subset S$, let $w_J$ denote the element of maximal length in the
  Coxeter group $W_J$. Then we have:
  #case-list(
    numbering: "(i)",
    [#case[
      $Delta_(J,+)=Delta_(w_J)^-$, $Delta_+-Delta_(J,+)=Delta_(w_J)^+$ where
      $Delta_(J,+)=Delta_J inter Delta_+$.
    ] <case:parabolic-longest-inversion-roots>],
    [#case[
      #source(676)
      Let $alpha in Delta_(w_J)^+$, $beta in Delta_J$, and suppose that
      $i alpha+j beta in Delta$, where $i,j>0$. Then
      $i alpha+j beta in Delta_(w_J)^+$.
    ] <case:parabolic-unipotent-root-closure>],
  )
] <lem:parabolic-longest-positive-root-complement>

#proof[
  #case-list(
    numbering: "(i)",
    [#case[
      This is easily proved from the definitions (see
      @def:reflection-length-inversions and @prop:parabolic-root-subsystem) and
      is left as an exercise.
    ] <case:parabolic-root-complement-proof>],
    [#case[
      By part~@case:parabolic-longest-inversion-roots,
      $alpha in Delta_+-Delta_(J,+)$. Since $beta in Delta_J$, and $i,j>0$, it
      follows that $i alpha+j beta$ is a linear combination of fundamental
      roots, in which some fundamental root not in $Pi_J$ appears with a
      positive coefficient. Then $i alpha+j beta in Delta_+$, by
      @th:fundamental-root-basis, and moreover
      $i alpha+j beta in Delta_+-Delta_(J,+)$, completing the proof.
    ] <case:parabolic-unipotent-closure-proof>],
  )
]

#proof(head: emph[Proof of Theorem~@th:split-bn-parabolic-levi-decomposition.])[
  First let $J=emptyset$. Then $L_J=T$, $V_J=U$, and
  @case:split-parabolic-levi-semidirect-product, @case:split-parabolic-p-core,
  and @case:standard-levi-split-bn-pair hold by definition of a split
  $B N$-pair. We have $N_G lr((U))>=B$, and must have equality; otherwise,
  $N_G lr((U))$ contains $dot(s)$ for some $s in S$, by
  @th:bn-pair-overgroups-borel, which is impossible since
  $attach(U, tl: s) != U$ by @prop:split-bn-root-subgroup-properties. Thus
  @case:split-parabolic-unipotent-normalizer holds, and the theorem is proved in
  this case.

  Now assume $J != emptyset$; then $V_J<=U_(w_J)^+$ by
  @lem:parabolic-longest-positive-root-complement,
  part~@case:parabolic-longest-inversion-roots, and by
  @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-ordered-root-factorization we have equality. Next, by
  @lem:parabolic-longest-positive-root-complement,
  part~@case:parabolic-unipotent-root-closure and the commutator formulas
  @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-root-commutator-formula, it follows that $L_J$ normalizes
  $V_J$. Using the Bruhat decomposition of $P_J$ together with the facts that
  $B dot(w)B=B dot(w)U_w^-$ and $U=U_w^+ U_w^-$, $w in W$ (by
  @prop:split-bn-root-subgroup-properties,
  parts~@case:split-bn-sharp-bruhat-decomposition and
  @case:split-bn-unipotent-inversion-factorization), we obtain
  $
    P_J=union.big_(w in W_J) U T dot(w)U_w^-
    =union.big_(w in W_J) V_J U_(w_J)^- T dot(w)U_w^-.
  $ <eq:split-parabolic-root-coset-factorization>

  We now verify that the coset representatives ${dot(w):w in W_J}$ belong to
  $L_J$. By @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-rank-one-root-subgroup,
  $U_(alpha_i)T union U_(alpha_i)T dot(s)_i U_(alpha_i)$ is a group, and hence
  contains $U_(-alpha_i)=attach(U_(alpha_i), tl: s_i)$. Moreover
  $U_(-alpha_i) subset.not U_(alpha_i) T$ by
  @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-opposite-unipotent-disjoint, and it follows that
  $ U_(-alpha_i) inter U_(alpha_i)T dot(s)_i U_(alpha_i) != emptyset. $
  Thus $v=u' t dot(s)_i u''$ for some $v in U_(-alpha_i)$,
  $u',u'' in U_(alpha_i)$, $t in T$. Solving for $dot(s)_i$, we obtain
  $ dot(s)_i in lr(chevron.l U_(alpha_i), U_(-alpha_i), T chevron.r). $
  Therefore $dot(s)_i in L_J$ if $s_i in J$, and since any element $w in W_J$ is
  a product of elements of $J$, we have shown that $dot(w) in L_J$ for all
  $w in W_J$. The subgroups $U_w^-$, for $w in W_J$, also are contained in
  $L_J$, since
  $U_w^-=lr(chevron.l U_alpha:alpha in Delta_w^- chevron.r)$
  (@prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-ordered-root-factorization), and
  $Delta_w^- subset.eq Delta_J$ if $w in W_J$ (see
  Exercise~@exc:parabolic-inversion-root-subsystem). Thus
  @eq:split-parabolic-root-coset-factorization implies that $P_J<=V_J L_J$.

  We next prove that $L_J$ has a $B N$-pair with subgroups $B',N'$, where
  $B'=U_(w_J)^- T$, $N'=lr(chevron.l T, dot(w):w in W_J chevron.r)$. The axioms
  are all easily verified except for showing that
  $
    s_i B' w subset.eq B' w B' union B' s_i w B',
    quad s_i in J, quad w in W_J.
  $
  This is proved as follows. Let $w_J=w' s_i$, $w' in W_J$, $l(w')=l(w_J)-1$.
  Then $Delta_(w_J)^-={alpha_i} union.dot s_i lr((Delta_(w')^-))$, and by the
  proof of @eq:unipotent-inversion-root-step we have
  $U_(w_J)^-=attach(U_(w')^-, tl: s_i) U_(alpha_i)$ so
  $
    s_i B'w=T U_(w')^- dot(s)_i U_(alpha_i)dot(w)
    subset.eq B' dot(s)_i U_(alpha_i)dot(w).
  $
  #source(677)
  If $w^(-1)alpha_i in Delta_+$, then by
  @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-root-group-weyl-action,
  $dot(w)^(-1)U_(alpha_i)dot(w)=U_(w^(-1)(alpha_i)) subset.eq B'$, and
  $ s_i B'w subset.eq B's_i w B' $
  in this case. Now assume $w^(-1)alpha_i in Delta_-$; then we have
  $
    s_i B'w subset.eq B'U_(-alpha_i)s_i dot(w)
    subset.eq B's_i w B' union B's_i U_(alpha_i)s_i w
  $
  since, as we noted above, $U_(-alpha_i)$ is contained in the group defined in
  @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-rank-one-root-subgroup. The second expression becomes
  $
    B'w w^(-1)s_i U_(alpha_i)s_i w
    subset.eq B'w U_(w^(-1)s_i alpha_i) subset.eq B'w B',
  $
  since $w^(-1)s_i alpha_i in Delta_+$, in this case. This completes the proof
  that $L_J$ has a $B N$-pair. An easy argument, again using
  @prop:split-bn-root-subgroup-properties, shows that $L_J$ has a split
  $B N$-pair of characteristic $p$, with $U_(w_J)^-=O_p lr((B'))$.

  The sharp form of the Bruhat decomposition of $L_J$ becomes
  $
    L_J=union.big_(w in W_J) U_(w_J)^- T dot(w)U_w^-.
  $ <eq:standard-levi-sharp-bruhat-decomposition>

  Then @eq:split-parabolic-root-coset-factorization asserts that $P_J=L_J V_J$.
  Moreover, $B inter L_J=U_(w_J)^- T$ by
  @eq:standard-levi-sharp-bruhat-decomposition combined with the Bruhat
  decomposition in $G$, so that
  $
    L_J inter V_J <= (L_J inter B)inter V_J
    =U_(w_J)^- T inter U_(w_J)^+=1
  $
  by @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-unipotent-inversion-factorization, and
  @case:split-parabolic-levi-semidirect-product is proved.

  We next prove @case:split-parabolic-p-core. Since $V_J<=U$ and $P_J=L_J V_J$
  by @case:split-parabolic-levi-semidirect-product, we have
  $V_J<=O_p lr((P_J))$. On the other hand, $O_p lr((P_J))<=U$, since $U$ is a
  Sylow $p$-subgroup of $P_J$, by @prop:split-bn-pair-order-sylow-steinberg,
  part~@case:split-bn-unipotent-sylow. Let $u in O_p lr((P_J))$; then by
  @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-unipotent-inversion-factorization, we have $u=u'u''$, with
  $u' in V_J$, $u'' in U_(w_J)^-$. Then
  $
    attach(u, tl: w_J) in O_p lr((P_J))<=U,
    quad attach(u, tl: w_J)=attach(u', tl: w_J)attach(u'', tl: w_J)
    in V_J dot attach(U_(w_J)^-, tl: w_J).
  $
  Since $attach(U_(w_J)^-, tl: w_J)<=U^-$, and $U inter U^-=1$, it follows that
  $u''=1$ and $u in V_J$, completing the proof of @case:split-parabolic-p-core.

  #case-list(start: 3, numbering: "(i)", [#case[
    By part~@case:split-parabolic-levi-semidirect-product, we have
    $P_J<=N_G lr((V_J))$. If the inclusion were proper, then
    $N_G lr((V_J))=P_(J')$, for some $J' supset.eq J$, by
    @th:bn-pair-overgroups-borel and @prop:bn-pair-parabolic-lattice. We would
    then have $attach(V_J, tl: w_(J'))=V_J$, which is impossible, since $V_J$
    contains $U_alpha$ for some $alpha in Delta_(w_(J'))^-$ if $J' != J$, and
    $attach(U_alpha, tl: w_(J'))<=U^-$, by
    @prop:split-bn-root-subgroup-properties,
    part~@case:split-bn-root-group-weyl-action. Thus $N_G lr((V_J))=P_J$, and
    @case:split-parabolic-unipotent-normalizer is proved. Since
    @case:standard-levi-split-bn-pair has already been proved, the theorem is
    established.
  ] <case:split-parabolic-normalizer-proof>])
]

#definition[
  Let $G$ be as in Theorem~@th:split-bn-parabolic-levi-decomposition, and let
  $J subset.eq S$. The semidirect product decomposition $P_J=L_J V_J$ is called
  a _Levi decomposition_ of $P_J$, and the subgroup $L_J$ is called a _standard
  Levi factor_ of $P_J$.
] <def:split-parabolic-levi-decomposition>
#idx("Levi decomposition", target: [@def:split-parabolic-levi-decomposition])

#source(678)
The Levi decomposition is of fundamental importance in the representation theory
of $G$, since questions about representations and characters of $G$ can often be
reduced to the corresponding questions for Levi subgroups, which are themselves
groups with $B N$-pairs of lower rank than $G$.

=== Intersections of Parabolic Subgroups
<ss:split-bn-pair-parabolic-intersections>

Throughout this subsection, the following notation will be used.
#reference-list(
  [$G=$],
  [a finite group with a split $B N$-pair of characteristic $p$],
  [$B=$],
  [a Borel subgroup of $G$],
  [$U=O_p lr((B))$],
  [],
  [$W=$],
  [the Weyl group of $G$],
  [$S={s_1,dots,s_n}=$],
  [the distinguished generators of $W$],
  [$Pi={alpha_1,dots,alpha_n}=$],
  [a set of fundamental roots in the root system associated with $W$, such that
    $s_i arrow.l.r s_(alpha_i)$, $1<=i<=n$.],
)

Let $J_1,J_2 subset.eq S$, and let $P_(J_1),P_(J_2)$ be the corresponding
standard parabolic subgroups of $G$, as in §~@ss:bn-pair-parabolic-subgroups. In
§§~@sec:cuspidal-characters, @sec:character-duality we shall have to calculate
$(phi_1^G,phi_2^G)$, for $phi_1 in op("ch") CC P_(J_1)$,
$phi_2 in op("ch") CC P_(J_2)$. In order to apply the Intertwining Number
Theorem~@i:th:intertwining-number, we require information about the
intersections $P_(J_1) inter attach(P_(J_2), tl: x)$, $x in G$. In contrast to
the situation for finite Coxeter groups (see
@th:parabolic-subgroup-intersection), the intersection
$P_(J_1) inter attach(P_(J_2), tl: x)$ is not always a parabolic subgroup. In
this subsection, we determine these intersections explicitly.

We shall make frequent use of the notation and results from
§§~@ss:split-bn-pair-levi-decomposition, @ss:finite-coxeter-parabolic-subgroups,
and @ss:bn-pair-parabolic-subgroups. In particular, for $J subset.eq S$ we set:
#reference-list(
  [$W_J=lr(chevron.l J chevron.r)$],
  [a parabolic subgroup of $W$],
  [$Delta_J,Pi_J=$],
  [the root system, and fundamental roots, associated with $W_J$ (see
    @prop:parabolic-root-subsystem)],
  [$Delta_(J,+)=Delta_+ inter Delta_J$],
  [where $Delta_+$ is the set of positive roots containing $Pi$],
  [$w_J=$],
  [the unique element of maximal length in $W_J$],
  [$P_J=L_J V_J=$],
  [the Levi decomposition of $P_J$ (see
    @th:split-bn-parabolic-levi-decomposition).],
)

The following results were proved in the context of reductive algebraic groups
defined over finite fields by Borel–Tits @bib:Borel1965, Harish-Chandra
@bib:HarishChandra1970, and Springer @bib:Springer1975. Their adaptations to
finite groups with split $B N$-pairs were given by Curtis @bib:Curtis1975.

#proposition[
  Let $J subset.eq S$. For all subsets $J' subset.eq J$, $P_(J') inter L_J$ is a
  standard parabolic subgroup of $L_J$ (containing the Borel subgroup
  $B inter L_J$ of $L_J$). Moreover,
  $ O_p lr((P_(J') inter L_J))=V_(J') inter L_J, $
  and $P_(J') inter L_J$ has a Levi decomposition
  $ P_(J') inter L_J=L_(J')(V_(J') inter L_J), $
  and $V_(J')=(V_(J') inter L_J)V_J$. The map $P_(J') arrow P_(J') inter L_J$
  gives a bijection from the set of
  #source(679)
  standard parabolic subgroups ${P_(J')}_(J' subset.eq J)$ of $G$ to the set of
  all standard parabolic subgroups of $L_J$.
] <prop:standard-levi-parabolic-correspondence>
#idx(
  "Parabolic subgroups",
  target: [@prop:standard-levi-parabolic-correspondence],
)

#proof[
  By @th:split-bn-parabolic-levi-decomposition,
  part~@case:standard-levi-split-bn-pair, $B inter L_J$ is a Borel subgroup of
  $L_J$. Now let $J' subset.eq J$. Then $P_(J')>=B$, and
  $P_(J') inter L_J>=B inter L_J$, so $P_(J') inter L_J$ is a standard parabolic
  subgroup of $L_J$. By the definition in
  @th:split-bn-parabolic-levi-decomposition, $L_(J')$ is a standard Levi factor
  of $P_(J') inter L_J$. Since $V_J<=V_(J')$, the Levi decomposition
  $P_J=L_J V_J$ implies that $V_(J')=(V_(J') inter L_J)V_J$. Then
  $P_(J')=L_(J') V_(J')=L_(J')(V_(J') inter L_J)V_J$. It is easily seen that
  $V_(J') inter L_J=O_p lr((P_(J') inter L_J))$, and hence
  $L_J inter P_(J')=L_(J')(V_(J') inter L_J)$ is a Levi decomposition of
  $L_J inter P_(J')$.

  Now let $J',J'' subset.eq J$, and suppose
  $P_(J') inter L_J=P_(J'') inter L_J$. Then
  $O_p lr((P_(J') inter L_J))=O_p lr((P_(J'') inter L_J))$, whence
  $V_(J') inter L_J=V_(J'') inter L_J$. By what has been shown above, this
  implies that $V_(J')=V_(J'')$, and we conclude that $P_(J')=P_(J'')$, by
  Theorem~@th:split-bn-parabolic-levi-decomposition,
  part~@case:split-parabolic-unipotent-normalizer. Finally, if $Q$ is a standard
  parabolic subgroup of $L_J$, then $Q V_J >= (B inter L_J)V_J=B$, by the proof
  of @th:split-bn-parabolic-levi-decomposition. Then $Q V_J$ is a standard
  parabolic subgroup of $G$ contained in $P_J$, and we clearly have
  $Q V_J inter L_J=Q$. Thus the correspondence $P_(J') arrow P_(J') inter L_J$,
  for $J' subset.eq J$, is a bijection, and the proof is complete.
]

For the remainder of §~@ss:split-bn-pair-parabolic-intersections, let $I,J$
denote fixed subsets of $S$, and let $x in D_(I J)$ be a fixed distinguished
double coset representative (see
@def:distinguished-parabolic-double-coset-representative). By
@th:parabolic-subgroup-intersection and @cor:parabolic-root-system-intersection
we have
$ W_I inter attach(W_J, tl: x)=W_K, quad "where" K=I inter attach(J, tl: x), $
$
  Delta_I inter x Delta_J=Delta_K, quad "and" quad
  Pi_I inter x Pi_J=Pi_K.
$

#theorem[
  Let $I,J subset.eq S$, and let $x in D_(I J)$, as above. Then the following
  statements hold:
  #case-list(
    numbering: "(i)",
    [#case[
      $P_K=(P_I inter attach(P_J, tl: x))V_I$, where
      $K=I inter attach(J, tl: x)$.
    ] <case:parabolic-intersection-enlargement>],
    [#case[
      $V_K=(P_I inter attach(V_J, tl: x))V_I$ and
      $L_K=L_I inter attach(L_J, tl: x)$.
    ] <case:parabolic-intersection-unipotent-levi>],
    [#case[
      $P_I inter attach(V_J, tl: x)
      =(L_I inter attach(V_J, tl: x))(V_I inter attach(V_J, tl: x))$.
    ] <case:parabolic-intersection-unipotent-projection>],
    [#case[
      $L_I inter attach(P_J, tl: x)$ is a standard parabolic subgroup of $L_I$,
      and
      $
        L_I inter attach(P_J, tl: x)=L_I inter P_K,
        quad O_p lr((L_I inter attach(P_J, tl: x)))
        =L_I inter attach(V_J, tl: x).
      $
    ] <case:parabolic-intersection-levi-parabolic>],
    [#case[
      We have a factorization
      $
        P_I inter attach(P_J, tl: x)
        =L_K lr((L_I inter attach(V_J, tl: x)))(V_I inter attach(L_J, tl: x))
        (V_I inter attach(V_J, tl: x)),
      $
      with uniqueness of expression.
    ] <case:parabolic-intersection-four-factor-decomposition>],
  )
] <th:split-parabolic-intersection-factorization>

#proof[
  #case-list(
    numbering: "(i)",
    [#case[
      The product on the right-hand side of
      @case:parabolic-intersection-enlargement is a subgroup, because $P_I$
      normalizes $V_I$ (see @th:split-bn-parabolic-levi-decomposition). From the
      definitions of $K,L_K$, and $V_K$, we have
      $ L_K<=L_I inter attach(L_J, tl: x) quad "and" quad V_K>=V_I, $
      #source(680)
      so
      $
        P_K=lr(
          chevron.l T, U_alpha ":" alpha in Delta_K union Delta_+ chevron.r
        )
        <=(P_I inter attach(P_J, tl: x))V_I.
      $
      Conversely, $P_I inter attach(P_J, tl: x)$ is a union of intersections of
      the form
      $
        B y B inter attach((B z B), tl: x),
        quad "with" y in W_I, quad z in W_J.
      $
      Since $x in D_(I J)$, we have
      $
        l(y x)=l(y)+l(x) quad "and" quad l(x z)=l(x)+l(z)
        quad "for all" y in W_I, quad z in W_J.
      $
      Also recall that if $l(x y)=l(x)+l(y)$, where $x,y in W$, then
      $ x B y subset.eq B x y B, $
      by @prop:bruhat-length-increasing-product. Thus if the above intersection
      $B y B inter attach((B z B), tl: x) != emptyset$, we have
      $B y B x inter x B z B != emptyset$, and hence
      $ B y x B inter B x z B != emptyset. $
      By the uniqueness statement in @th:bruhat-decomposition, it follows that
      $y x=x z$ in $W$, and therefore
      $y=x z x^(-1) in W_I inter attach(W_J, tl: x)=W_K$. We have now shown that
      if $B y B inter attach((B z B), tl: x) != emptyset$, then $y in W_K$, and
      hence $(P_I inter attach(P_J, tl: x))V_I<=P_K$, completing the proof of
      @case:parabolic-intersection-enlargement.
    ] <case:parabolic-intersection-enlargement-proof>],
    [#case[
      By part~@case:parabolic-intersection-enlargement, we have
      $(P_I inter attach(V_J, tl: x))V_I<=P_K$, and it is then clear that
      $(P_I inter attach(V_J, tl: x))V_I<=O_p lr((P_K))$. In order to prove the
      reverse inclusion, we start with the fact that by its definition in
      @th:split-bn-parabolic-levi-decomposition, $V_K$ is generated by root
      subgroups ${U_beta:beta in Delta_+-Delta_(K,+)}$; we shall prove that
      $U_beta<=(P_I inter attach(V_J, tl: x))V_I$ for each such root $beta$. If
      $beta in.not Delta_(I,+)$, then $U_beta<=V_I$ by the definition of $V_I$,
      and there is nothing further to prove in this case. We may thus assume
      that $beta in Delta_(I,+)$, and $beta in.not Delta_K$. Since
      $x in D_(I J)$, we have $l(s_i x)>=l(x)$ for all $s_i in I$, and hence
      $x^(-1) lr((alpha_i)) in Delta_+$ for all $alpha_i in Pi_I$, by
      @th:reflection-length-cancellation-exchange,
      part~@case:reflection-right-descent, and it follows that
      $x^(-1)beta in Delta_+$. On the other hand, $beta in.not Delta_K$ implies
      $x^(-1)beta in.not Delta_J$, since $Delta_K=Delta_I inter x Delta_J$, and
      we have $x^(-1)beta in Delta_+-Delta_(J,+)$. Thus $U_(x^(-1)beta)<=V_J$ by
      the definition of $V_J$, and since
      $U_(x^(-1)beta)=attach(U_beta, tl: x^(-1))$ by
      @prop:split-bn-root-subgroup-properties, we obtain
      $U_beta<=attach(V_J, tl: x)inter P_I$, completing the proof of the first
      statement. The second is proved after
      @case:parabolic-intersection-levi-parabolic.
    ] <case:parabolic-intersection-unipotent-proof>],
    [#case[
      The right-hand side is certainly contained in the left, since
      $P_I=L_I V_I$ by @th:split-bn-parabolic-levi-decomposition. For the
      reverse inclusion, we have
      $ P_I inter attach(V_J, tl: x)<=V_K, $
      by the first part of @case:parabolic-intersection-unipotent-levi. By
      @lem:parabolic-longest-positive-root-complement,
      part~@case:parabolic-longest-inversion-roots and the definition of $V_K$,
      we have $V_K=U_(w_K)^+$, where $w_K$ is the element of maximal length in
      $W_K$. By @prop:split-bn-root-subgroup-properties,
      part~@case:split-bn-ordered-root-factorization, it follows that $V_K$ is
      the product of the root subgroups
      ${U_beta:beta in Delta_+-Delta_(K,+)=Delta_(w_K)^+}$, taken in some order.
      By the proof of part~@case:parabolic-intersection-unipotent-levi, these
      root subgroups satisfy the condition:
      $
        "either" quad U_beta<=V_I quad "or" quad
        U_beta<=P_I inter attach(V_J, tl: x),
        quad "for" beta in.not Delta_+-Delta_(I,+).
      $
      #source(681)
      We also have $V_I ⊴ V_K$, since $K subset.eq I$, and $V_I$ is normalized
      by $P_I$, which certainly contains $V_K$. Thus
      $
        (U_beta,U_gamma)<=V_I,
        quad "if" U_beta<=V_I, quad U_gamma<=V_K.
      $ <eq:parabolic-intersection-root-reordering>

      Now let $g in P_I inter attach(V_J, tl: x)$. Since $g in V_K$, $g$ is a
      product of elements belonging to the root subgroups ${U_beta}$ as above,
      and by rearranging the factors, using the commutator relation
      @eq:parabolic-intersection-root-reordering, we obtain
      $ g=g' g'', $
      where $g'$ is a product of elements of root subgroups
      $U_beta<=P_I inter attach(V_J, tl: x)$, $beta in.not Delta_+-Delta_(I,+)$,
      and $g'' in V_I$. Thus $g'' in V_I inter attach(V_J, tl: x)$, since both
      $g$ and $g'$ belong to $attach(V_J, tl: x)$, and
      $g' in L_I inter attach(V_J, tl: x)$ because the root subgroups
      ${U_beta<=P_I inter attach(V_J, tl: x),beta in Delta_(w_K)^+,
        beta in.not Delta_+-Delta_I}$ all belong to $L_I$. Thus
      $g in (L_I inter attach(V_J, tl: x))(V_I inter attach(V_J, tl: x))$, and
      @case:parabolic-intersection-unipotent-projection is proved.
    ] <case:parabolic-intersection-projection-proof>],
    [#case[
      The proof of @case:parabolic-intersection-unipotent-levi shows that
      $x^(-1) lr((Delta_(I,+))) subset.eq Delta_+$. By the remark following
      @eq:standard-levi-sharp-bruhat-decomposition, $B inter L_I=U_(w_I)^- T$,
      and $Delta_(w_I)^-=Delta_(I,+)$ by
      @lem:parabolic-longest-positive-root-complement,
      part~@case:parabolic-longest-inversion-roots. It follows that
      $ B inter L_I<=L_I inter attach(P_J, tl: x), $
      and hence $L_I inter attach(P_J, tl: x)$ is a standard parabolic subgroup
      of $L_I$, containing the Borel subgroup $B inter L_I$ (see
      @th:split-bn-parabolic-levi-decomposition,
      part~@case:standard-levi-split-bn-pair). Moreover,
      $L_I inter attach(P_J, tl: x)<=L_I inter P_K$, and by
      @prop:standard-levi-parabolic-correspondence, we have
      $O_p lr((L_I inter P_K))=L_I inter V_K$. By
      parts~@case:parabolic-intersection-unipotent-levi and
      @case:parabolic-intersection-unipotent-projection, we obtain
      $L_I inter V_K=L_I inter attach(V_J, tl: x)$. By
      @prop:standard-levi-parabolic-correspondence again, we have
      $
        L_I inter P_K=L_K lr((L_I inter V_K))
        =L_K lr((L_I inter attach(V_J, tl: x)))<=L_I inter attach(P_J, tl: x),
      $
      using the fact that $Delta_K=Delta_I inter x Delta_J$. Combining our
      results, we have shown that
      $
        L_I inter attach(P_J, tl: x)=L_I inter P_K
        quad "and" quad O_p lr((L_I inter attach(P_J, tl: x)))
        =L_I inter attach(V_J, tl: x),
      $
      completing the proof of @case:parabolic-intersection-levi-parabolic.

      We are now in a position to prove the second statement of
      @case:parabolic-intersection-unipotent-levi. Since
      $Delta_K=Delta_I inter x Delta_J$, we have
      $L_K<=L_I inter attach(L_J, tl: x)$, by the definition of the Levi
      subgroups in @th:split-bn-parabolic-levi-decomposition. Then
      $
        L_I inter attach(L_J, tl: x)<=L_I inter attach(P_J, tl: x)
        =L_K lr((L_I inter attach(V_J, tl: x)))
      $
      by part~@case:parabolic-intersection-levi-parabolic. Suppose
      $l in L_I inter attach(L_J, tl: x)$, and write $l=m u$, with $m in L_K$,
      $u in L_I inter attach(V_J, tl: x)$. Then
      $m^(-1)l=u in attach(L_J, tl: x)inter attach(V_J, tl: x)=1$, so $u=1$, and
      $L_I inter attach(L_J, tl: x)<=L_K$, completing the proof.
    ] <case:parabolic-intersection-levi-parabolic-proof>],
    [#case[
      We first prove
      $
        P_I inter attach(P_J, tl: x)
        =L_K lr((P_I inter attach(V_J, tl: x)))(V_I inter attach(P_J, tl: x)).
      $ <eq:parabolic-intersection-three-factor-step>

      Now $P_I inter attach(P_J, tl: x)<=P_K=L_K V_K$ by
      part~@case:parabolic-intersection-enlargement, and
      $V_K=(P_I inter attach(V_J, tl: x))V_I$ by
      part~@case:parabolic-intersection-unipotent-levi. Thus
      #source(682)
      each element $g in P_I inter attach(P_J, tl: x)$ can be expressed in the
      form
      $
        g=l u v, quad "with" l in L_K,
        quad u in P_I inter attach(V_J, tl: x), quad v in V_I.
      $
      This formula implies that $v in V_I inter attach(P_J, tl: x)$, and we have
      $P_I inter attach(P_J, tl: x)
      <=L_K lr((P_I inter attach(V_J, tl: x)))(V_I inter attach(P_J, tl: x))$.
      For the reverse inequality, it suffices by
      @case:parabolic-intersection-enlargement to prove that
      $L_K<=P_I inter attach(P_J, tl: x)$, and this is immediate by the second
      part of @case:parabolic-intersection-unipotent-levi. The factorization of
      $P_I inter attach(P_J, tl: x)$ given in
      @case:parabolic-intersection-four-factor-decomposition follows from
      @eq:parabolic-intersection-three-factor-step, using
      @case:parabolic-intersection-unipotent-projection. The uniqueness of
      expression follows by consideration of the Levi decompositions in $P_I$
      and $attach(P_J, tl: x)$, and is left to the reader. This completes the
      proof of the theorem.
    ] <case:parabolic-intersection-four-factor-proof>],
  )
]

By @th:bn-pair-parabolic-normalizers-containment, two standard parabolic
subgroups $P_I$ and $P_J$ are never conjugate in $G$ unless they coincide. On
the other hand, their Levi subgroups may be conjugate even when $I != J$. To
conclude this subsection, we give a criterion for this to occur, in terms of the
results obtained in @th:split-parabolic-intersection-factorization on slicing up
intersections of parabolic subgroups.

#theorem[
  Let $I,J subset.eq S$, and let $x in D_(I J)$, as in
  @th:split-parabolic-intersection-factorization. Then the following statements
  are equivalent.
  #case-list(
    numbering: "(i)",
    [#case[$P_K=P_I$.] <case:standard-levi-containment-parabolic>],
    [#case[$P_I inter attach(V_J, tl: x)<=V_I$.]
      <case:standard-levi-containment-radical>],
    [#case[$L_I<=attach(L_J, tl: x)$.]
      <case:standard-levi-containment>],
  )
] <th:standard-levi-containment-criterion>
#proof[
  @case:standard-levi-containment-parabolic $=>$
  @case:standard-levi-containment. By @case:standard-levi-containment-parabolic
  we have $W_K=W_I$, whence $Delta_K=Delta_I$. Since
  $Delta_K=Delta_I inter x Delta_J$, it follows that
  $Delta_I subset.eq x Delta_J$. Then $L_I<=attach(L_J, tl: x)$, by
  @prop:split-bn-root-subgroup-properties,
  part~@case:split-bn-root-group-weyl-action and the definitions of the Levi
  subgroups in @th:split-bn-parabolic-levi-decomposition.

  @case:standard-levi-containment $=>$ @case:standard-levi-containment-radical.
  From @case:standard-levi-containment and
  @th:split-bn-parabolic-levi-decomposition applied to $P_J$, we obtain
  $L_I inter attach(V_J, tl: x)=1$. Then @case:standard-levi-containment-radical
  follows from @th:split-parabolic-intersection-factorization,
  part~@case:parabolic-intersection-unipotent-projection.

  @case:standard-levi-containment-radical $=>$
  @case:standard-levi-containment-parabolic. By
  @th:split-parabolic-intersection-factorization,
  part~@case:parabolic-intersection-unipotent-levi,
  $P_I inter attach(V_J, tl: x)<=V_I$ implies that $V_K=V_I$. Then $P_I=P_K$ by
  @th:split-bn-parabolic-levi-decomposition,
  part~@case:split-parabolic-unipotent-normalizer, completing the proof.
]

#exercise-heading

Describe the standard parabolics, and their Levi decompositions, for the split
$B N$-pair in $GL_(n+1) lr((FF_q))$ given in @prop:general-linear-split-bn-pair.
