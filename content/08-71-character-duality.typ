#import "main-defs.typ": *
#import "statements.typ": *

== A Duality Operation in $op("ch") CC G$ <sec:character-duality>

Let $H$ be a finite group. A _#idx("Duality operation")duality operation_ in
$op("ch") CC H$ is a $ZZ$-automorphism of order $2$ that preserves the inner
product $(lambda,mu)_H$, for $lambda,mu in op("ch") CC H$. Such an operation
clearly permutes, up to sign, the irreducible $CC$-characters of $H$. A familiar
example of a duality operation is the map $zeta arrow overline(zeta)$, for
$zeta in op("ch") CC H$, given by complex conjugation. This map corresponds to
the operation of forming the #idx("Contragredient")contragredient module of a
given $CC H$-module.

Now let $G$ be a finite group with a split $B N$-pair of characteristic $p$. We
shall
#source(705)
define another duality operation $D_G:op("ch") CC G arrow op("ch") CC G$ in this
case, such that $D_G 1_G=op("St")_G$, where $op("St")_G$ is the Steinberg
character of $G$. This operation has a number of applications to both the
ordinary and modular representation theory of $G$, which we shall discuss, along
with other things, in this section and the next. The results in this section are
due to Curtis @bib:Curtis1980a and Alvis (@bib:Alvis1980, @bib:Alvis1982) (see
also the survey article (Curtis @bib:Curtis1982)). The main results were proved
independently by Kawanaka @bib:Kawanaka1982, who also discussed $D_G$ in the
context of Fourier transforms of functions on the Lie algebra of $G$, and by
Deligne–Lusztig (@bib:Deligne1982, @bib:Deligne1983).

=== Definition and Basic Properties of $D_G$
<ss:character-duality-basic-properties>

Throughout this section, $G$ denotes a finite group with a split $B N$-pair of
characteristic $p$, and $(W,S)$ the pair consisting of the Weyl group $W$ and
the set $S$ of distinguished generators of $W$. We shall follow the notation of
§~@sec:cuspidal-characters, and also use most of its results. In particular,
$op("ch") H$ denotes the set of all virtual $CC$-characters of a finite group
$H$.

The general concept of a _duality operation_ was defined above. We begin with a
duality operation in $op("ch") W$, given by the map
$ mu arrow mu epsilon,quad mu in op("ch") W, $
where $epsilon$ is the sign character of $W$ (see
@def:coxeter-sign-representation). This map is clearly a duality operation, and
has traditionally been used to organize the character tables of finite Coxeter
groups. This operation is related to the parabolic subgroups of $W$ by the
following result.

#proposition[
  Let $(W,S)$ be a finite Coxeter system, and let $epsilon$ be the sign
  representation of $W$. Then
  $
    mu epsilon=sum_(J subset.eq S)(-1)^(abs(J))
    (lr(mu |)_(W_J))^W.
  $
] <prop:coxeter-sign-restriction-induction>

#proof[
  By Solomon's formula @cor:solomon-sign-character-formula, we have
  $ epsilon=sum_(J subset.eq S)(-1)^(abs(J))(1_(W_J))^W. $
  Multiplying by $mu$, we obtain
  $ mu epsilon=sum_(J subset.eq S)(-1)^(abs(J))mu dot (1_(W_J))^W. $
  The proof is completed by the observation that
  $
    mu dot (1_(W_J))^W=(lr(mu |)_(W_J))^W
    quad "for all" J subset.eq S,
  $
  by @i:lem:class-function-induction-product.
]

#source(706)
We now define a duality operation in $op("ch") G$, using a formula similar to
@prop:coxeter-sign-restriction-induction. The operations of restriction and
induction occurring in @prop:coxeter-sign-restriction-induction are replaced by
truncation and generalized induction (§~@ss:generalized-restriction-induction).

#definition[
  The _duality operation_ $D_G$ in $op("ch") G$ is the $ZZ$-endomorphism given
  by
  $
    D_G zeta=sum_(J subset.eq S)(-1)^(abs(J))
    R_(L_J)^G T_(L_J)^G zeta,quad "for" zeta in op("ch") G.
  $
] <def:character-duality-operation>
#idx("Duality operation", target: [@def:character-duality-operation])
#nidx("$D_G$", "duality operation", target: [@def:character-duality-operation])

#remarks(name: "Remarks and Example", numbered: false)[
  By @def:steinberg-representation, we have
  $ D_G 1_G=op("St")_G. $
  Note that in this case the degrees of $1_G$ and its dual $D_G 1_G$ differ by
  $abs(G)_p$, since
  $
    op("St")_G 1=abs(B ":" B inter attach(B, tl: w_0))
    =abs(B ":" T)=abs(U)=abs(G)_p,
  $
  by @th:steinberg-character-sign-correspondence and
  @prop:split-bn-pair-order-sylow-steinberg.

  On the other hand, we have
  $ D_G zeta=(-1)^(abs(S))zeta $
  for all cuspidal characters $zeta$ of $G$, by @def:cuspidal-character-module.

  For positive rank, these remarks show that the operation $D_G$ is _not_ given
  by multiplication by a linear character, as in
  @prop:coxeter-sign-restriction-induction; it is not even clear at this point
  whether @def:character-duality-operation defines a duality operation. This
  fact will follow from the next two theorems.
] <rem:character-duality-trivial-cuspidal>

The first is due to Curtis @bib:Curtis1980a, with a simplified proof based on
§~@sec:cuspidal-characters. Another proof, in a geometrical context, has been
given by Digne–Michel @bib:Digne1982. In order to state the result, we recall
that for each $J subset.eq S$, the standard Levi subgroup $L_J$ is a finite
group with a split $B N$-pair, so $D_(L_J):op("ch") L_J arrow op("ch") L_J$ is
defined (by @def:character-duality-operation).

#theorem[
  Let $zeta in op("ch") G$ and $I subset.eq S$. Then
  $ T_(L_I)^G D_G zeta=D_(L_I)T_(L_I)^G zeta. $
  In other words, truncation intertwines duality.
] <th:character-duality-truncation-intertwining>

#proof[
  We must prove that
  $
    sum_(J subset.eq S)(-1)^(abs(J))T_(L_I)^G R_(L_J)^G T_(L_J)^G zeta
    =sum_(K subset.eq I)(-1)^(abs(K))
    R_(L_K)^(L_I)T_(L_K)^(L_I)T_(L_I)^G zeta,
  $ <eq:character-duality-truncation-expanded-identity>
  for each $zeta in op("ch") G$. We begin by applying the Generalized Subgroup
  Theorem (Exercise~@exc:generalized-character-subgroup-theorem) to a typical
  term on the left side of @eq:character-duality-truncation-expanded-identity.
  We obtain
  $
    T_(L_I)^G R_(L_J)^G T_(L_J)^G zeta
    =sum_(x in D_(I J))R_(L_K)^(L_I)
    attach((T_(L_(K'))^(L_J)T_(L_J)^G zeta), tl: dot(x))
    =sum_(x in D_(I J))R_(L_K)^(L_I)
    attach((T_(L_(K'))^G zeta), tl: dot(x)),
  $
  #source(707)
  by transitivity of truncation @prop:truncation-induction-basic-properties,
  part~@case:generalized-character-operations-transitivity, where
  $ K=I inter attach(J, tl: x)=attach(K', tl: x) $
  as in the statement of the Generalized Subgroup Theorem. For $x in D_(I J)$
  and $K,K'$ as above, we have $L_K=attach(L_(K'), tl: x)$, and the
  corresponding term in the sum becomes
  $ R_(L_K)^(L_I)T_(L_K)^G zeta, $
  by @th:generalized-induction-parabolic-independence. Then the left side of
  @eq:character-duality-truncation-expanded-identity is given by
  $
    sum_(K subset.eq I)sum_(J subset.eq S)(-1)^(abs(J))
    a_(I J K)R_(L_K)^(L_I)T_(L_K)^G zeta,
  $
  where for $I,J subset.eq S$ and $K subset.eq I$,
  $ a_(I J K)=op("card"){x in D_(I J):I inter attach(J, tl: x)=K}. $
  The identity @eq:character-duality-truncation-expanded-identity is an
  immediate consequence of these facts, and the following:
]

#lemma[
  For $J subset.eq S$ and $K subset.eq I$, let $a_(I J K)$ be defined as above.
  Then
  $ sum_(J subset.eq S)(-1)^(abs(J))a_(I J K)=(-1)^(abs(K)). $
] <lem:distinguished-double-coset-alternating-count>

We omit the proof, and refer the reader to Curtis @bib:Curtis1980a. For a
geometric interpretation of the lemma, see Howlett–Lehrer @bib:Howlett1982 and
Digne–Michel @bib:Digne1982. This completes the proof of
Theorem~@th:character-duality-truncation-intertwining.

Since $D_G 1_G=op("St")_G$, we obtain:

#corollary[
  For each subset $I subset.eq S$, we have
  $ T_(L_I)^G op("St")_G=op("St")_(L_I). $
] <cor:steinberg-character-truncation>

We next state the following basic result:

#theorem(title: [Alvis @bib:Alvis1980])[
  The duality operation $D_G$ is a self-adjoint isometry in $op("ch") G$ of
  order $2$. Thus
  $ (D_G zeta,eta)=(zeta,D_G eta)quad "and" D_G^2 zeta=zeta, $
  for all $zeta,eta in op("ch") G$.
] <th:character-duality-self-adjoint-involution>
#idx("Alvis's Theorem", target: [@th:character-duality-self-adjoint-involution])

#proof[
  By @prop:truncation-induction-basic-properties,
  part~@case:truncation-invariant-module, we have
  $ T_(L_J)^G zeta=sum_(phi in op("Irr") L_J)(zeta,R_(L_J)^G phi)phi. $
  #source(708)
  Using this fact, we obtain
  $
    & (D_G zeta,eta)=sum_(J subset.eq S)(-1)^(abs(J))
      (R_(L_J)^G T_(L_J)^G zeta,eta) \
    & =sum_(J subset.eq S)(-1)^(abs(J))
      (R_(L_J)^G lr({sum_(phi in op("Irr") L_J)(zeta,R_(L_J)^G phi)phi}),eta) \
    & =sum_(J subset.eq S)(-1)^(abs(J))sum_(phi in op("Irr") L_J)
      (zeta,R_(L_J)^G phi)(R_(L_J)^G phi,eta)=(zeta,D_G eta),
  $
  by symmetry.

  We next prove that $D_G^2$ is the identity map. Let $zeta in op("ch") G$. Then
  $
    & D_G^2 zeta=sum_(J subset.eq S)(-1)^(abs(J))
      R_(L_J)^G T_(L_J)^G D_G zeta
      =sum_(J subset.eq S)(-1)^(abs(J))R_(L_J)^G D_(L_J)T_(L_J)^G zeta \
    & =sum_(J subset.eq S)(-1)^(abs(J))sum_(K subset.eq J)(-1)^(abs(K))
      R_(L_J)^G R_(L_K)^(L_J)T_(L_K)^(L_J)T_(L_J)^G zeta \
    & =sum_(J subset.eq S)(-1)^(abs(J))sum_(K subset.eq J)(-1)^(abs(K))
      R_(L_K)^G T_(L_K)^G zeta \
    & =sum_(K subset.eq S)(-1)^(abs(K))
      (sum_(J supset.eq K)(-1)^(abs(J)))R_(L_K)^G T_(L_K)^G zeta
      =(-1)^(2abs(S))zeta=zeta.
  $
  In this calculation, we have used
  @th:character-duality-truncation-intertwining at the second step,
  @prop:truncation-induction-basic-properties,
  part~@case:generalized-character-operations-transitivity at the fourth, and
  the fact that $sum_(J supset.eq K)(-1)^(abs(J))=0$ if $K!=S$ in the last step.

  From what has been shown, it is now easy to prove that $D_G$ is an isometry.
  Let $zeta,eta in op("ch") G$. Then
  $ (D_G zeta,D_G eta)=(zeta,D_G^2 eta)=(zeta,eta), $
  completing the proof.
]

#corollary[
  The map $D_G$ is a duality operation, and permutes the irreducible characters
  of $G$, up to sign.
] <cor:character-duality-signed-irreducible-permutation>

#proof[
  Let $zeta in op("Irr") G$. Then $D_G zeta in op("ch") G$ and
  $(D_G zeta,D_G zeta)=(zeta,zeta)=1$ by
  @th:character-duality-self-adjoint-involution. It follows that
  $plus.minus D_G zeta in op("Irr") G$, as required.
]

=== The Effects of $D_G$ on Character Degrees <ss:character-duality-degrees>

We keep the assumptions and notation of
§~@ss:character-duality-basic-properties. It will be necessary to extend the
operations of truncation $T_(L_J)^G$ and generalized induction $R_(L_J)^G$, for
$J subset.eq S$, to the vector spaces $cf(G)$ and $cf(L_J)$ of complex-valued
class functions on $G$ and $L_J$. This is easily done by linearity, since
$op("Irr") G$ is a $CC$-basis of $cf(G)$, by
@i:prop:class-function-orthonormal-basis, part (i).

The first result is a variation by Alvis @bib:Alvis1980 on a theorem of Springer
@bib:Springer1980.

#theorem[
  Let $V$ denote the set of all $p$-elements in $G$, and $chi_V$ the
  characteristic function on $V$ (that is, the function that is $1$ on $V$, and
  $0$ on the
  #source(709)
  complement of $V$). Then
  $ D_G rho_G=abs(G)_(p')chi_V, $
  where $rho_G$ is the regular character of $G$, and $abs(G)_(p')$ is the
  $p'$-part of the order of $G$.
] <th:character-duality-regular-unipotent-indicator>

Before starting the proof, we require a lemma. We recall (from
§~@ss:generalized-restriction-induction) that for a class function $xi$ on
$L_J$, $J subset.eq S$, the _pullback_ $tilde(xi)$ (or $xi^"~"$) is the class
function on the parabolic subgroup $P_J$ defined by $tilde(xi)(l v)=xi(l)$; here
$l in L_J$ and $v in V_J$, using the Levi decomposition $P_J=L_J V_J$ (see
@th:split-bn-parabolic-levi-decomposition).

#lemma[
  Let $J subset.eq S$. Then
  $ tilde(T_(L_J)^G chi_V)=lr(chi_V |)_(P_J). $
] <lem:unipotent-indicator-truncation-inflation>

#proof[
  Let $P_J=L_J V_J$ be the Levi decomposition of $P_J$. Since $V_J$ is a normal
  $p$-subgroup of $P_J$, it is easily verified that for an arbitrary element
  $v in V_J$, an element $g in P_J$ is a $p$-element if and only if $g v$ is a
  $p$-element. We have to prove that
  $
    tilde(T_(L_J)^G chi_V)(g)=chi_V lr((g))
    quad "for all" g in P_J.
  $
  First suppose $g$ is a $p$-element. Then $chi_V lr((g))=1$. Now write
  $g=l v in L_J V_J$, $v in V_J$, obtaining
  $
    tilde(T_(L_J)^G chi_V)(g)=(T_(L_J)^G chi_V)(l)
    =abs(V_J)^(-1)sum_(v in V_J)chi_V lr((l v)).
  $
  Since $g$ is assumed to be a $p$-element, so also is $l$, as well as all the
  products $l v$, $v in V_J$, by the first step of the proof. It follows that
  $tilde(T_(L_J)^G chi_V)(g)=1$, and the lemma is proved in this case. On the
  other hand if $g$ is not a $p$-element, the same argument shows that both
  $chi_V lr((g))$ and $tilde(T_(L_J)^G chi_V)(g)$ are zero, completing the
  proof.
]

#proof(head: emph[Proof of @th:character-duality-regular-unipotent-indicator.])[
  We note first that $op("St")_G lr((1))=abs(G)_p$, by
  @prop:split-bn-pair-order-sylow-steinberg, and hence $op("St")_G$ vanishes on
  $p$-irregular elements of $G$ by
  @i:prop:defect-zero-character-projective-simple and
  @i:th:projective-characters-supported-p-regular, part (ii), since
  $op("St")_G in op("Irr") G$. We now have
  $
    & abs(G)_(p')^(-1)rho_G=chi_V dot op("St")_G
      quad ("by direct verification") \
    & =sum_(J subset.eq S)(-1)^(abs(J))chi_V dot (1_(P_J))^G
      quad ("since" op("St")_G=D_G 1_G) \
    & =sum_(J subset.eq S)(-1)^(abs(J))(lr(chi_V |)_(P_J))^G
      =sum_(J subset.eq S)(-1)^(abs(J))(tilde(T_(L_J)^G chi_V))^G
      quad ("by" #[@i:lem:class-function-induction-product]
        "and" #[@lem:unipotent-indicator-truncation-inflation]) \
    & =sum_(J subset.eq S)(-1)^(abs(J))R_(L_J)^G T_(L_J)^G chi_V=D_G chi_V.
  $
  Now apply $D_G$ to both sides, to obtain
  $ abs(G)_(p')^(-1)D_G rho_G=D_G^2 chi_V=chi_V, $
  by @th:character-duality-self-adjoint-involution, completing the proof.
]

#source(710)
We obtain several new results about irreducible characters of $G$ as a
consequence of @th:character-duality-regular-unipotent-indicator. The last of
these is related to a conjecture of MacDonald (see Springer @bib:Springer1980
and Alvis @bib:Alvis1980, @bib:Alvis1982).

#theorem(title: [Alvis @bib:Alvis1980])[
  The following statements hold for all $zeta in op("Irr") G$:
  #case-list(
    numbering: "(i)",
    [#case[
      $sum_(u in V)zeta(u)=abs(G)_p D_G zeta(1)$.
    ] <case:duality-degree-unipotent-sum>],
    [#case[
      $(D_G zeta)(1)_(p')=zeta(1)_(p')$.
    ] <case:duality-degree-prime-to-p-part>],
    [#case[
      $zeta(1)^(-1)sum_(u in V)zeta(u)$ is, up to sign, a power of $p$.
    ] <case:unipotent-character-average-prime-power>],
  )
] <th:duality-character-degree-unipotent-sums>

#proof[
  @case:duality-degree-unipotent-sum By the definition of $chi_V$ and
  @th:character-duality-self-adjoint-involution, we obtain
  $
    sum_(u in V)zeta(u)=abs(G)(zeta,chi_V)_G
    =abs(G)(D_G zeta,D_G chi_V)_G.
  $
  Since $D_G chi_V=abs(G)_(p')^(-1)rho_G$ by
  @th:character-duality-regular-unipotent-indicator, the expression becomes
  $ sum_(u in V)zeta(u)=abs(G)_p lr((D_G zeta))(1), $
  using Exercise~@i:exc:regular-character-multiplicities and the fact that
  $plus.minus D_G zeta in op("Irr") G$.

  @case:duality-degree-prime-to-p-part We first note that the set $V$ of all
  $p$-elements is the union of conjugacy classes ${cal(C)'}$ of $p$-elements.
  For each $cal(C)'$, let $u_(cal(C)')$ denote an element of $cal(C)'$. Then
  $
    zeta(1)^(-1)sum_(u in V)zeta(u)
    =sum_(cal(C)')zeta(1)^(-1)abs(cal(C)')zeta(u_(cal(C)'))in ZZ,
  $
  since the left side is a rational number, by
  part~@case:duality-degree-unipotent-sum, and the right side is an algebraic
  integer by @i:prop:central-character-values-integral. Thus
  $ abs(G)_p D_G zeta(1)zeta(1)^(-1)in ZZ $
  by part~@case:duality-degree-unipotent-sum. Since
  $plus.minus D_G zeta in op("Irr") G$, we can replace $zeta$ by $D_G zeta$ in
  the above argument, to obtain
  $
    abs(G)_p lr((D_G^2 zeta))(1)(D_G zeta)(1)^(-1)
    =abs(G)_p zeta(1)(D_G zeta)(1)^(-1)in ZZ,
  $
  using @th:character-duality-self-adjoint-involution. Then
  @case:duality-degree-prime-to-p-part follows by comparing these results.

  @case:unipotent-character-average-prime-power is a direct consequence of
  @case:duality-degree-unipotent-sum and @case:duality-degree-prime-to-p-part,
  and completes the proof of the theorem.
]

#corollary(title: [Steinberg @bib:Steinberg1968])[
  Let $V$ denote the set of all $p$-elements in $G$. Then $abs(V)=(abs(G)_p)^2$.
] <cor:unipotent-element-count-sylow-square>

For the proof, simply apply @th:duality-character-degree-unipotent-sums,
part~@case:duality-degree-unipotent-sum, with $zeta=1_G$, and use the fact that
$D_G 1_G=op("St")_G$.

#source(711)
The next result shows how $D_G$ interacts with Harish-Chandra's “philosophy of
cusp forms” (see §~@ss:philosophy-cusp-forms).

#proposition[
  Let $J subset.eq S$, and let $phi$ be a cuspidal irreducible character of the
  standard Levi subgroup $L_J$. Then
  $ D_G lr((R_(L_J)^G phi))=(-1)^(abs(J))R_(L_J)^G phi. $
  Moreover,
  $
    (zeta,R_(L_J)^G phi)!=0 => (D_G zeta,R_(L_J)^G phi)!=0
    quad "for all" zeta in op("Irr") G.
  $
  Thus for $phi$ as above, $D_G$ permutes the irreducible components of
  $R_(L_J)^G phi$, up to sign.
] <prop:character-duality-cuspidal-series>

#proof[
  Let $zeta in op("Irr") G$. Then we have
  $
    & (D_G R_(L_J)^G phi,zeta)_G
      =(R_(L_J)^G phi,D_G zeta)_G
      =(phi,T_(L_J)^G D_G zeta)_(L_J) \
    & =(phi,D_(L_J)T_(L_J)^G zeta)_(L_J)
      =(D_(L_J)phi,T_(L_J)^G zeta)_(L_J)
      =(-1)^(abs(J))(phi,T_(L_J)^G zeta)_(L_J) \
    & =(-1)^(abs(J))(R_(L_J)^G phi,zeta)_G,
  $
  by @th:character-duality-self-adjoint-involution,
  @prop:truncation-induction-basic-properties,
  @th:character-duality-truncation-intertwining,
  @th:character-duality-self-adjoint-involution, and
  @prop:truncation-induction-basic-properties, respectively. We have also used
  the fact that $D_(L_J)phi=(-1)^(abs(J))phi$, for cuspidal characters $phi$ of
  $L_J$, by the remark following @def:character-duality-operation. This
  completes the proof.
]

The preceding result raises interesting questions as to the exact manner in
which $D_G$ permutes the characters in $R_(L_J)^G phi$, as in
@prop:character-duality-cuspidal-series, and whether a sharpened version of
Theorem~@th:duality-character-degree-unipotent-sums,
part~@case:unipotent-character-average-prime-power, in the comparison of
$deg zeta$ and $deg D_G zeta$ is valid in this context. We answer these
questions here for the case of $(1_B)^G$. For arbitrary principal series
characters, see McGovern @bib:McGovern1982, and for the general case, see
Howlett–Lehrer @bib:Howlett1983.

We require the parametrization $phi arrow zeta_(phi,q)$ of irreducible
characters in $(1_(B(q)))^(G(q))$ by characters $phi in op("Irr") W$, for a
system $cal(S)={G(q)}$ of finite groups with $B N$-pairs of type $(W,S)$ (see
the summary following @th:character-value-reduction-centralizer-levi).

#theorem(title: [Curtis @bib:Curtis1980a])[
  Let $epsilon$ denote the sign character of $W$ (see
  @def:coxeter-sign-representation). Then we have
  $ D_G zeta_(phi,q)=zeta_(epsilon phi,q), $
  for all irreducible characters ${zeta_(phi,q)}$ in $(1_(B(q)))^(G(q))$ and all
  $G(q)in cal(S)$.
] <th:principal-series-duality-sign-twist>
#idx("Sign representation", target: [@th:principal-series-duality-sign-twist])

#proof[
  By @prop:character-duality-cuspidal-series and
  @cor:character-duality-signed-irreducible-permutation, it is sufficient to
  show that for all $phi in op("Irr") W$, we have
  $ (D_G zeta_(phi,q),zeta_(epsilon phi,q))=1. $
  <eq:principal-series-duality-sign-inner-product>
  We first prove that for all characters $phi,phi' in op("Irr") W$ and
  $J subset.eq S$, the following
  #source(712)
  statement holds:
  $
    (R_(L_J)^G T_(L_J)^G zeta_(phi,q),zeta_(phi',q))_(G(q))
    =((lr(phi |)_(W_J))^W,phi')_W.
  $
  <eq:principal-series-truncation-weyl-multiplicity>
  To prove @eq:principal-series-truncation-weyl-multiplicity, apply
  @prop:truncation-induction-basic-properties and
  @lem:principal-series-levi-constituents to obtain
  $
    T_(L_J)^G zeta_(phi,q)=sum_(psi in op("Irr") W_J)
    (zeta_(phi,q),R_(L_J)^G eta_(psi,q))eta_(psi,q),
  $
  where ${eta_(psi,q)}$ are the irreducible characters in
  $(1_(B_J lr((q))))^(L_J lr((q)))$ parametrized by the characters
  $psi in op("Irr") W_J$, as in §~@ss:character-value-formulas. It follows that
  the left side of @eq:principal-series-truncation-weyl-multiplicity is given by
  $
    sum_(psi in op("Irr") W_J)(zeta_(phi,q),R_(L_J)^G eta_(psi,q))
    (R_(L_J)^G eta_(psi,q),zeta_(phi',q)).
  $
  By Theorem~@th:principal-series-character-value-weyl-reduction, this
  expression equals
  $ sum_(psi in op("Irr") W_J)(phi,psi^W)(psi^W,phi'), $
  which becomes
  $
    (sum_(psi in op("Irr") W_J)(phi,psi^W)psi^W,phi')
    =((sum_(psi in op("Irr") W_J)(lr(phi |)_(W_J),psi)psi)^W,phi'),
  $
  using Frobenius reciprocity. Thus
  @eq:principal-series-truncation-weyl-multiplicity follows. We now have
  $
    & (D_G zeta_(phi,q),zeta_(epsilon phi,q))
      =sum_(J subset.eq S)(-1)^(abs(J))((lr(phi |)_(W_J))^W,epsilon phi) \
    & =(sum_(J subset.eq S)(-1)^(abs(J))(lr(phi |)_(W_J))^W,epsilon phi)
      =(epsilon phi,epsilon phi)=1,
  $
  by @eq:principal-series-truncation-weyl-multiplicity and
  @prop:coxeter-sign-restriction-induction, using the definition of $D_G$. This
  establishes @eq:principal-series-duality-sign-inner-product and the theorem.
]

Now let us assume that @th:generic-degree-polynomiality applies to the system
$cal(S)$. Then for each $phi in op("Irr") W$ there exists a polynomial
$F_phi=F_phi lr((u))$ with rational coefficients, such that
$ deg zeta_(phi,q)=F_phi lr((q))quad "for all" q. $
We shall compare the generic degree polynomials $F_phi$ and $F_(epsilon phi)$,
for each $phi in op("Irr") W$. By
Theorem~@th:principal-series-duality-sign-twist, this information will describe
$deg zeta_(phi,q)$ and $deg D_(G(q)) lr((zeta_(phi,q)))$ for each $q$ (see
@th:duality-character-degree-unipotent-sums,
part~@case:duality-degree-prime-to-p-part).

Let $u$ be an indeterminate over $QQ$, $R=QQ[u]$, $K=QQ(u)$, $K^*$ an algebraic
closure of $K$, and let $A$ be the generic algebra of the Coxeter system $(W,S)$
associated with $cal(S)$. Then $A$ is an algebra over the ring
$QQ[u_1,dots,u_n]$, where $u_i=u^(c_i)$ and the ${c_i}$ are the index parameter
of $cal(S)$ (see @def:bn-pair-group-system).

#source(713)
Let $J_K$ be the involutory automorphism of $K$ that sends $u$ to $u^(-1)$, and
let $J_(K^*)$ be some fixed extension of $J_K$ to an involution of $K^*$. It is
then readily shown that there exists an involution of rings $J:A^K arrow A^K$,
given by
$
  J(sum xi_w e_w)=sum J_K lr((xi_w))op("SGN")(e_w)
  J_K lr((op("IND")e_w))e_w,
$
where $op("SGN")$ and $op("IND")$ are as defined in
@prop:generic-index-sign-homomorphisms, and the coefficients ${xi_w:w in W}$ are
in $K$. To see this, we observe that $J$ is a semilinear automorphism of the
vector space $A^K$, preserving the defining relations of $A$ given in
@prop:generic-coxeter-algebra-presentation.

It is also easily shown, using the discussion in Volume I,
§~@i:ss:splitting-fields, following @i:eq:galois-conjugate-representation, that
$J$ defines a permutation $mu arrow mu^J$ of the irreducible characters ${mu}$
of $A^(K^*)$, given by
$ mu^J lr((a))=J_(K^*) lr((mu(J(a)))),quad "for" a in A. $
In particular, we have
$ mu^J lr((e_w))=op("SGN")(e_w)op("IND")(e_w)J_(K^*) lr((mu(e_w))) $
for each basis element $e_w$. Using these ideas, we shall prove:

#theorem(title: [Green @bib:Green1970])[
  Let $F_phi lr((u))in QQ[u]$ be the generic degree polynomial associated with
  $phi in op("Irr") W$. Then we have
  $ F_(epsilon phi)=u^N F_phi lr((u^(-1))), $
  where $N$ is the integer defined by $u^N=op("IND")(e_(w_0))$, and $w_0$ is the
  element of maximal length in $W$.
] <th:generic-degree-duality-reciprocity>
#idx("Generic degree", target: [@th:generic-degree-duality-reciprocity])

#proof[
  Since we are assuming @th:generic-degree-polynomiality, we have
  $
    F_phi lr((u))=(P(u)deg phi)/
    (sum_(w in W)(op("IND")e_w)^(-1)mu_phi lr((e_w))
    mu_phi lr((e_(w^(-1))))),
  $
  where $mu_phi$ is the irreducible character of $A^(K^*)$ corresponding to
  $phi$. Clearly $u^N J_K lr((P(u)))=u^N P(u^(-1))=P(u)$, since
  $P(u)=sum_(w in W)op("IND")e_w$. By the remark preceding the theorem, the
  irreducible character of $A^(K^*)$ corresponding to $epsilon phi$ is
  $(mu_phi)^J$, and hence $F_(epsilon phi)$ is given by the same formula as
  $F_phi$, with $mu_phi$ replaced by $mu_phi^J$. The proof now follows from a
  simple calculation, using the definition of $(mu_phi)^J$.
]

=== The Values of the Steinberg Character <ss:steinberg-character-values>

In this subsection, we evaluate the Steinberg character $op("St")_G$ of a finite
group with a split $B N$-pair of characteristic $p$. The method we follow was
communicated to us by D. Alvis, and is based on the fact that truncation
intertwines duality (see @th:character-duality-truncation-intertwining and
@cor:steinberg-character-truncation). Using the theory of algebraic groups,
Steinberg (@bib:Steinberg1968, (15.5)) calculated $op("St")_G lr((x))$,
$x in G$, up to sign. Another approach to the calculation of
$op("St")_G lr((x))$, including the sign, is given in the context of homology
#source(714)
representations of reductive algebraic groups over finite fields, by
Curtis–Lehrer–Tits @bib:Curtis1980 (see
§~@ss:combinatorial-building-steinberg-representation).

The evaluation of irreducible characters of $G$ depends, in general, on detailed
information about conjugacy classes, which is available only in the context of
algebraic groups (see Springer–Steinberg @bib:Springer1970). Nevertheless, the
following result can be proved in the present context, and has applications to
the $p$-modular representation theory of $G$ and, in a sharpened form, to the
character theory of reductive algebraic groups over finite fields (see
Deligne–Lusztig @bib:DeligneLusztig1976).

As usual in this section, $G$ denotes a finite group with a split $B N$-pair of
characteristic $p$, $W$ the Weyl group of $G$, $S$ the set of distinguished
generators of $W$, and $op("St")_G$ the Steinberg character of $G$, given by the
formula
$ op("St")_G=sum_(J subset.eq S)(-1)^(abs(J))(1_(P_J))^G $
<eq:steinberg-character-alternating-parabolic-induction>
(see @th:steinberg-character-sign-correspondence). For each $J subset.eq S$, we
let $P_J=L_J V_J$ be the Levi decomposition of the parabolic subgroup $P_J$, as
in @th:split-bn-parabolic-levi-decomposition, with $V_J=O_p lr((P_J))$, and
$L_J$ a finite group with a split $B N$-pair of characteristic $p$, whose Weyl
group is $W_J$.
#idx(
  "Steinberg representation",
  target: [@eq:steinberg-character-alternating-parabolic-induction],
)

We also recall that each element $x in G$ can be expressed uniquely as a
commuting product $x=s u$ of a $p'$-element $s$ and a $p$-element $u$. We denote
the set of $p'$-elements in a group $H$ by $H_(p')$, and will sometimes write
$x=x_(p')x_p$, with $x_(p')=s$, $x_p=u$, as above.

#theorem[
  Let $G$ be a finite group with a split $B N$-pair of characteristic $p$, and
  let $op("St")_G$ be the Steinberg character of $G$. Then
  $
    op("St")_G lr((1))=abs(G)_p,quad "and"
    op("St")_G lr((x))=0quad "if" x in.not G_(p').
  $
  For each $s in G_(p')$, let $J$ be a subset of $S$ such that $s$ is conjugate
  to an element in $L_J$, but not to any element in $L_K$, for $K subset J$.
  Then
  $ op("St")_G lr((s))=(-1)^(abs(J))abs(C_G lr((s)))_p. $
] <th:steinberg-character-values-centralizers>

We begin the proof with a lemma that is a special case of the conjugacy part of
the Schur–Zassenhaus Theorem (see @i:th:schur-zassenhaus). Our self-contained
proof is due to Alvis.

#lemma[
  Let $p$ be a prime, and let the finite group $H$ be a semidirect product
  $H=V ⋊ L$, where $V$ is a $p$-subgroup. Then for all $l in L$ and $v in V$, we
  have
  $ (l v)_(p') =_V l_(p'), $
  that is, the $p'$-parts of $l v$ and $l$ are $V$-conjugate.
] <lem:semidirect-p-group-prime-to-p-parts-conjugate>

#proof[
  We may assume that $L=lr(chevron.l l chevron.r)$. Suppose first that there
  exists a nontrivial proper normal subgroup $V_1 ⊴ V$ such that
  $l V_1 l^(-1)=V_1$. Then $V_1 ⊴ H$, and we set $H_1=V_1 ⋊ L$, and
  $overline(H)=H slash V_1$. Then $overline(H)=overline(V)⋊overline(L)$, where
  $overline(H)=H slash V_1$, $overline(V)=V slash V_1$,
  #source(715)
  and $overline(L)=L V_1 slash V_1$. As an induction hypothesis, assume the
  lemma holds for $overline(H)$ and $H_1$. Let $h arrow overline(h)$ be the
  natural map from $H$ to $overline(H)$. Then clearly
  $ (overline(l v))_(p')=overline((l v)_(p')), $
  and it follows that
  $ (l v)_(p') =_V l_(p')u quad "for some" u in V_1. $
  But then $l_(p')u=(l_(p')u)_(p')$ and $l_(p')$ are $V_1$-conjugate in $H_1$,
  and so $(l v)_(p')$ and $l_(p')$ are $V$-conjugate, as required.

  It remains to check the minimal situation, in which $l$ normalizes no
  nontrivial proper normal subgroup of $V$. Then $C_V lr((l))=V$ or $1$. In the
  first case we have $(l v)_(p')=l_(p')$, and the result holds trivially. In the
  second case, where $C_V lr((l))=1$, the map $v_1 arrow l^(-1)v_1^(-1)l v_1$ is
  a bijection of $V$, since $V$ is finite. In particular,
  $v=l^(-1)v_1^(-1)l v_1$ for some $v_1 in V$, and hence $l v =_V l$. Then
  $(l v)_(p') =_V l_(p')$, and the proof is complete.
]

#proof(head: emph[Proof of @th:steinberg-character-values-centralizers.])[
  By @prop:split-bn-pair-order-sylow-steinberg,
  part~@case:split-bn-steinberg-p-part-degree, we have $op("St")_G 1=abs(G)_p$.
  Then $op("St")_G x=0$ for all $x in.not G_(p')$. This follows either from
  Gallagher's Theorem~@i:th:gallagher-character-vanishing (in the context of
  complex-valued characters of $G$) or by
  @i:prop:defect-zero-character-projective-simple and
  @i:th:projective-characters-supported-p-regular, using Brauer theory.

  Now consider an arbitrary $p'$-element $s in G$. We shall calculate
  $op("St")_G s$ in a series of steps.

  #case-list(
    prefix: "Step ",
    numbering: "1.",
    [#case[
      First assume that $s$ is not contained in any proper parabolic subgroup of
      $G$. Then $s x P_J!=x P_J$ for all $x in G$ and $J subset S$, and hence
      $(1_(P_J))^G lr((s))=0$ for all $J subset S$. By the alternating sum
      formula @eq:steinberg-character-alternating-parabolic-induction for
      $op("St")_G$, we obtain
      $
        op("St")_G lr((s))=(-1)^(abs(S))
        quad ("if" s in.not P "for all proper parabolic subgroups" P).
      $
    ] <case:steinberg-value-no-proper-parabolic>],
    [#case[
      Let $s in G_(p')$ be an arbitrary $p'$-element, and let $s$ be conjugate
      to an element in $L_J$, for some $J subset.eq S$, but not to an element in
      $L_K$, for $K subset J$. Then
      $ op("St")_G s=(-1)^(abs(J))abs(V_J inter C_G lr((s))). $
      <eq:steinberg-value-minimal-levi-unipotent-centralizer>
      We first apply @cor:steinberg-character-truncation, and obtain
      $
        op("St")_(L_J) lr((s))=T_(L_J)^G op("St")_G lr((s))
        =abs(V_J)^(-1)sum_(v in V_J)op("St")_G lr((s v)).
      $
      <eq:steinberg-value-truncation-average>
      We now calculate both sides of @eq:steinberg-value-truncation-average
      separately. Beginning with the left side, we note first that the standard
      parabolic subgroups of $L_J$ all have the form $L_J inter P_K$, for
      $K subset.eq J$, by @prop:standard-levi-parabolic-correspondence, and that
      each such subgroup has the Levi decomposition
      $ L_J inter P_K=L_K lr((V_K inter L_J)), $
      also by @prop:standard-levi-parabolic-correspondence. It follows that no
      conjugate of $s$ is contained in a proper parabolic subgroup of $L_J$,
      since otherwise $s$ is conjugate to an element of $L_K$ for $K subset J$,
      by Lemma~@lem:semidirect-p-group-prime-to-p-parts-conjugate, applied to
      the semidirect product $L_K lr((V_K inter L_J))$. We conclude
      #source(716)
      that
      $ op("St")_(L_J) s=(-1)^(abs(J)), $
      by Step~@case:steinberg-value-no-proper-parabolic applied to the group
      $L_J$.

      Now consider the right side of @eq:steinberg-value-truncation-average. If
      $op("St")_G lr((s v))!=0$ for some $v in V_J$, then $s v in G_(p')$, and
      hence $s v =_(V_J) s$ by
      @lem:semidirect-p-group-prime-to-p-parts-conjugate. Then the right side of
      @eq:steinberg-value-truncation-average becomes
      $ abs(V_J)^(-1)m dot op("St")_G s, $
      where
      $ m=op("card"){s v in s V_J:s v =_(V_J) s}. $
      Now any $V_J$-conjugate of $s$ can be written in the form
      $ v_1 s v_1^(-1)=s(s^(-1)v_1 s v_1^(-1)), $
      where $s^(-1)v_1 s v_1^(-1)in V_J$, since $s$ normalizes $V_J$. Thus $m$
      is the number of all $V_J$-conjugates of $s$, which equals
      $ abs(V_J)abs(V_J inter C_G lr((s)))^(-1). $
      Upon substituting this information in
      @eq:steinberg-value-truncation-average, we obtain
      @eq:steinberg-value-minimal-levi-unipotent-centralizer, as required.
    ] <case:steinberg-value-minimal-levi-average>],
    [#case[
      It is now sufficient to prove that for $s$ as in
      Step~@case:steinberg-value-minimal-levi-average, we have
      $ abs(V_J inter C_G lr((s)))=abs(C_G lr((s)))_p. $
      <eq:minimal-levi-unipotent-centralizer-sylow-order>
      Since $V_J$ is a $p$-group, $abs(V_J inter C_G lr((s)))$ clearly divides
      $abs(C_G lr((s)))_p$. On the other hand, since $op("St")_G in op("Irr") G$
      by @th:steinberg-character-sign-correspondence, part (i), we have
      $
        (abs(G ":" C_G lr((s)))op("St")_G s)/(op("St")_G 1)
        =abs(G)_(p')/abs(C_G lr((s)))_(p') dot
        (op("St")_G s)/abs(C_G lr((s)))_p.
      $
      <eq:steinberg-central-character-integrality-factorization>
      This is an algebraic integer, by
      @i:prop:central-character-values-integral. It also lies in $QQ$ by
      @eq:steinberg-value-minimal-levi-unipotent-centralizer, and hence is a
      rational integer. It follows that the $p$-part of
      @eq:steinberg-central-character-integrality-factorization is also a
      rational integer, and hence $abs(C_G lr((s)))_p$ divides $op("St")_G s$.
      This completes the proof of
      @eq:minimal-levi-unipotent-centralizer-sylow-order, and establishes the
      theorem.
    ] <case:steinberg-value-centralizer-p-part>],
  )
]
