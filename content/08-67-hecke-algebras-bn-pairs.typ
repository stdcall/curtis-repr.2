#import "main-defs.typ": *
#import "statements.typ": *

== The Hecke Algebra $cal(H)(G,B)$ and the Decomposition of $(1_B)^G$
<sec:hecke-algebras-bn-pairs>

In this section, we continue to explore the connections between the
representations of a finite group of Lie type $G$ and the representations of the
Weyl group $W$ of $G$. This time we consider the decomposition of the
permutation representation of $G$ on the cosets of a Borel subgroup $B$, through
the study of the Hecke algebra $cal(H)(G,B,1_B)$, denoted here by $cal(H)$. It
is shown that $cal(H)$ has a presentation as a $CC$-algebra with generators and
relations that are the exact counterparts of the defining relations of $W$ given
by the Coxeter system $(W,S)$. This fact is of crucial importance for the
construction of representations of $cal(H)$ and the corresponding
representations of $G$ (see §~@i:ss:hecke-algebras). In particular, the
representations of $cal(H)$ are calculated for the case of a $B N$-pair of rank
$2$, and applied to the incidence algebra of a generalized polygon, a proof of
the Feit–Higman theorem on generalized polygons, and a construction of the
reflection representation of the Hecke algebra $cal(H)$.

=== The Structure of the Hecke Algebra $cal(H)(G,B)$
<ss:hecke-algebra-bn-pair-structure>

Throughout this section, $G$ denotes a finite group with a $B N$-pair, $W$ the
Weyl group of $G$, and $S$ the set of distinguished generators of $W$. Let
$ G = union.dot.big_(w in W) B w B $
be the Bruhat decomposition of $G$ with respect to a Borel subgroup $B$ (see
@th:bruhat-decomposition). We recall that the pair $(W,S)$ is a Coxeter system
(see @th:bn-pair-weyl-coxeter-system and @def:finite-coxeter-system). Thus the
group $W$ has a presentation
$
  W = lr(
    chevron.l
    s_1, dots, s_n : (s_i s_j)^(m_(i j)) = 1
    "for all" i, j
    chevron.r
  ),
$
where $S = {s_1,dots,s_n}$, and the ${m_(i j)}$ are positive integers such that
$m_(i i)=1$ and $m_(i j)=m_(j i)$ for all $i,j$. This means that in order to
construct representations

#source(626)
$ T : W arrow GL(M) $
on a vector space $M$, it is sufficient to find elements ${T_i}_(1 <= i <= n)$
in $GL(M)$ satisfying the defining relations of $W$:
$ T_i^2 = 1, quad (T_i T_j)^(m_(i j)) = 1 quad "for all" i,j. $
Then the map $s_i arrow T_i$, $1 <= i <= n$, can be extended to a representation
$T$.

Our aim is to prove that the Hecke algebra $cal(H)(G,B)=cal(H)(G,B,1_B)$ has a
presentation, as an algebra, similar to the presentation of the group $W$. Using
this presentation, representations of $cal(H)(G,B)$ can be constructed, and used
to decompose the permutation representation $(1_B)^G$, by the methods of
§~@i:ss:hecke-algebras.

We shall denote the Hecke algebra $cal(H)(G,B)$ by $cal(H)$. Recall that
$cal(H)$ is a semisimple subalgebra of the complex group algebra $CC G$, defined
as
$ cal(H) = e CC G e, $
where $e = abs(B)^(-1) sum_(b in B) b$ is the idempotent in $CC B$ such that the
left ideal $CC G e$ affords the permutation representation $(1_B)^G$. The
algebra $cal(H)$ is isomorphic to the opposite algebra of the centralizer ring
$End_(CC G) CC G e$. Thus the representations and characters of $cal(H)$ are
closely related to the characters $zeta in Irr G$ for which
$(zeta,(1_B)^G) != 0$ (see Theorem @i:th:hecke-character-correspondence).

#idx("Hecke algebra H(G,B)")
#nidx("$cal(H)(G,B)$", "Hecke algebra")

The first step in analyzing the structure of $cal(H)$ is to examine the
_standard basis_ of $cal(H)$, consisting of the elements
$
  a_D = abs(B)^(-1) sum_(x in D) x, quad
  D in B backslash G "/" B quad ("see" #[@i:prop:permutation-hecke-formulas]).
$
Since there is a bijective map $w arrow.l.r B w B$ from $W$ to the double cosets
$B backslash G "/" B$, we shall label the standard basis elements by the
elements of $W$, and denote them by ${a_w}_(w in W)$. Their multiplication will
be derived from the results in §~@ss:bruhat-decomposition.

For each $w in W$, we define its _index_
$ op("ind") w = [B : attach(B, tl: w) inter B], $
using our convention from §~@ss:bruhat-decomposition that $attach(B, tl: w)$
stands for $attach(B, tl: dot(w))$, where $dot(w)$ is a coset representative in
$N$ corresponding to an element $w in N slash T$. In particular, the _index
parameters_ of $G$ are defined to be the numbers
$ q_i = op("ind") s_i, quad 1 <= i <= n, $ <eq:bn-pair-index-parameters>
where $S={s_1,dots,s_n}$ is the set of distinguished generators of $W$.

As in §§~@sec:root-systems-reflection-groups and @sec:finite-groups-bn-pairs,
let $l(w)$ denote the length function on the Coxeter group $W$. We now have:

#theorem[
  (Iwahori @bib:Iwahori1964). The multiplication of the standard basis elements
  ${a_w = abs(B)^(-1) sum_(x in B w B) x, w in W}$ of $cal(H)$ satisfies
  $ a_(s_i) a_w = a_(s_i w) quad "if" l(s_i w) > l(w), $
  #source(627)
  and
  $
    a_(s_i) a_w = q_i a_(s_i w) + (q_i-1) a_w
    quad "if" l(s_i w) < l(w),
  $
  for all $s_i in S$ and $w in W$, where the ${q_i}$ are the index parameters
  given in @eq:bn-pair-index-parameters.
] <th:iwahori-hecke-basis-multiplication>
#idx("Iwahori's Theorem", target: [@th:iwahori-hecke-basis-multiplication])

#proof[
  Multiplication in $cal(H)$ is given by
  $ a_u a_v = sum_(w in W) mu_(u v w) a_w quad "for" u,v in W, $
  where the $mu$'s are structure constants satisfying
  $ mu_(u v w) = abs(B)^(-1) abs(B u B inter w (B v B)^(-1)), $
  by @i:prop:permutation-hecke-formulas.

  In case $l(s_i w)>l(w)$, we have $s_i B w subset.eq B s_i w B$ by
  @prop:bruhat-length-increasing-product, so the product $a_(s_i) a_w$ is
  supported on the double coset $B s_i w B$. We therefore have
  $ a_(s_i) a_w = mu a_(s_i w), $
  where $mu$ is the structure constant
  $
    mu = abs(B)^(-1) abs(B s_i B inter s_i w B w^(-1) B)
    = abs(B)^(-1) abs(s_i B s_i B inter w B w^(-1) B).
  $
  Since $s_i B s_i subset.eq B union B s_i B$ by @eq:bn-pair-double-coset-axiom,
  and $B subset.eq w B w^(-1) B$, the first statement of the theorem (that
  $mu=1$) will follow once we prove that
  $
    B s_i B inter w B w^(-1) B = emptyset
    quad "if" l(s_i w)>l(w).
  $
  Suppose this is false, and let
  $ w = s_(j(1)) dots s_(j(p)), quad s_(j(k)) in S, quad 1 <= k <= p. $
  By the first formula in the proof of @prop:bn-pair-exchange-condition, we have
  $ B s_i B = B w y B, $
  where $y$ is a product of some factors of $w^(-1)$, so $l(y)<=l(w)$. By
  @th:bruhat-decomposition we have
  $ s_i = w y, quad "and" quad w^(-1) s_i = y. $
  Thus if $l(w)=p$, so $s_(j(1)) dots s_(j(p))$ is a reduced product, then
  $l(w^(-1) s_i)=l(s_i w)<=p$, contrary to assumption. Thus $mu=1$, proving the
  first formula.

  We next establish
  $
    a_(s_i)^2 = q_i a_1 + (q_i-1) a_(s_i) quad "for all" s_i in S.
  $ <eq:hecke-generator-quadratic-relation>
  #source(628)
  Since
  $ (B s_i B)(B s_i B) subset.eq B union B s_i B, $
  we have
  $ a_(s_i)^2 = eta a_1 + lambda a_(s_i), quad eta,lambda in CC, $
  where the structure constant $eta$ satisfies
  $
    eta = abs(B)^(-1) abs(B s_i B inter B s_i B)
    = op("ind") s_i = q_i.
  $
  By Exercise~@i:exc:hecke-index-homomorphism, the map
  $op("ind"):cal(H) arrow CC$ is a homomorphism of algebras. Upon applying
  $op("ind")$ to the formula for $(a_(s_i))^2$, we obtain
  $ q_i^2 = q_i + lambda q_i, $
  since $eta=q_i$ and $op("ind") a_1=1$. It follows that $lambda=q_i-1$, proving
  @eq:hecke-generator-quadratic-relation.

  Finally, let $l(s_i w)<l(w)$, and put $w'=s_i w$. Then $l(s_i w')>l(w')$, and
  by the first part of the proof we have
  $ a_w = a_(s_i) a_(w'). $
  Then
  $
    a_(s_i) a_w = a_(s_i)^2 a_(w')
    = q_i a_(w') + (q_i-1) a_(s_i) a_(w')
    = q_i a_(s_i w) + (q_i-1) a_w,
  $
  completing the proof of the theorem.
]

#corollary[
  The Hecke algebra $cal(H)$ is generated by elements
  ${1=a_1,a_(s_1),dots,a_(s_n)}$, where $S={s_1,dots,s_n}$. These generators
  satisfy the quadratic relations
  $ a_(s_i)^2 = q_i 1 + (q_i-1) a_(s_i), quad 1 <= i <= n, $
  and the homogeneous relations
  $
    (a_(s_i) a_(s_j))^(k_(i j)) = (a_(s_j) a_(s_i))^(k_(i j))
    quad "if" m_(i j)=2 k_(i j),
  $
  $
    (a_(s_i) a_(s_j))^(k_(i j)) a_(s_i)
    = (a_(s_j) a_(s_i))^(k_(i j)) a_(s_j)
    quad "if" m_(i j)=2 k_(i j)+1,
  $
  where $m_(i j)$ is the order of $s_i s_j$ in $W$.
] <cor:hecke-generator-braid-relations>

#corollary[
  If $s_i$ is conjugate to $s_j$ in $W$, then $q_i=q_j$.
] <cor:conjugate-simple-reflections-equal-parameters>

The proofs of both corollaries are left as exercises.

#theorem[
  (Iwahori, Matsumoto). The generators and relations given in
  @cor:hecke-generator-braid-relations define a presentation of the Hecke
  algebra $cal(H)$.
] <th:iwahori-matsumoto-hecke-presentation>

#source(629)
#proof[
  We have to prove that if $A$ is an associative $CC$-algebra containing
  elements ${a_1,dots,a_n}$ satisfying the relations in
  @cor:hecke-generator-braid-relations, then there exists a homomorphism of
  algebras $f:cal(H) arrow A$ such that $f(a_(s_i))=a_i$, $1<=i<=n$. By
  Matsumoto's Theorem~@th:matsumoto-reduced-word-monoid, there exists a map
  $f':W arrow A$ such that $f'(s_i)=a_i$, $1<=i<=n$, and such that
  $ f'(s_(i(1)) dots s_(i(m))) = a_(i(1)) dots a_(i(m)) $
  for every reduced product $s_(i(1)) dots s_(i(m))$ of elements of $S$. Since
  the elements ${a_w}_(w in W)$ form a basis for $cal(H)$, there exists a linear
  map $f:cal(H) arrow A$ such that $f(a_w)=f'(w)$, for $w in W$. It is then
  sufficient to prove that
  $
    f(a_(s_i) a_w) = f(a_(s_i)) f(a_w)
  $ <eq:hecke-presentation-generator-multiplicativity>
  for all $s_i in S$ and $w in W$. We now imitate the last part of the proof of
  Theorem~@th:finite-reflection-group-coxeter-presentation. First assume
  $l(s_i w)>l(w)$. Then a reduced expression for $s_i w$ is obtained from a
  reduced expression for $w$ by left multiplication by $s_i$, and the result
  @eq:hecke-presentation-generator-multiplicativity follows by the definition of
  $f$, since $a_(s_i) a_w=a_(s_i w)$ by @th:iwahori-hecke-basis-multiplication.
  Next assume $l(s_i w)<l(w)$, and let $w'=s_i w$. Then $l(s_i w')>l(w')$, and
  by the first part of the proof, we have
  $ f(a_w)=f(a_(s_i) a_(w'))=f(a_(s_i)) f(a_(w')), $
  since $a_(s_i) a_(w')=a_w$ by @th:iwahori-hecke-basis-multiplication. By
  assumption, the elements $f(a_(s_i))$ also satisfy the quadratic relations in
  @cor:hecke-generator-braid-relations, whence
  $
    f(a_(s_i)) f(a_w) & = f(a_(s_i))^2 f(a_(w')), \
                      & = q_i f(a_(w'))+(q_i-1) f(a_(s_i)) f(a_(w')) \
                      & = q_i f(a_(s_i w))+(q_i-1) f(a_w)
  $
  by the first part of the proof again, since $l(s_i w')>l(w')$ and $w'=s_i w$.
  On the other hand,
  $ a_(s_i) a_w=q_i a_(s_i w)+(q_i-1) a_w $
  by @th:iwahori-hecke-basis-multiplication. We then obtain
  @eq:hecke-presentation-generator-multiplicativity, in this case, by applying
  $f$ to the last relation and comparing with the previous formula. This
  completes the proof.
]

#remark(numbered: false)[
  The quadratic relations
  $ a_(s_i)^2=q_i a_1+(q_i-1) a_(s_i), quad 1<=i<=n, $
  can also be expressed in the form
  $ (a_(s_i)-q_i)(a_(s_i)+1)=0, quad 1<=i<=n. $
  Thus in order to construct representations of the Hecke algebra $cal(H)$, it
  is sufficient
  #source(630)
  to map the generators to matrices $T_i$,
  $ a_(s_i) arrow T_i, quad 1<=i<=n, $
  such that each matrix $T_i$ is diagonalizable with eigenvalues either $q_i$ or
  $-1$, and such that these matrices satisfy the homogeneous relations. The
  simplest examples are the one-dimensional representations of $cal(H)$, one of
  which is the _index homomorphism_
  $ op("ind"):cal(H) arrow CC $
  defined by
  $ op("ind") a_(s_i)=q_i, quad 1<=i<=n. $
  #idx("Index homomorphism")
  Another one-dimensional representation is the _sign representation_
  $ op("sgn"):cal(H) arrow CC $
  defined by
  $ op("sgn") a_(s_i)=-1, quad 1<=i<=n. $
  #idx("Sign representation")
  By Exercise~@i:exc:hecke-index-homomorphism, the index homomorphism
  corresponds to the trivial representation $1_G$, according to
  @i:th:hecke-character-correspondence. We shall show in the next subsection
  that $op("sgn")$ corresponds to the Steinberg representation, defined in
  @def:steinberg-representation.
] <rem:hecke-representation-generator-criterion>

=== The Sign Representation of $cal(H)$ and the Steinberg Representation of $G$
<ss:hecke-sign-steinberg>

As in the previous subsection, $G$ denotes a finite group with a $B N$-pair,
with Borel subgroup $B$ and Weyl group $W$. We shall construct the character of
the representation of $G$ corresponding to the sign representation of the Hecke
algebra $cal(H)=cal(H)(G,B,1_B)$, defined in
§~@ss:hecke-algebra-bn-pair-structure. It will turn out to be the character of
the Steinberg representation $upright("St")_G$, for which a construction was
given in §~@ss:combinatorial-building-steinberg-representation using homology
representations. The discussion to follow, which establishes further properties
of $upright("St")_G$, is independent of homology representations, except that we
require Solomon's formula @cor:solomon-sign-character-formula for the sign
representation of $W$ (see also
Exercise~@exc:solomon-formula-hyperplane-arrangement).

#lemma[
  Let $G$ be a transitive permutation group on each of the two finite sets $X$
  and $Y$, and let $H$ and $K$ be stabilizers of a point in $X$ and $Y$,
  respectively. Let $psi$ and $theta$ be the permutation characters of $G$
  defined by the permutation representations on $X$ and $Y$, respectively. Then
  $ (psi,theta)=abs(H backslash G "/" K). $
] <lem:permutation-character-double-coset-inner-product>
#proof[
  By Proposition~@i:prop:orbits-stabilizers, there are isomorphisms of $G$-sets
  $X tilde.equiv G slash H$ and $Y tilde.equiv G slash K$, and we have
  $psi=(1_H)^G$, $theta=(1_K)^G$. The number of double cosets
  #source(631)
  $abs(H backslash G "/" K)$ is the number of $H$-orbits in $G slash K$. Thus
  $
    abs(H backslash G "/" K)=(1_H,(1_K)^G |_H)_H
    =((1_H)^G,(1_K)^G)_G=(psi,theta)_G,
  $
  by Frobenius reciprocity @i:th:frobenius-class-functions, completing the
  proof. (The result is also a consequence of the intertwining number theorem
  @i:th:intertwining-number. Another proof is outlined in
  Exercise~@i:exc:permutation-character-orbits.)
]

The next result shows how to use the lemma to construct certain virtual
characters of $G$ from virtual characters of $W$, using information about double
cosets of parabolic subgroups (see @th:bn-pair-parabolic-double-cosets). As in
§~@ss:bn-pair-parabolic-subgroups, we denote standard parabolic subgroups of $W$
by ${W_J}_(J subset.eq S)$, and the corresponding parabolic subgroups of $G$ by
${P_J}_(J subset.eq S)$.

#proposition[
  The correspondence
  $
    xi=sum_(J subset.eq S) n_J (1_(W_J))^W
    arrow hat(xi)=sum_(J subset.eq S) n_J (1_(P_J))^G,
    quad "where each" n_J in ZZ,
  $
  defines a mapping of virtual characters of $W$ to virtual characters of $G$
  that preserves scalar products. Thus
  $ (xi,eta)_W=(hat(xi),hat(eta))_G $
  for two virtual characters $xi,eta in op("ch") CC W$ of the above form. In
  particular,
  $ xi in Irr W => plus.minus hat(xi) in Irr G. $
] <prop:parabolic-permutation-character-isometry>
#proof[
  By @th:bn-pair-parabolic-double-cosets, there is a bijection
  $
    W_I backslash W "/" W_J arrow.l.r P_I backslash G "/" P_J
    quad "for all" I,J subset.eq S.
  $
  Moreover, by Lemma~@lem:permutation-character-double-coset-inner-product, we
  have
  $
    (xi,xi')_W=sum_(I,J subset.eq S) n_I n'_J ((1_(W_I))^W,(1_(W_J))^W)
    =sum_(I,J subset.eq S) n_I n'_J abs(W_I backslash W "/" W_J),
  $
  while
  $
    (hat(xi),hat(xi'))_G
    =sum_(I,J subset.eq S) n_I n'_J abs(P_I backslash G "/" P_J),
  $
  for virtual characters $xi,xi'$ as above. In particular,
  $
    xi=xi' <=> (xi-xi',xi-xi')_W=0
    <=> (hat(xi)-hat(xi'),hat(xi)-hat(xi'))_G=0 <=> hat(xi)=hat(xi').
  $
  It follows that $xi arrow hat(xi)$ is a bijection for virtual characters of
  the above form, and preserves scalar products. This completes the proof.
]

#source(632)
#remark(numbered: false)[
  If $G=GL_(n+1) lr((FF_q))$, then by §~@ss:bn-pair-examples, we have
  $W tilde.equiv S_(n+1)$. In this case, a result of Frobenius (see
  §~@ss:solomon-symmetric-group-characters) asserts that every irreducible
  character of $W$ is a $ZZ$-linear combination of the characters $(1_(W_J))^W$,
  $J subset.eq S$. Thus @prop:parabolic-permutation-character-isometry provides
  the basis for an explicit construction, due to Steinberg @bib:Steinberg1951,
  of all characters $zeta in Irr G$ such that $(zeta,(1_B)^G)>0$. On the other
  hand, for a Weyl group of type $B_2$ (the dihedral group of order $8$), only
  the trivial character and the sign character can be expressed in this way.
  Nevertheless, the preceding result always produces at least one nontrivial
  irreducible character of $G$.
] <rem:parabolic-character-isometry-symmetric-group>

#theorem[
  Let $G$ be a finite group with a $B N$-pair, and Coxeter system $(W,S)$, and
  let $upright("St")_G$ be the virtual character defined by
  $ upright("St")_G=sum_(J subset.eq S) (-1)^abs(J) (1_(P_J))^G. $
  Then the following statements hold:
  #case-list(
    numbering: "(i)",
    [#case[
      $upright("St")_G in Irr G$, and
      $deg upright("St")_G=[B:B inter attach(B, tl: w_0)]$, where $w_0$ is the
      unique element of maximal length in $W$ (see
      @th:reflection-length-cancellation-exchange,
      part~@case:longest-reflection-group-element).
    ] <case:steinberg-character-irreducible-degree>],
    [#case[
      $upright("St")_G$ satisfies the conditions $(upright("St")_G,(1_B)^G)=1$,
      and $(upright("St")_G,(1_(P_J))^G)=0$ for all $J != emptyset$. Moreover,
      $upright("St")_G$ is characterized by these multiplicities: If
      $zeta in Irr G$ satisfies $(zeta,(1_B)^G)=1$ and $(zeta,(1_(P_J))^G)=0$
      for all $J != emptyset$, then $zeta=upright("St")_G$.
    ] <case:steinberg-character-parabolic-multiplicities>],
    [#case[
      The restriction $upright("St")_G |_(cal(H))$ of $upright("St")_G$ to the
      Hecke algebra $cal(H)=cal(H)(G,B,1_B)$ is the sign character $op("sgn")$
      of $cal(H)$, given by $op("sgn")(a_(s_i))=-1$ for all $s_i in S$.
    ] <case:steinberg-character-hecke-sign>],
  )
] <th:steinberg-character-sign-correspondence>
#idx(
  "Steinberg representation",
  target: [@th:steinberg-character-sign-correspondence],
)

#proof[
  #case-list(
    numbering: "(i)",
    [#case[
      By @cor:solomon-sign-character-formula (see also
      Exercise~@exc:solomon-formula-hyperplane-arrangement), the sign character
      of $W$ is given by the formula
      $ epsilon=sum_(J subset.eq S) (-1)^abs(J) (1_(W_J))^W. $
      By Proposition~@prop:parabolic-permutation-character-isometry, it follows
      that $upright("St")_G$, as defined above, is a virtual character such that
      $plus.minus upright("St")_G in Irr G$. We now calculate the degree
      $upright("St")_G lr((1))$, and show, in particular, that
      $upright("St")_G lr((1))>0$, which implies that
      $upright("St")_G in Irr G$. We use the formula
      $
        upright("St")_G lr((1))
        =sum_(J subset.eq S) (-1)^abs(J) [G:P_J],
      $
      and begin by showing that for each $J subset.eq S$, the index $[G:P_J]$ is
      given by
      $
        [G:P_J]=sum_(x in D_(emptyset J)) [B:B inter attach(B, tl: x)],
      $ <eq:parabolic-index-distinguished-cosets>
      where $D_(emptyset J)$ is a set of distinguished double coset
      representatives (see
      @def:distinguished-parabolic-double-coset-representative). It follows from
      @th:bn-pair-parabolic-double-cosets that
      $ G=union.dot.big_(x in D_(emptyset J)) B x P_J. $
      #source(633)
      By a familiar computation (see
      Proposition~@i:prop:orbits-stabilizers(ii)), we then have
      $
        abs(B x P_J slash P_J)=[B:B inter attach(P_J, tl: x)],
        quad x in D_(emptyset J).
      $
      To obtain @eq:parabolic-index-distinguished-cosets, it thus suffices to
      show that
      $
        B inter attach(P_J, tl: x)=B inter attach(B, tl: x)
        quad "for all" x in D_(emptyset J).
      $
      We have
      $ P_J=union.big_(w in W_J) B w B, $
      so @eq:parabolic-index-distinguished-cosets will follow if we can prove
      that
      $
        x B w B x^(-1) inter B=emptyset,
        quad "for" w in W_J, quad w != 1,
      $
      or equivalently, that
      $
        x B w B inter B x=emptyset, quad x in D_(emptyset J),
        quad w in W_J, quad w != 1.
      $
      By @prop:parabolic-double-coset-minimal-length we have $l(x w)=l(x)+l(w)$
      for all $w in W_J$ and for $x in D_(emptyset J)$, whence
      $x B w subset B x w B$. Consequently, $x B w B inter B x=emptyset$ for
      $w in W_J$, $w != 1$, by the uniqueness part of the Bruhat decomposition
      @th:bruhat-decomposition, completing the proof of
      @eq:parabolic-index-distinguished-cosets.

      Substituting @eq:parabolic-index-distinguished-cosets in the formula for
      $upright("St")_G lr((1))$, we obtain
      $
        upright("St")_G lr((1))=sum_(J subset.eq S) (-1)^abs(J)
        sum_(x in D_(emptyset J)) [B:B inter attach(B, tl: x)].
      $
      By @prop:parabolic-double-coset-minimal-length, it follows that an element
      $x in W$ belongs to $D_(emptyset J)$, for $J subset.eq S$, if and only if
      $l(x s_j)>l(x)$ $forall j in J$. Thus $[B:B inter attach(B, tl: x)]$
      appears in the formula for $upright("St")_G lr((1))$ exactly
      $sum_(J subset.eq R(x)) (-1)^abs(J)$ times, where
      $R(x)={s in S:l(x s)>l(x)}$. Moreover,
      $sum_(J subset.eq R(x)) (-1)^abs(J)=0$ for all $x in W$ such that
      $R(x) != emptyset$. We also have $R(x)=emptyset$ for the unique element
      $x=w_0$ of maximal length in $W$ (see
      @th:reflection-length-cancellation-exchange,
      part~@case:longest-reflection-group-element). For this element $w_0$, the
      contribution to $upright("St")_G lr((1))$ is
      $[B:B inter attach(B, tl: w_0)]$, and
      part~@case:steinberg-character-irreducible-degree is proved.
    ] <case:steinberg-proof-positive-degree>],
    [#case[
      The sign character $epsilon$ of $W$ has degree $1$, whence
      $(epsilon,1_({1})^W)=1$ since $1_({1})^W$ is the regular character of $W$.
      We also have $(epsilon,1_(W_J)^W)=0$ for $J != emptyset$, by Frobenius
      reciprocity, since $(epsilon|_(W_J),1_(W_J))_(W_J)=0$ if $J != emptyset$.
      We then apply the isometry of virtual characters given in
      Proposition~@prop:parabolic-permutation-character-isometry to obtain
      $
        (upright("St")_G,(1_B)^G)=1, quad
        (upright("St")_G,(1_(P_J))^G)=0, quad J != emptyset,
      $
      since $upright("St")_G$ corresponds to $epsilon$ under the map defined in
      @prop:parabolic-permutation-character-isometry.

      Now consider an arbitrary irreducible character $zeta$ of $G$ satisfying
      the conditions
      $ (zeta,(1_B)^G)=1, quad (zeta,(1_(P_J))^G)=0, quad J != emptyset. $
      #source(634)
      By the definition of $upright("St")_G$ in
      part~@case:steinberg-character-irreducible-degree, we have
      $
        (zeta,upright("St")_G)
        =lr((zeta,sum_(J subset.eq S) (-1)^abs(J) (1_(P_J))^G))=1.
      $
      Therefore $zeta=upright("St")_G$, completing the proof of
      part~@case:steinberg-character-parabolic-multiplicities.
    ] <case:steinberg-proof-multiplicity-characterization>],
    [#case[
      By @i:th:hecke-character-correspondence, the restriction
      $upright("St")_G |_(cal(H))$ of $upright("St")_G$ to the Hecke algebra
      $cal(H)$ is an irreducible character of degree
      $(upright("St")_G,(1_B)^G)=1$. In order to prove that
      $upright("St")_G |_(cal(H))$ is the sign character of $cal(H)$, it is
      sufficient to show that
      $ upright("St")_G lr((a_(s_i)))=-1 quad "for all" s_i in S. $
      By part~@case:steinberg-character-parabolic-multiplicities, we have
      $(upright("St")_G,(1_B)^G)=1$ and $(upright("St")_G,(1_(P_({s_i})))^G)=0$
      for all $s_i in S$. Then, by @i:prop:hecke-character-multiplicity, we
      obtain
      $
        upright("St")_G lr((e_B))=1 quad "and" quad
        upright("St")_G lr((e_(P_({s_i}))))=0, quad s_i in S,
      $
      where $e_B$ and $e_(P_({s_i}))$ are the idempotents affording the trivial
      representations of $B$ and $P_({s_i})$, respectively. Moreover,
      $ P_({s_i})=B union B s_i B. $
      Thus from $upright("St")_G lr((e_(P_({s_i}))))=0$ we have
      $upright("St")_G lr((sum_(x in P_({s_i})) x))=0$, whence
      $ upright("St")_G lr((sum_(b in B) b+sum_(x in B s_i B) x))=0. $
      Now
      $
        e_B=abs(B)^(-1) sum_(b in B) b, quad
        a_(s_i)=abs(B)^(-1) sum_(x in B s_i B) x, quad s_i in S,
      $
      so the preceding formula becomes
      $
        upright("St")_G lr((e_B))+upright("St")_G lr((a_(s_i)))=0
        quad "for all" s_i in S.
      $
      Therefore $upright("St")_G lr((a_(s_i)))=-1$ for all $s_i in S$,
      completing the proof.
    ] <case:steinberg-proof-corner-sign>],
  )
]

As an example, we shall calculate the degrees of the Steinberg representations
of the finite general linear groups, discussed in §~@ss:bn-pair-examples. The
result is as follows:

#proposition[
  Let $FF_q$ be a finite field of $q$ elements, where $q$ is a power of the
  prime $p$, and let $G=GL_(n+1) lr((FF_q))$. Then the degree of the Steinberg
  character of $G$ is given by
  $ upright("St")_G 1=q^(n(n+1)/2)=abs(G)_p. $
] <prop:general-linear-steinberg-degree>

#source(635)
#proof[
  It is sufficient to prove the first equality, since the second is a standard
  exercise in elementary group theory. By
  @th:steinberg-character-sign-correspondence, we have
  $ upright("St")_G lr((1))=[B:B inter attach(B, tl: w_0)], $
  where $w_0$ is the element of maximal length in the Weyl group. Thus
  $upright("St")_G lr((1))=op("ind") a_(w_0)$, where $a_(w_0)$ is the standard
  basis element corresponding to $w_0$ in the Hecke algebra
  $cal(H)=cal(H)(G,B,1_B)$. By @th:general-linear-bn-pair, the Weyl group of $G$
  is isomorphic to the symmetric group $S_(n+1)$, which is a g.g.r. associated
  with a root system $Delta$ of type $A_n$, by Exercise~@exc:type-a-root-system.
  Then $l(w_0)=abs(Delta_+)=n(n+1)/2$ by
  @th:reflection-length-cancellation-exchange,
  part~@case:longest-reflection-group-element and
  Exercise~@exc:type-a-root-system. Now let
  $ w_0=s_(i(1)) dots s_(i(m)), quad s_(i(j)) in S, $
  be a reduced expression for $w_0$, where $m=l(w_0)=n(n+1)/2$. Using
  @th:iwahori-hecke-basis-multiplication repeatedly, we obtain
  $ a_(w_0)=a_(s_(i(1))) dots a_(s_(i(m))). $
  Then, since $op("ind"):cal(H) arrow CC$ is a homomorphism of algebras, we have
  $
    op("ind") a_(w_0)=op("ind") a_(s_(i(1))) dots
    op("ind") a_(s_(i(m)))=q_(i(1)) dots q_(i(m)),
  $
  where the ${q_(i(j))}$ are the index parameters @eq:bn-pair-index-parameters.
  It remains to compute the index parameters
  $q_i=op("ind") s_i=[B:attach(B, tl: s_i) inter B]$, $s_i in S$. Using the
  coset representatives ${dot(s)_i}$ defined in the proof of
  @th:general-linear-bn-pair, it is easily checked that
  $op("ind") s_i=abs(FF_q)=q$ for all $s_i in S$. Therefore
  $ upright("St")_G 1=op("ind") a_(w_0)=q^(n(n+1)/2), $
  as required.
]

#remark(numbered: true)[
  The fact that $upright("St")_G lr((1))=abs(G)_p$ has many consequences, some
  of which we list here. By @i:prop:defect-zero-character-projective-simple,
  $upright("St")_G$ is an irreducible character of defect zero, and vanishes on
  the $p$-irregular elements of $G$. If $(K,R,k)$ is a $p$-modular system, for
  $K$ sufficiently large, then $upright("St")_G$ is the $K$-character afforded
  by $K M$, for some indecomposable projective $R G$-module $M$. Moreover,
  $overline(M)$ is a simple projective $k G$-module.

  We shall see later (in @prop:split-bn-pair-order-sylow-steinberg) that
  $upright("St")_G lr((1))=abs(G)_p$ for all finite groups $G$ with split
  $B N$-pairs of characteristic $p$, and hence for all finite Chevalley groups.
] <rem:steinberg-defect-zero-projectivity>

=== Representations of the Hecke Algebra $cal(H)$ for a $B N$-Pair of Rank 2
<ss:rank-two-bn-pair-hecke-representations>

We begin with the determination, by Kilmoyer–Solomon @bib:Kilmoyer1973, of the
irreducible representations of the Hecke algebra $cal(H)(G,B,1_B)$ for a finite
group $G$ with a $B N$-pair of rank $2$. Using their results together with
@i:th:hecke-character-formulas, part (iii), we shall then indicate
#source(636)
how to calculate explicitly the degrees of all characters $zeta in Irr G$ such
that $(zeta,(1_B)^G) != 0$; these degrees will be expressed in terms of the
index parameters @eq:bn-pair-index-parameters.

In §~@ss:feit-higman-generalized-polygons, we give a second application of the
Kilmoyer–Solomon results, namely, their proof of the Feit–Higman theorem
@bib:Feit1964 on generalized polygons. This result, in turn, is a crucial first
step in the classification by Tits (see @bib:Tits1974, §~11) of finite simple
groups with $B N$-pairs of rank $>=3$.

As another application of these results, in
§~@ss:hecke-algebra-reflection-representation we shall give Kilmoyer's
construction of the reflection representation of a finite group with a
$B N$-pair (see Kilmoyer @bib:Kilmoyer1969 and Curtis–Iwahori–Kilmoyer
@bib:Curtis1971).

Our first main objective is to prove the following theorem on the
representations of certain algebras $A$ whose presentation is analogous to that
of Hecke algebras of $B N$-pairs of rank $2$.

#theorem[
  Let $m$ be a positive integer. Let $A$ be a semisimple algebra over $CC$ of
  dimension $2m$, generated by two elements ${a_r,a_s}$, which satisfy the
  following relations:
  #case-list(
    numbering: "(a)",
    [#case[
      (Quadratic relations)
      $ a_r^2=q_r 1+(q_r-1)a_r, quad a_s^2=q_s 1+(q_s-1)a_s, $
      for some positive real numbers $q_r$ and $q_s$ (called index parameters),
      and
    ] <case:rank-two-hecke-quadratic-relations>],
    [#case[
      (Homogeneous relations)
      $ (a_r a_s)^k=(a_s a_r)^k quad "if" m=2k, $
      $ (a_r a_s)^k a_r=(a_s a_r)^k a_s quad "if" m=2k+1. $
    ] <case:rank-two-hecke-homogeneous-relations>],
  )
  Then we have:
  #case-list(
    prefix: "Case ",
    numbering: "1.",
    [#case[
      If $m=2k$ is even, there are precisely $4$ representations of $A$ of
      degree $1$, namely:
      $
        cases(
          "index representation of" A ", given by"
          op("ind") a_r=q_r \, op("ind") a_s=q_s";",
          "sign representation of" A ", given by"
          op("sgn") a_r=op("sgn") a_s=-1";",
          a_r arrow q_r \, quad a_s arrow -1";",
          a_r arrow -1 \, quad a_s arrow q_s.
        )
      $
      All other irreducible representations of $A$ have degree $2$, and are
      given as follows. Set
      $ rho=sqrt(q_r q_s), quad theta_j=2 pi j slash m, quad 1<=j<=m, $
      and let ${c_j}$, ${d_j}$ be complex numbers such that
      $ c_j d_j=q_r+q_s+2 rho cos theta_j, quad 1<=j<=m. $
      #source(637)
      For $1<=j<=k$, where $k=m/2$, put
      $
        T_j lr((a_r))=mat(-1, c_j; 0, q_r), quad
        T_j lr((a_s))=mat(q_s, 0; d_j, -1).
      $
      Then ${T_1,dots,T_(k-1)}$ are a full set of inequivalent irreducible
      two-dimensional representations of $A$.
    ] <case:rank-two-hecke-even-representations>],
    [#case[
      If $m=2k+1$ is odd, we assume that $q_r=q_s$. Then there are precisely two
      representations of $A$ of degree $1$, namely, the representations
      $op("ind")$ and $op("sgn")$ defined above. Further, we define $rho$,
      $theta_j$, and $T_j$ as above. Then all other irreducible representations
      of $A$ have degree $2$, and are given (up to equivalence) by
      $T_1,dots,T_k$.
    ] <case:rank-two-hecke-odd-representations>],
  )
] <th:rank-two-hecke-irreducible-representations>

#remarks(numbered: false)[
  #case-list(
    numbering: "(i)",
    [#case[
      Up to equivalence, the representation $T_j$ does not depend on the choice
      of $c_j$ and $d_j$, provided their product $c_j d_j$ is equal to
      $q_r+q_s+2 rho cos theta_j$.
    ] <case:rank-two-matrix-parameter-equivalence>],
    [#case[
      In the special case $q_r=q_s=1$, the algebra $A$ is just the group algebra
      of a dihedral group $D_m$ of order $2m$, with generators $a_r$ and $a_s$,
      and the representations of $A$ defined above are the irreducible complex
      representations of $D_m$ (see @i:exm:dihedral-group-algebra-reduced-norm
      and @i:exm:dihedral-group-characters).
    ] <case:rank-two-hecke-dihedral-specialization>],
    [#case[
      By Theorem~@th:iwahori-matsumoto-hecke-presentation, the Hecke algebra
      $cal(H)=cal(H)(G,B,1_B)$ of a finite group with a $B N$-pair of rank $2$
      has a presentation as in
      Theorem~@th:rank-two-hecke-irreducible-representations, with ${a_r,a_s}$
      the standard basis elements of $cal(H)$ corresponding to the distinguished
      generators ${r,s}$ of the Weyl group $W$ of $G$. In this case, the
      dimension of $cal(H)$ is $2m$, where $m$ is the order of $r s$ in $W$. The
      index parameters $q_r$ and $q_s$ in
      @th:rank-two-hecke-irreducible-representations coincide with the index
      parameters of $G$ defined in @eq:bn-pair-index-parameters, and satisfy the
      condition that $q_r=q_s$ if $m$ is odd, by
      @cor:conjugate-simple-reflections-equal-parameters. The Hecke algebra
      $cal(H)$ is semisimple, by the remark following
      Definition~@i:def:hecke-algebra.
    ] <case:rank-two-bn-pair-hecke-hypotheses>],
  )
] <rem:rank-two-hecke-representation-specializations>
#idx(
  "Dihedral group",
  target: [@case:rank-two-hecke-dihedral-specialization],
)

#proof[
  We first note that the algebra $A$ has a presentation with the generators
  $a_r$ and $a_s$, and relations @case:rank-two-hecke-quadratic-relations and
  @case:rank-two-hecke-homogeneous-relations. This observation holds since any
  algebra with two generators, satisfying the relations
  @case:rank-two-hecke-quadratic-relations and
  @case:rank-two-hecke-homogeneous-relations, is easily shown to have dimension
  $<=2m$, so the assumption that $dim A=2m$ implies that $A$ is the universal
  such algebra. We now discuss the cases separately.

  #case-list(
    prefix: "Case ",
    numbering: "1.",
    [#case[
      ($m=2k$). It is easily verified that the four displayed maps, defined on
      the generators of $A$, preserve the defining relations, and therefore give
      well-defined one-dimensional representations of $A$. Further, in any
      one-dimensional representation $phi:A arrow CC$, the quadratic relations
      impose restrictions on the images $phi(a_r)$, $phi(a_s)$, from which it
      follows readily that there are no other one-dimensional representations
      besides those defined previously.

      For the discussion of the two-dimensional representations, we simplify the
      notation by omitting (for the moment) the subscript $j$ from the symbols
      $c_j$, $d_j$, and $theta_j$, where $1<=j<k$. Let $bold(R)$, $bold(S)$ be
      the matrices given by
      $
        a_r arrow bold(R)=mat(-1, c; 0, q_r), quad
        a_s arrow bold(S)=mat(q_s, 0; d, -1).
      $
      #source(638)
      Since $bold(R)$ has eigenvalues ${-1,q_r}$ and $bold(S)$ has eigenvalues
      ${-1,q_s}$, the quadratic relations are clearly satisfied by the matrices
      $bold(R)$ and $bold(S)$. For the homogeneous relations, we first consider
      $
        bold(R) bold(S)=mat(-q_s+c d, -c; q_r d, -q_r)
        quad "and" quad bold(S) bold(R)=mat(-q_s, q_s c; -d, c d-q_r),
      $
      which both have the same characteristic polynomial
      $
        t^2+(q_r+q_s-c d)t+q_r q_s=t^2-2 rho(cos theta)t+rho^2 \
        =(t-rho e^(i theta))(t-rho e^(-i theta)).
      $
      Since $0<theta<pi$, the eigenvalues ${rho e^(plus.minus i theta)}$ of
      $bold(R) bold(S)$ and $bold(S) bold(R)$ are distinct, and there exists an
      invertible $2 times 2$ matrix $bold(P)$ such that
      $
        bold(P) bold(R) bold(S) bold(P)^(-1)
        =mat(rho e^(i theta), 0; 0, rho e^(-i theta))
        quad ("and similarly for" bold(S) bold(R)).
      $
      Let $bold(R)'=bold(P) bold(R) bold(P)^(-1)$,
      $bold(S)'=bold(P) bold(S) bold(P)^(-1)$, and
      $bold(D)=bold(R)' bold(S)'=op("diag")(rho e^(i theta),rho e^(-i theta))$.
      Since $m=2k$ is even, we have $e^(i k theta)=e^(i pi j)=e^(-i k theta)$,
      so that $(bold(R)' bold(S)')^k=(bold(S)' bold(R)')^k=plus.minus rho^k$,
      and the homogeneous relation holds. The representation defined by the
      matrices $bold(R)$ and $bold(S)$ is irreducible, since $A$ is semisimple,
      and the only matrices commuting with $bold(R)$ and $bold(S)$ are scalar
      multiples of $bold(I)$. We also note that
      $op("Tr") bold(R) bold(S)=2 rho cos theta$, so the characters of the
      representations ${T_1,dots,T_(k-1)}$ are distinct. The sum of the squares
      of the dimensions of the irreducible representations obtained so far is
      $2m$, and hence they form a basic set, by the results of
      §~@i:sec:semisimple-rings-modules on split semisimple algebras.
    ] <case:rank-two-hecke-even-proof>],
    [#case[
      ($m=2k+1$). In this case we let $q=q_r=q_s$, and continue with the
      discussion of the matrices $bold(R)$ and $bold(S)$ defined in
      Case~@case:rank-two-hecke-even-proof. Let
      $ bold(R)'=mat(alpha, beta; gamma, delta). $
      Then $det bold(R)'=det bold(R)=-q$, $rho=q$, and we have
      $
        bold(S)'=(bold(R)')^(-1) bold(D)
        =mat(
          -delta e^(i theta), beta e^(-i theta);
          gamma e^(i theta), -alpha e^(-i theta)
        ).
      $
      Since $op("Tr") bold(R)=op("Tr") bold(S)=q-1$, we have
      $ alpha+delta=q-1, quad alpha e^(-i theta)+delta e^(i theta)=-(q-1), $
      and it follows that $delta=-e^(-i theta) alpha$. Then
      $ bold(S)'=mat(alpha, beta e^(-i theta); gamma e^(i theta), delta). $
      #source(639)
      Using the fact that $e^((2k+1)i theta)=1$, a direct computation shows that
      $ bold(D)^k bold(R)' bold(D)^(-k)=bold(S)'. $
      Since $bold(D)=bold(R)' bold(S)'$, this implies that
      $ (bold(R)' bold(S)')^k bold(R)'=bold(S)'(bold(R)' bold(S)')^k, $
      proving the homogeneous relation. The rest of the proof is the same as in
      Case~@case:rank-two-hecke-even-proof.
    ] <case:rank-two-hecke-odd-proof>],
  )
]

The next result can be used to calculate explicitly the degrees of the
irreducible characters in $(1_B)^G$, for a finite group $G$ with a $B N$-pair of
rank $2$ (using also the proof of @th:feit-higman-even-generalized-polygons
below).

#corollary[
  Let $cal(H)$ be the Hecke algebra $cal(H)(G,B,1_B)$ of a finite group $G$ with
  a $B N$-pair of rank $2$. Let $phi$ be the character of any of the irreducible
  representations of $cal(H)$ constructed in
  @th:rank-two-hecke-irreducible-representations. Then $phi$ is the restriction
  to $cal(H)$ of a unique irreducible character $zeta$ of $G$ such that
  $(zeta,(1_B)^G)>0$. The degree of $zeta$ is given by
  $
    deg zeta=(deg phi)[G:B] slash
    sum_(w in W) (op("ind") a_w)^(-1) phi(a_w) phi(a_(w^(-1))),
  $
  where the ${a_w}$ are the standard basis elements of $cal(H)$. The set of
  characters ${zeta}$ of $G$ obtained in this way coincides with the set
  $ {zeta in Irr G:(zeta,(1_B)^G)>0}. $
] <cor:rank-two-principal-series-character-degrees>

The proof that $cal(H)$ satisfies the hypotheses of
@th:rank-two-hecke-irreducible-representations was given in
§~@ss:hecke-algebra-bn-pair-structure, and explained in the remark following the
statement of the theorem. The other statements follow from
§~@i:ss:hecke-algebras (see @i:th:hecke-character-correspondence and
@i:th:hecke-character-formulas).

=== The Feit–Higman Theorem on Generalized Polygons
<ss:feit-higman-generalized-polygons>

The results of §~@ss:rank-two-bn-pair-hecke-representations apply not only to
$B N$-pairs, but to other situations as well. In particular, certain finite
geometries lead to algebras satisfying the hypotheses of
@th:rank-two-hecke-irreducible-representations, and the character theory of
these algebras can be used to classify the geometries. As we mentioned in the
introduction to §~@ss:rank-two-bn-pair-hecke-representations, we shall give such
an application here to the theorem of Feit–Higman @bib:Feit1964 on generalized
polygons, following the simplified version of their proof by Kilmoyer–Solomon
@bib:Kilmoyer1973. The proof will use the orthogonality relations derived in
§~@i:sec:orthogonality-central-idempotents for the irreducible characters of a
split semisimple algebra, which in this case is neither a group algebra nor a
Hecke algebra. The incidence algebras defined below are examples of algebras
defined by combinatorial association schemes, also called coherent
configurations (see Dembowski @bib:Dembowski1968, §7.1, D. G. Higman
@bib:Higman1975, @bib:Higman1976, and MacWilliams–Sloane @bib:MacWilliams1977).

#source(640)
We define an _incidence structure_ $(P,L,F)$ to be a triple consisting of a set
$P$ of elements called _points_, a set $L$ of elements called _lines_, and a
subset $F subset.eq P times L$ of pairs $(p,l)$ called _flags_. A point $p$ is
on a line $l$, or is _incident_ to $l$, if $(p,l)$ is a flag. We assume
throughout that $P$ and $L$ are finite sets, and that there are $s+1$ points on
every line and $t+1$ lines incident to every point. If $x=(p,l)$ and $y=(q,m)$
are distinct flags, we write $x inter y=p$ if $p=q$ and $x inter y=l$ if $l=m$.
For each $x in F$, define subsets $S(x)$, $T(x)$ of $F$ by
$ S(x)={y in F:x inter y in L}, quad T(x)={z in F:x inter z in P}. $
Let $V$ be the vector space over $CC$ with the elements of $F$ as basis, and
define endomorphisms $sigma$, $tau$ of $V$ by
$ sigma(x)=sum_(y in S(x)) y, quad tau(x)=sum_(z in T(x)) z. $
Let $A$ be the algebra of endomorphisms of $V$ generated by $sigma$ and $tau$;
we shall call $A$ the _incidence algebra_ associated with $(P,L,F)$.
#idx("Incidence structure")

#lemma[
  The endomorphisms $sigma$ and $tau$ satisfy
  $
    sigma^2=s dot 1+(s-1)sigma quad "and" quad
    tau^2=t dot 1+(t-1)tau.
  $
] <lem:incidence-generators-quadratic-relations>
#proof[
  Let $x=(p,l) in F$, and let $p,p_1,dots,p_s$ be the points on $l$. Then $S(x)$
  consists of the flags ${(p_1,l),dots,(p_s,l)}$. For any one of the flags
  $y=(p_i,l)$, $p_i != p$, $S(y)$ consists of the flags $(p,l)$ and the flags
  $(p_j,l)$ for $j != i$. Thus
  $ sigma(x)=sum_i (p_i,l) $
  and
  $
    sigma^2(x)=sum_i lr([ (p,l)+sum_(j != i) (p_j,l) ])
    =s dot x+(s-1)sigma x.
  $
  The proof for $tau$ is similar.
]

Let $(P,L,F)$ be an incidence structure, and let $a,b in P union L$. A _chain_
of length $h$ from $a$ to $b$ is a sequence
$ a_0=a,a_1,dots,a_h=b $
of elements from $P union L$ such that $a_i$ and $a_(i+1)$ are incident, for
$0<=i<=h-1$. The least integer $h$ (if one exists) for which there is a chain of
length $h$ from $a$ to $b$ is called the _distance_ $rho(a, b)$ from $a$ to $b$.

#definition[
  A generalized $m$-gon, where $m>=2$, is an incidence structure $(P,L,F)$ for
  which the following conditions hold:#ed-note[
    The conventional restriction $m>=2$ excludes a single incident point-line
    pair. It satisfies the three distance axioms with $m=1$ and $s=t=0$, but its
    incidence algebra has dimension $1$, rather than $2m$ as in
    Theorem~@th:generalized-polygon-incidence-algebra.
  ]
  #source(641)
  #case-list(
    numbering: "(i)",
    [#case[$rho(a, b)<=m$ for all $a,b in P union L$.]
      <case:generalized-polygon-diameter-bound>],
    [#case[
      If $rho(a, b)=h<m$, then there is only one chain of length $h$ from $a$ to
      $b$.
    ] <case:generalized-polygon-short-geodesic-unique>],
    [#case[
      For each $a in P union L$, there exists an element $b in P union L$ such
      that $rho(a, b)=m$.
    ] <case:generalized-polygon-opposite-vertices>],
  )
] <def:generalized-polygon>
#idx("Generalized m-gon", target: [@def:generalized-polygon])

Note that the vertices and edges of an ordinary $m$-gon satisfy
@case:generalized-polygon-diameter-bound–#(
  [@case:generalized-polygon-opposite-vertices]
), with $s=t=1$. Examples of generalized $m$-gons arising from finite groups
with $B N$-pairs of rank $2$ are described in
Exercise~@exc:rank-two-bn-pair-generalized-polygon.

We now work out the structure of the incidence algebra $A$ associated with a
generalized $m$-gon, and begin with some additional definitions. Two flags $x,y$
are called _adjacent_ if either $x inter y in P$ or $x inter y in L$. A
_gallery_ of length $h$ from $x$ to $y$ is a sequence
$ x_0=x,x_1,dots,x_h=y $
of flags such that ${x_i,x_(i+1)}$ are adjacent, for $0<=i<=h-1$. The _distance_
$d(x,y)$ between two flags is the least integer $h$ for which there exists a
gallery of length $h$ from one to the other. A gallery from $x$ to $y$ is
_minimal_ if its length is $d(x,y)$; in this case, $x_(i-1) inter x_i in P$
implies $x_i inter x_(i+1) in L$, for each $i$. The following lemma follows
easily from the axioms, and its proof is left as an exercise.

#lemma[
  Let $(P,L,F)$ be a generalized $m$-gon, and let $x,y in F$. Then:
  #case-list(
    numbering: "(i)",
    [#case[$d(x,y)<=m$.] <case:polygon-gallery-diameter>],
    [#case[
      If $d(x,y)<m$, there exists a unique minimal gallery from $x$ to $y$.
    ] <case:polygon-short-gallery-unique>],
    [#case[
      If $d(x,y)=m$, there exist exactly two minimal galleries $x_0,dots,x_m$
      from $x$ to $y$, where $x_0=x$ and $x_m=y$. For one of these minimal
      galleries, $x_(m-1) inter y in P$, while for the other we have
      $x_(m-1) inter y in L$.
    ] <case:polygon-opposite-two-galleries>],
    [#case[
      For each integer $j>0$, let $S_j lr((x))$ be the set of all flags $y in F$
      such that $d(x,y)=j$ and there exists a minimal gallery $x_0,x_1,dots,x_j$
      from $x$ to $y$ for which $x_(j-1) inter y in L$. Similarly, $T_j lr((x))$
      is the set of flags $y$ for which $d(x,y)=j$ and $x_(j-1) inter y in P$,
      for a minimal gallery ${x_0,dots,x_j}$ from $x$ to $y$. Then we have:
      $ S(x)=S_1 lr((x)), quad T(x)=T_1 lr((x)), $
      $ S_j lr((x)) inter T_j lr((x))=emptyset, quad 1<=j<=m-1, $
      and
      $ S_m lr((x))=T_m lr((x)). $
    ] <case:polygon-gallery-distance-sets>],
  )
  Now let $1<=j<=m$. Then
  #case-list(
    start: 5,
    numbering: "(i)",
    [#case[
      $y in S_j lr((x))$ $<=>$ there exists a unique $z in T_(j-1) lr((x))$ such
      that $y in S(z)$.
    ] <case:polygon-gallery-s-extension>],
    [#case[
      $y in T_j lr((x))$ $<=>$ there exists a unique $z in S_(j-1) lr((x))$ such
      that $y in T(z)$.
    ] <case:polygon-gallery-t-extension>],
    [#case[If $m$ is odd, then $s=t$.]
      <case:odd-polygon-equal-parameters>],
  )
] <lem:generalized-polygon-gallery-properties>

#source(642)
We are now ready to prove:

#theorem[
  Let $A$ be the incidence algebra associated with a generalized $m$-gon
  $(P,L,F)$. Then $A$ is a semisimple algebra of dimension $2m$, and has a
  presentation as a $CC$-algebra with generators ${sigma,tau}$, and defining
  relations:
  $ sigma^2=s dot 1+(s-1)sigma, quad tau^2=t dot 1+(t-1)tau $
  and
  $
    cases(
      (sigma tau)^k=(tau sigma)^k & "if" m=2k "is even,",
      (sigma tau)^k sigma=(tau sigma)^k tau & "if" m=2k+1 "is odd."
    )
  $
] <th:generalized-polygon-incidence-algebra>
#proof[
  We first prove that $A$ is semisimple. The matrices of the generators $sigma$
  and $tau$ with respect to the basis $F$ are clearly real symmetric matrices.
  It follows that the algebra $A$, viewed as a matrix algebra, is closed under
  the operations of taking transposes $bold(X) arrow attach(bold(X), tl: t)$ and
  complex conjugates $bold(X) arrow overline(bold(X))$, where
  $overline(bold(X))=(overline(x)_(i j))$ if $bold(X)=(x_(i j))$. The radical
  $rad A$ of the matrix algebra $A$ is also closed under these operations. Now
  let $bold(X) in rad A$, so also
  $overline(bold(X)) attach(bold(X), tl: t) in rad A$. The diagonal entries of
  $overline(bold(X)) attach(bold(X), tl: t)$ are the squares of the norms of the
  rows of $bold(X)$, in the usual metric. It follows that if $bold(X) != 0$,
  then $op("Tr") overline(bold(X)) attach(bold(X), tl: t) != 0$, which is
  impossible if the matrix $overline(bold(X)) attach(bold(X), tl: t)$ is
  nilpotent. Since $rad A$ consists of nilpotent matrices, we have $rad A=0$,
  proving that $A$ is semisimple.

  Next define endomorphisms $sigma_j$ and $tau_j$ of $V$ by
  $
    sigma_j x=sum_(y in S_j lr((x))) y, quad
    tau_j x=sum_(y in T_j lr((x))) y.
  $
  By @lem:generalized-polygon-gallery-properties,
  part~@case:polygon-gallery-s-extension, we have, for $x in F$,
  $
    sigma tau_(j-1) x=sum_(z in T_(j-1) lr((x))) sigma z
    =sum_(z in T_(j-1) lr((x))) sum_(y in S(z)) y
    =sum_(y in S_j lr((x))) y=sigma_j x,
  $
  proving that $sigma tau_(j-1)=sigma_j$. Similarly $tau sigma_(j-1)=tau_j$.
  Since $sigma_1=sigma$ and $tau_1=tau$, we have
  $
    sigma_(2j-1)=(sigma tau)^(j-1) sigma, quad sigma_(2j)=(sigma tau)^j,
    quad tau_(2j-1)=(tau sigma)^(j-1) tau, quad tau_(2j)=(tau sigma)^j.
  $
  In particular, we have $S_m lr((x))=T_m lr((x))$ by
  @lem:generalized-polygon-gallery-properties,
  part~@case:polygon-gallery-distance-sets, so that $sigma_m=tau_m$, and the
  homogeneous relations in @th:generalized-polygon-incidence-algebra hold. The
  quadratic relations were proved in
  @lem:incidence-generators-quadratic-relations.

  It follows that $A$ is generated as a vector space by the elements
  $
    1,sigma_1,dots,sigma_(m-1),tau_1,dots,tau_(m-1),sigma_m=tau_m,
  $ <eq:polygon-incidence-standard-basis>
  so $dim A<=2m$. On the other hand, the sets $S_i lr((x)) inter S_j lr((x))$,
  $T_i lr((x)) inter T_j lr((x))$, and $S_i lr((x)) inter T_j lr((x))$ are empty
  if $i != j$, and by @lem:generalized-polygon-gallery-properties $F$ is the
  disjoint union of the sets
  $
    S_0 lr((x))=T_0 lr((x))={x}, quad
    S_1 lr((x)),dots,S_(m-1) lr((x)),T_1 lr((x)),dots,T_(m-1) lr((x)),
    S_m lr((x))=T_m lr((x)).
  $
  #source(643)
  Thus the elements in @eq:polygon-incidence-standard-basis form a basis for
  $A$, and $dim A=2m$. The proof that $A$ has the required presentation is the
  same as the first paragraph of the proof of
  @th:rank-two-hecke-irreducible-representations, and we are finished.
]

We shall call the elements @eq:polygon-incidence-standard-basis the _standard
basis_ of $A$, and denote them by ${beta_0,beta_1,dots,beta_(2m-1)}$, with
$beta_0=1$. We next describe a dual basis to the standard basis with respect to
a suitable bilinear form.

#proposition[
  #case-list(
    numbering: "(i)",
    [#case[
      The incidence algebra $A$ has a representation of degree $1$, called
      $op("ind")$, defined by
      $ op("ind") sigma=s, quad op("ind") tau=t. $
    ] <case:incidence-algebra-index-character>],
    [#case[
      The bilinear form $B:A times A arrow CC$, whose value at $(a,a')$ is the
      coefficient of $beta_0$ in the expression of the product $a a'$ in terms
      of the standard basis, is nondegenerate, associative, and symmetric (see
      §~@i:ss:frobenius-symmetric-algebras).
    ] <case:incidence-algebra-symmetrizing-form>],
    [#case[
      Let $a arrow hat(a)$ be the transpose map in $A$. Then
      $ hat(sigma)=sigma, quad hat(tau)=tau, $
      and $a arrow hat(a)$ is an antiautomorphism of $A$.
    ] <case:incidence-algebra-transpose>],
    [#case[
      The dual basis of the standard basis, with respect to the bilinear form
      defined in part~@case:incidence-algebra-symmetrizing-form, is
      $
        {hat(beta)_0=1,(op("ind") beta_1)^(-1) hat(beta)_1,dots,
          (op("ind") beta_(2m-1))^(-1) hat(beta)_(2m-1)}.
      $
    ] <case:incidence-algebra-dual-basis>],
  )
] <prop:incidence-algebra-symmetric-dual-basis>

The proof follows easily from the definition of $A$ and
Theorem~@th:generalized-polygon-incidence-algebra, and is left as an exercise
for the reader. For two irreducible characters $mu,mu'$ in $Irr A$, let us set
$
  lr(chevron.l mu, mu' chevron.r)=sum_(i=0)^(2m-1)
  (op("ind") beta_i)^(-1) mu(beta_i) mu'(hat(beta)_i).
$ <eq:incidence-algebra-character-pairing>
Then we have, by Propositions @prop:incidence-algebra-symmetric-dual-basis and
@i:prop:algebra-character-orthogonality:

#corollary[
  Let $mu,mu'$ be distinct irreducible characters of $A$. Then
  $lr(chevron.l mu, mu' chevron.r)=0$.
] <cor:incidence-algebra-character-orthogonality>

The main results of this subsection are the following three theorems, due to
Feit–Higman @bib:Feit1964.

#theorem(name: "Feit–Higman Theorem")[
  Let $(P,L,F)$ be a generalized $m$-gon, with $s+1$ points on each line, and
  $t+1$ lines through each point. Then either $s=t=1$ and $(P,L,F)$ is an
  ordinary polygon, or else $m in {2,3,4,6,8,12}$. If $s>1$ and $t>1$, then
  $m in {2,3,4,6,8}$. Under the same assumptions $s>1$ and $t>1$, moreover,
  $s t$ is a square if $m=6$, while $2s t$ is a square if $m=8$.
] <th:feit-higman-even-generalized-polygons>
#idx("Feit-Higman Theorem", target: [@th:feit-higman-even-generalized-polygons])

#source(644)
#theorem[
  Let $G$ be a finite group with a $B N$-pair of rank $2$, whose Weyl group is a
  dihedral group of order $2m$. Then $m in {2,3,4,6,8}$.
] <th:rank-two-bn-pair-coxeter-orders>

#theorem[
  The Weyl group of a finite group with a $B N$-pair is a direct product of a
  number (possibly zero) of dihedral groups of order $16$ and the Weyl group of
  a semisimple Lie algebra over $CC$.
] <th:finite-bn-pair-weyl-group-types>

Before proving @th:feit-higman-even-generalized-polygons and
@th:rank-two-bn-pair-coxeter-orders, we note that
Theorem~@th:finite-bn-pair-weyl-group-types follows from
@th:rank-two-bn-pair-coxeter-orders, using the fact that the Weyl group of a
finite group with a $B N$-pair is a Coxeter group (by
Theorem~@th:bn-pair-weyl-coxeter-system).

We now begin the proof of Theorem~@th:feit-higman-even-generalized-polygons. The
case $m=2$ is immediate, so we may assume $m>2$. The idea is to compute
explicitly the characters of the incidence algebra $A$ of a generalized $m$-gon,
using Theorem~@th:rank-two-hecke-irreducible-representations. Some details are
omitted and can be found in Kilmoyer–Solomon @bib:Kilmoyer1973. We first note
that $A$ satisfies the hypotheses of
Theorem~@th:rank-two-hecke-irreducible-representations, with ${sigma,tau}$ in
place of the generators $a_r$ and $a_s$, and $s$ and $t$ instead of the index
parameters $q_r$ and $q_s$. By @th:rank-two-hecke-irreducible-representations,
the irreducible representations of $A$ of degree $2$ are given as follows. Let
$ rho=sqrt(s t), quad theta_j=2 pi j slash m, quad 1<=j<=m, $
and let ${c_j,d_j}$ be complex numbers such that
$ c_j d_j=s+t+2 rho cos theta_j, quad 1<=j<=m. $
For $1<=j<=k-1$ if $m=2k$, or $1<=j<=k$ if $m=2k+1$, put
$
  T_j lr((sigma))=mat(-1, c_j; 0, s), quad
  T_j lr((tau))=mat(t, 0; d_j, -1).
$
Then the ${T_j}$ define a complete set of irreducible representations of $A$ of
degree $2$, by @th:rank-two-hecke-irreducible-representations. For each $j$, let
$mu_j$ be the character of $T_j$. Then it is readily shown, using the proof of
@th:rank-two-hecke-irreducible-representations, that
$
  mu_j lr((sigma_(2i)))=mu_j lr((tau_(2i)))
  =2 rho^i cos i theta_j, quad 1<=i<=k,
$
and that
$
  mu_j lr((sigma_(2i+1)))=rho^(i-1)(sin theta_j)^(-1)
  (s(t-1)sin i theta_j+rho(s-1)sin(i+1)theta_j),
$
while
$
  mu_j lr((tau_(2i+1)))=rho^(i-1)(sin theta_j)^(-1)
  (t(s-1)sin i theta_j+rho(t-1)sin(i+1)theta_j).
$
We use these formulas to compute the scalar products
$lr(chevron.l mu_j, mu_j chevron.r)$ of the characters
#source(645)
${mu_j}$, defined in @eq:incidence-algebra-character-pairing. The computation
becomes, in case $m=2k$,
$
  lr(chevron.l mu_j, mu_j chevron.r) = & sum_(i=0)^(k-1) lr(
                                           bracket.l
                                           (op("ind") sigma_(2i))^(-1)
                                           mu_j lr((sigma_(2i)))^2
                                           +(op("ind") tau_(2i))^(-1)
                                           mu_j lr((tau_(2i)))^2
                                         ) \
                                       & lr(
                                           +(op("ind") sigma_(2i+1))^(-1)
                                           mu_j lr((sigma_(2i+1)))^2
                                           +(op("ind") tau_(2i+1))^(-1)
                                           mu_j lr((tau_(2i+1)))^2 bracket.r
                                         ),
$
since $mu_j lr((a))=mu_j lr((hat(a)))$ for all $a in A$; a similar formula holds
in case $m=2k+1$. The sums are easily computed using the character values,
converting the trigonometric functions to exponential form, and summing the
geometric series which arise. The result is that
$
  lr(chevron.l mu_j, mu_j chevron.r)=4k+
  lr([ (s-1)^2/s+(t-1)^2/t ]) k/(sin^2 theta_j)
  +((s-1)(t-1))/rho (2k cos theta_j)/(sin^2 theta_j)
$
if $m=2k$, $theta_j=j pi slash k$, and
$
  lr(chevron.l mu_j, mu_j chevron.r)=4k+2+(s-1)^2/s (2k+1)/(1-cos theta_j)
  quad "if" m=2k+1, quad theta_j=(2j pi)/(2k+1).
$
Now let $phi_V$ be the character of $A$ afforded by the representation of $A$ on
$V$, and write
$ phi_V=sum_(mu in Irr A) n_mu mu $
where $n_mu$ is the multiplicity of $mu$ in $phi_V$. If $beta$ is a standard
basis element $!=1$, then the proof of @th:generalized-polygon-incidence-algebra
shows that for $x in F$, $beta x$ is a sum of flags different from $x$.
Consequently $phi_V lr((beta))=0$. On the other hand, $phi_V lr((1))=abs(F)$.
Thus $lr(chevron.l mu, phi_V chevron.r)=abs(F)mu(1)$. The orthogonality
relations @cor:incidence-algebra-character-orthogonality imply that
$
  abs(F)mu(1)=lr(chevron.l mu, phi_V chevron.r)
  =n_mu lr(chevron.l mu, mu chevron.r),
$
and it follows that
$ lr(chevron.l mu, mu chevron.r) in QQ quad "for all" mu in Irr A. $
Now assume $m=2k$. Then $theta_1+theta_(k-1)=pi$,
$cos theta_1=-cos theta_(k-1)$, and $sin theta_1=sin theta_(k-1)$. Using the
formulas for
$lr(chevron.l mu_1, mu_1 chevron.r)+lr(chevron.l mu_(k-1), mu_(k-1) chevron.r)$
given above, we obtain
$ lr([ (s-1)^2/s+(t-1)^2/t ]) k/(sin^2 theta_1) in QQ. $
If $s=t=1$, then clearly $(P,L,F)$ is an ordinary polygon. If either $s>1$ or
$t>1$, we conclude that
$ sin^2 theta_1=sin^2(pi/k) in QQ. $

#source(646)
Thus the field of $k$-th roots of $1$ is at most quadratic over $QQ$, so
$k in {1,2,3,4,6}$, and $m in {2,4,6,8,12}$. Since
$lr(chevron.l mu_j, mu_j chevron.r)
-lr(chevron.l mu_(k-j), mu_(k-j) chevron.r) in QQ$
for $1<=j<=k-1$, the preceding formulas show that
$ lr([ ((s-1)(t-1))/rho ]) (2k cos theta_j)/(sin^2 theta_j) in QQ. $
If both $s>1$ and $t>1$, then we obtain $rho^(-1) cos theta_j in QQ$ for
$1<=j<=k-1$, where $rho=sqrt(s t)$. This excludes the case $m=12$, and implies
$rho in QQ$ if $m=6$, while $sqrt(2) rho in QQ$ if $m=8$.

In case $m=2k+1$, we have $s=t$, and if $s>1$, the formulas for
$lr(chevron.l mu, mu chevron.r)$ imply that $cos(2 pi slash m) in QQ$. Thus the
field of $m$-th roots of $1$ is at most quadratic over $QQ$, and we obtain
$m=3$, completing the proof.

#proof(head: emph[Proof of Theorem~@th:rank-two-bn-pair-coxeter-orders.])[
  Let $G$ be a finite group with a $B N$-pair of rank $2$, whose Weyl group is
  dihedral of order $2m$, with distinguished generators ${r,s}$. Let $cal(H)$ be
  the Hecke algebra $cal(H)(G,B,1_B)$. By @eq:bn-pair-nondegeneracy-axiom it is
  clear that both index parameters $q_r$ and $q_s$ are $>1$. Since $cal(H)$ also
  has the structure of the algebra $A$ in
  @th:rank-two-hecke-irreducible-representations (by
  Theorem~@th:iwahori-matsumoto-hecke-presentation), the results used in the
  proof of @th:feit-higman-even-generalized-polygons can all be applied to
  characters of $cal(H)$. In this case, the orthogonality relations and the fact
  that $lr(chevron.l mu, mu chevron.r) in QQ$ for $mu in Irr A$ follow from
  @i:th:hecke-character-formulas, part (ii). Then
  Theorem~@th:rank-two-bn-pair-coxeter-orders follows by exactly the same
  arguments used in the proof of @th:feit-higman-even-generalized-polygons.
]

#remarks(numbered: false)[
  #case-list(
    numbering: "(i)",
    [#case[
      The formulas for $lr(chevron.l mu, mu chevron.r)$ calculated in the proof
      of @th:feit-higman-even-generalized-polygons are precisely the
      denominators in the formulas for degrees of characters in $(1_B)^G$ given
      in @cor:rank-two-principal-series-character-degrees.
    ] <case:feit-higman-principal-series-denominators>],
    [#case[
      Our approach to Theorems~@th:feit-higman-even-generalized-polygons and
      @th:rank-two-bn-pair-coxeter-orders has been to exploit the common
      structures of the incidence algebra $A$ and the Hecke algebra $cal(H)$.
    ] <case:incidence-hecke-common-structure>],
  )
] <rem:feit-higman-hecke-applications>

=== The Reflection Representation of the Hecke Algebra $cal(H)$
<ss:hecke-algebra-reflection-representation>

We return to the study of a finite group $G$ with a $B N$-pair of arbitrary
rank. Let $W$ be the Weyl group of $G$, and $S={s_1,dots,s_n}$ the distinguished
generators of $W$. The Hecke algebra $cal(H)=cal(H)(G,B,1_B)$ has a presentation
with generators ${a_(s_1),dots,a_(s_n)}$ and relations
$
  a_(s_i)^2=q_i 1+(q_i-1)a_(s_i), quad 1<=i<=n,
  quad q_i=op("ind") a_(s_i),
$
and
$
  cases(
    (a_(s_i) a_(s_j))^(k_(i j))=(a_(s_j) a_(s_i))^(k_(i j))
    & "if" m_(i j)=2k_(i j) ",",
    (a_(s_i) a_(s_j))^(k_(i j)) a_(s_i)
    =(a_(s_j) a_(s_i))^(k_(i j)) a_(s_j) & "if" m_(i j)=2k_(i j)+1,
  )
$
where $m_(i j)$ is the order of $s_i s_j$, as in
§~@ss:hecke-algebra-bn-pair-structure.

#source(647)
In the general case, it is a formidable task to construct irreducible
representations of $cal(H)$, other than the one-dimensional representations
$op("ind")$ and $op("sgn")$ defined earlier. Nevertheless, the results of the
preceding two subsections give some indications as to how to proceed. For a
$B N$-pair of rank $2$, it follows from the results of
§§~@ss:rank-two-bn-pair-hecke-representations,
@ss:feit-higman-generalized-polygons that the Hecke algebra $cal(H)$ and the
group algebra of $W$ are isomorphic as $CC$-algebras, even though no explicit
isomorphism is given. In the next section, it will be proved that
$cal(H) tilde.equiv CC W$ in the general case (see
@th:hecke-algebra-weyl-group-isomorphism). These results suggest that
irreducible representations of $W$ can somehow be lifted to $cal(H)$.

A particularly interesting representation of an indecomposable Coxeter group is
the reflection representation, defined in §~@ss:coxeter-groups. In this section,
we shall sketch Kilmoyer's construction of a corresponding irreducible
representation of $cal(H)$, called the _reflection representation_ (see
Curtis–Iwahori–Kilmoyer @bib:Curtis1971). Besides its intrinsic interest, the
method is a special case of a general construction of representations of Hecke
algebras and Coxeter groups, by what are called $W$-graphs (see Kazhdan–Lusztig
@bib:Kazhdan1979, Gyoja @bib:Gyoja1984).

#idx("Reflection representation")

By @th:finite-coxeter-geometric-representation, the reflection representation of
$W$ is irreducible only if $(W,S)$ is an indecomposable Coxeter system, so it is
natural to make this assumption throughout this subsection. We shall need to use
the fact that in this case the Coxeter graph of $(W,S)$ is a tree, by
Exercise~@exc:finite-coxeter-graph-tree.

Let $V=plus.o.big_(i=1)^n CC v_i$ be an $n$-dimensional $CC$-space, where
$n=abs(S)$. Let ${c_(i j)}_(1<=i,j<=n)$ be a set of complex numbers satisfying
the conditions:
$
  cases(
    c_(i i)=q_i+1 ", where" q_i "is the index parameter"
    op("ind") a_(s_i) ",",
    c_(i j)=c_(j i)=0 & "if" m_(i j)=2 ",",
    c_(i j)c_(j i)=q_i+q_j+2sqrt(q_i q_j)cos (2 pi)/(m_(i j)) & "if" m_(i j)>2.
  )
$
(Here the square root is the positive one, so that $sqrt(q_i q_j)=q_i=q_j$ if
$m_(i j)$ is odd, by @cor:conjugate-simple-reflections-equal-parameters.) Note
that in case $n=2$, $c_(1 2)$ and $c_(2 1)$ are defined in the same way as the
parameters $c_j$ and $d_j$ in @th:rank-two-hecke-irreducible-representations.

#lemma[
  There exists a nonzero symmetric bilinear form $B$ on $V$, such that
  $B(v_i,v_i) != 0$ for $1<=i<=n$, and that satisfies the condition
  $ -c_(i j)=((q_i+1)B(v_i,v_j))/(B(v_i,v_i)), quad 1<=i != j<=n. $
] <lem:hecke-reflection-symmetric-form>
#proof[
  We prove the lemma by induction on the rank $n$. The result is clear if $n=1$,
  so let $n>1$. Since the Coxeter graph of $(W,S)$ is a tree, it follows that
  there exists a subset $J$ of $S$, with $abs(J)=n-1$, such that $(W_J,J)$ is an
  indecomposable Coxeter system. Thus if $s_(i_0) in.not J$, there is a unique
  $s_(j_0) in J$ such that $m_(i_0 j_0)>2$. By the induction hypothesis, we may
  assume that $B$ is defined on the subspace of $V$
  #source(648)
  spanned by ${v_i}_(i != i_0)$. We then extend the definition of $B$ to $V$ by
  setting
  $
    cases(
      B(v_(i_0),v_(j_0))=B(v_(j_0),v_(i_0))
      =-B(v_(j_0),v_(j_0))c_(j_0 i_0)(q_(j_0)+1)^(-1) ",",
      B(v_(i_0),v_(i_0))=-B(v_(i_0),v_(j_0))(q_(i_0)+1)c_(i_0 j_0)^(-1) ",",
      B(v_(i_0),v_j)=B(v_j,v_(i_0))=0 & "if" j != i_0 \, j_0.
    )
  $
  It is easily checked that $B$ satisfies the conditions of the lemma.
]

#lemma[
  For $1<=i != j<=n$, let $lr(chevron.l v_i, v_j chevron.r)$ be the subspace of
  $V$ generated by $v_i$ and $v_j$. Then the restriction
  $B|_(lr(chevron.l v_i, v_j chevron.r))$ is nondegenerate.
] <lem:hecke-reflection-rank-two-nondegeneracy>
#proof[
  The matrix of $B_(lr(chevron.l v_i, v_j chevron.r))$ is
  $ bold(B)_(i j)=mat(B(v_i,v_i), B(v_i,v_j); B(v_j,v_i), B(v_j,v_j)), $
  and it suffices to prove that $det bold(B)_(i j) != 0$. Using
  @lem:hecke-reflection-symmetric-form, it is enough to show that
  $ d=c_(i j)c_(j i)-(q_i+1)(q_j+1) != 0. $
  By the definition of ${c_(i j)}$, we have $d != 0$ if $m_(i j)=2$. Now suppose
  $m_(i j)>2$. Then
  $
    d=2sqrt(q_i q_j)cos theta-q_i q_j-1
    =-(sqrt(q_i q_j)-e^(sqrt(-1)theta))
    (sqrt(q_i q_j)-e^(-sqrt(-1)theta)),
  $
  where $theta=2 pi slash m_(i j)$. It follows that $d != 0$, since $0<theta<pi$
  when $m_(i j)>2$, so $sin theta != 0$, and hence
  $e^(plus.minus sqrt(-1)theta)$ cannot equal the real number $sqrt(q_i q_j)$.
]

#theorem[
  Assume that the Coxeter system $(W,S)$ associated with $G$ is indecomposable,
  and let $cal(H)$ be the Hecke algebra $cal(H)(G,B,1_B)$. There exists a
  representation $T:cal(H) arrow End_CC V$ such that
  $
    T(a_(s_i))v=q_i v-((q_i+1)B(v_i,v))/(B(v_i,v_i)) v_i
    quad "for all" v in V, quad s_i in S.
  $
  The representation $T$ is irreducible, and the bilinear form $B$ is
  nondegenerate on $V$.
] <th:hecke-reflection-representation>
#idx("Reflection representation", target: [@th:hecke-reflection-representation])

#proof[
  For the first statement, it suffices to show that the map $T$, defined on the
  generators ${a_(s_i)}$ of $cal(H)$ as in @th:hecke-reflection-representation,
  preserves the defining relations of $cal(H)$. For each $i$, $1<=i<=n$, we have
  $V=lr(chevron.l v_i chevron.r) plus.o lr(chevron.l v_i chevron.r)^perp$ since
  $B(v_i,v_i) != 0$, where
  $lr(chevron.l v_i chevron.r)^perp={v in V:B(v,v_i)=0}$. Then $T(a_(s_i))$, as
  defined above, acts as scalar multiplication by $q_i$ on
  $lr(chevron.l v_i chevron.r)^perp$ and by $-1$ on
  $lr(chevron.l v_i chevron.r)$. It follows that
  $ T(a_(s_i))^2=q_i dot 1+(q_i-1)T(a_(s_i)), quad 1<=i<=n, $
  and the quadratic relations hold.

  #source(649)
  By Lemma~@lem:hecke-reflection-rank-two-nondegeneracy, the restriction
  $B|_(lr(chevron.l v_i, v_j chevron.r))$, $i != j$, is nondegenerate. Then
  $
    V=lr(chevron.l v_i, v_j chevron.r)
    plus.o lr(chevron.l v_i, v_j chevron.r)^perp.
  $
  On $lr(chevron.l v_i, v_j chevron.r)^perp$, $T(a_(s_i))$ and $T(a_(s_j))$ act
  as scalar multiplications by $q_i$ and $q_j$, respectively. It follows that
  the homogeneous relations for $T(a_(s_i))$ and $T(a_(s_j))$ hold on
  $lr(chevron.l v_i, v_j chevron.r)^perp$, since $q_i=q_j$ if $m_(i j)$ is odd,
  by @cor:conjugate-simple-reflections-equal-parameters. On
  $lr(chevron.l v_i, v_j chevron.r)$, the matrices of $T(a_(s_i))$ and
  $T(a_(s_j))$ are
  $ mat(-1, c_(i j); 0, q_i) quad "and" quad mat(q_j, 0; c_(j i), -1) $
  respectively, by the definition of $B$ (see
  @lem:hecke-reflection-symmetric-form). Then the homogeneous relations also
  hold on $lr(chevron.l v_i, v_j chevron.r)$ by the proof of
  @th:rank-two-hecke-irreducible-representations. Thus $T$ can be extended to
  define a representation of $cal(H)$, by
  @th:iwahori-matsumoto-hecke-presentation.

  We shall prove that $T$ is irreducible, and $B$ nondegenerate, by induction on
  $n$. We may assume $n>1$, and that the result holds for indecomposable Coxeter
  systems of rank $<n$. Choose a subset $J subset S$, $abs(J)=n-1$, as in the
  proof of @lem:hecke-reflection-symmetric-form, and let
  $V_J=lr(chevron.l v_j: s_j in J chevron.r)$. By the induction hypothesis,
  $B|_(V_J)$ is nondegenerate, so $V=V_J plus.o V_J^perp$, and
  $dim_CC V_J^perp=1$.

  Let $cal(H)_J$ be the subalgebra of $cal(H)$ generated by
  ${a_(s_j)}_(s_j in J)$. By the induction hypothesis, the restriction of $T$ to
  $cal(H)_J$ is irreducible on $V_J$, while $V_J^perp$ affords the
  representation $op("ind")$ of $cal(H)_J$, by the first part of the proof. The
  simple $cal(H)_J$-modules $V_J$ and $V_J^perp$ are nonisomorphic, since their
  dimensions are different if $n>=3$, while $V_J$ affords $op("sgn")$ in case
  $n=2$.

  Now consider $V$ as a left $cal(H)$-module. If $V$ is not simple, then
  $V=V' plus.o V''$ for some nontrivial submodules, since $cal(H)$ is
  semisimple. Then both $V'$ and $V''$ are $cal(H)_J$-modules, and hence
  coincide with $V_J$ and $V_J^perp$, by what has been seen earlier. But $V_J$
  is clearly not an $cal(H)$-submodule of $V$, by the properties of $J$ and the
  definition of $T$. This completes the proof that $T$ is irreducible.

  Finally, we prove that $B$ is nondegenerate on $V$. If not, then
  $V^perp != 0$. If $v$ is a nonzero vector in $V^perp$, then by the definition
  of $T$,
  $ T(a_(s_i))v=q_i v, quad 1<=i<=n, $
  and $lr(chevron.l v chevron.r)$ is a proper $cal(H)$-submodule of $V$. This
  contradicts the irreducibility of $T$, and finishes the proof.
]

#remarks(numbered: false)[
  #case-list(
    numbering: "(i)",
    [#case[
      The reader can easily verify that if we set all the parameters ${q_s}$
      equal to $1$, in the definition of $B$ and $T$, then $T$ defines a
      representation of $W$, which is the reflection representation
      @th:finite-coxeter-geometric-representation.
    ] <case:hecke-reflection-specialization>],
    [#case[
      Let $G$ be a finite group with a $B N$-pair, whose Weyl group $(W,S)$ is
      indecomposable. Then there exists a unique character $zeta in Irr G$ such
      that $(zeta,(1_B)^G)>0$, and $zeta|_(cal(H))$ is the character of $T$, by
      @i:th:hecke-character-correspondence. This is called the _reflection
      #source(650)
      character_ of $G$, and has a number of interesting properties. For
      example,
      $ (zeta,(1_(P_J))^G)=1 $
      for all maximal parabolic subgroups of $G$.#ed-note[
        This multiplicity condition alone does not characterize the reflection
        character: $1_G$ has the same multiplicities. Nor is “nontrivial”
        sufficient in general. In rank two with $m=6$ or $8$, every
        two-dimensional family in
        Theorem~@th:rank-two-hecke-irreducible-representations has a
        one-dimensional index eigenspace for each generator, giving respectively
        two or three such nontrivial $G$-characters by
        Corollary~@cor:rank-two-principal-series-character-degrees.
      ] Its degree has been computed explicitly for each individual type of
      Coxeter group (Curtis–Iwahori–Kilmoyer @bib:Curtis1971), and in case $G$
      is a Chevalley group, its values on regular $p'$-elements have been
      determined by Lusztig @bib:Lusztig1979, for Weyl groups of type $A_n$,
      $D_n$, and $E_n$, $n=6,7,8$.
    ] <case:finite-group-reflection-character>],
    [#case[
      The reflection representation of an indecomposable Coxeter group has the
      property that all its exterior powers are also irreducible. Corresponding
      irreducible representations of $cal(H)$ were constructed explicitly by
      Kilmoyer (see Curtis–Iwahori–Kilmoyer @bib:Curtis1971).
    ] <case:hecke-reflection-exterior-powers>],
  )
] <rem:hecke-reflection-character-properties>

#exercises-heading

#exercise[
  Let $W=lr(chevron.l s_1, s_2 ":" s_1^2=s_2^2=(s_1 s_2)^m=1 chevron.r)$ be a
  dihedral group of order $2m$. Define an incidence structure whose set of
  points is the coset space $W slash lr(chevron.l s_1 chevron.r)$, and whose
  lines are the cosets $W slash lr(chevron.l s_2 chevron.r)$. A point
  $x lr(chevron.l s_1 chevron.r)$ and a line $y lr(chevron.l s_2 chevron.r)$ are
  defined to be incident if their intersection is nonempty. Prove that the
  incidence structure is an ordinary $m$-gon (see
  §~@ss:feit-higman-generalized-polygons).
] <exc:dihedral-coset-polygon>

#exercise[
  (Feit–Higman @bib:Feit1964). Let $G$ be a finite group with a $B N$-pair of
  rank $2$, whose Weyl group $W=lr(chevron.l s_1, s_2 chevron.r)$ is dihedral of
  order $2m$. Let $P_1=B union B s_1 B$ and $P_2=B union B s_2 B$, where $B$ is
  the given Borel subgroup. Define an incidence structure $(cal(P),cal(L))$,
  whose set of points $cal(P)$ is the coset space $G slash P_1$, and whose set
  of lines $cal(L)$ is the set of cosets $G slash P_2$, with incidence defined
  as in Exercise~@exc:dihedral-coset-polygon.
  #case-list(numbering: "(i)", [#case[
    Define a double-coset incidence structure ${hat(cal(P)),hat(cal(L))}$, whose
    set of points $hat(cal(P))$ consists of the double cosets
    ${B g P_1:g in G}$, and whose lines are the double cosets
    ${B h P_2:h in G}$, with incidence defined as above. Prove that the double
    coset geometry is an ordinary $m$-gon.
  ] <case:bn-pair-double-coset-polygon>])
  #hint([@exc:rank-two-bn-pair-generalized-polygon])[
    Use @th:bn-pair-parabolic-double-cosets and the preceding exercises.
  ]
  #case-list(start: 2, numbering: "(i)", [#case[
    Prove that the coset geometry $(cal(P),cal(L))$ is a generalized $m$-gon.
  ] <case:bn-pair-coset-generalized-polygon>])
  #hint([@exc:rank-two-bn-pair-generalized-polygon])[
    Prove that if $X in cal(P) union cal(L)$, and if $B X$ is incident to
    $Z=B g P_i$ in the double-coset geometry, then $Z=B Y$, for
    $Y in cal(P) union cal(L)$ and $X inter Y != emptyset$. In order to prove
    that $rho(x, y)<=m$, it may be assumed that $Y=P_1$ or $P_2$ since $G$ acts
    transitively on the coset spaces $G slash P_1$ and $G slash P_2$. Then use
    the preceding remarks to show that if $Z_0=B X,dots,Z_h=B Y$ is a chain of
    length $<=m$ in the double-coset geometry then $Z_0=B X$,
    $Z_1=B X_1,dots,Z_h=B X_h$ for a chain $X_0=X,dots,X_h$ of length $<=m$ in
    the coset geometry. The same idea, along with properties of $B N$-pairs from
    §~@sec:finite-groups-bn-pairs, can be used to prove
    @case:generalized-polygon-short-geodesic-unique and
    @case:generalized-polygon-opposite-vertices of @def:generalized-polygon.
  ]
  #case-list(start: 3, numbering: "(i)", [#case[
    Prove that there are $[P_2:B]$ points on each line, and $[P_1:B]$ lines
    through each point, in the generalized $m$-gon $(cal(P),cal(L))$.
  ] <case:bn-pair-polygon-valencies>])
  #hint([@exc:rank-two-bn-pair-generalized-polygon])[
    The number of points on each line is the number of cosets $g P_1$
    intersecting a given coset $g' P_2$. Show that if it is nonempty, the
    intersection is given by $g P_1 inter g' P_2=g''(P_1 inter P_2)=g'' B$.
  ]
] <exc:rank-two-bn-pair-generalized-polygon>
