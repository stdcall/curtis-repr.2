#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/38c-resolutions.typ": *

=== Regular Rings <ss:regular-rings>

In §@ss:grothendieck-frobenius, we needed to distinguish between the
Grothendieck groups $G_0 lr((R G))$ and $G_0^R lr((R G))$, the first of which
was associated with the category of all f.g. $R G$-modules, and the second with
the category of $R G$-lattices. We shall see here that under suitable conditions
on $R$, there is an isomorphism $G_0 lr((R G)) tilde.equiv G_0^R lr((R G))$ of
additive groups, a result which will be extremely useful. It will be convenient
to treat a somewhat more general situation, rather than that of group rings.

Throughout this subsection, $Lambda$ denotes an arbitrary left noetherian
ring.#footnote[Some of the results are true even when $Lambda$ is not
  noetherian.] _All $Lambda$-modules considered are assumed to be f.g. left
$Lambda$-modules._ Let $cal(P)(Lambda)$ denote the category of (f.g.) projective
$Lambda$-modules. Given any $Lambda$-module $M$, and any integer $n >= 1$, we
can always find a $Lambda$-exact sequence:#footnote[This means an exact sequence
  of $Lambda$-modules.]
$
  0 -> L -> P_(n-1) arrow.r^(phi_(n-1)) dots arrow.r^(phi_1)
  P_0 arrow.r^(phi_0) M -> 0, quad P_i in cal(P)(Lambda),
$
<eq:partial-projective-resolution>
with $L$ some $Lambda$-module (see §@i:ss:ext-tor).

#definition[
  The $Lambda$-module $M$ has _finite homological dimension_
  $op("hd")_Lambda lr((M))$ if there exists a $Lambda$-exact sequence
  @eq:partial-projective-resolution in which $L$ is $Lambda$-projective. We
  write $op("hd")_Lambda lr((M)) <= n$ in this case. If $n$ is the least
  nonnegative integer for which $op("hd")_Lambda lr((M)) <= n$, we write
  $op("hd")_Lambda lr((M)) = n$. Finally, write
  $op("hd")_Lambda lr((M)) = infinity$ if $M$ does not have finite homological
  dimension.
] <def:homological-dimension>
#nidx(
  "$op(\"hd\")_A M$",
  "homological dimension",
  target: [@def:homological-dimension],
)
#idx("Finite homological dimension", target: [@def:homological-dimension])
#idx("Homological dimension", target: [@def:homological-dimension])

#source(36)
We have previously encountered this concept in Volume I
(§@i:ss:maximal-orders-hereditary), and we prove first that the above definition
agrees with our earlier one. Of course,
$
  op("hd")_Lambda lr((M)) = 0 arrow.l.r.double M in cal(P)(Lambda)
  arrow.l.r.double op("Ext")_Lambda^k lr((M, ast)) = 0 quad "for" k >= 1.
$
<eq:homological-dimension-zero>
The first equivalence is clear, while the second follows from
@i:rem:ext-properties(v). We now prove

#proposition[
  Let $M$ be a $Lambda$-module. Then
  $
    op("hd")_Lambda lr((M)) <= n quad "if and only if" quad
    op("Ext")_Lambda^k lr((M, ast)) = 0 quad "for" k >= n + 1.
  $
] <prop:homological-dimension-ext-criterion>
#proof[
  Suppose $op("hd")(M) <= n$ (we omit the subscript $Lambda$ for convenience).
  Then the module $L$ in some sequence @eq:partial-projective-resolution is
  $Lambda$-projective, and the sequence is a projective resolution of $M$. It
  follows from @i:eq:ext-definition that $op("Ext")^k lr((M, ast)) = 0$ whenever
  $k >= n + 1$.

  Conversely, suppose that $op("Ext")^(n+1) lr((M, ast)) = 0$, and let us prove
  that in any $Lambda$-exact sequence @eq:partial-projective-resolution, the
  module $L$ must be projective. The case $n = 0$ has already been settled, so
  let $n >= 1$. We may break @eq:partial-projective-resolution into a succession
  of ses’s:
  $
    0 -> L_0 -> P_0 arrow.r^(phi_0) M -> 0,
    quad 0 -> L_1 -> P_1 arrow.r^(phi_1) L_0 -> 0, dots,
    0 -> L -> P_(n-1) -> L_(n-2) -> 0
  $
  where $L_0 = ker phi_0$, $L_1 = ker phi_1$, and so on. From
  @i:eq:ext-long-exact-first-variable we obtain readily
  $
    op("Ext")^(n+1) lr((M, X)) tilde.equiv op("Ext")^n lr((L_0, X))
    tilde.equiv op("Ext")^(n-1) lr((L_1, X)) tilde.equiv dots
    tilde.equiv op("Ext")^1 lr((L, X)),
  $
  for each $Lambda$-module $X$. Thus, $op("Ext")^1 lr((L, ast)) = 0$, so $L$ is
  projective.
]

The preceding result implies that if there exists one sequence
@eq:partial-projective-resolution in which the left-most term $L$ is projective,
then the left-most term $L$ is necessarily projective in _every_ such sequence.
This also follows from

#lemma(name: "Generalized Schanuel’s Lemma")[
  Given a pair of $Lambda$-exact sequences
  $
    0 -> L -> P_(n-1) -> dots -> P_0 -> M -> 0,
    quad 0 -> L' -> P'_(n-1) -> dots -> P'_0 -> M -> 0,
  $
  with each $P_i$ and $P'_i$ projective, we have an isomorphism#footnote[
    The final terms in the isomorphism are $P_0$ and $P'_0$, and these occur on
    opposite sides, depending on the parity of $n$.
  ]
  $
    L plus.o P'_(n-1) plus.o P_(n-2) plus.o P'_(n-3) plus.o dots
    tilde.equiv L' plus.o P_(n-1) plus.o P'_(n-2) plus.o P_(n-3) plus.o dots.
  $
] <lem:generalized-schanuel>
#idx("Generalized Schanuel's Lemma", target: [@lem:generalized-schanuel])
#idx("Schanuel's Lemma (generalized)", target: [@lem:generalized-schanuel])
#proof[
  This follows from Schanuel’s Lemma @i:lem:schanuel, together with the
  decomposition of a long exact sequence into ses’s, as in the preceding proof.
  The details are left to the reader.
]

#source(37)
Suppose now that we are given an exact sequence of $Lambda$-modules
$ 0 -> M' -> M -> M'' -> 0. $ <eq:resolution-comparison-sequence>
We wish to compare projective resolutions and homological dimensions of these
modules. The comparison of homological dimension is an easy consequence of
@i:th:ext-long-exact-sequence; see Exercise
@exc:homological-dimension-short-exact. However, the approach by means of
projective resolutions yields more information, which will be needed for the
proofs of the basic theorems @th:regular-grothendieck-k0 and
@th:regular-grothendieck-k1 below. We shall start with partial projective
resolutions of $M'$ and $M''$, and show how to combine them to give such a
resolution of $M$. We have

#lemma(name: "Horseshoe Lemma")[
  Consider a “horseshoe” diagram of $Lambda$-modules
  #horseshoe-input
  where the column is exact (as in @eq:resolution-comparison-sequence), and
  where the rows are exact, with each $P'_i$, $P''_i$ projective. Then there
  exist a $Lambda$-module $K$ and maps for which the following diagram commutes,
  and has exact rows and exact columns:
  #horseshoe-output
  Each upper vertical arrow is injective, each lower one surjective.
] <lem:horseshoe>
#idx("Horseshoe Lemma", target: [@lem:horseshoe])
#proof[Left as exercise for the reader. Use induction on $n$.]

#definition[
  The (left) _global dimension_ $op("gl. dim.") Lambda$ of a ring $Lambda$ is
  defined by
  $
    op("gl. dim.") Lambda = sup {op("hd")_Lambda lr((M)):
      M = Lambda "-module"}.
  $
] <def:global-dimension>
#nidx(
  "$op(\"gl. dim.\")$",
  "global dimension",
  target: [@def:global-dimension],
)
#idx("Global dimension", target: [@def:global-dimension])

As shown by M. Auslander, one can compute $op("gl. dim.") Lambda$ by studying
f.g. $Lambda$-modules, and indeed even just cyclic modules.
#source(38)
This follows from the formula
$
  op("gl. dim.") Lambda = sup {op("hd")_Lambda lr((Lambda slash L)):
    L = "left ideal of" Lambda}
$
(see Rotman @bib:Rotman1979, Theorem 9.12 for a proof).

We remark that $op("gl. dim.") Lambda = 0$ if and only if every left
$Lambda$-module is projective, or equivalently, if and only if $Lambda$ is a
semisimple ring. Next, we note that $op("gl. dim.") Lambda <= 1$ if and only if
$Lambda$ is left hereditary. For, if $op("gl. dim.") Lambda <= 1$, then consider
the sequence $0 -> M -> Lambda -> Lambda slash M -> 0$, where $M$ is any left
ideal of $Lambda$. Since $op("hd")_Lambda lr((Lambda slash M)) <= 1$, it follows
that $M$ must be $Lambda$-projective, and so $Lambda$ is left hereditary.
Conversely, if $Lambda$ is left hereditary, then every submodule of a free
$Lambda$-module is projective (see @i:prop:hereditary-free-submodules), which
easily implies that $op("gl. dim.") Lambda <= 1$.

In particular, by @i:prop:dedekind-domain-criteria every Dedekind domain $R$ is
hereditary, and thus $op("gl. dim.") R <= 1$. (Indeed, $op("gl. dim.") R = 1$ if
$R$ is not a field!)

#definition[
  A left noetherian ring $Lambda$, such that every f.g. left $Lambda$-module $M$
  has finite homological dimension, is called a (left) _regular ring_.
] <def:regular-ring>
#idx("Regular ring", target: [@def:regular-ring])

All semisimple rings and all hereditary noetherian rings are regular. In
particular, every Dedekind domain is a regular ring.

(We caution the reader that there exist regular rings $Lambda$ for which
$op("gl. dim.") Lambda = infinity$. However, if $Lambda$ is noetherian and
$op("gl. dim.") Lambda$ is finite, then, of course, $Lambda$ is a regular ring.)

From now on, let $R$ be a commutative regular ring, so $R$ is noetherian, and
every f.g. $R$-module has finite homological dimension. Let $Lambda$ be an
$R$-algebra (see §@i:ss:algebras-integral-closure), and assume always that
$Lambda$ is f.g. and projective as $R$-module. (This certainly holds in case
$Lambda$ is a group ring $R G$, where $G$ is a finite group.) As usual, a
$Lambda$-_lattice_#idx("Lattice") is a left $Lambda$-module which is f.g. and
projective as $R$-module (see §@i:sec:lattices-orders).

Let $G_0 lr((Lambda))$, $G_1 lr((Lambda))$ be defined as in
§@ss:grothendieck-projective. Let $G_0^R lr((Lambda))$ and $G_1^R lr((Lambda))$
be defined analogously, by restricting our attention to $Lambda$-lattices rather
than arbitrary f.g. $Lambda$-modules. Our aim here is to establish the
isomorphisms
$
  G_0 lr((Lambda)) tilde.equiv G_0^R lr((Lambda)),
  quad G_1 lr((Lambda)) tilde.equiv G_1^R lr((Lambda)),
$
whenever $R$ is regular.

#theorem[
  Let $R$ be a commutative regular ring, and let $Lambda$ be an $R$-algebra,
  f.g. and projective as $R$-module. Then there is an isomorphism
  $ f: G_0^R lr((Lambda)) tilde.equiv G_0 lr((Lambda)), $
  defined by $f[M] = [M]$ for every $Lambda$-lattice $M$.
] <th:regular-grothendieck-k0>
#proof[
  The map $f$ is a well-defined homomorphism, and we need only construct an
  inverse map $g$. Given any f.g. $Lambda$-module $M$, let $n$ be such that
  $op("hd")_R lr((M)) <= n$, and choose a $Lambda$-exact sequence
  @eq:partial-projective-resolution with each $P_i in cal(P)(Lambda)$. Since
  $Lambda$ is $R$-projective, so is each $P_i$. Therefore $L$ is also
  $R$-projective, and is thus a $Lambda$-lattice.
  #source(39)
  We now put
  $
    g[M] = [P_0] - [P_1] + dots + (-1)^(n-1)[P_(n-1)]
    + (-1)^n [L] in G_0^R lr((Lambda)).
  $
  It follows at once from the Generalized Schanuel’s Lemma that $g[M]$ does not
  depend on the choice of the sequence @eq:partial-projective-resolution.
  Further, given @eq:resolution-comparison-sequence, we first choose partial
  resolutions of $M'$ and $M''$, and then use the Horseshoe Lemma to obtain one
  of $M$. It is then clear that $g[M] = g[M'] + g[M'']$, so $g$ is a
  well-defined homomorphism from $G_0 lr((Lambda))$ into $G_0^R lr((Lambda))$.
  It is straightforward to check that $g f = 1$ and $f g = 1$, so both $f$ and
  $g$ are isomorphisms, and the theorem is proved.
]

In the special case where $Lambda = R$, a $Lambda$-lattice $M$ is just a module
$M in cal(P)(Lambda)$. Thus, the theorem gives
$ K_0 lr((R)) tilde.equiv G_0 lr((R)) $
whenever $R$ is a commutative regular ring. As we shall see in
@cor:regular-ring-k-g-isomorphisms below, this isomorphism holds for an
arbitrary regular ring, not necessarily commutative.

We shall apply Theorem @th:regular-grothendieck-k0 to study the behavior of
$G_0$ and $K_0$ under ground ring extension. Given any ring homomorphism
$phi: Lambda -> Gamma$, there is an additive homomorphism
$K_0 lr((Lambda)) -> K_0 lr((Gamma))$, given by $Gamma times.o_Lambda ast$. This
means that we use $phi$ to make $Gamma$ into a right $Lambda$-module, and then
the map $K_0 lr((Lambda)) -> K_0 lr((Gamma))$ is given by
$[M] -> [Gamma times.o_Lambda M]$, for $M in cal(P)(Lambda)$. There is no
corresponding map $G_0 lr((Lambda)) -> G_0 lr((Gamma))$ in general, although
such a map is well defined whenever $Gamma$ is flat as right $Lambda$-module.

Suppose in particular that $Lambda$ is an $R$-algebra, and that $f: R -> S$ is a
homomorphism of commutative rings. Then there is a homomorphism
$ S times.o_R ast: K_0 lr((Lambda)) -> K_0 lr((S times.o_R Lambda)). $
As remarked earlier, this need not define a map on $G_0$, since $S$ need not be
$R$-flat. Nevertheless, we have

#proposition[
  Let $R$ be a commutative regular ring, and let $Lambda$ be an $R$-algebra,
  f.g. and projective as $R$-module. Let $f: R -> S$ be a homomorphism of
  commutative rings. Then there is an additive homomorphism
  $ phi: G_0 lr((Lambda)) -> G_0 lr((S times.o_R Lambda)), $
  defined by composition of maps
  $
    G_0 lr((Lambda)) arrow.r^alpha G_0^R lr((Lambda)) arrow.r^beta
    G_0^S lr((S times.o Lambda)) arrow.r^gamma G_0 lr((S times.o Lambda)),
  $
  where $times.o$ means $times.o_R$.
] <prop:regular-grothendieck-base-change>
#source(40)
#proof[
  The map $alpha$ is the isomorphism defined in @th:regular-grothendieck-k0,
  while $gamma$ is the obvious map (taking lattices to modules). Finally, $beta$
  is well-defined, since each ses of $Lambda$-lattices
  @eq:resolution-comparison-sequence is $R$-split; therefore $S times.o ast$
  preserves exactness (and splitting!).
]

#remarks(name: "Caution", numbered: false)[
  #enum(
    numbering: "(i)",
    [If $M$ is an arbitrary f.g. $Lambda$-module, then $phi[M]$ need not equal
      $[S times.o M]$ in $G_0 lr((S times.o Lambda))$. In order to compute
      $phi[M]$, we first choose a sequence @eq:partial-projective-resolution,
      and then
      $
        phi[M] = [S times.o P_0] - [S times.o P_1] + dots
        + (-1)^n [S times.o L] in G_0 lr((S times.o Lambda)).
      $],
    [Suppose for the moment that $Lambda = R G$, where $R$ is any commutative
      ring, and $G$ is a finite group. As remarked in
      §@ss:grothendieck-frobenius, $G_0^R lr((Lambda))$ is a commutative ring,
      with multiplication given by
      $ [M][N] = [M times.o_R N], $ <eq:regular-grothendieck-ring-product>
      where $M times.o_R N$ is the inner tensor product of the $Lambda$-lattices
      $M$ and $N$. The identity element of $G_0^R lr((Lambda))$ is the
      $G$-trivial $Lambda$-lattice $R$. If $R$ is regular, we can use the
      additive isomorphism $G_0 lr((Lambda)) tilde.equiv G_0^R lr((Lambda))$ to
      make $G_0 lr((Lambda))$ into a commutative ring as well. However, if $M$
      and $N$ are arbitrary f.g. $Lambda$-_modules_, then formula
      @eq:regular-grothendieck-ring-product need not be valid inside
      $G_0 lr((Lambda))$.],
  )
] <rem:regular-base-change-caution>

Next, we establish the analogue of Theorem @th:regular-grothendieck-k0 for $G_1$
in place of $G_0$. For an $R$-algebra $Lambda$, we define $G_1 lr((Lambda))$ as
in @def:whitehead-determinantal-group. Also, we define $G_1^R lr((Lambda))$ by
using the category of all $Lambda$-lattices. We have

#theorem[
  Let $R$ be a commutative regular ring, and let $Lambda$ be an $R$-algebra,
  f.g. and projective as $R$-module. Then there is an isomorphism
  $ G_1^R lr((Lambda)) tilde.equiv G_1 lr((Lambda)), $
  given by $[M, mu] -> [M, mu]$ for each $Lambda$-lattice $M$ and each
  $mu in Aut M$.
] <th:regular-grothendieck-k1>
#proof[
  _Step 1._ For $n >= 0$, let
  $
    cal(C)_n = {M: M = "f.g. left" Lambda "-module,"
      quad op("hd")_R lr((M)) <= n}.
  $
  Thus $cal(C)_0$ is the category of all $Lambda$-lattices, and every f.g.
  $Lambda$-module belongs to $cal(C)_n$ for all sufficiently large $n$. Let
  $H_n$ be the abelian group generated by all symbols $[M, mu]$,
  $M in cal(C)_n$, subject to the standard relations arising from
  @eq:determinantal-exact-relation and @eq:determinantal-composition-relation.
  The inclusion $cal(C)_n subset.eq cal(C)_(n+1)$ induces a homomorphism
  $H_n -> H_(n+1)$, and we may identify $G_1 lr((Lambda))$ with the direct limit
  $lim H_n$. This means that every element of $G_1 lr((Lambda))$ lies in some
  $H_n$, and that if $x in H_n$, $y in H_m$, then $x = y$ in $G_1 lr((Lambda))$
  if and only if $x$ and $y$ have the same images in some $H_r$, where $r >= m$
  and $r >= n$. Now $H_0 = G_1^R lr((Lambda))$, and we shall prove that for each
  $n$, the inclusion $cal(C)_n subset.eq cal(C)_(n+1)$ yields an isomorphism
  $H_n tilde.equiv H_(n+1)$. It will then follow that
  $H_0 tilde.equiv H_1 tilde.equiv dots tilde.equiv lim H_n = G_1 lr((Lambda))$,
  and the theorem will be established.

  #source(41)
  _Step 2._ We claim that for each f.g. $Lambda$-module $M$, there exists a
  surjection
  $ f_0: P_0 -> M, quad "where" P_0 in cal(P)(Lambda), $
  such that every automorphism $mu$ of $M$ lifts to an automorphism $pi_0$ of
  $P_0$. In other words, there exists a morphism $f_0$ of $(P_0, pi_0)$ onto
  $(M, mu)$.

  To begin with, let $f: P -> M$ be a surjection, with $P in cal(P)(Lambda)$.
  Set $P_0 = P plus.o P$, and let $f_0: P_0 -> M$ be the map defined by
  composition
  $ P_0 = P plus.o P arrow.r^((f, f)) M plus.o M arrow.r^((1, 0)) M, $
  so $f_0$ is surjective. Given any $mu in Aut M$, consider the following
  commutative diagram, to be solved for $pi_0 in Aut P_0$:
  #automorphism-lifting
  Such a $pi_0$ will be a lifting of $mu$, as required.

  Let $Gamma = End_Lambda M$, and view the map $(mu, mu^(-1))$ as a matrix
  $op("diag")(mu, mu^(-1)) in GL_2 lr((Gamma))$. This matrix can be written as a
  product of elementary matrices, as in
  @i:eq:balanced-units-elementary-factorization, and it suffices to show that
  each of these elementary matrices can be lifted to an automorphism of $P_0$.
  Consider, for example, the matrix
  $ mat(1, alpha; 0, 1), quad "where" alpha in Gamma. $
  It acts on $M plus.o M$ according to the rule
  $ (m_1, m_2) -> (m_1, m_2 + alpha m_1), quad m_i in M. $
  Symbolically, the automorphism of $M plus.o M$ given thus may be written as
  #elementary-action
  Since $f: P -> M$ is surjective, we can lift $alpha$ to an endomorphism
  $theta$ of $P$, by @i:prop:projective-module-criteria(iii). There is then a
  commutative diagram
  #elementary-lifting
  so $mat(1, theta; 0, 1)$ is the desired lifting of $mat(1, alpha; 0, 1)$. A
  similar argument holds for $mat(1, 0; alpha, 1)$, and we have now established
  the claim made at the start of this step.

  #source(42)
  _Step 3._ Now let $n >= 1$, and let $phi: H_(n-1) -> H_n$ be induced by
  $cal(C)_(n-1) subset.eq cal(C)_n$. We show that $phi$ is an isomorphism, by
  constructing an inverse map $psi: H_n -> H_(n-1)$. For this purpose, we shall
  view the category of ordered pairs $(M, mu)$ as a category of modules.
  Specifically, consider the polynomial ring $Lambda[x]$, where $x$ is an
  indeterminate which commutes with the elements of $Lambda$. Then $(M, mu)$ may
  be viewed as a left $Lambda[x]$-module $M$, on which $x$ acts as $mu$. We can
  thus apply module-theoretic arguments to such pairs.

  Given $M in cal(C)_n$, choose a surjection $f: P -> M$ with
  $P in cal(P)(Lambda)$, such that every automorphism $mu$ of $M$ lifts to an
  automorphism $pi$ of $P$. Letting $X = ker f$, we see from
  @lem:generalized-schanuel that $X in cal(C)_(n-1)$. Further, if $xi = pi|_X$,
  then $xi in Aut X$, and the sequence
  $ 0 -> (X, xi) -> (P, pi) arrow.r^f (M, mu) -> 0 $
  <eq:automorphism-projective-presentation>
  is exact. But then
  $ [M, mu] = [P, pi] - [X, xi] quad "in" H_n, $
  <eq:determinantal-resolution-relation>
  which proves that $phi$ maps $H_(n-1)$ _onto_ $H_n$. We now define
  $ psi[M, mu] = [P, pi] - [X, xi], $
  so $psi$ is a map from $H_n$ to $H_(n-1)$. In order to verify that $psi$ is a
  well-defined homomorphism, we must prove:
  #enum(
    numbering: "(a)",
    [$psi[M, mu]$ is independent of the choice of the sequence
      @eq:automorphism-projective-presentation.],
    [For $mu_1, mu_2 in Aut M$,
      $ psi[M, mu_1 mu_2] = psi[M, mu_1] + psi[M, mu_2]. $],
    [For each exact sequence
      $ 0 -> (M', mu') arrow.r^g (M, mu) arrow.r^h (M'', mu'') -> 0, $
      <eq:automorphism-horseshoe-sequence>
      where each module lies in $cal(C)_n$, we have
      $ psi[M, mu] = psi[M', mu'] + psi[M'', mu'']. $
      <eq:determinantal-resolution-additivity>],
  )
  To prove (a), consider another exact sequence
  $ 0 -> (X', xi') -> (P', pi') arrow.r^(f') (M, mu) -> 0, $
  with $P' in cal(P)(Lambda)$.
  #source(43)
  We now imitate the proof of Schanuel’s Lemma, viewing the ordered pairs as
  $Lambda[x]$-modules. Let $(Y, eta)$ be the pullback of the pair of maps
  $f, f'$. Then there is a commutative diagram of $Lambda[x]$-modules, with
  exact rows and columns:
  #automorphism-pullback
  Then $0 -> X -> Y -> P' -> 0$ is a $Lambda$-exact sequence, and so
  $Y tilde.equiv X plus.o P' in cal(C)_(n-1)$. Further, since $pi$ and $xi'$ are
  automorphisms, so is $eta$ (by the Snake Lemma). Using exactness of rows and
  columns above, we obtain two identities in $H_(n-1)$:
  $
    [Y, eta] = [X, xi] + [P', pi'],
    quad [Y, eta] = [X', xi'] + [P, pi].
  $
  This yields
  $ [P, pi] - [X, xi] = [P', pi'] - [X', xi'], $
  and completes the proof of (a).

  For (b), choose $f: P -> M$ as in @eq:automorphism-projective-presentation.
  Given $mu_1, mu_2 in Aut M$, we may find $pi_i in Aut P$, $xi_i in Aut X$,
  $i = 1, 2$, such that $pi_i$ lifts $mu_i$. Then $pi_1 pi_2$ lifts $mu_1 mu_2$,
  and we have
  $
    psi[M, mu_1 mu_2] & = [P, pi_1 pi_2] - [X, xi_1 xi_2] \
                      & = [P, pi_1] + [P, pi_2] - [X, xi_1] - [X, xi_2]
                        quad "in" H_(n-1),
  $
  which proves (b).

  Finally, we prove (c) by giving the first step in the proof of the Horseshoe
  Lemma in the present context. Starting with
  @eq:automorphism-horseshoe-sequence, choose surjections $f': P' -> M'$,
  $f'': P'' -> M''$, where $P', P'' in cal(P)(Lambda)$, with the lifting
  property for automorphisms. There is an exact sequence
  $ 0 -> (X', xi') -> (P', pi') arrow.r^(f') (M', mu') -> 0, $
  where $X' = ker f'$. Choose $f: P -> M$ as in
  @eq:automorphism-projective-presentation, and define a pair of morphisms:
  $
    (P', pi') arrow.r^(g f') (M, mu),
    quad (P, pi) arrow.r^(h f) (M'', mu'').
  $

  #source(44)
  Now pick $(X_0, xi_0)$ so that
  $
    0 -> (X_0, xi_0) -> (P', pi') plus.o (P, pi)
    arrow.r^((g f', f)) (M, mu) -> 0
  $
  is exact. Likewise, choose $(X'', xi'')$ so that
  $ 0 -> (X'', xi'') -> (P, pi) arrow.r^(h f) (M'', mu'') -> 0 $
  is exact. Clearly each of $X_0, X'$, and $X''$ lies in $cal(C)_(n-1)$, and
  there is a commutative diagram with exact rows and columns:
  #automorphism-horseshoe
  Viewing the pairs as $Lambda[x]$-modules, the Snake Lemma yields an exact
  sequence
  $ 0 -> (X', xi') -> (X_0, xi_0) -> (X'', xi'') -> 0. $
  Therefore
  $ [X_0, xi_0] = [X', xi'] + [X'', xi''] quad "in" H_(n-1). $
  (The Snake Lemma also shows that $xi''$ and $xi_0$ are automorphisms.) Now
  $ psi[M, mu] = [P', pi'] + [P, pi] - [X_0, xi_0], $
  $
    psi[M', mu'] = [P', pi'] - [X', xi'],
    quad psi[M'', mu''] = [P, pi] - [X'', xi''],
  $
  and so we obtain the desired formula @eq:determinantal-resolution-additivity.

  We have thus verified (a)–(c), so $psi: H_n -> H_(n-1)$ is a well-defined
  homomorphism. Next, if $M in cal(C)_(n-1)$ then
  @eq:determinantal-resolution-relation holds in $H_(n-1)$ as well as in $H_n$.
  This implies that $psi phi = 1$, so $phi$ is injective. We have shown above
  that $phi$ is surjective, so we conclude that $phi$ is an isomorphism, and the
  theorem is proved.
]

In the above proof, we have followed the treatment in Swan @bib:Swan1968. For
more general theorems of the above type, see Swan @bib:Swan1968, pages 224–247,
and especially (16.15)–(16.17).

For an arbitrary category $cal(C)$ of modules, we have defined
$K_0 lr((cal(C)))$ in @i:def:grothendieck-category-group; it is generated by
symbols $[M]$, $M in cal(C)$, with relations arising from ses’s of modules in
$cal(C)$. Also, we defined $K_"det" lr((cal(C)))$ in @eq:determinantal-k-group;
it is generated by symbols $[M, mu]$, $M in cal(C)$, $mu in Aut M$, with
relations of the types @eq:determinantal-exact-relation and
@eq:determinantal-composition-relation.
#source(45)
In the special case where $cal(C) = cal(P)(Lambda)$, the category of f.g.
projective $Lambda$-modules, we defined
$
  K_0 lr((Lambda)) = K_0 lr((cal(P)(Lambda))),
  quad K_1 lr((Lambda)) = K_"det" lr((cal(P)(Lambda))).
$

Following this review, we give some easy consequences of the proofs of Theorems
@th:regular-grothendieck-k0 and @th:regular-grothendieck-k1, namely:

#theorem[
  Let $Lambda$ be an arbitrary noetherian ring, and let $cal(C)$ be the category
  of all f.g. left $Lambda$-modules $M$ for which $op("hd")_Lambda lr((M))$ is
  finite. Then there exist isomorphisms
  $
    K_0 lr((Lambda)) tilde.equiv K_0 lr((cal(C))),
    quad K_1 lr((Lambda)) tilde.equiv K_"det" lr((cal(C))).
  $
] <th:finite-homological-dimension-k-groups>
#proof[
  Let $cal(C)_n$ be the category of all f.g. $Lambda$-modules $M$ with
  $op("hd")_Lambda lr((M)) <= n$. The proof of @th:regular-grothendieck-k1 shows
  that the inclusion $cal(C)_(n-1) subset.eq cal(C)_n$ induces an isomorphism
  $K_"det" lr((cal(C)_(n-1))) tilde.equiv K_"det" lr((cal(C)_n))$. This implies
  that
  $
    K_1 lr((Lambda)) = K_"det" lr((cal(C)_0))
    tilde.equiv K_"det" lr((cal(C)_1)) tilde.equiv dots
    tilde.equiv K_"det" lr((cal(C))).
  $
  If we omit all of the automorphisms, we get likewise
  $K_0 lr((Lambda)) tilde.equiv K_0 lr((cal(C)))$, and the theorem is proved.
]

We have at once:

#corollary[
  If $Lambda$ is a left regular ring, then
  $
    K_0 lr((Lambda)) tilde.equiv G_0 lr((Lambda)),
    quad K_1 lr((Lambda)) tilde.equiv G_1 lr((Lambda)).
  $
] <cor:regular-ring-k-g-isomorphisms>

In the remarks following @th:regular-grothendieck-k0, we already pointed out
that $K_0 lr((Lambda)) tilde.equiv G_0 lr((Lambda))$ for $Lambda$ a commutative
regular ring.

Our last topic in this subsection is the computation of the group $K_0 lr((R))$
for a Dedekind domain $R$. More precisely, we shall express $K_0 lr((R))$ in
terms of the ideal class group $op("Cl")(R)$ defined in
§@i:ss:ideal-class-groups-global-fields.

#theorem[
  Let $R$ be a Dedekind domain. Then
  $ K_0 lr((R)) tilde.equiv ZZ plus.o op("Cl")(R), $
  that is, $K_0 lr((R))$ is the direct product of the additive group $ZZ$ and
  the multiplicative group $op("Cl")(R)$.
] <th:dedekind-projective-class-group>
#proof[
  Steinitz’s Theorem tells us that each $M in cal(P)(R)$ is expressible as an
  external direct sum
  $ M = product.co_(i=1)^r J_i, $ <eq:dedekind-projective-ideal-sum>
  with each $J_i$ a nonzero ideal of $R$.
  #source(46)
  The isomorphism class of $M$ is uniquely determined by the rank
  $r = r(M)$#idx("Rank") and the ideal class of the product $J_1 dots J_r$. This
  ideal class is called the _Steinitz class_ of $M$, and we shall denote it for
  the moment by $op("St")(M)$.#idx("Steinitz class")

  Now $K_0 lr((R))$ is generated by stable isomorphism classes $[X]$ of modules
  $X in cal(P)(R)$. However, for $X, Y in cal(P)(R)$,
  $
    X plus.o R^((k)) tilde.equiv Y plus.o R^((k))
    arrow.r.double X tilde.equiv Y,
  $
  by Steinitz’s Theorem. Thus, $K_0 lr((R))$ is generated by symbols $[X]$,
  $X in cal(P)(R)$, and $[X] = [Y]$ in $K_0 lr((R))$ if and only if
  $X tilde.equiv Y$. The relations in $K_0 lr((R))$ are given by
  $ [X] + [X'] = [X plus.o X'], quad "for" X, X' in cal(P)(R). $
  For each $M in cal(P)(R)$, put
  $ psi[M] = (r(M), op("St")(M)) in ZZ plus.o op("Cl")(R). $
  Then $psi$ gives a well defined homomorphism
  $psi: K_0 lr((R)) -> ZZ plus.o op("Cl")(R)$, since for $M, M' in cal(P)(R)$,
  we have
  $
    r(M plus.o M') = r(M) + r(M'),
    quad op("St")(M plus.o M') = op("St")(M) dot op("St")(M').
  $
  It is easily verified that $psi$ is the desired isomorphism. (If the quotient
  field of $R$ is a global field, the result is a special case of Theorem
  @th:dedekind-order-projective-grothendieck below.)
]

The computation of $K_1 lr((R))$ lies considerably deeper, and we begin by
defining a homomorphism
$ det: K_1 lr((R)) -> R^dot, $
where $R^dot$ is the group of units of $R$. Consider an ordered pair $(M, mu)$,
where $M in cal(P)(R)$ is as in @eq:dedekind-projective-ideal-sum, and where
$mu in Aut_R M$. Let $F$ be the quotient field of $R$, so $F times.o_R M$ is an
$r$-dimensional vector space over $F$, where $r$ is the rank of $M$. The
automorphism $mu$ of $M$ defines an invertible linear transformation
$1 times.o mu$ on $F times.o_R M$, and we now set
$ det(M, mu) = det(1 times.o mu). $
In order to verify that $det$ is well defined on $K_1 lr((R))$, we must show
that
$
  det(M, mu mu') = det(M, mu) dot det(M, mu')
  quad "for" mu, mu' in Aut M,
$
and also that
$ det(M, mu) = det(L, lambda) det(N, nu), $
using the notation in @eq:determinantal-exact-relation and
@eq:determinantal-composition-relation. Both of these verifications are
straightforward, and are left to the reader.

#source(47)
We now define a homomorphism
$ theta: R^dot -> K_1 lr((R)), quad "by" u -> [R, u_r], quad u in R^dot, $
where $u_r$ denotes right multiplication by $u$ on $R$. Clearly,
$ det[R, u_r] = u, $
so the map $theta$ splits the surjection $det: K_1 lr((R)) -> R^dot$. Therefore
$ K_1 lr((R)) tilde.equiv R^dot times S K_1 lr((R)), $
<eq:dedekind-whitehead-splitting>
where $S K_1 lr((R)) = ker det$.#idx("SK₁") The notation $S K_1$ is suggested by
analogy with the notation $SL$ for the special linear group.

As we shall see in @eq:commutative-whitehead-splitting, this same decomposition
@eq:dedekind-whitehead-splitting holds for every commutative ring $R$. The
computation of $S K_1 lr((R))$ is often difficult, however. We now state without
proof the following basic theorem:

#theorem(name: "Bass–Milnor–Serre Theorem")[
  Let $R$ be a Dedekind domain whose quotient field $F$ is any global field.
  Then $S K_1 lr((R)) = 1$, and there is an isomorphism
  $ det: K_1 lr((R)) tilde.equiv R^dot. $
] <th:bass-milnor-serre>
#idx("Bass-Milnor-Serre Theorem", target: [@th:bass-milnor-serre])

For a proof, see Bass–Milnor–Serre @bib:Bass1967 or Milnor @bib:Milnor1971.
