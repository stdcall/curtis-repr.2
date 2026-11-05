#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/39-localization.typ": *

== Grothendieck Groups of Integral Group Rings
<sec:grothendieck-integral-group-rings>

Throughout this section, let $Lambda = R G$, $A = K G$, where $G$ is a finite
group of order $n$, and $R$ is a Dedekind domain with quotient field $K$. We
shall determine the additive structure of the Grothendieck group
$G_0 lr((Lambda))$ explicitly (see Definition
@i:def:ring-grothendieck-projective-groups). We begin by listing the key ideas
underlying this computation.

#statement(none, "rem")[
  A _hyper-elementary group_#idx("Hyper-elementary group") is a semidirect
  product $C times.r H$ of a cyclic $p'$-group $C$ and a $p$-group $H$, for some
  prime $p$. Let $cal(H)$ be the set of all hyper-elementary subgroups of a
  given group $G$. Solomon’s Induction Theorem
  @i:th:solomon-permutation-induction gives#footnote[See also the Witt–Berman
    Induction Theorem @i:th:witt-berman-induction.]
  $ G_0 lr((QQ G)) = sum_(H in cal(H)) op("ind")_H^G G_0 lr((QQ H)). $
] <rem:rational-hyperelementary-induction>

#statement(none, "rem")[
  The Grothendieck group $G_0^R lr((Lambda))$, associated with the category of
  left $Lambda$-lattices, is a commutative ring with identity. Multiplication is
  defined by
  $ [M][N] = [M times.o_R N] quad "for" Lambda "-lattice" M "and" N, $
  where $M times.o_R N$ is the inner tensor product of $M$ and $N$. Since in
  this case $R$ is a commutative regular ring, then by
  @th:regular-grothendieck-k0 there is an additive isomorphism
  $ G_0^R lr((Lambda)) tilde.equiv G_0 lr((Lambda)). $
] <rem:integral-grothendieck-ring>
#idx("Grothendieck ring", target: [@rem:integral-grothendieck-ring])

#statement(none, "rem")[
  Let $overline(R) = R slash P$, where $P$ is a maximal ideal of $R$. By
  @i:prop:lattice-reduction-composition-factors, there is a commutative diagram
  #decomposition-triangle
  in which $phi$ and $gamma$ are ring homomorphisms defined by change of ground
  ring, while $gamma'$ is the ring homomorphism given by the decomposition map.
] <rem:integral-decomposition-triangle>

#source(61)
#statement(none, "rem")[
  There is an exact sequence of groups (see
  @th:grothendieck-localization-sequence and
  @eq:torsion-grothendieck-prime-decomposition)
  $
    product.co_P G_0 lr((Lambda slash P Lambda))
    arrow.r^psi G_0^R lr((Lambda)) arrow.r^phi G_0 lr((A)) -> 0,
  $
  where $P$ ranges over all nonzero maximal ideals of $R$. If
  $char K divides.not n$, this sequence extends on the left by
  $K_1 lr((A)) arrow.r^delta product.co_P G_0 lr((Lambda slash P Lambda))$, by
  @th:heller-reiner-localization.#ed-note[
    For $R = FF_(p)[t]_(t)$ and $G = C_p$, put
    $Lambda = R[epsilon] slash (epsilon^p)$ and
    $A = K[epsilon] slash (epsilon^p)$. Then $G_0^t lr((Lambda)) = ZZ[k]$, where
    $k = FF_p$, and $psi[k] = 0$. But $im delta = p ZZ[k]$: the determinant over
    $K$ of an $A$-automorphism is the $p$-th power of its determinant modulo
    $epsilon$. Thus the left extension need not be exact when
    $char K divides n$.
  ]
] <rem:integral-grothendieck-localization>
#idx("Localization sequence", target: [@rem:integral-grothendieck-localization])

#statement(none, "rem")[
  Assume that $char K = 0$, and that each rational prime divisor of $n$ is a
  nonunit in $R$. Then by Swan’s Theorem
  @i:th:swan-projective-group-lattices-locally-free, for each projective
  $Lambda$-lattice $M$, we have
  $
    K M tilde.equiv A^((r)), quad M_P tilde.equiv Lambda_P^((r)),
    quad M slash P M tilde.equiv ((R slash P) G)^((r))
  $
  for some $r$. Here, $P$ can be any maximal ideal of $R$, and the subscript $P$
  indicates localization at $P$.
] <rem:swan-projective-local-freeness>

These facts will be used in §@ss:grothendieck-localization, together with the
techniques of Frobenius functors (see §@ss:grothendieck-frobenius), to obtain
Swan’s refinement of the localization sequence
@rem:integral-grothendieck-localization. The key step is the proof that $phi$ is
an isomorphism whenever $R$ is semilocal (that is, $R$ has finitely many maximal
ideals). Another interesting point in §@ss:grothendieck-localization is the
introduction of the locally free class group $op("Cl") Lambda$ (see
@def:locally-free-class-group), which is used to study the kernel of the map
$phi$ in @rem:integral-grothendieck-localization.

In §@ss:grothendieck-explicit, we shall prove the Heller–Reiner formula for the
additive structure of $G_0 lr((Lambda))$. We shall then apply this formula to
the case of cyclic and abelian groups, to obtain some results of Lenstra
@bib:Lenstra1981.

=== Localization Sequences <ss:grothendieck-localization>

As in the preceding introduction, let $G$ be a finite group, and let
$Lambda = R G$, $A = K G$, where $R$ is a Dedekind domain with quotient field
$K$. Let $H$ be a subgroup of $G$, and denote by $op("res")_H^G$,
$op("ind")_H^G$ the restriction and induction maps defined in
§@ss:grothendieck-frobenius:
$
  op("res")_H^G & : G_0 lr((R G)) -> G_0 lr((R H)),
                  quad G_0^R lr((R G)) -> G_0^R lr((R H)), \
  op("ind")_H^G & : G_0 lr((R H)) -> G_0 lr((R G)),
                  quad G_0^R lr((R H)) -> G_0^R lr((R G)).
$
Note that $G_0^R lr((R G))$ is a commutative ring with identity element $[R]$,
where $G$ acts trivially on $R$. The map $G_0^R lr((R G)) -> G_0 lr((R G))$
identifies the ring $G_0^R lr((R G))$ with the additive group $G_0 lr((R G))$.
If $cal(X)$ is some ideal of $G_0^R lr((R G))$, and $m in ZZ$, we write
$m in cal(X)$ to indicate that $m dot [R] in cal(X)$. Equivalently, this means
that $m$ annihilates the additive group $G_0^R lr((R G)) slash cal(X)$.

We shall be using properties of the Frobenius functor $G_0^R$ established in
§@ss:grothendieck-frobenius. Given any homomorphism $R -> S$, where $S$ is a
commutative ring, there is a “change of ground ring” map
$ G_0^R lr((R G)) -> G_0^S lr((S G)), $
which commutes with restriction and induction maps, and is a ring homomorphism.

#source(62)
Letting $cal(C)$ denote some collection of subgroups of $G$, we have defined
$ G_0 lr((R G))_cal(C) = sum_(H in cal(C)) op("ind")_H^G G_0 lr((R H)). $
We are now ready to prove

#lemma(title: [Swan @bib:Swan1960])[
  Let $cal(C)$ be any collection of subgroups of $G$, and let $m$ be a positive
  integer such that $m in G_0 lr((K G))_cal(C)$. Then
  $ m^2 in G_0 lr((R G))_cal(C), quad m in G_0 lr(((R slash P) G))_cal(C), $
  for each maximal ideal $P$ of $R$.
] <lem:swan-induction-annihilators>
#proof[
  Let $overline(R) = R slash P$, where $P$ is a maximal ideal of $R$. Let
  $gamma$ and $gamma'$ be the maps occurring in
  @rem:integral-decomposition-triangle. Since induction commutes with change of
  ground ring, we have
  $
    gamma lr({G_0 lr((R G))_cal(C)}) subset.eq
    G_0 lr((overline(R) G))_cal(C), \
    gamma' lr({G_0 lr((K G))_cal(C)}) subset.eq
    G_0 lr((overline(R) G))_cal(C).
  $
  Since $gamma'$ is a ring homomorphism, it follows that
  $m in G_0 lr((overline(R) G))_cal(C)$, as desired.

  Next, the map $phi: G_0^R lr((R G))_cal(C) -> G_0 lr((K G))_cal(C)$ is
  surjective, since the corresponding map $G_0^R lr((R H)) -> G_0 lr((K H))$ is
  surjective for each $H in cal(C)$. We may therefore choose
  $x in G_0^R lr((R G))_cal(C)$ with $phi(x) = m$. Then $phi(x - m) = 0$, so by
  @rem:integral-grothendieck-localization,
  $
    x - m = psi(y) quad "for some" y in
    product.co_P G_0 lr((Lambda slash P Lambda)).
  $
  But $m y in product.co G_0 lr((Lambda slash P Lambda))_cal(C)$ by
  @def:frobenius-functor(iv) and the first part of this proof, since
  $Lambda slash P Lambda = (R slash P) G$. Therefore
  $ m x - m^2 = psi(m y) in G_0^R lr((R G))_cal(C). $
  Since $m x$ lies in $G_0^R lr((R G))_cal(C)$, so does $m^2$, and we are done.
]

We apply this to obtain:

#theorem(title: [Swan @bib:Swan1960])[
  Letting $cal(H)$ denote the set of all hyper-elementary subgroups of $G$, we
  have
  $
    G_0^R lr((R G)) = G_0^R lr((R G))_cal(H)
    = sum_(H in cal(H)) op("ind")_H^G G_0^R lr((R H)).
  $ <eq:swan-hyperelementary-induction>
] <th:swan-hyperelementary-induction>
#proof[
  Since $1 in G_0 lr((QQ G))_cal(H)$ by @rem:rational-hyperelementary-induction,
  we have by
  @lem:swan-induction-annihilators
  $
    1 in G_0^ZZ lr((ZZ G))_cal(H), quad 1 in G_0 lr(((ZZ slash p ZZ) G))_cal(H)
  $
  for each rational prime $p$.
  #source(63)
  If $char R = 0$, the ring homomorphism $ZZ -> R$ induces a homomorphism
  $G_0^ZZ lr((ZZ G))_cal(H) -> G_0^R lr((R G))_cal(H)$, so the latter group
  contains 1. If $char R = p > 0$, there is a ring homomorphism
  $ZZ slash p ZZ -> R$, and so $1 in G_0^R lr((R G))_cal(H)$ once more. Now use
  @prop:frobenius-family-ideals(i) to finish the proof.
]

The above theorem, which depends on the Solomon Induction Theorem and the theory
of Frobenius functors, will be vital for our later discussion. It will permit us
to prove various identities by reducing the problem to the case of
hyper-elementary groups. As a first step in this direction, we prove

#corollary[
  Suppose that for each hyper-elementary subgroup $H$ of $G$, the change of
  ground ring map
  $ phi_H: G_0^R lr((R H)) -> G_0 lr((K H)) $
  is an isomorphism. Then we have an isomorphism
  $ phi_G: G_0^R lr((R G)) tilde.equiv G_0 lr((K G)). $
] <cor:grothendieck-hyperelementary-reduction>
#proof[
  By @rem:integral-grothendieck-localization, $phi_G$ is surjective. To prove
  $phi_G$ injective, let $phi_G lr((x)) = 0$. Since $op("res")_H^G$ commutes
  with the change of ground ring map $phi_G$, and since $phi_H$ is injective for
  each $H in cal(H)$, it follows that $op("res")_H^G lr((x)) = 0$ for each
  $H in cal(H)$. But then @prop:frobenius-family-ideals shows that $x = 0$, as
  desired.
]

A Dedekind domain $R$ is called _semilocal_ if $R$ has only finitely many
maximal ideals.#idx("Semilocal ring") (For example, the localization $R_P$ of
$R$ at a maximal ideal $P$ is a local ring, and is thus automatically semilocal
as well.) We are now ready to prove the following remarkable theorem due to Swan
@bib:Swan1963, which will be the key to the global situation:

#theorem[
  For each semilocal Dedekind domain $R$, the change of ground ring map gives an
  isomorphism of rings
  $ phi: G_0^R lr((R G)) tilde.equiv G_0 lr((K G)). $
] <th:semilocal-grothendieck-isomorphism>
#idx("Swan's Theorem", target: [@th:semilocal-grothendieck-isomorphism])
#proof[
  We need only show that $phi$ is injective, since we already know that $phi$ is
  surjective by @rem:integral-grothendieck-localization. It suffices by
  @rem:integral-grothendieck-localization to show that
  $psi(G_0 lr(((R slash P) G))) = 0$ for each nonzero maximal ideal $P$ of $R$.
  To avoid trivialities, assume $R != K$.

  Suppose first that $P divides.not n$, where $n = |G|$. Then
  $char K divides.not n$, so $K G$ is a separable $K$-algebra by Maschke’s
  Theorem. Let $X$ be any f.g. $(Lambda slash P Lambda)$-module. Then there
  exists a $Lambda$-exact sequence
  $ 0 -> M -> N -> X -> 0 $
  in which $M$ and $N$ are $Lambda$-lattices, and so $psi[X] = [N] - [M]$.
  #source(64)
  Since $op("ann")_R X = P$, we have $X_Q = 0$ for each maximal ideal $Q$ of $R$
  distinct from $P$. Therefore $M_Q tilde.equiv N_Q$ for $Q$ dividing $n$, so
  $M$ and $N$ are in the same genus by @i:prop:genus-nonmaximal-primes. But then
  $M_Q tilde.equiv N_Q$ for every maximal ideal $Q$ of $R$, and therefore by
  @i:prop:genus-semilocal-isomorphism $M tilde.equiv N$ since $R$ is semilocal.
  Thus $psi[X] = 0$ as desired.

  For the remainder of the proof, suppose that $P divides n$, and set
  $overline(R) = R slash P$. We must show that
  $psi(G_0 lr((overline(R) G))) = 0$, or equivalently, that $psi[M] = 0$ for
  each simple $overline(R) G$-module $M$. It suffices to treat the case where
  $G$ acts faithfully on $M$; for let
  $ H = {x in G: x m = m "for all" m in M}, quad tilde(G) = G slash H, $
  and view $M$ as an $overline(R) tilde(G)$-module. There is a commutative
  diagram
  #quotient-square
  where the vertical arrows come from viewing each $tilde(G)$-module as
  $G$-module. Now $tilde(G)$ acts faithfully on $M$, and if $tilde(psi)[M] = 0$,
  then also $psi[M] = 0$.

  It thus suffices to prove that $psi[M] = 0$ when $M$ is a simple
  $overline(R) G$-module on which $G$ acts faithfully. Further, we need only
  treat the case where $G$ is hyper-elementary, by
  @cor:grothendieck-hyperelementary-reduction. So now let $G = C times.r H$,
  where $C = chevron.l x chevron.r$ is cyclic of order $c$ with $(p, c) = 1$,
  and $H$ is a $p$-group. If $P divides c$, then $char overline(R) = q$ for some
  rational prime $q$ dividing $c$. The Sylow $q$-subgroup of $C$ is then normal
  in $G$, and acts trivially on $M$ by @i:prop:normal-p-subgroup-brauer-kernel,
  contradicting the assumption that $G$ acts faithfully on $M$.

  We are thus left with the case where $char overline(R) = p$, and where (as
  above) $G$ contains no nontrivial normal $p$-subgroup. Suppose first that
  $overline(R)$ contains $omega$, a primitive $c$-th root of 1. We shall show
  that $M$ is $overline(R) G$-projective. By Exercise
  @i:exc:cyclic-prime-to-p-unramified-decomposition, every simple
  $overline(R) C$-module is one-dimensional over $overline(R)$. Let $V$ be a
  simple $overline(R) C$-submodule of $M$. We have $sum y V subset.eq M$, where
  $y$ ranges over all elements of $H$, and the sum is an
  $overline(R) G$-submodule of $M$. Therefore $M = sum y V$, and we now show
  that the sum is direct, that is, $M tilde.equiv V^G$. We need only show that
  the $G$-conjugates $lr({y V})$ of $V$ are mutually nonisomorphic
  $overline(R) C$-modules. Since $M$ is $G$-faithful, it is easily seen that $V$
  is faithful as $C$-module.

  Now let $y V tilde.equiv V$ as $overline(R) C$-modules, where $y in H$. Since
  $C$ acts faithfully on $V$, this implies that $x = y^(-1) x y$. Put
  $ H_1 = {y in H: x = y^(-1) x y}, $
  the centralizer of $C$ in $H$. For each $t in G$, we have
  $C = chevron.l x^t chevron.r$, so for each $y in H_1$ it follows that $y^t$
  commutes with $x$. Write $y^t = z h$, $z in C$, $h in H$; then $h$ centralizes
  $C$, and commutes with $z$. Since $y^t$ has $p$-power order, it follows that
  $z = 1$ and $y^t = h$, so $y^t in H_1$. Therefore $H_1$ is a normal
  $p$-subgroup of $G$, and hence $H_1 = 1$.

  #source(65)
  This completes the proof that $M tilde.equiv V^G$. Since $V$ is a direct
  summand of $overline(R) C$, $M$ is a direct summand of $overline(R) G$, and is
  therefore projective.

  We reached the above conclusion under the simplifying assumption that
  $omega in overline(R)$. Dropping this hypothesis, put $E = overline(R)(omega)$
  and form the $E G$-module $L = E times.o_(overline(R)) M$. We have
  $ L tilde.equiv M^(dim_(overline(R)) E) quad "as" overline(R) G "-modules". $
  Now let $lr({M_i})$ be the set of composition factors of the $E G$-module $L$.
  Then each $overline(R) G$-composition factor of $M_i|_(overline(R) G)$ is
  isomorphic to $M$, so $M_i$ is a $G$-faithful simple $E G$-module (for each
  $i$), and thus $M_i$ is $E G$-projective by the preceding argument.

  Next, if $M_j$ is a simple factor module of $L$, the surjection $L -> M_j$
  must split since $M_j$ is projective. Repeating this argument, it follows that
  $L tilde.equiv product.co_i M_i$, so $L$ is $E G$-projective. Restricting the
  operator domain to $overline(R) G$, it follows that $M$ is
  $overline(R) G$-projective, as claimed.#footnote[If $R$ is a complete d.v.r.
    with maximal ideal $frak(p)$, the above shows that
    $M tilde.equiv M_0 slash frak(p) M_0$ for some projective $R G$-lattice
    $M_0$. This gives another proof of the main step in establishing
    @i:th:projective-character-map-split-injection.]

  We have now shown that every $G$-faithful simple $overline(R) G$-module $M$
  must be $overline(R) G$-projective, whether or not $omega in overline(R)$.
  Since $M$ is simple, it is a homomorphic image of $overline(R) G$, so
  $overline(R) G tilde.equiv M plus.o N$ for some $overline(R) G$-module $N$.
  Now choose $Lambda$-exact sequences
  $ 0 -> X -> Lambda -> M -> 0, quad 0 -> Y -> Lambda -> N -> 0. $
  We obtain a pair of $Lambda$-exact sequences
  $
    0 -> X plus.o Y -> Lambda^((2)) -> M plus.o N -> 0,
    quad 0 -> Lambda arrow.r^pi Lambda -> overline(R) G -> 0,
  $
  where the arrow $pi$ is multiplication by the prime element $pi$ of $P$.
  Schanuel’s Lemma then shows that $X$ is $Lambda$-projective. Further,
  $K X tilde.equiv K G$ since $M$ is an $R$-torsion module. By
  @i:th:local-projective-group-lattice-cancellation, applied over each $R_P$, we
  have $X_P tilde.equiv Lambda_P$. Thus $X$ lies in the genus of $Lambda$, so
  $X tilde.equiv Lambda$ because $R$ is semilocal. Therefore
  $psi[M] = [Lambda] - [X] = 0$, which completes the proof of Theorem
  @th:semilocal-grothendieck-isomorphism.
]

We are now ready to derive a number of important corollaries, and begin by
strengthening the localization sequence for the integral group ring case:

#theorem(title: [Swan @bib:Swan1963])[
  Let $R$ be an arbitrary Dedekind domain, and let $Omega$ be any finite set of
  maximal ideals of $R$. Then there is an exact sequence of groups
  $
    product.co_(P in.not Omega) G_0 lr(((R slash P) G))
    arrow.r^psi G_0^R lr((R G)) arrow.r^phi G_0 lr((K G)) -> 0,
  $
  where the sum extends over all nonzero maximal ideals of $R$ such that
  $P in.not Omega$.
] <th:swan-localization-omit-finite-primes>
#idx("Swan's Theorem", target: [@th:swan-localization-omit-finite-primes])
#proof[
  Let $Omega = {P_1, dots, P_m}$, and let $S$ be the multiplicative set
  $ S = R - {P_1 union dots union P_m}. $
  #source(66)
  If $R' = S^(-1) R$, then $R'$ is a semilocal Dedekind domain whose maximal
  ideals are $lr({P_i R': 1 <= i <= m})$ (see §@i:ss:localization). By
  @th:semilocal-grothendieck-isomorphism, there is an isomorphism
  $ phi': G_0^(R') lr((R' G)) tilde.equiv G_0 lr((K G)). $
  On the other hand, @th:grothendieck-localization-sequence gives the exact
  sequence
  $
    product.co_P G_0 lr(((R slash P) G)) arrow.r^psi G_0^R lr((R G))
    -> G_0^(R') lr((R' G)) tilde.equiv G_0 lr((K G)),
  $
  where $P$ ranges over all prime ideals of $R$ such that
  $P inter S != emptyset$. Thus $P$ ranges over the nonzero maximal ideals of
  $R$ outside of $Omega$, and the proof is complete.
]

If $R = K$, then of course the sum $product.co_P$ is vacuous. If $R != K$, the
result says that in the exact sequence @th:grothendieck-localization-sequence,
we may omit any preassigned finite set of summands from the first term.

We have already remarked in @eq:order-grothendieck-splitting that the additive
group $G_0 lr((K G))$ is $ZZ$-free, and so
$ G_0^R lr((R G)) tilde.equiv G_0 lr((K G)) plus.o ker phi. $
We intend to show that $ker phi$ is a finite group whenever $K$ is a global
field such that $char K divides.not n$. In addition to the basic Theorem
@th:swan-localization-omit-finite-primes, we shall need the locally free class
group $op("Cl") R G$, which we now define for arbitrary orders.

#definition[
  Let $R$ be a Dedekind domain with quotient field $K$, and let $Lambda$ be an
  arbitrary order in a f.d. $K$-algebra $A$. For each maximal ideal $P$ of $R$,
  let $Lambda_P$ be the localization of $Lambda$ at $P$, and let
  $K_0 lr((Lambda)) -> K_0 lr((Lambda_P))$ be the map induced by ground ring
  extension. The _locally free class group_ $op("Cl") Lambda$ is the kernel of
  the homomorphism
  $ K_0 lr((Lambda)) -> product_P K_0 lr((Lambda_P)), $
  where $P$ ranges over all maximal ideals of $R$.
] <def:locally-free-class-group>
#nidx(
  "$op(\"Cl\") Lambda$",
  "locally free class group",
  target: [@def:locally-free-class-group],
  chapter: [@ch:class-groups],
)
#idx("Locally free class group", target: [@def:locally-free-class-group])
#idx("Class group", target: [@def:locally-free-class-group])

Each $x in K_0 lr((Lambda))$ is of the form $x = [F] - [X]$ with $F$
$Lambda$-free and $X in cal(P)(Lambda)$. Then $x in op("Cl") Lambda$ if and only
if $[F_P] = [X_P]$ for all $P$, or equivalently, if and only if $F_P$ is stably
isomorphic to $X_P$. By Exercise @exc:local-order-module-cancellation, this
occurs if and only if $F_P tilde.equiv X_P$ for all $P$, that is, $X$ and $F$
lie in the same genus. If $F tilde.equiv Lambda^((k))$, then by
@i:cor:genus-multiple-decomposition we have
$X tilde.equiv Lambda^((k-1)) plus.o M$ for some left ideal $M$ in the genus of
$Lambda$. Therefore #equation-suffix(base: [@def:locally-free-class-group])[$
  op("Cl") Lambda = {[Lambda] - [M] in K_0 lr((Lambda)):
    M = "locally free left ideal of" Lambda}.
$] <eq:locally-free-ideal-representatives>

#source(67)
If $K$ is a global field and $A$ is a semisimple $K$-algebra, the
Jordan–Zassenhaus Theorem shows that there are only finitely many isomorphism
classes of left ideals of $Lambda$. Therefore we have:

#proposition[
  For any order $Lambda$ in a semisimple f.d. $K$-algebra, with $K$ a global
  field, the locally free class group $op("Cl") Lambda$ is finite.
] <prop:locally-free-class-group-finite>

In Chapter @ch:class-groups, we shall investigate $op("Cl") Lambda$ in more
detail. Here, we use it to finish our discussion of the map
$phi: G_0^R lr((R G)) -> G_0 lr((K G))$.

#theorem[
  Let $Lambda = R G$, $A = K G$, where $G$ is a finite group of order $n$, and
  $K$ is a global field for which $char K divides.not n$. Then there is an exact
  sequence of groups
  $
    op("Cl") Lambda arrow.r^mu G_0^R lr((Lambda)) arrow.r^phi G_0 lr((A)) -> 0,
  $
  where $mu$ is defined by viewing each $X in cal(P)(Lambda)$ as
  $Lambda$-lattice. Thus
  $ G_0^R lr((Lambda)) tilde.equiv G_0 lr((A)) plus.o ker phi, $
  and $ker phi$ is a finite abelian group.
] <th:integral-grothendieck-finite-kernel>
#proof[
  Clearly $phi mu = 0$. Now let $Omega$ be the finite set of maximal ideals of
  $R$ which divide $n$. By @th:swan-localization-omit-finite-primes, to prove
  that $ker phi = im mu$, it suffices to show that
  $ psi lr({G_0 lr(((R slash P) G))}) subset.eq im mu $
  for each $P in.not Omega$.

  Let $M$ be any f.g. $(R slash P) G$-module, and choose a $Lambda$-exact
  sequence
  $ 0 -> X -> F -> M -> 0, $
  with $F$ $Lambda$-free. Then $M_Q = 0$ for each maximal ideal $Q$ of $R$
  containing $n$, so $X_Q = F_Q$ for each such $Q$. But then $X$ lies in the
  genus of $F$ by @i:prop:genus-nonmaximal-primes, and thus
  $[F] - [X] in op("Cl") Lambda$. This gives $psi[M] = [F] - [X] in im mu$, as
  desired. The remaining assertions in the theorem are then obvious. The fact
  that $K$ is a global field is used only to insure that $op("Cl") Lambda$ is
  finite.
]

Our next step in the computation of $G_0 lr((Lambda))$ is the comparison of the
localization sequences of $Lambda$ and $Lambda'$, where $Lambda'$ is a maximal
order in $A$ containing $Lambda$. As shown by Swan @bib:Swan1963, we have

#theorem[
  Let $G$ be a finite group of order $n$, and $R$ a Dedekind domain with
  quotient field $K$ such that $char K divides.not n$. Let $Lambda = R G$,
  $A = K G$, and let $Lambda'$ be a maximal order in $A$ containing $Lambda$.
  Then there is a commutative diagram of groups, with exact rows:
  #class-group-comparison
  where $rho$ is the map defined by $Lambda' times.o_Lambda ast$, and $alpha$ is
  defined by restriction of operators from $Lambda'$ to $Lambda$. Further, both
  $rho$ and $alpha$ are surjective.
] <th:maximal-overorder-grothendieck-surjections>
#proof[
  By @i:th:order-contained-in-maximal-order, the order $Lambda$ may be embedded
  in a maximal order $Lambda'$. Each $Lambda'$-lattice is $Lambda'$-projective
  by @i:th:maximal-orders-are-hereditary, so
  $G_0^R lr((Lambda')) = K_0 lr((Lambda'))$. Let $x = [F] - [X] in ker phi'$,
  where $F$ is $Lambda'$-free and $X$ is a $Lambda'$-lattice. Since
  $phi'(x) = 0$, we have $[K F] = [K X]$ in $G_0 lr((A))$, and thus
  $K F tilde.equiv K X$. By the local structure of maximal orders in
  @i:th:dvr-maximal-orders-completion-lattices, their completed lattices are
  isomorphic at each maximal ideal $P$. By
  @i:prop:module-isomorphism-completion, $F_P tilde.equiv X_P$ for every $P$.
  Thus $F$ and $X$ are in the same genus, so $x in op("Cl") Lambda'$. This shows
  that the bottom row of the above diagram is exact.

  #source(68)
  The right-hand square is clearly commutative. For the left-hand square, let
  $xi in op("Cl") Lambda$, and write $xi = [Lambda] - [M]$ with $M$ a left ideal
  of $Lambda$ in the genus of $Lambda$. By Exercise
  @i:exc:genus-overorder-tensor-exchange, we have
  $
    [Lambda] - [M] = [Lambda'] - [Lambda' times.o_Lambda M]
    quad "in" G_0 lr((Lambda)).
  $
  Therefore $mu(xi) = (alpha mu' rho)(xi)$ in $G_0 lr((Lambda))$. Since
  $G_0 lr((Lambda)) tilde.equiv G_0^R lr((Lambda))$, it follows that
  $mu = alpha mu' rho$, as desired.

  To show that $rho$ is surjective, let
  $x' = [Lambda'] - [X] in op("Cl") Lambda'$, where $X$ is a left ideal in
  $Lambda'$. Let $P$ range over all maximal ideals of $R$; for each $P$ we have
  $X_P tilde.equiv Lambda'_P$, so $X_P = Lambda'_P beta_P$ for some
  $beta_P in A^dot$, with $beta_P = 1$ a.e. Set
  $ M = A inter lr({inter.big_P Lambda_P beta_P}), $
  and then $M$ is a full left $Lambda$-lattice in $A$ for which
  $M_P = Lambda_P beta_P$ for all $P$. Thus $M$ lies in the genus of $Lambda$,
  and $x = [Lambda] - [M] in op("Cl") Lambda$. In order to prove that
  $rho(x) = x'$, we need only show that
  $Lambda' times.o_Lambda M tilde.equiv X$. But for each $P$,
  $
    (Lambda' times.o_Lambda M)_P = Lambda'_P times.o_(Lambda_P) M_P
    tilde.equiv Lambda'_P beta_P = X_P,
  $
  so the map $Lambda' times.o_Lambda M -> Lambda' M subset.eq A$ is the desired
  isomorphism. Thus $rho$ is surjective.

  Finally, $alpha$ is surjective by “diagram-chasing”: let
  $x in G_0^R lr((Lambda))$, and choose $y in G_0^R lr((Lambda'))$ with
  $phi'(y) = phi(x)$. Then $phi(x - alpha y) = 0$, so $x - alpha y = mu z$ for
  some $z in op("Cl") Lambda$. Therefore
  $ x = alpha y + mu z = alpha y + alpha mu' rho z in im alpha. $
  Thus $alpha$ is surjective, and the theorem is proved.
]

At the end of §@ss:grothendieck-explicit we shall show by example that the map
$alpha$ in @th:maximal-overorder-grothendieck-surjections need not be an
isomorphism. Further (see @eq:class-group-kernel-sequence and
§@sec:class-groups-integral-group-rings) $op("Cl") Lambda$ is usually larger
than $op("Cl") Lambda'$, so the maps $rho$ and $mu$ need not be injective.

#source(69)
We conclude this subsection with a brief discussion of the ring structure of
$G_0^R lr((Lambda))$. The main result, due to Swan @bib:Swan1963, is as follows:

#theorem[
  Assume that $char K divides.not n$, and let
  $phi: G_0^R lr((Lambda)) -> G_0 lr((A))$ as in
  @th:integral-grothendieck-finite-kernel. Then $ker phi$ is an ideal of
  $G_0^R lr((Lambda))$ such that $(ker phi)^2 = 0$. Furthermore,
  $ ker phi = {x in G_0^R lr((Lambda)): x^2 = 0}. $
] <th:integral-grothendieck-square-zero-kernel>
#idx("Swan's Theorem", target: [@th:integral-grothendieck-square-zero-kernel])
#proof[
  If $x in G_0^R lr((Lambda))$ is such that $x^2 = 0$, then $(phi(x))^2 = 0$ in
  $G_0 lr((A))$. But $G_0 lr((A))$ has no nonzero nilpotent elements by Exercise
  @i:exc:grothendieck-group-ring-reduced, so $x in ker phi$. We show next that
  for $x, y in ker phi$, we have $x y = 0$. Write
  $ x = [Lambda] - [L], quad y = [Lambda] - [M], $
  where $L, M$ are locally free left ideals of $Lambda$. By definition of
  multiplication,
  $
    x y = [Lambda times.o Lambda] - [L times.o Lambda]
    - [Lambda times.o M] + [L times.o M],
  $
  where $times.o$ means inner tensor product over $R$. There is a $Lambda$-exact
  sequence $0 -> L -> Lambda -> T -> 0$, with $T$ an $R$-torsion
  $Lambda$-module. Since both $M$ and $Lambda$ are $R$-flat, we obtain
  $Lambda$-exact sequences
  $
    0 -> L times.o M -> Lambda times.o M -> T times.o M -> 0,
    quad 0 -> L times.o Lambda -> Lambda times.o Lambda
    -> Lambda times.o T -> 0.
  $
  For each maximal ideal $P$ in the finite $R$-support of $T$, choose a
  $Lambda_P$-isomorphism $M_P tilde.equiv Lambda_P$. Tensoring with $T_P$ gives
  $(T times.o M)_P tilde.equiv T_P times.o M_P tilde.equiv T_P times.o Lambda_P
  tilde.equiv (T times.o Lambda)_P$. Decomposing the torsion modules into their
  $P$-primary components and taking the direct sum of these isomorphisms gives
  $T times.o M tilde.equiv T times.o Lambda$.#ed-note[
    This is an abstract isomorphism, not necessarily the map induced by
    $M subset.eq Lambda$. For $G = 1$, $Lambda = ZZ$, $M = p ZZ$ and
    $T = ZZ slash p ZZ$, that induced map is zero between two nonzero modules.
  ] We now have $T times.o M tilde.equiv T times.o Lambda
  tilde.equiv Lambda times.o T$, and both $Lambda times.o M$ and
  $Lambda times.o Lambda$ are $Lambda$-projective (by Exercise
  @i:exc:regular-inner-tensor-projective), so applying Schanuel’s Lemma we
  obtain
  $
    (L times.o M) plus.o (Lambda times.o Lambda)
    tilde.equiv (L times.o Lambda) plus.o (Lambda times.o M).
  $
  Thus $x y = 0$, and the theorem is proved.
]

In the cases where the ring structure of $G_0^R lr((Lambda))$ has been worked
out, one begins by finding a ring homomorphism
$sigma: G_0 lr((A)) -> G_0^R lr((Lambda))$ for which $phi sigma = 1$. One may
then view $G_0 lr((A))$ as a subring of $G_0^R lr((Lambda))$, and the problem
reduces to calculating its action on the ideal $ker phi$. This calculation has
been performed for $Lambda = ZZ G$ when $G$ is cyclic (see Stancl
@bib:Stancl1967, Swan @bib:Swan1963), and for $G$ an elementary abelian
$p$-group (Stancl @bib:Stancl1967). For further results, see Obayashi
@bib:Obayashi1966, Uchida @bib:Uchida1967, and Matchett @bib:Matchett1976; the
work of Santa-Pietro @bib:SantaPietro1972 contains some errors, however.

One important application of Theorem
@th:integral-grothendieck-square-zero-kernel is as follows: the ring
$G_0^R lr((R G))$ acts on various abelian groups, such as $K_0 lr((R G))$ for
example. In some cases this action can be extended to an action of the ring
$G_0 lr((K G))$ on such abelian groups, by verifying that $ker phi$ acts
trivially. Thus we shall see in @prop:rational-grothendieck-projective-action
that $G_0 lr((QQ G))$ acts on $K_0 lr((ZZ G))$; see §@ss:class-group-frobenius
for other results of this nature.

#source(70)
=== Explicit Calculations <ss:grothendieck-explicit>

Here we shall derive the Heller–Reiner formula @eq:heller-reiner-formula for
$G_0^R lr((Lambda))$, where $Lambda = R G$, with $R$ a Dedekind domain whose
quotient field $K$ is an algebraic number field. As before, let $|G| = n$, and
assume $R != K$ to avoid trivialities.

Let $A = K G$, and let $Lambda'$ be a maximal $R$-order in $A$ containing
$Lambda$. By @i:th:maximal-orders-wedderburn-components we may write
$ A = plus.o.big_(i=1)^s A_i, quad Lambda' = plus.o.big_(i=1)^s Lambda_i, $
<eq:group-order-wedderburn-decomposition>
where the $lr({Lambda_i})$ are maximal $R$-orders in the Wedderburn components
$lr({A_i})$ of $A$. Let
$
  K_i = "center of" A_i, quad R_i = "integral closure of" R "in" K_i,
  quad 1 <= i <= s,
$
so $A_i$ is a central simple $K_i$-algebra, and $Lambda_i$ is a maximal
$R_i$-order in $A_i$. As in §@ss:grothendieck-localization, let
$G_0^t lr((Lambda'))$ be the Grothendieck group of the category of f.g.
$R$-torsion $Lambda'$-modules. Since such modules decompose the same way as
$Lambda'$, we have
$ G_0^t lr((Lambda')) tilde.equiv product.co_(i=1)^s G_0^t lr((Lambda_i)), $
noting that for a $Lambda_i$-module, $R$-torsion coincides with $R_i$-torsion by
Exercise @i:exc:lattices-integral-base-change. Using
@eq:torsion-grothendieck-ideal-isomorphism, we obtain an isomorphism
$ tau: G_0^t lr((Lambda')) tilde.equiv product_(i=1)^s I(R_i), $
where $I(R_i)$ is the group of $R_i$-ideals in $K_i$. Let $P_(A_i) lr((R_i))$ be
the subgroup of $I(R_i)$ defined as in
@th:dedekind-order-projective-grothendieck, and let
$delta': K_1 lr((A)) -> G_0^t lr((Lambda'))$ be the map occurring in the
localization sequence for $Lambda'$. Then
$ im tau delta' = product_(i=1)^s P_(A_i) lr((R_i)). $
Next, by @th:heller-reiner-localization there is a commutative diagram of
groups, with exact rows:
#order-localization-comparison
where $alpha$ and $beta$ come from restriction of operators from $Lambda'$ to
$Lambda$. By @th:maximal-overorder-grothendieck-surjections, $alpha$ is
surjective. An easy “diagram-chase” then shows that $beta$ is also surjective,
and that
$
  ker phi tilde.equiv op("cok") delta tilde.equiv
  G_0^t lr((Lambda')) slash (im delta' + ker beta).
$ <eq:grothendieck-kernel-overorder-quotient>

#source(71)
Since $G_0 lr((A))$ is $ZZ$-free, we have
$ G_0 lr((Lambda)) tilde.equiv G_0 lr((A)) plus.o ker phi, $
so the additive structure of $G_0 lr((Lambda))$ and $G_0^R lr((Lambda))$ is
determined by the group $ker phi$. This is a finite abelian group, by
@th:integral-grothendieck-finite-kernel.

Using the above isomorphism $tau$, we have
$
  op("cok") delta tilde.equiv lr(product_(i=1)^s I(R_i)) slash
  lr(product_(i=1)^s P_(A_i) lr((R_i))) dot tau(ker beta),
$
and it remains for us to describe $tau(ker beta)$. By
@eq:order-torsion-grothendieck-decomposition we may write
$beta = plus.o beta_P$, where
$
  beta_P: G_0 lr((Lambda' slash P Lambda')) -> G_0 lr((Lambda slash P Lambda)),
$
and where $P$ ranges over the maximal ideals of $R$. Since $beta$ is surjective,
so is each $beta_P$. If $P divides.not n$, then by @i:prop:group-ring-maximality
we have $Lambda_P = Lambda'_P$, and $beta_P$ is an isomorphism. Therefore
$
  tau(ker beta) = product_(P divides n) W_P,
  quad "where" W_P = tau(ker beta_P).
$
We now introduce additional notation, to help us describe $W_P$ explicitly. For
each maximal ideal $P$ of $R$ dividing $n$, we write
$
  P R_i = product_(j=1)^(t_i) P_(i j)^(e_(i j)),
  quad P_(i j) = "distinct prime ideals of" R_i, quad 1 <= i <= s,
$
with the $lr({e_(i j)})$ positive integers. For fixed $i$ and $j$, we have
$
  G_0 lr((Lambda_i slash P_(i j)^(e_(i j)) Lambda_i))
  tilde.equiv G_0 lr((Lambda_i slash P_(i j) Lambda_i)) tilde.equiv ZZ,
$
since the two artinian factor rings above have the same unique simple module,
hereafter denoted by $S_(i j)$ (see proof of
@th:dedekind-order-projective-grothendieck). Therefore
$
  G_0 lr((Lambda' slash P Lambda'))
  &tilde.equiv product.co_(i=1)^s G_0 lr((Lambda_i slash P Lambda_i)) \
  &tilde.equiv product.co_(i=1)^s product.co_(j=1)^(t_i)
  G_0 lr((Lambda_i slash P_(i j)^(e_(i j)) Lambda_i)) \
  &tilde.equiv product.co_(i,j) G_0 lr((Lambda_i slash P_(i j) Lambda_i))
  = product.co_(i,j) ZZ[S_(i j)].
$

#source(72)
The isomorphism $tau$ carries $[S_(i j)]$ onto its $R_i$-annihilator
$P_(i j) in I(R_i)$. Since $P subset.eq P_(i j)$, we may view $S_(i j)$ as a
$(Lambda slash P Lambda)$-module. We thus obtain
$
  W_P = tau(ker beta_P) = {product_(i,j) P_(i j)^(n_(i j)):
    sum_(i,j) n_(i j) [S_(i j)] = 0 "in" G_0 lr((Lambda slash P Lambda))}.
$ <eq:heller-reiner-prime-relations>
Combining all of this information, we obtain the formula
$
  G_0 lr((Lambda)) tilde.equiv G_0 lr((A)) plus.o
  lr((product_(i=1)^s I(R_i))) slash
  lr((product_(i=1)^s P_(A_i) lr((R_i)))) dot product_(P divides n) W_P,
$ <eq:heller-reiner-formula>
due to Heller–Reiner @bib:Heller1964, @bib:Heller1965.
#idx("Heller-Reiner Theorem", target: [@eq:heller-reiner-formula])

As our first application of this formula, we treat the case where $G$ is cyclic,
and $Lambda = ZZ G$. The result is due independently to Bass @bib:Bass1979,
Lenstra @bib:Lenstra1981, and Reiner (see Reiner–Roggenkamp @bib:Reiner1979, p.
97).

#theorem[
  Let $G$ be a cyclic group of order $n$, and let $Lambda = ZZ G$. For each $d$
  dividing $n$, let $zeta_d$ be a primitive $d$-th root of 1 over $QQ$, and set
  $ K_d = QQ(zeta_d), quad R_d = ZZ[zeta_d] = "alg. int." lr({K_d}). $
  Then
  $
    G_0 lr((Lambda)) tilde.equiv G_0 lr((A)) plus.o
    product_(d divides n) op("Cl") R_(d)[d^(-1)].
  $
] <th:cyclic-integral-grothendieck-formula>
#proof[
  The unique maximal order in $A$ is given by $Lambda' = product.co R_d$, and we
  have $A = product.co K_d$. If $G = chevron.l x chevron.r$, then $x$ acts on
  each $K_d$ and $R_d$ as multiplication by $zeta_d$. Let us calculate $W_p$,
  where $p$ is a prime divisor of $n$. Write
  $
    p R_d = product_j P_(d j)^(e_(d j)),
    quad lr({P_(d j)}) "distinct prime ideals of" R_d,
  $
  for each $d$ dividing $n$. The unique simple
  $(Lambda_d slash P_(d j) Lambda_d)$-module is just $R_d slash P_(d j)$, for
  each $j$. Thus, by @eq:heller-reiner-prime-relations,
  $
    W_p = {product_(d,j) P_(d j)^(n_(d j)):
      sum n_(d j) [R_d slash P_(d j)] = 0 "in" G_0 lr((Lambda slash p Lambda))}.
  $
  For each $d$, write $d = a p^u$, where $(p, a) = 1$. By
  @i:th:cyclotomic-prime-factorization, in the extension $K_a slash QQ$, the
  rational prime $p$ splits into distinct prime ideals $lr({P_(a j)})$ of $R_a$;
  in the extension $K_d slash K_a$, each $P_(a j)$ is completely ramified:
  $
    P_(a j) R_d = P_(d j)^(phi(p^u)),
    quad R_d slash P_(d j) tilde.equiv R_a slash P_(a j)
    quad "for each" j.
  $ <eq:cyclotomic-residue-prime-relations>
  The above isomorphism is a $(Lambda slash p Lambda)$-isomorphism, so $W_p$
  contains all products $P_(d j) P_(a j)^(-1)$, with $d, j$ varying.

  We show next that $W_p$ is generated by all such products, and for this
  purpose we compute $G_0 lr((Lambda slash p Lambda))$. Let $n = m p^k$,
  $p divides.not m$, and put $overline(ZZ) = ZZ slash p ZZ$. Then
  #source(73)
  $
    Lambda slash p Lambda tilde.equiv overline(ZZ)[x] slash (x^n - 1)
    tilde.equiv overline(ZZ)[x] slash (x^m - 1)^(p^k),
  $
  so
  $
    G_0 lr((Lambda slash p Lambda)) tilde.equiv
    G_0 lr((overline(ZZ)[x] slash (x^m - 1))).
  $
  But
  $
    overline(ZZ)[x] slash (x^m - 1)
    &tilde.equiv product.co_(a divides m)
    overline(ZZ)[x] slash (Phi_a lr((x))) \
    &tilde.equiv product.co_(a divides m) R_a slash p R_a
    tilde.equiv product.co_(a divides m) product.co_j R_a slash P_(a j).
  $
  The modules $lr({R_a slash P_(a j)})$ are nonisomorphic as
  $overline(ZZ)[x] slash (x^m - 1)$-modules, hence also as
  $(Lambda slash p Lambda)$-modules, and we have
  $ G_0 lr((Lambda slash p Lambda)) = product.co_(a,j) ZZ[R_a slash P_(a j)]. $
  It follows at once that the products $lr({P_(d j) P_(a j)^(-1)})$ generate
  $W_p$, as claimed. Note that such generators occur only when $d$ is a multiple
  of $p$.

  In formula @eq:heller-reiner-formula, the subgroup $P_(K_d) lr((R_d))$ of the
  ideal group $I(R_d)$ is just the usual subgroup of principal ideals $P(R_d)$,
  so now
  $
    ker phi tilde.equiv lr((product_(d divides n) I(R_d))) slash
    lr((product_(d divides n) P(R_d))) lr((product_(p divides n) W_p)).
  $ <eq:cyclic-grothendieck-kernel-ideals>
  To simplify this expression, let $N_(d slash e)$ denote the norm map
  $N_(K_d slash K_e)$ whenever $e divides d$. We now define an endomorphism
  $epsilon$ of the group $product_(d divides n) I(R_d)$, by setting
  $
    epsilon(X_d) = product_(e divides d, (e,d slash e)=1) N_(d slash e)
    lr((X_d)),
    quad "for" X_d in I(R_d), quad d divides n.
  $
  Since the divisors of $n$ form a partially ordered set with respect to
  divisibility, and since $epsilon(X_d) = X_d dot$ (elements of “lower” order),
  it follows that $epsilon$ is an _automorphism_ of $product I(R_d)$. Clearly
  $epsilon$ carries $product P(R_d)$ onto itself.

  We now show that #named-equation(name: [$(ast)$])[$
    product_(p divides n) epsilon(W_p) = product_(d divides n) Y_d,
  $] <eq:cyclotomic-prime-subgroups-transform>
  where $Y_d$ is the subgroup of $I(R_d)$ generated by the prime ideal divisors
  of $d$ in $R_d$. Consider a generator $P_(d j) P_(a j)^(-1)$ of $W_p$, where
  $d = p^u a$, $p divides.not a$. Then
  $
    epsilon(P_(d j) P_(a j)^(-1)) = product_e N_(d slash e) lr((P_(d j)))
    dot product_c N_(a slash c) lr((P_(a j)))^(-1),
  $
  where $e divides d$, $(e, d slash e) = 1$ and $c divides a$,
  $(c, a slash c) = 1$. The choices for $e$ are $p^u c$ and $c$, with $c$ as
  above. Since
  $
    N_(d slash c) lr((P_(d j))) = N_(a slash c) N_(d slash a) lr((P_(d j)))
    = N_(a slash c) lr((P_(a j))),
  $
  we obtain
  #source(74)
  $
    epsilon(P_(d j) P_(a j)^(-1)) = product_c N_(d slash (p^u c)) lr((P_(d j))).
  $
  This shows that the left side of formula
  @eq:cyclotomic-prime-subgroups-transform is contained in the right side. To
  prove the reverse inclusion, we use induction on the total number of prime
  factors of $d$ to establish that #named-equation(name: [(\*\*)])[$
    Y_d subset.eq product_(q divides n, q "prime") epsilon(W_q)
    quad "whenever" d divides n.
  $] <eq:cyclotomic-prime-subgroups-induction>
  This is clear when $d = p$, since $epsilon(P_(d j) P_(a j)^(-1)) = P_(d j)$
  for each $j$. Now let $d = p^u a$, $u >= 1$; then
  $
    epsilon(P_(d j) P_(a j)^(-1)) = P_(d j) dot
    product_c N_(d slash (p^u c)) lr((P_(d j))),
  $
  where $c$ ranges over all proper divisors of $a$ such that
  $(c, a slash c) = 1$. However, $product_c subset.eq product epsilon(W_q)$ by
  the induction hypothesis, and therefore also
  $P_(d j) subset.eq product epsilon(W_q)$. This proves
  @eq:cyclotomic-prime-subgroups-induction, and also
  @eq:cyclotomic-prime-subgroups-transform.

  We thus obtain
  $
    ker phi tilde.equiv product_(d divides n) lr({I(R_d) slash P(R_d) Y_d})
    tilde.equiv product_(d divides n) op("Cl")(R_d) slash V_d,
  $
  where $V_d$ is the subgroup of the ideal class group $op("Cl") R_d$ generated
  by the classes of all prime ideal divisors $lr({P_(d j)})$ of $d$. By Exercise
  @exc:ideal-class-localization-quotient, we have
  $ op("Cl")(R_d) slash V_d tilde.equiv op("Cl") R_(d)[d^(-1)], $
  where $R_(d)[d^(-1)]$ consists of all expressions
  $lr({alpha slash d^k: alpha in R_d, k >= 0})$. This completes the proof of the
  theorem.
]

#remarks[
  #enum(
    numbering: "(i)",
    [Keeping the above notation, let $Lambda' = product.co_(d divides n) R_d$ be
      the maximal order in $A$. The restriction map
      $alpha: G_0 lr((Lambda')) -> G_0 lr((Lambda))$ is given by
      $
        alpha: product.co op("Cl") R_d plus.o G_0 lr((A)) ->
        product.co op("Cl") R_(d)[d^(-1)] plus.o G_0 lr((A)),
      $
      where $op("Cl") R_d -> op("Cl") R_(d)[d^(-1)]$ is the surjection discussed
      above. Hence, if we choose a positive integer $d$ such that some prime
      ideal divisor of $d$ in $R_d$ is not principal, we obtain an example in
      which the map $alpha$ is not monic. For example, let $n = p q$ be a
      product of two distinct odd primes, chosen so that some prime ideal
      divisor $Q$ of $q$ in $R_p$ is not principal. Since $Q$ ramifies
      completely in the extension $R_n slash R_p$, it follows that
      $Q R_n = Q_0^(q-1)$ for some nonprincipal ideal $Q_0$ of $R_n$ dividing
      $q$. Thus the map $op("Cl") R_n -> op("Cl") R_(n)[n^(-1)]$ is not monic,
      and so $alpha$ is also not monic.],
    [Let $n = p^k$ be a prime power, and let $d divides n$. By
      @i:prop:prime-power-cyclotomic-ramification, the prime $p$ ramifies
      completely in $R_d$, and is a power of a principal ideal.
      #source(75)
      Thus $op("Cl") R_d = op("Cl") R_(d)[d^(-1)]$ in this case, so we obtain
      $G_0 lr((Lambda)) tilde.equiv G_0 lr((Lambda'))$. As we shall see below,
      this same isomorphism holds more generally when $Lambda = ZZ G$, with $G$
      any abelian $p$-group.],
  )
] <rem:cyclic-grothendieck-maximal-order-comparison>

Now let $A = QQ G$, $Lambda = ZZ G$, where $G$ is any finite abelian group. We
shall obtain a formula due to Lenstra @bib:Lenstra1981 for $G_0 lr((Lambda))$.
Let $lr({G_1, dots, G_t})$ be the set of all subgroups of $G$ for which the
factor group $G slash G_i$ is cyclic. Put
$
  H_i = G slash G_i = chevron.l x_i chevron.r,
  quad |H_i| = n_i, quad 1 <= i <= t,
$
and let
$
  K_(n_i) = QQ(zeta_(n_i)), quad R_(n_i) = ZZ[zeta_(n_i)],
  quad "where" zeta_(n_i) = "primitive" n_i "-th root of 1 over" QQ.
$
By Exercise @exc:abelian-rational-wedderburn-components, the Wedderburn
decomposition of $A$ is given by
$ A = product.co_(i=1)^t K_(n_i), $
and $G$ acts on $K_(n_i)$ by means of the surjection $G -> H_i$, and the
faithful action of $H_i$ on $K_(n_i)$ in which $x_i$ acts as multiplication by
$zeta_(n_i)$. The unique maximal order $Lambda'$ in $A$ is $product.co R_(n_i)$.
We have by @eq:heller-reiner-formula
$
  G_0 lr((Lambda)) tilde.equiv G_0 lr((A)) plus.o
  lr((product_(i=1)^t I(R_(n_i)))) slash
  lr((product_(i=1)^t P(R_(n_i)))) lr((product_(p divides n) W_p)).
$
For each prime $p$ dividing $n$, and each $i$, let $P_(i j)$ range over all
prime ideal divisors of $p$ in $R_(n_i)$. Then $lr({R_(n_i) slash P_(i j)})$
gives a basic set of simple $(Lambda' slash p Lambda')$-modules, and we have, as
before,
$
  W_p = {product_(i,j) P_(i j)^(b_(i j)):
    sum_(i,j) b_(i j) [R_(n_i) slash P_(i j)] = 0
    "in" G_0 lr((Lambda slash p Lambda))}.
$
For each $i$, write $n_i = m_i p^(k_i)$ where $p divides.not m_i$. Then as in
@eq:cyclotomic-residue-prime-relations,
$
  R_(n_i) slash P_(i j) tilde.equiv R_(m_i) slash P_(i j)^ast,
  quad "where" P_(i j)^ast = R_(m_i) inter P_(i j).
$
Apart from this, there are no other relations in
$G_0 lr((Lambda slash p Lambda))$, since $H_(m_i)$ is the unique cyclic factor
group of $G$ which acts faithfully on the module $R_(m_i) slash P_(i j)^ast$. It
follows at once that
$
  G_0 lr((ZZ G)) tilde.equiv product.co_(i=1)^t
  G_0 lr((R_(n_i)[n_i^(-1)])),
$
<eq:lenstra-abelian-grothendieck-formula>
or equivalently,
$
  G_0 lr((ZZ G)) tilde.equiv G_0 lr((A)) plus.o
  product_(i=1)^t op("Cl") R_(n_i)[n_i^(-1)].
$
Here each localized cyclotomic ring is Dedekind.#ed-note[
  For $G = C_2$, the printed right side $G_0 lr((ZZ)) plus.o G_0 lr((ZZ C_2))$
  has rank 3, whereas $G_0 lr((ZZ C_2))$ has rank 2. The localized cyclotomic
  factors above are those of @bib:Lenstra1981, Theorems 7.2 and 7.4.
] This is Lenstra’s formula for $G_0 lr((ZZ G))$; for further discussion of this
topic, and for its topological significance, see Bass @bib:Bass1979 and Lenstra
@bib:Lenstra1981.
#idx("Lenstra's formula", target: [@eq:lenstra-abelian-grothendieck-formula])

#source(76)
There is an analogous formula, somewhat more complicated, for the group
$G_1 lr((ZZ G))$ defined as in @def:whitehead-determinantal-group; for details,
see Liu @bib:Liu1982.

#corollary[
  For any abelian $p$-group $G$, we have
  $ G_0 lr((ZZ G)) tilde.equiv G_0 lr((Lambda')), $
  where $Lambda'$ is the maximal order of $QQ G$.
] <cor:abelian-p-group-grothendieck-maximal-order>

The above corollary has been generalized by David Webb @bib:Webb1983, by using
Frobenius functors. He showed that if $G$ is an arbitrary group which does not
contain a pair of commuting nonidentity elements of relatively prime order, then
$G_0 lr((ZZ G)) tilde.equiv G_0 lr((Lambda'))$, where $Lambda'$ is a maximal
order in $QQ G$. He also computed $G_0 lr((ZZ G))$ for $G$ dihedral. (Also see
Sumioka @bib:Sumioka1973.)

#exercises-heading

#exercise[
  Let $R$ be a d.v.r., not necessarily complete, and let $Lambda$ be an
  $R$-algebra, f.g./$R$ as module. Let $L, M, N$ be f.g. left $Lambda$-modules.
  Show that for $k >= 1$,
  $
    L^((k)) tilde.equiv M^((k)) arrow.r.double L tilde.equiv M
    quad "and" L plus.o M tilde.equiv L plus.o N arrow.r.double M tilde.equiv N.
  $
  #hint([@exc:local-order-module-cancellation])[
    Use @i:cor:complete-local-module-cancellation and
    @i:prop:module-isomorphism-completion.
  ]
] <exc:local-order-module-cancellation>

#exercise[
  Let $m$ be a nonzero element of a Dedekind domain $R$, and let $lr({P_i})$ be
  the set of prime ideal divisors of $m$ in $R$. Let $V$ be the subgroup of the
  ideal class group $op("Cl") R$ generated by the classes $[P_i]$. Prove that
  $op("Cl")(R) slash V tilde.equiv op("Cl") R[m^(-1)]$.
  #hint([@exc:ideal-class-localization-quotient])[
    Let $R' = R[m^(-1)]$; extension of ground ring from $R$ to $R'$ gives a
    homomorphism of ideal groups $I(R) -> I(R')$, which induces the desired
    isomorphism.
  ]
] <exc:ideal-class-localization-quotient>

#exercise[
  Let $Lambda$ be an arbitrary $R$-order in a f.d. $K$-algebra $A$, and let $e$
  be a central idempotent of $A$. Prove that there is a surjection
  $ G_0 lr((Lambda e)) plus.o G_0 lr((Lambda(1 - e))) -> G_0 lr((Lambda)). $
  Deduce from this that if $Lambda = ZZ G$ with $G$ abelian, then the map
  $alpha$ in @th:maximal-overorder-grothendieck-surjections is surjective. (See
  also Exercise @exc:fiber-product-grothendieck-sequence.)
] <exc:central-idempotent-grothendieck-decomposition>

#exercise[
  Let $G$ be a finite abelian group, and let $lr({G_1, dots, G_t})$ be the set
  of all subgroups of $G$ for which $G slash G_i$ is cyclic. Set
  $
    H_i = G slash G_i, quad n_i = |H_i|,
    quad H_i = chevron.l x_i chevron.r, quad 1 <= i <= t.
  $
  Let $K_(n_i) = QQ(zeta_(n_i))$, where $zeta_(n_i)$ is a primitive $n_i$-th
  root of 1 over $QQ$. Prove that
  $ QQ G tilde.equiv product.co_(i=1)^t K_(n_i), $
  where the $i$-th projection map is given by composition
  $ QQ G -> QQ H_i -> K_(n_i). $
  #source(77)
  #hint([@exc:abelian-rational-wedderburn-components])[
    Each Wedderburn component of $QQ G$ is a field $F = QQ(theta(G))$, where
    $theta: G -> F^dot$ is a homomorphism. Then $ker theta = G_i$ for some $i$,
    and $theta: H_i -> F^dot$ is a faithful representation of the cyclic group
    $H_i = G slash G_i$. This gives $F = QQ(theta(x_i))$, where
    $chevron.l x_i chevron.r = H_i$, so $F tilde.equiv K_(n_i)$. Further, there
    is a unique simple $QQ H_i$-module on which $H_i$ acts faithfully, namely
    $K_(n_i)$, so the Wedderburn components of $QQ G$ are in bijection with the
    set $lr({H_i: 1 <= i <= t})$.
  ]
] <exc:abelian-rational-wedderburn-components>

#exercise[
  Let $Lambda = R G$ where $G$ is a finite group and $R$ is a commutative ring.
  Prove that $K_1 lr((Lambda))$ is a Frobenius module over the Frobenius functor
  $G_0^R lr((Lambda))$.
  #hint([@exc:whitehead-frobenius-module])[
    Given $M in cal(P)(Lambda)$ and $mu in Aut_Lambda M$, and any
    $Lambda$-lattice $X$, define
    $ [X] dot [M, mu] = [X times.o_R M, 1 times.o mu]. $
    Show that this gives a well-defined action of $G_0^R lr((Lambda))$ on
    $K_1 lr((Lambda))$.
  ]
] <exc:whitehead-frobenius-module>
