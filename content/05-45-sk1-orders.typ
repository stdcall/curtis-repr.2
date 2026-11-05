#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/45-norms.typ": *

== $S K_1$ of Orders <sec:sk1-orders>

In order to study $K_1 lr((ZZ G))$ in §@sec:whitehead-integral-group-rings, we
shall need some general facts about $K_1$ and $S K_1$ of an arbitrary order. _We
assume throughout this section that $K$ is either a global field, or the
completion of a global field at a finite or infinite prime $P$._ Further, $R$ is
a Dedekind domain with quotient field $K$, and $Lambda$ is an $R$-order in the
f.d. separable $K$-algebra $A$.

=== Reduced Norms <ss:reduced-norms>

The calculation of $K_1 lr((A))$ reduces to the case of simple algebras, by
@eq:whitehead-wedderburn-decomposition. Until further notice, let $A$ be a
central simple $K$-algebra. As in @i:def:local-index-capacity-ramification and
@i:eq:positive-at-ramified-real-primes, we define
$
  K^+ = lr(
    {alpha in K^dot: alpha_P > 0 "at each real prime" P "of" K
      "ramified in" A}
  ).
$
<eq:reduced-norm-positive-subgroup>
#idx("K⁺", target: [@eq:reduced-norm-positive-subgroup])
Letting $op("nr"): A^dot -> K^dot$ be the reduced norm map
$op("nr")_(A slash K)$ defined in §@i:ss:reduced-norms, we have
$ op("nr") A^dot = K^+. $
<eq:reduced-norm-image>
#idx("Reduced norm", target: [@eq:reduced-norm-image])
This is the Hasse–Schilling–Maass Norm Theorem @i:th:hasse-schilling-maass-norm
when $K$ is a global field, while it is an easy exercise (see
@i:eq:real-quaternion-reduced-norm-image,
@i:th:local-field-reduced-norm-surjective) when $K$ is a complete field.

The notation $K^+$ is somewhat ambiguous, since $K^+$ depends not only on $K$,
but on the algebra $A$ as well. In practice, it will be clear from the context
what is intended.

We now amplify Remark @rem:maximal-order-k0-whitehead (ii), where we pointed out
the isomorphism $K_1 lr((A)) tilde.equiv K^+$.

#theorem[
  Let $A$ be a central simple $K$-algebra. Then the reduced norm
  $op("nr")_(A slash K)$ induces an isomorphism
  $ op("nr"): K_1 lr((A)) tilde.equiv K^+. $
  #source(155)
  Further, if $K$ is a complete field, then $K^+ = K^dot$ except when $K = RR$
  and $A tilde.equiv M_n lr((bb(H)))$, $bb(H) =$ real quaternions.
] <th:reduced-norm-whitehead-isomorphism>

#proof[
  The exercises in §@i:sec:separable-algebras-splitting-fields show that for
  $n >= 1$,
  $ op("nr") GL_n lr((A)) = op("nr") A^dot subset.eq K^dot. $
  Further, for $alpha in GL_n lr((A))$, we have
  $op("nr") mat(alpha, 0; 0, 1) = op("nr") alpha$. Thus the homomorphism
  $ op("nr"): GL lr((A)) -> K^dot $
  is well defined. Its kernel contains $GL' lr((A))$, so there is a homomorphism
  $op("nr"): K_1 lr((A)) -> K^dot$. By
  @i:eq:real-quaternion-reduced-norm-image–@i:th:hasse-schilling-maass-norm we
  have $op("nr") K_1 lr((A)) = K^+$.

  To prove $op("nr")$ injective, note that each element of $K_1 lr((A))$ can be
  represented by a $1 times 1$ matrix $(a)$, where $a in A^dot$ (see Exercise
  @exc:semisimple-whitehead-unit-representatives or Theorem
  @th:semilocal-whitehead-unit-surjection). If $op("nr")(a) = 1$, then
  $a in [A^dot,A^dot]$ by @i:th:nakayama-matsushima, @i:th:wang-platonov, and
  Exercise @i:exc:real-complex-norm-commutator-kernel. But then $(a) = 1$ in
  $K_1 lr((A))$, as desired.
]

Before turning to the calculation of $K_1 lr((Lambda))$, where $Lambda$ is a
maximal order, we need some information about the Eichler condition. Let $K$ be
a global field; by a _prime $P$ of $K$_ we mean an equivalence class of
valuations of $K$ (see §@i:ss:valuations-completions), always excluding the
trivial valuation.

#definitions[
  Let $K$ be a global field, and $R$ a Dedekind domain with quotient field $K$.
  A prime $P$ of $K$, which does not arise from a valuation of $K$ associated
  with a maximal ideal of $R$, will be called a “non-$R$” prime of $K$.

  Let $A$ be a simple f.d. $K$-algebra. We say that $A$ satisfies the _Eichler
  condition relative to $R$_, and use the notation $A = "Eichler" slash R$, if
  there exists at least one non-$R$ prime $P$ of $K$ such that at least one
  Wedderburn component of the $P$-adic completion $A_P$ is not a noncommutative
  division algebra. In other words, $A = "Eichler" slash R$ except when $A_P$ is
  a direct sum of noncommutative skewfields for every non-$R$ prime $P$ of $K$.

  Let $F$ be the center of $A$, and $S$ the integral closure of $R$ in $F$. By
  Exercise @exc:eichler-condition-center-extension below,
  $ A = "Eichler" slash R <=> A = "Eichler" slash S. $
  Further, for each prime $Q$ of $F$, the $Q$-adic completion $A_Q$ is a simple
  algebra with center $F_Q$. Therefore, $A = "Eichler" slash S$ except when
  $A_Q$ is a noncommutative division algebra for every non-$S$ prime $Q$ of $F$.

  Next, let $A$ be a f.d. semisimple $K$-algebra, with Wedderburn components
  $A_1,dots,A_s$. We shall say that $A$ satisfies the _Eichler condition
  relative to $R$_ if $A_i = "Eichler" slash R$ for each $i$.
] <def:eichler-condition>
#idx("Eichler condition", target: [@def:eichler-condition])
#idx("Non-R prime", target: [@def:eichler-condition])
#idx("Prime (of K)", target: [@def:eichler-condition])

#remarks[
  #enum(
    numbering: "(i)",
    [If $K$ is an algebraic number field and $R = "alg. int." lr({K})$,
      #source(156)
      then a central simple $K$-algebra $A$ satisfies the Eichler condition over
      $R$ except when $A$ is a totally definite quaternion algebra (see Volume
      I, @i:par:eichler-condition).],
    [The preceding version @def:eichler-condition of the Eichler condition was
      first introduced by Swan @bib:Swan1980. It coincides with the usual
      version when $K$ is an algebraic number field, but is a weaker restriction
      on $A$ when $K$ is a global function field (see, e.g., @bib:Reiner1975[MO]
      (Definition 34.3)). As shown by Swan, whose proof will be given in
      @th:eichler-maximal-order-unit-norm-global below, this weaker condition on
      $A$ is sufficient for the validity of the following fundamental result:],
  )
] <rem:eichler-condition-variants>

#theorem[
  Let $K$ be a global field, and let $Lambda$ be a maximal $R$-order in a
  central simple $K$-algebra $A$, where $A = "Eichler" slash R$. Then
  $ op("nr")_(A slash K) Lambda^dot = R^dot inter K^+. $
] <th:eichler-maximal-order-unit-norm>

From this, we derive readily:

#theorem[
  Let $K$ be a global field, and $Lambda$ a maximal $R$-order in a central
  simple $K$-algebra $A$. Then
  $ op("nr") K_1 lr((Lambda)) = R^dot inter K^+. $
] <th:maximal-order-whitehead-norm-image>

#proof[
  Since $op("nr")$ is multiplicative, we have
  $ op("nr") GL_n lr((Lambda)) subset.eq R^dot inter K^+, quad n >= 1. $
  Further, $M_2 lr((Lambda))$ is a maximal $R$-order in $M_2 lr((A))$. Now
  $M_2 lr((A))$ is a central simple $K$-algebra which is always
  $"Eichler" slash R$, whether or not $A$ is $"Eichler" slash R$. Therefore
  $op("nr") GL_2 lr((Lambda)) = R^dot inter K^+$ by
  @th:eichler-maximal-order-unit-norm, which establishes the theorem.
]

#remark[
  The reader may easily verify that $R^dot inter K^+$ is a subgroup of $R^dot$
  of finite index.
] <rem:positive-unit-subgroup-finite-index>

The local version of the preceding is much easier to prove:

#proposition[
  Let $R$ be a complete d.v.r. with quotient field $K$ and finite residue class
  field $overline(R)$. Let $Lambda$ be a maximal $R$-order in a central simple
  $K$-algebra $A$. Then
  $ op("nr") K_1 lr((Lambda)) = op("nr") Lambda^dot = R^dot. $
] <prop:local-maximal-order-unit-norm>

#proof[
  Let $A = M_k lr((D))$, where $D$ is a division algebra with center $K$, and
  let $Delta$ be the unique maximal $R$-order in $D$ (see
  @i:th:division-algebra-maximal-order-valuation). By
  @i:th:local-matrix-maximal-orders we have $Lambda = M_k lr((Delta))$ (up to
  conjugacy), and then (see Exercise @i:exc:matrix-algebra-reduced-norm-image)
  $
    K_1 lr((Lambda)) tilde.equiv K_1 lr((Delta)), quad
    op("nr")_(A slash K) Lambda^dot = op("nr")_(D slash K) Delta^dot.
  $
  #source(157)
  It suffices to show that $op("nr") Delta^dot = R^dot$, where now $op("nr")$
  means $op("nr")_(D slash K)$.

  By @bib:Reiner1975[MO] (§14), $D$ contains an _inertia subfield_ $W$, unique
  up to conjugacy, such that $W$ is a maximal subfield of $D$ and $W$ is
  unramified over $K$. Further, by @bib:Reiner1975[MO] (Exercise 14.5),
  $
    op("nr")_(D slash K) alpha = N_(W slash K) alpha
    quad "for all" alpha in W.
  $
  If $frak(o)_W$ denotes the integral closure of $R$ in $W$, then
  $frak(o)_W subset.eq Delta$, and thus
  $op("nr") Delta supset.eq N_(W slash K) lr((frak(o)_W))$. But the latter
  contains $R^dot$ by @bib:Reiner1975[MO] (14.1), and thus
  $op("nr") Delta supset.eq R^dot$. But if $x in Delta$ is such that
  $op("nr") x in R^dot$, it follows that also $N_(D slash K) lr((x)) in R^dot$,
  so $x in Delta^dot$ by @i:th:division-algebra-maximal-order-valuation or
  @i:cor:order-reduced-characteristic-integral. This completes the proof that
  $op("nr") Delta^dot = R^dot$, and establishes the proposition.
]
#idx("Inertia subfield", target: [@prop:local-maximal-order-unit-norm])

#remark[
  As we shall see in @th:local-maximal-order-sk1, the surjection
  $op("nr"): K_1 lr((Lambda)) -> R^dot inter K^+$ is seldom an isomorphism.
] <rem:order-norm-kernel-nontrivial>

To conclude this subsection, we briefly discuss the case of semisimple algebras.
Let $A$ be an f.d. separable $K$-algebra, with Wedderburn components
$lr({A_i: 1 <= i <= s})$. Let $C$ be the center of $A$, and write
$ C = plus.o.big_(i=1)^s F_i, quad F_i = "center of" A_i. $
We now define
$ C^+ = plus.o.big_(i=1)^s (F_i)^+, $
<eq:semisimple-positive-norm-subgroup>
so by @eq:reduced-norm-image and @th:reduced-norm-whitehead-isomorphism we
obtain
$
  op("nr"): K_1 lr((A)) tilde.equiv C^+, quad op("nr")_(A slash C) A^dot = C^+.
$
We now define
$
  S K_1 lr((Lambda)) = lr({x in K_1 lr((Lambda)): op("nr")_(A slash C) x = 1}),
$
<eq:reduced-whitehead-group>
#nidx(
  "$S K_1 lr((A))$",
  "kernel of determinant map or reduced norm map",
  target: [@eq:reduced-whitehead-group],
)
#idx("SK₁", target: [@eq:reduced-whitehead-group])
so there is an exact sequence
$ 1 -> S K_1 lr((Lambda)) -> K_1 lr((Lambda)) -> K_1 lr((A)). $
<eq:reduced-whitehead-kernel-sequence>
When $Lambda$ is commutative, then $op("nr")_(A slash C)$ is the usual
determinant map $det: K_1 lr((Lambda)) -> Lambda^dot$. Therefore
$
  S K_1 lr((Lambda)) = lr({x in K_1 lr((Lambda)): det x = 1})
  quad "if" Lambda "is commutative".
$
The surjection $det: K_1 lr((Lambda)) -> Lambda^dot$ is split by the
homomorphism $u mapsto (u)$, $u in Lambda^dot$, and therefore

#source(158)
$ K_1 lr((Lambda)) tilde.equiv Lambda^dot times S K_1 lr((Lambda)) $
whenever $Lambda$ is commutative. Thus, definitions @eq:reduced-whitehead-group
and @eq:commutative-whitehead-splitting agree in the commutative case. We also
have:

#proposition[
  Let $Lambda$ be a commutative semilocal ring. Then
  $ S K_1 lr((Lambda)) = 1, quad K_1 lr((Lambda)) tilde.equiv Lambda^dot. $
] <prop:commutative-semilocal-sk1>
#proof[
  Immediate from @th:semilocal-whitehead-unit-surjection and the preceding
  remarks.
]

=== Maximal Orders <ss:sk1-maximal-orders>

We show here how to compute $K_1 lr((Lambda))$ and $S K_1 lr((Lambda))$, where
$Lambda$ is a maximal order in a separable $K$-algebra $A$ over a global field
$K$. Of course, it suffices to treat the case where $A$ is a central simple
$K$-algebra. Further, let $A tilde.equiv M_n lr((D))$, with $D$ a skewfield, and
let $Delta$ be a maximal order in $D$. Then every maximal order $Lambda$ in $A$
is Morita equivalent to the maximal order $M_n lr((Delta))$, and we have
$
  K_1 lr((A)) tilde.equiv K_1 lr((D)), quad
  K_1 lr((Lambda)) tilde.equiv K_1 lr((Delta)), quad
  S K_1 lr((Lambda)) tilde.equiv S K_1 lr((Delta)),
$
so the problem reduces to the case of a maximal order in a skewfield.

We begin with the local calculation, due to Kuku @bib:Kuku1976 and Keating
@bib:Keating1976.

#theorem[
  Let $R$ be a complete d.v.r. with finite residue class field
  $overline(R) = R slash P$ and quotient field $K$. Let $D$ be a division
  algebra of dimension $m^2$ over its center $K$, and let $Delta$ be a maximal
  $R$-order in $D$. Then $S K_1 lr((Delta))$ is a cyclic group of order
  $(q^m-1) slash (q-1)$, where $q = |overline(R)|$, and there is an exact
  sequence of abelian groups
  $ 1 -> S K_1 lr((Delta)) -> K_1 lr((Delta)) arrow.r^(op("nr")) R^dot -> 1, $
  where $op("nr")$ means $op("nr")_(D slash K)$.
] <th:local-maximal-order-sk1>
#idx("SK₁", target: [@th:local-maximal-order-sk1])
#idx("Kuku's Theorem", target: [@th:local-maximal-order-sk1])
#idx("Keating’s Theorem", target: [@th:local-maximal-order-sk1])

#proof[
  We already know that $op("nr") K_1 lr((Delta)) = R^dot$ by
  @prop:local-maximal-order-unit-norm, and by definition $S K_1 lr((Delta))$ is
  the kernel of $op("nr")$. We must prove that $S K_1 lr((Delta))$ is a cyclic
  group of order $(q^m-1) slash (q-1)$. Let $W$ be an inertia subfield of $D$,
  as in the proof of @prop:local-maximal-order-unit-norm. As shown in
  @bib:Reiner1975[MO] (§14), we may write $W = K(omega)$, where $omega$ is a
  primitive $(q^m-1)$-st root of $1$ over $K$. Then
  $ overline(Delta) = Delta slash rad Delta = overline(R)(overline(omega)), $
  a field extension of $overline(R)$ of degree $m$. Here, $overline(omega)$ is
  the image of $omega$ in $overline(Delta)$, and is a primitive $(q^m-1)$-st
  root of $1$ over $overline(R)$; it generates the cyclic group
  $overline(Delta)^dot$.

  #source(159)
  Let $pi_D$ denote a prime element of $Delta$. Then (see @bib:Reiner1975[MO]
  (14.6))
  $
    rad Delta = pi_D Delta = Delta pi_D, quad
    pi_D omega pi_D^(-1) = omega^(q^r)
  $
  for some integer $r$ with $(r,m) = 1$. It is easily seen that $omega^(q^r-1)$
  has order $(q^m-1) slash (q-1)$; the same holds with $overline(omega)$ in
  place of $omega$. Further,
  $ omega^(q^r-1) = pi_D omega pi_D^(-1) omega^(-1), $
  so $op("nr") omega^(q^r-1) = 1$. Thus, the cyclic group $⟨ omega^(q^r-1) ⟩$
  maps into $S K_1 lr((Delta))$, and we claim the map is an embedding. Indeed,
  the homomorphism $K_1 lr((Delta)) -> K_1 lr((overline(Delta)))$ carries
  $(omega)$ onto $(overline(omega))$. Since
  $K_1 lr((overline(Delta))) = ⟨ overline(omega) ⟩$, this shows that the group
  $⟨ omega ⟩$ is embedded in $K_1 lr((Delta))$, and therefore
  $⟨ omega^(q^r-1) ⟩$ is embedded in $S K_1 lr((Delta))$. Note that
  $⟨ omega^(q^r-1) ⟩$ is cyclic of order $(q^m-1) slash (q-1)$, and we must show
  that it coincides with $S K_1 lr((Delta))$.

  We next observe that there is an exact localization sequence
  $ K_1 lr((cal(T))) arrow.r^epsilon K_1 lr((Delta)) -> K_1 lr((D)), $
  where $cal(T)$ is the category of all f.g. $R$-torsion $Delta$-modules of
  finite homological dimension. The last restriction is superfluous since
  $"gl. dim." Delta <= 1$, because the ring $Delta$ is hereditary. To describe
  the map $epsilon$, note that each element of $K_1 lr((cal(T)))$ is of the form
  $[T,tau]$ with $T in cal(T)$ and $tau in Aut_Delta T$. Since the homological
  dimension of $T$ is $<= 1$, we can then find $Q_i in cal(P)(Delta)$ and
  $phi_i in Aut_Delta Q_i$, $i = 1,2$, for which the sequence of pairs
  $ 0 -> (Q_1,phi_1) -> (Q_2,phi_2) -> (T,tau) -> 0 $
  is exact. Then
  $ epsilon[T,tau] = [Q_2,phi_2]-[Q_1,phi_1] in K_1 lr((Delta)). $
  (Note that we have used the determinantal version of $K_1 lr((cal(T)))$, as
  given in the discussion preceding @def:whitehead-determinantal-group.)

  Next, each $T in cal(T)$ has a filtration
  $ T supset pi_D T supset pi_D^2 T supset dots supset pi_D^l T = 0 $
  for some $l$. Each factor is a left $overline(Delta)$-module, so as in
  §@ss:localization-sequences we obtain
  $K_1 lr((cal(T))) tilde.equiv K_1 lr((overline(Delta)))$. Note that
  $K_1 lr((overline(Delta))) tilde.equiv overline(Delta)^dot
  = ⟨ overline(omega) ⟩$, and we shall now compute $epsilon ⟨ overline(omega) ⟩$
  in $K_1 lr((Delta))$. For this purpose, we note that the element
  $(overline(omega)) in K_1 lr((overline(Delta)))$ corresponds to the pair
  $[overline(Delta),overline(omega)]$. There is an exact sequence
  $
    0 -> (pi_D Delta,omega) -> (Delta,omega)
    -> (overline(Delta),overline(omega)) -> 0,
  $
  and therefore
  $
    epsilon(overline(omega)) = [Delta,omega]-[pi_D Delta,omega]
    in K_1 lr((Delta)).
  $

  #source(160)
  However,
  $ (pi_D Delta,omega) tilde.equiv (Delta,pi_D omega pi_D^(-1)), $
  as follows from the commutative diagram (of right multiplications)
  #local-unit-conjugation
  Therefore
  $
    epsilon(overline(omega)) = (omega pi_D omega^(-1) pi_D^(-1))
    = (omega^(1-q^r)) in K_1 lr((Delta)).
  $
  Since $im epsilon = S K_1 lr((Delta))$, we have now shown that
  $S K_1 lr((Delta))$ coincides with the cyclic group $⟨ omega^(q^r-1) ⟩$ of
  order $(q^m-1) slash (q-1)$, and the theorem is established.
]

The global version of the preceding theorem is considerably deeper. We follow
the treatment in Keating @bib:Keating1976, which uses the Bass–Milnor–Serre
Theorem and Quillen’s Localization Sequence. We begin by recalling some
notation. Let $D$ be a skewfield with center $K$. For each prime $P$ of $K$, let
$D_P$ be its $P$-adic completion. Then we may write
$
  D_P tilde.equiv M_(kappa_P) lr((Omega_P)), quad
  dim_(K_P) Omega_P = m_P^2,
$
<eq:division-algebra-local-index>
#idx("Local capacity", target: [@eq:division-algebra-local-index])
#idx("Local index", target: [@eq:division-algebra-local-index])
#idx("Unramified", target: [@eq:division-algebra-local-index])
where $Omega_P$ is a skewfield with center $K_P$ and index $m_P$. We call
$kappa_P$ the _local capacity_ of $D$ at $P$, and $m_P$ the _local index_. We
say that $P$ is _ramified_ in $D$ if $m_P > 1$, and _unramified_ if $m_P = 1$.
Then $m_P = 1$ a.e. (see @bib:Reiner1975[MO] (32.1)). We are now ready to prove:

#theorem(title: [Keating @bib:Keating1976])[
  Let $Delta$ be a maximal $R$-order in a division algebra $D$ with center $K$ a
  global field. For each maximal ideal $P$ of $R$, let $m_P$ be the local index
  of $D$ at $P$, and let $q_P = |R slash P|$. Then
  $ S K_1 lr((Delta)) tilde.equiv product.co_P S K_1 lr((Delta_P)), $
  and $S K_1 lr((Delta_P))$ is a cyclic group of order
  $(q_P^(m_P)-1) slash (q_P-1)$, which is trivial a.e. Further, there is an
  exact sequence
  $ 1 -> S K_1 lr((Delta)) -> K_1 lr((Delta)) -> R^dot inter K^+ -> 1, $
  where $K^+$ is defined as in @eq:reduced-norm-positive-subgroup.
] <th:keating-global-maximal-order-sk1>
#idx("Keating’s Theorem", target: [@th:keating-global-maximal-order-sk1])
#idx(
  "Quillen's Localization Sequence",
  target: [@th:keating-global-maximal-order-sk1],
)

#proof[
  _Step 1._ Let $cal(T)$ be the category of f.g. $R$-torsion $Delta$-modules;
  each $T in cal(T)$ has finite homological dimension, since $Delta$ is
  hereditary.
  #source(161)
  By Quillen’s Localization Sequence @rem:quillen-localization-sequence, there
  is an exact sequence#footnote[
    For an explicit description of the map $theta$ when $D$ is a global field,
    see the discussion of tame symbols in §@ss:k2-symbols.
  ]
  $
    K_2 lr((D)) arrow.r^theta K_1 lr((cal(T))) -> K_1 lr((Delta))
    -> K_1 lr((D)),
  $
  so $S K_1 lr((Delta)) tilde.equiv op("cok") theta$, and it remains to compute
  $op("cok") theta$. Note that $op("nr") K_1 lr((Delta)) = R^dot inter K^+$ by
  Theorem @th:maximal-order-whitehead-norm-image.

  As in the proof of @th:local-maximal-order-sk1, we have
  $
    K_1 lr((cal(T))) tilde.equiv product.co_P K_1 lr((cal(T)_P)), quad
    "where" cal(T)_P = "category of" P"-torsion modules in" cal(T).
  $
  Next, for fixed $P$, each $T in cal(T)_P$ is a $Delta_P$-module having a
  $Delta_P$-composition series, and therefore
  $K_1 lr((cal(T)_P)) tilde.equiv K_1 lr((Delta_P slash rad Delta_P))$. But (see
  @eq:division-algebra-local-index)
  $
    Delta_P tilde.equiv M_(kappa_P) lr((Gamma_P)), quad
    Delta_P slash rad Delta_P tilde.equiv M_(kappa_P) lr((overline(Gamma)_P)),
    quad "where" overline(Gamma)_P tilde.equiv Gamma_P slash rad Gamma_P.
  $
  Note that $overline(Gamma)_P$ is a field extension of $R slash P$ of degree
  $m_P$, so now
  $
    K_1 lr((cal(T)_P)) tilde.equiv K_1 lr((overline(Gamma)_P))
    tilde.equiv (overline(Gamma)_P)^dot,
  $
  <eq:torsion-whitehead-residue-field>
  a cyclic group of order $q_P^(m_P)-1$. Therefore
  $K_1 lr((cal(T))) tilde.equiv product.co_P (overline(Gamma)_P)^dot$, and it
  thus suffices to prove that
  $
    theta(K_2 lr((D))) = product.co_P (R slash P)^dot
    quad "in" product.co_P (overline(Gamma)_P)^dot.
  $
  For each maximal ideal $P_0$ of $R$, there is a commutative diagram
  #keating-localization-square
  But $im theta_0 subset.eq (R slash P_0)^dot$ by @th:local-maximal-order-sk1,
  and so we obtain
  $
    theta(K_2 lr((D))) subset.eq product.co_P (R slash P)^dot
    quad "in" product.co_P K_1 lr((overline(Gamma)_P)).
  $
  The entire difficulty lies in establishing the reverse inclusion.

  #source(162)
  Let $x = (x_P) in product.co (R slash P)^dot$, where $x_P = 1$ a.e. Let
  $cal(S)$ be a finite set of primes of $K$ (including possibly some of the
  infinite primes), such that for $P in.not cal(S)$ we have $x_P = 1$ and
  $m_P = 1$. In Step 2, we shall construct a maximal subfield $L$ of $D$, which
  depends on the set $cal(S)$, with certain properties. Let $S$ be the integral
  closure of $R$ in $L$. Since we may replace $Delta$ by any other maximal order
  $Delta'$ in $D$ without affecting the remainder of the argument, and since
  $K_1 lr((Delta_P slash rad Delta_P)) tilde.equiv
  K_1 lr((Delta'_P slash rad Delta'_P))$ for each $P$, we may assume that
  $S subset.eq Delta$. The inclusions $S subset.eq Delta$, $L subset.eq D$, give
  rise to a commutative diagram with exact rows:
  #keating-subfield-comparison
  Here, $Q$ ranges over all maximal ideals of $S$. The Bass–Milnor–Serre Theorem
  tells us that $S K_1 lr((S)) = 1$, or equivalently, that $theta'$ is
  surjective. It therefore suffices to prove that $x in im psi$.

  _Step 2._ Let $m$ be the index of the skewfield $D$, so $dim_K D = m^2$. By
  @eq:division-algebra-local-index we have $m_P kappa_P = m$ for each prime $P$
  of $K$. As above, let $cal(S)$ be a finite set of primes $P$ of $K$, including
  all those for which $x_P != 1$ or $m_P > 1$. By the Grunwald–Wang Theorem (see
  @bib:Reiner1975[MO] (32.18)), we may choose a field $L$ which is a Galois
  extension of $K$ with cyclic Galois group of order $m$, such that
  $
    dim_(K_P) L_(P_i) = m_P quad "for each" P in cal(S)
    "and each prime" P_i "of" L "extending" P.
  $
  Then $L$ is a splitting field for $D$ over $K$ (see @bib:Reiner1975[MO]
  (32.15)), and since $dim_K L = m$, we can embed $L$ as a maximal subfield of
  $D$ (see @bib:Reiner1975[MO] (28.10)).

  Let $S$ be the integral closure of $R$ in $L$; for each maximal ideal $P$ of
  $R$ such that $x_P != 1$, let $P_i$ range over the maximal ideals of $S$
  containing $P$. It suffices to show that the image of the map
  $ psi_P: product.co_i (S slash P_i)^dot -> K_1 lr((overline(Gamma)_P)) $
  is precisely $(R slash P)^dot$, using the identifications in
  @eq:torsion-whitehead-residue-field. The problem is thus reduced to a local
  situation, but one in which $R$ is not complete. There is no loss of
  generality in assuming that $R$ is a d.v.r. from this point on.

  Let us write
  $
    P S = product_(i=1)^kappa P_i^(e_i), quad
    f_i = dim_overline(R) lr((S slash P_i)),
  $
  where $overline(R) = R slash P$. Then $e_i f_i = dim_(K_P) L_i = m_P$, where
  $L_i$ is an abbreviation for $L_(P_i)$.

  #source(163)
  We have
  $ m = dim_(K_P) L_P = sum_(i=1)^kappa dim_(K_P) L_i = m_P kappa, $
  so $kappa = kappa_P$. For the remainder of the proof, we simplify the notation
  by writing
  $
    D_P tilde.equiv M_kappa lr((Omega)), quad Delta_P = M_kappa lr((Gamma)),
    quad overline(Gamma) = Gamma slash rad Gamma, quad
    overline(S) = S slash P_1, quad q = |overline(R)|.
  $
  The isomorphism $L_P tilde.equiv product.co L_i$ may be written as
  $ L_P = plus.o.big_(i=1)^kappa L_i epsilon_i, $
  where $1 = epsilon_1 + dots + epsilon_kappa$ is a decomposition into
  orthogonal primitive idempotents. Then $D_P = plus.o D_P epsilon_i$ is a
  decomposition of $D_P$ into minimal left ideals, and we may thus identify
  $epsilon_i$ with the diagonal matrix $op("diag")(0,dots,0,1,0,dots,0)$, with
  $1$ in $i$-th position, this for $1 <= i <= kappa$.

  Let $u in overline(S)^dot$, viewed as an element
  $[overline(S),u] in K_1 lr((overline(S)))$. Then
  $
    psi_P lr((u)) = [Delta times.o_S (S slash P_1),1 times.o u]
    = [Delta slash Delta P_1,1 times.o u] in K_1 lr((Delta slash P Delta)),
  $
  and in these formulas we may replace $Delta$ by its completion $Delta_P$. In
  order to identify $psi_P lr((u))$ as an element of
  $K_1 lr((overline(Gamma)))$, we need a $Delta_P$-composition series for
  $Delta slash Delta P_1$. Now we have
  $
    S_P = plus.o.big_(i=1)^kappa S_i epsilon_i, quad
    P_1 S_P = P_1 S_1 epsilon_1 plus.o
    lr((plus.o.big_(i=2)^kappa S_i epsilon_i)),
  $
  where $S_i$ is the $P_i$-adic completion of $S$. Therefore
  $
    Delta_P slash Delta_P P_1 tilde.equiv
    M_kappa lr((Gamma slash Gamma P_1)) dot epsilon_1.
  $
  Note that
  $
    Gamma tilde.equiv epsilon_1 Delta_P epsilon_1, quad
    S_1 = S_P epsilon_1 = epsilon_1 S_P,
  $
  so $Gamma$ is a two-sided $S_1$-module, and $S_1 subset Gamma$.

  Let $pi,pi_1$, and $xi$ denote prime elements, with
  $ P = pi R, quad P_1 = pi_1 S, quad rad Gamma = xi Gamma = Gamma xi. $
  Then up to unit factors we have
  $ pi = xi^(m_P), quad pi = pi_1^(e_1), quad "so" pi_1 = xi^(f_1), $
  using the fact that $e_1 f_1 = m_P$. Therefore
  $Gamma slash Gamma P_1 = Gamma slash Gamma xi^(f_1)$, so
  $Delta_P slash Delta_P P_1 tilde.equiv
  (Gamma slash Gamma xi^(f_1))^((kappa))$, #source(164)the left $Gamma$-module
  consisting of all $kappa times 1$ column vectors with entries in
  $Gamma slash Gamma xi^(f_1)$. As in the proof of @th:local-maximal-order-sk1,
  we may write
  $ xi u xi^(-1) = u^(q^r) quad "in" overline(S), $
  for some $r$ relatively prime to $m_P$. We obtain
  $
    psi_P lr((u)) & = [(Gamma slash Gamma xi^(f_1))^((kappa)),1 times.o u]
                    = sum_(i=0)^(f_1-1)
                    [(Gamma xi^i slash Gamma xi^(i+1))^((kappa)),1 times.o u] \
                  & = sum_i [(Gamma slash Gamma xi)^((kappa)),
                      xi^i (1 times.o u) xi^(-i)] in K_1 lr((cal(T)_P)).
  $
  Now $Gamma slash Gamma xi = overline(Gamma)$, and $overline(Gamma)^((kappa))$
  is a simple left $M_kappa lr((overline(Gamma)))$-module. Identifying
  $K_1 lr((cal(T)_P))$ with $K_1 lr((overline(Gamma)))$, the image of
  $psi_P lr((u))$ in $overline(Gamma)^dot$ becomes
  $ product_(i=0)^(f_1-1) u^(q^(i r)) in overline(S). $
  However, $overline(S)$ is a Galois extension of $overline(R)$ of degree $f_1$,
  with cyclic Galois group generated by the Frobenius automorphism
  $sigma: alpha mapsto alpha^q$, $alpha in overline(S)$. Then $sigma^r$ also
  generates this Galois group, and so
  $
    psi_P lr((u)) = product_(i=0)^(f_1-1) sigma^i lr((u))
    = N_(overline(S) slash overline(R)) lr((u)) in overline(R)^dot.
  $
  Moreover, $N_(overline(S) slash overline(R))$ maps $overline(S)$ onto
  $overline(R)$ (see @bib:Reiner1975[MO] (14.1)), and it follows that
  $
    psi_P lr({product.co_(i=1)^kappa (S slash P_i)^dot})
    = overline(R)^dot subset.eq overline(Gamma)^dot,
  $
  as desired. This completes the proof of the theorem.
]

The preceding theorem generalizes to the case of hereditary orders, as shown by
Oliver @bib:Oliver1980b. Since a hereditary order $Lambda$ in a $K$-algebra $A$
decomposes according to the Wedderburn decomposition of $A$ (see
@i:th:hereditary-orders-wedderburn-components), it suffices to treat the case
where $A$ is a central simple $K$-algebra. The main result is as follows:

#theorem(title: [Oliver])[
  Let $Lambda$ be a hereditary $R$-order in a central simple $K$-algebra $A$,
  where $K$ is a global field. Then
  $ S K_1 lr((Lambda)) tilde.equiv product.co_P S K_1 lr((Lambda_P)), $
  where $P$ ranges over the maximal ideals of $R$, and $Lambda_P$ is the
  $P$-adic completion of $Lambda$. The terms $S K_1 lr((Lambda_P))$ are zero for
  almost all $P$.

  #source(165)
  Further, for each $P$ we may write #equation-suffix(
    base: [@th:oliver-hereditary-order-sk1],
    suffix: "a",
  )[$
    Lambda_P slash rad Lambda_P tilde.equiv
    product.co_(i=1)^r M_(n_i) lr((overline(Delta)))
  $] <eq:hereditary-order-residue-decomposition>
  for some field $overline(Delta)$ containing $overline(R)$, where
  $overline(R) = R slash P$ (see @i:th:local-hereditary-orders-block-form (ii)).
  Then
  $
    S K_1 lr((Lambda_P)) tilde.equiv
    lr((product_(i=1)^r overline(Delta)^dot)) slash overline(R)^dot,
  $
  with $overline(R)^dot$ embedded diagonally in the product.
] <th:oliver-hereditary-order-sk1>

#proof[
  Let $Lambda subset.eq Gamma =$ maximal $R$-order in $A$. Then
  $Lambda_P = Gamma_P$ for almost all $P$, and therefore
  $S K_1 lr((Lambda_P)) = 1$ a.e. by @th:keating-global-maximal-order-sk1. To
  simplify the proof, we shall use a few results from the
  @app:class-group-basic-formulas. As shown there, we have a surjection
  $ S K_1 lr((Lambda)) -> product.co_P S K_1 lr((Lambda_P)), $
  whose kernel is denoted by $op("Cl")_1 Lambda$. From Keating’s Theorem we
  obtain $op("Cl")_1 Gamma = 1$, and we must prove here that
  $op("Cl")_1 Lambda = 1$.

  From the @app:class-group-basic-formulas, there is a commutative diagram with
  exact rows:
  #hereditary-class-kernel-comparison
  To prove that $op("Cl")_1 Lambda = 1$, it thus suffices to verify that
  #equation-suffix(base: [@th:oliver-hereditary-order-sk1], suffix: "b")[$
    im K_2 lr((Lambda_P)) = im K_2 lr((Gamma_P)) quad "in" K_2 lr((A_P))
  $] <eq:hereditary-maximal-order-k2-image>
  for each $P$.

  Changing notation for the rest of the proof, we now assume that $R$ is a
  complete d.v.r. with finite residue class field $overline(R)$. The Quillen
  Localization Sequence gives an exact sequence
  $
    1 -> K_2 lr((A)) slash im K_2 lr((Lambda)) -> K_1 lr((cal(T)))
    -> S K_1 lr((Lambda)) -> 1,
  $
  where $cal(T)$ is the category of f.g. $R$-torsion $Lambda$-modules of finite
  homological dimension. But every $Lambda$-module has finite homological
  dimension, since $Lambda$ is hereditary. The proof of
  @lem:class-group-localization-comparison then shows that
  $K_1 lr((cal(T))) tilde.equiv K_1 lr((Lambda slash rad Lambda))$. We thus
  obtain a commutative diagram with exact rows:

  #source(166)
  #hereditary-localization-comparison
  One easily verifies that in order to prove
  @eq:hereditary-maximal-order-k2-image, it suffices to establish
  #equation-suffix(base: [@th:oliver-hereditary-order-sk1], suffix: "c")[$
    |S K_1 lr((Lambda))| >=
    |K_1 lr((Lambda slash rad Lambda))| slash |im theta'|.
  $] <eq:hereditary-sk1-cardinality-bound>
  From the proof of @th:keating-global-maximal-order-sk1 we have
  $im theta' tilde.equiv overline(R)^dot$. Then as in
  @eq:hereditary-order-residue-decomposition we may write
  $
    Lambda slash rad Lambda tilde.equiv
    product.co_(i=1)^r M_(n_i) lr((overline(Delta))),
  $
  with $overline(Delta)$ some finite field extension of $overline(R)$. (Indeed,
  we have $Gamma slash rad Gamma tilde.equiv M_n lr((overline(Delta)))$ for some
  $n$, and $dim_overline(R) overline(Delta)$ is the index of the skewfield part
  of $A$.) We thus obtain
  $
    K_1 lr((Lambda slash rad Lambda)) tilde.equiv
    product_(i=1)^r K_1 lr((M_(n_i) lr((overline(Delta)))))
    tilde.equiv product_(i=1)^r overline(Delta)^dot,
  $
  a finite $p'$-group. It follows that $S K_1 lr((Lambda))$ is also a
  $p'$-group.

  Consider next the isomorphism
  $ op("nr"): K_1 lr((A)) tilde.equiv K^dot $
  given in @th:reduced-norm-whitehead-isomorphism. Identifying $K_1 lr((A))$
  with $K^dot$, it follows as in @prop:local-maximal-order-unit-norm that
  $op("nr") K_1 lr((Lambda)) subset.eq R^dot$, and there is an exact sequence
  $ 1 -> S K_1 lr((Lambda)) -> K_1 lr((Lambda)) arrow.r^(op("nr")) R^dot. $
  By @th:wall-whitehead-pro-p-splitting, we may write
  $
    K_1 lr((Lambda)) tilde.equiv K_1 lr((Lambda slash rad Lambda)) times V_0,
    quad "and" R^dot tilde.equiv overline(R)^dot times V_1,
  $
  where $V_0$ and $V_1$ are pro-$p$-groups. Since $S K_1 lr((Lambda))$ has
  already been shown to be a $p'$-group, it follows that there is an exact
  sequence
  $
    1 -> S K_1 lr((Lambda)) -> K_1 lr((Lambda slash rad Lambda))
    -> overline(R)^dot.
  $
  But this implies @eq:hereditary-sk1-cardinality-bound, and completes the proof
  of the first assertion of the theorem.

  #source(167)
  Finally, we obtain (in the local case)
  $
    S K_1 lr((Lambda)) tilde.equiv
    K_1 lr((Lambda slash rad Lambda)) slash im theta
    tilde.equiv lr((product_(i=1)^r overline(Delta)^dot)) slash overline(R)^dot,
  $
  where $overline(R)^dot$ is embedded diagonally in the product. This completes
  the proof of Oliver’s Theorem.
]

=== Finiteness of $S K_1$ <ss:sk1-finiteness>

Throughout this subsection, let $Lambda$ be an $R$-order in an f.d. separable
$K$-algebra $A$, where $K$ is either a global field or a non-archimedean
completion of a global field. Let $Lambda'$ be a maximal $R$-order in $A$
containing $Lambda$, so $S K_1 lr((Lambda'))$ is a finite group by
§@ss:sk1-maximal-orders. By comparing $S K_1 lr((Lambda))$ with
$S K_1 lr((Lambda'))$, we shall establish the fundamental result (due to Bass)
that $S K_1 lr((Lambda))$ is also a finite group.

We begin with a preliminary result, which is valid in a somewhat more general
situation.

#theorem[
  Let $Lambda subset Gamma$ be $R$-orders in a f.d. $K$-algebra $A$, where $R$
  is any Dedekind domain with finite residue class fields. Let
  $ theta: K_1 lr((Lambda)) -> K_1 lr((Gamma)) $
  be the homomorphism induced by the inclusion $Lambda subset Gamma$. Then
  $ker theta$ and $op("cok") theta$ are finite.
] <th:order-inclusion-whitehead-finite-kernel-cokernel>

#proof[
  _Step 1._ Choose a nonzero $r in R$ with $r Gamma subset.eq Lambda$, and let
  $n >= 3$. Then (see @eq:relative-general-linear-sequence) we have
  $
    GL_n lr((Gamma,r Gamma)) subset.eq GL_n lr((Lambda))
    subset.eq GL_n lr((Gamma)),
  $
  and $|GL_n lr((Gamma)): GL_n lr((Gamma,r Gamma))|$ is finite (since
  $Gamma slash r Gamma$ is a finite ring). Thus the map
  $ alpha: GL_n lr((Lambda)) -> GL_n lr((Gamma)) $
  has finite cokernel. But $GL_n lr((Gamma))$ maps onto $K_1 lr((Gamma))$ by
  @cor:surjective-stability-dedekind, so $op("cok") alpha$ maps onto
  $op("cok") theta$. Therefore $op("cok") theta$ is finite, as claimed.

  Now let $J$ be any two-sided ideal of $Lambda$ for which $K dot J = A$. By
  @eq:relative-whitehead-group and @cor:relative-k-theory-exact-sequence, there
  is an exact sequence
  $
    K_1 lr((Lambda,J)) arrow.r^phi K_1 lr((Lambda))
    -> K_1 lr((Lambda slash J)),
  $
  <eq:full-ideal-relative-whitehead-sequence>
  where $K_1 lr((Lambda,J)) = GL lr((Lambda,J)) slash E lr((Lambda,J))$. Since
  $Lambda slash J$ is a finite ring, $K_1 lr((Lambda slash J))$ is finite by
  @th:semilocal-whitehead-unit-surjection, and therefore $op("cok") phi$ is a
  finite group. Since $n >= 3$, it follows from
  @cor:relative-whitehead-finite-algebra-stability that

  #source(168)
  $
    K_1 lr((Lambda,J)) tilde.equiv GL_n lr((Lambda,J)) slash E_n lr((Lambda,J)),
    quad K_1 lr((Lambda)) tilde.equiv GL_n lr((Lambda)) slash E_n lr((Lambda)).
  $
  We shall use these formulas to prove that $ker phi$ is finite.

  _Step 2._ We set
  $ G = GL_n lr((Lambda)), quad N = GL_n lr((Lambda,J)) ⊴ G. $
  Then by @th:bass-relative-elementary-commutators and
  @th:relative-whitehead-injective-stability
  $
    K_1 lr((Lambda,J)) = N slash [G,N], quad
    K_1 lr((Lambda)) = G slash [G,G].
  $
  Note that $G slash N subset.eq GL_n lr((Lambda slash J))$, so $G slash N$ is
  finite. Let $overline(G) = G slash N$, and let $ZZ$ be the trivial $G$-module.
  There is an exact sequence of #idx("Homology groups")homology groups#footnote[
    This is the Hochschild–Serre–Lyndon sequence of homology groups; see Rotman
    @bib:Rotman1979, Theorem 11.6.
  ]
  $
    H_2 lr((G,ZZ)) -> H_2 lr((overline(G),ZZ))
    -> H_1 lr((N,ZZ)) slash I_overline(G) dot H_1 lr((N,ZZ))
    arrow.r^psi H_1 lr((G,ZZ)) -> H_1 lr((overline(G),ZZ)),
  $
  where $I_overline(G)$ is the augmentation ideal of $ZZ overline(G)$. By
  Exercise @i:exc:first-homology-abelianization,
  $
    H_1 lr((G,ZZ)) tilde.equiv G slash [G,G], quad
    H_1 lr((N,ZZ)) tilde.equiv N slash [N,N].
  $
  Put $T = N slash [N,N]$, viewed as $overline(G)$-module. For
  $overline(x)-1 in I_overline(G)$, where $x in G$, we have
  $ (overline(x)-1) n = x n x^(-1) n^(-1) = [x,n], quad n in T. $
  Therefore
  $
    H_1 lr((N,ZZ)) slash I_overline(G) dot H_1 lr((N,ZZ))
    tilde.equiv N slash [G,N],
  $
  and we may identify $psi$ with the map $phi$ occurring in Step 1. Thus, we
  need only show that the groups $H_2 lr((overline(G),ZZ))$ and
  $H_1 lr((overline(G),ZZ))$ are finite.

  However, $H_1 lr((overline(G),ZZ)) tilde.equiv
  overline(G) slash [overline(G),overline(G)]$, a finite group. Also we have
  (see Rotman @bib:Rotman1979, Theorem 10.31)
  $
    H_2 lr((overline(G),ZZ)) tilde.equiv H^2 lr((overline(G),QQ slash ZZ))
    tilde.equiv #idx("Schur multiplier") "Schur multiplier of" overline(G),
  $
  which is finite by @i:lem:schur-multiplier-finiteness. This completes the
  proof that the map $phi$ in @eq:full-ideal-relative-whitehead-sequence has
  finite kernel and cokernel.

  _Step 3._ With $r$ as in Step 1, put $I = r Gamma$, $J = r^2 Gamma$, a pair of
  two-sided $Gamma$-ideals in $Lambda$. For each $n$, every matrix in
  $GL_n lr((Lambda,J))$ is $equiv I_n (mod J)$, and so
  $
    GL_n lr((Lambda,J)) = GL_n lr((Gamma,J)), quad
    E_n lr((Lambda,J)) subset.eq E_n lr((Gamma,J)), quad n >= 3.
  $

  #source(169)
  Hence (see @eq:full-ideal-relative-whitehead-sequence) there is a map $sigma$
  giving rise to a commutative diagram
  #full-ideal-relative-comparison
  Since both $phi$ and $phi'$ have finite kernels and cokernels, we need only
  prove that $ker sigma$ is finite, which will imply that $ker theta$ is finite.

  Using the third formula in @eq:steinberg-elementary-relations with $a,b in I$,
  and using the equality $J = I^2$, we obtain from
  @th:bass-relative-elementary-commutators:
  $
    E_n lr((Gamma,J)) subset.eq [E_n lr((Gamma,I)),E_n lr((Gamma,I))]
    subset.eq [GL_n lr((Gamma,I)),GL_n lr((Gamma,I))] \
    = [GL_n lr((Lambda,I)),GL_n lr((Lambda,I))]
    subset.eq E_n lr((Lambda,I)) subset.eq E_n lr((Lambda)).
  $
  Therefore
  $
    ker sigma tilde.equiv E_n lr((Gamma,J)) slash E_n lr((Lambda,J))
    subset.eq E_n lr((Lambda)) slash E_n lr((Lambda,J))
    = [G,G] slash [G,N].
  $
  By Step 2, the quotient $[G,G] slash [G,N]$ is finite, since both $G slash N$
  and $ker phi$ are finite. Thus $ker sigma$ is finite, and the theorem is
  proved.
]

We may now prove the basic result:

#theorem(title: [Bass])[
  Let $Lambda$ be an $R$-order in a f.d. separable $K$-algebra $A$, where $K$ is
  either a global field or its completion at a non-archimedean prime. Then
  $S K_1 lr((Lambda))$ is a finite abelian group.
] <th:bass-sk1-finiteness>
#idx("Bass Theorem", "on SK₁", target: [@th:bass-sk1-finiteness])

#proof[
  Let $Lambda'$ be a maximal $R$-order in $A$ containing $Lambda$. There is a
  commutative diagram
  #sk1-finiteness-comparison
  so $ker theta' = ker theta$. But $ker theta$ is finite by the preceding
  theorem, while $S K_1 lr((Lambda'))$ is finite by §@ss:sk1-maximal-orders.
  Therefore $S K_1 lr((Lambda))$ is also finite.
]

The _rank_ of the abelian group $K_1 lr((Lambda))$ is defined as
$dim_QQ lr((QQ times.o_ZZ K_1 lr((Lambda))))$. We obtain at once:

#theorem(title: [Bass @bib:Bass1966#ed-note[
    The original bibliography has no entry for Bass @bib:Bass1966. The 1966
    article supplied here is the likely intended reference.
  ]])[
  Let $A$ be a f.d. semisimple $QQ$-algebra, and let $Lambda$ be a $ZZ$-order in
  $A$. Then
  #enum(
    numbering: "(i)",
    [#source(170)
      The rank of $K_1 lr((Lambda))$ equals $r-q$, where $q$ is the number of
      Wedderburn components of $A$, and $r$ the number of Wedderburn components
      of $RR times.o_QQ A$.],
    [Let $Lambda = ZZ G$, where $G$ is a finite group. Then
      $rank K_1 lr((Lambda)) = r-q$, where $r$ is the number of nonisomorphic
      simple $RR G$-modules, and $q$ the corresponding number of
      $QQ G$-modules.],
  )
] <th:bass-order-whitehead-rank>
#idx("Bass Theorem", "on rank of K₁", target: [@th:bass-order-whitehead-rank])

#proof[
  By @th:order-inclusion-whitehead-finite-kernel-cokernel,
  $ rank K_1 lr((Lambda)) = rank K_1 lr((Lambda')), $
  where $Lambda'$ is a maximal $ZZ$-order in $A$ containing $Lambda$. Let $C$ be
  the center of $A$, and $frak(O)$ the integral closure of $ZZ$ in $C$. Then we
  may write
  $
    C = product_(i=1)^q F_i, quad frak(O) = product_(i=1)^q R_i,
    quad R_i = "alg. int." lr({F_i}),
  $
  where $F_i$ is the center of the $i$-th Wedderburn component of $A$. By
  @th:maximal-order-whitehead-norm-image and @th:bass-sk1-finiteness,
  $
    rank K_1 lr((Lambda')) = rank(frak(O)^dot inter C^+)
    = rank frak(O)^dot = sum_(i=1)^q rank R_i^dot.
  $
  Let $n_i$ be the number of infinite primes of $F_i$, $1 <= i <= q$. Then
  $RR times.o_QQ F_i$ is a direct sum of $n_i$ fields, each summand being either
  $RR$ or $CC$. It follows that $r = sum_(i=1)^q n_i$. On the other hand,
  $rank R_i^dot = n_i-1$ by the Dirichlet Unit Theorem (see Weiss
  @bib:Weiss1963, Theorem 5.3.10, for example). Thus
  $ rank K_1 lr((Lambda')) = sum_(i=1)^q (n_i-1) = r-q, $
  which establishes (i). Assertion (ii) is a special case of (i).
]

We shall now give C. T. C. Wall’s proof of the $p$-adic version of
@th:bass-sk1-finiteness (see Wall @bib:Wall1973, Kuku @bib:Kuku1976). The
methods used will be needed for a finer investigation of the structure of
$K_1 lr((Lambda))$ and $S K_1 lr((Lambda))$. The proof uses some easy facts
about topological groups, and relies on a theorem of Borel about subgroups of
$SL_n lr((A))$, rather than on the Injective Stability Theorem and relative
$K$-theory.

#theorem[
  Let $K$ be a finite extension of the $p$-adic field $QQ_p$, $R$ its d.v.r.,
  and let $Lambda$ be an $R$-order in a f.d. semisimple $K$-algebra $A$. Then
  $S K_1 lr((Lambda))$ is finite.
] <th:wall-p-adic-sk1-finiteness>
#idx("Wall's Theorem", target: [@th:wall-p-adic-sk1-finiteness])

#proof[
  Let $n >= 2$, and topologize both the group $GL_n lr((A))$, and its subgroup
  $GL_n lr((Lambda))$, by choosing as basis for the open neighborhoods of $1$
  the normal subgroups $lr({1+p^k M_n lr((Lambda)): k = 1,2,dots})$. Note that
  $ 1+p^k M_n lr((Lambda)) = lr({1+x: x in p^k M_n lr((Lambda))}), $
  by definition.

  #source(171)
  The center $C$ of $A$ is a direct sum of $p$-adic fields, and so $C^dot$ may
  be topologized in a similar manner.

  The reduced norm $op("nr")_(A slash C)$ induces a continuous homomorphism of
  topological groups
  $ op("nr"): GL_n lr((A)) -> C^dot, $
  whose kernel $SL_n lr((A))$ is a closed normal subgroup of $GL_n lr((A))$. We
  have
  $
    SL_n lr((A)) = [GL_n lr((A)),GL_n lr((A))], quad
    K_1 lr((A)) = GL_n lr((A)) slash SL_n lr((A))
  $
  by §@ss:reduced-norms. Then $K_1 lr((A))$ is a topological group, with the
  topology induced from that of $GL_n lr((A))$.

  The homomorphism $theta$ defined by composition of maps
  $ GL_n lr((Lambda)) -> GL_n lr((A)) -> K_1 lr((A)) $
  is also a continuous map. Set
  $ W_n = ker theta = GL_n lr((Lambda)) inter SL_n lr((A)). $
  Then there is a commutative diagram with exact rows:
  #wall-compact-kernel-comparison
  Clearly $ker alpha subset.eq ker beta subset.eq ker theta$, so we have
  $ker alpha = ker beta$. Furthermore, since $beta$ is surjective, so is
  $alpha$.

  Now $SL_n lr((A))$ is a closed subgroup of $GL_n lr((A))$, and
  $GL_n lr((Lambda))$ is a compact open subgroup of $GL_n lr((A))$, so $W_n$ is
  a compact open subgroup of $SL_n lr((A))$. By a theorem#footnote[
    This uses the hypothesis $n >= 2$.
  ] of Borel (the proof is given in the article by Riehm @bib:Riehm1970), every
  noncentral normal subgroup of an open subgroup of $SL_N lr((D))$ is open,
  where $D$ is a finite-dimensional division algebra over a $p$-adic field and
  $N >= 2$. Write $A = product_i A_i$, where $A_i = M_(k_i) lr((D_i))$, and let
  $e_i$ be the corresponding central idempotents. Put $H = ker beta$, and view
  each $SL_n lr((A_i)) tilde.equiv SL_(n k_i) lr((D_i))$ as a factor of
  $SL_n lr((A))$. Then $U_i = GL_n lr((Lambda)) inter SL_n lr((A_i))$ is open in
  this factor, and $H_i = H inter SL_n lr((A_i))$ is normal in $U_i$. Choose
  $0 != c in R$ with $c e_i in Lambda$. The elementary matrix
  $E_(1 2) lr((c e_i))$ lies in $H_i$ and does not commute with
  $E_(2 1) lr((c e_i)) in U_i$, so $H_i$ is noncentral. Since $n k_i >= 2$,
  Borel's theorem shows that each $H_i$ is open. Their product is contained in
  $H$, so $ker alpha = H$ is open in $SL_n lr((A))$,#ed-note[
    For a product algebra, overall noncentrality does not suffice: in
    $SL_2 lr((ZZ_p)) times SL_2 lr((ZZ_p))$, the first factor is normal and
    noncentral but is not open. Wall @bib:Wall1973, Theorem~9, uses openness of
    the commutator subgroup in the semisimple case.
  ] and is therefore also open in $W_n$. This implies that $W_n slash ker alpha$
  is a discrete group. On the other hand, since $ker alpha$ is open in $W_n$, it
  is also closed in $W_n$. Since $W_n$ is compact, therefore so is
  $W_n slash ker alpha$. But then
  $S K_1 lr((Lambda)) tilde.equiv W_n slash ker alpha$ is a compact discrete
  group, and must therefore be finite.
]
#idx("Borel's Theorem", target: [@th:wall-p-adic-sk1-finiteness])

#corollary[
  Let $n >= 2$, and let $beta: GL_n lr((Lambda)) -> K_1 lr((Lambda))$. Then
  $ker beta$ is a closed normal subgroup of $GL_n lr((Lambda))$.
] <cor:p-adic-whitehead-kernel-closed>
#proof[
  Using the notation of the preceding proof, we have shown that $ker beta$ is
  open (and hence closed) in $W_n$. But $W_n$ is the kernel of the continuous
  homomorphism $theta$, so $W_n$ is closed in $GL_n lr((Lambda))$. Therefore
  $ker beta$ is closed in $GL_n lr((Lambda))$.
]

#source(172)
=== Profinite Groups <ss:sk1-profinite-groups>

We shall give here a brief summary of the theory of profinite groups; for more
details, see the article by Gruenberg (Chapter V of Cassels–Fröhlich
@bib:Cassels1967), and also Ribes @bib:Ribes1970. Topological background is
given in Eilenberg–Steenrod @bib:Eilenberg1952 and Pontrjagin
@bib:Pontrjagin1939, while results on inverse limits can be found in Rotman
@bib:Rotman1979. Some of the ideas in this subsection will be needed for a finer
discussion of $K_1$ and $S K_1$ of $p$-adic orders, and also in
§@sec:class-groups-integral-group-rings on locally free class groups.

#definition[
  An _inverse system_ of groups $lr({G_i})$ and homomorphisms $lr({phi_(j i)})$,
  where
  $ phi_(j i): G_j -> G_i, quad "for" 1 <= i <= j, $
  is a collection of groups and homomorphisms such that
  $
    phi_(i i) = 1 quad "for all" i, quad
    phi_(j i) phi_(k j) = phi_(k i) quad "for" 1 <= i <= j <= k.
  $
  An element $⟨ x_1,x_2,dots ⟩ in product_(i=1)^infinity G_i$ is _coherent_ if
  $ phi_(j i) lr((x_j)) = x_i quad "for" 1 <= i <= j. $
  The set $G$, consisting of all coherent elements of the direct product
  $product_(i=1)^infinity G_i$, is a subgroup of $product G_i$, called the
  _inverse limit_ (or _projective limit_) of the inverse system. We write
  $ G = limits(lim)_arrow.l G_i. $
  There is a canonical projection $pi_i: G -> G_i$, mapping each element of $G$
  onto its $i$-th coordinate. As shown in Exercise
  @exc:inverse-limit-universal-property, the inverse limit may be characterized
  in terms of a universal mapping property.
] <def:inverse-system-limit>
#idx("Inverse system", target: [@def:inverse-system-limit])
#idx("Inverse limit", target: [@def:inverse-system-limit])
#idx("Projective limit", target: [@def:inverse-system-limit])
#idx("Coherent", target: [@def:inverse-system-limit])

#remarks(numbered: false)[
  It is sometimes more convenient to partially order the integers by
  divisibility, rather than by size. In this situation, an inverse system
  $lr({G_i,phi_(j i)})$ consists of groups and homomorphisms $lr({phi_(j i)})$
  for $i$ dividing $j$, satisfying obvious compatibility requirements.

  More generally, let $I$ be any directed set with respect to an order relation
  $prec$ (which is transitive and reflexive). This means that for any
  $i,j in I$, there exists $k in I$ such that $i prec k$ and $j prec k$. We can
  then define $limits(lim)_arrow.l$ in the same way as above.
] <rem:directed-inverse-systems>

Suppose now that each $G_i$ is a Hausdorff topological group (see
Eilenberg–Steenrod @bib:Eilenberg1952), and that for $i <= j$,
$phi_(j i): G_j -> G_i$ is a continuous surjection. Then
$G = limits(lim)_arrow.l G_i$ is also a topological group, whose topology is
given as follows: the direct product $product_(i=1)^infinity G_i$ has a _product
topology_, in which a fundamental system of neighborhoods of $1$ in
$product G_i$ is given by all products $product N_i$, where $N_i = G_i$ a.e.
(almost everywhere, that is, for all but a finite number of subscripts $i$), and
where for those exceptional values of $i$, $N_i$ is a neighborhood of $1$ in
$G_i$. If each $G_i$ is compact, then so is $product G_i$ in the product
topology.
#idx("Product topology")

#source(173)
Let $G = limits(lim)_arrow.l G_i$; then $G$ is a closed subgroup of
$product G_i$, and $G$ inherits a topology from $product G_i$, namely, the open
sets in $G$ are given by $lr({G inter U: U = "open set in" product G_i})$. If
each $G_i$ is compact, then since $G$ is closed in $product G_i$, the group $G$
is also compact.

#definition[
  A _profinite group_ is a projective limit
  $ G = limits(lim)_arrow.l G_i $
  of an inverse system of discrete finite groups $lr({G_i})$. (If $p$ is a prime
  and each $G_i$ is a finite $p$-group, we call $G$ a _pro-$p$-group_.)
] <def:profinite-pro-p-group>
#idx("Profinite group", target: [@def:profinite-pro-p-group])
#idx("Pro-p-group", target: [@def:profinite-pro-p-group])

Let $pi_i: G -> G_i$ be the canonical projection map, and put $U_i = ker pi_i$.
Then the $lr({U_i})$ are a basis for the neighborhoods of $1$ in $G$, and are
open normal subgroups of $G$. It is easily seen that
$G = limits(lim)_arrow.l G slash U_i$. In fact, there is no loss of generality
in assuming each $phi_(j i)$ surjective, since otherwise we may replace $G_i$ by
$inter.big_(j >= i) im phi_(j i)$. But then each $pi_i$ is surjective, and
$G slash U_i tilde.equiv G_i$. We note that the profinite group $G$ is compact,
since each $G_i$ is compact. (It can be shown that a topological group $G$ is
profinite if and only if $G$ is Hausdorff, compact, and totally disconnected
(see Gruenberg, loc. cit.).)

#example(numbered: false)[
  Let $R$ be a complete d.v.r. with maximal ideal $P$, and finite residue class
  field $R slash P$. Let $G_i = R slash P^i$, $i >= 1$, and let $phi_(j i)$ be
  the canonical surjection $G_j -> G_i$ for $j >= i$. A coherent element
  $⟨ x_1,x_2,dots ⟩$ is a sequence of elements of $R$, with $x_i$ unique mod
  $P^i$, such that
  $ x_(i+1) equiv x_i (mod P^i), quad i >= 1. $
  Such a coherent element defines a unique element of $R$, since $R$ is complete
  in the $P$-adic topology. Conversely, each $y in R$ yields a coherent element
  $⟨ y_1,y_2,dots ⟩$, where $y_i$ is the image of $y$ in $G_i$. Thus we have
  $ R = limits(lim)_arrow.l R slash P^i. $
  Further, the additive subgroups $lr({P^i})$ are a basis for the neighborhoods
  of $0$ in $R$, so the $P$-adic and profinite topologies of $R$ are the same.
] <exm:complete-dvr-profinite-limit>

Suppose now that $G = limits(lim)_arrow.l G_i$ is any profinite group. Each open
subgroup $U$ of $G$ contains a subgroup $U_i$ for some $i$, where
$U_i = ker pi_i$, and so the index $|G:U|$ is necessarily finite. Further, the
coset decomposition $G = union.big_i (x_i U)$ shows that the complement of $U$
in $G$ is open, so $U$ must be closed in $G$. Let $lr({H_j})$ be the collection
of open normal subgroups of $G$, partially ordered by reverse inclusion:
$j <= k$ whenever $H_j supset.eq H_k$. For $j <= k$, there is a natural
surjection $G slash H_k -> G slash H_j$. Then we have:

#proposition[
  Let $lr({H_j})$ be the collection of all open normal subgroups of $G$, ordered
  by reverse inclusion. Then there is an isomorphism of topological groups
  #source(174)
  $ G = limits(lim)_arrow.l G slash H_j, $
  and each $H_j$ is a closed subgroup of $G$ of finite index.
] <prop:profinite-all-open-normal-limit>

For the proof of the above, and also for that of
@prop:profinite-closed-subgroup-quotient below, see Gruenberg, loc. cit.
Further, we have:

#proposition[
  Let $H$ be any closed subgroup of a profinite group $G$, and let $U$ range
  over all open normal subgroups of $G$ of finite index. Then
  #enum(
    numbering: "(i)",
    [$H$ is profinite, and
      $ H tilde.equiv limits(lim)_arrow.l H slash (H inter U). $],
    [If $H ⊴ G$, then
      $ G slash H tilde.equiv limits(lim)_arrow.l G slash H U $
      is profinite.],
  )
] <prop:profinite-closed-subgroup-quotient>

In the above, we can replace the system $lr({U})$ by the system $lr({U_i})$,
where $U_i = ker pi_i$.

We now give some more examples of profinite groups.

#example[
  Let
  $ hat(ZZ) = limits(lim)_arrow.l ZZ slash n ZZ, $
  where the set of subgroups $lr({n ZZ: n >= 1})$ is ordered by reverse
  inclusion. Then $hat(ZZ)$ is the _profinite completion_ of $ZZ$, and there is
  an isomorphism
  $ hat(ZZ) tilde.equiv product_p ZZ_p, $
  where $p$ ranges over all primes, and $ZZ_p$ is the ring of $p$-adic integers.
  Note that
  $ ZZ_p = limits(lim)_arrow.l ZZ slash p^i ZZ $
  is a pro-$p$-group.
] <exm:profinite-integers>
#idx("Profinite completion", target: [@exm:profinite-integers])

#example[
  Let $R$ be a complete d.v.r. with maximal ideal $P$ and finite residue class
  field $overline(R)$ of characteristic $p$. Let $Lambda$ be an $R$-order, and
  put $J = rad Lambda$, so $Lambda slash J$ is a f.d. semisimple
  $overline(R)$-algebra, and is therefore a finite $p$-group. By
  @i:th:complete-ring-idempotent-decompositions, $Lambda$ is complete in the
  $J$-adic topology, so
  $ Lambda = limits(lim)_arrow.l Lambda slash J^n. $

  #source(175)
  For each $n$, there is a filtration
  $
    Lambda slash J^n supset.eq J slash J^n supset.eq J^2 slash J^n
    supset.eq dots
  $
  whose factors $J^i slash J^(i+1)$ are $(Lambda slash J)$-modules, and are thus
  finite $p$-groups. This shows that each $Lambda slash J^n$ is a $p$-group, and
  so $Lambda$ is a pro-$p$-group.

  Now put
  $ 1+J^n = lr({1+x: x in J^n}), quad n >= 1, $
  a subgroup of the group of units $Lambda^dot$ of $Lambda$. We topologize
  $Lambda^dot$ by choosing the groups $lr({1+J^n})$ as basis for the
  neighborhoods of $1$ in $Lambda^dot$. Then $Lambda^dot$ is complete in this
  topology (since $Lambda$ is complete in the $J$-adic topology), and we have
  $ Lambda^dot = limits(lim)_arrow.l Lambda^dot slash (1+J^n). $
  Further,
  $ 1+J = limits(lim)_arrow.l (1+J) slash (1+J^n). $
  Now for each $n$ there is a chain
  $ (1+J) slash (1+J^n) supset.eq (1+J^2) slash (1+J^n) supset.eq dots, $
  with factors $(1+J^i) slash (1+J^(i+1))$. However, there is an isomorphism
  $ (1+J^i) slash (1+J^(i+1)) tilde.equiv J^i slash J^(i+1) $
  where the left-hand side is a multiplicative group, the right-hand side an
  additive group. Thus $(1+J) slash (1+J^n)$ is a finite $p$-group, so $1+J$ is
  a pro-$p$-group.
] <exm:adic-order-pro-p-groups>

#example[
  Let $K subset N$ be fields, with $N$ a Galois extension of $K$, that is, $N$
  is an algebraic extension of $K$ which is the splitting field of a set of
  separable polynomials over $K$. We do not assume $dim_K N$ finite. Let
  $op("Gal")(N slash K)$ be the Galois group of $N slash K$, that is, the group
  of $K$-automorphisms of $N$. We show that $op("Gal")(N slash K)$ is a
  profinite group.

  Let $lr({L_i})$ range over all fields with $K subset.eq L_i subset.eq N$,
  $L_i slash K$ finite Galois, and put $G_i = op("Gal")(L_i slash K)$. Partially
  order the fields $lr({L_i})$ by inclusion, so for $L_i subset.eq L_j$ there is
  a natural surjection $G_j -> G_i$. Each $sigma in G$ is uniquely determined by
  its restrictions $sigma|_(L_i) in G_i$ for all $i$, and $sigma$ determines a
  coherent element $⟨ sigma|_(L_i) ⟩ in product_i G_i$. Conversely, each
  coherent element $⟨ sigma_i ⟩ in product G_i$ determines a unique
  $sigma in G$, so we have
  $ G = limits(lim)_arrow.l G_i. $
  The kernel $H_i$ of the surjection $G -> G_i$ is given by
  $ H_i = op("Gal")(N slash L_i), $

  #source(176)
  for each $i$. These $lr({H_i})$ form a basis for the neighborhoods of $1$ in
  the profinite group $G$.

  Each open subgroup $U$ of $G$ contains some $H_i$, and its fixed field $N^U$
  is then a subfield of $L_i$. We have
  $ |G:U| = dim_K N^U, $
  so $|G:U|$ is finite. Conversely, given any finite extension $L slash K$,
  $L subset.eq N$, not necessarily Galois, let $U = op("Gal")(N slash L)$. Then
  $U$ is an open subgroup of $G$ (of finite index). The normal open subgroups of
  $G$ are precisely the groups $lr({H_i})$.

  We quote without proof the following result, which shows the significance of
  the topological structure of the profinite group $op("Gal")(N slash K)$:
] <exm:infinite-galois-profinite-group>
#idx("Profinite group", target: [@exm:infinite-galois-profinite-group])
#idx("Galois group (infinite)", target: [@exm:infinite-galois-profinite-group])

#theorem(name: "Krull’s Theorem", numbered: false)[
  Let $N slash K$ be a Galois extension. Then there is a lattice antiisomorphism
  $H <-> L$ between the set of closed subgroups $H$ of the profinite group
  $op("Gal")(N slash K)$, and the set of fields $L$ with
  $K subset.eq L subset.eq N$. The correspondence is given by
  $
    L = "subfield of" N "fixed by" H, quad "and"
    H = op("Gal")(N slash L).
  $
] <th:krull-infinite-galois-correspondence>
#idx("Krull's Theorem", target: [@th:krull-infinite-galois-correspondence])

We shall conclude this subsection with a result of Wall’s on $K_1$ of $p$-adic
orders, which will be needed for the discussion of Whitehead groups in
§@sec:whitehead-integral-group-rings.

#theorem[
  Let $R$ be a complete d.v.r. with maximal ideal $P$ and finite residue class
  field $overline(R)$ of characteristic $p$. Let $Lambda$ be an $R$-order, and
  put $overline(Lambda) = Lambda slash J$, where $J = rad Lambda$. Then there is
  an exact sequence
  $ 1 -> V -> K_1 lr((Lambda)) -> K_1 lr((overline(Lambda))) -> 1, $
  <eq:order-whitehead-residue-pro-p-sequence>
  in which $V$ is a pro-$p$-group and $K_1 lr((overline(Lambda)))$ is a finite
  group of order prime to $p$. The sequence has a canonical splitting, so
  $ K_1 lr((Lambda)) tilde.equiv V times K_1 lr((overline(Lambda))). $
] <th:wall-whitehead-pro-p-splitting>

#proof[
  Since $overline(R)$ is finite, we may write
  $
    overline(Lambda) = product.co_i M_(n_i) lr((F_i)), quad
    F_i = "finite field extension of" overline(R).
  $
  Then
  $
    K_1 lr((overline(Lambda))) tilde.equiv product_i K_1 lr((F_i))
    tilde.equiv product_i F_i^dot.
  $
  Each $F_i^dot$ is a finite group of order prime to $p$, so the same is true of
  $K_1 lr((overline(Lambda)))$.

  Now let $Gamma = M_3 lr((Lambda))$, so $rad Gamma = M_3 lr((J))$, and we set
  $overline(Gamma) = Gamma slash rad Gamma tilde.equiv
  M_3 lr((overline(Lambda)))$. There is a commutative diagram with exact rows:
  #wall-residue-splitting-comparison

  #source(177)
  in which $beta,gamma$ and $delta$ are surjective, and $V = ker lambda$. (Since
  $lambda beta = delta gamma$, $lambda$ is also surjective. The map $psi$ is
  induced by $beta$.)

  Next, we have
  $
    ker beta supset.eq [Gamma^dot,Gamma^dot], quad
    ker delta = [overline(Gamma)^dot,overline(Gamma)^dot],
  $
  so $gamma$ maps $ker beta$ onto $ker delta$. The Snake Lemma then shows that
  $psi$ is surjective, so now
  $ V tilde.equiv (1+rad Gamma) slash ker psi. $
  From @exm:adic-order-pro-p-groups, $1+rad Gamma$ is an open (and closed)
  subgroup of the profinite group $Gamma^dot$, and is itself a pro-$p$-group.
  Let $pi$ be a prime element of $R$. The ring $Lambda$ is complete for the
  powers of $pi Lambda$, and each $Lambda slash pi^m Lambda$ is finite of
  $p$-power order. By de Frutos-Fernández, Macías Castillo and Martínez Marqués
  @bib:deFrutosFernandez2026, Proposition~4.4, the canonical map
  $ K_1 lr((Lambda)) -> limits(lim)_arrow.l K_1 lr((Lambda slash pi^m Lambda)) $
  is injective. Hence $ker beta$ is the intersection of the kernels of the
  finite reduction maps, and is closed in $Gamma^dot$.#ed-note[
    With $Gamma = M_2 lr((Lambda))$ and $overline(Lambda) = FF_2$, the printed
    commutator assertion fails: $GL_2 lr((FF_2)) tilde.equiv S_3$ has commutator
    subgroup $A_3$, whereas $K_1 lr((FF_2)) = 1$. The preceding
    characteristic-zero argument does not cover a general complete d.v.r.; the
    continuity result @bib:deFrutosFernandez2026, Proposition~4.4, supplies the
    needed closedness.
  ] Since
  $ ker psi = (ker beta) inter (1+rad Gamma), $
  it follows that $ker psi$ is a closed normal subgroup of $1+rad Gamma$.
  Therefore $V$ is a pro-$p$-group by @prop:profinite-closed-subgroup-quotient
  (ii). We leave it as an exercise to deduce that the sequence
  @eq:order-whitehead-residue-pro-p-sequence has a canonical splitting (see
  Exercise @exc:canonical-pro-p-splitting).
]

#exercises-heading

#exercise[
  Let $K$ be a global field, $R$ a Dedekind domain with quotient field $K$, and
  let $A$ be a f.d. simple $K$-algebra with center $F$. Let $S$ be the integral
  closure of $R$ in $F$. Prove that $A$ satisfies the Eichler condition
  @def:eichler-condition relative to $R$ if and only if $A$ satisfies the
  Eichler condition relative to $S$.
  #hint([@exc:eichler-condition-center-extension])[
    Every $P$-adic valuation of $K$ arising from a maximal ideal of $R$ extends
    to a $Q$-adic valuation of $F$ arising from a maximal ideal of $S$. Thus,
    the non-$R$ primes $P$ of $K$ extend to non-$S$ primes $Q$ of $F$, with
    $Q|_K = P$. Let $lr({Q_i})$ be the set of all primes of $F$ which extend a
    given non-$R$ prime $P$ of $K$. Then
    $ K_P times.o_K F = F_P tilde.equiv product.co_i F_(Q_i), $
    so
    $
      A_P = K_P times.o_K A tilde.equiv (K_P times.o_K F) times.o_F A
      tilde.equiv product.co_i A_(Q_i).
    $
    Thus, the Wedderburn components of $A_P$ are the central simple
    $F_(Q_i)$-algebras $A_(Q_i)$.
  ]
] <exc:eichler-condition-center-extension>

#exercise[
  Let $R$ be a complete d.v.r. with quotient field $K$ and finite residue class
  field $overline(R)$. Let $Lambda$ be a maximal order in a central simple
  $K$-algebra $A$. Then show that $op("nr")_(A slash K) lr((Lambda)) = R$.
  #hint([@exc:local-maximal-order-all-norms])[
    Using the notation in the proof of @prop:local-maximal-order-unit-norm, let
    $pi_D$ be a prime element of $Delta$. Show that
    $op("nr")_(D slash K) pi_D = plus.minus pi$, where $pi$ is a prime element
    of $R$. Thus $op("nr") Delta$ contains $plus.minus pi$ and $R^dot$, by
    @prop:local-maximal-order-unit-norm.
  ]
] <exc:local-maximal-order-all-norms>

#exercise[
  Using the notation of @th:local-maximal-order-sk1, show that
  $
    S K_1 lr((Delta)) tilde.equiv overline(Delta)^dot slash overline(R)^dot,
    quad S K_1 lr((Delta)) tilde.equiv
    [Delta^dot,D^dot] slash [Delta^dot,Delta^dot], quad
    K_1 lr((Delta)) tilde.equiv Delta^dot slash [Delta^dot,Delta^dot].
  $
] <exc:local-order-sk1-unit-commutators>

#exercise[
  Let $Lambda$ be an $R$-order in a separable $A$. Define $C^+$ as in
  @eq:semisimple-positive-norm-subgroup, and let $frak(O)$ be the integral
  closure of $R$ in $C$.
  #source(178)
  Prove that $op("nr") K_1 lr((Lambda))$ is a subgroup of finite index in
  $frak(O)^dot inter C^+$, and is therefore also of finite index in
  $frak(O)^dot$.
  #hint([@exc:order-norm-image-finite-index])[
    Choose $Gamma$ a maximal order containing $Lambda$, so
    $op("nr") K_1 lr((Gamma)) = frak(O)^dot inter C^+$. If
    $beta: K_1 lr((Lambda)) -> K_1 lr((Gamma))$, then
    $
      op("nr")_(A slash C) lr((op("cok") beta))
      = (frak(O)^dot inter C^+) slash op("nr") K_1 lr((Lambda)).
    $
  ]
] <exc:order-norm-image-finite-index>

#exercise[
  Let $Lambda subset.eq Gamma$ be $R$-orders in a separable $K$-algebra $A$, and
  let $r Gamma subset.eq Lambda$ where $r in R$, $r != 0$. Show that the map
  $K_1 lr((Lambda)) -> K_1 lr((Gamma))$ has finite cokernel, by using the
  Mayer–Vietoris sequence associated with the fiber product
  #order-inclusion-fiber-product
] <exc:order-whitehead-finite-cokernel-mayer-vietoris>

#exercise[
  Let $lr({G_i,phi_(j i)})$ be an inverse system of groups and homomorphisms,
  and let $G = limits(lim)_arrow.l G_i$. Define $pi_i: G -> G_i$ as the
  canonical projection, for each $i$. Show that $G$ satisfies the following
  universal mapping property, which characterizes $G$ up to isomorphism:

  For each group $X$ and each family of homomorphisms $theta_i: X -> G_i$ such
  that $phi_(j i) theta_j = theta_i$ whenever $i <= j$, there is a unique
  homomorphism $theta: X -> G$ for which $theta_i = pi_i theta$ for all $i$.
] <exc:inverse-limit-universal-property>

#exercise[
  Let $lr({M_i,phi_(j i)})$ be an inverse system of $A$-modules and
  $A$-homomorphisms, where $A$ is an arbitrary ring. Prove that for an
  $A$-module $L$,
  $
    limits(lim)_arrow.l Hom_A lr((L,M_i)) tilde.equiv
    Hom_A lr((L,limits(lim)_arrow.l M_i)).
  $
] <exc:hom-commutes-inverse-limits>

#exercise[
  Prove that the inverse limit of an inverse system of profinite groups is again
  a profinite group. Show also that the direct product of profinite groups is
  profinite.
] <exc:limits-products-profinite-groups>

#exercise[
  Show that a finite subgroup of a pro-$p$-group must be a $p$-group. Show that
  any finite quotient group of a pro-$p$-group must be a $p$-group.
  #hint([@exc:finite-pro-p-subgroups-quotients])[
    Let $G = limits(lim)_arrow.l G_i$, where each $G_i$ is a finite $p$-group,
    and let $theta: G -> F$ be a surjection, with $F$ a finite group of order
    $p^k n$, where $p divides.not n$. Each $x in G$ is of the form
    $x = ⟨ x_i ⟩ in product G_i$. For each $i$, there is a unique $y_i in G_i$
    with $x_i = (y_i)^n$. Then $y = ⟨ y_i ⟩$ also lies in $G$, and $x = y^n$.
    Therefore $theta(x) = theta(y)^n$, so the order of $theta(x)$ is a divisor
    of $p^k$. This shows that every element of $F$ has $p$-power order, so
    $n = 1$.
  ]
] <exc:finite-pro-p-subgroups-quotients>

#exercise[
  Let $p$ be prime, and let $1 -> G -> A -> E -> 1$ be an exact sequence of
  abelian groups, in which $G$ is a pro-$p$-group and $E$ is a finite
  $p'$-group. Prove that there is a canonical splitting of this sequence.
  #hint([@exc:canonical-pro-p-splitting])[
    Let
    $ 1 -> G arrow.r^gamma A arrow.r^alpha E -> 1 $
    be an exact sequence of abelian groups, where $G$ is a pro-$p$-group and $E$
    is a finite $p'$-group. There is a unique homomorphism $phi: A -> G$ which
    splits $gamma$. To construct $phi$, suppose first that $G$ is a finite
    $p$-group, and let $e = |E|$, so $p divides.not e$. Choose $n in ZZ$ with
    $ n equiv 0 (mod e), quad n equiv 1 (mod |G|). $

    #source(179)
    Then for $a in A$, there is a unique $g in G$ with $a^n = gamma(g)$, and we
    define $phi(a) = g$. It is easily checked that $phi gamma = id_G$, and that
    $phi$ is independent of the choice of $n$, and finally that $phi$ is the
    unique splitting of $gamma$.

    Now let $G = limits(lim)_arrow.l G_i$, where for each $i$ we have
    $G_i = G slash H_i =$ finite $p$-group. Given the above exact sequence, we
    obtain (for each $i$) a commutative diagram of abelian groups, with exact
    rows:
    #canonical-splitting-quotient-comparison
    Then there is a unique $phi_i: A slash H_i -> G slash H_i$ which splits
    $gamma_i$, and we define the required splitting $phi: A -> G$ by the formula
    $ phi(a) = ⟨ phi_i pi_i lr((a)): i = 1,2,dots ⟩. $
  ]
] <exc:canonical-pro-p-splitting>

#exercise[
  Let $R$ be a complete d.v.r. with finite residue class field $overline(R)$.
  Show that the surjection $R^dot -> overline(R)^dot$ has a canonical splitting
  $ t: overline(R)^dot -> R^dot quad "(Teichmüller map)". $
  #hint([@exc:teichmuller-map])[
    If $q = "card" overline(R)$, then $R$ contains $omega$, a primitive
    $(q-1)$-st root of $1$, and the map $⟨ omega ⟩ -> ⟨ overline(omega) ⟩$ is an
    isomorphism, whose inverse is $t$.
  ]
] <exc:teichmuller-map>
#idx("Teichmüller map", target: [@exc:teichmuller-map])

#exercise[
  Show that any homomorphism $Lambda -> Delta$ of commutative rings induces a
  homomorphism of groups
  $ S K_1 lr((Lambda)) -> S K_1 lr((Delta)). $
] <exc:commutative-sk1-functoriality>

#exercise[
  Let $Lambda_i$ be an $R$-order in a separable $K$-algebra $A_i$, $i = 1,2$,
  where $K$ is a global field which is the quotient field of a Dedekind domain
  $R$. Show that any $K$-algebra homomorphism $A_1 -> A_2$, which carries
  $Lambda_1$ into $Lambda_2$, induces a homomorphism
  $ S K_1 lr((Lambda_1)) -> S K_1 lr((Lambda_2)). $
] <exc:order-sk1-functoriality>

#exercise[
  Let $Lambda$ be an $R$-order in a separable $K$-algebra $A$ (as above), and
  let $P$ be any maximal ideal of $R$. Then the inclusion $Lambda -> Lambda_P$
  induces a map $S K_1 lr((Lambda)) -> S K_1 lr((Lambda_P))$.
] <exc:order-sk1-completion-map>
