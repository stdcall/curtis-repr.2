#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/38d-localization.typ": *

=== Localization Sequences <ss:localization-sequences>

We have seen in @i:prop:artinian-grothendieck-simple-basis that when $Lambda$ is
a left artinian ring, the Grothendieck group $G_0 lr((Lambda))$ is a free
$ZZ$-module with basis $[S_1], dots, [S_n]$, where the $lr({S_i})$ are a basic
set of simple left $Lambda$-modules. The situation is much more complicated when
$Lambda$ is a noetherian ring which is not artinian, and one method of
calculating $G_0 lr((Lambda))$ is to reduce the problem to easier cases, by
means of a _localization sequence_.#idx("Localization sequence") The basic ideas
originated with Grothendieck and Gabriel, while the special cases occurring
below are due to Swan and Heller–Reiner.

To begin with, let $R$ be a commutative noetherian ring, and let $Lambda$ be an
$R$-algebra which is f.g. as $R$-module. Since every left ideal of $Lambda$ is
also an $R$-submodule of $Lambda$, it follows at once that $Lambda$ is a
noetherian ring. Now let $S$ be any multiplicative subset of $R$, and let us
form the ring of quotients $R' = S^(-1) R$ (see §@i:ss:localization). Then $R'$
is also a commutative noetherian ring, and by §@i:ss:localization (see also
@bib:Reiner1975[MO (3.8)]), $R'$ is flat as $R$-module (that is,
$R' times.o_R ast$ preserves exactness of sequences of $R$-modules). We now set
$
  Lambda' = R' times.o_R Lambda = S^(-1) Lambda,
  quad "and" M' = S^(-1) M = R' times.o_R M = Lambda' times.o_Lambda M,
$
for any left $Lambda$-module $M$. Then $Lambda'$ is an $R'$-algebra, f.g. as
$R'$-module, and every $Lambda$-module $M$ gives rise to a $Lambda'$-module
$M'$. If $M$ is f.g./$Lambda$, then $M'$ is f.g./$Lambda'$.

#source(48)
Our first localization sequence relates the Grothendieck groups
$G_0 lr((Lambda))$ and $G_0 lr((Lambda'))$. There is an additive homomorphism
$
  phi: G_0 lr((Lambda)) -> G_0 lr((Lambda')),
  quad "given by" phi[M] = [M'],
$
for each f.g. $Lambda$-module $M$, where $M'$ is as above. To see that $phi$ is
well defined, we need only observe that for each ses
$0 -> M_1 -> M_2 -> M_3 -> 0$ of $Lambda$-modules, the corresponding sequence of
$Lambda'$-modules $0 -> M'_1 -> M'_2 -> M'_3 -> 0$ is also exact, since $R'$ is
$R$-flat. We now prove:

#theorem(name: "Localization Sequence", title: [Swan @bib:Swan1963])[
  There exists an exact sequence of additive groups
  $
    G_0^t lr((Lambda)) arrow.r^psi G_0 lr((Lambda))
    arrow.r^phi G_0 lr((Lambda')) -> 0,
  $ <eq:grothendieck-localization-sequence>
  where $G_0^t lr((Lambda))$ is the Grothendieck group of the category of all
  f.g. $S$-torsion#footnote[An $S$-torsion $Lambda$-module $X$ is one such that
    for each $x in X$, we have $s x = 0$ for some $s in S$.] $Lambda$-modules,
  and where $psi$ is defined by $psi[L] = [L]$ for each such module $L$.

  Furthermore, if $R$ is a Dedekind domain,#footnote[In fact,
    @eq:torsion-grothendieck-prime-decomposition holds for rings of Krull
    dimension $<= 1$ (see §@sec:basic-elements-stable-range).] then
  $
    G_0^t lr((Lambda)) tilde.equiv
    product.co_(P, P inter S != emptyset) G_0 lr((Lambda slash P Lambda)),
  $ <eq:torsion-grothendieck-prime-decomposition>
  where $P$ ranges over all prime ideals of $R$ such that $P inter S$ is
  nonempty.
] <th:grothendieck-localization-sequence>
#nidx(
  "$G_0 lr((A)), G_0^R lr((Lambda)), G_0^t lr((Lambda))$",
  "Grothendieck groups",
  target: [@th:grothendieck-localization-sequence],
)
#idx(
  "Swan's Localization Sequence",
  target: [@th:grothendieck-localization-sequence],
)
#idx("Localization sequence", target: [@th:grothendieck-localization-sequence])
#idx("Grothendieck group", target: [@th:grothendieck-localization-sequence])
#proof[
  _Step 1._ If $L$ is any f.g. $S$-torsion $Lambda$-module, then $s L = 0$ for
  some $s in S$. Therefore
  $
    phi psi[L] = [R' times.o_R L]
    = [s^(-1) R' times.o_R s L] = 0,
  $
  so $phi psi = 0$, and $im psi subset.eq ker phi$. Furthermore, the proof of
  @i:prop:localized-module-finite-model remains valid even when $R$ is not a
  domain, and so $phi$ is a surjection.

  The homomorphism $phi: G_0 lr((Lambda)) -> G_0 lr((Lambda'))$ induces a
  homomorphism (also denoted by $phi$)
  $ phi: G_0 lr((Lambda)) slash im psi -> G_0 lr((Lambda')). $
  To prove the exactness of @eq:grothendieck-localization-sequence, we shall
  construct a map $rho: G_0 lr((Lambda')) -> G_0 lr((Lambda)) slash im psi$ for
  which both $rho phi$ and $phi rho$ are the identity maps. Given any
  $Lambda$-module $M$, we shall denote $R' times.o_R M$ by $R' M$, for brevity.
  However, the map $M -> R' M$ given by $m in M -> 1 times.o m in R' M$ is not
  necessarily injective, so we should not identify $M$ with its image
  $1 times.o M$ in $M'$.

  #source(49)
  We proceed to define
  $ rho: G_0 lr((Lambda')) -> G_0 lr((Lambda)) slash im psi, $
  as follows. Each f.g. $Lambda'$-module $X$ may be written as $X = R' M$ for
  some f.g. $Lambda$-module $M$ contained in $X$, by the proof of
  @i:prop:localized-module-finite-model. We set $rho[X] = [M] + im psi$, and
  must verify that $rho$ is a well-defined homomorphism. First, we claim that
  $rho[X]$ is independent of the choice of $M$. For if also $X = R' N$, we
  choose $s in S$ such that $s M subset.eq N$. Since
  $[M] - [s M] = psi[M slash s M] in im psi$, we may replace $M$ by $s M$
  without affecting $[X]$. Changing notation, we may now assume that
  $M subset.eq N subset.eq X$, and $R' M = R' N = X$. Then $R'(N slash M) = 0$.
  Setting $T = N slash M$, we see that $T$ is an $S$-torsion $Lambda$-module,
  and $[N] = [M] + [T]$ in $G_0 lr((Lambda))$. Thus $[M]$ and $[N]$ differ by an
  element in $im psi$, and we have shown that $rho[X]$ is independent of the
  choice of $M$.

  We must also prove that $rho$ preserves the defining relations of
  $G_0 lr((Lambda'))$: that is, given any $Lambda'$-exact sequence
  $ 0 -> X_1 arrow.r^f X_2 arrow.r^g X_3 -> 0, $
  we have $rho[X_2] = rho[X_1] + rho[X_3]$. Let $X_2 = R' M_2$ for some f.g.
  $Lambda$-submodule $M_2$ of $X_2$; then $X_3 = R' dot g(M_2)$, so we have
  $ rho[X_2] = [M_2] + im psi, quad rho[X_3] = [M_3] + im psi, $
  where $M_3 = g(M_2)$. Defining $M_1 = {x in X_1: f(x) in M_2}$, we obtain a
  $Lambda$-exact sequence
  $ 0 -> M_1 arrow.r^f M_2 arrow.r^g M_3 -> 0. $
  Tensoring with $R'$, and using the fact that $R' M_i = X_i$, $i = 2, 3$, we
  obtain the exact sequence
  $ 0 -> R' M_1 arrow.r^f X_2 arrow.r^g X_3 -> 0. $
  Therefore, $X_1 = R' M_1$, and so $rho[X_1] = [M_1] + im psi$. But
  $[M_2] = [M_1] + [M_3]$ in $G_0 lr((Lambda))$, and therefore
  $rho[X_2] = rho[X_1] + rho[X_3]$, as desired. This proves that $rho$ is a
  well-defined homomorphism from $G_0 lr((Lambda'))$ into
  $G_0 lr((Lambda)) slash im psi$. It is clear that $phi rho[X] = [X]$ for each
  $[X] in G_0 lr((Lambda'))$.

  Finally, let $[M] in G_0 lr((Lambda))$, and set $X = R' times.o M = R' N$,
  where $N = 1 times.o M subset.eq X$. Then $phi[M] = [X]$, and
  $rho phi[M] = rho[X] = [N] + im psi$. But there is a $Lambda$-exact sequence
  $ 0 -> M_0 -> M -> N -> 0, $
  where $M_0$ is the kernel of the map $M -> N$, that is, $M_0$ is the
  $S$-torsion submodule of $M$ (see §@i:ss:localization).
  #source(50)
  Therefore $[M] = [N] + [M_0]$, and $[M_0] in im psi$, which proves that
  $rho phi[M] = [M] + im psi$. This completes the proof that
  $G_0 lr((Lambda)) slash im psi tilde.equiv G_0 lr((Lambda'))$, and establishes
  @eq:grothendieck-localization-sequence.

  _Step 2._ In order to prove @eq:torsion-grothendieck-prime-decomposition, let
  $M$ be any f.g. $Lambda$-module. We show that there is a filtration
  $ M = M_n supset M_(n-1) supset dots supset M_1 supset M_0 = 0, $
  <eq:prime-annihilator-filtration>
  where each factor $M_i slash M_(i-1)$ is a cyclic $Lambda$-module whose
  $R$-annihilator is a prime ideal of $R$. We first write
  $M = sum_(i=1)^r Lambda m_i$, and note that $M$ has a filtration
  $
    M = sum_(i=1)^r Lambda m_i supset.eq sum_(i=1)^(r-1) Lambda m_i
    supset.eq dots supset.eq Lambda m_1 supset.eq 0,
  $
  with cyclic factors. We wish to refine this filtration to obtain one of the
  desired type, and so it suffices to prove the result for cyclic
  $Lambda$-modules. If the result is false, let $X = Lambda x$ be a nonzero
  counterexample for which the annihilator ideal $op("ann")_R X$ is as large as
  possible (among all counterexamples $X$). Set $I = op("ann")_R X$, a proper
  ideal of $R$. If $I$ is a prime ideal of $R$, then $X supset 0$ is a
  filtration of $X$ whose factor module $X$ has prime annihilator $I$, contrary
  to assumption. Thus $I$ is not prime, so there exist elements $a, b in R$ with
  $a b in I$, $a in.not I$, $b in.not I$. In the filtration
  $X supset a X supset 0$, the factors are $X slash a X$ and $a X$. Since
  $
    op("ann")_R X slash a X supset.eq I + R a supset I,
    quad op("ann")_R a X supset.eq I + R b supset I,
  $
  neither $X slash a X$ nor $a X$ can be a counterexample. Thus both of them
  have filtrations whose factor modules have prime ideal annihilators. The same
  is therefore true of $X$. This proves that no counterexamples exist, and shows
  that every f.g. $Lambda$-module $M$ has a filtration
  @eq:prime-annihilator-filtration for which, for each $i$,
  $
    op("ann")_R lr((M_i slash M_(i-1))) = P_i = "prime ideal of" R,
    quad 1 <= i <= n.
  $
  Now let $M$ be a f.g. $S$-torsion $Lambda$-module, and let
  @eq:prime-annihilator-filtration be a filtration as above. Since each factor
  $M_i slash M_(i-1)$ is an $S$-torsion module, it follows that
  $P_i inter S != emptyset$ for each $i$. Clearly
  $[M] = sum [M_i slash M_(i-1)]$ in $G_0^t lr((Lambda))$, and the map
  $
    [M] -> sum_(i=1)^n [M_i slash M_(i-1)]
    in product.co_P G_0 lr((Lambda slash P Lambda))
  $
  gives the desired isomorphism @eq:torsion-grothendieck-prime-decomposition.
  Since $R$ is Dedekind, each $P_i$ is maximal, and each factor
  $M_i slash M_(i-1)$ has finite length over $Lambda slash P_i Lambda$. Refining
  these factors by composition series, all their simple factors have
  $R$-annihilator $P_i$. The Jordan–Hölder Theorem shows that the proposed map
  is independent of the filtration. Concatenating composition series in a ses
  shows that it preserves the defining relations of $G_0^t lr((Lambda))$; the
  inclusions of the categories of $Lambda slash P Lambda$-modules give its
  inverse.#ed-note[
    The printed factors need not be simple: for $R = ZZ$ and
    $Lambda = ZZ[epsilon] slash (epsilon^2)$, the cyclic module
    $Lambda slash p Lambda$ has $R$-annihilator $p ZZ$ but has the proper
    nonzero submodule $epsilon(Lambda slash p Lambda)$, for every prime $p$.
  ] This completes the proof of Theorem @th:grothendieck-localization-sequence
  (See also Exercise @exc:central-localization-sequence).
]

#source(51)
For the remainder of this section, let $R$ be a Dedekind domain with quotient
field $K$. We recall from §@i:sec:lattices-orders that an $R$-order is an
$R$-algebra $Lambda$ which is f.g. and projective as $R$-module.#idx("Order")
For such an $R$-order $Lambda$, we set $A = K times.o_R Lambda$. Since $R$ is a
domain and $Lambda$ is $R$-torsionfree, we may identify $Lambda$ with its image
$1 times.o Lambda$ in $A$. Then we may write $A = K Lambda$, viewed as the
algebra of $K$-linear combinations of the elements of the $R$-algebra $Lambda$.
Our aim here is to calculate the Grothendieck group $G_0 lr((Lambda))$, and for
this purpose we shall extend the Localization Sequence
@eq:grothendieck-localization-sequence to the left, by means of an additional
term $K_1 lr((A))$, the Whitehead group of $A$ defined in
@def:whitehead-determinantal-group.

Let us first review some ideas from the theory of orders. For each $R$-module
$M$, there is an $R$-homomorphism $M -> K times.o_R M$ given by
$m -> 1 times.o m$, $m in M$, whose kernel is the $R$-torsion submodule of $M$.
If $M$ is $R$-torsionfree, this map is an embedding, and we identify $M$ with
its image $1 times.o M$ in $K times.o_R M$; the latter can then be written as
$K M$.

As in §@i:sec:lattices-orders, a $Lambda$-lattice is a left $Lambda$-module $M$
which is f.g. and projective as $R$-module (or equivalently, f.g. and
torsionfree as $R$-module). For each $Lambda$-lattice $M$, $K M$ is an f.g.
$A$-module; conversely, every f.g. $A$-module $V$ contains $Lambda$-lattices $M$
for which $K M = V$, and we call $M$ a _full $Lambda$-lattice_ in $V$.#idx(
  "Full sublattice",
)

Now let $Lambda$ be an $R$-order in an f.d. $K$-algebra $A$. Since
$K = S^(-1) R$, where $S$ is the multiplicative set $R - {0}$, the Localization
Sequence @eq:grothendieck-localization-sequence becomes
$
  G_0^t lr((Lambda)) arrow.r^psi G_0 lr((Lambda))
  arrow.r^phi G_0 lr((A)) -> 0.
$
Here, $G_0^t lr((Lambda))$ is the Grothendieck group of the category of f.g.
$R$-torsion $Lambda$-modules. By @eq:torsion-grothendieck-prime-decomposition,
we have
$ G_0^t lr((Lambda)) tilde.equiv product.co_P G_0 lr((Lambda slash P Lambda)), $
<eq:order-torsion-grothendieck-decomposition>
where $P$ ranges over all nonzero prime ideals of $R$.

We are now ready to give a longer localization sequence, due to Heller–Reiner
@bib:Heller1964, @bib:Heller1965:

#theorem[
  Let $R$ be a Dedekind domain with quotient field $K$, and let $Lambda$ be an
  $R$-order in a f.d. semisimple $K$-algebra $A$. There is an exact sequence of
  groups
  $
    K_1 lr((A)) arrow.r^delta G_0^t lr((Lambda)) arrow.r^psi
    G_0 lr((Lambda)) arrow.r^phi G_0 lr((A)) -> 0.
  $ <eq:heller-reiner-localization-sequence>
] <th:heller-reiner-localization>
#idx(
  "Heller-Reiner Localization Sequence",
  target: [@th:heller-reiner-localization],
)
#idx("Localization sequence", target: [@th:heller-reiner-localization])
#proof[
  _Step 1._ The preceding discussion shows that we need only define the
  homomorphism $delta$, and prove that $im delta = ker psi$. As a preliminary
  step, we carry out some elementary manipulations with $Lambda$-lattices. Let
  $M$ and $N$ be $Lambda$-lattices for which $K M = K N$. Then $M inter N$ is a
  full $Lambda$-lattice in $K M$, and $M slash (M inter N)$ is an $R$-torsion
  $Lambda$-module. We now define
  $
    [M slash slash N] = [M slash (M inter N)] - [N slash (M inter N)]
    in G_0^t lr((Lambda)).
  $
  #source(52)
  If $L$ is another $Lambda$-lattice for which $K L = K M$, we show that
  $
    [L slash slash M] + [M slash slash N] = [L slash slash N]
    quad "in" G_0^t lr((Lambda)).
  $ <eq:lattice-relative-class-transitivity>
  To see this, let $T = L inter M inter N$; from the exact sequence
  $ 0 -> (M inter N) slash T -> M slash T -> M slash (M inter N) -> 0, $
  and the corresponding ses with $M$ and $N$ interchanged, we obtain
  $[M slash slash N] = [M slash T] - [N slash T]$. Corresponding formulas hold
  with $M$ replaced by $L$, and so on, which gives
  @eq:lattice-relative-class-transitivity at once.

  Next, suppose we are given a diagram of $Lambda$-lattices
  #lattice-comparison
  in which each row is exact, and where the dotted arrows denote
  $A$-isomorphisms $K L_1 tilde.equiv K L_2$, etc., which commute with the
  horizontal maps $K L_i -> K M_i$, etc. Set
  $
    I_L = L_2 inter lambda L_1, quad I_M = M_2 inter mu M_1,
    quad I_N = N_2 inter nu N_1, quad H = I_N slash g_2 lr((I_M)).
  $
  These intersections are full lattices, so $H$ is an $R$-torsion
  $Lambda$-module. Put $E_2 = g_2^(-1) lr((I_N)) subset.eq M_2$. There are ses’s
  $
    0 -> L_2 slash I_L -> E_2 slash I_M -> H -> 0,
    quad 0 -> E_2 slash I_M -> M_2 slash I_M -> N_2 slash I_N -> 0.
  $
  Therefore, in $G_0^t lr((Lambda))$,
  $
    [M_2 slash I_M] = [L_2 slash I_L] + [N_2 slash I_N] + [H].
  $
  Applying the same argument to the image of the upper row gives
  $
    [mu M_1 slash I_M] = [lambda L_1 slash I_L]
    + [nu N_1 slash I_N] + [H].
  $
  Subtracting these formulas cancels $[H]$.#ed-note[
    The printed short exact sequence of intersection quotients can fail: take
    both rows to be $0 -> ZZ -> ZZ^2 -> ZZ -> 0$, with the first coordinate
    embedding and second coordinate projection, $lambda = nu = 1$ and
    $mu(a, b) = (a + b slash 2,b)$ over $QQ$. Its outer quotients are zero,
    whereas the middle quotient is $ZZ slash 2 ZZ$.
  ] Using @eq:lattice-relative-class-transitivity, we obtain
  $
    [M_2 slash slash mu M_1] = [L_2 slash slash lambda L_1]
    + [N_2 slash slash nu N_1] quad "in" G_0^t lr((Lambda)).
  $ <eq:lattice-relative-class-additivity>

  _Step 2._ We are now ready to construct a map
  $delta: K_1 lr((A)) -> G_0^t lr((Lambda))$. Since $K_1 lr((A))$ is generated
  by ordered pairs $(X, mu)$ with $X in cal(P)(A)$ and $mu in Aut_A X$, we need
  to define $delta(X, mu)$, and to show that this definition preserves the
  defining relations of $K_1 lr((A))$. Given an ordered pair $(X, mu)$, choose
  any full $Lambda$-lattice $M$ in $X$, and set
  $ delta(X, mu) = [M slash slash mu(M)] in G_0^t lr((Lambda)). $

  #source(53)
  If also $X = K N$ for some $Lambda$-lattice $N$, then by
  @eq:lattice-relative-class-transitivity we have
  $
    [M slash slash mu M] - [N slash slash mu N] = [M slash slash N]
    - [mu M slash slash mu N] quad "in" G_0^t lr((Lambda)).
  $
  But $mu$ maps $M$ isomorphically onto $mu M$, and $N$ onto $mu N$, so
  $[M slash slash N] = [mu M slash slash mu N]$ in $G_0^t lr((Lambda))$. This
  readily implies that $delta(X, mu)$ is independent of the choice of the full
  $Lambda$-lattice $M$ in $X$.

  We show next that $delta$ is well-defined on $K_1 lr((A))$. First, let
  $X in cal(P)(A)$ and let $mu, mu' in Aut_A X$. Choosing a full
  $Lambda$-lattice $M$ in $X$, we have
  $
    delta(X, mu mu') & = [M slash slash mu mu' M]
                       = [M slash slash mu M] + [mu M slash slash mu mu' M] \
                     & = [M slash slash mu M] + [M slash slash mu' M]
                       = delta(X, mu) + delta(X, mu').
  $
  Next, consider an exact sequence of ordered pairs (see
  @eq:determinantal-exact-relation):
  $ 0 -> (X_1, lambda) -> (X_2, mu) -> (X_3, nu) -> 0. $
  Let $L, M, N$ be full $Lambda$-lattices in $X_1$, $X_2$, and $X_3$,
  respectively, chosen so that $0 -> L -> M -> N -> 0$ is exact. Such a choice
  is obtained by taking a full lattice $M$ in $X_2$, its inverse image in $X_1$,
  and its image in $X_3$. Then @eq:lattice-relative-class-additivity is
  precisely the assertion that
  $ delta(X_2, mu) = delta(X_1, lambda) + delta(X_3, nu). $
  This completes the proof that $delta$ is well defined on $K_1 lr((A))$, and we
  write $delta[X, mu]$ instead of $delta(X, mu)$ hereafter.

  _Step 3._ It remains for us to prove that $im delta = ker psi$ in the sequence
  @eq:heller-reiner-localization-sequence. For $[X, mu] in K_1 lr((A))$, let
  $X = K M$ for some $Lambda$-lattice $M$. Then
  $
    psi delta[X, mu] & = psi[M slash slash mu M]
                       = {[M] - [M inter mu M]} - {[mu M] - [M inter mu M]} \
                     & = [M] - [mu M] = 0,
  $
  since $mu M tilde.equiv M$. Therefore, $im delta subset.eq ker psi$.

  To prove the reverse inclusion, let $xi = [T_1] - [T_2] in ker psi$, where
  $T_1$ and $T_2$ are f.g. $S$-torsion $Lambda$-modules. Choose $Lambda$-exact
  sequences
  $ 0 -> L_i -> M_i -> T_i -> 0, quad i = 1, 2, $
  with $L_i$ and $M_i$ $Lambda$-lattices; then
  $psi[T_i] = [M_i] - [L_i] in G_0 lr((Lambda))$. Therefore,
  $ 0 = psi(xi) = [M_1] - [L_1] - [M_2] + [L_2] quad "in" G_0 lr((Lambda)), $
  and so
  $ [L_1 plus.o M_2] = [L_2 plus.o M_1] quad "in" G_0 lr((Lambda)). $
  Using the isomorphism $G_0 lr((Lambda)) tilde.equiv G_0^R lr((Lambda))$
  established in @th:regular-grothendieck-k0, and the analogue of
  @prop:grothendieck-equal-classes-criterion for $G_0^R lr((Lambda))$, it
  follows that there exist $Lambda$-lattices $U, V, W$, and a pair of ses’s:
  #source(54)
  $
    0 -> U -> L_1 plus.o M_2 plus.o V -> W -> 0,
    quad 0 -> U -> L_2 plus.o M_1 plus.o V -> W -> 0.
  $
  Applying $K times.o_R ast$ to both of these, we obtain a pair of ses’s of
  $A$-modules. These sequences are split since $A$ is semisimple. Therefore, we
  can find an $A$-isomorphism
  $ mu: K(L_1 plus.o M_2 plus.o V) tilde.equiv K(L_2 plus.o M_1 plus.o V) $
  which yields the identity map on both $K U$ and $K W$. Applying
  @eq:lattice-relative-class-additivity, it follows that
  $
    [(L_2 plus.o M_1 plus.o V) slash slash mu(L_1 plus.o M_2 plus.o V)] = 0
    quad "in" G_0^t lr((Lambda)).
  $ <eq:localization-comparison-zero>
  On the other hand, from @eq:lattice-relative-class-transitivity we obtain (in
  $G_0^t lr((Lambda))$):
  $
    xi & = [T_1] - [T_2] = [M_1 slash L_1] - [M_2 slash L_2] \
       & = [(M_1 plus.o L_2 plus.o V) slash slash (M_2 plus.o L_1 plus.o V)].
  $
  Using @eq:localization-comparison-zero, we then have
  $
    xi & = [(M_1 plus.o L_2 plus.o V) slash slash (M_2 plus.o L_1 plus.o V)] \
       & quad - [(M_1 plus.o L_2 plus.o V) slash slash
           mu(M_2 plus.o L_1 plus.o V)] \
       & = -[(M_2 plus.o L_1 plus.o V) slash slash
           mu(M_2 plus.o L_1 plus.o V)] in im delta.
  $
  This completes the proof that $im delta = ker psi$, and establishes the
  theorem.
]

Since $A$ is an artinian ring, $G_0 lr((A))$ is a free $ZZ$-module with
$ZZ$-basis $lr({[S_1], dots, [S_n]})$, where the $lr({S_i})$ are a basic set of
simple left $A$-modules. Since $G_0 lr((A))$ is $ZZ$-free, the sequence
@eq:heller-reiner-localization-sequence is $ZZ$-split, and therefore,
$
  G_0 lr((Lambda)) tilde.equiv G_0 lr((A)) plus.o op("cok") delta,
  quad "where" op("cok") delta = G_0^t lr((Lambda)) slash im delta.
$ <eq:order-grothendieck-splitting>
Thus, the problem of determining the additive group $G_0 lr((Lambda))$ is
reduced to the calculation of $G_0^t lr((Lambda)) slash im delta$. This is a
much simpler problem, which we shall treat in detail in
§@sec:grothendieck-integral-group-rings. As a preliminary step, we now discuss
an important special case:

#theorem[
  Let $R$ be a Dedekind domain whose quotient field $K$ is a global field. Let
  $A$ be a central simple $K$-algebra, and let $Lambda$ be a maximal $R$-order
  in $A$. Then
  $
    G_0 lr((Lambda)) tilde.equiv ZZ plus.o op("Cl")_A R,
    quad "where" op("Cl")_A R = I(R) slash P_A lr((R)).
  $
  Here, $I(R)$ denotes the group of fractional $R$-ideals in $K$, and
  $P_A lr((R))$ is the subgroup of $I(R)$ consisting of all principal ideals
  $lr({R alpha: alpha in K^+})$, where#footnote[See
    @i:eq:positive-at-ramified-real-primes.]
  #source(55)
  $
    K^+ = {alpha in K^dot: alpha_P > 0 "at every infinite real prime"
      P "of" K "at which" A "is ramified"}.
  $
] <th:dedekind-order-projective-grothendieck>
#proof[
  There is only one isomorphism class of simple left $A$-modules in this case,
  since $A$ is a simple artinian ring, and therefore
  $G_0 lr((A)) tilde.equiv ZZ$. Thus, it suffices to show that
  $op("cok") delta tilde.equiv op("Cl")_A R$, and we begin by establishing an
  isomorphism
  $ tau: G_0^t lr((Lambda)) tilde.equiv I(R). $
  <eq:torsion-grothendieck-ideal-isomorphism>
  To define $tau$, let $X$ be any f.g. $R$-torsion $Lambda$-module. Then
  $alpha X = 0$ for some nonzero $alpha in R$, so $X$ is a f.g. module over the
  ring $Lambda slash alpha Lambda$; this ring is artinian and noetherian, and
  therefore so is $X$. This shows that the $Lambda$-module $X$ has a composition
  series. Let the composition factors be $lr({X_1, dots, X_n})$. We now define
  $ tau[X] = product_(i=1)^n op("ann")_R lr((X_i)) in I(R). $
  Since $tau$ is multiplicative on ses’s of f.g. $R$-torsion $Lambda$-modules,
  it follows that $tau$ is a well-defined homomorphism from $G_0^t lr((Lambda))$
  into $I(R)$.

  The theorem is trivially true when $R = K$, so we exclude this case for the
  remainder of the proof. Let $P$ range over the maximal ideals of $R$; by
  @eq:order-torsion-grothendieck-decomposition,
  $
    G_0^t lr((Lambda)) tilde.equiv product.co_P G_0 lr((Lambda slash P Lambda)).
  $
  For each $[X] in G_0^t lr((Lambda))$, its image in
  $G_0 lr((Lambda slash P Lambda))$ is precisely $sum_i [X_i]$, the sum
  extending over all $Lambda$-composition factors $lr({X_i})$ of $X$ for which
  $P X_i = 0$. (This follows readily from Step 2 of the proof of
  @th:grothendieck-localization-sequence.) On the other hand, $I(R)$ is the free
  abelian group generated by the set of all maximal ideals $P$ of $R$. Thus, to
  prove @eq:torsion-grothendieck-ideal-isomorphism it suffices to show that
  $tau$ gives rise to an isomorphism
  $
    tau_P: G_0 lr((Lambda slash P Lambda)) tilde.equiv lr(chevron.l P chevron.r)
    quad "for each" P,
  $
  where $lr(chevron.l P chevron.r)$ is the infinite cyclic subgroup of $I(R)$
  generated by $P$.

  Let $Lambda_P$ denote the localization of $Lambda$ at $P$. Then
  $ Lambda slash P Lambda tilde.equiv Lambda_P slash P Lambda_P, $
  and by @i:prop:ring-radical-quotients-and-modules we have
  $
    (Lambda_P slash P Lambda_P) slash rad(Lambda_P slash P Lambda_P)
    tilde.equiv Lambda_P slash rad Lambda_P.
  $
  The right-hand expression is a simple artinian ring, since $Lambda_P$ is a
  maximal $R_P$-order in a central simple $K$-algebra (see
  @i:th:dvr-maximal-orders-completion-lattices(ii)).
  #source(56)
  Therefore, the artinian ring $Lambda slash P Lambda$ has a simple left module,
  unique up to isomorphism, which we denote temporarily by $S(P)$. It now
  follows that $G_0 lr((Lambda slash P Lambda))$ is a free $ZZ$-module with a
  single basis element $[S(P)]$. Furthermore, by
  @i:th:dvr-maximal-orders-completion-lattices(ii) we have
  $ op("ann")_R S(P) = P. $
  This shows that $tau_(P)[S(P)] = P$, so
  $tau_P: G_0 lr((Lambda slash P Lambda)) tilde.equiv lr(chevron.l P chevron.r)$
  as desired, and we have completed the proof of
  @eq:torsion-grothendieck-ideal-isomorphism.

  Now let $a in Lambda inter A^dot$; then $Lambda slash Lambda a$ is an
  $R$-torsion $Lambda$-module, and we need to know the ideal
  $tau(Lambda slash Lambda a)$ in $R$. However, by @bib:Reiner1975[MO, (24.14)],
  the product of the $R$-annihilators of the $Lambda$-composition factors of
  $Lambda slash Lambda a$ is precisely the principal ideal $R op("nr")(a)$,
  where $op("nr")$ is the reduced norm map $op("nr")_(A slash K)$ from $A$ to
  $K$ (see §@i:ss:reduced-norms). Thus
  $
    tau(Lambda slash Lambda a) = R dot op("nr")(a),
    quad a in Lambda inter A^dot.
  $
  Using the isomorphism @eq:torsion-grothendieck-ideal-isomorphism, we have
  $
    op("cok") delta = G_0^t lr((Lambda)) slash im delta
    tilde.equiv I(R) slash im tau delta,
  $
  so to complete the proof of the theorem, we need only establish that
  $im tau delta = P_A lr((R))$, where $P_A lr((R))$ is the subgroup of $I(R)$
  defined in the statement of the theorem.

  By Exercise @exc:semisimple-whitehead-unit-representatives, each element of
  $K_1 lr((A))$ can be written as $[A, a_r]$ for some $a in A^dot$, where $a_r$
  denotes right multiplication on $A$ by $a$. Each $a in A^dot$ is expressible
  as a quotient $a = b c^(-1)$, with $b, c in Lambda inter A^dot$ (indeed, we
  can choose $c in R$ if desired), and therefore $tau delta(K_1 lr((A)))$ is the
  multiplicative subgroup of $I(R)$ generated by
  $ lr({tau delta[A, a_r]: a in Lambda inter A^dot}). $
  In order to calculate $delta[A, a_r]$, we must choose a full $Lambda$-lattice
  $M$ in $A$, and then
  $delta[A, a_r] = [M slash slash M a] in G_0^t lr((Lambda))$. Choosing
  $M = Lambda$, we obtain
  $ tau delta[A, a_r] = tau[Lambda slash Lambda a] = R dot op("nr")(a). $
  Thus
  $
    im tau delta = lr(
      chevron.l
      lr({R dot op("nr")(a): a in Lambda inter A^dot}) chevron.r
    )
    = {R dot op("nr")(x): x in A^dot}.
  $
  But by the Hasse–Schilling–Maass Norm Theorem
  @i:th:hasse-schilling-maass-norm,
  $ {op("nr")(x): x in A^dot} = K^+. $
  This proves that $im tau delta = P_A lr((R))$, as claimed, and the theorem is
  established.
]

#remarks[
  #enum(
    numbering: "(i)",
    [By @th:regular-grothendieck-k0, we have
      $G_0 lr((Lambda)) tilde.equiv G_0^R lr((Lambda))$. Since $Lambda$ is a
      maximal $R$-order, every $Lambda$-lattice is $Lambda$-projective.
      Therefore $G_0^R lr((Lambda)) = K_0 lr((Lambda))$, so from Theorem
      @th:dedekind-order-projective-grothendieck we obtain
      $ K_0 lr((Lambda)) tilde.equiv ZZ plus.o op("Cl")_A R. $
      #source(57)
      This result was proved in a somewhat different fashion by Swan
      @bib:Swan1962.],
    [For any global field $K$, and any central simple $K$-algebra
      $A = M_n lr((D))$, where $D$ is a division algebra with center $K$, there
      are isomorphisms
      $
        K_1 lr((A)) tilde.equiv K_1 lr((D)) tilde.equiv D^hash
        tilde.equiv op("nr")(D^dot) tilde.equiv K^+.
      $
      On the other hand, every element of $K_1 lr((A))$ is of the form
      $[A, a_r]$ with $a in A^dot$. Further,
      $ [A, a_r] + [A, b_r] = [A, (a b)_r] quad "for" a, b in A^dot, $
      so there is a surjective homomorphism
      $ A^dot -> K_1 lr((A)), quad "given by" a -> [A, a_r], quad a in A^dot. $
      Since $K_1 lr((A))$ is commutative, this yields a surjection
      $ A^dot slash [A^dot, A^dot] -> K_1 lr((A)). $
      However, $op("nr")_(A slash K) lr((A^dot)) =
      op("nr")_(D slash K) lr((D^dot))$, and there is a commutative diagram
      #whitehead-norm-square
      Both vertical arrows are isomorphisms, by the Wang–Platonov Theorem, and
      so we obtain
      $ K_1 lr((A)) tilde.equiv A^dot slash [A^dot, A^dot]. $
      (The result need not hold for arbitrary central simple algebras. For
      instance, if $A = M_2(F)$, $F = ZZ slash 2 ZZ$, then
      $K_1 lr((A)) tilde.equiv F^dot$ while $A^dot slash [A^dot, A^dot]$ has
      order 2.)],
  )
] <rem:maximal-order-k0-whitehead>

#exercises-heading

#exercise[
  Calculate $K_0 lr((F))$ for $F$ a field, skewfield, or local ring. What can be
  said about $G_0 lr((F))$ in the first two cases? Calculate $G_0 lr((R))$ for
  $R$ a local left regular ring.
] <exc:grothendieck-fields-local-rings>

#exercise[
  Show that each ring homomorphism $phi: A -> B$ induces an additive
  homomorphism $K_i lr((A)) -> K_i lr((B))$, $i = 0, 1$. Further, if $B$ is a
  flat right $A$-module (via $phi$), there are homomorphisms
  $G_i lr((A)) -> G_i lr((B))$, $i = 0, 1$.
] <exc:grothendieck-functoriality>

#source(58)
#exercise[
  Verify the assertions in @exm:frobenius-modules-morphisms.
] <exc:green-rings-assertions>

#exercise[
  Show that Morita equivalent rings have the same $K_0$ and the same $G_0$. Does
  this also hold for $K_1$ and $G_1$?
] <exc:grothendieck-morita-equivalence>

#exercise[
  Let $N$ be a nilpotent two-sided ideal of a left noetherian ring $A$. Prove
  that there is an isomorphism
  $theta: G_0 lr((A slash N)) tilde.equiv G_0 lr((A))$, given by
  $theta[X] = [X]$ for each f.g. $(A slash N)$-module $X$.
  #hint([@exc:grothendieck-nilpotent-ideal])[
    Define an inverse $psi: G_0 lr((A)) -> G_0 lr((A slash N))$ by setting
    $ psi[Y] = sum_i [N^(i-1) Y slash N^i Y] $
    for each f.g. $A$-module $Y$. To show that $psi$ is well defined, it
    suffices to show that for $X$ any $A$-submodule of $Y$, we have
    #named-equation(name: [$(ast)$])[$
      sum [N^(i-1) Y slash N^i Y]
      = sum lr(
        {[N^(i-1) X slash N^i X]
          + [N^(i-1) lr((Y slash X)) slash N^i lr((Y slash X))]}
      )
    $] <eq:nilpotent-filtration-additivity>
    in $G_0 lr((A slash N))$. By Zassenhaus’s Lemma, the finite chains
    $
      Y supset.eq X supset.eq 0, quad
      Y supset.eq N Y supset.eq N^2 Y supset.eq dots supset.eq N^k Y = 0
    $
    have equivalent refinements. Thus there exists a chain of $A$-modules
    $ Y = Y_0 supset.eq Y_1 supset.eq dots supset.eq Y_s = 0 $
    with some $Y_m = X$, and with $N(Y_(j-1) slash Y_j) = 0$ for each $j$. But
    in $G_0 lr((A slash N))$, both sides of formula
    @eq:nilpotent-filtration-additivity are equal to $sum [Y_(j-1) slash Y_j]$.
  ]
] <exc:grothendieck-nilpotent-ideal>

#exercise[
  Prove that $G_0 lr((A)) tilde.equiv G_0 lr((A slash rad A))
  tilde.equiv K_0 lr((A))$ for every left artinian ring $A$.
] <exc:artinian-k0-g0>

#exercise[
  Suppose that $Lambda$ is either a left artinian ring, or an $R$-algebra
  f.g./$R$ as $R$-module, where $R$ is a complete noetherian local ring. Let $N$
  be a two-sided ideal of $Lambda$ contained in $rad Lambda$, and set
  $overline(Lambda) = Lambda slash N$. Show that there is an isomorphism
  $
    K_0 lr((Lambda)) tilde.equiv K_0 lr((overline(Lambda))),
    quad "given by" [X] -> [X slash N X]
  $
  for each $X in cal(P)(Lambda)$. Show further that
  $K_0 lr((Lambda)) tilde.equiv G_0 lr((overline(Lambda)))$ when
  $N = rad Lambda$.
] <exc:complete-ring-projective-quotient>

#exercise[
  Prove that for an arbitrary ring $A$, each $x in K_0 lr((A))$ is of the form
  $x = [A^((n))] - [X]$ for some $n$ and some $X in cal(P)(A)$.
] <exc:projective-class-free-difference>

#exercise[
  Let $A$ be an arbitrary ring, $M$ a left $A$-module, and $E = End_A M$, where
  $E$ acts from the right on $M$. Let $cal(C)$ be the category of $A$-direct
  summands of $M^((k))$, $k = 1, 2, dots$, and let $K_0 lr((cal(C), plus.o))$ be
  the additive group generated by symbols $(X)$, $X in cal(C)$, with relations
  $(X plus.o X') = (X) + (X')$ for $X, X' in cal(C)$. Prove that
  $ K_0 lr((cal(C), plus.o)) tilde.equiv K_0 lr((E)). $
  #hint([@exc:summand-category-projective-group])[
    Use @i:prop:morita-summand-equivalence. The desired isomorphism is given by
    $
      [N] -> [Hom_A lr((attach(M, bl: A, br: E), attach(N, bl: A)))]
      quad "for" N in cal(C).
    $
  ]
] <exc:summand-category-projective-group>

#source(59)

#exercise[
  Keep the hypotheses of @th:regular-grothendieck-k0, and let
  $ 0 -> L -> M -> X -> 0 $
  be an exact sequence of f.g. $Lambda$-modules, where $L$ and $M$ are
  $Lambda$-lattices. Prove that the isomorphism
  $G_0 lr((Lambda)) tilde.equiv G_0^R lr((Lambda))$ maps $[X]$ onto $[M] - [L]$.
] <exc:regular-grothendieck-presentation>

#exercise[
  Let $A$ be an arbitrary ring, and let $0 -> L -> M -> N -> 0$ be an exact
  sequence of $A$-modules. Prove that
  $
    op("hd") M <= op("Max")(op("hd") L, op("hd") N),
    quad op("hd") L <= op("Max")(op("hd") M, op("hd") N), \
    op("hd") N <= op("Max")(1 + op("hd") L, op("hd") M).
  $
  #hint([@exc:homological-dimension-short-exact])[
    Use @lem:generalized-schanuel or @i:th:ext-long-exact-sequence.
  ]
] <exc:homological-dimension-short-exact>

#exercise[
  Let $G$ be a finite group, and let $M$ be any f.g. left $ZZ G$-module of
  finite homological dimension. Prove that $op("hd")(M) <= 1$ always, and that
  $op("hd")(M) = 0$ if $M$ is a $ZZ G$-lattice.
  #hint([@exc:group-ring-finite-homological-dimension], caption: [Hint (S.
    Chase):])[
    Suppose $op("hd")(M) = n > 1$, and consider a projective resolution
    $ 0 -> P_n -> P_(n-1) -> dots -> P_1 -> P_0 -> M -> 0 $
    with each $P_i in cal(P)(ZZ G)$. As in the proof of
    @prop:homological-dimension-ext-criterion, the above sequence may be broken
    up into a collection of ses’s:
    $
      0 -> L_0 -> P_0 -> M -> 0, quad 0 -> L_1 -> P_1 -> L_0 -> 0,
      dots, 0 -> P_n -> P_(n-1) -> L_(n-2) -> 0.
    $
    By Exercise @i:exc:lattice-extension-projective-splits, each of these
    sequences (except the first one) is $ZZ G$-split. Thus
    $L_0 in cal(P)(ZZ G)$, so $op("hd")(M) <= 1$. If $M$ is a $ZZ G$-lattice,
    then the sequence $0 -> L_0 -> P_0 -> M -> 0$ is $ZZ G$-split, so
    $M in cal(P)(ZZ G)$.
  ]
] <exc:group-ring-finite-homological-dimension>

#exercise[
  Let $G$ be a finite group, $G != {1}$. Prove that the global dimension of
  $ZZ G$ must be infinite.
  #hint([@exc:integral-group-ring-infinite-global-dimension])[
    If not, then $op("hd")_(ZZ G) lr((ZZ)) = 0$, where $G$ acts trivially on
    $ZZ$. But then $ZZ$ is $ZZ G$-projective, which is impossible.
  ]
] <exc:integral-group-ring-infinite-global-dimension>

#exercise[
  Let $A$ be a semisimple ring. Show that every element of $K_1 lr((A))$ is of
  the form $[A, a_r]$, where $a_r$ is right multiplication on $A$ by an element
  $a in A^dot$.
  #hint([@exc:semisimple-whitehead-unit-representatives])[
    It suffices to treat the case where $A$ is a simple artinian ring, say
    $A = End_D V$, as in the discussion following
    @eq:whitehead-morita-isomorphism. By @th:whitehead-skewfield-determinant,
    each element of $K_1 lr((D))$ is of the form $[D, d_r]$ for some
    $d in D^dot$. Under the isomorphism @eq:whitehead-morita-isomorphism, its
    image in $K_1 lr((A))$ is $[V, alpha]$ for some $alpha in Aut_A V$. Choose
    an $A$-module $V'$ with $V plus.o V' tilde.equiv A$; then in $K_1 lr((A))$,
    $ [V, alpha] = [V plus.o V', alpha plus.o 1] = [A, a_r] $
    for some $a in A^dot$.
  ]
] <exc:semisimple-whitehead-unit-representatives>

#source(60)
#exercise[
  Let $D$ be a skewfield. Calculate the Dieudonné determinant of the matrix
  $mat(a, b; c, d) in GL_2(D)$.
  #hint([@exc:dieudonne-determinant-two-by-two])[
    Treat separately the cases $a != 0$ and $a = 0$.
  ]
] <exc:dieudonne-determinant-two-by-two>

#exercise[
  Is it true that a homomorphic image of a left regular ring must also be left
  regular?
] <exc:regular-ring-homomorphic-image>

#exercise[
  Prove the following generalization of the Localization Sequence
  @th:grothendieck-localization-sequence: _Let $Lambda$ be a left noetherian
  ring, and let $S$ be any multiplicative subset of the center of $Lambda$. Then
  @eq:grothendieck-localization-sequence is an exact sequence, where now
  $Lambda' = S^(-1) Lambda$._
] <exc:central-localization-sequence>
