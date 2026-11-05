#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/62-cyclic-defect-blocks.typ": *

== Blocks with Cyclic Defect Groups <sec:cyclic-defect-blocks>

The main result gives the numbers of simple and indecomposable $k G$-modules
belonging to a $p$-block of $G$ with a cyclic defect group in terms of the
inertial #source(512)index of the block. The proof follows Michler
@bib:Michler1976, and draws together ideas from homological algebra, uniserial
algebras, the Green Correspondence, Clifford Theory from
§§~@i:sec:clifford-theory-hecke-algebras and @i:sec:vertices-sources, and many
other results discussed earlier in this chapter. The information about the
modules in such a block provides a basis for a new construction of a periodic
projective resolution of the trivial $R G$-module (see also Michler
@bib:Michler1975). Dade's comprehensive results on the $K$-characters belonging
to a cyclic block are not given in full generality, but are illustrated in
§~@ss:cyclic-defect-periodic-resolutions for the special case of a group with a
cyclic self-centralizing Sylow $p$-subgroup which is a T.I. set. A combinatorial
description of the relations between P.I.M.'s and simple $k G$-modules in a
cyclic block, called the Brauer tree, is also given in this case. A complete and
definitive account of blocks with cyclic defect groups, including Brauer's work
on blocks of defect one, Dade's work @bib:Dade1966 on cyclic blocks, with many
extensions and improvements, was given by Feit @bib:Feit1982. It remains a
challenging problem to obtain equally strong results for other types of blocks
(see, for example, Broué–Puig @bib:Broue1980).

=== Preliminary Results from Homological Algebra
<ss:cyclic-block-homological-preliminaries>

In §§~@ss:cyclic-block-homological-preliminaries and
@ss:green-correspondence-functorial-properties, we shall collect some elementary
facts from homological algebra concerning indecomposable modules for group
algebras and their connection with the Green correspondence. These will be
applied in §~@ss:cyclic-defect-modular-representations on modules in blocks with
cyclic defect groups, and some of them will also reappear in
§§~@sec:auslander-reiten-sequences and @sec:representation-rings on
Auslander–Reiten sequences and the Green ring.

In the first part of our discussion, $G$ denotes a finite group, and $R$ an
arbitrary commutative ring. We recall some facts about the relative trace map,
$G$-algebras, and relative projectivity, from §§~@i:sec:vertices-sources,
@i:sec:green-correspondence, and @sec:defect-groups-blocks.

Let $M$ and $N$ be f.g. left $R G$-modules, and let us set
$ (M,N) = op("Hom")_R lr((M,N)). $
Then $G$ acts on $(M,N)$ according to the rule
$ x phi = x phi x^(-1), quad "for" x in G, quad phi in (M,N). $
For an arbitrary subgroup $H <= G$, we set
$ (M,N)_H = {phi in (M,N): x phi = phi quad "for all" x in H}. $
Then $(M,N)_H$ is simply the set of $R H$-homomorphisms from $M$ to $N$:
$ (M,N)_H = op("Hom")_(R H) lr((M,N)). $
#nidx("$(M,N)_G$", "$op(\"Hom\")_(R G) lr((M,N))$")
Following the terminology introduced in §~@sec:defect-groups-blocks, we define
the _relative trace map_
$ T_(G slash H): (M,N)_H arrow (M,N)_G, $
#source(513)
for $H <= G$, by the formula
$ T_(G slash H) phi = sum_(x in G slash H) x phi, $
where the sum is taken over a cross section of the set of left cosets
$G slash H$. The map $T_(G slash H): (M,N)_H arrow (M,N)_G$ is independent of
the choice of a cross section. We next set
$ (M,N)_(G slash H) = op("im") T_(G slash H) = T_(G slash H) lr((M,N)_H), $
and obtain easily:

#lemma[
  Let $H <= G$, and let $L,M$ and $N$ be left $R G$-modules.
  #case-list(
    numbering: "(i)",
    [#case[Let $psi in (L,M)_G$ and $phi in (M,N)_G$. Then $phi psi in (L,N)_G$.
        Moreover, $phi psi in (L,N)_(G slash H)$ if either
        $psi in (L,M)_(G slash H)$ or $phi in (M,N)_(G slash H)$.]
      <case:projective-map-composition-ideal>],
    [#case[$(M,M)_(G slash H)$ is an ideal in $(M,M)_G$.]
      <case:relative-trace-endomorphism-ideal>],
    [#case[A left $R G$-module $M$ is $(G,H)$-projective if and only if
        $op("id")_M in (M,M)_(G slash H)$.]
      <case:relative-projectivity-trace-identity>],
  )
] <lem:module-homomorphism-relative-trace>

Parts~@case:projective-map-composition-ideal and
@case:relative-trace-endomorphism-ideal are similar to the results in
@prop:g-algebra-relative-trace-properties, and are left as exercises.
Part~@case:relative-projectivity-trace-identity is a restatement of part of
Theorem @i:th:gaschutz-relative-projectivity.

Now let $k$ be a field. We let $cal(P)(k G)$ denote the category of f.g.
projective $k G$-modules, and note that a $k G$-module $M$ belongs to
$cal(P)(k G)$ if and only if $M$ is $(G,1)$-projective, since the coefficient
ring is a field (see §~@i:ss:relative-projectivity).

#definitions[
  Let $M$ and $N$ be f.g. left $k G$-modules. A map $phi in (M,N)_G$ is called
  _projective_ provided that $phi in (M,N)_(G slash 1)$. A _projective
  presentation_ $(P,pi)$ of a $k G$-module $N$ is a surjective homomorphism
  $pi: P arrow N$ for some $P in cal(P)(k G)$. A left $k G$-module is called a
  _core_ if and only if $M$ has no nonzero projective direct summands.
] <def:projective-map-presentation-core>
#idx("Projective homomorphism", target: [@def:projective-map-presentation-core])
#idx("Core", target: [@def:projective-map-presentation-core])

From the preceding remarks, it is clear that a $k G$-module $M$ is projective if
and only if $op("id")_M$ is a projective map. The idea of a core is related to
the following construction. Let $M$ be an arbitrary f.g. $k G$-module. Then $M$
can be expressed as a direct sum of indecomposable $k G$-modules. If we discard
the projective ones, we are left with a module, called the _core of
$M$_, which is uniquely determined, up to isomorphism, by the K-S-A Theorem.
Thus a module is isomorphic to its core if it has the property stated in the
last part of @def:projective-map-presentation-core (see also
§~@ss:heller-loop-space-operator).

We now have:

#proposition[
  Let $L$ and $M$ be $k G$-modules, and let $pi: P arrow M$ be a projective
  presentation of $M$. A map $lambda in (L,M)_G$ is projective if and only if
  there exists a map $mu in (L,P)_G$ such that $lambda = pi mu$.
] <prop:projective-map-factorization-presentation>

#proof[
  #source(514)
  The condition means that for some $mu in (L,P)_G$, the diagram
  #projective-map-factorization
  commutes. If $mu$ exists, then we have
  $ lambda = pi(op("id")_P)mu, $
  where $op("id")_P$ is projective since $P$ is a projective module. Then
  $lambda$ is a projective map, by @lem:module-homomorphism-relative-trace.

  Conversely, let $lambda$ be a projective map; then
  $lambda = T_(G slash 1) lambda_0$ for some $lambda_0 in (L,M)$, by Definition
  @def:projective-map-presentation-core. Since $M$ is a projective $k$-module,
  there exists a map $j in (M,P)$ such that $pi j = op("id")_M$. Set
  $ mu = T_(G slash 1) lr((j lambda_0)). $
  Then $mu in (L,P)_G$, and we have
  $
    pi mu = pi T_(G slash 1) lr((j lambda_0))
    = T_(G slash 1) lr((pi j lambda_0)) = T_(G slash 1) lr((lambda_0)) = lambda,
  $
  using the basic properties of the trace map. This completes the proof.
]

Thus a map $lambda in (L,M)_G$ is projective if and only if $lambda$ factors
through a projective module. Let $M^*$ denote the contragredient $k G$-module,
for a f.g. left $k G$-module $M$. The correspondence $M arrow M^*$ is a
contravariant functor from the category of f.g. $k G$-modules to itself, by
§~@i:ss:contragredient-modules. Moreover, a f.g. $k G$-module is projective if
and only if it is injective, by @i:th:gaschutz-relative-projectivity. Using
these remarks, we obtain easily the following dual version of the preceding
result.

#proposition[
  Let $pi': M arrow Q$ be an injective embedding of a f.g. left $k G$-module $M$
  (that is, $Q$ is injective and $ker pi' = 0$). Let $lambda' in (M,L)_G$, for
  some f.g. $k G$-module $L$. Then $lambda'$ is a projective map if and only if
  there exists $mu' in (Q,L)_G$ such that $lambda' = mu' pi'$.
] <prop:projective-map-factorization-injective-embedding>

#proposition[
  Let $M$ be a core, and let $eta: M arrow N$ be a surjective homomorphism of
  $k G$-modules. Then $eta$ is not projective unless $eta = 0$.
] <prop:core-surjection-not-projective>

#proof[
  Let $pi: P arrow N$ be a projective cover of $N$ (see
  §~@i:ss:projective-covers). If $eta$ is projective, there exists a map
  $mu in (M,P)_G$ such that $eta = pi mu$, by
  @prop:projective-map-factorization-presentation. Since $eta$ is surjective, we
  have $op("im") mu = P$ by the definition of projective covers, from
  §~@i:ss:projective-covers. Then the extension $mu: M arrow P$ splits, since
  $P$ is projective. This contradicts the assumption that $M$ is a core, unless
  $eta = 0$.
]

#source(515)
The dual version is:

#corollary[
  Let $N$ be a core, and let $eta': M arrow N$ be a homomorphism of
  $k G$-modules such that $ker eta' = 0$. Then $eta'$ is not projective unless
  $eta' = 0$.
] <cor:core-injection-not-projective>

#proposition[
  Let $M$ and $N$ be f.g. $k G$-modules. Then $(M,N)_(G slash 1) = 0$ if either
  of the following statements hold:
  #case-list(
    numbering: "(i)",
    [#case[$M$ is a core and $N$ is simple.]
      <case:core-to-simple-projective-map-zero>],
    [#case[$M$ is simple and $N$ is a core.]
      <case:simple-to-core-projective-map-zero>],
  )
] <prop:core-simple-projective-maps-zero>

#proof[
  Let $eta in (M,N)_(G slash 1)$, and assume $eta != 0$. Then, in
  case~@case:core-to-simple-projective-map-zero, $eta$ is surjective, and is a
  projective map by @def:projective-map-presentation-core. This contradicts
  @prop:core-surjection-not-projective. In
  case~@case:simple-to-core-projective-map-zero, we contradict
  @cor:core-injection-not-projective unless $(M,N)_(G slash 1) = 0$.
]

#corollary[
  Let $M$ be simple and nonprojective. Then $(M,M)_(G slash 1) = 0$.
] <cor:simple-nonprojective-projective-endomorphisms-zero>

=== Functorial Properties of the Green Correspondence
<ss:green-correspondence-functorial-properties>

In this subsection, we extend the Green correspondence from indecomposable
lattices, as in §~@i:sec:green-correspondence, to maps in the category of
$R G$-lattices. These results, which are due to Feit @bib:Feit1969 and Green
@bib:Green1972, are interesting in themselves, and have important applications
to modules in blocks with cyclic defect groups (see
§§~@ss:cyclic-defect-modular-representations,
@ss:cyclic-defect-periodic-resolutions).

Throughout the discussion, $G$ denotes a finite group, and $R$ denotes either a
field of characteristic $p > 0$ or a d.v.r. whose residue field
$R slash frak(p)$ has characteristic $p > 0$, and with the property that $R$ is
complete in the $frak(p)$-adic topology. Then the K-S-A Theorem holds, in the
category of $R H$-lattices, for an arbitrary subgroup $H <= G$.

We first proceed to extend some of the concepts introduced in
§~@ss:cyclic-block-homological-preliminaries to a more general situation. Let
$cal(Z) = {Z_i}$ be a family of subgroups of $G$. Let $M,N$ be $R G$-lattices,
and let
$ (M,N)_(G,cal(Z)) = sum_(Z_i in cal(Z)) T_(G slash Z_i) lr((M,N)_(Z_i)), $
#nidx(
  "$(M,N)_(G slash cal(X))$",
  "$sum_(Z_i in cal(X)) T_(G slash Z_i) (M,N)_(Z_i)$",
)
where $T_(G slash Z_i)$ is the relative trace map defined in
§~@ss:cyclic-block-homological-preliminaries. In particular, we have
$(M,N)_(G,cal(Z)) = (M,N)_(G slash Z)$ as in
§~@ss:cyclic-block-homological-preliminaries, in case $cal(Z)$ contains only the
subgroup $Z$. We shall call a map $mu in (M,N)_G$ a $(G,cal(Z))$-_projective
map_ in case $mu in (M,N)_(G,cal(Z))$. An $R G$-lattice $M$ is called
$(G,cal(Z))$-_projective_ if and only if the identity map $op("id")_M$ is
$(G,cal(Z))$-projective (see @lem:module-homomorphism-relative-trace,
part~@case:relative-projectivity-trace-identity). It is easily shown, using
Rosenberg's Lemma @lem:rosenberg-primitive-idempotent-ideal-sum, that this
concept of a $(G,cal(Z))$-projective $R G$-lattice agrees with Definition
@i:def:family-relative-projectivity (see
Exercise~@exc:family-relative-projectivity). An $R G$-lattice $M$ is called a
$(G,cal(Z))$-_core_ (see @def:projective-map-presentation-core) provided that
$M$ contains no nonzero $(G,cal(Z))$-projective direct summands. It follows from
the K-S-A Theorem that each $R G$-lattice $M$ has a decomposition

$ M = f_(cal(Z)) M plus.o M'; $
<eq:relative-projective-core-decomposition>
#idx("Core")

#source(516)
where $f_(cal(Z)) M$ is a $(G,cal(Z))$-core and $M'$ is $(G,cal(Z))$-projective,
and that the $R G$-lattices $f_(cal(Z)) M$ and $M'$ are uniquely determined up
to isomorphism.

We now apply these ideas to the Green correspondence. As in
§~@i:sec:green-correspondence, $(G,H,D)$ denotes an admissible triple,
consisting of a $p$-subgroup $D <= G$, and $H <= G$ such that
$H >= N_G lr((D))$. We then let $cal(X)$ and $cal(Y)$ denote the families of
subgroups.
$
  cal(X) = {attach(D, tl: x) inter D: x in G - H} \
  cal(Y) = {attach(D, tl: x) inter H: x in G - H}.
$
We note that $cal(X) <=_H cal(Y)$, in the sense that for every subgroup
$X in cal(X)$, there exists a subgroup $Y in cal(Y)$ such that $X <=_H Y$. We
shall use the notation $A <=_H cal(X)$, for $A <= G$, to indicate that
$A <=_H X$ for some subgroup $X in cal(X)$.

Our first result is simply a reinterpretation of the Green correspondence
@i:th:green-correspondence in terms of the concepts introduced in this
subsection.

#proposition[
  Let $M$ be an indecomposable $R G$-lattice whose vertex $D^*$ satisfies the
  conditions
  $ D^* <= D quad "and" quad D^* lt.eq.not_G cal(X). $
  Let
  $ M_H = f_(cal(Y)) M_H plus.o M'_H $
  be the decomposition @eq:relative-projective-core-decomposition of the
  restriction $M_H$ of $M$ to $R H$, where $f_(cal(Y)) M_H$ is an
  $(H,cal(Y))$-core and $M'_H$ is $(H,cal(Y))$-projective. Then $f_(cal(Y)) M_H$
  is an indecomposable $R H$-lattice with vertex $D^*$, and is isomorphic to the
  Green correspondent of $M$ in the category of $R H$-lattices.
] <prop:green-correspondent-relative-core>
#idx(
  "Green Correspondence",
  "functorial properties",
  target: [@prop:green-correspondent-relative-core],
)

The proof is an immediate consequence of @i:th:green-correspondence, and is left
to the reader.

To simplify notation we set

$ f M = f_(cal(Y)) M_H, $
<eq:green-core-functor-objects>

for an arbitrary $R G$-lattice $M$; then $f M$ is a uniquely determined
$R H$-lattice having no nonzero $(H,cal(Y))$-projective direct summands.
Moreover, we have:

#proposition[
  Let $M$ be a $(G,D)$-projective $R G$-lattice, and let $f M$ be the
  $R H$-lattice defined by @eq:green-core-functor-objects. Then $f M$ is
  $(H,D)$-projective.
] <prop:green-core-relative-projectivity>

#proof[
  Since $M$ is $(G,D)$-projective, we have $M divides L^G$ for some
  $R D$-lattice $L$, by @i:th:gaschutz-relative-projectivity(v). Mackey's
  Theorem @i:th:mackey-subgroup expresses $(L^G)_H$ as $L^H$ together with
  $(H,cal(Y))$-projective summands, since every nonidentity double coset
  contributes a subgroup $H inter attach(D, tl: x)$ with $x in.not H$. By the
  K-S-A Theorem, every indecomposable summand of $f M$ is a summand of $L^H$,
  since $f M$ has no nonzero $(H,cal(Y))$-projective summand. Thus $f M$ is
  $(H,D)$-projective.#ed-note[
    The whole restriction need not be $(H,D)$-projective. For $k=bb(F)_2$,
    $G=S_4$, $D=chevron.l (1 2) chevron.r$ and
    $H=N_G lr((D))=chevron.l (1 2),(3 4) chevron.r$, the restriction of
    $op("ind")_D^G k$ contains $op("ind")_(chevron.l (3 4) chevron.r)^H k$. Its
    restriction to $chevron.l (3 4) chevron.r$ is trivial of dimension two,
    whereas an $(H,D)$-projective module restricts projectively there; see
    @i:th:gaschutz-relative-projectivity and @i:th:mackey-subgroup.
  ]
]

The main result of this subsection is the following theorem of Green
@bib:Green1972.

#source(517)
#theorem[
  Let $M$ and $N$ be $(G,D)$-projective $R G$-lattices, and let $f M$ and $f N$
  be the $(H,D)$-projective $R H$-lattices defined by
  @eq:green-core-functor-objects. Then there exists an isomorphism of
  $R$-modules
  $
    (M,N)_G slash (M,N)_(G,cal(X))
    tilde.equiv (f M,f N)_H slash (f M,f N)_(H,cal(X)).
  $
] <th:green-correspondence-stable-hom-isomorphism>

The proof is based on a series of lemmas.

#lemma[
  Let $U,V,W$ be $R H$-lattices, and let $alpha in (U,V)_H$, $beta in (V,W)_H$.
  Then $beta alpha in (U,W)_(H,cal(X))$ if one of the maps is $(H,D)$-projective
  and the other is $(H,cal(Y))$-projective.
] <lem:green-relative-projective-composition>

#proof[
  Let us first assume that, for some subgroup $Y in cal(Y)$,
  $ alpha = T_(H slash D) xi quad "and" quad gamma = T_(H slash Y) eta, $
  where $xi in (U,V)_D$ and $eta in (V,W)_Y$. Then
  $
    gamma alpha = (T_(H slash Y) eta)(T_(H slash D) xi)
    = sum_z T_(H slash (D inter attach(Y, tl: z))) lr((z eta dot xi)),
  $
  where $z eta in (V,W)_(attach(Y, tl: z))$, and the sum is taken over a cross
  section of the double cosets $D backslash H slash Y$, by the proof of
  @cor:relative-trace-ideal-mackey-product. For each $z$ in the cross section,
  we have
  $
    D inter attach(Y, tl: z) <= D quad "and" quad
    D inter attach(Y, tl: z) <=_H Y,
  $
  for $Y in cal(Y)$. This implies that $D inter attach(Y, tl: z) <=_H cal(X)$
  for each $z$, and hence $gamma alpha$ is $(H,cal(X))$-projective. Since an
  arbitrary $(H,cal(Y))$-projective map $beta in (V,W)_(H,cal(Y))$ can be
  expressed as a sum $beta = sum beta_i$, with $beta_i in (V,W)_(H slash Y_i)$
  for some subgroups $Y_i in cal(Y)$, the preceding calculation shows that
  $beta alpha in (U,W)_(H,cal(X))$, as required. A similar argument applies if
  the assumptions concerning $alpha$ and $beta$ are reversed.
]

Now let $M$ be a $(G,D)$-projective $R G$-lattice, and let
$ M_H = f M plus.o M', $
with $f M$ as in @eq:green-core-functor-objects, and $M'$
$(H,cal(Y))$-projective. Associated with this decomposition there are injection
and projection maps
#green-core-projections
with $p i = op("id")_(f M)$, $p' i' = op("id")_(M')$. Setting $epsilon = i p$,
$epsilon' = i' p'$, it follows that $epsilon$ and $epsilon'$ are orthogonal
idempotents in $(M_H,M_H)_H$, whose sum is $op("id")_(M_H)$. We shall write
$i_M,p_M$, etc., to indicate that these maps are associated with a given module
$M$.

It is now easy to prove:

#source(518)
#lemma[
  Let $M$ and $N$ be $(G,D)$-projective $R G$-lattices, and keep the preceding
  notation. There is an isomorphism of $R$-modules
  $
    mu: (M_H,N_H)_(H slash D) slash (M_H,N_H)_(H,cal(X))
    tilde.equiv (f M,f N)_(H slash D) slash (f M,f N)_(H,cal(X)),
  $
  with inverse $nu$, where the maps are defined by
  $
    mu lr([lambda]) = [p_N lambda i_M], quad
    lambda in (M_H,N_H)_(H slash D), \
    nu lr([alpha]) = [i_N alpha p_M], quad
    alpha in (f M,f N)_(H slash D).
  $
  Here, the brackets indicate elements of the factor modules given above.
] <lem:green-core-projection-stable-hom>

#proof[
  First of all, it is clear that
  $
    (M_H,N_H)_(H,cal(X)) <= (M_H,N_H)_(H slash D)
    quad "and" quad
    (f M,f N)_(H,cal(X)) <= (f M,f N)_(H slash D),
  $
  since each subgroup in $cal(X)$ lies in $D$. Now let
  $lambda in (M_H,N_H)_(H,cal(X))$. Then $lambda in (M_H,N_H)_(H,cal(Y))$ since
  $cal(X) <=_H cal(Y)$, and it follows that
  $p_N lambda i_M in (f M,f N)_(H,cal(X))$ by Lemma
  @lem:green-relative-projective-composition, since the other factors are
  $(H,D)$-projective maps. For example, $i_M: f M arrow M_H$ is
  $(H,D)$-projective since its domain $f M$ is $(H,D)$-projective, by
  @prop:green-core-relative-projectivity. Compose $i_M$ with the relative trace
  expression for $op("id")_(f M)$. The same argument applies to $p_N$, using its
  codomain $f N$. We have now proved that the map $mu$, given above, is a
  well-defined $R$-homomorphism. Similarly, the same is true for $nu$.

  Now let $lambda in (M_H,N_H)_(H slash D)$. Then we have
  $
    lambda = (epsilon_N + epsilon'_N) lambda (epsilon_M + epsilon'_M)
    = epsilon_N lambda epsilon_M + epsilon'_N lambda epsilon_M
    + epsilon_N lambda epsilon'_M + epsilon'_N lambda epsilon'_M,
  $
  and it follows that
  $
    nu mu lr([lambda]) = [i_N p_N lambda i_M p_M]
    = [epsilon_N lambda epsilon_M] = [lambda],
  $
  since the other terms $epsilon'_N lambda epsilon_M$,
  $epsilon_N lambda epsilon'_M$, $epsilon'_N lambda epsilon'_M$ belong to
  $(M_H,N_H)_(H,cal(X))$, by Lemma @lem:green-relative-projective-composition
  again. On the other hand, for $alpha in (f M,f N)_(H slash D)$, we have
  $ mu nu lr([alpha]) = [p_N i_N alpha p_M i_M] = [alpha], $
  since $p_M i_M = op("id")_(f M)$, and similarly for $N$. This completes the
  proof.
]

Using @lem:green-core-projection-stable-hom, to complete the proof of Green's
Theorem we need only establish:

#lemma[
  Keep the preceding notation. There exists an isomorphism of $R$-modules
  $
    (M_H,N_H)_(H slash D) slash (M_H,N_H)_(H,cal(X))
    tilde.equiv (M,N)_(G slash D) slash (M,N)_(G,cal(X)).
  $
] <lem:green-restriction-trace-stable-hom>

#proof[
  Since $M$ and $N$ are $(G,D)$-projective,
  #source(519)
  $(M,N)_G=(M,N)_(G slash D)$ by
  Exercise~@exc:relative-projective-map-factorization. Transitivity of trace
  gives
  $ T_(G slash H) (M_H,N_H)_(H slash D)=(M,N)_(G slash D). $
  Here $R_(G slash H)$ denotes restriction of homomorphisms. Its required image
  will be established below by Mackey's Theorem.

  We next observe that, from the proof of
  @cor:relative-trace-ideal-mackey-product(i), we have for all
  $xi in (M_D,N_D)_D$:
  $
    R_(G slash H) T_(G slash D) xi
    = sum T_(H slash (H inter attach(D, tl: x)))
    R_((attach(D, tl: x)) slash (H inter attach(D, tl: x))) x dot xi,
  $
  where the sum is taken over a cross section of $H backslash G slash D$. Using
  this formula, we obtain

  $
    R_(G slash H) T_(G slash H) beta
    equiv beta (mod (M_H,N_H)_(H,cal(Y)))
  $ <eq:green-restriction-trace-congruence>

  for all $beta in (M_H,N_H)_(H slash D)$. This follows since
  $beta = T_(H slash D) xi$ for some $xi in (M_D,N_D)_D$, so we have
  $
    R_(G slash H) T_(G slash H) beta
    = R_(G slash H) T_(G slash D) xi
    = T_(H slash D) xi
    + sum_(x in.not H) T_(H slash (H inter attach(D, tl: x)))
    R_((attach(D, tl: x)) slash (H inter attach(D, tl: x))) x dot xi \
    equiv beta (mod (M_H,N_H)_(H,cal(Y))),
  $
  since the subgroups $H inter attach(D, tl: x)$ belong to $cal(Y)$ for all
  $x in G - H$. The same argument shows that

  $
    R_(G slash H) (M,N)_(G slash D)
    <= (M_H,N_H)_(H slash D) + (M_H,N_H)_(H,cal(Y)).
  $ <eq:green-restriction-relative-trace-sum>

  We next prove that

  $
    R_(G slash H) (M,N)_(G,cal(X)) <= (M_H,N_H)_(H,cal(Y)).
  $ <eq:green-restriction-exceptional-trace>

  Let $X in cal(X)$; then for $eta in (M_X,N_X)_X$, we have
  $
    R_(G slash H) T_(G slash X) eta
    = sum_z T_(H slash (H inter attach(X, tl: z)))
    R_((attach(X, tl: z)) slash (H inter attach(X, tl: z))) z eta,
  $
  where the sum is taken over a cross section of $H backslash G slash X$.
  Moreover, $X = attach(D, tl: x) inter D$ for some $x in G - H$, so
  $
    H inter attach(X, tl: z)
    = H inter attach(D, tl: z x) inter attach(D, tl: z) <= Y
  $
  for some subgroup $Y in cal(Y)$, since for each $z$, either $z x in G - H$ or
  $z in G - H$. This proves @eq:green-restriction-exceptional-trace.

  Now let
  $ Q = (M_H,N_H)_(H slash D) inter (M_H,N_H)_(H,cal(Y)), $
  #source(520)
  and note that $(M_H,N_H)_(H,cal(X)) <= Q$. Consider the diagram of $R$-modules
  and $R$-homomorphisms

  #numbered-block[#green-trace-quotient-square]
  <eq:green-trace-quotient-square>

  The map $q$ is surjective, and $s$ is the natural isomorphism. Further, $t$ is
  a well-defined surjection defined by $T_(G slash H)$, since
  $ T_(G slash H) (M_H,N_H)_(H,cal(X)) <= (M,N)_(G,cal(X)). $
  The map $r$ is given by $R_(G slash H)$, using
  @eq:green-restriction-relative-trace-sum and
  @eq:green-restriction-exceptional-trace.

  We now show that the diagram @eq:green-trace-quotient-square commutes, that
  is, $q = s r t$. Let $x in (M_H,N_H)_(H slash D)$, and let $tilde(x)$ be its
  class in the quotient module. Then
  $
    (r t) tilde(x) = "class of" R_(G slash H) T_(G slash H) x
    = x + (M_H,N_H)_(H,cal(Y))
  $
  by @eq:green-restriction-trace-congruence. Then
  $(s r t) tilde(x) = x + Q = q tilde(x)$, as required.

  By @eq:green-trace-quotient-square we have
  $ ker t <= ker q = Q slash (M_H,N_H)_(H,cal(X)). $
  Let $lambda in Q$ and expand it using $epsilon_N+epsilon'_N$ on the left and
  $epsilon_M+epsilon'_M$ on the right. The three terms involving a prime are
  $(H,cal(X))$-projective by @lem:green-relative-projective-composition, since
  $lambda$ is $(H,D)$-projective and each $epsilon'$ is $(H,cal(Y))$-projective.
  The remaining term is $i_N lr((p_N lambda i_M)) p_M$. It too is
  $(H,cal(X))$-projective, since $lambda$ is $(H,cal(Y))$-projective and $i_M$
  is $(H,D)$-projective. Thus $Q=(M_H,N_H)_(H,cal(X))$, so $ker q=0$. Hence $t$
  is an isomorphism, and the lemma is proved.
]

This completes the proof of Theorem
@th:green-correspondence-stable-hom-isomorphism.

=== Uniserial Algebras and Blocks of Finite Representation Type
<ss:uniserial-algebras-finite-representation-type>
#idx("Finite representation type")
#idx("Higman's Theorem", "on indecomposable modules")

In this subsection, $k$ denotes a field of characteristic $p > 0$. A f.d.
$k$-algebra $A$ is called a $k$-algebra of _finite representation type_ if the
number of isomorphism classes of indecomposable left $A$-modules is finite. We
shall first obtain a sufficient condition for a block ideal in $k G$ to be of
finite representation type, in terms of the defect group of the block. As we
shall see, this result includes D. Higman's criterion for the group algebra
$k G$ itself to be of finite representation type (see @bib:CurtisReiner1962[CR]
64.1). The rest of the subsection will be devoted to the study of a particularly
important family of algebras of finite representation type, called uniserial
algebras. While not all block ideals of finite representation type are
uniserial, uniserial blocks play a crucial role in our analysis of blocks with
cyclic defect groups in §§~@ss:cyclic-defect-modular-representations,
@ss:cyclic-defect-periodic-resolutions.

#source(521)
#theorem[
  Let $B$ be a block ideal in $k G$, and let $D$ be a defect group of the
  corresponding block. Then $B$ is of finite representation type if and only if
  $D$ is cyclic.
] <th:block-finite-representation-type-cyclic-defect>

#proof[
  Let us assume $D = chevron.l x chevron.r$ is a cyclic group of order $d$ with
  generator $x$; then $k D$ has exactly $d$ isomorphism classes of
  indecomposable modules, by linear algebra. If $D$ is the defect group of the
  block $B$, then every $B$-module is $(G,D)$-projective, by
  @prop:trace-idempotent-relative-projectivity. Let $\{T_j: 1 <= j <= d\}$ be a
  basic set of indecomposable $k D$-modules. By the K-S-A Theorem, the number of
  isomorphism classes of indecomposable $k G$-modules $M$ such that
  $M divides T_j^G$, for $1 <= j <= d$, is finite. If $M$ is an indecomposable
  $k G$-module belonging to the block $B$, then it follows from the K-S-A
  Theorem that $M divides T_j^G$ for some $j$, $1 <= j <= d$, since $M$ is
  $(G,D)$-projective. Therefore $B$ has finite representation type. For the
  converse, see Benson @bib:Benson1984a.
]

The preceding result implies that if $G$ has a cyclic Sylow $p$-subgroup, then
$k G$ is of finite representation type, for an arbitrary field $k$ of
characteristic $p$. Higman's Theorem (@bib:CurtisReiner1962[CR] (64.1)) also
asserts that if the Sylow $p$-subgroups of $G$ are not cyclic, then $k G$ has
indecomposable modules of arbitrarily large dimension over $k$. The
corresponding result for block ideals holds, but the proof is more complicated
and will not be given here.

Let $A$ be an arbitrary f.d. $k$-algebra. We recall from
§~@ss:block-theory-background that a _principal indecomposable module_ (P.I.M.),
or _projective indecomposable module_, is an indecomposable direct summand of
$A$. Each (left) P.I.M. has the form $A e$, with $e$ a primitive idempotent in
$A$.

#definition[
  Let $A$ be a f.d. $k$-algebra. A f.g. left $A$-module $M$ is called a
  _uniserial module_ if $M$ has a unique composition series. (Every submodule
  and factor module of $M$ is then also uniserial.) We shall call $A$ a
  _uniserial_ $k$-_algebra_ if every left or right P.I.M. is a uniserial module.
] <def:uniserial-module-algebra>
#idx("Uniserial algebra", target: [@def:uniserial-module-algebra])
#idx("Uniserial module", target: [@def:uniserial-module-algebra])

We first make some simple observations. Let $N = rad A$, and let $M$ be a f.g.
left $A$-module. The _radical series_
$ M supset N M supset N^2 M supset dots $
is a chain of submodules such that each quotient $N^i M slash N^(i+1) M$ is
annihilated by $N$, and hence is a semisimple $A$-module. It follows that

$
  M "is uniserial" <=> N^i M slash N^(i+1) M "is simple or zero, for"
  i = 0,1,2,dots.
$ <eq:uniserial-radical-quotients>

For each f.g. left $A$-module $M$, the $k$-dual $M^* = op("Hom")_k lr((M,k))$ is
a f.g. right $A$-module, with the module operation defined by
$ (f a)(m) = f(a m), quad "for" f in M^*, quad a in A, quad m in M. $
It is easily checked that $M arrow M^*$ is a contravariant functor from the
category
#source(522)
of f.g. left $A$-modules to the category of f.g. right $A$-modules (see
§~@i:ss:contragredient-modules). A f.g. left $A$-module $M$ is uniserial if and
only if the right module $M^*$ is uniserial (see
Exercise~@exc:uniserial-duality). It also follows that a f.g. left $A$-module
$M$ is projective if and only if its $k$-dual $M^*$ is a f.g. injective right
module. Thus we have at once:

#proposition[
  A f.d. $k$-algebra $A$ is uniserial if and only if every indecomposable
  projective or injective left $A$-module is uniserial.
] <prop:uniserial-projectives-injectives>

The next result, due to Nakayama @bib:Nakayama1940, is proved by using the
theory of projective covers and injective hulls (see §~@i:ss:projective-covers).

#theorem[
  Let $A$ be f.d. uniserial $k$-algebra. Then $A$ has finite representation
  type. Moreover, every f.g. indecomposable left $A$-module $M$ is uniserial,
  and is a homomorphic image of an indecomposable projective module.
] <th:nakayama-uniserial-finite-representation-type>
#idx(
  "Finite representation type",
  target: [@th:nakayama-uniserial-finite-representation-type],
)

#proof(head: emph[Proof (Feit @bib:Feit1982).])[
  It is clearly sufficient to prove that every f.g. left $A$-module $M$ is a
  direct sum of uniserial modules, since every uniserial module is a homomorphic
  image of an indecomposable projective module
  (Exercise~@exc:uniserial-projective-cover). We shall use induction on
  $dim_k M$. The result is clearly true if $M$ is a simple module, so let us
  assume $M$ is not simple. Let $T$ be a maximal uniserial submodule of $M$, and
  let $U$ be a submodule which is maximal with respect to the property
  $U inter T = 0$. We may assume $0 < dim_k T < dim_k M$.

  We prove first that $M slash U$ has a simple socle. Let $U_0 supset U$, and
  assume that $U_0 slash U$ is a simple submodule of $M slash U$. Then
  $U_0 inter T != 0$ by the maximality of $U$, and we have $N(U_0 inter T) = 0$
  where $N = rad A$, since $N(U_0 inter T) subset.eq U inter T = 0$. Since $T$
  is uniserial, $U_0 inter T$ coincides with $op("soc") T$, and hence
  $U_0 = U + (U_0 inter T)$ is uniquely determined. It follows that
  $op("soc") M slash U = U_0 slash U$, and is a simple module.

  The injective hull of $M slash U$ also has a simple socle, and is
  indecomposable and hence uniserial, by @prop:uniserial-projectives-injectives,
  since $A$ is uniserial. Since $M slash U$ is isomorphic to a submodule of its
  injective hull, $M slash U$ is uniserial, so
  $F = (M slash U) slash rad(M slash U)$ is a simple module. Let $P$ be the
  projective cover of $F$; then $P$ is a P.I.M., hence uniserial, and there
  exists a commutative diagram
  #uniserial-projective-cover-triangle
  with $f$ surjective, and $ker h = U$, using the facts that $P$ is projective
  and $M slash U$ is uniserial (see Exercise~@exc:uniserial-projective-cover).

  The next step is to observe that $g(P)$ is a uniserial submodule of $M$, and
  $M = g(P) + U$ since $f$ is surjective. Then
  $M slash U tilde.equiv g(P) slash (g(P) inter U)$, so $dim_k g(P) >= dim_k T$
  since $T inter U = 0$. Moreover, $dim_k g(P) = dim_k T$, since $T$ is a
  uniserial submodule of maximal dimension. It then follows that
  $g(P) inter U = 0$, again by consideration of $dim_k M slash U$. Therefore
  $M = g(P) plus.o U$, and $U$ is a direct sum of
  #source(523)
  uniserial modules by the induction hypothesis. This completes the proof of the
  theorem.
]

As in the case of group algebras, an arbitrary f.d. $k$-algebra $A$ can be
expressed as a direct sum
$ A = A_1 plus.o dots plus.o A_m $
of indecomposable two-sided ideals, called _blocks_ or _block ideals_. These are
generated by primitive idempotents in the center of $A$, called _block
idempotents_ (see §~@sec:introduction-block-theory or @bib:CurtisReiner1962[CR]
§55). Next, let $U = A e$ be a P.I.M., where $e$ is a primitive idempotent in
$A$. The _multiplicity_ of $U$ in $A$ is, by definition, the number of summands
isomorphic to $U$ which occur in the decomposition of the left regular module
$lmodule(A, A)$ into a direct sum of P.I.M.'s. Note that the P.I.M.'s are
distributed into blocks, and each P.I.M. is contained in some block of $A$.

#theorem(title: [Morita @bib:Morita1951])[
  Let $A$ be a f.d. $k$-algebra, and let $N = rad A$. Then the following are
  equivalent:
  #case-list(
    numbering: "(i)",
    [#case[$N = c A = A c$ for some element $c in A$.]
      <case:radical-two-sided-principal>],
    [#case[$A$ is a uniserial algebra, and has the further property that for
        each block of $A$, all the P.I.M.'s in that block occur with the same
        multiplicity in $A$.]
      <case:uniserial-equal-projective-multiplicities>],
  )
] <th:morita-principal-radical-uniserial>
#idx("Morita's Theorem", target: [@th:morita-principal-radical-uniserial])

#proof[
  Assume~@case:radical-two-sided-principal, and let us first prove that $A$ is
  uniserial. We have $N^i = A c^i = c^i A$ for $i = 1,2,dots$. Let $A e$ be an
  indecomposable projective left ideal in $A$, generated by a primitive
  idempotent $e$, and let $L$ be a nonzero left ideal contained in $A e$. We
  shall prove that $L = N^i e$ for some $i$. Suppose $L subset.eq N^i e$ and
  $L subset.eq.not N^(i+1) e$. Let $a in L$ be an element such that
  $a in.not N^(i+1) e$. Since $N^i e = c^i A e$, we have
  $ a = c^i a_0, quad "where" a_0 in A e, quad a_0 in.not N e. $
  Then $A a_0 subset.eq.not N e$, and since $N e$ is the unique maximal
  submodule of $A e$, we obtain $A a_0 = A e$. Then
  $
    L supset.eq A a supset.eq A c^i a_0 = N^i a_0 = N^i A a_0
    = N^i A e = N^i e,
  $
  and hence $L = N^i e$. This proves that $A e$ is uniserial. The same argument
  shows that $e A$ is uniserial, so we have proved that $A$ is uniserial, and
  must still establish the remaining assertion in
  part~@case:uniserial-equal-projective-multiplicities.

  Let us write
  $ A = plus.o.big_i plus.o.big_(j=1)^(f(i)) A e_(i j), $
  where the $\{e_(i j)\}$ are primitive idempotents, numbered so that

  $
    A e_(i j) tilde.equiv A e_(i' j') <=> e_(i j) A tilde.equiv e_(i' j') A
    <=> i = i'.
  $ <eq:primitive-idempotent-isomorphism-groups>
  #source(524)
  Then $f(i)$ is the multiplicity of $A e_(i j)$ as a direct summand of
  $lmodule(A, A)$, for each $i,j$.

  The P.I.M.'s $\{A e_(i j)\}$ have the following properties, which hold because
  $A$ is uniserial and (by hypothesis) $N^j = c^j A = A c^j$ for each $j >= 1$.
]

#lemma[
  We have#footnote[These formulas hold for all $j >= 1$ for which the
    corresponding left ideals are different from zero.] for $j >= 1$,
  #case-list(
    numbering: "(i)",
    [#case[$A c^j e_(k i) tilde.equiv A c^j e_(k 1)$, $1 <= i <= f(k)$.]
      <case:radical-left-ideal-isomorphic-copies>],
    [#case[$A e_(k i) c^j tilde.equiv A e_(k 1) c^j$, $1 <= i <= f(k)$.]
      <case:socle-left-ideal-isomorphic-copies>],
    [#case[$A c^j e_(k 1) tilde.equiv.not A c^j e_(l 1)$ if $k != l$.]
      <case:radical-left-ideal-distinct-types>],
    [#case[$A e_(k 1) c^j tilde.equiv.not A e_(l 1) c^j$ if $k != l$.]
      <case:socle-left-ideal-distinct-types>],
    [#case[$A c^j e_(k i)$ and $A e_(k i) c^j$ are indecomposable left ideals.]
      <case:principal-radical-ideals-indecomposable>],
  )
] <lem:principal-radical-ideal-isomorphism-types>

#proof(head: emph[Sketch of proof.])[
  Since $A e_(k i) tilde.equiv A e_(k 1)$, the terms of their _radical series_
  $\{N^j e_(k i)\}$ and $\{N^j e_(k 1)\}$ are isomorphic, and the terms of their
  _socle series_ $A e_(k i) inter r(N^j)$ and $A e_(k 1) inter r(N^j)$ are also
  isomorphic. The first two statements of
  @lem:principal-radical-ideal-isomorphism-types follow from these remarks,
  since $N^j = c^j A = A c^j$. For the proof of
  part~@case:radical-left-ideal-distinct-types, assume that
  $A c^j e_(k 1) tilde.equiv A c^j e_(l 1)$. Then
  $N^j e_(k 1) tilde.equiv N^j e_(l 1)$. Moreover,
  $N^j e_(k 1) slash N^(j+1) e_(k 1)
  tilde.equiv N^j e_(l 1) slash N^(j+1) e_(l 1) tilde.equiv A e slash N e$
  for some primitive idempotent $e$, since $A$ is uniserial. Consequently there
  exist elements $a in e N^j e_(k 1)$ and $b in e N^j e_(l 1)$ such that
  $a,b in.not N^(j+1)$ and
  $ e N^j = a A = b A = a e_(k 1) A = b e_(l 1) A. $
  Then there exist surjective homomorphisms
  $ e_(k 1) A arrow e N^j quad "and" quad e_(l 1) A arrow e N^j, $
  and it follows that $k = l$ by @eq:primitive-idempotent-isomorphism-groups.
  The other statements are easily proved, and are left as exercises.
]

Continuing with the proof of Theorem @th:morita-principal-radical-uniserial, we
now have
$
  N^j = plus.o.big_(k=1)^d plus.o.big_(i=1)^(f(k)) A c^j e_(k i)
  = plus.o.big_(l=1)^d plus.o.big_(i'=1)^(f(l)) A e_(l i') c^j,
  quad "for" j >= 1.
$
Since the summands are indecomposable, the K-S-A Theorem and
@lem:principal-radical-ideal-isomorphism-types imply that there exists a
permutation $pi$ of $\{1,2,dots,d\}$ such that
$
  A c^j e_(k i) tilde.equiv A e_(pi(k) i') c^j quad "and" quad f(k) = f(pi(k)),
$
where we omit the terms which are zero. We also have
$
  N^j e_(k 1) slash N^(j+1) e_(k 1)
  tilde.equiv A e_(pi(k),1) slash N e_(pi(k),1) quad "if" A c^j e_(k 1) != 0.
$
Since the block ideals of $A$ are the sums of linkage classes of P.I.M.'s (see
§~@sec:introduction-block-theory or @bib:CurtisReiner1962[CR] §55), it follows
that the multiplicities $f(k)$ are the same for the P.I.M.'s $\{A e_(k i)\}$
belonging to a given block ideal. Thus part~@case:radical-two-sided-principal
implies part~@case:uniserial-equal-projective-multiplicities, as asserted in the
theorem.

#source(525)
Conversely, let us assume~@case:uniserial-equal-projective-multiplicities and
prove~@case:radical-two-sided-principal. We put
$ N e_(k 1) slash N^2 e_(k 1) tilde.equiv A e_(phi(k) 1) slash N e_(phi(k) 1). $
As before, $k != l$ implies $phi(k) != phi(l)$, and since $A e_(k 1)$ and
$A e_(phi(k))$ are contained in the same block, we have $f(k) = f(phi(k))$. It
follows that for all $k$ and $i$, there exists
$c_(k i) in e_(phi(k) i) N e_(k i)$, with $c_(k i) in.not N^2$ and such that
$ A c_(k i) tilde.equiv N e_(k i) quad "and" quad c_(k i) A = e_(phi(k) i) N, $
since $A$ is uniserial. We then put $c = sum_(k,i) c_(k i)$, and obtain
$ A c = sum A c_(k i), $
and therefore $N = A c$ by the preceding remarks. A similar argument shows that
$N = c A$, and the proof of the theorem is completed.

The next result shows that the composition factors of the P.I.M.'s in a given
block of a uniserial symmetric algebra occur in a periodic manner. This will be
applied in §~@ss:cyclic-defect-periodic-resolutions to obtain a periodic
projective resolution of the trivial $R G$-module, in case $G$ has a cyclic
Sylow $p$-subgroup.

#theorem(title: [Morita @bib:Morita1951])[
  Let $A$ be a f.d. $k$-algebra which is uniserial and symmetric (see
  §~@i:ss:frobenius-symmetric-algebras), and let $N = rad A$. Let
  $\{U_1,dots,U_m\}$ be a basic set of P.I.M.'s belonging to an arbitrary block
  of $A$, and let $\{F_1,dots,F_m\}$ be the corresponding simple modules, so
  that $F_i = U_i slash rad U_i$, $1 <= i <= m$. Then the composition lengths of
  any two of the modules $\{U_i\}$ are equal. Moreover, for a suitable ordering
  of $\{1,dots,m\}$ the composition factors of the $U_i$ occur as follows:
  $
    U_1 & : F_1,F_2,dots,F_m,F_1,dots,F_m,dots,F_1,dots,F_m,F_1 \
    U_2 & : F_2,F_3,dots,F_1,F_2,dots,F_1,dots,F_2,dots,F_1,F_2 \
        & dots \
    U_m & : F_m,F_1,dots,F_(m-1),F_m,dots,F_(m-1),dots,F_m,dots,F_(m-1),F_m,
  $
  where, for example, $F_1,F_2,dots,F_m,dots,F_1,dots,F_m,F_1$ are the factors
  of the radical series $U_1 supset N U_1 supset N^2 U_1 supset dots$ of $U_1$.
] <th:uniserial-symmetric-projective-composition-cycles>
#idx(
  "Morita's Theorem",
  target: [@th:uniserial-symmetric-projective-composition-cycles],
)
#idx(
  "Uniserial block",
  target: [@th:uniserial-symmetric-projective-composition-cycles],
)
#idx(
  "p-Blocks",
  "uniserial",
  target: [@th:uniserial-symmetric-projective-composition-cycles],
)

The proof uses some facts about symmetric algebras from
§~@i:ss:frobenius-symmetric-algebras. We first prove:

#lemma[
  Let $A$ satisfy the hypotheses of Theorem
  @th:uniserial-symmetric-projective-composition-cycles. Let $N = rad A$, and
  let $e$ and $f$ be primitive idempotents such that
  $ N e slash N^2 e tilde.equiv A f slash N f. $
  Then we have
  $ N e tilde.equiv A f slash op("soc") A f. $
] <lem:uniserial-symmetric-radical-socle-quotient>

#proof[
  #source(526)
  Since $A$ is uniserial, we have
  $ N e = A b quad "and" quad f N = b A $
  for some element $b in f N e$ such that $b in.not N^2$ (see the last part of
  the proof of Theorem @th:morita-principal-radical-uniserial). Then the map
  $a f arrow a f b$ (for $a in A$) is a surjective homomorphism from $A f$ to
  $A b = N e$, and hence defines an isomorphism
  $ A f slash (A f inter l(b)) tilde.equiv N e, $
  where#footnote[$l( )$ denotes left annihilator, and $r( )$ right annihilator.]
  $l(b) = \{x in A: x b = 0\}$. We then have
  $ A f inter l(b) = A f inter l(N), $
  since $l(N) subset.eq l(b)$, and $x in A f inter l(b)$ implies
  $x N = x f N = x b A = 0$. Moreover, $l(N) = r(N)$ by
  @i:prop:frobenius-algebra-properties since $A$ is a symmetric algebra, and we
  obtain
  $ A f inter l(N) = A f inter r(N) = op("soc") A f, $
  completing the proof.
]

#proof(head: emph[Proof of Theorem
  @th:uniserial-symmetric-projective-composition-cycles.])[
  A semisimple block has one simple P.I.M., of length one, and satisfies the
  assertion. We may therefore omit such blocks. No remaining P.I.M. is simple: a
  simple projective is also injective, since $A$ is symmetric, and its
  isomorphism class is then an isolated linkage class and a block. Thus every
  remaining P.I.M. has a nonzero first radical layer. The successor defined by
  its simple radical top is a permutation, since right uniseriality makes each
  simple type have at most one predecessor. Consequently there exists a sequence
  of nonisomorphic P.I.M.'s#ed-note[
    The displayed successor cycle is unavailable for a simple P.I.M., whose
    first radical layer is zero. For the symmetric top–socle property used here,
    see @i:prop:symmetric-projective-top-socle.
  ] $\{U_1,dots,U_m\}$ such that
  $
    N U_1 slash N^2 U_1 tilde.equiv U_2 slash N U_2, \
    N U_2 slash N^2 U_2 tilde.equiv U_3 slash N U_3, quad dots, quad
    N U_m slash N^2 U_m tilde.equiv U_1 slash N U_1,
  $
  for some integer $m >= 1$, with the understanding that in case $m = 1$, we
  have $N U_1 slash N^2 U_1 tilde.equiv U_1 slash N U_1$. Then
  $U_i slash N U_i tilde.equiv op("soc") U_i$ for $1 <= i <= m$ by
  @i:prop:symmetric-projective-top-socle, since $A$ is a symmetric algebra. It
  follows by Lemma @lem:uniserial-symmetric-radical-socle-quotient that the
  composition factors of $\{U_1,dots,U_m\}$ occur as asserted in
  @th:uniserial-symmetric-projective-composition-cycles. Then no simple module
  other than $\{F_1,dots,F_m\}$ can occur as a composition factor of
  $\{U_1,dots,U_m\}$ and hence $\{U_1,dots,U_m\}$ is a basic set of P.I.M.'s
  belonging to a block ideal of $A$ (see §~@ss:pim-block-linkage or
  @bib:CurtisReiner1962[CR] §55). Upon splitting off this block ideal, we can
  repeat the argument with the remaining P.I.M.'s, and the theorem follows.
]

#corollary[
  Let $A$ be a f.d. $k$-algebra which is uniserial, symmetric, and
  indecomposable as a two-sided ideal. Assume that its radical $N$ has the
  property that $N = A c = c A$ for some element $c in N$, and let $N^q = 0$,
  $N^(q-1) != 0$. Then the composition length of each indecomposable projective
  left $A$-module is $q$.
] <cor:uniserial-symmetric-projective-length>

#proof[
  For each left P.I.M. $A e$, with $e^2 = e$, we have $N^j e = A c^j e$. The
  result
  #source(527)
  follows from the preceding theorem and the formula for $N^j$ in the proof of
  Theorem @th:morita-principal-radical-uniserial.
]

The last result in this subsection is another useful criterion, due to Michler
@bib:Michler1976, for a $k$-algebra to be uniserial.

#theorem[
  Let $A$ be a f.d. $k$-algebra of finite representation type. Assume that $k$
  is a splitting field for $A$, and that $A$ has exactly one simple module, up
  to isomorphism. Then $A$ is a uniserial $k$-algebra.
] <th:finite-type-one-simple-uniserial>
#idx("Uniserial algebra", target: [@th:finite-type-one-simple-uniserial])

#proof[
  The hypothesis implies that $A$ has exactly one P.I.M. $U$, up to isomorphism.
  Since $A$ is a direct sum of $n$ copies of $U$, $U$ is a generator of the
  category $cal(M)_A$, by @i:lem:morita-generator-evaluation(iii). Let
  $U = A e$, with $e$ an idempotent. Then
  $
    A tilde.equiv M_n lr((B)), quad "where"
    B tilde.equiv (op("End")_A U)^"op" tilde.equiv e A e,
  $
  and $B$ is of finite representation type, by Morita's Theorem @i:th:morita.

  Let $J = rad B$. Then $B$ is a local $k$-algebra, by
  @i:prop:indecomposable-local-endomorphism-ring. Letting $a arrow overline(a)$
  denote the natural map from $A$ to $A slash rad A$, we have
  $
    (overline(e) overline(A) overline(e))^"op"
    tilde.equiv op("End")_(overline(A)) overline(A) overline(e) tilde.equiv k
  $
  since $overline(A) overline(e)$ is a simple $overline(A)$-module and $k$ is a
  splitting field. Since $rad e A e = e(rad A)e$ by
  @i:prop:radical-idempotent-corner, we obtain
  $
    B slash J tilde.equiv
    (overline(e) overline(A) overline(e)) tilde.equiv k,
  $
  and hence $B = k plus.o J$ (where we identify $k$ with $k dot 1$).

  Since $B$ has finite representation type, $B slash J^2$ has the same property,
  and is a commutative $k$-algebra. We shall prove that
  $dim_k lr((J slash J^2)) <= 1$ (see Lemma
  @lem:finite-type-local-radical-dimension below). If this dimension is zero,
  Nakayama's Lemma gives $J=0$, so $A tilde.equiv M_n lr((k))$ is uniserial.
  Otherwise choose $c in J$, $c in.not J^2$. Then $B c+J^2=J$, and Nakayama's
  Lemma @i:lem:nakayama gives $J=B c=c B$. Under $A tilde.equiv M_n lr((B))$,
  put $d=op("diag") lr((c,dots,c))$. Then $rad A=M_n lr((J))=A d=d A$, by
  @i:prop:radical-matrix-ring. Hence $A$ is uniserial by
  @th:morita-principal-radical-uniserial, completing the proof.#ed-note[
    In $A=M_2 lr((k[t] slash (t^2)))$, the corner element $t e_(1 1)$ generates
    only one column on the left, whereas $rad A$ has all four entries in $(t)$;
    compare @i:prop:radical-matrix-ring.
  ] It remains to prove:
]

#lemma[
  Let $B = k + J$, where $J = rad B$, and assume that $B$ has finite
  representation type. Then $dim_k lr((J slash J^2)) <= 1$.
] <lem:finite-type-local-radical-dimension>

The proof is a simple modification of @bib:CurtisReiner1962[CR] 64.3. We shall
prove that if $dim_k J slash J^2 > 1$, then $B slash J^2$ has indecomposable
modules of arbitrarily large dimension over $k$, contradicting the assumption
that $B$ is of finite representation type.

We have $B slash J^2 = (k plus.o J) slash J^2$. Let $u_1,dots,u_m$ be a
$k$-basis of $J slash J^2$, and suppose that $m > 1$. Let $d$ be a positive
integer, and let $M$ be the $k$-space with basis
$ x_0,x_1,dots,x_d,y_1,dots,y_d. $

#source(528)
To make $M$ into a $(B slash J^2)$-module, set
$
  u_j x_i = 0 "for all" i "and" j, quad
  u_j y_i = 0 "for" j > 2 "and all" i, \
  u_1 y_i = x_i, quad "and" quad u_2 y_i = x_(i-1), quad 1 <= i <= d.
$
It is easily checked that $M$ is a $(B slash J^2)$-module, and we shall prove it
is indecomposable. We have $M = X plus.o Y$, where $X$ and $Y$ are generated by
the basis elements $\{x_i\}$ and $\{y_j\}$, respectively. Let $pi$ be the
projection $M arrow Y$. Note that the maps defined by $u_1$ and $u_2$ are
injective from $Y$ to $X$, and map $X$ to $0$. Suppose $M = M_1 plus.o M_2$, for
nonzero $(B slash J^2)$-submodules $M_1$ and $M_2$, and let
$ dim_k pi M_1 = m_1, quad dim_k pi M_2 = m_2. $
We have $u_1 M_1 subset.eq M_1$ and $u_1 M_1 = u_1 pi M_1$ so
$dim u_1 M_1 = m_1$. We also note that $u_2 M_1$ contains a vector not in
$u_1 M_1$, and it follows that $dim_k M_1 >= 2 m_1 + 1$,
$dim_k M_2 >= 2 m_2 + 1$. Since $pi M = pi M_1 + pi M_2$, we have
$m_1 + m_2 >= d$, and hence $dim_k M >= 2(m_1 + m_2) + 2 > 2 d + 1$, which is
impossible. Thus $M$ is indecomposable, and the lemma is proved.

=== Modular Representations in Blocks with Cyclic Defect Groups
<ss:cyclic-defect-modular-representations>

In this subsection, $G$ denotes a finite group, and $k$ a perfect field of
characteristic $p > 0$, which is sufficiently large relative to $G$. We shall
prove a theorem which gives the number of simple and indecomposable
$k G$-modules in a $p$-block of $G$ with a cyclic defect group $D != 1$, in
terms of the inertial index of the block (see @def:block-inertial-index). One
also has information about the number of ordinary characters in such a block, as
well as a way of constructing the indecomposable modules themselves (see Dade
@bib:Dade1966, Janusz @bib:Janusz1969, and Feit @bib:Feit1982). Our proof, which
is due to Michler @bib:Michler1976, focuses on the use of the Green
correspondence to transfer information about indecomposable modules in blocks of
subgroups to blocks of $G$ itself. The main result is as follows:

#theorem[
  Let $upright(sans(B))$ be a block of $k G$-modules with a cyclic defect group
  $D != 1$, and let $e$ denote the inertial index of $upright(sans(B))$ (see
  @def:block-inertial-index). Then the following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[$e divides p - 1$.]
      <case:cyclic-defect-inertial-index-divisibility>],
    [#case[$upright(sans(B))$ contains exactly $e$ isomorphism classes of simple
        $k G$-modules.]
      <case:cyclic-defect-simple-module-count>],
    [#case[$upright(sans(B))$ is of finite representation type, and contains
        exactly $e abs(D)$ isomorphism classes of indecomposable $k G$-modules.]
      <case:cyclic-defect-indecomposable-module-count>],
  )
] <th:cyclic-defect-block-module-counts>
#idx("Cyclic defect group", target: [@th:cyclic-defect-block-module-counts])
#idx("Inertial index", target: [@th:cyclic-defect-block-module-counts])
#idx(
  "p-Blocks",
  "inertial index of",
  target: [@th:cyclic-defect-block-module-counts],
)

The proof will occupy the entire subsection. We remark incidentally, that blocks
having a trivial defect group are simply blocks of defect zero, and the
corresponding theorem has already been established (see
Exercise~@exc:simple-block-algebra-trivial-defect).

We begin with a proof of part~@case:cyclic-defect-inertial-index-divisibility of
the main theorem.

#source(529)
#proposition[
  The inertial index $e$ of $upright(sans(B))$ divides $p - 1$.
] <prop:cyclic-defect-inertial-index-divides-p-minus-one>

#proof[
  Since $D$ is cyclic, $D C_G lr((D)) = C_G lr((D))$. By
  @def:block-inertial-index, we have
  $ e = abs(op("Stab")_(N_G lr((D))) b' colon C_G lr((D))), $
  where $b'$ is a block idempotent in $k C_G lr((D))$ belonging to a block
  $upright(sans(B))'$ of $C_G lr((D))$ with defect group $D$, such that
  $(upright(sans(B))')^G = upright(sans(B))$. By
  @th:block-inertial-index-prime-to-p, we have $e equiv.not 0 (mod p)$. On the
  other hand, $e$ divides the order of the quotient group
  $N_G lr((D)) slash C_G lr((D))$, which is isomorphic to a subgroup of the
  automorphism group of the cyclic group $D$. If $D$ has order $p^d$, its
  automorphism group has order $p^(d-1)(p-1)$. The result follows by combining
  these observations.
]

#definition[
  A block $upright(sans(B))$ of $k G$-modules is called _uniserial_ if the
  corresponding block ideal $B$ is a uniserial $k$-algebra (see
  @def:uniserial-module-algebra).
] <def:uniserial-block>
#idx("Uniserial block", target: [@def:uniserial-block])
#idx("p-Blocks", "uniserial", target: [@def:uniserial-block])

We note that a uniserial block ideal $B$ has finite representation type, and
that every indecomposable $B$-module is a homomorphic image of a P.I.M. (see
@th:nakayama-uniserial-finite-representation-type).

Some properties of uniserial block ideals are given in
§~@ss:uniserial-algebras-finite-representation-type. While blocks with cyclic
defect groups are not necessarily uniserial, the consideration of uniserial
blocks is essential for the proof of the main theorem.

We continue the proof of Theorem @th:cyclic-defect-block-module-counts by
considering the important and interesting case of a normal cyclic defect group,
and establish a stronger result in this situation. Incidentally,
@case:normal-cyclic-defect-simple-module-count of the proof is a nice
application of the general version of Clifford theory from
§~@i:ss:clifford-systems.

#proposition[
  Let $upright(sans(B))$ be a block of $k G$-modules with a cyclic defect group
  $D$ such that $D ⊴ G$. Then $upright(sans(B))$ is a uniserial block, and
  satisfies parts from @case:cyclic-defect-inertial-index-divisibility through
  @case:cyclic-defect-indecomposable-module-count
  of Theorem @th:cyclic-defect-block-module-counts.
] <prop:normal-cyclic-defect-uniserial-module-counts>

#proof[
  #case-list(
    numbering: "Step 1.",
    [#case[
      We show first that $upright(sans(B))$ is uniserial, by proving that
      $rad B$ satisfies the hypothesis of
      @th:morita-principal-radical-uniserial, where $B$ is the block ideal in
      $k G$ associated with $upright(sans(B))$. Let $I$ denote the augmentation
      ideal of the group algebra $k D$ (see @i:th:p-group-algebra-local). If
      $D = chevron.l x chevron.r$, then clearly $I = (x-1) k D$. We shall prove

      $ rad B = (x-1) B = B(x-1). $
      <eq:normal-cyclic-defect-block-radical>

      Since $D ⊴ G$, we have $g I g^(-1) = I$ for all $g in G$, and it follows
      that $I B = B I$. Then $I B$ is a nilpotent two-sided ideal in $B$, since
      $I$ is the radical of $k D$ by @i:th:p-group-algebra-local. Then
      $I B subset.eq rad B$, and we shall prove equality by showing that
      $B slash I B$ is a semisimple algebra. Let $tau: k G arrow k(G slash D)$
      be the natural map. Then $ker tau = I k G$ by the proof of
      @i:prop:normal-p-subgroup-radical-kernel. It is then easily checked that
      $ I B = B inter ker tau, $
      using the fact that $B = b(k G)$ for a block idempotent $b$.
      #source(530)
      Now let $M$ be an arbitrary f.g. $B slash I B$-module. Then $M$ can be
      viewed as a $B$-module on which $D$ acts trivially. Since $D$ is the
      defect group of $upright(sans(B))$, $M$ is $(G,D)$-projective by
      @prop:trace-idempotent-relative-projectivity, and we have by
      @i:th:gaschutz-relative-projectivity
      $ sum_(g in G slash D) g gamma g^(-1) = op("id")_M $
      for some $gamma in op("End")_(k D) M$. Since $D$ acts trivially on $M$,
      the action of $g in G$ on $M$ is given by
      $ g m = tau(g)m, quad "for all" m in M, $
      and the preceding formula becomes
      $ sum_(tau(g) in G slash D) tau(g) gamma tau(g)^(-1) = op("id")_M $
      where the sum is taken over the factor group $G slash D$. This proves that
      $M$ is a projective $k(G slash D)$-module. Therefore every f.g.
      $(B slash I B)$-module is projective, and hence $B slash I B$ is a
      semisimple algebra. This completes the proof of
      @eq:normal-cyclic-defect-block-radical, and it follows by
      @th:morita-principal-radical-uniserial that $upright(sans(B))$ is a
      uniserial block.
    ] <case:normal-cyclic-defect-uniserial>],
    [#case[
      We have already proved in
      @prop:cyclic-defect-inertial-index-divides-p-minus-one that
      $e divides p - 1$. We next show, using the Clifford theory in
      §~@i:ss:clifford-systems, that the number of isomorphism classes of simple
      modules in $upright(sans(B))$ is equal to $e$. We begin with the
      observation that $C_G lr((D)) ⊴ G$ since $D ⊴ G$. By Theorem
      @th:extended-brauer-first-main(ii), the block ideal $B$ covers a unique
      conjugacy class of block ideals $\{B'\}$ in $k C_G lr((D))$, each of which
      has defect group $D$. Moreover, each block ideal $B'$ of $k C_G lr((D))$
      with defect group $D$ has exactly one simple module, by
      @th:centralizer-block-canonical-character.

      Now let $F$ be a simple $B$-module. By Clifford's Theorem
      @i:th:clifford-theorem, the restriction $F_(C_G lr((D)))$ is a semisimple
      $k C_G lr((D))$-module, and we have
      $ F_(C_G lr((D))) = plus.o.big attach(L, tl: x), $
      where the sum is taken over the $G$-conjugates
      $\{attach(L, tl: x): x in G\}$ of a simple summand $L$ of
      $F_(C_G lr((D)))$, and distinct conjugates occur with the same
      multiplicity.

      Let $b$ be the block idempotent in $B$, and $b'$ the block idempotent in
      $B'$, for a representative $B'$ of the conjugacy class of block ideals
      $C_G lr((D))$ covered by $B$. Then by Theorem
      @th:normal-subgroup-covering-blocks and Corollary
      @cor:covering-block-module-criterion we may assume that $L$ belongs to the
      block $upright(sans(B))'$, and $b' L != 0$. Then
      $attach(b', tl: x) dot attach(L, tl: x) != 0$ for each $x in G$, proving
      that $attach(L, tl: x)$ belongs to the conjugate block
      $attach(upright(sans(B))', tl: x)$ for each $x in G$. Since
      $upright(sans(B))'$ has, up to isomorphism, only the one simple module
      $L$, it follows that
      $ attach(L, tl: x) tilde.equiv L <=> attach(b', tl: x) = b'. $
      Thus we have $op("Stab")_G L = op("Stab")_G b'$. Letting $T$ denote this
      stabilizer, we have $C_G lr((D)) ⊴ T$, and the quotient group
      $T slash C_G lr((D))$ is a subgroup of the automorphism group of $D$.
      Since $D$ is cyclic of order $p^d$, its automorphism group is abelian of
      #source(531)
      order $p^(d-1)(p-1)$, and contains a cyclic subgroup of order $p-1$. Since
      $T$ is the stabilizer of $b'$, the order of $T slash C_G lr((D))$ is the
      inertial index $e$ of the block $upright(sans(B))$, by
      @def:block-inertial-index, and hence divides $p-1$. It follows that
      $T slash C_G lr((D))$ is a cyclic group of order dividing $p-1$.

      We are now ready to apply Clifford theory. We first observe that the
      simple $B$-modules $F$ are precisely the composition factors of the
      induced module $L^G$, where $L$ is the unique simple $B'$-module in a
      block ideal $B'$ of defect group $D$ covered by $B$. This follows since
      $L divides F_(C_G lr((D)))$ for every simple $B$-module $F$, by the
      preceding discussion, so $op("Hom")_(k G) lr((L^G,F)) != 0$ by Frobenius
      reciprocity @i:prop:graded-frobenius-reciprocity. Thus every simple
      $B$-module $F$ occurs as a composition factor of $L^G$. Moreover, every
      composition factor of $L^G$ is a $B$-module, since $B$ is the unique block
      ideal covering $B'$, by @th:normal-subgroup-covering-blocks(iv).

      It follows at once from @i:prop:graded-clifford-theorem and
      @i:th:graded-clifford-correspondence that the number of isomorphism
      classes of composition factors of $L^G$ is equal to the number of
      isomorphism classes of simple submodules of $L^T$, where
      $T = op("Stab")_G L$, and that there is a lattice isomorphism, preserving
      module homomorphisms, from the lattice of left ideals of
      $E = op("End")_(k T) lr((L^T))$ to the lattice of $k G$-modules of $L^G$.
      We shall prove that $E tilde.equiv k(T slash C_G lr((D)))$, and that $E$
      is a split semisimple $k$-algebra. By the proof of
      @i:th:clifford-projective-factorization, $E$ is isomorphic to a twisted
      group algebra $k(T slash C_G lr((D)))_alpha$ of the cyclic group
      $T slash C_G lr((D))$, of order dividing $p-1$, over the sufficiently
      large field $k$ of characteristic $p$. Although the results
      @i:prop:invariant-character-extension and
      @i:prop:multiplier-noncyclic-sylow were proved for algebraically closed
      fields of characteristic zero, they apply equally well in this situation,
      and show that the factor set $alpha$ can be taken to be the trivial factor
      set. Thus $E$ is a split semisimple group algebra with exactly
      $e = abs(T slash C_G lr((D)))$ simple modules. Moreover, $L^T$ is
      semisimple by @i:th:graded-clifford-correspondence, and it follows that
      $L^T$, and hence $L^G$ have exactly $e$ nonisomorphic composition factors.
      This completes the proof of
      @case:normal-cyclic-defect-simple-module-count.
    ] <case:normal-cyclic-defect-simple-module-count>],
    [#case[
      It remains to prove that the number of indecomposable $B$-modules is
      $abs(D)e$. By @case:normal-cyclic-defect-uniserial and
      @case:normal-cyclic-defect-simple-module-count, $B$ is a uniserial block
      ideal, with exactly $e$ simple modules. From
      @th:nakayama-uniserial-finite-representation-type, each indecomposable
      $B$-module is a homomorphic image of an indecomposable projective module.
      There are $e$ isomorphism classes of indecomposable projective
      $B$-modules, and each one has composition length $abs(D)$ by
      @cor:uniserial-symmetric-projective-length, since
      $rad B = (x-1)B = B(x-1)$ by @case:normal-cyclic-defect-uniserial. It
      follows that the number of indecomposable $B$-modules is exactly
      $abs(D)e$, as required.
    ] <case:normal-cyclic-defect-indecomposable-count>],
  )
]

The preceding result @prop:normal-cyclic-defect-uniserial-module-counts applies
to the block of $N_G lr((D))$, with defect group $D$, corresponding via
@th:brauer-first-main-theorem to the given block $upright(sans(B))$ in Theorem
@th:cyclic-defect-block-module-counts. The next task is to transfer this
information from $N_G lr((D))$ to $G$. This is not straightforward, however, for
the following reason. Suppose we have information about simple and
indecomposable modules in a block of $N_G lr((D))$ with defect group $D$,
corresponding to $upright(sans(B))$ as in @th:brauer-first-main-theorem. The
indecomposable modules will have vertices contained in $D$, by
@prop:trace-idempotent-relative-projectivity, but the Green Correspondence
@i:th:green-correspondence applies only to those indecomposable modules in
$upright(sans(B))$ whose vertices are not in the family
$\{attach(D, tl: x) inter D: x in G - N_G lr((D))\}$ (see
@i:eq:green-subgroup-families), and does not apply to all indecomposable
nonprojective modules in $upright(sans(B))$, in general.

To resolve this difficulty, we shall apply the Green Correspondence to a certain
#source(532)
subgroup $H >= N_G lr((D))$. The right choice is
$ H = N_G lr((Y)), $
where $Y$ is the unique minimal subgroup of $D$ of order $p$. Then
$ N_G lr((D)) <= H, $
since $Y$ is a characteristic subgroup of $D$; hence $(G,H,D)$ is an admissible
triple of groups for the Green Correspondence (see
@i:def:green-admissible-triple). For the rest of this subsection, we keep to
this choice of $Y$ and $H$. If $H=G$, the Green Correspondence is the identity,
and all its applications below are immediate; the defining families
$cal(X),cal(Y)$ are then empty. In the following calculation of these families
we assume $H<G$.

Before applying the Green Correspondence, let us describe the families of
subgroups $\{cal(X),cal(Y),cal(A)\}$ in @i:def:green-admissible-triple. We have

$
  cal(X) = \{attach(D, tl: x) inter D: x in G - H\} = \{1\},
$ <eq:cyclic-defect-green-exceptional-intersections>

since $attach(D, tl: x) inter D != 1$ implies $Y <= attach(D, tl: x) inter D$
and hence $x in H = N_G lr((Y))$. We next have

$ cal(Y) = \{attach(D, tl: x) inter H: x in G - H\}; $
<eq:cyclic-defect-green-restriction-family>

then $cal(Y)$ contains no nontrivial $H$-conjugates of subgroups of $D$.
Finally,

$
  cal(A) = \{D^* <= D: D^* lt.eq.not_G cal(X)\}
  = \{D^* <= D: D^* != 1\}
$ <eq:cyclic-defect-green-vertex-family>

by @eq:cyclic-defect-green-exceptional-intersections. We next recall that the
Green Correspondence @i:th:green-correspondence defines a bijection between
isomorphism classes of indecomposable $k G$-modules and indecomposable
$k H$-modules, with vertices in $cal(A)$. Corresponding modules
$M in op("Ind") k G$ and $N in op("Ind") k H$ have the same vertex, and we shall
write
$ f(M) = N quad "and" quad g(N) = M. $
By @i:th:green-correspondence we have
$
  M_H = f(M) plus.o O(cal(Y)) quad "and" quad
  N^G = g(N) plus.o O(cal(X)),
$
where $O(cal(Y))$ denotes an $(H,cal(Y))$-projective $k H$-module, and
$O(cal(X))$ a $(G,cal(X))$-projective $k G$-module (see
@i:def:family-relative-projectivity). By
@i:lem:family-relative-projectivity-vertex, it follows that an
$(H,cal(Y))$-projective $k H$-module is a direct sum of indecomposable modules
whose vertices are $H$-conjugate to subgroups of groups belonging to $cal(Y)$.

The critical question is whether the Green Correspondence is compatible with the
distribution of modules in blocks. Fortunately, we have:

#proposition[
  Let $upright(sans(B))$ be a block of $k G$-modules with cyclic defect group
  $D$, and let $H = N_G lr((Y))$, where $Y$ is the subgroup of $D$ of order $p$.
  Then:
  #case-list(
    numbering: "(i)",
    [#case[There exists a unique block $upright(sans(B))'$ of $k H$-modules with
        defect group $D$, such that $(upright(sans(B))')^G = upright(sans(B))$.]
      <case:cyclic-defect-green-block-existence>],
    [#case[
      #source(533)
      The Green Correspondence defines a bijection between the sets of
      indecomposable nonprojective modules in the blocks $upright(sans(B))$ and
      $upright(sans(B))'$.
    ] <case:cyclic-defect-green-block-bijection>],
    [#case[
      Let $M in upright(sans(B))$ and $N in upright(sans(B))'$ be indecomposable
      non-projective modules such that $f(M) = N$ and $g(N) = M$, as in
      part~@case:cyclic-defect-green-block-bijection. Then we have
      $ M_H = N plus.o N^* quad "and" quad N^G = M plus.o M^*, $
      where $N^*$ is a direct sum of projective $k H$-modules and of modules
      belonging to $H$-blocks different from $upright(sans(B))'$, while $M^*$ is
      a projective $k G$-module.
    ] <case:cyclic-defect-green-block-complement>],
  )
] <prop:cyclic-defect-green-block-compatibility>
#idx(
  "Green Correspondence",
  target: [@prop:cyclic-defect-green-block-compatibility],
)

#proof(head: emph[Proof (Alperin).])[
  The first statement follows from the Extended First Main Theorem
  @th:extended-brauer-first-main(i), since $H >= N_G lr((D))$.

  We next consider an indecomposable nonprojective $k H$-module $N$ in the block
  $upright(sans(B))'$ defined in part~@case:cyclic-defect-green-block-existence.
  Then $op("vtx") N != 1$, so $N$ corresponds by @i:th:green-correspondence to a
  $k G$-module $M$ with the same vertex. Thus $M$ is indecomposable and not
  projective, and we must prove that $M$ is in $upright(sans(B))$. Let
  $D' in op("vtx") N$; then $N divides M_H$ and we may assume that $D' <= D$, by
  @prop:trace-idempotent-relative-projectivity. Then
  $ H = N_G lr((Y)) >= C_G lr((Y)) >= C_G lr((D')) $
  since $D' != 1$ and $Y <= D'$. It follows that $M in upright(sans(B))$ by
  @th:brauer-correspondence-restriction-vertices, since
  $upright(sans(B)) = (upright(sans(B))')^G$.

  Now let $M$ be an indecomposable nonprojective $k G$-module in the block
  $upright(sans(B))$; then $op("vtx") M != 1$, and $op("vtx") M <=_G D$ by
  @prop:trace-idempotent-relative-projectivity, so $M$ corresponds to an
  indecomposable nonprojective $k H$-module $N$ with the same vertex $D' <= D$.
  Then $C_G lr((D')) <= H$, so $N$ belongs to a block $upright(sans(B))''$ of
  $H$ such that $(upright(sans(B))'')^G = upright(sans(B))$, and we have to
  prove that $upright(sans(B))'' = upright(sans(B))'$. If $D''$ is a defect
  group of $upright(sans(B))''$, then $D''$ contains a vertex of $N$, so we may
  assume that $D'' >= Y$. We also have $D'' <=_G D$ by Corollary
  @cor:brauer-correspondence-defect-subconjugacy, so $D''$ is cyclic, and hence
  $N_G lr((D'')) <= N_G lr((Y)) = H$. Then Theorem
  @th:extended-brauer-first-main(i) applies to $upright(sans(B))''$, and shows
  that $(upright(sans(B))'')^G = upright(sans(B))$ also has defect group $D''$.
  It follows that $D'' =_G D$ and hence $upright(sans(B))'' = upright(sans(B))'$
  by Theorem @th:extended-brauer-first-main(i) again.

  For the proof of part~@case:cyclic-defect-green-block-complement, we have
  $N^G = M plus.o M^*$ with $M^*$ projective, by
  @eq:cyclic-defect-green-exceptional-intersections, since $cal(X) = \{1\}$. On
  the other hand, if $M_H = N plus.o N^*$, then each indecomposable
  nonprojective summand of $N^*$ has a vertex which is $H$-conjugate to no
  subgroup of $D$, and hence does not belong to the block $upright(sans(B))'$ by
  @prop:trace-idempotent-relative-projectivity. This completes the proof.
]

We next prove that the numbers of simple modules in the blocks
$upright(sans(B))$ and $upright(sans(B))'$ are the same, where
$upright(sans(B))'$ is the $H$-block defined in
@prop:cyclic-defect-green-block-compatibility. In fact, we shall prove somewhat
more, and will apply the additional information in
§~@ss:cyclic-defect-periodic-resolutions. The discussion is based on the results
in §§~@ss:cyclic-block-homological-preliminaries,
@ss:green-correspondence-functorial-properties.

Let $\{S_1,dots,S_d\}$ be a basic set of simple modules in $upright(sans(B))'$,
and let $\{T_1,dots,T_d\}$ be a set of P.I.M.'s in $upright(sans(B))'$, such
that $T_i slash N' T_i tilde.equiv S_i$, $1 <= i <= d$, where $N'$ is the
radical of the block ideal $B'$. Let us assume that $upright(sans(B))'$ is a
uniserial block. If $(N')^m = 0$, $(N')^(m-1) != 0$, then
$ T_i supset N' T_i supset dots supset (N')^(m-1) T_i supset 0 $
#source(534)
is the unique composition series of each module $T_i$, by
@th:uniserial-symmetric-projective-composition-cycles, since $B'$ is a symmetric
algebra. Now set

$
  T_(i j) = T_i slash (N')^j T_i, quad 1 <= i <= d, quad 1 <= j <= m.
$
<eq:uniserial-block-indecomposable-quotients>

Then the modules $\{T_(i j)\}$ are a basic set of indecomposable modules in
$upright(sans(B))'$.

Let $\{V_1,dots,V_(d')\}$ be a basic set of simple modules in
$upright(sans(B)) = (upright(sans(B))')^G$, and set $I = \{1,dots,d\}$,
$J = \{1,dots,d'\}$. The modules $\{S_i: i in I\}$ and $\{V_j: j in J\}$ are
$(H,D)$- or $(G,D)$-projective, respectively, since $D$ is a defect group of
both blocks $upright(sans(B))'$ and $upright(sans(B))$. On the other hand, none
of the modules $\{S_i\}$ or $\{V_j\}$ is projective, since both blocks
$upright(sans(B))'$ and $upright(sans(B))$ have positive defect (see
Exercise~@exc:simple-projective-block-defect-zero).

In the statement and proof of the next result, we shall use the notation
$ (M,Q)_H, quad (M,Q)_(H slash 1), quad "etc.," $
from §~@ss:cyclic-block-homological-preliminaries, for a pair of $k H$-modules
$M$ and $Q$, and a corresponding notation for $k G$-modules.

#proposition[
  Keep the preceding notation, and assume that $upright(sans(B))'$ is a
  uniserial block of $H$. Then the following statements hold:
  #case-list(
    numbering: "(i)",
    [#case[The Green correspondents $\{f V_j: j in J\}$ and $\{g S_i: i in I\}$,
        of the simple modules $\{V_j\}$ in $upright(sans(B))$ and $\{S_i\}$ in
        $upright(sans(B))'$, are nonprojective indecomposable modules in
        $upright(sans(B))'$ and $upright(sans(B))$ respectively.]
      <case:cyclic-defect-simple-green-correspondents>],
    [#case[There exist $k$-isomorphisms
        $
          (S_i,f V_j)_H tilde.equiv (g S_i,V_j)_G quad "and" quad
          (f V_j,S_i)_H tilde.equiv (V_j,g S_i)_G
        $
        for all $i in I$, $j in J$.]
      <case:cyclic-defect-simple-green-hom-isomorphisms>],
    [#case[There exists a map $h: J arrow I$ such that
        $ h(j) = i <=> (f V_j,S_i)_H != 0, quad "for" i in I, quad j in J. $
        Moreover, $h$ is a bijection, so $d = d'$.]
      <case:cyclic-defect-simple-module-bijection>],
    [#case[$(f V_j,S_i)_H tilde.equiv k$ or $0$, according as $h(j) = i$ or
        $h(j) != i$.]
      <case:cyclic-defect-simple-green-hom-dimension>],
  )
] <prop:cyclic-defect-simple-green-correspondence>

#proof[
  The first statement follows from
  @prop:cyclic-defect-green-block-compatibility, since the modules $\{S_i\}$ and
  $\{V_j\}$ are nonprojective simple modules.

  @case:cyclic-defect-simple-green-hom-isomorphisms We first apply Theorem
  @th:green-correspondence-stable-hom-isomorphism to the $(G,D)$-projective
  modules $g S_i$ and $V_j$, using the fact that, in this case, the family of
  subgroups $cal(X)$ contains only the trivial subgroup, so
  $(g S_i,V_j)_(G,cal(X)) = (g S_i,V_j)_(G slash 1)$. We have, by
  @th:green-correspondence-stable-hom-isomorphism,
  $
    (g S_i,V_j)_G slash (g S_i,V_j)_(G slash 1)
    tilde.equiv (f g S_i,f V_j)_H slash (f g S_i,f V_j)_(H slash 1) \
    tilde.equiv (S_i,f V_j)_H slash (S_i,f V_j)_(H slash 1),
  $
  #source(535)
  since $f g S_i tilde.equiv S_i$ for each $i in I$. We can then apply
  Proposition @prop:core-simple-projective-maps-zero to obtain
  $
    (g S_i,V_j)_(G slash 1) = 0 quad "and" quad
    (S_i,f V_j)_(H slash 1) = 0, quad "for" i in I, quad j in J,
  $
  since $S_i$ and $V_j$ are simple modules, and $g S_i$ and $f V_j$ are
  indecomposable nonprojective modules. It follows that
  $(S_i,f V_j)_H tilde.equiv (g S_i,V_j)_G$. Similarly
  $(f V_j,S_i)_H tilde.equiv (V_j,g S_i)_G$, for $i in I$, $j in J$, and
  part~@case:cyclic-defect-simple-green-hom-isomorphisms is proved.

  Parts~@case:cyclic-defect-simple-module-bijection and
  @case:cyclic-defect-simple-green-hom-dimension. Let $j in J$. Then
  $f V_j tilde.equiv T_(h(j),v(j))$ for a unique indecomposable module
  $T_(h(j),v(j))$ defined above. This defines maps $h: J arrow I$ and
  $v: J arrow [1,m]$. Since $T_(h(j),v(j))$ is uniserial with top composition
  factor $S_(h(j))$, we have
  $ (f V_j,S_i)_H = cases(k "if" i = h(j), 0 "if" i != h(j)). $
  Now let $i in I$, and let $S$ be a minimal submodule of $g S_i$. Then
  $S in upright(sans(B))$, so $S tilde.equiv V_j$ for some $j$, and it follows
  that $(V_j,g S_i)_G != 0$. Then $(f V_j,S_i)_H != 0$ by
  part~@case:cyclic-defect-simple-green-hom-isomorphisms and we obtain
  $h(j) = i$, proving that $h$ is surjective. Next suppose $j,j' in J$ and
  $h(j) = h(j') = i$. Then $f V_j tilde.equiv T_(i,v)$ and
  $f V_(j') tilde.equiv T_(i,v')$ for some choices of $v$ and $v'$. Thus there
  exists a $k H$-surjection $theta: T_(i,v) arrow T_(i,v')$ by definition of the
  modules $\{T_(i j)\}$, and the map $theta$ is not projective by
  @prop:core-surjection-not-projective. It follows that
  $(f V_j,f V_(j'))_H slash (f V_j,f V_(j'))_(H slash 1) != 0$, and since
  $f V_j$ and $f V_(j')$ are $(H,D)$-projective, we obtain
  $(V_j,V_(j'))_G slash (V_j,V_(j'))_(G slash 1) != 0$ by
  @th:green-correspondence-stable-hom-isomorphism. Therefore
  $(V_j,V_(j'))_G != 0$, and we have $j = j'$. This completes the proof.
]

The next result is the stepping stone to the proof of the main theorem.

#proposition[
  Keep the preceding notation, and assume that $upright(sans(B))'$ is a
  uniserial block of $H$ with defect group $D$. If $upright(sans(B))'$ contains
  exactly $e$ simple modules and $e abs(D)$ indecomposable modules, then the
  same is true for $upright(sans(B))$.
] <prop:cyclic-defect-green-transfer-module-counts>

#proof[
  Then Green Correspondence defines a bijection between the isomorphism classes
  of nonprojective indecomposable modules in the blocks $upright(sans(B))$ and
  $upright(sans(B))'$, by @prop:cyclic-defect-green-block-compatibility. On the
  other hand, by @prop:cyclic-defect-simple-green-correspondence the blocks
  $upright(sans(B))$ and $upright(sans(B))'$ also contain the same number of
  simple modules, and hence the same number of indecomposable projective
  modules. This completes the proof.
]

#proof(head: emph[Proof of Theorem @th:cyclic-defect-block-module-counts.])[
  We shall use induction on $abs(G)$. Thus we shall consider a block
  $upright(sans(B))$ of $G$ with cyclic defect group $D$, and assume that for
  $abs(G_0) < abs(G)$, the result holds for blocks of $k G_0$ with cyclic defect
  group.

  #case-list(
    numbering: "Step 1.",
    [#case[
      We first prove the theorem when $abs(D) = p$. In this case, $Y = D$, and
      $H = N_G lr((Y)) = N_G lr((D))$. If $upright(sans(B))'$ is the $H$-block
      defined in @prop:cyclic-defect-green-block-compatibility,
      part~@case:cyclic-defect-green-block-existence, then $upright(sans(B))'$
      has the same inertial index as $upright(sans(B))$ by Definition
      @def:block-inertial-index. Since the defect group $D$ of
      $upright(sans(B))'$ is normal in $H$, we may apply
      @prop:normal-cyclic-defect-uniserial-module-counts to deduce that
      $upright(sans(B))'$ is a uniserial block, with exactly $e$ simple modules
      and $e abs(D)$ indecomposable modules. Then $upright(sans(B))$ also
      contains exactly $e$ simple modules and $e abs(D)$ indecomposable modules,
      completing the proof of @case:cyclic-defect-count-prime-defect.
    ] <case:cyclic-defect-count-prime-defect>],
    [#case[
      #source(536)
      We may now assume that $abs(D) > p$, and let $Y$ be the subgroup of $D$ of
      order $p$. In this step, we shall assume that $G = C_G lr((Y))$, and prove
      the theorem for $G$. In addition, we shall prove that $upright(sans(B))$
      is uniserial and has exactly one simple module and $abs(D)$ indecomposable
      modules.

      We first compute the inertial index, using the definition
      @def:block-inertial-index. Let $upright(sans(B))'$ be a block of
      $C_G lr((D))$ with defect group $D$ such that
      $(upright(sans(B))')^G = upright(sans(B))$. Then the inertial index of
      $upright(sans(B))$ is given by
      $ e = abs(op("Stab")_(N_G lr((D))) b' colon C_G lr((D))), $
      where $b'$ is the block idempotent of $upright(sans(B))'$ in
      $k C_G lr((D))$. Since $e equiv.not 0 (mod p)$ by
      @prop:cyclic-defect-inertial-index-divides-p-minus-one and
      $G = C_G lr((Y))$, it follows that
      $op("Stab")_(N_G lr((D))) b' slash C_G lr((D))$ is a $p'$-group of
      automorphisms of $D$ which acts trivially on the subgroup $Y$ of order
      $p$. It is not difficult to prove that the order of such a group is $1$,
      and hence $e = 1$ (see Gorenstein @bib:Gorenstein1968, Chapter 5, Theorem
      2.4).

      We next require a lemma which will permit us to use the induction
      hypothesis. We note that since $G = C_G lr((Y))$, $Y$ is a normal subgroup
      of each of the groups $G$, $N_G lr((D))$, $C_G lr((D))$, and of course of
      $D$.

      #lemma[
        Assume $G = C_G lr((Y))$, as in
        @case:cyclic-defect-count-central-order-p. Let $N = N_G lr((D))$,
        $C = C_G lr((D))$ and set $overline(G) = G slash Y$,
        $overline(N) = N slash Y$, $overline(C) = C slash Y$, and
        $overline(D) = D slash Y$. Let $upright(sans(B))_1$ be the unique block
        of $N$ with defect group $D$ such that
        $(upright(sans(B))_1)^G = upright(sans(B))$, and let $B_1$ and $B$
        denote the block ideals of $upright(sans(B))_1$ and $upright(sans(B))$,
        with block idempotents $b_1$ and $b$, respectively. Let
        $tau: k G arrow k overline(G)$ denote the natural homomorphism. Then:
        #case-list(
          numbering: "(i)",
          [#case[$tau(b)$ and $tau(b_1)$ are block idempotents in
              $k overline(G)$ and $k overline(N)$, respectively, and both have
              defect group $overline(D)$.]
            <case:central-p-quotient-block-idempotents>],
          [#case[The block ideals $k overline(G) tau(b)$ and
              $k overline(N) tau(b_1)$ are related by the Brauer correspondence,
              and both blocks have inertial index equal to $1$.]
            <case:central-p-quotient-brauer-inertial-index>],
        )
      ] <lem:cyclic-defect-central-p-quotient>

      #proof[
        Write $t=y-1$, where $Y=chevron.l y chevron.r$. In each of $k G$, $k N$,
        and $k C$, $t$ is central, $t^p=0$, and the kernel of $tau$ is the ideal
        generated by $t$. Idempotents lift through this nilpotent ideal. If
        orthogonal idempotents $e,f$ lift a central decomposition in the
        quotient, then $e(k G)f subset.eq t k G$. Centrality of $t$ gives
        $e(k G)f=t e(k G)f$, so nilpotence makes this corner zero; likewise
        $f(k G)e=0$. Thus central block decompositions lift and block
        idempotents correspond bijectively.

        For a $p$-subgroup $P>=Y$, consider a coset $x Y$ centralizing
        $P slash Y$. Its commutator map $P arrow Y$ is a homomorphism, since $Y$
        is central. If nontrivial it is onto, and $P$ permutes the $p$ elements
        of the coset transitively. The coefficients of a central element are
        equal there, so their sum is zero in $k$. Otherwise all elements of the
        coset centralize $P$. Therefore
        $ tau(sigma_P lr((b)))=sigma_(P slash Y)(tau(b)), $
        with $sigma_P$ the Brauer map @def:brauer-map. The same identity holds
        in $k N$. Since $Y$ is central in $C_G lr((P))$, a nonzero idempotent
        $sigma_P lr((b))$ cannot vanish under $tau$. The maximal subgroups with
        nonzero Brauer image, which contain $Y$, thus correspond under
        quotienting by $Y$. This proves the defect assertion in
        part~@case:central-p-quotient-block-idempotents.

        By @cor:brauer-map-block-idempotent-fibres, $sigma_D lr((b))b_1$ is a
        nonzero idempotent. Its image under $tau$ is still nonzero, and equals
        $sigma_(overline(D))(tau(b))tau(b_1)$ by the preceding identity. Since
        $overline(N)=N_(overline(G)) lr((overline(D)))$, the same criterion
        proves the asserted Brauer correspondence.#ed-note[
          In characteristic two, let $G$ be the semidirect product of
          $C_3=chevron.l a chevron.r$ by $C_4$, with inversion action, and put
          $D=C_4$. Then $Y=C_2$ is central, $N_G lr((D))=D$, the principal block
          idempotent of $k G$ is $b=1+a+a^2$, and the unique block idempotent of
          $k D$ is $b_1=1$. Thus $b b_1!=b_1$; the relevant criterion is
          @cor:brauer-map-block-idempotent-fibres.
        ]

        Finally, $N slash C$ embeds in the automorphisms of cyclic $D$ fixing
        $Y$ pointwise, a $p$-group. The quotient
        $N_(overline(G)) lr((overline(D))) slash
        C_(overline(G)) lr((overline(D)))$ is a quotient of this group. Each
        quotient block's inertial index divides its order and is prime to $p$,
        by @th:block-inertial-index-prime-to-p, so is one. This proves
        part~@case:central-p-quotient-brauer-inertial-index.
      ]

      To complete the proof of @case:cyclic-defect-count-central-order-p, let
      $overline(upright(sans(B)))$ be the block of $overline(G)$ defined by
      $tau(b)$. Since $overline(upright(sans(B)))$ has inertial index $1$ by the
      preceding lemma, it follows that $overline(upright(sans(B)))$ contains
      exactly one simple module and $abs(overline(D))$ indecomposable modules,
      up to isomorphism. We have $ker tau = I k G$, where $I$ is the
      augmentation ideal of the group algebra $k Y$. As in the
      #source(537)
      proof of @prop:normal-cyclic-defect-uniserial-module-counts, we have
      $ker tau inter B = I B subset.eq rad B$, and
      $overline(B) tilde.equiv B slash I B$. From these remarks, it follows that
      $upright(sans(B))$ contains a unique simple module, and hence
      $upright(sans(B))$ is a uniserial block, by
      @th:finite-type-one-simple-uniserial. Then $upright(sans(B))$ contains a
      unique indecomposable projective module $U$, and the number of
      indecomposable modules in $upright(sans(B))$ is the composition length of
      $U$. By @bib:CurtisReiner1962[CR] (89.8), the Cartan matrix of the block
      $upright(sans(B))$ is $(abs(D))$ and this proves that the composition
      length of $U$ is $abs(D)$, since $U$ is uniserial. This completes the
      proof of @case:cyclic-defect-count-central-order-p.
    ] <case:cyclic-defect-count-central-order-p>],
    [#case[
      This time we shall assume that $G = N_G lr((Y))$, and will prove that
      $upright(sans(B))$ is a uniserial block, containing exactly $e$ simple
      modules and $e abs(D)$ indecomposable modules, where $e$ is the inertial
      index.

      In this case, $C_G lr((Y)) ⊴ G$, so $upright(sans(B))$ covers a unique
      conjugacy class of blocks of $C_G lr((Y))$, all with defect group $D$.
      This follows from Theorem @th:normal-subgroup-covering-blocks, using the
      fact that $D <= C_G lr((Y))$ to calculate the defect groups. By
      @case:cyclic-defect-count-central-order-p, each of these blocks is
      uniserial, and contains exactly one simple module and $abs(D)$
      indecomposable modules.

      Our first objective is to prove that $upright(sans(B))$ is a uniserial
      block. Let $upright(sans(B))_0$ be a uniserial block of $C_G lr((Y))$ with
      defect group $D$ covered by $upright(sans(B))$ and let
      $T_0 = op("Stab")_G b_0$, where $b_0$ is the block idempotent of
      $upright(sans(B))_0$. Then $C_G lr((Y)) ⊴ T_0$, and we have

      $ abs(T_0 colon C_G lr((Y))) equiv.not 0 (mod p) $
      <eq:cyclic-defect-inertia-quotient-prime-to-p>

      by @th:maximal-covering-block-defect-index. Moreover, $upright(sans(B))_0$
      is covered by a unique block $tilde(upright(sans(B)))_0$ of $T_0$. Letting
      $B_0$ and $tilde(B)_0$ denote the block ideals of $upright(sans(B))_0$ and
      $tilde(upright(sans(B)))_0$, respectively, we have

      $
        rad tilde(B)_0 = tilde(B)_0(rad B_0) = (rad B_0) tilde(B)_0
      $ <eq:cyclic-defect-inertia-block-radical>

      by Exercise~@exc:crossed-product-prime-to-p-radical, because of
      @eq:cyclic-defect-inertia-quotient-prime-to-p. Since $B_0$ is uniserial,
      we have $rad B_0 = u B_0 = B_0 u$ for some element $u in B_0$ by
      @th:morita-principal-radical-uniserial, and hence the same is true for
      $tilde(B)_0$ because of @eq:cyclic-defect-inertia-block-radical. It
      follows that $tilde(upright(sans(B)))_0$ is also a uniserial block, by
      @th:morita-principal-radical-uniserial.

      Since $B_0$ is a uniserial block containing a unique simple module,
      $T_0 = op("Stab")_G b_0$ coincides with the stabilizer of each
      indecomposable module in $upright(sans(B))_0$. This follows easily from
      the fact that the isomorphism class of an indecomposable module in
      $upright(sans(B))_0$ is determined by its composition length. Then
      $U^G = op("ind")_(T_0)^G U$ is an indecomposable module in
      $upright(sans(B))$ for each indecomposable module $U$ in
      $tilde(upright(sans(B)))_0$, by
      @i:th:graded-inertia-indecomposable-induction. Moreover, $U$ is uniserial,
      and $F^G$ is a simple module for each composition factor $F$ of $U$. It
      follows that $U^G$ is also uniserial. Indeed, the conjugates of $b_0$
      indexed by $G slash T_0$ are orthogonal. A submodule of $U^G$ is the
      direct sum of its components under these idempotents, and all components
      are translates of its $b_0$-component, a $T_0$-submodule of $U$. Thus
      induction identifies the entire submodule lattices, and preserves
      uniseriality.#ed-note[
        Exactness alone does not preserve uniseriality: restriction from
        $k[t] slash (t^2)$-modules to $k$-spaces is exact and preserves simple
        modules, but sends the regular module to a nonuniserial two-dimensional
        space. The inertia hypothesis is essential; compare
        @i:th:graded-inertia-indecomposable-induction.
      ]

      We can now complete the proof that $upright(sans(B))$ is a uniserial
      block. Each indecomposable module $M$ in $upright(sans(B))$ is
      $(G,D)$-projective, and hence $(G,C_G lr((Y)))$-projective, since
      $C_G lr((Y)) >= D$. Then $M divides V^G$ for some indecomposable module
      $V$ in $upright(sans(B))_0$, and it follows easily from
      @i:th:graded-inertia-indecomposable-induction that in fact
      $M tilde.equiv U^G$ for some indecomposable module $U$ in
      $tilde(upright(sans(B)))_0$. Then $M$ is uniserial by the preceding
      discussion, and we have proved that $upright(sans(B))$ is uniserial.

      It remains to count the simple and indecomposable modules.#ed-note[
        A nilpotent kernel alone does not ensure that a block remains primitive:
        the principal block of $k S_3$ in characteristic three maps onto both
        blocks of $k C_2$. The centrality hypothesis in
        @lem:cyclic-defect-central-p-quotient is essential to its argument.
      ] Put $q=abs(D)$, $J=rad B$, $C_0=C_G lr((Y))$, and let $I$ be the
      augmentation ideal of $k Y$. If $U$ is a P.I.M. of $B_0$, it is free over
      $k Y$. Multiplication by $y-1$, for $Y=chevron.l y chevron.r$, has kernel
      of dimension $dim_k U slash p$. Since $U$ is uniserial of length $q$ with
      one simple type, $I U=(rad B_0)^(q slash p)U$. Hence
      $I B_0=(rad B_0)^(q slash p)$. The $T_0$-stable idempotent $b_0$ acts as
      identity on its unique covering block; uniqueness also follows from
      @th:normal-subgroup-covering-blocks(iv), since $C_(T_0) lr((D))<=C_0$. By
      @eq:cyclic-defect-inertia-block-radical the same equality holds in
      $tilde(B)_0$. The orthogonal conjugate idempotents give the matrix algebra
      identification
      $ B tilde.equiv M_(abs(G colon T_0)) lr((tilde(B)_0)), $
      which carries the $G$-stable ideal $I B$ to the matrix ideal generated by
      $I tilde(B)_0$. Consequently
      $ I B=J^(q slash p) subset.eq J^2, $
      since $q>p$.

      Let $tau:k G arrow k(G slash Y)$ be the quotient map. Then
      #source(538)
      $tau(b)$ is a block idempotent. To see this, a central decomposition of
      $B slash I B$ lifts to orthogonal idempotents $e,f$ in $B$. Its
      cross-corners lie in $J^2$, and $e J f=e J e dot e J f+e J f dot f J f$.
      Iteration and nilpotence of $J$ give $e J f=f J e=0$. Thus the lifted
      idempotents are central, contradicting the indecomposability of $B$.

      Write $overline(G)=G slash Y$, $overline(D)=D slash Y$. For every
      $p$-subgroup $P>=Y$, $P$ centralizes $Y$. In a coset $x Y$ centralizing
      $P slash Y$, if $x$ does not centralize $Y$, conjugation by $Y$ is
      transitive on that coset; otherwise the commutator homomorphism
      $P arrow Y$ is trivial or onto. As in
      @lem:cyclic-defect-central-p-quotient, central coefficient sums therefore
      give $tau sigma_P lr((b))=sigma_(P slash Y)tau(b)$. Since $Y$ is central
      in $C_G lr((P))$, nonzero Brauer idempotents survive this quotient. Thus
      the quotient block has defect $overline(D)$.

      Since $Y<=D$, $N_(overline(G)) lr((overline(D)))=N_G lr((D)) slash Y$. To
      compare inertial indices, put $C=C_G lr((D))$, $N=N_G lr((D))$, and choose
      the canonical block idempotent $c$ of $k C$ below $b$. Let
      $S=op("Stab")_N c$, and let $C^*$ be the preimage in $N$ of
      $C_(overline(G)) lr((overline(D)))$. The group $C^* slash C$ embeds in the
      kernel of $op("Aut") D arrow op("Aut") lr((D slash Y))$ and is a
      $p$-group. Since $S slash C$ has order $e$ prime to $p$, $S inter C^*=C$.
      The central-$Y$ block bijection in $k C$ shows that the
      $C^* slash C$-orbit of $tau(c)$ is free. Its orbit sum is one block
      idempotent of $k(C^* slash Y)$: the orthogonal idempotent matrix
      construction identifies its algebra with a matrix algebra over
      $k(C slash Y)tau(c)$. Its stabilizer in $N slash Y$ is $C^* S slash Y$.
      Since $sigma_D lr((b))c=c$, Brauer compatibility puts this orbit block
      below $sigma_(overline(D))(tau(b))$. Thus it is the canonical block below
      $tau(b)$, by @cor:brauer-map-block-idempotent-fibres. The quotient
      inertial index is therefore $abs(C^* S colon C^*)=abs(S colon C)=e$.

      Induction on $abs(G)$ now gives $e$ simple modules in $B slash I B$, and
      hence in $B$, since $I B subset.eq J$. Let $l$ be the common composition
      length of the P.I.M.'s of the symmetric uniserial algebra $B$, and let
      $F_1,dots,F_e$ be its simple modules. A nonzero P.I.M. $P$ is free over
      $k Y$, so $I P!=0$ and $l>q slash p$. Summing dimensions over one basic
      set of P.I.M.'s gives $l sum_i dim_k F_i$. Their quotients by $I$ have
      length $q slash p$, so their dimensions sum to
      $(q slash p)sum_i dim_k F_i$; at each radical depth the simple types are
      permuted, by @th:uniserial-symmetric-projective-composition-cycles. Each
      P.I.M. is free over $k Y$, so the first sum is $p$ times the second.
      Therefore $l=q$, and $B$ has $e q$ indecomposable modules by
      @th:nakayama-uniserial-finite-representation-type. This completes the
      proof of @case:cyclic-defect-count-normal-order-p.
    ] <case:cyclic-defect-count-normal-order-p>],
    [#case[
      We are in a position to complete the proof of the main Theorem
      @th:cyclic-defect-block-module-counts. Let $Y$ be the subgroup of $D$ of
      order $p$. Then $N_G lr((Y)) >= N_G lr((D))$, so the Brauer correspondence
      assigns to $upright(sans(B))$ a unique block $upright(sans(B))'$ of
      $N_G lr((Y))$ with defect group $D$, by @th:extended-brauer-first-main(i).
      Moreover, it is readily verified that $upright(sans(B))$ and
      $upright(sans(B))'$ have the same inertial index. We may apply
      @case:cyclic-defect-count-normal-order-p to $upright(sans(B))'$ and
      conclude that $upright(sans(B))'$ is a uniserial block containing $e$
      simple modules and $e abs(D)$ indecomposable modules. Then
      $upright(sans(B))$ contains $e$ simple modules and $e abs(D)$
      indecomposable modules by
      @prop:cyclic-defect-green-transfer-module-counts, completing the proof.
    ] <case:cyclic-defect-count-general-group>],
  )
]

=== Periodic Projective Resolutions in Blocks with Cyclic Defect Groups
<ss:cyclic-defect-periodic-resolutions>

Let $G$ be a finite group, and $(K,R,k)$ a $p$-modular system such that
$op("char") K = 0$, $K$ is sufficiently large relative to $G$, and $k$ is a
perfect field of characteristic $p$. Let $upright(sans(B))$ be a $p$-block of
$G$ with a cyclic defect group $D$. In
§~@ss:cyclic-defect-modular-representations, some definitive information was
obtained concerning the simple and indecomposable $k G$-modules belonging to
$upright(sans(B))$. The question arises, what can be said about the
$K G$-modules and $R G$-modules belonging to $upright(sans(B))$? In case
$upright(sans(B))$ is the principal block, and $D$ is a cyclic self-centralizing
Sylow $p$-subgroup such that $D^*$ is a T.I. set, the $K$-characters belonging
to $upright(sans(B))$ were described in §~@ss:principal-block-orthogonality,
using the results in §~@i:ss:green-correspondence-character-applications. These
results (of Thompson @bib:Thompson1967) were extended to determine the
$K$-characters belonging to an arbitrary block with cyclic defect group by Dade
@bib:Dade1966. A complete and up-to-date account of Dade's results, with
additions and improvements, was given by Feit @bib:Feit1982, Chapter VII.

In this subsection, we shall describe some properties of $R G$-modules belonging
to $upright(sans(B))$. In particular, we shall prove that the presence of a
cyclic Sylow $p$-subgroup manifests itself in the existence of a periodic
projective resolution (see @i:eq:projective-resolution) of the trivial
$R G$-module. The result, which is due to Green @bib:Green1974, and a closely
related theorem of Alperin–Janusz @bib:Alperin1973 were first proved using
Dade's results on the $K$-characters in $upright(sans(B))$. We shall give a new
proof of a somewhat less precise result, using the results on $k G$-modules in
$upright(sans(B))$ from §~@ss:cyclic-defect-modular-representations, combined
with Morita's work on uniserial blocks, from
§~@ss:uniserial-algebras-finite-representation-type (see also Michler
@bib:Michler1975). We shall also show the connection between these results and
the $K G$-modules in $upright(sans(B))$, in the special situation considered in
§~@ss:principal-block-orthogonality.

We begin with a few remarks about the Heller operator $Omega$ in the category of
f.g. $k G$-modules. A fuller discussion of this topic, with proofs of some facts
stated below, will be found in §~@sec:auslander-reiten-sequences. Let $M$ be a
core (see @def:projective-map-presentation-core). We define $Omega M$ to be the
kernel of a surjective homomorphism $pi: P arrow M$, where $P$ is a projective
cover of
#source(539)
$M$ (see §~@i:ss:krull-schmidt-azumaya). Thus we have a short exact sequence
(ses)
$ 0 arrow Omega M arrow P arrow M arrow 0. $
By Schanuel's Lemma @i:lem:schanuel and the properties of projective covers, it
follows easily that the isomorphism class of $Omega M$ is uniquely determined by
the isomorphism class of $M$ (see §~@ss:heller-loop-space-operator). The
resulting operation $(M) arrow (Omega M)$ in the set of isomorphism classes
$(M)$ of f.g. $k G$-modules is called the _Heller operator_. The same definition
and
#idx("Heller operator")
#nidx("$M arrow Omega M$", "means Heller operator")
remarks apply to $R G$-lattices, since $R G$ is a semiperfect ring (see
§~@i:ss:cartan-map-triangle). The main property of $Omega$ we require is
contained in the following result, which is proved for $k G$-modules in
§~@ss:heller-loop-space-operator.

#proposition[
  Let $M$ be a f.g. $k G$-module, or an $R G$-lattice. If $M$ is indecomposable
  and nonprojective, so is $Omega M$.
] <prop:heller-preserves-indecomposable-nonprojective>

The proof for $R G$-lattices is left as an exercise.

The next result uses reduction mod $frak(p)$,
$M arrow overline(M) = M slash frak(p) M$, from the category of $R G$-lattices
to the category of f.g. $k G$-modules (see §~@i:ss:reduction-decomposition-map).

#proposition[
  Let
  $ 0 arrow U arrow Q arrow V arrow 0 $
  be a ses of f.g. $k G$-modules, with $Q$ projective, and suppose there exists
  an $R G$-lattice $M$ such that $overline(M) tilde.equiv V$. Then there exists
  a commutative diagram, with exact rows, and $P$ projective,
  #projective-reduction-exact-rows
  where each vertical map is reduction mod $frak(p)$.
] <prop:projective-exact-sequence-lifting>

The proof is left as an exercise.

Now let $upright(sans(B))$ be a $p$-block of $G$ with a cyclic defect group
$D != 1$. Our first objective is to construct some short exact sequences
involving the indecomposable projective $k G$-modules in $upright(sans(B))$.
This will involve the connection between modules in $upright(sans(B))$ and
modules in a corresponding block $upright(sans(B))'$ of the subgroup
$H = N_G lr((Y))$, where $Y$ is subgroup of $D$ of order $p$. We shall make
frequent use of results from
§§~@ss:uniserial-algebras-finite-representation-type and
@ss:cyclic-defect-modular-representations, especially Proposition
@prop:cyclic-defect-simple-green-correspondence and the remarks preceding it,
and the proof of Theorem @th:cyclic-defect-block-module-counts.

Since $H >= N_G lr((D))$, there is a unique $p$-block $upright(sans(B))'$ of $H$
with defect group $D$ such that $(upright(sans(B))')^G = upright(sans(B))$. By
@case:cyclic-defect-count-normal-order-p of the proof of Theorem
@th:cyclic-defect-block-module-counts, $upright(sans(B))'$ is a uniserial block,
and both blocks $upright(sans(B))$ and $upright(sans(B))'$ contain exactly $e$
isomorphism classes of simple modules, where $e$ is the inertial index of
$upright(sans(B))$.

#source(540)
Let $\{S_1,dots,S_e\}$ be a basic set of simple modules in $upright(sans(B))'$,
and let $T_i$ be a projective cover of $S_i$, for $1 <= i <= e$. Then the
modules $\{T_i\}$ all have the same composition length $q$ by
@th:uniserial-symmetric-projective-composition-cycles, since the block ideal
$B'$ is a symmetric uniserial algebra. Letting $N' = rad B'$, each of the
modules $T_i$ has a unique composition series
$ T_i supset N' T_i supset (N')^2 T_i supset dots supset (N')^q T_i = 0, $
and the modules
$ T_(i j) = T_i slash (N')^j T_i, quad 1 <= i <= e, quad 1 <= j <= q, $
form a basic set of indecomposable modules in $upright(sans(B))'$. Since the
number of indecomposable modules in $upright(sans(B))'$ is $e abs(D)$ by Theorem
@th:cyclic-defect-block-module-counts, we have $q = abs(D) = p^d$ for some
positive integer $d$, and it follows that
$ q equiv 1 (mod e), $
since $e divides p-1$ by @th:cyclic-defect-block-module-counts,
part~@case:cyclic-defect-inertial-index-divisibility.

The periodic behavior of the modules in $upright(sans(B))$ and
$upright(sans(B))'$ is best explained if we index a set of modules
$\{S_i,T_i,T_(i j)\}$ so that $i$ is any integer, and $S_i,T_i,T_(i j)$ have
their previous interpretations for $1 <= i <= e$ and satisfy
$
  S_i tilde.equiv S_(i+e), quad T_i tilde.equiv T_(i+e), quad T_(i j)
  tilde.equiv T_(i+e,j),
$
for $1 <= j <= q$ and all $i in ZZ$. In this terminology, we have:

#proposition[
  There exists an ordering of $\{1,2,dots,e\}$ such that the following
  statements hold.
  #case-list(
    numbering: "(i)",
    [#case[For each $i in ZZ$, the modules in a composition series of $T_i$ are
        indecomposable, and are isomorphic, respectively, to the sequence of
        modules:
        $
          T_(i,q),T_(i+1,q-1),T_(i+2,q-2),dots,T_(i+q-1,1) tilde.equiv T_(i,1).
        $]
      <case:cyclic-uniserial-radical-submodules>],
    [#case[$T_(i j) in cal(P)(k H)$ if and only if $j = q$.]
      <case:cyclic-uniserial-quotient-projectivity>],
    [#case[$T_(i 1) tilde.equiv S_i$ for all $i in ZZ$.]
      <case:cyclic-uniserial-quotient-simple-top>],
    [#case[For each $i in ZZ$ and $j < q$ there exists a ses of $k H$-modules
        $ 0 arrow T_(i+j,q-j) arrow T_(i q) arrow T_(i j) arrow 0. $]
      <case:cyclic-uniserial-quotient-exact-sequence>],
    [#case[For each $j < q$ we have
        $ Omega T_(i j) tilde.equiv T_(i+j,q-j). $]
      <case:cyclic-uniserial-heller-quotient>],
    [#case[$Omega^2 S_i tilde.equiv S_(i+1)$ for all $i in ZZ$.]
      <case:cyclic-uniserial-heller-square-simple>],
  )
] <prop:cyclic-uniserial-heller-formulas>

#proof[
  #source(541)
  @case:cyclic-uniserial-radical-submodules We order $\{1,2,dots,e\}$ as in
  Morita's Theorem @th:uniserial-symmetric-projective-composition-cycles. Then
  part~@case:cyclic-uniserial-radical-submodules follows at once from
  @th:uniserial-symmetric-projective-composition-cycles and the description of
  the modules $\{T_(i j)\}$, together with the fact that $q equiv 1 (mod e)$.
  Statements from part~@case:cyclic-uniserial-quotient-projectivity through
  part~@case:cyclic-uniserial-quotient-exact-sequence follow from
  part~@case:cyclic-uniserial-radical-submodules, while
  part~@case:cyclic-uniserial-heller-quotient follows from
  part~@case:cyclic-uniserial-quotient-exact-sequence and the definition of the
  Heller operator $Omega$. For part~@case:cyclic-uniserial-heller-square-simple
  we have
  $
    Omega^2 S_i tilde.equiv Omega^2(T_(i,1)) tilde.equiv Omega(T_(i+1,q-1))
    tilde.equiv T_(i+q,1) tilde.equiv S_(i+1)
  $
  using part~@case:cyclic-uniserial-heller-quotient and the fact that
  $q equiv 1 (mod e)$, so that
  $ T_(i+q,1) tilde.equiv T_(i+1,1) tilde.equiv S_(i+1) $
  by part~@case:cyclic-uniserial-quotient-simple-top. This completes the proof.
]

The next result carries this information over to modules in $upright(sans(B))$,
using the Green Correspondence and Proposition
@prop:cyclic-defect-simple-green-correspondence.

#theorem[
  Keep the notation of Proposition @prop:cyclic-uniserial-heller-formulas. Then
  there exists a basic set of simple $k G$-modules $\{V_1,dots,V_e\}$ in
  $upright(sans(B))$ which can be ordered so that the following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[Let $\{f V_j\}$ and $\{g S_i\}$ denote the Green correspondents of
        the modules $\{V_j\}$ and $\{S_i\}$, respectively. We have
        $ (f V_j,S_i)_H tilde.equiv (V_j,g S_i)_G tilde.equiv k "or" 0, $
        according as $i = j$ or $i != j$.]
      <case:cyclic-defect-simple-top-socle-pairing>],
    [#case[There exists a permutation $delta$ of $\{1,2,dots,e\}$ such that
        $ (S_i,f V_j)_H tilde.equiv (g S_i,V_j)_G tilde.equiv k "or" 0, $
        according as $delta(i) = j$ or $delta(i) != j$.]
      <case:cyclic-defect-simple-socle-permutation>],
    [#case[For each $i$, $1 <= i <= e$, let $U_i$ denote a projective cover of
        the simple $k G$-module $V_i$, and, as in the case of modules in the
        block $upright(sans(B))'$, extend the definition of $U_i$ and $V_i$ so
        that $i$ is taken in $ZZ$, and $U_i tilde.equiv U_(i+e)$,
        $V_i tilde.equiv V_(i+e)$, and also $delta(i+e) = delta(i)$ for
        $i in ZZ$. Then there exist ses's of $k G$-modules
        $ F_(2 i): 0 arrow Omega g S_i arrow U_(delta(i)) arrow g S_i arrow 0 $
        and
        $ F_(2 i+1): 0 arrow g S_(i+1) arrow U_(i+1) arrow Omega g S_i arrow 0 $
        for all $i in ZZ$.]
      <case:cyclic-defect-projective-exact-sequences>],
  )
] <th:cyclic-defect-projective-sequence-cycle>
#idx(
  "Green Correspondence",
  target: [@th:cyclic-defect-projective-sequence-cycle],
)

#proof[
  We have already noted that $upright(sans(B))$ contains exactly $e$ isomorphism
  classes of simple modules. We order them in such a way that the bijection $h$
  described in @prop:cyclic-defect-simple-green-correspondence is the identity.
  Then part~@case:cyclic-defect-simple-top-socle-pairing of the theorem follows
  from @prop:cyclic-defect-simple-green-correspondence,
  parts~@case:cyclic-defect-simple-green-hom-isomorphisms through
  @case:cyclic-defect-simple-green-hom-dimension.
  #source(542)
  Using the fact that $(S_i,f V_j)_H tilde.equiv (g S_i,V_j)_G$ for all $i$ and
  $j$, by @prop:cyclic-defect-simple-green-correspondence,
  part~@case:cyclic-defect-simple-green-hom-isomorphisms, we can then
  essentially repeat the proof of
  @prop:cyclic-defect-simple-green-correspondence to prove the existence of a
  permutation $delta$ of $\{1,2,dots,e\}$ satisfying
  part~@case:cyclic-defect-simple-socle-permutation of the theorem.

  By parts~@case:cyclic-defect-simple-top-socle-pairing and
  @case:cyclic-defect-simple-socle-permutation, we have

  $
    op("soc") g S_i tilde.equiv V_i quad "and" quad
    g S_i slash rad g S_i tilde.equiv V_(delta(i)) quad "for" 1 <= i <= e.
  $ <eq:cyclic-defect-green-simple-top-socle>
  #idx("Inertial index")
  #idx("p-Blocks", "inertial index of")

  From the second of these isomorphisms, and the fact that $U_(delta(i))$ is a
  projective cover of $V_(delta(i))$, it follows that there exists a surjection
  $U_(delta(i)) arrow g S_i$, and consequently $U_(delta(i))$ is a projective
  cover of $g S_i$. Then we have a ses of $k G$-modules
  $ F_(2 i): 0 arrow Omega g S_i arrow U_(delta(i)) arrow g S_i arrow 0 $
  for all $i in ZZ$, using the definition of the Heller operator $Omega$.

  To obtain the exact sequences $F_(2 i+1)$, we start from the facts that
  $op("soc") g S_(i+1) tilde.equiv V_(i+1)$ by
  @eq:cyclic-defect-green-simple-top-socle, and that $U_(i+1)$ is an injective
  hull of $V_(i+1)$. Consequently there exists a ses, for each $i in ZZ$,

  $ 0 arrow g S_(i+1) arrow U_(i+1) arrow W_(i+1) arrow 0, $
  <eq:cyclic-defect-injective-hull-sequence>

  where $W_(i+1)$ is some $k G$-module.

  On the other hand, we have

  $ Omega g T_(i j) tilde.equiv g Omega T_(i j), quad i in ZZ, quad j < q, $
  <eq:heller-green-commutation>

  for each nonprojective indecomposable module $T_(i j)$ in $upright(sans(B))'$
  (see Exercise~@exc:heller-green-commutation). This implies that
  $ Omega(Omega g S_i) tilde.equiv g Omega^2 S_i tilde.equiv g S_(i+1) $
  by @prop:cyclic-uniserial-heller-formulas,
  part~@case:cyclic-uniserial-heller-square-simple, and hence there exists a ses
  $ 0 arrow g S_(i+1) arrow U arrow Omega g S_i arrow 0, $
  with $U$ projective. By a version of Schanuel's Lemma, we obtain
  $W_(i+1) tilde.equiv Omega g S_i$, and we can take
  @eq:cyclic-defect-injective-hull-sequence as the exact sequence $F_(2 i+1)$,
  for all $i in ZZ$. This completes the proof of the theorem.
]

Before stating the main result on $R G$-modules, we recall that a _projective
resolution_ of a module $M$ over a ring $A$ is an exact sequence
$ dots arrow P_2 arrow P_1 arrow M arrow 0 $
with $P_i$ projective, for all $i >= 1$.

#theorem[
  Let $G$ have a cyclic Sylow $p$-subgroup $D$, and let $e$ be the inertial
  #source(543)
  index of the principal $p$-block $upright(sans(B))_1$. Then there exists a
  family of $R G$-lattices $\{X_i: i >= 0\}$, and an ordering of indecomposable
  projective $R G$-modules $\{P_1,dots,P_e\}$ in $upright(sans(B))_1$, such that
  the following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[Extend the definition of the modules $\{P_i\}$ so that $i in ZZ$ and
        $P_(i+e) tilde.equiv P_i$ for all $i in ZZ$. Then there exist ses's of
        $R G$-lattices
        $ E_(2 i): 0 arrow X_(2 i+1) arrow P_(delta(i)) arrow X_(2 i) arrow 0 $
        and
        $ E_(2 i+1): 0 arrow X_(2 i+2) arrow P_(i+1) arrow X_(2 i+1) arrow 0 $
        for all $i in ZZ_+$, with $X_0$ the trivial $R G$-lattice, and $delta$
        as in @th:cyclic-defect-projective-sequence-cycle,
        part~@case:cyclic-defect-simple-socle-permutation.]
      <case:cyclic-sylow-integral-projective-sequences>],
    [#case[The ses's $\{E_i: i in ZZ_+\}$ provide a projective resolution of the
        trivial $R G$-lattice $X_0$, which is periodic of period $2 e$:
        $
          dots arrow P_(delta(0)) arrow P_0 arrow P_(delta(e-1))
          arrow P_(e-1) arrow dots arrow P_(delta(1)) arrow P_1
          arrow P_(delta(0)) arrow X_0 arrow 0.
        $]
      <case:cyclic-sylow-integral-periodic-resolution>],
  )
] <th:cyclic-sylow-periodic-projective-resolution>
#idx(
  "Projective resolution",
  target: [@th:cyclic-sylow-periodic-projective-resolution],
)

#proof[
  If $D=1$, then $e=1$ and $R$ is projective; alternating identity and zero maps
  gives the required split resolution of period two. We may therefore assume
  $D!=1$. We shall apply Theorem @th:cyclic-defect-projective-sequence-cycle to
  the principal block. By @th:cyclic-defect-projective-sequence-cycle,
  part~@case:cyclic-defect-projective-exact-sequences, there exist ses's of
  $k G$-modules in $upright(sans(B))_1$:
  $ F_(2 i): 0 arrow Y_(2 i+1) arrow U_(delta(i)) arrow Y_(2 i) arrow 0 $
  and
  $ F_(2 i+1): 0 arrow Y_(2 i+2) arrow U_(i+1) arrow Y_(2 i+1) arrow 0, $
  where $Y_(2 i) tilde.equiv g S_i$ and $Y_(2 i+1) tilde.equiv Omega g S_i$, for
  all $i in ZZ$. The $p$-block of $H$ corresponding to $upright(sans(B))_1$ is
  the principal block $upright(sans(B))'_1$ of $H$, which contains the trivial
  $H$-module, denoted by $S_0$. Then $Y_0 tilde.equiv g S_0$ is the trivial
  $k G$-module, by the properties of the Green Correspondence.

  We start the proof of the theorem with the observation that if $X_0$ denotes
  the trivial $R G$-lattice, then we have $overline(X)_0 tilde.equiv Y_0$, where
  $overline(X)_0 = X_0 slash frak(p) X_0$. We may assume the indecomposable
  projective $R G$-lattices in $upright(sans(B))_1$ are ordered in such a way
  that $overline(P)_i tilde.equiv U_i$, for all $i in ZZ$ (see
  §~@i:ss:cartan-map-triangle). By @prop:projective-exact-sequence-lifting, we
  can lift the ses $F_0$ to a ses of $R G$-lattices
  $ E_0: 0 arrow X_1 arrow P_(delta(0)) arrow X_0 arrow 0, $
  such that $overline(X)_0 tilde.equiv Y_0$ and $overline(X)_1 tilde.equiv Y_1$.
  By @prop:projective-exact-sequence-lifting again, starting from
  $overline(X)_1 tilde.equiv Y_1$, we can lift the ses $F_1$ to a ses of
  $R G$-lattices
  $ E_1: 0 arrow X_2 arrow P_1 arrow X_1 arrow 0, $
  such that $overline(X)_2 tilde.equiv Y_2$. Continuing by induction, we can
  define $R G$-lattices $\{X_i\}$ and ses $\{E_i\}$ for all $i in ZZ_+$, such
  that part~@case:cyclic-sylow-integral-projective-sequences of Theorem
  @th:cyclic-sylow-periodic-projective-resolution holds. To prove
  part~@case:cyclic-sylow-integral-periodic-resolution, observe that
  $overline(X)_(2 e) tilde.equiv Y_(2 e) tilde.equiv k$, so $X_(2 e)$ has
  $R$-rank one. Taking determinant characters in successive pairs of exact
  sequences gives
  $
    (det X_(2 i+2))(det X_(2 i))^(-1)
    =(det P_(i+1))(det P_(delta(i)))^(-1).
  $
  Multiplying for $0<=i<e$, the projective determinants cancel because $delta$
  permutes the residues modulo $e$. Hence $det X_(2 e)=1$, since $X_0=R$. A
  rank-one representation is its determinant, so $X_(2 e) tilde.equiv R$. Repeat
  this actual finite exact segment using the isomorphism
  $X_(2 e) tilde.equiv X_0$ to obtain the asserted periodic resolution,
  including its maps.#ed-note[
    Periodicity of the projective terms alone does not specify periodic maps; a
    projective resolution includes its exact differentials, as in
    @i:eq:projective-resolution.
  ] This finishes the proof.
]

#source(544)
#remarks(name: "Remarks and Examples. The Brauer Tree")[Let us interpret some of
  the preceding results in the special case, considered in
  §§~@i:sec:green-correspondence and @sec:p-sections-blocks, of a finite group
  $G$ with a cyclic self-centralizing Sylow $p$-subgroup $D$ such that $D^*$ is
  a T.I. set. Let
  $
    abs(D) = p^d, quad e = abs(N_G lr((D)) colon D), quad "and" quad
    n = (p^d - 1) slash e,
  $
  and assume $n >= 2$. By @lem:cyclic-ti-sylow-normalizer-single-block, the
  group $N_G lr((D))$ has only one $p$-block, and it follows that $e$ is the
  inertial index of the principal $p$-block $upright(sans(B))_1$ of $G$ (see
  @def:block-inertial-index). By Theorem @th:cyclic-ti-sylow-principal-block,
  there are exactly $e + (p^d - 1) slash e$ irreducible $K$-characters in
  $upright(sans(B))_1$, namely,
  $ \{theta_0 = 1_G,theta_1,dots,theta_(e-1),zeta_1,dots,zeta_n\} $
  (see @th:cyclic-ti-sylow-character-values). By Theorem
  @th:cyclic-defect-block-module-counts, there are exactly $e$ characters
  $\{tau_1,dots,tau_e\}$ afforded by the indecomposable projective
  $R G$-lattices in $upright(sans(B))_1$. We require one more crucial piece of
  information relating the characters $\{tau_i\}$ and the irreducible characters
  in $upright(sans(B))_1$.
] <rem:brauer-tree>

#proposition[
  Let $tau$ be a $K$-character afforded by an indecomposable projective
  $R G$-lattice belonging to $upright(sans(B))_1$. Then we have either
  $
    tau = sum_(i=1)^n zeta_i + theta_j,
    quad "for some" j, quad 0 <= j <= e-1
  $
  or
  $ tau = theta_i + theta_j, quad "with" 0 <= i < j <= e-1. $
] <prop:brauer-tree-projective-character-edges>

#proof[
  We shall take full advantage of what has already been proved in
  §~@i:ss:green-correspondence-character-applications. In particular, we know
  that if $(tau,zeta_i) > 0$ for an exceptional character $zeta_i$, then
  $sum zeta_i$ is a summand of $tau$. We also recall that the decomposition
  numbers of the irreducible characters in $upright(sans(B))_1$ are either $0$
  or $1$, so that $(tau,zeta) = 0$ or $1$ for all irreducible characters $zeta$
  in $upright(sans(B))_1$.

  Suppose $sum zeta_i$ is a summand of $tau$. Then $tau$ contains at least one
  of the characters $theta_j$, $0 <= j <= e-1$, since $tau$ vanishes on $D^*$,
  while $sum zeta_i$ does not, by Theorem
  @i:th:green-cyclic-sylow-character-values. Assume
  $sum zeta_i + theta_j + theta_l$ is a summand of $tau$. Then
  $h(sum zeta_i + theta_j + theta_l) <= 1$ by
  @i:prop:projective-character-restriction-height. We may assume that
  $
    Gamma_1 = (1_D - xi)^G = -epsilon zeta_1 + sum c_j theta_j,
    quad "where" c_0 theta_0 = 1_G.
  $
  Then
  $
    1 >= h(sum zeta_i + theta_j + theta_l)
    >= abs((sum zeta_i + theta_j + theta_l,1_D - xi)_D) \
    = abs((sum zeta_i + theta_j + theta_l,Gamma_1)_G)
    = abs(-epsilon + c_j + c_l).
  $
  Since $epsilon,c_j$, and $c_l$ are all $plus.minus 1$, some partial sum
  $-epsilon + c_j$, $-epsilon + c_l$ or $c_j + c_l$ is $plus.minus 2$, and this
  contradicts @i:prop:projective-character-restriction-height, since the
  characters $sum zeta_i + theta_j$, $sum zeta_i + theta_l$, and
  $theta_j + theta_l$ are
  #source(545)
  also summands of $tau$. A similar argument shows that if $sum zeta_i$ is not a
  summand of $tau$, then $tau$ is a sum of exactly two of the remaining
  characters $\{theta_i\}$. This completes the proof.
]

Using Proposition @prop:brauer-tree-projective-character-edges, the
decomposition numbers of the block $upright(sans(B))_1$, which are the
multiplicities of the irreducible $K$-characters in the indecomposable
projective characters $tau$ by @i:th:projective-characters-supported-p-regular,
can be described by a graph, as follows. There are $e + 1$ vertices of the
graph, labeled by the irreducible characters
$\{theta_0,theta_1,dots,theta_(e-1)\}$ and $theta_("exc") = sum zeta_i$. Two
vertices are joined by an edge if and only if the corresponding characters are
summands of some indecomposable projective character $tau$. This graph is
connected. Indeed, every ordinary character has a nonzero decomposition row, and
the exceptional rows agree. A disconnected incidence graph would make the Cartan
matrix, the transpose of the decomposition matrix times that matrix, block
diagonal, contrary to the linkage of P.I.M.'s in a block
(§~@ss:pim-block-linkage). Since the connected graph has exactly $e+1$ vertices
and $e$ edges, it has no closed paths and is a tree,#ed-note[
  Vertex and edge counts alone do not suffice: a triangle and a disjoint edge
  have five vertices and four edges. Block linkage supplies the needed
  connectedness; see @th:block-ideals-linkage-classes.
] called the _Brauer tree_ of the block $upright(sans(B))_1$.
#idx("Brauer tree")

From Dade's results @bib:Dade1966 (see also Feit @bib:Feit1982, Chapter VII), it
follows that the same remarks apply to an arbitrary block with a cyclic defect
group, in any finite group $G$. Green proved @bib:Green1974 that the periodic
projective resolution described in Theorem
@th:cyclic-sylow-periodic-projective-resolution is closely related to the Brauer
tree, and describes a “walk” around the Brauer tree.

#exercises-heading

In Exercises~@exc:family-relative-projectivity and
@exc:relative-projective-map-factorization, $R$ denotes a field of
characteristic $p$, or a complete d.v.r. whose residue field has characteristic
$p$.

#exercise[
  Let $cal(Z)$ be a family of subgroups of $G$. An $R G$-lattice $M$ is called
  $(G,cal(Z))$-projective (see @i:def:family-relative-projectivity) if and only
  if $M = plus.o.big M_i$, for a set of $R G$-lattices $\{M_i\}$ such that, for
  each $i$, $M_i$ is $(G,Z_i)$-projective for some subgroup $Z_i in cal(Z)$.
  Prove that $M$ is $(G,cal(Z))$-projective if and only if $op("id")_M$ is
  $(G,cal(Z))$-projective (see
  §~@ss:green-correspondence-functorial-properties).
] <exc:family-relative-projectivity>

#hint[@exc:family-relative-projectivity][
  Using @lem:module-homomorphism-relative-trace, reduce to the case of an
  indecomposable $R G$-lattice $M$. In that case, $op("id")_M$ is a primitive
  idempotent. If $(M,M)_G = sum (M,M)_(G slash Z_i)$, then
  $op("id")_M in (M,M)_(G slash Z_i)$ for some subgroup $Z_i$, by Rosenberg's
  Lemma @lem:rosenberg-primitive-idempotent-ideal-sum and
  @lem:module-homomorphism-relative-trace.
] <hint:family-relative-projectivity>

#exercise[
  Let $M_1,M_2$ be $(H,D)$-projective $R H$-lattices, for $D <= H$. Prove that
  $(M_1,M_2)_H = (M_1,M_2)_(H slash D)$.
] <exc:relative-projective-map-factorization>

#exercise[
  Let $k$ be a field of characteristic $p$, and let $G$ be a finite group having
  a cyclic Sylow $p$-subgroup. Apply Theorem
  @th:block-finite-representation-type-cyclic-defect to prove that $k G$ has
  finite representation type (see Higman's Theorem (@bib:CurtisReiner1962[CR]
  (64.1))).
] <exc:cyclic-sylow-finite-representation-type>

#exercise[
  Let $A$ be a f.d. $k$-algebra, for a field $k$. Prove that a f.g. left
  $A$-module $M$ is uniserial (see @def:uniserial-module-algebra) if and only if
  the $k$-dual $M^*$ is a f.g. uniserial right $A$-module.
] <exc:uniserial-duality>

#exercise[
  Let $M$ be a f.g. uniserial left $A$-module, for a f.d. algebra $A$ over a
  field $k$. Prove that $M$ is a homomorphic image of a P.I.M.
] <exc:uniserial-projective-cover>

#hint[@exc:uniserial-projective-cover][
  Let $P$ be a P.I.M. such that $P slash rad P tilde.equiv M slash rad M$, and
  deduce that $P$ is a projective cover of $M$ (see Theorem
  @i:th:semiperfect-projective-covers).
] <hint:uniserial-projective-cover>

#exercise[
  Let $H ⊴ G$, and assume $abs(G colon H) equiv.not 0 (mod p)$ for a prime $p$.
  Let $k$ be a field of characteristic $p$. Prove that
  $rad k G = (rad k H) k G = k G(rad k H)$.
] <exc:crossed-product-prime-to-p-radical>

#source(546)
#hint([@exc:crossed-product-prime-to-p-radical], caption: [Hint (Feit):])[
  Since $H ⊴ G$, the ideal $J=(rad k H) k G=k G(rad k H)$ is nilpotent, and
  hence $J subset.eq rad k G$. Put $A=k G slash J$. Every ses of $A$-modules
  splits over $k H slash rad k H$, since that algebra is semisimple. If $s$ is
  such a splitting, average $g s g^(-1)$ over representatives of $G slash H$,
  dividing by $abs(G colon H)$, which is a unit in $k$. The result is
  independent of the representatives and is a $G$-linear splitting. Thus $A$ is
  semisimple, and $rad k G=J$.
  #ed-note[
    For $G=H=C_p$, the augmentation sequence
    $0 arrow rad k C_p arrow k C_p arrow k arrow 0$ does not split over $k H$.
    Relative projectivity only turns an already $H$-split sequence into a
    $G$-split one; see @i:th:gaschutz-relative-projectivity.
  ]
] <hint:crossed-product-prime-to-p-radical>

#exercise[
  (Green @bib:Green1974). Prove that the Heller operator $Omega$ commutes with
  the Green Correspondence. More precisely, let $H >= N_G lr((D))$, and let $g$
  be the Green Correspondence on its vertex domain, as in
  @prop:green-correspondent-relative-core, from indecomposable nonprojective
  $(H,D)$-projective $k H$-modules $L$ to nonprojective indecomposable
  $(G,D)$-projective $k G$-modules $g(L)$. Prove that in this situation,
  $ Omega g L tilde.equiv g(Omega L). $

  (The result is needed (in @eq:heller-green-commutation) only in case
  $cal(X) = \{1\}$, and can be proved using Schanuel's Lemma.)
] <exc:heller-green-commutation>

#exercise[
  Determine the Brauer tree of the principal $p$-block of
  $op("PSL")_2 lr((FF_p))$ (see @rem:brauer-tree).
] <exc:psl-two-prime-brauer-tree>
