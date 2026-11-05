#import "main-defs.typ": *
#import "statements.typ": *

== Applications of Blocks to Character Theory <sec:blocks-character-theory>

Let $M$ be an indecomposable $R G$-lattice, and let $H$ be a subgroup of $G$.
The distribution of indecomposable summands of the restriction $M_H$ among the
blocks of $H$ was examined in §~@ss:brauer-correspondence-general
(Theorem~@th:brauer-correspondence-restriction-vertices). This section begins
with another result in this direction, called the Nagao Decomposition, which is
proved using the Brauer homomorphism. The result leads to Nagao's proof of
Brauer's Second Main Theorem. Most of the applications of block theory to
characters, and applications to finite group theory (see
§~@sec:blocks-group-theory) involve Brauer's
#source(479)
Second Main Theorem in some way. Other proofs of the theorem were given by
Brauer @bib:Brauer1959a, Iizuka @bib:Iizuka1961, and Dade @bib:Dade1965a.

=== The Nagao Decomposition <ss:nagao-decomposition>

In this subsection, $D$ denotes a $p$-subgroup of a finite group $G$, and $H$ a
subgroup satisfying
$ D dot C_G lr((D)) <= H <= N_G lr((D)). $ <eq:nagao-subgroup-bounds>
We let $(K,R,k)$ be a $p$-modular system with $op("char") K=0$ and $K$
sufficiently large relative to $G$; then $(K,R,k)$ is admissible for $G$ and its
subgroups. We let
#idx("Brauer map")
$ sigma: c(R G) arrow c(R H) $
denote the Brauer map @def:brauer-map relative to $D$. The main result of the
subsection is a theorem of Nagao @bib:Nagao1963 on a decomposition of the
restriction $M_H$ of an arbitrary $R G$-lattice $M$ belonging to a given
$p$-block $upright(sans(B))$ of $G$, in terms of the effect of the Brauer map on
the block idempotent in $upright(sans(B))$. As an application, we obtain a
connection between the Green Correspondence of indecomposable lattices
@i:cor:green-correspondence-fixed-vertex and the Brauer Correspondence of blocks
(§~@ss:brauer-correspondence-general). In §~@ss:brauer-second-main-theorem, we
give Nagao's proof of Brauer's Second Main Theorem, which is an application of
the Nagao decomposition to character theory.

#idx("G-algebra")
We shall use the theory of $G$-algebras from §~@sec:defect-groups-blocks (also
summarized at the beginning of §~@ss:brauer-map). In particular, $A$ denotes the
$G$-algebra $R G$. Define
$ A_H={a in A: x a=a "for all" x in H}, $
and
$ A_(H slash D')=T_(H slash D') lr((A_(D'))), quad "for" D' <= H. $
We recall that $A_(H slash D')$ is a two-sided ideal in $A_H$, for each subgroup
$D' <= H$. By @prop:trace-image-class-defect-support, we have
$ A_(H slash D') equiv sum R L_i quad (mod frak(p) A_H), $
<eq:nagao-trace-class-support>
where the sum is taken over $H$-class sums ${L_i}$ in $A_H$ whose class defect
groups ${D'_i}$ satisfy the condition that $D'_i <=_H D'$.

#lemma[
  Let $frak(L)$ be an $H$-conjugacy class in $G$, and assume that
  $frak(L) subset.not.eq C_G lr((D))$. Then the $H$-class sum
  $L=sum_(y in frak(L)) y$ belongs to $A_(H slash D')$ for some $p$-subgroup
  $D' <= H$ such that $D ≰ D'$.
] <lem:nagao-noncentral-class-trace>

#proof[
  Let $x in frak(L)-C_G lr((D))$, and let $D'$ be a Sylow $p$-subgroup of
  $C_H lr((x))$. Then $D'$ is a class defect group of the $H$-class $frak(L)$
  containing $x$, and we have $L in A_(H slash D')$ by
  @eq:nagao-trace-class-support. Moreover, $D ≰ D'$ since
  $x in.not C_G lr((D))$, and the proof is completed.
]

#source(480)
#theorem(name: "Nagao Decomposition Theorem")[
  Let $b$ be a block idempotent in $R G$, and let $M$ be an $R G$-lattice such
  that $b M=M$. Then $b=b_1+b_2$, where $b_1$ and $b_2$ are either orthogonal
  idempotents in $A_H$, or one of them is zero, and the resulting decomposition
  $ M_H=b_1 M plus.o b_2 M $
  of $M_H$ into $R H$-lattices has the following properties:
  #case-list(
    numbering: "(i)",
    [#case[$b_1 M equiv sigma(b)M quad (mod frak(p)M)$, and $b_1 M$ is either
        zero or a direct sum of indecomposable $R H$-lattices belonging to the
        blocks ${upright(sans(B))'_i}$ of $H$ such that
        $(upright(sans(B))'_i)^G=upright(sans(B))$.]
      <case:nagao-corresponding-block-summand>],
    [#case[$b_2 M$ is either zero or a direct sum of indecomposable
        $R H$-lattices whose vertices do not contain $D$.]
      <case:nagao-small-vertex-summand>],
  )
] <th:nagao-block-decomposition>
#idx("Nagao decomposition", target: [@th:nagao-block-decomposition])
#idx("Brauer Correspondence", target: [@th:nagao-block-decomposition])

#proof[
  By @cor:brauer-map-block-idempotent-fibres, it follows that either
  $sigma b equiv 0 quad (mod frak(p)A_H)$ or
  $sigma b equiv b' quad (mod frak(p)A_H)$, where
  $ b'=sum_i b'_i, $
  and the ${b'_i}$ are all the block idempotents in $c(R H)$ belonging to blocks
  ${upright(sans(B))'_i}$ of $H$ such that
  $(upright(sans(B))'_i)^G=upright(sans(B))$. Set $b'=0$ if
  $sigma b equiv 0 quad (mod frak(p)A_H)$; then we have
  $ sigma b equiv b' quad (mod frak(p)A_H) $
  in either case.

  Now let $frak(C)$ be a conjugacy class in $G$, and let
  $C=sum_(x in frak(C)) x$ be the class sum supported by $frak(C)$. We may write
  $ C=C'+C'' $
  where $C'=sum_(x in frak(C) inter C_G lr((D))) x$ if
  $frak(C) inter C_G lr((D)) != emptyset$ and $C'=0$ otherwise; then
  $C''=C-C' in A_H$, and $C''$ is supported by $H$-class sums containing
  elements $x in.not C_G lr((D))$. Then $sigma C=C'$ by @def:brauer-map, and by
  Lemma~@lem:nagao-noncentral-class-trace,
  $ C''=C-sigma C in sum_(D') A_(H slash D'), $
  where the sum is taken over $p$-subgroups $D' <= H$ such that $D ≰ D'$. Since
  $b$ is an $R$-linear combination of $G$-class sums, the preceding remarks
  imply, by linearity, that
  $ b-sigma b in sum_(D') A_(H slash D'), $ <eq:nagao-block-trace-error>
  where the sum is taken over subgroups $D' <= H$ such that $D ≰ D'$, as above.

  #source(481)
  Now set
  $ b_1=b b', quad b_2=b(b-b'); $
  then
  $ b=b_1+b_2, $
  and $b_1$ and $b_2$ are either orthogonal idempotents or one of them is zero.
  Then
  $ M=b M=b_1 M plus.o b_2 M. $
  Moreover,
  $ b-sigma b equiv b-b' quad (mod frak(p)A_H), $
  so
  $ b_1 M=b' M quad "and" quad b_1 M equiv sigma(b)M quad (mod frak(p)M), $
  using the assumption that $M=b M$. This completes the proof of
  @case:nagao-corresponding-block-summand, since $b'$ is a sum of block
  idempotents in $c(R H)$ with the required properties, by the first part of the
  proof.

  For the proof of @case:nagao-small-vertex-summand, we have
  $ b_2=b(b-b') equiv b(b-sigma b) quad (mod frak(p)A_H). $
  Then $b_2 in sum_(D ≰ D') A_(H slash D')+frak(p)A_H$ by
  @eq:nagao-block-trace-error, since $A_(H slash D')$ is a two-sided ideal in
  $A_H$ for each subgroup $D' <= H$. Then either $b_2=0$ and there is nothing
  further to be proved, or $b_2=sum b''_j$, where ${b''_j}$ are primitive
  orthogonal idempotents in $A_H$. Then, for each $j$,
  $ b''_j=b_2 b''_j in sum_(D ≰ D') A_(H slash D')+frak(p)A_H, $
  again using the fact that $A_(H slash D')$ is a two-sided ideal for each $D'$.
  By Rosenberg's Lemma~@lem:rosenberg-primitive-idempotent-ideal-sum, we obtain
  $ b''_j in A_(H slash D') $
  for some $p$-subgroup $D' <= H$ such that $D ≰ D'$. Then $b''_j M$ is
  $(H,D')$-projective by @prop:trace-idempotent-relative-projectivity, and hence
  $b''_j M$ is a direct sum of indecomposable $R H$-lattices whose vertices do
  not contain $D$, since they are $H$-conjugate to subgroups of $D'$ and
  $D ⊴ H$. Finally, $b_2 M=plus.big_j b''_j M$, and the proof of
  @case:nagao-small-vertex-summand is complete.
]

#corollary[
  Let $M$ be an indecomposable $R G$-lattice belonging to a block
  $upright(sans(B))$ of $G$, and let $N$ be an indecomposable $R H$-lattice such
  that $N divides M_H$. Then at least one of the following possibilities occurs.
  #case-list(
    numbering: "(i)",
    [#case[$N$ belongs to a block $upright(sans(B))'$ of $H$ with defect group
        $D'$ such that
        $
          (upright(sans(B))')^G=upright(sans(B))
          quad "and" quad C_G lr((D')) <= H.
        $]
      <case:nagao-restriction-corresponding-block>],
    [#case[$D$ is not contained in any vertex of $N$.]
      <case:nagao-restriction-small-vertex>],
  )
] <cor:nagao-restriction-block-or-small-vertex>

#source(482)
#proof[
  By Theorem~@th:nagao-block-decomposition and the K-S-A Theorem, either
  $N divides b_1 M$ or $N divides b_2 M$. In the first case,
  @case:nagao-corresponding-block-summand of @th:nagao-block-decomposition
  applies, and hence $N$ belongs to a block $upright(sans(B))'$ of $H$ such that
  $(upright(sans(B))')^G=upright(sans(B))$. Since $H$ satisfies
  @eq:nagao-subgroup-bounds, we have $D ⊴ H$, so $D <= D'$ by
  @prop:normal-p-subgroup-block-idempotents, and consequently
  $C_G lr((D')) <= C_G lr((D)) <= H$, again using @eq:nagao-subgroup-bounds. If
  $N divides b_2 M$, then @case:nagao-restriction-small-vertex holds, by
  @case:nagao-small-vertex-summand of @th:nagao-block-decomposition.
]

#corollary(title: [Green @bib:Green1978a])[
  #case-list(
    numbering: "(i)",
    [#case[Let $M in op("Ind") R G$, $N in op("Ind") R H$, and assume
      $N divides M_H$ and $D <= D''$ for some vertex $D''$ of $N$. If $N$
      belongs to the $p$-block $upright(sans(B))'$ of $H$, then
      $(upright(sans(B))')^G$ is defined, and
      $M in (upright(sans(B))')^G$.] <case:green-block-restriction>],
    [#case[Let $N in op("Ind") R H$, and assume $D <= D''$ for some vertex $D''$
        of $N$. If $N$ belongs to the block $upright(sans(B))'$ of $H$, then
        $op("ind")_H^G N$ contains a summand $M in op("Ind") R G$ such that
        $M in (upright(sans(B))')^G$.]
      <case:green-block-induction>],
  )
] <cor:green-large-vertex-block-correspondence>

#proof(head: none)[
  Part~@case:green-block-restriction follows from
  Corollary~@cor:nagao-restriction-block-or-small-vertex.
  Part~@case:green-block-induction follows from
  part~@case:green-block-restriction, using the fact that there exists
  $M in op("Ind") R G$ such that
  $ M divides op("ind")_H^G N quad "and" quad N divides M_H, $
  by the K-S-A Theorem.
]

The next result gives a connection between the Brauer Correspondence and the
Green Correspondence @i:cor:green-correspondence-fixed-vertex (see also
@th:brauer-correspondence-restriction-vertices). We first restate
@i:cor:green-correspondence-fixed-vertex, for convenient reference.

#theorem(name: "Green Correspondence")[
  Let $H=N_G lr((D))$, for a $p$-subgroup $D <= G$. There exists a bijection
  from the set of isomorphism classes of indecomposable $R G$-lattices $M$ with
  vertex $=_G D$, to the set of isomorphism classes of indecomposable
  $R H$-lattices $N$ with vertex $D$. Two lattices $M in op("Ind") R G$ and
  $N in op("Ind") R H$ correspond to each other if and only if either of the
  following conditions hold:
  $ op("ind")_H^G N=M plus.o X quad "or" quad M_H=N plus.o Y, $
  where the “error” term $X$ is a direct sum of indecomposable $R G$-lattices
  whose vertices are conjugate to proper subgroups of $D$, and the “error” term
  $Y$ is a direct sum of indecomposable $R H$-lattices whose vertices do not
  contain $D$.#ed-note[For $G=D_8$, with $D$ a reflection subgroup and
    $H=N_G lr((D))$, the other restriction summand can have a distinct vertex of
    order $2$. Thus the original’s “similar property” does not force
    smaller-order vertices. See @i:eq:green-subgroup-families and
    Theorem~@i:th:green-correspondence.]
] <th:green-correspondence-normalizer-restatement>
#idx(
  "Green Correspondence",
  target: [@th:green-correspondence-normalizer-restatement],
)

We now have

#theorem[
  Let $H=N_G lr((D))$, and let $M in op("Ind") R G$ and $N in op("Ind") R H$
  both have vertex $D$. Assume that $M arrow.l.r N$ in the Green Correspondence
  @th:green-correspondence-normalizer-restatement. Then $M$ and $N$ belong to
  blocks $upright(sans(B))$ of $G$ and $upright(sans(B))'$ of $H$, respectively,
  which are Brauer correspondents: $upright(sans(B))=(upright(sans(B))')^G$.
] <th:green-brauer-correspondence-compatibility>
#idx(
  "Brauer Correspondence",
  "and Green Correspondence",
  target: [@th:green-brauer-correspondence-compatibility],
)

#proof[
  Assume $M in upright(sans(B))$, for a $p$-block $upright(sans(B))$ of $G$.
  Then $N divides M_H$ by @th:green-correspondence-normalizer-restatement, and
  $N$ has vertex $D$. If $N in upright(sans(B))'$, for a block
  $upright(sans(B))'$ of $H$, then $(upright(sans(B))')^G=upright(sans(B))$ by
  @cor:green-large-vertex-block-correspondence@case:green-block-restriction,
  since $N$ has vertex $D$.
]

#source(483)
We conclude this subsection with a characterization of the defect group of a
block in terms of the vertices of indecomposable lattices belonging to the
block. By @cor:block-module-vertices-subconjugate-defect-group, we have
$D' <=_G D$, for $M in upright(sans(B))$, where $M$ is an indecomposable
$R G$-lattice with vertex $D'$, and $upright(sans(B))$ is a block of $G$ with
defect group $D$.

#theorem(title: "Hamernik")[
  Let $upright(sans(B))$ be a block of $G$ with defect group $D$. Then there
  exists an indecomposable $R G$-lattice $M$ such that $M in upright(sans(B))$
  and $D in op("vtx") M$.
] <th:hamernik-block-module-full-defect-vertex>
#idx(
  "Defect groups of idempotents",
  "of p-blocks",
  target: [@th:hamernik-block-module-full-defect-vertex],
)
#idx(
  "Vertex",
  "of an indecomposable module",
  target: [@th:hamernik-block-module-full-defect-vertex],
)

#proof(head: emph[Proof (Alperin–Burry @bib:Alperin1980).])[
  Let $H=N_G lr((D))$. By Brauer's First Main
  Theorem~@th:brauer-first-main-theorem and
  Theorem~@th:brauer-correspondence-brauer-map, it follows that
  $upright(sans(B))=(upright(sans(B))')^G$ for a $p$-block $upright(sans(B))'$
  of $H$ with defect group $D$. Let $b'$ be the block idempotent in
  $upright(sans(B))'$. Since the kernel of the natural map
  $tau: R H arrow R(H slash D)$ is contained in $op("rad") R H$ (by
  @i:prop:normal-p-subgroup-radical-kernel), $tau(b') != 0$, and there exists an
  indecomposable projective $R(H slash D)$-module $N$ such that $tau(b')N != 0$.
  Then $N$ can be viewed as an $R H$-module, and $N in upright(sans(B))'$ since
  $b' N != 0$. We first prove that $D in op("vtx") N$. Since
  $N in cal(P)(R(H slash D))$, it follows that $N$ is $(H,D)$-projective, by
  Gaschütz's criterion @i:th:gaschutz-relative-projectivity. Therefore
  $D' <=_H D$, for any vertex $D'$ of $N$. On the other hand, $D$ acts trivially
  on $N$, so $N_D$ is a direct sum of indecomposable $R D$-lattices all having
  vertex $D$, by @prop:trivial-module-sylow-vertices. It follows that $N$ also
  has vertex $D$, by @prop:vertex-preserving-restriction-summand.

  Now let $M in op("Ind") R G$ correspond to $N$ by
  @th:green-correspondence-normalizer-restatement. Then $D in op("vtx") M$, and
  $M in (upright(sans(B))')^G=upright(sans(B))$ by
  Theorem~@th:green-brauer-correspondence-compatibility. This completes the
  proof.
]

=== Brauer's Second Main Theorem <ss:brauer-second-main-theorem>

In this subsection, we apply the Nagao Decomposition
@th:nagao-block-decomposition to character theory. As in
§~@ss:nagao-decomposition, we let $(K,R,k)$ denote a $p$-modular system such
that $op("char") K=0$ and $K$ is sufficiently large relative to $G$. We also
assume that $R$ is complete in the $frak(p)$-adic topology, with a perfect
residue field $k$. Then $(K,R,k)$ is admissible for $G$ and its subgroups, and
the hypotheses of Green's theorem on zeros of characters
@i:th:green-character-zeros are satisfied.

Our objective is a theorem of Brauer @bib:Brauer1959a (see
@th:brauer-second-main-first-form and @th:brauer-second-main-second-form) which
gives the character values $zeta^i lr((x))$, for $zeta^i in op("Irr") G$ and
$x in G$, in terms of the values ${chi^j lr((x))}$, for certain irreducible
characters ${chi^j}$ of the centralizer $C_G lr((u))$, where $u$ is the $p$-part
of $x$. The crucial point is that the characters ${chi^j}$ are taken only from
those blocks of $C_G lr((u))$ which are Brauer correspondents of the block of
$G$ containing $zeta^i$. Most of the applications of block theory to finite
groups, including those discussed later in this chapter, involve this theorem in
some way.

We first recall @i:th:green-character-zeros.

#theorem(name: "Green's Theorem on Zeros of Characters")[
  Let $D$ be a $p$-subgroup of $G$, and let $D <= H <= G$. Let $M$ be an
  $(H,D)$-projective $R H$-lattice. Then for every element $x in H$ whose
  $p$-part is not $H$-conjugate to an element of $D$, we have
  $ op("Tr")(x,M)=0. $
  In other words, the $K$-character of $H$ afforded by $K times.o_R M$ vanishes
  at $x$.
] <th:green-character-zeros-restatement>
#idx(
  "Green's Theorem on Zeros of Characters",
  target: [@th:green-character-zeros-restatement],
)

#source(484)
Using @th:green-character-zeros-restatement, we next obtain the
character-theoretic version of the Nagao Decomposition.

#theorem(title: "Nagao")[
  Let $b$ be a block idempotent in $R G$, and let $M$ be an $R G$-lattice such
  that $b M=M$. For $x in G$, let $u$ be the $p$-part of $x$, and set $D=⟨ u ⟩$
  and $H=C_G lr((u))=C_G lr((D))$, so that the pair of subgroups ${D,H}$
  satisfies @eq:nagao-subgroup-bounds. Let
  $ M_H=b_1 M plus.o b_2 M $
  be the Nagao Decomposition @th:nagao-block-decomposition of the restriction of
  $M$ to $H$. Then
  $ op("Tr")(x,M)=op("Tr")(x,b_1 M). $
  In other words, if $chi$ and $chi_1$ are the $K$-characters of $G$ and $H$
  afforded by $K times.o_R M$ and $K times.o_R b_1 M$ respectively, then
  $ chi(x)=chi_1 lr((x)). $
] <th:nagao-character-trace-decomposition>
#idx("Nagao decomposition", target: [@th:nagao-character-trace-decomposition])

#proof[
  Since $x in H$ and $b_1 M$ and $b_2 M$ are $R H$-sublattices of $M_H$, we have
  $ op("Tr")(x,M)=op("Tr")(x,b_1 M)+op("Tr")(x,b_2 M). $
  so it is sufficient to prove that $op("Tr")(x,b_2 M)=0$. Let $N$ be an
  indecomposable $R H$-lattice such that $N divides b_2 M$, and let $D'$ be a
  vertex of $N$. Then $N$ is $(H,D')$-projective, and $D ≰ D'$ by
  @th:nagao-block-decomposition@case:nagao-small-vertex-summand. Since $D=⟨ u ⟩$
  and $H=C_G lr((u))$, it follows that $u$ is not $H$-conjugate to an element of
  $D'$. Since $u$ is the $p$-part of $x$, we can apply
  @th:green-character-zeros-restatement to obtain $op("Tr")(x,N)=0$. But $N$ is
  an arbitrary $R H$-component of $b_2 M$, so we obtain $op("Tr")(x,b_2 M)=0$,
  as required.
]

We next introduce some notation needed for the statement of Brauer's Theorem.
Let $zeta in op("Irr") G$, and let $H <= G$. Then we have
$
  zeta |_H=sum_(upright(sans(B))') (zeta |_H)_(upright(sans(B))'),
$ <eq:restricted-character-block-components>
where the sum is taken over the $p$-blocks $upright(sans(B))'$ of $H$, and
$(zeta |_H)_(upright(sans(B))')$ is the contribution to $zeta |_H$ from
irreducible characters of $H$ belonging to the block $upright(sans(B))'$.

#theorem(name: "Brauer's Second Main Theorem", title: "First Form")[
  Let $x in G$, and set $H=C_G lr((u))$, where $u$ is the $p$-part of $x$. Let
  $zeta$ be an irreducible $K$-character of $G$ belonging to a $p$-block
  $upright(sans(B))$ of $G$, and let $upright(sans(B))'$ range over the
  $p$-blocks of $H$. Then
  $
    zeta |_H lr((x))=sum_(upright(sans(B))')
    (zeta |_H)_(upright(sans(B))') lr((x)),
  $
  where the sum extends over all $upright(sans(B))'$ for which
  $(upright(sans(B))')^G=upright(sans(B))$. Further,
  $
    (zeta |_H)_(upright(sans(B))') lr((x))=0
    quad "whenever" (upright(sans(B))')^G != upright(sans(B)).
  $
] <th:brauer-second-main-first-form>
#idx(
  "Brauer's Second Main Theorem",
  target: [@th:brauer-second-main-first-form],
)

#source(485)
#proof[
  Let $M$ be an $R G$-lattice such that $K times.o_R M$ affords $zeta$. Then
  $b M=M$, where $b$ is the block idempotent in $upright(sans(B))$. Let
  $ M_H=b_1 M plus.o b_2 M $
  be the Nagao Decomposition @th:nagao-block-decomposition of $M_H$. By
  Theorem~@th:nagao-character-trace-decomposition,
  $ op("Tr")(x,M)=op("Tr")(x,b_1 M). $
  By Theorem~@th:nagao-block-decomposition, $b_1 M$ is either zero or a direct
  sum of indecomposable $R H$-lattices belonging to the blocks
  ${upright(sans(B))'}$ of $H$ such that
  $(upright(sans(B))')^G=upright(sans(B))$. Upon tensoring these with $K$ and
  computing the characters, we obtain
  $
    zeta |_H lr((x))=sum_((upright(sans(B))')^G=upright(sans(B)))
    (zeta |_H)_(upright(sans(B))') lr((x)).
  $
  It remains to show that $(zeta |_H)_(upright(sans(B))') lr((x))=0$ if
  $upright(sans(B))'$ is not a Brauer correspondent of $upright(sans(B))$. For
  such a block, it follows from the Nagao Decomposition
  @th:nagao-block-decomposition that $(zeta |_H)_(upright(sans(B))')$ is
  afforded by an $R H$-summand of $b_2 M$. By the proof of
  Theorem~@th:nagao-character-trace-decomposition, we obtain
  $(zeta |_H)_(upright(sans(B))') lr((x))=0$ for all such blocks
  $upright(sans(B))'$ for which $(upright(sans(B))')^G != upright(sans(B))$,
  completing the proof.
]

The next result is Brauer's original version of the Second Main Theorem, and
requires some preliminary discussion. Let $u$ be a fixed $p$-element in $G$, and
let $H=C_G lr((u))$. Let
$
  op("Irr") G={zeta^1,...,zeta^s}, quad
  op("Irr") H={chi^1,...,chi^(s')},
$
${xi^1,...,xi^(r')}=$ the irreducible Brauer characters of $H$.

#proposition[
  Keeping the above notation, there exist uniquely determined algebraic integers
  ${d^u_(i j)}$ in $K$, depending on $zeta^i$, $xi^j$, and $u$ as above, such
  that
  $ zeta^i lr((x u))=sum_(j=1)^(r') d^u_(i j) xi^j lr((x)), $
  for all $p'$-elements $x in H$.
] <prop:generalized-decomposition-coefficients>

#proof[
  For each $i$, the restriction $zeta^i |_H$ is a $ZZ$-linear combination of the
  characters $chi^j in op("Irr") H$, so we have
  $
    zeta^i |_H=sum_(j=1)^(s') q_(i j) chi^j,
    quad q_(i j) in ZZ, quad 1 <= i <= s.
  $
  The decomposition map for the group $H$ yields formulas
  $ chi^j=sum_(l=1)^(r') d'_(j l) xi^l quad "on" H_(p'), $
  where
  #source(486)
  $(d'_(j l))^(s' times r')$ is the decomposition matrix for $H$. Now let
  $x in H$ be a $p'$-element, and let $T_j$ be a matrix representation affording
  $chi^j$, $1 <= j <= s'$. Since $u$ belongs to the center of $H$, we have, by
  @i:prop:central-character-values-integral,
  $
    T_j lr((u))=epsilon_j I, quad "where"
    epsilon_j=chi^j lr((u)) slash chi^j lr((1)) in "alg. int." K.
  $
  Then
  $ T_j lr((x u))=epsilon_j T_j lr((x)) $
  and hence $chi^j lr((x u))=epsilon_j chi^j lr((x))$. Upon setting
  $
    d^u_(i l)=sum_(j=1)^(s') q_(i j) epsilon_j d'_(j l),
    quad "for" 1 <= i <= s, quad 1 <= l <= r',
  $
  and substituting in the preceding formulas, we obtain the desired result. The
  uniqueness of the elements ${d^u_(i l)}$ follows from the linear independence
  of the Brauer characters ${xi^j}$ (see
  @i:th:brauer-characters-class-function-basis).
]

Note that in case $u=1$, the algebraic integers $d^u_(i j)$ are all in $ZZ$, and
are simply the usual decomposition numbers for the group $G$.

#definition[
  The algebraic integers ${d^u_(i j)}$ defined by
  @prop:generalized-decomposition-coefficients for each $p$-element $u in G$ are
  called the _generalized decomposition numbers_ of $G$.
] <def:generalized-decomposition-numbers>

We can now state:

#theorem(name: "Brauer's Second Main Theorem", title: "Second Form")[
  Let $zeta^i in op("Irr") G$ be a character of $G$ belonging to a $p$-block
  $upright(sans(B))$. Let $u$ be a $p$-element of $G$, and set $H=C_G lr((u))$.
  Then the generalized decomposition number $d^u_(i j)=0$ unless the irreducible
  Brauer character $xi^j$ of $H$ belongs to a $p$-block $upright(sans(B))'$ of
  $H$ such that $(upright(sans(B))')^G=upright(sans(B))$.
] <th:brauer-second-main-second-form>
#idx(
  "Brauer's Second Main Theorem",
  target: [@th:brauer-second-main-second-form],
)

#proof[
  By @th:brauer-second-main-first-form, we have
  $ zeta^i lr((x u))=sum_j q_(i j) chi^j lr((x u)) $
  for each $p'$-element $x in H$, where the sum is taken over all irreducible
  $K$-characters ${chi^j}$ of $H$ belonging to $p$-blocks
  ${upright(sans(B))'_l}$ of $H$ such that
  $(upright(sans(B))'_l)^G=upright(sans(B))$. The preceding formulas, combined
  with the definition of the generalized decomposition numbers, yield the
  formula
  $ zeta^i lr((x u))=sum_j d^u_(i j) xi^j lr((x)), quad "for" x in H_(p'), $
  where the sum is taken over irreducible Brauer characters ${xi^j}$ of $H$
  belonging to $p$-blocks $upright(sans(B))'_l$ such that
  $(upright(sans(B))'_l)^G=upright(sans(B))$. Since the Brauer characters
  ${xi^j}$ are linearly independent on $H_(p')$, it follows that $d^u_(i j)=0$
  for all Brauer characters $xi^j$ belonging to $p$-blocks $upright(sans(B))'$
  of $H$ such that $(upright(sans(B))')^G != upright(sans(B))$, completing the
  proof.
]

#source(487)
#exercise-heading

#exercise[
  (Alperin). Use @th:brauer-correspondence-restriction-vertices to obtain the
  following strengthened version of
  @th:green-brauer-correspondence-compatibility. Let $D$ be a $p$-subgroup of
  $G$, and let $H$ be a subgroup such that $H >= N_G lr((D))$. Let
  $M in op("Ind") R G$, $N in op("Ind") R H$, and assume that both $M$ and $N$
  have vertex $D$. Let $M$ belong to the $p$-block $upright(sans(B))$ of $G$,
  and $N$ to the $p$-block $upright(sans(B))'$ of $H$. Prove that if
  $M arrow.l.r N$ according to the Green Correspondence, then
  $upright(sans(B))=(upright(sans(B))')^G$.
] <exc:green-brauer-correspondence-overgroups>
