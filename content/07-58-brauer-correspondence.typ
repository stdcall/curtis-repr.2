#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/58-brauer-correspondence.typ": *

== The Brauer Correspondence <sec:brauer-correspondence>
#source(461)

The main subject of this section is the connection between $p$-blocks of $G$ and
$p$-blocks of subgroups of $G$. The first connection is given by the Brauer map
$sigma$ relative to a $p$-subgroup $D$ of $G$. This defines a homomorphism of
$k$-algebras $sigma:c(k G) -> c(k N_G lr((D)))$, which is used to prove Brauer’s
First Main Theorem @th:brauer-first-main-theorem. To some extent, at least, this
theorem reduces the study of blocks with a given defect group $D$ to a situation
in which $D$ is a normal subgroup. Further group-theoretic reductions are
presented in §~@sec:brauer-correspondence-refinements. A general connection
between blocks of $G$ and blocks of subgroups of $G$, called the Brauer
Correspondence, is defined in §~@ss:brauer-correspondence-general. The Brauer
Correspondence can be interpreted in terms of central characters, in some cases
through the Brauer map with respect to a $p$-subgroup $D$, and through the Green
Correspondence of indecomposable modules (Theorem
@th:brauer-correspondence-restriction-vertices). All these approaches are
discussed, and the connections between them are worked out.

=== The Brauer Map <ss:brauer-map>

In this section $G$ denotes a finite group, $p$ a prime number, and $R$ is
either a field of characteristic $p$, or a complete d.v.r. with maximal ideal
$frak(p)$ containing $p$, as in §~@ss:block-g-algebras-trace. We first recall
some of the basic properties of $G$-algebras, trace maps, and defect groups from
the preceding section.

#idx("G-algebra")
Let $A$ be the $G$-algebra $R G$ on which $G$ acts by conjugation. For $H <= G$,
set
$ A_H={a in A:x dot a=a "for all" x in H} $
where $x dot a=x a x^(-1)$. Then $A_G$ is the center $c(R G)$ of $R G$. For
$D' <= H$, we defined a trace map
#idx("Trace map")
$
  T_(H slash D'):A_(D') -> A_H, quad
  "given by" T_(H slash D') a=sum_(x in H slash D') x dot a, quad a in A_(D').
$
We put
$ A_(H slash D')=T_(H slash D') lr((A_(D')))="the image of the trace map". $
Then $A_(H slash D')$ is a two-sided ideal in $A_H$, by
@prop:g-algebra-relative-trace-properties. A block idempotent $b$ in $A$ is a
primitive idempotent in $A_G$. A subgroup $D'$ is called a defect group of a
block idempotent $b in A_G$ provided that
$
  b in A_(G slash D'), quad "and" quad
  b in A_(G slash D'') ==> D' <=_G D''.
$
The defect groups of a block idempotent form a $G$-conjugacy class of
$p$-subgroups of $G$.

#definition[
  Let $D$ be a $p$-subgroup of $G$. The _Brauer map_ $sigma(=sigma_D)$ relative
  #source(462)
  to $D$ is the $R$-linear map $R G -> R C_G lr((D))$ defined on elements
  $x in G$ by
  $ sigma(x)=cases(x & "if" x in C_G lr((D)), 0 & "otherwise"), $
  and extended by linearity to all of $R G$.
] <def:brauer-map>
#idx("Brauer map", target: [@def:brauer-map])
#nidx(
  "$sigma$",
  "Brauer map (relative to a p-subgroup of G)",
  target: [@def:brauer-map],
)

The Brauer map has many interesting and subtle properties, which are used to
relate $p$-blocks of $G$ to $p$-blocks of subgroups of $G$. Following Alperin
and Broué @bib:Alperin1979, we summarize some of the basic facts about the
Brauer map in the next lemma. In our notation, we take $frak(p)=0$ if $R$ is a
field of characteristic $p$.

#lemma[
  Let $D <= H <= G$, for a $p$-subgroup $D$ of $G$, and let $sigma$ be the
  Brauer map relative to $D$. Then the following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[$sigma(A) subset.eq R C_G lr((D))$.] <case:brauer-map-image>],
    [#case[If $D C_G lr((D)) <= H <= N_G lr((D))$, then
      $sigma(A_G) subset.eq c(R H)$.] <case:brauer-map-normalizer-centrality>],
    [#case[If $L$ is an $H$-class sum whose class defect group#footnote[See
        @def:conjugacy-class-defect-group.] <fn:brauer-map-class-defect>
      contains no $H$-conjugate of $D$, then
      $sigma L=0$.] <case:brauer-map-class-defect-vanishing>],
    [#case[For any $D' <= H$ such that $D lt.eq.not_H D'$, we have
      $sigma(A_(H slash D'))=0 (mod frak(p) A)$.] <case:brauer-trace-zero>],
    [#case[We have $A_D=R C_G lr((D))+sum_(D'<D) A_(D slash D')$, and the map
      $sigma:A_D -> R C_G lr((D))$ is a homomorphism mod $frak(p)$, in the sense
      that for $a,a' in A_D$,
      $
        sigma(a a')=sigma(a)sigma(a') (mod frak(p) A).
      $] <case:brauer-map-modular-homomorphism>],
    [#case[For $a in A_D$,
      $
        sigma(T_(G slash D) a)=T_(N_G lr((D)) slash D) lr((sigma a))
        (mod frak(p) A).
      $] <case:brauer-map-relative-trace-compatibility>],
  )
] <lem:brauer-map-properties>

#proof[
  Part~@case:brauer-map-image is clear. For
  @case:brauer-map-normalizer-centrality, from $H <= N_G lr((D))$ we obtain
  $C_G lr((D)) ⊴ H$, and therefore
  $ sigma(y dot a)=y dot sigma(a) quad "for all" a in A, quad y in H. $
  <eq:brauer-map-normalizer-equivariance>
  If $a in A_G$, then $y dot sigma(a)=sigma(a)$ for all $y in H$, and
  @case:brauer-map-normalizer-centrality holds.

  @case:brauer-map-class-defect-vanishing Let $frak(L)$ be the $H$-conjugacy
  class defining $L$. If $sigma L != 0$, then
  $frak(L) inter C_G lr((D)) != emptyset$, and $D$ is contained in some class
  defect group of $frak(L)$,#footnote(
    <fn:brauer-map-class-defect>,
  ) completing the proof of @case:brauer-map-class-defect-vanishing.

  @case:brauer-trace-zero By @prop:trace-image-class-defect-support we have
  $ A_(H slash D')=sum R L_i (mod frak(p) A) $
  where the ${L_i}$ are $H$-class sums whose defect groups satisfy
  $D_i <=_H D'$. If $D lt.eq.not_H D'$, then $D lt.eq.not_H D_i$ for each $i$,
  and the result follows from @case:brauer-map-class-defect-vanishing.
  #source(463)

  @case:brauer-map-modular-homomorphism By
  @prop:trace-image-class-defect-support again, $A_D$ has an $R$-basis
  consisting of the $D$-class sums
  $
    L=sum_(u in D slash C_D lr((x))) u dot x=T_(D slash C_D lr((x))) x,
    quad "for" x in G.
  $
  Such a class sum is in $R C_G lr((D))$ if $x in C_G lr((D))$, while if
  $x in.not C_G lr((D))$, then $C_D lr((x))<D$ and
  $
    L in A_(D slash C_D lr((x))) subset.eq A_(D slash D')
    quad "for" D'=C_D lr((x))<D.
  $
  This proves the first assertion in @case:brauer-map-modular-homomorphism. For
  the second, write
  $ A_D=R C_G lr((D))+X, quad "where" X=sum_(D'<D) A_(D slash D'). $
  Then $X$ is a two-sided ideal in $A_D$, by
  @prop:g-algebra-relative-trace-properties. Moreover,
  $sigma(X) subset.eq frak(p) A$, by part~@case:brauer-trace-zero. It now
  follows easily that $sigma$ is a homomorphism mod $frak(p)$, for let
  $a,a' in A_D$, and write
  $
    a equiv u (mod X), quad a' equiv u' (mod X), quad
    "with" u,u' in R C_G lr((D)).
  $
  Then $a a' equiv u u' (mod X)$, and hence
  $
    sigma(a a')=sigma(u u')=sigma(u)sigma(u')=sigma(a)sigma(a')
    (mod frak(p) A),
  $
  as required.

  @case:brauer-map-relative-trace-compatibility By
  @prop:relative-trace-mackey-formulas, we have
  $
    T_(G slash D) a=sum_x
    T_(N_G lr((D)) slash (N_G lr((D)) inter attach(D, tl: x)))
    (x dot a), quad "for all" a in A_D,
  $
  where the sum is taken over a cross section of the $(N_G lr((D)),D)$-double
  cosets in $G$. Now apply $sigma$ to both sides of this formula. For each
  double coset $N_G lr((D))x D$, we have
  $
    D <=_(N_G lr((D))) (N_G lr((D)) inter attach(D, tl: x)) <==>
    N_G lr((D)) inter attach(D, tl: x)=D quad "and" quad x in N_G lr((D)).
  $
  Therefore
  $
    sigma(T_(G slash D) a)=sigma(T_(N_G lr((D)) slash D) a)
    (mod frak(p) A)
  $
  by part~@case:brauer-map-class-defect-vanishing and
  @prop:trace-image-class-defect-support. Finally,
  $ sigma(T_(N_G lr((D)) slash D) a)=T_(N_G lr((D)) slash D) sigma a $
  by @eq:brauer-map-normalizer-equivariance. This completes the proof of the
  lemma.
]

Several parts of the lemma come into sharp focus in the next result.

#proposition[
  Let $k$ be a field of characteristic $p$, and let $A$ be the $G$-algebra
  #source(464)
  $k G$. The Brauer map $sigma:A_G -> k C_G lr((D))$ (relative to $D$) defines a
  $k$-algebra homomorphism from $A_G$ into $c(k N_G lr((D)))$, whose kernel is
  precisely
  $ frak(A)=sum_(D'<=G, D lt.eq.not_G D') A_(G slash D'). $
  Moreover, $sigma$ defines a surjection of $k$-algebras
  $ A_(G slash D) -> T_(N_G lr((D)) slash D) lr((k C_G lr((D)))) $
  whose kernel contains no block idempotents of $G$ with defect group $D$.
] <prop:brauer-map-kernel-trace-image>

#proof[
  Since $A_G subset.eq A_D$, $sigma$ defines a $k$-algebra homomorphism by
  @lem:brauer-map-properties@case:brauer-map-modular-homomorphism, using $R=k$.
  Further, $sigma(A_G) subset.eq c(k N_G lr((D)))$ by
  @lem:brauer-map-properties@case:brauer-map-normalizer-centrality, using
  $H=N_G lr((D))$. By @lem:brauer-map-properties@case:brauer-trace-zero we have
  $
    A_(G slash D') subset.eq ker sigma quad "for all" D'<=G
    quad "with" D lt.eq.not_G D'.
  $
  Therefore $frak(A) subset.eq ker sigma$. To prove that $frak(A)=ker sigma$, we
  use the fact that $A_G$ has a $k$-basis consisting of $G$-class sums
  $
    C=sum_(y in frak(C)) y=T_(G slash C_G lr((x))) x,
    quad "for" x in frak(C).
  $
  By @lem:brauer-map-properties@case:brauer-trace-zero, $C in ker sigma$ unless
  $D <= C_G lr((x))$ for some $x in frak(C)$. In that case,
  $frak(C) inter C_G lr((D)) != emptyset$, and
  $ sigma C=C'=sum_(y in frak(C) inter C_G lr((D))) y != 0. $
  Since the $G$-conjugacy classes, and their nonempty intersections with
  $C_G lr((D))$ are disjoint, it follows that
  $ a in ker sigma <==> a in frak(A) quad "for all" a in A_G, $
  and the first statement is proved.

  The final statement in the proposition follows at once from
  @lem:brauer-map-properties@case:brauer-map-relative-trace-compatibility and
  the first part of the proof. In particular, no block idempotent with defect
  group $D$ is in $frak(A)$, by Rosenberg’s Lemma
  @lem:rosenberg-primitive-idempotent-ideal-sum and the fact that
  $A_(G slash D')$ is a two-sided ideal in $A_G$ for all $D' <= G$. This
  completes the proof.
]

=== Brauer’s First Main Theorem <ss:brauer-first-main-theorem>

We carry over the notation from §~@ss:brauer-map. The main result of this
subsection establishes a bijection from the set of $p$-blocks of $G$ with a
given defect group $D$ to the set of $p$-blocks of $N_G lr((D))$ with defect
group $D$. Thus, it is natural to begin with some properties of block
idempotents and defect groups in finite groups having a normal $p$-subgroup.
#source(465)

#proposition[
  Let $G$ be a finite group with a normal $p$-subgroup $D$, and let $A$ be the
  $G$-algebra $R G$, as in §~@ss:brauer-map. Then the following statements hold:
  #case-list(
    numbering: "(i)",
    [#case[For every block idempotent $b in A_G$, we have
      $
        b in R C_G lr((D)) inter A_G+frak(p) A_G.
      $] <case:normal-p-block-support>],
    [#case[$D$ is contained in the defect groups of all block idempotents in
      $A_G$.] <case:normal-p-contained-defects>],
  )
] <prop:normal-p-subgroup-block-idempotents>

#proof[
  @case:normal-p-block-support Put $C=A_G$ and $b_1=sigma(b)$. Since $D ⊴ G$,
  @eq:brauer-map-normalizer-equivariance shows that $b_1 in C$. By Lemma
  @lem:brauer-map-properties@case:brauer-map-modular-homomorphism,
  $ z=b-b_1 in X=sum_(D'<D) A_(D slash D'). $
  #ed-note[
    Over the field of three elements, take $G=S_3 times C_3$ and
    $D=A_3 times 1$. The full trace $T_(G slash 1)$ is zero, but a transposition
    class sum is not supported in $C_G lr((D))$. Also $1-4^2 in.not 9 ZZ_3$, so
    congruence modulo a radical does not give the asserted congruence modulo its
    square.
  ]
  Let $tau:R G -> R(G slash D)$ be the natural surjection. For $a in A_(D')$ and
  $D'<D$, we have
  $ tau(T_(D slash D') a)=abs(D colon D') tau(a) in frak(p) R(G slash D). $
  Since $ker tau subset.eq rad A$ by @i:prop:normal-p-subgroup-radical-kernel
  and $frak(p) A subset.eq rad A$ by @prop:order-radical-reduction, it follows
  that $X subset.eq rad A$. Thus $z in C inter rad A subset.eq rad C$: for
  $c in C$, the inverse of $1-c z$ in $A$ is central. Put $J=rad C$. Since
  $C slash frak(p) C$ is a finite-dimensional commutative
  $R slash frak(p)$-algebra, $J^N subset.eq frak(p) C$ for some positive integer
  $N$. Choose $r$ such that $p^r >= N$. The elements $b_1,z$ commute, and every
  interior binomial coefficient for the exponent $p^r$ is divisible by $p$.
  Consequently
  $
    b=b^(p^r)=(b_1+z)^(p^r) equiv b_1^(p^r)+z^(p^r)
    equiv b_1^(p^r) (mod frak(p) C).
  $
  Since $b_1 in R C_G lr((D)) inter C$, this proves the assertion.

  @case:normal-p-contained-defects Let $b$ be a block idempotent in $A_G$. From
  part~@case:normal-p-block-support, it follows that
  $ b=sum a_i L_i (mod frak(p) A_G), quad "with" a_i in R, $
  where the ${L_i}$ are $G$-class sums whose class defect groups $D_i$ contain
  $D$. On the other hand, if $D'$ is a defect group of $b$, then $D_i =_G D'$
  for the class defect group $D_i$ of some class sum $L_i$ whose coefficient
  $a_i in.not frak(p)$, by Theorem @th:block-defect-class-sum-characterization.
  Since $D$ is a normal subgroup, we obtain $D <= D'$, completing the proof.
]

Returning to the general situation, we shall establish the first of several
basic results of Brauer (@bib:Brauer1956, @bib:Brauer1959), which are called the
First, Second, and Third Main Theorems. Brauer first proved the theorem below in
case the coefficient ring $R$ is a splitting field of characteristic $p$ (Brauer
@bib:Brauer1956; see also @bib:CurtisReiner1962[CR], §87). The approach to
follow is based on Alperin–Broué @bib:Alperin1979.

#theorem(name: "Brauer’s First Main Theorem")[
  Let $G$ be a finite group, $D$ a $p$-subgroup
  #source(466)
  of $G$, and set $H=N_G lr((D))$. Let $sigma:c(R G) -> c(R H)$ denote the
  Brauer map with respect to $D$. For each block idempotent $b in c(R G)$ with
  defect group $D$, there exists a unique block idempotent $b' in c(R H)$ with
  defect group $D$ such that
  $ sigma b equiv b' (mod frak(p)c(R H)). $
  <eq:brauer-first-main-idempotent-correspondence>
  The mapping @eq:brauer-first-main-idempotent-correspondence defines a
  bijection from the set of block idempotents in $c(R G)$ with defect group $D$
  to the set of block idempotents in $c(R H)$ with defect group $D$.
] <th:brauer-first-main-theorem>
#idx("Brauer's First Main Theorem", target: [@th:brauer-first-main-theorem])

#proof[
  #idx("Brauer map")
  First assume the coefficient ring is a field $k$ of characteristic $p$. Let
  $A$ denote the $G$-algebra $k G$, and $A'$ the $H$-algebra $k H$, so
  $A_G=c(k G)$ and $A'_H=c(k H)$. By @prop:brauer-map-kernel-trace-image and
  @lem:brauer-map-properties@case:brauer-map-normalizer-centrality, the Brauer
  map $sigma$ relative to $D$ defines a surjection of $k$-algebras
  $ sigma:A_(G slash D) -> T_(H slash D) lr((k C_G lr((D)))) subset.eq A'_H. $
  Put $I=A_(G slash D)$ and $J=sigma(I)$. Decompose the finite-dimensional
  commutative algebra $A_G$ into its local factors. In each factor, $I$ is
  either the whole factor or a proper, hence nilpotent, ideal. A primitive
  factor idempotent belongs to $I$ precisely when its block has defect group
  subconjugate to $D$, by @def:primitive-idempotent-defect-group. Those of
  strictly smaller defect are killed by $sigma$, by
  @lem:brauer-map-properties@case:brauer-trace-zero; those of defect $D$
  survive, by @prop:brauer-map-kernel-trace-image.
  #ed-note[
    In $k S_3$ with $k=ZZ slash 2 ZZ$, let $a$ be a $3$-cycle and $D$ a subgroup
    of order $2$. Then $a+a^2$ is a primitive central idempotent with trivial
    defect group, belongs to $A_(G slash D)$, and is killed by $sigma$.
  ]
  The image of each surviving full factor is a local algebra, so its unit
  remains primitive. The images of the proper factor ideals are nilpotent and
  orthogonal to the full-factor images; they contribute no nonzero idempotents.
  Thus $sigma$ gives a bijection from the block idempotents of defect $D$ to the
  primitive idempotents of $J$. This uses the local factor argument of Exercise
  @exc:commutative-algebra-primitive-idempotent-surjection on the full factors,
  without assuming that $I$ has an identity. To complete the proof in this case,
  it remains to show (i) that each primitive idempotent in $A'_H$ with defect
  group $D$ belongs to $T_(H slash D) lr((k C_G lr((D))))$, and (ii) that for
  each primitive idempotent $b in A_(G slash D)$ with defect group $D$,
  $sigma(b)=b'$ is a primitive idempotent in $A'_H$ with defect group $D$.

  For the first statement, let $b^*$ be a primitive idempotent in $A'_H$ with
  defect group $D$. Since $D ⊴ H$, we have $b^* in k C_G lr((D)) inter A'_H$ by
  @prop:normal-p-subgroup-block-idempotents@case:normal-p-block-support.
  Therefore $sigma b^*=b^*$. Since $b^*$ has defect group $D$, we obtain
  $b^*=T_(H slash D) a$ for some $a in A'$, and hence
  $
    b^*=sigma b^*=sigma T_(H slash D) a=T_(H slash D) sigma a
    in T_(H slash D) lr((k C_G lr((D)))),
  $
  using @eq:brauer-map-normalizer-equivariance, and the fact that $D ⊴ H$.

  To prove (ii), we begin with the fact that $sigma(b)=b'$ is primitive in
  $T_(H slash D) lr((k C_G lr((D)))) subset.eq A'_(H slash D)$, and have to
  prove that $b'$ is primitive in $A'_H$ with defect group $D$. By
  @prop:normal-p-subgroup-block-idempotents@case:normal-p-contained-defects,
  $b'$ will have defect group $D$ if we can prove it is primitive in $A'_H$.
  Suppose it is not; then $b'=sum_(i=1)^m b'_i$ with $m>1$, for some block
  idempotents ${b'_i}$ in $A'_H$. Since
  $b'_i in.not T_(H slash D) lr((k C_G lr((D))))$, its defect group properly
  contains $D$, by part (i), for $1<=i<=m$. On the other hand,
  $b'_i=b'_i b' in A'_(H slash D)$ for each $i$, since $A'_(H slash D)$ is a
  two-sided ideal in $A'_H$. This is a contradiction, and establishes that $b'$
  is primitive in $A'_H$, completing the proof of the theorem in case $R$ is a
  field.

  Now let $R$ be a complete d.v.r. with quotient field $K$, and residue field
  $k=R slash frak(p)$ of characteristic $p$. Then $(K,R,k)$ is a $p$-modular
  system which is admissible for $G$ (see @def:admissible-modular-system). By
  @cor:trace-image-modular-reduction, it follows that the map
  $a mapsto overline(a)$ from $R G$ to $k G$ defines a bijection from the block
  idempotents in $R G$ with defect group $D$, to those in $k G$ with defect
  group $D$. The same statement holds for block idempotents in
  #source(467)
  $R H$ and $k H$. Moreover, the Brauer map, relative to $D$, from $k G$ to
  $k C_G lr((D))$ is clearly the map defined by
  $ overline(a) mapsto overline(sigma(a)), quad "for" a in R G, $
  where $sigma$ is the Brauer map, relative to $D$, on $R G$. From these remarks
  and the first part of the proof, it follows that there exists a bijection
  satisfying @eq:brauer-first-main-idempotent-correspondence from the set of
  block idempotents in $R G$ with defect group $D$ to those in $R H$ with defect
  group $D$, completing the proof of the theorem.
]

An important extension of the First Main Theorem is given in
§~@ss:brauer-first-main-theorem-extension.

=== The Brauer Correspondence <ss:brauer-correspondence-general>

Brauer’s First Main Theorem @th:brauer-first-main-theorem establishes a
connection between $p$-blocks of $G$ with a given defect group $D$, and
$p$-blocks of $N_G lr((D))$ with defect group $D$. Using the theory of central
characters, Brauer defined a more general connection, called the Brauer
correspondence, between $p$-blocks of $G$ and $p$-blocks of certain subgroups of
$G$. The bijection described in @th:brauer-first-main-theorem turns out to be a
special case of the Brauer correspondence (see Exercise
@exc:brauer-first-main-correspondence-compatibility).

Throughout this subsection, $(K,R,k)$ denotes a $p$-modular system which is
admissible for $G$ (see @def:admissible-modular-system).

#idx("Central character")
From §~@ss:central-characters-blocks we recall that a central character of $R G$
is a homomorphism of $R$-algebras
$ lambda:c(R G) -> k' $
where $k'$ is a finite extension field of $k$. The central characters of $R G$
are in bijective correspondence with the central characters of $k G$. There is
also a bijection between $p$-blocks of $G$ and equivalence classes of central
characters of $R G$. A central character $lambda$ of $R G$ corresponds to a
$p$-block $upright(sans(B))$ of $G$ if and only if
$ lambda(b)=1 quad "and" quad lambda(b')=0 quad "for all" b'!=b, $
where $b$ is the block idempotent of $upright(sans(B))$, and ${b'}$ are the
block idempotents of blocks $upright(sans(B))'!=upright(sans(B))$.

By @prop:split-modular-central-characters, the central characters of $R G$
themselves are in bijective correspondence with the $p$-blocks of $G$, in case
$k$ is a splitting field for $G$. In this situation, distinct central characters
are inequivalent.

#definition[
  Let $(K,R,k)$ be a $p$-modular system which is admissible for $G$. Let $H$ be
  a subgroup of $G$, and $psi'$ a central character of $R H$ associated with the
  $p$-block $upright(sans(B))'$ of $H$. Then $psi'$ determines an $R$-linear map
  $(psi')^G:c(R G) -> k'$ as follows.#footnote[The map $(psi')^G$ has nothing to
    do with induction of characters of modules.] Let $C=sum_(x in frak(C)) x$ be
  a class sum in $c(R G)$. Put
  #source(468)
  $ C'=sum_(x in frak(C) inter H) x in c(R H), $
  if $frak(C) inter H != emptyset$, and put $C'=0$ otherwise. The class sums $C$
  form an $R$-basis for $c(R G)$, so we may define an $R$-linear map $(psi')^G$
  by setting
  $
    (psi')^G lr((C))=cases(
      psi'(C') & "if" frak(C) inter H != emptyset,
      0 & "if" frak(C) inter H=emptyset
    ).
  $
  If the $R$-linear map $(psi')^G$ is a central character of $R G$, the
  $p$-block of $G$ associated with $(psi')^G$ will be denoted by
  $(upright(sans(B))')^G$, and we shall say that the _Brauer correspondence is
  defined_ for the block $upright(sans(B))'$. Then $(upright(sans(B))')^G$ is
  the _Brauer correspondent_ of $upright(sans(B))'$.
] <def:brauer-correspondence>
#idx("Brauer Correspondence", target: [@def:brauer-correspondence])
#nidx(
  "$upright(sans(B))' -> (upright(sans(B))')^G$",
  "means Brauer Correspondence of p-blocks",
  target: [@def:brauer-correspondence],
)

It is easily verified that if $psi'$ and $psi''$ are equivalent central
characters of $R H$ in the sense of @def:central-character-finite-algebra, and
if $(psi')^G$ and $(psi'')^G$ are central characters of $R G$, then $(psi')^G$
and $(psi'')^G$ are equivalent. Thus the Brauer correspondence
$upright(sans(B))' mapsto (upright(sans(B))')^G$, when it is defined, is
independent of the choice of representatives of equivalence classes of central
characters.

The purpose of this subsection is to give other useful interpretations of the
Brauer correspondence, and conditions under which it is defined, following
Brauer @bib:Brauer1959, Alperin @bib:Alperin1977, Okuyama @bib:Okuyama1978, and
Alperin–Burry @bib:Alperin1980.

As a start, we show that in some cases the Brauer correspondence can be defined
in terms of the Brauer map $sigma$, occurring in §~@ss:brauer-map.

#theorem[
  Let $(K,R,k)$ be a $p$-modular system such that $"char" K=0$ and $K$ is
  sufficiently large relative to $G$. Let $D$ be a $p$-subgroup of $G$, and let
  $H$ be a subgroup such that
  $ D C_G lr((D)) <= H <= N_G lr((D)). $
  Then the Brauer correspondence
  $upright(sans(B))' mapsto (upright(sans(B))')^G$ is defined for all $p$-blocks
  $upright(sans(B))'$ of $H$. If $psi'$ is a central character of $R H$, then
  the central character $(psi')^G$ of $R G$ is given by
  $ (psi')^G=psi' compose sigma $
  where $sigma:c(R G) -> c(R H) inter R C_G lr((D))$ is the Brauer map relative
  to $D$ (see @def:brauer-map).
] <th:brauer-correspondence-brauer-map>
#idx(
  "Brauer Correspondence",
  "and Brauer map",
  target: [@th:brauer-correspondence-brauer-map],
)
#idx("Brauer map", target: [@th:brauer-correspondence-brauer-map])

#proof[
  Let $psi'$ be an arbitrary central character of $R H$. By Lemma
  @lem:brauer-map-properties, the Brauer map
  $sigma:c(R G) -> c(R H) inter R C_G lr((D))$ is a homomorphism mod $frak(p)$.
  Since $frak(p) R H subset.eq ker psi'$, the map $psi' compose sigma$ is a
  central character of $R G$, and we have only to prove that
  $psi' compose sigma=(psi')^G$. Let $C=sum_(x in frak(C)) x$ be a class sum in
  $R G$, and suppose that $frak(C) inter H != emptyset$. Then
  $ C'=sum_(x in frak(C) inter H) x=sum_i C'_i+sum_j C''_j $
  where the ${C'_i}$ are class sums in $c(R H)$ supported by classes in
  $frak(C) inter C_G lr((D))$, while
  #source(469)
  the ${C''_j}$ are class sums in $c(R H)$ supported by $H$-conjugacy classes
  $frak(C)'_j$ such that $frak(C)'_j inter C_G lr((D))=emptyset$. We have
  $ (psi')^G lr((C))=psi'(C')=sum_i psi'(C'_i)+sum_j psi'(C''_j). $
  Since
  $ (psi' compose sigma)(C)=sum_i psi'(C'_i), $
  it is sufficient to prove that
  $ psi'(C''_j)=0 quad "for each" j. $
  Let $D'$ be a defect group of the $p$-block of $H$ associated with $psi'$. By
  Theorems @th:block-defect-class-sum-characterization and
  @eq:central-character-vanishes-smaller-defect, $psi'$ vanishes on all
  $H$-class sums in $c(R H)$ whose class defect groups do not contain an
  $H$-conjugate of $D'$. We also have $D <= D'$ by
  @prop:normal-p-subgroup-block-idempotents, since $D ⊴ H$. For each of the
  $H$-classes $frak(C)$ such that $frak(C) inter C_G lr((D))=emptyset$, the
  class defect groups do not contain $D$, and hence contain no $H$-conjugate of
  $D'$. Thus $psi'(C''_j)=0$ for each $j$, as required.
]

#corollary[
  Keep the hypothesis of @th:brauer-correspondence-brauer-map. If
  $upright(sans(B))'_1$ is the principal block of $H$, then
  $(upright(sans(B))'_1)^G=upright(sans(B))_1$, where $upright(sans(B))_1$ is
  the principal block of $G$.
] <cor:brauer-correspondence-principal-block>
#idx(
  "Principal p-block",
  "Brauer correspondent of",
  target: [@cor:brauer-correspondence-principal-block],
)

#proof[
  Let $psi'_1$ be the central character of $R H$ associated with
  $upright(sans(B))'_1$. By @cor:block-central-character-congruence we have
  $ psi'_1(C')=abs(frak(C)') $
  for each $H$-class sum $C'$ supported on $frak(C)'$. By
  @th:brauer-correspondence-brauer-map we have
  $
    (psi'_1)^G lr((C))=(psi'_1 compose sigma)(C)=abs(frak(C) inter C_G lr((D)))
  $
  for each $G$-class sum $C$ supported on $frak(C)$. However,
  $ abs(frak(C)) equiv abs(frak(C) inter C_G lr((D))) (mod p) $
  since $D$ is a $p$-group, by consideration of the orbits of the action of $D$
  on $frak(C)$. Thus
  $ (psi'_1)^G lr((C))=abs(frak(C)) $
  and $(psi'_1)^G$ corresponds to the principal block of $G$, by
  @cor:block-central-character-congruence again.
]

#corollary[
  Keep the notation of @th:brauer-correspondence-brauer-map. Let $b$ be a block
  idempotent of $R G$, associated with the $p$-block $upright(sans(B))$. Then
  either $sigma b equiv 0 (mod frak(p) R H)$ or
  $ sigma b equiv sum b'_i (mod frak(p) R H) $
  #source(470)
  where the sum is taken over block idempotents ${b'_i}$ of $R H$ associated
  with $p$-blocks ${upright(sans(B))'_i}$ of $H$ such that
  $(upright(sans(B))'_i)^G=upright(sans(B))$ for each $i$. We have
  $sigma b equiv 0 (mod frak(p) R H)$ if and only if there is no $p$-block
  $upright(sans(B))'$ of $H$ such that $(upright(sans(B))')^G=upright(sans(B))$.
] <cor:brauer-map-block-idempotent-fibres>

#proof[
  Let $overline(sigma):c(k G) -> c(k H)$ be the Brauer map defined on the center
  of $k G$. Then
  $
    overline(sigma)(overline(a))=overline(sigma(a))
    quad "for all" a in c(R G)
  $
  (see the proof of @th:brauer-first-main-theorem). Since $overline(sigma)$ is a
  homomorphism of $k$-algebras, $overline(sigma)(overline(b))$ is either zero or
  a sum of block idempotents in $k H$. If the image is zero, then
  $sigma(b) in frak(p) R H$, and for all central characters $psi'$ of $R H$ we
  have $psi'(sigma(b))=0$. This clearly occurs if and only if there is no
  $p$-block $upright(sans(B))'$ of $H$ such that
  $(upright(sans(B))')^G=upright(sans(B))$.

  Now assume $overline(sigma)(overline(b)) != 0$, and let
  $overline(sigma)(overline(b))=sum beta'_i$, where ${beta'_i}$ are block
  idempotents in $k H$. Then there exist block idempotents ${b'_i}$ in $R H$
  such that $overline(b)'_i=beta'_i$ for each $i$, and
  $ sigma b equiv sum b'_i (mod frak(p) R H). $
  Let ${psi'_i}$ be the central characters of $R H$ associated with the block
  idempotents ${b'_i}$ in the blocks ${upright(sans(B))'_i}$ of $R H$. Then we
  have $(upright(sans(B))'_i)^G=upright(sans(B))$ for each $i$ by the definition
  of the Brauer correspondence, since $(psi'_i)^G lr((b))=1$ for each $i$.
  Finally, let $b'$ be a block idempotent of $R H$ associated with the central
  character $psi'$, and assume that $(psi')^G=psi$, where $psi$ is a central
  character of $R G$ such that $psi(b)=1$. Then
  $ psi'((sigma b)b')=(psi')^G lr((b))psi'(b') != 0, $
  and hence $(sigma b)b' != 0$. This shows that $b'=b'_i$ for some $i$,
  completing the proof.
]

Suppose now that $(K,R,k)$ is a $p$-modular system, with $R$ a complete d.v.r.
For an arbitrary subgroup $H$ of $G$, we wish to investigate whether the Brauer
correspondence is defined for blocks of $H$. This will be accomplished by
obtaining another criterion (see
@prop:brauer-correspondence-endomorphism-criterion) for each central character
$psi'$ of $H$ to yield a central character $(psi')^G$ of $G$.

As in §~@ss:block-defect-groups-vertices, we view $R G$ as an
$R(G times G)$-lattice, with the action of $G times G$ given by
$ (x,y)a=x a y^(-1), quad "for" x,y in G, quad a in R G. $
For $T$ any subset of $G$ let $R T$ denote the $R$-sublattice of $R G$ spanned
by the elements of $T$. Further, let $Delta:H -> H times H$ denote the diagonal
map. Given an $R(G times G)$-lattice $M$, its restriction $M_(H times H)$ is an
$R(H times H)$-lattice. Each block idempotent $b' in c(R H)$ determines a block
ideal $B'=R H b'$ and a $p$-block $upright(sans(B))'$ of $H$.

As usual, we shall use the notation $M divides N$, for $A$-modules $M$ and $N$,
to mean that $M$ is isomorphic to a direct summand of $N$.

#lemma[
  Let $B'$ be a block ideal of $R H$.
  #source(471)
  #case-list(
    numbering: "(i)",
    [#case[We have
      $
        B' divides R(H y H) quad "and" quad
        R(H y H) divides (R G)_(H times H)
      $
      for some $(H,H)$ double coset $H y H$ in
      $G$.] <case:block-ideal-double-coset-summand>],
    [#case[For each $y in G$,
      $
        "Stab"_(H times H)y=
        attach((Delta(H inter attach(H, tl: y^(-1)))), tl: (y,1)).
      $
      Setting $X="Stab"_(H times H)y$, the $R(H times H)$-module $R(H y H)$ is
      $(H times H,X)$-projective.] <case:double-coset-bimodule-stabilizer>],
  )
] <lem:block-ideal-double-coset-summand>

#proof[
  Let $G=union.big_(i=1)^m H y_i H$; then we clearly have
  $ (R G)_(H times H)=plus.o.big_(i=1)^m R(H y_i H). $
  Since $R$ is complete and $B'$ is an indecomposable $R(H times H)$-lattice, it
  follows from the K-S-A Theorem that for some $i$, $1<=i<=m$,
  $B' divides R(H y_i H)$. Each $R(H times H)$-lattice of the form $R(H y H)$ is
  a transitive permutation module, with an $R$-basis consisting of the
  transitive $H times H$-set $H y H$. Then
  $R(H y H) tilde.equiv "ind"_X^(H times H) 1_X$ where $1_X$ is the trivial
  $R X$ module and $X="Stab"_(H times H)y$. By
  @i:th:gaschutz-relative-projectivity(v), $R(H y H)$ is
  $(H times H,X)$-projective. Finally,
  $"Stab"_(H times H)y=
  attach((Delta(H inter attach(H, tl: y^(-1)))), tl: (y,1))$
  by the proof of @lem:double-coset-permutation-module-vertex, completing the
  proof.
]

#lemma[
  Let $B'$ be a block ideal in $R H$ defined by the block idempotent $b'$. Then
  there exist isomorphisms of $R$-algebras
  $ alpha:c(R G) -> E="End"_(R(G times G)) R G $
  and
  $ alpha':c(B') -> E'="End"_(R(H times H)) B', $
  given by
  $ alpha(a)=a_l quad "and" quad alpha'(a')=(a')_l, $
  where $a_l$ and $(a')_l$ denote left multiplication by $a$ and $a'$ on $R G$
  and $B'$, respectively.
] <lem:block-centers-bimodule-endomorphisms>

#proof[
  It is clear that the map $alpha$ is an injective homomorphism of $R$-algebras.
  If $f in E$, then $f=a_l$ for some $a in R G$, since the left regular module
  $R G$ has the double centralizer property. Since $f$ also commutes with the
  left multiplications, it follows that $a in c(R G)$. Since $B'$ is an
  $R$-algebra with identity element $b'$, the same argument shows that $alpha'$
  is an isomorphism.
]

#corollary[
  Keep the notation of @lem:block-centers-bimodule-endomorphisms. Then
  $ E'="End"_(R(H times H)) B' $
  is a f.g. commutative local $R$-algebra, and $E' slash rad E'$ is a finite
  extension field of $k=R slash frak(p)$.
] <cor:block-endomorphism-residue-field>
#source(472)

#proof[
  Since $B'$ is an indecomposable $R(H times H)$-lattice, $E'$ is a local ring
  by @i:prop:indecomposable-local-endomorphism-ring. Moreover, $E'$ is
  commutative by @lem:block-centers-bimodule-endomorphisms, and
  $frak(p) E' subset.eq rad E'$ by @prop:order-radical-reduction. Thus
  $E' slash rad E'$ is a f.d. $k$-algebra, and the result follows.
]

Keep the notation of @lem:block-centers-bimodule-endomorphisms. The following
definitions will be used in the next three results. Since
$B' subset.eq R H subset.eq R G$, choose the natural inclusion
$ i:B' -> (R G)_(H times H) $
and the coefficient projection
$ j:(R G)_(H times H) -> B', quad j(a)=a_H b', $
where $a_H$ denotes the sum of the terms of $a$ supported in $H$. Both are
$R(H times H)$-homomorphisms, and $j i="id"_(B')$.#ed-note[
  With $R=ZZ_3$, $G=C_2=chevron.l g chevron.r$ and $H=1$, the splitting
  $i(1)=(1+g)/2$, $j="augmentation"$ makes $lambda theta$ multiplicative,
  whereas coefficient restriction sends $g$ to $0$ and $g^2$ to $1$. Arbitrary
  splitting maps therefore do not give the stated criterion.
] Using these maps we define an $R$-linear map
$ theta:E -> E' quad "by" theta(f)=j f i, quad f in E. $
Let $lambda$ be the natural homomorphism of $R$-algebras
$ lambda:E' -> k'=E' slash rad E' $
given in @cor:block-endomorphism-residue-field, where $k'$ is a finite extension
field of $k$. The key result is:

#proposition[
  (Okuyama @bib:Okuyama1978). Let $H <= G$, and let $upright(sans(B))'$ be a
  $p$-block of $H$. Then the Brauer correspondent $(upright(sans(B))')^G$ of
  $upright(sans(B))'$ is defined (see @def:brauer-correspondence) if and only if
  the $R$-linear map
  $ lambda theta:E -> E' -> k'=E' slash rad E' $
  is a homomorphism of $R$-algebras.
] <prop:brauer-correspondence-endomorphism-criterion>

#proof[
  For each element $a=sum_(x in G) c_x x in R G$, let
  $ a_H=sum_(x in H)c_x x, quad "and" quad a_(G-H)=sum_(x in.not H)c_x x. $
  Then $a=a_H+a_(G-H)$, and $a_H in c(R H)$ whenever $a in c(R G)$. For each
  $a in c(R G)$, let $tau(a)=a_H b'$, where $b'$ is the block idempotent in
  $R H$ associated with $upright(sans(B))'$, and set $B'=R H b'$. Then
  $tau(a) in c(B')$, and we shall prove that the diagram #numbered-block[
    #brauer-endomorphism-square
  ] <eq:brauer-endomorphism-square>
  #source(473)
  is commutative, where $alpha$ and $alpha'$ are the isomorphisms defined in
  @lem:block-centers-bimodule-endomorphisms, and $theta f=j f i$, as above, for
  $f in E$. Let $a in c(R G)$; then
  $ alpha'(tau(a))=(a_H b')_l quad "and" quad theta alpha(a)=j a_l i. $
  Applying these maps to $t in B'$, we have
  $ (a_H b')_l t=a_H t quad "and" quad (j a_l i)(t)=j(a t), $
  so it is sufficient to check that $a_H t=j(a t)$, for all $t in B'$. We have
  $a t=a_H t+a_(G-H)t$, and it is easily checked that $j(a_H t)=a_H t$ while
  $j(a_(G-H)t)=0$, using the fact that $R G$ is a free right $R H$-module with a
  basis given by a cross section of $G slash H$. This proves the commutativity
  of @eq:brauer-endomorphism-square.

  Now let
  $ psi':c(R H) -> c(B') slash rad c(B')=k' $
  be the central character associated with the block $upright(sans(B))'$. By
  Definition @def:brauer-correspondence, the map $(psi')^G$ is given by
  $ (psi')^G lr((a))=psi'(a_H b')=a_H b'+rad c(B'), quad "for" a in c(R G), $
  and is a central character if and only if this map is a homomorphism of
  $R$-algebras. Since the diagram @eq:brauer-endomorphism-square is commutative,
  this condition is clearly equivalent to the statement that the map
  $ lambda theta:E -> k' $
  is a homomorphism of $R$-algebras. This completes the proof.
]

Following Okuyama, we now obtain several module-theoretic interpretations of the
Brauer Correspondence. Among other things, these transfer questions about the
behavior of defect groups under the Brauer Correspondence to problems about
vertices of indecomposable lattices (see also Alperin–Burry @bib:Alperin1980).

#proposition[
  Let $H <= G$, and let $upright(sans(B))'$ be a $p$-block of $H$ for which a
  Brauer correspondent $(upright(sans(B))')^G$ is defined. Then
  $ B' divides B_(H times H), $
  where $B'$ and $B$ are the block ideals associated with $upright(sans(B))'$
  and $(upright(sans(B))')^G$, respectively.
] <prop:brauer-correspondent-block-summand>
#idx(
  "Brauer Correspondence",
  target: [@prop:brauer-correspondent-block-summand],
)

#proof[
  We have $R G=B plus.o I$ for some two-sided ideal $I$. Let
  $f in E="End"_(R(G times G)) R G$ be the projection on $B$. Then $f|_B="id"_B$
  and $f|_I=0$. By @prop:brauer-correspondence-endomorphism-criterion,
  $lambda theta$ is a homomorphism of $R$-algebras, so $lambda theta f=1$ in
  $k'$, since $f$ is an idempotent in $E$. Then $theta f=j f i$ is a unit in
  $E'$, because $E'$ is a local ring. Then the maps
  $ f i:B' -> B quad "and" quad j f:B -> B' $
  #source(474)
  are $R(H times H)$-homomorphisms, and
  $ (j f)(f i)=j f^2 i=j f i=theta f in E'. $
  Thus $(j f)(f i)$ is a unit in $E'$, so $B' divides B_(H times H)$, completing
  the proof.
]

#corollary[
  Keep the notation of @prop:brauer-correspondent-block-summand, and let $D'$ be
  a defect group of the block $upright(sans(B))'$. Then $D' <=_G D$, where $D$
  is a defect group of $(upright(sans(B))')^G$.
] <cor:brauer-correspondence-defect-subconjugacy>

#proof[
  The result follows at once from @prop:brauer-correspondent-block-summand and a
  basic property of vertices (Theorem @i:th:vertices-induction-restriction),
  using the interpretation of defect groups as vertices (see
  @prop:block-ideal-diagonal-vertex).
]

#theorem[
  Let $H <= G$, and let $upright(sans(B))'$ be a $p$-block of $H$ whose
  corresponding block ideal $B'$ occurs with multiplicity one in the
  decomposition of $(R G)_(H times H)$ into indecomposable
  $R(H times H)$-lattices. Then $(upright(sans(B))')^G$ is defined.
] <th:brauer-correspondence-multiplicity-one>
#idx(
  "Brauer Correspondence",
  target: [@th:brauer-correspondence-multiplicity-one],
)

#proof[
  Put $U=ker j$, so that $(R G)_(H times H)=i(B') plus.o U$, and identify
  $i(B')$ with $B'$. Then for any $R(H times H)$-endomorphisms $g:B' -> U$ and
  $h:U -> B'$, their composition $h g$ lies in $rad E'$. Otherwise, $h g$ is an
  automorphism of $B'$ since $E'$ is a local ring, and it follows that
  $B' divides U$ by @i:prop:split-short-exact-sequence, contradicting the
  assumption that $B'$ occurs with multiplicity one in $(R G)_(H times H)$.

  We shall prove that the criterion of
  @prop:brauer-correspondence-endomorphism-criterion is satisfied, namely that
  the map $lambda theta:E -> E' slash rad E'$ is a homomorphism of $R$-algebras.
  The map $lambda theta$ is $R$-linear, and we need only check that it is
  multiplicative. Let $f_1,f_2 in E$; then we can write
  $ f_i=f'_i+f''_i, quad i=1,2, $
  where $f'_i:R G -> B'$ and $f''_i:R G -> U$ are the
  $R(H times H)$-endomorphisms of $R G$ arising from the decomposition
  $(R G)_(H times H)=B' plus.o U$. Then
  $ theta f_i=j f_i i=j f'_i i+j f''_i i, quad "for" i=1,2, $
  and $j f''_i i in rad E'$ for $i=1,2$, since it is the composite of
  $R(H times H)$-maps from $B' -> U$ and $U -> B'$. By the same reasoning, we
  have
  $ theta(f_1 f_2) equiv j f'_1 f'_2 i (mod rad E') $
  and it follows that
  $ theta(f_1 f_2) equiv (theta f_1)(theta f_2) (mod rad E'). $
  Then $lambda theta$ preserves multiplication, since $lambda$ is the natural
  map from $E' -> E' slash rad E'$, and the result follows.
]

The preceding discussion yields some useful general conditions for the Brauer
correspondence to be defined.
#source(475)

#theorem[
  (Brauer @bib:Brauer1959). Let $D$ be a $p$-subgroup of $G$, and $H$ a subgroup
  such that $H >= D C_G lr((D))$. Let $upright(sans(B))'$ be a $p$-block of $H$
  with defect group $D'$. Then the block ideal $B'$ of $upright(sans(B))'$
  occurs with multiplicity one in $(R G)_(H times H)$, and therefore
  $(upright(sans(B))')^G$ is defined, provided that $D' >= D$.
] <th:brauer-correspondence-centralizer-containment>
#idx(
  "Brauer Correspondence",
  target: [@th:brauer-correspondence-centralizer-containment],
)

#proof[
  By @th:brauer-correspondence-multiplicity-one, it is sufficient to prove that
  $B'$ occurs with multiplicity one in $(R G)_(H times H)$. By
  @prop:block-ideal-diagonal-vertex, $Delta D' <= H times H$ is a vertex of the
  indecomposable $R(H times H)$-lattice $B'$. The multiplicity of $B'$ in
  $(R G)_(H times H)$ is the sum of the multiplicities of $B'$ in the submodules
  ${R(H y H):y in G}$, by
  @lem:block-ideal-double-coset-summand@case:block-ideal-double-coset-summand
  and the first step of the proof of @lem:block-ideal-double-coset-summand. If
  $B' divides R(H y H)$ for some $y in G$, then $R(H y H)$ is
  $(H times H,Y)$-projective, where
  $ Y=attach(Delta(H inter attach(H, tl: y^(-1))), tl: (y,1)) $
  by @lem:block-ideal-double-coset-summand, and hence
  $Delta D' <=_(H times H) Y$, since $Delta D'$ is a vertex of $B'$. An easy
  computation shows that if $Delta D' <=_(H times H) Y$, then
  $y in H C_G lr((D'))H$, and hence $y in H$, since $C_G lr((D')) <= H$ by
  hypothesis. It follows that $B' divides R H$ and $B' divides.not R(H y H)$ if
  $y in.not H$, completing the proof that $B'$ occurs with multiplicity one in
  $(R G)_(H times H)$.
]

The next result extends part of Theorem @th:brauer-correspondence-brauer-map to
block theory with respect to an arbitrary $p$-modular system which is admissible
for $G$, and gives a straightforward module-theoretic description of the Brauer
Correspondence.

#theorem[
  (Alperin @bib:Alperin1977). Let $D$ be a $p$-subgroup of $G$, and $H$ a
  subgroup satisfying the condition
  $ D C_G lr((D)) <= H <= N_G lr((D)). $
  Then the following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[The Brauer correspondence
      $upright(sans(B))' mapsto (upright(sans(B))')^G$ is defined for all
      $p$-blocks $upright(sans(B))'$ of
      $H$.] <case:brauer-correspondence-normalizer-defined>],
    [#case[Let $B'$ be a block ideal in $R H$, and $B$ a block ideal in $R G$,
      associated with the blocks $upright(sans(B))'$ of $H$ and
      $upright(sans(B))$ of $G$, respectively. Then we have
      $
        (upright(sans(B))')^G=upright(sans(B)) <==> B' divides B_(H times H).
      $] <case:brauer-correspondence-restriction-summand>],
  )
] <th:brauer-correspondence-block-summand-criterion>
#idx(
  "Alperin's Theorem",
  target: [@th:brauer-correspondence-block-summand-criterion],
)

#proof[
  @case:brauer-correspondence-normalizer-defined Let $upright(sans(B))'$ be an
  arbitrary block of $H$, with defect group $D' <= H$. Then $D' >= D$ by
  @prop:normal-p-subgroup-block-idempotents, since $D ⊴ H$. It follows that
  $C_G lr((D')) <= C_G lr((D)) <= H$, using the hypothesis of the Theorem. Then
  $D' C_G lr((D')) <= H$, and we can apply Brauer’s Theorem
  @th:brauer-correspondence-centralizer-containment to conclude that
  $(upright(sans(B))')^G$ is defined.

  @case:brauer-correspondence-restriction-summand First assume that
  $B' divides B_(H times H)$. Then $(upright(sans(B))')^G$ is defined by
  part~@case:brauer-correspondence-normalizer-defined, and $B'$ occurs with
  multiplicity one in $(R G)_(H times H)$. It follows that
  $upright(sans(B))=(upright(sans(B))')^G$, by
  @prop:brauer-correspondent-block-summand. Conversely,
  $B' divides B_(H times H)$ if $upright(sans(B))=(upright(sans(B))')^G$ by
  @prop:brauer-correspondent-block-summand, completing the proof.
]

The next theorem gives an interpretation of the Brauer Correspondence in terms
of vertices of indecomposable lattices (see also the Nagao Decomposition Theorem
@th:nagao-block-decomposition and its consequences, in case $H <= N_G lr((D))$).
#source(476)

#theorem[
  (Alperin). Let $D$ be a $p$-subgroup of $G$, let $H <= G$, and assume that
  $D C_G lr((D)) <= H$. Let $N in "ind" R H$, $M in "ind" R G$, and assume
  further that $N divides M_H$ and $D in "vtx" N$. Let $M$ belong to the
  $p$-block $upright(sans(B))$ of $G$. Then $N$ belongs to a $p$-block
  $upright(sans(B))'$ of $H$ such that $(upright(sans(B))')^G=upright(sans(B))$.
] <th:brauer-correspondence-restriction-vertices>
#idx(
  "Alperin's Theorem",
  target: [@th:brauer-correspondence-restriction-vertices],
)

#proof[
  (See Alperin–Burry @bib:Alperin1980). _Step 1._ We have
  $ R G=R H plus.o (plus.o.big_(y in.not H) R(H y H)). $
  Our first assertion is that if $U divides R(H y H)$, for
  $U in "ind" R(H times H)$ and $y in.not H$, then
  $Delta D lt.eq.not_(H times H) "vtx" U$. We begin with the fact that for each
  $y in G$,
  $ H y H tilde.equiv "ind"_Y^(H times H) $
  where
  $
    Y="Stab"_(H times H)y=
    attach(Delta(H inter attach(H, tl: y^(-1))), tl: (y,1))
  $
  (from §~@ss:block-defect-groups-sylow-intersections). Then
  $Delta D <=_(H times H) "vtx" U$ and $U divides R(H y H)$ imply that
  $Delta D <=_(H times H) Y$. An easy computation then shows that $y in H$ since
  $C_G lr((D)) <= H$, completing the proof of Step 1.

  _Step 2._ Let $e$ be the sum of the block idempotents in $R H$ from blocks
  corresponding to $upright(sans(B))$ (in the Brauer Correspondence) so $e=0$ if
  there are none. In any case,
  $ B=e B plus.o (1-e)B quad "as" R(H times H) "-modules", $
  where $B$ is the block ideal in $R G$ associated with the given block
  $upright(sans(B))$. Since
  $ R G=R H+sum_(y in.not H) R(H y H), $
  we have
  $ (1-e)B divides (1-e)R H plus.o (1-e)sum_(y in.not H) R(H y H). $
  Consider a block ideal $B'$ of $R H$ whose vertex contains an
  $(H times H)$-conjugate of $Delta D$. By @prop:block-ideal-diagonal-vertex,
  its defect group $D'$ can be chosen to contain $D$. Then
  $C_G lr((D')) <= C_G lr((D)) <= H$, so
  @th:brauer-correspondence-centralizer-containment shows that $B'$ occurs with
  multiplicity one in $(R G)_(H times H)$ and has a defined Brauer
  correspondent. Its unique copy lies in the correspondent block by
  @prop:brauer-correspondent-block-summand. Hence, if $B'$ occurs in
  $B_(H times H)$, its block idempotent is a summand of $e$.#ed-note[
    @prop:brauer-correspondent-block-summand supplies a summand from a defined
    correspondent; its converse is not asserted there. Only block ideals with
    vertices containing a conjugate of $Delta D$ are needed here.
  ] It follows that $(1-e)R H$ contributes no such summand to $(1-e)B$. Together
  with Step 1, this proves that $(1-e)B$ has no indecomposable
  $R(H times H)$-summand whose vertex contains $Delta D$.

  _Step 3._ Suppose the theorem is false. Then $(1-e)_N="id"_N$, where $N$ is
  the $R H$-lattice in the statement of the theorem. We next construct the
  $R H$-lattice $(1-e)B times.o_R N$, on which $H$ acts according to the rule
  $ h((1-e)a times.o n)=(1-e)h a h^(-1) times.o h n. $
  #source(477)
  We shall now prove, under the assumption of Step 3, that
  $N divides (1-e)B times.o_R N$ as $R H$-lattices. Since $N divides M_H$ by
  hypothesis, there exists an injection $i:N -> M_H$ and a projection
  $j:M_H -> N$. Define a homomorphism of $R H$-modules
  $ phi:N -> (1-e)B times.o_R N $
  by setting
  $ phi(n)=(1-e)b times.o n, $
  where $b$ is the block idempotent in $B$. Then define another homomorphism of
  $R H$-modules
  $ psi:(1-e)B times.o_R N -> N, $
  where
  $ psi((1-e)a times.o n)=j((1-e)a dot i(n)), quad "for" a in B. $
  To check that $psi$ is an $R H$-map, we have
  $
    psi(h((1-e)a times.o n)) & =psi((1-e)h a h^(-1) times.o h n)
                               =j((1-e)h a h^(-1) dot i(h n)) \
                             & =j((1-e)h a i(n))=h(j((1-e)a i(n)))
  $
  as required. Using the assumption that $(1-e)_N="id"_N$, we obtain
  $
    psi phi(n) & =psi((1-e)b times.o n)=j((1-e)b i(n)) \
               & =j((1-e)i(n))=j i((1-e)n)=j i n=n,
  $
  proving the assertion of Step 3.

  _Step 4._ The two $H$-actions on $B$, given by
  $
    h dot a=h a h^(-1) quad "and" quad h dot a=Delta(h) dot a,
    quad a in B, quad h in H,
  $
  clearly coincide. It follows that $(1-e)B$ contains no indecomposable
  $R H$-summands whose vertices contain $D$, by Step 2. Thus $(1-e)B$ is a
  direct sum of $(H,D_i)$-projective lattices, for subgroups ${D_i}$ such that
  $D lt.eq.not_H D_i$ for each $i$. It follows that the $R H$-lattice
  $(1-e)B times.o_R N$ has the same property (see Exercise
  @exc:inner-tensor-relative-projective). In particular, no indecomposable
  $R H$-summand of $(1-e)B times.o_R N$ has vertex $D$, contradicting Step 3,
  where it was shown that $N divides (1-e)B times.o_R N$. Thus we have proved
  that $e N=N$, and hence $N$ belongs to a block $upright(sans(B))'$ of $H$ such
  that $(upright(sans(B))')^G=upright(sans(B))$, as required.
]

#exercises-heading

In Exercise @exc:normal-defect-idempotent-class-support, $R$ denotes either a
field of characteristic $p$, or a complete d.v.r. whose residue field has
characteristic $p$.
#source(478)

#exercise[
  Let $D ⊴ G$, and let $b$ be a block idempotent in $R G$ with defect group $D$.
  Prove that
  $ b equiv sum beta_j L_j (mod frak(p) A_G), quad beta_j in R, $
  where the $L_j$ are $G$-class sums whose class defect groups satisfy $D_j=D$
  for each $j$.
] <exc:normal-defect-idempotent-class-support>

#hint([@exc:normal-defect-idempotent-class-support])[
  See the proof of @prop:normal-p-subgroup-block-idempotents.
]

#exercise[
  Let $k$ be a field, and let $phi:A -> A'$ be a surjection of f.d. commutative
  $k$-algebras. Prove that $phi$ defines a bijection from the set of all
  primitive idempotents of $A$ not contained in the kernel of $phi$ to the set
  of all primitive idempotents of $A'$.
] <exc:commutative-algebra-primitive-idempotent-surjection>

#hint([@exc:commutative-algebra-primitive-idempotent-surjection])[
  An idempotent $e in A$ is primitive if and only if $e A(=e A e)$ is a local
  $k$-algebra. Then show, using the assumption that $phi$ is surjective, that if
  $e$ is primitive in $A$, then either $phi(e)=0$ or $phi(e)$ is primitive in
  $A'$. To check that $phi$ defines a bijection, see
  @prop:commutative-order-primitive-idempotents.
]

In Exercises #(
  [@exc:brauer-correspondence-transitivity]
    + [–]
    + [@exc:brauer-first-main-block-defect-order]
), $(K,R,k)$ denotes a $p$-modular system satisfying the conditions stated in
the Exercises of §~@sec:introduction-block-theory.

#exercise[
  Prove the transitivity of the Brauer Correspondence. More precisely, let
  $H'' <= H' <= G$, and let $upright(sans(B))''$ be a $p$-block of $H''$ such
  that $(upright(sans(B))'')^(H')$ and $((upright(sans(B))'')^(H'))^G$ are
  defined. Prove that $(upright(sans(B))'')^G$ is defined, and coincides with
  the block $((upright(sans(B))'')^(H'))^G$. (See @def:brauer-correspondence.)
] <exc:brauer-correspondence-transitivity>
#idx(
  "Brauer Correspondence",
  "transitivity of",
  target: [@exc:brauer-correspondence-transitivity],
)

#exercise[
  Let $D$ be a $p$-subgroup of $G$, and let $H=N_G lr((D))$. Prove that the
  Brauer correspondence is defined for each $p$-block of $H$ with defect group
  $D$, and coincides with the bijection of $p$-blocks with defect group $D$
  described by the First Main Theorem @th:brauer-first-main-theorem.
] <exc:brauer-first-main-correspondence-compatibility>

#hint([@exc:brauer-first-main-correspondence-compatibility])[
  Use @eq:brauer-first-main-idempotent-correspondence and
  @cor:brauer-map-block-idempotent-fibres.
]

#exercise[
  Prove that the First Main Theorem @th:brauer-first-main-theorem establishes a
  bijection from the set of $p$-blocks of $G$ with defect group $D$ to the set
  of all $p$-blocks of $H=N_G lr((D))$ of defect $d$, where $abs(D)=p^d$.
] <exc:brauer-first-main-block-defect-order>

#exercise[
  Let $H <= G$, and let $R$ be a commutative ring. Let $N$ be an arbitrary
  $R G$-lattice, and let $M$ be a $(G,H)$-projective $R G$-lattice. Prove that
  the inner tensor product $M times.o_R N$ is $(G,H)$-projective.
] <exc:inner-tensor-relative-projective>

#hint([@exc:inner-tensor-relative-projective])[
  Apply @i:th:gaschutz-relative-projectivity(iii) to the endomorphism
  $gamma times.o 1$ of $M times.o N$, where $gamma in "End"_(R H) lr((M))$ and
  satisfies @i:th:gaschutz-relative-projectivity(iii).
]
