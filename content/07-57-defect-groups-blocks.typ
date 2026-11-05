#import "main-defs.typ": *
#import "statements.typ": *

== The Defect Group of a $p$-Block <sec:defect-groups-blocks>

=== $G$-Algebras, the Trace Map, and Defect Groups
<ss:block-g-algebras-trace>

Throughout this section, $G$ denotes a finite group, $p$ a fixed prime number,
and $R$ a commutative ring satisfying either of the following hypotheses:

#case-list(
  numbering: "(a)",
  [#case[$R$ is a field of characteristic $p$; or]
    <case:block-theory-coefficient-field>],
  [#case[$R$ is a d.v.r. with quotient field $K$ and maximal ideal $frak(p)$
      containing $p$, such that $R$ is complete in the $frak(p)$-adic topology.]
    <case:block-theory-complete-coefficient-ring>],
)

We recall the notations, defined for subsets $X,Y$ of $G$:
$
  attach(X, tl: a) = a X a^(-1) = X^(a^(-1))
  quad "for" X subset.eq G, quad a in G,\
  X =_H Y quad "if" X = attach(Y, tl: a) "for" a in H <= G;
$
and
$ X <=_H Y quad "if" X subset.eq attach(Y, tl: a) "for" a in H <= G. $
We shall call a family of representatives of the left cosets
$G slash H = {x H: x in G}$ a _cross section of $G slash H$_, and a set of
representatives of the double cosets ${H x L: x in G}$ a _cross section of
$H backslash G slash L$_, for $H,L <= G$.

#definition[
  A _$G$-algebra_ $A$ is an $R$-algebra with a finite $R$-basis, upon which $G$
  acts as a group of $R$-algebra automorphisms. Thus for each $x in G$,
  $a in A$, there is defined an element $x a in A$ (or $x dot a in A$) such that
  the map $a in A arrow.r.bar x a in A$ is an automorphism of $A$ as $R$-module,
  and we have
  $ x(y a) = (x y)a quad "and" quad x(a b) = (x a)(x b) $
  for all $x,y in G$ and $a,b in A$. For an arbitrary subgroup $H <= G$, $A_H$
  denotes the $R$-subalgebra of $A$ consisting of fixed elements under the
  $H$-action; thus
  $ A_H = {a in A: h a = a "for all" h in H}. $
] <def:finite-free-g-algebra>
#idx("G-algebra", target: [@def:finite-free-g-algebra])

#source(446)
Note that
$ D <= H => A_H subset.eq A_D $
for all subgroups $D$ and $H$ of $G$.

#definition[
  Let $A$ be a $G$-algebra, and let $H,D$ be subgroups of $G$ such that
  $D <= H$. The _trace map_ (defined by the pair of subgroups $D$ and $H$) is
  the $R$-endomorphism of $A$
  $ T_(H slash D): A arrow A $
  defined by
  $ T_(H slash D) lr((a)) = sum_(h in H slash D) h a, quad a in A, $
  where the notation $h in H slash D$ means that the sum is taken over a cross
  section of the left cosets $H slash D$. We shall use the notation
  $A_(H slash D)$ for the image of $A_D$ under the trace map $T_(H slash D)$;
  thus
  $ A_(H slash D) = T_(H slash D) lr((A_D)). $
] <def:g-algebra-relative-trace>
#idx("Trace map", target: [@def:g-algebra-relative-trace])
#nidx("$T_(H slash D)$", "trace map", target: [@def:g-algebra-relative-trace])
#nidx(
  "$A_(H slash D)$",
  "image of trace map in the G-algebra A",
  target: [@def:g-algebra-relative-trace],
)

The following properties of the trace map follow immediately from the
definitions, and are left as exercises for the reader.

#proposition[
  For $D <= H <= L <= G$, the following statements hold:
  #case-list(
    numbering: "(i)",
    [#case[$T_(H slash D) A_D subset.eq A_H$, and for $a in A_D$,
      $T_(H slash D) a$ is independent of the choice of the cross section of
      $H slash D$;] <case:relative-trace-cross-section>],
    [#case[$T_(L slash H) compose T_(H slash D) = T_(L slash D)$ on $A_D$
      (transitivity);] <case:relative-trace-transitivity>],
    [#case[For all $a in A_D$ and $b in A_H$ we have
        $
          T_(H slash D) lr((b a)) = b(T_(H slash D) a), quad "and"
          T_(H slash D) lr((a b)) = (T_(H slash D) lr((a)))b.
        $]
      <case:relative-trace-bimodule-linearity>],
    [#case[$A_(H slash D) = T_(H slash D) lr((A_D))$ is a two-sided ideal in
      $A_H$;] <case:relative-trace-image-ideal>],
    [#case[For all $x in G$ and $a in A_D$,
        $
          x dot A_H = A_(attach(H, tl: x)), quad "and"
          x dot T_(H slash D) lr((a)) =
          T_(attach(H, tl: x) slash attach(D, tl: x)) lr((x a)).
        $]
      <case:relative-trace-conjugation>],
  )
] <prop:g-algebra-relative-trace-properties>

#remarks[
  The preceding ideas will be applied to assign subgroups of $G$ to primitive
  idempotents in $G$-algebras. The following examples of $G$-algebras are
  particularly important.
  #enum(
    numbering: "(i)",
    [$E = op("End")_R M$, for a left $R G$-lattice $M$, with the $G$-action
      given by
      $ x dot f = x f x^(-1) quad "for" x in G, f in E; $],
    [#source(447)$A = R G$, with $x dot a = x a x^(-1)$, for $x in G$,
      $a in A$.],
  )

  In the first example, we have $E_G = op("End")_(R G) M$, and the trace map
  $T_(G slash H)$ carries $op("End")_(R H) lr((M_H))$ to $op("End")_(R G) M$. If
  $M$ is an indecomposable $R G$-lattice, then $1$ is the unique idempotent in
  $E_G$; in §~@i:sec:vertices-sources, the trace map was used to assign a
  conjugacy class of $p$-subgroups of $G$ to $M$ (the vertices of $M$). In the
  second example, we have $A_G = c(R G)$, and the primitive idempotents in $A_G$
  are the block idempotents of $R G$ discussed in the preceding section. In this
  situation, following Green @bib:Green1963, we shall assign a conjugacy class
  of $p$-subgroups to a given block idempotent in $A_G$, called the _defect
  groups_ of the block. We recover, in this way, previous definitions of defect
  groups of block idempotents, due to Brauer @bib:Brauer1956 and Osima
  @bib:Osima1955 (see @bib:CurtisReiner1962[CR] §87). The point of the present
  approach is that it gives useful connections between the theory of vertices
  and sources, from §~@i:sec:vertices-sources, and defect groups of $p$-blocks.
] <rem:g-algebra-endomorphism-and-conjugation-examples>

Returning to the general situation, we begin with the analogues of the Mackey
theorems (see §~@i:ss:mackey-theorems) for trace maps.

#proposition[
  Let $A$ be a $G$-algebra, $L$ a subgroup of $G$, and $D,H$ subgroups of $L$.
  Then
  #case-list(
    numbering: "(i)",
    [#case[$T_(L slash H) a = sum T_(D slash (D inter attach(H, tl: x)))
        lr((x a))$, for all $a in A_H$, where the sum is taken over a cross
        section ${x}$ of the $(D,H)$-double cosets in $L$. Moreover, we have]
      <case:relative-trace-mackey-decomposition>],
    [#case[$T_(L slash H) lr((a)) T_(L slash D) lr((b)) =
        sum T_(L slash (D inter attach(H, tl: x))) lr(((x dot a)b))$, for all
        $a in A_H$, $b in A_D$, where the sum is taken over the same cross
        section of $D backslash L slash H$ as in
        part~@case:relative-trace-mackey-decomposition.]
      <case:relative-trace-mackey-product>],
  )
] <prop:relative-trace-mackey-formulas>

#proof[
  @case:relative-trace-mackey-decomposition Let $L = union.dot D x H$, and
  consider a fixed double coset $D x H$. By the proof of Mackey's Subgroup
  Theorem @i:th:mackey-subgroup, we have
  $
    D = union.dot.big_j s_j lr((D inter attach(H, tl: x))) quad "and"
    D x H = union.dot.big_j s_j x H,
  $
  for a cross section ${s_j}$ of $D slash (D inter attach(H, tl: x))$. By
  @prop:g-algebra-relative-trace-properties@case:relative-trace-conjugation, we
  have $x a in A_(attach(H, tl: x)) subset.eq
  A_(D inter attach(H, tl: x))$ for all $a in A_H$, and hence
  $
    T_(D slash (D inter attach(H, tl: x))) lr((x dot a)) =
    sum_j s_j lr((x a)) = sum_j (s_j x)a.
  $ <eq:relative-trace-double-coset-sum>
  By the preceding remarks, the elements ${s_j x}$, taken over representatives
  of the different $(D,H)$-double cosets in $L$, form a cross section of left
  cosets $L slash H$. Upon adding the expressions
  @eq:relative-trace-double-coset-sum over the given cross section of
  $D backslash L slash H$, we obtain @case:relative-trace-mackey-decomposition.

  @case:relative-trace-mackey-product Let $a in A_H$, $b in A_D$. Then
  #source(448)
  $
    T_(L slash H) lr((a)) T_(L slash D) lr((b))
    &= T_(L slash D) lr((T_(L slash H) lr((a)) b))
    quad ("by" #[@prop:g-algebra-relative-trace-properties]
      #[@case:relative-trace-bimodule-linearity]) \
    &= T_(L slash D) lr(
      (sum_(D x H)
        (T_(D slash (D inter attach(H, tl: x))) lr((x a)))b)
    )
    quad ("by part" #[@case:relative-trace-mackey-decomposition]) \
    &= T_(L slash D) lr(
      (sum_(D x H)
        T_(D slash (D inter attach(H, tl: x))) lr(((x dot a)b)))
    )
    quad ("by" #[@prop:g-algebra-relative-trace-properties]
      #[@case:relative-trace-bimodule-linearity]) \
    &= sum_(D x H) T_(L slash (D inter attach(H, tl: x))) lr(((x dot a)b))
    quad ("by" #[@prop:g-algebra-relative-trace-properties]
      #[@case:relative-trace-transitivity]),
  $
  completing the proof.
]

#corollary[
  Let $L,D$, and $H$ be as in @prop:relative-trace-mackey-formulas. Then
  $
    A_(L slash H) A_(L slash D) subset.eq
    sum_x A_(L slash (D inter attach(H, tl: x))),
  $
  where the sum is taken over a cross section of the $(D,H)$ double cosets in
  $L$.
] <cor:relative-trace-ideal-mackey-product>

#lemma(name: "Rosenberg's Lemma")[
  Let $A$ be an $R$-algebra with a finite basis, over a commutative ring $R$
  satisfying either of the conditions @case:block-theory-coefficient-field or
  @case:block-theory-complete-coefficient-ring stated at the beginning of
  §~@ss:block-g-algebras-trace. Let $e$ be a primitive idempotent in $A$, and
  suppose that
  $ e in I + I', $
  for two-sided ideals $I$ and $I'$ in $A$. Then either $e in I$ or $e in I'$.
] <lem:rosenberg-primitive-idempotent-ideal-sum>
#idx(
  "Rosenberg's Lemma",
  target: [@lem:rosenberg-primitive-idempotent-ideal-sum],
)

#proof[
  Since $e$ is a primitive idempotent, $A e$ is an indecomposable left ideal,
  and we have $(op("End")_A A e)^"op" tilde.equiv e A e$ by
  @i:lem:idempotent-corner-endomorphisms. Then $e A e$ is a local ring with
  identity element $e$, by @i:prop:indecomposable-local-endomorphism-ring, which
  applies because of the hypotheses on $R$. Moreover,
  $ e in e I e + e I' e, $
  and $e I e$ and $e I' e$ are two-sided ideals of $e A e$. If both $e I e$ and
  $e I' e$ are properly contained in $e A e$, then both are contained in
  $op("rad") e A e$, and hence $e in op("rad") e A e$, which is impossible. Thus
  we may assume $e I e = e A e$; and obtain $e in e A e = e I e
  subset.eq I$, as required. (See Rosenberg @bib:Rosenberg1961).
]

The first main result of this subsection is the following theorem.

#theorem[
  (Green @bib:Green1963). Let $A$ be a $G$-algebra, $H$ a subgroup of $G$, and
  let $e$ be a primitive idempotent in $A_H$. There exists a $p$-subgroup
  $D <= H$ such that
  #case-list(
    numbering: "(i)",
    [#case[$e in A_(H slash D)$, and having the further property that]
      <case:primitive-idempotent-trace-membership>],
    [#case[$D <=_H D'$ for any other subgroup $D' <= H$ such that
        $e in A_(H slash D')$.]
      <case:primitive-idempotent-minimal-trace-subgroup>],
  )
] <th:primitive-idempotent-defect-group-existence>

#proof[
  #source(449)
  Since $A_H = A_(H slash H)$ and $e in A_H$, the family of subgroups ${D}$ such
  that $D <= H$ and $e in A_(H slash D)$ is nonempty, and contains a minimal
  subgroup $D_0$. Let $D'$ be another subgroup of $H$ such that
  $e in A_(H slash D')$. Then $e = e^2 in
  A_(H slash D') dot A_(H slash D_0)$, and we obtain
  $
    e in sum_(D_0 x D' subset.eq H)
    A_(H slash (D_0 inter attach(D', tl: x)))
  $
  by @cor:relative-trace-ideal-mackey-product. For each $x in H$,
  $A_(H slash (D_0 inter attach(D', tl: x)))$ is a two-sided ideal in $A_H$, by
  @prop:g-algebra-relative-trace-properties@case:relative-trace-image-ideal, and
  $e$ is contained in their sum. By Rosenberg's Lemma
  @lem:rosenberg-primitive-idempotent-ideal-sum, we have
  $e in A_(H slash (D_0 inter attach(D', tl: x)))$ for some $x in H$. By the
  minimality of $D_0$, it follows that $D_0 <=_H D'$.

  Now let $S$ be a Sylow $p$-subgroup of $H$; then the index $m = |H:S|$ is
  prime to $p$, and hence is a unit in $R$. Moreover, $A_H subset.eq A_S$, and,
  for all $a in A_H$, we have
  $
    T_(H slash S) a = m a, quad "and"
    T_(H slash S) lr((m^(-1) a)) = a,
  $
  since $m$ is a unit in $R$. In particular,
  $ e in T_(H slash S) lr((A_S)) = A_(H slash S), $
  so $D_0 <=_H S$, by the first part of the proof. Thus $D_0$ is a $p$-subgroup
  of $H$, and the proof is completed.
]

Note that
$
  e in A_(H slash D) => e in A_(H slash attach(D, tl: x))
  quad "for all" x in H,
$
by @prop:g-algebra-relative-trace-properties@case:relative-trace-conjugation,
since $x e = e$.

#definition[
  Let $H <= G$, and let $e$ be a primitive idempotent in $A_H$. By Theorem
  @th:primitive-idempotent-defect-group-existence, there exists a $p$-subgroup
  $D <= H$, which is the unique minimal subgroup up to $H$-conjugacy, such that
  $ e in A_(H slash D) = T_(H slash D) lr((A_D)). $
  The group $D$ and its $H$-conjugates are called _defect groups of the
  primitive idempotent $e$_.
] <def:primitive-idempotent-defect-group>
#idx(
  "Defect groups of idempotents",
  target: [@def:primitive-idempotent-defect-group],
)

For the rest of the subsection, let $A$ be the $G$-algebra $R G$, with
$G$-action given by conjugation (see
@rem:g-algebra-endomorphism-and-conjugation-examples). We shall examine the
connection between the coefficients of a primitive idempotent $e in A_G$, as a
linear combination of class sums, and the defect groups of $e$. Among other
things, this will show that the different definitions of defect groups (by
Brauer and Osima (see @bib:CurtisReiner1962[CR] §87), and Green
@def:primitive-idempotent-defect-group) coincide.

#definition[
  Let $H <= G$. An _$H$-conjugacy class_ $frak(L) subset.eq G$ is an orbit of
  the #source(450)$H$-action on $G$ by conjugation:
  $ h dot x = h x h^(-1), quad h in H, quad x in G. $
  The _$H$-class sums_ in $R G$ are the elements
  $ L = sum_(x in frak(L)) x, $
  where ${frak(L)}$ are the $H$-conjugacy classes in $G$. A _class defect group_
  of an $H$-conjugacy class $frak(L)$ is a Sylow $p$-subgroup $D$ of the
  centralizer $C_H lr((x))$, for some $x in frak(L)$.
] <def:conjugacy-class-defect-group>
#idx("Class defect group", target: [@def:conjugacy-class-defect-group])
#idx(
  "Defect groups of idempotents",
  "of classes",
  target: [@def:conjugacy-class-defect-group],
)

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [The class defect groups of an $H$-conjugacy class $frak(L)$ form a single
      conjugacy class of $p$-subgroups of $H$, by the Sylow theorem. Moreover,
      if $D$ is a class defect group of an $H$-conjugacy class $frak(L)$, then
      we have
      $
        D' <=_H D <=> D' "is a" p "-subgroup of" C_H lr((x))
        "for some" x in frak(L)
      $ <eq:class-defect-group-subconjugacy>],
    [In case $H = G$, the $H$-conjugacy classes are the usual conjugacy classes
      in $G$. If $D$ is a class defect group of a conjugacy class $frak(C)$ in
      $G$, then clearly
      $
        |D| = p^delta, quad "where" delta "is the defect of" frak(C),
        "defined in" #[@def:conjugacy-class-defect].
      $ <eq:class-defect-group-order>],
  )
] <rem:class-defect-group-conjugacy-and-order>

#proposition[
  Let $A$ be the $G$-algebra $R G$. For each subgroup $H <= G$, $A_H$ has an
  $R$-basis consisting of the $H$-class sums ${L}$, defined in
  @def:conjugacy-class-defect-group. If $D <= H <= G$, then#footnote[
    We follow the convention that $frak(p) = 0$ in case $R$ is a field of
    characteristic $p$.
  ]
  $ A_(H slash D) equiv sum_(D_i <=_H D) R L_i (mod frak(p) A_H) $
  where the sum is taken over all $H$-class sums ${L_i}$ whose class defect
  groups ${D_i}$ satisfy the condition that $D_i <=_H D$.
] <prop:trace-image-class-defect-support>

#proof[
  The first statement is similar to @i:lem:class-sums-center, and its proof is
  left to the reader. For the second statement, we note that $A_D$ has a basis
  consisting of $D$-class sums ${X}$, and
  $A_(H slash D) = T_(H slash D) lr((A_D))$. A $D$-class sum can be expressed in
  the form
  $ X = sum_(d in D slash C_D lr((x))) d dot x, $
  where $x$ is a representative of the corresponding $D$-class. Then
  $
    T_(H slash D) X & = sum_(h in H slash D) h dot X
                      = sum_(h in H slash C_D lr((x))) h dot x \
                    & = |C_H lr((x)):C_D lr((x))|
                      sum_(h in H slash C_H lr((x))) h dot x
                      = |C_H lr((x)):C_D lr((x))| L
  $ <eq:relative-trace-class-sum-centralizer-index>
  #source(451)
  where $L$ is the $H$-class sum associated with the $H$-class $frak(L)$
  containing $x$. For a given element $x$, put $m = |C_H lr((x)):C_D lr((x))|$.
  Then $T_(H slash D) X in frak(p) A_H$ if $p divides m$, by
  @eq:relative-trace-class-sum-centralizer-index. If $p divides.not m$, then $m$
  is a unit in $R$, and we have
  $ L = T_(H slash D) lr((m^(-1) X)) in A_(H slash D) $
  by @eq:relative-trace-class-sum-centralizer-index. Recalling that
  $m = |C_H lr((x)):C_D lr((x))|$, we have
  $
    p divides.not m <=> C_D lr((x)) "contains a Sylow" p "-subgroup of"
    C_H lr((x)) \
    <=> D "contains a class defect group of the" H "-class" frak(L) in.rev x.
  $
  The elements ${T_(H slash D) lr((X))}$ in
  @eq:relative-trace-class-sum-centralizer-index span the $R$-module
  $A_(H slash D)$, so the second statement of the proposition follows from the
  preceding discussion.
]

Now let $(K,R,k)$ be a $p$-modular system which is admissible for $G$ (see
@def:admissible-modular-system). The results proved earlier in
§~@ss:block-g-algebras-trace apply to both $G$-algebras
$ A = R G quad "and" quad overline(A) = overline(R) G = k G. $
This is clear in case $R$ is complete. If $R$ is not complete, the other
hypotheses of @def:admissible-modular-system imply that $e A e$ is a local ring
for any primitive idempotent $e$, so that Rosenberg's Lemma
@lem:rosenberg-primitive-idempotent-ideal-sum holds in this case, along with the
rest of the theory of defect groups. As an immediate consequence of
@prop:trace-image-class-defect-support, we then have:

#corollary[
  Keep the notation of the preceding paragraph, and let $D <= G$.#ed-note[
    For arbitrary $a$, the original omits $frak(p) A$ from the inverse image.
    With $R = ZZ_2 lr([i])$, $G = C_4$, and $D = 1$, the trace image is $4 R G$:
    $2 dot 1$ reduces to zero but does not belong to $4 R G$.
  ] Then for $a in A$,
  $
    overline(a) in overline(A)_(G slash D)
    <=> a in A_(G slash D) + frak(p) A.
  $
  For every central idempotent $b in A_G$, moreover,
  $ b in A_(G slash D) <=> overline(b) in overline(A)_(G slash D). $
] <cor:trace-image-modular-reduction>

#proof[
  Put $C = c(R G)$ and $I = A_(G slash D)$. The class-sum bases show that
  $A_D arrow overline(A)_D$ is surjective and that
  $C inter frak(p) A = frak(p) C$. Reduction commutes with the trace map, so the
  first equivalence follows.

  More generally, let $J$ be a finite sum of trace ideals $A_(G slash E)$. Each
  is an ideal of $C$ by
  @prop:g-algebra-relative-trace-properties@case:relative-trace-image-ideal. If
  $b in C$ is an idempotent and $b in J + frak(p) A$, the intersection equality
  gives $b in J + frak(p) C$. Multiplication by $b$ yields
  $ C b = J b + frak(p) C b. $
  The finite $R$-module $C b slash J b$ equals its product with $frak(p)$; hence
  Nakayama's Lemma gives $C b = J b$ and $b in J$. Taking $J = I$ proves the
  reverse implication for central idempotents, and the forward implication
  follows by reduction.
]

We now obtain:

#theorem[
  Let $(K,R,k)$ be a $p$-modular system which is admissible for $G$. Let
  $A = R G$, $overline(A) = k G$, $A_G = c(R G)$, $overline(A)_G = c(k G)$. Let
  $D$ be a fixed $p$-subgroup of $G$. Then the following statements hold:
  #case-list(
    numbering: "(i)",
    [#case[$D$ is a defect group of a block idempotent $b in A_G$ if and only if
        $D$ is a defect group of the block idempotent
        $overline(b) in overline(A)_G$.]
      <case:block-defect-group-modular-reduction>],
    [#case[$D$ is a defect group of $b$ if and only if
        $
          b equiv sum_(D_i =_G D) a_i C_i + sum_(D_j <_G D) a_j C_j
          (mod frak(p))
        $
        where (in the first sum) at least one coefficient
        $a_i equiv.not 0 (mod frak(p))$. Here each $C_i$ is a class sum, and
        $D_i$ is a class defect group of the class associated with $C_i$.]
      <case:block-defect-class-sum-coefficients>],
    [#case[#source(452)$D$ is a defect group of $overline(b)$ if and only if
        $
          overline(b) = sum_(D_i =_G D) alpha_i C_i
          + sum_(D_j <_G D) alpha_j C_j
        $
        with at least one coefficient (in the first sum) $alpha_i != 0$ in $k$,
        and the rest of the notation is as in
        part~@case:block-defect-class-sum-coefficients.]
      <case:modular-block-defect-class-sum-coefficients>],
    [#case[If $D$ is a defect group of $b$, then $D$ is a class defect group of
        some conjugacy class in $G$.]
      <case:block-defect-realized-by-class>],
  )
] <th:block-defect-class-sum-characterization>

#proof[
  @case:block-defect-group-modular-reduction By
  @prop:commutative-order-primitive-idempotents, the map $b arrow.r.bar
  overline(b)$ is a bijection of block idempotents in $A$ and $overline(A)$,
  respectively. For every subgroup $E <= G$, the central-idempotent assertion of
  Corollary @cor:trace-image-modular-reduction gives
  $ b in A_(G slash E) <=> overline(b) in overline(A)_(G slash E). $
  Thus the families of trace subgroups coincide, and so do their minimal
  conjugacy classes, by Definition @def:primitive-idempotent-defect-group.

  @case:block-defect-class-sum-coefficients Let $D$ be a defect group of $b$.
  Then $b$ has the required expression as a linear combination of class sums, by
  @prop:trace-image-class-defect-support and
  @def:primitive-idempotent-defect-group, except that possibly all the
  coefficients in the first sum are in $frak(p)$. But if this occurs, put
  $J = sum_(D_j <_G D) A_(G slash D_j)$. Then $b in J + frak(p) A_G$ by
  @prop:trace-image-class-defect-support, and $b in J$ by the finite-sum
  argument in the proof of @cor:trace-image-modular-reduction. If the sum is
  empty, this would give $b = 0$, a contradiction. Otherwise, the
  ${A_(G slash D_j)}$ are two-sided ideals in $A_G$ by
  @prop:g-algebra-relative-trace-properties@case:relative-trace-image-ideal.
  Then $b in A_(G slash D_j)$, for some $D_j <_G D$ by Rosenberg's Lemma,
  contradicting the assumption that $D$ is a defect group of $b$. Conversely,
  suppose that $b$ has an expression as in
  @case:block-defect-class-sum-coefficients. By
  @prop:trace-image-class-defect-support and the central-idempotent assertion of
  @cor:trace-image-modular-reduction, $b in A_(G slash D)$. Let $E$ be a defect
  group of $b$; then $E <=_G D$ by
  @th:primitive-idempotent-defect-group-existence. Since $b in A_(G slash E)$,
  @prop:trace-image-class-defect-support shows that the class defect group of
  each nonzero reduced coefficient is subconjugate to $E$. One such coefficient
  has class defect group conjugate to $D$, so $D <=_G E$. Therefore $D =_G E$,
  and $D$ is a defect group of $b$.

  Part~@case:modular-block-defect-class-sum-coefficients follows from
  part~@case:block-defect-group-modular-reduction, together with
  @prop:trace-image-class-defect-support and the argument used in
  part~@case:block-defect-class-sum-coefficients.

  Finally, @case:block-defect-realized-by-class follows from either
  part~@case:block-defect-class-sum-coefficients or
  @case:modular-block-defect-class-sum-coefficients.
]

#definition[
  Let $(K,R,k)$ be admissible for $G$, and let $sans(B)$ be a $p$-block of $G$
  defined by a block idempotent $b in R G$. A _defect group of the block_
  $sans(B)$ is any defect group of the block idempotent $b in A_G$, where
  $A = R G$. (Compare with @bib:CurtisReiner1962[CR], Definition~87.18.)
] <def:p-block-defect-group>
#idx(
  "Defect groups of idempotents",
  "of p-blocks",
  target: [@def:p-block-defect-group],
)
#idx("p-Blocks", "defect group of", target: [@def:p-block-defect-group])

By @th:primitive-idempotent-defect-group-existence, the defect groups of a
$p$-block of $G$ form a single conjugacy class of $p$-subgroups of $G$. By
@th:block-defect-class-sum-characterization, they coincide with the defect
groups of the block idempotents $overline(b) in overline(A)_G = c(k G)$. They
are related to the defect of the block as follows.

#corollary[
  Let $(K,R,k)$ be a $p$-modular system such that $op("char") K = 0$, and $K$ is
  sufficiently large relative to $G$. Let $sans(B)$ be a $p$-block of $G$ of
  defect $d$ (see @def:block-defect), and let $D$ be a defect group of
  $sans(B)$, as in @def:p-block-defect-group. Then $|D| = p^d$.
] <cor:block-defect-group-order>

The result follows at once from Theorems
@th:block-defect-class-sum-characterization and
@th:block-defect-central-character-criterion.

#source(453)
#corollary[
  Keep the hypothesis of Corollary @cor:block-defect-group-order. Then the
  defect groups of the principal $p$-block $sans(B)_1$ are the Sylow
  $p$-subgroups of $G$.
] <cor:principal-block-sylow-defect-groups>
#idx(
  "Principal p-block",
  "defect group of",
  target: [@cor:principal-block-sylow-defect-groups],
)

The proof is left as an exercise.

=== Defect Groups as Vertices <ss:block-defect-groups-vertices>

Defect groups of blocks can be interpreted as vertices of the indecomposable
block ideals in $R G$, under the two-sided action of $G times G$ on $R G$ (see
§~@i:sec:vertices-sources). We shall obtain this result, and other related
facts, in this subsection, after a review of the theory of vertices of
indecomposable $R G$-lattices from the point of view of $G$-algebras. This
approach, incidentally, is independent of most of §~@i:sec:vertices-sources, and
requires only Gaschütz's criterion @i:th:gaschutz-relative-projectivity for
relative projectivity.

We shall continue to use the definitions and notation introduced in
§~@ss:block-g-algebras-trace. We recall (see
§~@i:ss:indecomposable-lattice-vertices-sources) that an _$R G$-lattice_ is a
f.g. left $R G$-module, which is $R$-projective; we use the notation:
$ op("Ind") R H = "set of all indecomposable" R H "-lattices." $
Let $M$ be an $R G$-lattice, and let $E = op("End")_R M$, viewed as a
$G$-algebra as in @rem:g-algebra-endomorphism-and-conjugation-examples. The
$G$-action on $E$ is given by
$ x dot f = x f x^(-1) quad "for" x in G, quad f in E. $
Then
$ (x dot f)m = x f(x^(-1)m) quad "for all" m in M, quad x in G, quad f in E. $
As in §~@ss:block-g-algebras-trace, we set
$ E_H = {f in E: a f = f quad "for all" a in H}. $
Then $E_H$ is an $R$-subalgebra of $E$, for each subgroup $H <= G$, and, in
particular, we have
$ E_G = op("End")_(R G) M. $
We also require the trace map
$ T_(H slash D): E_D arrow E_H, quad "for" D <= H <= G, $
defined in @def:g-algebra-relative-trace, and use the notation
$ E_(H slash D) = T_(H slash D) E_D $
for the image of the trace map.

From §~@i:sec:vertices-sources, we recall that a _vertex_ of an indecomposable
$R G$-lattice $M$ is a subgroup $D <= G$ such that $M$ is $(G,D)$-projective,
and $D <=_G D'$ for any #source(454)other subgroup $D'$ such that $M$ is
$(G,D')$-projective. We also recall (see @i:th:gaschutz-relative-projectivity)
that $M$ is $(G,D)$-projective if and only if
$ T_(G slash D) f = op("id")_M quad "for some" f in E_D. $

#proposition[
  Let $M in op("Ind") R G$, and let $E = op("End")_R M$ be the $G$-algebra
  defined above. Then $op("id")_M$ is a primitive idempotent in $E_G$. Moreover,
  a subgroup $D <= G$ is a defect group of $op("id")_M$, in the sense of
  @def:primitive-idempotent-defect-group, if and only if $D$ is a vertex of $M$.
] <prop:endomorphism-defect-groups-vertices>
#idx(
  "Vertex",
  "of an indecomposable module",
  target: [@prop:endomorphism-defect-groups-vertices],
)
#idx(
  "Defect groups of idempotents",
  "as vertices",
  target: [@prop:endomorphism-defect-groups-vertices],
)

#proof[
  It is immediate, by @i:cor:indecomposable-endomorphism-idempotents, that
  $op("id")_M$ is primitive in $E_G = op("End")_(R G) M$. We next observe that
  $op("id")_M in E_(G slash D)$ for a subgroup $D <= G$ if and only if $M$ is
  $(G,D)$-projective, by the remarks preceding the statement of the proposition.
  Thus, in this case, the definitions of vertex and defect group coincide, and
  the proof is completed.
]

We next apply these ideas to block ideals in $R G$, and begin by noting that
$R G$ is an $R(G times G)$-lattice, where the action of $G times G$ on $R G$ is
given by
$ (x,y) dot a = x a y^(-1), quad a in R G, quad x,y in G. $
Let $G_0$ be the diagonal subgroup of $G times G$, and $Delta: G arrow G_0$ the
isomorphism given by
$ Delta(x) = (x,x), quad x in G. $
#nidx("$Delta G$", "diagonal subgroup of G × G")

#proposition[
  Let $b$ be a block idempotent in the $G$-algebra $A = R G$. A subgroup
  $D <= G$ is a defect group of $b in A_G$, in the sense of
  @def:primitive-idempotent-defect-group, if and only if $Delta D$ is a vertex
  of the indecomposable $R(G times G)$-lattice $A b = R G b$.
] <prop:block-ideal-diagonal-vertex>

#proof[
  It is easily checked that there is an isomorphism of $R(G times G)$-lattices
  $ R G tilde.equiv op("ind")_(G_0)^(G times G) 1_(G_0), $
  where $1_(G_0)$ denotes the trivial $R G_0$-module (see
  @i:prop:block-diagonal-relative-projectivity). A block ideal $R G b$ is an
  indecomposable direct summand of the $R(G times G)$-lattice $R G$, and hence
  is $(G times G,G_0)$-projective by @i:th:gaschutz-relative-projectivity(v),
  using the isomorphism above.

  It follows that a vertex of $R G b$ is a subgroup of $G_0$, and hence has the
  form $Delta D$, for some subgroup $D <= G$. We shall prove that $D$ is a
  defect group of the primitive idempotent $b in A_G$, where $A = R G$.

  Let $E = op("End")_R R G b$, viewed as a $(G times G)$-algebra with the action
  of $(x,y) in G times G$ on $f in E$ given by
  $ (x,y) f(a) = x f(x^(-1) a y)y^(-1) quad "for" a in A b. $
  Let $a_l$ denote left multiplication by $a in A$ on $R G b$; then $a_l in E$
  for all $a in A$, and $b_l$ acts as the identity on $R G b$. Let $H,L <= G$;
  then we have
  $
    b_l in E_(G times G slash H times L)
    <=> Delta D <=_(G times G) H times L,
  $ <eq:block-ideal-relative-projectivity-diagonal-vertex>
  #source(455)
  since $Delta D$ is a vertex of $R G b$. Using the formula for $(x,y) dot f$,
  $f in E$, we obtain
  $
    (x,y) dot a_l = (x dot a)_l quad "for all" a in A, quad x,y in G,
  $ <eq:block-left-multiplication-conjugation>
  where $x dot a = x a x^(-1)$. We also note that for $a in A$, $a_l$ commutes
  with the right multiplications on $R G b$ by elements of $G$; conversely, any
  element of $E$ which commutes with all the right multiplications by elements
  of $G$ has the form $a_l$ for some $a in A b$.

  We can now prove easily that
  $
    (A_H)_l = E_(H times G) quad "and"
    (A_(G slash D'))_l = E_(G times G slash D' times G)
  $ <eq:block-left-multiplication-trace-images>
  for all subgroups $D',H <= G$. For the first statement, let
  $(x,y) in H times G$. Then $(x,y) a_l = (x dot a)_l = a_l$ for $a in A_H$, by
  @eq:block-left-multiplication-conjugation. Thus
  $(A_H)_l subset.eq E_(H times G)$. Conversely, let $f in E_(H times G)$. Then
  $f = a_l$ for some $a in A b$ by a previous remark, and it follows that
  $a in A_H$ by @eq:block-left-multiplication-conjugation, since $A b$ acts
  faithfully on $A b$ by left multiplication. The second statement in
  @eq:block-left-multiplication-trace-images follows easily from the first.
  Indeed, $(A_(D'))_l = E_(D' times G)$ by the first part, so
  $
    E_(G times G slash D' times G) =
    T_(G times G slash D' times G) lr((A_(D')))_l.
  $
  If $a in A_(D')$, then we have
  $
    T_(G times G slash D' times G) lr((a_l))
    &= sum_(g in G slash D') (g,1) dot a_l \
    &= sum_(g in G slash D') (g dot a)_l
    quad ("by" #[@eq:block-left-multiplication-conjugation]) \
    &= (T_(G slash D') a)_l
  $
  by the definition of the trace maps. Thus we have proved
  @eq:block-left-multiplication-trace-images.

  Now let $D' <= G$. Then
  $
    b in A_(G slash D') <=> b_l in (A_(G slash D'))_l
    <=> b_l in E_(G times G slash D' times G)
    quad ("by" #[@eq:block-left-multiplication-trace-images]) \
    <=> Delta D <=_(G times G) D' times G
    quad ("by" #[@eq:block-ideal-relative-projectivity-diagonal-vertex]) \
    <=> D <=_G D'.
  $
  Therefore $D$ is a defect group of $b$ in $A_G$ in the sense of Definition
  @def:primitive-idempotent-defect-group, completing the proof.
]

We conclude this subsection with a connection between defect groups and vertices
of indecomposable modules in a block.

#proposition[
  Let $A$ be the $G$-algebra $R G$, let $D <= H <= G$, and let $e$ be an
  idempotent in $A_(H slash D)$. Let $M$ be a f.g. left $R G$-module such that
  $e M != 0$. Then $e M$ is an $(H,D)$-projective $R H$-module.
] <prop:trace-idempotent-relative-projectivity>
#idx(
  "Relative projective",
  target: [@prop:trace-idempotent-relative-projectivity],
)

#proof[
  #source(456)
  Since $e in A_H$, $x dot e = x e x^(-1) = e$ for all $x in H$, and hence $e M$
  is an $R H$-submodule of $M_H$. The further restriction that
  $e in A_(H slash D)$ means that
  $
    T_(H slash D) a = sum_(x in H slash D) x dot a = e
    quad "for some" a in A_D.
  $
  The operation $a arrow.r.bar x dot a$, $x in H$, is an $R$-algebra
  automorphism. Consequently,
  $
    e = e e e = sum_(x in H slash D) e(x dot a)e
    = sum_(x in H slash D) x dot lr((e a e)).
  $
  Thus
  $ T_(H slash D) lr((e a e)) = e. $
  The left multiplication $(e a e)_l$ lies in $op("End")_(R D) e M$, and we have
  $
    sum_(x in H slash D) x(e a e)_l x^(-1) = e_l = op("id")
    quad ("on" e M).
  $
  Thus $e M$ is $(H,D)$-projective by @i:th:gaschutz-relative-projectivity, and
  the proof is complete.
]

#corollary[
  Let $M$ be an indecomposable $R G$-lattice such that $b M = M$ for a block
  idempotent $b in R G$, and let $D$ be a defect group of $b$. Then $M$ is
  $(G,D)$-projective, so $D' <=_G D$ for any vertex $D'$ of $M$.
] <cor:block-module-vertices-subconjugate-defect-group>

#proof[
  Since $D$ is a defect group of $b$, we have $b in A_(G slash D)$, where $A$ is
  the $G$-algebra $R G$. Then $M$ is $(G,D)$-projective by
  @prop:trace-idempotent-relative-projectivity, and the result follows.
]

Later (see @th:hamernik-block-module-full-defect-vertex) we shall prove
Hamernik's Theorem that every $p$-block of $G$ with defect group $D$ contains an
indecomposable $R G$-lattice with vertex $D$. This result, together with
@cor:block-module-vertices-subconjugate-defect-group, characterizes defect
groups in terms of vertices of modules.

=== Defect Groups as Sylow Intersections
<ss:block-defect-groups-sylow-intersections>

This subsection is devoted to a proof of Green's Theorem (Green @bib:Green1962,
@bib:Green1963) that a defect group of a $p$-block can be expressed as the
intersection of two Sylow $p$-subgroups of $G$. The proof uses the preceding
discussion, and some additional properties of vertices proved in
§~@i:sec:vertices-sources.

Besides the notation introduced earlier in the section, we write $M divides N$
to indicate that an $R H$-module $M$ is isomorphic to a direct summand of $N$,
and
$ op("vtx") M, quad "for" M in op("Ind") R H $
to denote the set of vertices of the indecomposable $R H$-lattice $M$. Then
$op("vtx") M$ is an $H$-conjugacy class of $p$-subgroups of $H$.

#source(457)
#proposition[
  Let $M in op("Ind") R G$, let $D in op("vtx") M$, and let $D <= H <= G$. Then
  there exists $U in op("Ind") R H$ such that
  $ U divides M_H quad "and" quad D in op("vtx") U. $
] <prop:vertex-preserving-restriction-summand>

This result is an immediate consequence of Theorem
@i:th:green-vertices-going-down, since $D <= H$ implies that $M$ is
$(G,H)$-projective, by @i:prop:relative-projectivity-properties(vii).

#proposition[
  Let $M = R$, on which $G$ acts trivially. Then any Sylow $p$-subgroup of $G$
  is a vertex of $M$.
] <prop:trivial-module-sylow-vertices>

#proof[
  Let $D$ be a vertex of $M$, and $S$ a Sylow $p$-subgroup of $G$. Then
  $D <=_G S$ by @i:prop:vertices-p-subgroups-source-conjugacy(i) (or by
  @prop:endomorphism-defect-groups-vertices and
  @def:primitive-idempotent-defect-group). Now let $E = op("End")_R M$, viewed
  as a $G$-algebra as in §~@ss:block-defect-groups-vertices. Then
  $op("id")_M in T_(G slash D) E_D$, and $E_D = R dot op("id")_M$ since $M = R$.
  It follows that
  $ op("id")_M in |G:D| R dot op("id")_M. $
  If $D <_G S$ then $|G:D| in frak(p)$ so $op("id")_M in frak(p) op("id")_M$,
  which is impossible. Therefore $D =_G S$, as required.
]

The first statement of the next result is a consequence of the Green
Indecomposability Theorem (see
@i:cor:p-group-transitive-permutation-indecomposable). We shall give a new
elementary proof, due to M. Cabanes.

#proposition[
  Let $G$ be a $p$-group, and let $M$ be a transitive permutation module over
  $R G$, that is, $M$ has an $R$-basis $X$ which is a transitive $G$-set. Let
  $H = op("Stab")_G x_0$, for some $x_0 in X$. Then $M in op("Ind") R G$, and
  $H in op("vtx") M$.
] <prop:p-group-transitive-permutation-vertex>

#proof[
  We have $M tilde.equiv (1_H)^G$, as $R G$-module. In case $R$ is a d.v.r. with
  residue field $k$, it suffices to prove that $k times.o_R M$ is an
  indecomposable $k G$-module, and we have $k times.o_R M tilde.equiv (1_H)^G$
  as $k G$-modules. Thus, in case $R$ is either a field of characteristic $p$ or
  a d.v.r. with residue field $k$ of characteristic $p$, it is sufficient to
  prove that $(1_H)^G$ is indecomposable, in case $1_H$ is the trivial
  $k H$-module for a field $k$ of characteristic $p$. Since $op("inv")_G M != 0$
  for any $k G$-module $M$, for a finite $p$-group $G$ (see
  @i:th:p-group-algebra-local), the indecomposability of $(1_H)^G$ will follow
  if we can prove that
  $ dim_k op("inv")_G lr(((1_H)^G)) = 1. $
  But this follows at once from Frobenius reciprocity
  @i:prop:frobenius-right-adjoint, since
  $
    op("inv")_G lr(((1_H)^G)) tilde.equiv
    op("Hom")_(k G) lr((1_G,(1_H)^G)) tilde.equiv
    op("Hom")_(k H) lr((1_(k H),1_(k H))) tilde.equiv k.
  $
  Thus $M in op("Ind") R G$, and the first statement is proved.

  For the second statement, we begin with the fact that $M$ is
  $(G,H)$-projective by @i:th:gaschutz-relative-projectivity(v), since
  $M tilde.equiv (1_H)^G$. Then $D <=_G H$ for any $D in op("vtx") M$.
  Conversely, $1_H divides M_H$ #source(458)by
  @i:lem:induction-relative-splittings(a). By
  @prop:trivial-module-sylow-vertices, $H in op("vtx") 1_H$, and so $H <=_G D$
  by @i:th:vertices-induction-restriction(i). This completes the proof.
]

The main result can now be stated as follows:

#theorem[
  Let $D$ be a defect group of a block idempotent $b in R G$. Let $S$ be a Sylow
  $p$-subgroup of $G$ containing $D$. Then there exists an element
  $z in C_G lr((D))$ such that
  $ D = S inter attach(S, tl: z). $
] <th:block-defect-sylow-intersection>
#idx(
  "Defect groups of idempotents",
  "as Sylow intersections",
  target: [@th:block-defect-sylow-intersection],
)
#idx("Green's Theorem", target: [@th:block-defect-sylow-intersection])

#proof[
  The idea of the proof is straightforward. Since $D <= S$, we have
  $Delta D <= S times S$ in $G times G$. We then decompose $(R G)_(S times S)$
  as a direct sum of indecomposable $R(S times S)$-lattices, and determine their
  vertices. Since $(R G b)_(S times S) divides
  (R G)_(S times S)$, the K-S-A Theorem implies that $(R G b)_(S times S)$ is
  isomorphic to a direct sum of a subset of the indecomposable summands of
  $(R G)_(S times S)$. Since $Delta D$ is a vertex of the indecomposable
  $R(G times G)$-lattice $R G b$ by @prop:block-ideal-diagonal-vertex, it
  follows that $Delta D$ is a vertex of one of the $(S times S)$-summands of
  $R G$, which will turn out to have the required form. Now we shall fill in the
  details.

  Let
  $ G = union.dot.big_(i=1)^m S x_i S, $
  where ${S x_i S}$ are the $(S,S)$-double cosets in $G$. Then clearly
  $ R G = plus.big_(i=1)^m R(S x_i S), $
  where $R(S x_i S)$ is the $R$-submodule of $R G$ with an $R$-basis consisting
  of the elements of $S x_i S$. Each summand $R(S x_i S)$ is a submodule of
  $(R G)_(S times S)$ under the two-sided action of $S$. The key result is:
]

#lemma[
  Let $M = R(S x S)$ be the $R(S times S)$-sublattice of $(R G)_(S times S)$
  defined by an $(S,S)$-double coset $S x S$, for some $x in G$. Then
  $M in op("Ind") R(S times S)$, and
  $
    attach((Delta(S inter attach(S, tl: x^(-1)))), tl: (x,1))
    in op("vtx") M,
  $
  (where $attach((Delta X), tl: (x,1))$ denotes the conjugate of $Delta X$ by
  $(x,1)$ in $G times G$, for a subset $X subset.eq G$).
] <lem:double-coset-permutation-module-vertex>

#proof(head: emph[Proof of @lem:double-coset-permutation-module-vertex.])[
  The $p$-group $S times S$ acts transitively on the double coset $S x S$.
  Therefore $M$ is a transitive permutation module over $R(S times S)$, and, by
  @prop:p-group-transitive-permutation-vertex, $M$ is indecomposable, with
  vertex $op("Stab")_(S times S) x$. Thus we need only check that
  $
    op("Stab")_(S times S) x =
    attach((Delta(S inter attach(S, tl: x^(-1)))), tl: (x,1)).
  $
  Let $h in S inter attach(S, tl: x^(-1))$; then
  $attach((h,h), tl: (x,1)) = (attach(h, tl: x),h)$, and
  $ (attach(h, tl: x),h) dot x = x h x^(-1) x h^(-1) = x, $
  #source(459)
  so $attach((Delta(S inter attach(S, tl: x^(-1)))), tl: (x,1)) <=
  op("Stab")_(S times S) x$. For the reverse inclusion, let
  $(u,v) in S times S$, and assume that $(u,v)x = u x v^(-1) = x$. Then
  $v = x^(-1) u x in S inter attach(S, tl: x^(-1))$ and
  $(u,v) = attach((v,v), tl: (x,1))$, as required.
]

#proof(head: emph[Proof of @th:block-defect-sylow-intersection.])[
  By the K-S-A Theorem, it follows that $(R G b)_(S times S)$ is a direct sum of
  indecomposable $R(S times S)$-lattices, each of which is isomorphic to
  $R(S x_i S)$ for some $i$, $1 <= i <= m$. Since $Delta D <= S times S$ and
  $Delta D$ is a vertex of $R G b$ by @prop:block-ideal-diagonal-vertex, it
  follows that
  $
    Delta D =_(S times S)
    attach((Delta(S inter attach(S, tl: x^(-1)))), tl: (x,1)),
  $
  for some $x in G$, by @prop:vertex-preserving-restriction-summand and
  @lem:double-coset-permutation-module-vertex. Then for some element
  $(g,h) in S times S$, we have
  $
    Delta D = attach(
      Delta(S inter attach(S, tl: x^(-1))),
      tl: (g,h)(x,1)
    )
  $
  and
  $ (g,h)(x,1) = (g x h^(-1),1)(h,h). $
  It follows that
  $
    Delta D = attach((Delta(S inter attach(S, tl: z^(-1)))), tl: (z,1)),
    quad "for" z = g x h^(-1).
  $
  Then $u in D$ if and only if there exists $v in S inter attach(S, tl: z^(-1))$
  such that
  $ (u,u) = (attach(v, tl: z),v). $
  We obtain $D = S inter attach(S, tl: z^(-1))$ by comparing the second
  components, and $z in C_G lr((D))$ by comparing the first. This completes the
  proof.
]

Some applications are given in the Exercises. Refinements of Theorem
@th:block-defect-sylow-intersection have been obtained by Green @bib:Green1963,
Lam @bib:Lam1976, and Robinson @bib:Robinson1983. A different proof was given by
Thompson @bib:Thompson1967a. Robinson also found criteria for a given
$p$-subgroup of $G$ to be a defect group of some $p$-block. Humphreys
@bib:Humphreys1971 applied the theorem above to determine the $p$-blocks in
finite Chevalley groups over fields of characteristic $p$.

#exercises-heading

The assumptions about the underlying $p$-modular system $(K,R,k)$ in the
Exercises for §~@sec:introduction-block-theory remain in force. In addition, it
may be assumed that $R$ is complete in the $frak(p)$-adic topology, and that $k$
is a perfect field, in exercises involving Green's Theorem on Zeros of
Characters @i:th:green-character-zeros.

#exercise[
  Let $B$ be a block ideal in $k G$. Prove that $B$ is a simple $k$-algebra if
  and only if the defect group of the corresponding block idempotent is ${1}$.
] <exc:simple-block-algebra-trivial-defect>
#hint([@exc:simple-block-algebra-trivial-defect])[
  Use @cor:block-module-vertices-subconjugate-defect-group for one implication
  and Exercise @exc:simple-projective-block-defect-zero for the other. Also see
  Exercise @exc:defect-zero-block-maximal-order-proof.
]

#source(460)
#exercise[
  Let $zeta$ be an irreducible $K$-character of $G$ belonging to a $p$-block
  with defect group $D$. Let $x in G$ be an element whose $p$-part is not
  conjugate to an element of $D$. Prove that $zeta(x) = 0$.
] <exc:block-character-vanishing-outside-defect>
#hint([@exc:block-character-vanishing-outside-defect])[
  Use @prop:trace-idempotent-relative-projectivity and Green's Theorem on Zeros
  of Characters @i:th:green-character-zeros.
]

#exercise[
  A _trivial source module_ is an indecomposable $R G$-lattice $M$ such that
  $M divides (1_H)^G$ for some subgroup $H <= G$, where $1_H$ denotes the
  $R H$-lattice $R$ with trivial $H$-action. Prove the following statements (see
  also §~@sec:representation-rings).
  #case-list(
    numbering: "(i)",
    [#case[Let $D$ be a vertex of a trivial source module $M$. Prove that
      $M divides (1_D)^G$ (so that $M$ does indeed have a trivial source in the
      sense of Definition @i:def:lattice-vertex-source).
      #hint([@exc:trivial-source-module-vertices])[
        By @i:th:green-vertices-going-down(i), choose $N in op("Ind") R D$ with
        $N divides M_D$ and $M divides N^G$; then $D$ is a vertex of $N$.
        Mackey's Subgroup Theorem @i:th:mackey-subgroup shows that $N$ is a
        summand of a sum of modules $(1_E)^D$, where $E = D inter attach(
          H,
          tl: x
        )$. By @prop:p-group-transitive-permutation-vertex, each is
        indecomposable with vertex $E$. The K-S-A Theorem
        @i:th:krull-schmidt-azumaya therefore gives $N tilde.equiv (1_E)^D$ for
        one such $E$. Since $D$ is a vertex of $N$ and $E <= D$, we have
        $E = D$. Thus $N tilde.equiv 1_D$ and $M divides (1_D)^G$.#ed-note[
          The original Hint claims $1_H divides (1_D)^H$. Take $G = S_3$,
          $p = 2$, $R = ZZ_2 lr([zeta_3])$, $H = chevron.l (12) chevron.r$, and
          let $M$ be the augmentation summand of $R^3$: its reduction is simple
          and $M_H tilde.equiv R H$, so $D = 1$. But $(1_D)^H = R H$ is
          indecomposable and has no summand $1_H$.
        ]
      ]
    ] <case:trivial-source-induction-from-vertex>],
    [#case[Let $M$ be a trivial source module with vertex $D$. Prove that
      $1_D divides M_D$ (where $M_D = op("res")_D^G M$).
      #hint([@exc:trivial-source-module-vertices])[
        By part~@case:trivial-source-induction-from-vertex, $1_D$ is a source of
        $M$. Since $M$ is $(G,D)$-projective, $M_D$ has an indecomposable
        summand having a vertex and source in common with $M$, by
        @i:th:green-vertices-going-down.
      ]
    ] <case:trivial-source-vertex-restriction>],
    [#case[Let $M$ be a trivial source module with vertex $D$, such that
      $M divides (1_H)^G$ for some subgroup $H <= G$. Prove that $M_H$ has an
      indecomposable summand $U$ with vertex $D'$ such that $H inter D <=_H D'$.
      #hint([@exc:trivial-source-module-vertices])[
        By part~@case:trivial-source-vertex-restriction, $1_D divides M_D$, so
        $1_(D inter H) divides M_(D inter H)$. Then $M_H$ has an indecomposable
        summand $U$ such that $1_(D inter H) divides U_(D inter H)$. Since
        $D inter H$ is a vertex of $1_(D inter H)$ (by
        @prop:trivial-module-sylow-vertices), we have $D inter H <=_H D'$ (by
        @i:th:vertices-induction-restriction).
      ]
    ] <case:trivial-source-subgroup-intersection-vertex>],
  )
] <exc:trivial-source-module-vertices>
#idx(
  "Trivial source module",
  target: [@exc:trivial-source-module-vertices],
  see-also: (("pp-module",),),
)
#idx("pp-module", target: [@exc:trivial-source-module-vertices])

#exercise[
  Prove that block ideals in $R G$ are trivial source modules (as
  $R(G times G)$-modules). (The same result holds for block ideals in $k G$.)
] <exc:block-ideals-trivial-source>
#idx(
  "Block ideals",
  "as trivial source modules",
  target: [@exc:block-ideals-trivial-source],
)
#hint([@exc:block-ideals-trivial-source])[
  Use the fact that
  $ R G tilde.equiv (1_(Delta G))^(G times G) $
  as $R(G times G)$-lattices, where $Delta G$ denotes the diagonal subgroup of
  $G times G$.
]

#exercise[
  Let $B$ be a block ideal in $R G$. Prove that $B$ is an absolutely
  indecomposable $R(G times G)$-lattice.
] <exc:block-ideals-absolutely-indecomposable>
#idx(
  "Absolutely indecomposable",
  target: [@exc:block-ideals-absolutely-indecomposable],
)
#hint([@exc:block-ideals-absolutely-indecomposable])[
  Let $B = b R G$, for a block idempotent $b$. Let
  $E = op("End")_(R(G times G)) B$, and $tilde(E) = E slash op("rad") E$. Show
  that $E tilde.equiv c(R G)b$, by @eq:block-left-multiplication-trace-images,
  and that $tilde(E) tilde.equiv k$ by the results in
  §~@ss:central-characters-blocks. Then apply
  @i:th:absolute-indecomposability-residue-endomorphism.
]

#exercise[
  (Alperin @bib:Alperin1967; Green @bib:Green1963). Let $D$ be a defect group of
  a $p$-block of $G$. Prove that $D$ is a _tame intersection_ of Sylow
  $p$-subgroups of $G$, i.e., there exist Sylow subgroups $P,Q$ of $G$ such that
  $D = P inter Q$ and $N_P lr((D))$ and $N_Q lr((D))$ are both Sylow subgroups
  of $N_G lr((D))$.
] <exc:block-defect-tame-sylow-intersection>
#hint([@exc:block-defect-tame-sylow-intersection])[
  Let $A$ be a Sylow $p$-subgroup of $N_G lr((D))$. Then $A supset.eq D$. Choose
  a Sylow $p$-subgroup $P$ of $G$ such that $P supset.eq A$. Then
  $A = P inter N_G lr((D)) = N_P lr((D))$. By Theorem
  @th:block-defect-sylow-intersection, there exists $z in C_G lr((D))$ such that
  $D = P inter Q$ with $Q = attach(P, tl: z)$. Then
  $attach(A, tl: z) = attach(P, tl: z) inter N_G lr((D)) =
  Q inter N_G lr((D)) = N_Q lr((D))$, and the result follows.
]
