#import "main-defs.typ": *
#import "statements.typ": *

== $p$-Sections and Characters in Blocks <sec:p-sections-blocks>

=== Block Orthogonality and $p$-Sections <ss:block-orthogonality-p-sections>

We continue the study of characters in blocks, begun in
§~@ss:nagao-decomposition, with some orthogonality relations involving blocks of
characters and $p$-sections. These results, which are due to Brauer, often
provide a practical method for distributing the irreducible characters into
$p$-blocks, using information about the character table, in cases where it would
be difficult to test the congruence relations
@cor:block-central-character-congruence. Some applications are given in
§§~@ss:principal-block-orthogonality and @ss:prime-degree-permutation-groups.

As in §~@ss:nagao-decomposition, we fix a $p$-modular system $(K,R,k)$ such that
$op("char") K=0$, $K$ is sufficiently large relative to $G$, $R$ is a complete
d.v.r. with maximal ideal $frak(p)$ and quotient field $K$, and
$k=R slash frak(p)$, a perfect field of characteristic $p$. We set
$ op("Irr") G={zeta^1=1_G,...,zeta^s} $
and ${upright(sans(B))_1,...,upright(sans(B))_t}$ the $p$-blocks of $G$, defined
by block idempotents ${b_1,...,b_t}$ in $R G$, with $upright(sans(B))_1$ the
principal block, containing $zeta^1$.

#definition[
  Let $U$ denote the set of all $p$-elements in $G$. Each element $u in U$
  defines a _$p$-section_ $X=X(u)$, consisting of all elements $x in G$ whose
  $p$-part is conjugate to $u$.
] <def:p-section>
#idx("p-section", target: [@def:p-section])

An equivalence relation may be defined on $G$, putting $x$ equivalent to $y$ if
and only if the $p$-parts of $x$ and $y$ are conjugate in $G$. The $p$-sections
are clearly the equivalence classes in $G$ for this equivalence relation. It is
also clear that each $p$-section is a union of conjugacy classes. One
$p$-section has already been used extensively, namely the set $G_(p')$
consisting of all $p'$-elements of $G$.

The first result will be called the theorem on _$p$-section orthogonality_.

#theorem(title: "Brauer")[
  Let $upright(sans(B))_j$ be a $p$-block of $G$. Then
  $
    sum_(zeta^i in upright(sans(B))_j) zeta^i lr((x)) zeta^i lr((y^(-1)))=0,
    quad "for" x,y in G,
  $
  unless $x$ and $y$ belong to the same $p$-section.
] <th:block-p-section-orthogonality>
#idx("p-section orthogonality", target: [@th:block-p-section-orthogonality])

#source(488)
#proof(head: emph[Proof (Green @bib:Green1962).])[
  We shall apply Green's Theorem on Zeros of Characters
  @th:green-character-zeros-restatement. Let $b_j in R G$ be the block
  idempotent associated with $upright(sans(B))_j$, and let $D_j$ be a defect
  group of $upright(sans(B))_j$. By
  Proposition~@prop:block-ideal-diagonal-vertex, $Delta D_j={(d,d):d in D_j}$ is
  a vertex of the indecomposable $R(G times G)$-lattice $R G b_j subset.eq R G$,
  under the usual action of $G times G$ on $R G$. Then $R G b_j$ is
  $(G times G,Delta D_j)$-projective. Now let $x,y in G$, and let $u,v$ be the
  $p$-parts of $x$ and $y$, respectively. Then the $p$-part of
  $(x,y) in G times G$ is $(u,v)$. If $x$ and $y$ belong to different
  $p$-sections, then $u !=_G v$, and hence $(u,v)$ is not conjugate in
  $G times G$ to an element of $Delta D_j$. Thus we obtain
  $ op("Tr")((x,y),R G b_j)=0, $
  by Theorem~@th:green-character-zeros-restatement.

  The proof is completed as follows. Since $K G b_j=K times.o_R R G b_j$, we
  have
  $ op("Tr")((x,y),R G b_j)=op("Tr")((x,y),K G b_j)=0. $
  Moreover,
  $ K G b_j=sum_(zeta^i in upright(sans(B))_j) K G e_i, $
  where $e_i$ is the central primitive idempotent in $K G$ corresponding to
  $zeta^i$ (see @prop:block-idempotent-ordinary-components). The two-sided
  ideals $K G e_i$ are stable under the action of $(x,y) in G times G$, so it is
  sufficient to prove that for each irreducible character $zeta^i$, and
  $(x,y) in G times G$,
  $ op("Tr")((x,y),K G e_i)=zeta^i lr((x)) zeta^i lr((y^(-1))). $
  This is a nice problem in character theory, and is left to the reader. This
  completes the proof of the theorem.
]

#remarks(numbered: false)[
  The preceding result includes Lemma~@lem:block-mixed-character-orthogonality
  as a special case. The proofs we have given for the two results are quite
  different. The proof of @lem:block-mixed-character-orthogonality is based on
  calculations with Brauer characters and depends on the invertibility of the
  Brauer character table matrix $Phi$, while the proof of
  @th:block-p-section-orthogonality uses the theory of relatively projective
  modules and Green's Theorem on Zeros of Characters.

  Brauer's Theorem is closely related to the Second Orthogonality
  Theorem~@i:prop:first-second-character-orthogonality. By
  Theorem~@i:prop:first-second-character-orthogonality, any two distinct columns
  of the character table matrix $Z$ in @i:def:character-table-data are
  orthogonal. Brauer's theorem asserts that the parts of two distinct columns
  arising from characters in a single $p$-block are orthogonal, provided the
  columns are defined by conjugacy classes belonging to different $p$-sections.
] <rem:block-orthogonality-comparison>

#idx("Brauer's Second Main Theorem")
We turn now to another connection between blocks of characters and $p$-sections,
based on Brauer's Second Main Theorem. We first introduce some notation. Let
$ alpha=sum_(i=1)^s a_i zeta^i, quad a_i in K, $
#source(489)
be an arbitrary class function in $op("cf")_K G$. For each block
$upright(sans(B))_j$, define
$ alpha_(upright(sans(B))_j)=sum_(zeta^i in upright(sans(B))_j) a_i zeta^i. $
We then have:

#theorem[
  Let $alpha in op("cf")_K G$, and suppose that $alpha$ vanishes on a given
  $p$-section $X$. Then $alpha_(upright(sans(B))_j)$ vanishes on $X$, for each
  $p$-block $upright(sans(B))_j$, $1 <= j <= t$. In other words, if a class
  function vanishes on a $p$-section, then it vanishes block by block.
] <th:p-section-vanishing-blockwise>

#proof(head: emph[Proof (Feit @bib:Feit1982).])[
  Let $alpha=sum_(i=1)^s a_i zeta^i$, for $a_i in K$, and let $u$ be a
  $p$-element in the $p$-section $X$. Set $H=C_G lr((u))$. Then by assumption,
  $alpha(s u)=0$ for all $s in H_(p')$. Using
  Proposition~@prop:generalized-decomposition-coefficients, we obtain
  $
    alpha(s u)=sum_(j=1)^(r') (sum_(i=1)^s a_i d^u_(i j))
    xi^j lr((s))=0,
    quad "for all" s in H_(p'),
  $
  where ${xi^1,...,xi^(r')}$ are the irreducible Brauer characters of $H$, and
  the ${d^u_(i j)}$ are the generalized decomposition numbers. Since the
  irreducible Brauer characters of $H$ are linearly independent on $H_(p')$ (see
  @i:th:brauer-characters-class-function-basis), it follows that
  $ sum_(i=1)^s a_i d^u_(i j)=0 quad "for" j=1,...,r'. $
  <eq:p-section-generalized-coefficient-vanishing>
  Now let $upright(sans(B))$ be a fixed $p$-block of $G$. By the second form of
  Brauer's Second Main Theorem~@th:brauer-second-main-second-form, we know that
  $d^u_(i j) != 0$ for $zeta^i in upright(sans(B))$ only if $xi^j$ belongs to a
  block $upright(sans(B))'$ of $H$ such that
  $(upright(sans(B))')^G=upright(sans(B))$. It follows easily from this result
  and @eq:p-section-generalized-coefficient-vanishing that
  $ sum_(zeta^i in upright(sans(B))) a_i d^u_(i j)=0 quad "for" j=1,...,r'. $
  Upon substituting back in the formula for $alpha(s u)$, we obtain
  $
    alpha(s u)=sum_(j=1)^(r') (sum_(zeta^i in upright(sans(B))) a_i d^u_(i j))
    xi^j lr((s))=0
  $
  for all $s in H_(p')$ and hence
  $ alpha_(upright(sans(B))) lr((s u))=0 quad "for all" s in H_(p'). $
  Since every element in the given $p$-section $X$ is conjugate to $s u$ for
  some $s in H_(p')$, we have shown that $alpha_(upright(sans(B)))$ vanishes on
  $X$, for each block $upright(sans(B))$, as required.
]

=== Determination of the Principal Block Using Block Orthogonality
<ss:principal-block-orthogonality>

We shall apply the results on block orthogonality
(§~@ss:block-orthogonality-p-sections) to determine the principal block in
certain types of finite groups. In the rest of this subsection we assume:

#source(490)
#theorem(name: "Hypothesis")[
  $G$ is a finite group with a cyclic Sylow $p$-subgroup $D$ satisfying the
  conditions
  #case-list(
    numbering: "(i)",
    [#case[$C_G lr((D))=D$ ($D$ is self-centralizing)]
      <case:cyclic-sylow-self-centralizing>],
    [#case[$D^*$ is a T.I. set with normalizer $H=N_G lr((D))$, where
        $D^*=D-{1}$ (see @i:def:trivial-intersection-set).]
      <case:cyclic-sylow-trivial-intersections>],
  )
] <th:cyclic-self-centralizing-ti-sylow-hypothesis>

Examples of groups satisfying @th:cyclic-self-centralizing-ti-sylow-hypothesis
were given in §~@i:ss:green-correspondence-character-applications; they include
the infinite family of finite simple groups ${op("PSL")_2 lr((FF_p)):p >= 5}$.

The characters of finite groups satisfying
@th:cyclic-self-centralizing-ti-sylow-hypothesis were determined in
§~@i:ss:green-correspondence-character-applications, and we begin by recalling
some concepts and results from §~@i:ss:exceptional-characters-ca-groups and
§~@i:ss:green-correspondence-character-applications.

#proposition[
  Let $G$ be a finite group satisfying
  @th:cyclic-self-centralizing-ti-sylow-hypothesis. Then the following
  statements hold.
  #case-list(
    numbering: "(i)",
    [#case[For all $x in D^*$, $C_G lr((x))=D$ (so $D$ is an
        SA-subgroup#footnote[See Volume I,
          §~@i:ss:exceptional-characters-ca-groups, following
          Lemma~@i:lem:ca-maximal-abelian-centralizers.] <fn:sa-subgroup>).]
      <case:cyclic-ti-sylow-element-centralizers>],
    [#case[If $H != D$, the normalizer $H=N_G lr((D))$ is a Frobenius group with
      Frobenius kernel $D$.] <case:cyclic-ti-sylow-normalizer-frobenius>],
    [#case[$H tilde.equiv D ⋊ A$, where $A$ is an abelian group whose order
      divides $p-1$.] <case:cyclic-ti-sylow-normalizer-complement>],
  )
] <prop:cyclic-ti-sylow-normalizer-structure>

#proof[
  @case:cyclic-ti-sylow-element-centralizers. Let $z in C_G lr((x))$ for
  $x in D^*$, and assume for the moment that $z in.not D$. We first observe that
  $H slash D=N_G lr((D)) slash C_G lr((D))$, and is isomorphic to a subgroup of
  $op("Aut") D$. The only automorphisms $alpha != 1$ of a cyclic $p$-group $D$
  having nontrivial fixed points are those of order divisible by $p$, and these
  do not arise from elements of $H$ since $D$ is a Sylow $p$-subgroup of $G$.
  Thus we may assume $z in.not H$. In that case, $attach(D, tl: z) != D$ and
  $x in D inter attach(D, tl: z)$, contradicting the assumption that $D^*$ is a
  T.I. set. The statement @case:cyclic-ti-sylow-normalizer-frobenius follows
  from @case:cyclic-ti-sylow-element-centralizers, by
  @i:prop:sa-subgroup-special-classes(i). The factorization of $H$ given in
  @case:cyclic-ti-sylow-normalizer-complement follows from
  @case:cyclic-ti-sylow-normalizer-frobenius when $H != D$, and is trivial when
  $H=D$. The properties of $A$ are clear, since
  $A tilde.equiv N_G lr((D)) slash C_G lr((D))$ by
  @th:cyclic-self-centralizing-ti-sylow-hypothesis, and
  $N_G lr((D)) slash C_G lr((D))$ is isomorphic to a subgroup of the
  automorphism group of the cyclic group $D$.
]

We shall determine the structure of the principal block in groups $G$ satisfying
@th:cyclic-self-centralizing-ti-sylow-hypothesis. In case $abs(D)=p$, the
results are due to Brauer @bib:Brauer1941a, and, in the general case, to
Thompson @bib:Thompson1967. These ideas led to Dade's definitive work on the
structure of blocks with cyclic defect groups (see Dade @bib:Dade1966, Feit
@bib:Feit1982, VII, and §~@sec:cyclic-defect-blocks).

The results we need from §~@i:ss:green-correspondence-character-applications are
as follows. Let $H=D A$ as in @case:cyclic-ti-sylow-normalizer-complement, and
put
$ m=abs(D)=p^d, quad e=abs(H slash D)=abs(A), quad "and" n=(m-1) slash e. $
We shall assume, in the rest of the subsection, that $n >= 2$. By
@i:prop:sa-subgroup-special-classes, the set $D^*$ is the union of exactly $n$
special classes in $H$.

#source(491)
The characters are taken in a field $K$ such that $op("char") K=0$ and $K$ is
sufficiently large relative to $G$. When appropriate we also assume that $K$ is
part of a $p$-modular system $(K,R,k)$.

In $H=D ⋊ A$, the group $A$ acts freely on $D^*$. The nontrivial linear
characters of $D$ induce $n$ distinct irreducible characters ${psi_1,...,psi_n}$
of $H$, one for each $A$-orbit, all of degree $e$. By
@i:prop:sa-subgroup-special-classes(iv), a $ZZ$-basis for the virtual characters
of $H$ vanishing off the special classes is given by
$ lambda_i=psi_i-psi_n, quad 1 <= i <= n-1, $
together with any one additional character of the form
$ (1_D)^H-psi_i, quad 1 <= i <= n. $
By @i:th:green-cyclic-sylow-character-values we have
$ op("Irr") G={1_G,zeta_1,...,zeta_n;theta_1,...,theta_f;chi_1,...,chi_h}. $
There exists a sign $epsilon=plus.minus 1$ and multiplicities $a$ and
$c_l != 0$, $1 <= l <= f$, such that
$ (lambda_i)^G=(psi_i-psi_n)^G=epsilon(zeta_i-zeta_n), quad 1 <= i <= n-1 $
and
$
  Gamma_i=((1_D)^H-psi_i)^G=1_G-epsilon zeta_i+a sum_(j=1)^n zeta_j
  +sum_(l=1)^f c_l theta_l, quad 1 <= i <= n.
$
The constants $epsilon$, $a$, and ${c_l}$ are independent of $i$, $1 <= i <= n$,
and satisfy the conditions:
$
  e=a^2(n-1)+(a-epsilon)^2+sum_(l=1)^f c_l^2,\
  a=0, "or" epsilon, quad abs(c_l)=1, 1 <= l <= f, quad "and" f=e-1.
$
The characters ${zeta_1,...,zeta_n}$ are called _exceptional characters_
(relative to $D$), and the characters ${theta_1,...,theta_f;chi_1,...,chi_h}$
are called _nonexceptional_, and are arranged so that the first $f$ characters
${theta_j}$ appear with nonzero multiplicity in the virtual characters
$Gamma_i$, $1 <= i <= n$, while the remaining ones ${chi_j}$ have the property
that $(chi_j,Gamma_i)=0$ for all $j$, $1 <= j <= h$, and $i$, $1 <= i <= n$. We
then have (see @i:th:green-cyclic-sylow-character-values).

#theorem[
  Let $n=(m-1) slash e >= 2$. Then the following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[The exceptional characters ${zeta_i}$ have the same degree, which is
      prime to $p$. The nonexceptional characters ${theta_j:1 <= j <= f}$ have
      degrees satisfying $theta_j lr((1)) equiv plus.minus 1 quad
      (mod p)$, while the degrees of the remaining characters ${chi_j}$ are all
      divisible by $abs(D)$.] <case:cyclic-ti-character-degrees>],
    [#case[
      #source(492)
      Up to sign, the values of the ${zeta_i}$ agree with the values of the
      ${psi_i}$ on the special classes. More precisely, we have
      $ zeta_i |_(D^*)=epsilon psi_i |_(D^*), quad 1 <= i <= n. $
      The values of the nonexceptional characters ${theta_j}$ on the elements of
      $D^*$ are all $plus.minus 1$, while the nonexceptional characters
      ${chi_j}$ vanish on $D^*$.
    ] <case:cyclic-ti-character-special-values>],
    [#case[
      The exceptional characters agree on the elements of $G_(p')$:
      $
        zeta_i lr((x))=zeta_j lr((x)), quad "for all" x in G_(p'),
        quad 1 <= i,j <= n.
      $
      The values of the characters ${theta_j}$ and ${zeta_i}$ are related as
      follows:
      $
        delta zeta_1 lr((x))=1+sum_(i=1)^f delta_i theta_i lr((x))
        quad "for all" x in G_(p'),
      $
      where ${delta,delta_1,...,delta_f}$ are all $plus.minus 1$, and are
      independent of $x in G_(p')$.
    ] <case:cyclic-ti-character-regular-values>],
  )
] <th:cyclic-ti-sylow-character-values>

Here is the main result of this subsection.

#theorem[
  Let $G$ be a finite group satisfying
  @th:cyclic-self-centralizing-ti-sylow-hypothesis. Then the following
  statements hold.
  #case-list(
    numbering: "(i)",
    [#case[The principal block $upright(sans(B))_1$ of $G$ consists of the
      irreducible characters ${1_G,zeta_1,...,zeta_n;theta_1,...,theta_f}$ (in
      the notation of @th:cyclic-ti-sylow-character-values). These are precisely
      the irreducible characters of $G$ whose degrees are prime to
      $p$.] <case:cyclic-ti-principal-block-characters>],
    [#case[The decomposition numbers for irreducible characters in
      $upright(sans(B))_1$ are all either $0$ or
      $1$.] <case:cyclic-ti-principal-decomposition-numbers>],
    [#case[Each nonprincipal block of $G$ has defect zero, and contains a single
      nonexceptional irreducible character $chi_j$, for
      $1 <= j <= h$.] <case:cyclic-ti-nonprincipal-defect-zero>],
  )
] <th:cyclic-ti-sylow-principal-block>
#idx("p-Blocks", "principal", target: [@th:cyclic-ti-sylow-principal-block])
#idx("Principal p-block", target: [@th:cyclic-ti-sylow-principal-block])

Assuming the truth of part~@case:cyclic-ti-principal-block-characters, the rest
of the theorem is a consequence of earlier results. In fact,
@case:cyclic-ti-principal-decomposition-numbers follows from
Theorem~@i:th:green-cyclic-sylow-character-values(v), while
@case:cyclic-ti-nonprincipal-defect-zero is a consequence of
@th:cyclic-ti-sylow-character-values@case:cyclic-ti-character-degrees and
@prop:block-defect-brauer-degrees. Before giving the proof of
part~@case:cyclic-ti-principal-block-characters, we establish some preliminary
results.

#lemma[
  Let $D$ be a cyclic Sylow $p$-subgroup of $G$, satisfying
  @th:cyclic-self-centralizing-ti-sylow-hypothesis. Then the subgroup
  $H=N_G lr((D))$ has only one $p$-block.
] <lem:cyclic-ti-sylow-normalizer-single-block>

#proof[
  Let $(K,R,k)$ be a $p$-modular system, with $op("char") K=0$ and $K$
  sufficiently large. Let $upright(sans(B))$ be an arbitrary $p$-block of $H$,
  and $b$ the corresponding block idempotent in $c(R H)$. Since $D$ is a normal
  $p$-subgroup of $H$, we have $b in R C_H lr((D)) quad (mod frak(p))$ by
  @prop:normal-p-subgroup-block-idempotents, and hence
  $ b in R D quad (mod frak(p)), $
  #source(493)
  (because of the hypothesis @th:cyclic-self-centralizing-ti-sylow-hypothesis).
  Then $b equiv 1 quad (mod frak(p))$ since $R D$ is an indecomposable
  $R$-algebra and contains only one idempotent. The central character
  $overline(omega)$ of $R H$ associated with the trivial character of $H$
  therefore satisfies
  $ overline(omega)(b)=overline(omega)(1)=1, $
  and it follows that $upright(sans(B))$ is the principal block, by
  @prop:blocks-central-character-bijection.

  Another way of looking at it is to note that, for $b$ as above, the Brauer map
  $sigma:c(R H) arrow c(R D)=R D$ satisfies the condition
  $sigma(b) equiv b quad (mod frak(p))$. Since $b$ belongs to the principal
  block of $R D$, the preceding formula shows that $b$ also belongs to the
  principal block of $R H$, by @cor:brauer-map-block-idempotent-fibres and
  @cor:brauer-correspondence-principal-block.
]

#lemma[
  Let $D^*$ and $D^(* G)$ denote the union of special classes in $H$ and $G$,
  respectively, associated with $D^*=D-{1}$. Then $D^*$ and $D^(* G)$ are the
  complements, in $H$ and $G$ respectively, of the $p$-sections $H_(p')$ and
  $G_(p')$.
] <lem:cyclic-ti-special-class-complements>

The proof is immediate from the definitions. The point of
@lem:cyclic-ti-special-class-complements is that the virtual characters (of $H$
or $G$) vanishing off the special classes coincide with the virtual characters
vanishing on certain $p$-sections.

#lemma[
  Let $G$ be a finite group satisfying
  @th:cyclic-self-centralizing-ti-sylow-hypothesis, and let $xi$ be a class
  function on $G$ vanishing off $D^(* G)$. Then $xi=xi_(upright(sans(B))_1)$,
  that is, $xi$ is a linear combination of irreducible characters in the
  principal block.
] <lem:special-class-functions-principal-block>

#proof[
  Since $xi$ vanishes off $D^(* G)$, it vanishes on the $p$-section $G_(p')$, by
  @lem:cyclic-ti-special-class-complements. By
  @eq:restricted-character-block-components we have
  $ xi=sum xi_(upright(sans(B))_i), $
  and each $xi_(upright(sans(B))_i)$ vanishes off $D^(* G)$ by
  @th:p-section-vanishing-blockwise. Let $upright(sans(B))_i$ be a nonprincipal
  $p$-block of $G$, and suppose $xi_(upright(sans(B))_i) lr((x)) != 0$ for
  $x in D^*$. Then by the first version of Brauer's Second Main
  Theorem~@th:brauer-second-main-first-form, we have
  $
    xi_(upright(sans(B))_i) lr((x))=
    sum_((upright(sans(B))'_j)^G=upright(sans(B))_i)
    (xi |_H)_(upright(sans(B))'_j) lr((x)) != 0
  $
  where the sum is taken over blocks ${upright(sans(B))'_j}$ of $H$ which
  correspond to $upright(sans(B))_i$. But this is impossible by
  Lemma~@lem:cyclic-ti-sylow-normalizer-single-block, since $H$ has only one
  block, and that block is the Brauer correspondent of the principal block of
  $G$. Thus $xi_(upright(sans(B))_i)=0$ if $upright(sans(B))_i$ is not the
  principal block, as required.
]

#corollary[
  Let $zeta in op("Irr") G$, and assume $(zeta,psi^G) != 0$ for some class
  function $psi$ on $H$ vanishing off $D^*$. Then $zeta in upright(sans(B))_1$.
] <cor:special-class-induction-principal-block>

#proof[
  If $psi$ vanishes off $D^*$, then $psi^G$ vanishes off $D^(* G)$. Then
  $zeta in upright(sans(B))_1$ for any irreducible character $zeta$ satisfying
  $(zeta,psi^G) != 0$, by the preceding result.
]

#source(494)
#proof(head: emph[Proof of Theorem~@th:cyclic-ti-sylow-principal-block.])[
  First consider the characters ${1,zeta_1,...,zeta_n,theta_1,...,theta_f}$.
  These all occur with nonzero multiplicities in the virtual characters
  $Gamma_i$ or $lambda_i^G=(psi_i-psi_n)^G$ for some $i$, and hence belong to
  the principal block by the preceding corollary, using the fact that $Gamma_i$
  and $(psi_i-psi_n)^G$ vanish off $D^(* G)$. The remaining irreducible
  characters ${chi_j}$ all have the property that
  $chi_j lr((1)) equiv 0 quad (mod abs(D))$ by
  @th:cyclic-ti-sylow-character-values@case:cyclic-ti-character-degrees. Since
  $abs(D)=abs(G)_p$, each character $chi_j$ belongs to a block of defect zero,
  and is not in $upright(sans(B))_1$. This completes the proof.
]

#heading(level: 3)[
  Applications to the Classification of Transitive Permutation Groups of Degree
  $p$
] <ss:prime-degree-permutation-groups>

The study of transitive permutation groups on a set $Omega$ of $p$ elements, for
a prime $p$, has a long history. We shall present a few theorems on the subject,
which make use of the results obtained in §~@ss:principal-block-orthogonality.
For historical remarks and additional results, see Brauer @bib:Brauer1943 and
Feit @bib:Feit1982, VIII. In what follows, it is assumed that a _permutation
group_ $G$ on a set $Omega$ acts faithfully, so no element $g != 1$ fixes all
elements of $Omega$.

#proposition[
  Let $G$ be a transitive permutation group on a set $Omega$, with
  $abs(Omega)=p$ for some odd prime $p$, and let $D$ be a Sylow $p$-subgroup of
  $G$. Then $abs(D)=p$, $C_G lr((D))=D$, and $D^*$ is a T.I. set.
] <prop:prime-degree-cyclic-ti-sylow>

#proof[
  Let $H$ be the stabilizer of a point in $Omega$. Then $G slash H
  tilde.equiv Omega$ as $G$-sets, so $abs(G ":" H)=p$. On the other hand, $H$ is
  a faithful permutation group on a set of $p-1$ elements, so $abs(H)$ divides
  $(p-1)!$. Thus if $D$ is a Sylow $p$-subgroup, we have $abs(D)=p$. Now
  identify $G$ with a subgroup of the symmetric group $S_p$ on $p$ letters. Then
  $D$ is generated by a $p$-cycle, and an easy calculation shows that
  $C_G lr((D))=D$. The last statement is clear since $abs(D)=p$.
]

#remark[
  By the preceding result, any group $G$ satisfying the hypothesis of
  @prop:prime-degree-cyclic-ti-sylow also satisfies
  @th:cyclic-self-centralizing-ti-sylow-hypothesis. When $n >= 2$, the results
  of §~@ss:principal-block-orthogonality can be applied to the characters of
  $G$.
] <rem:prime-degree-principal-block-applicability>

#proposition[
  Let $G$ be a transitive permutation group on a set $Omega$ of $p$ elements,
  for a prime $p$, and assume that $abs(N_G lr((D)))=2p$. Then either $D ⊴ G$ or
  the action of $G$ on $Omega$ is $2$-transitive.
] <prop:prime-degree-dihedral-normalizer-doubly-transitive>

#remark[
  The conclusion of @prop:prime-degree-dihedral-normalizer-doubly-transitive
  holds without the assumption that $abs(N_G lr((D)))=2p$ (Burnside). We prove
  here only the special case, as an introduction to our main theorem
  @th:ito-prime-degree-sharp-three-transitivity in which the same hypothesis is
  used.
] <rem:burnside-prime-degree-dichotomy>

#proof(head: emph[Proof of
  @prop:prime-degree-dihedral-normalizer-doubly-transitive.])[
  We may assume $p>3$. From §~@ss:principal-block-orthogonality, we have
  $ op("Irr") G={1,zeta_1,...,zeta_n;theta;chi_1,...,chi_h}, $
  where there is only one nonexceptional character $theta$, since $e=2$ in this
  case. Let
  #source(495)
  $psi$ be the permutation character arising from the action of $G$ on $Omega$.
  Then $psi(1)=p$, and it is sufficient to prove that $psi=1_G+chi$ for some
  nontrivial $chi in op("Irr") G$ (by
  Exercise~@i:exc:doubly-transitive-character) or that $D ⊴ G$. From the
  information about degrees of characters, summarized in
  @th:cyclic-ti-sylow-character-values, none of the characters, $chi_i$,
  $1 <= i <= h$, can occur in $psi$. Since $theta(1) equiv plus.minus 1
  quad (mod p)$, $(theta,psi)>0$ implies that either $psi=1+theta$, or
  $theta(1)=1$. As we shall see, the latter case occurs only if $D ⊴ G$. Since
  $e=2$, we have $zeta_i lr((1)) equiv plus.minus 2 quad (mod p)$, from the
  proof of Theorem~@i:th:green-cyclic-sylow-character-values(i). We next prove:
]

#lemma[
  Keep the hypotheses of
  @prop:prime-degree-dihedral-normalizer-doubly-transitive. Then the irreducible
  characters ${zeta_1,...,zeta_n}$ are algebraic conjugates of one another (see
  Exercise~@i:exc:galois-conjugate-characters).
] <lem:prime-degree-exceptional-galois-conjugacy>

#proof[
  Since $abs(D)=p$, the nontrivial characters ${lambda_i}$ of $D$ are
  algebraically conjugate. It follows that the induced characters
  $psi_i=lambda_i^H$ are also algebraically conjugate, by the formula for
  induced characters. By
  @th:cyclic-ti-sylow-character-values@case:cyclic-ti-character-special-values
  we have
  $
    zeta_i |_(D^*)=epsilon psi_i |_(D^*) quad "for" 1 <= i <= n,
    quad "and" epsilon=plus.minus 1.
  $
  If $sigma$ is a field automorphism such that $sigma psi_i=psi_j$, then the
  preceding formula implies that $sigma zeta_i=zeta_j$ (since the exceptional
  characters ${zeta_i}$ take constant values on the $p'$-classes, by
  @th:cyclic-ti-sylow-character-values@case:cyclic-ti-character-regular-values).
]

#proof(head: none)[
  Let us return to the proof of
  @prop:prime-degree-dihedral-normalizer-doubly-transitive. If $(psi,zeta_i)>0$
  for some $i$, then $(psi,sigma zeta_i)>0$ for all field automorphisms $sigma$,
  since $psi$ is rational valued. Then $(psi,sum_(i=1)^n zeta_i)>0$. Since
  $n=1/2(p-1)$ and $zeta_i lr((1)) equiv plus.minus 2 quad (mod p)$, this is
  impossible unless $zeta_i lr((1))=2$ for all $i$. By
  @th:cyclic-ti-sylow-character-values
  @case:cyclic-ti-character-regular-values, we have
  $
    delta zeta_1 lr((1))=1+delta' theta(1)
    quad "where" delta,delta'=plus.minus 1.
  $
  Thus $zeta_i lr((1))=2$ only if $theta(1)=1$. In that case, $theta(x)=1$ for
  all $x in D$ by @i:prop:exceptional-character-values(iv), and hence $G$ has a
  proper normal subgroup containing $D$. The proof is completed by the following
  lemma.
]

#lemma[
  Keep the hypotheses of
  @prop:prime-degree-dihedral-normalizer-doubly-transitive. Then either $G$ is
  simple or $D ⊴ G$.
] <lem:prime-degree-dihedral-normalizer-simple-or-normal>

#proof[
  If $G$ is simple there is nothing to prove. Otherwise, we first prove that if
  $N$ is a nontrivial proper normal subgroup, then $N >= D$. To see this, we
  first note that all $N$-orbits $N alpha$, $alpha in Omega$, have the same size
  since $g(N alpha)=(g N g^(-1))g alpha=N(g alpha)$ and $G$ acts transitively.
  Since $abs(Omega)=p$, $N$ is either transitive on $Omega$ or
  $N <= G_alpha=op("Stab")_G alpha$ for some $alpha in Omega$. In the latter
  case we obtain $N <= inter.big_(alpha in Omega) G_alpha$, contrary to the
  assumption that $G$ acts faithfully on $Omega$. Thus $N$ acts transitively,
  and it follows that $G=G_alpha N$ for $alpha in Omega$. Then
  $p divides.not abs(G_alpha)$ since $G_alpha$ cannot contain a $p$-cycle, so
  $p divides abs(N)$, and $D <= N$, proving the first assertion.

  Now let $N$ be a minimal nontrivial proper normal subgroup. Then $D <= N$ by
  the previous discussion, and we shall prove that $G=N dot N_G lr((D))$ by what
  is called the _Frattini argument_, as follows. Let $g in G$. Then
  $attach(D, tl: g) <= N$ since $N ⊴ G$, so $attach(D, tl: g)=attach(D, tl: x)$
  for some $x in N$ since $D$ is a Sylow subgroup of $N$. Thus
  $x^(-1)g in N_G lr((D))$, as required.

  #source(496)
  We then note that the centralizer and normalizer of $D$ in $N$ both coincide
  with $D$, since $G != N$ and $abs(N_G lr((D)):D)=2$. Then $N$ has a _normal
  $p$-complement_ $L$ by Burnside's Theorem~@i:th:burnside-normal-p-complement.
  By the minimality of $N$, we obtain $L=1$, $N=D$, and $D ⊴ G$, completing the
  proof.
]

Before stating the main result of this subsection, we recall some properties of
multiply transitive permutation groups.

Let $G$ be a permutation group on a finite set $Omega$. For $alpha in Omega$, we
set $G_alpha=op("Stab")_G alpha$, and
$
  G_({alpha_1,...,alpha_k})=G_(alpha_1) inter dots inter G_(alpha_k)
  quad "for" alpha_i in Omega, quad 1 <= i <= k.
$
The group $G$ is called _$k$-transitive_ on $Omega$ for some integer $k >= 1$ if
$G$ acts transitively on the ordered $k$-tuples of distinct elements from
$Omega$, and _sharply $k$-transitive_ if it is $k$-transitive and
$G_({alpha_1,...,alpha_k})=1$ for one (and hence every) $k$-tuple
$(alpha_1,...,alpha_k)$ from $Omega$. Note that each sharply $2$-transitive
permutation group of degree greater than $2$ is a Frobenius group, by
@i:cor:fixed-point-free-permutation-kernel.

Our main result is:

#theorem(title: [Ito @bib:Ito1960])[
  Let $G$ be a nonsolvable $2$-transitive permutation group on a set $Omega$ of
  $p$ elements for some prime $p$. Let $D$ be a Sylow $p$-subgroup, and assume
  that $abs(N_G lr((D)))=2p$. Then $p=1+2^l$ for some integer $l$, and $G$ is
  sharply $3$-transitive on $Omega$.
] <th:ito-prime-degree-sharp-three-transitivity>
#idx("Ito's Theorem", target: [@th:ito-prime-degree-sharp-three-transitivity])

#remarks(numbered: false)[
  The simple sharply $3$-transitive groups were classified by Zassenhaus
  @bib:Zassenhaus1936 (see also Huppert–Blackburn @bib:Huppert1982). Using
  Zassenhaus's result combined with Ito's
  Theorem~@th:ito-prime-degree-sharp-three-transitivity, it follows that if $G$
  is a simple group satisfying the hypotheses of
  @th:ito-prime-degree-sharp-three-transitivity, then
  $G tilde.equiv op("SL")_2 lr((FF_(2^l)))$ for some $l>1$. Using the
  classification of finite simple groups, all nonsolvable $2$-transitive
  permutation groups are known, including of course those of prime degree (see
  Feit @bib:Feit1980).
] <rem:ito-theorem-classification-context>

We are now ready to begin the proof of Ito's
Theorem~@th:ito-prime-degree-sharp-three-transitivity. As in the case of
@prop:prime-degree-dihedral-normalizer-doubly-transitive, we may assume that
$p>3$.

#proof(head: none)[
  #case-list(
    numbering: "Step 1.",
    [#case[
      We first prove that $G$ is simple. If not, then $D ⊴ G$ by
      @lem:prime-degree-dihedral-normalizer-simple-or-normal, and it follows
      that $G$ is solvable, contrary to assumption.
    ] <case:ito-simplicity>],
    [#case[
      We next set up an application of character theory. By
      Theorem~@th:cyclic-ti-sylow-principal-block, the principal
      block#footnote[The theory of blocks is not required for the proof of Ito's
        Theorem beyond the organization it provides for the characters of
        $G$.] <fn:ito-block-organization>
      of $G$ is given by
      $ upright(sans(B))_1={1_G,zeta_1,...,zeta_n,theta}, $
      noting as before that there is only one nonexceptional character $theta$
      since $e=2$.
      #source(497)
      Letting $psi$ denote the permutation character on $Omega$, we have
      $ psi=1+theta, quad theta(1)=p-1, $
      using the proof of
      @prop:prime-degree-dihedral-normalizer-doubly-transitive.
    ] <case:ito-principal-block-character-setup>],
    [#case[
      We shall derive some additional properties of the characters ${zeta_i}$
      and $theta$. From @prop:prime-degree-cyclic-ti-sylow we know that
      $G_alpha$ consists of $p$-regular elements. Therefore, by
      @th:cyclic-ti-sylow-character-values
      @case:cyclic-ti-character-regular-values, we have
      $
        zeta_i |_(G_alpha)=zeta_j |_(G_alpha) quad "for all"
        i,j, 1 <= i,j <= n,
      $
      and for some constants $delta,delta'=plus.minus 1$, which are independent
      of $x in G_(p')$,
      $ delta zeta_1 |_(G_alpha)=1_(G_alpha)+delta' theta |_(G_alpha). $
      Since $theta(1)=p-1$, we have $delta' != 1$, otherwise
      $p divides zeta_1 lr((1))$ which is impossible. Therefore $delta'=-1$, so
      $ delta zeta_1 lr((1))=2-p<0, $
      hence $delta=-1$, and
      $ zeta_1 lr((1))=dots=zeta_n lr((1))=p-2. $
    ] <case:ito-exceptional-degrees-and-restrictions>],
    [#case[
      We shall prove that $zeta_i |_(G_alpha)$ is irreducible, for
      $1 <= i <= n$. Suppose not, and let
      $
        zeta_i |_(G_alpha)=a_1 xi_1+dots+a_r xi_r,
        quad xi_i in op("Irr") G_alpha,
      $
      with $r>0$, $a_i>0$ for all $i$, and $xi_i != xi_j$ if $i != j$. Since
      $op("deg") zeta_i=p-2$ by @case:ito-exceptional-degrees-and-restrictions,
      we may assume $op("deg") xi_1 < 1/2(p-2)$. Then
      $a_1=(zeta_i |_(G_alpha),xi_1)=(zeta_i,xi_1^G)$ by reciprocity, and
      $xi_1 != 1_(G_alpha)$ since $(1_(G_alpha))^G=psi$ and $(zeta_i,psi)=0$ by
      @case:ito-principal-block-character-setup. By
      @case:ito-exceptional-degrees-and-restrictions, we have
      $theta |_(G_alpha)=1_(G_alpha)+zeta_i |_(G_alpha)$, and hence
      $ a_1=(zeta_i |_(G_alpha),xi_1)=(theta |_(G_alpha),xi_1), $
      using the fact that $(1_(G_alpha),xi_1)=0$. We also have
      $a_1=(zeta_i |_(G_alpha),xi_1)=(zeta_j |_(G_alpha),xi_1)$ using
      @case:ito-exceptional-degrees-and-restrictions. Therefore
      $
        xi_1^G lr((1)) >= a_1(theta(1)+sum_(i=1)^n zeta_i lr((1)))
        =a_1(p-1+1/2(p-1)(p-2))\
        >= 1/2 a_1(p-1)(p).
      $
      On the other hand,
      $ xi_1^G lr((1))=p xi_1 lr((1)) <= 1/2 p(p-2), $
      #source(498)
      which is a contradiction. We have proved that $zeta_i |_(G_alpha)$ is
      irreducible, as required.
    ] <case:ito-irreducible-point-stabilizer-restrictions>],
    [#case[
      We have proved that
      $ theta |_(G_alpha)=1+zeta_i |_(G_alpha), quad "for" 1 <= i <= n, $
      and $zeta_i |_(G_alpha)$ is irreducible. Since $theta |_(G_alpha)$ is the
      permutation character of $G_alpha$ on $Omega-{alpha}$, it follows that
      $theta |_(G_alpha)$ is $2$-transitive on $Omega-{alpha}$ and hence $G$ is
      $3$-transitive on $Omega$. From this fact we also know that
      $p(p-1)(p-2) divides abs(G)$.
    ] <case:ito-three-transitivity>],
    [#case[
      We next prove that $G$ is sharply $3$-transitive, that is,
      $G_(alpha beta gamma)=1$ for $alpha,beta,gamma$ distinct in $Omega$. For
      this purpose we apply Exercise~@exc:three-transitive-exterior-character,
      using the fact that $G$ is $3$-transitive by @case:ito-three-transitivity.
      Let $x in G_(alpha beta gamma)$. We shall prove that $x in ker psi$, where
      $psi$ is the permutation character of $G$ on $Omega$. We can then conclude
      that $x=1$, since $G$ is simple, by @case:ito-simplicity. Let $theta_a$ be
      the antisymmetric part of $theta^2$. By
      Exercise~@exc:three-transitive-exterior-character,
      $ theta_a=1/2 theta(theta-1)-beta. $
      In particular, $theta_a lr((1))=1/2(p-1)(p-2)$, so
      $p divides.not theta_a lr((1))$, and for some $xi in op("Irr") G$, we have
      $ (xi,theta_a) != 0 quad "and" quad p divides.not xi(1). $
      Then by Theorem~@th:cyclic-ti-sylow-principal-block
      @case:cyclic-ti-principal-block-characters, $xi$ belongs to the principal
      block $upright(sans(B))_1$ of $G$, and $xi != 1_G,theta$ by
      Exercise~@exc:three-transitive-exterior-character
      @case:three-transitive-exterior-orthogonality. Then $xi=zeta_j$ for some
      $j$. By Lemma~@lem:prime-degree-exceptional-galois-conjugacy, it follows
      that $(sum_(j=1)^n zeta_j,theta_a)>0$, since $theta_a$ is a rational
      character. By @case:ito-exceptional-degrees-and-restrictions,
      $zeta_j lr((1))=p-2$ for each $j$, and by comparing degrees, we obtain
      $ theta_a=sum_(j=1)^n zeta_j, quad n=1/2(p-1). $
      Now let $x in G_(alpha beta gamma)$. Then $psi(x)>=3$. Since
      $x in G_alpha$, $x in G_(p')$,
      $
        theta_a lr((x))=sum zeta_j lr((x))=1/2(p-1)(theta(x)-1)
        =1/2 theta(x)(theta(x)-1)-beta(x),
      $
      using @case:ito-exceptional-degrees-and-restrictions. Then
      $ beta(x)=1/2(theta(x)-1)(theta(x)-(p-1))>=0 $
      and $theta(x)>=2$ since $x in G_alpha$. Therefore $theta(x)>=p-1$,
      $psi(x)=p$, and $x in ker psi={1}$, completing the proof.
    ] <case:ito-sharp-three-transitivity>],
    [#case[
      By @case:ito-sharp-three-transitivity, we have $abs(G)=p(p-1)(p-2)$ and
      $abs(G_alpha)=(p-1)(p-2)$. It remains to prove that $p-1=2^k$ for some
      $k$. Since $G_(alpha beta gamma)=1$, no nonidentity element of $G_alpha$
      fixes more than one element of $Omega-{alpha}$. Therefore, by
      Corollary~@i:cor:fixed-point-free-permutation-kernel, $G_alpha$ is a
      Frobenius group, with Frobenius kernel $N$ and complement $H$, and we have
      $Omega-{alpha} tilde.equiv G_alpha slash H$
      #source(499)
      as $G_alpha$-sets. Then $abs(H)=p-2$, $abs(N)=p-1$, and
      $C_(G_alpha) lr((x)) <= N$ for all $x in N-{1}$, by
      @i:prop:frobenius-group-characters. Since $abs(N)=p-1$ is even, $N$
      contains an involution $v$, and we have
      $ abs(G_alpha ":" C_(G_alpha) lr((v))) >= abs(G_alpha ":" N)=p-2. $
      It follows that the conjugacy class of $v$ coincides with $N-{1}$.
      Therefore $N$ is an elementary abelian $2$-group, and $p-1=2^k$ as
      required. This completes the proof of the theorem.
    ] <case:ito-fermat-prime-degree>],
  )
]

#exercises-heading

#exercise[
  Let $G$ be a $2$-transitive permutation group on a set $Omega$, and let
  $psi=1_G+theta$ be the permutation character. Then
  $ psi^2=psi or psi+psi and psi. $
  Since $psi=(1_(G_alpha))^G$, we can compute $psi or psi$ and $psi and psi$
  using Theorem~@i:th:mackey-induced-linear-character-squares. Prove that
  $ psi or psi=psi+mu_+, quad psi and psi=mu_-, $
  where $mu_+$ and $mu_-$ are defined as follows. Since $G$ is $2$-transitive,
  choose $beta != alpha$ and $v in G$ interchanging $alpha$ and $beta$. Then
  $G=G_alpha union.dot G_alpha v G_alpha$, and, with this choice,
  $v^2 in G_alpha inter attach(G_alpha, tl: v)$ (see
  §~@i:ss:symmetric-skew-squares-induced-modules). Let
  $N=chevron.l v,G_alpha inter attach(G_alpha, tl: v) chevron.r$. Then
  $mu_+=(1_N)^G$ while $mu_-=(epsilon_N)^G$, where $epsilon_N$ is the extension
  to $N$ of the unique nontrivial character of
  $N slash (G_alpha inter attach(G_alpha, tl: v))$.
] <exc:doubly-transitive-symmetric-exterior-characters>

#exercise[
  Keep the notation of
  Exercise~@exc:doubly-transitive-symmetric-exterior-characters, and assume that
  $G$ is $3$-transitive on $Omega$. Let $psi_s=psi or psi$ and
  $psi_a=psi and psi$.
  #case-list(
    numbering: "(i)",
    [#case[
      Prove that for all $x in G$,
      $ theta_a lr((x))=1/2 theta(x)(theta(x)-1)-beta(x), $
      where $beta(x)$ is the number of transpositions in the cycle decomposition
      of $x$ on $Omega$, and $theta_a$ is the antisymmetric part of $theta^2$.

      #hint([@exc:three-transitive-exterior-character])[
        Let ${v_alpha:alpha in Omega}$ be a basis of the $CC G$-module $V$
        affording $psi$, and let $v_0=sum_(alpha in Omega) v_alpha$. Then
        $V=W plus.o chevron.l v_0 chevron.r$, where $W$ affords $theta$ and
        $v_0$ affords $1_G$. Moreover,
        $V and V=W and W plus.o (W and chevron.l v_0 chevron.r)$, and
        $W and chevron.l v_0 chevron.r$ affords $theta$. Thus it is sufficient
        to prove that
        $ psi_a lr((x))=1/2 psi(x)(psi(x)-1)-beta(x), quad "for" x in G. $
        This is shown as follows. We have
        $
          V and V=plus.big V_(alpha beta) quad "where"
          V_(alpha beta)=chevron.l v_alpha times.o v_beta
          -v_beta times.o v_alpha chevron.r, quad alpha != beta.
        $
        The sum is over the unordered pairs ${alpha,beta}$ with $alpha != beta$.
        For $x in G$, only the invariant unordered pairs contribute to the
        trace. A pair of fixed points contributes $+1$, a $2$-cycle contributes
        $-1$, and every moved orbit of pair lines contributes $0$. Since
        $psi(x)$ is the number of fixed points of $x$, this gives the asserted
        formula for $psi_a lr((x))$.#ed-note[
          In $S_4$, $(1 2)$ interchanges $V_(1 3)$ and $V_(2 3)$; it does not
          act as $+1$ on each of these other pair lines.
        ]
      ]
    ] <case:three-transitive-exterior-value>],
    [#case[
      Let $theta_a=theta and theta$, as in
      part~@case:three-transitive-exterior-value. Prove that
      $(theta_a,1_G)=(theta_a,theta)=0$.
      #source(500)
      #hint([@exc:three-transitive-exterior-character])[
        Since $G$ is $3$-transitive on $Omega$, $G_alpha$ is $2$-transitive on
        $Omega-{alpha}$. Therefore
        $(theta |_(G_alpha),theta |_(G_alpha))_(G_alpha)
        =(theta_(G_alpha)^2,1_(G_alpha))=2$, and hence $(theta^2,psi)_G=2$. Then
        show that $theta or theta$ is the permutation character $tau$ of $G$ on
        the set of unordered pairs ${alpha,beta}_(alpha != beta)$, and that
        $(tau,psi)=(tau |_(G_alpha),1_(G_alpha))_(G_alpha)=2$. Since
        $theta^2=theta_s+theta_a$, the result follows.
      ]
    ] <case:three-transitive-exterior-orthogonality>],
  )
] <exc:three-transitive-exterior-character>
