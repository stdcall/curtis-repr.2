#import "main-defs.typ": *
#import "note-layout.typ": reference-data
#import "main-defs.typ": number-text as reference-number-text
#import "statements.typ": *
#import "diagrams/77-graphs.typ": *

== Representations of Graphs and Gabriel's Theorem
<sec:graph-representations-gabriel-theorem>

=== Representations of Graphs and Coxeter Functors
<ss:graph-representations-coxeter-functors>

Throughout this section, $Gamma$ denotes a _finite, connected, oriented graph_.
We denote the set of vertices of $Gamma$ by ${alpha}$, and let ${e}$ denote the
set of edges. We shall write $e=(alpha,beta)$ to indicate that $e$ goes from
$alpha$ to $beta$. At this point, we do not exclude the possibility of more than
one edge having the same pair of vertices, or of edges whose vertices coincide
(called loops). We shall denote by $|Gamma|$ the unoriented graph defined by
$Gamma$, with the same vertices and edges.

#definitions[
  Let $K$ be an algebraically closed field, and let $Gamma$ be a finite
  #source(807)
  connected oriented graph. The #idx("Representations of graphs")_category_
  $cal(L)(Gamma)$ of _$K$-representations_ of $Gamma$ is defined as follows. An
  _object_ $(V,f) in cal(L)(Gamma)$ consists of a family ${V_alpha}$ of f.d.
  $K$-spaces, indexed by the set of vertices ${alpha}$ of $Gamma$, and a family
  of $K$-linear maps $f_e:V_alpha arrow V_beta$, indexed by the set of edges
  ${e=(alpha,beta)}$ of $Gamma$. A _morphism_ $phi:(V,f) arrow (W,g)$ between
  two objects in $cal(L)(Gamma)$ consists of a family of $K$-linear maps
  $phi_alpha:V_alpha arrow W_alpha$, one for each vertex $alpha$, such that for
  each edge $e=(alpha,beta)$, the diagram commutes:
  #representation-square()
  A morphism $phi:(V,f) arrow (W,g)$ is called an _isomorphism_ if each map
  $phi_alpha:V_alpha arrow W_alpha$ is an isomorphism. The set of morphisms from
  $(V,f)$ to $(W,g)$ is denoted by $"Hom"((V,f), (W,g))$, or by $"End"(V, f)$,
  in case $(W,g)=(V,f)$. For each object $(V,f) in cal(L)(Gamma)$, the
  _dimension_ $dim(V, f)$ is defined by the $n$-tuple
  $ dim(V, f)=(dim_K V_alpha) in ZZ^n, $
  where $n$ is the cardinal number of the vertex set ${alpha}$.
]<def:graph-representation-category>

The terminology of categories was introduced in §~@i:ss:categories-functors, for
modules over rings, and is used here with appropriate modifications.

The _direct sum_ $(V,f) plus.o (W,g)$ of two objects in $cal(L)(Gamma)$ is
defined in the obvious way. The _trivial object_, whose $K$-spaces and maps are
all zero, is denoted by $0$. An object is _indecomposable_ if it is not the
trivial object, and is not isomorphic to a direct sum of nontrivial objects.

#proposition[
  Every object in $cal(L)(Gamma)$ is isomorphic to a direct sum of a finite set
  of indecomposable objects, and these are uniquely determined up to isomorphism
  and order of occurrence.
]<prop:graph-representation-krull-schmidt>

The proof is left as an exercise. It is essentially the same as the proof of the
K-S-A Theorem @i:th:krull-schmidt-azumaya. The key step is the observation that,
for each object $(V,f) in cal(L)(Gamma)$, $"End"(V, f)$ is a local $K$-algebra
if and only if $(V,f)$ is an indecomposable object (see §~@i:ss:idempotents).

#examples(numbered: false)[
  #case-list(
    numbering: "(i)",
    [#case[
      Weierstrass raised the problem of classifying pairs of linear maps
      $f,g:V_1 arrow V_2$, up to automorphisms of the vector spaces $V_1,V_2$.
      The problem remained open for more than $20$ years, and was solved by
      Kronecker (see the Kronecker–Weierstrass Theorem
      @i:th:kronecker-weierstrass-matrix-pairs). It involves the category
      $cal(L)(Gamma)$, for the graph #kronecker-graph().
    ]<case:kronecker-pair-graph>],
    [#case[
      Gelfand–Ponomarev (1970) considered the problem of classifying
      inclusion-ordered families of subspaces ${V_i}$ of a f.d. $K$-space $V$,
      up to
      #source(808)
      automorphisms of $V$. For example, in the case of two subspaces
      ${V_1,V_2}$, the problem is solved using the arithmetic invariants
      $(dim V_1,dim V_2,dim V_1 inter V_2)$. The solution for three subspaces is
      a special case of Gabriel's Theorem (see
      §~@ss:gabriel-finite-representation-type). These problems, in general,
      involve categories $cal(L)(Gamma)$ for the graphs
      #subspace-graphs()
    ]<case:subspace-configuration-graphs>],
    [#case[
      The classification of linear maps $f in "End"_K V$, up to automorphisms of
      $V$, involves the category $cal(L)(Gamma)$, for the graph #loop-graph().
      The indecomposable objects in $cal(L)(Gamma)$, in this case, are described
      by the Jordan canonical forms of the endomorphisms ${f}$.
    ]<case:jordan-endomorphism-loop-graph>],
  )
]<exm:graph-representation-classification-problems>

Our objective, in view of @prop:graph-representation-krull-schmidt, is the
construction of the indecomposable objects in $cal(L)(Gamma)$. We shall present
a solution of this problem in §~@ss:gabriel-finite-representation-type, for
categories $cal(L)(Gamma)$ of finite type (that is, having at most a finite
number of isomorphism classes of indecomposable objects).

Besides the indecomposable objects, we also need to consider the _simple
objects_ ${L_alpha}$ in $cal(L)(Gamma)$. For each vertex $alpha$, there exists a
unique simple object $L_alpha$, such that $L_alpha$ is the one-dimensional space
$K$, the vector spaces associated with other vertices $gamma≠alpha$ are zero,
and all maps are zero.

Following Bernstein–Gelfand–Ponomarev~@bib:Bernstein1973, we consider certain
changes in orientation of the graphs, and functors between the representation
categories resulting from them. We recall, from §~@i:ss:categories-functors,
that a _covariant functor_ $F$ from a category $cal(C)$ to a category $cal(C)'$
assigns to each object $C$ of $cal(C)$ an object $C'=F C$ of $cal(C)'$.
Moreover, $F$ assigns to each morphism $phi:C arrow D$ in $cal(C)$, a morphism
$F phi:F C arrow F D$ in $cal(C)'$, such that $F$ preserves identity maps and
composition of morphisms.

#definition[
  Let $Gamma$ be an oriented connected graph, and $alpha$ a vertex of $Gamma$.
  Define $sigma_alpha Gamma$ to be the oriented graph with the same set of
  vertices and unoriented edges as $Gamma$, which is obtained from $Gamma$ by
  reversing the orientation of all edges starting or ending at $alpha$, and
  leaving the rest of the graph unchanged.
]<def:graph-vertex-orientation-reversal>

#definition[
  A vertex $beta$ of $Gamma$ is called a _sink_ (or $+$-_accessible vertex_) if
  each edge through $beta$ ends at $beta$ (in particular there are no loops at
  $beta$). For each sink $beta$, we shall define a covariant functor
  $F_beta^+:cal(L)(Gamma) arrow cal(L)(sigma_beta Gamma)$, as follows. We first
  define an object $F_beta^+ lr((V,f))=(W,g)$ in $cal(L)(sigma_beta Gamma)$, for
  each object $(V,f)$ in $cal(L)(Gamma)$, where
  $ W_gamma=V_gamma, quad "for each vertex" gamma≠beta. $
  In order to define $W_beta$, let $e_1=(alpha_1,beta),dots,e_k=(alpha_k,beta)$
  be the edges ending at $beta$, and
  #source(809)
  set
  $
    W_beta={sum_(i=1)^k v_i in plus.o.big_(i=1)^k V_(alpha_i):
      sum_(i=1)^k f_(e_i) lr((v_i))=0}.
  $
  In other words, $W_beta=ker h$, where $h:plus.o.big V_(alpha_i) arrow V_beta$
  is the map given by $h=plus.o.big f_(e_i)$. The maps ${g_e}$ associated with
  $W$ are defined by setting
  $ g_e=f_e quad "if" e≠e_i quad "for" 1≤i≤k, $
  and
  $
    g_(e_i)=pi_i compose i_beta, quad "for" 1≤i≤k,
    quad "and" e_i=(alpha_i,beta),
  $
  where $i_beta:W_beta arrow plus.o.big_(i=1)^k V_(alpha_i)$ is the natural
  embedding, and $pi_i:plus.o.big V_(alpha_i) arrow V_(alpha_i)$ is the
  projection on the $i$-th summand.

  To complete the definition of the functor $F_beta^+$, we also have to define a
  morphism
  $
    F_beta^+ phi:F_beta^+ lr((V,f)) arrow F_beta^+ lr((V',f'))
    quad "in" cal(L)(sigma_beta Gamma)
  $
  for each morphism $phi:(V,f) arrow (V',f')$ in $cal(L)(Gamma)$. For each
  vertex $gamma≠beta$, we set
  $ (F_beta^+ phi)_gamma=phi_gamma. $
  Letting $(W,g)=F_beta^+ lr((V,f))$ and $(W',g')=F_beta^+ lr((V',f'))$, we
  define a map
  $ (F_beta^+ phi)_beta:W_beta arrow W'_beta $
  which takes $sum v_i in W_beta subset.eq plus.o.big_(i=1)^k V_(alpha_i)$ to
  $sum phi_(alpha_i) v_i in W'_beta subset.eq
  plus.o.big_(i=1)^k V'_(alpha_i)$.

  In order to check that $F_beta^+ phi$ is indeed a morphism in the category
  $cal(L)(sigma_beta Gamma)$, it is enough to show that $(F_beta^+ phi)_beta$
  takes $ker h arrow ker h'$, where $h$ and $h'$ are the maps defined in
  @def:graph-sink-coxeter-functor. Since $phi$ is a morphism in $cal(L)(Gamma)$,
  we have
  $
    phi_beta f_(e_i)=f'_(e_i) phi_(alpha_i)
    quad "for each edge" e_i=(alpha_i,beta) quad "in" Gamma.
  $
  Then, for each element $sum v_i in ker h$, we have
  $
    h'(sum phi_(alpha_i) v_i)=sum f'_(e_i) phi_(alpha_i) v_i
    =sum phi_beta f_(e_i) v_i=phi_beta lr((h(sum v_i)))=0,
  $
  as required.
]<def:graph-sink-coxeter-functor>

We next have:

#definition[
  A vertex $alpha$ of $Gamma$ is called a _source_ (or $-$-_accessible vertex_)
  if all
  #source(810)
  edges having $alpha$ as a vertex start at $alpha$. For each source $alpha$, we
  shall define a covariant functor
  $F_alpha^-:cal(L)(Gamma) arrow cal(L)(sigma_alpha Gamma)$. Let $(V,f)$ be an
  object in $cal(L)(Gamma)$. The corresponding object
  $F_alpha^- lr((V,f))=(W,g)$ in $cal(L)(sigma_alpha Gamma)$ is obtained by
  setting
  $ W_gamma=V_gamma quad "for all vertices" gamma≠alpha, quad "and" $
  $ g_e=f_e quad "for all edges" e "not having" alpha "as a vertex". $
  Now let $e_1=(alpha,beta_1),dots,e_m=(alpha,beta_m)$ be the edges having
  $alpha$ as a vertex, and set
  $ W_alpha=lr((plus.o.big_(i=1)^m V_(beta_i))) slash im tilde(h), $
  where
  $ tilde(h):V_alpha arrow plus.o.big_(i=1)^m V_(beta_i) $
  is the map defined by
  $
    v arrow tilde(h)(v)=sum f_(e_i) lr((v)) in
    plus.o.big_(i=1)^m V_(beta_i).
  $
  The maps $g_(e_i):W_(beta_i) arrow W_alpha$, $1≤i≤m$, are defined by
  $ g_(e_i)=nu compose j_(beta_i), $
  where $j_(beta_i):W_(beta_i) arrow plus.o.big_(j=1)^m W_(beta_j)$ is the
  natural embedding, and $nu:plus.o.big_(j=1)^m W_(beta_j) arrow
  lr((plus.o.big_(j=1)^m W_(beta_j))) slash im tilde(h)$ is the quotient map
  with kernel $im tilde(h)$.

  The morphism $F_alpha^- psi:(W,g) arrow (W',g')$ in
  $cal(L)(sigma_alpha Gamma)$, where $(W,g)=F_alpha^- lr((V,f))$,
  $(W',g')=F_alpha^- lr((V',f'))$, and $psi:(V,f) arrow (V',f')$ is a morphism
  in $cal(L)(Gamma)$, is defined as follows. We set
  $ (F_alpha^- psi)_gamma=psi_gamma quad "for all vertices" gamma≠alpha, $
  and define $(F_alpha^- psi)_alpha:W_alpha arrow W'_alpha$ to be the map
  $ nu lr((sum_(i=1)^m v_i)) arrow nu' lr((sum psi_(beta_i) v_i)), $
  where $nu$ and $nu'$ are quotient maps as above, and $v_i in V_(beta_i)$.

  We leave it to the reader to check that $F_alpha^-$ is a covariant functor
  from $cal(L)(Gamma) arrow cal(L)(sigma_alpha Gamma)$.
]<def:graph-source-coxeter-functor>

The functors ${F_beta^+}$ and ${F_alpha^-}$ defined in
@def:graph-sink-coxeter-functor and @def:graph-source-coxeter-functor are called
#idx("Coxeter functors")_Coxeter functors_. #nidx(
  "$F_alpha^-, F_alpha^+$",
  "Coxeter functors",
  target: [@def:graph-source-coxeter-functor],
) We shall see that they operate on the dimension vectors $dim(V, f)$ of
#source(811) objects in $cal(L)(Gamma)$ in a manner similar to the action of
reflections in a g.g.r. (see §~@sec:root-systems-reflection-groups). (In the
following discussion, $dim$ always means $dim_K$.)

#theorem[
  Let $(V,f)$ be an indecomposable object in $cal(L)(Gamma)$, for a finite
  connected oriented graph $Gamma$. Then the following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[
      Let $beta$ be a sink. Then either $(V,f)$ is isomorphic to the simple
      object $L_beta$, or we have:

      $F_beta^+ lr((V,f))$ is an indecomposable object in
      $cal(L)(sigma_beta Gamma)$,
      $ F_beta^- F_beta^+ lr((V,f)) ≅ (V,f), $
      and
      $
        dim(F_beta^+ V)_gamma=dim V_gamma
        quad "for all vertices" gamma≠beta
      $
      $ dim(F_beta^+ V)_beta=-dim V_beta+sum_(i=1)^k dim V_(alpha_i), $
      where ${(alpha_1,beta),dots,(alpha_k,beta)}$ are the edges in $Gamma$
      having $beta$ as a vertex.
    ]<case:sink-coxeter-functor-indecomposable-dimension>],
    [#case[
      Let $alpha$ be a source. Then either $(V,f) ≅ L_alpha$, or we have:

      $F_alpha^- lr((V,f))$ is an indecomposable object in
      $cal(L)(sigma_alpha Gamma)$,
      $ F_alpha^+ F_alpha^- lr((V,f)) ≅ (V,f) $
      and
      $
        dim(F_alpha^- V)_gamma=dim V_gamma
        quad "for all vertices" gamma≠alpha
      $
      $ dim(F_alpha^- V)_alpha=-dim V_alpha+sum_(i=1)^m dim V_(beta_i), $
      where ${(alpha,beta_i),1≤i≤m}$ are the edges having $alpha$ as a vertex.
    ]<case:source-coxeter-functor-indecomposable-dimension>],
  )
]<th:coxeter-functor-indecomposability-reflection>

The rest of the subsection is devoted to a proof of this theorem and a
corollary. First let $beta$ be a sink. We shall construct a morphism.
$ lambda_V^beta:F_beta^- F_beta^+ lr((V,f)) arrow (V,f), $
for each object $(V,f)$ in $cal(L)(Gamma)$. We set
$
  (lambda_V^beta)_gamma= upright("id")_(V_gamma)
  quad "for all vertices" gamma≠beta,
$
noting that $F_beta^- F_beta^+ lr((V,f))_gamma=V_gamma$ if $gamma≠beta$. The map
$ (lambda_V^beta)_beta:F_beta^- F_beta^+ lr((V,f))_beta arrow V_beta $
#source(812)
is defined as follows. From @def:graph-sink-coxeter-functor, we have
$ F_beta^+ lr((V,f))_beta=ker h, quad "where" h=plus.o.big f_(e_i), $
and ${e_i=(alpha_i,beta):1≤i≤k}$ are the edges having $beta$ as a vertex. The
maps $g_(e_i):(F_beta^+ V)_beta arrow (F_beta^+ V)_(alpha_i)=V_(alpha_i)$
associated with the object $F_beta^+ lr((V,f))$ are given by
$g_(e_i)=pi_i compose i_beta$, where
$i_beta:(F_beta^+ V)_beta arrow plus.o.big V_(alpha_i)$ is the natural
embedding, and $pi_i$ the projection upon $V_(alpha_i)$. From
@def:graph-source-coxeter-functor, we have
$ F_beta^- F_beta^+ lr((V,f))_beta=(plus.o.big V_(alpha_i)) slash im tilde(h) $
where $tilde(h)=plus.o.big g_(e_i)=plus.o.big pi_i compose i_beta$, by the
preceding remarks. We clearly have
$ im tilde(h)=ker h quad "in" plus.o.big_(i=1)^k V_(alpha_i), $
and it follows that there exists an injective $K$-linear map
$
  (lambda_V^beta)_beta:(F_beta^- F_beta^+ V)_beta
  =(plus.o.big V_(alpha_i)) slash im tilde(h)
  =(plus.o.big V_(alpha_i)) slash ker h arrow V_beta.
$
It is easily verified that the family of maps ${(lambda_V^beta)_gamma}$ is a
morphism in the category $cal(L)(Gamma)$.

Now let $alpha$ be a source. In this case, we shall construct a morphism
$ mu_V^alpha:(V,f) arrow F_alpha^+ F_alpha^- lr((V,f)), $
for each object $(V,f)$ in $cal(L)(Gamma)$. As in the previous case, the maps
${(mu_V^alpha)_gamma:gamma≠alpha}$ are all taken as identity maps. Put
$
  T=plus.o.big_(i=1)^m V_(beta_i), quad
  H=tilde(h)=plus.o.big_(i=1)^m f_(e_i):V_alpha arrow T,
$
where ${e_i=(alpha,beta_i)}$ are the edges containing $alpha$ as a vertex. Let
$Q=T slash im H$, and let $nu:T arrow Q$ be the quotient map. By
@def:graph-source-coxeter-functor, we have
$ (F_alpha^- lr((V,f)))_alpha=Q, quad g_(e_i)=nu compose j_(beta_i), $
where $j_(beta_i):V_(beta_i) arrow T$ is the natural embedding. Thus the map
$h:T arrow Q$ obtained by combining all the $g_(e_i)$ is $nu$, and
@def:graph-sink-coxeter-functor gives
$ F_alpha^+ F_alpha^- lr((V,f))_alpha=ker h=im H. $
Define $(mu_V^alpha)_alpha$ to be $H$, regarded as a surjection onto its image.
At each original edge $e_i$, the map in the target object is the restriction of
$pi_i:T arrow V_(beta_i)$ to $im H$, and $pi_i H=f_(e_i)$. Hence these
components define a morphism $mu_V^alpha$ in $cal(L)(Gamma)$. For a morphism
$psi:(V,f) arrow (V',f')$, the identity
$ H' psi_alpha=(plus.o.big psi_(beta_i)) H $
also shows that this family of morphisms is natural.
#ed-note[
  The coordinatewise cokernels in the original proof need not give the cokernel
  of the combined map. For $K arrow.l K arrow K$ with both maps identity, the
  former have total dimension $0$, whereas the latter has dimension $1$.
]

#source(813)
The next lemma summarizes the properties of the morphisms ${lambda_V^beta}$ and
${mu_V^alpha}$.

#lemma[
  Let $beta$ be a sink, and $alpha$ a source in the graph $Gamma$. Then the
  following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[The functors $F_beta^+$ and $F_alpha^-$ preserve direct sums.]
      <case:coxeter-functors-preserve-direct-sums>],
    [#case[
      The morphisms
      $
        lambda_V^beta:F_beta^- F_beta^+ lr((V,f)) arrow (V,f)
        quad "and" quad mu_V^alpha:(V,f) arrow F_alpha^+ F_alpha^- lr((V,f))
      $
      are injective and surjective, respectively, for all objects $(V,f)$ in
      $cal(L)(Gamma)$.
    ]<case:coxeter-unit-counit-monomorphism-epimorphism>],
    [#case[
      For each object $(V,f)$ in $cal(L)(Gamma)$, there exists a quotient object
      $(V,f) slash im lambda_V^beta$ in $cal(L)(Gamma)$ such that
      $((V,f) slash im lambda_V^beta)_gamma=0$ for all vertices $gamma≠beta$.
      Similarly, there exists an object $ker mu_V^alpha$ in $cal(L)(Gamma)$ such
      that $(ker mu_V^alpha)_gamma=0$ for all vertices $gamma≠alpha$.
    ]<case:coxeter-unit-counit-simple-support>],
    [#case[
      Let $(V,f)=F_beta^- lr((W,g))$, for some object $(W,g)$ in
      $cal(L)(sigma_beta Gamma)$. Then
      $lambda_V^beta:F_beta^- F_beta^+ lr((V,f)) arrow (V,f)$ is an isomorphism.
      On the other hand, if $(V,f)=F_alpha^+ lr((W,g))$ for some object $(W,g)$
      in $cal(L)(sigma_alpha Gamma)$, then
      $mu_V^alpha:(V,f) arrow F_alpha^+ F_alpha^- lr((V,f))$ is an isomorphism.
    ]<case:coxeter-unit-counit-essential-images>],
    [#case[
      For each object $(V,f)$ in $cal(L)(Gamma)$, there exist direct sum
      decompositions
      $
        (V,f) ≅ F_beta^- F_beta^+ lr((V,f))
        plus.o ((V,f) slash im lambda_V^beta)
      $
      and
      $ (V,f) ≅ ker mu_V^alpha plus.o F_alpha^+ F_alpha^- lr((V,f)). $
    ]<case:coxeter-unit-counit-split-decompositions>],
  )
]<lem:coxeter-functor-unit-counit-properties>

The proof is straightforward, in view of the preceding discussion, and is left
to the reader.

Now we can complete the proof of Theorem
@th:coxeter-functor-indecomposability-reflection. Let $(V,f)$ be an
indecomposable object in $cal(L)(Gamma)$. If $(V,f)$ is the simple object
$L_beta$, for a sink $beta$ in $Gamma$, then we obtain $F_beta^+ lr((V,f))=0$,
by the definition of the functor $F_beta^+$, while if $(V,f)=L_alpha$, at a
source $alpha$, we have $F_alpha^- lr((V,f))=0$, again by the definition of
$F_alpha^-$.

Let us assume next that $beta$ is a sink, and $(V,f)$ is indecomposable, but not
the simple object $L_beta$. Then $F_beta^+ lr((V,f))≠0$, and we shall prove it
is indecomposable and calculate its dimension. First assume that
$ F_beta^+ lr((V,f))=(W_1,g_1) plus.o (W_2,g_2) $
in $cal(L)(sigma_beta Gamma)$. Then we obtain
$
  (V,f) ≅ F_beta^- F_beta^+ lr((V,f))
  =F_beta^- lr((W_1,g_1)) plus.o F_beta^- lr((W_2,g_2))
$
by @case:coxeter-unit-counit-split-decompositions[#context {
  reference-number-text(
    "("
      + reference-data(<lem:coxeter-functor-unit-counit-properties>).text
      + reference-data(<case:coxeter-unit-counit-split-decompositions>)
        .text
        .trim(regex("[()]"))
      + ")",
  )
}] and @case:coxeter-functors-preserve-direct-sums[#context {
  reference-number-text(
    "("
      + reference-data(<lem:coxeter-functor-unit-counit-properties>).text
      + reference-data(<case:coxeter-functors-preserve-direct-sums>)
        .text
        .trim(regex("[()]"))
      + ")",
  )
}], so one of the objects $F_beta^- lr((W_i,g_i))$, $i=1,2$, is $0$. Suppose
$F_beta^- lr((W_1,g_1))=0$. By
@case:coxeter-unit-counit-essential-images[#context {
  reference-number-text(
    "("
      + reference-data(<lem:coxeter-functor-unit-counit-properties>).text
      + reference-data(<case:coxeter-unit-counit-essential-images>)
        .text
        .trim(regex("[()]"))
      + ")",
  )
}],
$
  mu_V^beta:F_beta^+ lr((V,f)) arrow
  F_beta^+ F_beta^- lr((F_beta^+ lr((V,f))))
$
#source(814)
is an isomorphism, and it follows that $(W_1,g_1)=0$, since
$F_beta^+ F_beta^- lr((W_1,g_1))=0$. Thus $F_beta^+ lr((V,f))$ is
indecomposable, and we shall calculate its dimension. We have
$
  dim F_beta^+ lr((V,f))_gamma=dim V_gamma
  quad "for all vertices" gamma≠beta.
$
Moreover, using @case:coxeter-unit-counit-split-decompositions[#context {
  reference-number-text(
    "("
      + reference-data(<lem:coxeter-functor-unit-counit-properties>).text
      + reference-data(<case:coxeter-unit-counit-split-decompositions>)
        .text
        .trim(regex("[()]"))
      + ")",
  )
}], $lambda_V^beta$ defines an isomorphism
$ (V,f) ≅ F_beta^- F_beta^+ lr((V,f)), $
and hence
$
  dim V_beta=dim lr(((plus.o.big V_(alpha_i)) slash ker h))
  =sum dim V_(alpha_i)-dim F_beta^+ lr((V,f))_beta,
$
which is the required formula for $dim F_beta^+ lr((V,f))_beta$. This completes
the proof of part~@case:sink-coxeter-functor-indecomposable-dimension of the
theorem. The proof of part~@case:source-coxeter-functor-indecomposable-dimension
is similar, using properties of the morphism ${mu_V^alpha}$, and is left to the
reader.

Iteration of Coxeter functors can be defined, relative to certain sequences of
vertices, and provides a useful method for constructing indecomposable objects
in $cal(L)(Gamma)$. More precisely, a sequence ${beta_1,dots,beta_m}$ of
vertices in $Gamma$ (possibly with repetitions) is called a _$+$-sequence_ if
$beta_1$ is a sink in $Gamma$, $beta_2$ is a sink in $sigma_(beta_1) Gamma$,
etc. We have:

#corollary[
  Let $Gamma$ be a finite, connected, oriented graph, and let
  ${beta_1,dots,beta_m}$ be a $+$-sequence of vertices in $Gamma$. Then the
  following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[
      For each $i$, $1≤i≤m$, let $L_(beta_i)$ denote the simple object in the
      category $cal(L)(sigma_(beta_(i-1)) dots sigma_(beta_1) Gamma)$,
      associated with the vertex $beta_i$. Then
      $F_(beta_1)^- dots F_(beta_(i-1))^- L_(beta_i)$ is either $0$ or an
      indecomposable object in $cal(L)(Gamma)$.
    ]<case:coxeter-sequence-simple-reconstruction>],
    [#case[
      Let $(V,f)$ be an indecomposable object in $cal(L)(Gamma)$, and assume
      that $F_(beta_m)^+ dots F_(beta_1)^+ lr((V,f))=0$. Then we have
      $ (V,f) ≅ F_(beta_1)^- dots F_(beta_(i-1))^- L_(beta_i), $
      for some $i$, $1≤i≤m$.
    ]<case:coxeter-sequence-vanishing-reconstruction>],
  )
]<cor:coxeter-functor-sequence-reconstruction>

The first statement follows directly from Theorem
@th:coxeter-functor-indecomposability-reflection. The hypothesis of
part~@case:coxeter-sequence-vanishing-reconstruction lets us choose the first
$i$, $1≤i≤m$, for which
$ F_(beta_(i-1))^+ dots F_(beta_1)^+ lr((V,f)) ≅ L_(beta_i). $
Then $F_(beta_i)^+ F_(beta_(i-1))^+ dots F_(beta_1)^+ lr((V,f))=0$, and it
follows that $F_(beta_1)^+ lr((V,f)),dots,
F_(beta_(i-1))^+ dots F_(beta_1)^+ lr((V,f))$ are all indecomposable objects, by
@th:coxeter-functor-indecomposability-reflection. Then, by
@th:coxeter-functor-indecomposability-reflection, we obtain
$
  F_(beta_(i-1))^- L_(beta_i) ≅
  F_(beta_(i-1))^- F_(beta_(i-1))^+ dots F_(beta_1)^+ lr((V,f))
  ≅ dots F_(beta_(i-2))^+ dots F_(beta_1)^+ lr((V,f)).
$
This argument can be repeated, and the result follows.

#source(815)
=== Representation Categories of Finite Type (Gabriel's Theorem)
<ss:gabriel-finite-representation-type>

Let $Gamma$ be a finite, oriented, connected graph. The category $cal(L)(Gamma)$
is said to be of #idx("Finite representation type")_finite type_ if there exist
at most a finite number of isomorphism classes of indecomposable objects. In
this subsection, we shall prove Gabriel's Theorem @bib:Gabriel1972, which
determines the graphs $Gamma$ for which $cal(L)(Gamma)$ is of finite type, and
describes a basic set of indecomposable objects in this situation. The proof we
shall give is due to Bernstein–Gelfand–Ponomarev~@bib:Bernstein1973, and is
based on the theory of Coxeter functors and root systems.

We may assume at the outset that $Gamma$ is without loops, since otherwise
$cal(L)(Gamma)$ is not of finite type. We shall denote by $E_Gamma$ the vector
space over $RR$ consisting of all vectors ${x=(x_alpha), "with"
  x_alpha in RR}$, whose components are indexed by the set of vertices ${alpha}$
of $Gamma$. A vector $x in E_Gamma$ is called _positive_ if $x≠0$ and
$x_alpha≥0$ for all vertices $alpha$, while $x in E_Gamma$ is called _integral_
if $x_alpha in ZZ$ for all $alpha$. The vector space $E_Gamma$ has an $RR$-basis
consisting of the vectors ${tilde(alpha)}$, where for each vertex $alpha$,
$tilde(alpha)$ is the vector such that $tilde(alpha)_alpha=1$ and
$tilde(alpha)_gamma=0$ if $gamma≠alpha$.

The proof of Gabriel's Theorem is based on a study of a certain quadratic form
$Q$ on the vector space $E_Gamma$, defined by the formula
$
  Q(x)=sum_alpha x_alpha^2-sum_((alpha,beta)) x_alpha x_beta,
  quad "for" x=(x_alpha) in E_Gamma,
$
<eq:graph-quadratic-form>
where the first sum is taken over the set of vertices ${alpha}$, and the second
is taken over the set of oriented edges ${(alpha,beta)}$. The quadratic form $Q$
is associated with a symmetric bilinear form $B$ on $E_Gamma$, given by
$ B(x,y)=frac(1, 2)(Q(x+y)-Q(x)-Q(y)), quad "for" x,y in E_Gamma. $
In this case, we have
$
  B(x,y)=frac(1, 2) lr(
    (
      sum_alpha 2 x_alpha y_alpha
      -sum_((alpha,beta)) x_alpha y_beta-sum_((alpha,beta)) y_alpha x_beta
    )
  ),
$
for $x,y in E_Gamma$. For distinct vertices $beta,gamma$, let $m_(beta gamma)$
be the number of edges joining them. For each vertex $beta$ of $Gamma$, we
define a linear endomorphism $S_beta$ of $E_Gamma$, where, for $x in E_Gamma$,
$ (S_beta x)_gamma=x_gamma quad "if" gamma≠beta $
and
$ (S_beta x)_beta=-x_beta+sum_gamma m_(beta gamma) x_gamma, $
where the sum is taken over the vertices $gamma≠beta$. Each edge incident to
$beta$ is counted once. (Since $Gamma$ has no loops, each individual edge starts
or ends at $beta$, but not both.)
#ed-note[
  Parallel edges are still allowed here. With two edges between two vertices,
  $Q(a,b)=(a-b)^2$; counting their common neighbour only once would send $(1,0)$
  to $(1,1)$ and change the value of $Q$ from $1$ to $0$.
]

The next result summarizes some of the basic properties of $Q$ and $B$, and the
maps $S_beta$.

#source(816)
#lemma[
  #case-list(
    numbering: "(i)",
    [#case[$Q(tilde(alpha))=1$, for each vertex $alpha$ of $Gamma$.]
      <case:graph-root-basis-unit-norm>],
    [#case[Let $alpha,beta$ be distinct vertices. Then
        $-2 B(tilde(alpha),tilde(beta))$ is the cardinal number of the set of
        all undirected edges joining $alpha$ and $beta$.]
      <case:graph-root-bilinear-edge-multiplicity>],
    [#case[For each vertex $beta$, we have $S_beta^2=1$, and
        $S_beta lr((x))=x-2 B(tilde(beta),x)tilde(beta)$, for all
        $x in E_Gamma$.]
      <case:graph-root-reflection-formula>],
    [#case[Each linear map $S_beta$ leaves the bilinear form $B$ invariant:
        $ B(S_beta x,S_beta y)=B(x,y) quad "for all" x,y in E_Gamma. $]
      <case:graph-root-reflection-bilinear-invariance>],
    [#case[Each map $S_beta$ maps the set of integral vectors in $E_Gamma$ onto
      itself.]<case:graph-root-reflection-integral-lattice>],
  )
]<lem:graph-quadratic-form-reflections>

The proof is straightforward from the definitions, and is left as an exercise.

By @case:graph-root-basis-unit-norm[#context {
  reference-number-text(
    "("
      + reference-data(<lem:graph-quadratic-form-reflections>).text
      + reference-data(<case:graph-root-basis-unit-norm>)
        .text
        .trim(regex("[()]"))
      + ")",
  )
}], each basis vector $tilde(beta)$ is nonisotropic with respect to the bilinear
form $B$, and we have $E_Gamma=chevron.l tilde(beta) chevron.r plus.o
chevron.l tilde(beta) chevron.r^perp$. By @lem:graph-quadratic-form-reflections,
the linear maps ${S_beta}$ belong to the orthogonal group $O(E_Gamma)$ defined
by the bilinear form $B$, and each linear map $S_beta$ is a reflection that
fixes the hyperplane $chevron.l tilde(beta) chevron.r^perp$. We shall denote the
group generated by the reflections ${S_beta}$ by $W$. In contrast to
§~@ss:finite-reflection-root-systems, however, the bilinear form $B$ is not
necessarily positive definite, and the group $W$ may be infinite.

#proposition[
  If the quadratic form $Q$ is positive definite, then $W$ is a finite group.
]<prop:positive-graph-form-finite-reflection-group>

#proof[
  If $Q$ is positive definite, the orthogonal group $O(E_Gamma)$ is compact.
  Moreover, $W$ is a closed subgroup of $O(E_Gamma)$, and hence $W$ is compact.
  On the other hand, $W$ preserves the lattice of integral vectors in $E_Gamma$
  by @case:graph-root-reflection-integral-lattice[#context {
    reference-number-text(
      "("
        + reference-data(<lem:graph-quadratic-form-reflections>).text
        + reference-data(<case:graph-root-reflection-integral-lattice>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }], and consequently is a discrete subgroup of $O(E_Gamma)$. It follows that
  $W$ is a compact and discrete subgroup of $O(E_Gamma)$, and hence is finite,
  as required.
]

#proposition[
  Assume that the quadratic form $Q$ is positive definite. Let $Delta$ be the
  subset of $E_Gamma$ consisting of all vectors of the form $x=w tilde(alpha)$,
  where $w in W$ and $alpha$ is a vertex of $Gamma$. Then $Delta$ is a #idx(
    "Root system",
  )root system in $E_Gamma$ satisfying the #idx(
    "Crystallographic root system",
  )crystallographic condition, and $W$ is the #idx(
    "Weyl group of a root system",
  )Weyl group associated with $Delta$.
]<prop:positive-graph-form-crystallographic-root-system>

The proof follows easily from @lem:graph-quadratic-form-reflections,
@prop:positive-graph-form-finite-reflection-group, and
§~@ss:finite-reflection-root-systems, and is left to the reader.

We now introduce the following types of unoriented graphs: #numbered-block[
  #dynkin-first-panels()
  #source(817)
  #dynkin-exceptional-panels()
]<eq:ade-unoriented-graphs>

In the rest of this subsection, it will be convenient to use the notation
$|Gamma|$ for the unoriented graph associated with $Gamma$.

#proposition[
  Let $Q$ be the quadratic form @eq:graph-quadratic-form. Then $Q$ is positive
  definite if and only if $|Gamma|$ is of type $A_n$ $(n≥1)$, $D_n$ $(n≥4)$, or
  $E_n$ $(n=6,7,8)$.
]<prop:positive-graph-form-ade-classification>

#proof[
  #case-list(
    prefix: "Step ",
    numbering: "1.",
    [#case[
      If $|Gamma|$ contains a subgraph of the form
      #numbered-block[#forbidden-graph-panels()]
      <eq:nonpositive-weighted-graph-obstructions>
      then $Q$ is not positive definite. This is shown by taking a vector $x$
      with components indicated at the vertices in
      @eq:nonpositive-weighted-graph-obstructions, zeros at all other vertices,
      and checking that $Q(x)≤0$. Thus if $Q$ is positive definite, $|Gamma|$
      has the form
      #numbered-block[#three-arm-graph()]
      <eq:three-arm-tree-coordinates>
      where $p,q,r$ are nonnegative integers.
    ]<case:ade-classification-obstructions>],
    [#case[
      For each nonnegative integer $p$, let $C_p lr((x_1,dots,x_(p+1)))$ be the
      quadratic form given by
      $
        C_p lr((x_1,dots,x_(p+1))) & = x_1^2+dots+x_p^2
                                     +frac(1, 2) p(p+1)^(-1) x_(p+1)^2 \
                                   & -x_1 x_2-x_2 x_3-dots-x_p x_(p+1).
      $
      Then $C_p$ is nonnegative definite. Moreover, if $x≠0$ and
      $C_p lr((x))=0$, then all components of $x$ are different from zero. These
      assertions are proved by rewriting
      #source(818)
      $C_p lr((x))$ in the form
      $
        C_p lr((x))=sum_(i=1)^p frac(i, 2(i+1))
        lr((x_(i+1)-frac(i+1, i) x_i))^2
      $
    ]<case:ade-classification-arm-squares>],
    [#case[
      Define a vector $x in E_Gamma$ by placing
      $x_1,dots,x_p,y_1,dots,y_q,z_1,dots,z_r,a$ at the vertices of $|Gamma|$ as
      in @eq:three-arm-tree-coordinates. Then we obtain
      $
        Q(x)=C_p lr((x_1,dots,x_p,a))+C_q lr((y_1,dots,y_q,a))
        +C_r lr((z_1,dots,z_r,a))+C a^2.
      $
      It follows that $Q$ is positive definite if and only if
      $ C=1-frac(p, 2(p+1))-frac(q, 2(q+1))-frac(r, 2(r+1))>0, $
      that is,
      $ A=frac(1, p+1)+frac(1, q+1)+frac(1, r+1)>1. $
    ]<case:ade-classification-central-coefficient>],
    [#case[
      Let $p≤q≤r$. We examine the possible cases, using
      Step~@case:ade-classification-central-coefficient.
      #case-list(
        numbering: "(i)",
        [#case[$p=0$, $q$ and $r$ are arbitrary. Then $A>1$, so $Q$ is positive
            definite, and $|Gamma|$ is of type $A_n$ $(n≥1)$.]
          <case:positive-three-arm-tree-type-a>],
        [#case[$p=1$, $q=1$, $r$ arbitrary. Then $A>1$ and $|Gamma|$ is of type
          $D_n$ $(n≥4)$.]<case:positive-three-arm-tree-type-d>],
        [#case[$p=1$, $q=2$, $r=2,3,4$. Then $A>1$, and $|Gamma|$ is of type
          $E_6$, $E_7$ or $E_8$.]<case:positive-three-arm-tree-type-e>],
        [#case[$p=1$, $q=2$, $r≥5$, or $p=1$, $q=3$, $r≥3$, or $p≥2$, $q≥2$, and
          $r≥2$. In all these cases $A≤1$, and the form is not positive
          definite.]<case:nonpositive-three-arm-tree-types>],
      )
    ]<case:ade-classification-arm-lengths>],
  )
  Thus $Q$ is positive definite for graphs $Gamma$ such that $|Gamma|$ is of
  type $A_n,D_n,E_6,E_7,E_8$, and only for these, completing the proof.
]

#definition[
  Let ${alpha_1,dots,alpha_n}$ be an ordering of the vertices of $Gamma$. The
  element $c in W$ defined by
  $ c=S_(alpha_1) S_(alpha_2) dots S_(alpha_n) $
  is called a #idx("Coxeter element")_Coxeter element_ (with respect to the
  given ordering of the vertices.)
]<def:graph-coxeter-element>

#proposition[
  Assume that the quadratic form $Q$ is positive definite, and let $c$ be an
  arbitrary Coxeter element in $W$. Then the following statements hold:
  #case-list(
    numbering: "(i)",
    [#case[No eigenvalue of $c$ is equal to $1$.]
      <case:coxeter-element-no-fixed-vectors>],
    [#case[Let $x in E_Gamma$, $x≠0$. Then there exists a positive integer $i$
        (depending on $x$) such that $c^i x$ is not positive.]
      <case:coxeter-orbit-leaves-positive-cone>],
  )
]<prop:graph-coxeter-element-positive-cone>

#source(819)
#proof[
  Part~@case:coxeter-element-no-fixed-vectors. Let
  $c=S_(alpha_1) dots S_(alpha_n)$, and assume that $c y=y$ for some vector
  $y in E_Gamma$. We shall prove that $y=0$. We first observe that, for all
  vectors $z in E_Gamma$, we have
  $ (S_(alpha_2) S_(alpha_3) dots S_(alpha_n) z)_(alpha_1)=z_(alpha_1), $
  by @case:graph-root-reflection-formula[#context {
    reference-number-text(
      "("
        + reference-data(<lem:graph-quadratic-form-reflections>).text
        + reference-data(<case:graph-root-reflection-formula>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }]. Apply this remark to the equation $c y=y$, and obtain
  $ (S_(alpha_1) y)_(alpha_1)=y_(alpha_1)=(c y)_(alpha_1) $
  using the facts that $S_(alpha_1)^2=1$ and $c y=y$. It follows that
  $S_(alpha_1) y=y$, by @case:graph-root-reflection-formula[#context {
    reference-number-text(
      "("
        + reference-data(<lem:graph-quadratic-form-reflections>).text
        + reference-data(<case:graph-root-reflection-formula>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }]. The argument can be repeated, and yields the result that
  $ S_(alpha_1) y=S_(alpha_2) y=dots=S_(alpha_n) y=y. $
  Then $B(y,tilde(alpha)_1)=B(y,tilde(alpha)_2)=dots=
  B(y,tilde(alpha)_n)=0$ by @case:graph-root-reflection-formula[#context {
    reference-number-text(
      "("
        + reference-data(<lem:graph-quadratic-form-reflections>).text
        + reference-data(<case:graph-root-reflection-formula>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }] again. Since ${tilde(alpha)_1,dots,tilde(alpha)_n}$ is a basis of
  $E_Gamma$, and $Q$ is positive definite, we obtain $y=0$, completing the proof
  of part~@case:coxeter-element-no-fixed-vectors.

  Part~@case:coxeter-orbit-leaves-positive-cone. The group $W$ is finite by
  @prop:positive-graph-form-finite-reflection-group. Then $c^h=1$ for some
  positive integer $h$. If ${x,c x,dots,c^(h-1) x}$ are all positive, then
  $ x+c x+dots+c^(h-1) x $
  is positive, and fixed by $c$. This contradicts
  part~@case:coxeter-element-no-fixed-vectors, and completes the proof.
]

We can now state the main result of the section.

#theorem(title: [Gabriel @bib:Gabriel1972])[
  #idx("Gabriel's Theorem")
  Let $Gamma$ be a finite, oriented, connected graph. Then the following
  statements hold.
  #case-list(
    numbering: "(i)",
    [#case[
      If the category $cal(L)(Gamma)$ is of finite type, then the quadratic form
      $Q$, given by @eq:graph-quadratic-form, is positive definite, and
      $|Gamma|$ is a graph of type $A_n$ $(n≥1)$, $D_n$ $(n≥4)$, or $E_n$
      $(n=6,7,8)$.
    ]<case:gabriel-finite-type-implies-ade>],
    [#case[
      Let $|Gamma|$ be a graph of type $A_n$ $(n≥1)$, $D_n$ $(n≥4)$, or $E_n$
      $(n=6,7,8)$. Then $cal(L)(Gamma)$ is of finite type. Moreover, the map
      $ (V,f) arrow dim(V, f)=(dim V_alpha) in E_Gamma $
      defines a bijection from the set of isomorphism classes of indecomposable
      objects ${(V,f)}$ in $cal(L)(Gamma)$, to the set of positive roots in the
      root system $Delta$ (see
      @prop:positive-graph-form-crystallographic-root-system), for a suitable
      ordering of the roots.
    ]<case:gabriel-ade-positive-root-bijection>],
  )
]<th:gabriel-finite-type-positive-root-classification>

#proof[
  Part~@case:gabriel-finite-type-implies-ade. (Tits) Consider the set of all
  objects $(V,f)$ in $cal(L)(Gamma)$ of a fixed nonzero dimension $d=(d_alpha)$.
  Let ${V_alpha}$ be a fixed set of $K$-spaces, indexed by the vertices of
  $Gamma$, such that $dim V_alpha=d_alpha$, for each $alpha$. An object of
  dimension $d$ is determined uniquely
  #source(820)
  by a family of linear maps
  $ f_e:V_alpha arrow V_beta, quad e=(alpha,beta), $
  and hence by an element
  $ f=(f_e) in product_(e=(alpha,beta)) "Hom"_K lr((V_alpha,V_beta)), $
  where the product is taken over the set of edges in $Gamma$. Let $f=(f_e)$ and
  $f'=(f'_e)$ represent two objects of dimension $d$. A morphism $phi$ from the
  object represented by $f$ to the one represented by $f'$ is described by a set
  of $K$-linear maps ${phi_alpha in "End"_K V_alpha}$ such that the diagrams
  commute:
  #base-change-square()
  The objects corresponding to $f$ and $f'$ are isomorphic if and only if
  $phi_alpha in "GL"(V_alpha)$ for each $alpha$, and
  $
    f'_e=phi_beta f_e phi_alpha^(-1)
    quad "for each edge" e=(alpha,beta).
  $
  The group $G=product_alpha "GL"(V_alpha)$ acts on the vector space
  $product_(e=(alpha,beta)) "Hom"_K lr((V_alpha,V_beta))$ in a natural way. From
  the preceding remarks, it is clear that two elements $f$ and $f'$ belong to
  the same $G$-orbit if and only if the corresponding objects of $cal(L)(Gamma)$
  are isomorphic.

  Now assume that $cal(L)(Gamma)$ is of finite type. By the preceding
  discussion, this means that, in a given dimension $d=(d_alpha)$, the number of
  $G$-orbits on $product_((alpha,beta)) "Hom"_K lr((V_alpha,V_beta))$ is finite,
  where $G=product_alpha "GL"(V_alpha)$. Since $G$ is a connected affine
  algebraic group over an algebraically closed field, the finiteness of the
  number of orbits means that there exists an open dense orbit. The dimension of
  this orbit is equal to
  $
    delta(d)=sum_(e=(alpha,beta)) dim_K "Hom"_K lr((V_alpha,V_beta))
    =sum_(e=(alpha,beta)) d_alpha d_beta,
  $
  and satisfies the inequality
  $ delta(d)≤dim G-1, $
  since $G$ contains a one-dimensional subgroup that acts trivially on
  $product_((alpha,beta)) "Hom"_K lr((V_alpha,V_beta))$. (For proofs of these
  facts, see any book on linear algebraic
  #source(821)
  groups.) Since $dim G=sum_alpha d_alpha^2$, it follows that
  $ sum_alpha d_alpha^2-sum_((alpha,beta)) d_alpha d_beta≥1>0. $
  Therefore the quadratic form $Q$, defined in @eq:graph-quadratic-form, is
  positive definite, because the preceding result shows that $Q(d)>0$ for each
  positive integral vector $d=(d_alpha)$.
  Part~@case:gabriel-finite-type-implies-ade of the theorem now follows at once
  from @prop:positive-graph-form-ade-classification.

  Part~@case:gabriel-ade-positive-root-bijection. Let $Gamma$ be a graph such
  that $|Gamma|$ is of type $A_n$ $(n≥1)$, $D_n$ $(n≥4)$, or $E_n$ $(n=6,7,8)$.
  Then the quadratic form $Q$ defined in @eq:graph-quadratic-form is positive
  definite, by @prop:positive-graph-form-ade-classification. This implies that
  the group $W$ generated by the reflections ${S_beta}$ is finite, by
  @prop:positive-graph-form-finite-reflection-group. Moreover, by
  @prop:positive-graph-form-crystallographic-root-system, the set $Delta$
  consisting of the $W$-transforms ${w tilde(alpha)}_(w in W)$ of the basis
  elements ${tilde(alpha)}$ is a root system in $E_Gamma$ satisfying the
  crystallographic condition. The basis elements ${tilde(alpha)}$ of $E_Gamma$
  clearly form a fundamental system of roots in $Delta$, and ${S_alpha}$ is the
  corresponding set of fundamental reflections in $W$ (see
  @def:fundamental-root-system). By
  @cor:positive-roots-unique-fundamental-system, there exists a unique set of
  positive roots $Delta_+$ containing the fundamental system ${tilde(alpha)}$.

  Choose an ordering ${beta_1,dots,beta_n}$ such that, for each edge
  $e=(alpha,beta)$, $alpha$ has a greater index than $beta$. Such an ordering
  exists because $|Gamma|$ is a tree. Extend it periodically by
  $beta_(j+n)=beta_j$. The resulting infinite sequence is a $+$-sequence: each
  edge is reversed twice in one period. Put
  $ c=S_(beta_n) dots S_(beta_1). $
  Let $(V_0,f_0)=(V,f)$ be indecomposable, of dimension $d_0=d$, and put
  $
    (V_j,f_j)=F_(beta_j)^+ lr((V_(j-1),f_(j-1))), quad
    d_j=S_(beta_j) d_(j-1).
  $
  By @prop:graph-coxeter-element-positive-cone, $c^h d$ is not positive for some
  $h>0$. If no object were killed in the first $h n$ steps,
  @th:coxeter-functor-indecomposability-reflection would make all these objects
  nonzero indecomposables of dimensions $d_j$, contradicting $d_(h n)=c^h d$.
  Let $k$ be the first killing step. Then $(V_(k-1),f_(k-1)) ≅ L_(beta_k)$, and
  the same theorem gives
  $
    (V,f) ≅ F_(beta_1)^- dots F_(beta_(k-1))^- L_(beta_k),
    quad d=S_(beta_1) dots S_(beta_(k-1)) tilde(beta)_k.
  $
  Thus $d in Delta_+$. Moreover, $k$ is the first index for which $d_k$ is not
  positive, since $d_k=-tilde(beta)_k$. It is determined by $d$, and the
  reconstruction determines $(V,f)$ up to isomorphism. Since $Delta_+$ is
  finite, $cal(L)(Gamma)$ is of finite type.
  #ed-note[
    The root assertion in Lemma~@lem:coxeter-functor-positive-root-dimensions
    cannot itself justify the preceding inclusion of dimension vectors among
    roots. The terminating argument uses only
    Theorem~@th:coxeter-functor-indecomposability-reflection and
    Proposition~@prop:graph-coxeter-element-positive-cone. In the converse
    construction, formal dimension calculations alone do not ensure that inverse
    functors give nonzero objects.
  ]

  We next summarize the effect of the reflections ${S_alpha}$ on these dimension
  vectors. The preceding argument establishes the root membership needed in the
  following lemma.

  #lemma[
    Let $beta$ be a sink in $Gamma$, and let $(V,f)$ be an indecomposable object
    in $cal(L)(Gamma)$ of dimension $d=(d_alpha)$. Then either $(V,f) ≅ L_beta$,
    $F_beta^+ lr((V,f))=0$, and $S_beta lr((d))$ is not a positive vector in
    $E_Gamma$, or $F_beta^+ lr((V,f))$ is indecomposable, and
    $dim F_beta^+ lr((V,f))=S_beta d in Delta_+$. A similar statement holds for
    a source vertex $alpha$, and the functor $F_alpha^-$.
  ]<lem:coxeter-functor-positive-root-dimensions>

  In the following corollary, we recall the concept of a $+$-sequence of
  vertices ${beta_1,beta_2,dots,beta_n}$, which is a sequence, possibly with
  repetitions, such that $beta_i$ is a sink in
  $sigma_(beta_(i-1)) dots sigma_(beta_1) Gamma$, for each $i>1$ (see
  @cor:coxeter-functor-sequence-reconstruction).

  #corollary[
    Let ${beta_1,dots,beta_m}$ be a $+$-sequence of vertices in $Gamma$, and let
    $(V,f)$ be an indecomposable object in $cal(L)(Gamma)$ of dimension $d$. Put
    $(V_0,f_0)=(V,f)$, $d_0=d$, and
    $ (V_j,f_j)=F_(beta_j)^+ dots F_(beta_1)^+ lr((V,f)), $
    $ d_j=S_(beta_j) dots S_(beta_1) d, quad "for" 1≤j≤m. $
    Let $i$ be the largest integer with $0≤i≤m$ such that $d_j in Delta_+$ for
    $0≤j≤i$. For $0≤j≤i$, $(V_j,f_j)$ is indecomposable, of dimension $d_j$, and
    $ (V,f) ≅ F_(beta_1)^- dots F_(beta_j)^- lr((V_j,f_j)), $
    where an empty product is the identity. If $i<m$, then
    $(V_i,f_i) ≅ L_(beta_(i+1))$ and $(V_j,f_j)=0$ for $i<j≤m$. If $i=m$, all
    the objects through $(V_m,f_m)$ remain indecomposable.
  ]<cor:positive-coxeter-sequence-reconstruction>
  The lemma follows from @th:coxeter-functor-indecomposability-reflection and
  the root membership just proved. For the corollary, apply that theorem
  successively. Until the first killing step, the objects remain indecomposable
  with the stated positive dimensions, and each step can be inverted. At a
  killing step $i+1$, the preceding object is $L_(beta_(i+1))$, and
  $d_(i+1)=-tilde(beta)_(i+1)$ is not positive. All later objects are zero.
  Conversely, a first failure of positivity forces a killing step, since the
  other case of the theorem has a nonzero dimension vector. This proves both the
  first-exit and the no-exit alternatives, including $i=0$ and the empty inverse
  product.
  #ed-note[
    For the graph $1 arrow 2$ and $V=L_1$, the one-term sink sequence $(2)$
    gives dimension $(1,1)$, not a vertex-simple object. Thus a finite sequence
    can end before any killing step; reconstruction from $V_j$ also requires all
    $j$ inverse functors.
  ]

  We have already proved finite type and uniqueness for each dimension. To
  complete part~@case:gabriel-ade-positive-root-bijection, it remains to
  #source(822)
  show that every positive root is the dimension of an indecomposable object.
  Let $x in Delta_+$, and use the same infinite periodic $+$-sequence. Put
  $x_0=x$ and $x_j=S_(beta_j) x_(j-1)$. By
  @prop:graph-coxeter-element-positive-cone, there is a first index $i+1$ for
  which $x_(i+1)$ is not positive. By the Main Lemma
  @lem:simple-reflection-positive-roots, $x_i=tilde(beta)_(i+1)$.

  Start with $L_(beta_(i+1))$ and apply the inverse functors in reverse order.
  Suppose the current object at stage $j$ is indecomposable of dimension $x_j$,
  where $1≤j≤i$. If it were $L_(beta_j)$, then
  $x_(j-1)=S_(beta_j) x_j=-tilde(beta)_j$, contradicting the positivity of
  $x_(j-1)$. Hence @th:coxeter-functor-indecomposability-reflection shows that
  $F_(beta_j)^-$ does not kill it, and gives an indecomposable of dimension
  $x_(j-1)$. Induction therefore proves that
  $ (V,f)=F_(beta_1)^- dots F_(beta_i)^- L_(beta_(i+1)) $
  is indecomposable, of dimension
  $ S_(beta_1) dots S_(beta_i) tilde(beta)_(i+1)=x. $
  This completes the proof of
  Theorem~@th:gabriel-finite-type-positive-root-classification.
]
