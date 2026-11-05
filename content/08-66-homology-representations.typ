#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/66-homology.typ": (
  orbit-universal-triangle, simplex-subdivision,
)

== Homology Representations of Finite Groups with $B N$-Pairs
<sec:homology-representations-bn-pairs>

This section contains a striking illustration of the close connection between
the representation theory of a finite group of Lie type $G$ and the
representations of the Weyl group $W$ of $G$. The connection arises in this case
through the comparison of the posets of proper parabolic subgroups of $W$ and
$G$, respectively, and the representations of $W$ and $G$ on their rational
homology. The section contains a general introduction to representations of
finite groups on the homology of simplicial complexes, followed by a discussion
of the particular representations obtained in the case of $W$ and $G$.

=== Homology Representations of Finite Groups
<ss:finite-group-homology-representations>

In this subsection, we present an introduction to representations of finite
groups arising from their actions on posets and finite simplicial complexes.
This work #source(603) extends the theory of permutation representations
afforded by group actions on sets, already discussed in
§~@i:ss:background-group-theory and §~@i:sec:induced-modules. Our approach
follows Curtis–Lehrer @bib:Curtis1981, which in turn is based partly on ideas
from Quillen @bib:Quillen1978, Lusztig @bib:Lusztig1974, Bredon @bib:Bredon1972,
and Curtis @bib:Curtis1980b. For further discussion of assumed results from
algebraic topology, see Hilton–Wylie @bib:Hilton1960, Eilenberg–Steenrod
@bib:Eilenberg1952, and Godement @bib:Godement1964.

The contents of this subsection, concentrating on the Lefschetz character and
the endomorphism algebra of a homology representation, are applied in
§~@ss:coxeter-poset-finite-reflection-group to give a geometric interpretation
of the sign representation of a finite g.g.r., and in
§~@ss:combinatorial-building-steinberg-representation to the Steinberg
representation of a finite group with a $B N$-pair.

We begin with some definitions. An (abstract) #idx(
  "Simplicial complex",
)_simplicial complex_ $Sigma$ consists of a set of points ${x,y,...}$, called
_vertices_, together with certain finite, non-empty sets of vertices ${sigma}$
called _simplices_, satisfying the axioms that
#case-list(
  numbering: "(i)",
  [#case[each singleton set ${x}$ is a simplex, and]
    <case:simplicial-singleton-axiom>],
  [#case[each non-empty subset $sigma'$ of a simplex $sigma$ is also a
    simplex.] <case:simplicial-face-axiom>],
)
We shall restrict our attention mainly to _finite_ simplicial complexes, that
is, complexes $Sigma$ whose vertex set is finite.

An _r-simplex_ of $Sigma$ is a simplex $sigma={x_0,x_1,...,x_r}$ consisting of
$r+1$ vertices. A _simplicial map_ $f:Sigma arrow.r Sigma'$ of simplicial
complexes is a map $f$ from the vertices of $Sigma$ to those of $Sigma'$, such
that if ${x_0,x_1,...,x_r}$ is an r-simplex in $Sigma$, then
${f(x_0),f(x_1),...,f(x_r)}$ are the vertices (possibly with repetitions) of a
simplex in $Sigma'$. The finite simplicial complexes form a category, in which
morphisms are simplicial maps.

Now let $G$ be a finite group; a simplicial complex $Sigma$ is called a
_$G$-complex_, and $G$ is said to _act_ on $Sigma$, if the vertices of $Sigma$
form a $G$-set (see @i:def:g-set), and if the action of $G$ carries simplices
onto simplices.

The representation theory of $G$-complexes will turn out to be equivalent to the
conceptually simpler theory of $G$-posets. A _poset_ $(X,<=)$ is a partially
ordered set with a reflexive, antisymmetric, transitive relation $<=$. A #idx(
  "G-poset",
)_$G$-poset_ is a poset $(X,<=)$, with $X$ a $G$-set such that the $G$-action
preserves the order relation: if $x<=y$, then $g x<=g y$, for $x,y in X$ and
$g in G$.

Each $G$-poset $X$ defines a $G$-complex $Sigma(X)$, whose vertices are the
elements of $X$, and whose simplices are chains in $X$ (i.e., finite totally
ordered subsets of $X$).

The finite $G$-complexes form a category, in which the objects are
$G$-complexes, and the morphisms are simplicial maps preserving the $G$-action.
The $G$-posets also form a category in the obvious way, namely, the morphisms
are $G$-maps preserving the partial order structure. Then the rule, which
assigns to each $G$-poset $X$ the corresponding complex $Sigma(X)$, is a functor
from one category to the other.

Clearly, $G$-posets are abundant in group theory; any family of subgroups of a
group $G$, closed under conjugation, is a $G$-poset, with the order relation
given by inclusion and the $G$-action by conjugation. Our object is to assign a
$QQ$-representation of $G$ to each such $G$-poset, and to investigate some of
its properties. In particular, we need to discuss the poset structure of
$G$-orbits, which is more subtle than the study of $G$-orbits in $G$-sets, and
which can best be understood by introducing some geometrical concepts.

#source(604)
To each simplicial complex $Sigma$ we may associate an #idx(
  "Underlying topological space",
)_underlying topological space_, or #idx("Geometric realization")_geometric
realization_, denoted by $|Sigma|$. This geometric realization $|Sigma|$ is
defined to be the set of all real-valued functions $p$, defined on the vertex
set of $Sigma$, and satisfying the three conditions:
$
  cases(
    p(x)>=0 quad "for all vertices" x "of" Sigma\,,
    sum_x p(x)=1\,,
    op("supp") p "is a simplex of" Sigma\,,
  )
$
where the _support_ of $p$ is defined by
$ op("supp") p={x:p(x)!=0}. $
For each n-simplex $sigma$ of $Sigma$, denote by $|sigma|$ the subset of
$|Sigma|$ defined by
$ |sigma|={p in |Sigma|:op("supp") p subset.eq sigma}. $
We now proceed to topologize $|sigma|$, by making its points correspond to those
inside a standard n-simplex in $RR^n$. Specifically, let $e_1,...,e_n$ be an
orthonormal basis for $RR^n$, and consider the standard n-simplex in $RR^n$ with
vertices 0 and the endpoints of the vectors $e_1,...,e_n$. Each point
$p in |sigma|$ determines a point in this standard n-simplex, namely, the
endpoint of the vector $sum_(i=1)^n p(x_i)e_i$, where $sigma={x_0,x_1,...,x_n}$.
In view of the condition $sum_(i=0)^n p(x_i)=1$, the correspondence between the
points of $|sigma|$ and those of the standard n-simplex in $RR^n$, is a
bijection. We then topologize $|sigma|$ by using this bijection, and the natural
topology in $RR^n$. Finally, we topologize the geometrical realization
$Sigma arrow.r |Sigma|$ by choosing, as the family of open sets, those subsets
$U$ of $|Sigma|$ such that $U inter |sigma|$ is open in $|sigma|$ for every
simplex $sigma$ of $Sigma$.

It will be convenient to write each point $p in |Sigma|$ as a formal sum
$p=sum_x p(x)x$, in which $x$ ranges over the vertex set of $Sigma$. The
correspondence, which carries the simplicial complex $Sigma$ onto its geometric
realization $|Sigma|$, is a functor from the category of simplicial complexes
and simplicial maps to the category of topological spaces and continuous maps. A
simplicial map $f:Sigma arrow.r Sigma'$ yields a continuous map
$|f|:|Sigma| arrow.r |Sigma'|$, defined by
$ p in |Sigma| arrow.r.bar |f|p=sum p(x)f(x) in |Sigma'|. $
Thus we have a composite functor
$ X arrow.r Sigma(X) arrow.r |Sigma(X)|, $
which carries the finite $G$-poset $X$ onto the geometrical realization
$|Sigma(X)|$ of the finite simplicial complex $Sigma(X)$. Here, $G$ is as usual
some finite group.

A useful construction is the #idx("Barycentric subdivision")_barycentric
subdivision_ $op("Sd") Sigma$ of a simplicial complex $Sigma$. This is the poset
whose elements are the simplices $sigma$ of $Sigma$, and the order #source(605)
relation is inclusion of simplices: $sigma'<=sigma$ if $sigma' subset.eq sigma$.
It is clear that if $Sigma$ is a $G$-complex, then $op("Sd") Sigma$ is a
$G$-poset, with the same $G$-action. The following result explains our previous
remark that the representation theory of a finite group $G$ on $G$-complexes is
equivalent to its representation theory on $G$-posets.

#proposition[
  Let $Sigma$ be a $G$-complex, and $X=op("Sd") Sigma$ be the $G$-poset defined
  above. Then there is a _$G$-equivariant_#footnote[
    A $G$-equivariant map between two sets with $G$-actions is a map preserving
    the $G$-action.
  ] <fn:equivariant-map>
  homeomorphism between the underlying topological spaces of $Sigma$ and of the
  $G$-complex $Sigma(op("Sd") Sigma)$ associated with the $G$-poset
  $op("Sd") Sigma$.
] <prop:barycentric-subdivision-realization>

#proof(head: emph[Sketch of Proof.])[
  It is sufficient to consider the case of a simplex $sigma$, and the argument
  in this case can easily be derived from the following example. Here $sigma$
  #simplex-subdivision()
  has vertices 0, 1, 2, 1-simplices 01, 12, 02, and 2-simplex 012. Then
  $Sigma(op("Sd") Sigma)$ has vertices corresponding to the simplices of
  $sigma$, 1-simplices $(0,01)$, $(1,01)$, $(1,12)$, $(2,12)$, etc., and
  2-simplices $(0,01,012)$, $(1,01,012)$, etc. One then defines a canonical
  homeomorphism from $|op("Sd") sigma|$ to $|sigma|$, using barycentric
  coordinates in the corresponding simplices in euclidean space, and that
  preserves a group action if one is present. (For further details, see
  Eilenberg–Steenrod @bib:Eilenberg1952.)
]

The preceding result allows us to concentrate on $G$-posets rather than
$G$-complexes. For a $G$-poset $X$, the _barycentric subdivision_ $op("Sd") X$
is the $G$-poset whose elements are the chains in $X$, and the order relation is
inclusion of one chain in another, with the same $G$-action. It is also useful
to introduce the notation $|X|$ for the underlying topological space of the
simplicial complex $Sigma(X)$. Then by @prop:barycentric-subdivision-realization
and the identifications we have made, there exists a $G$-equivariant
homeomorphism
$ |X| approx |op("Sd") X|. $
<eq:poset-barycentric-realization>
Another $G$-poset related to a given $G$-poset $X$ is the _opposite poset_
$X^degree$, consisting of the same elements as $X$, with the order reversed. We
clearly have $Sigma X=Sigma X^degree$, $op("Sd") X=op("Sd") X^degree$, and there
is a $G$-equivariant homeomorphism $|X| approx |X^degree|$.

We are now in a position to give geometric interpretations of fixed points and
orbits in $G$-posets.

#proposition[
  Let $X$ be a $G$-poset, for a group $G$, and let $g in G$. Then $g$ fixes a
  simplex $sigma$ in $op("Sd") X$ if and only if $g$ fixes all the vertices of
  $sigma$. Moreover, there exists a #source(606) homeomorphism
  $|X^g| approx |X|^g$, where $X^g$ denotes the subposet of $X$ consisting of
  elements fixed by $g$, and $|X|^g$ is the fixed point set of $g$ in the
  topological space $|X|$.
] <prop:poset-fixed-point-realization>

#proof[
  Recall that $g in G$ preserves the order relation in $X$, by definition. The
  first statement is clear, since $g$ fixes a chain in $X$ if and only if it
  fixes the elements of the chain. For the second part, we show that each
  element $p in |X|^g$ is in the geometric realization of a unique simplex fixed
  by $g$, which is then a simplex in $Sigma(X^g)$, by the first remark. The
  simplex in $Sigma(X^g)$, whose existence is claimed, is the unique minimal
  simplex $sigma$ with $p$ in the interior of $|sigma|$. Since $g$ fixes $p$,
  and $g$ is a simplicial map, it follows that $g$ maps the simplex $sigma$ to
  itself, as required. It is then straightforward to construct a homeomorphism
  $|X^g| approx |X|^g$.
]

We now come to an important concept, similar to one introduced by Bredon
@bib:Bredon1972 for $G$-complexes, that allows us to construct orbit posets.

#definition[
  Let $X$ be a $G$-poset. Then $X$ is said to be _regular_ (with respect to the
  $G$-action) if for all $x,y in X$, and $g in G$, the relations $x<=y$ and
  $g x<=y$ imply that $g x=x$.
] <def:regular-group-poset>
#idx("Regular G-poset", target: [@def:regular-group-poset])

The reader should check that, even in the simplest cases, a $G$-poset may fail
to be regular. Nevertheless, we have:

#proposition[
  Let $X$ be an arbitrary $G$-poset. Then the second barycentric subdivision
  $op("Sd")^2 X$ is a regular $G$-poset.#footnote[
    As an exercise, the reader can check that if $X$ is a finite $G$-poset, then
    $op("Sd") X$ is regular.
  ] <fn:first-subdivision-finite-regular>
] <prop:second-subdivision-regular>

#proof[
  The elements in $op("Sd") X$ are chains, denoted by $(x)=(x_0<x_1<dots<x_m)$,
  and the elements of $op("Sd")^2 X$ are chains of chains
  ${(Y^0) subset (Y^1) subset dots subset (Y^n)}$, where $(Y^i)$ is a chain
  $(y_0^i<dots<y_(d_i)^i)$, and the order relation is inclusion. Note that
  $op("card")(Y^0)<op("card")(Y^1)<dots<op("card")(Y^n)$. It follows that if an
  element $g in G$ carries one subchain $(Y^(i_0)) subset dots subset (Y^(i_m))$
  to another $(Y^(j_0)) subset dots subset (Y^(j_m))$, then we have
  $op("card")(Y^(i_0))=op("card")(Y^(j_0)),...,
  op("card")(Y^(i_m))=op("card")(Y^(j_m))$, since the action of $g$ preserves
  cardinality of subsets of $(Y^n)$. Therefore
  $(Y^(i_0))=(Y^(j_0)),...,(Y^(i_m))=(Y^(j_m))$, since the element
  $(Y^0) subset dots subset (Y^n)$ of $op("Sd")^2 X$ has a unique element
  $(Y^j)$ of a given cardinality. This completes the proof.
]

For a $G$-poset $X$, it follows from @eq:poset-barycentric-realization that the
structure of the underlying topological space $|X|$ and the action of $G$ on
this space are unchanged (up to homeomorphism) when $X$ is replaced by
$op("Sd")^2 X$. Since $op("Sd")^2 X$ is a regular $G$-poset by the preceding
result, it therefore suffices for us to consider regular $G$-posets in what
follows.

For a regular $G$-poset $X$, we now define the _orbit poset_
$ overline(X)=G backslash X $
as the poset whose elements are $G$-orbits $overline(x)=G x$ of elements $x$ of
$X$, with the order #source(607) relation $overline(x)<=overline(y)$ provided
that $x_0<=y_0$ for some $x_0 in overline(x)$ and $y_0 in overline(y)$. The
proof that $overline(x)<=overline(y)$ is a well-defined order relation is left
to the reader.

It is entirely possible for the opposite poset $X^degree$ to be regular, while
$X$ is not regular (this occurs, for example, in the case of the Coxeter poset
defined in @def:coxeter-poset). It is clear that if either $X$ or $X^degree$ is
regular, then the orbit poset $overline(X)$ is well defined.

#proposition[
  Let $X$ be a regular $G$-poset. Then $op("Sd") X$ is regular, and the map
  $
    psi:overline(x_0<x_1<dots<x_m)
    arrow.r.bar overline(x)_0<overline(x)_1<dots<overline(x)_m,
    quad x_i in X,
  $
  defines an isomorphism of posets
  $overline(op("Sd") X) approx op("Sd") overline(X)$.
] <prop:regular-poset-subdivision-orbits>

#proof[
  We show first that $op("Sd") X$ is regular. For suppose that $(x),(y)$ are
  chains in $X$, with $(x)<=(y)$, $g(x)<=(y)$ in $op("Sd") X$, for some
  $g in G$. Then we obtain $(x)=g(x)$, as desired, by applying the regularity
  condition to the maximal element of $(y)$. The map $psi$ defined above is
  clearly a map of posets, and is surjective. Now suppose we have two chains
  $ y_0<y_1<dots<y_m quad "and" y'_0<y'_1<dots<y'_m, $
  where $overline(y)_i=overline(y)'_i$ for $0<=i<=m$. Then for each $i$, we may
  write $y'_i=g_i y_i$ with $g_i in G$. Therefore $g_i y_i=y'_i<=y'_m=g_m y_m$,
  so $g_m^(-1) g_i y_i<=y_m$. Since $y_i<=y_m$, we deduce that
  $g_m^(-1) g_i y_i=y_i$, by regularity. It follows that
  $ g_m lr((y_0<dots<y_m))=y'_0<dots<y'_m, $
  completing the proof.
]

#corollary[
  Let $overline(x)_0<dots<overline(x)_m$ be a chain in the orbit poset
  $overline(X)$. Then the set of all chains $y_0<dots<y_m$ in $X$ lying over
  $overline(x)_0<dots<overline(x)_m$ (in the sense that $y_i in overline(x)_i$,
  $0<=i<=m$), is a single $G$-orbit in $op("Sd") X$.
] <cor:regular-poset-chain-orbits>

#proposition[
  Let $X$ be a finite regular $G$-poset. Then $|overline(X)|$ is homeomorphic to
  the topological orbit space $G backslash |X|$ of $G$-orbits on $|X|$.
] <prop:regular-orbit-poset-realization>

#proof[
  We first recall that if a discrete group $G$ acts on a topological space $Z$,
  then the topology in the orbit space $overline(Z)$ is defined by letting
  $U subset.eq overline(Z)$ be open in $overline(Z)$ whenever $pi^(-1) U$ is
  open in $Z$, where $pi:Z arrow.r overline(Z)$ is the natural map. This
  construction has the universal property that if $f:Z arrow.r W$ is a
  continuous map from $Z$ to a topological space $W$, which is constant on
  $G$-orbits, then there exists a continuous map
  $overline(f):overline(Z) arrow.r W$ making the following diagram commutative:
  #orbit-universal-triangle()

  #source(608)
  In our case, $x in X arrow.r overline(x) in overline(X)$ is a map of posets,
  so the composite functor $X arrow.r Sigma(X) arrow.r
  |Sigma(X)|=|X|$ defines a continuous map $phi:|X| arrow.r |overline(X)|$,
  given by
  $ phi lr((sum p(x)x))=sum p(x)overline(x), quad "for" p in |X|. $
  Since the action of $G$ on $|X|$ is defined by
  $ |g| lr((sum p(x)x))=sum p(x)g x, quad g in G, $
  it follows that $phi$ is constant on $G$-orbits in $|X|$, and hence defines a
  continuous map $overline(phi):G backslash |X| arrow.r |overline(X)|$, given by
  $ overline(phi) lr((overline(sum p(x)x)))=sum p(x)overline(x). $
  Then $overline(phi)$ is surjective, and since $G backslash |X|$ is a compact
  Hausdorff space, $overline(phi)$ will be a homeomorphism if it is injective.
  Now let $phi(p')=phi(p'')$, for $p',p'' in |X|$; we shall prove that $p'$ and
  $p''$ lie in the same $G$-orbit. We may assume $p'=sum p'(x)x$,
  $p''=sum p''(y)y$, where the supports of $p'$ and $p''$ are strictly
  increasing chains in $X$ lying over the chain in $overline(X)$ supporting
  $phi(p')=phi(p'')$. By @cor:regular-poset-chain-orbits, we have
  $op("supp") p'=g op("supp") p''$ for some $g in G$, and it follows that
  $p'=g dot p''$, since $phi(p')=phi(p'')$ implies $p'(x)=p''(y)$ if
  $overline(x)=overline(y)$. Thus $overline(phi)$ is injective, and the result
  follows.
]

#definition[
  Let $X$ and $Y$ be $G$-posets. Their _cartesian product_ $X times Y$ is the
  $G$-poset on the cartesian product of the sets $X$ and $Y$, with the order
  relation
  $
    (x,y)<=(x',y') quad "if and only if" x<=x' quad "and" y<=y',
    quad "for" x,x' in X quad "and" y,y' in Y.
  $
  The $G$-action on $X times Y$ is diagonal action:
  $ g(x,y)=(g x,g y), quad "for all" x in X, y in Y, g in G. $
] <def:group-poset-cartesian-product>

We quote without proof (see Eilenberg–Steenrod @bib:Eilenberg1952, II, §8):

#proposition[
  Let $X$ and $Y$ be $G$-posets. There exists a $G$-equivariant homeomorphism
  $ |X times Y| approx |X| times |Y|. $
] <prop:poset-product-realization>

With these topological preliminaries out of the way, we now turn to homology
representations. We first recall that a #idx("Chain complex")_chain complex_ $C$
over a field $K$ is a graded vector space
$ C=plus.o.big_(r=0)^infinity C_r, $
with the ${C_r}$ subspaces of $C$, together with a _boundary homomorphism_
$partial:C arrow.r C$, #source(609) which is a $K$-endomorphism such that
$
  partial C_r subset.eq C_(r-1) quad "for" r>=1,
  quad partial C_0=0, quad "and" partial^2=0.
$
Then $im partial subset.eq ker partial$, and the quotient
$
  H_ast lr((C))=frac(ker partial, im partial)
  =plus.o.big_(r=0)^infinity H_r lr((C))
$
is the #idx("Homology groups")_homology group_ of $C$. Clearly $H_ast lr((C))$
is also a graded vector space, with
$
  H_r lr((C))=(ker partial |_(C_r))/(im partial |_(C_(r+1)))
  quad "for" r>=0.
$
A finite group $G$ is said to _act_ on a chain complex $C$ if each subspace
$C_r$ is a f.d. $K G$-module and if $partial$ commutes with the action of $G$.
We refer to $C$ as a _chain complex with $G$-action_ in this case, and then the
homology spaces ${H_r lr((C))}$ are $K G$-modules, affording what we shall call
#idx("Homology representations")_homology representations_ of $G$.

Now let $X$ be a $G$-poset, and $K$ a field. We shall define a chain complex
$C(X)$ with $G$-action, as follows. For $r>=0$, the subspace $C_r lr((X))$ of
r-chains has a $K$-basis ${c_sigma}$, indexed by r-simplices
$sigma=(x_0<x_1<dots<x_r)$ in $Sigma(X)$. The action of $G$ is given by its
permutation action on the r-chains:
$ g c_sigma=c_(g sigma), quad "for" sigma "as above, and" g in G. $
The boundary homomorphism $partial:C_r lr((X)) arrow.r C_(r-1) lr((X))$ is given
by
$ partial c_sigma=sum_(i=0)^r (-1)^i c_(sigma_i), $
where if $sigma=(x_0<dots<x_r)$, then $sigma_i=(x_0<dots<hat(x)_i<dots<x_r)$ is
the _i-th face_ of $sigma$, for $0<=i<=r$; as usual, $hat(x)_i$ denotes the
omission of $x_i$. The vector space $C_r lr((X))$ is called the _vector space of
r-chains_, where an r-chain is a formal linear combination of r-simplices with
coefficients in $K$. It is easily verified that $partial^2=0$, so that $C(X)$ is
indeed a chain complex with $G$-action, and the resulting homology
representation
$ H_ast lr((X))=plus.o.big_(r=0)^infinity H_r lr((X)), $
where $H_r lr((X))$ means $H_r lr((C(X)))$, is called the _homology
representation associated with the $G$-poset $X$_.

The preceding discussion shows that the homology modules ${H_r lr((X))}$
associated with a $G$-poset $X$ are the same as the $K G$-modules arising from
the homology of the simplicial complex $Sigma X$, over the field $K$. These
homology modules, in turn, coincide with the singular homology modules of the
underlying topological space $|X|$, with the $G$-action defined as above. In
particular, these #source(610) remarks imply, by
@prop:second-subdivision-regular and @prop:barycentric-subdivision-realization,
that a $G$-poset $X$ and its barycentric subdivision $op("Sd") X$ afford the
same homology representations, so there is no loss of generality in restricting
our discussion to homology representations associated with regular $G$-posets
(see @def:regular-group-poset).

We now seek to define the character of a homology representation
$H_ast lr((X))$, whose properties should generalize those of the permutation
character associated with a $G$-set. (For example, we recall that the value of a
permutation character on $g in G$ is the number of fixed points of $g$ (see
Exercise~@i:exc:permutation-character-orbits).) This new type of character, the
_Lefschetz character_, is defined as follows:

#definition[
  Let $X$ be a $G$-poset. The _Lefschetz character_ of the homology
  representation $H_ast lr((X))$ is the map $Lambda:G arrow.r K$ defined by
  $ Lambda(g)=sum_(r>=0) (-1)^r tr(g, H_r lr((X))). $
  The _degree_ $Lambda(1)$ of the Lefschetz character is called the _Euler
  characteristic_ of $X$, and is denoted by $chi(X)$.
] <def:lefschetz-character-euler-characteristic>
#idx(
  "Lefschetz character",
  target: [@def:lefschetz-character-euler-characteristic],
)
#idx(
  "Euler characteristic",
  target: [@def:lefschetz-character-euler-characteristic],
)
#nidx(
  "$Lambda$",
  "Lefschetz character of a homology representation",
  target: [@def:lefschetz-character-euler-characteristic],
)

Here we assume, as usual, that $X$ and $G$ are finite, so that the homology
spaces ${H_r lr((X)),r>=0}$ are f.d./$K$, and are 0 for all sufficiently large
$r$, so $Lambda$ is well defined. We note that if $K$ is a field of
characteristic zero, then the Lefschetz character is a virtual $K$-character of
$G$, by Volume I, §~@i:ss:finite-group-character-orthogonality, following
Proposition~@i:prop:irreducible-group-characters-independent. In this case, the
homology representation over $K$ is obtained by extension of the base field from
the homology representation with coefficients in the rational field $QQ$, and
the Euler characteristic coincides with the alternating sum
$ sum_(r=0)^infinity (-1)^r dim H_r lr((X)). $
This is the usual Euler characteristic $chi(|X|)$ of the underlying topological
space $|X|$.

The computation of the Lefschetz character is transferred to the chain modules
$C_r lr((X))$ by means of the next result.

#theorem(name: [Hopf Trace Formula])[
  Let $C=plus.o.big_(r>=0) C_r$ be a chain complex over a field $K$, with
  boundary map $partial$, such that each subspace $C_r$ is f.d./$K$, and $C_r=0$
  for all sufficiently large $r$. Let $f:C arrow.r C$ be a graded chain map of
  degree zero, that is, a $K$-endomorphism $f:C arrow.r C$ such that
  $f(C_r) subset.eq C_r$ for each $r>=0$, and $f partial=partial f$. Then $f$
  induces a $K$-endomorphism $f_ast$ of $H_ast lr((C))$ such that
  $f_ast lr((H_r lr((C)))) subset.eq H_r lr((C))$ for all $r$, and we have
  $
    sum_(r=0)^infinity (-1)^r tr(f, C_r)
    =sum_(r=0)^infinity (-1)^r tr(f_ast, H_r lr((C))).
  $
] <th:hopf-trace-formula>
#idx("Hopf Trace Formula", target: [@th:hopf-trace-formula])

#proof[
  #source(611)
  For each $r>=0$, let $partial_r$ denote $partial|_(C_r)$. Now keep $r$ fixed,
  and set
  $ Z_r=ker partial_r, quad B_r=im partial_(r+1), $
  so
  $ B_r subset.eq Z_r subset.eq C_r $
  since $partial^2=0$. Both $B_r$ and $Z_r$ are $f$-stable, since $f$ commutes
  with $partial$. Therefore
  $ tr(f, C_r)=tr(f, C_r/Z_r)+tr(f, Z_r/B_r)+tr(f, B_r). $
  The surjection $partial_r:C_r arrow.r B_(r-1)$ has kernel $Z_r$, so we have
  $C_r/Z_r approx B_(r-1)$ as $f$-modules. Therefore
  $ tr(f, C_r/Z_r)=tr(f, B_(r-1)). $
  Since $Z_r/B_r=H_r lr((C))$, we obtain
  $ tr(f, C_r)=tr(f, H_r lr((C)))+tr(f, B_(r-1))+tr(f, B_r). $
  Substituting this expression for $tr(f, C_r)$ into the alternating sum
  $sum (-1)^r tr(f, C_r)$, we easily obtain the desired formula.
]

#corollary[
  Let $K$ be a field of characteristic zero. Then the Euler characteristic
  $chi(X)$ of a $G$-poset $X$ is given by
  $ chi(X)=sum_(r=0)^infinity (-1)^r dim C_r lr((X)), $
  where $C_r lr((X))$ is the vector space of r-chains, for $r>=0$.
] <cor:euler-characteristic-chain-count>

We now have:

#proposition[
  Let $X$ be a $G$-poset, and $Lambda$ the Lefschetz character of the homology
  representation $H_ast lr((X))$ of $G$. Then we have
  $ Lambda(g)=chi(X^g)=chi(|X|^g), quad "for each" g in G. $
  In other words, the value of the Lefschetz character at $g in G$ is the Euler
  characteristic of the fixed point set $|X|^g$.
] <prop:lefschetz-character-fixed-point-euler>

#proof[
  Let $g in G$. Since the action of $g$ commutes with the boundary map
  $partial$, we have
  $ Lambda(g)=sum (-1)^r tr(g, C_r lr((X))) $
  #source(612) by the Hopf trace formula. On each vector space $C_r lr((X))$,
  $g$ acts as a permutation of the basis elements, so by
  Exercise~@i:exc:permutation-character-orbits, $tr(g, C_r lr((X)))$ is the
  number of r-chains $sigma=(x_0<dots<x_r)$ fixed by $g$. By
  @prop:poset-fixed-point-realization, the r-chains fixed by $g$ are the
  r-chains of the fixed point poset $X^g$, and so we have
  $ Lambda(g)=chi(X^g) $
  by Corollary~@cor:euler-characteristic-chain-count. Finally,
  $chi(X^g)=chi(|X|^g)$ by the second part of
  @prop:poset-fixed-point-realization, since $|X^g|$ is homeomorphic to $|X|^g$.
]

Note how the preceding result extends, in a profound way, the result of
Exercise~@i:exc:permutation-character-orbits for permutation characters. The
value of a permutation character counts the number of fixed points; the value of
the Lefschetz character “counts” the fixed point set on the underlying
topological space, provided we use the Euler characteristic instead of
cardinality.

In our introduction to homology representations, the last main topic is an
interpretation of the endomorphism algebra $End_(K G) H_ast lr((X))$, for a
field $K$ of characteristic zero and a $G$-poset $X$. We first require an
analogue of Maschke's Theorem for chain complexes (see @i:th:maschke).

#proposition[
  Let $G$ be a finite group, and let $(C,partial)$ be a chain complex over a
  field $K$ with $G$-action, where $|G|!=0$ in $K$. As usual, let
  $op("inv")_G C={x in C:g x=x,g in G}$. Then $(op("inv")_G C,partial)$ is also
  a chain complex, and there is an isomorphism of graded vector spaces:
  $ op("inv")_G H_ast lr((C)) approx H_ast lr((op("inv")_G C)). $
] <prop:homology-invariants-exact>

#proof[
  Since $partial$ commutes with the action of $G$, $op("inv")_G C$ is stable
  under the action of $partial$. Therefore $op("inv")_G C$ is a chain complex,
  with graded components $op("inv")_G C_r$, $r>=0$, and with boundary map given
  by the restriction of $partial$ to $op("inv")_G C$. Let $Z=ker partial$,
  $B=im partial$ in $C$; then the $G$-action on $H_ast lr((C))=Z/B$ is given by
  $ g(z+B)=g z+B, quad z in Z, quad g in G. $
  Clearly $z+B in op("inv")_G H_ast lr((C))$ if and only if
  $g z equiv z (mod B)$ for all $g in G$. It follows that there is an injective
  $K$-homomorphism
  $ phi:H_ast lr((op("inv")_G C)) arrow.r op("inv")_G H_ast lr((C)), $
  given by
  $
    phi lr((z+partial(op("inv")_G C)))=z+B,
    quad z in op("inv")_G Z.
  $
  To check this, we need only verify that
  $ B inter op("inv")_G Z subset.eq partial(op("inv")_G C). $
  #source(613)
  Let $z$ be an element of this intersection; since $B=partial C$, we may write
  $z=partial c$ for some $c in C$. But then
  $
    z=|G|^(-1) sum_(g in G) g z
    =partial lr((|G|^(-1) sum_(g in G) g c)) in partial(op("inv")_G C),
  $
  since $partial$ commutes with the action of $G$.

  It remains to prove $phi$ surjective, and for this we must show that if
  $z in Z$ satisfies
  $ g z equiv z (mod B) quad "for all" g in G, $
  then $z+b in op("inv")_G Z$ for some $b in B$. We may write
  $ g z=z+b_g quad "with" b_g in B, quad "for all" g in G. $
  Then we have
  $ |G|^(-1) sum_(g in G) g z=z+|G|^(-1) sum_(g in G) b_g in z+B. $
  Choosing $b=|G|^(-1) sum b_g in B$, we obtain $z+b in op("inv")_G Z$,
  completing the proof.
]

This result can be applied to $G$-posets, and yields:

#proposition[
  Let $X$ be a regular $G$-poset, and let $C(X)$ be the chain complex of $X$
  over a field $K$ of characteristic zero. Then there is an isomorphism of chain
  complexes:
  $ op("inv")_G C approx C(overline(X)), $
  where $C(overline(X))$ is the chain complex over $K$ associated with the orbit
  poset $overline(X)=G backslash X$. Further, there is an isomorphism of graded
  vector spaces:
  $ op("inv")_G H_ast lr((X)) approx H_ast lr((overline(X))). $
] <prop:regular-orbit-poset-homology>

#proof[
  We first define a $K$-linear map $phi:C(X) arrow.r C(overline(X))$ with the
  properties that $phi$ commutes with the boundary maps in the two chain
  complexes, and $phi(g a)=phi(a)$ for all $g in G$, $a in C(X)$. The map $phi$
  is defined on a basis of $C(X)$, and sends $c_sigma$ to $c_(overline(sigma))$,
  where $sigma=(x_0<dots<x_r)$ is an r-simplex in $Sigma(X)$, and
  $overline(sigma)=(overline(x)_0<dots<overline(x)_r)$ is the corresponding
  r-simplex in $Sigma(overline(X))$. We leave it to the reader to check that
  $phi$ has the desired properties.

  Now consider $op("inv")_G C(X)=plus.o.big_(r>=0)
  op("inv")_G C_r lr((X))$. For fixed $r>=0$, $G$ acts as a permutation group on
  the basis ${c_sigma}$ of the vector space of r-chains $C_r lr((X))$. Therefore
  $op("inv")_G C_r lr((X))$ has a basis consisting of elements
  $sum_(sigma in overline(sigma)) c_sigma$, where ${overline(sigma)}$ ranges
  over the $G$-orbits of r-simplices in $Sigma X$ (see
  Exercise~@i:exc:permutation-character-orbits(ii)). Letting $phi_1$ be the
  restriction of $phi$, it follows that the map
  $phi_1:op("inv")_G C(X) arrow.r C(overline(X))$ is an isomorphism, since for
  each orbit $O$ of r-chains we have
  $phi_1 lr((sum_(sigma in O) c_sigma))=abs(O)c_(overline(O))$, where
  $overline(O)$ is the corresponding quotient chain and $abs(O)$ is invertible
  in characteristic zero; these orbits correspond bijectively to quotient chains
  #source(614) by Proposition~@prop:regular-poset-subdivision-orbits.#ed-note[
    For a two-point set exchanged by $C_2$, the quotient map identifies the two
    vertex basis vectors, whereas their invariant sum maps to twice the quotient
    vertex. Thus the asserted bijection on the full chain bases does not hold.
  ] Since $phi_1$ commutes with the boundary maps in $C(X)$ and
  $C(overline(X))$, respectively, the first part of the proposition is
  established. The second part follows immediately from
  @prop:homology-invariants-exact, completing the proof.
]

We also require the connection between the homology $H_ast lr((X times Y))$ of
the cartesian product $X times Y$ of two $G$-posets $X$ and $Y$, and the
homology of the factors $H_ast lr((X))$ and $H_ast lr((Y))$. Suppose first that
$M=plus.o.big_(r>=0) M_r$ and $N=plus.o.big_(s>=0) N_s$ are two graded vector
spaces over $K$, such that the subspaces ${M_r}$ and ${N_s}$ are $K G$-modules,
for a finite group $G$. Then $M times.o N$ has a natural structure as a graded
$K G$-module, given by
$ M times.o N=plus.o.big_(t>=0) (M times.o N)_t, $
where for each $t$,
$ (M times.o N)_t=plus.o.big_(r+s=t) M_r times.o N_s, $
and where each submodule $M_r times.o N_s$ is the inner tensor product of
$K G$-modules (Definition~@i:def:outer-inner-tensor-products). We then have:

#proposition[
  Let $X$ and $Y$ be $G$-posets, and $X times Y$ their cartesian product (as in
  @def:group-poset-cartesian-product). Let $K$ be an arbitrary field. There is
  an isomorphism of graded $K G$-modules
  $ H_ast lr((X times Y)) approx H_ast lr((X)) times.o H_ast lr((Y)), $
  such that for each $r>=0$,
  $
    H_r lr((X times Y)) approx
    plus.o.big_(j=0)^r H_j lr((X)) times.o H_(r-j) lr((Y))
  $
  as $K G$-modules.
] <prop:equivariant-homology-kunneth>

The proof depends on the Eilenberg–Zilber theorem and the theory of acyclic
models, and is given in Godement (@bib:Godement1964).

We now come to the main result of this subsection, which we will apply in
§~@ss:combinatorial-building-steinberg-representation to homology
representations of finite groups with $B N$-pairs.

#theorem[
  Let $H_ast lr((X))$ be a homology representation of a finite group $G$ over
  the field of rational numbers $QQ$, associated with a regular $G$-poset $X$.
  Then $X times X$ is a regular $G$-poset, and there is an isomorphism of graded
  vector spaces over $QQ$:
  $ H_ast lr((G backslash (X times X))) approx End_(QQ G) H_ast lr((X)), $
  #source(615) where $G backslash (X times X)$ is the orbit poset of the regular
  $G$-poset $X times X$. The isomorphism is such that for each $r>=0$,
  $
    H_r lr((G backslash (X times X))) approx
    plus.o.big_(j=0)^r Hom_(QQ G) lr((H_j lr((X)),H_(r-j) lr((X)))).
  $
] <th:homology-endomorphisms-orbit-product>

#proof[
  We first remark that by @i:rem:contragredient-actions, any f.d. $QQ G$-module
  $M$ is isomorphic to its contragredient module $M^*$, since the character
  afforded by $M$ is real-valued. Upon identifying $M$ with $M^*$, we then have
  $ M times.o_QQ N=Hom_QQ lr((M,N)) $
  for each $QQ G$-module $N$, and there is an isomorphism of vector spaces:
  $ op("inv")_G M times.o_QQ N approx Hom_(QQ G) lr((M,N)), $
  by @i:prop:contragredient-hom-tensor and @i:prop:invariants-induction-hom(ii).

  Now consider the homology representation $H_ast lr((X))$. It follows at once
  from the definitions that $X times X$ is regular. We have, by
  @prop:equivariant-homology-kunneth,
  $
    H_r lr((X times X)) approx
    plus.o.big_(j=0)^r H_j lr((X)) times.o H_(r-j) lr((X))
    quad "for" r>=0.
  $
  Since $X times X$ is regular, we have
  $
    H_ast lr((G backslash (X times X)))
    approx op("inv")_G H_ast lr((X times X)),
  $
  so for each $r>=0$, we obtain from @prop:regular-orbit-poset-homology
  $
    H_r lr((G backslash (X times X))) approx
    op("inv")_G H_r lr((X times X)) approx
    plus.o.big op("inv")_G (H_j lr((X)) times.o H_(r-j) lr((X))).
  $
  Finally, by the remark at the beginning of the discussion, there is an
  isomorphism of vector spaces over $QQ$:
  $
    op("inv")_G H_j lr((X)) times.o H_(r-j) lr((X))
    approx Hom_(QQ G) lr((H_j lr((X)),H_(r-j) lr((X))))
  $
  for $0<=j<=r$, completing the proof.
]

The preceding theorem is the first step toward the study, from the geometrical
point of view, of the $QQ G$-endomorphism algebra of a homology representation,
and is already quite powerful, as we shall see later in the section. The theory
is still incomplete, however. What is needed is a better geometrical
understanding of the multiplication in $End_(QQ G) H_ast lr((X))$. For example,
in the case of a permutation representation, there is an explicit description of
the multiplication in the endomorphism algebra in terms of the intersection
numbers ${mu_(i j k)}$ of the Hecke #source(616) algebra, as in
@i:prop:permutation-hecke-formulas. A generalization of this description is
still missing in the case of homology representations.

=== The Coxeter Poset of a Finite g.g.r.
<ss:coxeter-poset-finite-reflection-group>

Let $Delta$ be a root system in an n-dimensional euclidean space $V$, and let
$W=W(Delta)$ be the finite g.g.r. associated with $Delta$, as in
§~@ss:finite-reflection-root-systems. Since $W subset.eq O(V)$, $W$ acts on the
unit sphere $S^(n-1)$ in $V$. In this subsection, we shall prove that $S^(n-1)$
is the geometric realization $|Gamma|$ of a $W$-poset $Gamma$, called the
Coxeter poset of $W$, and will determine the homology representation of $W$ on
$Gamma$. By §~@ss:coxeter-groups, every finite Coxeter group is isomorphic to a
g.g.r., so the discussion applies to an arbitrary finite Coxeter group.

Following Steinberg @bib:Steinberg1967, we begin with the determination of a
#idx("Fundamental domain")fundamental domain for the action of $W$ on $V$. As in
§~@ss:finite-reflection-root-systems, we let $Delta_plus.minus$ denote the sets
of positive (resp. negative) roots associated with a fundamental system $Pi$
(see @def:fundamental-root-system).

#definition[
  Let $Pi$ be a fundamental system in $Delta$. The (closed) _chamber_ $D$ in $V$
  associated with $Pi$ is the set
  $ D={xi in V:(xi,alpha)>=0 quad "for all" alpha in Pi}. $
  The _faces_ of the chamber $D$ are the subsets $D_I$, $I subset Pi$, defined
  by
  $ D_I={xi in D:(xi,alpha)=0 quad "for all" alpha in I}. $
] <def:coxeter-chamber-faces>
#idx("Chamber", target: [@def:coxeter-chamber-faces])

The chamber $D$ is a closed convex cone with vertex at 0, and will turn out to
be a fundamental domain for the action of $W$ on $V$.

#lemma[
  Every $xi in V$ is in the $W$-orbit of some $xi' in D$.
] <lem:chamber-meets-every-orbit>

#proof[
  We introduce a partial order $<=$ on $V$, with $delta<=delta'$ if either
  $delta=delta'$ or $delta'-delta$ is in the positive span of $Pi$. The
  $W$-conjugates $xi''$ of $xi$, form a finite set, since $|W|<infinity$, so we
  can choose one which is maximal in the partial ordering. Now let
  $alpha in Pi$. Then $s_alpha xi'$ is a $W$-conjugate of $xi$, and
  $ s_alpha xi'=xi'-2(xi',alpha)(alpha,alpha)^(-1) alpha, $
  so $(xi',alpha)>=0$, since otherwise $s_alpha xi'>xi'$, contrary to the
  selection of $xi'$. Thus $xi' in D$, and the lemma is proved.
]

#lemma[
  Let $xi,eta in D$, $w in W$, and assume $w xi=eta$. Then:
  #case-list(
    numbering: "(i)",
    [#case[$w$ is a product of fundamental reflections ${s_alpha}$ such that
      $s_alpha xi=xi$, and] <case:chamber-orbit-stabilizer-reflections>],
    [#case[$xi=eta$.] <case:chamber-orbit-uniqueness>],
  )
] <lem:chamber-orbit-stabilizer-uniqueness>

#proof[
  We first recall (see @def:reflection-length-inversions and
  @th:reflection-length-cancellation-exchange) that
  $N(w)=op("card"){alpha in Delta_+:w alpha in Delta_-}$, and that $N(w)=l(w)$.
  We prove @lem:chamber-orbit-stabilizer-uniqueness using induction on $N(w)$,
  the result being trivial for $N(w)=0$. Now assume that $N(w)>0$, and choose
  #source(617) $alpha in Pi$ such that $w alpha in Delta_-$. Since $eta in D$,
  we obtain
  $ 0>=(eta,w alpha)=(w xi,w alpha)>=0, $
  whence $(xi,alpha)=0$, and $s_alpha xi=xi$. Then $w s_alpha xi=eta$ and
  $N(w s_alpha)<N(w)$ by @th:reflection-length-cancellation-exchange. We can
  therefore apply the induction hypothesis to $w s_alpha$ to obtain
  part~@case:chamber-orbit-stabilizer-reflections. Statement
  @case:chamber-orbit-uniqueness follows from
  part~@case:chamber-orbit-stabilizer-reflections.
]

In stating the next result, the symbol $I$ will denote a proper subset of $Pi$,
and will also denote the corresponding subset of the fundamental reflections, so
that $W_I$ is the parabolic subgroup of $W$ defined by this set of reflections
(see §~@ss:finite-coxeter-parabolic-subgroups).

#theorem[
  #case-list(
    numbering: "(i)",
    [#case[
      $D$ is a fundamental domain for the action of $W$ on $V$, in the sense
      that every element of $V$ is in the $W$-orbit of a unique element of $D$.
    ] <case:chamber-fundamental-domain>],
    [#case[
      Let $I$ be a subset of $Pi$, and $D_I$ the corresponding face of $D$, as
      in @def:coxeter-chamber-faces. Then the following three subgroups of $W$
      coincide:
      #case-list(
        numbering: "(a)",
        [#case[${w in W:w D_I=D_I}$, the stabilizer of the set $D_I$,]
          <case:chamber-face-set-stabilizer>],
        [#case[${w in W:w xi=xi,forall xi in D_I}$, the point-stabilizer of
          $D_I$, and] <case:chamber-face-point-stabilizer>],
        [#case[$W_I=chevron.l s_alpha:alpha in I chevron.r$, the parabolic
            subgroup of $W$ corresponding to $I$.]
          <case:chamber-face-parabolic-stabilizer>],
      )
    ] <case:chamber-face-stabilizers>],
  )
] <th:chamber-fundamental-domain-stabilizers>

#proof[
  @case:chamber-fundamental-domain By @lem:chamber-meets-every-orbit, each
  element of $V$ is conjugate to some element of $D$, and this element is unique
  by Lemma~@lem:chamber-orbit-stabilizer-uniqueness,
  part~@case:chamber-orbit-uniqueness.

  @case:chamber-face-stabilizers By
  Lemma~@lem:chamber-orbit-stabilizer-uniqueness, the point and set stabilizers
  of $D_I$ coincide, and are contained in the parabolic subgroup $W_I$, by
  @lem:chamber-orbit-stabilizer-uniqueness,
  part~@case:chamber-orbit-stabilizer-reflections. Conversely, it is clear that
  any element of $W_I$ fixes every vector in $D_I$, and the theorem is proved.
]

#corollary[
  #case-list(
    numbering: "(i)",
    [#case[
      Let $Pi$ be a fundamental system in $Delta$, and $D$ the chamber
      associated with $Pi$. For each $w in W$, $w D$ is the chamber associated
      with the fundamental system $w Pi$, and $V$ is the union of the chambers
      ${w D}$. The interiors ${op("int")(w D)}_(w in W)$, of the chambers
      ${w D}$ form a partition of the open set
      $ V-union.big_(alpha in Delta) H_alpha, $
      where for $alpha in Delta$, $H_alpha$ is the hyperplane
      $chevron.l alpha chevron.r^perp$.
    ] <case:coxeter-chambers-partition-regular-vectors>],
    [#case[
      The faces of the chamber $w D$, $w in W$, are the translates ${w D_I}$ of
      the faces ${D_I,I subset Pi}$, of $D$. Their stabilizers are the parabolic
      subgroups $w W_I w^(-1)$, $I subset Pi$.
    ] <case:translated-chamber-face-stabilizers>],
  )
] <cor:coxeter-chambers-faces>

#corollary[
  The map $w D_I arrow.r w W_I$, $w in W$, $I subset Pi$, is a bijection from
  the set of faces of the chambers ${w D}_(w in W)$ to the set of left cosets of
  the parabolic subgroup $W_I$. Moreover,
  $
    w D_I subset.eq w' D_(I') arrow.l.r w W_I supset.eq w' W_(I'),
    quad "for" w,w' in W quad "and" I,I' subset Pi.
  $
] <cor:chamber-face-parabolic-cosets>

#source(618)
Both @cor:coxeter-chambers-faces and @cor:chamber-face-parabolic-cosets follow
from the preceding discussion, especially
Lemma~@lem:chamber-orbit-stabilizer-uniqueness, and their proofs are left as
exercises. The following definition is suggested by these results.

#definition[
  Let $(W,S)$ be a finite Coxeter system, with $|S|>=2$. The _Coxeter poset_
  $Gamma$ is the $W$-poset consisting of all left cosets
  $ {w W_I:w in W,I subset S}, $
  ordered by inclusion. The action of $W$ on $Gamma$ is given by left
  translation: for $x in W$,
  $ w W_I arrow.r x w W_I quad "for all" w in W, quad I subset S. $
] <def:coxeter-poset>
#idx("Coxeter poset", target: [@def:coxeter-poset])

It is easily checked that $Gamma$ satisfies the definition of a $W$-poset, from
§~@ss:finite-group-homology-representations. The restriction $|S|>=2$ excludes
the trivial case $|W|=2$.

The results so far obtained give a geometric interpretation of the parabolic
subgroups of $W$. They lead us, in turn, to the homology representation of $W$
on $H_ast lr((Gamma))$. In particular, for $n=|S|$, $H_(n-1) lr((Gamma))$
affords the sign representation of $W$, defined below.

#definition[
  Let $(W,S)$ be a finite Coxeter system. The _sign representation_ $epsilon$ of
  $W$ is the representation $epsilon:W arrow.r QQ^dot$ of degree 1, defined
  uniquely by
  $ epsilon(s)=-1 quad "for all" s in S. $
] <def:coxeter-sign-representation>
#idx("Sign representation", target: [@def:coxeter-sign-representation])

It is clear from Definition~@def:finite-coxeter-system that the map $epsilon$,
given above, preserves the defining relations of $W$, and does indeed extend to
a linear representation $epsilon:W arrow.r QQ^dot$. In case $(W,S)$ is realized
as a finite g.g.r. associated with a root system in a euclidean space, then we
clearly have
$ epsilon(w)=det w quad "for all" w in W, $
<eq:coxeter-sign-determinant>
since the determinant of a reflection is $-1$.

We now have:

#theorem[
  Let $Delta$ be a root system in $V$, and $(W,S)$ the Coxeter system associated
  with $Delta$, where $W=W(Delta)$, and $S$ is the set of reflections associated
  with a fundamental system $Pi subset.eq Delta$. Let $n=|S|=dim V$, and assume
  $n>=2$. Then the following statements hold:
  #case-list(
    numbering: "(i)",
    [#case[
      The group $W$ acts on the unit sphere#footnote[
        The sphere $S^(n-1)$ is the set of vectors $xi in V$ such that
        $norm(xi)=(xi,xi)^(1/2)=1$.
      ] <fn:unit-sphere>
      $S^(n-1)$ in $V$, and there is a $W$-equivariant homeomorphism
      $ |Gamma| approx S^(n-1), $
      #source(619) where $|Gamma|$ is the underlying topological space of the
      Coxeter poset $Gamma$ associated with the Coxeter system $(W,S)$.
    ] <case:coxeter-complex-sphere>],
    [#case[
      The homology representation of $W$ on $H_ast lr((Gamma))$, over the
      rational field $QQ$, is given as follows: $H_i lr((Gamma))=0$ except in
      dimensions 0 and $n-1$. Moreover $H_0 lr((Gamma))$ affords the trivial
      representation $1_W$, while $H_(n-1) lr((Gamma))$ affords the sign
      representation $epsilon$.
    ] <case:coxeter-complex-homology-sign>],
  )
] <th:coxeter-poset-sphere-homology>
#nidx(
  "$|Gamma|$",
  "geometric realization = underlying topological space",
  target: [@th:coxeter-poset-sphere-homology],
)

#proof[
  Since $W$ is a group of orthogonal transformations, $W$ clearly acts on the
  sphere $S^(n-1)$. We now give an outline of the proof that
  $|Gamma| approx S^(n-1)$, leaving some points to be verified by the reader. (A
  more detailed discussion is given in Bourbaki @bib:Bourbaki1968, Ch. 5.) Let
  $D$ be the chamber in $V$ defined by $Pi$, as in @def:coxeter-chamber-faces.
  It is easily verified, using the fact that $Pi$ is a basis of $V$, that the
  hyperplanes ${H_alpha=chevron.l alpha chevron.r^perp:alpha in Pi}$ are the
  _walls_ of $D$, in the sense that $H_alpha inter D$ is contained in the
  boundary of $D$, and generates the vector space $H_alpha$. The same argument
  shows that each face $D_I=D inter H_(alpha_(i_1)) inter dots inter
  H_(alpha_(i_q))$, where $I={alpha_(i_1),...,alpha_(i_q)} subset Pi$, generates
  a subspace of $V$ of dimension $n-|I|$. Using the discussion in
  §~@ss:finite-group-homology-representations, it is then readily shown that the
  intersection $D inter S^(n-1)$ is homeomorphic to the underlying topological
  space of an (abstract) $(n-1)$-simplex $sigma$. The vertices of $sigma$
  correspond to the intersections $D_I inter S^(n-1)$, for $|I|=n-1$,
  $I subset Pi$, since for such $I$, each face $D_I$ is a half-line and
  intersects $S^(n-1)$ in a point. These points support a spherical simplex
  homeomorphic to $|sigma|$. The k-dimensional faces of $sigma$, $0<=k<=n-1$,
  are realized by the intersections $D_K inter S^(n-1)$, with $|K|=n-k-1$,
  $K subset.eq Pi$.

  By @cor:coxeter-chambers-faces, $S^(n-1)$ is the union of the intersections
  ${w D inter S^(n-1)}_(w in W)$, and their interiors partition the set
  $S^(n-1)-union.big_(alpha in Delta) H_alpha$. By the first paragraph, each
  such intersection is homeomorphic to $|sigma|$. These intersections
  ${w D inter S^(n-1)}_(w in W)$, and their faces
  ${w D_I inter S^(n-1)}_(w in W)$, where $I subset Pi$, form a $W$-poset under
  inclusion, with $W$-action given by left translation. By
  @cor:chamber-face-parabolic-cosets, this poset is isomorphic, as a $W$-poset,
  to the opposite poset $Gamma^degree$ of the Coxeter poset. By
  @cor:chamber-face-parabolic-cosets, the simplicial complex $Sigma(Gamma)$ is
  $W$-isomorphic to the barycentric subdivision of the simplicial complex whose
  geometric realization is $S^(n-1)$. Then by
  @prop:barycentric-subdivision-realization, there is a $W$-equivariant
  homeomorphism $|Gamma| approx S^(n-1)$, completing the proof of
  part~@case:coxeter-complex-sphere.

  @case:coxeter-complex-homology-sign Since $|Gamma| approx S^(n-1)$ by
  part~@case:coxeter-complex-sphere, we have
  $
    H_i lr((Gamma))=0, quad i!=0,n-1,
    quad H_0 lr((Gamma)) approx H_(n-1) lr((Gamma)) approx QQ,
  $
  by the standard result on the homology of the $(n-1)$-sphere $S^(n-1)$
  (Eilenberg–Steenrod @bib:Eilenberg1952, Theorem I.16.6). We leave it to the
  reader to prove that $H_0 lr((Gamma))$ affords the trivial representation of
  $W$.

  We now prove, using the Lefschetz character and
  Proposition~@prop:lefschetz-character-fixed-point-euler, that
  $H_(n-1) lr((Gamma))$ affords the sign representation. From what has been
  shown so far, the Lefschetz character $Lambda$ of $H_ast lr((Gamma))$ is given
  by
  $ Lambda=1_W+(-1)^(n-1) tr(dot, H_(n-1) lr((Gamma))). $
  Now let $s$ be an arbitrary reflection in $W$. Then the fixed point set
  $|Gamma|^s approx (S^(n-1))^s$ is #source(620) homeomorphic to an
  $(n-2)$-sphere, whose Euler characteristic is $1+(-1)^(n-2)$. By
  @prop:lefschetz-character-fixed-point-euler, we have
  $ Lambda(s)=1+(-1)^(n-2), $
  and comparing this formula with the general expression for $Lambda$, we obtain
  $ tr(s, H_(n-1) lr((Gamma)))=-1, $
  which completes the proof that $H_(n-1) lr((Gamma))$ affords the sign
  representation.
]

#corollary(title: [Solomon @bib:Solomon1966])[
  Let $epsilon$ be the sign character of a finite Coxeter group $W$. Then
  $ epsilon=sum_(J subset.eq S) (-1)^|J| (1_(W_J))^W. $
] <cor:solomon-sign-character-formula>
#idx("Solomon's Theorem", target: [@cor:solomon-sign-character-formula])

#proof[
  We apply the Hopf Trace Formula @th:hopf-trace-formula to the homology
  representation $H_ast lr((Gamma))$. From the proof of
  Theorem~@th:coxeter-poset-sphere-homology, the homology of $Gamma$ can be
  computed from a chain complex $C=plus.o.big_(r>=0) C_r$, where the vector
  space $C_r$ of r-chains has a basis corresponding to the elements of $Gamma$,
  $ {w W_I,|I|=n-r-1}. $
  The group $W$ acts as a permutation group on the basis of $C_r$. Thus we have,
  for each $r>=0$,
  $
    tr(x, C_r)=sum_(|I|=n-r-1) (1_(W_I))^W lr((x)),
    quad "for all" x in W,
  $
  since $(1_(W_I))^W lr((x))$ counts the number of cosets ${w W_I}_(w in W)$
  fixed by $x$, by Exercise~@i:exc:permutation-character-orbits(i). By the Hopf
  Trace Formula and by part~@case:coxeter-complex-homology-sign of the preceding
  theorem, the Lefschetz character $Lambda$ of $H_ast lr((Gamma))$ is given by
  $
    Lambda(x) & =1+(-1)^(n-1) epsilon(x)
                =sum_(r=0)^(n-1) (-1)^r tr(x, C_r) \
              & =sum_(J subset S) (-1)^(n-|J|-1) (1_(W_J))^W lr((x))
                quad "for" x in W.
  $
  Upon solving for $epsilon$, we obtain Solomon's formula.
]

While the formula @cor:solomon-sign-character-formula can perhaps best be
understood in terms of the preceding argument, it is also possible to give a
short direct proof of it, independent of the theory of homology representations
(see Exercise~@exc:solomon-formula-hyperplane-arrangement).

#heading(level: 3)[
  The Combinatorial Building and the Steinberg Representation of a Finite Group
  with a $B N$-Pair
]
<ss:combinatorial-building-steinberg-representation>

#source(621)
Throughout this subsection, $G$ denotes a finite group with a $B N$-pair of rank
$n$, and $W$ the Weyl group of $G$, with $(W,S)$ the Coxeter system in $W$, as
in @th:bn-pair-weyl-coxeter-system. We shall construct an absolutely irreducible
$QQ$-representation $op("St")_G$ of $G$, called the Steinberg representation,
which plays a special role in the representation theory of $G$. In case $n=1$,
the Bruhat decomposition implies that the permutation representation of $G$ on
the cosets $G/B$ of a Borel subgroup is 2-transitive, by
Exercise~@i:exc:doubly-transitive-character, and in this case $op("St")_G$ is
defined as the unique nontrivial irreducible component of this permutation
representation (see Exercise~@i:exc:doubly-transitive-character(ii), and Volume
I, §~@i:ss:brauer-character-orthogonality, Example (ii) following
Proposition~@i:prop:defect-zero-character-projective-simple, for the groups
$SL_2 lr((q))$). In case $n>1$, there is no straightforward construction of
$op("St")_G$ by the methods of Volume I, and it is for this reason that we have
introduced homology representations in this section. We shall exhibit
$op("St")_G$ as a homology representation on a $G$-poset with vanishing homology
except in two dimensions, in much the same way as the sign representation of $W$
was realized on the homology of $Gamma$ in the preceding section.

#definition(title: [Tits @bib:Tits1974])[
  The _combinatorial building_ $Delta$ of a finite group $G$ with a $B N$-pair
  of rank $n>1$ is the $G$-poset of all proper parabolic subgroups of $G$ (see
  @def:bn-pair-parabolic-subgroups), ordered by inclusion, with the $G$-action
  given by conjugation:
  $
    P arrow.r attach(P, tl: g)=g P g^(-1),
    quad "for" g in G, quad P in Delta.
  $
] <def:combinatorial-building>
#idx("Combinatorial building", target: [@def:combinatorial-building])

Our aim is to calculate the homology $H_ast lr((Delta))$ over the rational field
$QQ$, and the nature of the homology representations it affords. The main result
is due to Solomon and Tits (Solomon @bib:Solomon1969), and was also proved by
Garland @bib:Garland1973, using the determination of the homotopy type of the
underlying topological space $|Delta|$. We shall give a new proof, due to
Curtis–Lehrer @bib:CurtisLehrer1982, based on a comparison of the endomorphism
algebras of $H_ast lr((Delta))$ and $H_ast lr((Gamma))$, using
Theorem~@th:homology-endomorphisms-orbit-product, where $Gamma$ is the Coxeter
poset of $W$ (see @def:coxeter-poset). The key to this approach is the following
result, which shows that although $Delta$ and $Gamma$ are posets on which
different groups act, certain orbit posets associated with them have the same
structure.

#lemma[
  Let $G$ be a finite group with a $B N$-pair of rank $n>1$, and let $W$ be the
  Weyl group of $G$. Then the Coxeter poset $Gamma$ of $W$ and the combinatorial
  building $Delta$ of $G$ have the property that#footnote[
    $Gamma^degree$ denotes the opposite poset of $Gamma$ (see
    §~@ss:finite-group-homology-representations).
  ] <fn:opposite-coxeter-poset>
  $Gamma^degree$ and $Delta^degree$ are regular $W$- and $G$-posets,
  respectively. Moreover, there is an isomorphism of posets
  $ W backslash (Gamma times Gamma) approx G backslash (Delta times Delta). $
] <lem:building-coxeter-orbit-product-posets>

#proof[
  To prove that $Gamma^degree$ is regular, we have to show that if
  $x W_I subset.eq y W_J$ and $x W_I subset.eq z W_J$, for $x,y,z in W$, then
  $y W_J=z W_J$. This is clear, however, since the cosets $y W_J$ and $z W_J$
  both contain $x W_I$, and so have a nonempty intersection. The proof #source(
    622,
  ) that $Delta^degree$ is regular is less trivial: we have to show that if $P$
  and $Q$ are parabolic subgroups such that $P subset.eq Q$ and
  $P subset.eq attach(Q, tl: g)$, where $g in G$, then $Q=attach(Q, tl: g)$.
  This is precisely what was established in
  Theorem~@th:bn-pair-parabolic-normalizers-containment, in somewhat greater
  generality.

  It follows that the opposite posets of $Gamma times Gamma$ and
  $Delta times Delta$ are both regular, so the orbit posets
  $W backslash (Gamma times Gamma)$ and $G backslash (Delta times Delta)$ are
  both defined (see @th:homology-endomorphisms-orbit-product). We shall prove
  that both posets are isomorphic to the poset of triples
  $ Omega={(I,J,w),quad I,J subset S,quad w in D_(I J)}, $
  where $D_(I J)$ is a set of d.d.c.r.'s (see
  @def:distinguished-parabolic-double-coset-representative). The order relation
  in $Omega$ is given by
  $ (I,J,w)<=(I',J',w') $
  if and only if
  $
    I subset.eq I',quad J subset.eq J',quad "and"
    W_I w W_J subset.eq W_(I') w' W_(J').
  $

  First consider an orbit $cal(O)$ in $G backslash (Delta times Delta)$; then
  $cal(O)$ contains a representative of the form $(P_I,attach(P_J, tl: g))$ with
  $I,J subset S$ and $g in G$. By @th:bn-pair-parabolic-double-cosets,
  $g in P_I w P_J$ for some $w in D_(I J)$, whence $cal(O)$ contains
  $(P_I,attach(P_J, tl: w))$. We let $cal(O)$ correspond to the triple
  $(I,J,w) in Omega$. Now suppose another orbit
  $cal(O)' in G backslash (Delta times Delta)$ contains a representative
  $(P_(I'),attach(P_(J'), tl: w'))$, with $w' in D_(I' J')$. We shall prove that
  $
    cal(O)<=cal(O)' arrow.l.r I subset.eq I',quad J subset.eq J',
    quad "and" W_I w W_J subset.eq W_(I') w' W_(J').
  $ <eq:building-orbit-product-order>
  The proof is simply a workout with the properties of parabolic subgroups
  established in §~@ss:bn-pair-parabolic-subgroups. We have, for some $g in G$,
  $
    cal(O)<=cal(O)' arrow.l.r
    attach((P_I,attach(P_J, tl: w)), tl: g)
    <=(P_(I'),attach(P_(J'), tl: w'))
    arrow.l.r attach(P_I, tl: g) subset.eq P_(I') quad "and"
    attach((attach(P_J, tl: w)), tl: g)
    subset.eq attach(P_(J'), tl: w').
  $
  By @th:bn-pair-parabolic-normalizers-containment and
  @prop:bn-pair-parabolic-lattice, these conditions are equivalent to:
  $
    I subset.eq I',quad J subset.eq J',quad "and"
    P_I w P_J subset.eq P_(I') w' P_(J').
  $
  By @th:bn-pair-parabolic-double-cosets, the last condition is equivalent to
  $W_I w W_J subset.eq W_(I') w' W_(J')$, which proves statement
  @eq:building-orbit-product-order. It shows, in particular, that each orbit
  corresponds to a unique element of $Omega$, and that the posets
  $G backslash (Delta times Delta)$ and $Omega$ are isomorphic.

  The proof that $W backslash (Gamma times Gamma) approx Omega$ is easier, and
  is left as an exercise for the reader.
]

We now have:

#theorem(title: [Solomon–Tits])[
  Let $Delta$ be the combinatorial building of a finite group with a $B N$-pair
  of rank $n>=2$, and let $H_ast lr((Delta))=plus.o.big_(r>=0) H_r lr((Delta))$
  denote the rational homology of $Delta$. Then $H_r lr((Delta))=0$ except in
  dimensions $r=0$ and $r=n-1$. In these dimensions, $H_0 lr((Delta))$ affords
  the trivial representation, while $H_(n-1) lr((Delta))$ affords an absolutely
  irreducible nontrivial representation.
] <th:solomon-tits-homology>
#idx("Solomon-Tits Theorem", target: [@th:solomon-tits-homology])

#proof[
  #source(623)
  By Lemma~@lem:building-coxeter-orbit-product-posets and two applications of
  Theorem~@th:homology-endomorphisms-orbit-product, there exist isomorphisms of
  graded vector spaces over $QQ$:
  $
    End_(QQ W) H_ast lr((Gamma))
    approx H_ast lr((W backslash (Gamma times Gamma)))
    approx H_ast lr((G backslash (Delta times Delta)))
    approx End_(QQ G) H_ast lr((Delta)).
  $
  By Theorem~@th:coxeter-poset-sphere-homology, we have an isomorphism of vector
  spaces
  $
    End_(QQ W) H_0 lr((Gamma)) approx End_(QQ W) H_(n-1) lr((Gamma))
    approx QQ,
  $
  and
  $
    Hom_(QQ W) lr((H_i lr((Gamma)),H_j lr((Gamma))))=0
    quad "if" i+j!=0,2(n-1).
  $
  Upon carrying these results over to $End_(QQ G) H_ast lr((Delta))$, and
  checking that $H_0 lr((Delta))$ affords the trivial representation, we obtain
  the result. Note that the isomorphism
  $End_(QQ G) H_(n-1) lr((Delta)) approx QQ$ implies, by
  @i:th:absolute-simplicity-centralizer, that the representation of $G$ on
  $H_(n-1) lr((Delta))$ is absolutely irreducible.
]

#definition[
  Let $G$ be a finite group with a $B N$-pair of rank $n$. If $n>1$, the
  _Steinberg representation_ $op("St")_G$ is the nontrivial absolutely
  irreducible $QQ$-representation of $G$ afforded by the rational homology group
  $H_(n-1) lr((Delta))$, where $Delta$ is the combinatorial building of $G$.

  If $n=1$, $op("St")_G$ is the unique nontrivial irreducible component of the
  permutation representation of $G$ afforded by the $G$-set $G/B$.

  The character of $G$ afforded by the Steinberg representation will also be
  denoted by $op("St")_G$.
] <def:steinberg-representation>
#idx("Steinberg representation", target: [@def:steinberg-representation])
#nidx(
  "$op(\"St\")_G$",
  "Steinberg character",
  target: [@def:steinberg-representation],
)

Corresponding to #idx("Solomon's Theorem")Solomon's formula
@cor:solomon-sign-character-formula for the sign representation of $W$, we have
the following formula for the character $op("St")_G$ (see Curtis
@bib:Curtis1966).

#theorem[
  The character $op("St")_G$ of the Steinberg representation of a finite group
  with a $B N$-pair is given by
  $ op("St")_G=sum_(J subset.eq S) (-1)^|J| (1_(P_J))^G. $
] <th:steinberg-alternating-parabolic-character>
#idx(
  "Hopf Trace Formula",
  target: [@th:steinberg-alternating-parabolic-character],
)

#proof[
  As in the proof of @cor:solomon-sign-character-formula, it can be shown (see
  Exercise~@exc:building-maximal-parabolic-complex) that the homology
  $H_ast lr((Delta))$ can be derived from a chain complex
  $C=plus.o.big_(r>=0) C_r$, in which the vector space of r-chains $C_r$ has a
  basis indexed by the parabolic groups of the form $attach(P_I, tl: g)$, with
  $|I|=n-r-1$. Since $N_G lr((P_I))=P_I$ for all $I subset S$ by
  @th:bn-pair-parabolic-normalizers-containment, it follows that for $g in G$,
  $ tr(g, C_r)=sum_(|I|=n-r-1) (1_(P_I))^G lr((g)). $
  The formula for $op("St")_G$ now follows by the Hopf Trace Formula, exactly as
  in the proof of @cor:solomon-sign-character-formula.
]

#source(624)
_Remarks._ A more elementary approach to the formula for the character
$op("St")_G$, independent of the theory of homology representations, was given
by Curtis @bib:Curtis1966, and will be presented in
§~@sec:hecke-algebras-bn-pairs as part of the discussion of the Hecke algebra
$cal(H)(G,B)$. This approach gives the character $op("St")_G$, but not the
module which affords the character. For another construction of the module
affording $op("St")_G$, see Steinberg @bib:Steinberg1956, @bib:Steinberg1957.

For the group $G$ of $bold(F)_q$-rational points on a connected reductive affine
algebraic group defined over a finite field $bold(F)_q$, the values of the
Steinberg character on arbitrary elements of $G$ have been computed using the
Lefschetz character of the homology representation $H_ast lr((Delta))$, together
with Proposition~@prop:lefschetz-character-fixed-point-euler (see
Curtis–Lehrer–Tits @bib:Curtis1980). In §~@sec:character-duality, we shall give
a different approach to the problem of calculating the values of $op("St")_G$,
due to Alvis.

#exercises-heading

#exercise[
  (Steinberg) Let $cal(H)={H_1,...,H_t}$ be a finite set of distinct hyperplanes
  in a real euclidean space $V$, each containing the origin (see
  §~@ss:finite-reflection-root-systems). Let $cal(C)$ denote the set of
  equivalence classes ${c}$ defined by the equivalence relation on $V$ which
  puts $v tilde.op v'$, for $v,v' in V$, provided that, for each hyperplane
  $H_i in cal(H)$, either $v$ and $v'$ both belong to $H_i$, or both lie on the
  same side of $H_i$ (in the sense that $(v,alpha_i)$ and $(v',alpha_i)$ are
  both nonzero and of the same sign, where
  $chevron.l alpha_i chevron.r^perp=H_i$). For each element $c in cal(C)$, let
  $dim c$ be the dimension of the subspace of $V$ generated by the elements of
  $c$. Let $N_i$ denote the number of equivalence classes $c in cal(C)$ of
  dimension $i$, for $i>=0$. Prove that
  $ sum_(i>=0) (-1)^i N_i=(-1)^(dim V). $
] <exc:hyperplane-arrangement-euler-sum>

#hint[@exc:hyperplane-arrangement-euler-sum][
  Use induction on the number of hyperplanes. The proof of the induction step
  goes as follows. Let $cal(H)$ be a set consisting of $t$ hyperplanes, and let
  $cal(H)'$ be a set containing $cal(H)$ and one additional hyperplane $H$. Let
  $cal(C)$ and $cal(C)'$ be the sets of equivalence classes defined by $cal(H)$
  and $cal(H)'$, respectively. Prove that each element $c in cal(C)$ of
  dimension $i$, whose interior is divided into two parts by $H$, yields two
  elements of $cal(C)'$ of dimension $i$ and one element $c inter H in cal(C)'$
  of dimension $i-1$.
] <hint:hyperplane-arrangement-euler-sum>

#exercise[
  Prove Solomon's formula @cor:solomon-sign-character-formula using the
  preceding exercise.
] <exc:solomon-formula-hyperplane-arrangement>

#hint[@exc:solomon-formula-hyperplane-arrangement][
  Let $W=W(Phi)$, for a root system $Phi$ in a real euclidean space $V$. Let
  $cal(H)$ be the set of hyperplanes $chevron.l alpha chevron.r^perp$, for roots
  $alpha in Phi$, and let $cal(C)$ be the set of equivalence classes defined by
  $cal(H)$, as in Exercise~@exc:hyperplane-arrangement-euler-sum. Let $w in W$,
  and let $U={v in V:w v=v}$. Using @th:chamber-fundamental-domain-stabilizers,
  prove that $U$ is the union of all elements $c in cal(C)$ that are fixed by
  $w$. Apply Exercise~@exc:hyperplane-arrangement-euler-sum to $U$, and obtain
  $sum (-1)^i N_i=(-1)^(dim U)$. Using
  @th:chamber-fundamental-domain-stabilizers again, prove that
  $ N_i=sum_(J,n-|J|=i) (1_(W_J))^W lr((w)), quad (n=dim V) $
  for each $i$, and hence
  $ sum_J (-1)^(n-|J|) (1_(W_J))^W lr((w))=(-1)^(dim U). $
  #source(625)
  On the other hand,
  $ det w=(-1)^(n-dim U), $
  by standard properties of orthogonal transformations.
] <hint:solomon-formula-hyperplane-arrangement>

#exercise[
  Let $G$ be a finite group with a $B N$-pair, of rank greater than one. Define
  a simplicial complex $Delta'$ as follows: the vertices of $Delta'$ are the
  maximal parabolic subgroups of $G$, and a set of maximal parabolic subgroups
  defines a simplex in $Delta'$ if and only if their intersection is parabolic.
  Prove the following statements.
  #case-list(
    numbering: "(i)",
    [#case[
      The r-simplices of $Delta'$ form a $G$-set that is isomorphic to the
      $G$-set consisting of all parabolic subgroups $attach(P_I, tl: g)$,
      $|I|=n-r-1$.
    ] <case:building-simplices-parabolic-types>],
    [#case[
      $op("Sd")(Delta') approx Sigma(Delta)$, where $Delta$ is the combinatorial
      building of $G$, and $Sigma(Delta)$ is the simplicial complex associated
      with $Delta$ as in §~@ss:finite-group-homology-representations.
    ] <case:building-complex-subdivision>],
  )
  (For this interpretation of $Delta$, see Tits @bib:Tits1974.)
] <exc:building-maximal-parabolic-complex>
