#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/49-class-groups.typ": *

== Locally Free Class Groups <sec:locally-free-class-groups>

=== Basic Formulas <ss:class-group-basic-formulas>

Throughout this section, let $Lambda$ be an $R$-order in a f.d. separable
$K$-algebra $A$, where $R$ is a Dedekind domain with quotient field $K$. Usually
$K$ will be taken to be a global field. Let $P$ range over the maximal ideals of
$R$, and let $Lambda_P$, $A_P$, etc., denote $P$-adic _completions_ (rather than
localizations at $P$). Further, we denote by $Lambda_P^dot$ the group of units
of $Lambda_P$, and by $A_P^dot$ that of $A_P$.

Let us begin by reviewing some definitions and results from §@i:sec:genus. A
$Lambda$-lattice is a left $Lambda$-module which is f.g. and projective as
$R$-module. For any $Lambda$-lattice $M$, we identify $M$ with its image
$1 times.o M$ in $K times.o_R M$; then we may write $K times.o_R M = K M$, a
left $A$-module. Two $Lambda$-lattices $M$ and $N$ are in the _same genus_, or
are _locally isomorphic_, if $M_P tilde.equiv N_P$ as $Lambda_P$-modules for
each $P$; we write $M or N$ in this case. If $M or N$, then after replacing $N$
by an isomorphic copy, we may assume that $K M = K N$.
#idx("Genus")
#idx("Locally isomorphic")
#nidx("$N or M$", "means N ∈ g(M)")

#source(234)
Now define
$
  S(Lambda) = {P: Lambda_P != "maximal" R_P "-order in" A_P},
$ <eq:order-nonmaximal-primes>
so $S(Lambda)$ is a finite set of maximal ideals of $R$, and $S(Lambda)$ is
empty if and only if $Lambda$ is a maximal order. By
@i:prop:genus-nonmaximal-primes, the genus of a $Lambda$-lattice $M$ is
determined by the isomorphism classes of the modules ${M_P: P in S(Lambda)}$. If
$Lambda$ is a maximal order, the genus of $M$ is determined by the isomorphism
class of $K M$.

In @i:cor:genus-addition we showed how to “add” lattices in a given genus:

#proposition[
  Let $L$, $M$, and $N$ be $Lambda$-lattices in the same genus. Then there
  exists a $Lambda$-lattice $L'$ in the genus, such that
  $ M plus.o N tilde.equiv L plus.o L'. $
] <prop:genus-lattice-addition>

In the same vein, decomposability is a property of genera (see
@i:cor:genus-direct-sum-decomposition and @i:cor:genus-multiple-decomposition):

#proposition[
  If $L$, $M$, and $N$ are arbitrary $Lambda$-lattices such that
  $L or (M plus.o N)$, then $L tilde.equiv M' plus.o N'$ for some $M' or M$ and
  some $N' or N$. In particular, if $L or M^((r))$ for some $r$, then
  $ L tilde.equiv M^((r-1)) plus.o M' quad "for some" M' or M. $
] <prop:genus-lattice-decomposition>

For most of the discussion, we shall concentrate on the _principal
genus_#footnote[
  _Caution:_ The notation is different from that used in §@i:sec:genus, where
  $Gamma_M$ denoted the genus of $M$, and where $g(M)$ denoted the number of
  isomorphism classes in $Gamma_M$.
] <fn:class-group-genus-notation> $g(Lambda)$, consisting of all
$Lambda$-lattices in the genus of $Lambda$. We do this because if $M$ is an
arbitrary $Lambda$-lattice, the study of $Lambda$-lattices in the
genus#footnote(<fn:class-group-genus-notation>) $g(M)$ of $M$ reduces at once to
the study of locally free left ideals in the $R$-order $End_Lambda M$. Thus, for
the most part, it suffices to treat the genus associated with an order, rather
than with a lattice.
#idx("Genus", "principal")
#idx("Principal genus")
#nidx("$g(M)$", "genus of M")

Now let $M in g(Lambda)$; after replacing $M$ by an isomorphic copy if need be,
we may assume that $M subset A$. We call $M$ a _locally free_ left
$Lambda$-ideal in $A$. Each such $M$ is projective as $Lambda$-module, by
@i:prop:projectivity-localization. Let $P$ range over the maximal ideals of $R$.
For each $P$, we may write
#idx("Locally free")
$ M_P = Lambda_P alpha_P quad "for some" alpha_P in A_P^dot. $
Since $M_P = Lambda_P$ a.e., we have $alpha_P in Lambda_P^dot$ a.e. Let
$alpha = (alpha_P) in product_P A_P^dot$ be an _idele_, and view $alpha$ as an
element of the _idele group_
$
  J(A) = {(alpha_P) in product_P A_P^dot: alpha_P in Lambda_P^dot "a.e."}.
$ <eq:class-group-idele-group>
#idx("Idele")
#idx("Idele group", target: [@eq:class-group-idele-group])

As remarked in the discussion following @i:eq:idele-group, $J(A)$ does not
depend on the choice of the $R$-order $Lambda$ in $A$.
#source(235)
Further, given the idele $alpha$, we may recover the $Lambda$-lattice $M$ by the
formula $M = Lambda alpha$, where by definition
$
  Lambda alpha = A inter {inter_P Lambda_P alpha_P}.
$ <eq:idele-lattice-intersection>
As shown in @i:th:genus-idele-double-cosets, for $alpha,beta in J(A)$ we have
$
  Lambda alpha tilde.equiv Lambda beta "as" Lambda "-lattices"
  <=> beta in U(Lambda) dot alpha dot u(Lambda),
$ <eq:idele-lattice-isomorphism-double-cosets>
where
$
  cases(
    U(Lambda) = "group of unit ideles" = product_P Lambda_P^dot,
    u(Lambda) = "group of principal ideles" = "image of" A^dot "in" J(A).
  )
$ <eq:unit-principal-ideles>
#idx("Unit idele", target: [@eq:unit-principal-ideles])
#idx("Principal idele", target: [@eq:unit-principal-ideles])
We shall return to this equivalence @eq:idele-lattice-isomorphism-double-cosets
later.

Our next step is to define the locally free class group of $Lambda$, denoted by
$op("Cl") Lambda$. We begin by observing that “addition” of lattices in the
genus $g(Lambda)$, as given in @prop:genus-lattice-addition, can be put into a
more appealing form using idele notation. Up to isomorphism, each
$M in g(Lambda)$ is of the form $M = Lambda alpha$, $alpha in J(A)$. As shown in
@i:th:idele-lattice-multiplication, we have
$
  Lambda alpha plus.o Lambda beta tilde.equiv Lambda plus.o Lambda alpha beta
  quad "for" alpha,beta in J(A).
$ <eq:idele-lattice-addition>
Thus, the isomorphism classes of $Lambda alpha$ and $Lambda beta$ uniquely
determine that of $Lambda plus.o Lambda alpha beta$. However, as pointed out at
the end of §@i:ss:ideles-locally-free-class-groups, an example due to Swan
@bib:Swan1962 shows that the isomorphism class of $Lambda alpha beta$ need not
be uniquely determined, since “cancellation” need not hold. To overcome this
difficulty, let us recall the concept of stable isomorphism, already encountered
in @eq:projective-class-stable-witness and @eq:stable-projective-isomorphism.

For $X,Y in cal(P) lr((Lambda))$, call $X$ _stably isomorphic_ to $Y$ if
$
  X plus.o Lambda^((k)) tilde.equiv Y plus.o Lambda^((k))
  quad "for some" k >= 0,
$ <eq:order-stable-isomorphism>
#idx("Stable isomorphism", target: [@eq:order-stable-isomorphism])
or equivalently, if $[X] = [Y]$ in $K_0 lr((Lambda))$. Let $[X]$ denote the
stable isomorphism class of $X$, and let
$
  op("Cl") Lambda = {[X]: X in g(Lambda)} =
  "locally free class group of" Lambda.
$ <eq:locally-free-ideal-class-group>
#idx("Locally free class group", target: [@eq:locally-free-ideal-class-group])
#idx("Class group Cl(Λ)", target: [@eq:locally-free-ideal-class-group])
Note that by @i:cor:krull-schmidt-cancellation, stably isomorphic lattices must
lie in the same genus. Now let $X_1,X_2 in g(Lambda)$; by
@prop:genus-lattice-addition we have
$
  X_1 plus.o X_2 tilde.equiv Lambda plus.o X_3
  quad "for some" X_3 in g(Lambda).
$
It is easily seen that the stable isomorphism class $[X_3]$ is uniquely
determined by the classes $[X_1]$ and $[X_2]$. Indeed, let $k$ be such that
$
  X_i plus.o Lambda^((k)) tilde.equiv Y_i plus.o Lambda^((k)),
  quad i=1,2, quad "and let" Y_1 plus.o Y_2 tilde.equiv Lambda plus.o Y_3.
$
#source(236)
Then
$
  X_3 plus.o Lambda^((2k+1)) tilde.equiv X_1 plus.o X_2 plus.o Lambda^((2k))
  tilde.equiv Y_1 plus.o Y_2 plus.o Lambda^((2k))
  tilde.equiv Y_3 plus.o Lambda^((2k+1)),
$
so $[X_3] = [Y_3]$ as claimed.

We now define a group law on $op("Cl") Lambda$ by the formula
$
  [X_1] + [X_2] = [X_3] quad "whenever"
  X_1 plus.o X_2 tilde.equiv Lambda plus.o X_3,
$
where $X_1,X_2 in g(Lambda)$. This is now a well-defined commutative and
associative operation, with identity element $[Lambda]$. Further, inverses exist
since
$
  Lambda alpha plus.o Lambda alpha^(-1) tilde.equiv Lambda plus.o Lambda
  quad "for" alpha in J(A).
$
Thus, $op("Cl") Lambda$ is an abelian additive group, and formula
@eq:idele-lattice-addition now states that there is a surjective homomorphism
$
  J(A) -> op("Cl") Lambda, quad "given by"
  alpha in J(A) arrow.r [Lambda alpha] in op("Cl") Lambda.
$

#remarks[
  #enum(
    numbering: "(i)",
    [By the Bass Cancellation Theorem @th:bass-cancellation, two lattices
      $X,Y in g(Lambda)$ are stably isomorphic if and only if
      $X plus.o Lambda tilde.equiv Y plus.o Lambda$, so it suffices to take
      $k = 1$ in @eq:order-stable-isomorphism. We shall give another proof of
      this fact in §@sec:cancellation-theorems, when $K$ is a global field, by
      using the Jacobinski Cancellation Theorem @th:jacobinski-cancellation. We
      shall also see (in @th:jacobinski-cancellation) that when $Lambda$
      satisfies the Eichler condition, then stable isomorphism implies
      isomorphism for lattices in $g(Lambda)$.],
    [For $K$ a global field, the Jordan–Zassenhaus Theorem tells us that the
      number of isomorphism classes of left ideals of $Lambda$ is finite.
      Therefore $op("Cl") Lambda$ is a finite abelian group in this case.],
    [Our discussion shows that for arbitrary $K$, there is a surjective
      homomorphism
      $ J(A) -> op("Cl") Lambda, $
      whose kernel contains both the unit ideles $U(Lambda)$ and the principal
      ideles $u(Lambda)$. Since $op("Cl") Lambda$ is abelian, the kernel must
      also contain the commutator group $[J(A),J(A)]$. We shall see in
      @th:class-group-idele-quotient that when $K$ is a global field, we have
      $ J(A) slash J_0 lr((A)) A^dot U(Lambda) tilde.equiv op("Cl") Lambda, $
      where $J_0 lr((A))$ is the kernel of the reduced norm acting on $J(A)$.],
    [The locally free class group was first introduced by Swan @bib:Swan1960 for
      the special case where $Lambda$ is an integral group ring $R G$, with
      $R = "alg. int." {K}$. Let $S K_0 lr((Lambda))$ denote the kernel of the
      map $K_0 lr((Lambda)) -> K_0 lr((A))$ defined by $K times.o_R ast$; we
      shall call $S K_0 lr((Lambda))$ the _reduced projective class group_. It
      is often denoted by $tilde(K)_0 lr((Lambda))$ in the literature.
      #idx("Reduced projective class group")

      #source(237)
      For the case $Lambda = R G$, we show at once that
      $ op("Cl") Lambda tilde.equiv S K_0 lr((Lambda)). $
      Each $x in S K_0 lr((Lambda))$ is expressible as
      $x = [Lambda^((r))] - [M]$ for some $r >= 0$ and some
      $M in cal(P) lr((Lambda))$, with $K M tilde.equiv A^((r))$. By Swan’s
      Theorem @i:th:swan-projective-group-lattices-locally-free, we have
      $M or Lambda^((r))$, so by @prop:genus-lattice-decomposition we obtain
      $M tilde.equiv Lambda^((r-1)) plus.o X$ for some $X or Lambda$. Therefore
      $x = [Lambda] - [X]$, and the isomorphism is given by
      $
        [X] in op("Cl") Lambda arrow.r [Lambda] - [X]
        in S K_0 lr((Lambda)).
      $
      Of course, we cannot expect such an isomorphism to hold for arbitrary
      orders $Lambda$ which are not group rings.],
  )
] <rem:locally-free-class-group-properties>

We now return to an arbitrary order $Lambda$, and for brevity we shall call
$op("Cl") Lambda$ the class group of $Lambda$. For arbitrary $Lambda$, this
group was first defined by Jacobinski @bib:Jacobinski1968b, in his fundamental
work on genera of lattices. He used a deep result of Eichler to obtain an
explicit formula for $op("Cl") Lambda$. Later Fröhlich @bib:Frohlich1975 gave an
idele-theoretic version of the formula, somewhat easier to use in practice.
Wilson @bib:Wilson1977a then used the Localization Sequence from algebraic
$K$-theory to obtain a formula for $op("Cl") Lambda$ in terms of the idele group
$J K_1 lr((A))$. For the case where $K$ is a global field, the reduced norm map
allows one to eliminate the $K_1$-groups and to obtain Fröhlich’s formula.
Another approach, given independently by C. T. C. Wall @bib:Wall1974b, obtains
the formula by using the Mayer–Vietoris sequence associated with the Wall square
(see @th:wall-mayer-vietoris). More recently, Fröhlich @bib:Frohlich1976 gave a
“Hom” description of $op("Cl") Lambda$, in terms of certain groups of
homomorphisms (see §@sec:frohlich-hom-description). This version has played a
fundamental role in applications of $op("Cl") Lambda$ to algebraic number theory
(see Fröhlich @bib:Frohlich1983).
#idx("Class group Cl(Λ)")
#idx("Locally free class group")

We now give the Wilson–Wall approach to $op("Cl") Lambda$ via algebraic
$K$-theory. The Localization Sequence @th:whitehead-localization-sequence gives
an exact sequence
$
  K_1 lr((Lambda)) -> K_1 lr((A)) -> K_0 lr((cal(T))) ->
  K_0 lr((Lambda)) arrow.r^phi K_0 lr((A)),
$ <eq:order-class-group-localization-sequence>
where $cal(T)$ is the category of all f.g. $R$-torsion $Lambda$-modules $M$ of
finite homological dimension. It should be stressed that the existence of such a
sequence is a rather formal result, requiring little more than the definitions
of the $K$-groups involved, and valid in much more general circumstances than
the case of orders in algebras.

For each maximal ideal $P$ of $R$, let $cal(T)_P$ be the category of f.g.
$P$-torsion $Lambda_P$-modules of finite homological dimension. Each
$M in cal(T)$ is expressible as a finite direct sum
$
  M = plus.o.big_P M_P, quad "where" M_P in cal(T)_P
  quad "and" M_P = 0 quad "a.e."
$
(Indeed, $M_P$ is just the $P$-primary component of $M$.) This gives an
isomorphism
$ beta: K_0 lr((cal(T))) tilde.equiv product.co_P K_0 lr((cal(T)_P)). $

#source(238)
We set
$
  S K_0 lr((Lambda)) = ker phi, quad "where"
  phi: K_0 lr((Lambda)) -> K_0 lr((A)).
$
From @eq:order-class-group-localization-sequence we obtain an exact sequence
$
  1 -> K_1 lr((A)) slash im K_1 lr((Lambda)) -> K_0 lr((cal(T))) ->
  S K_0 lr((Lambda)) -> 0.
$
Similarly, for each $P$ there is such a sequence, with $A$, $Lambda$, and
$cal(T)$ replaced by $A_P$, $Lambda_P$, and $cal(T)_P$, respectively.

#lemma[
  There is a commutative diagram with exact rows:
  #class-group-localization-comparison
] <lem:class-group-localization-comparison>
#proof[
  We have just seen that $beta$ is an isomorphism. To show that $gamma$ is
  well-defined, note that the map $S K_0 lr((Lambda)) -> S K_0 lr((Lambda_P))$
  is defined for each $P$, and we must show that $gamma$ maps
  $S K_0 lr((Lambda))$ into the direct sum of the ${S K_0 lr((Lambda_P))}$. Each
  $x in S K_0 lr((Lambda))$ is expressible as
  $
    x = [X] - [Y], quad "with" X,Y in cal(P) lr((Lambda))
    quad "and" K X = K Y.
  $
  Then $X_P = Y_P$ a.e., and
  $ gamma(x) = sum_P ([X_P] - [Y_P]), $
  a finite sum. Thus $gamma$ and $beta$ are both well-defined, and induce a map
  $alpha$ as shown. By the Snake Lemma, it follows that $alpha$ is injective,
  $gamma$ is surjective, and $ker gamma tilde.equiv op("cok") alpha$, facts
  needed below.
]

#corollary[
  There is an exact sequence
  $
    1 -> K_1 lr((A)) slash im K_1 lr((Lambda)) arrow.r^alpha
    product.co_P K_1 lr((A_P)) slash im K_1 lr((Lambda_P)) arrow.r^partial
    op("Cl") Lambda -> 0,
  $
  with $partial$ defined below.
] <cor:class-group-localization-idele-sequence>
#proof[
  Keeping the notation of @lem:class-group-localization-comparison, it suffices
  to establish an isomorphism
  $ theta: op("Cl") Lambda tilde.equiv ker gamma. $
  <eq:class-group-localization-kernel-isomorphism>
  By the final remark in the proof of @lem:class-group-localization-comparison,
  we have $ker gamma tilde.equiv op("cok") alpha$, so we need only use the
  machinery of the Snake Lemma to define the map $partial$.

  #source(239)
  To begin with, there is an injective map
  $theta: op("Cl") Lambda -> ker gamma$, given by $theta[M] = [Lambda] - [M]$
  for $M in g(Lambda)$. We show that $theta$ is a homomorphism: if
  $M_1,M_2 in g(Lambda)$, then in $op("Cl") Lambda$ we have
  $
    [M_1]+[M_2]=[M_3], quad "where"
    M_1 plus.o M_2 tilde.equiv Lambda plus.o M_3.
  $
  It follows at once that $theta[M_1]+theta[M_2]=theta[M_3]$, so $theta$ is a
  well-defined injective homomorphism. To show $theta$ surjective, let
  $x=[Lambda^((k))]-[Y] in ker gamma$, where $Y in cal(P) lr((Lambda))$. From
  $gamma(x)=0$ we obtain $Lambda_P^((k)) tilde.equiv Y_P$ for all $P$, so
  $Y or Lambda^((k))$, and therefore $Y tilde.equiv Lambda^((k-1)) plus.o M$ for
  some $M in g(Lambda)$, by @prop:genus-lattice-decomposition. But then
  $x=[Lambda]-[M]=theta[M]$, as desired.

  The homomorphism $partial$ is obtained via composition of maps
  $ op("cok") alpha tilde.equiv ker gamma tilde.equiv op("Cl") Lambda, $
  and can be described explicitly as follows. Since $A_P^dot$ maps onto
  $K_1 lr((A_P))$ by @th:semilocal-whitehead-unit-surjection, each $x$ in the
  domain of $partial$ can be represented as the class of a product
  $product a_P$, where $a_P in A_P^dot$ for each $P$, and $a_P=1$ a.e. Let
  $a=(a_P) in J(A)$ be the corresponding idele, and choose a nonzero $r in R$
  such that $b_P=r a_P in Lambda_P$ for each $P$. Set $b=(b_P) in J(A)$. Then
  the image $partial(x)$ of $x$ in $op("Cl") Lambda$ is $partial(b)-partial(r)$,
  where $b$ and $r$ are viewed as elements in the domain of $partial$. From the
  proof of @th:whitehead-localization-sequence, the image of $b$ in
  $product.co_P K_0 lr((cal(T)_P))$ is $sum_P [Lambda_P slash Lambda_P b_P]$. We
  then have
  $
    beta^(-1) sum [Lambda_P slash Lambda_P b_P] = [Lambda slash Lambda b]
    quad "in" K_0 lr((cal(T))),
  $
  with $Lambda b$ defined as in @eq:idele-lattice-intersection. The map
  $K_0 lr((cal(T))) -> S K_0 lr((Lambda))$ carries $[Lambda slash Lambda b]$
  onto $[Lambda]-[Lambda b]$, and $theta^(-1)$ maps this latter expression onto
  $[Lambda b] in op("Cl") Lambda$. This gives $partial(b)=[Lambda b]$, and
  similarly $partial(r)=[Lambda r]$. Therefore
  $
    partial(x) = [Lambda b]-[Lambda r] = [Lambda b r^(-1)] = [Lambda a]
    in op("Cl") Lambda,
  $
  by @eq:idele-lattice-addition. In short, if $x$ is the class of an idele
  $a in J(A)$, then $partial(x)=[Lambda a] in op("Cl") Lambda$. This completes
  the proof.
]
#idx(
  "Class group Cl(Λ)",
  target: [@eq:class-group-localization-kernel-isomorphism],
)
#idx(
  "Locally free class group",
  target: [@eq:class-group-localization-kernel-isomorphism],
)

#remark[
  We had previously defined the locally free class group $op("Cl") Lambda$, in
  @def:locally-free-class-group, as the kernel of the homomorphism
  $ K_0 lr((Lambda)) -> product_P K_0 lr((Lambda_P)). $
  It is easily seen that this kernel coincides with $ker gamma$, where $gamma$
  is the map occurring in @lem:class-group-localization-comparison. Thus, the
  class group as defined in @def:locally-free-class-group is isomorphic to our
  current version @eq:locally-free-ideal-class-group, and we shall almost always
  use $op("Cl") Lambda$ in the sense of @eq:locally-free-ideal-class-group in
  this chapter.
] <rem:class-group-definition-comparison>

#source(240)
In our earlier discussion of the class group $op("Cl") Lambda$, and again in
proving @cor:class-group-localization-idele-sequence, the idele group $J(A)$
played a vital role. Our next aim is to refine
@cor:class-group-localization-idele-sequence so as to obtain an explicit formula
for $op("Cl") Lambda$ in terms of the _idele group_ $J K_1 lr((A))$ of
$K_1 lr((A))$ relative to $R$. Later, we shall use properties of reduced norms
to eliminate the occurrences of the $K_1$-groups, in the special case where $A$
is an algebra over a _global field_ $K$.

By definition, the idele group $J K_1 lr((A))$ of $K_1 lr((A))$ relative to $R$
is given by
$
  J K_1 lr((A)) = {(x_P) in product_P K_1 lr((A_P)):
    x_P in im K_1 lr((Lambda_P)) "a.e."}.
$
This group is independent of the choice of the $R$-order $Lambda$ in $A$, since
if $Lambda'$ is another such order, then $Lambda_P=Lambda'_P$ a.e. We also
introduce the group of unit ideles
$ U K_1 lr((Lambda)) = product_P K_1 lr((Lambda_P)). $
The maps $K_1 lr((Lambda_P)) -> K_1 lr((A_P))$, as $P$ varies, give rise to a
homomorphism $U K_1 lr((Lambda)) -> J K_1 lr((A))$. Since
$
  J K_1 lr((A)) = lr((product.co_P K_1 lr((A_P)))) dot
  im U K_1 lr((Lambda)),
$
we obtain
$
  (J K_1 lr((A))) / (im U K_1 lr((Lambda))) tilde.equiv
  product.co_P (K_1 lr((A_P))) / (im K_1 lr((Lambda_P))).
$

Next, the maps $A -> A_P$ (for each $P$) yield a homomorphism from $K_1 lr((A))$
into the direct product $product_P K_1 lr((A_P))$. Further, for
$x in K_1 lr((A))$, we may represent $x$ by a matrix $X in GL(A)$, and then
clearly $X in GL(Lambda_P)$ a.e. Thus we obtain the homomorphism $alpha$ given
in @cor:class-group-localization-idele-sequence, carrying $x$ onto the class of
the principal idele $(x)$ in
$product.co_P K_1 lr((A_P)) slash im K_1 lr((Lambda_P))$. Consequently, we may
reformulate @cor:class-group-localization-idele-sequence as follows:

#proposition[
  There is an isomorphism of groups
  $
    (J K_1 lr((A))) / (im K_1 lr((A)) dot im U K_1 lr((Lambda)))
    tilde.equiv op("Cl") Lambda,
  $
  given by representing each element of the left-hand side by an idele
  $a in J(A)$, and then mapping the element onto the class $[Lambda a]$ of the
  locally free ideal $Lambda a$ defined as in @eq:idele-lattice-intersection.
] <prop:class-group-k1-idele-description>

The preceding results give formulas for $op("Cl") Lambda$, where $Lambda$ is an
$R$-order in a f.d. separable $K$-algebra $A$, with arbitrary ground field $K$.
In the case where $K$ is a global field, however, we may obtain a simpler
expression for the class group $op("Cl") Lambda$, by using reduced norms to get
rid of the $K_1$ groups. The following basic formula is due to Fröhlich
@bib:Frohlich1975, and is the idele-theoretic version of an earlier formula of
Jacobinski @bib:Jacobinski1968b:

#source(241)
#theorem[
  Let $K$ be a global field, and let $Lambda$ be an $R$-order in a separable
  f.d. $K$-algebra $A$. Let $C$ be the center of $A$, and $J(C)$ its idele group
  defined as in @eq:class-group-idele-group. Then we have
  $
    op("Cl") Lambda tilde.equiv
    (J(C)) / (C^+ dot product_P op("nr") Lambda_P^dot),
  $
  where $C^+$ is the subgroup of $C^dot$ (viewed as principal ideles) given in
  @eq:semisimple-positive-norm-subgroup, and where $op("nr")$ is the reduced
  norm map.
] <th:class-group-reduced-norm-ideles>
#nidx(
  "$C^+$",
  "image of global reduced norm",
  target: [@eq:semisimple-positive-norm-subgroup],
  chapter: [@ch:class-groups],
)
#proof[
  The reduced norm map $op("nr")$ maps $A^dot$ onto $C^+$, by the
  Hasse–Schilling–Maass Theorem @i:th:hasse-schilling-maass-norm. On the other
  hand, for each $P$, it follows from Exercise @exc:center-under-field-extension
  that $A_P$ is a $K_P$-algebra with center $C_P$, so there is a reduced norm
  map $A_P^dot -> C_P^dot$, again denoted by $op("nr")$. This map is surjective
  by @i:th:local-field-reduced-norm-surjective.

  As shown in §@ss:reduced-norms, the reduced norm map induces isomorphisms
  $
    op("nr"): K_1 lr((A)) tilde.equiv C^+, quad
    op("nr"): K_1 lr((A_P)) tilde.equiv C_P^dot
  $ <eq:global-local-whitehead-reduced-norms>
  for each $P$. The first of these is a much deeper result, depending on the
  Wang–Platonov Theorem; see @th:reduced-norm-whitehead-isomorphism. However, we
  do not require the full force of this isomorphism, but only the weaker fact
  that $op("nr") K_1 lr((A)) = C^+$; this follows readily from the
  Hasse–Schilling–Maass Norm Theorem (see §@ss:reduced-norms). The isomorphism
  given in the local case is an immediate consequence of the Nakayama–Matsushima
  Theorem @i:th:nakayama-matsushima; see @th:reduced-norm-whitehead-isomorphism.

  Next, let $frak(O)$ be the integral closure of $R$ in $C$, so
  $ J(C) = {(c_P) in product C_P^dot: c_P in frak(O)_P^dot "a.e."}. $
  If $Gamma_P$ is a maximal $R_P$-order in $A_P$, then by
  @prop:local-maximal-order-unit-norm we have
  $
    op("nr") K_1 lr((Gamma_P)) = op("nr") Gamma_P^dot = frak(O)_P^dot
  $ <eq:local-maximal-order-whitehead-norms>
  for each $P$.

  It follows from the results (in the local case) that $op("nr")$ induces an
  isomorphism $J K_1 lr((A)) tilde.equiv J(C)$. In this isomorphism, the group
  of principal ideles $K_1 lr((A))$ maps onto $C^+$, while the group of unit
  ideles $U K_1 lr((Lambda))$ maps onto $product_P op("nr") K_1 lr((Lambda_P))$.
  Since each element of $K_1 lr((Lambda_P))$ is represented by an element of
  $Lambda_P^dot$, we have $op("nr") K_1 lr((Lambda_P)) = op("nr") Lambda_P^dot$.
  The desired formula for $op("Cl") Lambda$ is now a direct consequence of
  @prop:class-group-k1-idele-description.
]
#idx("Unit idele", target: [@eq:local-maximal-order-whitehead-norms])

#remark(numbered: true)[
  Let $K$ be a global field, and keep the above notation. By
  @th:semilocal-whitehead-unit-surjection, the elements of $K_1 lr((A_P))$,
  $K_1 lr((A))$, and $K_1 lr((Lambda_P))$ are representable by $1 times 1$
  matrices with entries in $A_P^dot$, $A^dot$, and $Lambda_P^dot$, respectively.
  It follows at once that there is a surjection $J(A) -> J K_1 lr((A))$, whose
  kernel we denote by $J_0 lr((A))$. Thus
  $ J K_1 lr((A)) tilde.equiv J(A) slash J_0 lr((A)). $
  <eq:whitehead-ideles-reduced-norm-kernel>
] <rem:idele-whitehead-surjection>

#source(242)
Next, the reduced norm $op("nr"): A -> C$ induces a map of idele groups, and
there is a commutative diagram
#idele-reduced-norm-triangle
in which the vertical map is an isomorphism by
@eq:global-local-whitehead-reduced-norms. It follows at once that
$ J_0 lr((A)) = {x in J(A): op("nr") x = 1}. $
Note that $J_0 lr((A)) supset.eq [J(A),J(A)]$ since $J K_1 lr((A))$ is abelian.

In the isomorphism @eq:whitehead-ideles-reduced-norm-kernel, the image of
$K_1 lr((A))$ in $J K_1 lr((A))$ maps onto $A^dot$, considered as the group of
principal ideles in $J(A)$. Likewise, the image of $U K_1 lr((Lambda))$ in
$J K_1 lr((A))$ maps onto the group of unit ideles $U(Lambda)$ in $J(A)$,
defined as in @eq:unit-principal-ideles. From
@prop:class-group-k1-idele-description and the isomorphism
@eq:whitehead-ideles-reduced-norm-kernel, we therefore obtain:

#theorem[
  Let $K$ be a global field, and let $Lambda$ be an $R$-order in a f.d.
  separable $K$-algebra $A$. Then
  $
    op("Cl") Lambda tilde.equiv
    (J(A)) / (J_0 lr((A)) A^dot U(Lambda)),
  $
  where $J_0 lr((A)) = {x in J(A): op("nr") x = 1}$.
] <th:class-group-idele-quotient>
#idx("Class group Cl(Λ)", target: [@th:class-group-idele-quotient])
#idx("Locally free class group", target: [@th:class-group-idele-quotient])

Of course, applying $op("nr")$ to the right-hand expression above yields
@th:class-group-reduced-norm-ideles at once.

It is sometimes desirable to use both finite and infinite primes in the idele
group of $A$. We conclude this subsection with a brief discussion of what
happens to the formulas in @th:class-group-reduced-norm-ideles and
@th:class-group-idele-quotient in this new context. Let $R = "alg. int." {K}$,
and write $P divides infinity$ to indicate that $P$ is an infinite (archimedean)
prime of $K$. For each such $P$, let $C_P^+$ be the subgroup of $C_P^dot$ (of
index a power of $2$) such that
$ op("nr") A_P^dot = C_P^+. $
This subgroup is defined just as in @i:def:local-index-capacity-ramification and
@i:eq:positive-at-ramified-real-primes, by first reducing to the case of central
simple algebras, and then using @i:eq:positive-at-ramified-real-primes for the
single prime $P$. As in §@ss:reduced-norms, we have
$op("nr") K_1 lr((A_P)) = C_P^+$ for $P divides infinity$.

We now define
$
  J^* lr((C)) = J(C) times C_infinity^dot, quad "where"
  C_infinity^dot = product_(P divides infinity) C_P^dot,
$
$
  U^* lr((Lambda)) = U(Lambda) times A_infinity^dot, quad "where"
  A_infinity^dot = product_(P divides infinity) A_P^dot,
$
#nidx(
  "$J(A), J^* lr((A))$",
  "idèle groups",
  target: [@eq:class-group-idele-group],
)
#nidx(
  "$U(Lambda), U^* lr((Lambda))$",
  "unit idèles",
  target: [@eq:unit-principal-ideles],
)
so now
$
  op("nr") A_infinity^dot = C_infinity^+
  = product_(P divides infinity) C_P^+.
$
#source(243)
There is an obvious embedding of $J(C)$ into $J^* lr((C))$, given by
$a arrow.r a times 1$ for $a in J(C)$. There are now two diagonal embeddings of
$C^dot$, one in $J(C)$, the other in $J^* lr((C))$. Denoting these by $i$ and
$i^*$, respectively, we may write for $c in C^dot$:
$
  i^* lr((c)) = i(c) times i_infinity lr((c)), quad "where"
  i_infinity lr((c)) in C_infinity^dot.
$
We are now ready to establish the following result of Fröhlich
@bib:Frohlich1975:

#theorem[
  Keeping the above notation, we have
  $
    op("Cl") Lambda tilde.equiv
    (J^* lr((C))) / (i^* lr((C^dot)) op("nr") U^* lr((Lambda))).
  $
] <th:class-group-all-prime-reduced-norm-ideles>
#proof[
  The existence of the desired isomorphism will follow from
  @th:class-group-reduced-norm-ideles once we show that the embedding
  $J(C) -> J^* lr((C))$ induces an isomorphism
  $
    theta: (J(C)) / (i(C^+) op("nr") U(Lambda)) tilde.equiv
    (J^* lr((C))) / (i^* lr((C^dot)) op("nr") U^* lr((Lambda))).
  $
  The right-hand expression may be written as
  $
    (J(C) times C_infinity^dot) /
    ({i(c) times i_infinity lr((c)): c in C^dot}
    {op("nr") U(Lambda)} C_infinity^+).
  $
  To show $theta$ well-defined, note that for $c in C^+$ we have
  $i_infinity lr((c)) in C_infinity^+$, so
  $ i(C^+) subset.eq i^* lr((C^dot)) C_infinity^+. $
  We show next that $theta$ is surjective, by proving that
  $
    C_infinity^dot subset.eq J(C) i^* lr((C^dot))
    op("nr") U^* lr((Lambda)).
  $
  Indeed, given $b in C_infinity^dot$, it follows from the Weak Approximation
  Theorem in valuation theory (see, for example, Weiss @bib:Weiss1963) that
  there exists an element $c in C^dot$ with
  $b i_infinity lr((c)) in C_infinity^+$. But therefore
  $b in J(C) i^* lr((C^dot)) C_infinity^+$, as desired.

  Finally, we prove that $theta$ is injective. Let $a in J(C)$ be such that
  $
    a times 1 = i(c) times i_infinity lr((c)) (op("nr") u) v
    quad "for some" c in C^dot, quad u in U(Lambda), quad
    v in C_infinity^+.
  $
  Then
  $ a = i(c) op("nr") u, quad 1 = i_infinity lr((c)) v. $
  #source(244)
  Therefore $i(c) in C^+$, which means that $c in C^+$, so
  $a in i(C^+) op("nr") U(Lambda)$ as desired. This shows that $theta$ is an
  isomorphism, and completes the proof of the theorem.
]

Analogously, formula @th:class-group-idele-quotient takes the form
$
  op("Cl") Lambda tilde.equiv
  (J^* lr((A))) / (tilde(J) lr((A)) A^dot U^* lr((Lambda))),
$ <eq:class-group-all-prime-idele-quotient>
where $tilde(J) lr((A)) = {x in J^* lr((A)): op("nr") x = 1}$. Fröhlich showed
that $tilde(J) lr((A))$ coincides with the closure of the commutator subgroup of
$J^* lr((A))$ in the standard idele topology, (see Exercise
@exc:idele-reduced-norm-commutator-closure).
#nidx(
  "$J_0 lr((A)), tilde(J) lr((A))$",
  "kernel of reduced norm",
  target: [@eq:whitehead-ideles-reduced-norm-kernel],
)

#heading(level: 4, numbering: none)[Appendix to §@ss:class-group-basic-formulas]
<app:class-group-basic-formulas>

We briefly consider a “higher” locally free class group
$op("Cl")_1 lr((Lambda))$, used by Oliver @bib:Oliver1980a, @bib:Oliver1980b in
his calculations of $S K_1$ of integral group rings. We have already used this
concept in the proof of Theorem @th:oliver-hereditary-order-sk1 above.

Let $Lambda$ be an $R$-order in a f.d. separable $K$-algebra $A$, where $R$ is a
Dedekind domain whose quotient field $K$ is a global field. The group
$S K_0 lr((Lambda))$ is (by definition) the kernel of the homomorphism
$K_0 lr((Lambda)) -> K_0 lr((A))$. For each maximal ideal $P$ of $R$, the group
$S K_0 lr((Lambda_P))$ is defined analogously. As shown in
@eq:class-group-localization-kernel-isomorphism, the locally free class group
$op("Cl") Lambda$ is isomorphic to $ker gamma$, where
$ gamma: S K_0 lr((Lambda)) -> product.co_P S K_0 lr((Lambda_P)). $
It seems natural to study the map #equation-suffix(
  base: [@eq:class-group-all-prime-idele-quotient],
)[$
  gamma_1: S K_1 lr((Lambda)) -> product.co_P S K_1 lr((Lambda_P)),
$] <eq:higher-class-group-localization-map>
when $S K_1 lr((Lambda))$ is the kernel of the homomorphism
$K_1 lr((Lambda)) -> K_1 lr((A))$, with $S K_1 lr((Lambda_P))$ defined
analogously. We have already seen in @th:oliver-hereditary-order-sk1 that
$S K_1 lr((Lambda_P))=1$ a.e. We shall show below that $gamma_1$ is surjective,
and following Oliver, we define
$ op("Cl")_1 Lambda = ker gamma_1, $
a “higher” locally free class group. Of course, $op("Cl")_1 Lambda$ is a finite
abelian group.
#idx("Class group Cl₁(Λ)")
We keep the notation of @lem:class-group-localization-comparison. There is a
commutative diagram with exact rows:
#higher-class-group-localization-comparison
#source(245)
This yields a similar diagram
#higher-class-group-kernel-comparison
It follows at once that $gamma_1$ is surjective. Further, as in
@lem:class-group-localization-comparison and
@cor:class-group-localization-idele-sequence, we obtain an exact sequence
#equation-suffix(
  base: [@eq:class-group-all-prime-idele-quotient],
  suffix: "b",
)[$
  1 -> K_2 lr((A)) slash im K_2 lr((Lambda)) ->
  product.co_P K_2 lr((A_P)) slash im K_2 lr((Lambda_P)) ->
  op("Cl")_1 Lambda -> 1,
$] <eq:higher-class-group-k2-idele-sequence>
since $op("Cl")_1 Lambda = ker gamma_1$.

Anticipating the discussion in §@ss:class-group-functorial-kernel, and
@th:class-group-ring-homomorphism in particular, we prove:

#theorem-suffix(base: [@eq:class-group-all-prime-idele-quotient], suffix: "c")[
  Let $Lambda,Gamma$ be $R$-orders in f.d. separable $K$-algebras $A,B$,
  respectively. Let $phi: A -> B$ be a surjection of $K$-algebras such that
  $phi(Lambda) subset.eq Gamma$. Then $phi$ induces a surjection
  $op("Cl")_1 Lambda -> op("Cl")_1 Gamma$.
] <th:higher-class-group-surjective-algebra-map>
#proof[
  Since $phi: A -> B$ is a split surjection of $K$-algebras, the induced
  homomorphism $K_2 lr((A)) -> K_2 lr((B))$ is surjective (and split). The same
  holds for the map $K_2 lr((A_P)) -> K_2 lr((B_P))$ for each $P$, and the
  desired result now follows from @eq:higher-class-group-k2-idele-sequence.
]

#corollary-suffix(
  base: [@eq:class-group-all-prime-idele-quotient],
  suffix: "d",
)[
  #enum(
    numbering: "(i)",
    [If $Lambda subset.eq Gamma$ are $R$-orders in $A$, then $op("Cl")_1 Lambda$
      maps onto $op("Cl")_1 Gamma$.],
    [A surjection $G -> overline(G)$ of finite groups induces a surjection
      $op("Cl")_1 R G -> op("Cl")_1 R overline(G)$.],
  )
] <cor:higher-class-group-order-group-surjections>

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [For any abelian group $G$ and any maximal ideal $P$ of $R$, we have
      $S K_1 lr((R_P G))=1$ by @prop:commutative-semilocal-sk1. We conclude that
      $
        op("Cl")_1 R G = S K_1 lr((R G))
        quad "whenever" G "is abelian."
      $],
    [For $p$ prime, let $(op("Cl")_1)_((p))$ denote the $p$-torsion subgroup of
      $op("Cl")_1$. Oliver @bib:Oliver1980a showed that for each group $G$,
      $
        (op("Cl")_1 ZZ G)_((p)) =
        sum_H op("ind")_H^G (op("Cl")_1 ZZ H)_((p)),
      $
      where $H$ ranges over all $p$-elementary subgroups of $G$.],
    [Some further results of Oliver @bib:Oliver1980a:
      #enum(
        [$op("Cl")_1 ZZ G != 0$ if $G$ is a non-abelian $p$-group, where $p$ is
          odd.],
        [$op("Cl")_1 ZZ G = 0$ for $G$ a dihedral or generalized quaternion
          $2$-group.],
        [$op("Cl")_1 ZZ G = 0$ if $RR G$ is a direct sum of matrix algebras over
          $RR$, that is, every complex representation of $G$ is realizable over
          $RR$ (see §@sec:unitary-orthogonal-symplectic-modules).],
      )],
  )
] <rem:higher-class-group-properties>

#heading(level: 3)[
  Functorial Properties and the Kernel Group
] <ss:class-group-functorial-kernel>

As above, let $Lambda$ be an $R$-order in a f.d. separable $K$-algebra $A$,
where for the moment the field $K$ may be arbitrary. Our aim here is to develop
some functorial properties of the class group $op("Cl") Lambda$, especially
those arising from homomorphisms from one order to another.
#source(246)
These properties, whose proofs use the $K$-theoretic description of
$op("Cl") Lambda$ given in @prop:class-group-k1-idele-description, will yield
techniques for calculation of class groups in specific cases.

We saw in @prop:class-group-k1-idele-description that there is an isomorphism
$
  (J K_1 lr((A))) / (im K_1 lr((A)) dot im U K_1 lr((Lambda)))
  tilde.equiv op("Cl") Lambda,
$
where (by definition)
$
  cases(
    J K_1 lr((A)) = {(x_P): x_P in K_1 lr((A_P)) "for all" P,
      "and" x_P in im K_1 lr((Lambda_P)) "a.e."},
    U K_1 lr((Lambda)) = product_P K_1 lr((Lambda_P)),
    quad im K_1 lr((A)) = "group of principal ideles."
  )
$
As an immediate consequence of these formulas, we have (Fröhlich
@bib:Frohlich1975):

#theorem[
  Let $Lambda,Gamma$ be $R$-orders in separable $K$-algebras $A,B$,
  respectively, and let $phi: A -> B$ be a homomorphism of $K$-algebras such
  that $phi(Lambda) subset.eq Gamma$. Then
  #enum(
    numbering: "(i)",
    [The map $phi$ induces a homomorphism
      $phi_*: op("Cl") Lambda -> op("Cl") Gamma$, given by
      $[X] arrow.r [Gamma times.o_Lambda X]$ for $[X] in op("Cl") Lambda$.],
    [If $phi$ is a surjection of $A$ into $B$, then
      $phi_* lr((op("Cl") Lambda)) = op("Cl") Gamma$.],
    [If $Lambda subset.eq Gamma$ are $R$-orders in $A$, this inclusion induces a
      surjection of $op("Cl") Lambda$ onto $op("Cl") Gamma$.],
  )
] <th:class-group-ring-homomorphism>
#proof[
  The map $phi: A -> B$ induces homomorphisms
  $
    J K_1 lr((A)) -> J K_1 lr((B)), quad K_1 lr((A)) -> K_1 lr((B)),
    quad U K_1 lr((Lambda)) -> U K_1 lr((Gamma)),
  $
  so by @eq:class-group-localization-kernel-isomorphism there is a map
  $phi_*: op("Cl") Lambda -> op("Cl") Gamma$. We leave it to the reader to
  verify that $phi_*$ agrees with the “change of rings” map
  $Gamma times.o_Lambda ast$.

  If $phi(A)=B$, then $phi$ maps $J K_1 lr((A))$ onto $J K_1 lr((B))$, whence
  $phi_*$ is also surjective. This proves assertion (ii), and finally (iii) is a
  special case of (ii).
]

For computational purposes, a special case of the Mayer–Vietoris sequence
@eq:mayer-vietoris-sequence is often useful. Consider a fiber product
#numbered-block[
  #order-fiber-product-square
] <eq:order-class-group-fiber-product>
in which $Lambda,Lambda_1$, and $Lambda_2$ are $R$-orders in $K$-algebras
$A,A_1$, and $A_2$, respectively, and where $overline(Lambda)$ is an $R$-torsion
$R$-algebra. (As we shall see, such fiber products arise naturally in many
cases.) We then obtain the following, first pointed out by Reiner–Ullom
@bib:Reiner1974a:

#source(247)
#theorem[
  Given a fiber product diagram @eq:order-class-group-fiber-product as above, in
  which either $g_1$ or $g_2$ is surjective, there is an exact “Mayer–Vietoris
  sequence”
  $
    K_1 lr((Lambda_1)) times K_1 lr((Lambda_2)) ->
    K_1 lr((overline(Lambda))) arrow.r^(partial') op("Cl") Lambda ->
    op("Cl") Lambda_1 plus.o op("Cl") Lambda_2 -> 0.
  $
] <th:reiner-ullom-class-group-mayer-vietoris>
#idx(
  "Reiner-Ullom Theorem",
  target: [@th:reiner-ullom-class-group-mayer-vietoris],
)
#idx(
  "Mayer-Vietoris sequence",
  target: [@th:reiner-ullom-class-group-mayer-vietoris],
)
#proof[
  Applying $K times.o_R ast$ to @eq:order-class-group-fiber-product and using
  the fact that $K times.o_R overline(Lambda)=0$, we see at once that
  $A tilde.equiv A_1 plus.o A_2$. Treating this isomorphism as an
  identification, we have
  $
    Lambda = {(x_1,x_2) in Lambda_1 plus.o Lambda_2:
      g_1 lr((x_1))=g_2 lr((x_2))}.
  $
  The inclusion $Lambda subset.eq Lambda_1 plus.o Lambda_2$ then gives a
  surjection $op("Cl") Lambda -> op("Cl") Lambda_1 plus.o op("Cl") Lambda_2$, by
  Theorem @th:class-group-ring-homomorphism.

  From Milnor’s Theorem @th:milnor-mayer-vietoris, we obtain an exact sequence
  $
    K_1 lr((Lambda_1)) times K_1 lr((Lambda_2)) ->
    K_1 lr((overline(Lambda))) arrow.r^partial K_0 lr((Lambda)) ->
    K_0 lr((Lambda_1)) plus.o K_0 lr((Lambda_2)).
  $
  In our special case, $overline(Lambda)$ is a semilocal ring, so each element
  of $K_1 lr((overline(Lambda)))$ may be represented by a unit of
  $overline(Lambda)$. The connecting homomorphism $partial$ constructed in the
  proof of @th:milnor-mayer-vietoris can now be described more simply: for
  $u in overline(Lambda)^dot$, we have
  $ partial(u) = [M(u)]-[Lambda] in K_0 lr((Lambda)), $
  where, as in @eq:patched-module-triple,
  $
    M(u) = (Lambda_1,Lambda_2,u) =
    {(x_1,x_2) in Lambda_1 plus.o Lambda_2:
      overline(x)_1 u = overline(x)_2 "in" overline(Lambda)}.
  $
  Let us show that $M(u) or Lambda$. For each prime $P$ of $R$, we have
  $ M(u)_P = ((Lambda_1)_P,(Lambda_2)_P,u). $
  If (say) $g_1$ is surjective, then there is a surjection
  $(Lambda_1)_P -> overline(Lambda)_P$, which yields a surjection of units by
  Exercise @i:exc:units-surject-quotient-local-base. But then we have
  $M(u)_P tilde.equiv Lambda_P$ by @lem:patched-free-module-equivalence. We have
  now proved that the connecting homomorphism $partial$ carries
  $K_1 lr((overline(Lambda)))$ into the kernel of the map
  $ gamma: S K_0 lr((Lambda)) -> product.co_P S K_0 lr((Lambda_P)). $
  Since $ker gamma tilde.equiv op("Cl") Lambda$ by
  @eq:class-group-localization-kernel-isomorphism, we obtain the desired exact
  sequence, where the map
  $partial': K_1 lr((overline(Lambda))) -> op("Cl") Lambda$ is given by
  $
    partial' lr((u)) = [M(u)] in op("Cl") Lambda
    quad "for" u in overline(Lambda)^dot.
  $
  This completes the proof.
]

#source(248)
See Exercise @exc:fiber-product-boundary-idele for an explicit description of
$M(u)$ in terms of ideles.

In the special case where $overline(Lambda)$ is commutative, we may identify
$K_1 lr((overline(Lambda)))$ with $overline(Lambda)^dot$, by
@eq:whitehead-unit-map. For $i=1,2$, the image of $K_1 lr((Lambda_i))$ in
$overline(Lambda)^dot$ is given by
$ {det g_i lr((x)): x in GL(Lambda_i)}, $
which contains $g_i lr((Lambda_i^dot))$ but need not coincide with it in
general. However, if $Lambda_i$ is commutative, we have
$ {det g_i lr((x)): x in GL(Lambda_i)} = g_i lr((Lambda_i^dot)). $
This implies

#corollary[
  If the algebra $A$ is commutative, the sequence
  $
    1 -> Lambda^dot -> Lambda_1^dot times Lambda_2^dot ->
    overline(Lambda)^dot -> op("Cl") Lambda ->
    op("Cl") Lambda_1 plus.o op("Cl") Lambda_2 -> 0
  $
  is exact.
] <cor:commutative-order-unit-class-group-sequence>

There is an analogous version when $A$ is not necessarily commutative, under
some mild restrictions. We begin with

#definition[
  An order $Lambda$ has _locally free cancellation_ if for any locally free
  $Lambda$-modules $X$ and $Y$,
  $
    X plus.o Lambda^((k)) tilde.equiv Y plus.o Lambda^((k))
    quad "for some" k => X tilde.equiv Y.
  $
] <def:locally-free-cancellation>
#idx("Cancellation", target: [@def:locally-free-cancellation])
#idx("Locally free cancellation", target: [@def:locally-free-cancellation])

By @prop:genus-lattice-decomposition, this holds if and only if it holds for
left ideals $X,Y$ in $g(Lambda)$. A commutative order $Lambda$ necessarily has
this cancellation property, since for $X in g(Lambda)$, the $(k+1)$-st exterior
power of $X plus.o Lambda^((k))$ is isomorphic to $X$ (see the proof of
@i:prop:commutative-order-steinitz-invariants). As we shall see below, most
noncommutative orders also have locally free cancellation; this is the case
whenever $A = "Eichler" slash R$ (see @th:jacobinski-cancellation).

#corollary[
  Given a fiber product as in @eq:order-class-group-fiber-product, assume that
  $Lambda$ is an order with locally free cancellation. Then there is an exact
  sequence
  $
    1 -> W -> overline(Lambda)^dot arrow.r^(partial') op("Cl") Lambda ->
    op("Cl") Lambda_1 plus.o op("Cl") Lambda_2 -> 0,
  $
  where
  $ W = {w_1 w_2: w_i in g_i lr((Lambda_i^dot)), quad i=1,2}. $
] <cor:cancellation-order-unit-class-group-sequence>
#proof[
  The homomorphism $partial'$ is given as in
  @th:reiner-ullom-class-group-mayer-vietoris, namely,
  $
    partial' lr((u)) = [M(u)], quad "where" M(u)=(Lambda_1,Lambda_2,u),
    quad "for" u in overline(Lambda)^dot.
  $
  Since $Lambda$ is assumed to have locally free cancellation, we have
  $partial' lr((u))=0$ if and only if $M(u) tilde.equiv Lambda$, that is,
  $(Lambda_1,Lambda_2,u) tilde.equiv (Lambda_1,Lambda_2,1)$.
  #source(249)
  The latter isomorphism holds if and only if $u in W$, by
  @lem:patched-free-module-equivalence.

  The above implies also that
  $ W = {w_2 w_1: w_i in g_i lr((Lambda_i^dot))}, $
  as well as the unexpected fact that $W ⊴ overline(Lambda)^dot$.
]

The above result, and an analogous version @th:kernel-group-mayer-vietoris
below, will be used in §@ss:metacyclic-class-groups to calculate the class group
$op("Cl") ZZ G$ of certain metacyclic groups $G$.

As in Chapters @i:ch:integral-representations and
@i:ch:local-global-integral-representations, we obtain information about
nonmaximal orders by relating them to maximal orders. This technique is also
important in studying class groups, and we shall begin by determining the class
group of a maximal order $Lambda$ in a f.d. separable $K$-algebra $A$. Since
$Lambda$ decomposes according to the Wedderburn decomposition of $A$, as in
@i:th:maximal-orders-wedderburn-components, it suffices to treat the case where
$A$ is a central simple $K$-algebra.

For the moment, let $K$ be a global field, and recall some notation from
§@sec:grothendieck-groups:
$
  cases(
    I(R) = "group of fractional" R "-ideals of" K,
    K^+ = {a in K^dot: a_P > 0 "at every infinite prime" P
      "of" K "ramified in" A},
    P_A lr((R)) = {R a: a in K^+} = "subgroup of" I(R),
    op("Cl")_A R = I(R) slash P_A lr((R)).
  )
$
<eq:restricted-ideal-class-group-notation>
In terms of this notation, we have:

#theorem[
  Let $Lambda$ be a maximal $R$-order in a central simple $K$-algebra $A$, where
  $K$ is a global field. Then
  $
    op("Cl") Lambda tilde.equiv S K_0 lr((Lambda))
    tilde.equiv op("Cl")_A R.
  $
] <th:maximal-order-restricted-ideal-class-group>
#proof[
  To establish the first isomorphism, let $P$ be a prime of $R$. If $X,Y$ are
  projective $Lambda_P$-lattices such that $K_P X tilde.equiv K_P Y$ as
  $A_P$-modules, then $X tilde.equiv Y$ by
  @i:th:dvr-maximal-orders-completion-lattices(iii). This shows that
  $S K_0 lr((Lambda_P))=0$, and therefore
  $op("Cl") Lambda tilde.equiv S K_0 lr((Lambda))$ by
  @eq:class-group-localization-kernel-isomorphism.

  Next, there is an exact sequence
  $ 0 -> S K_0 lr((Lambda)) -> K_0 lr((Lambda)) -> K_0 lr((A)) -> 0, $
  with $K_0 lr((A)) tilde.equiv ZZ$ since $A$ is a simple algebra. The proof of
  @th:dedekind-order-projective-grothendieck then gives
  $S K_0 lr((Lambda)) tilde.equiv op("Cl")_A R$, which establishes the theorem.
]

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [The theorem exhibits $op("Cl") Lambda$ as a “restricted” ideal class group
      of $R$, where the restriction is placed on the kind of principal ideals
      used. The result shows that $op("Cl") Lambda$ is independent of the choice
      of the maximal order $Lambda$. This is clear in any case from the fact
      that any two such orders are Morita equivalent. See also Exercise
      @exc:maximal-order-idele-conjugacy.],
    [We can also obtain the theorem by a more complicated argument based on
      @th:class-group-reduced-norm-ideles.
      #source(250)
      Indeed, from @th:class-group-reduced-norm-ideles and its proof we obtain
      $
        op("Cl") Lambda tilde.equiv J(K) slash K^+ U(R),
        quad "where" U(R)=product_P R_P^dot.
      $
      As in Example @i:exm:commutative-idele-class-group, we have
      $J(K) slash K^+ U(R) tilde.equiv op("Cl")_A R$.],
  )
] <rem:maximal-order-class-group-independence>

Returning to the case where $Lambda$ is an arbitrary order, and $K$ any field,
let $Lambda'$ be a maximal $R$-order in $A$ containing $Lambda$. By
@th:class-group-ring-homomorphism, there is a surjection
$op("Cl") Lambda -> op("Cl") Lambda'$, whose kernel $D(Lambda)$ is called the
_kernel group_ of $Lambda$. Thus, there is an exact sequence
$ 0 -> D(Lambda) -> op("Cl") Lambda -> op("Cl") Lambda' -> 0. $
<eq:class-group-kernel-sequence>
#idx("D(Λ)", target: [@eq:class-group-kernel-sequence])
#idx("Kernel group", target: [@eq:class-group-kernel-sequence])
#nidx("$D(Lambda)$", "kernel group", target: [@eq:class-group-kernel-sequence])
We shall see in a moment that $D(Lambda)$ is independent of the choice of
$Lambda'$.

The problem of calculating $op("Cl") Lambda$ reduces to that of calculating
$op("Cl") Lambda'$ and $D(Lambda)$, and the former can be handled by the
previous theorem (at least when $K$ is a global field). In most cases,
$D(Lambda)$ is harder to compute. There is also a secondary question, so far
settled in very few cases: what is the nature of the extension
@eq:class-group-kernel-sequence of $op("Cl") Lambda'$ by $D(Lambda)$?

We begin our discussion of kernel groups with an easy criterion, due to
Jacobinski, for a locally free ideal to give an element of $D(Lambda)$:

#proposition[
  Let $M in g(Lambda)$. Then $[M] in D(Lambda)$ if and only if
  $
    M plus.o X tilde.equiv Lambda plus.o X
    quad "for some f.g. left" Lambda "-module" X.
  $
  Consequently, $D(Lambda)$ is independent of the choice of $Lambda'$ in
  @eq:class-group-kernel-sequence.
] <prop:kernel-group-stable-lattice-criterion>
#proof[
  Given an isomorphism $M plus.o X tilde.equiv Lambda plus.o X$, let $t(X)$ be
  the $R$-torsion submodule of $X$, and put $overline(X)=X slash t(X)$, a
  $Lambda$-lattice. The isomorphism must carry $t(X)$ to itself, and so induces
  an isomorphism
  $ M plus.o overline(X) tilde.equiv Lambda plus.o overline(X). $
  We shall use this observation soon.

  Now let $Lambda subset.eq Lambda' = "maximal order"$. Since $M or Lambda$, it
  follows from Exercise @i:exc:genus-overorder-tensor-exchange that there is a
  $Lambda$-isomorphism
  $ M plus.o Lambda' tilde.equiv Lambda plus.o (Lambda' times.o M), $
  where $times.o$ means $times.o_Lambda$. If $[M] in D(Lambda)$, then
  $[Lambda' times.o M]=0$ in $op("Cl") Lambda'$, so $Lambda' times.o M$ is
  stably isomorphic to $Lambda'$. Adding copies of $Lambda'$ to both sides of
  the above isomorphism, we obtain
  $M plus.o Lambda'^((k)) tilde.equiv Lambda plus.o Lambda'^((k))$ for some $k$,
  as desired.

  #source(251)
  Conversely, suppose $M plus.o X tilde.equiv Lambda plus.o X$ for some $X$;
  apply $Lambda' times.o ast$ to both sides and factor out the torsion
  submodules, obtaining a $Lambda'$-isomorphism
  $
    (Lambda' times.o M) plus.o Y tilde.equiv Lambda' plus.o Y
    quad "for some" Lambda' "-lattice" Y.
  $
  But $Y$ is $Lambda'$-projective by @i:th:maximal-orders-are-hereditary(ii), so
  $Lambda' times.o M$ is stably isomorphic to $Lambda'$, that is,
  $[Lambda' times.o M]=0$ in $op("Cl") Lambda'$. Thus $[M] in D(Lambda)$, as
  claimed.
]

#corollary[
  If $Lambda$ is any hereditary order in $A$, and $Lambda'$ is a maximal order,
  then $op("Cl") Lambda tilde.equiv op("Cl") Lambda'$.
] <cor:hereditary-order-class-group-maximal-order>
#proof[
  If $[M] in D(Lambda)$, then $M plus.o X tilde.equiv Lambda plus.o X$ for some
  $Lambda$-lattice $X$. But $X$ is $Lambda$-projective by
  @i:prop:hereditary-free-submodules and Exercise
  @i:exc:lattice-embedding-finite-free-order-module, so $[M]=0$.
]

The idele-theoretic formulas for $op("Cl") Lambda$ and $op("Cl") Lambda'$
combine to give a formula for $D(Lambda)$, as follows:

#theorem[
  Let $K$ be a global field, and let $frak(O)$ be the integral closure of $R$ in
  the center $C$ of $A$. Then
  $
    D(Lambda) tilde.equiv
    (C^+ dot product frak(O)_P^dot) /
    (C^+ dot product op("nr") Lambda_P^dot),
  $
  where $P$ ranges over all prime ideals of $R$, and $C^+$ is as in
  @th:class-group-reduced-norm-ideles.
] <th:kernel-group-unit-idele-formula>
#proof[
  Let $Lambda'$ be a maximal order containing $Lambda$. As pointed out in
  @eq:local-maximal-order-whitehead-norms, we have
  $op("nr") lr((Lambda'_P^dot))=frak(O)_P^dot$. From
  @th:class-group-reduced-norm-ideles we then obtain
  $
    op("Cl") Lambda' = J(C) slash C^+ U(frak(O)),
    quad "where" U(frak(O))=product_P frak(O)_P^dot.
  $
  <eq:maximal-order-class-group-unit-ideles>
  Comparing the above with formula @th:class-group-reduced-norm-ideles for
  $op("Cl") Lambda$, the theorem follows.
]

#proposition[
  Let $phi: A -> B$ be a homomorphism of $K$-algebras such that
  $phi(Lambda) subset.eq Gamma$, where $Lambda,Gamma$ are $R$-orders in $A,B$,
  respectively. Then $phi$ induces a map $phi_*: D(Lambda) -> D(Gamma)$, and
  $phi_*$ is surjective whenever $phi(A)=B$.
] <prop:kernel-group-ring-homomorphism>
#proof[
  Let $M or Lambda$ be such that $[M] in D(Lambda)$; then by
  @prop:kernel-group-stable-lattice-criterion
  $M plus.o X tilde.equiv Lambda plus.o X$ for some f.g. $Lambda$-module $X$.
  Applying $Gamma times.o_Lambda ast$ to this isomorphism, it follows that
  $[Gamma times.o_Lambda M] in D(Gamma)$, so
  $phi_* D(Lambda) subset.eq D(Gamma)$.

  Now let $phi(A)=B$, so $phi$ is a projection of $A$ onto the sum of certain
  simple components of $A$. If $Lambda'$ is a maximal order in $A$, then
  $phi(Lambda')$ is a maximal order in $B$. However, we have
  $
    D(Lambda) tilde.equiv
    (im K_1 lr((A)) dot im U K_1 lr((Lambda'))) /
    (im K_1 lr((A)) dot im U K_1 lr((Lambda)))
  $
  by @prop:class-group-k1-idele-description, where all of these images lie in
  $J K_1 lr((A))$. It is then obvious that $phi_*$ is surjective.
]

#source(252)
Next, we show how to use @th:reiner-ullom-class-group-mayer-vietoris to obtain
information about kernel groups rather than class groups.

#theorem[
  Given a fiber product as in @th:reiner-ullom-class-group-mayer-vietoris, there
  is an exact “Mayer–Vietoris sequence”
  $
    K_1 lr((Lambda_1)) times K_1 lr((Lambda_2)) ->
    K_1 lr((overline(Lambda))) arrow.r^(partial') D(Lambda) ->
    D(Lambda_1) plus.o D(Lambda_2) -> 0.
  $
  Further, if $Lambda$ has locally free cancellation, the sequence
  $
    1 -> W -> overline(Lambda)^dot -> D(Lambda) ->
    D(Lambda_1) plus.o D(Lambda_2) -> 0
  $
  is exact, where $W$ is defined as in
  @cor:cancellation-order-unit-class-group-sequence.
] <th:kernel-group-mayer-vietoris>
#proof[
  Let $Lambda'$ be a maximal order containing $Lambda_1 plus.o Lambda_2$. Since
  the diagram
  #class-group-maximal-order-triangle
  commutes, it follows that in the sequence
  @th:reiner-ullom-class-group-mayer-vietoris, we have
  $im partial' subset.eq D(Lambda)$. The remaining assertions are then trivial.
]

Returning to the case where $K$ is a global field, we may simplify the formula
in @th:kernel-group-unit-idele-formula for $D(Lambda)$ by using the set
$S = S(Lambda)$ defined in @eq:order-nonmaximal-primes. We prove

#theorem[
  Let $K$ be a global field, and keep the notation of
  @th:kernel-group-unit-idele-formula. Then
  $
    D(Lambda) tilde.equiv
    (product_(P in S) frak(O)_P^dot) /
    (frak(O)^+ product_(P in S) op("nr") Lambda_P^dot),
  $
  where $frak(O)^+ = C^+ inter frak(O)^dot$, viewed as a subgroup of
  $product_(P in S) frak(O)_P^dot$.
] <th:kernel-group-finite-prime-formula>
#proof[
  Let $Lambda subset.eq Lambda' = "maximal" R "-order in" A$; then
  $Lambda_P=Lambda'_P$ for $P in.not S$. From
  @th:kernel-group-unit-idele-formula we obtain
  $
    D(Lambda) tilde.equiv
    (product frak(O)_P^dot) /
    ((product op("nr") Lambda_P^dot)(C^+ inter product frak(O)_P^dot)),
  $
  where the products extend over all $P$. Now
  $C^+ inter product frak(O)_P^dot = C^+ inter frak(O)^dot = frak(O)^+$, so we
  have
  $
    D(Lambda) tilde.equiv
    (product frak(O)_P^dot) / (frak(O)^+ product op("nr") Lambda_P^dot).
  $
  <eq:kernel-group-all-unit-ideles>
  #source(253)
  Setting $Y = product_(P in.not S) frak(O)_P^dot$, the above may be written as
  $
    D(Lambda) tilde.equiv
    (lr((product_(P in S) frak(O)_P^dot)) times Y) /
    (lr((product_(P in S) op("nr") Lambda_P^dot)) Y frak(O)^+).
  $
  There is a natural homomorphism
  $i: frak(O)^+ -> product_(P in S) frak(O)_P^dot$, and clearly
  $Y frak(O)^+ = i(frak(O)^+) times Y$. This gives the desired formula for
  $D(Lambda)$, with $frak(O)^+$ in the denominator understood as its image
  $i(frak(O)^+)$.
]

Following the above approach, we now give Fröhlich’s generalization of the
Mayer–Vietoris sequence @th:kernel-group-mayer-vietoris, valid when $K$ is a
global field. In addition to the notation in
@th:kernel-group-finite-prime-formula, we introduce the unit idele groups
$ U(frak(O))=product_P frak(O)_P^dot, quad U(Lambda)=product_P Lambda_P^dot, $
where $P$ ranges over all maximal ideals of $R$. The reduced norm
$op("nr"): A -> C$ induces a reduced norm map
$op("nr"): U(Lambda) -> U(frak(O))$.

#theorem(title: [Fröhlich @bib:Frohlich1975])[
  Let $K$ be a global field, and let
  $
    A=A_1 plus.o A_2, quad C=C_1 plus.o C_2,
    quad frak(O)=frak(O)_1 plus.o frak(O)_2,
    quad Lambda subset.eq Lambda_1 plus.o Lambda_2,
  $
  where $A_1$ and $A_2$ are direct sums of Wedderburn components of $A$, and
  where $Lambda_i$ is an $R$-order in $A_i$, $i=1,2$. Then there is an exact
  sequence
  $
    op("nr") U(Lambda) ->
    (frak(O)_1^+ op("nr") U(Lambda_1)) / (frak(O)_1^+) times
    (frak(O)_2^+ op("nr") U(Lambda_2)) / (frak(O)_2^+) ->
    D(Lambda) -> D(Lambda_1) plus.o D(Lambda_2) -> 0.
  $
  <eq:frohlich-kernel-group-exact-sequence>
] <th:frohlich-kernel-group-exact-sequence>
#idx("Fröhlich's Theorem", target: [@th:frohlich-kernel-group-exact-sequence])
#idx(
  "Mayer-Vietoris sequence",
  target: [@th:frohlich-kernel-group-exact-sequence],
)
#proof[
  We note first that
  $
    U(frak(O))=U(frak(O)_1) times U(frak(O)_2),
    quad frak(O)^dot=frak(O)_1^dot times frak(O)_2^dot,
    quad frak(O)^+=frak(O)_1^+ times frak(O)_2^+.
  $
  Formula @eq:kernel-group-all-unit-ideles takes the form
  $
    D(Lambda) tilde.equiv
    (U(frak(O))) / (frak(O)^+ op("nr") U(Lambda)).
  $
  #source(254)
  There are analogous formulas for $D(Lambda_1)$ and $D(Lambda_2)$. Since
  $U(frak(O))=U(frak(O)_1) times U(frak(O)_2)$, it follows that there is a
  surjection
  $
    theta: (U(frak(O))) / (frak(O)^+ op("nr") U(Lambda)) ->
    (U(frak(O)_1)) / (frak(O)_1^+ op("nr") U(Lambda_1)) times
    (U(frak(O)_2)) / (frak(O)_2^+ op("nr") U(Lambda_2)).
  $
  We have used the fact that for $i=1,2$, the projection map $A -> A_i$ carries
  $U(frak(O))$ to $U(frak(O)_i)$, $C^+$ to $C_i^+$, and $op("nr") U(Lambda)$ to
  $op("nr") U(Lambda_i)$.

  The kernel of $theta$ is clearly the image of
  $
    (frak(O)_1^+ op("nr") U(Lambda_1)) / (frak(O)_1^+) times
    (frak(O)_2^+ op("nr") U(Lambda_2)) / (frak(O)_2^+)
  $
  in $U(frak(O)) slash frak(O)^+ op("nr") U(Lambda)$. Finally, from the fact
  that
  $
    (frak(O)_i^+ op("nr") U(Lambda_i)) / (frak(O)_i^+) tilde.equiv
    (op("nr") U(Lambda_i)) / (frak(O)_i^+ inter op("nr") U(Lambda_i))
  $
  <eq:kernel-group-norm-subgroup-quotient>
  for $i=1,2$, it is easily seen that the sequence
  @eq:frohlich-kernel-group-exact-sequence is exact. This completes the proof.
]

#remark(numbered: true)[
  A fiber product @eq:order-class-group-fiber-product gives rise to a
  decomposition $A=A_1 plus.o A_2$ in which
  $Lambda subset.eq Lambda_1 plus.o Lambda_2$, so the sequence
  @eq:frohlich-kernel-group-exact-sequence can be viewed as a modified version
  of the Mayer–Vietoris sequence @th:kernel-group-mayer-vietoris.
] <rem:frohlich-sequence-fiber-product-comparison>

#heading(level: 3)[
  Frobenius Functor Properties for Class Groups of Group Rings
] <ss:class-group-frobenius>

Throughout this subsection, let $G$ be a finite group, and $K$ a global field
for which $char K divides.not |G|$. Let $R$ be a Dedekind domain with quotient
field $K$. In most applications we choose $R = "alg. int." {K}$, but for the
moment we shall not impose this hypothesis. The first result is due to Reiner
@bib:Reiner1975 and Matchett @bib:Matchett1977:

#theorem[
  Both $op("Cl") R G$ and $D(R G)$ are Frobenius modules over the Frobenius
  functor $G_0^R lr((R G))$.
] <th:class-kernel-groups-lattice-frobenius>
#idx("Frobenius module", target: [@th:class-kernel-groups-lattice-frobenius])
#proof[
  For each $G$, we have defined $G_0^R lr((R G))$ to be the Grothendieck group
  associated with the category of left $R G$-lattices, with multiplication given
  by inner tensor products (over $R$) of $R G$-lattices (see
  @def:lattice-grothendieck-group). As shown in
  @exm:frobenius-modules-morphisms, both $K_0 lr((R G))$ and $K_0 lr((K G))$ are
  Frobenius modules over the Frobenius functor $G_0^R lr((R G))$, and the map
  $K_0 lr((R G)) -> K_0 lr((K G))$ is a morphism of Frobenius modules. Its
  kernel $S K_0 lr((R G))$ is therefore also a Frobenius module over
  $G_0^R lr((R G))$.

  By @eq:class-group-localization-kernel-isomorphism, there is an exact sequence
  #equation-suffix(base: [@th:class-kernel-groups-lattice-frobenius])[$
    0 -> op("Cl") R G -> S K_0 lr((R G)) arrow.r^gamma
    product.co_P S K_0 lr((R_P G)) -> 0,
  $] <eq:class-group-localization-frobenius-sequence>
  #source(255)
  where $P$ ranges over all maximal ideals of $R$. Since $gamma$ is also a
  morphism of Frobenius modules, it follows that $op("Cl") R G$ is itself a
  Frobenius module over $G_0^R lr((R G))$.

  We show next that the kernel group $D(R G)$, defined as
  @eq:class-group-kernel-sequence, is also a Frobenius module. The entire
  difficulty lies in showing that kernel groups behave properly under
  restriction and induction. For $H <= G$, the inclusion $R H subset.eq R G$
  gives rise to maps
  $
    op("res")_H^G: op("Cl") R G -> op("Cl") R H,
    quad op("ind")_H^G: op("Cl") R H -> op("Cl") R G.
  $
  It is clear from @prop:kernel-group-stable-lattice-criterion that
  $op("ind")_H^G D(R H) subset.eq D(R G)$, as desired.

  Turning to the restriction map, let $abs(G colon H)=n$, so
  $R G tilde.equiv (R H)^((n))$ as $R H$-modules. Since $K_0 lr((R G))$ is
  spanned by f.g. projective $R G$-modules, it follows that $op("res")_H^G$
  carries $K_0 lr((R G))$ into $K_0 lr((R H))$. We now identify $op("Cl") R G$
  with $ker gamma$ as in @eq:class-group-localization-kernel-isomorphism, where
  $gamma$ is as in @eq:class-group-localization-frobenius-sequence. Let
  $x in D(R G)$ be expressed as $x=[M]-[R G]$ where $M or R G$ (since
  $gamma(x)=0$). Then
  $ op("res")_H^G x = [M_H]-n[R H] in S K_0 lr((R H)). $
  But $M_H or (R H)^((n))$, so by @prop:genus-lattice-decomposition we may write
  $M_H tilde.equiv N plus.o (R H)^((n-1))$ for some $N or R H$. Therefore
  $ op("res")_H^G x = [N]-[R H] in S K_0 lr((R H)). $
  On the other hand, since $x in D(R G)$ we have
  $M plus.o X tilde.equiv R G plus.o X$ for some f.g. $R G$-module $X$, by
  @prop:kernel-group-stable-lattice-criterion. Restricting to $H$, it follows
  that $N plus.o Y tilde.equiv R H plus.o Y$, where
  $Y=X_H plus.o (R H)^((n-1))$, and therefore $op("res")_H^G x in D(R H)$ as
  desired. We leave it as an exercise for the reader to verify that the
  induction and restriction maps between $D(R H)$ and $D(R G)$ satisfy the
  axioms in @def:frobenius-module.
]

A somewhat surprising consequence is:

#corollary[
  Both $op("Cl") R G$ and $D(R G)$ are Frobenius modules over the Frobenius
  functor $G_0 lr((K G))$.
] <cor:class-kernel-groups-field-frobenius>
#proof[
  Let $phi: G_0^R lr((R G)) -> G_0 lr((K G))$ be the ring surjection induced by
  the inclusion map $R G subset.eq K G$, as in
  @th:integral-grothendieck-finite-kernel. It suffices to show that $ker phi$
  annihilates $op("Cl") R G$. By @th:integral-grothendieck-finite-kernel, every
  element of $ker phi$ has the form $[R G]-[M]$ for some $M or R G$. But the
  typical element of $op("Cl") R G$ is of the form $[R G]-[N]$, with $N or R G$.
  However,
  $ ([R G]-[M])([R G]-[N])=0 quad "in" K_0 lr((R G)) $
  by the proof of @th:integral-grothendieck-square-zero-kernel. Therefore
  $(ker phi) dot op("Cl") R G=0$, as desired.
]

(Swan @bib:Swan1960, @bib:Swan1963 showed that $op("Cl") R G$ is a Frobenius
module over $G_0 lr((K G))$. The corresponding result for $D(R G)$ was
established by Endo–Miyata @bib:Endo1973 and Matchett @bib:Matchett1977.
#source(256)
For other results of this nature, see also Ullom @bib:Ullom1981.)

Along the same lines as the previous theorem, we have:

#proposition[
  $K_0 lr((ZZ G))$ is a Frobenius module over the Frobenius functor
  $G_0 lr((QQ G))$.
] <prop:rational-grothendieck-projective-action>
#idx(
  "Frobenius module",
  target: [@prop:rational-grothendieck-projective-action],
)
#proof[
  By @i:cor:swan-projective-lattice-left-ideal-decomposition, each
  $x in K_0 lr((ZZ G))$ is of the form
  $ x=m[ZZ G]-[M] quad "for some" m in ZZ quad "and some" M or ZZ G. $
  As above,
  $ ([ZZ G]-[N])([ZZ G]-[M])=0 quad "in" K_0 lr((ZZ G)) $
  for any $N or ZZ G$. On the other hand,
  $
    ([ZZ G]-[N]) dot [ZZ G] =
    [ZZ G times.o_ZZ ZZ G]-[N times.o_ZZ ZZ G]=0,
  $
  the last equality because $N times.o_ZZ ZZ G$ is $ZZ G$-free of rank $|G|$, by
  Exercise @i:exc:regular-inner-tensor-free. This shows that $ker phi$
  annihilates $K_0 lr((ZZ G))$, where $phi: G_0^ZZ lr((ZZ G)) -> G_0 lr((QQ G))$
  is the ring surjection induced by the inclusion $ZZ G subset.eq QQ G$. The
  rest is now clear.
]

#exercises-heading

#exercise[
  Let $A$ be a f.d. $K$-algebra with center $C$, and let $E$ be any extension
  field of $K$. Prove that $E times.o_K A$ is a f.d. $E$-algebra with center
  $E times.o_K C$. In particular, if $E$ is a $P$-adic completion $K_P$ of a
  field $K$ relative to some prime $P$ of $K$, show that the center of $A_P$ is
  $C_P (= K_P times.o_K C)$.
] <exc:center-under-field-extension>
#hint([@exc:center-under-field-extension])[
  Let $C'$ denote the center of $E times.o A$, where $times.o$ means
  $times.o_K$. Clearly $C' supset.eq E times.o C$. Now write
  $E=plus.o.big K e_i$, so $E times.o A = plus.o.big(e_i times.o A)$. If
  $x=sum e_i times.o a_i in C'$, then $x$ commutes with $1 times.o a$ for each
  $a in A$. Therefore each $a_i in C$, so $x in E times.o C$.
]

#exercise[
  Let $Lambda$ be an $R$-order, and set $Gamma=M_n lr((Lambda))$. Show that
  $
    op("Cl") Lambda tilde.equiv op("Cl") Gamma,
    quad D(Lambda) tilde.equiv D(Gamma).
  $
] <exc:matrix-order-class-kernel-groups>

#exercise[
  Starting with a fiber product @eq:order-class-group-fiber-product with $g_1$
  or $g_2$ surjective, there is a fiber product
  #matrix-order-fiber-product-square
  for $n >= 2$.
  #source(257)
  Deduce from @cor:cancellation-order-unit-class-group-sequence,
  @th:kernel-group-mayer-vietoris, and @th:jacobinski-cancellation that there
  are exact sequences
  #matrix-class-kernel-sequence-fork
  where
  $ W = {w_1 w_2: w_i in h_i lr((GL_n lr((Lambda_i)))), quad i=1,2}. $
] <exc:matrix-unit-class-kernel-sequences>

#exercise[
  Keep the above notation and suppose that $g_1$ maps $Lambda_1^dot$ onto
  $overline(Lambda)^dot$. Show that
  $
    op("Cl") Lambda tilde.equiv op("Cl") Lambda_1 plus.o op("Cl") Lambda_2,
    quad D(Lambda) tilde.equiv D(Lambda_1) plus.o D(Lambda_2).
  $
] <exc:unit-surjection-class-kernel-splitting>
#hint([@exc:unit-surjection-class-kernel-splitting])[
  Since $overline(Lambda)^dot$ maps onto $K_1 lr((overline(Lambda)))$, so does
  $K_1 lr((Lambda_1))$.
]

#exercise[
  Starting with a fiber product @eq:order-class-group-fiber-product in which
  $g_1$ or $g_2$ is surjective, suppose that
  $ g_1 lr((Lambda_1^dot)) = (g_1 lr((Lambda_1)))^dot. $
  Show that the surjections
  $ op("Cl") Lambda -> op("Cl") Lambda_1, quad D(Lambda) -> D(Lambda_1) $
  are split.
] <exc:class-kernel-projection-split>
#hint([@exc:class-kernel-projection-split], caption: [Hint (Reiner–Ullom
  @bib:Reiner1974a):])[
  If $g_1 lr((Lambda_1))=overline(Lambda)$, the result follows from Exercise
  @exc:unit-surjection-class-kernel-splitting. If
  $g_1 lr((Lambda_1)) != overline(Lambda)$, then by hypothesis
  $g_2 lr((Lambda_2))=overline(Lambda)$. Setting
  $Lambda_3 = g_2^(-1) lr((g_1 lr((Lambda_1))))$, there is a fiber product
  #restricted-image-fiber-product-square
  Then
  $
    op("Cl") Lambda tilde.equiv op("Cl") Lambda_1 plus.o op("Cl") Lambda_3,
    quad D(Lambda) tilde.equiv D(Lambda_1) plus.o D(Lambda_3)
  $
  by the first case.
]

#exercise[
  Let $Lambda$ be an $R$-order, and let $M,N in cal(P) lr((Lambda))$ be such
  that $M plus.o X tilde.equiv N plus.o X$ for some f.g. $Lambda$-module $X$ of
  finite homological dimension. Prove that $[M]=[N]$ in $K_0 lr((Lambda))$.
] <exc:finite-homological-witness-stable-class>
#hint([@exc:finite-homological-witness-stable-class])[
  Use @th:finite-homological-dimension-k-groups.
]

#exercise[
  Let $Lambda subset Lambda'$ be $R$-orders in $A$, and suppose that
  $op("hd")_Lambda Lambda'$ is finite. Deduce that
  $op("Cl") Lambda tilde.equiv op("Cl") Lambda'$.
] <exc:finite-homological-overorder-class-group>

#exercise[
  Let $X$ be a locally free $Lambda$-lattice, and let $Lambda' supset Lambda$.
  Show that the map
  $ Lambda' times.o X -> Lambda' X subset K X $
  is an isomorphism. This also holds for $X in cal(P) lr((Lambda))$.
] <exc:overorder-projective-tensor-multiplication>

#exercise[
  Let $Lambda_1$ and $Lambda_2$ be a pair of maximal $R$-orders in $A$. Show
  that $Lambda_2 = beta Lambda_1 beta^(-1)$ for some idele $beta in J(A)$, and
  deduce that
  $ J_0 lr((A)) A^dot U(Lambda_2) = J_0 lr((A)) A^dot U(Lambda_1), $
  which gives $op("Cl") Lambda_1 tilde.equiv op("Cl") Lambda_2$ (see
  @th:maximal-order-restricted-ideal-class-group).
] <exc:maximal-order-idele-conjugacy>

#source(258)
#exercise[
  Let $Lambda subset Gamma$ be a pair of $R$-orders in a f.d. $K$-algebra, and
  let $I$ be a two-sided $Gamma$-ideal contained in $Lambda$, such that $K I=A$.
  There is a fiber product
  #overorder-ideal-fiber-product-square
  where $overline(Lambda)=Lambda slash I$ and $overline(Gamma)=Gamma slash I$.
  Using Milnor’s Theorem @th:milnor-mayer-vietoris and the ideas in the proof of
  @th:reiner-ullom-class-group-mayer-vietoris, prove that these are exact
  sequences.
  #overorder-class-kernel-sequence-fork
  In particular, if $A$ is a commutative algebra and $Gamma$ is a maximal order,
  prove that
  $
    D(Lambda) tilde.equiv overline(Gamma)^dot slash
    ("image of" Gamma^dot)("image of" overline(Lambda)^dot).
  $
] <exc:full-ideal-class-kernel-sequences>
#hint([@exc:full-ideal-class-kernel-sequences], caption: [Hint (Matchett
  @bib:Matchett1980):])[
  Let $P$ range over the maximal ideals of $R$. There is a commutative diagram
  with exact rows
  #full-ideal-localization-comparison
  Since $overline(Gamma)$ and $overline(Lambda)$ are $R$-torsion $R$-algebras,
  we have
  $
    overline(Gamma) tilde.equiv product.co_P overline(Gamma)_P,
    quad overline(Lambda) tilde.equiv product.co_P overline(Lambda)_P,
  $
  so $f_1$, $f_4$, and $f_5$ are isomorphisms. Further, for each $P$ the map
  $K_1 lr((overline(Gamma)_P)) -> K_0 lr((Lambda_P))$ is the zero map (since
  $(Gamma_P)^dot -> (overline(Gamma)_P)^dot$ is surjective; see proof of
  @th:reiner-ullom-class-group-mayer-vietoris). Thus $partial'$ is the zero map.
  It follows easily that
  $ K_1 lr((overline(Gamma))) -> ker f_2 -> ker f_3 -> 0 $
  is exact. Finally, $ker f_2 tilde.equiv op("Cl") Lambda$ and
  $ker f_3 tilde.equiv op("Cl") Gamma$. Note also that $im partial subset.eq
  ker(op("Cl") Lambda -> op("Cl") Gamma) subset.eq D(Lambda)$.

  If $A$ is commutative, then the determinant map gives an isomorphism
  $det: K_1 lr((overline(Gamma))) tilde.equiv overline(Gamma)^dot$. Since
  #full-ideal-determinant-square
  commutes, it is clear that $K_1 lr((Gamma))$ and $Gamma^dot$ have the same
  image in $overline(Gamma)^dot$.
]

#source(259)
#exercise[
  Given a surjection $G -> overline(G)$ of finite groups, show that there is a
  surjection
  $ D(ZZ G) -> D(ZZ overline(G)). $
] <exc:group-quotient-kernel-group-surjection>
#hint([@exc:group-quotient-kernel-group-surjection])[
  Use @prop:kernel-group-ring-homomorphism.
]

#exercise[
  Let $G=N times.r H$ be a semidirect product. Prove that there are split
  surjections
  $ op("Cl") ZZ G -> op("Cl") ZZ H, quad D(ZZ G) -> D(ZZ H). $
] <exc:semidirect-class-kernel-split-surjections>
