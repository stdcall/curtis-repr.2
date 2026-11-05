#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/51-newton.typ": newton-polygon, two-slope-newton-polygon

#heading(level: 2)[
  Jacobinski’s Cancellation Theorem and the Eichler Condition
] <sec:cancellation-theorems>

#idx("Stable isomorphism")
#idx("Locally free cancellation")

Throughout this section, let $Lambda$ be an $R$-order in a f.d. separable
$K$-algebra $A$, where $R$ is a Dedekind domain whose quotient field $K$ is a
global field. We assume always that $R != K$, to avoid trivialities. A left
$Lambda$-lattice $X$ is called _locally free_ (of rank $n$) if
$X_P tilde.equiv Lambda_P^((n))$ as left $Lambda_P$-modules, for each maximal
ideal $P$ of $R$. (The subscript $P$ denotes $P$-adic completion.) If $X,Y$ are
locally free $Lambda$-lattices of the same rank, we call $X$ _stably isomorphic_
to $Y$ if
$
  X plus.o Lambda^((k)) tilde.equiv Y plus.o Lambda^((k))
  quad "for some" k >= 0.
$
We say that the order $Lambda$ has _locally free cancellation_ if
$ X "stably isomorphic to" Y <=> X tilde.equiv Y, $
<eq:locally-free-cancellation>
that is, we can “cancel” the summands $Lambda^((k))$. In many applications, it
is of the utmost importance to know whether $Lambda$ has locally free
cancellation.

One of the main results of this section is the Jacobinski Cancellation Theorem
@th:jacobinski-cancellation, which guarantees that every $R$-order $Lambda$ in
$A$ has locally free cancellation, provided that $A$ satisfies the Eichler
condition#footnote[
  See Definition @def:eichler-condition, as well as §@ss:eichler-condition.
] relative to $R$. Examples due to Eichler and Swan show that the Eichler
condition is a _sufficient_ condition for locally free cancellation, but is not
a necessary condition.

By @prop:genus-lattice-decomposition, each locally free $Lambda$-lattice $X$ of
rank $n$ can be written as
$ X tilde.equiv Lambda^((n-1)) plus.o X_0, $
with $X_0$ a locally free $Lambda$-lattice of rank 1. Further, by
§@i:ss:ideles-locally-free-class-groups, $X_0$ is isomorphic to a locally free
left ideal of $Lambda$. It follows at once that $Lambda$ has locally free
cancellation if and only if @eq:locally-free-cancellation holds for locally free
ideals $X$ and $Y$.

#idx("Locally free class group")
By definition, the _locally free class group_ $op("Cl") Lambda$ is the finite
abelian group whose elements are stable isomorphism classes $[X]$ of locally
free ideals $X$ of
#source(320)
#idx("Principal genus")
#idx("Genus", "principal")
$Lambda$ (that is, ideals in the _principal genus_ $g(Lambda)$). Then $Lambda$
has locally free cancellation if and only if for $X,Y in g(Lambda)$,
$ [X]=[Y] <=> X tilde.equiv Y. $

The proof of Jacobinski’s Theorem depends on a deep result concerning strong
approximation for the kernel of the reduced norm map. This result was
established by Eichler @bib:Eichler1938 when $K$ is an algebraic number field,
and by Swan @bib:Swan1980 for $K$ a (global) function field. The Eichler
condition is a sufficient condition for the validity of this Eichler–Swan
Theorem, which is proved in §@ss:eichler-swan-theorem.

=== The Eichler Condition <ss:eichler-condition>

In this subsection, we recall Definition @def:eichler-condition of the Eichler
condition, and give examples where the condition holds true or fails. If $K$ is
an algebraic number field, the condition is the same as Eichler’s original
formulation, as generalized by Swan (see Swan–Evans @bib:SwanEvans1970 or
@bib:Reiner1975[MO] (34.3)). On the other hand, if $K$ is a (global) function
field, the present version of the Eichler condition is a _weaker_ restriction
than that given in the above-cited references. As we shall see for $K$ any
global field, the Eichler condition defined below is a _sufficient_ condition
for the validity of the Eichler–Swan Theorem
@th:eichler-swan-strong-approximation, concerning strong approximation for the
kernel of the reduced norm.

#idx("Eichler condition")
#idx("Totally definite quaternion algebra")

Let $P$ range over the primes of the global field $K$. Those primes $P$ which
come from maximal ideals of $R$ are called “$R$-primes” of $K$, while all others
are “non-$R$ primes”. If $A$ is a central simple $K$-algebra, we say that $A$
satisfies the _Eichler condition relative to $R$_, and write
$A = "Eichler" slash R$, except when the $P$-adic completion $A_P$ is a
noncommutative skewfield for _every_ non-$R$ prime $P$ of $K$. Extending this
definition to the case where $A$ is a f.d. separable $K$-algebra with Wedderburn
components ${A_i}$, we write
$
  A = "Eichler" slash R <=> A_i = "Eichler" slash R_i
  quad "for each" i,
$
where $R_i$ is the integral closure of $R$ in the center of $A_i$.

As observed in @rem:eichler-condition-variants, if $R="alg. int." {K}$ with $K$
a number field, the only central simple $K$-algebras $A$ which _fail_ to be
$"Eichler" slash R$ are the _totally definite quaternion algebras_. (By
definition, these are algebras $A$ such that every infinite prime $P$ of $K$ is
a real prime, and such that $A_P tilde.equiv "real quaternions"$ for every
infinite prime $P$ of $K$.)

#examples(numbered: false)[
  #enum(
    numbering: "(i)",
    [The algebra $QQ plus.o QQ i plus.o QQ j plus.o QQ k$ of rational
      quaternions is a totally definite quaternion algebra.],
    [More generally, let $K$ be a totally real number field, so we may write
      $K=QQ(alpha)$, where
      $
        op("min. pol.")_QQ lr((alpha)) = product_(i=1)^n (x-alpha_i),
        quad "with each" alpha_i in RR.
      $
      #source(321)
      Then $K$ has $n$ real primes $P_1,dots,P_n$, and the isomorphism
      $K_(P_t) tilde.equiv RR$ is given by $alpha arrow.r alpha_t$,
      $1 <= t <= n$. Now set
      $
        A=K plus.o K i plus.o K j plus.o K k,
        quad "where" i^2=c, quad j^2=d, quad k=i j=-j i,
      $
      and where $c,d$ are totally negative elements of $K$ (that is, $c<0$ and
      $d<0$ in each $K_(P_t)$, $1<=t<=n$). Then $A$ is a totally definite
      quaternion algebra with center $K$.],
  )
]

Next, we list some cases where the Eichler condition obviously holds true:

#proposition[
  Let $A$ be a f.d. separable $K$-algebra. Then $A="Eichler" slash R$ in each of
  the following cases:
  #enum(
    numbering: "(i)",
    [$A$ is commutative.],
    [$A tilde.equiv M_n lr((D))$ where $n>1$ and $D$ is a $K$-algebra.],
    [$K$ is an algebraic number field with at least one complex prime.],
    [$K$ is an algebraic number field, and $A$ is a central simple $K$-algebra
      for which $dim_K A != 4$.],
  )
] <prop:eichler-condition-sufficient-cases>

Now consider the group algebra $A=K G$ of a finite group $G$ over an algebraic
number field $K$, and let $R="alg. int." {K}$. Then $A != "Eichler" slash R$ if
and only if $A$ has a simple component $B$ which is a totally definite
quaternion algebra. Suppose this is the case, and let $P$ be a real prime of the
center of $B$. Then
$ B_P tilde.equiv HH = "skewfield of real quaternions", $
and there is a homomorphism $phi: G arrow.r HH^dot$ given by composition of maps
$ G arrow.r K G=A arrow.r B arrow.r B_P tilde.equiv HH. $
Thus, $G$ must have a homomorphic image $overline(G)$ in $HH^dot$, whose
elements span $HH$ over $RR$.

The finite subgroups of $HH^dot$ are well known (see, e.g., Benson–Grove
@bib:Benson1971, Coxeter @bib:Coxeter1940, or Vignéras @bib:Vigneras1980, Ch. I,
Th. 3.7). To describe these subgroups, we use the notation $⟨p,q,r⟩$ to denote
the group
$ ⟨x,y,z,u: x^p=y^q=z^r=x y z=u, u^2=1⟩. $
Then the finite subgroups of $HH^dot$ are as follows:
#enum(
  numbering: "(1)",
  [$C_n = "cyclic group of order" n >= 1$.],
  [$Q_n = "generalized quaternion group of order" 4n = ⟨2,2,n⟩$, where $n>=1$.],
  [$tilde(T) = "binary tetrahedral group of order" 24 = ⟨2,3,3⟩$.],
  [$tilde(O) = "binary octahedral group of order" 48 = ⟨2,3,4⟩$.],
  [$tilde(I) = "binary icosahedral group of order" 120 = ⟨2,3,5⟩$.],
)

#source(322)
Now $C_n (n>=1)$ and $Q_1$ are abelian groups, and thus cannot span $HH$ over
$RR$. Consequently we obtain:

#theorem[
  Let $A=K G$, where $G$ is a finite group, and $K$ is an algebraic number field
  with $R="alg. int." {K}$. Then $A="Eichler" slash R$ if $G$ has no homomorphic
  image of any of the following types:
  $ Q_n (n>=2), tilde(T), tilde(O), tilde(I). $
  In particular, $A="Eichler" slash R$ if $abs(G)$ is odd.
] <th:group-algebra-eichler-quotient-criterion>

=== The Eichler–Swan Theorem <ss:eichler-swan-theorem>

The main result of this subsection is the Eichler–Swan Theorem, which states
that when $A="Eichler" slash R$, then the Strong Approximation Theorem
@th:eichler-swan-strong-approximation holds true for the kernel of the reduced
norm map. This result is due originally to Eichler @bib:Eichler1938 when $K$ is
an algebraic number field (see also Kneser @bib:Kneser1965). For the case where
$K$ is a function field, the version given below is due to Swan @bib:Swan1980,
and represents a strengthening of his earlier results for this case.

The proof of the Eichler–Swan Theorem is somewhat complicated. Our treatment
here is based on Swan’s article @bib:Swan1980, and is mostly self-contained,
except for relying on some results concerning central simple algebras, proved in
detail in @bib:Reiner1975[MO].

For the convenience of the reader, we begin with a brief review of the topology
on the adèle ring $hat(A)$ and the idele group $J(A)$, where $A$ is a
$K$-algebra.

*Additive Structure.* Let $K$ be a global field, and let $P$ range over the
maximal ideals of $R$. In our discussion, the archimedean primes of $K$ will
play a secondary role. For each $P$, the $P$-adic completion $K_P$ is a complete
metric space relative to the $P$-adic absolute value $phi_P$ defined as in
§@i:ss:valuations-completions. As basis for the neighborhoods of 0 in $K_P$, we
may choose the open sets ${P^n R_P: n>=0}$. Then $K_P$ is a locally compact
topological space, and $R_P$ is compact.

Now let $V$ be any f.d. $K$-space, and let $V_P=K_P times.o_K V$ be its $P$-adic
completion. Choose a $K$-basis ${v_i}$ of $V$, which we view as $K_P$-basis for
$V_P$. We may then define a metric on $V_P$ by the formula
$ norm(sum_i a_i v_i) = "Max" {phi_P lr((a_i))}, quad "where" a_i in K_P. $
This makes $V_P$ into a locally compact metric space, whose topology does not
depend on the choice of $K$-basis of $V$. Let $M$ be any full $R$-lattice in
$V$; the open sets ${P^n M_P:n>=0}$ form a basis for the neighborhoods of 0 in
$V_P$, and $M_P$ is a compact subspace of $V_P$.

Let $hat(A)$ be the _adèle ring_ of $A$, defined as in @exm:wall-square. Thus,
$ hat(A) = {(alpha_P) in product_P A_P: alpha_P in Lambda_P "a.e."}, $
#source(323)
where $P$ ranges over all maximal ideals of $R$, and where $Lambda$ is any
$R$-order in $A$. Note that $hat(A)$ is independent of the choice of $Lambda$,
since if $Gamma$ is another $R$-order in $A$, then $Lambda_P=Gamma_P$ a.e. We
now topologize $hat(A)$ by choosing, as basis for the neighborhoods of 0, all
open sets $U$ of the form
$ U=product_(P in S) N_P lr((0)) times product_(P in.not S) Lambda_P, $
<eq:adele-neighborhood-basis>
where $S$ ranges over all finite sets of primes of $R$, and each $N_P lr((0))$
ranges over all neighborhoods of 0 in $A_P$.

Each $a in A$ determines a principal adèle $(a) in hat(A)$, whose $P$-th
component is $a$ for each $P$. We shall identify $A$ with the ring of principal
adèles. It follows at once from the S.A.T. @i:th:strong-approximation that $A$
is _dense_ in $hat(A)$, that is, given any $x in hat(A)$ and any open set $U$ as
above, there exists a principal adèle $a$ such that $x-a in U$.

*Multiplicative Structure.* Let $hat(A)$ be the adèle ring of $A$, as above. It
is easily seen that the group of units of the ring $hat(A)$ is precisely the
_idele group_ $J(A)$ of $A$ relative to $R$, defined by
$ J(A)={(alpha_P) in product_P A_P^dot: alpha_P in Lambda_P^dot "a.e."}. $
This group depends on $A$ and $R$, but not on $Lambda$.

For each $R$-prime $P$ of $K$, we topologize $K_P^dot$ via the topology induced
from the $P$-adic valuation on $K_P$. As basis for neighborhoods of an element
$x in K_P^dot$, we take the open sets ${(x+P^m R_P) inter K_P^dot:m>=0}$. Thus
for $x,y in K_P^dot$, $y$ is near $x$ if $y-x in P^m R_P$ for large $m$, or
equivalently, if $y in x(1+P^n R_P)$ for large $n$. Then $K_P^dot$ is a locally
compact topological group, and $R_P^dot$ is a compact subgroup.

It is tempting to try topologizing $J(A)$ by means of the adèle topology of
$hat(A)$. However, $J(A)$ is _not_ a topological group in this induced topology
coming from $hat(A)$, since the map $alpha arrow.r alpha^(-1)$, $alpha in J(A)$,
is not continuous. For example, take the simplest case where $R=ZZ$ and $A=QQ$.
For $n>=1$, let
$ alpha_n=(1,dots,1,(p_n)^n,1,dots) in J(A), $
where $p_n$ is the $n$-th rational prime. In the adèle topology,
$lim_(n arrow.r infinity) alpha_n$ is the principal idele 1. On the other hand,
$ alpha_n^(-1)=(1,dots,1,(p_n)^(-n),1,dots) in J(A). $
Given any neighborhood $1+U$, with $U$ as in @eq:adele-neighborhood-basis, we
have $alpha_n^(-1) in.not 1+U$ for all sufficiently large $n$, and therefore
$lim_(n arrow.r infinity) alpha_n^(-1) != 1$ in the topology on $J(A)$ induced
by the adèle topology on $hat(A)$.

We therefore follow the standard procedure in algebraic number theory (see e.g.
Cassels–Fröhlich @bib:Cassels1967 or Weiss @bib:Weiss1963). To begin with, we
topologize
#source(324)
$A_P^dot$ by choosing, as basis for the neighborhoods of 1 in $A_P^dot$, all
open sets ${1+P^n Lambda_P:n>=1}$. Then $A_P^dot$ is locally compact, and
$Lambda_P^dot$ is compact. Now topologize the idele group $J(A)$ by choosing as
basis for the open neighborhoods of $1 in J(A)$, all open sets
$ W=product_(P in S) N_P lr((1)) times product_(P in.not S) Lambda_P^dot, $
<eq:idele-neighborhood-basis>
with $S$ ranging over all finite sets of $R$-primes $P$ of $K$, and where each
$N_P lr((1))$ ranges over all open neighborhoods of 1 in $A_P^dot$. Relative to
this _idele topology_, $J(A)$ is a topological group, and the maps
$
  alpha arrow.r alpha^(-1), quad alpha in J(A), quad "and"
  (alpha,beta) arrow.r alpha beta, quad alpha,beta in J(A),
$
are both continuous. Note that in the counterexample given above, $lim alpha_n$
does not exist in the idele topology.

We remark that the group $A^dot$ of principal ideles is _not_ dense in $J(A)$,
even in the simple case where $R=ZZ$ and $A=QQ$. For example, let
$x in ZZ_2^dot$, $x != plus.minus 1$ ($ZZ_2 = "2-adic integers"$), and consider
the idele $alpha=(x,1,1,dots) in J(A)$. Suppose we wish to choose $a in A^dot$
close to $alpha$ in the idele topology. Then $a x$ is near 1 in $ZZ_2$, while
$a in ZZ_p^dot$ for $p=3,5,7,11,dots$. This forces the equality
$a=plus.minus 2^m$ for some $m in ZZ$, and then we cannot make $a x$ close to 1
in $ZZ_2$.

*Reduced Norms.* Let $A$ be a f.d. separable $K$-algebra with center $C$, and
let
$ frak(O)="integer closure of" R "in" C. $
The reduced norm map $op("nr"):A^dot arrow.r C^dot$ extends to a map
$op("nr"):J(A) arrow.r J(C)$ of idele groups, and this latter homomorphism is
continuous (see, e.g., @bib:Reiner1975[MO] Exercise 33.2). We now define
$ J_0 lr((A))={alpha in J(A):op("nr") alpha=1}. $
<eq:reduced-norm-one-ideles>
#nidx(
  "$J_0 lr((A))$",
  "kernel of reduced norm",
  target: [@eq:reduced-norm-one-ideles],
)
Thus, an idele $alpha=(alpha_P) in J_0 lr((A))$ if and only if
$op("nr")_(A_P slash C_P) alpha_P=1$ for each $P$. Then $J_0 lr((A))$ is a
closed normal subgroup of $J(A)$, and acquires a topology induced from the idele
topology of $J(A)$. We now prove:

#lemma[
  The topology on $J_0 lr((A))$ induced from the idele topology of $J(A)$ agrees
  with that induced from the adèle topology of $hat(A)$.
] <lem:norm-one-idele-adele-topologies>
#proof[
  Let $alpha_0 in J_0 lr((A))$, and suppose $alpha in J_0 lr((A))$ is such that
  $alpha-alpha_0$ is near 0 in $hat(A)$. Then
  $ alpha^(-1) alpha_0-1=alpha^(-1)(alpha_0-alpha), $
  #source(325)
  so once we show that the map $alpha arrow.r alpha^(-1)$,
  $alpha in J_0 lr((A))$, is continuous in the adèle topology, it will follow
  that $alpha^(-1) alpha_0$ is near 1 in $J_0 lr((A))$, as desired.

  In order to prove that the inverse map $alpha arrow.r alpha^(-1)$,
  $alpha in J_0$, is continuous (in the adèle topology), we must show the
  following:

  Given an element $alpha in J_0 lr((A))$ and a neighborhood $U$ as in
  @eq:adele-neighborhood-basis, there exists a neighborhood $U'$ such that
  $ beta in J_0 lr((A)) inter (alpha+U') => beta^(-1) in alpha^(-1)+U. $
  <eq:norm-one-inversion-continuity>
  Let $Lambda$ be an $R$-order in $A$. To begin with, we work with a single
  $R$-prime $P$. Let $xi in A_P^dot$ be such that $op("nr") xi=1$. Then
  $
    op("red. char. pol.")_(A_P slash K_P) xi =
    X^n+a_1 X^(n-1)+dots+a_(n-1) X+(-1)^n in K_(P)[X],
  $
  where $n$ is independent of $xi$. The coefficients ${a_i}$ are continuous
  functions of $xi$ in the $P$-adic topology of $A_P$ (see @bib:Reiner1975[MO]
  Exercise 33.2, for example). We may write
  $
    xi^(-1)=(-1)^(n-1){xi^(n-1)+a_1 xi^(n-2)+dots+a_(n-1)}
    = f(xi) in K_(P)[xi].
  $
  Then $f(xi)$ is a continuous function of $xi$ in the $P$-adic topology.

  Keeping the above notation, suppose that $xi in Lambda_P$ and $op("nr") xi=1$.
  Then the coefficients ${a_i}$ lie in $R_P$, so
  $xi^(-1) in R_(P)[xi] subset.eq Lambda_P$, and therefore $xi in Lambda_P^dot$.

  Now let $alpha in J_0 lr((A))$ be given, as well as a neighborhood $U$. We may
  enlarge the finite set $S$ used to define $U$, so as to include all $R$-primes
  $P$ for which $alpha_P in.not Lambda_P$. We shall choose
  $ U'=product_(P in S) N'_P lr((0)) times product_(P in.not S) Lambda_P, $
  with each $N'_P lr((0))$ a neighborhood of 0 in $A_P$, to be determined later.
  For each $beta=(beta_P) in J_0 lr((A)) inter (alpha+U')$, we then have
  $alpha_P,beta_P in Lambda_P$ for $P in.not S$, and so
  $alpha_P^(-1),beta_P^(-1) in Lambda_P$, which implies that
  $beta_P^(-1)-alpha_P^(-1) in Lambda_P$ for $P in.not S$.

  On the other hand, for each of the finitely many primes $P in S$, we may
  choose a neighborhood $N'_P lr((0))$ in $A_P$, such that if
  $beta_P-alpha_P in N'_P lr((0))$, then
  $beta_P^(-1)-alpha_P^(-1) in N_P lr((0))$. Thus
  @eq:norm-one-inversion-continuity holds for $U'$ as above, which establishes
  the lemma.
]

Before starting the proof of the S.A.T. for the kernel of the reduced norm, let
us record several facts from algebraic number theory, available in most standard
texts on the subject. Let $K$ be a global field as always. For each finite prime
$P$ of $K$, we normalize the $P$-adic absolute value $phi_P$ by setting
$
  phi_P lr((a))=("card" R slash P)^(-v_P lr((a))),
  quad a in K^dot, quad "and" phi_P lr((0))=0,
$
where $v_P lr((a))$ is the largest integer $m$ such that $a in P^m R_P$. For an
infinite prime
#source(326)
$P$ of $K$, and $a in K$, set
$
  phi_P lr((a))=cases(
    abs(a_P) in RR & quad P "real",
    abs(a_P)^2 in RR & quad P "complex".
  )
$
These $P$-adic absolute values are related by:

#theorem(name: [Product Formula])[
  For $a in K^dot$, $phi_P lr((a))=1$ a.e., and
  $ product_P phi_P lr((a))=1, $
  where the product extends over all primes (finite and infinite) of $K$.
] <th:global-field-product-formula>
#idx("Product formula", target: [@th:global-field-product-formula])

Next we quote without proof.

#theorem(name: [Very Strong Approximation Theorem], title: [V.S.A.T.])[
  Let $P_1,dots,P_n$ be distinct primes of $K$ (finite or infinite), and let
  $P_0$ be any other prime of $K$. Given elements ${a_i in K_(P_i):1<=i<=n}$ and
  given any $epsilon>0$, there exists an element $a in K$ such that
  $
    phi_(P_i) lr((a-a_i)) < epsilon quad "for" 1<=i<=n,
    quad "and" phi_P lr((a))<=1 quad "for" P != P_0,P_1,dots,P_n.
  $
] <th:very-strong-approximation>
#idx(
  "Very strong approximation theorem",
  target: [@th:very-strong-approximation],
)

#corollary[
  Let $R="alg. int." {K}$, and let $P_0$ be an infinite prime. Given an element
  $a_i in R_(P_i)$ for each finite prime among ${P_1,dots,P_n}$, and given
  $epsilon>0$, there exists an element $a in R$ for which
  $
    phi_(P_i) lr((a-a_i)) < epsilon quad "for" 1<=i<=n,
    quad "and" phi_P lr((a))<=1 quad "for each infinite prime"
    P in.not {P_0,dots,P_n}.
  $
] <cor:integer-very-strong-approximation>

#idx("Newton polygon")

*Newton Polygons.* We shall need to use Newton polygons to compute the
valuations of the roots of an algebraic equation over a complete local field
$F$. Let $F$ be a $P$-adic field with a non-archimedean exponential valuation
$v$; thus
$ v(a+b)>="Min"(v(a),v(b)) quad "for" a,b in F, $
with equality whenever $v(a)!=v(b)$. First factor the original polynomial as
$x^r g(x)$ with $g(0)!=0$, and write the remaining polynomial as
$ g(x)=a_0 x^n+a_1 x^(n-1)+dots+a_n in F[x], quad a_0 a_n!=0. $
The removed zero roots have valuation $infinity$. If $g$ is constant, there are
no finite sides or nonzero roots. Otherwise, $g$ need not be irreducible; we
plot the points corresponding to its nonzero coefficients:
$ P_0=(0,v(a_0)), quad P_1=(1,v(a_1)),dots,P_n=(n,v(a_n)) $
in Euclidean 2-space. The _Newton polygon_ of $g(x)$ is formed by connecting
some
#source(327)
of these points so as to obtain a polygonal path which is concave upwards, and
such that each $P_i$ is either on or above this polygonal path. A picture helps:

#newton-polygon

#theorem[
  Let $alpha_1,dots,alpha_n$ be the zeros of $g(x)$ in some algebraic closure
  $tilde(F)$ of the $P$-adic field $F$, and let the valuation $v$ be extended
  from $F$ to $tilde(F)$. Then the values ${v(alpha_1),dots,v(alpha_n)}$
  coincide with the slopes of the sides of the Newton polygon of $g(x)$.
  Further, if $P_i P_j$ is one of the sides, these are precisely $j-i$ $alpha$’s
  for which $v(alpha)="slope of" P_i P_j$.
] <th:newton-polygon-root-valuations>
#proof[
  It is well known that $v$ extends uniquely from $F$ to $tilde(F)$ (see, e.g.,
  @bib:Reiner1975[MO] (12.10) or Weiss @bib:Weiss1963). Arrange the zeros
  ${alpha_i}$ so that
  $
    v(alpha_1)=dots=v(alpha_m)<v(alpha_(m+1))=dots=v(alpha_l)
    <v(alpha_(l+1))<=dots<=v(alpha_n).
  $
  Taking $a_0=1$ without loss of generality, so $P_0=(0,0)$, we may write
  $ g(x)=(x-alpha_1) dots (x-alpha_m)(x-alpha_(m+1)) dots (x-alpha_n). $
  Expressing the coefficients ${a_i}$ of $g(x)$ as symmetric polynomials in the
  $alpha$’s, it follows that
  $
    v(a_1)>=v(alpha_1), quad v(a_2)>=2v(alpha_1),dots,
    v(a_m)=m v(alpha_1),
  $
  $
    v(a_(m+1))>=m v(alpha_1)+v(alpha_(m+1))>(m+1)v(alpha_1),dots,
    v(a_n)=sum_(i=1)^n v(alpha_i).
  $
  It follows at once that $P_0 P_m$ is the first piece of the Newton polygon,
  and its slope is $v(alpha_1)$. Now repeat the argument for
  $h(x)=(x-alpha_(m+1)) dots (x-alpha_n)$.
]

Having completed the preliminary work, we are now ready to state one of the
major results of this section, due to Eichler when $K$ is a number field, and to
Swan when $K$ is a function field.

#source(328)
#theorem(
  name: [Strong Approximation Theorem for the Kernel of the Reduced Norm],
  title: [Eichler–Swan],
)[
  Let $A$ be a f.d. separable $K$-algebra satisfying the Eichler condition
  relative to $R$, and let $C$ denote the center of $A$. Write $op("nr")$ for
  the reduced norm map $op("nr")_(A slash C):A^dot arrow.r C^dot$, and also for
  the map on ideles $J(A) arrow.r J(C)$. Set
  $
    u_0 lr((A))={x in A^dot:op("nr") x=1},
    quad J_0 lr((A))={alpha in J(A):op("nr") alpha=1}.
  $
  Then $u_0 lr((A))$ is dense in $J_0 lr((A))$, where we view $u_0 lr((A))$ as a
  group of principal ideles.
] <th:eichler-swan-strong-approximation>
#idx("Eichler-Swan Theorem", target: [@th:eichler-swan-strong-approximation])
#idx(
  "Strong Approximation Theorem (for kernel of the reduced norm)",
  target: [@th:eichler-swan-strong-approximation],
)

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [There is a more general formulation which involves archimedean primes as
      well (see Kneser @bib:Kneser1965), but the formulation given above is
      adequate for our later applications.],
    [It clearly suffices to establish the result when $A$ is a central simple
      $K$-algebra.],
  )
]

#idx("Local capacity")
#idx("Local index")

Until further notice, we now assume that $A$ is a central simple $K$-algebra,
with $K$ a global field as always in this section. For each prime $P$ of $K$, we
know that $A_P$ is a central simple $K_P$-algebra, and we may write
$
  A_P tilde.equiv M_(kappa_P) lr((D_P)),
  quad "where" dim_(K_P) D_P=m_P^2,
$
and $D_P$ is a skewfield with center $K_P$ and index $m_P$. We call $kappa_P$
the _local capacity_ of $A$ at $P$, and $m_P$ the _local index_. By
@bib:Reiner1975[MO] (25.7), we have $m_P=1$ a.e. Let us write
$ dim_K A=n^2, quad "so" n=m_P kappa_P quad "for each" P. $
We wish to find elements of $A$ with given reduced norm, and this will be
accomplished by means of the following:

#lemma[
  Let $A$ be a central simple $K$-algebra of dimension $n^2$, and let
  $ f(x)=x^n+a_1 x^(n-1)+dots+a_n in K[x] $
  be a separable irreducible polynomial. Suppose that for each prime $P$ of the
  global field $K$, the degree of each irreducible factor of $f(x)$ in
  $K_(P)[x]$ is a multiple of the local index $m_P$. Then there exists an
  element $a in A$ such that
  $ op("red. char. pol.")_(A slash K) a=f(x). $
  For this element $a in A$, we have
  $ f(a)=0 quad "and" op("nr")_(A slash K) a=(-1)^n a_n. $
] <lem:prescribed-reduced-characteristic-polynomial>
#proof[
  Let $L$ be the field $K(alpha)$, where $f(alpha)=0$. For each prime $P$ of
  $K$, let $P_1,dots,P_r$ be the inequivalent valuations of $L$ extending $P$.
  Then (see @bib:Reiner1975[MO]
  #source(329)
  §5C) we have
  $ f(x)=product_(i=1)^r g_i lr((x)) quad "in" K_(P)[x], $
  a product of $r$ distinct irreducible factors in $K_(P)[x]$. Furthermore,
  $
    L_(P_i)=K_P lr((alpha_i)), quad "where" g_i lr((alpha_i))=0,
    quad "for" 1<=i<=r.
  $
  From the hypothesis of the lemma it follows that $m_P$ divides
  $dim_(K_P) L_(P_i)$ for each $P$ and each $i$. Therefore $L$ is a splitting
  field for $A$ over $K$ locally at each prime of $L$, by @bib:Reiner1975[MO]
  (31.10). Hence by the Hasse–Brauer–Noether–Albert Theorem, $L$ is a global
  splitting field:
  $ L times.o_K A tilde.equiv M_n lr((L)). $
  (See @bib:Reiner1975[MO] (32.11) and (32.15).) But $dim_K L=n$, and so $L$ is
  embeddable in $A$ as a maximal subfield (see @bib:Reiner1975[MO] (28.10)).
  Viewing $alpha$ as an element of $A$, we see at once that
  $ op("min. pol.")_K alpha=f(x)=op("red. char. pol.")_(A slash K) alpha, $
  by @i:eq:simple-algebra-characteristic-reduced-power. The rest of the lemma is
  now clear.
]

In applying the above lemma, it will be necessary to start with a polynomial
with constant term $(-1)^n$. As a preliminary step in choosing a suitable such
polynomial, we prove:

#lemma[
  Let $P_0$ be a non-$R$ prime of $K$, either finite or infinite, and let
  ${P_1,dots,P_k}$ be any set of finite primes of $K$ distinct from $P_0$. Given
  a polynomial
  $ f(x)=x^n+a_1 x^(n-1)+dots+a_(n-1) x+(-1)^n in K_(P_0)[x], $
  and given a positive integer $m<n$ dividing $n$, subject to the restrictions
  that $m=1$ if $K_(P_0)=CC$, and $m=1$ or 2 if $K_(P_0)=RR$, then there exists
  an element $d in R$ such that
  #enum(
    numbering: "(i)",
    [The degree of each irreducible factor of
      $ f(x)+d x^m $
      in $K_(P_0)[x]$ is a multiple of $m$, and],
    [$v_(P_i) lr((d))$ is arbitrarily large for $1<=i<=k$.],
  )
] <lem:polynomial-perturbation-local-degrees>
#proof[
  Suppose first that $P_0$ is archimedean. If $m=1$, choose $d=0$. If $m=2$,
  then necessarily $K_(P_0)=RR$; in this case, choose $d$ to be a large positive
  integer satisfying (ii), and such that $f(x)+d x^m$ has no real zeros. Clearly
  (i) holds for this choice of $d$, and the result is now established for
  archimedean primes.

  #source(330)
  For the rest of the proof, assume $P_0$ non-archimedean, and let $v$ be its
  exponential valuation, normalized so that its value group is $ZZ$. By
  hypothesis, $P_0$ is a non-$R$ prime of $K$. If there is a non-$R$ prime
  $P' in.not {P_0,dots,P_k}$, we can use the V.S.A.T.
  @th:very-strong-approximation to choose an element $b in R$ for which
  $ v(b)<0, quad "and" v_(P_i) lr((b))>0 quad "for" 1<=i<=k. $
  <eq:nonintegral-approximating-element>
  On the other hand, suppose each $P in.not {P_0,dots,P_k}$ is an $R$-prime of
  $K$. Again using @th:very-strong-approximation, we can find $b in R$ such that
  $v_(P_i) lr((b))>0$ for $1<=i<=k$. But then $v(b)<0$ by the Product Formula
  @th:global-field-product-formula, so again we have an element $b in R$
  satisfying @eq:nonintegral-approximating-element.

  Now choose $r slash s in K$ with $r,s in R$, such that $v(r slash s)=1$. Put
  $c=r s^(m-1) in R$, so now $v(c)=1+m v(s)$, which is relatively prime to $m$.
  Finally, we choose $d=c b^(q m)$, with $q$ a large positive integer to be
  specified later. Then
  $ v(d)=v(c)+q m v(b) equiv 1 (mod m). $
  For $1<=i<=k$, we can make $v_(P_i) lr((d))$ as large as desired by choosing
  $q$ sufficiently large. Further, since $v(b)<0$, we can choose $q$ so large
  that the Newton polygon of $f(x)+d x^m$ over $K_(P_0)$ takes the form shown:

  #two-slope-newton-polygon

  The sides have slopes
  $ v(d) slash (n-m) quad "and" -v(d) slash m. $
  When these fractions are reduced to lowest terms, the new denominators will be
  divisible by $m$. (In fact, the second fraction is already in lowest terms.)

  It remains for us to verify (i) in this case. Let $h(x)$ be an irreducible
  factor of $f(x)+d x^m$ in $K_(P_0)[x]$ of degree $l$; we must show that
  $m divides l$. Set $L=K_(P_0)(alpha)$, where $h(alpha)=0$. Then
  $dim_(K_(P_0)) L=l$, and $v(alpha)$ is one of the two slopes listed above. If
  $e=e(L slash K_(P_0))$ is the ramification index of $v$ in the extension
  $L slash K_(P_0)$, then $v(alpha)=a slash e$ for some $a in ZZ$. It follows
  that $m divides e$. But $e divides l$ by @i:eq:ramification-residue-degree,
  since $v$ extends uniquely from $K_(P_0)$ to $L$. Together, these show that
  $m divides l$, which completes the proof of the lemma.
]

We come now to the first place in the proof of the S.A.T.
@th:eichler-swan-strong-approximation where the Eichler condition appears. Let
$A$ be a central simple $K$-algebra of dimension $n^2$, satisfying
$"Eichler" slash R$. Then there exists a non-$R$ prime $P_0$ of $K$ for which
$A_(P_0)$ is _not_ a noncommutative skewfield. This means that
$ "either" m_(P_0)=n=1, quad "or else" 1<=m_(P_0)<n, $
#source(331)
where $m_(P_0)$ is the local index of $A$ at $P_0$. Using this fact, we are
ready to prove one of the key lemmas needed for
@th:eichler-swan-strong-approximation:

#proposition[
  Let $Lambda$ be an $R$-order in a central simple $K$-algebra $A$ of dimension
  $n^2$, and assume $A="Eichler" slash R$. Then there exists a nonzero ideal
  $frak(r)$ of $R$ with the following property:

  For each
  $ f(x)=x^n+a_1 x^(n-1)+dots+(-1)^n in R[x], $
  and for each pair of nonzero ideals $frak(a),frak(b)$ of $R$ with
  $frak(b)+frak(r) frak(a)=R$, there exists an element $xi in Lambda^dot$ such
  that
  $
    op("nr")_(A slash K) xi=1, quad f(xi) equiv 0 (mod frak(b) Lambda),
    quad "and" xi equiv 1 (mod frak(a) Lambda).
  $
  <eq:norm-one-polynomial-congruences>
] <prop:norm-one-polynomial-congruence-approximation>
#proof[
  _Step 1._ We begin by specifying the ideal $frak(r)$. For each maximal
  $R$-order $Gamma$ in $A$ and each $y in A^dot$, the conjugate $y Gamma y^(-1)$
  is again a maximal order in $A$. We show that there are only a finite number
  of conjugacy classes of maximal orders in $A$. Let $Gamma'$ be any maximal
  order in $A$; then
  $ Gamma'=(Gamma' Gamma) dot Gamma dot (Gamma' Gamma)^(-1) $
  by @bib:Reiner1975[MO] (22.21). But the number of isomorphism classes of right
  $Gamma$-ideals in $A$ is finite by the Jordan–Zassenhaus Theorem; let
  ${L_i:1<=i<=g}$ be a full set of representatives of these isomorphism classes.
  Then we may write $Gamma' Gamma=z L_i$ for some $z in A^dot$ and some $i$, and
  consequently
  $ Gamma'=z L_i Gamma L_i^(-1) z^(-1). $
  Thus, there are at most $g$ conjugacy classes of maximal $R$-orders in $A$;
  let $Gamma_1,dots,Gamma_h$ represent these classes, and choose a nonzero
  element $r in R$ such that $r Gamma_i subset.eq Lambda$ for each $i$. Finally,
  choose the ideal $frak(r)$ of $R$ so that $frak(r)$ is divisible by every
  prime ideal factor of $r R$, and also by each $R$-prime $P$ for which $m_P>1$
  (remember that $m_P=1$ a.e.).

  _Step 2._ The proposition is trivially true for $n=1$ (just choose $xi=1$), so
  let $n>1$ hereafter. Since $A="Eichler" slash R$, there exists a non-$R$ prime
  $P_0$ of $K$ for which $1<=m_(P_0)<n$. Choose $P_0$ to be archimedean if
  possible (this can only happen when $K$ is a number field). Further, when
  $P_0$ is chosen archimedean, assume $m_(P_0)$ is as large as possible, subject
  always to the condition that $m_(P_0)$ is a proper divisor of $n$.

  We now define
  $
    S_2={P:P="finite non-" R "prime", P!=P_0, m_P>1}
    union {P:P=R "-prime", P divides frak(r) frak(a)}.
  $
  Without loss of generality, we may assume $S_2 != emptyset$. For each
  $P in S_2$, we choose
  #source(332)
  a separable irreducible polynomial
  $ g^P lr((x))=x^n+dots+(-1)^n in R_(P)[x], $
  such that $g^P lr((x))$ is near $(x-1)^n$ coefficientwise in the $P$-adic
  topology. It is not hard to prove that such a choice is always possible; see,
  e.g., @bib:Reiner1975[MO], bottom of page 299.

  _Step 3._ We treat first the case $n>2$. We are given a polynomial
  $f(x)=x^n+dots+(-1)^n in R[x]$, and a pair of ideals $frak(a),frak(b)$ of $R$.
  Since $P_0$ is a non-$R$ prime, it follows from the V.S.A.T.
  @th:very-strong-approximation that we can find a polynomial
  $ g(x)=x^n+dots+(-1)^n in R[x] $
  such that (coefficientwise)
  $
    cases(
      g(x) "is near" g^P lr((x)) "for each" P in S_2 "," "and",
      g(x) "is near" f(x) "at each" R "-prime dividing" frak(b).
    )
  $
  Note that since $frak(b)+frak(r) frak(a)=R$ by hypothesis, no $R$-prime
  divisor of $frak(b)$ lies in the set $S_2$.

  Since $m_(P_0)$ is a proper divisor of $n$, we can apply Lemma
  @lem:polynomial-perturbation-local-degrees with $m=m_(P_0)$ to find an element
  $d in R$ such that
  $ h(x)=g(x)+d x^m $
  satisfies the conditions:
  #enum(
    numbering: "(i)",
    [The degree of each irreducible factor of $h(x)$ in $K_(P_0)[x]$ is a
      multiple of $m$, and],
    [$h(x)$ is coefficientwise close to $g(x)$ at each $P in S_2$ and also at
      each $R$-prime dividing $frak(b)$.],
  )

  We intend to apply Lemma @lem:prescribed-reduced-characteristic-polynomial to
  the polynomial $h(x) in R[x]$ constructed above, and begin by checking that
  $h(x)$ satisfies the hypotheses of that lemma. First of all, $h(x)$ is near
  $g^P lr((x))$ at each $P in S_2$; since $g^P lr((x))$ is separable and
  irreducible over $K_P$, so is $h(x)$ (see @bib:Reiner1975[MO] (33.8)). In
  particular, $h(x)$ must be separable irreducible over $K$. It remains to
  verify

  #statement(
    [$(ast)$],
    "prop",
    [
      For every prime $P$ of $K$, the degree of each irreducible factor of
      $h(x)$ over $K_P$ is divisible by $m_P$.
    ],
    italic: true,
    numbered: false,
  ) <prop:local-factor-degree-condition>

  This surely holds whenever $m_P=1$. Next, $S_2$ contains every finite prime
  $P$ (except possibly $P_0$) for which $m_P>1$; for each such $P$, $h(x)$ is
  irreducible over $K_P$, so @prop:local-factor-degree-condition is valid.
  Further, @prop:local-factor-degree-condition holds at $P_0$ itself, by
  @lem:polynomial-perturbation-local-degrees.

  We must still check @prop:local-factor-degree-condition at the infinite primes
  of $K$, if there are any. If $m_P=1$
  #source(333)
  for each infinite prime $P$, @prop:local-factor-degree-condition is trivially
  true. If $m_P=2$ for some real prime $P$ of $K$, then by the choice of $P_0$
  we must have $m_(P_0)=2$, so $m=2$ in the above discussion. The first part of
  the proof of @lem:polynomial-perturbation-local-degrees then shows that the
  element $d$ occurring there may be chosen so that $h(x)$ has no linear factors
  in $K_(P)[x]$ for each real prime $P$. After modifying our originally chosen
  $d$ in this way, condition @prop:local-factor-degree-condition now holds for
  every prime of $K$.

  We may thus apply Lemma @lem:prescribed-reduced-characteristic-polynomial to
  $h(x)$, and conclude that $A$ contains an element $xi$ for which
  $ h(xi)=0 quad "and" op("nr") xi=1, $
  where $op("nr")$ means $op("nr")_(A slash K)$. It remains for us to check that
  the congruences in @eq:norm-one-polynomial-congruences hold true. Since
  $frak(a)+frak(b)=R$, we have $a+b=1$ for some $a in frak(a)$, $b in frak(b)$,
  and therefore $R a+frak(b)=R$. It therefore suffices to prove the proposition
  for the case where $frak(a)=R a$ is principal.

  Each $R$-prime $P$ dividing $r a$ also divides $frak(r) frak(a)$, and so
  $P in S_2$ (here, $r$ is as in Step 1). At each such $P$, $h(x)$ is near
  $g(x)$, and $g(x)$ is near $(x-1)^n$, so we may write
  $
    h(x)=(x-1)^n+(r a)^n overline(h)(x)
    quad "for some" overline(h)(x) in R[x], quad deg overline(h)(x)<n.
  $
  Now set $xi=1+r a xi'$ with $xi' in A$. Since $h(xi)=0$, we have
  $ (xi')^n+overline(h)(1+r a xi')=0. $
  This shows that $xi'$ is integral over $R$, so by
  @i:cor:finite-subring-contained-in-maximal-order it follows that $xi'$ lies in
  some maximal $R$-order in $A$. Replacing $xi$ and $xi'$ by $y xi y^(-1)$ and
  $y xi' y^(-1)$, respectively, with $y in A^dot$, we may now assume that
  $xi' in Gamma_i$ for one of the maximal orders $Gamma_i$ defined in Step 1.
  Then $r xi' in Lambda$ from the choice of $r$, and consequently
  $xi equiv 1 (mod frak(a) Lambda)$. Further, this congruence implies that
  $xi in Lambda$, and then necessarily $xi in Lambda^dot$ because
  $op("nr") xi=1$.

  Finally, $h(x)$ is near $f(x)$ at each $R$-prime dividing $frak(b)$. Since
  $h(xi)=0$, it follows that $f(xi) equiv 0 (mod frak(b) Lambda)$. This shows
  that @eq:norm-one-polynomial-congruences holds, and completes the proof for
  the case $n>2$.

  _Step 4._ We finally consider the case where $n=2$, so now $P_0$ is a non-$R$
  prime for which $m_(P_0)=1$. In addition to the set $S_2$ of finite primes
  defined in Step 2, we also introduce the set
  $ S_1={P:P="real prime", P!=P_0, m_P=2}, $
  which may possibly be empty. As in Step 2, for each $P in S_2$ we again choose
  a separable irreducible polynomial
  $ g^P lr((x))=x^2+a^((P)) x+1 in R_(P)[x], $
  with $a^((P))$ close to $-2$ in the $P$-adic topology. Furthermore, for each
  $P in S_1$ (if
  #source(334)
  any), choose $g^P lr((x))$ as above, where now $a^((P))=2-epsilon$ for some
  small positive number $epsilon$. Since $P_0 in.not S_1 union S_2$ and $P_0$ is
  a non-$R$ prime, we can use the V.S.A.T. @th:very-strong-approximation to find
  a polynomial
  $ g(x)=x^2+c x+1 in R[x], $
  such that
  $
    cases(
      g(x) "is near" g^P lr((x)) "for each" P in S_1 union S_2 "," "and",
      g(x) "is near" f(x) "for each" R "-prime dividing" frak(b).
    )
  $
  It is easily checked that $g(x)$ is irreducible (and separable) over $K_P$ for
  each prime $P$ of $K$ for which $m_P=2$. We can therefore apply Lemma
  @lem:prescribed-reduced-characteristic-polynomial to the polynomial $g(x)$
  directly, obtaining an element $xi in A$ for which $g(xi)=0$ and
  $op("nr") xi=1$. The rest of the argument is identical with that given in the
  latter half of Step 3. This completes the proof of the proposition.
]

Continuing with our proof of @th:eichler-swan-strong-approximation, let $A$ be a
central simple $K$-algebra. For each prime $P$ of $K$, let
$
  u_0 lr((A_P))={x in A_P:op("nr")_(A_P slash K_P) x=1},
  quad "and" u_0 lr((A))={x in A:op("nr")_(A slash K) x=1}.
$
<eq:local-global-norm-one-groups>
We wish to prove that $u_0 lr((A))$ is dense in $J_0 lr((A))$ (see
@eq:reduced-norm-one-ideles) whenever $A="Eichler" slash R$. As a preliminary
step, independent of the Eichler condition, we prove:

#lemma[
  For any finite set $S$ of primes of $K$, $u_0 lr((A))$ is dense in
  $product_(P in S) u_0 lr((A_P))$.
] <lem:norm-one-weak-approximation>
#proof[
  Let $x=(x_P:P in S)$, with $x_P in u_0 lr((A_P))$ for each $P in S$, so
  $op("nr") x_P=1$. By @i:th:nakayama-matsushima and the remarks following it,
  we know that $x_P in [A_P^dot,A_P^dot]$. We may therefore write
  $
    x_P=product_(i=1)^m [b_(i P),c_(i P)],
    quad "with" b_(i P),c_(i P) in A_P^dot, quad forall P in S,
  $
  where we may assume $m$ independent of $P$. For each $i$, choose elements
  $b_i,c_i in A$ close to $b_(i P),c_(i P)$ (respectively) at all $P in S$. This
  can be done by virtue of the Weak Approximation Theorem in algebraic number
  theory (or else apply the V.S.A.T. @th:very-strong-approximation). Since $b_i$
  is close to $b_(i P)$, and $b_(i P) in A_P^dot$, it follows that
  $b_i in A^dot$ for each $i$; likewise, each $c_i in A^dot$. Now set
  $ y=product_(i=1)^m [b_i,c_i] in u_0 lr((A)), $
  and clearly $y$ is close to $x$. This completes the proof.
]

We are now ready to prove the S.A.T. @th:eichler-swan-strong-approximation for
the kernel $J_0 lr((A))$ of the reduced norm map on ideles. As we shall see,
most of the difficulties have already
#source(335)
been overcome in our preliminary lemmas. For the proof, it suffices to restrict
attention to the case where $A$ is a central simple $K$-algebra of dimension
$n^2$. We may assume that $n>1$, since $J_0 lr((A))=1$ when $n=1$. Let $Lambda$
be an $R$-order in $A$.

#proof(head: none)[
  _Step 1._ According to Lemma @lem:norm-one-idele-adele-topologies, as a basis
  for the neighborhoods of an element $x in J_0 lr((A))$, we may choose all open
  sets
  $
    x(J_0 lr((A)) inter W),
    quad "where" W=product_(P in S) N_P lr((1))
    times product_(P in.not S) Lambda_P^dot
  $
  (see @eq:idele-neighborhood-basis). Equivalently, we may choose all open sets
  $
    (x+U) inter J_0 lr((A)),
    quad "where" U=product_(P in S) N_P lr((0))
    times product_(P in.not S) Lambda_P
  $
  (see @eq:adele-neighborhood-basis). Here, $P$ ranges over maximal ideals of
  $R$, and $S$ over all finite sets of such $R$-primes $P$. We shall continue
  using the notation given in @eq:reduced-norm-one-ideles and
  @eq:local-global-norm-one-groups.

  We wish to prove that $u_0 lr((A))$ is dense in $J_0 lr((A))$ when
  $A="Eichler" slash R$. This means that for each finite set $S$ of $R$-primes
  of $K$, and each choice of elements $x_P in u_0 lr((A_P))$, $P in S$, there
  exists an element $a in u_0 lr((A))$ such that
  $
    a "is near" x_P "for each" P in S,
    quad "and" a in Lambda_Q "for each" R "-prime" Q in.not S.
  $

  _Step 2._ Assume hereafter that $A$ satisfies the Eichler condition relative
  to $R$, and that $A$ is a central simple $K$-algebra of dimension $n^2$, where
  $n>1$. Let $H$ denote the closure of $u_0 lr((A))$ in $J_0 lr((A))$. For each
  $R$-prime $P$, we may view $u_0 lr((A_P))$ as a subgroup of $J_0 lr((A))$, by
  identifying $u_0 lr((A_P))$ with
  $ 1 times dots times 1 times u_0 lr((A_P)) times 1 times dots. $
  Let $frak(r)$ be the nonzero ideal of $R$ defined in Proposition
  @prop:norm-one-polynomial-congruence-approximation, and set
  $ tilde(S)={P:P=R "-prime of" K, P divides.not frak(r), m_P=1}. $
  <eq:unramified-good-primes-approximation>
  Then almost every $R$-prime belongs to $tilde(S)$, since $m_P=1$ a.e. The aim
  of this step is to prove that $u_0 lr((A_P))<=H$ for each $P in tilde(S)$,
  where $H$ is the closure of $u_0 lr((A))$ in $J_0 lr((A))$. For this purpose,
  introduce the group
  $ H^ast={alpha=(a_P) in H:a_P=1 "a.e."}<=H. $
  We claim that $H^ast ◁ J_0 lr((A))$. Given $alpha=(a_P) in H^ast$ and
  $beta=(b_P) in J_0 lr((A))$, we must show that
  $beta alpha beta^(-1) in H^ast$. The $P$-component of $beta alpha beta^(-1)$,
  denoted by $(beta alpha beta^(-1))_P$, equals 1 for almost all $P$, and thus
  we are reduced to proving that $beta alpha beta^(-1) in H$. Let $S$ be the
  finite set of $R$-primes $P$ for which $a_P!=1$. By
  @lem:norm-one-weak-approximation we may choose a sequence ${c_1,c_2,dots}$ of
  elements of $u_0 lr((A))$ such that $lim_(i arrow.r infinity) c_i=b_P$ in
  $A_P$ at each
  #source(336)
  $P in S$. Then
  $
    (c_i alpha c_i^(-1))_P=(beta alpha beta^(-1))_P=1
    quad "for" P in.not S,
  $
  $
    (c_i alpha c_i^(-1))_P "is near" (beta alpha beta^(-1))_P
    quad "for" P in S.
  $
  Consequently we have
  $
    lim_(i arrow.r infinity) c_i alpha c_i^(-1)
    = beta alpha beta^(-1) quad "in" J_0 lr((A)).
  $
  But $c_i alpha c_i^(-1) in H^ast<=H$ for each $i$, and $H$ is closed in
  $J_0 lr((A))$, so it follows that $beta alpha beta^(-1) in H$, as desired. We
  have thus proved that $H^ast ◁ J_0 lr((A))$.

  Now fix a prime $P in tilde(S)$, and let us show that $u_0 lr((A_P))<=H^ast$.
  Since $m_P=1$, we have $A_P tilde.equiv M_n lr((K_P))$, and
  $op("nr")_(A_P slash K_P)$ is just the usual determinant map. Therefore
  $u_0 lr((A_P))=SL_n lr((K_P))$, and
  $ H^ast inter u_0 lr((A_P)) ◁ SL_n lr((K_P)). $
  However, any _proper_ normal subgroup of $SL_n lr((K_P))$ must consist only of
  scalar matrices (see, e.g., Artin @bib:Artin1957). We shall show that this
  cannot occur when $P in tilde(S)$, so we may then conclude that
  $u_0 lr((A_P))<=H^ast<=H$, as desired.

  Keeping $P in tilde(S)$ fixed, choose a polynomial
  $ f(x)=x^n+dots+(-1)^n in R[x] $
  such that $f(x)$ has no linear factors in $R_(P)[x]$. This is always possible
  since $R slash P$ is finite (and $n>1$); see @bib:Reiner1975[MO], Exercise
  34.1. We shall find an element
  $xi in H inter SL_n lr((K_P))=H^ast inter SL_n lr((K_P))$ such that $f(xi)=0$.
  Then $xi$ cannot be a scalar matrix since $f(x)$ has no linear factors over
  $K_P$. This implies that $H^ast inter SL_n lr((K_P))$ cannot consist entirely
  of scalar matrices, so the intersection coincides with $SL_n lr((K_P))$, and
  thus $u_0 lr((A_P))=SL_n lr((K_P))<=H^ast$.

  In order to find this element $xi$, we make use of Proposition
  @prop:norm-one-polynomial-congruence-approximation, whose proof required the
  Eichler condition. Let ${P_1,P_2,dots}$ be the set of all $R$-primes of $K$
  different from $P$. For each $m>=1$, let
  $ frak(a)_m=(P_1 P_2 dots P_m)^m. $
  (If there are only finitely many ${P_i}$, let $frak(a)_m$ be the $m$-th power
  of their product.) For each $m>=1$ we have $P^m+frak(a)_m=R$, so by
  @prop:norm-one-polynomial-congruence-approximation there exists an element
  $xi_m in u_0 lr((A)) inter Lambda$ such that
  $
    f(xi_m) equiv 0 (mod P^m Lambda),
    quad "and" xi_m equiv 1 (mod frak(a)_m Lambda).
  $
  Of course each $xi_m in Lambda^dot$, by the proof of
  @lem:norm-one-idele-adele-topologies. Therefore
  $lim_(m arrow.r infinity) xi_m=1$ in $Lambda_Q$ for each $R$-prime $Q!=P$. On
  the other hand, we may view each $xi_m$ as an element of the compact group
  $Lambda_P^dot$, and we can then find a subsequence ${xi_(m')}$ such that
  #source(337)
  $lim xi_(m')$ exists in $Lambda_P^dot$. Now let $xi=lim xi_(m') in H$; then
  $xi_Q=1$ for $Q!=P$, while $xi_P in u_0 lr((A_P))$. Since $f(xi_P)=0$ in
  $A_P$, we now have an element $xi=xi_P in H inter SL_n lr((K_P))$ for which
  $f(xi)=0$, as desired. This completes the proof that $u_0 lr((A_P))<=H$ for
  all $P in tilde(S)$.

  _Step 3._ We have defined $H$ as the closure of $u_0 lr((A))$ in
  $J_0 lr((A))$, and are trying to prove that $H=J_0 lr((A))$. We shall use the
  fact that the set $tilde(S)$, defined above, contains all but a finite number
  of $R$-primes of $K$. Consider first an element $alpha in J_0 lr((A))$ of the
  form
  $
    alpha=1 times dots times 1 times product_(P in tilde(S)) a_P,
    quad "with" a_P in u_0 lr((A_P)) "for" P in tilde(S).
  $
  For each finite subset $T$ of $tilde(S)$, by Step 2 we can find an element
  $h(T) in H$ with
  $
    h(T)_Q=cases(
      a_Q & quad Q in T,
      1 & quad Q=R "-prime" "," quad Q in.not T.
    )
  $
  Since $alpha=lim_T h(T)$ and $H$ is closed, we conclude that $alpha in H$, as
  desired.

  Now let $beta=(b_P) in J_0 lr((A))$ be arbitrary. By
  @lem:norm-one-weak-approximation, there exists a sequence ${c_1,c_2,dots}$ of
  elements of $u_0 lr((A))<=H$, with $c_i$ approaching $b_P$ at each of the
  finitely many $R$-primes $P in.not tilde(S)$. Let $delta_i=(d_P)$, where
  $ d_Q=cases(1 & quad Q in.not tilde(S), c_i^(-1) b_Q & quad Q in tilde(S).) $
  Then $beta=lim_(i arrow.r infinity) c_i delta_i$. But $delta_i in H$ by the
  preceding discussion, and also each $c_i in H$, so also $beta in H$. This
  proves that $J_0 lr((A))=H$, and establishes Theorem
  @th:eichler-swan-strong-approximation.
]

We conclude this subsection with the first important application of the
Eichler–Swan Theorem. We shall use it to prove Theorem
@th:eichler-maximal-order-unit-norm, which plays a vital role in the calculation
of $K_1$ of a maximal order, and which we restate for convenience:

#theorem[
  Let $Lambda$ be a maximal $R$-order in a central simple $K$-algebra $A$, where
  $K$ is a global field. Assume that $A="Eichler" slash R$. Then
  $ op("nr")_(A slash K) Lambda^dot=R^dot inter K^+, $
  where (as in @eq:reduced-norm-positive-subgroup)
  $
    K^+={a in K^dot:a_P>0 "at each real prime" P "of" K
      "ramified in" A}.
  $
] <th:eichler-maximal-order-unit-norm-global>
#proof[
  For each maximal ideal $P$ of $R$, $A_P$ is a central simple $K_P$-algebra. We
  shall use the notation $op("nr")$ to indicate either $op("nr")_(A slash K)$ or
  $op("nr")_(A_P slash K_P)$, depending on the context. The inclusion
  $op("nr") Lambda^dot subset.eq R^dot inter K^+$ is obvious from
  @i:cor:order-reduced-characteristic-integral and
  @i:th:hasse-schilling-maass-norm, and holds whether or not
  $A="Eichler" slash R$.
  #source(338)
  Now assume that $A="Eichler" slash R$, and let $a in R^dot inter K^+$; we must
  prove that $a in op("nr") Lambda^dot$. By @i:th:hasse-schilling-maass-norm we
  have $a=op("nr") x$ for some $x in A^dot$. On the other hand, for each $P$ we
  may view $a$ as an element of $R_P^dot$, and then by
  @prop:local-maximal-order-unit-norm, $a=op("nr") y_P$ for some
  $y_P in Lambda_P^dot$. Therefore the idele $beta=(y_P)x^(-1)$ lies in
  $J_0 lr((A))$, that is, $op("nr") beta=1$.

  Let $S$ be some finite set of primes of $R$, chosen so that
  $ y_P x^(-1) in Lambda_P^dot quad "for all" P in.not S. $
  By @th:eichler-swan-strong-approximation we may choose $z in u_0 lr((A))$ such
  that
  $
    z "is near" y_P x^(-1) "for" P in S,
    quad "and" z in Lambda_P^dot "for" P in.not S.
  $
  Then
  $ op("nr") z x=(op("nr") z)(op("nr") x)=a, $
  and we need only show that $z x in Lambda^dot$, or equivalently, that
  $z x in Lambda_P^dot$ for each $R$-prime $P$. For $P in.not S$, both $z$ and
  $x$ are in $Lambda_P^dot$, whence so is $z x$. On the other hand, for $P in S$
  we know that $z x$ is near $y_P$ in $A_P^dot$; but $y_P in Lambda_P^dot$, and
  $Lambda_P^dot$ is an open subgroup of $A_P^dot$, so it follows that
  $z x in Lambda_P^dot$, as desired. This completes the proof of the theorem.
]

#corollary[
  Let $Lambda$ be a maximal $R$-order in a central simple $K$-algebra $A$, where
  $K$ is a global field. Then for $n>=2$,
  $ op("nr") GL_n lr((Lambda))=R^dot inter K^+, $
  whether $A="Eichler" slash R$ or not.
] <cor:maximal-order-matrix-unit-norm>
#proof[
  For $n>1$, $M_n lr((A))="Eichler" slash R$. The result now follows from
  @th:eichler-maximal-order-unit-norm-global. (Compare the proof of
  @th:maximal-order-whitehead-norm-image.)
]

Swan @bib:Swan1980, pages 188–189, gives an example in which $A$ is a totally
definite quaternion algebra over its center $K=QQ(sqrt(3))$, so
$A != "Eichler" slash R$, where $R="alg. int." {K}$. He shows that Theorem
@th:eichler-maximal-order-unit-norm-global is not valid in this case, so the
Eichler condition cannot be omitted, generally speaking. This example also gives
an instance of a maximal order $Lambda$ for which
$ op("nr") Lambda^dot < op("nr") GL_2 lr((Lambda))=op("nr") K_1 lr((Lambda)). $

=== Locally Free Cancellation <ss:jacobinski-cancellation>

Keeping the notation of the earlier subsections, let $Lambda$ be an $R$-order in
a f.d. separable $K$-algebra $A$, where $R$ is a Dedekind domain whose quotient
field $K$ is a global field, $K!=R$. We shall apply the Eichler–Swan Theorem
@th:eichler-swan-strong-approximation to prove the important result:

#source(339)
#theorem(name: [Jacobinski Cancellation Theorem])[
  If $A$ satisfies the Eichler condition relative to $R$, then every $R$-order
  $Lambda$ in $A$ has locally free cancellation.
] <th:jacobinski-cancellation>
#idx("Jacobinski's Cancellation Theorem", target: [@th:jacobinski-cancellation])

The theorem was first proved by Jacobinski @bib:Jacobinski1968b for the case
where $K$ is a number field. We shall follow Fröhlich’s @bib:Frohlich1975
approach to the proof, for $K$ any global field, and begin with some easy
remarks which are independent of the Eichler condition.

#lemma[
  The $R$-order $Lambda$ has locally free cancellation if and only if
  $
    J_0 lr((A)) subset.eq alpha^(-1) U(Lambda) alpha dot A^dot
    quad "for all" alpha in J(A),
  $
  where
  $
    U(Lambda)=product_P Lambda_P^dot="group of unit ideles",
    quad A^dot="principal ideles".
  $
] <lem:cancellation-idele-containment>
#proof[
  By @th:class-group-idele-quotient, there is an isomorphism
  $ op("Cl") Lambda tilde.equiv J(A) slash J_0 lr((A)) A^dot U(Lambda), $
  and the elements of the locally free class group $op("Cl") Lambda$ are stable
  isomorphism classes $[Lambda alpha]$, $alpha in J(A)$. For
  $alpha,beta in J(A)$, we saw in @eq:idele-lattice-isomorphism-double-cosets
  that
  $ Lambda alpha tilde.equiv Lambda beta <=> beta in U(Lambda) alpha A^dot. $
  From the discussion at the beginning of §@sec:cancellation-theorems, we show
  that $Lambda$ has locally free cancellation if and only if for
  $alpha,beta in J(A)$, $[Lambda alpha]=[Lambda beta]$ implies
  $Lambda alpha tilde.equiv Lambda beta$. Thus, $Lambda$ has locally free
  cancellation if and only if for every $alpha in J(A)$,
  $
    beta in J_0 lr((A)) A^dot U(Lambda) alpha
    => beta in U(Lambda) alpha A^dot,
  $
  or equivalently,
  $ J_0 lr((A)) A^dot U(Lambda) alpha subset.eq U(Lambda) alpha A^dot. $
  Since $J_0 lr((A))$ contains the commutator subgroup of $J(A)$, the factors on
  the left-hand side can be arranged in any order, so the above condition can be
  rewritten as
  $ U(Lambda) alpha J_0 lr((A)) A^dot subset.eq U(Lambda) alpha A^dot, $
  or equivalently,
  $
    alpha J_0 lr((A)) subset.eq U(Lambda) alpha A^dot,
    quad "that is," J_0 lr((A)) subset.eq alpha^(-1) U(Lambda) alpha A^dot.
  $
  This completes the proof of the lemma.
]

#source(340)
#corollary(title: [Fröhlich @bib:Frohlich1975])[
  Whether or not $A="Eichler" slash R$, we have:
  #enum(
    numbering: "(i)",
    [Let $Lambda subset Gamma$ be $R$-orders in $A$. If $Lambda$ has locally
      free cancellation, then so does $Gamma$.],
    [Let $Lambda,Gamma$ be $R$-orders in f.d. separable $K$-algebras $A,B$,
      respectively. Let $phi:A arrow.r B$ be a surjection of $K$-algebras such
      that $phi(Lambda) subset.eq Gamma$. If $Lambda$ has locally free
      cancellation, then so does $Gamma$.],
  )
] <cor:cancellation-overorders-quotients>

We are now ready to prove the Jacobinski Cancellation Theorem. Assume now that
$A="Eichler" slash R$; then $u_0 lr((A))$ is dense in $J_0 lr((A))$, by the
Eichler–Swan Theorem @th:eichler-swan-strong-approximation. For each
$alpha in J(A)$, $alpha^(-1) U(Lambda) alpha$ is an open subgroup of $J(A)$, by
the discussion in §@ss:eichler-swan-theorem. It follows that
$
  J_0 lr((A)) subset.eq alpha^(-1) U(Lambda) alpha dot u_0 lr((A))
  subset.eq alpha^(-1) U(Lambda) alpha dot A^dot
$
for each $alpha in J(A)$. Thus $Lambda$ has locally free cancellation by Lemma
@lem:cancellation-idele-containment, and the proof is finished.

It is worthwhile to give some consequences of the Cancellation Theorem, and we
begin with a definition:

#definition[
  Let $M$ be a left $Lambda$-lattice, where $Lambda$ is an $R$-order in a f.d.
  separable $K$-algebra $A$. Put
  $ Gamma=End_Lambda M, quad "and" B=End_A K M, $
  so $Gamma$ is an $R$-order in the f.d. separable $K$-algebra $B$. Call $M$ an
  _Eichler lattice_ if $B="Eichler" slash R$.
] <def:eichler-lattice>
#idx("Eichler lattice", target: [@def:eichler-lattice])

Generalizing @th:jacobinski-cancellation, we prove:

#theorem(title: [Jacobinski])[
  Let $M$ be an Eichler lattice over the $R$-order $Lambda$, and let $X$ be a
  left $Lambda$-lattice such that $X divides M^((k))$ for some $k$. Then for any
  $Lambda$-lattice $L$,
  $ L plus.o X tilde.equiv M plus.o X <=> L tilde.equiv M. $
] <th:eichler-lattice-summand-cancellation>
#idx(
  "Jacobinski's Cancellation Theorem",
  target: [@th:eichler-lattice-summand-cancellation],
)
#proof[
  If $L plus.o X tilde.equiv M plus.o X$, then
  $L_P plus.o X_P tilde.equiv M_P plus.o X_P$ for each maximal ideal $P$ of $R$.
  Therefore $L_P tilde.equiv M_P$ by @i:cor:krull-schmidt-cancellation, which
  proves that $L$ is necessarily in the genus of $M$. Increasing $X$ if need be,
  we have
  $ L plus.o M^((k)) tilde.equiv M plus.o M^((k)) $
  <eq:eichler-lattice-stable-multiple>
  for some $k$. Furthermore, $L divides M^((2))$ by @i:cor:genus-addition. Now
  use the Morita correspondence @i:prop:morita-summand-equivalence between
  summands of ${M^((n)):n>=1}$ and projective left $Gamma$-modules, where
  $Gamma$ is as in @def:eichler-lattice. Let $L$ correspond to the locally free
  left ideal $W$ of $Gamma$. The
  #source(341)
  $Lambda$-isomorphism @eq:eichler-lattice-stable-multiple then yields an
  isomorphism of $Gamma$-lattices
  $ W plus.o Gamma^((k)) tilde.equiv Gamma plus.o Gamma^((k)). $
  Since $B=K Gamma$ is Eichler/$R$ by hypothesis, we may apply
  @th:jacobinski-cancellation to conclude that $W tilde.equiv Gamma$. Therefore
  $L tilde.equiv M$, as desired.
]

#corollary[
  Let $N$ be a locally free left ideal of $Lambda$, where $Lambda$ is an
  $R$-order in the f.d. separable $K$-algebra $A$. Then
  $
    N plus.o Lambda^((k)) tilde.equiv Lambda plus.o Lambda^((k))
    quad "for some" k>=1
    => N plus.o Lambda tilde.equiv Lambda^((2)),
  $
  whether or not $A$ is Eichler/$R$.
] <cor:stable-ideal-single-free-summand>
#proof[
  We have
  $
    End_A K(N plus.o Lambda) tilde.equiv End_A A^((2))
    tilde.equiv M_2 lr((A^compose)),
  $
  and $M_2 lr((A^compose))$ is Eichler/$R$ by
  @prop:eichler-condition-sufficient-cases. Thus $N plus.o Lambda$ is an Eichler
  $Lambda$-lattice. The hypotheses imply that
  $
    (N plus.o Lambda) plus.o Lambda^((k-1))
    tilde.equiv Lambda^((2)) plus.o Lambda^((k-1)).
  $
  and we may apply @th:eichler-lattice-summand-cancellation since
  $Lambda^((k-1)) divides (N plus.o Lambda)^((k-1))$. This gives
  $N plus.o Lambda tilde.equiv Lambda^((2))$, as desired.
]

#remarks[
  #enum(
    numbering: "(i)",
    [The result is a special case of the Bass Cancellation Theorem
      @th:bass-cancellation.],
    [Let $L$ and $M$ be $Lambda$-lattices in the same genus. It may well happen,
      even when $A$ is Eichler/$R$, that $L plus.o X tilde.equiv M plus.o X$ for
      some $Lambda$-lattice $X$, but $L cancel(tilde.equiv) M$. For example, if
      $M=Lambda$ then from $L plus.o X tilde.equiv Lambda plus.o X$ for some $X$
      we can only conclude that $[L]$ lies in the kernel group $D(Lambda)$
      defined in §@ss:class-group-functorial-kernel. Even when $A$ is a
      commutative algebra, this kernel group need not be trivial.],
  )
] <rem:eichler-lattice-cancellation-limits>

We return next to the question, considered in
@i:th:uniform-genus-class-number-bound, of finding a uniform upper bound on the
number $|g(M)|$ of isomorphism classes in the genus $g(M)$ of a $Lambda$-lattice
$M$. (Caution: this notation differs from that of §@i:sec:genus.) The approach
here, due to Jacobinski @bib:Jacobinski1968b, gives an easily computed bound.

#theorem[
  Let $Lambda$ be an $R$-order in $A$. There exists a positive constant
  $n_0=n_0 lr((Lambda))$ such that
  $ |g(M)| <= n_0 $
  for every Eichler lattice $M$.
] <th:eichler-lattice-uniform-genus-bound>
#idx("Jacobinski's Theorem", target: [@th:eichler-lattice-uniform-genus-bound])
#proof[
  We may assume that $M$ is a faithful $Lambda$-lattice, as in the proof of
  @i:th:roiter-local-direct-summand. Setting $Gamma=End_Lambda M$,
  $B=End_A K M$, it follows that $A$ and $B$ have the same center
  #source(342)
  $C$. Let $frak(O)$ be the integral closure of $R$ in $C$. Choose a maximal
  order $Lambda'$ in $A$, and a nonzero $r in R$ with
  $ r Lambda' subset Lambda subset Lambda'. $
  Then $Gamma'=End_(Lambda') (Lambda'M)$ is a maximal order in $B$ containing
  $Gamma$ (see @bib:Reiner1975[MO] Exercise 21.1), where $Lambda'M$ is computed
  inside $K M$. It is easily checked that $r Gamma' subset Gamma$.

  Now $Gamma$ is Eichler/$R$ by hypothesis, so
  @th:eichler-lattice-summand-cancellation yields
  $
    |g(M)|=|g(Gamma)|=|op("Cl") Gamma|
    =|op("Cl") Gamma'| dot |D(Gamma)|.
  $
  The factor $|op("Cl") Gamma'|$ is independent of the choice of $M$, by
  @th:maximal-order-restricted-ideal-class-group. Further,
  @th:kernel-group-finite-prime-formula gives
  $
    D(Gamma) tilde.equiv
    frac(
      product_(P in S) frak(O)_P^times,
      frak(O)^+ product_(P in S) op("nr") Gamma_P^times
    ),
  $
  where $S$ consists of all maximal ideals $P$ of $R$ containing $r$. Since the
  set $S$ is finite, it suffices to show that for each $P in S$, there is a
  uniform upper bound on the index $|frak(O)_P^times : op("nr") Gamma_P^times|$.
  Note that $frak(O)_P^times=op("nr")(Gamma'_P)^times$, and $S$ is independent
  of $M$.

  Fixing $P in S$, choose $t>0$ so that $P^t subset r R_P$. Then we have
  $ 1+P^t Gamma'_P subset Gamma_P^times subset (Gamma'_P)^times, $
  and therefore
  $
    |frak(O)_P^times:op("nr") Gamma_P^times|
    <= |frak(O)_P^times:op("nr")(1+P^t Gamma'_P)|.
  $
  The maximal order $Lambda'_P$ can be expressed as
  $ Lambda'_P tilde.equiv product_i M_(n_i) lr((Delta_i)), $
  with each $Delta_i$ a noncommutative d.v.r. (see
  @i:th:local-matrix-maximal-orders). Since
  $Gamma'_P=End_(Lambda'_P) (Lambda'_P M_P)$, it follows readily that
  $ Gamma'_P tilde.equiv product_i M_(m_i) lr((Delta_i^compose)), $
  for some integers ${m_i}$ which depend on $Lambda'_P M_P$ (and hence on $M$).
  But then
  $ op("nr")(1+P^t Gamma'_P)=op("nr")(1+P^t Lambda'_P), $
  and therefore
  $
    |frak(O)_P^times:op("nr")(1+P^t Gamma'_P)|
    =|frak(O)_P^times:op("nr")(1+P^t Lambda'_P)|,
  $
  with the right-hand side independent of $M$. This completes the proof.
]

#source(343)
Returning to the question of locally free cancellation, let $G$ be a finite
group. By Jacobinski’s Cancellation Theorem, $ZZ G$ has locally free
cancellation unless $G$ has a quotient $Q_n$ ($n>=2$), $tilde(T)$, $tilde(O)$,
or $tilde(I)$ (see @th:group-algebra-eichler-quotient-criterion). Even in these
cases, however, it may happen that $ZZ G$ has locally free cancellation. For
example, Martinet @bib:Martinet1971 proved that $ZZ Q_2$ has the cancellation
property. This question was investigated thoroughly by Swan @bib:Swan1983, who
also calculated the number of isomorphism classes in each stable class for
various cases. We state without proof some of his main results.

#case-list(numbering: "1.")[#case[
  Let $G$ be a binary polyhedral group. Then $ZZ G$ has locally free
  cancellation if and only if $G$ is one of the seven groups
  $ Q_2, Q_3, Q_4, Q_5, tilde(T), tilde(O), tilde(I). $
] <case:binary-polyhedral-cancellation>][#case[
  Cancellation fails for $Q_2 times C_2$, where $C_2$ is cyclic of order 2, but
  holds for $Q_2 times H$ if $|H|$ is odd.
] <case:quaternion-direct-product-cancellation>][#case[
  Let $Lambda'$ be a maximal order in $QQ G$, where $G$ is a binary polyhedral
  group. Then $Lambda'$ has locally free cancellation if and only if $G$ is one
  of the 11 groups
  $
    Q_2, Q_3, Q_4, Q_5, Q_6, Q_7, Q_9, Q_15,
    tilde(T), tilde(O), tilde(I).
  $
  (This result is a key step in proving (@case:binary-polyhedral-cancellation).)
] <case:binary-polyhedral-maximal-order-cancellation>][#case[
  For $G=Q_6$, the generalized quaternion group of order 24, there are 16
  isomorphism classes of locally free left ideals of $ZZ G$, and eight stable
  isomorphism classes. Of these stable classes, four of them consist of a single
  isomorphism class, and the other four have three isomorphism classes each.
] <case:quaternion-six-stable-classes>][#case[
  The set of isomorphism classes of locally free left ideals in $ZZ G$ has no
  natural group structure, generally speaking.
] <case:locally-free-ideals-no-natural-group>]

We conclude this section by stating without proof a number of results related to
our previous theorems. As always, $Lambda$ denotes an $R$-order in a f.d.
separable $K$-algebra $A$, where $K$ is a global field.

#theorem(title: [Jacobinski @bib:Jacobinski1968a])[
  Let $M$ and $N$ be $Lambda$-lattices in the same genus. There exists a finite
  extension $K'$ of $K$ such that
  $ R' times.o_R M tilde.equiv R' times.o_R N $
  as $(R' times.o_R Lambda)$-lattices, where $R'$ is the integral closure of $R$
  in $K'$.
] <th:genus-lattices-isomorphic-after-field-extension>
#idx(
  "Jacobinski's Theorem",
  target: [@th:genus-lattices-isomorphic-after-field-extension],
)

Jacobinski also extended his Cancellation Theorem @th:jacobinski-cancellation,
giving necessary and sufficient conditions under which
$ M plus.o X tilde.equiv N plus.o X => M tilde.equiv N, $
#source(344)
where $M,N$, and $X$ are arbitrary $Lambda$-lattices (and necessarily $M,N$ lie
in the same genus). His proof, and other related proofs in the literature, makes
use of the following important generalization of Theorem
@th:eichler-maximal-order-unit-norm-global:

#theorem(name: [Eichler’s Theorem on Units])[
  Let $Lambda$ be a maximal $R$-order in the central simple $K$-algebra $A$,
  where $A$ is Eichler/$R$. Let $frak(f)$ be a full two-sided ideal of $Lambda$,
  and let $x in Lambda$ be such that
  $ op("nr")_(A slash K) x equiv a (mod frak(f) inter R) $
  for some $a in R^times inter K^+$. Then there exists a unit
  $u in Lambda^times$ with $x equiv u (mod frak(f))$.
] <th:eichler-units-congruence>
#idx("Eichler's Theorem of Units", target: [@th:eichler-units-congruence])
(For a proof, see Swan @bib:Swan1980.)

#exercises-heading

#exercise[
  Show that the group $J_0 lr((A))$ defined in @eq:reduced-norm-one-ideles is
  the closure of $[J(A),J(A)]$, whether or not $A$ is Eichler/$R$.
  #hint([@exc:idele-reduced-norm-commutator-closure])[
    Use @lem:norm-one-weak-approximation.
  ]
] <exc:idele-reduced-norm-commutator-closure>

#exercise[
  Let $g(x) in F[x]$ be irreducible with $g(0)!=0$, where $F$ is a $P$-adic
  field. Show that the Newton polygon of $g$ consists of a single straight line
  segment.
] <exc:irreducible-polynomial-newton-segment>

#exercise[
  Use Newton polygons to deduce Eisenstein’s Irreducibility Criterion.
] <exc:newton-polygon-eisenstein-criterion>

#exercise[
  Let $M,N$ be $Lambda$-lattices in the same genus, where $Lambda$ is an
  $R$-order. Show that $M^((k)) tilde.equiv N^((k))$ for some positive integer
  $k$. Conversely, such an isomorphism implies that $M,N$ are in the same genus.
  The result is due to Jacobinski @bib:Jacobinski1968b and Roiter
  @bib:Roiter1966a.
  #hint([@exc:genus-lattices-isomorphic-multiples])[
    Passing over to the order $Gamma=End_Lambda M$, it suffices to prove the
    result for locally free left $Gamma$-modules. Now use
    @cor:stable-ideal-single-free-summand together with the finiteness of
    $op("Cl") Gamma$.
  ]
] <exc:genus-lattices-isomorphic-multiples>

#exercise[
  Let $M$ be a $Lambda$-lattice. Show that there is only a finite number of
  isomorphism classes of indecomposable lattices $X$ such that
  $X divides M^((k))$ for some $k$.
  #hint([@exc:finitely-many-indecomposable-summands-of-multiples])[
    It suffices to treat the case $M=Lambda$. Now imitate the proof of Jones’s
    Theorem @i:th:jones-finite-type-completions.
  ]
] <exc:finitely-many-indecomposable-summands-of-multiples>

#exercise[
  Let $A$ be a central simple $K$-algebra, $dim_K A=n^2$, and let $Lambda$ be a
  maximal $R$-order in $A$. Given a left ideal $M$ of $Lambda$ of finite index,
  its _reduced norm_ $op("nr") M$ is the ideal of $R$ defined as follows: for
  each prime $P$ of $R$, write $M_P=Lambda_P a_P$ with $a_P in A_P$, and set
  $ op("nr") M_P=R_P dot op("nr") a_P. $
  Then $op("nr") M$ is the unique ideal such that $(op("nr") M)_P=op("nr") M_P$
  for each $P$. Prove
  #enum(
    numbering: "(i)",
    [$(op("nr") M)^n=op("ord")_R lr((Lambda slash M))$, where $op("ord")_R$ is
      the $R$-order ideal defined in §@i:ss:modules-dedekind-domains.],
    [Let $alpha=(a_P) in J(A)$, with the ${a_P}$ as above. Show that
      $op("nr") M$ is the ideal of $R$ which corresponds to the idele
      $op("nr") alpha in J(K)$ under the isomorphism
      $J(K) slash U(R) tilde.equiv "ideal group of" R$.],
    [#source(345)
      Using @th:class-group-reduced-norm-ideles, show that if $op("nr") M=R x$
      for some $x in K^+$, then $[M]=0$ in $op("Cl") Lambda$.],
    [If $A$ is Eichler/$R$, deduce that if $op("nr") M=R x$ for some $x in K^+$,
      then $M$ is a principal ideal $Lambda m$ for some $m in A^times$.],
  )
  For further discussion of reduced norms of ideals, see @bib:Reiner1975[MO]
  §§24, 34, and 35.
] <exc:reduced-norm-ideal-order-and-principality>
