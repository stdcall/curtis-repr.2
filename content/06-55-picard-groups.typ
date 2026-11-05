#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/55-picard.typ": *

== Picard Groups <sec:picard-groups>

=== Basic Properties <ss:picard-basic-properties>

The Picard group of an order $Lambda$, denoted by $op("Pic") Lambda$, is in a
rough sense the two-sided analogue of the locally free class group
$op("Cl") Lambda$. The elements of $op("Pic") Lambda$ are bimodule isomorphism
classes $(M)$ of suitably restricted $(Lambda,Lambda)$-bimodules $M$. We shall
see that $op("Pic") Lambda$ and $op("Cl") Lambda$ are closely related. Generally
speaking, $op("Pic") Lambda$ is considerably harder to calculate than
$op("Cl") Lambda$, and furthermore $op("Pic") Lambda$ is not necessarily an
abelian group. Many of the results given in the beginning of this section are
due to Fröhlich @bib:Frohlich1973 (see also Bass @bib:Bass1968).

We begin with a brief review of some definitions from §@i:sec:invertible-ideals
on invertible ideals, which in turn depend heavily on the Morita theory given in
§@i:ss:morita-theorems. Throughout this section, let $R$ denote a commutative
ring (with $1$). Let $Lambda,Delta$ denote $R$-algebras, so there are
homomorphisms $R arrow c(Lambda)$, $R arrow c(Delta)$, where $c(Lambda)$ denotes
the center of $Lambda$. Let $M = attach(M, bl: Lambda, br: Delta)$ be a
$(Lambda,Delta)$-bimodule; _we assume always that $R$ centralizes $M$_, that is,
#source(386)
$ r m = m r quad "for all" r in R, m in M. $
(This really means that $(r 1_Lambda) m = m(r 1_Delta)$ for all $r,m$.) There is
no loss of generality in making these restrictions, since we can always choose
$R = ZZ$ if need be. We assume once and for all that all maps occurring
hereafter are $R$-homomorphisms.

A bimodule $attach(M, bl: Lambda, br: Delta)$ is _invertible_ if $M$ gives a
Morita equivalence between the rings $Lambda$ and $Delta$. By @i:th:morita, this
occurs if and only if $attach(M, bl: Lambda)$ is a progenerator#footnote[
  This means that $M$ is a f.g. projective $Lambda$-module, such that $Lambda$
  is a direct summand of $M^((k))$ for some $k$.
] for the category of left $Lambda$-modules, and
$Delta tilde.equiv (op("End")_Lambda M)^"op"$. Equivalently, there must exist a
bimodule $attach(N, bl: Delta, br: Lambda)$ and bimodule surjections
$ M times.o_Delta N arrow Lambda, quad N times.o_Lambda M arrow Delta, $
<eq:invertible-bimodule-pairings>
such that the diagrams
#numbered-block(invertible-bimodule-associativity-squares)
<eq:invertible-bimodule-associativity>
commute. In this case, the maps in @eq:invertible-bimodule-pairings are
isomorphisms. We call $N$ the _inverse_ of $M$. The bimodule isomorphism class
$(N)$ of $N$ is uniquely determined by $M$, and in fact $N tilde.equiv M^(-1)$,
where
$
  M^(-1) = op("Hom")_Lambda lr(
    (attach(M, bl: Lambda, br: Delta),
      attach(Lambda, bl: Lambda, br: Lambda))
  )
  tilde.equiv op("Hom")_Delta lr(
    (attach(M, bl: Lambda, br: Delta),
      attach(Delta, bl: Delta, br: Delta))
  ).
$ <eq:inverse-bimodule-hom>
#idx("Invertible bimodule", target: [@eq:invertible-bimodule-pairings])
Of course, $M^(-1)$ gives a Morita equivalence between $Delta$ and $Lambda$. We
note also that
$
  Lambda tilde.equiv op("Hom")_Delta lr((M,M)), quad
  Delta tilde.equiv op("Hom")_Lambda lr((M,M)),
$ <eq:invertible-bimodule-endomorphism-rings>
where now $Delta$ and $op("Hom")_Lambda lr((M,M))$ are viewed as rings of
_right_ operators on $M$. If $R$ is noetherian and $Lambda$, $Delta$ and $M$ are
finitely generated over $R$, then by @i:prop:invertible-bimodule-localization
invertibility is a “local” property: $M$ is invertible if and only if for each
maximal ideal $P$ of $R$, the localization $M_P$ is an invertible
$(Lambda_P,Delta_P)$-bimodule. Under these finiteness hypotheses the subscript
$P$ could equally well mean “$P$-adic completion.”

In the above discussion, we are going to choose $Delta = Lambda$, and then
consider invertible $(Lambda,Lambda)$-bimodules
$attach(M, bl: Lambda, br: Lambda)$. Unless otherwise stated, we do _not_ assume
that $Lambda$ centralizes $M$. Thus, $lambda m = m lambda$ need not hold true
for all $lambda in Lambda$, $m in M$. By the above,
$attach(M, bl: Lambda, br: Lambda)$ is invertible if and only if
$attach(M, bl: Lambda)$ is a progenerator for the category of left
$Lambda$-modules, and every left $Lambda$-endomorphism of $M$ is uniquely given
by right multiplication by an element of $Lambda$.

#definition[
  Let $Lambda$ be an $R$-algebra, where $R$ is a commutative ring. Let $(M)$
  denote the bimodule isomorphism class of the bimodule
  $attach(M, bl: Lambda, br: Lambda)$, where we assume that $R$ centralizes $M$.
  The _Picard group_ of $Lambda$ relative to $R$, denoted by
  $op("Pic")_R Lambda$, is the multiplicative group consisting of all classes
  $(M)$ of invertible bimodules. Multiplication is defined by
  #source(387)
  $ (M)(M') = (M times.o_Lambda M'). $
  The identity element is the class $(Lambda)$, and inverses are given by
  $
    (M)^(-1) = (M^(-1)), quad "since"
    (M)(M^(-1)) = (M^(-1))(M) = (Lambda).
  $
] <def:picard-group>
#idx("Picard group", target: [@def:picard-group])
#nidx("$op(\"Pic\")$", "Picard group", target: [@def:picard-group])

_Beware:_ $op("Pic")_R Lambda$ need not be a commutative group!

We have already seen in §@i:sec:invertible-ideals that when $Lambda = R$ is a
Dedekind domain, then the elements of $op("Pic")_R Lambda$ are precisely the
classes of invertible fractional $R$-ideals in the quotient field $K$; but each
fractional $R$-ideal is necessarily invertible, so in this case
$op("Pic")_R Lambda tilde.equiv op("Cl") R$, the usual ideal class group of $R$.

#definition[
  Let $Lambda$ be an arbitrary ring, and let $C = c(Lambda)$ be its center. We
  define $op("Picent") Lambda = op("Pic")_C Lambda$, so $op("Picent") Lambda$ is
  the subgroup of $op("Pic")_ZZ Lambda$ consisting of all isomorphism classes of
  invertible bimodules $attach(M, bl: Lambda, br: Lambda)$ centralized by $C$.
  (Note: “Picent” is pronounced “pick-sent.”) We shall see below that when
  $Lambda$ is an order in a semisimple algebra $A$ over a field,
  $op("Picent") Lambda$ is precisely the group of invertible two-sided
  $Lambda$-ideals in $A$, modulo the subgroup of principal ideals generated by
  units in $c(A)$. Thus $op("Picent") Lambda$ is a natural object of
  investigation. If $R$ is a commutative ring, then $op("Picent") R$ is the
  group of classes of invertible $(R,R)$-bimodules centralized by $R$.
] <def:central-picard-group>
#idx("Picent", target: [@def:central-picard-group])
#nidx("$op(\"Picent\")$", "Picard group", target: [@def:central-picard-group])

We proceed to derive a number of formal properties of Picard groups, and begin
with an easy result. #lemma[
  Let $Lambda,Delta$ be $R$-algebras, and let $attach(M, bl: Lambda, br: Delta)$
  be an invertible bimodule centralized by $R$. Then $M$ determines an
  $R$-isomorphism $phi: c(Lambda) tilde.equiv c(Delta)$, defined thus: for each
  $c in c(Lambda)$, $phi(c)$ is the unique element of $c(Delta)$ such that
  $ c dot m = m dot phi(c) quad "for all" m in M. $
  <eq:morita-center-action>
  Taking $R = ZZ$, it follows that Morita equivalent rings have isomorphic
  centers.
] <lem:morita-centers-isomorphism>
#proof[
  Since $M$ is invertible, elements of $Lambda$ and $Delta$ are completely
  determined by their action on $M$, by
  @eq:invertible-bimodule-endomorphism-rings. For $c in c(Lambda)$, the map
  $m mapsto c m$ is a left $Lambda$-endomorphism of $M$, so there is a unique
  $phi(c) in Delta$ for which @eq:morita-center-action holds true. For $m in M$
  and $x in Delta$, we have
  $ m(phi(c) x) = (c m) x = (m x) phi(c) = m(x phi(c)), $
  so $phi(c)$ commutes with each $x in Delta$, and thus lies in $c(Delta)$. It
  is easily checked that $phi$ gives the desired $R$-isomorphism
  $c(Lambda) tilde.equiv c(Delta)$.
]

#source(388)
We use this result to prove that Morita equivalent rings have isomorphic Picard
groups.

#theorem[
  #enum(
    numbering: "(i)",
    [If the $R$-algebras $Lambda,Delta$ are Morita equivalent over $R$, then
      $op("Pic")_R Lambda tilde.equiv op("Pic")_R Delta$.],
    [If the rings $Lambda,Lambda'$ are Morita equivalent, then
      $op("Picent") Lambda tilde.equiv op("Picent") Lambda'$.],
  )
] <th:picard-morita-invariance>
#proof[
  #enum(
    numbering: "(i)",
    [Let $attach(M, bl: Lambda, br: Delta)$ be an invertible bimodule
      centralized by $R$. The reader will easily check that the map
      $
        (X) mapsto (M^(-1) times.o_Lambda X times.o_Lambda M),
        quad (X) in op("Pic")_R Lambda,
      $
      gives an isomorphism $op("Pic")_R Lambda tilde.equiv op("Pic")_R Delta$.
      This isomorphism may depend on the choice of $M$.],
    [Now let $attach(N, bl: Lambda, br: Lambda')$ be an invertible bimodule, and
      as in @lem:morita-centers-isomorphism, let $N$ determine the isomorphism
      $phi: C tilde.equiv C'$ of centers. Thus
      $
        c dot n = n dot phi(c) quad "for all" c in C = c(Lambda)
        "and all" n in N.
      $
      For $(X) in op("Picent") Lambda$ we have $c x = x c$ for all $c in C$,
      $x in X$. We must show that
      $(N^(-1) times.o_Lambda X times.o_Lambda N) in op("Picent") Lambda'$. But
      each $c' in C'$ is of the form $c' = phi(c)$ for some $c in C$, and
      $
        (n' times.o x times.o n) phi(c)
        = n' times.o x times.o c n
        = n' c times.o x times.o n
        = phi(c)(n' times.o x times.o n),
      $
      so $c'$ centralizes $N^(-1) times.o X times.o N$, as desired. This
      completes the proof. For further results of this nature, see Exercises
      @exc:morita-central-picard-equivalence–@exc:azumaya-algebra-definition.],
  )
]

Now let $op("Aut")_R Lambda$ denote the group of all $R$-automorphisms of the
$R$-algebra $Lambda$, and let $op("In") Lambda$ be the subgroup consisting of
all inner automorphisms $lr({i_u: u in Lambda^times})$, where
$i_u lr((x)) = u x u^(-1)$, $x in Lambda$. Then
$op("In") Lambda ⊴ op("Aut")_R Lambda$, and we define
$
  op("Out")_R Lambda = op("Aut")_R Lambda slash op("In") Lambda
  = "outer automorphism group of" Lambda "over" R.
$
#idx("Outer automorphism group")
#nidx("$op(\"Aut\")$", "automorphism groups")
#nidx("$op(\"Out\")$", "outer automorphism groups")
We shall see that $op("Out")_R Lambda$ maps injectively into
$op("Pic")_R Lambda$. To begin with, let $attach(M, bl: Lambda, br: Delta)$ be
any bimodule, and let $f in op("Aut") Lambda$, $g in op("Aut") Delta$. Let
$attach(M, bl: f, br: g)$ be the $(Lambda,Delta)$-bimodule having the same
elements as $M$, but with the actions of $Lambda$ and $Delta$ “twisted” by $f$
and $g$, respectively:
$
  lambda compose m compose delta quad ("in" attach(M, bl: f, br: g))
  = f(lambda) m g(delta) quad ("in" M)
$
for all $lambda in Lambda$, $delta in Delta$, $m in M$. It is clear that
$
  attach(lr((attach(M, bl: f, br: g))), bl: f', br: g')
  tilde.equiv attach(M, bl: f f', br: g g') quad "as bimodules".
$
The reader will easily verify the following:

#source(389)
#proposition[
  Let $Lambda$ be an $R$-algebra, viewed as $(Lambda,Lambda)$-bimodule. For each
  $f,g in op("Aut")_R Lambda$ there is a $(Lambda,Lambda)$-bimodule
  $attach(Lambda, bl: f, br: g)$ centralized by $R$. There are bimodule
  isomorphisms
  $
    attach(Lambda, bl: f, br: g)
    tilde.equiv attach(Lambda, bl: h f, br: h g)
    tilde.equiv attach(Lambda, bl: 1, br: f^(-1) g)
    tilde.equiv attach(Lambda, bl: g^(-1) f, br: 1),
  $
  $
    attach(lr((attach(Lambda, bl: f, br: g))), bl: f', br: g')
    tilde.equiv attach(Lambda, bl: f f', br: g g'),
  $
  $
    attach(Lambda, bl: f, br: g) times.o
    attach(Lambda, bl: f', br: g')
    tilde.equiv attach(Lambda, bl: f, br: g f'^(-1) g'), quad
    attach(Lambda, bl: 1, br: g) times.o
    attach(Lambda, bl: 1, br: g')
    tilde.equiv attach(Lambda, bl: 1, br: g g'),
  $
  $
    attach(Lambda, bl: 1, br: f) times.o attach(Lambda, bl: f, br: 1)
    tilde.equiv Lambda tilde.equiv
    attach(Lambda, bl: f, br: 1) times.o attach(Lambda, bl: 1, br: f),
  $
  where $times.o$ means $times.o_Lambda$.
] <prop:twisted-bimodule-identities>

Using these, we obtain:

#theorem[
  Given an $R$-algebra $Lambda$, there is an exact sequence of groups
  $
    1 arrow op("In") Lambda arrow op("Aut")_R Lambda
    arrow^(omega_0) op("Pic")_R Lambda,
  $
  where $omega_0 lr((f)) = (attach(Lambda, bl: 1, br: f))$ for
  $f in op("Aut")_R Lambda$. Thus $omega_0$ induces a monomorphism
  $ omega: op("Out")_R Lambda arrow op("Pic")_R Lambda. $
] <th:outer-automorphism-picard-embedding>
#proof[
  Each $f in op("Aut")_R Lambda$ gives rise to a $(Lambda,Lambda)$-bimodule
  $attach(Lambda, bl: 1, br: f)$ centralized by $R$. By
  @prop:twisted-bimodule-identities, $attach(Lambda, bl: f, br: 1)$ is an
  inverse for $attach(Lambda, bl: 1, br: f)$, and $omega_0$ is a homomorphism.
  We must show that $ker omega_0 = op("In") Lambda$. We have
  $omega_0 lr((f)) = 1$ if and only if there exists a bimodule isomorphism
  $theta: Lambda tilde.equiv attach(Lambda, bl: 1, br: f)$, that is, there
  exists a bijection $theta: Lambda arrow Lambda$ such that #named-equation(
    name: [$(ast)$],
  )[
    $ theta(a x b) = a dot theta(x) f(b) quad "for all" a,b,x in Lambda. $
  ] <eq:outer-automorphism-bimodule-isomorphism>
  For $f = i_u$, where $i_u lr((x)) = u x u^(-1)$, choose $theta$ so that
  $theta(x) = x u^(-1)$. This proves that $ker omega_0 supset op("In") Lambda$.

  Conversely, let $theta: Lambda arrow Lambda$ be a bijection satisfying
  @eq:outer-automorphism-bimodule-isomorphism, and choose $u = theta(1)$. Then
  $Lambda = theta(Lambda) = theta(Lambda dot 1) = Lambda u$, and likewise
  $Lambda = u Lambda$, so $u in Lambda^times$. Taking $x = b = 1$ in
  @eq:outer-automorphism-bimodule-isomorphism, we obtain $theta(a) = a u$ for
  $a in Lambda$. Now set $a = x = 1$ in
  @eq:outer-automorphism-bimodule-isomorphism, so we have $b u = u f(b)$ for all
  $b in Lambda$, and thus $f$ is the inner automorphism $i_(u^(-1))$. This
  completes the proof.
]

In considering the one-sided module structure of invertible bimodules, we shall
repeatedly use the following elementary result:

#theorem[
  Let $(X),(Y) in op("Pic")_R Lambda$. Then
  $attach(X, bl: Lambda) tilde.equiv attach(Y, bl: Lambda)$ if and only if
  $(Y) in (X) dot im omega$, that is, $Y tilde.equiv attach(X, bl: 1, br: f)$ as
  bimodules for some $f in op("Aut")_R Lambda$.
] <th:picard-one-sided-isomorphism-cosets>
#proof[
  For $f in op("Aut")_R Lambda$, there is a bimodule isomorphism
  $
    attach(X, bl: 1, br: f)
    tilde.equiv X times.o_Lambda attach(Lambda, bl: 1, br: f).
  $
  #source(390)
  Thus $(Y) in (X) dot im omega$ if and only if
  $Y tilde.equiv attach(X, bl: 1, br: f)$ for some $f$. Clearly
  $attach(X, bl: Lambda) tilde.equiv attach(Y, bl: Lambda)$ whenever such an
  isomorphism exists.

  Conversely, a left $Lambda$-isomorphism $h: X tilde.equiv Y$ induces a ring
  isomorphism
  $
    h^*: op("End")_Lambda Y tilde.equiv op("End")_Lambda X, quad
    h^* lr((phi)) = h^(-1) phi h.
  $
  Since $attach(X, bl: Lambda, br: Lambda)$ is invertible, each element of
  $op("End")_Lambda X$ is a right multiplication $a_r$ for some $a in Lambda$,
  and $phi in op("End")_Lambda Y$ is some $b_r$. Thus each $b in Lambda$
  determines a unique $f(b) in Lambda$ such that $h^(-1) b_r h = (f(b))_r$ on
  $X$, that is,
  $ (h(x)) b = h(x f(b)) quad "for all" x in X, b in Lambda. $
  It follows easily that $f in op("Aut")_R Lambda$, and that
  $h: attach(X, bl: 1, br: f) arrow Y$ is a bimodule isomorphism.
]

Before studying $op("Picent") Lambda$ in more detail, we briefly consider the
relation between $op("Picent") Lambda$ and $op("Pic")_R Lambda$, where $Lambda$
is an $R$-algebra with center $C$. By @lem:morita-centers-isomorphism, each
invertible $attach(M, bl: Lambda, br: Lambda)$ centralized by $R$ determines an
$R$-automorphism $Phi_M$ of $C$, according to the formula
$ Phi_M lr((c)) dot m = m dot c quad "for all" c in C, m in M. $
Clearly $Phi_M$ depends only on the bimodule isomorphism class of $M$, and
$Phi_M = id_C$ if and only if $(M) in op("Picent") Lambda$. In the special case
where $M = attach(Lambda, bl: 1, br: f)$ with $f in op("Aut")_R Lambda$, we have
(for $c in C$)
$ f(c) m = m f(c) = m dot c quad "for all" c in C, m in M, $
where $m dot c$ is computed inside $attach(Lambda, bl: 1, br: f)$. Thus for
$M = attach(Lambda, bl: 1, br: f)$, $Phi_M$ is the restriction of $f$ to $C$.
From these remarks, we obtain:

#theorem[
  For any $R$-algebra $Lambda$ with center $C = c(Lambda)$, there is an exact
  sequence of groups
  $
    1 arrow op("Picent") Lambda arrow op("Pic")_R Lambda
    arrow^Phi op("Aut")_R C.
  $
  If $Lambda$ is commutative, this sequence is split exact.
] <th:picard-center-automorphism-sequence>
#proof[
  Let $(M),(N) in op("Pic")_R Lambda$, and set $f = Phi_M$, $g = Phi_N$. Then
  for each $c in C$ we have
  $ f(c) m = m c, quad g(c) n = n c quad "for all" m in M, n in N. $
  Therefore
  $
    (m times.o n) c = m times.o n c = m g(c) times.o n
    = f(g(c))(m times.o n),
  $
  which shows that $Phi_(M times.o N) = Phi_M compose Phi_N$, that is, $Phi$ is
  a homomorphism. Our earlier remarks show that $ker Phi = op("Picent") Lambda$.
  #source(391)
  Now suppose $Lambda = C$, and define $omega_0$ as in
  @th:outer-automorphism-picard-embedding, so
  $omega_0 lr((f)) = (attach(Lambda, bl: 1, br: f)) in op("Pic")_R Lambda$ for
  $f in op("Aut")_R Lambda$. By the above remarks, $Phi_(omega_0 lr((f))) = f$,
  so $Phi compose omega_0 = "identity map on" op("Aut")_R C$. This completes the
  proof.
]

#remarks[
  #enum(
    numbering: "(i)",
    [When $A = product.co_(i=1)^t A_i$ is a semisimple algebra over a field $K$,
      we can describe the map
      $ Phi_A: op("Pic")_K A arrow op("Aut")_K c(A) $
      explicitly, as follows. Suppose that the simple component $A_i$ has
      skewfield part $D_i$ and center $K_i$, so $c(A) = product.co K_i$ and each
      $f in op("Aut")_K c(A)$ must permute the $lr({K_i})$. Thus $f$ is
      completely determined by some permutation $pi$ of the set
      $lr({1, dots, t})$, together with a collection of $K$-isomorphisms
      $ f_i: K_i tilde.equiv K_(pi i), quad 1 <= i <= t, $
      where $f_i = f|_(K_i)$. Now $op("Picent") A = 1$ by
      @th:semisimple-central-picard-trivial, so $Phi_A$ is injective. Each
      $(X) in op("Pic")_K A$ yields a Morita equivalence of $A$ with itself.
      Using this fact, Fröhlich @bib:Frohlich1973 showed that the image of
      $Phi_A$ consists precisely of those elements $f in op("Aut")_K c(A)$ such
      that for each $i$, $1 <= i <= t$, the isomorphism
      $f_i: K_i tilde.equiv K_(pi(i))$ can be extended to an isomorphism
      $D_i tilde.equiv D_(pi(i))$.

      For a further discussion of these matters, we refer the reader to the work
      of Janusz @bib:Janusz1976.],
    [Let $R$ be a Dedekind domain with quotient field $K$, and let $Lambda$ be a
      maximal $R$-order in a f.d. separable $K$-algebra $A$. Keeping the above
      notation, we note first that there is a group isomorphism
      $ op("Aut")_R c(Lambda) tilde.equiv op("Aut")_K c(A), $
      given by extending each $R$-automorphism $f$ of $c(Lambda)$ to a
      $K$-automorphism $f'$ of $c(A)$. It follows readily that $f in im Phi$ if
      and only if $f' in im Phi_A$, where
      $Phi: op("Pic")_R Lambda arrow op("Aut")_R c(Lambda)$. Thus, the
      calculation of $im Phi$ reduces to the situation discussed in the previous
      remark.],
    [If $A$ is a central simple $K_1$-algebra, and $dim_K K_1 < infinity$, we
      may view $A$ as $K$-algebra. There is an exact sequence
      $
        1 arrow op("Picent") A arrow op("Pic")_K A
        arrow^(Phi_A) op("Aut")_K K_1,
      $
      and $im Phi_A$ consists precisely of those $K$-automorphisms of $K_1$
      which can be extended to $K$-automorphisms of $A$. (In this connection,
      see Janusz @bib:Janusz1976).],
  )
] <rem:semisimple-picard-center-automorphisms>

We now prove the fundamental result:

#theorem[
  For any f.d. semisimple $K$-algebra $A$, we have $op("Picent") A = 1$.
] <th:semisimple-central-picard-trivial>
#proof[
  By Exercise @exc:central-picard-direct-product it suffices to treat the case
  where $A$ is a central simple
  #source(392)
  $K$-algebra. By the discussion preceding
  @i:prop:invertible-bimodule-localization, for each $(X) in op("Picent") A$ we
  have $X tilde.equiv A$ as left $A$-modules. Therefore
  $X tilde.equiv attach(A, bl: 1, br: f)$ (as bimodules) for some
  $f in op("Aut")_K A$, by @th:picard-one-sided-isomorphism-cosets. But $f$ is
  an inner automorphism of $A$ by the Skolem–Noether Theorem
  @i:th:skolem-noether, so $(attach(A, bl: 1, br: f)) = 1$ in $op("Picent") A$
  by @th:outer-automorphism-picard-embedding. Thus $(X) = 1$ as desired. Another
  proof can be given by using Exercise @exc:azumaya-algebra-definition, since
  $A$ is an Azumaya $K$-algebra, and $op("Pic")_K K = 1$.
]

If $Lambda$ is a commutative ring, we may identify the set of
$(Lambda,Lambda)$-bimodules centralized by $Lambda$ with the set of one-sided
$Lambda$-modules. In our present notation, Theorem
@i:th:invertible-module-locally-free can now be stated as follows:

#theorem[
  Let $Lambda$ be a commutative $R$-algebra, f.g./$R$ as module, where $R$ is a
  commutative noetherian ring. Then any f.g. $Lambda$-module $M$ (centralized by
  $Lambda$) is invertible if and only if $M_P tilde.equiv Lambda_P$ for each
  maximal ideal $P$ of $R$. In particular, if $R$ is a local ring, then
  $op("Picent") Lambda = 1$.
] <th:commutative-invertible-locally-rank-one>

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [The proof of @i:th:invertible-module-locally-free shows that
      $op("Picent") Lambda = 1$ for any commutative ring $Lambda$ such that
      $Lambda slash op("rad") Lambda$ is a direct sum of fields.],
    [If $Lambda$ is commutative and $R$ is semilocal, then again
      $op("Picent") Lambda = 1$.],
  )
] <rem:semilocal-commutative-central-picard-trivial>

=== Picard Groups of Orders <ss:picard-orders>

We shall specialize the preceding discussion to the case where $Lambda$ is an
$R$-order in a f.d. $K$-algebra $A$, with $K$ the quotient field of an integral
domain $R$. We begin by explaining the connection between invertible ideals and
invertible modules. If $M$ and $N$ are two-sided $Lambda$-submodules of $A$ such
that $M N = N M = Lambda$, we call $M$ an _invertible $Lambda$-ideal in $A$_,
and $N$ its inverse. In this case, the maps
$
  M times.o_Lambda N arrow M N = Lambda, quad
  N times.o_Lambda M arrow N M = Lambda
$
are both surjective, so $M$ and $N$ are invertible bimodules, and $N = M^(-1)$.
Further, $c(Lambda)$ centralizes $M$, so $(M) in op("Picent") Lambda$.
#idx("Invertible ideal")

Let $I(Lambda)$ denote the multiplicative group of invertible $Lambda$-ideals in
$A$, with multiplication performed within $A$. If $C = c(Lambda)$, then clearly
$c(A) = K C$. We now show:

#theorem[
  There is an exact sequence of groups
  $
    1 arrow C^times arrow (K C)^times arrow^rho I(Lambda)
    arrow^sigma op("Picent") Lambda arrow^tau op("Picent") A,
  $
  where $rho(u) = Lambda u$, $sigma(M) = (M)$, and $tau(X) = (K X)$.
] <th:invertible-ideal-central-picard-sequence>
#proof[
  Exactness at $(K C)^times$ is clear, and $sigma rho = 1$. If $sigma(M) = 1$
  then there is a
  #source(393)
  bimodule isomorphism $theta: Lambda tilde.equiv M$. Letting $c = theta(1)$, we
  obtain $M = Lambda c$. Then $K M = K Lambda dot c$ implies that
  $c in A^times$. Further, from $theta(1) a = theta(a) = a theta(1)$ for all
  $a in Lambda$, we deduce that $c in (K C)^times$. Thus $M = rho(c)$, as
  desired.

  Finally, let $(X) in op("Picent") Lambda$ be such that $tau(X) = 1$. Since $X$
  is $Lambda$-projective, the map $X arrow K X$ is injective, and there is a
  bimodule isomorphism $f: K X tilde.equiv A$. Set $M = f(X)$, so $M$ is a
  $Lambda$-ideal in $A$ which is invertible as $(Lambda,Lambda)$-bimodule. Then
  $
    M^(-1) = op("Hom")_Lambda lr(
      (attach(M, bl: Lambda),
        attach(Lambda, bl: Lambda))
    )
    tilde.equiv op("Hom")_Lambda lr(
      (attach(M, br: Lambda),
        attach(Lambda, br: Lambda))
    ).
  $
  Tensoring with $K$ and identifying the new Hom’s with $A$, we may then
  identify $M^(-1)$ with a two-sided $Lambda$-ideal in $A$. From
  @eq:invertible-bimodule-pairings we deduce that
  $M M^(-1) = M^(-1) M = Lambda$, so $M$ is an invertible ideal. Then
  $(X) = (M) in im sigma$, as desired, and the proof is complete.
]

Combining the above with Theorem @th:semisimple-central-picard-trivial, we
obtain:

#corollary[
  If $Lambda$ is an $R$-order in a f.d. semisimple $K$-algebra $A$, then
  $
    op("Picent") Lambda tilde.equiv
    I(Lambda) slash lr({Lambda u: u in (K C)^times}).
  $
] <cor:central-picard-invertible-ideal-quotient>

This justifies our earlier remark that $op("Picent") Lambda$, rather than
$op("Pic")_R Lambda$, should be our primary concern. It may be viewed as a
natural generalization of the usual ideal class group occurring in algebraic
number theory. Furthermore, we have:

#theorem[
  Let $Lambda$ be an $R$-order in a f.d. semisimple $K$-algebra $A$, where $K$
  is a number field. Then $op("Pic") Lambda$ and $op("Picent") Lambda$ are
  finite groups.
] <th:order-picard-groups-finite>
#proof[
  Let $E$ be the image of $Lambda times.o_R Lambda^"op"$ in
  $A times.o_K A^"op"$, acting on $A$ by $(a times.o b) x = a x b$. The algebra
  $A times.o_K A^"op"$ is semisimple, since $K$ is a number field. The two-sided
  $Lambda$-ideals in $A$ are $E$-lattices in this fixed module, and their
  $E$-isomorphisms are precisely their bimodule isomorphisms.#ed-note[
    A left-module isomorphism need not respect the right action. Thus the
    original inference from finitely many left-module classes to finitely many
    bimodule classes requires an additional argument.
  ]

  To retain the generality of $R$, choose a full $ZZ$-order $O subset.eq R$ in
  $K$, and a nonzero integer $c$ with $c O_K subset.eq O$, where $O_K$ is the
  ring of integers of $K$. Put $overline(R) = R O_K$. This is a Dedekind
  overring of $O_K$, unless it is $K$, and $c overline(R) subset.eq R$; moreover
  $overline(R) slash c overline(R)$ is finite. Suppose first that
  $overline(R) != K$, and let $Gamma = overline(R) E$. By the Jordan–Zassenhaus
  Theorem (§@i:sec:jordan-zassenhaus), the $Gamma$-lattices $Gamma I$ in $A$
  have finitely many isomorphism classes. For each $E$-lattice $I$ we have
  $c Gamma I subset.eq I subset.eq Gamma I$. Each finite quotient
  $Gamma I slash c Gamma I$ has only finitely many submodules, proving
  finiteness of the $E$-lattice classes. If $overline(R) = K$, then
  $c overline(R) subset.eq R$ forces $R = K$, and the assertion is immediate.
  Hence $op("Picent") Lambda$ is finite by
  @cor:central-picard-invertible-ideal-quotient. Finally, by
  @th:picard-center-automorphism-sequence and
  @rem:semisimple-picard-center-automorphisms(ii),
  $op("Pic")(Lambda) slash op("Picent") Lambda$ embeds in the finite group
  $op("Aut")_QQ c(A)$.
]

Returning to the general case, let us define
$
  N(Lambda) = "normalizer of" Lambda "in" A
  = lr({x in A^times: x Lambda x^(-1) = Lambda}).
$
<eq:order-normalizer>
#idx("Normalizer of Λ", target: [@eq:order-normalizer])
The normalizer arises naturally from the following:

#lemma[
  Let $Lambda$ be an $R$-order in a f.d. separable $K$-algebra $A$, and let
  $x in A^times$. Then
  #enum(
    numbering: "(i)",
    [$Lambda x$ is a $(Lambda,Lambda)$-bimodule if and only if
      $x in N(Lambda)$.],
    [For $x in N(Lambda)$, $Lambda x$ is an invertible bimodule, with inverse
      $Lambda x^(-1)$.],
    [$x in N(Lambda)$ if and only if $Lambda x subset.eq x Lambda$.],
  )
] <lem:order-normalizer-invertible-principal-ideals>
#source(394)
#proof[
  For $x in A^times$, we have
  $
    Lambda x "is a bimodule" <=>
    x Lambda subset.eq Lambda x <=> x in N(Lambda),
  $
  where the last implication may be proved over the present arbitrary domain $R$
  as follows.#ed-note[
    Exercise @exc:order-conjugate-containment, cited in the original proof,
    assumes a Dedekind domain; this subsection assumes only an integral domain.
  ] Put $T(a) = x a x^(-1)$ for $a in A$. If $T Lambda subset.eq Lambda$, finite
  generation of $Lambda$ implies that $T$ is integral over $R$. Also
  $det T = 1$, as is seen after passing to a splitting field. Thus all
  eigenvalues of $T$ are integral over $R$, and each inverse eigenvalue is a
  product of the others, so is integral as well. The coefficients of the
  characteristic polynomial of $T^(-1)$ are therefore integral over $R$.
  Transitivity of integrality shows that $T^(-1)$ satisfies a monic equation
  over $R$; multiplying it by a suitable power of $T$ gives $T^(-1) in R[T]$.
  Hence $T^(-1) Lambda subset.eq Lambda$, proving equality. The rest of the
  lemma is now obvious.
]

Before stating the next result, which will be needed for the calculation of
$op("Picent") Lambda$ in various cases, we introduce some additional notation:
let $C = c(Lambda)$, and put
$
  op("Autcent") Lambda = op("Aut")_C Lambda, quad
  op("Outcent") Lambda = op("Out")_C Lambda
  = op("Aut")_C lr((Lambda)) slash op("In")(Lambda).
$
#idx("Autcent")
#idx("Outcent")
#nidx("$op(\"Autcent\")$", "automorphism groups")
#nidx("$op(\"Outcent\")$", "outer automorphism groups")
By @th:outer-automorphism-picard-embedding, there is a monomorphism
$
  omega: op("Outcent") Lambda arrow op("Picent") Lambda, quad
  "given by" omega(f) = (attach(Lambda, bl: 1, br: f))
  "for" f in op("Autcent") Lambda.
$
Then we have:

#theorem[
  Let $Lambda$ be an $R$-order in a f.d. semisimple $K$-algebra $A$.
  #enum(
    numbering: "(i)",
    [There is an isomorphism
      $
        rho: N(Lambda) slash Lambda^times (K C)^times
        tilde.equiv op("Outcent") Lambda
        = op("Autcent")(Lambda) slash op("In")(Lambda),
      $
      induced by the map $rho(x) = i_x$ for $x in N(Lambda)$, where $i_x$ is the
      automorphism of $Lambda$ given by $lambda mapsto x lambda x^(-1)$,
      $lambda in Lambda$.],
    [There is a commutative diagram
      #normalizer-central-picard-triangle
      where $omega' lr((x)) = (Lambda x)$ for $x in N(Lambda)$. The maps $omega$
      and $omega'$ are monomorphisms.],
    [We have
      $
        omega(op("Outcent") Lambda) = lr(
          {(X) in op("Picent") Lambda:
            attach(X, bl: Lambda) tilde.equiv attach(Lambda, bl: Lambda)}
        ).
      $],
  )
] <th:normalizer-outer-central-automorphisms>
#proof[
  Each $f in op("Aut")_C Lambda$ extends to an $tilde(f) in op("Aut")_(K C) A$.
  By the Skolem–Noether Theorem @i:th:skolem-noether, $tilde(f) = i_x$ for some
  $x in A^times$, so $rho$ is surjective. The rest of the proof is an easy
  exercise for the reader.
]

#corollary[
  Let $R$ be a d.v.r., and let $Lambda$ be a maximal $R$-order in a separable
  $K$-algebra $A$. Then the maps $rho,omega,omega'$ above are isomorphisms. In
  particular, if $Lambda tilde.equiv M_n lr((R))$ for some $R$, then
  $N(Lambda) = Lambda^times dot K^times$.
] <cor:local-maximal-order-picard-normalizer>
#source(395)
#proof[
  Given $(X) in op("Picent") Lambda$, we may assume by
  @cor:central-picard-invertible-ideal-quotient that $X$ is a two-sided
  $Lambda$-ideal in $A$ such that $K X = A$. Then
  $attach(X, bl: Lambda) tilde.equiv attach(Lambda, bl: Lambda)$ by Exercise
  @i:exc:dvr-maximal-order-lattice-isomorphism, so $(X) in im omega$ by
  @th:normalizer-outer-central-automorphisms(iii). Thus $omega$ gives an
  isomorphism $op("Outcent") Lambda tilde.equiv op("Picent") Lambda$ in this
  case. Finally, for $Lambda = M_n lr((R))$ we have
  $op("Picent") Lambda tilde.equiv op("Picent") R = 1$, so
  $N(Lambda) = Lambda^times dot K^times$ as claimed.
]

In the above proof, the hypothesis that $Lambda$ be a maximal order was used
only to guarantee that for $(X) in op("Picent") Lambda$, the
$(Lambda,Lambda)$-bimodule $X$ is free as left $Lambda$-module. This property
also holds when $Lambda$ is a group ring $R G$ of a finite group $G$ over a
d.v.r. $R$ of characteristic $0$. If $(X) in op("Picent") Lambda$, then
$K X tilde.equiv K G$ as bimodules, and $attach(X, bl: Lambda)$ is a projective
$R G$-module. By Swan’s Theorem
@i:th:local-projective-group-lattice-cancellation, it follows that
$attach(X, bl: Lambda) tilde.equiv attach(Lambda, bl: Lambda)$. We thus obtain
the important result, basic in the calculation of Picard groups of group rings:
$ op("Picent") R G tilde.equiv N(R G) slash (R G)^times (K C)^times, $
where $N(R G)$ is the normalizer of $R G$ in $K G$, and $K C$ is the center of
$K G$. We shall return to this result in
@th:locally-free-picard-local-global-sequence, but for the moment let us
continue with our discussion of maximal orders.

#theorem[
  Let $R$ be a complete d.v.r., and let $Lambda$ be a maximal $R$-order in a
  central simple $K$-algebra $A$ with skewfield part $D$. Let $e = e(D slash K)$
  be the ramification index of $D$ over $K$, and $d(Lambda slash R)$ the
  discriminant. Then
  $ op("Picent") Lambda tilde.equiv ZZ slash e ZZ, $
  and $op("Picent") Lambda = 1$ if $d(Lambda slash R) = R$.
] <th:local-maximal-order-central-picard-cyclic>
#proof[
  Let $pi$ be a prime element of $R$, and $pi_D$ a prime element of $Delta$,
  where $Delta$ is the maximal $R$-order in $D$ (see
  @i:th:division-algebra-maximal-order-valuation). Then by
  @i:th:local-matrix-maximal-orders,
  $ pi Delta = (pi_D Delta)^e, quad op("rad") Lambda = pi_D Lambda, $
  and every two-sided $Lambda$-ideal in $A$ is a power of $op("rad") Lambda$.
  Since $op("Picent") Lambda tilde.equiv
  I(Lambda) slash lr({pi^k Lambda: k in ZZ})$, we obtain
  $op("Picent") Lambda tilde.equiv ZZ slash e ZZ$. Finally, if $e > 1$ then
  $pi^(e-1) R$ divides $d(Lambda slash R)$, as follows from an easy
  generalization of Exercise @i:exc:different-ramification-bound (see
  @bib:Reiner1975[MO] §25). This yields the last assertion in the theorem, and
  completes the proof.
]

In order to extend the above to the global case, we must investigate the
connection between local and global Picard groups. The key result, valid for
nonmaximal orders as well, is the following:

#theorem(title: [Fröhlich @bib:Frohlich1973])[
  Let $Lambda$ be any $R$-order in a separable $K$-algebra $A$, where $R$ is a
  Dedekind domain with quotient field $K$, and let $C = c(Lambda)$. For each
  maximal ideal $P$ of $R$, let $Lambda_P$ denote the $P$-adic completion of
  $Lambda$. Then
  #source(396)
  $op("Picent") Lambda_P = 1$ a.e., and there is an exact sequence
  $
    1 arrow op("Picent") C arrow^tau op("Picent") Lambda
    arrow^(tau') product_P op("Picent") Lambda_P arrow 1.
  $
  The map $tau$ is given by $tau(L) = (L times.o_C Lambda)$ for
  $(L) in op("Picent") C$.
] <th:central-picard-local-global-sequence>
#proof[
  Since $A$ is separable over $K$, for almost all $P$ the center $C_P$ is étale
  over $R_P$ and $Lambda_P$ is an Azumaya $C_P$-algebra. Thus
  $op("Picent") Lambda_P tilde.equiv op("Picent") C_P$ by Exercise
  @exc:azumaya-algebra-definition, and this group is $1$ because $C_P$ is
  commutative and semilocal, by
  @th:commutative-invertible-locally-rank-one.#ed-note[
    The split-matrix premise in the original proof need not hold. For
    $R = RR[t]$ and $Lambda = bb(H) times.o_RR R$, the Hamilton quaternion
    algebra remains division on completion at every real prime $(t-a)$.
  ]

  Now let us make each left $C$-module $L$ into a bimodule centralized by $C$.
  Then $L times.o_C Lambda$ is naturally a $(Lambda,Lambda)$-bimodule
  centralized by $C$. As usual, let $I(C)$ denote the group of invertible
  $C$-ideals in $K C$. Then for each $L in I(C)$, there is a
  $(Lambda,Lambda)$-isomorphism
  $ L times.o_C Lambda tilde.equiv L Lambda quad ("computed inside" A). $
  If $L' = L^(-1)$, then $(L Lambda)(L' Lambda) = L L' Lambda = Lambda$, so for
  each $L in I(C)$ we have $L Lambda in I(Lambda)$. It is now clear that $tau$
  is a homomorphism, and we must prove $tau$ injective.

  For any bimodule $attach(M, bl: Lambda, br: Lambda)$, let us define
  $
    M^Lambda = lr(
      {m in M: lambda m = m lambda
        "for all" lambda in Lambda}
    ).
  $
  Then $M^Lambda$ is a $C$-module, determined up to isomorphism by the class
  $(M)$. Clearly
  $
    (M plus.o N)^Lambda = M^Lambda plus.o N^Lambda, quad "and"
    Lambda^Lambda = C.
  $
  We observe next that for $(L) in op("Picent") C$, we have
  $
    (L times.o_C Lambda)^Lambda = L times.o_C C tilde.equiv L
    quad "as" C "-modules".
  $
  (The formula is obvious when $L = C$, and hence also for every projective
  $C$-module $L$.) But now suppose that $tau(L) = 1$; then
  $L times.o_C Lambda tilde.equiv Lambda$, so
  $
    L tilde.equiv (L times.o_C Lambda)^Lambda
    tilde.equiv Lambda^Lambda tilde.equiv C,
  $
  which completes the proof that $tau$ is a monomorphism.

  We show next that $tau'$ is surjective, where $tau' lr((X)) = product_P (X_P)$
  for each $(X) in op("Picent") Lambda$. To begin with, $c(Lambda_P) = C_P$ so
  $(X_P) in op("Picent") Lambda_P$ for each $P$. Suppose now that for each $P$,
  we are given an element $X(P) in I(Lambda_P)$, and we wish to find an
  $(X) in op("Picent") Lambda$ for which $tau' lr((X)) = product X(P)$. Since
  $op("Picent") Lambda_P = 1$ a.e., we may assume that $X(P) = Lambda_P$ a.e. We
  now set
  $ X = A inter lr((inter_P X(P))), $
  a two-sided $Lambda$-ideal of $A$ such that $X_P = X(P)$ for all $P$. For each
  $P$, let $Y(P) =$
  #source(397)
  $X(P)^(-1)$, and define $Y$ analogously. Then $X Y = Y X = Lambda$, since
  these equalities hold at each $P$. Thus $X in I(Lambda)$, and
  $(X) in op("Picent") Lambda$ as desired.

  It remains to verify that $ker tau' subset.eq im tau$, the reverse inclusion
  being obvious. Let $X in I(Lambda)$ be such that $tau' lr((X)) = 1$, that is,
  $(X_P) = 1$ in $op("Picent") Lambda_P$ for each $P$. By
  @cor:central-picard-invertible-ideal-quotient, for each $P$ there exists a
  unit $c_P in c(A_P)$ such that $X_P = Lambda_P c_P$. Further, since
  $X_P = Lambda_P$ a.e., we may choose $c_P = 1$ a.e. Now set
  $
    L = K C inter lr((inter_P C_P c_P)), quad
    L' = K C inter lr((inter_P C_P c_P^(-1))).
  $
  Then $L$ and $L'$ are $C$-lattices in $K C$, with $L_P = C_P c_P$,
  $L'_P = C_P c_P^(-1)$ for each $P$. Then $L L' = C$ since $L_P L'_P = C_P$ for
  each $P$. It follows that $(L) in op("Picent") C$, and $X = L Lambda$ since
  $X_P = L_P Lambda_P$ for each $P$. Thus $(X) in im tau$, as claimed, and the
  theorem is proved.
]

Before going on, let us show that when $Lambda$ is a commutative order, the
group $op("Picent") Lambda$ can be described in more familiar terms:

#theorem[
  Let $Lambda$ be an $R$-order in a f.d. separable commutative $K$-algebra $A$.
  There is a canonical isomorphism of groups
  $ theta: op("Picent") Lambda tilde.equiv op("Cl") Lambda, $
  where $op("Cl") Lambda$ is the locally free class group, defined as in
  §@sec:locally-free-class-groups.
] <th:commutative-central-picard-class-group>
#proof[
  This is _not_ an immediate consequence of
  @th:commutative-invertible-locally-rank-one, because the group structures of
  $op("Picent") Lambda$ and $op("Cl") Lambda$ are different. By
  @cor:central-picard-invertible-ideal-quotient, $op("Picent") Lambda$ consists
  of isomorphism classes $(X)$ of locally free $Lambda$-ideals $X$ in $A$. For
  $(X),(Y) in op("Picent") Lambda$ we have $(X) dot (Y) = (X Y)$, since
  $X times.o_Lambda Y tilde.equiv X Y$ (computed inside $A$); note that
  $op("Picent") Lambda$ is a _multiplicative_ group.

  On the other hand, $op("Cl") Lambda$ is the _additive_ group whose elements
  are stable isomorphism classes $[M]$ of locally free $Lambda$-ideals $M$ in
  $A$. Given $[M],[M'] in op("Cl") Lambda$, we have $[M] + [M'] = [M'']$, where
  $M plus.o M' tilde.equiv Lambda plus.o M''$. Since $Lambda$ is commutative,
  @def:locally-free-cancellation shows that $Lambda$ has locally free
  cancellation, so stable isomorphism coincides with isomorphism. Thus the map
  $theta: op("Picent") Lambda arrow op("Cl") Lambda$, given by $theta(X) = [X]$,
  is a bijection. We must verify that $theta$ is a homomorphism of groups.

  For each $(X) in op("Picent") Lambda$, we may write $X = Lambda alpha$ for
  some idèle $alpha in J(A)$, by §@ss:class-group-basic-formulas. For
  $alpha,beta in J(A)$, we have $Lambda alpha dot Lambda beta = Lambda
  alpha beta$ since $Lambda$ is commutative. On the other hand,
  @eq:idele-lattice-addition gives
  $
    [Lambda alpha] + [Lambda beta] = [Lambda alpha beta]
    quad "in" op("Cl") Lambda.
  $
  It follows that $theta$ is an isomorphism of groups, as claimed. (See also
  @th:locally-free-picard-class-group-homomorphism below.)
]

In particular, we have $op("Picent") R tilde.equiv op("Cl") R$, as already
observed in the discussion following @def:picard-group. More generally, let
$C = c(Lambda)$ be the center of an $R$-order $Lambda$, as
#source(398)
in @th:central-picard-local-global-sequence. Then
$ op("Picent") C tilde.equiv op("Cl") C $
by @th:commutative-central-picard-class-group.

By @th:central-picard-local-global-sequence, the calculation of
$op("Picent") Lambda$ reduces to the following problems:
#enum(
  numbering: "(i)",
  [Determine $op("Picent") C$, that is, the class group $op("Cl") C$. We have
    studied this question in detail in §§@sec:locally-free-class-groups and
    @sec:class-groups-integral-group-rings.],
  [Determine $op("Picent") Lambda_P$ for each $P$. For $Lambda$ an integral
    group ring $R G$, the remarks following
    @cor:local-maximal-order-picard-normalizer show that
    $
      op("Picent") Lambda_P tilde.equiv op("Outcent") Lambda_P
      tilde.equiv N(Lambda_P) slash Lambda_P^times (K_P C)^times,
    $
    where $N(Lambda_P)$ is the normalizer of $Lambda_P$ in $K_P G$.],
  [Find the structure of $op("Picent") Lambda$ as an extension of
    $product_P op("Picent") Lambda_P$ by $op("Picent") C$. Relatively little is
    known in this direction.],
)
Combining our earlier results, we have:

#theorem(title: [Fröhlich @bib:Frohlich1973])[
  Let $R$ be a Dedekind domain with quotient field $K$, and let $Lambda$ be a
  maximal $R$-order in the central simple $K$-algebra $A$. For each maximal
  ideal $P$ of $R$ dividing the discriminant $d(Lambda slash R)$, let $e_P$ be
  the ramification index of the skewfield part of $A_P$ over $K_P$. Then there
  is an exact sequence of abelian groups
  $
    1 arrow op("Cl") R arrow op("Picent") Lambda
    arrow product_(P divides d(Lambda slash R)) ZZ slash e_P ZZ arrow 0.
  $
  If $K$ is a global field, then for each $P$, $e_P$ equals the local index
  $m_P$ of $A$ at $P$.
] <th:maximal-order-central-picard-global-sequence>
#proof[
  In this case $c(Lambda) = R$, and $op("Picent") R tilde.equiv op("Cl") R$. The
  group $I(Lambda)$ is abelian by @i:th:maximal-order-ideal-factorization, so
  $op("Picent") Lambda$ is also abelian. The remaining assertions now follow
  from @th:local-maximal-order-central-picard-cyclic and
  @i:th:division-algebra-maximal-order-valuation(iv).
]

=== Locally Free Picard Groups <ss:locally-free-picard-groups>

Throughout this section, let $Lambda$ be an $R$-order in a f.d. separable
$K$-algebra $A$, where $R$ is a Dedekind domain with quotient field $K$. Here we
shall define the locally free Picard group $op("LFP")(Lambda)$ as a certain
subgroup of $op("Picent") Lambda$, and shall derive its main properties. For
$R = "alg. int." lr({K})$ and $G$ a finite group, we have
$op("LFP")(R G) = op("Picent") R G$. Generally speaking, $op("LFP")$ is easier
to calculate than $op("Picent")$. The results in this section are due to
Fröhlich @bib:Frohlich1973 and Fröhlich–Reiner–Ullom
@bib:FrohlichReinerUllom1974.

#definition[
  A $Lambda$-lattice $M$ is _locally free of rank $n$_ if
  $M_P tilde.equiv Lambda_P^((n))$ as $Lambda_P$-#source(399)modules, for each
  maximal ideal $P$ of $R$ (equivalently, $M$ is in the genus of
  $Lambda^((n))$). Let $op("LF")_n lr((Lambda))$ denote the set of isomorphism
  classes of such $M$’s.
] <def:locally-free-module-isomorphism-classes>
#idx("Locally free", target: [@def:locally-free-module-isomorphism-classes])
#nidx(
  "$op(\"LF\")_n lr((Lambda))$",
  "locally free Λ-modules of rank n",
  target: [@def:locally-free-module-isomorphism-classes],
)

Now let $attach(M, bl: Lambda, br: Delta)$ be an invertible bimodule, where
$Lambda$ and $Delta$ are $R$-orders in $A$. We claim that
$M in op("LF")_1 lr((Lambda))$ if and only if $M in op("LF")_1 lr((Delta))$.
Passing to $P$-adic completions and changing notation briefly, we must show that
$attach(M, bl: Lambda) tilde.equiv Lambda$ implies
$attach(M, br: Delta) tilde.equiv Delta$ (and conversely). Suppose that
$M = Lambda m tilde.equiv Lambda$ for some $m in M$. Since $M$ is invertible, we
obtain
$
  Delta tilde.equiv op("End")_Lambda M
  tilde.equiv op("End")_Lambda Lambda tilde.equiv Lambda,
$
where endomorphisms are right operators as in
@eq:invertible-bimodule-endomorphism-rings. Consequently
$M = m Delta tilde.equiv Delta$. Thus, for invertible bimodules the property of
being locally free does not depend on whether we use the left or right
structure. It also follows readily from the above that if $M$ is invertible and
$M in op("LF")_n lr((Lambda))$, then necessarily $n = 1$.

Suppose next that $M,M'$ are invertible $(Lambda,Lambda)$-bimodules in
$op("LF")_1 lr((Lambda))$. Then also $M^(-1)$ and $M times.o_Lambda M'$ lie in
$op("LF")_1 lr((Lambda))$. We may therefore define the _locally free Picard
group_ $op("LFP")(Lambda)$ as the subgroup of $op("Picent") Lambda$ consisting
of all classes of invertible bimodules $attach(M, bl: Lambda, br: Lambda)$
centralized by $c(Lambda)$, such that
$attach(M, bl: Lambda) in op("LF")_1 lr((Lambda))$ (or equivalently,
$attach(M, br: Lambda) in op("LF")_1 lr((Lambda))$).
#idx("Locally free Picard group")
#nidx("$op(\"LFP\")$", "locally free Picard group")

By @cor:central-picard-invertible-ideal-quotient, each class
$(M) in op("Picent") Lambda$ can be represented by an invertible two-sided
$Lambda$-ideal $M$ in $A$. Let us show at once that any two-sided $Lambda$-ideal
$X$ in $A$, such that $attach(X, bl: Lambda) in op("LF")_1 lr((Lambda))$, is
necessarily invertible. To prove this, it suffices by
@i:prop:invertible-bimodule-localization to check that $X_P$ is invertible for
each $P$. Passing to $P$-adic completions and changing notation for the moment,
$X$ is a $(Lambda,Lambda)$-bimodule such that
$attach(X, bl: Lambda) tilde.equiv attach(Lambda, bl: Lambda)$. It follows that
$X$ is invertible, by @lem:order-normalizer-invertible-principal-ideals. We thus
obtain:

#proposition[
  The locally free Picard group $op("LFP")(Lambda)$ consists of all bimodule
  isomorphism classes $(M)$ of two-sided $Lambda$-ideals $M$ in $A$, which are
  locally free as one-sided ideals. If $M'$ is another such ideal,
  then#footnote[
    This follows from @th:invertible-ideal-central-picard-sequence.
  ] $(M) = (M')$ if and only if $M' = M c$ for some $c in (K C)^times$, where
  $C = c(Lambda)$.
] <prop:locally-free-picard-ideal-description>

If $R$ is a d.v.r., then for any $R$-order $Lambda$, $op("LF")_1 lr((Lambda))$
consists of all free $Lambda$-modules of rank $1$. Hence in this case
$
  op("LFP")(Lambda)
  = lr(
    {(X) in op("Picent") Lambda:
      attach(X, bl: Lambda) tilde.equiv attach(Lambda, bl: Lambda)}
  )
  = lr({(attach(Lambda, bl: 1, br: f)): f in op("Autcent") Lambda})
  = op("Outcent") Lambda,
$
by @th:normalizer-outer-central-automorphisms.

Returning to the situation where $R$ is arbitrary, consider the map
$tau: op("Picent") C arrow op("Picent") Lambda$ defined in
@th:central-picard-local-global-sequence. Since
$ op("Picent") C tilde.equiv op("Cl") C tilde.equiv op("LFP")(C) $
#source(400)
by @th:commutative-central-picard-class-group, it is clear that the image of
$tau$ lies in $op("LFP")(Lambda)$. In view of the preceding remarks,
@th:central-picard-local-global-sequence now gives:

#theorem[
  Let $Lambda$ be an $R$-order (with center $C$) in a f.d. separable $K$-algebra
  $A$. There is an exact sequence of groups
  $
    1 arrow op("Cl") C arrow op("LFP")(Lambda)
    arrow product_P op("Outcent") Lambda_P arrow 1,
  $
  with $op("Outcent") Lambda_P = 1$ a.e. We have
  $
    op("Outcent") Lambda_P tilde.equiv
    N(Lambda_P) slash Lambda_P^times (K_P C)^times quad "for each" P,
  $
  where
  $
    N(Lambda_P) = "normalizer of" Lambda_P
    = lr({a in A_P^times: a Lambda_P a^(-1) = Lambda_P}).
  $
] <th:locally-free-picard-local-global-sequence>

The remarks in §@ss:picard-orders show at once that for each finite group $G$
and $R = "alg. int." lr({K})$,
$
  op("LFP")(R G) tilde.equiv op("Picent") R G, quad "and"
  op("Picent") R_P G tilde.equiv op("Outcent") R_P G
$
<eq:group-ring-locally-free-central-picard>
for each $P$. Thus, @th:locally-free-picard-local-global-sequence gives us a
method of calculating $op("Picent")$ for integral group rings.

Generalizing the results in @th:commutative-central-picard-class-group, we now
establish the connection between $op("LFP")(Lambda)$ and the locally free class
group $op("Cl") Lambda$, for an arbitrary $R$-order $Lambda$. We begin with a
theorem due to Fröhlich–Reiner–Ullom @bib:FrohlichReinerUllom1974:

#theorem[
  Let $Lambda$ be an $R$-order in an f.d. separable $K$-algebra $A$. There is a
  homomorphism of groups
  $ theta: op("LFP")(Lambda) arrow op("Cl") Lambda, $
  given by $theta(X) = [X]$ for each $(X) in op("LFP")(Lambda)$.
] <th:locally-free-picard-class-group-homomorphism>
#idx(
  "Fröhlich-Reiner-Ullom Theorem",
  target: [@th:locally-free-picard-class-group-homomorphism],
)
#proof[
  Let $(X),(Y) in op("LFP")(Lambda)$; without loss of generality, we may assume
  that $X$ is a two-sided ideal of $Lambda$ such that
  $attach(X, bl: Lambda) in op("LF")_1 lr((Lambda))$. There is then an exact
  sequence of $(Lambda,Lambda)$-bimodules
  $ 0 arrow X arrow Lambda arrow T arrow 0, $
  with $T$ an $R$-torsion bimodule. Since $Y in op("LF")_1 lr((Lambda))$, the
  functor $ast times.o_Lambda Y$ preserves exactness, and we obtain another
  exact sequence of bimodules:
  $ 0 arrow X times.o Y arrow Y arrow T times.o Y arrow 0, $
  where $times.o$ means $times.o_Lambda$. But $T times.o Y$ is direct sum of its
  $P$-primary components,
  #source(401)
  where $P$ ranges over the maximal ideals of $R$. Since
  $Y_P tilde.equiv Lambda_P$ as left $Lambda_P$-modules for each $P$, it follows
  that $T times.o Y tilde.equiv T$ as left $Lambda$-modules. Schanuel’s Lemma
  thus gives a left $Lambda$-isomorphism
  $ X plus.o Y tilde.equiv Lambda plus.o (X times.o Y). $
  In view of the definition of addition in $op("Cl") Lambda$, we obtain
  $ [X] + [Y] = [X times.o_Lambda Y] quad "in" op("Cl") Lambda. $
  Thus $theta$ is a homomorphism, as claimed.
]

Keeping the above notation, let $X$ be a two-sided $Lambda$-ideal in $A$, such
that $attach(X, bl: Lambda) in op("LF")_1 lr((Lambda))$. Then for each $P$, we
may write $X_P = Lambda_P x_P$, and by
@lem:order-normalizer-invertible-principal-ideals the element $x_P$ must lie in
the normalizer
$ N(Lambda_P) = lr({y in A_P^times: y Lambda_P y^(-1) = Lambda_P}). $
Further, $x_P in Lambda_P^times$ a.e., so $x = (x_P)$ lies in the idèle group
$J(A)$. We have $X = Lambda x$, where the latter is defined as in
@eq:idele-lattice-intersection, namely,
$ Lambda x = A inter lr({inter_P Lambda_P x_P}). $
The above discussion suggests that we introduce the _idèle normalizer_ of
$Lambda$, defined by
$
  J N(Lambda) = lr(
    {(x_P) in J(A): x_P in N(Lambda_P)
      "for each" P}
  ).
$
<eq:idele-normalizer>
#idx("Idele normalizer", target: [@eq:idele-normalizer])
Then each class of $op("LFP")(Lambda)$ is of the form $(Lambda x)$ for some
$x in J N(Lambda)$. The homomorphism $theta$, defined above, carries
$(Lambda x)$ onto $[Lambda x] in op("Cl") Lambda$. We note further that for
$x,y in J N(Lambda)$ we have
$
  Lambda x times.o_Lambda Lambda y tilde.equiv
  Lambda x dot Lambda y = Lambda x y,
$
since $Lambda x = x Lambda$ (check $P$-adic completions!). Further,
$Lambda x tilde.equiv Lambda y$ if and only if $Lambda x = Lambda y dot c$ for
some $c in (K C)^times$, that is, $x in U(Lambda) y (K C)^times$. It follows
that there is a surjective homomorphism $J N(Lambda) arrow op("LFP")(Lambda)$,
given by $x mapsto (Lambda x)$, with kernel $U(Lambda)(K C)^times$. This gives
$
  op("LFP")(Lambda) tilde.equiv
  J N(Lambda) slash U(Lambda)(K C)^times.
$
<eq:locally-free-picard-idele-normalizer-quotient>

We now return to the homomorphism
$theta: op("LFP")(Lambda) arrow op("Cl") Lambda$ defined in
@th:locally-free-picard-class-group-homomorphism, and we shall describe its
kernel and cokernel under some simplifying hypotheses.

#theorem[
  Let $Lambda$ be an $R$-order in a f.d. separable $K$-algebra $A$, where
  #source(402)
  $K$ is a global field. Assume that $Lambda$ has locally free cancellation.
  Then there is an exact sequence of groups
  $
    1 arrow op("Outcent") Lambda arrow^omega op("LFP")(Lambda)
    arrow^theta op("Cl") Lambda arrow op("cok") theta arrow 1,
  $
  where (using the notation in @th:class-group-idele-quotient)
  $ op("cok") theta tilde.equiv J(A) slash J_0 lr((A)) A^times J N(Lambda). $
] <th:locally-free-picard-class-group-kernel-cokernel>
#proof[
  Let $(X) in op("LFP")(Lambda)$ be such that $theta(X) = 0$, that is,
  $[X] = [Lambda]$ in $op("Cl") Lambda$. Then $X tilde.equiv Lambda$ as left
  $Lambda$-modules, since $Lambda$ has locally free cancellation by hypothesis.
  Therefore $(X) in im omega$ by
  @th:normalizer-outer-central-automorphisms(iii). Since $theta omega = 0$, it
  follows that $ker theta = im omega$.

  We next use the formula @th:class-group-idele-quotient
  $ op("Cl") Lambda tilde.equiv J(A) slash J_0 lr((A)) A^times U(Lambda), $
  where $U(Lambda)$ is the group of unit idèles, and
  $J_0 lr((A)) = lr({alpha in J(A): op("nr") alpha = 1})$. The image of
  $op("LFP")(Lambda)$ in this group consists of the classes containing elements
  of the idèle normalizer $J N(Lambda)$, defined by @eq:idele-normalizer. Since
  $J N(Lambda) supset.eq U(Lambda)$, we obtain the desired formula for
  $op("cok") theta$.
]

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [If $Lambda$ is a commutative order, it has locally free cancellation by the
      discussion in @def:locally-free-cancellation. Further, in this case
      $op("Outcent") Lambda = 1$ and $J N(Lambda) = J(A)$, so
      @th:locally-free-picard-class-group-kernel-cokernel implies that $theta$
      is an isomorphism. We have already proved this in
      @th:commutative-central-picard-class-group, without the restrictive
      hypothesis that $K$ be a global field.],
    [The formula for $op("cok") theta$, in terms of idèles, is valid whether or
      not $Lambda$ has locally free cancellation. Further, taking reduced norms,
      we obtain
      $
        op("cok") theta tilde.equiv
        J(K C) slash (K C)^+ dot op("nr") J N(Lambda).
      $
      For an ideal-theoretic version of this formula, see Fröhlich–Reiner–Ullom
      @bib:FrohlichReinerUllom1974, Theorem 5.13.],
  )
] <rem:locally-free-picard-class-group-cokernel-norms>

We now compute $op("cok") theta$ for the case where $Lambda$ is a maximal order,
again keeping the hypotheses of
@th:locally-free-picard-class-group-kernel-cokernel. It suffices to treat the
case where $A$ is simple, and we begin by fixing the notation. Let $A$ be a
central simple $K$-algebra, where $K$ is a global field, and set
$dim_K A = n^2$. Let $Lambda$ be a maximal $R$-order in $A$, so by
@th:maximal-order-restricted-ideal-class-group there is an isomorphism
$ op("Cl") Lambda tilde.equiv op("Cl")_A R = I(R) slash P_A lr((R)). $
The isomorphism may be described thus: each element of $op("Cl") Lambda$ is of
the form $Lambda alpha$, with $alpha = (alpha_P) in J(A)$. Then $Lambda alpha$
is a left $Lambda$-ideal in $A$, whose reduced norm
#source(403)
$op("nr")(Lambda alpha)$ is an $R$-ideal in $K$. For each maximal ideal $P$ of
$R$, we have
$
  (op("nr") Lambda alpha)_P = op("nr") Lambda_P alpha_P
  = R_P op("nr") alpha_P
$
(see @bib:Reiner1975[MO] (24.11)). Viewing $op("nr") alpha$ as element of the
idèle group $J(K)$, we obtain
$
  op("nr") Lambda alpha = R op("nr") alpha
  = K inter lr({inter_P R_P op("nr") alpha_P}).
$
The isomorphism $op("Cl") Lambda tilde.equiv op("Cl")_A R$ carries
$[Lambda alpha]$ onto the class of $R op("nr") alpha$ in $op("Cl")_A R$.

We now define a homomorphism
$
  t_n: op("Cl") R arrow op("Cl")_A R, quad "by"
  t_n lr((frak(a))) = (frak(a)^n)
$
for each $R$-ideal $frak(a)$ in $K$. In order for the map to be well-defined, we
must have $R a^n in P_A lr((R))$ for each $a in K^times$. If no infinite prime
of $K$ ramifies in $A$, then $P_A lr((R)) = P(R)$. On the other hand, if some
infinite prime of $K$ does ramify in $A$, then $n$ must be even. In either case,
we conclude that $R a^n in P_A lr((R))$, so $t_n$ is a well-defined
homomorphism.

Before stating our results, we need one more definition, already encountered in
@eq:division-algebra-local-index. For each prime $P$ of $K$, we may write
$
  A_P tilde.equiv M_(kappa_P) lr((Omega(P))), quad
  dim_(K_P) Omega(P) = m_P^2, quad m_P kappa_P = n,
$
where $Omega(P)$ is a skewfield with center $K_P$ and index $m_P$. We call $m_P$
the _local index_ of $A$ at $P$, and $kappa_P$ the _local capacity_. We now
prove:

#theorem[
  Let $Lambda$ be a maximal $R$-order in a central simple $K$-algebra $A$, where
  $K$ is a global field and $A$ is not a totally definite quaternion algebra.
  Keeping the above notation, there is an exact sequence of groups
  $
    1 arrow ker t_n arrow ker theta arrow product_P ZZ slash m_P ZZ
    arrow op("cok") t_n arrow op("cok") theta arrow 1,
  $
  <eq:maximal-order-picard-class-kernel-cokernel-sequence>
  where $theta: op("LFP")(Lambda) arrow op("Cl") Lambda$ is as in
  @th:locally-free-picard-class-group-homomorphism.

  Further, let $V$ be the subgroup of the class group $op("Cl")_A R$ generated
  by all $lr({P^(kappa_P): m_P > 1})$. Then
  $
    op("cok") theta tilde.equiv
    (op("Cl")_A R) / (t_n lr((op("Cl") R)) dot V).
  $
  <eq:maximal-order-picard-class-cokernel>
] <th:maximal-order-picard-class-kernel-cokernel>
#proof[
  By the proof of @th:local-maximal-order-central-picard-cyclic, we know that
  $op("Picent") Lambda_P tilde.equiv ZZ slash m_P ZZ$ (see also
  @th:maximal-order-central-picard-global-sequence), and that
  $op("Picent") Lambda_P$ is generated by the class $(op("rad") Lambda_P)$.
  Further, the proof of @th:local-maximal-order-central-picard-cyclic shows that
  $op("Picent") Lambda = op("LFP")(Lambda)$, since each invertible
  $(Lambda,Lambda)$-bimodule must be locally free. We claim next that there is a
  commutative diagram with
  #source(404)
  exact rows:
  #maximal-order-picard-class-snake
  The top row is given by @th:maximal-order-central-picard-global-sequence, and
  $sigma$ is the inverse of the isomorphism
  $op("Cl") Lambda tilde.equiv op("Cl")_A R$ coming from the reduced norm map.
  To check commutativity, let $frak(a)$ be an ideal of $R$. Its image in
  $op("LFP")(Lambda)$ is then $(Lambda frak(a))$, which maps to
  $[Lambda frak(a)] in op("Cl") Lambda$. Then
  $
    sigma^(-1)[Lambda frak(a)] = (op("nr") Lambda frak(a))
    = (frak(a)^n) = t_n lr((frak(a))),
  $
  so the left-hand square commutes. The exact sequence
  @eq:maximal-order-picard-class-kernel-cokernel-sequence now comes from the
  Snake Lemma.

  It remains to check the formula for $op("cok") theta$, and for this we must
  compute the image of $product_P ZZ slash m_P ZZ$ in $op("cok") t_n$. Now
  $ZZ slash m_P ZZ tilde.equiv op("Picent") Lambda_P$, and
  $op("Picent") Lambda_P$ is a cyclic group of order $m_P$ with generator
  $(op("rad") Lambda_P)$. Since $op("nr")(op("rad") Lambda_P) = P^(kappa_P)$
  (see @bib:Reiner1975[MO] (25.11)), the image of $ZZ slash m_P ZZ$ in
  $op("cok") t_n$ is the group generated by the class of $P^(kappa_P)$. This
  gives formula @eq:maximal-order-picard-class-cokernel at once.
]

It should be remarked that in formula @eq:maximal-order-picard-class-cokernel,
we may replace $V$ by the group $tilde(V)$ generated by all
$lr({P^(kappa_P): P "arbitrary"})$. For if $P$ is such that $m_P = 1$, then
necessarily $kappa_P = n$, and so $P^(kappa_P) in im t_n$.

We have seen in @th:picard-morita-invariance that Morita equivalent rings have
isomorphic Picard groups. On the other hand, if $Lambda$ is an $R$-order and
$Gamma = M_n lr((Lambda))$, then by §@sec:locally-free-class-groups we have
$op("Cl") Lambda tilde.equiv op("Cl") Gamma$. It is of interest to combine these
facts with the sequence in @th:locally-free-picard-class-group-kernel-cokernel
relating Picard groups and class groups. The results below are due to
Fröhlich–Reiner–Ullom @bib:FrohlichReinerUllom1974:

#theorem[
  Let $Lambda$ be an $R$-order in a f.d. separable $K$-algebra $A$, where $K$ is
  a global field, and where $Lambda$ has locally free cancellation. Let $n >= 1$
  and set $E = M_n lr((R))$, and
  $ Gamma = E times.o_R Lambda tilde.equiv M_n lr((Lambda)). $
  Then $Gamma$ also has locally free cancellation, and we have:
  #enum(
    numbering: "(i)",
    [There is a commutative diagram with exact rows
      #matrix-order-picard-class-comparison
      #source(405)
      where $alpha(f) = 1 times.o f$ for $f in op("Outcent") Lambda$, and where
      $beta$ and $gamma$ are given by the “change of rings” functor
      $E times.o_R ast$. The map $beta$ is an isomorphism.],
    [For the above map $gamma: op("Cl") Lambda arrow op("Cl") Gamma$, we have
      $
        ker gamma tilde.equiv (op("Cl") Lambda)_n, quad
        op("cok") gamma tilde.equiv
        (op("Cl") Lambda) slash (n dot op("Cl") Lambda),
      $
      where
      $
        (op("Cl") Lambda)_n = lr({xi in op("Cl") Lambda: n xi = 0}), quad
        n dot op("Cl") Lambda = lr({n xi: xi in op("Cl") Lambda}).
      $],
    [There is an exact sequence of groups
      $
        1 arrow op("Outcent") Lambda arrow^alpha op("Outcent") Gamma
        arrow^mu (op("Cl") Lambda)_n arrow op("cok") theta
        arrow op("cok") theta' \
        arrow
        (op("Cl") Lambda) slash (n dot op("Cl") Lambda) arrow 0.
      $],
  )
] <th:matrix-order-picard-class-comparison>
#idx(
  "Fröhlich-Reiner-Ullom Theorem",
  target: [@th:matrix-order-picard-class-comparison],
)
#proof[
  It will be convenient to identify $op("Cl") Lambda$ with a subgroup of
  $S K_0 lr((Lambda))$ as in @eq:class-group-localization-kernel-isomorphism.
  Thus
  $ op("Cl") Lambda = lr({[Lambda] - [M]: M in g(Lambda)}). $
  The Morita equivalence $Lambda tilde Gamma$ gives an isomorphism
  $phi: op("Cl") Lambda tilde.equiv op("Cl") Gamma$, which we may describe as
  follows. Let $L = R^((n)) times.o_R Lambda$, a $(Gamma,Lambda)$-bimodule
  giving a Morita equivalence between the orders $Lambda$ and $Gamma$. To each
  left $Lambda$-module $X$ there corresponds a left $Gamma$-module
  $L times.o_Lambda X$, and this correspondence is bijective on isomorphism
  classes. There is an isomorphism
  $phi: K_0 lr((Lambda)) tilde.equiv K_0 lr((Gamma))$, given by
  $[X] mapsto [L times.o_Lambda X]$ for $X in cal(P)(Lambda)$. Then $phi$
  induces an isomorphism $op("Cl") Lambda tilde.equiv op("Cl") Gamma$, again
  denoted by $phi$, and we have (for $M in g(Lambda)$)
  $
    phi([Lambda] - [M]) & = [L times.o_Lambda Lambda] - [L times.o_Lambda M] \
                        & = [L times.o_Lambda Lambda^((n))]
                          - [L times.o_Lambda (Lambda^((n-1)) plus.o M)].
  $
  Since $Gamma tilde.equiv L^((n)) tilde.equiv
  L times.o_Lambda Lambda^((n))$ as left $Gamma$-modules, we obtain
  $
    phi([Lambda] - [M]) = [Gamma]
    - [L times.o_Lambda (Lambda^((n-1)) plus.o M)] in op("Cl") Gamma.
  $
  The above formula exhibits $phi([Lambda] - [M])$ as a difference of locally
  free left ideals of $Gamma$. It follows readily from the above that if
  $Lambda$ has locally free cancellation, then so does $Gamma$. (The converse
  may be false, however! See @prop:eichler-condition-sufficient-cases and
  @th:jacobinski-cancellation.)

  We now write $Gamma = E times.o_R Lambda$; if $C = "center of" Lambda$, then
  $1 times.o C = "center of" Gamma$. By Exercise
  @exc:morita-central-picard-equivalence, there is an isomorphism
  $op("Pic")_R Lambda tilde.equiv op("Pic")_R Gamma$, given by
  $(X) mapsto (E times.o_R X)$ for $(X) in op("Pic")_R Lambda$. This induces an
  isomorphism $op("Picent") Lambda tilde.equiv op("Picent") Gamma$, which
  commutes with taking $P$-adic completion for $P$ a maximal ideal of $R$. It
  follows that there is an isomorphism
  $beta: op("LFP")(Lambda) tilde.equiv op("LFP")(Gamma)$, induced by the functor
  $Gamma times.o_Lambda ast$, or equivalently, by $E times.o_R ast$. The
  remaining assertions in (i) above are obvious from
  @th:locally-free-picard-class-group-kernel-cokernel.

  #source(406)
  Now let $phi: op("Cl") Lambda tilde.equiv op("Cl") Gamma$ be as above, and let
  $gamma: op("Cl") Lambda arrow op("Cl") Gamma$ be the map given by
  $Gamma times.o_Lambda ast$. Then $gamma = n phi$ by Exercise
  @exc:matrix-morita-class-group-multiplication, and the assertions in (ii) are
  clear. It remains to establish the exactness of the sequence in (iii). For
  this purpose, consider the commutative diagram with exact rows:
  #matrix-order-picard-class-snake
  The Snake Lemma gives
  $
    1 arrow ker theta arrow ker theta' arrow ker gamma
    arrow op("cok") theta arrow^(gamma_*) op("cok") theta',
  $
  where $gamma$ induces $gamma_*$. Then
  $
    op("cok") gamma_*
    = frac(
      frac(op("Cl") Gamma, im theta'),
      gamma_* lr({(op("Cl") Lambda) slash im theta}),
    )
    tilde.equiv (op("Cl") Gamma) / (gamma(op("Cl") Lambda))
    = op("cok") gamma,
  $
  which completes the proof of (iii) and the theorem.
]

As an immediate consequence of the above theorem, we see that the group
$op("Outcent") Gamma slash im(op("Outcent") Lambda)$ has exponent dividing $n$.
Thus we obtain:

#corollary[
  Keep the notation and hypotheses of @th:matrix-order-picard-class-comparison,
  so $Gamma = M_n lr((Lambda))$. Then
  #enum(
    numbering: "(i)",
    [For each $f in op("Autcent") Gamma$, we have $f^n = (1 times.o g) eta$ for
      some $g in op("Autcent") Lambda$ and some inner automorphism $eta$ of
      $Gamma$.],
    [For $Lambda$ a commutative $R$-order, we have
      $ op("Outcent") M_n lr((Lambda)) tilde.equiv (op("Cl") Lambda)_n. $],
  )
  Thus, for commutative $Lambda$ and each $f in op("Autcent") M_n lr((Lambda))$,
  $f^n$ is an inner automorphism of $M_n lr((Lambda))$.
] <cor:matrix-order-outer-automorphism-exponent>
#proof[
  Assertion (i) is clear. For (ii), use
  @th:matrix-order-picard-class-comparison(iii) together with the facts that
  $op("Outcent") Lambda = 0$ and that $theta$ is an isomorphism.
]

As a special case of @cor:matrix-order-outer-automorphism-exponent(ii), we
obtain
$ op("Out")_R M_n lr((R)) tilde.equiv (op("Cl") R)_n, $
a result due originally to Rosenberg–Zelinsky @bib:RosenbergZelinsky1961.

#source(407)
=== Radical Reduction <ss:picard-radical-reduction>

The results in this section are all due to Fröhlich @bib:Frohlich1973. Let
$Lambda$ be an $R$-algebra, where $R$ is a commutative ring, and let
$J = op("rad") Lambda$. Our aim here is to compare $op("Pic")_R Lambda$ with
$op("Pic")_R Lambda slash J^m$, for $m >= 1$. We assume throughout that $Lambda$
is a semilocal ring, that is, $Lambda slash J$ is a semisimple artinian ring.
(This is surely the case if $Lambda$ is a f.d. algebra over a field, or an
algebra over a d.v.r., finitely generated as module; see §@i:sec:radicals.) By
Exercises @exc:invertible-bimodule-characteristic-ideal and
@exc:invertible-bimodule-quotient, for each $(X) in op("Pic")_R Lambda$,
$X slash J^m X$ is an invertible bimodule over $Lambda slash J^m$, so “reduction
mod $J^m$” gives a homomorphism
$ rho: op("Pic")_R Lambda arrow op("Pic")_R Lambda slash J^m. $
To determine $ker rho$, we use two facts repeatedly: first, for $m >= 1$, the
map $Lambda^times arrow (Lambda slash J^m)^times$ is surjective, by
@lem:semilocal-quotient-unit-surjectivity; second, by Nakayama’s Lemma, a
homomorphism between finitely generated projective $Lambda$-modules which is an
isomorphism mod $J^m$ is itself an isomorphism.

For each $f in op("Aut")_R Lambda$, $f(J^m) = J^m$ for $m >= 1$, so $f$ induces
$overline(f) in op("Aut")_R Lambda slash J^m$. Let us define a relative
automorphism group
$
  op("Aut")_R lr((Lambda,J^m)) = lr(
    {f in op("Aut")_R Lambda:
      overline(f) = 1 "on" Lambda slash J^m}
  ).
$
As in @th:outer-automorphism-picard-embedding, there is a homomorphism
$
  omega: op("Aut")_R lr((Lambda,J^m)) arrow op("Pic")_R Lambda, quad
  "given by" omega(f) = (attach(Lambda, bl: 1, br: f)),
$
and $ker omega = (op("In") Lambda) inter op("Aut")_R lr((Lambda,J^m))$. We now
prove:

#theorem(title: [Fröhlich])[
  Let $Lambda$ be a semilocal $R$-algebra, and let $J = op("rad") Lambda$. For
  $m >= 1$, there is an exact sequence of groups
  $
    op("Aut")_R lr((Lambda,J^m)) arrow^omega op("Pic")_R Lambda
    arrow^rho op("Pic")_R Lambda slash J^m.
  $
  Further, if $m >= 2$ and $J^(m+1) = 0$, the sequence
  $
    H^1 lr((Lambda slash J^2,J^m)) arrow op("Pic")_R Lambda
    arrow op("Pic")_R Lambda slash J^m
  $
  is exact.
] <th:semilocal-picard-radical-reduction>
#proof[
  It is obvious that $rho omega = 1$. Now let $(X) in op("Pic")_R Lambda$ be
  such that $rho(X) = 1$, so there is a bimodule isomorphism
  $phi: overline(X) tilde.equiv overline(Lambda)$, where bars indicate reduction
  mod $J^m$. We may lift $phi$ to a left $Lambda$-homomorphism
  $f: X arrow Lambda$; since $f("mod" J^m) = phi$, $f$ is an isomorphism
  $X tilde.equiv Lambda$. By @th:picard-one-sided-isomorphism-cosets we conclude
  that $X tilde.equiv attach(Lambda, bl: 1, br: g)$ as bimodules, for some
  $g in op("Aut")_R Lambda$. Then
  $attach(overline(Lambda), bl: 1, br: overline(g)) tilde.equiv
  overline(Lambda)$ as $overline(Lambda)$-bimodules, so by
  @th:outer-automorphism-picard-embedding $overline(g)$ is an inner automorphism
  of $overline(Lambda)$. Hence there exists $u in Lambda^times$ such that
  $overline(g) = (i_(overline(u)))^(-1)$. But then in $op("Pic")_R Lambda$ we
  have
  $
    (X) = (attach(Lambda, bl: 1, br: g))
    = (attach(Lambda, bl: 1, br: i_u g)) = omega(i_u g)
  $
  and $i_u g in op("Aut")_R lr((Lambda,J^m))$. This proves the exactness of the
  first sequence.

  #source(408)
  Now let $m >= 2$ and assume that $J^(m+1) = 0$. By definition (see Volume I,
  @i:eq:bimodule-first-cohomology), the cohomology group $H^1$ is given by
  $
    H^1 lr((Lambda slash J^2,J^m))
    = op("Der")_R lr((Lambda slash J^2,J^m)) slash "inner derivations".
  $
  The numerator is the $R$-module consisting of all derivations
  $d: Lambda slash J^2 arrow J^m$, that is, all $R$-linear maps $d$ such that
  $ d(x y) = x d y + (d x) y quad "for" x,y in Lambda slash J^2. $
  The inner derivations are those given by $d(x) = x b - b x$,
  $x in Lambda slash J^2$, for some $b in J^m$. But $J^(m+1) = 0$, so for each
  $d in op("Der")_R lr((Lambda,J^m))$ we have $d(J^2) = 0$, and thus
  $ op("Der")_R lr((Lambda,J^m)) = op("Der")_R lr((Lambda slash J^2,J^m)) $
  in this case.

  We note next that there is an $R$-isomorphism
  $
    op("Der")_R lr((Lambda slash J^2,J^m))
    tilde.equiv op("Aut")_R lr((Lambda,J^m)),
  $
  in which the derivation $d$ corresponds to the automorphism $f$, where
  $ f(lambda) = lambda + d lambda quad "for" lambda in Lambda. $
  (It is easily checked that $f$ is an automorphism if and only if $d$ is a
  derivation.) Further, if $d$ is an inner derivation, say
  $d lambda = lambda b - b lambda$ for all $lambda in Lambda$, then
  $
    f(lambda) = lambda + lambda b - b lambda
    = (1 + b)^(-1) lambda (1+b) quad "for" lambda in Lambda,
  $
  so $f$ is inner. It follows that there is a homomorphism from
  $H^1 lr((Lambda slash J^2,J^m))$ into $op("Pic")_R Lambda$, whose image is
  precisely $ker rho$. This completes the proof.
]
#idx("Fröhlich's Theorem", target: [@th:semilocal-picard-radical-reduction])

#corollary[
  Keep the above notation and hypotheses, and suppose that
  $c(Lambda) arrow c(Lambda slash J)$ is surjective. Then so is
  $ op("Autcent") Lambda arrow op("Picent") Lambda. $
] <cor:semilocal-central-picard-automorphism-surjection>
#proof[
  Put $C = c(Lambda)$, $S = Lambda slash J$, and let
  $(X) in op("Picent") Lambda$. Since $C arrow c(S)$ is surjective, the
  invertible $S$-bimodule $X slash J X$ preserves every central simple component
  $S_i = M_(n_i) lr((D_i))$ of $S$. Write its left $S_i$-module as
  $V_i^((r_i))$, where $V_i$ is simple. Invertibility identifies its
  endomorphism ring, with ordinary composition, with $S_i^"op"$. Comparing
  matrix capacities gives $r_i = n_i$, so $X slash J X tilde.equiv S$ as left
  modules.#ed-note[
    The original proof appeals to triviality of $op("Picent") S$. The
    finite-dimensional hypothesis used in @th:semisimple-central-picard-trivial
    is absent here.
  ] Lift a left generator to a homomorphism $Lambda arrow X$. Nakayama’s Lemma
  makes it surjective, and projectivity of $X$ splits it. Its finitely generated
  kernel has zero reduction modulo $J$, hence is zero. Therefore
  $X tilde.equiv Lambda$ as left modules. By
  @th:picard-one-sided-isomorphism-cosets, $X$ is a twist by an automorphism of
  $Lambda$, and centrality of $X$ makes that automorphism fix $C$. This proves
  the required surjectivity.
]

#corollary[
  Let $Lambda$ be a finite ring. Then
  #enum(numbering: "(i)", [$op("Pic") Lambda$ is finite.], [Let
    $J = op("rad") Lambda$, and let
    $rho: op("Pic") Lambda arrow op("Pic") Lambda slash J^2$ be the map defined
    in @th:semilocal-picard-radical-reduction, given by reduction mod $J^2$. If
    $Lambda$ is $p$-torsion for some prime $p$, then $ker rho$ is a finite
    $p$-group.])
] <cor:finite-ring-picard-radical-primary-kernel>
#source(409)
#proof[
  By @th:picard-center-automorphism-sequence, there is an exact sequence
  $
    1 arrow op("Picent") Lambda slash J arrow op("Pic") Lambda slash J
    arrow op("Aut") c(Lambda slash J).
  $
  But $op("Picent") Lambda slash J = 1$ since $Lambda slash J$ is a semisimple
  artinian ring. Therefore $op("Pic") Lambda slash J$ is finite.

  Taking $R = ZZ$ in @th:semilocal-picard-radical-reduction, we obtain an exact
  sequence
  $
    op("Aut") lr((Lambda,J)) arrow op("Pic") Lambda
    arrow op("Pic") Lambda slash J.
  $
  It follows that $op("Pic") Lambda$ is finite, as claimed.

  Now assume that $Lambda$ is $p$-torsion, so $p^k Lambda = 0$ for some $k > 0$.
  For $n >= 2$, let
  $
    L_n = ker lr({op("Pic") Lambda slash J^n arrow op("Pic") Lambda slash J^2}),
  $
  so $L_2 = lr({1})$, and $L_n = ker rho$ for large $n$. To show that $L_n$ is a
  $p$-group, use induction on $n$. Let $n > 2$, and suppose that $L_(n-1)$ is a
  $p$-group. There is a commutative diagram
  #finite-ring-picard-radical-triangle
  so $mu: L_n arrow L_(n-1)$. We now apply the second part of
  @th:semilocal-picard-radical-reduction, with $Lambda$ replaced by
  $Lambda slash J^n$, $J$ replaced by
  $J slash J^n = op("rad") Lambda slash J^n$, and $J^m$ replaced by
  $J^(n-1) slash J^n$. We obtain an exact sequence
  $
    H^1 lr((Lambda slash J^2,J^(n-1) slash J^n)) arrow
    op("Pic") Lambda slash J^n
    arrow^mu op("Pic") Lambda slash J^(n-1).
  $
  Therefore $ker(L_n arrow L_(n-1)) subset.eq im H^1$; but $Lambda slash J^2$ is
  $p$-torsion, whence so is $im(H^1)$, which shows that $L_n$ is a $p$-group.
  This completes the proof.
]

For the remainder of this section, let $R$ be a d.v.r. with maximal ideal
$P = pi R$, and quotient field $K$. Let $Lambda$ be an $R$-order in a f.d.
separable $K$-algebra $A$, and let $C = c(Lambda)$ be the center of $Lambda$. We
wish to study the behavior of $op("Picent") Lambda$ under reduction mod $P^m$
for sufficiently large $m$. For $m >= 1$, there is a homomorphism
$
  op("Picent") Lambda arrow op("Pic")_R Lambda slash P^m, quad
  "given by" (X) mapsto (X slash P^m X).
$
We intend to prove that this map is injective for large $m$. Some notation is
#source(410)
required in order to state the result. For $(X) in op("Picent") Lambda$ and
$m >= 1$, define
$ T^m lr((X)) = lr({x in X: x a - a x in P^m X "for all" a in Lambda}), $
$ X^Lambda = lr({x in X: x a = a x "for all" a in Lambda}). $
Then $X^Lambda$ is a $C$-submodule of $T^m lr((X))$. Note that
$Lambda^Lambda = C$, and $C subset.eq T^m lr((Lambda))$.

The main result is as follows:

#theorem[
  Let $(X) in op("Picent") Lambda$. Then
  $ T^n lr((X)) subset.eq X^Lambda + P X $
  <eq:approximate-centralizer-bound>
  for all sufficiently large $n$. For each such $n$, the homomorphism
  $ op("Picent") Lambda arrow op("Pic")_R Lambda slash P^n Lambda $
  is injective.
] <th:order-central-picard-finite-reduction-injective>
#proof[
  _Step 1._ Since $A$ is a f.d. separable $K$-algebra, there is a nonzero ideal
  $i(Lambda)$ of $R$ with the property that
  $ i(Lambda) dot H^1 lr((Lambda,X)) = 0 $
  for each $(Lambda,Lambda)$-bimodule $X$. Here, $H^1$ is a cohomology group,
  defined as in @i:eq:bimodule-first-cohomology. The largest ideal $i(Lambda)$
  with this property is called the _Higman ideal_ of $Lambda$; see Volume I,
  §@i:ss:ext-annihilator-higman-ideal, or @bib:CurtisReiner1962[CR] (75.11). It
  follows that there exists an integer $e >= 0$ such that
  $ pi^e H^1 lr((Lambda,X)) = 0 quad "for all" X. $
  Let us show that
  $ T^(m+e) lr((X)) subset.eq X^Lambda + P^m X quad "for" m >= 1, $
  <eq:approximate-centralizer-higman-bound>
  which will imply @eq:approximate-centralizer-bound for all $n >= e+1$. Fix
  $x in T^(m+e) lr((X))$; then for each $a in Lambda$, we may write
  $ x a - a x = pi^(m+e) d(a), quad "where" d(a) in X. $
  This equation uniquely determines $d(a)$, since $X$ is $R$-torsionfree. It is
  easily checked that the map $d: Lambda arrow X$ is a derivation (see
  @i:eq:bimodule-derivation), and thus determines a cohomology class in
  $H^1 lr((Lambda,X))$. Then $pi^e d$ is an inner derivation, so there exists an
  element $y in X$ such that
  $ pi^e d(a) = y a - a y quad "for all" a in Lambda. $
  #source(411)
  Therefore
  $ x a - a x = pi^m lr((y a - a y)) quad "for all" a in Lambda, $
  which proves that $x - pi^m y in X^Lambda$. This establishes
  @eq:approximate-centralizer-higman-bound, as well as
  @eq:approximate-centralizer-bound for $n >= e+1$.

  _Step 2._ Now let $n >= 1$ be such that @eq:approximate-centralizer-bound
  holds, and let $(X) in op("Picent") Lambda$. We write
  $
    X_n = X slash P^n X, quad Lambda_n = Lambda slash P^n Lambda,
    quad R_n = R slash P^n.
  $
  We must show that if $(X_n) = 1$ in $op("Pic")_R Lambda_n$, then $(X) = 1$ in
  $op("Picent") Lambda$. Without loss of generality, we may assume that $X$ is
  an invertible two-sided $Lambda$-ideal in $A$, and that $K X = A$.

  Since $(X_n) = 1$ in $op("Pic")_R Lambda_n$, there is a bimodule isomorphism
  $theta: X_n tilde.equiv Lambda_n$ which commutes with the action of $R$. It
  follows that $theta$ maps $pi X_n$ isomorphically onto $pi Lambda_n$, and also
  that $theta$ gives an isomorphism
  $ T^n lr((X)) slash P^n X tilde.equiv T^n lr((Lambda)) slash P^n Lambda. $
  Now consider the commutative diagram with exact rows
  #approximate-centralizer-reduction-comparison
  Then $theta_1$ and $theta_2$ are isomorphisms, whence so is $theta_3$.

  By @eq:approximate-centralizer-bound we have (since
  $X^Lambda subset.eq T^n lr((X))$)
  $ T^n lr((X)) + P X = X^Lambda + P X = (X inter K C) + P X, $
  and therefore
  $
    lr({T^n lr((X)) + P X}) slash P X tilde.equiv
    X^Lambda slash (X^Lambda inter P X).
  $
  But $X^Lambda = X inter K C$, which is an $R$-pure $C$-submodule of $X$, and
  therefore $X^Lambda inter P X = P X^Lambda$. Thus $theta_3$ gives an
  isomorphism (of $C$-modules)
  $
    X^Lambda slash P X^Lambda tilde.equiv
    Lambda^Lambda slash P Lambda^Lambda = C slash P C.
  $
  It follows from @i:th:dvr-projectivity-reduction that $X^Lambda$ is projective
  as $C$-module, and then $X^Lambda tilde.equiv C$ by
  @i:prop:projective-isomorphism-modulo-radical.

  #source(412)
  _Step 3._ There is a $(Lambda,Lambda)$-bimodule homomorphism
  $
    psi: X^Lambda times.o_C Lambda arrow X, quad
    "given by" x times.o a mapsto x a quad "for" x in X^Lambda,
    a in Lambda.
  $
  We shall show that $psi$ is a surjection. Since $X^Lambda times.o Lambda$ and
  $X$ are $R$-lattices of the same $R$-rank, it will then follow that $psi$ is
  an isomorphism. This will imply $X = C times.o_C Lambda tilde.equiv Lambda$ as
  bimodules, i.e., $(X) = 1$ in $op("Picent") Lambda$, as desired.

  To prove $psi$ surjective, we note first that there is a bimodule isomorphism
  $ (X_n)^Lambda times.o_(c(Lambda_n)) Lambda_n tilde.equiv X_n, $
  since $X_n tilde.equiv Lambda_n$ as bimodules. Further, we have
  $ (X_n)^Lambda = T^n lr((X)) slash P^n X. $
  Consequently we obtain
  $ X = T^n lr((X)) Lambda + P^n X, $
  so also (by @eq:approximate-centralizer-bound)
  $ X = T^n lr((X)) Lambda + P X = X^Lambda dot Lambda + P X. $
  Nakayama’s Lemma then gives $X = X^Lambda dot Lambda$, so $psi$ is surjective,
  and the theorem is proved.
]

Combining the above with Theorem @th:semilocal-picard-radical-reduction and its
corollaries, we deduce:

#corollary(title: [Fröhlich @bib:Frohlich1973])[
  Let $Lambda$ be as in @th:order-central-picard-finite-reduction-injective, and
  suppose that $R slash P$ is a finite field. Then $op("Picent") Lambda$ is a
  finite group, and so is#footnote[
    We use the notation of @th:locally-free-picard-local-global-sequence.
  ] $N(Lambda) slash Lambda^times (K C)^times$.
] <cor:local-order-central-picard-finite>
#proof[
  For sufficiently large $n$, $op("Picent") Lambda$ maps injectively into
  $op("Pic")_R Lambda slash P^n Lambda$, which is finite by
  @cor:finite-ring-picard-radical-primary-kernel(i). Further,
  $N(Lambda) slash Lambda^times (K C)^times$ is isomorphic to
  $op("Outcent") Lambda$ by @th:normalizer-outer-central-automorphisms, and
  $op("Outcent") Lambda$ maps injectively into $op("Picent") Lambda$.
]

=== Picard Groups of Group Rings <ss:picard-group-rings>

Throughout this section, let $R$ be a Dedekind domain with quotient field $K$,
and let $G$ be a finite group such that $op("char") K divides.not |G|$. Set
$Lambda = R G$, $A = K G$, so $Lambda$ is an $R$-order in the f.d. separable
$K$-algebra $A$. Let $C = c(Lambda)$.

We begin with an easy result:

#proposition[
  Let $R$ be a d.v.r. with residue class field $k = R slash P$. If
  $op("char") k divides.not |G|$, then $op("Picent") R G = 1$.
] <prop:prime-to-residue-order-group-ring-central-picard-trivial>
#source(413)
#proof[
  The hypothesis implies that $|G| in R^times$, so $Lambda$ is a separable
  $R$-algebra (see Exercise @exc:azumaya-algebra-definition), and is therefore a
  central separable $C$-algebra. Thus
  $op("Picent") Lambda tilde.equiv op("Picent") C$, and $op("Picent") C = 1$ by
  @th:commutative-invertible-locally-rank-one.

  When $R$ is the ring of integers of a finite extension of $QQ_p$, another
  proof is available. Let $hat(Lambda)$ be the $P$-adic completion of $Lambda$.
  Then $hat(Lambda)$ is a maximal order in a direct sum of full matrix algebras
  over fields (see @th:prime-to-p-group-algebra-unramified-splitting), so
  $op("Picent") hat(Lambda) = 1$. Now use Exercise
  @exc:central-picard-completion-injective.
]

Somewhat more difficult is the following result of Fröhlich @bib:Frohlich1973.

#theorem[
  Let $R$ be a d.v.r. with finite residue class field $k = R slash P$, and let
  $G$ be a $p$-group, where $p$ is prime. Then $op("Picent") R G$ is also a
  finite $p$-group.
] <th:local-p-group-ring-central-picard-primary>
#proof[
  If $op("char") k divides.not p$, then $op("Picent") R G = 1$ by
  @prop:prime-to-residue-order-group-ring-central-picard-trivial. Hence we may
  assume from now on that $op("char") k = p$. By Exercise
  @exc:central-picard-radical-square-primary-kernel, there is a homomorphism
  $ rho: op("Picent") Lambda arrow op("Pic")_R Lambda slash J^2, $
  where $J = op("rad") Lambda$, and $ker rho$ is a finite $p$-group. By
  @eq:group-ring-locally-free-central-picard,
  $op("Picent") Lambda tilde.equiv op("Outcent") Lambda$, so it suffices to show
  that $rho(op("Outcent") Lambda) = 1$. Equivalently, we must prove that for
  each $f in op("Autcent") Lambda$, its image
  $f' in op("Aut")_R Lambda slash J^2$ is trivial.

  Let $G^"ab" = G slash [G,G]$, and set
  $
    Lambda = R G, quad J = op("rad") Lambda; quad
    tilde(Lambda) = R G^"ab", quad tilde(J) = op("rad") tilde(Lambda).
  $
  The surjection $G arrow G^"ab"$ induces a ring surjection
  $Lambda arrow tilde(Lambda)$, and we claim that this gives rise to an
  isomorphism of rings
  $Lambda slash J^2 tilde.equiv tilde(Lambda) slash tilde(J)^2$. Indeed, we have
  $J = P Lambda + I$, where $I$ is the augmentation ideal of $R G$. Then
  $J^2 = (P^2,P I,I^2)$. For $x,y in G$,
  $
    x y - y x = (x-1)(y-1) - (y-1)(x-1) in I^2.
  $
  Hence the kernel of $Lambda arrow tilde(Lambda)$ lies in $I^2 subset.eq J^2$,
  while $J$ maps onto $tilde(J)$. This proves
  $Lambda slash J^2 tilde.equiv tilde(Lambda) slash tilde(J)^2$, as
  claimed.#ed-note[
    The displayed augmentation basis in the original proof is too large. For
    $R = ZZ_3$ and $G = C_3$, the quotient has length $3$, whereas the printed
    direct sum has length $4$.
  ]

  Next, the kernel of the surjection $Lambda arrow tilde(Lambda)$ is the ideal
  generated by all $lr({x y - y x: x,y in Lambda})$, which is mapped onto itself
  by each $f in op("Autcent") Lambda$. Thus $f$ induces an automorphism
  $tilde(f)$ of $tilde(Lambda)$. But $f$ preserves class sums in $Lambda$, so
  for each conjugacy class $frak(C)$ of $G$, $f$ fixes $sum_(x in frak(C)) x$.
  This class sum has image $|frak(C)| overline(x)$ in $tilde(Lambda)$, and since
  $op("char") K divides.not |G|$ by hypothesis, also
  $op("char") K divides.not |frak(C)|$. Therefore $tilde(f)$ fixes each
  $overline(x) in G^"ab"$ so $tilde(f) = 1$.

  Now consider the commutative diagram
  #group-ring-abelianization-radical-square
  #source(414)
  Since each $f in op("Autcent") Lambda$ induces the identity automorphism of
  $tilde(Lambda)$, it follows that the image of $f$ in
  $op("Aut")_R Lambda slash J^2$ is also $1$. This completes the proof of the
  theorem.
]
#idx(
  "Fröhlich's Theorem",
  target: [@th:local-p-group-ring-central-picard-primary],
)

#corollary[
  Let $G$ be a $p$-group, and let $R$ be an arbitrary Dedekind domain. Let $P$
  range over all maximal ideals of $R$. Then
  $ product_P op("Picent") R_P G $
  is a finite $p$-group.#ed-note[
    The preceding proof uses finite residue fields. For a general residue field,
    completion and Borger @bib:Borger2004, Construction~1.7 and
    Propositions~1.8, 1.11, give a faithfully flat extension to a complete
    d.v.r. $B$; Weierstrass preparation makes $B$ finite over the Witt ring
    $W(F)$, with $F$ algebraically closed of characteristic $p$. Central outer
    automorphism classes inject under this extension: their intertwiners descend
    as rank-one projective modules over the semilocal center, hence are free.
    Every $W(F)$-derivation of $B G$ is $B$-linear, since $B$ is generically
    separable over $W(F)$, and
    $
      op("HH")^1_B lr((B G))
      tilde.equiv plus.o_([g]) op("Hom") lr((C_G lr((g)),B^+)) = 0.
    $
    Here $B^+$ denotes the additive group of $B$. Thus Eisele @bib:Eisele2022,
    Theorem~B, gives finiteness. The injection in
    @th:order-central-picard-finite-reduction-injective and the nilpotent
    derivation filtration in @th:semilocal-picard-radical-reduction give the
    $p$-primary assertion without finiteness of the residue field. Only the
    finitely many primes over $p$ contribute to the product.
  ]
] <cor:p-group-ring-local-central-picard-product>

Next we show:

#theorem(title: [Fröhlich])[
  Let $Lambda = ZZ G$, where $G$ is a $p$-group, with $p$ prime. Let
  $C = "center of" Lambda$, and let $D(C)$ be the kernel group (see
  @eq:class-group-kernel-sequence). Then $D(C)$ is a finite $p$-group.
] <th:p-group-center-kernel-group-primary>
#proof[
  Let $frak(O)$ be a maximal $ZZ$-order in $QQ times.o_ZZ C$. Then
  $C_q = frak(O)_q$ for each rational prime $q != p$. As in the proof of
  @th:p-group-integral-kernel-is-p-group, we deduce that
  $ D(C) tilde.equiv frak(O)_p^times slash frak(O)^times C_p^times. $
  The rest of the proof is parallel to that of
  @th:p-group-integral-kernel-is-p-group, and we omit the details.
]
#idx("Fröhlich's Theorem", target: [@th:p-group-center-kernel-group-primary])

We shall next give an example of the calculation of $op("Picent") ZZ G$ to
illustrate the methods developed in the previous subsections. Following Fröhlich
@bib:Frohlich1973 and Fröhlich–Reiner–Ullom @bib:FrohlichReinerUllom1974, we
consider the case where $G$ is a dihedral group of order $2 p$, with $p$ an odd
prime. To fix the notation, let
$ G = ⟨ x,y: x^p = 1, y^2 = 1, y x y^(-1) = x^(-1) ⟩. $
Let $omega$ be a primitive $p$-th root of $1$ over $QQ$, and set
$
  R = ZZ[omega], quad K = QQ(omega); quad
  S = ZZ[omega + overline(omega)], quad L = QQ(omega + overline(omega)),
$
where for $alpha in K$, $overline(alpha)$ denotes its complex conjugate. As in
the proof of @th:galovich-reiner-ullom-metacyclic-class-groups (see also
@i:eq:metacyclic-integral-fibre-product and the discussion following it), there
is a fiber product
#numbered-block[#dihedral-group-ring-picard-fiber-product]
<eq:dihedral-group-ring-picard-fiber-product>
where $H = ⟨ y: y^2 = 1 ⟩$, $overline(ZZ) = ZZ slash p ZZ$, and
$Gamma = R plus.o R y$ is a twisted group ring in which $y^2 = 1$ and
$y alpha = overline(alpha) y$ for all $alpha in R$. We have seen that
$
  A = QQ G tilde.equiv QQ H plus.o B, quad "where"
  B = QQ times.o_ZZ Gamma = K compose H tilde.equiv M_2 lr((L)).
$
<eq:dihedral-rational-group-algebra-picard-decomposition>

#source(415)
The algebra $B$ embeds in $M_2(K)$ via
$
  alpha in K mapsto mat(alpha, 0; 0, overline(alpha)), quad
  y mapsto mat(0, 1; 1, 0).
$
Then $Gamma$ is a hereditary $ZZ$-order in the central simple $L$-algebra $B$,
and its center is $S$ (viewed as a set of scalar matrices). Since $R$ is
unramified over $S$ except at the unique prime ideal of $S$ containing $p$, it
follows that the $2$-adic completion $Gamma_2$ is a maximal order in $B_2$, and
is isomorphic to the ring of all $2 times 2$ matrices over $S_2$. On the other
hand, the $p$-adic completion $Gamma_p$ is a hereditary order in
$M_2 lr((L_p))$.

We have $S = "alg.int." lr({L})$; let $op("Cl") S$ be its ideal class group,
written multiplicatively, and define a homomorphism
$ t: op("Cl") S arrow op("Cl") S quad "by" t(frak(a)) = (frak(a)^2) $
for each $S$-ideal $frak(a)$ in $L$. Clearly,
$
  ker t = (op("Cl") S)_2 = lr({x in op("Cl") S: x^2 = 1}), quad
  op("cok") t = (op("Cl") S) slash (op("Cl") S)^2.
$
We observe next that by @eq:dihedral-rational-group-algebra-picard-decomposition
the algebra $A$ satisfies the Eichler condition relative to $ZZ$ (see
@prop:eichler-condition-sufficient-cases), and therefore the order $Lambda$ has
locally free cancellation by the Jacobinski Cancellation Theorem
@th:jacobinski-cancellation. Thus by
@th:locally-free-picard-class-group-kernel-cokernel there is a well-defined
homomorphism $theta: op("LFP")(Lambda) arrow op("Cl") Lambda$, whose kernel is
isomorphic to $op("Outcent") Lambda$.

Our main result is as follows:

#theorem[
  Let $Lambda = ZZ G$, where $G$ is a dihedral group of order $2 p$, and keep
  the above notation. Then
  #enum(
    numbering: "(i)",
    [$op("Outcent") Lambda tilde.equiv ker theta
      tilde.equiv (op("Cl") S)_2 times
      ("cyclic group of order" (p-1) slash 2)$.],
    [$op("cok") theta tilde.equiv op("cok") t
      tilde.equiv (op("Cl") S) slash (op("Cl") S)^2$.],
    [$op("Cl") Lambda tilde.equiv op("Cl") S$ and
      $
        op("Picent") Lambda = op("LFP")(Lambda)
        tilde.equiv (op("Cl") S) times
        ("cyclic group of order" (p-1) slash 2).
      $],
  )
] <th:dihedral-prime-order-central-picard-group>
#proof[
  _Step 1._ Since $Lambda = ZZ G$, every projective $ZZ G$-lattice is locally
  free. Thus $op("Picent") Lambda = op("LFP")(Lambda)$. Likewise,
  $op("Picent") Lambda_q tilde.equiv op("Outcent") Lambda_q$ for each rational
  prime $q$, and
  $
    op("Outcent") Lambda_q tilde.equiv
    N(Lambda_q) slash Lambda_q^times (K_q C)^times.
  $
  By @th:locally-free-picard-local-global-sequence, there is an exact sequence
  $
    1 arrow op("Cl") C arrow^tau op("LFP")(Lambda)
    arrow product_q op("Outcent") Lambda_q arrow 1.
  $
  #source(416)
  In Step 3 we shall prove that $op("Outcent") Lambda_q = 1$ for each $q$, so
  $tau: op("Cl") C tilde.equiv op("LFP")(Lambda)$. We take this for granted for
  the time being.

  Now let $Gamma'$ be a maximal $ZZ$-order in $B$ containing $Gamma$, and set
  $Lambda' tilde.equiv ZZ plus.o ZZ plus.o Gamma'$, a maximal order in $A$
  containing $Lambda$. Then $op("Cl") Lambda tilde.equiv
  op("Cl") Lambda'$ by @th:galovich-reiner-ullom-metacyclic-class-groups, while
  $op("Cl") Gamma tilde.equiv op("Cl") Gamma'$ by
  @cor:hereditary-order-class-group-maximal-order since $Gamma$ is hereditary.
  Further, $op("Cl") Gamma' tilde.equiv op("Cl") S$ by
  @th:maximal-order-restricted-ideal-class-group. Let
  $C' = ZZ plus.o ZZ plus.o S$ be the center of $Lambda'$. Composition of maps
  gives a homomorphism
  $
    op("Cl") S tilde.equiv op("Cl") C' arrow op("LFP")(Lambda')
    arrow op("Cl") Lambda' tilde.equiv op("Cl") S,
  $
  which is precisely the map $t$ defined above (see the proof of
  @th:maximal-order-picard-class-kernel-cokernel). We thus obtain a commutative
  diagram
  #dihedral-picard-class-comparison
  Since $phi$ is the composite of the surjection $op("Cl") C arrow op("Cl") C'$
  and the isomorphism $op("Cl") C' tilde.equiv op("Cl") S$, it follows that
  $phi$ is surjective. Taking for granted that $tau$ is an isomorphism, we
  obtain
  $
    ker theta tilde.equiv ker t phi, quad
    op("cok") theta tilde.equiv op("cok") t phi.
  $
  However, there is an exact sequence
  $
    1 arrow ker phi arrow ker t phi arrow ker t arrow op("cok") phi
    arrow op("cok") t phi arrow op("cok") t arrow 1.
  $
  Since $op("cok") phi = 1$, we deduce that
  $op("cok") theta tilde.equiv op("cok") t$ (so (ii) is proved), and also the
  sequence
  $ 1 arrow ker phi arrow ker theta arrow ker t arrow 1 $
  <eq:dihedral-picard-class-kernel-extension>
  is exact.

  _Step 2._ From the diagram @eq:dihedral-group-ring-picard-fiber-product we
  obtain a new fiber product
  #dihedral-center-picard-fiber-product
  where now $g_2: S arrow S slash (omega-overline(omega))^2
  tilde.equiv overline(ZZ) subset overline(ZZ) H$. This gives a Mayer–Vietoris
  sequence
  $
    (ZZ H)^times times S^times arrow^h (overline(ZZ) H)^times
    arrow op("Cl") C arrow^phi op("Cl") S plus.o op("Cl") ZZ H arrow 0,
  $
  #source(417)
  and $op("Cl") ZZ H = 0$ by Theorem @th:rim-cyclic-prime-class-group, so this
  $phi$ agrees with our earlier $phi$. We have
  $(overline(ZZ) H)^times = overline(ZZ)^times times overline(ZZ)^times$ and
  $h(S^times) = overline(ZZ)^times$, since for $n in ZZ$ prime to $p$, the
  element $(omega^n - omega^(-n)) slash (omega-omega^(-1))$ lies in $S^times$
  and has image $overline(n)$ in $overline(ZZ)^times$. Further,
  $(ZZ H)^times = lr({plus.minus 1, plus.minus y})$. It follows readily that
  $op("cok") h$ is cyclic of order $(p-1) slash 2$. Furthermore, since
  $g_2 lr((S^times)) = (g_2 lr((S)))^times$, Exercise
  @exc:class-kernel-projection-split shows that the surjection
  $phi: op("Cl") C arrow op("Cl") S$ is split. Therefore
  $
    op("Cl") C tilde.equiv op("Cl") S plus.o ker phi, quad
    ker phi = "cyclic group of order" (p-1) slash 2.
  $

  _Step 3._ We now verify that $tau: op("Cl") C tilde.equiv
  op("LFP")(Lambda)$, or equivalently, that $op("Outcent") Lambda_q = 1$ for
  each rational prime $q$. For $q != 2$ or $p$, $Lambda_q$ is a maximal order in
  $A_q$, so $op("Outcent") Lambda_q = 1$ by
  @th:local-maximal-order-central-picard-cyclic. For $q = 2$, we have
  $ Lambda_2 tilde.equiv ZZ_2 H plus.o Gamma_2, $
  and $op("Picent") Lambda_2 = op("Picent") ZZ_2 H times
  op("Picent") Gamma_2 = op("Cl") ZZ_2 H = 1$, using the fact that $Gamma_2$ is
  a maximal order in $A_2$.

  It remains to verify that $op("Outcent") Lambda_p = 1$, that is, if
  $x in A_p^times$ is such that $x Lambda_p x^(-1) = Lambda_p$, then
  $x in Lambda_p^times (K_p C)^times$ (see
  @th:normalizer-outer-central-automorphisms). Replacing $x$ by $a x$ with
  $a in R_p$, and changing notation, we may assume that
  $x in Lambda_p inter A_p^times$. Taking $p$-adic completions in the fiber
  product @eq:dihedral-group-ring-picard-fiber-product, we obtain a new fiber
  product
  #dihedral-completed-picard-fiber-product
  in which $g_2$ is the map $Gamma_p arrow Gamma_p slash op("rad") Gamma_p$. We
  have
  $
    Lambda_p = lr(
      {(y_1,y_2) in ZZ_p H plus.o Gamma_p:
        g_1 lr((y_1)) = g_2 lr((y_2)) "in" overline(ZZ) H}
    ).
  $
  Write $x = (x_1,x_2) in Lambda_p inter A_p^times$. Then
  $x(y_1,y_2)x^(-1) in Lambda_p$ for each $(y_1,y_2) in Lambda_p$, which implies
  that for each $y_2 in Gamma_p$, we have
  $
    x_2 y_2 x_2^(-1) in Gamma_p quad "and"
    x_2 y_2 x_2^(-1) equiv y_2 quad (mod op("rad") Gamma_p).
  $
  <eq:dihedral-completed-normalizer-congruence>
  Let $pi$ denote a prime element of $S_p$. Since $Gamma_p$ is a hereditary
  order in $M_2 lr((S_p))$, and $Gamma_p$ is not a maximal order, it follows
  from @i:th:local-hereditary-orders-block-form that we may write
  $
    Gamma_p = mat(S_p, pi S_p; S_p, S_p)
    = lr({mat(a, b; c, d): a,b,c,d in S_p, b in pi S_p}).
  $
  There are precisely two maximal orders containing $Gamma_p$, namely,
  $
    Omega = mat(S_p, S_p; S_p, S_p) quad "and"
    Omega' = z Omega z^(-1), quad "where" z = mat(pi, 0; 0, 1).
  $
  #source(418)
  Conjugation by $x_2$ must either fix both $Omega$ and $Omega'$, or else must
  interchange them. If $x_2 Omega x_2^(-1) = Omega$, then
  $x_2 in Omega^times L_p^times$ by @cor:local-maximal-order-picard-normalizer.
  An easy calculation shows that for $x_2 in Omega^times$, the first condition
  in @eq:dihedral-completed-normalizer-congruence implies that
  $x_2 in Gamma_p^times$. In this case there exists an
  $x' = (x'_1,x_2) in Lambda_p^times$, such that conjugation by $x'$ and $x$
  coincide, and thus $x in Lambda_p^times (K_p C)^times$ as desired. On the
  other hand, if $x_2 Omega x_2^(-1) = Omega'$, then $x'_2 = z^(-1) x_2$
  conjugates $Omega$ into itself. Then $z^(-1) x_2 in Omega^times L_p^times$,
  and it is easily checked that the second condition in
  @eq:dihedral-completed-normalizer-congruence cannot hold.

  We have now proved all of the assertions of the theorem, except that the
  sequence @eq:dihedral-picard-class-kernel-extension is split. We leave this as
  an exercise for the reader.
]

We conclude the discussion of Picard groups with a brief guide to the
literature.

#enum(
  numbering: "(1)",
  [Endo–Miyata–Sekiguchi @bib:Endo1982 studied $op("Picent") ZZ G$ for the
    cases:
    #case-list(
      numbering: "(a)",
      [#case[$G = "metacyclic group" C_n times.r C_q$, where $(q,n) = 1$ and
        where $C_q$ acts faithfully on each Sylow subgroup of $C_n$.
      ] <case:endo-metacyclic-central-picard>],
      [#case[$G = "dihedral group of order" 2 n$, with $n$ arbitrary.
      ] <case:endo-dihedral-central-picard>],
    )
    In both cases, they showed that $op("Outcent") ZZ_p G = 1$ for all primes
    $p$, and thus
    $
      op("Picent") ZZ G = op("LFP")(ZZ G)
      tilde.equiv op("Cl") ("center of" ZZ G).
    $
    They obtained formulas for the orders of $op("Picent") ZZ G$ and
    $op("Outcent") ZZ G$, in terms of the orders of various locally free class
    groups. See @bib:Endo1982, Theorem 4.8 for case
    @case:endo-metacyclic-central-picard, and Theorem 5.6 for case
    @case:endo-dihedral-central-picard.],
  [Let $G$ be a finite group, and let $f in op("Aut") G$. We say that $f$ is
    _class-preserving_ if for each $x in G$, $f(x)$ is $G$-conjugate to $x$. Let
    $op("Aut")_c G$ be the group of all class-preserving automorphisms $f$ of
    $G$, and $op("In")(G)$ its subgroup consisting of all inner automorphisms of
    $G$. Define
    $ op("Out")_c G = (op("Aut")_c G) slash op("In") G. $
    Then we have: #theorem(title: [Endo–Miyata–Sekiguchi @bib:Endo1982])[
      Let $G$ be a nilpotent group of order $n$. Then both of the homomorphisms
      $
        op("Out")_c G arrow op("Outcent") ZZ G, quad
        op("Out")_c G arrow product_(p divides n) op("Outcent") ZZ_p G,
      $
      are injective.
    ] <th:nilpotent-class-preserving-outer-picard-embedding>
    #idx(
      "Endo-Miyata-Sekiguchi Theorem",
      target: [@th:nilpotent-class-preserving-outer-picard-embedding],
    )
    For each prime $p$, there exists a $p$-group $G$ for which $op("Out")_c G$
    is non-abelian (see Sah @bib:Sah1968). For each such $G$, it follows that
    the groups
    $
      op("Outcent") ZZ G, quad
      op("Picent") ZZ G (= op("LFP")(ZZ G)), quad
      op("Outcent") ZZ_p G
    $
    <eq:nonabelian-integral-group-ring-picard-groups>
    are non-abelian.
    #source(419)
    Similar results were obtained by Keating @bib:Keating1979. Given a prime
    $p$, Keating constructed a sequence of $p$-groups $lr({G_n: n >= 1})$ such
    that $|G_n| = p^(6 n)$ and $G_n$ is nilpotent of class $2$. He showed that
    (in the above notation) $op("Out")_c G$ contains a subgroup isomorphic to
    $(ZZ slash p^n ZZ)^((4))$, which then embeds in all of the groups listed in
    @eq:nonabelian-integral-group-ring-picard-groups.],
  [Sekiguchi @bib:Sekiguchi1983 showed that $op("Outcent") ZZ_p G = 1$ for all
    metacyclic $p$-groups $G$, where $p$ is any odd prime.],
  [Fröhlich @bib:Frohlich1973 showed that for $G$ the quaternion group of order
    $8$, $op("Picent") ZZ G$ has order $2$, and $op("Outcent") ZZ G$ is
    trivial.],
)

#exercises-heading

#exercise[
  Let $E = M_n lr((R))$, where $R$ is a commutative ring and $n >= 1$. Given an
  $R$-algebra $Lambda$, let
  $Gamma = E times.o_R Lambda tilde.equiv M_n lr((Lambda))$. Show that the
  isomorphism $op("Pic")_R Lambda tilde.equiv op("Pic")_R Gamma$ given in
  @th:picard-morita-invariance can also be described by the map
  $ (X) mapsto (E times.o_R X) quad "for" (X) in op("Pic")_R Lambda. $
] <exc:morita-central-picard-equivalence>
#hint([@exc:morita-central-picard-equivalence])[
  Let $L = R^((n)) times.o_R Lambda$, viewed as invertible
  $(Gamma,Lambda)$-bimodule. Set $L^(-1) = op("Hom")_Lambda lr((L,Lambda))$.
  Then $L$ gives an isomorphism
  $
    op("Pic")_R Lambda tilde.equiv op("Pic")_R Gamma, quad "with"
    (X) mapsto (L times.o_Lambda X times.o_Lambda L^(-1))
    "for" (X) in op("Pic")_R Lambda.
  $
  However, there are two-sided $Gamma$-isomorphisms
  $
    L times.o_Lambda X times.o_Lambda L^(-1)
    tilde.equiv op("Hom")_Lambda lr((L,L times.o_Lambda X))
    tilde.equiv op("Hom")_Lambda lr((Lambda^((n)),X^((n))))
    tilde.equiv E times.o_R X.
  $
]

#exercise[
  Keeping the above notation, let $[Y] in K_0 lr((Lambda))$. Show that
  $ [E times.o_R Y] = n [L times.o_Lambda Y] quad "in" K_0 lr((Gamma)). $
] <exc:matrix-morita-class-group-multiplication>
#hint([@exc:matrix-morita-class-group-multiplication])[
  $L times.o_Lambda Y tilde.equiv R^((n)) times.o_R Y$ as left $Gamma$-modules.
  Since $E$ is isomorphic to a direct sum of $n$ copies of the left $E$-module
  $R^((n))$, we obtain
  $ [E times.o_R Y] = n [R^((n)) times.o_R Y] = n [L times.o_Lambda Y], $
  as desired.
]

#exercise[
  Let $R$ be a commutative ring, and let $E$ be an $R$-algebra. Call $E$ an
  _Azumaya $R$-algebra_ (= central separable $R$-algebra) if $c(E) = R$ and $E$
  is projective as left $(E times.o_R E^"op")$-module. (This generalizes the
  concept of separable algebras over fields in
  §@i:ss:separable-algebras-modules; see DeMeyer–Ingraham @bib:DeMeyer1971.)
  Show that for every $R$-algebra $Lambda$ and every $R$-Azumaya algebra $E$,
  there is an isomorphism
  $
    op("Pic")_R Lambda tilde.equiv op("Pic")_R lr((Lambda times.o_R E)), quad
    "given by" (X) mapsto (X times.o_R E).
  $
] <exc:azumaya-algebra-definition>
#idx("Azumaya algebra", target: [@exc:azumaya-algebra-definition])
#idx("Central separable R-algebra", target: [@exc:azumaya-algebra-definition])
#hint([@exc:azumaya-algebra-definition])[
  See DeMeyer–Ingraham @bib:DeMeyer1971, or @bib:Reiner1975[MO] Exercise 37.4.
]

#source(420)
#exercise[
  Let $Lambda = product.co_(i=1)^t Lambda_i$ be a direct sum of rings. Prove
  that
  $ op("Picent") Lambda tilde.equiv product_(i=1)^t op("Picent") Lambda_i. $
] <exc:central-picard-direct-product>
#hint([@exc:central-picard-direct-product])[
  Let $e_1,dots,e_t$ be central idempotents in $Lambda$ such that
  $Lambda_i = Lambda e_i$. For each $(X) in op("Picent") Lambda$ we have
  $e_i X = X e_i$, so $(e_i X) in op("Picent") Lambda_i$. The desired
  isomorphism is given by $(X) mapsto product (e_i X)$.
]

#exercise[
  Let $M,N$ be full $R$-lattices in a f.d. $K$-space $V$, where $R$ is a
  Dedekind domain with quotient field $K$. Define the _generalized $R$-order
  ideal_ $op("ord") M slash slash N$ by the formula
  $
    op("ord") M slash slash N =
    (op("ord") M slash (M inter N))(op("ord") N slash (M inter N))^(-1),
  $
  where $op("ord") M slash (M inter N)$ is the usual $R$-order ideal (see
  §@i:ss:modules-dedekind-domains). Show that if $L$ is another full $R$-lattice
  in $V$, then
  $
    (op("ord") L slash slash M)(op("ord") M slash slash N)
    = op("ord") L slash slash N.
  $
] <exc:generalized-order-ideal>
#idx("Order ideal", target: [@exc:generalized-order-ideal])
#idx("R-order (generalized)", target: [@exc:generalized-order-ideal])

#exercise[
  Let $M$ be a full $R$-lattice in a f.d. separable $K$-algebra $A$, where $R,K$
  are as above, and let $x in A^times$. Prove that
  $ op("ord") M slash slash M x = op("ord") M slash slash x M. $
  Deduce that if $M x subset.eq x M$, then $M x = x M$.
] <exc:order-conjugate-containment>
#hint([@exc:order-conjugate-containment])[
  By Exercise @exc:generalized-order-ideal, it suffices to treat the case where
  $M x subset.eq M$ and $x M subset.eq M$. By
  @i:prop:order-endomorphism-cokernel,
  $ op("ord") M slash M x = R dot N_(A slash K) lr((x)), $
  where $N_(A slash K) lr((x))$ denotes the norm, computed by letting $x$ act as
  right multiplication on $A$. But the right and left norms coincide since $A$
  is separable, as is clear by passing to a splitting field, and using the fact
  that a matrix and its transpose have the same characteristic polynomial.
]

#exercise[
  Let $Lambda$ be a semilocal ring, that is, $overline(Lambda) = Lambda slash J$
  is semisimple artinian, where $J = op("rad") Lambda$. Show that for each
  invertible bimodule $attach(M, bl: Lambda, br: Lambda)$ we have
  $J^r M = M J^r$ for $r >= 0$.
] <exc:invertible-bimodule-characteristic-ideal>
#hint([@exc:invertible-bimodule-characteristic-ideal], caption: [Hint
  (Fröhlich):])[
  Put $overline(M) = M slash J M$, a $(overline(Lambda),Lambda)$-bimodule, and
  set $E = op("End")_(overline(Lambda)) overline(M)$. Then $E$ is semisimple
  artinian and may be viewed as a ring of right operators on $overline(M)$. For
  $a in Lambda$, let $a_r$ denote right multiplication on $M$ or $overline(M)$.
  The map $a mapsto a_r$ (on $overline(M)$) gives a ring homomorphism
  $phi: Lambda arrow E$, and $phi$ is surjective since every
  $overline(Lambda)$-endomorphism of $overline(M)$ lifts to a
  $Lambda$-endomorphism of $M$, and hence is some $a_r$. It follows that
  $phi(J) subset.eq op("rad") E = 0$, so $M J subset.eq J M$. Therefore
  $M J = J M$ by symmetry.
]

#exercise[
  Keeping the above notation, show that $M slash J^r M$ is an invertible
  bimodule over the ring $Lambda slash J^r$ for $r >= 1$.
] <exc:invertible-bimodule-quotient>
#hint([@exc:invertible-bimodule-quotient])[
  If $Lambda' = Lambda slash J^r$, where $r >= 1$, then
  $Lambda' times.o_Lambda M tilde.equiv M slash J^r M$, while
  $M times.o_Lambda Lambda' tilde.equiv M slash M J^r = M slash J^r M$ by the
  preceding exercise.
]

#exercise[
  Let $R$ be a d.v.r. with quotient field $K$, maximal ideal $P$, and finite
  residue class field
  #source(421)
  $k = R slash P$ of characteristic $p$. Let $Lambda$ be an $R$-order in a f.d.
  separable $K$-algebra $A$, and let $J = op("rad") Lambda$. Show that
  $ ker(op("Picent") Lambda arrow op("Pic")_R Lambda slash J^2) $
  is a finite $p$-group.
] <exc:central-picard-radical-square-primary-kernel>
#hint([@exc:central-picard-radical-square-primary-kernel], caption: [Hint
  (Fröhlich):])[
  Choose $n$ so large that $P^n Lambda subset.eq J^2$ and
  $op("Picent") Lambda arrow op("Pic")_R Lambda_n$ is injective, where
  $Lambda_n = Lambda times.o_R k_n$, and $k_n = R slash P^n$. Then
  $
    Lambda slash J^2 tilde.equiv Lambda slash J^2 times.o_R k_n
    tilde.equiv Lambda_n slash J_n^2.
  $
  Consider the commutative diagram:
  #central-picard-primary-kernel-reduction
  Then $ker g$ is a $p$-group, and $ker f subset.eq ker g$.
]

#exercise[
  Keeping the above notation, show that
  $op("Pic")_R Lambda arrow op("Pic")_R Lambda slash P^n Lambda$ is injective
  for sufficiently large $n$.
] <exc:picard-finite-reduction-injective>
#hint([@exc:picard-finite-reduction-injective])[
  Use @th:order-central-picard-finite-reduction-injective.
]

#exercise[
  Let $Lambda$ be as above, but do not assume $R slash P$ finite. Let
  $hat(Lambda)$ be the $P$-adic completion of $Lambda$. Prove that
  $op("Picent") Lambda tilde.equiv op("Picent") hat(Lambda)$.
] <exc:central-picard-completion-injective>
#hint([@exc:central-picard-completion-injective])[
  Use @cor:central-picard-invertible-ideal-quotient.
]

#exercise[
  Prove that if $G$ is a finite nilpotent group, then so are both
  $op("LFP")(ZZ G)$ and $op("Outcent") ZZ G$.
] <exc:nilpotent-integral-group-ring-picard-groups>
#hint([@exc:nilpotent-integral-group-ring-picard-groups], caption: [Hint
  (Endo–Miyata–Sekiguchi @bib:Endo1982):])[
  Use @cor:p-group-ring-local-central-picard-product and the fact that the map
  $tau$ in @th:central-picard-local-global-sequence carries $op("Picent") C$
  into the center of $op("Picent") ZZ G$.
]
