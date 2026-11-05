#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/42-fiber-products.typ": *

== Mayer–Vietoris Sequences <sec:mayer-vietoris>

#source(117)
Let #numbered-block(fiber-product-square) <eq:ring-fiber-product-square>
be a fiber product of rings and ring homomorphisms (see end of
§@i:ss:homomorphisms). This means that there is a ring isomorphism
$
  A tilde.equiv lr(
    {(a_1,a_2): a_i in A_i,
      g_1 lr((a_1)) = g_2 lr((a_2))}
  ),
$
or equivalently, an exact sequence (of additive groups)
$
  0 -> A arrow.r^((f_1,f_2)) A_1 plus.o A_2
  arrow.r^((g_1,-g_2)) overline(A).
$
<eq:fiber-product-additive-sequence>

Our object is to study properties of the ring $A$, and in particular the
category $cal(P)(A)$, in terms of corresponding properties of $A_1,A_2$, and
$overline(A)$. We shall be especially interested in the relation between the
$K$-theory of $A$ and that of the other rings. This relation, called a
_Mayer–Vietoris sequence_, is as follows: if either $g_1$ or $g_2$ is
surjective, there is an exact sequence of groups
$
  K_1 lr((A)) -> K_1 lr((A_1)) times K_1 lr((A_2))
  -> K_1 lr((overline(A))) -> K_0 lr((A))
  -> K_0 lr((A_1)) plus.o K_0 lr((A_2)) -> K_0 lr((overline(A))).
$
The result, due to Milnor, is of the utmost importance in calculations of
$K$-groups. Further, if both $g_1$ and $g_2$ are surjective, the sequence can be
extended to the left by means of $K_2$ terms, where $K_2 lr((A))$ is the Milnor
group of $A$ (see §@ss:relative-k2).
#idx("Mayer-Vietoris sequence", target: [@eq:ring-fiber-product-square])

#example[
  Let $I$ and $J$ be two-sided ideals of $A$. Then there is a fiber product
  #ideal-quotient-square

  As an illustration, consider Example
  @i:exm:dihedral-group-algebra-reduced-norm where $A = ZZ G$, with
  $
    G = chevron.l x,y: x^n = 1, y^2 = 1, y x y^(-1) = x^(-1) chevron.r,
    quad H = chevron.l x chevron.r ⊴ G.
  $
  Let
  $ I = (x-1) A, quad J = (x^(n-1)+x^(n-2)+dots+x+1) A, $
  a pair of two-sided ideals of $A$. Since $A$ is free as $ZZ H$-module, and
  $ (x-1) ZZ H inter (x^(n-1)+dots+x+1) ZZ H = 0, $
  we obtain
  $ I inter J = 0, quad I+J = n A + (x-1) A. $
  #source(118)
  The fiber product becomes
  #numbered-block(dihedral-integral-square)
  <eq:dihedral-integral-fiber-product>
  where $overline(ZZ) = ZZ slash n ZZ$, and $R circle.small [y]$, is the twisted
  group ring of the cyclic group $chevron.l y chevron.r$ of order $2$ over the
  commutative ring
  $ R = ZZ[x] slash (x^(n-1)+dots+x+1) $
  (see @i:eq:twisted-group-ring-module). The action of $y$ on $R$ is given by
  $ y alpha = overline(alpha) y, quad alpha in R, $
  where the bar denotes the automorphism of $R$ defined by $x -> x^(-1)$. Since
  $QQ$ is $ZZ$-flat, tensoring with $QQ$ over $ZZ$ gives a new fiber product
  (see @eq:fiber-product-additive-sequence)
  #dihedral-rational-square
  where
  $
    K = QQ[x] slash (x^(n-1)+dots+x+1)
    tilde.equiv product_(d divides n, d > 1)
    QQ[x] slash (Phi_d lr((x))) = product K_d.
  $
  Here, $Phi_d lr((x))$ is the $d$-th cyclotomic polynomial. Thus we obtain
  $
    QQ G tilde.equiv QQ[y] plus.o
    product_(d divides n, d > 1) K_d circle.small [y],
  $
  which agrees with the formula in @i:exm:dihedral-group-algebra-reduced-norm.
  In this connection, see also @i:eq:metacyclic-integral-fibre-product.
] <exm:ideal-quotient-fiber-product>
#idx("Dihedral group", target: [@exm:ideal-quotient-fiber-product])

#example(title: [Wall square; see C. T. C. Wall @bib:Wall1974b])[
  Let $R$ be a Dedekind domain with quotient field $K != R$, and let $Lambda$ be
  an $R$-order in a f.d. $K$-algebra $A$. For each maximal ideal $P$ of $R$, let
  $Lambda_P,A_P$, etc., denote _$P$-adic completions_.

  #source(119)
  The _adèle ring_ $hat(A)$ is defined as
  $ hat(A) = lr({(a_P) in product_P A_P: a_P in Lambda_P "a.e."}). $
  The diagonal mapping $A -> hat(A)$ is a ring homomorphism. Define
  $ hat(Lambda) = product_P Lambda_P = "ring of integral adèles", $
  a subring of $hat(A)$. By @i:prop:localization-completion-lattices we have
  $A inter hat(Lambda) = Lambda$, so there is a fiber product
  #wall-square
  called a _Wall square_.
] <exm:wall-square>
#idx("Adele ring", target: [@exm:wall-square])
#idx("Integral adeles", target: [@exm:wall-square])
#idx("Wall square", target: [@exm:wall-square])

Returning to the general fiber product @eq:ring-fiber-product-square, we note
that each $A_i$-module can be viewed as $A$-module via $f_i$, and likewise each
$overline(A)$-module becomes an $A_i$-module via $g_i$, for $i = 1,2$. Given any
$P in cal(P)(A)$, applying $ast times.o_A P$ to
@eq:fiber-product-additive-sequence yields a new exact sequence, and thus we
obtain a fiber product of left $A$-modules:
#numbered-block(projective-base-change-square)
<eq:projective-fiber-product-square>
Then $P_i in cal(P)(A_i)$, and there is a canonical $overline(A)$-isomorphism
$
  kappa: overline(A) times.o_(A_1) P_1 tilde.equiv
  overline(A) times.o_(A_2) P_2.
$
Then we have
$
  P tilde.equiv lr(
    {(x_1,x_2): x_i in P_i,
      kappa(overline(x)_1) = overline(x)_2}
  )
$
<eq:projective-fiber-product-elements>
where bars denote images in $overline(A) times.o P$.

We wish to reverse this procedure: starting with a pair of projective modules
$P_i in cal(P)(A_i)$, $i = 1,2$, and with some $overline(A)$-isomorphism
$phi: overline(P)_1 tilde.equiv overline(P)_2$ (where $overline(P)_i$ means
$overline(A) times.o P_i$), we want to find a module $P in cal(P)(A)$ for which
$A_i times.o_A P tilde.equiv P_i$, $i = 1,2$. For this purpose, we define
$
  (P_1,P_2,phi) = lr(
    {(x,y): x in P_1,y in P_2,
      phi(overline(x)) = overline(y)}
  ).
$
<eq:patched-module-triple>
Then $(P_1,P_2,phi)$ is an $A$-module, since for $a in A$,
$(x,y) in (P_1,P_2,phi)$, we have $a(x,y) = (a x,a y)$, and
$ phi(overline(a x)) = overline(a) phi(overline(x)) = overline(a y). $

#source(120)
Thus, @eq:projective-fiber-product-elements is just the assertion that
$P tilde.equiv (P_1,P_2,kappa)$. We note that $A = (A_1,A_2,1)$, and that
$
  (P_1,P_2,phi) plus.o (Q_1,Q_2,psi)
  tilde.equiv (P_1 plus.o Q_1,P_2 plus.o Q_2,phi plus.o psi).
$
Further, each map $f_i: P_i -> Q_i$ in $cal(P)(A_i)$ yields a map
$overline(f)_i: overline(P)_i -> overline(Q)_i$. We now define a _morphism_ of
triples#idx("Morphism", "of triples")
$ (f,g): (P_1,P_2,phi) -> (Q_1,Q_2,psi) $
to consist of a pair $f: P_1 -> Q_1$, $g: P_2 -> Q_2$, such that
$overline(g) phi = psi overline(f)$. As anticipated by the notation, the pair
$(f,g)$ induces an $A$-homomorphism of triples, by means of
$ (f,g)(x,y) = (f x,g y) quad "for" (x,y) in (P_1,P_2,phi). $
Indeed, we have
$
  psi(overline(f x)) = psi overline(f)(overline(x))
  = overline(g) phi(overline(x)) = overline(g) overline(y)
  = overline(g y).
$
Further, $(f,g)$ is an isomorphism if and only if both $f$ and $g$ are
isomorphisms. However, the module $(P_1,P_2,phi)$ defined in
@eq:patched-module-triple need not be $A$-projective, and we shall impose some
additional hypotheses to ensure this.

For convenience, we shall denote $A^((n))$ simply by $A^n$. Further, we set
$
  overline(A)_i = overline(A) times.o_(A_i) A_i tilde.equiv overline(A),
  quad i = 1,2,
$
and we identify both $overline(A)_1$ and $overline(A)_2$ with $overline(A)$
hereafter. We need two easy lemmas:

#lemma[
  Let $psi,psi' in GL_n lr((overline(A)))$ be such that
  $
    psi' = overline(phi)_2 psi overline(phi)_1
    quad "for some" phi_i in GL_n lr((A_i)), quad i = 1,2.
  $
  Then there is an isomorphism of $A$-modules
  $ (A_1^n,A_2^n,psi) tilde.equiv (A_1^n,A_2^n,psi'). $
] <lem:patched-free-module-equivalence>
#proof[
  The isomorphism is given by
  $
    (x,y) in (A_1^n,A_2^n,psi) -> (phi_1^(-1) x,phi_2 y)
    in (A_1^n,A_2^n,psi').
  $
]

As we shall see in @th:milnor-projective-patching, the converse of the lemma
holds under the additional hypothesis that either $g_1$ or $g_2$ is surjective.

#lemma[
  Suppose that in the fiber product @eq:ring-fiber-product-square, either $g_1$
  or $g_2$ is surjective. Then
  #enum(
    numbering: "(i)",
    [For all $phi in E(n,overline(A))$,
      $ (A_1^n,A_2^n,phi) tilde.equiv A^n. $],
    [For all $phi in GL_n lr((overline(A)))$, we have
      $
        (A_1^n,A_2^n,phi) plus.o (A_1^n,A_2^n,phi^(-1))
        tilde.equiv A^(2n),
      $
      and therefore
      $ (A_1^n,A_2^n,phi) in cal(P)(A). $],
  )
] <lem:patched-free-module-projectivity>
#source(121)
#proof[
  If (say) $g_1$ is surjective, every elementary matrix over $overline(A)$ lifts
  to one over $A_1$, so (i) follows from @lem:patched-free-module-equivalence.
  Then (ii) is immediate, using the identity @eq:whitehead-block-factorization.
]

We are now ready to prove

#theorem(name: "Theorem (Milnor)")[
  Suppose that in the fiber product @eq:ring-fiber-product-square, either $g_1$
  or $g_2$ is surjective. Let $P_i in cal(P)(A_i)$, $i = 1,2$, and let
  $phi: overline(P)_1 tilde.equiv overline(P)_2$ be an
  $overline(A)$-isomorphism, where
  $overline(P)_i = overline(A) times.o_(A_i) P_i$. Then the $A$-module
  $
    (P_1,P_2,phi) = lr(
      {(x,y): x in P_1,y in P_2,
        phi(overline(x)) = overline(y)}
    )
  $
  lies in $cal(P)(A)$. Further,
  $ A_i times.o_A (P_1,P_2,phi) tilde.equiv P_i, quad i = 1,2. $
  <eq:patched-module-base-change>
  Finally, let $Q_i in cal(P)(A_i)$, $i = 1,2$, and let
  $phi': overline(Q)_1 tilde.equiv overline(Q)_2$ be an
  $overline(A)$-isomorphism. Then $(P_1,P_2,phi) tilde.equiv (Q_1,Q_2,phi')$ as
  $A$-modules if and only if
  $
    phi' = overline(nu) phi overline(mu)^(-1)
    quad "for some isomorphisms" mu: P_1 tilde.equiv Q_1,
    quad nu: P_2 tilde.equiv Q_2.
  $
] <th:milnor-projective-patching>
#idx("Milnor's Theorem", target: [@th:milnor-projective-patching])
#proof[
  Choose $N_i in cal(P)(A_i)$ with $P_i plus.o N_i tilde.equiv A_i^n$,
  $i = 1,2$. Then $phi$ gives rise to an isomorphism $psi$, defined by
  composition of maps:
  $
    overline(A)_1^n plus.o overline(N)_1
    tilde.equiv overline(P_2 plus.o N_2 plus.o N_1)
    tilde.equiv overline(P_1 plus.o N_2 plus.o N_1)
    tilde.equiv overline(A)_2^n plus.o overline(N)_2.
  $
  Therefore by @lem:patched-free-module-projectivity,
  $
    (P_1,P_2,phi) plus.o (A_1^n plus.o N_1,A_2^n plus.o N_2,psi)
    tilde.equiv (A_1^(2n),A_2^(2n),phi plus.o psi) in cal(P)(A).
  $
  This shows that $(P_1,P_2,phi) in cal(P)(A)$. Also, since
  @eq:patched-module-base-change holds for triples of the form
  $(A_1^(2n),A_2^(2n),phi plus.o psi)$, it also holds for direct summands of
  such triples.

  #source(122)
  To complete the proof, let $M = (P_1,P_2,phi)$, $N = (Q_1,Q_2,phi')$. If
  $phi' = overline(nu) phi overline(mu)^(-1)$ for some $mu,nu$, then
  $(mu,nu): M tilde.equiv N$ is the desired $A$-isomorphism. Conversely, given
  an $A$-isomorphism $rho: M tilde.equiv N$, let
  $
    sigma_i: A_i times.o_A M tilde.equiv P_i,
    quad tau_i: A_i times.o_A N tilde.equiv Q_i, quad i = 1,2,
  $
  be the isomorphisms in @eq:patched-module-base-change. Consider the
  commutative diagram
  #patching-isomorphism-comparison
  Define
  $
    mu = tau_1 (1 times.o rho) sigma_1^(-1): P_1 -> Q_1,
    quad "and" nu = tau_2 (1 times.o rho) sigma_2^(-1): P_2 -> Q_2.
  $
  Then $mu,nu$ are isomorphisms for which
  $phi' overline(mu) = overline(nu) phi$, as desired.
]

The main result of the section is as follows:

#theorem(name: "Milnor’s Theorem")[
  Given a fiber product @eq:ring-fiber-product-square in which at least one of
  the maps $g_1$ and $g_2$ is surjective, there is an exact
  _Mayer–Vietoris sequence_
  $
    K_1 lr((A)) arrow.r^((f_1,f_2)) K_1 lr((A_1)) times K_1 lr((A_2))
    arrow.r^(g_1 times (1 slash g_2)) K_1 lr((overline(A))) \
    arrow.r^partial K_0 lr((A)) arrow.r^((f_1,f_2))
    K_0 lr((A_1)) plus.o K_0 lr((A_2))
    arrow.r^(g_1-g_2) K_0 lr((overline(A))),
  $
  <eq:mayer-vietoris-sequence>
  where $g_1 times (1 slash g_2): (x,y) ->
  g_1 lr((x)) slash g_2 lr((y))$.
] <th:milnor-mayer-vietoris>
#idx("Mayer-Vietoris sequence", target: [@th:milnor-mayer-vietoris])
#proof[
  A ring homomorphism $phi: A -> B$ induces homomorphisms of groups
  $K_i lr((A)) -> K_i lr((B))$, $i = 0,1$, so all of the above maps are
  well-defined, except that we must describe the connecting homomorphism
  $partial$. Identifying $overline(A)_1$ with $overline(A)_2$, each
  $phi: overline(A)_1^n tilde.equiv overline(A)_2^n$ may be viewed as an element
  of $GL_n lr((overline(A)))$. Put
  $ M(phi) = (A_1^n,A_2^n,phi) in cal(P)(A). $
  By @lem:patched-free-module-projectivity, $M(phi) tilde.equiv A^n$ if
  $phi in E_n lr((overline(A)))$. We now define
  $
    partial: K_1 lr((overline(A))) -> K_0 lr((A))
    quad "by" partial(phi) = [M(phi)] - [A^n]
    quad "for" phi in GL_n lr((overline(A))).
  $
  Since $partial lr((mat(phi, 0; 0, 1))) = partial(phi)$, and since $partial$ is
  trivial on $E(overline(A))$, it follows that $partial$ is well-defined on
  $K_1 lr((overline(A)))$. To show that $partial$ is a homomorphism, let
  $phi,psi in GL_n lr((overline(A)))$.
  #source(123)
  Then
  $
    partial lr((mat(phi, 0; 0, psi)))
    = lr([M lr((mat(phi, 0; 0, psi)))]) - [A^(2n)]
    = [M(phi)] - [A^n] + [M(psi)] - [A^n] \
    = partial(phi) + partial(psi).
  $
  However,
  $
    mat(phi, 0; 0, psi) = mat(phi psi, 0; 0, 1)
    quad "in" K_1 lr((overline(A)))
  $
  by @eq:whitehead-block-factorization, so
  $partial(phi psi) = partial(phi)+partial(psi)$ as desired. Using
  @lem:patched-free-module-equivalence–@th:milnor-projective-patching, it is
  easily verified that the composite of two successive maps in
  @eq:mayer-vietoris-sequence is $0$.

  We proceed to verify exactness at each position. First, let
  $(x_1,x_2) in ker(g_1-g_2)$. We may write
  $ x_i = [P_i] - [A_i^n], quad P_i in cal(P)(A_i), quad i = 1,2, $
  where $n$ is independent of $i$. Then $[overline(P)_1] = [overline(P)_2]$ in
  $K_0 lr((overline(A)))$, so $overline(P)_1$ is stably isomorphic to
  $overline(P)_2$ as $overline(A)$-module. Increasing $P_1$ and $P_2$, we may
  assume (after changing notation) that
  $overline(P)_1 tilde.equiv overline(P)_2$. By @th:milnor-projective-patching,
  there exists a module $P in cal(P)(A)$ such that
  $P_i tilde.equiv A_i times.o_A P$, $i = 1,2$; then
  $(x_1,x_2) = (f_1,f_2)([P]-[A^n])$, so $ker(g_1-g_2) = im(f_1, f_2)$.

  Next, let $x = [P]-[A^n] in ker(f_1, f_2)$, where $P in cal(P)(A)$. Writing
  $P_i = A_i times.o P$, we have $[P_i] = [A_i^n]$ in $K_0 lr((A_i))$,
  $i = 1,2$. Increasing $P$ and changing notation, we may assume that
  $P_i tilde.equiv A_i^n$, $i = 1,2$. If
  $kappa: overline(P)_1 tilde.equiv overline(P)_2$ is the canonical isomorphism,
  there is a commutative diagram
  #patching-free-trivialization
  for some $phi in GL_n lr((overline(A)))$. Therefore
  $P tilde.equiv (P_1,P_2,kappa) tilde.equiv (A_1^n,A_2^n,phi)$, so
  $x = [M(phi)]-[A^n] = partial(phi)$, as desired.

  We suppose next that $phi in GL_n lr((overline(A)))$ is such that
  $partial(phi) = 0$, that is, $[M(phi)] = [A^n]$ in $K_0 lr((A))$. Replacing
  $phi$ by $mat(phi, 0; 0, I)$ if need be, and changing notation, we may then
  assume that $M(phi) tilde.equiv A^n$, that is,
  $ (A_1^n,A_2^n,phi) tilde.equiv (A_1^n,A_2^n,1). $
  Then $phi in im g_1 times 1 slash g_2$ by @th:milnor-projective-patching.

  Finally, let $alpha_i in GL_n lr((A_i))$, $i = 1,2$, be such that
  $overline(alpha)_1 = overline(alpha)_2$ in $K_1 lr((overline(A)))$. Then
  $
    mat(overline(alpha)_1, 0; 0, I) in
    mat(overline(alpha)_2, 0; 0, I) dot E_m lr((overline(A))).
  $
  for some $m$ and some identity matrix $I$. Replacing $alpha_i$ by
  $mat(alpha_i, 0; 0, I)$ leaves the image of $alpha_i$ in $K_1 lr((A_i))$
  unchanged, and elements of $E_m lr((overline(A)))$ are trivial in
  $K_1 lr((overline(A)))$, so we now assume (after changing notation) that
  $overline(alpha)_1 = overline(alpha)_2$.
  #source(124)
  It follows at once from the fiber product
  #numbered-block(general-linear-fiber-square)
  <eq:general-linear-fiber-product>
  that the pair $(alpha_1,alpha_2)$ lifts to an element $alpha in GL_n lr((A))$.
  Thus the sequence @eq:mayer-vietoris-sequence is exact at
  $K_1 lr((A_1)) times K_1 lr((A_2))$, and the proof is complete.
]

As an illustration, we give a calculation due to Rim @bib:Rim1959:

#example[
  Let $G = chevron.l x: x^p = 1 chevron.r$, $p$ prime, and put
  $
    overline(ZZ) = ZZ slash p ZZ,
    quad R = ZZ[x] slash (Phi_p lr((x))) = ZZ[omega],
  $
  where $omega$ is a primitive $p$-th root of $1$. There is a fiber product
  #cyclic-prime-fiber-square
  in which all maps are surjective. The Mayer–Vietoris sequence becomes
  $
    K_1 lr((ZZ G)) -> K_1 lr((ZZ)) times K_1 lr((R))
    arrow.r^h K_1 lr((overline(ZZ))) -> K_0 lr((ZZ G))
    -> K_0 lr((ZZ)) plus.o K_0 lr((R)) -> K_0 lr((overline(ZZ))).
  $
  Now $K_1 lr((overline(ZZ))) tilde.equiv overline(ZZ)^dot$, and
  $R^dot -> overline(ZZ)^dot$ is surjective by the proof of
  @i:th:prime-cyclic-integral-lattice-classification, so $h$ is surjective. Thus
  the sequence
  $ 0 -> K_0 lr((ZZ G)) -> ZZ plus.o K_0 lr((R)) -> ZZ -> 0 $
  is exact, and so $K_0 lr((ZZ G)) tilde.equiv K_0 lr((R))$. Finally,
  $K_0 lr((R)) tilde.equiv ZZ plus.o op("Cl") R$ by
  @th:dedekind-projective-class-group. For more complicated calculations of this
  type, see Chapter @ch:class-groups.
] <exm:rim-cyclic-prime-projective-class-group>
#idx("Rim's Theorem", target: [@exm:rim-cyclic-prime-projective-class-group])

#remark(numbered: true)[
  In §@sec:milnor-k2 we shall define a Milnor group $K_2 lr((A))$, and shall
  prove that starting with a fiber product @eq:ring-fiber-product-square in
  which _both_ $g_1$ and $g_2$ are surjective, the exact sequence
  @eq:mayer-vietoris-sequence can be extended to the left:
  $
    K_2 lr((A)) -> K_2 lr((A_1)) times K_2 lr((A_2))
    -> K_2 lr((overline(A))) -> K_1 lr((A))
    -> K_1 lr((A_1)) times K_1 lr((A_2)) -> dots.
  $
  However, as shown by Swan @bib:Swan1971, the sequence does not in general
  extend further to the left, despite the existence of higher $K$-groups $K_n$,
  $n >= 3$.
] <rem:mayer-vietoris-higher-k-groups>

#source(125)
We conclude this section by showing that for a Wall square as in
@exm:wall-square, the analogues of
@lem:patched-free-module-projectivity–@th:milnor-mayer-vietoris remain valid,
despite the fact that neither of the maps $A -> hat(A)$ and
$hat(Lambda) -> hat(A)$ is surjective. We shall follow the treatment of this
topic given by Swan @bib:Swan1980.

Keeping the notation of @exm:wall-square, set
$
  hat(R) = product_P R_P,
  quad hat(K) = lr(
    {(alpha_P) in product_P K_P:
      alpha_P in R_P "a.e."}
  ),
$
where $P$ ranges over all maximal ideals of $R$. Since $Lambda$ is an
$R$-lattice, and $A$ is $K$-free, we have
$
  hat(Lambda) = hat(R) times.o_R Lambda,
  quad hat(A) = hat(K) times.o_K A.
$
For each $P$, the ring $Lambda_P$ has its natural $P$-adic topology, in which
$lr({P^n Lambda_P: n >= 0})$ is a fundamental system of neighborhoods of $0$.
Since $hat(Lambda) = product_P Lambda_P$, it acquires the product topology. We
then topologize $hat(A)$ by requiring $hat(Lambda)$ to be an open subgroup of
$hat(A)$. Note that $K$ is dense in $hat(K)$ (by the Strong Approximation
Theorem), and that $hat(R)$ is an open subgroup of $hat(K)$.

The topology on $hat(A)$ extends to a topology on $hat(A)^n$ for each $n$, and
hence to each summand of $hat(A)^n$. Thus, each $Y in cal(P)(hat(A))$ has a
topology, and likewise so does each $X in cal(P)(hat(Lambda))$.

#proposition[
  Given a Wall square @exm:wall-square, let $V in cal(P)(A)$ and
  $X in cal(P)(hat(Lambda))$ be such that
  $ hat(K) times.o_K V tilde.equiv hat(K) times.o_(hat(R)) X $
  as $hat(A)$-modules. Then there exists an $M in cal(P)(Lambda)$ such that
  $
    K times.o_R M tilde.equiv V,
    quad hat(R) times.o_R M tilde.equiv X,
  $
  these isomorphisms being consistent with the given isomorphism.
] <prop:wall-projective-patching>
#proof[
  Replacing $V$ by an isomorphic copy, we may assume that
  $ hat(K) times.o_(hat(R)) X = hat(K) times.o_K V = hat(V), $
  with both $V$ and $X$ embedded in $hat(V)$. Define $M = X inter V$. Now $V$ is
  dense in $hat(V)$, since $K$ is dense in $hat(K)$. Also, $X$ is an open subset
  of $hat(V)$ since $hat(R)$ is an open subgroup of $hat(K)$. It follows at once
  that $M$ is dense in $X$, and therefore $hat(R) M = X$. Since
  $hat(V) = hat(K) X = hat(K) dot K M$, we conclude that $K M = V$.

  It remains for us to check that $M in cal(P)(Lambda)$. We may choose a finite
  set of elements $lr({m_i})$ from $M$ such that $sum hat(R) m_i = X$. Then
  $ hat(R) times.o_R (M slash sum R m_i) = 0, $
  so $M = sum R m_i$ because $hat(R)$ is faithfully flat as $R$-module.
  #source(126)
  Therefore $M$ is a $Lambda$-lattice, and then $M in cal(P)(Lambda)$ by
  @i:prop:projectivity-localization. This completes the proof. (The result
  should be compared with @i:prop:localization-completion-lattices(iv) and
  @bib:Reiner1975[MO (5.2ii)].)
]

Having established the analogue of @th:milnor-projective-patching, we now obtain

#theorem(name: "Theorem (C. T. C. Wall)")[
  Given a Wall square @exm:wall-square, there is an exact Mayer–Vietoris
  sequence
  $
    K_1 lr((Lambda)) -> K_1 lr((A)) times K_1 lr((hat(Lambda)))
    -> K_1 lr((hat(A))) -> K_0 lr((Lambda))
    -> K_0 lr((A)) plus.o K_0 lr((hat(Lambda))) -> K_0 lr((hat(A))).
  $
  <eq:wall-mayer-vietoris-sequence>
] <th:wall-mayer-vietoris>
#idx("Wall's Theorem", target: [@th:wall-mayer-vietoris])
#proof[
  The proof of @th:milnor-mayer-vietoris carries over to the present case,
  except for that part of the argument which shows that
  $M(phi) tilde.equiv Lambda^n$ whenever $phi in E(n,hat(A))$. Replacing $phi$
  by $mat(phi, 0; 0, I)$ if need be, and changing notation, we may assume that
  $n >= 3$. Let $E(hat(A)),E(A)$, etc., be the elementary subgroups defined in
  §@ss:elementary-matrices, and keep the notation of
  @eq:elementary-matrix-definition and @eq:steinberg-elementary-relations. We
  are going to show that the Wall square is _E-surjective_ in the sense of Bass
  @bib:Bass1968, page 360, Def. 3.3, that is,
  $
    phi = phi_1 phi_2 quad "for some" phi_1 in E(A),
    quad phi_2 in E(hat(Lambda)).
  $
  <eq:wall-elementary-factorization>
  Once this is known, we obtain $[M(phi)] = [Lambda^n]$ in $K_0 lr((Lambda))$ by
  @lem:patched-free-module-equivalence.

  To prove @eq:wall-elementary-factorization, we note that
  $hat(A) = A + hat(Lambda)$ by Exercise @exc:wall-adele-sum, and therefore
  $E(hat(A))$ is generated by its subgroups $E(A)$ and $E(hat(Lambda))$. Set
  $
    E(A) E(hat(Lambda)) = lr(
      {bold(X) bold(Y): bold(X) in E(A),
        bold(Y) in E(hat(Lambda))}
    ).
  $
  It suffices to prove that for each $bold(X) in E(A)$ and each elementary
  matrix $bold(E)_(i j) lr((y))$, $y in hat(Lambda)$, we have
  $
    bold(X)^(-1) bold(E)_(i j) lr((y)) bold(X)
    in E(A) E(hat(Lambda)).
  $
  Choose a nonzero $r in R$ such that both $r bold(X)$ and $r bold(X)^(-1)$ have
  entries in $Lambda$. Since $Lambda slash r^4 Lambda tilde.equiv
  hat(Lambda) slash r^4 hat(Lambda)$, we may write $y = z+r^4 w$, $z in Lambda$,
  $w in hat(Lambda)$. Then
  $
    bold(X)^(-1) bold(E)_(i j) lr((y)) bold(X)
    = (bold(X)^(-1) bold(E)_(i j) lr((z)) bold(X))
    (bold(X)^(-1) bold(E)_(i j) lr((r^4 w)) bold(X)),
  $
  and the first factor on the right surely lies in $E(A)$. To handle the second
  factor, choose $k != i,j$, and use formula @eq:steinberg-elementary-relations
  to obtain
  $
    bold(X)^(-1) bold(E)_(i j) lr((r^4 w)) bold(X)
    = [bold(X)^(-1) bold(E)_(i k) lr((r^2)) bold(X),
      bold(X)^(-1) bold(E)_(k j) lr((r^2 w)) bold(X)].
  $
  Using the notation of @eq:elementary-matrix-definition, we have
  $
    bold(X)^(-1) bold(E)_(i k) lr((r^2)) bold(X)
    = bold(I) + (r bold(X)^(-1)) e_(i k) (r bold(X))
    in GL(hat(Lambda)),
  $
  where $bold(I)$ is the identity matrix. Likewise,
  $bold(X)^(-1) bold(E)_(k j) lr((r^2 w)) bold(X) in GL(hat(Lambda))$, so the
  above commutator lies in the commutator subgroup $GL'(hat(Lambda))$, that is,
  in $E(hat(Lambda))$. This completes the proof of
  @eq:wall-elementary-factorization, as well as that of Wall’s Theorem
  @th:wall-mayer-vietoris.
]

#source(127)
#remarks[
  #enum(
    numbering: "(i)",
    [Let $phi: A -> B$ be a homomorphism of arbitrary rings, and let $S$ be a
      multiplicative subset of the center of $A$ such that no element of $S$ is
      a zero divisor in $A$. Suppose that $phi(S)$ lies in the center of $B$,
      and consists only of non-zero divisors in $B$. Let $S^(-1) A$ denote the
      quotient ring of $A$ relative to $S$ (see §@i:ss:localization), and
      $S^(-1) B$ that of $B$ relative to $phi(S)$. Assume further that for each
      $s in S$, $phi$ induces an isomorphism (of $A$-modules)
      $A slash s A tilde.equiv B slash s B$. The square
      #karoubi-square
      is called a _Karoubi square_. (For example, the Wall square
      @exm:wall-square is of this form, if we take $S = R - lr({0})$.)

      Karoubi proved that such squares always yield Mayer–Vietoris sequences of
      type @eq:mayer-vietoris-sequence, and Murthy showed that every Karoubi
      square is _E-surjective_. For proofs and generalizations, see Swan
      @bib:Swan1980.],
    [Given a Wall square @exm:wall-square, there is an exact sequence
      $
        dots -> K_n lr((Lambda))
        -> K_n lr((A)) plus.o K_n lr((hat(Lambda)))
        -> K_n lr((hat(A))) -> K_(n-1) lr((Lambda))
        -> dots -> K_0 lr((hat(A))),
      $
      where the $lr({K_n})$ are the Quillen $K$-groups. This follows from
      Quillen’s Localization Sequence in @rem:quillen-localization-sequence; for
      details, see Swan @bib:Swan1980, §5.],
  )
] <rem:karoubi-squares-higher-mayer-vietoris>
#idx("Karoubi square", target: [@rem:karoubi-squares-higher-mayer-vietoris])
#idx("E-surjective", target: [@eq:wall-elementary-factorization])

#exercises-heading

#exercise[
  Let $S$ and $T$ be multiplicatively closed subsets of the center of ring $A$
  such that $A s+A t = A$ for all $s in S$, $t in T$, and let
  $S T = lr({s t: s in S,t in T})$. Show that there is a fiber product diagram
  #localization-fiber-square
] <exc:comaximal-central-localizations-fiber-product>

#exercise[
  Let $P = (P_1,P_2,phi)$, $P' = (P'_1,P'_2,phi')$ as in
  @eq:patched-module-triple. Show that $P tilde.equiv P'$ if
  $phi' overline(alpha)_1 = overline(alpha)_2 phi$ for some
  $alpha_i: P_i tilde.equiv P'_i$, $i = 1,2$.
] <exc:patched-module-triple-isomorphism>

#exercise[
  Assume $g_1$ surjective in @eq:ring-fiber-product-square, and let
  $phi in GL_n lr((overline(A)))$. Let $mu in E_(2n) lr((A_1))$ be such that
  $ overline(mu) = mat(phi, 0; 0, phi^(-1)), $
  and let
  $
    e_i = mat(I, 0; 0, 0) in M_(2n) lr((A_i)),
    quad e = (mu^(-1) e_1 mu,e_2)
    in M_(2n) lr((A_1)) plus.o M_(2n) lr((A_2)).
  $
  Show that there is a fiber product diagram
  #matrix-fiber-square
  and that $e in M_(2n) lr((A))$ is an idempotent for which
  $ M(phi) tilde.equiv A^(2n) dot e. $
] <exc:patched-projective-idempotent>

#source(128)
#exercise[
  Let $k$ be a field, $A = k + x^2 k[x]$, where $x$ is an indeterminate over
  $k$. Use the fiber product
  #cusp-fiber-square
  to prove that
  $
    K_0 lr((A)) tilde.equiv ZZ plus.o k^+,
    quad k^+ = "additive group of" k.
  $
] <exc:cusp-projective-class-group>

#exercise[
  In the Wall square @exm:wall-square, prove that $A + hat(Lambda) = hat(A)$.
  #hint([@exc:wall-adele-sum])[
    Use the Strong Approximation Theorem @i:th:strong-approximation.
  ]
] <exc:wall-adele-sum>

#exercise[
  Given a Wall square @exm:wall-square, deduce the exactness of
  $
    K_1 lr((A)) times K_1 lr((hat(Lambda)))
    -> K_1 lr((hat(A))) arrow.r^(partial') K_0 lr((Lambda))
    -> K_0 lr((A)) plus.o K_0 lr((hat(Lambda))) -> K_0 lr((hat(A)))
  $
  directly from the Localization Sequence
  @cor:algebra-whitehead-localization
  $
    K_1 lr((Lambda)) -> K_1 lr((A)) arrow.r^partial K_0 lr((cal(T)))
    -> K_0 lr((Lambda)) -> K_0 lr((A)).
  $
  #hint([@exc:wall-mayer-vietoris-from-localization], caption: [Hint (Swan
    @bib:Swan1980, pages 165–166):])[
    For $phi in GL_n lr((hat(A)))$,
    $partial'(phi) = [Lambda^n] - [(hat(Lambda)^n,A^n,phi)]$, where the triple
    $(hat(Lambda)^n,A^n,phi)$ is defined as in @eq:patched-module-triple, and is
    isomorphic to $A^n inter phi(hat(Lambda)^n)$.
  ]
] <exc:wall-mayer-vietoris-from-localization>

#exercise[
  Consider a fiber product as in Exercise
  @exc:comaximal-central-localizations-fiber-product, in which no element of $S$
  is a zero divisor. Show that the analogues of
  @prop:wall-projective-patching–@eq:wall-elementary-factorization are valid for
  this case. #hint([@exc:localization-mayer-vietoris])[
    The result is due to Murthy; see Gersten @bib:Gersten1973, Problem 4.
  ] (Ref. in Swan @bib:Swan1980, p. 164).
] <exc:localization-mayer-vietoris>

#exercise[
  Given a fiber product @exm:ideal-quotient-fiber-product in which the ring $A$
  is left noetherian, show that there exists an exact sequence of groups
  $
    G_0 lr((A slash (I+J)))
    -> G_0 lr((A slash I)) plus.o G_0 lr((A slash J))
    -> G_0 lr((A slash (I inter J))) -> 0.
  $
  #hint([@exc:fiber-product-grothendieck-sequence])[
    See Bass @bib:Bass1981, Th. 4.2. The result can be used to provide a proof
    of Lenstra’s formula @eq:lenstra-abelian-grothendieck-formula.
  ]
] <exc:fiber-product-grothendieck-sequence>
