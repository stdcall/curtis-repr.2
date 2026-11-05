#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/43-polynomial.typ": polynomial-k-g-square

== $K$-Theory of Polynomial Rings <sec:polynomial-k-theory>

Let $R$ be a left noetherian ring of finite global dimension, and let
$R' = R[x_1,dots,x_n]$, where the $lr({x_i})$ are indeterminates which commute
with each other and with all elements of $R$. Ground ring extension
$R' times.o_R ast$ gives rise to homomorphisms $K_i lr((R)) -> K_i lr((R'))$,
$i = 0,1$. Here, we shall use the ideas of §@ss:regular-rings to prove:

#source(129)
#theorem(title: [Grothendieck])[
  $K_0 lr((R)) tilde.equiv K_0 lr((R'))$.
] <th:grothendieck-polynomial-k0>
#idx("Grothendieck's Theorem", target: [@th:grothendieck-polynomial-k0])

#theorem(title: [Bass–Heller–Swan])[
  $K_1 lr((R)) tilde.equiv K_1 lr((R'))$.
] <th:bass-heller-swan-polynomial-k1>
#idx("Bass-Heller-Swan Theorem", target: [@th:bass-heller-swan-polynomial-k1])

When $R$ is a P.I.D., this gives
$K_0 lr((R')) tilde.equiv K_0 lr((R)) tilde.equiv ZZ$, and therefore every
$P in cal(P)(R')$ is stably free. This result led Serre to conjecture that each
such $P$ is in fact free. Seshadri @bib:Seshadri1958 proved a special case of
this conjecture (see @th:seshadri-polynomial-projectives), and the general
result was established independently by Quillen and Suslin. They proved a
stronger result:

#theorem(name: "Quillen–Suslin Theorem", numbered: false)[
  Let $R$ be a Dedekind domain, and let $R' = R[x_1,dots,x_n]$ be a polynomial
  domain over $R$. Then each $P in cal(P)(R')$ is of the form
  $P tilde.equiv R' times.o_R X$ for some $X in cal(P)(R)$. If $R$ is a P.I.D.,
  each $P in cal(P)(R')$ is $R'$-free.
] <th:quillen-suslin>
#idx("Quillen-Suslin Theorem", target: [@th:quillen-suslin])

We shall content ourselves with a proof of Seshadri’s Theorem. For a proof of
the Quillen–Suslin Theorem, see Lam @bib:Lam1978 or Rotman @bib:Rotman1979.

Our first task is to establish that $K_0 lr((R)) tilde.equiv K_0 lr((R'))$
whenever $R$ is a left noetherian ring of finite global dimension. We need to
know that $R'$ inherits these properties from $R$. Let us recall a well-known
result (see, e.g., Jacobson @bib:Jacobson1980, §7.9):

#theorem(name: "Hilbert Basis Theorem")[
  If $R$ is a left noetherian ring, then so is $R[x_1,dots,x_n]$.
] <th:hilbert-basis>
#idx("Hilbert Basis Theorem", target: [@th:hilbert-basis])

Thus, if $R$ is left noetherian, so is $R'$. Our next step is to show that if
$R$ has finite global dimension, then so does $R'$.#idx("Global dimension") The
proof of this result depends on the _characteristic sequence_ of an
endomorphism, as we now explain. Suppose that $R$ is arbitrary, and let
$R' = R[x]$. For each $R$-module $M$, define $M' = R' times.o_R M$. Each
$m' in M'$ is uniquely expressible as a finite sum
$
  m' = sum_0^infinity x^i times.o m_i,
  quad m_i in M, quad m_i = 0 "a.e."
$
Now let $alpha in End_R M$, and make $M$ into a left $R'$-module by letting $x$
act as $alpha$ on $M$. We may then define an $R'$-homomorphism
$alpha^ast: M' -> M$ by
$
  alpha^ast lr((h(x) times.o m)) = h(x) m = h(alpha) m,
  quad "for all" h(x) in R', quad m in M.
$
There is also an $R'$-homomorphism
$
  x-alpha: M' -> M', quad "where"
  (x-alpha)(h(x) times.o m) = x h(x) times.o m - h(x) times.o alpha m.
$
The relation between the maps $alpha^ast$ and $x-alpha$ is given by:

#source(130)
#theorem(name: "Characteristic Sequence of an Endomorphism")[
  For each $alpha in End_R M$, there is an $R'$-exact sequence
  $ 0 -> M' arrow.r^(x-alpha) M' arrow.r^(alpha^ast) M -> 0, $
  the _characteristic sequence_ of $alpha$.
] <th:characteristic-endomorphism-sequence>
#idx(
  "Characteristic sequence",
  target: [@th:characteristic-endomorphism-sequence],
)
#proof[
  It is trivial to check that $alpha^ast compose (x-alpha) = 0$. Next, let
  $sum x^i times.o m_i in M'$, where $m_i = 0$ a.e., and let us try to solve
  $
    sum_0^infinity x^i times.o m_i
    = (x-alpha) sum_0^infinity x^i times.o v_i
    = sum_0^infinity (x^(i+1) times.o v_i-x^i times.o alpha v_i)
  $
  for elements $v_i in M$. Supposing that $v_k = v_(k+1) = dots = 0$, we obtain
  a system of equations
  $
    m_0 = -alpha v_0, quad m_1 = -alpha v_1+v_0, dots,
    m_k = v_(k-1),
  $
  and $m_(k+1) = m_(k+2) = dots = 0$. Using the last $k$ equations above, we
  solve successively for $v_(k-1),dots,v_0$. Substituting into the first
  equation, we obtain
  $ alpha^k m_k+alpha^(k-1) m_(k-1)+dots+alpha m_1+m_0 = 0, $
  that is, $alpha^ast lr((sum x^i times.o m_i)) = 0$. This condition is
  necessary and sufficient that $sum x^i times.o m_i in im(x-alpha)$, so
  $ker alpha^ast = im(x-alpha)$. Finally, the above formulas also show that if
  each $m_i = 0$, then each $v_j = 0$, and thus the map $x-alpha$ is injective.
  This completes the proof.
]

In @def:global-dimension, we defined the (left) global dimension of the ring
$R$. We now prove a weak version of the Hilbert Syzygy Theorem:

#theorem[
  For any ring $R$,
  $ op("gl. dim.") R[x] <= 1+op("gl. dim.") R. $
  Therefore
  $ op("gl. dim.") F[x_1,dots,x_n] <= n $
  for any field $F$ and any $n >= 1$.
] <th:polynomial-global-dimension-bound>
#idx("Hilbert Syzygy Theorem", target: [@th:polynomial-global-dimension-bound])
#idx("Global dimension", target: [@th:polynomial-global-dimension-bound])
#proof[
  Let $R' = R[x]$, and let $op("gl. dim.") R = m$. Then for each $R$-module $M$,
  there exists an $R$-exact sequence
  $
    0 -> P_m -> dots -> P_0 -> M -> 0,
    quad "where" P_i "is" R"-projective".
  $
  Since $R'$ is $R$-free, $R' times.o_R ast$ preserves exactness, and we obtain
  an $R'$-exact sequence
  $ 0 -> P'_m -> dots -> P'_0 -> M' -> 0. $
  #source(131)
  This shows that #named-equation(name: [$(ast)$])[
    $ op("hd")_(R') M' <= m quad "for every" R"-module" M. $
  ] <eq:polynomial-induced-homological-dimension>
  Now let $M$ be any $R'$-module, and define $alpha in End_R M$ as left
  multiplication by $x$. Viewing $M$ as an $R$-module, and making it into an
  $R'$-module by letting $x$ act as $alpha$, we recover the original $R'$-module
  $M$. Consider now the characteristic sequence
  @th:characteristic-endomorphism-sequence. By
  @eq:polynomial-induced-homological-dimension and Exercise
  @exc:homological-dimension-short-exact, we obtain
  $
    op("hd")_(R') M <= op("Max") (op("hd")_(R') M',
      1+op("hd")_(R') M') <= m+1.
  $
  This shows that $op("gl. dim.") R' <= 1+op("gl. dim.") R$. Since
  $op("gl. dim.") F = 0$, the rest of the theorem is clear.
]

It is not hard to prove a stronger version of the above theorem:
$ op("gl. dim.") R[x] = 1+op("gl. dim.") R, $
for $R$ left noetherian of finite global dimension (see Rotman @bib:Rotman1979,
Th. 9.34). Thus
$
  op("gl. dim.") F[x_1,dots,x_n] = n,
  quad op("gl. dim.") R[x_1,dots,x_n] = n+1,
$
for $F$ a field, and $R$ a Dedekind domain not a field.

Now let $R$ be any left noetherian ring of finite global dimension, and let
$R' = R[x_1,dots,x_n]$. Then $R'$ has the same properties, by @th:hilbert-basis
and @th:polynomial-global-dimension-bound. In order to prove Grothendieck’s
result that $K_0 lr((R)) tilde.equiv K_0 lr((R'))$, it suffices to treat the
case $n = 1$, so hereafter let $R' = R[x]$. The following proof was supplied to
the authors by Swan.

The inclusion $R subset.eq R'$ gives a commutative diagram
#polynomial-k-g-square
The vertical maps are isomorphisms, by @cor:regular-ring-k-g-isomorphisms. Next,
the surjection $R' -> R' slash x R' = R$ induces a map
$phi': K_0 lr((R')) -> K_0 lr((R))$. Clearly $phi' phi = 1$, so $phi$ is
injective, and it remains for us to show that $psi$ (and hence also $phi$) is
surjective.

Given any f.g. $R'$-module $Y$, there is an $R'$-exact sequence
$ 0 -> L -> R' times.o F -> Y -> 0, $
where $F = R^((k))$ for some finite $k$, and $times.o$ means $times.o_R$. Then
$[Y] = [R' times.o F]-[L]$ in $G_0 lr((R'))$, and we must show that
$[L] in im psi$.
#source(132)
Define
$
  M = L inter plus.o.big_(i=0)^n (x^i times.o F)
  supset.eq N = L inter plus.o.big_(i=0)^(n-1) (x^i times.o F),
$
where $L$ is viewed as $R'$-submodule of
$R' times.o F = plus.o.big_0^infinity (x^i times.o F)$, and where $n$ is chosen
large enough that $M$ contains a set of $R'$-generators of $L$. Note that $M$
and $N$ are f.g. $R$-submodules of $L$, and that #named-equation(
  name: [$(ast)$],
)[
  $ m in M, quad x m in M ==> m in N. $
] <eq:polynomial-degree-cutoff>
Now define $alpha in End_R L$ as left multiplication by $x$. Since
$x N subset.eq M$, the characteristic sequence
@th:characteristic-endomorphism-sequence, for $alpha$ acting on $L$, yields a
sequence of $R'$-modules
$
  0 -> R' times.o N arrow.r^(x-alpha) R' times.o M
  arrow.r^(alpha^ast) L -> 0.
$
<eq:polynomial-generator-characteristic-sequence>
The map $alpha^ast$ is surjective, while $x-alpha$ is injective. We claim that
the sequence @eq:polynomial-generator-characteristic-sequence is exact, and it
suffices to show that $ker alpha^ast subset.eq im(x-alpha)$, the reverse
inclusion being obvious. Let
$ u = sum_(i=0)^k x^i times.o m_i in ker alpha^ast, quad m_i in M. $
As in the proof of @th:characteristic-endomorphism-sequence, we obtain
$ m_0 = -x v_0, quad m_1 = -x v_1+v_0, dots, m_k = v_(k-1), $
and clearly each $v_i in M$. These equations show that also each $x v_i in M$,
so by @eq:polynomial-degree-cutoff above, it follows that each $v_i in N$. Thus
$u in im(x-alpha)$, which completes the proof that
@eq:polynomial-generator-characteristic-sequence is exact. But then
$ [L] = [R' times.o M]-[R' times.o N] in psi lr({G_0 lr((R))}), $
and so we have proved that $K_0 lr((R)) tilde.equiv K_0 lr((R'))$.

Turning next to the proof of the Bass–Heller–Swan Theorem
@th:bass-heller-swan-polynomial-k1, we need only treat the case $n = 1$, so let
$R' = R[x]$. A matrix $bold(N) in M_n lr((R))$ is _nilpotent_ if $bold(N)^d = 0$
for some $d$; then $1+bold(N)$ is called _unipotent_, and lies in
$GL_n lr((R))$. We now show that #named-equation(name: [$(ast)$])[
  $
    bold(N) in M_n lr((R)), quad 1+x bold(N) in GL_n lr((R'))
    ==> bold(N) "nilpotent".
  $
] <eq:polynomial-unit-nilpotence>
#idx("Unipotent", target: [@eq:polynomial-unit-nilpotence])
Indeed, embed $R'$ in the ring $R'' = R[[x]]$ of formal power series in $x$.
Then
$
  (1+x bold(N))^(-1) = 1-x bold(N)+x^2 bold(N)^2-dots
  in GL_n lr((R'')).
$
But the left-hand side lies in $GL_n lr((R'))$, so $bold(N)^d = 0$ for all
sufficiently large $d$.

#source(133)
Let $tau: K_1 lr((R)) -> K_1 lr((R'))$ be $R' times.o ast$, where $times.o$
means $times.o_R$. Since the composite of the ring homomorphisms
$ R -> R' -> R' slash x R' = R $
is the identity map, we see at once that $tau$ is injective. The difficulty lies
in proving $tau$ surjective.

For $bold(M)(x) in GL_n lr((R'))$, let $bold(M)(0)$ be the matrix obtained from
$bold(M)(x)$ by setting $x = 0$ in each entry of $bold(M)(x)$. Clearly
$bold(M)(0) in GL_n lr((R))$. Setting
$
  bold(T) = bold(M)(0)^(-1) bold(M)(x)
  = 1+x bold(T)_1+dots+x^k bold(T)_k in GL_n lr((R')),
$
where each $bold(T)_i in M_n lr((R))$, we need only show that
$bold(T) in im tau$. If $bold(I)$ denotes the $n times n$ identity matrix, then
$bold(T) = mat(bold(T), 0; 0, bold(I))$ in $K_1 lr((R'))$. Elementary row and
column operations in $GL_(2n) lr((R'))$ give
$
  mat(bold(T), 0; 0, bold(I)) ~ mat(bold(T), x bold(I); 0, bold(I))
  ~ mat(bold(T)-x bold(A), x bold(I); -bold(A), bold(I))
$
for any $bold(A) in M_n lr((R'))$. Assuming $k > 1$, choose
$bold(A) = x^(k-1) bold(T)_k$. Then in $K_1 lr((R'))$ we have
$bold(T) = bold(T)^ast$, where $bold(T)^ast$ has no terms of degree $>= k$.
Continuing with $k-1$ in place of $k$, we find eventually that in $K_1 lr((R'))$
we have $bold(T) = 1+x bold(N)$ for some $bold(N) in M_m lr((R))$ for some $m$.
We are trying to prove that $bold(T) in im tau$, and it suffices to show that
$1+x bold(N)$ is the trivial element of $K_1 lr((R'))$. Note that $bold(N)$ is
nilpotent by @eq:polynomial-unit-nilpotence above, so $1+x bold(N)$ is a
unipotent matrix in $GL_m lr((R'))$.

Let $F$ be the free $R'$-module of rank $m$ on which $1+x bold(N)$ acts, and let
$theta$ be the nilpotent endomorphism of $F$ corresponding to the matrix
$x bold(N)$. If $theta^d = 0$, there is a descending chain of $R'$-modules
$
  F supset theta(F) supset theta^2 lr((F)) supset dots
  supset theta^d lr((F)) = 0,
$
and $1+theta$ acts as identity on each quotient factor. But then $[F,1+theta]$
is the trivial element of the group $G_1 lr((R'))$ defined in
@def:whitehead-determinantal-group. However,
$G_1 lr((R')) tilde.equiv K_1 lr((R'))$ by @cor:regular-ring-k-g-isomorphisms,
since the ring $R'$ is left regular. This shows that $1+theta$ is trivial in
$K_1 lr((R'))$, as desired, and the proof of @th:bass-heller-swan-polynomial-k1
is completed.

#remarks[
  #enum(
    numbering: "(i)",
    [Quillen showed that $K_n lr((R)) tilde.equiv K_n lr((R'))$ for $n >= 0$,
      where $R'$ is as in @th:grothendieck-polynomial-k0. (See Quillen
      @bib:Quillen1973, page 114, Corollary of Theorem 8.)],
    [The proofs of @th:grothendieck-polynomial-k0 and
      @th:bass-heller-swan-polynomial-k1 work equally well whenever the ring $R$
      is left regular (see @def:regular-ring).],
    [If $R$ is any left regular ring, then
      $
        K_1 lr((R[x,x^(-1)])) tilde.equiv
        K_1 lr((R)) plus.o K_0 lr((R)).
      $
      For a proof, see Swan @bib:Swan1968, (16.5).],
    [#source(134)
      Let $R$ be left regular, and let $X$ be a set of noncommuting
      indeterminates, each of which commutes with all elements of $R$. Let
      $R' = R lr({X})$ be the ring of all polynomials in the variables in $X$,
      with coefficients in $R$. Then the inclusion $R subset.eq R lr({X})$ gives
      an isomorphism $K_1 lr((R)) tilde.equiv K_1 lr((R lr({X})))$. The result
      is due to Gersten; see Exercise @exc:free-associative-polynomial-k1.],
  )
] <rem:polynomial-k-theory-extensions>

We conclude this section with

#theorem(title: [Seshadri @bib:Seshadri1958])[
  Let $R$ be a Dedekind domain with quotient field $F$, and let $R' = R[x]$
  where $x$ is an indeterminate. Then every $Y in cal(P)(R')$ is an _extended
  module_, that is,
  $ Y tilde.equiv R' times.o_R M quad "for some" M in cal(P)(R). $
] <th:seshadri-polynomial-projectives>
#idx("Seshadri's Theorem", target: [@th:seshadri-polynomial-projectives])
#idx("Extended module", target: [@th:seshadri-polynomial-projectives])
#proof[
  Clearly, every extended module $R' times.o_R M$ lies in $cal(P)(R')$.
  Conversely, let $Y in cal(P)(R')$ be embedded in $F Y = F times.o_R Y$. Then
  $F Y tilde.equiv F[x] times.o_(R') Y in cal(P) lr([F[x]])$. Since $F[x]$ is a
  P.I.D., $F Y$ is a free $F[x]$-module, and we may write
  $
    F Y = plus.o.big_(i=1)^n F[x] y_i,
    quad "with each" y_i in Y.
  $
  Put $V = plus.o R' y_i$, a free $R'$-submodule of $Y$. Then $V$ is of course
  an extended module, and $Y slash V$ is an $R$-torsion $R'$-module. Thus
  $I Y subset.eq V subset.eq Y$ for some nonzero ideal $I$ of $R$. We now show,
  by induction on the number of prime ideal factors of $I$, that $Y$ is also an
  extended module. (The case $R = F$ is trivial, and excluded from the
  argument.) It suffices to prove:

  #lemma(numbered: false)[
    Suppose we are given $Y in cal(P)(R')$ and inclusions
    $I P Y subset.eq V subset.eq Y$, where $P$ is a maximal ideal of $R$, $I$
    any nonzero ideal of $R$, and $V$ an extended module. Then there exists an
    extended module $W$ such that $I Y subset.eq W subset.eq Y$.
  ] <lem:seshadri-prime-ideal-step>

  To prove the lemma, suppose that $V = R' times.o_R M$ for some
  $M in cal(P)(R)$. By Steinitz’s Theorem @i:th:steinitz we can express $M$ as
  an external direct sum of nonzero ideals $lr({A_i})$ of $R$, and then
  $
    V = plus.o.big_(i=1)^n (R' times.o_R A_i) v_i
    = plus.o.big_(i=1)^n A_i lr([x]) v_i,
  $
  Choose $t_i in A_i without P A_i$, and replace $A_i$ by $t_i^(-1) A_i$ and
  $v_i$ by $t_i v_i$. We may thus assume that $1 in A_i$ and $(A_i)_P = R_P$,
  with each $v_i in V$. Let bars denote reduction mod $P$. Then
  $
    overline(V) = V slash P V = plus.o overline(A)_i lr([x]) overline(v)_i
    tilde.equiv plus.o overline(R)[x] overline(v)_i,
  $
  since $overline(A)_i tilde.equiv overline(R)$ by
  @i:eq:fractional-ideal-quotient.

  #source(135)
  The inclusion $V subset.eq Y$ induces an $overline(R)[x]$-homomorphism
  $f: overline(V) -> overline(Y)$ with kernel
  $ U_1 = frac(V inter P Y, P V) subset.eq overline(V). $
  If $U_1 = 0$ then
  $ I P Y subset.eq V inter P Y = P V ==> I Y subset.eq V, $
  so we may choose $W = V$ and we are done. Suppose for the rest of the proof
  that $U_1 != 0$. Since $f(overline(V))$ is an $overline(R)[x]$-submodule of
  $overline(Y)$, it is $overline(R)[x]$-free by
  @i:prop:hereditary-free-submodules, and therefore the sequence
  $ 0 -> U_1 -> overline(V) -> f(overline(V)) -> 0 $
  is split. Thus $overline(V) = U_1 plus.o U_2$, and $U_1$ is a free
  $overline(R)[x]$-module of rank $r$, for some positive integer $r <= n$.

  By the Structure Theorem for modules over a P.I.D., we can find an
  $epsilon in Aut_(overline(R)[x]) overline(V)$ such that
  $
    epsilon lr({plus.o.big_(i=1)^r overline(R)[x] overline(v)_i}) = U_1,
    quad epsilon lr(
      {plus.o.big_(i=r+1)^n
        overline(R)[x] overline(v)_i}
    ) = U_2.
  $
  Relative to the basis $lr({overline(v)_i})$ of $overline(V)$, we may represent
  $epsilon$ by a matrix over $overline(R)[x]$, and then we may write
  $epsilon = alpha beta$ where $alpha in E_n lr((overline(R)[x]))$ and $beta$ is
  diagonal. Therefore
  $
    U_1 = alpha beta lr({plus.o overline(R)[x] overline(v)_i})
    = alpha lr({plus.o overline(R)[x] overline(v)_i}).
  $
  Put $J_(i j) = (A_i A_j^(-1)) inter R$. Since $(J_(i j))_P = R_P$, we have
  $J_(i j) + P = R$. Thus each coefficient of an elementary factor of $alpha$
  lifts to $J_(i j)$, and we may lift $alpha$ coefficientwise to an element
  $h in E_n lr((R'))$, where $R' = R[x]$. Each lifted elementary factor and its
  inverse preserve $V$, since $J_(i j) A_j subset.eq A_i$. Hence
  $h in Aut_(R') V$.#ed-note[
    For $R = ZZ$, $P = 3 ZZ$ and $V = ZZ plus.o frac(1, 2) ZZ$, the ordinary
    elementary matrix $E_(1 2) lr((1))$ sends $(0, frac(1, 2))$ to
    $(frac(1, 2), frac(1, 2))$, which is not in $V$. An arbitrary ordinary
    elementary lift therefore need not preserve the sum of ideals.
  ] We obtain
  $
    V = V_1 plus.o V_2,
    quad V_1 = plus.o.big_(i=1)^r A_i lr([x]) v_i,
    quad V_2 = plus.o.big_(i=r+1)^n A_i lr([x]) v_i,
    quad overline(h)(overline(V)_i) = U_i, quad i = 1,2.
  $
  We now choose
  $ W = P^(-1) h(V_1) plus.o h(V_2), $
  and we claim that $I Y subset.eq W subset.eq Y$. First, $h(V_1)$ and
  $V inter P Y$ have the same image in $overline(V)$, so
  $ h(V_1)+P V = V inter P Y, $
  and therefore $h(V_1) subset.eq P Y$, so $W subset.eq Y$. Furthermore,
  $
    I P Y subset.eq V ==> I Y subset.eq (P^(-1) V inter Y)
    = P^(-1)(V inter P Y) = P^(-1)(h(V_1)+P V) = W.
  $

  #source(136)
  Finally, both of the summands $P^(-1) h(V_1)$ and $h(V_2)$ are extended
  modules, since
  $
    P^(-1) h(V_1) tilde.equiv
    plus.o.big_(i=1)^r P^(-1) A_i lr([x]) v_i
    tilde.equiv R' times.o_R product_(i=1)^r P^(-1) A_i,
  $
  with a similar formula for $h(V_2)$. This completes the proof of the lemma,
  and of Seshadri’s Theorem.
]

#corollary[
  Let $R' = F[x_1,x_2]$, where $F$ is a field. Then every f.g. projective
  $R'$-module is free.
] <cor:two-variable-polynomial-projectives-free>

#exercises-heading

#exercise[
  Let $M = R^((n))$ be $R$-free, where $R$ is a commutative ring. Let
  $alpha in End_R M$. Use @th:characteristic-endomorphism-sequence to prove the
  *Cayley–Hamilton Theorem:*
  $
    "The equation" det(x-alpha) = 0 "has" x = alpha
    "as a matrix root".
  $
  #hint([@exc:characteristic-sequence-cayley-hamilton])[
    Let $R' = R[x]$, and view $x-alpha$ as a matrix over $R'$. To show that
    $lr({det(x-alpha)}) M = 0$, use @th:characteristic-endomorphism-sequence and
    establish that, more generally, $(det phi)(op("cok") phi) = 0$ for any
    endomorphism $phi$ of a free $R'$-module of finite rank.
  ]
] <exc:characteristic-sequence-cayley-hamilton>
#idx(
  "Cayley-Hamilton Theorem",
  target: [@exc:characteristic-sequence-cayley-hamilton],
)

#exercise[
  Prove @rem:polynomial-k-theory-extensions(iv).
  #hint([@exc:free-associative-polynomial-k1], caption: [Hint (Gersten):])[
    Let $R' = R lr({X})$, $tau: K_1 lr((R)) -> K_1 lr((R'))$ the map induced by
    the inclusion $R subset R'$. There is a surjection $R' -> R$ which is the
    identity on $R$, so $tau$ is injective. As in the proof of
    @th:bass-heller-swan-polynomial-k1, each element of $op("cok") tau$ can be
    represented by a matrix $1+bold(N)$, where
    $bold(N) = sum_(i=1)^r x_i bold(N)_i$, $x_i in X$, with the
    $lr({bold(N)_i})$ matrices over $R$.

    Then $bold(N)$ is nilpotent, so there exists an integer $d$ such that
    $bold(N)_(i_1) dots bold(N)_(i_d) = 0$ for all indices between $1$ and $r$.
    Further,
    $
      (1+bold(N))(1-x_1 bold(N)_1) dots (1-x_r bold(N)_r)
      equiv 1+sum x_i x_j bold(N)_(i j),
    $
    $
      (1+bold(N))(1-x_1 bold(N)_1) dots (1-x_r bold(N)_r)
      product_(i,j) (1-x_i x_j bold(N)_(i j))
      equiv 1+sum x_i x_j x_k bold(N)_(i j k),
    $
    where the congruences are modulo words of length at least $3$ and $4$,
    respectively, and each $bold(N)_(i j)$, $bold(N)_(i j k)$ is a matrix over
    $R$. Continuing, the minimum length of the remaining nonconstant words
    increases until all terms vanish at length $d$. Eliminating individual terms
    in this way expresses $(1+bold(N))^(-1)$ as a product of factors
    $1+y bold(M)$, where $y$ is a product of $x$’s and $bold(M)$ is a signed
    product of $bold(N)_i$’s. But $1+y bold(M)$ is trivial in $K_1 lr((R[y]))$,
    hence also in $K_1 lr((R'))$.
  ]
] <exc:free-associative-polynomial-k1>
