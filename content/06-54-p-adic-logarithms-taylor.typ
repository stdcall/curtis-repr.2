#import "main-defs.typ": *
#import "statements.typ": *

== $p$-Adic Logarithms and Taylor’s Theorem <sec:p-adic-logarithms-taylor>

This section is devoted to the proof of a theorem of M. Taylor @bib:Taylor1980
which asserts that for a finite $p$-group $G$, the Swan subgroup $T(G)$ of the
class group $op("Cl") ZZ G$ is cyclic of order equal to the Artin exponent
$A(G)$ (or $A(G) slash 2$ if $p = 2$ with some exceptions). The method used
involves a modified version of the $p$-adic logarithm, which is crucial not only
to the determination of the Swan subgroup, but is also a key tool in problems in
algebraic number theory connected with the existence of normal integral bases.
For this latter application, we refer the reader to Fröhlich @bib:Frohlich1983,
as well as the articles by Taylor listed in the bibliography therein.

We begin with a review of the $p$-adic logarithm and $p$-adic exponential
function. Until further notice, let $K$ be a $p$-adic field
($= "finite extension of" QQ_p$) with valuation ring $R$, and let $P$ be the
maximal ideal of $R$. Let $v$ denote the exponential valuation on $K$,
normalized so that $v(p) = 1$, and thus the smallest positive value of $v$ on
$K$ is $1 slash e$, where $e$ is the ramification index of $K$ over $QQ_p$.
Consider the series
$
  log(1 + x) = sum_(n=1)^infinity (-1)^(n-1) x^n slash n,
  quad "and" exp x = sum_(n=0)^infinity x^n slash n !,
$ <eq:p-adic-log-exp-series>
#idx("Exp", target: [@eq:p-adic-log-exp-series])
#idx("Logarithm", target: [@eq:p-adic-log-exp-series])
for $x in R$. Since $v$ is non-archimedean, a series $sum a_n$ converges if and
only if $lim_(n arrow.r infinity) v(a_n) = infinity$. The following is a
well-known result:

#proposition[
  #enum(
    numbering: "(i)",
    [The series for $log(1+x)$ converges to an element of $K$ for all $x in P$.
      If $v(x) >= 1$, then $log(1+x) in p R$.],
    [The series for $exp x$ converges to an element of $1+P$ whenever
      $v(x) > 1 slash (p-1)$. For $p$ odd, if $v(x) >= 1$ then
      $exp x in 1+p R$.],
    [For $p$ odd, we have
      $
        exp(log(1+x)) = 1+x, quad log(exp x) = x
        quad "for" v(x) >= 1.
      $],
  )
] <prop:p-adic-log-exp-convergence>
#proof[
  (i) If $p^k divides n$ but $p^(k+1)$ does not, then
  $v(n) = k <= (log n) slash (log p)$. For $x in R$, this gives
  $ v(x^n slash n) = n v(x) - v(n) >= n v(x) - (log n) slash (log p). $
  #source(373)
  Thus the series for $log(1+x)$ converges for $v(x)>0$, that is, for $x in P$.
  If $v(x) >= 1$ then $v(x^n slash n) >= 1$ for $n >= 1$, so $log(1+x) in p R$.

  (ii) For $n>0$ we have $v(x^n slash n !) = n v(x)-v(n !)$. But
  $
    v(n !) = floor(n slash p) + floor(n slash p^2) + dots
    <= n slash p + n slash p^2 + dots < n slash (p-1),
  $
  where brackets is the “greatest integer” function. Thus
  $ v(x^n slash n !) > n lr((v(x)-1 slash (p-1))) quad "for" n>0. $
  This shows that $exp x$ converges for $v(x)>1 slash (p-1)$, and that
  $exp x in 1+P$. For odd $p$, $v(x)>=1$ implies that $v(x^n slash n !) >= 1$
  for $n>0$, so $exp x in 1+p R$.

  Assertion (iii) follows from the usual manipulations with series.
]

#remarks[
  #enum(
    numbering: "(i)",
    [For $x,y in P$,
      $ log((1+x)(1+y)) = log(1+x) + log(1+y). $],
    [If $x,y in R$ are such that $v(x)>1 slash (p-1)$ and $v(y)>1 slash (p-1)$,
      then
      $ exp(x+y) = (exp x)(exp y). $],
    [For $p=2$, the equalities in @prop:p-adic-log-exp-convergence(iii) hold
      whenever $v(x)>=2$.],
    [Let $omega in R$ be a $p^m$-th root of 1, where $m>0$. Then $1-omega in P$,
      so $log omega = log(1+(omega-1))$ converges. But then
      $ 0 = log omega^(p^m) = p^m log omega, $
      so $log omega=0$. If $omega!=1$, then $omega != exp(log omega)$.],
    [Let $x in 1+P$ be such that $log x=0$. We claim that $x$ must be a
      $p$-power root of 1. Choose $m$ large enough that $x^(p^m) in 1+p^2 R$.
      Then $log x^(p^m)=p^m log x=0$, and
      $ x^(p^m) = exp(log x^(p^m)) = 1, $
      so $x$ is a $p^m$-th root of 1.],
    [For odd $p$, $1+p R$ contains no nontrivial $p$-power root of 1, since for
      such a root $x$ we would have $x=exp log x=1$. Likewise, $1+4R$ contains
      no nontrivial 2-power root of 1.],
  )
] <rem:p-adic-logarithm-identities>

From now on, let $Lambda$ be an $R$-order in a f.d. $K$-algebra $A$, and let
$J = rad Lambda$.
#source(374)
By @i:prop:finite-algebra-local-base-radical we have
$ J^l subset.eq P Lambda subset.eq J quad "for some" l>0. $
It follows readily from the proof of @prop:p-adic-log-exp-convergence that
$log(1+x)$ converges to an element of $A$ for all $x in J$, and that
$ log(1+x) in p Lambda quad "for" x in p Lambda. $
Likewise, for $p$ odd, $exp x$ converges to an element of $1+p Lambda$ for all
$x in p Lambda$; for $p=2$, $exp x$ converges to an element of $1+J$ if
$x in p J$, and to an element of $1+p Lambda$ if $x in p^2 Lambda$. Again, log
and exp are inverse between $p Lambda$ and $1+p Lambda$ for odd $p$, and between
$p^2 Lambda$ and $1+p^2 Lambda$ for $p=2$.

If $A$ is noncommutative, formulas such as $log u v = log u + log v$ may break
down because $u$ and $v$ need not commute. To overcome this difficulty, we
introduce the quotient space
$ overline(A) = A slash sum_(x,y in A) K(x y-y x). $
Generally speaking, $overline(A)$ is a $K$-space but not a ring. There is a
canonical surjection $A -> overline(A)$ of $K$-spaces, but this need not be a
ring homomorphism.

Assume hereafter that $A=K G$, $Lambda=R G$, where $G$ is a finite group, and
set
$
  overline(A) = K G slash sum_(x,y in G) K(x y-y x),
  quad overline(Lambda) = R G slash sum_(x,y in G) R(x y-y x).
$
As we have seen in @i:lem:group-ring-commutator-quotient-free,
$overline(Lambda)$ is isomorphic to the free $R$-module spanned by symbols
${frak(C)_x}$, one for each conjugacy class in $G$. We may thus view
$overline(Lambda)$ as embedded in $overline(A)$. Let
$y in A arrow.r overline(y) in overline(A)$; then for each $zeta in op("ch") G$,
the value $zeta(y)$ depends only on $overline(y)$, and we may write
$zeta(overline(y))$ instead of $zeta(y)$ if we wish.

We now introduce Taylor’s modified version of the $p$-adic logarithm for group
rings $R G$, where $R$ is a $p$-adic ring and $G$ is a $p$-group. For this
purpose, we impose the extra hypothesis that $K slash QQ_p$ is unramified, so
$p R$ is the maximal ideal of $R$, and $K slash QQ_p$ is a Galois extension. The
Galois group $op("Gal")(K slash QQ_p)$ is cyclic, and is generated by the
Frobenius automorphism $F$ (see Volume I, p. 95, or proof of
@th:keating-global-maximal-order-sk1). This automorphism is characterized by the
property
$ F(a) equiv a^p (mod p R) quad "for all" a in R. $
In the special case where $K=QQ_p$, we have $F=1$, and the above congruence is
the familiar Fermat Theorem:
$ a^p equiv a (mod p ZZ_p) quad "for all" a in ZZ_p. $

#source(375)
Let us now define a $QQ_p$-linear endomorphism $theta$ of $K G$, by the formula
$ theta lr((sum_(x in G) alpha_x x)) = sum_(x in G) F(alpha_x) x^p. $
Put $f=[K:QQ_p]$. Note that $theta$ need not be a ring homomorphism, and $theta$
is not $K$-linear if $f != 1$.

Now let
$ J = rad R G = I(R G) + p R G, $
where $I = "augmentation ideal"$. Then $1+J$ is a multiplicative subgroup of
$(R G)^dot$. We define a modified logarithmic map
$ L_0: 1+J -> K G $
by the formula
$
  L_0(1-y) = -p sum_(n=1)^infinity y^n slash n
  + sum_(n=1)^infinity theta(y^n) slash n, quad y in J.
$ <eq:modified-p-adic-logarithm>
Since $y^l in p R G$ for some $l>0$, it is easily verified that the above series
converge to elements of $K G$. Let $overline(L)_0(1-y)$ denote the image of
$L_0(1-y)$ in $overline(K G)$, and set
$ L(1-y) = overline(L)_0(1-y) in overline(K G). $
We intend to prove that $L$ gives a homomorphism:
$ L(u v) = L(u) + L(v) quad "for" u,v in 1+J. $
At first glance this seems obvious, since by passing from $A$ to $overline(A)$,
we have removed the obstacle arising from noncommutativity. However, this
heuristic argument breaks down because $overline(A)$ is not a factor ring of
$A$, but just a quotient space.

We now prove the following result of Taylor @bib:Taylor1978c:

#theorem[
  Let $R$ be an unramified extension of $ZZ_p$, with Frobenius automorphism $F$.
  Let $G$ be a $p$-group, and set $J=rad R G$. Let $theta$ be the $ZZ_p$-linear
  endomorphism of $R G$ defined by
  $ theta lr((sum_(x in G) alpha_x x)) = sum_(x in G) F(alpha_x) x^p. $
  For each $y in J$, let
  $
    L(1-y) = overline(L)_0(1-y), quad "where"
    L_0(1-y) = -p sum_(n=1)^infinity y^n slash n
    + sum_(n=1)^infinity theta(y^n) slash n,
  $
  #source(376)
  and where $overline(L)_0$ denotes the image of $L_0$ in
  $overline(K G) = K G slash sum_(x,y in G) K(x y-y x)$. Then for $u,v in 1+J$
  we have $L(u),L(v) in p overline(R G)$, and
  $ L(u v) = L(u) + L(v). $
] <th:taylor-integral-logarithm>
#proof[
  _Step 1._ Let $E supset K$ be a splitting field for $G$, and identify the
  character ring $op("ch") G$ with the ring $op("ch") E G$ of virtual characters
  of $G$ afforded by $E G$-modules. Let $psi$ be the $p$-th Adams operator on
  $op("ch") G$, defined by
  $ (psi(zeta)) x = zeta(x^p) quad "for" x in G, quad zeta in op("Irr") G $
  (see §@i:ss:adams-operators-virtual-characters). Then by
  @i:cor:adams-ring-endomorphisms, $psi$ is an endomorphism of the ring
  $op("ch") G$.
  #idx("Adams operator")

  Let $T$ be an $E$-representation of $G$, affording the character $tau$. Let
  $S$ be the valuation ring of $E$, with maximal ideal $P'$. We may assume $T$
  chosen so that the matrices ${T(x):x in G}$ have entries in $S$. By
  definition,
  $ scripts(det)_tau y = det T(y), quad y in K G, $
  and $scripts(det)_tau y$ is independent of the choice of $T$ affording the
  given character $tau$. If $tau'$ is another character of $G$, then (by
  definition)
  $
    scripts(det)_(tau-tau') lr((y)) =
    (scripts(det)_tau y) slash (scripts(det)_(tau') y)
    quad "for" y in (K G)^dot.
  $
  Suppose now that $x in J$, so $1-x in (R G)^dot$. Then $T(1-x) = I-T(x)$.
  Since $x^l in p R G$ for some $l>0$, it follows that $T(x)^l$ has entries in
  $p S$, and therefore
  $ scripts(det)_tau lr((1-x)) = det(I-T(x)) equiv 1 (mod P'). $
  It follows from @prop:p-adic-log-exp-convergence that the series for
  $log scripts(det)_tau lr((1-x))$ converges to an element of $E$. Indeed, this
  holds for each $tau in op("ch") G$.

  We now extend the Frobenius automorphism $F$ of $K slash QQ_p$ to a ring
  automorphism $x arrow.r x^F$ of $K G$. Note that $F$ is an automorphism of
  $R G$ which carries $J$ onto itself. It follows from the above discussion that
  for $x in J$, the series for $log scripts(det)_tau lr((1-x^F))$ converges in
  $E$, for each virtual character $tau in op("ch") G$.

  _Step 2._ Keep the above notation. We shall show, for each
  $zeta in op("ch") G$ and $x in J$, that
  $
    zeta(L_0(1-x)) = log lr(
      {
        scripts(det)_(p zeta) lr((1-x)) dot
        scripts(det)_(-psi(zeta)) lr((1-x^F))
      }
    ).
  $ <eq:modified-logarithm-character-evaluation>
  Here, $psi(zeta)$ is the $p$-th Adams operator $psi$ applied to $zeta$, while
  $p zeta$ is $zeta+dots+zeta$ ($p$ copies).

  To begin with, both sides of @eq:modified-logarithm-character-evaluation are
  additive in $zeta$, by virtue of @rem:p-adic-logarithm-identities(i). It
  therefore suffices to consider the case where $zeta in op("Irr") G$. Let
  $T:G -> GL_d lr((S))$ be a representation affording the character $zeta$, and
  extend $T$ to a $K$-algebra homomorphism
  $ T:K G -> M_d lr((E)) $
  #source(377)
  by linearity. For $x in J$, the eigenvalues ${a_j}$ of $T(x)$ lie in the
  valuation ring of some finite extension of $E$, and each $v(a_j)>0$ since
  $x in J$. We have
  $
    op("char. pol.") T(x) = det(lambda I_d-T(x)) = product_(j=1)^d (lambda-a_j),
  $
  where $lambda$ is an indeterminate. Therefore
  $
    scripts(det)_zeta lr((1-x)) = det T(1-x) = det(I-T(x))
    = product_(j=1)^d (1-a_j).
  $
  We may then take $p$-adic logs of both sides, obtaining
  $
    log scripts(det)_zeta lr((1-x)) =
    -sum_(j=1)^d sum_(n=1)^infinity a_j^n slash n
    = -sum_(n=1)^infinity 1 slash n lr((sum_j a_j^n)).
  $
  Since $T(x^n)$ has eigenvalues ${a_j^n}$, we have
  $ sum_(j=1)^d a_j^n = op("trace") T(x^n) = zeta(x^n), $
  by definition of the character $zeta$ afforded by $T$. Thus for $x in J$,
  $
    log scripts(det)_zeta lr((1-x)) =
    -sum_(n=1)^infinity zeta(x^n) slash n
    = zeta lr((-sum_(n=1)^infinity x^n slash n)).
  $ <eq:log-determinant-trace-series>
  We shall use this formula twice, once with $zeta$ replaced by $p zeta$, the
  second time with $-psi(zeta)$ in place of $zeta$. We obtain
  $
    log scripts(det)_(p zeta) lr((1-x))
    = p zeta lr((-sum x^n slash n))
    = zeta lr((-p sum x^n slash n)),
  $
  $
    log scripts(det)_(-psi(zeta)) lr((1-x^F))
    = psi(zeta) lr({sum F(x^n) slash n})
    = zeta lr((sum theta(x^n) slash n)),
  $
  the last equality holding because of the definitions of $psi(zeta)$ and
  $theta$. But then @eq:modified-logarithm-character-evaluation follows, by
  adding the above two formulas.

  _Step 3._ Now let $u,v in 1+J$. For any $zeta in op("ch") G$ we have
  $ scripts(det)_zeta lr((u v)) = (scripts(det)_zeta u)(scripts(det)_zeta v), $
  and therefore
  $
    log scripts(det)_zeta lr((u v)) =
    log scripts(det)_zeta u + log scripts(det)_zeta v.
  $
  Since $(u v)^F=u^F v^F$, it follows from
  @eq:modified-logarithm-character-evaluation that
  $ zeta(L_0(u v)) = zeta(L_0(u)) + zeta(L_0(v)). $

  #source(378)
  But for $x in K G$, the value $zeta(x)$ depends only on the image
  $overline(x) in overline(K G)$, since $zeta$ is a class function. Thus
  $ zeta(L(u v)) = zeta(L(u)) + zeta(L(v)) quad "for all" zeta in op("Irr") G. $
  However, the irreducible characters of $G$ form a basis for the ring of class
  functions on $G$, and so we conclude that
  $ L(u v) = L(u) + L(v) quad "for" u,v in 1+J, $
  as desired.

  _Step 4._ Now let $u=1-y$, where $y in J$. It remains for us to verify that
  $L(1-y) in p overline(R G)$, where
  $ overline(R G) = R G slash sum_(x,z in G) R(x z-z x). $
  By definition, $L(1-y)$ is the image in $overline(K G)$ of
  $ -p sum_(n=1)^infinity y^n slash n + sum_(n=1)^infinity theta(y^n) slash n, $
  which is an element of $K G$. We remark that
  $K times.o_R overline(R G) tilde.equiv overline(K G)$, since $overline(R G)$
  is $R$-free (see @i:lem:group-ring-commutator-quotient-free). Since
  $p y^n slash n in p R G$ whenever $p divides.not n$, we may ignore the terms
  in the first series for which $p divides.not n$. Thus, we must show
  $ sum_(n=1)^infinity (theta(y^n)-y^(p n)) slash n in p overline(R G), $
  after taking the image of the left-hand side in $overline(R G)$. Let
  $p^(m-1) divides n$ but $p^m$ does not, and write $n=p^(m-1) n_0$, where
  $p divides.not n_0$. Setting $x=y^(n_0)$, we have $y^n=x^(p^(m-1))$, so we
  need only prove
  $
    theta(x^(p^(m-1)))-x^(p^m) in p^m overline(R G)
    quad "for" x in J, quad m>=1,
  $ <eq:frobenius-power-commutator-congruence>
  where again the left side must be viewed as element of $overline(R G)$. We
  shall establish the above relation by grouping terms in $x^(p^m)$ and
  $theta(x^(p^(m-1)))$ so that their difference has the desired congruence
  property in $overline(R G)$.

  Let us write $x=sum a_i g_i$, $a_i in R$, $g_i in G$. Then for $m>=1$,
  $ x^(p^m) = sum a_(j_1) dots a_(j_(p^m)) g_(j_1) dots g_(j_(p^m)), $
  where $(j_1,dots,j_(p^m))$ ranges over all ordered $p^m$-tuples of indices,
  with repetitions allowed. In this expansion of $x^(p^m)$, let us consider the
  subsum $xi$ of all terms in which ${j_1,dots,j_(p^m)}$ is a cyclic
  #source(379)
  permutation of some fixed $p^m$-tuple ${i_1,dots,i_(p^m)}$. Then
  $ product g_(j_mu) "is conjugate to" product g_(i_mu) quad "in" G, $
  so all of the terms in the subsum $xi$ have the same image in $overline(R G)$.
  Now let $H$ be a cyclic group of order $p^m$ which permutes $p^m$-tuples
  cyclically, and suppose there are precisely $p^t$ elements of $H$ which fix
  the $p^m$-tuple ${i_1,dots,i_(p^m)}$. Then there are precisely $p^(m-t)$
  distinct cyclic arrangements of this $p^m$-tuple, and we may write
  $ a_(i_1) dots a_(i_(p^m)) g_(i_1) dots g_(i_(p^m)) = alpha^(p^t) g^(p^t), $
  where
  $
    alpha = a_(i_1) dots a_(i_(p^(m-t))),
    quad g = g_(i_1) dots g_(i_(p^(m-t))).
  $ <eq:cyclic-word-orbit-block>
  It follows that in $overline(R G)$,
  $ overline(xi) = p^(m-t) alpha^(p^t) overline(g^(p^t)), $
  since conjugate elements of $G$ have the same image in $overline(R G)$.

  Now consider the assertion @eq:frobenius-power-commutator-congruence which we
  are trying to establish. For any subsum $xi$ of $x^(p^m)$ such that $t=0$, we
  already know that $overline(xi) in p^m overline(R G)$, by the above formula
  for $overline(xi)$. On the other hand, we show that for every subsum $xi$ such
  that $t>=1$, there is a corresponding subsum $theta(xi')$ in
  $theta(x^(p^(m-1)))$ such that
  $overline(theta(xi'))-overline(xi) in p^m overline(R G)$. Indeed, let $xi'$ be
  the subsum of $x^(p^(m-1))$ consisting of all terms
  $ a_(j_1) dots a_(j_(p^(m-1))) g_(j_1) dots g_(j_(p^(m-1))) $
  for which ${j_1,dots,j_(p^(m-1))}$ is a cyclic permutation of
  ${i_1,dots,i_(p^(m-1))}$. There are now $p^(t-1)$ elements of the cyclic group
  $overline(H)$ of order $p^(m-1)$ which stabilize ${i_1,dots,i_(p^(m-1))}$, and
  thus there are $p^((m-1)-(t-1))$ distinct cyclic arrangements of this
  $p^(m-1)$-tuple. We may thus write $xi'$ as a sum of terms
  $ xi' = alpha^(p^(t-1)) g^(p^(t-1)) + dots, $
  where the dots indicate conjugates of $g^(p^(t-1))$, and where $alpha,g$ are
  as in @eq:cyclic-word-orbit-block. Then
  $
    theta(xi') = F(alpha^(p^(t-1))) g^(p^t) + dots,
    quad "and" overline(theta(xi')) =
    p^(m-t) F(alpha^(p^(t-1))) overline(g^(p^t)).
  $
  Since $F(alpha) equiv alpha^p (mod p R)$, we obtain readily (by induction on
  $t$)
  $ F(alpha^(p^(t-1))) equiv alpha^(p^t) (mod p^t R). $
  Therefore
  $
    overline(theta(xi')) = p^(m-t) alpha^(p^t) overline(g^(p^t))
    = overline(xi) (mod p^m overline(R G)),
  $
  #source(380)
  so $overline(theta(xi'))-overline(xi) in p^m overline(R G)$. This completes
  the proof of @eq:frobenius-power-commutator-congruence, and establishes
  Theorem @th:taylor-integral-logarithm.
]

Before giving some easy consequences of the above theorem, we introduce some
notation. For $zeta in op("ch") G$, we write
$
  zeta equiv 0 (mod p^k) quad "if and only if"
  zeta(x) equiv 0 (mod p^k) quad "for all" x in G.
$ <eq:character-value-divisibility>
Then we have

#corollary[
  Let $k>=0$ and suppose $zeta in op("ch") G$ satisfies
  $zeta equiv 0 (mod p^k)$. Then
  $
    zeta(x^(p^m)) equiv psi(zeta)(x^(p^(m-1))) (mod p^(m+k))
    quad "for" x in ZZ_p G quad "and" m>=1.
  $
] <cor:adams-character-power-congruence>
#proof[
  In Step 4 of the preceding proof, we showed that
  $ theta(x^(p^(m-1)))-x^(p^m) in p^m overline(R G) $
  for each $x in R G$, where the left-hand side is viewed as element of
  $overline(R G)$. (The hypothesis $x in J$ was not used in proving
  @eq:frobenius-power-commutator-congruence.) Applying $zeta$ linearly to this
  congruence, we obtain
  $
    zeta(theta(x^(p^(m-1))))-zeta(x^(p^m))
    in p^m zeta(overline(R G)) subset.eq p^(m+k) S.
  $
  Now choose $R=ZZ_p$, so $F=1$ and thus
  $
    zeta(theta(x^(p^(m-1)))) = psi(zeta)(x^(p^(m-1)))
    quad "for" x in ZZ_p G.
  $
  This completes the proof.
]

The next consequence of Theorem @th:taylor-integral-logarithm will be vital in
proving Taylor’s Theorem about the Swan subgroup.

#corollary[
  Let $zeta in op("ch") G$ be such that $zeta equiv 0 (mod p^k)$ for some $k>0$.
  Then for each $z in (ZZ_p G)^dot$, there exists a $p$-power root of unity
  $mu(z) in QQ_p lr((zeta))$ such that #numbered-block[$
    (scripts(det)_(p zeta) z)(scripts(det)_(-psi(zeta)) z)
    equiv mu(z) (mod p^(k+1)).
  $] <eq:adams-determinant-root-congruence>
] <cor:adams-determinant-root-congruence>
#proof[
  Denote by $w$ the left-hand side of @eq:adams-determinant-root-congruence. We
  have $(ZZ_p G)^dot = ZZ_p^dot (1+J)$, where $J=rad ZZ_p G$. For
  $z in ZZ_p^dot$, we obtain $w=z^(p d) z^(-d)$, where $d=zeta(1)$. Since
  $z^(p-1) equiv 1 (mod p)$ and $p^k divides d$, it follows that
  $w equiv 1 (mod p^(k+1))$, and in this case we may choose $mu(z)=1$.

  It remains to treat the case where $z in 1+J$. Let $K_0=QQ_p lr((zeta))$,
  $R_0="d.v.r. in" K_0$, and $P_0="maximal ideal of" R_0$. Since $z in 1+J$, it
  is clear from Exercise @exc:character-determinant-in-character-field that
  $w equiv 1 (mod P_0)$. We must show that $w equiv mu(z) (mod p^(k+1))$ with
  $mu(z)$ a $p$-power root of 1 in $K_0$. Taking $R=ZZ_p$ and $f=1$ in
  @eq:modified-logarithm-character-evaluation, we have $log w=$
  #source(381)
  $zeta(L(z))$, where $L(z)$ is the logarithm defined in
  @th:taylor-integral-logarithm. But $L(z) in p overline(ZZ_p G)$, and the
  values ${zeta(g):g in G}$ are multiples of $p^k$ by hypothesis. It follows as
  in the preceding proof that $zeta(L(z)) equiv 0 (mod p^(k+1))$. Thus we have
  $ w equiv 1 (mod P_0), quad log w equiv 0 (mod p^(k+1) R_0). $
  We shall deduce from this that $w equiv mu(z) (mod p^(k+1))$ for some $mu(z)$.

  It is easily seen that for $p$ odd
  $
    log(1+p^n y) equiv p^n y (mod p^(n+1))
    quad "for" n>=1 quad "and" y in R_0,
  $ <eq:logarithm-principal-unit-leading-term>
  while for $p=2$ the above holds for all $n>=2$.

  Since $log w equiv 0 (mod p^(k+1))$ and $k>=1$, we may use
  @eq:logarithm-principal-unit-leading-term repeatedly to find elements
  ${x_i:i=k+1,k+2,dots}$ of $R_0$ such that for $i>=k+1$,
  $
    x_i equiv w (mod p^(k+1)), quad log x_i equiv 0 (mod p^i),
    quad "and" lim_(i arrow.r infinity) x_i=x' "exists".
  $
  Then $log x'=0$ and $x' equiv w (mod p^(k+1))$, so $x' in 1+P_0$. By
  @rem:p-adic-logarithm-identities(v), $x'$ is a $p$-power root of 1, and so we
  need only choose $mu(z)=x'$. This completes the proof.
]

Before embarking on the proof of Taylor’s Theorem, let us tabulate the Artin
exponent $A(G)$ and the order $abs(T(G))$ of the Swan subgroup $T(G)$, for $G$ a
$p$-group.

#table(
  columns: (1fr, auto, auto),
  align: (left, center, center),
  table.header([$G=p$-group of order $p^m$], [$A(G)$], [$abs(T(G))$]),
  [Cyclic], [$1$], [$1$],
  [Noncyclic, $p$ odd], [$p^(m-1)$], [$p^(m-1)$],
  [Generalized quaternion group of order $2^m$, $m>=3$], [$2$], [$2$],
  [Dihedral group of order $2^m$, $m>=2$], [$2$], [$1$],
  [Semidihedral group of order $2^m$, $m>=4$], [$4$], [$2$],
  [All other noncyclic 2-groups of order $2^m$], [$2^(m-1)$], [$2^(m-2)$],
)
#idx("A(G)")
#idx("Artin exponent")

For $G$ cyclic, $A(G)=1$ by definition, while $T(G)$ is trivial by
@prop:swan-subgroup-elementary-properties. In general, by
@prop:swan-subgroup-elementary-properties and
@th:artin-exponent-annihilates-swan-subgroup, $T(G)$ is a cyclic $p$-group. For
$p^m>2$, its order divides $phi(p^m) slash 2$; thus $abs(T(G))$ divides
$p^(m-1)$ for $p$ odd, and divides $2^(m-2)$ for $p=2$.

By @th:quaternion-swan-subgroup-order-two and
@th:semidihedral-swan-subgroup-order-two, $abs(T(G))=2$ for $G$ a generalized
quaternion 2-group or semidihedral 2-group, while $D(ZZ G)$ and $T(G)$ are
trivial for a dihedral 2-group by @th:dihedral-two-group-trivial-kernel (see
also Exercise @exc:dihedral-swan-subgroup-trivial). Thus, it remains for us to
prove:

#theorem(name: [Taylor’s Theorem])[
  Let $G$ be a noncyclic $p$-group of order $p^m$. If $p=2$, assume that $G$ is
  not generalized quaternion, dihedral, or semidihedral. Then the order of the
  Swan subgroup $T(G)$ of the locally free class group $op("Cl") ZZ G$ is given
  by
  $ abs(T(G))=p^(m-1), quad p "odd"; quad abs(T(G))=2^(m-2), quad p=2. $
] <th:taylor-swan-subgroup-order>
#idx("Taylor's Theorem", target: [@th:taylor-swan-subgroup-order])
#proof[
  #source(382)
  Let $E=QQ(omega)$, where $omega$ is a primitive $p^m$-th root of 1, so $E$ is
  a splitting field for $G$. Let $Omega=op("Gal")(E slash QQ)$, and
  $S="alg. int." lr({E})$. Let $Lambda=ZZ G$, so by
  @eq:p-group-hom-kernel-group-formula we have (writing Hom in place of
  $Hom_Omega$, for brevity)
  $
    D(Lambda) tilde.equiv
    Hom(op("ch") G, S_p^dot) slash
    (Hom^+(op("ch") G,S^dot) dot op("Det") Lambda_p^dot).
  $ <eq:p-group-kernel-hom-taylor>
  The Swan subgroup $T(G)$ of $D(Lambda)$ consists of the classes $[r,sigma]$,
  where $p divides.not r$. The class $[r,sigma]$ is represented by the function
  $f in Hom(op("ch") G, S_p^dot)$ such that
  $ f(zeta) = cases(r & "if" zeta=1, 1 & "if" zeta in op("Irr") G\, zeta!=1) $
  (see @exm:swan-module-det-representative). By @eq:swan-subgroup-k1-sequence
  and @eq:swan-subgroup-unit-sequence, $T(G)$ is a factor group of
  $overline(ZZ)^dot slash (plus.minus 1)$, where $overline(ZZ)=ZZ slash p^m ZZ$.

  We begin with the case where $p$ is odd, so now $abs(G)=p^m$, $m>=2$, and $G$
  is noncyclic. The element $1+p$ has order $p^(m-1)$ in
  $overline(ZZ)^dot slash (plus.minus 1)$, so we shall consider the class
  $[1+p,sigma] in T(G)$, and then take its representative function
  $f in Hom(op("ch") G, S_p^dot)$. We shall then find a homomorphic image of the
  right-hand side of @eq:p-group-kernel-hom-taylor, such that $f$ maps onto an
  element $overline(f)$ of order $p^(m-1)$ in this image. It will then follow
  that $abs(T(G))>=p^(m-1)$, and consequently $abs(T(G))=p^(m-1)$, as desired.

  To construct the homomorphic image, we need some additional notation. For
  $zeta in op("ch") G$, we write (as above)
  $
    zeta equiv 0 (mod p^k) quad "if"
    zeta(g) equiv 0 (mod p^k) quad "for each" g in G.
  $
  Let $psi$ be the $p$-th Adams operator on $op("ch") G$, and let
  $op("ch")^((k)) G$ be the additive subgroup of $op("ch") G$ defined by
  $
    op("ch")^((k)) G = {p zeta-psi(zeta):
      zeta in op("ch") G, zeta equiv 0 (mod p^k)}.
  $
  Now let
  $
    V_k & = brace.l f in Hom_Omega lr((op("ch") G, S_p^dot)): \
        & "For each" xi=p zeta-psi(zeta) in op("ch")^((k)) G,
          f(xi) equiv mu_xi (mod p^(k+1)) \
        & "with" mu_xi "some" p "-power root of" 1 "in"
          QQ_p lr((zeta)) brace.r .
  $
  Then Corollary @cor:adams-determinant-root-congruence can be restated as
  follows:
  $ op("Det") Lambda_p^dot "is a subgroup of" V_k quad "for" k>0. $
  We observe next that inclusion $op("ch")^((k)) G subset op("ch") G$ defines a
  restriction homomorphism
  $ op("res"):Hom(op("ch") G, S_p^dot) -> Hom(op("ch")^((k)) G, S_p^dot). $

  #source(383)
  By @eq:p-group-kernel-hom-taylor, res induces a surjective homomorphism
  $
    D(Lambda) ->
    frac(
      op("res") Hom(op("ch") G, S_p^dot),
      op("res") lr({Hom^+(op("ch") G,S^dot) dot V_k})
    ), quad k>0,
  $
  using the fact that $op("Det") Lambda_p^dot <= V_k$. We shall combine this
  surjection with another map, to be defined below. Given any
  $zeta in op("ch") G$ such that $zeta equiv 0 (mod p^k)$, where $k>0$, let
  $K=QQ(zeta) subset.eq E$, $R="alg. int." lr({K}) subset.eq S$, and let
  $hat(R)=R_p$, $hat(S)=S_p$. Define a homomorphism
  $
    frac(
      op("res") Hom(op("ch") G, hat(S)^dot),
      op("res") lr({Hom^+(op("ch") G,S^dot) dot V_k})
    )
    arrow.r^theta
    frac(hat(R)^dot, R^dot (1+p^(k+1) hat(R)))
  $
  as follows: for each $f in Hom(op("ch") G, hat(S)^dot)$, let
  $ theta(op("res") f) = "residue class of" f(p zeta-psi(zeta)). $
  Note that $f(p zeta-psi(zeta)) in hat(R)^dot$ since $f(p zeta-psi(zeta))$ is
  invariant under $op("Gal")(E slash K)$. Further,
  $hat(R)^dot inter S^dot=R^dot$, and $R^dot$ contains each $p$-power root of
  unity in $hat(R)$. It follows readily that $theta$ is well-defined.

  In particular, we construct the map $theta$ corresponding to the regular
  character $rho$ of $G$; we have $rho(1)=p^m$ and $rho equiv 0 (mod p^m)$. In
  this case we have $K=QQ(rho)=QQ$, $R=ZZ$, $hat(R)=ZZ_p$. Thus we obtain
  homomorphisms
  $
    D(Lambda) ->
    frac(
      Hom(op("ch") G, hat(S)^dot),
      Hom^+(op("ch") G,S^dot) dot op("Det") Lambda_p^dot
    )
    arrow.r^(theta compose op("res"))
    frac(ZZ_p^dot, (plus.minus 1)(1+p^(m+1) ZZ_p)) = W,
  $
  say, where for each $f in Hom(op("ch") G, hat(S)^dot)$,
  $ theta(op("res") f) = "image of" f(p rho-psi(rho)) quad "in" W. $

  We wish to calculate the image of $f$, where $f$ is the representative
  function of the class $[1+p,sigma] in T(G)$, given by
  $ f(zeta)=cases(1+p & quad zeta=1, 1 & quad zeta in op("Irr") G\, zeta!=1). $
  We have
  $ f(p rho-psi(rho)) = f(rho)^p slash f(psi(rho)), $
  and we must calculate the multiplicities of the trivial character 1 in $rho$
  and $psi(rho)$. Clearly,
  $
    (rho,1) = abs(G)^(-1) sum_(x in G) rho(x)=1,
    quad (psi(rho),1) = abs(G)^(-1) sum_(x in G) rho(x^p).
  $
  #source(384)
  Since $G$ is a noncyclic $p$-group, $p$ odd, Kulakoff’s Theorem tells us that
  $ "card" {x in G:x^p=1} equiv 0 (mod p^2) $
  (see Huppert @bib:Huppert1967, Theorem III.8.8(b), or Zassenhaus
  @bib:Zassenhaus1949, p. 123). It follows that $f(p rho-psi(rho))=(1+p)^(p q)$
  for some integer $q$ prime to $p$. Since $(1+p)^p$ has order $p^(m-1)$ in $W$,
  the above remarks prove that the class $[1+p,sigma]$ has order $p^(m-1)$ in
  $D(Lambda)$, and is a generator of the cyclic group $T(G)$.

  Consider finally the case where $p=2$, and let $G$ be a noncyclic 2-group of
  order $2^m$, with $G$ not generalized quaternion, dihedral, or semidihedral.
  In this case, a theorem of Thompson, Feit, and Alperin (see Isaacs
  @bib:Isaacs1976, p. 52) states that
  $ "card" {x in G:x^2=1} equiv 0 (mod 4). $
  We now show that the class $[5,sigma] in T(G)$ has order $2^(m-2)$, and thus
  generates the cyclic group $T(G)$. Let $f$ be the representative function of
  this class; as above, define the map $theta$ by using the regular
  representation of $G$. Then
  $ f(2 rho-psi(rho))=5^(2 q), quad "where" q "is odd". $
  In this case,
  $ W=ZZ_2^dot slash ((plus.minus 1)(1+2^(m+1) ZZ_2)), $
  and clearly $5^(2 q)$ has order $2^(m-2)$ in $W$. This shows that $[5,sigma]$
  has order $2^(m-2)$, and completes the proof of Taylor’s Theorem.
]

We conclude by stating, without proof, some results due to Oliver
@bib:Oliver1983b, which provide a deeper understanding of Taylor’s Theorem. Let
$G$ be a $p$-group, where $p$ is odd, and let $Delta$ be the subgroup of order
$p-1$ in $ZZ_p^dot$, with its cyclotomic power action. If $G$ is cyclic, this
gives the canonical power action of $Delta$ on $G$, trivial when $G=1$, and
hence an action on the finite $p$-group $D(ZZ G)$. This action gives rise to a
decomposition of $D(ZZ G)$ into eigenspaces ${""^i D(ZZ G)}$; see the discussion
following @th:cyclic-two-group-kernel-order.

Now let $G$ be an arbitrary $p$-group, $p$ odd. The center of $QQ G$ is a direct
sum of cyclotomic field extensions $F_i$ of $QQ$, and restriction of the
cyclotomic action gives an action of $Delta$ on each $F_i$, trivial on $QQ$, and
hence on the center of $QQ G$. Oliver proved that one can define an action of
$Delta$ on $D(ZZ G)$, giving rise to eigenspaces ${""^i D(ZZ G)}$, with
$""^0 D(ZZ G)$ the $Delta$-trivial submodule of $D(ZZ G)$. His main results are
as follows:

#case-list(
  numbering: "(1)",
  [#case[If $p$ is a regular odd prime, then
    $D^+(ZZ G) tilde.equiv ""^0 D(ZZ G)$.
  ] <case:oliver-regular-prime-zero-eigenspace>],
  [#case[The Swan subgroup $T(G)$ is a subgroup of $""^0 D(ZZ G)$.
  ] <case:oliver-swan-subgroup-zero-eigenspace>],
  [#case[Define the _Artin cokernel_ (see §@sec:artin-exponent) of $G$ to be the
    ring
    $ (op("ch") QQ G) slash sum_(C<=G) op("ind")_C^G op("ch") QQ C, $
    where $C$ ranges over all cyclic subgroups of $G$. This is a commutative
    ring
    #source(385)
    (with identity element), whose characteristic is the Artin exponent $A(G)$
    of $G$. There is an isomorphism
    $ ""^0 D(ZZ G) tilde.equiv "Artin cokernel of" G. $
    This isomorphism carries $T(G)$ onto the group $ZZ dot 1$, where 1 is the
    identity element of the Artin cokernel. Consequently $T(G)$ is cyclic, of
    order $A(G)$.
  ] <case:oliver-zero-eigenspace-artin-cokernel>],
  [#case[For an arbitrary finite group $H$, let
    $
      QQ H tilde.equiv product.co_i M_(n_i) lr((D_i)),
      quad D_i="skewfield", quad d_i=dim_QQ D_i.
    $
    Let $C$ range over a full set of nonconjugate cyclic subgroups of $H$. Then
    $
      ("order of Artin cokernel of" H)^2 =
      frac(
        product_C frac(phi(abs(C)) abs(N_H lr((C)):C), abs(C)),
        product_i d_i
      ),
    $
    where $phi = "Euler" phi "-function"$. For another version of this formula,
    due to Solomon @bib:Solomon1974, see @th:solomon-artin-cokernel-order.
  ] <case:oliver-artin-cokernel-order>],
)
For $G$ an arbitrary $p$-group, $p$ odd, the isomorphism in
@case:oliver-zero-eigenspace-artin-cokernel then yields an explicit formula for
the order of $""^0 D(ZZ G)$.

#exercises-heading

#exercise[
  Keeping the notation of @cor:adams-determinant-root-congruence, assume that
  both $zeta$ and $psi(zeta)$ are characters of $G$ (not just virtual
  characters). Show that in @eq:adams-determinant-root-congruence, $mu(z)$ is
  necessarily equal to 1.

  #hint[@exc:adams-determinant-congruence-without-root][
    (Taylor @bib:Taylor1978a): Use Newton’s identities and
    @cor:adams-character-power-congruence.
  ] <hint:adams-determinant-congruence-without-root>
] <exc:adams-determinant-congruence-without-root>
