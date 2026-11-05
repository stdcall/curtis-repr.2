#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/50-class-groups.typ": *

== Class Groups of Integral Group Rings <sec:class-groups-integral-group-rings>

In this section we shall show how to compute the locally free class group
$op("Cl") ZZ G$ for various finite groups $G$. The methods often apply to the
more general case $op("Cl") R G$, with $R$ a ring of algebraic integers. In most
cases, we shall determine the kernel group $D(ZZ G)$, which differs from the
class group $op("Cl") ZZ G$ by class groups of rings of algebraic integers.
Furthermore, the kernel group $D(ZZ G)$ is usually calculated in terms of
information about the distribution of units (in rings of algebraic integers)
modulo certain ideals. Deeper investigation of units leads to difficult problems
in algebraic number theory, which are usually beyond the scope of this book, and
in any case are often unsolved.

=== Cyclic Groups of Squarefree Order <ss:cyclic-squarefree-class-groups>

Throughout this subsection, $p$ denotes a rational prime, $C_n$ a cyclic group
of order $n$, and $omega_n$ a primitive $n$-th root of $1$ over $QQ$. We set
(see §@i:ss:cyclotomic-fields)
$
  K_n = QQ(omega_n), quad R_n = "alg. int." lr({K_n}) = ZZ[omega_n], quad
  pi_n = product_(p divides n) (1 - omega_p).
$ <eq:cyclotomic-class-group-notation>
Let $R_n^dot$ be the group of units of $R_n$, and $(R_n slash pi_n)^dot$ the
group of units of $R_n slash pi_n$, where we write $R_n slash pi_n$ in place of
$R_n slash pi_n R_n$ for brevity. By Exercise
@i:exc:rational-cyclic-group-wedderburn, we may write
$ QQ C_n tilde.equiv product.co_(d divides n) K_d. $
The unique maximal $ZZ$-order $Lambda'$ in $QQ C_n$ is therefore given by
$ Lambda' tilde.equiv product.co_(d divides n) R_d, $
and consequently
$ op("Cl") Lambda' tilde.equiv product.co_(d divides n) op("Cl") R_d. $

#source(260)
There is an exact sequence (see @eq:class-group-kernel-sequence)
$ 0 arrow D(ZZ C_n) arrow op("Cl") ZZ C_n arrow op("Cl") Lambda' arrow 0, $
and we shall usually study the _kernel group_ $D(ZZ C_n)$ rather than
$op("Cl") ZZ C_n$.

We begin with a “classical” result, due to Rim @bib:Rim1959: #theorem[
  For each prime $p$,
  $ op("Cl") ZZ C_p tilde.equiv op("Cl") R, quad D(ZZ C_p) = 0 $
  where $R = ZZ[omega]$, with $omega$ a primitive $p$-th root of $1$ over $QQ$.
] <th:rim-cyclic-prime-class-group>
#idx("Rim's Theorem", target: [@th:rim-cyclic-prime-class-group])
#proof[
  We have already proved this theorem in Example
  @exm:rim-cyclic-prime-projective-class-group, but repeat the argument here
  with slightly different notation. By
  @i:prop:prime-power-cyclotomic-ramification (i) we have
  $
    R slash pi tilde.equiv ZZ slash p, quad
    (R slash pi)^dot tilde.equiv (ZZ slash p)^dot, quad "where" pi = 1 - omega.
  $
  Let $C_p = chevron.l x: x^p = 1 chevron.r$, and consider the fiber product
  #numbered-block[#cyclic-prime-rim-square] <eq:cyclic-prime-rim-fiber-product>
  where $f(x) = omega$ and $g(x) = 1$. By
  @cor:commutative-order-unit-class-group-sequence and
  @th:kernel-group-mayer-vietoris, there are exact sequences
  #cyclic-prime-class-kernel-fork
  Since $D(ZZ) = D(R) = op("Cl") ZZ = 0$, it suffices to prove that $h$ is
  surjective.

  Each element of $(R slash pi)^dot$ is of the form $overline(n) = n + pi R$ for
  some $n in ZZ$ relatively prime to $p$. Since $omega$ is expressible as a
  power of $omega^n$, it follows that
  $
    (1 - omega^n) slash (1 - omega) quad "and" quad
    (1 - omega) slash (1 - omega^n) quad "lie in" R.
  $
  Therefore $u = (1 - omega^n) slash (1 - omega) in R^dot$. Since
  $omega = 1 - pi$, we have
  $ u = (1 - (1 - pi)^n) / pi equiv n quad (mod pi), $
  so $h(u) = overline(n)$. This proves that $h$ is surjective, and establishes
  Rim's Theorem.
]

#source(261)
We note next that for $m, n$ relatively prime integers, $omega_m omega_n$ is a
primitive $m n$-th root of $1$ over $QQ$. This implies that
$ R_m times.o_ZZ R_n tilde.equiv R_(m n) quad "when" (m, n) = 1, $
a fact used repeatedly below. One consequence is an obvious extension of Rim's
result: #corollary[
  Let $p$ be prime, and assume $p divides.not m$. Then
  $
    D(R_m C_p) tilde.equiv
    op("cok") (R_(m p)^dot arrow (R_(m p) slash pi_p)^dot),
  $
  using the notation of @eq:cyclotomic-class-group-notation.
] <cor:cyclotomic-base-prime-cyclic-kernel>
#proof[
  Applying $R_m times.o_ZZ ast$ to @eq:cyclic-prime-rim-fiber-product, we obtain
  a fiber product
  #numbered-block[#cyclotomic-base-prime-square]
  <eq:cyclotomic-base-prime-fiber-product>
  (The isomorphism occurring in this diagram follows from
  @i:th:cyclotomic-prime-factorization (ii).) But the corollary is now an
  immediate consequence of the Mayer–Vietoris sequence
  @th:kernel-group-mayer-vietoris.
]

We now turn to a consideration of $D(ZZ C_n)$ for squarefree $n$. The case where
$n = 2 p$, with $p$ an odd prime, is due to Ullom @bib:Ullom1970. The general
case was treated independently by Cassou-Noguès @bib:CassouNogues1972,
@bib:CassouNogues1974 and Matchett @bib:Matchett1980. We follow Matchett's
approach, somewhat modified. The symbol $p$ always denotes a prime (not
necessarily odd), and as in @eq:cyclotomic-class-group-notation $R_p$ means
$ZZ[omega_p]$, rather than the $p$-adic completion of a ring $R$. Further, we
set $pi_p = 1 - omega_p$, and
$ pi_d = product_(p divides d) (1 - omega_p) in R_d. $
We write $R_d slash pi_d$ instead of $R_d slash pi_d R_d$, for brevity;
likewise, $R_d slash p$ means $R_d slash p R_d$.

The main result exhibits the order of $D(ZZ C_n)$ as a product of the orders of
certain cokernels. The explicit calculation of these orders leads to complicated
questions in algebraic number theory, concerning the distribution of units of
cyclotomic rings $R_d$ among the residue classes $mod pi_d$. We shall prove:
#theorem[
  Let $C_n$ be a cyclic group of squarefree order $n$. Then
  $
    abs(D(ZZ C_n)) = product_(d divides n)
    abs(op("cok") lr({R_d^dot arrow (R_d slash pi_d)^dot})),
  $
  using the notation @eq:cyclotomic-class-group-notation and setting $pi_1 = 1$.
  In particular, if $n = p q$ where $p, q$ are distinct primes, then
  $ abs(D(ZZ C_n)) = abs(op("cok") lr({R_n^dot arrow (R_n slash pi_n)^dot})). $
] <th:squarefree-cyclic-kernel-order>
#source(262)
#proof[
  _Step 1._ Let $Lambda = ZZ C_n$, and let $Lambda'$ be the unique maximal
  $ZZ$-order in $A$, where $A = QQ C_n$. As pointed out at the beginning of this
  subsection,
  $
    A tilde.equiv product.co_(d divides n) K_d, quad
    Lambda' tilde.equiv product.co_(d divides n) R_d,
  $
  where $d$ ranges over all positive divisors of $n$. Since $n Lambda'$ is a
  two-sided ideal of $Lambda$ by @i:prop:group-ring-maximality, there is a fiber
  product
  #cyclic-maximal-order-conductor-square
  From Exercise @exc:full-ideal-class-kernel-sequences, we obtain an exact
  sequence
  $
    1 arrow Lambda^dot arrow
    (Lambda slash n Lambda')^dot times (Lambda')^dot arrow
    (Lambda' slash n Lambda')^dot arrow D(Lambda) arrow 0.
  $
  On the other hand, there is a commutative diagram
  #cyclic-conductor-unit-triangle
  The map $psi$ is surjective, by virtue of the following useful result:
]
#lemma[
  Let $Gamma$ be any semilocal ring#footnote[
    This means that $Gamma slash op("rad") Gamma$ is a semisimple artinian ring.
    See the discussion in @i:prop:artinian-and-finite-local-algebras-semilocal.
  ] (not necessarily commutative) and let $I$ be any two-sided ideal of $Gamma$.
  Then the surjection of rings $Gamma arrow Gamma slash I$ induces a surjection
  $Gamma^dot arrow (Gamma slash I)^dot$ of groups of units.
] <lem:semilocal-quotient-unit-surjectivity>
#idx(
  "Units (in semilocal rings)",
  target: [@lem:semilocal-quotient-unit-surjectivity],
)
#proof[
  The factor ring $Gamma slash op("rad") Gamma$ is semisimple artinian, by
  hypothesis. The proof of Exercise @i:exc:units-surject-quotient-local-base
  carries over directly to the present situation, using $Gamma$ in place of the
  ring $A$ in that exercise.
]
#proof(head: none)[
  _Step 2._ Returning to the proof of the theorem, we observe that since $psi$
  is surjective, the maps $alpha$ and $alpha'$ above have the same image in
  $(Lambda' slash n Lambda')^dot$. Thus there is an exact sequence
  $
    (Lambda slash n Lambda)^dot times (Lambda')^dot
    arrow^((alpha, beta)) (Lambda' slash n Lambda')^dot arrow D(Lambda) arrow 0,
  $
  and so $D(Lambda) tilde.equiv op("cok") (alpha, beta)$. We shall calculate
  $op("cok") (alpha, beta)$ by first determining $op("cok") alpha$, and then
  factoring out the image of $beta$ in $op("cok") alpha$.

  #source(263)
  Consider the natural maps
  $
    f: Lambda / (n Lambda) arrow Lambda' / (n Lambda'), quad
    alpha: (Lambda / (n Lambda))^dot arrow (Lambda' / (n Lambda'))^dot.
  $
  Since $n$ is squarefree, there are decompositions
  $
    Lambda / (n Lambda) tilde.equiv
    product.co_(p divides n) Lambda / (p Lambda),
    quad Lambda' / (n Lambda') tilde.equiv
    product.co_(p divides n) Lambda' / (p Lambda'),
  $
  where $p$ ranges over the prime divisors of $n$. Then $f = product f_p$,
  $alpha = product alpha_p$, where
  $
    f_p: Lambda / (p Lambda) arrow Lambda' / (p Lambda'), quad
    alpha_p: (Lambda / (p Lambda))^dot arrow (Lambda' / (p Lambda'))^dot.
  $
  Using these maps, we now establish:
]
#lemma[
  Keeping the above notation, we have
  $
    op("cok") alpha tilde.equiv
    product_(m divides n) (R_m slash pi_m)^dot.
  $
] <lem:squarefree-cyclic-conductor-unit-cokernel>
#proof[
  Since $Lambda' tilde.equiv product.co_(d divides n) R_d$, we may write (for
  each prime $p$ dividing $n$)
  $
    f_p: Lambda / (p Lambda) arrow product.co_(d divides n) R_d / p, quad
    alpha_p: (Lambda / (p Lambda))^dot arrow
    product_(d divides n) (R_d / p)^dot,
  $
  where (as usual), $R_d slash p$ is an abbreviation for $R_d slash p R_d$. Let
  $tilde(Lambda)$ denote the localization of $Lambda$ at $p$, and $tilde(R)_d$
  that of $R_d$, for $d divides n$. As in §@sec:whitehead-groups, we have
  $
    tilde(Lambda) slash p tilde(Lambda) tilde.equiv Lambda slash p Lambda,
    quad tilde(R)_d slash p tilde(R)_d tilde.equiv R_d slash p,
  $
  so in computing $op("cok") f_p$ and $op("cok") alpha_p$, we may replace
  $Lambda$ and each $R_d$ by their localizations at $p$.

  Since localization preserves exactness (see @i:prop:localization-criteria
  (ii)), the pullback diagram @eq:cyclic-prime-rim-fiber-product yields a fiber
  product
  #localized-cyclic-prime-square
  We apply the exact functor $tilde(ZZ) C_q times.o_tilde(ZZ) ast$ to the above,
  where $q = n slash p$. This gives a new fiber product
  #localized-cyclic-squarefree-square
  #source(264)
  But $q$ is a unit in $tilde(R)_p$, so $tilde(R)_p C_q$ is a maximal
  $tilde(R)_p$-order in $K_p C_q$. Therefore we may write
  $
    tilde(ZZ) C_q tilde.equiv product.co_(d divides q) tilde(R)_d, quad
    tilde(R)_p C_q tilde.equiv product.co_(d divides q) tilde(R)_(p d),
  $
  where, for the latter formula, we have used the obvious fact that
  $
    R_p times.o_ZZ R_q = ZZ[omega_p] times.o_ZZ ZZ[omega_q]
    tilde.equiv ZZ[omega_(p q)]
  $
  whenever $(p, q) = 1$.

  The preceding fiber product diagram can thus be written as an exact sequence
  $
    0 arrow tilde(ZZ) C_n arrow
    product.co_(d divides q) lr({tilde(R)_d plus.o tilde(R)_(p d)}) arrow
    product.co_(d divides q) tilde(R)_(p d) slash pi_p arrow 0.
  $
  <eq:squarefree-local-cyclotomic-fiber-sequence>
  Viewing $tilde(ZZ) C_n$ as embedded in $tilde(Lambda)'$, we may thus describe
  $tilde(ZZ) C_n$ as the set of all vectors
  $ chevron.l x_m in tilde(R)_m: m divides n chevron.r $
  satisfying the congruence conditions
  $
    x_d equiv x_(p d) (mod pi_p tilde(R)_(p d))
    quad "for each" d "dividing" n slash p.
  $
  On the other hand, $ZZ C_n$ is the intersection of its localizations
  $tilde(ZZ) C_n$ as $p$ ranges over all rational primes. The only restrictions
  arise from primes $p$ dividing $n$, so we have the useful formula
  $
    ZZ C_n = lr(
      {chevron.l x_m in R_m: m divides n chevron.r:
        x_d equiv x_(p d) (mod pi_p R_(p d))
        "for each prime" p \ "dividing" n,
        "and each" d "dividing" n slash p}
    ).
  $
  <eq:squarefree-cyclic-ring-congruences>
  Passing over to groups of units, we have
  $
    (ZZ C_n)^dot = lr(
      {chevron.l x_m chevron.r in
        product_(m divides n) R_m^dot:
        x_d x_(p d)^(-1) equiv 1 (mod pi_p R_(p d))
        "for" p divides n, d divides (n slash p)}
    ).
  $
  <eq:squarefree-cyclic-unit-congruences>
  We now apply the right exact functor $(tilde(ZZ) slash p) times.o_tilde(ZZ)
  ast$ to @eq:squarefree-local-cyclotomic-fiber-sequence, obtaining a new exact
  sequence
  $
    (tilde(ZZ) slash p) C_n arrow
    product.co_(d divides q)
    lr({tilde(R)_d slash p plus.o tilde(R)_(p d) slash p})
    arrow product.co_(d divides q)
    lr({(tilde(ZZ) slash p) times.o_tilde(ZZ) tilde(R)_(p d) slash pi_p})
    arrow 0.
  $
  #source(265)
  But
  $
    (tilde(ZZ) slash p) times.o_tilde(ZZ) (tilde(R)_(p d) slash pi_p)
    tilde.equiv tilde(R)_(p d) slash pi_p,
    quad "since" p in pi_p tilde(R)_(p d).
  $
  Passing over to groups of units, we obtain an exact sequence
  $
    (Lambda / (p Lambda))^dot arrow
    product_(d divides q) lr({(R_d / p)^dot times (R_(p d) / p)^dot})
    arrow^theta product_(d divides q) (R_(p d) / pi_p)^dot arrow 1.
  $
  Note that we can specify $theta$ by the formulas
  $
    theta(x_d) = x_d^(-1) (mod pi_p R_(p d)), quad
    theta(x_(p d)) = x_(p d) (mod pi_p R_(p d)),
    quad "for" x_d in R_d, quad x_(p d) in R_(p d).
  $
  The last exact sequence can be rewritten thus:
  $
    (Lambda / (p Lambda))^dot arrow^(alpha_p)
    product_(m divides n) (R_m / p)^dot arrow^theta
    product_(d divides q) (R_(p d) / pi_p)^dot arrow 1,
  $
  and consequently we obtain
  $
    op("cok") alpha_p tilde.equiv product_(d divides q)
    (R_(p d) slash pi_p)^dot,
  $
  where $q = n slash p$.

  We are now ready to complete the proof of Lemma
  @lem:squarefree-cyclic-conductor-unit-cokernel. We have
  $
    op("cok") alpha = product_(p divides n) op("cok") alpha_p
    = product_(p divides n) product_(d divides n slash p)
    (R_(p d) slash pi_p)^dot.
  $
  Each divisor $m$ of $n$, $m > 1$, occurs as a subscript $p d$ for some $p$ and
  $d$. Thus
  $
    op("cok") alpha tilde.equiv product_(m divides n \ m > 1)
    lr({product_(p divides m) (R_m / pi_p)^dot}).
  $
  By the Chinese Remainder Theorem we have
  $ R_m slash pi_m tilde.equiv product.co_(p divides m) R_m slash pi_p, $
  so we obtain
  $
    op("cok") alpha tilde.equiv product_(m divides n \ m > 1)
    (R_m slash pi_m)^dot,
  $
  which yields @lem:squarefree-cyclic-conductor-unit-cokernel at once.
]

#source(266)
#proof(head: none)[
  _Step 3._ Let $beta: (Lambda')^dot arrow (Lambda' slash n Lambda')^dot$. We
  have shown in Step 1 that
  $
    D(Lambda) tilde.equiv op("cok") alpha slash
    ("image of" beta "in" op("cok") alpha),
  $
  and we must compute the denominator on the right side. We have seen that
  $
    op("cok") alpha tilde.equiv product_(p divides n) op("cok") alpha_p,
    quad "and" quad op("cok") alpha_p tilde.equiv
    product_(k divides n slash p) (R_(p k) slash pi_p)^dot.
  $
  We shall calculate the image of $beta$ in each $op("cok") alpha_p$, and for
  this it suffices to find the image of an element $x_d in R_d^dot$, where
  $d divides n$. If $p divides.not d$, then by Step 2 we have
  $
    x_d in R_d^dot arrow x_d^(-1) in (R_d slash p)^dot
    tilde.equiv (R_(p d) slash pi_p)^dot,
  $
  so the image of $x_d$ in $op("cok") alpha_p$ is precisely
  $x_d^(-1) in (R_(p d) slash pi_p)^dot$, that is, the image is
  $
    lr({1, dots, x_d^(-1), 1, dots, 1}) in
    product_(k divides n slash p) (R_(p k) slash pi_p)^dot.
  $
  On the other hand, if $p divides d$ and we write $d = p d'$, then
  $x_d in R_d^dot$ maps onto $x_d$ $(mod R_d slash pi_p)$, with all other
  components $1$.

  Combining $p$-parts for all primes $p$ dividing $n$, we see that the map
  $ gamma: (Lambda')^dot arrow op("cok") alpha $
  is given by $gamma = product_(d divides n) gamma_d$, where
  $
    gamma_d: R_d^dot arrow
    lr({product_(p divides d) (R_d slash pi_p)^dot}) times
    lr({product_(p divides n slash d) (R_(p d) slash pi_p)^dot}),
  $
  and where the right-hand side is viewed as a direct factor of
  $op("cok") alpha$. The map $gamma_d$ carries an element $x_d in R_d^dot$ onto
  the congruence class of $x_d$ in each of the first set of factors, and onto
  the class of $x_d^(-1)$ in each of the second set of factors. We may therefore
  write
  $
    gamma_d: R_d^dot arrow (R_d slash pi_d)^dot times
    product_(p divides n slash d) (R_(p d) slash pi_p)^dot
    subset.eq op("cok") alpha,
  $
  where now for $x_d in R_d^dot$,
  $
    gamma_d lr((x_d)) = chevron.l x_d, x_d^(-1), dots, x_d^(-1),
    1, dots, 1 chevron.r in op("cok") alpha.
  $
  It will be convenient to let $psi_d$ denote the natural map
  $ psi_d: R_d^dot arrow (R_d slash pi_d)^dot, quad d divides n. $
  #source(267)
  Then of course $op("cok") psi_1 = 1$, and we are trying to prove that
  $ abs(op("cok") gamma) = product_(d divides n) abs(op("cok") psi_d). $
  <eq:squarefree-cyclic-unit-cokernel-order-product>
  In order to use an induction argument, we begin by arranging the distinct
  positive divisors of $n$ as a sequence
  $ d_0 = 1, d_1, d_2, dots, d_N = n, $
  in such a way that for $i < j$, the number of prime factors of $d_i$ is $<=$
  the corresponding number for $d_j$. For each $i$, put
  $
    B_i = product_(j >= i) R_(d_j)^dot, quad
    Y_i = product_(j >= i) (R_(d_j) slash pi_(d_j))^dot.
  $
  Then $gamma(B_i) subset.eq Y_i$, and we have
  $ op("cok") gamma = op("cok") (R_1^dot times B_1 arrow Y_1). $
  We shall prove that $R_1^dot times B_1$ and $B_1$ have the same image in
  $Y_1$, and shall also show that
  $
    abs(op("cok") (B_i arrow Y_i)) = abs(op("cok") psi_(d_i))
    abs(op("cok") (B_(i+1) arrow Y_(i+1))).
  $
  <eq:squarefree-cyclic-unit-cokernel-induction>
  These facts will imply the validity of formula
  @eq:squarefree-cyclic-unit-cokernel-order-product, by taking
  $i = 1, dots, N - 1$ successively.

  _Step 4._ Let us verify that $gamma(R_1^dot times B_1) = gamma(B_1)$ in $Y_1$.
  For any $x_1 in R_1^dot$, we choose $xi = x_1 1_Lambda in
  Lambda^dot$. Since $gamma(Lambda^dot) = 1$, it follows that $gamma(xi) = 1$,
  and therefore
  $ gamma(x_1) = gamma(xi^(-1) x_1), quad "and" quad xi^(-1) x_1 in B_1. $
  This implies that $gamma(R_1^dot) subset.eq gamma(B_1)$, and establishes the
  claim.

  Next we prove @eq:squarefree-cyclic-unit-cokernel-induction for
  $1 <= i <= N - 1$. We have
  $
    op("cok") (B_i arrow Y_i) = op("cok")
    (R_(d_i)^dot times B_(i+1) arrow
      (R_(d_i) slash pi_(d_i))^dot times Y_(i+1)),
  $
  and $gamma(B_(i+1)) subset.eq Y_(i+1)$. By Exercise
  @exc:product-homomorphism-cokernel-order we obtain
  $
    abs(op("cok") (B_i arrow Y_i)) =
    abs(op("cok") (R_(d_i)^dot arrow (R_(d_i) slash pi_(d_i))^dot))
    abs(op("cok") (W arrow Y_(i+1))),
  $
  where
  $ W = lr({x in R_(d_i)^dot: x equiv 1 (mod pi_(d_i))}) times B_(i+1). $
  To complete the proof of @eq:squarefree-cyclic-unit-cokernel-induction, it
  remains to show that $gamma(W) = gamma(B_(i+1))$ in $Y_(i+1)$.

  #source(268)
  Let $x in R_(d_i)^dot$ be such that $x equiv 1 (mod pi_(d_i))$, and define
  $xi = chevron.l xi_(d_j): 0 <= j <= N chevron.r in (Lambda')^dot$ by the
  formula
  $
    xi_(d_j) = cases(
      x & "if" d_j "is divisible by" d_i,
      1 & "otherwise."
    )
  $
  Then $xi^(-1) x in B_(i+1)$ (viewed as direct factor of $(Lambda')^dot$), and
  we shall show that $gamma(xi) = 1$. This will imply that
  $gamma(x) = gamma(xi^(-1) x) in gamma(B_(i+1))$, so
  $gamma(W) = gamma(B_(i+1))$, as desired.

  To prove that $gamma(xi) = 1$, it suffices to find the image of $gamma$ in
  each $op("cok") alpha_p$, where $p$ ranges over the prime divisors of $n$, and
  where
  $
    op("cok") alpha_p = product_(d divides n slash p)
    (R_(p d) slash pi_p)^dot
  $
  (see Step 2). If the prime $p$ divides the given $d_i$, then $pi_p$ is a
  factor of $pi_(d_i)$, and the image of $xi$ (under the map $gamma$) is $1$ in
  each $(R_(p d) slash pi_p)^dot$, since $x equiv 1 (mod pi_p)$. On the other
  hand, if $p divides.not d_i$, then the $lr({d_j})$ which are multiples of
  $d_i$ can be grouped into pairs $lr({d_j, p d_j})$, where $p divides.not d_j$;
  then by definition of the map $gamma$, the image $gamma(xi)$ in
  $op("cok") alpha_p$ is again equal to $1$. This shows that $gamma(xi) = 1$,
  and completes the proof of @eq:squarefree-cyclic-unit-cokernel-induction,
  @eq:squarefree-cyclic-unit-cokernel-order-product, and the first assertion of
  Theorem @th:squarefree-cyclic-kernel-order.

  Finally, the special case where $n = p q$ is an immediate consequence of the
  general case, since we have already shown in the proof of Theorem
  @th:rim-cyclic-prime-class-group that for each prime $p$, the map
  $R_p^dot arrow (R_p slash pi_p)^dot$ is surjective. This completes the proof
  of Theorem @th:squarefree-cyclic-kernel-order.
]

We remark that, just as in @cor:cyclotomic-base-prime-cyclic-kernel, Theorem
@th:squarefree-cyclic-kernel-order may be extended to the case in which $ZZ$ is
replaced by a cyclotomic ring $R_m$, with $(m, n) = 1$.

We may slightly refine the preceding theorem to obtain: #theorem(title: [Ullom
  @bib:Ullom1970])[
  For $p$ an odd prime,
  $
    D(ZZ C_(2 p)) tilde.equiv
    op("cok") (R_p^dot arrow (R_p slash 2 R_p)^dot).
  $
] <th:ullom-cyclic-twice-prime-kernel>
#idx("Ullom's Theorem", target: [@th:ullom-cyclic-twice-prime-kernel])
#proof[
  From @th:squarefree-cyclic-kernel-order we have
  $
    D(ZZ C_(2 p)) tilde.equiv op("cok")
    (R_p^dot arrow (R_p slash 2 pi_p)^dot) = op("cok")
    (R_p^dot arrow (R_p slash 2)^dot times (R_p slash pi_p)^dot).
  $
  By Exercise @exc:product-homomorphism-cokernel-order, we obtain
  $
    abs(D(ZZ C_(2 p))) = abs(op("cok") (R_p^dot arrow (R_p slash 2)^dot))
    abs((R_p slash pi_p)^dot : im V),
  $
  where
  $ V = lr({v in R_p^dot: v equiv 1 (mod 2 R_p)}). $
  It suffices to establish that $im V = (R_p slash pi_p)^dot$, since the proof
  of Exercise @exc:product-homomorphism-cokernel-order will then give the
  desired isomorphism in @th:ullom-cyclic-twice-prime-kernel.

  #source(269)
  We have seen before that each unit of $R_p slash pi_p$ is of the form
  $overline(u)$ for some unit $u in R_p^dot$. We shall construct a unit
  $w in R_p^dot$ such that
  $ w equiv u (mod 2 R_p), quad w equiv 1 (mod pi_p). $
  <eq:cyclic-twice-prime-adjusted-unit-congruences>
  For such $w$ we have $u w^(-1) in V$, and $u w^(-1)$ has the same image as $u$
  in $(R_p slash pi_p)^dot$. Thus $im V = (R_p slash pi_p)^dot$, as desired.

  It remains to construct $w$. Choose $theta in op("Gal") (QQ(omega_p)
    slash QQ)$ such that $theta(omega_p) = omega_p^2$. Then for all $z in R_p$
  we have
  $ theta(z) equiv z^2 (mod 2) quad "and" quad theta(z) equiv z (mod pi_p), $
  since these hold when $z$ is any power of $omega_p$, and hence also when
  $z in ZZ[omega_p]$. Setting $w = theta(u) slash u$, it follows that
  $w in R_p^dot$ satisfies the congruences
  @eq:cyclic-twice-prime-adjusted-unit-congruences. This completes the proof.
]

#remarks(numbered: false)[
  #enum(
    numbering: "(1)",
    [For the cyclic group $C_(2 p)$ with $p$ an odd prime, Ullom @bib:Ullom1970
      obtained lower bounds for the order $abs(D(ZZ C_(2 p)))$ of the kernel
      group. These results were generalized by Reiner–Ullom @bib:Reiner1974b to
      the case $C_(p q)$, with $p$ and $q$ distinct primes. Their work was
      extended by Cassou-Noguès @bib:CassouNogues1972, who obtained lower bounds
      for $abs(D(ZZ C_(p q)))$ for various numerical values of $p$ and $q$.],
    [If $G arrow overline(G)$ is a surjection of finite groups, then by
      @prop:kernel-group-ring-homomorphism there is an induced surjection
      $D(ZZ G) arrow D(ZZ overline(G))$, so $abs(D(ZZ overline(G)))$ divides
      $abs(D(ZZ G))$. In particular, if $G$ is an abelian group having a factor
      group of type $C_(p q)$, with $p$ and $q$ distinct primes, one obtains a
      lower bound for $abs(D(ZZ G))$. This is one of the key steps in proving:],
  )
] <rem:abelian-kernel-group-lower-bounds>

#theorem(title: [Cassou-Noguès @bib:CassouNogues1972])[
  For $G$ a finite abelian group, $D(ZZ G) = 0$ precisely for the following
  groups $G$:
  #enum(
    numbering: "(i)",
    [$G$ is trivial or has prime order,],
    [$G$ is cyclic of order $4, 6, 8, 9, 10, 14$,],
    [$G$ is an elementary group of type $(2,2)$.],
  )
] <th:cassou-nogues-abelian-trivial-kernel-classification>
#idx(
  "Cassou-Noguès Theorem",
  target: [@th:cassou-nogues-abelian-trivial-kernel-classification],
)
Since $D(ZZ G)$ and $op("Cl") ZZ G$ differ by class groups of rings of
cyclotomic integers, and since $abs(op("Cl") R_p) > 1$ whenever $p >= 23$, one
obtains (Cassou-Noguès @bib:CassouNogues1972): #corollary[
  Let $G$ be a finite abelian group. Then $op("Cl") ZZ G = 0$ for precisely the
  following groups:
  #enum(
    numbering: "(i)",
    [$G$ cyclic of order $n$, $1 <= n <= 11$],
    [$G$ cyclic of order $13, 14, 17, 19$],
    [$G$ elementary abelian of type $(2,2)$.],
  )
] <cor:abelian-trivial-integral-class-group-classification>

#source(270)
=== The Kernel Group for $p$-Groups <ss:p-group-kernel-groups>

The aim of this subsection is to prove the fundamental result that when $G$ is a
finite $p$-group, where $p$ is prime, then the kernel group $D(ZZ G)$ is also a
$p$-group. Before starting the proof, we remark that the result depends strongly
on the fact that the coefficient ring is $ZZ$, rather than a more general ring
of algebraic integers. Further, it is tempting to conjecture that for arbitrary
$G$, each prime factor of $abs(D(ZZ G))$ must divide $abs(G)$. However, this
conjecture is definitely false, as can be seen from the examples at the end of
§@ss:cyclic-squarefree-class-groups. Indeed, let $C_(2 p)$ be a cyclic group of
order $2 p$. Then for suitably chosen odd primes $p$, it happens that
$abs(D(ZZ C_(2 p)))$ has odd prime factors different from $p$.

The following theorem was proved first by Fröhlich @bib:Frohlich1969 for the
case of abelian $p$-groups, and then for the general case by Reiner–Ullom
@bib:Reiner1972: #theorem[
  Let $G$ be a $p$-group, where $p$ is prime. Then $D(ZZ G)$ is also a
  $p$-group.
] <th:p-group-integral-kernel-is-p-group>
#idx("Reiner-Ullom Theorem", target: [@th:p-group-integral-kernel-is-p-group])
#proof[
  We revert to our earlier notation, in which the subscript $p$ indicates
  $p$-adic completion. We shall give a simplified version of the Reiner–Ullom
  proof, by making use of Fröhlich's formula for kernel groups, and some easy
  facts about pro-$p$-groups.

  For $G=1$, the assertion is immediate from $D(ZZ)=0$. Assume henceforth that
  $G$ is nontrivial. Let $Lambda = ZZ G$. The set $S(Lambda)$ in
  @eq:order-nonmaximal-primes consists of the single prime $p$. From
  @th:kernel-group-finite-prime-formula we obtain
  $
    D(Lambda) tilde.equiv frak(O)_p^dot slash
    frak(O)^+ op("nr") Lambda_p^dot,
  $
  where $frak(O)$ is the integral closure of $ZZ$ in the center $C$ of $QQ G$.

  _Case 1._ $p$ odd. By Schilling's Theorem
  @th:schilling-odd-p-group-rational-components, we may write
  $
    A = QQ G tilde.equiv product.co M_(n_i) lr((F_i)), quad
    C = product.co F_i, quad frak(O) = product.co R_i,
  $
  where each $F_i$ is a cyclotomic field $QQ(omega_i)$ for some $p$-power root
  of unity $omega_i$. There is exactly one simple component $A_i$ of $A$ for
  which $F_i = QQ$, say $A_1$, and then $A_1 = F_1 = QQ$. By
  @i:prop:prime-power-cyclotomic-ramification, there is a unique prime ideal
  $P_i$ of $R_i$ containing $p$, and we have $R_i slash P_i
  tilde.equiv ZZ slash p ZZ$. Further, the $p$-adic completion of $R_i$
  coincides with its $P_i$-adic completion, which we now denote by $hat(R)_i$.
  Thus
  $
    frak(O)_p = product.co hat(R)_i, quad "and" quad
    frak(O)_p^dot = product.co (hat(R)_i)^dot.
  $
  On the other hand, no infinite primes ramify in this case, so $C^+ =
  C^dot$ and $frak(O)^+ = frak(O)^dot$. Thus we obtain
  $
    D(Lambda) tilde.equiv frak(O)_p^dot slash
    frak(O)^dot op("nr") Lambda_p^dot.
  $
  Now let $alpha = sum alpha_i in frak(O)_p^dot$, with $alpha_i in
  (hat(R)_i)^dot$ for each $i$. Then $alpha_i equiv a_i (mod hat(P)_i)$, for
  some $a_i in ZZ$.
  #source(271)
  Choose $t in ZZ$ with $(t,p) = 1$, such that $t a_1 equiv 1
  (mod hat(P)_1)$. Viewing $t$ as element of $Lambda_p^dot$, we note that
  $op("nr")(t)$ has component $t$ in $A_1$. Replacing $alpha$ by
  $alpha dot op("nr")(t)$, which does not affect the image of $alpha$ in
  $D(Lambda)$, we may hereafter assume that $alpha_1 equiv 1 (mod hat(P)_1)$.

  On the other hand, as shown in the proof of @th:rim-cyclic-prime-class-group,
  for each $i > 1$ there exists a unit $u_i in R_i^dot$ with
  $u_i a_i equiv 1 (mod hat(P)_i)$. Replacing $alpha$ by
  $alpha dot product.co u_i$ again does not change its image in $D(Lambda)$, so
  after changing notation, we may write
  $
    alpha = sum alpha_i, quad "where" alpha_i equiv 1 (mod hat(P)_i)
    quad "for each" i.
  $
  Thus there exists a surjection
  $
    1 + product.co hat(P)_i arrow frak(O)_p^dot slash
    frak(O)^dot op("nr") Lambda_p^dot.
  $
  The left-hand expression is a pro-$p$-group by @exm:adic-order-pro-p-groups,
  while the right side is a finite group, and is therefore a finite $p$-group
  (see Exercise @exc:finite-pro-p-subgroups-quotients).

  _Case 2._ $p = 2$. By @th:two-group-rational-simple-components we may write
  $
    A = product.co A_i quad ("simple components"), quad
    C = product.co F_i, quad F_i = "center of" A_i,
  $
  where for each $i$, $F_i$ is a subfield of $E_i = QQ(omega_i)$, with $omega_i$
  a $2$-power root of unity. Let
  $ R_i = "alg. int." lr({F_i}), quad S_i = "alg. int." lr({E_i}). $
  Now we have
  $
    D(Lambda) tilde.equiv frak(O)_2^dot slash
    frak(O)^+ op("nr") Lambda_2^dot,
  $
  and $frak(O)^dot slash frak(O)^+$ is a finite $2$-group, so in order to prove
  that $D(Lambda)$ is a $2$-group, it suffices to show that
  $frak(O)_2^dot slash frak(O)^dot op("nr") Lambda_2^dot$ is a $2$-group.

  The prime $2$ ramifies completely in $E_i$, and hence also in $F_i$. Let $P_i$
  and $frak(P)_i$ be the unique prime ideals containing $2$ in $R_i$ and $S_i$,
  respectively. Then
  $ S_i slash frak(P)_i tilde.equiv R_i slash P_i tilde.equiv ZZ slash 2 ZZ, $
  and the same isomorphisms hold when we pass to $2$-adic completions. Now let
  $alpha = sum alpha_i in frak(O)_2^dot$, with each $alpha_i in hat(R)_i$. Since
  $hat(R)_i slash hat(P)_i tilde.equiv
  ZZ slash 2 ZZ$, we have $alpha_i equiv 1 (mod hat(P)_i)$. But then, as in Case
  1, there is a surjection
  $
    1 + product.co hat(P)_i arrow frak(O)_2^dot slash
    frak(O)^dot op("nr") Lambda_2^dot,
  $
  and the left-hand expression is a pro-$2$-group. This completes the proof.
]

S. Ullom has pointed out another proof of Theorem
@th:p-group-integral-kernel-is-p-group. To begin with, a simplified version of
the above proof shows that for each cyclic $p$-group $C$, the kernel group
$D(ZZ C)$ is a $p$-group. Now let $G$ be an arbitrary $p$-group, and $cal(C)$
the set of cyclic subgroups of $G$.
#source(272)
As in @def:frobenius-family-subgroups, define
$ D(ZZ G)_(cal(C)) = sum_(C in cal(C)) op("ind")_C^G D(ZZ C). $
Then $D(ZZ G)_(cal(C))$ is a $p$-group, since each $D(ZZ C)$ is a $p$-group. On
the other hand, by @cor:class-kernel-groups-field-frobenius, $D(ZZ G)$ is a
Frobenius module over the Frobenius functor $G_0 lr((QQ G))$. The Artin
Induction Theorem shows that
$ abs(G) dot G_0 lr((QQ G)) subset.eq G_0 lr((QQ G))_(cal(C)), $
so by @cor:frobenius-induction-annihilators we may conclude that
$ abs(G) dot D(ZZ G) subset.eq D(ZZ G)_(cal(C)). $
Therefore $D(ZZ G)$ is a $p$-group, as claimed.

As shown by Ullom @bib:Ullom1974, the proof of
@th:p-group-integral-kernel-is-p-group can be refined so as to yield an upper
bound on the exponent $e(G)$ of the finite $p$-group $D(ZZ G)$. The main result
is: #theorem(title: [Ullom @bib:Ullom1974])[
  Let $G$ be a group of order $p^n$, where $p$ is prime, and let $e(G)$ be the
  exponent of the kernel group $D(ZZ G)$. For $G=1$ or $G=C_2$, we have
  $e(G)=1$. In the other cases,
  #enum(
    numbering: "(i)",
    [For odd $p$, $e(G)$ divides $p^(n - 1)$.],
    [For $p = 2$, $e(G)$ divides $2^(n - 2)$.],
  )
] <th:ullom-p-group-kernel-exponent>
#idx("Ullom's Theorem", target: [@th:ullom-p-group-kernel-exponent])
#proof[
  We restrict our attention to the easier case of odd $p$. Keeping the notation
  of Case 1 in the proof of @th:p-group-integral-kernel-is-p-group, we saw there
  that
  $
    D(Lambda) tilde.equiv frak(O)_p^dot slash
    frak(O)^dot op("nr") Lambda_p^dot,
  $
  <eq:p-group-kernel-reduced-norm-quotient>
  and that each element of $D(Lambda)$ can be represented as the image of an
  element $alpha = sum alpha_i$, where
  $
    alpha_i in (hat(R)_i)^dot, quad alpha_i equiv 1 (mod hat(P)_i)
    quad "for each" i.
  $
  On the other hand, since $Lambda'_q = Lambda_q$ for each prime $q != p$, the
  formula for $D(Lambda)$ in the proof of @prop:kernel-group-ring-homomorphism
  takes the form
  $
    D(Lambda) tilde.equiv
    (im K_1 lr((A)) dot im K_1 lr((Lambda'_p))) /
    (im K_1 lr((A)) dot im K_1 lr((Lambda_p))),
  $
  <eq:p-group-kernel-whitehead-quotient>
  where all these images are contained in $K_1 lr((A_p))$. Formula
  @th:kernel-group-finite-prime-formula is obtained from the above by applying
  the reduced norm map
  $ op("nr"): K_1 lr((A_p)) arrow C_p^dot, $
  which induces isomorphisms
  $
    im K_1 lr((A)) tilde.equiv C^dot, quad
    im K_1 lr((Lambda'_p)) tilde.equiv frak(O)_p^dot, quad
    im K_1 lr((Lambda_p)) tilde.equiv op("nr") Lambda_p^dot.
  $
  #source(273)
  Further, in this situation $A_p$ is a direct sum of matrix algebras over
  fields, and we have
  $
    A_p tilde.equiv product.co_i M_(n_i) lr((hat(F)_i)), quad
    Lambda'_p = product.co Lambda_i, quad "where"
    Lambda_i tilde.equiv M_(n_i) lr((hat(R)_i)).
  $
  Here, $hat(F)_i$ and $hat(R)_i$ denote the $p$-adic completions of $F_i$ and
  $R_i$, respectively. The reduced norm map in this case is just the usual
  determinant map, computed componentwise.

  Let $xi in D(Lambda)$ be represented (via formula
  @eq:p-group-kernel-reduced-norm-quotient) by an element $alpha = sum
  alpha_i$ as above. Define
  $
    beta = sum beta_i, quad "where"
    beta_i = op("diag") (1, dots, 1, alpha_i) in Lambda_i^dot.
  $
  Then $op("nr") beta = alpha$, and via formula
  @eq:p-group-kernel-whitehead-quotient $beta$ represents the element
  $xi in D(Lambda)$. Clearly
  $ beta_i equiv 1 (mod hat(P)_i Lambda_i) quad "for each" i, $
  and to prove the theorem, we need only show that these congruences imply that
  $beta^(p^(n - 1)) in Lambda_p^dot$. In fact, since $beta in
  (Lambda'_p)^dot$, it suffices to show that $beta^(p^(n - 1)) in Lambda_p$. (We
  may assume $n >= 1$, since the result is trivial when $n = 0$.)

  Let $(Lambda': Lambda)_l$ be the left conductor of $Lambda'$ into $Lambda$. By
  Jacobinski's Theorem @i:th:jacobinski-conductor-formula, we have
  $
    (Lambda'_p: Lambda_p)_l = product.co_i
    (p^n slash n_i) frak(D)_i^(-1) subset.eq Lambda_p,
  $
  where $frak(D)_i^(-1) = frak(D)^(-1) lr((Lambda_i slash hat(ZZ)))$ is the
  inverse different of $Lambda_i$ relative to $hat(ZZ)$, defined in terms of the
  reduced trace. The proof of @i:th:jacobinski-central-conductor gives
  $
    frak(D)^(-1) lr((Lambda_i slash hat(ZZ))) =
    frak(D)^(-1) lr((Lambda_i slash hat(R)_i)) dot
    frak(D)^(-1) lr((hat(R)_i slash hat(ZZ))).
  $
  However, since $Lambda_i tilde.equiv M_(n_i) lr((hat(R)_i))$, it is easily
  verified that $frak(D)^(-1) lr((Lambda_i slash hat(R)_i)) = Lambda_i$ (see
  @bib:Reiner1975[MO] (25.7), for example). We thus obtain
  $
    (Lambda'_p: Lambda_p)_l = product.co_i (p^n slash n_i)
    frak(D)^(-1) lr((hat(R)_i slash hat(ZZ))) Lambda_i subset.eq Lambda_p.
  $
  #source(274)
  It therefore suffices to show (for each $i$) that
  $
    alpha_i in hat(R)_i, quad alpha_i equiv 1 (mod hat(P)_i)
    arrow.double.r alpha_i^(p^(n - 1)) equiv 1
    (mod (p^n slash n_i) frak(D)^(-1) lr((hat(R)_i slash hat(ZZ)))).
  $
  To simplify the notation, drop the subscript $i$, and let
  $
    hat(F) = hat(QQ)(omega), quad hat(R) = hat(ZZ)[omega], quad
    hat(P) = pi hat(R), quad "where" omega "is a primitive" p^m
    "-th root of" 1.
  $
  Here, we have $0 <= m <= n$, and $pi = p$ if $m = 0$, $pi = 1 - omega$ if
  $m > 0$. By Exercise @exc:prime-power-cyclotomic-different, we know that
  $
    frak(D) lr((hat(R) slash hat(ZZ))) = hat(P)^t,
    quad "where" t = m phi(p^m) - p^(m - 1) quad "if" m >= 1.
  $
  It therefore suffices to prove
  $
    (1 + pi z)^(p^(n - 1)) equiv 1 (mod p^n pi^(-t) hat(R))
    quad "for" z in hat(R).
  $
  <eq:cyclotomic-principal-unit-power-congruence>
  This is clear (by induction on $n$) when $m = 0$, for then $pi = p$,
  $hat(R) = hat(ZZ)$, and $t = 0$. Now let $m >= 1$. We shall show that
  $
    (1 + pi z)^(p^(m - 1)) equiv 1 (mod p^m pi^(-t) hat(R))
    quad "for" z in hat(R).
  $
  <eq:cyclotomic-principal-unit-ramification-congruence>
  Once this is established, we may then deduce
  @eq:cyclotomic-principal-unit-power-congruence by raising both sides of
  @eq:cyclotomic-principal-unit-ramification-congruence to the $p$-th power
  $n - m$ times. Let $v$ be the exponential valuation on $hat(F)$, normalized so
  that $v(pi) = 1$. Then
  $ v(p^m pi^(-t)) = m v(p) - t = m phi(p^m) - t = p^(m - 1). $
  Let $X$ be an indeterminate, and define
  $ g(X) = lr({(1 + pi X)^(p^(m - 1)) - 1}) slash X in hat(R)[X]. $
  It then suffices to prove that $v(a_i) >= p^(m - 1)$ for each coefficient
  $a_i$ of $g(X)$. Note that $v(a_0) = p^(m - 1)$, where $a_0$ is the leading
  coefficient of $g(X)$. We may assume $m > 1$, since $g(X) = pi$ when $m = 1$.

  We shall use the Newton polygon of $g(X)$ (see §@ss:eichler-swan-theorem). For
  each root $alpha$ of the equation $g(X) = 0$, we obtain
  $ (1 + pi alpha)^(p^(m - 1)) = 1, quad alpha != 0. $
  Therefore we may write
  $
    1 + pi alpha = omega^(p k) quad "for some" k,
    quad "so" alpha = (omega^(p k) - 1) slash pi.
  $
  This implies that
  $ v(alpha) = v(omega^(p k) - 1) - 1 >= p - 1, $
  the inequality holding because $omega^(p k) - 1$ is a prime element in some
  proper cyclotomic subfield of $hat(F)$.
  #source(275)
  It follows that the slope of each side of the Newton polygon for $g(X)$ is
  positive, so $v(a_i) >= v(a_0)$ for each coefficient $a_i$ of $g(X)$. This
  proves @eq:cyclotomic-principal-unit-ramification-congruence, and completes
  the proof of the theorem for odd $p$.
]

The theorem is in some sense best possible, since Galovich @bib:Galovich1974
showed that for $G$ cyclic of order $p^n$, $p > 3$, the exponent of the kernel
group $D(ZZ G)$ is precisely $p^(n - 1)$.

=== Metacyclic Groups <ss:metacyclic-class-groups>

In this subsection we discuss the class group $op("Cl") ZZ G$ and kernel group
$D(ZZ G)$ for metacyclic groups $G$. We shall begin with a detailed treatment of
the case in which
$ G = chevron.l x, y: x^p = 1, y^q = 1, y x y^(-1) = x^r chevron.r, $
<eq:prime-by-cyclic-metacyclic-presentation>
where $p$ is an odd prime, $q$ is any divisor of $p - 1$, and $r$ is a primitive
$q$-th root of $1$ $(mod p)$. Thus $G$ is a semidirect product
$chevron.l x chevron.r times.r chevron.l y chevron.r$, where the cyclic group
$chevron.l y chevron.r$ acts faithfully on the cyclic subgroup
$chevron.l x chevron.r$ by conjugation. If $q>1$, then $G$ has trivial center.
We shall prove the following result of Galovich–Reiner–Ullom @bib:Galovich1972:
#idx("Metacyclic group", target: [@eq:prime-by-cyclic-metacyclic-presentation])
#theorem[
  Let $G$ be as above, and let $omega$ be a primitive $p$-th root of $1$ over
  $QQ$. Set
  $ K = QQ(omega), quad R = "alg. int." lr({K}) = ZZ[omega]. $
  Let $L$ be the unique subfield of $K$ with $dim_L K = q$, that is, $L$ is the
  subfield of $K$ fixed by the automorphism $sigma$ defined by
  $omega^sigma = omega^r$. Let $S = "alg. int." lr({L})$, and set
  $H = chevron.l y: y^q = 1 chevron.r$.

  Then there are exact sequences of finite abelian groups
  $
    0 arrow D_0 arrow op("Cl") ZZ G arrow
    op("Cl") S plus.o op("Cl") ZZ H arrow 0,
    quad 0 arrow D_0 arrow D(ZZ G) arrow D(ZZ H) arrow 0,
  $
  where $D_0$ is a cyclic group, and where
  $
    abs(D_0) = cases(
      q & "if" q "is odd,",
      q slash 2 & "if" q "is even."
    )
  $
  In particular, for $q = 2$ and $p$ an odd prime, $G$ is the dihedral group of
  order $2 p$, and
  $
    op("Cl") ZZ G tilde.equiv op("Cl") S, quad D(ZZ G) = 0,
    quad "where" S = ZZ[omega + omega^(-1)].
  $
] <th:galovich-reiner-ullom-metacyclic-class-groups>
#idx(
  "Galovich-Reiner-Ullom Theorem",
  target: [@th:galovich-reiner-ullom-metacyclic-class-groups],
)
#proof[
  _Step 1._ The Galois group of $K slash QQ$ is cyclic of order $p - 1$, and the
  automorphism $sigma$ of $K$ has order $q$ in this group. Therefore the fixed
  field $L$ of $chevron.l sigma chevron.r$ is the unique subfield of $K$ for
  which $dim_L K = q$.

  #source(276)
  As in @i:eq:metacyclic-integral-fibre-product, there is a fiber product
  #metacyclic-prime-fiber-square
  where
  $ overline(ZZ) = ZZ slash p ZZ tilde.equiv R slash (1 - omega) R, $
  and where $f_1 lr((x)) = omega$, $f_2 lr((x)) = 1$. In the twisted group ring
  $R compose H$ we have
  $ y alpha = alpha^sigma y, quad alpha in R, $
  where $sigma$ is the automorphism of $R$ for which $omega^sigma = omega^r$.

  Next, we note that $QQ G tilde.equiv QQ H plus.o K compose H$, so $QQ G$
  satisfies the Eichler condition. Therefore (see @th:jacobinski-cancellation)
  $ZZ G$ has locally free cancellation, and by
  @cor:cancellation-order-unit-class-group-sequence we obtain an exact sequence
  $
    1 arrow W arrow (overline(ZZ) H)^dot arrow op("Cl") Lambda arrow
    op("Cl") R compose H plus.o op("Cl") ZZ H arrow 0,
  $
  where $W$ is the subgroup of $(overline(ZZ) H)^dot$ generated by the images of
  $(ZZ H)^dot$ and $(R compose H)^dot$. Since $(ZZ H)^dot
  subset.eq (R compose H)^dot$, the subgroup $W$ is precisely the image of
  $(R compose H)^dot$ in $(overline(ZZ) H)^dot$.

  Next, we recall the proof that $R compose H$ is a hereditary order (see
  §@i:ss:dihedral-metacyclic-integral-representations or
  @i:th:twisted-group-ring-heredity). In the extension $K slash L$, there is a
  unique prime ideal $P_0$ of $S$ ramified in $R$, namely, the prime ideal
  containing $p$. Then $P_0 R = P^q$, where $P = (1 - omega) R$ is the prime
  ideal of $R$ containing $p$, and we have
  $
    S slash P_0 tilde.equiv R slash P tilde.equiv overline(ZZ) = ZZ slash p ZZ.
  $
  Since $p divides.not q$, it follows from Exercise
  @i:exc:tame-ramification-trace that $R$ is tamely ramified over $S$. Therefore
  $R compose H$ is hereditary, by @i:th:twisted-group-ring-heredity and the
  discussion following it.

  By @cor:hereditary-order-class-group-maximal-order we obtain
  $ D(R compose H) = 0, quad op("Cl") R compose H tilde.equiv op("Cl") Gamma, $
  where $Gamma$ is a maximal $ZZ$-order in the twisted group algebra
  $K compose H$. But $K compose H tilde.equiv M_q lr((L))$ by
  @i:exm:galois-twisted-group-algebra, and $S$ is the integral closure of $ZZ$
  in the center $L$ of $K compose H$, so $op("Cl") Gamma tilde.equiv
  op("Cl") S$ by @th:maximal-order-restricted-ideal-class-group. Thus we have
  exact sequences
  #metacyclic-prime-class-kernel-fork
  #source(277)
  Let
  $ D_0 = (overline(ZZ) H)^dot slash "image of" (R compose H)^dot. $
  To complete the proof, we must show that $D_0$ is cyclic of order $q$ if $q$
  is odd, and of order $q slash 2$ if $q$ is even.

  _Step 2._ The homomorphism $S arrow S slash P_0 tilde.equiv overline(ZZ)$ maps
  $S^dot$ into $overline(ZZ)^dot$. We show next that
  $overline(ZZ)^dot slash im S^dot$ is cyclic of order $q$ or $q slash 2$,
  depending on whether $q$ is odd or even. We note first that $L$ is a Galois
  extension of $QQ$, whose Galois group $op("Gal")(L slash QQ)$ is cyclic of
  order $m$, where
  $ p - 1 = q m. $
  Each $tau in op("Gal")(L slash QQ)$ induces an element $overline(tau) in
  op("Gal")(overline(S) slash overline(ZZ))$, where $overline(S) = S slash
  P_0$. Since $overline(S) tilde.equiv overline(ZZ)$, we obtain
  $ u^tau equiv u (mod P_0) quad "for all" u in S^dot. $
  Multiplying these congruences, where $tau$ ranges over
  $op("Gal")(L slash QQ)$, we obtain
  $ N_(L slash QQ) u = product_tau u^tau equiv u^m (mod P_0), $
  where $N_(L slash QQ)$ is the norm from $L$ to $QQ$ (see
  @bib:CurtisReiner1962[CR], §20B). Now suppose that $u in S^dot$; then
  $N_(L slash QQ) u = plus.minus 1$, and so we obtain
  $ u^m equiv plus.minus 1 (mod P_0) quad "for all" u in S^dot. $
  Furthermore, the field $K$ is totally imaginary, that is, there are no real
  primes of $K$. Hence any real prime of $L$ must split into an even number of
  complex primes of $K$, so $dim_L K$ must be even if $L$ has any real primes.
  Thus if $q$ is odd, it follows that $L$ is also totally imaginary, and
  therefore $N_(L slash QQ) u = +1$ for $u in S^dot$. Thus for $q$ odd we have
  $ u^m equiv 1 (mod P_0) quad "for all" u in S^dot. $

  _Case 1._ $q$ even. Let
  $ T = lr({x in overline(ZZ)^dot: x^(2 m) = 1}), $
  a subgroup of $overline(ZZ)^dot$ of order $2 m$. We shall show that
  $im S^dot = T$, so $abs(overline(ZZ)^dot slash im S^dot) = (p - 1)
  slash 2 m = q slash 2$, as desired. The preceding discussion shows that
  $u^(2 m) equiv 1 (mod P_0)$ for every $u in S^dot$, and therefore
  $im S^dot subset.eq T$.

  For the reverse inclusion, let $overline(a) in overline(ZZ)^dot$, where
  $a in ZZ$ is prime to $p$. Let $K^+ = QQ(omega + overline(omega))$,
  $R^+ = "alg. int." lr({K^+})$, so $K^+$ is the maximal real subfield of $K$,
  and $dim_(K^+) K = 2$. Since $q$ is even, $L$ is a subfield of $K^+$.
  #source(278)
  Now set
  $ xi_a = (omega^a - omega^(-a)) slash (omega - omega^(-1)) in (R^+)^dot. $
  As in the proof of @i:th:prime-cyclic-integral-lattice-classification, we have
  $ xi_a equiv a (mod P^+), quad "where" P^+ = R^+ inter P. $
  Let $u_a = N_(K^+ slash L) xi_a$, so $u_a in S^dot$. Taking norms from $K^+$
  to $L$ in the above congruence, we obtain
  $ u_a equiv a^(q slash 2) (mod P_0). $
  Thus
  $
    im S^dot supset.eq lr(
      {overline(a)^(q slash 2):
        overline(a) in overline(ZZ)^dot}
    ) = T,
  $
  which completes the proof that $overline(ZZ)^dot slash im S^dot$ is cyclic of
  order $q slash 2$ for $q$ even.

  _Case 2._ $q$ odd. It suffices to show that $im S^dot = T_1$, where
  $ T_1 = lr({x in overline(ZZ)^dot: x^m = 1}). $
  The earlier discussion shows that $im S^dot subset.eq T_1$, so we need only
  prove the reverse inclusion. In this case, let $xi_a$ be as above, and set
  $v_a = N_(K slash L) xi_a in S^dot$. Then
  $ v_a equiv a^q (mod P_0), $
  so
  $
    im S^dot supset.eq lr({overline(a)^q: overline(a) in overline(ZZ)^dot})
    = T_1,
  $
  and we are through.

  _Step 3._ To complete the proof of the theorem, we shall exhibit an
  isomorphism
  $
    theta: ((overline(ZZ) H)^dot) / (im (R compose H)^dot)
    tilde.equiv (overline(ZZ)^dot) / (im S^dot),
  $
  <eq:metacyclic-unit-image-determinant-isomorphism>
  which will be given by a determinant map. We shall compute $(R compose H)^dot$
  by observing that this group of units is anti-isomorphic to the automorphism
  group of $R compose H$ as left $(R compose H)$-module. Now we have an
  isomorphism
  $
    phi: (R compose H) slash (P compose H) tilde.equiv
    overline(ZZ) H = "direct sum of" q "simple modules",
  $
  using the fact that $overline(ZZ)$ contains the $q$-th roots of $1$.
  Furthermore,
  $
    R = ZZ[omega] = S[omega] = S plus.o S omega plus.o dots
    plus.o S omega^(q-1),
  $
  a free $S$-module.
  #source(279)
  The discussion in Volume I (pages 597–599; see also
  @i:eq:ambiguous-lattice-rank-decomposition) then shows that
  $ R compose H tilde.equiv R plus.o P plus.o P^2 plus.o dots plus.o P^(q - 1) $
  as left $(R compose H)$-modules. For each $i$, $P^i$ is the module on which
  $R$ acts naturally, and the generator $y$ of $H$ acts as the automorphism
  $sigma in op("Gal")(K slash L)$. We use this isomorphism to establish:
]
#lemma[
  The group $(R compose H)^dot$ is isomorphic to the group of all $q times q$
  matrices $(alpha_(i j)) in GL_q lr((S))$ whose entries below the main diagonal
  all lie in $P_0$.
] <lem:metacyclic-twisted-order-unit-matrices>
#proof[
  We compute $op("End")_(R compose H) lr((R compose H))$, using the module
  structure of $R compose H$, so
  $
    op("End")(R compose H) tilde.equiv plus.o.big_(i,j=0)^(q - 1)
    op("Hom")_(R compose H) lr((P^i, P^j)).
  $
  Now $K P^i tilde.equiv K P^j tilde.equiv K$, the unique simple
  $(K compose H)$-module, and $op("End")_(K compose H) K tilde.equiv L$.
  Therefore
  $
    op("Hom")_(R compose H) lr((P^j, P^i)) = L inter P^(i - j)
    = cases(S & i <= j, P_0 & i > j),
  $
  using the fact that $P_0 R = P^q$. Thus the units of $op("End") R compose
  H$ are represented by matrices in $GL_q lr((S))$ whose entries above the main
  diagonal lie in $P_0$. Now take transposes because of the anti-isomorphism
  between $(R compose H)^dot$ and the units of $op("End") R compose H$, so the
  lemma is proved.
]

We shall use this description of $(R compose H)^dot$ to calculate its image
$phi((R compose H)^dot)$ in $(overline(ZZ) H)^dot$. We have
$
  overline(ZZ) H tilde.equiv (R compose H) slash P(R compose H)
  tilde.equiv product.co_(i=0)^(q - 1) (P^i slash P^(i+1)),
$
and the $lr({P^i slash P^(i+1)})$ are a full set of simple
$overline(ZZ) H$-modules. Identifying $overline(ZZ) H$ with the endomorphism
ring of the left regular module, we find that if $u in (R compose H)^dot$ is
represented by a matrix $(alpha_(i j)) in GL_q lr((S))$ as in the lemma, then
$phi(u)$ is represented by a matrix
$
  op("diag")(overline(alpha)_(1 1), dots, overline(alpha)_(q q))
  in GL_q lr((overline(ZZ))),
$
where bars denote images in $S slash P_0$. Therefore we may identify
$(overline(ZZ) H)^dot$ with the group of all diagonal matrices in
$GL_q lr((overline(ZZ)))$, and $phi(lr((R compose H))^dot)$ with those diagonal
matrices which come from a matrix $(alpha_(i j)) in GL_q lr((S))$ whose entries
below the main diagonal lie in $P_0$.

#source(280)
Now consider the commutative diagram
#metacyclic-unit-determinant-square
where the lower arrow arises from the map $S arrow S slash P_0 tilde.equiv
overline(ZZ)$. There is then an induced map $theta$ as in
@eq:metacyclic-unit-image-determinant-isomorphism, which is surjective since
$det: (overline(ZZ) H)^dot arrow overline(ZZ)^dot$ is surjective. It remains to
prove $theta$ injective, so let
$ bold(x) = op("diag")(beta_1, dots, beta_q) in GL_q lr((overline(ZZ))) $
be such that $theta(bold(x)) = 1$, that is, $product beta_i in im S^dot$. Then
$product beta_i = overline(u)$ for some $u in S^dot$; choose elements
$alpha_i in S$ with $overline(alpha)_i = beta_i$, and then $product alpha_i
= u + pi_0$ for some $pi_0 in P_0$. We now choose $bold(y) in M_q lr((S))$ as
follows:
$
  mat(
    delim: "[",
    alpha_1, 1, 0, dots, 0;
    0, alpha_2, 1, dots, 0;
    0, 0, alpha_3, dots, 0;
    dots.v, dots.v, dots.v, dots.v, dots.v;
    (-1)^q pi_0, 0, 0, dots, alpha_q
  )
$
(for $q = 1$, let $bold(y) = (u)$). Then for $q >= 1$,
$ det bold(y) = product_i alpha_i - pi_0 = u, $
so $bold(y) in GL_q lr((S))$ represents an element of $(R compose H)^dot$. We
have $bold(x) = "image of" bold(y)$ in $(overline(ZZ) H)^dot$, so $theta$ is
injective, as desired. This completes the proof of the theorem.

The special case of Theorem @th:galovich-reiner-ullom-metacyclic-class-groups,
in which $G$ is dihedral of order $2 p$, is due originally to Reiner–Ullom
@bib:Reiner1972. We remark also that (in the general case) we have
$ D(ZZ G) tilde.equiv D_0 plus.o D(ZZ H), $
since $G$ is a semidirect product $chevron.l x chevron.r times.r H$ (see
Exercise @exc:semidirect-class-kernel-split-surjections).

The theorem was generalized by Keating @bib:Keating1974 as follows: #theorem[
  Let $p$ be a regular#footnote[
    This means that $p$ does not divide the class number of $QQ(root(p, 1))$.
  ] odd prime, $q$ an even divisor of $p - 1$, and let
  $
    G_k = chevron.l x, y: x^(p^k) = 1, y^q = 1,
    y x y^(-1) = x^r chevron.r, quad k >= 1,
  $
  where $chevron.l y chevron.r$ acts faithfully on $chevron.l x chevron.r$ by
  conjugation. Put $H=chevron.l y:y^q=1 chevron.r$ and $G_0=H$. Let $omega$ be a
  primitive $p^k$-th root of $1$, and let $L_k$ be the unique subfield of
  $QQ(omega)$ for which $dim_(L_k) QQ(omega)
  = q$. Put $S_k = "alg. int." lr({L_k})$.

  Then there are exact sequences
  $
    1 arrow C_(q') arrow op("Cl") ZZ G_k arrow
    op("Cl") ZZ G_(k - 1) plus.o op("Cl") S_k arrow 0,
  $
  $ 1 arrow C_(q') arrow D(ZZ G_k) arrow D(ZZ G_(k - 1)) arrow 0, $
  where $C_(q')$ is a cyclic group of order $q' = q slash (q,2)$.
] <th:keating-prime-power-metacyclic-class-kernel-sequences>
#source(281)
Matchett @bib:Matchett1976 showed that under the above hypotheses,
$ D(ZZ G_k) tilde.equiv D(ZZ H) plus.o (C_(q'))^((k)), $
the direct sum of $D(ZZ H)$ and $k$ copies of $C_(q')$.

A further generalization, due to Cassou-Noguès @bib:CassouNogues1975, showed
that if the odd prime $p$ is not assumed regular, then in fact#ed-note[
  The sequences in @th:keating-prime-power-metacyclic-class-kernel-sequences are
  stated here for even $q$ and $k>=1$, with $G_0=H$. The printed odd-$q$ claim
  fails for $p=7$, $q=3$, $k=2$: the weight-$3$ line of $D(ZZ C_49)^-$ is fixed
  by $C_3$, giving $C_7 plus.o C_3^2$ rather than $C_3^2$. For arbitrary $q$
  dividing $p-1$, Hironaka @bib:Hironaka1979, Proposition~1.3 and its proof,
  give the precise formula
  $
    D(ZZ G_k) tilde.equiv D(ZZ H) plus.o (C_(q'))^((k))
    plus.o D(ZZ C_(p^k))^H.
  $
  For regular $p$ and even $q$, the last summand vanishes by
  @cor:regular-cyclic-p-group-kernel-order, since $H$ contains inversion. The
  natural quotient maps then give the kernel $C_(q')$; applying
  @th:class-group-ring-homomorphism(iii) to the full overorder
  $ZZ G_(k-1) plus.o (ZZ[omega] compose H)$, whose second factor is hereditary,
  gives the class-group sequence. The split summand $D(ZZ H)$ must be retained,
  already when $k=1$.
]
$
  D(ZZ G_k) tilde.equiv D(ZZ H) plus.o (C_(q'))^((k)) plus.o "some" p "-group".
$

We now give a brief description of some results of Cassou-Noguès
@bib:CassouNogues1975 for the metacyclic group
$ G = chevron.l x, y: x^n = 1, y^q = 1, y x y^(-1) = x^r chevron.r, $
where $n$ is odd, $(n,q) = 1$, and the cyclic group
$H = chevron.l y: y^q = 1 chevron.r$ acts faithfully on each Sylow subgroup of
$C = chevron.l x: x^n = 1 chevron.r$. Keeping the notation of
@eq:cyclotomic-class-group-notation, let $sigma in op("Gal")(K_n slash QQ)$ be
defined by $(omega_n)^sigma = (omega_n)^r$. For each divisor $d$ of $n$, view
$K_d$ as a subfield of $K_n$, let $L_d$ be the subfield of $K_d$ fixed by
$sigma$, and put $S_d = "alg. int." lr({L_d})$. Then
$ QQ G tilde.equiv QQ H plus.o product.co_(d divides n, d > 1) K_d compose H. $
For $d > 1$, the action of $H$ on $K_d$ is faithful, so
$K_d compose H tilde.equiv M_q lr((L_d))$. The extension $K_d slash L_d$ is
tamely ramified; hence $R_d compose H$ is hereditary by
@i:th:twisted-group-ring-heredity. If $Gamma_d$ is a maximal overorder, then
@cor:hereditary-order-class-group-maximal-order and
@th:maximal-order-restricted-ideal-class-group give
$
  op("Cl") (R_d compose H) tilde.equiv op("Cl") Gamma_d
  tilde.equiv op("Cl") S_d.
$
There are exact sequences
$
  0 arrow D_0 lr((ZZ G)) arrow op("Cl") ZZ G arrow
  op("Cl") ZZ H plus.o product.co_(d divides n, d > 1) op("Cl") S_d arrow 0,
$
$ 0 arrow D_0 lr((ZZ G)) arrow D(ZZ G) arrow D(ZZ H) arrow 0, $
where $D_0 lr((ZZ G))$ is the kernel of the quotient-induced map
$D(ZZ G) arrow D(ZZ H)$. Further, induction gives a homomorphism
$ f': D(ZZ C) arrow D_0 lr((ZZ G)), $
whose cokernel is a direct sum of copies of the cyclic group $C_(q')$, where
$q' = q slash (q,2)$.
#source(282)
The number of copies is $Omega(n)$, the total number of prime divisors of $n$,
counting multiplicities. Consequently,
$ abs(D(ZZ G)) = abs(D(ZZ H)) abs(im f') (q')^(Omega(n)). $
Thus it remains to determine the image of induction as well as $D(ZZ H)$. In the
special case where $q$ is an odd prime, $D(ZZ H) = 0$.#ed-note[
  See Hironaka @bib:Hironaka1979, Proposition~1.3 and its proof, for these
  hypotheses and the induction-cokernel statement. Faithfulness on $C$ alone
  does not imply coprimality or faithfulness on every cyclotomic component; for
  example, $n=9$, $q=3$, $r=4$ violates coprimality. The component $d=1$ is
  $QQ H$, and the other crossed orders need only be hereditary, not maximal. The
  target of $f'$ is $D_0 lr((ZZ G))$; with target $D(ZZ G)$ its cokernel also
  contains the split summand $D(ZZ H)$.

  The original paragraph additionally attributes to Cassou-Noguès estimates for
  $abs(op("cok") f')$, and an explicit calculation when $q divides.not h_d$ for
  every $d divides n$, where $h_d$ is the ideal class number of $S_d$. For the
  induction map specified above, the cokernel already has the fixed structure
  displayed here; the missing term in the order calculation is its image.
]

For further results on $op("Cl") ZZ G$ and $D(ZZ G)$ when $G$ is metacyclic or
dihedral, see Endo–Miyata–Sekiguchi @bib:Endo1982, Prop. 4.4. We conclude this
subsection with a brief discussion as to which finite groups $G$ have the
property that the kernel group $D(ZZ G)$ is trivial. The case of abelian groups
is completely settled by Theorem
@th:cassou-nogues-abelian-trivial-kernel-classification. For non-abelian groups,
we have: #theorem(title: [Endo–Hironaka @bib:Endo1979])[
  A non-abelian group $G$ for which $D(ZZ G) = 0$ must be one of the groups
  $D_n, A_4, A_5$, or $S_4$.

  For $G = A_4, A_5$, or $S_4$, we have $D(ZZ G) = 0$ by Reiner–Ullom
  @bib:Reiner1974b. For $G = D_n$, the dihedral group of order $2 n$, we know
  that $D(ZZ G) = 0$ in the following cases:
  #enum(
    numbering: "(i)",
    [$n = "odd prime"$ (see
      @th:galovich-reiner-ullom-metacyclic-class-groups).],
    [$n = "power of a regular odd prime"$ (see
      @th:keating-prime-power-metacyclic-class-kernel-sequences).],
    [$n = "power of" 2$ (see @th:dihedral-two-group-trivial-kernel below).],
  )
] <th:endo-hironaka-nonabelian-trivial-kernel-restriction>
#idx(
  "Kernel group",
  "triviality of",
  target: [@th:endo-hironaka-nonabelian-trivial-kernel-restriction],
)
#idx(
  "Endo-Hironaka Theorem",
  target: [@th:endo-hironaka-nonabelian-trivial-kernel-restriction],
)
On the other hand, the results of Cassou-Noguès described above show that there
exist infinitely many pairs of distinct odd primes $p, q$ for which
$D(ZZ D_(p q)) != 0$. It seems difficult to determine precisely those integers
$n$ for which $D(ZZ D_n) = 0$. The best result in this direction is: #theorem(
  title: [Endo–Miyata @bib:Endo1980],
)[
  If $D(ZZ D_n)$ has odd order (possibly $1$), then $n = 2^r p^s q^t$ for some
  $r, s, t$ and some odd primes $p, q$. In particular, $D(ZZ D_n) = 0$ for
  $2 <= n < 60$, while $D(ZZ D_60)$ has order $2$.
] <th:endo-miyata-dihedral-odd-kernel-order>
#idx("Endo-Miyata Theorem", target: [@th:endo-miyata-dihedral-odd-kernel-order])

=== Dihedral and Quaternion 2-Groups <ss:dihedral-quaternion-class-groups>

We begin with a discussion of dihedral $2$-groups. The methods of
§@ss:metacyclic-class-groups do not apply to this case, and the calculations
needed are somewhat more subtle. The main result, due to Reiner–Ullom
@bib:Reiner1974b for the dihedral group of order $8$, and to
Fröhlich–Keating–Wilson @bib:Frohlich1974 for the general case, is as follows:
#theorem[
  For $G_n$ a dihedral group of order $2^(n+2)$, where $n >= 0$, the kernel
  group $D(ZZ G_n)$ is trivial.
] <th:dihedral-two-group-trivial-kernel>
#idx(
  "Fröhlich-Keating-Wilson Theorem",
  target: [@th:dihedral-two-group-trivial-kernel],
)
#proof[
  _Step 1._ For $n = 0$, $G_0$ is an elementary $(2,2)$-group, so
  $D(ZZ G_0) = 0$ (see Exercise @exc:klein-four-cyclic-four-kernel-groups). Now
  let $n > 0$, and let
  $
    G_n = chevron.l x, y: x^(2^(n+1)) = 1, y^2 = 1,
    y x y^(-1) = x^(-1) chevron.r
  $
  be the dihedral group of order $2^(n+2)$. We set
  $
    K = QQ(omega), quad R = ZZ[omega], quad L = QQ(omega + overline(omega)),
    quad S = ZZ[omega + overline(omega)] = "alg. int." lr({L}),
  $
  where $omega$ is a primitive $2^(n+1)$-st root of $1$.
  #source(283)
  Since $x^(2^(n+1)) - 1 = (x^(2^n) - 1)(x^(2^n) + 1)$, there is a fiber product
  #dihedral-two-group-fiber-square
  where $H = chevron.l y: y^2 = 1 chevron.r$. The maps $f_1, f_2$ are given by
  $ f_1 lr((x)) = x in G_(n-1), quad f_2 lr((x)) = omega in R, $
  and $Gamma$ is the twisted group ring of $H$ over $R$, in which $y$ acts on
  $R$ by complex conjugation: $y alpha = overline(alpha) y$, $alpha in R$.

  Consider the display
  #dihedral-cyclotomic-field-chart
  Here, $dim_L K = 2$ and $dim_QQ L = 2^(n-1)$. The only rational prime which
  ramifies in the extension $K slash QQ$ is $2$, and $2$ is completely ramified
  (see §@i:ss:cyclotomic-fields). Further, $pi_0 R$ and $pi S$ are prime ideals,
  and
  $
    2 S = (pi S)^(2^(n-1)), quad 2 R = (pi_0 R)^(2^n), quad
    pi R = pi_0^2 R; quad R slash pi_0 R tilde.equiv S slash pi S
    tilde.equiv ZZ slash 2 ZZ.
  $
  We observe that $Gamma$ is an $S$-order in the twisted group algebra
  $K compose H$, but $Gamma$ is _not_ hereditary, since $K$ is not tamely
  ramified over $L$. Since $K compose H tilde.equiv M_2 lr((L))$, we may write
  $
    QQ G_n tilde.equiv K compose H plus.o QQ G_(n-1), quad
    C tilde.equiv L plus.o tilde(C), quad frak(O) = S plus.o tilde(frak(O)),
  $
  where $C, tilde(C)$ are the centers of $QQ G_n, QQ G_(n-1)$, respectively, and
  where $frak(O), tilde(frak(O))$ are the integral closures of $ZZ$ in $C$ and
  $tilde(C)$, respectively.

  _Step 2._ By @th:frohlich-kernel-group-exact-sequence, there is an exact
  sequence
  $
    op("nr") U(Lambda) arrow
    (S^dot op("nr") U(Gamma)) / S^dot times
    (tilde(frak(O))^dot op("nr") U(Delta)) / tilde(frak(O))^dot
    arrow^g D(Lambda) arrow D(Gamma) plus.o D(Delta) arrow 0.
  $
  (Note that in this case, by @i:exm:dihedral-group-algebra-reduced-norm, we
  have $S^+ = S^dot$ and $tilde(frak(O))^+ = tilde(frak(O))^dot$.)
  #source(284)
  For each odd prime $p$, we see readily that $Lambda_p^dot = Gamma_p^dot
  times Delta_p^dot$, so in the above sequence we may replace the groups of unit
  ideles by their $2$-components. Thus, there is an exact sequence
  $
    op("nr") Lambda_2^dot arrow^h
    (S^dot op("nr") Gamma_2^dot) / S^dot times
    (tilde(frak(O))^dot op("nr") Delta_2^dot) / tilde(frak(O))^dot
    arrow^g D(Lambda) arrow D(Gamma) plus.o D(Delta) arrow 0.
  $
  <eq:dihedral-two-group-kernel-mayer-vietoris>
  Proceeding by induction on $n$, it therefore suffices to show that
  $D(Gamma) = 0$ and that $h$ is surjective.

  Now $Gamma_p$ is a maximal order for each odd prime $p$, so from
  @th:kernel-group-finite-prime-formula we obtain
  $ D(Gamma) tilde.equiv S_2^dot slash S^dot op("nr") Gamma_2^dot. $
  We now prove that $op("nr") Gamma_2^dot = S_2^dot$, and therefore
  $D(Gamma) = 0$. By @i:exm:dihedral-group-algebra-reduced-norm we may write
  $
    Gamma_2 = R_2 plus.o R_2 y, quad "and" quad
    op("nr")_(Gamma_2 slash S_2) lr((alpha + beta y)) =
    alpha overline(alpha) - beta overline(beta) quad "for" alpha, beta in R_2.
  $
  (Note that for $alpha in R_2$, $overline(alpha)$ is the image of $alpha$ under
  the automorphism of $R_2$ defined by $omega arrow omega^(-1)$.)

  When $n = 1$, the argument is simple, since in this case $S_2 = ZZ_2$, and
  each $u in S_2^dot$ has the form $u = 1 + 2 v$ with $v in S_2$. But then
  $ op("nr") ((v + 1) + v y) = (v + 1)^2 - v^2 = u, $
  so $op("nr") Gamma_2^dot = S_2^dot$, as desired.

  The proof when $n > 1$ is not much harder. In this case for $i >= 1$ and
  $alpha, beta in R_2$, we obtain
  $
    op("nr") (1 + pi^i lr((alpha + beta y))) equiv
    1 + pi^i lr((alpha + overline(alpha))) equiv 1 (mod pi^(i+1) S_2),
  $
  since $alpha + overline(alpha) equiv 0 (mod pi S_2)$. This shows that
  $op("nr")(1 + pi^i Gamma_2) subset.eq 1 + pi^(i+1) S_2$ for $i >= 1$. On the
  other hand, for $pi_0 = 1 - omega$ as above,
  $
    op("nr")(1 + pi^i pi_0) = (1 + pi^i pi_0)(1 + pi^i overline(pi)_0)
    equiv 1 + pi^(i+1) (mod pi^(2 i+1))
  $
  for $i >= 1$. Now each $u in 1 + pi^2 S_2$ is of the form
  $u = 1 + sum_(i=2)^infinity a_i pi^i$, with $a_i in lr({0,1})$. Since $R_2$ is
  complete, it follows from the above discussion that
  $ op("nr")(1 + pi Gamma_2) = 1 + pi^2 S_2. $
  Therefore
  $ abs(S_2^dot: op("nr") Gamma_2^dot) <= abs(S_2^dot: 1 + pi^2 S_2) = 2. $
  However, since $n > 1$ we have
  $
    op("nr")(1 + omega + y) = 1 + omega + overline(omega) = 3 - pi
    equiv 1 + pi (mod pi^2 S_2),
  $
  and therefore $op("nr") Gamma_2^dot supset 1 + pi^2 S_2$. It follows that
  $op("nr") Gamma_2^dot = S_2^dot$, which shows that $D(Gamma) = 0$, as claimed.

  #source(285)
  _Step 3._ It remains for us to prove that the map $h$ occurring in
  @eq:dihedral-two-group-kernel-mayer-vietoris is surjective. Consider the fiber
  product used in defining the map $h$, namely
  #completed-dihedral-fiber-square
  Then
  $
    f_1 lr({1 + (x^(2^n) - 1) Lambda_2}) = 1, quad
    f_2 lr({1 + (x^(2^n) - 1) Lambda_2}) = 1 + 2 Gamma_2,
  $
  and consequently
  $ im h supset.eq op("nr")(1 + 2 Gamma_2) times 1. $
  On the other hand, the map $Lambda_2^dot arrow Delta_2^dot$ is surjective by
  @lem:semilocal-quotient-unit-surjectivity, so $im(h)$ covers the factor
  $tilde(frak(O))^dot op("nr") Delta_2^dot slash
  tilde(frak(O))^dot$. It therefore suffices to prove that
  $ S^dot op("nr") Gamma_2^dot = S^dot op("nr")(1 + 2 Gamma_2). $
  But $op("nr") Gamma_2^dot = S_2^dot$ and
  $op("nr")(1 + 2 Gamma_2) = 1 + 2 pi S_2$, by Step 2. Thus we must show that
  $ S_2^dot = S^dot (1 + 2 pi S_2). $
  <eq:dihedral-real-cyclotomic-global-local-units>
  This is obvious when $n = 1$, for the desired equality becomes
  $ZZ_2^dot = lr({plus.minus 1}) dot (1 + 4 ZZ_2)$, which is clearly true. Now
  let $n > 1$ and consider the map $rho: S^dot arrow S_2^dot slash
  (1 + 2 pi S_2)$. We shall prove
  @eq:dihedral-real-cyclotomic-global-local-units by showing that $rho$ is
  surjective. The proof will require some deep results from algebraic number
  theory. Since there is a surjection
  $ S_2^dot slash (1 + 4 S_2) arrow S_2^dot slash (1 + 2 pi S_2), $
  it suffices to prove the (harder) result that
  $ tau: S^dot arrow S_2^dot slash (1 + 4 S_2) $
  is surjective.

  To simplify the notation, we set
  $
    U = S_2^dot = lr({1 + sum_(i=1)^infinity a_i pi^i: a_i = 0 "or" 1}),
    quad U^2 = lr({u^2: u in U}).
  $
  #source(286)
  We wish to show that $U = tau(S^dot)(1 + 4 S_2)$; for this, it suffices to
  prove that
  $ U = U^2 tau(S^dot)(1 + 4 S_2), $
  <eq:dihedral-global-units-modulo-local-squares>
  for then we obtain the desired result by applying Nakayama's Lemma to the
  finite $2$-group $U slash (1 + 4 S_2)$.

  We need an elementary result from local field theory:
]
#lemma[
  Keeping the above notation, set
  $ W = U slash U^2(1 + 4 S_2). $
  Then $W$ is an elementary abelian $2$-group on $2^(n-1)$ generators.
] <lem:real-cyclotomic-local-units-square-quotient>
#proof[
  The only roots of unity in $QQ_2 lr((omega + omega^(-1)))$ are $plus.minus 1$,
  so the group structure of $U$ is given by
  $
    U tilde.equiv lr({plus.minus 1}) times
    lr({2^(n-1) "copies of the additive group" ZZ_2})
  $
  (see, for example, Serre @bib:Serre1962, p. 220, Prop. 10 or Long
  @bib:Long1977, p. 63, Th. 2.9). It follows that $U slash U^2$ is an elementary
  abelian $2$-group on $2^(n-1) + 1$ generators, and we may view $U slash U^2$
  as a vector space over $overline(ZZ)$ $(= ZZ slash 2 ZZ)$ of dimension
  $2^(n-1) + 1$. Further (see Long @bib:Long1977, p. 64, Prop. 2.11)
  $ 1 + 4 S_2 subset.eq.not U^2, quad "and" quad 1 + 4 pi S_2 subset.eq U^2. $
  Since $abs(1 + 4 S_2: 1 + 4 pi S_2) = lr(|S_2: pi S_2|) = 2$, it then follows
  that $dim_(overline(ZZ)) W = 2^(n-1)$, as desired.
]
#proof(head: none)[
  _Step 4._ To complete the proof of the theorem, we must show that the natural
  map $phi: S^dot arrow W$ is surjective. We shall use Hilbert symbols to
  construct a symmetric bilinear form $F: W times W arrow
  overline(ZZ)$, and we shall find $2^(n-1)$ units $lr({u_i})$ in $S$ such that
  $ F(phi(u_i), phi(u_j)) = delta_(i j), quad 1 <= i, quad j <= 2^(n-1). $
  The images $lr({phi(u_i)})$ thus form an orthonormal $overline(ZZ)$-basis for
  $W$, and consequently $phi$ is surjective.

  We begin by reviewing some basic facts about Hilbert symbols, generalizing the
  discussion in §@ss:k2-symbols. For more details on these symbols, we refer the
  reader to Cassels–Fröhlich @bib:Cassels1967, pages 351–353. For the moment,
  let $K$ be an arbitrary algebraic number field, and let
  $R = "alg. int." lr({K})$. For $P$ ranging over the primes of $lr({K})$,
  finite or infinite, let $K_P, R_P$ denote $P$-adic completions (with
  $R_P = K_P$ for $P$ infinite).

  Given a prime $P$ of $K$, there is a Hilbert symbol $(a,b)_P$, defined for
  $a,b in K_P^dot$, whose values are $plus.minus 1$. Specifically, we define
  $
    (a,b)_P = 1 arrow.double.l.r a x^2 + b y^2 = 1
    "has a solution with" x,y in K_P.
  $
  #source(287)
  This symbol is a special case of the norm residue symbol, corresponding to
  Kummer extensions defined by square roots. Equivalently,
  $
    (a,b)_P = 1 arrow.double.l.r b "is a norm from"
    K_P lr((sqrt(a))) "to" K_P.
  $
  This symbol satisfies the following identities:
  $
    (a,b)_P = (b,a)_P, quad (a a',b)_P = (a,b)_P (a',b)_P,
    quad (a x^2,b)_P = (a,b)_P
  $
  where $a,a',b,x in K_P^dot$. Furthermore, we have:
  #enum(
    numbering: "(1)",
    [Let $P$ be a finite prime of $K$, and assume that $q = op("card") R
      slash P$ is odd. Let $v$ be the exponential $P$-adic valuation of $K_P$.
      For $a,b in K_P^dot$, define
      $ c = (-1)^(v(a) v(b)) a^(v(b)) slash b^(v(a)) in R_P^dot. $
      (Compare with the tame symbol defined in the proof of
      @th:tate-k2-rationals.) Then
      $ (a,b)_P equiv c^((q-1) slash 2) (mod P). $
      In particular, in this case
      $ (a,b)_P = 1 quad "for all" a,b in R_P^dot. $],
    [For any prime $P$ of $K$, let $a in K_P^dot$ be such that the prime $P$ is
      unramified in the extension $K_P lr((sqrt(a))) slash K_P$. Then every
      $b in R_P^dot$ is a norm from $K_P lr((sqrt(a)))$, and consequently
      $ (a,b)_P = 1 quad "for all" b in R_P^dot. $],
    [_(Product Formula)_ For $a,b in K^dot$ there is an identity
      $ product_P (a,b)_P = 1, $
      where $P$ ranges over all primes of $K$. (Compare with the Hilbert
      Reciprocity Theorem @th:hilbert-reciprocity.) Further, if $P$ is a
      non-archimedean prime which does not contain the rational prime $2$, then
      $(a,b)_P = 1$ for all $a,b in R^dot$.],
  )
  After these preliminaries, we are ready to return to our study of the
  $overline(ZZ)$-space $W = U slash U^2(1 + 4 S_2)$, where
  $
    L_2 = QQ_2 lr((omega + omega^(-1))), quad
    S_2 = ZZ_(2)[omega + omega^(-1)], quad U = S_2^dot.
  $
  #source(288)
  We are trying to show that the natural map $phi: S^dot arrow W$ is a
  surjection. Let $P_2 = pi S_2$ be the prime ideal in the valuation ring in
  $L_2$. We intend to define a bilinear form $F: W times W arrow
  lr({plus.minus 1})$ by setting
  $ F(a,b) = (a,b)_(P_2) quad "for" a,b in U. $
  To prove that $F$ is well-defined, we note first that $F(a,b) = 1$ if either
  $a in U^2$ or $b in U^2$. Next, let $d in 1 + 4 S_2$, $d in.not U^2$; then
  $(1 plus.minus sqrt(d)) slash 2$ lies in the valuation ring of
  $L_2 lr((sqrt(d)))$, and so $P_2$ is unramified in the extension
  $L_2 lr((sqrt(d))) slash L_2$. It follows that $(d,b)_(P_2) = 1$ for all
  $b in U$. This shows that $F$ is indeed well-defined (and bilinear).

  We now make use of:
]
#theorem(name: [Weber's Theorem], numbered: false)[
  Let $L = QQ(omega + omega^(-1))$, $S = "alg. int." lr({L})$, where $omega$ is
  a primitive $2^(n+1)$-st root of $1$, and $n >= 1$. Let
  $lr({frak(q)_i: 1 <= i <= 2^(n-1)})$ be the infinite primes of $L$
  (necessarily real primes). Then for each $i$, $1 <= i <= 2^(n-1)$, there
  exists a unit $u_i in S^dot$ such that
  $
    u_i < 0 "in" L_(frak(q)_i), quad "and" quad
    u_i > 0 "in each" L_(frak(q)_j), quad j != i.
  $
  (See Hasse @bib:Hasse1952, p. 29.)
] <th:weber-real-cyclotomic-unit-signatures>
#idx("Weber's Theorem", target: [@th:weber-real-cyclotomic-unit-signatures])
#proof(head: none)[
  From the definition of the Hilbert symbol, it follows at once that
  $
    (u_i,u_i)_(frak(q)_i) = -1, quad "and" quad
    (u_i,u_j)_(frak(q)_k) = +1 quad "if" i,j,k "do not coincide".
  $
  Since $pi S$ is the unique prime ideal of $S$ containing $2$, the Product
  Formula now gives
  $ (u_i,u_j)_(P_2) = (-1)^(delta_(i j)), quad 1 <= i,j <= 2^(n-1). $
  This implies that the images $lr({phi(u_i): 1 <= i <= 2^(n-1)})$ form an
  orthonormal $overline(ZZ)$-basis of $W$ relative to the form $F$. Therefore
  $phi$ is surjective, which completes the proof of
  @eq:dihedral-global-units-modulo-local-squares and establishes the theorem.
]

#remark[
  For another proof of Theorem @th:dihedral-two-group-trivial-kernel for the
  case $n = 1$, see Wall @bib:Wall1974c.
] <rem:dihedral-eight-kernel-alternative-proof>

We turn next to the quaternion group
$
  G_n = chevron.l x,y: x^(2^(n+1)) = 1, x^(2^n) = y^2,
  y x y^(-1) = x^(-1) chevron.r
$
of order $2^(n+2)$. Fröhlich–Keating–Wilson @bib:Frohlich1974 proved: #theorem[
  Let $G_n$ be the generalized quaternion group of order $2^(n+2)$, where
  $n >= 1$. Then#footnote[
    The nontrivial element of $D(ZZ G_n)$ is represented by $I + 3 ZZ G_n$,
    where $I$ is the augmentation ideal of $ZZ G_n$; see Swan @bib:Swan1983,
    Remark 9.9, and @th:quaternion-swan-subgroup-order-two.
  ] $abs(D(ZZ G_n)) = 2$.
] <th:quaternion-two-group-kernel-order-two>
#idx(
  "Fröhlich-Keating-Wilson Theorem",
  target: [@th:quaternion-two-group-kernel-order-two],
)
#source(289)
#proof[
  The special case where $G$ is the quaternion group of order $8$ was first
  proved independently by Martinet @bib:Martinet1971 and Reiner–Ullom
  @bib:Reiner1972. Other versions for this case are given by Keating
  @bib:Keating1973, Reiner–Ullom @bib:Reiner1974b, and Wall @bib:Wall1974c. Here
  we shall prove the theorem only for this case, and refer the reader to the
  article by Fröhlich–Keating–Wilson @bib:Frohlich1974 for the general case.
  #idx("Quaternion group")

  For $G$ the quaternion group of order $8$, we start with the fiber product
  #quaternion-eight-fiber-square
  where $H = chevron.l x,y: x^2 = y^2 = 1, x y = y x chevron.r$,
  $overline(ZZ) = ZZ slash 2 ZZ$, $R = ZZ[i]$, and where $Gamma$ is the ring of
  integral quaternions, that is,
  $
    y^2 = -1, quad y alpha = overline(alpha) y "in" Gamma,
    quad "for" alpha in R.
  $
  The maps $f_j$ are given by $f_1 lr((x)) = x$, $f_2 lr((x)) = i$,
  $f_1 lr((y)) = f_2 lr((y)) = y$.

  As in @eq:dihedral-two-group-kernel-mayer-vietoris, there is an exact sequence
  $
    op("nr") Lambda_2^dot arrow^h
    (ZZ^+ op("nr") Gamma_2^dot) / ZZ^+ times
    (Delta^dot Delta_2^dot) / Delta^dot arrow D(Lambda) arrow
    D(Gamma) plus.o D(Delta) arrow 0,
  $
  where $ZZ^+ = ZZ^dot inter QQ^+ = lr({1})$. (We have used the fact that
  $op("nr") Delta_2^dot = Delta_2^dot$.) We already know from Exercise
  @exc:klein-four-cyclic-four-kernel-groups that $D(Delta) = 0$. Next, we
  observe that $D(Gamma) tilde.equiv ZZ_2^dot slash
  op("nr") Gamma_2^dot$. But for $alpha + beta y in Gamma_2$, where
  $alpha = a_1 + a_2 i in R_2$, $beta = b_1 + b_2 i in R_2$, with each
  $a_j,b_j in ZZ_2$, we have
  $
    op("nr")(alpha + beta y) = alpha overline(alpha) + beta overline(beta)
    = a_1^2 + a_2^2 + b_1^2 + b_2^2.
  $
  Thus, $op("nr") Gamma_2^dot$ contains $1,3,5,7$. But also
  $op("nr") Gamma_2^dot$ contains $1 + 8 ZZ_2$ (see the argument in Step 2 of
  the proof of @th:dihedral-two-group-trivial-kernel). Therefore
  $op("nr") Gamma_2^dot = ZZ_2^dot$, so $D(Gamma) = 0$.

  Finally, we must show that $abs(op("cok") h) = 2$. Since
  $op("nr") Lambda_2^dot$ maps onto $Delta_2^dot$, it follows that
  $ op("cok") h tilde.equiv ZZ_2^dot slash im X, $
  where $X = lr({u in Lambda_2^dot: f_1 lr((u)) = 1 "in" Delta_2^dot})$. Then
  $f_2 lr((X)) = 1 + 2 Gamma_2$, and for $alpha,beta in R_2$ we have
  $
    op("nr")(1 + 2 alpha + 2 beta y) =
    (1 + 2 alpha)(1 + 2 overline(alpha)) + 4 beta overline(beta) in ZZ_2^dot.
  $
  This readily implies that $op("nr")(1 + 2 Gamma_2) = 1 + 4 ZZ_2$, so
  $ op("cok") h tilde.equiv (1 + 2 ZZ_2) slash (1 + 4 ZZ_2). $
  Therefore $abs(op("cok") h) = 2$, as claimed.
]

#source(290)
=== An Involution on Class Groups and Kernel Groups
<ss:class-kernel-group-involution>

Let $G$ be a finite group, and set
$ Lambda = R G, quad A = K G, quad "where" R = "alg. int." lr({K}). $
Let $tau$ be the involution of $Lambda$ defined by $g mapsto g^(-1)$, $g in G$,
extended by linearity. Then $tau$ is an anti-automorphism of $Lambda$, and
extends to an involution on $A$ and on the idele group $J(A)$. Further, $tau$
induces an automorphism on the center $C$ of $A$, and its idele group $J(C)$.
Let us show that $tau$ acts on the class group $op("Cl") Lambda$ and the kernel
group $D(Lambda)$.
#idx("Involution (on class group)")

For any left $Lambda$-module $M$, let $M^* = op("Hom")_R lr((M,R))$ be its dual,
viewed as right $Lambda$-module. We make $M^*$ into a left $Lambda$-module
$tilde(M)$, the _contragredient_ of $M$, by defining
$ x dot m^* = m^* tau(x) quad "for" x in Lambda, m^* in M^*. $
#idx("Contragredient")
By @i:prop:frobenius-right-adjoint, we have
$M^* tilde.equiv op("Hom")_Lambda lr((M,Lambda))$, and we treat this isomorphism
as an identification. In particular, when $M = Lambda a$ is principal, where
$a in A^dot$, then
$ M^* = op("Hom")_Lambda lr((Lambda a,Lambda)) tilde.equiv a^(-1) Lambda. $
We claim that there is a left $Lambda$-isomorphism
$
  f: tilde(M) tilde.equiv Lambda tau(a^(-1)), quad "given by"
  f(a^(-1) lambda) = tau(lambda) tau(a^(-1)) quad "for" lambda in Lambda.
$
Indeed, for $x in Lambda$ and for each $lambda in Lambda$, we have
$
  f(x dot a^(-1) lambda) = f(a^(-1) lambda tau(x))
  = tau(lambda tau(x)) tau(a^(-1))
  = x tau(lambda) tau(a^(-1)) = x f(a^(-1) lambda).
$
Thus, the contragredient of $Lambda a$ is isomorphic to the left $Lambda$-ideal
$Lambda tau(a^(-1))$. Of course, the ideal $Lambda$ is self-contragredient.

Now let $alpha in J(A)$, and take $M = Lambda alpha$. Since $tau$ commutes with
$P$-adic completion, the above remarks show that
$
  "contragredient of" Lambda alpha tilde.equiv Lambda tau(alpha^(-1))
  = Lambda tau(alpha)^(-1), quad alpha in J(A).
$
The action of the involution $tau$ on $op("Cl") Lambda$ is given by
$ tau[Lambda alpha] = [Lambda tau(alpha)] quad "for" alpha in J(A), $
or equivalently,
$ tau[M] = ["contragredient of" M^(-1)], quad [M] in op("Cl") Lambda, $
where $M^(-1)$ means the inverse of $M$ in $op("Cl") Lambda$.

#source(291)
It follows readily that $tau$ acts as an involution on $D(Lambda)$; for if
$[M] in D(Lambda)$, then also $[M^(-1)] in D(Lambda)$, and hence
$ M^(-1) plus.o X tilde.equiv Lambda plus.o X $
for some f.g. $Lambda$-module $X$. Taking contragredients, and using the fact
that $Lambda$ is self-contragredient, it follows at once that
$tau[M] in D(Lambda)$, as desired.

The involution $tau$ acts on the idele group $J(C)$, where $C$ is the center of
$A$, and $tau$ commutes with the isomorphisms
$
  op("Cl") Lambda tilde.equiv J(C) / (C^+ product op("nr") Lambda_P^dot),
  quad D(Lambda) tilde.equiv
  (C^+ product frak(O)_P^dot) / (C^+ product op("nr") Lambda_P^dot)
$
given in @th:class-group-reduced-norm-ideles and
@th:kernel-group-unit-idele-formula.

We now concentrate on the case $Lambda = ZZ G$, $A = QQ G$, and begin with an
easy result: #proposition[
  For $A = QQ G$, the involution $tau$ maps each simple component $A_i$ of $A$
  onto itself, and induces the complex conjugation map on the center $K_i$ of
  $A_i$.
] <prop:group-inversion-simple-component-conjugation>
#proof[
  Let $A_i$ afford the character $mu_i$ of $G$. Then $tau(A_i)$ is also a simple
  component of $A$, and affords the character
  $ g mapsto mu_i lr((g^(-1))), quad g in G. $
  But $mu_i lr((g^(-1))) = overline(mu_i lr((g)))$, $g in G$, where bar denotes
  complex conjugation (see the discussion preceding
  @i:prop:class-function-orthonormal-basis). Further,
  $overline(mu_i lr((g))) = mu_i lr((g))$ for all $g in G$, since $mu_i$ takes
  values in $QQ$. It follows that $tau(A_i) = A_i$, as claimed.

  Furthermore, the center $K_i$ of $A_i$ is a subfield of a cyclotomic field
  $QQ(omega)$, with $omega$ a root of unity. Then $tau$ induces an automorphism
  of $K_i$ by means of the map $omega mapsto omega^(-1)$, noting that
  $tau(K_i) = K_i$ since $K_i$ is a Galois extension of $QQ$. This completes the
  proof.
]

#example(numbered: false)[
  Let $G$ be cyclic of order $p$, and keep the notation of
  @eq:cyclotomic-class-group-notation. Each $[M] in op("Cl") ZZ G$ is
  represented by an ideal class $[frak(a)] in op("Cl") R$, and $[M^(-1)]$ by
  $[frak(a)^(-1)]$. If $tilde(M)$ denotes the contragredient of $M$, then the
  preceding discussion shows that
  $ [tilde(M)] "corresponds to" [overline(frak(a))^(-1)] in op("Cl") R, $
  where bar denotes complex conjugation. This result was pointed out by Reiner
  @bib:Reiner1968.
] <exm:contragredient-cyclic-prime-ideal-class>

For any additive group $D$ on which an involution $tau$ acts, we set
$
  D^+ = lr({x in D: tau(x) = x}) quad "and" quad
  D^- = lr({x in D: tau(x) = -x}).
$
#source(292)
We call $D^+$ and $D^-$ the “plus part” and “minus part” of $D$, respectively.
We shall now give Fröhlich's @bib:Frohlich1972 calculation of the order of
$D^-(Lambda)$, where $Lambda = ZZ G$ with $G$ an abelian $p$-group and $p$ an
odd prime. Here, $D^-(Lambda)$ denotes the minus part of the kernel group
$D(Lambda)$ on which the canonical involution $tau$ acts, where $tau$ is as
above. This calculation generalizes earlier results of Kervaire–Murthy
@bib:Kervaire1977 for the case where $G$ is a cyclic $p$-group; their work
circulated in preprint form in the late 1960s.

Let $A = QQ G$ where $G$ is an abelian $p$-group, $p$ odd. By Exercise
@exc:abelian-rational-wedderburn-components, we may write
$
  A = product.co_(i=0)^m K_i, quad "where" K_i = QQ(omega_i),
  quad omega_i = p^(s_i) "-th root of" 1.
$ <eq:abelian-p-group-cyclotomic-components>
The simple component $QQ$ occurs exactly once in $A$, and we set $K_0 = QQ$.
Since $A$ has no other $G$-trivial summands, we have $s_i >= 1$ for
$1 <= i <= m$. By @prop:group-inversion-simple-component-conjugation, $tau$ acts
as the identity on $K_0$, and as complex conjugation on each $K_i$. There is a
unique maximal $ZZ$-order $Gamma$ in $A$, given by
$
  Gamma = product.co_(i=0)^m R_i, quad "where"
  R_i = "alg. int." lr({K_i}) = ZZ[omega_i] "for each" i.
$ <eq:abelian-p-group-cyclotomic-maximal-order>
Clearly $tau(Gamma) = Gamma$, and indeed $tau(R_i) = R_i$ for each $i$. As in
§@ss:p-group-kernel-groups, the rational prime $p$ ramifies completely in $K_i$,
and thus
$
  p R_i = P_i^(e_i), quad "where" e_i = phi(p^(s_i)), quad 1 <= i <= m.
$
The $p$-adic and $P_i$-adic completions of $R_i$ coincide, and will be denoted
by $hat(R)_i$, for each $i$.

In order to calculate $abs(D^-(Lambda))$, we shall use formula
@eq:p-group-kernel-reduced-norm-quotient for $D(Lambda)$. In this case where $A$
is commutative, the ring $frak(O)$ coincides with $Gamma$, and $frak(O)^+$ with
$Gamma^dot$. Further, the reduced norm map is the identity map, so we obtain
$ D(Lambda) tilde.equiv Gamma_p^dot slash (Gamma^dot Lambda_p^dot). $
We show at once that the sequence
$
  1 arrow Gamma^dot slash Lambda^dot arrow
  Gamma_p^dot slash Lambda_p^dot arrow D(Lambda) arrow 0
$ <eq:abelian-p-group-kernel-unit-sequence>
is exact. In view of the preceding formula for $D(Lambda)$, we need only prove
that $Gamma^dot inter Lambda_p^dot = Lambda^dot$. But this is clear, since
$Lambda_q = Gamma_q$ for primes $q != p$, so
$
  Gamma^dot inter Lambda_p^dot subset.eq
  lr(inter_(q != p) Lambda_q^dot) inter Lambda_p^dot = Lambda^dot.
$
Note that by Exercise @exc:order-unit-group-finite-index, the quotient groups in
@eq:abelian-p-group-kernel-unit-sequence are finite. Further, $D(Lambda)$ is a
finite $p$-group by Theorem @th:p-group-integral-kernel-is-p-group.

#source(293)
Keeping the notation of @eq:abelian-p-group-cyclotomic-maximal-order, we have
$
  Gamma_p = product.co hat(R)_i, quad
  N = op("rad") Gamma_p = product.co hat(P)_i.
$ <eq:abelian-p-group-completed-order-radical>
Then $Gamma_p slash N tilde.equiv product.co ZZ slash p ZZ$, so
$(Gamma_p slash N)^dot$ is a finite group of order prime to $p$. Therefore
$1 + N$ is a subgroup of $Gamma_p^dot$ of index prime to $p$. Since $D(Lambda)$
is a $p$-group, it follows from @eq:abelian-p-group-kernel-unit-sequence that
$1 + N$ maps onto $D(Lambda)$, and there is an exact sequence
$
  1 arrow (Gamma^dot inter (1+N)) / (Lambda^dot inter (1+N)) arrow
  (1+N) / (Lambda_p^dot inter (1+N)) arrow D(Lambda) arrow 0.
$ <eq:abelian-p-group-principal-unit-sequence>
Further, $tau$ acts on each of the groups $Gamma^dot inter (1+N)$,
$Lambda^dot inter (1+N)$, etc., in the above formula, and the maps in
@eq:abelian-p-group-principal-unit-sequence commute with $tau$. Since $2$ acts
invertibly on $D(Lambda)$, it follows from Exercise
@exc:involution-minus-part-exactness that
$
  abs(D^-(Lambda)) = k slash l, quad "where"
  k = "order of minus part of" (1+N) / (Lambda_p^dot inter (1+N)), \
  l = "order of minus part of"
  (Gamma^dot inter (1+N)) / (Lambda^dot inter (1+N)).
$ <eq:minus-kernel-group-principal-unit-orders>
We shall proceed to calculate $k$ and $l$ explicitly, and begin with: #lemma[
  Let $N = op("rad") Gamma_p$ and $M = Lambda_p inter N$, viewed as additive
  groups on which the involution $tau$ acts. Then
  $Lambda_p^dot inter (1+N) = 1+M$, and
  $ k = "order of the minus part of" N slash M. $
] <lem:principal-unit-minus-order-additive-quotient>
#proof[
  The equality $Lambda_p^dot inter (1+N) = 1+(Lambda_p inter N)$ is obvious. Now
  set
  $ G_r = 1+N^r+M quad "and" quad H_r = N^r+M, quad r >= 1, $
  so $G_r$ is a multiplicative subgroup of $1+N$, and $H_r$ an additive subgroup
  of $N$. We have
  $ G_1 = 1+N, quad G_s = 1+M $
  for sufficiently large $s$, using the fact that $N^s subset Lambda_p$ for
  large $s$ (see @i:prop:finite-algebra-local-base-radical). Likewise,
  $ H_1 = N, quad H_s = M, $
  and $tau$ acts on all of the $lr({G_r})$ and $lr({H_r})$. For $r >= 1$, there
  is an isomorphism
  $
    H_r / H_(r+1) = (N^r+M) / (N^(r+1)+M)
    tilde.equiv (1+N^r+M) / (1+N^(r+1)+M) = G_r / G_(r+1)
  $
  #source(294)
  given by $alpha in H_r mapsto 1+alpha in G_r$. This isomorphism preserves the
  action of $tau$. But $H_r slash H_(r+1)$ is a finite $p$-group since $p in N$,
  whence so is $G_r slash G_(r+1)$.

  Now consider the filtrations
  $
    1+N = G_1 supset.eq G_2 supset.eq dots supset.eq G_s = 1+N^s+M, \
    N = H_1 supset.eq H_2 supset.eq dots supset.eq H_s = N^s+M.
  $
  The factor groups are finite groups of odd order, so by Exercise
  @exc:involution-minus-part-exactness we deduce that
  $
    abs(lr({G_1 slash G_s})^-) =
    product_(r=1)^(s-1) abs(lr({G_r slash G_(r+1)})^-) =
    product_(r=1)^(s-1) abs(lr({H_r slash H_(r+1)})^-) =
    abs(lr({H_1 slash H_s})^-),
  $
  which proves the lemma.
]

We are trying to calculate the order $k$ of the minus part of $N slash M$; by
Exercise @exc:involution-minus-part-exactness we have
$ k = abs(N^- slash M^-), $
since $N slash M$ is a finite $p$-group by the proof of the above lemma. The
group $N$ is given by @eq:abelian-p-group-completed-order-radical. For each $i$,
$1 <= i <= m$, we have#footnote[
  Here, bar denotes the unique involution in
  $op("Gal")(hat(K)_i slash hat(QQ))$. The congruence holds for
  $alpha = omega_i$ since $hat(P)_i = (1-omega_i) hat(R)_i$, and hence it holds
  for all $alpha in hat(R)_i$ because $hat(R)_i = hat(ZZ)[omega_i]$.
]
$ alpha equiv overline(alpha) (mod hat(P)_i) quad "for" alpha in hat(R)_i. $
Then
$
  hat(R)_i^- = lr({alpha in hat(R)_i: tau(alpha) = -alpha})
  = lr({alpha in hat(R)_i: overline(alpha) = -alpha}) \
  = lr({alpha in hat(P)_i: overline(alpha) = -alpha}) = hat(P)_i^-.
$
This shows that
$
  N^- = (Gamma_p)^- quad "and" quad
  M^- = (N inter Lambda_p)^- = (Gamma_p)^- inter (Lambda_p)^- = (Lambda_p)^-.
$
Since $Gamma_p slash Lambda_p$ is a finite $p$-group, we may apply Exercise
@exc:involution-plus-minus-decomposition to conclude that
$ k = lr(|Gamma_p: Lambda_p|) slash lr(|Gamma_p^+: Lambda_p^+|). $
We intend to use discriminants to calculate these indices.

Let $T: A_p times A_p arrow QQ_p$ be the bilinear trace form
$ (x,y) mapsto op("Tr")_(A_p slash QQ_p) lr((x y)) quad "for" x,y in A_p. $
Then $T$ is a nondegenerate symmetric bilinear form, extending the usual trace
form $A times A arrow QQ$. If $Lambda_p = plus.o_(i=1)^t hat(ZZ) x_i$, we define
the discriminant
$ d(Lambda_p) = det(T(x_i x_j))_(1 <= i,j <= t). $

#source(295)
Then $d(Lambda_p)$ is uniquely determined up to a unit factor from the ring
$hat(ZZ)$ of $p$-adic integers (see §@i:ss:duals-lattices). By
@i:prop:lattice-discriminant-index we have
$
  lr(|Gamma_p: Lambda_p|)^2 = "power of" p "in" d(Lambda_p) / d(Gamma_p).
$
Likewise, consider the intrinsic regular trace form
$T^+: A_p^+ times A_p^+ arrow QQ_p$ of the algebra $A_p^+$, where
$A_p^+ = "plus part of" A_p = lr({x in A_p: tau(x) = x})$, and we have
$
  lr(|Gamma_p^+: Lambda_p^+|)^2 =
  "power of" p "in" d(Lambda_p^+) / d(Gamma_p^+).
$
Thus we obtain
$
  k^2 = p "-part of" d(Lambda_p) / d(Gamma_p) dot
  d(Gamma_p^+) / d(Lambda_p^+).
$
We shall now compute the $p$-part of $d(Gamma_p^+) slash d(Gamma_p)$, and for
this it suffices to treat separately each summand $hat(R)_i$ of $Gamma_p$. Let
$1 <= i <= m$, and keep the notation in
@eq:abelian-p-group-cyclotomic-maximal-order. Since the discriminant
$d(R_i slash ZZ)$ is a power of $p$, and is unaffected by passage to $p$-adic
completion, it follows that
$ p "-part of" d(Gamma_p^+) / d(Gamma_p) = d(Gamma^+) / d(Gamma). $
We now use (see Exercise @exc:cyclotomic-real-discriminant-ratio for proof):
#lemma[
  Let $K = QQ(omega)$, $R = ZZ[omega]$, where $omega$ is a primitive $p^s$-th
  root of $1$, with $p$ odd and $s >= 1$. Let
  $
    K_0 = QQ(omega + overline(omega)), quad
    R_0 = ZZ[omega + overline(omega)] = "alg. int." lr({K_0}),
  $
  so $K_0$ is the unique maximal real subfield of $K$. Then
  $
    d(R) / d(R_0) = p^(f(s)), quad "where"
    f(s) = 1/2 (s p^s - (s+1) p^(s-1) + 1).
  $
] <lem:cyclotomic-real-discriminant-ratio>
Now let us set
$ w_s = "number of cyclic subgroups of" G "of order" p^s. $
<eq:cyclic-subgroup-multiplicities>
In view of the isomorphism $G tilde.equiv op("Hom")(G,CC^dot)$, it follows that
$w_s$ is also the number of quotient groups of $G$ which are cyclic of order
$p^s$. Hence $w_s$ equals the number of simple summands of $QQ G$ which are
isomorphic to $QQ(omega)$, $omega = "primitive" p^s "-th root of" 1$. From
@lem:cyclotomic-real-discriminant-ratio we obtain
$ d(Gamma) / d(Gamma^+) = p^e, quad "where" e = sum_(s >= 1) w_s f(s). $
We shall now carry out the same computation for $d(Lambda_p)$ and
$d(Lambda_p^+)$. By @i:prop:group-ring-maximality we know that
#source(296)
$ d(Lambda) = (p^n)^(p^n), quad "where" abs(G) = p^n. $
(Here, we use the $ZZ$-basis of $Lambda$ consisting of the elements of $G$.)
Thus, $d(Lambda)$ coincides with the $p$-part of $d(Lambda_p)$; likewise
$d(Lambda^+)$ is the $p$-part of $d(Lambda_p^+)$. To compute $d(Lambda^+)$, note
that
$ Lambda^+ = ZZ dot 1 plus.o lr(plus.o_x ZZ u_x), quad "where" u_x = x+x^(-1), $
and where $x$ ranges over $(p^n-1) slash 2$ elements of $G$, one for each
unordered pair $(x,x^(-1))$, $x in G - lr({1})$. Then clearly
$ u_x u_y = u_(x y) + u_(x y^(-1)), quad "where" u_1 = 2. $
Let $T^+$ be the trace form on $A^+$; then
$T^+(1) = (p^n+1) slash 2 = dim_QQ A^+$. An easy calculation, left to the
reader, shows that $T^+(u_x) = 1$ for $x in G - lr({1})$. Therefore we obtain
for $x,y in G - lr({1})$:
$
  T^+(u_x u_y) = T^+(u_(x y)) + T^+(u_(x y^(-1)))
  = cases(
    2 & "if" (x,x^(-1)) != (y,y^(-1)),
    p^n+2 & "if" (x,x^(-1)) = (y,y^(-1)).
  )
$
Consequently we have
$
  d(Lambda^+) = mat(
    delim: "|",
    (p^n+1)/2, 1, 1, dots, 1;
    1, p^n+2, 2, dots, 2;
    1, 2, p^n+2, dots, 2;
    dots.v, dots.v, dots.v, , dots.v;
    1, 2, 2, dots, p^n+2;
  ).
$
Subtracting twice the first row from the other rows, we find readily that
$ d(Lambda^+) = p^(n(p^n+1)/2). $
Combining all of the above formulas, we obtain
$ k = p^z, quad "where" z = n(p^n-1)/4 - sum_(s >= 1) w_s f(s)/2. $
We are ready to compute the integer $l$ occurring in
@eq:minus-kernel-group-principal-unit-orders. The group $Gamma^dot inter (1+N)$
decomposes into a direct product
$ (1) times product_(i=1)^m lr({alpha in R_i^dot: alpha equiv 1 (mod P_i)}), $
#source(297)
using the notation of @eq:abelian-p-group-cyclotomic-maximal-order and
@eq:abelian-p-group-completed-order-radical. (Note that $-1 in.not 1+N$.) Next,
since $(Gamma^dot inter (1+N)) slash (Lambda^dot inter (1+N))$ is a $p$-group,
Exercise @exc:involution-plus-minus-decomposition tells us that its minus part
is
$ (Gamma^dot inter (1+N))^- slash (Lambda^dot inter (1+N))^-, $
and we now calculate these minus parts. For this purpose, we need: #lemma(
  name: [Kummer's Lemma],
)[
  Let $p$ be any prime, $p >= 2$, and let $omega$ be a primitive $p^s$-th root
  of $1$, where $s >= 1$. (Assume $s >= 2$ if $p = 2$). Let
  $ K = QQ(omega), quad R = ZZ[omega], quad R_0 = ZZ[omega + overline(omega)], $
  where bars denote complex conjugation.

  #enum(
    numbering: "(i)",
    [If $p$ is odd, then
      $ R^dot = chevron.l omega chevron.r times R_0^dot, $
      that is, every unit of $R$ is uniquely expressible as a power of $omega$
      times a real unit.],
    [If $p = 2$, then $R^dot = chevron.l omega chevron.r R_0^dot$, and
      $chevron.l omega chevron.r inter R_0^dot = lr({plus.minus 1})$.],
  )
] <lem:kummer-cyclotomic-unit-real-decomposition>
#idx("Kummer's Lemma", target: [@lem:kummer-cyclotomic-unit-real-decomposition])
#proof[
  (Kervaire–Murthy @bib:Kervaire1977). It suffices to prove for $p >= 2$ that
  $R^dot = chevron.l omega chevron.r R_0^dot$. Let $frak(G)$ denote the Galois
  group $op("Gal")(K slash QQ)$, and view complex conjugation on $K$ as an
  element of $frak(G)$. Given $u in R^dot$, let $v = overline(u) slash u$, so
  $v in R^dot$. Then for all $sigma in frak(G)$,
  $
    abs(sigma(v)) = abs(sigma overline(u) slash sigma u)
    = abs(overline(sigma u) slash sigma u) = 1,
  $
  using the fact that $frak(G)$ is abelian. For fixed $m in ZZ$, it follows that
  $abs(sigma(v^m)) = 1$ for all $sigma in frak(G)$. Therefore the coefficients
  of $op("min. pol.")_QQ lr((v^m))$ are rational integers, bounded independently
  of $m$. Consequently there are only finitely many distinct elements in the set
  $lr({v,v^2,dots})$, so $v$ is a root of $1$. Therefore
  $ overline(u) slash u = plus.minus omega^t quad "for some" t in ZZ. $
  If $overline(u) slash u = omega^t$, where $t = 2r$ is even, then
  $u omega^r in R_0^dot$ and
  $u = omega^(-r) dot u omega^r in chevron.l omega chevron.r R_0^dot$, as
  desired. The rest of the argument is aimed at proving that
  $overline(u) slash u$ must equal $omega^t$ for some even integer $t$.

  _Case 1._ $p$ odd. Since $t$ is determined $mod p^s$, we may assume $t$ even.
  We claim that the equation $overline(u) slash u = -omega^t$ cannot occur.
  Indeed, since $overline(u) equiv u mod (1-omega) R$, the equation would imply
  that $1 equiv -1 mod (1-omega) R$, a contradiction.

  _Case 2._ $p = 2$, $s >= 2$. Since $-1$ is a power of $omega$, we may write
  $overline(u) slash u = omega^t$ for some $t in ZZ$, and we need only show $t$
  even. Let $N$ denote the norm map from $K$ to $QQ(i)$, where $i^2 = -1$. Then
  $N(omega) = plus.minus i$, and since $N u$ is a unit in $ZZ[i]$, we must have
  $N u = plus.minus 1$ or $plus.minus i$. From $overline(u) = omega^t u$ we
  obtain
  #source(298)
  $ overline(N u) = N overline(u) = (N omega)^t N u = (plus.minus i)^t N u. $
  This implies that $t$ is even, and completes the proof of Kummer's Lemma.
]

We now return to our calculations of $(Gamma^dot inter (1+N))^-$ and
$(Lambda^dot inter (1+N))^-$, where $p$ is an odd prime. The involution $tau$
acts as complex conjugation on $R$ and acts trivially on
$R_0 = ZZ[omega + overline(omega)]$. From Kummer's Lemma we deduce that
$
  (R^dot)^+ = R_0^dot, quad "and" quad
  (R^dot)^- = lr({plus.minus 1}) times chevron.l omega chevron.r.
$
Therefore we obtain
$ (Gamma^dot inter (1+N))^- = product_(i=1)^m chevron.l omega_i chevron.r. $
Since $QQ(root(p^s, 1))$ occurs $w_s$ times as a simple summand of $A$, we thus
have
$
  abs((Gamma^dot inter (1+N))^-) = p^(z'), quad "where"
  z' = sum_(s >= 1) s w_s.
$
On the other hand, $(Lambda^dot inter (1+N))^-$ is a subgroup of
$(Gamma^dot inter (1+N))^-$, hence is finite. But the only units of $Lambda$ of
finite order are $lr({plus.minus g: g in G})$, by Higman's Theorem (see page
164). Further, $-g in.not 1+N$ and $g in 1+N$, for $g in G$. Therefore
$ abs((Lambda^dot inter (1+N))^-) = abs(G) = p^n, $
and so we obtain $l = p^(z'-n)$. Combining all of our results, we have now
established: #theorem(title: [Fröhlich @bib:Frohlich1972])[
  Let $G$ be an abelian $p$-group of order $p^n$, where $p$ is an odd prime. For
  $s >= 1$ let $w_s$ be the number of cyclic subgroups of $G$ of order $p^s$.
  Then $abs(D^-(ZZ G)) = p^r$, where
  $ 4r = n(p^n+3) - sum_(s >= 1) w_s (s p^s - (s+1) p^(s-1) + 1 + 4s). $
] <th:frohlich-abelian-p-group-minus-kernel-order>

As our first consequence, we obtain: #corollary(title: [Kervaire–Murthy
  @bib:Kervaire1977])[
  Let $G$ be a cyclic group of order $p^n$. Then $abs(D^-(ZZ G)) = p^r$, where
  $ r = 1/2 lr({(p^n-1)/(p-1) - n^2}). $
] <cor:cyclic-p-group-minus-kernel-order>
Second, we obtain:
#source(299)
#corollary[
  Let $G$ be an elementary abelian $p$-group of order $p^n$. Then
  $abs(D^-(ZZ G)) = p^r$, where
  $ 4r = 3n + lr({(n-1) p^(n+1) - (n+3) p^n + p + 3}) slash (p-1). $
] <cor:elementary-abelian-minus-kernel-order>
These formulas have been generalized to arbitrary $p$-groups by Oliver. We state
without proof: #theorem(title: [Oliver @bib:Oliver1983c])[
  Let $G$ be a $p$-group, where $p$ is odd. Let $C$ range over a full set of
  nonconjugate cyclic subgroups of $G$, with $1 < C <= G$. For each $C$, let
  $
    lr(|N_G lr((C)): C|) = p^(a(C)), quad
    abs(C) dot abs(Z_G lr((C))) slash abs(N_G lr((C))) = p^(b(C)),
  $
  where $Z_G lr((C))$ is the centralizer of $C$ in $G$, and $N_G lr((C))$ the
  normalizer. Then $abs(D^-(ZZ G)) = p^r$, where
  $
    r = log_p lr(|G: [G,G]|) + 1/4 sum_C
    lr({(a(C)-1) phi(p^(b(C))) + p^(b(C)) - 4 b(C) - 1}).
  $
] <th:oliver-p-group-minus-kernel-order>
#idx("Oliver's Theorem", target: [@th:oliver-p-group-minus-kernel-order])

=== Cyclic $p$-Groups <ss:cyclic-p-group-class-groups>

We shall discuss here the calculation of the locally free class group
$op("Cl") ZZ G$ of a cyclic $p$-group $G$, where $p$ is prime. The main results
are due to Kervaire–Murthy @bib:Kervaire1977 and Galovich @bib:Galovich1974,
with later refinements by Ullom @bib:Ullom1977, @bib:Ullom1978, and Oliver
@bib:Oliver1983c. The Kervaire–Murthy article circulated in preprint form in the
late 1960s, though it was published much later.

As usual, there is an exact sequence of finite abelian groups
$ 0 arrow D(ZZ G) arrow op("Cl") ZZ G arrow op("Cl") Lambda' arrow 0, $
<eq:cyclic-p-group-class-kernel-sequence>
where $Lambda'$ is the unique maximal $ZZ$-order in $QQ G$. Then $Lambda'$ is a
direct sum $product.co R_i$ of rings of cyclotomic integers, and
$op("Cl") Lambda' tilde.equiv product op("Cl") R_i$. These class groups
$op("Cl") R_i$ have been studied intensively in algebraic number theory, and we
shall not consider them further in this subsection. Most of the research on
$op("Cl") ZZ G$ has been devoted to the calculation of the kernel group
$D(ZZ G)$.

By Rim's Theorem @th:rim-cyclic-prime-class-group we have $D(ZZ G) = 0$ for
$abs(G) = p$, so the first case to be handled here is that where $G$ is cyclic
of order $p^2$. For $p = 2$ it is easily seen that $D(ZZ G) = 0$ (see Exercise
@exc:klein-four-cyclic-four-kernel-groups). For odd $p$, the determination of
$D(ZZ G)$ leads to delicate problems concerning units in cyclotomic fields, and
is surprisingly difficult. As we shall see below in
@th:cyclic-prime-square-regular-irregular-kernel, the formula for $abs(D(ZZ G))$
depends on whether $p$ is a regular odd prime or not.

In §@ss:class-kernel-group-involution we have already obtained a lower bound for
the order of $D(ZZ G)$, when $G$ is a cyclic group of order $p^n$ with $p$ odd.
There is a canonical involution $tau$ acting on $ZZ G$, given by
$tau(x) = x^(-1)$ for $x in G$, and extended by linearity.
#source(300)
This involution $tau$ acts on $D(ZZ G)$, and we define
$
  D^+(ZZ G) = lr({zeta in D(ZZ G): tau(zeta) = zeta}), quad
  D^-(ZZ G) = lr({zeta in D(ZZ G): tau(zeta) = -zeta}).
$
Since $D(ZZ G)$ has odd order, we have (Exercise
@exc:involution-plus-minus-decomposition)
$ D(ZZ G) = D^+(ZZ G) plus.o D^-(ZZ G). $
We have already calculated $abs(D^-)$ in @cor:cyclic-p-group-minus-kernel-order,
where we found that if $G$ is cyclic of order $p^n$, with $p$ odd, then
$ abs(D^-(ZZ G)) = p^r, quad "with" r = 1/2 lr({(p^n-1)/(p-1) - n^2}). $
In particular,
$
  abs(D^-(ZZ G)) = p^((p-3)/2) quad
  "for" G "cyclic of order" p^2, "with" p "odd".
$
Before stating one of the main results, let us recall the definition of a
regular prime. By definition, an odd prime $p$ is _regular_ if $p$ does not
divide the ideal class number $h_R$, where $R = ZZ[omega]$, with $omega$ a
primitive $p$-th root of $1$. As general reference for results about regular and
irregular primes, see Borevich–Shafarevich @bib:Borevich1966. To test a prime
for regularity, one considers the Bernoulli numbers#footnote[
  We now follow the standard notation for Bernoulli numbers, rather than that
  used in Volume I (page 741; see the regularity discussion in
  §@i:ss:cyclic-p-squared-lattices).
]
#idx("Regular prime")
$ B_2,B_4,dots,B_(2 p^*), quad "where" p^* = (p-3)/2. $
<eq:regular-prime-bernoulli-numbers>
The first few of these are
$
  B_2 = 1/6, quad B_4 = -1/30, quad B_6 = 1/42, quad B_8 = -1/30, \
  B_10 = 5/66, quad B_12 = -691/2730.
$
Then $p$ is regular if and only if $p$ does not divide the numerator of the
$lr({B_i})$ listed in @eq:regular-prime-bernoulli-numbers. The first three
irregular primes are 37, 59 and 67. Of the first 550 primes, 218 are irregular
and 332 are regular, counting $2$ as regular for this count.

We shall now prove the following result, due independently to Kervaire–Murthy
@bib:Kervaire1977 and Galovich @bib:Galovich1974: #theorem[
  Let $G$ be cyclic of order $p^2$, where $p$ is a regular odd prime. Then
  $ abs(D(ZZ G)) = p^((p-3)/2). $
] <th:regular-prime-square-cyclic-kernel-order>
#idx(
  "Galovich's Theorem",
  target: [@th:regular-prime-square-cyclic-kernel-order],
)
#idx(
  "Kervaire-Murthy Theorem",
  target: [@th:regular-prime-square-cyclic-kernel-order],
)
#proof[
  _Step 1._ Let $G = chevron.l x: x^(p^2) = 1 chevron.r$ and $R = ZZ[omega]$,
  where $omega$ is a primitive $p$-th root of $1$. We shall follow Galovich's
  approach, and begin by proving that whether or not $p$ is regular, there is an
  exact sequence
  #source(301)
  $
    R^dot arrow^j overline(R)^dot arrow D(ZZ G) arrow 0,
    quad "where" overline(R) = R slash p R.
  $ <eq:cyclic-prime-square-kernel-unit-cokernel>
  Let $Phi_(p^i) lr((x))$ be the cyclotomic polynomial whose zeros are the
  primitive $p^i$-th roots of $1$. There is a fiber product
  #cyclic-prime-square-augmentation-fiber-square
  (see @i:eq:ideal-fibre-product). From
  @cor:commutative-order-unit-class-group-sequence and
  @th:kernel-group-mayer-vietoris, we obtain an exact sequence
  $
    Gamma^dot times ZZ^dot arrow (ZZ slash p^2 ZZ)^dot arrow
    D(ZZ G) arrow D(Gamma) arrow 0.
  $
  However, $Gamma^dot$ maps onto $(ZZ slash p^2 ZZ)^dot$, since if $m in ZZ$ is
  prime to $p$, then the element $(1-x^m) slash (1-x)$ is a unit in $Gamma$, and
  has image $m (mod p^2)$ in $ZZ slash p^2 ZZ$. Thus we obtain
  $D(ZZ G) tilde.equiv D(Gamma)$.

  Let $R_2 = ZZ[omega_2]$, where $omega_2$ is a primitive $p^2$-th root of $1$.
  Then $Gamma$ is given by a fiber product
  #cyclic-prime-square-cyclotomic-fiber-square
  where $overline(R) = R slash p R$. As above, we obtain an exact sequence
  $ R_2^dot times R^dot arrow overline(R)^dot arrow D(Gamma) arrow 0. $
  But $R_2^dot$ and $R^dot$ have the same image in $overline(R)^dot$ by Exercise
  @i:exc:cyclotomic-unit-reduction-norm, which establishes the exactness of the
  sequence @eq:cyclic-prime-square-kernel-unit-cokernel.

  _Step 2._ We must now evaluate $op("cok") j$, where
  $j: R^dot arrow overline(R)^dot$. Let $S = ZZ[omega + overline(omega)]$, where
  $overline(omega)$ is the complex conjugate of $omega$. By Kummer's Lemma
  @lem:kummer-cyclotomic-unit-real-decomposition, we have
  $ R^dot = chevron.l omega chevron.r times S^dot, $
  which will help us compute the image of $R^dot$ in $overline(R)^dot$. We set
  $ pi = 1-omega, quad pi_0 = (1-omega)(1-overline(omega)), $
  so by Exercise @exc:cyclotomic-real-discriminant-ratio we obtain
  $ p R = pi^(p-1) R, quad p S = pi_0^((p-1)/2) S. $
  #source(302)
  Then $overline(R) = R slash p R tilde.equiv
  overline(ZZ)[pi] slash (pi^(p-1))$, where $overline(ZZ) = ZZ slash p ZZ$. This
  gives
  $
    overline(R)^dot = overline(ZZ)^dot times chevron.l 1+pi chevron.r times
    chevron.l 1+pi^2 chevron.r times dots times chevron.l 1+pi^(p-2) chevron.r,
  $
  a direct product of a cyclic group $overline(ZZ)^dot$ of order $p-1$, and
  $p-2$ cyclic groups $chevron.l 1+pi^i chevron.r$, each of order $p$. Likewise,
  setting $overline(S) = S slash p S$, we have
  $
    overline(S)^dot tilde.equiv overline(ZZ)^dot times
    chevron.l 1+pi_0 chevron.r times chevron.l 1+pi_0^2 chevron.r times dots
    times chevron.l 1+pi_0^(p^*) chevron.r,
  $
  where $p^* = (p-3) slash 2$. Since $p R inter S = p S$, the map
  $overline(S) arrow overline(R)$ is injective, whence so is the map
  $overline(S)^dot arrow overline(R)^dot$. Further, for $1 <= i <= p^*$,
  $
    1+pi_0^i = 1+(1-omega)^i (1-overline(omega))^i
    equiv 1+pi^(2i) (-1)^i (mod pi^(2i+1)).
  $
  It follows from the above remarks that there is an exact sequence
  $
    1 arrow overline(S)^dot arrow overline(R)^dot arrow
    overline(ZZ)^(((p-1)/2)) arrow 0,
  $
  where $overline(ZZ)^(((p-1)/2))$ denotes the direct sum of $(p-1) slash 2$
  cyclic groups of order $p$.

  Now consider the map $j: R^dot arrow overline(R)^dot$, whose cokernel is a
  direct sum of copies of $overline(ZZ)$. Now $j(omega) = 1-pi$, which generates
  the subgroup $chevron.l 1-pi chevron.r$ of $overline(R)^dot$. Furthermore, we
  have $R^dot = chevron.l omega chevron.r times S^dot$, and the map
  $S^dot arrow overline(R)^dot$ factors through $overline(S)^dot$. It follows at
  once that $op("cok") j$ is a direct sum of at least $(p-3) slash 2$ copies of
  $overline(ZZ)$.

  _Step 3._ It remains for us to show that when $p$ is a regular prime, then
  $op("cok") j$ is at most $p^*$ copies of $overline(ZZ)$. The crucial tool is
  an old result of Hilbert @bib:Hilbert1970, sec. 138, p. 281:
]
#proposition(numbered: false)[
  Keep the above notation. There exist units $u_i in S^dot$, $1 <= i <= p^*$,
  such that
  $
                u_1 = 1+a_1 pi^2 & (mod pi^3), \
                u_2 = 1+a_2 pi^4 & (mod pi^5), \
                          dots.c & \
    u_(p^*) = 1+a_(p^*) pi^(p-3) & (mod pi^(p-2)),
  $
  where each $a_i in ZZ$, and where $p divides a_i$ if and only if $p$ divides
  the numerator of the $2i$-th Bernoulli number $B_(2i)$.
] <prop:hilbert-real-cyclotomic-unit-congruences>
#proof(head: none)[
  Taking this for granted, we now finish the proof of the theorem. Assume $p$ is
  regular, so each $a_i$ above is prime to $p$, where $1 <= i <= p^*$. We are
  trying to find an upper bound on the size of $op("cok") j$, where
  $j: R^dot arrow overline(R)^dot$. The proof of
  @th:rim-cyclic-prime-class-group shows that $im j$ contains the factor
  $overline(ZZ)^dot$ of $overline(R)$. Furthermore,
  $im j supset.eq chevron.l 1-pi chevron.r$ since $j(omega) = 1-pi$. But $im j$
  also contains the product
  $chevron.l u_1 chevron.r times chevron.l u_2 chevron.r times dots times
  chevron.l u_(p^*) chevron.r$, where the $lr({u_i})$ are as above. It follows
  that $op("cok") j$ is a direct sum of at most $(p-3) slash 2$ copies of
  $overline(ZZ)$. Combining this fact with the results of the previous steps, we
  conclude that $op("cok") j$ is the direct sum of exactly $(p-3) slash 2$
  copies of $overline(ZZ)$, and the theorem is proved.
]

#source(303)
The above theorem can be generalized to the case of certain (possibly all)
irregular primes. An odd prime $p$ is called _properly irregular_ if
$
  p divides h_R "but" p divides.not h_S, quad "where"
  R = ZZ[omega], quad S = ZZ[omega + overline(omega)],
$
with $omega$ a primitive $p$-th root of $1$. In all cases known to this date, a
prime is either regular or properly irregular.
#idx("Properly irregular prime")

Let us denote by $delta(p)$ the number of Bernoulli numbers in
@eq:regular-prime-bernoulli-numbers whose numerators are divisible by $p$. As
remarked earlier,
$ delta(p) = 0 quad "if and only if" p "is a regular prime". $
If $delta(p) > 0$, then $delta(p)$ of the leading coefficients $a_i$ in
Hilbert's Proposition above are divisible by $p$. For these indices, the
displayed congruences do not give nonzero leading terms in the assigned degrees,
so the same upper bound no longer follows. We might therefore suspect that
@th:regular-prime-square-cyclic-kernel-order no longer holds in this case. In
fact, the following generalization was proved independently by Kervaire–Murthy
@bib:Kervaire1977 and Galovich @bib:Galovich1974: #theorem[
  Let $G$ be cyclic of order $p^2$, where $p$ is an odd prime which is either
  regular or properly irregular. Let $delta(p)$ be the number of Bernoulli
  numbers $lr({B_(2i): 1 <= i <= (p-3)/2})$ with numerators divisible by $p$.
  Then
  $ D(ZZ G) tilde.equiv D^-(ZZ G) plus.o D^+(ZZ G), $
  and
  $
    D^-(ZZ G) tilde.equiv overline(ZZ)^(((p-3)/2)), quad
    D^+(ZZ G) tilde.equiv overline(ZZ)^(delta(p)),
  $
  where $overline(ZZ) = ZZ slash p ZZ$.
] <th:cyclic-prime-square-regular-irregular-kernel>
#idx(
  "Galovich's Theorem",
  target: [@th:cyclic-prime-square-regular-irregular-kernel],
)
#idx(
  "Kervaire-Murthy Theorem",
  target: [@th:cyclic-prime-square-regular-irregular-kernel],
)
#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [For another proof, see Ullom @bib:Ullom1977, @bib:Ullom1978.],
    [As predicted by @th:ullom-p-group-kernel-exponent, $D(ZZ G)$ is a group of
      exponent dividing $p$.],
    [Ullom @bib:Ullom1977 showed that for $p$ properly irregular and $G$ cyclic
      of order $p^n$, $n >= 2$, the sequence
      @eq:cyclic-p-group-class-kernel-sequence is _not_ split.],
  )
] <rem:prime-square-cyclic-kernel-refinements>

We turn next to the case of cyclic groups of order $p^n$, where $p >= 2$ and
$n >= 2$. Let
$
  G_n = chevron.l x: x^(p^n) = 1 chevron.r, quad
  G_(n-1) = chevron.l x: x^(p^(n-1)) = 1 chevron.r,
$
and view $G_(n-1)$ as a factor group of $G_n$. We calculate $D(ZZ G_n)$ by
relating it to $D(ZZ G_(n-1))$ via a Mayer–Vietoris sequence. For each $n$, let
us set
$
  R_n = ZZ[omega_n], quad K_n = QQ(omega_n), quad
  overline(R)_n = R_n slash (1-omega_n)^(p^(n-1)) R_n,
$ <eq:cyclic-p-power-cyclotomic-quotients>
#source(304)
where $omega_n$ is a primitive $p^n$-th root of $1$, and where
$omega_(n-1) = omega_n^p$. Let
$Phi_(p^n) lr((x)) = op("min. pol.")_QQ lr((omega_n))$, the $p^n$-th cyclotomic
polynomial. From the formula
$ x^(p^n)-1 = Phi_(p^n) lr((x)) dot (x^(p^(n-1))-1), $
we obtain a fiber product diagram
#cyclic-p-power-fiber-square
where $overline(ZZ) = ZZ slash p ZZ$. From
@cor:commutative-order-unit-class-group-sequence and
@th:kernel-group-mayer-vietoris, there is an exact sequence
$
  1 arrow (ZZ G_n)^dot arrow R_n^dot times (ZZ G_(n-1))^dot arrow^j
  overline(R)_n^dot arrow D(ZZ G_n) arrow D(ZZ G_(n-1)) arrow 0.
$
The problem thus reduces to calculating $op("cok") j$. Let us set#footnote[
  Kervaire–Murthy and Ullom choose $G$ cyclic of order $p^(n+1)$. Our $V_(n+1)$
  is their $V_n$.
]
$
  V_n = op("cok") j = overline(R)_n^dot slash
  "image of" (R_n^dot times (ZZ G_(n-1))^dot).
$ <eq:cyclic-p-power-kernel-transition-cokernel>
Suppose first that $p$ is odd, and let $tau$ be the canonical involution on
$ZZ G_n$, acting also on $D(ZZ G_n)$, $D(ZZ G_(n-1))$, and $V_n$. There is then
an exact sequence of “minus parts” relative to $tau$:
$ 0 arrow V_n^- arrow D^-(ZZ G_n) arrow D^-(ZZ G_(n-1)) arrow 0, $
and @cor:cyclic-p-group-minus-kernel-order can be used to calculate the orders
of those terms. The difficulty lies in determining $V_n^+$. We quote without
proof the following result of Kervaire–Murthy, which depends on Iwasawa's work
on cyclotomic fields: #theorem[
  Keep the above notation, and let $p$ be an odd prime which is either regular
  or properly irregular. Then there is a canonical injection
  $
    "character group of" V_n^+ arrow
    p "-primary component of" (op("Cl") R_(n-1))^-.
  $
] <th:cyclic-kernel-plus-character-class-group-injection>
In particular, if the prime $p$ is regular, then $abs(op("Cl") R_(n-1))$ is
prime to $p$ for all $n >= 2$, and therefore $V_n^+ = 1$ whenever $p$ is
regular. This yields the important consequence, due to Kervaire–Murthy
@bib:Kervaire1977 and Galovich @bib:Galovich1974: #corollary[
  For $p$ a regular odd prime and $G$ cyclic of order $p^n$, $n >= 1$, we have
  $D^+(ZZ G) = 0$ and
  $
    abs(D(ZZ G)) = abs(D^-(ZZ G)) = p^r, quad "where"
    r = 1/2 lr(( (p^n-1)/(p-1) - n^2 )).
  $
] <cor:regular-cyclic-p-group-kernel-order>
#idx(
  "Kervaire-Murthy Theorem",
  target: [@cor:regular-cyclic-p-group-kernel-order],
)
Kervaire–Murthy also settle the case $p = 2$:
#source(305)
#theorem[
  Let $G$ be cyclic of order $2^n$, $n >= 1$. Then
  $ abs(D(ZZ G)) = 2^r, quad "where" r = 2^(n-1) - 1/2 n(n-1) - 1. $
] <th:cyclic-two-group-kernel-order>

We turn next to the refinements of these results, due to Ullom @bib:Ullom1977,
@bib:Ullom1978 and Oliver @bib:Oliver1983c. Let $p$ be an odd prime, and let $G$
be cyclic of order $p^n$, $n >= 2$. Then
$
  op("Aut") G tilde.equiv op("Gal")(K_n slash QQ) tilde.equiv
  "cyclic group of order" p^(n-1)(p-1).
$
Let $Delta$ be the unique subgroup of $op("Aut") G$ of order $p-1$, and identify
$Delta$ with $op("Gal")(K_1 slash QQ)$. Then $Delta$ acts on $ZZ G$ and
$Lambda'$, inducing an action of $Delta$ on the groups $D(ZZ G)$,
$op("Cl") ZZ G$, and $op("Cl") Lambda'$. Let $hat(ZZ)$ denote the $p$-adic
completion of $ZZ$. Since $D(ZZ G)$ is a finite $p$-group, we may view it as a
$hat(ZZ) Delta$-module. Now $hat(ZZ)$ contains a primitive $(p-1)$-st root of
$1$, say $theta$ (see Volume I, bottom of page 748), and there is a
decomposition
$ hat(ZZ) Delta tilde.equiv product.co_(i=0)^(p-2) hat(ZZ) e_i, $
where the $lr({e_i})$ are primitive idempotents in $hat(ZZ) Delta$, and where a
generator $delta$ of $Delta$ acts as $theta^i$ on $e_i$. Each
$hat(ZZ) Delta$-module $M$ then decomposes into a direct sum of eigenspaces:
$
  M = plus.o_(i=0)^(p-2) e_i M, quad "with"
  e_i M = lr({m in M: delta m = theta^i m}), quad 0 <= i <= p-2.
$
Let $tau$ be the canonical involution of $ZZ G$, which acts on $D(ZZ G)$. It is
easily seen that
$
  D^+(ZZ G) = plus.o_(i "even") e_i D(ZZ G), quad
  D^-(ZZ G) = plus.o_(i "odd") e_i D(ZZ G),
$
and there are corresponding decompositions of the group $V_n$ defined in
@eq:cyclic-p-power-kernel-transition-cokernel.

Now consider the automorphism of $G$ given by $g mapsto g^(1+p)$, $g in G$,
which induces an automorphism $gamma$ of $D(ZZ G)$ for which
$gamma^(p^(n-2)) = 1$. Then $D(ZZ G)$ is a $hat(ZZ)[gamma]$-module, on which
$gamma-1$ acts nilpotently. As in Iwasawa theory, we introduce the power series
ring $Lambda = hat(ZZ)[[T]]$ in an indeterminate $T$. Then $D(ZZ G)$ can be made
into a left $Lambda$-module by letting $T$ act as $gamma-1$. The map
$D(ZZ G_n) arrow D(ZZ G_(n-1))$ is then a $Lambda$-homomorphism, so $V_n$ and
its eigenspaces $e_i V_n$ are also $Lambda$-modules. Ullom @bib:Ullom1977 proved
that each $e_i V_n$ is a cyclic left $Lambda$-module, whose generator can be
given explicitly. From this he showed that for $n >= 2$,
$
  op("ann")_Lambda e_i V_n = p op("ann")_Lambda e_i V_(n-1)
  + T^(p^(n-2)-delta_(1i)) Lambda, quad i "odd", 1 <= i <= p-2,
$
where $delta_(1i) = "Kronecker delta"$. (An analogous formula holds for
$p = 2$.) From the above, it follows that
#source(306)
$
  e_i V_n tilde.equiv product_(r=0)^(n-2)
  (ZZ slash p^(n-1-r) ZZ)^((phi(p^r))), quad i "odd", 3 <= i <= p-2,
$
while for $e_1 V_n$ the term with $r = 0$ must be omitted. This readily yields
the known formula for $abs(D^-(ZZ G_n))$.

On the other hand, $V_n^+ = plus.o_(i "even") e_i V_n$. These even eigenspaces
$lr({e_i V_n})$ were studied by Ullom @bib:Ullom1978, who showed that
$e_0 V_n = 0$. Further, for irregular $p$ satisfying some mild hypothesis (see
below) known to hold for $p < 125,000$,
$e_i V_n tilde.equiv e_i lr((P_n slash Q_n))$, where $P_n slash Q_n$ is a ray
class group. Specifically,
$
  P_n = "group of principal" R_n "-ideals of" K_n "prime to" p, \
  Q_n = "subgroup of all" lr(
    {R_n a: a in K_n,
      v_n lr((a-1)) >= v_n lr((1-omega_1))}
  ),
$
where $v_n$ is the $p$-adic exponential valuation of $K_n$. (The isomorphism
$e_i V_n tilde.equiv e_i lr((P_n slash Q_n))$ for odd $i$ was pointed out in
Ullom @bib:Ullom1977, and follows from Reiner–Ullom @bib:Reiner1974b.) For even
$i$, Ullom @bib:Ullom1978 computed the annihilator of the $Lambda$-module
$e_i lr((P_n slash Q_n))$, which leads to the following result: #theorem(
  title: [Ullom @bib:Ullom1978],
)[
  Let $G_n$ be cyclic of order $p^n$, $n >= 2$, where $p$ is an odd prime which
  is either regular or properly irregular. If $n >= 3$, assume that for each
  $i$, the Iwasawa invariant $lambda_i$ is $0$ or $1$. Let $delta(p)$ be as in
  @th:cyclic-prime-square-regular-irregular-kernel. Then

  #enum(
    numbering: "(i)",
    [$e_0 V_n = e_0 D(ZZ G_n) = 0$.],
    [For even $i$, $2 <= i <= p-3$,
      $
        e_i V_n = 0 "if" p divides.not B_i, quad "and" quad
        e_i V_n tilde.equiv ZZ slash p^(n-1) ZZ "if" p divides B_i.
      $
      Therefore
      $
        e_i D(ZZ G_n) = 0 "if" p divides.not B_i, quad "and" quad
        e_i D(ZZ G_n) tilde.equiv product_(j=1)^(n-1) ZZ slash p^j ZZ
        "if" p divides B_i.
      $
    ],
    [$plus.o_(i "even") e_i V_n$ is isomorphic to the direct sum of $delta(p)$
      copies of $ZZ slash p^(n-1) ZZ$. Therefore
      $
        D^+(ZZ G) tilde.equiv "direct sum of" delta(p) "copies of"
        product_(j=1)^(n-1) ZZ slash p^j ZZ,
      $
      and
      $ abs(D^+(ZZ G_n)) = p^m, quad "where" m = delta(p) n(n-1)/2. $
    ],
  )
] <th:ullom-cyclic-p-group-kernel-eigenspaces>

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [The above theorem includes Theorems
      @th:cyclic-prime-square-regular-irregular-kernel and
      @cor:regular-cyclic-p-group-kernel-order as special cases. Theorem
      @th:cyclic-two-group-kernel-order is a consequence of the work in Ullom
      @bib:Ullom1977.],
    [#source(307)
      Oliver @bib:Oliver1983c has completely determined the structure of
      $D^-(ZZ G_n)$ as abelian group.],
  )
] <rem:cyclic-p-group-kernel-complete-structure>

=== Twisted Group Rings and Crossed-Product Orders
<ss:crossed-product-order-kernel-groups>

The study of integral group rings often leads to problems involving twisted
group rings; see @i:exm:dihedral-twisted-group-ring and
§§@ss:metacyclic-class-groups, @ss:dihedral-quaternion-class-groups for example.
These are, in turn, special cases of the more general concept of a
crossed-product order, already encountered in Volume I, p. 268,
@i:exm:twisted-group-algebra-clifford-system, as well as in
@i:th:crossed-product-order-heredity. Before stating Wilson's Theorem
@th:wilson-crossed-product-order-trivial-kernel, which is the main result of
this subsection, we recall some definitions and fix the notation.

We assume throughout that $R,S$ are Dedekind domains with quotient fields $K,L$,
respectively, where $L$ is a finite Galois extension of $K$ with Galois group
$G = op("Gal")(L slash K)$, and where $S$ is the integral closure of $R$ in $L$.
The _twisted group algebra_ $L compose G$, and the _twisted group ring_
$S compose G$, are defined by
$
  L compose G = plus.o_(sigma in G) L u_sigma, quad
  S compose G = plus.o_(sigma in G) S u_sigma,
$
where $u_sigma a = sigma(a) u_sigma$, $u_sigma u_tau = u_(sigma tau)$ for all
$sigma,tau in G$ and $a in S$. Then $S compose G$ is an $R$-order in the
$K$-algebra $L compose G$, and by @i:exm:galois-twisted-group-algebra
$L compose G tilde.equiv M_n lr((K))$, where $n = dim_K L = abs(G)$.
#idx("Twisted group ring")

Let us generalize this construction by assuming instead that the $S$-basis
elements $lr({u_sigma: sigma in G})$ multiply according to some factor set
$f: G times G arrow S^dot$. The _crossed-product algebra_ $(L compose G)_f$ and
the _crossed-product order_ $(S compose G)_f$ are defined by setting
$
  cases(
    (L compose G)_f = plus.o_(sigma in G) L u_sigma "," quad
    (S compose G)_f = plus.o_(sigma in G) S u_sigma,
    "where" u_sigma a = sigma(a) u_sigma quad "and" quad
    u_sigma u_tau = f(sigma,tau) u_(sigma tau)
    "for all" sigma "," tau in G "," a in L.
  )
$ <eq:crossed-product-algebra-order-definition>
#idx("Crossed product algebra")
#idx(
  "Crossed product order",
  target: [@eq:crossed-product-algebra-order-definition],
)
The condition that $f$ be a factor set is equivalent to the condition that
multiplication of the elements $lr({u_sigma})$ be associative. As pointed out in
@i:exm:crossed-products-twisted-group-algebras(i) (see also @bib:Reiner1975[MO]
§29), $(L compose G)_f$ is a central simple $K$-algebra, often denoted by
$(L slash K,f)$. Up to $K$-isomorphism, this algebra depends only on the class
of $f$ in the cohomology group $H^2(G,L^dot)$. Of course, when $f = 1$ we have
the usual twisted group algebra $L compose G$.

The main result, due to S. M. J. Wilson @bib:Wilson1977b, is as follows:
#theorem[
  Let $Lambda = (S compose G)_f$ be the crossed-product order defined in
  @eq:crossed-product-algebra-order-definition, and assume that $K$ is a global
  field. Then the kernel group $D(Lambda)$ is $0$.
] <th:wilson-crossed-product-order-trivial-kernel>
#idx(
  "Wilson's Theorem",
  target: [@th:wilson-crossed-product-order-trivial-kernel],
)
We remark that if $S$ is tamely ramified over $R$, then $Lambda$ is a hereditary
$R$-order by Williamson's Theorem (see @i:th:crossed-product-order-heredity or
Exercise @exc:tame-crossed-product-order-hereditary). In this case, we already
know that $D(Lambda) = 0$ by @cor:hereditary-order-class-group-maximal-order.

Turning to the general case, the proof proceeds in a number of steps, which we
now list:
#source(308)
#enum(
  numbering: "(i)",
  [Technical results on reduced norms; see
    @lem:crossed-product-matrix-reduced-norm,
    @lem:crossed-product-subgroup-reduced-norm, and Exercise
    @exc:cyclic-crossed-product-binomial-norm.],
  [Reduction of the problem to the local case.],
  [Preliminary result for the tamely ramified case; see
    @prop:crossed-product-tame-norm-quotient-surjection.],
  [The case of wild ramification with cyclic ramification group; see
    @prop:cyclic-wild-crossed-product-unit-norm-surjection.],
  [Reduction to the cyclic case via local class field theory.],
)
We begin with some results on reduced norms; as general references on this
topic, see §@i:ss:reduced-norms and §@ss:reduced-norms, as well as
@bib:Reiner1975[MO] §9.

#lemma[
  Let $A = (L compose G)_f$ as in @eq:crossed-product-algebra-order-definition,
  where $G = lr({sigma_1,dots,sigma_n})$. There is a $K$-algebra monomorphism
  $phi: A arrow M_n lr((L))$, given by
  $
    phi(a) = a^*, quad "where"
    a^* = op("diag")(sigma_1^(-1) a,dots,sigma_n^(-1) a), quad a in L, \
    phi(u_sigma) = U(sigma), quad "where"
    U(sigma) = [(sigma sigma_j)^(-1) f(sigma,sigma_j)
      delta_(sigma_i,sigma sigma_j)]_(1 <= i,j <= n),
  $
  for $sigma in G$. Furthermore, for each $x in A$ we have
  $ op("nr")_(A slash K) x = det phi(x), $
  where $op("nr")_(A slash K)$ is the reduced norm map from $A$ to its center
  $K$.
] <lem:crossed-product-matrix-reduced-norm>
#proof[
  (Compare with Exercises @i:exc:twisted-galois-matrix-representation,
  @i:exc:twisted-galois-reduced-norm) Let
  $bold(w) = (u_(sigma_1),dots,u_(sigma_n))$ be a row vector. It is easily
  verified that for $a in L$, $sigma,tau in G$,
  $ a bold(w) = bold(w) a^*, quad u_sigma bold(w) = bold(w) U(sigma). $
  This yields the formulas
  $
    U(sigma) a^* = (sigma(a))^* U(sigma), quad
    U(sigma) U(tau) = (f(sigma,tau))^* U(sigma tau),
  $
  so after extending $phi$ by linearity, we obtain a $K$-algebra homomorphism
  $phi: A arrow M_n lr((L))$. Further, $ker phi = 0$ since $A$ is simple. It
  follows that the map
  $ 1 times.o phi: L times.o_K A arrow M_n lr((L)) $
  is an $L$-isomorphism. Therefore for $x in A$,
  $
    op("red. char. pol.")_(A slash K) x =
    "char. pol. of the matrix" phi(x).
  $
  This implies the desired formula for $op("nr")_(A slash K) x$.
]

#lemma[
  Let $G = op("Gal")(L slash K)$, and let $H <= G$. Let $L_0$ be the subfield of
  $L$ fixed elementwise by $H$, so $H = op("Gal")(L slash L_0)$. Set
  $ A = (L compose G)_f, quad B = (L compose H)_f, $
  viewing $B$ as $K$-subalgebra of $A$. Then
  #source(309)
  $
    op("nr")_(A slash K) b = N_(L_0 slash K) lr((op("nr")_(B slash L_0) b))
    quad "for" b in B,
  $
  where $N_(L_0 slash K)$ is the usual norm from $L_0$ to $K$.
] <lem:crossed-product-subgroup-reduced-norm>
#proof[
  We observe first that $B$ is a central simple $L_0$-algebra. Now set
  $ abs(G) = n, quad abs(H) = m, quad d = lr(|G: H|) = n slash m = dim_K L_0. $
  Let $b in B$ act by right multiplication on both $A$ and $B$. By
  @i:eq:simple-algebra-characteristic-reduced-power,
  $
    f(X) = op("char. pol.")_(B slash L_0) b
    = lr({op("red. char. pol.")_(B slash L_0) b})^m, \
    g(X) = op("char. pol.")_(A slash K) b
    = lr({op("red. char. pol.")_(A slash K) b})^n.
  $
  Since $A tilde.equiv B^((d))$ as right $B$-modules, we obtain
  $
    g(X) = lr({op("char. pol.")_(B slash K) b})^d
    = lr({N_(L_0 slash K) lr((f(X)))})^d,
  $
  the second equality by @bib:Reiner1975[MO] (9.12). Since $n = m d$, we deduce
  that
  $
    op("red. char. pol.")_(A slash K) b
    = N_(L_0 slash K) lr((op("red. char. pol.")_(B slash L_0) b)).
  $
  Comparing constant terms, the formula for $op("nr")_(A slash K) b$ is now
  clear.
]

#corollary[
  There is a commutative diagram
  #crossed-product-k1-norm-square
  where $theta$ is the “change of rings” homomorphism arising from the inclusion
  $B arrow A$.
] <cor:crossed-product-k1-norm-compatibility>

Continuing with the proof of Wilson's Theorem, let $Lambda = (S compose G)_f$
and $A = (L compose G)_f$, as in @eq:crossed-product-algebra-order-definition.
From @i:cor:order-reduced-characteristic-integral we have
$op("nr")_(A slash K) Lambda subset.eq R$, and therefore
$op("nr")_(A slash K) Lambda^dot subset.eq R^dot$ since $op("nr")$ is
multiplicative. Let $P$ range over the maximal ideals of $R$. For each $P$,
$Lambda_P$ is an $R_P$-order in the central simple $K_P$-algebra $A_P$. Using
the formula for $D(Lambda)$ in Theorem @th:kernel-group-unit-idele-formula, we
see that in order to prove $D(Lambda) = 0$, it suffices to show that
$op("nr") Lambda_P^dot = R_P^dot$ for each $P$.

Keep $P$ fixed, and let us write
$ P S = (P_1 dots P_g)^e, $
#source(310)
where the $lr({P_i})$ are the distinct maximal ideals of $S$ containing $P$.
Since $G = op("Gal")(L slash K)$ acts transitively on the $lr({P_i})$, they all
have the same ramification index $e$ in the extension $L slash K$. Let
$
  L_i = P_i "-adic completion of" L, quad
  S_i = P_i "-adic completion of" S, quad "for" 1 <= i <= g,
$
so $S_i$ is the valuation ring of $L_i$. We have
$
  L_P = K_P times.o_K L tilde.equiv product.co_(i=1)^g L_i, quad
  S_P = R_P times.o_R S tilde.equiv product.co_(i=1)^g S_i.
$
The _decomposition group_ of $P_1$ (for the extension $L slash K$) is defined as
$ D = lr({sigma in G: sigma(P_1) = P_1}) $
(see Volume I, page 599, @i:term:decomposition-inertia-groups). In Step 3 of the
proof of @th:wall-abelian-sylow-sk1-trivial, we showed that the direct sum
decomposition of $S_P$ gives rise to an isomorphism of $R_P$-algebras:
$
  Lambda_P tilde.equiv M_g lr((Gamma)), quad "where"
  Gamma = (S_1 compose D)_f = plus.o_(sigma in D) S_1 u_sigma.
$
#idx("Decomposition group")
Here, $f$ is viewed as a factor set $f: D times D arrow S_1^dot$, via the
homomorphism $S^dot arrow S_1^dot$. It follows that
$K_1 lr((Lambda_P)) tilde.equiv K_1 lr((Gamma))$. Further, $Gamma$ is an order
in a central simple $K_P$-algebra, and
$ op("nr") K_1 lr((Lambda_P)) = op("nr") K_1 lr((Gamma)) = op("nr") Gamma^dot, $
the latter equality holding since $Gamma^dot$ maps onto $K_1 lr((Gamma))$. Thus,
in order to prove that $op("nr") Lambda_P^dot = R_P^dot$, it suffices to show
that $op("nr") Gamma^dot = R_P^dot$. Note that $D = op("Gal")(L_1 slash K_P)$.

_Changing notation for the rest of the proof_, we may assume that $R$ is a
complete d.v.r. with maximal ideal $P$ and finite residue class field
$overline(R) = R slash P$ of characteristic $p$, and that $L slash K$ is a
finite extension of local fields with Galois group $G = op("Gal")(L slash K)$.
Let $Lambda = (S compose G)_f$, $A = (L compose G)_f$ as in
@eq:crossed-product-algebra-order-definition. We must show that in this
situation, $op("nr")_(A slash K) Lambda^dot = R^dot$.

Let us recall some definitions and facts from ramification theory, as described
in any standard reference on algebraic number theory. Let
$G = op("Gal")(L slash K)$, with $K$ local, as above. Let $S$ be the valuation
ring of $L$, $frak(P)$ the maximal ideal of $S$, and let
$overline(S) = S slash frak(P)$ be its residue class field. Define the _inertia
group_ $G_0$ and the _first ramification group_ $G_1$ by the formula
$
  G_i = lr(
    {sigma in G: sigma(x) equiv x mod frak(P)^(i+1)
      "for all" x in S}
  ), quad i = 0,1.
$
#idx("Inertia group")
#idx("First ramification group")
Both $G_0$ and $G_1$ are normal subgroups of $G$. Let $L_i$ be the subfield of
$L$ fixed by $G_i$, and let $S_i$ be the valuation ring of $L_i$, and
$frak(P)_i$ the maximal ideal of $S_i$, for $i = 0,1$. We have a diagram
#source(311)
#local-ramification-field-ring-chart
The following facts are well known:
#enum(
  numbering: "(i)",
  [$L_0 slash K$ is unramified, and
    $
      G slash G_0 tilde.equiv op("Gal")(L_0 slash K)
      tilde.equiv op("Gal")(overline(S) slash overline(R)).
    $],
  [$L slash L_0$ is completely ramified, so
    $overline(S) = overline(S)_1 = overline(S)_0$.],
  [$L_1 slash L_0$ is tamely ramified, and
    $
      G_0 slash G_1 tilde.equiv op("Gal")(L_1 slash L_0)
      = "cyclic group of order" e', quad "where" p divides.not e'.
    $],
  [$L slash L_1$ is wildly ramified, and
    $ G_1 = op("Gal")(L slash L_1) = p "-group". $],
  [Using the Schur–Zassenhaus Theorem, it follows that $G_0$ is a semidirect
    product
    $
      G_0 = G_1 times.r chevron.l phi.alt chevron.r quad
      "for some cyclic group" chevron.l phi.alt chevron.r "of order" e'.
    $
    <eq:inertia-tame-wild-semidirect-product>
  ],
)
#idx("Ramification", "tame")
#idx("Ramification", "wild")
#idx("Ramified")
We shall consider the $R$-order $Lambda = (S compose G)_f$ in the $K$-algebra
$A = (L compose G)_f$, as in @eq:crossed-product-algebra-order-definition. For
convenience of notation, we shall use the notation $op("nr")_(Lambda slash R)$
to denote the restriction to $Lambda$ of the reduced norm
$op("nr")_(A slash K)$. Likewise, for $i = 0,1$, $N_(S_i slash R)$ will mean the
restriction to $S_i$ of the field norm $N_(L_i slash K)$. Keeping this notation,
we prove a preliminary result which essentially involves just tame ramification.

#proposition[
  Consider the crossed-product orders
  $
    Lambda_1 = (S compose G_1)_f subset.eq Lambda_0 = (S compose G_0)_f
    subset.eq Lambda = (S compose G)_f.
  $
  Then the norm $N_(S_1 slash R)$ induces a surjective homomorphism
  $
    N_(S_1 slash R): S_1^dot / (op("nr")_(Lambda_1 slash S_1) Lambda_1^dot)
    arrow R^dot / (op("nr")_(Lambda slash R) Lambda^dot).
  $
] <prop:crossed-product-tame-norm-quotient-surjection>
#source(312)
#proof[
  By Lemma @lem:crossed-product-subgroup-reduced-norm, we have
  $
    N_(S_1 slash R) lr((op("nr")_(Lambda_1 slash S_1) Lambda_1^dot))
    subset.eq op("nr")_(Lambda slash R) Lambda^dot,
  $
  so the above map on quotients is well-defined. Likewise, there is a
  homomorphism
  $
    N_(S_1 slash S_0):
    S_1^dot / (op("nr")_(Lambda_1 slash S_1) Lambda_1^dot) arrow
    S_0^dot / (op("nr")_(Lambda_0 slash S_0) Lambda_0^dot).
  $
  <eq:tame-subextension-unit-norm-quotient-map>
  Now $N_(S_0 slash R) lr((S_0^dot)) = R^dot$ because $S_0 slash R$ is
  unramified. Hence, to establish the proposition, it suffices to prove that the
  map $N_(S_1 slash S_0)$ in @eq:tame-subextension-unit-norm-quotient-map is
  surjective.

  The reduced norm $op("nr")_(Lambda_0 slash S_0)$ maps $frak(P) Lambda_0$ into
  $frak(P)_0$, and induces a map
  $overline(op("nr")): Lambda_0 slash frak(P) Lambda_0 arrow
  S_0 slash frak(P)_0$. We may write
  $
    overline(Lambda)_0 = Lambda_0 slash frak(P) Lambda_0
    = lr({plus.o_(sigma in G_0) S u_sigma}) slash
    lr({plus.o_(sigma in G_0) frak(P) u_sigma})
    = plus.o_(sigma in G_0) overline(S) overline(u)_sigma,
  $
  where $overline(S) = S slash frak(P)$. Then $G_0$ acts trivially on
  $overline(S)$, and the structure of the $overline(S)$-algebra
  $overline(Lambda)_0$ is determined by the multiplication formula
  $
    overline(u)_sigma overline(u)_tau = overline(f(sigma,tau))
    overline(u)_(sigma tau) quad "for" sigma,tau in G_0.
  $
  There is a commutative diagram
  #numbered-block(tame-crossed-product-reduction-norm-square)
  <eq:tame-crossed-product-reduced-norm-reduction>
  which we shall use in a moment.

  Writing $G_0 = G_1 times.r chevron.l phi.alt chevron.r$ as in
  @eq:inertia-tame-wild-semidirect-product, consider the
  $overline(S)$-subalgebra $Phi$ of $overline(Lambda)_0$ given by
  $ Phi = plus.o_(i=0)^(e'-1) overline(S) overline(u)_(phi.alt^i). $
  We may assume the factor set $f$ chosen so that
  $
    u_(phi.alt^i) = (u_phi.alt)^i, quad 0 <= i <= e'-1; quad
    (u_phi.alt)^(e') = beta in S^dot,
  $
  where $phi.alt(beta) = beta$. Consequently we obtain
  $
    Phi tilde.equiv overline(S)[X] slash (X^(e') - overline(beta))
    tilde.equiv product.co_j F_j,
  $
  #source(313)
  with each $F_j$ a finite field extension of $overline(S)$. There is then a
  surjection
  $
    N: Phi^dot arrow overline(S)^dot, quad "where"
    N = product_j N_(F_j slash overline(S)).
  $
  We note next that $overline(Lambda)_0$ is a free $Phi$-module of rank $q$,
  where $q = abs(G_1)$. It is easily verified that
  $ overline(op("nr")) x = (N x)^q quad "for" x in Phi^dot. $
  Since the map $alpha in overline(S)^dot mapsto alpha^q in overline(S)^dot$ is
  a surjection of $overline(S)^dot$ onto itself, and since $N$ is surjective, it
  follows that $overline(op("nr")) overline(Lambda)_0^dot = overline(S)^dot$. We
  may then conclude from @eq:tame-crossed-product-reduced-norm-reduction that
  $
    op("nr")_(Lambda_0 slash S_0) Lambda_0^dot
    equiv S_0^dot mod (1+frak(P)),
  $
  <eq:tame-crossed-product-unit-norm-residue-surjectivity>
  where this congruence (and the later ones as well) are to be read
  multiplicatively. Since $op("nr") Lambda_0^dot$ and $S_0$ lie in $L_0$, and
  $frak(P) inter L_0 = frak(P)_0$, the above congruence holds
  $mod (1+frak(P)_0)$.

  For any $y in frak(P)_0$ we have $N_(S_1 slash S_0) lr((1+y)) = (1+y)^(e')$;
  since $p divides.not e'$, we conclude that
  $N_(S_1 slash S_0) lr((1+frak(P)_0)) = 1+frak(P)_0$. Therefore
  $
    N_(S_1 slash S_0) S_1^dot supset.eq
    N_(S_1 slash S_0) lr((1+frak(P)_1)) supset.eq
    N_(S_1 slash S_0) lr((1+frak(P)_0)) = 1+frak(P)_0.
  $
  This gives
  $
    (N_(S_1 slash S_0) S_1^dot)(op("nr")_(Lambda_0 slash S_0) Lambda_0^dot)
    supset.eq (1+frak(P)_0)(op("nr")_(Lambda_0 slash S_0) Lambda_0^dot)
    = S_0^dot,
  $
  the last by virtue of @eq:tame-crossed-product-unit-norm-residue-surjectivity.
  It follows that the map @eq:tame-subextension-unit-norm-quotient-map is
  surjective, which completes the proof.
]

Our next step involves the wild ramification when $G_1$ is assumed cyclic:
#proposition[
  Keeping the above notation, let $G_1$ be a cyclic group of order $q$. Then
  $ op("nr")_(Lambda_1 slash S_1) Lambda_1^dot = S_1^dot. $
] <prop:cyclic-wild-crossed-product-unit-norm-surjection>
#proof[
  As in @eq:tame-crossed-product-reduced-norm-reduction, there is a commutative
  diagram
  #wild-crossed-product-reduction-norm-square
  Now $q$ is a power of $p$, and viewing $overline(S)^dot$ as subgroup of
  $overline(Lambda)_1^dot$ (which may require a preliminary normalization of the
  factor set $f$), we have $overline(overline(op("nr"))) alpha = alpha^q$ for
  $alpha in overline(S)^dot$. This shows that $overline(overline(op("nr")))$ is
  surjective, and therefore
  #source(314)
  $
    op("nr")_(Lambda_1 slash S_1) Lambda_1^dot
    equiv S_1^dot (mod (1+frak(P)_1))
  $
  (multiplicative congruence!). To complete the proof, we need only show that
  $op("nr") Lambda_1^dot supset.eq 1+frak(P)_1$, where we write $op("nr")$ in
  place of $op("nr")_(Lambda_1 slash S_1)$ for brevity.

  Let $G_1 = chevron.l gamma: gamma^q = 1 chevron.r$, and assume the factor set
  $f$ chosen so that
  $
    u_(gamma^i) = (u_gamma)^i, quad 0 <= i <= q-1; quad
    (u_gamma)^q = c in S^dot,
  $
  where $gamma(c) = c$, that is, $c in S_1^dot$. Let $frak(P) = pi S$,
  $frak(P)_1 = pi_1 S_1$; since $S slash S_1$ is completely ramified, we may
  choose $pi_1 = N_(S slash S_1) pi$. We now define filtrations of $1+frak(P)_1$
  and $Lambda_1^dot$ by setting
  $ W_i = 1+pi_1^i S_1, quad X_i = 1+pi^i Lambda_1, quad i = 1,2,dots. $
  Then
  $
    W_1 = 1+frak(P)_1, quad "and" quad
    X_1 = 1+frak(P)(S compose G_1)_f subset.eq Lambda_1^dot.
  $
  We intend to prove that $op("nr") X_1 supset.eq W_1$, which will establish the
  proposition.

  Given $w in W_1$, we shall construct a sequence of elements
  $x_1,x_2,dots in X_1$ such that for $i >= 1$,
  $
    op("nr") x_i equiv w (mod W_i) quad "and" quad
    x_(i+1) equiv x_i (mod X_i).
  $
  <eq:cyclic-wild-unit-norm-successive-approximations>
  We shall then set $x = lim x_i in X_1$, and clearly $op("nr") x = w$, as
  desired. To find the $lr({x_i})$, we choose $x_1 = 1$. Suppose now that
  $i >= 1$, and that $x_1,dots,x_i$ have already been found satisfying
  @eq:cyclic-wild-unit-norm-successive-approximations. Let $w_i = op("nr") x_i$,
  so $w_i equiv w (mod W_i)$, and thus
  $ w = w_i lr((1+pi_1^i c v)) quad "for some" v in S_1, $
  where $u_gamma^q = c in S_1^dot$ as above. Choose a positive $n in ZZ$ such
  that $n q equiv 1 (mod abs(overline(S)^dot))$, and set
  $y_i = 1+u_gamma pi^i v^n$. By Exercise
  @exc:cyclic-crossed-product-binomial-norm we obtain
  $
    op("nr") y_i = 1-(-1)^q pi_1^i c v^(n q)
    equiv 1+pi_1^i c v (mod W_(i+1)).
  $
  Choosing $x_(i+1) = x_i y_i$, we have
  $ op("nr") x_(i+1) = w_i op("nr") y_i equiv w (mod W_(i+1)), $
  which completes the proof.
]

Combining the two previous propositions, we show: #corollary[
  Let $Lambda = (S compose G)_f$. Then
  $op("nr")_(Lambda slash R) Lambda^dot = R^dot$ if $G_1$ is cyclic.
] <cor:cyclic-wild-ramification-crossed-product-unit-norm>
#source(315)
#proof[
  Let $Lambda_1 = (S compose G_1)_f$; then by
  @lem:crossed-product-subgroup-reduced-norm and
  @prop:cyclic-wild-crossed-product-unit-norm-surjection we have
  $
    op("nr")_(Lambda slash R) Lambda^dot supset.eq
    N_(S_1 slash R) lr((op("nr")_(Lambda_1 slash S_1) Lambda_1^dot))
    = N_(S_1 slash R) S_1^dot.
  $
  On the other hand,
  $
    R^dot = (N_(S_1 slash R) S_1^dot)
    (op("nr")_(Lambda slash R) Lambda^dot)
  $
  by @prop:crossed-product-tame-norm-quotient-surjection. This shows that
  $R^dot subset.eq op("nr")_(Lambda slash R) Lambda^dot$, and therefore
  $R^dot = op("nr")_(Lambda slash R) Lambda^dot$, as desired.
]

In order to reduce the general case to that considered in Corollary
@cor:cyclic-wild-ramification-crossed-product-unit-norm, we use some facts from
local class field theory which are available in most standard treatments of the
subject (see, e.g., Cassels–Fröhlich @bib:Cassels1967, Serre @bib:Serre1962, or
Neukirch @bib:Neukirch1969). #proposition[
  Let $G = op("Gal")(L slash K)$, where $K,L$ are local fields. Then for each
  $a in R^dot$, there exists a cyclic subgroup $C <= G$ such that
  $a in N_(tilde(S) slash R) tilde(S)^dot$, where $tilde(S)$ is the subring of
  $S$ fixed elementwise by $C$.
] <prop:local-unit-norm-cyclic-fixed-subfield>
#proof[
  Consider a tower of local fields $K subset.eq F subset.eq L$, with $L slash K$
  a Galois extension. Set
  $
    G = op("Gal")(L slash K), quad H = op("Gal")(L slash F), quad
    G^"ab" = G slash [G,G], quad H^"ab" = H slash [H,H].
  $
  Then there is a commutative diagram of abelian groups, with exact rows:
  #local-artin-norm-exact-rows
  Here, $alpha$ and $alpha'$ are the Artin homomorphisms, while $i_*$ is induced
  by the inclusion $i: H arrow G$. Since
  $N_(L slash K) L^dot = N_(F slash K) lr((N_(L slash F) L^dot))$, an easy
  diagram-chase shows that for $a in K^dot$,
  $ a in N_(F slash K) F^dot arrow.l.r.double alpha(a) in im i_*. $
  Now let $a in R^dot$, and choose $sigma in G$ so that $alpha(a)$ equals the
  image of $sigma$ in $G^"ab"$. We choose $H = chevron.l sigma chevron.r <= G$
  in the above discussion, and $F$ the subfield of $L$ fixed by $H$, so
  $H = op("Gal")(L slash F)$. It follows that $a = N_(F slash K) lr((b))$ for
  some $b in F^dot$. But then $b$ lies in the valuation ring of $F$, since its
  norm is a unit of $R$. This completes the proof of the proposition.
]

We may now finish the proof of Wilson's Theorem
@th:wilson-crossed-product-order-trivial-kernel. We are still treating the local
case $Lambda = (S compose G)_f$, to which the proof has been reduced, and we
need to show that each $a in R^dot$ lies in
$op("nr")_(Lambda slash R) lr((Lambda^dot))$. Choose $C$ to be a cyclic subgroup
of $G$ as in @prop:local-unit-norm-cyclic-fixed-subfield, so that
$a in N_(tilde(S) slash R) lr((tilde(S)^dot))$, where $tilde(S)$ is the subring
of $S$ fixed by $C$. Let
#source(316)
$ tilde(Lambda) = (S compose C)_f, $
a crossed-product order with center $tilde(S)$. Then
$op("nr")_(tilde(Lambda) slash tilde(S)) lr((tilde(Lambda)^dot)) = tilde(S)^dot$
by Corollary @cor:cyclic-wild-ramification-crossed-product-unit-norm. However,
$
  N_(tilde(S) slash R) lr(
    (op("nr")_(tilde(Lambda) slash tilde(S))
      tilde(Lambda)^dot)
  ) subset.eq op("nr")_(Lambda slash R) Lambda^dot
$
by @lem:crossed-product-subgroup-reduced-norm, so
$a in op("nr")_(Lambda slash R) lr((Lambda^dot))$ as required. This completes
the proof of the theorem.

#exercises-heading

#exercise[
  Prove that $D(ZZ G) = op("Cl") ZZ G = 0$ for $G$ an elementary abelian
  $(2,2)$-group or a cyclic group of order $4$.
] <exc:klein-four-cyclic-four-kernel-groups>
#hint([@exc:klein-four-cyclic-four-kernel-groups])[
  Use the fiber products
  #klein-four-fiber-square
  and
  #cyclic-four-fiber-square
  in the two cases, where $abs(H) = 2$ and $overline(ZZ) = ZZ slash 2 ZZ$.
]

#exercise[
  Let $f: A arrow X$ and $g: A arrow Y$ be group homomorphisms, where $X$ and
  $Y$ are finite groups. Set
  $ (f,g) A = lr({(f(a),g(a)) in X times Y: a in A}), $
  a subgroup of the direct product $X times Y$. Prove that
  $ lr(|X times Y: (f,g) A|) = lr(|X: f(A)|) lr(|Y: g(ker f)|). $
  In particular, if $f(A) = X$ and $(f,g) A lt.closed.eq X times Y$, show that
  $ (X times Y) / ((f,g) A) tilde.equiv Y / g(ker f). $
] <exc:product-homomorphism-cokernel-order>
#hint([@exc:product-homomorphism-cokernel-order])[
  The sequence
  $ 1 arrow g(ker f) arrow (f,g) A arrow f(A) arrow 1 $
  is exact.
]

#exercise[
  Let $Lambda subset.eq Gamma$ be $R$-orders in a $K$-algebra $A$. Prove that
  $ Lambda inter Gamma^dot = Lambda^dot. $
] <exc:order-overorder-unit-intersection>
#source(317)
#hint([@exc:order-overorder-unit-intersection])[
  For $x in Lambda inter Gamma^dot$, we have $x^(-1) in Gamma$, so $x^(-1)$ is
  integral over $R$. Thus there is an equation
  $ (x^(-1))^n + a_1 lr((x^(-1)))^(n-1) + dots + a_n = 0, quad a_i in R. $
  Multiplying by $x^(n-1)$, we deduce that $x^(-1) in R[x] subset.eq Lambda$, so
  $x in Lambda^dot$.
]

#exercise[
  Keep the above notation, and assume that $R$ has finite residue class fields.
  Show that $Gamma^dot slash Lambda^dot$ is finite.
] <exc:order-unit-group-finite-index>
#hint([@exc:order-unit-group-finite-index])[
  Choose $a in R$, $a != 0$, such that $1+a Gamma subset.eq Lambda subset.eq
  Gamma$, and set $overline(Gamma) = Gamma slash a Gamma$ (a finite ring). There
  is a homomorphism $Gamma^dot arrow overline(Gamma)^dot$ whose kernel is
  $(1+a Gamma) inter Gamma^dot$, which is $(1+a Gamma)^dot$ according to the
  preceding exercise. Hence $Gamma^dot slash (1+a Gamma)^dot$ is embedded in the
  finite group $overline(Gamma)^dot$, so $(1+a Gamma)^dot$ has finite index in
  $Gamma^dot$. The same then holds for $Lambda^dot$.
]

#exercise[
  Let $D$ be an additive group with involution $tau$, and suppose that $2$ acts
  invertibly on $D$. Prove that (see p. 275)
  $ D tilde.equiv D^+ plus.o D^-. $
] <exc:involution-plus-minus-decomposition>

#exercise[
  Let
  $ 0 arrow A arrow^f B arrow^g C arrow 0 $
  be an exact sequence of additive groups with involution $tau$ which commutes
  with $f$ and $g$. Assume that $2$ acts invertibly on $C$. Prove that
  $ 0 arrow A^- arrow B^- arrow C^- arrow 0 $
  is exact.
] <exc:involution-minus-part-exactness>
#hint([@exc:involution-minus-part-exactness])[
  Let $c in C^-$, so $tau(c) = -c$. Choose $b in B$ with $g(b) = c slash 2$.
  Then
  $ g(b-tau b) = c, $
  so $g(B^-) = C^-$.
]

#exercise[
  Let $Lambda = ZZ G$, where $G$ is an abelian $p$-group, $p$ odd. Prove that
  $
    Lambda^dot = (Lambda^dot)^+ times G, quad "where"
    (Lambda^dot)^+ = lr({u in Lambda^dot: tau(u) = u}),
  $
  with $tau$ the canonical involution on $Lambda$ (see
  §@ss:class-kernel-group-involution).
] <exc:abelian-p-group-units-real-times-group>
#hint([@exc:abelian-p-group-units-real-times-group], caption: [Hint
  (Fröhlich):])[
  Let $Gamma$ be the maximal order in $QQ G$. Then
  $Gamma^dot = (Gamma^dot)^+ times T$, where $T$ is the odd part of the torsion
  subgroup of $Gamma^dot$. For $u in Lambda^dot$, write $u = x y$ with
  $x in (Gamma^dot)^+$, $y in T$. Then $u^m = x^m$ for some odd $m$, so
  $u^m in (Lambda^dot)^+$. Therefore $(Lambda^dot)^+ times G$ has odd index in
  $Lambda^dot$, and hence $G = Lambda^dot inter T$. But for any
  $x in Lambda^dot$,
  $x^2 = (x tau(x))(x slash tau(x)) in (Lambda^dot)^+ times G$. Hence
  $Lambda^dot = (Lambda^dot)^+ times G$.
]

#exercise[
  Let $R = ZZ[omega]$, $K = QQ(omega)$, where $omega$ is a primitive $p^m$-th
  root of $1$, $m >= 1$, and $p$ is prime. Let $P = (1-omega) R$, the unique
  prime ideal of $R$ containing $p$. Show that
  $
    p R = P^(phi(p^m)) quad "and" quad frak(D)(R slash ZZ) = P^t,
    quad "where" t = m phi(p^m) - p^(m-1).
  $
  Here, $frak(D)(R slash ZZ)$ denotes the different of $R$ relative to $ZZ$ (see
  §@i:ss:dedekind-ideal-theory).
] <exc:prime-power-cyclotomic-different>
#source(318)
#hint([@exc:prime-power-cyclotomic-different])[
  The prime $p$ ramifies completely in $K$, so $p R = P^(phi(p^m))$. By
  §@i:ss:dedekind-ideal-theory, the absolute norm of $frak(D)(R slash ZZ)$ is
  the discriminant of $R$ relative to $ZZ$. But $N_(K slash QQ) P = p$, and
  therefore
  $
    frak(D)(R slash ZZ) = P^t, quad "where" t "is such that"
    d(R slash ZZ) = plus.minus p^t.
  $
  The discriminant $d(R slash ZZ)$ is well known (see @bib:CurtisReiner1962[CR]
  (21.12), for example), and the exponent $t$ is precisely
  $m phi(p^m) - p^(m-1)$.
]

#exercise[
  In the above, let $p$ be odd, put $s=m$, and set
  $K_0 = QQ(omega+overline(omega))$, $R_0 = "alg. int." lr({K_0})$. In this
  exercise, $d$ denotes the discriminant ideal. Prove that
  $
    d(R slash ZZ) / d(R_0 slash ZZ) = p^(f(s)) ZZ,
    quad "where" f(s) = 1/2 lr({s p^s - (s+1) p^(s-1) + 1}).
  $
] <exc:cyclotomic-real-discriminant-ratio>
#hint([@exc:cyclotomic-real-discriminant-ratio])[
  Put $P_0 = P inter R_0$, so $P_0 R = P^2$ and $P_0$ is tamely ramified in
  $K slash K_0$. By Exercises @i:exc:different-ramification-bound and
  @i:exc:tame-ramification-trace, we obtain $frak(D)(R slash R_0) = P R$.
  Therefore
  $
    frak(D)(R slash ZZ) = frak(D)(R slash R_0) frak(D)(R_0 slash ZZ)
    = P frak(D)(R_0 slash ZZ).
  $
  Applying $N_(K slash QQ)$ to both sides, we have
  $ d(R slash ZZ) = p lr({d(R_0 slash ZZ)})^2. $
]

#exercise[
  Prove that if $S$ is tamely ramified over $R$, then the crossed-product order
  $(S compose G)_f$, defined as in @eq:crossed-product-algebra-order-definition,
  is hereditary.
] <exc:tame-crossed-product-order-hereditary>
#hint([@exc:tame-crossed-product-order-hereditary])[
  Imitate the proof of @i:th:twisted-group-ring-heredity after normalizing the
  factor set so that $u_1 = 1$. The result is due to Williamson
  @bib:Williamson1963 and Harada @bib:Harada1964.
]

#exercise[
  Let $G = op("Gal")(L slash K)$ be a cyclic group of order $n$, with generator
  $sigma$, and let $A = (L compose G)_f$ be a crossed-product algebra as in
  @eq:crossed-product-algebra-order-definition. Let $f$ be the factor set
  arising from the relations
  $
    u_(sigma^i) = u_sigma^i, quad 0 <= i <= n-1, quad
    u_sigma^n = r, r in L^dot.
  $
  Show that $r in K^dot$, and that
  $
    op("nr")_(A slash K) lr((a+u_sigma b)) = N_(L slash K) lr((a))
    - (-1)^n (N_(L slash K) lr((b))) r quad "for" a,b in L.
  $
] <exc:cyclic-crossed-product-binomial-norm>
#hint([@exc:cyclic-crossed-product-binomial-norm])[
  Since $u_sigma$ commutes with $r$, it follows that $r in K^dot$. Next, the map
  $phi: A arrow M_n lr((L))$ given in @lem:crossed-product-matrix-reduced-norm
  carries $a+u_sigma b$ onto the $n times n$ matrix
  $
    mat(
      delim: "[",
      a, b, 0, dots, 0, 0;
      0, sigma a, sigma b, dots, 0, 0;
      0, 0, sigma^2 a, dots, 0, 0;
      , , , dots, , ;
      , , , , sigma^(n-2) a, sigma^(n-2) b;
      r sigma^(n-1) b, 0, 0, dots, 0, sigma^(n-1) a;
    ),
  $
  whose determinant is easily computed.
]

#source(319)
#exercise[
  Let $K <= H lt.closed.eq G$ be finite groups, with $K lt.closed.eq G$, and let
  $chi: H arrow CC^dot$ be a linear character trivial on $K$. Assume that
  $op("ind")_H^G chi$ is an irreducible complex character of $G$, and let $phi$
  be the projection of $CC G$ onto the corresponding simple component. Prove
  that for the $ZZ$-order $phi(ZZ G)$, the kernel group $D(phi(ZZ G))$ is
  trivial.#ed-note[
    The original Hint uses $G slash K$ as the acting group instead of
    $G slash H$. Its construction also requires normality of $ker chi$, which is
    not a hypothesis of the exercise. For example, take $G=A_4$, $H=V_4$, $K=1$
    and a nontrivial linear $chi$: its three conjugates are distinct, so its
    induction is irreducible, but its kernel is not normal in $A_4$. Thus the
    argument in the Hint proves the normal-kernel case; the printed Hint does
    not establish the general assertion, which is quoted from Wilson
    @bib:Wilson1977b.
  ]
] <exc:normal-subgroup-monomial-component-trivial-kernel>
#hint(
  [@exc:normal-subgroup-monomial-component-trivial-kernel],
  caption: [Hint (Wilson @bib:Wilson1977b):],
)[
  Suppose first that $J=ker chi$ is normal in $G$, and set
  $overline(G)=G slash J$, $overline(H)=H slash J$, $T=G slash H$. Then
  $overline(H)$ is cyclic and $chi$ is faithful on it. The order $phi(ZZ G)$ is
  a crossed-product order $(R compose T)_f$, where $R=ZZ[eta]$ and $eta$ is a
  primitive $abs(overline(H))$-th root of $1$. The factor set $f$ is the image
  under $chi$ of the factor set of
  $1 arrow overline(H) arrow overline(G) arrow T arrow 1$. Irreducibility of
  $op("ind")_H^G chi$ and the Mackey criterion imply that $T$ acts faithfully on
  $overline(H)$, hence on $R$. Wilson's Theorem
  @th:wilson-crossed-product-order-trivial-kernel proves the conclusion in this
  case.]
