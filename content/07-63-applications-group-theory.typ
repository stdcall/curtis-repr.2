#import "main-defs.typ": *
#import "statements.typ": *

== Applications to Group Theory <sec:blocks-group-theory>

=== The Kernel of the Principal Block <ss:principal-block-kernel>

In this subsection, $G$ denotes a finite group, $p$ a prime number, and
$(K,R,k)$ a $p$-modular system such that $"char" K=0$ and $K$ is sufficiently
large relative to $G$. The _$K$-kernel_ of a $p$-block $upright(sans(B))$ of $G$
is the intersection of the kernels of the irreducible $K$-characters belonging
to $upright(sans(B))$. Similarly, the _$k$-kernel_ of $upright(sans(B))$ is the
intersection of the kernels of the irreducible $k$-representations of $G$
belonging to $upright(sans(B))$. We shall prove two results of Brauer
@bib:Brauer1964 on the kernel of the principal block.
#idx("p-Blocks", "kernel of", target: [@ss:principal-block-kernel])
#idx("Principal p-block", "kernel of", target: [@ss:principal-block-kernel])

#theorem[
  The $K$-kernel of the principal $p$-block $upright(sans(B))_1$ of $G$ is the
  maximal normal $p'$-subgroup $O_(p') lr((G))$ of $G$.
] <th:principal-block-character-kernel>

#proof[
  Let
  $ f=abs(O_(p') lr((G)))^(-1) sum_(x in O_(p') lr((G))) x. $
  Then $f$ is an idempotent in the center $c(R G)$ of $R G$, since
  $O_(p') lr((G))$ is a normal $p'$-subgroup of $G$; $K f$ affords the trivial
  representation of $O_(p') lr((G))$. We have
  $ f=sum_(i in I) b_i, $
  for certain block idempotents $b_i in c(R G)$, and each block idempotent $b_i$
  can be
  #source(547)
  expressed as a sum
  $ b_i=sum_(zeta^j in upright(sans(B))_i) e_j, $
  where $lr({e_j})$ is the set of central primitive idempotents in $K G$
  associated with characters $zeta^j$ belonging to the block
  $upright(sans(B))_i$ defined by $b_i$. The central primitive idempotents $e_j$
  which occur as summands of $f$ are characterized by the condition $f e_j=e_j$.
  In particular, we have $f e_1=e_1$, where $e_1=abs(G)^(-1) sum_(g in G) g$ is
  the central primitive idempotent associated with the trivial $K$-character
  $1_G$ of $G$. It follows that the block idempotent $b_1$ associated with the
  principal block $upright(sans(B))_1$ of $G$ is a summand of $f$. Consequently,
  $f e_j=e_j$ for all irreducible characters $zeta^j$ belonging to
  $upright(sans(B))_1$, and it follows that
  $ O_(p') lr((G)) <= inter.big_(zeta^j in upright(sans(B))_1) ker zeta^j. $
  For the reverse inclusion, let $N$ denote the $K$-kernel of
  $upright(sans(B))_1$. If $N subset.eq.not O_(p') lr((G))$, then
  $p divides abs(N)$, and hence $N$ contains a $p$-element $u !=1$. Then by the
  $p$-section orthogonality theorem @th:block-p-section-orthogonality, we have
  $
    0=sum_(zeta^j in upright(sans(B))_1) zeta^j lr((u)) zeta^j lr((1))
    =sum_(zeta^j in upright(sans(B))_1) (zeta^j lr((1)))^2,
  $
  which is impossible. Therefore $N <= O_(p') lr((G))$ and the theorem is
  proved.
]

#theorem[
  The $k$-kernel of the principal $p$-block $upright(sans(B))_1$ is
  $O_(p',p) lr((G))$, which is the maximal normal subgroup $L$ containing
  $O_(p') lr((G))$ such that the quotient $L slash O_(p') lr((G))$ is a
  $p$-group.
] <th:principal-block-modular-kernel>

#proof[
  Let $Q$ be the $k$-kernel of $upright(sans(B))_1$, and let $F_j$ be a simple
  $k G$-module belonging to $upright(sans(B))_1$. Then there exists a simple
  $K G$-module $Z_i$ belonging to $upright(sans(B))_1$ such that $F_j$ occurs as
  a composition factor of $overline(M)_i$, where $M_i$ is a full $R G$-lattice
  in $Z_i$, since the decomposition map is surjective (see Corollary
  @i:cor:decomposition-map-surjective). If $x in O_(p') lr((G))$, then $x$ acts
  trivially on $Z_i$ by Theorem @th:principal-block-character-kernel, and hence
  $x$ acts trivially on $F_j$. This proves that
  $ O_(p') lr((G)) <= Q. $
  Now let $s$ be a $p'$-element in $Q$. Then $phi^j lr((s))=phi^j lr((1))$ for
  all irreducible Brauer characters $phi^j in upright(sans(B))_1$. For each
  irreducible $K$-character $zeta^i in upright(sans(B))_1$, we have
  $ zeta^i=sum_(phi^j in upright(sans(B))_1) d_(i j) phi^j quad "on" G_(p'), $
  where $(d_(i j))$ is the decomposition matrix (see
  @eq:block-decomposition-matrix). It follows that
  $
    zeta^i lr((s))=sum_(phi^j in upright(sans(B))_1) d_(i j) phi^j lr((s))
    =sum_(phi^j in upright(sans(B))_1) d_(i j) phi^j lr((1))=zeta^i lr((1)).
  $
  Thus $s$ belongs to the $K$-kernel of $upright(sans(B))_1$, which is
  $O_(p') lr((G))$ by @th:principal-block-character-kernel. At this point, we
  have proved that $Q slash O_(p') lr((G))$ is a $p$-group.
  #source(548)

  On the other hand, $O_(p') lr((G))$ acts trivially on each simple $k G$-module
  $F_j$ belonging to $upright(sans(B))_1$, by the first part of the proof, so
  $F_j$ is a simple $k(G slash O_(p') lr((G)))$-module. By Clifford’s Theorem
  (see @i:prop:normal-p-subgroup-brauer-kernel), any normal $p$-subgroup of
  $G slash O_(p') lr((G))$ acts trivially on $F_j$, and it follows that
  $O_(p',p) lr((G)) <= Q$. This completes the proof.
]

#corollary[
  The group $G$ has a normal $p$-complement (see
  §~@i:ss:normal-p-complements-transfer) if and only if the Brauer character
  $phi^1$ afforded by the trivial $k G$-module is the only irreducible Brauer
  character belonging to the principal block.
] <cor:principal-block-single-brauer-character>

#proof[
  We clearly have
  $ O_(p',p) lr((G))=G <==> G "has a normal" p"-complement". $
  But the condition $O_(p',p) lr((G))=G$ is also equivalent to the statement
  that $phi^1$ is the only irreducible Brauer character belonging to
  $upright(sans(B))_1$, by @th:principal-block-modular-kernel. This completes
  the proof.
]

=== The Brauer–Suzuki Theorem on Quaternion Sylow 2-Groups
<ss:brauer-suzuki-quaternion-sylow>

A generalized quaternion $2$-group $S$ has a presentation
$ S=chevron.l x,y:x^(2^n)=1,y^2=x^(2^(n-1)),x^y=x^(-1) chevron.r. $
The quaternion group $Q$ is the generalized quaternion group of order $8$. In
§~@i:ss:brauer-suzuki-generalized-quaternion, we proved that the generalized
quaternion groups of order $>=16$ cannot occur as Sylow $2$-subgroups of finite
simple groups. In this subsection we shall prove the corresponding result for
Sylow $2$-subgroups of order $8$:

#theorem[
  (Brauer–Suzuki @bib:Brauer1959). Let $G$ be a finite group whose Sylow
  $2$-subgroups are quaternion groups of order $8$, and let $t$ be the unique
  involution in a Sylow $2$-subgroup of $G$. Then $G$ contains a proper normal
  subgroup $N$ such that $t in N$.
] <th:brauer-suzuki-quaternion-eight>
#idx("Brauer-Suzuki Theorem", target: [@th:brauer-suzuki-quaternion-eight])

This theorem completes the line of investigation begun in
§~@i:ss:brauer-suzuki-generalized-quaternion, and will be applied in
§~@ss:glauberman-z-star to prove the important $Z^*$-theorem of Glauberman. A
new approach is needed in order to prove Theorem
@th:brauer-suzuki-quaternion-eight, however, since the first two steps of the
proof of Theorem @i:th:brauer-suzuki-generalized-quaternion are not valid in
case the Sylow groups are quaternion of order $8$. Our method this time will be
to investigate the $K$-characters in the principal $2$-block of $G$, following
the lectures of Dade @bib:Dade1971a.

We begin with some general remarks based on our previous discussion of
$p$-sections and orthogonality (§~@ss:block-orthogonality-p-sections). As in
§~@ss:block-orthogonality-p-sections, we fix a $p$-modular system $(K,R,k)$ such
that $"char" K=0$, $K$ is sufficiently large relative to $G$, and $R$ is a
complete d.v.r. with maximal ideal $frak(p)$ such that $R slash frak(p)$ is a
perfect field of characteristic $p$.

Let $T$ be a set of $p$-elements in $G$ such that $T=T^(-1)$. The _union of
$p$-sections_ $X(T)$ is defined by
$ X(T)={x in G:x_p in_G T}, $
#source(549)
where $x_p$ denotes the $p$-part of $x$, and $u in_G T$ means that $u^g in T$
for some $g in G$. Then $X(T)$ is a union of conjugacy classes,
$X(T)=X(T)^(-1)$, and $X(T)$ is also a union of $p$-sections (see
§~@ss:block-orthogonality-p-sections).

It will be useful to introduce some notation. We define sets of class functions:
$
  "cf"(G,X(T))={alpha in "cf"_K lr((G)):alpha(x)=0
    "for all" x in G-X(T)},
$
$
  "cf"(G,X(T);upright(sans(B))_j)=
  {alpha_(upright(sans(B))_j):alpha in "cf"(G,X(T))},
$
where $alpha_(upright(sans(B))_j)$ is the contribution to $alpha$ from
irreducible characters in the $p$-block $upright(sans(B))_j$:
$
  alpha_(upright(sans(B))_j)=
  sum_(zeta^i in upright(sans(B))_j) (alpha,zeta^i) zeta^i,
  quad "for" alpha in "cf"_K lr((G)).
$
As an immediate consequence of Theorem @th:p-section-vanishing-blockwise and the
above remarks, we have:

#proposition[
  Keep the preceding notation. Then
  $ "cf"(G,X(T))=plus.o.big_j "cf"(G,X(T);upright(sans(B))_j), $
  where the sum is taken over the $p$-blocks of $G$, and the summands are
  orthogonal with respect to the usual scalar product of class functions.
] <prop:p-section-block-projection-decomposition>

Now let $S$ be a T.I. set in $G$ with the property that $x in S$ if and only if
$x_p in S$, where $x_p$ is the $p$-part of $x$ (see
@i:def:trivial-intersection-set). Let $T$ be the set of $p$-elements in $S$, and
assume that $T=T^(-1)$. Let $H=N_G lr((S))$; then $S$ is the $p$-section in $H$
defined by $T$, and the $p$-section $X(T)$ in $G$ defined by $T$ is the set of
all conjugates of elements of $S$:
$ X(T)={x^g:x in S,g in G}. $
We shall denote $X(T)$ by $S^G$, in view of the preceding remark.

#theorem[
  Keep the preceding assumptions and notation. Then the induction map defines a
  surjective isometry
  $
    "ind"_H^G:"cf"(H,S;upright(sans(B))'_1) -> "cf"(G,S^G;upright(sans(B))_1),
  $
  where $upright(sans(B))'_1$ and $upright(sans(B))_1$ denote the principal
  $p$-blocks of $H$ and $G$, respectively. The inverse map is given by
  $ mu |-> mu_S, quad "for" mu in "cf"(G,S^G;upright(sans(B))_1), $
  where $mu_S$ is the class function on $H$ which coincides with $mu$ on $S$ and
  vanishes on $H-S$.
] <th:ti-principal-block-induction-isometry>

#proof[
  Using Steps 2 and 3 of the proof of Frobenius’s Theorem
  @i:th:frobenius-kernel, it follows that
  #source(550)
  $ "ind"_H^G:"cf"(H,S) -> "cf"(G,S^G) $
  is an isometry, where $S$ is the T.I. set described above and $H=N_G lr((S))$.
  The same arguments show that
  $ (psi^G)_S=psi quad "and" quad (mu_S)^G=mu $
  for all $psi in "cf"(H,S)$ and $mu in "cf"(G,S^G)$, where
  $psi^G="ind"_H^G psi$, and $mu_S$ is defined as in the statement of the
  theorem. Therefore the induction map from $"cf"(H,S)$ to $"cf"(G,S^G)$ is
  surjective, and the inverse map is $mu |-> mu_S$.

  In order to make a connection between the induction map and the principal
  blocks of $H$ and $G$, we shall use Brauer’s Second Main Theorem, and
  therefore we consider centralizers of the $p$-elements contained in $S$.

  Let $u in T$; then $C_G lr((u)) <= H$ since $S$ is a T.I. set, and we set
  $ X(u)={x in C_G lr((u)):x_p in {u,u^(-1)}}. $
  Then $X(u)$ is an inverse-closed union of $p$-sections in $C_G lr((u))$ for
  each $u in T$, and we have
  $ S=union.big_(u in T) X(u) $
  (note that $X(u)=X(u^(-1))$ and that $X(u)$ is a union of conjugacy classes in
  $C_G lr((u))$).

  Let $mu$ be a class function on any subgroup containing $H$, and let $u in T$.
  We let $mu_(X(u))$ denote the class function on $C_G lr((u))$ which coincides
  with $mu$ on $X(u)$ and vanishes outside $X(u)$. Then by
  @prop:p-section-block-projection-decomposition, applied to $C_G lr((u))$, we
  have
  $
    mu_(X(u))=
    sum_(tilde(upright(sans(B)))_i) (mu_(X(u)))_(tilde(upright(sans(B)))_i),
  $
  <eq:centralizer-section-block-components>
  where $lr({tilde(upright(sans(B)))_i})$ are the blocks of $C_G lr((u))$.

  In particular, if $mu in "cf"(G,S^G;upright(sans(B))_1)$, then
  @eq:centralizer-section-block-components becomes
  $
    mu_(X(u))=(mu_(X(u)))_(tilde(upright(sans(B)))_1), quad
    (mu_(X(u)))_(tilde(upright(sans(B)))_i)=0
    quad "if" tilde(upright(sans(B)))_i !=
    tilde(upright(sans(B)))_1,
  $ <eq:centralizer-section-principal-component>
  where $tilde(upright(sans(B)))_1$ is the principal block of $C_G lr((u))$, by
  Brauer’s Second and Third Main Theorems (see @th:brauer-second-main-first-form
  and @th:brauer-third-main-theorem).

  On the other hand, if $psi$ is a class function on a subgroup containing $H$,
  we have
  $ psi_S=sum_(upright(sans(B))'_j) (psi_S)_(upright(sans(B))'_j), $
  by @prop:p-section-block-projection-decomposition again, since $S$ is a
  $p$-section in $H$, and the sum is taken over the blocks of $H$. Another
  application of the Second Main Theorem yields
  $
    ((psi_S)_(upright(sans(B))'_j))_(X(u))=
    sum_((tilde(upright(sans(B)))_i)^H=upright(sans(B))'_j)
    (psi_(X(u)))_(tilde(upright(sans(B)))_i),
  $
  where the sum is taken over the blocks of $C_G lr((u))$.
  #source(551)

  Now let $mu in "cf"(G,S^G;upright(sans(B))_1)$. For each $u in T$, the
  principal block of $C_G lr((u))$ is the only block occurring in
  @eq:centralizer-section-principal-component. Its induced block in $H$ is the
  principal block $upright(sans(B))'_1$, by @th:brauer-third-main-theorem. Thus
  the preceding local projection identity gives
  $
    ((mu_S)_(upright(sans(B))'_j))_(X(u))=0
    quad "if" upright(sans(B))'_j !=upright(sans(B))'_1.
  $
  Each projection $(mu_S)_(upright(sans(B))'_j)$ vanishes off $S$, by
  @prop:p-section-block-projection-decomposition. Since
  $S=union.big_(u in T) X(u)$, these nonprincipal projections vanish everywhere.
  Consequently
  $ mu_S=(mu_S)_(upright(sans(B))'_1). $
  Thus the map $mu |-> mu_S$ carries $"cf"(G,S^G;upright(sans(B))_1)$ into
  $"cf"(H,S;upright(sans(B))'_1)$.

  In order to finish the proof, we have to show that
  $psi^G in "cf"(G,S^G;upright(sans(B))_1)$ for all
  $psi in "cf"(H,S;upright(sans(B))'_1)$. We have
  $psi^G=sum (psi^G)_(upright(sans(B))_i)$, and
  $(psi^G)_(upright(sans(B))_i) in "cf"(G,S^G;upright(sans(B))_i)$ for all
  $p$-blocks $upright(sans(B))_i$ of $G$, by
  @prop:p-section-block-projection-decomposition. We shall prove that
  $
    (((psi^G)_(upright(sans(B))_i))_S)_(upright(sans(B))'_1)=0
    quad "if" upright(sans(B))_i != upright(sans(B))_1.
  $ <eq:nonprincipal-block-restriction-principal-zero>
  This will imply that
  $ ((psi^G)_(upright(sans(B))_1))_S=(psi^G)_S, $
  and hence
  $psi^G=(psi^G)_(upright(sans(B))_1) in "cf"(G,S^G;upright(sans(B))_1)$ since
  $mu |-> mu_S$ is the inverse of the induction map. In order to prove
  @eq:nonprincipal-block-restriction-principal-zero, let
  $mu in "cf"(G,S^G;upright(sans(B))_i)$, for $i !=1$. Then for each $u in T$,
  we have, as in @eq:centralizer-section-principal-component,
  $ mu_(X(u))=sum (mu_(X(u)))_(tilde(upright(sans(B)))_j), $
  where the sum is taken over blocks $tilde(upright(sans(B)))_j$ of
  $C_G lr((u))$ such that $(tilde(upright(sans(B)))_j)^G=upright(sans(B))_i$.
  Then $(mu_(X(u)))_(tilde(upright(sans(B)))_1)=0$, by
  @th:brauer-third-main-theorem, where $tilde(upright(sans(B)))_1$ is the
  principal block of $C_G lr((u))$. The local projection identity above,
  together with @th:brauer-third-main-theorem, therefore gives
  $ ((mu_S)_(upright(sans(B))'_1))_(X(u))=0 $
  for every $u in T$: the principal block of $C_G lr((u))$ is the only block
  inducing the principal block of $H$. The projection
  $(mu_S)_(upright(sans(B))'_1)$ vanishes off $S$, by
  @prop:p-section-block-projection-decomposition, and the sets $X(u)$ cover $S$.
  Hence $(mu_S)_(upright(sans(B))'_1)=0$, proving
  @eq:nonprincipal-block-restriction-principal-zero and completing the proof of
  Theorem @th:ti-principal-block-induction-isometry.#ed-note[
    The printed proof adds local functions on overlapping sets $X(u)$. For
    $G=H=C_3=chevron.l a chevron.r$, $p=3$, $S={a,a^2}$, and a nontrivial linear
    character $chi$, let $mu=2 dot 1-chi-chi^2$. Both $X(a)$ and $X(a^2)$ equal
    $S$, so that sum is $2 mu$, not $mu$. The pointwise argument uses the local
    projection identity, Brauer’s Second Main Theorem
    @th:brauer-second-main-first-form and Third Main Theorem
    @th:brauer-third-main-theorem.
  ]
]

The preceding result gives a method for finding the irreducible characters in
the principal block of $G$ which do not vanish on $S^G$. In particular, this
construction works in the following situation.

#definition[
  Keep the assumptions and notation from Theorem
  @th:ti-principal-block-induction-isometry. Let $lr({psi_1,...,psi_h})$ be the
  set of irreducible $K$-characters of $upright(sans(B))'_1$ which do not vanish
  on $S$; these characters $lr({psi_i})$ are said to be _coherent_ in case there
  exist irreducible $K$-characters of $G$ $lr({zeta_1,...,zeta_h})$ and signs
  $epsilon_i=plus.minus 1$, $1<=i<=h$, with the property that whenever
  $a_1 psi_1+...+a_h psi_h in "cf"(H,S;upright(sans(B))'_1)$, for $a_i in K$, we
  have
  $ (a_1 psi_1+...+a_h psi_h)^G=a_1 epsilon_1 zeta_1+...+a_h epsilon_h zeta_h. $
] <def:coherent-principal-block-characters>
#idx("Coherent", target: [@def:coherent-principal-block-characters])

#theorem[
  Let $lr({psi_1,...,psi_h})$ be coherent, according to
  @def:coherent-principal-block-characters. Then $lr({zeta_1,...,zeta_h})$ are
  precisely the irreducible characters in the principal block
  $upright(sans(B))_1$ of $G$
  #source(552)
  which do not vanish on $S^G$. Moreover, we have
  $ zeta_i bar.v_S=epsilon_i psi_i bar.v_S, quad "for" 1<=i<=h. $
] <th:coherent-principal-block-character-correspondence>

#proof[
  We shall use the notation $xi_X$ for the function which is equal to $xi$ on
  $X$, and vanishes off $X$, and $xi bar.v_X$ for the restriction of $xi$ to
  $X$, for $xi in "cf"(G)$, and $X subset.eq G$. We shall also need the result
  that, for a union of $p$-sections $X subset.eq G$ and an irreducible character
  $zeta$ belonging to a block $upright(sans(B))$, we have
  $
    zeta_X in "cf"(G,X;upright(sans(B))),
  $ <eq:section-truncation-block-support>
  which is easily proved using $p$-section orthogonality
  @th:block-p-section-orthogonality and @th:p-section-vanishing-blockwise.

  To begin the proof, let $zeta$ be an irreducible character in
  $upright(sans(B))_1$ which does not vanish on $S^G$. Then $zeta_(S^G)$ is a
  nonzero element of $"cf"(G,S^G;upright(sans(B))_1)$, and hence, by Theorem
  @th:ti-principal-block-induction-isometry, $(zeta_(S^G),psi^G) !=0$ for some
  $psi in "cf"(H,S;upright(sans(B))'_1)$. Since the characters $lr({psi_i})$ are
  coherent, we have $psi=sum a_i psi_i$ for some coefficients $a_i in K$, and
  $psi^G=sum a_i epsilon_i zeta_i in "cf"(G,S^G;upright(sans(B))_1)$. Then
  $ (zeta_(S^G),psi^G)=(zeta,sum a_i epsilon_i zeta_i) !=0, $
  and $zeta=zeta_i$ for some $i$, $1<=i<=h$.

  It remains to prove that $zeta_i in upright(sans(B))_1$ and
  $zeta_i bar.v_(S^G) !=0$, etc. for $1<=i<=h$. By
  @eq:section-truncation-block-support,
  $(psi_i)_S in "cf"(H,S;upright(sans(B))'_1)$, for $1<=i<=h$. Then
  $((psi_i)_S,psi)_H !=0$ for some $psi=sum a_j psi_j$ in
  $"cf"(H,S;upright(sans(B))'_1)$ and we have
  $ a_i=(psi_i,psi)_H=((psi_i)_S,psi)_H !=0. $
  Then $psi^G=sum a_i epsilon_i zeta_i in "cf"(G,S^G;upright(sans(B))_1)$ by
  @th:ti-principal-block-induction-isometry, and $zeta_i$ appears with nonzero
  multiplicity in $psi^G$, so $zeta_i in upright(sans(B))_1$.

  For all $psi in "cf"(H,S;upright(sans(B))'_1)$, we have
  $ (zeta_i,psi^G)=((epsilon_i psi_i)_S,psi) quad "for" 1<=i<=h, $
  by the preceding discussion. It follows that
  $
    ((zeta_i)_S,psi)_H=(zeta_i bar.v_H,psi)
    =(zeta_i,psi^G)=((epsilon_i psi_i)_S,psi)
  $ <eq:coherent-character-restriction-pairing>
  for all $psi in "cf"(H,S;upright(sans(B))'_1)$. We have
  $(epsilon_i psi_i)_S in "cf"(H,S;upright(sans(B))'_1)$ and
  $(zeta_i)_(S^G) in "cf"(G,S^G;upright(sans(B))_1)$ by
  @eq:section-truncation-block-support, and hence
  $(zeta_i)_S=((zeta_i)_(S^G))_S in "cf"(H,S;upright(sans(B))'_1)$, by Theorem
  @th:ti-principal-block-induction-isometry. Then
  $(zeta_i)_S=(epsilon_i psi_i)_S$ by
  @eq:coherent-character-restriction-pairing, since the scalar product $(,)_H$
  is nondegenerate when restricted to $"cf"(H,S;upright(sans(B))'_1)$ (see
  @prop:p-section-block-projection-decomposition). This completes the proof of
  the theorem.
]

We are now ready to begin the proof of the Brauer–Suzuki Theorem
@th:brauer-suzuki-quaternion-eight. Let $G$ be a counterexample of minimal
order, and let $Q$ be a fixed Sylow $2$-subgroup of $G$. Using the preceding
results, we shall first study the characters in the principal
#source(553)
$2$-blocks of certain subgroups of $G$, and use this information to derive a
contradiction involving characters in the principal $2$-block of $G$.

Throughout the discussion, we are concerned only with the prime $p=2$, and
therefore consider characters, modules, etc., with reference to a fixed
$2$-modular system $(K,R,k)$ satisfying the assumptions made earlier in the
section. We begin with a series of lemmas, starting from properties of the
subgroup $Q$.

#lemma[
  All elements of order $4$ in $Q$ are conjugate in $G$.
] <lem:quaternion-order-four-fusion>

#proof[
  Let $x,y$ have order $4$ in $Q$. We may assume that $chevron.l x chevron.r !=
  chevron.l y chevron.r$ since $x=_Q x^(-1)$. Suppose $x eq.not_G y$; then
  $chevron.l x chevron.r eq.not_G chevron.l y chevron.r$. We shall apply the
  transfer homomorphism
  $ V_(chevron.l y chevron.r)^G:G slash G' -> chevron.l y chevron.r $
  (see @i:eq:transfer-domain), and will prove that
  $x G' in.not ker V_(chevron.l y chevron.r)^G$, using a computation similar to
  the proof of Burnside’s Transfer Theorem @i:th:burnside-normal-p-complement.
  We first consider the orbits of $chevron.l x chevron.r$ acting on
  $G slash chevron.l y chevron.r$. Let $z_i chevron.l y chevron.r$ be a
  representative of an $chevron.l x chevron.r$-orbit of cardinality $d_i$; then
  $lr({x^j z_i,0<=j<=d_i-1})$ are representatives of the cosets of
  $G slash chevron.l y chevron.r$ corresponding to the orbit, and we have
  $
    x x^j z_i=x^(j+1) z_i, quad 0<=j<=d_i-1 quad "and" quad
    x x^(d_i-1) z_i=z_i y_i, quad "for" y_i in chevron.l y chevron.r.
  $
  Then
  $ V_(chevron.l y chevron.r)^G x G'=product y_i=product z_i^(-1) x^(d_i) z_i, $
  where the product is taken over the $chevron.l x chevron.r$-orbits, of
  cardinalities $lr({d_i})$. If some $d_i$ is odd, then
  $chevron.l (x^(d_i))^(z_i) chevron.r=chevron.l x^(z_i) chevron.r subset.eq
  chevron.l y chevron.r$ since $d_i$ is the least power of $x^(z_i)$ contained
  in $chevron.l y chevron.r$. This implies that $x=_G y$, contrary to
  assumption. If $d_i$ is even, then $(x^(d_i))^(z_i)=x^(d_i)$ (since
  $4 divides d_i ==> x^(d_i)=1$, while if $2 divides d_i$ (but not $4$), then
  $(x^(d_i))^(z_i)=y^2=x^2=x^(d_i)$). Therefore
  $
    V_(chevron.l y chevron.r)^G x G'=x^(abs(G colon chevron.l y chevron.r)) !=1
  $
  since $abs(G colon chevron.l y chevron.r)=2 q$ with $q$ odd, and
  $x^(2 q) !=1$. On the other hand, $V_(⟨ y ⟩)^G x^2 G'=
  x^(2 abs(G colon chevron.l y chevron.r))=1$. It follows that $G$ contains a
  proper normal subgroup $N$ such that $t=x^2 in N$, where $t$ is the involution
  in $Q$. This contradicts the assumption that $G$ is a minimal counterexample,
  and completes the proof.
]

#corollary[
  All elements of order $4$ in $Q$ are conjugate in $C_G lr((t))$, where $t$ is
  the unique involution in $Q$.
] <cor:quaternion-centralizer-order-four-fusion>

#proof[
  Let $x,y in Q$ be elements of order $4$. Then $x^g=y$ for some $g in G$, by
  @lem:quaternion-order-four-fusion. Then $x^2=y^2=t$, and it follows that
  $g in C_G lr((t))$.
]
#source(554)

Now we fix some notation for the rest of the proof. We set
$ H=C_G lr((t)) quad "and" quad L=N_G lr((chevron.l x chevron.r)), $
where $t$ is the involution in $Q$ and $x$ is a fixed element of order $4$ in
$Q$. We clearly have $L<=H$.

#lemma[
  We have
  $ L=Q O_(2') lr((L)) quad "and" quad O_(2') lr((L)) <= C_G lr((x)). $
] <lem:quaternion-normalizer-odd-complement>

#proof[
  Since $chevron.l x chevron.r ⊴ Q$, $Q$ is also a Sylow $2$-subgroup of $L$.
  The map $x |-> x^(-1)$ is the only nontrivial automorphism of
  $chevron.l x chevron.r$, so any element of $Q-chevron.l x chevron.r$ inverts
  $x$. It follows that $L=Q C_G lr((x))$, and that
  $chevron.l x chevron.r=Q inter C_G lr((x))$ is a cyclic Sylow $2$-subgroup of
  $C_G lr((x))$. Then
  $C_G lr((x))=chevron.l x chevron.r O_(2') lr((C_G lr((x))))$ by
  @i:cor:cyclic-sylow-two-normal-complement. Moreover,
  $O_(2') lr((C_G lr((x))))$ is characteristic in $C_G lr((x))$ and hence normal
  in $L$, so $L=Q O_(2') lr((C_G lr((x))))$ and
  $O_(2') lr((C_G lr((x))))=O_(2') lr((L))$. This completes the proof.
]

By @th:principal-block-character-kernel, the characters in the principal block
$upright(sans(B))_1(L)$ contain $O_(2') lr((L))$ in their kernels, and are
consequently the irreducible characters of $Q$, lifted to $L$, by
@lem:quaternion-normalizer-odd-complement. We expect a factorization
$G=H O_(2') lr((G))$, and hence, using @th:principal-block-character-kernel, we
hope to construct characters in the principal block of $G$ from those in
$upright(sans(B))_1(H)$, and, in turn, from the known characters in
$upright(sans(B))_1(L)$. We now begin to put this plan into action.

The character table of $Q$ is as follows:

#table(
  columns: 6,
  align: center,
  table.header([], [$1$], [$t$], [$x$], [$y$], [$x y$]),
  table.hline(),
  table.vline(x: 1),
  [$1$], [$1$], [$1$], [$1$], [$1$], [$1$],
  [$lambda_1$], [$1$], [$1$], [$1$], [$-1$], [$-1$],
  [$lambda_2$], [$1$], [$1$], [$-1$], [$1$], [$-1$],
  [$lambda_3$], [$1$], [$1$], [$-1$], [$-1$], [$1$],
  [$theta$], [$2$], [$-2$], [$0$], [$0$], [$0,$],
)

where $y$ is an element of order $4$ such that
$chevron.l y chevron.r !=chevron.l x chevron.r$.

Each irreducible character $chi$ of $Q$ can be extended to an irreducible
character $tilde(chi)$ of $L$ having $O_(2') lr((L))$ in its kernel, by
@lem:quaternion-normalizer-odd-complement. As an immediate consequence of
@th:principal-block-character-kernel and
@lem:quaternion-normalizer-odd-complement, we have:

#lemma[
  $
    upright(sans(B))_1(L)={tilde(1),tilde(lambda)_1,
      tilde(lambda)_2,tilde(lambda)_3,
      tilde(theta)}.
  $
] <lem:quaternion-normalizer-principal-characters>

We next begin to investigate $upright(sans(B))_1(H)$, using
@th:ti-principal-block-induction-isometry, and the sets
$ sqrt(x)={l in L:x in chevron.l l chevron.r} $
#source(555)
and
$ sqrt(x)^H={l^h:l in sqrt(x),h in H}. $

#lemma[
  #case-list(
    numbering: "(i)",
    [#case[$sqrt(x)$ is a T.I. set in $L$ with the property that
        $l in sqrt(x) <==> l_2 in sqrt(x)$.]
      <case:quaternion-root-four-ti>],
    [#case[$sqrt(x)=x O_(2') lr((L)) union x^(-1) O_(2') lr((L))$.]
      <case:quaternion-root-four-cosets>],
    [#case[$"cf"(L,sqrt(x);upright(sans(B))_1(L))=
        chevron.l tilde(1)+tilde(lambda)_1-tilde(lambda)_2
        -tilde(lambda)_3 chevron.r$.]
      <case:quaternion-root-four-character-space>],
    [#case[The virtual character
        $ phi=(tilde(1)+tilde(lambda)_1-tilde(lambda)_2-tilde(lambda)_3)^H $
        generates $"cf"(H,sqrt(x)^H;upright(sans(B))_1(H))$.]
      <case:quaternion-root-four-induced-generator>],
    [#case[$(phi,phi)_H=4$, so $phi=1+a_1 psi_1+a_2 psi_2+a_3 psi_3$ for some
        irreducible characters $psi_i in upright(sans(B))_1(H)$ and signs
        $a_i=plus.minus 1$. Moreover,
        $lr({tilde(1),tilde(lambda)_1,tilde(lambda)_2,tilde(lambda)_3})$ are
        coherent (see @def:coherent-principal-block-characters) with
        $epsilon_1=a_1$, $epsilon_2=-a_2$, $epsilon_3=-a_3$.]
      <case:quaternion-root-four-coherence>],
    [#case[The irreducible characters in $upright(sans(B))_1(H)$ which do not
        vanish on $(sqrt(x))^H$ are precisely $lr({1,psi_1,psi_2,psi_3})$.]
      <case:quaternion-root-four-supported-characters>],
    [#case[We have $a_1 psi_1=a_2 psi_2=a_3 psi_3=1$ on $sqrt(x)$ and also on
      $(sqrt(x))^H$.] <case:quaternion-root-four-character-values>],
  )
] <lem:quaternion-root-four-principal-characters>

The proof is left as an exercise, using
@th:ti-principal-block-induction-isometry and
@th:coherent-principal-block-character-correspondence. For the application of
@th:ti-principal-block-induction-isometry, note that $sqrt(x)$ is a T.I. set in
$H$ with normalizer $L$: an intersection with its conjugate by $h in H$ forces
$chevron.l x chevron.r=chevron.l x chevron.r^h$, by taking $2$-parts, and hence
$h in L$. Note that @case:quaternion-root-four-character-space follows from
@lem:quaternion-normalizer-principal-characters. The fact that $(phi,phi)_H=4$
follows by Steps 2 and 3 of Theorem @i:th:frobenius-kernel, since
$tilde(1)+tilde(lambda)_1-tilde(lambda)_2-tilde(lambda)_3$ vanishes off the T.I.
set $sqrt(x)$. Part~@case:quaternion-root-four-coherence follows from
@th:ti-principal-block-induction-isometry, and the coherence condition
@def:coherent-principal-block-characters is easily verified. For the proof of
@case:quaternion-root-four-character-values we have
$
  a_1 psi_1 lr((x)) & =tilde(lambda)_1 lr((x))=1, \
  a_2 psi_2 lr((x)) & =-epsilon_2 psi_2 lr((x))=-tilde(lambda)_2 lr((x))=1, \
  a_3 psi_3 lr((x)) & =-epsilon_3 psi_3 lr((x))=-tilde(lambda)_3 lr((x))=1,
$
using the character table of $Q$.

In order to construct the remaining irreducible characters in
$upright(sans(B))_1(H)$, we make a deeper study of $"ch" H$, using the Brauer
Criterion @i:th:brauer-virtual-character-criterion, and the fact that for all
irreducible characters $psi$ of $H$, we have
$
  "either" psi(t h)=psi(h) quad "for all" h in H,
  quad "or" psi(t h)=-psi(h) quad "for all" h in H,
$
since $chevron.l t chevron.r$ is contained in $Z(H)$. We also note that
$ chevron.l t chevron.r H_(2')=H_(2') union t H_(2'), $
where $H_(2')$ is the set of all elements of odd order belonging to $H$. Since
$t in Z(H)$,
#source(556)
$chevron.l t chevron.r H_(2')$ is the $2$-section in $H$ consisting of all
elements whose $2$-part is either $1$ or $t$.

We now define two sets of virtual characters:
$
  X_(+)={xi in "ch" H:
    xi in "cf"(H,chevron.l t chevron.r H_(2');upright(sans(B))_1(H))
    "and" xi(t h)=xi(h) "for all" h in H},
$
$
  X_(-)={xi in "ch" H:
    xi in "cf"(H,chevron.l t chevron.r H_(2');upright(sans(B))_1(H))
    "and" xi(t h)=-xi(h) "for all" h in H}.
$
Both $X_(+)$ and $X_(-)$ are $ZZ$-submodules of $"ch" H$. We next define a map
$xi |-> xi^*$, for $xi in X_(+) union X_(-)$, where $xi^* in "cf" H$ is given by
$
  xi^* lr((h))=cases(
    xi(h) & "if" h in H_(2'),
    -xi(h) & "if" h in t H_(2'),
    0 & "otherwise".
  )
$

#lemma[
  The map $xi |-> xi^*$ has the properties
  $ (X_(+))^* subset.eq X_(-), quad (2 X_(-))^* subset.eq X_(+), $
  and is an isometry with respect to the scalar product of class functions on
  $H$.
] <lem:central-involution-character-star>

#proof[
  Let $xi in X_(+) union 2 X_(-)$. We first prove that $xi^* in "ch" H$, using
  Brauer’s Criterion @i:th:brauer-virtual-character-criterion. We must show that
  $xi^* bar.v_E in "ch" E$, for all elementary subgroups $E<=H$. By
  @cor:quaternion-centralizer-order-four-fusion, $lr({1,t,x})$ are
  representatives of all conjugacy classes of $2$-elements in $H$, so it is
  sufficient to consider elementary subgroups $E$ of the following types:
  $
    E=T, quad chevron.l t chevron.r times T, quad chevron.l x chevron.r times T,
    quad "and" quad Q times T
  $
  where $T$ is any subgroup of odd order.
  #case-list(
    prefix: "Case ",
    numbering: "1.",
    [#case[$E=T$. Then $xi^*=xi$.]
      <case:character-star-odd-elementary>],
    [#case[$E=chevron.l t chevron.r times T$. Since $xi in X_(+) union 2 X_(-)$,
        we have $xi bar.v_E=lambda times.o mu$, where $lambda$ is a linear
        character of $chevron.l t chevron.r$ and $mu$ is a virtual character of
        $T$. Then $xi^* bar.v_E=lambda' times.o mu$, where $lambda'$ is the
        other linear character of $chevron.l t chevron.r$.]
      <case:character-star-central-involution-elementary>],
    [#case[$E=chevron.l x chevron.r times T$. If $xi in X_(+) union X_(-)$, then
        $xi$ vanishes on elements of order $4$, so
        $xi bar.v_E=lambda^(chevron.l x chevron.r) times.o tau$ where $lambda$
        is a linear character of $chevron.l t chevron.r$ and $tau in "ch" T$.
        Then
        $xi^* bar.v_E=(lambda')^(chevron.l x chevron.r) times.o tau in "ch" E$,
        where $lambda'$ is defined as in
        Case~@case:character-star-central-involution-elementary.]
      <case:character-star-cyclic-four-elementary>],
    [#case[$E=Q times T$. Assume first that $xi in X_(-)$. Then
        $xi bar.v_E=theta times.o tau$ for some $tau in "ch" T$, since all
        characters of $Q$ different from $theta$ have $t$ in their kernel. Then
        if $xi in 2 X_(-)$, $xi bar.v_E=2 theta times.o tau$ and
        $xi^* bar.v_E=(1+lambda_1+lambda_2+lambda_3) times.o tau$ (since
        $2 theta$ has degree $4$, and a character of $Q$ vanishing on
        $Q-chevron.l t chevron.r$ is a multiple of the regular character of
        $Q slash chevron.l t chevron.r$). If $xi in X_(+)$, then
        $xi bar.v_E=(1+lambda_1+lambda_2+lambda_3) times.o tau$ for
        $tau in "ch" T$, and $xi^* bar.v_E=2 theta times.o tau$.]
      <case:character-star-quaternion-elementary>],
  )
  This completes the proof that $xi^* in "ch" H$ for all
  $xi in X_(+) union 2 X_(-)$.
  #source(557)

  We have, for $xi_1,xi_2 in X_(+) union 2 X_(-)$
  $
    (xi_1^*,xi_2^*)=abs(H)^(-1) sum_(h in H)
    xi_1^* lr((h)) xi_2^* lr((h^(-1)))
    =abs(H)^(-1) sum_(h in H) xi_1 lr((h)) xi_2 lr((h^(-1)))
  $
  by the definition of $xi^*$.

  At this point, we have $xi^* in "cf"(H,chevron.l t chevron.r H_(2'))$ for all
  $xi in X_(+) union 2 X_(-)$, and have to prove it is supported on
  $upright(sans(B))_1(H)$. Let $psi in op("Irr") H$, and assume
  $(psi,xi^*) !=0$, for $xi in X_(+) union 2 X_(-)$. Then
  $ (psi,xi^*)=(psi,(xi)_(H_(2'))-(xi)_(t H_(2'))) !=0. $
  Since both $(xi)_(H_(2'))$ and $(xi)_(t H_(2'))$ are in
  $"cf"(H,chevron.l t chevron.r H_(2');upright(sans(B))_1(H))$ by
  @eq:section-truncation-block-support, we have $xi^* in X_(+) union X_(-)$. The
  statements that $(X_(+))^* subset.eq X_(-)$ and $(2 X_(-))^* subset.eq X_(+)$
  are clear from what has been shown, and the lemma is proved.
]

#lemma[
  The irreducible characters in $upright(sans(B))_1(H)$ whose kernels contain
  $t$ are precisely $lr({1,psi_1,psi_2,psi_3})$.
] <lem:quaternion-centralizer-plus-characters>

#proof[
  By @case:quaternion-root-four-character-values, we have
  $ a_i psi_i lr((x))=1 quad "for" i=1,2,3. $
  If $t in.not ker psi_i$, then
  $psi_i bar.v_(chevron.l x chevron.r)=c_1 eta_1+c_2 eta_2$, with $c_i in ZZ$,
  where $eta_1,eta_2$ are the characters of $chevron.l x chevron.r$ not having
  $t$ in their kernels, and it follows that $psi_i lr((x))$ is a multiple of
  $sqrt(-1)$, which is impossible. Thus the characters $1,psi_1,psi_2,psi_3$ all
  have $t$ in their kernels, and they all belong to $upright(sans(B))_1(H)$ by
  @case:quaternion-root-four-coherence.

  Now let $psi$ be an irreducible character in $upright(sans(B))_1(H)$ such that
  $t in ker psi$, and suppose that $psi in.not lr({1,psi_1,psi_2,psi_3})$. By
  @case:quaternion-root-four-supported-characters, $psi$ vanishes on
  $sqrt(x)^H=H-chevron.l t chevron.r H_(2')$. It follows that $psi in X_(+)$,
  and hence $psi^* in X_(-)$ by @lem:central-involution-character-star. Then
  $(psi^*,psi^*)=(psi,psi)=1$ and $psi^* lr((1))=psi(1)$, so
  $psi^* in op("Irr") H$. The corresponding central idempotents $epsilon$ and
  $epsilon^* in c(K H)$ satisfy
  $
    epsilon+epsilon^* & =psi(1) abs(H)^(-1) sum_(h in H)
                        (psi(h^(-1))+psi^* lr((h^(-1)))) h \
                      & =psi(1) abs(H)^(-1) sum_(h in H_(2')) 2 psi(h^(-1)) h,
  $
  by the definition of $psi^*$. Since $psi$ vanishes on
  $Q-chevron.l t chevron.r$ and $t in ker psi$, we have $4 divides deg psi$
  (since $psi bar.v_Q$ is a multiple of the regular character of
  $Q slash chevron.l t chevron.r$). Then we obtain $epsilon+epsilon^* in R H$,
  and hence $epsilon+epsilon^*=b_1$, where $b_1$ is the block idempotent in
  $upright(sans(B))_1(H)$ (see @prop:block-idempotent-ordinary-components); but
  this is clearly impossible, since $b_1$ must also have as a summand the
  central idempotent associated with the trivial representation.
]

#corollary[
  $
    X_(+)={c_0 1+c_1 a_1 psi_1+c_2 a_2 psi_2+c_3 a_3 psi_3:
      sum c_i=0,c_i in ZZ}.
  $
] <cor:quaternion-plus-character-lattice>

#proof[
  By @lem:quaternion-centralizer-plus-characters and the definition of $X_(+)$,
  any virtual character $xi in X_(+)$ is a $ZZ$-linear combination of
  $lr({1,a_1 psi_1,a_2 psi_2,a_3 psi_3})$. Moreover, since $xi$ vanishes off
  $chevron.l t chevron.r H_(2')$, we have $xi(x)=0$, and hence $sum c_i=0$ by
  @case:quaternion-root-four-character-values.
]
#source(558)

#lemma[
  $upright(sans(B))_1(H)$ contains exactly three irreducible characters
  $psi_4,psi_5,psi_6$ whose kernels do not contain $t$, and
  $X_(-)=ZZ psi_4+ZZ psi_5+ZZ psi_6$.
] <lem:quaternion-centralizer-minus-characters>

#proof[
  If $psi$ is an irreducible character in $upright(sans(B))_1(H)$ whose kernel
  does not contain $t$, then $psi in.not lr({1,psi_1,psi_2,psi_3})$ by
  @lem:quaternion-centralizer-plus-characters; therefore $psi$ vanishes on
  $(sqrt(x))^H$ by @case:quaternion-root-four-supported-characters, and hence
  $psi in X_(-)$. By @lem:central-involution-character-star, $X_(+)$ and $X_(-)$
  have the same $ZZ$-rank, and the $ZZ$-rank of $X_(+)$ is $3$ by
  @cor:quaternion-plus-character-lattice. The lemma follows from these remarks.
]

#lemma[
  There exist integers $a_4,a_5,a_6=plus.minus 1$ such that (after renumbering)
  we have
  $
    2 a_4 psi_4^* & =1+a_1 psi_1-a_2 psi_2-a_3 psi_3, \
    2 a_5 psi_5^* & =1-a_1 psi_1+a_2 psi_2-a_3 psi_3, \
    2 a_6 psi_6^* & =1-a_1 psi_1-a_2 psi_2+a_3 psi_3.
  $
] <lem:quaternion-character-star-pairings>

#proof[
  We first observe that $lr({2 psi_4,2 psi_5,2 psi_6})$ form a $ZZ$-basis for
  $2 X_(-)$, by @lem:quaternion-centralizer-minus-characters. We also have
  $ (2 psi_i^*,2 psi_j^*)_H=4 delta_(i j), $
  using @lem:central-involution-character-star; since
  $(2 X_(-))^* subset.eq X_(+)$, we obtain
  $
    2 psi_4^*=c_0 1+c_1 a_1 psi_1+c_2 a_2 psi_2+c_3 a_3 psi_3,
    quad sum c_i=0,
  $
  by @cor:quaternion-plus-character-lattice. It is then easily checked that we
  can choose $a_4=plus.minus 1$ so that the first formula in
  @lem:quaternion-character-star-pairings holds. The others are proved
  similarly.
]

By the argument used in the proof of @case:quaternion-root-four-ti, it follows
that $sqrt(t)={g in H:t in chevron.l g chevron.r}$ is a T.I. set in $G$ with
normalizer $H$. Indeed, an element in an intersection with its conjugate by
$h in G$ has unique involution both $t$ and $t^h$, whence $h in H$. The set
satisfies the condition that $g in sqrt(t)$ if and only if $g_2 in sqrt(t)$ (so
we can apply @th:ti-principal-block-induction-isometry).

#lemma[
  Let $"ch"(H,sqrt(t);upright(sans(B))_1(H))$ denote the set of virtual
  characters of $H$ which belong to
  $lr({"cf"(H,sqrt(t);upright(sans(B))_1(H))})$. Then
  $
    & brace.l 1+a_1 psi_1+a_2 psi_2+a_3 psi_3,
      a_2 psi_2+a_3 psi_3+a_4 psi_4, \
    & a_1 psi_1+a_3 psi_3+a_5 psi_5,
      a_1 psi_1+a_2 psi_2+a_6 psi_6 brace.r
  $
  form a $ZZ$-basis of $"ch"(H,sqrt(t);upright(sans(B))_1(H))$.
] <lem:involution-root-principal-character-basis>

#proof[
  Since $sqrt(x) subset sqrt(t)$ and $H-sqrt(t)=H_(2')$, it is straightforward
  to verify that the virtual characters listed above belong to
  $"ch"(H,sqrt(t);upright(sans(B))_1(H))$, using the preceding results. For
  example, $1+a_1 psi_1+a_2 psi_2+a_3 psi_3$ vanishes on
  $H-sqrt(x)^H supset H_(2')$, by @case:quaternion-root-four-coherence. Using
  @lem:quaternion-character-star-pairings we obtain
  $
    (1+a_1 psi_1-a_2 psi_2-a_3 psi_3)_(H_(2'))
    &=2 a_4 psi_4^* bar.v_(H_(2'))=2 a_4 psi_4 bar.v_(H_(2')) \
    &=-2(a_2 psi_2+a_3 psi_3)_(H_(2')).
  $
  #source(559)
  Thus $a_2 psi_2+a_3 psi_3+a_4 psi_4 in "ch"(H,sqrt(t);upright(sans(B))_1(H))$,
  and similarly for the others. These virtual characters span a $ZZ$-submodule
  $T$ of $"ch"(H,sqrt(t);upright(sans(B))_1(H))$ of rank $4$. Since
  $lr({psi_4,psi_5,psi_6})$ are linearly independent on $H_(2')$ by
  @lem:quaternion-centralizer-minus-characters, the map
  $xi |-> xi bar.v_(H_(2'))$ (for $xi$ a virtual character supported on
  $upright(sans(B))_1(H)$) has an image of $ZZ$-rank $>=3$, and contains
  $"ch"(H,sqrt(t);upright(sans(B))_1(H))$ in its kernel. Since the number of
  irreducible characters in $upright(sans(B))_1(H)$ is $7$, the rank of
  $"ch"(H,sqrt(t);upright(sans(B))_1(H))$ is $<=4$. It is easily checked that
  $"ch"(H,sqrt(t);upright(sans(B))_1(H)) slash T$ is torsion-free, and hence
  $"ch"(H,sqrt(t);upright(sans(B))_1(H))=T$ because both sides have the same
  $ZZ$-rank. This completes the proof.
]

We are ready to obtain some precise information about the irreducible characters
belonging to the principal block $upright(sans(B))_1(G)$.

#lemma[
  The characters $lr({1,psi_1,...,psi_6})$ in $upright(sans(B))_1(H)$ are
  coherent (see @def:coherent-principal-block-characters). In fact, there exist
  irreducible characters $lr({1,zeta_1,...,zeta_6})$ in $upright(sans(B))_1(G)$,
  and signs $epsilon_i=plus.minus 1$, such that
  $
    (1+a_1 psi_1+a_2 psi_2+a_3 psi_3)^G
    &=1+epsilon_1 zeta_1+epsilon_2 zeta_2+epsilon_3 zeta_3, \
    (a_2 psi_2+a_3 psi_3+a_4 psi_4)^G
    &=epsilon_2 zeta_2+epsilon_3 zeta_3+epsilon_4 zeta_4, \
    (a_1 psi_1+a_3 psi_3+a_5 psi_5)^G
    &=epsilon_1 zeta_1+epsilon_3 zeta_3+epsilon_5 zeta_5, \
    (a_1 psi_1+a_2 psi_2+a_6 psi_6)^G
    &=epsilon_1 zeta_1+epsilon_2 zeta_2+epsilon_6 zeta_6.
  $
] <lem:quaternion-involution-root-coherence>

#proof[
  This result follows easily from @lem:involution-root-principal-character-basis
  and the Isometry Theorem @th:ti-principal-block-induction-isometry. For
  example, let
  $ theta_1=(1+a_1 psi_1+a_2 psi_2+a_3 psi_3)^G. $
  Then $(theta_1,theta_1)=4$ by @th:ti-principal-block-induction-isometry, and
  $(theta_1,1_G)=1$. Therefore there exist irreducible characters
  $lr({zeta_1,zeta_2,zeta_3})$ in $upright(sans(B))_1(G)$ such that the first
  statement of the lemma holds, for suitably chosen $epsilon_i=plus.minus 1$.
  Using @th:ti-principal-block-induction-isometry again, we conclude that
  $theta_2=(a_2 psi_2+a_3 psi_3+a_4 psi_4)^G$ has norm $3$ and that
  $(theta_1,theta_2)=2$. This yields another irreducible character
  $zeta_4 in upright(sans(B))_1(G)$ such that the first two relations hold.
  Continuing in this way, we construct characters in $upright(sans(B))_1(G)$
  satisfying the assertions of the lemma. To verify that
  $lr({1,psi_1,...,psi_6})$ are coherent, we use what has already been shown,
  and the explicit $ZZ$-basis of $"ch"(H,sqrt(t);upright(sans(B))_1(H))$ given
  in @lem:involution-root-principal-character-basis. This completes the proof.
]

#corollary[
  We have
  $
    epsilon_i zeta_i bar.v_(sqrt(t))=a_i psi_i bar.v_(sqrt(t))
    quad "for" 1<=i<=6.
  $
] <cor:quaternion-involution-root-character-values>

This follows from @th:coherent-principal-block-character-correspondence, since
coherence has been established in @lem:quaternion-involution-root-coherence. In
the notation of @th:coherent-principal-block-character-correspondence, we have
for each $i$, $1<=i<=6$,
$ a_i psi_i |-> epsilon'_i a_i zeta_i quad "with" epsilon'_i a_i=epsilon_i. $
#source(560)
Thus
$
  zeta_i bar.v_(sqrt(t))=epsilon'_i psi_i bar.v_(sqrt(t))
  ==>epsilon_i zeta_i bar.v_(sqrt(t))=
  epsilon_i epsilon'_i psi_i bar.v_(sqrt(t))=a_i psi_i bar.v_(sqrt(t)),
$
as required.

#proof(head: emph[Proof of the Brauer–Suzuki Theorem
  @th:brauer-suzuki-quaternion-eight.])[
  Let $frak(C)$ be the conjugacy class in $G$ containing $t$, and let
  $C=sum_(x in frak(C)) x$ be the corresponding class sum. We first prove that
  $ frak(C)^2 inter sqrt(t)=emptyset. $ <eq:involution-class-products-no-roots>
  Otherwise, there exist $u,v in frak(C)$ with $t in chevron.l u v chevron.r$.
  It is easily checked that $chevron.l u,v chevron.r$ is a dihedral group, with
  $chevron.l u v chevron.r$ a cyclic subgroup of index $2$. Since
  $t in chevron.l u v chevron.r$, $4 divides abs(chevron.l u "," v chevron.r)$
  and $chevron.l u,v chevron.r$ contains a Klein $4$-group, which is impossible
  because the Sylow $2$-subgroup of $G$ is a quaternion group.

  Let $theta=a_2 psi_2+a_3 psi_3+a_4 psi_4$. Then
  $theta^G in "cf"(G,sqrt(t)^G;upright(sans(B))_1(G))$ and hence
  $theta^G lr((C^2))=0$ by @eq:involution-class-products-no-roots. Since
  $theta^G=epsilon_2 zeta_2+epsilon_3 zeta_3+epsilon_4 zeta_4$ by
  @lem:quaternion-involution-root-coherence, we obtain
  $
    epsilon_2 zeta_2 lr((C^2))+epsilon_3 zeta_3 lr((C^2))
    +epsilon_4 zeta_4 lr((C^2))=0,
  $
  and hence, using the central characters $omega_i$ associated with the
  $zeta_i$,
  $
    0 & =epsilon_2 zeta_2 lr((1)) frac(zeta_2 lr((C^2)), zeta_2 lr((1)))
        +epsilon_3 zeta_3 lr((1)) frac(zeta_3 lr((C^2)), zeta_3 lr((1)))
        +epsilon_4 zeta_4 lr((1)) frac(zeta_4 lr((C^2)), zeta_4 lr((1))) \
      & =epsilon_2 zeta_2 lr((1)) frac(zeta_2 lr((C))^2, zeta_2 lr((1))^2)
        +epsilon_3 zeta_3 lr((1)) frac(zeta_3 lr((C))^2, zeta_3 lr((1))^2)
        +epsilon_4 zeta_4 lr((1)) frac(zeta_4 lr((C))^2, zeta_4 lr((1))^2) \
      & =abs(frak(C))^2 lr(
          (
            frac(epsilon_2 zeta_2 lr((t))^2, zeta_2 lr((1)))
            +frac(epsilon_3 zeta_3 lr((t))^2, zeta_3 lr((1)))
            +frac(epsilon_4 zeta_4 lr((t))^2, zeta_4 lr((1)))
          )
        ).
  $
  Now $1+a_1 psi_1+a_2 psi_2+a_3 psi_3=
  (tilde(1)+tilde(lambda)_1-tilde(lambda)_2-tilde(lambda)_3)^H$ vanishes on $t$
  by @case:quaternion-root-four-induced-generator, so
  $
    2 a_4 psi_4 lr((t)) & =-2 a_4 psi_4^* lr((t))
                          =-(1+a_1 psi_1-a_2 psi_2-a_3 psi_3)(t) \
                        & =2 a_2 psi_2 lr((t))+2 a_3 psi_3 lr((t)),
  $
  using @lem:quaternion-character-star-pairings. Since
  $epsilon_i zeta_i bar.v_(sqrt(t))=a_i psi_i bar.v_(sqrt(t))$ by
  @cor:quaternion-involution-root-character-values, we obtain
  $ (epsilon_2 zeta_2+epsilon_3 zeta_3-epsilon_4 zeta_4)(t)=0. $
  Moreover $epsilon_2 zeta_2 lr((1))+epsilon_3 zeta_3 lr((1))
  +epsilon_4 zeta_4 lr((1))=0$ since $theta^G$ vanishes off $sqrt(t)^G$.
  Combining the preceding results, we have
  $
    frac(epsilon_2 zeta_2 lr((t))^2, epsilon_2 zeta_2 lr((1)))
    +frac(epsilon_3 zeta_3 lr((t))^2, epsilon_3 zeta_3 lr((1)))
    -frac(
      (epsilon_2 zeta_2 lr((t))+epsilon_3 zeta_3 lr((t)))^2,
      epsilon_2 zeta_2 lr((1))+epsilon_3 zeta_3 lr((1))
    )=0,
  $
  where the denominators are nonzero by the preceding degree relation. Clearing
  them gives the square of the following determinant, and hence
  $
    epsilon_2 zeta_2 lr((t)) epsilon_3 zeta_3 lr((1))
    -epsilon_3 zeta_3 lr((t)) epsilon_2 zeta_2 lr((1))=0.
  $
  #source(561)
  Therefore
  $ zeta_2 lr((t)) zeta_3 lr((1))-zeta_3 lr((t)) zeta_2 lr((1))=0. $
  Similarly we obtain
  $ zeta_3 lr((t)) zeta_1 lr((1))-zeta_3 lr((1)) zeta_1 lr((t))=0. $
  It follows that, for some constant $d$, we have
  $ zeta_i lr((t))=d zeta_i lr((1)), quad i=1,2,3. $
  Since
  $
    1+epsilon_1 zeta_1+epsilon_2 zeta_2+epsilon_3 zeta_3
    &=(1+a_1 psi_1+a_2 psi_2+a_3 psi_3)^G \
    &=(tilde(1)+tilde(lambda)_1-tilde(lambda)_2-tilde(lambda)_3)^G
  $
  vanishes outside $(sqrt(x))^G$, and hence at $1$ and $t$, we have
  $
    1+epsilon_1 zeta_1 lr((1))+epsilon_2 zeta_2 lr((1))
    +epsilon_3 zeta_3 lr((1))=0
  $
  and
  $
    1+d(epsilon_1 zeta_1 lr((1))+epsilon_2 zeta_2 lr((1))
      +epsilon_3 zeta_3 lr((1)))=0.
  $
  Therefore $d=1$, so $t in ker zeta_1$, and $N=ker zeta_1$ is a normal subgroup
  of $G$ containing $t$. Moreover, $N !=G$ since $zeta_1 !=1_G$. This proves
  that $G$ is not a counterexample, and we have reached a contradiction,
  finishing the proof.
]

=== Glauberman’s $Z^*$-Theorem <ss:glauberman-z-star>

The Brauer–Suzuki Theorem (§~@i:ss:brauer-suzuki-generalized-quaternion and
§~@ss:brauer-suzuki-quaternion-sylow) states that a finite group $G$, whose
Sylow $2$-subgroups are quaternion or generalized quaternion groups, has a
proper normal subgroup containing the unique involution in a given Sylow
$2$-subgroup. Glauberman @bib:Glauberman1966 proved a far-reaching
generalization of the Brauer–Suzuki Theorem, called the $Z^*$-theorem, which has
played a crucial part in the proofs of a number of results related to the
classification of the finite simple groups.

In this subsection we shall give a proof of the $Z^*$-theorem, based on the
lectures of Dade @bib:Dade1971a. The main step is another application of blocks
of characters to produce proper normal subgroups.

Let $G$ be a finite group. We let $Z^* lr((G))$ denote the unique normal
subgroup containing $O_(2') lr((G))$ such that
$Z^* lr((G)) slash O_(2') lr((G))=Z(G slash O_(2') lr((G)))$, the center of
$G slash O_(2') lr((G))$.

#theorem(name: [Glauberman’s $Z^*$-Theorem])[
  Let $t$ be an involution in a finite group $G$, such that some Sylow
  $2$-subgroup $S$ of $G$ contains $t$ but no other conjugates of $t$; in other
  words $frak(C) inter S={t}$ where $frak(C)$ is the conjugacy class containing
  $t$. Then $t in Z^* lr((G))$.
] <th:glauberman-z-star>
#idx("Glauberman's $Z^*$-Theorem", target: [@th:glauberman-z-star])
#source(562)

The Brauer–Suzuki Theorem is a special case of the $Z^*$-theorem, and is used in
an essential way in the first part of the proof of the $Z^*$-theorem. The rest
of the subsection is devoted to a proof of the $Z^*$-theorem. As in
§~@ss:brauer-suzuki-quaternion-sylow, we fix a $2$-modular system $(K,R,k)$ such
that $"char" K=0$ and $K$ is sufficiently large relative to $G$.

To begin the proof, let $G$ be a minimal counterexample to the $Z^*$-theorem,
and let $S$ be a Sylow $2$-subgroup of $G$. If $t$ is the given involution in
$S$, then $S$ contains another involution $u !=t$. Otherwise, $S$ contains a
unique involution, and it is not difficult to prove that in this case $S$ is
either cyclic or generalized quaternion. The first possibility is ruled out by
Burnside’s Transfer Theorem @i:cor:cyclic-sylow-two-normal-complement, and the
second by the Brauer–Suzuki Theorem (@i:th:brauer-suzuki-generalized-quaternion
and @th:brauer-suzuki-quaternion-eight).

#case-list(
  numbering: "Step 1.",
  [#case[Let $h,g in G$, and assume that $chevron.l t^h,t^g chevron.r$ is a
      $2$-group. Then $t^h=t^g$. Moreover for arbitrary $g in G$,
      $chevron.l t,u^g chevron.r$ is dihedral of order $4 q$, for $q$ an odd
      number, where $u$ is an involution in $S$ different from $t$. The first
      statement holds since $t^h !=t^g$ implies that
      $chevron.l t^h,t^g chevron.r$ is contained in a conjugate of $S$, which
      contradicts the hypothesis of the $Z^*$-theorem. For the second statement,
      we have $t !=u$ in $S$, so $t eq.not_G u$ and $u^g !=t$. Then
      $chevron.l t,u^g chevron.r$ is a dihedral group of order $2^a q$, for $q$
      odd. If $a=1$, then $t=_G u^g$, contrary to assumption. If $a>2$, then a
      Sylow $2$-group of $chevron.l t,u^g chevron.r$ is dihedral of order $2^a$,
      and does not have $t$ in the center. We then reach a contradiction, as in
      the proof of the first statement.]
    <case:z-star-involution-dihedral-fusion>],
  [#case[We shall prove that there exists no proper normal subgroup $N ⊴ G$ such
      that $t in N$. First of all, since $G$ is a minimal counterexample, we
      have $O_(2') lr((G))=1$. Now suppose that $t in N$ for some subgroup
      $N ⊴ G$. Then $O_(2') lr((N))$ is a characteristic subgroup of $N$, and
      $O_(2') lr((N)) <= O_(2') lr((G))=1$. Therefore $S inter N$ is a Sylow
      $2$-subgroup of $N$, and $S inter N$ contains $t$ and no other
      $N$-conjugate of $t$. By the minimality of $G$, and the fact that
      $O_(2') lr((N))=1$, we obtain $t in Z^* lr((N))=Z(N)$. Then $t$ belongs to
      a Sylow $2$-group of $Z(N)$. If $g in G$, then $t$ and $t^g$ commute since
      both are in $Z(N)$, so $chevron.l t,t^g chevron.r$ is a $2$-group, and
      $t=t^g$ by @case:z-star-involution-dihedral-fusion. Since $g in G$ is
      arbitrary, we obtain $t in Z(G)$, which is impossible.]
    <case:z-star-no-proper-normal-containing-involution>],
  [#case[Now let $H$ be any proper subgroup of $G$ containing $t$. We claim that
    $t in Z^* lr((H))$, and begin by checking that $H$ satisfies the hypotheses
    of the $Z^*$-theorem. Let $T$ be a Sylow $2$-group of $H$ containing $t$. If
    $t$ and $t^h$ belong to $T$, for some $h in H$, then
    $chevron.l t,t^h chevron.r$ is a $2$-group, and $t=t^h$ by
    @case:z-star-involution-dihedral-fusion. Thus we can apply the $Z^*$-theorem
    to $H$, in view of the minimality of $G$, and obtain
    $t in Z^* lr((H))$.] <case:z-star-proper-subgroups>],
  [#case[Let $t,u$ be distinct involutions in $S$, and let $zeta$ be an
      irreducible character in the principal block $upright(sans(B))_1(G)$. We
      shall prove that $zeta(t(u^g))=zeta(t u)$ for all $g in G$.

      First assume that $chevron.l t,u^g chevron.r$ is abelian. We may assume
      that $S<G$, so $t in Z^* lr((S))$ by @case:z-star-proper-subgroups. Then
      $t in Z(S)$, and $chevron.l t,u chevron.r$ is abelian. Then $t$ and $t^g$
      both belong to $C_G lr((u^g))$. By Sylow’s Theorem, there exists
      $h in C_G lr((u^g))$ such that $t$ and $t^(g h)$ belong to the same Sylow
      $2$-subgroup of $C_G lr((u^g))$. Then $chevron.l t,t^(g h) chevron.r$ is a
      $2$-group, and $t=t^(g h)$ by @case:z-star-involution-dihedral-fusion.
      Moreover, $t u^g=t^(g h) u^g=(t u)^(g h)$ since $h in C_G lr((u^g))$. It
      follows that $zeta(t u^g)=zeta(t u)$ for all $g in G$ and
      $zeta in op("Irr") G$.
      #source(563)

      A delicate situation occurs when $chevron.l t,u^g chevron.r$ is not
      abelian. In this case, $chevron.l t,u^g chevron.r$ is dihedral of order
      $4 q$, with $q$ odd, by @case:z-star-involution-dihedral-fusion. Moreover
      $chevron.l t u^g chevron.r$ is cyclic of index $2$ in
      $chevron.l t,u^g chevron.r$, and hence contains an involution
      $v in Z chevron.l t,u^g chevron.r$.

      We prove next that $H=C_G lr((v))<G$. Otherwise, $v in Z(G)$, and it is
      easily checked that $G slash chevron.l v chevron.r$ satisfies the
      hypotheses of the $Z^*$-theorem. Then
      $t chevron.l v chevron.r in Z^* lr((G slash chevron.l v chevron.r))$ by
      minimality of $G$. If $N ⊴ G$ is the inverse image of
      $O_(2') lr((G slash chevron.l v chevron.r))$, then
      $N slash chevron.l v chevron.r$ has odd order and
      $N=N_1 chevron.l v chevron.r$ for $N_1=O_(2') lr((N))$ (by a special case
      of the Schur–Zassenhaus Theorem @i:th:schur-zassenhaus). Then $N_1=1$
      since $O_(2') lr((G))=1$, and hence
      $t chevron.l v chevron.r in Z(G slash chevron.l v chevron.r)$. This means
      that $chevron.l t,v chevron.r ⊴ G$, and hence $chevron.l t,v chevron.r=G$
      by @case:z-star-no-proper-normal-containing-involution. Thus $t in Z(G)$
      and we have reached a contradiction.

      Since $H=C_G lr((v))<G$ and $t in H$, we have $t in Z^* lr((H))$ by
      @case:z-star-proper-subgroups. We also have $t u^g in H$ and $u^g in H$.
      The image of $chevron.l t,u^g chevron.r$ in $H slash O_(2') lr((H))$ is
      dihedral, and $t O_(2') lr((H)) in Z(H slash O_(2') lr((H)))$. Then
      $(t u^g)^2 in O_(2') lr((H))$, and the image of
      $chevron.l t,u^g chevron.r$ in $H slash O_(2') lr((H))$ is a Klein
      $4$-group.

      Now let $zeta in upright(sans(B))_1(G)$. We have, for
      $x in O_(2') lr((H))$,
      $
        zeta(v x) & =sum_(xi_j in upright(sans(B))_1(H)) a_j xi_j lr((v x)) \
                  & =sum a_j xi_j lr((v))=zeta(v),
      $
      using @th:principal-block-character-kernel and Brauer’s Second and Third
      Main Theorems @th:brauer-second-main-first-form and
      @th:brauer-third-main-theorem. Now $t u^g equiv v (mod O_(2') lr((H)))$,
      since $(t u^g)^2 in O_(2') lr((H))$ and $chevron.l t u^g chevron.r=
      ⟨ v ⟩ chevron.l (t u^g)^2 chevron.r$. Then $zeta(t u^g)=zeta(v)$ for
      $zeta in upright(sans(B))_1(G)$. The Sylow $2$-subgroup of
      $chevron.l t,u^g chevron.r$ containing $t$ is just
      $chevron.l t,v chevron.r$, so $t v$ is an involution commuting with $t$,
      and $t v=(u^g)^z$ for some $z in chevron.l t,u^g chevron.r$. Then
      $chevron.l t,u^(g z) chevron.r$ is abelian, and $v=t^2 v=t u^(g z)$ so
      $ zeta(v)=zeta(t u^(g z))=zeta(t u) $
      by the proof of the first part of this step. Combining our results, we
      obtain $zeta(t u^g)=zeta(v)=zeta(t u)$, as required.]
    <case:z-star-principal-character-involution-products>],
  [#case[Let $t,u$ be distinct involutions in $S$, and let
      $frak(C)_t,frak(C)_u$, and $C_t,C_u$ be the conjugacy classes and class
      sums defined by them. For all $zeta in upright(sans(B))_1(G)$ we have
      $
        frac(zeta(C_t C_u), zeta(1))=
        lr((frac(zeta(C_t), zeta(1)) frac(zeta(C_u), zeta(1))))
      $
      so
      $ zeta(1) zeta(C_t C_u)=zeta(C_t) zeta(C_u). $
      Now
      $ C_t C_u=sum t^g u^h=sum (t u^(h g^(-1)))^g $
      so, using @case:z-star-principal-character-involution-products, we obtain
      $
        zeta(1) abs(frak(C)_t) abs(frak(C)_u) zeta(t u)
        =abs(frak(C)_t) abs(frak(C)_u) zeta(t) zeta(u).
      $
      On the other hand, $t in Z(S)$ by the hypothesis of the $Z^*$-theorem, so
      $t u$ is an involution in $S$ different from $t$, and we have
      $ zeta(1) zeta(u)=zeta(t) zeta(t u) $
      #source(564)
      by the argument used above. Then
      $ zeta(t)^2 zeta(u)=zeta(1) zeta(t) zeta(t u)=zeta(1)^2 zeta(u). $
      If $zeta(u) !=0$, then $zeta(t)=plus.minus zeta(1)$ and
      $t dot ker zeta in Z(G slash ker zeta)$. Let $N$ be the intersection of
      the kernels of characters $zeta in upright(sans(B))_1(G)$ such that
      $zeta(u) !=0$ for some involution $u$ in $S-{t}$. Then
      $t N in Z(G slash N)$.

      In order to prove the $Z^*$-theorem, it is sufficient to prove that $N$
      contains no involutions, since that implies that $N=1$ and $t in Z(G)$, in
      view of the fact that $O_(2') lr((G))=1$. In fact, it suffices to show
      that $N$ contains no involutions belonging to $S$. First assume that $N$
      contains an involution $u !=t$, with $u in S$. By the $p$-Section
      Orthogonality Theorem @th:block-p-section-orthogonality, we obtain
      $
        0 & =sum_(zeta in upright(sans(B))_1(G)) zeta(u) zeta(1)
            =sum_(zeta in upright(sans(B))_1(G),zeta(u) !=0) zeta(u) zeta(1) \
          & =sum_(zeta in upright(sans(B))_1(G),zeta(u) !=0) zeta(1)^2
      $
      by the definition of $N$. This is a contradiction, since the trivial
      character $zeta^1 in upright(sans(B))_1(G)$ and $zeta^1 lr((u)) !=0$.

      Now suppose $t in N$. Then $N=G$ by
      @case:z-star-no-proper-normal-containing-involution, and hence $N$
      contains an involution $u in S$ such that $u !=t$, since $S$ has that
      property. But we have just shown that this is impossible. Therefore $N$
      contains no involutions, so $N <= O_(2') lr((G))=1$, and therefore
      $t in Z(G)$, completing the proof.]
    <case:z-star-central-quotient-kernel>],
)
