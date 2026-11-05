#import "main-defs.typ": *
#import "note-layout.typ": reference-data
#import "main-defs.typ": number-text as reference-number-text
#import "statements.typ": *
#import "diagrams/76-artin.typ": *

== The Artin Exponent
<sec:artin-exponent>

Throughout this section, let $G$ be a finite group of order $n$, and let
$cal(C)(=cal(C)(G))$ be the set of cyclic subgroups of $G$. As usual,
$"ch" QQ G$ denotes the ring of virtual characters afforded by $QQ G$-modules.
By @i:lem:class-function-induction-product,
$sum_(C in cal(C)) upright("ind")_C^G "ch" QQ C$ is an ideal in $"ch" QQ G$. We
define the #idx("Artin cokernel")_Artin cokernel_ of $G$, denoted by $A C(G)$,
as follows:
$
  A C(G)="Artin cokernel of" G
  =("ch" QQ G) slash (sum_(C in cal(C)) upright("ind")_C^G "ch" QQ C).
$
<eq:artin-cokernel-definition>
Then $A C(G)$ is a commutative ring with identity element. The characteristic of
$A C(G)$ is by definition the #idx("Artin exponent")_Artin exponent_ #idx(
  "A(G)",
)$A(G)$ of $G$. Thus, $A(G)$ is the least positive integer $m$ such that
$ m dot "ch" QQ G subset.eq sum_(C in cal(C)) upright("ind")_C^G "ch" QQ C, $
<eq:artin-exponent-annihilator>
and $A(G)$ divides any $m$ for which @eq:artin-exponent-annihilator is valid.
Now let $phi$ be a rational-valued character of $G$. By Solomon's Theorem
@th:solomon-subgroup-permutation-character-induction, we may write
$ n phi=sum_(C in cal(C)) a_C (1_C)^G quad "with coefficients" a_C in ZZ. $
<eq:solomon-rational-character-multiple>
It follows that @eq:artin-exponent-annihilator holds when $m$ is replaced by
$n$, and consequently
$ A(G) "divides" n, quad "where" n=|G|. $
<eq:artin-exponent-divides-order>
We note also that since $sum_(C in cal(C)) upright("ind")_C^G "ch" QQ C$ is an
ideal of $"ch" QQ G$, $A(G)$ is the least positive $m$ such that $m dot 1_G$ is
a $ZZ$-linear combination of characters induced from rational characters of
cyclic subgroups of $G$.

The importance of the Artin exponent stems from the theory of Frobenius functors
and Frobenius modules. By @i:prop:grothendieck-character-ring we have
$"ch" QQ G ≅ G_0(QQ G)$, and so $"ch" QQ G$ is a Frobenius functor. We have
shown in §~@ss:class-group-frobenius that the locally free class group
$"Cl" ZZ G$, the kernel group $D(ZZ G)$, and the projective class group
$K_0(ZZ G)$ are Frobenius modules over $G_0(QQ G)$. From
@cor:frobenius-induction-annihilators we thus obtain:

#proposition[
  Let $A(G)$ be the Artin exponent of $G$, and let $M(G)$ be any Frobenius
  module over the Frobenius functor $"ch" QQ G$.
  #case-list(
    numbering: "(i)",
    [#case[Let $x in M(G)$ be such that $upright("res")_C^G x=0$ for all
        $C in cal(C)$. Then $A(G)dot x=0$.]
      <case:artin-exponent-cyclic-restriction-kernel>],
    [#case[We have
        $ A(G)dot M(G) subset.eq sum_(C in cal(C)) upright("ind")_C^G M(C). $]
      <case:artin-exponent-cyclic-induction-image>],
  )
]<prop:artin-exponent-frobenius-modules>

#source(799)
In particular, these results hold when $M(G)$ is chosen to be $"Cl" ZZ G$,
$D(ZZ G)$, or $K_0(ZZ G)$.

This proposition plays a key role in the proof of Ullom's Theorem
@th:artin-exponent-annihilates-swan-subgroup, which asserts that $A(G)$
annihilates the Swan subgroup $T(G)$ defined in §~@ss:swan-subgroup. On the
other hand, taking for granted the values of $A(G)$ for $G$ a $p$-group,
Taylor's Theorem @th:taylor-swan-subgroup-order shows that for $p$ odd,
$|T(G)|=A(G)$ for each $p$-group $G$. Further, for $p=2$, $|T(G)|=A(G) slash 2$
apart from a few exceptional cases.

In computations of the Artin exponent $A(G)$, it is often useful to work with
permutation characters $(1_C)^G$ rather than arbitrary rational characters of
$G$. The justification for this procedure comes from the following key result of
Lam~@bib:Lam1968b, which is based on an earlier argument by Swan~@bib:Swan1963.

#proposition[
  For $G$ a cyclic group,
  $ "ch" QQ G=sum_(C≤G) ZZ(1_C)^G, $
  where $C$ ranges over all subgroups of $G$.
]<prop:cyclic-rational-characters-permutation-lattice>

#proof[
  The result is trivial for $|G|=1$. Next, let $G=chevron.l x chevron.r$ be a
  cyclic $p$-group of order $p^m$, where $p$ is prime and $m≥1$. The simple
  $QQ G$-modules are given by $K_r=QQ[x] slash (Phi_(p^r) lr((x)))$, $0≤r≤m$,
  where $Phi_(p^r) lr((x))$ denotes the cyclotomic polynomial of order $p^r$.
  For $r≥1$,
  $ (x^(p^r)-1)=(x^(p^(r-1))-1)Phi_(p^r) lr((x)), $
  and thus we obtain
  $ QQ[x] slash (x^(p^r)-1) ≅ K_r plus.o QQ[x] slash (x^(p^(r-1))-1). $
  However, $QQ[x] slash (x^(p^r)-1)$ affords the permutation character $(1_C)^G$
  of $G$, where $C≤G$ has index $p^r$. It follows from the above that the
  character of $G$ afforded by $K_r$ is a difference of permutation characters
  for $r≥1$. On the other hand, $K_0$ affords the trivial character $1_G$. This
  completes the proof when $G$ is a cyclic $p$-group.

  Now let $G$ be arbitrary, and use induction on $|G|$. We may assume that
  $G=G_1 times G_2$, where $G_1$ and $G_2$ are nontrivial cyclic groups of
  relatively prime orders, and where the proposition holds for both $G_1$ and
  $G_2$. Each simple $QQ G$-module is a cyclotomic field of the form
  $L_1 times.o_QQ L_2$, with $L_i$ a simple $QQ G_i$-module, $i=1,2$. If $L_i$
  affords the irreducible character $phi_i$ of $G_i$, then $L_1 times.o L_2$
  affords the character $phi_1 times phi_2$ of $G_1 times G_2$. Let $C_i$ range
  over the subgroups of $G_i$, $i=1,2$. The proposition then holds for $G$, by
  virtue of the obvious formula
  $
    (1_(C_1))^(G_1) times (1_(C_2))^(G_2) ≅
    (1_(C_1 times C_2))^(G_1 times G_2).
  $
  <eq:product-permutation-character>
  This completes the proof.
]

#source(800)
Returning to arbitrary groups $G$, we note next that conjugate subgroups of $G$
yield the same induced characters, by @i:lem:conjugate-modules(ii). Hence in all
of our previous remarks, we may replace $cal(C)$ by $cal(C)_0$, where $cal(C)_0$
is a full set of nonconjugate cyclic subgroups of $G$. By Exercise
@i:exc:rational-simple-modules-cyclic-subgroups, the permutation characters
${(1_C)^G:C in cal(C)_0}$ are linearly independent over $QQ$, and span the space
of $QQ$-valued class functions on $G$ that are constant on rational conjugacy
classes. Thus, in expressing a virtual character $phi in "ch" QQ G$ as a linear
combination of characters ${(1_C)^G:C in cal(C)_0}$, the coefficients are
rational numbers that are uniquely determined by $phi$. Further, by the tensor
identity @i:lem:class-function-induction-product, @eq:artin-exponent-annihilator
holds if and only if $m dot 1_G$ lies in the right hand expression in
@eq:artin-exponent-annihilator. From these remarks, together with
@prop:cyclic-rational-characters-permutation-lattice, we obtain at once:

#corollary[
  #idx("Lam's Theorem")
  Let $G$ be an arbitrary finite group, and $cal(C)_0$ a full set of
  nonconjugate cyclic subgroups of $G$. Then $A(G)$ is the smallest positive
  integer $m$ such that
  $ m dot 1_G=sum_(C in cal(C)_0) a_C (1_C)^G quad "with each" a_C in ZZ. $
  <eq:artin-exponent-permutation-identity>
]<cor:artin-exponent-permutation-identity>

#remarks(numbered: true)[
  #case-list(
    numbering: "(i)",
    [#case[If $m$ is a positive integer, and
        @eq:artin-exponent-permutation-identity holds for some set of integers
        ${a_C}$ with G.C.D. $1$, then necessarily $m=A(G)$.]
      <case:artin-exponent-primitive-coefficients>],
    [#case[Given a group $G$, one can compute the characters ${(1_C)^G}$
        explicitly, and then use @cor:artin-exponent-permutation-identity to
        determine $A(G)$. For example, let $G=S_3$, and take
        $cal(C)_0={C_1,C_2,C_3}$, with $C_i$ cyclic of order $i$. It is easily
        verified that
        $ 2dot 1_G=-(1_(C_1))^G+2(1_(C_2))^G+(1_(C_3))^G, $
        and therefore $A(G)=2$. For other examples, see Exercises
        @exc:elementary-abelian-artin-exponent,
        @exc:prime-product-artin-exponent.]
      <case:symmetric-three-artin-exponent>],
  )
]<rem:artin-exponent-computation>

We turn next to some functorial properties of the Artin exponent, all due to
Lam~@bib:Lam1968b. We use repeatedly the fact that for $m in ZZ$,
$
  m dot 1_G in sum_(C≤G) ZZ dot (1_C)^G
  quad "if and only if" quad A(G) "divides" m,
$
<eq:artin-exponent-permutation-divisibility>
where $C$ ranges over all cyclic subgroups of $G$. Using this, we show:

#proposition[
  #case-list(
    numbering: "(i)",
    [#case[If $H≤G$, then $A(H)$ divides $A(G)$.]
      <case:artin-exponent-subgroup-divisibility>],
    [#case[If $overline(G)$ is a homomorphic image of $G$, then $A(overline(G))$
        divides $A(G)$.]
      <case:artin-exponent-quotient-divisibility>],
    [#case[$A(G_1 times G_2)=A(G_1)A(G_2)$ if $(|G_1|,|G_2|)=1$.]
      <case:artin-exponent-coprime-product>],
  )
]<prop:artin-exponent-functorial-properties>

#proof[
  Part~@case:artin-exponent-subgroup-divisibility. We may write
  $ A(G)dot 1_G=sum_(C≤G) a_C (1_C)^G, quad a_C in ZZ. $
  <eq:artin-exponent-integral-cyclic-induction>
  #source(801)
  For $H≤G$, this gives
  $ A(G)dot 1_H=sum_C a_C upright("res")_H^G (1_C)^G. $
  But $upright("res")_H^G (1_C)^G$ is a sum of permutation characters of $H$, by
  Mackey's Subgroup Theorem @i:th:mackey-subgroup. Therefore $A(H)$ divides
  $A(G)$.

  Part~@case:artin-exponent-quotient-divisibility. The homomorphism
  $G arrow overline(G)$ extends to a surjection of rings
  $QQ G arrow QQ overline(G)$, inducing a surjection
  $G_0(QQ G) arrow G_0(QQ overline(G))$ of Grothendieck groups. Each cyclic
  subgroup $C≤G$ maps onto a cyclic subgroup $overline(C)≤overline(G)$, and the
  diagram
  #artin-quotient-square()
  commutes. It follows that the Artin cokernel of $G$ maps onto that of
  $overline(G)$, and therefore $A(G)$ annihilates the Artin cokernel of
  $overline(G)$. This implies that $A(G)$ is a multiple of $A(overline(G))$, as
  claimed.

  Part~@case:artin-exponent-coprime-product. $A(G_1)A(G_2)$ divides
  $A(G_1 times G_2)$, by part~@case:artin-exponent-subgroup-divisibility. On the
  other hand from @eq:product-permutation-character, and
  @eq:artin-exponent-integral-cyclic-induction for $G_1$ and $G_2$, we deduce
  that $A(G_1 times G_2)$ divides $A(G_1)A(G_2)$. This completes the proof of
  the proposition.
]

It is obvious that if $G$ is cyclic, then $A(G)=1$. As shown by
Lam~@bib:Lam1968b, the converse also holds, and thus we have:

#theorem[
  The Artin exponent $A(G)=1$ if and only if $G$ is cyclic.
]<th:artin-exponent-one-cyclic>

#proof[
  Assume $A(G)=1$, so by @case:artin-exponent-subgroup-divisibility[#context {
    reference-number-text(
      "("
        + reference-data(<prop:artin-exponent-functorial-properties>).text
        + reference-data(<case:artin-exponent-subgroup-divisibility>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }], $A(P)=1$ for each Sylow $p$-subgroup $P$ of $G$. Therefore the exponent of
  $P$ equals the order of $P$, by Exercise
  @exc:group-exponent-artin-divisibility, and so $P$ is cyclic. It follows that
  $G$ must be metacyclic (see Hall~@bib:Hall1959, Th. 9.4.3), and so there
  exists a normal series
  $ 1≤H⊴G, quad "with" H,G slash H "cyclic". $
  Since $[G,G]≤H$, each $H_0$ with $H≤H_0≤G$ is also normal in $G$. Increasing
  $H$ if need be, we may assume that $H$ is a maximal cyclic subgroup of $G$.
  Now consider the equation
  $ A(G)1_G=a_H (1_H)^G+sum_C a_C (1_C)^G, $
  where the coefficients $a_H,a_C$ are integers, and where $C$ ranges over some
  set of cyclic subgroups of $G$, none of which contains a conjugate of $H$.
  Evaluating both sides of the above equation at a generator $h$ of $H$, we
  obtain
  $ A(G)=a_H|N_G lr((H)):H|, $
  since $(1_C)^G lr((h))=0$ for each $C$ above. Since $A(G)=1$ by hypothesis, we
  conclude that $N_G lr((H))=H$, that is, $G=H$. This completes the proof.
]

#source(802)
For noncyclic $p$-groups, where $p$ is an odd prime, the Artin exponent can be
evaluated easily. The next result is due to Lam~@bib:Lam1968b.

#theorem[
  #idx("Lam's Theorem")
  Let $G$ be a noncyclic $p$-group of order $p^m$, where $p$ is an odd prime.
  Then $A(G)=p^(m-1)$.
]<th:odd-p-group-artin-exponent>

#proof[
  By the Artin Induction Theorem @i:th:artin-induction-explicit-coefficients, we
  have
  $
    1_G=sum_(C≤G) a_C (1_C)^G, quad "where"
    a_C=frac(1, abs(G\:C)) sum_(C^*≥C) mu(|C^*:C|).
  $
  <eq:artin-cyclic-induction-coefficients>
  Here, $C$ ranges over all cyclic subgroups of $G$, and $C^*$ over all cyclic
  subgroups of $G$ containing $C$. Let $cal(C)_0$ be a full set of nonconjugate
  cyclic subgroups of $G$. A given $C in cal(C)_0$ has $|G:N_G lr((C))|$
  distinct conjugates, so @eq:artin-cyclic-induction-coefficients becomes
  $
    1_G=sum_(C in cal(C)_0) b_C (1_C)^G, quad "where"
    b_C=frac(1, abs(N_G lr((C))\:C)) sum_(C^*≥C) mu(|C^*:C|).
  $
  <eq:artin-conjugacy-grouped-coefficients>
  Note that since $G$ is a $p$-group, $mu(|C^*:C|)=0$ except when $|C^*:C|=1$ or
  $p$. Of course, $A(G)$ is the least positive integer such that $A(G)b_C in ZZ$
  for each $C in cal(C)_0$.

  We now evaluate $b_1$, corresponding to $C={1}$. Then
  $ b_1=|G|^(-1)(1-k), $
  where $k$ is the number of subgroups of $G$ of order $p$. Since $G$ is
  noncyclic, we may apply Kulakoff's Theorem (see the proof of
  @th:taylor-swan-subgroup-order) to conclude that the number of elements of
  order dividing $p$ in $G$ is a multiple of $p^2$. This gives
  $ k(p-1)+1≡0 quad (mod p^2), quad "whence" k≡p+1 quad (mod p^2). $
  Therefore $b_1=l slash p^(m-1)$ for some $l in ZZ$, where $p∤l$. This shows
  that $p^(m-1)|A(G)$. For each nontrivial cyclic subgroup $C$ of $G$,
  $|N_G lr((C)):C|$ divides $p^(m-1)$, so the coefficient $b_C$ in
  @eq:artin-conjugacy-grouped-coefficients has denominator dividing $p^(m-1)$.
  Together with the value of $b_1$, this shows that $p^(m-1)b_C in ZZ$ for every
  $C in cal(C)_0$. Hence $A(G)$ divides $p^(m-1)$, and the proof is
  complete.#ed-note[
    The original proof cites Exercise @exc:group-exponent-artin-divisibility to
    exclude $A(G)=p^m$, but that exercise gives only the lower divisibility
    $n slash e | A(G)$.
  ]
]

The situation for $2$-groups is somewhat more complicated, and we state the
results without proof (see Lam~@bib:Lam1968b):

#theorem[
  Let $G$ be a group of order $2^m$. Then $A(G)=2^(m-1)$, with the following
  exceptions:

  $A(G)=1$ if $G$ is cyclic.

  $A(G)=2$ if $G$ is a generalized quaternion group (with $m≥3$) or a dihedral
  group (with $m≥2$).

  $A(G)=4$ if $G$ is a semidihedral group#footnote[
    S. Endo pointed out that $A(G)=4$ in this case; Lam gave the incorrect
    formula $A(G)=2$.
  ] (with $m≥4$).
]<th:two-group-artin-exponent>

#source(803)
For arbitrary groups $G$, Lam has shown how to compute $A(G)$, by determining
its $p$-part $A_p lr((G))$ for each prime $p$. The proofs are based on formula
@eq:artin-conjugacy-grouped-coefficients, and are given in detail in
Lam~@bib:Lam1968b. Here, we shall summarize the main results, denoting by $G_p$
a Sylow $p$-subgroup of $G$.

#theorem[
  Let $p$ be an odd prime, and suppose $G$ has a noncyclic Sylow subgroup $G_p$
  of order $p^m$. Then
  #case-list(
    numbering: "(i)",
    [#case[$A_p lr((G))=p^m$ if $G$ contains a cyclic $p'$-group $D$, normalized
      by $G_p$, with $G_p$ acting faithfully by conjugation on
      $D$.]<case:noncyclic-sylow-artin-faithful-action>],
    [#case[$A_p lr((G))=p^(m-1)$ otherwise.]
      <case:noncyclic-sylow-artin-other-action>],
  )
]<th:noncyclic-odd-sylow-artin-exponent>

#corollary[
  Keeping the above notation, $A_p lr((G))=p^(m-1)$ if $G_p⊴G$ or if $G_p$ is
  non-abelian.
]<cor:normal-nonabelian-odd-sylow-artin-exponent>

On the other hand, Lam~@bib:Lam1968b proved:

#theorem[
  Let $p$ be any prime, and suppose $G$ has a cyclic Sylow $p$-subgroup $G_p$.
  Then $A_p lr((G))=p^s$, where $s$ is the smallest nonnegative integer such
  that the following property holds:

  For each $x in G_p$, and each cyclic $p'$-subgroup $D$ of $G$,
  $ x in N_G lr((D)) arrow.r.double x^(p^s) in C_G lr((D)). $
]<th:cyclic-sylow-artin-exponent-action>

#corollary[
  $A_p lr((G))=1$ if and only if
  #case-list(
    numbering: "(i)",
    [#case[$G_p$ is cyclic, and]
      <case:artin-primary-one-cyclic-sylow>],
    [#case[for each $P≤G_p$ and each cyclic $p'$-subgroup $D≤G$, $P$ normalizes
        $D$ if and only if $P$ centralizes $D$.]
      <case:artin-primary-one-normalizer-centralizer>],
  )
]<cor:artin-primary-one-action-criterion>

#corollary[
  Assume $G_p$ cyclic. Then $A_p lr((G))=1$ if any of the following hold:
  #case-list(
    numbering: "(i)",
    [#case[$G_p⊴G$.]<case:artin-primary-one-normal-sylow>],
    [#case[$p∤(q-1)$ for each prime divisor $q$ of $|G|$.]
      <case:artin-primary-one-prime-divisor-condition>],
    [#case[$p$ is the largest prime divisor of $|G|$.]
      <case:artin-primary-one-largest-prime>],
  )
]<cor:cyclic-sylow-artin-primary-one-sufficient>

For further results on the Artin exponent, see Rasmussen~@bib:Rasmussen1974,
@bib:Rasmussen1977.

We turn next to the question of determining the order of the #idx(
  "Artin cokernel",
)Artin cokernel $A C(G)$, rather than its characteristic $A(G)$. Before stating
the result, let us introduce some notation, and review some facts from
§~@sec:schur-index. Let $cal(C)_0$ be a full set of non-conjugate cyclic
subgroups of $G$, say
$ cal(C)_0={C_1,dots,C_s}, quad C_i=chevron.l x_i chevron.r. $
For each $i$, let $phi_i=(1_(C_i))^G$ be the corresponding permutation character
of $G$. We
#source(804)
have seen that these ${phi_i}$ are linearly independent, and there are
inclusions
$ P(G)=plus.o.big_(i=1)^s ZZ phi_i subset.eq "ch" QQ G subset.eq "ch"' QQ G, $
where $"ch"' QQ G$ is the ring of rational-valued characters on $G$. By
definition, $A C(G)=("ch" QQ G) slash P(G)$, and we are trying to calculate
$|"ch" QQ G:P(G)|$.

Let $frak(G)=upright("Gal")(QQ(epsilon) slash QQ)$, where $epsilon$ is a
primitive $n$-th root of $1$, $n=|G|$. Then $frak(G)$ permutes the absolutely
irreducible characters of $G$, and there are $s$ orbits $X_1,dots,X_s$ in
$"Irr" G$ under the action of $frak(G)$. Correspondingly,
$ QQ G ≅ plus.o.big_(i=1)^s A_i, quad A_i="simple component". $
Let $m_i="index of" A_i$; the character of $G$ afforded by a simple $A_i$-module
is given by $m_i psi_i$, with
$ psi_i=sum_(zeta in X_i) zeta, $
and $m_i$ is the Schur index $m_QQ lr((zeta))$ for each $zeta in X_i$. We have
(from §~@sec:schur-index)
$
  "ch"' QQ G=plus.o.big_(i=1)^s ZZ psi_i
  supset.eq "ch" QQ G=plus.o.big_(i=1)^s ZZ m_i psi_i.
$
Thus $|"ch"' QQ G:"ch" QQ G|=product m_i$.

The group $frak(G)$ also acts on the conjugacy classes of $G$. If
$sigma in frak(G)$ is such that $sigma(epsilon)=epsilon^k$, where $(k,n)=1$,
then $sigma$ carries the conjugacy class of a given element $x$ onto the class
of $x^k$. Suppose that the conjugacy classes of $G$, under the action of
$frak(G)$, are partitioned into orbits $Y_1,dots,Y_s$. Each $Y_i$ corresponds to
a family of conjugate cyclic subgroups of $G$, so the number of orbits equals
the number of simple components of $QQ G$. Let $|Y_i|="card" Y_i$, and
$|X_i|="card" X_i$, $1≤i≤s$. Finally, put
$ N_i=N_G lr((C_i)), quad H_i=C_G lr((C_i)), quad 1≤i≤s. $
Keeping all of the above notation, we now give Solomon's formula for the order
of the Artin cokernel $A C(G)$ of $G$.

#theorem[
  #idx("Solomon's Theorem")
  The order of $A C(G)$ is given by the formula
  $
    |A C(G)|^2=v product_(i=1)^s |N_i:C_i|^2 slash (|H_i|m_i^2),
    quad "where" v=product_(i=1)^s |Y_i| slash |X_i|.
  $
]<th:solomon-artin-cokernel-order>

#proof[
  By the preceding discussion, it suffices to show that
  $ |"ch"' QQ G:P(G)|^2=v product_i |N_i:C_i|^2 slash |H_i|, $
  which was proved in §~@ss:solomon-symmetric-group-characters (see Theorem
  @th:solomon-subgroup-permutation-character-induction).
]

#source(805)
At the end of §~@sec:p-adic-logarithms-taylor, we stated without proof a
different version of the formula @case:oliver-artin-cokernel-order for
$|A C(G)|^2$, due to Oliver. We leave it to the reader to verify the equivalence
of Oliver's formula with that of Solomon.

#exercises-heading

#exercise[
  Let $G$ be an elementary abelian $p$-group on $n$ generators, where $p$ is
  prime. Prove that $A(G)=p^(n-1)$.
]<exc:elementary-abelian-artin-exponent>
#hint([@exc:elementary-abelian-artin-exponent])[
  Use @cor:artin-exponent-permutation-identity.
]<hint:elementary-abelian-artin-exponent>

#exercise[
  Let $|G|=p q$, where $p<q$ are primes, and $G$ is not cyclic. Prove that
  $A(G)=p$.
]<exc:prime-product-artin-exponent>
#hint([@exc:prime-product-artin-exponent], caption: [Hint (T. Y. Lam):])[
  We may write $G=C_q ⋊ C_p$. Now compute $(1_C)^G$ for $C$ cyclic of order $1$,
  $p$ and $q$, and use @cor:artin-exponent-permutation-identity.
]<hint:prime-product-artin-exponent>

#exercise[
  Let $G$ be a group of order $n$ and exponent $e$. Then prove that $n slash e$
  divides $A(G)$.
]<exc:group-exponent-artin-divisibility>
#hint([@exc:group-exponent-artin-divisibility])[
  Evaluating both sides of @eq:artin-exponent-integral-cyclic-induction at $1$,
  we obtain
  $ A(G)=sum_C a_C|G:C|. $
  But $n slash e$ divides $|G:C|$ for each cyclic $C≤G$.
]<hint:group-exponent-artin-divisibility>

#exercise[
  Let $cal(H)$ be the set of hyper-elementary subgroups of $G$. Show that
  $ A(G)="L.C.M."{A(H):H in cal(H)}. $
]<exc:hyperelementary-artin-exponent-lcm>
#hint([@exc:hyperelementary-artin-exponent-lcm])[
  Denote this L.C.M. by $m$, so $m|A(G)$ by
  @prop:artin-exponent-functorial-properties. On the other hand, for
  $H in cal(H)$, $m dot 1_H$ is a $ZZ$-linear combination of characters
  ${(1_C)^H:C≤H,C "cyclic"}$. Now use Solomon's Theorem
  @i:th:solomon-permutation-induction to obtain an expression for $m dot 1_G$.
]<hint:hyperelementary-artin-exponent-lcm>
