#import "main-defs.typ": *
#import "statements.typ": *

== $S K_1$ of Integral Group Rings <sec:sk1-integral-group-rings>

Throughout this section, $G$ denotes a finite group, and $G_p$ a Sylow
$p$-subgroup of $G$ for each prime $p$. Let $R$ be a Dedekind domain whose
quotient field $F$ is either an algebraic number field or else a finite
extension of a $p$-adic field $QQ_p$. In the latter case, $R$ is taken to be the
valuation ring in $F$, and is called a _p-adic ring_.

Our purpose here is to describe some of the main results about
$S K_1 lr((R G))$. The proofs are beyond the scope of this book, since they
involve a generalized version of the Bass–Milnor–Serre Theorem, as well as
detailed calculations with $K_2$-groups. We begin by recalling some earlier
results.

The inclusion $R G subset.eq F G$ induces a map
$K_1 lr((R G)) -> K_1 lr((F G))$, whose kernel is denoted by $S K_1 lr((R G))$.
We have already established:
#idx("SK₁")

#enum(
  [$S K_1 lr((R G))$ is a finite abelian group (Bass’s Theorem
    @th:bass-sk1-finiteness).],
  [If $R$ is a $p$-adic ring, then $S K_1 lr((R G))$ is a finite $p$-group
    (Wall’s Theorem @th:p-adic-group-ring-sk1-p-group).],
  [If $R$ is a $p$-adic ring, then $S K_1 lr((R G)) = 1$ if $G_p$ is abelian or
    if $p$ does not divide $|G'|$ (see @th:wall-abelian-sylow-sk1-trivial and
    @rem:wall-crossed-product-azumaya-generalization(ii)).],
)

#source(227)
For $G$ cyclic of prime order, we proved at the end of §@ss:relative-k2 that
$S K_1 lr((ZZ G)) = 1$. More generally, the following holds true:

#theorem(name: "Bass-Milnor Theorem")[
  $S K_1 lr((ZZ G)) = 1$ for every cyclic group $G$.
] <th:bass-milnor-cyclic-group-sk1>
#idx("Bass-Milnor Theorem", target: [@th:bass-milnor-cyclic-group-sk1])

For a proof, see Bass–Milnor–Serre @bib:Bass1967, Prop. 4.14. The theorem
remains valid when $ZZ$ is replaced by a ring $R$ of algebraic integers, see
Alperin–Dennis–Stein @bib:Alperin1985 and Alperin–Dennis–Oliver–Stein
@bib:AlperinDennisOliverStein1986.
#idx("Alperin-Dennis-Oliver-Stein Theorem")

We next introduce the _induction_ and _restriction_ maps:
$
  op("ind")_H^G: K_1 lr((R H)) -> K_1 lr((R G)), quad
  op("res")_H^G: K_1 lr((R G)) -> K_1 lr((R H)).
$
These were discussed in §@sec:whitehead-integral-group-rings (see
@lem:whitehead-trivial-units-frobenius-submodules), where we showed that
$K_1 lr((R G))$ is a Frobenius module over the Frobenius functor
$G_0^R lr((R G))$. Since $op("ind")$ and $op("res")$ commute with maps obtained
by change of ground ring from $R$ to $F$, it follows readily that
$S K_1 lr((R G))$ is also a Frobenius module over $G_0^R lr((R G))$. We may
therefore apply the induction theorems established in
§@ss:grothendieck-frobenius.

For a prime $p$, let the subscript $(p)$ denote localization at $p$. Then
$S K_1 lr((R G))_((p))$ is precisely the _p-torsion submodule_ of the finite
abelian group $S K_1 lr((R G))$:
#idx("p-torsion subgroup")
$
  S K_1 lr((R G))_((p)) =
  {x in S K_1 lr((R G)): p^n x = 0 "for some" n >= 0}.
$
As in @th:wall-abelian-sylow-sk1-trivial, we see that $S K_1 lr((R G))_((p))$ is
a Frobenius module over $G_0^R lr((R G))_((p))$, where
$
  G_0^R lr((R G))_((p)) = ZZ_((p)) times.o_ZZ G_0^R lr((R G)).
$
On the other hand, starting with our given field $F$, we denote by $cal(H)_p$
the set of all subgroups $H$ of $G$ which are $F$-elementary at the prime $p$
(see Volume I, §@i:ss:witt-berman-induction). Then we obtain
$
  G_0 lr((F G))_((p)) =
  sum_(H in cal(H)_p) op("ind")_H^G G_0 lr((F H))_((p)),
$
by an easy modification of the proof of the Witt–Berman Theorem
@i:th:witt-berman-induction. As in the proof of
@cor:lattice-hyperelementary-induction, the above implies that
$
  G_0^R lr((R G))_((p)) =
  sum_(H in cal(H)_p) op("ind")_H^G G_0^R lr((R H))_((p)).
$
Therefore we obtain from @prop:frobenius-family-ideals:
$
  S K_1 lr((R G))_((p)) =
  sum_(H in cal(H)_p) op("ind")_H^G S K_1 lr((R H))_((p)),
$
$
  inter.big_(H in cal(H)_p)
  ker(op("res")_H^G "acting on" S K_1 lr((R G))_((p))) = 0.
$
Thus, we may obtain information about $S K_1 lr((R G))$ from knowledge of
$S K_1 lr((R H))$ for various $F$-elementary subgroups $H$ of $G$.
#source(228)
However, a much stronger result is true. We state without proof the following
fundamental theorem, due to R. Oliver @bib:Oliver1981:

#theorem(name: "Oliver’s Theorem")[
  Let $p$ be prime, and let $cal(E)_p$ be the set of $p$-elementary subgroups of
  $G$, that is, subgroups which are a direct product of a $p$-group and a cyclic
  $p'$-group. Then
  #enum(
    numbering: "(i)",
    [For $R = "alg. int." {F}$, we have
      $
        S K_1 lr((R G))_((p)) =
        sum_(H in cal(E)_p) op("ind")_H^G S K_1 lr((R H))_((p)).
      $],
    [If $R$ is a $p$-adic ring, then
      $
        S K_1 lr((R G)) =
        sum_(H in cal(E)_p) op("ind")_H^G S K_1 lr((R H)).
      $],
    [There exist groups $G$ for which
      $
        inter.big_(H in cal(E)_p)
        ker(op("res")_H^G "acting on" S K_1 lr((R G))_((p))) != 0.
      $],
  )
] <th:oliver-elementary-sk1-induction>
#idx("Oliver's Theorem", target: [@th:oliver-elementary-sk1-induction])

This powerful theorem seems rather unexpected, and it also provides an instance
where the induction and restriction properties are markedly different. Before
applying Oliver’s Theorem, we describe some induction theorems involving the set
$cal(C)$ of all _cyclic_ subgroups of a given group $G$. By definition, the
_Artin exponent_ $A(G)$ (see also §@sec:artin-exponent) is the least positive
integer $n$ such that
#idx("Artin exponent")
#nidx("$A(G)$", "Artin exponent", chapter: [@ch:rationality-questions])
$
  n dot G_0 lr((QQ G)) subset.eq
  sum_(H in cal(C)) op("ind")_H^G G_0 lr((QQ H)).
$
By Artin’s Induction Theorem @i:th:artin-induction-explicit-coefficients we know
that $A(G)$ divides $|G|$. Next, by @th:swan-grothendieck-annihilation we obtain
$
  A(G)^2 dot G_0^ZZ lr((ZZ G)) subset.eq
  sum_(H in cal(C)) op("ind")_H^G G_0^ZZ lr((ZZ H)),
$
and consequently
$
  A(G)^2 dot S K_1 lr((ZZ G)) subset.eq
  sum_(H in cal(C)) op("ind")_H^G S K_1 lr((ZZ H)).
$
However, each term $S K_1 lr((ZZ H))$, $H in cal(C)$, is trivial by the
Bass–Milnor Theorem. We have thus established:

#theorem(name: "Lam’s Theorem")[
  Let $A(G)$ be the Artin exponent of $G$. Then
  $ A(G)^2 S K_1 lr((ZZ G)) = 0. $
] <th:lam-artin-exponent-sk1>
#idx("Lam's Theorem", target: [@th:lam-artin-exponent-sk1])

#source(229)
As shown by Alperin–Dennis–Oliver–Stein @bib:AlperinDennisOliverStein1986, the
analogous result holds true when $ZZ$ is replaced by a ring of algebraic
integers:

#theorem[
  Let $R = "alg. int." {F}$, where $F$ is an algebraic number field. Then
  $ A(G)^2 dot S K_1 lr((R G)) = 0, $
  where $A(G)$ is the Artin exponent of $G$.
] <th:integer-ring-artin-exponent-sk1>
#proof[
  As shown in the proof of @cor:lattice-cyclic-induction, $S K_1 lr((R G))$ is a
  Frobenius module over the Frobenius functor $G_0^ZZ lr((ZZ G))$. By the
  remarks preceding @th:lam-artin-exponent-sk1, we obtain
  $
    A(G)^2 dot S K_1 lr((R G)) subset.eq
    sum_(H in cal(C)) op("ind")_H^G S K_1 lr((R H)).
  $
  But $S K_1 lr((R H))$ is trivial for each cyclic group $H$, as pointed out in
  the remarks after @th:bass-milnor-cyclic-group-sk1. This gives the desired
  result.
]

As an immediate consequence of the above, we obtain:

#corollary[
  Let $R = "alg. int." {F}$, and let $p$ be prime. Then
  #enum(
    numbering: "(i)",
    [If $G$ is a $p$-group, then so is $S K_1 lr((R G))$.],
    [If $p divides.not |G|$, then $S K_1 lr((R G))$ is $p$-torsionfree.],
    [If $G$ has a cyclic normal Sylow $p$-subgroup, then $S K_1 lr((R G))$ is
      $p$-torsionfree.],
  )
] <cor:integral-group-ring-sk1-primary-torsion>

The first two assertions follow from @th:integer-ring-artin-exponent-sk1, since
$A(G)$ divides $|G|$. Assertion (iii) is a consequence of a result of Lam
@bib:Lam1968b (see @cor:cyclic-sylow-artin-primary-one-sufficient), which states
that if $G$ has a cyclic normal Sylow $p$-subgroup, then $p divides.not A(G)$.

We turn next to the question as to which groups $G$ have trivial
$S K_1 lr((ZZ G))$. This is a difficult question, even for abelian groups. The
key result below is proved in Alperin–Dennis–Stein @bib:Alperin1985 and
Alperin–Dennis–Oliver–Stein @bib:AlperinDennisOliverStein1986, and may be viewed
as a far-reaching generalization of the Bass–Milnor Theorem. The proofs, beyond
the scope of this book, use detailed facts about $K_2$-groups, as well as
earlier calculations by various authors (Bass, Kervaire, Lam, Milnor). Also
needed is the result#footnote[
  This result holds even when $G$ is non-abelian, provided $H$ is abelian; see
  Magurn @bib:Magurn1978a. However, as shown by Oliver, the result may fail
  without such hypothesis on $H$.
] that a surjection of abelian groups $G -> H$ induces a surjection
$S K_1 lr((ZZ G)) -> S K_1 lr((ZZ H))$.

#theorem(title: [Alperin–Dennis–Oliver–Stein])[
  Let $G$ be an abelian group. Then $S K_1 lr((ZZ G)) = 1$ in precisely the
  following cases:
  #enum(
    numbering: "(i)",
    [$G = "elementary abelian 2-group"$,],
    [All Sylow subgroups of $G$ are cyclic,],
    [For each $p$ for which $G_p$ is noncyclic, the Sylow $p$-subgroup has the
      form $C_p times C_(p^n)$ for some $n >= 1$,],
  )
  where $C_m$ denotes a cyclic group of order $m$.#ed-note[
    The alternatives must allow different Sylow types at different primes. For
    example, $C_2 times C_3^2$ has trivial $S K_1$, but is excluded by the
    literal three alternatives in the original. See Oliver @bib:Oliver1988,
    Theorem~14.2(iii).
  ]
] <th:abelian-group-ring-sk1-triviality>
#idx(
  "Alperin-Dennis-Oliver-Stein Theorem",
  target: [@th:abelian-group-ring-sk1-triviality],
)

#source(230)
This theorem, used in conjunction with Oliver’s Theorem and a result of
Obayashi, allows us to prove the triviality of $S K_1 lr((ZZ G))$ in most of the
known cases. For example, we obtain:
#idx("Alperin-Dennis-Oliver-Stein Theorem")

#theorem(title: [Magurn @bib:Magurn1978b])[
  For $D_n$ the dihedral group of order $2n$, we have $S K_1 lr((ZZ D_n)) = 1$.
] <th:magurn-dihedral-sk1>
#proof[
  The elementary subgroups $H$ of $D_n$ are either cyclic or of the form
  $C_2 times C_2$, or possibly a dihedral $2$-group. In the first two cases we
  know that $S K_1 lr((ZZ H)) = 1$ by @th:abelian-group-ring-sk1-triviality. For
  a dihedral $2$-group $H$ we again have $S K_1 lr((ZZ H)) = 1$ by Obayashi
  @bib:Obayashi1973. Therefore $S K_1 lr((ZZ D_n)) = 1$ by Oliver’s Theorem
  @th:oliver-elementary-sk1-induction.
]

#theorem[
  If $p^3 divides.not |G|$ then $S K_1 lr((ZZ G))$ is $p$-torsionfree.
] <th:cube-free-primary-sk1-torsionfree>
#proof[
  Let $G_p$ be a Sylow $p$-subgroup of $G$; then $|G_p| <= p^2$, so $G_p$ is one
  of $1$, $C_p$, $C_(p^2)$ or $C_p times C_p$. Each $p$-elementary subgroup $H$
  of $G$ is therefore a subgroup of $C times G_p$ for some cyclic $p'$-group
  $C$. But then $S K_1 lr((ZZ H)) = 1$ by @th:abelian-group-ring-sk1-triviality,
  so the desired result follows from Oliver’s Theorem.
]

A similar argument yields another proof of
@cor:integral-group-ring-sk1-primary-torsion(iii) for the case $R = ZZ$; we have
the details as an exercise for the reader.

Next, we list some cases where $S K_1 lr((ZZ G))$ is known explicitly. The
following results are stated in Stein @bib:Stein1978:

#enum(
  numbering: "(1)",
  [Let $G$ be an elementary abelian $p$-group of rank $k$, where $p$ is an odd
    prime. Then $S K_1 lr((ZZ G))$ is also an elementary abelian $p$-group, of
    rank
    $ (p^k - 1) / (p - 1) - binom(p+k-1, p), $
    which is positive for $k >= 3$. The proof is sketched in
    Alperin–Dennis–Stein @bib:Alperin1973a. For full details, see
    Alperin–Dennis–Oliver–Stein @bib:AlperinDennisOliverStein1986.],
  [For $G$ abelian, the calculation of $S K_1 lr((ZZ G))$ can be reduced to that
    of $S K_1 lr((ZZ G_p))$, with $G_p$ ranging over the Sylow subgroups of $G$.
    For the proof, see Alperin–Dennis–Stein @bib:Alperin1985.#ed-note[
      The reduction involves multiplicities and an additional elementary abelian
      $2$-group; see Oliver @bib:Oliver1988, Theorem~13.13. Thus vanishing
      cannot always be tested on the integral Sylow group rings alone:
      $S K_1 lr((ZZ[C_2^3 times C_3])) tilde.equiv C_2$, although
      $S K_1 lr((ZZ C_2^3)) = S K_1 lr((ZZ C_3)) = 1$.
    ]],
  [Let $C_n$ denote a cyclic group of order $n$, and $p$ an odd prime. As shown
    in Alperin–Dennis–Oliver–Stein @bib:AlperinDennisOliverStein1986, the
    following table gives the structure of $S K_1 lr((ZZ G))$:
    #table(
      columns: 2,
      align: (left, left),
      table.header([$G$], [$S K_1 lr((ZZ G))$]),
      table.hline(),
      [$C_(p^2) times C_(p^n), quad n >= 1$], [$C_p^((p-1)(n-1))$],
      [$C_(p^n) times C_p times C_p, quad n >= 1$], [$C_p^(n p(p-1) slash 2)$],
      [$C_(p^3) times C_(p^3)$], [$C_p^((p^2-1)) times C_(p^2)^((p-1))$],
      [$C_3 times C_9 times C_9$], [$C_3^((15)) times C_9^((2))$],
      [$C_8 times C_8$], [$C_2^((4))$],
      [$C_4 times C_4$], [$C_2$],
      [$C_2 times C_2 times C_4$], [$C_2$],
      [$C_2 times C_2 times C_2 times C_4$], [$C_2^((3)) times C_4$],
    )
    #source(231)
    The cases where $G = C_(p^n) times C_p^((3))$ and
    $G = C_(2^n) times C_2^((k))$ have also been worked out explicitly in the
    above reference.],
)

To conclude this brief survey, we quote some results of Oliver @bib:Oliver1980b.
#enum(
  numbering: "(1)",
  start: 4,
  [For odd $p$, there exist groups $G$ of order $p^5$ for which
    $S K_1 lr((ZZ_p G)) != 1$, where $ZZ_p$ is the ring of $p$-adic integers.

    For $p = 2$, there is a group $G$ of order $64$ with
    $S K_1 lr((ZZ_2 G)) != 1$.],
  [Let $R$ be a $p$-adic ring, and $G$ a $p$-group. Then
    $ S K_1 lr((R G)) tilde.equiv H_2 lr((G)) slash H_2^(a b) lr((G)), $
    where $H_2 lr((G))$ is the Schur multiplier of $G$, and $H_2^(a b) lr((G))$
    is the subgroup of $H_2 lr((G))$ generated by the image of all
    ${H_2 lr((A))}$, where $A$ ranges over the abelian subgroups of $G$.

    In particular, $S K_1 lr((R G))$ is independent of $R$.],
)
