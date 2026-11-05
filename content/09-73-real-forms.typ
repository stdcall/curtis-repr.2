#import "main-defs.typ": *
#import "statements.typ": *

#source(736)
== Unitary, Orthogonal, and Symplectic $CC G$-Modules
<sec:unitary-orthogonal-symplectic-modules>

=== Rationality Questions over the Real Field $RR$
<ss:real-field-rationality>

We consider $CC G$-modules $M$, where $G$ is a finite group, and are interested
in subfields $K$ of $CC$ such that $M$ is _realizable_ in $K$. This means that
there exists an isomorphism of $CC G$-modules
#idx("Realizable")
$ M tilde.equiv CC times.o_K M_0 $
<eq:complex-module-field-form>
for some $K G$-module $M_0$ (called a $K$-form of $M$). A $K$-basis of $M_0$ is
then a $CC$-basis of $M$, and relative to this basis, the matrices
${bold(M)(x):x in G}$ have entries in $K$. It is easily shown (see
@i:prop:splitting-field-criteria) that a field $K subset.eq
CC$ is a splitting field for $G$ if and only if every simple $CC G$-module has a
$K$-form.

In this subsection we consider the basic question as to which $CC G$-modules
admit $RR$-forms, where $RR$ is the real field. A beautiful solution of this
problem, which involves interesting and unexpected connections with the internal
structure of the group $G$, was given by Frobenius–Schur @bib:Frobenius1906. Our
account follows Serre @bib:Serre1977, with some changes and additions.

We first recall that the contragredient module $M^*$ of a $CC G$-module $M$ is
the dual space $M^*="Hom"_CC lr((M,CC))$, on which $G$ acts according to the
rule
#idx("Contragredient")
$ (x dot f)m=f(x^(-1)m), quad "for all" f in M^*, quad m in M, quad x in G. $
If $M$ affords the character $mu$ of $G$, then $M^*$ affords the character
$mu^*$ given by
$ mu^*(x)=mu(x^(-1))=overline(mu(x)) quad "for" x in G, $
<eq:contragredient-complex-character>
where bar denotes complex conjugation (see §~@i:ss:contragredient-modules). We
shall call $mu$ _real-valued_ if $mu(x) in RR$ for all $x in G$, or
equivalently, if $mu=overline(mu)$. Clearly $mu$ is real-valued whenever $M$ has
an $RR$-form.

We now have:

#idx("Frobenius-Schur Theorem")
#theorem(title: [Frobenius–Schur])[
  Let $M$ be a $CC G$-module with character $mu$. Then
  #case-list(
    numbering: "(i)",
    [#case[
      $mu$ is real-valued if and only if $M$ admits a nondegenerate
      $G$-invariant bilinear form.
    ]<case:real-character-invariant-bilinear-form>],
    [#case[
      $M$ has an $RR$-form if and only if $M$ admits a nondegenerate symmetric
      $G$-invariant bilinear form (over $CC$). In this case, $M$ affords a
      representation in which each $x in G$ is represented by a real orthogonal
      matrix.
    ]<case:real-form-symmetric-invariant-bilinear-form>],
  )
]<th:frobenius-schur-real-forms>

#proof[
  (i) $mu$ is real-valued if and only if $M tilde.equiv M^*$. The existence of a
  $CC G$-isomorphism from $M$ to $M^*$ is easily shown to be equivalent to the
  existence of a $G$-invariant nondegenerate bilinear form on $M$, by the sort
  of argument used in §~@i:ss:contragredient-modules. We leave it as an exercise
  for the reader to check this assertion.

  #source(737)
  (ii) First assume $M$ has an $RR$-form $M_0$. The $RR G$-module $M_0$ admits a
  positive definite symmetric $G$-invariant bilinear form
  $lr(chevron.l m, n chevron.r)$, obtained by the averaging process from the
  usual inner product $(m,n)$ defined with respect to some $RR$-basis of $M_0$.
  Specifically, define
  $
    lr(chevron.l m, n chevron.r)=abs(G)^(-1) sum_(x in G)(x m,x n),
    quad "for" m,n in M_0.
  $
  Since $M tilde.equiv CC times.o_RR M_0$, the form
  $lr(chevron.l m, n chevron.r)$ extends to a nondegenerate, symmetric,
  $G$-invariant bilinear form on $M$, proving one implication in part (ii).

  Conversely, let $M$ admit a symmetric nondegenerate $G$-invariant bilinear
  form $B(m,n)$. Let $[m,n]$ be a nondegenerate $G$-invariant positive definite
  hermitian bilinear form on $M$ (whose existence follows by the same argument
  used above: see @bib:CurtisReiner1962[CR] Exercise (10.6)). Then there exists
  a map $phi:M arrow.r M$ such that
  $ B(m,n)=overline([phi(m),n]) quad "for all" m,n in M. $
  The map $phi$ is clearly bijective and semilinear, in the sense that
  $ phi(z m)=overline(z) phi(m) quad "for all" z in CC, quad m in M. $
  Moreover, $phi^2 in op("GL")(M)$, and we have
  $
    [phi^2 m,n]=overline(B(phi(m),n))
    =overline(B(n,phi(m)))=[phi n,phi m] quad "for all" m,n in M.
  $
  Since $[m,n]=overline([n,m])$, we obtain
  $
    [m,phi^2 n]=overline([phi^2 n,m])=overline([phi m,phi n])
    =[phi n,phi m]=[phi^2 m,n],
  $
  using the previous computation. Thus $phi^2$ is self-adjoint. Moreover,
  $ [phi^2 m,m]=[phi m,phi m]>0 quad "for all" m !=0, $
  so $phi^2$ is positive definite. A standard application of the spectral
  theorem for self-adjoint linear transformations shows that a positive definite
  self-adjoint map $T$ has a unique positive definite self-adjoint square root
  $U$ such that $U^2=T$ and $U=p(T)$ for some polynomial $p$ with real
  coefficients. Let $nu$ be the positive definite self-adjoint square root of
  $phi^2$, and put $sigma=phi nu^(-1)$. Since $nu=p(phi^2)$, $nu$ and $phi$
  commute, and we obtain
  $ sigma^2=phi^2 nu^(-2)=1. $
  It follows that $M=M_0 plus.o M_1$, where $M_0={m in M:sigma m=m}$ and
  $M_1={m in M:sigma m=-m}$. Since $sigma$ is semilinear, $M_0$ and $M_1$ are
  $RR$-subspaces of $M$ such that $M_1=i M_0$ (where $i=sqrt(-1)$). Thus
  $M=M_0 plus.o i M_0$. Since both $B(m,n)$

  #source(738)
  and $[m,n]$ are $G$-invariant, it follows that $phi^2$ and $nu$ commute with
  the action of $G$, whence so does $sigma$. Then $M_0$ is clearly an $RR$-form
  of $M$, and the theorem is proved.
]

#example[
  Let $Q=lr(chevron.l a, b ":" a^4=1, b^2=a^2, b a b^(-1)=a^(-1) chevron.r)$ be
  the quaternion group of order $8$. The $CC$-characters of $Q$ are all
  rational-valued, and in fact $Q$ has the same character table as the dihedral
  group $D_4$ (see @i:exc:equal-character-tables-dihedral-quaternion). Let $M$
  be the unique simple two-dimensional $CC Q$-module. Then its character is
  real-valued, but $M$ does not admit an $RR$-form. To see this, suppose to the
  contrary that $M_0$ is an $RR$-form of $M$. By @th:frobenius-schur-real-forms,
  it follows that the matrices ${bold(M)(x):x in Q}$ afforded by $M$, with
  respect to a suitable $RR$-basis of $M_0$, are real orthogonal matrices. But
  it is easily shown that the finite subgroups of the orthogonal group on the
  plane are either cyclic or dihedral. Thus $M$ does not have an $RR$-form. (See
  also the example at the end of §~@ss:schur-index-general-theory.)
]<exm:quaternion-real-valued-no-real-form>

In the next part of the discussion, we make use of the theorem of Frobenius,
which states that every f.d. division algebra over $RR$ is isomorphic to exactly
one of the following: $RR$, $CC$, or $ℍ$, where $ℍ$ is the division algebra of
real quaternions (for proof see @bib:Reiner1975[MO], Exercise 31.8). Thus the
simple $RR G$-modules $M$ can be put in three classes, according as
$"End"_(RR G) M tilde.equiv RR$, $CC$, or $ℍ$. (The same idea gives a
classification of simple $A$-modules, for any f.g. semisimple $RR$-algebra.)

We also require the following important construction, which we describe in a
general form for later use (see also §~@i:ss:induction-frobenius).

#definition[
  Let $M$ be a f.g. $K G$-module, where $G$ is a finite group, and $K$ a field.
  For any subfield $F subset K$ such that $dim_F K<infinity$, the natural
  embedding $F G subset K G$ defines the structure of a f.g. $F G$-module on
  $M$, called the $F G$-module obtained by _restriction of scalars_, and denoted
  by $lr(M |)_(F G)$ (or simply $M_(F G)$).
]<def:module-restriction-of-scalars>

#lemma[
  Let $M$ be a $K G$-module affording a matrix representation
  $x arrow.r bold(M)(x)=(m_(i j) lr((x)))$, $x in G$, with entries
  $m_(i j) lr((x))$ in $K$. Then for any subfield $F subset K$ with
  $dim_F K<infinity$, $M_(F G)$ affords a matrix representation
  $x arrow.r rho_(K slash F) lr((m_(i j) lr((x))))$, where $rho_(K slash F)$ is
  the regular matrix representation of $K$ over $F$.
]<lem:restriction-scalars-regular-matrix>

#proof[
  Let $u_1,dots,u_d$ be a $K$-basis for $M$, and $xi_1,dots,xi_e$ an $F$-basis
  of $K$. Thus the set
  $ {xi_i u_j:1 lt.eq i lt.eq e,1 lt.eq j lt.eq d} $
  is an $F$-basis of $M_(F G)$. We have, for $x in G$:
  $
    x(xi_i u_j)&=xi_i lr((x u_j))=xi_i sum_(k=1)^d lr((m_(k j) lr((x)) u_k)) \
    &=sum_(k=1)^d lr((m_(k j) lr((x)) xi_i)) u_k
    =sum_(k=1)^d sum_(l=1)^e rho_(l i) lr((m_(k j) lr((x)))) xi_l u_k,
  $

  #source(739)
  where $rho_(K slash F) lr((a))=(rho_(i j) lr((a)))$, $a in K$, is the regular
  matrix representation of $K$ over $F$ with respect to the basis
  $xi_1,dots,xi_e$. This completes the proof.
]

#corollary[
  Keep the previous notation, and assume that $K slash F$ is a Galois extension
  with Galois group $frak(G)="Gal"(K slash F)$. Then for all $x in G$,
  $ "Tr"(x,M_(F G))=sum_(sigma in frak(G)) sigma "Tr"(x,M). $
]<cor:restriction-scalars-galois-trace>

#proof[
  By @lem:restriction-scalars-regular-matrix,
  $
    "Tr"(x,M_(F G)) & =sum_(k=1)^d "Trace" rho_(K slash F)
                      lr((m_(k k) lr((x)))) \
                    & =sum_(sigma in frak(G)) sigma "Tr"(x,M),
  $
  as required, since by Galois theory, the trace of the regular representation
  of $K slash F$ is given by $sum_(sigma in frak(G)) sigma$.
]

Returning to the real and complex fields, we have:

#corollary[
  Let $M$ be a f.g. $CC G$-module with character $mu$. Then the character
  afforded by the $RR G$-module $lr(M |)_(RR G)$ obtained by restriction of
  scalars is given by
  $ x arrow.r "Tr"(x,lr(M |)_(RR G))=mu(x)+overline(mu(x)), quad x in G, $
  where bar denotes complex conjugation.
]<cor:complex-real-restriction-character>

This result follows at once from @cor:restriction-scalars-galois-trace, since
$CC slash RR$ is a Galois extension with Galois group
$lr(chevron.l sigma chevron.r)$, where $sigma$ is complex conjugation.

#theorem[
  Let $M$ be a simple $CC G$-module, with character $mu$, and let $n=dim_CC M$.
  Then exactly one of the following possibilities occurs:
  #case-list(
    numbering: "(i)",
    [#case[
      $mu$ is not real-valued. Then the $RR G$-module $M_(RR G)$, obtained from
      $M$ by restriction of scalars, is a simple $RR G$-module of dimension $2n$
      over $RR$, affording the character $mu+overline(mu)$. In this case, the
      endomorphism algebra $"End"_(RR G) M_(RR G)$ is isomorphic to $CC$, and
      the corresponding Wedderburn component of $RR G$ is isomorphic to
      $M_n lr((CC))$.
    ]<case:complex-type-real-simple-module>],
    [#case[
      $mu$ is real-valued, and $M$ has an $RR$-form $M_0$. Then $M_0$ is
      absolutely simple, with character $mu$. Moreover,
      $"End"_(RR G) M_0 tilde.equiv RR$, and the Wedderburn component of $RR G$
      corresponding to $M_0$ is isomorphic to $M_n lr((RR))$. In this case,
      $M_(RR G)$ is a direct sum of two copies of $M_0$.
    ]<case:real-type-real-simple-module>],
    [#case[
      $mu$ is real-valued, but $M$ does not have an $RR$-form. Then the
      $RR G$-module $M_(RR G)$ obtained by restriction of scalars is a simple
      $RR G$-module of dimension $2n$, whose
      #source(740)
      character is $2mu$. The endomorphism algebra $"End"_(RR G) M_(RR G)$ is
      isomorphic to $ℍ$, and the corresponding Wedderburn component of $RR G$ is
      isomorphic to $M_(n slash 2) lr((ℍ))$.
    ]<case:quaternion-type-real-simple-module>],
  )
]<th:real-complex-simple-module-types>

#proof[
  (i) By @cor:complex-real-restriction-character, we have
  $"Tr"(x,M_(RR G))=mu(x)+overline(mu(x))$ for all $x in G$. Then the character
  of $CC times.o_RR M_(RR G)$ is $mu+overline(mu)$, and hence
  $CC times.o_RR M_(RR G) tilde.equiv M plus.o M^*$, and $M^* ≄ M$ by
  @eq:contragredient-complex-character, since $mu !=overline(mu)$ because of the
  hypothesis that $mu$ is not real-valued. We next prove that $M_(RR G)$ is a
  simple $RR G$-module. Suppose, to the contrary, that $M_1$ is a proper
  submodule of $M_(RR G)$. Then $CC times.o M_1$ is isomorphic either to $M$,
  $M^*$, or $M plus.o M^*$, and each of these possibilities is easily seen to be
  impossible. Thus $M_(RR G)$ is a simple $RR G$-module. By
  @i:exc:endomorphism-field-extension, we have
  $
    dim_RR "End"_(RR G) M_(RR G)
    =dim_CC "End"_(CC G) CC times.o M_(RR G)
    =dim_CC "End"_(CC G)(M plus.o M^*)=2,
  $
  since $M$ is simple and $M ≄ M^*$. By Frobenius' theorem on real division
  algebras, we conclude that $"End"_(RR G) M tilde.equiv CC$, and the rest
  follows from the Wedderburn theorems.

  (ii) The $RR$-form $M_0$ is clearly a simple $RR G$-module, with character
  $mu$. Since $CC times.o_RR M_0 tilde.equiv M$, we have
  $dim_RR "End"_(RR G) M_0=dim_CC "End"_(CC G) M=1$ by the same reasoning as in
  the proof of (i). The rest of part (ii) follows from the Wedderburn theorems.

  (iii) This is proved by an argument similar to the proof of (i), and is left
  as an exercise for the reader. This completes the proof of the theorem.
]

We shall now give some other ways of distinguishing between the possibilities
described in the above theorem. The first is a kind of geometric
characterization, in terms of the existence of $G$-invariant bilinear forms on
$M$.

#theorem[
  Let $M$ be a simple $CC G$-module, affording the character $mu$.
  #case-list(
    keep-together: true,
    numbering: "(i)",
    [#case[
      If $M$ does not admit a nonzero $G$-invariant bilinear form, then $mu$ is
      not real-valued, and $M$ has no $RR$-form. Call $M$ _unitary_ in this
      case.
      #idx("Unitary CG-module")
    ]<case:unitary-simple-complex-module>],
    [#case[
      If $M$ admits a nonzero $G$-invariant bilinear form, then this form is
      unique up to scalar multiples. It is nondegenerate, and is either
      symmetric or skew-symmetric. If the form is symmetric, then $mu$ is
      real-valued, and $M$ has an $RR$-form. We call $M$ _orthogonal_ in this
      case (since $M$ affords a real representation of $G$ by orthogonal
      transformations).
      #idx("Orthogonal CG-module")

      If the form is skew-symmetric, then $mu$ is real-valued, but $M$ has no
      $RR$-form. We call $M$ _symplectic_, since $M$ affords a representation of
      $G$ by symplectic transformations.#footnote[
        A _symplectic transformation_ on a vector space over a field is a linear
        map preserving a nondegenerate skew-symmetric bilinear form on the
        vector space.
      ]
      #idx("Symplectic CG-module")
      #idx("Symplectic character")
    ]<case:orthogonal-symplectic-simple-complex-module>],
  )
]<th:simple-complex-module-form-types>

#proof[
  If $M$ admits a nonzero $G$-invariant bilinear form $B$, then $B$ defines a
  nonzero $CC G$-homomorphism between $M$ and $M^*$. This homomorphism is
  uniquely determined up to a scalar multiple by Schur's Lemma, since both $M$
  and $M^*$ are simple $CC G$-modules. It follows that $B$ is nondegenerate and
  is uniquely #source(741) determined up to scalar multiples. Now write
  $B=B_++B_-$, with $B_+$ symmetric and $B_-$ skew-symmetric. It is clear that
  both $B_+$ and $B_-$ are also $G$-invariant, so by uniqueness we may assume
  that either $B=B_+$ or $B=B_-$. In the first case, it follows that $M$ has a
  real form, and hence is orthogonal, by @th:frobenius-schur-real-forms
  (part~@case:real-form-symmetric-invariant-bilinear-form). In case $B=B_-$, we
  conclude that $mu$ is real-valued by
  @th:frobenius-schur-real-forms
  (part~@case:real-character-invariant-bilinear-form), and that $M$ does not
  admit a nondegenerate symmetric $G$-invariant bilinear form, because of the
  uniqueness of $B$. Then $M$ is symplectic in this case. Finally, $M$ is
  unitary if and only if neither of the above situations occur. This is
  equivalent to the assertions that $mu$ is not real-valued, and that $M$ admits
  no nonzero $G$-invariant bilinear form. These remarks complete the proof of
  the theorem.
]

We remark that in case $M$ is unitary, $M$ does admit a positive definite
$G$-invariant hermitian form (see the proof of @th:frobenius-schur-real-forms).

We conclude this subsection with an important test of the type of a simple
$CC G$-module, as in @th:simple-complex-module-form-types, in terms of the
character table of $G$. We first recall some concepts introduced in
§~@i:ss:symmetric-skew-squares-induced-modules. Let $M$ be an arbitrary f.g.
$CC G$-module, with character $mu$. Starting from the isomorphism of vector
spaces over $CC$,
$ "Hom"_(CC G)(M^*,M) tilde.equiv "inv"_G lr((M times.o M)), $
we define the _intertwining number_
$ i(M^*,M)=dim_CC "inv"_G lr((M times.o M)). $
We also introduce the _symmetric and antisymmetric intertwining numbers_,
defined by
$
  i_s lr((M^*,M))=dim_CC "inv"_G lr((M or M))
  quad "and" quad
  i_a lr((M^*,M))=dim_CC "inv"_G lr((M and M)),
$
<eq:symmetric-alternating-intertwining-numbers>
where $M or M$ and $M and M$ denote the $CC G$-modules consisting of symmetric
tensors and skewsymmetric tensors, respectively, in $M times.o M$. Since we have
$ M times.o M tilde.equiv (M or M) plus.o (M and M) $
as $CC G$-modules, it follows that
$ i(M^*,M)=i_s lr((M^*,M))+i_a lr((M^*,M)). $
We now define the _Frobenius–Schur indicator_
$ c(M)=i_s lr((M^*,M))-i_a lr((M^*,M)), $
<eq:frobenius-schur-indicator-definition>
#idx("Frobenius-Schur indicator")
#nidx("$c(M)$", "Frobenius-Schur indicator", target: [
  @eq:frobenius-schur-indicator-definition
])
and note that $c(M) in {0,plus.minus 1}$ for a simple $CC G$-module
$M$.#footnote[
  We take this opportunity to correct the statement of
  @i:prop:symmetric-intertwining-invariant-properties. In the statement of
  @i:prop:symmetric-intertwining-invariant-properties(ii), delete
  “$c(M times.o N)=c(M)c(N)$, and,” and in
  @i:prop:symmetric-intertwining-invariant-properties(iii), replace “ring
  homomorphisms” by “$ZZ$-homomorphisms.”
]

#source(742)
The next result shows that the Frobenius–Schur indicator $c(M)$ determines the
type of a simple module $M$, and gives a method for calculating $c(M)$ in terms
of the character afforded by $M$. The invariant $c(M)$ has proved to be so
useful, in recent calculations of characters of finite simple groups, that there
is good reason to regard the Frobenius–Schur indicators $c(Z_i)$ of a basic set
of simple $CC G$-modules ${Z_i:1 lt.eq i lt.eq s}$, as part of the character
table data of an arbitrary finite group $G$ (see @i:def:character-table-data).

#idx("Frobenius-Schur Theorem")
#theorem(title: [Frobenius–Schur])[
  Let $M$ be a simple $CC G$-module with character $mu$. Then
  $c(M) in {0,plus.minus 1}$, and is given by
  $ c(M)=abs(G)^(-1) sum_(x in G) mu(x^2). $
  <eq:frobenius-schur-character-square-average>
  Moreover, $M$ is orthogonal if $c(M)=1$, symplectic if $c(M)=-1$, and unitary
  if $c(M)=0$ (see @th:simple-complex-module-form-types).
]<th:frobenius-schur-indicator>

#proof[
  We first establish @eq:frobenius-schur-character-square-average for an
  arbitrary $CC G$-module $M$ affording the character $mu$. Since $x^abs(G)=1$
  for each $x in G$, the minimal polynomial of the action of $x$ on $M$ has no
  repeated factors, and hence $M$ has a basis $m_1,dots,m_d$ consisting of
  eigenvectors of $x$, with eigenvalues $xi_1,dots,xi_d$, respectively, for a
  given $x in G$. By @i:prop:symmetric-exterior-tensors-as-invariants, it
  follows easily that $M or M$ has a basis consisting of the tensors
  ${m_i times.o m_j+m_j times.o m_i:1 lt.eq i lt.eq j lt.eq d}$ while $M and M$
  has a basis consisting of the tensors
  ${m_i times.o m_j-m_j times.o m_i:1 lt.eq i<j lt.eq d}$. It follows that we
  have
  $
    cases(
      mu(x)=sum_(i=1)^d xi_i "," quad mu(x^2)=sum_(i=1)^d xi_i^2 ",",
      mu_s lr((x))=sum_(i lt.eq j) xi_i xi_j
      =sum xi_i^2+sum_(i<j) xi_i xi_j ",",
      mu_a lr((x))=sum_(i<j) xi_i xi_j ",",
    )
  $
  where $mu_s$ and $mu_a$ are the characters of $G$ afforded by $M or M$ and
  $M and M$, respectively. Thus we obtain
  $ mu(x^2)=mu_s lr((x))-mu_a lr((x)) quad "for" x in G. $
  <eq:symmetric-alternating-character-difference>
  On the other hand, by @eq:symmetric-alternating-intertwining-numbers
  $
    i_s lr((M^*,M))=(mu_s,1_G),
    quad "and" quad i_a lr((M^*,M))=(mu_a,1_G).
  $
  Therefore we obtain from @eq:symmetric-alternating-character-difference
  $ c(M)=(mu_s-mu_a,1_G)=abs(G)^(-1) sum_(x in G) mu(x^2), $
  which establishes formula @eq:frobenius-schur-character-square-average.

  #source(743)
  For an arbitrary f.d. $CC G$-module $M$, the dual $(M times.o M)^*$ of the
  inner tensor product $M times.o M$ is the vector space of bilinear forms on
  $M$, on which $G$ acts diagonally. It follows that the duals of $M or M$ and
  $M and M$ are the vector spaces of symmetric and skew-symmetric bilinear forms
  on $M$, with diagonal $G$-action. Moreover,
  $ dim_CC "inv"_G M=dim_CC "inv"_G M^* $
  for any f.g. $CC G$-module $M$.

  Now let $M$ be a simple $CC G$-module. By
  @eq:frobenius-schur-indicator-definition, we have $c(M) in {0,plus.minus 1}$,
  as noted earlier. It is clear that $c(M)=1$ if and only if
  $i_s lr((M^*,M))=dim "inv"_G lr((M or M))
  =dim_CC "inv"_G lr((M or M))^*=1$. This occurs if and only if $M$ admits a
  nonzero $G$-invariant symmetric bilinear form, and hence $M$ is orthogonal, by
  @th:simple-complex-module-form-types
  (part~@case:orthogonal-symplectic-simple-complex-module). A similar argument,
  again based on @th:simple-complex-module-form-types
  (part~@case:orthogonal-symplectic-simple-complex-module), shows that $M$ is
  symplectic if and only if $c(M)=-1$. Finally, $M$ admits no nonzero
  $G$-invariant bilinear form if and only if $c(M)=0$, and in this case $M$ is
  unitary, by @th:simple-complex-module-form-types
  (part~@case:unitary-simple-complex-module). This completes the proof.
]

For an interesting connection between the Frobenius–Schur indicators $c(M)$ of
the simple $CC G$-modules, and the set of involutions in $G$, see the Exercises.

=== Induction Theorems for Real-Valued Characters
<ss:real-valued-character-induction>

Let $M$ be a $CC G$-module with character $mu$. By
@th:frobenius-schur-real-forms, $mu$ is real-valued if and only if $M$ admits a
nondegenerate $G$-invariant bilinear form. If $M$ is a simple module, then the
character $mu$ is real-valued if and only if $M$ is either orthogonal or
symplectic; by @th:simple-complex-module-form-types. The characterization of
real-valued virtual characters is more subtle, however, and suggests the study
of the following $ZZ$-submodules of the ring of virtual characters of $G$.

We shall denote by $"ch" G$ the ring of virtual $CC$-characters of $G$; then
$"ch" G$ is a free $ZZ$-module with a basis consisting of the characters
$ "Irr" G={zeta^1,dots,zeta^s} $
afforded by a basic set of simple $CC G$-modules (see
§~@i:ss:finite-group-character-orthogonality).

#definition[
  Let $G$ be a finite group. We define two $ZZ$-submodules of $"ch" G$,
  $ "ch"_O G quad "and" quad "ch"_S G, $
  as follows. The first, $"ch"_O G$, is the $ZZ$-module generated by the
  characters of all $CC G$-modules that admit symmetric nondegenerate
  $G$-invariant bilinear forms, while the second, $"ch"_S G$, is generated by
  the characters of all $CC G$-modules that admit skew-symmetric nondegenerate
  $G$-invariant bilinear forms.
]<def:orthogonal-symplectic-character-groups>

#source(744)
By @th:frobenius-schur-real-forms
(part~@case:real-character-invariant-bilinear-form), both $"ch"_O G$ and
$"ch"_S G$ consist of real-valued virtual characters. Further properties of
$"ch"_O G$ and $"ch"_S G$ are contained in the next result, which is a nice
application of the Frobenius–Schur theory from §~@ss:real-field-rationality.

Let $"Irr" RR G$ be the set of characters of $G$ afforded by a basic set of
simple $RR G$-modules, and let $"ch" RR G$ be the subring of $"ch" G$ spanned
(over $ZZ$) by all characters in $"Irr" RR G$. As usual, $"Irr" G$ denotes the
set of irreducible complex characters of $G$. For $mu in "Irr" G$, we call $mu$
_unitary_, _orthogonal_, or _symplectic_, according to the types of simple
$CC G$-modules, given in @th:simple-complex-module-form-types.

#proposition[
  #case-list(
    numbering: "(i)",
    [#case[
      Let $zeta^i$, $zeta^j$, $zeta^k$ range over the orthogonal, unitary, and
      symplectic characters in $"Irr" G$, respectively. Then
      $
        "Irr" RR G={zeta^i} union.dot {zeta^j+overline(zeta^j)}
        union.dot {2zeta^k},
      $
      and these form a $ZZ$-basis for $"ch" RR G$.
    ]<case:real-irreducible-character-basis>],
    [#case[
      $"ch"_O G="ch" RR G$, and is a subring of $"ch" G$ containing $1_G$.
    ]<case:orthogonal-character-ring-real-forms>],
    [#case[
      We have
      $ "ch"_O G dot "ch"_S G subset.eq "ch"_S G, $
      so $"ch"_S G$ is a module over the ring $"ch"_O G$.
    ]<case:symplectic-character-module>],
  )
]<prop:real-orthogonal-symplectic-character-groups>

#proof[
  (i) The characters $zeta^i$, $zeta^j+overline(zeta^j)$, and $2zeta^k$ are
  afforded by simple $RR G$-modules, by @th:real-complex-simple-module-types,
  and are clearly linearly independent over $ZZ$. It remains to prove that an
  arbitrary character $mu$, afforded by an $RR G$-module $M$, is a $ZZ$-linear
  combination of the characters in the list. It is enough to consider the case
  of a simple $RR G$-module $M$. Let $zeta$ be the irreducible complex character
  afforded by a simple $CC G$-direct summand of $CC times.o_RR M$. Then it is
  easily shown, using @th:real-complex-simple-module-types, that $mu=zeta$,
  $zeta+overline(zeta)$, or $2zeta$, according as $zeta$ is orthogonal, unitary,
  or symplectic; this completes the proof of part (i).

  (ii) It is sufficient to prove that $"ch"_O G="ch" RR G$, since $"ch" RR G$ is
  clearly a subring of $"ch" G$ containing $1_G$. First let $mu$ be the
  character of an $RR G$-module $M$. Then $mu$ is also the character of the
  $CC G$-module $CC times.o_RR M$, which has an $RR$-form, by construction. By
  @th:frobenius-schur-real-forms
  (part~@case:real-form-symmetric-invariant-bilinear-form), $CC times.o_RR M$
  admits a nondegenerate symmetric $G$-invariant bilinear form, so
  $mu in "ch"_O G$, and we have proved that $"ch" RR G subset.eq "ch"_O G$. For
  the reverse inclusion, let $lambda$ be a character afforded by a $CC G$-module
  $L$ that admits a symmetric nondegenerate $G$-invariant bilinear form. Then
  $L$ has an $RR$-form, by @th:frobenius-schur-real-forms
  (part~@case:real-form-symmetric-invariant-bilinear-form), and it follows that
  $lambda in "ch" RR G$. Therefore $"ch" RR G="ch"_O G$, and (ii) is proved.

  (iii) Let $mu$ and $nu$ be characters afforded by $CC G$-modules $M$ and $N$,
  such that $M$ admits a symmetric nondegenerate $G$-invariant bilinear form
  $f$, and $N$ admits a skew-symmetric nondegenerate $G$-invariant bilinear form
  $g$. Then the inner tensor product $M times.o N$ admits a bilinear form
  $f times.o g$, defined by
  $
    (f times.o g)(m_1 times.o n_1,m_2 times.o n_2)
    =f(m_1,m_2)g(n_1,n_2).
  $

  #source(745)
  It is easily checked that $f times.o g$ is nondegenerate, $G$-invariant, and
  skew-symmetric. The character afforded by $M times.o N$ is $mu nu$, and we
  have shown that $mu nu in "ch"_S G$. This completes the proof that
  $"ch"_O G dot "ch"_S G subset.eq "ch"_S G$.
]

The main result of this subsection is an induction theorem for virtual
characters in $"ch"_O G$, due to Serre @bib:Serre1971. This theorem, and a
similar one for $"ch"_S G$, have arithmetical applications to Galois Gauss sums
and Artin root numbers of real-valued characters (see Martinet
@bib:Martinet1977, Serre @bib:Serre1971, and Deligne @bib:Deligne1976). Serre's
proof uses the Borel–Serre theorem on supersolvable subgroups of compact Lie
groups. We shall give a proof due to Ritter @bib:Ritter1982, based on the
Witt–Berman Induction Theorem (see §~@i:sec:induction-arbitrary-fields or
@bib:CurtisReiner1962[CR] §42).

We require a preliminary definition. By @exc:dihedral-simple-modules-orthogonal,
every irreducible complex character of a dihedral group $D_m$ (of order $2m$) is
orthogonal. Thus, if $G$ is an arbitrary group and $xi in "Irr" G$, it is
natural to call $xi$ a _dihedral character_ of $G$ if $xi$ is the pullback of an
irreducible complex character, of degree $2$, of a dihedral homomorphic image of
$G$. This means that $deg xi=2$, and $G/ker xi tilde.equiv D_m$ for some $m$. It
is then clear that all dihedral characters of $G$ are orthogonal. We now prove:

#idx("Serre's Induction Theorem")
#theorem(name: "Serre's Induction Theorem")[
  Every virtual character in $"ch"_O G$ is a $ZZ$-linear combination of induced
  characters $"ind"_H^G psi$, where $H lt.eq G$ and $psi in "Irr" RR H$ is one
  of the following types:
  #case-list(
    numbering: "(i)",
    [#case[
      $psi$ is a linear character, $psi:H arrow.r {plus.minus 1}$,
    ]<case:serre-induction-real-linear-character>],
    [#case[
      $psi=lambda+overline(lambda)$ for some linear character
      $lambda:H arrow.r CC^dot$;
    ]<case:serre-induction-complex-linear-pair>],
    [#case[
      $psi$ is a dihedral character.
    ]<case:serre-induction-dihedral-character>],
  )
]<th:serre-real-character-induction>

#proof[
  We have $"ch"_O G="ch" RR G$, by
  @prop:real-orthogonal-symplectic-character-groups. The Witt–Berman Theorem
  @i:th:witt-berman-induction, applied to $"ch" RR G$, asserts that every
  virtual character in $"ch" RR G$ is a $ZZ$-linear combination of induced
  characters of the form $"ind"_H^G mu$, where $H$ is an $RR$-elementary
  subgroup of $G$, and $mu$ is a character afforded by a simple $RR H$-module.
  By transitivity of induction, the theorem follows once we establish:
]

#lemma[
  Let $H$ be an $RR$-elementary group. Then the conclusion of
  @th:serre-real-character-induction holds for $H$.
]<lem:real-elementary-character-induction>

#proof[
  Since $"ch"_O H="ch" RR H$, it is sufficient to prove that an arbitrary
  character $mu$ afforded by a simple $RR H$-module $M$ is induced from a
  character of a subgroup of type (i)–(iii), as in
  @th:serre-real-character-induction.

  Let $Delta="End"_(RR H) M$. The simple $RR H$-module $M$ is called
  _$Delta$-primitive_ if it is impossible to express $M$ as a direct sum
  $ M=M_1 plus.o dots plus.o M_t, quad "with" t>1, $
  where the $M_i$ are nonzero $Delta$-submodules of $M$ that are permuted
  transitively by #source(746) the action of $H$. First assume that $M$ is not
  $Delta$-primitive. Then for a decomposition above, with $t>1$, we have
  $M tilde.equiv "ind"_(H_1)^H M_1$ by the Imprimitivity Theorem
  @i:prop:induced-module-criterion, where
  $ H_1="Stab"_H M_1={h in H:h M_1=M_1}. $
  It is easily checked that $M_1$ is a simple $RR H_1$-module, $H_1<H$, and
  $H_1$ is an $RR$-elementary group (since all subgroups of $RR$-elementary
  groups are $RR$-elementary).

  Therefore, using induction on $abs(H)$, we may assume that $M$ is a
  $Delta$-primitive simple $RR H$-module, on which $H$ acts faithfully. The
  $RR$-elementary group $H$ can be expressed as a semidirect product
  $ H=lr(chevron.l x chevron.r) ⋊ D, $
  where $lr(chevron.l x chevron.r)$ is a cyclic $p'$-group, $D$ is a $p$-group
  for some prime $p$, and where
  $ u x u^(-1)=x^(plus.minus 1) quad "for all" u in D $
  (see §~@i:ss:witt-berman-induction).

  Let $N$ be a maximal abelian normal subgroup of $H$ containing
  $lr(chevron.l x chevron.r)$. Then $H/N$ is a $p$-group, and we have
  $C_H lr((N))=N$. Otherwise, there is a subgroup $N_1 ⊴ H$ such that
  $N<N_1 lt.eq C_H lr((N))$ and $abs(N_1 ":" N)=p$, so $N_1$ is an abelian
  normal subgroup of $H$, contradicting the choice of $N$.

  Let $e_1,dots,e_r$ be the set of primitive idempotents in the commutative
  group algebra $RR N$. Then we have
  $ M=plus.o.big_(i=1)^r e_i M. $
  Since $N ⊴ H$, the idempotents $e_i$ are permuted by inner automorphisms, and
  hence $H$ permutes the subspaces ${e_i M:1 lt.eq i lt.eq r}$. The $H$-action
  is clearly transitive, because $M$ is a simple $RR H$-module. We also have
  $Delta e_i M subset.eq e_i M$, for each $i$, where $Delta="End"_(RR H) M$.
  Since $M$ is $Delta$-primitive, we obtain $M=e_i M$ for some $i$, and
  $e_j M=0$ if $j !=i$.

  Now let $T:RR H arrow.r "End"_RR M$ be the representation of the group algebra
  $RR H$ on $M$. Then we have $T(RR N)=T(RR N e_i)$, and $T(RR N e_i)$ is
  invariant under inner automorphisms by elements of $T(H)$, since $M=e_i M$ and
  $e_j M=0$ if $j !=i$. The Wedderburn component $RR N e_i$ of $RR N$ is a
  field, so its image $T(RR N e_i)$ is also a field, which we shall denote by
  $F$. Since $T(N)$ is a subgroup of the multiplicative group of $F$, $T(N)$ is
  cyclic and generates $F$ over the field $RR$. However, the representation $T$
  is faithful on $H$ and thus it follows that $N$ is cyclic, and that $H/N$ is
  represented faithfully by a group of field automorphisms of $F$ over $RR$,
  using the fact that $C_H lr((N))=N$. This shows that $abs(H/N)=1$ or $2$.

  If $abs(H/N)=1$, then $H$ is cyclic, and it is easily checked that the
  character $mu$ of $M$ satisfies either (i) or (ii) of
  @th:serre-real-character-induction.

  Now assume that $abs(H/N)=2$. Then $H$ has a cyclic subgroup
  $lr(chevron.l y chevron.r)$ of index $2$, so #source(747) the irreducible
  nonlinear characters of $H$ are induced from linear characters of
  $lr(chevron.l y chevron.r)$, and have degree $2$. From
  §~@ss:real-field-rationality, we have either
  #case-list(
    numbering: "(a)",
    [#case[
      $CC times.o_RR M$ is a simple $CC H$-module, or
    ]<case:real-elementary-absolutely-simple>],
    [#case[
      $CC times.o_RR M tilde.equiv V plus.o V^*$, for a symplectic or unitary
      simple $CC H$-module $V$.
    ]<case:real-elementary-complex-pair>],
  )
  In case~@case:real-elementary-absolutely-simple, $H$ is represented faithfully
  as a group of orthogonal transformations on a two-dimensional space over $RR$,
  and hence is isomorphic to a dihedral group. Then $mu$ is a dihedral character
  in this case.

  If part~@case:real-elementary-complex-pair holds, then the character of $V$
  has the form $"ind"_(lr(chevron.l y chevron.r))^H tau$ for a linear character
  $tau$ of $lr(chevron.l y chevron.r)$, and hence
  $ mu="ind"_(lr(chevron.l y chevron.r))^H lr((tau+overline(tau))). $
  This completes the proof of the lemma, and of the Serre Induction Theorem.
]

#exercises-heading

#exercise[
  Let $D_m$ be the dihedral group of order $2m$. Prove that every simple
  $CC D_m$-module is orthogonal (see @th:simple-complex-module-form-types).
]<exc:dihedral-simple-modules-orthogonal>

#hint([@exc:dihedral-simple-modules-orthogonal])[
  Let $D_m=lr(chevron.l a, b ":" a^m=(a b)^2=b^2=1 chevron.r)$. Use elementary
  linear algebra to construct the correct number of inequivalent nonlinear
  irreducible representations from $D_m$ to $O(V)$, where $O(V)$ is the
  orthogonal group on a two-dimensional real euclidean space $V$ (see also
  @i:exm:dihedral-group-algebra-reduced-norm). For another approach, use
  @exc:involution-count-frobenius-schur below.
]

#exercise[
  Let $Q_m$ denote the generalized quaternion group of order $4m$ (see
  @i:exm:dihedral-quaternion-presentations). Prove that every simple two
  dimensional $CC Q_m$-module $M$ is either symplectic or orthogonal, and is
  orthogonal if and only if $M$ is the pullback of a simple
  $CC overline(Q)_m$-module, for a dihedral quotient group $overline(Q)_m$ of
  $Q_m$.
]<exc:quaternion-simple-module-form-types>

#hint([@exc:quaternion-simple-module-form-types])[
  See @i:exm:quaternion-group-algebra-reduced-norm.
]

In Exercises
@exc:coprime-power-map-bijection–@exc:involution-count-frobenius-schur, $G$
denotes a finite group of order $n$.

#exercise[
  Prove that if $m$ is an integer such that $op("G.C.D.")(m,n)=1$, then for each
  $y in G$, the equation $x^m=y$ has a unique solution.
]<exc:coprime-power-map-bijection>

#exercise[
  Let $m$ be a positive integer, and let $theta_m lr((y))$ be the number of
  solutions of the equation $x^m=y$, for each $y in G$. Prove that $theta_m$ is
  a class function on $G$, and that
  $
    theta_m=sum_(zeta in "Irr" G) c_m lr((zeta)) zeta,
    quad "with" c_m lr((zeta))=n^(-1) sum_(x in G) zeta(x^m).
  $
]<exc:power-root-count-character-expansion>

#hint([@exc:power-root-count-character-expansion])[
  Use the orthogonality relations to show that
  $
    c_m lr((zeta))=(theta_m,zeta)=n^(-1) sum_(y in G)
    theta_m lr((y)) overline(zeta(y)), quad "for" zeta in "Irr" G.
  $
  #source(748)
  Each term in the sum can be expressed in the form
  $
    theta_m lr((y)) overline(zeta(y))
    =sum_(x in G,x^m=y) overline(zeta(x^m)),
  $
  and it follows that
  $
    n^(-1) sum_(x in G) overline(zeta(x^m))
    =n^(-1) sum_(y in G) sum_(x^m=y) overline(zeta(x^m))=c_m lr((zeta)).
  $
]

#exercise[
  Keep the notation of @exc:power-root-count-character-expansion. Note that
  $c_2 lr((zeta))=c(M)$, where $c(M)$ is the Frobenius–Schur indicator of a
  simple $CC G$-module $M$ affording $zeta$. Prove that if $t$ is the number of
  involutions in $G$, then
  $ t+1=sum_(zeta in "Irr" G) c_2 lr((zeta)) zeta(1). $
]<exc:involution-count-frobenius-schur>


