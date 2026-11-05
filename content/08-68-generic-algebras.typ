#import "main-defs.typ": *
#import "statements.typ": *
#import "note-layout.typ": reference-data
#import "main-defs.typ": number-text as reference-number-text

== Generic Algebras and Finite Coxeter Groups
<sec:generic-algebras-finite-coxeter-groups>

=== Generic Algebras and the Deformation Theorem
<ss:generic-algebras-deformation-theorem>

#source(651)
In §~@sec:hecke-algebras-bn-pairs, we have shown that the Hecke algebra
$cal(H)=cal(H)(G,B,1_B)$ of a finite group $G$ with a $B N$-pair is closely
related to the group algebra $CC W$ of the Weyl group of $G$. Following Tits
(see Bourbaki @bib:Bourbaki1968, Ch.~4), we shall make the connection more
precise. This is done by introducing the generic algebra of the Coxeter system
$(W,S)$, and using it to prove that in fact the algebras $cal(H)$ and $CC W$ are
isomorphic. These methods are also applied to parametrize the characters in
$Irr cal(H)$ in terms of the characters in $Irr W$. Thus we obtain, using
§~@i:ss:hecke-algebras, a canonical parametrization of the characters
$zeta in Irr G$ such that $(zeta,(1_B)^G) != 0$ in terms of the characters of
$W$.

#proposition[
  Let $(W,S)$ be a finite Coxeter system (see §~@ss:coxeter-groups), and let
  $S={s_1,dots,s_n}$. Let $R$ be any commutative $QQ$-algebra containing
  elements ${u_1,dots,u_n}$ such that $u_i=u_j$ whenever#footnote[We write
    $s =_W s'$ to indicate that $s$ and $s'$ are conjugate in $W$.]
  $s_i =_W s_j$. Let $A$ be a free $R$-module with a basis ${e_w:w in W}$
  indexed by the elements $w$ of $W$. Then there exists an $R$-algebra, whose
  underlying $R$-module is $A$, and whose multiplication is uniquely determined
  by the following formulas:
  $
    e_(s_i)e_w=cases(
      e_(s_i w) & "if" l(s_i w)>l(w),
      u_i e_(s_i w)+(u_i-1)e_w & "if" l(s_i w)<l(w),
    )
  $
  for all $s_i in S$, $w in W$.
] <prop:generic-coxeter-algebra-construction>

#remark(numbered: false)[
  For motivation, see Theorem @th:iwahori-hecke-basis-multiplication. That
  result, however, does not imply @prop:generic-coxeter-algebra-construction,
  since not every finite Coxeter group is the Weyl group of a finite group with
  a $B N$-pair (see the Feit–Higman Theorems
  @th:feit-higman-even-generalized-polygons–
  @th:finite-bn-pair-weyl-group-types).
]

#proof[
  (Bourbaki @bib:Bourbaki1968, Ch.~4, Ex.~23). Let $j$ be the $R$-automorphism
  of $A$ defined by $j(e_w)=e_(w^(-1))$, $w in W$, so $j^2=1$. For each $i$, let
  $P_i$ be the $R$-endomorphism of $A$ such that $P_i e_w=e_(s_i)e_w$, as in the
  statement of @prop:generic-coxeter-algebra-construction, and let
  $Q_i=j P_i j$, $1<=i<=n$. We first prove that
  $
    P_i Q_k=Q_k P_i, quad "for" 1<=i,k<=n,
  $ <eq:generic-left-right-operators-commute>

  by letting both sides of @eq:generic-left-right-operators-commute act on basis
  elements ${e_w}_(w in W)$. An easy calculation shows that the result holds for
  $l(w)=0$. Assuming $l(w)>0$, we have to prove that
  $ e_(s_i)j(e_(s_k)e_(w^(-1)))=j e_(s_k)j(e_(s_i)e_w). $
  By @th:reflection-length-cancellation-exchange, it follows that either
  $l(s_i w s_k)=l(w)$ or $l(s_i w s_k)=l(w) plus.minus 2$. In the latter case,
  the result follows easily, since the possibilities for $l(s_i w)$, $l(w s_k)$,
  etc. are uniquely determined. On the other hand, suppose that
  $l(s_i w s_k)=l(w)$. If
  #source(652)
  $l(s_i w)!=l(w s_k)$, then the possibilities again can be determined, and the
  result checked using the formulas for $e_(s_i) dot e_w$. Finally, if
  $l(s_i w s_k)=l(w)$ and $l(s_i w)=l(w s_k)$, then it follows from the results
  in §~@ss:finite-reflection-root-systems that $s_i w=w s_k$, and hence
  $s_i=attach(s_k, tl: w)$. The result @eq:generic-left-right-operators-commute
  thus holds in this case as well, using the hypothesis that $u_i=u_k$ if
  $s_i =_W s_k$.

  We next prove that if $s_(i_1) dots s_(i_l)=s_(j_1) dots s_(j_l)$ are two
  reduced products of elements of $S$, then
  $
    P_(i_1) dots P_(i_l)=P_(j_1) dots P_(j_l).
  $ <eq:generic-reduced-product-operators>

  Let both sides act on $e_w$, $w in W$, and use induction on $l(w)$. The result
  is clear if $l(w)=0$, so we may assume $l(w)>0$. Let $w=w' s_k$, $s_k in S$,
  where $l(w')<l(w)$. Then
  $ e_w=j e_(w^(-1))=j P_k j e_(w')=Q_k e_(w'), $
  and hence, by @eq:generic-left-right-operators-commute,
  $
    (P_(i_1) dots P_(i_l)-P_(j_1) dots P_(j_l))e_w
    =Q_k lr((P_(i_1) dots P_(i_l)-P_(j_1) dots P_(j_l)))e_(w')=0,
  $
  using the induction hypothesis.

  Next, define left multiplication by $e_w$, for $w in W$, by the formula

  $
    e_w e_(w')=P_(i_1) dots P_(i_l)e_(w'),
  $ <eq:generic-algebra-left-multiplication>

  if $w=s_(i_1) dots s_(i_l)$ is a reduced expression for $w$. Note that, by
  @eq:generic-reduced-product-operators, this operation is well defined.
  Further, we have
  $
    e_w e_(s_i)=Q_i e_w, quad "for all" w in W, s_i in S,
  $ <eq:generic-algebra-right-generator>

  since if $w=s_(i_1) dots s_(i_l)$ as above, then
  $
    e_w e_(s_i)=P_(i_1) dots P_(i_l)e_(s_i)
    =P_(i_1) dots P_(i_l)Q_i e_1=Q_i e_w,
  $
  by @eq:generic-left-right-operators-commute.

  An argument similar to the proof of @eq:generic-reduced-product-operators
  shows that
  $
    e_w e_(w'')=Q_(j_m) dots Q_(j_1)e_w,
  $ <eq:generic-algebra-right-multiplication>

  if $w''=s_(j_1) dots s_(j_m)$ is a reduced product of factors from $S$. The
  proof, of course, uses @eq:generic-algebra-right-generator as a start.

  The associative law
  $ (e_w e_(w'))e_(w'')=e_w lr((e_(w')e_(w''))) quad "for all" w,w',w'' in W, $
  follows at once from @eq:generic-algebra-left-multiplication and
  @eq:generic-algebra-right-multiplication, since the endomorphisms $P_i$ and
  $Q_k$ commute, by @eq:generic-left-right-operators-commute. The uniqueness of
  the multiplication is clear, and the proposition is proved.
]

#source(653)
#definition[
  Let $(W,S)$ be a finite Coxeter system, with $S={s_1,dots,s_n}$, and let $R$
  be a commutative ring containing elements ${u_1,dots,u_n}$ such that $u_i=u_j$
  whenever $s_i =_W s_j$. The $R$-algebra $A$ defined in
  @prop:generic-coxeter-algebra-construction is called the _generic algebra_ of
  the Coxeter system $(W,S)$ over the ring $R$, and its $R$-basis ${e_w:w in W}$
  is the _standard basis_ of $A$.
] <def:generic-coxeter-algebra>
#idx("Generic algebra", target: [@def:generic-coxeter-algebra])

#proposition[
  Let $A$ be the generic algebra of a Coxeter system $(W,S)$ over a commutative
  ring $R$, as in @def:generic-coxeter-algebra. Then $A$ has a presentation as
  an $R$-algebra with generators ${e_(s_i):s_i in S}$, and relations as follows:
  $
    e_(s_i)^2=u_i 1+(u_i-1)e_(s_i), quad 1<=i<=n
    quad ("quadratic relations")
  $
  and, for $1<=i,j<=n$, the homogeneous relations:
  $
    (e_(s_i)e_(s_j))^(k_(i j))=(e_(s_j)e_(s_i))^(k_(i j))
    quad "if" m_(i j)=2 k_(i j),
  $
  $
    (e_(s_i)e_(s_j))^(k_(i j))e_(s_i)
    =(e_(s_j)e_(s_i))^(k_(i j))e_(s_j)
    quad "if" m_(i j)=2 k_(i j)+1,
  $
  where $e_1=1$, and where $m_(i j)$ is the order of $s_i s_j$ in $W$.
] <prop:generic-coxeter-algebra-presentation>

The proof is exactly the same as that of Theorem
@th:iwahori-matsumoto-hecke-presentation, after checking that the defining
relations hold in $A$, using the properties of the multiplication stated in
Proposition @prop:generic-coxeter-algebra-construction.

#proposition[
  For the generic algebra $A$ of a Coxeter system $(W,S)$ there exist two
  $R$-algebra homomorphisms from $A$ to $R$, called $"IND"$ and $"SGN"$, defined
  by:
  $ "IND" e_(s_i)=u_i quad "and" quad "SGN" e_(s_i)=-1, quad 1<=i<=n. $
] <prop:generic-index-sign-homomorphisms>
#nidx(
  "$\"IND\", \"SGN\"$",
  "index and sign homomorphisms",
  target: [@prop:generic-index-sign-homomorphisms],
)

This result follows at once from the presentation of $A$ given in
@prop:generic-coxeter-algebra-presentation, since the proposed mappings preserve
the defining relations.

Suppose for the moment that $R$ is an arbitrary commutative ring, and that
$A=plus.o.big_(i=1)^n R a_i$ is an $R$-free $R$-algebra. A _specialization_ of
$R$ is a ring homomorphism $f:R arrow F$, with $F$ a field. Then $F$ becomes an
$(F,R)$-bimodule, with $R$ acting from the right via $f$. As in
§~@i:ss:tensor-products, the tensor product $F times.o_R A$ acquires the
structure of an $F$-algebra, and we have
$
  F times.o_R A=plus.o.big_(i=1)^n F a'_i, quad "where"
  a'_i=1 times.o a_i, quad 1<=i<=n.
$
#idx("Specialized algebra")
Call $F times.o_R A$ the _specialized algebra_, and denote it by $A_f$. For
$1<=i,j<=n$, we have:
$
  a_i a_j=sum_k r_(i j k)a_k
  arrow.double a'_i a'_j=sum_k f(r_(i j k))a'_k,
$ <eq:algebra-specialization-structure-constants>

where the $r$'s lie in $R$. It is sometimes convenient to view the specialized
algebra
#source(654)
$F times.o_R A$ as an $R$-algebra, using the $R$-action on $F$ via $f$. Then the
map $f:R arrow F$ can be extended to a homomorphism of $R$-algebras
$f:A arrow A_f$, such that $f(a_i)=a'_i$, $1<=i<=n$, for the bases of $A$ and
$A_f$ described above.

We can now begin to make more precise the still somewhat vague connection
between the Hecke algebra $cal(H)(G,B,1_B)$ of a finite group $G$ with a
$B N$-pair, and the group algebra $CC W$ of the Weyl group $W$ associated with
the $B N$-pair.

#proposition[
  Let $A$ be the generic algebra of a finite Coxeter system $(W,S)$, over a
  commutative ring $R$, as in @def:generic-coxeter-algebra.
  #case-list(
    numbering: "(i)",
    [#case[Assume that $F$ is a field, and that $f':R arrow F$ is a
        specialization such that $f'(u_i)=1$, $1<=i<=n$. Then
        $A_(f') tilde.equiv F W$ as $F$-algebras.]
      <case:generic-specialization-group-algebra>],
    [#case[Assume that $W$ is the Weyl group of a finite group $G$ with a
      $B N$-pair, with index parameters ${q_i}_(1<=i<=n)$ (see
      §~@ss:hecke-algebra-bn-pair-structure). Let $f'':R arrow CC$ be a
      specialization such that $f''(u_i)=q_i$, $1<=i<=n$. Then $A_(f'')$ is
      isomorphic to the Hecke algebra $cal(H)(G,B,1_B)$, as
      $CC$-algebras.] <case:generic-specialization-hecke-algebra>],
  )
] <prop:generic-group-hecke-specializations>

#remark(numbered: false)[
  Specializations $f'$ and $f''$, as in
  @case:generic-specialization-group-algebra and
  @case:generic-specialization-hecke-algebra, need not exist for an arbitrary
  commutative ring $R$. When $F$ has characteristic zero, a sufficient condition
  for them to exist is that $R=QQ[u_1,dots,u_n]$, where the ${u_i}$ are
  indeterminates over $QQ$ such that $u_i=u_j$ if $s_i =_W s_j$.
]

#proof[
  @case:generic-specialization-group-algebra. By
  @prop:generic-coxeter-algebra-construction and
  @eq:algebra-specialization-structure-constants, the specialized basis elements
  $e'_w=f'(e_w)$, $w in W$, multiply according to the rule
  $e'_(s_i) e'_w=e'_(s_i w)$, for all $s_i in S$ and $w in W$, since both
  formulas in @prop:generic-coxeter-algebra-construction give the same result
  when $u_i arrow 1$. It is then clear that the map $w mapsto e'_w$ extends to
  an isomorphism $F W tilde.equiv A_(f')$.

  @case:generic-specialization-hecke-algebra. This time we have
  $
    e''_(s_i) e''_w=cases(
      e''_(s_i w) & "if" l(s_i w)>l(w),
      q_i e''_(s_i w)+(q_i-1)e''_w & "if" l(s_i w)<l(w),
    )
  $
  for all $s_i in S$ and $w in W$, where ${e''_w}$ are the specialized basis
  elements. By Theorem @th:iwahori-matsumoto-hecke-presentation, there exists a
  homomorphism of $CC$-algebras $cal(H) arrow A_(f'')$ such that
  $a_(s_i) mapsto e''_(s_i)$, $1<=i<=n$. The homomorphism is clearly surjective,
  and $dim_CC cal(H)=dim_CC A_(f'')$, so we have $cal(H) tilde.equiv A_(f'')$,
  as required.
]

#corollary[
  Let $(W,S)$ be a finite Coxeter system, and let $R$ be a commutative integral
  domain containing elements ${u_i}$ such that $u_i=u_j$ if $s_i =_W s_j$ in
  $S$. Let $K$ be the quotient field of $R$. Suppose there exists a
  specialization $f':R arrow QQ$ for which $f'(u_i)=1$ for each $i$. Then
  $A^K=K times.o_R A$ is a separable $K$-algebra.
] <cor:generic-algebra-separability>

#proof[
  Let $T$ be the trace form on $A^K$ defined by
  $ T(a,b)=T_(A slash K)(a b). $
  By Exercise @i:exc:separable-trace-form, $A^K$ is separable if $T$ is
  nondegenerate. For any specialization
  #source(655)
  $f:R arrow F$ to a field $F$, we have $T(e_x,e_y) in R$ for all $x,y in W$, by
  @prop:generic-coxeter-algebra-construction. It follows directly that
  $ f(T(e_x,e_y))=T_f lr((e'_x,e'_y)) quad "for all" x,y in W, $
  where $T$ and $T_f$ are the trace forms on $A^K$ and $A_f$, respectively, and
  ${e'_x:x in W}$ are the specialized basis elements in $A_f$. In particular,
  for the specialization $f':R arrow QQ$ as in
  @cor:generic-algebra-separability, we have $A_(f') tilde.equiv QQ W$ by
  @prop:generic-group-hecke-specializations, and $T_(f')$ is the trace form on
  $QQ W$. The bilinear form $T_(f')$ is nondegenerate on $QQ W$ by the
  discussion of Example @i:exm:associative-form-examples(c), and hence $T$ is
  nondegenerate on $A^K$, completing the proof.
]

Our aim is to compare the structures of the specialized algebras ${A_f}$ of a
generic algebra $A$ as $f$ varies over specializations for which the specialized
algebras $A_f$ are separable.

#definition[
  Let $B$ be a separable algebra over a field $F$. The _numerical invariants_ of
  $B$ are the dimensions of the simple $B^(F^*)$-modules, where $F^*$ is an
  algebraic closure of $F$, and $B^(F^*)=F^* times.o_F B$.
] <def:separable-algebra-numerical-invariants>
#idx(
  "Numerical invariants",
  target: [@def:separable-algebra-numerical-invariants],
)

Clearly two separable algebras over $F$ become isomorphic when the field is
extended to $F^*$ if and only if they have the same numerical invariants (see
§~@i:ss:separable-algebras-modules).

We now give three lemmas leading to the proof of Tits's Deformation Theorem. Our
approach follows Steinberg @bib:Steinberg1967 (see also Bourbaki
@bib:Bourbaki1968, p.~56, Ex.~26).

#lemma[
  Let $B=plus.o.big_(i=1)^n L b_i$ be a split semisimple algebra over an
  algebraically closed field $L$. Let
  $ L'=L[t_1,dots,t_n], quad tilde(L)=L(t_1,dots,t_n), $
  where the ${t_i}$ are indeterminates over $L$. Set
  $
    b=sum_(i=1)^n t_i b_i in B^(tilde(L)), quad "where"
    B^(tilde(L))=plus.o.big tilde(L)b_i.
  $
  We call $b$ a “general element” of $B$; its characteristic polynomial
  $P(X) in tilde(L)[X]$ can be computed by letting $b$ act on the basis elements
  ${b_j}$, so $P(X) in L'[X]$. Let
  $ P(X)=product P_i lr((X))^(p_i) $
  be the factorization of $P(X)$ into prime powers in $L'[X]$. Then we have:
  #case-list(
    numbering: "(i)",
    [#case[The multiplicities ${p_i}$ are the numerical invariants of $B$.]
      <case:general-element-numerical-invariants>],
    [#case[$p_i=deg P_i lr((X))$ for all $i$.]
      <case:general-element-factor-degrees>],
    [#case[Let $-phi_i lr((t_1,dots,t_n)) in L'$ be the coefficient of
        $X^(p_i-1)$ in $P_i lr((X))$. Then the map
        $
          sum xi_j b_j mapsto phi_i lr((xi_1,dots,xi_n)),
          quad "where each" xi_j in L,
        $
        #source(656)
        is an irreducible character of $B$, and all irreducible characters of
        $B$ are obtained in this way.]
      <case:general-element-factor-characters>],
    [#case[Let $P(X)=product Q_j lr((X))^(q_j)$ be another factorization of
        $P(X)$, with the ${Q_j lr((X))}$ monic in $L'[X]$, and
        $q_j=deg Q_j lr((X))$, for each $j$. Then the polynomials
        ${Q_j lr((X))}$ are distinct, and coincide with the polynomials
        ${P_i lr((X))}$.]
      <case:general-element-factorization-uniqueness>],
  )
] <lem:general-element-characteristic-polynomial>

#proof[
  We leave it to the reader to check that the statements of the lemma are
  independent of the choice of the basis and the set of indeterminates used to
  define a general element. For the proof of
  @case:general-element-numerical-invariants–
  @case:general-element-factor-characters, we may assume that $B=M_n lr((L))$ is
  a split simple $L$-algebra, with $L$-basis given by the $n^2$ matrix units
  ${E_(i j)}$. Denoting the indeterminates by ${t_(i j)}$, the general element
  $b in B^(tilde(L))$ is represented by the matrix
  $ bold(b)=sum_(i,j=1)^n t_(i j)E_(i j). $
  The matrix $bold(b)$ is obtained from the action of $b$ on an $L$-basis of a
  simple left $B$-module $V$. Therefore
  $
    "char. pol."_(B^(tilde(L)) slash tilde(L)) b
    =("char. pol." bold(b))^n,
  $
  and
  $ "char. pol." bold(b)=det(X 1-(t_(i j))) in L'[X]. $
  To complete the proof of @case:general-element-numerical-invariants and
  @case:general-element-factor-degrees, we need only show that
  $"char. pol." bold(b)$ is irreducible in $L'[X]$. Any proper factorization of
  this polynomial remains proper after specializing the indeterminates
  ${t_(i j)}$. In particular, a specialization of $"char. pol." bold(b)$ is
  given by
  $
    "char. pol." mat(
      delim: "[",
      0, 0, dots, 0, t;
      1, 0, dots, 0, 0;
      0, 1, dots, 0, 0;
      dots.v, , , , dots.v;
      0, 0, dots, 1, 0;
    )=X^n-t,
  $
  with $t$ an indeterminate. But $X^n-t$ is irreducible by Eisenstein's
  criterion, so it follows that $"char. pol." bold(b)$ must also be irreducible.

  Next, suppose that
  $
    "char. pol." bold(b)=X^n-psi({t_(i j)})X^(n-1)
    +dots+(-1)^n det(t_(i j)).
  $
  Then a simple left $B$-module $V$ affords a character $phi$ of $B$, given by
  $
    phi:sum xi_(i j)E_(i j) mapsto
    "trace of" sum xi_(i j)E_(i j)=psi({xi_(i j)}).
  $
  This implies @case:general-element-factor-characters at once.

  #source(657)
  @case:general-element-factorization-uniqueness. Returning to the general
  situation, let
  $ P(X)=product P_i lr((X))^(p_i)=product Q_j lr((X))^(q_j), $
  where the first factorization is as given above, and where
  $q_j=deg Q_j lr((X))$ for each $j$. But the ${P_i lr((X))}$ are distinct
  irreducible polynomials, since they involve different indeterminates, and so
  $P_i lr((X))$ occurs exactly $p_i$ times as factor of $P(X)$. If now
  $P_i lr((X)) divides Q_j lr((X))$ for some $j$, then $deg Q_j lr((X))>=p_i$.
  Hence if $Q_j lr((X))!=P_i lr((X))$, $P_i lr((X))$ would occur more than $p_i$
  times in $P(X)$. Thus the ${Q_j}$ are a permutation of the ${P_i}$, as
  claimed, and the lemma is proved.
]

The next two lemmas are standard results in commutative algebra.

#lemma[
  Let $R$ be an integral domain with quotient field $K$, and let $K^*$ be an
  algebraic closure of $K$, and $R^*$ the integral closure of $R$ in $K^*$.
  Then, for any set of indeterminates ${t_1,dots,t_n}$ over $K^*$,
  $R^*[t_1,dots,t_n]$ is the integral closure of $R[t_1,dots,t_n]$ in
  $K^*[t_1,dots,t_n]$.
] <lem:polynomial-integral-closure>

For a proof, see Bourbaki (@bib:Bourbaki1964, p.~19, Prop.~13).

#lemma[
  Keep the above notation, and let $f$ be a homomorphism of $R$ into a field
  $F$. Then $f$ can be extended to a homomorphism $f^*:R^* arrow F^*$, where
  $F^*$ is an algebraic closure of $F$.
] <lem:specialization-integral-closure-extension>

For a proof, see Atiyah–MacDonald (@bib:Atiyah1969, Ex.~5.2).

#theorem(name: "Deformation Theorem", title: [Tits])[
  Let $R$ be an integral domain, $K$ its field of quotients, and let
  $f:R arrow F$ be a homomorphism of $R$ into a field $F$. Let $A$ be an
  $R$-algebra with a finite basis over $R$, let $A^K$ be the $K$-algebra
  $K times.o_R A$, and $A_f$ the specialized $F$-algebra $F times.o_R A$ (see
  the discussion following @prop:generic-index-sign-homomorphisms). If both
  $A^K$ and $A_f$ are separable algebras, then they have the same numerical
  invariants.
] <th:tits-deformation>
#idx("Deformation Theorem of Tits", target: [@th:tits-deformation])

#proof[
  Let $K^*$ and $F^*$ be algebraic closures of $K$ and $F$, respectively, and
  let $R^*$ be the integral closure of $R$ in $K^*$. Let $n=dim_K A^K$, and let
  ${t_1,dots,t_n}$ and ${t'_1,dots,t'_n}$ be sets of indeterminates over $K^*$
  and $F^*$, respectively. Let #numbered-block[
    $
      R'=R[t_1,dots,t_n], quad R^(*')=R^*[t_1,dots,t_n],
      quad K^(*')=K^*[t_1,dots,t_n],
    $
    $ F'=F[t'_1,dots,t'_n], quad F^(*')=F^*[t'_1,dots,t'_n]. $
  ] <eq:deformation-polynomial-coefficient-rings>
  Let $A=plus.o.big_(i=1)^n R a_i$; then we may identify ${a_1,dots,a_n}$ with a
  $K^*$-basis of $A^(K^*)$, and $a=sum_(i=1)^n t_i a_i$ with a general element
  of $A^(K^*)$. A general element of the specialized algebra $A_f$ is
  $a'=sum_(i=1)^n t'_i a'_i$, where $a'_i=1 times.o a_i$, $1<=i<=n$.

  Let $P(X)="char. pol." a$, and $P'(X)="char. pol." a'$. Then $P(X) in R'[X]$
  since the structure constants of $A$ are in $R$, and $P'(X) in F'[X]$. We may
  extend $f$ to a homomorphism from $R'[X]$ to $F'[X]$, also denoted by $f$, by
  setting $f(t_i)=t'_i$,
  #source(658)
  $1<=i<=n$, and $f(X)=X$. By @eq:algebra-specialization-structure-constants, it
  follows that
  $ f(P(X))=P'(X). $ <eq:deformation-characteristic-polynomial-specialization>

  Now consider the factorization of $P(X)$ described in Lemma
  @lem:general-element-characteristic-polynomial. We have
  $P(X)=product P_i lr((X))^(p_i)$, where the factors $P_i lr((X)) in K^(*')[X]$
  for each $i$. Since $P(X)$ is monic, its roots are integral over $R'$. The
  coefficients of the factors ${P_i lr((X))}$, which already belong to $K^(*')$,
  are symmetric functions of the roots of $P(X)$, and hence are also integral
  over $R'$. Thus $P_i lr((X)) in R^(*')[X]$ for each $i$, by Lemma
  @lem:polynomial-integral-closure.

  We next extend $f:R arrow F$ to a homomorphism $f^*:R^* arrow F^*$, by
  @lem:specialization-integral-closure-extension. Then $f:R'[X] arrow F'[X]$
  extends to a homomorphism $f^*:R^(*')[X] arrow F^(*')[X]$. Using
  @eq:deformation-characteristic-polynomial-specialization, we obtain
  $ f^*(P(X))=P'(X)=product f^*(P_i lr((X)))^(p_i), $
  where each polynomial $f^*(P_i lr((X))) in F^(*')[X]$. Since
  $p_i=deg P_i lr((X))$ for each $i$, we also have $p_i=deg f^*(P_i lr((X)))$
  for each $i$. The multiplicities ${p_i}$ are the numerical invariants of $A^K$
  by @case:general-element-numerical-invariants[#context reference-number-text(
    "("
      + reference-data(<lem:general-element-characteristic-polynomial>).text
      + reference-data(<case:general-element-numerical-invariants>)
        .text
        .trim(regex("[()]"))
      + ")",
  )], and are also the numerical invariants of $A_f$ by
  @case:general-element-factorization-uniqueness[#context reference-number-text(
    "("
      + reference-data(<lem:general-element-characteristic-polynomial>).text
      + reference-data(<case:general-element-factorization-uniqueness>)
        .text
        .trim(regex("[()]"))
      + ")",
  )]. This completes the proof.
]

#corollary[
  Keeping the notation of @th:tits-deformation, assume that both $A^K$ and $A_f$
  are separable algebras. Let $R^*$ be the integral closure of $R$ in $K^*$, and
  let $f^*:R^* arrow F^*$ be an extension of $f$ (see Lemma
  @lem:specialization-integral-closure-extension). Let $mu in Irr A^(K^*)$. Then
  $ mu(a_i) in R^*, quad 1<=i<=n. $
  For each irreducible character $mu in Irr A^(K^*)$, define an $F^*$-linear map
  $mu_(f^*):A_f^(F^*) arrow F^*$, by setting
  $
    mu_(f^*)(a'_i)=f^*(mu(a_i)), quad "where" a'_i=1 times.o a_i,
    quad "for" 1<=i<=n.
  $
  Then $mu_(f^*) in Irr A_f^(F^*)$, and the map $mu mapsto mu_(f^*)$ is a
  bijection from $Irr A^(K^*)$ to $Irr A_f^(F^*)$ (which depends on the choice
  of $f^*$).
] <cor:deformation-character-specialization>

#proof[
  We shall use the notation from the proof of @th:tits-deformation. Let
  $mu in Irr A^(K^*)$. By Lemma
  @case:general-element-factor-characters[#context reference-number-text(
    "("
      + reference-data(<lem:general-element-characteristic-polynomial>).text
      + reference-data(<case:general-element-factor-characters>)
        .text
        .trim(regex("[()]"))
      + ")",
  )], we have
  $
    mu(sum xi_i a_i)=phi_i lr((xi_1,dots,xi_n))
    quad "for all" sum xi_i a_i in A^(K^*), quad xi_i in K^*,
  $
  where $-phi_i$ is a coefficient of some irreducible factor $P_i lr((X))$ of
  $P(X)$. In the proof of @th:tits-deformation, it was shown that each
  $P_i lr((X)) in R^(*')[X]$. It follows that $phi_i in R^(*')$, and hence
  $mu(a_i) in R^*$ for each $i$. From the proof of @th:tits-deformation, we also
  know that $f^*(P_i lr((X)))$ is a monic irreducible factor of the
  characteristic polynomial $P'(X)$ of the general element of $A_f$. Then
  $-f^*(phi_i) in F^(*')$, and is the coefficient of $f^*(P_i lr((X)))$
  corresponding to $-phi_i$. Using
  @case:general-element-factor-characters[#context reference-number-text(
    "("
      + reference-data(<lem:general-element-characteristic-polynomial>).text
      + reference-data(<case:general-element-factor-characters>)
        .text
        .trim(regex("[()]"))
      + ")",
  )] again, we deduce that
  $
    sum xi_i a'_i mapsto f^*(phi_i)(xi_1,dots,xi_n)
    quad "for all" xi_i in F^*
  $
  #source(659)
  is an irreducible character of $A_f^(F^*)$, which we shall denote by
  $mu_(f^*)$. From its definition, we have
  $ mu_(f^*)(a'_i)=f^*(mu(a_i)). $
  The last statement follows from
  @lem:general-element-characteristic-polynomial. This completes the proof.
]

We are now in a position to prove:

#theorem[
  Let $G$ be a finite group with a $B N$-pair, and let $(W,S)$ be the Weyl group
  of $G$. Let $cal(H)$ be the Hecke algebra $cal(H)(G,B,1_B)$. Then there exists
  an isomorphism of $CC$-algebras:
  $ cal(H) tilde.equiv CC W. $
] <th:hecke-algebra-weyl-group-isomorphism>

#proof[
  Let $A$ be the generic ring of the Coxeter system $(W,S)$ over the commutative
  integral domain $R=QQ[u_1,dots,u_n]$, where $S={s_1,dots,s_n}$, and the
  ${u_i}$ are indeterminates over $QQ$ such that $u_i=u_j$ if $s_i =_W s_j$.
  Then, putting $F=CC$ in @prop:generic-group-hecke-specializations, the
  specializations $f':R arrow CC$ and $f'':R arrow CC$ in parts
  @case:generic-specialization-group-algebra and
  @case:generic-specialization-hecke-algebra of
  @prop:generic-group-hecke-specializations are defined, and we have
  $ A_(f') tilde.equiv CC W quad "and" quad A_(f'') tilde.equiv cal(H), $
  by @prop:generic-group-hecke-specializations. By Corollary
  @cor:generic-algebra-separability, $A^K$ is a separable $K$-algebra, where $K$
  is the quotient field of $R$. Both of the specialized algebras $CC W$ and
  $cal(H)$ are also separable. By the Deformation Theorem, the algebras $cal(H)$
  and $CC W$ have the same numerical invariants, and hence are isomorphic, since
  $CC$ is algebraically closed.
]

#remarks(numbered: false)[
  + Keep the notation of @th:tits-deformation. With suitable hypotheses on $R$,
    it is possible to define a decomposition map $d$ from $G_0(K^* times.o_R A)$
    to $G_0(F^* times.o_F A_f)$ and a Cartan map $c$ from
    $K_0(F^* times.o_F A_f)$ to $G_0(F^* times.o_R A_f)$ so that
    $C=attach(D, tl: t)D$, where $C$ is the Cartan matrix and $D$ is the
    decomposition matrix. If $A_f$ is separable, then $C$ is the identity
    matrix, $D$ is a permutation matrix, and
    @cor:deformation-character-specialization and @th:tits-deformation both
    follow as in the proof of @i:cor:prime-to-p-brauer-ordinary-characters. The
    elementary proof of @th:tits-deformation given above, however, applies to a
    more general situation.
  + It is possible to construct explicitly an isomorphism
    $cal(H) tilde.equiv CC W$ (see Lusztig @bib:Lusztig1981).
]

=== Parametrization of Characters in $(1_B)^G$
<ss:hecke-character-parametrization>

Finite groups of Lie type do not occur in isolation; they are members of
infinite families with a fixed Weyl group, parametrized by finite fields
${F_q}$. For example, the general linear groups ${GL_(n+1)(F_q)}$, for fixed
$n$, form such a family, all having the Weyl group $S_(n+1)$, by
§~@ss:bn-pair-examples. Our first task will be to axiomatize the concept of
families of groups with $B N$-pairs.

#source(660)
The main objective of representation theory for such a family is to determine
all the irreducible representations and characters at once, by some sort of
generic method. This ambitious plan is now surprisingly near completion (see
Carter @bib:Carter1985).

A significant step in this program is the parametrization of irreducible
characters in $(1_B)^G$ in terms of characters of the Weyl group. The existence
and properties of this parametrization are the main objectives of this
subsection.

#definition[
  Let $(W,S)$ be a finite Coxeter system. A system $scr(S)$ of finite groups
  with $B N$-pairs of type $(W,S)$ consists of the following data:
  #case-list(
    numbering: "(i)",
    [#case[An infinite set $"CP"$ of prime powers ${q}$, called _characteristic
      powers_.] <case:bn-system-characteristic-powers>],
    [#case[For each $q in "CP"$, there exists a finite group $G(q) in scr(S)$
        with a $B N$-pair, with Weyl group $(W,S)$.]
      <case:bn-system-groups>],
    [#case[There exists a set of positive integers ${c_s}_(s in S)$ such that
        for each $q in "CP"$, the index parameters (see
        @eq:bn-pair-index-parameters) of $G(q)$ are given by
        $
          abs(B(q):attach(B(q), tl: s) inter B(q))=q^(c_s),
          quad "for each" s in S,
        $
        where $B(q)$ is a standard Borel subgroup of $G(q)$.]
      <case:bn-system-index-exponents>],
  )
] <def:bn-pair-group-system>
#idx(
  "System of finite groups with BN-pairs",
  target: [@def:bn-pair-group-system],
)

#remarks(numbered: false)[
  + By Corollary @cor:conjugate-simple-reflections-equal-parameters, it follows
    that $c_s=c_(s')$, for $s,s' in S$, if $s =_W s'$.
  + Let $scr(S)={GL_(n+1)(F_q)}$, for a fixed $n$, where ${F_q}$ ranges over all
    finite fields. Then $scr(S)$ is a system, as in @def:bn-pair-group-system,
    for which $"CP"$ is the set of all prime powers, $c_s=1$ for all $s in S$,
    and for each $q in "CP"$,
    $ G(q)=GL_(n+1)(F_q). $
  + Twisted types of Chevalley groups give rise to systems for which not all the
    integers ${c_s}$ in
    @case:bn-system-index-exponents[#context reference-number-text(
      "("
        + reference-data(<def:bn-pair-group-system>).text
        + reference-data(<case:bn-system-index-exponents>)
          .text
          .trim(regex("[()]"))
        + ")",
    )] are equal to $1$ (see Carter @bib:Carter1972b, Steinberg
    @bib:Steinberg1967).
]

Before we come to the main results, we require some additional properties of the
index homomorphism $"IND":A arrow R$ defined in
@prop:generic-index-sign-homomorphisms. We let $(W,S)$ be a fixed Coxeter
system, $S={s_1,dots,s_n}$, and let $R=QQ[u_1,dots,u_n]$ be the polynomial ring
over $QQ$, with indeterminates ${u_i}$ such that $u_i=u_j$ if $s_i =_W s_j$. We
also recall the definition of the generic algebra $A$ of $(W,S)$ over $R$ (see
@def:generic-coxeter-algebra).

#lemma[
  Let $scr(S)={G(q)}$ be a system of finite groups with $B N$-pairs of type
  $(W,S)$, and let $A$ be the generic algebra of the Coxeter system $(W,S)$ over
  the ring $R=QQ[u_1,dots,u_n]$. Let $J subset.eq S$, and let $W_J$ be the
  parabolic subgroup of $W$ corresponding to $J$ (see
  §~@ss:finite-coxeter-parabolic-subgroups). Then the following statements hold:
  #case-list(
    numbering: "(i)",
    [#case[Let $X$ be a nonempty subset of $W$ such that $W_J X=X$, and let
        $e_X=sum_(w in X)e_w$, where ${e_w}$ is the standard basis of $A$. Then
        $ e_(s_i)e_X="IND"(e_(s_i))e_X quad "for all" s_i in J. $]
      <case:generic-parabolic-stable-subset-sum>],
    [#case[#source(661)
        Let $epsilon_J=sum_(w in W_J)e_w$. Then $"IND" epsilon_J != 0$, and
        $ epsilon_J^2=("IND" epsilon_J)epsilon_J. $
        In particular, $("IND" epsilon_J)^(-1)epsilon_J$ is an idempotent in
        $A^K$, where $K$ is the quotient field of $R$.]
      <case:generic-parabolic-idempotent>],
    [#case[Let $G(q) in scr(S)$, let $B=B(q)$ be a Borel subgroup of $G(q)$, and
        let $P_J >= B$ be the standard parabolic subgroup of $G(q)$
        corresponding to $J$ (see §~@ss:bn-pair-parabolic-subgroups). Let
        $f:R arrow CC$ be the specialization defined by $f(u_i)=q^(c_i)$,
        $1<=i<=n$, where ${q^(c_i)}$ are the index parameters of $G(q)$, as in
        @case:bn-system-index-exponents[#context reference-number-text(
          "("
            + reference-data(<def:bn-pair-group-system>).text
            + reference-data(<case:bn-system-index-exponents>)
              .text
              .trim(regex("[()]"))
            + ")",
        )]. Then
        $ abs(P_J ":" B)=f("IND" epsilon_J). $]
      <case:generic-parabolic-index>],
  )
] <lem:generic-parabolic-sums>

#proof[
  @case:generic-parabolic-stable-subset-sum. For each $s_i in J$, there is a
  partition
  $ X=X_+(s_i) union X_-(s_i), $
  where
  $ X_±(s_i)={w in X:l(s_i w) ≷ l(w)}. $
  From the properties of the length function $l(w)$, we then have
  $ s_i X_+(s_i)=X_-(s_i) quad "and" quad s_i X_-(s_i)=X_+(s_i). $
  Put
  $
    e_(X,+)=sum_(w in X_+(s_i))e_w, quad
    e_(X,-)=sum_(w in X_-(s_i))e_w.
  $
  By @prop:generic-coxeter-algebra-construction, we then have
  $
    e_(s_i)e_(X,+)=e_(X,-), quad
    e_(s_i)e_(X,-)=u_i e_(X,+)+(u_i-1)e_(X,-).
  $
  Since $e_X=e_(X,+)+e_(X,-)$, we obtain
  $ e_(s_i)e_X=u_i e_X, $
  which is part @case:generic-parabolic-stable-subset-sum. Part
  @case:generic-parabolic-idempotent is left as an exercise for the reader.

  @case:generic-parabolic-index. We have
  $ P_J=union.big_(w in W_J) B w B. $
  Then
  $
    abs(P_J ":" B)=sum_(w in W_J)abs(B w B) slash abs(B)
    =sum_(w in W_J)abs(B ":" attach(B, tl: w) inter B)
    =sum_(w in W_J)op("ind")_B dot(w),
  $
  where $dot(w) in N$ is a coset representative corresponding to
  $w in N slash T$. By Exercise @i:exc:hecke-index-homomorphism,
  #source(662)
  there is a homomorphism of $CC$-algebras
  $op("ind"):cal(H)(G(q),B,1_B) arrow CC$ such that
  $op("ind")a_w=op("ind")_B dot(w)$, where $a_w$ is the standard basis element
  of $cal(H)(G,B,1_B)$ defined by the double coset $B w B$. If
  $w=s_((1)) dots s_((k))$ is a reduced expression for $w$, with each
  $s_((i)) in S$, then we have
  $
    e_w=e_(s_((1))) dots e_(s_((k))) quad "in" A
    quad ("by" #[@prop:generic-coxeter-algebra-construction])
  $
  and
  $
    a_w=a_(s_((1))) dots a_(s_((k))) quad "in" cal(H)(G(q),B,1_B)
    quad ("by" #[@th:iwahori-hecke-basis-multiplication]).
  $
  Moreover, writing $u_(s_j)=u_j$, we have $op("ind")a_(s_((i)))=
  abs(B ":" attach(B, tl: s_((i))) inter B)=q^(c_(s_((i))))$, for $1<=i<=k$.
  Therefore $f(u_(s_((i))))=op("ind")a_(s_((i)))$, $1<=i<=k$, for the
  specialization $f$ defined above, and we obtain
  $
    f("IND" e_w)=product_i f("IND" e_(s_((i))))
    =product_i op("ind")a_(s_((i)))=op("ind")a_w.
  $
  Combining these facts, we obtain
  $ f("IND" epsilon_J)=sum_(w in W_J)f("IND" e_w)=abs(P_J ":" B), $
  as required.
]

Keep the notation introduced earlier in this subsection. In addition, let
$
  K= "the quotient field of" R=QQ[u_1,dots,u_n],
$
$ K^*="an algebraic closure of" K, $
$ R^*="the integral closure of" R "in" K^*, $
$ f':R arrow CC="the specialization such that" f'(u_i)=1, quad 1<=i<=n, $
$
  f'':R arrow CC="the specialization such that" f''(u_i)=q^(c_i),
  quad 1<=i<=n,
$
where ${q^(c_i)}$ are the index parameters of the group $G(q) in scr(S)$,
$
  (f')^*,(f'')^*="extensions of" f' "and" f''
  "to homomorphisms from" R^* "to" CC
$
(see Lemma @lem:specialization-integral-closure-extension).

#theorem[
  Let $G(q) in scr(S)$. There exists a bijection $phi arrow.l.r zeta_(phi,q)$
  from $Irr W$ to ${zeta in Irr G(q):(zeta,(1_B)^G)>0}$. This bijection depends
  only on the choices of the extensions $(f')^*$ and $(f'')^*$, and has the
  following property. For each $J subset.eq S$, let $W_J$ and $P_J lr((q))$ be
  the corresponding parabolic subgroups of $W$ and $G(q)$, respectively. Then
  $ (zeta_(phi,q),(1_(P_J lr((q))))^(G(q)))=(phi,(1_(W_J))^W). $
  In particular,
  $ (zeta_(phi,q),(1_(B(q)))^(G(q)))=deg phi, quad "for all" phi in Irr W. $
] <th:hecke-character-parametrization-parabolic-multiplicities>

#proof[
  By @prop:generic-group-hecke-specializations, we have
  $A_(f') tilde.equiv CC W$ and $A_(f'') tilde.equiv cal(H)(G(q),B(q),1)$. By
  @cor:deformation-character-specialization, there exist bijections, depending
  only on the choice of the extensions $(f')^*$ and
  #source(663)
  $(f'')^*$:
  $
    Irr A^(K^*) arrow.l.r Irr A_(f') quad "and" quad
    Irr A^(K^*) arrow.l.r Irr A_(f'').
  $
  Let $phi in Irr W$, let $mu_phi in Irr A^(K^*)$ correspond to $phi$ in the
  first bijection, and let $mu_(phi,q) in Irr A_(f'')$ correspond to $mu_phi$ in
  the second bijection.

  By the proof of @prop:generic-group-hecke-specializations, the isomorphism
  $A_(f'') tilde.equiv cal(H)$ carries the basis elements ${e''_w:w in W}$ of
  $A_(f'')$ to the standard basis elements ${a_w:w in W}$ of $cal(H)$, where
  $ a_w=abs(B(q))^(-1)sum_(x in B(q) w B(q))x, quad "for each" w in W, $
  as in §~@i:ss:hecke-algebras. By Theorem @i:th:hecke-character-correspondence,
  there exists a unique character $zeta_(phi,q) in Irr G(q)$ such that
  $(zeta_(phi,q),(1_(B(q)))^(G(q)))>0$, and whose restriction to $cal(H)$ is
  given by
  $
    zeta_(phi,q)(a_w)=mu_(phi,q)(e''_w), quad "for all" w in W.
  $ <eq:generic-hecke-character-correspondence>

  The correspondence $phi arrow.l.r zeta_(phi,q)$ is the bijection described in
  the statement of the theorem, and we now have to check the statement about
  multiplicities.

  Let $J subset.eq S$, and let $epsilon_J=sum_(w in W_J)e_w$, as in
  @case:generic-parabolic-idempotent[#context reference-number-text(
    "("
      + reference-data(<lem:generic-parabolic-sums>).text
      + reference-data(<case:generic-parabolic-idempotent>)
        .text
        .trim(regex("[()]"))
      + ")",
  )]. Then $("IND" epsilon_J)^(-1)epsilon_J$ is an idempotent in $A^K$, on which
  the irreducible characters $mu_phi$ of $A^(K^*)$ take nonnegative integer
  values $m(phi,J)$. Therefore, for $J subset.eq S$ and $phi in Irr W$, we have
  $ mu_phi lr((epsilon_J))=m(phi,J)"IND" epsilon_J, $
  for some nonnegative integer $m(phi,J)$. Upon applying the specialization
  $(f'')^*$ to this equation, and using
  @cor:deformation-character-specialization and
  @eq:generic-hecke-character-correspondence, we obtain
  $
    zeta_(phi,q)lr((sum_(w in W_J)a_w))=mu_(phi,q)(epsilon_J)
    =m(phi,J)abs(P_J lr((q)):B(q)),
  $
  since $f''("IND" epsilon_J)=abs(P_J lr((q)):B(q))$ by
  @case:generic-parabolic-index[#context reference-number-text(
    "("
      + reference-data(<lem:generic-parabolic-sums>).text
      + reference-data(<case:generic-parabolic-index>).text.trim(regex("[()]"))
      + ")",
  )]. Since
  $ sum_(w in W_J)a_w=abs(B(q))^(-1)sum_(g in P_J lr((q)))g, $
  it follows that
  $ m(phi,J)=zeta_(phi,q)lr((abs(P_J lr((q)))^(-1)sum_(g in P_J lr((q)))g)). $
  By @i:prop:hecke-character-multiplicity, we then obtain
  $ m(phi,J)=(zeta_(phi,q),(1_(P_J lr((q))))^(G(q))). $
  A similar argument, which we leave to the reader, shows that also
  $ m(phi,J)=(phi,(1_(W_J))^W), $
  and the theorem is proved.
]

#source(664)
#remarks(numbered: false)[
  By Theorem @th:steinberg-character-sign-correspondence(iii), the Steinberg
  character $upright("St")_G$ of any one of the groups $G=G(q)$ in $scr(S)$ has
  the following multiplicities in the permutation characters $(1_(P_J))^G$,
  $J subset.eq S$:
  $
    (upright("St")_G,(1_B)^G)=1, quad (upright("St")_G,(1_(P_J))^G)=0,
    quad J!=emptyset.
  $
  Since $upright("St")_G$ is uniquely determined in $Irr G$ by these
  multiplicities, and the sign character $epsilon$ of $W$ is determined by the
  corresponding multiplicities, it follows that
  $ upright("St")_G=zeta_(epsilon,q) $
  for any choices of the extended specializations $(f')^*$ and $(f'')^*$. A
  similar result is true for all characters of $W$, apart from a few exceptions.
]

#theorem(title: [Benson–Curtis @bib:Benson1972])[
  Let $(W,S)$ be an indecomposable Coxeter system associated with a system
  $scr(S)$ of finite groups with $B N$-pairs. Then each character $phi in Irr W$
  is uniquely determined by the multiplicities
  ${(phi,(1_(W_J))^W):J subset.eq S}$, with the following exceptions:
  #case-list(
    numbering: "(a)",
    [#case[the characters of degree $2$, in case $W$ is dihedral of order $12$
        or $16$ (see the Feit–Higman Theorem
        @th:feit-higman-even-generalized-polygons);]
      <case:parabolic-multiplicity-dihedral-exceptions>],
    [#case[the two characters of degree $2^9=512$, in case $W$ is of type
      $E_7$;] <case:parabolic-multiplicity-e7-exceptions>],
    [#case[the four characters of degree $2^12=4096$, in case $W$ is of type
      $E_8$.] <case:parabolic-multiplicity-e8-exceptions>],
  )
] <th:parabolic-multiplicity-character-uniqueness>
#idx(
  "Benson-Curtis Theorem",
  target: [@th:parabolic-multiplicity-character-uniqueness],
)

We omit the proof, which involves a lengthy case-by-case argument. The point of
the theorem is that the correspondence $phi arrow.l.r zeta_(phi,q)$ described in
Theorem @th:hecke-character-parametrization-parabolic-multiplicities is
canonical, that is, independent of the choices of $(f')^*$ and $(f'')^*$, with
the exceptions noted above. For another application, see the exercises.

=== Generic Degrees <ss:generic-degrees>

Now that we have parametrized the characters in $(1_B)^G$ for a group $G=G(q)$
belonging to a system $scr(S)$, we are in a position to consider the main
problems of character theory, at least for components of $(1_B)^G$. Can we give
the degrees, and possibly other character values, of the characters
${zeta_(phi,q)}$ for all the groups $G(q) in scr(S)$, by some uniform method?
The main result of this subsection is that the degrees of these characters
${zeta_(phi,q)}$ can be expressed as polynomials in $q$. This result was
predicted by Brauer, and is clearly a step in the right direction. We also
include some other properties of the degrees; these results lead, through a
case-by-case analysis, to the explicit calculation of the degrees for each
family of finite groups with $B N$-pairs. For some results on other character
values, see §~@ss:character-value-formulas.

We shall use the notation given in §~@ss:hecke-character-parametrization (see
@prop:generic-coxeter-algebra-construction, the statements of
@lem:generic-parabolic-sums and
@th:hecke-character-parametrization-parabolic-multiplicities, and the remarks
preceding @th:hecke-character-parametrization-parabolic-multiplicities). For
each character $phi in Irr W$, we have
$
  (f')^*(mu_phi lr((e_w)))=phi(w), quad w in W,
$ <eq:generic-character-group-specialization>

where we have identified the specialized algebra $A_(f')$ with $CC W$, using
@case:generic-specialization-group-algebra[#context reference-number-text(
  "("
    + reference-data(<prop:generic-group-hecke-specializations>).text
    + reference-data(<case:generic-specialization-group-algebra>)
      .text
      .trim(regex("[()]"))
    + ")",
)].

#source(665)
The degree formula @i:th:hecke-character-formulas(iii) motivates the following:

#definition[
  Let $phi in Irr W$. The _generic degree_ (or _formal degree_) associated with
  $phi$ is the element of $K^*$ given by
  $
    d_phi=frac(
      P(u)deg phi,
      sum_(w in W)("IND" e_w)^(-1)mu_phi lr((e_w))mu_phi lr((e_(w^(-1))))
    ),
  $
  where $P(u)=sum_(w in W)"IND" e_w in R$.
] <def:generic-character-degree>
#idx("Generic degree", target: [@def:generic-character-degree])
#nidx(
  "$d_phi, F_phi lr((u))$",
  "generic degree, generic degree polynomial",
  target: [@def:generic-character-degree],
)

Of course, it is not clear from the definition that $d_phi$ is a well-defined
element of $K^*$. This point, and the exact sense in which it is a generic
degree, will be made precise in @prop:generic-degree-specializations. We shall
need to use the fact that a homomorphism $f:R arrow F$, from a commutative
integral domain $R$ into a field $F$, can be extended canonically to the
localization $R_f$ of $R$ at the prime ideal $ker f$ (see §~@i:ss:localization).
The ring $R_f$, which is a subring of the quotient field of $K$, is sometimes
called the _specialization ring_ of $f$. Given a map $f:R arrow F$, its
extension to $R_f$ will also be denoted by $f$.

We also need to look more closely at the generic algebra $A^(K^*)$. Since $A^K$
is separable by @cor:generic-algebra-separability, the algebra $A^(K^*)$ is a
split semisimple $K^*$-algebra, having a $K^*$-basis that we may identify with
the standard $R$-basis ${e_w:w in W}$ of $A$. By analogy with
@i:prop:hecke-standard-basis(iii), it is natural to consider the bilinear form
$beta:A^(K^*) times A^(K^*) arrow K^*$, whose value $beta(e_w, e_(w'))$ is the
coefficient of $1$ $(=e_1)$ in the expression of the product $e_w e_(w')$ as a
$K^*$-linear combination of the standard basis elements. We then have:

#lemma[
  The bilinear form $beta:A^(K^*) times A^(K^*) arrow K^*$ is symmetric,
  associative, and nondegenerate. The elements
  $
    {("IND" e_w)^(-1)e_w}_(w in W) quad "and" quad
    {e_(w^(-1))}_(w in W)
  $
  are dual bases with respect to the form.
] <lem:generic-algebra-dual-bases>

The form $beta$ is clearly associative. Its other properties follow from the
formula
$
  beta(e_w, e_(w'))=cases(
    0 & "if" w^(-1)!=w',
    "IND" e_w & "if" w^(-1)=w'.
  )
$
This is easily proved by induction on $l(w)$, using the properties of
multiplication of standard basis elements established in
@prop:generic-coxeter-algebra-construction, and is left as an exercise for the
reader.

With this result in hand, we can apply the orthogonality relations
@i:prop:kilmoyer-central-idempotents to the characters ${mu_phi}_(phi in Irr W)$
of the split semisimple $K^*$-algebra $A^(K^*)$.

#proposition[
  Let ${d_phi}$ be the generic degrees associated with the characters
  $phi in Irr W$, for a finite Coxeter system $(W,S)$. Then the elements $d_phi$
  are well-defined elements of the quotient field of $R^*$ in $K^*$. Moreover,
  the following statements hold.
  #case-list(
    numbering: "(i)",
    [#case[#source(666)
        $(f')^*(d_phi)=deg phi$ for all $phi in Irr W$.]
      <case:generic-degree-group-specialization>],
    [#case[The generic degrees are the unique solutions in $K^*$ of the system
      of equations
      $
        sum_(phi in Irr W)d_phi mu_phi lr((e_w))=cases(
          P(u) & w=1,
          0 & w!=1.
        )
      $] <case:generic-degree-character-equations>],
    [#case[If $(W,S)$ is the Coxeter system of a system $scr(S)$ of finite
        groups with $B N$-pairs, then
        $
          (f'')^*(d_phi)=deg zeta_(phi,q)
          quad "for each" phi in Irr W "and" q in "CP",
        $
        where $zeta_(phi,q)$ is the character in $(1_(B(q)))^(G(q))$ associated
        with $phi$, as in
        @th:hecke-character-parametrization-parabolic-multiplicities.]
      <case:generic-degree-hecke-specialization>],
  )
] <prop:generic-degree-specializations>

#proof[
  We have $mu_phi lr((e_w)) in R^*$ for all $w in W$, by
  @cor:deformation-character-specialization. The next calculation shows that
  $d_phi in R_((f')^*)^*$, and proves @case:generic-degree-group-specialization.
  We have
  $
    (f')^*(d_phi)=frac(
      abs(W)deg phi,
      sum_(w in W)phi(w)phi(w^(-1))
    )=deg phi, quad phi in Irr W,
  $
  by @eq:generic-character-group-specialization, @def:generic-character-degree,
  and the orthogonality relations for $Irr W$.

  @case:generic-degree-character-equations. Using the dual bases of $A^(K^*)$
  given in @lem:generic-algebra-dual-bases, an easy calculation using
  Proposition @i:prop:kilmoyer-central-idempotents shows that the central
  primitive idempotent $epsilon_phi$ in $A^(K^*)$ corresponding to the character
  $mu_phi$ is given by
  $
    epsilon_phi=frac(d_phi, P(u))sum_(w in W)
    ("IND" e_w)^(-1)mu_phi lr((e_(w^(-1))))e_w.
  $
  The relation $sum_(phi in Irr W)epsilon_phi=1$ implies the formula stated in
  @case:generic-degree-character-equations. The uniqueness of the elements
  ${d_phi}$ as solutions of the equations in
  @case:generic-degree-character-equations follows from the orthogonality
  relations @i:prop:kilmoyer-central-idempotents for $Irr A^(K^*)$.

  @case:generic-degree-hecke-specialization. As in the proof of
  @case:generic-degree-group-specialization, we shall show that $d_phi$ belongs
  to the specialization ring $R_((f'')^*)^*$, which will imply
  @case:generic-degree-hecke-specialization. We first require the formula
  $ zeta_(phi,q)(a_w)=mu_(phi,q)(e''_w) quad "for all" w in W $
  (see @eq:generic-hecke-character-correspondence). We then obtain
  $
    (f'')^*(d_phi) & =frac(
                       (f'')^*(P(u))deg phi,
                       sum_(w in W)f''("IND" e_w)^(-1)
                       (f'')^*(mu_phi lr((e_w)))(f'')^*(mu_phi lr((e_(w^(-1)))))
                     ) \
                   & =frac(
                       abs(G(q):B(q))(zeta_(phi,q),(1_(B(q)))^(G(q))),
                       sum_(w in W)(op("ind")a_w)^(-1)
                       zeta_(phi,q)(a_w)zeta_(phi,q)(a_(w^(-1)))
                     ) \
                   & =deg zeta_(phi,q).
  $
  #source(667)
  The proof of the preceding formula uses @i:th:hecke-character-formulas(iii),
  together with the facts that $f''("IND" e_w)=op("ind")a_w$ and
  $f''(P(u))=abs(G(q):B(q))$, by @lem:generic-parabolic-sums. We have also
  applied @th:hecke-character-parametrization-parabolic-multiplicities to obtain
  $deg phi=(zeta_(phi,q),(1_(B(q)))^(G(q)))$. This completes the proof.
]

The next result is due to Benson–Curtis @bib:Benson1972.

#theorem[
  Let $scr(S)$ be a system of finite groups with $B N$-pairs. Assume that the
  set of characteristic powers $"CP"$ contains almost all primes. Let
  ${c_1,dots,c_n}$ define the index parameters of the groups in $scr(S)$ (see
  @def:bn-pair-group-system). Take the generic algebra $A$ over the one-variable
  base $R=QQ[u]$, with parameters $u_i=u^(c_i)$, $1<=i<=n$, for a fixed
  indeterminate $u$ over $QQ$. Then for each $phi in Irr W$, the generic degree
  $d_phi$ (see @def:generic-character-degree) belongs to $R=QQ[u]$, and thus
  there exists a polynomial $F_phi lr((u)) in QQ[u]$ such that
  $d_phi=F_phi lr((u))$.
] <th:generic-degree-polynomiality>
#idx("Generic degree polynomial", target: [@th:generic-degree-polynomiality])

#remarks(numbered: false)[
  Once the polynomials ${F_phi lr((u)),phi in Irr W}$ have been determined, the
  degrees of the irreducible characters $zeta_(phi,q)$ in $(1_(B(q)))^(G(q))$
  can be found by substitution:
  $ deg zeta_(phi,q)=F_phi lr((q)) $
  (see @case:generic-degree-hecke-specialization[#context reference-number-text(
    "("
      + reference-data(<prop:generic-degree-specializations>).text
      + reference-data(<case:generic-degree-hecke-specialization>)
        .text
        .trim(regex("[()]"))
      + ")",
  )]). For example, let $scr(S)$ be the system consisting of the groups
  ${GL_(n+1)(F_q)}$. Then the generic degree associated with the sign character
  $epsilon$ of $W$ is given by
  $ F_epsilon lr((u))=u^(n(n+1) slash 2), $
  and for each prime power $q$, $F_epsilon lr((q))=deg upright("St")_G$, where
  $upright("St")_G=zeta_(epsilon,q)$ is the Steinberg character of
  $GL_(n+1)(F_q)$, by the example in §~@ss:hecke-sign-steinberg.
]

The assumption that $"CP"$ contains almost all primes is satisfied by all
families of untwisted Chevalley groups, and for some families of twisted types
of Chevalley groups such as the unitary groups. For the twisted Chevalley groups
defined by Suzuki and Ree, however, all of the characteristic powers associated
with the family are powers of a single prime, $2$ or $3$. In the case of the
family of type $attach(F, tl: 2)_4$, defined by Ree, the generic degrees defined
above need not be polynomials (see Curtis–Iwahori–Kilmoyer @bib:Curtis1971,
§~9).

The proof of @th:generic-degree-polynomiality depends on the following result
from analytic number theory:

#theorem(name: "Hilbert Irreducibility Theorem")[
  Let $F(u,X) in ZZ[u,X]$ be an irreducible polynomial in two variables, of
  positive degree in $X$. Then there exist infinitely many primes ${q}$ such
  that $F(q,X)$ is an irreducible polynomial in $ZZ[X]$.
] <th:hilbert-prime-specialization-irreducibility>
#idx(
  "Hilbert Irreducibility Theorem",
  target: [@th:hilbert-prime-specialization-irreducibility],
)

For a proof, see Lang (@bib:Lang1962, Ch.~VIII).

#proof(head: emph[Proof of @th:generic-degree-polynomiality.])[
  Let $K$ be the quotient field of $R$, and let $phi$ be a fixed irreducible
  #source(668)
  character of $W$. We first prove that $d_phi in K$. Let
  $
    c_phi=op("L.C.M."){ "IND" e_w:w in W } dot
    sum_(w in W)("IND" e_w)^(-1)mu_phi lr((e_w))mu_phi lr((e_(w^(-1)))).
  $
  Once we prove that $c_phi in K$, then clearly also $d_phi in K$, by Definition
  @def:generic-character-degree. For each $w in W$, we have
  $mu_phi lr((e_w)) in R^*$ by @cor:deformation-character-specialization, and
  hence $c_phi in R^*$. Then $op("min. pol.")_K c_phi in R[X]$, by Proposition
  @i:prop:minimal-polynomial-integrality, since $R=QQ[u]$ is integrally closed
  in $K$. For a suitably chosen integer $a$, it follows that
  $ F(u,X)=a dot op("min. pol.")_K c_phi in ZZ[u,X], $
  and $F(u,X)$ is irreducible, of positive degree in $X$. If $F(u,X)$ has degree
  $1$ in $X$, then $c_phi in K$, and there is nothing further to prove. Now
  suppose the degree in $X$ of $F(u,X)$ is $>1$. For each $q in "CP"$, let
  $(f'')^*:R^* arrow CC$ extend the specialization $f'':u mapsto q$. By
  @prop:generic-degree-specializations, $(f'')^*(d_phi)=deg zeta_(phi,q) in ZZ$,
  and hence $(f'')^*(c_phi) in QQ$. Then
  $ F(q,(f'')^*(c_phi))=0 $
  for each $q in "CP"$, since $F(u,c_phi)=0$. It follows that the polynomials
  ${F(q,X):q in "CP"}$ all have a rational zero, contradicting the
  Irreducibility Theorem @th:hilbert-prime-specialization-irreducibility. Thus
  $c_phi in K$, as required.

  The proof of the theorem is completed using the following elementary result,
  whose verification is left to the reader.
]

#lemma[
  Let $h(u) in QQ(u)$ be a rational function such that for infinitely many
  positive integers ${n_i}$, we have $h(n_i) in ZZ$. Then $h(u) in QQ[u]$.
] <lem:integer-valued-rational-function-polynomial>

The next result and Proposition
@case:generic-degree-character-equations[#context reference-number-text(
  "("
    + reference-data(<prop:generic-degree-specializations>).text
    + reference-data(<case:generic-degree-character-equations>)
      .text
      .trim(regex("[()]"))
    + ")",
)] have turned out to be of decisive importance for the calculation of the
generic degrees. (See Carter @bib:Carter1985 for tables of generic degrees for
the exceptional Weyl groups of type $E_6$, $E_7$, $E_8$, $F_4$, and $G_2$.) The
independent-parameter case, where the ${u_i}$ are indeterminates over $QQ$
satisfying only $u_i=u_j$ if $s_i =_W s_j$, has the following rationality
property: for the nonexceptional characters of
Theorem~@th:parabolic-multiplicity-character-uniqueness, the generic degrees
$d_phi$ lie in $QQ(u_1, dots, u_n)$, by
Exercise~@exc:nonexceptional-generic-character-rationality. Indeed, that
exercise puts their generic character values in $R$, so the formula in
Definition~@def:generic-character-degree is a quotient of elements of its
fraction field.#ed-note[
  For $W=I_2(6)$ with independent parameters $x,y$, put $rho^2=x y$,
  $P=(1+x)(1+y)(1+x y+x^2 y^2)$, $A=x+y+x^(-1)+y^(-1)-1$, and
  $C=(x-1)(y-1)/rho$. The two degree-two characters in
  Theorem~@th:rank-two-hecke-irreducible-representations have generic degrees
  $P/(2(A+C))$ and $P/(2(A-C))$ by Definition~@def:generic-character-degree.
  They are exchanged unequally by $rho |-> -rho$, so neither lies in $QQ(x, y)$.
  Thus these exceptional characters cannot be included in an unrestricted
  rationality claim.
]

#theorem[
  Keep the assumptions of @th:generic-degree-polynomiality. Then for each
  $phi in Irr W$, the generic degree $F_phi lr((u))$ divides the polynomial
  $"IND" e_(w_0) dot P(u)$ in the polynomial ring $QQ[u]$, where $w_0$ is the
  unique element of maximal length in $W$ (see
  @th:reflection-length-cancellation-exchange).
] <th:generic-degree-poincare-divisibility>

#proof[
  Let $m(u)="IND" e_(w_0) in QQ[u]$. It is clear that
  $ m(u)=op("L.C.M.")_(w in W) "IND" e_w. $
  By Theorem @i:th:hecke-character-formulas(iv), we have
  $ F_phi lr((q)) divides m(q)P(q) $
  #source(669)
  for all $q in "CP"$, since $F_phi lr((q))=deg zeta_(phi,q)$,
  $(zeta_(phi,q),(1_(B(q)))^(G(q)))>0$, and $P(q)=abs(G(q):B(q))$, by
  @case:generic-parabolic-index[#context reference-number-text(
    "("
      + reference-data(<lem:generic-parabolic-sums>).text
      + reference-data(<case:generic-parabolic-index>).text.trim(regex("[()]"))
      + ")",
  )]. From this, it follows easily that $F_phi lr((u)) divides m(u)P(u)$ in
  $QQ[u]$, as required.
]

#exercises-heading

#exercise[
  Keep the notation preceding the statement of Theorem
  @th:hecke-character-parametrization-parabolic-multiplicities. Let
  $phi in Irr W$, for an indecomposable Coxeter system $(W,S)$ associated with a
  system $scr(S)$ of finite groups with $B N$-pairs. Using Theorem
  @th:parabolic-multiplicity-character-uniqueness, prove that, if $phi$ is not
  one of the exceptions @case:parabolic-multiplicity-dihedral-exceptions,
  @case:parabolic-multiplicity-e7-exceptions, or
  @case:parabolic-multiplicity-e8-exceptions to
  @th:parabolic-multiplicity-character-uniqueness, then the corresponding
  character $mu_phi in Irr(K^* times.o_R A)$ is rational, in the sense that
  $mu_phi lr((1 times.o e_w)) in R$, for each basis element $1 times.o e_w$ of
  $K^* times.o_R A$ (Benson–Curtis @bib:Benson1972).
] <exc:nonexceptional-generic-character-rationality>
#idx(
  "Benson-Curtis Theorem",
  target: [@exc:nonexceptional-generic-character-rationality],
)

#hint([@exc:nonexceptional-generic-character-rationality])[
  Let $sigma:K^* arrow K^*$ be a field automorphism which acts as the identity
  on the subfield $K$. Then $sigma(R^*)=R^*$, and $sigma$ permutes the
  irreducible characters of $K^* times.o_R A$, in such a way that, for
  $phi in Irr W$, $sigma mu_phi=mu_(phi')$, for some $phi' in Irr W$, where
  $mu_(phi')(1 times.o e_w)=sigma(mu_phi lr((1 times.o e_w)))$ for all $w in W$
  (see @cor:deformation-character-specialization). We have
  $mu_phi lr((epsilon_J))=("IND" epsilon_J)m(phi,J)$ for each subset
  $J subset.eq S$, as in the proof of
  @th:hecke-character-parametrization-parabolic-multiplicities. Apply $sigma$,
  and obtain $mu_(phi')(epsilon_J)=("IND" epsilon_J)m(phi,J)$, since
  $"IND" epsilon_J$ and $m(phi,J)$ are both fixed by $sigma$. By the proof of
  @th:hecke-character-parametrization-parabolic-multiplicities, it follows that
  $(phi,(1_(W_J))^W)=(phi',(1_(W_J))^W)$ for all $J subset.eq S$. By
  @th:parabolic-multiplicity-character-uniqueness, it follows that $phi=phi'$.
  Since this holds for each automorphism $sigma$ of $K^*$ over $K$, it follows
  from @cor:deformation-character-specialization that
  $mu_phi lr((1 times.o e_w)) in K inter R^*=R$, for all $w in W$, as required.
]

#exercise[
  Let $G(q) in scr(S)$. Apply the preceding exercise to prove that, for each
  nonexceptional (in the sense of
  @th:parabolic-multiplicity-character-uniqueness) character $phi in Irr W$, the
  corresponding character $zeta_(phi,q)$ is rational-valued on $G(q)$.
] <exc:nonexceptional-bn-character-rationality>

#hint([@exc:nonexceptional-bn-character-rationality])[
  Apply @i:prop:permutation-hecke-formulas.
]
