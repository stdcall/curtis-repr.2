#import "main-defs.typ": *
#import "statements.typ": *

== Cuspidal Characters <sec:cuspidal-characters>

=== Generalized Restriction and Induction <ss:generalized-restriction-induction>

Each proper standard parabolic subgroup $P_I$ in a finite group $G$ of Lie type
has a Levi subgroup $L_I$. This is also a finite group of Lie type, with a
$B N$-pair whose rank is smaller than that of the given $B N$-pair in $G$. Thus
it is natural
#source(683)
to seek as much information as possible on the relation between characters of
$L_I$ and $G$. The usual operations of induction and restriction, and their
connections through the Mackey theorems (§§~@i:ss:mackey-theorems,
@i:ss:intertwining-number), require information concerning the double cosets
$L_I backslash G slash L_I$. This involves the subgroup $V_I=O_p lr((P_I))$,
where $p$ is the characteristic, and depends in a complicated way on the
structure of the group $G$. On the other hand, the double cosets
$P_I backslash G slash P_I$ are parametrized by elements of the Weyl group $W$
of $G$, by @th:bn-pair-parabolic-double-cosets, and are thus described by
generic information, depending only on the family of groups of Lie type of type
$W$ to which $G$ belongs.

For these reasons, it is useful to define generalized operations of restriction
and induction, which suppress the influence of the $p$-subgroups $V_I$. These
ideas were first used systematically by Green @bib:Green1955b in his
determination of the characters of $G L_n lr((FF_q))$, and were applied by
Harish-Chandra @bib:HarishChandra1970 to reductive groups over finite fields.

We begin with some elementary remarks about these generalized operations,
suggested by the Levi decomposition of standard parabolic subgroups
$P_I=L_I ⋉ V_I$, where $V_I=O_p lr((P_I))$, and where $L_I$ is a standard Levi
subgroup (see §~@ss:split-bn-pair-levi-decomposition). We shall use some
notation from §§~@i:sec:orthogonality-central-idempotents,
@i:sec:induced-modules\:

#reference-list(
  [$op("ch") H=op("ch") CC H$],
  [the ring of virtual $CC$-characters of a finite group $H$,],
  [$op("Irr") H$],
  [a basic set of irreducible $CC$-characters of $H$,],
  [$zeta arrow zeta_H=op("res")_H^G zeta$],
  [the operation of restriction from $op("ch") G$ to $op("ch") H$, for a
    subgroup $H<=G$,],
  [$lambda arrow lambda^G=op("ind")_H^G lambda$],
  [the operation of induction from $op("ch") H$ to $op("ch") G$.],
)

For the moment, let $G$ denote an arbitrary finite group, $H$ a subgroup of $G$,
and $V$ a normal subgroup of $H$. In this situation, we can define an operation
of _#idx("Generalized restriction, induction")generalized restriction_
$r_(H slash V)^G:op("ch") G arrow op("ch") H slash V$, as follows. Let $X$ be a
$CC G$-module, affording the character $xi$. Then
$ op("inv")_V X={x in X:v x=x "for all" v in V} $
is a $CC H$-submodule of $op("res")_H^G X$, since $V ⊴ H$, and is in fact a
$CC(H slash V)$-module, since $V$ acts trivially on $op("inv")_V X$. We then
define $r_(H slash V)^G xi$ to be the $CC$-character of $H slash V$ afforded by
$op("inv")_V X$, and extend by linearity to obtain a $ZZ$-homomorphism
$r_(H slash V)^G:op("ch") G arrow op("ch") H slash V$.

The operation of _generalized induction_
$i_(H slash V)^G:op("ch") H slash V arrow op("ch") G$ is defined as the
composite of the pullback operation
$lambda in op("ch") H slash V arrow tilde(lambda) in op("ch") H$ (via the
natural homomorphism $H arrow H slash V$), and the induction map
$op("ind")_H^G$. Specifically, for $lambda in op("ch") H slash V$, define
$
  i_(H slash V)^G lambda=op("ind")_H^G tilde(lambda)=tilde(lambda)^G,
  quad "where" tilde(lambda)(h)=lambda(overline(h)),
  quad h in H arrow overline(h) in H slash V.
$

The following properties of these operations are easily verified:

#proposition[
  Keep the preceding notation, so that $V ⊴ H<=G$. Then the following statements
  hold.

  #source(684)
  #case-list(
    numbering: "(i)",
    [#case[
      For each $xi in op("ch") G$, let $xi_H=op("res")_H^G xi$ and write
      $ xi_H=xi'+xi'', $
      where $xi'$ is the contribution to $xi_H$ from characters
      $lambda in op("Irr") H$ whose kernels contain $V$, and $xi''$ is the
      contribution from the other characters in $op("Irr") H$. Then $xi'$ can be
      viewed as a virtual character of $H slash V$, and we have
      $ r_(H slash V)^G xi=xi'. $
    ] <case:generalized-restriction-constituents>],
    [#case[
      For all $xi in op("ch") G$, we have
      $
        r_(H slash V)^G xi
        =sum_(lambda in op("Irr") H slash V)
        (xi,i_(H slash V)^G lambda)lambda,
      $
      where $i_(H slash V)^G lambda=tilde(lambda)^G$ for
      $lambda in op("ch") H slash V$.
    ] <case:generalized-restriction-expansion>],
    [#case[
      The operations of generalized restriction and induction are adjoint
      operations with respect to the usual scalar products of characters of $G$
      and $H slash V$, respectively:
      $
        (xi,i_(H slash V)^G lambda)_G
        =(r_(H slash V)^G xi,lambda)_(H slash V),
        quad "for" xi in op("ch") G,lambda in op("ch") H slash V.
      $
    ] <case:generalized-induction-adjointness>],
  )
] <prop:generalized-character-restriction-induction>

The proof is left as an exercise for the reader.

We next discuss these operations for virtual $CC$-characters of a finite group
$G$ with a split $B N$-pair of characteristic $p$. As usual, let $W$ denote the
Weyl group of $G$, $S$ the set of distinguished generators of $W$, and ${B,N}$
the given $B N$-pair in $G$, with $T=B inter N$. For each subset
$I subset.eq S$, $P_I$ denotes the standard parabolic subgroup $B W_I B$. By
@def:split-parabolic-levi-decomposition, $P_I$ has the Levi decomposition

$
  P_I=L_I ⋉ V_I,
$ <eq:standard-parabolic-character-levi-decomposition>

where $V_I=O_p lr((P_I))$, and $L_I$ is the standard Levi factor of $P_I$
generated by $T$ and the root subgroups ${U_alpha:alpha in Delta_I}$. The
parabolic subgroup $W_I<=W$ is the Weyl group of $L_I$, associated with the
$B N$-pair ${B inter L_I,N inter L_I}$.

By the preceding discussion, for each $I subset.eq S$ we have
$ V_I ⊴ P_I<=G, quad P_I slash V_I tilde.equiv L_I, $
and we can define the operations of generalized restriction and induction from
$op("ch") G$ to $op("ch") L_I$, using the identification
$P_I slash V_I tilde.equiv L_I$.

By @cor:bn-pair-parabolic-unique-standard-conjugate, two standard parabolic
subgroups $P_I$ and $P_J$ ($I,J subset.eq S$) are never conjugate in $G$ unless
$I=J$. On the other hand, standard Levi factors $L_I$ and $L_J$ may be conjugate
by elements of $N$ even though $I!=J$; when this occurs, it may happen that
$i_(P_I slash V_I)^G xi=i_(P_J slash V_J)^G eta$ for characters $xi,eta$ of
$L_I$ and $L_J$, respectively. This phenomenon is not accounted for by the usual
connection between conjugacy
#source(685)
and induction (see Lemma~@i:lem:conjugate-modules). One of the main results of
this subsection is a general version of a theorem relating conjugacy of Levi
subgroups to generalized induction (see
@th:strong-conjugacy-generalized-induction). In order to obtain this result,
however, we have to consider a wider class of parabolic subgroups.

Throughout the rest of this subsection, $cal(P)$ denotes the family of all
$N$-conjugates of the standard parabolic subgroups ${P_I:I subset.eq S}$. Each
subgroup $P in cal(P)$ has the form $P=attach(P_I, tl: n)$ for some $n in N$,
and some uniquely determined standard parabolic subgroup $P_I$ (by
@th:bn-pair-parabolic-normalizers-containment). Then $P$ has a Levi
decomposition arising from @eq:standard-parabolic-character-levi-decomposition,
and we have

$ P=L ⋉ V,quad L=attach(L_I, tl: n),quad V=attach(V_I, tl: n). $
<eq:conjugate-parabolic-canonical-levi-decomposition>

Moreover, the subgroups $L$ and $V$ depend only on the subgroup $P in cal(P)$,
and are independent of the choice of $n in N$ such that $P=attach(P_I, tl: n)$,
by @th:bn-pair-parabolic-normalizers-containment, since $N inter P_I<=L_I$. We
shall call $L$ a _standard Levi subgroup_ of $P$, and sometimes denote $L$ and
$V$ by $L_P$ and $V_P$, respectively, noting that $V_P=O_p lr((P))$. We also let
$W_L$ denote the subgroup $(N inter P)slash T<=W$; then $W_L$ is the Weyl group
of the $B N$-pair $(attach(B, tl: n)inter L,N inter L)$ in $L$.
#idx(
  "Levi decomposition",
  target: [@eq:conjugate-parabolic-canonical-levi-decomposition],
)

Given $L<=P$ as in @eq:conjugate-parabolic-canonical-levi-decomposition, similar
considerations apply to the parabolic subgroups of $L$, using
@prop:standard-levi-parabolic-correspondence. The set of parabolic subgroups of
$L$ that plays the role of $cal(P)$ is given by
$ cal(P)_L={Q inter L:Q in cal(P) "and" Q<=P}. $
Each parabolic subgroup $Q$, such that $Q in cal(P)$ and $Q<=P$ has a standard
Levi decomposition
$ Q=L_Q V_Q,quad "where" L_Q<=L "and" V_Q=O_p lr((Q)). $
By @prop:standard-levi-parabolic-correspondence, the corresponding parabolic
subgroup $Q inter L$ of $L$ has the Levi decomposition
$ Q inter L=L_Q lr((V_(Q inter L))), $
where $V_(Q inter L)=O_p lr((Q inter L))$, and $L_Q$ is the standard Levi
subgroup. Moreover, we have, by @prop:standard-levi-parabolic-correspondence,
$ V_Q=V_(Q inter L) ⋉ V_P, $
where $V_P=O_p lr((P))$.

#definition[
  Let $P$ be a parabolic subgroup of $G$ belonging to the family $cal(P)$, and
  let $P=L ⋉ V$ be its Levi decomposition, as in
  @eq:conjugate-parabolic-canonical-levi-decomposition. The operation of
  generalized restriction $T_(L,P)^G:op("ch") G arrow op("ch") L$ is called
  _truncation_, and is defined by
  $
    T_(L,P)^G xi(l)=abs(V)^(-1)sum_(v in V)xi(l v),
    quad "for" xi in op("ch") G,quad l in L.
  $

  #source(686)
  The operation of _generalized induction_
  $R_(L,P)^G:op("ch") L arrow op("ch") G$ is defined by
  $
    R_(L,P)^G lambda=op("ind")_P^G tilde(lambda)=tilde(lambda)^G,
    quad "for" lambda in op("ch") L,
  $
  where $lambda arrow tilde(lambda)$ is the pullback operation from $op("ch") L$
  to $op("ch") P$, given by
  $ tilde(lambda)(l v)=lambda(l)quad "for all" l in L,quad v in V. $
] <def:character-truncation-generalized-induction>
#idx("Truncation", target: [@def:character-truncation-generalized-induction])
#nidx(
  "$T_L^G, R_L^G$",
  "truncation and generalized induction",
  target: [@def:character-truncation-generalized-induction],
)

#remarks[
  Later in this subsection we shall prove that the operations $T_(L,P)^G$ and
  $R_(L,P)^G$ depend only on the Levi factor $L$, and not on the parabolic
  subgroups $P in cal(P)$ (see
  @th:generalized-induction-parabolic-independence), justifying the simpler
  notation $T_L^G$ and $R_L^G$, respectively.

  The standard Borel subgroup $B$ lies in $cal(P)$, and has the Levi
  decomposition $B=T ⋉ U$, where $U=O_p lr((B))$ and is a Sylow $p$-subgroup of
  $G$ (by @prop:split-bn-pair-order-sylow-steinberg). Then $T$ is an abelian
  $p'$-group, and $op("Irr") T$ consists of linear characters. For each
  $lambda in op("Irr") T$, the operation
  $ lambda arrow R_(T,B)^G lambda=tilde(lambda)^G $
  is a special case of the operation $theta arrow R_T^G theta$, defined by
  Deligne–Lusztig for each maximal torus $T$ and character
  $theta in op("Irr") T$ (see Deligne–Lusztig @bib:DeligneLusztig1976, Example
  1.10). Note in particular that $R_(T,B)^G 1_T=(1_B)^G$, whose decomposition is
  the main subject of §§~@sec:hecke-algebras-bn-pairs and
  @sec:generic-algebras-finite-coxeter-groups.
] <rem:truncation-parabolic-independence-torus-example>

The next result summarizes the basic properties of truncation and generalized
induction, including an easy form of the conjugacy result.

#proposition[
  #case-list(
    numbering: "(i)",
    [#case[
      Let $P in cal(P)$, and let $L$ be the standard Levi subgroup of $P$. Let
      $xi in op("ch") G$ be a character afforded by a $CC G$-module $X$. Then
      $
        T_(L,P)^G xi "is the character of" L "afforded by"
        op("inv")_V X quad "where" V=O_p lr((P)),quad "and"
      $
      $
        T_(L,P)^G xi=sum_(lambda in op("Irr") L)
        (xi,R_(L,P)^G lambda)lambda.
      $
    ] <case:truncation-invariant-module>],
    [#case[
      (Adjointness.) For $P,L$ as above, let $xi in op("ch") G$,
      $eta in op("ch") L$. Then
      $ (T_(L,P)^G xi,eta)_L=(xi,R_(L,P)^G eta)_G. $
    ] <case:truncation-generalized-induction-adjointness>],
    [#case[
      (Transitivity.) Let $P<=Q$, for parabolic subgroups $P$ and $Q$ in
      $cal(P)$, and let $L,M$ be the standard Levi subgroups of $P$ and $Q$,
      respectively. Then $P inter M$ is a parabolic subgroup of $M$, $L$ is a
      standard Levi subgroup of $P inter M$, and we have
      $
        T_(L,P)^G=T_(L,M inter P)^M compose T_(M,Q)^G
        quad "and" R_(L,P)^G=R_(M,Q)^G compose R_(L,M inter P)^M.
      $
    ] <case:generalized-character-operations-transitivity>],
    [#case[
      (Weak conjugacy.) Let $P_1,P_2,Q_1,Q_2 in cal(P)$, and let
      $L_1,L_2,M_1,M_2$ be their standard Levi subgroups. Assume $P_1<=Q_1$,
      $P_2<=Q_2$; then $L_1$ and $L_2$ are also standard Levi subgroups of
      $M_1 inter P_1$ and $M_2 inter P_2$. Let $w in W$ be an element such that
      $P_1=attach(P_2, tl: w)$, $Q_1=attach(Q_2, tl: w)$,
      $L_1=attach(L_2, tl: w)$, $M_1=attach(M_2, tl: w)$. Then
      $M_1 inter P_1=attach((M_2 inter P_2), tl: w)$,
      #source(687)
      and we have
      $
        T_(L_1,M_1 inter P_1)^(M_1) attach(xi, tl: w)
        =attach((T_(L_2,M_2 inter P_2)^(M_2) xi), tl: w)
      $
      for all virtual characters $xi in op("ch") M_2$.
    ] <case:generalized-character-operations-weak-conjugacy>],
  )
] <prop:truncation-induction-basic-properties>

#proof[
  @case:truncation-invariant-module We clearly have
  $ e_V X=op("inv")_V X,quad "where" e_V=abs(V)^(-1)sum_(v in V)v $
  and $V=O_p lr((P))$. If $l in L$, then $l e_V=e_V l$ since $L$ normalizes $V$.
  Consequently,
  $ xi(e_V l)=op("Tr")(l,e_V X)=op("Tr")(l,op("inv")_V X), $
  since $e_V$ is an idempotent projection from $X$ to $op("inv")_V X$. We also
  have $T_(L,P)^G xi(l)=xi(e_V l)$ by
  Definition~@def:character-truncation-generalized-induction, completing the
  proof of the first statement. The second statement follows from
  @prop:generalized-character-restriction-induction.
  Part~@case:truncation-generalized-induction-adjointness follows for characters
  $xi$ of $G$ and $eta in op("Irr") L$ by the second statement in
  part~@case:truncation-invariant-module, and extends to virtual characters by
  linearity.

  For the proof of @case:generalized-character-operations-transitivity, it is
  sufficient to derive either one of the transitivity formulas, since the other
  will follow by adjointness. By the preceding discussion, we have
  $ V_P=(V_P inter M) ⋉ V_Q,quad "and" M inter P=L ⋉ (V_P inter M), $
  where $V_P=O_p lr((P))$ and $V_Q=O_p lr((Q))$. Transitivity of the truncation
  operation follows at once from these remarks and
  Definition~@def:character-truncation-generalized-induction.

  @case:generalized-character-operations-weak-conjugacy The assumptions imply
  that $O_p lr((M_1 inter P_1))
  =attach(O_p lr((M_2 inter P_2)), tl: w)$, and the result follows from
  Definition~@def:character-truncation-generalized-induction.
]

We next obtain a version of Mackey's Intertwining Number
Theorem~@i:th:intertwining-number for generalized induction. The result is
proved first for standard parabolic subgroups, and then for parabolic subgroups
in $cal(P)$.

#proposition[
  Let $I,J subset.eq S$, and let $D_(I J)$ denote the distinguished cross
  section of $W_I backslash W slash W_J$. Let $lambda in op("ch") L_I$,
  $mu in op("ch") L_J$. Then
  $
    (R_(L_I,P_I)^G lambda,R_(L_J,P_J)^G mu)
    =sum_(x in D_(I J))
    (T_(L_K,P_K inter L_I)^(L_I) lambda,
      attach(T_(L_(K'),P_(K') inter L_J)^(L_J), tl: dot(x))mu)_(L_K),
  $
  where for a fixed $x in D_(I J)$, the subsets $K$ and $K'$ of $S$ are defined
  by
  $ K=I inter attach(J, tl: x),quad K'=attach(K, tl: x^(-1)), $
  and we have $L_K=attach(L_(K'), tl: dot(x))$.
] <prop:standard-parabolic-generalized-intertwining>
#idx(
  "Intertwining Number Theorem",
  target: [@prop:standard-parabolic-generalized-intertwining],
)

#source(688)
#proof[
  The subset of $N$ consisting of coset representatives ${dot(x):x in D_(I J)}$
  forms a cross section of $P_I backslash G slash P_J$. (To simplify notation in
  what follows, we shall often write $x$ instead of $dot(x)$, for
  $x in D_(I J)$.) By Theorem~@i:th:intertwining-number and the definition,
  $
    (R_(L_I,P_I)^G lambda,R_(L_J,P_J)^G mu)
    =sum_(x in D_(I J))
    (lr(tilde(lambda) |)_(P_I inter attach(P_J, tl: x)),
      lr(attach(tilde(mu), tl: x) |)_(P_I inter attach(P_J, tl: x)))_(P_I
    inter attach(P_J, tl: x)),
  $
  where $tilde(lambda)$ and $tilde(mu)$ denote the pullbacks of $lambda$ and
  $mu$ to $P_I$ and $P_J$, respectively. We now calculate the scalar products on
  the right-hand side. Let $x$ be a fixed element of $D_(I J)$, and let
  $
    K=I inter attach(J, tl: x) subset.eq I,
    quad K'=attach(K, tl: x^(-1))subset.eq J,
  $
  as in the statement above. Since $K=attach(K', tl: x)$,
  $Delta_K=x dot Delta_(K')$, it follows from the definition of the standard
  Levi subgroups $L_K$ and $L_(K')$ that $L_K=attach(L_(K'), tl: x)$ (see
  @th:split-bn-parabolic-levi-decomposition). By
  Theorem~@th:split-parabolic-intersection-factorization,
  part~@case:parabolic-intersection-four-factor-decomposition, there is a
  factorization
  $
    P_I inter attach(P_J, tl: x)=L_K lr((L_I inter attach(V_J, tl: x)))
    (V_I inter attach(L_J, tl: x))(V_I inter attach(V_J, tl: x)),
  $
  with uniqueness of expression. Note that by
  §~@ss:finite-coxeter-parabolic-subgroups, $x^(-1) in D_(J I)$ and
  $K'=J inter attach(I, tl: x^(-1))$, so that
  @th:split-parabolic-intersection-factorization can be applied to the terms
  $L_I inter attach(V_J, tl: x)$, and also to $V_I inter attach(L_J, tl: x)
  =attach((attach(V_I, tl: x^(-1))inter L_J), tl: x)$, in the factorization of
  $P_I inter attach(P_J, tl: x)$. This gives (for
  $V_(I K)=O_p lr((P_K inter L_I))$ etc.),
  $
    L_I inter attach(V_J, tl: x)=V_(I K)=L_I inter V_K quad "and"
    V_I inter attach(L_J, tl: x)=attach(V_(J,K'), tl: x)
    =attach((L_J inter V_(K')), tl: x),
  $ <eq:intertwining-levi-unipotent-intersections>

  by @th:split-parabolic-intersection-factorization,
  part~@case:parabolic-intersection-levi-parabolic. We then obtain, for the
  scalar product corresponding to $x in D_(I J)$,
  $
    (lr(tilde(lambda) |)_(P_I inter attach(P_J, tl: x)),
      lr(attach(tilde(mu), tl: x) |)_(P_I inter attach(P_J, tl: x)))_(P_I
    inter attach(P_J, tl: x))
    =abs(P_I inter attach(P_J, tl: x))^(-1)
    sum_(l,v,y,z)tilde(lambda)(l v attach((y), tl: x)z)
    overline(attach(tilde(mu), tl: x)(l v attach((y), tl: x)z)),
  $
  where $l in L_K$, $v in V_(I K)$, $y in V_(J,K')$,
  $z in V_I inter attach(V_J, tl: x)$. In order to simplify this expression, we
  first note that since $L_I$ normalizes $V_I$ and $L_J$ normalizes $V_J$, we
  have
  $ (u,u') in V_I inter attach(V_J, tl: x) $
  for all commutators $(u,u')=u u' u^(-1)(u')^(-1)$, with
  $u in V_(I K)=L_I inter attach(V_J, tl: x)$,
  $u' in attach(V_(J K'), tl: x)=V_I inter attach(L_J, tl: x)$ (by
  @eq:intertwining-levi-unipotent-intersections). Then for each element of
  $P_I inter attach(P_J, tl: x)$ in factored form, as above, we have
  $
    l v attach((y), tl: x)z equiv l v (mod V_I) quad "and"
    l v attach((y), tl: x)z equiv l attach((y), tl: x)
    (mod attach(V_J, tl: x)).
  $
  Therefore, by the definitions of $tilde(lambda)$ and $tilde(mu)$, we obtain
  $
    tilde(lambda)(l v attach((y), tl: x)z)=lambda(l v) quad "and"
    attach(tilde(mu), tl: x)(l v attach((y), tl: x)z)
    =attach(mu, tl: x)(l attach((y), tl: x)).
  $
  By the uniqueness of factorization of elements of
  $P_I inter attach(P_J, tl: x)$, it follows that the
  #source(689)
  scalar product becomes
  $
    abs(L_K)^(-1)abs(V_(I K))^(-1)abs(V_(J K'))^(-1)
    sum_(l,v,y)lambda(l v)
    overline(attach(mu, tl: x)(l attach((y), tl: x))),
  $
  with $l,v,y$ as above. Finally, using the definition of truncation
  @def:character-truncation-generalized-induction, and the facts that
  $V_(I K)=O_p lr((P_K inter L_I))$ and $V_(J K')=O_p lr((P_(K') inter L_J))$ by
  @th:split-parabolic-intersection-factorization,
  part~@case:parabolic-intersection-levi-parabolic, we have
  $
    abs(V_(I K))^(-1)sum_v lambda(l v)
    =T_(L_K,P_K inter L_I)^(L_I) lambda(l)
  $
  and
  $
    abs(V_(J K'))^(-1)sum_y attach(mu, tl: x)(l attach((y), tl: x))
    =attach(T_(L_(K'),P_(K') inter L_J)^(L_J), tl: x)mu(l).
  $
  Then the scalar product corresponding to $x in D_(I J)$ becomes
  $
    (T_(L_K,P_K inter L_I)^(L_I) lambda,
      attach(T_(L_(K'),P_(K') inter L_J)^(L_J), tl: x)mu)_(L_K),
  $
  since $attach(L_(K'), tl: x)=L_K$, and the proof is completed.
]

It is now straightforward to extend the preceding result to parabolic subgroups
in the family $cal(P)$.

#theorem[
  Let $P$ and $Q$ be parabolic subgroups in $cal(P)$, with standard Levi
  subgroups $L$ and $M$, respectively. Let $W_L,W_M$ be the Weyl groups of $L$
  and $M$, and let $D$ be an arbitrary cross section of
  $W_L backslash W slash W_M$. For each $w in D$, $L inter attach(Q, tl: w)$ is
  a parabolic subgroup of $L$, $attach(P, tl: w^(-1))inter M$ is a parabolic
  subgroup of $M$, and $L inter attach(M, tl: w)$,
  $attach(L, tl: w^(-1))inter M$ are standard Levi subgroups of
  $L inter attach(Q, tl: w)$ and $attach(P, tl: w^(-1))inter M$, respectively.
  Let $xi in op("ch") L$ and $eta in op("ch") M$. Then
  $
    (R_(L,P)^G xi,R_(M,Q)^G eta)
    =sum_(w in D)
    (T_(L inter attach(M, tl: w),L inter attach(Q, tl: w))^L xi,
      attach(
        T_(attach(L, tl: w^(-1))inter M,
        attach(P, tl: w^(-1))inter M)^M, tl: w
      )eta)_(L inter attach(M, tl: w)).
  $
] <th:generalized-intertwining-number>

#proof[
  We may assume that for some elements $r,s in W$, and some uniquely determined
  subsets $I,J subset.eq S$, we have
  $
    P=attach(P_I, tl: r),quad L=attach(L_I, tl: r),
    quad W_L=attach(W_I, tl: r),quad "and"
    Q=attach(P_J, tl: s),quad M=attach(L_J, tl: s),
    quad W_M=attach(W_J, tl: s).
  $
  Then
  $
    W=union.big_(w in D)W_L w W_M
    =union.big_(w in D)W_I r^(-1)w s W_J,
  $
  so $r^(-1)D s$ is a cross section of $W_I backslash W slash W_J$. It follows
  that $D$ is a cross section of $P backslash G slash Q$, by
  @th:bn-pair-parabolic-double-cosets. By Theorem~@i:th:intertwining-number we
  have
  $
    (R_(L,P)^G xi,R_(M,Q)^G eta)_G
    =sum_(w in D)(lr(tilde(xi) |)_(P inter attach(Q, tl: w)),
      lr(attach(tilde(eta), tl: w) |)_(P inter attach(Q, tl: w)))_(P inter
    attach(Q, tl: w)),
  $
  where $tilde(xi)$ and $tilde(eta)$ denote the pullbacks of $xi$ and $eta$ to
  $P$ and $Q$, respectively.

  #source(690)
  Now let $w$ be a fixed element of $D$. Then
  $ W_L w W_M=r W_I r^(-1)w s W_J s^(-1). $
  Replacing $s$ by $s s_1$ for some $s_1 in W_J$, and $r$ by $r r_1$ for some
  $r_1 in W_I$, we may assume that the same conjugacy relations
  $
    P=attach(P_I, tl: r),quad L=attach(L_I, tl: r),
    quad Q=attach(P_J, tl: s),quad M=attach(L_J, tl: s),
  $
  hold and that $r^(-1)w s=z in D_(I J)$. Then the scalar product corresponding
  to $w$ becomes
  $
    (lr(tilde(xi) |)_(P inter attach(Q, tl: w)),
      lr(attach(tilde(eta), tl: w) |)_(P inter attach(Q, tl: w)))_(P inter
    attach(Q, tl: w))
    =(lr(attach(tilde(xi), tl: r^(-1)) |)_(P_I inter attach(P_J, tl: z)),
      lr(attach((attach(tilde(eta), tl: s^(-1))), tl: z) |)_(P_I inter
      attach(P_J, tl: z)))_(P_I inter attach(P_J, tl: z)),
  $
  by the definition of conjugate characters. Since $z=r^(-1)w s in D_(I J)$, we
  may apply the proof of @prop:standard-parabolic-generalized-intertwining to
  the right-hand side, to obtain
  $
    (T_(L_K,P_K inter L_I)^(L_I) attach(xi, tl: r^(-1)),
      attach(T_(L_(K'),P_(K') inter L_J)^(L_J), tl: z)
      attach(eta, tl: s^(-1)))_(L_K),
  $
  where $K=I inter attach(J, tl: z)$, $K'=attach(I, tl: z^(-1))inter J$, and
  $
    L_K=L_I inter attach(L_J, tl: z)
    =attach((L inter attach(M, tl: w)), tl: r^(-1)),
    quad L_(K')=attach((attach(L, tl: w^(-1))inter M), tl: s^(-1)),
  $
  by @th:split-parabolic-intersection-factorization,
  part~@case:parabolic-intersection-unipotent-levi. Applying the weak conjugacy
  formula for truncation @prop:truncation-induction-basic-properties,
  part~@case:generalized-character-operations-weak-conjugacy, we obtain
  $
    T_(L_K,P_K inter L_I)^(L_I) attach(xi, tl: r^(-1))
    =attach(
      (T_(L inter attach(M, tl: w),L inter attach(Q, tl: w))^L xi),
      tl: r^(-1)
    )
  $
  and
  $
    attach(T_(L_(K'),P_(K') inter L_J)^(L_J), tl: z)
    attach(eta, tl: s^(-1))
    =attach(
      T_(attach(L, tl: w^(-1))inter M,
      attach(P, tl: w^(-1))inter M)^M, tl: r^(-1)w
    )eta.
  $
  Their scalar product on $L_K$ becomes
  $
    & (attach(
          T_(L inter attach(M, tl: w),L inter attach(Q, tl: w))^L,
          tl: r^(-1)
        )xi,
        attach(
          T_(attach(L, tl: w^(-1))inter M,
          attach(P, tl: w^(-1))inter M)^M, tl: r^(-1)w
        )eta)_(L_K) \
    & =(T_(L inter attach(M, tl: w),L inter attach(Q, tl: w))^L xi,
        attach(
          T_(attach(L, tl: w^(-1))inter M,
          attach(P, tl: w^(-1))inter M)^M, tl: w
        )eta)_(L inter attach(M, tl: w)),
  $
  since $L_K=attach((L inter attach(M, tl: w)), tl: r^(-1))$. This completes the
  proof of the theorem.
]

We now prove that the operations of truncation $T_(L,P)^G$ and generalized
induction $R_(L,P)^G$ are independent of the parabolic subgroup $P in cal(P)$
containing a given Levi subgroup $L$. This result, and the conjugacy result
following from it, are basic for the analysis of cuspidal characters in
§~@ss:philosophy-cusp-forms. For standard parabolic subgroups, the result is due
to Curtis @bib:Curtis1980a, Alvis @bib:Alvis1980, Kawanaka @bib:Kawanaka1982,
and Deligne (see Lusztig–Spaltenstein @bib:LusztigSpaltenstein1979). The proof
to follow is an elementary version of an argument due to Deligne.

#theorem[
  Let $P$ and $Q$ be parabolic subgroups in $cal(P)$ having a common
  #source(691)
  standard Levi subgroup $L$. Then
  $
    R_(L,P)^G lambda=R_(L,Q)^G lambda quad "and"
    T_(L,P)^G xi=T_(L,Q)^G xi
  $
  for all virtual characters $lambda in op("ch") L$ and $xi in op("ch") G$,
  respectively.
] <th:generalized-induction-parabolic-independence>

#proof[
  The theorem clearly holds in case the Weyl group of $G$ is trivial, that is,
  the rank of the $B N$-pair in $G$ is zero. Thus we may assume $L!=G$, and that
  the Theorem holds for groups of smaller $B N$-rank than $G$. By the
  adjointness property @prop:truncation-induction-basic-properties,
  part~@case:truncation-generalized-induction-adjointness, it is sufficient to
  prove the theorem for the operation of generalized induction, and we may
  assume, from the induction hypothesis, that the theorem holds for $L$ and
  parabolic subgroups in $cal(P)_L$. Let $lambda in op("ch") L$, and let $D$ be
  a fixed cross section of $W_L backslash W slash W_L$. From three applications
  of Theorem~@th:generalized-intertwining-number, we have
  $
    (R_(L,P)^G lambda,R_(L,P)^G lambda)
    =sum_(w in D)
    (T_(L inter attach(L, tl: w),L inter attach(P, tl: w))^L lambda,
      attach(
        T_(attach(L, tl: w^(-1))inter L,
        attach(P, tl: w^(-1))inter L)^L, tl: w
      )lambda)_(L inter attach(L, tl: w)),
  $
  $
    (R_(L,P)^G lambda,R_(L,Q)^G lambda)
    =sum_(w in D)
    (T_(L inter attach(L, tl: w),L inter attach(Q, tl: w))^L lambda,
      attach(
        T_(attach(L, tl: w^(-1))inter L,
        attach(P, tl: w^(-1))inter L)^L, tl: w
      )lambda)_(L inter attach(L, tl: w)),
  $
  and
  $
    (R_(L,Q)^G lambda,R_(L,Q)^G lambda)
    =sum_(w in D)
    (T_(L inter attach(L, tl: w),L inter attach(Q, tl: w))^L lambda,
      attach(
        T_(attach(L, tl: w^(-1))inter L,
        attach(Q, tl: w^(-1))inter L)^L, tl: w
      )lambda)_(L inter attach(L, tl: w)).
  $
  By the induction hypothesis, the three expressions on the right-hand side
  coincide. It follows that
  $
    (R_(L,P)^G lambda-R_(L,Q)^G lambda,
      R_(L,P)^G lambda-R_(L,Q)^G lambda)=0,
  $
  and hence $R_(L,P)^G lambda=R_(L,Q)^G lambda$, as required.
]

As a corollary we obtain:

#theorem(name: "Strong Conjugacy Theorem")[
  Let $I,J subset.eq S$, and assume that $L_I=attach(L_J, tl: x)$ for some
  $x in W$, where $L_I$ and $L_J$ are the standard Levi subgroups of $P_I$ and
  $P_J$, respectively. Let $psi in op("ch") L_J$ and let
  $phi=attach(psi, tl: dot(x))in op("ch") L_I$. Then
  $ R_(L_I,P_I)^G phi=R_(L_J,P_J)^G psi. $
] <th:strong-conjugacy-generalized-induction>
#idx(
  "Strong Conjugacy Theorem",
  target: [@th:strong-conjugacy-generalized-induction],
)

#proof[
  Since $attach(P_J, tl: x)$ and $P_I$ are in $cal(P)$ and both have the same
  standard Levi subgroup $L_I$, we have
  $ R_(L_I,P_I)^G phi=R_(L_I,attach(P_J, tl: x))^G phi $
  by Theorem~@th:generalized-induction-parabolic-independence. Since
  $phi=attach(psi, tl: x)$ and $L_I=attach(L_J, tl: x)$, we then obtain
  $
    R_(L_I,attach(P_J, tl: x))^G phi
    =R_(attach(L_J, tl: x),attach(P_J, tl: x))^G attach(psi, tl: x)
    =R_(L_J,P_J)^G psi
  $
  #source(692)
  by the usual conjugacy theorem for induced characters
  @i:lem:conjugate-modules, since the pullback of $attach(psi, tl: x)$ to
  $attach(P_J, tl: x)$ clearly coincides with the conjugate
  $attach(tilde(psi), tl: x)$ of the pullback $tilde(psi)$ of $psi$ to $P_J$.
  This completes the proof.
]

#remark[
  As an illustration of Theorem~@th:strong-conjugacy-generalized-induction, let
  $P_I$ and $P_J$ be standard parabolic subgroups such that $I!=J$, but
  $L_I=attach(L_J, tl: x)$ for some $x in W$. Then $P_I$ and $P_J$ are not
  conjugate in $G$, by @th:bn-pair-parabolic-normalizers-containment.
  Nevertheless, we have $(1_(P_I))^G=(1_(P_J))^G$ by
  @th:strong-conjugacy-generalized-induction, since
  $(1_(P_I))^G=R_(L_I,P_I)^G 1_(L_I)$ and $(1_(P_J))^G=R_(L_J,P_J)^G 1_(L_J)$.
  For a particular case of this phenomenon, see
  Exercise~@i:exc:gluck-permutation-characters. This raises the interesting
  problem of classification of transitive permutation representations of a
  finite group $G$, and shows that it involves more than the question of
  conjugacy of subgroups stabilizing points.
] <rem:associated-parabolics-permutation-characters>

=== The Philosophy of Cusp Forms <ss:philosophy-cusp-forms>

Throughout this subsection, $G$ denotes a finite group with a split $B N$-pair
of characteristic $p$, $W$ the Weyl group of $G$, and $S$ the set of
distinguished generators of $W$. For each subset $I subset.eq S$, $P_I$ denotes
the standard parabolic subgroup, and $L_I$ the standard Levi subgroup, both
associated with the parabolic subgroup $W_I$ of $W$. As in
§~@ss:generalized-restriction-induction, $cal(P)$ denotes the family of all
$N$-conjugates of the standard parabolic subgroups. For each parabolic subgroup
$P in cal(P)$ with standard Levi subgroup $L$, we let
$
  T_L^G:op("ch") G arrow op("ch") L quad "and"
  R_L^G:op("ch") L arrow op("ch") G
$
denote the operations of truncation and generalized induction. Thus,
$T_L^G=T_(L,P)^G$ and $R_L^G=R_(L,P)^G$ in the notation of
Definition~@def:character-truncation-generalized-induction. The simplified
notation is justified by @th:generalized-induction-parabolic-independence, where
we proved that
$ T_(L,P)^G=T_(L,Q)^G quad "and" R_(L,P)^G=R_(L,Q)^G $
for any two parabolic subgroups $P$ and $Q$ in $cal(P)$ having the same standard
Levi subgroup.

#definition[
  A virtual character $zeta in op("ch") G$ is called _cuspidal_ if
  $T_(L_I)^G zeta=0$ for all Levi subgroups $L_I$ of proper parabolic subgroups
  $P_I$, $I subset S$. A left $CC G$-module $M$ is called _cuspidal_ if
  $op("inv")_(V_I) M=0$ for all proper subsets $I subset S$, where
  $V_I=O_p lr((P_I))$. In case $G$ is an abelian $p'$-group (so that
  $S=emptyset$), all virtual characters $zeta in op("ch") G$ and all
  $CC G$-modules are said to be cuspidal.
] <def:cuspidal-character-module>
#idx("Cuspidal representation", target: [@def:cuspidal-character-module])

It follows from @prop:truncation-induction-basic-properties,
part~@case:truncation-invariant-module, that a left $CC G$-module $M$ is
cuspidal if and only if its character is cuspidal.

#proposition[
  For $zeta in op("ch") G$, the following statements are equivalent:
  #case-list(
    numbering: "(i)",
    [#case[$zeta$ is cuspidal.] <case:cuspidal-character-definition>],
    [#case[
      #source(693)
      For all proper subsets $I subset S$ and elements $x in L_I$,
      $ abs(V_I)^(-1)sum_(v in V_I)zeta(x v)=0, $
      where $V_I=O_p lr((P_I))$.
    ] <case:cuspidal-character-average-vanishing>],
    [#case[
      $lr((T_(L_I)^G zeta,T_(L_I)^G zeta))_(L_I)=0$ for all proper subsets
      $I subset S$.
    ] <case:cuspidal-character-unipotent-permutation-orthogonality>],
    [#case[
      $(zeta,R_L^G lambda)=0$ for all standard Levi subgroups $L$ of proper
      parabolic subgroups $P in cal(P)$, $P!=G$, and all virtual characters
      $lambda in op("ch") L$.
    ] <case:cuspidal-character-generalized-induction-orthogonality>],
  )
] <prop:cuspidal-character-equivalent-criteria>

#proof[
  The results of §~@ss:generalized-restriction-induction identify the averaging
  condition with vanishing of the truncations. By adjunction and orthonormality
  of the irreducible characters of $L_I$,
  $
    lr((T_(L_I)^G zeta,T_(L_I)^G zeta))_(L_I)
    =sum_(lambda in op("Irr") L_I) abs(lr((zeta,R_(L_I)^G lambda)))^2.
  $
  This finite sum is zero if and only if every coefficient vanishes,
  equivalently $T_(L_I)^G zeta=0$. Conjugating the standard parabolics covers
  the family $cal(P)$, so adjunction also gives the last condition. This proves
  the four equivalences for all virtual characters.

  If $zeta$ is the character of a $CC G$-module, one may also use the original
  dimension test $(zeta,(1_(V_I))^G)=0$ for every proper $I$: this scalar
  product is the dimension of the $V_I$-invariant module, and is zero exactly
  when that module is zero.#ed-note[
    Take $G=GL_2 lr((FF_3))$, let $epsilon$ be the quadratic character of the
    determinant, and put $zeta=1_G-epsilon$. Both linear characters are trivial
    on $U$, so their invariant dimensions $1-1$ cancel. Nevertheless
    $T_T^G zeta$ has value $2$ at $op("diag")(-1,1)$ in the diagonal torus $T$,
    and is nonzero. Thus the dimension test alone fails for virtual differences.
  ]
]

#remarks(numbered: false)[
  The concept of cuspidal representations and characters is due to
  Harish-Chandra @bib:HarishChandra1970, who had already used the same concept
  in the representation theory of reductive Lie groups, and reductive algebraic
  groups over local fields. In the case of finite groups of Lie type, the
  significance of the concept is clear from
  Proposition~@prop:cuspidal-character-equivalent-criteria. For such a group, we
  might hope to calculate $op("Irr") L_I$ for proper subsets $I subset S$, and
  then to decompose the induced characters $R_(L_I)^G lambda$ for
  $lambda in op("Irr") L_I$, $I subset S$. The cuspidal characters
  $zeta in op("Irr") G$, if any exist, are precisely the characters of $G$ that
  are missed by this procedure (see
  @prop:cuspidal-character-equivalent-criteria,
  part~@case:cuspidal-character-generalized-induction-orthogonality). The main
  point of this subsection is that not only do cuspidal characters exist, but in
  a certain precise sense, they control the character theory of $G$. This is
  Harish-Chandra's philosophy of cusp forms.

  Other expositions of Harish-Chandra's work have been given by Springer
  @bib:Springer1975 and, in the present context, by Curtis @bib:Curtis1975.
] <rem:harish-chandra-philosophy-cusp-forms>

#proposition[
  Let $zeta in op("Irr") G$. Then either $zeta$ is cuspidal, or else there
  exists a proper subset $I subset S$ and a cuspidal character
  $lambda in op("Irr") L_I$, such that $(zeta,R_(L_I)^G lambda)!=0$.
] <prop:irreducible-character-cuspidal-support-existence>

#proof[
  If $zeta$ is not cuspidal, then $S!=emptyset$ and $T_(L_I)^G zeta!=0$ for some
  proper subset $I subset S$. Let $I$ be a minimal subset of $S$ such that
  $T_(L_I)^G zeta!=0$. Then by @prop:truncation-induction-basic-properties,
  part~@case:truncation-invariant-module, we have
  $
    T_(L_I)^G zeta=sum_(lambda in op("Irr") L_I)
    (zeta,R_(L_I)^G lambda)lambda,
  $
  with at least one multiplicity $(zeta,R_(L_I)^G lambda)!=0$. Using the
  minimality of $I$, we shall prove that all characters
  $lambda in op("Irr") L_I$ such that $(zeta,R_(L_I)^G lambda)!=0$ are cuspidal.

  Let $lambda in op("Irr") L_I$ be such a character, and assume it fails to be
  cuspidal. Then for some proper subset $K subset I$ we have
  $T_(L_K)^(L_I) lambda!=0$. By transitivity of truncation (see
  @prop:truncation-induction-basic-properties,
  part~@case:generalized-character-operations-transitivity), we obtain
  $
    T_(L_K)^G zeta=T_(L_K)^(L_I)T_(L_I)^G zeta
    =sum_(lambda in op("Irr") L_I)
    (zeta,R_(L_I)^G lambda)T_(L_K)^(L_I) lambda!=0,
  $
  since the multiplicities are nonnegative and $T_(L_K)^(L_I) lambda!=0$ for at
  least one $lambda$ such that
  #source(694)
  $(zeta,R_(L_I)^G lambda)!=0$. This contradicts the assumption that $I$ is a
  minimal subset such that $T_(L_I)^G zeta!=0$, and finishes the proof.
]

The main result of this subsection is the following version in two parts, A, B,
of a theorem of Harish-Chandra @bib:HarishChandra1970, formulated as in Springer
@bib:Springer1975.

#theorem-suffix(suffix: "A")[
  Let $I,J subset.eq S$, and let $phi$ and $psi$ be irreducible cuspidal
  characters of $L_I$ and $L_J$, respectively. Then we have:
  #case-list(
    numbering: "(i)",
    [#case[
      $(R_(L_I)^G phi,R_(L_J)^G psi)=0$ unless there exists $x in W$ such that
      $L_I=attach(L_J, tl: x)$ and $phi=attach(psi, tl: dot(x))$.
    ] <case:cuspidal-induced-series-orthogonality>],
    [#case[
      In case $(R_(L_I)^G phi,R_(L_J)^G psi)!=0$, we have
      $R_(L_I)^G phi=R_(L_J)^G psi$.
    ] <case:cuspidal-induced-series-coincidence>],
  )
] <th:harish-chandra-cuspidal-series>

Part B of Theorem~@th:harish-chandra-cuspidal-series gives a formula for
$(R_(L_I)^G phi,R_(L_I)^G phi)$, for $phi$ cuspidal in $op("Irr") L_I$, in terms
of the Weyl group of $G$. We first require some definitions. Let
$N_W lr((L_I))={w in W:attach(L_I, tl: w)=L_I}$, for a fixed subset
$I subset.eq S$. Then $W_I ⊴ N_W lr((L_I))$, and the factor group
$N_W lr((L_I))slash W_I$ acts by conjugation on $op("Irr") L_I$, according to
the rule
$
  attach(lambda, tl: overline(t))=attach(lambda, tl: dot(t)),
  quad "for" overline(t)=dot(t)W_I in N_W lr((L_I))slash W_I.
$
For each $lambda in op("Irr") L_I$, let $S_lambda$ denote the stabilizer in
$N_W lr((L_I))slash W_I$ of $lambda$, that is,
$
  S_lambda={overline(t) in N_W lr((L_I))slash W_I:
    attach(lambda, tl: dot(t))=lambda}.
$

#theorem-suffix(base: [@th:harish-chandra-cuspidal-series], suffix: "B")[
  Let $phi$ be an irreducible cuspidal character of $L_I$, for some
  $I subset.eq S$. Then
  $ (R_(L_I)^G phi,R_(L_I)^G phi)=abs(S_phi), $
  where $S_phi$ is the stabilizer of $phi$ in $N_W lr((L_I))slash W_I$.
] <th:cuspidal-induction-stabilizer-norm>

#proof(head: emph[Proof of @th:harish-chandra-cuspidal-series.])[
  By Proposition~@prop:standard-parabolic-generalized-intertwining, we have
  $
    (R_(L_I)^G phi,R_(L_J)^G psi)
    =sum_(x in D_(I J))
    (T_(L_K)^(L_I) phi,
      attach(T_(L_(K'))^(L_J), tl: dot(x))psi)_(L_K),
  $
  where for a fixed $x in D_(I J)$, $K=I inter attach(J, tl: x)$ and
  $K'=attach(K, tl: x^(-1))$. Since $phi$ and $psi$ are cuspidal characters of
  $L_I$ and $L_J$, respectively, at least one of the truncations
  $T_(L_K)^(L_I) phi$ or $T_(L_(K'))^(L_J) psi$ is zero (in the summand
  corresponding to $x in D_(I J)$), unless both $K=I$ and $K'=J$. The latter is
  clearly equivalent to $I=attach(J, tl: x)$, and this implies
  $L_I=attach(L_J, tl: x)$ by @cor:parabolic-root-system-intersection and the
  definition of the standard Levi subgroups $L_I$ and $L_J$ (see
  @th:split-bn-parabolic-levi-decomposition). The intertwining number thus
  becomes
  $
    (R_(L_I)^G phi,R_(L_J)^G psi)
    =sum(phi, attach(psi, tl: dot(x)))_(L_I),
  $ <eq:cuspidal-induction-intertwining-normalizer-sum>

  where the sum is taken over all $x in D_(I J)$ such that
  $L_I=attach(L_J, tl: x)$. It follows that $(R_(L_I)^G phi,R_(L_J)^G psi)=0$
  unless $L_I=attach(L_J, tl: x)$ and $phi=attach(psi, tl: dot(x))$ for some
  $x in D_(I J)$, since both $phi$ and $psi$
  #source(695)
  are irreducible characters. If these conditions hold, for some $x in D_(I J)$,
  then $R_(L_I)^G phi=R_(L_J)^G psi$ by the Strong Conjugacy
  Theorem~@th:strong-conjugacy-generalized-induction, completing the proof of
  both parts of @th:harish-chandra-cuspidal-series.
]

#proof(head: emph[Proof of @th:cuspidal-induction-stabilizer-norm.])[
  Since $phi$ is cuspidal and irreducible, we can apply the proof of
  @th:harish-chandra-cuspidal-series, in particular
  @eq:cuspidal-induction-intertwining-normalizer-sum, to obtain
  $
    (R_(L_I)^G phi,R_(L_I)^G phi)
    =sum(phi, attach(phi, tl: dot(x)))_(L_I),
  $
  where the sum is taken over all $x in D_(I I)$ such that
  $attach(L_I, tl: x)=L_I$ and $attach(phi, tl: dot(x))=phi$. The elements
  $x in D_(I I)$ with the property that $attach(L_I, tl: x)=L_I$ clearly form a
  cross section of $N_W lr((L_I))slash W_I$, and those that also satisfy the
  condition $attach(phi, tl: dot(x))=phi$ are in bijective correspondence with
  the elements of $S_phi$. Since the corresponding scalar products
  $(phi,attach(phi, tl: dot(x)))$ are all $1$, for $x W_I in S_phi$, we obtain
  $ (R_(L_I)^G phi,R_(L_I)^G phi)=abs(S_phi), $
  as required.
]

#remarks[
  #case-list(
    numbering: "(i)",
    [#case[
      In view of Theorems~@th:harish-chandra-cuspidal-series and
      @th:cuspidal-induction-stabilizer-norm, the calculation of $op("Irr") G$,
      for a finite group of Lie type $G$, is equivalent to the solution of the
      following problems:

      #case-list(
        prefix: "Problem ",
        numbering: "I.",
        [#case[
          Find all irreducible cuspidal characters for each finite group of Lie
          type.
        ] <case:cuspidal-character-construction-problem>],
        [#case[
          (The Decomposition Problem.) For each subset $I subset.eq S$, and each
          irreducible cuspidal character $phi$ of $L_I$, find the characters in
          $op("Irr") G$ which appear with positive multiplicity in
          $R_(L_I)^G phi$.
        ] <case:cuspidal-induction-decomposition-problem>],
      )
    ] <case:cuspidal-character-theory-two-problems>],
    [#case[
      By Theorem~@th:cuspidal-induction-stabilizer-norm, it follows that
      $ (R_(L_I)^G phi,R_(L_I)^G phi)<=abs(W) $
      for each $I subset.eq S$ and each cuspidal character
      $phi in op("Irr") L_I$. We also recall that, by
      Definition~@def:cuspidal-character-module, the trivial character $1_T$
      (and all other irreducible characters of $T$) are cuspidal characters of
      $T=B inter N$. Then $R_T^G 1_T=(1_B)^G$, and
      $
        (R_T^G 1_T,R_T^G 1_T)=((1_B)^G,(1_B)^G)
        =abs(B backslash G slash B)=abs(W)
      $
      by the Bruhat decomposition @th:bruhat-decomposition. Thus the
      decomposition problem for the permutation character $(1_B)^G$, discussed
      in §§~@sec:hecke-algebras-bn-pairs and
      @sec:generic-algebras-finite-coxeter-groups, is an extreme case of
      Problem~@case:cuspidal-induction-decomposition-problem. It has been shown
      that the methods used to decompose $(1_B)^G$, suitably extended, also
      yield crucial information about multiplicities, generic degrees, etc., in
      the general case of Problem~@case:cuspidal-induction-decomposition-problem
      (see Howlett–Lehrer @bib:Howlett1980, Lusztig @bib:Lusztig1984, Chapter 8,
      Carter @bib:Carter1985, Chapter 10).
    ] <case:cuspidal-induction-norm-bound-principal-series>],
  )
] <rem:cuspidal-character-construction-decomposition>
#idx(
  "Decomposition problem",
  target: [@case:cuspidal-induction-decomposition-problem],
)

#examples[
  Let $G$ be the simple group $P S L_2 lr((FF_5))$ of order $60$; then
  #source(696)
  $G tilde.equiv A_5 tilde.equiv S L_2 lr((FF_4))$. The characters of $G$ were
  calculated in §~@i:ss:a5-exceptional-characters. These characters can also be
  found using the philosophy of cusp forms, as follows. Let $B$ be the Borel
  subgroup of $P S L_2 lr((FF_5))$, and let $B=U ⋊ T$. Then $abs(B)=10$,
  $abs(U)=5$, and $abs(T)=2$. In this case $B$ is the only proper standard
  parabolic subgroup, and $U=O_p lr((B))$. We have
  $
    (1_U)^B=1_B+epsilon_B,quad "and"
    (1_U)^G=(1_B)^G+(epsilon_B)^G,
  $
  where $epsilon_B$ is the pullback (to $B$) of the nontrivial character of $T$.
  Since both $1_B$ and $epsilon_B$ are cuspidal characters of $T$, we obtain
  $
    ((1_B)^G,(epsilon_B)^G)=0 quad "and"
    ((1_B)^G,(1_B)^G)=((epsilon_B)^G,(epsilon_B)^G)=2.
  $
  Moreover, $(1_B)^G=1_G+op("St")_G$, where $op("St")_G$ is the Steinberg
  character of degree $5$, and $(epsilon_B)^G=zeta_1+zeta_2$, where $zeta_1$ and
  $zeta_2$ are irreducible characters of degree $3$, as is easily shown using
  the facts that $deg(epsilon_B)^G=6$ and that the degrees of its two components
  divide $abs(G)=60$. Thus the solution of
  Problem~@case:cuspidal-induction-decomposition-problem yields the irreducible
  components of $(1_U)^G$, of degrees $1,5,3,3$. Using the isomorphism
  $G tilde.equiv S L_2 lr((FF_4))$, we also obtain an irreducible character of
  degree $4$, the Steinberg character of $G$ in its realization as a group of
  Lie type in characteristic $2$. This character does not appear in $(1_U)^G$,
  and, by Proposition~@prop:cuspidal-character-equivalent-criteria, is the
  unique cuspidal character of $P S L_2 lr((FF_5))$. Adding the squares of the
  degrees of the characters obtained so far, we see that we have found all
  irreducible characters of $G$.

  #case-list(start: 2, numbering: "(i)", [#case[
    Let $G$ be the simple group $P S L_2 lr((FF_p))$, with $p$ an odd prime and
    $p>=5$. Then $G$ has a cyclic self-centralizing Sylow $p$-subgroup which is
    a T.I. set, so the characters of $G$ can be determined by the methods of
    §~@i:ss:green-correspondence-character-applications. We have
    $
      op("Irr") G={1,zeta_1,dots,zeta_n;
        theta_1,dots,theta_f;chi_1,dots,chi_h},
    $
    in the notation of §~@i:ss:green-correspondence-character-applications. The
    numbers $n,f,h$ are given by
    $ n=2,quad f=e-1=1/2(p-3)quad "and" h=1. $
    The following statements about $op("Irr") G$ are left as exercises for the
    reader. We have
    $
      zeta_i lr((1))=1/2(p plus.minus 1),quad
      theta_j lr((1))=p plus.minus 1,quad "and" chi_1 lr((1))=p,
    $
    for $i=1,2$, $j=1,dots,e-1$. Moreover,
    $
      zeta_i lr((1))=cases(
        1/2(p+1) & "if" p equiv 1(mod 4),
        1/2(p-1) & "if" p equiv -1(mod 4)
      ),
    $
    while both possibilities for $theta_j lr((1))$ usually occur. The group $G$
    has a split $B N$-pair of characteristic $p$, with Weyl group $W$ of order
    $2$, by §~@ss:bn-pair-examples. We have $chi_1=op("St")_G$, and the
    remaining characters either are cuspidal or are components
    #source(697)
    of $(1_U)^G$. Those of degree $p-1$ and $1/2(p-1)$ (if they occur) are
    cuspidal, while those of degree $p+1$ and $1/2(p+1)$ (if they occur) are
    components of $(1_U)^G$ (along with $1_G$ and $op("St")_G$).
  ] <case:psl-two-prime-cuspidal-character-degrees>])
] <exm:rank-one-cuspidal-characters>

=== Formulas for Character Values <ss:character-value-formulas>

In addition to providing an organization of $op("Irr") G$ for a finite group of
Lie type $G$, the methods of §§~@ss:generalized-restriction-induction,
@ss:philosophy-cusp-forms also yield explicit information about values of
irreducible characters of $G$. We shall give illustrations of these ideas, after
some preliminary remarks. Let us keep the notation introduced at the beginning
of §~@ss:philosophy-cusp-forms.

#definition[
  Two standard parabolic subgroups $P_I,P_J$, for $I,J subset.eq S$, are said to
  be _associated_ (notation: $P_I ∼ P_J$) whenever their standard Levi subgroups
  $L_I$ and $L_J$ are conjugate by an element of $N$, that is,
  $L_J=attach(L_I, tl: dot(x))$, for some $x in W$.
] <def:associated-parabolic-subgroups>

#proposition[
  The relation $∼$ extends to an equivalence relation on the family of all
  parabolic subgroups of $G$. Thus $P ∼ Q$ if and only if $P =_G P_I$,
  $Q =_G P_J$, and $P_I ∼ P_J$. We also have, for $I,J subset.eq S$,
  $ P_I ∼ P_J "if and only if" W_I =_W W_J. $
] <prop:parabolic-association-weyl-conjugacy>

The proof of the first statement is immediate, using the fact that by
@cor:bn-pair-parabolic-unique-standard-conjugate, each parabolic subgroup is
$G$-conjugate to a unique standard parabolic subgroup. For the second statement,
see Exercise~@exc:levi-weyl-subgroup-conjugacy.

The equivalence classes arising from the relation $∼$ are called _association
classes_, and are denoted by ${cal(A)_I:I subset.eq S}$. Then, for
$I subset.eq S$,
$ cal(A)_I={P<=G:P "parabolic, and" P ∼ P_I}. $
By Theorem~@th:harish-chandra-cuspidal-series, we have a corresponding partition
of the irreducible characters of $G$:
$ op("Irr") G=union.big_(I subset.eq S)cal(E)_I, $
where
$
  cal(E)_I={zeta in op("Irr") G:(zeta,R_(L_I)^G phi)!=0
    "for" phi "cuspidal in" op("Irr") L_I}.
$ <eq:harish-chandra-association-character-series>

#nidx(
  "$cal(A)_J, cal(E)_J$",
  "association classes of parabolic subgroups, irreducible characters",
  target: [@eq:harish-chandra-association-character-series],
)
We note that $cal(E)_I=cal(E)_J$ if $P_I ∼ P_J$, and
$cal(E)_I inter cal(E)_J=emptyset$ if $P_I ≁ P_J$, for $I,J subset.eq S$. The
characters in $cal(E)_S$ are the cuspidal characters of $G$, while at the other
extreme, the characters in $cal(E)_emptyset$ are the irreducible components of
characters of the form
$ R_T^G lambda=op("ind")_B^G tilde(lambda), $
where $lambda$ is a linear character of the standard torus $T=B inter N$, and
$tilde(lambda)$ denotes its pullback (or lift) to $B$.

#source(698)
The characters in $cal(E)_S$ are sometimes called the _discrete series_ of $G$,
while those in $cal(E)_emptyset$ are said to belong to the _principal series_,
by analogy with the representation theory of semisimple Lie groups. In
particular, the characters in $(1_B)^G$ all belong to the principal series. For
the construction of the characters in the discrete series $cal(E)_S$, see
Deligne–Lusztig @bib:DeligneLusztig1976, Srinivasan @bib:Srinivasan1979, and
Carter @bib:Carter1985.

The above considerations of course apply to the irreducible characters of
standard Levi subgroups $L_I$, for $I subset.eq S$. Thus for $J subset.eq I$, we
set
$
  cal(E)_J lr((L_I))={lambda in op("Irr") L_I:
    (lambda,R_(L_J)^(L_I) mu)_(L_I)!=0,
    "for" mu "cuspidal in" op("Irr") L_J}.
$
We clearly have
$
  cal(E)_(J_1) lr((L_I))=cal(E)_(J_2) lr((L_I))
  =>cal(E)_(J_1) lr((G))=cal(E)_(J_2) lr((G))
  quad "for all" J_1,J_2 subset.eq I,
$
but the converse is not necessarily true (see
Exercise~@exc:levi-association-fusion-general-linear).

The next result shows that generalized induction respects the distribution of
irreducible characters into association classes ${cal(E)_I}$.

#proposition[
  Let $zeta in op("Irr") G$, and let $lambda in op("Irr") L_I$ for some subset
  $I subset.eq S$. Then $(zeta,R_(L_I)^G lambda)=0$ unless there exists a subset
  $J subset.eq I$ such that
  $
    zeta in cal(E)_J lr((G))quad "and"
    lambda in cal(E)_J lr((L_I)).
  $
] <prop:generalized-induction-preserves-character-series>

#proof[
  We have $lambda in cal(E)_J lr((L_I))$ for some subset $J subset.eq I$, by
  @prop:irreducible-character-cuspidal-support-existence. This means that for
  some cuspidal character $phi in op("Irr") L_J$, we have
  $
    R_(L_J)^(L_I) phi=(lambda,R_(L_J)^(L_I) phi)lambda
    +sum_(lambda' in op("Irr") L_I,lambda'!=lambda)
    (lambda',R_(L_J)^(L_I) phi)lambda',
  $
  with the multiplicity $(lambda,R_(L_J)^(L_I) phi)!=0$. By transitivity of
  generalized induction @prop:truncation-induction-basic-properties, it follows
  that
  $
    R_(L_J)^G phi=R_(L_I)^G R_(L_J)^(L_I) phi
    =(lambda,R_(L_J)^(L_I) phi)R_(L_I)^G lambda
    +sum_(lambda'!=lambda)(lambda',R_(L_J)^(L_I) phi)R_(L_I)^G lambda'.
  $
  Now let $zeta in op("Irr") G$, and assume $(zeta,R_(L_I)^G lambda)!=0$. Since
  $
    (lambda,R_(L_J)^(L_I) phi)>0 quad "and"
    (lambda',R_(L_J)^(L_I) phi)>=0 quad "for" lambda'!=lambda,
  $
  we obtain $(zeta,R_(L_J)^G phi)>0$. Thus $zeta in cal(E)_J lr((G))$, as
  required.
]

We are now in a position to prove two reduction theorems, which express certain
character values $zeta(x)$, for $zeta in op("Irr") G$ and $x in G$, in terms of
the character values $lambda(x)$ of irreducible characters $lambda$ of smaller
groups of Lie type containing $C_G lr((x))$.

#theorem(title: [Curtis @bib:Curtis1975])[
  Let $zeta in cal(E)_J lr((G))$, where $J subset.eq S$. Let $x in G$ be an
  element
  #source(699)
  such that $C_G lr((x))<=L_I$ for some subset $I subset.eq S$. Set
  $
    cal(U)=union.big_(J' subset.eq I,
    cal(E)_(J') lr((G))=cal(E)_J lr((G))) cal(E)_(J') lr((L_I)).
  $
  Then either $zeta(x)=0$, or else
  $ zeta(x)=sum_(lambda in cal(U)) (zeta,R_(L_I)^G lambda)lambda(x), $
  where each irreducible character $lambda$ in the set $cal(U)$ is counted once.
] <th:character-value-reduction-centralizer-levi>

#proof[
  By @prop:generalized-character-restriction-induction, we have
  $ zeta(x)=lr(zeta |)_(P_I)(x)=T_(L_I)^G zeta(x)+zeta''(x), $
  where
  $
    T_(L_I)^G zeta=sum_(lambda in op("Irr") L_I)
    (zeta,R_(L_I)^G lambda)lambda,
  $
  and $zeta''$ is the contribution to the restriction $lr(zeta |)_(P_I)$ from
  irreducible characters of $P_I$ whose kernels do not contain
  $V_I=O_p lr((P_I))$. Since $C_G lr((x))<=L_I$, we have
  $C_G lr((x))inter V_I=1$, and hence $zeta''(x)=0$ by the Feit–Thompson Lemma
  (Exercise~@i:exc:feit-thompson-character-vanishing). The result now follows
  from @prop:generalized-induction-preserves-character-series, since the
  multiplicities $(zeta,R_(L_I)^G lambda)$ vanish unless
  $lambda in cal(E)_(J') lr((L_I))$ and $cal(E)_(J') lr((G))=cal(E)_J lr((G))$,
  for $J' subset.eq I$.
]

#remarks(numbered: false)[
  #case-list(
    numbering: "(i)",
    [#case[
      The preceding result, and extensions of it to follow, are somewhat
      analogous to #idx("Brauer's Second Main Theorem")Brauer's Second Main
      Theorem~@th:brauer-second-main-first-form. The organization of characters
      of $G$ into $p$-blocks (as in Brauer's Theorem) is replaced, in this case,
      by the distribution of characters into series
      ${cal(E)_J lr((G)):J subset.eq S}$, following
      @eq:harish-chandra-association-character-series. The Brauer
      correspondence, from blocks of $C_G lr((x))$ to blocks of $G$, is replaced
      by generalized induction from Levi subgroups ${L_I:I subset.eq S}$ to $G$.
    ] <case:character-value-reduction-brauer-analogy>],
    [#case[
      Much stronger versions of @th:character-value-reduction-centralizer-levi
      have been proved for irreducible characters of reductive algebraic groups
      defined over finite fields, using the Deligne–Lusztig theory (see
      Fong–Srinivasan @bib:Fong1982).
    ] <case:character-value-reduction-algebraic-extensions>],
  )
] <rem:character-value-reduction-extensions>

Our second reduction theorem shows that, in the case of principal series
characters $zeta$ in $(1_B)^G$, the nonzero multiplicities appearing in the
formula for $zeta(x)$ in @th:character-value-reduction-centralizer-levi are
independent of $q$ if $G=G(q)$ as in @def:bn-pair-group-system. This result has
been extended to arbitrary principal series characters by McGovern
@bib:McGovern1982, and to the general situation described in
Theorem~@prop:generalized-induction-preserves-character-series by Howlett–Lehrer
@bib:Howlett1983.

Before stating the result, we review the parametrization of irreducible
characters in $(1_B)^G$ in terms of characters in $op("Irr") W$, from
§~@ss:hecke-character-parametrization. Throughout the rest of the subsection, we
let $cal(S)={G(q)}$ be a system of finite groups with $B N$-pairs of type
$(W,S)$, with the following properties (see @def:bn-pair-group-system):
#case-list(
  numbering: "(i)",
  [#case[
    The set of characteristic powers ${q}$ contains almost all primes.
  ] <case:character-value-system-almost-all-primes>],
  [#case[
    For each characteristic powers $q=p^a$ of a prime $p$, the group
    $G(q)in cal(S)$ has a split $B N$-pair of characteristic $p$, with the fixed
    Weyl group $W$ (see @def:split-bn-pair).
  ] <case:character-value-system-split-bn>],
)
By Theorem~@th:hecke-character-parametrization-parabolic-multiplicities, for
each group $G(q)in cal(S)$ there exists a bijection $phi arrow zeta_(phi,q)$
from the characters $phi in op("Irr") W$ to the characters
$zeta_(phi,q)in op("Irr") G(q)$, such that $zeta_(phi,q)$ appears with positive
multiplicity in $(1_(B(q)))^(G(q))$.

#source(700)
Besides the parametrization $phi arrow zeta_(phi,q)$, we require the fact that
the degrees of the characters $zeta_(phi,q)$ are given by polynomials in $q$.
Because of assumption~@case:character-value-system-almost-all-primes above, we
may apply Theorem~@th:generic-degree-polynomiality to obtain a polynomial
$F_phi lr((u))in QQ[u]$ for each $phi in op("Irr") W$, such that the degree of
the character $zeta_(phi,q)$ is given by
$ deg zeta_(phi,q)=F_phi lr((q))quad "for all groups" G(q)in cal(S). $

These considerations also apply to the standard Levi subgroups ${L_I lr((q))}$
of the groups $G(q)in cal(S)$, associated with a fixed subset $I subset.eq S$
(see @def:split-parabolic-levi-decomposition). These form a system of groups
with $B N$-pairs of type $(W_I,I)$, where $W_I$ is the parabolic subgroup of $W$
generated by the reflections in $I$. This system also satisfies the hypotheses
@case:character-value-system-almost-all-primes and
@case:character-value-system-split-bn above, so there is a bijection
$psi arrow eta_(psi,q)$ from the characters $psi in op("Irr") W_I$ to the
characters $eta_(psi,q)$ in $op("Irr") L_I lr((q))$ that appear with positive
multiplicity in $(1_(B_I lr((q))))^(L_I lr((q)))$, where
$B_I lr((q))=B(q)inter L_I lr((q))$. For each group $G(q)in cal(S)$, we let
$T(q)=B(q)inter N(q)$, so $(1_(B(q)))^(G(q))=R_(T(q))^(G(q))1$.

#theorem(title: [Curtis @bib:Curtis1975])[
  Let $G(q)in cal(S)$, and let $x in G(q)$ be an element such that
  $C_(G(q)) lr((x))<=L_I lr((q))$ for some $I subset.eq S$. Then for each
  $phi in op("Irr") W$,
  $
    zeta_(phi,q) lr((x))=sum_(psi in op("Irr") W_I)
    (zeta_(phi,q),R_(L_I lr((q)))^(G(q))eta_(psi,q))eta_(psi,q) lr((x)).
  $
  The multiplicities are independent of $q$, and are given by
  $
    (zeta_(phi,q),R_(L_I lr((q)))^(G(q))eta_(psi,q))_(G(q))
    =(phi,psi^W)_W,
  $
  for all $G(q)in cal(S)$, $phi in op("Irr") W$ and $psi in op("Irr") W_I$.
] <th:principal-series-character-value-weyl-reduction>

To prove this, let us first establish several preliminary results.

#lemma[
  Let $(zeta_(phi,q),R_(L_I lr((q)))^(G(q))eta)!=0$ for some character
  $eta in op("Irr") L_I lr((q))$. Then $(eta,R_(T(q))^(L_I lr((q)))1)!=0$ and
  $eta=eta_(psi,q)$, for some character $psi in op("Irr") W_I$.
] <lem:principal-series-levi-constituents>

#proof[
  By Theorem~@prop:generalized-induction-preserves-character-series, we have
  $(eta,R_(T(q))^(L_I lr((q)))lambda)!=0$ for some linear character
  $lambda in op("Irr") T(q)$. Then by transitivity of generalized induction, we
  have
  $ (R_(T(q))^(G(q))1,R_(T(q))^(G(q))lambda)!=0, $
  and hence $lambda=1$ by Theorem~@th:harish-chandra-cuspidal-series. Since
  $R_(T(q))^(L_I lr((q)))1=(1_(B_I lr((q))))^(L_I lr((q)))$, we have
  $eta=eta_(psi,q)$ for some character $psi in op("Irr") W_I$, by the remarks
  preceding the theorem.
]

We next take up the calculation of the multiplicities, using some ideas of Scott
@bib:Scott1973. Let ${c_1,dots,c_n}$ define the index parameters of the groups
$G(q)in cal(S)$ (see @def:bn-pair-group-system). Let $R=QQ[u_1,dots,u_n]$, where
$u_i=u^(c_i)$, $1<=i<=n$, for some fixed indeterminate $u$ over $QQ$, and let
$A$ be the generic algebra of the Coxeter system $(W,S)$ over the ring $R$ (see
§~@ss:generic-algebras-deformation-theorem).

#source(701)
For each group $G(q)in cal(S)$, the map $u arrow q$ defines a specialization of
$R$ such that the specialized algebra $A_((q))$ is isomorphic to the Hecke
algebra $cal(H)(G(q),B(q),1_B)$, by @prop:generic-group-hecke-specializations.
The map $u arrow 1$ defines a specialization such that the specialized algebra
$A_((1))tilde.equiv CC W$.

Now let:
#reference-list(
  [$K$],
  [quotient field of $R$,],
  [$K^*$],
  [a splitting field of $A^K$ such that $dim_K K^*<infinity$,],
  [$R^*$],
  [the integral closure of $R$ in $K^*$,],
  [$hat(R)$],
  [the localization of $R^*$ at some fixed prime ideal $frak(q)$ containing
    either $u-1$, or $u-q$ for some $G(q)in cal(S)$.],
)
By @cor:deformation-character-specialization, there is a bijection
$op("Irr") W arrow.l.r op("Irr") A^(K^*)$; for each $phi in op("Irr") W$, we
shall denote the corresponding irreducible character of $A^(K^*)$ by $mu_phi$.

#lemma[
  Let $mu_phi in op("Irr") A^(K^*)$ for an arbitrary character
  $phi in op("Irr") W$. Then there exists a primitive idempotent $e in A^(K^*)$
  such that the minimal left ideal $A^(K^*)e$ affords $mu_phi$, and
  $mu_phi lr((e a))in hat(R)$ for all elements $a in A$.
] <lem:generic-character-integral-primitive-idempotent>

#proof[
  The localization $hat(R)$ is a d.v.r. Therefore, letting $V$ be a simple
  $A^(K^*)$-module affording $mu_phi$, there is an $A^(hat(R))$-lattice $V_0$ in
  $V$ such that $V_0^(K^*)tilde.equiv V$. Then $V_0$ is a free $hat(R)$-module
  with a finite basis ${v_1,dots,v_d}$. For each $a in A$, left multiplication
  by $a$ acting on the basis ${v_i}$ is given by a matrix
  $(alpha_(i j) lr((a)))$ with entries in $hat(R)$. The Wedderburn component of
  $A^(K^*)$ corresponding to $mu_phi$ is faithfully represented by its action on
  $V$. Let $e$ be the primitive idempotent in $A^(K^*)$ whose matrix with
  respect to the basis ${v_i}$ is $op("diag")(1,0,dots,0)$. Then $A^(K^*)e$
  affords $mu_phi$, and if $a in A$, it follows that
  $mu_phi lr((e a))in hat(R)$, since
  $mu_phi lr((e a))=op("Tr")(e a,V)=alpha_(1 1) lr((a))$, where
  $(alpha_(i j) lr((a)))$ is as above.
]

#lemma[
  Let $e$ be an arbitrary primitive idempotent in $A^(K^*)$ affording the
  character $mu_phi$, for some $phi in op("Irr") W$. Then
  $
    e=F_phi lr((u))P(u)^(-1)sum_(w in W)
    (op("IND")e_w)^(-1)mu_phi lr((e e_(w^(-1))))e_w,
  $
  where $F_phi lr((u))in QQ[u]$ is the generic degree corresponding to $phi$,
  and $P(u)=sum_(w in W)op("IND")e_w$.
] <lem:primitive-idempotent-generic-degree-expansion>

#proof[
  Let $rho:A^(K^*)arrow K^*$ be the map defined by
  $ rho=sum_(phi in op("Irr") W)F_phi lr((u))mu_phi. $
  By @prop:generic-degree-specializations,
  part~@case:generic-degree-character-equations, we have
  $ rho(e_w)=cases(0 & "if" w!=1, P(u)&"if" w=1). $

  #source(702)
  Using the bilinear form $beta:A^K times A^K arrow K$ defined in
  §~@ss:generic-degrees, it follows that for $w,w' in W$,
  $
    e_w e_(w')=c_1 e_1+sum_(x!=1)c_x e_x,
    quad c_x in K,quad x in W,
  $
  where $c_1=0$ if $w w'!=1$ and $c_1=op("IND")e_w$ if $w w'=1$. Combining this
  result with the preceding formula, we obtain
  $
    rho(e_w e_(w'))=cases(
      0 & "if" w w'!=1,
      P(u)op("IND")e_w & "if" w w'=1
    ).
  $
  Now let $e=sum_(w in W)lambda_w e_w$, with $lambda_w in K^*$ for all $w in W$.
  Applying $rho$ to both sides of the formula,
  $
    e e_(w_1^(-1))=sum_(w in W)lambda_w e_w e_(w_1^(-1)),
    quad "for" w_1 in W,
  $
  we obtain
  $
    F_phi lr((u))mu_phi lr((e e_(w_1^(-1))))
    =lambda_(w_1)P(u)op("IND")e_(w_1),
  $
  since $mu_(phi') lr((e e_(w_1^(-1))))=0$ if $phi'!=phi$. Thus the coefficients
  ${lambda_w}$ of $e$ have the required form, and the lemma is proved.
]

Before stating the next result, we recall that $hat(R)$ denotes the localization
of $R^*$ at a prime ideal containing either $u-1$ or $u-q$, for some group
$G(q)in cal(S)$. By Lemma~@lem:specialization-integral-closure-extension there
exists an extension of the given specialization to $R^*$, and hence a further
extension $hat(f)$ to the localization $hat(R)$, that is,
$hat(f):hat(R)arrow CC$. The specialized algebra defined by $hat(f)$ will be
denoted by $hat(A)$. The map $hat(f)$ can be extended to a homomorphism of
$hat(R)$-algebras $hat(f):A^(hat(R))arrow hat(A)$, where the $hat(R)$-algebra
structure of $hat(A)$ is defined using the homomorphism $hat(f):hat(R)arrow CC$.

#lemma[
  Keep the notation of the preceding paragraph. Let $phi in op("Irr") W$, and
  let $mu_phi$ be the corresponding character of $A^(K^*)$. Then there exists a
  primitive idempotent $e$ in $A^(K^*)$ affording $mu_phi$, with the following
  properties:
  #case-list(
    numbering: "(i)",
    [#case[$e in A^(hat(R))$.] <case:generic-idempotent-integral>],
    [#case[
      $hat(f)(e)=hat(e)$ is a primitive idempotent in the specialized algebra
      $hat(A)$.
    ] <case:generic-idempotent-specialization-primitive>],
    [#case[
      $hat(e)$ affords the specialized character $hat(mu)_phi=mu_(phi,hat(f))$
      (see @cor:deformation-character-specialization).
    ] <case:generic-idempotent-specialization-character>],
  )
] <lem:generic-primitive-idempotent-specialization>

#proof[
  @case:generic-idempotent-integral By
  Lemma~@lem:generic-character-integral-primitive-idempotent, there exists a
  primitive idempotent $e in A^(K^*)$ affording $mu_phi$, such that
  $mu_phi lr((e a))in hat(R)$ for all $a in A$. By
  Lemma~@lem:primitive-idempotent-generic-degree-expansion, we obtain
  $e in A^(hat(R))$, since the elements $P(u)$ and ${op("IND")e_w:w in W}$ are
  clearly invertible in $hat(R)$.

  @case:generic-idempotent-specialization-primitive Because $e in A^(hat(R))$ is
  primitive in $A^(K^*)$, we have
  $
    e A e subset.eq e A^(K^*)e inter A^(hat(R))
    subset.eq K^*e inter A^(hat(R))subset.eq hat(R)e,
  $
  #source(703)
  using the fact that $hat(R)$ is a d.v.r. It follows that
  $ hat(e)hat(A)hat(e)=CC hat(e) $
  and hence $hat(e)=hat(f)(e)$ is primitive in $hat(A)$.

  @case:generic-idempotent-specialization-character By
  @cor:deformation-character-specialization, the specialized character
  $hat(mu)_phi$ satisfies the condition
  $ hat(mu)_phi lr((hat(e)))=hat(f)(mu_phi lr((e)))=1. $
  Thus $hat(A)hat(e)$ is a minimal ideal in the semisimple algebra $hat(A)$, and
  affords the character $hat(mu)_phi$.
]

#proof(head: emph[Proof of
  Theorem~@th:principal-series-character-value-weyl-reduction.])[
  Since $C_G lr((x))<=L_I$ and $zeta_(phi,q)in cal(E)_emptyset lr((G(q)))$, we
  obtain
  $
    zeta(x)=sum_(lambda in cal(E)_emptyset lr((L_I)))
    (zeta_(phi,q),R_(L_I lr((q)))^(G(q))lambda)lambda(x)
  $
  by Theorem~@th:character-value-reduction-centralizer-levi. By
  Lemma~@lem:principal-series-levi-constituents, the multiplicities
  $(zeta_(phi,q),R_(L_I lr((q)))^(G(q))lambda)$ are $0$ unless
  $lambda=eta_(psi,q)$ for some character $psi in op("Irr") W_I$. It remains to
  calculate these multiplicities in terms of the characters of $W$ and $W_I$.

  Let $A_I$ be the $R$-subalgebra of $A$ generated by the elements
  ${e_w:w in W_I}$. Then $A_I$ is the generic algebra of the system of finite
  groups with $B N$-pairs of type $W_I$, consisting of the standard Levi
  subgroups ${L_I lr((q))}$ of the groups $G(q)in cal(S)$. Let
  $psi in op("Irr") W_I$, $phi in op("Irr") W$, and let $nu_psi$ and $mu_phi$ be
  the irreducible characters of $A_I^(K^*)$ and $A^(K^*)$ corresponding to $psi$
  and $phi$, respectively. There exists a primitive idempotent $e in A_I^(K^*)$
  affording $nu_psi$, satisfying the conditions of
  Lemma~@lem:generic-primitive-idempotent-specialization, where $hat(R)$ is a
  d.v.r. chosen as in the discussion preceding the lemma. Then
  $mu_phi lr((e))=m$, for some nonnegative integer $m$; moreover, $m$ is
  independent of the choice of the primitive idempotent $e$ affording $nu_psi$,
  since all such idempotents are conjugate in $A_I^(K^*)$, by
  Exercise~@i:exc:semisimple-isomorphic-idempotents-conjugate. We shall prove
  that
  $
    m=(phi,psi^W)_W
    =(zeta_(phi,q),R_(L_I lr((q)))^(G(q))eta_(psi,q))_(G(q)),
  $
  for all groups $G(q)in cal(S)$. The proof is based on
  Lemma~@lem:generic-primitive-idempotent-specialization.

  First assume the homomorphism $hat(f):hat(R)arrow CC$ extends the
  specialization $u arrow 1$. Then the specialized algebras $hat(A)$ and
  $hat(A)_I$ are isomorphic to $CC W$ and $CC W_I$, respectively, by
  @prop:generic-group-hecke-specializations. By
  Lemma~@lem:generic-primitive-idempotent-specialization, the idempotent
  $hat(e)=hat(f)(e)in hat(A)_I$ corresponds to a primitive idempotent in
  $CC W_I$ affording the character $psi$, and
  $
    m=hat(f)(mu_phi lr((e)))=hat(mu)_phi lr((hat(e)))
    =(phi,psi^W)_W,
  $
  by Frobenius reciprocity.

  Now let $hat(f):hat(R)arrow CC$ extend a specialization $u arrow q$, for some
  group $G(q)in cal(S)$. In this case, we have,
  $
    hat(A)tilde.equiv H(G(q),B(q),1)quad "and"
    hat(A)_I tilde.equiv H(P_I lr((q)),B(q),1)
  $
  #source(704)
  for the specialized algebras $hat(A)$ and $hat(A)_I$. By
  Theorem~@th:hecke-character-parametrization-parabolic-multiplicities, the
  specialized characters $hat(mu)_phi$ and $hat(nu)_psi$ of $hat(A)$ and
  $hat(A)_I$, respectively, correspond to the restrictions of $zeta_(phi,q)$ to
  $cal(H)(G(q),B(q),1)$ and of $tilde(eta)_(psi,q)$ to
  $cal(H)(P_I lr((q)),B(q),1)$, where $tilde(eta)_(psi,q)$ denotes the pullback
  of $eta_(psi,q)$ to $P_I lr((q))$. Thus if $e in A_I^(hat(R))$ is a primitive
  idempotent in $A_I^(K^*)$ affording $nu_psi$, the specialized idempotent
  $hat(e)in hat(A)_I$ corresponds to a primitive idempotent in
  $cal(H)(P_I lr((q)),B(q),1)$ affording the restriction of
  $tilde(eta)_(psi,q)$. By Lemma~@i:lem:hecke-primitive-idempotents, this
  idempotent is primitive in $CC P_I lr((q))$, and affords $tilde(eta)_(psi,q)$.
  We then obtain
  $
    m=hat(f)(mu_phi lr((e)))=hat(mu)_phi lr((hat(e)))
    =(lr(zeta_(phi,q) |)_(P_I lr((q))),tilde(eta)_(psi,q))
    =(zeta_(phi,q),R_(L_I lr((q)))^(G(q))eta_(psi,q)),
  $
  by Frobenius reciprocity, completing the proof of the Theorem.
]

#exercises-heading

#exercise[
  Let $G$ be a finite group with a split $B N$-pair of characteristic $p$, and
  let $(W,S)$ be the Coxeter system associated with $G$. Let $I,J subset.eq S$.
  Prove that $L_I=attach(L_J, tl: dot(x))$, for $x in W$, if and only if
  $W_I=attach(W_J, tl: x)$.
] <exc:levi-weyl-subgroup-conjugacy>

#exercise[
  Keep the notation of Exercise~@exc:levi-weyl-subgroup-conjugacy. Prove the
  _Generalized Subgroup Theorem_: Let $I,J subset.eq S$, and let
  $lambda in op("ch") L_J$. Then
  $
    T_(L_I)^G R_(L_J)^G lambda
    =sum_(x in D_(I J))R_(L_K)^(L_I)
    attach(T_(L_(K'))^(L_J), tl: x)lambda,
  $
  where for each $x in D_(I J)$, $K=I inter attach(J, tl: x)=attach(K', tl: x)$.

  #hint([@exc:generalized-character-subgroup-theorem])[
    Use @prop:truncation-induction-basic-properties,
    part~@case:truncation-generalized-induction-adjointness, and
    @prop:standard-parabolic-generalized-intertwining.
  ] <hint:generalized-character-subgroup-theorem>
] <exc:generalized-character-subgroup-theorem>

#exercise[
  Let $G=G L_4 lr((FF_q))$, with the usual $B N$-pair. Let ${s_1,s_2,s_3}$ be
  the set of distinguished generators of the Weyl group. Let $J_1={s_1}$,
  $J_2={s_3}$, $I={s_1,s_3}$. Prove that
  $cal(E)_(J_1) lr((G))=cal(E)_(J_2) lr((G))$, but
  $cal(E)_(J_1) lr((L_I))!=cal(E)_(J_2) lr((L_I))$ (see the remarks preceding
  @prop:generalized-induction-preserves-character-series).
] <exc:levi-association-fusion-general-linear>

#exercise[
  Let $phi in op("Irr") W$, and let $zeta_(phi,q)$ be the corresponding
  character in $(1_(B(q)))^(G(q))$. Apply the reduction theorem
  @th:principal-series-character-value-weyl-reduction to prove that for each
  $t in T(q)$ which is _regular_ in the sense that $C_(G(q)) lr((t))=T(q)$, we
  have
  $
    zeta_(phi,q) lr((t))
    =(zeta_(phi,q),(1_(B(q)))^(G(q)))=deg phi.
  $
] <exc:principal-series-regular-torus-values>
