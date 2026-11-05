#import "main-defs.typ": *
#import "statements.typ": *
#import "note-layout.typ": reference-data
#import "main-defs.typ": number-text as reference-number-text

== The Schur Index <sec:schur-index>

In this section we shall develop the general theory of the Schur index, giving
its main properties in §~@ss:schur-index-general-theory, and then concentrating
on the case of group algebras in §§~@ss:group-algebra-schur-indices,
@ss:benard-schacher-theorem. The Schur index $m_QQ lr((zeta))$, of an
irreducible complex character $zeta$ of a finite group $G$, is the index of a
certain skewfield associated to $zeta$. This index gives significant information
about fields in which $zeta$ can be realized. We shall treat the more general
situation in which $QQ$ is replaced by an arbitrary ground field, not
necessarily of characteristic $0$. Our approach uses the theory of central
simple algebras, rather than manipulations with characters and idempotents.

In §~@ss:schur-index-general-theory we derive a number of different
characterizations of the Schur index, first for arbitrary algebras, and then
specifically for group algebras. We apply these results in
§~@ss:group-algebra-schur-indices, introducing the theory of Hasse invariants
when needed. This in turn leads to a review of Brauer groups in
§~@ss:benard-schacher-theorem, which play a key role in the proofs of the
Benard-Schacher Theorem and the Brauer-Witt Theorem.

For other treatments of Schur indices, and especially the theorems in
§§~@ss:schur-index-general-theory, @ss:group-algebra-schur-indices, see
Feit~@bib:Feit1967, @bib:Feit1983, and Isaacs~@bib:Isaacs1976. It is a useful
exercise, which we leave to the reader, to interpret the results of the
preceding section in terms of Schur indices.

=== General Theory <ss:schur-index-general-theory>

In this subsection we collect a number of results, mostly proved earlier in this
book, that relate splitting fields for algebras, indices of skewfields, and
irreducible characters of finite groups. We fix the following notation once and
for all: $A$ is a f.d. $k$-algebra with center $c(A)$, where $k$ is a field. If
$D$ is a division algebra of finite dimension over its center $K$, then by
@i:cor:maximal-subfield-degree $dim_K D=m^2$ for some integer $m$, called the
#idx("Index")_index_ of $D$. If $A ≅ M_r lr((D))$, we also call $m$ the index of
$A$. A finite direct sum of full matrix algebras over a field $K$ is called a
#idx("Split semisimple algebra")_split semisimple $K$-algebra_.

In the proof of @i:th:tensor-simple-algebras (see also Exercise
@exc:center-under-field-extension), we established the following easy result:

#source(749)
#lemma[
  Let $A$ and $B$ be any $k$-algebras. Then
  $ c(A times.o_k B)=c(A) times.o_k c(B). $
]<lem:tensor-algebra-center>

#proof[
  (We do not require that $A$ and $B$ be f.d. $k$-algebras.) Denote $times.o_k$
  by $times.o$ for brevity. Let $x=sum a_i times.o b_i in c(A times.o B)$, where
  each $a_i in A$, $b_i in B$. We may assume that the ${b_i}$ are linearly
  independent over $k$. Since $x$ commutes with $a times.o 1$ for each $a in A$,
  it follows that each $a_i in c(A)$. We then rewrite $x$ as
  $x=sum a'_j times.o b'_j$, with each $a'_j in c(A)$, $b'_j in B$, where now
  the ${a'_j}$ are linearly independent over $k$. Then each $b'_j in c(B)$,
  since $x$ commutes with $1 times.o b$ for each $b in B$. Thus
  $x in c(A) times.o c(B)$, as desired.
]

We show next that under ground field extensions, simple algebras behave in the
same way as their centers. To be explicit, we now prove:

#proposition[
  Let $A$ be a f.d. simple $k$-algebra with center $K$, and let $E$ be a finite
  separable field extension of $k$.
  #case-list(
    numbering: "(i)",
    [#case[
      There is a decomposition
      $ E times.o_k K=plus.o.big_(i=1)^t (E times.o_k K) epsilon_i, $
      a direct sum of fields, where $1=sum epsilon_i$ is the decomposition of
      $1$ into central primitive idempotents in $E times.o_k K$.
      Correspondingly,
      $
        E times.o_k A=plus.o.big_(i=1)^t A_i,
        quad A_i=(E times.o_k A)epsilon_i.
      $
      For each $i$, $A_i$ is a simple algebra with center
      $(E times.o_k K)epsilon_i$.
    ]<case:simple-algebra-separable-center-components>],
    [#case[
      If $K slash k$ is a Galois extension of degree $t=dim_k K$, then
      $ K times.o_k K ≅ plus.o.big_(i=1)^t K epsilon_i, $
      with each $K epsilon_i$ a field. Correspondingly, viewing $A$ as embedded
      in $K times.o_k A$, we have
      $ K times.o_k A ≅ plus.o.big_(i=1)^t A epsilon_i, $
      with each $A epsilon_i ≅ A$ as $k$-algebra. The Galois group
      $upright("Gal")(K slash k)$ acts transitively on the simple components
      ${A epsilon_i}$ of $K times.o_k A$, and $c(A epsilon_i)=K epsilon_i$.
    ]<case:simple-algebra-galois-center-components>],
  )
]<prop:simple-algebra-center-scalar-extension>

#proof[
  Since $E slash k$ is separable, $E times.o_k K$ is a direct sum of fields. The
  assertions in part~@case:simple-algebra-separable-center-components then
  follow directly from @i:th:tensor-simple-algebras and
  @lem:tensor-algebra-center. For
  part~@case:simple-algebra-galois-center-components, we may write
  $K=k[x] slash (f(x))$, with $f(x)$ irreducible over $k$. Then $f(x)$ splits
  into linear factors
  #source(750)
  in $K[x]$, so
  $ K times.o_k K ≅ K[x] slash (f(x)) ≅ K plus.o dots plus.o K. $
  The remaining assertions in part~@case:simple-algebra-galois-center-components
  are then clear, since $upright("Gal")(K slash k)$ acts transitively on the
  zeros of $f(x)$.
]

As a consequence, we may describe the behavior of a simple module under ground
field extension, in a special case needed for our later discussion. We show,
keeping the notation of @prop:simple-algebra-center-scalar-extension:

#corollary[
  Let $A$ be a f.d. simple $k$-algebra, whose center $K$ is a Galois extension
  of $k$. Let $U$ be a simple left $A$-module. Then there is a
  $(K times.o_k A)$-isomorphism
  $ K times.o_k U ≅ W_1 plus.o dots plus.o W_t, $
  where $W_i$ is a simple left $A epsilon_i$-module.
]<cor:simple-module-galois-center-extension>

#proof[
  We may write $A ≅ M_r lr((D))$ where $D$ is a skewfield with center $K$. Then
  $A ≅ U^((r))$ as left $A$-modules. By
  @case:simple-algebra-galois-center-components[#context {
    reference-number-text(
      "("
        + reference-data(<prop:simple-algebra-center-scalar-extension>).text
        + reference-data(<case:simple-algebra-galois-center-components>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }], $K times.o_k A$ is a direct sum of $t$ simple algebras $A epsilon_i$, and
  $A epsilon_i ≅ M_r lr((D))epsilon_i$ for each $i$. Thus
  $
    K times.o_k A ≅ plus.o.big_(i=1)^t M_r lr((D))epsilon_i
    ≅ (W_1 plus.o dots plus.o W_t)^((r))
  $
  as left $(K times.o_k A)$-modules. Since
  $K times.o_k A ≅ (K times.o_k U)^((r))$, this gives the desired result.
]

Let us combine @prop:simple-algebra-center-scalar-extension with the results in
§~@i:ss:splitting-fields to obtain a more precise form of the basic Theorem
@i:prop:galois-orbit-simple-module-extension. We again restrict our attention to
simple modules over a simple algebra, since the general case eventually reduces
to this special case. The fundamental result, which will be applied later to the
case of group algebras, is as follows:

#theorem[
  Let $A=M_r lr((D))$ be a f.d. simple $k$-algebra, where $D$ is a skewfield
  with center#footnote[We are not assuming here that $K$ is a Galois extension
    of $k$.] $K$ and index $m$. Let $E$ be a finite Galois extension of $k$ with
  Galois group $frak(G)$, and assume that $E$ splits $A$ over $k$, that is,
  $E times.o_k A$ is a split semisimple $E$-algebra. Then
  $
    E times.o_k K=plus.o.big_(i=1)^t E epsilon_i quad "and" quad
    E times.o_k A=plus.o.big_(i=1)^t A_i,
    quad A_i=(E times.o_k A)epsilon_i,
  $
  where the ${epsilon_i}$ are orthogonal central primitive idempotents, and
  $t=dim_k K$. For each $i$, $A_i$ is a simple algebra whose center
  $E epsilon_i$ is isomorphic to $E$. Then we have:
  #source(751)
  #case-list(
    numbering: "(i)",
    [#case[
      $frak(G)$ acts transitively on the idempotents
      ${epsilon_1,dots,epsilon_t}$, and on the simple components
      ${A_1,dots,A_t}$ of $E times.o_k A$.
    ]<case:split-extension-galois-component-orbit>],
    [#case[
      For each $i$, $1≤i≤t$, let $V_i$ be a simple left $A_i$-module. Then
      $frak(G)$ acts transitively on the set ${V_1,dots,V_t}$, which is a full
      set of simple $(E times.o_k A)$-modules. Let
      $ frak(H)={sigma in frak(G):attach(V_1, tl: sigma) ≅ V_1}. $
      Then $K$ is isomorphic to the subfield of $E$ fixed by $frak(H)$.
    ]<case:split-extension-character-stabilizer-field>],
    [#case[
      Let $U$ be a simple left $A$-module. Then
      $
        E times.o_k U ≅ (V_1 plus.o dots plus.o V_t)^((m))
        quad "as left" (E times.o_k A)"-modules".
      $
    ]<case:split-extension-simple-module-index-multiplicity>],
  )
]<th:simple-algebra-splitting-field-index-multiplicity>

#proof[
  Most of the above assertions were proved in
  @i:prop:galois-orbit-simple-module-extension and
  @i:cor:galois-orbits-simple-modules, and we restate part of the argument for
  convenience. Let $times.o_k$ be written as $times.o$ for convenience. Since
  $E times.o A$ is split, it follows from @i:lem:separable-split-extension that
  $K$ is separable over $k$, and also (by
  @case:simple-algebra-separable-center-components[#context {
    reference-number-text(
      "("
        + reference-data(<prop:simple-algebra-center-scalar-extension>).text
        + reference-data(<case:simple-algebra-separable-center-components>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }]) that $E times.o K$ is a direct sum of $t$ copies of $E$. This gives
  $t=dim_k K$, as claimed.

  We now write
  $ K=k(alpha)=k[x] slash (f(x)), quad "where" f(x)="min. pol." alpha. $
  Then $E times.o K=E[x] slash (f(x))$, so $f(x)$ factors completely in $E[x]$;
  thus
  $ f(x)=product_(i=1)^t (x-alpha_i), quad alpha_i in E. $
  Consequently we may write
  $
    E times.o K ≅ product_(i=1)^t E[x] slash (x-alpha_i)
    =plus.o.big_(i=1)^t E epsilon_i.
  $
  The Galois group $frak(G)=upright("Gal")(E slash k)$ acts transitively on the
  ${alpha_i}$, and also on the ${epsilon_i}$. If $sigma in frak(G)$ is such that
  $sigma(alpha_1)=alpha_i$, then $sigma(epsilon_1)=epsilon_i$. Thus for
  $sigma in frak(G)$,
  $
    sigma(epsilon_1)=epsilon_1 arrow.l.r.double sigma(alpha_1)=alpha_1
    arrow.l.r.double sigma "fixes the field" k(alpha_1).
  $
  Letting $frak(H)={sigma in frak(G):attach(V_1, tl: sigma) ≅ V_1}$, it follows
  that $sigma in frak(H)$ if and only if $sigma$ fixes $k(alpha_1)$. Therefore
  $k(alpha_1)$ is the subfield of $E$ fixed by $frak(H)$. But $K ≅ k(alpha_1)$,
  so part~@case:split-extension-character-stabilizer-field is proved.

  Finally, we have
  $ E times.o A ≅ plus.o.big_(i=1)^t M_l lr((E))epsilon_i $
  for some $l$. Comparing $E$-dimensions of both sides, we obtain $l=m r$. Since
  #source(752)
  $A ≅ U^((r))$ as left $A$-modules, we deduce that
  $
    E times.o A ≅ (E times.o U)^((r))
    ≅ plus.o.big_(i=1)^t V_i^((m r)),
  $
  so $E times.o U ≅ plus.o.big V_i^((m))$ as claimed. This completes the proof.
]

Now let $G$ be a finite group, and let $k$ be an arbitrary field, of
characteristic $≥0$. The results below hold whether or not $"char" k$ divides
$|G|$, and are of significance even when $"char" k=0$. Let $E$ be a finite
Galois extension of $k$, such that $E$ is a splitting field for $G$. By Exercise
@exc:finite-galois-group-splitting-field, such fields $E$ necessarily exist; see
also §~@i:ss:modular-splitting-fields. For such a field $E$, the $E$-algebra
$E G slash "rad" E G$ is a split semisimple $E$-algebra, and each simple
$E G$-module $V$ is absolutely simple (that is, $upright("End")_(E G) V ≅ E$).

With the above notation, let $V$ be a simple $E G$-module. We say that $V$ is
#idx("Realizable")_realizable_ in a subfield $F$ of $E$ if $V ≅ E times.o_F V_0$
for some $F G$-module $V_0$ (which is then necessarily simple). If $V$ affords
the matrix representation $T$ of $G$, then $V$ is realizable in $F$ if and only
if $T$ is equivalent (over $E$) to an $F$-representation of $G$. In this case,
$F$ must contain all of the character values ${zeta(x):x in G}$, where $zeta$ is
the character of $G$ afforded by $V$ (or $V_0$).

Let us denote by $k(zeta)$ the field obtained by adjoining to $k$ all of the
character values ${zeta(x):x in G}$. Since each $zeta(x)$ is a sum of roots of
unity, it follows that $k(zeta)$ is a subfield of a cyclotomic extension of $k$,
and therefore $k(zeta)$ is a Galois extension of $k$.

If $U$ is a simple left $k G$-module, then $("rad" k G)U=0$. Since
$"rad" E G=E times.o_k "rad" k G$ by the proof of
@i:th:group-algebra-separable-radical-quotient, it follows that $E times.o_k U$
is a semisimple $E G$-module. By @i:th:separable-extension-radical-simples, each
simple $E G$-module $V$ is a summand of $E times.o_k U$ for some simple
$k G$-module $U$, unique up to isomorphism. The preceding Theorem
@th:simple-algebra-splitting-field-index-multiplicity plays a key role in
studying the relationship between $U$ and $V$, and in determining in which
fields $V$ is realizable. Our main result is as follows:

#theorem[
  Let $G$ be a finite group, $k$ any field, and let $E$ be a splitting field for
  $G$, such that $E$ is a finite Galois extension of $k$. Let
  $frak(G)=upright("Gal")(E slash k)$ be the Galois group of $E$ over $k$. Then
  we have:
  #case-list(
    numbering: "(i)",
    [#case[
      For $U$ a simple left $k G$-module, set
      $
        D=upright("End")_(k G) U, quad K="center of" D,
        quad m="index of" D, quad t=dim_k K.
      $
      <eq:schur-index-division-algebra-data>
      Then there is an isomorphism of $E G$-modules
      $ E times.o_k U ≅ (V_1 plus.o dots plus.o V_t)^((m)), $
      <eq:schur-index-simple-module-extension>
      where ${V_1,dots,V_t}$ are a set of nonisomorphic simple left
      $E G$-modules permuted transitively by $frak(G)$.
    ]<case:schur-index-galois-module-decomposition>],
    [#case[
      Let $zeta$ be an absolutely irreducible character of $G$, afforded by some
      #source(753)
      (absolutely) simple left $E G$-module $V$. There is a simple $k G$-module
      $U$, unique up to isomorphism, such that $zeta$ occurs in the character
      $eta$ of $G$ afforded by $U$. Then $V$ is one of the ${V_i}$ occurring in
      @eq:schur-index-simple-module-extension, say $V=V_1$, and we have
      $
        eta=m(zeta_1+dots+zeta_t), quad
        K ≅ k(zeta_1)=dots=k(zeta_t),
      $
      where $V_i$ affords the character $zeta_i$ of $G$.
    ]<case:schur-index-character-field>],
    [#case[
      Suppose that the absolutely irreducible character $zeta$ of $G$ is
      afforded by a simple $F G$-module, where $F$ is a finite extension of $k$.
      Then $F supset k(zeta)$, and
      $ dim_(k(zeta)) F "is a multiple of" m. $
      Further, there exist such fields $F$ for which $dim_(k(zeta)) F=m$.
    ]<case:schur-index-minimal-realization-degree>],
  )
]<th:schur-index-character-realization>

#proof[
  The discussion preceding the statement of the theorem shows that there exist
  splitting fields $E$ for $G$ which are finite Galois over $k$. Further, by
  @i:th:group-algebra-separable-radical-quotient we have
  $
    E times.o_k (k G slash "rad" k G)=E G slash "rad" E G
    ="split semisimple" E"-algebra".
  $
  Let us write
  $ k G slash "rad" k G=plus.o.big B_j, $
  where the ${B_j}$ are f.d. simple $k$-algebras. Given a simple $k G$-module
  $U$, there is a unique $j$ such that $U$ is a simple faithful left
  $B_j$-module. For $x in k G$, let $x_l$ denote left multiplication on $U$, and
  set $(k G)_l={x_l:x in k G}$. Then $U$ is also a simple faithful left
  $(k G)_l$-module. Therefore $B_j ≅ (k G)_l$ as $k$-algebras, and so
  $ E times.o_k B_j ≅ (E G)_l=E times.o_k (k G)_l $
  as algebras acting from the left on $E times.o_k U$. By the above,
  $E times.o_k B_j$ is a split semisimple $E$-algebra.

  Now set $A=(k G)_l$ and $D=upright("End")_(k G) U=upright("End")_A U$. Then
  the assertions in part~@case:schur-index-galois-module-decomposition are
  merely a restatement of part of Theorem
  @th:simple-algebra-splitting-field-index-multiplicity.

  To prove part~@case:schur-index-character-field, let $V$ afford the absolutely
  irreducible character $zeta$ of $G$. By
  @i:th:separable-extension-radical-simples, $V$ is a summand of $E times.o_k U$
  for some simple $k G$-module $U$. Decompose $E times.o_k U$ as in
  @eq:schur-index-simple-module-extension, with $V=V_1$. Let $zeta_i$ be the
  character of $G$ afforded by $V_i$, $1≤i≤t$, and let $U$ afford the character
  $eta$. Then @eq:schur-index-simple-module-extension gives
  $ eta=m(zeta_1+dots+zeta_t), $
  where $t=dim_k K$ as in @eq:schur-index-division-algebra-data. The characters
  ${zeta_1,dots,zeta_t}$ are distinct by the Frobenius-Schur Theorem
  @i:th:frobenius-schur-matrix-coordinates, and by
  part~@case:schur-index-galois-module-decomposition, $frak(G)$ permutes these
  characters transitively.

  #source(754)
  Now write
  $
    E times.o_k A=plus.o.big_(i=1)^t A_i,
    quad A_i="simple" k"-algebra",
  $
  where $V_i$ is a simple left $A_i$-module, and where
  $A_i ≅ M_(m r) lr((E))epsilon_i$ as in
  @th:simple-algebra-splitting-field-index-multiplicity. Put
  $frak(H)={sigma in frak(G):sigma(A_1)=A_1}$, so we have
  $
    frak(H)={sigma in frak(G):attach(V_1, tl: sigma) ≅ V_1}
    ={sigma in frak(G):sigma(zeta_1)=zeta_1}.
  $
  It follows that the subfield of $E$ fixed by $frak(H)$ is precisely
  $k(zeta_1)$, so $K ≅ k(zeta_1)$ by
  @th:simple-algebra-splitting-field-index-multiplicity. This completes the
  proof of part~@case:schur-index-character-field.

  Before starting the proof of
  part~@case:schur-index-minimal-realization-degree, we examine formula
  @eq:schur-index-simple-module-extension more carefully, using the fact that
  $K=k(zeta_1)=dots=k(zeta_t)$ is a Galois extension of $k$. By
  @cor:simple-module-galois-center-extension we have
  $ K times.o_k U ≅ W_1 plus.o dots plus.o W_t, $
  a sum of $t$ nonisomorphic simple $K G$-modules ${W_i}$ that are permuted
  transitively by $upright("Gal")(K slash k)$. The proof of
  @cor:simple-module-galois-center-extension shows also that $W_i$ is a simple
  $M_r lr((D))$-module for some $r$ (independent of $i$), so
  $upright("End")_(K G) W_i ≅ D$. Further,
  $
    E times.o_k U ≅ E times.o_K (K times.o_k U)
    ≅ plus.o.big_(i=1)^t (E times.o_K W_i).
  $
  By @eq:schur-index-simple-module-extension, we have
  $ E times.o_K W_i ≅ V_i^((m)). $
  Thus, in the step from $k$ to $K$, the simple $k G$-module $U$ splits into $t$
  nonisomorphic simple $K G$-modules ${W_i}$. In the step from $K$ to $E$, each
  $W_i$ splits into $m$ copies of the absolutely simple $E G$-module $V_i$.

  We now prove part~@case:schur-index-minimal-realization-degree, so let
  $F supset k$ be a field in which the character $zeta$ is realizable. Obviously
  $F supset k(zeta)=K$, and there is an absolutely simple $F G$-module $X$
  affording the character $zeta$, such that $X$ is a summand of some
  $F times.o_K W_i$, where the ${W_i}$ are the simple $K G$-modules defined
  above. Since $upright("End")_(K G) W_i ≅ D$, it follows from Exercise
  @exc:absolute-simplicity-division-splitting that $F$ splits $D$ over $K$. Then
  $ F times.o_K D ≅ M_m lr((F)). $
  Let $Y=F^m$ be a simple left $M_m lr((F))$-module. Restriction through
  $D arrow F times.o_K D$ makes $Y$ a left $D$-space. Counting dimensions over
  $K$ gives
  $ (dim_K F)m=m^2 dim_D Y, quad dim_K F=m dim_D Y, $
  so $m$ divides $dim_K F$ as claimed.

  On the other hand, we may choose $F$ to be a maximal subfield of $D$. Then
  #source(755)
  by @i:cor:maximal-subfield-degree, $dim_K F=m$ and $F$ splits $D$ over $K$.
  The preceding argument can be reversed to show that $zeta$ is realizable in
  $F$. This completes the proof of the theorem.
]

In the above, we started with an absolutely irreducible character $zeta$ of $G$,
afforded by some absolutely simple $E G$-module $V$. We showed that there exists
a simple $k G$-module $U$, affording a character $eta$ of $G$, with
$
  eta=m(zeta_1+dots+zeta_t), quad
  E times.o_k U ≅ V_1^((m)) plus.o dots plus.o V_t^((m)),
$
where (say) $V=V_1$ and $zeta=zeta_1$. The characters ${zeta_i}$ are distinct,
and are a full set of algebraic conjugates of $zeta$ under the action of
$upright("Gal")(E slash k)$. The integer $m$ is the index of the skewfield $D$,
where $D=upright("End")_(k G) U$. The center $K$ of $D$ is isomorphic (over $k$)
to each field $k(zeta_i)$ obtained by adjoining the character values
${zeta_i lr((x)):x in G}$ to $k$.

We call $m$ the #idx("Schur index")_Schur index_ of $zeta$ relative to $k$,
#nidx("$m_K lr((zeta))$", "Schur index")
and write $m=m_k lr((zeta))$. From the above theorem, we obtain at once:

#corollary[
  Let $m=m_k lr((zeta))$ be the Schur index of the absolutely irreducible
  character $zeta$ of $G$.
  #case-list(
    numbering: "(i)",
    [#case[
      If $mu$ is a character of $G$ afforded by some $k G$-module, then the
      multiplicity of $zeta$ in $mu$ is a multiple of $m$. For suitably chosen
      $mu$, this multiplicity equals $m$.
    ]<case:schur-index-character-multiplicity-divisibility>],
    [#case[
      Let $V$ be an absolutely simple $E G$-module affording the character
      $zeta$. Then $V^((m))$ is realizable in the field $k(zeta)$, and $m$ is
      the smallest positive integer with this property. Furthermore,
      $ m "is a divisor of" dim_E V. $
    ]<case:schur-index-minimal-realizable-multiple>],
  )
]<cor:schur-index-multiplicities-realizable-multiple>

#proof[
  The assertions are clear from Theorem @th:schur-index-character-realization.
  For the second statement in
  part~@case:schur-index-minimal-realizable-multiple, we note that by Theorem
  @th:schur-index-character-realization, $V$ is a simple
  $M_(m r) lr((E))$-module for some integer $r$; then $dim_E V=m r$, which is a
  multiple of $m$.
]

For fields of characteristic $p>0$, the theory becomes much simpler.

#theorem[
  Let $zeta$ be an absolutely irreducible character of $G$ afforded by an
  $E G$-module $V$, and suppose that $"char" E=p>0$. Then $m_k lr((zeta))=1$,
  and $V$ is realizable in the field $k(zeta)$.
]<th:positive-characteristic-schur-index-one>

#proof[
  The proof of @i:cor:group-algebra-multiplicity-free-extension shows that
  $k G slash "rad" k G$ is a direct sum of matrix algebras over fields. Thus all
  Schur indices are $1$, and the remaining assertion of
  @th:positive-characteristic-schur-index-one follows from
  @case:schur-index-minimal-realizable-multiple[#context {
    reference-number-text(
      "("
        + reference-data(
          <cor:schur-index-multiplicities-realizable-multiple>,
        ).text
        + reference-data(<case:schur-index-minimal-realizable-multiple>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }].
]

#remarks[
  #case-list(
    numbering: "(i)",
    [#case[
      Let $E$ be a splitting field for $G$ containing $k$, and let $zeta$ be an
      absolutely irreducible character of $G$ (afforded by a simple
      $E G$-module). By @case:schur-index-minimal-realization-degree[#context {
        reference-number-text(
          "("
            + reference-data(<th:schur-index-character-realization>).text
            + reference-data(<case:schur-index-minimal-realization-degree>)
              .text
              .trim(regex("[()]"))
            + ")",
        )
      }], there exist fields $F supset K$, with $dim_K F=m_k lr((zeta))$, such
      that $zeta$ is realizable in $F$ (that is, $zeta$ is afforded by some
      simple $F G$-module). However, there is no
      #source(756)
      guarantee that $F$ can be chosen as a subfield of $E$, and indeed there
      exist counterexamples to this supposition (Fein~@bib:Fein1974).
    ]<case:minimal-realization-field-outside-splitting-field>],
    [#case[
      Let $k$ be an algebraic number field, and let $M_r lr((D))$ be a simple
      component of $k G$, where $D$ is a skewfield of index $m$. By
      @cor:schur-index-multiplicities-realizable-multiple, $m r=zeta(1)$ for
      some irreducible complex character $zeta$ of $G$. Since $zeta(1)$ divides
      $|G|$, we conclude that also $m r$ divides $|G|$. Thus, each Schur index
      $m_k lr((zeta))$ is a divisor of $|G|$. We proved these results in another
      manner in @i:th:schur-index-divides-group-order, using Jacobinski's
      Conductor Formula @i:th:jacobinski-conductor-formula.
    ]<case:schur-index-divides-group-order>],
    [#case[
      Let $zeta in upright("Irr") G$, and let $K$ be a field of characteristic
      $0$. Then for any character $eta$ of $G$ afforded by a $K G$-module,
      $ (zeta,eta)_G ≡ 0 quad ("mod" m_K lr((zeta))). $
      Further, $(zeta,eta)_G=m_K lr((zeta))$ for suitably chosen $eta$.
    ]<case:schur-index-inner-product-divisibility>],
  )
]<rem:schur-index-fields-divisibility-inner-products>

#example(numbered: false)[
  Let $G$ be a quaternion group of order $8$. Then
  $ QQ G ≅ QQ plus.o QQ plus.o QQ plus.o QQ plus.o upright(sans(H)), $
  where $upright(sans(H))$ is the skewfield of rational quaternions, and is of
  #idx(
    "Index",
  )index $2$. There is a unique irreducible complex character $zeta$ of $G$ of
  degree $2$, afforded by a simple $E G$-module $V$, where $E=QQ(i)$. Then
  $V^((2))$ is realizable in $QQ$, and indeed
  $E times.o_QQ upright(sans(H)) ≅ V^((2))$, but $V$ is not realizable in $QQ$.
  The character $zeta$ is rational-valued (necessarily!), and $QQ(zeta)=QQ$. See
  also Exercise @exc:quaternion-simple-module-form-types.
]<exm:quaternion-rational-schur-index-two>

=== Schur Indices for Group Algebras <ss:group-algebra-schur-indices>

We present here a number of general results on Schur indices and the structure
of group algebras. For example, we study the group algebra $QQ G$ of a $p$-group
$G$; we have already used the structure of $QQ G$ in our proofs in
§~@ss:p-group-kernel-groups, for example. We also give some results on $K G$ for
$K$ a $p$-adic field and $G$ any $p'$-group.

We begin with:

#theorem[
  Let $K$ be a finite extension of the $p$-adic field $QQ_p$, where $p$ is any
  prime, and let $G$ be a finite group whose order $n$ is prime to $p$. Then
  $ K G ≅ product_(i=1)^t M_(n_i) lr((K_i)), $
  where each $K_i$ is a field, unramified over $K$.
]<th:prime-to-p-group-algebra-unramified-splitting>

#proof[
  Let $A=K G$, $Lambda=R G$, where $R$ is the valuation ring of $K$. Let $P$ be
  the prime ideal of $R$, and $overline(R)=R slash P$ its residue class field of
  characteristic $p$. By hypothesis $n in R^dot$, so by
  @i:prop:group-ring-maximality $Lambda$ is a maximal $R$-order in $A$. Let us
  write
  $
    A=plus.o.big_(i=1)^t A_i, quad
    A_i="simple algebra with center" K_i, quad dim_(K_i) A_i=n_i^2.
  $
  #source(757)
  Then $Lambda=plus.o.big Lambda_i$, with $Lambda_i$ a maximal $R_i$-order in
  $A_i$, where $R_i$ is the valuation ring of $K_i$.

  Since $Lambda$ is maximal, the Jacobinski Conductor Formula
  @i:th:jacobinski-conductor-formula shows that $frak(D)_i^(-1)=Lambda_i$ for
  each $i$ (since $n slash n_i in R^dot$), where $frak(D)_i^(-1)$ is the inverse
  different of $Lambda_i$ relative to $R$, using reduced traces. Thus the
  different $frak(D)(Lambda_i slash R)=Lambda_i$. But the proof of
  @i:th:jacobinski-central-conductor shows that
  $ frak(D)(Lambda_i slash R)=frak(D)(Lambda_i slash R_i)frak(D)(R_i slash R). $
  Further, by @bib:Reiner1975[MO] (20.3),
  $ frak(D)(Lambda_i slash R_i)=("rad" Lambda_i)^(m_i-1), $
  where $m_i$ is the index of $A_i$. Also, by Exercise
  @i:exc:different-ramification-bound, $("rad" R_i)^(e_i-1)$ divides
  $frak(D)(R_i slash R)$, where $e_i$ is the ramification index of $K_i$ over
  $K$. It follows that $m_i=1$ and $e_i=1$, which proves the theorem.
]

It is of interest to give an alternative proof of the above theorem using
character theory. As above, let $K$ be a $p$-adic field and $G$ a $p'$-group of
order $n$. Let $zeta$ be an absolutely irreducible character of $G$, afforded by
a representation in some extension field of $K$. Then there is a simple
component $A_i$ of $K G$, for which the simple $A_i$-module $U$ affords a
character $eta$ in which $zeta$ occurs. By
@th:schur-index-character-realization, we have
$ K subset.eq K_i ≅ K(zeta) subset.eq K(root(n, 1)), $
where $K_i$ is the center of $A_i$. Since $p divides.not n$, it follows from
§~@i:ss:cyclotomic-fields that $K(root(n, 1)) slash K$ is unramified, and
therefore also $K_i slash K$ is unramified.

It remains for us to show that the Schur index $m_K lr((zeta))$ equals $1$.
Since
$ m_(K(zeta)) lr((zeta))=m_K lr((zeta)) $
<eq:schur-index-character-field-invariance>
by @case:schur-index-minimal-realization-degree[#context {
  reference-number-text(
    "("
      + reference-data(<th:schur-index-character-realization>).text
      + reference-data(<case:schur-index-minimal-realization-degree>)
        .text
        .trim(regex("[()]"))
      + ")",
  )
}], we may replace $K$ by $K(zeta)$. Changing notation, we assume now that
$K=K(zeta)$, so the values ${zeta(x):x in G}$ lie in $R$. By the proof of
@th:schur-index-character-realization (see also
@case:schur-index-minimal-realizable-multiple[#context {
  reference-number-text(
    "("
      + reference-data(
        <cor:schur-index-multiplicities-realizable-multiple>,
      ).text
      + reference-data(<case:schur-index-minimal-realizable-multiple>)
        .text
        .trim(regex("[()]"))
      + ")",
  )
}]), we have $eta=m zeta$, where $m=m_K lr((zeta))$, and so $R$ contains all
values of the character $eta$.

Let bars denote reduction $"mod" P$, and let us show that $overline(eta)$ is an
irreducible character of $G$. Let $M$ be any full $R G$-lattice in $U$, and set
$overline(M)=M slash P M$, an $overline(R)G$-module which affords the character
$overline(eta)$. Since $overline(R)G$ is semisimple, $overline(M)$ is a direct
sum of simple modules. By @i:th:complete-ring-idempotent-decompositions, each
direct sum decomposition of $overline(M)$ lifts to one of $M$. But $M$ is
indecomposable, since $K M=U$ is a simple module. This shows that $overline(M)$
is simple, and hence $overline(eta)$ is irreducible.

To complete the argument, we show directly that every simple component of $K G$
is split over its center.#ed-note[
  The original reduction argument infers absolute simplicity from the reduced
  character values and then infers an integer multiplicity from its reduction
  modulo $p$. These implications require the following additional argument.
] Put $Lambda=R G$ and $Z=op("Z")(Lambda)$. Since $n$ is a unit of $R$,
$n^(-1)sum_(g in G) g times.o g^(-1)$ is a separability idempotent, and
$a arrow n^(-1)sum_(g in G) g a g^(-1)$ is an $R$-linear projection onto $Z$.
This projection commutes with reduction, so
$ Z slash P Z ≅ op("Z")(overline(R)G). $
Maschke's Theorem and the fact that a finite division ring is a field show that
this center is a product of finite separable extensions of $overline(R)$. The
finite free commutative $R$-algebra $Z$ is therefore étale: its module of
relative differentials reduces to zero and is zero by Nakayama's Lemma. Since
$R$ is complete, $Z=product_i R_i$, where each $R_i$ is the valuation ring of a
finite unramified extension $K_i$ of $K$.

Write $Lambda=product_i Lambda_i$ accordingly. Each reduction
$Lambda_i slash P Lambda_i$ is a full matrix algebra over the residue field of
$R_i$. Lift its orthogonal primitive idempotents, and their matrix-unit
equivalences, through the radical of the complete order $Lambda_i$. These lifts
give
$ Lambda_i ≅ M_(d_i) lr((e_i Lambda_i e_i)), $
where $e_i$ lifts a primitive matrix idempotent. The corner $e_i Lambda_i e_i$
is finite free over $R_i$, and its reduction has dimension $1$ over the residue
field. Hence its rank is $1$, and the identity map $R_i arrow e_i Lambda_i e_i$
is an isomorphism by Nakayama's Lemma. Consequently
$Lambda_i ≅ M_(d_i) lr((R_i))$ and $K G ≅ product_i M_(d_i) lr((K_i))$, with
each $K_i slash K$ unramified. In particular $m_K lr((zeta))=1$, as required.

#source(758)
For yet another version of the proof, and for generalizations of the theorem,
see Feit~@bib:Feit1982, Ch. IV, Th. 9.3 and its corollaries.

We now turn to some results on group algebras over global fields, and
concentrate on the structure of $QQ G$, where $G$ is a $p$-group. We intend to
show that, for $p$ odd, $QQ G$ is a direct sum of matrix algebras over fields
which are cyclotomic extensions of $QQ$. A somewhat more complicated result
holds when $p=2$, since quaternion skewfields may occur in this case. Our
approach is as follows: We first establish Schilling's Theorem, which says that
if $G$ is nilpotent, then each simple component of $QQ G$ has index $1$ or $2$.
We then use some easy character theory to find the centers of these simple
components. As we shall see, it suffices to prove the results when $G$ is a
$p$-group, and then use the fact that a nilpotent group is the direct product of
its Sylow subgroups.

Our proof of Schilling's Theorem follows that given in @bib:Reiner1975[MO]
(41.9), and as a preliminary step, we review some facts about indices of
skewfields and Hasse invariants. Let $D$ be a skewfield with center $K$ and
index $m$, where $K$ is an algebraic number field. For each prime $P$ of $K$,
let $m_P$ be the _local index_ of $D$ at $P$ (see the discussion preceding
@lem:prescribed-reduced-characteristic-polynomial). Note that if $P$ is an
infinite prime of $K$, then $m_P=1$ if $P$ is a complex prime, or if $P$ is real
and $D_P$ is a matrix algebra over $K_P$. On the other hand, $m_P=2$ if $P$ is
real and $D_P$ is a matrix algebra over the real quaternions.

The relation between the global index $m$ of $D$ and the local indices ${m_P}$
is given by
$ m="least common multiple of" {m_P:P="prime of" K}. $
<eq:global-index-local-index-lcm>
(See @bib:Reiner1975[MO] (32.19).)

For each prime $P$ of $K$, we associate with the skewfield $D$ an element
$"inv"_P D in QQ slash ZZ$, called the _Hasse invariant_ of $D$ at $P$, defined
by $"inv"_P D=r_P slash m_P$, with $r_P in ZZ$, $(r_P,m_P)=1$. Explicitly, we
write
$
  D_P ≅ M_l lr((Omega)), quad
  Omega="skewfield with center" K_P "and index" m_P.
$
For $P$ an infinite prime, choose $r_P=1$ always, so
$"inv"_P D=1 slash m_P in QQ slash ZZ$, and thus $"inv"_P D$ is $0$ or
$1 slash 2$ $("mod" ZZ)$. On the other hand, let $P$ be a finite prime of $K$,
let $q_P$ be the cardinality of its residue field, and let $W=K_P lr((omega))$
be the unique unramified extension of $K_P$ of degree $m_P$, with $omega$ a
primitive $(q_P^(m_P)-1)$-st root of $1$. Write $"inv"_P D=r_P slash m_P$, and
choose a nonnegative integer $s_P$ such that $r_P s_P≡1$ $("mod" m_P)$. Let
$"Frob"_(q_P)$ denote arithmetic Frobenius on $W$, inducing $a arrow a^(q_P)$ on
its residue field. We may choose a prime element $pi in Omega$ such that
$pi^(m_P)$ is a prime element of $K_P$ and
$
  Omega=plus.o.big_(i=0)^(m_P-1) W pi^i,
  quad pi a pi^(-1)="Frob"_(q_P)^(s_P) lr((a)) quad (a in W).
$
In particular $pi omega pi^(-1)=omega^(q_P^(s_P))$. With the convention that the
cyclic algebra for arithmetic Frobenius and a prime element has invariant
$1 slash m_P$, this presentation, for $m_P>1$, has invariant $r_P slash m_P$ in
$QQ slash ZZ$, since the inverse of $s_P$ modulo $m_P$ is $r_P$. When $m_P=1$,
the extension and its automorphism are trivial. The numerator $r_P$ is uniquely
determined modulo $m_P$, with $(r_P,m_P)=1$ (see @bib:Reiner1975[MO],
§14).#ed-note[
  The root exponent is a power of the residue cardinality, not the invariant
  numerator. For index $3$ and residue cardinality $7$, the exponents $7$ and
  $49$ are both $1$ modulo $3$, although the corresponding invariant numerators
  $1$ and $2$ differ.
]

The Hasse invariants ${"inv"_P D}$ satisfy the condition
$ sum_P r_P slash m_P in ZZ, $
<eq:hasse-invariant-reciprocity>
#source(759)
where $P$ ranges over all primes of $K$, including the infinite primes. (Indeed,
this is the only restriction in the Hasse invariants. Given any set of fractions
$r_P slash m_P$ in lowest terms, whose sum is an integer, and such that $m_P=1$
for complex $P$, $m_P=1$ or $2$ for real $P$, there always exists a skewfield
$D$ with prescribed Hasse invariants ${r_P slash m_P}$; see @bib:Reiner1975[MO]
(32.12).)

We now prove:

#theorem(name: "Schilling's Theorem")[
  #idx("Schilling's Theorem")
  Let $G$ be a group of order $p^r$, where $p$ is prime and $r≥0$. Let $K$ be
  any field of characteristic $0$.
  #case-list(
    numbering: "(i)",
    [#case[
      For $p$ odd, each simple component of $K G$ is a full matrix algebra over
      a field.
    ]<case:odd-p-group-schur-index-one>],
    [#case[
      For $p=2$, each simple component of $K G$ has the form $M_k lr((D))$,
      where $D$ is either a field or a skewfield of index $2$.
    ]<case:two-group-schur-index-at-most-two>],
  )
]<th:schilling-p-group-schur-index>

#proof[
  We begin with the case where $K=QQ$, so let $M_k lr((D))$ be a simple
  component of $QQ G$, where $D$ is a skewfield with center $E$. For each prime
  $P$ of $E$, let $m_P$ be the local index of $D$ at $P$, and $r_P slash m_P$
  its Hasse invariant. By @case:schur-index-character-field[#context {
    reference-number-text(
      "("
        + reference-data(<th:schur-index-character-realization>).text
        + reference-data(<case:schur-index-character-field>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }], $E subset K(omega)$ where $omega$ is a primitive $p^r$-th root of $1$. By
  §~@i:ss:cyclotomic-fields, there is thus a unique prime $P_0$ of $E$ dividing
  $p$.

  Now suppose $p$ is odd; then the index $m$ of $D$ is odd, by
  @case:schur-index-divides-group-order[#context {
    reference-number-text(
      "("
        + reference-data(
          <rem:schur-index-fields-divisibility-inner-products>,
        ).text
        + reference-data(<case:schur-index-divides-group-order>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }], since $m divides p^r$. It follows at once that $m_P$ is odd for every
  prime $P$ of $E$, so in particular no infinite prime $P$ of $E$ can have local
  index $2$. The sum in @eq:hasse-invariant-reciprocity thus consists of a
  single term $r_(P_0) slash m_(P_0)$, where $r_(P_0) in ZZ$ and
  $(r_(P_0),m_(P_0))=1$. It follows that $m_(P_0)=1$, and therefore $m=1$ by
  @eq:global-index-local-index-lcm. Thus $D=E$, as claimed.

  On the other hand, for $p=2$ there may be real primes $P$ of $E$ such that
  $m_P=2$. It follows from @eq:hasse-invariant-reciprocity that
  $r_(P_0) slash m_(P_0)=1 slash 2$ or $1$, so $m_(P_0)=1$ or $2$. Thus $m=1$ or
  $2$ by @eq:global-index-local-index-lcm, so either $D=E$ or else $D$ is a
  skewfield of index $2$; in the latter case, there must exist at least one real
  prime $P$ of $E$ such that $D_P$ is the skewfield of real quaternions.

  Now let $K$ be arbitrary, and let $B_j$ range over the simple components of
  $QQ G$. Then $K G=plus.o.big (K times.o_QQ B_j)$. If $E_j$ denotes the center
  of $B_j$, then
  $ K times.o_QQ B_j=(K times.o_QQ E_j)times.o_(E_j) B_j. $
  We may write $K times.o_QQ E_j=plus.o.big F_(i j)$, with each $F_(i j)$ a
  finite field extension of $K$. Since the index of $F_(i j) times.o_(E_j) B_j$
  divides the index of $B_j$ (Exercise
  @exc:division-algebra-index-scalar-extension), the theorem is proved.
]

This theorem was rediscovered by Witt and Roquette, with different proofs. As an
immediate corollary, we have:

#corollary[
  Let $G$ be a finite nilpotent group of order $n$, and let $K$ be a field of
  characteristic $0$. For $n$ odd, each simple component of $K G$ is a full
  matrix algebra over a field. For $n$ even, each simple component is a full
  matrix algebra over a field or over a skewfield of index $2$.
]<cor:nilpotent-group-schur-index-at-most-two>

#source(760)
#proof[
  Let $G_(p_1),dots,G_(p_t)$ be the Sylow subgroups of $G$. Then
  $G=G_(p_1) times dots times G_(p_t)$, and so
  $ K G ≅ K G_(p_1) times.o_K dots times.o_K K G_(p_t). $
  The result is then clear from Schilling's Theorem.
]

We now strengthen the previous results, and begin with:

#theorem[
  Let $G$ be a $p$-group, where $p$ is an odd prime. Then
  $ QQ G ≅ QQ plus.o plus.o.big_(i=1)^t M_(n_i) lr((K_i)), $
  where for $1≤i≤t$, $K_i$ is a cyclotomic extension $QQ(omega_i)$, with
  $omega_i$ a $p$-power root of $1$, and $dim_QQ K_i>1$.
]<th:schilling-odd-p-group-rational-components>

#proof[
  The simple component $QQ$ of $QQ G$ corresponds to the trivial representation
  of $G$. Now let $B$ be any simple component of $QQ G$, so its center $K$ has
  the form $K=QQ(zeta)$, where $zeta in upright("Irr") G$, and thus $K$ is a
  subfield of a cyclotomic field. If $zeta$ is a linear character, the values
  ${zeta(x):x in G}$ are $p$-power roots of $1$, and clearly $QQ(zeta)$ is a
  cyclotomic field; note that $dim_QQ QQ(zeta)>1$ if $zeta≠1$.

  We use induction on $|G|$ to show that for each $zeta in upright("Irr") G$,
  $QQ(zeta)$ is a cyclotomic field. The result is clear from the above remarks
  when $|G|=p$, since then each $zeta in upright("Irr") G$ is a linear
  character. Now assume the result for proper subgroups of $G$, and let
  $zeta in upright("Irr") G$ be nonlinear. By Blichfeldt's Theorem
  @i:th:nilpotent-group-monomial we may write $zeta=upright("ind")_S^G lambda$
  for some linear character $lambda$ on a proper subgroup $S$ of $G$. We may
  therefore write $zeta=upright("ind")_H^G theta$ for some
  $theta in upright("Irr") H$, where $H$ is a normal subgroup of $G$ of index
  $p$. Then $QQ(theta)=QQ(omega)$ for $omega$ some $p$-power root of $1$, by the
  induction hypothesis. Clearly $QQ(zeta) subset QQ(theta)$, and we shall now
  show that either $QQ(zeta)=QQ(omega)$ or $QQ(zeta)=QQ(omega^p)$.

  Let us write $G=chevron.l H,g chevron.r$, where $g^p in H$. For each $i$,
  $0≤i≤p-1$, let $theta_i in upright("Irr") H$ be the character conjugate to
  $theta$, defined by
  $ theta_i lr((x))=theta(g^(-i)x g^i), quad x in H. $
  Since $zeta=upright("ind")_H^G theta$ is irreducible, it follows from
  @i:th:induced-character-irreducibility that the characters ${theta_i:0≤i≤p-1}$
  are distinct, and $upright("ind")_H^G theta_i=zeta$ for each $i$. By Frobenius
  Reciprocity, these are the only irreducible characters of $H$ which induce to
  $zeta$. Since $H ⊴ G$, $zeta$ vanishes on $G-H$, and furthermore,
  $
    zeta(x)=sum_(i=0)^(p-1) theta_i lr((x))
    =sum_(i=0)^(p-1) theta(g^(-i)x g^i) quad "for" x in H.
  $
  We note also that $QQ(theta)=QQ(theta_i)$ for each $i$. The discussion now
  splits into two cases.

  #source(761)
  #case-list(
    prefix: "Case ",
    numbering: "1.",
    [#case[
      Suppose that the map $theta arrow attach(theta, tl: g)$ is induced by an
      automorphism $sigma$ of the field $QQ(theta)$, that is, for some
      $sigma in upright("Gal")(QQ(theta) slash QQ)$ we have
      $ theta(g^(-1)x g)=(theta(x))^sigma quad "for all" x in H. $
      Then for $x in H$,
      $
        zeta(x)=sum_(i=0)^(p-1) (theta(x))^(sigma^i)
        =T_(QQ(theta) slash F) theta(x),
      $
      where $F$ is the subfield of $QQ(theta)$ fixed by $sigma$, and $T$ denotes
      the trace map. Since $theta(g^(-p)x g^p)=theta(x)$ for $x in H$, we have
      $sigma^p=1$ and $sigma≠1$. But $upright("Gal")(QQ(theta) slash QQ)$ is a
      cyclic group of order $p^(k-1)(p-1)$, for some $k≥1$. In this case, we
      must therefore have $k≥2$, and $F$ is the unique subfield of $QQ(theta)$
      with $dim_F QQ(theta)=p$. Thus in this case we have $QQ(theta)=QQ(omega)$,
      and $QQ(zeta)=F=QQ(omega^p)$, where $omega$ is a primitive $p^k$-th root
      of $1$, and $k≥2$.
    ]<case:odd-p-character-field-galois-conjugation>],
    [#case[
      Let $Omega=upright("Gal")(QQ(theta) slash QQ)$, and suppose that
      $attach(theta, tl: g)≠theta^sigma$ for any $sigma in Omega$. We shall show
      that for each $sigma in Omega$, #named-equation(name: [$(ast)$])[
        $ zeta^sigma=zeta arrow.l.r.double theta^sigma=theta. $
      ]<eq:odd-p-character-field-stabilizer>
      Since $QQ(zeta) subset QQ(theta)$, this will imply that
      $QQ(zeta)=QQ(theta)$, as desired. To prove
      @eq:odd-p-character-field-stabilizer, note that if $sigma in Omega$ fixes
      $theta$, it also fixes $zeta$. Conversely, let $sigma in Omega$ be such
      that $zeta^sigma=zeta$. Then
      $ zeta=zeta^sigma=sum_(i=0)^(p-1) theta_i^sigma, $
      so $sigma$ must permute the $p$ characters ${theta_i:0≤i≤p-1}$. If
      $theta^sigma≠theta$, then $sigma$ permutes them cyclically, and therefore
      $attach(theta, tl: g)=theta^(sigma^j)$ for some $j$, contrary to the
      hypotheses of Case~@case:odd-p-character-field-stabilizer. Thus
      $theta^sigma=theta$, as claimed, which proves
      @eq:odd-p-character-field-stabilizer.
    ]<case:odd-p-character-field-stabilizer>],
  )

  We have now shown that in both cases $QQ(zeta)$ is a cyclotomic field. It
  remains to show that $QQ(zeta) supset QQ$ if $zeta≠1$. If $zeta$ is not the
  trivial character, we may (after changing notation) assume that $zeta$ is a
  faithful irreducible character of $G$, where $G$ is a nontrivial $p$-group.
  Then the center of $G$ contains an element $x≠1$, and we must have
  $zeta(x)=omega zeta(1)$, where $omega$ is a $p$-power root of $1$, $omega≠1$.
  Thus $dim_QQ QQ(zeta)>1$. This completes the proof of the theorem.
]

Turning to the case of $2$-groups, the situation is somewhat more complicated:

#theorem[
  Let $G$ be a $2$-group, and let $M_n lr((D))$ be a simple component of $QQ G$,
  where $D$ is a skewfield with center $K$ and index $m$. Then $m=1$ or $2$, and
  $K$ is a subfield of a cyclotomic field $QQ(omega)$, with $omega$ a $2$-power
  root of $1$. In the case $m=2$, $K$ must be a subfield of
  $QQ(omega+omega^(-1))$.
]<th:two-group-rational-simple-components>

#proof[
  The arguments used to prove @th:schilling-p-group-schur-index and
  @th:schilling-odd-p-group-rational-components show that $K subset QQ(omega)$
  #source(762)
  for some $omega$, and there is a unique finite prime $P_0$ of $K$ dividing
  $2$. Let $m_P$ be the local index of $D$ at $P$, for $P$ a prime of $K$. Then
  $m_P=1$ for all finite primes $P≠P_0$, while $m_(P_0)=1$ or $2$. The latter
  case can only occur when $m_P=2$ for some real prime of $K$, by virtue of
  @eq:hasse-invariant-reciprocity. Thus $m=1$ or $2$, and when $m=2$, $K$ must
  have at least one real prime. Thus $K subset QQ(omega+omega^(-1))$ if $m=2$.
]

#remarks(numbered: true)[
  #case-list(
    numbering: "(i)",
    [#case[
      For each subfield $K$ of $QQ(omega)$, where $omega$ is a $2$-power root of
      $1$, there exists a $2$-group $G$ such that $M_n lr((K))$ is a simple
      component of $QQ G$, for some $n$.
    ]<case:two-group-arbitrary-cyclotomic-subfield-center>],
    [#case[
      If $G$ is a nilpotent group of odd order, then combining the results of
      @th:schilling-odd-p-group-rational-components with those of
      @cor:nilpotent-group-schur-index-at-most-two, it follows that every simple
      component of $QQ G$ is a full matrix algebra over a cyclotomic field
      $QQ(root(n, 1))$, where $n$ divides $|G|$.
    ]<case:odd-nilpotent-group-cyclotomic-components>],
    [#case[
      For further results of this nature, see Feit~@bib:Feit1967, §14 and §16,
      and Rasmussen~@bib:Rasmussen1974.
    ]<case:rational-component-further-results>],
    [#case[
      Let $G$ be a finite group of exponent $n$, and let $K$ be any field of
      characteristic $0$. Let $p$ be a prime, and suppose that a Sylow
      $p$-subgroup $P$ of $upright("Gal")(K(root(n, 1)) slash K)$ is cyclic. If
      $|P|$ is even, assume further that $sqrt(-1) in K$. Then
      $p divides.not m_K lr((zeta))$ for every irreducible complex character
      $zeta$ of $G$. This result, due to
      Goldschmidt–Isaacs~@bib:Goldschmidt1975, generalizes Schilling's Theorem
      @th:schilling-p-group-schur-index.
    ]<case:cyclic-galois-sylow-schur-index-prime-to-p>],
  )
]<rem:group-algebra-schur-index-refinements>

=== The Benard-Schacher Theorem <ss:benard-schacher-theorem>

Let $K$ be an algebraic number field. It is a natural question to ask which
central simple $K$-algebras can occur as simple components of group algebras. If
$A$ is a central simple $K$-algebra occurring as a component of $k H$, where $k$
is a subfield of $K$ and $H$ is a finite group, then by
@th:schur-index-character-realization and its proof we know that $K=k(zeta)$ for
some $zeta in upright("Irr") H$, and that $A$ is one of the simple components of
$K H$. The Benard-Schacher Theorem is a beautiful and powerful result, which
relates the index of $A$ with the group of roots of $1$ in $K$.

To fix the notation, let $epsilon_m$ denote a primitive $m$-th root of $1$ over
$QQ$. For a f.d. central simple $K$-algebra $B$, we may write $B ≅ M_k lr((D))$
where $D$ is a skewfield with center $K$. We define
$ "index of" B="index of" D=m, quad "where" dim_K D=m^2. $
For each prime $P$ of $K$, whether finite or infinite, the $P$-adic completion
$B_P$ is a central simple $K_P$-algebra; its index $m_P$ is called the #idx(
  "Local index",
)_local index_ of $B$ at $P$. We also consider the #idx("Hasse invariant")_Hasse
invariant_ of $B$ at $P$, denoted by $"inv"_P B$, defined as in
§~@ss:group-algebra-schur-indices. This invariant is an element of $QQ slash ZZ$
of the form $"inv"_P B=r_P slash m_P$, where $r_P in ZZ$ and $(r_P,m_P)=1$.

The main result of this subsection is the following theorem, proved by
Benard–Schacher~@bib:Benard1972:

#theorem(name: "Benard-Schacher Theorem")[
  #idx("Benard-Schacher Theorem")
  Let $K$ be an algebraic number field, and let
  #source(763)
  $A$ be a central simple $K$-algebra occurring as a simple component of a group
  algebra $k H$, where $k$ is a subfield of $K$, and $H$ is a finite group. Let
  $m$ be the index of $A$. Then
  #case-list(
    numbering: "(i)",
    [#case[$K$ contains $epsilon_m$.]<case:schur-component-roots-of-unity>],
    [#case[
      For each prime $P$ of $K$ and each $sigma in upright("Aut")_QQ K$,
      $ "inv"_P A=r dot "inv"_(P^sigma) A quad ("mod" ZZ), $
      <eq:schur-component-conjugate-hasse-invariants>
      where $sigma(epsilon_m)=epsilon_m^r$, and where $P^sigma$ is the conjugate
      (under $sigma$) of the prime $P$. Consequently,
      $
        m_P lr((A))=m_(P^sigma) lr((A))
        quad "for each" sigma in upright("Aut")_QQ K.
      $
      <eq:schur-component-conjugate-local-indices>
    ]<case:schur-component-conjugate-prime-invariants>],
  )
]<th:benard-schacher>

As a first step in the proof, let us review some facts about the Brauer group
$B(K)$ of the algebraic number field $K$; for details, see @bib:Reiner1975[MO],
§§28, 32, for example. Let $A$ and $A'$ be f.d. central simple $K$-algebras; we
call them #idx("Similar algebras")_similar_, and write $A∼A'$, if there is an
isomorphism of $K$-algebras
$ M_n lr((K))times.o_K A ≅ M_(n') lr((K))times.o_K A' $
for some integers $n$, $n'$. The similarity classes $[A]$ of such algebras, with
multiplication defined via $times.o_K$, form an abelian group $B(K)$, the #idx(
  "Brauer group",
)_Brauer group_ of $K$. For each prime $P$ of $K$, the map
$ "inv"_P:B(K) arrow QQ slash ZZ, $
which maps each class $[A] in B(K)$ onto its Hasse invariant $"inv"_P A$, is a
well-defined homomorphism. The set of values ${"inv"_P A}$, as $P$ varies over
the primes of $K$ (including the infinite ones), uniquely determines the element
$[A] in B(K)$.

Now let $L$ be a finite Galois extension of $K$, with Galois group
$G=upright("Gal")(L slash K)$. We denote by $B(L slash K)$ the subgroup of
$B(K)$ consisting of all central simple $K$-algebras split by $L$. (Every
element of $B(K)$ lies in some $B(L slash K)$.) There is an isomorphism
$ H^2(G,L^dot) ≅ B(L slash K), $
<eq:brauer-crossed-product-cohomology>
defined thus: given any factor set $f:G times G arrow L^dot$, we may form the
#idx("Crossed product algebra")_crossed-product algebra_
$ (L slash K,f)=plus.o.big_(x in G) L u_x, $
<eq:crossed-product-algebra-decomposition>
whose structure is given by the formula
$
  u_x u_y=f(x,y)u_(x y), quad u_x a=(x a)u_x
  quad "for" a in L, quad x,y in G.
$
<eq:crossed-product-algebra-multiplication>

#source(764)
The isomorphism in @eq:brauer-crossed-product-cohomology maps the cohomology
class of $f$ onto the class of $(L slash K,f)$ in $B(L slash K)$.

We recall finally that if $A$ is a central simple $K$-algebra of index $m$, then
$m$ is also the order of $[A]$ as an element of $B(K)$; see @bib:Reiner1975[MO]
(32.19). We have already noted that
$ m="least common multiple of all" {m_P}, $
where $P$ ranges over all primes of $K$.

The simplified proof of the Benard-Schacher Theorem given below is based on the
work of Janusz~@bib:Janusz1972. The authors wish to thank G. Janusz for many
helpful conversations during the preparation of the material which follows. As
we shall see, the proof depends strongly on an extended form of the Brauer-Witt
Theorem, to be established in @th:brauer-witt and
@cor:schur-components-similar-cyclotomic below. This latter theorem enables us
to reduce the proof of the Benard-Schacher Theorem to the case of cyclotomic
algebras. These are a special kind of crossed-product algebra, defined as
follows. Let $L=K(omega)$ be a cyclotomic extension of the algebraic number
field $K$, where $omega$ is a root of $1$, and let
$G=upright("Gal")(L slash K)$. Then $G$ is abelian, a fact needed later. Let
$f:G times G arrow chevron.l omega chevron.r$ be a factor set with values in the
cyclic group $chevron.l omega chevron.r$. The crossed-product algebra
$(L slash K,f)$ is called a #idx("Cyclotomic algebra")_cyclotomic algebra_. As
we shall see in @cor:schur-components-similar-cyclotomic, every central simple
$K$-algebra $B$, which occurs as a component of a group algebra, must be similar
to some cyclotomic algebra $A$. It thus suffices to establish
@th:benard-schacher for $A$ rather than $B$, since similar $K$-algebras have the
same index and the same set of Hasse invariants.

Continuing with the proof of the Benard-Schacher Theorem, let $A=(L slash K,f)$
be a cyclotomic algebra of index $m$, where $L=K(omega)$ and
$G=upright("Gal")(L slash K)$ as above, and where
$f:G times G arrow chevron.l omega chevron.r$ is a factor set. The values of $f$
generate a cyclic subgroup $chevron.l zeta chevron.r$ of
$chevron.l omega chevron.r$, so now
$f:G times G arrow chevron.l zeta chevron.r$. Each
$sigma in upright("Aut")_QQ K$ lifts to an element
$overline(sigma) in upright("Aut")_QQ L$, though not in a unique manner. We
define a map
$
  overline(sigma)f:G times G arrow chevron.l zeta chevron.r
  quad "by" (overline(sigma)f)(x,y)=overline(sigma){f(x,y)}
  quad "for" x,y in G.
$
The condition, that $f$ be a factor set, is as follows:
$ (x f(y,z))f(x,y z)=f(x,y)f(x y,z) quad "for all" x,y,z in G. $
Since the actions of $overline(sigma)$ and $x$ on $chevron.l zeta chevron.r$
commute, it follows easily that $overline(sigma)f$ is also a factor set. If
$tilde(sigma) in upright("Aut")_QQ L$ is another lifting of $sigma$, we have
$ (L slash K,overline(sigma)f) ≅ (L slash K,tilde(sigma)f) $
by Exercise @exc:abelian-galois-factor-set-automorphism. Thus the class of
$(L slash K,overline(sigma)f)$ in $B(L slash K)$ depends only on $sigma$, and
will be denoted by $[sigma A]$. If $overline(sigma)(zeta)=zeta^r$, then
$overline(sigma)f=f^r$, and therefore (by @eq:brauer-crossed-product-cohomology)
$ [sigma A]=[A]^r quad "in" B(L slash K). $

#source(765)
Keeping the above notation, suppose that $zeta$ has order $n$. Then $f^n=1$, so
$[A]^n=1$ in $B(L slash K)$. Since $[A]$ has order $m$ in $B(L slash K)$, it
follows that $m$ divides $n$. Therefore $epsilon_m in chevron.l zeta chevron.r$,
and so $overline(sigma)(epsilon_m)=epsilon_m^r$. We now apply these arguments to
the case where $sigma=1$. In this situation $[sigma A]=[A]$, so we obtain
$[A]=[A]^r$. Therefore $r≡1$ $("mod" m)$ and
$overline(sigma)(epsilon_m)=epsilon_m$. This shows that every
$overline(sigma) in upright("Gal")(L slash K)$ fixes $epsilon_m$, so
$epsilon_m in K$, and we have proved the first part of the Benard-Schacher
Theorem.

For the second part, let $sigma in upright("Aut")_QQ K$ be arbitrary, and let
$P$ be any prime of $K$. The automorphism $sigma$ of $K$ maps $P$ onto a
conjugate prime $P^sigma$, and induces an isomorphism
$sigma:K_P arrow K_(P^sigma)$. We now construct an isomorphism
$
  psi:K_P times.o_K (L slash K,f) ≅ K_(P^sigma) times.o_K
  (L slash K,overline(sigma)f)
$
as follows. Let $(L slash K,f)$ be as in
@eq:crossed-product-algebra-decomposition, and correspondingly let
$
  (L slash K,overline(sigma)f)=plus.o.big_(x in G) L v_x,
  quad "where" v_x v_y=overline(sigma)f(x,y)v_(x y)
  quad "for" x,y in G.
$
Define $psi$ by the formula
$
  psi(a times.o b u_x)=sigma(a)times.o overline(sigma)(b)v_x
  quad "for" a in K_P, quad b in L, quad x in G.
$
It is easily verified that for $k in K$,
$ psi(a k times.o b u_x)=psi(a times.o k b u_x), $
so $psi$ is well defined. Clearly $psi$ is an isomorphism of simple algebras
over local fields, and so these algebras have the same Hasse invariant.
Therefore
$ "inv"_P A="inv"_(P^sigma) [sigma A]. $
But $[sigma A]=[A]^r$, where $sigma(epsilon_m)=epsilon_m^r$; since
$"inv"_(P^sigma):B(L slash K) arrow QQ slash ZZ$ is a homomorphism, we obtain
$ "inv"_(P^sigma) [sigma A]=r dot "inv"_(P^sigma) [A], $
as desired.

Finally, as remarked in §~@ss:group-algebra-schur-indices, the Hasse invariant
$"inv"_P A$ is a fraction in lowest terms, with denominator the local index
$m_P lr((A))$. Since $m_P$ divides the index $m$ of $A$, and the integer $r$ is
relatively prime to $m$, we see that @eq:schur-component-conjugate-local-indices
is a direct consequence of @eq:schur-component-conjugate-hasse-invariants. This
completes the proof of the Benard-Schacher Theorem.

#remark(numbered: false)[
  If $K$ is a finite extension of a $p$-adic field $QQ_p$, where $p$ is a
  rational prime, then part~@case:schur-component-roots-of-unity of the
  Benard-Schacher Theorem remains valid. This is clear from the preceding proof,
  and the proof of the Brauer-Witt Theorem below. Assertion
  @case:schur-component-conjugate-prime-invariants does not apply in this local
  case.
]<rem:local-schur-component-roots-of-unity>

#source(766)
We now give some immediate consequences of the above results to the theory of
the Schur index $m_K lr((zeta))$ for $zeta in upright("Irr") G$, where $G$ is
any finite group. The first corollary is merely a restatement of the
Benard-Schacher Theorem for our case.

#theorem[
  Let $zeta$ be an irreducible complex character of a finite group $G$, and let
  $K=QQ(zeta)$. Let#footnote[In general,
    $m_QQ lr((zeta))=m_(QQ(zeta)) lr((zeta))$ by
    @eq:schur-index-character-field-invariance.]
  $ m=m_QQ lr((zeta))=m_K lr((zeta)) $
  be the Schur index of $zeta$. Then
  #case-list(
    numbering: "(i)",
    [#case[$K$ contains all $m$-th roots of $1$.]
      <case:character-field-schur-index-roots-of-unity>],
    [#case[
      Let $P$ and $P'$ be primes of $K$ lying over the same prime $p$ of $QQ$,
      where $p$ is either a rational prime number or $p=infinity$. Then
      $ m_(K_P) lr((zeta))=m_(K_(P')) lr((zeta)), $
      that is, $zeta$ has the same Schur indices over the complete fields $K_P$
      and $K_(P')$.
    ]<case:character-field-uniform-local-schur-indices>],
  )
]<th:character-field-schur-index-roots-local-uniformity>

It follows from part~@case:character-field-uniform-local-schur-indices that for
each $zeta in upright("Irr") G$ and each $p$ the Schur index of
$m_(QQ_p) lr((zeta))$ is well defined (as the common value of all
$m_(K_P) lr((zeta))$, where $P$ extends $p$), and is independent of the
embedding of $QQ(zeta)$ into the algebraic closure of $QQ_p$.

Next, we have:

#theorem(name: "Brauer-Speiser Theorem")[
  #idx("Brauer-Speiser Theorem")
  Let $zeta in upright("Irr") G$ be real-valued. Then $m_QQ lr((zeta))=1$ or
  $2$, and $m_QQ lr((zeta))=1$ if $zeta(1)$ is odd.
]<th:brauer-speiser-schur-index>

#proof[
  #footnote[The Benard-Schacher Theorem is not required for the proof of
    @th:brauer-speiser-schur-index. As an exercise, the reader can give a proof
    using @th:real-complex-simple-module-types and
    @case:schur-index-minimal-realizable-multiple[#context {
      reference-number-text(
        "("
          + reference-data(
            <cor:schur-index-multiplicities-realizable-multiple>,
          ).text
          + reference-data(<case:schur-index-minimal-realizable-multiple>)
            .text
            .trim(regex("[()]"))
          + ")",
      )
    }].]
  The only roots of $1$ in $QQ(zeta)$ are $±1$, so $m_QQ lr((zeta))=1$ or $2$.
  Further, $m_QQ lr((zeta))$ divides $zeta(1)$ by
  @case:schur-index-minimal-realizable-multiple[#context {
    reference-number-text(
      "("
        + reference-data(
          <cor:schur-index-multiplicities-realizable-multiple>,
        ).text
        + reference-data(<case:schur-index-minimal-realizable-multiple>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }].
]

We now take up the proof of the Brauer-Witt Theorem, and its corollary that
simple components of group algebras are similar to cyclotomic algebras. For the
rest of our discussion, $K$ may be any field of characteristic $0$. As usual
$upright("Irr") G$ denotes the set of irreducible complex characters of a finite
group $G$. A character of $G$ afforded by a $K G$-module is called a
_$K$-character_ of $G$. On the other hand, a character $eta$ of $G$, such that
$K(eta)=K$, is said to _lie in_ $K$.

By @th:schur-index-character-realization, for each $zeta in upright("Irr") G$
there is a unique simple component $A(K,zeta)$ of $K G$, affording a
$K$-character $eta$ of $G$, such that
$ eta=m(zeta_1+dots+zeta_t), quad "where" t=dim_K K(zeta), $
and $m=m_K lr((zeta))$. The ${zeta_i}$ are the distinct algebraic conjugates of
$zeta$ under the action of $upright("Gal")(K(zeta) slash K)$, and are called the
_Galois conjugates_ of $zeta$ over $K$. We have seen
#source(767)
that $A(K,zeta)$ has center $K(zeta)$, and that
$ K(zeta)times.o_K A(K,zeta)=plus.o.big_i A(K,zeta_i). $
In particular, for each $zeta in upright("Irr") G$,
$
  A(K(zeta),zeta) ≅ A(K,zeta),
  quad m_(K(zeta)) lr((zeta))=m_K lr((zeta)).
$
<eq:character-field-component-index-invariance>
In proving that each $A(K,zeta)$ is similar to a cyclotomic algebra, there is
thus no loss of generality in assuming that $K(zeta)=K$.

We shall follow the treatment of Yamada~@bib:Yamada1974, with minor variations.
Let us first recall the Witt-Berman Induction Theorem
@i:th:witt-berman-induction. Let $epsilon_n$ be a primitive $n$-th root of $1$,
where $G$ has exponent $n$, and let $p$ be prime. A subgroup $H≤G$ is called
#idx(
  "(K,p)-elementary subgroup",
)_$(K,p)$-elementary_ if $H=chevron.l a chevron.r ⋊ P$, where
$chevron.l a chevron.r$ is a cyclic $p'$-group and $P$ is a $p$-group. Put
$d=|a|$, and let $epsilon_d$ be a primitive $d$-th root of $1$. For each
$h in H$, there must exist an integer $i$ and
$sigma in op("Gal")(K(epsilon_d) slash K)$ such that
$ h a h^(-1)=a^i, quad sigma(epsilon_d)=epsilon_d^i. $
Thus the conjugation action on $chevron.l a chevron.r$ is contained in the
Galois action over $K$. (See §~@i:sec:induction-arbitrary-fields.)

Examining the proof of @i:th:witt-berman-induction, we find readily that the
following stronger version is valid:

#theorem(name: "Witt-Berman Induction Theorem")[
  #idx("Witt-Berman Theorem")
  Let $p$ be prime. There exists an integer $r$ prime to $p$ such that, denoting
  by $1_G$ the $1$-character of $G$, $r dot 1_G$ is a $ZZ$-linear combination of
  induced characters $mu_i^G$, where for each $i$, $mu_i$ is a $K$-character of
  some $(K,p)$-elementary subgroup of $G$.
]<th:witt-berman-prime-to-p-multiple-induction>

We begin with an easy corollary, which slightly improves
@bib:CurtisReiner1962[CR] (70.25). As usual, let $(zeta,eta)$ or $(zeta,eta)_G$
denote inner products of characters, defined as in
@i:eq:character-hermitian-scalar-product.

#lemma[
  Let $p$ be prime, let $zeta in upright("Irr") G$, and let $F$ be a field such
  that
  $
    K(zeta) subset.eq F subset K(epsilon_n),
    quad dim_F K(epsilon_n)="power of" p.
  $
  Then there exist an $(F,p)$-elementary subgroup $H$ of $G$ and a character
  $xi in upright("Irr") H$ such that
  $ p divides.not (zeta_H,xi) quad "and" F(xi)=F. $
]<lem:elementary-subgroup-prime-to-p-character-multiplicity>

#proof[
  Choose $r$ prime to $p$ as in @th:witt-berman-prime-to-p-multiple-induction.
  We may then write $r dot 1_G=sum a_i mu_i^G$, with $mu_i$ an $F$-character of
  an $(F,p)$-elementary subgroup $H_i$ of $G$. Then
  $ r zeta=sum a_i zeta mu_i^G=sum a_i (mu_i dot zeta_(H_i))^G. $
  For $H≤G$ and $xi in upright("Irr") H$, let $upright("Tr")_F lr((xi))$ be the
  sum of the Galois conjugates of $xi$
  #source(768)
  over $F$. Each character $mu$ of $H$ lying in $F$ is then a $ZZ$-linear
  combination of such traces $upright("Tr")_F lr((xi))$, with
  $xi in upright("Irr") H$. We may apply this to each character
  $mu_i dot zeta_(H_i)$ above, which lies in $F$ since both $mu_i$ and $zeta$
  lie in $F$. Therefore we may write
  $
    r zeta=sum b_i (upright("Tr")_F xi_i)^G,
    quad b_i in ZZ, quad xi_i in upright("Irr") H_i.
  $
  Consequently we obtain
  $
    r=(zeta,sum b_i (upright("Tr")_F xi_i)^G)
    =sum b_i (zeta_(H_i),upright("Tr")_F xi_i)_(H_i).
  $
  But $(zeta_(H_i),xi_i)=(zeta_(H_i),xi'_i)$ for each $F$-conjugate $xi'_i$ of
  $xi_i$, since $zeta_(H_i)$ lies in $F$. If $d_i=dim_F F(xi_i)$, there are
  $d_i$ such ${xi'_i}$, and so
  $ r=sum b_i d_i (zeta_(H_i),xi_i)_(H_i). $
  Since $p divides.not r$, there is a subscript $j$ for which
  $p divides.not d_j lr((zeta_(H_j),xi_j))$. Therefore $d_j=1$, since $d_j$
  divides $dim_F K(epsilon_n)$. Thus we obtain $F(xi_j)=F$ and
  $p divides.not (zeta_(H_j),xi_j)$, which proves the lemma.
]

As our next step, let us show how cyclotomic algebras arise from group
representations. By definition, a _cyclotomic algebra_ is a crossed-product
algebra $(L slash K,f)$, where $L=K(omega)$ with $omega$ a root of $1$, and $f$
is a factor set on $upright("Gal")(L slash K)$ whose values are roots of $1$ in
$L$. We may assume that the values of $f$ lie in $chevron.l omega chevron.r$,
since we can always replace $omega$ by $omega'$, where
$chevron.l omega' chevron.r=chevron.l omega,"im" f chevron.r$.

#proposition[
  Let $zeta in upright("Irr") G$, and let $K(zeta)=K$. Suppose that $zeta=psi^G$
  for some linear character $psi$ of $N$, where $N ⊴ G$, and put
  $frak(G)=upright("Gal")(K(psi) slash K)$. Define
  $
    G_0={x in G:attach(psi, tl: x)=tau(x)psi
      "for some" tau(x) in frak(G)},
  $
  <eq:monomial-character-galois-stabilizer>
  and set $psi_0=psi^(G_0)$. Then $psi_0 in upright("Irr") G_0$, $K(psi_0)=K$,
  and the simple component $A(K,psi_0)$ of $K G_0$, which corresponds to
  $psi_0$, is a cyclotomic algebra $(K(psi) slash K,f)$ for some factor set $f$.
]<prop:monomial-character-cyclotomic-component>

#proof[
  #case-list(
    prefix: "Step ",
    numbering: "1.",
    [#case[
      Suppose first that $psi in upright("Irr") N$, but $psi$ need not be
      linear. For $x in G$, the $G$-conjugate $attach(psi, tl: x)$ of $psi$ also
      lies in $upright("Irr") N$ (see §~@i:ss:mackey-theorems), and we have for
      $n in N$, $x,y in G$:
      $
        (attach(psi, tl: x))n=psi(n^x),
        quad "and" attach(psi, tl: x y)=attach((attach(psi, tl: y)), tl: x).
      $
      Next, for each $tau in frak(G)$, $tau psi$ is the Galois conjugate of
      $psi$ over $K$ defined by $(tau psi)n=tau(psi(n))$, $n in N$. By Exercise
      @i:exc:galois-conjugate-characters, $tau psi in upright("Irr") N$.

      Let us set $G=union.big_(i=1)^d N x_i$. Since $zeta=psi^G$ is irreducible,
      it follows from @i:th:induced-character-irreducibility that the
      $G$-conjugates ${attach(psi, tl: x_i)}$ are distinct. Further, since
      $N ⊴ G$,
      $ zeta=psi^G=sum_(i=1)^d attach(psi^∘, tl: x_i), $
      #source(769)
      where $psi^∘=psi$ on $N$ and $psi^∘=0$ on $G-N$ (see
      @i:eq:induced-character-cosets). In particular,
      $ zeta_N=sum_i attach(psi, tl: x_i). $
      Note also that $frak(G)$ is abelian.

      Define $G_0$ by @eq:monomial-character-galois-stabilizer; each $x in G_0$
      determines a unique $tau(x) in frak(G)$, and the map $x arrow tau(x)$
      gives a homomorphism from $G_0$ into $frak(G)$, with kernel $N$. Now write
      $
        G_0=union.big_(i=1)^t N x_i, quad t=|G_0:N|,
        quad "and set" tau_i=tau(x_i) in frak(G).
      $
      Then we have
      $ G_0 slash N={tau_1,dots,tau_t}≤frak(G). $
      Setting $psi_0=psi^(G_0)$, we shall now prove
      $
        psi_0 in upright("Irr") G_0, quad K(psi_0)=K,
        quad "and" {tau_1,dots,tau_t}=frak(G).
      $
      <eq:monomial-character-galois-stabilizer-properties>
      First of all, from $zeta=psi_0^G$ we conclude that
      $psi_0 in upright("Irr") G_0$. Next,
      $ psi_0=sum_(i=1)^t attach(psi^∘, tl: x_i)=sum_i tau_i psi^∘. $
      Therefore $tau_j psi_0=psi_0$ for each $j$, and therefore
      $tau_j in upright("Gal")(K(psi) slash K(psi_0))$. Conversely, if
      $sigma in upright("Gal")(K(psi) slash K(psi_0))$, then
      $sigma psi_0=psi_0$, so $sigma psi=tau_i psi$ for some $i$, and then
      $sigma=tau_i$. We have thus shown that
      $ {tau_1,dots,tau_t}=upright("Gal")(K(psi) slash K(psi_0)). $
      On the other hand, for $sigma in frak(G)$ we have $sigma zeta=zeta$, so
      $sigma$ permutes the $G$-conjugates ${attach(psi, tl: x_i):1≤i≤d}$, where
      $d=|G:N|$. In particular, $sigma psi=attach(psi, tl: x_i)$ for some $i$,
      and then $x_i in G_0$, by the definition of $G_0$. Therefore
      $sigma=tau_i$, so we have proved that
      $ upright("Gal")(K(psi) slash K(psi_0))=upright("Gal")(K(psi) slash K). $
      Thus $K(psi_0)=K$, and @eq:monomial-character-galois-stabilizer-properties
      is established.
    ]<case:monomial-character-galois-stabilizer-proof>],
    [#case[
      Keeping the above notation, suppose hereafter that $psi$ is linear. Put
      $L=K(psi)$ and $rho_i=tau_i^(-1)$, for $1≤i≤t$. Write
      $
        x_i x_j=n_(i j)x_(pi(i, j)), quad n_(i j) in N,
        quad f(rho_i,rho_j)=psi(n_(i j)).
      $
      #source(770)
      Conjugation by $x_i$ acts on the values of $psi$ as $rho_i$. Associativity
      of the products $x_i x_j x_k$ therefore gives
      $
        f(rho_i,rho_j)f(rho_i rho_j,rho_k)
        =rho_i lr((f(rho_j,rho_k)))f(rho_i,rho_j rho_k).
      $
      Thus $f$ is a factor set, with values roots of $1$ in $L$. Form the
      cyclotomic algebra
      $
        C=(L slash K,f)=plus.o.big_(i=1)^t L u_i,
        quad u_i a=rho_i lr((a))u_i,
        quad u_i u_j=f(rho_i,rho_j)u_(pi(i, j)).
      $
      The assignments $n arrow psi(n)$ for $n in N$ and $x_i arrow u_i$ respect
      the conjugation and product relations, and hence define a surjective
      $K$-algebra homomorphism $K G_0 arrow C$, since the values of $psi$ span
      $L$ over $K$.

      View $L$ as a left $K N$-module by multiplication by $psi(n)$. Its
      $K$-character is $op("Tr")_(L slash K) psi$, not merely $psi$. The map
      $
        V=K G_0 times.o_(K N) L arrow C,
        quad x_i times.o a arrow u_i a,
      $
      is an isomorphism of left $K G_0$-modules: the ${x_i}$ and ${u_i}$ are
      right $K N$- and right $L$-bases, respectively, and the action on $C$ is
      through the displayed homomorphism. Since every Galois conjugate of $psi$
      is a $G_0$-conjugate, $V$ has character
      $
        (op("Tr")_(L slash K) psi)^(G_0)=t psi_0,
        quad dim_K V=t^2.
      $
      The irreducible character $psi_0$ is $K$-valued by
      Step~@case:monomial-character-galois-stabilizer-proof. Therefore only the
      simple component $A(K,psi_0)$ of $K G_0$ acts nontrivially on $V$. The
      left regular action of $C$ is faithful, so the preceding surjection
      identifies $A(K,psi_0)$ with $C$. This proves the proposition.#ed-note[
        The original crossed-product action must be inverted, and the
        $K$-character of $L$ is a trace of $psi$, rather than $psi$ itself. The
        corrected construction above gives the required component.
      ]
    ]<case:monomial-character-cyclotomic-algebra-construction>],
  )
]

We shall apply the preceding proposition to a $(K,p)$-elementary group $G$ and a
character $zeta in upright("Irr") G$ lying in $K$. Our object is to show that
$zeta=psi^G$ for some linear character $psi$ of a subgroup $N$ of $G$, such that
$psi^H$ lies in $K$ for a suitable $H$ containing $N$. Specifically, we show:

#proposition[
  Let $G=chevron.l a chevron.r ⋊ P$ be a $(K,p)$-elementary group, where
  $chevron.l a chevron.r$ is a cyclic $p'$-group and $P$ is a $p$-group. Let
  $zeta in upright("Irr") G$ lie in $K$. Then there exist groups $N≤H≤G$, and a
  linear character $psi$ of $N$, such that
  #case-list(
    numbering: "(i)",
    [#case[$zeta=psi^G$, and $chevron.l a chevron.r≤N ⊴ H$.]
      <case:elementary-character-normal-linear-induction>],
    [#case[Each $H$-conjugate of $psi$ is a Galois conjugate of $psi$ over
      $K$.]<case:elementary-character-galois-conjugates>],
    [#case[$K(psi^H)=K$.]<case:elementary-character-intermediate-field>],
  )
]<prop:elementary-character-cyclotomic-induction>

#proof[
  We use induction on $|G|$. Let $T$ be a minimal normal subgroup of $G$ such
  that
  $
    cases(
      zeta=theta^G "for some" theta in upright("Irr") T ","
      "where every" G"-conjugate of" theta,
      "is a Galois conjugate of" theta "over" K.
    )
  $
  Since $G$ itself satisfies the above condition, the existence of $T$ is
  obvious.
  #source(771)
  If $theta(1)=1$, we need only choose $N=T$, $H=G$, and $psi=theta$. For the
  rest of the proof, assume $theta(1)>1$. By Exercise
  @exc:elementary-group-character-properties, $theta$ is induced from a linear
  character of some proper subgroup of $T$. Therefore $theta=rho^T$ for some
  $rho in upright("Irr") S$ and some $S<T$ of index $p$. Since
  $zeta=theta^G=rho^G$, Exercise @exc:elementary-group-character-properties
  shows that $chevron.l a chevron.r≤S$, and then necessarily $S ⊴ T$. We shall
  use this information to construct a subgroup $E<G$ and a character
  $lambda in upright("Irr") E$, such that $zeta=lambda^G$ and $K(lambda)=K$. The
  desired result will then follow by applying the induction hypothesis to $E$
  and $lambda$.

  Given $S ⊴ T$ of index $p$, and $theta=rho^T in upright("Irr") T$, as above,
  we note first that $theta=0$ on $T-S$. We wish to replace $S$ by a subgroup
  $T_0<T$, also of index $p$, such that $T_0 ⊴ G$. For this purpose, define
  $ X=inter.big_(x in G) attach(S, tl: x) ⊴ G, quad "so" X<T. $
  Then $chevron.l a chevron.r≤X$, and thus $G slash X$ is a $p$-group. We may
  then choose $T_0 ⊴ G$ such that
  $ X≤T_0<T ⊴ G, quad |T:T_0|=p. $
  Now $theta=0$ on $T-S$, and every $G$-conjugate of $theta$ is a Galois
  conjugate of $theta$, so $theta=0$ on $T-X$, and thus also on $T-T_0$. This
  gives
  $
    (theta_(T_0),theta_(T_0))
    =|T_0|^(-1) sum_(t in T_0) theta(t)overline(theta(t))
    =|T_0|^(-1) sum_(t in T) theta(t)overline(theta(t))=p.
  $
  By §~@i:ss:clifford-character-theory, we deduce that $theta_(T_0)$ is a sum of
  $p$ distinct $T$-conjugates of some $phi in upright("Irr") T_0$, and that
  $theta=phi^T$. Therefore $zeta=phi^G$.

  From the minimality of $T$, it follows that $upright("Gal")(K(phi) slash K)$
  does not act transitively on the $G$-conjugates of $phi$. Setting
  $
    E={x in G:attach(phi, tl: x)=tau(x)phi
      "for some" tau(x) in upright("Gal")(K(phi) slash K)},
  $
  it follows that $chevron.l a chevron.r≤T_0≤E<G$, and $T_0 ⊴ G$. By
  Step~@case:monomial-character-galois-stabilizer-proof of the proof of
  @prop:monomial-character-cyclotomic-component, we obtain $zeta=(phi^E)^G$ and
  $K(phi^E)=K$. The existence of the desired groups $N$ and $H$, and of the
  linear character $psi$ of $N$, now follows by applying the induction
  hypothesis to the group $E$ and its irreducible character $phi^E$.
]

Continuing with the preliminary steps required for the Brauer-Witt Theorem, we
now review some additional properties of the Brauer group $B(K)$. Let
$[A] in B(K)$ have index $m$ and order $e$. If $K$ is an algebraic number field,
or more generally any global field, then $m=e$ (see @bib:Reiner1975[MO]
(32.19)). In the case of arbitrary $K$, we can only assert that
$
  e divides m, quad "and" e,m
  "have the same prime factors (apart from multiplicity)"
$
(see @bib:Reiner1975[MO] (29.22), (29.24)). This will suffice for our discussion
below.

For a prime $p$, let $B(K)_p$ be the $p$-torsion subgroup of $B(K)$. Each
$x in B(K)$ is uniquely expressible as a product of $p$-torsion elements for
various primes $p$.
#source(772)
More precisely, let $D$ be a skewfield with center $K$ and index $m$, and write
$m=product_(i=1)^t p_i^(e_i)$, where the ${p_i}$ are distinct primes and each
$e_i≥1$. By @bib:Reiner1975[MO], Exercise 29.7, there exist skewfields
${D_1,dots,D_t}$ where $D_i$ has center $K$ and index $p_i^(e_i)$, such that
$ D ≅ D_1 times.o_K dots times.o_K D_t. $
Thus in $B(K)$ we have
$ [D]=[D_1] dots [D_t]; $
we call $[D_i]$ the _$p_i$-part_ of $[D]$, and write $[D_i]=[D]_(p_i)$. For
$p divides.not m$, put $[D]_p=1$. Using these ideas, we shall prove:

#proposition[
  Given $H≤G$, $xi in upright("Irr") H$, $zeta in upright("Irr") G$, where
  $(zeta_H,xi)>0$, let $K$ be a field with $K(zeta)=K(xi)=K$. Let $A(K,xi)$ and
  $A(K,zeta)$ be the simple components of $K H$ and $K G$, respectively,
  corresponding to $xi$ and $zeta$. Then $A(K,xi)$ and $A(K,zeta)$ are central
  simple $K$-algebras, and
  $ [A(K,xi)]_p=[A(K,zeta)]_p quad "in" B(K) $
  for each prime $p$ not dividing $(zeta_H,xi)$.
]<prop:prime-to-p-multiplicity-brauer-components>

#proof[
  Let $r=(zeta_H,xi)$, and let $p$ be a prime such that $p divides.not r$. Let
  $epsilon$ be a primitive $n$-th root of $1$, where $G$ has exponent $n$. There
  is a unique field $F$ such that
  $
    K subset F subset K(epsilon), quad p divides.not dim_K F,
    quad dim_F K(epsilon)="power of" p.
  $
  <eq:cyclotomic-prime-to-p-intermediate-field>
  By @th:schur-index-character-realization, $A(K,xi)$ and $A(K,zeta)$ are simple
  algebras with center $K$, while $A(F,xi)$ and $A(F,zeta)$ are simple algebras
  with center $F$. Further,
  $
    F times.o_K A(K,xi)=A(F,xi), quad
    F times.o_K A(K,zeta)=A(F,zeta).
  $
  We note next that $K(epsilon)$ is a splitting field for both of the central
  simple $F$-algebras $A(F,xi)$ and $A(F,zeta)$, so by Exercise
  @exc:division-algebra-index-scalar-extension their indices must divide
  $dim_F K(epsilon)$, and are therefore powers of $p$. Since the homomorphism
  $B(K)_p arrow B(F)_p$, defined by $F times.o_K *$, is injective (see Exercise
  @exc:brauer-p-torsion-prime-to-p-extension), the proposition will follow once
  we prove that
  $ [A(F,xi)]=[A(F,zeta)] quad "in" B(F). $
  Before proving this, we note for later use that, by the preceding discussion,
  $
    p"-part of" m_K lr((zeta))=m_F lr((zeta)),
    quad p"-part of" m_K lr((xi))=m_F lr((xi)).
  $
  <eq:prime-to-p-extension-schur-index-primary-part>
  In order to show that $[A(F,xi)]=[A(F,zeta)]$ in $B(F)$, we need some easy
  facts
  #source(773)
  about tensor products of simple components of group algebras. Given groups
  $G_1$, $G_2$ and characters $zeta_i in upright("Irr") G_i$, $i=1,2$, let $F$
  be a field of characteristic $0$ such that both $zeta_1$ and $zeta_2$ lie in
  $F$. Then $zeta_1 times.o zeta_2$ is an irreducible character of the direct
  product $G_1 times G_2$. Since $F G_1 times.o_F F G_2 ≅ F(G_1 times G_2)$, we
  deduce that
  $ A(F,zeta_1)times.o_F A(F,zeta_2) ≅ A(F,zeta_1 times.o zeta_2). $
  Now let $overline(zeta)$ denote the complex conjugate of $zeta$. Using
  contragredient modules, we find readily that $A(F,overline(zeta))$ is
  antiisomorphic to $A(F,zeta)$. From @i:th:tensor-simple-algebras we obtain
  $ A(F,zeta)times.o_F A(F,overline(zeta)) ≅ M_l lr((F)) $
  for some $l$. The left-hand side is just $A(F,zeta times.o overline(zeta))$,
  where now $zeta times.o overline(zeta) in upright("Irr")(G times G)$. It
  follows that the character $zeta times.o overline(zeta)$ of $G times G$ is
  realizable in the field $F$, whence so is the character
  $zeta_H times.o overline(zeta)$ of $H times G$. On the other hand,
  $xi times.o overline(zeta) in upright("Irr")(H times G)$ has character values
  in $F$. Then @th:schur-index-character-realization shows that
  $
    m_F lr((xi times.o overline(zeta))) "divides"
    (xi times.o overline(zeta),zeta_H times.o overline(zeta)).
  $
  However,
  $
    (xi times.o overline(zeta),zeta_H times.o overline(zeta))
    =(xi,zeta_H)(zeta,zeta)_G=r,
  $
  so $m_F lr((xi times.o overline(zeta)))$ is prime to $p$. However,
  $ A(F,xi times.o overline(zeta)) ≅ A(F,xi)times.o_F A(F,overline(zeta)), $
  and each of the factors $A(F,xi)$ and $A(F,overline(zeta))$ has $p$-power
  index, whence so does $A(F,xi times.o overline(zeta))$. This shows that
  $m_F lr((xi times.o overline(zeta)))=1$, and so
  $[A(F,xi times.o overline(zeta))]=1$ in $B(F)$. Therefore
  $ [A(F,xi)]=[A(F,overline(zeta))]^(-1)=[A(F,zeta)] quad "in" B(F), $
  which completes the proof.
]

We are finally ready to state and prove an extended version of the Brauer-Witt
Theorem, which involves not only the calculation of Schur indices of irreducible
characters, but also gives information on the structure of simple components of
group algebras. We continue to follow the approach of Yamada~@bib:Yamada1974.

#theorem(name: "Brauer-Witt Theorem")[
  #idx("Brauer-Witt Theorem")
  Let $zeta in upright("Irr") G$, and let $K$ be an algebraic number field such
  that $K(zeta)=K$. Let $p$ be a prime, and let $F$ be the subfield of
  $K(epsilon)$ defined in @eq:cyclotomic-prime-to-p-intermediate-field. Then
  there exist an $(F,p)$-elementary subgroup $H≤G$, a character
  $xi in upright("Irr") H$, a group $N ⊴ H$, and a linear character $psi$ of
  $N$, such that
  #case-list(
    numbering: "(i)",
    [#case[$p divides.not (zeta_H,xi)$, and $F(xi)=F$.]
      <case:brauer-witt-prime-to-p-multiplicity>],
    [#source(774)
      #case[
        $xi=psi^H$, and each $H$-conjugate of $psi$ is a Galois conjugate of
        $psi$ over $F$.
      ]<case:brauer-witt-linear-induction>],
    [#case[
      The simple component $A(F,xi)$ of $F H$, corresponding to $xi$, is
      $F$-isomorphic to a cyclotomic algebra $(F(psi) slash F,f)$, where $f$ is
      a factor set whose values are roots of $1$ in $F(psi)$.
    ]<case:brauer-witt-cyclotomic-component>],
    [#case[
      In the Brauer group $B(F)$, we have
      $ [A(F,zeta)]=[A(F,xi)]=[(F(psi) slash F,f)]. $
    ]<case:brauer-witt-brauer-class>],
    [#case[The $p$-part of $m_K lr((zeta))$ equals $m_F lr((xi))$.]
      <case:brauer-witt-primary-schur-index>],
  )
]<th:brauer-witt>

#proof[
  By @lem:elementary-subgroup-prime-to-p-character-multiplicity, there exist an
  $(F,p)$-elementary subgroup $tilde(H)≤G$ and a character
  $tilde(xi) in upright("Irr") tilde(H)$, such that
  $ p divides.not (zeta,tilde(xi)^G) quad "and" F(tilde(xi))=F. $
  We now apply @prop:elementary-character-cyclotomic-induction with $G$, $K$,
  and $zeta$ replaced by $tilde(H)$, $F$, and $tilde(xi)$, respectively. Then
  there exist groups $N≤H≤tilde(H)≤G$, and a linear character $psi$ of $N$, such
  that
  $
    cases(
      tilde(xi)=psi^(tilde(H)) "," quad N ⊴ H "," quad F(psi^H)=F,
      "and each" H"-conjugate of" psi
      "is a Galois conjugate of" psi "over" F.
    )
  $
  Put $xi=psi^H$, so $xi^G=tilde(xi)^G$, and
  $(zeta_H,xi)=(zeta,xi^G)=(zeta,tilde(xi)^G)$. Thus, assertions
  @case:brauer-witt-prime-to-p-multiplicity and
  @case:brauer-witt-linear-induction are valid for this choice of $xi$, $N$,
  $H$, and $psi$.

  Now let us use @prop:monomial-character-cyclotomic-component, with $G$, $K$,
  $zeta$, and $G_0$ replaced by $H$, $F$, $xi$, and $H$, respectively. It
  follows from @prop:monomial-character-cyclotomic-component that $A(F,xi)$ is
  $F$-isomorphic to a cyclotomic algebra $(F(psi) slash F,f)$, constructed
  explicitly in Step~@case:monomial-character-cyclotomic-algebra-construction of
  the proof of @prop:monomial-character-cyclotomic-component. Further, since
  $p divides.not (zeta_H,xi)$, the proof of
  @prop:prime-to-p-multiplicity-brauer-components shows that
  $[A(F,xi)]=[A(F,zeta)]$ in $B(F)$. This proves
  part~@case:brauer-witt-brauer-class, and
  part~@case:brauer-witt-primary-schur-index then follows from
  @eq:prime-to-p-extension-schur-index-primary-part.
]

#corollary[
  Let $K$ be a field of characteristic $0$. Then every simple component
  $A(K,zeta)$ of a group algebra is similar to a cyclotomic algebra.
]<cor:schur-components-similar-cyclotomic>

#proof[
  By @eq:character-field-component-index-invariance, it suffices to treat the
  case where $zeta in upright("Irr") G$ is such that $K(zeta)=K$, and we assume
  this holds from now on. First suppose that $K$ is an algebraic number field.
  Let $A=A(K,zeta)$, so $[A] in B(K)$. We shall show that for each prime $p$,
  there exists a cyclotomic algebra $B^(p)$ with center $K$, such that
  $[A]_p=[B^(p)]$ in $B(K)$. (Note that $[A]_p=1$ for all but a finite number of
  primes $p_1,dots,p_l$, say.) Then
  $ [A]=product_(i=1)^l [A]_(p_i)=product_(i=1)^l [B^(p_i)], $
  so $A$ is similar to a tensor product of cyclotomic algebras:
  $ A∼B^(p_1) times.o_K dots times.o_K B^(p_l). $
  #source(775)
  Any such tensor product is similar to a cyclotomic algebra (see Exercise
  @exc:cyclotomic-algebra-tensor-product), so also $A$ is similar to a
  cyclotomic algebra, as desired.

  Now let $p$ be any prime, and let $F$ be the field defined in @th:brauer-witt,
  so $d=dim_K F$ is prime to $p$. As shown in any standard
  reference#footnote[See Cassels–Fröhlich~@bib:Cassels1967,
    Huppert~@bib:Huppert1967, or Weiss~@bib:Weiss1969.] on cohomology of groups,
  there exist homomorphisms
  $ "res":B(K) arrow B(F), quad "cor":B(F) arrow B(K), $
  called #idx("Restriction map")_restriction_ and #idx(
    "Corestriction",
  )_corestriction_ (or #idx("Transfer")_transfer_), respectively. The composite
  $"cor" circle "res"$ is multiplication by $d$. In terms of factor sets and the
  isomorphism @eq:brauer-crossed-product-cohomology, we note that given
  $x in B(K)$ and $y in B(F)$, we can find a finite Galois extension $L slash K$
  such that $x in B(L slash K)$, $y in B(L slash F)$. Put
  $ frak(H)=upright("Gal")(L slash F)≤frak(G)=upright("Gal")(L slash K). $
  The inclusion $frak(H)≤frak(G)$ induces a restriction homomorphism
  $"res":H^2(frak(G),L^dot) arrow H^2(frak(H),L^dot)$, and there is a
  commutative diagram
  #include "diagrams/74-brauer-restriction.typ"
  The vertical arrows are the isomorphisms in
  @eq:brauer-crossed-product-cohomology, and we have
  $ "res" [A]_p=[B] quad "in" B(F), $
  where $B$ is the cyclotomic algebra $(F(psi) slash F,f)$ defined in
  @th:brauer-witt.

  On the other hand, the corestriction map on Brauer groups comes from the map
  $"cor":H^2(frak(H),L^dot) arrow H^2(frak(G),L^dot)$, which is described
  explicitly by Huppert~@bib:Huppert1967, p. 114, or Weiss~@bib:Weiss1969,
  p. 81. In particular, if $f:frak(H)times frak(H) arrow L^dot$ is a factor set,
  the $"cor" [f]$ is represented by a factor set
  $g:frak(G)times frak(G) arrow L^dot$, whose values are products of values of
  $f$. Consequently, corestrictions of cyclotomic algebras are cyclotomic (up to
  similarity).

  We apply all this to $x=[A]_p in B(K)$, so
  $ x^d="cor" circle "res"(x)="cor" [B] quad "in" B(K), $
  and $"cor" [B]$ is (up to similarity) cyclotomic. Since $x$ is $p$-torsion and
  $p divides.not d$, we conclude that
  $ x=("cor" [B])^r quad "in" B(K) $
  for some $r$. Hence (by Exercise @exc:cyclotomic-algebra-tensor-product), $x$
  is a cyclotomic algebra (up to similarity).
  #source(776)
  This shows that for each $p$, $[A]_p=[B^(p)]$ in $B(K)$ for some cyclotomic
  algebra $B^(p)$ over $K$. By the first paragraph of the proof, we conclude
  that $A$ is similar to a cyclotomic algebra over $K$ in the number-field case.

  Now let $K$ be any field of characteristic $0$ with $K(zeta)=K$, and put
  $K_0=QQ(zeta) subset.eq K$. The number-field case supplies a cyclotomic
  representative $C_0=(L_0 slash K_0,f)$ of the class of $A(K_0,zeta)$, where
  $L_0=K_0(omega)$ and $f$ has root-of-unity values. Scalar extension carries
  this class to that of $A(K,zeta)$.

  The étale $K$-algebra $K times.o_(K_0) L_0$ is a product of fields. Choose a
  primitive idempotent $e$ and identify its field factor with $L=K(omega)$. Its
  stabilizer in $op("Gal")(L_0 slash K_0)$ is $H=op("Gal")(L slash K)$, by
  restriction. In the base-changed crossed product, the conjugate idempotents of
  $e$ sum to $1$, and
  $
    e(K times.o_(K_0) C_0)e ≅ (L slash K,f|_(H times H)).
  $
  Indeed, precisely the crossed-product basis elements indexed by $H$ survive in
  this corner; their multiplication has the restricted cocycle, whose values are
  still roots of $1$. The idempotent $e$ is full, since all its conjugates sum
  to $1$, so this corner is similar to $K times.o_(K_0) C_0$. It is therefore a
  cyclotomic representative of the class of $A(K,zeta)$. This proves the
  corollary without any embedding of $K$ in $CC$.#ed-note[
    The original proof invokes the number-field Brauer-Witt theorem, while this
    corollary allows arbitrary characteristic-zero fields. The base-change
    argument supplies the missing passage to that scope.
  ]
]

#heading(level: 3, numbering: none, outlined: false)[Notes]

+ Let $A$ be a central simple $K$-algebra, where $K$ is an algebraic number
  field, and consider the group $upright("Aut")_QQ A$ of $QQ$-automorphisms of
  $A$. Each $phi in upright("Aut")_QQ A$ induces a $QQ$-automorphism $phi'$ of
  $K$. We set
  $
    upright("Aut")(K,A)={sigma in upright("Aut")_QQ K:
      sigma=phi' "for some" phi in upright("Aut")_QQ A}.
  $
  Janusz~@bib:Janusz1976 showed that $upright("Aut")(K,A)$ consists precisely of
  those $sigma in upright("Aut")_QQ K$ such that for every prime $P$ of $K$,
  there is an isomorphism of rings
  $ K_P times.o_K A ≅ K_(P^sigma) times.o_K A. $
  (In this connection, see
  @case:schur-component-conjugate-prime-invariants[#context {
    reference-number-text(
      "("
        + reference-data(<th:benard-schacher>).text
        + reference-data(<case:schur-component-conjugate-prime-invariants>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }].)
+ From the Brauer-Witt Theorem @th:brauer-witt,
  part~@case:brauer-witt-primary-schur-index, the computation of Schur indices
  reduces to the case of $(K,p)$-elementary subgroups for various $K$ and $p$.
  This special case, nevertheless, can be quite difficult, and few general
  results are available.
+ For $zeta in upright("Irr") G$, and $p$ a prime, define $m_(QQ_p) lr((zeta))$
  as in the discussion following
  @th:character-field-schur-index-roots-local-uniformity. Feit~@bib:Feit1983
  proved:

  Let $x in G$ be a $p'$-element such that $zeta_i lr((x)) in QQ_p lr((zeta))$
  for every $zeta_i in upright("Irr") G$. Then
  $zeta(x) slash m_(QQ_p) lr((zeta))$ is an algebraic integer.

  Taking $x=1$, this yields the well-known result that $m_(QQ_p) lr((zeta))$
  divides $zeta(1)$; see @case:schur-index-divides-group-order[#context {
    reference-number-text(
      "("
        + reference-data(
          <rem:schur-index-fields-divisibility-inner-products>,
        ).text
        + reference-data(<case:schur-index-divides-group-order>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }] in this connection.
+ It is easily shown that each cyclotomic algebra is a simple component of some
  group algebra (see Yamada~@bib:Yamada1974, Prop. 2.1).
+ Let $K$ be a finite extension of $QQ_p$, where $p$ is prime, and let $G$ be a
  $p$-hyperelementary group (see @rem:rational-hyperelementary-induction). Then
  $ K G ≅ plus.o.big M_(n_i) lr((D_i)), $
  where for $p$ odd, each $D_i$ is a field, while for $p=2$, each $D_i$ is
  either a field or a skewfield of index $2$. This result was proved by
  Oliver~@bib:Oliver1981, Lemma 8, p. 187. It suffices to establish the result
  for $K=QQ_p$, and for this case one must prove that for
  $zeta in upright("Irr") G$, $m_K lr((zeta))=1$ or $2$. By Exercise
  @exc:elementary-group-character-properties, $zeta(1)$ is a power of $p$, and
  therefore so is $m_K lr((zeta))$. On the other hand, Witt has shown that for
  $F=K(root(p, 1))$, $m_F lr((zeta))=1$ or $2$. Oliver's Theorem now follows
  from Exercise @exc:schur-index-finite-extension-divisibility.

#source(777)
#exercises-heading

#exercise[
  Let $G$ be a finite group, and $k$ any field. Show that there exists a finite
  Galois extension $E$ of $k$ that is a splitting field for $G$ (that is,
  $E G slash "rad" E G$ is a split semisimple $E$-algebra).
]<exc:finite-galois-group-splitting-field>

#hint([@exc:finite-galois-group-splitting-field])[
  See the proof of @i:cor:perfect-field-galois-splitting-field. Instead of the
  hypothesis that $k$ be a perfect field, use
  @i:th:group-algebra-separable-radical-quotient and its proof.
]

#exercise[
  Let $A=M_r lr((D))$, where $D$ is a skewfield with center $K$ and index $m$.
  Let $V$ be a simple $(F times.o_K A)$-module, where $F$ is an extension field
  of $K$. Show that $V$ is absolutely simple if and only if $F$ splits $D$, that
  is, $F times.o_K D ≅ M_m lr((F))$.
]<exc:absolute-simplicity-division-splitting>

#hint([@exc:absolute-simplicity-division-splitting])[
  Let $times.o$ denote $times.o_K$. Then $F times.o A ≅ M_r lr((F times.o D))$,
  and $F times.o D ≅ M_s lr((D'))$ for some skewfield $D'$ with center $F$. Thus
  $F times.o A ≅ M_(r s) lr((D'))$, and $upright("End") V ≅ D'$. But $V$ is
  absolutely simple if and only if $D'=F$ (see
  @i:th:absolute-simplicity-centralizer), that is, $F$ splits $D$. It is easily
  checked that $s=m$ in this case.
]

#exercise[
  Let $k subset F subset Omega$ be fields, where $dim_k F$ is finite, and where
  $Omega$ is a splitting field for $G$. Let $zeta$ be an irreducible
  $Omega$-character of $G$, and let $m_k lr((zeta))$, $m_F lr((zeta))$ denote
  Schur indices. Prove that
  $ m_k lr((zeta)) "divides" m_F lr((zeta))dot dim_(k(zeta)) F(zeta). $
]<exc:schur-index-finite-extension-divisibility>

#exercise[
  Let $D$ be a skewfield with center $K$ and index $m$, and let $E$ be an
  extension field of $K$. Prove
  #case-list(
    numbering: "(i)",
    [#case[$E times.o_K D$ is a central simple $E$-algebra whose index divides
      $m$.]<case:division-index-extension-divisibility>],
    [#case[If $E$ splits $D$ and $dim_K E$ is finite, then $m$ divides
      $dim_K E$.]<case:division-index-splitting-degree-divisibility>],
  )
]<exc:division-algebra-index-scalar-extension>

#hint([@exc:division-algebra-index-scalar-extension])[
  For part~@case:division-index-splitting-degree-divisibility, see the end of
  the proof of @th:schur-index-character-realization.
]

#exercise[
  Let $L slash K$ be a finite Galois extension of number fields, and assume
  $G=upright("Gal")(L slash K)$ is abelian. Let $f:G times G arrow L^dot$ be a
  factor set. Fix $sigma in G$, and define $g=sigma f$. Show that $g$ is also a
  factor set, and that there is a $K$-algebra isomorphism
  $(L slash K,f) ≅ (L slash K,g)$ of crossed-product algebras.
]<exc:abelian-galois-factor-set-automorphism>

#hint([@exc:abelian-galois-factor-set-automorphism])[
  Since $G$ is abelian, $sigma f$ is a factor set. Write
  $(L slash K,f)=plus.o.big L u_x$, $(L slash K,g)=plus.o.big L v_x$, where the
  summation extends over $x in G$. The map $a u_x arrow sigma(a)v_x$, $a in L$,
  $x in G$, gives the desired isomorphism.
]

#exercise[
  Let $G=chevron.l a chevron.r ⋊ P$ be a $(K,p)$-elementary group, where
  $chevron.l a chevron.r$ is a cyclic $p'$-group and $P$ is a $p$-group. Prove:
  #case-list(
    numbering: "(i)",
    [#case[Each subgroup of $G$ is $(K,p)$-elementary.]
      <case:elementary-group-subgroups>],
    [#case[For $zeta in upright("Irr") G$, $zeta(1)$ is a power of $p$, and
      $zeta=lambda^G$ for some linear character $lambda$ of a subgroup of
      $G$.]<case:elementary-group-monomial-p-power-degrees>],
    [#case[If $H≤G$ has $p$-power index, then $a in H$.]
      <case:elementary-group-p-power-index-subgroup>],
    [#case[If $H≤G$, and $mu in upright("Irr") H$ is such that
        $mu^G in upright("Irr") G$, then $|G:H|=p$-power, and $a in H$.]
      <case:elementary-group-irreducible-induction-index>],
  )
]<exc:elementary-group-character-properties>

#hint([@exc:elementary-group-character-properties])[
  For part~@case:elementary-group-monomial-p-power-degrees, use Ito's Theorem
  @i:cor:ito-character-degree and Blichfeldt's Theorem
  @i:prop:blichfeldt-imprimitivity. For
  part~@case:elementary-group-irreducible-induction-index, we have
  $mu^G lr((1))=|G:H|mu(1)$.
]

#exercise[
  Let $K subset E$ be algebraic number fields, $n=dim_K E$, and let $p$ be a
  prime such that $p divides.not n$.
  #source(778)
  Denote by $B(K)_p$ the $p$-torsion subgroup of the Brauer group $B(K)$. Prove
  that there is an injective homomorphism
  $ B(K)_p arrow B(E)_p, $
  defined by $E times.o_K *$.
]<exc:brauer-p-torsion-prime-to-p-extension>

#hint([@exc:brauer-p-torsion-prime-to-p-extension])[
  Let $[A] in B(K)_p$ have index $m$, so $m$ is a power of $p$. If
  $[E times.o_K A]=1$ in $B(E)$, then $E$ splits $A$, so $m divides n$ by
  Exercise @exc:division-algebra-index-scalar-extension.
]

#exercise[
  Let $B_i=(L_i slash K,f_i)$, $i=1,2$, be cyclotomic algebras over $K$. Prove
  that $B_1 times.o_K B_2$ is similar to a cyclotomic algebra over $K$.
]<exc:cyclotomic-algebra-tensor-product>

#hint([@exc:cyclotomic-algebra-tensor-product])[
  After inflation (see @bib:Reiner1975[MO] (29.16)), we may assume that
  $L_1=L_2$. Then use @eq:brauer-crossed-product-cohomology.
]
