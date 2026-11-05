#import "main-defs.typ": *
#import "statements.typ": *
#import "case-series.typ": *
#import "diagrams/81-representation-rings.typ": *

== Representation Rings <sec:representation-rings>

We shall study representations of a finite group $G$ over some integral domain
$R$, usually chosen as a field of characteristic $p$ or a ring of $p$-adic
integers. We restrict our attention always to $R G$-lattices, that is, f.g.
$R G$-modules that are $R$-projective. For $R$ a field, every f.g. $R G$-module
is automatically a lattice; for $R$ a P.I.D., the lattices are $R G$-modules
with finite $R$-bases.

The algebraic framework for our investigation is the _representation ring_
$a(R G)$. This is also called the _Green ring_, after J. A.
Green~@bib:Green1962b. By definition, $a(R G)$ is spanned over $ZZ$ by elements
$[M]$, one for each isomorphism class of $R G$-modules. These elements are
combined according to the formulas
$ [M]+[M'] = [M plus.o M'], quad [M][M'] = [M times.o_R M'], $
where $G$ acts diagonally in the inner tensor product $M times.o_R M'$. Then
$a(R G)$ is a commutative ring with identity element $[R]$, where $G$ acts
trivially on $R$. Let $M,N$ be $R G$-lattices; as in the proof of
@prop:grothendieck-equal-classes-criterion, we have $[M]=[N]$ in $a(R G)$ if and
only if $M plus.o X tilde.equiv N plus.o X$ for some $R G$-lattice $X$. If
cancellation holds for $R G$-lattices, as is the case if $R$ is a field or a
complete d.v.r., then $[M]=[N]$ if and only if $M tilde.equiv N$.

We are interested here in the problems about $R G$-lattices that arise from
studying the algebraic structures of $a(R G)$. It is usually easier to work with
the _representation algebra_ (or _Green algebra_)
$ A_CC lr((R G)) = CC times.o_ZZ a(R G). $
#idx("Representation algebra")
#idx("Green algebra", see: ("Representation algebra",))
#source(885)
One also studies the rings
$
  A_QQ lr((R G)) = QQ times.o_ZZ a(R G), quad "and" A_(Z') lr((R G)) = Z'
  times.o_ZZ a(R G),
$
where $Z'$ is any commutative ring.

=== Preliminary Results <ss:representation-ring-preliminaries>

In this section we shall collect some fundamental definitions and notation,
involving ground field extension, relative projective modules, and induced
modules. In many cases, the proofs are easy generalizations of those given in
earlier sections, and are sketched briefly or sometimes omitted.

#case-series(numbering: "(I)")[
  #case-heading[*_Ground Field
  Extension_*] <case:representation-ground-field-extension>

  Throughout let $G$ be a finite group, and $K$ a field with
  $op("char") K = p >= 0$. We collect here some facts about indecomposability of
  $K G$-modules $M$ where as usual we consider only f.g. modules. Given a
  $K G$-module $M$, we set
  $
    E(M) = op("End")_(K G) M, quad tilde(E) lr((M)) = E(M) slash
    lr((op("rad") E(M))).
  $
  <eq:module-endomorphism-semisimple-quotient>
  By §~@i:ss:idempotents, $M$ is indecomposable if and only if $E(M)$ is a local
  ring, or equivalently, $tilde(E) lr((M))$ is a division algebra. Note that
  both $E(M)$ and $tilde(E) lr((M))$ are f.d./$K$, so if $K$ is algebraically
  closed, then $M$ is indecomposable if and only if
  $tilde(E) lr((M)) tilde.equiv K$.

  In general, we call a $K G$-module $M$ _absolutely indecomposable_ if for each
  field $K' supset.eq K$, the $K' G$-module $K' times.o_K M$ is indecomposable.
  The discussion in §~@i:ss:extension-ground-ring-local-theory carries over to
  the present case, and we obtain the following analogue of
  @i:th:absolute-indecomposability-inseparable, whose proof is left to the
  reader:
  #idx("Absolutely indecomposable")

  #theorem[
    For $M$ a $K G$-module, define $tilde(E) lr((M))$ by
    @eq:module-endomorphism-semisimple-quotient. Then $M$ is absolutely
    indecomposable if and only if $tilde(E) lr((M))$ is a field that is purely
    inseparable over $K$. In particular, $M$ is absolutely indecomposable
    whenever $tilde(E) lr((M)) tilde.equiv K$. If $K$ is algebraically closed,
    then every indecomposable $K G$-module is absolutely indecomposable.
  ] <th:absolute-indecomposable-group-module-criterion>

  We shall next give a generalization of Exercises
  @i:exc:semisimple-scalar-extension-complement and
  @i:exc:finite-field-extension-complement-descent, concerning properties of
  direct summands under ground field extension. For a $K G$-module $X$, and a
  field $L$ containing $K$, set $X^L = L times.o_K X$, an $L G$-module. By
  @i:eq:hom-field-extension we have
  $ op("End")_(L G) lr((X^L)) tilde.equiv L times.o_K op("End")_(K G) X. $
  As usual, $X divides Y$ means that $X$ is isomorphic to a direct summand of
  $Y$. The following result may be viewed as a generalization of the
  Noether–Deuring Theorem (see Exercise @i:exc:noether-deuring):

  #theorem[
    Let $X$ and $Y$ be $K G$-modules, and let $L$ be an extension field of $K$.
    Then $X^L divides Y^L$ if and only if $X divides Y$.
  ] <th:field-extension-direct-summand-descent>
  #source(886)
  #proof[
    Clearly $X divides Y$ implies $X^L divides Y^L$. For the reverse
    implication, let $X tilde.equiv V plus.o X_0$, $Y tilde.equiv V plus.o Y_0$.
    Then $X_0^L divides Y_0^L$, and it suffices to prove that $X_0 divides Y_0$.
    Changing notation, we may assume that $X$ and $Y$ have no common direct
    summand, and that $X^L divides Y^L$. We must show that $X=0$, so assume
    $X != 0$ and let us obtain a contradiction. Extending the field $L$ if need
    be, we may assume that $L$ contains an algebraic closure $E$ of $K$. Then
    $X^L = (X^E)^L$, and we set #named-equation(name: [$(ast)$])[
      $ X^E = plus.o.big X_i, quad Y^E = plus.o.big Y_j, $
    ] <eq:scalar-extension-indecomposable-decompositions>
    where the ${X_i}$ and ${Y_j}$ are absolutely indecomposable $E G$-modules
    (see @th:absolute-indecomposable-group-module-criterion and the discussion
    preceding it). Then $X_1^L$ is indecomposable, and is a direct summand of
    $(Y^E)^L$, so $X_1^L tilde.equiv Y_j^L$ for some $j$, say $j=1$ to fix the
    notation. Therefore $X_1 tilde.equiv Y_1$ by the Noether–Deuring Theorem.

    Now let $pi: X^E -> X_1$ and $pi': Y^E -> Y_1$ be the idempotent projection
    maps associated with the decompositions in
    @eq:scalar-extension-indecomposable-decompositions. Then
    $pi in op("End")_(E G) lr((X^E)) = E times.o_K op("End")_(K G) X$, and since
    $E slash K$ is algebraic, it follows that $E$ contains a field $F$ that is
    f.d./$K$, and such that
    $
      pi in op("End")_(F G) lr((X^F)),
      quad pi' in op("End")_(F G) lr((Y^F)).
    $
    We have
    $ X_1 = {pi(X^F)}^E tilde.equiv Y_1 = {pi'(Y^F)}^E, $
    so $pi(X^F) tilde.equiv pi'(Y^F)$ by the Noether–Deuring Theorem. This shows
    that $X^F$ and $Y^F$ have a common direct summand. However,
    $X^F tilde.equiv X^((n))$ and $Y^F tilde.equiv Y^((n))$ as $K G$-modules,
    where $n = dim_K F$. It follows that the $K G$-modules $X^((n))$ and
    $Y^((n))$ have a common direct summand, and therefore so do $X$ and $Y$.
    This is a contradiction, and completes the proof.
  ]

  #remark[
    The above argument also shows that if $X^L$ and $Y^L$ have a common direct
    summand, then so do $X$ and $Y$.
  ] <rem:field-extension-common-summand-descent>

  To conclude these remarks about ground field extension, we consider the
  representation ring $a(K G)$ and the representation algebra
  $A(K G) = CC times.o_ZZ a(K G)$. We note that for $K G$-modules $M$ and $N$,
  we have $[M]=[N]$ in $a(K G)$ if and only if $M tilde.equiv N$. The
  Noether–Deuring Theorem (Exercise @i:exc:noether-deuring) then gives:

  #proposition[
    Let $E$ be an extension field of $K$. Then there are ring monomorphisms
    $ a(K G) -> a(E G), quad A(K G) -> A(E G), $
    given by $[X] |-> [E times.o_K X]$ for each $K G$-module $X$.
  ] <prop:scalar-extension-representation-ring-embedding>

  We now view $A(K G)$ as embedded in $A(E G)$, and prove the following result
  of Benson–Parker~@bib:Benson1984\:

  #source(887)
  #theorem[
    Let $E slash K$ be a separable algebraic extension of fields. Then $A(E G)$
    is integral over its subring $A(K G)$.
  ] <th:benson-parker-field-extension-integrality>
  #idx(
    "Benson-Parker Theorem",
    target: [@th:benson-parker-field-extension-integrality],
  )
  #proof[
    Each $E G$-module $M$ affords a matrix representation of $G$ with entries in
    some finite extension field of $K$. Thus for each $x in A(E G)$, $E$
    contains a subfield $F$ finite over $K$, such that $x$ lies in the image of
    $A(F G)$ in $A(E G)$. It is therefore sufficient to prove the result for
    $E slash K$ finite.

    Extending $E$ if need be, we may assume that $E slash K$ is a finite Galois
    extension with Galois group $frak(G)$. Then $frak(G)$ acts on $A(E G)$. Let
    $a in A(E G)$. Clearly $a$ is a zero of the polynomial
    $ product_(sigma in frak(G)) (X-a^sigma), $
    so we need only show that each coefficient lies in $A(K G)$. We note that
    each coefficient $b$ lies in $A(E G)$ and is fixed by $frak(G)$.

    Let $b = sum lambda_(i)[M_i]$, $lambda_i in CC$, $M_i = E G"-module"$. For
    each $E G$-module $M$ occurring in $b$, all of its $frak(G)$-conjugates also
    occur, and with the same coefficient. It thus suffices to show that if
    $M_1, dots, M_t$ are the distinct $frak(G)$-conjugates of $M$, then
    $c = sum_(i=1)^t [M_i] in A(K G)$. Now we have
    $ product.co_(sigma in frak(G)) M^sigma tilde.equiv E times.o_K M $
    by the proof of @i:eq:unramified-conjugate-lattice-decomposition. On the
    other hand, $product.co_(sigma in frak(G)) [M^sigma] = n c$, where $n$ is
    the order of the $frak(G)$-stabilizer of $M$. Thus $n c in A(K G)$, so also
    $c in A(K G)$, as desired.
  ]

  #case-heading[*_Restriction, Induction,
  Conjugation_*] <case:representation-induction-restriction-conjugation>

  Let $G$ be a finite group, $R$ an integral domain, and denote the
  representation ring $a(R G)$ by $a(G)$, for brevity. For $H <= G$, the
  _restriction map_ $op("res")_H^G: a(G) -> a(H)$ is a ring homomorphism. For
  $x in a(G)$, set $x_H = op("res")_H^G x$ for brevity. The _induction map_
  $op("ind")_H^G: a(H) -> a(G)$, given by $y |-> y^G$, is an additive
  homomorphism. Then $a(G)$ is a Frobenius functor of $G$ (see
  §~@ss:grothendieck-frobenius).

  For $H,K <= G$, write $H <=_G K$ to indicate that some $G$-conjugate of $H$ is
  contained in $K$. A collection $cal(C)$ of subgroups of $G$ is called
  _subconjugately closed_ if
  $ E <=_G H in cal(C) => E in cal(C). $
  For any $cal(C)$, define
  $
    a(G)_(cal(C)) = sum_(H in cal(C)) a(H)^G, quad a(G)^(cal(C)) = {x in
      a(G): x_H=0 "for all" H in cal(C)},
  $
  where $a(H)^G$ means $op("ind")_H^G a(H)$. By the Frobenius identities, both
  $a(G)_(cal(C))$ and $a(G)^(cal(C))$ are ideals of $a(G)$; further,
  $ a(G)_(cal(C)) dot a(G)^(cal(C)) = 0 $
  #source(888)
  by @prop:frobenius-family-ideals. Both ideals are unchanged if $cal(C)$ is
  replaced by its subconjugate closure. In keeping with the above notation, for
  $H <= G$ we write
  $ a(G)^H = {x in a(G): x_H=0}. $
  This notation is unorthodox, but unambiguous since for $H <= G$, the
  superscript $H$ cannot possibly indicate induction.

  #case-heading[*_Relative Splitting and Relative Projective
  Modules_*] <case:relative-splitting-projective-modules>

  Throughout, “$G$-module” means “$R G$-lattice,” where $R$ is some integral
  domain fixed during the discussion. Let
  $ xi: 0 -> L -> M -> N -> 0 $
  <eq:group-lattice-short-exact-sequence>
  be a $G$-ses, that is, a short exact sequence of $G$-modules. For $H <= G$,
  restriction of operators gives an $H$-ses
  $ xi_H: 0 -> L_H -> M_H -> N_H -> 0. $
  If this latter sequence is split exact, we call $xi$ _$H$-split_.
  #idx(
    "Split exact sequence",
    target: [@eq:group-lattice-short-exact-sequence],
  )

  #proposition[
    Let $H <= G$, and let $xi$ be any $G$-ses.
    #case-list(
      numbering: "(i)",
      [
        #case[
          If $xi$ is $H$-split, then also $xi$ is $E$-split whenever $E <=_G H$.
        ] <case:relative-splitting-subconjugate-subgroup>],
      [
        #case[
          $xi$ is $H$-split if and only if $(xi_H)^G$ is $G$-split.
        ] <case:relative-splitting-induced-restriction>],
      [
        #case[
          Let $E <= H$ be such that $abs(H : E) in R^times$. Then $xi$ is
          $H$-split if and only if $xi$ is $E$-split.
        ] <case:relative-splitting-unit-index>],
      [
        #case[
          For any $G$-module $M$, set $(M_H)^G = R G times.o_(R H) M$, and
          define a $G$-surjection $mu: (M_H)^G -> M$ by $mu(g times.o m) = g m$,
          $g in G$, $m in M$. Then the $G$-ses
          $ 0 -> ker mu -> (M_H)^G arrow.r^mu M -> 0 $
          is $H$-split, and the splitting map $i: M -> (M_H)^G$ such that
          $mu i = op("id")_M$ is given by $i(m) = 1 times.o m$, $m in M$.
        ] <case:canonical-induced-projection-relative-section>
      ],
    )
  ] <prop:relative-splitting-properties>
  #proof[
    To prove @case:relative-splitting-subconjugate-subgroup, consider an
    $H$-splitting $theta: N -> M$ of a $G$-surjection $f: M -> N$. For $E <= H$,
    $theta$ is also an $E$-homomorphism. Thus if $xi$ is $H$-split, it is also
    $E$-split. Further, for $x in G$, the $x$-conjugate of $theta$ gives an
    $E^x$-splitting of $f$. This completes the proof of
    @case:relative-splitting-subconjugate-subgroup. Assertion
    @case:relative-splitting-unit-index is obvious, while
    @case:canonical-induced-projection-relative-section is established as in the
    proof of @i:lem:induction-relative-splittings part (b).

    To prove @case:relative-splitting-induced-restriction, consider the diagram

    #relative-splitting-square

    #source(889)
    where $f$ is a $G$-surjection, and the vertical maps are as in
    @case:canonical-induced-projection-relative-section. The diagram commutes,
    using either upward or downward arrows. To prove
    @case:relative-splitting-induced-restriction, it suffices to show that a
    $G$-splitting $psi': (N_H)^G -> (M_H)^G$ of $1 times.o f$ gives rise to an
    $H$-splitting of $f$. It is easily verified that $mu psi' i'$ is the desired
    $H$-splitting of $f$, which completes the proof.
  ]

  Let $H <= G$; a $G$-module $M$ is called _$(G,H)$-projective_ if every $G$-ses
  $ 0 -> X -> Y -> M -> 0 $
  <eq:relative-projectivity-test-sequence>
  which is $H$-split is also necessarily $G$-split. There is a dual concept of
  _$(G,H)$-injective_ $G$-modules. By @i:th:gaschutz-relative-projectivity, the
  following conditions are equivalent:#footnote[
    As usual, $X divides Y$ means $X$ is isomorphic to a direct summand of $Y$.
  ]
  #idx("Relative projective")
  #idx("Relative injective")
  #case-list(
    numbering: "(i)",
    [
      #case[$M$ is $(G,H)$-projective.]
      <case:single-subgroup-relative-projectivity>],
    [
      #case[$M$ is $(G,H)$-injective.]
      <case:single-subgroup-relative-injectivity>],
    [
      #case[
        If $G = union.dot g_i H$, then $sum_i g_i gamma g_i^(-1) = op("id")_M$
        for some $gamma in op("End")_(R H) M$.
      ] <case:single-subgroup-relative-trace-identity>],
    [
      #case[$M divides (M_H)^G$.]
      <case:single-subgroup-relative-induced-restriction-summand>],
    [
      #case[$M divides L^G$ for some $H$-module $L$.]
      <case:single-subgroup-relative-induced-summand>
    ],
  )

  Every $G$-module is $(G,G)$-projective. At the other extreme, the
  $(G,1)$-projective $G$-modules are the usual f.g. projective $R G$-modules,
  because of our agreement that “$G$-module” means “$R G$-lattice.” Note that if
  $abs(G : H) in R^times$, we may choose $gamma = abs(G : H)^(-1)$ in
  @case:single-subgroup-relative-trace-identity, so _every_ $G$-module is
  $(G,H)$-projective in this case.

  Generalizing the above, let $cal(C)$ be any collection of subgroups of $G$. We
  say that a $G$-ses $xi$ is _$cal(C)$-split_ if $xi$ is $H$-split for every
  $H in cal(C)$. A $G$-module $M$ is _$(G,cal(C))$-projective_ if each $G$-ses
  @eq:relative-projectivity-test-sequence that is $cal(C)$-split is necessarily
  $G$-split. Just as above, we have:

  #proposition[
    Let $cal(C)$ be a nonempty set of subgroups of $G$, and let $M$ be a
    $G$-module ($= R G$-lattice). The following are equivalent:
    #case-list(
      numbering: "(i)",
      [
        #case[$M$ is $(G,cal(C))$-projective.]
        <case:subgroup-family-relative-projectivity>],
      [
        #case[$M$ is $(G,cal(C))$-injective.]
        <case:subgroup-family-relative-injectivity>],
      [
        #case[
          There exist endomorphisms $phi_C in op("End")_(R C) M$ such that
          $ sum_(C in cal(C)) sum_(g_C) g_C phi_C g_C^(-1) = op("id")_M, $
          where for each $C in cal(C)$ the element $g_C$ ranges over a cross
          section of left cosets $G slash C$.
        ] <case:subgroup-family-relative-trace-identity>],
      [
        #case[$M divides product.co_(C in cal(C)) (M_C)^G$.]
        <case:subgroup-family-relative-induced-restriction-summand>],
      [
        #case[
          $M divides product.co_(C in cal(C)) (L(C))^G$, where each $L(C)$ is a
          $C$-module.
        ] <case:subgroup-family-relative-induced-summand>
      ],
    )
  ] <prop:subgroup-family-relative-projectivity-criteria>
  #source(890)
  #proof(head: emph[Sketch of Proof.])[
    The $G$-surjection
    $ f: product.co_(C in cal(C)) (M_C)^G -> M $
    is always $cal(C)$-split. If $M$ is $(G,cal(C))$-projective, there is a
    $G$-homomorphism $theta: M -> product.co (M_C)^G$ that splits $f$. As in the
    proof of @i:th:gaschutz-relative-projectivity, it is easily seen that
    $theta = product.co theta_C$, where for $C in cal(C)$,
    $
      theta_C lr((m)) = sum_(g_C) g_C times.o phi_C lr((g_C^(-1) m)), quad m
      in M,
    $
    with $phi_C in op("End")_(R C) M$. Then
    @case:subgroup-family-relative-trace-identity follows from the formula
    $f theta = op("id")_M$.

    Next, for each $C in cal(C)$ we can find a $C$-homomorphism
    $psi_C: M -> (M_C)^G$ splitting the $G$-surjection $(M_C)^G -> M$. Suppose
    now that @case:subgroup-family-relative-trace-identity holds. It is then
    easily checked that
    $ sum_(C in cal(C)) sum_(g_C) g_C psi_C phi_C g_C^(-1) $
    is a $G$-homomorphism from $M$ into $product.co (M_C)^G$ that splits $f$.
    The proofs of the remaining equivalences among the above five conditions are
    as in @i:th:gaschutz-relative-projectivity, and are left to the reader.
  ]

  It follows readily that if $M$ is $(G,cal(C))$-projective, so is
  $M times.o_R X$ for each $G$-module $X$. Further, if $N$ is a $C$-module where
  $C in cal(C)$, the induced $G$-module $N^G$ is necessarily
  $(G,cal(C))$-projective and so is each direct summand of $N^G$. Now define
  $a(G,cal(C)) =$ subgroup of $a(G)$ spanned by all $(G,cal(C))$-projectives.
  Then by the above, $a(G,cal(C))$ is an ideal of $a(G)$, and
  $
    a(G)_(cal(C)) = sum_(C in cal(C)) a(C)^G subset.eq a(G,cal(C)) subset.eq
    a(G).
  $
  <eq:relative-projective-induction-ideal-inclusion>
  Furthermore, the induced ideal and the restriction kernel satisfy
  $ a(G)_(cal(C)) dot a(G)^(cal(C)) = 0. $
  <eq:relative-projective-restriction-annihilation>

  #remark(numbered: false)[
    Let $i_(cal(C))$ be the ideal of $a(G)$ generated by $[M]-[L]-[N]$ for all
    $cal(C)$-split ses's $0 arrow.r L arrow.r M arrow.r N arrow.r 0$.#ed-note[
      The relative-projective ideal need not annihilate the restriction kernel.
      For $R=CC$, $G=C_2$ and $cal(C)={1}$, every module is relatively
      $1$-projective, but the nonzero class $["sign"]-[1]$ restricts to zero.
    ] Then $a(G,cal(C)) dot i_(cal(C))=0$. Indeed, tensoring such a sequence
    with an induced lattice $U^G$, where $U$ is an $R C$-lattice and
    $C in cal(C)$, gives a split sequence by the tensor identity
    @i:cor:induction-tensor-identity, since its restriction to $C$ is split. If
    a lattice is a direct summand of a sum of these induced lattices, compose a
    contracting homotopy with the inclusion and projection of that summand. The
    tensor sequence is again split. This proves the assertion for every
    relatively $cal(C)$-projective lattice and hence for the ideal.
  ] <rem:relative-split-relation-annihilation>

  (A. Dress has introduced a variant of the above concepts. Given a $G$-set $S$,
  form the permutation module $R[S]$. For any $G$-module $M$, let us set
  $ M[S] = R[S] times.o_R M quad "(inner tensor product)." $
  We say that the $G$-ses $xi$ in @eq:group-lattice-short-exact-sequence is
  _$S$-split_ if the $G$-ses
  $ xi[S]: 0 -> L[S] -> M[S] -> N[S] -> 0 $
  is $G$-split. Let $S = union.dot S_i$ be a partition of $G$-sets, and let
  $f: M -> N$ be a $G$-homomorphism. Then
  $1 times.o f: R[S] times.o M -> R[S] times.o N$ carries $M[S_i]$ into
  $N[S_i]$. Therefore $xi$ is $S$-split if and only if $xi$ is $S_i$-split for
  each $i$.
  #source(891)
  Now let $S_i$ be a transitive $G$-set, say $S_i tilde.equiv G slash H_i$ for
  some $H_i <= G$. By @i:cor:induction-tensor-identity,
  $
    R(G slash H_i) times.o_R M tilde.equiv (R_(H_i))^G times.o_R M tilde.equiv
    (M_(H_i))^G.
  $
  Thus $xi[S_i]$ splits if and only if $(xi_(H_i))^G$ splits, and by
  @prop:relative-splitting-properties
  part~@case:relative-splitting-induced-restriction this occurs if and only if
  $xi$ is $H_i$-split. Given a $G$-set $S$, let
  $ cal(U)(S) = {H <= G: op("inv")_H S != emptyset}, $
  so $cal(U)(S)$ consists of all subgroups $H <= G$ that stabilize at least one
  element of the $G$-set $S$. The above discussion gives
  $ xi "is" S"-split" <=> xi "is" H"-split for each" H in cal(U)(S). $
  In the same way, we can define what is meant by a $G$-module $M$ to be
  $(G,S)$-projective. It is easily seen that $M$ is $(G,S)$-projective if and
  only if $M$ is $(G,cal(U)(S))$-projective.)

  #case-heading[*_Change of Groups_*] <case:representation-change-of-groups>

  In §~@ss:conlon-induction, we used the Conlon Induction Theorem to establish a
  relation @cor:conlon-representation-algebra-induction-detection between the
  representation algebra $A(K G)$ and the algebras $A(K H)$, with $H$ ranging
  over all $p$-hypo-elementary subgroups of $G$. Here, $K$ is a field of
  characteristic $p >= 0$. We now concentrate on a related question, that of
  comparing the algebras $A(K G)$ and $A(K H)$, where $H$ is a subgroup of $G$.
  The results are due to Benson–Parker~@bib:Benson1984, and the first is an easy
  consequence of our earlier calculations with Burnside rings.

  #theorem[
    Let $H <= G$, and let $K$ be any field. Let
    $
      A(K G) = CC times.o_ZZ a(K G),
      quad A(K H)^G = op("ind")_H^G A(K H), quad A(K
        G)^H = {x in A(K G): x_H=0}.
    $
    Then $A(K G)$ is a direct sum of ideals:
    $ A(K G) = A(K H)^G plus.o A(K G)^H. $
  ] <th:representation-induction-restriction-ideal-decomposition>
  #proof[
    Let $Omega(G)$ be the Burnside ring of $G$ (see @def:burnside-ring). Then
    $A(K G)$ is a Frobenius module over $Omega(G)$, and so the desired result
    follows from the special case of
    @cor:burnside-frobenius-module-decomposition in which $cal(C)$ consists of
    the single subgroup $H$. Benson and Parker prove this theorem directly, but
    their argument is essentially the same as that which establishes the general
    formula (see @cor:burnside-frobenius-module-decomposition)
    $ A(K G) = A(K G)_(cal(C)) plus.o A(K G)^(cal(C)) $
    for any set $cal(C)$ of subgroups of $G$.
  ]

  #source(892)
  The next result, again due to Benson–Parker, is a bit more complicated. The
  simplified proof below is due to Landrock.

  #theorem[
    Let $H <= G$, and let $K$ be any field. Set
    $
      A(K G)_H = op("res")_H^G A(K G), quad attach(
        A(K H),
        tl: G
      ) = {x in A(K H):
        x^G=0}.
    $
    Then $A(K G)_H$ is a subalgebra of $A(K H)$, and
    $ A(K H) = A(K G)_H plus.o attach(A(K H), tl: G), $
    a direct sum of vector spaces over $CC$.
  ] <th:benson-parker-restriction-induction-kernel-decomposition>
  #idx(
    "Benson-Parker Theorem",
    target: [@th:benson-parker-restriction-induction-kernel-decomposition],
  )
  #proof[
    We show first that $A(K H) = tilde(A)$, where we temporarily write
    $ A(K G)_H + attach(A(K H), tl: G) = tilde(A). $
    For $E <= H$, we shall prove by induction on $abs(E)$ that #named-equation(
      name: [$(ast)$],
    )[
      $ M^H in tilde(A) quad "for each" K E"-module" M. $
    ] <eq:representation-induction-image-kernel-span>
    Once this is established, we take $E=H$, to obtain $A(K H) = tilde(A)$.

    When $E=1$, we have
    $
      [(K_E)^H] = [K H] = abs(G : H)^(-1) op("res")_(H)^(G)[K G] in A(K G)_H,
    $
    so @eq:representation-induction-image-kernel-span holds when $E=1$. Now let
    $abs(E)>1$, and let $M$ be a $K E$-module. Mackey's Formula gives
    $
      (M^G)_H tilde.equiv product.co_(x) (attach(M, tl: x)|_(attach(E, tl: x)
        inter H))^H, quad "where" G = union.dot H x E.
    $
    The left-hand expression lies in $A(K G)_H$; the terms on the right for
    which $abs(attach(E, tl: x) inter H) < abs(E)$ lie in $tilde(A)$, by the
    induction hypothesis. Finally, if $x in G$ is such that
    $attach(E, tl: x) <= H$, then the corresponding term on the right is
    $ (attach(M, tl: x)|_(attach(E, tl: x)))^H, $
    which differs from $(M_E)^H$ by an element of $attach(A(K H), tl: G)$. It
    follows that
    $ k[(M_E)^H] in tilde(A), $
    where $k$ is the number of double coset representatives $x$ for which
    $attach(E, tl: x) <= H$. This proves
    @eq:representation-induction-image-kernel-span, and shows that
    $A(K H) = tilde(A)$.

    It remains to show that
    $ A(K G)_H inter attach(A(K H), tl: G) = 0. $
    #source(893)
    Let $x$ lie in the intersection, and write $x=z_H$ for some $z in A(K G)$.
    Now
    $ A(K G)_H dot attach(A(K H), tl: G) subset.eq attach(A(K H), tl: G) $
    by a Frobenius identity. Since $A(K H) = tilde(A)$, we deduce that
    $ A(K H) dot x subset.eq attach(A(K H), tl: G). $
    Therefore
    $ z dot A(K H)^G = (z_H dot A(K H))^G = (x dot A(K H))^G = 0. $
    It follows from @th:representation-induction-restriction-ideal-decomposition
    that $z in A(K G)^H$, that is, $z_H=0$. This proves that $x=0$, and
    establishes the theorem.
  ]

  We conclude with an interesting result of Puig (see
  Benson–Parker~@bib:Benson1984, Prop.~5.3), needed for our later work.

  #theorem[
    For $H <= G$, $A(K H)$ is integral over its subring $op("res")_H^G A(K G)$.
  ] <th:puig-restriction-image-integrality>
  #idx("Puig's Theorem", target: [@th:puig-restriction-image-integrality])
  #proof[
    We drop the symbol $K$, and write $A(G)_H$ instead of
    $op("res")_H^G A(K G)$, so $A(G)_H$ is a subalgebra of $A(H)$. Let
    $N=N_G lr((H))$, so $N$ acts by conjugation on $A(H)$; denote by
    $op("inv")_N A(H)$ the $N$-fixed subalgebra of $A(H)$. For $a in A(H)$, the
    polynomial
    $ product_(x in N) (X-a^x) $
    has coefficients in $op("inv")_N A(H)$, and $X=a$ is a zero of the
    polynomial. Therefore $A(H)$ is integral over $op("inv")_N A(H)$. By
    “transitivity of integrality,” it thus suffices to show that
    $op("inv")_N A(H)$ is integral over $A(G)_H$. Using induction on $abs(H)$,
    we may assume the result for each $E<H$.

    Given $a in op("inv")_N A(H)$, for each $E<H$ we put
    $ X(E) = {op("res")_E^(H^g) lr((a^g)): g in G "such that" E < H^g}, $
    and let
    $
      Y(E) = "subring of" A(E) "generated by" A(G)_E "and the finite set"
      X(E).
    $
    Then $Y(E)$ is f.g. over $A(G)_E$, by the induction hypothesis. We now set
    $ B = A(G)_H + sum_(E<H) (Y(E))^H subset.eq A(H), $
    which is an $A(G)_H$-submodule of $A(H)$, since for $alpha in A(G)$,
    $beta in Y(E)$, we have
    $ alpha_H dot beta^H = (alpha_E dot beta)^H in Y(E)^H. $
    We shall show that $B$ is a ring containing $a$, and that $B$ is f.g. as
    $A(G)_H$-module,
    #source(894)
    which will imply the desired conclusion that $a$ is integral over $A(G)_H$.
    To show that $a in B$, we use the fact that $a^g=a$ for all $g in N$, so
    Mackey's Formula gives
    $ (a^G)_H = abs(N : H) a + sum_(x) ((a^x)_(H inter H^x))^H, $
    where $x$ ranges over some elements of $G-N$. Each summand thus lies in
    $X(E)^H$, hence in $B$. Since $(a^G)_H in A(G)_H$, we deduce that $a in B$,
    as claimed.

    To prove that $B$ is a ring, let $D<H$, $E<H$, $y in Y(D)$, $z in Y(E)$, and
    consider $y^H dot z^H$ in $A(H)$. By Mackey's Formula,
    $ y^H dot z^H = sum_(g) ((y dot z^g)_(F_g))^H, $
    where $g$ ranges over certain elements of $G$, and where
    $F_g = D inter E^g$. Since $y$ lies in the subring of $A(D)$ generated by
    $A(G)_D$ and $X(D)$, its restriction to $F_g$ lies in the subring of
    $A(F_g)$ generated by $A(G)_(F_g)$ and $X(D)_(F_g)$. But
    $X(D)_(F_g) subset.eq X(F_g)$ from the definitions of $X(D)$ and $X(F_g)$.
    Thus $y_(F_g) in Y(F_g)$. Likewise, conjugating and restricting the
    generators of $Y(E)$ shows that $(z^g)_(F_g) in Y(F_g)$, so
    $ ((y dot z^g)_(F_g))^H in Y(F_g)^H subset.eq B. $
    Finally, for each $E<H$, $Y(E)$ is a f.g. module over $A(G)_E$, say
    $ Y(E) = sum A(G)_E dot c, $
    with $c$ ranging over some finite subset of $A(E)$. For $alpha in A(G)$, we
    have
    $
      (alpha_E dot c)^H = ((alpha_H)_E dot c)^H = alpha_H dot c^H in A(G)_H
      c^H,
    $
    so
    $ Y(E)^H = sum A(G)_H c^H. $
    Thus $B$ is f.g. as $A(G)_H$-module, and the proof is finished.
  ]
]

=== Conlon's Theorems <ss:conlon-representation-ring-theorems>

Let $R$ be either a complete d.v.r. with $R slash frak(p)=k$,
$op("char") k=p>0$, or else $R=k$ (and $p>0$). Our aim here is to prove Conlon's
Theorems concerning decompositions of the representation algebra $A(R G)$, and
the relations between idempotents in $A(R G)$ and those in the Burnside algebra
$CC times.o_ZZ Omega(G)$, where $Omega(G)$ is the Burnside ring of $G$. We shall
follow the approach given in Benson~@bib:Benson1984a. (For other treatments, see
Conlon~@bib:Conlon1968a, @bib:Conlon1968b, and Feit~@bib:Feit1982.)

An $R G$-lattice $M$ will be called _permutation projective_ (notation: pp), or
a _trivial source module_, if $M$ is a direct summand of a permutation module.
The terminology is justified by the following result, used repeatedly throughout
our discussion (see also Exercise @exc:trivial-source-module-vertices).
#idx("Permutation projective")
#idx("pp-module")

#source(895)
#lemma[
  Let $P <= G$, where $P$ is a $p$-group.
  #case-list(
    [
      #case[The trivial module $1_P$ has vertex $P$.]
      <case:pp-trivial-module-vertex>],
    [
      #case[For $M in op("Ind") R G$, $M$ is a pp module if and only if $M$ has
        trivial source.] <case:pp-trivial-source-equivalence>],
    [
      #case[If $P ◁ G$, then every indecomposable summand of $(1_P)^G$ has
        vertex $P$.] <case:pp-normal-subgroup-vertices>],
    [
      #case[Let $N=N_G lr((P))$. For each indecomposable pp $R N$-lattice $X$ of
        vertex $P$ and source $1_P$, its Green correspondent $Y$ is a pp
        $R G$-lattice of vertex $P$ and source $1_P$. We have
        $ X^G tilde.equiv Y plus.o Y', $
        where the summands of $Y'$ have vertices properly subconjugate to $P$.
        Write $Y_N tilde.equiv X plus.o X''$. For $P <= H <= N$ we have
        $ Y_H tilde.equiv X_H plus.o (X'')_H, $
        where every indecomposable summand of $X_H$ has vertex $P$, and no
        summand of $(X'')_H$ has a vertex containing $P$ up to $H$-conjugacy.
        The vertices of the latter summands have order at most $abs(P)$; they
        need not have smaller order. If $P$ is a Sylow $p$-subgroup of $H$,
        these other vertices are properly subconjugate to $P$ in $H$.
      ] <case:pp-green-correspondence-remainders>
    ],
  )
] <lem:permutation-projective-vertices-sources>
#proof[
  Assertion~@case:pp-trivial-module-vertex was proved in
  @prop:trivial-module-sylow-vertices. For
  part~@case:pp-trivial-source-equivalence, let $M in op("Ind") R G$ be such
  that $M divides (1_H)^G$ for some $H <= G$, and let $op("vtx") M=P$. Then
  $M_P divides ((1_H)^G)_P$, so by Mackey's Formula the only summand of $M_P$ of
  vertex $P$ is $1_P$. Thus $1_P$ is a source of $M$, by
  @i:th:green-vertices-going-down.

  For part~@case:pp-normal-subgroup-vertices, assume $P ◁ G$ and let $M$ be an
  indecomposable summand of $(1_P)^G$, with vertex $D$. Then $P$ acts trivially
  on $M$, and $D <= P$ since $M$ is $(G,P)$-projective. Using the notation in
  §~@ss:block-g-algebras-trace, we may write
  $
    op("id")_M=T_(G slash P) T_(P slash D) phi "for some" phi in
    op("End")_(R D) M.
  $
  But $T_(P slash D) phi=abs(P : D) phi$ since $M$ is $P$-trivial. Therefore
  $P=D$, as desired.

  To prove part~@case:pp-green-correspondence-remainders, use the Green
  correspondence and its exclusion families in @i:eq:green-subgroup-families and
  @i:th:green-correspondence. For a representative $g$ outside $N$, the subgroup
  $P inter P^g$ is properly contained in $P$, which gives the asserted induction
  remainder. The other restriction vertices are contained in $N inter P^g$ with
  $g$ outside $N$; none contains $P$ up to $N$-conjugacy. Restricting further to
  $H$ preserves this exclusion. Finally, a summand $W$ of $X_H$ is a summand of
  $(1_P)^H$, by Mackey's Formula, since $P$ is normal in $N$.
  Part~@case:pp-normal-subgroup-vertices gives vertex $P$ for $W$. If $P$ is
  Sylow in $H$, a subgroup of order at most $abs(P)$ excluded from its conjugacy
  class must have smaller order and be properly subconjugate.

]

We next observe that the inner tensor product of pp modules is again pp, by
virtue of Mackey's Formula
$ (1_E)^G times.o (1_H)^G tilde.equiv product.co_(x) (1_(E inter H^x))^G, $
<eq:permutation-projective-tensor-mackey>
where $G=union.dot.big_(x) H x E$.

#source(896)
We denote by $P P(R G)$ the subring of the Green algebra $A(R G)$ spanned (over
$CC$) by all pp $R G$-modules. This subring is also denoted by $A(R G, "Triv")$,
the subring of trivial source modules. Note that for $H <= G$,
$op("res")_H^G P P(R G) subset.eq P P(R H)$.
#nidx("$P P(R G)$", "permutation projective RG-modules")

#proposition[
  Let $R$ be a complete d.v.r., with $R slash frak(p)=k$. Reduction mod
  $frak(p)$ gives a ring isomorphism
  $ P P(R G) tilde.equiv P P(k G). $
] <prop:permutation-projective-reduction-isomorphism>
#proof[
  We show first that for pp $R G$-lattices $M$ and $N$, the map
  $
    op("Hom")_(R G) lr((M,N)) arrow.r
    op("Hom")_(k G) lr((overline(M),overline(N)))
  $
  <eq:permutation-projective-hom-reduction>
  is surjective, where $overline(M)=M slash lr((frak(p) M))$. It suffices to
  prove this when $M=(1_E)^G$, $N=(1_H)^G$, with $E,H <= G$, and we need only
  verify that the $R$-rank of the left-hand side of
  @eq:permutation-projective-hom-reduction equals the $k$-dimension of the right
  hand side. But
  $ op("Hom")_(R G) lr((M,N)) tilde.equiv op("inv")_G M^* times.o N, $
  so it suffices to calculate the rank of
  $op("inv")_(G) [(1_E)^G times.o (1_H)^G]$. By
  @eq:permutation-projective-tensor-mackey, this rank is precisely the number of
  $(H,E)$-double cosets in $G$, since $op("inv")_G lr((1_(E inter H^x)))^G$ has
  rank $1$. This completes the proof that the map
  @eq:permutation-projective-hom-reduction is surjective.

  Now let $M$ be any pp $R G$-lattice; then, by the above, the ring homomorphism
  $op("End")_(R G) M arrow.r op("End")_(k G) overline(M)$ is surjective. By
  lifting idempotents, it follows that every direct sum decomposition of
  $overline(M)$ can be lifted to one of $M$. Further, if $X$ and $Y$ are
  summands of $M$, both of which are lifts of the summand $V$ of $overline(M)$,
  then $op("id")_V$ lifts to a pair of $R G$-maps $f:X arrow.r Y$ and
  $g:Y arrow.r X$, whose composites $f g$ and $g f$ are $1$ (mod $frak(p)$).
  Thus $f$ and $g$ are isomorphisms, by Nakayama's Lemma. It now follows that
  every pp $k G$-module lifts uniquely (up to isomorphism) to a pp $R G$-module,
  and the proof is complete.
]

We next introduce Brauer characters. For each $k G$-module $V$, we may define
its Brauer character $phi_V$ by first extending $k$ to a sufficiently large
field $k'$, and then computing the Brauer character of $G$ afforded by the
$k' G$-module $k' times.o_k V$. This character $phi_V$, which is a complex
valued function defined on $G_(p')$ (= set of $p$-regular elements of $G$),
determines the composition factors of $k' times.o_k V$, by
@i:cor:brauer-character-composition-factors. These, in turn, determine the
composition factors of $V$, by virtue of
@i:prop:grothendieck-scalar-extension-injections. In particular, if $V$ is a
projective $k G$-module, then by @i:cor:projective-modules-composition-factors
$V$ is determined up to isomorphism by its composition factors, and hence also
by its Brauer character $phi_V$. In other words, $V$ is determined by the map
$x arrow.r phi_V lr((x))$, $x in G_(p')$.

We apply this to prove: #lemma[
  Let $P$ be a normal $p$-subgroup of $N$, and let $X in op("Ind") R N$ be a pp
  module with vertex $P$. Then $P$ acts trivially on $X$, and $X$ is projective
  as
  #source(897)
  $R(N slash P)$-module. The $k(N slash P)$-module
  $overline(X)=X slash lr((frak(p) X))$ affords a Brauer character
  $phi_(overline(X))$ of the group $N slash P$, and this Brauer character
  determines $overline(X)$ (and $X$) uniquely, up to isomorphism.
] <lem:normal-vertex-permutation-projective-character>
#proof[
  The hypotheses imply that $X divides (1_P)^N$, so $X$ is $P$-trivial because
  $P ◁ N$. Further, $(1_P)^N tilde.equiv R(N slash P)$ as $(N slash P)$-modules,
  so $X$ is projective as $R(N slash P)$-module. Then $overline(X)$ determines
  $X$ by @prop:permutation-projective-reduction-isomorphism, and $overline(X)$
  is determined up to isomorphism by $phi_(overline(X))$.
]

Now let $cal(H)'$ be the set of $p$-hypo-elementary subgroups of $G$, defined as
the set of all subgroups $H <= G$ with the property that $H slash O_p lr((H))$
is a cyclic $p'$-group, where $O_p lr((H))$ denotes the largest normal
$p$-subgroup of $H$. By Schur's Theorem @i:th:schur-zassenhaus, each
$p$-hypo-elementary subgroup $H$ can be expressed as a semidirect product:
$ H=P times.r C, $
with $P=O_p lr((H))$ and $C$ a cyclic $p'$-subgroup. Note that $C$ is not
uniquely determined, although it is always true that $C tilde.equiv H slash P$.
(See also §~@ss:conlon-induction.)

For each $H in cal(H)'$ and each $c in H slash P$, we shall define a nonzero
$CC$-algebra homomorphism (called a _species_)
$ s_(H,c):P P(k G) arrow.r CC $
by defining the map on pp modules and then extending linearly. Specifically,
given any pp $k G$-module $V$, we write
$ V_H=V' plus.o V'', $ <eq:permutation-projective-normal-vertex-part>
where each indecomposable summand of $V'$ has vertex $P$, and each summand of
$V''$ has vertex $<P$. (Note that the vertex of any summand of $V_H$ is
necessarily $<=P$.) Then both $V'$ and $V''$ are pp modules, since $V_H$ is a pp
module. By @lem:normal-vertex-permutation-projective-character, $V'$ is
$P$-trivial, and is projective as $k(H slash P)$-module, affording a Brauer
character $phi_(V')$ of $H slash P$. Let $c$ be any element of the cyclic
$p'$-group $H slash P$ (we will later assume $c$ generates $H slash P$), and
define
$ s_(H,c)[V]=phi_(V') lr((c)). $ <eq:permutation-projective-species>
It follows readily that $s_(H,c)$, extended linearly, is a $CC$-algebra
homomorphism from $P P(k G)$ to $CC$.

#lemma[
  Keep the above notation.
  #case-list(
    [
      #case[$s_(H,c)$ is not the zero map.]
      <case:permutation-projective-species-nonzero>],
    [
      #case[Assume that $k$ is a splitting field for $G$ and its subgroups, and
        let $c,c' in H slash P$. Then $s_(H,c)=s_(H,c')$ if and only if $c$ and
        $c'$ are conjugate in $N slash P$, where $N=N_G lr((P))$.]
      <case:permutation-projective-species-conjugacy>
    ],
  )
] <lem:permutation-projective-species-separation>
#source(898)
#proof[
  Let $X$ range over the indecomposable $k N$-modules of vertex $P$ and source
  $1_P$, or equivalently, over all indecomposable projective
  $k(N slash P)$-modules. By @lem:permutation-projective-vertices-sources,
  part~@case:pp-green-correspondence-remainders, for each $X$ we can find an
  indecomposable $k G$-module $V$ of vertex $P$ and source $1_P$, such that
  $ V_H=X_H plus.o V'', $
  where each indecomposable summand of $X_H$ has vertex $P$, and where the
  summands of $V''$ have smaller vertex. Then by definition of $s_(H,c)$, we
  have
  $ s_(H,c)[V]=phi_X lr((c)), $
  where $X$ is viewed as a $k(N slash P)$-module affording the Brauer character
  $phi_X$. By @i:th:cartan-map-cokernel-p-primary, the trivial character of
  $N slash P$ is expressible as a $CC$-linear combination of the restrictions
  $(phi_X)|_H$. Hence it is impossible that $phi_X lr((c))=0$ for all $X$, which
  proves part~@case:permutation-projective-species-nonzero. Further, if $k$ is a
  splitting field, the Brauer characters ${phi_X}$ form a $CC$-basis for the
  space of $CC$-valued class functions on the $p$-regular elements of
  $N slash P$, which implies part~@case:permutation-projective-species-conjugacy
  and completes the proof.
]

#remark(numbered: true)[
  Dropping the hypothesis that $k$ be a splitting field for $G$, we can still
  decide whether $s_(H,c)=s_(H,c')$, where $c,c'$ are $p'$-elements of
  $N slash P$. We partition $N slash P$ into $k$-conjugacy classes as in
  §~@i:ss:cartan-brauer-general-case. Then by the Witt-Berman Theorem
  @i:th:modular-field-character-conjugacy-classes and Theorem
  @i:th:cartan-map-cokernel-p-primary, the Brauer characters ${phi_X}$ occurring
  above form a $CC$-basis for the space of complex-valued functions that are
  constant on the $p$-regular $k$-conjugacy classes of $N slash P$. Hence
  $s_(H,c)=s_(H,c')$ if and only if $c$ and $c'$ belong to the same
  $k$-conjugacy class of $N slash P$. In particular, in this situation, the
  cyclic subgroups $chevron.l c
  chevron.r$ and $chevron.l c' chevron.r$ must be conjugate in $N slash P$.
] <rem:permutation-projective-species-field-conjugacy>

We have now constructed a family ${s_(H,c)}$ of species of $P P(k G)$. We
emphasize that if $P=O_p lr((H))$, then $s_(H,c)$ vanishes on each
indecomposable pp $k G$-module $V$ of vertex $<P$, and is nonzero at some $V$ of
vertex $P$. It follows that if $s_(H,c)=s_(H',c')$, then $O_p lr((H')) =_G P$.
Replacing $H'$ by a conjugate subgroup, we may thus assume that
$O_p lr((H'))=P$, and therefore $H' <= N=N_G lr((P))$. It follows that $c$ and
$c'$ must be $k$-conjugate elements of $N slash P$, by the above Remark
@rem:permutation-projective-species-field-conjugacy, and the cyclic groups
$chevron.l c chevron.r$, $chevron.l c' chevron.r$ must be conjugate in
$N slash P$. Further, if $k$ is a splitting field, then $c$ and $c'$ are
conjugate in $N slash P$.

Whether or not $k$ is a splitting field, let $cal(S)={s_(H,c)}$ be the set of
species obtained by letting $O_p lr((H))$ range over a full set of nonconjugate
$p$-subgroups of $G$, and letting $c$ range over nonconjugate $p'$-elements of
$N_G lr((P)) slash P$ such that $H slash P=chevron.l c chevron.r$. We now prove:

#theorem[
  The above-defined set $cal(S)$ of species of $P P(k G)$ separates elements of
  $P P(k G)$, that is, if $xi,eta in P P(k G)$ are such that $s(xi)=s(eta)$ for
  all $s in cal(S)$, then $xi=eta$.
] <th:permutation-projective-species-detection>
#proof[
  It suffices to prove the result when $eta=0$, so let
  $xi=sum_(i=1)^t alpha_(i) [M_i] in P P(k G)$,
  #source(899)
  where $alpha_i in CC$ are nonzero, and the ${M_i}$ are nonisomorphic
  indecomposable pp $k G$-modules. We assume $t >= 1$, and that $s(xi)=0$ for
  all $s in cal(S)$, and try to obtain a contradiction.

  Choose $P <= G$ maximal among the set of vertices of the ${M_i}$, and to fix
  the notation, suppose that $M_1$ has vertex $P$. Set $N=N_G lr((P))$, and
  write
  $ (M_i)_N=X_i plus.o Y_i, quad 1 <= i <= t, $
  where the indecomposable summands of $X_i$ have vertex $P$, and those of $Y_i$
  do not. From the choice of $P$, the vertices of the summands of $Y_i$ do not
  contain $P$. Further, $X_1 != 0$ since $M_1$ has vertex $P$.

  Now let $c in N slash P$ range over a full set of nonconjugate $p'$-elements
  of $N slash P$. For each $c$, choose $H in cal(H)'$ so that $O_p lr((H))=P$
  and $H slash P=chevron.l c chevron.r$. Then we obtain a species
  $s_(H,c) in cal(S)$. Now the vertex of each indecomposable summand of
  $(Y_i)_H$ is $<P$. The proof of @lem:permutation-projective-vertices-sources,
  part~@case:pp-green-correspondence-remainders, then gives
  $ s_(H,c)[M_i]=phi_(X_i) lr((c)), quad 1 <= i <= t, $
  where now $X_i$ is viewed as a projective $k(N slash P)$-module, and affords
  the Brauer character $phi_(X_i)$ of $N slash P$.

  From the assumption that $s(xi)=0$ for all $s in cal(S)$, we thus conclude
  that
  $ sum_(i=1)^t alpha_i phi_(X_i) lr((c))=0 $
  for each $p'$-element $c in N slash P$. However, the Brauer characters
  associated with nonisomorphic P.I.M.'s of $N slash P$ are linearly independent
  over $CC$, by @i:th:projective-characters-supported-p-regular and
  @i:prop:cartan-triangle-injectivity-cokernel. It follows that for some $i>1$,
  $X_i$ and $X_1$ have a common indecomposable summand. By
  §~@i:ss:green-correspondence, the Green correspondent of each indecomposable
  summand of $X_1$ (of vertex $P$) is an indecomposable $k G$-module of vertex
  $P$, and must therefore coincide with $M_1$. It follows that
  $M_i tilde.equiv M_1$, which is the desired contradiction, and completes the
  proof.
]

#corollary[
  Let $M,N$ be pp $R G$-modules. Then $M tilde.equiv N$ if and only if
  $M_H tilde.equiv N_H$ for all $H in cal(H)'$.
] <cor:permutation-projective-hypoelementary-detection>
#proof[
  For an $R G$-lattice $M$, let $overline(M)=M slash lr((frak(p) M))$. Since
  $P P(R G) tilde.equiv P P(k G)$ via reduction mod $frak(p)$, we need only show
  that if $overline(M)_H tilde.equiv overline(N)_H$ for all $H in cal(H)'$, then
  $overline(M) tilde.equiv overline(N)$. But this is clear from
  @th:permutation-projective-species-detection.
]

#corollary[
  $P P(R G)$ is a f.d. semisimple $CC$-algebra. Letting $s_i$ range over the
  distinct species in $cal(S)$, there exist primitive orthogonal idempotents
  ${e_i}$ in $P P(R G)$, with sum $1$, such that $s_i lr((e_j))=delta_(i j)$.
] <cor:permutation-projective-algebra-semisimple>
#proof[
  The commutative $CC$-algebra $P P(R G)$ is f.d./$CC$, since it is spanned by
  the indecomposable components of $(1_H)^G$, with $H <= G$. The algebra has no
  nonzero
  #source(900)
  nilpotent elements, since if $xi in P P(R G)$ is such that $xi^n=0$, then
  $s(xi)^n=0$ for each $s in cal(S)$, and therefore $s(xi)=0$ for each $s$. The
  assertions of the corollary are now clear.
]

We may use these ideas to give another proof of the Conlon Induction Theorem
@th:conlon-permutation-induction, and indeed what follows is essentially the
same as Conlon's original proof. Starting with an arbitrary group $G$, let
$Omega(G)$ be its Burnside ring, defined as in §~@ss:burnside-rings, and let
$CC times.o_ZZ Omega(G)$ be its Burnside algebra. Let
$ cal(T)={H_1,...,H_m} $
be a full set of nonconjugate subgroups of $G$. By
@cor:burnside-transitive-basis we have
$ CC times.o_ZZ Omega(G)=plus.o.big_i CC [G slash H_i]. $
By @prop:burnside-mark-full-lattice, there is a $CC$-algebra isomorphism
$ phi:CC times.o_ZZ Omega(G) tilde.equiv CC^((m)), $
given by
$ [T] arrow.r (abs(op("inv")_(H_1) T),...,abs(op("inv")_(H_m) T)) $
for each $G$-set $T$. We may therefore find a set of orthogonal primitive
idempotents ${epsilon_H:H in cal(T)}$ in $CC times.o Omega(G)$, such that
$
  1=sum_(H in cal(T)) epsilon_H, quad "and" quad
  phi(epsilon_H)=(0,...,1,0,...,0) in CC^((m)),
$
where the $m$-tuple has entry $1$ at the $H$-th place, and zeros elsewhere. In
fact, the discussion in §~@ss:burnside-rings shows that
$epsilon_H in QQ times.o_ZZ Omega(G)$ for each $H in cal(T)$. Let us write
$ epsilon_H=sum_(i=1)^m alpha_(i) [G slash H_i], quad alpha_i in QQ. $
If $alpha_i != 0$ for some $H_i$ not contained in a conjugate of $H$, choose a
maximal such $H_i$ (relative to $<=_G$). By @eq:burnside-mark-subconjugacy, it
follows that the $i$-th component of $phi(epsilon_H)$ is nonzero, which is
impossible. Therefore
$ epsilon_H=sum_(H_i <=_G H) alpha_(i) [G slash H_i] $
<eq:burnside-primitive-idempotent-subgroup-support>
for some rational coefficients ${alpha_i}$.

Now let $R$ be a complete d.v.r. and consider the algebra $P P(R G)$ of pp
$R G$-lattices. This is a $CC$-subalgebra of the representation algebra
$A(R G)$, and there is a $CC$-algebra homomorphism
$
  CC times.o_ZZ Omega(G) arrow.r P P(R G), quad
  "given by" [T] arrow.r [R[T]]
$
for each $G$-set $T$, where $R[T]$ is the permutation module with the elements
of $T$ as $R$-basis. We shall use the idempotents ${epsilon_H:H in cal(T)}$ in
$CC times.o Omega(G)$ to construct idempotents in $P P(R G)$. It is clear that
for each $epsilon_H$, its image $e_H in P P(R G)$ is either idempotent or $0$,
and that $1=sum e_H$ in $P P(R G)$.

#source(901)
Let $cal(S)_0$ consist of the distinct species in the collection ${s_(H,c)}$,
where $H in cal(H)'$ ranges over all $p$-hypo-elementary subgroups of $G$ (up to
conjugacy), and $H slash O_p lr((H))=chevron.l c
chevron.r$. Then there is an isomorphism of $CC$-algebras
$
  psi:P P(R G) tilde.equiv CC^((n)), quad
  "where" n=abs(cal(S)_0), quad cal(S)_0={s_1,...,s_n},
$
given by
$ [M] arrow.r (s_(1)[M],...,s_(n)[M]) $
for each pp $R G$-lattice $M$. We show at once:

#lemma[
  Keeping the above notation, there is a commutative diagram

  #representation-species-mark-square()

  where for $f in CC^((m))$, $(rho f)(s_(H,c))=f(H)$, $H in cal(H)'$. Further,
  for each $H in cal(T)$, let the idempotent
  $epsilon_H in CC times.o_ZZ Omega(G)$ have image $e_H in P P(R G)$. Then $e_H$
  is a nonzero idempotent if and only if $H in cal(H)'$.
] <lem:burnside-permutation-species-square>
#proof[
  To prove the diagram commutative, we must show that for each $G$-set $T$,
  $ rho phi[T]=psi(R[T]), $
  that is, for each $H in cal(H)'$ and
  $H slash O_p lr((H))=chevron.l c chevron.r$, we have
  $ s_(H,c) lr((R[T]))=abs(op("inv")_H T). $
  It suffices to check this for $T=G slash D$, a transitive $G$-set, where
  $D <= G$. Let $M=R[T]$, so $M tilde.equiv (R_D)^G$, where $R_D$ is the
  $D$-trivial module $R$. Then
  $
    M_H=plus.o.big_(x) (R_(D^x inter H))^H, quad
    "where" G=union.dot.big_(x) D x H.
  $
  To compute $s_(H,c) lr((M))$, we need to find the indecomposable summands of
  $M_H$ of vertex $P$. The sum of these is precisely
  $ M'=plus.o.big (R_(D^x inter H))^H, quad "where" D^x inter H >= P, $
  #source(902)
  and then
  $
    s_(H,c) lr((M)) & = "Brauer character of" M' "evaluated at" c. \
                    & = "trace of" c "acting on" M'.
  $
  But if $D^x inter H<H$, then the trace of $c$ on $(R_(D^x inter H))^H$ is $0$,
  and therefore
  $
    s_(H,c) lr((M)) = "number of double coset representatives" x
    "such that" D^x >= H.
  $
  But then $s_(H,c) lr((M))=abs(op("inv")_H G slash D)$ by
  @prop:g-set-maps-fixed-points, which completes the proof of the first
  assertion of the lemma. The second follows at once from the first.
]

We remark that for $H in cal(H)'$, $phi(epsilon_H)$ is the $m$-tuple
$(0,...,1,0,...,0)$, with $1$ at position $H$. It follows that
$ psi(e_H)=(0,...,0,1,...,1,0,...,0) in CC^((n)) $
with $1$'s occurring at entries corresponding to the distinct species of
$P P(R G)$ of the form $s_(H,c)$. Thus we obtain for $H in cal(H)'$:
$ e_H=sum_c e_(H,c), $ <eq:permutation-projective-idempotent-species-sum>
the sum extending over generators $c$ of $H slash O_p lr((H))$ for which the
species $s_(H,c)$ are distinct from one another. This gives a decomposition of
$e_H$ into primitive orthogonal idempotents in $P P(R G)$. Further, from
@eq:burnside-primitive-idempotent-subgroup-support we obtain a formula
$ e_H=sum_(H_i <=_G H) alpha_(i) [(1_(H_i))^G], $
<eq:permutation-projective-idempotent-induction-expansion>
for some $alpha_i in QQ$ and subgroups $H_i$ of $H$. Each term in $e_H$ is
therefore $(G,P)$-projective, where $P=O_p lr((H))$. Since $s_(H,c) lr((e_H))=1$
for each $c$, it follows that $e_H$ contains at least one term with vertex $P$.

As a first consequence of the preceding results, we obtain a new proof of the
following theorem (compare with @th:conlon-permutation-induction): #theorem(
  name: "Conlon's Induction Theorem",
)[
  There exist rational numbers ${alpha_H:H in cal(H)'}$ such that
  $ [R_G]=sum_(H in cal(H)') alpha_(H) [(R_H)^G] "in" P P(R G). $
] <th:conlon-p-permutation-induction>
#idx("Conlon's Induction Theorem", target: [@th:conlon-p-permutation-induction])
#proof[
  From the formula
  $ 1=sum_(H in cal(T)) epsilon_H "in" CC times.o_ZZ Omega(G), $
  #source(903)
  we obtain the equality
  $ 1=sum_(H in cal(H)') e_H "in" P P(R G), $
  with one summand $e_H$ for each conjugacy class of groups in $cal(H)'$. But we
  may write $e_H$ as a $QQ$-linear combination of permutation modules, by
  @eq:permutation-projective-idempotent-induction-expansion. The rest of the
  argument is the same as in Step 1 of the proof of
  @th:conlon-permutation-induction.
]

By @cor:frobenius-induction-annihilators, we obtain: #corollary[
  Let $cal(H)'$ be the set of $p$-hypo-elementary subgroups of $G$. Then
  $
    P P(R G)=sum_(H in cal(H)') {P P(R H)}^G, quad
    A(R G)=sum_(H in cal(H)') {A(R H)}^G.
  $
  Further, if $x in A(R G)$ (or $x in P P(R G)$) is such that $x_H=0$ for all
  $H in cal(H)'$, then $x=0$.
] <cor:representation-hypoelementary-induction-detection>

Combining the above results with formula
@eq:permutation-projective-idempotent-induction-expansion, we obtain
decompositions of $1 in A(R G)$ into orthogonal idempotents:
$ 1=sum_H e_H=sum_(H,c) e_(H,c), $
where $H$ ranges over a full set of nonconjugate $p$-hypo-elementary subgroups
of $G$, and for each $H$, $c$ ranges over generators of $H slash O_p lr((H))$
for which the species $s_(H,c)$ of $P P(R G)$ are distinct from one another.
Consequently we obtain
$ A(R G)=plus.o.big_H A(R G) e_H=plus.o.big_(H,c) A(R G) e_(H,c). $
<eq:representation-hypoelementary-idempotent-decomposition>

Our next aim is to relate the above decomposition of $A(R G)$ to the ideals
$A(G,H)$ of $A(R G)$, where, by definition $A(G,H)$ is spanned over $CC$ by the
$(G,H)$-projective $R G$-modules. We remark that if $P$ is a Sylow $p$-subgroup
of $H$, then by @i:prop:relative-projectivity-properties an $R G$-module is
$(G,H)$-projective if and only if it is $(G,P)$-projective. Hence
$A(G,H)=A(G,P)$, so in studying the ideals $A(G,H)$, there is no loss of
generality in assuming that $H$ is a $p$-group.

We begin with some simple remarks on ideals and rings. Let $A$ be a commutative
ring with $1$, and let $I$ be an ideal of $A$. Write $I divides A$ to indicate
that $I$ is an ideal direct summand of $A$, that is, $A=I plus.o I'$ for some
ideal $I'$. It will be convenient to view $I$ as a ring, possibly without
identity element. We leave it as exercise for the reader to prove:

#lemma[
  Let $A$ be a commutative ring with $1$, and let $I$ be an ideal of $A$. Then
  we have:
  $
    I divides A <=> I "has an identity element" e <=>
    I=A e "for some idempotent" e.
  $
  In this case, $A$ decomposes uniquely as $A=I plus.o A(1-e)$. Further,
  $I divides J$ for each bigger ideal $J$.

  #source(904)
  Next, assume that $I divides A$, and that $I subset J subset A$. If
  $J slash I$ has an identity element, then $J divides A$, and $J=I plus.o L$
  for some unique ideal $L$ of $A$. We have $L divides A$, and
  $J slash I tilde.equiv L$.
] <lem:ideal-direct-summand-idempotent-unit>

Now let $P$ be a $p$-subgroup of $G$, and denote by $a(G,P)$ the ideal of
$a(R G)$ spanned by $(G,P)$-projective $R G$-lattices. We need next a result of
Green~@bib:Green1964, which reduces the study of $a(G,P)$ to the case where
$P ◁ G$. We set
$
  a'(G,P)=sum_(D<P) a(G,D), quad
  A'(G,P)=CC times.o_ZZ a'(G,P).
$
Then we have, as a direct consequence of
@i:cor:green-correspondence-fixed-vertex\:

#theorem(name: "Green's Transfer Theorem")[
  Let $P$ be a $p$-subgroup of $G$, and let $N_G lr((P)) <= H <= G$. There is an
  isomorphism of rings
  $ a(G,P) slash a'(G,P) tilde.equiv a(H,P) slash a'(H,P), $
  induced by the Green correspondence in
  @i:cor:green-correspondence-fixed-vertex. Specifically, the left-hand side is
  spanned by all $M in op("Ind") R G$ with vertex $P$, and the isomorphism is
  given by
  $ [M]+a'(G,P) arrow.r [N]+a'(H,P), $
  where $N in op("Ind") R H$ is the Green correspondent of $M$. More precisely,
  retain from $M_H$ the summands of vertex $H$-conjugate to $P$; their class
  modulo $a'(H,P)$ is $[N]+a'(H,P)$. Also
  $ [N^G]=[M]+"an element of" a'(G,P). $
  The isomorphism preserves the property of being permutation projective.
] <th:green-relative-projective-transfer>
#proof[
  The Green correspondence gives the asserted mutually inverse additive maps on
  the bases of indecomposable classes with vertex conjugate to $P$. Its
  induction remainder has proper-$P$ vertices, whereas other summands of raw
  restriction are only excluded from the $H$-conjugacy class of $P$.
  #ed-note[
    Raw restriction may have another vertex of the same order. Over $FF_2$, take
    $G=chevron.l r,s: r^4=s^2=1,s r s=r^(-1) chevron.r$,
    $P=chevron.l s chevron.r$, and $H=N_G lr((P))=chevron.l r^2,s chevron.r$.
    The restriction of $FF_2[G slash P]$ has a second transitive summand with
    vertex $chevron.l r^2 s chevron.r$, of the same order as $P$. Thus the Green
    component, rather than the whole restriction, is required.
  ]
  To check products, use the vertex bound for tensor products: a vertex of a
  tensor summand is contained in an intersection of conjugates of vertices of
  its factors. All restriction summands here have vertices of order at most
  $abs(P)$. Such an intersection can have vertex $H$-conjugate to $P$ only when
  both factor vertices are themselves $H$-conjugate to $P$. The terms discarded
  by the Green-component projection therefore contribute no vertex-$P$
  component. Terms with proper-$P$ vertices belong to $a'(H,P)$. Since
  restriction preserves tensor products, the projected map is multiplicative
  modulo this ideal. Its additive inverse, induced by induction, is consequently
  multiplicative as well. This proves the ring isomorphism. Trivial sources are
  preserved by the Green correspondence, giving the final assertion.
]
#idx(
  "Green's Transfer Theorem",
  target: [@th:green-relative-projective-transfer],
)

We conclude the subsection with two results that will be applied in
§~@ss:representation-algebra-semisimplicity. #theorem(name: "Conlon's Theorem")[
  Let $R$ be either a complete d.v.r. with $R slash frak(p)=k$, or else $R=k$,
  where $k$ is a field of characteristic $p>0$. Let $P$ be a $p$-subgroup of
  $G$, and define $A(G)=A(R G)$, $A(G,P)$, and $A'(G,P)$ as above.
  #case-list(
    [
      #case[$A(G,P)$ is an ideal direct summand of $A(G)$, with an idempotent
        generator $e_P$ that belongs to $P P(R G)$.]
      <case:conlon-relative-projective-idempotent>],
    [
      #case[There is a uniquely determined ideal direct summand $A''(G,P)$ of
        $A(G)$, such that
        $ A(G,P)=A'(G,P) plus.o A''(G,P). $
      ] <case:conlon-vertex-ideal-complement>],
    [
      #case[We have
        $ A(G,P)=plus.o.big_(D <= P) A''(G,D) $
        where $D$ ranges over a cross section of the $G$-conjugacy classes of
        subgroups of $P$.
      ] <case:conlon-vertex-ideal-decomposition>
    ],
  )
] <th:conlon-relative-projective-ideal-decomposition>
#idx(
  "Conlon's Theorem",
  target: [@th:conlon-relative-projective-ideal-decomposition],
)
#source(905)
#proof[
  #case-list(
    prefix: "Step ",
    numbering: "1.",
    [
      #case[
        Assume that $P ◁ G$, and that $R=k$. Denote by $i(G,P)$ the ideal of
        $a(G)$ spanned (over $ZZ$) by all expressions $[X]-[X']-[X'']$ arising
        from ses's of $k G$-modules
        $ 0 arrow.r X' arrow.r X arrow.r X'' arrow.r 0 $
        which are $P$-split (see §~@ss:representation-ring-preliminaries), and
        let $I(G,P)=CC times.o_ZZ i(G,P)$. In the extreme case where $P=1$, the
        quotient $a(G) slash i(G,1)$ is precisely the Grothendieck ring
        $G_0 lr((k G))$ defined in §~@i:ss:reduction-decomposition-map. Further,
        $a(G,1)$ is the ideal of $a(G)$ spanned by projective $k G$-modules,
        i.e., $a(G,1)=K_0 lr((k G))$. The map
        $ K_0 lr((k G))=a(G,1) arrow.r a(G) slash i(G,1)=G_0 lr((k G)) $
        is just the Cartan homomorphism $c$. By
        @i:th:cartan-map-cokernel-p-primary, $c$ is an isomorphism mod torsion,
        so there are isomorphisms
        $
          CC times.o_ZZ a(G,1) tilde.equiv A(G) slash I(G,1) tilde.equiv
          CC times.o_ZZ G_0 lr((k G)).
        $
        We apply the above with $G$ replaced by $overline(G)$, where
        $overline(G)=G slash P$. It follows that there exists an element
        $y_0 in A(overline(G),1)$ whose image (under the Cartan map) is the
        identity element of $A(overline(G)) slash I(overline(G),1)$, and thus
        $1-y_0 in I(overline(G),1)$. By inflation, each $overline(G)$-module
        becomes a $G$-module on which $P$ acts trivially. It follows that the
        map $op("inf"):A(overline(G)) arrow.r A(G)$ maps $A(overline(G),1)$ into
        $A(G,P)$, and $I(overline(G),1)$ into $I(G,P)$. Letting
        $y=op("inf") y_0$, we now have
        $ y in A(G,P), quad 1-y in I(G,P). $
        But $A(G,P) dot I(G,P)=0$ by @rem:relative-split-relation-annihilation,
        so $y(1-y)=0$ and $y$ is an idempotent. Further, since
        $ k overline(G) tilde.equiv (k_P)^G, $
        we have $y in P P(k G)$. Thus we obtain
        $ A(G)=A(G,P) plus.o I(G,P), $
        and the idempotent generator $y$ of $A(G,P)$ lies in $P P(k G)$, so
        part~@case:conlon-relative-projective-idempotent holds in this case.
      ] <case:conlon-normal-vertex-field-proof>],
    [
      #case[
        Continue to assume that $P ◁ G$, and let $R$ be a complete d.v.r. Write
        $Q=G slash P$ and $frak(p)=pi R$. The ordinary field Cartan theorem
        @i:th:cartan-map-cokernel-p-primary gives a rational virtual projective
        $k Q$-module $y$ whose image in $QQ times.o G_0 lr((k Q))$ is $[k]$.
        Lift its projective terms to $R Q$ by idempotent lifting, and inflate
        their rational linear combination to $G$, obtaining
        $e in P P(R G) inter A(G,P)$. We show that $e$ acts as the identity on
        every relatively $P$-projective lattice.
        #ed-note[
          The fixed reduction used in the original appeal to Maranda's Theorem
          @i:th:maranda-lattice-isomorphism need not distinguish all lattices at
          the present scope. For $R=FF_2[[t]]$, $G=C_2$, let its generator act
          on $R^2$ by $I+t^n J_2$, where $J_2$ is the nonzero square-zero Jordan
          block. Its endomorphism ring $R I+R J_2$ is local, so the lattice is
          indecomposable; for $n >= m$ its reduction modulo $t^m$ is two trivial
          copies.
        ]

        Fix an indecomposable $R P$-lattice $L$, and set $N=op("ind")_P^G L$,
        $B=op("End")_(R G) lr((N))^("op")$,
        $C_0=op("End")_(R P) lr((N_P))^("op")$, and $J=B inter op("rad") C_0$.
        Restriction embeds $B$ in $C_0$. For $j in J$, the inverse in $C_0$ of
        $1-b j$, $b in B$, is again $G$-equivariant. Hence
        $J subset.eq op("rad") B$, and also $pi B subset.eq J$. The category of
        summands of finite sums of $N$ is equivalent, under
        $op("Hom")_(R G) lr((N,-))$, to finite projective left $B$-modules.

        Set $E_L=op("End")_(R P) lr((L))^("op")$ and
        $D=E_L slash lr((op("rad") E_L))$. Completeness makes $E_L$ local, so
        $D$ is a finite-dimensional division $k$-algebra. If $t_q$ are
        representatives of $q in Q$, let $L_q$ be the conjugate on which
        $h in P$ acts as $t_q^(-1) h t_q$, and put
        $I={q in Q:L_q tilde.equiv L}$. Frobenius reciprocity determines each
        endomorphism of $N$ from its maps from $L$ to the copies $L_q$ in $N_P$.
        Components between nonisomorphic indecomposables lie in the categorical
        radical; for $q in I$, their quotient is one copy of $D$. A chosen
        intertwiner for $q in I$ extends to an invertible homogeneous
        endomorphism of $N$. These components lift separately, without averaging
        over $I$. Thus
        $ B slash J tilde.equiv E=D ast I, $
        a crossed product with homogeneous units $u_q$, satisfying
        $u_q d=sigma_q lr((d)) u_q$ and $u_q u_r=c(q,r) u_(q r)$. The opposite
        convention makes the homogeneous degree $q r$.

        #source(906)
        Since $J subset.eq op("rad") B$ and $pi B subset.eq J$, reduction
        induces an isomorphism between the split $K_0$ groups of finite
        projective $B$-modules and finite projective $E$-modules. Indeed,
        $J slash pi B$ is nilpotent in $B slash pi B$; idempotents lift through
        this quotient and then through the complete $pi$-adic filtration. The
        simple types and projective covers are unchanged. Neither
        $J=op("rad") B$ nor semisimplicity of $E$ is required.

        For any $R Q$-lattice $W$, the Frobenius isomorphism
        $W times.o_R N tilde.equiv N^(op("rank")_R W)$ is given by
        $w times.o (t times.o l) arrow.r (t times.o l) times.o t^(-1) w$, with
        $G$ acting only on $N$ in the target. Tensoring a homogeneous
        endomorphism of degree $q$ consequently gives the matrix factor
        $rho_W lr((q^(-1)))$. Radical components remain radical, so this functor
        descends through $B arrow.r E$ and depends only on $overline(W)|_I$. It
        is the diagonal tensor action on left $E$-projectives: on the free left
        module, right multiplication by $u_q$ has exactly the same inverse
        matrix factor.

        For a $k I$-module $V$, homogeneous untwisting gives
        $
          V times.o_k E tilde.equiv E times.o_k V, quad
          v times.o d u_q arrow.r d u_q times.o q^(-1) v,
        $
        where $E$ acts only on its first factor on the right. The crossed
        product relations verify this map: under $u_r$ the vector becomes
        $(r q)^(-1) r v=q^(-1) v$, with the same coefficient
        $sigma_r lr((d)) c(r,q)$ on both sides. Hence tensoring any
        $E$-projective with $V$ remains projective. A short exact sequence of
        $k I$-modules therefore gives a split sequence after tensoring with an
        $E$-projective. The action on projective $K_0 lr((E))$ factors through
        the ordinary group $G_0 lr((k I))$.

        The restriction to $I$ of the Cartan image of $y$ is $[k]$. Consequently
        $e$ acts as the identity on every projective $E$-module, and the split
        $K_0$ isomorphism gives $e[M]=[M]$ for every $M$ in the category
        generated by $N$. By Krull–Schmidt, each indecomposable relatively
        $P$-projective lattice is a summand of such an $N$ for some
        indecomposable $L$. Thus $e$ acts as the identity on $A(G,P)$. Since it
        belongs to that ideal, $e^2=e$ and $A(G,P)=e A(G)$. We obtain the
        decomposition required in
        part~@case:conlon-relative-projective-idempotent:
        $ A(G)=e A(G) plus.o (1-e) A(G). $
      ] <case:conlon-normal-vertex-dvr-proof>],
    [
      #case[
        We have now established part~@case:conlon-relative-projective-idempotent
        for the case $P ◁ G$, and proceed to prove the theorem by induction on
        $abs(P)$, noting that it holds for $P=1$ by the previous steps. Let
        $abs(P)>1$, and assume the theorem holds for $p$-groups $D<P$. Then for
        each such $D$, we have (choosing one $D$ from each class of
        $G$-conjugates):
        $
          A(G,D)=A(G) i_D, quad A(G,D)=plus.o.big_(E <= D) A''(G,E), quad
          i_D in P P(R G).
        $
        Now set
        $ e=1-product_(D<P) (1-i_D). $
        Then $e$ acts as $1$ on $A'(G,P)$, and $e in P P(R G)$. Further,
        $e != 0$ since $e$ acts as $1$ on $A(G,1)$, so $e$ is an idempotent.
        Therefore part~@case:conlon-vertex-ideal-complement holds with
        $A''(G,P)=A(G,P)(1-e)$.

        We now use the ring isomorphism in
        @th:green-relative-projective-transfer, with $H=N_G lr((P))$, to obtain:
        $
          A(N,P) slash A'(N,P) tilde.equiv A(G,P) slash A'(G,P)
          tilde.equiv A''(G,P).
        $
        By the previous steps, $A(N,P) slash A'(N,P)$ has an identity element,
        namely, the idempotent generator of $A(N,P)$. It follows from
        @lem:ideal-direct-summand-idempotent-unit that $A''(G,P)$ has an
        idempotent generator in $P P(k G)$, which establishes both
        parts~@case:conlon-relative-projective-idempotent and
        @case:conlon-vertex-ideal-complement. Assertion
        @case:conlon-vertex-ideal-decomposition follows from the fact that
        $A''(G,P)$ has as basis
        ${[M]+A'(G,P):M in op("Ind") R G, "vertex" M=P}$. This completes the
        proof of the theorem.
      ] <case:conlon-general-vertex-proof>
    ],
  )
]

The above proof shows that for each $p$-subgroup $P <= G$, there exist
idempotents $i_P$, $i'_P$, and $i''_P in P P(k G)$, such that
$
  A(G,P)=A(G) i_P, quad A'(G,P)=A(G) i'_P, quad
  A''(G,P)=A(G) i''_P,
$ <eq:conlon-relative-vertex-idempotent-generators>
with $i_P=i'_P+i''_P$, $i'_P i''_P=0$. Next, we may express those idempotents in
terms of the primitive idempotents ${e_(H,c)}$ of $P P(k G)$. Clearly, $i_P$ is
the sum (over all pairs $H,c$ yielding distinct species of $P P(k G)$) of those
$e_(H,c)$ that lie in $A(G,P)$. The discussion preceding
@th:conlon-p-permutation-induction shows that $e_(H,c) in A(G,P)$ if and only if
$O_p lr((H)) <= P$. Therefore we
#source(907)
obtain
$
  i_P=sum_(H,c \ O_p lr((H)) <= P) e_(H,c), quad
  i'_P=sum_(H,c \ O_p lr((H)) < P) e_(H,c), quad
  i''_P=sum_(H,c \ O_p lr((H)) = P) e_(H,c).
$
<eq:conlon-vertex-species-idempotent-sums>
Note that by @eq:permutation-projective-idempotent-species-sum we may also write
$
  i_P=sum_(O_p lr((H)) <= P) e_H, quad
  i'_P=sum_(O_p lr((H)) < P) e_H, quad
  i''_P=sum_(O_p lr((H)) = P) e_H.
$
<eq:conlon-vertex-hypoelementary-idempotent-sums>
In view of formula @eq:permutation-projective-idempotent-induction-expansion, we
may write
$ i''_P=sum_j beta_(j) [(1_(H_j))^G], quad beta_j in QQ, $
<eq:conlon-vertex-idempotent-rational-induction>
where the $H_j$ are $p$-hypo-elementary subgroups of $G$ such that
$O_p lr((H_j)) <= P$. Using this, we prove:

#proposition(title: [Conlon])[
  Let $P$ be a $p$-subgroup of $G$, and let $cal(H)^*$ be the set of
  $p$-hypo-elementary subgroups $H$ of $G$ for which $O_p lr((H))=P$. Then there
  is a monomorphism of $CC$-algebras
  $ A''(G,P) arrow.r product_(H in cal(H)^*) A''(H,P). $
] <prop:conlon-vertex-hypoelementary-restriction>
#proof[
  For $H in cal(H)^*$, we identify $A''(H,P)$ with $A(H,P) slash A'(H,P)$, and
  define the map $A''(G,P) arrow.r A''(H,P)$ via restriction from $G$ to $H$.
  Now let $xi in A''(G,P)$ be such that $xi arrow.r 0$ at each $H in cal(H)^*$,
  i.e., $xi_H in A'(H,P)$ for each $H in cal(H)^*$. We must prove that $xi=0$.
  By @eq:conlon-vertex-idempotent-rational-induction,
  $
    xi=i''_P xi=sum_j beta_(j) [(1_(H_j))^G times.o xi]
    =sum_j beta_j lr((xi_(H_j)))^G.
  $
  If $O_p lr((H_j))<P$, the induced class $(xi_(H_j))^G$ belongs to $A'(G,P)$,
  since every $H_j$-lattice is relatively $O_p lr((H_j))$-projective. On the
  other hand, Frobenius reciprocity writes it as $[(1_(H_j))^G] xi$, so it
  belongs to the ideal $A''(G,P)$. These two complementary ideals have zero
  intersection, and hence the induced class vanishes.

  The remaining $H_j$ satisfy $O_p lr((H_j))=P$, so the hypothesis gives
  $xi_(H_j) in A'(H_j,P)$. Its induction again belongs to $A'(G,P)$, and the
  same Frobenius identity places it in $A''(G,P)$, so this induced class is zero
  as well. Every term in the displayed sum vanishes, and therefore $xi=0$. No
  vanishing of the raw restricted class is needed.
  #ed-note[
    Induction places the terms in the common algebra $A(G)$. The raw
    restrictions also vanish: if $z=xi_H$ and $u=op("res")_H^G [R[G slash H]]$,
    Frobenius reciprocity gives $lr((z^G))_H=u z$. Every Burnside mark of the
    restricted coset set is positive, since every subgroup of $H$ fixes the
    coset $H$. Its class is therefore a unit in the complex Burnside algebra, so
    $u$ is a unit in $A(R H)$. Hence $z^G=0$ implies $z=0$ on the restriction
    image.
  ]

]

The preceding results will play a vital role in the proof of the Benson-Carlson
Theorem @th:benson-carlson-cyclic-vertex-semisimplicity below.

=== Species <ss:representation-ring-species>

Let $G$ be a finite group, and $k$ a field of characteristic $p$. In
§§~@ss:representation-ring-preliminaries,
@ss:conlon-representation-ring-theorems we studied the representation algebra
$A(k G)$, spanned over $CC$ by all f.g. $k G$-modules. This is a commutative
$CC$-algebra, and is f.d./$CC$ if and only if the Sylow $p$-subgroups of $G$ are
#source(908)
cyclic. In $A(k G)$ there is the important subalgebra $P P(k G)$, spanned by
permutation projective $k G$-modules. We have seen in
§~@ss:conlon-representation-ring-theorems that the decomposition of $P P(k G)$
into ideals yields important information about $A(k G)$ itself. Furthermore, the
structure of $P P(k G)$ can be determined by constructing a set of nonzero
algebra homomorphisms (called species) from $P P(k G)$ into $CC$. We shall
discuss here the Benson-Parker theory of species on the $CC$-algebra $A(k G)$,
as described in Benson–Parker~@bib:Benson1984 and Benson~@bib:Benson1984a.

It should be pointed out that $A(k G)$ may contain nonzero nilpotent elements,
and for each such element $x$ we have $f(x)=0$ for every species $f$ of
$A(k G)$. Thus, we cannot expect that species can serve to separate the elements
of $A(k G)$, but nevertheless they may provide interesting information about its
structure.

We begin with some general remarks on species of arbitrary commutative
$CC$-algebras.

Let $A$ be a commutative $CC$-algebra, not necessarily f.d. A _species_ of $A$
is a nonzero $CC$-algebra homomorphism $f:A arrow.r CC$. We use the same
terminology whether or not $A$ has an identity element, so in particular we can
talk about species of ideals of $A$. If ${e_1,...,e_n}$ are a set of orthogonal
idempotents of $A$ with $sum e_i=1$, then for each species $f$ of $A$, there is
a unique $i$ such that $f(e_i)=1$, $f(e_j)=0$ for $j != i$, and in this case $f$
is also a species of $A e_i$. In particular, when $A$ is
$CC times dots times CC$ ($n$ copies), then $A$ has precisely $n$ distinct
species.
#idx("Species")

We note that any set of distinct species of a $CC$-algebra $A$ must be linearly
independent over $CC$, by the proof of Artin's Theorem in Exercise
@i:exc:artin-embeddings-independent. Next, if $I$ is any ideal of $A$, then each
species $f:I arrow.r CC$ extends uniquely to a species $g$ of $A$. Indeed,
choose $x in I$ such that $f(x)=1$ and then set $g(a)=f(a x)$, $a in A$. It is
easily verified that $g$ is the unique extension of $f$ and is independent of
the choice of $x$.

Given an algebra homomorphism $phi:A arrow.r B$, each species $g:B arrow.r CC$
lifts to a homomorphism $f:A arrow.r CC$, with $f=g phi$. Then $f$ is a species
of $A$ if and only if $g(phi(A)) != 0$, i.e., $phi(A) subset.not ker g$. In
particular, if $phi$ maps $A$ onto $B$, then every species of $B$ lifts uniquely
to a species of $A$.

#example[
  Let $(K,R,k)$ be a $p$-modular system for $G$. With each $k G$-module $V$
  there is associated its Brauer character $phi_V$, defined as the Brauer
  character of $k' times.o_k V$ for $k'$ sufficiently large. Then $phi_V$ is a
  complex-valued class function defined on $G_(p')$, the set of $p'$-elements of
  $G$. For each $x in G_(p')$, define a homomorphism $b_x:A(k G) arrow.r CC$ by
  the formula
  $ b_(x)[V]=phi_V lr((x)) quad "for each" k G "-module" V, $
  and then extend $b_x$ by linearity. Since $b_(x)[1]=1$, $b_x != 0$. It follows
  from @i:lem:brauer-character-tensor-product that $b_x$ is a species of
  $A(k G)$, and is called a _Brauer species_.

  Let $G_0 lr((k G))$ be the Grothendieck ring of $k G$. The map $b_x$ defined
  above is actually a species of $CC times.o_ZZ G_0 lr((k G))$, which lifts to a
  species of $A(k G)$ via the surjection
  $A(k G) arrow.r CC times.o_ZZ G_0 lr((k G))$.
  #source(909)
  If $K$ is sufficiently large, then by §~@i:sec:brauer-characters,
  $
    CC times.o_ZZ G_0 lr((k G)) &tilde.equiv CC times.o_ZZ op("Bch") k G \
    &tilde.equiv "ring of complex-valued class functions on" G_(p').
  $
  If $r$ denotes the number of $p$-regular classes of $G$, then we obtain $r$
  distinct species ${b_x}$ on $A(k G)$, by letting $x$ range over
  representatives of the $p$-regular classes.
] <exm:brauer-character-species>
#idx("Brauer species", target: [@exm:brauer-character-species])

#example[
  Let $k=FF_2$ and let $G$ be cyclic of order $2$. The indecomposable
  $k G$-modules are $k$ and $k G$, and so
  $ A(k G)=CC dot 1 plus.o CC dot y, quad "where" y=[k G]. $
  We have $y^2=2 y$ in $A(k G)$. There is only one Brauer species of $A(k G)$,
  given by $[V] arrow.r dim_k V$ for $V=k G$-module. There is a second species
  $f$, given by $f(1)=1$, $f(y)=0$.
] <exm:cyclic-two-green-algebra-species>

Keeping the field $k$ fixed, let us write $A(G)$ instead of $A(k G)$. We may
often construct species of $A(G)$ by lifting species of $A(H)$, where $H <= G$.
Consider the diagram

#representation-species-fusion-triangle()

Starting with a species $g$, we may define $f$ as $g compose op("res")$, and
then $f$ is a species if and only if $g(op("res") A(G)) != 0$. Conversely,
starting with a species $f$, we say that $f$ _factors through_ $H$ if there
exists a species $g$ for which the diagram commutes, that is, for which
$ f(x)=g(x_H) quad "for all" x in A(G). $
<eq:representation-species-fusion>
#idx("Fusing of species", target: [@eq:representation-species-fusion])
(In this case, we write $g arrow.r f$ and say that $g$ _fuses_ to $f$.)

#lemma[
  Let $H <= G$, and let $f$ be a species of $A(G)$. The following are
  equivalent:
  #case-list(
    [
      #case[$f$ factors through $H$.] <case:species-factors-through-subgroup>],
    [
      #case[$ker f supset.eq A(G)^H={x in A(G):x_H=0}$.]
      <case:species-restriction-kernel-containment>],
    [
      #case[$ker f supset.not A(H)^G=op("ind")_H^G A(H)$.]
      <case:species-induction-ideal-nonvanishing>
    ],
  )
] <lem:species-factorization-kernel-induction>
#proof[
  The implication @case:species-factors-through-subgroup $arrow.r$
  @case:species-restriction-kernel-containment is clear from
  @eq:representation-species-fusion. Conversely, assume
  part~@case:species-restriction-kernel-containment\:
  #source(910)
  then there is a unique species $f':A(G)_H arrow.r CC$, defined by
  $ f'(xi_H)=f(xi) quad "for" xi in A(G). $
  By @th:puig-restriction-image-integrality, $A(H)$ is integral over its subring
  $A(G)_H$. By the “Going-Up Theorem” (see Atiyah–MacDonald~@bib:Atiyah1969,
  Theorems~5.10–5.11), $f'$ lifts to a species $g$ of $A(H)$, so $f$ factors
  through $H$.

  Next we use the decomposition of $A(G)$ into ideals
  $ A(G)=A(H)^G plus.o A(G)^H $
  (see @th:representation-induction-restriction-ideal-decomposition). Given a
  species $f$, let $I=ker f$; then $A(G) slash I tilde.equiv CC$, so $I$ is a
  maximal ideal of $A(G)$. Thus $I$ contains exactly one of the ideals $A(H)^G$
  and $A(G)^H$, so parts~@case:species-restriction-kernel-containment and
  @case:species-induction-ideal-nonvanishing are equivalent.
]

#definition[
  Let $f$ be a species of $A(G)$. An _origin_ of $f$ is a subgroup $H <= G$ that
  is minimal among those subgroups of $G$ through which $f$ factors.
] <def:representation-species-origin>
#idx("Origin of species", target: [@def:representation-species-origin])

By @lem:species-factorization-kernel-induction, the origin of $f=H$ if and only
if
$ f(A(H)^G) != 0, quad f(A(K)^G)=0 quad "for" K<H. $
Further, if $g$ is a species of $A(H)$ that fuses to $f$, and the origin of
$f=H$, then also the origin of $g=H$ (see Exercise
@exc:species-factorization-transitivity).

#proposition[
  For a species $f$ of $A(G)$, its origins form a class of conjugate subgroups
  of $G$.
] <prop:representation-species-origins-conjugate>
#proof[
  It is clear from the preceding remarks that conjugates of origins are again
  origins. Now let $H$ and $K$ be origins of $f$. Then $ker f$ is a maximal
  ideal of $A(G)$ that does not contain either $A(H)^G$ or $A(K)^G$, and so does
  not contain their product. But Mackey's Formula gives
  $ A(H)^G dot A(K)^G subset.eq sum_(x) A(H^x inter K)^G, $
  summed over certain elements $x in G$. Therefore
  $ker f supset.not A(H^x inter K)^G$ for some $x$, and so $f$ factors through
  $H^x inter K$. The minimality of $H$ and $K$ then gives $H^x=K$, as desired.
]

In the preceding discussion, we can replace the representation algebra $A(G)$ by
the algebra $P P(k G)$ of pp $k G$-modules, and omit the symbol $k$ for
convenience. The algebra $P P(G)$ behaves well with respect to the induction and
restriction maps, and the Mackey Formulas still hold in this context. The proof
of @th:puig-restriction-image-integrality carries over to the algebra $P P(G)$,
to show that for $H <= G$, $P P(H)$ is integral over its subring
$op("res")_H^G P P(G)$. Furthermore, using
@cor:burnside-frobenius-module-decomposition with $M(G)=P P(G)$, we obtain
$
  P P(G)=P P(E)^G plus.o P P(G)^E
  =op("ind")_E^G P P(E) plus.o {x in P P(G):x_E=0}.
$
<eq:permutation-projective-induction-restriction-decomposition>

#source(911)
The analogue of Lemma @lem:species-factorization-kernel-induction clearly holds
for the present case, and we can again define species of $P P(G)$, and their
origins, just as above.

We now determine the origin of the species $s=s_(H,c)$ of $P P(G)$ constructed
in §~@ss:conlon-representation-ring-theorems, where $H$ is a $p$-hypo-elementary
subgroup of $G$, and $H slash O_p lr((H))=chevron.l c chevron.r$. #proposition[
  The species $s_(H,c)$ of $P P(G)$ has origin $H$.
] <prop:permutation-projective-species-origin>
#proof[
  Let $s=s_(H,c)$; we must show that $s$ factors through $H$ but not through any
  proper subgroup $K<H$. Using the notation in
  @eq:permutation-projective-normal-vertex-part, for each pp $k G$-module $V$ we
  have $s[V]=phi_(V') lr((c))$, so $s[V]$ is determined by $V_H$, and therefore
  $s$ factors through $H$.

  Now let $H=P times.r C$, $K=P_0 times.r C_0$, where $P_0 <= P$, $C_0 <= C$,
  $P=O_p lr((H))$, $C=chevron.l c chevron.r$. If $P_0<P$, then each
  indecomposable $k G$-module in $P P(K)^G$ has vertex $<=P_0$, and thus $s$
  vanishes on $P P(K)^G$. Therefore $s$ cannot factor through $K$ in this case,
  and so necessarily $K=P times.r C_0$. The proof of
  @lem:permutation-projective-species-separation shows that as $X$ ranges over
  all indecomposable projective $k(N slash P)$-modules, for each $X$ there
  exists a pp $k G$-module $V$ such that $s[V]=phi_X lr((c))$, where $phi_X$ is
  the Brauer character of $N slash P$ afforded by $X$. If $s$ factors through
  $K$, then $s[V]$ is determined by $V_K$, or equivalently, by the way that
  $c_0$ acts on $X$, where $C_0=chevron.l c_0 chevron.r$. By Remark
  @rem:permutation-projective-species-field-conjugacy we conclude that $c_0$ and
  $c$ generate conjugate subgroups of $N slash P$, and therefore $C_0=C$, and
  $K=H$, as desired. This completes the proof.
]

#corollary[
  The Brauer species $b_x$ of $A(G)$, defined in Example
  @exm:brauer-character-species, has as origin the cyclic group
  $chevron.l x chevron.r$.
] <cor:brauer-species-cyclic-origin>

#remarks[
  #case-list(
    [
      #case[
        Let $H <= G$, and let $g$ be a species of $A(H)$. Define the
        _stabilizer_ of $g$ as
        $
          op("Stab")_G g={x in N_G lr((H)):g(u)=g(u^x)
            "for all" u in A(H)}.
        $
        Now let $f$ be a species of $A(G)$ with origin $H$, set $N=N_G lr((H))$,
        and denote by $op("inv")_N A(H)$ the $N$-trivial subalgebra of $A(H)$.
        Then (see Benson–Parker~@bib:Benson1984, Theorem~8.2) $N$ acts
        transitively on the species $g_1,...,g_r$ of $A(H)$ that fuse to $f$,
        and the number $r$ of such species is precisely
        $abs(N : op("Stab")_G g_1)$.
      ] <case:species-fusion-normalizer-orbit>],
    [
      #case[
        Keep the above notation, and let $M$ be a $k E$-module, where $E <= G$.
        Benson-Parker established an _induction formula_
        $ f(M^G)=sum_(h arrow.r f) c_h h(M), $
        where the sum extends over all species $h$ of $A(E)$ that fuse to $f$,
        and where
        $
          c_h=abs(
            N_G lr(("origin of" h)) inter op("Stab")_G h:
            N_E lr(("origin of" h))
          ).
        $
      ] <case:species-induction-formula>
    ],
  )
] <rem:species-stabilizers-fusion-induction>

Now let $E <= G$, and consider the algebra $A(G)=A(k G)$. By Theorem
@th:representation-induction-restriction-ideal-decomposition, we
#source(912)
may write
$
  A(G)=A(E)^G plus.o A(G)^E
  =op("ind")_E^G A(E) plus.o {x in A(G):x_E=0},
$
a direct sum of two ideals. We shall determine idempotent generators of these
ideals, in terms of the primitive idempotents ${e_(H,c)}$ of $P P(G)$ (see
@eq:permutation-projective-idempotent-species-sum). Using
@eq:permutation-projective-induction-restriction-decomposition, we may write
$
  1=alpha+beta, quad alpha in P P(E)^G, quad beta in P P(G)^E, quad
  alpha beta=0.
$
Then we have
$
  A(G)=A(G) alpha plus.o A(G) beta, quad A(G) alpha subset.eq A(E)^G, quad
  A(G) beta subset.eq A(G)^E,
$
and consequently
$ A(E)^G=A(G) alpha, quad A(G)^E=A(G) beta. $
It therefore suffices to determine the idempotents $alpha,beta$ in $P P(G)$.

Now $alpha$ is the sum of all $e_(H,c)$ for which $e_(H,c) in P P(E)^G$, and
$beta$ is the sum of the other $e$'s. #lemma[
  We have
  $ e_(H,c) in P P(E)^G <=> H <=_G E. $
] <lem:species-idempotent-induction-subgroup-support>
#proof[
  Let $H <=_G E$; replacing $E$ by a conjugate, we may assume that $H <= E$.
  Then $e_H in P P(E)^G$ by
  @eq:permutation-projective-idempotent-induction-expansion, since for
  $H_i <= H$ we have
  $ (1_(H_i))^G=((1_(H_i))^E)^G in P P(E)^G. $
  But then $e_(H,c)=e_H dot e_(H,c) in P P(E)^G$, since $P P(E)^G$ is an ideal
  of $P P(G)$. On the other hand, suppose that $e_(H,c) in P P(E)^G$. Then the
  species $s_(H,c)$ of $P P(G)$ does not vanish on $P P(E)^G$, and hence
  $s_(H,c)$ factors through $E$. Therefore $E$ contains an origin of $s_(H,c)$,
  so $E >=_G H$ by @prop:permutation-projective-species-origin.
]

From the above discussion, we obtain: #theorem[
  Let $E <= G$. Then
  $ A(E)^G=A(G) alpha, quad A(G)^E=A(G) beta, $
  where the orthogonal idempotents $alpha$ and $beta$ are given by
  $ alpha=sum_(H <=_G E) e_(H,c), quad beta=sum_(H ≰_G E) e_(H,c), $
  #source(913)
  with $H$ ranging over nonconjugate $p$-hypo-elementary subgroups of $G$, and
  $c$ over generators of $H slash O_p lr((H))$ yielding distinct species
  $s_(H,c)$.
] <th:species-induction-restriction-idempotent-generators>

We may use Conlon's Induction Theorem to show: #theorem[
  The origin of any species of $A(G)$ is a $p$-hypo-elementary subgroup of $G$.
] <th:representation-species-hypoelementary-origin>
#idx(
  "Origin of species",
  target: [@th:representation-species-hypoelementary-origin],
)
#proof[
  Let $f$ be a species of $A(G)$ with origin $H$. By
  @th:conlon-p-permutation-induction, we have
  $ A(H)=sum_K A(K)^H, $
  where $K$ ranges over the $p$-hypo-elementary subgroups of $H$. Therefore
  $ A(H)^G=sum_K A(K)^G. $
  Since $f$ factors through $H$, we have $ker f supset.not A(H)^G$ by
  @lem:species-factorization-kernel-induction, so $ker f supset.not A(K)^G$ for
  some $K$. Then $f$ factors through $K$, so $K=H$ by the minimality of $H$.
  This completes the proof.
]

We shall also introduce the concept of the _vertex_ of a species $f$ of $A(G)$,
defined as a minimal element of the set of vertices of indecomposable
$k G$-modules $M$ for which $f[M] != 0$. We have:
#idx("Vertex", "of a species")
#theorem[
  The vertices of a species $f$ of $A(G)$ form a conjugacy class of
  $p$-subgroups of $G$.
] <th:representation-species-vertices-conjugate>
#proof[
  Let $P_1$ and $P_2$ be vertices of $f$. Then for $i=1,2$, there exist
  $M_i in op("Ind") k G$ with $f[M_i] != 0$, and $P_i$ is a vertex of $M_i$. We
  have $f[M_1 times.o M_2]=f[M_1] f[M_2] != 0$, so $f[X] != 0$ for some
  indecomposable summand $X$ of $M_1 times.o M_2$. From the remarks in
  §~@ss:representation-ring-preliminaries, $M_1 times.o M_2$ is
  $(G,P_i)$-projective for $i=1,2$, so the vertices of $X$ are conjugate to
  subgroups of both $P_1$ and $P_2$. By the minimality of $P_1$ and $P_2$, we
  conclude that $P_1 =_G P_2$.
]

There is a close connection between the origin and the vertex of a species $f$
of $A(G)$, given as follows: #theorem[
  Let $f$ be a species of $A(G)$ with origin $H$. Then the vertex of $f$ is
  $O_p lr((H))$, up to $G$-conjugacy.
] <th:representation-species-origin-vertex>
#proof[
  By @th:representation-species-hypoelementary-origin, $H$ is
  $p$-hypo-elementary; let $P=O_p lr((H))$. Then
  $ f(A(H)^G) != 0, quad f(A(K)^G)=0 quad "for" K<H. $
  By @th:species-induction-restriction-idempotent-generators, $A(H)^G$ is
  generated by the idempotent $sum e_(K,c)$, with $K$ ranging over
  #source(914)
  subgroups of $H$, and various choices of $c$. Since $e_(K,c) in A(K)^G$, it
  follows that $f(e_(H,c)) != 0$ for some $c$. Therefore $f(A''(G,P)) != 0$ by
  @eq:conlon-relative-vertex-idempotent-generators, so $f[M] != 0$ for some
  $M in op("Ind") k G$ of vertex $P$.

  Next, $f$ must vanish on $A(G)^H$, so by
  @th:species-induction-restriction-idempotent-generators, $f(e_(K,c))=0$ if
  $K ≰_G H$. Combining this fact with the previous argument, it follows from
  @eq:conlon-relative-vertex-idempotent-generators that $f(A'(G,P))=0$, which
  completes the proof that $f$ has vertex $P$.
]

For further reading on species of $A(G)$, and character tables that extend those
involving Brauer characters, see Benson–Parker~@bib:Benson1984,
Benson~@bib:Benson1984a, and Webb~@bib:Webb1984.

#numbering-gap()

=== Dual Elements in the Green Algebra <ss:green-algebra-dual-elements>

Throughout this section, $G$ denotes a finite group, and $K$ a field of
characteristic $p >= 0$. By a “$G$-module”, we shall mean a f.g. (left)
$K G$-module. Define the representation ring $a(K G)$ and the representation
algebra (= Green algebra) $A(K G)=CC times.o_ZZ a(K G)$ as in
§~@ss:representation-ring-preliminaries. Here we shall describe the work of
Benson–Parker~@bib:Benson1984, who defined various inner product on $A(K G)$,
and construct a kind of #idx("Dual elements (in A(G))")dual basis by using the
theory of Auslander-Reiten sequences.

For a $G$-module $M$, let $M^*$ denote its contragredient, and $op("inv")_G M$
its $G$-trivial submodule. Let $K$ or $K_G$ be the field $K$ on which $G$ acts
trivially. For $G$-modules $M$ and $N$, define their _intertwining number_ as
$ (M,N)_G=dim_K op("Hom")_(K G) lr((M,N)) $
<eq:green-algebra-intertwining-number>
#idx("Intertwining number", target: [@eq:green-algebra-intertwining-number])
(see @i:prop:character-scalar-products-multiplicities). Write $times.o$ instead
of $times.o_K$ for brevity. By @i:prop:invariants-induction-hom(ii) and
@i:eq:contragredient-hom-duality, there are $K$-isomorphisms
$
  op("inv")_G M^* times.o N tilde.equiv op("Hom")_(K G) lr((M,N)) tilde.equiv
  op("Hom")_(K G) lr((N^*,M^*)).
$
<eq:green-algebra-intertwining-duality>
But we also have
$ op("inv")_G M^* times.o N tilde.equiv op("Hom")_(K G) lr((K,M^* times.o N)), $
so we immediately obtain the formulas
$ (M,N)_G=(K,M^* times.o N)_G=(M times.o N^*,K)_G=(N^*,M^*)_G. $
Next, let $H <= G$, and let $M$ be a $G$-module, $L$ an $H$-module. The
Frobenius reciprocity formulas @i:th:frobenius-reciprocity and
@i:prop:frobenius-right-adjoint yield
$ (L^G,M)_G=(L,M_H)_H, quad (M,L^G)_G=(M_H,L)_H. $
If $K G$ is semisimple (i.e., $p divides.not abs(G)$), then $(M,N)_G=(N,M)_G$
for any $G$-modules $M,N$. Simple examples show that this need not hold when $p$
divides $abs(G)$. Later,
#source(915)
we shall introduce a second inner product $chevron.l ,
chevron.r$, which is symmetric, and the entire theory can be developed equally
well using it rather than $(,)$.

Continuing with our discussion, we note that the intertwining number $(M,N)_G$,
defined in @eq:green-algebra-intertwining-number, is additive on direct sums of
modules. We may therefore extend this symbol by linearity to obtain a pairing
$
  A(K G) times A(K G) arrow.r CC, quad
  "given by" (x times y) arrow.r (x,y)_G in CC.
$
<eq:green-algebra-hom-pairing>

Generally speaking, $(x,y)_G$ need not coincide with $(y,x)_G$. To simplify the
calculations, we _assume $K$ algebraically closed from now on_, unless stated
otherwise. Let $op("char") K=p >= 0$. If $p divides.not abs(G)$, then $K G$ is
semisimple, and the representation ring $a(K G)$ coincides with the Grothendieck
ring $G_0 lr((K G))$ (see §~@i:ss:grothendieck-groups,
§~@ss:grothendieck-frobenius). This ring has a $ZZ$-basis consisting of a basic
set of simple $K G$-modules. By @i:cor:prime-to-p-brauer-ordinary-characters, we
have
$
  G_0 lr((K G)) tilde.equiv G_0 lr((CC G)) tilde.equiv op("ch") CC G, quad
  A(K G) tilde.equiv op("cf")_CC G,
$
where $op("ch") CC G$ is the ring of virtual complex characters of $G$, and
$op("cf")_CC G$ the ring of complex-valued class functions on $G$. By
§~@i:sec:orthogonality-central-idempotents, the ring $op("cf")_CC G$ is
semisimple, and the pairing @eq:green-algebra-intertwining-number is symmetric
and nondegenerate.

Dropping the assumption that $p divides.not abs(G)$, we can no longer identify
$a(K G)$ with $G_0 lr((K G))$. The ring $a(K G)$ has as $ZZ$-basis the set
${[M]:M in op("Ind") K G}$, where as usual $op("Ind") K G$ is the set of
(isomorphism classes of) indecomposable $K G$-modules. This set is also a
$CC$-basis for $A(K G)$, so $A(K G)$ is f.d./$CC$ if and only if $K G$ has
finite representation type. By D. G. Higman's Theorem (see Volume I, Exercise
@i:exc:finite-indecomposable-group-algebras), this occurs if and only if $G$ has
a cyclic Sylow $p$-subgroup.

Returning to the general case, we now give the main result of this subsection:
#theorem(name: "Benson-Parker Theorem")[
  Let $K$ be an algebraically closed field of characteristic $p >= 0$, let $G$
  be any finite group, and consider the pairing $A(K G) times A(K G) arrow.r CC$
  defined above. Then this pairing is nondegenerate in the following sense: for
  each $M in op("Ind") K G$, there exists an element $hat(M) in A(K G)$ such
  that
  $ (N,hat(M))_G=delta_(M N) quad "for" M,N in op("Ind") K G, $
  where $delta_(M N)=1$ if $M tilde.equiv N$, and $=0$ otherwise.
] <th:benson-parker-green-algebra-duality>
#idx("Benson-Parker Theorem", target: [@th:benson-parker-green-algebra-duality])

Before giving the proof, which is based on the theory of Auslander-Reiten
sequences developed in §~@sec:auslander-reiten-sequences, we give an easy but
surprising consequence: #corollary[
  #case-list(
    [
      #case[The map
        $
          A(K G) arrow.r op("Hom")_CC lr((A(K G),CC)), quad
          "given by" x arrow.r (x,dot)_G,
        $
        is injective.
      ] <case:green-hom-pairing-left-nondegenerate>],
    [
      #case[
        #source(916)
        A $K G$-module $M$ is uniquely determined (up to isomorphism) by the set
        of values
        $ {(M,X)_G:X=K G "-module"}. $
      ] <case:module-determined-by-hom-dimensions>
    ],
  )
] <cor:green-hom-pairing-module-detection>
#proof[
  For part~@case:green-hom-pairing-left-nondegenerate, let $x in A(K G)$ be such
  that $(x,N)_G=0$ for every $K G$-module $N$. We may write $x$ as a finite sum
  $
    x=sum xi_(i) [M_i], quad "with" xi_i in CC, quad
    M_i in op("Ind") K G,
  $
  and $M_i ≇ M_j$ for $i != j$. Then for each $i$,
  $ 0=(x,hat(M)_i)_G=xi_i lr((M_i,hat(M)_i))=xi_i, $
  so $x=0$. Assertion @case:module-determined-by-hom-dimensions follows from
  part~@case:green-hom-pairing-left-nondegenerate.
]

We begin the proof of @th:benson-parker-green-algebra-duality with a lemma which
uses the hypothesis that $K$ is algebraically closed. #lemma[
  Consider a ses of $K G$-modules
  $ 0 arrow.r N arrow.r E arrow.r^phi M arrow.r 0, $
  <eq:ar-hom-cokernel-criterion-sequence>
  where $M,N in op("Ind") K G$. For each $X in op("Ind") K G$, $phi$ induces a
  $K$-linear map
  $
    phi_*:op("Hom")_(K G) lr((X,E)) arrow.r
    op("Hom")_(K G) lr((X,M)).
  $
  Then @eq:ar-hom-cokernel-criterion-sequence is an AR-sequence (for $M$) if and
  only if
  $
    dim_K lr((op("cok") phi_*))=delta_(X M) quad
    "for all" X in op("Ind") K G.
  $
  <eq:ar-hom-cokernel-delta>
] <lem:ar-sequence-hom-cokernel-criterion>
#proof[
  For brevity, write $op("Hom")$ and $op("End")$ in place of $op("Hom")_(K G)$
  and $op("End")_(K G)$. Since $M$ is indecomposable and $K$ is algebraically
  closed, by §~@ss:representation-ring-preliminaries we know that $op("End")(M)$
  is a local ring for which
  $ op("End")(M) slash lr((op("rad") op("End")(M))) tilde.equiv K. $
  Now consider a $K G$-homomorphism $f:X arrow.r M$, where $X in op("Ind") K G$.
  Then $f$ is a split surjection if and only if $f$ is an isomorphism, since
  both $X$ and $M$ are indecomposable. On the other hand, $f$ factors through
  $E$ if and only if $f in op("im") phi_*$.

  Suppose now that @eq:ar-hom-cokernel-criterion-sequence is an AR-sequence,
  which means that the sequence is nonsplit, and that for each $K G$-module $Y$,
  each map $Y arrow.r M$ that is not a split surjection must factor through $E$.
  In particular, for $X in op("Ind") K G$, each nonisomorphism $f:X arrow.r M$
  must lie in $op("im") phi_*$. If $X tilde.equiv M$, then $op("im") phi_*$
  contains all elements of $op("End") M$ that are not automorphisms of $M$;
  further, $op("im") phi_*$ contains no automorphism of $M$, since otherwise the
  sequence @eq:ar-hom-cokernel-criterion-sequence would split. Thus,
  #source(917)
  $op("im") phi_*$ coincides with the radical $op("rad") op("End")(M)$ of the
  local ring $op("End")(M)$, and so $op("cok") phi_* tilde.equiv K$. This shows
  that $dim_K op("cok") phi_*=1$ if $X tilde.equiv M$.

  On the other hand, for any $X in op("Ind") K G$ that is not isomorphic to $M$,
  every map $f:X arrow.r M$ is not a split surjection, and hence lies in
  $op("im") phi_*$. Therefore $op("cok") phi_*=0$ in this case. We have now
  shown that @eq:ar-hom-cokernel-delta holds whenever
  @eq:ar-hom-cokernel-criterion-sequence is an AR-sequence. By using Exercise
  @exc:ar-factorization-indecomposable-test the argument is easily reversed; we
  leave the details to the reader.
]

We are now ready to prove the Benson-Parker Theorem, and begin by defining the
elements ${hat(M):M in op("Ind") K G}$. #definition[
  Let $J=op("rad") K G$, and write $op("Hom")$, $op("End")$ in place of
  $op("Hom")_(K G)$, $op("End")_(K G)$ for brevity. Let $M in op("Ind") K G$.
  #case-list(
    numbering: "(a)",
    [
      #case[If $M$ is projective, set
        $ hat(M)=[M]-[J M] in A(K G). $
      ] <case:green-right-dual-projective>],
    [
      #case[If $M$ is nonprojective, set
        $ hat(M)=[M]-[E]+[Omega^2 M] in A(K G), $
        where
        $ 0 arrow.r Omega^2 M arrow.r E arrow.r^phi M arrow.r 0 $
        <eq:green-right-dual-ar-sequence>
        is an AR-sequence for $M$ (see @eq:group-algebra-ar-extension).
      ] <case:green-right-dual-nonprojective>
    ],
  )
] <def:green-algebra-right-dual>
#idx("Dual elements (in A(G))", target: [@def:green-algebra-right-dual])

We proceed to verify that $(N,hat(M))_G=delta_(M N)$ for $M,N in op("Ind") K G$.
Suppose first that $M$ is projective, and let $S=M slash lr((J M))$ be the “top”
of $M$. Then
$
  (M,hat(M))_G=dim_K op("Hom")(M,M)-dim_K op("Hom")(M,J M)
  =dim_K op("Hom")(M,S)
$
since $op("Hom")(M,ast)$ is an exact functor. But
$op("Hom")(M,S) tilde.equiv op("Hom")(S,S) tilde.equiv K$, so $(M,hat(M))_G=1$.
On the other hand, if $N in op("Ind") K G$ is not isomorphic to $M$, then there
are no surjections from $N$ onto $M$. Hence for each $f:N arrow.r M$ we must
have $f(N) subset.eq J M$, and therefore
$ op("Hom")(N,M)=op("Hom")(N,J M). $
But then
$ (N,hat(M))_G=dim_K op("Hom")(N,M)-dim_K op("Hom")(N,J M)=0, $
as desired.

Now suppose that $M$ is a nonprojective indecomposable $K G$-module, and let
@eq:green-right-dual-ar-sequence be its AR-sequence. For any
$N in op("Ind") K G$, there is an exact sequence
#source(918)
of $K$-spaces
$
  0 arrow.r op("Hom")(N,Omega^2 M) arrow.r op("Hom")(N,E)
  arrow.r^(phi_*) op("Hom")(N,M) arrow.r op("cok") phi_* arrow.r 0.
$
Therefore $(N,hat(M))_G=dim_K op("cok")(phi_*)=delta_(N M)$ by Lemma
@lem:ar-sequence-hom-cokernel-criterion. This completes the proof of the
Benson-Parker Theorem.

We remark that the dual elements ${hat(M):M in op("Ind") K G}$ are obviously
linearly independent over $CC$, and we may ask whether they span $A(K G)$. The
answer, due to Auslander~@bib:Auslander1984 and Brenner-Butler-Hughes, is as
follows: #theorem[
  The dual elements ${hat(M):M in op("Ind") K G}$ are a $CC$-basis for $A(K G)$
  if and only if $K G$ is of finite representation type, that is, $G$ has a
  cyclic Sylow $p$-subgroup.
] <th:green-dual-basis-finite-representation-type>
#proof[
  If $K G$ has finite representation type, then $A(K G)$ is a f.d. $CC$-space;
  in this case, the elements ${hat(M):M in op("Ind") K G}$ and
  ${[M]:M in op("Ind") K G}$ are a pair of dual bases relative to the pairing
  $(,)_G$.

  On the other hand, suppose that the ${hat(M)}$'s span $A(K G)$. For each
  $X in op("Ind") K G$, we may write $[X]$ as a finite sum
  $ [X]=sum lambda_M hat(M), quad "where" lambda_M in CC. $
  Since $lambda_M=(M,X)_G$, it follows that for each $X$ there are finitely many
  $M in op("Ind") K G$ for which $op("Hom")(M,X) != 0$.

  Now let $X_1,...,X_r$ be the indecomposable injective (= projective)
  $K G$-modules, up to isomorphism. Each $M in op("Ind") K G$ embeds in some
  f.g. injective $K G$-module (for Exercise @i:exc:lattice-embeds-free), and
  hence embeds in a direct sum of $X$'s. Thus for each $M$,
  $op("Hom")(M,X_i) != 0$ for some $i$. But if $K G$ has infinite representation
  type, there are infinitely many $M$'s, and so for some $i$, $1 <= i <= r$, we
  must have $op("Hom")(M,X_i) != 0$ for infinitely many $M in op("Ind") K G$.
  This contradicts the conclusion of the previous paragraph, and establishes the
  theorem.
]

We shall next discuss another inner product $chevron.l ,
chevron.r$ on the representation algebra $A(K G)$. Let $M$ and $N$ be
$G$-modules, and write $op("Hom")$ rather than $op("Hom")_(K G)$ for brevity. As
in §~@ss:cyclic-block-homological-preliminaries and
§~@ss:heller-loop-space-operator, a map $f in op("Hom")(M,N)$ is called a
_projective homomorphism_ if $f$ factors through a projective, or equivalently,
$ f=sum_(x in G) x h x^(-1) quad "for some" h in op("Hom")_K lr((M,N)). $
Denoting by $op("Hom")(M,N)_(G slash 1)$ the space of such $f$'s, we now define
$ chevron.l M,N chevron.r=dim_K op("Hom")(M,N)_(G slash 1). $
<eq:green-projective-hom-pairing>
Following Benson-Parker, we give an important characterization of this inner
product:

#source(919)
#proposition[
  Let $P_1$ be the projective cover of the trivial $G$-module $K$. Then
  $
    chevron.l M,N chevron.r = "multiplicity of" P_1
    "as direct summand of" M^* times.o N,
  $
  where $M^*$ is the contragredient of $M$, and $times.o$ means inner tensor
  product over $K$.
] <prop:projective-hom-pairing-trivial-projective-multiplicity>
#proof[
  It is easily verified that the isomorphism
  $ op("Hom")(M,N) tilde.equiv op("Hom")(K,M^* times.o N), $
  given in @eq:hom-inner-tensor-invariants, preserves projective homomorphisms.
  Therefore we have
  $ chevron.l M,N chevron.r=chevron.l K,M^* times.o N chevron.r. $
  Since $P_1$ is indecomposable, it thus suffices to show that #named-equation(
    name: [$(ast)$],
  )[
    $ dim_K op("Hom")(K,X)_(G slash 1)=delta_(X,P_1) $
  ] <eq:projective-hom-trivial-module-delta>
  for each indecomposable direct summand $X$ of $M^* times.o N$.

  The projective cover $P_1$ of $K$ is also the injective hull of $K$. Each
  nonzero $f in op("Hom")(K,X)_(G slash 1)$ is a monomorphism that factors
  through a projective (= injective) module, and therefore $f$ factors through a
  monomorphism $P_1 arrow.r X$. Since $P_1$ is injective, this map must split,
  and therefore $X tilde.equiv P_1$. Thus,
  @eq:projective-hom-trivial-module-delta surely holds if $X ≇ P_1$. On the
  other hand, for $X tilde.equiv P_1$, the above discussion gives
  $
    op("Hom")(K,P_1)_(G slash 1)=op("Hom")(K,P_1)=op("Hom")(K,K) tilde.equiv K,
  $
  so again @eq:projective-hom-trivial-module-delta holds. This completes the
  proof.
]

#corollary[
  Let $L,M$, and $N$ be $G$-modules. Then
  $
    chevron.l M,N chevron.r=chevron.l N,M chevron.r
    =chevron.l M^*,N^* chevron.r, quad
    chevron.l L times.o M,N chevron.r=chevron.l L,M^* times.o N chevron.r,
  $
  and $chevron.l M,N chevron.r$ is additive on direct sums of modules.
] <cor:projective-hom-pairing-symmetry-tensor>
#proof[
  Since $K$ is self-contragredient, so is $P_1$. Thus the multiplicity of $P_1$
  as direct summand of $M^* times.o N$ is the same as in $(M^* times.o N)^*$.
  The latter is isomorphic to $N^* times.o M$, so
  $chevron.l M,N chevron.r=chevron.l N,M chevron.r$. Further,
  $
    M^* times.o N tilde.equiv (N^*)^* times.o M^*, quad "so"
    chevron.l M,N chevron.r=chevron.l M^*,N^* chevron.r.
  $
  Also,
  $
    (L times.o M)^* times.o N tilde.equiv L^* times.o (M^* times.o N), quad
    "so" chevron.l L times.o M,N chevron.r
    =chevron.l L,M^* times.o N chevron.r.
  $
  The additivity of $chevron.l M,N chevron.r$ is clear.
]

#source(920)
We may thus extend $chevron.l , chevron.r$ by linearity to a _symmetric_ pairing
$
  A(K G) times A(K G) arrow.r CC, quad
  "given by" x times y arrow.r chevron.l x,y chevron.r.
$
<eq:green-symmetric-projective-hom-pairing>
The relation between this pairing and that defined in
@eq:green-algebra-hom-pairing is as follows:

#proposition[
  Let $P_1$ be the projective cover of $K$, and let $Omega$ be the #idx(
    "Heller operator",
  )Heller operator defined in §~@ss:heller-loop-space-operator. Let
  $ u=[P_1]-[Omega^(-1) K], quad v=[P_1]-[Omega K], $
  viewed as elements of $A(K G)$. Then $u v=v u=1$ in $A(K G)$, and
  $ chevron.l M,N chevron.r=(u M,N)_G=(M,v N)_G $
  <eq:green-hom-pairings-unit-translation>
  for any $G$-modules $M$ and $N$, where $u M$ means the product $u[M]$ in
  $A(K G)$.
] <prop:green-pairings-syzygy-units>
#proof[
  We start with the exact sequence
  $ 0 arrow.r K arrow.r P_1 arrow.r Omega^(-1) K arrow.r 0 $
  <eq:trivial-module-injective-hull-sequence>
  (if $K$ is projective, then $p divides.not abs(G)$, and we set
  $Omega^(-1) K=0$). Tensoring with $M$, we obtain an exact sequence
  $
    0 arrow.r M arrow.r P_1 times.o M arrow.r Omega^(-1) K times.o M
    arrow.r 0.
  $
  If $M$ is projective, this sequence splits, and thus $u M=M$ in $A(K G)$. But
  then
  $
    chevron.l M,N chevron.r=dim_K op("Hom")(M,N)_(G slash 1)
    =dim_K op("Hom")(M,N)=(M,N)_G,
  $
  as desired.

  Suppose now that $M$ has no projective summands, so there is an exact sequence
  $ 0 arrow.r Omega M arrow.r P_M arrow.r M arrow.r 0, $
  where $P_M$ is a projective cover of $M$. Tensoring with $Omega^(-1) K$ and
  using Schanuel's Lemma, we obtain #named-equation(name: [$(ast)$])[
    $
      M plus.o (Omega^(-1) K times.o P_M) tilde.equiv P_1 times.o M plus.o
      (Omega^(-1) K times.o Omega M).
    $
  ] <eq:syzygy-unit-schanuel-comparison>
  On the other hand,
  $
    u(P_M-Omega M)=P_1 lr((P_M-Omega M))-Omega^(-1) K dot P_M
    +Omega^(-1) K dot Omega M quad "in" A(K G).
  $
  But $P_1 lr((P_M-Omega M))=P_1 dot M$, so using
  @eq:syzygy-unit-schanuel-comparison we have
  #source(921)
  $ u(P_M-Omega M)=M quad "in" A(K G). $
  In the same way, we find that
  $ v(I_M-Omega^(-1) M)=M quad "in" A(K G), $
  where $I_M$ is an injective hull of $M$. Choosing $M=K$, it follows that
  $u v=v u=1$ in $A(K G)$.

  To prove @eq:green-hom-pairings-unit-translation, note that
  $
    chevron.l M,N chevron.r=chevron.l K,M^* times.o N chevron.r, quad
    (u M,N)_G=(u,M^* times.o N)_G.
  $
  It thus suffices to verify that $chevron.l K,X chevron.r=(u,X)_G$ for each
  $G$-module $X$. Now $op("Hom")(K,X)_(G slash 1)$ consists of all
  $f in op("Hom")(K,X)$ that factor through $P_1$. By
  @eq:trivial-module-injective-hull-sequence, we obtain
  $
    chevron.l K,X chevron.r & =dim_K op("Hom")(K,X)_(G slash 1) \
                            & =dim_K
                              op("Hom")(P_1,X)-dim_K op("Hom")(Omega^(-1) K,X)
                              =(u,X)_G.
  $
  The second formula in @eq:green-hom-pairings-unit-translation follows in a
  similar fashion.
]

We prove next a Frobenius reciprocity formula for the pairing
$chevron.l , chevron.r$. #proposition[
  Let $H <= G$, and let $M$ be a $G$-module, $N$ an $H$-module. Then
  $ chevron.l M,N^G chevron.r=chevron.l M_H,N chevron.r. $
] <prop:projective-hom-pairing-frobenius-reciprocity>
#proof[
  Let $K'$ be the trivial $H$-module, $P'$ its $K H$-projective cover. Comparing
  the two exact sequences
  $
    0 arrow.r K' arrow.r P' arrow.r Omega^(-1) K' arrow.r 0, quad
    0 arrow.r K' arrow.r (P_1)_H arrow.r (Omega^(-1) K)_H arrow.r 0,
  $
  Schanuel's Lemma shows that $op("res")_H^G u_G=u_H$, where
  $ u_G=P_1-Omega^(-1) K, quad u_H=P'-Omega^(-1) K'. $
  But then
  $
    chevron.l M,N^G chevron.r=(u_G M,N^G)_G=(u_H M_H,N)_H
    =chevron.l M_H,N chevron.r.
  $
]

The dual elements for this symmetric pairing on $A(K G)$ are given as follows:
#case-list(
  [
    #case[If $M$ is a projective indecomposable $G$-module, put
      $ M'=["socle of" M] in A(K G). $
    ] <case:symmetric-green-dual-projective>],
  [
    #case[
      #source(922)
      If $M$ is a nonprojective indecomposable $G$-module, define
      $ M'=[X]-[Omega M]-[Omega^(-1) M] in A(K G), $
      where
      $ 0 arrow.r Omega M arrow.r X arrow.r Omega^(-1) M arrow.r 0 $
      is an AR-sequence. As in the proof of
      @th:benson-parker-green-algebra-duality, or by using
      @th:benson-parker-green-algebra-duality and
      @eq:green-hom-pairings-unit-translation, we obtain
      $
        chevron.l N,M' chevron.r=delta_(N M) quad
        "for" N,M in op("Ind") K G.
      $
      <eq:symmetric-green-algebra-dual-delta>
      #idx(
        "Dual elements (in A(G))",
        target: [@eq:symmetric-green-algebra-dual-delta],
      )
      We leave the details to the reader.
    ] <case:symmetric-green-dual-nonprojective>
  ],
)

=== Semisimplicity of Representation Algebras
<ss:representation-algebra-semisimplicity>

Let $K$ be a field of characteristic $p >= 0$, and let $A(G)$ be the
representation algebra, spanned over $CC$ by the indecomposable $K G$-modules.
If $p=0$, then $A(G)$ is isomorphic to the $CC$-algebra of class functions
$op("cf")(G)$ and is necessarily semisimple. Thus, in discussing the
semisimplicity of $A(G)$, we may as well restrict our attention to the case
where $p>0$. We have already remarked that $A(G)$ is f.d./$CC$ if and only if
$G$ has a cyclic Sylow $p$-subgroup. Our main aim here is to prove O'Reilly's
Theorem, that $A(G)$ is semisimple in this case. Rather than following the
original proof (O’Reilly~@bib:OReilly1965a; see also Feit~@bib:Feit1982), we
present a new proof due to Benson–Carlson~@bib:Benson1986, which is rather
conceptual.

On the other hand, if $G$ has a noncyclic Sylow $p$-subgroup, then $A(G)$ may
contain nonzero nilpotent elements. Such examples were first found by
Zemanek~@bib:Zemanek1971, @bib:Zemanek1973, and in
§~@ss:representation-algebra-nilpotent-elements we give the Benson-Carlson
interpretation of these examples.

As a starting point of the Benson-Carlson method, we begin by giving a criterion
as to when the $G$-trivial module $K$ occurs as direct summand of $M times.o N$,
when $M,N in op("Ind") K G$. If $K G$ is semisimple, then $op("Ind") K G$
consists of the simple $K G$-modules. For $M,N$ simple,
§~@ss:green-algebra-dual-elements gives
$ K divides M times.o N <=> (M^*,N)_G != 0 <=> N tilde.equiv M^*, $
where $M^*$ is the contragredient of $M$.

Now let $op("char") K=p>0$, where $p$ divides $abs(G)$. Let $N$ be any
$K G$-module such that $p divides.not d$, where $d=dim_K N$. As pointed out by
Feit~@bib:Feit1982, III.2.2, we have $K divides (N^* times.o N)$. To see this,
we first observe that
$ N^* times.o N tilde.equiv op("Hom")_K lr((N,N)) tilde.equiv M_d lr((K)). $
The group $G$ acts by conjugation on $M_d lr((K))$, and thus $K dot I_d$ is a
$K G$-submodule
#source(923)
of $M_d lr((K))$. So also is
$ X={x in M_d lr((K)):op("trace") x=0}. $
Since $p divides.not d$ by hypothesis, we have
$ M_d lr((K))=X plus.o K dot I_d, $
<eq:endomorphism-trace-trivial-summand>
so $K divides (N^* times.o N)$, as claimed.

We now prove the Benson-Carlson criterion for the tensor product of
$K G$-modules to contain the trivial $G$-module $K$ as direct summand. #theorem[
  Let $M,N in op("Ind") K G$ be such that
  $tilde(E) lr((M)) tilde.equiv tilde(E) lr((N)) tilde.equiv K$ (using the
  notation in @eq:module-endomorphism-semisimple-quotient). Then
  $K divides (M times.o N)$ if and only if
  #case-list(
    [
      #case[$M tilde.equiv N^*$,
        and] <case:trivial-tensor-summand-dual-isomorphism>],
    [
      #case[$p divides.not dim_K N$.]
      <case:trivial-tensor-summand-prime-to-p-dimension>
    ],
  )
  Further, if parts~@case:trivial-tensor-summand-dual-isomorphism and
  @case:trivial-tensor-summand-prime-to-p-dimension hold, then the multiplicity
  of $K$ as direct summand of $M times.o N$ is precisely $1$.
] <th:benson-carlson-trivial-tensor-summand>
#proof[
  By @th:absolute-indecomposable-group-module-criterion, $M$ and $N$ are
  absolutely indecomposable. To determine whether $K divides (M times.o N)$, we
  may replace $K$ by its algebraic closure by virtue of
  @th:field-extension-direct-summand-descent, so assume for the rest of the
  proof that $K$ is algebraically closed. We have $K divides (M times.o N)$ if
  and only if there exist $K$-homomorphisms
  $ K arrow.r M times.o N arrow.r K $
  whose composite is nonzero. Using the isomorphisms
  @eq:green-algebra-intertwining-duality
  $
    op("inv")_G M times.o N tilde.equiv op("Hom")_(K G) lr((N^*,M)), quad
    op("inv")_G lr((M times.o N))^* tilde.equiv op("Hom")_(K G) lr((M,N^*)),
  $
  it suffices to determine whether the composite map $j i != 0$, where
  $
    op("Hom")_(K G) lr((N^*,M)) arrow.r^i M times.o N
    arrow.r^j {op("Hom")_(K G) lr((M,N^*))}^*.
  $
  The $K$-homomorphisms $i,j$ are injective and surjective, respectively, and
  can be described explicitly as follows: let
  $
    N=plus.o.big_(i=1)^d K n_r, quad
    N^*=plus.o.big_(s=1)^d K phi_s, quad
    "where" phi_s lr((n_r))=delta_(r s).
  $
  Then for $g in op("Hom")_(K G) lr((N^*,M))$, and
  $h in op("Hom")_(K G) lr((M,N^*))$, we have
  $
    i(g)=sum_r g(phi_r) times.o n_r, quad
    {j(m times.o n)} h=h(m) n.
  $
  Therefore
  $
    {(j i)(g)} h=sum_r {h g(phi_r)} n_r
    ="trace of" h g "acting on" N^*.
  $
  #source(924)
  It follows that $j i != 0$ if and only if the composite map
  $
    eta:op("Hom")_(K G) lr((N^*,M)) times.o_K
    op("Hom")_(K G) lr((M,N^*)) arrow.r^tau E(N^*)
    arrow.r^(op("trace")) K
  $
  is not the zero map, where $tau(g times.o h)=h g$, and where
  $E(N^*)=op("End")_(K G) N^*$. Now $E(N^*) tilde.equiv E(N)$, and
  $E(N) slash op("rad") E(N) tilde.equiv K$, so
  $ E(N^*)=K dot 1+op("rad") E(N^*). $
  Since each element of $op("rad") E(N^*)$ is nilpotent (and thus has trace
  $0$), we see that
  $ {op("trace") y:y in E(N^*)}=K dot d, quad "where" d=dim_K N. $
  If $p divides d$, then necessarily $K dot d=0$ and $j i=0$, so
  $K divides.not (M times.o N)$. Suppose hereafter that $p divides.not d$; then
  $j i != 0$ if and only if there exist elements $h,g$ for which
  $h g in op("Aut")_(K G) lr((N^*))$. Such elements exist if and only if
  $N^* divides M$, or equivalently (since $M$ is indecomposable)
  $N^* tilde.equiv M$. This proves the first part of the theorem.

  Now suppose that parts~@case:trivial-tensor-summand-dual-isomorphism and
  @case:trivial-tensor-summand-prime-to-p-dimension are satisfied. If
  $K^((2)) divides (M times.o N)$, then $dim_K op("im")(j i)>1$. This means that
  there exist $K$-subspaces of $op("Hom")_(K G) lr((N^*,M))$ and
  $op("Hom")_(K G) lr((M,N^*))$, of dimension $>1$, on which the map $eta$ is a
  nonsingular pairing. Thus there is a subspace of $op("Hom")_(K G) lr((N^*,M))$
  of dimension $>1$, each nonzero element of which is an isomorphism. This is
  impossible since $tilde(E) lr((N)) tilde.equiv K$, and the proof is complete.
]

#corollary[
  Let $M,N in op("Ind") K G$ be distinct. Then $K divides.not M times.o N^*$.
] <cor:distinct-indecomposable-tensor-no-trivial-summand>
#proof[
  Let $E$ be an algebraic closure of $K$, and denote $E times.o_K M$ by $E M$
  for brevity. If $K divides M times.o N^*$, then
  $E divides (E M) times.o (E N)^*$. Writing $E M$ and $E N$ as direct sums of
  absolutely indecomposable $E G$-modules, it follows from
  @th:benson-carlson-trivial-tensor-summand that $E M$ and $E N$ must have a
  common direct summand. But then $M$ and $N$ have a common summand, by the
  proof of @th:field-extension-direct-summand-descent, so $M tilde.equiv N$.
]

#corollary[
  Let $M$ be an absolutely indecomposable $K G$-module such that
  $p divides dim_K M$. Then for every $K G$-module $N$ and every $K G$-direct
  summand $U$ of $M times.o N$, we have $p divides dim_K U$.
] <cor:absolutely-indecomposable-p-divisible-tensor-summands>
#proof[
  Assume $U divides M times.o N$ and $p divides.not dim_K U$. Then
  $K divides U^* times.o U$ by the discussion preceding
  @eq:endomorphism-trace-trivial-summand, and thus $K$ is a direct summand of
  $U^* times.o M times.o N$, that is, of $M times.o (U^* times.o N)$. Passing to
  an algebraic closure of $K$ and using
  @th:benson-carlson-trivial-tensor-summand, it follows that
  $p divides.not dim_K M$. This is a contradiction, and completes the proof.
]

It will be convenient to introduce some temporary terminology. A $K G$-module
$M$ will be called a _$p$-module_ if for each field $K' supset.eq K$ and each
$K' G$-direct summand $X$ of $K' M$, we have $p divides dim_(K') X$.
#idx("p-module")
It is clear that direct sums (or direct summands) of $p$-modules are again
$p$-modules. It follows readily from
@th:absolute-indecomposable-group-module-criterion that if $E$ is an algebraic
closure of $K$, and $M$ is a $K G$-module, then $M$ is a $p$-module if and
#source(925)
only if $E M$ is a $p$-module. By @th:field-extension-direct-summand-descent and
@th:benson-carlson-trivial-tensor-summand, we obtain at once:
$ K divides.not M times.o M^* "if and only if" M "is a" p "-module." $
<eq:p-module-trivial-tensor-summand-criterion>

We now define
$
  a(G,p)=sum_(M=p "-module") ZZ[M], quad
  A(G,p)=sum_(M=p "-module") CC[M],
$
<eq:p-divisible-representation-ideals>
where $M$ ranges over all $K G$-modules that are $p$-modules. Following
Benson-Carlson, we prove: #proposition[
  $a(G,p)$ and $A(G,p)$ are ideals of the rings $a(G)$ and $A(G)$, respectively.
  Further, #named-equation(name: [$(ast)$])[
    $ a(G,p)=A(G,p) inter a(G). $
  ] <eq:p-module-ideal-integral-intersection>
] <prop:p-module-representation-ideals>
#proof[
  Let the $K G$-module $M$ be a $p$-module; we must show that for any
  $K G$-module $N$, $M times.o N$ is also a $p$-module. Replacing $K$ by an
  algebraic closure, and changing notation, it suffices to establish the result
  for $M$ absolutely indecomposable. But then the result holds by
  @cor:absolutely-indecomposable-p-divisible-tensor-summands. Thus, $a(G,p)$ is
  an ideal of $a(G)$, and $A(G,p)=CC times.o_ZZ a(G,p)$. Since $a(G,p)$ has as
  $ZZ$-basis all $p$-modules in the set $op("Ind") K G$, it is clear that
  $a(G,p)$ is a $ZZ$-direct summand of $a(G)$. Assertion
  @eq:p-module-ideal-integral-intersection is now obvious.
]

#theorem(title: [Benson-Carlson])[
  The ring $A(G) slash A(G,p)$ has no nilpotent elements (except $0$).
] <th:benson-carlson-p-module-quotient-reduced>
#idx(
  "Benson-Carlson Theorem",
  target: [@th:benson-carlson-p-module-quotient-reduced],
)
#proof[
  For $x in A(G)$, write $K divides x$ to indicate that the trivial $G$-module
  $K$ appears in $x$ with nonzero coefficient. Clearly $K divides.not x$ for any
  $x in A(G,p)$.

  Now define an involution $x arrow.r x'$ on $A(G)$, by the formula
  $
    {sum xi_(i) [M_i]}'=sum overline(xi)_(i) [M_i^*], quad
    xi_i in CC, quad M_i=K G "-module",
  $
  where $overline(xi)_i=$ complex conjugate of $xi_i$. We claim that for
  $x in A(G)$,
  $ x x' in A(G,p) => x in A(G,p). $
  <eq:p-module-ideal-conjugate-dual-detection>
  Let us write
  $
    x=sum_i a_(i)[M_i], quad a_i in CC, quad a_i != 0, quad
    M_i in op("Ind") K G,
  $
  with the ${M_i}$ distinct. Then
  $ x x'=sum_(i,j) a_i overline(a)_(j) [M_i times.o M_j^*], $
  #source(926)
  For $i != j$, $K divides.not M_i times.o M_j^*$ by
  @cor:distinct-indecomposable-tensor-no-trivial-summand. Further,
  $K divides.not x x'$, since $x x' in A(G,p)$. It follows that for each $i$,
  $K divides.not M_i times.o M_i^*$, and thus $M_i$ is a $p$-module by
  @eq:p-module-trivial-tensor-summand-criterion. This establishes
  @eq:p-module-ideal-conjugate-dual-detection.

  We now prove that $A(G) slash A(G,p)$ has no nonzero nilpotent elements, and
  it suffices to show that there are no such elements whose square is $0$. So
  let $x in A(G)$ be such that $x^2 in A(G,p)$, and put $y=x x'$. Then
  $y y'=x^2 lr((x'))^2 in A(G,p)$, and thus $y in A(G,p)$ by
  @eq:p-module-ideal-conjugate-dual-detection. But then $x in A(G,p)$ by
  @eq:p-module-ideal-conjugate-dual-detection, and the proof is finished.
]

Let us define
$ A(G,"Cyc")=sum_M CC[M]. $
where $M$ ranges over all indecomposable $K G$-modules having a cyclic vertex.
(Of course, if $G$ has a cyclic Sylow $p$-subgroup, then every
$M in op("Ind") K G$ has cyclic vertex, so in this case $A(G,"Cyc")$ coincides
with $A(G)$.) Note that $A(G,"Cyc")$ is a f.d. $CC$-algebra, since cyclic groups
have only finitely many distinct indecomposable $K$-representations, and since
the tensor product of modules of cyclic vertex is a direct sum of such modules.
Our aim is to prove: #theorem(name: "Benson-Carlson Theorem")[
  $A(G,"Cyc")$ is a f.d. semisimple $CC$-algebra.
] <th:benson-carlson-cyclic-vertex-semisimplicity>

Since $A(G,"Cyc")$ is f.d./$CC$, it will suffice to prove that it contains no
nonzero nilpotent elements. The proof will depend on the Conlon Theorems in
§~@ss:conlon-representation-ring-theorems. We begin with: #lemma[
  Let $K$ be an algebraically closed field of characteristic $p>0$, and let
  $H=P times.r C$ be a $p$-hypo-elementary group, where $P$ is a nontrivial
  cyclic $p$-group, and $C$ is a cyclic $p'$-group. Let $P_1$ be the unique
  subgroup of $P$ of index $p$, and set $H_1=P_1 times.r C$. Then
  $ A(H,p)=op("ind")_(H_1)^H A(H_1). $
] <lem:cyclic-hypoelementary-p-module-induction>
#proof[
  From @i:prop:cyclic-normal-sylow-indecomposables we have
  $ K C=plus.o.big_(i=1)^r F_i, quad dim_K F_i=1, $
  $
    K H_1=plus.o.big_i V_i, quad V_i=(F_i)^(H_1), quad
    K H=plus.o.big_i U_i, quad U_i=(F_i)^H,
  $
  and the ${V_i}$ are the P.I.M.'s for $H_1$, while the ${U_i}$ are those for
  $H$. The indecomposable $K H$-modules ${M_(i j)}$ are given by
  $
    M_(i j)=U_i slash lr(((x-1)^j U_i)), quad 1 <= i <= r, quad
    1 <= j <= p^d=abs(P), quad P=chevron.l x chevron.r.
  $
  Then $dim M_(i j)=j dim F_i=j$, and $d >= 1$ by hypothesis. Then $M_(i j)$ is
  a $p$-module if
  #source(927)
  and only if $p divides j$. For such $j$, write $j=p n$ with
  $1 <= n <= p^(d-1)$. Then
  $
    M_(i j)=U_i slash lr(((x^p-1)^n U_i)) tilde.equiv
    op("ind")_(H_1)^H lr((V_i slash lr(((x^p-1)^n V_i))))
    in op("ind")_(H_1)^H A(H_1),
  $
  which gives the desired result.
]

#corollary[
  Keep the above notation, but drop the hypotheses that $K$ be algebraically
  closed and that $P != 1$. Then $A(K H)$ has no nonzero nilpotent elements.
] <cor:cyclic-hypoelementary-representation-algebra-reduced>
#proof[
  Let $E$ be an algebraic closure of $K$. By
  @prop:scalar-extension-representation-ring-embedding, $A(K H)$ embeds in
  $A(E H)$, so it suffices to show that $A(E H)$ has no nonzero nilpotent
  elements. Changing notation, for the rest of the proof we may assume that $K$
  is algebraically closed.

  If $P=1$, then $H$ is a $p'$-group, and $A(H)$ is isomorphic to the ring of
  class functions on $H$, hence semisimple. Now use induction on $abs(H)$, and
  let $P != 1$. By @th:representation-induction-restriction-ideal-decomposition
  we have
  $
    A(H) & =op("ind")_(H_1)^H A(H_1) plus.o {x in A(H):x_(H_1)=0} \
         & =A(H,p) plus.o "kernel of" op("res")_(H_1)^H.
  $
  The restriction map $op("res")_(H_1)^H$ is thus a ring monomorphism of
  $A(H,p)$ into $A(H_1)$, so by the induction hypothesis, $A(H,p)$ has no
  nonzero nilpotent elements. On the other hand, $A(H) slash A(H,p)$ has no
  nonzero nilpotent elements by @th:benson-carlson-p-module-quotient-reduced. It
  follows that the same holds for $A(H)$, as desired.
]

We are now ready to complete the proof of the Benson-Carlson Theorem. Given the
group $G$, denote by $cal(H)_c$ a full set of nonconjugate $p$-hypo-elementary
subgroups $H <= G$ such that $O_p lr((H))$ is cyclic. Then $A(H)$ has no nonzero
nilpotent elements for $H in cal(H)_c$, by
@cor:cyclic-hypoelementary-representation-algebra-reduced. We need only show
that there is a ring monomorphism (given by restriction maps)
$ A(G,"Cyc") arrow.r product_(H in cal(H)_c) A(H), $
that is, if $x in A(G,"Cyc")$ satisfies the condition that $x_H=0$ for all
$H in cal(H)_c$, then $x=0$. By Conlon's Theorem
@th:conlon-relative-projective-ideal-decomposition, we may write
$ x=sum_D x(D), quad "where" x(D) in A''(G,D), $
with $D$ ranging over a full set of nonconjugate $p$-subgroups of $G$. #idx(
  "Conlon's Theorem",
) Each nonzero $x(D)$ contains terms of vertex $D$, and it follows that $x(D)=0$
for noncyclic $D$, since $x in A(G,"Cyc")$.

Now let $D$ range over cyclic $p$-subgroups of $G$. By
@prop:conlon-vertex-hypoelementary-restriction, for each $D$ there is a
monomorphism
$ A''(G,D) arrow.r product_(H <= G \ O_p lr((H))=D) A''(H,D), $
#source(928)
where $H$ ranges over $p$-hypo-elementary subgroups of $G$ for which
$O_p lr((H))=D$. Each such $H$ lies in $cal(H)_c$, so the composite map
$
  product_(D "cyclic") A''(G,D) arrow.r
  product_D product_(H <= G \ O_p lr((H))=D) A''(H,D) arrow.r
  product_(H in cal(H)_c) A''(H)
$
is a monomorphism. Since $x=sum x(D)$, with $x(D) in A''(G,D)$, it follows that
if $x_H=0$ for all $H in cal(H)_c$, then necessarily $x=0$. This completes the
proof of the Benson-Carlson Theorem
@th:benson-carlson-cyclic-vertex-semisimplicity.

In particular, if $G$ has a cyclic Sylow $p$-subgroup, then $A(G)=A(G,"Cyc")$,
as remarked above. Thus from @th:benson-carlson-cyclic-vertex-semisimplicity we
obtain as a corollary: #theorem(name: "O'Reilly's Theorem")[
  If $G$ has a cyclic Sylow $p$-subgroup, then $A(G)$ is a f.d. semisimple
  $CC$-algebra.
] <th:oreilly-cyclic-sylow-representation-algebra-semisimple>
#idx(
  "O'Reilly's Theorem",
  target: [@th:oreilly-cyclic-sylow-representation-algebra-semisimple],
)

Benson-Carlson give the following example to show that even though the algebra
$A(G) slash A(G,p)$ has no nonzero nilpotent elements, its structure may
nevertheless be quite complicated. Let $op("char") K=p>2$, where $K$ is an
infinite field, and let $G$ be an elementary abelian $p$-group with generators
$x$ and $y$. For each $a in K$, let
$
  M_a=K G slash I_a, quad "where"
  I_a=K G(x-1)(y-1)+K G((y-1)^2-a(x-1)^(p-1)).
$
Then $dim_K M_a=p+1$, and the ${M_a:a in K^times}$ are distinct nonisomorphic
modules. For $a != 0$, it turns out that $[M_a]^2=1$ in $A(G) slash A(G,p)$, so
this quotient ring is an infinite-dimensional $CC$-algebra containing infinitely
many elements of order $2$.

=== Nilpotent Elements in Representation Algebras
<ss:representation-algebra-nilpotent-elements>

Throughout let $K$ be a field, $op("char") K=p>0$, and consider $K G$-modules,
writing $A(G)$ instead of $A(K G)$. Let $Omega$ be the Heller operator as in
§~@sec:auslander-reiten-sequences. Thus, for each $G$-module $M$ there is a
$G$-ses
$ 0 arrow.r Omega M arrow.r P arrow.r M arrow.r 0, $
where $P$ is a projective cover of $M$. Tensoring with an arbitrary $G$-module
$N$, and using the fact that $P times.o N$ is projective, we obtain
$ Omega M times.o N tilde.equiv Omega(M times.o N) plus.o "proj", $
<eq:heller-tensor-projective-summand>
where “proj” indicates a projective $K G$-module.

To construct nilpotent elements in $A(G)$, we begin with a simple generalization
of Schanuel's Lemma: #lemma[
  Consider a pair of ses's of $G$-modules:
  #source(929)
  $
    0 arrow.r W_1 arrow.r U_1 arrow.r^sigma V arrow.r 0, quad
    0 arrow.r W_2 arrow.r P_2 arrow.r^mu V arrow.r 0,
  $
  where $P_2$ is projective, and where $sigma$ factors through a projective
  module. Then
  $ W_1 plus.o P_2 tilde.equiv W_2 plus.o U_1. $
] <lem:projective-factor-schanuel-pullback>
#proof[
  Consider a diagram

  #projective-factor-pullback-diagram()

  with $P_1$ projective, and $sigma,tau$ surjective. We may choose $beta$ so
  that $sigma=mu beta alpha$, and then we put
  $ X={(u,v) in U_1 plus.o P_2:sigma(u)=mu(v)}, $
  the pullback of the pair of maps $sigma,mu$. Since $sigma$ is surjective,
  there is an exact sequence
  $ 0 arrow.r ker sigma arrow.r X arrow.r P_2 arrow.r 0, $
  and therefore $X tilde.equiv W_1 plus.o P_2$. On the other hand, the
  surjection $X arrow.r U_1$, given by $(u,v) arrow.r u$, is split by the map
  $u in U_1 arrow.r (u,beta alpha u) in X$. Therefore
  $X tilde.equiv U_1 plus.o W_2$, and the lemma is proved.
]

#lemma[
  Let $K$ be the trivial $G$-module, and let
  $ 0 arrow.r L arrow.r Omega^2 K arrow.r^zeta K arrow.r 0 $
  be exact, where $Omega$ is the Heller-operator. Let $M$ be a $G$-module such
  that the map
  $ zeta times.o 1:Omega^2 K times.o M arrow.r K times.o M tilde.equiv M $
  factors through a projective module. Then there exist projective modules
  $E,E'$ such that
  $ (L times.o M) plus.o E tilde.equiv Omega M plus.o Omega^2 M plus.o E'. $
] <lem:carlson-kernel-tensor-syzygy-relation>
#proof[
  There are exact sequences
  $
    0 arrow.r L times.o M arrow.r Omega^2 K times.o M
    arrow.r^(zeta times.o 1) M arrow.r 0, quad
    0 arrow.r Omega M arrow.r P arrow.r M arrow.r 0,
  $
  #source(930)
  where $P$ is a projective cover of $M$. By
  @lem:projective-factor-schanuel-pullback, the hypothesis implies that
  $ (L times.o M) plus.o P tilde.equiv Omega M plus.o (Omega^2 K times.o M). $
  But, by @eq:heller-tensor-projective-summand,
  $ Omega^2 K times.o M=Omega^2 lr((K times.o M)) plus.o "proj" $
  which gives the result.
]

#remark[
  Using the identification
  $op("Hom")(Omega^2 K,K) tilde.equiv op("Ext")^2 lr((K,K))$, $zeta$ determines
  an element $hat(zeta) in op("Ext")^2 lr((K,K))$. Then $hat(zeta)$ acts (via
  cup product) on the cohomology ring $op("Ext")^* lr((M,M))$, and
  $zeta times.o 1$ factors through a projective if and only if
  $hat(zeta) dot op("Ext")^* lr((M,M))=0$.
] <rem:carlson-kernel-cohomology-annihilation>

#corollary[
  Let $G$ be a $p$-group, and let $zeta:Omega^2 K arrow.r K$ be a surjection
  with kernel $L$. Assume that
  #case-list(
    [
      #case[the map $zeta times.o 1:Omega^2 K times.o L arrow.r L$ factors
        through a projective and]
      <case:carlson-square-zero-projective-factor>],
    [
      #case[$L ≇ Omega L$, $L tilde.equiv Omega^2 L$, and
        $dim L=dim Omega L$.] <case:carlson-square-zero-period-dimension>
    ],
  )
  Then $[L]-[Omega L]$ is a nonzero element of $A(G)$ whose square is $0$.
] <cor:carlson-periodic-kernel-square-zero>
#proof[
  In $A(G)$ we have
  $
    ([L]-[Omega L])^2=[L times.o L]-2[L times.o Omega L]
    +[Omega L times.o Omega L].
  $
  Since $dim L=dim Omega L$, the right-hand side has dimension $0$. Further,
  projectives are free since $G$ is a $p$-group, so it suffices to show that the
  right-hand side is $0$ modulo projectives. But by
  @lem:carlson-kernel-tensor-syzygy-relation we have
  $ L times.o L tilde.equiv Omega L plus.o Omega^2 L plus.o "proj", $
  and by @eq:heller-tensor-projective-summand,
  $
    L times.o Omega L tilde.equiv Omega(L times.o L) plus.o "proj", quad
    Omega L times.o Omega L tilde.equiv Omega^2 lr((L times.o L)) plus.o "proj",
  $
  and the desired result follows since $L tilde.equiv Omega^2 L$.
]

We shall apply this result to the special case where
$G=chevron.l x,y:x^p=y^p=1,x y=y x chevron.r$ is a $(p,p)$-group, with $p>2$.
There is an exact sequence
$
  0 arrow.r Omega^2 K arrow.r K G plus.o K G arrow.r^theta K G
  arrow.r^epsilon K arrow.r 0,
$
<eq:elementary-abelian-two-generator-resolution>
where $epsilon$ is the augmentation map, and where
$ theta(xi, eta)=xi(x-1)+eta(y-1) quad "for" xi,eta in K G. $

#source(931)
Therefore $ker theta$ is generated by
$ a_0=(0,N_y), quad a_1=(-(y-1),x-1), quad a_2=(N_x,0), $
where $N_x=1+x+dots+x^(p-1)=(x-1)^(p-1)$, and the generators satisfy the
relations
$ (x-1) a_0=N_y a_1, quad (y-1) a_2=-N_x a_1. $
(See Exercise @exc:elementary-abelian-syzygy-generators.)

Now let
$ 0 arrow.r L arrow.r Omega^2 K arrow.r^zeta K arrow.r 0 $
be exact, where $zeta$ is given by
$ a_0 arrow.r 1, quad a_1 arrow.r 0, quad a_2 arrow.r alpha, $
for some fixed parameter $alpha in K$. Then $L$ is the submodule of $Omega^2 K$
generated by
$ a_1=(-(y-1),x-1) quad "and" quad b_1=(N_x,-alpha N_y). $
We show that there is an exact sequence
$
  0 arrow.r L arrow.r K G plus.o K G arrow.r^f K G plus.o K G
  arrow.r^g L arrow.r 0,
$
<eq:carlson-kernel-two-periodic-resolution>
where $g(xi,eta)=xi b_1+eta a_1$. Define
$ f(rho,sigma)=((x-1) rho+(y-1) sigma,alpha N_y rho+N_x sigma), $
so $f(L)=0$ and $g f=0$. We claim that $L=ker f$. Let $(rho,sigma) in ker f$;
then $(x-1) rho+(y-1) sigma=0$, so $(rho,sigma) in Omega^2 K$, and we may write
$
  (rho,sigma)=t_0 a_0+t_1 a_1+t_2 a_2
  =(t_2 N_x,t_0 N_y)+t_1 a_1.
$
From $alpha N_y rho+N_x sigma=0$ we obtain $(alpha t_2+t_0) N_x N_y=0$, and thus
$t_0=-alpha t_2+u$ for some $u$ in the augmentation ideal of $K G$. Therefore
$ (rho,sigma)=t_2 lr((N_x,-alpha N_y))+t_1 a_1+(0,u N_y). $
Since for $i >= 1$,
$ (0,(x-1)^i N_y)=(x-1)^(i-1) N_y lr((-(y-1),x-1)) in L, $
it follows that $(rho,sigma) in L$. This shows that $ker f=L$, so comparing
$K$-dimensions we obtain $op("im") f=ker g$, and the sequence is exact.

#source(932)
We may represent $L$ by a picture, in which the lattice points form a $K$-basis
for $L$, and where the diagonals represent multiplication by $x-1$ and $y-1$,
respectively. We illustrate the case $p=3$ below:

#carlson-kernel-lattice()


In general, we have $dim L=dim Omega^2 K-1=p^2$. We leave it as exercise for the
reader to show that $L$ is indecomposable as $K G$-module. It follows from
@eq:carlson-kernel-two-periodic-resolution that $Omega^2 L tilde.equiv L$, and
further that $Omega L tilde.equiv ker g tilde.equiv op("im") f$. Thus, $Omega L$
is generated by
$ c_1=(x-1,alpha N_y), quad d_1=(y-1,N_x), $
and $dim Omega L=dim(K G plus.o K G)-dim L=p^2$. The picture of $Omega L$ for
$p=3$ is given by

#carlson-omega-kernel-lattice()


For $p > 2$, to distinguish $L$ from $Omega L$ for every $alpha$, put $X=x-1$,
$Y=y-1$, $A=K G=K[X,Y] slash (X^p,Y^p)$, and $J=(X,Y)$. The maps in
@eq:carlson-kernel-two-periodic-resolution have their entries in $J$; the free
cover of $L$ sends its basis to $(b_1,a_1)$, and
$Omega L tilde.equiv A c_1+A d_1$ is its minimal syzygy. Now
$ X b_1=-alpha Y^(p-1) a_1, quad Y b_1=-X^(p-1) a_1, $
both of which belong to $J^2 L$. Thus $J L slash J^2 L$ is generated by
$X a_1,Y a_1$. Their independent degree-$2$ coordinate vectors remain
independent modulo $J^2 L$, whose coordinates have degree at least $3$; hence
$dim_K lr((J L slash J^2 L))=2$.

For $Omega L$, we have $Y c_1=X d_1=(X Y,0)$. The radical layer is generated by
$X c_1,Y c_1,Y d_1$, whose first coordinates are $X^2,X Y,Y^2$. They are
independent modulo $J^2 Omega L$, whose first coordinates have degree at least
$3$, since $p>2$. Therefore $dim_K lr((J Omega L slash J^2 Omega L))=3$, and $L$
is not isomorphic to $Omega L$ for any $alpha$.
#ed-note[
  For $alpha != 0$, the asserted split quotient would require an element
  $r in A$ with $r X Y=0$ and $r X^2=alpha X Y^(p-1)$. These equations are
  incompatible with the monomial basis of $A$. The drawings record short chains
  and do not display all the parameter-dependent long relations; the radical
  layers distinguish the modules for every $alpha$.
]
(But $L tilde.equiv Omega L$ when $p=2$!)

It remains to prove that the $K G$-surjection
$
  zeta times.o 1:Omega^2 K times.o L arrow.r K times.o L tilde.equiv L, quad
  u times.o l arrow.r zeta(u) l,
$
factors through a projective. Consider the diagram

#carlson-resolution-comparison()

#source(933)
where the bottom row is obtained by applying $ast times.o L$ to the exact
sequence
$ 0 arrow.r Omega^2 K arrow.r W_1 arrow.r W_0 arrow.r K arrow.r 0 $
obtained from a minimal projective resolution of $K$. (Here, $W_0=K G$,
$W_1=(K G)^((2))$.) One can then find maps ${mu_i}$ making the diagram commute
(see Benson–Carlson~@bib:Benson1986, Lemma~4.5). It turns out that
$(zeta times.o 1) compose mu_2$ is the zero map from $L$ to $L$. Thus, in the
diagram

#carlson-extension-pushout()

the bottom row represents the element $hat(zeta) dot op("id")_L$ in
$op("Ext")^2 lr((L,L))$, and is zero in $op("Ext")^2 lr((L,L))$. (See
@rem:carlson-kernel-cohomology-annihilation.) Thus $zeta times.o 1$ factors
through a projective, as claimed.

As shown by Zemanek~@bib:Zemanek1971, if the above group $G$ is a Sylow
$p$-subgroup of $G_0$, then the element
$[L^(G_0)]-[(Omega L)^(G_0)] in A(K G_0)$ is nonzero and has square $0$. To
summarize the results known up to this point, we have: #theorem[
  Let $K$ be a field, $op("char") K=p>0$. Let $G$ be an arbitrary group, and $P$
  a Sylow $p$-subgroup of $G$.
  #case-list(
    [
      #case[If $P$ is cyclic, then $A(K G)$ has no nilpotent elements except
        $0$.] <case:green-algebra-cyclic-sylow-reduced>],
    [
      #case[Assume $P$ is noncyclic. If $p>2$, or if $p=2$ and $P$ is not an
        elementary abelian $2$-group, then $A(K G)$ contains nonzero nilpotent
        elements.$ast$]
      <case:green-algebra-noncyclic-sylow-nilpotents>],
    [
      #idx(
        "Zemanek's Theorem",
        target: [@case:green-algebra-noncyclic-sylow-nilpotents],
      )
      #case[If $p=2$ and $P$ is a $(2,2)$-group, then $A(K G)$ contains no
        nonzero nilpotent elements.]
      <case:green-algebra-klein-four-sylow-reduced>
    ],
  )
] <th:modular-green-algebra-nilpotent-classification>

Assertion @case:green-algebra-cyclic-sylow-reduced is O'Reilly's Theorem
@th:oreilly-cyclic-sylow-representation-algebra-semisimple. Part
@case:green-algebra-noncyclic-sylow-nilpotents is due to
Zemanek~@bib:Zemanek1971, @bib:Zemanek1973, and is re-proved by
Benson–Carlson~@bib:Benson1986 for the special case $G=P$. Part
@case:green-algebra-klein-four-sylow-reduced is due to Conlon~@bib:Conlon1966.

The situation changes drastically when $K$ is replaced by a $p$-adic ring $R$,
i.e., a complete d.v.r. in a finite extension of $QQ_p$. Let $ZZ_p$ denote the
ring of $p$-adic integers in $QQ_p$. #theorem[
  Let $R$ be a $p$-adic ring with maximal ideal $pi R$.
  #case-list(
    [
      #case[Assume that $G$ contains an element of order $n$, where
        $n in pi^2 R$ if $p>2$, and $n in 2 pi R$ if $p=2$. Then $A(R G)$
        contains nonzero nilpotent elements. On the other hand, if $p$ exactly
        divides $abs(G)$, then $A(ZZ_p G)$ contains no nonzero nilpotent
        elements.] <case:padic-green-algebra-order-nilpotents>],
    [
      #idx(
        "Reiner's Theorem",
        target: [@case:padic-green-algebra-order-nilpotents],
      )
      #case[If $G$ has a noncyclic Sylow $p$-subgroup, then $A(ZZ_p G)$ contains
        nonzero nilpotent elements.]
      <case:padic-green-algebra-noncyclic-sylow-nilpotents>
      #idx(
        "Zemanek's Theorem",
        target: [@case:padic-green-algebra-noncyclic-sylow-nilpotents],
      )
    ],
  )
] <th:padic-green-algebra-nilpotents>

Part @case:padic-green-algebra-order-nilpotents is due to
Reiner~@bib:Reiner1966a, while
part~@case:padic-green-algebra-noncyclic-sylow-nilpotents is proved in
Zemanek~@bib:Zemanek1971.

#source(934)
#exercises-heading

#exercise[
  For $x in A(K G)$, define its _contragredient_ $x^*$ as follows: if
  $x=sum xi_(i) [M_i]$, $xi_i in CC$, $M_i in op("Ind") K G$, then
  $ x^*=sum xi_(i) [M_i^*], $
  where $M_i^*$ is the contragredient of $M_i$. Prove that for $x,y in A(K G)$
  we have
  $ (x,y)_G=(y^*,x^*)_G, $
  where $(x,y)_G$ is the pairing defined in @eq:green-algebra-hom-pairing.
] <exc:green-hom-pairing-contragredients>

#exercise[
  For each $M in op("Ind") K G$, let $hat(M) in A(K G)$ be its dual, as in
  @th:benson-parker-green-algebra-duality. Prove that for $N in op("Ind") K G$,
  $ (hat(M)^*,N^*)_G=delta_(M N). $
  Thus, each $L in op("Ind") K G$ has a left dual $(hat(L^*))^*$ as well as a
  right dual $hat(L)$.
] <exc:green-algebra-left-duals-by-contragredients>

#exercise[
  Show that for $M in op("Ind") K G$, the element $hat(M) in A(K G)$ is uniquely
  determined by the formula
  $ (N,hat(M))_G=delta_(M N) quad "for" N in op("Ind") K G. $
] <exc:green-algebra-right-dual-uniqueness>

#exercise[
  Let $M in op("Ind") K G$, and let $phi:E arrow.r M$ be a surjection. For $X$
  any $K G$-module, let $cal(P)(X)$ be the following statement:

  Each $f in op("Hom")_(K G) lr((X,M))$ that is not a split surjection must
  factor through $E$.

  Show that if $cal(P)(X)$ holds for every $X in op("Ind") K G$, then
  $cal(P)(Y)$ holds for every $K G$-module $Y$.
] <exc:ar-factorization-indecomposable-test>
#hint([@exc:ar-factorization-indecomposable-test])[
  Let $f:Y arrow.r M$, and write $Y=product.co X_i$ as a sum of indecomposable
  modules ${X_i}$. Then $f=product.co f_i$, where $f_i:X_i arrow.r M$. For each
  $i$, $f_i$ is not an isomorphism, otherwise $f$ can be split. Then each $f_i$
  factors through $E$, whence so does $f$.
] <hint:ar-factorization-indecomposable-test>

#exercise[
  Show that there exist left duals $caron(L)$ of indecomposable $K G$-modules
  $L$ analogous to the right duals given in
  @th:benson-parker-green-algebra-duality. Explicitly, define
  $ caron(L)=[L]-[L slash lr((op("soc") L))] quad "if" L "is projective." $
  If $L$ is not projective, let
  $ 0 arrow.r L arrow.r E arrow.r Omega^(-2) L arrow.r 0 $
  be an AR$'$-sequence for $L$, and set
  $ caron(L)=[L]-[E]+[Omega^(-2) L]. $
  Prove that
  $ (caron(L),M)_G=delta_(L M) quad "for" M in op("Ind") K G. $
  #source(935)
  Show also that
  $ caron(L)=(hat(L^*))^* quad "for" L in op("Ind") K G, $
  where $ast$ denotes contragredient, and $hat$ the dual defined in
  @th:benson-parker-green-algebra-duality.
] <exc:green-algebra-left-dual-ar-description>

#exercise[
  Let $A$ be a f.d. $K$-algebra, and consider an ses of $A$-modules
  $0 arrow.r L arrow.r M arrow.r N arrow.r 0$. Prove that the sequence splits if
  and only if $M tilde.equiv L plus.o N$.
] <exc:exact-sequence-split-middle-isomorphism>
#hint([@exc:exact-sequence-split-middle-isomorphism], caption: [Hint
  (Auslander):])[
  If $M tilde.equiv L plus.o N$, then the sequence
  $
    0 arrow.r op("Hom")(N,L) arrow.r op("Hom")(N,M)
    arrow.r op("Hom")(N,N) arrow.r 0
  $
  is exact, by considering $dim_K$.
] <hint:exact-sequence-split-middle-isomorphism>

#exercise[
  Let
  $ 0 arrow.r A arrow.r B arrow.r C arrow.r 0 $
  be a ses of $K G$-modules, in which $A$ and $C$ are indecomposable. Suppose
  that #named-equation(name: [$(ast)$])[
    $ [A]-[B]+[C]=hat(M) $
  ] <eq:ar-sequence-class-characterization>
  for some nonprojective $M in op("Ind") K G$. Prove that $C tilde.equiv M$, and
  that the given sequence is the AR-sequence for $M$.
] <exc:ar-sequence-class-characterization>
#hint([@exc:ar-sequence-class-characterization])[
  Use @lem:ar-sequence-hom-cokernel-criterion.
] <hint:ar-sequence-class-characterization>

#exercise[
  Let
  $
    0 arrow.r M arrow.r E arrow.r N arrow.r 0, quad
    0 arrow.r N arrow.r E arrow.r M arrow.r 0
  $
  be a pair of AR-sequences of $K G$-modules. Prove that $M tilde.equiv N$.
] <exc:opposite-ar-sequences-same-middle>

#exercise[
  Keeping the notation of Exercise @exc:ar-sequence-class-characterization, drop
  the hypothesis that $A$ and $C$ are indecomposable, but suppose still that
  @eq:ar-sequence-class-characterization holds for some nonprojective
  indecomposable $M$. Deduce that the given sequence is the direct sum of the
  AR-sequence for $M$ and a split ses.
] <exc:ar-class-sequence-split-complement>

#exercise[
  Let $H <= G$, and let $M,N$ be $K H$-modules. Prove that
  $ M^G tilde.equiv N^G <=> M^G|_H tilde.equiv N^G|_H. $
] <exc:induced-module-restriction-isomorphism-detection>
#hint([@exc:induced-module-restriction-isomorphism-detection])[
  Use @th:benson-parker-restriction-induction-kernel-decomposition.
] <hint:induced-module-restriction-isomorphism-detection>

#exercise[
  Let $f:A(G) arrow.r CC$ be a species which factors through the subgroup
  $H <= G$. Show
  #case-list(
    [
      #case[If $H <=_G E <= G$, then $f$ factors through $E$.]
      <case:species-factorization-larger-subgroup>],
    [
      #case[Let $g$ be a species of $A(H)$ which fuses to $f$, and suppose that
        $g$ factors through a subgroup $H_0 <= H$. Show that $f$ factors through
        $H_0$.] <case:species-factorization-transitive>
    ],
  )
] <exc:species-factorization-transitivity>

#source(936)
#exercise[
  Let $G=chevron.l x chevron.r times chevron.l y chevron.r$ be an elementary
  abelian $(p,p)$-group, and let $op("char") K=p$. Put $N_x=1+x+dots+x^(p-1)$,
  and define $N_y$ analogously. Starting with the projective resolution
  $
    arrow.r K chevron.l x chevron.r arrow.r^(N_x) K chevron.l x chevron.r
    arrow.r^(x-1) K chevron.l x chevron.r arrow.r^(epsilon_1) K arrow.r 0.
  $
  and similarly for $chevron.l y chevron.r$, we may tensor the complexes (see
  Exercise @i:exc:outer-tensor-ext-kunneth) to obtain a projective resolution
  $
    arrow.r (K G)^((3)) arrow.r^(partial_3) (K G)^((2)) arrow.r K G
    arrow.r^epsilon K arrow.r 0
  $
  of the trivial $G$-module $K$. Then $Omega^2 K=op("im") partial_3$. Use this
  to determine generators for $Omega^2 K$, and relations connecting these
  generators. Show that $dim_K Omega^2 K=p^2+1$.
] <exc:elementary-abelian-syzygy-generators>
