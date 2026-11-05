#import "main-defs.typ": *
#import "note-layout.typ": reference-data
#import "main-defs.typ": number-text as reference-number-text
#import "statements.typ": *
#import "diagrams/78-auslander-reiten.typ": *

== Auslander–Reiten Sequences
<sec:auslander-reiten-sequences>

This section is intended to serve as an introduction to the extensive theory of
Auslander–Reiten sequences, with special emphasis on the case of group algebras.
The results for this case will be sufficiently powerful to yield significant
information about the Green ring of a group algebra (see
§~@ss:green-algebra-dual-elements). A full treatment of Auslander–Reiten
sequences over arbitrary rings is beyond the scope of this book.

The fundamental ideas leading to the theory of almost split sequences were first
introduced by M. Auslander, and played a key role in his generalization of
Roiter's proof of the first Brauer–Thrall conjecture (see
§~@sec:roiter-brauer-thrall-theorem). Later, Auslander and Reiten developed the
theory of almost split sequences from a module-#source(823)theoretic viewpoint,
rather than that of functor categories. These sequences are now called
Auslander–Reiten sequences.

The authors wish to thank P. Landrock and P. Webb for many helpful comments on
the material in this section.

In §~@ss:heller-loop-space-operator, we review the theory of the Heller
loop-space operator for modules over group algebras (see
§~@ss:cyclic-defect-periodic-resolutions), since this plays an important role in
our treatment of Auslander–Reiten sequences. The existence of such sequences,
for the group algebra case, is established in
§~@ss:auslander-reiten-group-algebras. In
§~@ss:auslander-reiten-finite-dimensional-algebras, we consider the general case
of f.d. algebras over a field.

Throughout this section, let $A$ be a ring. We assume once and for all that all
$A$-modules considered below are f.g./$A$. Denote by $cal(P)(A)$ the category of
f.g. projective $A$-modules, and $cal(I)(A)$ the category of f.g. injective
$A$-modules. Let $upright("Ind") A$ be the set of isomorphism classes of f.g.
indecomposable $A$-modules. We also write $M in upright("Ind") A$ to indicate
that $M$ is an indecomposable module. Thus,
$
  upright("Ind") A-cal(P)(A)="set of (isomorphism classes of) nonprojective" \
  "indecomposable" A"-modules",
$
while $upright("Ind") A inter cal(P)(A)$ is the set of projective indecomposable
$A$-modules, and so on.

=== Heller Loop-Space Operator
<ss:heller-loop-space-operator>

Throughout this subsection, let $A=K G$, where $K$ is a field and $G$ a finite
group. Consider only f.g. $A$-modules in what follows. Each left $A$-module $M$
determines a right $A$-module $M'$, called the #idx(
  "Dual of a module",
)_$K$-dual_ of $M$, given by
$ M'="Hom"_K lr((M,K)). $
The action of $G$ on $M'$ is defined by the formula
$ (f x)m=f(x m) quad "for all" f in M', quad x in G, quad m in M. $
We may also form the contragredient module $M^*$, which is a left $A$-module
whose underlying space is $M'$, and where $G$ acts by the rule
$ (x f)m=f(x^(-1)m) quad "for" f in M^*, quad x in G, quad m in M. $
We shall repeatedly use:

#proposition[
  Let $P$ be a f.g. projective left $A$-module. Then so is its contragredient
  $P^*$, while its $K$-dual $P'$ is a f.g. projective right $A$-module.
]<prop:group-algebra-projective-duals>

#proof[
  The result for contragredients follows from the isomorphism
  $ A^* ≅ A quad "as left" A"-modules" $
  #source(824)
  (see @i:cor:group-ring-self-contragredient). That for duals follows from the
  isomorphism
  $ (lmodule(A, A))' ≅ attach(A, br: A) quad "as right" A"-modules", $
  which holds since $A$ is a symmetric $K$-algebra by
  @i:prop:group-algebra-symmetric.
]

#corollary[
  A f.g. $A$-module is projective if and only if it is injective.
]<cor:group-algebra-projective-injective>

#proof[
  Taking contragredients reverses all arrows in a diagram.
]

Given an $A$-module $M$, we may write
$
  M=N_1 plus.o dots plus.o N_r plus.o P_1 plus.o dots plus.o P_s,
  quad N_i in upright("Ind") A-cal(P)(A),
  quad P_j in upright("Ind") A inter cal(P)(A).
$
Then we have $M=N plus.o P$, with $P in cal(P)(A)$, and where $N$ has no
projective direct summand. We shall call $N$ the #idx("Core")_core_ of $M$; it
is unique up to isomorphism, by the Krull–Schmidt–Azumaya Theorem. When $M=N$
and $P=0$, we call $M$ a core. In particular, each
$M in upright("Ind") A-cal(P)(A)$ is a core.

For any left $A$-module $M$, there is an exact sequence
$ 0 arrow N arrow P arrow M arrow 0 quad "with" P in cal(P)(A). $
Now define
$ Omega(M)="core of" N. $
By Schanuel's Lemma, the isomorphism class of $M$ uniquely determines that of
$Omega(M)$. The operator $Omega$, defined on isomorphism classes of $A$-modules,
is the #idx("Heller operator")_Heller loop-space operator_, introduced
previously in §~@ss:cyclic-defect-periodic-resolutions.

We leave it to the reader to verify the formulas
$
  Omega(M plus.o P) ≅ Omega(M), quad
  Omega(M plus.o N) ≅ Omega(M) plus.o Omega(N)
$
<eq:heller-operator-additivity-projective-invariance>
for all $A$-modules $M$ and $N$, and all $P in cal(P)(A)$. Next, we show:

#proposition[
  For $A=K G$, the loop-space operator $Omega$ gives a bijection from the set of
  isomorphism classes of cores onto itself, preserving indecomposability.
]<prop:heller-operator-core-bijection>

#proof[
  For any $A$-module $M$, there is an exact sequence
  $
    0 arrow Omega(M) plus.o P_0 arrow P_1 arrow M arrow 0
    quad "with" P_i in cal(P)(A).
  $
  Taking contragredients, we obtain a new exact sequence
  $ 0 arrow M^* arrow P_1^* arrow Omega(M)^* plus.o P_0^* arrow 0, $
  #source(825)
  and each $P_i^* in cal(P)(A)$. Therefore
  $ "core of" M^* ≅ Omega((Omega M)^*). $
  Suppose now that $M$ is a core; then so is $M^*$, by
  @prop:group-algebra-projective-duals, and we obtain
  $ M^* ≅ Omega((Omega M)^*) $
  in this case. Thus $Omega M$ determines $M^*$ (and hence $M$) up to
  isomorphism; further, every core $N$ is of the form $M^*$ for some $M$, and so
  $N in im Omega$. This completes the proof.
]

For any core $N$, we may write $N ≅ Omega M$ for some core $M$, unique up to
isomorphism; we denote this $M$ by $Omega^(-1) N$. For an arbitrary $A$-module
$X$, define $Omega^(-1) X=Omega^(-1) lr(("core of" X))$. The following result
will be used repeatedly:

#proposition[
  #case-list(
    numbering: "(i)",
    [#case[
      For any core $M$, there is an exact sequence
      $ 0 arrow Omega M arrow P_M arrow M arrow 0, $
      <eq:heller-projective-cover-sequence>
      where $P_M$ is a projective cover of $M$. In this sequence, $P_M$ is also
      an injective hull of $Omega M$.
    ]<case:heller-cover-injective-hull>],
    [#case[
      Dually, for each core $N$ there is an exact sequence
      $ 0 arrow N arrow I_N arrow Omega^(-1) N arrow 0, $
      <eq:heller-injective-hull-sequence>
      where $I_N$ is an injective hull of $N$; then $I_N$ is also a projective
      cover of $Omega^(-1) N$.
    ]<case:heller-hull-projective-cover>],
    [#case[
      Given any exact sequence of $A$-modules
      $ 0 arrow X arrow P arrow Y arrow 0 quad "with" P in cal(P)(A), $
      we have
      $ "core of" X ≅ Omega Y, quad "core of" Y ≅ Omega^(-1) X. $
    ]<case:heller-exact-projective-middle-cores>],
  )
]<prop:heller-projective-covers-injective-hulls>

#proof[
  Part~@case:heller-cover-injective-hull. Let $M$ be a core, $P_M$ its
  projective cover, and let
  $ 0 arrow X arrow P_M arrow M arrow 0 $
  be exact. To prove that $X ≅ Omega M$, it suffices to show that $X$ is a core.
  However, any projective direct summand of $X$ is also injective, and can
  therefore be split off from $P_M$; this would contradict the assumption that
  $P_M$ is a projective cover of $M$. The dual of Schanuel's Lemma now shows
  that $P_M$ is an injective hull of $Omega M$. The proof of
  part~@case:heller-hull-projective-cover is similar, and is left to the reader.
  It is then easy to verify part~@case:heller-exact-projective-middle-cores,
  again left as exercise for the reader.
]

#source(826)
#example[
  Let $A=K G$, where $char K=p>0$, and $p$ divides $|G|$. Given a nonsimple
  $P in cal(P)(A) inter upright("Ind") A$, put $S=op("soc") P$. By
  @i:prop:projective-cover-summary, $P$ has a unique maximal submodule $J P$,
  where $J=rad A$. Further, $S$ is simple, and
  $ P slash J P ≅ S, quad 0 subset S subset.eq J P subset P. $
  Since $P$ has a unique maximal submodule, each nonzero factor module of $P$
  must be indecomposable. Likewise, since $S$ is simple, every nonzero submodule
  of $P$ is indecomposable. From the exact sequence
  $ 0 arrow J P arrow P arrow S arrow 0 $
  we conclude that
  $ J P=Omega(S), $
  noting that $J P≠0$ because of our hypothesis that $P≠S$. Since the sequence
  $ 0 arrow S arrow P arrow P slash S arrow 0 $
  is also exact, we obtain
  $ S=Omega(P slash S), quad "and thus" J P=Omega(S)=Omega^2 lr((P slash S)). $
  For later use, we observe that there is a fiber product of $A$-modules:
  #radical-socle-square()
  with each $i$ an inclusion, each $j$ a canonical surjection. This gives a
  nonsplit ses:
  $
    0 arrow J P arrow P plus.o (J P slash op("soc") P)
    arrow P slash op("soc") P arrow 0.
  $
  <eq:projective-radical-socle-ar-sequence>
]<exm:projective-radical-socle-sequence>

We now digress slightly to the topic of projective homomorphisms, which
generalizes the discussion of projective endomorphisms given in
§~@i:ss:projective-endomorphisms (see also
§~@ss:cyclic-block-homological-preliminaries). Given a commutative ring $R$ and
a finite group $G$, let $Lambda=R G$. Let us recall some facts about extensions
of $Lambda$-modules (see the discussion in Volume I, §~@i:ss:ext-tor). We write
$op("Ext")$ in place of $op("Ext")_Lambda^1$, for brevity.

Given a pair of f.g. left $Lambda$-modules $M$ and $N$, and any
$f in "Hom"_Lambda lr((N,M))$, there is an induced map
$ f^*:op("Ext")(M,X) arrow op("Ext")(N,X) $
#source(827)
for each $Lambda$-module $X$, with no finite-generation restriction on $X$. To
describe $f^*$, note that each $xi in op("Ext")(M,X)$ determines an extension
$Y$ of $M$ by $X$, unique up to equivalence:
$ xi:0 arrow X arrow Y arrow M arrow 0. $
Then $f^* xi=xi f$, where $xi f$ is the extension of $N$ by $X$ occurring in the
commutative diagram
#extension-pullback()
in which $Y_1$ is the pullback of the pair of maps $(f,theta)$. We call $f$ a
#idx("Projective homomorphism")_projective homomorphism_ if $f^*$ is the zero
map for every $X$, that is, if $xi f$ is a split exact sequence for every ses
$xi$ ending in $M$.

#lemma[
  A map $f in "Hom"_Lambda lr((N,M))$ is a projective homomorphism if and only
  if $f$ “factors through a projective”, that is, there exists a commutative
  diagram
  #projective-factor-triangle()
  with $P in cal(P)(Lambda)$.#ed-note[
    Restricting the auxiliary tests to f.g. modules would not suffice. For
    $R=product_(i>=1) FF_2$, let $I$ be its ideal of finite-support sequences.
    The cyclic module $R slash I$ is not projective, but
    $op("Ext")_R^1 lr((R slash I,X))=0$ for every f.g. $X$: finite generators of
    $X$ allow arbitrary coordinate maps $I arrow X$ to extend to $R arrow X$.
  ]
]<lem:projective-homomorphism-factorization>

#proof[
  If $f$ factors through a projective $P$, then $f=f_2 f_1$ where
  $f_1:N arrow P$ and $f_2:P arrow M$. For any $xi in op("Ext")(M,X)$, we have
  $xi f=(xi f_2)f_1=0$, since $xi f_2=0$ because $P$ is projective. Conversely,
  suppose $f$ is a projective homomorphism, and choose $xi$ with middle term
  $Y in cal(P)(Lambda)$. Since $xi f$ splits, we obtain a map $N arrow Y$
  lifting $f$.
]

As in @i:prop:projective-endomorphism-dual-tensor, there is a map
$ "Hom"_Lambda lr((N,Lambda)) times.o_Lambda M arrow "Hom"_Lambda lr((N,M)), $
whose image is precisely the set of projective homomorphisms from $N$ to $M$. We
may then carry over the proof of @i:th:higman-projective-endomorphism-transfer
to the present more general situation, to obtain:

#proposition[
  Let $M$ and $N$ be left $Lambda$-lattices. Then $f in "Hom"_Lambda lr((N,M))$
  is a projective homomorphism if and only if
  $ f=sum_(x in G) x h x^(-1) quad "for some" h in "Hom"_R lr((N,M)). $
]<prop:projective-homomorphism-transfer>

#source(828)
Let us now return to the case where $A=K G$, with $K$ a field. Given left
$A$-modules $M$ and $N$, let $"Hom"_A lr((M,N))_(G slash 1)$ denote the subspace
of $"Hom"_A lr((M,N))$ consisting of all projective homomorphisms from $M$ to
$N$, that is, all those homomorphisms which factor through a projective. We
define
$
  bold("Hom")_A lr((M,N))="Hom"_A lr((M,N)) slash "Hom"_A lr((M,N))_(G slash 1).
$
<eq:stable-hom-definition>
#nidx(
  "$bold(\"Hom\")_A lr((M,N))$",
  "$\"Hom\"_A lr((M,N)) slash \"Hom\"_A lr((M,N))_(G slash 1)$",
  target: [@eq:stable-hom-definition],
)

We leave it as an easy exercise to check that
$
  bold("Hom")_A lr((M plus.o P,N)) ≅ bold("Hom")_A lr((M,N))
  quad "for any" P in cal(P)(A).
$
<eq:stable-hom-projective-summand>
It follows readily from the definition, or from
@prop:projective-homomorphism-transfer, that $"Hom"_A lr((M,M))_(G slash 1)$ is
a two-sided ideal of the endomorphism ring $"End"_A M$. We set
$ bold("End")_A M=("End"_A M) slash "Hom"_A lr((M,M))_(G slash 1), $
<eq:stable-endomorphism-ring>
a factor ring of $"End"_A M$. If $M in cal(P)(A)$, then of course
$bold("End")_A M=0$. The converse also holds, since if the identity map $"id"_M$
factors through a projective module $P$, then $M divides P$, so $M$ is
projective.

Now let $M$ and $N$ be a pair of $A$-modules, and let $Omega$ be the Heller
loop-space operator. In our discussion of Auslander–Reiten sequences in
§~@ss:auslander-reiten-group-algebras, it will be vital to use the relation
between $bold("Hom")_A lr((M,N))$ and extensions of $N$ by $Omega^2 M$, where of
course $Omega^2 M=Omega(Omega M)$. The following proof is based on the work of
Auslander–Reiten @bib:Auslander1975:

#theorem[
  #footnote[See @th:auslander-reiten-duality-finite-dimensional-algebras for the
    generalization to f.d. $K$-algebras.]
  Let $M$ and $N$ be left $A$-modules, where $A=K G$. There is a natural
  $K$-isomorphism
  $
    op("Ext")_A^1 lr((N,Omega^2 M)) ≅ K"-dual of"
    bold("Hom")_A lr((M,N)).
  $
]<th:group-algebra-auslander-reiten-duality>

#proof[
  #case-list(
    prefix: "Step ",
    numbering: "1.",
    [#case[
      Neither side of the proposed isomorphism changes if we delete projective
      summands of $M$ or $N$, so we may assume that both $M$ and $N$ are cores.
      We show first that
      $
        op("Ext")_A^1 lr((M,N)) ≅
        op("Ext")_A^1 lr((Omega M,Omega N)).
      $
      By @prop:heller-projective-covers-injective-hulls, there are exact
      sequences
      $
        0 arrow Omega M arrow P_M arrow M arrow 0,
        quad 0 arrow Omega N arrow P_N arrow N arrow 0.
      $
      Using @i:rem:ext-long-exact-sequence twice, we obtain
      $
        op("Ext")_A^1 lr((M,N)) ≅ op("Ext")_A^2 lr((M,Omega N))
        ≅ op("Ext")_A^1 lr((Omega M,Omega N)),
      $
      #source(829)
      as desired. Thus we have
      $
        op("Ext")_A^1 lr((N,Omega^2 M)) ≅
        op("Ext")_A^1 lr((Omega^(-1) N,Omega M)).
      $
      We claim next that
      $ op("Ext")_A^1 lr((Omega^(-1) N,L)) ≅ bold("Hom") lr((N,L)) $
      for any $A$-module $L$, where $bold("Hom")$ means $bold("Hom")_A$. Using
      the exact sequence @eq:heller-injective-hull-sequence and
      @i:rem:ext-long-exact-sequence(iii), we have
      $
        op("Ext")_A^1 lr((Omega^(-1) N,L)) ≅
        "Hom" lr((N,L)) slash im "Hom" lr((I_N,L)).
      $
      Since every map from $N$ to $L$ that factors through an injective must
      factor through $I_N$, the right-hand side is precisely
      $bold("Hom") lr((N,L))$, as desired. Therefore
      $
        op("Ext")_A^1 lr((Omega^(-1) N,Omega M)) ≅
        bold("Hom") lr((N,Omega M)),
      $
      and it remains for us to establish
      $
        bold("Hom") lr((N,Omega M)) ≅ K"-dual of"
        bold("Hom") lr((M,N)).
      $
      <eq:stable-hom-heller-duality>
    ]<case:ar-duality-dimension-shift>],
    [#case[
      We shall now simplify the problem by reducing the verification of the
      above isomorphism to the special case in which $N$ is the $G$-trivial
      module $K$. Given any $A$-modules $X$ and $Y$, we show at once that there
      are natural isomorphisms
      $
        "Hom" lr((X,Y)) ≅ "Hom" lr((K,X^* times.o Y)) ≅
        "Hom" lr((X times.o Y^*,K)),
      $
      <eq:hom-inner-tensor-invariants>
      where $times.o$ denotes inner tensor product (over $K$) of $A$-modules. By
      @i:prop:invariants-induction-hom, we have
      $
        "Hom" lr((X,Y)) ≅ op("inv")_G lr((X^* times.o Y))
        =op("inv")_G lr((K^* times.o (X^* times.o Y)))
        ≅ "Hom" lr((K,X^* times.o Y)),
      $
      which proves the first isomorphism. The second then follows from
      @i:eq:contragredient-hom-duality and the identity
      $(X times.o Y^*)^* ≅ X^* times.o Y$.

      Using the characterization of projective homomorphisms given in
      @prop:projective-homomorphism-transfer, it follows from
      @eq:hom-inner-tensor-invariants that
      $
        bold("Hom") lr((X,Y)) ≅ bold("Hom") lr((K,X^* times.o Y)) ≅
        bold("Hom") lr((X times.o Y^*,K)).
      $
      The isomorphism @eq:stable-hom-heller-duality, which we wish to prove, now
      takes the form
      $
        bold("Hom") lr((K,N^* times.o Omega M)) ≅ K"-dual of"
        bold("Hom") lr((N^* times.o M,K)).
      $
      On the other hand, from the exact sequence
      $
        0 arrow N^* times.o Omega M arrow N^* times.o P_M
        arrow N^* times.o M arrow 0,
      $
      #source(830)
      whose middle term is projective by
      Exercise~@i:exc:regular-inner-tensor-projective, we deduce that
      $
        N^* times.o Omega M ≅ Omega(N^* times.o M) plus.o P
        quad "for some" P in cal(P)(A).
      $
      Therefore
      $
        bold("Hom") lr((K,N^* times.o Omega M)) ≅
        bold("Hom") lr((K,Omega(N^* times.o M))).
      $
      Setting $V=N^* times.o M$, the problem reduces to proving that
      $
        bold("Hom") lr((K,Omega V)) ≅ K"-dual of"
        bold("Hom") lr((V,K)).
      $
      <eq:stable-invariants-heller-duality>
    ]<case:ar-duality-tensor-reduction>],
    [#case[
      In proving @eq:stable-invariants-heller-duality, we may assume that $V$ is
      a core, so let
      $ 0 arrow Omega V arrow P arrow V arrow 0 $
      be an exact sequence, with $P$ a projective cover of $V$. By
      Exercise~@exc:stable-hom-simple-core, we may replace $bold("Hom")$ by
      $"Hom"$ in @eq:stable-invariants-heller-duality. By
      @prop:heller-projective-covers-injective-hulls, $P$ is an injective hull
      of $Omega V$, so $P$ has the same socle as $Omega V$. Therefore
      $
        "Hom" lr((K,Omega V))="Hom" lr((K,op("soc") Omega V))
        ="Hom" lr((K,op("soc") P))="Hom" lr((K,P)).
      $
      On the other hand,
      $ "Hom" lr((V,K))="Hom" lr((P,K)) $
      by Exercise~@exc:projective-cover-simple-hom, so we need only prove that
      $ "Hom"_A lr((K,P)) ≅ K"-dual of" "Hom"_A lr((P,K)). $
      Since both sides are covariant additive functors of $P$, it suffices to
      verify the result when $P=lmodule(A, A)$. But in this case the result is a
      special case of @i:prop:frobenius-right-adjoint, using $H={1}$ and $M=L=K$
      in @i:prop:frobenius-right-adjoint.
    ]<case:ar-duality-projective-pairing>],
  )
  We leave it to the reader to check that all the isomorphisms used in the proof
  are natural.
]

It is now necessary to discuss the bimodule structures of the $K$-spaces
occurring in Theorem~@th:group-algebra-auslander-reiten-duality. To begin with,
we observe that $"Hom"_A lr((M,N))$ is a bimodule on which $"End"_A N$ acts from
the left, and $"End"_A M$ from the right. We call $"Hom"_A lr((M,N))$ an
$("End"_A N,"End"_A M)$-bimodule, to indicate this fact. We leave it to the
reader to verify that $bold("Hom")_A lr((M,N))$ has this same bimodule
structure. Further, by Exercise~@exc:stable-endomorphism-heller-invariance,
$"End"_A M$ acts from the left on $op("Ext")_A^1 lr((N,Omega^2 M))$. It then
follows that this Ext group is an $("End"_A M,"End"_A N)$-bimodule. Its $K$-dual
is therefore an $("End"_A N,"End"_A M)$-bimodule. Since all of the isomorphisms
occurring in @th:group-algebra-auslander-reiten-duality are natural ones, they
commute with endomorphisms of the modules involved. Thus we obtain:

#corollary[
  The isomorphisms in @th:group-algebra-auslander-reiten-duality are
  $("End"_A M,"End"_A N)$-bimodule #source(831)isomorphisms. In particular, for
  each left $A$-module $M$, there is a two-sided $("End"_A M)$-isomorphism
  $ op("Ext")_A^1 lr((M,Omega^2 M)) ≅ (bold("End")_A M)', $
  where $bold("End")_A M$ is given by @eq:stable-endomorphism-ring, and prime
  denotes $K$-dual.
]<cor:group-algebra-ar-duality-bimodules>

Now let $M$ be a left $A$-module, with endomorphism ring $E="End"_A M$. Denote
by $bold("End")_A M$ the factor ring of $E$ defined in
@eq:stable-endomorphism-ring, and view $bold("End")_A M$ as an $(E,E)$-bimodule.
The discussion following @eq:stable-endomorphism-ring shows that
$bold("End")_A M=0$ if and only if $M in cal(P)(A)$. The bimodule structure of
$bold("End")_A M$ allows us to make its $K$-dual $(bold("End")_A M)'$ into an
$(E,E)$-bimodule, and the correspondence between submodules and their $K$-duals
is inclusion-reversing. This shows that the minimal submodules of
$(bold("End")_A M)'$ are in bijective correspondence with the maximal submodules
of $bold("End")_A M$. This is the key fact needed to establish the following
result, which will be used in §~@ss:auslander-reiten-group-algebras to prove the
existence of Auslander–Reiten sequences for $A$-modules.

#proposition[
  Let $M$ be a nonprojective indecomposable left $A$-module, where $A=K G$, and
  let $E="End"_A M$ be its endomorphism ring. Let $Omega$ denote the Heller
  loop-space operator, and form the left $A$-module $Omega^2 M$. Then
  $ op("Ext")_A^1 lr((M,Omega^2 M)) $
  is an $(E,E)$-bimodule. As a one-sided $E$-module (left or right), its socle
  $ op("soc") op("Ext")_A^1 lr((M,Omega^2 M)) $
  is a simple $E$-module.
]<prop:ar-extension-simple-socle>

#proof[
  Since $M$ is indecomposable, its endomorphism ring $E$ is a local ring (see
  @i:prop:indecomposable-local-endomorphism-ring), whose radical $rad E$ is the
  unique maximal left (or right) ideal of $E$. The factor ring $bold("End")_A M$
  of $E$ is not zero, since $M$ is (by hypothesis) nonprojective. It follows
  that as left $E$-module (or as right $E$-module), $bold("End")_A M$ has a
  unique maximal submodule. Therefore its $K$-dual $(bold("End")_A M)'$ has a
  unique minimal submodule, that is, this $K$-dual has a simple socle as left
  (or right) $E$-module. On the other hand, there is an $(E,E)$-bimodule
  isomorphism
  $ op("Ext")_A^1 lr((M,Omega^2 M)) ≅ (bold("End")_A M)' $
  by @cor:group-algebra-ar-duality-bimodules. Thus
  $op("soc") op("Ext")_A^1 lr((M,Omega^2 M))$ is simple as claimed, and the
  proposition is established.
]

=== Auslander–Reiten Sequences for Group Algebras
<ss:auslander-reiten-group-algebras>

Our aim in this subsection is to define Auslander–Reiten sequences for
$A$-modules, where $A$ is an arbitrary artinian ring. We shall then follow an
approach #source(832)shown to us by P. Webb, based on the fundamental work of
Auslander–Reiten @bib:Auslander1975, to prove the existence of such sequences in
the special case where $A=K G$, with $K$ a field and $G$ a finite group. In
§~@ss:green-algebra-dual-elements, we will indicate the significance of such
sequences for studying the representation theory of $G$ over the field $K$.

From now on, $A$ denotes a left artinian ring, and all $A$-modules considered
below are assumed to be finitely generated. Denote by $cal(P)(A)$, $cal(I)(A)$,
and $upright("Ind") A$, respectively, the sets of (isomorphism classes of)
projective, injective, and indecomposable $A$-modules. Thus,
$upright("Ind") A-cal(P)(A)$ consists of all nonprojective indecomposable
modules.

#definition[
  An #idx("AR-sequence")#idx("Almost split sequence", see: (
    "AR-sequence",
  ))#idx("Auslander-Reiten sequence", see: ("AR-sequence",))_Auslander–Reiten
  sequence_ (or _almost-split sequence_) for an indecomposable $A$-module $M$ is
  a nonsplit ses
  $ 0 arrow N arrow E arrow M arrow 0, $
  <eq:auslander-reiten-sequence>
  in which $N$ is indecomposable, with the following universal mapping property:
  For each $A$-module $X$, each map $f:X arrow M$, that is not a split
  surjection factors through $E$. In other words, for each such $f$, there
  exists a map $g$ making the diagram
  #ar-factorization-triangle()
  commute. We call @eq:auslander-reiten-sequence an _AR-sequence for_ $M$.
]<def:auslander-reiten-sequence>

In the example @exm:projective-radical-socle-sequence given earlier, it will
turn out that the sequence
$
  0 arrow J P arrow P plus.o (J P slash op("soc") P)
  arrow P slash op("soc") P arrow 0
$
is an $A R$-sequence for $P slash op("soc") P$. This is not obvious now,
however.

#remarks(numbered: true)[
  #case-list(
    numbering: "(i)",
    [#case[
      A map $f:X arrow M$ is a split surjection if and only if there exists an
      $f':M arrow X$ such that $f f'="id"_M$. If this occurs, then
      $M divides X$.
    ]<case:ar-split-surjection>],
    [#case[
      If $M$ is projective or $N$ is injective, any sequence
      @eq:auslander-reiten-sequence must split, and so cannot be an
      $A R$-sequence.
    ]<case:ar-nonprojective-noninjective>],
    [#case[
      Let @eq:auslander-reiten-sequence be an $A R$-sequence for $M$, and let
      $ 0 arrow X arrow Y arrow M arrow 0 $
      be any nonsplit ses. From the definition of $A R$-sequence, it follows at
      once that there must exist homomorphisms (indicated by the vertical
      arrows) for which the diagram
      #source(833)
      #ar-nonsplit-comparison()
      commutes.
    ]<case:ar-nonsplit-universal-comparison>],
    [#case[
      There is a dual notion: an #idx("AR*-sequence")_$A R'$-sequence_ for an
      indecomposable $A$-module $N$ is a nonsplit ses
      @eq:auslander-reiten-sequence in which $M$ is indecomposable, such that:
      For each $A$-module $Y$, each map $h:N arrow Y$, that is not a split
      monomorphism extends to a map $E arrow Y$.
    ]<case:ar-dual-almost-split-sequence>],
  )
]<rem:ar-sequence-basic-properties>

It is by no means obvious that there exists an $A R$-sequence for each
$M in upright("Ind") A-cal(P)(A)$. Likewise, for each
$N in upright("Ind") A-cal(I)(A)$, is there an $A R'$-sequence for $N$? Further,
what is the connection between these two concepts?

We quote without proof:

#theorem(title: [Auslander])[
  Let $M$ and $N$ denote f.g. left $A$-modules, where $A$ is an artinian ring,
  f.g. as module over its center.#footnote[Every f.d. $K$-algebra $A$ over a
    field $K$ satisfies this hypothesis.] #idx("Auslander-Reiten Theorem")#idx(
    "Auslander's Theorem",
  ) Then we have:
  #case-list(
    numbering: "(i)",
    [#case[
      For each $M in upright("Ind") A-cal(P)(A)$, there exists an $A R$-sequence
      for $M$. It is unique up to isomorphism, that is, for any pair of
      $A R$-sequences for $M$, there is a commutative diagram
      #ar-uniqueness-statement()
      with $alpha$ and $beta$ isomorphisms.
    ]<case:auslander-ar-existence-uniqueness>],
    [#case[
      Dually, for each $N in upright("Ind") A-cal(I)(A)$, there exists an
      $A R'$-sequence for $N$, unique up to isomorphism.
    ]<case:auslander-dual-ar-existence-uniqueness>],
    [#case[
      The concepts of $A R$- and $A R'$-sequences coincide, in the sense that
      @eq:auslander-reiten-sequence is an $A R$-sequence for $M$ if and only if
      it is an $A R'$-sequence for $N$.
    ]<case:auslander-ar-dual-coincidence>],
  )
]<th:auslander-almost-split-sequences>

We shall prove this result in the special case where $A$ is a group algebra
$K G$, by using the machinery developed in §~@ss:heller-loop-space-operator.
Indeed, we shall be able to exhibit $A R$-sequences explicitly in this
situation, by using the following result, due to Auslander–Reiten
@bib:Auslander1975:

#theorem[
  Let $M$ be a nonprojective indecomposable left $A$-module, where $A=K G$, with
  $K$ a field and $G$ a finite group. Set $E="End"_A M$, a local f.d.
  $K$-algebra. Let $Omega$ be the Heller loop-space operator, and view
  $op("Ext")_A^1 lr((M,Omega^2 M))$ as left $E$-module via the
  action#footnote[See Exercise~@exc:stable-endomorphism-heller-invariance.] of
  $E$ on $op("Ext")(*,Omega^2 M)$.
  #source(834)
  Then $op("Ext")_A^1 lr((M,Omega^2 M))$ has a simple socle as left $E$-module,
  and any generator $xi$ of this socle determines an extension
  $ xi:0 arrow Omega^2 M arrow L arrow M arrow 0, $
  <eq:group-algebra-ar-extension>
  unique up to equivalence of extensions. For each $xi$, the above is an
  Auslander–Reiten sequence for $M$.

  Furthermore, $Omega$ is bijective on nonprojective (= noninjective)
  indecomposable $A$-modules, so each nonprojective indecomposable module $N$
  can be written as $N=Omega^2 M$ for some $M$, unique up to isomorphism. For
  this $M$, the sequence @eq:group-algebra-ar-extension is an $A R'$-sequence
  for $N$.
]<th:group-algebra-ar-sequence-socle-construction>

#proof[
  Write $op("Ext")$ instead of $op("Ext")_A^1$, for brevity. By
  @prop:ar-extension-simple-socle, $op("soc") op("Ext")(M,Omega^2 M)$ is a
  simple left $E$-module. Let $xi$ be any generator of this socle, that is, any
  nonzero element of the socle, and let @eq:group-algebra-ar-extension be an
  extension of $M$ by $Omega^2 M$ defined by $xi$. Then $Omega^2 M$ is
  indecomposable and the sequence is nonsplit, so in order to show that it is an
  $A R$-sequence for $M$, it remains to verify the universal mapping property:
  given any $f in "Hom"_A lr((X,M))$ which is not a split surjection, we must
  show that $f$ factors through $L$:
  #ar-socle-factorization()
  The map $f in "Hom"_A lr((X,M))$ induces a map
  $ f_*:"Hom"_A lr((M,X)) arrow "Hom"_A lr((M,M)). $
  If $f_*$ is surjective, then $f h="id"_M$ for some $h:M arrow X$, which
  contradicts the hypothesis that $f$ is not a split surjection. We have thus
  shown that $f_*$ is not surjective.

  Next, $f_*$ induces a map $tilde(f)$ on $bold("Hom")$'s, making the diagram
  #stable-hom-induced-square()
  commute. As shown in the proof of @prop:ar-extension-simple-socle, $bold(E)$
  is a nonzero local ring, since it is a nonzero factor ring of the local ring
  $E$. Therefore $ker phi subset.eq rad E$. This shows that $tilde(f)$ is not
  surjective, since otherwise we would obtain
  $ E=im f_*+ker phi=im f_*+rad E, $
  #source(835)
  and then $E=im f_*$ by Nakayama's Lemma, contradicting the fact that $f_*$ is
  not surjective.

  We are now ready to use @th:group-algebra-auslander-reiten-duality; we have
  $
    op("Ext")(X,Omega^2 M) ≅ K"-dual of" bold("Hom")_A lr((M,X)),
    quad op("Ext")(M,Omega^2 M) ≅ K"-dual of" bold(E).
  $
  Therefore $tilde(f)$ induces a map
  $ f':op("Ext")(M,Omega^2 M) arrow op("Ext")(X,Omega^2 M), $
  and $f'$ is not injective since $tilde(f)$ is not surjective. View both Ext
  groups as left $E$-modules; then $f'$ is an $E$-homomorphism, and
  $ ker f' supset.eq op("soc") op("Ext")(M,Omega^2 M), $
  since $ker f'≠0$ and the socle is a simple $E$-module. It follows that
  $f'(xi)=0$, so there is a commutative diagram
  #ar-socle-pullback()
  in which the bottom sequence $xi f$ is split (because $f'(xi)=0$). Hence there
  is a map $i:X arrow L_1$ with $j i="id"_X$. But then $h(g i)=f$, so we have
  factored the map $f$ through $L$, as desired.

  Let $bold(E)=bold("End")_A M$ as above. By virtue of the isomorphism
  $ bold(E)=bold("End")_A M ≅ bold("End")_A Omega^2 M $
  (see Exercise~@exc:stable-endomorphism-heller-invariance), and the action of
  $"End"_A Omega^2 M$ on $op("Ext")(*,Omega^2 M)$, we may view
  $op("Ext")(M,Omega^2 M)$ as left $bold(E)$-module. We have shown above that,
  as $bold(E)$-module, $op("Ext")(M,Omega^2 M)$ has simple socle, and any
  generator of this socle yields an $A R$-sequence for $M$.

  Dually, let $N$ be any nonprojective indecomposable module; since $Omega$ is
  bijective on such modules, the module $Omega^(-2) N$ is uniquely determined up
  to isomorphism. The isomorphism
  $ bold("End")_A Omega^(-2) N ≅ bold("End")_A N $
  allows us to view $op("Ext")(Omega^(-2) N,*)$ as right
  $(bold("End")_A N)$-module. Then any generator of
  $op("soc") op("Ext")(Omega^(-2) N,N)$ yields an $A R'$-sequence for $N$.

  In particular, an $A R'$-sequence for $Omega^2 M$ arises from a generator of
  $op("soc") op("Ext")(M,Omega^2 M)$ as right $bold(E)$-module. However, the
  proof of @prop:ar-extension-simple-socle shows that this #source(836)socle
  coincides with $op("soc") op("Ext")(M,Omega^2 M)$ as left $bold(E)$-module. It
  follows at once that the sequence @eq:group-algebra-ar-extension is also an
  $A R'$-sequence for $Omega^2 M$, as claimed, and the theorem is established.
]

Finally, we prove that $A R$-sequences are unique up to isomorphism.

#theorem[
  Let $M$ be a nonprojective indecomposable $A$-module, with $A$ any artinian
  ring, f.g. over its center. Let
  $
    xi_i:0 arrow N_i arrow^(f_i) E_i arrow^(g_i) M arrow 0,
    quad i=1,2,
  $
  be a pair of $A R$-sequences for $M$. Then there exists a commutative diagram
  #ar-uniqueness-proof-diagram()
  in which $alpha$ and $beta$ are isomorphisms.
]<th:ar-sequence-uniqueness>

#proof[
  If such a diagram exists, we indicate it by the notation
  $ xi_2=(alpha,beta,1_M)xi_1. $
  By Remark~@case:ar-nonsplit-universal-comparison[#context {
    reference-number-text(
      "("
        + reference-data(<rem:ar-sequence-basic-properties>).text
        + reference-data(<case:ar-nonsplit-universal-comparison>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }], $beta$ exists since $xi_2$ is an $A R$-sequence for $M$. Then $beta$
  induces the map $alpha$, and it remains to show that $alpha$ and $beta$ are
  isomorphisms.

  Reversing the roles of $xi_1$ and $xi_2$, we obtain
  $ xi_1=(alpha',beta',1_M)xi_2 $
  for some maps $alpha'$, $beta'$. Therefore
  $ xi_1=(alpha'alpha,beta'beta,1_M)xi_1. $
  Now $alpha'alpha in "End"_A N_1$, and $"End"_A N_1$ is a local ring since
  $N_1$ is indecomposable. Thus either $alpha'alpha in "Aut"_A N_1$, or else
  $alpha'alpha in rad "End"_A N_1$. In the latter case we have
  $(alpha'alpha)^n=0$ for some $n$, since the hypotheses on $A$ imply that
  $rad "End"_A N_1$ is nilpotent. Therefore
  $ xi_1=((alpha'alpha)^n,(beta'beta)^n,1)xi_1=(0,*,1)xi_1=0, $
  so $xi_1$ is split exact, contradicting the hypothesis that $xi_1$ is an
  $A R$-sequence.

  We have thus shown that $alpha'alpha in "Aut"_A N_1$. Similarly, we obtain
  $alpha alpha' in "Aut"_A N_2$, so $alpha$ and $alpha'$ are isomorphisms. The
  same then holds for $beta$ and $beta'$, by the Snake Lemma, and the result is
  established.
]

#source(837)
As a special case of Theorem~@th:group-algebra-ar-sequence-socle-construction,
we have:

#proposition[
  Let $S$ be a simple left $A$-module that is not projective, where $A=K G$.
  #case-list(
    numbering: "(i)",
    [#case[
      Every non-split exact sequence
      $ 0 arrow Omega^2 S arrow L arrow S arrow 0 $
      is an $A R$-sequence for $S$, and an $A R'$-sequence for $Omega^2 S$.
    ]<case:ar-simple-module-sequences>],
    [#case[
      Every non-split exact sequence
      $ 0 arrow Omega S arrow M arrow Omega^(-1) S arrow 0 $
      is an $A R$-sequence for $Omega^(-1) S$ and an $A R'$-sequence for
      $Omega S$.
    ]<case:ar-inverse-heller-simple-sequences>],
  )
]<prop:ar-simple-module-sequences>

#proof[
  We have $"End"_A S$ a skewfield, and then $bold("End")_A S="End"_A S$ since
  $S$ is not projective. Then $op("Ext")_A^1 lr((S,Omega^2 S))$ is a
  one-dimensional space over this skewfield, so any nonzero element of this Ext
  group generates its socle. Assertion~@case:ar-simple-module-sequences now
  follows from @th:group-algebra-ar-sequence-socle-construction.

  For part~@case:ar-inverse-heller-simple-sequences, we note that
  $bold("End")_A Omega^(-1) S$ is also a skewfield: by
  Exercise~@exc:stable-endomorphism-heller-invariance it is isomorphic to
  $bold("End")_A S$, which is a skewfield by
  Exercise~@exc:simple-stable-endomorphism-ring. We again apply
  @th:group-algebra-ar-sequence-socle-construction.
]

As an illustration of @case:ar-inverse-heller-simple-sequences[#context {
  reference-number-text(
    "("
      + reference-data(<prop:ar-simple-module-sequences>).text
      + reference-data(<case:ar-inverse-heller-simple-sequences>)
        .text
        .trim(regex("[()]"))
      + ")",
  )
}], consider the example @exm:projective-radical-socle-sequence above. We saw
there that
$ Omega^(-1) S=P slash op("soc") P, quad Omega S=J P, $
so the non-split sequence @eq:projective-radical-socle-ar-sequence is always an
$A R$-sequence.

*Notes*

Let $Lambda$ be an $R$-order in a separable $K$-algebra $A$, where $R$ is a
complete d.v.r. with quotient field $K$. We can then define $A R$-sequences for
the category of $Lambda$-lattices (rather than $Lambda$-modules). As shown by
Auslander, $A R$-sequences exist for every nonprojective indecomposable
$Lambda$-lattice. See also Roggenkamp–Schmidt @bib:Roggenkamp1976. An explicit
construction of such sequences, for the special case where $Lambda=R G$ with $G$
a finite group, was given by Roggenkamp @bib:Roggenkamp1977, using the
techniques of the proof of
Theorem~@th:group-algebra-ar-sequence-socle-construction. The result is also
inherent in the work of Auslander. The loop-space operator $Omega$ is well
defined, and for each nonprojective indecomposable $Lambda$-lattice $M$, there
is an analogue of @prop:ar-extension-simple-socle, namely:
$op("Ext")_Lambda^1 lr((M,Omega M))$ has a simple socle as
$("End"_Lambda M)$-module. Then any generator of this socle gives rise to an
extension
$ 0 arrow Omega M arrow L arrow M arrow 0, $
which is an $A R$-sequence for $M$. (See Roggenkamp @bib:Roggenkamp1977 for
other references.)

#source(838)
=== Auslander–Reiten Sequences for Algebras
<ss:auslander-reiten-finite-dimensional-algebras>

Throughout, let $A$ be a f.d. algebra over a field $K$, and consider only f.g.
$A$-modules in this subsection. Our aim here is to generalize the results of
§~@ss:auslander-reiten-group-algebras, so as to show the existence of
$A R$-sequences for $A$-modules. The results are due to Auslander–Reiten
@bib:AuslanderReiten1974, @bib:Auslander1975, and we follow here the treatment
in Gabriel @bib:Gabriel1980.

For left $A$-modules $M$, $N$, we denote $"Hom"_A lr((M,N))$ by $(M,N)$ for
brevity. Let $P(M,N)$ be the space of projective homomorphisms from $M$ to $N$
(see @lem:projective-homomorphism-factorization), and let
$ bold("Hom") lr((M,N))=(M,N) slash P(M,N). $
In order to construct $A R$-sequences, the key step is to generalize
@th:group-algebra-auslander-reiten-duality and
@cor:group-algebra-ar-duality-bimodules by replacing $Omega^2 M$ by some
suitable module $cal(A)(M)$. For each $A$-module $M$, put
$ D M="Hom"_K lr((M,K))=K"-dual of" M. $
#idx("Dual of a module")
Then $D$ is an exact contravariant functor with $D^2=1$, and $D$ takes left
$A$-modules into right $A$-modules, and vice versa. Further, $D$ maps projective
modules onto injective modules, and vice versa. Next, define another
contravariant functor $d$ by
$ d M="Hom"_A lr((M,A)). $
Then $d$ is left exact, takes left $A$-modules to right $A$-modules, and carries
projectives to projectives. We now define the #idx("Nakayama functor")_Nakayama
functor_ $cal(N)=D d$, so for each left $A$-module $M$,
$ cal(N) M=D d M=K"-dual of" "Hom"_A lr((M,A))=D(M,A). $
<eq:nakayama-functor-definition>
#nidx("$cal(N)$", "Nakayama functor", target: [@eq:nakayama-functor-definition])
We note that for each idempotent $e in A$, we have
$ d(A e)="Hom"_A lr((A e,A)) ≅ e A. $
<eq:dual-projective-principal-ideal>
Furthermore, $cal(N)$ is a covariant right exact functor, taking left
$A$-modules to left $A$-modules, and carrying projective modules to injective
modules.

We now define the #idx("Auslander-Reiten translate")_Auslander–Reiten
translate_#footnote[Also denoted by $D op("Tr") M$, the dual transpose of $M$.]
$cal(A) M$ of a left $A$-module $M$ as follows.
#nidx("$cal(A) M$", "Auslander-Reiten translate of $M$")
Choose any exact sequence
$ P_1 arrow^(f_1) P_0 arrow^(f_0) M arrow 0, quad P_i "projective", $
<eq:projective-presentation-ar-translate>
and apply $cal(N)$ to obtain an exact sequence of left $A$-modules
$
  cal(N) P_1 arrow^(cal(N) f_1) cal(N) P_0 arrow^(cal(N) f_0)
  cal(N) M arrow 0.
$
#source(839)
Then define $cal(A) M=ker cal(N) f_1$, so there is an exact sequence
$
  0 arrow cal(A) M arrow cal(N) P_1 arrow^(cal(N) f_1) cal(N) P_0
  arrow^(cal(N) f_0) cal(N) M arrow 0.
$
<eq:auslander-reiten-translate-sequence>
Then $cal(A) M$ depends on the choice of the $P_i$, but is unique up to
injective direct summands. In particular, if
@eq:projective-presentation-ar-translate is part of a minimal projective
resolution#footnote[In this situation, this means that $P_0$ is a projective
  cover of $M$, and $P_1$ is a projective cover of $ker f_0$ (see
  §~@i:ss:projective-covers).] of $M$, then $cal(A) M$ has no injective direct
summands.

#example(numbered: false)[
  If $A=K G$, where $G$ is a finite group, then by
  @i:prop:frobenius-right-adjoint for each $A$-module $M$ we have
  $ "Hom"_A lr((M,A)) ≅ "Hom"_K lr((M,K)). $
  Thus in this case $cal(N) M=M$. With a minimal projective presentation,
  $cal(A) M=Omega^2 M$; for arbitrary presentations this equality holds modulo
  injective direct summands, as above.
]<exm:group-algebra-nakayama-identity>

We shall show that the entire discussion in
§~@ss:auslander-reiten-group-algebras carries over to the more general case of
f.d. $K$-algebras, provided that we replace $Omega^2 M$ in
§~@ss:auslander-reiten-group-algebras by the above-defined module $cal(A) M$. In
fact, it suffices to establish two fundamental results:

For the first, let $lmodule(A, underline(op("mod")))$ denote the category of
f.g. left $A$-modules modulo projectives. Thus, $M$ and $M'$ determine the same
object in $lmodule(A, underline(op("mod")))$ if and only if
$M plus.o P ≅ M' plus.o P'$ for some projectives $P$, $P'$. Morphisms are
defined as above, i.e.,
$ bold("Hom")_A lr((M,N))=(M,N) slash P(M,N). $
Dually, let $lmodule(A, overline(op("mod")))$ be the category of f.g. left
$A$-modules, modulo injectives. Our first key result is as follows:

#theorem[
  There is a bijection of isomorphism classes $M arrow.l.r cal(A) M$ giving an
  equivalence of categories
  $lmodule(A, underline(op("mod"))) ≅ lmodule(A, overline(op("mod")))$. Hence
  $M$ is a nonprojective indecomposable module if and only if $cal(A) M$ is a
  noninjective indecomposable module (up to projective and injective summands of
  $M$ and $cal(A) M$, respectively).
]<th:auslander-reiten-translate-stable-equivalence>

The second key fact, generalizing @th:group-algebra-auslander-reiten-duality and
@cor:group-algebra-ar-duality-bimodules, is given by the following theorem
(Auslander–Reiten @bib:Auslander1975, Props. 7.2, 7.3):

#theorem[
  #idx("Auslander-Reiten Theorem")
  Let $S$ and $M$ be left $A$-modules. There is a natural $K$-isomorphism
  $
    op("Ext")_A^1 lr((S,cal(A) M)) ≅ K"-dual of" (M,S) slash P(M,S)
    =D[(M,S) slash P(M,S)].
  $
  Further, the above is an $(E(M),E(S))$-bimodule isomorphism, where $E(M)$
  denotes $"End"_A M$, and $E(S)$ is defined analogously.
  #source(840)
  In particular, there is a two-sided $E(M)$-isomorphism
  $ op("Ext")_A^1 lr((M,cal(A) M)) ≅ D(bold("End")_A M). $
]<th:auslander-reiten-duality-finite-dimensional-algebras>

Once we have proved these two theorems, the entire discussion in
§~@ss:auslander-reiten-group-algebras carries over to the more general case. In
particular, @th:group-algebra-ar-sequence-socle-construction generalizes as
follows: let $M$ be a nonprojective indecomposable left $A$-module, where $A$ is
any f.d. $K$-algebra, and let $N$ be an injective-free core of $cal(A) M$. Then
$op("Ext")_A^1 lr((M,N))$ has a simple socle as left $E(M)$-module, and any
generator $xi$ of this socle determines an extension
$ xi:0 arrow N arrow L arrow M arrow 0, $
which is an $A R$-sequence for $M$ and an $A R'$-sequence for $N$. The
“uniqueness” of such sequences is proved as in @th:ar-sequence-uniqueness.

The proof of @th:auslander-reiten-translate-stable-equivalence, which we now
give, is a routine exercise on projective covers and injective hulls of modules.
For an $A$-module $M$, consider an exact sequence #named-equation(
  name: [$(ast)$],
)[
  $ P_1 arrow^(f_1) P_0 arrow^(f_0) M arrow 0, quad P_i "projective". $
]<eq:translate-equivalence-projective-presentation>
Since the Nakayama function $cal(N)$ preserves direct sums, it follows from
Exercise~@exc:projective-presentations-minimal-decomposition that $cal(A) M$ is
unique up to injective direct summands, and further that no such summands occur
if @eq:translate-equivalence-projective-presentation is part of a minimal
projective resolution of $M$.

We now construct a functor $cal(B)$ on left $A$-modules, which will turn out to
be an inverse for $cal(A)$. Given a left $A$-module $N$, choose any exact
sequence
$ 0 arrow N arrow I_0 arrow^h I_1, quad I_0,I_1 "injective". $
Then there is an exact sequence
$
  0 arrow d D N arrow d D I_0 arrow^(h^*) d D I_1 arrow cal(B)(N)
  arrow 0,
$
<eq:inverse-translate-injective-presentation>
where $cal(B)(N)$ is defined as $op("cok") h^*$.

For an $A$-module $M$, there is an exact sequence
$ 0 arrow cal(A) M arrow D d P_1 arrow^(D d f_1) D d P_0, $
which is part of an injective resolution of $cal(A) M$. By definition, the
sequence
$
  (d D)(D d P_1) arrow^((d D)(D d f_1)) (d D)(D d P_0)
  arrow cal(B)(cal(A) M) arrow 0
$
is exact. However, for each projective $A$-module $P$, there are natural
isomorphisms
$ (d D)(D d P) ≅ d^2 P ≅ P. $
#source(841)
It follows that $cal(B)(cal(A) M)=op("cok")(P_1 arrow^(f_1) P_0)=M$, as desired.
Dually, we obtain $cal(A)(cal(B) N)=N$ for each $N$. It is easily verified that
for given $N$, $cal(B) N$ is unique up to projective direct summands and no such
summands occur when we use a minimal injective resolution of $N$.

Finally, we show that if $M$ is an $A$-module such that $cal(A) M$ is
decomposable (ignoring injective summands), then $M$ is also decomposable
(ignoring projective summands). Indeed, if $cal(A) M$ has a proper
decomposition, then so does its injective resolution, by
@i:prop:injective-hulls-additive. This gives rise to a decomposition of the
modules $d D I_0$, $d D I_1$, and the map $h^*$ occurring in
@eq:inverse-translate-injective-presentation, where now $N=cal(A) M$,
$I_0=D d P_1$, $I_1=D d P_0$. It follows as above that the modules $P_1$, $P_0$
and the map $P_1 arrow^(f_1) P_0$ decompose, and therefore so does $M$. A dual
argument proves that if $cal(B) N$ is decomposable, then so is $N$. This
completes the proof of @th:auslander-reiten-translate-stable-equivalence.

We begin the proof of @th:auslander-reiten-duality-finite-dimensional-algebras
with an easy result:

#lemma[
  Let $X$ and $P$ be left $A$-modules, with $P$ projective. There is a
  $K$-isomorphism
  $ alpha_X:D(P,X) ≅ (X,cal(N) P) $
  which is natural in $X$.
]<lem:nakayama-projective-hom-duality>

#proof[
  Since both sides are additive in $P$, it suffices to treat the case $P=A e$,
  with $e in A$ idempotent. Since $"Hom"_A lr((A e,X)) ≅ e X$ as $K$-spaces, and
  $"Hom"_A lr((A e,A)) ≅ e A$ as right $A$-modules, it suffices to find maps
  $alpha,gamma$ that are inverses of one another, where now
  #nakayama-evaluation-inverses()
  For $f in "Hom"_K lr((e X,K))$, define $alpha f$ by the formula
  $ [(alpha f)(x)](e a)=f(e a x), quad x in X, quad a in A. $
  For $g in "Hom"_A lr((X,"Hom"_K lr((e A,K))))$, define $gamma g$ by
  $ (gamma g)(e x)=[g(e x)](e), quad x in X. $
  It is easily checked that $alpha$, $gamma$ are well-defined, and that
  $alpha gamma=1$, $gamma alpha=1$, so $alpha$ is an isomorphism with inverse
  $gamma$.
]

Now start with the exact sequence @eq:projective-presentation-ar-translate, and
let $X$ be a left $A$-module. Then
$ 0 arrow (M,X) arrow (P_0,X) arrow (P_1,X) $
is exact, whence so is
$ D(P_1,X) arrow^(f'_1) D(P_0,X) arrow^(f'_0) D(M,X) arrow 0. $

#source(842)
From @lem:nakayama-projective-hom-duality, it follows that there is a
commutative diagram with exact rows:
#nakayama-duality-exact-diagram()
where $alpha_0$, $alpha_1$ are isomorphisms, and $beta=f'_0 alpha_0^(-1)$.

Now let $S$ be any left $A$-module; for each $theta in (S,cal(N) P_0)$, let
$E(theta)$ be the module defined by the pullback diagram
#nakayama-pullback-square()
with $g$, $h$ canonical projection maps. It follows that the sequence
#named-equation(name: [$(ast)$])[
  $ 0 arrow cal(A) M arrow E(theta) arrow^g S $
]<eq:nakayama-pullback-left-exact>
is exact. Furthermore,
$
  g "surjective" <==> im theta subset.eq im cal(N) f_1
  <==> im theta subset.eq ker cal(N) f_0.
$
Applying $(X,-)$ to @eq:nakayama-pullback-left-exact, we obtain a larger
commutative diagram with exact rows:
#nakayama-pullback-hom-diagram()
where $a_X=beta_X theta_X$. The lower half is natural in $X$, so for each
$phi in (X,S)$, there is a commutative diagram
#nakayama-naturality-square()

#source(843)
where $phi$ induces $phi^*$ and $phi'$. Since $phi^*("id"_S)=phi$, we obtain
$
  a_X lr((phi))=phi'(t_theta), quad "where"
  t_theta=a_S lr(("id"_S)) in D(M,S).
$
Note that $a_X lr((phi)) in "Hom"_K lr(((M,X),K))$, and for each $psi in (M,X)$,
$ [a_X lr((phi))](psi)=[phi'(t_theta)](psi)=t_theta lr((phi psi)). $
It follows that
$
  ker a_X={phi in (X,S):a_X lr((phi))=0}
  ={phi in (X,S):phi compose (M,X) subset.eq ker t_theta}.
$
Furthermore, $g_X$ is surjective if and only if $ker a_X=(X,S)$.

Choosing $X=A$ in the above, we conclude that the map $(A,E(theta)) arrow (A,S)$
is surjective if and only if
$ (A,S) compose (M,A) subset.eq ker t_theta, $
where the left-hand expression is defined as the $K$-span of all composites
$h h'$, $h in (A,S)$, $h' in (M,A)$. By
Exercise~@exc:projective-homomorphism-composite-span,
$(A,S) compose (M,A)=P(M,S)$. On the other hand, $(A,E(theta)) arrow (A,S)$ is
surjective if and only if $g:E(theta) arrow S$ is surjective, or equivalently,
if and only if $im theta subset.eq im cal(N) f_1$. Thus we obtain
$ im theta subset.eq im cal(N) f_1 <==> t_theta lr((P(M,S)))=0. $
<eq:ar-duality-projective-annihilator-criterion>

Continuing with the proof of
@th:auslander-reiten-duality-finite-dimensional-algebras, we identify
$D[(M,S) slash P(M,S)]$ with a $K$-subspace of $D(M,S)$, namely,
$
  D[(M,S) slash P(M,S)]
  ={phi in "Hom"_K lr(((M,S),K)):phi(P(M,S))=0}.
$
<eq:stable-hom-dual-annihilator>
We are trying to establish an isomorphism
$op("Ext")_A^1 lr((S,cal(A) M)) ≅ D[(M,S) slash P(M,S)]$; and
@eq:ar-duality-projective-annihilator-criterion and
@eq:stable-hom-dual-annihilator will enable us to calculate the right-hand side.
Turning to the left-hand side, we use the exact sequence (see
@eq:auslander-reiten-translate-sequence)
$
  0 arrow cal(A) M arrow cal(N) P_1 arrow^(cal(N) f_1)
  im cal(N) f_1 arrow 0.
$
Since $cal(N) P_1$ is injective and so $op("Ext")_A^1 lr((-,cal(N) P_1))=0$ (see
@i:rem:ext-properties(v)), it follows from @i:eq:ext-long-exact-second-variable
that there is a $K$-isomorphism
$
  op("Ext")_A^1 lr((S,cal(A) M)) ≅
  (S,im cal(N) f_1) slash im (S,cal(N) P_1)
$
that is natural in $S$.

From the exact sequence
$ (S,cal(N) P_1) arrow (S,cal(N) P_0) arrow D(M,S) arrow 0, $
#source(844)
we conclude that
$ im (S,cal(N) P_1)=ker beta_S. $
Next, we must determine which elements $theta in (S,cal(N) P_0)$ have the
property that $beta_S theta$ represents an element of $D[(M,S) slash P(M,S)]$,
that is, such that $(beta_S theta)P(M,S)=0$. Choosing $X=S$ in the discussion
following @lem:nakayama-projective-hom-duality, we have
$ (beta_S theta)P(M,S)=[a_S lr(("id"_S))]P(M,S)=t_theta lr((P(M,S))). $
Thus by @eq:ar-duality-projective-annihilator-criterion
$
  {theta in (S,cal(N) P_0):beta_S theta in D[(M,S) slash P(M,S)]}
  ={theta in (S,cal(N) P_0):t_theta lr((P(M,S)))=0}
  \
  ={theta in (S,cal(N) P_0):im theta subset.eq im cal(N) f_1}
  =(S,im cal(N) f_1).
$
We have thus shown that $beta_S$ maps $(S,im cal(N) f_1)$ onto
$D[(M,S) slash P(M,S)]$, with kernel $im (S,cal(N) P_1)$. This establishes the
desired isomorphism, and completes the proof of
Theorem~@th:auslander-reiten-duality-finite-dimensional-algebras.

We leave it to the reader to verify that the entire discussion of
§~@ss:auslander-reiten-group-algebras carries over to the case where $A$ is a
f.d. $K$-algebra, provided we replace $Omega^2 M$ by $cal(A) M$ throughout that
discussion. In particular, we have now proved:

#theorem(title: [Auslander])[
  All the assertions in @th:auslander-almost-split-sequences are valid when $A$
  is a f.d. algebra over a field.
]<th:finite-dimensional-algebra-almost-split-sequences>

#exercises-heading

Throughout, let $A=K G$.

#exercise[
  Let $M$ be an $A$-module, where $A=K G$, and consider an exact sequence of
  $A$-modules
  $
    0 arrow L arrow P_r arrow dots arrow P_0 arrow M arrow 0,
    quad "with each" P_i in cal(P)(A).
  $
  Prove that
  $ "core of" L ≅ Omega^(r+1) M, $
  where $Omega$ is the Heller loop-space operator.
]<exc:long-projective-sequence-heller-core>

#exercise[
  Let $S$ be a simple $A$-module and $M$ a core. Show that
  $
    bold("Hom")_A lr((M,S))="Hom"_A lr((M,S)),
    quad bold("Hom")_A lr((S,M))="Hom"_A lr((S,M)).
  $
]<exc:stable-hom-simple-core>

#hint([@exc:stable-hom-simple-core])[
  Let $f in "Hom"_A lr((M,S))$, $f≠0$; then $f$ is surjective. If $f$ factors
  through a projective, #source(845)then $f$ factors through a projective cover
  $P$ of $S$, so there is a commutative diagram
  #simple-core-factorization()
  Then $X=rad P$, and since $f$ is surjective we have $P=g(M)+X$. Therefore
  $P=g(M)$, so $P divides M$, a contradiction. The second isomorphism follows in
  a similar way.
]<hint:stable-hom-simple-core>

#exercise[
  Let $S$ be a simple $A$-module, and let $P$ be a projective cover of an
  $A$-module $V$. Show that
  $ "Hom"_A lr((V,S)) ≅ "Hom"_A lr((P,S)). $
]<exc:projective-cover-simple-hom>

#hint([@exc:projective-cover-simple-hom])[
  Each $f:V arrow S$ lifts to a map $g:P arrow S$. Conversely, given $g$, let
  $X=ker(P arrow V)$; then $X subset.eq (rad A)P$ by
  @i:cor:semiperfect-projective-cover-properties, so $g(X)=0$. Therefore $g$
  induces a map $f$.
]<hint:projective-cover-simple-hom>

#exercise[
  Let $S$ be a simple nonprojective $A$-module. Prove that
  $ bold("End")_A S="End"_A S="skewfield". $
]<exc:simple-stable-endomorphism-ring>

#exercise[
  Prove that
  $ bold("End")_A M ≅ bold("End")_A Omega M ≅ bold("End")_A Omega^2 M, $
  and that $op("Ext")_A^1 lr((X,Omega^2 M))$ is naturally a left
  $("End"_A M)$-module.
]<exc:stable-endomorphism-heller-invariance>

#hint([@exc:stable-endomorphism-heller-invariance])[
  Each $f in "End" M$ induces a map $g in "End" Omega M$, shown in the diagram
  #heller-endomorphism-lift()
  where $P$ is a projective cover of $M$. If $f$ factors through $P$, we may
  choose $g=0$. If both $h$ and $h'$ lift $f$, then $h-h':P arrow Omega M$, so
  $g-g'$ factors through a projective.
]<hint:stable-endomorphism-heller-invariance>

#exercise[
  Let $A=K G$, where $char K=p>0$, and $G$ is a cyclic $p$-group
  $chevron.l x:x^q=1 chevron.r$. Prove
  #case-list(
    numbering: "(i)",
    [#case[
      There are exactly $q$ indecomposable $A$-modules, and these are given by
      $ V_i=(1-x)^(q-i) A ≅ A slash (1-x)^i A, quad "for" 1≤i≤q. $
      Further, $dim_K V_i=i$, and
      $
        Omega V_i ≅ V_(q-i), quad Omega^2 V_i ≅ V_i
        quad "for" 1≤i<q.
      $
    ]<case:cyclic-p-group-indecomposable-heller-modules>],
    [#case[
      Put $V_0=0$. For $1≤i<q$, there is an $A R$-sequence of $A$-modules
      $ 0 arrow V_i arrow V_(i-1) plus.o V_(i+1) arrow V_i arrow 0. $
    ]<case:cyclic-p-group-ar-sequences>],
  )
]<exc:cyclic-p-group-ar-sequences>

#hint([@exc:cyclic-p-group-ar-sequences])[
  For part~@case:cyclic-p-group-ar-sequences: Let
  $overline(A)=A slash (1-x)^(i+1) A$, and view the above modules as
  $overline(A)$-modules. Then #source(
    846,
  )$V_(i+1)=overline(A)$, and the above sequence is that given in
  @eq:projective-radical-socle-ar-sequence. Finally, check that this
  $A R$-sequence of $overline(A)$-modules is also one over $A$.
]<hint:cyclic-p-group-ar-sequences>

In Exercises~@exc:projective-homomorphism-composite-span and
@exc:projective-presentations-minimal-decomposition, $A$ is a f.d. $K$-algebra,
over a field $K$.

#exercise[
  Let $M$, $S$ be left $A$-modules. Prove that
  $ (A,S) compose (M,A)=P(M,S), $
  where the left-hand side is the $K$-space spanned by all composites $h g$,
  $h in (A,S)$, $g in (M,A)$, and $P(M,S)$ denotes the space of projective maps.
]<exc:projective-homomorphism-composite-span>

#hint([@exc:projective-homomorphism-composite-span])[
  Each $f in P(M,S)$ factors through a free $A$-module.
]<hint:projective-homomorphism-composite-span>

#exercise[
  Let $M$ be a left $A$-module, and let
  $overline(P)_1 arrow overline(P)_0 arrow M arrow 0$ be part of a minimal
  projective resolution of $M$. Show that for any exact sequence
  $P_1 arrow P_0 arrow M arrow 0$, with $P_i$ projective, there exists a
  commutative diagram with exact rows:
  #minimal-presentation-comparison()
  where the vertical maps are isomorphisms and the $Q_i$ are projective. Dualize
  to obtain a corresponding result for injective resolutions.
]<exc:projective-presentations-minimal-decomposition>

#hint([@exc:projective-presentations-minimal-decomposition])[
  Let $P_M$ denote a projective cover of $M$, with kernel $N$. We choose
  $overline(P)_0=P_M$, $overline(P)_1=P_N$, and $f:P_N arrow N arrow P_M$ the
  composite map. The surjection $P_0 arrow M$ factors through a surjection
  $P_0 arrow P_M$, so we may take $P_0=P_M plus.o Q_0$. Now consider
  #projective-cover-kernel-comparison()
  Then $N'=N plus.o Q_0$, and $P_1$ maps onto $N'$, so $P_1=P^* plus.o Q_0$,
  where $P^* arrow N$ is surjective. As above, $P^*=P_N plus.o Q_1$ for some
  $Q_1$.
]<hint:projective-presentations-minimal-decomposition>
