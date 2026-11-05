#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/46-whitehead.typ": *

== Whitehead Groups of Integral Group Rings
<sec:whitehead-integral-group-rings>

We present here C. T. C. Wall’s results on the Whitehead group#footnote[
  We have previously referred to $K_1$ as a “Whitehead group,” but we shall
  avoid that terminology here.
] $op("Wh") lr((R G))$, where $R$ is a commutative ring and $G$ is a finite
group. Let
$ G^(a b) = G slash [G,G] = "commutator factor group of" G, $
and let $R G^(a b)$ denote its group ring over $R$.
#source(180)
The composite map
$ G arrow.r (R G)^dot arrow.r K_1 lr((R G)) $
induces a homomorphism $G^(a b) arrow.r K_1 lr((R G))$. Likewise, the inclusion
$eta: R arrow.r R G$ induces a homomorphism
$eta_*: K_1 lr((R)) arrow.r K_1 lr((R G))$. In order to define
$op("Wh") lr((R G))$, we need a preliminary result:

#proposition[
  The homomorphism
  $ phi: K_1 lr((R)) times G^(a b) arrow.r K_1 lr((R G)) $
  is injective.
] <prop:whitehead-scalar-abelianization-injection>
#proof[
  The augmentation map $epsilon: R G arrow.r R$ induces
  $epsilon_*: K_1 lr((R G)) arrow.r K_1 lr((R))$. Since
  $epsilon eta = op("id")_R$, we have $epsilon_* eta_* = 1$, so $eta_*$ is
  injective and $epsilon_*$ is surjective. Since
  $epsilon_* lr({phi lr((G^(a b)))}) = 1$ in $K_1 lr((R))$, it follows that the
  product $K_1 lr((R)) times phi lr((G^(a b)))$ in $K_1 lr((R G))$ is a direct
  product. We must still check that $phi: G^(a b) arrow.r K_1 lr((R G))$ is
  injective. But there are homomorphisms
  $
    G^(a b) arrow.r^phi K_1 lr((R G)) arrow.r K_1 lr((R G^(a b)))
    arrow.r^det (R G^(a b))^dot,
  $
  where composite is the inclusion $G^(a b) arrow.r (R G^(a b))^dot$. Therefore
  $phi$ is injective, and the result is established.
]

From now on, we identify $K_1 lr((R)) times G^(a b)$ with its image in
$K_1 lr((R G))$, and define the _Whitehead group_ as
$
  op("Wh") lr((R G)) = K_1 lr((R G)) slash (K_1 lr((R)) times G^(a b)).
$ <eq:whitehead-group>
#nidx(
  "$op(\"Wh\") lr((R G))$",
  "Whitehead group",
  target: [@eq:whitehead-group],
)
#idx("Whitehead group", target: [@eq:whitehead-group])
When $R = ZZ$, we write simply $op("Wh") lr((G))$. Since
$K_1 lr((ZZ)) = lr({plus.minus 1})$, we have
$ op("Wh") lr((G)) = K_1 lr((ZZ G)) slash plus.minus G^(a b). $
<eq:integral-whitehead-group>

Let us now recall (see Exercise @i:exc:abelian-integral-group-ring-torsion-units
or @bib:CurtisReiner1962[CR] §37):

#theorem(title: [G. Higman], numbered: false)[
  Let $R = "alg. int." lr({F})$, where $F$ is an algebraic number field, and let
  $G$ be a finite abelian group. Then every unit of $R G$ of finite order is of
  the form $epsilon x$, with $epsilon$ a root of unity in $R$, and $x in G$. In
  other words,
  $
    "torsion subgroup of" (R G)^dot
    = ("torsion subgroup of" R^dot) times G.
  $
] <th:higman-group-ring-torsion-units>
#idx(
  "Higman's Theorem",
  "on units in group rings",
  target: [@th:higman-group-ring-torsion-units],
)

C. T. C. Wall @bib:Wall1974c generalized this to an arbitrary finite group $G$,
by proving a $K$-theoretic version in which $(R G)^dot$ is replaced by
$K_1 lr((R G))$. Of course, $S K_1 lr((R G))$ lies in the torsion subgroup of
$K_1 lr((R G))$. The aim of this section is to prove:

#theorem(name: [Wall’s Theorem])[
  Let $R$ be the ring of all algebraic integers in an algebraic number field
  $F$, and let $G$ be an arbitrary finite group.
  #source(181)
  Then the torsion subgroup of $K_1 lr((R G))$ is precisely
  $ ("torsion subgroup of" R^dot) times G^(a b) times S K_1 lr((R G)). $
] <th:wall-integral-group-ring-torsion>
#idx("Wall's Theorem", target: [@th:wall-integral-group-ring-torsion])

The proof of Wall’s Theorem is based on the following steps:
#enum(
  [It suffices to show that $op("Wh")^F lr((R G))$ is torsionfree, where (see
    below)
    $
      op("Wh")^F lr((R G)) = K_1 lr((R G)) slash
      (S K_1 lr((R G)) times K_1 lr((R)) times G^(a b)).
    $],
  [To prove $op("Wh")^F lr((R G))$ torsionfree, it suffices to establish the
    result after extending or completing the ground field (Lemma
    @lem:whitehead-torsion-field-extension).],
  [For $R = p$-adic ring, $S K_1 lr((R G))$ is a finite $p$-group (Theorem
    @th:p-adic-group-ring-sk1-p-group).],
  [For $G = p$-group and $R = p$-adic ring, $op("Wh")^F lr((R G))$ is
    $p$-torsionfree (Theorem @th:p-group-whitehead-p-torsionfree).],
  [For $R = "alg. int." lr({F})$, induction techniques reduce the problem of
    $p$-torsion in $op("Wh")^F lr((R G))$ to the case where $G$ is a
    $p$-hyper-elementary group (Prop.
    @prop:whitehead-hyperelementary-torsion-detection). This case is easily
    handled by using the results of the previous steps.],
)

Our first step in the proof of Wall’s Theorem is to reduce the problem to
calculations in $K_1 lr((F G))$. Let $K_1^F lr((R G))$ denote the image of
$K_1 lr((R G))$ in $K_1 lr((F G))$, so the sequence
$
  1 arrow.r S K_1 lr((R G)) arrow.r K_1 lr((R G))
  arrow.r K_1^F lr((R G)) arrow.r 1
$
is exact. There is a commutative diagram
#numbered-block(whitehead-image-triangle)
<eq:whitehead-scalar-image-comparison>
The proof of @prop:whitehead-scalar-abelianization-injection shows that the map
$K_1 lr((F)) times G^(a b) arrow.r K_1 lr((F G))$ is injective. We define
$
  op("Wh")^F lr((R G)) = K_1^F lr((R G)) slash (K_1^F lr((R)) times G^(a b)),
$
#nidx(
  "$op(\"Wh\")^F lr((R G))$",
  "Whitehead group defined by extension of scalars to F",
)
where $K_1^F lr((R))$ is the image of $K_1 lr((R))$ in $K_1 lr((F))$, that is,
$K_1^F lr((R)) = R^dot$. Since $S K_1 lr((R)) = 1$ by the Bass–Milnor–Serre
Theorem, we have $K_1 lr((R)) tilde.equiv K_1^F lr((R))
= R^dot$. It follows that $phi'$ is injective, the sequence
$
  1 arrow.r S K_1 lr((R G)) arrow.r op("Wh") lr((R G))
  arrow.r op("Wh")^F lr((R G)) arrow.r 1
$
is exact, and $S K_1 lr((R G)) times K_1 lr((R)) times G^(a b)$ is a direct
product in $K_1 lr((R G))$.
#source(182)
Wall’s Theorem is therefore equivalent to each of the following equivalent
assertions: #numbered-block[
  #enum(
    numbering: "(i)",
    [$"torsion subgroup of" K_1^F lr((R G))
      = ("torsion subgroup of" R^dot) times G^(a b)$.],
    [$op("Wh")^F lr((R G))$ is torsionfree.],
  )
] <eq:wall-torsion-equivalent-assertions>

We remark that @eq:wall-torsion-equivalent-assertions is trivially true when
$G = lr({1})$. Next, let $G$ be arbitrary. For any abelian group $A$ and any
prime $p$, define the
$
  p"-torsion subgroup of" A = lr({a in A: p^n a = 0 "for some" n >= 0}).
$
#idx("p-torsion subgroup")
#idx("p-torsion")
For $phi$ and $phi'$ as in @eq:whitehead-scalar-image-comparison, and for each
prime $p$, it is easily seen that the following conditions are equivalent:
#enum(
  numbering: "(i)",
  [$im phi supset.eq p$-torsion subgroup of $K_1 lr((R G))$.],
  [$phi$ induces an isomorphism of $p$-torsion subgroups.],
  [$op("Wh") lr((R G))$ is $p$-torsionfree.],
)
Further, the same remark holds with $phi'$, $K_1^F lr((R G))$, and
$op("Wh")^F lr((R G))$ in place of $phi$, $K_1 lr((R G))$, and
$op("Wh") lr((R G))$, respectively. We note also that
$
  op("Wh") lr((R G)) "is" p"-torsionfree" arrow.l.r.double
  "both" op("Wh")^F lr((R G)) "and" S K_1 lr((R G)) "are" p"-torsionfree."
$ <eq:whitehead-p-torsion-decomposition>

For the remainder of our discussion, either $R = "alg. int." lr({F})$ for $F$ an
algebraic number field, or else $R$ is a d.v.r. in a $p$-adic field $F$ (with
$dim_(QQ_p) F < infinity$). Call $R$ a _$p$-adic ring_ in the latter case.
#idx("p-adic ring")

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [If the group $G$ is abelian, then $K_1^F lr((R G)) tilde.equiv (R G)^dot$,
      so @eq:wall-torsion-equivalent-assertions gives Higman’s Theorem, which is
      therefore a consequence of Wall’s Theorem.],
    [If $G$ is abelian and $R$ is a $p$-adic ring, then by
      @prop:commutative-semilocal-sk1 we have
      $
        (R G)^dot tilde.equiv K_1 lr((R G)) tilde.equiv K_1^F lr((R G)),
        S K_1 lr((R G)) = 1.
      $],
    [If $G$ is abelian and $R = "alg. int." lr({F})$, then
      $
        (R G)^dot tilde.equiv K_1^F lr((R G)), "but" S K_1 lr((R G))
        "may be nontrivial."
      $],
  )
] <rem:abelian-whitehead-unit-comparison>

#lemma[
  Let $F subset.eq E$ be fields, with rings of integers $R subset.eq S$, such
  that one of the following holds:
  #enum(
    numbering: "(a)",
    [Both fields are algebraic number fields.],
    [Both are $p_0$-adic fields (for the same $p_0$).],
    [$F$ is a number field, and $E$ a $p_0$-adic field.],
  )
  Then if $op("Wh")^E lr((S G))$ is $p$-torsionfree, so is
  $op("Wh")^F lr((R G))$.
] <lem:whitehead-torsion-field-extension>
#source(183)
#proof[
  Let $C = "center of" F G$, and define $C^+$ as in
  @eq:semisimple-positive-norm-subgroup. From the commutative diagram
  #norm-field-extension-square
  it follows that the map $K_1 lr((F G)) arrow.r K_1 lr((E G))$ is a
  monomorphism. Therefore so are the maps
  $K_1^F lr((R G)) arrow.r K_1^E lr((S G))$ and
  $K_1^F lr((R)) arrow.r K_1^E lr((S))$. Now consider the commutative diagram
  #whitehead-extension-augmentation
  in which all vertical maps are monomorphisms. By hypothesis
  $op("Wh")^E lr((S G))$ is $p$-torsionfree, so all $p$-torsion elements of
  $K_1^E lr((S G))$ lie in $im phi'$. If $x in K_1^F lr((R G))$ is a $p$-torsion
  element, then $sigma(x) = phi' lr((s,g))$ for some $s in S^dot$,
  $g in G^(a b)$. Then $s = epsilon'_* sigma(x) = sigma' epsilon_*(x)$, so
  $s in R^dot$. Therefore $x in im phi$, which shows that $im phi$ contains all
  $p$-torsion elements of $K_1^F lr((R G))$. This shows that
  $op("Wh")^F lr((R G))$ is $p$-torsionfree, as desired.
]

#theorem[
  Let $R$ be a complete d.v.r. with residue class field $k$ and quotient field
  $F$, where $dim_(QQ_p) F$ is finite. Then $S K_1 lr((R G))$ is a finite
  $p$-group, for any finite group $G$.
] <th:p-adic-group-ring-sk1-p-group>
#idx(
  "SK₁",
  "of integral group rings",
  target: [@th:p-adic-group-ring-sk1-p-group],
)
#proof[
  _Step 1._ We set
  $
    Lambda = R G, quad overline(Lambda) = Lambda slash rad Lambda
    tilde.equiv k G slash rad k G.
  $
  By @th:wall-whitehead-pro-p-splitting, there is a canonical injection
  $mu: K_1 lr((overline(Lambda))) arrow.r K_1 lr((Lambda))$, and we have
  $
    K_1 lr((Lambda)) = K_1 lr((overline(Lambda))) times V,
    quad "where" V "is a pro-"p"-group."
  $
  Let $sigma: K_1 lr((Lambda)) arrow.r K_1 lr((F G))$, so
  $S K_1 lr((Lambda)) = ker sigma$. We shall show below that the composite map
  $sigma mu$ is injective. Taking this for granted for the moment, we obtain
  $(ker sigma) inter (im mu) = 1$, and so $ker sigma <= V$. But any finite
  subgroup of a pro-$p$-group is a $p$-group, so $ker sigma$ is a finite
  $p$-group, and we are done.

  Now let $F'$ be a finite extension field of $F$, with d.v.r. $R'$ and residue
  class field $k'$, such that $F'$ and $k'$ are splitting fields for $G$. We
  have
  $
    R' G slash rad R' G tilde.equiv k' G slash rad k' G
    tilde.equiv k' times.o_k (k G slash rad k G)
    tilde.equiv k' times.o_k overline(Lambda),
  $
  using @i:prop:finite-algebra-local-base-radical and the proof of
  @i:th:group-algebra-separable-radical-quotient.
  #source(184)
  Then there is a commutative diagram
  #sk1-splitting-field-square
  in which both vertical maps are injective by Exercise
  @exc:whitehead-field-extension-injectivity. To prove $sigma mu$ injective, it
  suffices to prove $sigma' mu'$ injective. Changing notation, we may assume
  henceforth that both $F$ and $k$ are splitting fields for $G$.

  _Step 2._ Since $F$ is a splitting field for $G$, we may write
  $
    F G tilde.equiv product.co_(i=1)^s M_(n_i) lr((F)),
    quad "and" psi: K_1 lr((F G)) tilde.equiv product_(i=1)^s F^dot.
  $
  To describe $psi$ explicitly, let $lr({Z_1, dots, Z_s})$ be a basic set of
  simple left $F G$-modules. In the Morita equivalence
  $M_(n_i) lr((F)) tilde F$, the simple modules $Z_i$ and $F$ correspond to each
  other. Thus $psi$ is given by
  $
    sum_(i=1)^s [Z_i,a_i] arrow.r^psi (a_1,dots,a_s)
    in product_(i=1)^s F^dot.
  $
  On the other hand, we can construct the image of $K_1 lr((overline(Lambda)))$
  in $K_1 lr((Lambda))$ explicitly, as follows. Let $lr({P_1,dots,P_r})$ be a
  full set of nonisomorphic indecomposable projective $Lambda$-modules, and set
  $overline(P)_i = P_i slash (rad Lambda) P_i$, so
  $lr({overline(P)_1,dots,overline(P)_r})$ are a basic set of simple left
  $overline(Lambda)$-modules. Let $n = abs(k^dot)$, where $k$ is the residue
  class field of $R$. Via the Teichmüller map $t: k^dot arrow.r R^dot$ (see
  Exercise @exc:teichmuller-map), we can find an $n$-th root of unity
  $omega in R^dot$ such that $k^dot = ⟨overline(omega)⟩$. For each $i$,
  $[P_i,omega^(a_i)] in K_1 lr((Lambda))$ for $a_i in ZZ$, and its image in
  $K_1 lr((overline(Lambda)))$ is $[overline(P)_i,overline(omega)^(a_i)]$. Let
  $W$ be the subgroup of $K_1 lr((Lambda))$ consisting of all expressions
  $ w = sum_(i=1)^r [P_i,omega^(a_i)], quad a_i in ZZ. $
  The above shows that $W tilde.equiv K_1 lr((overline(Lambda)))$, and since
  $K_1 lr((overline(Lambda)))$ is canonically embedded in $K_1 lr((Lambda))$,
  $W$ must be its image in $K_1 lr((Lambda))$.

  We now show that
  $
    W inter ker sigma = 1, quad "where"
    sigma: K_1 lr((Lambda)) arrow.r K_1 lr((F G)).
  $
  Consider the lifting homomorphism $e: K_0 lr((k G)) arrow.r K_0 lr((F G))$
  defined in §@i:sec:cartan-brauer-triangle, and let $(e_(i j))^(r times s)$ be
  its matrix representation relative to the bases $lr({overline(P)_i})$,
  $lr({Z_j})$.
  #source(185)
  Then in $K_0 lr((F G))$ we have
  $ [F times.o_R P_i] = sum_(j=1)^s e_(i j) [Z_j], quad 1 <= i <= r. $
  Now let $w = sum_(i=1)^r [P_i,omega^(a_i)] in ker sigma$. Then
  $
    0 = sigma(w) = sum_(j=1)^s [Z_j,omega^(sum_i a_i e_(i j))]
    "in" K_1 lr((F G)),
  $
  so by the previous remarks we obtain
  $ sum_(i=1)^r a_i e_(i j) equiv 0 (mod n) quad "for" 1 <= j <= s. $
  But the map $e$ is a split injection by
  @i:prop:cartan-triangle-injectivity-cokernel, so we conclude that
  $a_i equiv 0 (mod n)$ for each $i$. Thus $w = 1$, so we have shown that
  $W inter ker sigma = 1$. As remarked in Step 1 above, this implies that
  $ker sigma <= V$, and so $S K_1 lr((Lambda))$ is a finite $p$-group, as was to
  be shown. The authors thank K. Uno for pointing out this simplified version of
  the original proof.
]

#theorem[
  Let $G$ be a $p$-group, where $p$ is prime. Let $R$ be a $p$-adic ring or a
  ring of algebraic integers, and let $F$ be its quotient field. Then
  $op("Wh")^F lr((R G))$ is $p$-torsionfree#footnote[
    By Exercise @exc:p-adic-p-group-whitehead-torsionfree,
    $op("Wh")^F lr((R G))$ is torsionfree if $R$ is a $p$-adic ring and $G$ is a
    $p$-group.
  ].
] <th:p-group-whitehead-p-torsionfree>
#proof[
  _Step 1._ We may assume $G != lr({1})$, since otherwise the result is
  trivially true. Suppose first that $R = "alg. int." lr({F})$, and let $P$ be a
  prime ideal of $R$ dividing $p$. Let $E = F_P$, $S = "d.v.r. in" E$. By
  @lem:whitehead-torsion-field-extension, if $op("Wh")^E lr((S G))$ is
  $p$-torsionfree, then so is $op("Wh")^F lr((R G))$. For the rest of the proof,
  we may concentrate on the local case, in which $R$ is a $p$-adic ring.
  Further, again by @lem:whitehead-torsion-field-extension, we may extend the
  ground field $F$, if desired, so we may assume that $R$ contains the
  $abs(G)$-th roots of 1.

  _Step 2._ Here we shall prove the theorem for the special case where $G$ is an
  abelian $p$-group, using induction on $abs(G)$. (This case could also be
  deduced from Higman’s Theorem.) Let $p^r$ be the exponent of $G$, so $r > 0$
  since $G != lr({1})$, and let $omega$ be a primitive $p^r$-th root of 1. By
  Step 1, we may assume that $omega in R$. Let $v$ be the valuation on $R$,
  normalized (for convenience) so that $v(p) = (p-1) slash p$. By
  @i:prop:prime-power-cyclotomic-ramification we obtain
  $v lr((1-omega)) = 1 slash p^r$.

  Now in this case
  $
    K_1 lr((R G)) tilde.equiv K_1^F lr((R G)) tilde.equiv (R G)^dot,
    quad K_1 lr((R)) tilde.equiv R^dot,
  $
  and we must show that each $p$-torsion element $x in (R G)^dot$ lies in
  $R^dot times G$.

  Each irreducible character $psi in op("Irr") lr((F G))$ maps $R G$ into $R$,
  and is a ring homomorphism. The trivial character $psi_1$ is just the
  augmentation map.
  #source(186)
  If $x in (R G)^dot$ is a $p$-torsion element, then $psi_1(x) = r in R^dot$.
  Replacing $x$ by $r^(-1) x$ and changing notation, we may now assume that
  $psi_1(x) = 1$.

  Choose an element $g in G$ of order $p$, and let $overline(G) = G slash ⟨g⟩$.
  There is an exact sequence
  $ 0 arrow.r (1-g) R G arrow.r R G arrow.r R overline(G) arrow.r 0, $
  and the ring surjection $R G arrow.r R overline(G)$ induces a homomorphism
  $(R G)^dot arrow.r (R overline(G))^dot$. This map carries $x$ onto a
  $p$-torsion element $overline(x) in (R overline(G))^dot$, and
  $overline(psi)_1 lr((overline(x))) = psi_1(x) = 1$, where $overline(psi)_1$ is
  the trivial character of $overline(G)$. By the induction hypothesis, we may
  conclude that
  $ x equiv g_0 quad (mod (1-g) R G) $
  for some $g_0 in G$. Replacing $x$ by $g_0^(-1) x$ and changing notation, we
  may now assume that
  $ x equiv 1 quad (mod (1-g) R G). $
  <eq:p-group-unit-augmentation-congruence>

  Now let $theta$ be a character of $G$ for which $theta(g) != 1$, so $theta(g)$
  is a $p$-th root of 1, and $v lr((1-theta(g))) = 1 slash p$. Extend $theta$ to
  a map $R G arrow.r R$. Then
  $
    1-theta(x) = theta lr((1-x)) = (1-theta(g)) dot theta(y)
    quad "for some" y in R G.
  $
  Therefore $v lr((1-theta(x))) >= 1 slash p$; but $theta(x)$ is a $p$-power
  root of 1, since $x$ is a $p$-torsion element. Therefore $theta(x)$ is either
  1 or a $p$-th root of 1, and so $theta(x) = theta(g)^a$ for some $a$.
  Replacing $x$ by $x g^(-a)$ and changing notation, we obtain a new $x$
  satisfying @eq:p-group-unit-augmentation-congruence for which $theta(x) = 1$.
  Writing $(1-x) = (1-g)y$, where $y in R G$, it follows that $theta(y) = 0$, so
  $
    y in ker theta, quad "and" ker theta
    = plus.o.big_(u in G, u != 1) R (u-theta(u)).
  $
  Now let $psi$ range over $op("Irr") lr((F G))$; then
  $ 1-psi(x) = (1-psi(g)) psi(y). $
  If $psi(g) = 1$, then $psi(x) = 1$. If $psi(g) != 1$, then $psi(g)$ is a
  $p$-th root of 1, so $v lr((1-psi(g))) = 1 slash p$. Further,
  $
    v lr((psi lr((u-theta(u))))) = v lr((psi(u)-theta(u))) > 0
    quad "for" u in G,
  $
  so
  $ v lr((1-psi(x))) > 1 slash p. $
  Since $psi(x)$ is a $p$-power root of 1, this gives $psi(x) = 1$. We have now
  shown that $psi(x) = 1$ for all $psi in op("Irr") lr((F G))$, whence $x = 1$.
  This completes the proof of the theorem when $G$ is an abelian $p$-group.

  #source(187)
  _Step 3._ Now let $G$ be an arbitrary $p$-group. The map $G arrow.r G^(a b)$
  induces a homomorphism:
  $ tau: K_1^F lr((R G)) arrow.r K_1^F lr((R G^(a b))) $
  which preserves torsion. Each element of $K_1^F lr((R G))$ can be represented
  by an element of $(R G)^dot$. Given a $p$-torsion element $x in (R G)^dot$, we
  must prove that $x in R^dot times G^(a b)$ in $K_1^F lr((R G))$. Since
  $tau(x)$ is a $p$-torsion element of $K_1^F lr((R G^(a b)))$, by Step 2 we may
  write $tau(x) = r g$ for some $r in R^dot$, $g in G$. Replacing $x$ by
  $x (r g)^(-1)$ and changing notation, we may assume $tau(x) = 1$. In order to
  prove that $x = 1$ in $K_1^F lr((R G))$, it suffices to verify that
  $op("nr") x = 1$, where the reduced norm $op("nr")$ carries $K_1^F lr((R G))$
  into the center of $F G$. The rest of the proof is devoted to showing, by
  induction on $abs(G)$, that
  $ tau(x) = 1 arrow.r.double op("nr") x = 1. $
  Suppose to begin with that $G$ contains an abelian normal subgroup $H$ of
  index $p$, and let $G = ⟨H,g⟩$, where $g^p = h_0 in H$. We may write
  $
    R G = plus.o.big_(i=0)^(p-1) (R H) g^i
    = plus.o.big_(i=0)^(p-1) g^i (R H),
  $
  a twisted group algebra of the cyclic group $G slash H$ over the commutative
  coefficient ring $R H$. The powers $lr({g^i})$ act by conjugation on $R H$,
  and conjugation by $g$ defines a ring automorphism $sigma$ of $R H$:
  $ sigma(alpha) = g^(-1) alpha g = alpha^g, quad forall alpha in R H. $
  <eq:cyclic-subgroup-conjugation-action>
  Note that $sigma^p = 1$ since $g^p = h_0 in H$. There is an analogous
  decomposition $F G = plus.o.big (F H) g^i$.

  Now let $F G = product.co A_j$ be the Wedderburn decomposition of $F G$. As
  pointed out in Step 1, we may assume that $F$ is a splitting field for $G$ and
  its subgroups. The $p$-torsion element $x in (R G)^dot$ may be written as
  $x = sum x_j$, $x_j in A_j$, and we must show that each $op("nr") x_j = 1$.
  This is clear when $A_j tilde.equiv F$, that is, $A_j$ corresponds to a linear
  character of $F G$; for then $tau(x) = 1$ implies that $x_j = 1$. We are left
  with the case where $A_j$ is a matrix algebra over $F$. Keep $j$ fixed, and
  let $S$ denote a simple left $A_j$-module. The character afforded by $S$ is of
  the form $psi^G$, where $psi$ is a linear character of $H$ distinct from its
  $G$-conjugates. Let $e$ be the central idempotent of $F H$ corresponding to
  $psi$, so
  $ F H dot e = F e, quad "and" h e = psi(h) e, quad h in H. $
  We obtain
  $
    S = F G times.o_(F H) e = plus.o.big_(i=0)^(p-1) F (g^i times.o e),
    quad "and" A_j tilde.equiv M_p lr((F)).
  $
  #source(188)
  In order to calculate $op("nr") x_j$, we let $x_S$ denote left multiplication
  by $x$ on $S$. Relative to the $F$-basis $lr({g^i times.o e})$ of $S$, $x_S$
  is represented by a matrix $bold(M)(x)$, and then
  $op("nr") x_j = det bold(M)(x)$. (This procedure works for all elements
  $x in F G$.) Let us write
  $
    x = alpha_0 + alpha_1 g + dots + alpha_(p-1) g^(p-1),
    quad "where" alpha_i in R H.
  $
  Then
  $ bold(M)(x) = sum_(i=0)^(p-1) bold(M) lr((alpha_i)) bold(M) lr((g^i)). $
  Next, we observe for $alpha in R H$:
  $
    alpha(g^i times.o e) = g^i times.o alpha^(g^i) e
    = g^i times.o sigma^i lr((alpha)) e
    = psi lr((sigma^i lr((alpha)))) lr({g^i times.o e}), quad 0 <= i <= p-1,
  $
  $
    g(g^i times.o e) = cases(
      g^(i+1) times.o e quad & 0 <= i <= p-2,
      psi lr((h_0)) lr({1 times.o e}) quad & i = p-1
    ).
  $
  On the other hand, we may let $x$ act from the left on the free right
  $F H$-module $plus.o.big g^i (F H)$. Relative to its basis $lr({g^i})$, $x$ is
  then represented by a matrix $bold(N)(x) in M_p lr((F H))$. The above formulas
  then show that
  $ psi lr((det bold(N)(x))) = det bold(M)(x) = op("nr") x_j. $
  <eq:induced-reduced-norm-transfer-determinant>
  It will be vital to give another interpretation of the matrix $bold(N)(x)$,
  where now $x in (R G)^dot$. Using the determinantal interpretation of $K_1$,
  the element $x$ corresponds to the pair $[R G,x_l]$, where $x_l$ is left
  multiplication by $x$ on the right $R G$-module $R G$. But $R G$ is also a
  free right $R H$-module on the $p$ generators $lr({g^i})$, so $x_l$ may be
  viewed as an automorphism of a free $R H$-module, and then $[R G,x_l]$ is an
  element of $K_1 lr((R H))$, represented by the matrix
  $bold(N)(x) in M_p lr((R H))$. Thus, $bold(N)$ is a homomorphism
  $ bold(N): K_1 lr((R G)) arrow.r K_1 lr((R H)), $
  and of course it carries $K_1^F lr((R G))$ into $K_1^F lr((R H))$.

  _Step 4._ Keeping the above notation, we study $bold(N)(x)$ in more detail,
  assuming for the moment that $x$ is an arbitrary element of $R G$, not
  necessarily a unit. Let $N^*(x) = det bold(N)(x)$, $x in R G$. For
  $alpha in R H$, we have
  $
    N^*(alpha) = det bold(N)(alpha) = product_(i=0)^(p-1) sigma^i lr((alpha))
    = "norm of" alpha.
  $
  #idx("Norm", target: [@eq:induced-reduced-norm-transfer-determinant])
  This suggests the definitions
  $
    T(alpha) = sum_(i=0)^(p-1) sigma^i lr((alpha)) = "trace of" alpha,
    quad "and" T lr((R H)) = lr({T(alpha): alpha in R H}).
  $
  #source(189)
  We call $T lr((R H))$ the _trace subgroup_ of $R H$; it is an $R$-submodule of
  $R H$. We now prove that there is an additive homomorphism
  $
    R G arrow.r R H slash T lr((R H)), quad "given by"
    x arrow.r det bold(N)(x) quad (mod T lr((R H))).
  $
  In order to avoid notational difficulties, we carry out the proof for the case
  $p = 3$, so now
  $ x = alpha_0 + alpha_1 g + alpha_2 g^2, quad "and" g^3 = h_0 in H. $
  Then
  $
    bold(N)(x) = mat(
      delim: "[",
      alpha_0, h_0 alpha_2, h_0 alpha_1;
      sigma lr((alpha_1)), sigma lr((alpha_0)), h_0 sigma lr((alpha_2));
      sigma^2 lr((alpha_2)), sigma^2 lr((alpha_1)), sigma^2 lr((alpha_0));
    ).
  $
  We find readily that
  $
    N^*(x) equiv N^* lr((alpha_0)) + h_0 N^* lr((alpha_1))
    + h_0^2 N^* lr((alpha_2)) (mod T lr((R H))).
  $
  <eq:cyclic-three-transfer-norm-congruence>
  Likewise, for $alpha,beta in R H$, we obtain
  $ N^* lr((alpha+beta)) equiv N^*(alpha) + N^*(beta) (mod T lr((R H))). $
  Together, these give
  $
    N^* lr((x+y)) equiv N^*(x) + N^*(y) (mod T lr((R H))),
    quad "for" x,y in R G.
  $
  <eq:transfer-norm-additivity-modulo-trace>
  #idx("Trace subgroup", target: [@eq:transfer-norm-additivity-modulo-trace])

  _Step 5._ We return to the situation in Step 3, where $x in (R G)^dot$ is a
  $p$-torsion element such that $tau(x) = 1$, and where $G$ contains an abelian
  normal subgroup $H$ of index $p$. Then $bold(N)(x)$ is a $p$-torsion element
  in $K_1 lr((R H))$, hence is represented by $r h_1$ for some $r in R^dot$,
  $h_1 in H$. Further, $r = 1$ because $tau(x) = 1$. Therefore we obtain
  $ N^*(x) = h_1 "in" (R H)^dot, $
  since the isomorphism $K_1 lr((R H)) tilde.equiv (R H)^dot$ is given by the
  determinant map.

  Put $G' = [G,G]$; since $G = ⟨H,g⟩$, we find at once that
  $
    G' = lr({h^(1-sigma): h in H}), quad "where"
    h^(1-sigma) = h (sigma lr((h)))^(-1).
  $
  The elements $lr({overline(g^i)})$ in $G^(a b)$ are clearly distinct.

  Let us write
  $
    x = sum_(i=0)^(p-1) sum_(h in H) a_(i h) h g^i,
    quad "so" tau(x) = sum sum a_(i h) overline(h g^i) in R G^(a b).
  $
  #source(190)
  From $tau(x) = 1$, we obtain, for each coset $z G'$ in $G$,
  $
    sum_(h in z G') a_(i h)
    = cases(1 quad & "if" i = 0 "and" z in G', 0 quad & "otherwise.")
  $
  <eq:abelianization-coefficient-sums>
  But also, by Step 4,
  $
    N^*(x) equiv sum_(i,h) N^* lr((a_(i h) h g^i))
    equiv sum_(i,h) a_(i h)^p h_0^i N^*(h) (mod T lr((R H))).
  $
  $
    equiv sum_z lr({sum_i sum_(h in z G') a_(i h)^p h_0^i N^*(h)})
    (mod T lr((R H))).
  $
  However, $N^*$ is trivial on commutators, so for $h in z G'$, the value
  $N^*(h)$ depends only on $z$. Furthermore,
  $ sum_(h in z G') a_(i h)^p equiv (sum_h a_(i h))^p (mod p R H). $
  Using @eq:abelianization-coefficient-sums, we thus obtain
  $
    N^*(x) equiv 1 (mod (T lr((R H)) + p R H)),
    quad "that is," h_1 - 1 in T lr((R H)) + p R H.
  $
  However, the coefficient of 1 in $T(alpha)$, for any $alpha in R H$, is a
  multiple of $p$. Therefore $h_1$ must equal 1, which shows that $N^*(x) = 1$.
  Then by @eq:induced-reduced-norm-transfer-determinant we obtain
  $ op("nr") x_j = psi lr((det bold(N)(x))) = psi lr((N^*(x))) = 1, $
  which completes the proof of the theorem in case $G$ has an abelian normal
  subgroup $H$ of index $p$.

  _Step 6._ Now let $G$ be an arbitrary $p$-group, $F$ a splitting field for
  $G$, and let $x in (R G)^dot$ be a $p$-torsion element such that $tau(x) = 1$
  in $R G^(a b)$. We must prove that $op("nr") x = 1$. Let $A_j$ be a Wedderburn
  component of $F G$, and (as in Step 3) we need only show that
  $op("nr") x_j = 1$ whenever $dim_F A_j > 1$. Let $S$ be a simple left
  $A_j$-module. By Blichfeldt’s Theorem @i:th:nilpotent-group-monomial, there
  exists a subgroup $H <= G$ of index $p$, and a simple left $F H$-module $M$,
  such that $S = op("ind")_H^G M$. Just as in Step 3, we have $G = ⟨H,g⟩$ for
  some $g$ with $g^p in H$, and again
  $ R G = plus.o.big (R H) g^i, quad S = plus.o.big g^i times.o M. $
  Since $G$ is a $p$-group and $abs(G colon H) = p$, we have $H ⊴ G$, and $R G$
  is a twisted group ring of the cyclic group $G slash H$ over the (possibly
  noncommutative) coefficient ring $R H$. We note further that
  $ S |_H = plus.o.big_0^(p-1) (g^i times.o M), $
  a sum of $p$ distinct $G$-conjugates of $M$.

  #source(191)
  Just as in Step 3, there is a homomorphism
  $bold(N): K_1 lr((R G)) arrow.r K_1 lr((R H))$. To compute $op("nr") x_j$, we
  use the formula
  $ op("nr") x_j = op("nr") bold(N)(x), $
  <eq:reduced-norm-under-transfer>
  where the entries of $bold(N)(x)$ act on the $F H$-module $M$.

  Now $H' = [H,H]$ is characteristic in $H$, hence normal in $G$, and there is a
  commutative diagram
  #p-group-transfer-comparison
  The group $G slash H'$ has an abelian normal subgroup $H slash H'$ of index
  $p$, so we can apply the results of Steps 3–5 to it. In particular, since
  $theta' lr((theta(x))) = tau(x) = 1$, it follows that $theta(x) = 1$. But then
  $rho bold(N)(x) = 1$, so by the induction hypothesis (applied to $H$) we
  conclude that $bold(N)(x) = 1$. Therefore $op("nr") x_j = 1$ by
  @eq:reduced-norm-under-transfer, so $x = 1$ in $K_1^F lr((R G))$, as desired.
  This completes the proof of @th:p-group-whitehead-p-torsionfree.
]

Continuing with our proof of Wall’s Theorem
@th:wall-integral-group-ring-torsion, we now use induction techniques to reduce
the problem to the case of hyper-elementary groups. Let $R$ be any commutative
ring, and let $G_0^R$ be the Frobenius functor which assigns to each finite
group $G$ the commutative ring $G_0^R lr((R G))$ (see
@exm:frobenius-modules-morphisms). Let $K_1$ be the Frobenius module over
$G_0^R$, which assigns to each $G$ the $G_0^R lr((R G))$-module $K_1 lr((R G))$.
As shown in Exercise @exc:whitehead-frobenius-module, there is a well-defined
action of $G_0^R$ on $K_1$, namely,
$ [X] [M,mu] = [X times.o_R M, 1 times.o mu] $
for each $R G$-lattice $X$, each $M in cal(P) lr((R G))$, and each
$mu in Aut_(R G) M$.

We investigate in more detail the behavior of $K_1 lr((R G))$ under induction
and restriction. Let $H <= G$ be finite groups. The inclusion
$R H subset.eq R G$ induces a “change of rings” homomorphism
$ op("ind")_H^G: K_1 lr((R H)) arrow.r K_1 lr((R G)), $
by mapping $GL_n lr((R H))$ into $GL_n lr((R G))$ for all $n$. On the other
hand, the restriction map carries $cal(P) lr((R G))$ into $cal(P) lr((R H))$,
since $R G$ is a free $R H$-module on $abs(G colon H)$ generators. Thus,
$ op("res")_H^G: K_1 lr((R G)) arrow.r K_1 lr((R H)) $
is given by $[M,mu] arrow.r [M_H,mu]$ for $M in cal(P) lr((R G))$,
$mu in Aut_(R G) M$.

#source(192)
#lemma[
  Let $R$ be a P.I.D. Then the functors
  $
    G arrow.r G^(a b) times R^dot quad "and"
    G arrow.r G^(a b) dot S K_1 lr((R G)) dot eta_* K_1 lr((R))
  $
  define $G_0^R lr((R G))$-submodules of the Frobenius module $K_1 lr((R G))$.
] <lem:whitehead-trivial-units-frobenius-submodules>
#ed-note[
  The first assertion is retained as stated, but its tensor-stability step
  requires that every finite-order matrix $A$ over $R$ satisfy $[A] = [det A]$
  in $K_1 lr((R))$. The argument below does not establish this for an arbitrary
  P.I.D. It does prove stability of $eta_* K_1 lr((R)) dot G^(a b)$ and its
  product with $S K_1 lr((R G))$. The second functor is written as a product of
  subgroups because
  $eta_* K_1 lr((R)) inter S K_1 lr((R G)) = eta_* S K_1 lr((R))$.
]
#proof[
  Let $H <= G$; the induction map arises from the inclusion $R H subset.eq R G$,
  which induces a map $H^(a b) times R^dot arrow.r G^(a b) times R^dot$. For the
  restriction map, consider an element $x in G$; its image in $K_1 lr((R G))$
  can be represented as $[R G,x_l]$, where $x_l$ is left multiplication by $x$
  on the right $R G$-module $R G$. Then
  $ op("res")_H^G [R G,x_l] = [R G |_(R H), x_l]. $
  If $G = union.dot g_i H$, then $R G = plus.o.big g_i R H$. Now $x_l$ permutes
  the left cosets $lr({g_i H})$, and is therefore represented by a monomial
  matrix. Factoring its permutation and diagonal parts gives the class
  $epsilon(x) V_H^G lr((x))$ in $K_1 lr((R H))$. Here, $epsilon(x)$ is the sign
  of the permutation, and $V_H^G$ is the transfer map defined in
  @i:eq:transfer-coset-formula (compare
  @i:prop:induced-character-determinant-transfer(i)). Thus in $K_1 lr((R H))$ we
  have
  $ op("res")_H^G lr((x)) = epsilon(x) V_H^G lr((x)) in R^dot times H^(a b), $
  as desired. Restriction sends a scalar class $eta_* a$ to
  $eta_* lr((a^(|G:H|)))$.

  Next, let $X = plus.o.big R x_i$ be a right $R G$-lattice of rank $d$ over
  $R$. For $g in G$, the product $[X] [R G,g_l]$ is
  $ [X times.o_R R G, 1 times.o g_l]. $
  The untwisting isomorphism of Exercise @i:exc:regular-inner-tensor-free sends
  $x times.o h$ to $x h^(-1) times.o h$. It conjugates $1 times.o g_l$ to the
  map $x times.o h mapsto x g^(-1) times.o g h$. If $rho_X lr((g^(-1)))$ is the
  matrix of $x mapsto x g^(-1)$ over $R$, this gives
  $
    [X] [R G,g_l] = eta_* [rho_X lr((g^(-1)))] dot g^d
    "in" K_1 lr((R G)).
  $
  Thus this product lies in $eta_* K_1 lr((R)) dot G^(a b)$. Tensoring a scalar
  class $eta_* a$ gives $eta_* lr((a^d))$, so this larger subgroup is stable.
  For the first, smaller subgroup the required condition is
  $[rho_X lr((g^(-1)))] = [det rho_X lr((g^(-1)))]$. Conversely, augmentation
  shows that this condition is necessary. Letting a cyclic group act by any
  finite-order matrix gives exactly the condition in the editorial note.
  Finally, the map $K_1 lr((R G)) arrow.r K_1 lr((F G))$ is a morphism of
  Frobenius modules over $G_0^R lr((R G))$, so the kernel $S K_1 lr((R G))$ is
  also a Frobenius module. This proves the second assertion, and the first under
  the stated condition on finite-order matrices. The arguments hold equally well
  for left modules.
]

#corollary[
  Let $R = "alg. int." lr({F})$. Then $op("Wh") lr((R G))$ and
  $op("Wh")^F lr((R G))$ are Frobenius modules over the Frobenius functor
  $G_0^ZZ lr((ZZ G))$.
] <cor:whitehead-frobenius-modules>
#proof[
  We may make $K_1 lr((R G))$ into a Frobenius module over $G_0^ZZ lr((ZZ G))$
  as follows: for each $ZZ G$-lattice $X$, and each $[M,mu] in K_1 lr((R G))$,
  where $M in cal(P) lr((R G))$, $mu in Aut M$, define
  $ [X] [M,mu] = [(R times.o_ZZ X) times.o_R M, 1 times.o mu], $
  where $times.o_R$ is the inner tensor product of a pair of $R G$-modules.
  #source(193)
  For an integer lattice $X$, the action matrix $rho_X lr((g^(-1)))$ is defined
  over $ZZ$. Since $K_1 lr((ZZ)) = lr({plus.minus 1})$, its scalar extension to
  $K_1 lr((R))$ equals its determinant. Thus the exact tensor calculation above
  applies without the unresolved arbitrary-P.I.D. step. It shows that
  $eta_* K_1 lr((R)) dot G^(a b)$ and its product with $S K_1 lr((R G))$ are
  Frobenius submodules of $K_1 lr((R G))$. Then by
  @exm:frobenius-modules-morphisms(iv), $op("Wh") lr((R G))$ and
  $op("Wh")^F lr((R G))$
  are also Frobenius modules over $G_0^ZZ lr((ZZ G))$.
]

In order to apply the above results, we need a modified version of Solomon’s
Induction Theorem @i:th:solomon-permutation-induction, and Swan’s application
thereof in @th:swan-hyperelementary-induction. Let $p$ be a rational prime;
recall from @rem:rational-hyperelementary-induction that a $p$-_hyper-elementary
group_ is a semidirect product $C times.r P$ of a cyclic $p'$-group $C$ and a
$p$-group $P$. Let us set
$ ZZ_((p)) = lr({a slash b: a,b in ZZ, (b,p) = 1}), $
the _localization of $ZZ$ at $p$_, so all other rational primes are invertible
in $ZZ_((p))$. We now have

#theorem[
  Let $p$ be prime, and let $cal(H)_p$ be the set of all $p$-hyper-elementary
  subgroups of a given finite group $G$. Then there exist rational numbers
  $c_i in ZZ_((p))$ such that
  $ 1_G = sum_(H_i in cal(H)_p) c_i (1_(H_i))^G, $
  where both sides are viewed as $ZZ_((p))$-valued class functions on $G$.
] <th:localized-solomon-hyperelementary-induction>
#idx(
  "Hyper-elementary group",
  target: [@th:localized-solomon-hyperelementary-induction],
)

The result follows easily from the proof of @i:th:solomon-permutation-induction,
once we modify @i:lem:integer-function-ring-unit so that it deals with
$ZZ_((p))$-valued functions. The details are left to the reader. Using the above
theorem, we obtain

#corollary[
  Let $p$ be prime, and let $cal(H)_p lr((G))$ be the set of all
  $p$-hyper-elementary subgroups of $G$. Let $Phi$ be the Frobenius functor
  which assigns to each group $G$ the $ZZ_((p))$-algebra
  $ Phi(G) = ZZ_((p)) times.o_ZZ G_0^ZZ lr((ZZ G)). $
  Then
  #enum(
    numbering: "(i)",
    [$Phi(G) = sum_(H in cal(H)_p lr((G))) op("ind")_H^G Phi(H)$.],
    [If $M$ is any Frobenius module over $Phi$, then for each $x in M(G)$,
      $
        op("res")_H^G x = 0 quad "for all" H in cal(H)_p lr((G))
        arrow.r.double x = 0.
      $],
  )
] <cor:localized-frobenius-hyperelementary-detection>

The result follows easily from @th:localized-solomon-hyperelementary-induction;
see the proof of @cor:frobenius-induction-annihilators(i).

We are now ready to apply these results to the study of torsion in Whitehead
groups. As remarked earlier, Wall’s Theorem @th:wall-integral-group-ring-torsion
is equivalent to the assertion that $op("Wh")^F lr((R G))$ is torsionfree. The
techniques of Frobenius functors allow us to reduce the problem to the case of
hyper-elementary groups, as follows:

#proposition[
  Let $p$ be a prime, and let $R = "alg. int." lr({F})$. Then
  $op("Wh") lr((R G))$
  is $p$-torsionfree if $op("Wh") lr((R H))$ is $p$-torsionfree for every
  $p$-hyper-elementary subgroup $H$ of $G$. The same holds with $op("Wh")^F$ in
  place of $op("Wh")$.
] <prop:whitehead-hyperelementary-torsion-detection>
#source(194)
#proof[
  By @cor:whitehead-frobenius-modules, both $op("Wh") lr((R G))$ and
  $op("Wh")^F lr((R G))$ are Frobenius modules over the Frobenius functor
  $G_0^ZZ lr((ZZ G))$. Now define
  $
    Phi(G) = ZZ_((p)) times.o_ZZ G_0^ZZ lr((ZZ G)),
    quad Psi(G) = ZZ_((p)) times.o_ZZ op("Wh")^F lr((R G)),
  $
  where $ZZ_((p))$ is the localization of $ZZ$ at $p$, and where
  $op("Wh")^F lr((R G))$ is viewed as $ZZ$-module. Then $Psi(G)$ has the same
  $p$-torsion as $op("Wh")^F lr((R G))$, so it suffices to test whether $Psi(G)$
  is $p$-torsionfree. As in @cor:localized-frobenius-hyperelementary-detection,
  $Phi$ is a Frobenius functor, and $Psi$ is a Frobenius module over $Phi$.
  Since the restriction of a $p$-torsion element is $p$-torsion, the proposition
  now follows from @cor:localized-frobenius-hyperelementary-detection(ii).
]

We remark that the above proof is valid for any commutative ring $R$.#ed-note[
  The converse printed in the original is false. For $R = ZZ$ and $p = 3$, take
  $G = S_9$ and $H = ⟨(1 2 3),(4 5 6),(7 8 9)⟩ tilde.equiv C_3^3$. Then
  $op("Wh") lr((ZZ G)) = 0$, whereas $S K_1 lr((ZZ H)) tilde.equiv C_3^3$ embeds
  in $op("Wh") lr((ZZ H))$. These computations are given in Oliver
  @bib:Oliver1988, introduction, Examples 4 and 6(i), and Theorem 14.1.
]

To finish the proof of Wall’s Theorem, we need one more preliminary result:

#lemma[
  Let $p,q$ be distinct primes, and let $R = "alg. int." lr({F})$. Let
  $overline(G) = G slash H$, where $H$ is a normal $q$-subgroup of $G$. Then if
  $op("Wh")^F lr((R overline(G)))$ is $p$-torsionfree, so is
  $op("Wh")^F lr((R G))$.
] <lem:whitehead-normal-prime-quotient-torsion>
#proof[
  Let $hat(R)$ be the $Q$-adic completion of $R$ at some prime $Q$ dividing $q$,
  so $hat(R)$ is a $q$-adic ring. By @i:prop:normal-p-subgroup-radical-kernel we
  have
  $
    hat(R) G slash rad hat(R) G tilde.equiv
    hat(R) overline(G) slash rad hat(R) overline(G).
  $
  Now $K_1 lr((hat(R) G))$ and $K_1 lr((hat(R) overline(G)))$ have _finite_
  Sylow $p$-subgroups, and by @th:wall-whitehead-pro-p-splitting, the map
  $ rho: K_1 lr((hat(R) G)) arrow.r K_1 lr((hat(R) overline(G))) $
  induces an isomorphism of these Sylow $p$-subgroups. By
  @th:p-adic-group-ring-sk1-p-group, the same holds for the map
  $
    rho': K_1^hat(F) lr((hat(R) G)) arrow.r
    K_1^hat(F) lr((hat(R) overline(G))).
  $
  Now consider the commutative diagram
  #quotient-completion-square
  Both vertical arrows are monomorphisms by Exercise
  @exc:whitehead-field-extension-injectivity, and $rho'$ gives an isomorphism of
  Sylow $p$-subgroups (which are finite, by the above discussion).
  #source(195)
  Therefore $rho_0$ maps the Sylow $p$-subgroup of $K_1^F lr((R G))$ injectively
  into that of $K_1^F lr((R overline(G)))$.

  On the other hand, the composite map
  $
    K_1^F lr((R)) times G^(a b) arrow.r^(rho_1) K_1^F lr((R G))
    arrow.r^(rho_0) K_1^F lr((R overline(G)))
  $
  is surjective on Sylow $p$-subgroups, by virtue of the equivalence of
  conditions (i)–(iii) below @eq:wall-torsion-equivalent-assertions, since we
  are assuming that $op("Wh")^F lr((R overline(G)))$ is $p$-torsionfree. This
  implies that $rho_0$ is a surjection of Sylow $p$-subgroups, whence so is
  $rho_1$. But then $op("Wh")^F lr((R G))$ is $p$-torsionfree, again by the
  conditions (i)–(iii). This completes the proof.
]

We are now ready to finish the proof of Wall’s Theorem. Let
$R = "alg. int." lr({F})$, and let $G$ be an arbitrary finite group. As remarked
earlier, we must show that $op("Wh")^F lr((R G))$ is torsionfree. For this, it
suffices to prove that for each prime $p$, $op("Wh")^F lr((R G))$ is
$p$-torsionfree. By @prop:whitehead-hyperelementary-torsion-detection, we need
only verify this when $G$ is $p$-hyper-elementary, say $G = C times.r P$ for
some cyclic $p'$-group $C$ and some $p$-group $P$. By repeated use of
@lem:whitehead-normal-prime-quotient-torsion, we may peel off the $q$-primary
components of $C$ for each prime $q$ dividing $abs(C)$, so the problem is
reduced to showing that $op("Wh")^F lr((R P))$ is $p$-torsionfree. But this case
has already been settled in Theorem @th:p-group-whitehead-p-torsionfree, so the
proof of Wall’s Theorem is completed.

#remark[
  If $R$ is a $p$-adic ring, the Whitehead group $op("Wh")^F lr((R G))$ may have
  $p$-torsion elements, even when $G$ is $p$-hyper-elementary.
] <rem:p-adic-hyperelementary-whitehead-torsion>

Turning next to $S K_1$, we prove:

#theorem(title: [Wall])[
  Let $R$ be a $p$-adic ring, and suppose that $G$ has an abelian Sylow
  $p$-subgroup. Then $S K_1 lr((R G)) = 1$.
] <th:wall-abelian-sylow-sk1-trivial>
#idx("Wall's Theorem", target: [@th:wall-abelian-sylow-sk1-trivial])
#idx(
  "SK₁",
  "of integral group rings",
  target: [@th:wall-abelian-sylow-sk1-trivial],
)
#proof[
  _Step 1._ By @th:p-adic-group-ring-sk1-p-group we know that $S K_1 lr((R G))$
  is a finite $p$-group, and so
  $ S K_1 lr((R G)) tilde.equiv ZZ_((p)) times.o_ZZ S K_1 lr((R G)), $
  where $ZZ_((p))$ is the localization of $ZZ$ at $p$, and where $S K_1$ is
  viewed as $ZZ$-module. Then $S K_1 lr((R G))$ is a Frobenius module over the
  Frobenius functor $ZZ_((p)) times.o_ZZ G_0^ZZ lr((ZZ G))$. Just as in the
  proof of @prop:whitehead-hyperelementary-torsion-detection, it follows that if
  $S K_1 lr((R H)) = 1$ for every $p$-hyper-elementary subgroup $H$ of $G$, then
  necessarily $S K_1 lr((R G)) = 1$. (This part of the argument does not require
  the hypothesis on the Sylow $p$-subgroup of $G$.)

  _Step 2._ Changing notation, we may now assume that
  $
    G = C times.r P, quad "where"
    C = "cyclic group of order" n, p divides.not n,
  $
  and $P$ is an abelian $p$-group. We proceed to study the group ring $R G$, and
  we may write $R G = (R C) compose P$, the twisted group ring (with trivial
  factor set) of the $p$-group $P$ over the commutative coefficient ring $R C$.
  #source(196)
  Note that $P$ acts by conjugation on $R C$.

  The decomposition of the ring $R C$ is given in Exercise
  @i:exc:cyclic-prime-to-p-unramified-decomposition. We have (letting $F$ be the
  quotient field of $R$)
  $ F C = product.co F_i, quad R C = product.co R_i, $
  where $F_i$ is a Galois unramified extension of $F$, and $R_i$ is the integral
  closure of $R$ in $F_i$. The action of $P$ on $R C$ permutes the summands
  $lr({R_i})$, not necessarily in a transitive fashion. Let $R_1,dots,R_m$ be
  the distinct conjugates of $R_1$ under the action of $P$; then
  $Lambda = (R_1 plus.o dots plus.o R_m) compose P$ is a ring direct summand of
  $R G$, and $R G$ decomposes into a direct sum of such $Lambda$’s. Thus, we
  need only prove that $S K_1 lr((Lambda)) = 1$.

  _Step 3._ Put
  $
    S = R_1 plus.o dots plus.o R_m
    = S delta_1 plus.o dots plus.o S delta_m,
  $
  where the $lr({delta_i})$ are primitive orthogonal idempotents in $S$, and
  where $P$ acts transitively on the $lr({delta_i})$. These $delta_i$ are also
  orthogonal idempotents in the ring $Lambda = S compose P$, and therefore
  $ Lambda tilde.equiv M_m lr((delta_1 Lambda delta_1)) $
  by Exercise @exc:conjugate-idempotent-matrix-ring.

  Next, we have
  $
    delta_1 Lambda delta_1 = (S delta_1) compose P_1 = R_1 compose P_1,
  $
  where $P_1 = lr({x in P: x delta_1 x^(-1) = delta_1})$. Of course,
  $
    S K_1 lr((Lambda)) tilde.equiv S K_1 lr((delta_1 Lambda delta_1))
    tilde.equiv S K_1 lr((R_1 compose P_1)),
  $
  and we must show that $S K_1 lr((R_1 compose P_1)) = 1$.

  Let
  $ P_0 = lr({x in P_1: x "acts trivially on" R_1}), $
  and set $H = P_1 slash P_0$. Then $H$ acts by conjugation on both $R_1$ and
  $P_0$, and now we put
  $ Gamma = R_1 compose P_1 = (R_1 P_0) compose H. $
  Here, $R_1 P_0$ is an ordinary group ring, and $(R_1 P_0) compose H$ is a
  twisted group ring of $H$ with possibly nontrivial factor set
  $f: H times H arrow.r P_0$.

  _Step 4._ The above group $H$ may be viewed as a subgroup of
  $op("Gal") lr((F_1 slash F))$, where $F_1$ is the quotient field of $R_1$. Let
  $F_0$ be the subfield of $F_1$ fixed (elementwise) by $H$, and let $R_0$ be
  its d.v.r.
  #source(197)
  Denote by $frak(p)_i$ the prime ideal of $R_i$, and set
  $overline(R)_i = R_i slash frak(p)_i$, $i = 0,1$. Since
  $F subset.eq F_0 subset.eq F_1$ and $F_1$ is unramified over $F$, it follows
  that $F_1$ is unramified over $F_0$, and that
  $
    H = op("Gal") lr((F_1 slash F_0))
    tilde.equiv op("Gal") lr((overline(R)_1 slash overline(R)_0))
  $
  (see the discussion in Exercise
  @i:exc:cyclic-prime-to-p-unramified-decomposition).

  Since $R_1$ is a $p$-adic ring and $P_0$ is a $p$-group, we have
  $ R_1 P_0 slash rad R_1 P_0 tilde.equiv overline(R)_1, $
  and $R_1 P_0$ is a commutative local ring. Then
  $ N = (rad R_1 P_0) compose H $
  is a two-sided ideal of $Gamma$ contained in $rad Gamma$, and
  $ Gamma slash N tilde.equiv overline(R)_1 compose H, $
  a crossed-product algebra (see
  @i:exm:crossed-products-twisted-group-algebras(i)). Since the factor set $f$
  takes values in $P_0$, and since $x equiv 1 (mod N)$ for every $x in P_0$, the
  above algebra has trivial factor set. By @i:exm:galois-twisted-group-algebra,
  we obtain
  $
    overline(R)_1 compose H tilde.equiv M_t lr((overline(R)_0)),
    quad "where" t = abs(H).
  $
  This shows that in fact $N = rad Gamma$.

  By the Theorem on Lifting Idempotents @i:th:lifting-idempotents, we may choose
  orthogonal idempotents $e_1,dots,e_t in Gamma$ with sum 1, whose images in
  $Gamma slash N$ are a set of primitive orthogonal idempotents. Then
  $
    Gamma = plus.o.big_(i=1)^t Gamma e_i
    tilde.equiv M_t lr((e_1 Gamma e_1))
  $
  by Exercise @exc:conjugate-idempotent-matrix-ring. Now $Gamma$ is a free left
  $(R_1 P_0)$-module of rank $t$, and $Gamma e_i tilde.equiv Gamma e_1$ for each
  $i$, so $Gamma e_1$ is a free $(R_1 P_0)$-module of rank 1. Therefore
  $
    (e_1 Gamma e_1)_(compose) = End_Gamma Gamma e_1
    subset.eq End_(R_1 P_0) lr((Gamma e_1)) tilde.equiv R_1 P_0.
  $
  This proves that $e_1 Gamma e_1$ is commutative, and in fact we see that
  $ e_1 Gamma e_1 = "subring of" R_1 P_0 "on which" H "acts trivially." $
  We remark also that
  $
    e_1 Gamma e_1 slash rad(e_1 Gamma e_1)
    tilde.equiv overline(e)_1 (Gamma slash rad Gamma) overline(e)_1
    tilde.equiv overline(R)_0,
  $
  #source(198)
  Combining our results, we obtain
  $
    Lambda tilde.equiv M_m lr((delta_1 Lambda delta_1))
    tilde.equiv M_m lr((R_1 compose P_1))
    tilde.equiv M_(m t) lr((e_1 Gamma e_1)).
  $
  But then
  $ S K_1 lr((Lambda)) tilde.equiv S K_1 lr((e_1 Gamma e_1)) = 1, $
  the latter step by virtue of @prop:commutative-semilocal-sk1. This completes
  the proof of Theorem @th:wall-abelian-sylow-sk1-trivial.
]

#remarks[
  #enum(
    numbering: "(i)",
    [Let us record here the following result, proved above:

      Let $Lambda = (R_1 plus.o dots plus.o R_m) compose P$, where $P$ is a
      finite abelian $p$-group acting transitively on the $p$-adic rings
      $lr({R_i})$. Let $P_1 = "stabilizer of" R_1 "in" P$,
      $P_0 = "subgroup of" P_1$ which acts trivially on $R_1$. Assume that the
      quotient field $F_1$ of $R_1$ is unramified over its fixed field
      $F_1^(P_1 slash P_0)$. Then, for some $t$,
      $ Lambda tilde.equiv M_(m t) lr((Delta)), $
      where the commutative local ring $Delta$ is the subring of $R_1 P_0$ fixed
      elementwise by $P_1 slash P_0$.

      Furthermore, under the same unramified hypothesis, the above holds
      whenever $P_0$ is abelian, whether or not $P$ is abelian.#ed-note[
        The unramified hypothesis is needed. For $R_1 = ZZ_(2)[i]$ and $P = C_2$
        acting by conjugation, $R_1 compose P$ maps onto $FF_2$, by reduction
        modulo $1+i$ and by sending $P$ to $1$. Dimension would force the
        asserted matrix ring to be $M_2 lr((ZZ_2))$, which admits no such unital
        quotient. The preceding application to the factors of $R C$ already
        satisfies the unramified hypothesis.
      ]],
    [The preceding calculation has been generalized by DeMeyer–Janusz
      @bib:DeMeyer1983, as follows. Let $R$ be an arbitrary commutative ring,
      and $G$ a finite group with commutator subgroup $G'$. They proved that the
      group ring $R G$ is an Azumaya algebra over its center (see Exercise
      @exc:azumaya-algebra-definition) if and only if $abs(G')$ is a unit in
      $R$.

      In particular, suppose that $R$ is a $p$-adic ring and that $p$ does not
      divide $abs(G')$. The ring direct summands of the center of $R G$ have
      trivial Brauer group, since they are complete local rings with finite
      residue class fields. It follows that $R G$ is a direct sum of matrix
      rings of the form $M_n lr((Gamma))$, with $Gamma$ a commutative
      $R$-algebra, f.g./$R$ as module. But then
      $ S K_1 lr((M_n lr((Gamma)))) tilde.equiv (S K_1 lr((Gamma))) = 1 $
      by @prop:commutative-semilocal-sk1, which shows that $S K_1 lr((R G)) = 1$
      whenever $abs(G') != 0 (mod p)$. It is easily checked that this condition
      on $abs(G')$ is satisfied when $G$ is a $p$-hyper-elementary group with
      abelian Sylow $p$-subgroup.],
  )
] <rem:wall-crossed-product-azumaya-generalization>

#exercises-heading

#exercise[
  Let $tau: u arrow.r u^*$ be the involution of $ZZ G$ defined by
  $g arrow.r g^(-1)$, $g in G$, extended by linearity. Prove that $tau$ acts
  trivially on the Whitehead group
  $
    op("Wh")^QQ lr((ZZ G)) = K_1 lr((ZZ G)) slash
    (plus.minus G^(a b) times S K_1 lr((ZZ G))).
  $
  #hint([@exc:integral-whitehead-involution-trivial], caption: [Hint (Wall):])[
    Let $QQ G = product.co A_j$ be the Wedderburn decomposition of $QQ G$,
    $F_j = "center of" A_j$, and let $u in QQ G$ be expressed as $u = sum u_j$,
    $u_j in A_j$.
    #source(199)
    Let $op("nr")_j$ be the reduced norm from $A_j$ to $F_j$, extended to a map
    on $GL lr((A_j))$.

    Put $U = op("nr") K_1 lr((ZZ G)) subset.eq C^+$, with $C^+$ as in
    @eq:semisimple-positive-norm-subgroup. The reduced norm
    $op("nr") = product_j op("nr")_j$ induces an isomorphism
    $ op("Wh")^QQ lr((ZZ G)) tilde.equiv U slash "torsion subgroup of" U. $
    It suffices to show that for fixed $j$, and any $u in GL lr((ZZ G))$,
    $
      op("nr")_j lr((u^*))_j = (op("nr")_j lr((u_j))) dot
      "torsion element of" F_j^dot.
    $
    For any absolutely irreducible complex representation $bold(M)$ of $G$,
    there exists an invertible matrix $bold(P)$ such that
    $
      bold(M) lr((g^(-1))) = bold(P) overline(bold(M)(g))^t bold(P)^(-1)
      quad "for" g in G,
    $
    where bar denotes complex conjugation. For matrices over $ZZ G$, the
    involution also transposes the outer matrix indices. It follows that, up to
    similarity, $bold(M) lr((u^*))$ is the complex conjugate transpose of
    $bold(M)(u)$. Therefore
    $ op("nr")_j lr((u^*))_j = overline(op("nr")_j lr((u_j))). $
    Both $u$ and $u^(-1)$ preserve an integral representation lattice, so
    $alpha = op("nr")_j lr((u_j))$ is an algebraic unit. Put
    $frak(O)_j = "alg. int." lr({F_j})$. Let $theta_1,dots,theta_m$ be the
    inequivalent embeddings of $F_j$ into $CC$, and define
    $
      Phi(alpha) = (log abs(theta_1 lr((alpha))),dots,
        log abs(theta_m lr((alpha)))), quad "for" alpha in frak(O)_j^dot.
    $
    As in the proof of Dirichlet’s Unit Theorem, $ker Phi$ is the finite group
    of roots of unity in $F_j$. These character fields lie in a cyclotomic
    splitting field, whose complex conjugation is central. Thus every embedding
    commutes with conjugation, and $Phi(overline(alpha) slash alpha) = 0$. Hence
    $overline(alpha) slash alpha$ is a root of unity, proving the assertion.
  ]
] <exc:integral-whitehead-involution-trivial>

#exercise[
  Let $1 = e_1 + dots + e_m$ be a decomposition into orthogonal idempotents in a
  ring $Lambda$, and suppose that for each $i$, there exists a unit
  $u_i in Lambda^dot$ such that $u_i e_1 u_i^(-1) = e_i$. Show that
  $ Lambda tilde.equiv M_m lr((e_1 Lambda e_1)). $
  #hint([@exc:conjugate-idempotent-matrix-ring])[
    By Exercise @i:exc:conjugate-idempotent-decompositions, these $lr({u_i})$
    exist if and only if $Lambda e_i tilde.equiv Lambda e_1$ for each $i$. Next,
    the hypothesis implies that $Lambda tilde.equiv (Lambda e_1)^((m))$ as left
    $Lambda$-modules. Therefore
    $
      Lambda^compose tilde.equiv End_Lambda lr((Lambda))
      tilde.equiv End_Lambda lr(((Lambda e_1)^((m))))
      tilde.equiv M_m lr((End_Lambda lr((Lambda e_1))))
    $
    $
      tilde.equiv M_m lr(((e_1 Lambda e_1)^compose))
      tilde.equiv lr({M_m lr((e_1 Lambda e_1))})^compose.
    $
  ]
] <exc:conjugate-idempotent-matrix-ring>

#exercise[
  Let $G$ be a finite abelian group. Show that
  $ K_1 lr((ZZ G)) tilde.equiv (ZZ G)^dot times S K_1 lr((ZZ G)), $
  and that there is a canonical decomposition
  $ (ZZ G)^dot tilde.equiv lr({plus.minus 1}) times G times F $
  for some free abelian group $F$.

  (References: Dennis @bib:Dennis1980, Roggenkamp–Scott @bib:Roggenkamp1983.)
] <exc:abelian-integral-group-ring-unit-decomposition>

#source(200)
#exercise[
  Let $R = "alg. int." lr({F})$, and let $Lambda = R G$, where $G$ is a finite
  group. Let $Gamma$ be a maximal $R$-order in $F G$ containing $Lambda$. Prove
  that the sequence
  $
    1 arrow.r S K_1 lr((Lambda)) arrow.r K_1 lr((Lambda))
    arrow.r K_1 lr((Gamma))
  $
  is exact.
  #hint([@exc:group-ring-maximal-order-whitehead-kernel], caption: [Hint
    (Oliver):])[
    It suffices to show that $S K_1 lr((Lambda)) arrow.r
    S K_1 lr((Gamma))$ is the zero map. By @th:keating-global-maximal-order-sk1,
    this amounts to proving that
    $ S K_1 lr((Lambda_P)) arrow.r S K_1 lr((Gamma_P)) $
    is the zero map for each prime ideal $P$ of $R$. But $S K_1 lr((Gamma_P))$
    is a $p'$-group where $p$ is the rational prime in $P$, while
    $S K_1 lr((Lambda_P))$ is a $p$-group.
  ]
] <exc:group-ring-maximal-order-whitehead-kernel>

#exercise[
  Prove that $op("Wh")^F lr((R G))$ is torsionfree if $R$ is a $p$-adic ring and
  $G$ is a $p$-group.
  #hint([@exc:p-adic-p-group-whitehead-torsionfree])[
    By @th:wall-whitehead-pro-p-splitting,
    $K_1 lr((R G)) tilde.equiv ("pro-"p"-group") times overline(R)^dot$, where
    $overline(R)^dot$ is the group of roots of unity in the residue class field
    $overline(R)$ of $R$. This group $overline(R)^dot$ is isomorphic to the
    prime-to-$p$ torsion subgroup of $R^dot$. Now let $x in K_1 lr((R G))$ be a
    torsion element in $op("Wh")^F lr((R G))$. Write $x = x_1 x_2$, with
    $x_1 in "pro-"p"-group"$, $x_2 = p'$-element. Then $x_2$ is a root of unity
    in $R^dot$, so $x$ and $x_1$ have the same image in $op("Wh")^F lr((R G))$.
    Then $x_1 = 1$ in $op("Wh")^F lr((R G))$, since $op("Wh")^F lr((R G))$ is
    $p$-torsionfree.
  ]
] <exc:p-adic-p-group-whitehead-torsionfree>
