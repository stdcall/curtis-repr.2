#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/53-swan-subgroups.typ": *

== The Swan Subgroup of the Class Group <sec:swan-subgroup-class-group>

#source(359)
=== The Swan Subgroup <ss:swan-subgroup>

Let $G$ be a group of order $n$, and set
$ sigma = sigma_G = sum_(x in G) x in ZZ G, $
so $e = sigma slash n$ is a central idempotent in the group algebra $QQ G$. For
each nonzero integer $r$ relatively prime to $n$, let us define a _Swan
module_#idx(
  "Swan module",
)
$ chevron.l r,sigma chevron.r = ZZ G r + ZZ G sigma = ZZ G r + ZZ sigma, $
a two-sided ideal of $ZZ G$. If $p$ is any prime divisor of $n$, then
$chevron.l r,sigma chevron.r_p = ZZ_p G$, so by §@i:ss:genus-basic-properties
$chevron.l r,sigma chevron.r$ is locally free as left ideal of $ZZ G$, and
determines a class $[r,sigma] in op("Cl") ZZ G$. As we shall see in a moment,
the set of all classes $[r,sigma]$ with $(r,n)=1$ forms a subgroup $T(G)$ of
$op("Cl") ZZ G$, called the _Swan subgroup_ of $op("Cl") ZZ G$. In fact, $T(G)$
is a subgroup of the kernel group $D(ZZ G)$. #idx(
  "Swan subgroup of the class group",
  target: [@ss:swan-subgroup],
)
#nidx("$T(G)$", "Swan subgroup of D(ℤG)", target: [@ss:swan-subgroup])
Consider the fiber product #numbered-block(
  swan-fiber-product,
) <eq:swan-fiber-product>
where $epsilon$ is the augmentation map. This gives rise to an exact sequence
$
  ZZ^dot times K_1 lr((Gamma)) arrow.r^h overline(ZZ)^dot
  arrow.r^partial D(ZZ G) -> D(Gamma) -> 0,
$ <eq:swan-kernel-group-sequence>
by @th:kernel-group-mayer-vietoris. We claim that
$ partial(overline(r)) = [r,sigma] in D(ZZ G). $
<eq:swan-boundary-class>
In fact, the final part of the proof of
@th:reiner-ullom-class-group-mayer-vietoris shows that
$
  partial(overline(r)) = [M], quad "where"
  M = {(z,y) in ZZ plus.o Gamma: overline(z) = overline(r) overline(y)
    "in" overline(ZZ)}.
$
On the other hand,
$ZZ G tilde.equiv {(z,y): overline(z)=overline(y) "in" overline(ZZ)}$. There is
an embedding $M -> ZZ G$, given by $(z,y) in M arrow.r (z,r y) in ZZ G$. But
$r in ZZ G$ corresponds to $(r,r) in ZZ plus.o Gamma$, and $sigma in ZZ G$ to
$(n,0) in ZZ plus.o Gamma$. Therefore the image of $M$ in $ZZ G$ is precisely
$chevron.l r,sigma chevron.r$, which proves @eq:swan-boundary-class. This shows
that $T(G)$ is a subgroup of $D(ZZ G)$, and the sequence
$
  ZZ^dot times K_1 lr((Gamma)) arrow.r^h overline(ZZ)^dot
  arrow.r^partial T(G) -> 0
$ <eq:swan-subgroup-k1-sequence>
is exact. Further, if $QQ G$ satisfies the Eichler condition (or, more
generally, if $ZZ G$
#source(360)
has locally free cancellation), then as in @th:kernel-group-mayer-vietoris the
above sequence simplifies to an exact sequence
$
  ZZ^dot times Gamma^dot arrow.r^h overline(ZZ)^dot
  arrow.r^partial T(G) -> 0.
$ <eq:swan-subgroup-unit-sequence>
Since $h$ is a homomorphism, it follows from the group structure of
$op("Cl") ZZ G$ that
$
  chevron.l r,sigma chevron.r plus.o chevron.l s,sigma chevron.r
  tilde.equiv ZZ G plus.o chevron.l r s,sigma chevron.r
  quad "for" (r s,n)=1.
$
(One can also prove this result, due to Swan, by giving an explicit
isomorphism.) Furthermore,
$chevron.l r,sigma chevron.r = chevron.l -r,sigma chevron.r$, while by
@th:milnor-projective-patching,
$
  chevron.l r,sigma chevron.r tilde.equiv chevron.l s,sigma chevron.r
  <=> overline(s)=overline(gamma) overline(r) "in" overline(ZZ)
  quad "for some" gamma in Gamma^dot.
$
We remark finally that by Exercise @exc:swan-module-stabilization,
$ chevron.l r,sigma chevron.r plus.o ZZ tilde.equiv ZZ G plus.o ZZ. $
From @eq:swan-subgroup-k1-sequence we obtain:

#proposition[
  #case-list(
    numbering: "(i)",
    [#case[$T(G)$ is a homomorphic image of
        $overline(ZZ)^dot slash {plus.minus 1}$, and therefore $abs(T(G))$
        divides $phi(n) slash 2$ if $n>2$.]
      <case:swan-subgroup-unit-quotient>],
    [#case[If $G$ is a $p$-group, then $T(G)$ is cyclic.]
      <case:swan-subgroup-prime-power-cyclic>],
    [#case[$T(G)=0$ if $G$ is cyclic or dihedral.]
      <case:swan-subgroup-cyclic-dihedral-trivial>],
  )
] <prop:swan-subgroup-elementary-properties>
#proof[
  Part @case:swan-subgroup-unit-quotient is clear from
  @eq:swan-subgroup-k1-sequence, since $overline(ZZ)^dot$ has order $phi(n)$.
  Next, if $n$ is a prime power $p^k$, then $overline(ZZ)^dot$ is cyclic for odd
  $p$, while for $p=2$ and $k>1$,
  $overline(ZZ)^dot tilde.equiv {plus.minus 1} times
  ("cyclic group of order" phi(n) slash 2)$, which gives
  @case:swan-subgroup-prime-power-cyclic.

  To prove @case:swan-subgroup-cyclic-dihedral-trivial, first let
  $G=chevron.l x:x^n=1 chevron.r$, and let $(r,n)=1$. Then the element
  $u=(x^r-1) slash (x-1) in Gamma$ depends only on the class of $r(mod n)$, and
  $u in Gamma^dot$ since $u^(-1)=(x-1) slash (x^r-1)$ in $Gamma$. The element
  $u in Gamma^dot$ maps onto $overline(r) in overline(ZZ)^dot$, so $h$ is
  surjective. Thus $T(G)=0$ by @eq:swan-subgroup-unit-sequence. For the dihedral
  case, see Exercise @exc:dihedral-swan-subgroup-trivial or Theorem
  @th:metacyclic-swan-subgroup-order.
]
The locally free left ideal $chevron.l r,sigma chevron.r$ of $ZZ G$ may be
expressed as $chevron.l r,sigma chevron.r=ZZ G alpha$ for some idele
$alpha=(alpha_p) in J(QQ G)$. If $p divides.not r$, then
$chevron.l r,sigma chevron.r_p = ZZ_p G$, and we may take $alpha_p=1$. On the
other hand, if $p divides r$ then $p divides.not n$, and so
$ZZ_p G=ZZ_p plus.o Gamma_p$. Viewing elements of $ZZ_p G$ as ordered pairs from
$ZZ_p plus.o Gamma_p$, we have $r=(r,r)$, $sigma=(n,0)$. Thus
$chevron.l r,sigma chevron.r_p$ is the ideal generated by $(r,r)$ and $(n,0)$,
that is, $(1,r)(ZZ_p plus.o Gamma_p)$. This yields
$
  chevron.l r,sigma chevron.r = ZZ G alpha,
  quad "where" alpha=(alpha_p), quad "and"
  alpha_p=cases(
    (1,1) "," & quad p divides.not r,
    (1,r) "," & quad p divides r,
  )
$ <eq:swan-module-first-idele>
with $(1,1)$ and $(1,r)$ viewed as elements of $ZZ_p plus.o Gamma_p$.

#source(361)
Another version of the above is also useful. Let $e=sigma slash n$ as above, and
put
$ u=(1-e)+r e = "central unit in" QQ G. $
<eq:swan-central-unit>
Then
$
  chevron.l r,sigma chevron.r
  tilde.equiv (u slash r) chevron.l r,sigma chevron.r
  = chevron.l u,(u sigma) slash r chevron.r = chevron.l u,sigma chevron.r,
$
the last because $u sigma=r sigma$. We may write
$chevron.l u,sigma chevron.r = ZZ G dot beta$ for some idele $beta=(beta_p)$. If
$p divides.not n$, then $e in chevron.l u,sigma chevron.r$ and
$chevron.l u,sigma chevron.r_p = chevron.l u,e chevron.r = ZZ_p G$, so
$beta_p=1$. If $p divides n$ then $sigma=(u slash r)sigma in u ZZ_p G$, so
$chevron.l u,sigma chevron.r = u dot ZZ_p G$. Thus
$
  chevron.l r,sigma chevron.r tilde.equiv chevron.l u,sigma chevron.r
  = ZZ G beta,
  quad "where" beta_p=cases(
    1 & quad "if" p divides.not n,
    u & quad "if" p divides n,
  )
$ <eq:swan-module-central-unit-idele>
with $u$ as in @eq:swan-central-unit (compare
@exm:swan-module-det-representative). We now prove:

#proposition[
  A surjection $phi:G -> overline(G)$ induces a surjection
  $T(G) -> T(overline(G))$.
] <prop:swan-subgroup-quotient-surjection>
#proof[
  We have already seen in @prop:kernel-group-ring-homomorphism that $phi$
  induces a map $D(ZZ G) -> D(ZZ overline(G))$. Now let $r in ZZ$ be relatively
  prime to $abs(overline(G))$, and we may assume that also $(r,n)=1$. Write
  $
    QQ G tilde.equiv QQ plus.o B,
    quad QQ overline(G) tilde.equiv QQ plus.o overline(B).
  $
  Then $phi$ induces $QQ -> QQ$, $B -> overline(B)$, and $phi$ carries the idele
  $alpha$ associated with $chevron.l r,sigma chevron.r$ onto the idele
  $overline(alpha)$ associated with $chevron.l r,sigma_(overline(G)) chevron.r$,
  by @eq:swan-module-first-idele. Thus $phi[r,sigma]=[r,sigma_(overline(G))]$,
  which proves the proposition.
]

#theorem(title: [Ullom @bib:Ullom1976])[
  If $H$ is a subgroup of $G$, then the restriction map $op("res")_H^G$ takes
  $T(G)$ onto $T(H)$, and indeed $op("res")[r,sigma_G]=[r,sigma_H]$.
] <th:swan-subgroup-restriction-surjection>
#idx("Ullom's Theorem", target: [@th:swan-subgroup-restriction-surjection])
#proof[
  The easiest proof uses the Hom description of the class group. By
  @exm:swan-module-det-representative, the class $[r,sigma] in T(G)$ is
  represented by the function
  $
    f in Hom_Omega lr((op("ch") G, J(E))),
    quad "where" f_p lr((zeta))=scripts(det)_zeta lr((beta_p))
    "for" zeta in op("Irr") G.
  $
  Thus for $zeta in op("Irr") G$, we have from
  @eq:swan-module-central-unit-idele
  $
    f_p lr((zeta))=1 "if" p divides.not n; quad
    f_p lr((zeta))=1 "if" p divides n "and" zeta != 1; quad
    f_p lr((1_G))=r "if" p divides n.
  $
  We observe next that $op("res")_H^G:op("Cl") ZZ G -> op("Cl") ZZ H$ arises
  from the induction map $op("ind")_H^G:op("ch") H -> op("ch") G$. If
  $g=op("res")_H^G f$, then by @rem:hom-change-of-group-restriction
  $ g(zeta)=f(op("ind")_H^G zeta) quad "for" zeta in op("ch") H. $
  #source(362)
  But by Frobenius reciprocity, for $zeta in op("Irr") H$ we have
  $ (1_G,op("ind")_H^G zeta)_G = (1_H,zeta)_H, $
  and therefore
  $ g(zeta)=1 "for" zeta != 1_H, quad g(1_H)=f(1_G). $
  Let $g'$ be the function in $Hom_Omega lr((op("ch") H, J(E)))$ which
  represents $[r,sigma_H]$, so for $zeta in op("Irr") H$,
  $
    g'(zeta)=1 "for" zeta != 1_H, quad
    g'_p lr((1_H))=cases(
      1 "," & quad p divides.not abs(H),
      r "," & quad p divides abs(H).
    )
  $
  Thus $g$ and $g'$ agree, except at the primes $q$ which divide $abs(G)$ but
  not $abs(H)$. For such $q$ (if any) we have
  $ g_q lr((1_H))=r, quad g'_q lr((1_H))=1. $
  However, we may write $ZZ_q H=ZZ_q plus.o Delta$, with $Delta$ a maximal order
  in $QQ_q H slash QQ_q sigma_H$. Choose $xi=(r,1) in (ZZ_q H)^dot$, so $xi$ may
  be viewed as a unit idele concentrated at position $q$. Then for
  $zeta in op("Irr") H$,
  $
    op("Det")_zeta xi=cases(
      1 "," & quad zeta != 1,
      r "," & quad zeta=1.
    )
  $
  This shows that $g=g' dot op("Det") xi$, so $g$ and $g'$ represent the same
  element in $op("Cl") ZZ H$, by @th:frohlich-hom-kernel-group-formula.
  Therefore $op("res")[r,sigma_G]=[r,sigma_H]$, as desired.
]

As an easy consequence of the above, we deduce: #theorem(title: [Ullom
  @bib:Ullom1976])[
  The Artin exponent $A(G)$ of $G$ annihilates the Swan subgroup $T(G)$ of
  $op("Cl") ZZ G$. Therefore $abs(G) T(G)=0$.
] <th:artin-exponent-annihilates-swan-subgroup>
#idx("A(G)", target: [@th:artin-exponent-annihilates-swan-subgroup])
#idx("Artin exponent", target: [@th:artin-exponent-annihilates-swan-subgroup])
#proof[
  From the definition of the Artin exponent (see §@sec:artin-exponent), we may
  write
  $ A(G)=sum_i op("ind")_(C_i)^G x_i quad "in" op("ch") QQ G, $
  where the ${C_i}$ are cyclic subgroups of $G$, and $x_i in op("ch") QQ C_i$.
  By @cor:class-kernel-groups-field-frobenius, $op("Cl") ZZ G$ is a Frobenius
  module over the Frobenius functor#idx("Frobenius functor") $op("ch") QQ G$.
  For $t in T(G)$ we obtain
  $
    A(G)t=sum_i t op("ind")_(C_i)^G x_i
    =sum_i op("ind")_(C_i)^G lr((op("res")_(C_i)^G t dot x_i)),
  $
  using a Frobenius identity. But $T(C_i)=0$ by
  @prop:swan-subgroup-elementary-properties, and $op("res")_(C_i)^G t in T(C_i)$
  by @th:swan-subgroup-restriction-surjection,
  #source(363)
  so $A(G)t=0$, as desired. The second assertion of the theorem holds because
  $A(G)$ divides $abs(G)$.
]

#corollary[
  The restriction map $T(G) -> product_p T(G_p)$ is surjective, where ${G_p}$
  ranges over a set of Sylow subgroups of $G$.
] <cor:swan-subgroup-sylow-restriction>
#proof[
  For each $p$, $T(G_p)$ is a $p$-group, and $op("res"):T(G) -> T(G_p)$ is
  surjective, by @th:swan-subgroup-restriction-surjection and
  @th:artin-exponent-annihilates-swan-subgroup. Now use the Chinese Remainder
  Theorem.
]

#theorem(title: [Ullom @bib:Ullom1976])[
  Let $G$ be an elementary abelian $p$-group of order $p^(s+1)$, where $p$ is an
  odd prime and $s>=0$. Then $T(G)$ is cyclic of order $p^s$, and is generated
  by the class $[1+p,sigma]$.
] <th:elementary-abelian-odd-swan-subgroup>
#idx("Ullom's Theorem", target: [@th:elementary-abelian-odd-swan-subgroup])
#proof[
  Let $K=QQ(omega)$, $R=ZZ[omega]$, where $omega$ is a primitive $p$-th root
  of 1. Then
  $
    QQ G tilde.equiv QQ plus.o K^((m)), quad "where" m=(p^(s+1)-1) slash (p-1).
  $
  Then $Gamma=ZZ G slash ZZ sigma$ is an order in $K^((m))$, and hence is
  contained in the unique maximal order $R^((m))$. Since
  $overline(ZZ)^dot tilde.equiv C_(p-1) times chevron.l 1+p chevron.r$, a
  product of cyclic groups of orders $p-1$ and $p^s$, respectively, the exact
  sequence @eq:swan-subgroup-unit-sequence becomes
  $
    ZZ^dot times Gamma^dot arrow.r^h
    C_(p-1) times chevron.l 1+p chevron.r arrow.r^partial T(G) -> 0.
  $
  Since $T(G)$ is a $p$-group by @th:artin-exponent-annihilates-swan-subgroup,
  it suffices to show that $h(Gamma^dot) subset.eq C_(p-1)$, for then $T(G)$ is
  generated by $partial(1+p)$, that is, by $[1+p,sigma]$.

  Let us view $Gamma$ as a subring of $R^((m))$; each $u in Gamma^dot$ is of the
  form $u=(u_1,dots,u_m)$, $u_i in R^dot$, and we must show that
  $h(u) in C_(p-1)$, that is, $h(u)$ has order dividing $p-1$. For
  $a=1,dots,p-1$, let $phi_a in op("Aut") G$ be defined by $phi_a lr((g))=g^a$,
  $g in G$. Then $phi_a$ induces a ring automorphism of $QQ G$, carrying each
  simple component $K$ of $QQ G$ onto itself via the automorphism
  $omega arrow.r omega^a$. Therefore
  $ product_(a=1)^(p-1) phi_a lr((u_i))=N_(K slash QQ) u_i=+1, $
  since the norm $N(u_i)=plus.minus 1$, and $N(u_i)>0$ because $p$ is odd.
  Consequently $product_a phi_a lr((u))=1$ in $Gamma^dot$. But for each $a$, $u$
  and $phi_a lr((u))$ have the same image $overline(u) in overline(ZZ)^dot$.
  Thus $overline(u)^(p-1)=1$ in $overline(ZZ)^dot$, so $h(u) in C_(p-1)$, and
  the proof is completed.
]

The case $p=2$ is even easier: #theorem[
  For $G$ elementary abelian of order $2^(s+1)$, where $s>=1$, $T(G)$ is cyclic
  of order $2^(s-1)$, generated by $[5,sigma]$.
] <th:elementary-abelian-two-swan-subgroup>
#proof[
  Let $n=2^(s+1)$, so
  $overline(ZZ)^dot tilde.equiv {plus.minus 1} times chevron.l 5 chevron.r$, a
  product of cyclic groups of orders $2$, $2^(s-1)$, respectively. We may assume
  $s>=2$, the case $s=1$ being trivial. Then
  $ 5^(2^(s-2)) equiv 1+2^s (mod n). $
  #source(364)
  Set $r=1+2^s$, so
  $ [5,sigma]^(2^(s-2))=[r,sigma], $
  and we need only show that $[r,sigma] != 0$ in $D(ZZ G)$.

  Write $G=chevron.l y chevron.r times H$, where $y^2=1$ and $H=C_2^((s))$.
  There is a fiber product
  #elementary-two-fiber-product
  where $f(y)=1$, $g(y)=-1$. This yields an exact Mayer–Vietoris sequence
  $
    (ZZ H)^dot times (ZZ H)^dot arrow.r^psi (k H)^dot
    arrow.r^delta D(ZZ G) -> D(ZZ H) plus.o D(ZZ H) -> 0.
  $
  By Exercise @exc:fiber-product-boundary-idele, we have (noting that
  $1+sigma_H in (k H)^dot$)
  $
    delta(1+sigma_H)=[ZZ G gamma], quad "where" gamma=(gamma_p),
    quad "and" gamma_p=cases(
      (1,1) "," & quad p "odd",
      (1+sigma_H,1) "," & quad p=2.
    )
  $
  Now let $u=1-e+r e=1+sigma slash 2$ as in @eq:swan-central-unit. Then
  $
    chevron.l r,sigma chevron.r tilde.equiv chevron.l u,sigma chevron.r
    =ZZ G beta,
    quad "where" beta_p=cases(
      (1,1) "," & quad p "odd",
      u "," & quad p=2.
    )
  $
  But viewing $u$ as element of $QQ G$, we have $f(u)=1+sigma_H$, $g(u)=1$. It
  follows that
  $ delta(1+sigma_H)=[r,sigma] quad "in" D(ZZ G). $
  To show that $[r,sigma] != 0$, it therefore suffices to prove that
  $1+sigma_H in.not im psi$. But every unit of $ZZ H$ is a torsion unit, and
  hence has the form $plus.minus h$, $h in H$, by Higman's Theorem. Since
  $psi(plus.minus h)$ cannot equal $1+sigma_H$ in $k H$, it follows that
  $[r,sigma] != 0$, and establishes the theorem.
]

In the same vein, we have: #theorem[
  Let $G=C_2^((l)) times C_4^((m))$, where $l+m>=2$. Then $T(G)$ is cyclic of
  order $2^(l+2m-2)$, with generator $[5,sigma]$.
] <th:abelian-exponent-four-swan-subgroup>
#proof[
  If $m=0$, the result follows from @th:elementary-abelian-two-swan-subgroup.
  Assume $m>0$. The preceding argument carries over to this case. Write
  $G=chevron.l y chevron.r times H$
  #source(365)
  where $y^4=1$, and use the fiber product
  #exponent-four-fiber-product
  where $G_0=chevron.l y^2 chevron.r times H$, $R=ZZ[i]$, and $k=ZZ slash 2 ZZ$.
]

The situation for quaternion groups is as follows: #theorem[
  Let $G$ be the generalized quaternion group of order $2^(n+2)$, where $n>=1$.
  Then $T(G)=D(ZZ G)$ is of order $2$, with generator $[3,sigma]$.
] <th:quaternion-swan-subgroup-order-two>
#idx("Quaternion group", target: [@th:quaternion-swan-subgroup-order-two])
#proof[
  We treat only the case $n=1$, and use the notation and proof of
  @th:quaternion-two-group-kernel-order-two. As shown there, $D(ZZ G)$ has order
  $2$, and its nontrivial element may be taken as $[ZZ G xi]$, where $xi=(xi_p)$
  is the idele with $xi_p=1$ for $p$ odd, and
  $ xi_2=(i+j+k,1) in Gamma_2^dot times Delta_2^dot. $
  (As first component, we could have used any element of $Gamma_2^dot$ with
  reduced norm $3(mod 8)$.) On the other hand,
  $[3,sigma]=[5,sigma]=[ZZ G beta]$, where $beta=(beta_p)$, with $beta_p=1$ for
  $p$ odd, and
  $
    beta_2=1+4(sigma slash 8)=1+(sigma slash 2)=(1,1+sigma_H)
    in Gamma_2^dot times Delta_2^dot.
  $
  Then $xi_2 beta_2^(-1)=(i+j+k,(2+x+y+x y)^(-1)) in (ZZ_2 G)^dot$, so
  $ZZ G xi=ZZ G beta$. This completes the proof.
]

For $G$ a dihedral $2$-group, we already know from
@th:dihedral-two-group-trivial-kernel that $D(ZZ G)$ is trivial, whence so is
$T(G)$. On the other hand, we have: #theorem(title: [Endo])[
  Let $G$ be the semidihedral group of order $2^(n+2)$, $n>=2$, defined by
  $
    op("SD")_n=chevron.l a,b:a^(2^(n+1))=1,b^2=1,
    b a b^(-1)=a^(2^n-1) chevron.r.
  $
  Then $D(ZZ G)=T(G)="group of order" 2$.
] <th:semidihedral-swan-subgroup-order-two>
#idx("Semidihedral group", target: [@th:semidihedral-swan-subgroup-order-two])
#proof[
  As in §@ss:dihedral-quaternion-class-groups, one shows that $abs(D(ZZ G))<=2$.
  However, the quaternion group of order $8$ is a subgroup of $op("SD")_n$. Thus
  $T(G) != 1$ by @th:swan-subgroup-restriction-surjection and
  @th:quaternion-swan-subgroup-order-two. (For details, see Taylor
  @bib:Taylor1984.)
]

Turning to metacyclic groups, we use the results of §@ss:metacyclic-class-groups
to prove the following theorem due to Ullom @bib:Ullom1976: #theorem[
  Consider the metacyclic group $G$ of order $p q$, given by
  #source(366)
  $ G=chevron.l x,y:x^p=1,y^q=1,y x y^(-1)=x^k chevron.r, $
  where $p$ is an odd prime, $q$ is any divisor of $p-1$, and $k$ is a primitive
  $q$-th root of $1(mod p)$. Then $T(G)$ is cyclic of order $q'=q slash (q,2)$.
] <th:metacyclic-swan-subgroup-order>
#idx("Metacyclic group", target: [@th:metacyclic-swan-subgroup-order])
#proof[
  Let $H=chevron.l y:y^q=1 chevron.r$ and $R=ZZ[omega]$, where $omega$ is a
  primitive $p$-th root of $1$ over $QQ$. As in Step 1 of the proof of Theorem
  @th:galovich-reiner-ullom-metacyclic-class-groups, where we calculated
  $D(ZZ G)$, there is a fiber product
  #metacyclic-fiber-product
  where $overline(ZZ)=ZZ slash p ZZ$. This gives rise to an exact sequence
  $
    (R compose H)^dot arrow.r^h (overline(ZZ) H)^dot
    arrow.r^delta D(ZZ G) arrow.r^f D(ZZ H),
  $
  using the fact that $D(R compose H)=0$ by
  @cor:hereditary-order-class-group-maximal-order, since $R compose H$ is
  hereditary. Since $f(T(G)) subset.eq T(H)$ by
  @prop:swan-subgroup-quotient-surjection, and $T(H)=0$ by
  @prop:swan-subgroup-elementary-properties, we conclude that
  $T(G) subset.eq ker f$. We shall show below that $delta$ maps $op("cok") h$
  into $T(G)$. It will then follow that $T(G) tilde.equiv op("cok") h$. Now Step
  3 of the proof of @th:galovich-reiner-ullom-metacyclic-class-groups shows that
  there is an isomorphism
  $
    theta:op("cok") h tilde.equiv
    overline(ZZ)^dot slash {z^(q'):z in overline(ZZ)^dot},
  $
  given by the determinant map. For each $r in ZZ$ prime to $p$, we shall find
  an element $xi in (overline(ZZ) H)^dot$ representing
  $theta^(-1)(overline(r)) in op("cok") h$, and such that $delta(xi) in T(G)$.
  Once this is done, we deduce that
  $T(G) tilde.equiv op("cok") h tilde.equiv "cyclic group of order" q'$, as
  desired.

  Given $r in ZZ$ prime to $p$, we may assume that $r equiv 1(mod q)$. Writing
  $r-1=q m$, we choose
  $ xi=1+m sigma_H in overline(ZZ) H. $
  Since $overline(ZZ)$ contains the $q$-th roots of $1$, it follows that
  $
    overline(ZZ) H tilde.equiv overline(ZZ) plus.o dots plus.o overline(ZZ)
    quad (q "copies"),
  $
  and that
  $ xi=(1+m q,1,dots,1)=(r,1,dots,1). $
  Thus $xi in (overline(ZZ) H)^dot$, and $theta(xi)=r$.

  We now show that $delta(xi)=-[r,sigma] in T(G)$. As in @eq:swan-central-unit,
  let $u=1-e+r e=1+m sigma slash p$, where $e=sigma slash p q$. Then
  $u arrow.r 1+m sigma_H in overline(ZZ) H$, and $u arrow.r 1$ in $R compose H$,
  so after identifying $QQ G$ with $QQ H plus.o QQ(R compose H)$, we may write
  $u=(xi,1)$. Note that $u$ is a
  #source(367)
  unit in the completions of $ZZ H plus.o R compose H$ at both $p$ and $q$. By
  Exercise @exc:fiber-product-boundary-idele, we have
  $
    delta(xi)=[ZZ G gamma], quad "where" gamma=(gamma_P),
    quad "with" gamma_P=cases(
      1 "," & quad P != p,
      (xi^(-1),1) "," & quad P=p,
    )
  $
  $P$ denoting a variable rational prime. On the other hand,
  $chevron.l r,sigma chevron.r tilde.equiv
  chevron.l u,sigma chevron.r=ZZ G beta$, where $beta=(beta_P)$ and
  $
    beta_P=cases(
      1 "," & quad P divides.not p q,
      u "," & quad P=p "or" P divides q.
    )
  $
  Then $beta_P^(-1)=gamma_P$ if $P divides.not q$, while
  $beta_P^(-1) gamma_P^(-1)=u^(-1) in (ZZ_P G)^dot$ if $P divides q$. Thus
  $ZZ G beta^(-1)=ZZ G gamma$, so $delta(xi)=-[r,sigma] in T(G)$ as claimed, and
  the proof is finished.
]

As is evident from the results proved so far in this subsection, there seems to
be a close connection between the Artin exponent $A(G)$ and the Swan subgroup
$T(G)$, especially when $G$ is a $p$-group. Ullom conjectured that in fact if
$G$ is a noncyclic $p$-group, with $p$ odd, then $T(G)$ is a cyclic group of
order equal to $A(G)$. In §@sec:p-adic-logarithms-taylor we shall give M.
Taylor's proof of this conjecture, as well as the corresponding result for
$p=2$.

For results on $T(G)$ with $G$ the symmetric or alternating group, see
Endo–Miyata @bib:Endo1976.

=== Rings of Integers in Tame Extensions <ss:normal-integral-bases>

Let $K subset.eq L$ be algebraic number fields, with rings of integers
$R subset.eq S$, and suppose that $L slash K$ is a Galois extension with Galois
group $G$. We view $L$ as $K G$-module, and $S$ as $R G$-module, as in Example
@exm:integers-tamely-ramified-extensions. As shown there, if $L slash K$ is
tamely ramified then $S$ is projective as $R G$-module, and determines a class
$[S] in op("Cl") R G$. Via the restriction homomorphism
$op("Cl") R G -> op("Cl") ZZ G$, we may consider $[S]$ as element of
$op("Cl") ZZ G$. In this subsection, we give the readily accessible proof that
$[S]$ is self-dual in $op("Cl") ZZ G$. The result is due to Taylor
@bib:Taylor1978c in a special case, and to Chase @bib:Chase1984 for the general
case. The proof is a nice application of Swan modules
$chevron.l r,sigma chevron.r$, and we follow the treatment in Taylor
@bib:Taylor1984.

Let $caron(S)$ be the contragredient of the $R G$-module $S$ (see
§@i:ss:contragredient-modules), so
$ caron(S)=Hom_(R G) lr((S,R G)) tilde.equiv Hom_R lr((S,R)). $
Each element of $Hom_K lr((L,K))$ is given by
$x in L arrow.r T_(L slash K)(a x) in K$, for some $a in L$, where
$T_(L slash K)$ is the trace map. It follows that we may identify $caron(S)$
with the _inverse different_ (see §@i:ss:dedekind-ideal-theory)
$ frak(D)^(-1)(S slash R)={a in L:T_(L slash K)(a S) subset.eq R}. $
Assuming hereafter that $L slash K$ is tamely ramified, both $S$ and
$frak(D)^(-1)(S slash R) tilde.equiv caron(S)$ are
#source(368)
$R G$-projective, and so (using the restriction map from $op("Cl") R G$ to
$op("Cl") ZZ G$) they determine elements of $op("Cl") ZZ G$. The main result is:
#theorem(title: [Taylor, Chase])[
  For $L slash K$ tamely ramified,
  $ [S]=[caron(S)]=[frak(D)^(-1)(S slash R)] quad "in" op("Cl") ZZ G. $
] <th:tame-integers-self-dual-class>
#idx("Chase's Theorem", target: [@th:tame-integers-self-dual-class])
#idx("Taylor's Theorem", target: [@th:tame-integers-self-dual-class])
#idx("Tamely ramified extension", target: [@th:tame-integers-self-dual-class])
To begin the proof, consider the torsion $R G$-module
$ T=(frak(D)^(-1)(S slash R)) / S, $
of homological dimension $1$ over $R G$. Identifying $op("Cl") R G$ with the
kernel of the homomorphism $K_0 lr((R G)) -> K_0 lr((K G))$ (see
@rem:locally-free-class-group-properties(iv)), we have a surjection
$K_0 lr((cal(T))) -> op("Cl") R G$, where $cal(T)$ is the category of all
$R$-torsion f.g. $R G$-modules of finite homological dimension. Then the image
of $T$ in $op("Cl") R G$ is $[frak(D)^(-1)(S slash R)]-[S]$, and we must show
this equals zero in $op("Cl") ZZ G$.

Let $P$ range over the maximal ideals of $R$. Then $T=plus.o T_P$, a finite
direct sum of $P$-adic completions, and
$ T_P=(frak(D)^(-1)(S_P slash R_P)) / S_P. $
It suffices to show that each $T_P$ has zero image in $op("Cl") ZZ G$. Keep $P$
fixed, and let us use the notation in the discussion following
@prop:crossed-product-tame-norm-quotient-surjection. Thus
$
  P S=(P_1 dots P_g)^e, quad "and" p divides.not e
  quad ("since" L slash K "is tame"),
$
where $p="characteristic of" R slash P$. By Exercise
@i:exc:different-ramification-bound, we have
$ frak(D)(S_P slash R_P)=(P_1 dots P_g)^(e-1), $
so now
$
  T_P=(P_1 dots P_g)^(-(e-1)) S_P slash S_P
  tilde.equiv product_(i=1)^g P_i^(-(e-1)) S_i slash S_i,
$
where $S_i$ is the $P_i$-adic completion of $S$. Let $D$ be the decomposition
group of $P_1$, so
$D={sigma in G:sigma P_1=P_1} tilde.equiv op("Gal")(L_1 slash K_P)$, where $L_1$
is the $P_1$-adic completion of $L$. Since $G$ acts transitively on the ${P_i}$,
it is easily seen that
$ T_P tilde.equiv R_P G times.o_(R_P D) (P_1^(-(e-1)) S_1 slash S_1). $
It thus suffices to prove that $P_1^(-(e-1)) S_1 slash S_1$ has zero image in
$op("Cl") ZZ D$.

Replacing $G$ by $D$ and then changing notation, we assume hereafter that $g=1$
and $P S=P_1^e$. Let $T_1=P_1^(-(e-1)) slash S$; we must show that in the
composite
#source(369)
map $K_0 lr((cal(T))) -> op("Cl") R G -> op("Cl") ZZ G$, the image of $T_1$ in
$op("Cl") ZZ G$ is zero. As in the discussion on pages 295, 296, let
$ G_0={sigma in G:sigma(x) equiv x(mod P_1) "for all" x in S} $
be the inertia group of $P_1$ in the extension $L slash K$. Let $L_0$ be the
subfield of $L$ fixed by $G_0$; then $L_0 slash K$ is unramified, while
$L slash L_0$ is tamely ramified with ramification index $e=abs(G_0)$.
Furthermore, $G_0$ is a cyclic group, and
$S slash P_1 tilde.equiv S_0 slash P S_0$. Therefore
$
  S / (P S+S_0) tilde.equiv (P_1+S_0) / (P S+S_0)
  tilde.equiv P_1 / (P S) tilde.equiv (P_1^(-(e-1))) / S = T_1,
$
where these are $R G$-isomorphisms. In computing $S slash (P S+S_0)$ we may
first localize at $P$, and then assume that $S_P tilde.equiv R_P G$ since
$L slash K$ is tamely ramified at $P$. We thus obtain
$
  T_1 tilde.equiv (R G) / (P dot R G+R G sigma_0),
  quad "where" sigma_0=sum_(x in G_0) x,
$
since $R G sigma_0$ is the $G_0$-trivial submodule of $R G$. It follows that
$
  T_1 tilde.equiv R G times.o_(R G_0) W, quad "where"
  W=R G_0 slash (P dot R G_0+R sigma_0)
  tilde.equiv overline(R) G_0 slash overline(R) sigma_0,
$
and where $overline(R)=R slash P$. Since
$overline(R) tilde.equiv overline(ZZ)^((f))$, where $overline(ZZ)=ZZ slash p ZZ$
and $f=dim_(overline(ZZ)) overline(R)$, we conclude that
$
  W tilde.equiv {ZZ G_0 slash chevron.l p,sigma_0 chevron.r}^((f))
  quad "as" ZZ G_0 "-modules".
$
Here, $chevron.l p,sigma_0 chevron.r$ is a Swan submodule of $ZZ G_0$, noting
that $(p,abs(G_0))=1$. But $chevron.l p,sigma_0 chevron.r$ is $ZZ G_0$-free
since $G_0$ is cyclic, so the image of $W$ in $op("Cl") ZZ G_0$ is zero, and
therefore $T_1$ has zero image in $op("Cl") ZZ G$. This completes the proof.

For generalizations of the above theorem to the case where $L slash K$ is an
arbitrary Galois extension, not necessarily tame, see Cassou-Noguès and Queyrut
@bib:CassouNogues1982, and Desrochers @bib:Desrochers1984.

=== Generalized Swan Subgroups <ss:generalized-swan-subgroups>

#idx(
  "Swan subgroup of the class group",
  target: [@ss:generalized-swan-subgroups],
)

We describe here some results of Oliver @bib:Oliver1978, showing that for a
finite group $G$, the kernel group $D(ZZ G)$ can be generated by certain
“generalized” Swan subgroups. These were first defined by Matchett
@bib:Matchett1976 as follows: let $H ⊴ G$ and set $h=abs(H)$, and
$ sigma_H=sum_(x in H) x, quad e=h^(-1) sigma_H. $
#source(370)
Starting with the fiber product
#normal-subgroup-fiber-product
where $overline(ZZ)=ZZ slash h ZZ$, we apply the induction map
$ZZ G times.o_(ZZ H) dot$ to obtain a new fiber product
#induced-normal-subgroup-fiber-product
This gives rise to the exact Mayer–Vietoris sequence
$
  K_1 lr((overline(ZZ)(G slash H))) arrow.r^partial D(ZZ G)
  -> D(ZZ G slash ZZ G sigma_H) plus.o D(ZZ(G slash H)) -> 0,
$
and we define
$
  T_H lr((G))="image of" partial "in" D(ZZ G)
  ="generalized Swan subgroup".
$
We now state without proof some functorial properties of $T_H lr((G))$, proved
by Matchett @bib:Matchett1976, which generalize
@prop:swan-subgroup-quotient-surjection and
@th:swan-subgroup-restriction-surjection:
#enum(
  numbering: "(1)",
  [Let $G -> overline(G)$ be a surjection of groups, and let $N ⊴ G$ map onto
    $overline(N) ⊴ overline(G)$. Then there is a surjection
    $T_N lr((G)) -> T_(overline(N)) lr((overline(G)))$.],
  [Let $N ⊴ G$, and suppose that $G=H N$ for some subgroup $H$ of $G$. Then the
    restriction map $op("res")_H^G$ carries $T_N lr((G))$ onto
    $T_(N inter H) lr((H))$.],
)
Oliver extended the definition of $T_H lr((G))$ to the case where $H$ is an
arbitrary subgroup of $G$, not necessarily normal. Let $N=N_G lr((H))$, so by
the above $T_H lr((N))$ is a well defined subgroup of $D(ZZ N)$. Extending the
previous definition, we set
$ T_H lr((G))=op("ind")_N^G T_H lr((N)), $
so $T_H lr((G))$ is the image of the composite map
$
  K_1 lr((overline(ZZ)(N slash H))) -> D(ZZ N) arrow.r^(op("ind")_N^G) D(ZZ G).
$
Then we have#footnote[Wilson's Theorem
  @th:wilson-crossed-product-order-trivial-kernel plays a key role in the proof
  of @th:oliver-generalized-swan-generation.] <fn:wilson-oliver-generation>:
#theorem(name: "Oliver's Theorem")[
  For any finite group $G$, we have
  $ D(ZZ G)=sum_(H subset.eq G) T_H lr((G)). $
  #source(371)
  In fact, it suffices to let $H$ range over all subgroups of $G$ of prime power
  order.] <th:oliver-generalized-swan-generation>
#idx("D(Λ)", target: [@th:oliver-generalized-swan-generation])
#idx("Oliver's Theorem", target: [@th:oliver-generalized-swan-generation])
Oliver also gave an example showing that the analogous result fails, when $ZZ$
is replaced by a ring of algebraic integers. For details, and for the proof of
the above theorem, see Oliver @bib:Oliver1978.

#exercises-heading

#exercise[
  Consider a fiber product of rings
  #exercise-fiber-product
  where $Lambda$, $Lambda'$, and $Lambda''$ are $ZZ$-orders, and
  $overline(Lambda)$ is $ZZ$-torsion, and $f$ is surjective. Given
  $a in overline(Lambda)^dot$, define
  $
    M={(x,y) in Lambda' plus.o Lambda'':overline(y)=overline(x) a
      "in" overline(Lambda)}.
  $
  Show that $M=Lambda alpha$, where $alpha=(alpha_p)$ is the idele whose
  components in $Lambda'_p plus.o Lambda''_p$ are given by
  $
    alpha_p=cases(
      (1,1) & quad "if" overline(Lambda)_p=0,
      (u_p^(-1),1) & quad "if" overline(Lambda)_p != 0,
    )
  $
  where in the second case, $u_p$ is a unit of $Lambda'_p$ such that $f(u_p)=a$
  in $overline(Lambda)_p$. Note that in the Mayer–Vietoris sequence
  $
    overline(Lambda)^dot arrow.r^delta D(Lambda)
    -> D(Lambda') plus.o D(Lambda''),
  $
  we have for $a in overline(Lambda)^dot$,
  $ delta(a)=[M]=[Lambda alpha] in D(Lambda). $
] <exc:fiber-product-boundary-idele>

#exercise[
  Let $r!=0$ and $(r,n)=1$, where $abs(G)=n$. Prove that
  $ chevron.l r,sigma chevron.r plus.o ZZ tilde.equiv ZZ G plus.o ZZ. $
] <exc:swan-module-stabilization>
#hint([@exc:swan-module-stabilization])[
  There are exact sequences
  $
    0 -> ZZ G arrow.r^r chevron.l r,sigma chevron.r -> ZZ slash r ZZ -> 0,
    quad 0 -> ZZ arrow.r^r ZZ -> ZZ slash r ZZ -> 0.
  $
  Now use Roiter's Lemma @i:prop:genus-schanuel.
]

#exercise[
  Show that $T(G)=0$ for a dihedral group $G$.
] <exc:dihedral-swan-subgroup-trivial>
#hint([@exc:dihedral-swan-subgroup-trivial], caption: [Hint (Oliver):])[
  Let $G=chevron.l a,b:a^n=b^2=1,b a b^(-1)=a^(-1) chevron.r$, and let $2k+1$ be
  relatively prime to $n$. Define
  $ u_k=1+a+dots+a^k+b+a b+dots+a^(k-1)b in ZZ G slash (sigma). $
  #source(372)
  Then $u_k$ depends only on the class of $k(mod n)$, and under the map
  $ZZ G slash (sigma) -> ZZ slash 2n ZZ$, the image of $u_k$ is $2k+1$. It
  suffices to show that $u_k$ is a unit in $ZZ G slash (sigma)$. But
  $ (1+a^(2k)b+a^(2k+1))u_k=u_(k+(2k+1)), $
  $ (1+a^(2k)b+a^(2k+1)+a^(4k+1)b+a^(4k+2))u_k=u_(k+2(2k+1)), $
  and so on, so $u_k$ is a unit. (Also see @th:metacyclic-swan-subgroup-order.)
]
