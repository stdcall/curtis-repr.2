#import "main-defs.typ": *
#import "statements.typ": *

#source(735)
= Rationality Questions
<ch:rationality-questions>

Let $G$ be a finite group, and let $K$ be a field. A $K G$-module $M$ is
_realizable_ in a subfield $F$ of $K$ provided that there exists an $F G$-module
$M_0$ such that $M=K times.o_F M_0$. When this occurs, we shall call $M_0$ an
_$F$-form_ of $M$. The existence of an $F$-form means that $M$ affords an
$F$-rational matrix representation $x arrow.r bold(M)(x)$, $x in G$, with the
property that all the entries of the matrices ${bold(M)(x),x in G}$ lie in $F$.
Thus the term “rationality questions” refers to problems connected with
realizability.

There are, first of all, general principles that apply to all finite groups.
These are first discussed in §~@sec:unitary-orthogonal-symplectic-modules for
$CC G$-modules, with reference to the real field $RR$. The results in this case
are particularly elegant and explicit, and are due to Frobenius–Schur
@bib:Frobenius1906. We have given an elementary self-contained approach,
following Serre, which belongs in every course on basic character theory.

Rationality questions involving arbitrary fields are discussed in
§~@sec:schur-index, from the point of view of central simple algebras. Here the
main ideas, especially for number fields, are due to Schur. We have given a
survey of the classical results of Schur, Brauer, Witt, and others, along with
recent contributions by Benard–Schacher, Yamada, and Janusz.

A second approach to rationality questions is to investigate families of finite
groups that behave exceptionally, either well or badly. The prototypes of good
behavior are the symmetric groups, where the situation can be described quite
simply: everything is rational. Section @sec:symmetric-group-representations
contains a new approach to the representation theory of the symmetric groups due
to James, which produces a basic set of simple modules over an arbitrary field.
Strong results on the rationality properties of simple modules also hold for
other types of Weyl groups and generic Hecke algebras associated with them, but
that is another story (see Benson–Curtis @bib:Benson1972 and Lusztig
@bib:Lusztig1981).

The chapter also contains several induction theorems closely related to
questions of rationality. These include Serre's theorem on real-valued
characters in §~@ss:real-valued-character-induction, Frobenius' theorem on
characters of the symmetric groups, Solomon's generalization of the Artin
Induction Theorem in §~@ss:solomon-symmetric-group-characters, and an
introduction to the Artin exponent in §~@sec:artin-exponent.
