#import "../main-defs.typ": *
#import "frontmatter-style.typ": preface-addendum

#heading(level: 1, numbering: none)[Preface] <ch:preface>

#source(5)
In this volume, the reader can follow each of the main directions in the current
work on the representation theory of finite groups. The subject owes much of its
present vitality to the achievements of R. Brauer, J. A. Green, G. Lusztig, and
R. G. Swan. Their work not only has set the foundations, but also has
established close ties between representation theory and the theory of finite
groups, algebraic number theory, and algebraic geometry and topology. Our main
objective has been to present an accessible, self-contained, and detailed
introduction to their contributions, so that the reader can find in one place
all that is needed for a thorough understanding of the main results, along with
concrete information on how the ideas are applied.

As a supplement to the table of contents, we include here some remarks about the
chapters in this volume and the earlier parts of the book they depend on. It has
been our intention that the chapters can be read independently of one another.

Chapter @ch:algebraic-k-theory is a comprehensive introduction to
low-dimensional algebraic $K$-theory. We present the basic properties of the
groups $K_0$, $K_1$, and $K_2$, together with information on methods of
computing them for integral group rings and orders. Prerequisites include
homological algebra, from the @i:ch:introduction[Introduction] to Volume I, and
other parts of Volume I, which are reviewed as they occur in the discussion.

Chapter @ch:class-groups, on class groups, is a culmination of integral
representation theory. It contains a representative collection of explicit
calculations of locally free class groups of integral group rings, including a
discussion of the algebraic number theory needed to carry them out. This
requires a good understanding of parts of Chapters
@i:ch:integral-representations and @i:ch:local-global-integral-representations,
as well as a portion of the @i:ch:introduction[Introduction] to Volume I.
Chapters @ch:algebraic-k-theory and @ch:class-groups also contain several
references to the book _Maximal Orders_ (Reiner @bib:Reiner1975), cited as
@bib:Reiner1975[MO] in the text.

Chapter @ch:block-theory is devoted to Brauer’s theory of blocks. It contains
the basic results pertaining to blocks of modules over the group algebras $K G$,
$R G$, and $k G$ for a $p$-modular system $(K, R, k)$. A main theme is the new
approach to the foundations of block theory provided by Green’s work on
indecomposable modules and $G$-algebras. For this chapter, a thorough
understanding of Chapters @i:ch:group-representations-character-theory and
@i:ch:modular-representations is essential. We note incidentally that the
character theory of finite groups with self-centralizing, cyclic Sylow
$p$-subgroups that are $T I$-sets, from §§
@i:sec:special-classes-exceptional-characters and @i:sec:green-correspondence,
is reconsidered in the context of block theory in §§ @sec:p-sections-blocks and
@sec:cyclic-defect-blocks. The chapter also contains several comparisons with
the earlier account of block theory, Curtis–Reiner @bib:CurtisReiner1962, cited
throughout as @bib:CurtisReiner1962[CR].

Finite groups of Lie type occupy a special place in finite group theory, as the
#source(6)
classification of finite simple groups has shown. The contributions of Lusztig
to the solution of many challenging problems concerning their representations
have been responsible for a surge of interest in all aspects of the character
theory of these groups. His work is based on the theory of reductive algebraic
groups over finite fields, and their actions on certain algebraic varieties. Our
purpose in Chapter @ch:finite-groups-lie-type has been to give a self-contained
introduction, for persons coming to the subject from other parts of
representation theory, to topics that can be understood without extensive
background on algebraic groups and $l$-adic cohomology, and that nevertheless
are important in Lusztig’s theory. Prerequisites for this chapter are Chapter
@i:ch:group-representations-character-theory, especially § @i:ss:hecke-algebras
on Hecke algebras, and Chapter @i:ch:modular-representations, as preparation for
§ @sec:modular-lie-type.

Chapter @ch:rationality-questions, on rationality questions, begins with a
section on the Frobenius–Schur classification of irreducible complex-valued
characters, from the point of view of realizability of the representations over
$RR$, which belongs in every first course in character theory. The prerequisite
for the entire chapter is Chapter @i:ch:group-representations-character-theory
and the theory of splitting fields from the @i:ch:introduction[Introduction] to
Volume I.

Chapter @ch:indecomposable-modules takes up some new directions in the
classification of indecomposable representations, including Gabriel’s theorem on
representations of graphs, and an introduction to the theory of Auslander–Reiten
sequences. As an application of the latter topic, we present Yamagata’s proof of
Roiter’s theorem on the Brauer–Thrall conjecture. An account of some earlier
work on the classification of indecomposable modules over artinian rings was
given in @bib:CurtisReiner1962[CR], Chapters 8 and 9.

The last chapter is devoted to Burnside rings and representation rings, which
give a new perspective to the induction theorems discussed in Chapters
@i:ch:group-representations-character-theory and @i:ch:modular-representations,
and to the problem of classifying indecomposable modules over non-semisimple
group algebras.

Although it has resulted in a longer book, we have not hesitated to review basic
concepts and proofs each time they are applied, so that the book can be picked
up and read locally, without too great penalties for skipping from one part to
another.

This volume is, to a great extent, a personal odyssey, containing much of what
we know ourselves about the research problems we have worked on during the last
twenty years. Chapters @ch:algebraic-k-theory–@ch:finite-groups-lie-type have
each been a basis of graduate courses and seminars we have given.

While the progress in representation theory made since the publication of
@bib:CurtisReiner1962[CR] encouraged us to undertake this project, its size and
scope have been a surprise to us. Perhaps it is not out of place to express the
hope that this book will be a useful guide, as @bib:CurtisReiner1962[CR] was in
its time, during a period of continuing activity in representation theory and
its applications.

It remains to thank those persons and institutions whose help has been essential
for the completion of this volume: Dan Grayson, Steve Ullom, Mike Stein, Gerald
Cliff, Dean Alvis, Jerry Janusz, and Peter Webb for their help with the
manuscript and the proof reading; the National Science Foundation for research
support; and Hilda K. Britt for her tireless efforts devoted to the preparation
of the manuscript. We also extend our thanks to the many friends,
#source(7)
colleagues, and students whom we have consulted on various points connected with
the project. Once again, we add a special note of appreciation to our wives,
Betsy and Irma, for their affection and encouragement.

Charles W. Curtis \
Irving Reiner

Eugene, Oregon \
Urbana, Illinois \
August 1986

#preface-addendum[
  #strong[Addendum to the Preface]

  #emph[Irving Reiner died in October, 1986, while the book was in production. I
    deeply regret that he did not live to see the book in print. We had
    completed together the manuscript and the preface, and sent them to the
    publisher earlier in 1986. Along with the persons mentioned in the Preface,
    I want to thank Irma Reiner for her help with the proof reading.]

  Charles W. Curtis

  #emph[Eugene, Oregon \
    May, 1987]
]
