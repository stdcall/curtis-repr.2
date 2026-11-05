#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
#theorem[
 Opening no-note assertion.
 #case-list(numbering:"1.",prefix:"Case ",
 [#case[First ordinary case.]<case:first>],
 [#case[Second ordinary case.
 #case-list(numbering:"(i)", [#case[Nested ordinary item.]<case:inner>])
 Its conclusion.]<case:second>],
 )
]<th:ordinary>
#exercise[Ordinary exercise.]<exc:ordinary>
#hint[@exc:ordinary][Ordinary complete hint.]
#proof[Ordinary direct note.#footnote[CONTROLNOTE Native ordinary proof note.]
 The rest of this first paragraph concludes.]
AFTER @case:first, @case:second, @case:inner and @th:ordinary.
