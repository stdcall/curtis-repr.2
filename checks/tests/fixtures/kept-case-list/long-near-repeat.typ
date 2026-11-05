#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
#theorem[
 Opening assertion.
 #case-list(numbering: "(i)",
  [#case[An opening case without a note.]<case:first>],
  [#case[
   FIRSTAUTHOR argument.#footnote[AUTHORONE The first author note.]<fn:author>
   NEARREPEAT refers to the same entry.#footnote(<fn:author>)

   A separate continuation paragraph with a display
   $ a+b=c, $
   and the following continued argument has a second note.#footnote[AUTHORTWO A different native author note.]

   #for i in range(12) [Continuation #i. #lorem(38)

]
   The long continuation concludes.
   An editorial clarification.#ed-note[EDITORIALONE A distinct editorial note.]
   #case-list(numbering:"(a)",
     [#case[Nested native item.]<case:nested>],
   )
   CASEEND The original case finishes here.
  ]<case:second>],
 )
]<th:multi>
AFTER @case:first, @case:second, @case:nested and @th:multi.
#case-list([#case[Next list resets.]<case:reset>])
Reset @case:reset.
