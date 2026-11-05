#set document(
  title: "Methods of Representation Theory, Volume II",
  author: ("Charles W. Curtis", "Irving Reiner"),
  date: none,
)
#import "book-style.typ": book-style
#import "frontmatter/cover.typ": cover
#import "frontmatter/frontmatter-style.typ": blank-leaf, preliminary-break
#import "main-defs.typ": source
#import "numbering.typ": continue-sections, section-counter
#cover()
#show: book-style
#set page(numbering: "i")
#counter(page).update(3)
#page(header: none, footer: none)[#include "frontmatter/title.typ"]
#page(header: none, footer: none)[#include "frontmatter/publication.typ"]
#page(header: none, footer: none)[#include "frontmatter/dedication.typ"]
#blank-leaf()
#include "frontmatter/preface.typ"
#preliminary-break()
#heading(level: 1, numbering: none, outlined: false)[Contents]
#source(9)
#outline(title: none, depth: 3)
#preliminary-break()
#page(header: none, footer: none)[#include "frontmatter/half-title.typ"]
#blank-leaf()
#set page(numbering: "1")
#counter(page).update(1)
#counter(heading).update(4)
#section-counter.update(37)
#include "05-00-introduction.typ"
#continue-sections()
#include "05-38-grothendieck.typ"
#include "05-38a-further-results.typ"
#include "05-38b-grothendieck-projective.typ"
#include "05-38c-regular-rings.typ"
#include "05-38d-localization-sequences.typ"
#include "05-39-swan-induction.typ"
#include "05-40-whitehead-groups.typ"
#include "05-41-basic-elements.typ"
#include "05-42-mayer-vietoris.typ"
#include "05-43-polynomial-k-theory.typ"
#include "05-44-relative-k-theory.typ"
#include "05-45-sk1-orders.typ"
#include "05-46-whitehead-integral-group-rings.typ"
#include "05-47-milnor-k2.typ"
#include "05-48-sk1-integral-group-rings.typ"
#include "06-00-introduction.typ"
#continue-sections()
#include "06-49-locally-free-class-groups.typ"
#include "06-50-class-groups-integral-group-rings.typ"
#include "06-51-cancellation-theorems.typ"
#include "06-52-frohlich-hom-description.typ"
#include "06-53-swan-subgroup-class-group.typ"
#include "06-54-p-adic-logarithms-taylor.typ"
#include "06-55-picard-groups.typ"
#include "07-00-introduction.typ"
#continue-sections()
#include "07-56-introduction-block-theory.typ"
#include "07-57-defect-groups-blocks.typ"
#include "07-58-brauer-correspondence.typ"
#include "07-59-blocks-character-theory.typ"
#include "07-60-p-sections-blocks.typ"
#include "07-61-refinements-brauer-correspondence.typ"
#include "07-62-cyclic-defect-blocks.typ"
#include "07-63-applications-group-theory.typ"
#include "08-00-introduction.typ"
#continue-sections()
#include "08-64-root-systems-reflection-groups.typ"
#include "08-65-bn-pairs.typ"
#include "08-66-homology-representations.typ"
#include "08-67-hecke-algebras-bn-pairs.typ"
#include "08-68-generic-algebras.typ"
#include "08-69-split-bn-pairs.typ"
#include "08-70-cuspidal-characters.typ"
#include "08-71-character-duality.typ"
#include "08-72-modular-lie-type.typ"
#include "09-00-introduction.typ"
#continue-sections()
#include "09-73-real-forms.typ"
#include "09-74-schur-index.typ"
#include "09-75-symmetric-groups.typ"
#include "09-76-artin-induction.typ"
#include "10-00-introduction.typ"
#continue-sections()
#include "10-77-graph-representations-gabriel.typ"
#include "10-78-auslander-reiten-sequences.typ"
#include "10-79-finite-representation-type.typ"
#include "11-00-introduction.typ"
#continue-sections()
#include "11-80-permutation-representations-burnside-rings.typ"
#include "11-81-representation-rings.typ"
#include "80-bibliography.typ"
#include "89-notation-index.typ"
#include "90-index.typ"
