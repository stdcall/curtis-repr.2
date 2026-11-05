{
 import "/content/main-defs.typ": metadata-value
 (placements:query(metadata).filter(m=>type(m.value)==dictionary and m.value.at("kind",default:none)=="footnote-placement").map(m=>m.value),
 notes:query(footnote.entry).map(e=>(marker:e.note.location().position(),entry:e.location().position())),
 records:query(metadata).filter(m=>type(m.value)==dictionary and m.value.at("kind",default:none)in("numbered","unnumbered")).map(m=>(value:m.value,position:m.location().position())),
 refs:query(metadata).filter(m=>type(m.value)==dictionary and m.value.at("kind",default:none)in("cross-reference","hint-link")).map(m=>(value:metadata-value(m),position:m.location().position())),
 )}
