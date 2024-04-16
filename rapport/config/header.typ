#let get_headings(loc) = {
  let headings_before = query(
    selector(heading).before(loc), 
    loc
  )
  if headings_before == () {
    none
  } else {
    headings_before
  }
}


#let get_header = locate(loc => [
    #let headings = get_headings(loc)
    #let heading_lvl_1 = if headings!= none {
      let res = headings.filter(e => e.at("level") == 1)
      if res == () { none } else { res.last()  }
    } else {
      none
    }
    #let heading_lvl_2 = if headings != none {
      let res = headings.filter(e => e.at("level") == 2)
      if res == () { none } else { res.last() }
    } else {
      none
    }

    #if heading_lvl_1 != none and counter(heading).at(loc).first() > 0 [
      
      #counter(heading).at(loc).first().#upper(heading_lvl_1.at("body"))
    ]
    #h(1fr)
    #if heading_lvl_2 != none and (counter(heading).get().len() >= 2) [
      #counter(heading).get().at(0).#counter(heading).get().at(1).#upper(heading_lvl_2.at("body"))
    ]
    #line(start: (-1em, 0em), length: 100% + 2em, stroke: .5pt)
  ]
)



