#import "header.typ": get_header
#let template(
  body, 
  env_counter: none, 
  title: none,
  authors: none,
) = [
  #set text(lang: "fr")
  #set heading(numbering: "1.")
  #set list(marker: "-")
  #set page(
    margin: (
      top: 3cm, 
      bottom: 3cm, 
      left: 2.5cm, 
      right: 2.5cm
    ), 
    header: get_header,
    footer: [
    #line(start: (-1em, 0em), length: 100% + 2em, stroke: .5pt)
      #align(center)[
        #counter(page).display(
          "1/1",
          both: true,
        )
      ]
      
      
    ], 
  )
  #set par(
    leading: 0.55em, 
    first-line-indent: 1.8em, 
    justify: true
  )
  #set text(font: "New Computer Modern", size: 14pt)
  // #show raw: set text(font: "New Computer Modern Mono")
  #show par: set block(spacing: 0.55em)
  #show heading: set block(above: 1.4em, below: 1em)

  #show heading.where(level:1): it => {
    if env_counter != none {env_counter.update(0)}
    it
  }
  #[
    #set page(
      margin: (top: 15em), 
      header: [], 
      footer: []
    )
    #set align(center)
    #text(size: 20pt)[#title] 
    #v(15pt)
    #text(size: 14pt)[
      #for author in authors [
        #author\
      ]
       
    ] 
    #v(15pt)
    #text(size: 14pt)[
      #datetime.today().display(
        "[day]/[month]/[year]"
      )
    ]
  ]
  
  #pagebreak()
  
  
  #show: par
  #set math.cancel(
    angle: 45deg, length: 80%
  )

  #import "@preview/quick-maths:0.1.0": shorthands
  #show: shorthands.with(($|-$, $tack.r$))

  #outline()
  #pagebreak()

  #body
  
]

