#let raccourcis(body) = {
  show "ssi ": "si et seulement si "
  show "cad ": "c'est-à-dire "
  body
}

#let ignoreHeading(body) = [
  #set heading(numbering: none)
  body
]