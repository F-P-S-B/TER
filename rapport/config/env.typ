#let def_env_counter = counter("def_env")

#let default(body) = block[
  #set text(style: "normal", weight: "regular")
  \

  #body
]

#let environnement(
  body: "", 
  name: "", 
  title: "", 
  show_counter: true,
  title_style: "normal",
  title_weight: "bold",
  body_style: "normal",
  body_weight: "regular",
  plural: false,
) = block[
  #set text(style: title_style, weight: title_weight)
  #{name + if plural [s]}#{
    if show_counter [
      #def_env_counter.step()#def_env_counter.display(
        count => [
          #counter(heading.where(level:1)).display()#count#{
            if title =="" [.]
          }
        ]
      )
    ]
  }
  #set text(style: body_style, weight: body_weight)
  #if title != "" [(#title).]
  #body
]

#let thm_style(
  name: "", 
  title: "", 
  plural: false,
  show_counter: true, 
  body: "", 
) = environnement(
  body: body,
  name: name, 
  title: title,
  show_counter: show_counter, 
  title_style: "normal",
  title_weight: "bold",
  body_style: "italic",
  body_weight: "regular",
  plural: plural
)

#let thm(it, title:"", show_counter: true, plural: false) = thm_style(
  name: "Théorème",
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it, 
)

#let cor(it, title:"", show_counter: true, plural: false) = thm_style(
  name: "Corollaire",
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it, 
)

#let propriete(it, title:"", show_counter: true, plural: false) = thm_style(
  name: "Propriété",
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it, 
)

#let proposition(it, title:"", show_counter: true, plural: false) = thm_style(
  name: "Proposition",
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it, 
)

#let interlude(it, title:"", show_counter: true, plural: false) = thm_style(
  name: "Interlude",
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it, 
)


#let def_style(
  name: "", 
  title: "", 
  plural: false,
  show_counter: true, 
  body: "", 
) = environnement(
  body: body,
  name: name, 
  title: title,
  show_counter: show_counter, 
  title_style: "normal",
  title_weight: "bold",
  body_style: "normal",
  body_weight: "regular",
  plural: plural
)



#let def(
  it, 
  title:"", 
  show_counter: true, 
  plural: false
) =  def_style(
  name: "Définition", 
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it
)

#let term(
  it, 
  title:"", 
  show_counter: true, 
  plural: false
) =  def_style(
  name: "Terminologie", 
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it
)

#let notation(
  it, 
  title:"", 
  show_counter: true, 
  plural: false
) =  def_style(
  name: "Notation", 
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it
)

#let meth(
  it, 
  title:"", 
  show_counter: true, 
  plural: false
) =  def_style(
  name: "Méthodologie", 
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it
)

#let algo(
  it, 
  title:"", 
  show_counter: true, 
  plural: false
) =  def_style(
  name: "Algorithme", 
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it
)

#let exemple_style(
  name: "", 
  title: "", 
  plural: false,
  show_counter: true, 
  body: "", 
) = environnement(
  body: body,
  name: name, 
  title: title,
  show_counter: show_counter, 
  title_style: "italic",
  title_weight: "regular",
  body_style: "normal",
  body_weight: "regular",
  plural: plural
)

#let exemple(
  it, 
  title:"", 
  show_counter: true, 
  plural: false
) =  exemple_style(
  name: "Exemple", 
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it
)

#let exo(
  it, 
  title:"", 
  show_counter: true, 
  plural: false
) =  exemple_style(
  name: "Exercice", 
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it
) // TODO: voir pour numéroter à part

#let rmq(
  it, 
  title:"", 
  show_counter: true, 
  plural: false
) =  exemple_style(
  name: "Remarque", 
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it
) 

#let rapp(
  it, 
  title:"", 
  show_counter: true, 
  plural: false
) =  exemple_style(
  name: "Rappel", 
  title: title, 
  plural: plural,
  show_counter: show_counter, 
  body: it
) 

#let demo(
  it, 
) = [
  #exemple_style(
  name: "Démonstration", 
  show_counter: false, 
  body: it
)
#align(right)[$square.stroked.small$]
 ]
