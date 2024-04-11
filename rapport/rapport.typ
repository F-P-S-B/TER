#show raw.where(lang: "foo_lang"): it => [
    #show regex("(Inductive|Set)") : keyword => "aaaaaaaa"
    #show regex("\\(\\*.*\\*\\)") : keyword =>  text(fill: green, keyword)
    #it
]

```foo_lang
(* Ceci est un test *)
```
