# Syntaxe (abstraite)
```
Fragment de base
e ::= x                         (var "x"    )
    | e₁ e₂                     (app e₁ e₂  )
    | fun (x: t) -> e           (fun x t e  )
    | true
    | false 
    | if e₁ then e₂ else e₃  


On rajoute ensuite
    | let x = e₁ in e₂  
    ~ (λ x . e₂) e₁       

    | z ∈ ℤ                     (int z      ) 
    | e₁ - e₂                   (sub e₁ e₂  )
    | (e₁, e₂)                  (pair e₁ e₂ )
    | fst(e₁)                   (fst e₁     )
    | snd(e₁)                   (snd e₁     )        
```

# Sémantique
Aucun ajout pour l'instant

## Valeurs
- `true`
- `false`
- `fun (x: t) -> e`

## Évaluation
Pour tout ce qui n'est pas une variable
```
            v₂ ∈ Vals
-------------------------------------
(fun (x: t) -> e₁) v₂ --> e₁[x <- v₂]

        e₁ --> e₁'
------------------------
    e₁ e₂ --> e₁' e₂


        v₁ ∈ Vals
        e₂ --> e₂'
------------------------
    v₁ e₂ --> v₁ e₂'


------------------------------
if true then e₁ else e₂ -> e₁

------------------------------
if false then e₁ else e₂ -> e₂

                    e₁ --> e₁'  
-----------------------------------------------
if e₁ then e₂ else e₃ -> if e₁' then e₂ else e₃

```


# Typage

```
type ::= Bool 
       | type -> type

 

 Γ x = τ 
---------
Γ ⊢ x : τ


       x : τ₁, Γ ⊢ e : τ₂
-------------------------------
Γ ⊢ fun (x: τ₁) -> e : τ₁ -> t₂ 


Γ ⊢ e₁ : τ₁ -> τ₂   Γ ⊢ e₂ : τ₁    
-------------------------------
        Γ ⊢ e₁ e₂ : t₂ 


---------------
Γ ⊢ true : Bool

----------------
Γ ⊢ false : Bool


Γ |- e₁ ∈ Bool    Γ |- e₁ ∈ τ    Γ |- e₃ ∈ τ
---------------------------------------------
                 Γ ⊢  : τ 

```