#import "./config/env.typ"
#import "./config/template.typ": template
#import "./config/misc.typ": raccourcis
#import "@preview/ouset:0.1.1" : overset
#import "./config/prooftree.typ": *


#show: raccourcis
#show: template.with(
  title: [Rapport de TER:\ Formalisation d'un système de types en Coq],
  authors: ([Félix SASSUS BOURDA],),
  env_counter: env.def_env_counter,
) 

#let string = math.op("string")
#let type = math.op("type")
#let expr = math.op("expr")
#let lsexpr = math.op("lsexpr")
#let val = math.op("val")


= Présentation du résultat final


Le langage d'étude est une forme enrichie du $lambda$-calcul simplement typé.
//  avec les nom commençant par "e" des expressions quelconques, par "t" des types quelconques, et la lettre "x" une chaine de caractères quelconque et la lettre "z" un entier relatif quelconque.
== Syntaxe
=== Termes 
Un terme du langage est une expression. On a aussi une construction de liste d'expression, 
=== Valeurs
On définit inductivement les valeurs du langage:
#pagebreak()
= Annexe


#figure(
    caption: "Syntaxe du langage, avec à gauche la syntaxe concrète et à droite représentation abstraite",
    kind: "def",
    supplement: [Définition]
)[
#let constructeur(nom, ..vars) = [
#nom 
#vars.pos().map(
    e => 
    [
        $#e space$
    ]
).join()]
$
expr ::=&   && \#x                              quad && constructeur("E_Var", x)
\       & | && e_1 e_2                          quad && constructeur("E_App", e_1, e_2)
\       & | && "fun" x : t => e                 quad && constructeur("E_Fun", x, t, e)
\       & | && "true"                           quad && constructeur("E_True")
\       & | && "false"                          quad && constructeur("E_False")
\       & | && "if" e_1 "then" e_2 "else" e_3   quad && constructeur("E_If", e_1, e_2, e_3)
\       & | && "let" x = e_1 "in" e_2           quad && constructeur("E_Let", x, e_1, e_2)
\       & | && z                                quad && constructeur("E_Num", z)
\       & | && e_1 - e_2                        quad && constructeur("E_Minus", e_1, e_2)
\       & | && e_1 == e_2                       quad && constructeur("E_Eq", e_1, e_2)
\       & | && (e_1, e_2)                       quad && constructeur("E_Pair", e_1, e_2)
\       & | && "first" e                        quad && constructeur("E_First", e)
\       & | && "second" e                       quad && constructeur("E_Second", e)
\       & | && { space l space }                quad && constructeur("E_Rec", l) 
\       & | && e::x                             quad && constructeur("E_Rec_Access", e, x) 
\       & | && "fix" e                          quad && constructeur("E_Fix", e) 
\       & | && "inl" < t_1 | t_2 > e            quad && constructeur("E_In_Left", t_1, t_2, e) 
\       & | && "inr" < t_1 | t_2 > e            quad && constructeur("E_In_Right", t_1, t_2, e) 
\       & | && "match" e "with" | "inl" => e_l | "inr" => e_r           
                                                quad && constructeur("E_Match", e, e_l, e_r) 
\       & | && "unit"                           quad && constructeur("E_Unit") 
\       & | && x[e]                             quad && constructeur("E_Sum_Constr", x, e) 
\       & | && "match_sum" e "with" l : e_d "end_sum"   
                                                quad && constructeur("E_Sum_Match", e, e_d, l)  
\ \
lsexpr ::=&   && "nil"                          quad && constructeur("LSE_Nil")
\         & | && x := e_1 space ; space l       quad && constructeur("LSE_Cons", x, e_1, l) 
$ \
]


#figure(
    caption: "Valeurs du langage",
    kind: "def",
    supplement: [Définition],
)[
#let val(e) = $"val" space  #e$
#let valls(e) = $"val"_"ls" space #e$
    $
    #prooftree(
        axiom(""),
        rule(label : "(VTrue)", $val("true")$)
    ) 
    quad & quad
    #prooftree(
        axiom(""),
        rule(label : "(VFalse)", $val("false")$)
    )
    \ \ \
    #prooftree(
        axiom(""),
        rule(label : "(VNum)", $val(z)$)
    )
    quad & quad
    #prooftree(
        axiom(""),
        rule(label : "(VUnit)", $val("unit")$)
    )
    \ \ \
    #prooftree(
        axiom(""),
        rule(label : "(VFun)", $val("fun" x : t => e)$)
    )
    quad & quad
    #prooftree(
        axiom($e_1 : expr$),
        axiom($e_2 : expr$),
        rule(n : 2, label : "(VPair)", $val((e_1, space e_2))$)
    )
    \ \ \
    #prooftree(
        axiom(val(v)),
        axiom($valls("tail")$),
        rule(n : 2, label : "(VRec)", $val( { space x := v space ; space "tail" space } )$)
    )
    quad & quad
    #prooftree(
        axiom(val(v)),
        rule(label : "(VInLeft)", $val( "inl" < t_1 | t_2 > v)$)
    )
    \ \ \
    #prooftree(
        axiom(val(v)),
        rule(label : "(VInRight)", $val("inr" < t_1 | t_2 > v)$)
    )
    quad & quad
    #prooftree(
        axiom(val(v)),
        rule(label : "(VSumConstr)", $val(x[v])$)
    )
    $ \
]
// TODO: 
// - Types
// - Canonical_form
// - Closed
// - Subst
// - Step
// - Preservation
// - Progress
// - Pair_records