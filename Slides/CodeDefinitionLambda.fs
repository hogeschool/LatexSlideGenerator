﻿module CodeDefinitionLambda

open Coroutine
open CommonLatex
open System.Collections.Generic

type Type =
  | Var of string
  | Arrow of Type * Type
  | Forall of string * Type
  | Mu of string * Type
  | Application of Type * Type
  | Boolean
  | Nat
  | Product
  | Sum
  with 
    member this.Length = 
      match this with
      | Arrow(t,u) -> t.Length + u.Length
      | Forall(x,t) -> 1 + t.Length
      | Mu(x,t) -> 1 + t.Length
      | Application(t,u) -> t.Length + u.Length
      | _ -> 1
    member t.replace (x:string) (u:Type) : Type =
      match t with
      | Var s when s = x -> u
      | Forall(v,f) when v <> x -> Forall(v, f.replace x u)
      | Application(t,f) -> 
        Application(t.replace x u,f.replace x u)
      | Arrow(t,f) -> 
        Arrow(t.replace x u,f.replace x u)
      | _ -> t
    member this.ToLambdaForallInner =
      match this with
      | Forall(a,u) ->
        sprintf @" %s%s)" (toGreekLetter a) (u.ToLambdaForallInner)
      | t -> 
        sprintf @" $\Rightarrow$%s)" (t.ToLambda)
    member this.ToLambdaInner =
      match this with
      | Arrow(t,u) ->
        sprintf @"%s$\rightarrow$%s" (t.ToLambda) (u.ToLambdaInner)
      | t -> 
        t.ToLambda
      
    member this.ToLambdaMuInner = this.ToLambda
    member this.ToLambda =
      match this with
      | Var s -> toGreekLetter s
      | Arrow(t,u) ->
        sprintf @"(%s$\rightarrow$%s)" (t.ToLambda) (u.ToLambdaInner)
      | Forall(a,u) ->
        sprintf @"($\forall$%s%s" (toGreekLetter a) (u.ToLambdaForallInner)
      | Mu(a,u) ->
        sprintf @"($\mu$%s$\Rightarrow$%s)" (toGreekLetter a) (u.ToLambdaMuInner)
      | Application(Application(Product,t),u) ->
        sprintf @"(%s$\times$%s)" (t.ToLambda) (u.ToLambda)
      | Application(Application(Sum,t),u) ->
        sprintf @"(%s+%s)" (t.ToLambda) (u.ToLambda)
      | Application(t,u) ->
        sprintf @"(%s %s)" (t.ToLambda) (u.ToLambda)
      | Boolean ->
        "Boolean"
      | Nat ->
        "Nat"
      | Product ->
        @"$\times$"
      | Sum ->
        @"+"

type Term =
  | Type of Type
  | Var of string
  | Application of Term * Term
  | Lambda of (string * Type) * Term
  | TypeApplication of Term * Type
  | TypeLambda of string * Term
  | Let of (string * Type) * Term * Term
  | True
  | False
  | Not
  | And
  | Or
  | Plus
  | Minus
  | Mult
  | IsZero
  | If
  | Fix
  | Highlighted of Term * highlightType:HighlightType
  | Hidden of Term
  | MakePair
  | First
  | Second
  | Inl
  | Inr
  | Match
  with
    member t.replace (x:string) (u:Term) : Term =
      match t with
      | Var s when s = x -> u
      | Lambda((v,t_v),f) when v <> x -> Lambda((v,t_v), f.replace x u)
      | Application(t,f) -> 
        Application(t.replace x u,f.replace x u)
      | Let((v,t_v),t,rest) when v <> x -> Let((v,t_v),t.replace x u,rest.replace x u)
      | TypeApplication(t,a) -> 
        t.replace x u
      | TypeLambda(a,t) -> 
        t.replace x u
      | _ -> t
    member t.typeReplace (x:string) (u:Term) : Term =
      match t with
      | Var s when s = x -> u
      | Lambda((v,t_v),f) when v <> x -> Lambda((v,t_v), f.typeReplace x u)
      | Application(t,f) -> 
        Application(t.typeReplace x u,f.typeReplace x u)
      | Let((v,t_v),t,rest) when v <> x -> Let((v,t_v),t.typeReplace x u,rest.typeReplace x u)
      | TypeApplication(t,a) -> 
        TypeApplication(t.typeReplace x u,a)
      | TypeLambda(a,t) when x <> a -> 
        TypeLambda(a,t.typeReplace x u)
      | _ -> t

    member this.ToLambdaInner (printTypes:PrintTypes) =
      let (!) = printTypes.PrintVar
      match this with
      | TypeLambda(a,t) -> 
        sprintf @"$\rightarrow$%s %s" (printTypes.PrintTypeLambda a) (t.ToLambda printTypes)
      | Lambda(x,t) -> sprintf @" %s%s" !x (t.ToLambdaInner printTypes)
      | Highlighted(Lambda(x,t),Underlined) ->
        sprintf @"(*@\underline{%s}@*)%s" !x ((Highlighted(t,Underlined)).ToLambdaInner printTypes)
      | Highlighted(Lambda(x,t),Colored) ->
        sprintf @"(*@\colorbox{yellow}{%s}@*)%s" !x ((Highlighted(t,Colored)).ToLambdaInner printTypes)
      | _ -> sprintf @"$\rightarrow$%s" (this.ToLambda printTypes)
    member this.Length = 
      match this with
      | Highlighted(t,_) -> t.Length
      | Application(t,u) -> t.Length + u.Length
      | Lambda(x,t) -> 1 + t.Length
      | TypeLambda(x,t) -> 1 + t.Length
      | TypeApplication(t,u) -> t.Length + u.Length
      | Type(t) -> 1 + t.Length
      | _ -> 1

    member this.ToLambda (printTypes:PrintTypes) =
      match this with
      | Type t -> 
        printTypes.PrintType t
      | TypeApplication(t,a) ->
        printTypes.PrintTypeApplication (t.ToLambda printTypes) a
      | TypeLambda(a,t) ->
        sprintf "%s%s" (printTypes.PrintTypeLambda a) (t.ToLambda printTypes)
      | Var s -> s
      | Hidden t -> sprintf @"..."
      | Highlighted(t,Colored) -> 
        sprintf @"(*@\colorbox{yellow}{%s}@*)" (t.ToLambda printTypes)
      | Highlighted(t,Underlined) -> 
        if t.Length <= 10 then
          sprintf @"(*@\underline{%s}@*)" (t.ToLambda printTypes)
        else
          match t with
//          | Application(Application(And,t),u) -> sprintf @"(%s $\wedge$ %s)" (t.ToLambda) (u.ToLambda)
//          | Application(Application(Or,t),u) -> sprintf @"(%s $\vee$ %s)" (t.ToLambda) (u.ToLambda)
//          | Application(Application(Plus,t),u) -> sprintf @"(%s $+$ %s)" (t.ToLambda) (u.ToLambda)
//          | Application(Application(Minus,t),u) -> sprintf @"(%s $-$ %s)" (t.ToLambda) (u.ToLambda)
//          | Application(Application(Mult,t),u) -> sprintf @"(%s $\times$ %s)" (t.ToLambda) (u.ToLambda)
//          | Application(IsZero,t) -> sprintf @"(%s $=$ 0)" (t.ToLambda)
          | Application(Application(Application(If,c),t),e) -> 
            Application(Application(Application(If,Highlighted(c,Underlined)),Highlighted(t,Underlined)),Highlighted(e,Underlined)).ToLambda printTypes
          | Application(t,u) ->
            Application(Highlighted(t,Underlined),Highlighted(u,Underlined)).ToLambda printTypes
          | Lambda(x,t) -> 
            sprintf @"(*@\underline{$\lambda$%s$\rightarrow$}@*) %s" (printTypes.PrintVar x) ((Highlighted(t,Underlined)).ToLambdaInner printTypes)
          | TypeLambda(a,t) -> 
            sprintf @"(*@\underline{%s}@*) %s" (printTypes.PrintTypeLambda a) (Highlighted(t,Underlined).ToLambda printTypes)
          | t -> 
            t.ToLambda printTypes
      | Application(Application(And,t),u) -> sprintf @"(%s $\wedge$ %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Application(Application(Or,t),u) -> sprintf @"(%s $\vee$ %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Application(Application(Plus,t),u) -> sprintf @"(%s $+$ %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Application(Application(Minus,t),u) -> sprintf @"(%s $-$ %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Application(Application(Mult,t),u) -> sprintf @"(%s $\times$ %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Application(IsZero,t) -> sprintf @"(%s $=$ 0)" (t.ToLambda printTypes)
      | Application(Application(Application(If,c),t),e) -> sprintf "if %s then %s else %s" (c.ToLambda printTypes) (t.ToLambda printTypes) (e.ToLambda printTypes)
      | Application(Application(MakePair,t),u) -> sprintf @"(%s, %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Application(t,u) -> sprintf "(%s %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Lambda(x,t) -> sprintf @"($\lambda$%s%s)" (printTypes.PrintVar x) (t.ToLambdaInner printTypes)
      | Let(_bind,_expr,_in) -> sprintf "let %s = %s in %s" (printTypes.PrintVar _bind) (_expr.ToLambda printTypes) (_in.ToLambda printTypes)
      | True -> sprintf "TRUE"
      | False -> sprintf "FALSE"
      | Not -> sprintf @"$\neg$"
      | And -> sprintf @"$\wedge$"
      | Or -> sprintf @"$\vee$"
      | Plus -> sprintf "+"
      | Minus -> sprintf "-"
      | IsZero -> sprintf "0?"
      | Mult -> sprintf @"$\times$"
      | If -> sprintf "if-then-else"
      | Fix -> sprintf "fix"
      | MakePair -> sprintf "(,)"
      | First -> sprintf "$\pi_1$"
      | Second -> sprintf "$\pi_2$"
      | Match -> sprintf @"match"
      | Inl -> sprintf @"inl"
      | Inr -> sprintf @"inr"
    member this.ToString (printTypes:PrintTypes) =
      match this with
      | Type t -> 
        printTypes.PrintType t
      | TypeApplication(t,a) ->
        printTypes.PrintTypeApplication (t.ToString printTypes) a
      | TypeLambda(a,t) ->
        sprintf "%s%s" (printTypes.PrintTypeLambda a) (t.ToString printTypes)
      | Var s -> s
      | Hidden t -> sprintf @"..."
      | Highlighted(t,_) -> t.ToString printTypes
      | Application(Application(And,t),u) -> sprintf "(%s AND %s)" (t.ToString printTypes) (u.ToString printTypes)
      | Application(Application(Or,t),u) -> sprintf "(%s OR %s)" (t.ToString printTypes) (u.ToString printTypes)
      | Application(Application(Plus,t),u) -> sprintf "(%s + %s)" (t.ToString printTypes) (u.ToString printTypes)
      | Application(Application(Minus,t),u) -> sprintf @"(%s $-$ %s)" (t.ToString printTypes) (u.ToString printTypes)
      | Application(Application(Mult,t),u) -> sprintf "(%s * %s)" (t.ToString printTypes) (u.ToString printTypes)
      | Application(IsZero,t) -> sprintf @"(%s $=$ 0)" (t.ToString printTypes)
      | Application(Application(Application(If,c),t),e) -> sprintf "if %s then %s else %s" (c.ToString printTypes) (t.ToString printTypes) (e.ToString printTypes)
      | Application(Application(MakePair,t),u) -> sprintf @"(%s, %s)" (t.ToString printTypes) (u.ToString printTypes)
      | Application(t,u) -> sprintf "(%s %s)" (t.ToString printTypes) (u.ToString printTypes)
      | Lambda(x,t) -> sprintf @"(\%s.%s)" (printTypes.PrintVar x) (t.ToString printTypes)
      | Let(_bind,_expr,_in) -> sprintf "let %s = %s in %s" (printTypes.PrintVar _bind) (_expr.ToString printTypes) (_in.ToString printTypes)
      | True -> sprintf "TRUE"
      | False -> sprintf "FALSE"
      | And -> sprintf "AND"
      | Or -> sprintf "OR"
      | Not -> sprintf "!"
      | Plus -> sprintf "+"
      | Minus -> sprintf "-"
      | Mult -> sprintf "*"
      | IsZero -> sprintf "0?"
      | If -> sprintf "if"
      | Fix -> sprintf "fix"
      | MakePair -> sprintf "(,)"
      | First -> sprintf "$\pi_1$"
      | Second -> sprintf "$\pi_2$"
      | Match -> sprintf @"match"
      | Inl -> sprintf @"inl"
      | Inr -> sprintf @"inr"
    member this.ToFSharpInner newLine (printTypes:PrintTypes) pre =
      match this with
      | TypeLambda(x,t) -> t.ToFSharpInner newLine printTypes pre
      | Lambda(x,t) -> sprintf @"%s %s" (printTypes.PrintVar x) (t.ToFSharpInner newLine printTypes pre)
      | Highlighted(Lambda(x,t),_) ->
        Lambda(x,t).ToFSharpInner newLine printTypes pre
      | _ -> 
        let nl,pre = newLine (pre + "  ")
        sprintf "-> %s%s" nl (this.ToFSharp printTypes pre)
    member this.ToFSharp (printTypes:PrintTypes) pre =
      match this with
      | Type t -> 
        printTypes.PrintType t
      | TypeApplication(t,a) ->
        sprintf "%s%s" pre (printTypes.PrintTypeApplication (t.ToFSharp printTypes "") a)
      | TypeLambda(a,t) ->
        sprintf "%s%s%s" pre (printTypes.PrintTypeLambda a) (t.ToFSharp printTypes "")
      | Var s -> pre + s
      | Hidden t -> sprintf @"..."
      | Highlighted(t,_) -> t.ToFSharp printTypes pre
      | Application(Application(And,t),u) -> sprintf "%s(%s && %s)" pre (t.ToFSharp printTypes "") (u.ToFSharp printTypes "")
      | Application(Application(Or,t),u) -> sprintf "%s(%s || %s)" pre (t.ToFSharp printTypes "") (u.ToFSharp printTypes "")
      | Application(Application(Plus,t),u) -> sprintf "%s(%s + %s)" pre (t.ToFSharp printTypes "") (u.ToFSharp printTypes "")
      | Application(Application(Minus,t),u) -> sprintf @"%s(%s - %s)" pre (t.ToFSharp printTypes "") (u.ToFSharp printTypes "")
      | Application(Application(Mult,t),u) -> sprintf "%s(%s * %s)" pre (t.ToFSharp printTypes "") (u.ToFSharp printTypes "")
      | Application(IsZero,t) -> sprintf @"%s(%s = 0)" pre (t.ToFSharp printTypes "")
      | Application(Application(Application(If,c),t),e) -> sprintf "%sif %s then\n%s\n%selse\n%s\n" pre (c.ToFSharp printTypes "") (t.ToFSharp printTypes (pre + "  ")) pre (e.ToFSharp printTypes (pre + "  "))
      | Application(Application(MakePair,t),u) -> sprintf @"%s(%s, %s)" pre (t.ToFSharp printTypes "") (u.ToFSharp printTypes "")
      | Application(Application(Application(Match, t), Lambda(x,f)), (Lambda(y,g))) ->
        let f' = f.replace (fst x) (Var"x")
        let g' = g.replace (fst y) (Var"y")
        sprintf "%smatch %s with\n%s| Choice1Of2 x ->\n %s\n%s| Choice2Of2 y -> \n%s\n" pre (t.ToFSharp printTypes "") pre (f'.ToFSharp printTypes (pre + "  ")) pre (g'.ToFSharp printTypes (pre + "  "))
      | Let(f_name,Lambda(x,t),u) ->
        if t.Length < 10 then
          sprintf "%slet %s = \n%sfun %s %s\n%s" pre (printTypes.PrintVar f_name) (pre + "  ") (printTypes.PrintVar x) (t.ToFSharpInner (fun pre -> "","") printTypes (pre + "  ")) (u.ToFSharp printTypes (pre))
        else
          sprintf "%slet %s = \n%sfun %s %s\n%s" pre (printTypes.PrintVar f_name) (pre + "  ") (printTypes.PrintVar x) (t.ToFSharpInner (fun pre -> "\n",pre) printTypes (pre + "  ")) (u.ToFSharp printTypes (pre))
      | Let(f_name,Application(Fix,Lambda(f,Lambda(x,t))),u) ->
        let t' = t.replace (printTypes.PrintVar f) (Var (printTypes.PrintVar f_name))
        sprintf "%slet rec %s = \n%sfun %s %s\n%s" pre (printTypes.PrintVar f_name) (pre + "  ") (printTypes.PrintVar x) (t'.ToFSharpInner (fun pre -> "\n",pre) printTypes (pre + "  ")) (u.ToFSharp printTypes (pre))
      | Application(t,u) -> sprintf "%s(%s %s)" pre (t.ToFSharp printTypes "") (u.ToFSharp printTypes "")
      | Lambda(x,t) -> 
        if t.Length < 10 then
          sprintf @"%s(fun %s %s)" pre (printTypes.PrintVar x) (t.ToFSharpInner (fun pre -> "","") printTypes pre)
        else
          sprintf @"%s(fun %s %s)" pre (printTypes.PrintVar x) (t.ToFSharpInner (fun pre -> "\n",pre) printTypes pre)
      | Let(_bind,_expr,_in) -> 
        if _expr.Length < 5 then
          sprintf "%slet %s = %s\n%s" pre (printTypes.PrintVar _bind) (_expr.ToFSharp printTypes "") (_in.ToFSharp printTypes pre)
        else
          sprintf "%slet %s = \n%s\n%s" pre (printTypes.PrintVar _bind) (_expr.ToFSharp printTypes (pre + "  ")) (_in.ToFSharp printTypes pre)
      | True -> sprintf "true"
      | False -> sprintf "false"
      | And -> sprintf "(&&)"
      | Or -> sprintf "(||)"
      | Not -> sprintf "not"
      | Plus -> sprintf "(+)"
      | Minus -> sprintf "(-)"
      | Mult -> sprintf "(*)"
      | IsZero -> sprintf "((=) 0)"
      | If -> sprintf "if"
      | Fix -> sprintf "letrec"
      | MakePair -> sprintf "(,)"
      | First -> sprintf "fst"
      | Second -> sprintf "snd"
      | Match -> sprintf @"match"
      | Inl -> sprintf @"Choice1Of2"
      | Inr -> sprintf @"Choice2Of2"

and PrintTypes =
  { PrintVar : (string * Type) -> string;
    PrintType : Type -> string;
    PrintTypeLambda : string -> string;
    PrintTypeApplication : string -> Type -> string }
  with 
    static member Untyped =
      {
        PrintVar = fst
        PrintType = (fun _ -> "")
        PrintTypeLambda = (fun a -> "")
        PrintTypeApplication = (fun t a -> t)
      }
    static member TypedLambda =
      {
        PrintVar = (fun (x,t) -> sprintf "(%s:%s)" x (t.ToLambda))
        PrintType = (fun t -> t.ToLambda)
        PrintTypeLambda = (fun a -> sprintf @"$\Lambda$%s$\Rightarrow$" (toGreekLetter a))
        PrintTypeApplication = (fun t a -> sprintf "(%s %s)" t (a.ToLambda))
      }

let (!!) x = Var x
let (>>) t u = Application(t,u)
let (>>=) t u = TypeApplication(t,u)
let (==>) (x,x_t) t = Lambda((x,x_t), t)
let (!!!) x = Type.Var x
let (~-) x = x,!!!""
let (>=>) a t = TypeLambda(a, t)
let (>>>) t u = Type.Application(t,u)
let (-->) t u = Type.Arrow(t,u)


let invDefaultTypes,defaultTypes =
  [
    Boolean, Forall("a", !!!"a" --> (!!!"a" --> !!!"a"))
    Nat, Forall("a", (!!!"a" --> !!!"a") --> (!!!"a" --> !!!"a"))
    Type.Product, Forall("a", Forall("b", Forall("c", !!!"a" --> (!!!"b" --> !!!"c"))))
    Type.Sum, Forall("a", Forall("b", Forall("c", (!!!"a" --> !!!"c") --> ((!!!"b" --> !!!"c") --> !!!"c"))))
  ] |> (fun l -> l |> List.map (fun (x,y) -> y,x) |> Map.ofList, l |> Map.ofList)

let invDefaultTerms, defaultTerms =
  [
    True, ("a" >=> (("t",!!!"a") ==> (("f",!!!"a") ==> (!!"t"))))
    False, ("a" >=> (("t",!!!"a") ==> (("f",!!!"a") ==> (!!"f"))))
    And, ((("p",Boolean) ==> (("q",Boolean) ==> (((!!"p" >>= Boolean) >> !!"q") >> !!"p"))))
    Or, ((("p",Boolean) ==> (("q",Boolean) ==> (((!!"p" >>= Boolean) >> !!"p") >> !!"q"))))
    If, (("b" >=> (("p",Boolean) ==> (("th",!!!"b") ==> (("el",!!!"b") ==> ((!!"p" >>= !!!"b") >> !!"th" >> !!"el"))))))

    Plus, ((("m",Nat) ==> (("n",Nat) ==> 
              ("a" >=> (("s",((!!!"a")-->(!!!"a"))) ==> (("z",!!!"a") ==> (((!!"m" >>= !!!"a") >> !!"s") >> (((!!"n" >>= !!!"a") >> !!"s") >> !!"z"))))))))
    Mult, ((("m",Nat) ==> (("n",Nat) ==> 
              ("a" >=> (("s",((!!!"a")-->(!!!"a"))) ==> (("z",!!!"a") ==> (((!!"m" >>= !!!"a") >> ((!!"n" >>= !!!"a") >> !!"s")) >> !!"z")))))))
    IsZero, ((("m",Nat) ==> (("n",Nat) ==> 
                (((!!"m" >>= Boolean) >> (("x",Boolean) ==> False)) >> True))))

    Fix, ("a" >=> (("f",!!!"a" --> !!!"a") ==> ((-"x" ==> (!!"f" >> (!!"x" >> !!"x"))) >> (-"x" ==> (!!"f" >> (!!"x" >> !!"x"))))))
    MakePair, ("a" >=> ("b" >=> (("x",!!!"a") ==> (("y",!!!"b") ==> ("c" >=> (("f",(!!!"a" --> (!!!"b" --> !!!"c"))) ==> ((!!"f" >> !!"x") >> !!"y")))))))
    First, ("a" >=> ("b" >=> (("p",((Type.Product >>> !!!"a") >>> !!!"b")) ==> ((!!"p" >>= !!!"a") >> (("x",!!!"a") ==> (("y",!!!"a") ==> (!!"x")))))))
    Second, ("a" >=> ("b" >=> (("p",((Type.Product >>> !!!"a") >>> !!!"b")) ==> ((!!"p" >>= !!!"a") >> (("x",!!!"a") ==> (("y",!!!"a") ==> (!!"y")))))))

    Inl, ("a" >=> ("b" >=> (("x",!!!"a") ==> ("c" >=> (("f",(!!!"a" --> !!!"c")) ==> (("g",(!!!"b" --> !!!"c")) ==> (!!"f" >> !!"x")))))))
    Inr, ("a" >=> ("b" >=> (("y",!!!"b") ==> ("c" >=> (("f",(!!!"a" --> !!!"c")) ==> (("g",(!!!"b" --> !!!"c")) ==> (!!"g" >> !!"y")))))))
    Match, ("a" >=> ("b" >=> 
                  (("u",(Type.Sum >>> !!!"a") >>> !!!"b") ==> 
                        ("c" >=> (("f",(!!!"a" --> !!!"c")) ==> (("g",(!!!"b" --> !!!"c")) ==> (((!!"u" >>= !!!"c") >> !!"f") >> !!"g")))))))
  ] |> (fun l -> l |> List.map (fun (x,y) -> y,x) |> Map.ofList, l |> Map.ofList)

let deltaRules (t:Term) : Option<Term> =
  match defaultTerms |> Map.tryFind t with
  | Some v -> Some v
  | _ ->
    match t with
    | Var v ->
      let res = ref 0
      if System.Int32.TryParse(v, res) then
        let mutable t = !!"z"
        for i = 1 to res.Value do
          t <- !!"s" >> t
        t <- ("a" >=> (("s",((!!!"a")-->(!!!"a"))) ==> (("z",!!!"a") ==> t)))
        Some t
      else
        Option.None
    | Let(x,t,u) ->
      Some ((x ==> u) >> t)
    | _ -> 
      Option.None

let inverseDeltaRules (t:Term) : Option<Term> =
  match invDefaultTerms |> Map.tryFind t with
  | Some v -> 
    Some v
  | _ ->
    match t with
    | TypeLambda("c", Lambda(("f",_),Lambda(("g",_),Application(Var "f", t)))) ->
      Some(Application(Inl, t))
    | TypeLambda("c", Lambda(("f",_),Lambda(("g",_),Application(Var "g", t)))) ->
      Some(Application(Inr, t))

    | TypeLambda("a", Lambda(("s",Type.Arrow(Type.Var"a",Type.Var"a")),Lambda(("z",Type.Var"a"),t))) ->
      let rec loop t = 
        match t with
        | Var "z" -> 
          Some(0)
        | Application(Var "s", t') ->
          match loop t' with
          | Some x -> Some(x + 1)
          | _ -> Option.None
        | _ -> Option.None
      match loop t with
      | Some x -> Some (Var(string x))
      | _ -> Option.None
    | _ -> 
      Option.None
