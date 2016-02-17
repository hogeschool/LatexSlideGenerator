module CodeDefinitionLambda

open Coroutine
open CommonLatex
open System.Collections.Generic


type Term =
  | Var of string
  | Application of Term * Term
  | Lambda of string * Term
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
  | Let of string * Term * Term
  | Highlighted of Term
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
      | Lambda(t,f) when t <> x -> Lambda(t, f.replace x u)
      | Application(t,f) -> Application(t.replace x u,f.replace x u)
      | _ -> t

    member this.ToLambdaInner =
      match this with
      | Lambda(x,t) -> sprintf @"%s$\rightarrow$%s" x (t.ToLambdaInner)
      | Highlighted(Lambda(x,t)) ->
        sprintf @"(*@\underline{%s$\rightarrow$}@*) %s" x ((Highlighted t).ToLambdaInner)
      | _ -> this.ToLambda
    member this.Length = 
      match this with
      | Highlighted t -> t.Length
      | Application(t,u) -> t.Length + u.Length
      | Lambda(x,t) -> 1 + t.Length
      | _ -> 1

    member this.ToLambda =
      match this with
      | Var s -> s
      | Hidden t -> sprintf @"..."
      | Highlighted t -> 
        if t.Length <= 15 then
          sprintf @"(*@\underline{%s}@*)" t.ToLambda
        else
          match t with
//          | Application(Application(And,t),u) -> sprintf @"(%s $\wedge$ %s)" (t.ToLambda) (u.ToLambda)
//          | Application(Application(Or,t),u) -> sprintf @"(%s $\vee$ %s)" (t.ToLambda) (u.ToLambda)
//          | Application(Application(Plus,t),u) -> sprintf @"(%s $+$ %s)" (t.ToLambda) (u.ToLambda)
//          | Application(Application(Minus,t),u) -> sprintf @"(%s $-$ %s)" (t.ToLambda) (u.ToLambda)
//          | Application(Application(Mult,t),u) -> sprintf @"(%s $\times$ %s)" (t.ToLambda) (u.ToLambda)
//          | Application(IsZero,t) -> sprintf @"(%s $=$ 0)" (t.ToLambda)
          | Application(Application(Application(If,c),t),e) -> 
            Application(Application(Application(If,Highlighted(c)),Highlighted(t)),Highlighted(e)).ToLambda
          | Application(t,u) ->
            Application(Highlighted(t),Highlighted(u)).ToLambda
          | Lambda(x,t) -> 
            sprintf @"(*@\underline{$\lambda$%s$\rightarrow$}@*) %s" x ((Highlighted t).ToLambdaInner)
          | t -> 
            t.ToLambda
      | Application(Application(And,t),u) -> sprintf @"(%s $\wedge$ %s)" (t.ToLambda) (u.ToLambda)
      | Application(Application(Or,t),u) -> sprintf @"(%s $\vee$ %s)" (t.ToLambda) (u.ToLambda)
      | Application(Application(Plus,t),u) -> sprintf @"(%s $+$ %s)" (t.ToLambda) (u.ToLambda)
      | Application(Application(Minus,t),u) -> sprintf @"(%s $-$ %s)" (t.ToLambda) (u.ToLambda)
      | Application(Application(Mult,t),u) -> sprintf @"(%s $\times$ %s)" (t.ToLambda) (u.ToLambda)
      | Application(IsZero,t) -> sprintf @"(%s $=$ 0)" (t.ToLambda)
      | Application(Application(Application(If,c),t),e) -> sprintf "if %s then %s else %s" (c.ToLambda) (t.ToLambda) (e.ToLambda)
      | Application(Application(MakePair,t),u) -> sprintf @"(%s, %s)" (t.ToLambda) (u.ToLambda)
      | Application(t,u) -> sprintf "(%s %s)" (t.ToLambda) (u.ToLambda)
      | Lambda(x,t) -> sprintf @"($\lambda$%s$\rightarrow$%s)" x (t.ToLambdaInner)
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
      | Let(_bind,_expr,_in) -> sprintf "let %s = %s in %s" _bind _expr.ToLambda _in.ToLambda
    member this.ToString =
      match this with
      | Var s -> s
      | Hidden t -> sprintf @"..."
      | Highlighted t -> t.ToString
      | Application(Application(And,t),u) -> sprintf "(%s AND %s)" (t.ToString) (u.ToString)
      | Application(Application(Or,t),u) -> sprintf "(%s OR %s)" (t.ToString) (u.ToString)
      | Application(Application(Plus,t),u) -> sprintf "(%s + %s)" (t.ToString) (u.ToString)
      | Application(Application(Minus,t),u) -> sprintf @"(%s $-$ %s)" (t.ToString) (u.ToString)
      | Application(Application(Mult,t),u) -> sprintf "(%s * %s)" (t.ToString) (u.ToString)
      | Application(IsZero,t) -> sprintf @"(%s $=$ 0)" (t.ToString)
      | Application(Application(Application(If,c),t),e) -> sprintf "if %s then %s else %s" (c.ToString) (t.ToString) (e.ToString)
      | Application(Application(MakePair,t),u) -> sprintf @"(%s, %s)" (t.ToString) (u.ToString)
      | Application(t,u) -> sprintf "(%s %s)" (t.ToString) (u.ToString)
      | Lambda(x,t) -> sprintf @"(\%s.%s)" x (t.ToString)
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
      | Let(_bind,_expr,_in) -> sprintf "let %s = %s in %s" _bind _expr.ToString _in.ToString
    member this.ToFSharpInner pre =
      match this with
      | Lambda(x,t) -> sprintf @"%s %s" x (t.ToFSharpInner pre)
      | Highlighted(Lambda(x,t)) ->
        Lambda(x,t).ToFSharpInner pre
      | _ -> sprintf "->\n%s" (this.ToFSharp (pre + "  "))
    member this.ToFSharp pre =
      match this with
      | Var s -> pre + s
      | Hidden t -> sprintf @"..."
      | Highlighted t -> t.ToFSharp pre
      | Application(Application(And,t),u) -> sprintf "%s(%s && %s)" pre (t.ToFSharp "") (u.ToFSharp "")
      | Application(Application(Or,t),u) -> sprintf "%s(%s || %s)" pre (t.ToFSharp "") (u.ToFSharp "")
      | Application(Application(Plus,t),u) -> sprintf "%s(%s + %s)" pre (t.ToFSharp "") (u.ToFSharp "")
      | Application(Application(Minus,t),u) -> sprintf @"%s(%s - %s)" pre (t.ToFSharp "") (u.ToFSharp "")
      | Application(Application(Mult,t),u) -> sprintf "%s(%s * %s)" pre (t.ToFSharp "") (u.ToFSharp "")
      | Application(IsZero,t) -> sprintf @"%s(%s = 0)" pre (t.ToFSharp "")
      | Application(Application(Application(If,c),t),e) -> sprintf "%sif %s then\n%s\n%selse\n%s\n" pre (c.ToFSharp "") (t.ToFSharp (pre + "  ")) pre (e.ToFSharp (pre + "  "))
      | Application(Application(MakePair,t),u) -> sprintf @"%s(%s, %s)" pre (t.ToFSharp "") (u.ToFSharp "")
      | Application(Application(Application(Match, t), Lambda(x,f)), (Lambda(y,g))) ->
        let f' = f.replace x (Var"x")
        let g' = g.replace y (Var"y")
        sprintf "%smatch %s with\n%s| Choice1Of2 x ->\n %s\n%s| Choice2Of2 y -> \n%s\n" pre (t.ToFSharp "") pre (f'.ToFSharp (pre + "  ")) pre (g'.ToFSharp (pre + "  "))
      | Let(f_name,Lambda(x,t),u) ->
        sprintf "%slet %s = \n%sfun %s %s\n%s" pre f_name (pre + "  ") x (t.ToFSharpInner (pre + "  ")) (u.ToFSharp (pre))
      | Let(f_name,Application(Fix,Lambda(f,Lambda(x,t))),u) ->
        let t' = t.replace f (Var f_name)
        sprintf "%slet rec %s = \n%sfun %s %s\n%s" pre f_name (pre + "  ") x (t'.ToFSharpInner (pre + "  ")) (u.ToFSharp (pre))
      | Application(t,u) -> sprintf "%s(%s %s)" pre (t.ToFSharp "") (u.ToFSharp "")
      | Lambda(x,t) -> 
        let t_inner = (t.ToFSharpInner pre)
        sprintf @"%s(fun %s %s)" pre x t_inner
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
      | Let(_bind,_expr,_in) -> sprintf "%slet %s = \n%s\n%s" pre _bind (_expr.ToFSharp (pre + "  ")) (_in.ToFSharp pre)

let (!!) x = Var x
let (>>>) t u = Application(t,u)
let (==>) x t = Lambda(x, t)


let invDefaultTerms, defaultTerms =
  [
    True, ("t" ==> ("f" ==> (!!"t")))
    False, ("t" ==> ("f" ==> (!!"f")))
    Not, ("a" ==> ("b" ==> ("c" ==> (!!"a" >>> !!"c" >>> !!"b"))))
    And, ("a" ==> ("b" ==> (!!"a" >>> !!"b" >>> !!"a")))
    Or, ("a" ==> ("b" ==> (!!"a" >>> !!"a" >>> !!"b")))
    If, ("c" ==> ("t" ==> ("e" ==> (!!"c" >>> !!"t" >>> !!"e"))))

    Plus, ("m" ==> ("n" ==> ("s" ==> ("z" ==> ((!!"m" >>> !!"s") >>> ((!!"n" >>> !!"s") >>> !!"z"))))))
    Mult, ("m" ==> ("n" ==> ("s" ==> ("z" ==> ((!!"m" >>> (!!"n" >>> !!"s")) >>> !!"z")))))
    IsZero, ("m" ==> ((!!"m" >>> ("x" ==> False)) >>> True))

    Fix, ("f" ==> (("x" ==> (!!"f" >>> (!!"x" >>> !!"x"))) >>> ("x" ==> (!!"f" >>> (!!"x" >>> !!"x")))))
    MakePair, ("x" ==> ("y" ==> ("f" ==> ((!!"f" >>> !!"x") >>> !!"y"))))
    First, ("p" ==> (!!"p" >>> ("x" ==> ("y" ==> (!!"x")))))
    Second, ("p" ==> (!!"p" >>> ("x" ==> ("y" ==> (!!"y")))))

    Inl, ("x" ==> ("f" ==> ("g" ==> (!!"f" >>> !!"x"))))
    Inr, ("y" ==> ("f" ==> ("g" ==> (!!"g" >>> !!"y"))))
    Match, ("u" ==> ("f" ==> ("g" ==> ((!!"u" >>> !!"f") >>> !!"g"))))
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
          t <- !!"s" >>> t
        t <- "s" ==> ("z" ==> t)
        Some t
      else
        Option.None
    | Let(x,t,u) ->
      Some ((x ==> u) >>> t)
    | _ -> 
      Option.None

let inverseDeltaRules (t:Term) : Option<Term> =
  match invDefaultTerms |> Map.tryFind t with
  | Some v -> 
    Some v
  | _ ->
    match t with
    | Lambda("f",Lambda("g",Application(Var "f", t))) ->
      Some(Application(Inl, t))
    | Lambda("f",Lambda("g",Application(Var "g", t))) ->
      Some(Application(Inr, t))
    | Lambda("s",Lambda("z",t)) ->
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
