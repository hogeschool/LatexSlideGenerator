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
  with
    member this.ToLambdaInner =
      match this with
      | Lambda(x,t) -> sprintf @"%s$\rightarrow$%s" x (t.ToLambdaInner)
      | Highlighted(Lambda(x,t)) ->
        sprintf @"(*@\underline{%s$\rightarrow$}@*) %s" x ((Highlighted t).ToLambdaInner)
      | _ -> this.ToLambda
    member this.ToLambda =
      match this with
      | Var s -> s
      | Hidden t -> sprintf @"..."
      | Highlighted t -> 
        let t_lambda = t.ToLambda
        if t_lambda.Length <= 50 then
          sprintf @"(*@\underline{%s}@*)" t_lambda
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
      | Let(_bind,_expr,_in) -> sprintf "let %s = %s in %s" _bind _expr.ToString _in.ToString

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
