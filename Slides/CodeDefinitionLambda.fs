module CodeDefinitionLambda

open Coroutine
open CommonLatex

type Type =
  | Id of string
  | Var of string
  | Arrow of Type * Type
  | Forall of string * Type
  | Mu of string * Type
  | Application of Type * Type
  | Boolean
  | Nat
  | String
  | Unit
  | Product
  | Sum
  | Record of List<string * Type>
  | Union of List<string * List<Type>>
  with 
    member this.Length = 
      match this with
      | Arrow(t,u) -> t.Length + u.Length
      | Forall(x,t) -> 1 + t.Length
      | Mu(x,t) -> 1 + t.Length
      | Application(t,u) -> t.Length + u.Length
      | Record(ls) -> 
        1 + (ls |> List.map snd |> List.map (fun t -> t.Length) |> List.sum)
      | Union(ls) -> 
        1 + (ls |> List.map snd |> List.map (fun t -> t |> List.map (fun t -> t.Length) |> List.sum) |> List.sum)
      | _ -> 1
    member t.replace (x:string) (u:Type) : Type =
      match t with
      | Id s | Var s when s = x -> u
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
      | Id s -> s
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
      | Unit ->
        "Unit"
      | String ->
        "String"
      | Boolean ->
        "Boolean"
      | Nat ->
        "Nat"
      | Product ->
        @"$\times$"
      | Sum ->
        @"|"
      | _ -> 
        failwith "Unsupported lambda calculus type declaration."
    member this.ToFSharpInner =
      match this with
      | Arrow(t,u) ->
        sprintf @"-> %s %s" (t.ToFSharp) (u.ToFSharpInner)
      | t -> 
        sprintf @"-> %s" t.ToFSharp
    member this.ToFSharp =
      match this with
      | Id s -> s
      | Var s -> sprintf "'%s" s
      | Arrow(t,u) ->
        sprintf @"(%s %s)" (t.ToFSharp) (u.ToFSharpInner)
//      | Mu(a,u) ->
//        sprintf @"($\mu$%s$\Rightarrow$%s)" (toGreekLetter a) (u.ToLambdaMuInner)
      | Application(Application(Product,t),u) ->
        sprintf @"(%s*%s)" (t.ToFSharp) (u.ToFSharp)
      | Application(Application(Sum,t),u) ->
        sprintf @"Choice<%s,%s>" (t.ToFSharp) (u.ToFSharp)
      | Application(t,u) ->
        sprintf @"(%s %s)" (t.ToFSharp) (u.ToFSharp)
      | Unit ->
        "Unit"
      | String ->
        "string"
      | Boolean ->
        "bool"
      | Nat ->
        "int"
      | Product ->
        @"*"
      | Sum ->
        @"Choice"
      | Record(fs) ->
        let decls = fs |> List.map (fun (n,t) -> sprintf "%s:%s" n t.ToFSharp) |> List.reduce (fun a b -> a + "; " + b)
        sprintf @"{ %s }" decls
      | Union(cs) ->
        let caseArgs (ts:List<Type>) = 
          match ts with
          | [] -> ""
          | _ ->
            let args = ts |> List.map (fun t -> t.ToLambda) |> List.reduce (fun a b -> a + "*" + b)
            let res = sprintf " of %s" args
            res
        let decls = cs |> List.map (fun (n,t) -> sprintf "\n  | %s%s" n (caseArgs t)) |> List.reduce (+)
        decls
      | _ -> failwith "Unsupported F\# type declaration."

type Term =
  | Type of Type
  | Var of string
  | Application of Term * Term
  | Lambda of (string * Type) * Term
  | TypeApplication of Term * Type
  | TypeLambda of string * Term
  | TypeLet of string * Type * Term
  | Let of (string * Type) * Term * Term
  | MakeRecord of List<string * Term>
  | RecordWith of Term * List<string * Term>
  | MatchCustom of Term * List<string * List<string> * Term>
  | HaskellFuncDef of string * Option<List<Term>> * List<Term>
  | Unit
  | Dot of Term * string
  | StringConst of string
  | True
  | False
  | Not
  | And
  | Or
  | Plus
  | Minus
  | Mult
  | Pow
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
    member t.Untyped =
      match t with
      | TypeApplication(t,a) ->
        t.Untyped
      | TypeLambda(a,t) ->
        t.Untyped
      | Hidden t -> 
        Hidden(t.Untyped)
      | Highlighted(t,h) -> 
        Highlighted(t.Untyped,h)
      | Application(t,u) -> 
        Application(t.Untyped,u.Untyped)
      | Lambda((x,t_x),t) -> 
        Lambda((x,Type.Var("")),t.Untyped)
      | Let((x,t_x),_expr,_in) ->
        Let((x,Type.Var""),_expr.Untyped,_in.Untyped)
      | t -> t
      
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
        sprintf @"(*@\colorbox{orange}{%s}@*)%s" !x ((Highlighted(t,Underlined)).ToLambdaInner printTypes)
      | Highlighted(Lambda(x,t),Colored) ->
        sprintf @"(*@\colorbox{yellow}{%s}@*)%s" !x ((Highlighted(t,Colored)).ToLambdaInner printTypes)
//      | _ -> sprintf @"$\rightarrow$%s" (this.ToLambda printTypes)
      | _ -> sprintf @"$.$%s" (this.ToLambda printTypes)
    member this.Length = 
      match this with
      | Highlighted(t,_) -> t.Length
      | Application(t,u) -> t.Length + u.Length
      | Lambda(x,t) -> 1 + t.Length
      | TypeLambda(x,t) -> 1 + t.Length
      | TypeApplication(t,u) -> t.Length + u.Length
      | Type(t) -> 1 + t.Length
      | Match -> 10
      | MatchCustom(_) -> 10
      | _ -> 1

    member this.ToLambda (printTypes:PrintTypes) =
      match this with
      | Unit -> "()"
      | TypeLet(t_n,t,u) -> 
        sprintf "%s%s" (printTypes.PrintTypeDecl t_n t) (u.ToLambda printTypes)
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
        sprintf @"(*@\colorbox{orange}{%s}@*)" (t.ToLambda printTypes)
//      | Highlighted(t,Underlined) -> 
//        if t.Length <= 10 then
//          sprintf @"(*@\underline{%s}@*)" (t.ToLambda printTypes)
//        else
//          match t with
////          | Application(Application(And,t),u) -> sprintf @"(%s $\wedge$ %s)" (t.ToLambda) (u.ToLambda)
////          | Application(Application(Or,t),u) -> sprintf @"(%s $\vee$ %s)" (t.ToLambda) (u.ToLambda)
////          | Application(Application(Plus,t),u) -> sprintf @"(%s $+$ %s)" (t.ToLambda) (u.ToLambda)
////          | Application(Application(Minus,t),u) -> sprintf @"(%s $-$ %s)" (t.ToLambda) (u.ToLambda)
////          | Application(Application(Mult,t),u) -> sprintf @"(%s $\times$ %s)" (t.ToLambda) (u.ToLambda)
////          | Application(IsZero,t) -> sprintf @"(%s $=$ 0)" (t.ToLambda)
//          | Application(Application(Application(If,c),t),e) -> 
//            Application(Application(Application(If,Highlighted(c,Underlined)),Highlighted(t,Underlined)),Highlighted(e,Underlined)).ToLambda printTypes
//          | Application(t,u) ->
//            Application(Highlighted(t,Underlined),Highlighted(u,Underlined)).ToLambda printTypes
//          | Lambda(x,t) -> 
//            sprintf @"(*@\underline{$\lambda$%s$\rightarrow$}@*) %s" (printTypes.PrintVar x) ((Highlighted(t,Underlined)).ToLambdaInner printTypes)
//          | TypeLambda(a,t) -> 
//            sprintf @"(*@\underline{%s}@*) %s" (printTypes.PrintTypeLambda a) (Highlighted(t,Underlined).ToLambda printTypes)
//          | t -> 
//            t.ToLambda printTypes
      | Application(Application(And,t),u) -> sprintf @"(%s $\wedge$ %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Application(Application(Or,t),u) -> sprintf @"(%s $\vee$ %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Application(Application(Plus,t),u) -> sprintf @"(%s $+$ %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Application(Application(Minus,t),u) -> sprintf @"(%s $-$ %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Application(Application(Mult,t),u) -> sprintf @"(%s $\times$ %s)" (t.ToLambda printTypes) (u.ToLambda printTypes)
      | Application(Application(Pow,m),n) -> sprintf @"($%s^{%s}$)" (m.ToLambda printTypes) (n.ToLambda printTypes)
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
      | Pow -> sprintf @"$\wedge$"
      | If -> sprintf "if-then-else"
      | Fix -> sprintf "fix"
      | MakePair -> sprintf "(,)"
      | First -> sprintf "$\pi_1$"
      | Second -> sprintf "$\pi_2$"
      | Match -> sprintf @"match"
      | Inl -> sprintf @"inl"
      | Inr -> sprintf @"inr"
      | MakeRecord(fs) ->
        let decls = fs |> List.map (fun (n,t) -> sprintf "%s = %s" n (t.ToLambda printTypes)) |> List.reduce (fun a b -> a + "; " + b)
        sprintf @"{ %s }" decls
      | _ -> failwith "Unsupported lambda term."
    member this.ToString (printTypes:PrintTypes) =
      match this with
      | Unit -> "()"
      | Type t -> 
        printTypes.PrintType t
      | TypeLet(t_n,t,u) -> 
        sprintf "%s%s" (printTypes.PrintTypeDecl t_n t) (u.ToLambda printTypes)
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
      | Application(Application(Pow,m),n) -> sprintf @"($%s^{%s}$)" (m.ToString printTypes) (n.ToString printTypes)
      | Application(IsZero,t) -> sprintf @"(%s $=$ 0)" (t.ToString printTypes)
      | Application(Application(Application(If,c),t),e) -> sprintf "if %s then %s else %s" (c.ToString printTypes) (t.ToString printTypes) (e.ToString printTypes)
      | Application(Application(MakePair,t),u) -> sprintf @"(%s, %s)" (t.ToString printTypes) (u.ToString printTypes)
      | Application(t,u) -> sprintf "(%s %s)" (t.ToString printTypes) (u.ToString printTypes)
      | Lambda(x,t) -> sprintf @"(\%s.%s)" (printTypes.PrintVar x) (t.ToString printTypes) // should '\' be '\lambda' ?
      | Let(_bind,_expr,_in) -> sprintf "let %s = %s in %s" (printTypes.PrintVar _bind) (_expr.ToString printTypes) (_in.ToString printTypes)
      | True -> sprintf "TRUE"
      | False -> sprintf "FALSE"
      | And -> sprintf "AND"
      | Or -> sprintf "OR"
      | Not -> sprintf "!"
      | Plus -> sprintf "+"
      | Minus -> sprintf "-"
      | Mult -> sprintf "*"
      | Pow -> sprintf @"\wedge"
      | IsZero -> sprintf "0?"
      | If -> sprintf "if"
      | Fix -> sprintf "fix"
      | MakePair -> sprintf "(,)"
      | First -> sprintf "$\pi_1$"
      | Second -> sprintf "$\pi_2$"
      | Match -> sprintf @"match"
      | Inl -> sprintf @"inl"
      | Inr -> sprintf @"inr"
      | MakeRecord(fs) ->
        let decls = fs |> List.map (fun (n,t) -> sprintf "%s = %s" n (t.ToString printTypes)) |> List.reduce (fun a b -> a + "; " + b)
        sprintf @"{ %s }" decls
      | _ -> failwith "Unsupported lambda term."
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
      | Unit -> "()"
      | Type t -> 
        printTypes.PrintType t
      | TypeLet(t_n,t,u) -> 
        sprintf "%s%s" (printTypes.PrintTypeDecl t_n t) (u.ToFSharp printTypes pre)
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
      | Application(Application(Pow,m),n) -> sprintf @"(%s$**${%s})" (m.ToFSharp printTypes "") (n.ToFSharp printTypes "")
      | Application(IsZero,t) -> sprintf @"%s(%s = 0)" pre (t.ToFSharp printTypes "")
      | Application(Application(Application(If,c),t),e) -> sprintf "%sif %s then\n%s\n%selse\n%s\n" pre (c.ToFSharp printTypes "") (t.ToFSharp printTypes (pre + "  ")) pre (e.ToFSharp printTypes (pre + "  "))
      | Application(Application(Var"::",t),u) -> sprintf @"%s%s :: %s" pre (t.ToFSharp printTypes "") (u.ToFSharp printTypes "")
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
      | Pow -> sprintf @"(\wedge)"
      | IsZero -> sprintf "((=) 0)"
      | If -> sprintf "if"
      | Fix -> sprintf "letrec"
      | MakePair -> sprintf "(,)"
      | First -> sprintf "fst"
      | Second -> sprintf "snd"
      | Match -> sprintf @"match"
      | Inl -> sprintf @"Choice1Of2"
      | Inr -> sprintf @"Choice2Of2"
      | StringConst(s) ->
        sprintf @"""%s""" s
      | Dot(r,f) ->
        sprintf @"%s.%s" (r.ToFSharp printTypes pre) f
      | MakeRecord(fs) ->
        let decls = fs |> List.map (fun (n,t) -> sprintf "%s = %s" n (t.ToFSharp printTypes "")) |> List.reduce (fun a b -> a + "; " + b)
        sprintf @"%s{ %s }" pre decls
      | RecordWith(r,fs) ->
        let decls = fs |> List.map (fun (n,t) -> sprintf "%s = %s" n (t.ToFSharp printTypes "")) |> List.reduce (fun a b -> a + "; " + b)
        sprintf @"%s{ %s with %s }" pre (r.ToFSharp printTypes "") decls
      | MatchCustom(u,ps) ->
        let makeArgs (c:string) (a:List<string>) = 
          let args =
            match a with
            | [] -> ""
            | _ ->
              sprintf @"(%s)" (a |> List.reduce (fun x y -> x + ", " + y))
          sprintf "%s%s" c args
        let makePattern ((c,a,t):string*List<string> * Term) =
          let args = makeArgs c a
          sprintf "%s| %s -> %s" pre args (t.ToFSharp printTypes "")
        let cases = ps |> List.map makePattern |> List.reduce (fun a b -> a + "\n" + b)
        sprintf "%smatch %s with\n%s" pre (u.ToFSharp printTypes "") cases

    member this.ToHaskellInner newLine (printTypes:PrintTypes) pre =
      match this with
      | TypeLambda(x,t) -> t.ToHaskellInner newLine printTypes pre
      | Lambda(x,t) -> sprintf @"%s %s" (printTypes.PrintVar x) (t.ToHaskellInner newLine printTypes pre)
      | Highlighted(Lambda(x,t),_) ->
        Lambda(x,t).ToHaskellInner newLine printTypes pre
      | _ -> 
        let nl,pre = newLine (pre + "  ")
        sprintf "-> %s%s" nl (this.ToHaskell printTypes pre)
    member this.ToHaskell (printTypes:PrintTypes) pre =
      match this with
      | Unit -> "()"
      | Type t -> 
        printTypes.PrintType t
      | TypeLet(t_n,t,u) -> 
        sprintf "%s%s" (printTypes.PrintTypeDecl t_n t) (u.ToHaskell printTypes pre)
      | TypeApplication(t,a) ->
        sprintf "%s%s" pre (printTypes.PrintTypeApplication (t.ToHaskell printTypes "") a)
      | TypeLambda(a,t) ->
        sprintf "%s%s%s" pre (printTypes.PrintTypeLambda a) (t.ToHaskell printTypes "")
      | Var s -> pre + s
      | Hidden t -> sprintf @"..."
      | Highlighted(t,_) -> t.ToHaskell printTypes pre
      | Application(Application(And,t),u) -> sprintf "%s(%s && %s)" pre (t.ToHaskell printTypes "") (u.ToHaskell printTypes "")
      | Application(Application(Or,t),u) -> sprintf "%s(%s || %s)" pre (t.ToHaskell printTypes "") (u.ToHaskell printTypes "")
      | Application(Application(Plus,t),u) -> sprintf "%s(%s + %s)" pre (t.ToHaskell printTypes "") (u.ToHaskell printTypes "")
      | Application(Application(Minus,t),u) -> sprintf @"%s(%s - %s)" pre (t.ToHaskell printTypes "") (u.ToHaskell printTypes "")
      | Application(Application(Mult,t),u) -> sprintf "%s(%s * %s)" pre (t.ToHaskell printTypes "") (u.ToHaskell printTypes "")
      | Application(Application(Pow,m),n) -> sprintf @"(%s\wedge%s)" (m.ToHaskell printTypes "") (n.ToHaskell printTypes "")
      | Application(IsZero,t) -> sprintf @"%s(%s == 0)" pre (t.ToHaskell printTypes "")
      | Application(Application(Application(If,c),t),e) -> sprintf "%sif %s then\n%s\n%selse\n%s\n" pre (c.ToHaskell printTypes "") (t.ToHaskell printTypes (pre + "  ")) pre (e.ToHaskell printTypes (pre + "  "))
      | Application(Application(Var":",t),u) -> sprintf @"%s%s : %s" pre (t.ToHaskell printTypes "") (u.ToHaskell printTypes "")
      | Application(Application(MakePair,t),u) -> sprintf @"%s(%s, %s)" pre (t.ToHaskell printTypes "") (u.ToHaskell printTypes "")
      | Application(Application(Application(Match, t), Lambda(x,f)), (Lambda(y,g))) ->
        let f' = f.replace (fst x) (Var"x")
        let g' = g.replace (fst y) (Var"y")
        sprintf "%scase %s of\n%s Left x ->\n %s\n%s Right y -> \n%s\n" pre (t.ToHaskell printTypes "") pre (f'.ToHaskell printTypes (pre + "  ")) pre (g'.ToHaskell printTypes (pre + "  "))
      | Let(f_name,Lambda(x,t),u) ->
        if t.Length < 10 then
          sprintf "%slet %s = \n%s\\ %s %s in\n%s" pre (printTypes.PrintVar f_name) (pre + "  ") (printTypes.PrintVar x) (t.ToHaskellInner (fun pre -> "","") printTypes (pre + "  ")) (u.ToHaskell printTypes (pre))
        else
          sprintf "%slet %s = \n%s\\ %s %s in\n%s" pre (printTypes.PrintVar f_name) (pre + "  ") (printTypes.PrintVar x) (t.ToHaskellInner (fun pre -> "\n",pre) printTypes (pre + "  ")) (u.ToHaskell printTypes (pre))
      | Let(f_name,Application(Fix,Lambda(f,Lambda(x,t))),u) ->
        let t' = t.replace (printTypes.PrintVar f) (Var (printTypes.PrintVar f_name))
        sprintf "%s%s = \n%s\\ %s %s\n%s" pre (printTypes.PrintVar f_name) (pre + "  ") (printTypes.PrintVar x) (t'.ToHaskellInner (fun pre -> "\n",pre) printTypes (pre + "  ")) (u.ToHaskell printTypes (pre))
      | Application(t,u) -> sprintf "%s(%s %s)" pre (t.ToHaskell printTypes "") (u.ToHaskell printTypes "")
      | Lambda(x,t) -> 
        if t.Length < 10 then
          sprintf @"%s(\%s %s)" pre (printTypes.PrintVar x) (t.ToHaskellInner (fun pre -> "","") printTypes pre)
        else
          sprintf @"%s(\%s %s)" pre (printTypes.PrintVar x) (t.ToHaskellInner (fun pre -> "\n",pre) printTypes pre)
      | Let(_bind,_expr,_in) -> 
        if _expr.Length < 5 then
          sprintf "%slet %s = %s in\n%s" pre (printTypes.PrintVar _bind) (_expr.ToHaskell printTypes "") (_in.ToHaskell printTypes pre)
        else
          sprintf "%slet %s = \n%s in\n%s" pre (printTypes.PrintVar _bind) (_expr.ToHaskell printTypes (pre + "  ")) (_in.ToHaskell printTypes pre)
      | True -> sprintf "True"
      | False -> sprintf "False"
      | And -> sprintf "(&&)"
      | Or -> sprintf "(||)"
      | Not -> sprintf "not"
      | Plus -> sprintf "(+)"
      | Minus -> sprintf "(-)"
      | Mult -> sprintf "(*)"
      | Pow -> sprintf @"(\wedge)"
      | IsZero -> sprintf "((=) 0)"
      | If -> sprintf "if"
      | Fix -> sprintf "letrec"
      | MakePair -> sprintf "(,)"
      | First -> sprintf "fst"
      | Second -> sprintf "snd"
      | Match -> sprintf @"case"
      | Inl -> sprintf @"Left"
      | Inr -> sprintf @"Right"
      | StringConst(s) ->
        sprintf @"""%s""" s
      | Dot(r,f) ->
        sprintf @"%s.%s" (r.ToHaskell printTypes pre) f
      | HaskellFuncDef(fname, typeOpt, functions) ->
          let typeDecl =
            match typeOpt with
            | None -> ""
            | Some typeVars ->
                sprintf "%s :: %s\n" fname (typeVars |> List.map(fun t -> t.ToHaskell printTypes "") |> List.reduce (fun a b -> a + "->" + b))
          let funcDecls = (functions |> List.map(fun t -> fname + "=" + t.ToHaskell printTypes "") |> List.reduce (fun a b -> a + "\n" + b))
          typeDecl + funcDecls
      | MakeRecord(fs) ->
        let decls = fs |> List.map (fun (n,t) -> sprintf "%s = %s" n (t.ToHaskell printTypes "")) |> List.reduce (fun a b -> a + ", " + b)
        sprintf @"%s{ %s }" pre decls
      | MatchCustom(u,ps) ->
        let makeArgs (c:string) (a:List<string>) = 
          let args =
            match a with
            | [] -> ""
            | _ ->
              sprintf @"(%s)" (a |> List.reduce (fun x y -> x + ", " + y))
          sprintf "%s%s" c args
        let makePattern ((c,a,t):string*List<string> * Term) =
          let args = makeArgs c a
          sprintf "%s %s -> %s" pre args (t.ToHaskell printTypes "")
        let cases = ps |> List.map makePattern |> List.reduce (fun a b -> a + "\n" + b)
        sprintf "%scase %s of\n%s" pre (u.ToHaskell printTypes "") cases


and PrintTypes =
  { PrintVar : (string * Type) -> string;
    PrintType : Type -> string;
    PrintTypeDecl : string -> Type -> string;
    PrintTypeLambda : string -> string;
    PrintTypeApplication : string -> Type -> string }
  with 
    static member Untyped =
      {
        PrintVar = fst
        PrintType = (fun _ -> "")
        PrintTypeDecl = (fun _ _ -> "")
        PrintTypeLambda = (fun a -> "")
        PrintTypeApplication = (fun t a -> t)
      }
    static member TypedLambda =
      {
        PrintVar = (fun (x,t) -> sprintf "(%s:%s)" x (t.ToLambda))
        PrintType = (fun t -> t.ToLambda)
        PrintTypeDecl = (fun t_n t -> sprintf "type %s = %s in" t_n t.ToLambda)
        PrintTypeLambda = (fun a -> sprintf @"$\Lambda$%s$\Rightarrow$" (toGreekLetter a))
        PrintTypeApplication = (fun t a -> sprintf "(%s %s)" t (a.ToLambda))
      }
    static member TypedFSharp =
      {
        PrintVar = (fun (x,t) -> sprintf "(%s:%s)" x (t.ToFSharp))
        PrintType = (fun t -> t.ToLambda)
        PrintTypeDecl = (fun t_n t -> sprintf "type %s = %s\n" t_n t.ToFSharp)
        PrintTypeLambda = (fun a -> sprintf @"<'%s>" a)
        PrintTypeApplication = (fun t a -> sprintf "%s<%s>" t (a.ToFSharp))
      }

let (!!) x = Var x
let (>>) t u = Application(t,u)
let (>>=) t u = TypeApplication(t,u)
let (==>) (x,x_t) t = Lambda((x,x_t), t)
let (!!!) x = Type.Var x
let (!!!!) x = Type.Id x
let (~-) x = x,!!!""
let (>=>) a t = TypeLambda(a, t)
let (>>>) t u = Type.Application(t,u)
let (-->) t u = Type.Arrow(t,u)


let invDefaultTypes,defaultTypes =
  [
    Boolean, Forall("a", !!!"a" --> (!!!"a" --> !!!"a"))
    Nat, Forall("a", (!!!"a" --> !!!"a") --> (!!!"a" --> !!!"a"))
    Type.Product, Forall("a", Forall("b", Forall("c", (!!!"a" --> (!!!"b" --> !!!"c")) --> !!!"c")))
    Type.Sum, Forall("a", Forall("b", Forall("c", (!!!"a" --> !!!"c") --> ((!!!"b" --> !!!"c") --> !!!"c"))))
  ] |> (fun l -> l |> List.map (fun (x,y) -> y,x) |> Map.ofList, l |> Map.ofList)

let invDefaultTerms, defaultTerms =
  let inverse,forward = 
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
      Pow, ((("m",Nat) ==> (("n",Nat) ==> 
                ("a" >=> (("s",((!!!"a")-->(!!!"a"))) ==> (("z",!!!"a") ==> ((((!!"n" >>= !!!"a") >> (!!"m" >>= !!!"a")) >> (!!"s")) >> !!"z")))))))
      IsZero, ((("n",Nat) ==> (((!!"n" >>= Boolean) >> (("x",Boolean) ==> False)) >> True)))

      Fix, ("a" >=> (("f",!!!"a" --> !!!"a") ==> ((-"x" ==> (!!"f" >> (!!"x" >> !!"x"))) >> (-"x" ==> (!!"f" >> (!!"x" >> !!"x"))))))
      MakePair, ("a" >=> ("b" >=> (("x",!!!"a") ==> (("y",!!!"b") ==> ("c" >=> (("f",(!!!"a" --> (!!!"b" --> !!!"c"))) ==> ((!!"f" >> !!"x") >> !!"y")))))))
      First, ("a" >=> ("b" >=> (("p",((Type.Product >>> !!!"a") >>> !!!"b")) ==> ((!!"p" >>= !!!"a") >> (("x",!!!"a") ==> (("y",!!!"b") ==> (!!"x")))))))
      Second, ("a" >=> ("b" >=> (("p",((Type.Product >>> !!!"a") >>> !!!"b")) ==> ((!!"p" >>= !!!"b") >> (("x",!!!"a") ==> (("y",!!!"b") ==> (!!"y")))))))

      Inl, ("a" >=> ("b" >=> (("x",!!!"a") ==> ("c" >=> (("f",(!!!"a" --> !!!"c")) ==> (("g",(!!!"b" --> !!!"c")) ==> (!!"f" >> !!"x")))))))
      Inr, ("a" >=> ("b" >=> (("y",!!!"b") ==> ("c" >=> (("f",(!!!"a" --> !!!"c")) ==> (("g",(!!!"b" --> !!!"c")) ==> (!!"g" >> !!"y")))))))
      Match, ("a" >=> ("b" >=> 
                    (("u",(Type.Sum >>> !!!"a") >>> !!!"b") ==> 
                          ("c" >=> (("f",(!!!"a" --> !!!"c")) ==> (("g",(!!!"b" --> !!!"c")) ==> (((!!"u" >>= !!!"c") >> !!"f") >> !!"g")))))))
    ] |> (fun l -> l |> List.map (fun (x,y) -> y,x),l)
  let inverse = 
    inverse @
     ([
        True, (-"t" ==> (-"f" ==> (!!"t")))
        False, (-"t" ==> (-"f" ==> (!!"f")))
        And, (-"p" ==> (-"q" ==> (!!"p" >> !!"q" >> !!"p")))
        Or, (-"p" ==> (-"q" ==> (!!"p" >> !!"p" >> !!"q")))
        If, (-"p" ==> (-"th" ==> (-"el" ==> (!!"p" >> !!"th" >> !!"el"))))

        Plus, (-"m" ==> (-"n" ==> (-"s" ==> (-"z" ==> ((!!"m" >> !!"s") >> ((!!"n" >> !!"s") >> !!"z"))))))
        Mult, (-"m" ==> (-"n" ==> (-"s" ==> (-"z" ==> ((!!"m" >> (!!"n" >> !!"s")) >> !!"z")))))
        Pow, (-"m" ==> (-"n" ==> (-"s" ==> (-"z" ==> (!!"n" >> !!"m" >> !!"s" >> !!"z")))))
        IsZero, (-"m" ==> ((!!"m" >> (-"x" ==> False)) >> True))

        Fix, (-"f" ==> ((-"x" ==> (!!"f" >> (!!"x" >> !!"x"))) >> (-"x" ==> (!!"f" >> (!!"x" >> !!"x")))))
        MakePair, (-"x" ==> (-"y" ==> (-"f" ==> ((!!"f" >> !!"x") >> !!"y"))))
        First, (-"p" ==> (!!"p" >> (-"x" ==> (-"y" ==> (!!"x")))))
        Second, (-"p" ==> (!!"p" >> (-"x" ==> (-"y" ==> (!!"y")))))

        Inl, (-"x" ==> (-"f" ==> (-"g" ==> (!!"f" >> !!"x"))))
        Inr, (-"y" ==> (-"f" ==> (-"g" ==> (!!"g" >> !!"y"))))
        Match, (-"u" ==> (-"f" ==> (-"g" ==> ((!!"u" >> !!"f") >> !!"g"))))
      ] |> List.map (fun (x,y) -> y,x))
  inverse |> Map.ofList,forward |> Map.ofList

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
    | Lambda(("f",_),Lambda(("g",_),Application(Var "f", t))) ->
      Some(Application(Inl, t))
    | Lambda(("f",_),Lambda(("g",_),Application(Var "g", t))) ->
      Some(Application(Inr, t))
    | Lambda(("s",_),Lambda(("z",_),t)) ->
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
