module TypeChecker

open CodeDefinitionImperative
open Coroutine

open CommonLatex

let typeFromName t =
  match t with
  | "void" -> VoidType
  | "bool" -> BoolType
  | "int" -> IntType
  | "float" -> FloatType
  | "string" -> StringType
  | _ -> ClassType t

let makeArrowType c m args t =
  let retT = if t = "" then ClassType c else typeFromName t
  let res = ArrowType(args |> List.map fst |> List.map typeFromName, retT)
  res

type TypeCheckingState<'code> = { Variables : List<Map<string, 'code>>; PC : int; GenericClasses : Map<string, List<string> * 'code>; Classes : Map<string, 'code>; Errors : List<string> }
  with 
    static member Zero : TypeCheckingState<'code> =
      { Variables = []; PC = 1; GenericClasses = Map.empty; Classes = Map.empty; Errors = [] }
    member this.AsSlideContent dots isHidden toCode toString =
      let varTable = 
        let vars = 
          match this.Variables with
          | [] -> 
            [Map.empty |> Map.add "PC" (toCode this.PC)]
          | v::vs ->
            (v |> Map.add "PC" (toCode this.PC)) :: vs
        let varFrames = 
          [
            for sf in vars do
            yield Runtime.printBindings toString isHidden sf 
          ] |> List.rev
        let varNamesByFrame = varFrames |> List.map fst
        let varValuesByFrame = varFrames |> List.map snd
        let varNames = varNamesByFrame |> List.reduce (fun a b -> a + " & & " + b)
        let varValues = varValuesByFrame |> List.reduce (fun a b -> a + " & & " + b)

        let hd = 
          [ 
            for sf in vars do
              yield [for v in sf do yield "c"]
          ] |> List.rev |> List.reduce (fun a b -> a @ (@">{\columncolor[gray]{0.8}}c" :: b))
        let varTableContent = sprintf "%s \\\\\n\\hline\n%s \\\\\n\\hline\n" varNames varValues
        sprintf "%s\n%s\n%s\n" (beginTabular hd) varTableContent endTabular

      let classes = 
        let inlineGenericArgs c_name (args,o) =
          //let args_suffix = sprintf "<%s>" (args |> List.reduce (fun a b -> a + ", " + b))
          c_name, o
        let allClasses = 
          [ for x in this.GenericClasses do yield inlineGenericArgs x.Key x.Value ] @ [ for x in this.Classes do yield x.Key,x.Value ] |> Map.ofList
        if allClasses |> Seq.filter (fun x -> isHidden x.Value |> not) |> Seq.isEmpty then ""
        else 
          let classesNames,classesValues = Runtime.printBindings toString isHidden allClasses
          let hd = classesNames |> Seq.map (fun _ -> "c") |> Seq.toList
          let classesTableContent = sprintf "%s \\\\\n\\hline\n%s \\\\\n\\hline\n" classesNames classesValues
          sprintf "%s\n%s\n%s" (beginTabular hd) classesTableContent endTabular
      varTable, classes



let rec lookupInClass (s:TypeCheckingState<Code>) c (vs:List<string>) =
  match s.Classes |> Map.tryFind c, s.GenericClasses |> Map.tryFind c with
  | Some(Object(ds)),_
  | Some(Hidden(Object(ds))),_
  | _,Some(_,Object(ds))
  | _,Some(_,Hidden(Object(ds))) ->
    match vs with
    | [] -> 
      failwith "Failed lookup on empty name"
    | v::[] ->
      ds.[v]
    | v::vs ->
      match ds.[v] with
      | ClassType(c) ->
        lookupInClass s c vs
      | _ ->
        failwith "Failed compound lookup on non-class object"
  | _ ->
    failwithf "Cannot find class definition for name %s" c
  

let lookup (s:TypeCheckingState<Code>) (v:string) =
  let vs = v.Split [|'.'|] |> Seq.toList
  match vs with
  | v::vs ->
    let rec loop ds = 
      match ds with
      | [] -> Option.None
      | d::ds ->
        match d |> Map.tryFind v with
        | Some y -> Some y
        | Option.None -> loop ds
    match loop s.Variables with
    | Some y when vs.IsEmpty ->
        y
    | Some(ClassType c) ->
      lookupInClass s c vs
    | _ ->
      match s.Classes |> Map.tryFind v,s.GenericClasses |> Map.tryFind v with
      | Some c,_ | _,Some (_,c) ->
        if vs.IsEmpty then
          c
        else
          failwith "Static lookup not yet implemented"
      | _ -> 
        failwithf "Malformed lookup of name %s" v
  | _ -> failwithf "Malformed lookup of name %s" v

let store (s:TypeCheckingState<Code>) (v:string) (y:Code) : TypeCheckingState<Code> =
  let rec loop ds = 
    match ds with
    | [] -> Option.None
    | d::ds ->
      match d |> Map.tryFind v with
      | Some _ -> 
        Some((d |> Map.add v y) :: ds)
      | Option.None -> 
        match loop ds with
        | Some ds' -> Some(d :: ds')
        | Option.None -> Option.None
  match loop s.Variables with
  | Some vs' ->
    { s with Variables = vs' }
  | Option.None ->
    match s.Variables with
    | [] ->
      { s with Variables = [Map.empty |> Map.add v y] }
    | x :: xs -> 
      { s with Variables = (x |> Map.add v y) :: xs }

let getPC : Coroutine<TypeCheckingState<Code>,int> =
  co{
    let! s = getState
    return s.PC
  }

let changePC f =
  co{
    let! s = getState
    do! setState { s with PC = f s.PC }
  }

let incrPC : Coroutine<TypeCheckingState<Code>,Unit> = changePC ((+) 1)

let rec typeCheck showMethodsTypeChecking pause addThisToMethodArgs consName toString numberOfLines (p:Code) : Coroutine<TypeCheckingState<Code>,Code> =
  let invisibleTypeCheck = typeCheck showMethodsTypeChecking (ret()) addThisToMethodArgs consName toString numberOfLines
  let typeCheck = typeCheck showMethodsTypeChecking pause addThisToMethodArgs consName toString numberOfLines
  co{
    match p with
    | Dots -> 
      return None
    | None -> 
      return None
    | Hidden c | Private c | Public c | Static c -> 
      return! typeCheck c
    | Ref _ as r ->
      return r
    | Var v -> 
      let! s = getState
      return lookup s v
    | ConstInt i ->
      return IntType
    | ConstFloat f ->
      return FloatType
    | ConstBool b ->
      return BoolType
    | ConstString s ->
      return StringType
    | Assign (v,e) ->
      return None
    | GenericTypedDecl(args,v,t,_) ->
      do! changeState 
            (fun s -> 
              if s.Variables.IsEmpty then
                { s with Variables = [Map.empty |> Map.add v (GenericClassType(t,args))] }
              else 
                { s with Variables = (s.Variables.Head |> Map.add v (GenericClassType(t,args))) :: s.Variables.Tail })
      return None
    | TypedDecl(v,t,Option.None) ->
      do! changeState 
            (fun s -> 
              if s.Variables.IsEmpty then
                { s with Variables = [Map.empty |> Map.add v (typeFromName t)] }
              else 
                { s with Variables = (s.Variables.Head |> Map.add v (typeFromName t)) :: s.Variables.Tail })
      return None
    | TypedDecl(v,t,Some y) ->
      // should type check the right-hand-side
      do! changeState 
            (fun s -> 
              if s.Variables.IsEmpty then
                { s with Variables = [Map.empty |> Map.add v (typeFromName t)] }
              else 
                { s with Variables = (s.Variables.Head |> Map.add v (typeFromName t)) :: s.Variables.Tail })
      return None
    | Sequence (ClassDef(name, body),k) ->
      let! _ = typeCheck (ClassDef(name, body))
      do! pause
      do! incrPC
      
      return! typeCheck k
    | Sequence (p,k) ->
      let! _ = typeCheck p
      do! incrPC
      do! pause
      return! typeCheck k
    | Op (a,op,b) -> 
      let! aVal = typeCheck a
      let! bVal = typeCheck b
      match op with
      | Plus | Times | Minus | DividedBy ->
        match aVal,bVal with
        | IntType, IntType ->
          return IntType
        | FloatType, FloatType ->
          return FloatType
        | IntType, FloatType ->
          return FloatType
        | FloatType, IntType ->
          return FloatType
        | StringType, StringType -> 
          match op with
          | Plus -> return StringType
          | _ -> return failwithf "Cannot perform %s %s %s" (toString a) op.AsPython (toString b)
        | _ -> return failwithf "Cannot perform %s %s %s" (toString a) op.AsPython (toString b)
      | GreaterThan ->
        match aVal,bVal with
        | IntType, IntType
        | FloatType, FloatType
        | IntType, FloatType
        | FloatType, IntType ->
          return BoolType
        | _ -> 
          return failwithf "Cannot perform %s %s %s" (toString a) op.AsPython (toString b)
      | _ -> 
        return failwithf "Invalid operation %s %s %s" (toString a) op.AsPython (toString b)
    | GenericInterfaceDef(args,n,m) ->
      let! res = typeCheck (InterfaceDef(n,m))
      do! changeState (fun s -> { s with Classes = s.Classes |> Map.remove n; 
                                         GenericClasses = s.GenericClasses |> Map.add n (args,s.Classes.[n]) })
      return res
    | InterfaceDef (n,ms) as intf ->
      let! pc = getPC
      let msValsByName = 
        [
          for m in ms do
            match m with
            | TypedSig(f,args,t) -> 
              let c = n
              let a = 1
              yield f,ArrowType(ClassType n :: (args |> List.map fst |> List.map typeFromName), typeFromName t)
            | _ -> ()
        ] |> Map.ofList
      do! changeState (fun s -> { s with Classes = (s.Classes |> Map.add n ((*Hidden*)(Object(msValsByName)))) })
      let nl = intf |> numberOfLines
      do! changePC ((+) (nl - 1))
      return None
    | Implementation i -> return None
    | GenericClassDef(args,n,m) ->
      let! res = typeCheck (ClassDef(n,m))
      do! changeState (fun s -> { s with Classes = s.Classes |> Map.remove n; 
                                         GenericClasses = s.GenericClasses |> Map.add n (args,s.Classes.[n]) })
      return res
    | ClassDef (n,ms) as cls ->
      let! pc = getPC
      let! s = getState
      let allMethods = ms |> List.filter (function Implementation _ -> false | Inheritance _ -> false | _ -> true)
      let allBaseMethods = 
        let baseClasses = 
          ms |> List.filter (function Inheritance _ -> true | _ -> false)
             |> List.map (function Inheritance i -> i,s.Classes.[i] | _ -> failwith "Malformed inheritance declaration.")
             |> List.map (function (i,Object(o)) -> [ for x in o |> Map.remove i do yield x.Key, x.Value ] | _ -> failwith "Malformed inheritance declaration.")
        baseClasses |> List.fold (@) []
      let allMethodsWithThis =
         allMethods |> List.map (fun f -> match f with 
                                          | TypedDef(m,args,t,b) | Public(TypedDef(m,args,t,b)) | Private(TypedDef(m,args,t,b)) -> 
                                            TypedDef(m,(n,"this") :: args,t,b)
                                          | Static(TypedDef(m,args,t,b)) | Static(Public(TypedDef(m,args,t,b))) | Static(Private(TypedDef(m,args,t,b))) -> 
                                            TypedDef(m,args,t,b)
                                          | _ -> f)
      let fields = ms |> List.filter (function TypedDecl(_) | Private(TypedDecl(_)) | Public(TypedDecl(_)) -> true | _ -> false) 
                      |> List.map (fun f -> match f with 
                                            | TypedDecl(n,t,_) | Public(TypedDecl(n,t,_)) | Private(TypedDecl(n,t,_)) -> n,typeFromName t
                                            | _ -> failwith "Malformed field declaration")
      let allMethodsUnchecked =
         allMethodsWithThis |> List.filter (function TypedDef(_) | Private(TypedDef(_)) | Public(TypedDef(_)) -> true | _ -> false) 
                            |> List.map (fun f -> match f with 
                                                  | TypedDef(m,args,t,b) -> 
                                                    m,makeArrowType n m args t
                                                  | _ -> failwith "Malformed method declaration")
      do! changeState (fun s -> { s with Classes = (s.Classes |> Map.add n ((*Hidden*)(Object((fields @ allMethodsUnchecked @ allBaseMethods) |> Map.ofList)))) })
      let! s = getState
      do! incrPC
      let rec typeCheckMethods ms = 
        co{
          match ms with
          | [] -> return []
          | m::ms ->
            match m with
            | TypedDef(m,args,t,b) as td -> 
              do! incrPC
              let! m_t = (if showMethodsTypeChecking then typeCheck else invisibleTypeCheck) td
              let! ms_t = typeCheckMethods ms
              return m_t :: ms_t
            | _ ->
              do! incrPC
              let! ms_t = typeCheckMethods ms
              return m :: ms_t
        }
      let! msVals = typeCheckMethods allMethodsWithThis
      let class_methods =
        [
          for m,m_orig in Seq.zip msVals allMethods do
            match m with
            | Assign(f,ArrowType(args,ret)) -> 
              match m_orig with
              | Static _ -> 
                yield f,ArrowType(args,ret)
              | _ ->
                yield f,ArrowType(args,ret)
            | _ -> ()
        ]
      let filtered_base_methods = //allBaseMethods 
        [for (m, code) in allBaseMethods do if class_methods |> List.exists(fun (m1, code1) -> m = m1) |> not then yield (m, code)]

      let msValsByName = fields @ class_methods @ filtered_base_methods |> Map.ofList
      do! changeState (fun s -> { s with Classes = (s.Classes |> Map.add n ((*Hidden*)(Object(msValsByName)))) })
      let nl = cls |> numberOfLines
      do! changePC (fun _ -> pc + (nl - 1))
      let! s = getState
      return None
    | TypedDef(f,args,t,body) -> 
      let! pc = getPC
      let nl = body |> numberOfLines
      let! s = getState
      let argsTyped = 
        [
          for t,n in args do
          yield typeFromName t, n
        ]
      let variablesWithArgs =
        argsTyped |> List.fold (fun vars (t,v) -> vars |> Map.add v t) Map.empty
      do! changeState (fun s -> { s with Variables = variablesWithArgs :: s.Variables })
      do! pause
      let! bodyT = typeCheck body
      do! changeState (fun s -> { s with Variables = s.Variables.Tail })
      do! changePC ((+) nl)
      let retT = if t = "" then typeFromName f else typeFromName t
      let res = Assign(f, ArrowType(argsTyped |> List.map fst, retT))
      do! if retT <> bodyT && t <> "" then
            changeState (fun s -> { s with Errors = "Return type mismatch" :: s.Errors})
          else
            ret()
      return res
    | New(c,argExprs) ->
      let! argTypes = argExprs |> mapCo typeCheck
      let! s = getState
      match s.Classes.[c] with
      | Hidden(Object(ms))
      | Object(ms) ->
        match ms.[c] with
        | ArrowType(argTypesExpected, retT) ->
          let localFrame = 
            [
              for a,i in Seq.zip argTypes [1..argTypes.Length] do
              yield "arg$_" + string(i) + "$", a
            ] |> Map.ofList
          do! changeState (fun s -> { s with Variables = localFrame :: s.Variables })
          if argTypes = argTypesExpected.Tail then
            do! pause
            do! changeState (fun s -> { s with Variables = (localFrame |> Map.add "ret" retT) :: s.Variables.Tail })
            do! pause
            do! changeState (fun s -> { s with Variables = s.Variables.Tail })
            return retT
          else
            return failwithf "Incompatible types %A and %A" argTypes argTypesExpected
        | _ -> return failwith ""
      | _ -> return failwith ""
    | Return e ->
      let! res = typeCheck e
      do! changeState 
            (fun s -> 
              match s.Variables with
              | [] -> { s with Variables = (s.Variables.Head |> Map.add "ret" res) :: [] }
              | v::vs -> { s with Variables = (v |> Map.add "ret" res) :: vs } )
      return res
    | If(c,t,e) ->
      let! cVal = typeCheck c
      match cVal with
      | BoolType ->
        do! changeState (fun s -> { s with Variables = Map.empty :: s.Variables })
        let! resT = typeCheck (Sequence(End,t))
        do! changeState (fun s -> { s with Variables = s.Variables.Tail })
        do! incrPC
        do! pause
        do! changeState (fun s -> { s with Variables = Map.empty :: s.Variables })
        let! resE = typeCheck (Sequence(End,e))
        do! changeState (fun s -> { s with Variables = s.Variables.Tail })
        match resT, resE with
        | VoidType, VoidType -> return VoidType
        | VoidType,t | t,VoidType -> return t
        | t1,t2 -> 
          return failwithf "Incompatible if-branches returning %s and %s" (t1.AsCSharp "") (t2.AsCSharp "")
      | _ -> return failwith "Malformed if"
    | StaticMethodCall("Console","WriteLine",[arg]) ->
      let! argType = typeCheck arg
      return VoidType
//      match argType with
//      | StringType -> return VoidType
//      | _ -> return failwithf "Wrong argument type %s for console.writeline" (argType.AsCSharp "")
    | StaticMethodCall("Math","Sqrt",[arg]) ->
      return FloatType
    | StaticMethodCall("Console","ReadLine",[]) ->
      return StringType
    | StaticMethodCall("Int32","Parse",[i]) ->
      let! iType = typeCheck i
      match iType with
      | StringType -> return IntType
      | _ -> return failwithf "Wrong argument type %s for int.parse" (iType.AsCSharp "")
    | MethodCall(v,m,argExprs) ->
      let! argTypes = argExprs |> mapCo typeCheck
      let! s = getState
      match lookup s v with
      | ClassType c ->
        match s.Classes.[c] with
        | Hidden(Object(ms))
        | Object(ms) ->
          match ms.[m] with
          | ArrowType(argTypesExpected, retT) ->
            let localFrame = 
              [
                yield "ret", None
                yield "this", ClassType c
                for a,i in Seq.zip argTypes [1..argTypes.Length] do
                yield "arg$_" + string(i) + "$", a
              ] |> Map.ofList
            do! changeState (fun s -> { s with Variables = localFrame :: s.Variables })
            if argTypes = argTypesExpected.Tail then
              do! pause
              do! changeState (fun s -> { s with Variables = (localFrame |> Map.add "ret" retT) :: s.Variables.Tail })
              do! pause
              do! changeState (fun s -> { s with Variables = s.Variables.Tail })
              return retT
            else
              return failwithf "Incompatible types %A and %A" argTypes argTypesExpected
          | _ -> return failwith ""
        | _ -> return failwith ""
      | _ -> return failwith ""
    | StaticMethodCall(c,m,argExprs) ->
      let! argTypes = argExprs |> mapCo typeCheck
      let! s = getState
      match s.Classes.[c] with
      | Hidden(Object(ms))
      | Object(ms) ->
        match ms.[m] with
        | ArrowType(argTypesExpected, retT) ->
          let localFrame = 
            [
              yield "ret", None
              for a,i in Seq.zip argTypes [1..argTypes.Length] do
              yield "arg$_" + string(i) + "$", a
            ] |> Map.ofList
          do! changeState (fun s -> { s with Variables = localFrame :: s.Variables })
          if argTypes = argTypesExpected then
            do! pause
            do! changeState (fun s -> { s with Variables = (localFrame |> Map.add "ret" retT) :: s.Variables.Tail })
            do! pause
            do! changeState (fun s -> { s with Variables = s.Variables.Tail })
            return retT
          else
            return failwithf "Incompatible types %A and %A" argTypes argTypesExpected
        | _ -> return failwith ""
      | _ -> return failwith ""
    | End -> return None
//    | Call(f,argExprs) ->
//      let! argVals = argExprs |> mapCo interpret
//      let! s = getState
//      match s.Heap.[f] with
//      | Hidden(ConstLambda(pc,argNames,body))
//      | ConstLambda(pc,argNames,body) ->
//        let c = Seq.zip argNames argVals |> Map.ofSeq |> Map.add "PC" (ConstInt pc) |> Map.add "ret" None
//        do! setState { s with Stack = c :: s.Stack }
//        do! pause
//        return! typeCheck body
//      | _ -> return failwithf "Cannot find function %s" f            
//    | ToString(v) ->
//      let! v_val = typeCheck v
//      match v_val with
//      | ConstInt x -> return ConstString(x.ToString())
//      | ConstBool x -> return ConstString(x.ToString())
//      | ConstFloat x -> return ConstString(x.ToString())
//      | ConstString x -> return ConstString(x)
//      | _ -> return failwith "ToString() on objects is not yet implemented."
//    | While(c,body) ->
//      let! cVal = interpret c
//      let body_nl = body |> numberOfLines
//      match cVal with
//      | ConstBool true ->
//        let! res = interpret (Sequence(End,body))
//        do! changePC (fun pc -> pc - body_nl)
//        do! pause
//        return! interpret(While(c,body))
//      | ConstBool false ->
//        do! changePC ((+) ((body_nl) + 1))
//        return None
//      | _ -> return failwith "Malformed if"
//    | MainCall ->
//      return! typeCheck (StaticMethodCall("Program","Main",[None]))
    | c -> return failwithf "Unsupported construct %A" c
  }


let typeCheckCSharp showMethodsTypeChecking p = typeCheck showMethodsTypeChecking pause (fun c args -> "this" :: args) id (fun (c:Code) -> c.AsCSharp "") (fun (c:Code) -> c.NumberOfCSharpLines) p
