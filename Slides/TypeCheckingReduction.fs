module TypeCheckingReduction

open CodeDefinitionLambda
open CommonLatex
open Coroutine

let (|ConstInt|_|) =
  function
  | Var x ->
    match System.Int32.TryParse(x) with
    | (true,i) -> Some i
    | _ -> None
  | _ ->
    None

let rec reduceType p : Coroutine<_,Unit> =
  co{
    do! 
      co{
        let! (k,t) = getState
        match t with
        | Type(Type.Application(t,u)) ->
          do! setState ((fun t -> k(Application(t,Type(u)))), Type t)
          do! reduceType p
          let! (k1,t_t) = getState
          do! setState ((fun u -> k(Application(t_t,u))), Type u)
          let! (k2,u_t) = getState
          do! reduceType p
          do! setState (k, Application(t_t,u_t))
          do! reduce p
          return()
        | _ ->
          return()
      }
    let! (k,t) = getState
    match t with
    | Type t ->
      match defaultTypes |> Map.tryFind t with
      | Some t' ->
        do! setState (k, Highlighted(Type t,Underlined))
        do! p
        do! setState (k, Highlighted(Type t',Colored))
        do! p
        do! setState (k, Type t')
        do! p
        return ()
      | _ ->
        match invDefaultTypes |> Map.tryFind t with
        | Some t' ->
          do! setState (k, Highlighted(Type t,Underlined))
          do! p
          do! setState (k, Highlighted(Type t',Colored))
          do! p
          do! setState (k, Type t')
          do! p
          return ()
        | _ ->
          return ()
    | _ ->
      return failwith "Unexpected term."
  }

and reduce (p:Coroutine<_,Unit>) : Coroutine<_,Unit> = 
  let rec reduce p = 
    let rec reduce_step p = 
      co{
          let! (k,(t:Term)) = getState
          match t with
          | Type t -> 
            do! reduceType p
            let! (k,t) = getState
            return ()
          | Lambda(x,f) -> 
            do! setState ((fun f -> k(Highlighted(Lambda(x,f),Underlined))), f)
            do! p
            let f_h = f.typeReplace (fst x) (Highlighted(Type(snd x),Colored))
            do! setState ((fun f -> k(Lambda(x,f))), f_h)
            do! p
            let f_h = f.typeReplace (fst x) (Type(snd x))
            do! setState ((fun f -> k(Lambda(x,f))), f_h)
            do! p
            do! reduce p
            let! (k1,f_t) = getState
            match f_t with
            | Type f_t ->
              do! setState ((fun f -> k(Highlighted(Lambda(x,f),Underlined))), Type(f_t))
              do! p
              do! setState (k, Highlighted(Type(Arrow(snd x,f_t)),Colored))
              do! p
              do! setState (k, Type(Arrow(snd x,f_t)))
              do! p
              return ()
//            | f_t when f_t <> f_h ->
//              do! reduce p
//              return ()
            | f_t ->
              return failwith "Unsupported type checking construct"
          | TypeLambda(a,f) -> 
            do! setState ((fun f -> k(TypeLambda(a,f))), f)
            do! reduce p
            let! (k1,f_t) = getState
            match f_t with
            | Type f_t ->
              do! setState ((fun f -> k(Highlighted(TypeLambda(a,f),Underlined))), Type(f_t))
              do! p
              do! setState (k, Highlighted(Type(Forall(a,f_t)),Colored))
              do! p
              do! setState (k, Type(Forall(a,f_t)))
              do! p
              return ()
//            | f_t when f_t <> f ->
//              do! reduce p
//              return ()
            | f_t ->
              return failwith "Unsupported type checking construct"
          | TypeApplication(t,u) ->
            do! setState (k, Application(t,Type(u)))
            do! reduce p
            return ()
          | Application(Type(Forall(a,f)),Type(u)) ->
            do! setState (k, Highlighted(Application(Type(Forall(a,f)),Type(u)),Underlined))
            do! p
            let f_new = f.replace a u
            do! setState (k,Highlighted(Type f_new,Colored))
            do! p
            do! setState (k,Type f_new)
            do! p
            do! reduce p
            return ()
          | Application(Type(Arrow(a,b)),Type(a1)) when a = a1 ->
            do! setState (k, Highlighted(Application(Type(Arrow(a,b)),Type(a1)),Underlined))
            do! p
            do! setState (k, Highlighted(Type(b),Colored))
            do! p
            do! setState (k, Type(b))
            do! p
            do! reduce p
            return ()
          | Application(t,u) ->
  //          do! setState ((fun t -> k(Highlighted(Application(t,u)))), t)
  //          do! p
            do! setState ((fun t -> k(Application(t,u))), t)
            do! reduce p
            let! (k1,t_t) = getState
            do! setState ((fun u -> k(Application(t_t,u))), u)
            do! reduce p
            let! (k2,u_t) = getState
            do! setState (k, Application(t_t,u_t))
  //          do! p
            do! reduce p
            return ()
          | t ->
            match deltaRules t with
            | Some t' ->
              do! setState (k, Highlighted(t,Underlined))
              do! p
              do! setState (k, Highlighted(t',Colored))
              do! p
              do! setState (k, t')
              do! p
              return ()
            | _ ->
              return failwith "Unsupported type checking construct"
  //        | Hidden t ->
  //          do! setState((fun t -> k t), t)
  //          let! res = reduce_step p
  //          let! (_,t) = getState
  //          do! setState(k, t)
  //          return res
  //        | Highlighted t ->
  //          do! setState((fun t -> k t), t)
  //          let! res = reduce_step p
  //          let! (_,t) = getState
  //          do! setState((fun t -> k(Highlighted(t))), t)
  //          return res
  //        | Application(Lambda(x,f),u) ->
  //            do! setState ((fun u -> k(Application(Lambda(x,f),u))), u)
  //            let! replaced = reduce p
  //            let! (k1,v) = getState
  //            do! setState ((fun v -> k(Highlighted(Application(Lambda(x,f),v)))), v)
  //            do! p
  //            let f_new = typeReplace f (fst x) v
  //            do! setState (k,f_new)
  //            do! p
  //            return true
  //        | Application(Var x,u) -> 
  //          return false
  //        | Application(t,u) ->
  //          do! setState ((fun t -> k(Application(t,u))), t)
  //          let! replacedT = reduce_step p
  //          let! (k1,t_new) = getState
  //          do! setState ((fun u -> k(Application(t_new,u))), u)
  //          let! replacedU = reduce_step p
  //          let! (k2,u_new) = getState
  //          do! setState (k, Application(t_new,u_new))
  //          return replacedT || replacedU
      }
    reduce_step p

  co{
    do! reduce p
    let! (k,t) = getState
    match t with
    | Type t ->
      match invDefaultTypes |> Map.tryFind t with
      | Some t' ->
        do! setState (k, Highlighted(Type t,Underlined))
        do! p
        do! setState (k, Highlighted(Type t',Colored))
        do! p
        do! setState (k, Type t')
        do! p
        return ()
      | _ ->
        return ()
    | _ ->
      return ()
  }
