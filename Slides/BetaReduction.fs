module BetaReduction

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

let rec reduce maxSteps expandInsideLambda showArithmetics showControlFlow showLet showPairs showUnions p = 
  let rec reduce maxSteps on_lambda p : Coroutine<(Term -> Term) * Term, bool> =
    let rec reduce_lambda x f =
      co{
        let! (k,t) = getState
        do! setState ((fun f -> k(Lambda(x,f))), f)
        let! replacedT = reduce_step reduce_lambda p
        let! (k1,f_new) = getState
        do! setState (k, Lambda(x,f_new))
        return replacedT
      }
    and reduce_step on_lambda p = 
      co{
        if maxSteps <= 0 then
          return false
        else
          let! (k,t) = getState
          match t with
          | Hidden t ->
            do! setState((fun t -> k t), t)
            let! res = reduce_step on_lambda  p
            let! (_,t) = getState
            do! setState(k, t)
            return res
          | Highlighted(t,h) ->
            do! setState((fun t -> k t), t)
            let! res = reduce_step on_lambda  p
            let! (_,t) = getState
            do! setState((fun t -> k(Highlighted(t,h))), t)
            return res
          | Lambda(x,f) -> 
            return! on_lambda x f
          | Application(Lambda(x,f),u) ->
              do! setState ((fun u -> k(Application(Lambda(x,f),u))), u)
              let! replaced = reduce (maxSteps - 1) on_lambda p
              let! (k1,v) = getState
              do! setState ((fun v -> k(Highlighted(Application(Lambda(x,f),v),Underlined))), v)
              do! p
              let f_new = replace f (fst x) (Highlighted(v,Colored))
              do! setState (k,f_new)
              do! p
              let f_new = replace f (fst x) v
              do! setState (k,f_new)
              do! p
              return true
          | Application(Var x,u) -> 
            return false
          | Application(Application(Application(If,True),t),e) as _if when not showControlFlow ->
            do! setState ((fun v -> k(Highlighted(v,Underlined))), _if)
            do! p
            do! setState (k, Highlighted(t,Colored))
            do! p
            do! setState (k, t)
            do! p
            return true
          | Application(Application(Application(If,False),t),e) as _if when not showControlFlow ->
            do! setState ((fun v -> k(Highlighted(v,Underlined))), _if)
            do! p
            do! setState (k, Highlighted(e,Colored))
            do! p
            do! setState (k, e)
            do! p
            return true
          | Application(Application(Application(If,c),t),e) as _if when not showControlFlow ->
            do! setState ((fun c -> k(Application(Application(Application(If,c),t),e))), c)
            let! replacedC = reduce_step on_lambda p
            let! (k1,c_new) = getState
            do! setState (k, Application(Application(Application(If,c_new),t),e))
            return replacedC
          | If when not showControlFlow ->
            return false
          | Application(Application(And,True),True) as a when not showArithmetics ->
            do! setState ((fun v -> k(Highlighted(v,Underlined))), a)
            do! p
            do! setState (k, Highlighted(True,Colored))
            do! p
            do! setState (k, True)
            do! p
            return true
          | Application(Application(And,True),False) as a when not showArithmetics ->
            do! setState ((fun v -> k(Highlighted(v,Underlined))), a)
            do! p
            do! setState (k, Highlighted(False,Colored))
            do! p
            do! setState (k, False)
            do! p
            return true
          | Application(Application(And,False),True) as a when not showArithmetics ->
            do! setState ((fun v -> k(Highlighted(v,Underlined))), a)
            do! p
            do! setState (k, Highlighted(False,Colored))
            do! p
            do! setState (k, False)
            do! p
            return true
          | Application(Application(And,False),False) as a when not showArithmetics ->
            do! setState ((fun v -> k(Highlighted(v,Underlined))), a)
            do! p
            do! setState (k, Highlighted(False,Colored))
            do! p
            do! setState (k, False)
            do! p
            return true
          | Application(IsZero,ConstInt(i)) as a when not showArithmetics ->
            do! setState ((fun v -> k(Highlighted(v,Underlined))), a)
            do! p
            do! setState (k, Highlighted((if i = 0 then True else False),Colored))
            do! p
            do! setState (k, if i = 0 then True else False)
            do! p
            return true
          | Application(Application(Plus,ConstInt(i)),ConstInt(j)) as a when not showArithmetics ->
            do! setState ((fun v -> k(Highlighted(v,Underlined))), a)
            do! p
            do! setState (k, Highlighted(Var((i+j).ToString()),Colored))
            do! p
            do! setState (k, Var((i+j).ToString()))
            do! p
            return true
          | Application(Application(Minus,ConstInt(i)),ConstInt(j)) as a when not showArithmetics ->
            do! setState ((fun v -> k(Highlighted(v,Underlined))), a)
            do! p
            do! setState (k, Highlighted(Var((i-j).ToString()),Colored))
            do! p
            do! setState (k, Var((i-j).ToString()))
            do! p
            return true
          | Application(Application(Mult,ConstInt(i)),ConstInt(j)) as a when not showArithmetics ->
            do! setState ((fun v -> k(Highlighted(v,Underlined))), a)
            do! p
            do! setState (k, Highlighted(Var((i*j).ToString()),Colored))
            do! p
            do! setState (k, Var((i*j).ToString()))
            do! p
            return true
          | Application(Application(Mult,t),u) as a when not showArithmetics ->
            do! setState ((fun t -> k(Application(Application(Mult,t),u))), t)
            let! replacedT = reduce_step on_lambda p
            let! (k1,t_new) = getState
            do! setState ((fun u -> k(Application(Application(Mult,t),u))), u)
            let! replacedU = reduce_step on_lambda p
            let! (k2,u_new) = getState
            do! setState (k, Application(Application(Mult,t_new),u_new))
            return replacedT || replacedU
          | Application(Application(MakePair,t),u) as a when not showPairs ->
            do! setState ((fun t -> k(Application(Application(MakePair,t),u))), t)
            let! replacedT = reduce_step on_lambda p
            let! (k1,t_new) = getState
            do! setState ((fun u -> k(Application(Application(MakePair,t_new),u))), u)
            let! replacedU = reduce_step on_lambda p
            let! (k2,u_new) = getState
            do! setState (k, Application(Application(MakePair,t_new),u_new))
            return replacedT || replacedU
          | Application(First, Application(Application(MakePair,t),u)) when not showPairs ->
            do! setState ((fun a -> k(Highlighted(Application(First,a),Underlined))), Application(Application(MakePair,t),u))
            do! p
            let! replacedA = reduce_step on_lambda p
            let! (k1,a_new) = getState
            match a_new with
            | Application(Application(MakePair,t_new),u_new) ->
              do! setState ((fun t -> k(t)), Highlighted(t_new,Colored))
              do! p
              do! setState ((fun t -> k(t)), t_new)
              do! p
              return replacedA || true
            | _ ->
              return failwith "Malformed pair evaluation"
          | Application(Second, Application(Application(MakePair,t),u)) when not showPairs ->
            do! setState ((fun a -> k(Highlighted(Application(Second,a),Underlined))), Application(Application(MakePair,t),u))
            do! p
            let! replacedA = reduce_step on_lambda p
            let! (k1,a_new) = getState
            match a_new with
            | Application(Application(MakePair,t_new),u_new) ->
              do! setState ((fun t -> k(t)), Highlighted(u_new,Colored))
              do! p
              do! setState ((fun t -> k(t)), u_new)
              do! p
              return replacedA || true
            | _ ->
              return failwith "Malformed pair evaluation"
          | Application(Application(Application(Match, Application(Inl,t)), f), g) when not showUnions ->
            do! setState ((fun t -> k(Application(Application(Highlighted(Application(Match, Application(Inl,t)),Underlined), f), g))), t)
            do! p
            do! setState ((fun t -> k(Application(f, t))), Highlighted(t,Colored))
            do! p
            do! setState ((fun t -> k(Application(f, t))), t)
            do! p
            let! replacedF = reduce_step on_lambda p
            return replacedF || true
          | Application(Application(Application(Match, Application(Inr,t)), f), g) when not showUnions ->
            do! setState ((fun t -> k(Application(Application(Highlighted(Application(Match, Application(Inr,t)),Underlined), f), g))), t)
            do! p
            do! setState ((fun t -> k(Application(g, t))), Highlighted(t,Colored))
            do! p
            do! setState ((fun t -> k(Application(g, t))), t)
            do! p
            let! replacedF = reduce_step on_lambda p
            return replacedF || true
          | Application(Application(Application(Match, t), f), g) when not showUnions ->
            do! setState ((fun t -> k(Application(Application(Application(Match, t), f), g))), t)
            let! replacedT = reduce_step on_lambda p
            let! (k1,t_new) = getState
            do! setState (k, Application(Application(Application(Match, t_new), f), g))
            let! replacedTNew = reduce_step on_lambda p
            return replacedT || replacedTNew
          | Inl when not showUnions ->
            return false
          | Inr when not showUnions ->
            return false
          | Let(x,t,u) as l when not showLet ->
            do! setState ((fun t -> k(Let(x,t,u))), t)
            let! replacedT = reduce (maxSteps-1) on_lambda p
            let! (k1,t_new) = getState
            //do! if not replacedT then setState ((fun t -> k(Highlighted(Let(x,t,u),Underlined))), t_new) >> p else ret ()
            let u_new = replace u (fst x) (Highlighted(t_new,Colored))
            do! setState ((fun u -> k(u)), u_new)
            do! p
            let u_new = replace u (fst x) t_new
            do! setState ((fun u -> k(u)), u_new)
            do! p
            let! replacedU = reduce_step on_lambda p
            do! if replacedU then p else ret()              
            return replacedT || replacedU
          | Application(Fix,Lambda(f,t)) as fix ->
            do! setState ((fun f -> k(Highlighted(Application(Fix,f),Underlined))), Lambda(f,t))
            do! p
            let t_new = replace t (fst f) (Highlighted(Hidden fix,Colored))
            do! setState (k, t_new)
            do! p
            let t_new = replace t (fst f) (Hidden fix)
            do! setState (k, t_new)
            do! p
            let! replacedF = reduce_step on_lambda p
            return replacedF
          | And when not showArithmetics ->
            return false
          | True when not showArithmetics ->
            return false
          | False when not showArithmetics ->
            return false
          | ConstInt(i) when not showArithmetics ->
            return false
          | TypeLambda(a,t) ->
            do! setState (k, t)
            let! replacedT = reduce_step on_lambda p
            let! (k1,t_new) = getState
            do! setState (k,t_new)
            return replacedT
          | TypeApplication(t,a) ->
            do! setState (k, t)
            let! replacedT = reduce_step on_lambda p
            let! (k1,t_new) = getState
            do! setState (k,t_new)
            return replacedT
          | Application(t,u) ->
            do! setState ((fun t -> k(Application(t,u))), t)
            let! replacedT = reduce_step on_lambda p
            let! (k1,t_new) = getState
            do! setState ((fun u -> k(Application(t_new,u))), u)
            let! replacedU = reduce_step on_lambda p
            let! (k2,u_new) = getState
            do! setState (k, Application(t_new,u_new))
            return replacedT || replacedU
          | Var x as t -> 
            match deltaRules t with
            | Some t' ->
              do! setState (k, Highlighted(t,Underlined))
              do! p
              do! setState (k, Highlighted(t',Colored))
              do! p
              do! setState (k, t')
              do! p
              return true
            | _ ->
              return false
          | t ->
            match deltaRules t with
            | Some t' ->
              do! setState (k, Highlighted(t,Underlined))
              do! p
              do! setState (k, Highlighted(t',Colored))
              do! p
              do! setState (k, t')
              do! p
              return true
            | _ ->
              return false
      }
    co{
      let! replaced = reduce_step on_lambda p
      if replaced then
        return! reduce (maxSteps-1) on_lambda p
      else
        let! replaced = reduce_step (if expandInsideLambda then reduce_lambda else (fun _ _ -> ret false)) p
        if replaced then 
          return! reduce (maxSteps-1) on_lambda p
        else
          let! (k,t) = getState
          match inverseDeltaRules t with
          | Some t' ->
            do! setState (k, Highlighted(t,Underlined))
            do! p
            do! setState (k, Highlighted(t',Colored))
            do! p
            do! setState (k, t')
            do! p
            return false
          | _ ->
            return false
    }
  reduce maxSteps (fun _ _ -> ret false) p

and replace (t:Term) (x:string) u = t.replace x u
