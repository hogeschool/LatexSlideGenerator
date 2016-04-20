module CodeDefinitionImperative

open Coroutine
open CommonLatex

type Operator = Plus | Minus | Times | DividedBy | GreaterThan | Equals
  with
    member this.AsPython =
      match this with
      | Plus -> "+"
      | Minus -> "-"
      | Times -> "*"
      | DividedBy -> "//"
      | GreaterThan -> ">"
      | Equals -> "=="
    member this.AsCSharp =
      match this with
      | DividedBy -> "/"
      | _ -> this.AsPython
    member this.AsJava = this.AsCSharp

let toJavaType =
  function
  | "bool" -> "boolean"
  | "string" -> "String"
  | t -> t

let toTypeAsArgument =
  function
  | "int" -> "Integer"
  | "bool" -> "Boolean"
  | "float" -> "Float"
  | t -> t |> toJavaType

let (!+) = List.fold (+) ""

type UML = UMLItem list
and UMLItem =
  | Package of string * UMLItem list
  | Interface of string * float * float * float * UMLItem list// name * name width * pos_x * pos_y * operations
  | Operation of string * string list * Option<string> //methodname * args * ret_type
  | Class of string * float * float * Option<string> * UMLItem list * UMLItem list // name * pos_x * pos_y * implements * attributes * operations
  | Attribute of string * string // Position * Point 
  | Arrow of string * string * string // from * message * to
  | Aggregation of string * string * int * string // from * message * to
  member this.ToStringAsElement() =
    match this with
    | Package(name, items) -> 
      let items = items |> List.fold(fun s e -> s + "\n" + e.ToStringAsElement()) ""
      (@"\begin{package}{" + name + "}") + items + ("\n\end{package}")
    | Interface(name, text_size, pos_x, pos_y, operations) -> // name * name width * pos_x * pos_y * operations
      let items = operations |> List.fold(fun s e -> s + "\n" + e.ToStringAsElement()) ""
      (@"\begin{interface}[text width=" + (string) text_size + "cm]{" + name + "}{"+string pos_x+","+string pos_y+"}") + items + ("\n\end{interface}")
    | Attribute(name, _type) -> "\attribute{" + name + " : " + _type + "}"
    | Arrow(from, name, _to) ->
      @"\draw[umlcd style dashed line ,->] (" + from + ")  --node[above , sloped , black]{" + name + "} (" + _to + ");"
    | Aggregation(from, name, amount, _to) ->
      @"\aggregation{" + from + "}{" + name + "}{" + string amount + "}{" + _to + "}"
    | Operation(name, args, ret_type) ->
      let args = if args.Length > 1 then args.Tail |> List.fold(fun s e -> s + ", " + e) args.Head
                 else ""
      let ret_type = match ret_type with  | None -> "" | Some ret -> " : " + ret
      @"\operation{" + name + "(" + args + ") " + ret_type + "}"
    | Class (name, pos_x, pos_y, implements, attributes, operations) -> // name * pos_x * pos_y * implements * attributes * operations
      let items = operations |> List.fold(fun s e -> s + " \n " + e.ToStringAsElement()) ""
      let implements = match implements with | None -> "" | Some entity -> "\implement{" + entity + "}"
      (@"\begin{class}{" + name + "}{" + string pos_x + "," + string pos_y + "}" + implements + " ") + items + ("\n\end{class}")
  
type Code =
  | Static of Code
  | Public of Code
  | Private of Code
  | Dots
  | End
  | ToString of Code
  | None
  | Ref of string
  | Object of Map<string, Code>
  | Array of Map<int,Code>
  | New of string * List<Code>
  | GenericNew of string * List<string> * List<Code>
  | NewArray of string * int
  | Implementation of string
  | Inheritance of string
  | GenericInterfaceDef of List<string> * string * List<Code>
  | InterfaceDef of string * List<Code>
  | ClassDef of string * List<Code>
  | GenericClassDef of List<string> * string * List<Code>
  | GenericLambdaFuncDecl of i_t:string * o_t:string * v_name:string * arg_name:string * body:Code
  | GenericLambdaFuncCall of v_name:string * args:List<Code>
  | Return of Code
  | TypedDecl of string * string * Option<Code>
  | GenericTypedDecl of List<string> * string * string * Option<Code>
  | ArrayDecl of string * string * Option<Code>
  | ArraySet of string * int * Code
  | ArrayGet of string * int
  | Var of string
  | Hidden of Code
  | ConstLambda of int * List<string> * Code
  | ConstBool of bool
  | ConstInt of int
  | ConstFloat of float
  | ConstString of string
  | IntType | FloatType | StringType | BoolType | VoidType
  | ClassType of string
  | GenericClassType of string * List<string>
  | ArrowType of List<Code> * Code
  | Assign of string * Code
  | TypedDef of string * List<string * string> * string * Code
  | TypedSig of string * List<string * string> * string
  | Def of string * List<string> * Code
  | Call of string * List<Code>
  | MainCall
  | MethodCall of string * string * List<Code>
  | StaticMethodCall of string * string * List<Code>
  | If of Code * Code * Code
  | IfThen of Code * Code
  | While of Code * Code
  | Op of Code * Operator * Code
  | Sequence of Code * Code
  | InlineSequence of Code * Code
  with 
    member this.AsPython pre = 
      match this with
      | Object bs ->
        let argss = bs |> Seq.map (fun a -> a.Key.Replace("__", "\_\_") + "=" + (a.Value.AsPython "") + ", ") |> Seq.toList
        sprintf "%s%s" pre ((!+argss).TrimEnd[|','; ' '|])
      | End -> ""
      | None -> "None"
      | ClassDef(s,ms) -> 
        let mss = ms |> List.map (fun m -> m.AsPython (pre + "  "))
        sprintf "class %s:\n%s" s ((!+mss).Replace("\n\n", "\n"))
      | Return c ->
        sprintf "%sreturn %s\n" pre ((c.AsPython "").Replace("\n",""))
      | Var s -> s
      | Dots -> "...\n"
      | ConstBool b -> b.ToString()
      | ConstInt i -> i.ToString()
      | ConstFloat f -> f.ToString()
      | ConstString s -> sprintf "\"%s\"" s
      | Ref s -> sprintf "ref %s" s
      | Assign (v,c) -> sprintf "%s%s = %s\n" pre v ((c.AsPython "").TrimEnd([|'\n'|]))
      | ConstLambda (pc,args,body) ->
        let argss = args |> List.map (fun a -> a + ",")
        sprintf "%slambda(%s): %s" pre ((!+argss).TrimEnd[|','|]) (body.AsPython (pre + "  "))
      | Def (n,args,body) ->
        let argss = args |> List.map (fun a -> a + ",")
        sprintf "%sdef %s(%s):\n%s" pre n ((!+argss).TrimEnd[|','|]) (body.AsPython (pre + "  "))
      | New(c,args) ->
        let argss = args |> List.map (fun a -> (a.AsPython "").TrimEnd([|'\n'|]) + ",")
        sprintf "%s%s(%s)\n" pre c ((!+argss).TrimEnd[|','|])
      | Call(n,args) ->
        let argss = args |> List.map (fun a -> (a.AsPython "").TrimEnd([|'\n'|]) + ",")
        sprintf "%s%s(%s)\n" pre n ((!+argss).TrimEnd[|','|])
      | MethodCall(n,m,args) ->
        let argss = args |> List.map (fun a -> (a.AsPython "").TrimEnd([|'\n'|]) + ",")
        sprintf "%s%s.%s(%s)\n" pre n m ((!+argss).TrimEnd[|','|])
      | StaticMethodCall(c,m,args) ->
        let argss = args |> List.map (fun a -> (a.AsPython "").TrimEnd([|'\n'|]) + ",")
        sprintf "%s%s.%s(%s)\n" pre c m ((!+argss).TrimEnd[|','|])
      | If(c,t,e) ->
        let tS = (t.AsPython (pre + "  "))
        sprintf "%sif %s:\n%s%selse:\n%s" pre ((c.AsPython "").TrimEnd([|'\n'|])) tS pre (e.AsPython (pre + "  "))
      | IfThen(c,t) ->
        let tS = (t.AsPython (pre + "  "))
        sprintf "%sif %s:\n%s" pre ((c.AsPython "").TrimEnd([|'\n'|])) tS
      | While(c,b) ->
        let bs = (b.AsPython (pre + "  "))
        sprintf "%swhile %s:\n%s" pre (c.AsPython "") bs
      | Op(a,op,b) ->
        sprintf "(%s %s %s)" ((a.AsPython "").Replace("\n","")) (op.AsPython) ((b.AsPython (pre + "  ")).Replace("\n",""))
      | Sequence (p,q) ->
        let res = sprintf "%s%s" (p.AsPython pre) (q.AsPython pre)
        res
      | Hidden(_) -> ""
      | s -> failwithf "Unsupported Python statement %A" s
    member this.NumberOfPythonLines = 
      let code = ((this.AsPython ""):string).TrimEnd([|'\n'|])
      let lines = code.Split([|'\n'|])
      lines.Length

    member this.AsJava pre =
      match this with
      | Private p ->
        (sprintf "%sprivate%s" pre (p.AsJava pre)).Replace("private" + pre, "private ")
      | Static p ->
        (sprintf "%sstatic%s" pre (p.AsJava pre)).Replace("static" + pre, "static ")
      | Public p ->
        (sprintf "%spublic%s" pre (p.AsJava pre)).Replace("public" + pre, "public ")
      | ToString p ->
        (sprintf "%s%s.toString()" pre (p.AsJava ""))
      | Object bs ->
        let argss = bs |> Seq.map (fun a -> a.Key.Replace("__", "\_\_") + "=" + (a.Value.AsJava "") + ", ") |> Seq.toList
        sprintf "%s%s" pre ((!+argss).TrimEnd[|','; ' '|])
      | MainCall -> ""
      | End -> ""
      | None -> "null"
      | Dots -> "...\n"
      | Implementation i | Inheritance i -> ""
      | GenericInterfaceDef(args,s,ms) ->
        let args_suffix = sprintf "<%s>" (args |> List.reduce (fun a b -> a + ", " + b))
        InterfaceDef(s + args_suffix,ms).AsJava pre
      | InterfaceDef(s,ms) ->
        let mss = ms |> List.map (fun m -> m.AsJava (pre + "  "))
        let res = sprintf "interface %s {\n%s%s}\n" s (!+mss) pre
        res        
      | GenericClassDef(args,s,ms) ->
        let args_suffix = sprintf "<%s>" (args |> List.reduce (fun a b -> a + ", " + b))
        ClassDef(s + args_suffix,ms).AsJava pre
      | ClassDef(s,ms) -> 
        let mss = ms |> List.map (fun m -> m.AsJava (pre + "  "))
        let is = ms |> List.filter (function Implementation _ -> true | _ -> false)
        let es = ms |> List.filter (function Inheritance _ -> true | _ -> false)
        let classHeader = sprintf "class %s" s
        let classHeader = 
          match is with
          | [] ->
            classHeader
          | _ -> 
            let isNames = is |> List.map (function Implementation i -> i | _ -> failwith "Invalid interface") 
                             |> List.reduce (fun a b -> a + ", " + b)
            sprintf "%s implements %s" classHeader isNames
        let classHeader = 
          match es with
          | [] ->
            classHeader
          | _ -> 
            let esNames = es |> List.map (function Inheritance i -> i | _ -> failwith "Invalid inheritance") 
                             |> List.reduce (fun a b -> a + ", " + b)
            sprintf "%s extends %s" classHeader esNames
        sprintf "%s {\n%s%s}\n" classHeader (!+mss) pre
      | Return c ->
        sprintf "%sreturn %s;\n" pre ((c.AsJava "").TrimEnd[|','; '\n'; ';'|])
      | GenericTypedDecl(args, v, t, c) ->
        let args_suffix = sprintf "<%s>" (args |> List.map toTypeAsArgument |> List.reduce (fun a b -> a + ", " + b))
        TypedDecl(v,t + args_suffix,c).AsJava pre
      | TypedDecl(s,t,Option.None) -> 
        if t = "" then sprintf "%s%s;\n" pre s
        else sprintf "%s%s %s;\n" pre (toJavaType t) s
      | TypedDecl(s,t,Some v) -> 
        if t = "" then sprintf "%s%s = %s;\n" pre s ((v.AsJava "").TrimEnd[|','; '\n'; ';'|])
        else 
          let x = ((v.AsJava "").TrimEnd[|','; '\n'; ';'|])
          let res = sprintf "%s%s %s = %s;\n" pre (toJavaType t) s x
          res
      | Var s -> s
      | ConstBool b -> b.ToString().ToLower()
      | ConstInt i -> i.ToString()
      | ConstFloat f -> f.ToString()
      | ConstString s -> sprintf "\"%s\"" s
      | Ref s -> sprintf "ref %s" s
      | Assign (v,c) -> sprintf "%s%s = %s;\n" pre v ((c.AsJava "").TrimEnd[|','; '\n'; ';'|])
      | ConstLambda (pc,args,body) ->
        let argss = args |> List.map (fun a -> a + ",")
        sprintf "%s(%s) => %s" pre ((!+argss).TrimEnd[|','|]) (body.AsJava (pre + "  "))
      | TypedSig (n,args,t) ->
        let argss = args |> List.map (fun (t,a) -> t + " " + a + ",")
        sprintf "%s%s %s(%s);\n" pre t n ((!+argss).TrimEnd[|','; '\n'|])
      | TypedDef (n,args,t,body) ->
        let argss = args |> List.map (fun (t,a) -> (toJavaType t) + " " + a + ",")
        (if t = "" then sprintf "%s%s(%s) {\n%s%s}\n" pre n
         else sprintf "%s%s %s(%s) {\n%s%s}\n" pre t n) ((!+argss).TrimEnd[|','; '\n'|]) (body.AsJava (pre + "  ")) pre
      | GenericNew(c,t_args,args) ->
        let args_suffix = sprintf "<%s>" (t_args |> List.map toTypeAsArgument |> List.reduce (fun a b -> a + ", " + b))
        New(c + args_suffix, args).AsJava pre
      | New(c,args) ->
        let argss = args |> List.map (fun a -> ((a.AsJava "").TrimEnd[|','; '\n'; ';'|]) + ",")
        sprintf "%snew %s(%s);\n" pre c ((!+argss).TrimEnd[|','; '\n'; ';'|])
      | Call(n,args) ->
        let argss = args |> List.map (fun a -> ((a.AsJava "").TrimEnd[|','; '\n'; ';'|]) + ",")
        sprintf "%s%s(%s);\n" pre n ((!+argss).TrimEnd[|','; '\n'; ';'|])
      | MethodCall(n,m,args) ->
        let argss = args |> List.map (fun a -> ((a.AsJava "").TrimEnd[|','; '\n'; ';'|]) + ",")
        sprintf "%s%s.%s(%s);\n" pre n m ((!+argss).TrimEnd[|','; '\n'; ';'|])
      | StaticMethodCall("Int32","Parse",args) ->
        StaticMethodCall("Integer","parseInt",args).AsJava pre
      | StaticMethodCall("Console","WriteLine",args) ->
        StaticMethodCall("System.out","println",args).AsJava pre
      | StaticMethodCall("Console","ReadLine",args) ->
        StaticMethodCall("new Scanner(System.in)","nextLine",args).AsJava pre
      | StaticMethodCall(c,m,args) ->
        let argss = args |> List.map (fun a -> (a.AsJava "").TrimEnd([|'\n'|]) + ",")
        sprintf "%s%s.%s(%s);\n" pre c m ((!+argss).TrimEnd[|','; '\n'; ';'|])
      | If(c,t,e) ->
        sprintf "%sif %s {\n%s } else {\n%s }\n" pre (c.AsJava "") (t.AsJava (pre + "  ")) (e.AsJava (pre + "  "))
      | While(c,b) ->
        sprintf "%swhile %s {\n%s }\n" pre (c.AsJava "") (b.AsJava (pre + "  "))
      | Op(a,op,b) ->
        sprintf "(%s %s %s)" ((a.AsJava "").Replace("\n","").Replace(";","").Replace("  ","")) (op.AsJava) ((b.AsJava (pre + "")).Replace("\n","").Replace(";","").Replace("  ",""))
      | Sequence (p,q) ->
        sprintf "%s%s" (p.AsJava pre) (q.AsJava pre)
      | Hidden(_) -> ""
      | ArraySet(x,i,e) -> 
        sprintf "%s%s[%d] = %s;\n" pre x i (e.AsJava "")
      | ArrayGet(x,i) -> 
        sprintf "%s%s[%d];\n" pre x i
      | ArrayDecl(x,t,Option.None) ->
        sprintf "%s%s[] %s;\n" pre (toJavaType t) x
      | ArrayDecl(x,t,Some c) ->
        sprintf "%s%s[] %s = %s;\n" pre (toJavaType t) x (c.AsJava "")
      | NewArray(t,n) ->
        sprintf "%snew %s[%d]" pre (toJavaType t) n
      | GenericLambdaFuncCall(_) | GenericLambdaFuncDecl(_) -> 
        "Error: unsupported lambda functions in Java pretty printer"
      | s -> failwithf "Unsupported Java statement %A" s
    member this.NumberOfJavaLines = 
      let code = ((this.AsJava ""):string).TrimEnd([|'\n'|])
      let lines = code.Split([|'\n'|])
      lines.Length

    member this.AsCSharp pre = 
      match this with
      | GenericClassType(c,args) ->
        let args_suffix = sprintf "<%s>" (args |> List.reduce (fun a b -> a + ", " + b))
        sprintf "%s%s%s" pre c args_suffix
      | ClassType c -> sprintf "%s%s" pre c
      | VoidType -> sprintf "%svoid" pre
      | BoolType -> sprintf "%sbool" pre
      | IntType -> sprintf "%sint" pre
      | FloatType -> sprintf "%sfloat" pre
      | StringType -> sprintf "%sstring" pre
      | Private p ->
        (sprintf "%sprivate%s" pre (p.AsCSharp pre)).Replace("private" + pre, "private ")
      | Static p ->
        (sprintf "%sstatic%s" pre (p.AsCSharp pre)).Replace("static" + pre, "static ")
      | Public p ->
        (sprintf "%spublic%s" pre (p.AsCSharp pre)).Replace("public" + pre, "public ")
      | ToString p ->
        (sprintf "%s%s.ToString()" pre (p.AsCSharp ""))
      | Object bs ->
        let argss = bs |> Seq.map (fun a -> a.Key.Replace("__", "\_\_") + @"=" + (a.Value.AsCSharp "") + @" \\") |> Seq.toList
        sprintf @"%s\begin{tabular}{c} %s \end{tabular}" pre ((!+argss).TrimEnd[|','; ' '; '\\'|])
      | MainCall -> ""
      | End -> ""
      | None -> "null"
      | Dots -> "...\n"
      | Implementation i | Inheritance i -> ""
      | GenericInterfaceDef(args,s,ms) ->
        let args_suffix = sprintf "<%s>" (args |> List.reduce (fun a b -> a + ", " + b))
        InterfaceDef(s + args_suffix,ms).AsCSharp pre
      | InterfaceDef(s,ms) ->
        let mss = ms |> List.map (fun m -> m.AsCSharp (pre + "  "))
        let res = sprintf "interface %s {\n%s%s}\n" s (!+mss) pre
        res
      | GenericClassDef(args,s,ms) ->
        let args_suffix = sprintf "<%s>" (args |> List.reduce (fun a b -> a + ", " + b))
        ClassDef(s + args_suffix,ms).AsCSharp pre
      | ClassDef(s,ms) -> 
        let mss = ms |> List.map (fun m -> m.AsJava (pre + "  "))
        let is = ms |> List.filter (function Implementation _ -> true | _ -> false)
        let es = ms |> List.filter (function Inheritance _ -> true | _ -> false)
        let classHeader = sprintf "class %s" s
        let classHeader = 
          match is with
          | [] ->
            classHeader
          | _ -> 
            let isNames = is |> List.map (function Implementation i -> i | _ -> failwith "Invalid interface") 
                             |> List.reduce (fun a b -> a + ", " + b)
            sprintf "%s : %s" classHeader isNames
        let classHeader = 
          match es with
          | [] ->
            classHeader
          | _ -> 
            let esNames = es |> List.map (function Inheritance i -> i | _ -> failwith "Invalid inheritance") 
                             |> List.reduce (fun a b -> a + ", " + b)
            sprintf "%s : %s" classHeader esNames
        sprintf "%s {\n%s%s}\n" classHeader (!+mss) pre
      | Return c ->
        sprintf "%sreturn %s;\n" pre ((c.AsCSharp "").TrimEnd[|','; '\n'; ';'|])
      | GenericTypedDecl(args, v, t, c) ->
        let args_suffix = sprintf "<%s>" (args |> List.reduce (fun a b -> a + ", " + b))
        TypedDecl(v,t + args_suffix,c).AsCSharp pre
      | TypedDecl(s,t,Option.None) -> 
        if t = "" then sprintf "%s%s;\n" pre s
        else sprintf "%s%s %s;\n" pre t s
      | TypedDecl(s,t,Some v) -> 
        
        if t = "" then sprintf "%s%s = %s;\n" pre s ((v.AsCSharp "").TrimEnd[|','; '\n'; ';'|])
        else sprintf "%s%s %s = %s;\n" pre t s ((v.AsCSharp "").TrimEnd[|','; '\n'; ';'|])
      | Var s -> s
      | ConstBool b -> b.ToString().ToLower()
      | ConstInt i -> i.ToString()
      | ConstFloat f -> f.ToString()
      | ConstString s -> sprintf "\"%s\"" s
      | Ref s -> sprintf "ref %s" s
      | Assign (v,c) -> sprintf "%s%s = %s;\n" pre v ((c.AsCSharp "").TrimEnd[|','; '\n'; ';'|])
      | ConstLambda (pc,args,body) ->
        let argss = args |> List.map (fun a -> a + ",")
        sprintf "%s(%s) => %s" pre ((!+argss).TrimEnd[|','|]) (body.AsCSharp (pre + "  "))
      | TypedSig (n,args,t) ->
        let argss = args |> List.map (fun (t,a) -> t + " " + a + ",")
        sprintf "%s%s %s(%s);\n" pre t n ((!+argss).TrimEnd[|','; '\n'|])
      | TypedDef (n,args,t,body) ->
        let argss = args |> List.map (fun (t,a) -> t + " " + a + ",")
        (if t = "" then sprintf "%s%s(%s) {\n%s%s}\n" pre n
         else sprintf "%s%s %s(%s) {\n%s%s}\n" pre t n) ((!+argss).TrimEnd[|','; '\n'|]) (body.AsCSharp (pre + "  ")) pre
      | GenericNew(c,t_args,args) ->
        let args_suffix = sprintf "<%s>" (t_args |> List.reduce (fun a b -> a + ", " + b))
        New(c + args_suffix, args).AsCSharp pre
      | New(c,args) ->
        let argss = args |> List.map (fun a -> ((a.AsCSharp "").TrimEnd[|','; '\n'; ';'|]) + ",")
        sprintf "%snew %s(%s);\n" pre c ((!+argss).TrimEnd[|','; '\n'; ';'|])
      | GenericLambdaFuncCall(v_name, args) ->
        let argss = args |> List.map (fun a -> ((a.AsCSharp "").TrimEnd[|','; '\n'; ';'|]) + ",")
        sprintf "%s%s(%s);\n" pre v_name ((!+argss).TrimEnd[|','; '\n'; ';'|])
      | Call(n,args) ->
        let argss = args |> List.map (fun a -> ((a.AsCSharp "").TrimEnd[|','; '\n'; ';'|]) + ",")
        sprintf "%s%s(%s);\n" pre n ((!+argss).TrimEnd[|','; '\n'; ';'|])
      | MethodCall(n,m,args) ->
        let argss = args |> List.map (fun a -> ((a.AsCSharp "").TrimEnd[|','; '\n'; ';'|]) + ",")
        sprintf "%s%s.%s(%s);\n" pre n m ((!+argss).TrimEnd[|','; '\n'; ';'|])
      | StaticMethodCall(c,m,args) ->
        let argss = args |> List.map (fun a -> (a.AsCSharp "").TrimEnd([|'\n'|]) + ",")
        if argss.Length = 1 then
          sprintf "%s%s.%s(%s);\n" pre c m ((!+argss).TrimEnd[|','; '\n'; ';'|])
        else
          sprintf "%s%s.%s(%s);\n" pre c m ((!+argss).TrimEnd[|','; '\n'; ';'|])
      | If(c,t,e) ->
        sprintf "%sif %s {\n%s } else {\n%s }\n" pre (c.AsCSharp "") (t.AsCSharp (pre + "  ")) (e.AsCSharp (pre + "  "))
      | While(c,b) ->
        sprintf "%swhile %s {\n%s }\n" pre (c.AsCSharp "") (b.AsCSharp (pre + "  "))
      | Op(a,op,b) ->
        sprintf "(%s %s %s)" ((a.AsCSharp "").Replace("\n","").Replace(";","").Replace("  ","")) (op.AsCSharp) ((b.AsCSharp (pre + "")).Replace("\n","").Replace(";","").Replace("  ",""))
      | Sequence (p,q) ->
        sprintf "%s%s" (p.AsCSharp pre) (q.AsCSharp pre)
      | Hidden(_) -> ""
      | ArrowType([],ret) ->
        sprintf @"%s() $\rightarrow$ %s" pre (ret.AsCSharp "")
      | ArrowType(args,ret) ->
        if args.Length = 1 then
          sprintf @"%s%s $\rightarrow$ %s" pre (args.Head.AsCSharp "") (ret.AsCSharp "")
        else
          let argNames = args |> List.map (fun arg -> arg.AsCSharp "") |> List.reduce (fun a b -> a + @"$\times$" + b)
          sprintf @"%s(%s) $\rightarrow$ %s" pre argNames (ret.AsCSharp "")
      | ArrayDecl(x,t,Option.None) ->
        sprintf "%s%s[] %s;\n" pre t x
      | ArrayDecl(x,t,Some c) ->
        sprintf "%s%s[] %s = %s;\n" pre t x (c.AsCSharp "")
      | NewArray(t,n) ->
        sprintf "%snew %s[%d]" pre (toJavaType t) n
      | ArraySet(x,i,e) -> 
        sprintf "%s%s[%d] = %s;\n" pre x i (e.AsCSharp "")
      | ArrayGet(x,i) -> 
        sprintf "%s%s[%d];\n" pre x i
      | Array(vs) ->
        let vs_s = 
          [ for v in vs do yield (v.Value.AsCSharp "").Replace("\n","").Replace(";","")] |> List.reduce (fun a b -> a + " ;" + b)
        sprintf "%s[%s]" pre vs_s
      | GenericLambdaFuncDecl(i_t:string, o_t:string, v_name:string, arg_name:string, Return(res)) ->
        sprintf "%sFunc<%s,%s> %s = %s => %s;\n" pre i_t o_t v_name arg_name (res.AsCSharp "")
      | s -> failwithf "Unsupported C# statement %A" s
    member this.NumberOfCSharpLines = 
      let code = ((this.AsCSharp ""):string).TrimEnd([|'\n'|])
      if code = "" then 
        0
      else 
        let lines = code.Split([|'\n'|])
        lines.Length



let makeStatic c = Static(c)
let makePublic c = Public(c)
let makePrivate c = Private(c)
let implements i = Implementation(i)
let extends i = Inheritance(i)
let interfaceDef c m = InterfaceDef(c,m)
let genericInterfaceDef args c m = GenericInterfaceDef(args,c,m)
let classDef c m = ClassDef(c,m)
let genericClassDef args c m = GenericClassDef(args,c,m)
let (:=) x y = Assign(x,y)
let newC c a = New(c,a)
let genericNewC c args a = GenericNew(c,args,a)
let constBool x = ConstBool(x)
let constInt x = ConstInt(x)
let constFloat x = ConstFloat(x)
let constString x = ConstString(x)
let dots = Dots
let genericLambdaFuncDecl i_t o_t v_name arg body = GenericLambdaFuncDecl(i_t,o_t,v_name,arg,body)
let genericLambdaFuncCall f arg = GenericLambdaFuncCall(f,arg)
let genericTypedDecl args x t = GenericTypedDecl(args,x,t,Option.None)
let genericTypedDeclAndInit args x t c = GenericTypedDecl(args,x,t,Some c)
let typedDecl x t = TypedDecl(x,t,Option.None)
let typedDeclAndInit x t c = TypedDecl(x,t,Some c)
let arrayDecl x t = ArrayDecl(x,t,Option.None)
let arrayDeclAndInit x t c = ArrayDecl(x,t,Some c)
let arraySet x i c = ArraySet(x,i,c)
let arrayGet x i = ArrayGet(x,i)
let newArray t n = NewArray(t,n)
let var x = Var(x)
let ret x = Return(x)
let def x l b = Def(x,l,b)
let typedDef x l t b = TypedDef(x,l,t,b)
let typedSig x l t = TypedSig(x,l,t)
let call x l = Call(x,l)
let staticMethodCall c m l = StaticMethodCall(c,m,l)
let mainCall = MainCall
let methodCall x m l = MethodCall(x,m,l)
let ifelse c t e = If(c,t,e)
let ifthen c t = IfThen(c,t)
let whiledo c b = While(c,b)
let (.+) a b = Op(a, Plus, b)
let (.-) a b = Op(a, Minus, b)
let (.*) a b = Op(a, Times, b)
let (./) a b = Op(a, DividedBy, b)
let (.>) a b = Op(a, GreaterThan, b)
let (.=) a b = Op(a, Equals, b)
let (>>) a b = Sequence(a, b)
let endProgram = End
let toString c = ToString c
