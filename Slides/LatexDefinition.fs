module LatexDefinition

open CodeDefinitionImperative
open CodeDefinitionLambda
open Coroutine
open CommonLatex
open Runtime
open TypeChecker
open Interpreter

let rec skipEveryThree =
  function 
  | x::y::z::xs -> x :: y :: skipEveryThree (xs)
  | l -> l

type LatexElement = 
  | Section of string 
  | Image of string * float
  | Advanced of LatexElement
  | SubSection of string 
  | Paragraph of string 
  | Pause
  | Question of string
  | Figure of string * float
  | InlineCode of string
  | InLineCodeResized of TextSize * string
  | GenericCodeBlock of TextSize * bool * string
  | Text of string
  | Block of LatexElement
  | BlockWithTitle of string * LatexElement
  | Items of List<LatexElement>
  | PythonCodeBlock of TextSize * Code
  | LambdaCodeBlock of TextSize * Term * showTypes:bool
  | FSharpCodeBlock of TextSize * Term * showTypes:bool
  | HaskellCodeBlock of TextSize * Term * showTypes:bool
  | CSharpCodeBlock of TextSize * Code
  | Unrepeated of LatexElement
  | Tiny
  | Small
  | Normal
  | Large
  | TypingRules of List<TypingRule>
  | VerticalStack of List<LatexElement>
  
  | PythonStateTrace of TextSize * Code * RuntimeState<Code>
  | CSharpStateTrace of TextSize * Code * RuntimeState<Code>
  | CSharpTypeTrace of TextSize * Code * TypeCheckingState<Code> * showMethodsTypeChecking:bool
  | LambdaStateTrace of textSize:TextSize * term:Term * maxSteps:Option<int> * expandInsideLambda:bool * showArithmetics:bool * showControlFlow:bool * showLet:bool * showPairs:bool * showUnions:bool
  | LambdaTypeTrace of textSize:TextSize * term:Term
  with
    member this.ToDocumentString() = 
      match this with
      | Section t ->
        sprintf @"\section{%s}%s" t "\n"
      | SubSection t ->
        sprintf @"\subsection{%s}%s" t "\n"
      | Paragraph t ->
        sprintf @"\paragraph{%s}%s" t "\n"
      | Pause -> @""
      | Question q -> 
          sprintf @"\textit{%s}" q
      | Figure(path,scale) ->
          sprintf "\\begin{figure}\n\\includegraphics[scale=%f]{%s}\n\\end{figure}" scale path
      | InlineCode c -> sprintf @"\texttt{%s}" c
      | InLineCodeResized(size,c) -> sprintf @"%s\texttt{%s}" (size.ToString()) c
      | GenericCodeBlock(size,showLines,c) ->
          sprintf "\\lstset{showstringspaces=false}\\lstset{basicstyle=\\ttfamily%s}%s\\begin{lstlisting}\n%s\n\\end{lstlisting}" (size.ToString()) (if showLines then "" else "\\lstset{numbers=none}") c
      | Text t -> t
      | Tiny -> sprintf "\\tiny\n"
      | Small -> sprintf "\\small\n"
      | Normal -> sprintf "\\normal\n"
      | Large -> sprintf "\\large\n"
      | Block t ->
        let ts = t.ToDocumentString()
        sprintf @"%s" ts
      | Items items ->
        let items = items |> List.map (function | Pause -> @"" | item -> let i = item.ToDocumentString() in @"\item " + i + "\n")
        sprintf @"%s%s%s" beginItemize (items |> Seq.fold (+) "" ) endItemize
      | PythonCodeBlock (ts,c) ->
          let textSize = ts.ToString()
          sprintf @"\lstset{basicstyle=\ttfamily%s}%s%s%s" textSize (beginCode "Python") (c.AsPython "") endCode
      | PythonStateTrace(ts,p,st) ->
        let textSize = ts.ToString()
        let stackTraces = st :: runToEnd (runPython p) st
        let ps = (p.AsPython "").TrimEnd([|'\n'|])
        let stackTraceTables = 
          [ 
            yield sprintf @"\lstset{basicstyle=\ttfamily%s}%s%s%s  " textSize (beginCode "Python") ps endCode
            for st in stackTraces do 
              let stack,heap,input,output = st.AsSlideContent Dots (function Code.Hidden _ -> true | _ -> false) (fun c -> c.AsPython)
              let input = if input = "" then "" else "Input: " + input + @"\\"
              let output = if output = "" then "" else "Output: " + output + @"\\"
              let heap = if heap = "" then "" else "Heap: " + heap + @"\\"
              let slide = sprintf @"%s Stack: %s\\%s%s" textSize stack input output
              yield slide ]
        stackTraceTables |> List.fold (+) ""
      | FSharpCodeBlock (ts, c, showTypes) ->
          let textSize = ts.ToString()
          sprintf @"\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s" textSize (beginCode "ML") (c.ToFSharp (if showTypes then PrintTypes.TypedFSharp else PrintTypes.Untyped) "") endCode
      | HaskellCodeBlock (ts, c , showTypes) ->
          let textSize = ts.ToString()
          sprintf @"\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s" textSize (beginCode "Haskell") (c.ToHaskell (if showTypes then PrintTypes.TypedFSharp else PrintTypes.Untyped) "") endCode
      | LambdaCodeBlock(ts, c, showTypes) ->
          let textSize = ts.ToString()
          sprintf @"\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s" textSize (beginCode "Python") (c.ToLambda (if showTypes then PrintTypes.TypedLambda else PrintTypes.Untyped)) endCode
      | Unrepeated s ->
        s.ToDocumentString()
      | CSharpCodeBlock (ts,c) ->
          let textSize = ts.ToString()
          sprintf @"\lstset{basicstyle=\ttfamily%s}%s%s%s" textSize (beginCode "[Sharp]C") (c.AsCSharp "") endCode
      | TypingRules tr ->
          let trs = tr |> List.map (fun t -> t.ToString())
          (List.fold (+) "" trs)
      | LambdaStateTrace(ts,term,maxSteps,expandInsideLambda,showArithmetics,showControlFlow,showLet,showPairs,showUnions) ->
        let textSize = ts.ToString()
        let states = 
          match maxSteps with
          | Some maxSteps ->
            (id,term) :: runToEnd (BetaReduction.reduce maxSteps expandInsideLambda showArithmetics showControlFlow showLet showPairs showUnions pause) (id,term)
          | _ ->
            (id,term) :: runToEnd (BetaReduction.reduce System.Int32.MaxValue expandInsideLambda showArithmetics showControlFlow showLet showPairs showUnions pause) (id,term)
        let terms = states |> List.map (fun (k,t) -> k t)
        let stackTraceTables = 
          [ for term in terms.Head :: (terms.Tail |> skipEveryThree) do 
              let slide = sprintf @"\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s" textSize (beginCode "ML") (term.ToLambda PrintTypes.Untyped) endCode
              yield slide ]
        let res = stackTraceTables |> List.fold (+) ""
        res
      | LambdaTypeTrace(ts,term) ->
        let textSize = ts.ToString()
        let states = 
            (id,term) :: runToEnd (TypeCheckingReduction.reduce pause) (id,term)
        let terms = states |> List.map (fun (k,t) -> k t)
        let stackTraceTables = 
          [ for term in terms.Head :: (terms.Tail |> skipEveryThree) do 
              let slide = sprintf @"\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s" textSize (beginCode "ML") (term.ToLambda PrintTypes.TypedLambda) endCode
              yield slide ]
        let res = stackTraceTables |> List.fold (+) ""
        res
      | CSharpTypeTrace(ts,p,st,showMethodsTypeChecking) ->
        let textSize = ts.ToString()
        let stackTraces = st :: runToEnd (typeCheckCSharp showMethodsTypeChecking p) st
        let ps = (p.AsCSharp "").TrimEnd([|'\n'|])
        let code = sprintf @"\lstset{basicstyle=\ttfamily%s}%s%s%s" textSize (beginCode "[Sharp]C") ps endCode

        let stackTraceTables = 
          [ for st in stackTraces do 
            let declarations,classes = st.AsSlideContent Dots (function Code.Hidden _ -> true | _ -> false) ConstInt (fun (c:Code) -> c.AsCSharp)
            let declarations = if declarations = "" then "" else "Declarations: " + declarations
            let classes = if classes = "" then "" else "Classes: " + classes
            let slide = sprintf @"\item {%s %s \\ %s \\}" textSize declarations classes
            yield slide ]
        code + (@"\begin{enumerate} " + (stackTraceTables |> List.fold (+) "") + @" \end{enumerate}")
      | CSharpStateTrace(ts,p,st) ->
        let textSize = ts.ToString()
        let heapLabel,stackLabel = "Heap: ","Stack: "
        let stackTraces = st :: runToEnd (runCSharp p) st
        let ps = (p.AsCSharp "").TrimEnd([|'\n'|])
        let code = sprintf @"\lstset{basicstyle=\ttfamily%s}%s%s%s" textSize (beginCode "[Sharp]C") ps endCode
        let stackTraceTables = 
          [ for st in stackTraces do 
            let stack,heap,input,output = st.AsSlideContent Dots (function Code.Hidden _ -> true | _ -> false) (fun c -> c.AsCSharp)

            let input = if input = "" then "" else "Input: " + input + @"\\"
            let output = 
              if output = "" then "" 
              else "Output: " + output + @"\\"
            let heap = if heap = "" then "" else heapLabel + heap + @"\\"
            let slide = sprintf @"\item {%s %s%s\\%s%s%s}" textSize stackLabel stack heap input output
            yield slide ]
        code + (@"\begin{enumerate} " + (stackTraceTables |> List.fold (+) "") + @" \end{enumerate}")
      | VerticalStack items ->
          let items = items |> List.map (fun item -> let i = item.ToDocumentString() in i + "\n")
          let allItems = items |> List.map (fun i -> i + " \n") |> List.fold (+) ""
          allItems
      | _ -> ""
    member this.ToStringAsElement() = 
      match this with
      | Pause -> @"\pause", []
      | Question q -> 
          sprintf @"%s\textit{%s}%s" beginExampleBlock q endExampleBlock, []
      | Figure(path,scale) ->
          sprintf "\\begin{figure}\n\\includegraphics[scale=%f]{%s}\n\\end{figure}" scale path, []
      | InlineCode c -> sprintf @"\texttt{%s}" c, []
      | InLineCodeResized(size,c) -> sprintf @"%s\texttt{%s}" (size.ToString()) c, []
      | GenericCodeBlock(size,showLines,c) -> sprintf "\\lstset{showstringspaces=false}\\lstset{basicstyle=\\ttfamily%s}%s\\begin{lstlisting}\n%s\n\\end{lstlisting}" (size.ToString()) (if showLines then "" else "\\lstset{numbers=none}") c, []
      | Image(image, scale) ->
          
          sprintf @"\includegraphics[scale=%s]{%s}" (string scale) image, []
      | Text t -> t, []
      | Tiny -> sprintf "\\tiny\n", []
      | Small -> sprintf "\\small\n", []
      | Normal -> sprintf "\\normal\n", []
      | Large -> sprintf "\\large\n", []
      | BlockWithTitle(title,t) ->
        let ts,k = t.ToStringAsElement()
        sprintf @"%s%s%s" (beginBlockWithTitle title) ts endExampleBlock, k
      | Block t ->
        let ts,k = t.ToStringAsElement()
        sprintf @"%s%s%s" beginExampleBlock ts endExampleBlock, k
      | Items items ->
        let items = items |> List.map (function | Pause -> @"\pause",[] | item -> let i,k = item.ToStringAsElement() in @"\item " + i + "\n", k)
        let k = items |> List.map snd |> List.fold (@) []
        let items = items |> List.map fst
        sprintf @"%s%s%s" beginItemize (items |> Seq.fold (+) "" ) endItemize, []
      | PythonCodeBlock (ts,c) ->
          let textSize = ts.ToString()
          sprintf @"\lstset{basicstyle=\ttfamily%s}%s%s%s" textSize (beginCode "Python") (c.AsPython "") endCode, []
      | FSharpCodeBlock (ts, c, showTypes) ->
          let textSize = ts.ToString()
          sprintf @"\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s" textSize (beginCode "ML") (c.ToFSharp (if showTypes then PrintTypes.TypedFSharp else PrintTypes.Untyped) "") endCode, []
      | HaskellCodeBlock (ts, c, showTypes) ->
          let textSize = ts.ToString()
          sprintf @"\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s" textSize (beginCode "Haskell") (c.ToHaskell (if showTypes then PrintTypes.TypedFSharp else PrintTypes.Untyped) "") endCode, []
      | LambdaCodeBlock(ts, c, showTypes) ->
          let textSize = ts.ToString()
          sprintf @"\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s" textSize (beginCode "ML") (c.ToLambda (if showTypes then PrintTypes.TypedLambda else PrintTypes.Untyped)) endCode, []
      | Unrepeated s ->
        s.ToStringAsElement() |> fst,[]
      | CSharpCodeBlock (ts,c) ->
          let textSize = ts.ToString()
          let javaVersion = "\n\n" + sprintf @"%s %sWhich in Java then becomes:%s \lstset{basicstyle=\ttfamily%s}%s%s%s%s" beginFrame beginExampleBlock endExampleBlock textSize (beginCode "Java") (c.AsJava "") endCode endFrame
          sprintf @"\lstset{basicstyle=\ttfamily%s}%s%s%s" textSize (beginCode "[Sharp]C") (c.AsCSharp "") endCode, 
            [
              javaVersion
            ]
      | TypingRules tr ->
          let trs = tr |> List.map (fun t -> t.ToString())
          (List.fold (+) "" trs), []
      | VerticalStack items ->
          let items = items |> List.map (fun item -> let i,k = item.ToStringAsElement() in @"\item " + i + "\n", k)
          let k = items |> List.map snd |> List.fold (@) []
          let items = items |> List.map fst
          let allItems = items |> List.map (fun i -> i + " \n") |> List.fold (+) ""
          allItems,k
      | _ -> "", []
    member this.ToBeamerString() =
      match this with
      | Section t ->
        sprintf @"\SlideSection{%s}%s" t "\n"
      | SubSection t ->
        sprintf @"\SlideSubSection{%s}%s" t "\n"
      | Advanced se ->
        //TODO: \footnote{Warning: this material is to be considered advanced!}
        se.ToBeamerString()
      | Block t ->
        let content,rest = t.ToStringAsElement()
        sprintf @"%s%s%s%s%s" beginFrame beginBlock content endBlock endFrame
      | Pause -> @"\pause"
      | Question q ->
        sprintf @"%s%s\textit{%s}%s%s" beginFrame beginExampleBlock q endExampleBlock endFrame
      | Figure(path,scale) ->
          sprintf "\\begin{figure}\n\\includegraphics[scale=%f]{%s}\n\\end{figure}" scale path
      | InlineCode c ->
          sprintf @"%s\texttt{%s}%s" (beginCode "Python") c endCode
      | GenericCodeBlock(size,showLines,c) -> sprintf "\\lstset{showstringspaces=false}\\lstset{basicstyle=\\ttfamily%s}%s\\begin{lstlisting}\n%s\n\\end{lstlisting}" (size.ToString()) (if showLines then "" else "\\lstset{numbers=none}") c
      | InLineCodeResized(size,c) -> sprintf @"%s\texttt{%s}" (size.ToString()) c
      | Text t -> t
      | Items items ->
        let items = items |> List.map (function | Pause -> @"\pause",[] | item -> let i,k = item.ToStringAsElement() in @"\item " + i + "\n", k)
        let k = items |> List.map snd |> List.fold (@) []
        let items = items |> List.map fst
        sprintf @"%s%s%s%s%s" beginFrame beginItemize (items |> Seq.fold (+) "") endItemize endFrame
      | PythonCodeBlock (ts,c) ->
          let textSize = ts.ToString()
          sprintf @"%s\lstset{basicstyle=\ttfamily%s}%s%s%s%s" beginFrame textSize (beginCode "Python") (c.AsPython "") endCode endFrame
      | FSharpCodeBlock (ts, c, showTypes) ->
          let textSize = ts.ToString()
          sprintf @"%s\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s%s" beginFrame textSize (beginCode "ML") (c.ToFSharp (if showTypes then PrintTypes.TypedFSharp else PrintTypes.Untyped) "") endCode endFrame
      | HaskellCodeBlock (ts, c, showTypes) ->
          let textSize = ts.ToString()
          sprintf @"%s\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s%s" beginFrame textSize (beginCode "Haskell") (c.ToHaskell (if showTypes then PrintTypes.TypedFSharp else PrintTypes.Untyped) "") endCode endFrame
      | LambdaCodeBlock (ts, c, showTypes) ->
          let textSize = ts.ToString()
          sprintf @"%s\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s%s" beginFrame textSize (beginCode "ML") (c.ToLambda (if showTypes then PrintTypes.TypedLambda else PrintTypes.Untyped)) endCode endFrame
      | CSharpCodeBlock (ts,c) ->
          let textSize = ts.ToString()
          (sprintf @"%s\lstset{basicstyle=\ttfamily%s}%s%s%s%s" beginFrame textSize (beginCode "[Sharp]C")  (c.AsCSharp "") endCode endFrame) + "\n\n" +
            (sprintf @"%s%sWhich in Java then becomes:%s \lstset{basicstyle=\ttfamily%s}%s%s%s%s" beginFrame beginExampleBlock endExampleBlock textSize (beginCode "Java")  (c.AsJava "") endCode endFrame)
      | TypingRules tr ->
          let trs = tr |> List.map (fun t -> t.ToString())
          sprintf @"%s%s%s" beginFrame (List.fold (+) "" trs) endFrame
      | VerticalStack items ->
          let items = items |> List.map (fun item -> item.ToStringAsElement())
          let k = items |> List.map snd |> List.fold (@) [] |> List.map (fun x -> x + "\n") |> List.fold (+) ""
          let items = items |> List.map fst
          let allItems = items |> List.map (fun i -> i + " \n") |> List.fold (+) ""
          (sprintf @"%s%s%s" beginFrame allItems endFrame) + k
      | PythonStateTrace(ts,p,st) ->
        let textSize = ts.ToString()
        let stackTraces = st :: runToEnd (runPython p) st
        let ps = (p.AsPython "").TrimEnd([|'\n'|])
        let stackTraceTables = 
          [ for st in stackTraces do 
            let stack,heap,output,input = st.AsSlideContent Dots (function Code.Hidden _ -> true | _ -> false) (fun c -> c.AsPython)
            let input = if input = "" then "" else "Input: " + input + @"\\"
            let output = if output = "" then "" else "Output: " + output + @"\\"
            let heap = if heap = "" then "" else "Heap: " + heap + @"\\"
            let slide = sprintf @"%s\lstset{basicstyle=\ttfamily%s}%s%s%s%s Stack: %s\\%s%s%s%s" beginFrame textSize (beginCode "Python") ps endCode textSize stack heap input output endFrame
            yield slide ]
        stackTraceTables |> List.fold (+) ""
      | CSharpTypeTrace(ts,p,st,showMethodsTypeChecking) ->
        let textSize = ts.ToString()
        let stackTraces = st :: runToEnd (typeCheckCSharp showMethodsTypeChecking p) st
        let ps = (p.AsCSharp "").TrimEnd([|'\n'|])
        let stackTraceTables = 
          [ for st in stackTraces do 
            let declarations,classes = st.AsSlideContent Dots (function Code.Hidden _ -> true | _ -> false) ConstInt (fun (c:Code) -> c.AsCSharp)
            let declarations = if declarations = "" then "" else "Declarations: " + declarations
            let classes = if classes = "" then "" else "Classes: " + classes
            let slide = sprintf @"%s\lstset{basicstyle=\ttfamily%s}%s%s%s%s %s\\%s%s" beginFrame textSize (beginCode "[Sharp]C") ps endCode textSize declarations classes endFrame
            yield slide ]
        stackTraceTables |> List.fold (+) ""
      | CSharpStateTrace(ts,p,st) ->
        let textSize = ts.ToString()
        let heapLabel,stackLabel = "Heap: ","Stack: "
        let stackTraces = st :: runToEnd (runCSharp p) st
        let ps = (p.AsCSharp "").TrimEnd([|'\n'|])
        let stackTraceTables = 
          [ for st in stackTraces do 
            let stack,heap,input,output = st.AsSlideContent Dots (function Code.Hidden _ -> true | _ -> false) (fun c -> c.AsCSharp)
            let input = if input = "" then "" else "Input: " + input + @"\\"
            let output = if output = "" then "" else "Output: " + output + @"\\"
            let heap = if heap = "" then "" else heapLabel + heap + @"\\"
            let slide = sprintf @"%s\lstset{basicstyle=\ttfamily%s}%s%s%s%s %s%s\\%s%s%s%s" beginFrame textSize (beginCode "[Sharp]C") ps endCode textSize stackLabel stack heap input output endFrame
            yield slide ]
        stackTraceTables |> List.fold (+) ""
      | LambdaStateTrace(ts,term,maxSteps,expandInsideLambda,showArithmetics,showControlFlow,showLet,showPairs,showUnions) ->
        let textSize = ts.ToString()
        let states = 
          match maxSteps with
          | Some maxSteps ->
            (id,term) :: runToEnd (BetaReduction.reduce maxSteps expandInsideLambda showArithmetics showControlFlow showLet showPairs showUnions pause) (id,term)
          | _ ->
            (id,term) :: runToEnd (BetaReduction.reduce System.Int32.MaxValue expandInsideLambda showArithmetics showControlFlow showLet showPairs showUnions pause) (id,term)
        let terms = states |> List.map (fun (k,t) -> k t)
        let frames = Seq.zip terms (terms.Tail) |> Seq.toList |> skipEveryThree
        let stackTraceTables = 
          [ for term,term' in frames do 
              let slide = sprintf @"%s\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s\pause%s%s%s%s" beginFrame textSize (beginCode "ML") (term.ToLambda PrintTypes.Untyped) endCode (beginCode "ML") (term'.ToLambda PrintTypes.Untyped) endCode endFrame
              yield slide ]
        let res = stackTraceTables |> List.fold (+) ""
        res
      | LambdaTypeTrace(ts,term) ->
        let textSize = ts.ToString()
        let states = 
            (id,term) :: runToEnd (TypeCheckingReduction.reduce pause) (id,term)
        let terms = states |> List.map (fun (k,t) -> k t)
        let frames = Seq.zip terms (terms.Tail) |> Seq.toList |> skipEveryThree
        let stackTraceTables = 
          [ for term,term' in frames do 
              let slide = sprintf @"%s\lstset{basicstyle=\ttfamily%s}\lstset{numbers=none}%s%s%s\pause%s%s%s%s" beginFrame textSize (beginCode "ML") (term.ToLambda PrintTypes.TypedLambda) endCode (beginCode "ML") (term'.ToLambda PrintTypes.TypedLambda) endCode endFrame
              yield slide ]
        let res = stackTraceTables |> List.fold (+) ""
        res
      | Unrepeated s ->
        s.ToBeamerString()
      | _ -> failwith "Unsupported"

and TypingRule =
  {
    Premises : List<string>
    Conclusion : string
  }
  with 
    override this.ToString() =
      let ps = 
        match this.Premises |> List.map ((+) "\ ") with
        | [] -> ""
        | ps -> ps |> List.reduce (fun a b -> a + "\wedge" + b)
      sprintf @"%s\frac{%s}{%s}%s" beginMath ps this.Conclusion endMath

let (!) = Text
let (!!) = InlineCode
let ItemsBlock l = l |> Items |> Block 
let ItemsBlockWithTitle t l = BlockWithTitle(t, l |> Items)
let TextBlock l = l |> Text |> Block 

let rec generatePresentation author title (slides:List<LatexElement>) =
  @"\documentclass{beamer}
\usetheme[hideothersubsections]{HRTheme}
\usepackage{beamerthemeHRTheme}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{graphicx}
\usepackage[space]{grffile}
\usepackage{soul,xcolor}
\usepackage{listings}
\usepackage{tabularx}
\lstset{language=C,
basicstyle=\ttfamily\footnotesize,
escapeinside={(*@}{@*)},
mathescape=true,
breaklines=true}
\lstset{
  literate={ï}{{\""i}}1
           {ì}{{\`i}}1
}

\title{" + title + @"}

\author{" + author + @"}

\institute{Hogeschool Rotterdam \\ 
Rotterdam, Netherlands}

\date{}

\begin{document}
\maketitle
" + (slides |> List.map (fun x -> x.ToBeamerString()) |> List.fold (+) "") + @"
\begin{frame}{This is it!}
\center
\fontsize{18pt}{7.2}\selectfont
The best of luck, and thanks for the attention!
\end{frame}

\end{document}"


let rec generateDocument author title (elements:List<LatexElement>) =
  @"\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage{graphicx}
\usepackage[space]{grffile}
\usepackage{soul,xcolor}
\usepackage{colortbl}
\usepackage{color}
\newcommand{\red}[1]{
\textcolor{red}{#1}
}
\newcommand{\white}[1]{
\textcolor{white}{#1}
}
\usepackage{listings}
\usepackage[margin=0.5in]{geometry}
\usepackage{tabularx}
\usepackage{pdflscape}
\lstset{language=C,
basicstyle=\ttfamily\footnotesize,
frame=single,
numbers=left,
breaklines=true,
escapeinside={(*@}{@*)},
mathescape=true,
breaklines=true}
\lstset{
  literate={ï}{{\""i}}1
           {ì}{{\`i}}1
}

\title{" + title + @"}

\author{" + author + @"}

\date{}

\begin{document}
\maketitle
\begin{landscape}
" + (elements |> List.map (fun x -> x.ToDocumentString()) |> List.fold (+) "") + @"
\end{landscape}
\end{document}"
