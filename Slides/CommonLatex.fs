﻿module CommonLatex

let beginFrame = @"\begin{frame}[fragile]{\CurrentSection}" + "\n"
let endFrame = "\n" + @"\end{frame}" + "\n\n"
let beginTikzpicture = @"\resizebox{\textwidth}{!}{\n\begin{tikzpicture}"
let endTikzpicture = @"\end{tikzpicture}\n}\n"
let beginBlock = @"\begin{block}{\CurrentSubSection}" + "\n"
let endBlock = "\n" + @"\end{block}" + "\n\n"
let beginBlockWithTitle t = @"\begin{block}{" + t + "}" + "\n"
let endBlockWithTitle = "\n" + @"\end{block}" + "\n\n"
let beginExampleBlock = @"\begin{exampleblock}{}" + "\n"
let endExampleBlock = "\n" + @"\end{exampleblock}" + "\n\n"
let beginItemize = @"\begin{itemize}" + "\n"
let endItemize = "\n" + @"\end{itemize}" + "\n"
let beginCode lang = (sprintf @"\lstset{language=%s}\begin{lstlisting}" lang) + "\n"
let endCode = "\n" + @"\end{lstlisting}" + "\n"
let beginMath = @"$$"
let endMath = @"$$" + "\n"

let beginTabular c = 
  match c with
  | [] -> @"\begin{tabular}{|c|}" + "\n\\hline"
  | _ -> @"\begin{tabular}{ |" + (c |> List.reduce (fun a b -> a + "|" + b))  + "| }\n\\hline"
let endTabular = @"\end{tabular}"

type TextSize = ScriptSize | FootnoteSize | Tiny | Small | Normal | Large
  with 
    override this.ToString() =
      match this with
      | FootnoteSize -> @"\footnotesize"
      | ScriptSize -> @"\scriptsize"
      | Tiny -> @"\tiny"
      | Small -> @"\small"
      | Normal -> @"\normal"
      | Large -> @"\large"

let toGreekLetter s =
  match s with
  | "a" -> @"$\alpha$"
  | "b" -> @"$\beta$"
  | "c" -> @"$\gamma$"
  | "d" -> @"$\delta$"
  | "e" -> @"$\epsilon$"

  | "h" -> @"$\theta$"
  | "i" -> @"$\iota$"

  | "k" -> @"$\kappa$"

  | "r" -> @"$\rho$"
  | "s" -> @"$\sigma$"

  | "t" -> @"$\tau"

  | "z" -> @"$\zeta"
  | _ -> s


type HighlightType = 
  | Underlined
  | Colored
