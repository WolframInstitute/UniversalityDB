#!/usr/bin/env wolframscript

(* generate_notebooks.wls -- Convert Wiki/Notebooks/*.md -> Notebooks/*.nb locally.

   For each markdown source:
     1. Convert to .nb via the Markdown importer.
     2. Walk the cell list; for each Input cell, evaluate its boxes in the
        current kernel session and append a constructed Output cell after it.
        Variables defined in earlier cells persist across cells in the same
        notebook (a fresh kernel context is started per notebook).

   This bypasses the front-end entirely -- `NotebookEvaluate` in headless
   wolframscript was either unable to write Output cells or coerced graphics
   to OutputForm strings via `InsertResults`. The programmatic path saves
   real GraphicsBox/RasterBox so plots render in the cached .nb.

   Special handling:
   - `NotebookDirectory[]` is overridden to point to the project Notebooks/
     directory (where the .nb files live), so relative paths resolve.
   - `Print[...]` calls are captured and emitted as Text Output cells so
     diagnostic output isn't lost.
   - Evaluation errors are caught and rendered as a Failure cell, never
     aborting the whole script. *)

root = ParentDirectory[ DirectoryName[ ExpandFileName[ $ScriptCommandLine[[ 1 ]] ] ] ];
srcDir = FileNameJoin[ { root, "Wiki", "Notebooks" } ];
outDir = FileNameJoin[ { root, "Notebooks" } ];

mdFiles = FileNames[ "*.md", srcDir ];

If[ mdFiles === {},
  Print[ "No .md files found in ", srcDir ];
  Exit[ 1 ] ];

If[ !DirectoryQ[ outDir ], CreateDirectory[ outDir ] ];

(* Sanitize a base name into a valid Mathematica context fragment. *)
sanitizeContext[ name_String ] :=
  Module[ { sanitized },
    sanitized = StringReplace[ name, RegularExpression[ "[^a-zA-Z0-9]" ] -> "" ];
    If[ sanitized === "" || !UpperCaseQ @ StringTake[ sanitized, 1 ] && !LowerCaseQ @ StringTake[ sanitized, 1 ],
      "Notebook" <> sanitized,
      sanitized ]
  ]

parseHeldStatements[ boxes_ ] :=
  Module[ { source, expr },
    source = Quiet @ Check[ ToExpression[ ToString[ boxes, InputForm ], InputForm ], $Failed ];
    If[ source === $Failed, Return[ $Failed ] ];
    expr = Quiet @ Check[ ToExpression[ source, InputForm, HoldComplete ], $Failed ];
    If[ expr === $Failed, Return[ $Failed ] ];
    Replace[
      expr,
      HoldComplete[ args___ ] :> DeleteCases[ Hold /@ Unevaluated[ { args } ], Hold[ Null ] ]
    ]
  ]

(* Evaluate a single Input cell's boxes, returning a list of cells:
   - any Print outputs as Text cells (if produced)
   - the Output cell holding the result (or Failure cell on error)
   - empty list if the result is Null and no prints occurred. *)
SetAttributes[ buildOutputCells, HoldAll ];
buildOutputCells[ boxes_, notebookDir_String ] :=
  Module[ { statements, prints, result, cells },
    statements = parseHeldStatements[ boxes ];
    If[ statements === $Failed,
      Return[ { Cell[ BoxData[ ToBoxes[ Failure[ "ParseError",
        <| "MessageTemplate" -> "Could not parse Input cell." |> ] ] ], "Output" ] } ] ];
    prints = {};
    result = Block[
      { NotebookDirectory, Print },
      NotebookDirectory[___] := notebookDir;
      Print[ args___ ] := AppendTo[ prints, StringJoin[ ToString /@ { args } ] ];
      Fold[ Quiet @ Check[ ReleaseHold[ #2 ], "EvalError" ] &, Null, statements ]
    ];
    cells = {};
    Do[ AppendTo[ cells, Cell[ p, "Print" ] ], { p, prints } ];
    If[ result =!= Null,
      AppendTo[ cells, Cell[ BoxData[ ToBoxes[ result ] ], "Output" ] ] ];
    cells
  ]

processCell[ Cell[ BoxData[ boxes_ ], "Input", inputOpts___ ], notebookDir_ ] :=
  Prepend[ buildOutputCells[ boxes, notebookDir ], Cell[ BoxData[ boxes ], "Input", inputOpts ] ]
processCell[ other_, _ ] := { other }

processNotebook[ Notebook[ cells_List, opts___ ], notebookDir_ ] :=
  Notebook[ Flatten[ Function[ c, processCell[ c, notebookDir ] ] /@ cells ], opts ]

Do[
  baseName = FileBaseName[ mdFile ];
  nbFile = FileNameJoin[ { outDir, baseName <> ".nb" } ];
  contextName = sanitizeContext[ baseName ];
  Print[ "[", baseName, "] Wiki/Notebooks/", baseName, ".md -> Notebooks/", baseName, ".nb" ];

  (* Convert markdown to a fresh notebook expression. *)
  Export[ nbFile, ImportString[ Import[ mdFile, "Text" ], { "Markdown", "Notebook" } ] ];

  Print[ "[", baseName, "] Evaluating cells programmatically..." ];
  Begin[ "NotebookEval`" <> contextName <> "`" ];
  result = Check[
    nbExpr = Get[ nbFile ];
    newNb = processNotebook[ nbExpr, outDir ];
    Export[ nbFile, newNb ];
    True,
    False ];
  End[];
  If[ !result,
    Print[ "[", baseName, "] Evaluation step failed; .nb retained without cached outputs." ] ],
  { mdFile, mdFiles } ];

Print[ "Done. Generated ", Length[ mdFiles ], " notebook(s) in Notebooks/." ];
