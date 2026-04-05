#!/usr/bin/env wolframscript

(* generate_notebooks.wls — Convert Wiki/Notebooks/*.md -> Notebooks/*.nb locally *)

root = ParentDirectory[ DirectoryName[ ExpandFileName[ $ScriptCommandLine[[ 1 ]] ] ] ];
srcDir = FileNameJoin[ { root, "Wiki", "Notebooks" } ];
outDir = FileNameJoin[ { root, "Notebooks" } ];

mdFiles = FileNames[ "*.md", srcDir ];

If[ mdFiles === {},
  Print[ "No .md files found in ", srcDir ];
  Exit[ 1 ] ];

If[ !DirectoryQ[ outDir ], CreateDirectory[ outDir ] ];

Do[
  baseName = FileBaseName[ mdFile ];
  nbFile = FileNameJoin[ { outDir, baseName <> ".nb" } ];
  Print[ "[", baseName, "] Wiki/Notebooks/", baseName, ".md -> Notebooks/", baseName, ".nb" ];
  Export[ nbFile, ImportString[ Import[ mdFile, "Text" ], { "Markdown", "Notebook" } ] ],
  { mdFile, mdFiles } ];

Print[ "Done. Generated ", Length[ mdFiles ], " notebook(s) in Notebooks/." ];
