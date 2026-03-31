#!/usr/bin/env wolframscript

(* generate_notebooks.wls — Convert Notebooks/*.md -> .nb locally *)

root = ParentDirectory[ DirectoryName[ ExpandFileName[ $ScriptCommandLine[[ 1 ]] ] ] ];
nbDir = FileNameJoin[ { root, "Notebooks" } ];

mdFiles = FileNames[ "*.md", nbDir ];

If[ mdFiles === {},
  Print[ "No .md files found in ", nbDir ];
  Exit[ 1 ] ];

Do[
  baseName = FileBaseName[ mdFile ];
  nbFile = FileNameJoin[ { nbDir, baseName <> ".nb" } ];
  Print[ "[", baseName, "] .md -> .nb" ];
  Export[ nbFile, ImportString[ Import[ mdFile, "Text" ], { "Markdown", "Notebook" } ] ],
  { mdFile, mdFiles } ];

Print[ "Done. Generated ", Length[ mdFiles ], " notebook(s)." ];
