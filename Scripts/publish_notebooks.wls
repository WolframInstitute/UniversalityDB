#!/usr/bin/env wolframscript

(* publish_notebooks.wls — Convert Wiki/Notebooks/*.md -> .nb and upload to Wolfram Cloud *)

root = ParentDirectory[ DirectoryName[ ExpandFileName[ $ScriptCommandLine[[ 1 ]] ] ] ];
srcDir = FileNameJoin[ { root, "Wiki", "Notebooks" } ];
outDir = FileNameJoin[ { root, "Notebooks" } ];

mdFiles = FileNames[ "*.md", srcDir ];

If[ mdFiles === {},
  Print[ "No .md files found in ", srcDir ];
  Exit[ 1 ] ];

If[ !DirectoryQ[ outDir ], CreateDirectory[ outDir ] ];

Print[ "Universality Graph Notebook Publisher" ];
Print[ "======================================" ];

results = {};

Do[
  baseName = FileBaseName[ mdFile ];
  nbFile = FileNameJoin[ { outDir, baseName <> ".nb" } ];

  Print[ "[", baseName, "] Converting .md -> .nb..." ];
  Export[ nbFile, ImportString[ Import[ mdFile, "Text" ], { "Markdown", "Notebook" } ] ];

  Print[ "[", baseName, "] Uploading to Wolfram Cloud..." ];
  cloudObj = CloudObject[ "UniversalityGraph/" <> baseName <> ".nb", Permissions -> "Public" ];
  CopyFile[ nbFile, cloudObj, OverwriteTarget -> True ];
  Print[ "[", baseName, "] Published: ", First[ cloudObj ] ];
  Print[ "" ];
  AppendTo[ results, baseName -> ToString[ First[ cloudObj ] ] ],
  { mdFile, mdFiles } ];

Print[ "======================================" ];
Do[ Print[ "  ", r[[ 1 ]], ": ", r[[ 2 ]] ], { r, results } ];
