#!/usr/bin/env wolframscript

(* publish_notebooks.wls — Upload Notebooks/*.nb to Wolfram Cloud.

   Assumes Notebooks/*.nb already exist (run Scripts/generate_notebooks.wls
   first). This script does NOT convert .md or evaluate cells; it just
   uploads whatever is on disk, so you can inspect locally before publishing. *)

root = ParentDirectory[ DirectoryName[ ExpandFileName[ $ScriptCommandLine[[ 1 ]] ] ] ];
outDir = FileNameJoin[ { root, "Notebooks" } ];

nbFiles = FileNames[ "*.nb", outDir ];

If[ nbFiles === {},
  Print[ "No .nb files in ", outDir, ". Run Scripts/generate_notebooks.wls first." ];
  Exit[ 1 ] ];

Print[ "Universality Graph Notebook Publisher" ];
Print[ "======================================" ];
Print[ "Uploading ", Length[ nbFiles ], " notebook(s) to Wolfram Cloud." ];
Print[ "" ];

results = {};

Do[
  baseName = FileBaseName[ nbFile ];
  Print[ "[", baseName, "] Uploading..." ];
  cloudObj = CloudObject[ "UniversalityGraph/" <> baseName <> ".nb", Permissions -> "Public" ];
  CopyFile[ nbFile, cloudObj, OverwriteTarget -> True ];
  Print[ "[", baseName, "] Published: ", First[ cloudObj ] ];
  Print[ "" ];
  AppendTo[ results, baseName -> ToString[ First[ cloudObj ] ] ],
  { nbFile, nbFiles } ];

Print[ "======================================" ];
Do[ Print[ "  ", r[[ 1 ]], ": ", r[[ 2 ]] ], { r, results } ];
