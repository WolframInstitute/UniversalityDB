/- Not a lakefile.lean root — not part of `lake build`. Compiled standalone in CI
   (`lake env lean -o ...`) so leanchecker/nanoda, which auto-detect a module named
   after the package, have something to find. `import Integrity` transitively
   covers every other module, since Integrity.lean is already required to import
   all of them (see Scripts/verify_integrity.sh's sync check). -/
import Integrity
