#!/bin/bash
# Proof integrity verification for UniversalityDB
# See Wiki/Concepts/ProofIntegrity.md for the full trust model.
#
# Uses Lean's own tools exclusively:
#
#   1. lake build — compiles project including Integrity.lean, which uses
#      CollectAxioms.collect to programmatically trace axiom dependencies
#      of every key theorem. Violations cause logError → build failure.
#
#   2. leanchecker — replays all compiled declarations through Lean's kernel,
#      catching anything metaprogramming might have smuggled past the elaborator.
#      Built into Lean 4.28+.
#
# No grep, no string parsing of axiom traces — all checking is done inside
# Lean using its Environment API.

set -euo pipefail

VERBOSE=0
for arg in "$@"; do
    case "$arg" in
        -v|--verbose) VERBOSE=1 ;;
        -h|--help)
            cat <<EOF
Usage: verify_integrity.sh [-v|--verbose]
  -v, --verbose   List each theorem's classification (absolute vs conditional)
                  rather than just aggregate counts.
EOF
            exit 0
            ;;
    esac
done

cd "$(dirname "$0")/.."

FAIL=0

# ============================================================================
# Step 1: Build
#
# Integrity.lean uses CollectAxioms.collect on every key theorem and
# logError on violations. If the build succeeds, the axiom checks passed.
# Sorry warnings are reported by the compiler but don't fail the build.
# ============================================================================

# ============================================================================
# Step 0: Sync check
#
# Verify Integrity.lean imports match lakefile.lean roots. If someone adds
# a module to lakefile but forgets the import, its theorems won't be checked.
# ============================================================================

echo "=== Import sync check ==="
LAKE_ROOTS=$(grep '`' Lean/lakefile.lean \
    | grep -v 'autoImplicit\|package\|lean_lib\|srcDir' \
    | sed 's/.*`//;s/,.*//;s/]//' | tr -d ' ' \
    | grep -v '^Integrity$' | sort)
INTEGRITY_IMPORTS=$(grep '^import ' Lean/Integrity.lean \
    | grep -v 'import Lean' \
    | sed 's/import //' | sort)

if [ "$LAKE_ROOTS" = "$INTEGRITY_IMPORTS" ]; then
    echo "PASS: Integrity.lean imports match lakefile.lean roots"
else
    echo "FAIL: Integrity.lean imports do not match lakefile.lean roots"
    echo "  Missing from Integrity.lean:"
    comm -23 <(echo "$LAKE_ROOTS") <(echo "$INTEGRITY_IMPORTS") | sed 's/^/    /'
    echo "  Extra in Integrity.lean:"
    comm -13 <(echo "$LAKE_ROOTS") <(echo "$INTEGRITY_IMPORTS") | sed 's/^/    /'
    FAIL=1
fi

# ============================================================================
# Step 1: Build
# ============================================================================

echo ""
echo "=== Building project (Lean-native integrity checks) ==="
BUILD_LOG=$(mktemp)
set +e
if [ "$VERBOSE" -eq 1 ]; then
    (cd Lean && lake build 2>&1) | tee "$BUILD_LOG"
else
    # Suppress per-theorem ABSOLUTE/CONDITIONAL detail lines unless --verbose;
    # show everything else (warnings, errors, build progress, summary counts).
    (cd Lean && lake build 2>&1) | tee "$BUILD_LOG" \
        | grep -v 'info:.*Integrity\.lean.*ABSOLUTE \|info:.*Integrity\.lean.*CONDITIONAL '
fi
BUILD_EXIT=${PIPESTATUS[0]}
set -e

# Verify Integrity.lean ran
if ! grep -q "INTEGRITY CHECK\|INTEGRITY VIOLATION" "$BUILD_LOG"; then
    echo ""
    echo "FAIL: Integrity.lean output not found in build log."
    echo "  Verify Integrity is listed in Lean/lakefile.lean roots."
    FAIL=1
fi

if [ "$BUILD_EXIT" -ne 0 ]; then
    echo ""
    echo "FAIL: lake build exited with code $BUILD_EXIT"
    FAIL=1
fi

# ============================================================================
# Step 2: Sorry count
# ============================================================================

echo ""
echo "=== Sorry check ==="
SORRY_COUNT=$(grep -c "declaration uses.*sorry" "$BUILD_LOG" 2>/dev/null || true)

if [ "$SORRY_COUNT" -eq 0 ]; then
    echo "sorry: 0 (clean)"
else
    echo "sorry: $SORRY_COUNT warning(s) (tracked, not a failure — verify against Wiki/Status.md):"
    grep "declaration uses.*sorry" "$BUILD_LOG" | sed 's/^/  /'
fi

rm -f "$BUILD_LOG"

# ============================================================================
# Step 3: Kernel replay (leanchecker)
#
# Replays all compiled declarations through Lean's kernel, verifying that
# every declaration in every project module is accepted. Catches environment
# manipulation via metaprogramming that the elaborator might have missed.
# ============================================================================

echo ""
echo "=== Kernel replay (leanchecker) ==="
# Derive module list from lakefile.lean — no hardcoded list to keep in sync.
MODULES=$(grep '`' Lean/lakefile.lean \
    | grep -v 'autoImplicit\|package\|lean_lib\|srcDir' \
    | sed 's/.*`//;s/,.*//;s/]//' | tr -d ' ')
set +e
CHECKER_OUTPUT=$(cd Lean && lake env leanchecker $MODULES 2>&1)
CHECKER_EXIT=$?
set -e

if [ "$CHECKER_EXIT" -eq 0 ]; then
    echo "PASS: all declarations accepted by kernel"
else
    echo "FAIL: leanchecker rejected declarations"
    echo "$CHECKER_OUTPUT" | sed 's/^/  /'
    FAIL=1
fi

# ============================================================================
# Summary
# ============================================================================

echo ""
echo "========================================"
if [ "$FAIL" -eq 0 ]; then
    echo "  ALL CHECKS PASSED"
else
    echo "  SOME CHECKS FAILED"
fi
echo "========================================"

exit "$FAIL"
