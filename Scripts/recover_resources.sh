#!/usr/bin/env bash
# recover_resources.sh — Download all resources referenced in Resources/*.md

set -euo pipefail
cd "$(dirname "$0")/../Resources"

for md in *.md; do
  name="${md%.md}"

  # Skip non-paper resources
  url=$(grep -m1 '^Download:' "$md" 2>/dev/null | sed 's/^Download: *//' || true)
  [ -z "$url" ] && continue

  # Determine output filename
  case "$url" in
    *.pdf) out="${name}.pdf" ;;
    *)     out="${name}.pdf" ;;  # most DOI/arxiv links resolve to PDF
  esac

  if [ -f "$out" ]; then
    echo "[skip] $out already exists"
    continue
  fi

  echo "[download] $name -> $out"
  curl -fSL -o "$out" "$url" 2>/dev/null || {
    # DOI/arxiv links may need redirect following; try with accept header
    curl -fSL -H "Accept: application/pdf" -o "$out" "$url" 2>/dev/null || {
      echo "[warn] Failed to download $name from $url"
      rm -f "$out"
    }
  }
done

echo "Done."
