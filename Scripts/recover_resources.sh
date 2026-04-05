#!/usr/bin/env bash
# recover_resources.sh — Download all resources from Wiki/Resources/*.md
# Parses ## Recover sections for Download: and Clone: lines.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WIKI_DIR="$ROOT/Wiki/Resources"
RES_DIR="$ROOT/Resources"

mkdir -p "$RES_DIR"

for md in "$WIKI_DIR"/*.md; do
  [ -f "$md" ] || continue
  name="$(basename "$md" .md)"

  # Extract the ## Recover section
  in_recover=false
  while IFS= read -r line; do
    if [[ "$line" == "## Recover" ]]; then
      in_recover=true
      continue
    fi
    if $in_recover && [[ "$line" == "## "* ]]; then
      break
    fi
    if ! $in_recover; then
      continue
    fi

    # Parse Download: lines
    if [[ "$line" == Download:* ]]; then
      url="${line#Download: }"
      # Read next line for Target:
      target=""
      continue
    fi
    if [[ "$line" == Target:* ]]; then
      target="${line#Target: }"
    fi

    # Parse Clone: lines
    if [[ "$line" == Clone:* ]]; then
      clone_cmd="${line#Clone: }"
      repo_dir="$(echo "$clone_cmd" | awk '{print $NF}')"
      if [ -d "$ROOT/$repo_dir" ]; then
        echo "[skip] $repo_dir already exists"
      else
        echo "[clone] $name -> $repo_dir"
        (cd "$ROOT" && $clone_cmd) || echo "[warn] Failed to clone $name"
      fi
      continue
    fi
  done < "$md"

  # Download if we have a URL
  if [ -n "${url:-}" ]; then
    out="${target:-Resources/${name}.pdf}"
    out_path="$ROOT/$out"

    if [ -f "$out_path" ]; then
      echo "[skip] $out already exists"
    else
      echo "[download] $name -> $out"
      curl -fSL -o "$out_path" "$url" 2>/dev/null || {
        curl -fSL -H "Accept: application/pdf" -o "$out_path" "$url" 2>/dev/null || {
          echo "[warn] Failed to download $name from $url"
          rm -f "$out_path"
        }
      }
    fi
    unset url target
  fi
done

echo "Done."
