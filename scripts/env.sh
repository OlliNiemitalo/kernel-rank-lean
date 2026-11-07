# Sourced by the scripts in this directory. Keeps every tool, cache and build output inside
# the repository's ignored `.tmp/` directory.
repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp="$repo/.tmp"
export ELAN_HOME="$tmp/elan"
export XDG_CACHE_HOME="$tmp/cache"
export MATHLIB_CACHE_DIR="$tmp/cache/mathlib"
export PATH="$ELAN_HOME/bin:$PATH"
isabelle_version=Isabelle2026
isabelle_bin="$tmp/$isabelle_version/bin/isabelle"
