#!/usr/bin/env bash
# Install the external tools needed to run the AIQ challenge comparator check.
#
# This installs:
#   - landrun from github.com/zouuup/landrun@main
#   - leanprover/comparator
#   - lean4export, from comparator's pinned Lake dependency
#
# Defaults mirror the setup that worked on Jon's machine. Override paths with:
#   AIQ_COMPARATOR_TOOL_ROOT=/path/to/tools bash scripts/install_comparator_tools.sh
#
set -euo pipefail

TOOL_ROOT="${AIQ_COMPARATOR_TOOL_ROOT:-$HOME/code/lean-tools}"
COMPARATOR_REPO="${AIQ_COMPARATOR_REPO:-$TOOL_ROOT/comparator}"
COMPARATOR_URL="${AIQ_COMPARATOR_URL:-https://github.com/leanprover/comparator.git}"
LANDRUN_GO_REF="${AIQ_LANDRUN_GO_REF:-main}"
GO_BIN="$(go env GOPATH 2>/dev/null)/bin"

need_cmd() {
    if ! command -v "$1" >/dev/null 2>&1; then
        echo "error: required command not found: $1" >&2
        exit 1
    fi
}

need_cmd go
need_cmd git
need_cmd lake

mkdir -p "$TOOL_ROOT"

printf 'Installing landrun from github.com/zouuup/landrun/cmd/landrun@%s\n' "$LANDRUN_GO_REF"
go install "github.com/zouuup/landrun/cmd/landrun@$LANDRUN_GO_REF"

if [ ! -d "$COMPARATOR_REPO/.git" ]; then
    if [ -e "$COMPARATOR_REPO" ]; then
        echo "error: $COMPARATOR_REPO exists but is not a git checkout" >&2
        exit 1
    fi
    echo "Cloning comparator into $COMPARATOR_REPO"
    git clone "$COMPARATOR_URL" "$COMPARATOR_REPO"
else
    echo "Updating existing comparator checkout at $COMPARATOR_REPO"
    git -C "$COMPARATOR_REPO" fetch origin main
    current_branch="$(git -C "$COMPARATOR_REPO" branch --show-current || true)"
    if [ "$current_branch" = "main" ] || [ "$current_branch" = "master" ]; then
        git -C "$COMPARATOR_REPO" pull --ff-only || {
            echo "warning: could not fast-forward comparator checkout; continuing with existing checkout" >&2
        }
    else
        echo "warning: comparator checkout is on branch '$current_branch'; not changing branches" >&2
    fi
fi

echo "Building comparator"
(
    cd "$COMPARATOR_REPO"
    lake build comparator
)

echo "Building lean4export from comparator's pinned dependency"
(
    cd "$COMPARATOR_REPO/.lake/packages/lean4export"
    lake build lean4export
)

COMPARATOR_BIN="$COMPARATOR_REPO/.lake/build/bin/comparator"
LEAN4EXPORT_BIN="$COMPARATOR_REPO/.lake/packages/lean4export/.lake/build/bin/lean4export"
LANDRUN_BIN="$GO_BIN/landrun"

for exe in "$LANDRUN_BIN" "$COMPARATOR_BIN" "$LEAN4EXPORT_BIN"; do
    if [ ! -x "$exe" ]; then
        echo "error: expected executable missing: $exe" >&2
        exit 1
    fi
done

ENV_FILE="$TOOL_ROOT/aiq-comparator-env.sh"
cat > "$ENV_FILE" <<EOF_ENV
# Source this file to use the comparator tools installed for aiq-dkps-formalization.
export PATH="$GO_BIN:$COMPARATOR_REPO/.lake/build/bin:\$PATH"
export COMPARATOR_LANDRUN="$LANDRUN_BIN"
export COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT_BIN"
EOF_ENV

cat <<EOF_DONE

Comparator tools installed successfully.

landrun:     $LANDRUN_BIN
comparator:  $COMPARATOR_BIN
lean4export: $LEAN4EXPORT_BIN

env file:    $ENV_FILE

Run the challenge check from the repository root with:

  bash scripts/run_challenge_comparator.sh

Or, for a shell with the tools configured:

  source "$ENV_FILE"

EOF_DONE
