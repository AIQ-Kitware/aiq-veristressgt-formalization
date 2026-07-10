#!/usr/bin/env bash
# Install and verify a Lean 4 environment for this repository.
#
# This uses elan, Lean's version manager, and prefers a project-local
# lean-toolchain file so everyone in the repo uses the same Lean version.

set -Eeuo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO_ROOT"

ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export ELAN_HOME
export PATH="$ELAN_HOME/bin:$PATH"

DEFAULT_LEAN_TOOLCHAIN="${LEAN_TOOLCHAIN:-leanprover/lean4:stable}"

log() {
    printf '[setup_lean] %s\n' "$*"
}

fail() {
    printf '[setup_lean] error: %s\n' "$*" >&2
    exit 1
}

fetch_elan_init() {
    if command -v curl >/dev/null 2>&1; then
        curl -sSf https://elan.lean-lang.org/elan-init.sh
    elif command -v wget >/dev/null 2>&1; then
        wget -qO- https://elan.lean-lang.org/elan-init.sh
    else
        fail "curl or wget is required to install elan"
    fi
}

install_elan_if_needed() {
    if command -v elan >/dev/null 2>&1; then
        log "elan is already installed: $(command -v elan)"
        return
    fi

    log "installing elan into $ELAN_HOME"
    fetch_elan_init | sh -s -- -y

    # The installer writes this file for shell setup. Source it in this process
    # so the rest of the script can immediately use elan, lean, and lake.
    if [ -f "$ELAN_HOME/env" ]; then
        # shellcheck disable=SC1091
        . "$ELAN_HOME/env"
    fi

    export PATH="$ELAN_HOME/bin:$PATH"
    command -v elan >/dev/null 2>&1 || fail "elan install completed, but elan is not on PATH"
}

ensure_project_toolchain() {
    if [ -f lean-toolchain ]; then
        log "using existing lean-toolchain: $(tr -d '\r\n' < lean-toolchain)"
        return
    fi

    log "creating lean-toolchain with default toolchain: $DEFAULT_LEAN_TOOLCHAIN"
    printf '%s\n' "$DEFAULT_LEAN_TOOLCHAIN" > lean-toolchain
}

verify_lean_tools() {
    log "elan state"
    elan show

    log "lean version"
    lean --version

    log "lake version"
    lake --version
}

maybe_show_lake_hint() {
    if [ -f lakefile.lean ] || [ -f lakefile.toml ]; then
        log "Lean project detected. To fetch/build dependencies, run: lake update && lake build"
    else
        log "No lakefile.lean or lakefile.toml found. Lean and Lake are installed and ready."
    fi
}

main() {
    install_elan_if_needed
    ensure_project_toolchain
    verify_lean_tools
    maybe_show_lake_hint
    log "done"
}

main "$@"
