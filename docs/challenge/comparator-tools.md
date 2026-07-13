# Comparator tool setup

This repository includes a challenge package for the AI-authored Mathlib-candidate
lemmas:

- `Challenge/*/Conformance.lean` imports only Mathlib and states the challenge
  claims with `sorry`.
- `Challenge/*/Leaderboard.lean` imports this project and fills those claims.
- `comparator/*.json` configures comparator runs.
- `formalization.yaml` records provenance and AI usage notes.

The comparator check needs external tools: `landrun`, `comparator`, and
`lean4export`. The working setup used `landrun` from the `main` branch rather
than the latest released tag.

## Install tools

From the repository root:

```bash
bash scripts/install_comparator_tools.sh
```

By default this uses:

```text
~/code/lean-tools/comparator
$(go env GOPATH)/bin/landrun
```

Override the tool root if desired:

```bash
AIQ_COMPARATOR_TOOL_ROOT=/tmp/lean-tools bash scripts/install_comparator_tools.sh
```

## Run checks

From the repository root:

```bash
bash scripts/run_challenge_comparator.sh
```

This performs:

```bash
lake env lean Challenge/MathlibCandidate/Softmax/Conformance.lean
lake env lean Challenge/MathlibCandidate/Softmax/Leaderboard.lean
lake build Challenge.MathlibCandidate.Softmax.Leaderboard
lake env comparator comparator/candidate-01-softmax.json
```

using explicit `COMPARATOR_LANDRUN` and `COMPARATOR_LEAN4EXPORT` paths.

## Development fallback

If real `landrun` fails locally with a sandbox permission error, the wiring can
be checked with comparator's fake landrun wrapper:

```bash
bash scripts/run_challenge_comparator.sh --fake-landrun
```

A fake-landrun pass is useful for development, but it is not the hardened
sandboxed check. The real check should end with:

```text
Lean default kernel accepts the solution
Your solution is okay!
```


## Current challenge layout

The challenge files now live under `Challenge/` rather than at repository root.
The runner reads the module names from each comparator JSON file and derives the
corresponding paths automatically.

Default configs run by `scripts/run_challenge_comparator.sh`:

* `comparator/candidate-01-softmax.json` — the softmax package (definition, Fréchet
  derivative, tight `½`-Lipschitz, Loewner Jacobian bounds).

See `Challenge/README.md` for the manifest. The VeriStressGT certificate theorems
themselves are documented (each library's `README.md`), not comparator challenges — their
statements are in the constructions' own vocabulary, whose faithfulness is a human review
task, not something the comparator can certify.
