# Implementation guidance — closing F2 (T2 attention derivation) and F4b (IBP → MILP wiring)

**Date:** 2026-07-08 · Companion to [`AUDIT.md`](AUDIT.md) §4 (findings F2, F3, F4) and §5
(steps 3–4). All Mathlib lemma names below were **verified to exist in the pinned rev**
(`lake-manifest.json` mathlib `476fb97b…`) by grepping the DKPS checkout's
`.lake/packages/mathlib` — file:line given at first use so nobody re-learns the
wrong-name trap (`AGENTS.md` §6). Notably verified: **there is no `softmax` anywhere in
the pinned Mathlib**, so §F2-B's definition duplicates nothing.

Effort at a glance:

| Piece | What it buys | Size |
|---|---|---|
| F2-A linear-dominance bridge | closes F2 for `attention.linear_dominance`; fixes F3 en route | ~1 day |
| F2-B softmax `LipschitzWith ½` | the missing consumer of the flagship Jacobian lemma; strongest Mathlib candidate in the repo | ~1–2 days (calculus plumbing) |
| F2-C fixed-pattern assembly | derives `L_attn`; **adjudicates the `n/4` vs `n/2` question** (see F2-C.3 — read before starting) | ~1–2 days after F2-B |
| F4b-1..4 advSet + Rmax + IBP wiring | concrete `advSet`, geometric `label_sound`, `milp-rmax-clamp` as a lemma, `bigM_relu_complete` premises discharged by `Layer.sound` | ~1 day |
| F4b-5 full Theorem A (`BigMReach`) | whole-network encoding soundness+completeness ⟹ feasible set = true adversaries | ~1–2 days |

Recommended order: **F4b-1..4 → F2-A → F2-B → F2-C → F4b-5.** F4b-1..4 is the cheapest
and unlocks doc/edge fixes; F2-A establishes the deviation-form pattern F2-C reuses;
F2-C should not start before reading §F2-C.3.

Workflow reminders (repo conventions): syntax-check with `lake env lean <file>` (no
parallel `lake build`); `set_option autoImplicit false`; new public theorems go into the
axiom-audit file and `formalization.yaml`; the per-library README tables and the
`edges:` block must be updated when anchors land.

---

## Part I — F2: deriving the attention block constants

### The shape of the fix (read first)

The current wrappers assume `LipschitzWith K g` for the *whole margin function* — a fact
about an object (the end-to-end map) that is never modelled, with a constant that (for
`linear_dominance`) doesn't even have the right ε-dimension (F3). The repair is **not**
to prove that Lipschitz fact. The UCLA constructions never establish a Lipschitz
constant either — they establish **total-deviation bounds over the ε-box** (`dw`, `dV`,
`B_i`, `B_max` in `linear_dominance.py:189-196`; `L_attn·ε` in `fixed_pattern.py`). So
the faithful formalization replaces "assumed Lipschitz constant of the margin" with
"assumed (or derived) deviation bounds on the block's *intermediate* quantities" — which
are exactly the numbers the code computes — and proves everything from there to
robustness. After F2-A, the *assumed* facts are `Δw`/`ΔV`; after its optional step 5,
nothing about the linear-dominance block is assumed at all.

### F2-A — the `linear_dominance` bridge

New file suggestion: `SelfAttention/LinearDominanceBlock.lean` (keep the existing
`LinearDominance.lean` until the derived theorem replaces `linearDominance_robust`;
delete or deprecate the assumed-Lipschitz wrapper at the end, updating README/yaml).

**Step 0 — the deviation-margin lemma** (in `LipschitzMargin/Basic.lean`; this is also
the F3 fix, listed here since F2-A depends on it):

```lean
/-- Margin certificate from a *total deviation* bound over the ball (the form the
attention constructions actually establish — `B_max` is a box deviation, not a
Lipschitz constant; cf. AUDIT.md F3). -/
theorem robust_of_deviation_lt_margin
    {E : Type*} [PseudoMetricSpace E]
    (g : E → ℝ) (x₀ : E) (ε D : ℝ)
    (hdev : ∀ x, dist x x₀ ≤ ε → |g x - g x₀| ≤ D)
    (hmargin : D < g x₀) :
    ∀ x, dist x x₀ ≤ ε → 0 < g x := by
  intro x hx
  have h := abs_le.mp (hdev x hx)
  linarith [h.1]
```

**Step 1 — input space and box.** Use `X : Fin n → Fin d → ℝ` with the **default Pi
metric, which is already the sup (L∞) metric**: `nndist_pi_def`
(`Mathlib/Topology/MetricSpace/Pseudo/Pi.lean:48`) and `dist_pi_le_iff`
(used e.g. at `Mathlib/Topology/MetricSpace/Lipschitz.lean:351`) give
`dist X X₀ ≤ ε ↔ ∀ i, dist (X i) (X₀ i) ≤ ε ↔ ∀ i j, |X i j − X₀ i j| ≤ ε`
(apply twice; `Real.dist_eq` at the leaves). So the VNN-LIB ε-box **is**
`Metric.closedBall X₀ ε` — no bespoke box predicate, and the certificate theorems
compose with `robust_of_deviation_lt_margin` with zero adaptation. State this
correspondence once as a lemma (`box_iff_dist_le`) and use it everywhere (F4b uses the
same fact on `Fin n → ℝ`).

**Step 2 — the block, abstractly.** Do *not* model UCLA's weight construction; model the
diagonal-gated shape and take the construction's engineered facts as hypotheses:

```lean
variable {n d dv : ℕ}

/-- Diagonal gated-linear attention: per-token output `Z i = w(X) i • V(X) i`.
`w`/`V` are arbitrary here; the construction's structure enters through the
deviation hypotheses `hw`/`hV` below (= the code's `dw`, `dV`). -/
structure GatedAttn (n d dv : ℕ) where
  w : (Fin n → Fin d → ℝ) → Fin n → ℝ
  V : (Fin n → Fin d → ℝ) → Fin n → EuclideanSpace ℝ (Fin dv)

def GatedAttn.Z (A : GatedAttn n d dv) (X : Fin n → Fin d → ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin dv) := A.w X i • A.V X i
```

**Step 3 — per-token deviation** (this is where the already-proved
`linearDominance_token_bound` finally gets consumed):

```lean
theorem token_deviation (A : GatedAttn n d dv) (X₀ : Fin n → Fin d → ℝ)
    (ε Δw ΔV Bmax : ℝ)
    (hw : ∀ X, dist X X₀ ≤ ε → ∀ i, |A.w X i - A.w X₀ i| ≤ Δw)
    (hV : ∀ X, dist X X₀ ≤ ε → ∀ i, ‖A.V X i - A.V X₀ i‖ ≤ ΔV)
    (hB : ∀ i, Δw * (‖A.V X₀ i‖ + ΔV) + |A.w X₀ i| * ΔV ≤ Bmax) :
    ∀ X, dist X X₀ ≤ ε → ∀ i, ‖A.Z X i - A.Z X₀ i‖ ≤ Bmax :=
  fun X hX i => (linearDominance_token_bound _ _ _ _ _ _ (hw X hX i) (hV X hX i)).trans (hB i)
```

Faithfulness note for the docstring: `hB` with `Bmax := max_i B_i` is the code's
`B_max` loop (`linear_dominance.py:192-197`); `hw`/`hV` with `Δw := ε·2(gate+ε)`,
`ΔV := ε·√d·σ_V` are `dw`/`dV` (lines 189–190). These are the honest new seams — and
they are *deviation* quantities, so no spurious ε appears anywhere (the F3 fix).

**Step 4 — aggregate over tokens and through the head.** Flatten to
`EuclideanSpace ℝ (Fin n × Fin dv)` (avoids `Fin (n*dv)` index arithmetic;
`Fintype.sum_prod_type` splits the norm-square sum):

```lean
def GatedAttn.zflat (A : GatedAttn n d dv) (X : Fin n → Fin d → ℝ) :
    EuclideanSpace ℝ (Fin n × Fin dv) := fun p => A.Z X p.1 p.2

theorem zflat_deviation … (hBmax : 0 ≤ Bmax) … :
    ‖A.zflat X - A.zflat X₀‖ ≤ Real.sqrt n * Bmax
```

Proof route: `EuclideanSpace.norm_eq`, `Fintype.sum_prod_type` to get
`Σ_i ‖Z_i − Z_i⁰‖² ≤ n·Bmax²`, then `Real.sqrt_le_sqrt` and
`Real.sqrt_mul_self hBmax` (mind the `n`-cast: `Real.sqrt (n * Bmax^2) = √n * Bmax`
needs `Real.sqrt_mul (by positivity)`). Include `hBmax : 0 ≤ Bmax` explicitly — for
`n = 0` the `hB` hypothesis is vacuous and cannot supply it.

For the head, take `Whead : EuclideanSpace ℝ (Fin n × Fin dv) →L[ℝ] EuclideanSpace ℝ (Fin c)`
(or a `Matrix` via `toEuclideanCLM`, matching the SoftmaxJacobianBound idioms) and the
per-competitor margin `g k X := (Whead (A.zflat X) + bhead) y - (Whead (A.zflat X) + bhead) k`.
The coordinate extraction `|u j| ≤ ‖u‖` on `EuclideanSpace`: use
`|u j| = |⟪EuclideanSpace.single j 1, u⟫|` + `abs_inner_le_norm`. Then

```lean
theorem margin_deviation … :
    |g k X - g k X₀| ≤ 2 * ‖Whead‖ * (Real.sqrt n * Bmax)
```

(the bias cancels in the difference; two coordinates each move by at most
`‖Whead‖·‖Δzflat‖`).

**Step 5 — the derived certificate**, replacing `linearDominance_robust`:

```lean
/-- Linear-dominance certificate, DERIVED: per-token deviation hypotheses
(the code's dw/dV/B_max) ⟹ robust. Margin hypothesis is exactly the code's
`m_X0 > 2·L_h·√n·B_max` (linear_dominance.py:206) — note: NO ε factor
(AUDIT.md F3). -/
theorem linearDominance_robust_derived
    (A : GatedAttn n d dv) … (hw hV hB hBmax as above)
    (hmargin : ∀ k, k ≠ y → 2 * ‖Whead‖ * (Real.sqrt n * Bmax) < g k X₀) :
    ∀ X, dist X X₀ ≤ ε → ∀ k, k ≠ y → 0 < g k X
```

— assemble steps 3–4 with `robust_of_deviation_lt_margin`. This closes F2 for the
linear construction: the only assumed facts are the code's own intermediate quantities.

**Step 6 (optional, second pass) — derive `hw`/`hV` too.** `V X i` is affine in the
token (`W_Vᵀ (X i)`): `lipschitz_affine_of_opNorm` + the L∞→L2 step
`‖v‖₂ ≤ √d·max|vⱼ|` (prove inline: `EuclideanSpace.norm_eq` + bound each summand) gives
`ΔV = ε·√d·σ_V` exactly. The gate `w X i = ⟪q_i(X), k_i(X)⟫` with affine `q, k` and
`‖q₀‖ = ‖k₀‖ = gate_scale` yields, by the *same* product-rule pattern as
`linearDominance_token_bound` (reuse it with the inner product in place of `•`):
`|Δw| ≤ 2ε·gate + ε² ≤ 2ε(gate+ε) = dw` — the code's constant is slightly conservative
(safe direction); note that in the docstring. After this step, nothing about the block
is assumed. Not required to declare F2 closed for this construction, but cheap.

### F2-B — `LipschitzWith ½ softmax` (the ForMathlib prize)

New file: `ForMathlib/Analysis/SoftmaxLipschitz.lean`. This is the missing *consumer* of
`softmax_jacobian_opNorm_le_half` and, since softmax is absent from Mathlib, the
repo's strongest upstream candidate when packaged with it.

**Prerequisite refactor:** `sjJ`, `sjJ_mulVec`, `sjJ_isHermitian` in
`SoftmaxJacobianBound.lean` are `private`. Promote them (drop `private`, keep them
namespaced; or move them above a `section`) — the fderiv statement below needs `sjJ` by
name. Re-run the axiom audit after (mechanical).

```lean
noncomputable def softmax (s : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  toLp 2 (fun i => Real.exp (ofLp s i) / ∑ j, Real.exp (ofLp s j))
```

(Use the same `toLp`/`ofLp` plumbing the Rayleigh proof already navigated;
`EuclideanSpace` is `PiLp 2`, so don't define it as a bare lambda.)

Supporting lemmas, all easy: `softmax_pos` (needs `[NeZero n]` or `0 < n` for the
denominator via `Finset.sum_pos` + `Real.exp_pos` + `Finset.univ_nonempty`),
`softmax_nonneg`, `softmax_sum_one` (`Finset.sum_div`). These instantiate the Jacobian
bound's probability-vector hypotheses.

**The calculus core:**

```lean
theorem hasFDerivAt_softmax (s : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt softmax (toEuclideanCLM (𝕜 := ℝ) (sjJ (ofLp (softmax s)))) s
```

∂ⱼ softmaxᵢ = aᵢ(δᵢⱼ − aⱼ) with `a = softmax s`, which is entry `(i,j)` of
`diag a − a aᵀ = sjJ a` — so the claimed derivative is exactly the proved-bounded
matrix. Route: coordinatewise via `hasFDerivAt_pi`
(`Mathlib/Analysis/Calculus/FDeriv/Pi.lean`); each coordinate is
`s ↦ exp(sᵢ) / Σⱼ exp(sⱼ)` — build with `Real.hasDerivAt_exp` composed with the
coordinate-evaluation CLM (`EuclideanSpace.proj i` / `PiLp.proj`), `HasFDerivAt.sum`
for the denominator, `HasFDerivAt.div` (denominator ≠ 0 from `softmax_pos`'s
underlying sum-positivity). Then `ext`-check the resulting CLM against
`toEuclideanCLM (sjJ a)` entrywise. This is the fiddly part of F2-B — pure plumbing, no
mathematical risk. Budget most of the effort here.

**The payoff, three lines after that:**

```lean
theorem lipschitzWith_softmax : LipschitzWith (1/2 : ℝ≥0) (softmax (n := n)) := by
  refine lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hasFDerivAt_softmax x).differentiableAt) (fun x => ?_)
  rw [(hasFDerivAt_softmax x).fderiv]
  -- ‖toEuclideanCLM (sjJ a)‖₊ = ‖sjJ a‖₊ ≤ ½ :
  --   l2_opNorm_toEuclideanCLM + softmax_jacobian_opNorm_le_half
  --   (+ softmax_nonneg, softmax_sum_one); coerce norm→nnnorm via NNReal.coe_le_coe.
```

`lipschitzWith_of_nnnorm_fderiv_le` is in the **root namespace**,
`Mathlib/Analysis/Calculus/MeanValue.lean:515` (verified in the pinned rev; the
`Convex.lipschitzOnWith_of_nnnorm_fderiv_le` variant at :508 is the on-set form if you
ever need box-local constants). Mind the `‖·‖₊` vs `‖·‖` coercion — the Jacobian bound
is stated for `‖·‖`; bridge with `← NNReal.coe_le_coe` / `coe_nnnorm` and the fact that
`(1/2 : ℝ≥0) = ((1:ℝ)/2).toNNReal`-style normalization. Also mind that `‖·‖` here must
elaborate as the L²-operator norm — `open scoped Matrix.Norms.L2Operator` (the §6 trap).

### F2-C — fixed-pattern assembly, and the `n/4` question

**F2-C.1 — score deviation.** Scores `S i j (X) = α·⟪X i, X j⟫` with unit-norm nominal
tokens (`hunit : ∀ i, ‖X₀ i‖ = 1` — an explicit hypothesis; the construction enforces
it). Same bilinear pattern as F2-A step 6:
`|ΔS i j| ≤ α(2√d·ε + d·ε²) = B_S·ε` where `B_S := α(2√d + εd)` — matching
`compute_L_attn`'s `B_S` (`fixed_pattern.py:63`) exactly, as a *sensitivity* whose box
deviation is `B_S·ε`. Per row: `‖ΔS i ·‖₂ ≤ √n·B_S·ε`.

**F2-C.2 — through softmax and the values.** With `a i (X) := softmax (α • S-row)`:
`‖a i X − a i X₀‖₂ ≤ ½·√n·B_S·ε` by `lipschitzWith_softmax`. Output row
`Z i = Σⱼ (a i)ⱼ • Vⱼ`; product-rule decomposition into three terms
(`Δa·V₀ + a₀·ΔV + Δa·ΔV`), bounded via `‖Σⱼ cⱼ • vⱼ‖ ≤ ‖c‖₁·maxⱼ‖vⱼ‖` and
`‖c‖₁ ≤ √n·‖c‖₂` (Cauchy–Schwarz — check for `Finset.inner_mul_le_norm_mul_norm` or
prove inline). The middle term uses `‖a₀ i‖₁ = 1` (probability vector!) — which yields
exactly the code's `√d·σ(W_V)` term with **no** n-factor. That the ℓ¹-normalization of
softmax rows is what kills the n-factor in the value path is a nice, checkable piece of
the accounting.

**F2-C.3 — STOP AND COMPARE (read before proving the final constant).** Assembling
C.1–C.2 as above gives, per row,

```
‖ΔZ i‖ ≤ (n/2)·B_S·ε·V0_inf  +  √d·σ_V·ε  +  (n/2)·B_S·ε · √d·σ_V·ε
```

i.e. leading coefficient **n/2** (= `√n` from the row-ℓ² score bound × `½` softmax ×
`√n` from ℓ¹→ℓ²). The code (`fixed_pattern.py:66-70`) uses **n/4** on the first and
third terms; the prose (`prose/self-attention-lipschitz.md` §2) attributes the extra
factor ½ to "the symmetric attention structure" but transcribes no argument, and edge
SA-2 already flags this pooling as the crux. Three possible resolutions, in order of
preference:

1. **Find the halving argument** in Kim et al. (arXiv:2006.04710) or the VeriStressGT
   paper and formalize it (candidate: a sharper joint bound using the symmetry
   `S = αXXᵀ`, or a tighter `‖Δsoftmax‖₁`-based accounting replacing the
   `√n·‖·‖₂ ≥ ‖·‖₁` step). If found, the Lean constant matches the code and SA-2 closes.
2. **If no valid argument exists, this is a candidate soundness bug in
   `compute_L_attn`** — the certified sensitivity would be ~2× too small on two of three
   terms, which is in the *unsafe* direction (could ship a false-UNSAT instance,
   partially cushioned by `margin_slack`). That is precisely the class of finding this
   program exists to surface: quantify it (does the shipped `margin_slack ≥ 2`? check
   the sweep configs), add it as a **new high-severity Family-A edge**
   (`attn-Lattn-n4-pooling`), and raise it with UCLA alongside the Appendix-A
   power-iteration item. Note the suspicious numerology: `¼ = max aᵢ(1−aᵢ)` is the
   **entrywise** softmax-Jacobian bound — the exact spectral-vs-entrywise trap
   `AGENTS.md` §6 warns about, so a `¼`-seeded derivation on UCLA's side is plausible.
3. Either way, **state the Lean theorem with the constant the proof actually yields**
   (n/2 today), never with the code's constant on trust. The certificate wrapper then
   takes `hLattn : L_attn_code ≥ derived_bound` as an explicit hypothesis-edge if the
   gap persists.

**F2-C.4 — what the gap condition turns out to be.** Because `lipschitzWith_softmax` is
*global*, the C.1–C.3 chain certifies the margin condition **without** the gap/pattern
condition — `1−μ > 4ε√d + 2ε²d` is a difficulty-shaping device (locks the argmax
pattern, keeps softmax in its saturated regime), not a soundness prerequisite of the
margin certificate. Formalizing C makes that precise; document it in the SelfAttention
README and consider downgrading edge `attn-fixed-pattern-gap`'s role accordingly
(`gap_implies_stability_margin` stays as the SA-3 anchor; a full `PatternFixed`
predicate becomes optional and can be dropped from the roadmap unless UCLA's paper
argument turns out to *need* pattern-fixedness for resolution 1 above).

---

## Part II — F4b: wiring `ibp_network_sound` into the MILP thread

New file suggestion: `ExactMILP/Network.lean` with `import IntervalBounds` (this import
is itself the point — today no Lean file consumes `IntervalBounds` from the MILP side).

### F4b-1 — concretize `advSet`

```lean
open VeriStressGT.IntervalBounds

/-- The TRUE adversarial set of `net` w.r.t. certified class `y`:
inputs where some competitor's logit reaches `y`'s. -/
def advSet {n : ℕ} (net : List (Layer n)) (y : Fin n) : Set (Fin n → ℝ) :=
  {x | ∃ k, k ≠ y ∧ netEval net x y ≤ netEval net x k}
```

Structural gift, worth a docstring of its own: the default `Pi` metric on
`Fin n → ℝ` **is the L∞ metric** (`nndist_pi_def`,
`Mathlib/Topology/MetricSpace/Pseudo/Pi.lean:48`; `dist_pi_le_iff` for the ≤-form). So
`Metric.infDist x₀ (advSet net y)` is *literally* the exact L∞ robustness radius `r*`
of `exact_radius.py`, and `Metric.closedBall x₀ ε` is the VNN-LIB box — the whole MILP
thread lives in the correct metric for free. (Class-targeted variant
`advSetTo net y k` with `r* = min over k` is optional; the union form above suffices for
the soundness direction.)

### F4b-2 — the geometric label-soundness theorem (fixes F4's docstring gap)

```lean
theorem robust_of_lt_infDist_advSet {n : ℕ} (net : List (Layer n))
    (x₀ : Fin n → ℝ) (y : Fin n) (ε : ℝ)
    (h : ε < Metric.infDist x₀ (advSet net y)) :
    ∀ x, dist x x₀ ≤ ε → ∀ k, k ≠ y → netEval net x k < netEval net x y := by
  intro x hx k hk
  by_contra hle
  exact absurd ((Metric.infDist_le_dist_of_mem
      (⟨k, hk, not_lt.mp hle⟩ : x ∈ advSet net y)).trans
      (by rwa [dist_comm])) (not_le.mpr h)
```

Then restate `label_sound_of_optimal` as a corollary over this concrete set:
premise `hoptimal : Metric.infDist x₀ (advSet net y) = rStar` (same MILP-2 edge, same
seam), conclusion the *geometric* statement above with `ε < rStar` — the docstring
("the closed ε-box contains no adversary") finally matches the theorem. Keep the old
name; the abstract-`advSet` version can be deleted (it was a rewrite).

### F4b-3 — the `milp-rmax-clamp` edge as a lemma

Mathlib nearly has it: `Metric.infDist_inter_closedBall_of_mem`
(`Mathlib/Topology/MetricSpace/HausdorffDistance.lean:716`) —
`y ∈ s → infDist x (s ∩ closedBall x (dist y x)) = infDist x s`. Generalize the radius:

```lean
/-- If some adversary lies within the search radius R, clamping the search to the
R-ball does not change the infimum distance — the formal content of "Rmax was
non-binding" (edge milp-rmax-clamp). -/
theorem infDist_inter_closedBall_of_exists_mem_ball
    {E : Type*} [PseudoMetricSpace E] (s : Set E) (x₀ : E) {R : ℝ}
    (hy : ∃ y ∈ s, dist y x₀ ≤ R) :
    Metric.infDist x₀ (s ∩ Metric.closedBall x₀ R) = Metric.infDist x₀ s
```

Proof: squeeze between `infDist_le_infDist_of_subset` (`:622`, needs the nonempty
witness from `hy`) and `infDist_inter_closedBall_of_mem` at radius `dist y x₀ ≤ R`
(nested balls ⟹ nested intersections ⟹ inequalities both ways; mind `dist y x₀` vs
`dist x₀ y` — the Mathlib lemma is stated with `dist y x`). Interpretation for the
yaml edge: OPTIMAL with incumbent `rStar < Rmax` supplies the witness, so the
box-restricted infimum the MILP computes equals the true `r*`. Companion freebie:
`advSet ∩ closedBall x₀ Rmax = ∅ → ∀ ε < Rmax, robust` — the formal meaning of a Gurobi
INFEASIBLE verdict, and it sidesteps the `infDist ∅ = 0` artifact (AUDIT F9) for this
thread.

### F4b-4 — the actual IBP wiring: per-stage bounds validity

`ibp_network_sound` speaks only about the *final* output; the MILP needs the
*intermediate* pre-activations inside their propagated boxes. Refactor rather than
duplicate — prove the every-stage version, then re-derive the existing theorem from it
(API stays stable; the axiom audit gains one name):

```lean
/-- Every intermediate value of the true trace lies in its propagated box.
The every-stage strengthening of `ibp_network_sound`; the MILP encoding's
`l ≤ s ≤ u` premises are its instances. -/
theorem netTrace_mem_netBoxes {n : ℕ} (net : List (Layer n)) (l u x : Fin n → ℝ)
    (hlx : ∀ i, l i ≤ x i) (hxu : ∀ i, x i ≤ u i) :
    List.Forall₂ (fun (v : Fin n → ℝ) (b : (Fin n → ℝ) × (Fin n → ℝ)) =>
        ∀ i, b.1 i ≤ v i ∧ v i ≤ b.2 i)
      (netTrace net x) (netBoxes net l u)
```

with `netTrace`/`netBoxes` the evident `List`-recursions mirroring `netEval`/`netProp`
(`x :: netTrace rest (L.eval x)` etc.). Same induction as today, each step
`Layer.sound`. Corollary at every ReLU stage: the pre-activation `s` satisfies the
stage's `propLower/propUpper` bounds, so **`bigM_relu_complete l u s` applies with its
`hls`/`hsu` premises discharged by `Layer.sound` — the sentence the READMEs have been
claiming, now a Lean fact.** If you go straight to F4b-5, this theorem is absorbed into
the completeness induction and you may skip the standalone `Forall₂` form — but it is
the minimal artifact if F4b-5 is deferred, so land it first regardless.

### F4b-5 — full Theorem A: the network big-M relation (optional but recommended)

Avoid trace-list alignment pain by defining feasibility as a recursion that threads the
box exactly like `netProp` — affine layers are equality constraints (no choice), ReLU
layers introduce the `(z, a)` big-M witnesses:

```lean
/-- `BigMReach net l u v out`: from intermediate value `v` (with box `[l,u]`),
some big-M–feasible assignment of the remaining layers reaches output `out`.
Affine layers are equalities; ReLU layers use the four big-M constraints with
the `netProp`-propagated bounds. -/
def BigMReach {n : ℕ} : List (Layer n) → (Fin n → ℝ) → (Fin n → ℝ) →
    (Fin n → ℝ) → (Fin n → ℝ) → Prop
  | [], _, _, v, out => out = v
  | (Layer.affine W b) :: rest, l, u, v, out =>
      BigMReach rest ((Layer.affine W b).propLower l u)
        ((Layer.affine W b).propUpper l u) (W.mulVec v + b) out
  | Layer.relu :: rest, l, u, v, out =>
      ∃ z a : Fin n → ℝ,
        (∀ i, (a i = 0 ∨ a i = 1) ∧ 0 ≤ z i ∧ v i ≤ z i
          ∧ z i ≤ u i * a i ∧ z i ≤ v i - l i * (1 - a i))
        ∧ BigMReach rest (Layer.relu.propLower l u) (Layer.relu.propUpper l u) z out
```

Two theorems, one induction each:

```lean
/-- Encoding SOUNDNESS: any feasible assignment computes the true network output.
Per-neuron `bigM_relu_faithful`; note it needs NO bounds validity — the big-M
constraints alone pin z = max 0 s. -/
theorem bigMReach_sound … : BigMReach net l u x out → out = netEval net x

/-- Encoding COMPLETENESS: the true trace is feasible — THE F4b WIRING.
The ReLU step is `bigM_relu_complete`, its `l ≤ s ≤ u` premises supplied by
`Layer.sound` (i.e. by IBP box validity propagating along the induction). -/
theorem bigMReach_complete … (hlx : ∀ i, l i ≤ x i) (hxu : ∀ i, x i ≤ u i) :
    BigMReach net l u x (netEval net x)
```

The asymmetry is worth a display comment: *soundness is bounds-free, completeness is
where IBP earns its keep* — that is the precise sense in which
`ibp_network_sound`/`Layer.sound` "discharges the `(l,u)` validity hypothesis of the
exact-MILP oracle." Capstone corollary (prose Theorem A minus Gurobi):

```lean
theorem bigM_feasible_iff_netEval {n} (net) (x₀ : Fin n → ℝ) (R : ℝ)
    (x : Fin n → ℝ) (hx : dist x x₀ ≤ R) (out) :
    BigMReach net (fun i => x₀ i - R) (fun i => x₀ i + R) x out ↔ out = netEval net x
```

(the box hypotheses come from `dist_pi_le_iff` + `Real.dist_eq`), and one more
display corollary equating "feasible ∧ misclassified" with
`Metric.closedBall x₀ R ∩ advSet net y` — which, chained with F4b-2/3, is the complete
formal story: *big-M feasible set = true adversaries in the search box; OPTIMAL
non-clamped value = `infDist` to `advSet`; `ε < r*` ⟹ UNSAT label correct.* The
remaining unformalized trust is exactly "Gurobi returns the true optimum of the stated
MILP" plus float vs real arithmetic — i.e. edges `milp-incomplete-label` and
`float32-export`, which is where the edge accounting says it should be.

### Bookkeeping after both parts land

- Add every new public theorem to the axiom-audit file and re-run it.
- `formalization.yaml`: `milp-rmax-clamp` gains a real Lean anchor
  (`infDist_inter_closedBall_of_exists_mem_ball`); update the F2 edge anchors from the
  deleted assumed-Lipschitz wrappers to the derived certificates; if F2-C.3 resolution 2
  materializes, add `attn-Lattn-n4-pooling` (Family A, high).
- READMEs: SelfAttention (derived vs assumed status flips; gap-condition role per
  F2-C.4), ExactMILP (+`Network.lean` table rows), IntervalBounds
  (+`netTrace_mem_netBoxes`), ForMathlib (+`SoftmaxLipschitz.lean` as the packaged
  Mathlib candidate with the Jacobian bound).
- `AGENTS.md` §9: the "known open structural gap" paragraph retires when F2-A lands
  (linear case) and F2-C lands (softmax case); replace with the `n/4` question status.
