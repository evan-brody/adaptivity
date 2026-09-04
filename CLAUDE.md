# CLAUDE.md

Guidance for Claude Code (claude.ai/code) working in this repository.

## What this repo is

A Lean 4 formalization of two adaptivity-gap theorems for the **Unlimited-Flips
Unanimous Vote problem**. Nothing else: no application code, no library API, no
test suite. Each theorem says that on the domain

```
0 ≤ p₁ ≤ pₙ ≤ 1        and        p₁ + pₙ ≤ 1
```

some *nonadaptive* strategy comes close to the adaptive cost `Aₙ p₁ pₙ`, where
`Aₙ p₁ pₙ = pₙ / (1 - p₁) + 1 / pₙ` (identical in both files):

| File | Theorem | Bound |
| --- | --- | --- |
| [MulAdaptivityGap.lean](MulAdaptivityGap.lean) | `mul_adaptivity_gap` | `min (C₁, C₂, C₃) ≤ 1.2 * Aₙ` |
| [AddAdaptivityGap.lean](AddAdaptivityGap.lean) | `add_adaptivity_gap` | `min (C₁, C₂, C₄) ≤ 1/2 + Aₙ` |

The multiplicative constant `1.2` is tight: it is attained at `pₙ = 1/2`,
`p₁ = 0`. Neither file contains `sorry`.

The `C₃` / `C₄` mismatch between the two rows is deliberate — see
[Keeping the two files parallel](#keeping-the-two-files-parallel).

Toolchain `leanprover/lean4:v4.30.0-rc2`, pinned in `lean-toolchain`; the only
dependency is Mathlib, via Lake.

## Building and checking

```sh
lake build                    # both files — this is the only check that matters
lake build MulAdaptivityGap   # one file at a time
lake build AddAdaptivityGap
```

Proof checking *is* the test suite. There is no executable target and no
`Main.lean`; `lakefile.toml` declares two `lean_lib`s and puts both in
`defaultTargets`.

The first build after a fresh clone downloads Mathlib and is slow. After that a
full rebuild of both files takes well under a minute (roughly 6s for the
additive file, 20s for the multiplicative one), so **run `lake build` after
every edit** — there is no cheaper signal.

## The two files

Both are self-contained: each imports only `Mathlib`, shares no module with the
other, and wraps everything in a `noncomputable section`.

[MulAdaptivityGap.lean](MulAdaptivityGap.lean), ~690 lines, opens with

```lean
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
```

Both are load-bearing for the large `nlinarith` / `ring` goals in `case2` and
`N₆_disc_neg`. Do not lower them without re-elaborating the whole file.

[AddAdaptivityGap.lean](AddAdaptivityGap.lean), ~415 lines, elaborates at the
default budgets. Do not add `set_option` lines to it.

## Keeping the two files parallel

The files are deliberately symmetric, and that symmetry is worth preserving
when editing:

- Module docstring: `# <Multiplicative|Additive> adaptivity gap for the
  Unlimited-Flips Unanimous Vote problem`, then the bound, the statement, the
  case split, and a note about the division-free polynomial core.
- Section headers are `/-! ## Title -/`, drawn from a shared vocabulary:
  *Main definitions*, *Denominator clearing*, *Case 1* / *Case 2* / *Case 3*,
  *Assembly*.
- `Aₙ`, `C₁` and `C₂` are defined identically in both. `C₁` ignores its first
  argument (`def C₁ (_p₁ pₙ : ℝ)`) in both files so that all three candidates
  have the same arity and the two main theorems read alike.
- The two main theorems take the same hypotheses, same order, same names:
  `(hp₁0 : 0 ≤ p₁) (hp₁pₙ : p₁ ≤ pₙ) (hs : p₁ + pₙ ≤ 1) (hpₙ1 : pₙ ≤ 1)`.

Two differences are intentional — leave them alone:

- **The candidate subscripts are intentional, not a typo or an oversight.**
  The third candidate is `C₃` in the multiplicative file and `C₄` in the
  additive one, and both keep those names. The subscripts come from different
  strategy enumerations: in the additive setting `C₁, C₂, C₄` were derived as
  `S_2, S_3, S_5` in the slack analysis, so the gap at `C₃` is meaningful — it
  marks a strategy that does not appear in the final case analysis. Do **not**
  rename `C₄` to `C₃`, renumber either file's candidates, or otherwise "fix"
  the mismatch in the name of symmetry; the same goes for `C₄_le_iff_L₅` and
  every other declaration whose name carries the subscript.
- The polynomial witnesses are `N₃, N₆` in the multiplicative file (numerators,
  where the goal is `N_i ≤ 0`) and `L₂, L₃, L₅` in the additive one (slacks,
  where the goal is `0 ≤ L_i`). They are not the same construction and should
  not be given matching names.

## Multiplicative proof (MulAdaptivityGap.lean)

Sections, in file order:

1. **Main definitions** — `Aₙ`; the candidates `C₁`, `C₂`, `C₃`; the
   denominator-cleared numerators `N₃`, `N₆`; and the cubic machinery
   `evalCubic`, `cubicDiscrim`, `two_roots_discrim_nonneg` (a cubic with two
   distinct real roots has discriminant `≥ 0` — used contrapositively in
   case 2).
2. **Denominator clearing** — `C₂_le_iff_N₃` and `C₃_le_iff_N₆` prove
   `C_i ≤ 1.2 * Aₙ ↔ N_i ≤ 0` via the identity `N_i = (C_i - 1.2·Aₙ) · P` with
   `P > 0` the product of cleared denominators (`field_simp; ring`, then
   `nlinarith` to transfer signs both ways).
3. **Adaptive cost** — `Aₙ_mono`, monotonicity in the first argument, used by
   case 1 to reduce to the `p₁ = 0` endpoint.
4. **Case 1** (`pₙ ≤ 1/2`) — `case1`: `C₁` wins, by direct polynomial
   factoring after the `Aₙ_mono` reduction.
5. **Supporting lemmas** — `concave_ge` (a concave parabola on an interval is
   bounded below by its endpoints), `N₆_1mpₙ_neg` (`N₆(1-pₙ, pₙ) < 0`),
   `N₆_eq_evalCubic`, `N₆_leading_ne_zero`, and `N₆_disc_neg`, which bounds the
   cubic discriminant away from zero on `[1/2, 5/6]` using a Bernstein-basis
   SOS certificate (a degree-16 expansion with explicit rational coefficients).
6. **Case 2** (`1/2 < pₙ ≤ 5/6`) — `case2`, the hard case, ~200 lines. By
   contradiction from `N₃ > 0` and `N₆ > 0`: IVT produces a root `a₁` of `N₃`,
   a polynomial identity `25(2pₙ-1)²·N₆ = Qt·N₃ + Rt` transfers the sign to
   `N₆(a₁)`, IVT twice more produces two distinct roots of `N₆(·, pₙ)`, and
   `two_roots_discrim_nonneg` then contradicts `N₆_disc_neg`. The inner
   "remainder is nonpositive" step splits on the signs of `ρ₁` and
   `5pₙ² + 4pₙ - 4` and uses two more Bernstein certificates, on `[1/2, 2/3]`
   and `[2/3, 5/6]`. The nine steps are numbered in the `case2` docstring and
   the numbering is repeated in the proof body — keep the two in sync.
7. **Case 3** (`5/6 < pₙ < 1`) — `case3`: `N₆(·, pₙ)` is monotone on
   `[0, 1-pₙ]` (`Q_div`, `Q_nonneg`, `N₆_mono`, via `concave_ge`), and
   `N₆(1-pₙ, pₙ) < 0`, so `C₃` wins.
8. **Assembly** — `bound_lower_half` dispatches the three cases on the interior
   `0 < pₙ < 1`; `mul_adaptivity_gap` adds the `pₙ = 0` and `pₙ = 1`
   boundaries, where the hypotheses force `p₁ = 0` and the costs are
   division-by-zero junk that `norm_num` disposes of.

## Additive proof (AddAdaptivityGap.lean)

1. **Main definitions** — `Aₙ`; the candidates `C₁`, `C₂`, `C₄`; the slack
   polynomials `L₂`, `L₃`, `L₅` and their helpers `M`, `R₃`, `N₅`, `P`, `g`,
   `E`. Each `L_i` is `-2·(denom)·(C_i - Aₙ - 1/2)`, so `0 ≤ L_i` is exactly
   the bound for candidate `i`.
2. **SOS certificates** — the scalar positivity facts the case analysis
   consumes: `M_pos`, `quad_6_8_3_pos`, `quad_6_4_25_pos`, `P_pos`, `g_nonneg`,
   `quartic_nonneg`.
3. **Polynomial identities** — `L₃_factorization`, `concavity_master_identity`,
   `neg_E_decomp`, `L₃_complete_square`, all closed by `ring`. Note the comment
   above `concavity_master_identity`: `M` must be unfolded *last*, because `E`
   mentions `M` in its body.
4. **Case 1** (`pₙ ≤ 1/2`) — `L₂_nonneg_of_q_le_half`, direct SOS on `L₂`,
   itself split at `pₙ = 1/3`. `C₁` wins.
5. **Case 2** (`1/2 < pₙ ≤ 2/3`) — `L₃_nonneg_of_q_le_two_thirds`, splitting on
   the sign of `pₙ² + 3pₙ - 2`. The easy branch (`L₃_nonneg_case1`) is termwise
   nonnegative; the hard branch (`L₃_nonneg_case2`) derives `pₙ ≥ 27/50`, uses
   a Taylor expansion of a cubic at `27/50`, and finishes with
   `L₃_complete_square`. `C₂` wins.
6. **Case 3** (`2/3 < pₙ`) — a further split: either `0 ≤ L₃` and `C₂` wins, or
   `L₃ < 0`, which forces `(1-pₙ)² ≤ p₁·M` (`Delta_nonneg_of_L₃_nonpos`,
   step 3a) and hence `0 ≤ L₅` (`L₅_nonneg_of_Delta_nonneg`, step 3b), so `C₄`
   wins.
7. **Polynomial core** — `polynomial_core` performs the dispatch above and is
   entirely division-free: `0 ≤ L₂ ∨ 0 ≤ L₃ ∨ 0 ≤ L₅`.
8. **Denominator clearing** — `C₁_le_iff_L₂`, `C₂_le_iff_L₃`, `C₄_le_iff_L₅`
   (built on the `C_*_normalized` lemmas plus the two small division helpers)
   convert the polynomial conclusions back to `C_i - Aₙ ≤ 1/2`.
9. **Assembly** — `add_adaptivity_gap` handles the `pₙ = 0` and `pₙ = 1`
   boundaries, then delegates to `polynomial_core`.

## Conventions to match when editing

- **Bernstein certificates are machine-generated.** The explicit rational
  coefficients in `N₆_disc_neg` and in the `hRtI` / `hG` sub-proofs inside
  `case2` are not human-derived. If one breaks after a surrounding polynomial
  changes, regenerate the certificate; do not hand-patch coefficients.
- **Polynomial identities** are closed with `unfold …; field_simp; ring` or
  `unfold …; ring`. When `ring` fails here, the cause is nearly always a sign
  error in the claimed identity, not a `ring` limitation.
- **Polynomial inequalities** are closed with `nlinarith` plus explicit hints
  (`sq_nonneg …`, `mul_nonneg …`, `mul_pos …`). The hints are what make these
  goals finish; `nlinarith` without them will often exhaust even the raised
  heartbeat budget.
- **`push Not`** appears throughout both files. It is `push_neg` written oddly
  (the tactic name is case-insensitive in this version). Keep the existing
  spelling in nearby edits so diffs stay small.
- **Line numbers are cited in [README.md](README.md)'s "Where things are"
  table.** Update it whenever declarations move.

## CI

[.github/workflows/lean_action_ci.yml](.github/workflows/lean_action_ci.yml)
runs `leanprover/lean-action@v1` on push, PR, and manual dispatch. A green run
means `lake build` succeeded on Ubuntu — same check as running it locally.
