# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Lean 4 formalization of a single theorem, `adaptivity_gap`: for `a, b ∈ [0,1]` with `a ≤ b` and `a + b ≤ 1`, at least one of the three costs `C₂ b`, `C₃ a b`, `C₆ a b` is `≤ (6/5) · min (A_a a b) (A_b a b)`. A witness `tight` shows the `6/5` constant is achieved at `b = 1/2`, `a = 0`.

Toolchain: `leanprover/lean4:v4.30.0-rc2` (pinned in `lean-toolchain`). Depends on `mathlib` via Lake.

## Build / check

```sh
lake build           # builds the library + executable; this is also how you check the proofs
lake exe adaptivity  # runs the (trivial) executable entry point
```

There is no test suite. Proof checking *is* the test: `lake build` must succeed. First build after a fresh clone will fetch Mathlib and take a long time; subsequent builds are incremental.

To check just one file without building the exe, `lake env lean Main.lean` works.

## Layout

The repo looks like a stock `lake new` scaffold, but nearly all real content lives in one file:

- [Main.lean](Main.lean) — the entire proof (~520 lines). Self-contained except for `import Mathlib`. Sets `maxHeartbeats 8000000` and `maxRecDepth 4000` at the top because several `nlinarith`/`ring` goals are expensive; do not lower these without checking every lemma still elaborates. The whole file is inside a `noncomputable section`.
- [Adaptivity.lean](Adaptivity.lean) + [Adaptivity/Basic.lean](Adaptivity/Basic.lean) — empty scaffold (`def hello := "world"`). The `lean_lib` target in [lakefile.toml](lakefile.toml) exists only so `lake build` picks up the exe root `Main`. Do not put new proof content here unless you are actually modularizing — `Main.lean` is the source of truth.

## Proof architecture

Read `Main.lean` top-to-bottom; the sections (delimited by `═══` banners) correspond to the proof's logical structure:

1. **Cubic discriminant** — `two_roots_discrim_nonneg`: if a cubic has two distinct real roots, its discriminant is `≥ 0`. Used contrapositively in case 2.
2. **Definitions** — `A_a`, `A_b` (adaptive costs), `C₂`, `C₃`, `C₆` (candidate bounds), and `N₃`, `N₆` (denominator-cleared numerators of `C_i - (6/5)·A_b`).
3. **Denominator clearing** — `C₃_le_iff_N₃`, `C₆_le_iff_N₆` reduce rational inequalities to polynomial ones via `field_simp; ring`.
4. **Three cases on `b`**, which is the load-bearing split:
   - `case1` (`b ≤ 1/2`): direct polynomial factoring; `C₂ b ≤ (6/5)·A_b`.
   - `case2` (`1/2 < b ≤ 5/6`): the hard case. Assumes both `N₃ > 0` and `N₆ > 0` for contradiction, uses IVT twice to produce two distinct roots of `N₆(·, b)`, invokes `two_roots_discrim_nonneg`, and contradicts it with `N₆_disc_neg` — which itself is proved by a Bernstein-basis SOS certificate (degree-16 expansion with explicit rational coefficients). The inner "remainder is nonpositive" argument splits further on signs of `ρ₁` and `5b²+4b-4` and uses two more Bernstein certificates on sub-intervals `[1/2, 2/3]` and `[2/3, 5/6]`.
   - `case3` (`5/6 < b < 1`): monotonicity of `N₆(·, b)` on `[0, 1-b]` via a concave-parabola lemma (`concave_ge`) plus `N₆(1-b, b) < 0`.
5. **Assembly** — `bound_lower_half` dispatches the three cases; `adaptivity_gap` handles the `b = 0` and `b = 1` boundary cases (where the expressions are division-by-zero junk but trivially satisfy the bound at `a = 0`) and reduces `min` to `A_b` via `A_b_le_A_a`.

The Bernstein certificates in `N₆_disc_neg`, the `hRtI` sub-lemma, and the `hG` sub-lemma are almost certainly computer-generated — the rational coefficients are not human-derived. If one breaks after editing surrounding polynomials, regenerate rather than hand-patch.

## Editing conventions to match

- Polynomial identities are closed with `unfold ...; field_simp; ring` or `unfold ...; ring`. When `ring` fails, the usual culprit is a sign error in the claimed identity, not a `ring` bug.
- Inequalities over polynomials are closed with `nlinarith` given enough hints (`sq_nonneg ...`, `mul_nonneg ...`, `mul_pos ...`). Hints matter; `nlinarith` without them will often time out at these heartbeat budgets.
- `push Not` appears in case 2 — this is `push_neg` written oddly (tactic is case-insensitive in this version). Preserve the existing spelling when editing nearby so diffs stay minimal.

## CI

[.github/workflows/lean_action_ci.yml](.github/workflows/lean_action_ci.yml) just runs `leanprover/lean-action@v1` on push/PR — a green CI run means `lake build` succeeded on Ubuntu.
