import Mathlib

/-!
# Adaptivity gap: `min (C₁, C₂, C₃) ≤ (1.2) · Aₙ`

This file proves a single result, `adaptivity_gap`, bounding three candidate
(non-adaptive) costs `C₁ pₙ`, `C₂ p₁ pₙ`, `C₃ p₁ pₙ` against the adaptive
cost `Aₙ p₁ pₙ` for `0 ≤ p₁ ≤ pₙ`, `p₁ + pₙ ≤ 1`. The constant `1.2` is
tight, attained at `pₙ = 1/2`, `p₁ = 0`.

The proof splits on the value of `pₙ`:
* `pₙ ≤ 1/2`  — `C₁` works (`case1`), direct polynomial factoring.
* `1/2 < pₙ ≤ 5/6` — the hard case (`case2`): a double-IVT + cubic
  discriminant argument, with the discriminant's negativity shown by a
  Bernstein SOS certificate (`N₆_disc_neg`).
* `5/6 < pₙ < 1` — `C₃` works (`case3`) via monotonicity of `N₆(·, pₙ)`.

The `noncomputable section` is because of the rationals-as-reals; the high
heartbeat/recDepth budgets are load-bearing for the larger `nlinarith` /
`ring` calls below.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open Real

-- ═══════════════════ Main definitions ═══════════════════

-- `Aₙ` is the adaptive cost the three candidates are measured against.
def Aₙ (p₁ pₙ : ℝ) : ℝ := pₙ / (1 - p₁) + 1 / pₙ

-- The three candidate non-adaptive costs. The goal is that for every
-- `(p₁, pₙ)` at least one of `C₁, C₂, C₃` is `≤ (1.2)·Aₙ`.
def C₁ (pₙ : ℝ) : ℝ := 1 / pₙ + pₙ / (1 - pₙ)
def C₂ (p₁ pₙ : ℝ) : ℝ := 1 + p₁ / (1 - pₙ) + (1 - p₁) / pₙ
def C₃ (p₁ pₙ : ℝ) : ℝ :=
  1 + pₙ * (1 + p₁) / (1 - p₁ * pₙ) + (1 - pₙ) * (2 - p₁) / (p₁ + pₙ - p₁ * pₙ)

-- `N₃` and `N₆` are `C₂ - (1.2)·Aₙ` and `C₃ - (1.2)·Aₙ` with positive
-- denominators cleared (see `C₂_le_iff_N₃`, `C₃_le_iff_N₆`). The "≤ (1.2)·Aₙ"
-- inequalities become purely polynomial statements `N₃ ≤ 0`, `N₆ ≤ 0`.
def N₃ (p₁ pₙ : ℝ) : ℝ :=
  5 * p₁ ^ 2 * (1 - 2 * pₙ) + p₁ * (5 * pₙ ^ 2 + 4 * pₙ - 4) +
  (6 * pₙ ^ 3 - 11 * pₙ ^ 2 + 6 * pₙ - 1)
def N₆ (p₁ pₙ : ℝ) : ℝ :=
  5*p₁^3*pₙ^3 + p₁^3*pₙ^2 - 6*p₁^3*pₙ - 6*p₁^2*pₙ^4 - 4*p₁^2*pₙ^3 - 2*p₁^2*pₙ^2 +
  6*p₁^2 + 6*p₁*pₙ^4 + 6*p₁*pₙ^3 + 2*p₁*pₙ - 6*p₁ - pₙ^3 - 5*pₙ^2 + 4*pₙ

/-- Standard evaluation of the cubic `a·x³ + b·x² + c·x + d` at `x`. -/
def evalCubic (a b c d x : ℝ) : ℝ := a * x ^ 3 + b * x ^ 2 + c * x + d

/-- The classical discriminant of `a·x³ + b·x² + c·x + d`. Nonnegative iff
the cubic has three real roots (counted with multiplicity). -/
def cubicDiscrim (a b c d : ℝ) : ℝ :=
  18 * a * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 27 * a ^ 2 * d ^ 2

/-- Two distinct real roots force the discriminant to be `≥ 0`. Used
contrapositively in `case2`: if we can show the discriminant is strictly
negative on a `pₙ`-interval, then `N₆(·, pₙ)` cannot have two distinct roots
there, contradicting an IVT-produced pair of roots.

Strategy: write `c` and `d` in terms of the two known roots (Vieta-style,
with the third root `r₃ = -(b/a) - r₁ - r₂` eliminated), then observe
that after those substitutions the discriminant is a perfect square. -/
lemma two_roots_discrim_nonneg (a b c d r₁ r₂ : ℝ) (ha : a ≠ 0) (hr : r₁ ≠ r₂)
    (h₁ : evalCubic a b c d r₁ = 0) (h₂ : evalCubic a b c d r₂ = 0) :
    0 ≤ cubicDiscrim a b c d := by
  have hc : c = a * (r₁ * r₂ + r₁ * (-(b / a) - r₁ - r₂) + r₂ * (-(b / a) - r₁ - r₂)) := by
    unfold evalCubic at *
    cases lt_or_gt_of_ne hr <;> cases lt_or_gt_of_ne ha <;>
      nlinarith [mul_div_cancel₀ (b : ℝ) ha, mul_self_nonneg (r₁ - r₂)]
  have hd : d = -a * (r₁ * r₂ * (-(b / a) - r₁ - r₂)) := by
    unfold evalCubic at *
    cases lt_or_gt_of_ne hr <;> cases lt_or_ge r₁ 0 <;> cases lt_or_ge r₂ 0 <;>
      nlinarith [mul_div_cancel₀ b ha]
  -- The discriminant equals a perfect square after substitution
  have key : cubicDiscrim a b c d =
      (a ^ 2 * (r₁ - r₂) * (r₁ - (-(b / a) - r₁ - r₂)) *
       (r₂ - (-(b / a) - r₁ - r₂))) ^ 2 := by
    unfold cubicDiscrim; rw [hc, hd]; field_simp; ring
  rw [key]; exact sq_nonneg _

-- ═══════════════════ Denominator clearing ═══════════════════
--
-- These two lemmas witness the equivalence between the rational bound
-- `C_i ≤ (1.2)·Aₙ` and the polynomial statement `N_i ≤ 0`. The trick is
-- the identity `N_i = (C_i - (1.2)·Aₙ) · P` where `P > 0` is the product
-- of the cleared denominators; `field_simp; ring` discharges the identity
-- and `nlinarith` uses `P > 0` to transfer signs in both directions.

lemma C₂_le_iff_N₃ {p₁ pₙ : ℝ} (hpₙ0 : 0 < pₙ) (hpₙ1 : pₙ < 1) (hp₁1 : p₁ < 1) :
    C₂ p₁ pₙ ≤ (1.2) * Aₙ p₁ pₙ ↔ N₃ p₁ pₙ ≤ 0 := by
  have h1pₙ : (0 : ℝ) < 1 - pₙ := by linarith
  have h1p₁ : (0 : ℝ) < 1 - p₁ := by linarith
  have hP : (0 : ℝ) < 5 * pₙ * (1 - pₙ) * (1 - p₁) :=
    mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 5) hpₙ0) h1pₙ) h1p₁
  have hid : N₃ p₁ pₙ = (C₂ p₁ pₙ - (1.2) * Aₙ p₁ pₙ) *
      (5 * pₙ * (1 - pₙ) * (1 - p₁)) := by
    unfold N₃ C₂ Aₙ; field_simp; ring
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma C₃_le_iff_N₆ {p₁ pₙ : ℝ} (hp₁0 : 0 ≤ p₁) (hpₙ0 : 0 < pₙ) (hpₙ1 : pₙ < 1)
    (hp₁1 : p₁ < 1) :
    C₃ p₁ pₙ ≤ (1.2) * Aₙ p₁ pₙ ↔ N₆ p₁ pₙ ≤ 0 := by
  have h1 : (0 : ℝ) < 1 - p₁ * pₙ := by nlinarith
  have h2 : (0 : ℝ) < p₁ + pₙ - p₁ * pₙ := by nlinarith
  have h3 : (0 : ℝ) < 1 - p₁ := by linarith
  have hP : (0 : ℝ) < 5 * pₙ * (1 - p₁ * pₙ) * (p₁ + pₙ - p₁ * pₙ) * (1 - p₁) :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 5) hpₙ0) h1) h2) h3
  have hid : N₆ p₁ pₙ = (C₃ p₁ pₙ - (1.2) * Aₙ p₁ pₙ) *
      (5 * pₙ * (1 - p₁ * pₙ) * (p₁ + pₙ - p₁ * pₙ) * (1 - p₁)) := by
    unfold N₆ C₃ Aₙ; field_simp; ring
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

-- ═══════════════════ Adaptive cost ═══════════════════
--
-- `Aₙ_mono` is used in `case1` to reduce to the `p₁ = 0` endpoint.

/-- `Aₙ` is monotone in its first argument: the difference times a
positive denominator equals `pₙ · (a₂ − a₁)`. -/
lemma Aₙ_mono {a₁ a₂ pₙ : ℝ} (hpₙ0 : 0 < pₙ) (ha₂ : a₂ < 1) (h : a₁ ≤ a₂) :
    Aₙ a₁ pₙ ≤ Aₙ a₂ pₙ := by
  have h1 : (0 : ℝ) < 1 - a₂ := by linarith
  have h2 : (0 : ℝ) < 1 - a₁ := by linarith
  suffices hsuff : 0 ≤ Aₙ a₂ pₙ - Aₙ a₁ pₙ by linarith
  have hkey : (Aₙ a₂ pₙ - Aₙ a₁ pₙ) * ((1 - a₁) * (1 - a₂)) = pₙ * (a₂ - a₁) := by
    unfold Aₙ; field_simp; ring
  have hnum : 0 ≤ pₙ * (a₂ - a₁) := mul_nonneg (le_of_lt hpₙ0) (by linarith)
  have hden : (0 : ℝ) < (1 - a₁) * (1 - a₂) := mul_pos h2 h1
  by_contra h_neg; simp only [not_le] at h_neg
  linarith [mul_neg_of_neg_of_pos h_neg hden]

-- ═══════════════════ Case 1: pₙ ≤ 1/2 ═══════════════════

/-- When `pₙ ≤ 1/2`, `C₁ pₙ` already beats `(1.2)·Aₙ p₁ pₙ`. Strategy: since
`C₁ pₙ` does not depend on `p₁`, monotonicity of `Aₙ` in `p₁` lets us reduce
to the endpoint `p₁ = 0`. At `p₁ = 0` the inequality factors as
`(2pₙ − 1)(3pₙ² + pₙ + 1) ≤ 0`, with the second factor `> 0` (complete the
square) and the first `≤ 0` by hypothesis. -/
theorem case1 {p₁ pₙ : ℝ} (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ < 1) (hpₙ0 : 0 < pₙ)
    (hpₙ1 : pₙ ≤ 1/2) : C₁ pₙ ≤ (1.2) * Aₙ p₁ pₙ := by
  have hpₙ1' : (0 : ℝ) < 1 - pₙ := by linarith
  -- Reduce to `p₁ = 0` using `Aₙ` monotonicity.
  suffices h0 : C₁ pₙ ≤ (1.2) * Aₙ 0 pₙ by
    linarith [mul_le_mul_of_nonneg_left (Aₙ_mono hpₙ0 hp₁1 hp₁0) (by norm_num : (0:ℝ) ≤ 1.2)]
  -- Polynomial identity: `(C₁ − (1.2)Aₙ) · positive = (2pₙ−1)(3pₙ²+pₙ+1)`.
  suffices hprod : (C₁ pₙ - (1.2) * Aₙ 0 pₙ) * (5 * pₙ * (1 - pₙ)) =
      (2*pₙ - 1) * (3*pₙ^2 + pₙ + 1) by
    have hden : (0 : ℝ) < 5 * pₙ * (1 - pₙ) :=
      mul_pos (mul_pos (by norm_num : (0:ℝ) < 5) hpₙ0) hpₙ1'
    have hnum : (2*pₙ - 1) * (3*pₙ^2 + pₙ + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by nlinarith [sq_nonneg (pₙ + 1/6)])
    by_contra h_neg; simp only [not_le] at h_neg
    linarith [mul_pos (show (0:ℝ) < C₁ pₙ - 1.2 * Aₙ 0 pₙ by linarith) hden]
  unfold C₁ Aₙ; field_simp; ring

-- ═══════════════════ Parabola lemma ═══════════════════

/-- Concave parabola bound: if `c ≤ 0` (downward-opening or linear) and the
quadratic is nonneg at both endpoints `x₁`, `x₂`, then it is nonneg on the
whole interval. Used in `case3` to extend `Q_div`'s endpoint nonnegativity
to `[0, 1-pₙ]`. Proof is the standard convex-combination identity, cleared
by `ring`. -/
lemma concave_ge {c d e x₁ x₂ x : ℝ} (hc : c ≤ 0)
    (h1 : x₁ ≤ x) (h2 : x ≤ x₂)
    (hf1 : 0 ≤ c*x₁^2 + d*x₁ + e) (hf2 : 0 ≤ c*x₂^2 + d*x₂ + e) :
    0 ≤ c*x^2 + d*x + e := by
  by_cases heq : x₁ = x₂
  · have hx : x = x₁ := le_antisymm (by linarith) h1; rw [hx]; exact hf1
  · have hlt : (0 : ℝ) < x₂ - x₁ := by
      cases lt_or_eq_of_le (show x₁ ≤ x₂ by linarith) with
      | inl h => linarith | inr h => exact absurd h heq
    have hid : (x₂ - x₁) * (c * x^2 + d * x + e) =
        (x₂ - x) * (c * x₁^2 + d * x₁ + e) +
        (x - x₁) * (c * x₂^2 + d * x₂ + e) +
        (-c) * (x - x₁) * (x₂ - x) * (x₂ - x₁) := by ring
    have t1 := mul_nonneg (by linarith : (0:ℝ) ≤ x₂ - x) hf1
    have t2 := mul_nonneg (by linarith : (0:ℝ) ≤ x - x₁) hf2
    have t3 := mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ -c)
      (by linarith : (0:ℝ) ≤ x - x₁)) (by linarith : (0:ℝ) ≤ x₂ - x))
      (by linarith : (0:ℝ) ≤ x₂ - x₁)
    by_contra h_neg; simp only [not_le] at h_neg
    linarith [mul_neg_of_pos_of_neg hlt h_neg]

-- ═══════════════════ N₆(1−pₙ) < 0 ═══════════════════

/-- `N₆(1−pₙ, pₙ) < 0` for `0 < pₙ < 1`. Needed as a "known sign" endpoint in
case 2 (to run IVT producing a root on `[p₁, 1−pₙ]`) and in case 3 (to
upper-bound `N₆` after monotonicity). The factorization `N₆(1-pₙ, pₙ) =
-pₙ(pₙ+1)(pₙ²-pₙ+1)(11pₙ²-16pₙ+6)` exposes four strictly positive factors on
`(0,1)`. Note `11pₙ² - 16pₙ + 6 > 0` via completing the square at `pₙ = 8/11`. -/
lemma N₆_1mpₙ_neg {pₙ : ℝ} (hpₙ0 : 0 < pₙ) (hpₙ1 : pₙ < 1) : N₆ (1-pₙ) pₙ < 0 := by
  have key : N₆ (1-pₙ) pₙ = -(pₙ*(pₙ+1)*(pₙ^2-pₙ+1)*(11*pₙ^2-16*pₙ+6)) := by
    unfold N₆; ring
  rw [key]
  linarith [mul_pos (mul_pos (mul_pos hpₙ0 (show (0:ℝ) < pₙ+1 by linarith))
    (show (0:ℝ) < pₙ^2-pₙ+1 by nlinarith [sq_nonneg (pₙ-1/2)]))
    (show (0:ℝ) < 11*pₙ^2-16*pₙ+6 by nlinarith [sq_nonneg (pₙ-8/11)])]

-- ═══════════════════ N₆ as evalCubic ═══════════════════
--
-- For the discriminant argument, view `N₆(·, pₙ)` as a cubic in `p₁` with
-- `pₙ`-dependent coefficients. These two lemmas package that view.

/-- `N₆(p₁, pₙ)` as a univariate cubic in `p₁`. Coefficients in decreasing
order: `5pₙ³+pₙ²−6pₙ`, `−6pₙ⁴−4pₙ³−2pₙ²+6`, `6pₙ⁴+6pₙ³+2pₙ−6`, `−pₙ³−5pₙ²+4pₙ`. -/
lemma N₆_eq_evalCubic (p₁ pₙ : ℝ) :
    N₆ p₁ pₙ = evalCubic (5*pₙ^3+pₙ^2-6*pₙ) (-6*pₙ^4-4*pₙ^3-2*pₙ^2+6)
      (6*pₙ^4+6*pₙ^3+2*pₙ-6) (-pₙ^3-5*pₙ^2+4*pₙ) p₁ := by
  unfold N₆ evalCubic; ring

/-- Leading coefficient (in `p₁`) is nonzero on `0 < pₙ < 1`, so `N₆(·, pₙ)`
is a genuine cubic. Factors as `pₙ(5pₙ+6)(pₙ−1)`. -/
lemma N₆_leading_ne_zero {pₙ : ℝ} (hpₙ0 : 0 < pₙ) (hpₙ1 : pₙ < 1) :
    5*pₙ^3+pₙ^2-6*pₙ ≠ 0 := by
  have : 5*pₙ^3+pₙ^2-6*pₙ = pₙ*(5*pₙ+6)*(pₙ-1) := by ring
  intro h; rw [this] at h
  have := mul_ne_zero (mul_ne_zero (ne_of_gt hpₙ0)
    (show (5:ℝ)*pₙ+6 ≠ 0 by linarith)) (show pₙ-1 ≠ 0 by linarith)
  exact this h

-- ═══════════════════ Discriminant < 0 (Bernstein certificate) ═══════════════════

/-- The cubic discriminant of `N₆(·, pₙ)` is strictly negative on `[1/2, 5/6]`.
This is the pivotal fact: combined with `two_roots_discrim_nonneg` it shows
`N₆(·, pₙ)` has at most one real root on this `pₙ`-range, contradicting the
two distinct roots manufactured by IVT in `case2`.

Strategy: substitute `pₙ = 1/2 + u/3` so the `pₙ`-range becomes `u ∈ [0,1]`,
then show `−(disc) − 1` equals a nonnegative combination of Bernstein
basis polynomials `uᵏ (1−u)^(16−k)` with explicit rational coefficients.
The coefficients are computer-generated — do not hand-edit. -/
lemma N₆_disc_neg {pₙ : ℝ} (hpₙ_lo : 1/2 ≤ pₙ) (hpₙ_hi : pₙ ≤ 5/6) :
    cubicDiscrim (5*pₙ^3+pₙ^2-6*pₙ) (-6*pₙ^4-4*pₙ^3-2*pₙ^2+6)
      (6*pₙ^4+6*pₙ^3+2*pₙ-6) (-pₙ^3-5*pₙ^2+4*pₙ) < 0 := by
  unfold cubicDiscrim
  -- Reparametrize `pₙ ∈ [1/2, 5/6]` as `pₙ = 1/2 + u/3` with `u ∈ [0, 1]`.
  set u := 3 * (pₙ - 1/2) with hu_def
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 := by linarith
  have h1mu : 0 ≤ 1 - u := by linarith
  have hpₙ_eq : pₙ = 1/2 + u/3 := by linarith
  -- It suffices to show `−disc ≥ 1`, i.e. disc ≤ −1 < 0.
  suffices hsuff : 1 ≤ -(18 * (5*pₙ^3+pₙ^2-6*pₙ) * (-6*pₙ^4-4*pₙ^3-2*pₙ^2+6) *
      (6*pₙ^4+6*pₙ^3+2*pₙ-6) * (-pₙ^3-5*pₙ^2+4*pₙ) -
      4 * (-6*pₙ^4-4*pₙ^3-2*pₙ^2+6)^3 * (-pₙ^3-5*pₙ^2+4*pₙ) +
      (-6*pₙ^4-4*pₙ^3-2*pₙ^2+6)^2 * (6*pₙ^4+6*pₙ^3+2*pₙ-6)^2 -
      4 * (5*pₙ^3+pₙ^2-6*pₙ) * (6*pₙ^4+6*pₙ^3+2*pₙ-6)^3 -
      27 * (5*pₙ^3+pₙ^2-6*pₙ)^2 * (-pₙ^3-5*pₙ^2+4*pₙ)^2) by linarith
  -- Bernstein-basis identity: `(−disc − 1)` is a sum of 17 products
  -- `cₖ · uᵏ · (1−u)^(16−k)`, each with `cₖ ≥ 0`.
  have hbern : -(18 * (5*pₙ^3+pₙ^2-6*pₙ) * (-6*pₙ^4-4*pₙ^3-2*pₙ^2+6) *
      (6*pₙ^4+6*pₙ^3+2*pₙ-6) * (-pₙ^3-5*pₙ^2+4*pₙ) -
      4 * (-6*pₙ^4-4*pₙ^3-2*pₙ^2+6)^3 * (-pₙ^3-5*pₙ^2+4*pₙ) +
      (-6*pₙ^4-4*pₙ^3-2*pₙ^2+6)^2 * (6*pₙ^4+6*pₙ^3+2*pₙ-6)^2 -
      4 * (5*pₙ^3+pₙ^2-6*pₙ) * (6*pₙ^4+6*pₙ^3+2*pₙ-6)^3 -
      27 * (5*pₙ^3+pₙ^2-6*pₙ)^2 * (-pₙ^3-5*pₙ^2+4*pₙ)^2) - 1 =
    (39827/1024) * (1-u)^16 + (150083/256) * u * (1-u)^15 +
    (9198857/2304) * u^2 * (1-u)^14 + (112438813/6912) * u^3 * (1-u)^13 +
    (914740163/20736) * u^4 * (1-u)^12 + (5195908745/62208) * u^5 * (1-u)^11 +
    (6978480389/62208) * u^6 * (1-u)^10 + (730348189/6912) * u^7 * (1-u)^9 +
    (74425041467/1119744) * u^8 * (1-u)^8 + (123652426291/5038848) * u^9 * (1-u)^7 +
    (57505087879/15116544) * u^10 * (1-u)^6 + (62771258831/45349632) * u^11 * (1-u)^5 +
    (392465107603/136048896) * u^12 * (1-u)^4 + (288741570409/136048896) * u^13 * (1-u)^3 +
    (95305101785/136048896) * u^14 * (1-u)^2 + (12598913125/136048896) * u^15 * (1-u) +
    (315680707/544195584) * u^16 := by rw [hpₙ_eq]; ring
  have h0 := mul_nonneg (show (0:ℝ) ≤ 39827/1024 by norm_num) (pow_nonneg h1mu 16)
  have h1 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 150083/256 by norm_num) hu0) (pow_nonneg h1mu 15)
  have h2 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 9198857/2304 by norm_num) (pow_nonneg hu0 2)) (pow_nonneg h1mu 14)
  have h3 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 112438813/6912 by norm_num) (pow_nonneg hu0 3)) (pow_nonneg h1mu 13)
  have h4 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 914740163/20736 by norm_num) (pow_nonneg hu0 4)) (pow_nonneg h1mu 12)
  have h5 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 5195908745/62208 by norm_num) (pow_nonneg hu0 5)) (pow_nonneg h1mu 11)
  have h6 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 6978480389/62208 by norm_num) (pow_nonneg hu0 6)) (pow_nonneg h1mu 10)
  have h7 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 730348189/6912 by norm_num) (pow_nonneg hu0 7)) (pow_nonneg h1mu 9)
  have h8 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 74425041467/1119744 by norm_num) (pow_nonneg hu0 8)) (pow_nonneg h1mu 8)
  have h9 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 123652426291/5038848 by norm_num) (pow_nonneg hu0 9)) (pow_nonneg h1mu 7)
  have h10 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 57505087879/15116544 by norm_num) (pow_nonneg hu0 10)) (pow_nonneg h1mu 6)
  have h11 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 62771258831/45349632 by norm_num) (pow_nonneg hu0 11)) (pow_nonneg h1mu 5)
  have h12 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 392465107603/136048896 by norm_num) (pow_nonneg hu0 12)) (pow_nonneg h1mu 4)
  have h13 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 288741570409/136048896 by norm_num) (pow_nonneg hu0 13)) (pow_nonneg h1mu 3)
  have h14 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 95305101785/136048896 by norm_num) (pow_nonneg hu0 14)) (pow_nonneg h1mu 2)
  have h15 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 12598913125/136048896 by norm_num) (pow_nonneg hu0 15)) h1mu
  have h16 := mul_nonneg (show (0:ℝ) ≤ 315680707/544195584 by norm_num) (pow_nonneg hu0 16)
  linarith

-- ═══════════════════ Case 2: 1/2 < pₙ ≤ 5/6 ═══════════════════

/-- The hard case. On `1/2 < pₙ ≤ 5/6`, at least one of `N₃(p₁, pₙ)`,
`N₆(p₁, pₙ)` is `≤ 0` (equivalently, one of `C₂`, `C₃` beats `(1.2)·Aₙ`).

Proof is by contradiction, in nine steps (marked below):
  1. `N₃(0, pₙ) ≤ 0` from a direct factorization.
  2. Assuming `N₃(p₁, pₙ) > 0`, IVT gives some `a₁ ∈ [0, p₁]` with `N₃(a₁) = 0`.
  3. A polynomial identity `25(2pₙ−1)² · N₆(x) = Qt(x)·N₃(x) + Rt(x)` holds
     for all `x`; evaluating at `a₁` kills the `N₃` term.
  4. Show `Rt(a₁) ≤ 0`. This splits on the signs of `ρ₁` (the coefficient
     of `a₁` in `Rt`) and `5pₙ²+4pₙ−4`; the hard sub-case uses another
     polynomial identity `(5pₙ²+4pₙ−4)·Rt = 5·ρ₁·(2pₙ−1)·a₁² + F(pₙ)` (again
     from `N₃(a₁) = 0`) and two Bernstein certificates on `[1/2, 2/3]`
     and `[2/3, 5/6]` to control `F(pₙ)`.
  5. Therefore `N₆(a₁, pₙ) ≤ 0`, but by assumption `N₆(p₁, pₙ) > 0`, so IVT
     produces root `r₁ ∈ [a₁, p₁]` of `N₆(·, pₙ)`.
  6. Similarly `N₆(1−pₙ, pₙ) < 0` (from `N₆_1mpₙ_neg`) and `N₆(p₁, pₙ) > 0`
     give root `r₂ ∈ [p₁, 1−pₙ]`.
  7. `r₁ ≠ r₂` (else both would equal `p₁`, forcing `N₆(p₁, pₙ) = 0`).
  8. Two distinct roots ⇒ `cubicDiscrim ≥ 0` by `two_roots_discrim_nonneg`.
  9. But `N₆_disc_neg` says the discriminant is `< 0` on `[1/2, 5/6]`.
     Contradiction. -/
theorem case2 {p₁ pₙ : ℝ} (hp₁0 : 0 ≤ p₁) (hp₁pₙ : p₁ ≤ pₙ) (hpₙ1 : pₙ < 1)
    (hpₙ_lo : (1 : ℝ) / 2 < pₙ) (hpₙ_hi : pₙ ≤ 5/6) (hs : p₁ + pₙ ≤ 1) :
    N₃ p₁ pₙ ≤ 0 ∨ N₆ p₁ pₙ ≤ 0 := by
  -- Negate the goal: assume `N₃(p₁, pₙ) > 0` and `N₆(p₁, pₙ) > 0`.
  by_contra h; simp only [not_or, not_le] at h; obtain ⟨hN₃, hN₆⟩ := h
  -- Step 1: N₃(0, pₙ) ≤ 0
  have hN₃_0 : N₃ 0 pₙ ≤ 0 := by
    have : N₃ 0 pₙ = (pₙ - 1) * (2*pₙ - 1) * (3*pₙ - 1) := by unfold N₃; ring
    rw [this]
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · linarith
  -- Step 2: IVT gives a₁ ∈ [0, p₁] with N₃(a₁) = 0
  have hN₃_cont : Continuous (fun x => N₃ x pₙ) := by unfold N₃; fun_prop
  have hconn_N₃ : IsPreconnected (Set.Icc 0 p₁) := isPreconnected_Icc
  obtain ⟨a₁, ha₁_mem, ha₁_eq⟩ := IsPreconnected.intermediate_value₂
    hconn_N₃ (Set.left_mem_Icc.mpr hp₁0) (Set.right_mem_Icc.mpr hp₁0)
    hN₃_cont.continuousOn continuousOn_const hN₃_0 (le_of_lt hN₃)
  -- ha₁_eq : N₃ a₁ pₙ = 0
  have ha₁_ge : 0 ≤ a₁ := ha₁_mem.1
  have ha₁_le : a₁ ≤ p₁ := ha₁_mem.2
  -- Step 3: Polynomial identity: 25(2pₙ-1)²·N₆ = Qt·N₃ + Rt
  have hpoly_id : ∀ x, 25 * (2*pₙ-1)^2 * N₆ x pₙ =
      (-50*x*pₙ^4+15*x*pₙ^3+65*x*pₙ^2-30*x*pₙ+35*pₙ^5-15*pₙ^4+46*pₙ^3+18*pₙ^2-84*pₙ+30) *
      N₃ x pₙ + (125*x*pₙ^7-105*x*pₙ^6+45*x*pₙ^5-29*x*pₙ^4+177*x*pₙ^3-297*x*pₙ^2+
      164*x*pₙ-30*x-210*pₙ^8+475*pₙ^7-651*pₙ^6+423*pₙ^5+11*pₙ^4-291*pₙ^3+327*pₙ^2-164*pₙ+30) := by
    intro x; unfold N₃ N₆; ring
  have hid_a₁ := hpoly_id a₁
  rw [ha₁_eq, mul_zero, zero_add] at hid_a₁
  have pₙ_term_pos : (0 : ℝ) < (2*pₙ-1) := by linarith
  -- Step 4: Rt(a₁) ≤ 0 using constraint N₃(a₁) = 0
  have h25sq : (0 : ℝ) < 25 * (2*pₙ-1)^2 := by positivity
  have hN₃_zero : 5*(1-2*pₙ)*a₁^2 + (5*pₙ^2+4*pₙ-4)*a₁ + (6*pₙ^3-11*pₙ^2+6*pₙ-1) = 0 := by
    have : N₃ a₁ pₙ = 5*a₁^2*(1-2*pₙ) + a₁*(5*pₙ^2+4*pₙ-4) + (6*pₙ^3-11*pₙ^2+6*pₙ-1) := by
      unfold N₃; ring
    linarith [ha₁_eq]
  have hRt_le : 125*a₁*pₙ^7 - 105*a₁*pₙ^6 + 45*a₁*pₙ^5 - 29*a₁*pₙ^4 + 177*a₁*pₙ^3 -
      297*a₁*pₙ^2 + 164*a₁*pₙ - 30*a₁ - 210*pₙ^8 + 475*pₙ^7 - 651*pₙ^6 + 423*pₙ^5 +
      11*pₙ^4 - 291*pₙ^3 + 327*pₙ^2 - 164*pₙ + 30 ≤ 0 := by
    -- Split on sign of ρ₁ (coefficient of a₁ in the remainder)
    by_cases hρ : 0 ≤ 125*pₙ^7-105*pₙ^6+45*pₙ^5-29*pₙ^4+177*pₙ^3-297*pₙ^2+164*pₙ-30
    · -- Case ρ₁ ≥ 0: Rt is linear-increasing in a₁ (coeff of a₁ is ρ₁ ≥ 0),
      -- so Rt(a₁) ≤ Rt(1-pₙ) since a₁ ≤ 1 - pₙ.
      -- First show Rt(1-pₙ) ≤ 0 via Rt(1-pₙ) = -pₙ·(Rt_inner) with Rt_inner ≥ 0.
      suffices h1mpₙ : -pₙ*(335*pₙ^7-705*pₙ^6+801*pₙ^5-497*pₙ^4+195*pₙ^3-183*pₙ^2+134*pₙ-30) ≤ 0 by
        have hRt_ring : 125*a₁*pₙ^7-105*a₁*pₙ^6+45*a₁*pₙ^5-29*a₁*pₙ^4+177*a₁*pₙ^3-
            297*a₁*pₙ^2+164*a₁*pₙ-30*a₁-210*pₙ^8+475*pₙ^7-651*pₙ^6+423*pₙ^5+
            11*pₙ^4-291*pₙ^3+327*pₙ^2-164*pₙ+30 =
            -pₙ*(335*pₙ^7-705*pₙ^6+801*pₙ^5-497*pₙ^4+195*pₙ^3-183*pₙ^2+134*pₙ-30) -
            (125*pₙ^7-105*pₙ^6+45*pₙ^5-29*pₙ^4+177*pₙ^3-297*pₙ^2+164*pₙ-30)*(1-pₙ-a₁) := by
          ring
        linarith [mul_nonneg hρ (show (0:ℝ) ≤ 1-pₙ-a₁ by linarith)]
      -- Rt_inner ≥ 0 on [1/2, 5/6] via degree-7 Bernstein SOS certificate
      -- with the reparametrization v = 3·(pₙ − 1/2) ∈ [0, 1].
      have hRtI : 0 ≤ 335*pₙ^7-705*pₙ^6+801*pₙ^5-497*pₙ^4+195*pₙ^3-183*pₙ^2+134*pₙ-30 := by
        set v := 3*(pₙ-1/2) with hv_def
        have hv0 : 0 ≤ v := by linarith
        have h1mv : 0 ≤ 1-v := by linarith
        have hbern : 335*pₙ^7-705*pₙ^6+801*pₙ^5-497*pₙ^4+195*pₙ^3-183*pₙ^2+134*pₙ-30 =
            (153/128)*(1-v)^7+(1221/128)*v*(1-v)^6+(9103/384)*v^2*(1-v)^5+
            (9107/384)*v^3*(1-v)^4+(4145/384)*v^4*(1-v)^3+(113935/10368)*v^5*(1-v)^2+
            (1440719/93312)*v^6*(1-v)+(1971865/279936)*v^7 := by
          rw [show pₙ = 1/2+v/3 from by linarith]; ring
        have t0 := mul_nonneg (show (0:ℝ) ≤ 153/128 by norm_num) (pow_nonneg h1mv 7)
        have t1 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1221/128 by norm_num) hv0) (pow_nonneg h1mv 6)
        have t2 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 9103/384 by norm_num) (pow_nonneg hv0 2)) (pow_nonneg h1mv 5)
        have t3 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 9107/384 by norm_num) (pow_nonneg hv0 3)) (pow_nonneg h1mv 4)
        have t4 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 4145/384 by norm_num) (pow_nonneg hv0 4)) (pow_nonneg h1mv 3)
        have t5 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 113935/10368 by norm_num) (pow_nonneg hv0 5)) (pow_nonneg h1mv 2)
        have t6 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1440719/93312 by norm_num) (pow_nonneg hv0 6)) h1mv
        have t7 := mul_nonneg (show (0:ℝ) ≤ 1971865/279936 by norm_num) (pow_nonneg hv0 7)
        linarith
      nlinarith
    · -- Case ρ₁ < 0
      push Not at hρ
      by_cases h54 : 5*pₙ^2+4*pₙ-4 ≤ 0
      · -- Sub-case 5pₙ²+4pₙ-4 ≤ 0: together with ρ₁ < 0 and N₃(a₁) = 0 this
        -- pins down a₁ = 0 (each term of N₃(a₁) at 0 is nonpositive, forcing
        -- their sum — which is 0 — to be degenerate). Then N₃(0, pₙ) < 0
        -- contradicts N₃(a₁) = 0.
        exfalso
        have hγ : 6*pₙ^3-11*pₙ^2+6*pₙ-1 ≤ 0 := by
          have : N₃ 0 pₙ = 6*pₙ^3-11*pₙ^2+6*pₙ-1 := by unfold N₃; ring
          linarith [hN₃_0]
        have hsq_nonpos : 5*(2*pₙ-1)*a₁^2 ≤ 0 := by
          have := mul_nonpos_of_nonpos_of_nonneg h54 ha₁_ge
          nlinarith
        have ha₁_zero : a₁ = 0 := by
          by_contra hne
          have hpos : 0 < a₁ := lt_of_le_of_ne ha₁_ge (Ne.symm hne)
          have : 0 < 5*(2*pₙ-1)*a₁^2 := by positivity
          linarith
        rw [ha₁_zero] at ha₁_eq
        have hN₃_0_neg : N₃ 0 pₙ < 0 := by
          have : N₃ 0 pₙ = (pₙ-1)*(2*pₙ-1)*(3*pₙ-1) := by unfold N₃; ring
          rw [this]
          exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith)) (by linarith)
        linarith
      · -- Sub-case 5pₙ²+4pₙ-4 > 0: the harder branch. Use a polynomial
        -- identity that expresses `(5pₙ²+4pₙ-4)·Rt(a₁)` purely in terms of
        -- `ρ₁·(2pₙ−1)·a₁²` and `F(pₙ)` (both already shown nonpositive),
        -- then divide through by the positive factor `5pₙ²+4pₙ-4`.
        push Not at h54
        -- Identity: (5pₙ²+4pₙ-4)·Rt = 5·ρ₁·(2pₙ-1)·a₁² + F(pₙ), derived from N₃(a₁)=0
        have h_prod : (125*pₙ^7-105*pₙ^6+45*pₙ^5-29*pₙ^4+177*pₙ^3-297*pₙ^2+164*pₙ-30) *
            (5*(1-2*pₙ)*a₁^2+(5*pₙ^2+4*pₙ-4)*a₁+(6*pₙ^3-11*pₙ^2+6*pₙ-1)) = 0 := by
          rw [hN₃_zero]; ring
        have hid : (5*pₙ^2+4*pₙ-4)*(125*a₁*pₙ^7-105*a₁*pₙ^6+45*a₁*pₙ^5-29*a₁*pₙ^4+
            177*a₁*pₙ^3-297*a₁*pₙ^2+164*a₁*pₙ-30*a₁-210*pₙ^8+475*pₙ^7-651*pₙ^6+423*pₙ^5+
            11*pₙ^4-291*pₙ^3+327*pₙ^2-164*pₙ+30) =
            5*(125*pₙ^7-105*pₙ^6+45*pₙ^5-29*pₙ^4+177*pₙ^3-297*pₙ^2+164*pₙ-30)*(2*pₙ-1)*a₁^2+
            (-1800*pₙ^10+3540*pₙ^9-2690*pₙ^8-965*pₙ^7+2595*pₙ^6+845*pₙ^5-4915*pₙ^4+5595*pₙ^3-
            3425*pₙ^2+1120*pₙ-150) := by
          have hring : (5*pₙ^2+4*pₙ-4)*(125*a₁*pₙ^7-105*a₁*pₙ^6+45*a₁*pₙ^5-29*a₁*pₙ^4+
              177*a₁*pₙ^3-297*a₁*pₙ^2+164*a₁*pₙ-30*a₁-210*pₙ^8+475*pₙ^7-651*pₙ^6+423*pₙ^5+
              11*pₙ^4-291*pₙ^3+327*pₙ^2-164*pₙ+30)-
              5*(125*pₙ^7-105*pₙ^6+45*pₙ^5-29*pₙ^4+177*pₙ^3-297*pₙ^2+164*pₙ-30)*(2*pₙ-1)*a₁^2-
              (-1800*pₙ^10+3540*pₙ^9-2690*pₙ^8-965*pₙ^7+2595*pₙ^6+845*pₙ^5-4915*pₙ^4+5595*pₙ^3-
              3425*pₙ^2+1120*pₙ-150) =
              (125*pₙ^7-105*pₙ^6+45*pₙ^5-29*pₙ^4+177*pₙ^3-297*pₙ^2+164*pₙ-30)*
              (5*(1-2*pₙ)*a₁^2+(5*pₙ^2+4*pₙ-4)*a₁+(6*pₙ^3-11*pₙ^2+6*pₙ-1)) := by ring
          linarith
        -- First term ≤ 0: ρ₁ < 0, (2pₙ-1) > 0, a₁² ≥ 0
        have hterm1 : 5*(125*pₙ^7-105*pₙ^6+45*pₙ^5-29*pₙ^4+177*pₙ^3-297*pₙ^2+164*pₙ-30)*
            (2*pₙ-1)*a₁^2 ≤ 0 := by
          have h1 : 0 ≤ -(125*pₙ^7-105*pₙ^6+45*pₙ^5-29*pₙ^4+177*pₙ^3-297*pₙ^2+164*pₙ-30) := by
            linarith
          have h2 : (0:ℝ) ≤ 2*pₙ-1 := by linarith
          nlinarith [mul_nonneg (mul_nonneg h1 h2) (sq_nonneg a₁)]
        -- F(pₙ) = -5·(2pₙ-1)²·G(pₙ) ≤ 0 where G ≥ 0. G is a degree-8 polynomial
        -- in pₙ; its nonnegativity on [1/2, 5/6] is proved by *two* separate
        -- Bernstein certificates, one on each half of the interval, because
        -- a single certificate on the full range wasn't tight enough.
        have hG : 0 ≤ 90*pₙ^8-87*pₙ^7+25*pₙ^6+95*pₙ^5-41*pₙ^4-107*pₙ^3+149*pₙ^2-104*pₙ+30 := by
          by_cases h23 : pₙ ≤ 2/3
          · -- G ≥ 0 on [1/2, 2/3] via Bernstein degree 8, w = 6·(pₙ-1/2) ∈ [0,1]
            set w := 6*(pₙ-1/2) with hw_def
            have hw0 : 0 ≤ w := by linarith
            have h1mw : 0 ≤ 1-w := by linarith
            have hbern : 90*pₙ^8-87*pₙ^7+25*pₙ^6+95*pₙ^5-41*pₙ^4-107*pₙ^3+149*pₙ^2-104*pₙ+30 =
                (75/32)*(1-w)^8+(1861/128)*w*(1-w)^7+(2405/64)*w^2*(1-w)^6+
                (4969/96)*w^3*(1-w)^5+(17353/432)*w^4*(1-w)^4+(33167/1944)*w^5*(1-w)^3+
                (11095/2916)*w^6*(1-w)^2+(544/729)*w^7*(1-w)+(154/729)*w^8 := by
              rw [show pₙ = 1/2+w/6 from by linarith]; ring
            have s0 := mul_nonneg (show (0:ℝ) ≤ 75/32 by norm_num) (pow_nonneg h1mw 8)
            have s1 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1861/128 by norm_num) hw0) (pow_nonneg h1mw 7)
            have s2 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 2405/64 by norm_num) (pow_nonneg hw0 2)) (pow_nonneg h1mw 6)
            have s3 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 4969/96 by norm_num) (pow_nonneg hw0 3)) (pow_nonneg h1mw 5)
            have s4 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 17353/432 by norm_num) (pow_nonneg hw0 4)) (pow_nonneg h1mw 4)
            have s5 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 33167/1944 by norm_num) (pow_nonneg hw0 5)) (pow_nonneg h1mw 3)
            have s6 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 11095/2916 by norm_num) (pow_nonneg hw0 6)) (pow_nonneg h1mw 2)
            have s7 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 544/729 by norm_num) (pow_nonneg hw0 7)) h1mw
            have s8 := mul_nonneg (show (0:ℝ) ≤ 154/729 by norm_num) (pow_nonneg hw0 8)
            linarith
          · -- G ≥ 0 on [2/3, 5/6] via Bernstein degree 8, w = 6·(pₙ-2/3) ∈ [0,1]
            push Not at h23
            set w := 6*(pₙ-2/3) with hw_def
            have hw0 : 0 ≤ w := by linarith
            have h1mw : 0 ≤ 1-w := by linarith
            have hbern : 90*pₙ^8-87*pₙ^7+25*pₙ^6+95*pₙ^5-41*pₙ^4-107*pₙ^3+149*pₙ^2-104*pₙ+30 =
                (154/729)*(1-w)^8+(640/243)*w*(1-w)^7+(16541/972)*w^2*(1-w)^6+
                (353147/5832)*w^3*(1-w)^5+(487957/3888)*w^4*(1-w)^4+(135295/864)*w^5*(1-w)^3+
                (5432377/46656)*w^6*(1-w)^2+(1483721/31104)*w^7*(1-w)+(129295/15552)*w^8 := by
              rw [show pₙ = 2/3+w/6 from by linarith]; ring
            have s0 := mul_nonneg (show (0:ℝ) ≤ 154/729 by norm_num) (pow_nonneg h1mw 8)
            have s1 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 640/243 by norm_num) hw0) (pow_nonneg h1mw 7)
            have s2 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 16541/972 by norm_num) (pow_nonneg hw0 2)) (pow_nonneg h1mw 6)
            have s3 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 353147/5832 by norm_num) (pow_nonneg hw0 3)) (pow_nonneg h1mw 5)
            have s4 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 487957/3888 by norm_num) (pow_nonneg hw0 4)) (pow_nonneg h1mw 4)
            have s5 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 135295/864 by norm_num) (pow_nonneg hw0 5)) (pow_nonneg h1mw 3)
            have s6 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 5432377/46656 by norm_num) (pow_nonneg hw0 6)) (pow_nonneg h1mw 2)
            have s7 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1483721/31104 by norm_num) (pow_nonneg hw0 7)) h1mw
            have s8 := mul_nonneg (show (0:ℝ) ≤ 129295/15552 by norm_num) (pow_nonneg hw0 8)
            linarith
        have hF : -1800*pₙ^10+3540*pₙ^9-2690*pₙ^8-965*pₙ^7+2595*pₙ^6+845*pₙ^5-4915*pₙ^4+
            5595*pₙ^3-3425*pₙ^2+1120*pₙ-150 ≤ 0 := by
          have hF_eq : -1800*pₙ^10+3540*pₙ^9-2690*pₙ^8-965*pₙ^7+2595*pₙ^6+845*pₙ^5-4915*pₙ^4+
              5595*pₙ^3-3425*pₙ^2+1120*pₙ-150 = -5*(2*pₙ-1)^2*
              (90*pₙ^8-87*pₙ^7+25*pₙ^6+95*pₙ^5-41*pₙ^4-107*pₙ^3+149*pₙ^2-104*pₙ+30) := by
            ring
          nlinarith [sq_nonneg (2*pₙ-1)]
        -- Combine: (5pₙ²+4pₙ-4)·Rt ≤ 0, and 5pₙ²+4pₙ-4 > 0, so Rt ≤ 0
        have h_prod_nonpos : (5*pₙ^2+4*pₙ-4)*(125*a₁*pₙ^7-105*a₁*pₙ^6+45*a₁*pₙ^5-29*a₁*pₙ^4+
            177*a₁*pₙ^3-297*a₁*pₙ^2+164*a₁*pₙ-30*a₁-210*pₙ^8+475*pₙ^7-651*pₙ^6+423*pₙ^5+
            11*pₙ^4-291*pₙ^3+327*pₙ^2-164*pₙ+30) ≤ 0 := by linarith
        by_contra habs; push Not at habs
        linarith [mul_pos h54 habs]
  -- Step 5: N₆(a₁) ≤ 0
  have hN₆_a₁ : N₆ a₁ pₙ ≤ 0 := by
    by_contra h_pos; simp only [not_le] at h_pos
    linarith [mul_pos h25sq h_pos]
  -- Step 6: IVT for two roots of N₆
  have hN₆_cont : Continuous (fun x => N₆ x pₙ) := by unfold N₆; fun_prop
  -- Root r₁ in [a₁, p₁]: N₆(a₁) ≤ 0 < N₆(p₁)
  obtain ⟨r₁, hr₁_mem, hr₁_eq⟩ := IsPreconnected.intermediate_value₂
    isPreconnected_Icc (Set.left_mem_Icc.mpr ha₁_le) (Set.right_mem_Icc.mpr ha₁_le)
    hN₆_cont.continuousOn continuousOn_const hN₆_a₁ (le_of_lt hN₆)
  -- Root r₂ in [p₁, 1-pₙ]: swap f and g since N₆(p₁) > 0 > N₆(1-pₙ)
  have hp₁_1mpₙ : p₁ ≤ 1 - pₙ := by linarith
  have hN₆_end := N₆_1mpₙ_neg (by linarith) hpₙ1
  obtain ⟨r₂, hr₂_mem, hr₂_eq⟩ := IsPreconnected.intermediate_value₂
    isPreconnected_Icc (Set.left_mem_Icc.mpr hp₁_1mpₙ) (Set.right_mem_Icc.mpr hp₁_1mpₙ)
    continuousOn_const hN₆_cont.continuousOn (le_of_lt hN₆) (le_of_lt hN₆_end)
  -- hr₂_eq : 0 = N₆ r₂ pₙ
  -- Step 7: r₁ ≠ r₂
  have hr₁_le : r₁ ≤ p₁ := hr₁_mem.2
  have hr₂_ge : p₁ ≤ r₂ := hr₂_mem.1
  have hr_ne : r₁ ≠ r₂ := by
    intro heq; subst heq; have : r₁ = p₁ := le_antisymm hr₁_le hr₂_ge
    subst this; linarith
  -- Step 8: two_roots_discrim_nonneg
  have hr₁_root : evalCubic (5*pₙ^3+pₙ^2-6*pₙ) (-6*pₙ^4-4*pₙ^3-2*pₙ^2+6)
      (6*pₙ^4+6*pₙ^3+2*pₙ-6) (-pₙ^3-5*pₙ^2+4*pₙ) r₁ = 0 := by
    rw [← N₆_eq_evalCubic]; exact hr₁_eq
  have hr₂_root : evalCubic (5*pₙ^3+pₙ^2-6*pₙ) (-6*pₙ^4-4*pₙ^3-2*pₙ^2+6)
      (6*pₙ^4+6*pₙ^3+2*pₙ-6) (-pₙ^3-5*pₙ^2+4*pₙ) r₂ = 0 := by
    rw [← N₆_eq_evalCubic]; exact hr₂_eq.symm
  have hdisc_nn := two_roots_discrim_nonneg _ _ _ _ r₁ r₂
    (N₆_leading_ne_zero (by linarith) hpₙ1) hr_ne hr₁_root hr₂_root
  -- Step 9: Contradiction with disc < 0
  linarith [N₆_disc_neg (le_of_lt hpₙ_lo) hpₙ_hi]

-- ═══════════════════ Case 3: 5/6 < pₙ < 1 ═══════════════════
--
-- Strategy here is much simpler than case 2: show `N₆(·, pₙ)` is monotone
-- on `[0, 1-pₙ]` with `N₆(1-pₙ, pₙ) < 0` as the right endpoint, so `N₆(p₁, pₙ)
-- ≤ N₆(1-pₙ, pₙ) < 0` for any `p₁ ≤ 1 - pₙ`. Monotonicity follows from
-- factoring `N₆(1-pₙ, pₙ) − N₆(p₁, pₙ) = (1 − pₙ − p₁) · Q_div(p₁, pₙ)` and
-- showing `Q_div ≥ 0` on the relevant rectangle.

/-- `Q_div` is the "divided difference" factor: `N₆(1−pₙ, pₙ) − N₆(p₁, pₙ) =
(1 − pₙ − p₁) · Q_div p₁ pₙ`. As a polynomial in `p₁`, it is a quadratic with
leading coefficient `5pₙ³ + pₙ² − 6pₙ` (nonpositive on `(0, 1)`, i.e. concave
down), so endpoint nonnegativity at `p₁ = 0` and `p₁ = 1 − pₙ` extends to
the whole interval via `concave_ge`. -/
def Q_div (p₁ pₙ : ℝ) : ℝ :=
  (5*pₙ^3+pₙ^2-6*pₙ)*p₁^2 + (-11*pₙ^4+5*pₙ^2-6*pₙ+6)*p₁ + (11*pₙ^5-5*pₙ^4+pₙ^3+11*pₙ^2-10*pₙ)

/-- The identity that makes `Q_div` useful: `N₆(1−pₙ, pₙ) − N₆(p₁, pₙ)` factors
as `(1 − pₙ − p₁) · Q_div(p₁, pₙ)`. -/
lemma N₆_diff_factor (p₁ pₙ : ℝ) :
    N₆ (1-pₙ) pₙ - N₆ p₁ pₙ = (1 - pₙ - p₁) * Q_div p₁ pₙ := by unfold N₆ Q_div; ring

/-- Leading coefficient of `Q_div(·, pₙ)` (as a quadratic in `p₁`) is `≤ 0`
on `(0, 1)`: factors as `pₙ · (5pₙ+6) · (pₙ−1)` with the last factor negative. -/
lemma Q_leading_nonpos {pₙ : ℝ} (hpₙ0 : 0 < pₙ) (hpₙ1 : pₙ < 1) : 5*pₙ^3+pₙ^2-6*pₙ ≤ 0 := by
  have : 5*pₙ^3+pₙ^2-6*pₙ = pₙ*(5*pₙ+6)*(pₙ-1) := by ring
  nlinarith [mul_pos hpₙ0 (show (0:ℝ) < 5*pₙ+6 by linarith)]

/-- `Q_div(0, pₙ) ≥ 0` on `pₙ ≥ 5/6`. Proved by a Taylor-like expansion around
`pₙ = 5/6`: the constant `2945/1296 > 0` plus `(pₙ − 5/6) · (positive)`. -/
lemma Q_at_zero_nonneg {pₙ : ℝ} (hpₙ : 5/6 ≤ pₙ) : 0 ≤ Q_div 0 pₙ := by
  have heq : Q_div 0 pₙ = pₙ * (11*pₙ^4-5*pₙ^3+pₙ^2+11*pₙ-10) := by unfold Q_div; ring
  rw [heq]; apply mul_nonneg (by linarith)
  have : 11*pₙ^4-5*pₙ^3+pₙ^2+11*pₙ-10 =
    2945/1296 + (pₙ-5/6)*(11*pₙ^3+25*pₙ^2/6+161*pₙ/36+3181/216) := by ring
  rw [this]
  have hd : (0:ℝ) ≤ pₙ-5/6 := by linarith
  have hpₙ0 : (0:ℝ) ≤ pₙ := by linarith
  have hpₙ2 : (0:ℝ) ≤ pₙ^2 := sq_nonneg pₙ
  have hpₙ3 : (0:ℝ) ≤ pₙ^3 := by nlinarith
  have hbr : (0:ℝ) ≤ 11*pₙ^3+25*pₙ^2/6+161*pₙ/36+3181/216 := by nlinarith
  linarith [mul_nonneg hd hbr]

/-- `Q_div(1−pₙ, pₙ) ≥ 0` on `pₙ ≥ 5/6`. Same idea — a double Taylor-like
expansion around `pₙ = 5/6` yields a positive constant plus `(pₙ − 5/6) · (nonneg)`. -/
lemma Q_at_1mpₙ_nonneg {pₙ : ℝ} (hpₙ : 5/6 ≤ pₙ) : 0 ≤ Q_div (1-pₙ) pₙ := by
  have heq : Q_div (1-pₙ) pₙ = 27*pₙ^5-25*pₙ^4-7*pₙ^3+35*pₙ^2-28*pₙ+6 := by
    unfold Q_div; ring
  rw [heq]
  have : 27*pₙ^5-25*pₙ^4-7*pₙ^3+35*pₙ^2-28*pₙ+6 =
    4447/2592 + (pₙ-5/6)*(9929/432 + (pₙ-5/6)*(27*pₙ^3+20*pₙ^2+91*pₙ/12+135/4)) := by ring
  rw [this]
  have hd : (0:ℝ) ≤ pₙ-5/6 := by linarith
  have hpₙ2 : (0:ℝ) ≤ pₙ^2 := sq_nonneg pₙ
  have hpₙ3 : (0:ℝ) ≤ pₙ^3 := by nlinarith [show (0:ℝ) ≤ pₙ by linarith]
  have hbr : (0:ℝ) ≤ 27*pₙ^3+20*pₙ^2+91*pₙ/12+135/4 := by nlinarith [show (0:ℝ) ≤ pₙ by linarith]
  have hm : (0:ℝ) ≤ 9929/432 + (pₙ-5/6)*(27*pₙ^3+20*pₙ^2+91*pₙ/12+135/4) := by
    linarith [mul_nonneg hd hbr]
  linarith [mul_nonneg hd hm]

/-- `Q_div(p₁, pₙ) ≥ 0` on the rectangle `0 ≤ p₁ ≤ 1-pₙ`, `5/6 ≤ pₙ < 1`.
Combines the two endpoint lemmas with `concave_ge` (using `Q_leading_nonpos`
to get the concave-down hypothesis). -/
lemma Q_nonneg {p₁ pₙ : ℝ} (hp₁0 : 0 ≤ p₁) (hp₁pₙ : p₁ ≤ 1-pₙ) (hpₙ : 5/6 ≤ pₙ)
    (hpₙ1 : pₙ < 1) : 0 ≤ Q_div p₁ pₙ := by
  have hidA : Q_div p₁ pₙ = (5*pₙ^3+pₙ^2-6*pₙ)*p₁^2 + (-11*pₙ^4+5*pₙ^2-6*pₙ+6)*p₁ +
      (11*pₙ^5-5*pₙ^4+pₙ^3+11*pₙ^2-10*pₙ) := by unfold Q_div; ring
  have hid0 : Q_div 0 pₙ = (5*pₙ^3+pₙ^2-6*pₙ)*0^2 + (-11*pₙ^4+5*pₙ^2-6*pₙ+6)*0 +
      (11*pₙ^5-5*pₙ^4+pₙ^3+11*pₙ^2-10*pₙ) := by unfold Q_div; ring
  have hid1 : Q_div (1-pₙ) pₙ = (5*pₙ^3+pₙ^2-6*pₙ)*(1-pₙ)^2 + (-11*pₙ^4+5*pₙ^2-6*pₙ+6)*(1-pₙ) +
      (11*pₙ^5-5*pₙ^4+pₙ^3+11*pₙ^2-10*pₙ) := by unfold Q_div; ring
  rw [hidA]; exact concave_ge (Q_leading_nonpos (by linarith) hpₙ1) hp₁0 hp₁pₙ
    (by rw [← hid0]; exact Q_at_zero_nonneg hpₙ)
    (by rw [← hid1]; exact Q_at_1mpₙ_nonneg hpₙ)

/-- `N₆(p₁, pₙ) ≤ N₆(1-pₙ, pₙ)` on the case-3 rectangle. Directly from
`N₆_diff_factor` — the difference is `(1-pₙ-p₁) · Q_div` and both factors
are nonneg. -/
lemma N₆_mono {p₁ pₙ : ℝ} (hp₁0 : 0 ≤ p₁) (hp₁pₙ : p₁ ≤ 1-pₙ) (hpₙ : 5/6 ≤ pₙ)
    (hpₙ1 : pₙ < 1) : N₆ p₁ pₙ ≤ N₆ (1-pₙ) pₙ :=
  le_of_sub_nonneg (by linarith [N₆_diff_factor p₁ pₙ,
    (mul_nonneg (show (0:ℝ) ≤ 1-pₙ-p₁ by linarith) (Q_nonneg hp₁0 hp₁pₙ hpₙ hpₙ1))])

/-- Case 3 conclusion: `N₆(p₁, pₙ) ≤ 0` when `5/6 < pₙ < 1` and `p₁ ≤ 1-pₙ`.
Chain `N₆(p₁, pₙ) ≤ N₆(1-pₙ, pₙ) < 0`. -/
theorem case3 {p₁ pₙ : ℝ} (hp₁0 : 0 ≤ p₁) (hp₁pₙ : p₁ ≤ 1-pₙ) (hpₙ : 5/6 < pₙ)
    (hpₙ1 : pₙ < 1) : N₆ p₁ pₙ ≤ 0 :=
  le_trans (N₆_mono hp₁0 hp₁pₙ (le_of_lt hpₙ) hpₙ1) (le_of_lt (N₆_1mpₙ_neg (by linarith) hpₙ1))

-- ═══════════════════ Assembly ═══════════════════

/-- At least one of the three candidates beats `(1.2)·Aₙ` on the interior
`0 < pₙ < 1`. Dispatches on `pₙ` into the three cases and uses the
denominator-clearing equivalences to convert case 2/3's polynomial
conclusions back to the rational form. -/
theorem bound_lower_half {p₁ pₙ : ℝ} (hp₁0 : 0 ≤ p₁) (hp₁pₙ : p₁ ≤ pₙ) (hpₙ0 : 0 < pₙ)
    (hpₙ1 : pₙ < 1) (hp₁1 : p₁ < 1) (hs : p₁ + pₙ ≤ 1) :
    C₁ pₙ ≤ (1.2) * Aₙ p₁ pₙ ∨ C₂ p₁ pₙ ≤ (1.2) * Aₙ p₁ pₙ ∨
    C₃ p₁ pₙ ≤ (1.2) * Aₙ p₁ pₙ := by
  by_cases hpₙ2 : pₙ ≤ 1/2
  · exact Or.inl (case1 hp₁0 hp₁1 hpₙ0 hpₙ2)
  · simp only [not_le] at hpₙ2
    by_cases hpₙ4 : pₙ ≤ 5/6
    · rcases case2 hp₁0 hp₁pₙ hpₙ1 hpₙ2 hpₙ4 hs with h | h
      · exact Or.inr (Or.inl ((C₂_le_iff_N₃ hpₙ0 hpₙ1 hp₁1).mpr h))
      · exact Or.inr (Or.inr ((C₃_le_iff_N₆ hp₁0 hpₙ0 hpₙ1 hp₁1).mpr h))
    · simp only [not_le] at hpₙ4
      exact Or.inr (Or.inr ((C₃_le_iff_N₆ hp₁0 hpₙ0 hpₙ1 hp₁1).mpr
        (case3 hp₁0 (by linarith) hpₙ4 hpₙ1)))

/-- **Main result.** For `0 ≤ p₁ ≤ pₙ`, `p₁ + pₙ ≤ 1`, `pₙ ≤ 1`,
`min (C₁ pₙ, C₂ p₁ pₙ, C₃ p₁ pₙ) ≤ (1.2) · Aₙ p₁ pₙ` — i.e. at least
one of the three nonadaptive candidates is within a factor `1.2` of the
adaptive cost.

Handles the boundary cases `pₙ = 0` and `pₙ = 1` (which force `p₁ = 0` and
make all the `C_i` division-by-zero junk that happens to evaluate in a
way `norm_num` can dispose of), then delegates to `bound_lower_half`. -/
theorem adaptivity_gap {p₁ pₙ : ℝ} (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1) (hpₙ0 : 0 ≤ pₙ)
    (hpₙ1 : pₙ ≤ 1) (hp₁pₙ : p₁ ≤ pₙ) (hs : p₁ + pₙ ≤ 1) :
    min (min (C₁ pₙ) (C₂ p₁ pₙ)) (C₃ p₁ pₙ)
      ≤ (1.2) * Aₙ p₁ pₙ := by
  -- Boundary case pₙ = 0 (forces p₁ = 0; all costs are junk values via div-by-zero)
  rcases eq_or_lt_of_le hpₙ0 with rfl | hpₙ0'
  · have : p₁ = 0 := le_antisymm (by linarith) hp₁0; subst this
    have hC : C₁ 0 ≤ (1.2) * Aₙ 0 0 := by
      unfold C₁ Aₙ; norm_num
    calc min (min (C₁ 0) (C₂ 0 0)) (C₃ 0 0)
        ≤ min (C₁ 0) (C₂ 0 0) := min_le_left _ _
      _ ≤ C₁ 0 := min_le_left _ _
      _ ≤ (1.2) * Aₙ 0 0 := hC
  -- Boundary case pₙ = 1 (forces p₁ = 0 from p₁ + pₙ ≤ 1)
  rcases eq_or_lt_of_le hpₙ1 with rfl | hpₙ1'
  · have : p₁ = 0 := le_antisymm (by linarith) hp₁0; subst this
    have hC : C₁ 1 ≤ (1.2) * Aₙ 0 1 := by
      unfold C₁ Aₙ; norm_num
    calc min (min (C₁ 1) (C₂ 0 1)) (C₃ 0 1)
        ≤ min (C₁ 1) (C₂ 0 1) := min_le_left _ _
      _ ≤ C₁ 1 := min_le_left _ _
      _ ≤ (1.2) * Aₙ 0 1 := hC
  -- Interior: 0 < pₙ < 1. Dispatch on which candidate wins.
  have hp₁1' : p₁ < 1 := by linarith
  rcases bound_lower_half hp₁0 hp₁pₙ hpₙ0' hpₙ1' hp₁1' hs with h | h | h
  · calc min (min (C₁ pₙ) (C₂ p₁ pₙ)) (C₃ p₁ pₙ)
        ≤ min (C₁ pₙ) (C₂ p₁ pₙ) := min_le_left _ _
      _ ≤ C₁ pₙ := min_le_left _ _
      _ ≤ (1.2) * Aₙ p₁ pₙ := h
  · calc min (min (C₁ pₙ) (C₂ p₁ pₙ)) (C₃ p₁ pₙ)
        ≤ min (C₁ pₙ) (C₂ p₁ pₙ) := min_le_left _ _
      _ ≤ C₂ p₁ pₙ := min_le_right _ _
      _ ≤ (1.2) * Aₙ p₁ pₙ := h
  · calc min (min (C₁ pₙ) (C₂ p₁ pₙ)) (C₃ p₁ pₙ)
        ≤ C₃ p₁ pₙ := min_le_right _ _
      _ ≤ (1.2) * Aₙ p₁ pₙ := h

end
