/-
  The Additive Adaptivity Gap for Two-Coin Sequential Stopping is 1/2

  We prove: for 0 ≤ p ≤ q ≤ 1 with p+q ≤ 1, at least one of the slack
  functions L₂, L₃, L₅ is nonneg, meaning at least one nonadaptive strategy
  achieves gap ≤ 1/2. All identities verified by `ring`, all inequalities
  by `nlinarith` with explicit SOS witnesses. No division anywhere.
-/

import Mathlib.Tactic

noncomputable section

/-! ## Polynomial Definitions -/

def M (q : ℝ) : ℝ := 2*q^2 - 2*q + 1
def L₂ (p q : ℝ) : ℝ := 1 - p - q + 3*p*q - 2*q^2
def R₃ (p q : ℝ) : ℝ := p*(2*q - 1) + (1 - q)^2
def L₃ (p q : ℝ) : ℝ := q*(1 - p)*(1 - q) - 2*(q - p)*R₃ p q
def N₅ (p q : ℝ) : ℝ :=
  2*p^2*q^2 - 2*p^2*q + p^2 - 3*p*q^2 + 6*p*q - 3*p + 2*q^2 - 4*q + 2
def L₅ (p q : ℝ) : ℝ := q*(1 - p)*(1 - q) - 2*(q - p)*N₅ p q
def P (q : ℝ) : ℝ := 8*q^4 - 18*q^3 + 22*q^2 - 15*q + 4
def g (q : ℝ) : ℝ := 8*q^3 - 8*q^2 - q + 2
def E (p q : ℝ) : ℝ := 2*(1 - q)^2 + 2*M q*(1 - q + p) + (-4*q^3 - 2*q^2 + 10*q - 6)

/-! ## SOS Certificates -/

theorem M_pos (q : ℝ) : 0 < M q := by
  unfold M; nlinarith [sq_nonneg (2*q - 1)]

theorem quad_6_8_3_pos (q : ℝ) : 0 < 6*q^2 - 8*q + 3 := by
  nlinarith [sq_nonneg (3*q - 2)]

theorem quad_6_4_25_pos (q : ℝ) : 0 < 6*q^2 - 4*q + 25 := by
  nlinarith [sq_nonneg (6*q - 2)]

theorem P_pos (q : ℝ) : 0 < P q := by
  unfold P; nlinarith [sq_nonneg ((2*q - 1)*(8*q - 5)), sq_nonneg (22*q - 15)]

theorem g_nonneg {q : ℝ} (hq1 : 1/2 ≤ q) : 0 ≤ g q := by
  unfold g
  by_cases hq23 : q ≤ 2/3
  · -- g = 2q(2q-1)² + (2-3q), both nonneg
    nlinarith [sq_nonneg (2*q - 1)]
  · push Not at hq23
    nlinarith [sq_nonneg (2*q - 1), sq_nonneg (32*q - 25)]

theorem quartic_nonneg {q : ℝ} (hq : 2/3 ≤ q) :
    0 ≤ 2*q^4 - 4*q^3 + 11*q^2 - 9*q + 2 := by
  nlinarith [sq_nonneg (3*q - 2), quad_6_4_25_pos q]

/-! ## Polynomial Identities (verified by `ring`) -/

theorem L₃_factorization (p q : ℝ) :
    (M q)^2 * L₃ p q = q^2*(1 - q)*P q +
      (p * M q - (1 - q)^2) *
      (2 * M q * (2*q - 1) * p - q*(2*q^3 + q - 1)) := by
  unfold L₃ R₃ M P; ring

/- CRITICAL: `M` must be unfolded LAST because `E` references `M` in its body.
   If `M` is unfolded before `E`, the `M q` terms introduced by unfolding `E`
   remain unexpanded and `ring` cannot close the goal. -/
theorem concavity_master_identity (p q : ℝ) :
    (2*q - 1) * M q * L₅ p q =
      (1 - q - p) * q * P q +
      M q * (p * M q - (1 - q)^2) * g q -
      (p * M q - (1 - q)^2) * (1 - q - p) * (2*q - 1) * E p q := by
  unfold L₅ N₅ P g E M; ring

theorem neg_E_decomp (p q : ℝ) :
    -E p q = 2*q*(6*q^2 - 8*q + 3) + 2*M q*(1 - q - p) := by
  unfold E M; ring

theorem L₃_complete_square (p q : ℝ) :
    8*(2*q - 1) * L₃ p q =
      (4*(2*q - 1)*p - (q^2 + 3*q - 2))^2 -
      (3*q - 2)*(11*q^3 - 12*q^2 + 7*q - 2) := by
  unfold L₃ R₃; ring

/-! ## Case A: L₂ ≥ 0 for q ≤ 1/2 -/

theorem L₂_nonneg_of_q_le_half {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hpq1 : p + q ≤ 1) (hq : q ≤ 1/2) :
    0 ≤ L₂ p q := by
  unfold L₂
  by_cases hq3 : q ≤ 1/3
  · nlinarith [sq_nonneg (1 - q)]
  · push Not at hq3; nlinarith

/-! ## Case B: L₃ ≥ 0 for 1/2 < q ≤ 2/3 -/

theorem L₃_nonneg_case1 {p q : ℝ}
    (hp : 0 ≤ p) (hq12 : 1/2 ≤ q)
    (hcoeff : q^2 + 3*q ≤ 2) :
    0 ≤ L₃ p q := by
  -- L₃ = 2(2q-1)p² + (2-3q-q²)p + q(1-q)(2q-1): all terms nonneg
  unfold L₃ R₃; nlinarith [sq_nonneg p, sq_nonneg (1 - q)]

theorem L₃_nonneg_case2 {p q : ℝ}
    (hp : 0 ≤ p) (hpq1 : p + q ≤ 1) (hq12 : 1/2 ≤ q)
    (hq23 : q ≤ 2/3) (hcoeff : 2 < q^2 + 3*q) :
    0 ≤ L₃ p q := by
  -- q²+3q > 2 forces q > 27/50
  have hq27 : 27/50 ≤ q := by
    by_contra h; push Not at h
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 27/50 - q by linarith)
                          (show (0:ℝ) ≤ 27/50 + q + 3 by linarith)]
  -- 11q³-12q²+7q-2 ≥ 0 via Taylor at 27/50
  have hid : 11*q^3 - 12*q^2 + 7*q - 2 =
      (q - 27/50) * (11*q^2 - 303*q/50 + 9319/2500) + 1613/125000 := by ring
  have hg_pos : 0 < 11*q^2 - 303*q/50 + 9319/2500 := by
    nlinarith [sq_nonneg (11*q - 3)]
  have hcubic : 0 ≤ 11*q^3 - 12*q^2 + 7*q - 2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ q - 27/50 by linarith) (le_of_lt hg_pos)]
  -- 8(2q-1)L₃ = square - (3q-2)(cubic): since 3q-2 ≤ 0 and cubic ≥ 0, product ≤ 0
  have hcsq := L₃_complete_square p q
  nlinarith [sq_nonneg (4*(2*q - 1)*p - (q^2 + 3*q - 2))]

theorem L₃_nonneg_of_q_le_two_thirds {p q : ℝ}
    (hp : 0 ≤ p) (hpq1 : p + q ≤ 1)
    (hq12 : 1/2 ≤ q) (hq23 : q ≤ 2/3) :
    0 ≤ L₃ p q := by
  by_cases hcoeff : q^2 + 3*q ≤ 2
  · exact L₃_nonneg_case1 hp hq12 hcoeff
  · push Not at hcoeff
    exact L₃_nonneg_case2 hp hpq1 hq12 hq23 hcoeff

/-! ## Step 3a: L₃ ≤ 0 ⟹ pM ≥ (1-q)²

  From M²L₃ = q²(1-q)P + Δ·Q: if Δ < 0 and q ≥ 2/3, then Q ≤ 0,
  so Δ·Q ≥ 0, giving M²L₃ > 0. This contradicts L₃ ≤ 0.
-/

theorem Delta_nonneg_of_L₃_nonpos {p q : ℝ}
    (hp : 0 ≤ p) (hpq1 : p + q ≤ 1)
    (hq23 : 2/3 ≤ q) (hL3 : L₃ p q ≤ 0) :
    (1 - q)^2 ≤ p * M q := by
  by_contra h_neg
  push Not at h_neg
  have hfact := L₃_factorization p q
  have hM := M_pos q
  have h_pm_nn : 0 ≤ p * M q := mul_nonneg hp (le_of_lt hM)
  have h_sq_pos : 0 < (1 - q) ^ 2 := by linarith
  have h1q_nn : 0 ≤ 1 - q := by linarith
  have h1q_pos : 0 < 1 - q := by
    by_contra h1q; push Not at h1q
    -- From h1q : 1-q ≤ 0 and h1q_nn : 0 ≤ 1-q: 1-q = 0, so (1-q)² = 0
    have := le_antisymm h1q h1q_nn
    nlinarith  -- contradicts h_sq_pos
  have hq_pos : 0 < q := by linarith
  have h2q1 : 0 ≤ 2*q - 1 := by linarith
  -- Q ≤ 0: Q is linear increasing in p; at max p it equals -(quartic) ≤ 0
  have hQ : 2 * M q * (2*q - 1) * p - q*(2*q^3 + q - 1) ≤ 0 := by
    have : 2 * M q * (2*q - 1) * p ≤ 2*(2*q - 1)*(1 - q)^2 := by
      nlinarith [mul_nonneg h2q1 (show 0 ≤ (1-q)^2 - p*M q by linarith)]
    nlinarith [quartic_nonneg hq23]
  -- Δ·Q ≥ 0: both factors ≤ 0, product ≥ 0
  have hprod : 0 ≤ (p * M q - (1 - q)^2) *
      (2 * M q * (2*q - 1) * p - q*(2*q^3 + q - 1)) := by
    nlinarith [mul_nonneg (show 0 ≤ (1-q)^2 - p*M q by linarith)
                          (show 0 ≤ q*(2*q^3+q-1) - 2*M q*(2*q-1)*p by linarith)]
  -- M²L₃ = q²(1-q)P + (≥0) > 0
  have hP_pos : 0 < q^2 * (1 - q) * P q :=
    mul_pos (mul_pos (pow_pos hq_pos 2) h1q_pos) (P_pos q)
  -- But M²L₃ ≤ 0 since M² ≥ 0 and L₃ ≤ 0
  nlinarith [sq_nonneg (M q), mul_nonneg (sq_nonneg (M q)) (show 0 ≤ -L₃ p q by linarith)]

/-! ## Step 3b: pM ≥ (1-q)² ⟹ L₅ ≥ 0

  (2q-1)ML₅ = (1-q-p)qP + MΔg - Δ(1-q-p)(2q-1)E
  All three RHS terms are nonneg when Δ ≥ 0, q > 1/2, (p,q) ∈ R₁.
  NOTE: requires strict q > 1/2 (not ≤) since we divide out (2q-1)M > 0.
-/

theorem L₅_nonneg_of_Delta_nonneg {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hpq1 : p + q ≤ 1)
    (hq12 : 1/2 < q) (hDelta : (1 - q)^2 ≤ p * M q) :
    0 ≤ L₅ p q := by
  have hmaster := concavity_master_identity p q
  have hM := M_pos q
  have h2q1 : 0 < 2*q - 1 := by linarith
  have h1qp : 0 ≤ 1 - q - p := by linarith
  have hDelta' : 0 ≤ p * M q - (1 - q)^2 := by linarith
  have hq_nn : 0 ≤ q := by linarith
  -- Term 1: (1-q-p)qP ≥ 0
  have hterm1 : 0 ≤ (1 - q - p) * q * P q :=
    mul_nonneg (mul_nonneg h1qp hq_nn) (le_of_lt (P_pos q))
  -- Term 2: MΔg ≥ 0
  have hterm2 : 0 ≤ M q * (p * M q - (1 - q)^2) * g q :=
    mul_nonneg (mul_nonneg (le_of_lt hM) hDelta') (g_nonneg (le_of_lt hq12))
  -- Term 3: -Δ(1-q-p)(2q-1)E ≥ 0 since -E ≥ 0
  have hnE : 0 ≤ -E p q := by
    rw [neg_E_decomp]; nlinarith [quad_6_8_3_pos q]
  have hterm3 : 0 ≤ -(p * M q - (1 - q)^2) * (1 - q - p) * (2*q - 1) * E p q := by
    have key : -(p * M q - (1 - q)^2) * (1 - q - p) * (2*q - 1) * E p q =
        (p * M q - (1 - q)^2) * (1 - q - p) * (2*q - 1) * (-E p q) := by ring
    rw [key]
    exact mul_nonneg (mul_nonneg (mul_nonneg hDelta' h1qp) (le_of_lt h2q1)) hnE
  -- (2q-1)ML₅ = sum of three nonneg terms ≥ 0
  have h_key : 0 ≤ (2*q - 1) * M q * L₅ p q := by linarith
  -- Since (2q-1)M > 0 and (2q-1)M·L₅ ≥ 0: L₅ ≥ 0
  -- Proof: if L₅ < 0, then (2q-1)M·L₅ < (2q-1)M·0 = 0, contradicting h_key
  by_contra h_neg
  push Not at h_neg
  have h_prod_pos : 0 < (2*q - 1) * M q := mul_pos h2q1 hM
  have := mul_lt_mul_of_pos_left h_neg h_prod_pos
  rw [mul_zero] at this
  linarith

/-! ## Main Theorem -/

theorem polynomial_core {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hpq1 : p + q ≤ 1) :
    0 ≤ L₂ p q ∨ 0 ≤ L₃ p q ∨ 0 ≤ L₅ p q := by
  by_cases hq12 : q ≤ 1/2
  · -- Case A: q ≤ 1/2 → L₂ ≥ 0
    exact Or.inl (L₂_nonneg_of_q_le_half hp hpq hpq1 hq12)
  · push Not at hq12
    -- hq12 : 1/2 < q (strict!)
    by_cases hq23 : q ≤ 2/3
    · -- Case B: 1/2 < q ≤ 2/3 → L₃ ≥ 0
      exact Or.inr (Or.inl
        (L₃_nonneg_of_q_le_two_thirds hp hpq1 (le_of_lt hq12) hq23))
    · push Not at hq23
      -- Case C: q > 2/3
      by_cases hL3 : 0 ≤ L₃ p q
      · exact Or.inr (Or.inl hL3)
      · push Not at hL3
        -- L₃ < 0, q > 2/3: Step 3a gives Δ ≥ 0, Step 3b gives L₅ ≥ 0
        have hDelta := Delta_nonneg_of_L₃_nonpos hp hpq1
          (le_of_lt hq23) (le_of_lt hL3)
        exact Or.inr (Or.inr
          (L₅_nonneg_of_Delta_nonneg hp hpq hpq1 hq12 hDelta))

end
