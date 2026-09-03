/-
  The Additive Adaptivity Gap for Two-Coin Sequential Stopping is 1/2

  We prove: for 0 ≤ p₁ ≤ pₙ ≤ 1 with p₁+pₙ ≤ 1, the minimum
  of three nonadaptive expected costs C₁, C₂, C₄ is at most
  `1/2 + Aₙ p₁ pₙ`, where Aₙ is the cheaper of the two adaptive costs on
  this domain — i.e., some nonadaptive strategy achieves additive
  gap ≤ 1/2.

  The polynomial core works without division via slack polynomials L₂, L₃, L₅
  (`polynomial_core`); the equivalence `0 ≤ L_i ↔ C_i - Aₙ ≤ 1/2` is proved
  by clearing denominators (`C_*_le_iff_L_*`). All polynomial identities
  verified by `ring`; inequalities by `nlinarith` with explicit SOS witnesses.
-/

import Mathlib

noncomputable section

/-! ## Polynomial Definitions -/

/-! ## Rational-form Costs and Equivalence

  C₁, C₂, C₄ are the three nonadaptive expected costs (originally derived as
  S_2, S_3, S_5 in the slack analysis); Aₙ is the adaptive cost. Each L_i
  equals -2·(denom)·(C_i - Aₙ - 1/2), so 0 ≤ L_i ↔ C_i - Aₙ ≤ 1/2. -/

def Aₙ (p₁ pₙ : ℝ) : ℝ :=
  pₙ / (1 - p₁) + 1 / pₙ

def C₁ (_p₁ pₙ : ℝ) : ℝ :=
  1 / pₙ + pₙ / (1 - pₙ)

def C₂ (p₁ pₙ : ℝ) : ℝ :=
  1 + p₁ / (1 - pₙ) + (1 - p₁) / pₙ

def C₄ (p₁ pₙ : ℝ) : ℝ :=
  1 + p₁ * (1 + pₙ + p₁ * pₙ / (1 - pₙ))
    + (1 - p₁) * (2 - pₙ + (1 - pₙ) * (1 - p₁) / pₙ)

def M (pₙ : ℝ) : ℝ := 2*pₙ^2 - 2*pₙ + 1
def L₂ (p₁ pₙ : ℝ) : ℝ := 1 - p₁ - pₙ + 3*p₁*pₙ - 2*pₙ^2
def R₃ (p₁ pₙ : ℝ) : ℝ := p₁*(2*pₙ - 1) + (1 - pₙ)^2
def L₃ (p₁ pₙ : ℝ) : ℝ := pₙ*(1 - p₁)*(1 - pₙ) - 2*(pₙ - p₁)*R₃ p₁ pₙ
def N₅ (p₁ pₙ : ℝ) : ℝ :=
  2*p₁^2*pₙ^2 - 2*p₁^2*pₙ + p₁^2 - 3*p₁*pₙ^2 + 6*p₁*pₙ - 3*p₁ + 2*pₙ^2 - 4*pₙ + 2
def L₅ (p₁ pₙ : ℝ) : ℝ := pₙ*(1 - p₁)*(1 - pₙ) - 2*(pₙ - p₁)*N₅ p₁ pₙ
def P (pₙ : ℝ) : ℝ := 8*pₙ^4 - 18*pₙ^3 + 22*pₙ^2 - 15*pₙ + 4
def g (pₙ : ℝ) : ℝ := 8*pₙ^3 - 8*pₙ^2 - pₙ + 2
def E (p₁ pₙ : ℝ) : ℝ := 2*(1 - pₙ)^2 + 2*M pₙ*(1 - pₙ + p₁) + (-4*pₙ^3 - 2*pₙ^2 + 10*pₙ - 6)

/-! ## SOS Certificates -/

theorem M_pos (pₙ : ℝ) : 0 < M pₙ := by
  unfold M; nlinarith [sq_nonneg (2*pₙ - 1)]

theorem quad_6_8_3_pos (pₙ : ℝ) : 0 < 6*pₙ^2 - 8*pₙ + 3 := by
  nlinarith [sq_nonneg (3*pₙ - 2)]

theorem quad_6_4_25_pos (pₙ : ℝ) : 0 < 6*pₙ^2 - 4*pₙ + 25 := by
  nlinarith [sq_nonneg (6*pₙ - 2)]

theorem P_pos (pₙ : ℝ) : 0 < P pₙ := by
  unfold P; nlinarith [sq_nonneg ((2*pₙ - 1)*(8*pₙ - 5)), sq_nonneg (22*pₙ - 15)]

theorem g_nonneg {pₙ : ℝ} (hpₙ1 : 1/2 ≤ pₙ) : 0 ≤ g pₙ := by
  unfold g
  by_cases hpₙ23 : pₙ ≤ 2/3
  · -- g = 2pₙ(2pₙ-1)² + (2-3pₙ), both nonneg
    nlinarith [sq_nonneg (2*pₙ - 1)]
  · push Not at hpₙ23
    nlinarith [sq_nonneg (2*pₙ - 1), sq_nonneg (32*pₙ - 25)]

theorem quartic_nonneg {pₙ : ℝ} (hpₙ : 2/3 ≤ pₙ) :
    0 ≤ 2*pₙ^4 - 4*pₙ^3 + 11*pₙ^2 - 9*pₙ + 2 := by
  nlinarith [sq_nonneg (3*pₙ - 2), quad_6_4_25_pos pₙ]

/-! ## Polynomial Identities (verified by `ring`) -/

theorem L₃_factorization (p₁ pₙ : ℝ) :
    (M pₙ)^2 * L₃ p₁ pₙ = pₙ^2*(1 - pₙ)*P pₙ +
      (p₁ * M pₙ - (1 - pₙ)^2) *
      (2 * M pₙ * (2*pₙ - 1) * p₁ - pₙ*(2*pₙ^3 + pₙ - 1)) := by
  unfold L₃ R₃ M P; ring

/- CRITICAL: `M` must be unfolded LAST because `E` references `M` in its body.
   If `M` is unfolded before `E`, the `M pₙ` terms introduced by unfolding `E`
   remain unexpanded and `ring` cannot close the goal. -/
theorem concavity_master_identity (p₁ pₙ : ℝ) :
    (2*pₙ - 1) * M pₙ * L₅ p₁ pₙ =
      (1 - pₙ - p₁) * pₙ * P pₙ +
      M pₙ * (p₁ * M pₙ - (1 - pₙ)^2) * g pₙ -
      (p₁ * M pₙ - (1 - pₙ)^2) * (1 - pₙ - p₁) * (2*pₙ - 1) * E p₁ pₙ := by
  unfold L₅ N₅ P g E M; ring

theorem neg_E_decomp (p₁ pₙ : ℝ) :
    -E p₁ pₙ = 2*pₙ*(6*pₙ^2 - 8*pₙ + 3) + 2*M pₙ*(1 - pₙ - p₁) := by
  unfold E M; ring

theorem L₃_complete_square (p₁ pₙ : ℝ) :
    8*(2*pₙ - 1) * L₃ p₁ pₙ =
      (4*(2*pₙ - 1)*p₁ - (pₙ^2 + 3*pₙ - 2))^2 -
      (3*pₙ - 2)*(11*pₙ^3 - 12*pₙ^2 + 7*pₙ - 2) := by
  unfold L₃ R₃; ring

/-! ## Case A: L₂ ≥ 0 for pₙ ≤ 1/2 -/

theorem L₂_nonneg_of_q_le_half {p₁ pₙ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₁pₙ : p₁ ≤ pₙ) (hp₁pₙ1 : p₁ + pₙ ≤ 1) (hpₙ : pₙ ≤ 1/2) :
    0 ≤ L₂ p₁ pₙ := by
  unfold L₂
  by_cases hpₙ3 : pₙ ≤ 1/3
  · nlinarith [sq_nonneg (1 - pₙ)]
  · push Not at hpₙ3; nlinarith

/-! ## Case B: L₃ ≥ 0 for 1/2 < pₙ ≤ 2/3 -/

theorem L₃_nonneg_case1 {p₁ pₙ : ℝ}
    (hp₁ : 0 ≤ p₁) (hpₙ12 : 1/2 ≤ pₙ)
    (hcoeff : pₙ^2 + 3*pₙ ≤ 2) :
    0 ≤ L₃ p₁ pₙ := by
  -- L₃ = 2(2pₙ-1)p₁² + (2-3pₙ-pₙ²)p₁ + pₙ(1-pₙ)(2pₙ-1): all terms nonneg
  unfold L₃ R₃; nlinarith [sq_nonneg p₁, sq_nonneg (1 - pₙ)]

theorem L₃_nonneg_case2 {p₁ pₙ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₁pₙ1 : p₁ + pₙ ≤ 1) (hpₙ12 : 1/2 ≤ pₙ)
    (hpₙ23 : pₙ ≤ 2/3) (hcoeff : 2 < pₙ^2 + 3*pₙ) :
    0 ≤ L₃ p₁ pₙ := by
  -- pₙ²+3pₙ > 2 forces pₙ > 27/50
  have hpₙ27 : 27/50 ≤ pₙ := by
    by_contra h; push Not at h
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 27/50 - pₙ by linarith)
                          (show (0:ℝ) ≤ 27/50 + pₙ + 3 by linarith)]
  -- 11pₙ³-12pₙ²+7pₙ-2 ≥ 0 via Taylor at 27/50
  have hid : 11*pₙ^3 - 12*pₙ^2 + 7*pₙ - 2 =
      (pₙ - 27/50) * (11*pₙ^2 - 303*pₙ/50 + 9319/2500) + 1613/125000 := by ring
  have hg_pos : 0 < 11*pₙ^2 - 303*pₙ/50 + 9319/2500 := by
    nlinarith [sq_nonneg (11*pₙ - 3)]
  have hcubic : 0 ≤ 11*pₙ^3 - 12*pₙ^2 + 7*pₙ - 2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ pₙ - 27/50 by linarith) (le_of_lt hg_pos)]
  -- 8(2pₙ-1)L₃ = square - (3pₙ-2)(cubic): since 3pₙ-2 ≤ 0 and cubic ≥ 0, product ≤ 0
  have hcsq := L₃_complete_square p₁ pₙ
  nlinarith [sq_nonneg (4*(2*pₙ - 1)*p₁ - (pₙ^2 + 3*pₙ - 2))]

theorem L₃_nonneg_of_q_le_two_thirds {p₁ pₙ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₁pₙ1 : p₁ + pₙ ≤ 1)
    (hpₙ12 : 1/2 ≤ pₙ) (hpₙ23 : pₙ ≤ 2/3) :
    0 ≤ L₃ p₁ pₙ := by
  by_cases hcoeff : pₙ^2 + 3*pₙ ≤ 2
  · exact L₃_nonneg_case1 hp₁ hpₙ12 hcoeff
  · push Not at hcoeff
    exact L₃_nonneg_case2 hp₁ hp₁pₙ1 hpₙ12 hpₙ23 hcoeff

/-! ## Step 3a: L₃ ≤ 0 ⟹ p₁M ≥ (1-pₙ)²

  From M²L₃ = pₙ²(1-pₙ)P + Δ·Q: if Δ < 0 and pₙ ≥ 2/3, then Q ≤ 0,
  so Δ·Q ≥ 0, giving M²L₃ > 0. This contradicts L₃ ≤ 0.
-/

theorem Delta_nonneg_of_L₃_nonpos {p₁ pₙ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₁pₙ1 : p₁ + pₙ ≤ 1)
    (hpₙ23 : 2/3 ≤ pₙ) (hL3 : L₃ p₁ pₙ ≤ 0) :
    (1 - pₙ)^2 ≤ p₁ * M pₙ := by
  by_contra h_neg
  push Not at h_neg
  have hfact := L₃_factorization p₁ pₙ
  have hM := M_pos pₙ
  have h_pm_nn : 0 ≤ p₁ * M pₙ := mul_nonneg hp₁ (le_of_lt hM)
  have h_sq_pos : 0 < (1 - pₙ) ^ 2 := by linarith
  have h1pₙ_nn : 0 ≤ 1 - pₙ := by linarith
  have h1pₙ_pos : 0 < 1 - pₙ := by
    by_contra h1pₙ; push Not at h1pₙ
    -- From h1pₙ : 1-pₙ ≤ 0 and h1pₙ_nn : 0 ≤ 1-pₙ: 1-pₙ = 0, so (1-pₙ)² = 0
    have := le_antisymm h1pₙ h1pₙ_nn
    nlinarith  -- contradicts h_sq_pos
  have hpₙ_pos : 0 < pₙ := by linarith
  have h2pₙ1 : 0 ≤ 2*pₙ - 1 := by linarith
  -- Q ≤ 0: Q is linear increasing in p₁; at max p₁ it equals -(quartic) ≤ 0
  have hQ : 2 * M pₙ * (2*pₙ - 1) * p₁ - pₙ*(2*pₙ^3 + pₙ - 1) ≤ 0 := by
    have : 2 * M pₙ * (2*pₙ - 1) * p₁ ≤ 2*(2*pₙ - 1)*(1 - pₙ)^2 := by
      nlinarith [mul_nonneg h2pₙ1 (show 0 ≤ (1-pₙ)^2 - p₁*M pₙ by linarith)]
    nlinarith [quartic_nonneg hpₙ23]
  -- Δ·Q ≥ 0: both factors ≤ 0, product ≥ 0
  have hprod : 0 ≤ (p₁ * M pₙ - (1 - pₙ)^2) *
      (2 * M pₙ * (2*pₙ - 1) * p₁ - pₙ*(2*pₙ^3 + pₙ - 1)) := by
    nlinarith [mul_nonneg (show 0 ≤ (1-pₙ)^2 - p₁*M pₙ by linarith)
                          (show 0 ≤ pₙ*(2*pₙ^3+pₙ-1) - 2*M pₙ*(2*pₙ-1)*p₁ by linarith)]
  -- M²L₃ = pₙ²(1-pₙ)P + (≥0) > 0
  have hP_pos : 0 < pₙ^2 * (1 - pₙ) * P pₙ :=
    mul_pos (mul_pos (pow_pos hpₙ_pos 2) h1pₙ_pos) (P_pos pₙ)
  -- But M²L₃ ≤ 0 since M² ≥ 0 and L₃ ≤ 0
  nlinarith [sq_nonneg (M pₙ), mul_nonneg (sq_nonneg (M pₙ)) (show 0 ≤ -L₃ p₁ pₙ by linarith)]

/-! ## Step 3b: p₁M ≥ (1-pₙ)² ⟹ L₅ ≥ 0

  (2pₙ-1)ML₅ = (1-pₙ-p₁)pₙP + MΔg - Δ(1-pₙ-p₁)(2pₙ-1)E
  All three RHS terms are nonneg when Δ ≥ 0, pₙ > 1/2, (p₁,pₙ) ∈ R₁.
  NOTE: requires strict pₙ > 1/2 (not ≤) since we divide out (2pₙ-1)M > 0.
-/

theorem L₅_nonneg_of_Delta_nonneg {p₁ pₙ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₁pₙ : p₁ ≤ pₙ) (hp₁pₙ1 : p₁ + pₙ ≤ 1)
    (hpₙ12 : 1/2 < pₙ) (hDelta : (1 - pₙ)^2 ≤ p₁ * M pₙ) :
    0 ≤ L₅ p₁ pₙ := by
  have hmaster := concavity_master_identity p₁ pₙ
  have hM := M_pos pₙ
  have h2pₙ1 : 0 < 2*pₙ - 1 := by linarith
  have h1pₙp₁ : 0 ≤ 1 - pₙ - p₁ := by linarith
  have hDelta' : 0 ≤ p₁ * M pₙ - (1 - pₙ)^2 := by linarith
  have hpₙ_nn : 0 ≤ pₙ := by linarith
  -- Term 1: (1-pₙ-p₁)pₙP ≥ 0
  have hterm1 : 0 ≤ (1 - pₙ - p₁) * pₙ * P pₙ :=
    mul_nonneg (mul_nonneg h1pₙp₁ hpₙ_nn) (le_of_lt (P_pos pₙ))
  -- Term 2: MΔg ≥ 0
  have hterm2 : 0 ≤ M pₙ * (p₁ * M pₙ - (1 - pₙ)^2) * g pₙ :=
    mul_nonneg (mul_nonneg (le_of_lt hM) hDelta') (g_nonneg (le_of_lt hpₙ12))
  -- Term 3: -Δ(1-pₙ-p₁)(2pₙ-1)E ≥ 0 since -E ≥ 0
  have hnE : 0 ≤ -E p₁ pₙ := by
    rw [neg_E_decomp]; nlinarith [quad_6_8_3_pos pₙ]
  have hterm3 : 0 ≤ -(p₁ * M pₙ - (1 - pₙ)^2) * (1 - pₙ - p₁) * (2*pₙ - 1) * E p₁ pₙ := by
    have key : -(p₁ * M pₙ - (1 - pₙ)^2) * (1 - pₙ - p₁) * (2*pₙ - 1) * E p₁ pₙ =
        (p₁ * M pₙ - (1 - pₙ)^2) * (1 - pₙ - p₁) * (2*pₙ - 1) * (-E p₁ pₙ) := by ring
    rw [key]
    exact mul_nonneg (mul_nonneg (mul_nonneg hDelta' h1pₙp₁) (le_of_lt h2pₙ1)) hnE
  -- (2pₙ-1)ML₅ = sum of three nonneg terms ≥ 0
  have h_key : 0 ≤ (2*pₙ - 1) * M pₙ * L₅ p₁ pₙ := by linarith
  -- Since (2pₙ-1)M > 0 and (2pₙ-1)M·L₅ ≥ 0: L₅ ≥ 0
  -- Proof: if L₅ < 0, then (2pₙ-1)M·L₅ < (2pₙ-1)M·0 = 0, contradicting h_key
  by_contra h_neg
  push Not at h_neg
  have h_prod_pos : 0 < (2*pₙ - 1) * M pₙ := mul_pos h2pₙ1 hM
  have := mul_lt_mul_of_pos_left h_neg h_prod_pos
  rw [mul_zero] at this
  linarith

/-! ## Polynomial Core -/

theorem polynomial_core {p₁ pₙ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₁pₙ : p₁ ≤ pₙ) (hp₁pₙ1 : p₁ + pₙ ≤ 1) :
    0 ≤ L₂ p₁ pₙ ∨ 0 ≤ L₃ p₁ pₙ ∨ 0 ≤ L₅ p₁ pₙ := by
  by_cases hpₙ12 : pₙ ≤ 1/2
  · -- Case A: pₙ ≤ 1/2 → L₂ ≥ 0
    exact Or.inl (L₂_nonneg_of_q_le_half hp₁ hp₁pₙ hp₁pₙ1 hpₙ12)
  · push Not at hpₙ12
    -- hpₙ12 : 1/2 < pₙ (strict!)
    by_cases hpₙ23 : pₙ ≤ 2/3
    · -- Case B: 1/2 < pₙ ≤ 2/3 → L₃ ≥ 0
      exact Or.inr (Or.inl
        (L₃_nonneg_of_q_le_two_thirds hp₁ hp₁pₙ1 (le_of_lt hpₙ12) hpₙ23))
    · push Not at hpₙ23
      -- Case C: pₙ > 2/3
      by_cases hL3 : 0 ≤ L₃ p₁ pₙ
      · exact Or.inr (Or.inl hL3)
      · push Not at hL3
        -- L₃ < 0, pₙ > 2/3: Step 3a gives Δ ≥ 0, Step 3b gives L₅ ≥ 0
        have hDelta := Delta_nonneg_of_L₃_nonpos hp₁ hp₁pₙ1
          (le_of_lt hpₙ23) (le_of_lt hL3)
        exact Or.inr (Or.inr
          (L₅_nonneg_of_Delta_nonneg hp₁ hp₁pₙ hp₁pₙ1 hpₙ12 hDelta))

lemma nonpos_of_div_nonpos_of_pos {x d : ℝ} (hd : 0 < d) (h : x / d ≤ 0) :
    x ≤ 0 := by
  by_contra hx
  have hx' : 0 < x := by linarith
  have : 0 < x / d := div_pos hx' hd
  linarith

lemma div_nonpos_of_nonpos_of_pos {x d : ℝ} (hx : x ≤ 0) (hd : 0 < d) :
    x / d ≤ 0 := by
  have hdinv : 0 ≤ d⁻¹ := by positivity
  simpa [div_eq_mul_inv] using mul_nonpos_of_nonpos_of_nonneg hx hdinv

lemma C₁_normalized {p₁ pₙ : ℝ}
    (hpₙ : 0 < pₙ) (hp₁1 : p₁ < 1) (hpₙ1 : pₙ < 1) :
    C₁ p₁ pₙ - Aₙ p₁ pₙ - (1 / 2 : ℝ)
      = -(L₂ p₁ pₙ) / (2 * ((1 - pₙ) * (1 - p₁))) := by
  have hpₙ0 : pₙ ≠ 0 := ne_of_gt hpₙ
  have hp₁0 : 1 - p₁ ≠ 0 := by linarith
  have hpₙ10 : 1 - pₙ ≠ 0 := by linarith
  unfold C₁ Aₙ L₂
  field_simp
  ring

lemma C₂_normalized {p₁ pₙ : ℝ}
    (hpₙ : 0 < pₙ) (hp₁1 : p₁ < 1) (hpₙ1 : pₙ < 1) :
    C₂ p₁ pₙ - Aₙ p₁ pₙ - (1 / 2 : ℝ)
      = -(L₃ p₁ pₙ) / (2 * (pₙ * (1 - p₁) * (1 - pₙ))) := by
  have hpₙ0 : pₙ ≠ 0 := ne_of_gt hpₙ
  have hp₁0 : 1 - p₁ ≠ 0 := by linarith
  have hpₙ10 : 1 - pₙ ≠ 0 := by linarith
  unfold C₂ Aₙ L₃ R₃
  field_simp
  ring

lemma C₄_normalized {p₁ pₙ : ℝ}
    (hpₙ : 0 < pₙ) (hp₁1 : p₁ < 1) (hpₙ1 : pₙ < 1) :
    C₄ p₁ pₙ - Aₙ p₁ pₙ - (1 / 2 : ℝ)
      = -(L₅ p₁ pₙ) / (2 * (pₙ * (1 - p₁) * (1 - pₙ))) := by
  have hpₙ0 : pₙ ≠ 0 := ne_of_gt hpₙ
  have hp₁0 : 1 - p₁ ≠ 0 := by linarith
  have hpₙ10 : 1 - pₙ ≠ 0 := by linarith
  unfold C₄ Aₙ L₅ N₅
  field_simp
  ring

lemma C₁_le_iff_L₂ {p₁ pₙ : ℝ}
    (hpₙ : 0 < pₙ) (hp₁1 : p₁ < 1) (hpₙ1 : pₙ < 1) :
    (C₁ p₁ pₙ - Aₙ p₁ pₙ ≤ (1 / 2 : ℝ)) ↔ 0 ≤ L₂ p₁ pₙ := by
  have hp₁' : 0 < 1 - p₁ := by linarith
  have hpₙ' : 0 < 1 - pₙ := by linarith
  have hden : 0 < 2 * ((1 - pₙ) * (1 - p₁)) := by nlinarith
  constructor
  · intro h
    have h' : C₁ p₁ pₙ - Aₙ p₁ pₙ - (1 / 2 : ℝ) ≤ 0 := by linarith
    rw [C₁_normalized hpₙ hp₁1 hpₙ1] at h'
    have h'' : -(L₂ p₁ pₙ) ≤ 0 := nonpos_of_div_nonpos_of_pos hden h'
    linarith
  · intro h
    have h'' : -(L₂ p₁ pₙ) ≤ 0 := by linarith
    have h' : -(L₂ p₁ pₙ) / (2 * ((1 - pₙ) * (1 - p₁))) ≤ 0 :=
      div_nonpos_of_nonpos_of_pos h'' hden
    rw [← C₁_normalized hpₙ hp₁1 hpₙ1] at h'
    linarith

lemma C₂_le_iff_L₃ {p₁ pₙ : ℝ}
    (hpₙ : 0 < pₙ) (hp₁1 : p₁ < 1) (hpₙ1 : pₙ < 1) :
    (C₂ p₁ pₙ - Aₙ p₁ pₙ ≤ (1 / 2 : ℝ)) ↔ 0 ≤ L₃ p₁ pₙ := by
  have hp₁' : 0 < 1 - p₁ := by linarith
  have hpₙ' : 0 < 1 - pₙ := by linarith
  have hden0 : 0 < pₙ * (1 - p₁) * (1 - pₙ) := mul_pos (mul_pos hpₙ hp₁') hpₙ'
  have hden : 0 < 2 * (pₙ * (1 - p₁) * (1 - pₙ)) := by nlinarith
  constructor
  · intro h
    have h' : C₂ p₁ pₙ - Aₙ p₁ pₙ - (1 / 2 : ℝ) ≤ 0 := by linarith
    rw [C₂_normalized hpₙ hp₁1 hpₙ1] at h'
    have h'' : -(L₃ p₁ pₙ) ≤ 0 := nonpos_of_div_nonpos_of_pos hden h'
    linarith
  · intro h
    have h'' : -(L₃ p₁ pₙ) ≤ 0 := by linarith
    have h' : -(L₃ p₁ pₙ) / (2 * (pₙ * (1 - p₁) * (1 - pₙ))) ≤ 0 :=
      div_nonpos_of_nonpos_of_pos h'' hden
    rw [← C₂_normalized hpₙ hp₁1 hpₙ1] at h'
    linarith

lemma C₄_le_iff_L₅ {p₁ pₙ : ℝ}
    (hpₙ : 0 < pₙ) (hp₁1 : p₁ < 1) (hpₙ1 : pₙ < 1) :
    (C₄ p₁ pₙ - Aₙ p₁ pₙ ≤ (1 / 2 : ℝ)) ↔ 0 ≤ L₅ p₁ pₙ := by
  have hp₁' : 0 < 1 - p₁ := by linarith
  have hpₙ' : 0 < 1 - pₙ := by linarith
  have hden0 : 0 < pₙ * (1 - p₁) * (1 - pₙ) := mul_pos (mul_pos hpₙ hp₁') hpₙ'
  have hden : 0 < 2 * (pₙ * (1 - p₁) * (1 - pₙ)) := by nlinarith
  constructor
  · intro h
    have h' : C₄ p₁ pₙ - Aₙ p₁ pₙ - (1 / 2 : ℝ) ≤ 0 := by linarith
    rw [C₄_normalized hpₙ hp₁1 hpₙ1] at h'
    have h'' : -(L₅ p₁ pₙ) ≤ 0 := nonpos_of_div_nonpos_of_pos hden h'
    linarith
  · intro h
    have h'' : -(L₅ p₁ pₙ) ≤ 0 := by linarith
    have h' : -(L₅ p₁ pₙ) / (2 * (pₙ * (1 - p₁) * (1 - pₙ))) ≤ 0 :=
      div_nonpos_of_nonpos_of_pos h'' hden
    rw [← C₄_normalized hpₙ hp₁1 hpₙ1] at h'
    linarith

/-! ## Main Theorem

  At least one of the three nonadaptive costs C₁, C₂, C₄ is within 1/2 of
  the better adaptive cost: `min (C₁, C₂, C₄) ≤ 1/2 + Aₙ`. This is the
  strongest form of the statement: the other adaptive cost dominates Aₙ
  on this domain, by the identity
  `(A₁ − Aₙ) · pₙ(1 − p₁) = (pₙ − p₁)(1 − p₁ − pₙ) ≥ 0`. -/

theorem add_adaptivity_gap {p₁ pₙ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₁pₙ : p₁ ≤ pₙ) (hp₁pₙ1 : p₁ + pₙ ≤ 1)
    (hpₙ : 0 ≤ pₙ) (hpₙ1 : pₙ ≤ 1) :
    min (min (C₁ p₁ pₙ) (C₂ p₁ pₙ)) (C₄ p₁ pₙ)
      ≤ 1/2 + Aₙ p₁ pₙ := by
  -- Boundary pₙ = 0: hypotheses force p₁ = 0; expressions degenerate via x/0 = 0
  by_cases hpₙ_zero : pₙ = 0
  · have hp1_zero : p₁ = 0 := le_antisymm (by linarith) hp₁
    subst hpₙ_zero; subst hp1_zero
    unfold Aₙ C₁ C₂ C₄
    norm_num
  -- Boundary pₙ = 1: p₁ + pₙ ≤ 1 forces p₁ = 0
  by_cases hpₙ_one : pₙ = 1
  · have hp1_zero : p₁ = 0 := le_antisymm (by linarith) hp₁
    subst hpₙ_one; subst hp1_zero
    unfold Aₙ C₁ C₂ C₄
    norm_num
  -- Interior 0 < pₙ < 1: original argument applies
  have hpₙ_pos : 0 < pₙ := lt_of_le_of_ne hpₙ (Ne.symm hpₙ_zero)
  have hpₙ_lt : pₙ < 1 := lt_of_le_of_ne hpₙ1 hpₙ_one
  have hp₁1 : p₁ < 1 := by linarith
  rcases polynomial_core hp₁ hp₁pₙ hp₁pₙ1 with h | h | h
  · have hC : C₁ p₁ pₙ - Aₙ p₁ pₙ ≤ 1/2 := (C₁_le_iff_L₂ hpₙ_pos hp₁1 hpₙ_lt).mpr h
    have hle : C₁ p₁ pₙ ≤ 1/2 + Aₙ p₁ pₙ := by linarith
    calc min (min (C₁ p₁ pₙ) (C₂ p₁ pₙ)) (C₄ p₁ pₙ)
        ≤ min (C₁ p₁ pₙ) (C₂ p₁ pₙ) := min_le_left _ _
      _ ≤ C₁ p₁ pₙ := min_le_left _ _
      _ ≤ 1/2 + Aₙ p₁ pₙ := hle
  · have hC : C₂ p₁ pₙ - Aₙ p₁ pₙ ≤ 1/2 := (C₂_le_iff_L₃ hpₙ_pos hp₁1 hpₙ_lt).mpr h
    have hle : C₂ p₁ pₙ ≤ 1/2 + Aₙ p₁ pₙ := by linarith
    calc min (min (C₁ p₁ pₙ) (C₂ p₁ pₙ)) (C₄ p₁ pₙ)
        ≤ min (C₁ p₁ pₙ) (C₂ p₁ pₙ) := min_le_left _ _
      _ ≤ C₂ p₁ pₙ := min_le_right _ _
      _ ≤ 1/2 + Aₙ p₁ pₙ := hle
  · have hC : C₄ p₁ pₙ - Aₙ p₁ pₙ ≤ 1/2 := (C₄_le_iff_L₅ hpₙ_pos hp₁1 hpₙ_lt).mpr h
    have hle : C₄ p₁ pₙ ≤ 1/2 + Aₙ p₁ pₙ := by linarith
    calc min (min (C₁ p₁ pₙ) (C₂ p₁ pₙ)) (C₄ p₁ pₙ)
        ≤ C₄ p₁ pₙ := min_le_right _ _
      _ ≤ 1/2 + Aₙ p₁ pₙ := hle

end
