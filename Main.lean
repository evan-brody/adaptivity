import Mathlib

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open Real

-- ═══════════════════ From CubicDiscriminant.lean ═══════════════════

def evalCubic (a b c d x : ℝ) : ℝ := a * x ^ 3 + b * x ^ 2 + c * x + d

def cubicDiscrim (a b c d : ℝ) : ℝ :=
  18 * a * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 27 * a ^ 2 * d ^ 2

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

-- ═══════════════════ Main definitions ═══════════════════

def A_b (a b : ℝ) : ℝ := b / (1 - a) + 1 / b
def A_a (a b : ℝ) : ℝ := 1 / (1 - a) + (1 - a) / b
def C₂ (b : ℝ) : ℝ := (b ^ 2 - b + 1) / (b * (1 - b))
def C₃ (a b : ℝ) : ℝ := 1 + a / (1 - b) + (1 - a) / b
def C₆ (a b : ℝ) : ℝ :=
  1 + b * (1 + a) / (1 - a * b) + (1 - b) * (2 - a) / (a + b - a * b)
def N₃ (a b : ℝ) : ℝ :=
  5 * a ^ 2 * (1 - 2 * b) + a * (5 * b ^ 2 + 4 * b - 4) +
  (6 * b ^ 3 - 11 * b ^ 2 + 6 * b - 1)
def N₆ (a b : ℝ) : ℝ :=
  5*a^3*b^3 + a^3*b^2 - 6*a^3*b - 6*a^2*b^4 - 4*a^2*b^3 - 2*a^2*b^2 +
  6*a^2 + 6*a*b^4 + 6*a*b^3 + 2*a*b - 6*a - b^3 - 5*b^2 + 4*b

-- ═══════════════════ Denominator clearing ═══════════════════

lemma C₃_le_iff_N₃ {a b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (ha1 : a < 1) :
    C₃ a b ≤ (6/5) * A_b a b ↔ N₃ a b ≤ 0 := by
  have h1b : (0 : ℝ) < 1 - b := by linarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hP : (0 : ℝ) < 5 * b * (1 - b) * (1 - a) :=
    mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 5) hb0) h1b) h1a
  have hid : N₃ a b = (C₃ a b - (6/5) * A_b a b) * (5 * b * (1 - b) * (1 - a)) := by
    unfold N₃ C₃ A_b; field_simp; ring
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma C₆_le_iff_N₆ {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 < b) (hb1 : b < 1) (ha1 : a < 1) :
    C₆ a b ≤ (6/5) * A_b a b ↔ N₆ a b ≤ 0 := by
  have h1 : (0 : ℝ) < 1 - a * b := by nlinarith
  have h2 : (0 : ℝ) < a + b - a * b := by nlinarith
  have h3 : (0 : ℝ) < 1 - a := by linarith
  have hP : (0 : ℝ) < 5 * b * (1 - a * b) * (a + b - a * b) * (1 - a) :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 5) hb0) h1) h2) h3
  have hid : N₆ a b = (C₆ a b - (6/5) * A_b a b) *
      (5 * b * (1 - a * b) * (a + b - a * b) * (1 - a)) := by
    unfold N₆ C₆ A_b; field_simp; ring
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

-- ═══════════════════ Adaptive cost ═══════════════════

lemma A_b_le_A_a {a b : ℝ} (hab : a ≤ b) (hs : a + b ≤ 1) (hb0 : 0 < b)
    (_ha1 : a < 1) : A_b a b ≤ A_a a b := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  suffices h : 0 ≤ A_a a b - A_b a b by linarith
  have hkey : (A_a a b - A_b a b) * (b * (1 - a)) = (b - a) * (1 - a - b) := by
    unfold A_a A_b; field_simp; ring
  have hnum : 0 ≤ (b - a) * (1 - a - b) := mul_nonneg (by linarith) (by linarith)
  have hden : (0 : ℝ) < b * (1 - a) := mul_pos hb0 h1a
  by_contra h_neg; simp only [not_le] at h_neg
  linarith [mul_neg_of_neg_of_pos h_neg hden]

lemma A_b_mono {a₁ a₂ b : ℝ} (hb0 : 0 < b) (ha₂ : a₂ < 1) (h : a₁ ≤ a₂) :
    A_b a₁ b ≤ A_b a₂ b := by
  have h1 : (0 : ℝ) < 1 - a₂ := by linarith
  have h2 : (0 : ℝ) < 1 - a₁ := by linarith
  suffices hsuff : 0 ≤ A_b a₂ b - A_b a₁ b by linarith
  have hkey : (A_b a₂ b - A_b a₁ b) * ((1 - a₁) * (1 - a₂)) = b * (a₂ - a₁) := by
    unfold A_b; field_simp; ring
  have hnum : 0 ≤ b * (a₂ - a₁) := mul_nonneg (le_of_lt hb0) (by linarith)
  have hden : (0 : ℝ) < (1 - a₁) * (1 - a₂) := mul_pos h2 h1
  by_contra h_neg; simp only [not_le] at h_neg
  linarith [mul_neg_of_neg_of_pos h_neg hden]

-- ═══════════════════ Case 1: b ≤ 1/2 ═══════════════════

theorem case1 {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 < b)
    (hb1 : b ≤ 1/2) : C₂ b ≤ (6/5) * A_b a b := by
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  suffices h0 : C₂ b ≤ (6/5) * A_b 0 b by
    linarith [mul_le_mul_of_nonneg_left (A_b_mono hb0 ha1 ha0) (by norm_num : (0:ℝ) ≤ 6/5)]
  suffices hprod : (C₂ b - (6/5) * A_b 0 b) * (5 * b * (1 - b)) =
      (2*b - 1) * (3*b^2 + b + 1) by
    have hden : (0 : ℝ) < 5 * b * (1 - b) :=
      mul_pos (mul_pos (by norm_num : (0:ℝ) < 5) hb0) hb1'
    have hnum : (2*b - 1) * (3*b^2 + b + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by nlinarith [sq_nonneg (b + 1/6)])
    by_contra h_neg; simp only [not_le] at h_neg
    linarith [mul_pos (show (0:ℝ) < C₂ b - 6/5 * A_b 0 b by linarith) hden]
  unfold C₂ A_b; field_simp; ring

-- ═══════════════════ Parabola lemma ═══════════════════

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

-- ═══════════════════ N₆(1−b) < 0 ═══════════════════

lemma N₆_1mb_neg {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) : N₆ (1-b) b < 0 := by
  have key : N₆ (1-b) b = -(b*(b+1)*(b^2-b+1)*(11*b^2-16*b+6)) := by unfold N₆; ring
  rw [key]
  linarith [mul_pos (mul_pos (mul_pos hb0 (show (0:ℝ) < b+1 by linarith))
    (show (0:ℝ) < b^2-b+1 by nlinarith [sq_nonneg (b-1/2)]))
    (show (0:ℝ) < 11*b^2-16*b+6 by nlinarith [sq_nonneg (b-8/11)])]

-- ═══════════════════ N₆ as evalCubic ═══════════════════

lemma N₆_eq_evalCubic (a b : ℝ) :
    N₆ a b = evalCubic (5*b^3+b^2-6*b) (-6*b^4-4*b^3-2*b^2+6)
      (6*b^4+6*b^3+2*b-6) (-b^3-5*b^2+4*b) a := by
  unfold N₆ evalCubic; ring

lemma N₆_leading_ne_zero {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    5*b^3+b^2-6*b ≠ 0 := by
  have : 5*b^3+b^2-6*b = b*(5*b+6)*(b-1) := by ring
  intro h; rw [this] at h
  have := mul_ne_zero (mul_ne_zero (ne_of_gt hb0)
    (show (5:ℝ)*b+6 ≠ 0 by linarith)) (show b-1 ≠ 0 by linarith)
  exact this h

-- ═══════════════════ Discriminant < 0 (Bernstein certificate) ═══════════════════

lemma N₆_disc_neg {b : ℝ} (hb_lo : 1/2 ≤ b) (hb_hi : b ≤ 5/6) :
    cubicDiscrim (5*b^3+b^2-6*b) (-6*b^4-4*b^3-2*b^2+6)
      (6*b^4+6*b^3+2*b-6) (-b^3-5*b^2+4*b) < 0 := by
  unfold cubicDiscrim
  set u := 3 * (b - 1/2) with hu_def
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 := by linarith
  have h1mu : 0 ≤ 1 - u := by linarith
  have hb_eq : b = 1/2 + u/3 := by linarith
  suffices hsuff : 1 ≤ -(18 * (5*b^3+b^2-6*b) * (-6*b^4-4*b^3-2*b^2+6) *
      (6*b^4+6*b^3+2*b-6) * (-b^3-5*b^2+4*b) -
      4 * (-6*b^4-4*b^3-2*b^2+6)^3 * (-b^3-5*b^2+4*b) +
      (-6*b^4-4*b^3-2*b^2+6)^2 * (6*b^4+6*b^3+2*b-6)^2 -
      4 * (5*b^3+b^2-6*b) * (6*b^4+6*b^3+2*b-6)^3 -
      27 * (5*b^3+b^2-6*b)^2 * (-b^3-5*b^2+4*b)^2) by linarith
  have hbern : -(18 * (5*b^3+b^2-6*b) * (-6*b^4-4*b^3-2*b^2+6) *
      (6*b^4+6*b^3+2*b-6) * (-b^3-5*b^2+4*b) -
      4 * (-6*b^4-4*b^3-2*b^2+6)^3 * (-b^3-5*b^2+4*b) +
      (-6*b^4-4*b^3-2*b^2+6)^2 * (6*b^4+6*b^3+2*b-6)^2 -
      4 * (5*b^3+b^2-6*b) * (6*b^4+6*b^3+2*b-6)^3 -
      27 * (5*b^3+b^2-6*b)^2 * (-b^3-5*b^2+4*b)^2) - 1 =
    (39827/1024) * (1-u)^16 + (150083/256) * u * (1-u)^15 +
    (9198857/2304) * u^2 * (1-u)^14 + (112438813/6912) * u^3 * (1-u)^13 +
    (914740163/20736) * u^4 * (1-u)^12 + (5195908745/62208) * u^5 * (1-u)^11 +
    (6978480389/62208) * u^6 * (1-u)^10 + (730348189/6912) * u^7 * (1-u)^9 +
    (74425041467/1119744) * u^8 * (1-u)^8 + (123652426291/5038848) * u^9 * (1-u)^7 +
    (57505087879/15116544) * u^10 * (1-u)^6 + (62771258831/45349632) * u^11 * (1-u)^5 +
    (392465107603/136048896) * u^12 * (1-u)^4 + (288741570409/136048896) * u^13 * (1-u)^3 +
    (95305101785/136048896) * u^14 * (1-u)^2 + (12598913125/136048896) * u^15 * (1-u) +
    (315680707/544195584) * u^16 := by rw [hb_eq]; ring
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

-- ═══════════════════ Case 2: 1/2 < b ≤ 5/6 ═══════════════════

theorem case2 {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1)
    (hb_lo : (1 : ℝ) / 2 < b) (hb_hi : b ≤ 5/6) (hs : a + b ≤ 1) :
    N₃ a b ≤ 0 ∨ N₆ a b ≤ 0 := by
  by_contra h; simp only [not_or, not_le] at h; obtain ⟨hN₃, hN₆⟩ := h
  -- Step 1: N₃(0, b) ≤ 0
  have hN₃_0 : N₃ 0 b ≤ 0 := by
    have : N₃ 0 b = (b - 1) * (2*b - 1) * (3*b - 1) := by unfold N₃; ring
    rw [this]
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · linarith
  -- Step 2: IVT gives a₁ ∈ [0, a] with N₃(a₁) = 0
  have hN₃_cont : Continuous (fun x => N₃ x b) := by unfold N₃; fun_prop
  have hconn_N₃ : IsPreconnected (Set.Icc 0 a) := isPreconnected_Icc
  obtain ⟨a₁, ha₁_mem, ha₁_eq⟩ := IsPreconnected.intermediate_value₂
    hconn_N₃ (Set.left_mem_Icc.mpr ha0) (Set.right_mem_Icc.mpr ha0)
    hN₃_cont.continuousOn continuousOn_const hN₃_0 (le_of_lt hN₃)
  -- ha₁_eq : N₃ a₁ b = 0
  have ha₁_ge : 0 ≤ a₁ := ha₁_mem.1
  have ha₁_le : a₁ ≤ a := ha₁_mem.2
  -- Step 3: Polynomial identity: 25(2b-1)²·N₆ = Qt·N₃ + Rt
  have hpoly_id : ∀ x, 25 * (2*b-1)^2 * N₆ x b =
      (-50*x*b^4+15*x*b^3+65*x*b^2-30*x*b+35*b^5-15*b^4+46*b^3+18*b^2-84*b+30) *
      N₃ x b + (125*x*b^7-105*x*b^6+45*x*b^5-29*x*b^4+177*x*b^3-297*x*b^2+
      164*x*b-30*x-210*b^8+475*b^7-651*b^6+423*b^5+11*b^4-291*b^3+327*b^2-164*b+30) := by
    intro x; unfold N₃ N₆; ring
  have hid_a₁ := hpoly_id a₁
  rw [ha₁_eq, mul_zero, zero_add] at hid_a₁
  have b_term_pos : (0 : ℝ) < (2*b-1) := by linarith
  -- Step 4: Rt(a₁) ≤ 0 using constraint N₃(a₁) = 0
  have h25sq : (0 : ℝ) < 25 * (2*b-1)^2 := by positivity
  have hN₃_zero : 5*(1-2*b)*a₁^2 + (5*b^2+4*b-4)*a₁ + (6*b^3-11*b^2+6*b-1) = 0 := by
    have : N₃ a₁ b = 5*a₁^2*(1-2*b) + a₁*(5*b^2+4*b-4) + (6*b^3-11*b^2+6*b-1) := by
      unfold N₃; ring
    linarith [ha₁_eq]
  have hRt_le : 125*a₁*b^7 - 105*a₁*b^6 + 45*a₁*b^5 - 29*a₁*b^4 + 177*a₁*b^3 -
      297*a₁*b^2 + 164*a₁*b - 30*a₁ - 210*b^8 + 475*b^7 - 651*b^6 + 423*b^5 +
      11*b^4 - 291*b^3 + 327*b^2 - 164*b + 30 ≤ 0 := by
    -- Split on sign of ρ₁ (coefficient of a₁ in the remainder)
    by_cases hρ : 0 ≤ 125*b^7-105*b^6+45*b^5-29*b^4+177*b^3-297*b^2+164*b-30
    · -- Case ρ₁ ≥ 0: Rt increasing in a₁, so Rt(a₁) ≤ Rt(1-b)
      -- First show Rt(1-b) ≤ 0 via Rt(1-b) = -b·(Rt_inner) with Rt_inner ≥ 0
      suffices h1mb : -b*(335*b^7-705*b^6+801*b^5-497*b^4+195*b^3-183*b^2+134*b-30) ≤ 0 by
        have hRt_ring : 125*a₁*b^7-105*a₁*b^6+45*a₁*b^5-29*a₁*b^4+177*a₁*b^3-
            297*a₁*b^2+164*a₁*b-30*a₁-210*b^8+475*b^7-651*b^6+423*b^5+
            11*b^4-291*b^3+327*b^2-164*b+30 =
            -b*(335*b^7-705*b^6+801*b^5-497*b^4+195*b^3-183*b^2+134*b-30) -
            (125*b^7-105*b^6+45*b^5-29*b^4+177*b^3-297*b^2+164*b-30)*(1-b-a₁) := by ring
        linarith [mul_nonneg hρ (show (0:ℝ) ≤ 1-b-a₁ by linarith)]
      have hRtI : 0 ≤ 335*b^7-705*b^6+801*b^5-497*b^4+195*b^3-183*b^2+134*b-30 := by
        set v := 3*(b-1/2) with hv_def
        have hv0 : 0 ≤ v := by linarith
        have h1mv : 0 ≤ 1-v := by linarith
        have hbern : 335*b^7-705*b^6+801*b^5-497*b^4+195*b^3-183*b^2+134*b-30 =
            (153/128)*(1-v)^7+(1221/128)*v*(1-v)^6+(9103/384)*v^2*(1-v)^5+
            (9107/384)*v^3*(1-v)^4+(4145/384)*v^4*(1-v)^3+(113935/10368)*v^5*(1-v)^2+
            (1440719/93312)*v^6*(1-v)+(1971865/279936)*v^7 := by rw [show b = 1/2+v/3 from by linarith]; ring
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
      by_cases h54 : 5*b^2+4*b-4 ≤ 0
      · -- Sub-case 5b²+4b-4 ≤ 0: forces a₁ = 0, contradiction with N₃(0,b) < 0
        exfalso
        have hγ : 6*b^3-11*b^2+6*b-1 ≤ 0 := by
          have : N₃ 0 b = 6*b^3-11*b^2+6*b-1 := by unfold N₃; ring
          linarith [hN₃_0]
        have hsq_nonpos : 5*(2*b-1)*a₁^2 ≤ 0 := by
          have := mul_nonpos_of_nonpos_of_nonneg h54 ha₁_ge
          nlinarith
        have ha₁_zero : a₁ = 0 := by
          by_contra hne
          have hpos : 0 < a₁ := lt_of_le_of_ne ha₁_ge (Ne.symm hne)
          have : 0 < 5*(2*b-1)*a₁^2 := by positivity
          linarith
        rw [ha₁_zero] at ha₁_eq
        have hN₃_0_neg : N₃ 0 b < 0 := by
          have : N₃ 0 b = (b-1)*(2*b-1)*(3*b-1) := by unfold N₃; ring
          rw [this]
          exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith)) (by linarith)
        linarith
      · -- Sub-case 5b²+4b-4 > 0: use polynomial identity
        push Not at h54
        -- Identity: (5b²+4b-4)·Rt = 5·ρ₁·(2b-1)·a₁² + F(b), derived from N₃(a₁)=0
        have h_prod : (125*b^7-105*b^6+45*b^5-29*b^4+177*b^3-297*b^2+164*b-30) *
            (5*(1-2*b)*a₁^2+(5*b^2+4*b-4)*a₁+(6*b^3-11*b^2+6*b-1)) = 0 := by
          rw [hN₃_zero]; ring
        have hid : (5*b^2+4*b-4)*(125*a₁*b^7-105*a₁*b^6+45*a₁*b^5-29*a₁*b^4+
            177*a₁*b^3-297*a₁*b^2+164*a₁*b-30*a₁-210*b^8+475*b^7-651*b^6+423*b^5+
            11*b^4-291*b^3+327*b^2-164*b+30) =
            5*(125*b^7-105*b^6+45*b^5-29*b^4+177*b^3-297*b^2+164*b-30)*(2*b-1)*a₁^2+
            (-1800*b^10+3540*b^9-2690*b^8-965*b^7+2595*b^6+845*b^5-4915*b^4+5595*b^3-
            3425*b^2+1120*b-150) := by
          have hring : (5*b^2+4*b-4)*(125*a₁*b^7-105*a₁*b^6+45*a₁*b^5-29*a₁*b^4+
              177*a₁*b^3-297*a₁*b^2+164*a₁*b-30*a₁-210*b^8+475*b^7-651*b^6+423*b^5+
              11*b^4-291*b^3+327*b^2-164*b+30)-
              5*(125*b^7-105*b^6+45*b^5-29*b^4+177*b^3-297*b^2+164*b-30)*(2*b-1)*a₁^2-
              (-1800*b^10+3540*b^9-2690*b^8-965*b^7+2595*b^6+845*b^5-4915*b^4+5595*b^3-
              3425*b^2+1120*b-150) =
              (125*b^7-105*b^6+45*b^5-29*b^4+177*b^3-297*b^2+164*b-30)*
              (5*(1-2*b)*a₁^2+(5*b^2+4*b-4)*a₁+(6*b^3-11*b^2+6*b-1)) := by ring
          linarith
        -- First term ≤ 0: ρ₁ < 0, (2b-1) > 0, a₁² ≥ 0
        have hterm1 : 5*(125*b^7-105*b^6+45*b^5-29*b^4+177*b^3-297*b^2+164*b-30)*
            (2*b-1)*a₁^2 ≤ 0 := by
          have h1 : 0 ≤ -(125*b^7-105*b^6+45*b^5-29*b^4+177*b^3-297*b^2+164*b-30) := by linarith
          have h2 : (0:ℝ) ≤ 2*b-1 := by linarith
          nlinarith [mul_nonneg (mul_nonneg h1 h2) (sq_nonneg a₁)]
        -- F(b) = -5·(2b-1)²·G(b) ≤ 0 where G ≥ 0
        have hG : 0 ≤ 90*b^8-87*b^7+25*b^6+95*b^5-41*b^4-107*b^3+149*b^2-104*b+30 := by
          by_cases h23 : b ≤ 2/3
          · -- G ≥ 0 on [1/2, 2/3] via Bernstein degree 8, w = 6·(b-1/2)
            set w := 6*(b-1/2) with hw_def
            have hw0 : 0 ≤ w := by linarith
            have h1mw : 0 ≤ 1-w := by linarith
            have hbern : 90*b^8-87*b^7+25*b^6+95*b^5-41*b^4-107*b^3+149*b^2-104*b+30 =
                (75/32)*(1-w)^8+(1861/128)*w*(1-w)^7+(2405/64)*w^2*(1-w)^6+
                (4969/96)*w^3*(1-w)^5+(17353/432)*w^4*(1-w)^4+(33167/1944)*w^5*(1-w)^3+
                (11095/2916)*w^6*(1-w)^2+(544/729)*w^7*(1-w)+(154/729)*w^8 := by
              rw [show b = 1/2+w/6 from by linarith]; ring
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
          · -- G ≥ 0 on [2/3, 5/6] via Bernstein degree 8, w = 6·(b-2/3)
            push Not at h23
            set w := 6*(b-2/3) with hw_def
            have hw0 : 0 ≤ w := by linarith
            have h1mw : 0 ≤ 1-w := by linarith
            have hbern : 90*b^8-87*b^7+25*b^6+95*b^5-41*b^4-107*b^3+149*b^2-104*b+30 =
                (154/729)*(1-w)^8+(640/243)*w*(1-w)^7+(16541/972)*w^2*(1-w)^6+
                (353147/5832)*w^3*(1-w)^5+(487957/3888)*w^4*(1-w)^4+(135295/864)*w^5*(1-w)^3+
                (5432377/46656)*w^6*(1-w)^2+(1483721/31104)*w^7*(1-w)+(129295/15552)*w^8 := by
              rw [show b = 2/3+w/6 from by linarith]; ring
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
        have hF : -1800*b^10+3540*b^9-2690*b^8-965*b^7+2595*b^6+845*b^5-4915*b^4+
            5595*b^3-3425*b^2+1120*b-150 ≤ 0 := by
          have hF_eq : -1800*b^10+3540*b^9-2690*b^8-965*b^7+2595*b^6+845*b^5-4915*b^4+
              5595*b^3-3425*b^2+1120*b-150 = -5*(2*b-1)^2*
              (90*b^8-87*b^7+25*b^6+95*b^5-41*b^4-107*b^3+149*b^2-104*b+30) := by ring
          nlinarith [sq_nonneg (2*b-1)]
        -- Combine: (5b²+4b-4)·Rt ≤ 0, and 5b²+4b-4 > 0, so Rt ≤ 0
        have h_prod_nonpos : (5*b^2+4*b-4)*(125*a₁*b^7-105*a₁*b^6+45*a₁*b^5-29*a₁*b^4+
            177*a₁*b^3-297*a₁*b^2+164*a₁*b-30*a₁-210*b^8+475*b^7-651*b^6+423*b^5+
            11*b^4-291*b^3+327*b^2-164*b+30) ≤ 0 := by linarith
        by_contra habs; push Not at habs
        linarith [mul_pos h54 habs]
  -- Step 5: N₆(a₁) ≤ 0
  have hN₆_a₁ : N₆ a₁ b ≤ 0 := by
    by_contra h_pos; simp only [not_le] at h_pos
    linarith [mul_pos h25sq h_pos]
  -- Step 6: IVT for two roots of N₆
  have hN₆_cont : Continuous (fun x => N₆ x b) := by unfold N₆; fun_prop
  -- Root r₁ in [a₁, a]: N₆(a₁) ≤ 0 < N₆(a)
  obtain ⟨r₁, hr₁_mem, hr₁_eq⟩ := IsPreconnected.intermediate_value₂
    isPreconnected_Icc (Set.left_mem_Icc.mpr ha₁_le) (Set.right_mem_Icc.mpr ha₁_le)
    hN₆_cont.continuousOn continuousOn_const hN₆_a₁ (le_of_lt hN₆)
  -- Root r₂ in [a, 1-b]: swap f and g since N₆(a) > 0 > N₆(1-b)
  have ha_1mb : a ≤ 1 - b := by linarith
  have hN₆_end := N₆_1mb_neg (by linarith) hb1
  obtain ⟨r₂, hr₂_mem, hr₂_eq⟩ := IsPreconnected.intermediate_value₂
    isPreconnected_Icc (Set.left_mem_Icc.mpr ha_1mb) (Set.right_mem_Icc.mpr ha_1mb)
    continuousOn_const hN₆_cont.continuousOn (le_of_lt hN₆) (le_of_lt hN₆_end)
  -- hr₂_eq : 0 = N₆ r₂ b
  -- Step 7: r₁ ≠ r₂
  have hr₁_le : r₁ ≤ a := hr₁_mem.2
  have hr₂_ge : a ≤ r₂ := hr₂_mem.1
  have hr_ne : r₁ ≠ r₂ := by
    intro heq; subst heq; have : r₁ = a := le_antisymm hr₁_le hr₂_ge
    subst this; linarith
  -- Step 8: two_roots_discrim_nonneg
  have hr₁_root : evalCubic (5*b^3+b^2-6*b) (-6*b^4-4*b^3-2*b^2+6)
      (6*b^4+6*b^3+2*b-6) (-b^3-5*b^2+4*b) r₁ = 0 := by
    rw [← N₆_eq_evalCubic]; exact hr₁_eq
  have hr₂_root : evalCubic (5*b^3+b^2-6*b) (-6*b^4-4*b^3-2*b^2+6)
      (6*b^4+6*b^3+2*b-6) (-b^3-5*b^2+4*b) r₂ = 0 := by
    rw [← N₆_eq_evalCubic]; exact hr₂_eq.symm
  have hdisc_nn := two_roots_discrim_nonneg _ _ _ _ r₁ r₂
    (N₆_leading_ne_zero (by linarith) hb1) hr_ne hr₁_root hr₂_root
  -- Step 9: Contradiction with disc < 0
  linarith [N₆_disc_neg (le_of_lt hb_lo) hb_hi]

-- ═══════════════════ Case 3: 5/6 < b < 1 ═══════════════════

def Q_div (a b : ℝ) : ℝ :=
  (5*b^3+b^2-6*b)*a^2 + (-11*b^4+5*b^2-6*b+6)*a + (11*b^5-5*b^4+b^3+11*b^2-10*b)

lemma N₆_diff_factor (a b : ℝ) :
    N₆ (1-b) b - N₆ a b = (1 - b - a) * Q_div a b := by unfold N₆ Q_div; ring

lemma Q_leading_nonpos {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) : 5*b^3+b^2-6*b ≤ 0 := by
  have : 5*b^3+b^2-6*b = b*(5*b+6)*(b-1) := by ring
  nlinarith [mul_pos hb0 (show (0:ℝ) < 5*b+6 by linarith)]

lemma Q_at_zero_nonneg {b : ℝ} (hb : 5/6 ≤ b) : 0 ≤ Q_div 0 b := by
  have heq : Q_div 0 b = b * (11*b^4-5*b^3+b^2+11*b-10) := by unfold Q_div; ring
  rw [heq]; apply mul_nonneg (by linarith)
  have : 11*b^4-5*b^3+b^2+11*b-10 =
    2945/1296 + (b-5/6)*(11*b^3+25*b^2/6+161*b/36+3181/216) := by ring
  rw [this]
  have hd : (0:ℝ) ≤ b-5/6 := by linarith
  have hb0 : (0:ℝ) ≤ b := by linarith
  have hb2 : (0:ℝ) ≤ b^2 := sq_nonneg b
  have hb3 : (0:ℝ) ≤ b^3 := by nlinarith
  have hbr : (0:ℝ) ≤ 11*b^3+25*b^2/6+161*b/36+3181/216 := by nlinarith
  linarith [mul_nonneg hd hbr]

lemma Q_at_1mb_nonneg {b : ℝ} (hb : 5/6 ≤ b) : 0 ≤ Q_div (1-b) b := by
  have heq : Q_div (1-b) b = 27*b^5-25*b^4-7*b^3+35*b^2-28*b+6 := by unfold Q_div; ring
  rw [heq]
  have : 27*b^5-25*b^4-7*b^3+35*b^2-28*b+6 =
    4447/2592 + (b-5/6)*(9929/432 + (b-5/6)*(27*b^3+20*b^2+91*b/12+135/4)) := by ring
  rw [this]
  have hd : (0:ℝ) ≤ b-5/6 := by linarith
  have hb2 : (0:ℝ) ≤ b^2 := sq_nonneg b
  have hb3 : (0:ℝ) ≤ b^3 := by nlinarith [show (0:ℝ) ≤ b by linarith]
  have hbr : (0:ℝ) ≤ 27*b^3+20*b^2+91*b/12+135/4 := by nlinarith [show (0:ℝ) ≤ b by linarith]
  have hm : (0:ℝ) ≤ 9929/432 + (b-5/6)*(27*b^3+20*b^2+91*b/12+135/4) := by
    linarith [mul_nonneg hd hbr]
  linarith [mul_nonneg hd hm]

lemma Q_nonneg {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ 1-b) (hb : 5/6 ≤ b)
    (hb1 : b < 1) : 0 ≤ Q_div a b := by
  have hidA : Q_div a b = (5*b^3+b^2-6*b)*a^2 + (-11*b^4+5*b^2-6*b+6)*a +
      (11*b^5-5*b^4+b^3+11*b^2-10*b) := by unfold Q_div; ring
  have hid0 : Q_div 0 b = (5*b^3+b^2-6*b)*0^2 + (-11*b^4+5*b^2-6*b+6)*0 +
      (11*b^5-5*b^4+b^3+11*b^2-10*b) := by unfold Q_div; ring
  have hid1 : Q_div (1-b) b = (5*b^3+b^2-6*b)*(1-b)^2 + (-11*b^4+5*b^2-6*b+6)*(1-b) +
      (11*b^5-5*b^4+b^3+11*b^2-10*b) := by unfold Q_div; ring
  rw [hidA]; exact concave_ge (Q_leading_nonpos (by linarith) hb1) ha0 hab
    (by rw [← hid0]; exact Q_at_zero_nonneg hb)
    (by rw [← hid1]; exact Q_at_1mb_nonneg hb)

lemma N₆_mono {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ 1-b) (hb : 5/6 ≤ b)
    (hb1 : b < 1) : N₆ a b ≤ N₆ (1-b) b :=
  le_of_sub_nonneg (by linarith [N₆_diff_factor a b,
    (mul_nonneg (show (0:ℝ) ≤ 1-b-a by linarith) (Q_nonneg ha0 hab hb hb1))])

theorem case3 {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ 1-b) (hb : 5/6 < b)
    (hb1 : b < 1) : N₆ a b ≤ 0 :=
  le_trans (N₆_mono ha0 hab (le_of_lt hb) hb1) (le_of_lt (N₆_1mb_neg (by linarith) hb1))

-- ═══════════════════ Assembly ═══════════════════

theorem bound_lower_half {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb0 : 0 < b)
    (hb1 : b < 1) (ha1 : a < 1) (hs : a + b ≤ 1) :
    C₂ b ≤ (6/5) * A_b a b ∨ C₃ a b ≤ (6/5) * A_b a b ∨
    C₆ a b ≤ (6/5) * A_b a b := by
  by_cases hb2 : b ≤ 1/2
  · exact Or.inl (case1 ha0 ha1 hb0 hb2)
  · simp only [not_le] at hb2
    by_cases hb4 : b ≤ 5/6
    · rcases case2 ha0 hab hb1 hb2 hb4 hs with h | h
      · exact Or.inr (Or.inl ((C₃_le_iff_N₃ hb0 hb1 ha1).mpr h))
      · exact Or.inr (Or.inr ((C₆_le_iff_N₆ ha0 hb0 hb1 ha1).mpr h))
    · simp only [not_le] at hb4
      exact Or.inr (Or.inr ((C₆_le_iff_N₆ ha0 hb0 hb1 ha1).mpr
        (case3 ha0 (by linarith) hb4 hb1)))

theorem adaptivity_gap {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hab : a ≤ b) (hs : a + b ≤ 1) :
    ∃ cost, (cost = C₂ b ∨ cost = C₃ a b ∨ cost = C₆ a b) ∧
    cost ≤ (6/5) * min (A_a a b) (A_b a b) := by
  -- Boundary case b = 0 (forces a = 0; all costs are junk values via div-by-zero)
  rcases eq_or_lt_of_le hb0 with rfl | hb0'
  · have : a = 0 := le_antisymm (by linarith) ha0; subst this
    exact ⟨C₂ 0, Or.inl rfl, by unfold C₂ A_a A_b; norm_num⟩
  -- Boundary case b = 1 (forces a = 0 from a + b ≤ 1)
  rcases eq_or_lt_of_le hb1 with rfl | hb1'
  · have : a = 0 := le_antisymm (by linarith) ha0; subst this
    exact ⟨C₂ 1, Or.inl rfl, by unfold C₂ A_a A_b; norm_num⟩
  -- Interior: 0 < b < 1
  have ha1' : a < 1 := by linarith
  rw [min_eq_right (A_b_le_A_a hab hs hb0' ha1')]
  rcases bound_lower_half ha0 hab hb0' hb1' ha1' hs with h | h | h
  · exact ⟨C₂ b, Or.inl rfl, h⟩
  · exact ⟨C₃ a b, Or.inr (Or.inl rfl), h⟩
  · exact ⟨C₆ a b, Or.inr (Or.inr rfl), h⟩

theorem tight : C₂ (1/2 : ℝ) = (6/5) * A_b 0 (1/2 : ℝ) := by unfold C₂ A_b; norm_num

end
