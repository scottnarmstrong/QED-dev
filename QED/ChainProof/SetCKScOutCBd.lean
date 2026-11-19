/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutCAbs
public import QED.TwoLoop.UnitSCLimitCMasters

/-!
# Set (c), Stage K, group G4: elementary estimates for the outer-massive corner bound

Helper level (no frozen statement). Ingredients of the domination `ScOutCBound t`:

* polynomial bounds on the simplex `y₃, y₄ ≥ 0`, `y₃ + y₄ ≤ 1`, `x ∈ [0, 1]`
  (`|p₂ - 2(x-1)g| ≤ 4`, `|r + p₂| ≤ 5`, `|r| ≤ 3`, `|p₁| ≤ 2`, `|q - p₁| ≤ 3`, `|q| ≤ 1`),
  hence, for `β ≥ g > 0`, the coefficient sizes (**`scOutC_Ac_le`**, **`scOutC_Aa_le`**)
  `|c₁| + |c₂|/β + |c₃|/β² ≤ 3x` and `|a₀| + |a₁|/β + |a₂|/β² ≤ 2x`
  (sampled maxima `2.25x` and `1.25x`, scratch `stageK/g4c2/m.py`);
* logarithm bounds through twelfth roots: `-log y ≤ 12/y^(1/12)` and
  `-log(1-Y) ≤ 2√Y/√(1-Y)`;
* the algebraic step **`scOutC_dom_alg`**: with `Y = ŷ¹²`, `y₃ = b¹²`, `x = ẑ¹²` and
  `a ≥ max(Y², x y₃)` (so `a ≥ ŷ⁶ ẑ⁹ b⁹` and `a ≥ ŷ⁸ ẑ⁸ b⁸`), the sum of the corner bound
  pieces is at most `200 (1 + 1/t) (ŷ⁻⁸ + (√(1-Y))⁻¹) b⁻¹⁰ ẑ⁻⁸`.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit
open QED.TwoLoop.UnitSCReduce (cornerP1 cornerP2)

section Poly

variable {x y3 y4 : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h3 : 0 ≤ y3) (h4 : 0 ≤ y4)
    (hY : y3 + y4 ≤ 1)
include hx0 hx1 h3 h4 hY

theorem scOutC_poly_c1 : |cornerP2 x y3 y4 - 2 * (x - 1) * cornerG y3 y4| ≤ 4 := by
  have h1 := sub_nonneg.2 hx1; have h2 := sub_nonneg.2 hY
  unfold cornerP2 cornerG
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hx0 h3, mul_nonneg hx0 h4, mul_nonneg h3 h4,
      mul_nonneg (mul_nonneg hx0 hx0) h3, mul_nonneg h1 h3, mul_nonneg h2 h3, mul_nonneg h2 h4,
      mul_nonneg (mul_nonneg hx0 h3) h2, mul_nonneg (mul_nonneg hx0 h3) h3]

theorem scOutC_poly_c2 : |cornerR x y3 + cornerP2 x y3 y4| ≤ 5 := by
  have h1 := sub_nonneg.2 hx1; have h2 := sub_nonneg.2 hY
  unfold cornerP2 cornerR
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hx0 h3, mul_nonneg hx0 h4, mul_nonneg h3 h4,
      mul_nonneg (mul_nonneg hx0 hx0) h3, mul_nonneg h1 h3, mul_nonneg h2 h3, mul_nonneg h2 h4,
      mul_nonneg (mul_nonneg hx0 h3) h2, mul_nonneg (mul_nonneg hx0 h3) h3, mul_nonneg h1 h4,
      mul_nonneg (mul_nonneg hx0 h1) h3]

theorem scOutC_poly_c3 : |cornerR x y3| ≤ 3 := by
  unfold cornerR
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hx0 h3, mul_nonneg hx0 h4]

theorem scOutC_poly_a0 : |cornerP1 x y3 y4| ≤ 2 := by
  have h1 := sub_nonneg.2 hx1; have h2 := sub_nonneg.2 hY
  unfold cornerP1
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hx0 h3, mul_nonneg hx0 h4, mul_nonneg h3 h4,
      mul_nonneg (mul_nonneg hx0 hx0) h3, mul_nonneg h1 h3, mul_nonneg h2 h3, mul_nonneg h2 h4,
      mul_nonneg (mul_nonneg hx0 h3) h2, mul_nonneg (mul_nonneg hx0 h3) h3, mul_nonneg h1 h4,
      mul_nonneg (mul_nonneg hx0 h1) h3, mul_nonneg (mul_nonneg hx0 h1) h4,
      mul_nonneg (mul_nonneg h1 h1) h3, mul_nonneg (mul_nonneg h1 h1) h4]

theorem scOutC_poly_a1 : |cornerQ x y3 - cornerP1 x y3 y4| ≤ 3 := by
  have h1 := sub_nonneg.2 hx1; have h2 := sub_nonneg.2 hY
  unfold cornerP1 cornerQ
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hx0 h3, mul_nonneg hx0 h4, mul_nonneg h3 h4,
      mul_nonneg (mul_nonneg hx0 hx0) h3, mul_nonneg h1 h3, mul_nonneg h2 h3, mul_nonneg h2 h4,
      mul_nonneg (mul_nonneg hx0 h3) h2, mul_nonneg (mul_nonneg hx0 h3) h3, mul_nonneg h1 h4,
      mul_nonneg (mul_nonneg hx0 h1) h3, mul_nonneg (mul_nonneg hx0 h1) h4,
      mul_nonneg (mul_nonneg h1 h1) h3, mul_nonneg (mul_nonneg h1 h1) h4]

theorem scOutC_poly_a2 : |cornerQ x y3| ≤ 1 := by
  have h1 := sub_nonneg.2 hx1
  unfold cornerQ
  rw [abs_mul]
  have ha : |x * (2 - x)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg h1 h1]
  have hb : |1 - 2 * y3| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc |x * (2 - x)| * |1 - 2 * y3| ≤ 1 * 1 :=
        mul_le_mul ha hb (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end Poly

section Coef

variable {x y3 y4 β : ℝ}

/-- `|g c| / β ≤ |c|` and `|g² c| / β² ≤ |c|` for `β ≥ g > 0`. -/
theorem scOutC_div_beta_le {g c : ℝ} (hg : 0 < g) (hβ : g ≤ β) :
    |g * c| / β ≤ |c| ∧ |g ^ 2 * c| / β ^ 2 ≤ |c| := by
  have hβ0 : 0 < β := hg.trans_le hβ
  constructor
  · rw [abs_mul, abs_of_pos hg, div_le_iff₀ hβ0]
    nlinarith [abs_nonneg c]
  · rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < g ^ 2), div_le_iff₀ (by positivity)]
    have : g ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hg.le hβ 2
    nlinarith [abs_nonneg c]

/-- **The `c`-coefficient size**: `|c₁| + |c₂|/β + |c₃|/β² ≤ 3x`. -/
theorem scOutC_Ac_le (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h3 : 0 ≤ y3) (h4 : 0 ≤ y4)
    (hY : y3 + y4 ≤ 1) (hg : 0 < cornerG y3 y4) (hβ : cornerG y3 y4 ≤ β) :
    |cornerC1 x y3 y4| + |cornerC2 x y3 y4| / β + |cornerC3 x y3 y4| / β ^ 2 ≤ 3 * x := by
  have p1 := scOutC_poly_c1 hx0 hx1 h3 h4 hY
  have p2 := scOutC_poly_c2 hx0 hx1 h3 h4 hY
  have p3 := scOutC_poly_c3 hx0 hx1 h3 h4 hY
  have e1 : |cornerC1 x y3 y4| = x / 4 * |cornerP2 x y3 y4 - 2 * (x - 1) * cornerG y3 y4| := by
    rw [cornerC1, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x / 4)]
  have e2 : cornerC2 x y3 y4 = cornerG y3 y4 * (x / 4 * (cornerR x y3 + cornerP2 x y3 y4)) := by
    rw [cornerC2]; ring
  have e3 : cornerC3 x y3 y4 = cornerG y3 y4 ^ 2 * (-(x / 4 * cornerR x y3)) := by
    rw [cornerC3]; ring
  have d2 := (scOutC_div_beta_le (c := x / 4 * (cornerR x y3 + cornerP2 x y3 y4)) hg hβ).1
  have d3 := (scOutC_div_beta_le (c := -(x / 4 * cornerR x y3)) hg hβ).2
  rw [← e2] at d2
  rw [← e3] at d3
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x / 4)] at d2
  rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x / 4)] at d3
  have q1 : x / 4 * |cornerP2 x y3 y4 - 2 * (x - 1) * cornerG y3 y4| ≤ x / 4 * 4 :=
    mul_le_mul_of_nonneg_left p1 (by positivity)
  have q2 : x / 4 * |cornerR x y3 + cornerP2 x y3 y4| ≤ x / 4 * 5 :=
    mul_le_mul_of_nonneg_left p2 (by positivity)
  have q3 : x / 4 * |cornerR x y3| ≤ x / 4 * 3 := mul_le_mul_of_nonneg_left p3 (by positivity)
  linarith

/-- **The `a`-coefficient size**: `|a₀| + |a₁|/β + |a₂|/β² ≤ 2x`. -/
theorem scOutC_Aa_le (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h3 : 0 ≤ y3) (h4 : 0 ≤ y4)
    (hY : y3 + y4 ≤ 1) (hg : 0 < cornerG y3 y4) (hβ : cornerG y3 y4 ≤ β) :
    |cornerA0 x y3 y4| + |cornerA1 x y3 y4| / β + |cornerA2 x y3 y4| / β ^ 2 ≤ 2 * x := by
  have p1 := scOutC_poly_a0 hx0 hx1 h3 h4 hY
  have p2 := scOutC_poly_a1 hx0 hx1 h3 h4 hY
  have p3 := scOutC_poly_a2 hx0 hx1 h3 h4 hY
  have e1 : |cornerA0 x y3 y4| = x / 4 * |cornerP1 x y3 y4| := by
    rw [cornerA0, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x / 4)]
  have e2 : cornerA1 x y3 y4 = cornerG y3 y4 * (x / 4 * (cornerQ x y3 - cornerP1 x y3 y4)) := by
    rw [cornerA1]; ring
  have e3 : cornerA2 x y3 y4 = cornerG y3 y4 ^ 2 * (-(x / 4 * cornerQ x y3)) := by
    rw [cornerA2]; ring
  have d2 := (scOutC_div_beta_le (c := x / 4 * (cornerQ x y3 - cornerP1 x y3 y4)) hg hβ).1
  have d3 := (scOutC_div_beta_le (c := -(x / 4 * cornerQ x y3)) hg hβ).2
  rw [← e2] at d2
  rw [← e3] at d3
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x / 4)] at d2
  rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x / 4)] at d3
  have q1 : x / 4 * |cornerP1 x y3 y4| ≤ x / 4 * 2 := mul_le_mul_of_nonneg_left p1 (by positivity)
  have q2 : x / 4 * |cornerQ x y3 - cornerP1 x y3 y4| ≤ x / 4 * 3 :=
    mul_le_mul_of_nonneg_left p2 (by positivity)
  have q3 : x / 4 * |cornerQ x y3| ≤ x / 4 * 1 := mul_le_mul_of_nonneg_left p3 (by positivity)
  linarith

end Coef

section Logs

/-- `-log y ≤ 12/y^(1/12)` for `y > 0`. -/
theorem scOutC_neg_log_le {y : ℝ} (hy : 0 < y) : -log y ≤ 12 / y ^ ((1 : ℝ) / 12) := by
  have hr : 0 < y ^ ((1 : ℝ) / 12) := rpow_pos_of_pos hy _
  have hy' : y = (y ^ ((1 : ℝ) / 12)) ^ (12 : ℕ) := by
    rw [← rpow_natCast, ← rpow_mul hy.le]; norm_num
  have h := log_le_sub_one_of_pos (inv_pos.2 hr)
  rw [log_inv] at h
  conv_lhs => rw [hy', log_pow]
  have : 12 / y ^ ((1 : ℝ) / 12) = 12 * (y ^ ((1 : ℝ) / 12))⁻¹ := by ring
  rw [this]
  push_cast
  have := inv_pos.2 hr
  nlinarith

/-- `-log(1 - Y) ≤ 2√Y/√(1 - Y)` for `0 < Y < 1`. -/
theorem scOutC_neg_log_one_sub_le {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    -log (1 - Y) ≤ 2 * √Y / √(1 - Y) := by
  have h1 : 0 < 1 - Y := by linarith [hY.2]
  set r := √(1 - Y) with hr
  have hr0 : 0 < r := sqrt_pos.2 h1
  have hr1 : r ≤ 1 := by rw [hr, sqrt_le_one]; linarith [hY.1]
  have hr2 : r ^ 2 = 1 - Y := sq_sqrt h1.le
  have hlog : -log (1 - Y) = 2 * log r⁻¹ := by
    rw [← hr2, log_pow, log_inv]; push_cast; ring
  have hl := log_le_sub_one_of_pos (inv_pos.2 hr0)
  have hs : 1 - r ≤ √Y := by
    rw [le_sqrt (by linarith) hY.1.le]
    nlinarith
  rw [hlog]
  calc 2 * log r⁻¹ ≤ 2 * (r⁻¹ - 1) := by linarith
    _ = 2 * (1 - r) / r := by field_simp
    _ ≤ 2 * √Y / r := by gcongr

end Logs

section Alg

theorem scOutC_mul_le_one {p q : ℝ} (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1) : p * q ≤ 1 := by
  rcases le_or_gt p 0 with h | h
  · nlinarith
  · nlinarith

variable {yy b zz S t a ly lx l1 lY : ℝ}

/-- `F₀ = ŷ⁻⁸ b⁻¹⁰ ẑ⁻⁸ ≥ 1`. -/
theorem scOutC_one_le_F0 (hyy : 0 < yy) (hyy1 : yy ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hzz : 0 < zz) (hzz1 : zz ≤ 1) : 1 ≤ 1 / yy ^ 8 * (1 / b ^ 10) * (1 / zz ^ 8) := by
  have h : yy ^ 8 * b ^ 10 * zz ^ 8 ≤ 1 :=
    scOutC_mul_le_one (scOutC_mul_le_one (pow_le_one₀ hyy.le hyy1) (by positivity)
      (pow_le_one₀ hb.le hb1)) (by positivity) (pow_le_one₀ hzz.le hzz1)
  have e : 1 / yy ^ 8 * (1 / b ^ 10) * (1 / zz ^ 8) = 1 / (yy ^ 8 * b ^ 10 * zz ^ 8) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity), one_mul]
  exact h

/-- **The algebraic step of the corner domination.** -/
theorem scOutC_dom_alg (hyy : 0 < yy) (hyy1 : yy ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hzz : 0 < zz) (hzz1 : zz ≤ 1) (hS : 0 < S) (ht : 0 < t)
    (ha1 : yy ^ 6 * zz ^ 9 * b ^ 9 ≤ a) (ha2 : yy ^ 8 * zz ^ 8 * b ^ 8 ≤ a)
    (hly : 0 ≤ ly) (hly' : ly ≤ 12 / b) (hlx : 0 ≤ lx) (hlx' : lx ≤ 12 / zz)
    (hl1 : 0 ≤ l1) (hl1' : l1 ≤ 2 * yy ^ 6 / S) (hlY' : lY ≤ 12 / yy) :
    6 * zz ^ 12 * (3 + ly + lx + l1) / a + 2 / a + (2 + 2 / t * lY) ≤
      200 * (1 + 1 / t) * ((1 / yy ^ 8 + 1 / S) * (1 / b ^ 10) * (1 / zz ^ 8)) := by
  set F₀ := 1 / yy ^ 8 * (1 / b ^ 10) * (1 / zz ^ 8) with hF₀
  set F₁ := 1 / S * (1 / b ^ 10) * (1 / zz ^ 8) with hF₁
  have hF0 : 1 ≤ F₀ := scOutC_one_le_F0 hyy hyy1 hb hb1 hzz hzz1
  have hF1 : 0 ≤ F₁ := by positivity
  have hL1 : 0 < yy ^ 6 * zz ^ 9 * b ^ 9 := by positivity
  have hL2 : 0 < yy ^ 8 * zz ^ 8 * b ^ 8 := by positivity
  have hyy2 : yy ^ 2 ≤ 1 := pow_le_one₀ hyy.le hyy1
  have hzz3 : zz ^ 3 ≤ 1 := pow_le_one₀ hzz.le hzz1
  -- the logarithmic piece
  have hA : zz ^ 12 * (3 + ly + lx) / a ≤ 27 * F₀ := by
    have hl : (3 + ly + lx) * (b * zz) ≤ 27 := by
      have e1 : ly * b ≤ 12 := by rwa [le_div_iff₀ hb] at hly'
      have e2 : lx * zz ≤ 12 := by rwa [le_div_iff₀ hzz] at hlx'
      have e3 : b * zz ≤ 1 := scOutC_mul_le_one hb1 hzz.le hzz1
      nlinarith [mul_le_mul_of_nonneg_left hzz1 (mul_nonneg hly hb.le),
        mul_le_mul_of_nonneg_left hb1 (mul_nonneg hlx hzz.le)]
    calc zz ^ 12 * (3 + ly + lx) / a ≤ zz ^ 12 * (3 + ly + lx) / (yy ^ 6 * zz ^ 9 * b ^ 9) :=
          div_le_div_of_nonneg_left (by positivity) hL1 ha1
      _ = (3 + ly + lx) * (b * zz) * (yy ^ 2 * zz ^ 10) * F₀ := by
          rw [hF₀]; field_simp
      _ ≤ 27 * 1 * F₀ := by
          have h' : yy ^ 2 * zz ^ 10 ≤ 1 :=
            scOutC_mul_le_one hyy2 (by positivity) (pow_le_one₀ hzz.le hzz1)
          exact mul_le_mul_of_nonneg_right (mul_le_mul hl h' (by positivity) (by norm_num))
            (by positivity)
      _ = 27 * F₀ := by ring
  have hB : zz ^ 12 * l1 / a ≤ 2 * F₁ := by
    calc zz ^ 12 * l1 / a ≤ zz ^ 12 * l1 / (yy ^ 6 * zz ^ 9 * b ^ 9) :=
          div_le_div_of_nonneg_left (by positivity) hL1 ha1
      _ ≤ zz ^ 12 * (2 * yy ^ 6 / S) / (yy ^ 6 * zz ^ 9 * b ^ 9) := by gcongr
      _ = 2 * (b * zz ^ 11) * F₁ := by rw [hF₁]; field_simp
      _ ≤ 2 * 1 * F₁ := by
          gcongr
          exact scOutC_mul_le_one hb1 (by positivity) (pow_le_one₀ hzz.le hzz1)
      _ = 2 * F₁ := by ring
  have hC : 1 / a ≤ F₀ := by
    calc 1 / a ≤ 1 / (yy ^ 8 * zz ^ 8 * b ^ 8) := one_div_le_one_div_of_le hL2 ha2
      _ = b ^ 2 * F₀ := by rw [hF₀]; field_simp
      _ ≤ 1 * F₀ := by gcongr; exact pow_le_one₀ hb.le hb1
      _ = F₀ := one_mul _
  have hD : lY ≤ 12 * F₀ := by
    calc lY ≤ 12 / yy := hlY'
      _ = 12 * (yy ^ 7 * b ^ 10 * zz ^ 8) * F₀ := by rw [hF₀]; field_simp
      _ ≤ 12 * 1 * F₀ := by
          gcongr
          exact scOutC_mul_le_one (scOutC_mul_le_one (pow_le_one₀ hyy.le hyy1) (by positivity)
            (pow_le_one₀ hb.le hb1)) (by positivity) (pow_le_one₀ hzz.le hzz1)
      _ = 12 * F₀ := by ring
  have hsplit : 6 * zz ^ 12 * (3 + ly + lx + l1) / a =
      6 * (zz ^ 12 * (3 + ly + lx) / a) + 6 * (zz ^ 12 * l1 / a) := by ring
  have h2a : 2 / a = 2 * (1 / a) := by ring
  have ht' : 0 < 1 / t := by positivity
  have hE : 2 / t * lY ≤ 24 * (1 / t) * F₀ := by
    have := mul_le_mul_of_nonneg_left hD ht'.le
    calc 2 / t * lY = 2 * (1 / t * lY) := by ring
      _ ≤ 2 * (1 / t * (12 * F₀)) := by gcongr
      _ = 24 * (1 / t) * F₀ := by ring
  have hRHS : 200 * (1 + 1 / t) * ((1 / yy ^ 8 + 1 / S) * (1 / b ^ 10) * (1 / zz ^ 8)) =
      200 * F₀ + 200 * F₁ + 200 * (1 / t) * F₀ + 200 * (1 / t) * F₁ := by
    rw [hF₀, hF₁]; ring
  rw [hsplit, h2a, hRHS]
  nlinarith [mul_nonneg ht'.le hF1, mul_le_mul_of_nonneg_left hF0 ht'.le]

end Alg

end QED.ChainProof.SetCK

end
