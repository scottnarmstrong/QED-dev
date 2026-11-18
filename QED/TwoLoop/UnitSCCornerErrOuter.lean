/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerErrInner
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner error terms: the outer photon at mass `Λ`

Section 2.3 of `docs/TWO-LOOP-UNITS.md` for the corner graph. The Pauli–Villars pair with the
outer photon at mass `Λ`, `O = cornerOut Λ λ Λ`, is kept as the `b`-integral
`∫_{b > β} [A₂ (1/D₁² - 1/D₂²) + A₁ (1/D₁ - 1/D₂)] db` (its mass function can vanish). Each
denominator is bounded below on the integration range by the positive linear function
`D ≥ P + (b - β) H`, `P = Y² + β x`, `H = h_Λ = (x² + (1-x) Λ²)/x` (`cornerP_le_massAt`), since the
outer photon parameter `z_a = b(1-x)/x - e` is nonnegative. This file proves, for
`0 < λ ≤ 1 ≤ Λ`, `(y₃, y₄)` in the open triangle and `0 < x < 1` (`abs_cornerOut_le`):

`|O| ≤ x²/(Λ √P) + (3/2) x/(P H) + 4 x/(√β √P √H)` (`cornerOutBound`).

The steps: the integrand is bounded by `c₀ (1/D₁ - 1/D₂) + (3/2) x/(P + zH)² + 4 x/(√β √P + z √H)²`
(`abs_cornerOut_integrand_le`; the masters are monotone in the mass, the coefficients are bounded
by `QED.TwoLoop.UnitSCCorner.abs_cornerA0_le` and friends, and
`(z + β)(P + zH) ≥ (√β √P + z √H)²`), whose integral is elementary (`hasIoiInt_inv_sq`,
`hasIoiInt_inv_sub`); the logarithm `log(1 + Δ/D₁(β))`, `Δ ≤ Λ²`, is at most `2 Λ/√P`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-! ### Two elementary improper integrals -/

/-- `∫₀^∞ dz/(a + z c)² = 1/(a c)`. -/
theorem hasIoiInt_inv_sq {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    HasIoiInt (fun z => 1 / (a + z * c) ^ 2) (1 / (a * c)) := by
  have hd : ∀ z ∈ Ici (0 : ℝ), HasDerivAt (fun z => -(1 / (c * (a + z * c))))
      (1 / (a + z * c) ^ 2) z := fun z hz => by
    have hz' : (0 : ℝ) ≤ z := hz
    have p1 : 0 < a + z * c := by positivity
    have : HasDerivAt (fun z => (c * (a + z * c))⁻¹) (-(c * (1 * c)) / (c * (a + z * c)) ^ 2) z :=
      ((((hasDerivAt_id z).mul_const c).const_add a).const_mul c).inv
        (by simp only [id]; positivity)
    simp only [one_div]
    refine this.neg.congr_deriv ?_
    field_simp
  have hk : (∀ z ∈ Ioi (0 : ℝ), 0 ≤ 1 / (a + z * c) ^ 2) ∨
      (∀ z ∈ Ioi (0 : ℝ), 1 / (a + z * c) ^ 2 ≤ 0) := Or.inl fun z _ => by positivity
  have hl : Tendsto (fun z => -(1 / (c * (a + z * c)))) atTop (𝓝 (-(0 / c))) := by
    refine ((tendsto_inv_add_atTop (M := a) hc).div_const c).neg.congr fun z => ?_
    field_simp
  have := hasIoiInt_shift hd hk hl
  refine this.congr (fun z _ => by rw [add_zero]) ?_
  simp only [zero_mul, add_zero]
  field_simp
  ring

/-- `∫₀^∞ (1/(a + z c) - 1/(a' + z c)) dz = (log a' - log a)/c`. -/
theorem hasIoiInt_inv_sub {a a' c : ℝ} (ha : 0 < a) (ha' : 0 < a') (hc : 0 < c) :
    HasIoiInt (fun z => 1 / (a + z * c) - 1 / (a' + z * c)) ((log a' - log a) / c) := by
  have hd : ∀ z ∈ Ici (0 : ℝ), HasDerivAt (fun z => (log (a + z * c) - log (a' + z * c)) / c)
      (1 / (a + z * c) - 1 / (a' + z * c)) z := fun z hz => by
    have hz' : (0 : ℝ) ≤ z := hz
    have p1 : 0 < a + z * c := by positivity
    have p2 : 0 < a' + z * c := by positivity
    have := ((hasDerivAt_log_add p1).sub (hasDerivAt_log_add p2)).div_const c
    refine this.congr_deriv ?_
    field_simp
  have hk : (∀ z ∈ Ioi (0 : ℝ), 0 ≤ 1 / (a + z * c) - 1 / (a' + z * c)) ∨
      (∀ z ∈ Ioi (0 : ℝ), 1 / (a + z * c) - 1 / (a' + z * c) ≤ 0) := by
    rcases le_total a a' with hle | hle
    · left
      intro z hz
      have hz' : (0 : ℝ) < z := hz
      have p1 : 0 < a + z * c := by positivity
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le p1 (by linarith)
    · right
      intro z hz
      have hz' : (0 : ℝ) < z := hz
      have p2 : 0 < a' + z * c := by positivity
      rw [sub_nonpos]
      exact one_div_le_one_div_of_le p2 (by linarith)
  have := hasIoiInt_shift hd hk (tendsto_log_sub_log_atTop' ha.le ha'.le hc)
  refine this.congr (fun z _ => by rw [add_zero]) ?_
  simp only [zero_mul, add_zero]
  ring

/-! ### The lower bound on the denominators -/

/-- `P = Y² + β x`, the value at `b = β` of the lower bound of the denominators. -/
noncomputable def cornerP (y3 y4 x : ℝ) : ℝ :=
  (y3 + y4) ^ 2 + betaG (cornerG y3 y4) (y3 * y4) x * x

section Outer

variable {lam Lam x y3 y4 : ℝ}

theorem sq_le_cornerP (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (hY : y3 + y4 < 1) :
    (y3 + y4) ^ 2 ≤ cornerP y3 y4 x := by
  unfold cornerP
  have := betaG_pos (e := y3 * y4) (x := x) (cornerG_pos h3 hY)
  have := hx.1
  nlinarith

theorem cornerP_pos (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1) :
    0 < cornerP y3 y4 x :=
  lt_of_lt_of_le (by positivity) (sq_le_cornerP hx h3 hY)

/-- **The denominator at `b = β` is at least `P`**: `M(Λ, μ) + β h_Λ ≥ Y² + β x`. -/
theorem cornerP_le_massAt (μ : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hY : y3 + y4 < 1) :
    cornerP y3 y4 x ≤
      cornerMass Lam μ y3 y4 + betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 Lam x / x) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hb := betaG_mul_one_sub_ge (g := cornerG y3 y4) (e := y3 * y4) ⟨hx0, hx1⟩
  unfold cornerP cornerMass ladderInnerMass
  have e : betaG (cornerG y3 y4) (y3 * y4) x * ((x ^ 2 * 1 ^ 2 + (1 - x) * Lam ^ 2) / x) =
      betaG (cornerG y3 y4) (y3 * y4) x * x +
        Lam ^ 2 * (betaG (cornerG y3 y4) (y3 * y4) x * (1 - x)) / x := by
    field_simp
  rw [e]
  have h1 : Lam ^ 2 * (y3 * y4) ≤ Lam ^ 2 * (betaG (cornerG y3 y4) (y3 * y4) x * (1 - x)) / x := by
    rw [le_div_iff₀ hx0]
    have := mul_le_mul_of_nonneg_left hb (sq_nonneg Lam)
    linarith
  have h2 : 0 ≤ (1 - (y3 + y4)) * μ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  linarith

theorem one_le_hLam (hLam : 1 ≤ Lam) (hx : x ∈ Ioo (0 : ℝ) 1) :
    1 ≤ ladderInnerMass 1 Lam x / x := by
  obtain ⟨hx0, hx1⟩ := hx
  rw [le_div_iff₀ hx0]
  unfold ladderInnerMass
  have : 1 ≤ Lam ^ 2 := by nlinarith
  nlinarith [sq_nonneg (1 - x)]

/-- `c₀/h_Λ ≤ x²/(2 Λ²)`. -/
theorem cornerC0_div_hLam_le (hLam : 1 ≤ Lam) (hx : x ∈ Ioo (0 : ℝ) 1) :
    cornerC0 x / (ladderInnerMass 1 Lam x / x) ≤ x ^ 2 / (2 * Lam ^ 2) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hm := ladderInnerMass_pos one_pos (by linarith : (0 : ℝ) < Lam) ⟨hx0.le, hx1.le⟩
  unfold cornerC0
  rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  unfold ladderInnerMass
  have h1 : 0 < 1 - x := by linarith
  have : 0 ≤ x ^ 2 * 1 ^ 2 * (x ^ 2 * (1 - x) * 2) := by positivity
  nlinarith [mul_pos (mul_pos hx0 hx0) h1]

/-- The AM–GM step: `(z + β)(P + z H) ≥ (√β √P + z √H)²` for `z ≥ 0`. -/
theorem sq_sqrt_add_le {z β P H : ℝ} (hz : 0 ≤ z) (hβ : 0 ≤ β) (hP : 0 ≤ P) (hH : 0 ≤ H) :
    (√β * √P + z * √H) ^ 2 ≤ (z + β) * (P + z * H) := by
  have e1 : β = √β ^ 2 := (Real.sq_sqrt hβ).symm
  have e2 : P = √P ^ 2 := (Real.sq_sqrt hP).symm
  have e3 : H = √H ^ 2 := (Real.sq_sqrt hH).symm
  generalize √β = s at e1 ⊢
  generalize √P = t at e2 ⊢
  generalize √H = w at e3 ⊢
  subst e1 e2 e3
  nlinarith [mul_nonneg hz (sq_nonneg (t - s * w))]

theorem abs_mul_sub_le_of {k t₁ t₂ : ℝ} (h0 : 0 ≤ t₂) (h1 : t₂ ≤ t₁) :
    |k * (t₁ - t₂)| ≤ |k| * t₁ := by
  rw [abs_mul, abs_of_nonneg (sub_nonneg.2 h1)]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg k)

/-- **The integrand of the outer pair, abstractly**: the difference of the master combinations at
two denominators `0 < D₁ ≤ D₂` (`b ≥ g`). -/
theorem abs_masters_sub_le {c₀ a₀ a₁ a₂ c₁ c₂ c₃ b D₁ D₂ x g : ℝ} (hb : 0 < b) (hD₁ : 0 < D₁)
    (hD : D₁ ≤ D₂) (hc0 : 0 ≤ c₀) (hg : 0 < g) (hgb : g ≤ b) (hx : 0 < x)
    (ha0 : |a₀| ≤ x / 2) (ha1 : |a₁| ≤ 3 / 4 * x * g) (ha2 : |a₂| ≤ x * g ^ 2 / 4)
    (hc1 : |c₁| ≤ 9 / 8 * x) (hc2 : |c₂| ≤ 7 / 4 * x * g) (hc3 : |c₃| ≤ 3 / 4 * x * g ^ 2) :
    |(c₀ * (1 / D₁) + a₀ * (1 / D₁ ^ 2) + a₁ * (1 / (b * D₁ ^ 2)) + a₂ * (1 / (b ^ 2 * D₁ ^ 2)) +
        c₁ * (1 / (b * D₁)) + c₂ * (1 / (b ^ 2 * D₁)) + c₃ * (1 / (b ^ 3 * D₁))) -
      (c₀ * (1 / D₂) + a₀ * (1 / D₂ ^ 2) + a₁ * (1 / (b * D₂ ^ 2)) + a₂ * (1 / (b ^ 2 * D₂ ^ 2)) +
        c₁ * (1 / (b * D₂)) + c₂ * (1 / (b ^ 2 * D₂)) + c₃ * (1 / (b ^ 3 * D₂)))| ≤
      c₀ * (1 / D₁ - 1 / D₂) + 3 / 2 * x * (1 / D₁ ^ 2) + 4 * x * (1 / (b * D₁)) := by
  have hD₂ : 0 < D₂ := hD₁.trans_le hD
  have e : (c₀ * (1 / D₁) + a₀ * (1 / D₁ ^ 2) + a₁ * (1 / (b * D₁ ^ 2)) + a₂ * (1 / (b ^ 2 * D₁ ^ 2)) +
        c₁ * (1 / (b * D₁)) + c₂ * (1 / (b ^ 2 * D₁)) + c₃ * (1 / (b ^ 3 * D₁))) -
      (c₀ * (1 / D₂) + a₀ * (1 / D₂ ^ 2) + a₁ * (1 / (b * D₂ ^ 2)) + a₂ * (1 / (b ^ 2 * D₂ ^ 2)) +
        c₁ * (1 / (b * D₂)) + c₂ * (1 / (b ^ 2 * D₂)) + c₃ * (1 / (b ^ 3 * D₂))) =
      c₀ * (1 / D₁ - 1 / D₂) +
        (a₀ * (1 / D₁ ^ 2 - 1 / D₂ ^ 2) + a₁ * (1 / (b * D₁ ^ 2) - 1 / (b * D₂ ^ 2)) +
          a₂ * (1 / (b ^ 2 * D₁ ^ 2) - 1 / (b ^ 2 * D₂ ^ 2)) +
          c₁ * (1 / (b * D₁) - 1 / (b * D₂)) + c₂ * (1 / (b ^ 2 * D₁) - 1 / (b ^ 2 * D₂)) +
          c₃ * (1 / (b ^ 3 * D₁) - 1 / (b ^ 3 * D₂))) := by ring
  rw [e]
  have hsq : D₁ ^ 2 ≤ D₂ ^ 2 := pow_le_pow_left₀ hD₁.le hD 2
  have m0 : 1 / D₂ ≤ 1 / D₁ := one_div_le_one_div_of_le hD₁ hD
  have m1 : 1 / D₂ ^ 2 ≤ 1 / D₁ ^ 2 := one_div_le_one_div_of_le (by positivity) hsq
  have m2 : 1 / (b * D₂ ^ 2) ≤ 1 / (b * D₁ ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hsq hb.le)
  have m3 : 1 / (b ^ 2 * D₂ ^ 2) ≤ 1 / (b ^ 2 * D₁ ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hsq (by positivity))
  have m4 : 1 / (b * D₂) ≤ 1 / (b * D₁) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hD hb.le)
  have m5 : 1 / (b ^ 2 * D₂) ≤ 1 / (b ^ 2 * D₁) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hD (by positivity))
  have m6 : 1 / (b ^ 3 * D₂) ≤ 1 / (b ^ 3 * D₁) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hD (by positivity))
  have t1 := abs_mul_sub_le_of (k := a₀) (by positivity) m1
  have t2 := abs_mul_sub_le_of (k := a₁) (by positivity) m2
  have t3 := abs_mul_sub_le_of (k := a₂) (by positivity) m3
  have t4 := abs_mul_sub_le_of (k := c₁) (by positivity) m4
  have t5 := abs_mul_sub_le_of (k := c₂) (by positivity) m5
  have t6 := abs_mul_sub_le_of (k := c₃) (by positivity) m6
  have hsix := abs_add_six_le (a₀ * (1 / D₁ ^ 2 - 1 / D₂ ^ 2))
    (a₁ * (1 / (b * D₁ ^ 2) - 1 / (b * D₂ ^ 2))) (a₂ * (1 / (b ^ 2 * D₁ ^ 2) - 1 / (b ^ 2 * D₂ ^ 2)))
    (c₁ * (1 / (b * D₁) - 1 / (b * D₂))) (c₂ * (1 / (b ^ 2 * D₁) - 1 / (b ^ 2 * D₂)))
    (c₃ * (1 / (b ^ 3 * D₁) - 1 / (b ^ 3 * D₂)))
  -- the coefficients
  have s1 : |a₀| * (1 / D₁ ^ 2) ≤ x / 2 * (1 / D₁ ^ 2) :=
    mul_le_mul_of_nonneg_right ha0 (by positivity)
  have s2 : |a₁| * (1 / (b * D₁ ^ 2)) ≤ 3 / 4 * x * (1 / D₁ ^ 2) := by
    calc _ ≤ (3 / 4 * x * b) * (1 / (b * D₁ ^ 2)) :=
          mul_le_mul_of_nonneg_right (ha1.trans (mul_le_mul_of_nonneg_left hgb (by positivity)))
            (by positivity)
      _ = 3 / 4 * x * (1 / D₁ ^ 2) := by field_simp
  have s3 : |a₂| * (1 / (b ^ 2 * D₁ ^ 2)) ≤ x / 4 * (1 / D₁ ^ 2) := by
    have : g ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hg.le hgb 2
    calc _ ≤ (x * b ^ 2 / 4) * (1 / (b ^ 2 * D₁ ^ 2)) :=
          mul_le_mul_of_nonneg_right (ha2.trans (by
            have := mul_le_mul_of_nonneg_left this hx.le; linarith)) (by positivity)
      _ = x / 4 * (1 / D₁ ^ 2) := by field_simp
  have s4 : |c₁| * (1 / (b * D₁)) ≤ 9 / 8 * x * (1 / (b * D₁)) :=
    mul_le_mul_of_nonneg_right hc1 (by positivity)
  have s5 : |c₂| * (1 / (b ^ 2 * D₁)) ≤ 7 / 4 * x * (1 / (b * D₁)) := by
    calc _ ≤ (7 / 4 * x * b) * (1 / (b ^ 2 * D₁)) :=
          mul_le_mul_of_nonneg_right (hc2.trans (mul_le_mul_of_nonneg_left hgb (by positivity)))
            (by positivity)
      _ = 7 / 4 * x * (1 / (b * D₁)) := by field_simp
  have s6 : |c₃| * (1 / (b ^ 3 * D₁)) ≤ 3 / 4 * x * (1 / (b * D₁)) := by
    have : g ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hg.le hgb 2
    calc _ ≤ (3 / 4 * x * b ^ 2) * (1 / (b ^ 3 * D₁)) :=
          mul_le_mul_of_nonneg_right (hc3.trans (mul_le_mul_of_nonneg_left this (by positivity)))
            (by positivity)
      _ = 3 / 4 * x * (1 / (b * D₁)) := by field_simp
  have hA0 : 0 ≤ c₀ * (1 / D₁ - 1 / D₂) := mul_nonneg hc0 (by linarith)
  have hpos : 0 ≤ x * (1 / (b * D₁)) := by positivity
  calc _ ≤ |c₀ * (1 / D₁ - 1 / D₂)| + |a₀ * (1 / D₁ ^ 2 - 1 / D₂ ^ 2) +
        a₁ * (1 / (b * D₁ ^ 2) - 1 / (b * D₂ ^ 2)) +
        a₂ * (1 / (b ^ 2 * D₁ ^ 2) - 1 / (b ^ 2 * D₂ ^ 2)) +
        c₁ * (1 / (b * D₁) - 1 / (b * D₂)) + c₂ * (1 / (b ^ 2 * D₁) - 1 / (b ^ 2 * D₂)) +
        c₃ * (1 / (b ^ 3 * D₁) - 1 / (b ^ 3 * D₂))| := abs_add_le _ _
    _ ≤ _ := by
        rw [abs_of_nonneg hA0]
        have : 9 / 8 * x * (1 / (b * D₁)) + 7 / 4 * x * (1 / (b * D₁)) +
            3 / 4 * x * (1 / (b * D₁)) ≤ 4 * x * (1 / (b * D₁)) := by
          have e1 : 9 / 8 * x * (1 / (b * D₁)) + 7 / 4 * x * (1 / (b * D₁)) +
            3 / 4 * x * (1 / (b * D₁)) = 29 / 8 * (x * (1 / (b * D₁))) := by ring
          have e2 : 4 * x * (1 / (b * D₁)) = 4 * (x * (1 / (b * D₁))) := by ring
          rw [e1, e2]; linarith
        linarith

/-- **The integrand of the outer pair**, bounded by an integrable function of `z`. -/
theorem abs_cornerOut_integrand_le (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam)
    (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1) {z : ℝ} (hz : 0 < z) :
    |cornerAX Lam lam y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x) -
        cornerAX Lam Lam y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x)| ≤
      cornerC0 x * (1 / ((cornerMass Lam lam y3 y4 +
          betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 Lam x / x)) +
          z * (ladderInnerMass 1 Lam x / x)) -
        1 / ((cornerMass Lam Lam y3 y4 +
          betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 Lam x / x)) +
          z * (ladderInnerMass 1 Lam x / x))) +
      3 / 2 * x * (1 / (cornerP y3 y4 x + z * (ladderInnerMass 1 Lam x / x)) ^ 2) +
      4 * x * (1 / (√(betaG (cornerG y3 y4) (y3 * y4) x) * √(cornerP y3 y4 x) +
        z * √(ladderInnerMass 1 Lam x / x)) ^ 2) := by
  have hPle1 := cornerP_le_massAt (Lam := Lam) lam hx hY
  have hPle2 := cornerP_le_massAt (Lam := Lam) Lam hx hY
  have hP := cornerP_pos hx h3 h4 hY
  have hg := cornerG_pos h3 hY
  have hM12 : cornerMass Lam lam y3 y4 ≤ cornerMass Lam Lam y3 y4 := by
    unfold cornerMass
    have : lam ^ 2 ≤ Lam ^ 2 := by nlinarith
    nlinarith
  have hH : 0 < ladderInnerMass 1 Lam x / x := selfH_pos hx
  have hβ : 0 < betaG (cornerG y3 y4) (y3 * y4) x := betaG_pos hg
  have hgβ : cornerG y3 y4 ≤ betaG (cornerG y3 y4) (y3 * y4) x := le_betaG _ _ _
  have hb : 0 < z + betaG (cornerG y3 y4) (y3 * y4) x := by linarith
  have e1 : cornerMass Lam lam y3 y4 + (z + betaG (cornerG y3 y4) (y3 * y4) x) *
      (ladderInnerMass 1 Lam x / x) = (cornerMass Lam lam y3 y4 +
        betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 Lam x / x)) +
          z * (ladderInnerMass 1 Lam x / x) := by ring
  have e2 : cornerMass Lam Lam y3 y4 + (z + betaG (cornerG y3 y4) (y3 * y4) x) *
      (ladderInnerMass 1 Lam x / x) = (cornerMass Lam Lam y3 y4 +
        betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 Lam x / x)) +
          z * (ladderInnerMass 1 Lam x / x) := by ring
  have hD1 : cornerP y3 y4 x + z * (ladderInnerMass 1 Lam x / x) ≤
      cornerMass Lam lam y3 y4 + (z + betaG (cornerG y3 y4) (y3 * y4) x) *
        (ladderInnerMass 1 Lam x / x) := by rw [e1]; linarith
  have hD12 : cornerMass Lam lam y3 y4 + (z + betaG (cornerG y3 y4) (y3 * y4) x) *
        (ladderInnerMass 1 Lam x / x) ≤ cornerMass Lam Lam y3 y4 +
          (z + betaG (cornerG y3 y4) (y3 * y4) x) * (ladderInnerMass 1 Lam x / x) := by linarith
  have hPz : 0 < cornerP y3 y4 x + z * (ladderInnerMass 1 Lam x / x) := by positivity
  have hD1pos := hPz.trans_le hD1
  have hD2pos := hD1pos.trans_le hD12
  rw [cornerAX_eq hx (by linarith) hb hD1pos, cornerAX_eq hx (by linarith) hb hD2pos]
  unfold masterK2 masterK3 masterK4 masterK5 masterK6 masterK7
  have h0 := abs_masters_sub_le (c₀ := cornerC0 x) (a₀ := cornerA0 x y3 y4)
    (a₁ := cornerA1 x y3 y4) (a₂ := cornerA2 x y3 y4) (c₁ := cornerC1 x y3 y4)
    (c₂ := cornerC2 x y3 y4) (c₃ := cornerC3 x y3 y4) hb hD1pos hD12 (cornerC0_nonneg hx) hg
    (by linarith) hx.1 (abs_cornerA0_le hx h3 h4 hY) (abs_cornerA1_le hx h3 h4 hY)
    (abs_cornerA2_le hx h3 h4 hY) (abs_cornerC1_le hx h3 h4 hY) (abs_cornerC2_le hx h3 h4 hY)
    (abs_cornerC3_le hx h3 h4 hY)
  refine h0.trans ?_
  rw [e1, e2]
  rw [e1] at hD1 hD1pos
  have hx0 := hx.1
  have k1 : 1 / ((cornerMass Lam lam y3 y4 +
      betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 Lam x / x)) +
      z * (ladderInnerMass 1 Lam x / x)) ^ 2 ≤
      1 / (cornerP y3 y4 x + z * (ladderInnerMass 1 Lam x / x)) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hPz.le hD1 2)
  have hsq := sq_sqrt_add_le hz.le hβ.le hP.le hH.le
  have hs : 0 < √(betaG (cornerG y3 y4) (y3 * y4) x) * √(cornerP y3 y4 x) +
      z * √(ladderInnerMass 1 Lam x / x) := by
    have := Real.sqrt_pos.2 hβ
    have := Real.sqrt_pos.2 hP
    have := Real.sqrt_nonneg (ladderInnerMass 1 Lam x / x)
    positivity
  have k2 : 1 / ((z + betaG (cornerG y3 y4) (y3 * y4) x) * ((cornerMass Lam lam y3 y4 +
      betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 Lam x / x)) +
      z * (ladderInnerMass 1 Lam x / x))) ≤
      1 / (√(betaG (cornerG y3 y4) (y3 * y4) x) * √(cornerP y3 y4 x) +
        z * √(ladderInnerMass 1 Lam x / x)) ^ 2 := by
    exact one_div_le_one_div_of_le (by positivity)
      (hsq.trans (mul_le_mul_of_nonneg_left hD1 hb.le))
  have := mul_le_mul_of_nonneg_left k1 (by positivity : (0 : ℝ) ≤ 3 / 2 * x)
  have := mul_le_mul_of_nonneg_left k2 (by positivity : (0 : ℝ) ≤ 4 * x)
  linarith

/-- **The bound on the outer pair**: `x²/(Λ √P) + (3/2) x/(P H) + 4 x/(√β √P √H)`. -/
noncomputable def cornerOutBound (Lam y3 y4 x : ℝ) : ℝ :=
  x ^ 2 / (Lam * √(cornerP y3 y4 x)) +
    3 / 2 * x / (cornerP y3 y4 x * (ladderInnerMass 1 Lam x / x)) +
    4 * x / (√(betaG (cornerG y3 y4) (y3 * y4) x) * √(cornerP y3 y4 x) *
      √(ladderInnerMass 1 Lam x / x))

/-- **The outer pair**: for `0 < λ ≤ 1 ≤ Λ`, `(y₃, y₄)` in the open triangle and `0 < x < 1`,
`|O(Λ; λ, Λ)| ≤ x²/(Λ √P) + (3/2) x/(P H) + 4 x/(√β √P √H)`. -/
theorem abs_cornerOut_le (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam)
    (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1) :
    |cornerOut Lam lam Lam y3 y4 x| ≤ cornerOutBound Lam y3 y4 x := by
  have hPle1 := cornerP_le_massAt (Lam := Lam) lam hx hY
  have hPle2 := cornerP_le_massAt (Lam := Lam) Lam hx hY
  have hP := cornerP_pos hx h3 h4 hY
  have hg := cornerG_pos h3 hY
  have hH : 0 < ladderInnerMass 1 Lam x / x := selfH_pos hx
  have hβ : 0 < betaG (cornerG y3 y4) (y3 * y4) x := betaG_pos hg
  have hs : 0 < √(betaG (cornerG y3 y4) (y3 * y4) x) * √(cornerP y3 y4 x) :=
    mul_pos (Real.sqrt_pos.2 hβ) (Real.sqrt_pos.2 hP)
  have hsH : 0 < √(ladderInnerMass 1 Lam x / x) := Real.sqrt_pos.2 hH
  have I := (((hasIoiInt_inv_sub (hP.trans_le hPle1) (hP.trans_le hPle2) hH).const_mul
    (cornerC0 x)).add ((hasIoiInt_inv_sq hP hH).const_mul (3 / 2 * x))).add
    ((hasIoiInt_inv_sq hs hsH).const_mul (4 * x))
  unfold cornerOut
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le I.1 ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs]
    exact abs_cornerOut_integrand_le hlam hlam1 hLam hx h3 h4 hY hz
  rw [I.2]
  -- the logarithm
  set a := cornerMass Lam lam y3 y4 +
    betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 Lam x / x) with ha
  set a' := cornerMass Lam Lam y3 y4 +
    betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 Lam x / x) with ha'
  have hapos : 0 < a := hP.trans_le hPle1
  have hd : a' - a ≤ Lam ^ 2 := by
    rw [ha, ha']; unfold cornerMass
    have : 0 ≤ (1 - (y3 + y4)) * lam ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith
  have hd0 : 0 ≤ a' - a := by
    rw [ha, ha']; unfold cornerMass
    have : lam ^ 2 ≤ Lam ^ 2 := by nlinarith
    nlinarith
  have hLam0 : 0 < Lam := by linarith
  have hlog : log a' - log a ≤ 2 * (Lam / √(cornerP y3 y4 x)) := by
    have e : log a' - log a = log (1 + (a' - a) / a) := by
      rw [← log_div (by linarith) hapos.ne']
      congr 1; field_simp; ring
    rw [e]
    refine (log_one_add_le_two_sqrt (by positivity)).trans ?_
    gcongr
    calc √((a' - a) / a) ≤ √(Lam ^ 2 / cornerP y3 y4 x) :=
          Real.sqrt_le_sqrt ((div_le_div_of_nonneg_right hd hapos.le).trans
            (div_le_div_of_nonneg_left (sq_nonneg _) hP hPle1))
      _ = Lam / √(cornerP y3 y4 x) := by
          rw [Real.sqrt_div' _ hP.le, Real.sqrt_sq hLam0.le]
  have hc := cornerC0_div_hLam_le hLam hx
  have hlog0 : 0 ≤ log a' - log a := sub_nonneg.2 (log_le_log hapos (by linarith))
  have hc0 := cornerC0_nonneg hx
  have h1 : cornerC0 x * ((log a' - log a) / (ladderInnerMass 1 Lam x / x)) ≤
      x ^ 2 / (Lam * √(cornerP y3 y4 x)) := by
    have hsP := Real.sqrt_pos.2 hP
    calc cornerC0 x * ((log a' - log a) / (ladderInnerMass 1 Lam x / x))
        = cornerC0 x / (ladderInnerMass 1 Lam x / x) * (log a' - log a) := by ring
      _ ≤ x ^ 2 / (2 * Lam ^ 2) * (2 * (Lam / √(cornerP y3 y4 x))) :=
          mul_le_mul hc hlog hlog0 (by positivity)
      _ = x ^ 2 / (Lam * √(cornerP y3 y4 x)) := by field_simp
  unfold cornerOutBound
  have e2 : 3 / 2 * x * (1 / (cornerP y3 y4 x * (ladderInnerMass 1 Lam x / x))) =
      3 / 2 * x / (cornerP y3 y4 x * (ladderInnerMass 1 Lam x / x)) := by ring
  have e3 : 4 * x * (1 / (√(betaG (cornerG y3 y4) (y3 * y4) x) * √(cornerP y3 y4 x) *
      √(ladderInnerMass 1 Lam x / x))) = 4 * x / (√(betaG (cornerG y3 y4) (y3 * y4) x) *
        √(cornerP y3 y4 x) * √(ladderInnerMass 1 Lam x / x)) := by ring
  linarith

end Outer

end QED.TwoLoop.UnitSCCorner

end
