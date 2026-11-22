/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KTaylor

/-!
# Set (d), master `I₁₅`: the splitting of every Taylor coefficient of `K`

Write `c = x (1 - x)`, `v = 1 - u`, `P = c v² + u`, `b₁ = log (c u / P²)`, `b₂ = log (c / u)`
(so `Fₖ` is `QED.ThreeLoopD.i15F k`). Since `P / (c u) = 1 / c + v² / u`,

  `Fₖ = A₁,ₖ + A₂₃,ₖ`,  `A₁,ₖ = (b₁ᵏ - b₂ᵏ) / (k! c)`,  `A₂₃,ₖ = (v² b₁ᵏ - (-b₂)ᵏ) / (k! u)`,

the splitting used for `k = 2` in `QED.ThreeLoopD.SetDMastersI15KValTwoA`. On the open square
`u ≤ P` and `c ≤ P`, that is `b₁ ≤ b₂` and `b₁ + b₂ ≤ 0`. Hence `A₁,₃ ≤ 0` (the factor
`b₁³ - b₂³ = (b₁ - b₂)(b₁² + b₁ b₂ + b₂²)`) and `A₁,₄ ≥ 0`
(`b₁⁴ - b₂⁴ = (b₁ - b₂)(b₁ + b₂)(b₁² + b₂²)`), so the `A₁` parts of `F₃` and `F₄` are
integrable as soon as their iterated integrals are finite (Tonelli), and then so are the `A₂₃`
parts, `Fₖ` being integrable (`QED.ThreeLoopD.integrable_i15F_real`).

Numerically (`setDI15d/ps1.py`), `∫∫ A₁,₃ = 14 π² + 56 ζ(3) - 16 π² log 2 - 100` and
`∫∫ A₂₃,₃ = 5 ζ(3) - 5 π²/8 - 65/16`; all of `π² log 2` sits in `A₁,₃`.

## Main results

* `QED.ThreeLoopD.i15F_eq_add`: `Fₖ = A₁,ₖ + A₂₃,ₖ`.
* `QED.ThreeLoopD.i15B1_le_i15B2`, `QED.ThreeLoopD.i15B1_add_i15B2_nonpos`.
* `QED.ThreeLoopD.i15A1k_three_nonpos`, `QED.ThreeLoopD.i15A1k_four_nonneg`.
* `QED.ThreeLoopD.integral_i15F_eq_add`: `∫∫ Fₖ = ∫∫ A₁,ₖ + ∫∫ A₂₃,ₖ` for `k < 5`, given the
  integrability of `A₁,ₖ`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.ThreeLoopD

/-- `A₁,ₖ = (b₁ᵏ - b₂ᵏ) / (k! c)`. -/
noncomputable def i15A1k (k : ℕ) (z : ℝ × ℝ) : ℝ :=
  (i15B1 z.1 z.2 ^ k - i15B2 z.1 z.2 ^ k) / (k.factorial * (z.1 * (1 - z.1)))

/-- `A₂₃,ₖ = (v² b₁ᵏ - (-b₂)ᵏ) / (k! u)`. -/
noncomputable def i15A23k (k : ℕ) (z : ℝ × ℝ) : ℝ :=
  ((1 - z.2) ^ 2 * i15B1 z.1 z.2 ^ k - (-i15B2 z.1 z.2) ^ k) / (k.factorial * z.2)

theorem i15F_eq_add (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i15F k z = i15A1k k z + i15A23k k z := by
  obtain ⟨⟨hx0, hx1⟩, hu0, hu1⟩ := hz
  have hc : z.1 * (1 - z.1) ≠ 0 := (mul_pos hx0 (by linarith)).ne'
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  unfold i15F i15A1k i15A23k
  simp only [i15P, i9Poly]
  field_simp
  ring

theorem i15_u_le_P {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : u ≤ i15P x u := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  simp only [i15P, i9Poly, mul_one]
  nlinarith [sq_nonneg (1 - u)]

theorem i15_c_le_P {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    x * (1 - x) ≤ i15P x u := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hu0, hu1⟩ := hu
  have hc4 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hc : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  simp only [i15P, i9Poly, mul_one]
  nlinarith [mul_le_mul_of_nonneg_left hc4 (mul_pos hu0 (by linarith : (0 : ℝ) < 2 - u)).le]

theorem i15B1_le_i15B2 {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15B1 x u ≤ i15B2 x u := by
  have hP := i15_P_pos hx hu
  have hl : Real.log u ≤ Real.log (i15P x u) := Real.log_le_log hu.1 (i15_u_le_P hx)
  unfold i15B1 i15B2
  linarith

theorem i15B1_add_i15B2_nonpos {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15B1 x u + i15B2 x u ≤ 0 := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have hl : Real.log (x * (1 - x)) ≤ Real.log (i15P x u) :=
    Real.log_le_log hc (i15_c_le_P hx hu)
  unfold i15B1 i15B2
  linarith

theorem i15A1k_three_nonpos {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i15A1k 3 z ≤ 0 := by
  have hc : 0 < z.1 * (1 - z.1) := mul_pos hz.1.1 (by linarith [hz.1.2])
  have h1 := i15B1_le_i15B2 hz.1 hz.2
  unfold i15A1k
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have e : i15B1 z.1 z.2 ^ 3 - i15B2 z.1 z.2 ^ 3 = (i15B1 z.1 z.2 - i15B2 z.1 z.2) *
      ((i15B1 z.1 z.2 + i15B2 z.1 z.2 / 2) ^ 2 + 3 / 4 * i15B2 z.1 z.2 ^ 2) := by ring
  rw [e]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem i15A1k_four_nonneg {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    0 ≤ i15A1k 4 z := by
  have hc : 0 < z.1 * (1 - z.1) := mul_pos hz.1.1 (by linarith [hz.1.2])
  have h1 := i15B1_le_i15B2 hz.1 hz.2
  have h2 := i15B1_add_i15B2_nonpos hz.1 hz.2
  unfold i15A1k
  apply div_nonneg _ (by positivity)
  have e : i15B1 z.1 z.2 ^ 4 - i15B2 z.1 z.2 ^ 4 = (i15B1 z.1 z.2 - i15B2 z.1 z.2) *
      (i15B1 z.1 z.2 + i15B2 z.1 z.2) * (i15B1 z.1 z.2 ^ 2 + i15B2 z.1 z.2 ^ 2) := by ring
  rw [e]
  exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) h2) (by positivity)

/-- **The split integral.** Given the integrability of `A₁,ₖ`, `∫∫ Fₖ = ∫∫ A₁,ₖ + ∫∫ A₂₃,ₖ`
(and `A₂₃,ₖ = Fₖ - A₁,ₖ` is integrable). -/
theorem integral_i15F_eq_add {k : ℕ} (hk : k < 5)
    (h1 : IntegrableOn (i15A1k k) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    IntegrableOn (i15A23k k) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ∧
      ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F k z =
        (∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15A1k k z) +
          ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15A23k k z := by
  have hF := integrable_i15F_real hk
  have h23 : IntegrableOn (i15A23k k) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    refine (hF.sub h1).congr ?_
    filter_upwards [ae_restrict_mem i15_S_meas] with z hz
    simp only [Pi.sub_apply, i15F_eq_add k hz]
    ring
  refine ⟨h23, ?_⟩
  rw [← integral_add h1 h23]
  refine setIntegral_congr_fun i15_S_meas fun z hz => i15F_eq_add k hz

end QED.ThreeLoopD
