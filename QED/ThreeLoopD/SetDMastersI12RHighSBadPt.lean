/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSBadReg

/-!
# Set (d), master `I₁₂`: the integrand of the bad part on `Reg`, exactly in `ε`

On `Reg` (`x ∈ (0, 1)`, `0 < s < x⁻¹`, chart of the sector `t < v`, `t = xs`) the integrand
`W_ε - Good_ε` of `QED.ThreeLoopD.i12HSBadF_eq_reg` is explicit
(`QED.ThreeLoopD.i12HSWe_sub_good`):

  `W_ε - Good_ε = SecWt(x, s) [((1 - t)^{-ε} - 1)(G₁ - 1_{s ≥ 1} h₀^{2ε-1} F)`
    `+ 1_{s ≥ 1} (h(x)^{2ε-1} - h₀^{2ε-1}) F]`,

with `G₁ = h(x)^{2ε-1} (u(1 - u))^ε Φ₀(us, (1 - u) h(x))` (`G_A` without its factor
`(1 - t)^{-ε}`, `QED.ThreeLoopD.i12HSG1`) and `F = a w(u) (sk)^{-3ε}`
(`QED.ThreeLoopD.i12HSFt`). So the bad part lives on `t = 1` up to the explicit term
`(h^{2ε-1} - h₀^{2ε-1}) F` of the reflected sector: for `‖ε‖ < 1/200`

  `Bad(ε) = R₁(ε) + ∫_{Reg} BadW_ε - ∫_{(0,1) × (0,∞) × (0,1) \ Reg} Good_ε`

(`QED.ThreeLoopD.i12HSBadF_eq_badW`, `BadW = QED.ThreeLoopD.i12HSBadW`).

## Proof

On the cube (`s < 1`) the face terms of `R_A` are those of the good part
(`QED.ThreeLoopD.i12HS_goodH_eq`, from `QED.ThreeLoopD.i12HS_D_eq` and the homogeneity of `Φ₀`).
On `i12HSDom` the face `ρ = 0` of `R_B` is reflected onto that of `R_A`
(`QED.ThreeLoopD.i12GA_zero_reflect`), and its face `θ = 0` becomes
`-SecWt(x, s) h₀^{2ε-1} (1 - t)^{-ε} F` (`QED.ThreeLoopD.i12HS_Ft_eq`,
`QED.ThreeLoopD.i12HS_secWt_pull`).

## Main results

* `QED.ThreeLoopD.i12HSWe_sub_good`, `QED.ThreeLoopD.i12HSBadF_eq_badW`.
-/

@[expose] public section

open Complex Set MeasureTheory Metric

namespace QED.ThreeLoopD

/-- `G_A` without its factor `(1 - ρθ)^{-ε}`:
`h(x)^{2ε-1} (u(1 - u))^ε Φ₀(us, (1 - u) h(x))`. -/
noncomputable def i12HSG1 (ε : ℂ) (x s u : ℝ) : ℂ :=
  ((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
    i12Phi0 ε (u * s) ((1 - u) * i12H x)

/-- The subtraction of the good part for `s ≥ 1`: `a w(u) (sk)^{-3ε}`. -/
noncomputable def i12HSFt (ε : ℂ) (s u : ℝ) : ℂ :=
  (2 - 3 * ε) * i12HSw ε u * ((s * i12HSk u : ℝ) : ℂ) ^ (-3 * ε)

/-- `w(u) = (u(1 - u))^ε (1 - u)^{-3ε}`. -/
theorem i12HS_w_eq (ε : ℂ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    i12HSw ε u = ((u * (1 - u) : ℝ) : ℂ) ^ ε * ((1 - u : ℝ) : ℂ) ^ (-3 * ε) := by
  have h1 : 0 < 1 - u := by linarith
  simp only [i12HSw]
  rw [i12_cpow_lin hu0, i12_cpow_lin h1, i12_cpow_lin (mul_pos hu0 h1), i12_cpow_lin h1,
    Real.log_mul hu0.ne' h1.ne', ← exp_add, ← exp_add]
  congr 1; push_cast; ring

/-- One scale of the good part in the variables of `G_A`. -/
theorem i12HS_goodH_eq (ε : ℂ) {s u H : ℝ} (hs : 0 < s) (hu0 : 0 < u) (hu1 : u < 1)
    (hH : 0 < H) :
    i12HSw ε u * ((H : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / H)) =
      (H : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε * i12Phi0 ε (u * s) ((1 - u) * H) -
        if s < 1 then (H : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
          ((2 - 3 * ε) * (((1 - u) * H : ℝ) : ℂ) ^ (-3 * ε))
        else (H : ℂ) ^ (2 * ε - 1) * i12HSFt ε s u := by
  have h1 : 0 < 1 - u := by linarith
  have hk : 0 < i12HSk u := div_pos hu0 h1
  rw [i12HS_D_eq ε hs hk hH]
  have hΦ := i12Phi0_mul_mul ε h1 (mul_pos hs hk) hH
  rw [show (1 - u) * (s * i12HSk u) = u * s by unfold i12HSk; field_simp] at hΦ
  have hY : (((1 - u) * H : ℝ) : ℂ) ^ (-3 * ε) =
      ((1 - u : ℝ) : ℂ) ^ (-3 * ε) * (H : ℂ) ^ (-3 * ε) := by
    rw [ofReal_mul, mul_cpow_ofReal_nonneg h1.le hH.le]
  simp only [i12HSG, i12HSFt, hΦ, i12HS_w_eq ε hu0 hu1, hY]
  split_ifs <;> ring

/-- `a w(u) (sk)^{-3ε} = a (s⁻¹)^{3ε} (u(1 - u))^ε u^{-3ε}`. -/
theorem i12HS_Ft_eq (ε : ℂ) {s u : ℝ} (hs : 0 < s) (hu0 : 0 < u) (hu1 : u < 1) :
    i12HSFt ε s u = ((s⁻¹ : ℝ) : ℂ) ^ (3 * ε) *
      (((u * (1 - u) : ℝ) : ℂ) ^ ε * ((2 - 3 * ε) * (u : ℂ) ^ (-3 * ε))) := by
  have h1 : 0 < 1 - u := by linarith
  have hk : 0 < s * i12HSk u := mul_pos hs (div_pos hu0 h1)
  simp only [i12HSFt, i12HSw]
  rw [i12_cpow_lin hu0, i12_cpow_lin h1, i12_cpow_lin hk, i12_cpow_lin (inv_pos.2 hs),
    i12_cpow_lin (mul_pos hu0 h1), i12_cpow_lin hu0, i12HSk,
    Real.log_mul hs.ne' (div_pos hu0 h1).ne', Real.log_div hu0.ne' h1.ne',
    Real.log_mul hu0.ne' h1.ne', Real.log_inv]
  have e : ∀ A B C D E F : ℂ, (2 - 3 * ε) * (exp A * exp B) * exp C =
      exp D * (exp E * ((2 - 3 * ε) * exp F)) ↔ (2 - 3 * ε) * exp (A + B + C) =
      (2 - 3 * ε) * exp (D + E + F) := fun A B C D E F => by
    simp only [exp_add]; constructor <;> intro h <;> linear_combination h
  rw [e]
  congr 2; push_cast; ring


/-- **The integrand of the bad part on `Reg`, pointwise and exactly in `ε`**: with
`t = xs`, `W_ε - Good_ε = SecWt(x, s) [((1 - t)^{-ε} - 1)(G₁ - 1_{s ≥ 1} h₀^{2ε-1} F)
+ 1_{s ≥ 1} (h^{2ε-1} - h₀^{2ε-1}) F]`, `G₁ = QED.ThreeLoopD.i12HSG1`,
`F = QED.ThreeLoopD.i12HSFt`. -/
theorem i12HSWe_sub_good (ε : ℂ) {x s u : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hs0 : 0 < s)
    (hu0 : 0 < u) (hu1 : u < 1) :
    i12HSWe ε x s u - i12HSGood ε x s u = i12SecWt ε x s *
      ((((1 - x * s : ℝ) : ℂ) ^ (-ε) - 1) * (i12HSG1 ε x s u -
          if s < 1 then 0 else ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * i12HSFt ε s u) +
        if s < 1 then 0 else
          (((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1)) *
            i12HSFt ε s u) := by
  have hh : 0 < i12H x := i12H_pos (by linarith)
  have hh0 : 0 < i12H 0 := i12H_pos (by norm_num)
  have hG : i12HSGood ε x s u = i12SecWt ε x s *
      (i12HSw ε u * (((i12H x : ℝ) : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / i12H x)) -
        i12HSw ε u * (((i12H 0 : ℝ) : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / i12H 0))) := by
    simp only [i12HSGood, i12SecWt]; ring
  rw [hG, i12HS_goodH_eq ε hs0 hu0 hu1 hh, i12HS_goodH_eq ε hs0 hu0 hu1 hh0]
  have e0 : i12GA ε 0 s u = i12HSG1 ε 0 s u := by
    simp only [i12GA, i12HSG1, zero_mul, sub_zero, ofReal_one, one_cpow, mul_one]
  by_cases hs : s < 1
  · simp only [i12HSWe, hs, ↓reduceIte, i12RA3Ig, e0]
    simp only [i12GA, i12GA0, i12HSG1]
    ring
  · simp only [i12HSWe, hs, ↓reduceIte]
    have hsi : 0 < s⁻¹ := inv_pos.2 hs0
    set P := ((s⁻¹ : ℝ) : ℂ) ^ (3 * ε) with hP
    have hP0 : P ≠ 0 := by rw [hP, i12_cpow_lin hsi]; exact exp_ne_zero _
    have hZ := i12GA_zero_reflect ε hsi hu0 hu1
    rw [inv_inv, e0] at hZ
    have hB : i12GB ε 0 s⁻¹ u = P⁻¹ * i12HSG1 ε 0 s u := by
      rw [hZ, ← hP]; field_simp
    have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.2 hs0.ne'
    rw [hB, i12HS_secWt_pull ε hs0 hx0, ← hP, i12HS_Ft_eq ε hs0 hu0 hu1, ← hP]
    simp only [i12GA, i12GB0, i12HSG1, sub_zero, ofReal_one, one_cpow, mul_one]
    field_simp
    ring

/-- The integrand of the bad part on `Reg` (right side of `QED.ThreeLoopD.i12HSWe_sub_good`). -/
noncomputable def i12HSBadW (ε : ℂ) (x s u : ℝ) : ℂ :=
  i12SecWt ε x s * ((((1 - x * s : ℝ) : ℂ) ^ (-ε) - 1) * (i12HSG1 ε x s u -
      if s < 1 then 0 else ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * i12HSFt ε s u) +
    if s < 1 then 0 else
      (((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1)) * i12HSFt ε s u)

/-- `QED.ThreeLoopD.i12HSWe_sub_good` on all of `Reg`. -/
theorem i12HSWe_sub_good_eqOn (ε : ℂ) :
    EqOn (fun z : ℝ × ℝ × ℝ => i12HSWe ε z.1 z.2.1 z.2.2 - i12HSGood ε z.1 z.2.1 z.2.2)
      (fun z => i12HSBadW ε z.1 z.2.1 z.2.2) i12HSReg := by
  rintro ⟨x, s, u⟩ (⟨hx, hs, hu⟩ | ⟨hs, hx, hu⟩)
  · exact i12HSWe_sub_good ε hx.1 hx.2 hs.1 hu.1 hu.2
  · have hs1 : (1 : ℝ) < s := hs
    exact i12HSWe_sub_good ε hx.1 (hx.2.trans (inv_lt_one_of_one_lt₀ hs1))
      (zero_lt_one.trans hs1) hu.1 hu.2

/-- **The bad part as explicit integrals**, exactly in `ε` (`‖ε‖ < 1/200`):
`Bad(ε) = R₁(ε) + ∫_{Reg} BadW_ε - ∫_{(0,1) × (0,∞) × (0,1) \ Reg} Good_ε`. -/
theorem i12HSBadF_eq_badW {ε : ℂ} (hε : ‖ε‖ < 1 / 200) :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSBadW ε z.1 z.2.1 z.2.2) i12HSReg ∧
      i12HSBadF ε = i12R1 ε + ((∫ z in i12HSReg, i12HSBadW ε z.1 z.2.1 z.2.2) -
          ∫ z in (Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1)) \ i12HSReg,
            i12HSGood ε z.1 z.2.1 z.2.2) := by
  obtain ⟨hI, -, hE⟩ := i12HSBadF_eq_reg hε
  have hReg : MeasurableSet i12HSReg :=
    (measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)).union
      measurableSet_i12HSDom
  refine ⟨hI.congr_fun (i12HSWe_sub_good_eqOn ε) hReg, ?_⟩
  rw [hE, setIntegral_congr_fun hReg (i12HSWe_sub_good_eqOn ε)]

end QED.ThreeLoopD
