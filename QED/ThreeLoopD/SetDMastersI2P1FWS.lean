/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P1FW
public import QED.ThreeLoopD.SetDMastersI2P1FRect
public import QED.ThreeLoopD.SetDMastersI2P1USub
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Set (d), master `I₂`: the simplex step of the `ℱ`-part

With `α₁ = u`, `α₃ = v`, `α₂ = 1 - u - v`, `A = α₁ α₂`, `B = α₂ α₃`, `C = α₁ α₃`, the slice
length satisfies `len(s) + min(1/s, 1/A + 1/B) = min(1/s, 1/A) + min(1/s, 1/B)`, so at fixed
`q > 0` (with `s = q - C`)

  `∫_{triangle} 1[C < q] len(q - C) + ∫₀¹ h(q / k) / k dξ = ∫₀¹ g(q / k) / k dξ`,

`k = ξ (1 - ξ)`, with `g = QED.ThreeLoopD.i2P1Fgr`, `h = QED.ThreeLoopD.i2P1Fhr`. The first two
min-terms are integrated over `α₃` at fixed `α₁` (`QED.ThreeLoopD.i2P1FW_one`, using the symmetry
`α₁ ↔ α₃` for the second); the third in the coordinates `α₁ = σ ξ`, `α₃ = σ (1 - ξ)`
(`QED.ThreeLoopD.i2P1FW_three`).

## Main results

* `QED.ThreeLoopD.i2P1FWS_polar`: `∫_{triangle} f = ∫₀¹ dξ ∫₀¹ σ dσ f(σ ξ, σ (1 - ξ))`.
* `QED.ThreeLoopD.i2P1FWS_len`: the identity for the slice length.
* `QED.ThreeLoopD.i2P1FWS_main`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Function
open scoped ENNReal

namespace QED.ThreeLoopD

/-- Almost every `u` has `u (1 - u) ≠ q`. -/
theorem i2P1FWS_ae (q : ℝ) : ∀ᵐ u : ℝ, q ≠ u * (1 - u) := by
  refine ae_iff.2 (measure_mono_null (t := {(1 - Real.sqrt (1 - 4 * q)) / 2,
    (1 + Real.sqrt (1 - 4 * q)) / 2}) (fun u hu => ?_) ((toFinite _).measure_zero _))
  simp only [ne_eq, not_not, mem_ofPred_eq] at hu
  have h : (2 * u - 1) ^ 2 = 1 - 4 * q := by rw [hu]; ring
  have hs : Real.sqrt (1 - 4 * q) = |2 * u - 1| := by rw [← h, Real.sqrt_sq_eq_abs]
  rcases le_total 0 (2 * u - 1) with h0 | h0
  · right
    simp only [mem_singleton_iff, hs, abs_of_nonneg h0]
    ring
  · left
    simp only [hs, abs_of_nonpos h0]
    ring

/-- Lower integrals over the triangle are measurable in the outer variable. -/
theorem i2P1FWS_meas_tri {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (uncurry f)) :
    Measurable fun u => ∫⁻ v in Ioo (0 : ℝ) (1 - u), f u v := by
  have hT : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < 1 - p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop))
  have e : (fun u => ∫⁻ v in Ioo (0 : ℝ) (1 - u), f u v) =
      fun u => ∫⁻ v, {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < 1 - p.1}.indicator (uncurry f) (u, v) := by
    funext u
    rw [← lintegral_indicator measurableSet_Ioo]
    congr 1
  rw [e]
  exact (hf.indicator hT).lintegral_prod_right'

/-- **Polar coordinates on the triangle**: `α₁ = σ ξ`, `α₃ = σ (1 - ξ)`. -/
theorem i2P1FWS_polar {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (uncurry f)) :
    ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), f u v =
      ∫⁻ ξ in Ioo (0 : ℝ) 1, ∫⁻ σ in Ioo (0 : ℝ) 1,
        ENNReal.ofReal σ * f (σ * ξ) (σ * (1 - ξ)) := by
  have m1 : Measurable (uncurry fun σ u : ℝ => f u (σ - u)) :=
    hf.comp (measurable_snd.prodMk (measurable_fst.sub measurable_snd))
  have m2 : Measurable (uncurry fun σ ξ : ℝ => ENNReal.ofReal σ * f (σ * ξ) (σ - σ * ξ)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hf.comp ((measurable_fst.mul measurable_snd).prodMk
        (measurable_fst.sub (measurable_fst.mul measurable_snd))))
  calc ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), f u v
      = ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ σ in Ioo u 1, f u (σ - u) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
        have := i2P1FRect_add u (1 - u) (fun σ => f u (σ - u))
        simp only [add_sub_cancel_left, add_sub_cancel] at this
        exact this
    _ = ∫⁻ σ in Ioo (0 : ℝ) 1, ∫⁻ u in Ioo (0 : ℝ) σ, f u (σ - u) :=
        (i2P1US_lower_swap (g := fun σ u => f u (σ - u)) m1).symm
    _ = ∫⁻ σ in Ioo (0 : ℝ) 1, ∫⁻ ξ in Ioo (0 : ℝ) 1,
          ENNReal.ofReal σ * f (σ * ξ) (σ - σ * ξ) :=
        setLIntegral_congr_fun measurableSet_Ioo fun σ hσ =>
          i2P1US_scale hσ.1 (fun u => f u (σ - u))
    _ = ∫⁻ ξ in Ioo (0 : ℝ) 1, ∫⁻ σ in Ioo (0 : ℝ) 1,
          ENNReal.ofReal σ * f (σ * ξ) (σ - σ * ξ) := i2P1US_swap m2
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun ξ _ => ?_
        refine setLIntegral_congr_fun measurableSet_Ioo fun σ _ => ?_
        rw [show σ - σ * ξ = σ * (1 - ξ) by ring]

/-- **The slice length as three min-terms**:
`len(s) + min(1/s, 1/A + 1/B) = min(1/s, 1/A) + min(1/s, 1/B)`. -/
theorem i2P1FWS_len {A B s : ℝ} (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) :
    ENNReal.ofReal (i2P1FLen A B s) + ENNReal.ofReal (min (1 / s) (1 / A + 1 / B)) =
      ENNReal.ofReal (min (1 / s) (1 / A)) + ENNReal.ofReal (min (1 / s) (1 / B)) := by
  have ha : 0 < 1 / A := one_div_pos.2 hA
  have hb : 0 < 1 / B := one_div_pos.2 hB
  have hS : 0 < 1 / s := one_div_pos.2 hs
  simp only [i2P1FLen, ← one_div]
  set a := 1 / A
  set b := 1 / B
  set S := 1 / s
  rw [← ENNReal.ofReal_add (le_min hS.le ha.le) (le_min hS.le hb.le)]
  rcases le_or_gt 0 (min a S - max 0 (S - b)) with h | h
  · rw [← ENNReal.ofReal_add h (le_min hS.le (by positivity))]
    congr 1
    simp only [min_def, max_def] at h ⊢
    split_ifs at h ⊢ <;> linarith
  · rw [ENNReal.ofReal_of_nonpos h.le, zero_add]
    congr 1
    simp only [min_def, max_def] at h ⊢
    split_ifs at h ⊢ <;> linarith

theorem measurable_i2P1Fgr : Measurable i2P1Fgr := by
  unfold i2P1Fgr
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) (by fun_prop)
    (by fun_prop)

theorem measurable_i2P1Fhr : Measurable i2P1Fhr := by
  unfold i2P1Fhr
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) (by fun_prop)
    (by fun_prop)

theorem i2P1Fgr_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ i2P1Fgr ρ := by
  unfold i2P1Fgr
  split_ifs with h
  · exact neg_nonneg.2 (log_nonpos (by linarith) (by linarith))
  · have h1 : 1 ≤ ρ := not_lt.1 h
    have : 0 ≤ 1 / ρ := by positivity
    have : 1 / ρ ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
    exact neg_nonneg.2 (log_nonpos (by linarith) (by linarith))

theorem i2P1FWS_meas_ite {f : ℝ → ℝ → ℝ} (hf : Measurable (uncurry f)) (q : ℝ) :
    Measurable (uncurry fun u v : ℝ => if u * v < q then ENNReal.ofReal (f u v) else 0) :=
  Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    (ENNReal.measurable_ofReal.comp hf) measurable_const

/-- **Term one**: `∫_{triangle} 1[u v < q] min(1 / (q - u v), 1 / A) = ∫₀¹ g(q / k) / ξ`. -/
theorem i2P1FWS_one {q : ℝ} (hq : 0 < q) :
    ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), (if u * v < q then
        ENNReal.ofReal (min (1 / (q - u * v)) (1 / (u * (1 - u - v)))) else 0) =
      ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Fgr (q / (ξ * (1 - ξ))) / ξ) :=
  setLIntegral_congr_fun_ae measurableSet_Ioo
    ((i2P1FWS_ae q).mono fun _ hne hu => i2P1FW_one hq hu hne)

/-- **Term two**, by the symmetry `α₁ ↔ α₃`. -/
theorem i2P1FWS_two {q : ℝ} (hq : 0 < q) :
    ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), (if u * v < q then
        ENNReal.ofReal (min (1 / (q - u * v)) (1 / (v * (1 - u - v)))) else 0) =
      ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Fgr (q / (ξ * (1 - ξ))) / ξ) := by
  rw [i2P1US_tri_swap (i2P1FWS_meas_ite (by fun_prop) q), ← i2P1FWS_one hq]
  refine setLIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
  refine setLIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  simp only [mul_comm u v, show 1 - u - v = 1 - v - u by ring]

/-- **Term three**: `∫_{triangle} 1[u v < q] min(1 / (q - u v), 1 / A + 1 / B)
= ∫₀¹ h(q / k) / k`. -/
theorem i2P1FWS_three {q : ℝ} (hq : 0 < q) :
    ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), (if u * v < q then
        ENNReal.ofReal (min (1 / (q - u * v)) (1 / (u * (1 - u - v)) + 1 / (v * (1 - u - v))))
        else 0) =
      ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Fhr (q / (ξ * (1 - ξ))) / (ξ * (1 - ξ))) := by
  rw [i2P1FWS_polar (i2P1FWS_meas_ite (by fun_prop) q)]
  refine setLIntegral_congr_fun_ae measurableSet_Ioo ((i2P1FWS_ae q).mono fun ξ hne hξ => ?_)
  have hk : 0 < ξ * (1 - ξ) := mul_pos hξ.1 (by linarith [hξ.2])
  rw [← i2P1FW_three hq hk hne]
  refine setLIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
  have hσ0 : σ ≠ 0 := hσ.1.ne'
  have hσ1 : 1 - σ ≠ 0 := by linarith [hσ.2]
  have hξ0 : ξ ≠ 0 := hξ.1.ne'
  have hξ1 : 1 - ξ ≠ 0 := by linarith [hξ.2]
  rw [show σ * ξ * (σ * (1 - ξ)) = σ ^ 2 * (ξ * (1 - ξ)) by ring,
    show 1 - σ * ξ - σ * (1 - ξ) = 1 - σ by ring,
    show 1 / (σ * ξ * (1 - σ)) + 1 / (σ * (1 - ξ) * (1 - σ)) =
      1 / (σ * (ξ * (1 - ξ)) * (1 - σ)) by field_simp; ring]
  split_ifs
  · rw [ENNReal.ofReal_mul hσ.1.le]
  · simp

/-- **Symmetrization**: `2 ∫₀¹ g(q / k) / ξ = ∫₀¹ g(q / k) / k`. -/
theorem i2P1FWS_sym {q : ℝ} (hq : 0 < q) :
    (∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Fgr (q / (ξ * (1 - ξ))) / ξ)) +
        ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Fgr (q / (ξ * (1 - ξ))) / ξ) =
      ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Fgr (q / (ξ * (1 - ξ))) / (ξ * (1 - ξ))) := by
  have hm : Measurable fun ξ : ℝ => ENNReal.ofReal (i2P1Fgr (q / (ξ * (1 - ξ))) / ξ) :=
    ENNReal.measurable_ofReal.comp ((measurable_i2P1Fgr.comp (by fun_prop)).div measurable_id)
  have hr : ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Fgr (q / (ξ * (1 - ξ))) / ξ) =
      ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Fgr (q / (ξ * (1 - ξ))) / (1 - ξ)) := by
    rw [← i2P1US_reflect 1]
    refine setLIntegral_congr_fun measurableSet_Ioo fun ξ _ => ?_
    rw [show (1 - ξ) * (1 - (1 - ξ)) = ξ * (1 - ξ) by ring]
  nth_rewrite 2 [hr]
  rw [← lintegral_add_left hm]
  refine setLIntegral_congr_fun measurableSet_Ioo fun ξ hξ => ?_
  have h0 : 0 < ξ := hξ.1
  have h1 : 0 < 1 - ξ := by linarith [hξ.2]
  have hg := i2P1Fgr_nonneg (ρ := q / (ξ * (1 - ξ))) (by positivity)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- **The simplex step**: at fixed `q > 0`,
`∫_{triangle} 1[C < q] len(q - C) + ∫₀¹ h(q / k) / k = ∫₀¹ g(q / k) / k`. -/
theorem i2P1FWS_main {q : ℝ} (hq : 0 < q) :
    (∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), (if u * v < q then
        ENNReal.ofReal (i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) (q - u * v)) else 0)) +
      ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Fhr (q / (ξ * (1 - ξ))) / (ξ * (1 - ξ))) =
      ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Fgr (q / (ξ * (1 - ξ))) / (ξ * (1 - ξ))) := by
  have mL := i2P1FWS_meas_ite (q := q)
    (f := fun u v => i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) (q - u * v))
    (by unfold i2P1FLen; fun_prop)
  have m3 := i2P1FWS_meas_ite (q := q)
    (f := fun u v => min (1 / (q - u * v)) (1 / (u * (1 - u - v)) + 1 / (v * (1 - u - v))))
    (by fun_prop)
  have m1 := i2P1FWS_meas_ite (q := q)
    (f := fun u v => min (1 / (q - u * v)) (1 / (u * (1 - u - v)))) (by fun_prop)
  have m2 := i2P1FWS_meas_ite (q := q)
    (f := fun u v => min (1 / (q - u * v)) (1 / (v * (1 - u - v)))) (by fun_prop)
  rw [← i2P1FWS_sym hq, ← i2P1FWS_three hq]
  nth_rewrite 1 [← i2P1FWS_one hq]
  rw [← i2P1FWS_two hq]
  rw [← lintegral_add_left (i2P1FWS_meas_tri mL), ← lintegral_add_left (i2P1FWS_meas_tri m1)]
  refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  rw [← lintegral_add_left (show Measurable fun v : ℝ => if u * v < q then
      ENNReal.ofReal (i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) (q - u * v)) else 0 from
        mL.comp measurable_prodMk_left),
    ← lintegral_add_left (show Measurable fun v : ℝ => if u * v < q then
      ENNReal.ofReal (min (1 / (q - u * v)) (1 / (u * (1 - u - v)))) else 0 from
        m1.comp measurable_prodMk_left)]
  refine setLIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  split_ifs with h
  · have hw : 0 < 1 - u - v := by linarith [hv.2]
    exact i2P1FWS_len (mul_pos hu.1 hw) (mul_pos hv.1 hw) (by linarith)
  · simp

end QED.ThreeLoopD
