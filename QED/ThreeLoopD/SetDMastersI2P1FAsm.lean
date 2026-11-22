/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P1FWS
public import QED.ThreeLoopD.SetDMastersI2P1FSub
public import QED.ThreeLoopD.SetDMastersI2P1UTot

/-!
# Set (d), master `I₂`: assembling the `ℱ`-part as lower integrals

With `G(y, q) = log (1 + y² / (q + y)) / (q + y)²` (the integrand after the photon lines, with
`q = s + α₁ α₃` and `y = y₄`), we prove:

* (`y₄` integral) `∫_{y > 0} G(y, q) dy = M_t(q) / q` (`y = q t`);
* the lower integral of `(1 - w) log (ℱ / 𝒰) / 𝒰²` over the domain of `I₂` is
  `∫_{q > 0} M_t(q) / q · W(q)`, `W(q) = ∫_{triangle} 1[α₁ α₃ < q] len(q - α₁ α₃)`;
* (`q = k ρ`) `∫_{q > 0} M_t(q) / q ∫₀¹ F(q / k) / k dξ = ∫_{ρ > 0} F(ρ) ∫₀¹ M_t(ρ k) / (ρ k) dξ`;
* with the simplex step `QED.ThreeLoopD.i2P1FWS_main` and the substitutions
  `QED.ThreeLoopD.i2P1FSub_main`: `V + R(h) = R(g)` (`QED.ThreeLoopD.i2P1FAsm_main`), where
  `R(f) = ∫₀¹ ds 8 (1 + s²) / (s (1 - s²)) log² s ∫₀¹ dz 2 z f(r(s, z)²)`.

## Main results

* `QED.ThreeLoopD.i2P1FAsm_y`, `QED.ThreeLoopD.i2P1FAsm_q`, `QED.ThreeLoopD.i2P1FAsm_rho`.
* `QED.ThreeLoopD.i2P1FAsm_V`, `QED.ThreeLoopD.i2P1FAsm_main`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Function
open scoped ENNReal

namespace QED.ThreeLoopD

theorem measurable_i2P1FMt : Measurable i2P1FMt := by
  have : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (log (1 + p.1 * p.2 ^ 2 / (1 + p.2)) / (1 + p.2) ^ 2) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  exact this.lintegral_prod_right'

/-- **The `y₄`-integral**: `∫_{y > 0} log (1 + y² / (q + y)) / (q + y)² dy = M_t(q) / q`. -/
theorem i2P1FAsm_y {q : ℝ} (hq : 0 < q) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (log (1 + y ^ 2 / (q + y)) / (q + y) ^ 2) =
      ENNReal.ofReal (1 / q) * i2P1FMt q := by
  rw [i2P1FSub_scale (one_div_pos.2 hq), i2P1FMt, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show t / (1 / q) = t * q by field_simp, one_div_one_div,
    show (t * q) ^ 2 / (q + t * q) = q * t ^ 2 / (1 + t) by field_simp]
  field_simp

/-- Shift `q = s + c`: `∫_{s > 0} F(s) = ∫_{q > 0} 1[c < q] F(q - c)` for `c ≥ 0`. -/
theorem i2P1FAsm_shift {c : ℝ} (hc : 0 ≤ c) (F : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioi (0 : ℝ), F s = ∫⁻ q in Ioi (0 : ℝ), (if c < q then F (q - c) else 0) := by
  have e : ∀ q, (if c < q then F (q - c) else 0) = (Ioi c).indicator (fun q => F (q - c)) q :=
    fun q => by simp [indicator_apply]
  simp_rw [e]
  rw [setLIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left hc,
    ← i2P1FRect_shift c]
  simp

/-- **The integrand on the triangle**: at fixed `(α₁, α₃) = (u, v)`, the `y₄` and `s`
integrals give `∫_{q > 0} 1[u v < q] len(q - u v) M_t(q) / q`. -/
theorem i2P1FAsm_q {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    ∫⁻ y in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) s) *
          ENNReal.ofReal (log (1 + y ^ 2 / (s + u * v + y)) / (s + u * v + y) ^ 2) =
      ∫⁻ q in Ioi (0 : ℝ), (if u * v < q then
        ENNReal.ofReal (i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) (q - u * v)) else 0) *
          (ENNReal.ofReal (1 / q) * i2P1FMt q) := by
  have hm : Measurable (uncurry fun y s : ℝ =>
      ENNReal.ofReal (i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) s) *
        ENNReal.ofReal (log (1 + y ^ 2 / (s + u * v + y)) / (s + u * v + y) ^ 2)) :=
    (ENNReal.measurable_ofReal.comp (by unfold i2P1FLen; fun_prop)).mul
      (ENNReal.measurable_ofReal.comp (by fun_prop))
  rw [lintegral_lintegral_swap hm.aemeasurable,
    i2P1FAsm_shift (mul_pos hu hv).le]
  refine setLIntegral_congr_fun measurableSet_Ioi fun q (hq : 0 < q) => ?_
  split_ifs with h
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, sub_add_cancel, i2P1FAsm_y hq]
  · simp

/-- **`q = k ρ`**: `∫_{q > 0} M_t(q) / q ∫₀¹ F(q / k) / k dξ
= ∫_{ρ > 0} F(ρ) ∫₀¹ M_t(ρ k) / (ρ k) dξ`. -/
theorem i2P1FAsm_rho {F : ℝ → ℝ} (hF : Measurable F) :
    ∫⁻ q in Ioi (0 : ℝ), ENNReal.ofReal (1 / q) * i2P1FMt q *
        ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (F (q / (ξ * (1 - ξ))) / (ξ * (1 - ξ))) =
      ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (F ρ) * ∫⁻ ξ in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) * i2P1FMt (ρ * (ξ * (1 - ξ))) := by
  have hMt := measurable_i2P1FMt
  have m1 : Measurable (uncurry fun q ξ : ℝ => ENNReal.ofReal (1 / q) * i2P1FMt q *
      ENNReal.ofReal (F (q / (ξ * (1 - ξ))) / (ξ * (1 - ξ)))) :=
    ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hMt.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp ((hF.comp (by fun_prop)).div (by fun_prop)))
  have m2 : Measurable (uncurry fun ξ ρ : ℝ => ENNReal.ofReal (F ρ) *
      (ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) * i2P1FMt (ρ * (ξ * (1 - ξ))))) :=
    (ENNReal.measurable_ofReal.comp (hF.comp measurable_snd)).mul
      ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hMt.comp (by fun_prop)))
  calc ∫⁻ q in Ioi (0 : ℝ), ENNReal.ofReal (1 / q) * i2P1FMt q *
        ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (F (q / (ξ * (1 - ξ))) / (ξ * (1 - ξ)))
      = ∫⁻ q in Ioi (0 : ℝ), ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / q) * i2P1FMt q *
          ENNReal.ofReal (F (q / (ξ * (1 - ξ))) / (ξ * (1 - ξ))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun q _ => ?_
        exact (lintegral_const_mul _ (show Measurable fun ξ : ℝ =>
          ENNReal.ofReal (F (q / (ξ * (1 - ξ))) / (ξ * (1 - ξ))) from
            ENNReal.measurable_ofReal.comp ((hF.comp (by fun_prop)).div (by fun_prop)))).symm
    _ = ∫⁻ ξ in Ioo (0 : ℝ) 1, ∫⁻ q in Ioi (0 : ℝ), ENNReal.ofReal (1 / q) * i2P1FMt q *
          ENNReal.ofReal (F (q / (ξ * (1 - ξ))) / (ξ * (1 - ξ))) :=
        lintegral_lintegral_swap m1.aemeasurable
    _ = ∫⁻ ξ in Ioo (0 : ℝ) 1, ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (F ρ) *
          (ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) * i2P1FMt (ρ * (ξ * (1 - ξ)))) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun ξ hξ => ?_
        have hk : 0 < ξ * (1 - ξ) := mul_pos hξ.1 (by linarith [hξ.2])
        have hξ0 : ξ ≠ 0 := hξ.1.ne'
        have hξ1 : 1 - ξ ≠ 0 := by linarith [hξ.2]
        rw [i2P1FSub_scale (one_div_pos.2 hk)]
        refine setLIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
        rw [show ρ / (1 / (ξ * (1 - ξ))) = ρ * (ξ * (1 - ξ)) by field_simp,
          show ρ * (ξ * (1 - ξ)) / (ξ * (1 - ξ)) = ρ by field_simp]
        calc ENNReal.ofReal (1 / (1 / (ξ * (1 - ξ)))) *
              (ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) * i2P1FMt (ρ * (ξ * (1 - ξ))) *
                ENNReal.ofReal (F ρ / (ξ * (1 - ξ))))
            = (ENNReal.ofReal (1 / (1 / (ξ * (1 - ξ)))) *
                ENNReal.ofReal (F ρ / (ξ * (1 - ξ)))) *
                (ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) * i2P1FMt (ρ * (ξ * (1 - ξ)))) := by
              ring
          _ = _ := by
              rw [← ENNReal.ofReal_mul (by positivity),
                show 1 / (1 / (ξ * (1 - ξ))) * (F ρ / (ξ * (1 - ξ))) = F ρ by field_simp]
    _ = ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (F ρ) *
          (ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) * i2P1FMt (ρ * (ξ * (1 - ξ)))) :=
        lintegral_lintegral_swap m2.aemeasurable
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
        exact lintegral_const_mul _ (show Measurable fun ξ : ℝ =>
          ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) * i2P1FMt (ρ * (ξ * (1 - ξ))) from
            (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hMt.comp (by fun_prop)))

/-- Lower integrals over the triangle, with a parameter, are jointly measurable. -/
theorem i2P1FAsm_meas_tri {f : ℝ → ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) :
    Measurable (uncurry fun u q => ∫⁻ v in Ioo (0 : ℝ) (1 - u), f u v q) := by
  set T : Set ((ℝ × ℝ) × ℝ) := {x | 0 < x.2 ∧ x.2 < 1 - x.1.1} with hT
  have hTm : MeasurableSet T :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop))
  have e : (uncurry fun u q => ∫⁻ v in Ioo (0 : ℝ) (1 - u), f u v q) =
      fun p : ℝ × ℝ => ∫⁻ v, T.indicator (fun x => f x.1.1 x.2 x.1.2) (p, v) := by
    funext p
    rw [uncurry_apply_pair, ← lintegral_indicator measurableSet_Ioo]
    rfl
  rw [e]
  exact ((hf.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk
    measurable_fst.snd))).indicator hTm).lintegral_prod_right'

/-- **The `ℱ`-part as an integral over `q`**: the lower integral of
`(1 - w) log (ℱ / 𝒰) / 𝒰²` over the domain of `I₂` is `∫_{q > 0} M_t(q) / q · W(q)`. -/
theorem i2P1FAsm_V :
    ∫⁻ z in i2Dom, ENNReal.ofReal ((1 - z.2.1) *
        log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) =
      ∫⁻ q in Ioi (0 : ℝ), ENNReal.ofReal (1 / q) * i2P1FMt q *
        ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), (if u * v < q then
          ENNReal.ofReal (i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) (q - u * v)) else 0) := by
  have hmΦ : Measurable fun z : ℝ × ℝ × ℝ × ℝ × ℝ => ENNReal.ofReal ((1 - z.2.1) *
      log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 / i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) :=
    ENNReal.measurable_ofReal.comp (by unfold i2F i2U i2LineA i2LineB i2LineC; fun_prop)
  have h4 : Measurable fun r : ((ℝ × ℝ) × ℝ) × ℝ =>
      ENNReal.ofReal (i2P1FLen (r.1.1.1 * (1 - r.1.1.1 - r.1.1.2))
        (r.1.1.2 * (1 - r.1.1.1 - r.1.1.2)) r.2) *
      ENNReal.ofReal (log (1 + r.1.2 ^ 2 / (r.2 + r.1.1.1 * r.1.1.2 + r.1.2)) /
        (r.2 + r.1.1.1 * r.1.1.2 + r.1.2) ^ 2) :=
    (ENNReal.measurable_ofReal.comp (by unfold i2P1FLen; fun_prop)).mul
      (ENNReal.measurable_ofReal.comp (by fun_prop))
  have hg := (h4.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).lintegral_prod_right'
    (ν := volume.restrict (Ioi (0 : ℝ)))
  have hK : Measurable fun p : ℝ × ℝ × ℝ => (if p.1 * p.2.1 < p.2.2 then
      ENNReal.ofReal (i2P1FLen (p.1 * (1 - p.1 - p.2.1)) (p.2.1 * (1 - p.1 - p.2.1))
        (p.2.2 - p.1 * p.2.1)) else 0) * (ENNReal.ofReal (1 / p.2.2) * i2P1FMt p.2.2) :=
    (Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
      (ENNReal.measurable_ofReal.comp (by unfold i2P1FLen; fun_prop)) measurable_const).mul
      ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul (measurable_i2P1FMt.comp (by fun_prop)))
  have hite := i2P1FWS_meas_ite (q := 0) (f := fun _ _ => 0) (by fun_prop)
  rw [i2P1U_lint_dom hmΦ]
  calc _ = ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - w) *
          ∫⁻ y in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
            ENNReal.ofReal (i2P1FLen ((1 - w) * x * (1 - (1 - w) * x - (1 - w) * (1 - x)))
              ((1 - w) * (1 - x) * (1 - (1 - w) * x - (1 - w) * (1 - x))) s) *
            ENNReal.ofReal (log (1 + y ^ 2 / (s + (1 - w) * x * ((1 - w) * (1 - x)) + y)) /
              (s + (1 - w) * x * ((1 - w) * (1 - x)) + y) ^ 2) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        refine setLIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
        rw [i2P1FRect_y78 hx hw hy, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
        rw [show 1 - (1 - w) * x - (1 - w) * (1 - x) = w by ring,
          ENNReal.ofReal_mul (by linarith [hw.2] : (0 : ℝ) ≤ 1 - w), i2P1Fg,
          show s + i2LineC x w y = s + (1 - w) * x * ((1 - w) * (1 - x)) + y by
            simp only [i2LineC]; ring,
          show w * (1 - w) * x = (1 - w) * x * w by ring,
          show w * (1 - w) * (1 - x) = (1 - w) * (1 - x) * w by ring]
        ring
    _ = ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u),
          ∫⁻ y in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
            ENNReal.ofReal (i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) s) *
            ENNReal.ofReal (log (1 + y ^ 2 / (s + u * v + y)) / (s + u * v + y) ^ 2) :=
        i2P1US_xw_C (g := fun u v => ∫⁻ y in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
            ENNReal.ofReal (i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) s) *
            ENNReal.ofReal (log (1 + y ^ 2 / (s + u * v + y)) / (s + u * v + y) ^ 2)) hg
    _ = ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), ∫⁻ q in Ioi (0 : ℝ),
          (if u * v < q then
            ENNReal.ofReal (i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) (q - u * v)) else 0) *
          (ENNReal.ofReal (1 / q) * i2P1FMt q) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
        refine setLIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
        exact i2P1FAsm_q hu.1 hv.1
    _ = ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ q in Ioi (0 : ℝ), ∫⁻ v in Ioo (0 : ℝ) (1 - u),
          (if u * v < q then
            ENNReal.ofReal (i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) (q - u * v)) else 0) *
          (ENNReal.ofReal (1 / q) * i2P1FMt q) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
        exact lintegral_lintegral_swap ((hK.comp (by fun_prop :
          Measurable fun p : ℝ × ℝ => (u, p.1, p.2))).aemeasurable)
    _ = ∫⁻ q in Ioi (0 : ℝ), ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u),
          (if u * v < q then
            ENNReal.ofReal (i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) (q - u * v)) else 0) *
          (ENNReal.ofReal (1 / q) * i2P1FMt q) :=
        lintegral_lintegral_swap (i2P1FAsm_meas_tri hK).aemeasurable
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun q _ => ?_
        have m1 := i2P1FWS_meas_ite (q := q)
          (f := fun u v => i2P1FLen (u * (1 - u - v)) (v * (1 - u - v)) (q - u * v))
          (by unfold i2P1FLen; fun_prop)
        rw [mul_comm (ENNReal.ofReal (1 / q) * i2P1FMt q),
          ← lintegral_mul_const _ (i2P1FWS_meas_tri m1)]
        refine setLIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
        exact lintegral_mul_const _ (m1.comp measurable_prodMk_left)

/-- **`V + R(h) = R(g)`**: the lower integral `V` of the `ℱ`-part over the domain of `I₂`,
with `R(f) = ∫₀¹ ds 8 (1 + s²) / (s (1 - s²)) log² s ∫₀¹ dz 2 z f(r(s, z)²)`. -/
theorem i2P1FAsm_main :
    (∫⁻ z in i2Dom, ENNReal.ofReal ((1 - z.2.1) *
        log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2)) +
      ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2) *
        ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * z) *
          ENNReal.ofReal (i2P1Fhr (((1 - s ^ 2) * z / (s * (1 - z ^ 2))) ^ 2)) =
      ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2) *
        ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * z) *
          ENNReal.ofReal (i2P1Fgr (((1 - s ^ 2) * z / (s * (1 - z ^ 2))) ^ 2)) := by
  have hh := i2P1FSub_main (H := fun ρ => ENNReal.ofReal (i2P1Fhr ρ))
    (ENNReal.measurable_ofReal.comp measurable_i2P1Fhr)
  have hgg := i2P1FSub_main (H := fun ρ => ENNReal.ofReal (i2P1Fgr ρ))
    (ENNReal.measurable_ofReal.comp measurable_i2P1Fgr)
  have hW3 : Measurable fun q : ℝ => ENNReal.ofReal (1 / q) * i2P1FMt q *
      ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Fhr (q / (ξ * (1 - ξ))) / (ξ * (1 - ξ))) := by
    have : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (i2P1Fhr (p.1 / (p.2 * (1 - p.2))) / (p.2 * (1 - p.2))) :=
      ENNReal.measurable_ofReal.comp ((measurable_i2P1Fhr.comp (by fun_prop)).div (by fun_prop))
    exact ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul measurable_i2P1FMt).mul
      this.lintegral_prod_right'
  rw [← hh, ← hgg, ← i2P1FAsm_rho measurable_i2P1Fhr, ← i2P1FAsm_rho measurable_i2P1Fgr,
    i2P1FAsm_V, ← lintegral_add_right _ hW3]
  refine setLIntegral_congr_fun measurableSet_Ioi fun q (hq : 0 < q) => ?_
  rw [← mul_add, i2P1FWS_main hq]

end QED.ThreeLoopD
