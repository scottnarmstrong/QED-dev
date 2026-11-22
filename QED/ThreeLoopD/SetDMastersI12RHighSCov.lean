/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSRefl
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Set (d), master `I₁₂`: the reflection of the sectors as an identity of integrals

In the chart `(x, s) = (ρ, θ)` of the sector `t < v` of the bulk remainder, the sector `v < t`
is the region `s > 1`, `x < s⁻¹` (`QED.ThreeLoopD.i12HSDom`): the map
`(x, s, u) ↦ (ρ, θ, u) = (xs, s⁻¹, u)` carries `i12HSDom` onto the cube with Jacobian `s⁻¹`.
By the pointwise reflection `QED.ThreeLoopD.i12HSMainB_eq_reflect`, the main part of the
order-`n` integrand of `R_B` becomes the main part of that of `R_A`, continued past `s = 1`.
So the two sectors are one integral over `0 < s < x⁻¹`, whose main part is the single function
`i12HSMainA n x s u` (the input of the Mellin evaluation in `s ∈ (0, ∞)`), and whose face
parts are those of `R_A` for `s < 1` and the reflected ones of `R_B` for `s > 1`.

The change of variables is proved by two fibrewise one-dimensional substitutions (`θ = s⁻¹`,
then `ρ = xs`), transporting integrability from the cube; no bound is needed.

## Main results

* `QED.ThreeLoopD.i12HS_cov`: for any measurable `f` integrable on the cube,
  `∫_{(0,1)³} f = ∫_{i12HSDom} f(xs, s⁻¹, u) / s`, with integrability.
* `QED.ThreeLoopD.integral_i12RB3Dn_eq_pull`:
  `∫_{(0,1)³} D_Bⁿ = ∫_{i12HSDom} (MainAⁿ(x, s, u) + s⁻¹ FaceBⁿ(xs, s⁻¹, u))`.
* `QED.ThreeLoopD.integral_i12RA3Dn_add_i12RB3Dn`:
  `∫ D_Aⁿ + ∫ D_Bⁿ = ∫_{i12HSReg} W_n` (`QED.ThreeLoopD.i12HSW`), `W_n` integrable.
* `QED.ThreeLoopD.iteratedDeriv_succ_i12Rest_eq_reg`: the Taylor coefficients of the remainder
  with the merged sectors.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ThreeLoopD

section Transfer

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β} [SFinite μ] [SFinite ν]

/-- **Fibrewise transfer in the first coordinate**: if, for every `b`, the slice `G(·, b)`
matches the slice `F(·, b)` of an integrable `F` (integrability, integral, integral of the
norm), then `G` is integrable with the same integral and the same integral of the norm. -/
theorem i12HS_transfer_fst {F G : α × β → ℝ} (hF : Integrable F (μ.prod ν))
    (hG : AEStronglyMeasurable G (μ.prod ν))
    (hsl : ∀ b, Integrable (fun a => F (a, b)) μ → Integrable (fun a => G (a, b)) μ ∧
      ∫ a, G (a, b) ∂μ = ∫ a, F (a, b) ∂μ ∧ ∫ a, ‖G (a, b)‖ ∂μ = ∫ a, ‖F (a, b)‖ ∂μ) :
    Integrable G (μ.prod ν) ∧ ∫ z, G z ∂(μ.prod ν) = ∫ z, F z ∂(μ.prod ν) ∧
      ∫ z, ‖G z‖ ∂(μ.prod ν) = ∫ z, ‖F z‖ ∂(μ.prod ν) := by
  have hae := hF.prod_left_ae
  have hGi : Integrable G (μ.prod ν) := by
    refine (integrable_prod_iff' hG).2 ⟨?_, ?_⟩
    · filter_upwards [hae] with b hb using (hsl b hb).1
    · refine hF.integral_norm_prod_right.congr ?_
      filter_upwards [hae] with b hb using ((hsl b hb).2.2).symm
  refine ⟨hGi, ?_, ?_⟩
  · rw [integral_prod_symm G hGi, integral_prod_symm F hF]
    refine integral_congr_ae ?_
    filter_upwards [hae] with b hb using (hsl b hb).2.1
  · rw [integral_prod_symm _ hGi.norm, integral_prod_symm _ hF.norm]
    refine integral_congr_ae ?_
    filter_upwards [hae] with b hb using (hsl b hb).2.2

/-- **Fibrewise transfer in the second coordinate.** -/
theorem i12HS_transfer_snd {F G : α × β → ℝ} (hF : Integrable F (μ.prod ν))
    (hG : AEStronglyMeasurable G (μ.prod ν))
    (hsl : ∀ a, Integrable (fun b => F (a, b)) ν → Integrable (fun b => G (a, b)) ν ∧
      ∫ b, G (a, b) ∂ν = ∫ b, F (a, b) ∂ν ∧ ∫ b, ‖G (a, b)‖ ∂ν = ∫ b, ‖F (a, b)‖ ∂ν) :
    Integrable G (μ.prod ν) ∧ ∫ z, G z ∂(μ.prod ν) = ∫ z, F z ∂(μ.prod ν) ∧
      ∫ z, ‖G z‖ ∂(μ.prod ν) = ∫ z, ‖F z‖ ∂(μ.prod ν) := by
  have hae := hF.prod_right_ae
  have hGi : Integrable G (μ.prod ν) := by
    refine (integrable_prod_iff hG).2 ⟨?_, ?_⟩
    · filter_upwards [hae] with a ha using (hsl a ha).1
    · refine hF.integral_norm_prod_left.congr ?_
      filter_upwards [hae] with a ha using ((hsl a ha).2.2).symm
  refine ⟨hGi, ?_, ?_⟩
  · rw [integral_prod G hGi, integral_prod F hF]
    refine integral_congr_ae ?_
    filter_upwards [hae] with a ha using (hsl a ha).2.1
  · rw [integral_prod _ hGi.norm, integral_prod _ hF.norm]
    refine integral_congr_ae ?_
    filter_upwards [hae] with a ha using (hsl a ha).2.2

end Transfer

/-- **One-dimensional change of variables for functions extended by zero.** -/
theorem i12HS_slice {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {σ σ' h g : ℝ → ℝ} (hσ : ∀ x ∈ A, HasDerivWithinAt σ (σ' x) A x) (hinj : InjOn σ A)
    (himg : σ '' A = B) (hg : ∀ x ∈ A, |σ' x| * h (σ x) = g x) :
    (Integrable (B.indicator h) → Integrable (A.indicator g)) ∧
      ∫ x, A.indicator g x = ∫ x, B.indicator h x ∧
      ∫ x, ‖A.indicator g x‖ = ∫ x, ‖B.indicator h x‖ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [integrable_indicator_iff hB, integrable_indicator_iff hA, ← himg,
      integrableOn_image_iff_integrableOn_abs_deriv_smul hA hσ hinj]
    exact fun hi => hi.congr_fun (fun x hx => by simp only [smul_eq_mul, hg x hx]) hA
  · rw [integral_indicator hA, integral_indicator hB, ← himg,
      integral_image_eq_integral_abs_deriv_smul hA hσ hinj]
    exact setIntegral_congr_fun hA fun x hx => by simp only [smul_eq_mul, hg x hx]
  · simp_rw [norm_indicator_eq_indicator_norm]
    rw [integral_indicator hA, integral_indicator hB, ← himg,
      integral_image_eq_integral_abs_deriv_smul hA hσ hinj]
    refine setIntegral_congr_fun hA fun x hx => ?_
    rw [← hg x hx, smul_eq_mul, norm_mul, Real.norm_eq_abs |σ' x|, abs_abs]

/-- The image of the sector `v < t` in the chart of the sector `t < v`:
`{(x, s, u) : s > 1, 0 < x < s⁻¹, 0 < u < 1}`. -/
def i12HSDom : Set (ℝ × ℝ × ℝ) :=
  {z | z.2.1 ∈ Ioi 1 ∧ z.1 ∈ Ioo 0 z.2.1⁻¹ ∧ z.2.2 ∈ Ioo 0 1}

theorem measurableSet_i12HSDom : MeasurableSet i12HSDom := by
  unfold i12HSDom
  refine (measurableSet_lt measurable_const (by fun_prop)).inter
    (((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst (by fun_prop))).inter
      ((measurableSet_lt measurable_const (by fun_prop)).inter
        (measurableSet_lt (by fun_prop) measurable_const)))

/-- The intermediate region `(0, 1) × (1, ∞) × (0, 1)`. -/
abbrev i12HSMid : Set (ℝ × ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ (Ioi (1 : ℝ) ×ˢ Ioo (0 : ℝ) 1)

/-- **The reflection as a change of variables on the cube**: `(ρ, θ) = (xs, s⁻¹)` carries
`i12HSDom` onto `(0, 1)²` (in the first two coordinates) with Jacobian `s⁻¹`. -/
theorem i12HS_cov {f : ℝ × ℝ × ℝ → ℝ} (hf : Measurable f) (hI : IntegrableOn f i12Cube) :
    IntegrableOn (fun z => f (z.1 * z.2.1, z.2.1⁻¹, z.2.2) / z.2.1) i12HSDom ∧
      ∫ z in i12Cube, f z = ∫ z in i12HSDom, f (z.1 * z.2.1, z.2.1⁻¹, z.2.2) / z.2.1 := by
  have hC : MeasurableSet i12Cube :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  have hM : MeasurableSet i12HSMid :=
    measurableSet_Ioo.prod (measurableSet_Ioi.prod measurableSet_Ioo)
  set F := i12Cube.indicator f with hFd
  set F1 := i12HSMid.indicator (fun z => f (z.1, z.2.1⁻¹, z.2.2) / z.2.1 ^ 2) with hF1d
  set F2 := i12HSDom.indicator (fun z => f (z.1 * z.2.1, z.2.1⁻¹, z.2.2) / z.2.1) with hF2d
  have hF : Integrable F (volume.prod (volume.prod volume)) :=
    (integrable_indicator_iff hC).2 hI
  have mF1 : Measurable F1 :=
    ((hf.comp (by fun_prop)).div (by fun_prop)).indicator hM
  have mF2 : Measurable F2 :=
    ((hf.comp (by fun_prop)).div (by fun_prop)).indicator measurableSet_i12HSDom
  -- step 1: `θ = s⁻¹`
  have step1 := i12HS_transfer_snd hF mF1.aestronglyMeasurable fun ρ hρi => by
    by_cases hρ : ρ ∈ Ioo (0 : ℝ) 1
    · refine i12HS_transfer_fst hρi (mF1.comp measurable_prodMk_left).aestronglyMeasurable
        fun u hui => ?_
      by_cases hu : u ∈ Ioo (0 : ℝ) 1
      · have e0 : ∀ θ, F (ρ, θ, u) = (Ioo 0 1).indicator (fun θ => f (ρ, θ, u)) θ := fun θ => by
          simp [hFd, indicator_apply, hρ, hu]
        have e1 : ∀ s, F1 (ρ, s, u) = (Ioi 1).indicator (fun s => f (ρ, s⁻¹, u) / s ^ 2) s :=
          fun s => by simp [hF1d, indicator_apply, hρ, hu]
        simp only [e0] at hui
        simp only [e0, e1]
        have hs := i12HS_slice (A := Ioi 1) (B := Ioo 0 1) measurableSet_Ioi measurableSet_Ioo
          (σ := fun s => s⁻¹) (σ' := fun s => -(s ^ 2)⁻¹) (h := fun θ => f (ρ, θ, u))
          (g := fun s => f (ρ, s⁻¹, u) / s ^ 2)
          (fun s hs => (hasDerivAt_inv (by linarith [mem_Ioi.1 hs])).hasDerivWithinAt)
          (fun a ha b hb hab => inv_injective hab)
          (by
            ext θ
            simp only [mem_image, mem_Ioi, mem_Ioo]
            constructor
            · rintro ⟨s, hs, rfl⟩
              exact ⟨inv_pos.2 (by linarith), inv_lt_one_of_one_lt₀ hs⟩
            · rintro ⟨h0, h1⟩
              exact ⟨θ⁻¹, (one_lt_inv₀ h0).2 h1, inv_inv θ⟩)
          (fun s hs => by
            have : 0 < s := by linarith [mem_Ioi.1 hs]
            rw [abs_neg, abs_of_pos (by positivity)]
            ring)
        exact ⟨hs.1 hui, hs.2.1, hs.2.2⟩
      · have e0 : ∀ θ, F (ρ, θ, u) = 0 := fun θ => by simp [hFd, hu]
        have e1 : ∀ s, F1 (ρ, s, u) = 0 := fun s => by simp [hF1d, hu]
        simp [e0, e1]
    · have e0 : ∀ c : ℝ × ℝ, F (ρ, c) = 0 := fun c => by simp [hFd, hρ]
      have e1 : ∀ c : ℝ × ℝ, F1 (ρ, c) = 0 := fun c => by simp [hF1d, hρ]
      simp [e0, e1]
  -- step 2: `ρ = xs`
  have step2 := i12HS_transfer_fst step1.1 mF2.aestronglyMeasurable fun b hbi => by
    obtain ⟨s, u⟩ := b
    by_cases hb : s ∈ Ioi (1 : ℝ) ∧ u ∈ Ioo (0 : ℝ) 1
    · obtain ⟨hs, hu⟩ := hb
      have hs0 : 0 < s := by linarith [mem_Ioi.1 hs]
      have e0 : ∀ ρ, F1 (ρ, s, u) = (Ioo 0 1).indicator (fun ρ => f (ρ, s⁻¹, u) / s ^ 2) ρ :=
        fun ρ => by simp [hF1d, indicator_apply, mem_Ioi.1 hs, hu.1, hu.2]
      have e1 : ∀ x, F2 (x, s, u) = (Ioo 0 s⁻¹).indicator (fun x => f (x * s, s⁻¹, u) / s) x :=
        fun x => by simp [hF2d, i12HSDom, indicator_apply, mem_Ioi.1 hs, hu.1, hu.2]
      simp only [e0] at hbi
      simp only [e0, e1]
      have hsl := i12HS_slice (A := Ioo 0 s⁻¹) (B := Ioo 0 1) measurableSet_Ioo
        measurableSet_Ioo (σ := fun x => x * s) (σ' := fun _ => s)
        (h := fun ρ => f (ρ, s⁻¹, u) / s ^ 2) (g := fun x => f (x * s, s⁻¹, u) / s)
        (fun x _ => ((hasDerivAt_id x).mul_const s).hasDerivWithinAt.congr_deriv (by simp))
        (fun a _ b _ hab => mul_right_cancel₀ hs0.ne' hab)
        (by rw [image_mul_right_Ioo _ _ hs0]; simp [hs0.ne'])
        (fun x _ => by
          rw [abs_of_pos hs0]
          field_simp)
      exact ⟨hsl.1 hbi, hsl.2.1, hsl.2.2⟩
    · have e0 : ∀ ρ, F1 (ρ, s, u) = 0 := fun ρ => by
        rw [hF1d, indicator_of_notMem (by simp only [mem_prod]; tauto)]
      have e1 : ∀ x, F2 (x, s, u) = 0 := fun x => by
        rw [hF2d, indicator_of_notMem (by simp only [i12HSDom, mem_ofPred_eq]; tauto)]
      simp [e0, e1]
  have hI2 : Integrable F2 (volume.prod (volume.prod volume)) := step2.1
  refine ⟨(integrable_indicator_iff measurableSet_i12HSDom).1 hI2, ?_⟩
  have h1 : ∫ z, F z ∂(volume.prod (volume.prod volume)) = ∫ z in i12Cube, f z :=
    integral_indicator hC
  have h2 : ∫ z, F2 z ∂(volume.prod (volume.prod volume)) =
      ∫ z in i12HSDom, f (z.1 * z.2.1, z.2.1⁻¹, z.2.2) / z.2.1 :=
    integral_indicator measurableSet_i12HSDom
  rw [← h1, ← h2, step2.2.1, step1.2.1]

theorem measurable_i12RB3Dn (n : ℕ) :
    Measurable fun z : ℝ × ℝ × ℝ => i12RB3Dn n z.1 z.2.1 z.2.2 := by
  unfold i12RB3Dn i12H; fun_prop

theorem measurable_i12RA3Dn (n : ℕ) :
    Measurable fun z : ℝ × ℝ × ℝ => i12RA3Dn n z.1 z.2.1 z.2.2 := by
  unfold i12RA3Dn i12H; fun_prop

/-- The integrand of `R_B` (order `n`) carried to `i12HSDom` by the reflection: the main part
of `R_A` continued to `s > 1`, plus the reflected face part of `R_B`. -/
noncomputable def i12HSPullB (n : ℕ) (x s u : ℝ) : ℝ :=
  i12HSMainA n x s u + s⁻¹ * i12HSFaceB n (x * s) s⁻¹ u

theorem i12RB3Dn_reflect (n : ℕ) {z : ℝ × ℝ × ℝ} (hz : z ∈ i12HSDom) :
    i12RB3Dn n (z.1 * z.2.1) z.2.1⁻¹ z.2.2 / z.2.1 = i12HSPullB n z.1 z.2.1 z.2.2 := by
  obtain ⟨x, s, u⟩ := z
  obtain ⟨hs, ⟨hx0, hx1⟩, hu0, hu1⟩ := hz
  simp only [mem_Ioi] at hs hx0 hx1 hu0 hu1 ⊢
  have hs0 : 0 < s := by linarith
  have hxs : x * s * s⁻¹ = x := by field_simp
  have hx1' : x < 1 := lt_of_lt_of_le hx1 (inv_le_one_of_one_le₀ hs.le)
  rw [i12RB3Dn_eq_main_add_face, i12HSMainB_eq_reflect n (by positivity) (inv_pos.2 hs0) hu0 hu1
    (by rw [hxs]; exact i12H_pos (by linarith)), hxs, inv_inv, i12HSPullB]
  field_simp

/-- **The sector `v < t` in the chart of the sector `t < v`**, order `n`:
`∫_{(0,1)³} D_Bⁿ = ∫_{i12HSDom} (main part of D_Aⁿ + reflected face part of D_Bⁿ)`. -/
theorem integral_i12RB3Dn_eq_pull (n : ℕ) :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSPullB n z.1 z.2.1 z.2.2) i12HSDom ∧
      ∫ z in i12Cube, i12RB3Dn n z.1 z.2.1 z.2.2 =
        ∫ z in i12HSDom, i12HSPullB n z.1 z.2.1 z.2.2 := by
  obtain ⟨hB, -⟩ := iteratedDeriv_i12RB3_eq_integral n
  have hBr : IntegrableOn (fun z : ℝ × ℝ × ℝ => i12RB3Dn n z.1 z.2.1 z.2.2) i12Cube := by
    exact hB.re
  obtain ⟨h1, h2⟩ := i12HS_cov (measurable_i12RB3Dn n) hBr
  refine ⟨h1.congr_fun (fun z hz => i12RB3Dn_reflect n hz) measurableSet_i12HSDom, ?_⟩
  rw [h2]
  exact setIntegral_congr_fun measurableSet_i12HSDom fun z hz => i12RB3Dn_reflect n hz

/-- The region `{(x, s, u) : 0 < x < 1, 0 < s < x⁻¹, s ≠ 1, 0 < u < 1}` (the two sectors in the
chart of the sector `t < v`). -/
abbrev i12HSReg : Set (ℝ × ℝ × ℝ) := i12Cube ∪ i12HSDom

/-- The integrand of `S_A + S_B` on `i12HSReg`: the main part of `D_Aⁿ` everywhere, plus the
face part of `D_Aⁿ` for `s < 1` and the reflected face part of `D_Bⁿ` for `s > 1`. -/
noncomputable def i12HSW (n : ℕ) (x s u : ℝ) : ℝ :=
  i12HSMainA n x s u + if s < 1 then i12HSFaceA n x s u else s⁻¹ * i12HSFaceB n (x * s) s⁻¹ u

theorem disjoint_i12Cube_i12HSDom : Disjoint i12Cube i12HSDom := by
  rw [Set.disjoint_left]
  rintro ⟨x, s, u⟩ ⟨-, ⟨-, hs⟩, -⟩ ⟨hs', -, -⟩
  simp only [mem_Ioi] at hs hs'
  linarith

/-- **The two sectors of the bulk remainder as one integral** (order `n`):
`∫_{(0,1)³} D_Aⁿ + ∫_{(0,1)³} D_Bⁿ = ∫_{i12HSReg} W_n`, where in the chart `(x, s) = (ρ, θ)` of
`t < v` and `(x, s) = (ρθ, θ⁻¹)` of `v < t` the main part of the integrand is the single
function `i12HSMainA n x s u` on `0 < s < x⁻¹`. -/
theorem integral_i12RA3Dn_add_i12RB3Dn (n : ℕ) :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSW n z.1 z.2.1 z.2.2) i12HSReg ∧
      (∫ z in i12Cube, (i12RA3Dn n z.1 z.2.1 z.2.2 : ℂ)) +
          ∫ z in i12Cube, (i12RB3Dn n z.1 z.2.1 z.2.2 : ℂ) =
        ((∫ z in i12HSReg, i12HSW n z.1 z.2.1 z.2.2 : ℝ) : ℂ) := by
  obtain ⟨hA, -⟩ := iteratedDeriv_i12RA3_eq_integral n
  have hAr : IntegrableOn (fun z : ℝ × ℝ × ℝ => i12RA3Dn n z.1 z.2.1 z.2.2) i12Cube := by
    exact hA.re
  obtain ⟨hP, hPe⟩ := integral_i12RB3Dn_eq_pull n
  have hC : MeasurableSet i12Cube :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  have eA : EqOn (fun z : ℝ × ℝ × ℝ => i12RA3Dn n z.1 z.2.1 z.2.2)
      (fun z => i12HSW n z.1 z.2.1 z.2.2) i12Cube := fun z hz => by
    simp only [i12HSW, hz.2.1.2, ↓reduceIte, i12RA3Dn_eq_main_add_face]
  have eB : EqOn (fun z : ℝ × ℝ × ℝ => i12HSPullB n z.1 z.2.1 z.2.2)
      (fun z => i12HSW n z.1 z.2.1 z.2.2) i12HSDom := fun z hz => by
    have : ¬ z.2.1 < 1 := not_lt.2 (le_of_lt hz.1)
    simp only [i12HSW, i12HSPullB, this, ↓reduceIte]
  have iA := hAr.congr_fun eA hC
  have iB := hP.congr_fun eB measurableSet_i12HSDom
  refine ⟨iA.union iB, ?_⟩
  rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_add,
    setIntegral_union disjoint_i12Cube_i12HSDom measurableSet_i12HSDom iA iB, hPe,
    setIntegral_congr_fun hC eA, setIntegral_congr_fun measurableSet_i12HSDom eB]

/-- **Every Taylor coefficient of the remainder with the two sectors merged**:
`i12Rest⁽ⁿ⁺¹⁾(0) = (n + 1) (∫ D₁ⁿ + ∫_{i12HSReg} W_n) + ∫ T_Aⁿ⁺¹ + ∫ T_Bⁿ⁺¹`. -/
theorem iteratedDeriv_succ_i12Rest_eq_reg (n : ℕ) :
    iteratedDeriv (n + 1) i12Rest 0 =
      (n + 1) * ((∫ z in i12Cube, (i12R1Dn n z.1 z.2.1 z.2.2 : ℂ)) +
        ((∫ z in i12HSReg, i12HSW n z.1 z.2.1 z.2.2 : ℝ) : ℂ)) +
      (∫ z in i12Sq, (i12TAd (n + 1) z.1 z.2 : ℂ)) +
      ∫ z in i12Sq, (i12TBd (n + 1) z.1 z.2 : ℂ) := by
  rw [iteratedDeriv_succ_i12Rest_eq_explicit, add_assoc (∫ z in i12Cube, (i12R1Dn n z.1 z.2.1
    z.2.2 : ℂ)), (integral_i12RA3Dn_add_i12RB3Dn n).2]

end QED.ThreeLoopD
