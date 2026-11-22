/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEQZ
public import QED.Integration.SimplexMerge
public import QED.Integration.TwoLoopParametricAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The two-line affine block of the self-energy in closed form

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan. After the
partial fractions of `QED/ChainProof/SetCRegDispShellSEPF.lean`, the affine part of the class
`V` limit is a combination of the limits `seProdLim` of the affine numerator against two photon
lines of masses `μ, ν`. For `μ² ≠ ν²` the simplex integral is a logarithm:

`seProdLim 0 (c + b ℓ̸) m ![μ, ν] P = ∫₀¹ 2 G(y) (log Δ_μ(y) - log Δ_ν(y)) / (μ² - ν²) dy`,

with `Δ_M(y) = y m² + (1 - y) M² + y (1 - y) P²` and `G(y)` the constant of the closed form
`seAffY` at `n = 1` (`seAffG`). Since `Δ_M(y) = (1 - y) (M² + a(y))`, the logarithm is the tail
`∫_a^∞ (P_{μ²} - P_{ν²})` of the photon pair (`QED.ChainProof.SetCRegDisp.seArg`).

* `seAffG`, `seAffY_zero`: the closed form at `n = 1` is `G(y) Δ⁻¹`;
* `integral_simplexOne_inv`: `∫_{Δ₁} (A + B u)⁻¹ du = (log (A + B) - log A)/B`;
* `selfEnergyFeynmanMass_mixMass_two`: `Δ` at the mixed mass of `![μ, ν]` is affine in `u`;
* **`seProdLim_seAff_two`**: the closed form above;
* **`seProdLim_seAff_double`**: the repeated mass `![μ, μ]`, `∫₀¹ seWt₁(y) G(y) Δ_μ(y)⁻¹ dy`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.WickModel.SelfEnergyLimit QED.OneLoop
open QED.ChainProof.SetCRegDispSE (seWt seRadC seProdLim)
open QED.TwoLoop.VPHalfAtLimit (energyConst mixMass mixMassSq mixMass_ge mixMassSq_nonneg
  continuous_mixMass)
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  isCompact_simplexSet)
open QED.Integration.TwoLoop (simplexPoint_castSucc simplexPoint_last)

/-- The constant of the affine closed form at `n = 1`. -/
noncomputable def seAffG (c b : ℂ) (α β : Fin 4) (P : Fin 4 → ℝ) (y : ℝ) : ℂ :=
  (-1) ^ 3 * ((energyConst 3 : ℝ) : ℂ) * seAff c b α β (-(y • P)) *
    (exp (π * I * (-((5 / 2 : ℝ) : ℂ))) * ((4 * π * seRadC 0 : ℝ) : ℂ))

theorem seAffY_zero (c b : ℂ) (α β : Fin 4) (m M : ℝ) (P : Fin 4 → ℝ) (y : ℝ) :
    seAffY c b α β m M 0 P y =
      seAffG c b α β P y * ((selfEnergyFeynmanMass m M (Minkowski.dot P P) y)⁻¹ : ℝ) := by
  unfold seAffY seAffG
  simp only [Nat.cast_zero, zero_add, Real.rpow_neg_one]
  push_cast
  ring

/-! ### The simplex integral -/

theorem integral_simplexOne_eq (h : ℝ → ℝ) :
    ∫ x in simplexSet 1, h (x 0) = ∫ t in (0 : ℝ)..1, h t := by
  have hs : simplexSet 1 = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Icc (0 : ℝ) 1 := by
    ext x
    rw [QED.Integration.SimplexMerge.mem_simplexSet_iff_le one_pos]
    simp [MeasurableEquiv.funUnique]
  rw [hs, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding h _

/-- `∫_{Δ₁} (A + B u)⁻¹ du = (log (A + B) - log A)/B`. -/
theorem integral_simplexOne_inv {A B : ℝ} (hA : 0 < A) (hAB : 0 < A + B) (hB : B ≠ 0) :
    ∫ u in simplexSet 1, (A + B * u 0)⁻¹ = (Real.log (A + B) - Real.log A) / B := by
  rw [integral_simplexOne_eq (fun t => (A + B * t)⁻¹)]
  have e : (fun t : ℝ => (A + B * t)⁻¹) = fun t => (fun x : ℝ => x⁻¹) (B * t + A) := by
    funext t; ring_nf
  rw [e, intervalIntegral.integral_comp_mul_add (fun x : ℝ => x⁻¹) hB A, mul_zero, zero_add,
    mul_one, integral_inv]
  · rw [Real.log_div (by linarith) hA.ne', smul_eq_mul, add_comm B A]
    field_simp
  · rw [Set.mem_uIcc]
    push Not
    constructor <;> intro h <;> linarith

theorem selfEnergyFeynmanMass_mixMass_two (m μ ν s y : ℝ) {u : Fin 1 → ℝ}
    (hu : u ∈ simplexSet 1) :
    selfEnergyFeynmanMass m (mixMass ![μ, ν] u) s y =
      selfEnergyFeynmanMass m ν s y + (1 - y) * (μ ^ 2 - ν ^ 2) * u 0 := by
  unfold mixMass
  rw [selfEnergyFeynmanMass, Real.sq_sqrt (mixMassSq_nonneg _ hu), selfEnergyFeynmanMass]
  have h0 : simplexPoint u (0 : Fin (1 + 1)) = u 0 := simplexPoint_castSucc u 0
  have h1 : simplexPoint u (1 : Fin (1 + 1)) = 1 - u 0 := by
    rw [show (1 : Fin (1 + 1)) = Fin.last 1 from rfl, simplexPoint_last, Fin.sum_univ_one]
  simp only [mixMassSq, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  erw [h0, h1]
  simp
  ring

/-! ### The block -/

/-- **The two-line affine block**: for `μ² ≠ ν²`, below threshold,
`seProdLim 0 (c + b ℓ̸) m ![μ, ν] P = ∫₀¹ 2 G(y) (log Δ_μ - log Δ_ν)/(μ² - ν²) dy`. -/
theorem seProdLim_seAff_two {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {P : Fin 4 → ℝ}
    (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)
    {μ ν : ℝ} (hμ : M₀ ≤ μ) (hν : M₀ ≤ ν) (hμν : μ ^ 2 ≠ ν ^ 2) (c b : ℂ) (α β : Fin 4) :
    seProdLim 0 (seAff c b α β) m ![μ, ν] P =
      ∫ y in Ioc (0 : ℝ) 1, 2 * seAffG c b α β P y *
        (((Real.log (selfEnergyFeynmanMass m μ (Minkowski.dot P P) y) -
          Real.log (selfEnergyFeynmanMass m ν (Minkowski.dot P P) y)) / (μ ^ 2 - ν ^ 2) : ℝ) :
            ℂ) := by
  set s := Minkowski.dot P P
  have hMs : ∀ j, M₀ ≤ (![μ, ν] : Fin 2 → ℝ) j := by
    intro j; fin_cases j <;> simpa
  rw [seProdLim_seAff_eq hM₀ hc₀ hP hMs c b α β]
  simp only [zero_add, Nat.factorial_one, Nat.cast_one, one_mul]
  simp_rw [seAffY_zero]
  -- Fubini on `Δ₁ × (0, 1]`
  have : IsFiniteMeasure ((volume : Measure (Fin 1 → ℝ)).restrict (simplexSet 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_simplexSet 1).measure_lt_top.ne
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hpos : ∀ u ∈ simplexSet 1, ∀ y ∈ Icc (0 : ℝ) 1,
      c₀ ≤ selfEnergyFeynmanMass m (mixMass ![μ, ν] u) s y := fun u hu y hy =>
    (hP y hy).trans (SetCRegDispSE.selfEnergyFeynmanMass_mono hM₀ (mixMass_ge hM₀ hMs hu) hy)
  set CN := ‖c‖ + ‖b‖ * seGs α β
  set CG : ℝ := ‖(-1 : ℂ) ^ 3 * ((energyConst 3 : ℝ) : ℂ)‖ * (CN * (1 + ‖P‖)) *
    ‖exp (π * I * (-((5 / 2 : ℝ) : ℂ))) * ((4 * π * seRadC 0 : ℝ) : ℂ)‖
  have hG : ∀ y ∈ Icc (0 : ℝ) 1, ‖seAffG c b α β P y‖ ≤ CG := by
    intro y hy
    unfold seAffG
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      (norm_nonneg _)
    refine (norm_seAff_le c b α β _).trans ?_
    rw [pow_one]
    have hCN : 0 ≤ CN := by have := seGs_nonneg α β; positivity
    refine mul_le_mul_of_nonneg_left ?_ hCN
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hy.1]
    have := mul_le_of_le_one_left (norm_nonneg P) hy.2
    linarith
  have hmeas : Measurable fun q : (Fin 1 → ℝ) × ℝ => seWt 1 q.2 * (seAffG c b α β P q.2 *
      (((selfEnergyFeynmanMass m (mixMass ![μ, ν] q.1) s q.2)⁻¹ : ℝ) : ℂ)) := by
    have h1 : Continuous fun y : ℝ => seAffG c b α β P y := by
      unfold seAffG
      have : Continuous fun y : ℝ => -(y • P) := (continuous_id.smul continuous_const).neg
      exact ((continuous_const.mul ((continuous_seAff c b α β).comp this)).mul continuous_const)
    have h2 : Measurable fun q : (Fin 1 → ℝ) × ℝ =>
        selfEnergyFeynmanMass m (mixMass ![μ, ν] q.1) s q.2 := by
      unfold selfEnergyFeynmanMass
      have : Measurable fun q : (Fin 1 → ℝ) × ℝ => mixMass ![μ, ν] q.1 :=
        (continuous_mixMass ![μ, ν]).measurable.comp measurable_fst
      fun_prop
    exact ((SetCRegDispSE.continuous_seWt 1).measurable.comp measurable_snd).mul
      ((h1.measurable.comp measurable_snd).mul (Complex.measurable_ofReal.comp h2.inv))
  have hint : Integrable (fun q : (Fin 1 → ℝ) × ℝ => seWt 1 q.2 * (seAffG c b α β P q.2 *
      (((selfEnergyFeynmanMass m (mixMass ![μ, ν] q.1) s q.2)⁻¹ : ℝ) : ℂ)))
      (((volume : Measure (Fin 1 → ℝ)).restrict (simplexSet 1)).prod
        ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))) := by
    refine (integrable_const ((1 + 1) * (CG * c₀⁻¹))).mono' hmeas.aestronglyMeasurable ?_
    have h1 := (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure (Fin 1 → ℝ)).restrict (simplexSet 1))
      (ν := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))).ae
      (ae_restrict_mem (measurableSet_simplexSet 1))
    have h2 := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Fin 1 → ℝ)).restrict (simplexSet 1))
      (ν := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))).ae
      (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [h1, h2] with q hq1 hq2
    have hy := Ioc_subset_Icc_self hq2
    have hD := hpos q.1 hq1 q.2 hy
    have hDp : 0 < selfEnergyFeynmanMass m (mixMass ![μ, ν] q.1) s q.2 := hc₀.trans_le hD
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hDp]
    have hW := SetCRegDispSE.seWt_norm_le (n := 1) hy
    push_cast at hW
    have hinv : (selfEnergyFeynmanMass m (mixMass ![μ, ν] q.1) s q.2)⁻¹ ≤ c₀⁻¹ :=
      inv_anti₀ hc₀ hD
    have hCG : 0 ≤ CG := (norm_nonneg _).trans (hG q.2 hy)
    exact mul_le_mul hW (mul_le_mul (hG q.2 hy) hinv (by positivity) hCG) (by positivity)
      (by norm_num)
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  have hyI := Ioc_subset_Icc_self hy
  rw [integral_const_mul, integral_const_mul, integral_complex_ofReal]
  set A := selfEnergyFeynmanMass m ν s y
  set B := (1 - y) * (μ ^ 2 - ν ^ 2)
  have hA : 0 < A := hc₀.trans_le ((hP y hyI).trans
    (SetCRegDispSE.selfEnergyFeynmanMass_mono hM₀ hν hyI))
  have hAμ : selfEnergyFeynmanMass m μ s y = A + B := by
    simp only [A, B, selfEnergyFeynmanMass]; ring
  have hAB : 0 < A + B := by
    rw [← hAμ]
    exact hc₀.trans_le ((hP y hyI).trans (SetCRegDispSE.selfEnergyFeynmanMass_mono hM₀ hμ hyI))
  have hcongr : ∫ u in simplexSet 1, (selfEnergyFeynmanMass m (mixMass ![μ, ν] u) s y)⁻¹ =
      ∫ u in simplexSet 1, (A + B * u 0)⁻¹ :=
    setIntegral_congr_fun (measurableSet_simplexSet 1) fun u hu => by
      rw [selfEnergyFeynmanMass_mixMass_two m μ ν s y hu]
  rw [hcongr, hAμ]
  have hμν' : μ ^ 2 - ν ^ 2 ≠ 0 := sub_ne_zero.2 hμν
  rcases eq_or_lt_of_le hy.2 with h1 | h1
  · -- `y = 1`: both sides vanish
    have hB0 : B = 0 := by simp only [B, h1, sub_self, zero_mul]
    simp only [seWt, hB0, add_zero, sub_self, zero_div, h1]
    push_cast
    ring
  · have hB : B ≠ 0 := mul_ne_zero (by linarith) hμν'
    rw [integral_simplexOne_inv hA hAB hB]
    have hy1 : (1 - y) ≠ 0 := by linarith
    have key : (1 - y) * ((Real.log (A + B) - Real.log A) / B) =
        (Real.log (A + B) - Real.log A) / (μ ^ 2 - ν ^ 2) := by
      simp only [B]
      field_simp
    rw [← key]
    simp only [seWt]
    push_cast
    ring

/-- **The double-line affine block**: `seProdLim 0 (c + b ℓ̸) m ![μ, μ] P = ∫₀¹ 2 (1 - y) G(y)
Δ_μ(y)⁻¹ dy`. -/
theorem seProdLim_seAff_double {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {P : Fin 4 → ℝ}
    (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)
    {μ : ℝ} (hμ : M₀ ≤ μ) (c b : ℂ) (α β : Fin 4) :
    seProdLim 0 (seAff c b α β) m ![μ, μ] P =
      ∫ y in Ioc (0 : ℝ) 1, seWt 1 y * (seAffG c b α β P y *
        (((selfEnergyFeynmanMass m μ (Minkowski.dot P P) y)⁻¹ : ℝ) : ℂ)) := by
  have hMs : ∀ j, M₀ ≤ (![μ, μ] : Fin 2 → ℝ) j := by
    intro j; fin_cases j <;> simpa
  rw [seProdLim_seAff_eq hM₀ hc₀ hP hMs c b α β]
  simp only [zero_add, Nat.factorial_one, Nat.cast_one, one_mul]
  simp_rw [seAffY_zero]
  have hcongr : ∀ u ∈ simplexSet 1, (∫ y in Ioc (0 : ℝ) 1, seWt 1 y * (seAffG c b α β P y *
      (((selfEnergyFeynmanMass m (mixMass ![μ, μ] u) (Minkowski.dot P P) y)⁻¹ : ℝ) : ℂ))) =
      ∫ y in Ioc (0 : ℝ) 1, seWt 1 y * (seAffG c b α β P y *
        (((selfEnergyFeynmanMass m μ (Minkowski.dot P P) y)⁻¹ : ℝ) : ℂ)) := by
    intro u hu
    refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    rw [selfEnergyFeynmanMass_mixMass_two m μ μ _ y hu, sub_self, mul_zero, zero_mul, add_zero]
  rw [setIntegral_congr_fun (measurableSet_simplexSet 1) hcongr, setIntegral_const]
  have hv : (volume.real (simplexSet 1)) = 1 := by
    have h := integral_simplexOne_eq (fun _ => (1 : ℝ))
    simp only [setIntegral_const, smul_eq_mul, mul_one, intervalIntegral.integral_const,
      sub_zero] at h
    exact h
  rw [hv, one_smul]

end QED.ChainProof.SetCRegDisp

end
