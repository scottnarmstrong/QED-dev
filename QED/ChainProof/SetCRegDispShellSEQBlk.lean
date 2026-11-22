/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSECov
public import QED.ChainProof.SetCRegDispShellSESim2
public import QED.Integration.TwoLoopParametricAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The three-line quadratic block of the self-energy in closed form

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (b1b). After the
reductions of `QED/ChainProof/SetCRegDispShellSERed.lean` the quadratic part of the class `V`
limit is a combination of the limits `seProdLim` of `seQuad p` (energy-squared coefficient
`seQuadA p`) against three photon lines. For pairwise distinct squared masses the simplex
integral is explicit: with `dᵢ(y) = Δ_{xᵢ}(y)`,

`seProdLim (seQuadA p) (seQuad p) m ![x₀, x₁, x₂] P`
`  = 2 ∫₀¹ seWt₂(y) (G₂(y) I₂(d(y)) - G₁ I₁(d(y))) dy`,

where `I₂`, `I₁` are the two-simplex integrals of `Λ⁻²`, `Λ⁻¹`
(`QED/ChainProof/SetCRegDispShellSESim2.lean`), `G₂(y)` carries `Q(-y P)` and `G₁` carries `p̸`
(the covariant form `QED.ChainProof.SetCRegDisp.seQuadY_seQuadA`).

* `seQuadG₂`, `seQuadG₁`, `seQuadY_seQuadA_zero`: the closed form at `n = 2` as
  `G₂ Δ⁻² - G₁ Δ⁻¹`;
* `selfEnergyFeynmanMass_mixMass_three`: `Δ` at the mixed mass of `![x₀, x₁, x₂]` is `Λ(u)`;
* `seSimI₂`, `seSimI₁`: the closed forms of the two-simplex integrals;
* `seSimJ₂`, `seSimJ₁`, `seSimJ₂_eq`, `seSimJ₁_eq`: the two-simplex integrals, explicit for
  distinct `dᵢ`;
* **`seProdLim_seQuad_three`**: the closed form above (with `J₂`, `J₁`).
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

/-- The coefficient of `Δ⁻²` in the quadratic closed form at `n = 2`. -/
noncomputable def seQuadG₂ (p : Fin 4 → ℝ) (α β : Fin 4) (P : Fin 4 → ℝ) (y : ℝ) : ℂ :=
  ((energyConst 4 : ℝ) : ℂ) * exp (π * I * (-((7 / 2 : ℝ) : ℂ))) *
    (seQuad p α β (-(y • P)) * ((4 * π * seRadC 1 : ℝ) : ℂ))

/-- The coefficient of `-Δ⁻¹` in the quadratic closed form at `n = 2`. -/
noncomputable def seQuadG₁ (p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  ((energyConst 3 - energyConst 4 : ℝ) : ℂ) * exp (π * I * (-((5 / 2 : ℝ) : ℂ))) *
    ((4 * π * seRadC 0 : ℝ) : ℂ) * Dirac.slash p α β

theorem seQuadY_seQuadA_zero (p : Fin 4 → ℝ) (α β : Fin 4) (m M : ℝ) (P : Fin 4 → ℝ)
    (y : ℝ) :
    seQuadY (seQuadA p α β) p α β m M 0 P y =
      seQuadG₂ p α β P y *
          (((selfEnergyFeynmanMass m M (Minkowski.dot P P) y ^ 2)⁻¹ : ℝ) : ℂ) -
        seQuadG₁ p α β * (((selfEnergyFeynmanMass m M (Minkowski.dot P P) y)⁻¹ : ℝ) : ℂ) := by
  rw [seQuadY_seQuadA]
  set Δ := selfEnergyFeynmanMass m M (Minkowski.dot P P) y
  have e2 : Δ ^ (-(((0 : ℕ) : ℝ) + 2)) = (Δ ^ 2)⁻¹ := by
    rw [show -(((0 : ℕ) : ℝ) + 2) = ((-2 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast,
      zpow_neg, zpow_ofNat]
  have e1 : Δ ^ (-(((0 : ℕ) : ℝ) + 1)) = Δ⁻¹ := by
    rw [show -(((0 : ℕ) : ℝ) + 1) = ((-1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast,
      zpow_neg, zpow_one]
  rw [e2, e1]
  unfold seQuadG₂ seQuadG₁
  simp only [Nat.cast_zero, zero_add]
  push_cast
  ring

theorem selfEnergyFeynmanMass_mixMass_three (m x₀ x₁ x₂ s y : ℝ) {u : Fin 2 → ℝ}
    (hu : u ∈ simplexSet 2) :
    selfEnergyFeynmanMass m (mixMass ![x₀, x₁, x₂] u) s y =
      simplexAff (selfEnergyFeynmanMass m x₀ s y) (selfEnergyFeynmanMass m x₁ s y)
        (selfEnergyFeynmanMass m x₂ s y) u := by
  unfold mixMass
  rw [selfEnergyFeynmanMass, Real.sq_sqrt (mixMassSq_nonneg _ hu)]
  have h0 : simplexPoint u (0 : Fin (2 + 1)) = u 0 := simplexPoint_castSucc u 0
  have h1 : simplexPoint u (1 : Fin (2 + 1)) = u 1 := simplexPoint_castSucc u 1
  have h2 : simplexPoint u (2 : Fin (2 + 1)) = 1 - (u 0 + u 1) := by
    rw [show (2 : Fin (2 + 1)) = Fin.last 2 from rfl, simplexPoint_last, Fin.sum_univ_two]
  simp only [mixMassSq, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  erw [h0, h1, h2]
  simp [simplexAff, selfEnergyFeynmanMass]
  ring

/-- `∫_{Δ₂} Λ⁻²` in closed form. -/
noncomputable def seSimI₂ (d₀ d₁ d₂ : ℝ) : ℝ :=
  ((Real.log d₁ - Real.log d₂) / (d₁ - d₂) - (Real.log d₁ - Real.log d₀) / (d₁ - d₀)) /
    (d₀ - d₂)

/-- `∫_{Δ₂} Λ⁻¹` in closed form. -/
noncomputable def seSimI₁ (d₀ d₁ d₂ : ℝ) : ℝ :=
  ((d₁ * Real.log d₁ - d₀ * Real.log d₀) / (d₁ - d₀) -
    (d₁ * Real.log d₁ - d₂ * Real.log d₂) / (d₁ - d₂)) / (d₀ - d₂)

/-- `∫_{Δ₂} Λ⁻²`. -/
noncomputable def seSimJ₂ (d₀ d₁ d₂ : ℝ) : ℝ :=
  ∫ u in simplexSet 2, (simplexAff d₀ d₁ d₂ u ^ 2)⁻¹

/-- `∫_{Δ₂} Λ⁻¹`. -/
noncomputable def seSimJ₁ (d₀ d₁ d₂ : ℝ) : ℝ :=
  ∫ u in simplexSet 2, (simplexAff d₀ d₁ d₂ u)⁻¹

theorem seSimJ₂_eq {d₀ d₁ d₂ : ℝ} (h₀ : 0 < d₀) (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₀₁ : d₀ ≠ d₁)
    (h₀₂ : d₀ ≠ d₂) (h₁₂ : d₁ ≠ d₂) : seSimJ₂ d₀ d₁ d₂ = seSimI₂ d₀ d₁ d₂ :=
  integral_simplexTwo_inv_sq h₀ h₁ h₂ h₀₁ h₀₂ h₁₂

theorem seSimJ₁_eq {d₀ d₁ d₂ : ℝ} (h₀ : 0 < d₀) (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₀₁ : d₀ ≠ d₁)
    (h₀₂ : d₀ ≠ d₂) (h₁₂ : d₁ ≠ d₂) : seSimJ₁ d₀ d₁ d₂ = seSimI₁ d₀ d₁ d₂ :=
  integral_simplexTwo_inv h₀ h₁ h₂ h₀₁ h₀₂ h₁₂

/-- **The three-line quadratic block**, below threshold:
`seProdLim (seQuadA p) (seQuad p) m ![x₀, x₁, x₂] P = 2 ∫₀¹ seWt₂ (G₂ J₂ - G₁ J₁) dy`, with
`J₂`, `J₁` the two-simplex integrals of `Λ⁻²`, `Λ⁻¹` at `dᵢ = Δ_{xᵢ}(y)` (closed forms:
`seSimJ₂_eq`, `seSimJ₁_eq` for distinct `dᵢ`). -/
theorem seProdLim_seQuad_three {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {P : Fin 4 → ℝ}
    (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)
    {x₀ x₁ x₂ : ℝ} (h₀ : M₀ ≤ x₀) (h₁ : M₀ ≤ x₁) (h₂ : M₀ ≤ x₂) (p : Fin 4 → ℝ)
    (α β : Fin 4) :
    seProdLim (seQuadA p α β) (seQuad p α β) m ![x₀, x₁, x₂] P =
      2 * ∫ y in Ioc (0 : ℝ) 1, seWt 2 y *
        (seQuadG₂ p α β P y * (seSimJ₂ (selfEnergyFeynmanMass m x₀ (Minkowski.dot P P) y)
            (selfEnergyFeynmanMass m x₁ (Minkowski.dot P P) y)
            (selfEnergyFeynmanMass m x₂ (Minkowski.dot P P) y) : ℂ) -
          seQuadG₁ p α β * (seSimJ₁ (selfEnergyFeynmanMass m x₀ (Minkowski.dot P P) y)
            (selfEnergyFeynmanMass m x₁ (Minkowski.dot P P) y)
            (selfEnergyFeynmanMass m x₂ (Minkowski.dot P P) y) : ℂ)) := by
  set s := Minkowski.dot P P
  have hMs : ∀ j, M₀ ≤ (![x₀, x₁, x₂] : Fin 3 → ℝ) j := by
    intro j; fin_cases j <;> simpa
  rw [seProdLim_seQuad_eq (j := 0) hM₀ hc₀ hP hMs (seQuadA p α β) p α β]
  simp only [zero_add, Nat.factorial_two, Nat.cast_ofNat]
  simp_rw [seQuadY_seQuadA_zero]
  congr 1
  -- Fubini on `Δ₂ × (0, 1]`
  have : IsFiniteMeasure ((volume : Measure (Fin 2 → ℝ)).restrict (simplexSet 2)) :=
    isFiniteMeasure_restrict.mpr (isCompact_simplexSet 2).measure_lt_top.ne
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hpos : ∀ u ∈ simplexSet 2, ∀ y ∈ Icc (0 : ℝ) 1,
      c₀ ≤ selfEnergyFeynmanMass m (mixMass ![x₀, x₁, x₂] u) s y := fun u hu y hy =>
    (hP y hy).trans (SetCRegDispSE.selfEnergyFeynmanMass_mono hM₀ (mixMass_ge hM₀ hMs hu) hy)
  set CQ : ℝ := ‖((energyConst 4 : ℝ) : ℂ) * exp (π * I * (-((7 / 2 : ℝ) : ℂ)))‖ *
    ((4 * ‖p‖ * seGs α β) * (1 + ‖P‖) ^ 2 * ‖((4 * π * seRadC 1 : ℝ) : ℂ)‖)
  have hG : ∀ y ∈ Icc (0 : ℝ) 1, ‖seQuadG₂ p α β P y‖ ≤ CQ := by
    intro y hy
    unfold seQuadG₂
    rw [norm_mul _ (seQuad p α β (-(y • P)) * _), norm_mul (seQuad p α β (-(y • P)))]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine mul_le_mul_of_nonneg_right ((norm_seQuad_le p α β _).trans ?_) (norm_nonneg _)
    have hCN : 0 ≤ 4 * ‖p‖ * seGs α β := by have := seGs_nonneg α β; positivity
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 2) hCN
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hy.1]
    have := mul_le_of_le_one_left (norm_nonneg P) hy.2
    linarith
  set F : (Fin 2 → ℝ) × ℝ → ℂ := fun q => seWt 2 q.2 *
    (seQuadG₂ p α β P q.2 *
        (((selfEnergyFeynmanMass m (mixMass ![x₀, x₁, x₂] q.1) s q.2 ^ 2)⁻¹ : ℝ) : ℂ) -
      seQuadG₁ p α β * (((selfEnergyFeynmanMass m (mixMass ![x₀, x₁, x₂] q.1) s q.2)⁻¹ : ℝ) :
        ℂ)) with hF
  have hmeas : Measurable F := by
    have h1 : Continuous fun y : ℝ => seQuadG₂ p α β P y := by
      unfold seQuadG₂
      have : Continuous fun y : ℝ => -(y • P) := (continuous_id.smul continuous_const).neg
      exact continuous_const.mul (((continuous_seQuad p α β).comp this).mul continuous_const)
    have h2 : Measurable fun q : (Fin 2 → ℝ) × ℝ =>
        selfEnergyFeynmanMass m (mixMass ![x₀, x₁, x₂] q.1) s q.2 := by
      unfold selfEnergyFeynmanMass
      have : Measurable fun q : (Fin 2 → ℝ) × ℝ => mixMass ![x₀, x₁, x₂] q.1 :=
        (continuous_mixMass ![x₀, x₁, x₂]).measurable.comp measurable_fst
      fun_prop
    exact ((SetCRegDispSE.continuous_seWt 2).measurable.comp measurable_snd).mul
      (((h1.measurable.comp measurable_snd).mul
        (Complex.measurable_ofReal.comp (h2.pow_const 2).inv)).sub
        (measurable_const.mul (Complex.measurable_ofReal.comp h2.inv)))
  have hint : Integrable F
      (((volume : Measure (Fin 2 → ℝ)).restrict (simplexSet 2)).prod
        ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))) := by
    refine (integrable_const ((2 + 1) * (CQ * (c₀ ^ 2)⁻¹ + ‖seQuadG₁ p α β‖ * c₀⁻¹))).mono'
      hmeas.aestronglyMeasurable ?_
    have h1 := (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure (Fin 2 → ℝ)).restrict (simplexSet 2))
      (ν := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))).ae
      (ae_restrict_mem (measurableSet_simplexSet 2))
    have h2 := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Fin 2 → ℝ)).restrict (simplexSet 2))
      (ν := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))).ae
      (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [h1, h2] with q hq1 hq2
    have hy := Ioc_subset_Icc_self hq2
    have hD := hpos q.1 hq1 q.2 hy
    set Δ := selfEnergyFeynmanMass m (mixMass ![x₀, x₁, x₂] q.1) s q.2
    have hDp : 0 < Δ := hc₀.trans_le hD
    have hW := SetCRegDispSE.seWt_norm_le (n := 2) hy
    push_cast at hW
    have hinv : Δ⁻¹ ≤ c₀⁻¹ := inv_anti₀ hc₀ hD
    have hinv2 : (Δ ^ 2)⁻¹ ≤ (c₀ ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hc₀.le hD 2)
    have hCQ : 0 ≤ CQ := (norm_nonneg _).trans (hG q.2 hy)
    simp only [hF]
    rw [norm_mul]
    refine mul_le_mul hW ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _)
      (by norm_num)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul (hG q.2 hy) hinv2 (by positivity) hCQ
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  have hyI := Ioc_subset_Icc_self hy
  set d₀ := selfEnergyFeynmanMass m x₀ s y
  set d₁ := selfEnergyFeynmanMass m x₁ s y
  set d₂ := selfEnergyFeynmanMass m x₂ s y
  have hd : ∀ x, M₀ ≤ x → 0 < selfEnergyFeynmanMass m x s y := fun x hx =>
    hc₀.trans_le ((hP y hyI).trans (SetCRegDispSE.selfEnergyFeynmanMass_mono hM₀ hx hyI))
  have hint1 : IntegrableOn (fun u => (simplexAff d₀ d₁ d₂ u ^ 2)⁻¹) (simplexSet 2) :=
    (ContinuousOn.inv₀ ((continuous_simplexAff d₀ d₁ d₂).pow 2).continuousOn
      fun u hu => (pow_pos (simplexAff_pos_of_mem (hd x₀ h₀) (hd x₁ h₁) (hd x₂ h₂) hu)
        2).ne').integrableOn_compact (isCompact_simplexSet 2)
  have hint2 : IntegrableOn (fun u => (simplexAff d₀ d₁ d₂ u)⁻¹) (simplexSet 2) := by
    refine ContinuousOn.integrableOn_compact (isCompact_simplexSet 2) ?_
    exact ContinuousOn.inv₀ (continuous_simplexAff d₀ d₁ d₂).continuousOn
      fun u hu => (simplexAff_pos_of_mem (hd x₀ h₀) (hd x₁ h₁) (hd x₂ h₂) hu).ne'
  have hcongr : ∀ u ∈ simplexSet 2, F (u, y) = seWt 2 y *
      (seQuadG₂ p α β P y * (((simplexAff d₀ d₁ d₂ u ^ 2)⁻¹ : ℝ) : ℂ) -
        seQuadG₁ p α β * (((simplexAff d₀ d₁ d₂ u)⁻¹ : ℝ) : ℂ)) := fun u hu => by
    simp only [hF]
    rw [selfEnergyFeynmanMass_mixMass_three m x₀ x₁ x₂ s y hu]
  rw [setIntegral_congr_fun (measurableSet_simplexSet 2) hcongr, integral_const_mul,
    integral_sub ((hint1.ofReal).const_mul _) ((hint2.ofReal).const_mul _),
    integral_const_mul, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  rfl

end QED.ChainProof.SetCRegDisp

end
