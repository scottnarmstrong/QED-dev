/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.MassScalingBasic
public import QED.TwoLoop.CountertermScaling
public import QED.TwoLoop.WardIdentity
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Mass scaling of the frozen counterterm conditions

The counterterms `δᵢ` are dimensionless: the frozen conditions at masses `s m, s m_γ, s Λ, s M₁,
s M₂` (`s > 0`) are equivalent to the same conditions, with the same counterterms, at
`m, m_γ, Λ, M₁, M₂`.

* `isChargeNormalized_mul_iff`: the charge condition (K₀), for every charge `e`. The `γ^μ`
  coefficient `A₀` of the one-loop vertex at `q = 0` is invariant (`chargeA0_mul`).
* `isPhotonOnShell_massScale_iff`: the photon on-shell condition (Z₈). The loop coefficient
  `Π_loop(0) ∝ ∫ x (1 - x) ∑_f c_f log M_f²` is invariant because `∑_f c_f = 0`
  (`vacuumPolarizationLoop_massScale`).
* `isElectronOnShell_massScale_iff`: the electron on-shell conditions (Z₅). The self-energy
  coefficients satisfy `A_{sP}(s² t) = A_P(t)`, `B_{sP}(s² t) = B_P(t)`
  (`selfEnergyLoopA_massScale`), so the on-shell values `onShellδ₂`, `onShellδm` are invariant.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace QED.TwoLoop.MassScaling

open QED.WickModel QED.OneLoop QED.OneLoop.VertexLimit

/-! ### The charge condition (K₀) -/

theorem formIntegrandAq_mul {s : ℝ} (hs : s ≠ 0) (m mγ Λ : ℝ) (z : ℝ × ℝ) :
    formIntegrandAq (s * m) (s * mγ) (s * Λ) 0 z = formIntegrandAq m mγ Λ 0 z := by
  simp only [formIntegrandAq, massDq, mul_zero, add_zero, sub_zero]
  set X := (1 - z.2) * mγ ^ 2 + z.2 ^ 2 * m ^ 2
  set Y := (1 - z.2) * Λ ^ 2 + z.2 ^ 2 * m ^ 2
  have hX : (1 - z.2) * (s * mγ) ^ 2 + z.2 ^ 2 * (s * m) ^ 2 = s ^ 2 * X := by ring
  have hY : (1 - z.2) * (s * Λ) ^ 2 + z.2 ^ 2 * (s * m) ^ 2 = s ^ 2 * Y := by ring
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have h1 : s ^ 2 * (s ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hs2
  rw [hX, hY, mul_div_mul_left _ _ hs2, mul_inv, mul_inv]
  linear_combination (2 * z.2 * (1 / 2) * (X⁻¹ - Y⁻¹) *
    (2 * ((1 - 4 * (1 - z.2) + (1 - z.2) ^ 2) * m ^ 2))) * h1

theorem chargeA0_mul {s : ℝ} (hs : s ≠ 0) (e m mγ Λ : ℝ) :
    chargeA0 e (s * m) (s * mγ) (s * Λ) = chargeA0 e m mγ Λ := by
  simp only [chargeA0, formIntegrandAq_mul hs]

theorem chargeZ_mul {s : ℝ} (hs : s ≠ 0) (e m mγ Λ : ℝ) :
    chargeZ e (s * m) (s * mγ) (s * Λ) = chargeZ e m mγ Λ := by
  simp only [chargeZ, chargeA0_mul hs]

/-- **Mass scaling of the charge condition (K₀)**: for `s > 0` and every charge `e`, the
condition with `Z₁` at masses `(s m, s m_γ, s Λ)` is equivalent to the condition with the same
`Z₁` at `(m, m_γ, Λ)`. -/
theorem isChargeNormalized_mul_iff {e Z₁ m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {s : ℝ} (hs : 0 < s) (hm' : 0 < s * m) (hmγ' : 0 < s * mγ) (hΛ' : 0 < s * Λ) :
    IsChargeNormalized e Z₁ (s * m) (s * mγ) (s * Λ) hm' hmγ' hΛ' ↔
      IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ := by
  by_cases he : e = 0
  · subst he
    exact ⟨fun _ => QED.TwoLoop.Ward.isChargeNormalized_zero _ _ _ _ _ _ _,
      fun _ => QED.TwoLoop.Ward.isChargeNormalized_zero _ _ _ _ _ _ _⟩
  constructor
  · intro h
    have hZ := eq_chargeZ_of_isChargeNormalized he hm' hmγ' hΛ' h
    rw [chargeZ_mul hs.ne'] at hZ
    rw [hZ]
    exact isChargeNormalized_chargeZ hm hmγ hΛ
  · intro h
    have hZ := eq_chargeZ_of_isChargeNormalized he hm hmγ hΛ h
    rw [← chargeZ_mul hs.ne'] at hZ
    rw [hZ]
    exact isChargeNormalized_chargeZ hm' hmγ' hΛ'

/-! ### The photon condition (Z₈) -/

theorem mass_massScale (s : ℝ) (P : Params) (f : Fin 3) :
    (massScale s P).mass f = s * P.mass f := by
  fin_cases f <;> rfl

theorem loopCoeff_massScale (s : ℝ) (P : Params) : (massScale s P).loopCoeff = P.loopCoeff := rfl

/-- **The photon-condition coefficient `Π_loop(0)` is invariant** under the mass scaling, for
nonzero masses and `∑_f c_f = 0`. -/
theorem vacuumPolarizationLoop_massScale (P : Params) (hpos : ∀ f, P.mass f ≠ 0)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) {s : ℝ} (hs : s ≠ 0) :
    vacuumPolarizationLoop (massScale s P) 0 = vacuumPolarizationLoop P 0 := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hpt : ∀ x : ℝ, x * (1 - x) * ∑ f, (massScale s P).loopCoeff f *
      Real.log (vacuumPolarizationFeynmanMass ((massScale s P).mass f) 0 x) =
      x * (1 - x) * ∑ f, P.loopCoeff f *
        Real.log (vacuumPolarizationFeynmanMass (P.mass f) 0 x) := by
    intro x
    have hl : ∀ f, Real.log (vacuumPolarizationFeynmanMass ((massScale s P).mass f) 0 x) =
        Real.log (s ^ 2) + Real.log (vacuumPolarizationFeynmanMass (P.mass f) 0 x) := by
      intro f
      simp only [vacuumPolarizationFeynmanMass, mass_massScale, mul_zero, add_zero]
      rw [mul_pow, Real.log_mul hs2 (pow_ne_zero 2 (hpos f))]
    simp only [hl, loopCoeff_massScale, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    have hc : ∑ f, P.loopCoeff f = 0 := by
      simp only [Fin.sum_univ_three, Params.loopCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      linarith
    rw [hc]
    ring
  simp only [vacuumPolarizationLoop, massScale_e, hpt]

theorem mass_ne_zero {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (f : Fin 3) : P.mass f ≠ 0 := by
  fin_cases f
  · exact hm.ne'
  · exact (hm.trans hM₁).ne'
  · exact (hm.trans hM₂).ne'

/-- **Mass scaling of the photon on-shell condition (Z₈)**, with the same `δ₃`. -/
theorem isPhotonOnShell_massScale_iff (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {s : ℝ} (hs : 0 < s)
    (hm' : 0 < (massScale s P).m) (hM₁' : (massScale s P).m < (massScale s P).M₁)
    (hM₂' : (massScale s P).m < (massScale s P).M₂)
    (hPV₁' : 1 + (massScale s P).c₁ + (massScale s P).c₂ = 0)
    (hPV₂' : (massScale s P).m ^ 2 + (massScale s P).c₁ * (massScale s P).M₁ ^ 2 +
      (massScale s P).c₂ * (massScale s P).M₂ ^ 2 = 0) :
    IsPhotonOnShell (massScale s P) hm' hM₁' hM₂' hPV₁' hPV₂' ↔
      IsPhotonOnShell P hm hM₁ hM₂ hPV₁ hPV₂ := by
  rw [QED.TwoLoop.Scaling.isPhotonOnShell_iff, QED.TwoLoop.Scaling.isPhotonOnShell_iff,
    vacuumPolarizationLoop_massScale P (mass_ne_zero hm hM₁ hM₂) hPV₁ hs.ne', massScale_δ₃]

/-! ### The electron conditions (Z₅) -/

theorem selfEnergyFeynmanMass_mul (s m M t x : ℝ) :
    selfEnergyFeynmanMass (s * m) (s * M) (s ^ 2 * t) x =
      s ^ 2 * selfEnergyFeynmanMass m M t x := by
  unfold selfEnergyFeynmanMass
  ring

theorem selfEnergyLoopA_massScale (P : Params) {s : ℝ} (hs : s ≠ 0) (t : ℝ) :
    selfEnergyLoopA (massScale s P) (s ^ 2 * t) = selfEnergyLoopA P t := by
  simp only [selfEnergyLoopA, massScale_e, massScale_m, massScale_Λ, massScale_mγ,
    selfEnergyFeynmanMass_mul, mul_div_mul_left _ _ (pow_ne_zero 2 hs)]

theorem selfEnergyLoopB_massScale (P : Params) {s : ℝ} (hs : s ≠ 0) (t : ℝ) :
    selfEnergyLoopB (massScale s P) (s ^ 2 * t) = selfEnergyLoopB P t := by
  simp only [selfEnergyLoopB, massScale_e, massScale_m, massScale_Λ, massScale_mγ,
    selfEnergyFeynmanMass_mul, mul_div_mul_left _ _ (pow_ne_zero 2 hs)]

theorem re_selfEnergyLoopA_massScale (P : Params) {s : ℝ} (hs : s ≠ 0) :
    (fun t => (selfEnergyLoopA (massScale s P) t).re) =
      fun t => (selfEnergyLoopA P ((s ^ 2)⁻¹ * t)).re := by
  funext t
  rw [← selfEnergyLoopA_massScale P hs, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hs), one_mul]

theorem re_selfEnergyLoopB_massScale (P : Params) {s : ℝ} (hs : s ≠ 0) :
    (fun t => (selfEnergyLoopB (massScale s P) t).re) =
      fun t => (selfEnergyLoopB P ((s ^ 2)⁻¹ * t)).re := by
  funext t
  rw [← selfEnergyLoopB_massScale P hs, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hs), one_mul]

theorem onShell_point (s m : ℝ) (hs : s ≠ 0) : (s ^ 2)⁻¹ * -(s * m) ^ 2 = -m ^ 2 := by
  field_simp

theorem deriv_comp_inv_sq (g : ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) (m : ℝ) :
    deriv (fun t => g ((s ^ 2)⁻¹ * t)) (-(s * m) ^ 2) = (s ^ 2)⁻¹ * deriv g (-m ^ 2) := by
  have h := deriv_comp_mul_left ((s ^ 2)⁻¹) g (-(s * m) ^ 2)
  rw [onShell_point s m hs, smul_eq_mul] at h
  exact h

theorem neg_sq_mul (s m : ℝ) : -(s * m) ^ 2 = s ^ 2 * -m ^ 2 := by ring

theorem onShellδ₂_massScale (P : Params) {s : ℝ} (hs : s ≠ 0) :
    onShellδ₂ (massScale s P) = onShellδ₂ P := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  unfold onShellδ₂
  rw [re_selfEnergyLoopA_massScale P hs, re_selfEnergyLoopB_massScale P hs,
    massScale_m]
  have hA := deriv_comp_inv_sq (fun u => (selfEnergyLoopA P u).re) hs P.m
  have hB := deriv_comp_inv_sq (fun u => (selfEnergyLoopB P u).re) hs P.m
  rw [hA, hB, neg_sq_mul, selfEnergyLoopA_massScale P hs]
  field_simp

theorem onShellδm_massScale (P : Params) {s : ℝ} (hs : s ≠ 0) :
    onShellδm (massScale s P) = onShellδm P := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  unfold onShellδm
  rw [re_selfEnergyLoopA_massScale P hs, re_selfEnergyLoopB_massScale P hs,
    massScale_m]
  have hA := deriv_comp_inv_sq (fun u => (selfEnergyLoopA P u).re) hs P.m
  have hB := deriv_comp_inv_sq (fun u => (selfEnergyLoopB P u).re) hs P.m
  rw [hA, hB, neg_sq_mul, selfEnergyLoopB_massScale P hs]
  field_simp

/-- **Mass scaling of the electron on-shell conditions (Z₅)**, with the same `δ₂`, `δ_m`. -/
theorem isElectronOnShell_massScale_iff (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {s : ℝ} (hs : 0 < s) (hm' : 0 < (massScale s P).m)
    (hmγ' : 0 < (massScale s P).mγ) (hΛ' : 0 < (massScale s P).Λ) :
    IsElectronOnShell (massScale s P) hm' hmγ' hΛ' ↔ IsElectronOnShell P hm hmγ hΛ := by
  rw [QED.TwoLoop.Scaling.isElectronOnShell_iff, QED.TwoLoop.Scaling.isElectronOnShell_iff,
    onShellδ₂_massScale P hs.ne', onShellδm_massScale P hs.ne', massScale_δ₂, massScale_δm]

end QED.TwoLoop.MassScaling

end
