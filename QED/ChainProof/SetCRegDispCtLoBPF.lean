/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBPhoton
import QED.TwoLoop.VPHalfAtLimitPauli
public import QED.TwoLoop.VPUnitNestedOneLoop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The doubled vertex: partial fractions in the photon masses

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), first step of the
value of the doubled vertex (`QED/ChainProof/SetCRegDispCtLoBPhoton.lean`). For distinct photon
masses the limit `dblProdLimit` of the doubled vertex with `k + 2` photon denominators is a
combination of limits with `k + 1` denominators, and finally of the limits `dblOneLimit` with a
**single** photon denominator (power one; convergent, since the doubled vertex has four
denominators). So the value of the doubled vertex is reduced to that of
`N(ℓ)/(D_m(p'+ℓ) D_m(p+ℓ) D_m(ℓ_d) D_M(ℓ))` for one photon mass `M`; repeated masses follow by
continuity (`QED.ChainProof.CtLoB.tendsto_dblProdLimit`).

* `dblOneLimit`: `∫ spatialW (dblWt d 0) (0, 0, M)` (order one), the `ε → 0⁺` limit of the
  doubled vertex with one photon denominator (`tendsto_efi_dblOne`, `efInt_dblOne`);
* **`dblProdLimit_pf`**: `dblProdLimit (M₀, M₁, M₂, …) = (M₁² - M₀²)⁻¹ (dblProdLimit (M₀, M₂, …) -
  dblProdLimit (M₁, M₂, …))` for `M₀² ≠ M₁²`;
* **`dblProdLimit_two`**: `dblProdLimit (a, b) = (b² - a²)⁻¹ (dblOneLimit a - dblOneLimit b)`
  for `a² ≠ b²`.

All are proved at fixed common prescriptions by partial fractions of the integrand, and passed to
the limit by uniqueness of limits.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.Integration.Feynman
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested

/-- The limit of the doubled vertex with one photon denominator: `∫ spatialW (dblWt d 0)`, order
one, at `ε = η = 0`. -/
noncomputable def dblOneLimit (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (d : Fin 2)
    (p' p : Fin 4 → ℝ) : ℂ :=
  ∫ v, spatialW (dblWt d 0) α N m M 1 0 0 p' p v

/-! ### Partial fractions of the integrand -/

theorem denom_sub_denom (M M' η : ℝ) (ℓ : Fin 4 → ℝ) :
    denom M' η ℓ - denom M η ℓ = ((M' ^ 2 - M ^ 2 : ℝ) : ℂ) := by
  simp only [denom]
  push_cast
  ring

/-- `1/(D_a D_b) = (b² - a²)⁻¹ (1/D_a - 1/D_b)` at a common prescription. -/
theorem inv_denom_mul_inv_denom {a b η : ℝ} (hη : 0 < η) (hab : a ^ 2 ≠ b ^ 2)
    (ℓ : Fin 4 → ℝ) :
    (denom a η ℓ)⁻¹ * (denom b η ℓ)⁻¹ =
      ((b ^ 2 - a ^ 2 : ℝ) : ℂ)⁻¹ * ((denom a η ℓ)⁻¹ - (denom b η ℓ)⁻¹) := by
  have ha := denom_ne_zero_of_pos (M := a) hη ℓ
  have hb := denom_ne_zero_of_pos (M := b) hη ℓ
  have hc : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 (Ne.symm hab)
  have e := denom_sub_denom a b η ℓ
  field_simp
  rw [← e]

/-- **Partial fractions in the first two photon denominators.** -/
theorem dblProdIntegrand_pf (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms : Fin (k + 3) → ℝ)
    (hM : Ms 0 ^ 2 ≠ Ms 1 ^ 2) {η : ℝ} (hη : 0 < η) (ε : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) :
    dblProdIntegrand N m Ms (fun _ => η) ε d p' p ℓ =
      ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹ *
        (dblProdIntegrand N m (Fin.cons (Ms 0) (Fin.tail (Fin.tail Ms)) : Fin (k + 2) → ℝ)
            (fun _ => η) ε d p' p ℓ -
          dblProdIntegrand N m (Fin.tail Ms) (fun _ => η) ε d p' p ℓ) := by
  have key := inv_denom_mul_inv_denom hη hM ℓ
  simp only [dblProdIntegrand, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  set E := (denom m ε (p' + ℓ) * denom m ε (p + ℓ) * denom m ε (dblMom d p' p ℓ))⁻¹
  linear_combination (N ℓ * E * ((denom (Ms 2) η ℓ)⁻¹ *
    ∏ i : Fin k, (denom (Ms i.succ.succ.succ) η ℓ)⁻¹)) * key

/-- **Partial fractions with two photon denominators**: single photon denominators of power one. -/
theorem dblProdIntegrand_two (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (Ms : Fin 2 → ℝ)
    (hM : Ms 0 ^ 2 ≠ Ms 1 ^ 2) {η : ℝ} (hη : 0 < η) (ε : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) :
    dblProdIntegrand N m (k := 0) Ms (fun _ => η) ε d p' p ℓ =
      ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹ *
        (dblIntegrand N m (Ms 0) 0 ε η d p' p ℓ - dblIntegrand N m (Ms 1) 0 ε η d p' p ℓ) := by
  have key := inv_denom_mul_inv_denom hη hM ℓ
  simp only [dblProdIntegrand, dblIntegrand, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    Fin.succ_zero_eq_one, zero_add, pow_one]
  set E := denom m ε (p' + ℓ) * denom m ε (p + ℓ) * denom m ε (dblMom d p' p ℓ)
  rw [mul_inv E (denom (Ms 0) η ℓ), mul_inv E (denom (Ms 1) η ℓ)]
  linear_combination (N ℓ * E⁻¹) * key

/-! ### The doubled vertex with one photon denominator -/

section One

variable {m M₀ : ℝ} {p' p : Fin 4 → ℝ} {N : (Fin 4 → ℝ) → ℂ} {α : ℂ} {CN : ℝ}

theorem efInt_dblOne (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {M : ℝ} (hM : M₀ ≤ M) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) (d : Fin 2) :
    EFInt (dblIntegrand N m M 0 ε η d p' p) := by
  refine ⟨integrable_time_dblIntegrand hNc hNb m M 0 hε hη d p' p, ?_⟩
  obtain ⟨C, -, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb (n := 1) le_rfl
  have hb := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul (((0 : ℕ) + 1) * ((0 : ℕ) + 2) * ((0 : ℕ) + 3) * C)
  refine (Integrable.mono' hb (aestronglyMeasurable_spatialW (continuous_dblWt d 0) hNc α m M 1
    ε η p' p) (Eventually.of_forall fun v => ?_)).congr
    (Eventually.of_forall fun v => (integral_time_dblIntegrand hNc hNq hNb m M 0 hε hη d p' p
      v).symm)
  exact norm_spatialW_le (fun z hz => dblWt_norm_le d 0 hz)
    (fun z hz w => hC M hM _ z hz w) v

/-- The `ε, η → 0⁺` limit of the doubled vertex with one photon denominator. -/
theorem tendsto_efi_dblOne (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {M : ℝ} (hM : M₀ ≤ M) (d : Fin 2) :
    Tendsto (fun t : ℝ => energyFirstIntegral (dblIntegrand N m M 0 t t d p' p)) (𝓝[>] 0)
      (𝓝 (dblOneLimit α N m M d p' p)) :=
  tendsto_energyFirstIntegral_dblIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb 0 d tendsto_id
    tendsto_id tendsto_const_nhds (Eventually.of_forall fun _ => hM)

/-! ### Partial fractions of the limits -/

/-- **Partial fractions of the doubled limit in the first two photon masses.** -/
theorem dblProdLimit_pf (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k : ℕ} {Ms : Fin (k + 3) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hM : Ms 0 ^ 2 ≠ Ms 1 ^ 2) (d : Fin 2) :
    dblProdLimit α N m Ms d p' p = ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹ *
      (dblProdLimit α N m (Fin.cons (Ms 0) (Fin.tail (Fin.tail Ms)) : Fin (k + 2) → ℝ) d p' p -
        dblProdLimit α N m (Fin.tail Ms) d p' p) := by
  set M₁ : Fin (k + 2) → ℝ := Fin.cons (Ms 0) (Fin.tail (Fin.tail Ms))
  have hM₁ : ∀ j, M₀ ≤ M₁ j := fun j => Fin.cases (by simpa [M₁] using hMs 0)
    (fun i => by simpa [M₁, Fin.tail] using hMs i.succ.succ) j
  have hM₂ : ∀ j, M₀ ≤ Fin.tail Ms j := fun j => hMs j.succ
  have hes : ∀ j : Fin (k + 3), Tendsto (fun t : ℝ => (fun _ : Fin (k + 3) => t) j) (𝓝[>] 0)
      (𝓝[>] 0) := fun _ => tendsto_id
  have hes' : ∀ j : Fin (k + 2), Tendsto (fun t : ℝ => (fun _ : Fin (k + 2) => t) j) (𝓝[>] 0)
      (𝓝[>] 0) := fun _ => tendsto_id
  have L := tendsto_energyFirstIntegral_dblProdIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs
    d (ε := fun t : ℝ => t) (es := fun t : ℝ => fun _ => t) tendsto_id hes
  have L1 := tendsto_energyFirstIntegral_dblProdIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hM₁
    d (ε := fun t : ℝ => t) (es := fun t : ℝ => fun _ => t) tendsto_id hes'
  have L2 := tendsto_energyFirstIntegral_dblProdIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hM₂
    d (ε := fun t : ℝ => t) (es := fun t : ℝ => fun _ => t) tendsto_id hes'
  refine tendsto_nhds_unique L (((L1.sub L2).const_mul _).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have i1 : EFInt (dblProdIntegrand N m M₁ (fun _ => t) t d p' p) :=
    ⟨(energyFirstIntegral_dblProdIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hM₁
      (fun _ => ht) ht d).1,
     (energyFirstIntegral_dblProdIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hM₁
      (fun _ => ht) ht d).2.1⟩
  have i2 : EFInt (dblProdIntegrand N m (Fin.tail Ms) (fun _ => t) t d p' p) :=
    ⟨(energyFirstIntegral_dblProdIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hM₂
      (fun _ => ht) ht d).1,
     (energyFirstIntegral_dblProdIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hM₂
      (fun _ => ht) ht d).2.1⟩
  have e : dblProdIntegrand N m Ms (fun _ => t) t d p' p = fun ℓ =>
      ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹ * dblProdIntegrand N m M₁ (fun _ => t) t d p' p ℓ +
        (-((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹) *
          dblProdIntegrand N m (Fin.tail Ms) (fun _ => t) t d p' p ℓ := by
    funext ℓ
    rw [dblProdIntegrand_pf N m Ms hM ht t d p' p ℓ]
    ring
  rw [e, efi_add (i1.const_mul _) (i2.const_mul _), efi_const_mul, efi_const_mul]
  ring

/-- **The doubled limit with two photon denominators** in terms of single photon denominators. -/
theorem dblProdLimit_two (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {Ms : Fin 2 → ℝ} (hMs : ∀ j, M₀ ≤ Ms j)
    (hM : Ms 0 ^ 2 ≠ Ms 1 ^ 2) (d : Fin 2) :
    dblProdLimit α N m (k := 0) Ms d p' p = ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹ *
      (dblOneLimit α N m (Ms 0) d p' p - dblOneLimit α N m (Ms 1) d p' p) := by
  have hes : ∀ j : Fin 2, Tendsto (fun t : ℝ => (fun _ : Fin 2 => t) j) (𝓝[>] 0)
      (𝓝[>] 0) := fun _ => tendsto_id
  have L := tendsto_energyFirstIntegral_dblProdIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs
    d (k := 0) (ε := fun t : ℝ => t) (es := fun t : ℝ => fun _ => t) tendsto_id hes
  have L1 := tendsto_efi_dblOne hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (hMs 0) d
  have L2 := tendsto_efi_dblOne hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (hMs 1) d
  refine tendsto_nhds_unique L (((L1.sub L2).const_mul _).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have i1 := efInt_dblOne hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (hMs 0) ht ht d
  have i2 := efInt_dblOne hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (hMs 1) ht ht d
  have e : dblProdIntegrand N m (k := 0) Ms (fun _ => t) t d p' p = fun ℓ =>
      ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹ * dblIntegrand N m (Ms 0) 0 t t d p' p ℓ +
        (-((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹) * dblIntegrand N m (Ms 1) 0 t t d p' p ℓ := by
    funext ℓ
    rw [dblProdIntegrand_two N m Ms hM ht t d p' p ℓ]
    ring
  rw [e, efi_add (i1.const_mul _) (i2.const_mul _), efi_const_mul, efi_const_mul]
  ring

end One

end QED.ChainProof.CtLoB

end
