/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBUnd
import QED.TwoLoop.PauliZeroLimitCt
import QED.Algebra.Contraction
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The Pauli-projected undoubled chain with the identity on the doubled line

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), layer 5 of the
plan. On the doubled line `d` of the outer vertex, the undoubled part of the merged insertion at
`cbBParams` replaces the electron numerator `A_d` by the identity. The Pauli projection of the
resulting Feynman-gauge chain (`undChain`) is affine in the loop momentum: by
`γ^ρ (m - a̸) γ^μ γ_ρ = 2m γ^μ - 4 a^μ` (and the mirror identity), the chain is
`κ_e (2m γ^μ - 4 a^μ)`, `a` the momentum of the other open line. Its value at `ℓ = -K` is
`4 κ_e (1 - y) q² (4m² + q²)²`, and the engine limit for two photon denominators follows from
`QED.ChainProof.CtLoB.prodLimit_affN_two`.

* `undChain e m d p' p ℓ`: the Pauli numerator of `vertexChain e μ X Y g` with
  `(X, Y) = (A_out, 1)` for `d = 0` and `(1, A_in)` for `d = 1`;
* `contract_mass_sub_slash_gamma`, `contract_gamma_mass_sub_slash`: the two contractions;
* `undChain_eq_affN`: the chain is `affN (undC₀ e m d p' p) (undC e m p' p)`;
* `undChain_neg_shift`: its value at `-K`;
* **`prodLimit_undChain_two`**: `prodLimit 0 (undChain e m d p' p) m ![a, b] =
  ∫ 6 y (1-y) i (π²/6) 4 κ_e (1-y) q² (4m² + q²)² / (Δ_a Δ_b)`, for `q² > 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Matrix
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.Dirac QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.Bridge
open QED.TwoLoop.Insertion

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### Contractions -/

theorem gamma_eq_slash_single (μ : Fin 4) :
    gamma μ = slash (Minkowski.metric μ μ • Pi.single μ 1) := by
  fin_cases μ <;> simp [slash, Minkowski.lower_eq, Fin.sum_univ_four, Minkowski.metric]

theorem dot_metric_smul_single' (μ : Fin 4) (a : Fin 4 → ℝ) :
    Minkowski.dot (Minkowski.metric μ μ • Pi.single μ 1) a = a μ := by
  rw [Minkowski.dot_eq]
  fin_cases μ <;> simp [Minkowski.metric]

theorem sum_metric_smul_gamma_mul_mul' (A B : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    ∑ ν, ∑ ρ, ((Minkowski.metric ν ρ : ℝ) : ℂ) • (gamma ρ * A * gamma μ * B * gamma ν) =
      ∑ ρ, gamma ρ * A * gamma μ * B * gammaLower ρ := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [gammaLower, Finset.mul_sum, mul_smul_comm]
  exact Finset.sum_congr rfl fun ν _ => by rw [Minkowski.metric_symm]

/-- `γ^ρ (m - a̸) γ^μ γ_ρ = 2m γ^μ - 4 a^μ`. -/
theorem contract_mass_sub_slash_gamma (m : ℝ) (a : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ ρ, gamma ρ * ((m : ℂ) • 𝟙 - slash a) * gamma μ * gammaLower ρ =
      (2 * (m : ℂ)) • gamma μ - ((4 * a μ : ℝ) : ℂ) • 𝟙 := by
  have h : ∀ ρ, gamma ρ * ((m : ℂ) • 𝟙 - slash a) * gamma μ * gammaLower ρ =
      (m : ℂ) • (gamma ρ * gamma μ * gammaLower ρ) - gamma ρ * slash a * gamma μ * gammaLower ρ :=
    fun ρ => by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one]
  rw [Finset.sum_congr rfl fun ρ _ => h ρ, Finset.sum_sub_distrib, ← Finset.smul_sum,
    gamma_eq_slash_single μ, contract_slash, contract_slash_slash, Minkowski.dot_comm,
    dot_metric_smul_single']
  module

/-- `γ^ρ γ^μ (m - b̸) γ_ρ = 2m γ^μ - 4 b^μ`. -/
theorem contract_gamma_mass_sub_slash (m : ℝ) (b : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ ρ, gamma ρ * gamma μ * ((m : ℂ) • 𝟙 - slash b) * gammaLower ρ =
      (2 * (m : ℂ)) • gamma μ - ((4 * b μ : ℝ) : ℂ) • 𝟙 := by
  have h : ∀ ρ, gamma ρ * gamma μ * ((m : ℂ) • 𝟙 - slash b) * gammaLower ρ =
      (m : ℂ) • (gamma ρ * gamma μ * gammaLower ρ) - gamma ρ * gamma μ * slash b * gammaLower ρ :=
    fun ρ => by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one]
  rw [Finset.sum_congr rfl fun ρ _ => h ρ, Finset.sum_sub_distrib, ← Finset.smul_sum,
    gamma_eq_slash_single μ, contract_slash, contract_slash_slash, dot_metric_smul_single']
  module

/-! ### The chain -/

/-- The momentum of the open line that keeps its electron numerator. -/
def undMom (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) : Fin 4 → ℝ := if d = 0 then p' + ℓ else p + ℓ

/-- The Pauli-projected chain with the identity on the doubled line `d`. -/
noncomputable def undChain (e m : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  pauliNum m p' p fun μ => vertexChain e μ
    (if d = 0 then electronNumerator m (p' + ℓ) else 𝟙)
    (if d = 0 then 𝟙 else electronNumerator m (p + ℓ)) gPhoton

theorem vertexChain_und (e m : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) (μ : Fin 4) :
    vertexChain e μ (if d = 0 then electronNumerator m (p' + ℓ) else 𝟙)
        (if d = 0 then 𝟙 else electronNumerator m (p + ℓ)) gPhoton =
      kappa e • ((2 * (m : ℂ)) • gamma μ - ((4 * undMom d p' p ℓ μ : ℝ) : ℂ) • 𝟙) := by
  unfold vertexChain gPhoton
  rw [sum_metric_smul_gamma_mul_mul']
  congr 1
  by_cases hd : d = 0
  · simp only [hd, ite_true, undMom, Matrix.mul_one]
    exact contract_mass_sub_slash_gamma m (p' + ℓ) μ
  · simp only [hd, ite_false, undMom, Matrix.mul_one]
    exact contract_gamma_mass_sub_slash m (p + ℓ) μ

/-! ### The affine form -/

/-- The Pauli weight of the identity in the direction `μ`. -/
noncomputable def pauliOne (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) : ℂ :=
  ∑ i, ∑ j, pauliWt m p' p μ i j * (𝟙 : Matrix (Fin 4) (Fin 4) ℂ) i j

theorem undChain_eq (e m : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) :
    undChain e m d p' p ℓ = kappa e * (2 * (m : ℂ) * pauliNum m p' p (fun μ => gamma μ) -
      4 * ∑ μ, (undMom d p' p ℓ μ : ℂ) * pauliOne m p' p μ) := by
  unfold undChain
  simp only [vertexChain_und, pauliNum_eq_sum, pauliOne, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
  refine congrArg₂ (· - ·) ?_ ?_ <;>
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by push_cast; ring

/-- The constant term of the affine form. -/
noncomputable def undC₀ (e m : ℝ) (d : Fin 2) (p' p : Fin 4 → ℝ) : ℂ :=
  kappa e * (2 * (m : ℂ) * pauliNum m p' p (fun μ => gamma μ) -
    4 * ∑ μ, (undMom d p' p 0 μ : ℂ) * pauliOne m p' p μ)

/-- The linear coefficients of the affine form. -/
noncomputable def undC (e m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) : ℂ :=
  -4 * kappa e * pauliOne m p' p μ

theorem undMom_apply (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) (μ : Fin 4) :
    undMom d p' p ℓ μ = undMom d p' p 0 μ + ℓ μ := by
  unfold undMom
  split_ifs <;> simp

/-- **The chain is affine in the loop momentum.** -/
theorem undChain_eq_affN (e m : ℝ) (d : Fin 2) (p' p : Fin 4 → ℝ) :
    undChain e m d p' p = affN (undC₀ e m d p' p) (undC e m p' p) := by
  funext ℓ
  have hu : ∀ μ, (undMom d p' p ℓ μ : ℂ) = (undMom d p' p 0 μ : ℂ) + (ℓ μ : ℂ) := fun μ => by
    rw [undMom_apply d p' p ℓ μ]
    push_cast
    ring
  rw [undChain_eq, affN, undC₀]
  simp only [undC, hu, add_mul, Finset.sum_add_distrib]
  rw [show ∑ i, (ℓ i : ℂ) * (-4 * kappa e * pauliOne m p' p i) =
      -4 * kappa e * ∑ i, (ℓ i : ℂ) * pauliOne m p' p i by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring]
  ring

/-! ### The value at `-K` -/

/-- **The Pauli-projected undoubled chain at `-K`**: `4 κ_e (1 - y) q² (4m² + q²)²`. -/
theorem undChain_neg_shift (e : ℝ) {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (d : Fin 2) (z : ℝ × ℝ) :
    undChain e m d p' p (-shiftK p' p z) =
      4 * kappa e * ((1 - z.2 : ℝ) : ℂ) * ((Minkowski.dot (p' - p) (p' - p) : ℂ) *
        (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  set c' : ℂ := if d = 0 then ((1 + z.2 - 2 * z.2 * z.1 : ℝ) : ℂ) / 2
    else ((-1 + z.2 - 2 * z.2 * z.1 : ℝ) : ℂ) / 2
  have hv : ∀ μ, (undMom d p' p (-shiftK p' p z) μ : ℂ) =
      ((1 - z.2 : ℝ) : ℂ) / 2 * ((p' μ + p μ : ℝ) : ℂ) + c' * ((p' μ - p μ : ℝ) : ℂ) := by
    intro μ
    simp only [c', undMom, shiftK]
    split_ifs <;> simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] <;>
      push_cast <;> ring
  have hS : ∑ μ, (undMom d p' p (-shiftK p' p z) μ : ℂ) * pauliOne m p' p μ =
      pauliNum m p' p (fun μ => ((undMom d p' p (-shiftK p' p z) μ : ℝ) : ℂ) • 𝟙) := by
    rw [pauliNum_eq_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [pauliOne, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [undChain_eq, pauliNum_gamma hm hp' hp hq, hS,
    pauliNum_eq_of_sandwich (a := 0) (b := ((1 - z.2 : ℝ) : ℂ) / 2) (c := c') (d := 0)
      hm hp' hp hq]
  · field_simp
    ring
  · intro μ u w _ _
    rw [hv μ]
    simp

/-! ### The engine limit for two photon denominators -/

/-- **The undoubled vertex with the identity on the doubled line, two photon denominators.** -/
theorem prodLimit_undChain_two (e : ℝ) {m a b : ℝ} (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (d : Fin 2) :
    prodLimit 0 (undChain e m d p' p) m ![a, b] p' p =
      I * ((π ^ 2 / 6 : ℝ) : ℂ) * (4 * kappa e * ((Minkowski.dot (p' - p) (p' - p) : ℂ) *
        (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2)) *
      ∫ z, feynWt 1 z * ((1 - z.2 : ℝ) : ℂ) /
        ((feynmanMass m a z.1 z.2 p' p : ℂ) * (feynmanMass m b z.1 z.2 p' p : ℂ))
        ∂feynmanMeasure := by
  rw [undChain_eq_affN, prodLimit_affN_two hm ha hb hp' hp hp0' hp0, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [← undChain_eq_affN, undChain_neg_shift e hm.ne' hp' hp hq d z]
  ring

end QED.ChainProof.CtLoB

end
