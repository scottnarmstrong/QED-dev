/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopMoments
public import QED.Integration.SymanzikIntegrability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The two-loop parametric representation with numerators of degree at most two

Extension of the scalar parametric representation `jointEnergyFirstIntegral_prod_inv_lineDenom`
(`QED/Integration/TwoLoopParametric.lean`) to numerators polynomial of degree at most two in the
loop momenta (obligations O2-10 and O2-11, `docs/TWO-LOOP-DERIVATION.md`, section 4.4). For
`N = m + 1 ≥ 6` propagators `Dᵢ = kᵢ·kᵢ + Mᵢ² - iε` (mostly-plus metric, `kᵢ = ∑ₛ αᵢₛ ℓₛ + pᵢ`)
and `P(ℓ) = c + ∑ L_{sμ} ℓₛ^μ + ∑ Q_{sμ,rν} ℓₛ^μ ℓᵣ^ν`:
`J[P] = -π⁴ ∫_Δ U⁻² ((N-5)! (V-iε)^{4-N} P(-S) + (N-6)!/2 (V-iε)^{5-N} ∑ Q_{sμ,rν} g^{μν} (A⁻¹)ₛᵣ)`,
with `S(z) = A⁻¹B` the loop-momentum shift of the completed square (energy part `τ`, spatial part
`σ`) and `g = diag(-1, 1, 1, 1)`. Equivalently: `ℓ` is replaced by `-S`, and each product
`ℓₛ^μ ℓᵣ^ν` gains the contraction `g^{μν} (A⁻¹)ₛᵣ (V - iε)/(2(N-5))` relative to the scalar
normalization `-π⁴ (N-5)! U⁻² (V - iε)^{4-N}`. In the mostly-minus metric `g' = -g` this is the rule
`ℓℓ → -g' (A⁻¹) Δ/(2(N-5))` of CK-R rule 6 and AKN (64)–(65), with `Δ = V - iε`.

## Hypotheses

* `N ≥ 6` (`5 ≤ m`): after the energy integral, the spatial integrals `∫ y y (yᵀAy + w)^{1-N}` and
  `∫ (yᵀAy + w)^{2-N}` over `ℝ⁶` need `N - 1 ≥ 5` and `N - 2 ≥ 4`. For a quadratic numerator this
  is overall power counting: `8 + 2 - 2N < 0`.
* Two of the `αᵢ` are linearly independent, and `U⁻²` is integrable on the simplex, as in the
  scalar case.
* `tr A · U⁻³ = tr(A⁻¹) U⁻²` is integrable on the simplex. The numerator raises the degree of the
  one-loop subintegrations; this is their absolute convergence after the energy integral (the
  absolute spatial integral of `|y|² |w|^{1-N}` is `≍ tr(A⁻¹) U^{-3/2}`). It fails for graphs with
  a one-loop subgraph of three lines (the five-line sunset), where a quadratic numerator in that
  loop momentum diverges logarithmically. Power counting suggests that it holds when every one-loop
  subgraph has at least four lines counted with multiplicity (as with Pauli–Villars-combined photon
  lines); that criterion is not proved here. For affine
  numerators it is stronger than necessary (`tr(A⁻¹)^{1/2} U⁻²` and `N ≥ 5` would do).

The shifts `τ`, `σ` are bounded on the simplex (`exists_abs_mulVec_coefVec_le`), by the
Cauchy–Binet form `2U = ∑ᵢⱼ zᵢ zⱼ det(αᵢ, αⱼ)²` of `U`.

## Main statements

* `LoopQuadratic`, `LoopQuadratic.eval`, `LoopQuadratic.contract`: numerators of degree at most
  two and the contraction `∑ Q_{sμ,rν} g^{μν} (A⁻¹)ₛᵣ`.
* `integral_loopQuadratic_mul_prod_lineDenom_eq` (sub-step (a)): the energy integral at fixed
  spatial momenta.
* `jointEnergyFirstIntegral_loopQuadratic_mul_prod_inv_lineDenom`: the full representation, with
  the integrability of both stages.
* `jointEnergyFirstIntegral_mul_prod_inv_lineDenom_degree_one`,
  `jointEnergyFirstIntegral_mul_prod_inv_lineDenom_degree_two`: the monomials `ℓₛ^μ` and
  `ℓₛ^μ ℓᵣ^ν`.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix Filter Function
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint simplexComb)
open QED.Integration.Spatial (quadForm)

/-! ### Numerators of degree at most two -/

/-- A polynomial of degree at most two in the two loop momenta `ℓ₁, ℓ₂ ∈ ℝ⁴`,
`P(ℓ) = c + ∑ L_{sμ} ℓₛ^μ + ∑ Q_{sμ,rν} ℓₛ^μ ℓᵣ^ν`, with complex coefficients. -/
structure LoopQuadratic where
  /-- The constant term `c`. -/
  const : ℂ
  /-- The linear coefficients `L_{sμ}`. -/
  lin : Fin 2 → Fin 4 → ℂ
  /-- The quadratic coefficients `Q_{sμ,rν}`. -/
  quad : Fin 2 → Fin 4 → Fin 2 → Fin 4 → ℂ

namespace LoopQuadratic

/-- The value `P(ℓ)`. -/
def eval (P : LoopQuadratic) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  P.const + ∑ s, ∑ μ, P.lin s μ * ((ℓ s μ : ℝ) : ℂ) +
    ∑ s, ∑ μ, ∑ r, ∑ ν, P.quad s μ r ν * ((ℓ s μ * ℓ r ν : ℝ) : ℂ)

/-- The quadratic part `∑ Q_{sμ,rν} δₛ^μ δᵣ^ν`. -/
def quadPart (P : LoopQuadratic) (δ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ s, ∑ μ, ∑ r, ∑ ν, P.quad s μ r ν * ((δ s μ * δ r ν : ℝ) : ℂ)

/-- The contraction `∑ Q_{sμ,rν} g^{μν} (A⁻¹)ₛᵣ`, with `g = diag(-1, 1, 1, 1)`. -/
noncomputable def contract (P : LoopQuadratic) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ∑ s, ∑ μ, ∑ r, ∑ ν, P.quad s μ r ν * ((Minkowski.metric μ ν : ℝ) : ℂ) * ((A⁻¹ s r : ℝ) : ℂ)

/-- The energy contraction `∑ₛᵣ Q_{s0,r0} (A⁻¹)ₛᵣ`. -/
noncomputable def energyContract (P : LoopQuadratic) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ∑ s, ∑ r, P.quad s 0 r 0 * ((A⁻¹ s r : ℝ) : ℂ)

/-- The spatial contraction `∑ₛᵣ ∑_c Q_{sc,rc} (A⁻¹)ₛᵣ`. -/
noncomputable def spatialContract (P : LoopQuadratic) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ∑ s, ∑ c : Fin 3, ∑ r, P.quad s c.succ r c.succ * ((A⁻¹ s r : ℝ) : ℂ)

/-- The sum of the norms of the coefficients. -/
noncomputable def coeffBound (P : LoopQuadratic) : ℝ :=
  ‖P.const‖ + ∑ s, ∑ μ, ‖P.lin s μ‖ + ∑ s, ∑ μ, ∑ r, ∑ ν, ‖P.quad s μ r ν‖

theorem contract_eq (P : LoopQuadratic) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    P.contract A = -P.energyContract A + P.spatialContract A := by
  simp only [contract, energyContract, spatialContract, Fin.sum_univ_two, Fin.sum_univ_four,
    Fin.sum_univ_three, Minkowski.metric]
  norm_num
  ring

theorem eval_add_add_eval_sub (P : LoopQuadratic) (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    P.eval (ℓ + δ) + P.eval (ℓ - δ) = 2 * (P.eval ℓ + P.quadPart δ) := by
  simp only [eval, quadPart, Pi.add_apply, Pi.sub_apply]
  have e1 : ∑ s, ∑ μ, P.lin s μ * ((ℓ s μ + δ s μ : ℝ) : ℂ) +
      ∑ s, ∑ μ, P.lin s μ * ((ℓ s μ - δ s μ : ℝ) : ℂ) =
      2 * ∑ s, ∑ μ, P.lin s μ * ((ℓ s μ : ℝ) : ℂ) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    push_cast
    ring
  have e2 : ∑ s, ∑ μ, ∑ r, ∑ ν, P.quad s μ r ν *
        (((ℓ s μ + δ s μ) * (ℓ r ν + δ r ν) : ℝ) : ℂ) +
      ∑ s, ∑ μ, ∑ r, ∑ ν, P.quad s μ r ν * (((ℓ s μ - δ s μ) * (ℓ r ν - δ r ν) : ℝ) : ℂ) =
      2 * ∑ s, ∑ μ, ∑ r, ∑ ν, P.quad s μ r ν * ((ℓ s μ * ℓ r ν : ℝ) : ℂ) +
        2 * ∑ s, ∑ μ, ∑ r, ∑ ν, P.quad s μ r ν * ((δ s μ * δ r ν : ℝ) : ℂ) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun ν _ => ?_
    push_cast
    ring
  linear_combination e1 + e2

theorem norm_eval_le (P : LoopQuadratic) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ‖P.eval ℓ‖ ≤ P.coeffBound * (1 + ∑ s, ∑ μ, ℓ s μ ^ 2) := by
  set S := ∑ s, ∑ μ, ℓ s μ ^ 2 with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun μ _ => sq_nonneg _
  have hle : ∀ s μ, ℓ s μ ^ 2 ≤ S := fun s μ =>
    (Finset.single_le_sum (fun μ _ => sq_nonneg (ℓ s μ)) (Finset.mem_univ μ)).trans
      (Finset.single_le_sum (f := fun s => ∑ μ, ℓ s μ ^ 2)
        (fun s _ => Finset.sum_nonneg fun μ _ => sq_nonneg (ℓ s μ)) (Finset.mem_univ s))
  have h1 : ∀ s μ, ‖((ℓ s μ : ℝ) : ℂ)‖ ≤ 1 + S := fun s μ => by
    rw [norm_real, Real.norm_eq_abs]
    nlinarith [hle s μ, abs_nonneg (ℓ s μ), sq_abs (ℓ s μ), sq_nonneg (|ℓ s μ| - 1)]
  have h2 : ∀ s μ r ν, ‖((ℓ s μ * ℓ r ν : ℝ) : ℂ)‖ ≤ 1 + S := fun s μ r ν => by
    rw [norm_real, Real.norm_eq_abs, abs_mul]
    nlinarith [hle s μ, hle r ν, abs_nonneg (ℓ s μ), abs_nonneg (ℓ r ν), sq_abs (ℓ s μ),
      sq_abs (ℓ r ν), sq_nonneg (|ℓ s μ| - |ℓ r ν|)]
  have hL : ‖∑ s, ∑ μ, P.lin s μ * ((ℓ s μ : ℝ) : ℂ)‖ ≤ (∑ s, ∑ μ, ‖P.lin s μ‖) * (1 + S) := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h1 s μ) (norm_nonneg _)
  have hQ : ‖∑ s, ∑ μ, ∑ r, ∑ ν, P.quad s μ r ν * ((ℓ s μ * ℓ r ν : ℝ) : ℂ)‖ ≤
      (∑ s, ∑ μ, ∑ r, ∑ ν, ‖P.quad s μ r ν‖) * (1 + S) := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h2 s μ r ν) (norm_nonneg _)
  have hc : ‖P.const‖ ≤ ‖P.const‖ * (1 + S) := le_mul_of_one_le_right (norm_nonneg _) (by linarith)
  unfold eval coeffBound
  calc ‖P.const + ∑ s, ∑ μ, P.lin s μ * ((ℓ s μ : ℝ) : ℂ) +
        ∑ s, ∑ μ, ∑ r, ∑ ν, P.quad s μ r ν * ((ℓ s μ * ℓ r ν : ℝ) : ℂ)‖
      ≤ ‖P.const‖ + ‖∑ s, ∑ μ, P.lin s μ * ((ℓ s μ : ℝ) : ℂ)‖ +
        ‖∑ s, ∑ μ, ∑ r, ∑ ν, P.quad s μ r ν * ((ℓ s μ * ℓ r ν : ℝ) : ℂ)‖ := norm_add₃_le
    _ ≤ ‖P.const‖ * (1 + S) + (∑ s, ∑ μ, ‖P.lin s μ‖) * (1 + S) +
        (∑ s, ∑ μ, ∑ r, ∑ ν, ‖P.quad s μ r ν‖) * (1 + S) := by gcongr
    _ = _ := by ring

theorem coeffBound_nonneg (P : LoopQuadratic) : 0 ≤ P.coeffBound := by
  unfold coeffBound
  positivity

theorem continuous_eval (P : LoopQuadratic) : Continuous P.eval := by
  unfold eval
  fun_prop

end LoopQuadratic

/-! ### The loop momenta -/

theorem loopMomenta_add (t t' : Fin 2 → ℝ) (v v' : Fin 2 → Fin 3 → ℝ) :
    loopMomenta (t + t') (v + v') = loopMomenta t v + loopMomenta t' v' := by
  funext s μ
  refine Fin.cases ?_ (fun c => ?_) μ <;> simp [loopMomenta]

theorem loopMomenta_sub (t t' : Fin 2 → ℝ) (v v' : Fin 2 → Fin 3 → ℝ) :
    loopMomenta (t - t') (v - v') = loopMomenta t v - loopMomenta t' v' := by
  funext s μ
  refine Fin.cases ?_ (fun c => ?_) μ <;> simp [loopMomenta]

theorem loopMomenta_neg (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    loopMomenta (-t) (-v) = -loopMomenta t v := by
  funext s μ
  refine Fin.cases ?_ (fun c => ?_) μ <;> simp [loopMomenta]

theorem sum_sq_loopMomenta (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    ∑ s, ∑ μ, loopMomenta t v s μ ^ 2 = ∑ s, t s ^ 2 + ∑ s, ∑ c, v s c ^ 2 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fin.sum_univ_succ]
  simp [loopMomenta]

theorem continuous_loopMomenta :
    Continuous fun q : (Fin 2 → ℝ) × (Fin 2 → Fin 3 → ℝ) => loopMomenta q.1 q.2 := by
  refine continuous_pi fun s => continuous_pi fun μ => ?_
  refine Fin.cases ?_ (fun c => ?_) μ
  · simp only [loopMomenta, Fin.cons_zero]
    fun_prop
  · simp only [loopMomenta, Fin.cons_succ]
    fun_prop

theorem quadPart_loopMomenta_energy (P : LoopQuadratic) (u : Fin 2 → ℝ) :
    P.quadPart (loopMomenta u 0) = ∑ s, ∑ r, P.quad s 0 r 0 * ((u s * u r : ℝ) : ℂ) := by
  simp only [LoopQuadratic.quadPart, Fin.sum_univ_succ (n := 3), loopMomenta, Fin.cons_zero,
    Fin.cons_succ, Pi.zero_apply, mul_zero, zero_mul, ofReal_zero, Finset.sum_const_zero,
    add_zero]

theorem quadPart_loopMomenta_spatial (P : LoopQuadratic) (y : Fin 2 → Fin 3 → ℝ) :
    P.quadPart (loopMomenta 0 y) =
      ∑ s, ∑ c : Fin 3, ∑ r, ∑ d : Fin 3, P.quad s c.succ r d.succ * ((y s c * y r d : ℝ) : ℂ) := by
  simp only [LoopQuadratic.quadPart, Fin.sum_univ_succ (n := 3), loopMomenta, Fin.cons_zero,
    Fin.cons_succ, Pi.zero_apply, mul_zero, zero_mul, ofReal_zero, Finset.sum_const_zero,
    zero_add]

/-- The loop-momentum shift `S(z) = A⁻¹ B` of the completed square: energy part `τ`, spatial
part `σ`. -/
noncomputable def loopShift {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) : Fin 2 → Fin 4 → ℝ :=
  loopMomenta (energyShift α p z) (spatialShift α p z)

/-! ### The shifts are bounded on the simplex -/

section Shift

variable {m : ℕ}

theorem adjugate_mulVec_coefVec_eq (α : Fin (m + 1) → Fin 2 → ℝ) (z q : Fin (m + 1) → ℝ)
    (s : Fin 2) : ∃ κ : Fin (m + 1) → ℝ, (∀ j, |κ j| ≤ |α j 0| + |α j 1|) ∧
      ((symanzikMatrix α z).adjugate *ᵥ coefVec α z q) s =
        ∑ i, ∑ j, z i * z j * q i * (κ j * pairDet α i j) := by
  rw [adjugate_fin_two]
  fin_cases s
  · refine ⟨fun j => α j 1, fun j => by linarith [abs_nonneg (α j 0)], ?_⟩
    simp only [Fin.zero_eta, mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val',
      cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, symanzikMatrix, coefVec,
      pairDet]
    rw [show (∑ i, z i * α i 1 * α i 1) * ∑ i, z i * α i 0 * q i +
        -(∑ i, z i * α i 0 * α i 1) * ∑ i, z i * α i 1 * q i =
        (∑ i, z i * α i 0 * q i) * (∑ j, z j * α j 1 * α j 1) -
          (∑ i, z i * α i 1 * q i) * (∑ j, z j * α j 0 * α j 1) by ring,
      Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · refine ⟨fun j => -α j 0, fun j => by rw [abs_neg]; linarith [abs_nonneg (α j 1)], ?_⟩
    simp only [Fin.mk_one, mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val',
      cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, symanzikMatrix, coefVec,
      pairDet]
    rw [show -(∑ i, z i * α i 1 * α i 0) * ∑ i, z i * α i 0 * q i +
        (∑ i, z i * α i 0 * α i 0) * ∑ i, z i * α i 1 * q i =
        (∑ i, z i * α i 1 * q i) * (∑ j, z j * α j 0 * α j 0) -
          (∑ i, z i * α i 0 * q i) * (∑ j, z j * α j 1 * α j 0) by ring,
      Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- **The shift `A⁻¹ β` is bounded** for nonnegative Feynman parameters with `U ≠ 0`: by
Cauchy–Binet, `|adj(A) β| ≤ C ∑ᵢⱼ zᵢ zⱼ det(αᵢ, αⱼ)² = 2 C U`. -/
theorem exists_abs_mulVec_coefVec_le (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → ℝ) :
    ∃ C, ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → symanzikU α z ≠ 0 → ∀ s,
      |((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q) s| ≤ C := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_pairDet_sq α
  set Kq := ∑ i, |q i|
  set Kα := ∑ j, (|α j 0| + |α j 1|)
  refine ⟨2 * (Kq * Kα / Real.sqrt c), fun z hz hU s => ?_⟩
  have hUpos : 0 < symanzikU α z := lt_of_le_of_ne (symanzikU_nonneg α hz) (Ne.symm hU)
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hqle : ∀ i, |q i| ≤ Kq := fun i =>
    Finset.single_le_sum (f := fun i => |q i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  obtain ⟨κ, hκ, hadjeq⟩ := adjugate_mulVec_coefVec_eq α z q s
  have hαle : ∀ j, |κ j| ≤ Kα := fun j =>
    (hκ j).trans (Finset.single_le_sum (f := fun j => |α j 0| + |α j 1|)
      (fun j _ => by positivity) (Finset.mem_univ j))
  have hpd : ∀ i j, |pairDet α i j| ≤ pairDet α i j ^ 2 / Real.sqrt c := fun i j => by
    rw [le_div_iff₀ hsc]
    by_cases h : pairDet α i j = 0
    · simp [h]
    · have h1 : Real.sqrt c ≤ |pairDet α i j| := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (hc i j h)
      calc |pairDet α i j| * Real.sqrt c ≤ |pairDet α i j| * |pairDet α i j| :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = pairDet α i j ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
  have hadj : |((symanzikMatrix α z).adjugate *ᵥ coefVec α z q) s| ≤
      Kq * Kα / Real.sqrt c * (2 * symanzikU α z) := by
    rw [hadjeq, two_mul_symanzikU, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    simp only [abs_mul, abs_of_nonneg (hz i), abs_of_nonneg (hz j)]
    have hzij : 0 ≤ z i * z j := mul_nonneg (hz i) (hz j)
    have e1 : |q i| * (|κ j| * |pairDet α i j|) ≤
        Kq * (Kα * (pairDet α i j ^ 2 / Real.sqrt c)) :=
      mul_le_mul (hqle i) (mul_le_mul (hαle j) (hpd i j) (abs_nonneg _)
        ((abs_nonneg _).trans (hαle j))) (by positivity) ((abs_nonneg _).trans (hqle i))
    calc z i * z j * |q i| * (|κ j| * |pairDet α i j|)
        = z i * z j * (|q i| * (|κ j| * |pairDet α i j|)) := by ring
      _ ≤ z i * z j * (Kq * (Kα * (pairDet α i j ^ 2 / Real.sqrt c))) :=
          mul_le_mul_of_nonneg_left e1 hzij
      _ = Kq * Kα / Real.sqrt c * (z i * z j * pairDet α i j ^ 2) := by ring
  have hinv : (symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q =
      (symanzikU α z)⁻¹ • ((symanzikMatrix α z).adjugate *ᵥ coefVec α z q) := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_mulVec]
    rfl
  rw [hinv, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hUpos]
  calc (symanzikU α z)⁻¹ * |((symanzikMatrix α z).adjugate *ᵥ coefVec α z q) s|
      ≤ (symanzikU α z)⁻¹ * (Kq * Kα / Real.sqrt c * (2 * symanzikU α z)) := by gcongr
    _ = 2 * (Kq * Kα / Real.sqrt c) := by field_simp

theorem exists_sum_sq_energyShift_le (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) :
    ∃ K, ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → symanzikU α z ≠ 0 →
      ∑ s, energyShift α p z s ^ 2 ≤ K := by
  obtain ⟨C, hC⟩ := exists_abs_mulVec_coefVec_le α (fun i => p i 0)
  refine ⟨2 * C ^ 2, fun z hz hU => ?_⟩
  have h : ∀ s, energyShift α p z s ^ 2 ≤ C ^ 2 := fun s => by
    have := hC z hz hU s
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [Fin.sum_univ_two]
  linarith [h 0, h 1]

theorem exists_sum_sq_spatialShift_le (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) :
    ∃ K, ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → symanzikU α z ≠ 0 →
      ∑ s, ∑ c, spatialShift α p z s c ^ 2 ≤ K := by
  choose C hC using fun c : Fin 3 => exists_abs_mulVec_coefVec_le α (fun i => p i c.succ)
  refine ⟨∑ s : Fin 2, ∑ c, C c ^ 2, fun z hz hU => ?_⟩
  refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun c _ => ?_
  have := hC c z hz hU s
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

theorem trace_symanzikMatrix_le (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) :
    (symanzikMatrix α z).trace ≤ ∑ i, (α i 0 ^ 2 + α i 1 ^ 2) := by
  have hzle : ∀ i, z i ≤ 1 := fun i => by
    rw [← hz1]
    exact Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i)
  rw [trace_fin_two]
  simp only [symanzikMatrix, of_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [hz i, hzle i, sq_nonneg (α i 0), sq_nonneg (α i 1)]

/-- `|(A⁻¹)ₛᵣ| ≤ tr A / det A` for positive definite `2 × 2` matrices. -/
theorem abs_inv_apply_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (s r : Fin 2) :
    |A⁻¹ s r| ≤ A.trace / A.det := by
  have hdet := hA.det_pos
  have h0 : 0 < A 0 0 := hA.diag_pos
  have h1 : 0 < A 1 1 := hA.diag_pos
  have hsym : A 1 0 = A 0 1 := by simpa using hA.isHermitian.apply 0 1
  have hb : |A 0 1| ≤ A 0 0 + A 1 1 := by
    have : A 0 1 ^ 2 < A 0 0 * A 1 1 := by rw [det_fin_two, hsym] at hdet; linarith
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (A 0 0 - A 1 1), sq_nonneg (A 0 1 + A 0 0 + A 1 1),
      sq_nonneg (A 0 1 - A 0 0 - A 1 1)]
  rw [Matrix.inv_def, Ring.inverse_eq_inv', adjugate_fin_two, trace_fin_two]
  rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hdet, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hdet.le)
  fin_cases s <;> fin_cases r <;> simp [abs_of_pos h0, abs_of_pos h1, hsym] <;> linarith

end Shift

/-! ### The parametrized functions with a numerator -/

section Numerator

variable {m : ℕ} (P : LoopQuadratic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- The energy-integrated parametrized integrand of the second energy moment,
`π/(2 N' (N'-1)) U^{-1/2} w^{2-N}`, `N' = N - 1 = m`. -/
noncomputable def energyValueTwo (ε : ℝ) (x : Fin m → ℝ) (v : Fin 2 → Fin 3 → ℝ) : ℂ :=
  π / (2 * ((m : ℂ) * ((m : ℂ) - 1))) * ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
    (shiftedConst α p M ε x v ^ (m - 1))⁻¹

/-- The energy-integrated parametrized integrand with the numerator `P`:
`P(-τ, v) · (-(π/(N-1)) U^{-1/2} w^{1-N}) + (∑ Q_{s0,r0} (A⁻¹)ₛᵣ) · π/(2(N-1)(N-2)) U^{-1/2} w^{2-N}`. -/
noncomputable def numEnergyValue (ε : ℝ) (x : Fin m → ℝ) (v : Fin 2 → Fin 3 → ℝ) : ℂ :=
  P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) * energyValue α p M ε x v +
    P.energyContract (symanzikMatrix α (simplexPoint x)) * energyValueTwo α p M ε x v

theorem measurable_energyShift :
    Measurable fun z : Fin (m + 1) → ℝ => energyShift α p z := by
  refine measurable_pi_iff.mpr fun s => ?_
  simp only [energyShift, mulVec, dotProduct, coefVec]
  exact Finset.measurable_sum _ fun r _ =>
    (measurable_symanzikMatrix_inv α).eval_matrix.mul (by fun_prop)

theorem measurable_energyValueTwo (hε : ε ≠ 0) :
    Measurable fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) => energyValueTwo α p M ε q.1 q.2 := by
  have hZ := (continuous_simplexPoint' (m := m)).measurable
  have hA : Measurable fun x : Fin m → ℝ => symanzikMatrix α (simplexPoint x) :=
    (continuous_symanzikMatrix α).measurable.comp hZ
  have hσ := (measurable_spatialShift α p).comp hZ
  have hV := (measurable_symanzikV α p M).comp hZ
  have hΨ := (continuous_quadForm_inv (m := m - 1) hε).measurable.comp
    ((hA.comp measurable_fst).prodMk (((measurable_snd).add (hσ.comp measurable_fst)).prodMk
      (hV.comp measurable_fst)))
  have hU : Measurable fun x : Fin m → ℝ =>
      ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ :=
    (continuous_ofReal.comp (continuous_symanzikU_simplexPoint α).sqrt).measurable.inv
  exact (measurable_const.mul (hU.comp measurable_fst)).mul hΨ

theorem measurable_energyContract :
    Measurable fun x : Fin m → ℝ => P.energyContract (symanzikMatrix α (simplexPoint x)) := by
  have hZ := (continuous_simplexPoint' (m := m)).measurable
  have hinv := (measurable_symanzikMatrix_inv α).comp hZ
  unfold LoopQuadratic.energyContract
  exact Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun r _ =>
    measurable_const.mul (Complex.measurable_ofReal.comp hinv.eval_matrix)

theorem measurable_eval_loopMomenta :
    Measurable fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      P.eval (loopMomenta (-energyShift α p (simplexPoint q.1)) q.2) := by
  have hZ := (continuous_simplexPoint' (m := m)).measurable
  have hτ := (measurable_energyShift α p).comp hZ
  exact P.continuous_eval.measurable.comp (continuous_loopMomenta.measurable.comp
    ((hτ.neg.comp measurable_fst).prodMk measurable_snd))

end Numerator

/-! ### Integrability on the simplex -/

theorem inv_mul_inv_sqrt_le (r : ℝ) : r⁻¹ * (Real.sqrt r)⁻¹ ≤ 1 + (r ^ 2)⁻¹ := by
  rcases le_or_gt r 0 with h | h
  · rw [Real.sqrt_eq_zero'.mpr h, _root_.inv_zero, mul_zero]
    positivity
  rcases le_or_gt r 1 with h1 | h1
  · have hs : r ≤ Real.sqrt r := by
      rw [Real.le_sqrt h.le h.le]
      nlinarith
    have : r⁻¹ * (Real.sqrt r)⁻¹ ≤ r⁻¹ * r⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ h hs) (inv_nonneg.mpr h.le)
    have h2 : r⁻¹ * r⁻¹ = (r ^ 2)⁻¹ := by rw [sq, mul_inv]
    linarith
  · have hs : 1 ≤ Real.sqrt r := by rw [Real.one_le_sqrt]; exact h1.le
    have : r⁻¹ * (Real.sqrt r)⁻¹ ≤ 1 := by
      have a1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1.le
      have a2 : (Real.sqrt r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
      have a3 : 0 ≤ (Real.sqrt r)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      nlinarith
    have : 0 ≤ (r ^ 2)⁻¹ := by positivity
    linarith

theorem integrableOn_inv_mul_inv_sqrt_symanzikU {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m)) :
    IntegrableOn (fun x => (symanzikU α (simplexPoint x))⁻¹ *
      (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹) (simplexSet m) := by
  have : IsFiniteMeasure (volume.restrict (simplexSet m)) :=
    isFiniteMeasure_restrict.mpr (Feynman.isCompact_simplexSet m).measure_lt_top.ne
  refine ((integrable_const (1 : ℝ)).add hU).mono'
    (((continuous_symanzikU_simplexPoint α).measurable.inv).mul
      (continuous_symanzikU_simplexPoint α).sqrt.measurable.inv).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hnn : 0 ≤ (symanzikU α (simplexPoint x))⁻¹ *
      (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ := by
    rcases le_or_gt (symanzikU α (simplexPoint x)) 0 with h | h
    · rw [Real.sqrt_eq_zero'.mpr h, _root_.inv_zero, mul_zero]
    · positivity
  rw [Real.norm_of_nonneg hnn]
  exact inv_mul_inv_sqrt_le _

/-! ### Sub-step (a): the energy integral at fixed spatial momenta -/

section StageA

variable {m : ℕ} (P : LoopQuadratic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

theorem norm_eval_loopMomenta_le (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    ‖P.eval (loopMomenta t v)‖ ≤
      P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) * (1 + ∑ s, t s ^ 2) := by
  refine (P.norm_eval_le _).trans ?_
  rw [sum_sq_loopMomenta, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ P.coeffBound_nonneg
  have h1 : 0 ≤ ∑ s, t s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  have h2 : 0 ≤ ∑ s, ∑ c, v s c ^ 2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg _
  nlinarith [mul_nonneg h1 h2]

theorem continuous_eval_loopMomenta_left (v : Fin 2 → Fin 3 → ℝ) :
    Continuous fun t : Fin 2 → ℝ => P.eval (loopMomenta t v) :=
  P.continuous_eval.comp (continuous_loopMomenta.comp (continuous_id.prodMk continuous_const))

theorem continuous_eval_loopMomenta_right (t : Fin 2 → ℝ) :
    Continuous fun v : Fin 2 → Fin 3 → ℝ => P.eval (loopMomenta t v) :=
  P.continuous_eval.comp (continuous_loopMomenta.comp (continuous_const.prodMk continuous_id))

/-- The pointwise bound on the energy integrand at an interior point of the simplex. -/
theorem norm_eval_mul_inv_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (τ t : Fin 2 → ℝ)
    (v : Fin 2 → Fin 3 → ℝ) (F : ℂ) :
    ‖P.eval (loopMomenta t v) * F‖ ≤
      P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) *
        (1 + 2 * ∑ i, τ i ^ 2 + 2 * (A.trace / A.det)) *
          ((1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)) ^ 1 * ‖F‖) := by
  have hK : 0 ≤ P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) := mul_nonneg P.coeffBound_nonneg
    (by positivity)
  have h1 := norm_eval_loopMomenta_le P t v
  have h2 := one_add_sum_sq_le hA t τ
  rw [norm_mul, pow_one]
  calc ‖P.eval (loopMomenta t v)‖ * ‖F‖
      ≤ (P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) * (1 + ∑ s, t s ^ 2)) * ‖F‖ := by gcongr
    _ ≤ (P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) *
          ((1 + 2 * ∑ i, τ i ^ 2 + 2 * (A.trace / A.det)) * (1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)))) *
          ‖F‖ := by gcongr
    _ = _ := by ring

/-- At an interior point of the simplex, the parametrized energy integrand with the numerator is
integrable in the energies (`N ≥ 3`). -/
theorem integrable_eval_mul_paramDenom (hm : 2 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) (v : Fin 2 → Fin 3 → ℝ) :
    Integrable fun t : Fin 2 → ℝ =>
      P.eval (loopMomenta t v) * (paramDenom α p M ε x t v ^ (m + 1))⁻¹ := by
  have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
  simp only [paramDenom_eq α p M hdet]
  have hw : (shiftedConst α p M ε x v).im < 0 := by rw [shiftedConst_im]; linarith
  have hb := ((integrable_one_add_quadratic_pow_mul_norm hPD hw (j := 1)
    (by omega : 1 + 2 ≤ m + 1)).comp_add_right (energyShift α p (simplexPoint x))).const_mul
    (P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) *
      (1 + 2 * ∑ i, energyShift α p (simplexPoint x) i ^ 2 +
        2 * ((symanzikMatrix α (simplexPoint x)).trace / (symanzikMatrix α (simplexPoint x)).det)))
  refine hb.mono' ?_ (Eventually.of_forall fun t => ?_)
  · refine ((continuous_eval_loopMomenta_left P v).mul ?_).aestronglyMeasurable
    exact (continuous_inv_neg_add_pow hw (m + 1)).comp
      ((continuous_quadratic _).comp (continuous_id.add continuous_const))
  · exact norm_eval_mul_inv_le P hPD _ t v _

theorem integrable_eval_mul_paramDenom_prod (hm : 2 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m))
    (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun q : (Fin m → ℝ) × (Fin 2 → ℝ) =>
        P.eval (loopMomenta q.2 v) * (paramDenom α p M ε q.1 q.2 v ^ (m + 1))⁻¹)
      ((volume.restrict (simplexSet m)).prod volume) := by
  have hm0 : 0 < m := by omega
  have hmeas : AEStronglyMeasurable (fun q : (Fin m → ℝ) × (Fin 2 → ℝ) =>
      P.eval (loopMomenta q.2 v) * (paramDenom α p M ε q.1 q.2 v ^ (m + 1))⁻¹)
      ((volume.restrict (simplexSet m)).prod volume) :=
    (((continuous_eval_loopMomenta_left P v).comp continuous_snd).mul
      (continuous_paramDenom α p M hε.ne' v)).aestronglyMeasurable
  obtain ⟨Kτ, hKτ⟩ := exists_sum_sq_energyShift_le α p
  have hK : 0 ≤ energyBound α p M v := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  set Kv := P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) with hKv
  have hKv0 : 0 ≤ Kv := mul_nonneg P.coeffBound_nonneg (by positivity)
  set KA := ∑ i, (α i 0 ^ 2 + α i 1 ^ 2) with hKA
  set C := Kv * ((Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 1 * energyNormConst m) with hC
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    exact integrable_eval_mul_paramDenom P α p M hm hε hPD v
  · have hb : IntegrableOn (fun x => C * ((1 + 2 * Kτ) *
        (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ + 2 * KA *
          ((symanzikU α (simplexPoint x))⁻¹ * (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹)))
        (simplexSet m) :=
      (((integrableOn_inv_sqrt_symanzikU α hU).const_mul _).add
        ((integrableOn_inv_mul_inv_sqrt_symanzikU α hU).const_mul _)).const_mul _
    refine hb.mono' hmeas.norm.integral_prod_right' ?_
    filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
    have hUpos : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
    have hz := Feynman.simplexPoint_mem_stdSimplex hxS
    have hτ := hKτ _ hz.1 hdet
    have htr := trace_symanzikMatrix_le α hz.1 hz.2
    have hre : |(shiftedConst α p M ε x v).re| ≤ energyBound α p M v := by
      rw [shiftedConst_re]
      exact abs_re_shifted_le α p M hz.1 hz.2 hdet v
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    simp only [paramDenom_eq α p M hdet]
    set A := symanzikMatrix α (simplexPoint x) with hAdef
    set τ := energyShift α p (simplexPoint x) with hτdef
    set w := shiftedConst α p M ε x v with hwdef
    have hw : w.im < 0 := by rw [hwdef, shiftedConst_im]; linarith
    have hAdet : A.det = symanzikU α (simplexPoint x) := rfl
    set B := 1 + 2 * ∑ i, τ i ^ 2 + 2 * (A.trace / A.det) with hB
    have hBle : B ≤ 1 + 2 * Kτ + 2 * KA * (symanzikU α (simplexPoint x))⁻¹ := by
      rw [hB, hAdet, div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_right htr (inv_nonneg.mpr hUpos.le)
      linarith
    have hint1 := (integrable_one_add_quadratic_pow_mul_norm hPD hw (j := 1)
      (by omega : 1 + 2 ≤ m + 1)).comp_add_right τ
    have hI := integral_one_add_quadratic_pow_mul_norm_le hPD hre (shiftedConst_im α p M x v)
      hδ0 hδ hδε (j := 1) (by omega : 1 + 2 ≤ m + 1)
    rw [Nat.add_sub_cancel] at hI
    have hI0 : 0 ≤ ∫ u : Fin 2 → ℝ, (1 + u ⬝ᵥ A *ᵥ u) ^ 1 *
        ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖ :=
      integral_nonneg fun u => by
        have := dotProduct_mulVec_self_nonneg hPD u
        positivity
    calc ∫ t, ‖P.eval (loopMomenta t v) *
          ((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖
        ≤ ∫ t, Kv * B * ((1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)) ^ 1 *
            ‖((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖) :=
          integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            (hint1.const_mul _) (Eventually.of_forall fun t => norm_eval_mul_inv_le P hPD τ t v _)
      _ = Kv * B * ∫ u : Fin 2 → ℝ, (1 + u ⬝ᵥ A *ᵥ u) ^ 1 *
            ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖ := by
          rw [integral_const_mul, integral_add_right_eq_self (fun u : Fin 2 → ℝ =>
            (1 + u ⬝ᵥ A *ᵥ u) ^ 1 * ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖) τ]
      _ ≤ Kv * (1 + 2 * Kτ + 2 * KA * (symanzikU α (simplexPoint x))⁻¹) *
            ((Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 1 * ((Real.sqrt A.det)⁻¹ * energyNormConst m)) := by
          have hB0 : 0 ≤ B := by
            have := trace_div_det_nonneg hPD
            have : 0 ≤ ∑ i, τ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
            linarith
          calc Kv * B * ∫ u : Fin 2 → ℝ, (1 + u ⬝ᵥ A *ᵥ u) ^ 1 *
                ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖
              ≤ Kv * B * ((Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 1 *
                  ((Real.sqrt A.det)⁻¹ * energyNormConst m)) :=
                mul_le_mul_of_nonneg_left hI (mul_nonneg hKv0 hB0)
            _ ≤ _ := by
                have : 0 ≤ (Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 1 *
                    ((Real.sqrt A.det)⁻¹ * energyNormConst m) :=
                  hI0.trans hI
                gcongr
      _ = C * ((1 + 2 * Kτ) * (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ + 2 * KA *
            ((symanzikU α (simplexPoint x))⁻¹ * (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹)) := by
          rw [hC, hAdet]
          ring

/-- At an interior point, the energy integral with the numerator is `numEnergyValue`. -/
theorem integral_eval_mul_paramDenom (hm : 2 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) (v : Fin 2 → Fin 3 → ℝ) :
    ∫ t : Fin 2 → ℝ, P.eval (loopMomenta t v) * (paramDenom α p M ε x t v ^ (m + 1))⁻¹ =
      numEnergyValue P α p M ε x v := by
  have hint := integrable_eval_mul_paramDenom P α p M hm hε hPD v
  have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
  simp only [paramDenom_eq α p M hdet] at hint ⊢
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set τ := energyShift α p (simplexPoint x) with hτdef
  set w := shiftedConst α p M ε x v with hwdef
  have hw : w.im < 0 := by rw [hwdef, shiftedConst_im]; linarith
  have hshift := integral_add_right_eq_self (μ := volume) (fun u : Fin 2 → ℝ =>
    P.eval (loopMomenta (u - τ) v) * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹) τ
  simp only [add_sub_cancel_right] at hshift
  rw [hshift]
  have hint' : Integrable fun u : Fin 2 → ℝ =>
      P.eval (loopMomenta (u - τ) v) * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹ := by
    have := hint.comp_sub_right τ
    simpa only [sub_add_cancel] using this
  have heven : ∀ u : Fin 2 → ℝ, P.eval (loopMomenta (u - τ) v) + P.eval (loopMomenta (-u - τ) v) =
      2 * (P.eval (loopMomenta (-τ) v) +
        ∑ s, ∑ r, P.quad s 0 r 0 * ((u s * u r : ℝ) : ℂ)) := fun u => by
    have e1 : loopMomenta (u - τ) v = loopMomenta (-τ) v + loopMomenta u 0 := by
      rw [← loopMomenta_add, add_zero, neg_add_eq_sub]
    have e2 : loopMomenta (-u - τ) v = loopMomenta (-τ) v - loopMomenta u 0 := by
      rw [← loopMomenta_sub, sub_zero]
      congr 1
      abel
    rw [e1, e2, LoopQuadratic.eval_add_add_eval_sub, quadPart_loopMomenta_energy]
  rw [integral_mul_inv_neg_quadratic_add_pow_of_even hPD hw (by omega) hint'
    (P.eval (loopMomenta (-τ) v)) (fun s r => P.quad s 0 r 0) heven]
  simp only [numEnergyValue, energyValue, energyValueTwo, LoopQuadratic.energyContract]
  rw [show m + 1 - 2 = m - 1 by omega]
  have hAU : A.det = symanzikU α (simplexPoint x) := rfl
  rw [hAU]
  push_cast
  ring

/-- **Sub-step (a) with a numerator: the energy integral at fixed spatial momenta.** For
`N = m + 1 ≥ 3` propagators, `ε > 0`, two independent `αᵢ`, `U⁻²` integrable on the simplex and a
numerator `P` of degree at most two, the energy integrand `P(ℓ) ∏ᵢ Dᵢ(t, v)⁻¹` is integrable and
`∫_{ℝ²} P ∏ᵢ Dᵢ⁻¹ dt = m! ∫_Δ (P(-τ, v) E₀ + (∑ Q_{s0,r0} (A⁻¹)ₛᵣ) E₂) dx`, with
`E₀ = -(π/(N-1)) U^{-1/2} w^{1-N}` and `E₂ = π/(2(N-1)(N-2)) U^{-1/2} w^{2-N}`. -/
theorem integral_loopQuadratic_mul_prod_lineDenom_eq (hm : 2 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m))
    (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun t : Fin 2 → ℝ =>
        P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹) ∧
      ∫ t : Fin 2 → ℝ, P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValue P α p M ε x v := by
  have hm0 : 0 < m := by omega
  have hint := integrable_eval_mul_paramDenom_prod P α p M hm hε hspan hU v
  have hfey : ∀ t : Fin 2 → ℝ,
      P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m,
          P.eval (loopMomenta t v) * (paramDenom α p M ε x t v ^ (m + 1))⁻¹ := by
    intro t
    have h : ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m, (paramDenom α p M ε x t v ^ (m + 1))⁻¹ := by
      refine Feynman.prod_inv_eq_factorial_mul_integral_simplex fun i => ?_
      simp only [lineDenom, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
        add_zero, zero_sub]
      linarith
    rw [h, integral_const_mul]
    ring
  refine ⟨?_, ?_⟩
  · simp only [hfey]
    exact hint.integral_prod_right.const_mul _
  · simp only [hfey]
    rw [integral_const_mul]
    congr 1
    rw [← integral_integral_swap (f := fun x t =>
      P.eval (loopMomenta t v) * (paramDenom α p M ε x t v ^ (m + 1))⁻¹) hint]
    refine integral_congr_ae ?_
    filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    exact integral_eval_mul_paramDenom P α p M hm hε hPD v

end StageA

/-! ### The spatial integrals at a fixed interior point -/

section StageB

variable {m : ℕ} (P : LoopQuadratic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

theorem energyValue_eq (x : Fin m → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    energyValue α p M ε x v = -(π / (((m + 1 : ℕ) : ℂ) - 1)) *
      ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
      ((((quadForm (symanzikMatrix α (simplexPoint x))
        (v + spatialShift α p (simplexPoint x)) : ℝ) : ℂ) +
        (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ m)⁻¹ := by
  simp only [energyValue, shiftedConst, Nat.add_sub_cancel]

theorem energyValueTwo_eq (x : Fin m → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    energyValueTwo α p M ε x v = π / (2 * ((m : ℂ) * ((m : ℂ) - 1))) *
      ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
      ((((quadForm (symanzikMatrix α (simplexPoint x))
        (v + spatialShift α p (simplexPoint x)) : ℝ) : ℂ) +
        (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 1))⁻¹ := by
  simp only [energyValueTwo, shiftedConst]

theorem sum_sq_neg (τ : Fin 2 → ℝ) : ∑ s, (-τ) s ^ 2 = ∑ s, τ s ^ 2 := by
  simp only [Pi.neg_apply, neg_sq]

/-- The pointwise bound on the spatial integrand at an interior point of the simplex. -/
theorem norm_eval_neg_mul_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (τ : Fin 2 → ℝ)
    (σ v : Fin 2 → Fin 3 → ℝ) (F : ℂ) :
    ‖P.eval (loopMomenta (-τ) v) * F‖ ≤
      P.coeffBound * (1 + ∑ s, τ s ^ 2) *
        (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) *
          ((1 + quadForm A (v + σ)) ^ 1 * ‖F‖) := by
  have h1 := (P.norm_eval_le (loopMomenta (-τ) v)).trans_eq (by
    rw [sum_sq_loopMomenta, sum_sq_neg])
  have h2 := one_add_sum_sum_sq_le hA v σ
  have hτ : 0 ≤ ∑ s, τ s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  have hv : 0 ≤ ∑ s, ∑ c, v s c ^ 2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg _
  have h3 : 1 + (∑ s, τ s ^ 2 + ∑ s, ∑ c, v s c ^ 2) ≤
      (1 + ∑ s, τ s ^ 2) * (1 + ∑ s, ∑ c, v s c ^ 2) := by nlinarith [mul_nonneg hτ hv]
  have hcb := P.coeffBound_nonneg
  rw [norm_mul, pow_one]
  calc ‖P.eval (loopMomenta (-τ) v)‖ * ‖F‖
      ≤ (P.coeffBound * ((1 + ∑ s, τ s ^ 2) * (1 + ∑ s, ∑ c, v s c ^ 2))) * ‖F‖ := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h3 hcb)
    _ ≤ (P.coeffBound * ((1 + ∑ s, τ s ^ 2) *
          ((1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) * (1 + quadForm A (v + σ))))) *
          ‖F‖ := by gcongr
    _ = _ := by ring

theorem continuous_quadForm' (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun v : Fin 2 → Fin 3 → ℝ => quadForm A v := by
  simp only [Spatial.quadForm_eq_sum]
  fun_prop

/-- Integrability in the spatial momenta of the first part of `numEnergyValue`, with the norm
bound used for Fubini. -/
theorem integrable_eval_mul_energyValue (hm : 5 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) {K δ : ℝ}
    (hV : |symanzikV α p M (simplexPoint x)| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) :
    Integrable (fun v : Fin 2 → Fin 3 → ℝ =>
        P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) * energyValue α p M ε x v) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ,
          ‖P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) * energyValue α p M ε x v‖ ≤
        ‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ *
          (P.coeffBound * (1 + ∑ s, energyShift α p (simplexPoint x) s ^ 2) *
            (1 + 2 * ∑ s, ∑ c, spatialShift α p (simplexPoint x) s c ^ 2 +
              2 * ((symanzikMatrix α (simplexPoint x)).trace /
                (symanzikMatrix α (simplexPoint x)).det))) *
          ((Real.sqrt δ ^ m)⁻¹ * (spatialNormConst (m - 1) *
            (Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3)⁻¹)) := by
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set τ := energyShift α p (simplexPoint x) with hτdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  set W : ℂ := ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I with hWdef
  have hw : W.im < 0 := by simp [hWdef]; linarith
  set c₀ : ℂ := -(π / (((m + 1 : ℕ) : ℂ) - 1)) with hc₀
  set K' := P.coeffBound * (1 + ∑ s, τ s ^ 2) *
    (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) with hK'
  have hK'0 : 0 ≤ K' := by
    have := trace_div_det_nonneg hPD
    have := P.coeffBound_nonneg
    positivity
  have hfun : ∀ v : Fin 2 → Fin 3 → ℝ, P.eval (loopMomenta (-τ) v) *
      energyValue α p M ε x v = c₀ * ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) :
        ℂ)⁻¹ * (P.eval (loopMomenta (-τ) v) * ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ m)⁻¹) := by
    intro v
    rw [energyValue_eq]
    ring
  have hb := ((integrable_one_add_quadForm_pow_mul_norm hPD hw (j := 1)
    (by omega : 1 + 4 ≤ m)).comp_add_right σ).const_mul K'
  have hg : Integrable fun v : Fin 2 → Fin 3 → ℝ =>
      P.eval (loopMomenta (-τ) v) * ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ m)⁻¹ := by
    refine hb.mono' ?_ (Eventually.of_forall fun v => norm_eval_neg_mul_le P hPD τ σ v _)
    exact ((continuous_eval_loopMomenta_right P _).mul ((continuous_inv_add_pow hw m).comp
      ((continuous_quadForm' A).comp (continuous_id.add continuous_const)))).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · simp only [hfun]
    exact hg.const_mul _
  · simp only [hfun]
    simp only [norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [integral_const_mul]
    have hI := integral_one_add_quadForm_pow_mul_norm_le hPD hV hδ0 hδ hδε (j := 1)
      (by omega : 1 + 4 ≤ m)
    have hI0 : 0 ≤ ∫ v : Fin 2 → Fin 3 → ℝ, (1 + quadForm A v) ^ 1 *
        ‖((((quadForm A v : ℝ) : ℂ) + W) ^ m)⁻¹‖ :=
      integral_nonneg fun v => by
        have := quadForm_nonneg hPD v
        positivity
    have hmono : ∫ v : Fin 2 → Fin 3 → ℝ, ‖P.eval (loopMomenta (-τ) v)‖ *
        (‖(((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ m‖)⁻¹ ≤
        K' * ∫ v : Fin 2 → Fin 3 → ℝ, (1 + quadForm A v) ^ 1 *
          ‖((((quadForm A v : ℝ) : ℂ) + W) ^ m)⁻¹‖ := by
      rw [← integral_add_right_eq_self (μ := volume) (fun v : Fin 2 → Fin 3 → ℝ =>
        (1 + quadForm A v) ^ 1 * ‖((((quadForm A v : ℝ) : ℂ) + W) ^ m)⁻¹‖) σ,
        ← integral_const_mul]
      refine integral_mono_of_nonneg (Eventually.of_forall fun v => by positivity)
        hb (Eventually.of_forall fun v => ?_)
      have := norm_eval_neg_mul_le P hPD τ σ v ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ m)⁻¹
      simp only [norm_mul, norm_inv] at this ⊢
      exact this
    have hpos : 0 ≤ ‖c₀‖ * (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ := by positivity
    calc ‖c₀‖ * (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ *
          ∫ v : Fin 2 → Fin 3 → ℝ, ‖P.eval (loopMomenta (-τ) v)‖ *
            (‖(((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ m‖)⁻¹
        ≤ ‖c₀‖ * (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ *
          (K' * ∫ v : Fin 2 → Fin 3 → ℝ, (1 + quadForm A v) ^ 1 *
            ‖((((quadForm A v : ℝ) : ℂ) + W) ^ m)⁻¹‖) :=
          mul_le_mul_of_nonneg_left hmono hpos
      _ ≤ ‖c₀‖ * (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ *
          (K' * ((Real.sqrt δ ^ m)⁻¹ * (spatialNormConst (m - 1) * (Real.sqrt A.det ^ 3)⁻¹))) := by
          gcongr
      _ = _ := by ring

/-- Integrability in the spatial momenta of the second part of `numEnergyValue`, with the norm
bound used for Fubini. -/
theorem integrable_energyContract_mul_energyValueTwo (hm : 5 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) {K δ : ℝ}
    (hV : |symanzikV α p M (simplexPoint x)| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) :
    Integrable (fun v : Fin 2 → Fin 3 → ℝ =>
        P.energyContract (symanzikMatrix α (simplexPoint x)) * energyValueTwo α p M ε x v) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ,
          ‖P.energyContract (symanzikMatrix α (simplexPoint x)) * energyValueTwo α p M ε x v‖ ≤
        ‖P.energyContract (symanzikMatrix α (simplexPoint x))‖ *
          ‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ *
            (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ *
          ((Real.sqrt δ ^ (m - 1))⁻¹ * (π ^ 3 * ((((m - 1 : ℕ) : ℝ) - 1) *
            (((m - 1 : ℕ) : ℝ) - 2) * (((m - 1 : ℕ) : ℝ) - 3))⁻¹ *
              (Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3)⁻¹)) := by
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  have hw : (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I).im < 0 := by
    simp; linarith
  have hfun : ∀ v : Fin 2 → Fin 3 → ℝ, P.energyContract A * energyValueTwo α p M ε x v =
      P.energyContract A * ((π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))) *
        ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
        ((((quadForm A (v + σ) : ℝ) : ℂ) +
          (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 1))⁻¹ := by
    intro v
    rw [energyValueTwo_eq]
    ring
  refine ⟨?_, ?_⟩
  · simp only [hfun]
    exact (integrable_inv_quadForm_shifted_add_pow hPD hw (by omega) σ).const_mul _
  · simp only [hfun]
    simp only [norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [integral_const_mul]
    have hI := integral_norm_inv_quadForm_shifted_le hPD hV hδ0 hδ hδε (k := m - 1)
      (by omega) σ
    simp only [norm_inv] at hI
    have hpos : 0 ≤ ‖P.energyContract A‖ * ‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ *
        (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hI hpos

/-- The spatial integral of the first part of `numEnergyValue` at an interior point. -/
theorem integral_eval_mul_energyValue (hm : 5 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) :
    ∫ v : Fin 2 → Fin 3 → ℝ,
        P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) * energyValue α p M ε x v =
      -(π / (((m + 1 : ℕ) : ℂ) - 1)) * ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
        (P.eval (loopMomenta (-energyShift α p (simplexPoint x))
            (-spatialShift α p (simplexPoint x))) *
          ((π : ℂ) ^ 3 * (((m : ℂ) - 1) * ((m : ℂ) - 2) * ((m : ℂ) - 3))⁻¹ *
            ((Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3 : ℝ) : ℂ)⁻¹ *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹) +
        P.spatialContract (symanzikMatrix α (simplexPoint x)) * ((π : ℂ) ^ 3 *
          (2 * (((m : ℂ) - 1) * ((m : ℂ) - 2) * ((m : ℂ) - 3) * ((m : ℂ) - 4)))⁻¹ *
          ((Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3 : ℝ) : ℂ)⁻¹ *
          ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹)) := by
  have hz : ∃ K, |symanzikV α p M (simplexPoint x)| ≤ K := ⟨_, le_rfl⟩
  obtain ⟨K, hV⟩ := hz
  have hK : 0 ≤ K := (abs_nonneg _).trans hV
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set τ := energyShift α p (simplexPoint x) with hτdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  set W : ℂ := ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I with hWdef
  have hw : W.im < 0 := by simp [hWdef]; linarith
  have hfun : (fun v : Fin 2 → Fin 3 → ℝ => P.eval (loopMomenta (-τ) v) *
      energyValue α p M ε x v) = fun v => -(π / (((m + 1 : ℕ) : ℂ) - 1)) *
        ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
        (P.eval (loopMomenta (-τ) v) * ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ m)⁻¹) := by
    funext v
    rw [energyValue_eq]
    ring
  have hg : Integrable fun v : Fin 2 → Fin 3 → ℝ =>
      P.eval (loopMomenta (-τ) v) * ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ m)⁻¹ := by
    have hb := ((integrable_one_add_quadForm_pow_mul_norm hPD hw (j := 1)
      (by omega : 1 + 4 ≤ m)).comp_add_right σ).const_mul (P.coeffBound * (1 + ∑ s, τ s ^ 2) *
        (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)))
    refine hb.mono' ?_ (Eventually.of_forall fun v => norm_eval_neg_mul_le P hPD τ σ v _)
    exact ((continuous_eval_loopMomenta_right P _).mul ((continuous_inv_add_pow hw m).comp
      ((continuous_quadForm' A).comp (continuous_id.add continuous_const)))).aestronglyMeasurable
  rw [hfun, integral_const_mul]
  congr 1
  have hshift := integral_add_right_eq_self (μ := volume) (fun y : Fin 2 → Fin 3 → ℝ =>
    P.eval (loopMomenta (-τ) (y - σ)) * ((((quadForm A y : ℝ) : ℂ) + W) ^ m)⁻¹) σ
  simp only [add_sub_cancel_right] at hshift
  rw [hshift]
  have hint' : Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      P.eval (loopMomenta (-τ) (y - σ)) * ((((quadForm A y : ℝ) : ℂ) + W) ^ m)⁻¹ := by
    have := hg.comp_sub_right σ
    simpa only [sub_add_cancel] using this
  have heven : ∀ y : Fin 2 → Fin 3 → ℝ, P.eval (loopMomenta (-τ) (y - σ)) +
      P.eval (loopMomenta (-τ) (-y - σ)) =
      2 * (P.eval (loopMomenta (-τ) (-σ)) + ∑ s, ∑ c : Fin 3, ∑ r, ∑ d : Fin 3,
        P.quad s c.succ r d.succ * ((y s c * y r d : ℝ) : ℂ)) := fun y => by
    have e1 : loopMomenta (-τ) (y - σ) = loopMomenta (-τ) (-σ) + loopMomenta 0 y := by
      rw [← loopMomenta_add, add_zero, neg_add_eq_sub]
    have e2 : loopMomenta (-τ) (-y - σ) = loopMomenta (-τ) (-σ) - loopMomenta 0 y := by
      rw [← loopMomenta_sub, sub_zero]
      congr 1
      abel
    rw [e1, e2, LoopQuadratic.eval_add_add_eval_sub, quadPart_loopMomenta_spatial]
  rw [integral_mul_inv_quadForm_add_pow_of_even hPD hw hm hint'
    (P.eval (loopMomenta (-τ) (-σ))) (fun s c r d => P.quad s c.succ r d.succ) heven]
  rfl

/-- The spatial integral of the second part of `numEnergyValue` at an interior point. -/
theorem integral_energyContract_mul_energyValueTwo (hm : 5 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) :
    ∫ v : Fin 2 → Fin 3 → ℝ,
        P.energyContract (symanzikMatrix α (simplexPoint x)) * energyValueTwo α p M ε x v =
      P.energyContract (symanzikMatrix α (simplexPoint x)) *
        ((π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))) *
        ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
        ((π : ℂ) ^ 3 * ((((m - 1 : ℕ) : ℂ) - 1) * (((m - 1 : ℕ) : ℂ) - 2) *
          (((m - 1 : ℕ) : ℂ) - 3))⁻¹ *
          ((Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3 : ℝ) : ℂ)⁻¹ *
          ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 1 - 3))⁻¹) := by
  have hw : (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I).im < 0 := by
    simp; linarith
  simp only [energyValueTwo_eq]
  simp only [← mul_assoc]
  rw [integral_const_mul, integral_inv_quadForm_shifted_add_pow hPD hw (by omega)]
  ring

end StageB

/-! ### Fubini on simplex × space and the representation -/

section Main

variable {m : ℕ} (P : LoopQuadratic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

theorem norm_energyContract_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) :
    ‖P.energyContract A‖ ≤ (∑ s, ∑ r, ‖P.quad s 0 r 0‖) * (A.trace / A.det) := by
  unfold LoopQuadratic.energyContract
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_inv_apply_le hA s r) (norm_nonneg _)

theorem integrable_numEnergyValue (hm : 5 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m))
    (hA : IntegrableOn (fun x => (symanzikMatrix α (simplexPoint x)).trace *
      (symanzikU α (simplexPoint x) ^ 3)⁻¹) (simplexSet m)) :
    Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) => numEnergyValue P α p M ε q.1 q.2)
      ((volume.restrict (simplexSet m)).prod volume) := by
  have hm0 : 0 < m := by omega
  set K := ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2) with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  obtain ⟨Kτ, hKτ⟩ := exists_sum_sq_energyShift_le α p
  obtain ⟨Kσ, hKσ⟩ := exists_sum_sq_spatialShift_le α p
  -- the first part
  have h1 : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      P.eval (loopMomenta (-energyShift α p (simplexPoint q.1)) q.2) *
        energyValue α p M ε q.1 q.2) ((volume.restrict (simplexSet m)).prod volume) := by
    have hmeas := ((measurable_eval_loopMomenta P α p).mul
      (measurable_energyValue α p M hε.ne')).aestronglyMeasurable
      (μ := (volume.restrict (simplexSet m)).prod volume)
    set C₁ := ‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * P.coeffBound * (1 + Kτ) *
      ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 1)) with hC₁
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hV := abs_symanzikV_le α p M hz.1 hz.2 hPD.det_pos.ne'
      exact (integrable_eval_mul_energyValue P α p M hm hε hPD hV hδ0 hδ hδε).1
    · have hb : IntegrableOn (fun x => C₁ * ((1 + 2 * Kσ) * (symanzikU α (simplexPoint x) ^ 2)⁻¹ +
          2 * ((symanzikMatrix α (simplexPoint x)).trace * (symanzikU α (simplexPoint x) ^ 3)⁻¹)))
          (simplexSet m) :=
        ((hU.const_mul _).add (hA.const_mul _)).const_mul _
      refine hb.mono' hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      have hUpos : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hV := abs_symanzikV_le α p M hz.1 hz.2 hdet
      have hτ := hKτ _ hz.1 hdet
      have hσ := hKσ _ hz.1 hdet
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      refine (integrable_eval_mul_energyValue P α p M hm hε hPD hV hδ0 hδ hδε).2.trans ?_
      have hAdet : (symanzikMatrix α (simplexPoint x)).det = symanzikU α (simplexPoint x) := rfl
      rw [hAdet]
      have htr0 : 0 ≤ (symanzikMatrix α (simplexPoint x)).trace := by
        have := trace_div_det_nonneg hPD
        rw [hAdet] at this
        exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hUpos)
      have hsnc : 0 ≤ spatialNormConst (m - 1) := by
        have h4 : (4 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ m - 1)
        unfold spatialNormConst
        have : 0 < (((m - 1 : ℕ) : ℝ) - 1) * (((m - 1 : ℕ) : ℝ) - 2) * (((m - 1 : ℕ) : ℝ) - 3) := by
          have a1 : 0 < ((m - 1 : ℕ) : ℝ) - 1 := by linarith
          have a2 : 0 < ((m - 1 : ℕ) : ℝ) - 2 := by linarith
          have a3 : 0 < ((m - 1 : ℕ) : ℝ) - 3 := by linarith
          positivity
        positivity
      set sU := Real.sqrt (symanzikU α (simplexPoint x)) with hsU
      have hsU0 : 0 < sU := Real.sqrt_pos.mpr hUpos
      have hUs : symanzikU α (simplexPoint x) = sU ^ 2 := (Real.sq_sqrt hUpos.le).symm
      set T := ∑ s, energyShift α p (simplexPoint x) s ^ 2 with hT
      set S := ∑ s, ∑ c, spatialShift α p (simplexPoint x) s c ^ 2 with hS
      set tr := (symanzikMatrix α (simplexPoint x)).trace with htr
      have hT0 : 0 ≤ T := Finset.sum_nonneg fun s _ => sq_nonneg _
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg _
      rw [hUs]
      have hX : 0 ≤ ‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * P.coeffBound *
          ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 1)) := by
        have := P.coeffBound_nonneg
        positivity
      calc ‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * sU⁻¹ *
            (P.coeffBound * (1 + T) * (1 + 2 * S + 2 * (tr / sU ^ 2))) *
            ((Real.sqrt δ ^ m)⁻¹ * (spatialNormConst (m - 1) * (sU ^ 3)⁻¹))
          = (‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * P.coeffBound *
              ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 1))) * (1 + T) *
              ((1 + 2 * S) * ((sU ^ 2) ^ 2)⁻¹ + 2 * (tr * ((sU ^ 2) ^ 3)⁻¹)) := by
            field_simp
        _ ≤ (‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * P.coeffBound *
              ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 1))) * (1 + Kτ) *
              ((1 + 2 * Kσ) * ((sU ^ 2) ^ 2)⁻¹ + 2 * (tr * ((sU ^ 2) ^ 3)⁻¹)) := by
            have hKτ0 : 0 ≤ 1 + Kτ := by linarith
            have hR : (1 + 2 * S) * ((sU ^ 2) ^ 2)⁻¹ + 2 * (tr * ((sU ^ 2) ^ 3)⁻¹) ≤
                (1 + 2 * Kσ) * ((sU ^ 2) ^ 2)⁻¹ + 2 * (tr * ((sU ^ 2) ^ 3)⁻¹) := by
              have : 0 ≤ ((sU ^ 2) ^ 2)⁻¹ := by positivity
              nlinarith
            have hR0 : 0 ≤ (1 + 2 * S) * ((sU ^ 2) ^ 2)⁻¹ + 2 * (tr * ((sU ^ 2) ^ 3)⁻¹) :=
              add_nonneg (mul_nonneg (by linarith) (by positivity))
                (mul_nonneg (by norm_num) (mul_nonneg htr0 (by positivity)))
            exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hX) hR hR0
              (mul_nonneg hX hKτ0)
        _ = _ := by
            rw [hC₁]
            ring
  -- the second part
  have h2 : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      P.energyContract (symanzikMatrix α (simplexPoint q.1)) * energyValueTwo α p M ε q.1 q.2)
      ((volume.restrict (simplexSet m)).prod volume) := by
    have hmeas := (((measurable_energyContract P α).comp measurable_fst).mul
      (measurable_energyValueTwo α p M hε.ne')).aestronglyMeasurable
      (μ := (volume.restrict (simplexSet m)).prod volume)
    set Qb := ∑ s, ∑ r, ‖P.quad s 0 r 0‖ with hQb
    set c₂ := ‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ with hc₂
    set k₃ := π ^ 3 * ((((m - 1 : ℕ) : ℝ) - 1) * (((m - 1 : ℕ) : ℝ) - 2) *
      (((m - 1 : ℕ) : ℝ) - 3))⁻¹ with hk₃
    have hk₃0 : 0 ≤ k₃ := by
      have h4 : (4 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ m - 1)
      have a1 : 0 < ((m - 1 : ℕ) : ℝ) - 1 := by linarith
      have a2 : 0 < ((m - 1 : ℕ) : ℝ) - 2 := by linarith
      have a3 : 0 < ((m - 1 : ℕ) : ℝ) - 3 := by linarith
      positivity
    set C₂ := Qb * c₂ * ((Real.sqrt δ ^ (m - 1))⁻¹ * k₃) with hC₂
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hV := abs_symanzikV_le α p M hz.1 hz.2 hPD.det_pos.ne'
      exact (integrable_energyContract_mul_energyValueTwo P α p M hm hε hPD hV hδ0 hδ hδε).1
    · refine (hA.const_mul C₂).mono' hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      have hUpos : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hV := abs_symanzikV_le α p M hz.1 hz.2 hdet
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      refine (integrable_energyContract_mul_energyValueTwo P α p M hm hε hPD hV hδ0 hδ
        hδε).2.trans ?_
      have hAdet : (symanzikMatrix α (simplexPoint x)).det = symanzikU α (simplexPoint x) := rfl
      have hec := norm_energyContract_le P hPD
      rw [hAdet] at hec ⊢
      rw [← hk₃]
      set sU := Real.sqrt (symanzikU α (simplexPoint x)) with hsU
      have hsU0 : 0 < sU := Real.sqrt_pos.mpr hUpos
      have hUs : symanzikU α (simplexPoint x) = sU ^ 2 := (Real.sq_sqrt hUpos.le).symm
      rw [hUs] at hec ⊢
      have hX : 0 ≤ c₂ * sU⁻¹ * ((Real.sqrt δ ^ (m - 1))⁻¹ * (k₃ * (sU ^ 3)⁻¹)) := by
        positivity
      calc ‖P.energyContract (symanzikMatrix α (simplexPoint x))‖ * c₂ * sU⁻¹ *
            ((Real.sqrt δ ^ (m - 1))⁻¹ * (k₃ * (sU ^ 3)⁻¹))
          = ‖P.energyContract (symanzikMatrix α (simplexPoint x))‖ *
              (c₂ * sU⁻¹ * ((Real.sqrt δ ^ (m - 1))⁻¹ * (k₃ * (sU ^ 3)⁻¹))) := by ring
        _ ≤ (Qb * ((symanzikMatrix α (simplexPoint x)).trace / sU ^ 2)) *
              (c₂ * sU⁻¹ * ((Real.sqrt δ ^ (m - 1))⁻¹ * (k₃ * (sU ^ 3)⁻¹))) :=
            mul_le_mul_of_nonneg_right hec hX
        _ = _ := by
            rw [hC₂]
            field_simp
  have hfun : (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) => numEnergyValue P α p M ε q.1 q.2) =
      fun q => P.eval (loopMomenta (-energyShift α p (simplexPoint q.1)) q.2) *
          energyValue α p M ε q.1 q.2 +
        P.energyContract (symanzikMatrix α (simplexPoint q.1)) * energyValueTwo α p M ε q.1 q.2 :=
    rfl
  rw [hfun]
  exact h1.add h2

/-- At an interior point, `m!` times the spatial integral of `numEnergyValue` is the integrand of
the representation. -/
theorem factorial_mul_integral_numEnergyValue (hm : 5 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) :
    (m.factorial : ℂ) * ∫ v : Fin 2 → Fin 3 → ℝ, numEnergyValue P α p M ε x v =
      -((π : ℂ) ^ 4) * (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 4).factorial : ℂ) *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
            P.eval (-loopShift α p (simplexPoint x)) +
          ((m - 5).factorial : ℂ) / 2 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
            P.contract (symanzikMatrix α (simplexPoint x)))) := by
  have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
  have hUpos : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
  obtain ⟨K, hV⟩ : ∃ K, |symanzikV α p M (simplexPoint x)| ≤ K := ⟨_, le_rfl⟩
  have hK : 0 ≤ K := (abs_nonneg _).trans hV
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  have i1 := (integrable_eval_mul_energyValue P α p M hm hε hPD hV hδ0 hδ hδε).1
  have i2 := (integrable_energyContract_mul_energyValueTwo P α p M hm hε hPD hV hδ0 hδ hδε).1
  have hsplit : ∫ v : Fin 2 → Fin 3 → ℝ, numEnergyValue P α p M ε x v =
      (∫ v : Fin 2 → Fin 3 → ℝ, P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) *
        energyValue α p M ε x v) + ∫ v : Fin 2 → Fin 3 → ℝ,
        P.energyContract (symanzikMatrix α (simplexPoint x)) * energyValueTwo α p M ε x v :=
    integral_add i1 i2
  rw [hsplit, integral_eval_mul_energyValue P α p M hm hε hPD,
    integral_energyContract_mul_energyValueTwo P α p M hm hε hPD, LoopQuadratic.contract_eq]
  have hneg : -loopShift α p (simplexPoint x) =
      loopMomenta (-energyShift α p (simplexPoint x)) (-spatialShift α p (simplexPoint x)) := by
    rw [loopShift, loopMomenta_neg]
  rw [hneg]
  have hAdet : (symanzikMatrix α (simplexPoint x)).det = symanzikU α (simplexPoint x) := rfl
  rw [hAdet]
  set a := P.eval (loopMomenta (-energyShift α p (simplexPoint x))
    (-spatialShift α p (simplexPoint x)))
  set ec := P.energyContract (symanzikMatrix α (simplexPoint x))
  set sc := P.spatialContract (symanzikMatrix α (simplexPoint x))
  set W : ℂ := ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I with hW
  have hW0 : W ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hW] at this
    linarith
  set sU := Real.sqrt (symanzikU α (simplexPoint x)) with hsU
  have hsU0 : (sU : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hUpos).ne'
  have hUs : symanzikU α (simplexPoint x) = sU ^ 2 := (Real.sq_sqrt hUpos.le).symm
  rw [hUs]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
  rw [show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 1 - 3 = k + 1 by omega, show k + 5 - 5 = k by omega,
    show ((k + 5 - 1 : ℕ) : ℂ) = (k : ℂ) + 4 by push_cast [show k + 5 - 1 = k + 4 by omega]; ring,
    show (k + 5).factorial = (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) * k.factorial by
      simp only [Nat.factorial_succ]; ring,
    show (k + 1).factorial = (k + 1) * k.factorial by simp only [Nat.factorial_succ]]
  push_cast
  have e1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
  have e2 : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : k + 2 ≠ 0)
  have e3 : (k : ℂ) + 3 ≠ 0 := by exact_mod_cast (by omega : k + 3 ≠ 0)
  have e4 : (k : ℂ) + 4 ≠ 0 := by exact_mod_cast (by omega : k + 4 ≠ 0)
  have e5 : (k : ℂ) + 5 ≠ 0 := by exact_mod_cast (by omega : k + 5 ≠ 0)
  have r1 : (k : ℂ) + 5 + 1 - 1 = (k : ℂ) + 5 := by ring
  have r2 : (k : ℂ) + 5 - 1 = (k : ℂ) + 4 := by ring
  have r3 : (k : ℂ) + 5 - 2 = (k : ℂ) + 3 := by ring
  have r4 : (k : ℂ) + 5 - 3 = (k : ℂ) + 2 := by ring
  have r5 : (k : ℂ) + 5 - 4 = (k : ℂ) + 1 := by ring
  have r6 : (k : ℂ) + 4 - 1 = (k : ℂ) + 3 := by ring
  have r7 : (k : ℂ) + 4 - 2 = (k : ℂ) + 2 := by ring
  have r8 : (k : ℂ) + 4 - 3 = (k : ℂ) + 1 := by ring
  rw [r1, r2, r3, r4, r5, r6, r7, r8]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  field_simp
  ring

/-- **The two-loop parametric representation with a numerator of degree at most two**
(O2-10/O2-11 infrastructure). For `N = m + 1 ≥ 6` propagators with line momenta
`kᵢ(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ`, masses `Mᵢ`, `ε > 0`, two linearly independent `αᵢ`, `U⁻²` and
`tr A · U⁻³` integrable on the simplex, and a numerator `P(ℓ) = c + ∑ L_{sμ} ℓₛ^μ +
∑ Q_{sμ,rν} ℓₛ^μ ℓᵣ^ν`: both stages of the joint energy-first integral of `P ∏ᵢ Dᵢ⁻¹`,
`Dᵢ = kᵢ·kᵢ + Mᵢ² - iε`, are integrable, and
`jointEnergyFirstIntegral 2 (P ∏ᵢ Dᵢ⁻¹) = -π⁴ ∫_Δ U⁻² ((N-5)! (V - iε)^{4-N} P(-S) +
(N-6)!/2 (V - iε)^{5-N} ∑ Q_{sμ,rν} g^{μν} (A⁻¹)ₛᵣ) dx`,
with `S = loopShift α p z = A⁻¹B` the shift of the completed square, `A = symanzikMatrix α z`,
`U = det A`, `V = symanzikV` and `g = diag(-1, 1, 1, 1)`. -/
theorem jointEnergyFirstIntegral_loopQuadratic_mul_prod_inv_lineDenom (hm : 5 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m))
    (hA : IntegrableOn (fun x => (symanzikMatrix α (simplexPoint x)).trace *
      (symanzikU α (simplexPoint x) ^ 3)⁻¹) (simplexSet m)) :
    (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ =>
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ,
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m, ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 4).factorial : ℂ) *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
            P.eval (-loopShift α p (simplexPoint x)) +
          ((m - 5).factorial : ℂ) / 2 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
            P.contract (symanzikMatrix α (simplexPoint x))) := by
  have hm0 : 0 < m := by omega
  have hA' := integral_loopQuadratic_mul_prod_lineDenom_eq P α p M (by omega) hε hspan hU
  have hH := integrable_numEnergyValue P α p M hm hε hspan hU hA
  refine ⟨fun v => (hA' v).1, ?_, ?_⟩
  · have : (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ,
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) =
        fun v => (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValue P α p M ε x v :=
      funext fun v => (hA' v).2
    rw [this]
    exact hH.integral_prod_right.const_mul _
  · have hA2 : ∀ v : Fin 2 → Fin 3 → ℝ, ∫ t : Fin 2 → ℝ,
        P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
          (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValue P α p M ε x v :=
      fun v => (hA' v).2
    have hspat : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
        (m.factorial : ℂ) * ∫ v : Fin 2 → Fin 3 → ℝ, numEnergyValue P α p M ε x v =
          -((π : ℂ) ^ 4) * (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
            (((m - 4).factorial : ℂ) *
                ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
                P.eval (-loopShift α p (simplexPoint x)) +
              ((m - 5).factorial : ℂ) / 2 *
                ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
                P.contract (symanzikMatrix α (simplexPoint x)))) := by
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      exact factorial_mul_integral_numEnergyValue P α p M hm hε hPD
    show ∫ v : Fin 2 → Fin 3 → ℝ, ∫ t : Fin 2 → ℝ,
        P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ = _
    simp only [hA2]
    rw [integral_const_mul, ← integral_integral_swap
      (f := fun x v => numEnergyValue P α p M ε x v) hH, ← integral_const_mul,
      integral_congr_ae hspat, integral_const_mul]

end Main

/-! ### Monomials of degree one and two -/

namespace LoopQuadratic

/-- The monomial `ℓₛ^μ`. -/
def linMono (s : Fin 2) (μ : Fin 4) : LoopQuadratic where
  const := 0
  lin := fun s' μ' => if s' = s then (if μ' = μ then 1 else 0) else 0
  quad := 0

/-- The monomial `ℓₛ^μ ℓᵣ^ν`. -/
def quadMono (s : Fin 2) (μ : Fin 4) (r : Fin 2) (ν : Fin 4) : LoopQuadratic where
  const := 0
  lin := 0
  quad := fun s' μ' r' ν' =>
    if s' = s then (if μ' = μ then (if r' = r then (if ν' = ν then 1 else 0) else 0) else 0) else 0

theorem eval_linMono (s : Fin 2) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (linMono s μ).eval ℓ = ((ℓ s μ : ℝ) : ℂ) := by
  simp [eval, linMono]

theorem contract_linMono (s : Fin 2) (μ : Fin 4) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (linMono s μ).contract A = 0 := by
  simp [contract, linMono]

theorem eval_quadMono (s : Fin 2) (μ : Fin 4) (r : Fin 2) (ν : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    (quadMono s μ r ν).eval ℓ = ((ℓ s μ * ℓ r ν : ℝ) : ℂ) := by
  simp [eval, quadMono]

theorem contract_quadMono (s : Fin 2) (μ : Fin 4) (r : Fin 2) (ν : Fin 4)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (quadMono s μ r ν).contract A =
      ((Minkowski.metric μ ν : ℝ) : ℂ) * ((A⁻¹ s r : ℝ) : ℂ) := by
  simp [contract, quadMono]

end LoopQuadratic

section Monomials

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- **Degree one.** Under the hypotheses of
`jointEnergyFirstIntegral_loopQuadratic_mul_prod_inv_lineDenom`, the loop momentum `ℓₛ^μ` in the
numerator is replaced by `-Sₛ^μ`:
`J[ℓₛ^μ] = -π⁴ (N-5)! ∫_Δ U⁻² (V - iε)^{4-N} (-Sₛ^μ) dx`. -/
theorem jointEnergyFirstIntegral_mul_prod_inv_lineDenom_degree_one (hm : 5 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m))
    (hA : IntegrableOn (fun x => (symanzikMatrix α (simplexPoint x)).trace *
      (symanzikU α (simplexPoint x) ^ 3)⁻¹) (simplexSet m)) (s : Fin 2) (μ : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => ((ℓ s μ : ℝ) : ℂ) * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ((m - 4).factorial : ℂ) *
        ∫ x in simplexSet m, ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
          ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
          ((-loopShift α p (simplexPoint x) s μ : ℝ) : ℂ) := by
  have h := (jointEnergyFirstIntegral_loopQuadratic_mul_prod_inv_lineDenom
    (LoopQuadratic.linMono s μ) α p M hm hε hspan hU hA).2.2
  simp only [LoopQuadratic.eval_linMono, LoopQuadratic.contract_linMono, mul_zero,
    add_zero] at h
  rw [h, mul_assoc]
  congr 1
  rw [← integral_const_mul ((m - 4).factorial : ℂ)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.neg_apply]
  ring

/-- **Degree two.** Under the hypotheses of
`jointEnergyFirstIntegral_loopQuadratic_mul_prod_inv_lineDenom`,
`J[ℓₛ^μ ℓᵣ^ν] = -π⁴ ∫_Δ U⁻² ((N-5)! (V - iε)^{4-N} Sₛ^μ Sᵣ^ν +
(N-6)!/2 (V - iε)^{5-N} g^{μν} (A⁻¹)ₛᵣ) dx`: the shifted product plus the contraction. -/
theorem jointEnergyFirstIntegral_mul_prod_inv_lineDenom_degree_two (hm : 5 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m))
    (hA : IntegrableOn (fun x => (symanzikMatrix α (simplexPoint x)).trace *
      (symanzikU α (simplexPoint x) ^ 3)⁻¹) (simplexSet m)) (s : Fin 2) (μ : Fin 4) (r : Fin 2)
    (ν : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => ((ℓ s μ * ℓ r ν : ℝ) : ℂ) * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m, ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 4).factorial : ℂ) *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
            ((loopShift α p (simplexPoint x) s μ * loopShift α p (simplexPoint x) r ν : ℝ) : ℂ) +
          ((m - 5).factorial : ℂ) / 2 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
            (((Minkowski.metric μ ν : ℝ) : ℂ) *
              (((symanzikMatrix α (simplexPoint x))⁻¹ s r : ℝ) : ℂ))) := by
  have h := (jointEnergyFirstIntegral_loopQuadratic_mul_prod_inv_lineDenom
    (LoopQuadratic.quadMono s μ r ν) α p M hm hε hspan hU hA).2.2
  simp only [LoopQuadratic.eval_quadMono, LoopQuadratic.contract_quadMono] at h
  rw [h]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.neg_apply, neg_mul_neg]

end Monomials

end QED.Integration.TwoLoop

end
