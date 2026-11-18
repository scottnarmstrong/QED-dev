/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopRefinedBound
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The two Fubini integrabilities under the numerator-aware criterion

Part of obligations O2-7, O2-10 and O2-11 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.3–4.4).
For `N = m + 1 ≥ 8` propagators `Dᵢ = kᵢ·kᵢ + Mᵢ² - iε` (`ε > 0`, any masses and external
momenta) and a numerator `P` of degree at most four whose values satisfy the pointwise bound
`RefinedBound α E 4 P.eval` (`QED/Integration/TwoLoopRefinedBound.lean`), the absolute
parametric integrands of both Fubini stages are bounded, uniformly on the simplex, by a constant
times `refinedWeight 2 E α = U⁻² ∏_{e ∈ E} (1 + Q_e/U)^{1/2}`:

* stage one (simplex × energies, at fixed spatial momenta): the energy integral of
  `|P| (1 + uᵀAu)²|−uᵀAu + w|^{-N}` is at most a constant times `U^{-1/2}` times the line weight
  (`integral_norm_eval_mul_paramDenom_le_refined`), and `U^{-1/2} ≤ (1 + U²) U⁻²`;
* stage two (simplex × space): each of the three terms of `numEnergyValueQuartic` is at most a
  constant times `U^{-1/2} · U^{-3/2}` times the line weight
  (`integral_norm_eval_mul_energyValue_le_refined`, `…energyContractTwo…`,
  `…energyContractFour…`); the energy contractions are bounded through the finite-difference
  bounds `norm_energyContractTwo_le_of_bound`, `norm_energyContractFour_le_of_bound`.

So if `refinedWeight 2 E α` is integrable on the simplex, both hypotheses of
`jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_integrable` hold
(`integrable_eval_mul_paramDenom_prod_of_refined`,
`integrable_numEnergyValueQuartic_of_refined`), and under `NoSubdivergenceRefined 2 E α` the
representation holds with both stages integrable
(`jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_refined`).

The second stage needs `N ≥ 8` (the quadratic contraction is bounded with weight
`(1 + quadForm)²` against the kernel `w^{2-N}`); the open-line classes have `N = 8`.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix Filter Function
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.Spatial (quadForm)

/-! ### Real inequalities -/

theorem RefinedBound.exists_le_sq {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ}
    {E : Finset (Fin (m + 1))} {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (h : RefinedBound α E 4 F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef → ∀ ℓ,
      ‖F ℓ‖ ≤ C * lineWeight α E A * (1 + loopNorm A ℓ) ^ 2 := by
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨C, hC, fun A hA ℓ => (hF A hA ℓ).trans_eq ?_⟩
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by linarith [loopNorm_nonneg hA ℓ])]

/-- `U^{-1/2} ≤ (1 + U²) U⁻²`. -/
theorem inv_sqrt_le_one_add_sq_mul_inv_sq {U : ℝ} (hU : 0 < U) :
    (Real.sqrt U)⁻¹ ≤ (1 + U ^ 2) * (U ^ 2)⁻¹ := by
  have hs : 0 < Real.sqrt U := Real.sqrt_pos.mpr hU
  have key : U ^ 2 ≤ (1 + U ^ 2) * Real.sqrt U := by
    rcases le_or_gt U 1 with h | h
    · have h1 : Real.sqrt U ≤ 1 := Real.sqrt_le_one.mpr h
      have h2 : U ≤ Real.sqrt U := by
        have := Real.mul_self_sqrt hU.le
        nlinarith
      nlinarith [sq_nonneg U]
    · have h1 : 1 ≤ Real.sqrt U := Real.one_le_sqrt.mpr h.le
      nlinarith [sq_nonneg U]
  rw [show (1 + U ^ 2) * (U ^ 2)⁻¹ = (1 + U ^ 2) / U ^ 2 by ring, le_div_iff₀ (by positivity),
    inv_mul_eq_div, div_le_iff₀ hs]
  exact key

theorem quadForm_add_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (v w : Fin 2 → Fin 3 → ℝ) : quadForm A (v + w) ≤ 2 * quadForm A v + 2 * quadForm A w := by
  rw [quadForm_eq_sum_dotProduct, quadForm_eq_sum_dotProduct, quadForm_eq_sum_dotProduct,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun c _ => qf_add_le hA (fun s => v s c) (fun s => w s c)

theorem quadForm_le_trace_mul {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (v : Fin 2 → Fin 3 → ℝ) : quadForm A v ≤ A.trace * ∑ s, ∑ c, v s c ^ 2 := by
  rw [quadForm_eq_sum_dotProduct, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => qf_le_trace_mul hA (fun s => v s c)

theorem qf_neg (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    (-x) ⬝ᵥ A *ᵥ (-x) = x ⬝ᵥ A *ᵥ x := by
  simp [mulVec_neg]

/-- The size of the loop momenta at the first stage, in terms of the shifted energies. -/
theorem one_add_loopNorm_loopMomenta_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    {KA Kτ : ℝ} (htr : A.trace ≤ KA) (τ : Fin 2 → ℝ) (hτ : ∑ s, τ s ^ 2 ≤ Kτ)
    (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    (1 + loopNorm A (loopMomenta t v)) ^ 2 ≤
      (2 + 2 * (KA * Kτ) + KA * ∑ s, ∑ c, v s c ^ 2) ^ 2 * (1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)) ^ 2 := by
  have htr0 : 0 ≤ A.trace := trace_nonneg_of_posDef hA
  have hτ0 : 0 ≤ ∑ s, τ s ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hv0 : 0 ≤ ∑ s, ∑ c, v s c ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hu0 := dotProduct_mulVec_self_nonneg hA (t + τ)
  have h1 : t ⬝ᵥ A *ᵥ t ≤ 2 * ((t + τ) ⬝ᵥ A *ᵥ (t + τ)) + 2 * (τ ⬝ᵥ A *ᵥ τ) := by
    have := qf_add_le hA (t + τ) (-τ)
    rw [add_neg_cancel_right, qf_neg] at this
    exact this
  have h2 : τ ⬝ᵥ A *ᵥ τ ≤ KA * Kτ :=
    (qf_le_trace_mul hA τ).trans (mul_le_mul htr hτ hτ0 (htr0.trans htr))
  have h3 : quadForm A v ≤ KA * ∑ s, ∑ c, v s c ^ 2 :=
    (quadForm_le_trace_mul hA v).trans (mul_le_mul_of_nonneg_right htr hv0)
  have hKA : 0 ≤ KA := htr0.trans htr
  have hKτ : 0 ≤ Kτ := hτ0.trans hτ
  have h4 : 1 + loopNorm A (loopMomenta t v) ≤
      (2 + 2 * (KA * Kτ) + KA * ∑ s, ∑ c, v s c ^ 2) * (1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)) := by
    rw [loopNorm_loopMomenta]
    nlinarith [mul_nonneg (mul_nonneg hKA hKτ) hu0, mul_nonneg (mul_nonneg hKA hv0) hu0]
  have h5 : 0 ≤ 1 + loopNorm A (loopMomenta t v) := by
    linarith [loopNorm_nonneg hA (loopMomenta t v)]
  rw [← mul_pow]
  exact pow_le_pow_left₀ h5 h4 2

/-- The size of the loop momenta at the second stage, in terms of the shifted spatial momenta. -/
theorem one_add_loopNorm_loopMomenta_neg_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    {KA Kτ Kσ : ℝ} (htr : A.trace ≤ KA) (τ : Fin 2 → ℝ) (hτ : ∑ s, τ s ^ 2 ≤ Kτ)
    (σ : Fin 2 → Fin 3 → ℝ) (hσ : ∑ s, ∑ c, σ s c ^ 2 ≤ Kσ) (v : Fin 2 → Fin 3 → ℝ) :
    (1 + loopNorm A (loopMomenta (-τ) v)) ^ 2 ≤
      (2 + KA * Kτ + 2 * (KA * Kσ)) ^ 2 * (1 + quadForm A (v + σ)) ^ 2 := by
  have htr0 : 0 ≤ A.trace := trace_nonneg_of_posDef hA
  have hτ0 : 0 ≤ ∑ s, τ s ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hσ0 : 0 ≤ ∑ s, ∑ c, σ s c ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq0 := quadForm_nonneg hA (v + σ)
  have hKA : 0 ≤ KA := htr0.trans htr
  have hKτ : 0 ≤ Kτ := hτ0.trans hτ
  have hKσ : 0 ≤ Kσ := hσ0.trans hσ
  have h1 : (-τ) ⬝ᵥ A *ᵥ (-τ) ≤ KA * Kτ := by
    rw [qf_neg]
    exact (qf_le_trace_mul hA τ).trans (mul_le_mul htr hτ hτ0 hKA)
  have h2 : quadForm A v ≤ 2 * quadForm A (v + σ) + 2 * quadForm A (-σ) := by
    have := quadForm_add_le hA (v + σ) (-σ)
    rwa [add_neg_cancel_right] at this
  have h3 : quadForm A (-σ) ≤ KA * Kσ := by
    refine (quadForm_le_trace_mul hA (-σ)).trans ?_
    have : ∑ s, ∑ c, (-σ) s c ^ 2 = ∑ s, ∑ c, σ s c ^ 2 := by simp
    rw [this]
    exact mul_le_mul htr hσ hσ0 hKA
  have h4 : 1 + loopNorm A (loopMomenta (-τ) v) ≤
      (2 + KA * Kτ + 2 * (KA * Kσ)) * (1 + quadForm A (v + σ)) := by
    rw [loopNorm_loopMomenta]
    nlinarith [mul_nonneg (mul_nonneg hKA hKτ) hq0, mul_nonneg (mul_nonneg hKA hKσ) hq0]
  have h5 : 0 ≤ 1 + loopNorm A (loopMomenta (-τ) v) := by
    linarith [loopNorm_nonneg hA (loopMomenta (-τ) v)]
  rw [← mul_pow]
  exact pow_le_pow_left₀ h5 h4 2

theorem symanzikU_sq_le {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hPD : (symanzikMatrix α z).PosDef) :
    symanzikU α z ^ 2 ≤ (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) ^ 4 := by
  have h1 := det_le_trace_sq hPD
  have h2 := trace_symanzikMatrix_le α hz hz1
  have h0 := trace_nonneg_of_posDef hPD
  have hU := hPD.det_pos
  have h3 : symanzikU α z ≤ (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) ^ 2 :=
    h1.trans (pow_le_pow_left₀ h0 h2 2)
  calc symanzikU α z ^ 2 ≤ ((∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) ^ 2) ^ 2 :=
        pow_le_pow_left₀ hU.le h3 2
    _ = _ := by ring

/-! ### Stage one: simplex × energies -/

section StageOne

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- **The first stage at an interior point**: the absolute energy integral of the parametrized
integrand is at most a constant (independent of the point) times `refinedWeight 2 E`. -/
theorem integral_norm_eval_mul_paramDenom_le_refined (hm : 3 ≤ m) (hε : 0 < ε)
    {x : Fin m → ℝ} (hxS : x ∈ simplexSet m) (hPD : (symanzikMatrix α (simplexPoint x)).PosDef)
    {E : Finset (Fin (m + 1))} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hB : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef → ∀ ℓ,
      ‖P.eval ℓ‖ ≤ Cb * lineWeight α E A * (1 + loopNorm A ℓ) ^ 2)
    {Kτ : ℝ} (hKτ : ∑ s, energyShift α p (simplexPoint x) s ^ 2 ≤ Kτ) (v : Fin 2 → Fin 3 → ℝ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (energyBound α p M v + 1) ^ 2) ≤ ε ^ 2) :
    ∫ t : Fin 2 → ℝ, ‖P.eval (loopMomenta t v) * (paramDenom α p M ε x t v ^ (m + 1))⁻¹‖ ≤
      Cb * (2 + 2 * ((∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kτ) +
          (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * ∑ s, ∑ c, v s c ^ 2) ^ 2 *
        ((Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 2 * energyNormConst (m - 1)) *
        (1 + (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) ^ 4) *
        refinedWeight 2 E α (simplexPoint x) := by
  have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
  have hUpos : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
  have hz := Feynman.simplexPoint_mem_stdSimplex hxS
  have htr := trace_symanzikMatrix_le α hz.1 hz.2
  have hre : |(shiftedConst α p M ε x v).re| ≤ energyBound α p M v := by
    rw [shiftedConst_re]
    exact abs_re_shifted_le α p M hz.1 hz.2 hdet v
  simp only [paramDenom_eq α p M hdet]
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set τ := energyShift α p (simplexPoint x) with hτdef
  set w := shiftedConst α p M ε x v with hwdef
  set U := symanzikU α (simplexPoint x) with hUdef
  set KA := ∑ i, (α i 0 ^ 2 + α i 1 ^ 2) with hKA
  set Cv := 2 + 2 * (KA * Kτ) + KA * ∑ s, ∑ c, v s c ^ 2 with hCv
  set lw := lineWeight α E A with hlw
  have hlw0 : 0 ≤ lw := lineWeight_nonneg α E A
  have hw : w.im < 0 := by rw [hwdef, shiftedConst_im]; linarith
  have hAdet : A.det = U := rfl
  have hint2 := (integrable_one_add_quadratic_pow_mul_norm hPD hw (j := 2)
    (by omega : 2 + 2 ≤ m + 1)).comp_add_right τ
  have hI := integral_one_add_quadratic_pow_mul_norm_le hPD hre (shiftedConst_im α p M x v)
    hδ0 hδ hδε (j := 2) (by omega : 2 + 2 ≤ m + 1)
  rw [show m + 1 - 2 = m - 1 by omega] at hI
  have hpt : ∀ t : Fin 2 → ℝ, ‖P.eval (loopMomenta t v) *
      ((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖ ≤
      Cb * lw * Cv ^ 2 * ((1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)) ^ 2 *
        ‖((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖) := fun t => by
    rw [norm_mul]
    have h1 := hB A hPD (loopMomenta t v)
    have h2 := one_add_loopNorm_loopMomenta_le hPD htr τ hKτ t v
    have h3 : ‖P.eval (loopMomenta t v)‖ ≤ Cb * lw * Cv ^ 2 * (1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)) ^ 2 :=
      h1.trans (by
        rw [mul_assoc (Cb * lw)]
        exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hCb hlw0))
    calc _ ≤ (Cb * lw * Cv ^ 2 * (1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)) ^ 2) *
          ‖((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖ :=
          mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = _ := by ring
  have hE0 : 0 ≤ energyNormConst (m - 1) := integral_nonneg fun _ => norm_nonneg _
  have hKA0 : 0 ≤ KA := Finset.sum_nonneg fun _ _ => by positivity
  have hsq := inv_sqrt_le_one_add_sq_mul_inv_sq hUpos
  have hU2 : U ^ 2 ≤ KA ^ 4 := symanzikU_sq_le α hz.1 hz.2 hPD
  have hRW : refinedWeight 2 E α (simplexPoint x) = (U ^ 2)⁻¹ * lw :=
    refinedWeight_eq_lineWeight α 2 E (simplexPoint x)
  calc ∫ t, ‖P.eval (loopMomenta t v) *
        ((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖
      ≤ ∫ t, Cb * lw * Cv ^ 2 * ((1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)) ^ 2 *
          ‖((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖) :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
          (hint2.const_mul _) (Eventually.of_forall hpt)
    _ = Cb * lw * Cv ^ 2 * ∫ u : Fin 2 → ℝ, (1 + u ⬝ᵥ A *ᵥ u) ^ 2 *
          ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖ := by
        rw [integral_const_mul, integral_add_right_eq_self (fun u : Fin 2 → ℝ =>
          (1 + u ⬝ᵥ A *ᵥ u) ^ 2 * ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖) τ]
    _ ≤ Cb * lw * Cv ^ 2 * ((Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 2 *
          ((Real.sqrt A.det)⁻¹ * energyNormConst (m - 1))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = Cb * Cv ^ 2 * ((Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 2 * energyNormConst (m - 1)) *
          (lw * (Real.sqrt U)⁻¹) := by rw [hAdet]; ring
    _ ≤ Cb * Cv ^ 2 * ((Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 2 * energyNormConst (m - 1)) *
          (lw * ((1 + KA ^ 4) * (U ^ 2)⁻¹)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hsq.trans ?_) hlw0)
          (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by rw [hRW]; ring

/-- **The first Fubini hypothesis** under the pointwise bound: for every spatial momentum, the
parametrized integrand is integrable on simplex × energies. -/
theorem integrable_eval_mul_paramDenom_prod_of_refined (hm : 3 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) {E : Finset (Fin (m + 1))}
    (hB : RefinedBound α E 4 P.eval)
    (hW : IntegrableOn (fun x => refinedWeight 2 E α (simplexPoint x)) (simplexSet m))
    (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun q : (Fin m → ℝ) × (Fin 2 → ℝ) =>
        P.eval (loopMomenta q.2 v) * (paramDenom α p M ε q.1 q.2 v ^ (m + 1))⁻¹)
      ((volume.restrict (simplexSet m)).prod volume) := by
  have hm0 : 0 < m := by omega
  obtain ⟨Cb, hCb, hB'⟩ := hB.exists_le_sq
  have hmeas : AEStronglyMeasurable (fun q : (Fin m → ℝ) × (Fin 2 → ℝ) =>
      P.eval (loopMomenta q.2 v) * (paramDenom α p M ε q.1 q.2 v ^ (m + 1))⁻¹)
      ((volume.restrict (simplexSet m)).prod volume) :=
    (((continuous_eval_loopMomenta_left_quartic P v).comp continuous_snd).mul
      (continuous_paramDenom α p M hε.ne' v)).aestronglyMeasurable
  obtain ⟨Kτ, hKτ⟩ := exists_sum_sq_energyShift_le α p
  have hK : 0 ≤ energyBound α p M v := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    exact integrable_eval_mul_paramDenom_quartic P α p M hm hε hPD v
  · refine (hW.const_mul (Cb * (2 + 2 * ((∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kτ) +
          (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * ∑ s, ∑ c, v s c ^ 2) ^ 2 *
        ((Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 2 * energyNormConst (m - 1)) *
        (1 + (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) ^ 4))).mono' hmeas.norm.integral_prod_right' ?_
    filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    have hz := Feynman.simplexPoint_mem_stdSimplex hxS
    have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    exact integral_norm_eval_mul_paramDenom_le_refined P α p M hm hε hxS hPD hCb hB'
      (hKτ _ hz.1 hdet) v hδ0 hδ hδε

end StageOne

/-! ### Stage two: simplex × space -/

section StageTwo

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- Common data of the three spatial bounds at an interior point. -/
theorem refinedWeight_eq_mul {x : Fin m → ℝ} (E : Finset (Fin (m + 1)))
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) :
    (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ * (Real.sqrt (symanzikU α (simplexPoint x)) ^ 3)⁻¹ *
      lineWeight α E (symanzikMatrix α (simplexPoint x)) =
      refinedWeight 2 E α (simplexPoint x) := by
  have hU : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
  rw [inv_sqrt_mul_inv_sqrt_pow_three hU, refinedWeight_eq_lineWeight]

/-- The first term of `numEnergyValueQuartic`, at an interior point. -/
theorem integrable_eval_mul_energyValue_refined (hm : 6 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hxS : x ∈ simplexSet m) (hPD : (symanzikMatrix α (simplexPoint x)).PosDef)
    {E : Finset (Fin (m + 1))} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hB : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef → ∀ ℓ,
      ‖P.eval ℓ‖ ≤ Cb * lineWeight α E A * (1 + loopNorm A ℓ) ^ 2)
    {K δ : ℝ} (hV : |symanzikV α p M (simplexPoint x)| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) {Kτ Kσ : ℝ}
    (hτ : ∑ s, energyShift α p (simplexPoint x) s ^ 2 ≤ Kτ)
    (hσ : ∑ s, ∑ c, spatialShift α p (simplexPoint x) s c ^ 2 ≤ Kσ) :
    Integrable (fun v : Fin 2 → Fin 3 → ℝ =>
        P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) * energyValue α p M ε x v) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ,
          ‖P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) * energyValue α p M ε x v‖ ≤
        ‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * Cb *
          (2 + (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kτ + 2 * ((∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kσ)) ^ 2 *
          ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 2)) *
          refinedWeight 2 E α (simplexPoint x) := by
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set τ := energyShift α p (simplexPoint x) with hτdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  set U := symanzikU α (simplexPoint x) with hUdef
  set KA := ∑ i, (α i 0 ^ 2 + α i 1 ^ 2) with hKA
  set Cs := 2 + KA * Kτ + 2 * (KA * Kσ) with hCs
  set lw := lineWeight α E A with hlw
  have hlw0 : 0 ≤ lw := lineWeight_nonneg α E A
  have hz := Feynman.simplexPoint_mem_stdSimplex hxS
  have htr := trace_symanzikMatrix_le α hz.1 hz.2
  have hAdet : A.det = U := rfl
  set c₀ : ℂ := -(π / (((m + 1 : ℕ) : ℂ) - 1)) with hc₀
  have hfun : ∀ v, P.eval (loopMomenta (-τ) v) * energyValue α p M ε x v =
      c₀ * ((Real.sqrt U : ℝ) : ℂ)⁻¹ * (P.eval (loopMomenta (-τ) v) *
        ((((quadForm A (v + σ) : ℝ) : ℂ) +
          (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ m)⁻¹) := fun v => by
    rw [energyValue_eq]
    ring
  have hbd : ∀ v, ‖P.eval (loopMomenta (-τ) v)‖ ≤ (Cb * lw * Cs ^ 2) * (1 + quadForm A (v + σ)) ^ 2 :=
    fun v => by
      have h2 := one_add_loopNorm_loopMomenta_neg_le hPD htr τ hτ σ hσ v
      calc ‖P.eval (loopMomenta (-τ) v)‖ ≤ Cb * lw * (1 + loopNorm A (loopMomenta (-τ) v)) ^ 2 :=
            hB A hPD _
        _ ≤ Cb * lw * (Cs ^ 2 * (1 + quadForm A (v + σ)) ^ 2) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hCb hlw0)
        _ = _ := by ring
  have hG := integrable_mul_inv_quadForm_shifted_and_le hPD hε hV hδ0 hδ hδε (j := 2) (k := m)
    (by omega) σ (P.continuous_eval.comp
      (continuous_loopMomenta.comp (continuous_const.prodMk continuous_id))) hbd
  refine ⟨?_, ?_⟩
  · simp only [hfun]
    exact hG.1.const_mul _
  · have hn : ∀ v, ‖P.eval (loopMomenta (-τ) v) * energyValue α p M ε x v‖ =
        ‖c₀ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * ‖P.eval (loopMomenta (-τ) v) *
          ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ m)⁻¹‖ := fun v => by
      rw [hfun, norm_mul]
    simp only [hn]
    rw [integral_const_mul]
    have hRW := refinedWeight_eq_mul α E hPD
    calc ‖c₀ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * ∫ v, ‖P.eval (loopMomenta (-τ) v) *
          ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ m)⁻¹‖
        ≤ ‖c₀ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * (Cb * lw * Cs ^ 2 *
            ((Real.sqrt δ ^ m)⁻¹ * (spatialNormConst (m - 2) * (Real.sqrt A.det ^ 3)⁻¹))) :=
          mul_le_mul_of_nonneg_left hG.2 (norm_nonneg _)
      _ = _ := by
          rw [← hRW, norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
            hAdet]
          ring

/-- The second term of `numEnergyValueQuartic`, at an interior point (`N ≥ 8`). -/
theorem integrable_energyContractTwo_mul_energyValueTwo_refined (hm : 7 ≤ m) (hε : 0 < ε)
    {x : Fin m → ℝ} (hxS : x ∈ simplexSet m) (hPD : (symanzikMatrix α (simplexPoint x)).PosDef)
    {E : Finset (Fin (m + 1))} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hB : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef → ∀ ℓ,
      ‖P.eval ℓ‖ ≤ Cb * lineWeight α E A * (1 + loopNorm A ℓ) ^ 2)
    {K δ : ℝ} (hV : |symanzikV α p M (simplexPoint x)| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) {Kτ Kσ : ℝ}
    (hτ : ∑ s, energyShift α p (simplexPoint x) s ^ 2 ≤ Kτ)
    (hσ : ∑ s, ∑ c, spatialShift α p (simplexPoint x) s c ^ 2 ≤ Kσ) :
    Integrable (fun v : Fin 2 → Fin 3 → ℝ =>
        P.energyContractTwo (symanzikMatrix α (simplexPoint x))
          (loopComp (loopMomenta (-energyShift α p (simplexPoint x)) v)) *
        energyValueTwo α p M ε x v) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ,
          ‖P.energyContractTwo (symanzikMatrix α (simplexPoint x))
            (loopComp (loopMomenta (-energyShift α p (simplexPoint x)) v)) *
          energyValueTwo α p M ε x v‖ ≤
        ‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ * (6 * 34 ^ 2 * Cb) *
          (2 + (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kτ + 2 * ((∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kσ)) ^ 2 *
          ((Real.sqrt δ ^ (m - 1))⁻¹ * spatialNormConst (m - 1 - 2)) *
          refinedWeight 2 E α (simplexPoint x) := by
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set τ := energyShift α p (simplexPoint x) with hτdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  set U := symanzikU α (simplexPoint x) with hUdef
  set KA := ∑ i, (α i 0 ^ 2 + α i 1 ^ 2) with hKA
  set Cs := 2 + KA * Kτ + 2 * (KA * Kσ) with hCs
  set lw := lineWeight α E A with hlw
  have hlw0 : 0 ≤ lw := lineWeight_nonneg α E A
  have hz := Feynman.simplexPoint_mem_stdSimplex hxS
  have htr := trace_symanzikMatrix_le α hz.1 hz.2
  have hAdet : A.det = U := rfl
  set c₂ : ℂ := (π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1))) with hc₂
  have hfun : ∀ v, P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
      energyValueTwo α p M ε x v = c₂ * ((Real.sqrt U : ℝ) : ℂ)⁻¹ *
        (P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
          ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 1))⁻¹) :=
    fun v => by
      rw [energyValueTwo_eq]
      ring
  have hbd : ∀ v, ‖P.energyContractTwo A (loopComp (loopMomenta (-τ) v))‖ ≤
      (6 * 34 ^ 2 * Cb * lw * Cs ^ 2) * (1 + quadForm A (v + σ)) ^ 2 := fun v => by
    have h1 := norm_energyContractTwo_le_of_bound P hPD (mul_nonneg hCb hlw0) (hB A hPD)
      (loopMomenta (-τ) v)
    refine h1.trans ?_
    have h2 := one_add_loopNorm_loopMomenta_neg_le hPD htr τ hτ σ hσ v
    have h3 : 0 ≤ 6 * 34 ^ 2 * (Cb * lw) := by positivity
    calc 6 * 34 ^ 2 * (Cb * lw) * (1 + loopNorm A (loopMomenta (-τ) v)) ^ 2
        ≤ 6 * 34 ^ 2 * (Cb * lw) * (Cs ^ 2 * (1 + quadForm A (v + σ)) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = _ := by ring
  have hG := integrable_mul_inv_quadForm_shifted_and_le hPD hε hV hδ0 hδ hδε (j := 2)
    (k := m - 1) (by omega) σ ((P.continuous_energyContractTwo A).comp (continuous_loopComp.comp
      (continuous_loopMomenta.comp (continuous_const.prodMk continuous_id)))) hbd
  refine ⟨?_, ?_⟩
  · simp only [hfun]
    exact hG.1.const_mul _
  · have hn : ∀ v, ‖P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
        energyValueTwo α p M ε x v‖ = ‖c₂ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ *
          ‖P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
            ((((quadForm A (v + σ) : ℝ) : ℂ) +
              (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 1))⁻¹‖ :=
      fun v => by rw [hfun, norm_mul]
    simp only [hn]
    rw [integral_const_mul]
    have hRW := refinedWeight_eq_mul α E hPD
    calc ‖c₂ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * ∫ v, ‖P.energyContractTwo A
          (loopComp (loopMomenta (-τ) v)) * ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 1))⁻¹‖
        ≤ ‖c₂ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * (6 * 34 ^ 2 * Cb * lw * Cs ^ 2 *
            ((Real.sqrt δ ^ (m - 1))⁻¹ *
              (spatialNormConst (m - 1 - 2) * (Real.sqrt A.det ^ 3)⁻¹))) :=
          mul_le_mul_of_nonneg_left hG.2 (norm_nonneg _)
      _ = _ := by
          rw [← hRW, norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
            hAdet]
          ring

/-- The third term of `numEnergyValueQuartic`, at an interior point. -/
theorem integrable_energyContractFour_mul_energyValueFour_refined (hm : 6 ≤ m) (hε : 0 < ε)
    {x : Fin m → ℝ} (hPD : (symanzikMatrix α (simplexPoint x)).PosDef)
    {E : Finset (Fin (m + 1))} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hB : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef → ∀ ℓ,
      ‖P.eval ℓ‖ ≤ Cb * lineWeight α E A * (1 + loopNorm A ℓ) ^ 2)
    {K δ : ℝ} (hV : |symanzikV α p M (simplexPoint x)| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) :
    Integrable (fun v : Fin 2 → Fin 3 → ℝ =>
        P.energyContractFour (symanzikMatrix α (simplexPoint x)) * energyValueFour α p M ε x v) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ,
          ‖P.energyContractFour (symanzikMatrix α (simplexPoint x)) *
            energyValueFour α p M ε x v‖ ≤
        ‖-(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2))))‖ * (5 * 33 ^ 2 * Cb) *
          ((Real.sqrt δ ^ (m - 2))⁻¹ * spatialNormConst (m - 2 - 0)) *
          refinedWeight 2 E α (simplexPoint x) := by
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  set U := symanzikU α (simplexPoint x) with hUdef
  set lw := lineWeight α E A with hlw
  have hlw0 : 0 ≤ lw := lineWeight_nonneg α E A
  have hAdet : A.det = U := rfl
  set c₄ : ℂ := -(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2)))) with hc₄
  have hfun : ∀ v, P.energyContractFour A * energyValueFour α p M ε x v =
      c₄ * ((Real.sqrt U : ℝ) : ℂ)⁻¹ * (P.energyContractFour A *
        ((((quadForm A (v + σ) : ℝ) : ℂ) +
          (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 2))⁻¹) :=
    fun v => by
      rw [energyValueFour_eq]
      ring
  have hC4 := norm_energyContractFour_le_of_bound P hPD (mul_nonneg hCb hlw0) (hB A hPD)
  have hG := integrable_mul_inv_quadForm_shifted_and_le hPD hε hV hδ0 hδ hδε (j := 0)
    (k := m - 2) (by omega) σ (continuous_const (y := P.energyContractFour A))
    (C := 5 * 33 ^ 2 * Cb * lw) (fun v => by rw [pow_zero, mul_one]; linarith)
  refine ⟨?_, ?_⟩
  · simp only [hfun]
    exact hG.1.const_mul _
  · have hn : ∀ v, ‖P.energyContractFour A * energyValueFour α p M ε x v‖ =
        ‖c₄ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * ‖P.energyContractFour A *
          ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 2))⁻¹‖ :=
      fun v => by rw [hfun, norm_mul]
    simp only [hn]
    rw [integral_const_mul]
    have hRW := refinedWeight_eq_mul α E hPD
    calc ‖c₄ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * ∫ v, ‖P.energyContractFour A *
          ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 2))⁻¹‖
        ≤ ‖c₄ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * (5 * 33 ^ 2 * Cb * lw *
            ((Real.sqrt δ ^ (m - 2))⁻¹ *
              (spatialNormConst (m - 2 - 0) * (Real.sqrt A.det ^ 3)⁻¹))) :=
          mul_le_mul_of_nonneg_left hG.2 (norm_nonneg _)
      _ = _ := by
          rw [← hRW, norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
            hAdet]
          ring

/-- **The second Fubini hypothesis** under the pointwise bound (`N ≥ 8`): the energy-integrated
integrand is integrable on simplex × space. -/
theorem integrable_numEnergyValueQuartic_of_refined (hm : 7 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) {E : Finset (Fin (m + 1))}
    (hB : RefinedBound α E 4 P.eval)
    (hW : IntegrableOn (fun x => refinedWeight 2 E α (simplexPoint x)) (simplexSet m)) :
    Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
        numEnergyValueQuartic P α p M ε q.1 q.2)
      ((volume.restrict (simplexSet m)).prod volume) := by
  have hm0 : 0 < m := by omega
  obtain ⟨Cb, hCb, hB'⟩ := hB.exists_le_sq
  set K := ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2) with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  obtain ⟨Kτ, hKτ⟩ := exists_sum_sq_energyShift_le α p
  obtain ⟨Kσ, hKσ⟩ := exists_sum_sq_spatialShift_le α p
  -- the first part
  have h1 : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      P.eval (loopMomenta (-energyShift α p (simplexPoint q.1)) q.2) *
        energyValue α p M ε q.1 q.2) ((volume.restrict (simplexSet m)).prod volume) := by
    have hmeas := ((measurable_eval_loopMomenta_quartic P α p).mul
      (measurable_energyValue α p M hε.ne')).aestronglyMeasurable
      (μ := (volume.restrict (simplexSet m)).prod volume)
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      exact (integrable_eval_mul_energyValue_refined P α p M (by omega) hε hxS hPD hCb hB'
        (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).1
    · refine (hW.const_mul (‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * Cb *
          (2 + (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kτ + 2 * ((∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kσ)) ^ 2 *
          ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 2)))).mono' hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact (integrable_eval_mul_energyValue_refined P α p M (by omega) hε hxS hPD hCb hB'
        (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).2
  -- the second part
  have h2 : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      P.energyContractTwo (symanzikMatrix α (simplexPoint q.1))
          (loopComp (loopMomenta (-energyShift α p (simplexPoint q.1)) q.2)) *
        energyValueTwo α p M ε q.1 q.2) ((volume.restrict (simplexSet m)).prod volume) := by
    have hmeas := ((measurable_energyContractTwo_loopMomenta P α p).mul
      (measurable_energyValueTwo α p M hε.ne')).aestronglyMeasurable
      (μ := (volume.restrict (simplexSet m)).prod volume)
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      exact (integrable_energyContractTwo_mul_energyValueTwo_refined P α p M hm hε hxS hPD hCb
        hB' (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).1
    · refine (hW.const_mul (‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ * (6 * 34 ^ 2 * Cb) *
          (2 + (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kτ + 2 * ((∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kσ)) ^ 2 *
          ((Real.sqrt δ ^ (m - 1))⁻¹ * spatialNormConst (m - 1 - 2)))).mono' hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact (integrable_energyContractTwo_mul_energyValueTwo_refined P α p M hm hε hxS hPD hCb
        hB' (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).2
  -- the third part
  have h3 : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      P.energyContractFour (symanzikMatrix α (simplexPoint q.1)) *
        energyValueFour α p M ε q.1 q.2) ((volume.restrict (simplexSet m)).prod volume) := by
    have hmeas := (((measurable_energyContractFour P α).comp measurable_fst).mul
      (measurable_energyValueFour α p M hε.ne')).aestronglyMeasurable
      (μ := (volume.restrict (simplexSet m)).prod volume)
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      exact (integrable_energyContractFour_mul_energyValueFour_refined P α p M (by omega) hε hPD
        hCb hB' (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε).1
    · refine (hW.const_mul (‖-(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2))))‖ * (5 * 33 ^ 2 * Cb) *
          ((Real.sqrt δ ^ (m - 2))⁻¹ * spatialNormConst (m - 2 - 0)))).mono' hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact (integrable_energyContractFour_mul_energyValueFour_refined P α p M (by omega) hε hPD
        hCb hB' (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε).2
  exact (h1.add h2).add h3

end StageTwo

/-! ### The representation under the numerator-aware criterion -/

section Representation

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- **The representation with a numerator of degree at most four under the numerator-aware
criterion.** For `N = m + 1 ≥ 8` propagators, `ε > 0`, a numerator whose values satisfy the
pointwise bound `RefinedBound α E 4 P.eval`, and `NoSubdivergenceRefined 2 E α`: both stages of
the joint energy-first integral are integrable and the parametric formula of
`jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom` holds. -/
theorem jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_refined (hm : 7 ≤ m)
    (hε : 0 < ε) {E : Finset (Fin (m + 1))} (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 P.eval) :
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
            P.contractTwo (symanzikMatrix α (simplexPoint x))
              (loopComp (-loopShift α p (simplexPoint x))) +
          ((m - 6).factorial : ℂ) / 4 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 5))⁻¹ *
            P.contractFour (symanzikMatrix α (simplexPoint x))) := by
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  have hW := integrableOn_refinedWeight_of_criterion α 2 E hcrit
  exact jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_integrable P α p M
    (by omega) hε hspan
    (integrable_eval_mul_paramDenom_prod_of_refined P α p M (by omega) hε hspan hB hW)
    (integrable_numEnergyValueQuartic_of_refined P α p M hm hε hspan hB hW)

/-- **Both stages of the joint energy-first integral are integrable** (T₉′), under the
numerator-aware criterion and the pointwise bound. -/
theorem jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined (hm : 7 ≤ m)
    (hε : 0 < ε) {E : Finset (Fin (m + 1))} (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 P.eval) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2
      (fun ℓ => P.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) := by
  obtain ⟨h1, h2, -⟩ :=
    jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_refined P α p M hm hε hcrit hB
  exact ⟨h1, h2⟩

end Representation

end QED.Integration.TwoLoop

end
