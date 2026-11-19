/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopRefinedBoundFubini
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The two Fubini integrabilities for a cubic numerator and seven propagators

The variant of `QED/Integration/TwoLoopRefinedBoundFubini.lean` for a numerator of degree at
most three (`P.quart = 0`). There the second Fubini stage needs `N ≥ 8` propagators only for the
quadratic energy contraction, which is bounded with weight `(1 + quadForm)²` against the kernel
`w^{2-N}`. For a cubic numerator the energy Hessian is affine in the loop momenta, so a bound of
the values by `K (1 + |ℓ|²_A)²` already gives the bound `5 K' (1 + |ℓ|²_A)` on the contraction
(`norm_energyContractTwo_le_of_bound_cubic`, by rescaling `ℓ` to unit size). With weight
`(1 + quadForm)¹` the kernel `w^{2-N}` is integrable for `N ≥ 7`, which is the case of the
two-loop self-energy graphs (three electron lines and two Pauli–Villars photons).

The main result is `jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic`.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix Filter Function
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.Spatial (quadForm)

/-! ### Affinity of the energy Hessian of a cubic -/

namespace LoopQuartic

variable (P : LoopQuartic)

theorem energyHess_smul_of_quart (hq : P.quart = 0) (t : ℝ) (X : LoopIndex → ℂ)
    (w : Fin 2 → ℝ) :
    P.energyHess ((t : ℂ) • X) w =
      P.energyHess 0 w + t * (P.energyHess X w - P.energyHess 0 w) := by
  have hs : ∀ a b c d, P.quartSym a b c d = 0 := by intro a b c d; simp [quartSym, hq]
  simp only [energyHess, hess, hs, zero_mul, Finset.sum_const_zero, add_zero, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply, mul_zero]
  simp only [add_mul, Finset.sum_add_distrib, add_sub_cancel_left, Finset.sum_mul]
  congr 1
  simp only [mul_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;>
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_ <;> ring

end LoopQuartic

theorem loopComp_smul (t : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    loopComp (t • ℓ) = (t : ℂ) • loopComp ℓ := by
  funext a
  simp [loopComp]

theorem loopComp_zero' : loopComp 0 = 0 := by
  funext a
  simp [loopComp]

theorem loopNorm_smul (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    loopNorm A (t • ℓ) = t ^ 2 * loopNorm A ℓ := by
  unfold loopNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h : (fun s => (t • ℓ) s μ) = t • fun s => ℓ s μ := by
    funext s
    simp
  rw [h, qf_smul]

/-- **The quadratic energy contraction of a cubic grows linearly.** -/
theorem norm_energyContractTwo_le_of_bound_cubic (P : LoopQuartic) (hq : P.quart = 0)
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) {K : ℝ} (hK : 0 ≤ K)
    (hP : ∀ ℓ, ‖P.eval ℓ‖ ≤ K * (1 + loopNorm A ℓ) ^ 2) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ‖P.energyContractTwo A (loopComp ℓ)‖ ≤ 5 * (6 * 34 ^ 2 * K) * (1 + loopNorm A ℓ) := by
  obtain ⟨w₁, w₂, hG⟩ := exists_inv_decomp hA
  set g : (Fin 2 → Fin 4 → ℝ) → ℂ := fun ℓ => P.energyContractTwo A (loopComp ℓ) with hg
  have haff : ∀ (t : ℝ) ℓ, g (t • ℓ) = g 0 + t * (g ℓ - g 0) := by
    intro t ℓ
    simp only [hg, P.energyContractTwo_eq_of_decomp hG, loopComp_smul, loopComp_zero',
      P.energyHess_smul_of_quart hq]
    ring
  have hb := norm_energyContractTwo_le_of_bound P hA hK hP
  set B := 6 * 34 ^ 2 * K with hB
  have hB0 : 0 ≤ B := by positivity
  set N := loopNorm A ℓ with hN
  have hN0 : 0 ≤ N := loopNorm_nonneg hA ℓ
  have h0 : ‖g 0‖ ≤ B := by
    have := hb 0
    rw [loopNorm_zero] at this
    simpa using this
  show ‖g ℓ‖ ≤ 5 * B * (1 + N)
  by_cases hN1 : N ≤ 1
  · have h := hb ℓ
    have h2 : (1 + N) ^ 2 ≤ 2 * (1 + N) := by nlinarith
    calc ‖g ℓ‖ ≤ B * (1 + N) ^ 2 := h
      _ ≤ B * (2 * (1 + N)) := mul_le_mul_of_nonneg_left h2 hB0
      _ ≤ 5 * B * (1 + N) := by nlinarith
  · replace hN1 := not_le.mp hN1
    have hNpos : 0 < N := by linarith
    set t : ℝ := N⁻¹ with ht
    have htN : t * N = 1 := inv_mul_cancel₀ hNpos.ne'
    have hnt : loopNorm A (t • ℓ) ≤ 1 := by
      rw [loopNorm_smul, ← hN]
      have : t ^ 2 * N = t := by rw [sq, mul_assoc, htN, mul_one]
      rw [this, ht]
      exact inv_le_one_of_one_le₀ hN1.le
    have h1 : ‖g (t • ℓ)‖ ≤ 4 * B := by
      have h := hb (t • ℓ)
      have h0' := loopNorm_nonneg hA (t • ℓ)
      have : (1 + loopNorm A (t • ℓ)) ^ 2 ≤ 4 := by nlinarith
      calc _ ≤ B * (1 + loopNorm A (t • ℓ)) ^ 2 := h
        _ ≤ B * 4 := mul_le_mul_of_nonneg_left this hB0
        _ = 4 * B := by ring
    have hrep : g ℓ = g 0 + (N : ℂ) * (g (t • ℓ) - g 0) := by
      rw [haff t ℓ]
      have : (N : ℂ) * (t : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, mul_comm, htN, Complex.ofReal_one]
      linear_combination -(g ℓ - g 0) * this
    rw [hrep]
    calc ‖g 0 + (N : ℂ) * (g (t • ℓ) - g 0)‖
        ≤ ‖g 0‖ + N * (‖g (t • ℓ)‖ + ‖g 0‖) := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hN0]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hN0
      _ ≤ B + N * (4 * B + B) := by gcongr
      _ ≤ 5 * B * (1 + N) := by nlinarith

/-! ### Stage two with seven propagators -/

section StageTwo

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

theorem one_add_loopNorm_loopMomenta_neg_le_one {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    {KA Kτ Kσ : ℝ} (htr : A.trace ≤ KA) (τ : Fin 2 → ℝ) (hτ : ∑ s, τ s ^ 2 ≤ Kτ)
    (σ : Fin 2 → Fin 3 → ℝ) (hσ : ∑ s, ∑ c, σ s c ^ 2 ≤ Kσ) (v : Fin 2 → Fin 3 → ℝ) :
    1 + loopNorm A (loopMomenta (-τ) v) ≤
      (2 + KA * Kτ + 2 * (KA * Kσ)) * (1 + quadForm A (v + σ)) := by
  have h := one_add_loopNorm_loopMomenta_neg_le hA htr τ hτ σ hσ v
  rw [← mul_pow] at h
  have hKA : 0 ≤ KA := (trace_nonneg_of_posDef hA).trans htr
  have hKτ : 0 ≤ Kτ := (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans hτ
  have hKσ : 0 ≤ Kσ :=
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _).trans hσ
  have hq0 := quadForm_nonneg hA (v + σ)
  have h1 : 0 ≤ 1 + loopNorm A (loopMomenta (-τ) v) := by
    linarith [loopNorm_nonneg hA (loopMomenta (-τ) v)]
  have h2 : 0 ≤ (2 + KA * Kτ + 2 * (KA * Kσ)) * (1 + quadForm A (v + σ)) := by positivity
  exact (pow_le_pow_iff_left₀ h1 h2 two_ne_zero).mp h

/-- The second term of `numEnergyValueQuartic` for a cubic, at an interior point (`N ≥ 7`). -/
theorem integrable_energyContractTwo_mul_energyValueTwo_cubic (hq : P.quart = 0) (hm : 6 ≤ m)
    (hε : 0 < ε) {x : Fin m → ℝ} (hxS : x ∈ simplexSet m)
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef)
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
        ‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ * (5 * (6 * 34 ^ 2 * Cb)) *
          (2 + (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kτ + 2 * ((∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kσ)) *
          ((Real.sqrt δ ^ (m - 1))⁻¹ * spatialNormConst (m - 1 - 1)) *
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
      (5 * (6 * 34 ^ 2 * Cb) * lw * Cs) * (1 + quadForm A (v + σ)) ^ 1 := fun v => by
    have h1 := norm_energyContractTwo_le_of_bound_cubic P hq hPD (mul_nonneg hCb hlw0)
      (hB A hPD) (loopMomenta (-τ) v)
    refine h1.trans ?_
    have h2 := one_add_loopNorm_loopMomenta_neg_le_one hPD htr τ hτ σ hσ v
    have h3 : 0 ≤ 5 * (6 * 34 ^ 2 * (Cb * lw)) := by positivity
    calc 5 * (6 * 34 ^ 2 * (Cb * lw)) * (1 + loopNorm A (loopMomenta (-τ) v))
        ≤ 5 * (6 * 34 ^ 2 * (Cb * lw)) * (Cs * (1 + quadForm A (v + σ))) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = _ := by ring
  have hG := integrable_mul_inv_quadForm_shifted_and_le hPD hε hV hδ0 hδ hδε (j := 1)
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
        ≤ ‖c₂ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * (5 * (6 * 34 ^ 2 * Cb) * lw * Cs *
            ((Real.sqrt δ ^ (m - 1))⁻¹ *
              (spatialNormConst (m - 1 - 1) * (Real.sqrt A.det ^ 3)⁻¹))) :=
          mul_le_mul_of_nonneg_left hG.2 (norm_nonneg _)
      _ = _ := by
          rw [← hRW, norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
            hAdet]
          ring

/-- **The second Fubini hypothesis for a cubic** (`N ≥ 7`). -/
theorem integrable_numEnergyValueQuartic_of_cubic (hq : P.quart = 0) (hm : 6 ≤ m) (hε : 0 < ε)
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
      exact (integrable_eval_mul_energyValue_refined P α p M hm hε hxS hPD hCb hB'
        (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).1
    · refine (hW.const_mul (‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * Cb *
          (2 + (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kτ +
            2 * ((∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kσ)) ^ 2 *
          ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 2)))).mono'
            hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact (integrable_eval_mul_energyValue_refined P α p M hm hε hxS hPD hCb hB'
        (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).2
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
      exact (integrable_energyContractTwo_mul_energyValueTwo_cubic P α p M hq hm hε hxS hPD
        hCb hB' (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).1
    · refine (hW.const_mul (‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ *
          (5 * (6 * 34 ^ 2 * Cb)) *
          (2 + (∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kτ +
            2 * ((∑ i, (α i 0 ^ 2 + α i 1 ^ 2)) * Kσ)) *
          ((Real.sqrt δ ^ (m - 1))⁻¹ * spatialNormConst (m - 1 - 1)))).mono'
            hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact (integrable_energyContractTwo_mul_energyValueTwo_cubic P α p M hq hm hε hxS hPD
        hCb hB' (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).2
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
      exact (integrable_energyContractFour_mul_energyValueFour_refined P α p M hm hε hPD
        hCb hB' (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε).1
    · refine (hW.const_mul (‖-(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2))))‖ *
          (5 * 33 ^ 2 * Cb) * ((Real.sqrt δ ^ (m - 2))⁻¹ * spatialNormConst (m - 2 - 0)))).mono'
            hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact (integrable_energyContractFour_mul_energyValueFour_refined P α p M hm hε hPD
        hCb hB' (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε).2
  exact (h1.add h2).add h3

end StageTwo

/-! ### The representation for a cubic numerator -/

section Representation

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- **Both stages of the joint energy-first integral are integrable** (T₉′) for a numerator of
degree at most three and `N = m + 1 ≥ 7` propagators, under the numerator-aware criterion and the
pointwise bound. -/
theorem jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic
    (hq : P.quart = 0) (hm : 6 ≤ m) (hε : 0 < ε) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 P.eval) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2
      (fun ℓ => P.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) := by
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  have hW := integrableOn_refinedWeight_of_criterion α 2 E hcrit
  obtain ⟨h1, h2, -⟩ := jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_integrable
    P α p M hm hε hspan
    (integrable_eval_mul_paramDenom_prod_of_refined P α p M (by omega) hε hspan hB hW)
    (integrable_numEnergyValueQuartic_of_cubic P α p M hq hm hε hspan hB hW)
  exact ⟨h1, h2⟩

end Representation

end QED.Integration.TwoLoop

end
