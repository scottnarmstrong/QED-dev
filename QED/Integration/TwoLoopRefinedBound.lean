/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopNumeratorQuarticFull
public import QED.Integration.SymanzikIntegrabilityRefined
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Numerator bounds by the line weights

Part of obligations O2-7, O2-10 and O2-11 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.3–4.4).
The representation with numerators of degree at most four
(`QED/Integration/TwoLoopNumeratorQuarticFull.lean`) has a form
`jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_integrable` that takes the two
Fubini integrabilities as hypotheses. This file supplies the pointwise bounds that will give
them under the numerator-aware criterion `NoSubdivergenceRefined`
(`QED/Integration/SymanzikIntegrabilityRefined.lean`).

For a positive definite `2 × 2` matrix `A` (the Symanzik matrix at an interior point), loop
momenta `ℓ` and lines `e` with loop coefficients `α_e`:

* `loopNorm A ℓ = ∑_μ (ℓ^μ)ᵀ A ℓ^μ`, the Euclidean size of `ℓ` in the metric `A`;
* `lineWeight α E A = ∏_{e ∈ E} (1 + α_eᵀ A⁻¹ α_e)^{1/2}`; at `A = A(z)` it is
  `∏_{e ∈ E} (1 + Q_e/U)^{1/2}`, so that `refinedWeight 2 E α z = U⁻² · lineWeight`
  (`refinedWeight_eq_lineWeight`).

**The pointwise bound.** `RefinedBound α E k F`: there is `C ≥ 0` with
`‖F ℓ‖ ≤ C · lineWeight α E A · (1 + loopNorm A ℓ)^{k/2}` for every positive definite `A` and
every `ℓ`. By Cauchy–Schwarz in the metric `A`, `|α_e·x| ≤ (α_eᵀA⁻¹α_e)^{1/2} (xᵀAx)^{1/2}`
(`sq_dotProduct_le`), so every component of a line momentum `k_e = α_e·ℓ + p_e` satisfies
`RefinedBound α {e} 1` (`refinedBound_lineMomentum`). The predicate is closed under sums,
constant multiples and products over disjoint line sets (`RefinedBound.mul`,
`RefinedBound.prod`), so a product `∏_{e ∈ E} (k_e)^{μ_e}` satisfies `RefinedBound α E |E|`.

**The energy contractions.** The representation involves, besides `P(ℓ)`, the contractions
`∑ₛᵣ Hₛ₀,ᵣ₀(X) (A⁻¹)ₛᵣ` (`LoopQuartic.energyContractTwo`) and
`∑ Rₛ₀,ᵣ₀,ₜ₀,q₀ Πₛᵣₜq(A⁻¹)` (`LoopQuartic.energyContractFour`). Writing `A⁻¹ = w₁w₁ᵀ + w₂w₂ᵀ`
(`exists_inv_decomp`, a Cholesky factorization, with `w₁ᵀAw₁ + w₂ᵀAw₂ = tr(A A⁻¹) = 2`), they are
values of the quadratic and quartic parts of `P` in energy directions of bounded `A`-length
(`energyContractTwo_eq_of_decomp`, `energyContractFour_eq_of_decomp`), and these are finite
differences of `P` (`energyHess_eq_fd`, `energyQuart_eq_fd`). So a bound on `P` alone bounds
both contractions with the same line weight (`norm_energyContractTwo_le_of_bound`,
`norm_energyContractFour_le_of_bound`), without computing the coefficients of `P`.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix Filter Function
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### Positive definite `2 × 2` matrices -/

section PosDefTwo

variable {A : Matrix (Fin 2) (Fin 2) ℝ}

theorem posDef_symm (hA : A.PosDef) : A 1 0 = A 0 1 := by
  simpa using hA.1.apply 0 1

theorem dotProduct_mulVec_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) (x y : Fin 2 → ℝ) :
    x ⬝ᵥ A *ᵥ y = x 0 * (A 0 0 * y 0 + A 0 1 * y 1) + x 1 * (A 1 0 * y 0 + A 1 1 * y 1) := by
  simp [dotProduct, mulVec, Fin.sum_univ_two]

/-- `(x + y)ᵀA(x + y) ≤ 2 xᵀAx + 2 yᵀAy`. -/
theorem qf_add_le (hA : A.PosDef) (x y : Fin 2 → ℝ) :
    (x + y) ⬝ᵥ A *ᵥ (x + y) ≤ 2 * (x ⬝ᵥ A *ᵥ x) + 2 * (y ⬝ᵥ A *ᵥ y) := by
  have h := dotProduct_mulVec_self_nonneg hA (x - y)
  have hs := posDef_symm hA
  simp only [dotProduct_mulVec_fin_two, Pi.add_apply, Pi.sub_apply, hs] at h ⊢
  nlinarith [h]

theorem qf_smul (A : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (x : Fin 2 → ℝ) :
    (c • x) ⬝ᵥ A *ᵥ (c • x) = c ^ 2 * (x ⬝ᵥ A *ᵥ x) := by
  simp only [dotProduct_mulVec_fin_two, Pi.smul_apply, smul_eq_mul]
  ring

/-- `xᵀAx ≤ tr A · |x|²`. -/
theorem qf_le_trace_mul (hA : A.PosDef) (x : Fin 2 → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ A.trace * ∑ s, x s ^ 2 := by
  have h := dotProduct_mulVec_self_nonneg hA ![x 1, -x 0]
  have hs := posDef_symm hA
  simp only [dotProduct_mulVec_fin_two, hs, trace_fin_two, Fin.sum_univ_two, cons_val_zero,
    cons_val_one] at h ⊢
  nlinarith [h]

/-- `det A ≤ (tr A)²`. -/
theorem det_le_trace_sq (hA : A.PosDef) : A.det ≤ A.trace ^ 2 := by
  have h0 : 0 < A 0 0 := hA.diag_pos
  have h1 : 0 < A 1 1 := hA.diag_pos
  rw [det_fin_two, trace_fin_two, posDef_symm hA]
  nlinarith [sq_nonneg (A 0 1), mul_pos h0 h1]

/-- **Cauchy–Schwarz in the metric `A`**: `(a·x)² ≤ (aᵀA⁻¹a)(xᵀAx)`. -/
theorem sq_dotProduct_le (hA : A.PosDef) (a x : Fin 2 → ℝ) :
    (a ⬝ᵥ x) ^ 2 ≤ (a ⬝ᵥ A⁻¹ *ᵥ a) * (x ⬝ᵥ A *ᵥ x) := by
  have hdet : 0 < A.det := hA.det_pos
  have hs := posDef_symm hA
  have hinv : a ⬝ᵥ A⁻¹ *ᵥ a = A.det⁻¹ * (a ⬝ᵥ adjugate A *ᵥ a) := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have key : (a ⬝ᵥ adjugate A *ᵥ a) * (x ⬝ᵥ A *ᵥ x) - A.det * (a ⬝ᵥ x) ^ 2 =
      (a 0 * (A 0 1 * x 0 + A 1 1 * x 1) - a 1 * (A 0 0 * x 0 + A 0 1 * x 1)) ^ 2 := by
    rw [adjugate_fin_two, det_fin_two]
    simp [dotProduct, mulVec, Fin.sum_univ_two, hs]
    ring
  have h2 : A.det * (a ⬝ᵥ x) ^ 2 ≤ (a ⬝ᵥ adjugate A *ᵥ a) * (x ⬝ᵥ A *ᵥ x) := by
    nlinarith [key, sq_nonneg (a 0 * (A 0 1 * x 0 + A 1 1 * x 1) -
      a 1 * (A 0 0 * x 0 + A 0 1 * x 1))]
  rw [hinv, mul_assoc]
  rw [le_inv_mul_iff₀ hdet]
  exact h2

theorem abs_dotProduct_le (hA : A.PosDef) (a x : Fin 2 → ℝ) :
    |a ⬝ᵥ x| ≤ Real.sqrt (a ⬝ᵥ A⁻¹ *ᵥ a) * Real.sqrt (x ⬝ᵥ A *ᵥ x) := by
  rw [← Real.sqrt_mul (dotProduct_mulVec_self_nonneg hA.inv a)]
  exact Real.abs_le_sqrt (sq_dotProduct_le hA a x)

end PosDefTwo

/-! ### The size of the loop momenta and the line weights -/

/-- `loopNorm A ℓ = ∑_μ (ℓ^μ)ᵀ A ℓ^μ`. -/
def loopNorm (A : Matrix (Fin 2) (Fin 2) ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℝ :=
  ∑ μ : Fin 4, (fun s => ℓ s μ) ⬝ᵥ A *ᵥ (fun s => ℓ s μ)

/-- `lineWeight α E A = ∏_{e ∈ E} (1 + α_eᵀ A⁻¹ α_e)^{1/2}`. -/
noncomputable def lineWeight {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (E : Finset (Fin (m + 1)))
    (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ∏ e ∈ E, Real.sqrt (1 + α e ⬝ᵥ A⁻¹ *ᵥ α e)

section Norms

variable {A : Matrix (Fin 2) (Fin 2) ℝ}

theorem loopNorm_nonneg (hA : A.PosDef) (ℓ : Fin 2 → Fin 4 → ℝ) : 0 ≤ loopNorm A ℓ :=
  Finset.sum_nonneg fun _ _ => dotProduct_mulVec_self_nonneg hA _

theorem loopNorm_add_le (hA : A.PosDef) (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    loopNorm A (ℓ + δ) ≤ 2 * loopNorm A ℓ + 2 * loopNorm A δ := by
  unfold loopNorm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun μ _ => qf_add_le hA (fun s => ℓ s μ) (fun s => δ s μ)

theorem loopNorm_neg (A : Matrix (Fin 2) (Fin 2) ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    loopNorm A (-ℓ) = loopNorm A ℓ := by
  unfold loopNorm
  refine Finset.sum_congr rfl fun μ _ => ?_
  have := qf_smul A (-1) (fun s => ℓ s μ)
  simp only [neg_smul, one_smul, even_two, Even.neg_pow, one_pow, one_mul] at this
  convert this using 2

theorem loopNorm_sub_le (hA : A.PosDef) (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    loopNorm A (ℓ - δ) ≤ 2 * loopNorm A ℓ + 2 * loopNorm A δ := by
  rw [sub_eq_add_neg, ← loopNorm_neg A δ]
  exact loopNorm_add_le hA ℓ (-δ)

theorem loopNorm_zero (A : Matrix (Fin 2) (Fin 2) ℝ) : loopNorm A 0 = 0 := by
  simp [loopNorm]

theorem loopNorm_loopMomenta_energy (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) :
    loopNorm A (loopMomenta w 0) = w ⬝ᵥ A *ᵥ w := by
  unfold loopNorm
  rw [Fin.sum_univ_succ]
  have h0 : (fun s => loopMomenta w 0 s 0) = w := by funext s; simp [loopMomenta]
  have h1 : ∀ c : Fin 3, (fun s => loopMomenta w 0 s c.succ) = 0 := fun c => by
    funext s; simp [loopMomenta]
  simp [h0, h1]

theorem loopNorm_loopMomenta (A : Matrix (Fin 2) (Fin 2) ℝ) (t : Fin 2 → ℝ)
    (v : Fin 2 → Fin 3 → ℝ) :
    loopNorm A (loopMomenta t v) = t ⬝ᵥ A *ᵥ t + Spatial.quadForm A v := by
  unfold loopNorm
  rw [Fin.sum_univ_succ, quadForm_eq_sum_dotProduct]
  rfl

theorem sqrt_one_add_loopNorm_one_le (hA : A.PosDef) (ℓ : Fin 2 → Fin 4 → ℝ) :
    1 ≤ Real.sqrt (1 + loopNorm A ℓ) := by
  rw [Real.one_le_sqrt]
  linarith [loopNorm_nonneg hA ℓ]

theorem qf_le_loopNorm (hA : A.PosDef) (ℓ : Fin 2 → Fin 4 → ℝ) (ν : Fin 4) :
    (fun s => ℓ s ν) ⬝ᵥ A *ᵥ (fun s => ℓ s ν) ≤ loopNorm A ℓ :=
  Finset.single_le_sum (f := fun μ => (fun s => ℓ s μ) ⬝ᵥ A *ᵥ (fun s => ℓ s μ))
    (fun _ _ => dotProduct_mulVec_self_nonneg hA _) (Finset.mem_univ ν)

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)

theorem lineWeight_nonneg (E : Finset (Fin (m + 1))) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    0 ≤ lineWeight α E A :=
  Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _

theorem one_le_sqrt_lineFactor (hA : A.PosDef) (e : Fin (m + 1)) :
    1 ≤ Real.sqrt (1 + α e ⬝ᵥ A⁻¹ *ᵥ α e) := by
  rw [Real.one_le_sqrt]
  linarith [dotProduct_mulVec_self_nonneg hA.inv (α e)]

theorem lineWeight_mono (hA : A.PosDef) {E E' : Finset (Fin (m + 1))} (h : E ⊆ E') :
    lineWeight α E A ≤ lineWeight α E' A :=
  Finset.prod_le_prod_of_subset_of_one_le₀ h (fun _ _ => Real.sqrt_nonneg _)
    fun e _ _ => one_le_sqrt_lineFactor α hA e

theorem lineWeight_union {E E' : Finset (Fin (m + 1))} (h : Disjoint E E')
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    lineWeight α (E ∪ E') A = lineWeight α E A * lineWeight α E' A :=
  Finset.prod_union h

theorem lineWeight_singleton (e : Fin (m + 1)) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    lineWeight α {e} A = Real.sqrt (1 + α e ⬝ᵥ A⁻¹ *ᵥ α e) :=
  Finset.prod_singleton _ _

/-- At the Symanzik matrix the line weight is `∏_{e ∈ E} (1 + Q_e/U)^{1/2}`, and
`refinedWeight 2 E α z = U⁻² · lineWeight α E A(z)`. -/
theorem refinedWeight_eq_lineWeight (k : ℕ) (E : Finset (Fin (m + 1))) (z : Fin (m + 1) → ℝ) :
    refinedWeight k E α z = (symanzikU α z ^ k)⁻¹ * lineWeight α E (symanzikMatrix α z) := by
  unfold refinedWeight lineWeight
  simp only [lineQuad_div_symanzikU]

end Norms

/-! ### The pointwise bound -/

/-- **The pointwise bound by the line weights**: there is `C ≥ 0` with
`‖F ℓ‖ ≤ C · lineWeight α E A · (1 + loopNorm A ℓ)^{k/2}` for every positive definite `A` and
all loop momenta `ℓ`. -/
def RefinedBound {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (E : Finset (Fin (m + 1))) (k : ℕ)
    (F : (Fin 2 → Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef → ∀ ℓ,
    ‖F ℓ‖ ≤ C * lineWeight α E A * Real.sqrt (1 + loopNorm A ℓ) ^ k

namespace RefinedBound

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {E E' : Finset (Fin (m + 1))} {k k' : ℕ}
  {F G : (Fin 2 → Fin 4 → ℝ) → ℂ}

theorem mono (h : RefinedBound α E k F) (hE : E ⊆ E') (hk : k ≤ k') : RefinedBound α E' k' F := by
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨C, hC, fun A hA ℓ => (hF A hA ℓ).trans ?_⟩
  have h1 := lineWeight_mono α hA hE
  have h2 := pow_le_pow_right₀ (sqrt_one_add_loopNorm_one_le hA ℓ) hk
  have h3 := lineWeight_nonneg α E A
  have h4 := lineWeight_nonneg α E' A
  have h5 : 0 ≤ Real.sqrt (1 + loopNorm A ℓ) ^ k := pow_nonneg (Real.sqrt_nonneg _) k
  calc C * lineWeight α E A * Real.sqrt (1 + loopNorm A ℓ) ^ k
      ≤ C * lineWeight α E' A * Real.sqrt (1 + loopNorm A ℓ) ^ k := by gcongr
    _ ≤ C * lineWeight α E' A * Real.sqrt (1 + loopNorm A ℓ) ^ k' :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hC h4)

theorem const (c : ℂ) : RefinedBound α ∅ 0 fun _ => c :=
  ⟨‖c‖, norm_nonneg _, fun A _ ℓ => by simp [lineWeight]⟩

theorem add (hF : RefinedBound α E k F) (hG : RefinedBound α E k G) :
    RefinedBound α E k fun ℓ => F ℓ + G ℓ := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C + D, add_nonneg hC hD, fun A hA ℓ => ?_⟩
  calc ‖F ℓ + G ℓ‖ ≤ ‖F ℓ‖ + ‖G ℓ‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (hF A hA ℓ) (hG A hA ℓ)
    _ = _ := by ring

theorem const_mul (c : ℂ) (hF : RefinedBound α E k F) : RefinedBound α E k fun ℓ => c * F ℓ := by
  obtain ⟨C, hC, hF⟩ := hF
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun A hA ℓ => ?_⟩
  rw [norm_mul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← mul_assoc]
  exact hF A hA ℓ

theorem neg (hF : RefinedBound α E k F) : RefinedBound α E k fun ℓ => -F ℓ := by
  simpa using hF.const_mul (-1)

theorem sub (hF : RefinedBound α E k F) (hG : RefinedBound α E k G) :
    RefinedBound α E k fun ℓ => F ℓ - G ℓ := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

theorem zero : RefinedBound α E k fun _ => 0 :=
  ⟨0, le_rfl, fun A hA ℓ => by simp⟩

theorem sum {ι : Type*} (s : Finset ι) {F : ι → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, RefinedBound α E k (F i)) : RefinedBound α E k fun ℓ => ∑ i ∈ s, F i ℓ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : RefinedBound α E k fun _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mul (hF : RefinedBound α E k F) (hG : RefinedBound α E' k' G) (hd : Disjoint E E') :
    RefinedBound α (E ∪ E') (k + k') fun ℓ => F ℓ * G ℓ := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C * D, mul_nonneg hC hD, fun A hA ℓ => ?_⟩
  rw [norm_mul, lineWeight_union α hd, pow_add]
  calc ‖F ℓ‖ * ‖G ℓ‖ ≤ (C * lineWeight α E A * Real.sqrt (1 + loopNorm A ℓ) ^ k) *
        (D * lineWeight α E' A * Real.sqrt (1 + loopNorm A ℓ) ^ k') :=
        mul_le_mul (hF A hA ℓ) (hG A hA ℓ) (norm_nonneg _)
          (by have := lineWeight_nonneg α E A; positivity)
    _ = _ := by ring

/-- **Products over distinct lines.** If each factor `g i` is bounded by the single line `e i`,
with `e` injective on `s`, the product is bounded by the lines `e '' s` with exponent `|s|`. -/
theorem prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → Fin (m + 1))
    (he : Set.InjOn e s) {g : ι → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hg : ∀ i ∈ s, RefinedBound α {e i} 1 (g i)) :
    RefinedBound α (s.image e) s.card fun ℓ => ∏ i ∈ s, g i ℓ := by
  induction s using Finset.induction_on with
  | empty => simpa using (const 1 : RefinedBound α ∅ 0 fun _ => (1 : ℂ))
  | insert a s ha ih =>
    have he' : Set.InjOn e s := he.mono (by simp)
    have hea : e a ∉ s.image e := by
      intro h
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp h
      have : b = a := he (by simp [hb]) (by simp) hba
      exact ha (this ▸ hb)
    have h1 := (hg a (Finset.mem_insert_self a s)).mul
      (ih he' fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (Finset.disjoint_singleton_left.mpr hea)
    simp only [Finset.prod_insert ha, Finset.image_insert, Finset.card_insert_of_notMem ha]
    rw [Finset.insert_eq]
    exact h1.mono le_rfl (by omega)

end RefinedBound

/-- **A component of a line momentum is bounded by its line**: `|α_e·ℓ^ν + p_{eν}| ≤
(1 + |p_{eν}|) (1 + α_eᵀA⁻¹α_e)^{1/2} (1 + loopNorm A ℓ)^{1/2}`. -/
theorem refinedBound_lineMomentum {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (e : Fin (m + 1)) (ν : Fin 4) :
    RefinedBound α {e} 1 fun ℓ => ((lineMomentum α p e ℓ ν : ℝ) : ℂ) := by
  refine ⟨1 + |p e ν|, by positivity, fun A hA ℓ => ?_⟩
  rw [norm_real, Real.norm_eq_abs, lineWeight_singleton, pow_one]
  have hcs := abs_dotProduct_le hA (α e) (fun s => ℓ s ν)
  have hq := Real.sqrt_le_sqrt (qf_le_loopNorm hA ℓ ν)
  have hN1 := sqrt_one_add_loopNorm_one_le hA ℓ
  have hQ1 := one_le_sqrt_lineFactor α hA e
  have hQ : Real.sqrt (α e ⬝ᵥ A⁻¹ *ᵥ α e) ≤ Real.sqrt (1 + α e ⬝ᵥ A⁻¹ *ᵥ α e) :=
    Real.sqrt_le_sqrt (by linarith)
  have hN : Real.sqrt (loopNorm A ℓ) ≤ Real.sqrt (1 + loopNorm A ℓ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hlm : lineMomentum α p e ℓ ν = α e ⬝ᵥ (fun s => ℓ s ν) + p e ν := by
    simp [lineMomentum, dotProduct]
  rw [hlm]
  have h1 : |α e ⬝ᵥ (fun s => ℓ s ν)| ≤
      Real.sqrt (1 + α e ⬝ᵥ A⁻¹ *ᵥ α e) * Real.sqrt (1 + loopNorm A ℓ) :=
    hcs.trans (mul_le_mul hQ (hq.trans hN) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have h2 : 1 ≤ Real.sqrt (1 + α e ⬝ᵥ A⁻¹ *ᵥ α e) * Real.sqrt (1 + loopNorm A ℓ) :=
    one_le_mul_of_one_le_of_one_le hQ1 hN1
  calc |α e ⬝ᵥ (fun s => ℓ s ν) + p e ν| ≤ |α e ⬝ᵥ (fun s => ℓ s ν)| + |p e ν| := abs_add_le _ _
    _ ≤ Real.sqrt (1 + α e ⬝ᵥ A⁻¹ *ᵥ α e) * Real.sqrt (1 + loopNorm A ℓ) +
        |p e ν| * (Real.sqrt (1 + α e ⬝ᵥ A⁻¹ *ᵥ α e) * Real.sqrt (1 + loopNorm A ℓ)) := by
        gcongr
        nlinarith [abs_nonneg (p e ν)]
    _ = _ := by ring

/-! ### Finite differences in the energy directions -/

namespace LoopQuartic

variable (P : LoopQuartic)

/-- The quadratic part in an energy direction: `∑ₛᵣ Hₛ₀,ᵣ₀(X) wₛ wᵣ`. -/
noncomputable def energyHess (X : LoopIndex → ℂ) (w : Fin 2 → ℝ) : ℂ :=
  ∑ s, ∑ r, P.hess X (s, 0) (r, 0) * ((w s * w r : ℝ) : ℂ)

/-- The quartic part in an energy direction: `∑ Rₛ₀,ᵣ₀,ₜ₀,q₀ wₛ wᵣ wₜ w_q`. -/
noncomputable def energyQuart (w : Fin 2 → ℝ) : ℂ :=
  ∑ s, ∑ r, ∑ t, ∑ q, P.quart (s, 0) (r, 0) (t, 0) (q, 0) * ((w s * w r * w t * w q : ℝ) : ℂ)

theorem eval_add_add_eval_sub_energy (ℓ : Fin 2 → Fin 4 → ℝ) (w : Fin 2 → ℝ) :
    P.eval (ℓ + loopMomenta w 0) + P.eval (ℓ - loopMomenta w 0) =
      2 * (P.eval ℓ + P.energyHess (loopComp ℓ) w + P.energyQuart w) := by
  rw [P.eval_add_add_eval_sub, sum_sum_hess_loopComp_energy, quartPart_loopComp_energy]
  rfl

theorem energyHess_two_smul (X : LoopIndex → ℂ) (w : Fin 2 → ℝ) :
    P.energyHess X ((2 : ℝ) • w) = 4 * P.energyHess X w := by
  unfold energyHess
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem energyQuart_two_smul (w : Fin 2 → ℝ) :
    P.energyQuart ((2 : ℝ) • w) = 16 * P.energyQuart w := by
  unfold energyQuart
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The quadratic part as a finite difference of values of `P`. -/
theorem energyHess_eq_fd (ℓ : Fin 2 → Fin 4 → ℝ) (w : Fin 2 → ℝ) :
    24 * P.energyHess (loopComp ℓ) w =
      16 * (P.eval (ℓ + loopMomenta w 0) + P.eval (ℓ - loopMomenta w 0) - 2 * P.eval ℓ) -
        (P.eval (ℓ + loopMomenta ((2 : ℝ) • w) 0) + P.eval (ℓ - loopMomenta ((2 : ℝ) • w) 0) -
          2 * P.eval ℓ) := by
  rw [eval_add_add_eval_sub_energy, eval_add_add_eval_sub_energy, energyHess_two_smul,
    energyQuart_two_smul]
  ring

/-- The quartic part as a finite difference of values of `P`. -/
theorem energyQuart_eq_fd (w : Fin 2 → ℝ) :
    24 * P.energyQuart w =
      (P.eval (loopMomenta ((2 : ℝ) • w) 0) + P.eval (-loopMomenta ((2 : ℝ) • w) 0) -
          2 * P.eval 0) -
        4 * (P.eval (loopMomenta w 0) + P.eval (-loopMomenta w 0) - 2 * P.eval 0) := by
  have h1 := P.eval_add_add_eval_sub_energy 0 w
  have h2 := P.eval_add_add_eval_sub_energy 0 ((2 : ℝ) • w)
  simp only [zero_add, zero_sub] at h1 h2
  rw [h1, h2, energyHess_two_smul, energyQuart_two_smul]
  ring

/-- The energy contraction of the quadratic coefficients, for `A⁻¹ = w₁w₁ᵀ + w₂w₂ᵀ`. -/
theorem energyContractTwo_eq_of_decomp {A : Matrix (Fin 2) (Fin 2) ℝ} {w₁ w₂ : Fin 2 → ℝ}
    (hG : ∀ s r, A⁻¹ s r = w₁ s * w₁ r + w₂ s * w₂ r) (X : LoopIndex → ℂ) :
    P.energyContractTwo A X = P.energyHess X w₁ + P.energyHess X w₂ := by
  unfold energyContractTwo energyHess
  simp only [hG]
  push_cast
  simp only [Fin.sum_univ_two]
  ring

/-- The energy contraction of the quartic coefficients, for `A⁻¹ = w₁w₁ᵀ + w₂w₂ᵀ`. -/
theorem energyContractFour_eq_of_decomp {A : Matrix (Fin 2) (Fin 2) ℝ} {w₁ w₂ : Fin 2 → ℝ}
    (hG : ∀ s r, A⁻¹ s r = w₁ s * w₁ r + w₂ s * w₂ r) :
    P.energyContractFour A = 2 * P.energyQuart w₁ + 2 * P.energyQuart w₂ +
      (P.energyQuart (w₁ + w₂) + P.energyQuart (w₁ - w₂)) / 2 := by
  unfold energyContractFour energyQuart matPair
  simp only [hG, Pi.add_apply, Pi.sub_apply]
  push_cast
  simp only [Fin.sum_univ_two]
  ring

end LoopQuartic

/-! ### The Cholesky factorization of `A⁻¹` -/

section Decomp

variable {A : Matrix (Fin 2) (Fin 2) ℝ}

/-- `A⁻¹ = w₁w₁ᵀ + w₂w₂ᵀ` for a positive definite `A`. -/
theorem exists_inv_decomp (hA : A.PosDef) :
    ∃ w₁ w₂ : Fin 2 → ℝ, ∀ s r, A⁻¹ s r = w₁ s * w₁ r + w₂ s * w₂ r := by
  have hG := hA.inv
  have h00 : 0 < A⁻¹ 0 0 := hG.diag_pos
  have hdet : 0 < A⁻¹.det := hG.det_pos
  have hs : A⁻¹ 1 0 = A⁻¹ 0 1 := posDef_symm hG
  rw [det_fin_two, hs] at hdet
  set a := A⁻¹ 0 0
  set b := A⁻¹ 0 1
  set c := A⁻¹ 1 1
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr h00).ne'
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt h00.le
  have hD : 0 ≤ (a * c - b * b) / a := div_nonneg hdet.le h00.le
  have hsD : Real.sqrt ((a * c - b * b) / a) * Real.sqrt ((a * c - b * b) / a) =
      (a * c - b * b) / a := Real.mul_self_sqrt hD
  refine ⟨![Real.sqrt a, b / Real.sqrt a], ![0, Real.sqrt ((a * c - b * b) / a)], ?_⟩
  rw [Fin.forall_fin_two, Fin.forall_fin_two, Fin.forall_fin_two]
  simp only [cons_val_zero, cons_val_one]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show a = _
    rw [hsq]; ring
  · show b = _
    rw [mul_div_cancel₀ _ hsa]; ring
  · rw [hs, div_mul_cancel₀ _ hsa]; ring
  · show c = _
    rw [hsD, div_mul_div_comm, hsq]
    field_simp
    ring

/-- For `A⁻¹ = w₁w₁ᵀ + w₂w₂ᵀ`, `w₁ᵀAw₁ + w₂ᵀAw₂ = tr(A A⁻¹) = 2`. -/
theorem qf_add_qf_eq_two_of_decomp (hA : A.PosDef) {w₁ w₂ : Fin 2 → ℝ}
    (hG : ∀ s r, A⁻¹ s r = w₁ s * w₁ r + w₂ s * w₂ r) :
    w₁ ⬝ᵥ A *ᵥ w₁ + w₂ ⬝ᵥ A *ᵥ w₂ = 2 := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hI := mul_nonsing_inv A hu
  have h1 : (A * A⁻¹) 0 0 = 1 := by rw [hI]; simp
  have h2 : (A * A⁻¹) 1 1 = 1 := by rw [hI]; simp
  simp only [mul_apply, Fin.sum_univ_two, hG] at h1 h2
  have hs := posDef_symm hA
  simp only [dotProduct_mulVec_fin_two, hs] at h1 h2 ⊢
  linear_combination h1 + h2

theorem qf_le_two_of_decomp (hA : A.PosDef) {w₁ w₂ : Fin 2 → ℝ}
    (hG : ∀ s r, A⁻¹ s r = w₁ s * w₁ r + w₂ s * w₂ r) :
    w₁ ⬝ᵥ A *ᵥ w₁ ≤ 2 ∧ w₂ ⬝ᵥ A *ᵥ w₂ ≤ 2 := by
  have h := qf_add_qf_eq_two_of_decomp hA hG
  have h1 := dotProduct_mulVec_self_nonneg hA w₁
  have h2 := dotProduct_mulVec_self_nonneg hA w₂
  constructor <;> linarith

end Decomp

/-! ### Bounds on the energy contractions from a bound on `P` -/

section ContractBounds

variable (P : LoopQuartic) {A : Matrix (Fin 2) (Fin 2) ℝ}

theorem norm_add_sub_two_mul_le (a b e : ℂ) : ‖a + b - 2 * e‖ ≤ ‖a‖ + ‖b‖ + 2 * ‖e‖ := by
  have h1 := norm_sub_le (a + b) (2 * e)
  have h2 := norm_add_le a b
  have h3 : ‖(2 : ℂ) * e‖ = 2 * ‖e‖ := by rw [norm_mul]; norm_num
  linarith

/-- The quadratic part in a direction of bounded `A`-length is bounded like `P`. -/
theorem norm_energyHess_le (hA : A.PosDef) {K : ℝ} (hK : 0 ≤ K)
    (hP : ∀ ℓ, ‖P.eval ℓ‖ ≤ K * (1 + loopNorm A ℓ) ^ 2) (ℓ : Fin 2 → Fin 4 → ℝ)
    {w : Fin 2 → ℝ} {c : ℝ} (hc : 0 ≤ c) (hw : w ⬝ᵥ A *ᵥ w ≤ c) :
    ‖P.energyHess (loopComp ℓ) w‖ ≤ 3 * (K * (2 * (1 + 8 * c)) ^ 2 * (1 + loopNorm A ℓ) ^ 2) := by
  set N := loopNorm A ℓ with hN
  have hN0 : 0 ≤ N := loopNorm_nonneg hA ℓ
  set B := K * (2 * (1 + 8 * c)) ^ 2 * (1 + N) ^ 2 with hB
  have hpt : ∀ ℓ', loopNorm A ℓ' ≤ 2 * N + 8 * c → ‖P.eval ℓ'‖ ≤ B := by
    intro ℓ' h
    have h0 := loopNorm_nonneg hA ℓ'
    calc ‖P.eval ℓ'‖ ≤ K * (1 + loopNorm A ℓ') ^ 2 := hP ℓ'
      _ ≤ K * (2 * (1 + 8 * c) * (1 + N)) ^ 2 := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) ?_ 2) hK
          nlinarith [mul_nonneg hc hN0]
      _ = B := by rw [hB]; ring
  have hδ := loopNorm_loopMomenta_energy A w
  have hδ2 : loopNorm A (loopMomenta ((2 : ℝ) • w) 0) = 4 * (w ⬝ᵥ A *ᵥ w) := by
    rw [loopNorm_loopMomenta_energy, qf_smul]; ring
  have hw0 := dotProduct_mulVec_self_nonneg hA w
  have e0 := hpt ℓ (by linarith)
  have e1 := hpt (ℓ + loopMomenta w 0) ((loopNorm_add_le hA _ _).trans (by linarith))
  have e2 := hpt (ℓ - loopMomenta w 0) ((loopNorm_sub_le hA _ _).trans (by linarith))
  have e3 := hpt (ℓ + loopMomenta ((2 : ℝ) • w) 0) ((loopNorm_add_le hA _ _).trans (by linarith))
  have e4 := hpt (ℓ - loopMomenta ((2 : ℝ) • w) 0) ((loopNorm_sub_le hA _ _).trans (by linarith))
  have hfd := congrArg norm (P.energyHess_eq_fd ℓ w)
  rw [norm_mul, show ‖(24 : ℂ)‖ = 24 by norm_num] at hfd
  have hr := norm_sub_le
    (16 * (P.eval (ℓ + loopMomenta w 0) + P.eval (ℓ - loopMomenta w 0) - 2 * P.eval ℓ))
    (P.eval (ℓ + loopMomenta ((2 : ℝ) • w) 0) + P.eval (ℓ - loopMomenta ((2 : ℝ) • w) 0) -
      2 * P.eval ℓ)
  rw [norm_mul, show ‖(16 : ℂ)‖ = 16 by norm_num] at hr
  have a1 := norm_add_sub_two_mul_le (P.eval (ℓ + loopMomenta w 0))
    (P.eval (ℓ - loopMomenta w 0)) (P.eval ℓ)
  have a2 := norm_add_sub_two_mul_le (P.eval (ℓ + loopMomenta ((2 : ℝ) • w) 0))
    (P.eval (ℓ - loopMomenta ((2 : ℝ) • w) 0)) (P.eval ℓ)
  have hB0 : 0 ≤ B := by positivity
  nlinarith

/-- The quartic part in a direction of bounded `A`-length is bounded like `P` at the origin. -/
theorem norm_energyQuart_le (hA : A.PosDef) {K : ℝ} (hK : 0 ≤ K)
    (hP : ∀ ℓ, ‖P.eval ℓ‖ ≤ K * (1 + loopNorm A ℓ) ^ 2) {w : Fin 2 → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hw : w ⬝ᵥ A *ᵥ w ≤ c) :
    ‖P.energyQuart w‖ ≤ K * (1 + 4 * c) ^ 2 := by
  set B := K * (1 + 4 * c) ^ 2 with hB
  have hpt : ∀ ℓ', loopNorm A ℓ' ≤ 4 * c → ‖P.eval ℓ'‖ ≤ B := by
    intro ℓ' h
    have h0 := loopNorm_nonneg hA ℓ'
    calc ‖P.eval ℓ'‖ ≤ K * (1 + loopNorm A ℓ') ^ 2 := hP ℓ'
      _ ≤ B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2) hK
  have hδ := loopNorm_loopMomenta_energy A w
  have hδ2 : loopNorm A (loopMomenta ((2 : ℝ) • w) 0) = 4 * (w ⬝ᵥ A *ᵥ w) := by
    rw [loopNorm_loopMomenta_energy, qf_smul]; ring
  have hw0 := dotProduct_mulVec_self_nonneg hA w
  have e0 := hpt 0 (by rw [loopNorm_zero]; linarith)
  have e1 := hpt (loopMomenta w 0) (by linarith)
  have e2 := hpt (-loopMomenta w 0) (by rw [loopNorm_neg]; linarith)
  have e3 := hpt (loopMomenta ((2 : ℝ) • w) 0) (by linarith)
  have e4 := hpt (-loopMomenta ((2 : ℝ) • w) 0) (by rw [loopNorm_neg]; linarith)
  have hfd := congrArg norm (P.energyQuart_eq_fd w)
  rw [norm_mul, show ‖(24 : ℂ)‖ = 24 by norm_num] at hfd
  have hr := norm_sub_le
    (P.eval (loopMomenta ((2 : ℝ) • w) 0) + P.eval (-loopMomenta ((2 : ℝ) • w) 0) -
      2 * P.eval 0)
    (4 * (P.eval (loopMomenta w 0) + P.eval (-loopMomenta w 0) - 2 * P.eval 0))
  rw [norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num] at hr
  have a1 := norm_add_sub_two_mul_le (P.eval (loopMomenta ((2 : ℝ) • w) 0))
    (P.eval (-loopMomenta ((2 : ℝ) • w) 0)) (P.eval 0)
  have a2 := norm_add_sub_two_mul_le (P.eval (loopMomenta w 0)) (P.eval (-loopMomenta w 0))
    (P.eval 0)
  have hB0 : 0 ≤ B := by positivity
  nlinarith

/-- **The quadratic energy contraction is bounded like `P`.** -/
theorem norm_energyContractTwo_le_of_bound (hA : A.PosDef) {K : ℝ} (hK : 0 ≤ K)
    (hP : ∀ ℓ, ‖P.eval ℓ‖ ≤ K * (1 + loopNorm A ℓ) ^ 2) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ‖P.energyContractTwo A (loopComp ℓ)‖ ≤ 6 * 34 ^ 2 * K * (1 + loopNorm A ℓ) ^ 2 := by
  obtain ⟨w₁, w₂, hG⟩ := exists_inv_decomp hA
  obtain ⟨h1, h2⟩ := qf_le_two_of_decomp hA hG
  rw [P.energyContractTwo_eq_of_decomp hG]
  have b1 := norm_energyHess_le P hA hK hP ℓ (by norm_num : (0 : ℝ) ≤ 2) h1
  have b2 := norm_energyHess_le P hA hK hP ℓ (by norm_num : (0 : ℝ) ≤ 2) h2
  calc _ ≤ ‖P.energyHess (loopComp ℓ) w₁‖ + ‖P.energyHess (loopComp ℓ) w₂‖ := norm_add_le _ _
    _ ≤ _ := add_le_add b1 b2
    _ = _ := by ring

/-- **The quartic energy contraction is bounded like `P` at the origin.** -/
theorem norm_energyContractFour_le_of_bound (hA : A.PosDef) {K : ℝ} (hK : 0 ≤ K)
    (hP : ∀ ℓ, ‖P.eval ℓ‖ ≤ K * (1 + loopNorm A ℓ) ^ 2) :
    ‖P.energyContractFour A‖ ≤ 5 * 33 ^ 2 * K := by
  obtain ⟨w₁, w₂, hG⟩ := exists_inv_decomp hA
  obtain ⟨h1, h2⟩ := qf_le_two_of_decomp hA hG
  have h0₁ := dotProduct_mulVec_self_nonneg hA w₁
  have h0₂ := dotProduct_mulVec_self_nonneg hA w₂
  have hp : (w₁ + w₂) ⬝ᵥ A *ᵥ (w₁ + w₂) ≤ 8 := (qf_add_le hA w₁ w₂).trans (by linarith)
  have hm : (w₁ - w₂) ⬝ᵥ A *ᵥ (w₁ - w₂) ≤ 8 := by
    rw [sub_eq_add_neg]
    refine (qf_add_le hA w₁ (-w₂)).trans ?_
    have := qf_smul A (-1) w₂
    simp only [neg_smul, one_smul, even_two, Even.neg_pow, one_pow, one_mul] at this
    rw [this]
    linarith
  have b1 := norm_energyQuart_le P hA hK hP (by norm_num : (0 : ℝ) ≤ 8) (h1.trans (by norm_num))
  have b2 := norm_energyQuart_le P hA hK hP (by norm_num : (0 : ℝ) ≤ 8) (h2.trans (by norm_num))
  have b3 := norm_energyQuart_le P hA hK hP (by norm_num : (0 : ℝ) ≤ 8) hp
  have b4 := norm_energyQuart_le P hA hK hP (by norm_num : (0 : ℝ) ≤ 8) hm
  rw [P.energyContractFour_eq_of_decomp hG]
  have t1 := norm_add_le (2 * P.energyQuart w₁ + 2 * P.energyQuart w₂)
    ((P.energyQuart (w₁ + w₂) + P.energyQuart (w₁ - w₂)) / 2)
  have t2 := norm_add_le (2 * P.energyQuart w₁) (2 * P.energyQuart w₂)
  have t3 := norm_add_le (P.energyQuart (w₁ + w₂)) (P.energyQuart (w₁ - w₂))
  rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at t2
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num] at t1
  nlinarith

end ContractBounds

end QED.Integration.TwoLoop

end
