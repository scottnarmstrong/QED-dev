/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Moment
import Mathlib.Tactic.Ring

/-!
# The completed square along a line of external momenta

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A1. Along the line `s ↦ p + s q` of external line momenta (loop matrix `α`, Feynman point
`z`), the derivative of the line denominator `Dᵢ = kᵢ·kᵢ + Mᵢ² - iε` is the affine form
`∂ₛDᵢ(ℓ) = 2 kᵢ(ℓ)·qᵢ = dLineC (pᵢ + s qᵢ) qᵢ + dLineL αᵢ qᵢ · ℓ` (`dLineC_add_linF`). Then:

* `loopShift_add_smul`: the shift `S` is affine along the line, `S' = S(q)`;
* `hasDerivAt_symanzikV`: `V' = ∑ᵢ zᵢ ∂ₛDᵢ(-S)` (the derivative of the completed square at its
  centre);
* `metric_mul_dLineL`: `G (∑ᵢ zᵢ dLineL αᵢ qᵢ) = 2 S(q)`, `G = loopMetricInv A(z)`.
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.WI2

open QED.Integration.TwoLoop QED.Minkowski

variable {m : ℕ}

/-- The constant part `2 P·q` of the derivative of a line denominator. -/
def dLineC (P q : Fin 4 → ℝ) : ℂ := 2 * (dot P q : ℂ)

/-- The linear part `ℓ ↦ 2 (∑ₛ aₛ ℓₛ)·q` of the derivative of a line denominator. -/
def dLineL (a : Fin 2 → ℝ) (q : Fin 4 → ℝ) : LoopIndex → ℂ :=
  fun b => 2 * (a b.1 : ℂ) * (lower q b.2 : ℂ)

/-- The derivative of a line denominator is `2 k(ℓ)·q`. -/
theorem dLineC_add_linF (a : Fin 2 → ℝ) (P q : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    dLineC P q + linF (dLineL a q) (loopComp ℓ) =
      2 * (dot (fun μ => ∑ s, a s * ℓ s μ + P μ) q : ℂ) := by
  simp only [dLineC, dLineL, linF, loopComp, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_four, dot, lower, metric]
  push_cast
  simp
  ring

/-! ### The shift along the line -/

theorem loopShift_add_smul (α : Fin (m + 1) → Fin 2 → ℝ) (p q : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) (s : ℝ) :
    loopShift α (p + s • q) z = loopShift α p z + s • loopShift α q z := by
  funext r μ
  rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    QED.TwoLoop.LimitCovariance.loopShift_apply, QED.TwoLoop.LimitCovariance.loopShift_apply,
    QED.TwoLoop.LimitCovariance.loopShift_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem hasDerivAt_loopComp_shift (α : Fin (m + 1) → Fin 2 → ℝ) (p q : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) (t : ℝ) (a : LoopIndex) :
    HasDerivAt (fun s => loopComp (-loopShift α (p + s • q) z) a)
      (loopComp (-loopShift α q z) a) t := by
  simp only [loopShift_add_smul, loopComp, Pi.neg_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  have h := (((hasDerivAt_id t).mul_const (loopShift α q z a.1 a.2)).const_add
    (loopShift α p z a.1 a.2)).neg.ofReal_comp
  convert h using 1
  · funext s
    simp
  · simp

/-! ### The derivative of the second Symanzik function -/

theorem coefVec_add_mul (α : Fin (m + 1) → Fin 2 → ℝ) (z a b : Fin (m + 1) → ℝ) (s : ℝ) :
    coefVec α z (fun i => a i + s * b i) = coefVec α z a + s • coefVec α z b := by
  funext r
  simp only [coefVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The derivative of the remainder of one column** along `a + s b`: with the centre
`y = -A⁻¹ β(a + t b)`, it is `2 ∑ᵢ zᵢ (αᵢ·y + aᵢ + t bᵢ) bᵢ`. -/
theorem hasDerivAt_remainder (α : Fin (m + 1) → Fin 2 → ℝ) (z a b : Fin (m + 1) → ℝ) (t : ℝ) :
    HasDerivAt (fun s => remainder α z (fun i => a i + s * b i))
      (2 * ∑ i, z i * ((∑ r, α i r *
        (-((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z (fun i => a i + t * b i))) r) +
          (a i + t * b i)) * b i) t := by
  set B := (symanzikMatrix α z)⁻¹ with hB
  have hsym : B 0 1 = B 1 0 := by
    have h := Matrix.transpose_nonsing_inv (symanzikMatrix α z)
    rw [(symanzikMatrix_isSymm α z).eq] at h
    calc B 0 1 = (symanzikMatrix α z)⁻¹ᵀ 1 0 := rfl
      _ = B 1 0 := by rw [h]
  set ca := coefVec α z a
  set cb := coefVec α z b
  have hR : ∀ s, remainder α z (fun i => a i + s * b i) =
      ∑ i, z i * (a i + s * b i) ^ 2 -
        ((ca 0 + s * cb 0) * (B 0 0 * (ca 0 + s * cb 0) + B 0 1 * (ca 1 + s * cb 1)) +
          (ca 1 + s * cb 1) * (B 1 0 * (ca 0 + s * cb 0) + B 1 1 * (ca 1 + s * cb 1))) := by
    intro s
    simp only [remainder, coefVec_add_mul, dotProduct, mulVec, Fin.sum_univ_two, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, ca, cb, hB]
  simp only [hR]
  have hl : ∀ c d : ℝ, HasDerivAt (fun s => c + s * d) d t := fun c d => by
    simpa using ((hasDerivAt_id t).mul_const d).const_add c
  have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    ((hl (a i) (b i)).pow 2).const_mul (z i)
  have h2 := ((hl (ca 0) (cb 0)).mul (((hl (ca 0) (cb 0)).const_mul (B 0 0)).add
    ((hl (ca 1) (cb 1)).const_mul (B 0 1)))).add ((hl (ca 1) (cb 1)).mul
    (((hl (ca 0) (cb 0)).const_mul (B 1 0)).add ((hl (ca 1) (cb 1)).const_mul (B 1 1))))
  convert h1.sub h2 using 1
  have hs : ∑ i, z i * ((∑ r, α i r * (-(B *ᵥ coefVec α z (fun i => a i + t * b i))) r) +
      (a i + t * b i)) * b i =
      -(B *ᵥ (ca + t • cb)) 0 * cb 0 - (B *ᵥ (ca + t • cb)) 1 * cb 1 +
        ∑ i, z i * (a i + t * b i) * b i := by
    rw [coefVec_add_mul]
    simp only [cb, coefVec, Fin.sum_univ_two, Pi.neg_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hsum : ∑ i, z i * (((2 : ℕ) : ℝ) * (a i + t * b i) ^ (2 - 1) * b i) =
      2 * ∑ i, z i * (a i + t * b i) * b i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by norm_num; ring
  rw [hs, hsum]
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsym]
  ring

/-- **The derivative of `V` along the line** is `∑ᵢ zᵢ ∂ₛDᵢ` at the centre `ℓ = -S`. -/
theorem hasDerivAt_symanzikV (α : Fin (m + 1) → Fin 2 → ℝ) (p q : Fin (m + 1) → Fin 4 → ℝ)
    (M z : Fin (m + 1) → ℝ) (t : ℝ) :
    HasDerivAt (fun s => symanzikV α (p + s • q) M z)
      (∑ i, z i * (2 * dot (lineMomentum α (p + t • q) i (-loopShift α (p + t • q) z))
        (q i))) t := by
  have hV : ∀ s, symanzikV α (p + s • q) M z = ∑ i, z i * M i ^ 2 -
      remainder α z (fun i => p i 0 + s * q i 0) +
      ∑ c : Fin 3, remainder α z (fun i => p i c.succ + s * q i c.succ) := fun s => by
    simp only [symanzikV_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [hV]
  have h := ((hasDerivAt_const t (∑ i, z i * M i ^ 2)).sub
    (hasDerivAt_remainder α z (fun i => p i 0) (fun i => q i 0) t)).add
    (HasDerivAt.fun_sum (u := Finset.univ) fun (c : Fin 3) _ =>
      hasDerivAt_remainder α z (fun i => p i c.succ) (fun i => q i c.succ) t)
  convert h using 1
  have hy : ∀ (μ : Fin 4) (r : Fin 2),
      (-((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z (fun i => p i μ + t * q i μ))) r =
        (-loopShift α (p + t • q) z) r μ := fun μ r => by
    simp only [Pi.neg_apply, QED.TwoLoop.LimitCovariance.loopShift_apply, mulVec, dotProduct,
      coefVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [hy]
  set ℓ := -loopShift α (p + t • q) z
  have hk : ∀ i, z i * (2 * dot (lineMomentum α (p + t • q) i ℓ) (q i)) =
      -(2 * (z i * ((∑ r, α i r * ℓ r 0) + (p i 0 + t * q i 0)) * q i 0)) +
        ∑ c : Fin 3, 2 * (z i * ((∑ r, α i r * ℓ r c.succ) + (p i c.succ + t * q i c.succ)) *
          q i c.succ) := fun i => by
    rw [minkowski_dot_eq, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    simp only [lineMomentum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [hk, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := (Finset.univ : Finset (Fin 3)))]
  ring

/-- **`G (∑ᵢ zᵢ dLineL αᵢ qᵢ) = 2 S(q)`** for `G = loopMetricInv A(z)`. -/
theorem sum_loopMetricInv_dLineL (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) (a : LoopIndex) :
    ∑ d, ((loopMetricInv (symanzikMatrix α z) a d : ℝ) : ℂ) *
        (∑ i, (z i : ℂ) * dLineL (α i) (q i) d) =
      2 * loopComp (loopShift α q z) a := by
  obtain ⟨s, μ⟩ := a
  set B := (symanzikMatrix α z)⁻¹
  have per : ∀ i, ∑ d, ((loopMetricInv (symanzikMatrix α z) (s, μ) d : ℝ) : ℂ) *
      dLineL (α i) (q i) d = 2 * ∑ r, ((B s r * (α i r * q i μ) : ℝ) : ℂ) := fun i => by
    simp only [loopMetricInv, dLineL, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_four, lower, metric, B]
    fin_cases μ <;> simp <;> ring
  have lhs : ∑ d, ((loopMetricInv (symanzikMatrix α z) (s, μ) d : ℝ) : ℂ) *
      (∑ i, (z i : ℂ) * dLineL (α i) (q i) d) = ∑ i, (z i : ℂ) *
        ∑ d, ((loopMetricInv (symanzikMatrix α z) (s, μ) d : ℝ) : ℂ) *
          dLineL (α i) (q i) d := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [lhs, loopComp, QED.TwoLoop.LimitCovariance.loopShift_apply]
  simp only [per]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end QED.GradedProof.WI2

end
