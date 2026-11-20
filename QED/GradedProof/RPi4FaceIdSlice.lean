/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdSE

/-!
# (R-Π₄) step L6d3: the reduced bracket depends only on a loop-`0` slice

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3.

The reduced one-loop bracket `faceIdRedBr n R X v` contracts only with `eS 0`, i.e. it
differentiates only along loop `0`. Hence at a point `X = (x, y)` it depends on the quartic `R`
only through the slice `ℓ₀ ↦ R(ℓ₀, y)`: if `R(ℓ₀, y) = P(ℓ₀, 0)` for every real `ℓ₀`, then
`faceIdRedBr n R (x, y) v = faceIdRedBr n P (x, 0) v` (**`faceId_faceIdRedBr_slice`**). This
removes the loop-`1` point `-b₁(W)` of the self-energy face (`faceId_faceIdVal_se`).

* `faceId_loopComp_slice_add`, `faceId_hessForm_slice` (loop-`0` second differences);
* `faceId_cTwoG_eS0_slice`, `faceId_hess_center`, `faceId_cFourG_eS0_slice`;
* `faceId_polar_eS0`, `faceId_cTwoG_center`;
* **`faceId_faceIdRedBr_slice`**, `faceId_eval_lmap_faceIdMb`, **`faceId_faceIdVal_se_slice`**
  (the self-energy face value as the integral of reduced brackets at `(-P₀, 0)` of any family
  `T W` representing the slices `ℓ₀ ↦ Q(ℓ₀, -b₁(W) - b(W) ℓ₀)`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.TwoLoop.PauliZeroExplicit (sum_mul_eq_of_quadForm)
open QED.TwoLoop.LimitCovariance (hessForm_eq)

/-- The loop-`0` direction of a real vector on `LoopIndex`. -/
def faceIdDir0 (z : LoopIndex → ℝ) : Fin 4 → ℝ := fun μ => z (0, μ)

theorem faceId_loopComp_slice_add (x y d : Fin 4 → ℝ) (t : ℂ) (ht : t = 1 ∨ t = -1 ∨ t = 2 ∨
    t = -2) :
    loopComp ![x, y] + t • loopComp ![d, 0] =
      loopComp ![x + (t.re : ℝ) • d, y] := by
  funext a
  obtain ⟨a1, a2⟩ := a
  rcases ht with rfl | rfl | rfl | rfl <;> fin_cases a1 <;> simp [loopComp]

theorem faceId_loopComp_slice_sub (x y d : Fin 4 → ℝ) (t : ℂ) (ht : t = 1 ∨ t = 2) :
    loopComp ![x, y] - t • loopComp ![d, 0] =
      loopComp ![x - (t.re : ℝ) • d, y] := by
  funext a
  obtain ⟨a1, a2⟩ := a
  rcases ht with rfl | rfl <;> fin_cases a1 <;> simp [loopComp]

variable {R P : LoopQuartic}

/-- **The loop-`0` second difference along a slice.** -/
theorem faceId_hessForm_slice {y : Fin 4 → ℝ}
    (h : ∀ ℓ₀ : Fin 4 → ℝ, R.eval ![ℓ₀, y] = P.eval ![ℓ₀, 0]) (x d : Fin 4 → ℝ) :
    ∑ a, ∑ b, R.hess (loopComp ![x, y]) a b * (loopComp ![d, 0] a * loopComp ![d, 0] b) =
      ∑ a, ∑ b, P.hess (loopComp ![x, 0]) a b * (loopComp ![d, 0] a * loopComp ![d, 0] b) := by
  rw [hessForm_eq, hessForm_eq]
  have e1 : (1 : ℂ) • loopComp ![d, 0] = loopComp ![d, 0] := one_smul _ _
  have hp : ∀ z : Fin 4 → ℝ, ∀ t : ℂ, t = 1 ∨ t = -1 ∨ t = 2 ∨ t = -2 →
      R.evalC (loopComp ![x, y] + t • loopComp ![d, 0]) =
        P.evalC (loopComp ![x, 0] + t • loopComp ![d, 0]) := fun _ t ht => by
    rw [faceId_loopComp_slice_add x y d t ht, faceId_loopComp_slice_add x 0 d t ht]
    exact h _
  have hm : ∀ t : ℂ, t = 1 ∨ t = 2 →
      R.evalC (loopComp ![x, y] - t • loopComp ![d, 0]) =
        P.evalC (loopComp ![x, 0] - t • loopComp ![d, 0]) := fun t ht => by
    rw [faceId_loopComp_slice_sub x y d t ht, faceId_loopComp_slice_sub x 0 d t ht]
    exact h _
  have h0 : R.evalC (loopComp ![x, y]) = P.evalC (loopComp ![x, 0]) := h x
  have a1 := hp x 1 (Or.inl rfl)
  have a2 := hm 1 (Or.inl rfl)
  have a3 := hp x 2 (Or.inr (Or.inr (Or.inl rfl)))
  have a4 := hm 2 (Or.inr rfl)
  rw [e1] at a1 a2
  rw [a1, a2, a3, a4, h0]

/-- The loop-`0` mask of a real vector, as a loop momentum. -/
theorem faceId_mask_eq (z : LoopIndex → ℝ) (a : LoopIndex) :
    (if a.1 = 0 then ((z a : ℝ) : ℂ) else 0) = loopComp ![faceIdDir0 z, 0] a := by
  obtain ⟨a1, a2⟩ := a
  fin_cases a1 <;> simp [loopComp, faceIdDir0]

theorem faceId_gMet_eS0_off {a b : LoopIndex} (h : ¬(a.1 = 0 ∧ b.1 = 0)) :
    gMet (eS 0) a b = 0 := by
  simp [gMet, eS, h]

/-- **The `eS 0` contraction along a slice.** -/
theorem faceId_cTwoG_eS0_slice {y : Fin 4 → ℝ}
    (h : ∀ ℓ₀ : Fin 4 → ℝ, R.eval ![ℓ₀, y] = P.eval ![ℓ₀, 0]) (x : Fin 4 → ℝ) :
    cTwoG R (eS 0) (loopComp ![x, y]) = cTwoG P (eS 0) (loopComp ![x, 0]) := by
  classical
  set HR : LoopIndex → LoopIndex → ℂ := fun a b =>
    if a.1 = 0 ∧ b.1 = 0 then R.hess (loopComp ![x, y]) a b else 0
  set HP : LoopIndex → LoopIndex → ℂ := fun a b =>
    if a.1 = 0 ∧ b.1 = 0 then P.hess (loopComp ![x, 0]) a b else 0
  have hmask : ∀ (H : LoopIndex → LoopIndex → ℂ) (a b : LoopIndex),
      H a b * ((gMet (eS 0) a b : ℝ) : ℂ) =
        (if a.1 = 0 ∧ b.1 = 0 then H a b else 0) * ((gMet (eS 0) a b : ℝ) : ℂ) :=
    fun H a b => by
      by_cases hab : a.1 = 0 ∧ b.1 = 0
      · simp [hab]
      · simp [hab, faceId_gMet_eS0_off hab]
  have hq : ∀ z : LoopIndex → ℝ, ∑ a, ∑ b, HR a b * (((z a : ℝ) : ℂ) * ((z b : ℝ) : ℂ)) =
      ∑ a, ∑ b, HP a b * (((z a : ℝ) : ℂ) * ((z b : ℝ) : ℂ)) := by
    intro z
    have e : ∀ (H : LoopIndex → LoopIndex → ℂ), ∑ a, ∑ b,
        (if a.1 = 0 ∧ b.1 = 0 then H a b else 0) * (((z a : ℝ) : ℂ) * ((z b : ℝ) : ℂ)) =
        ∑ a, ∑ b, H a b * (loopComp ![faceIdDir0 z, 0] a * loopComp ![faceIdDir0 z, 0] b) :=
      fun H => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [← faceId_mask_eq, ← faceId_mask_eq]
        by_cases ha : a.1 = 0 <;> by_cases hb : b.1 = 0 <;> simp [ha, hb]
    rw [e, e]
    exact faceId_hessForm_slice h x _
  have hs := sum_mul_eq_of_quadForm hq (G := gMet (eS 0)) (faceId_gMet_symm (faceId_eS_symm 0))
  unfold cTwoG
  simp only [hmask (R.hess _), hmask (P.hess _)]
  exact hs

/-- The second difference of the Hessian coefficients around any center. -/
theorem faceId_hess_center (Q : LoopQuartic) (Z D : LoopIndex → ℂ) (a b : LoopIndex) :
    Q.hess (Z + D) a b + Q.hess (Z - D) a b - 2 * Q.hess Z a b =
      2 * ∑ c, ∑ d, Q.quartSym a b c d * (D c * D d) := by
  set K : LoopIndex → ℂ := fun c => Q.cub a b c + Q.cub a c b + Q.cub c a b
  have hl : ∑ c, K c * (Z + D) c + ∑ c, K c * (Z - D) c = 2 * ∑ c, K c * Z c := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by simp only [Pi.add_apply, Pi.sub_apply]; ring
  have hq : ∑ c, ∑ d, Q.quartSym a b c d * ((Z + D) c * (Z + D) d) +
      ∑ c, ∑ d, Q.quartSym a b c d * ((Z - D) c * (Z - D) d) =
      2 * ∑ c, ∑ d, Q.quartSym a b c d * (Z c * Z d) +
        2 * ∑ c, ∑ d, Q.quartSym a b c d * (D c * D d) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
      simp only [Pi.add_apply, Pi.sub_apply]; ring
  simp only [LoopQuartic.hess]
  linear_combination hl + hq

/-- **Masked polarization**: two coefficient matrices whose quadratic forms agree on loop-`0`
directions have the same `eS 0` contraction. -/
theorem faceId_polar_eS0 {H H' : LoopIndex → LoopIndex → ℂ}
    (h : ∀ d : Fin 4 → ℝ, ∑ a, ∑ b, H a b * (loopComp ![d, 0] a * loopComp ![d, 0] b) =
      ∑ a, ∑ b, H' a b * (loopComp ![d, 0] a * loopComp ![d, 0] b)) :
    ∑ a, ∑ b, H a b * ((gMet (eS 0) a b : ℝ) : ℂ) =
      ∑ a, ∑ b, H' a b * ((gMet (eS 0) a b : ℝ) : ℂ) := by
  classical
  have hmask : ∀ (H : LoopIndex → LoopIndex → ℂ) (a b : LoopIndex),
      H a b * ((gMet (eS 0) a b : ℝ) : ℂ) =
        (if a.1 = 0 ∧ b.1 = 0 then H a b else 0) * ((gMet (eS 0) a b : ℝ) : ℂ) :=
    fun H a b => by
      by_cases hab : a.1 = 0 ∧ b.1 = 0
      · simp [hab]
      · simp [hab, faceId_gMet_eS0_off hab]
  have e : ∀ (H : LoopIndex → LoopIndex → ℂ) (z : LoopIndex → ℝ), ∑ a, ∑ b,
      (if a.1 = 0 ∧ b.1 = 0 then H a b else 0) * (((z a : ℝ) : ℂ) * ((z b : ℝ) : ℂ)) =
      ∑ a, ∑ b, H a b * (loopComp ![faceIdDir0 z, 0] a * loopComp ![faceIdDir0 z, 0] b) :=
    fun H z => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [← faceId_mask_eq, ← faceId_mask_eq]
      by_cases ha : a.1 = 0 <;> by_cases hb : b.1 = 0 <;> simp [ha, hb]
  have hs := sum_mul_eq_of_quadForm
    (H := fun a b => if a.1 = 0 ∧ b.1 = 0 then H a b else 0)
    (H' := fun a b => if a.1 = 0 ∧ b.1 = 0 then H' a b else 0)
    (fun z => by rw [e H z, e H' z]; exact h _) (G := gMet (eS 0))
    (faceId_gMet_symm (faceId_eS_symm 0))
  simp only [hmask H, hmask H']
  exact hs

/-- The second difference of the `G` contraction is the quartic coefficients contracted with
`G` and the direction twice. -/
theorem faceId_cTwoG_center (Q : LoopQuartic) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (Z D : LoopIndex → ℂ) :
    cTwoG Q G (Z + D) + cTwoG Q G (Z - D) - 2 * cTwoG Q G Z =
      2 * ∑ c, ∑ d, (∑ a, ∑ b, Q.quartSym a b c d * ((gMet G a b : ℝ) : ℂ)) * (D c * D d) := by
  have e : cTwoG Q G (Z + D) + cTwoG Q G (Z - D) - 2 * cTwoG Q G Z =
      ∑ a, ∑ b, (Q.hess (Z + D) a b + Q.hess (Z - D) a b - 2 * Q.hess Z a b) *
        ((gMet G a b : ℝ) : ℂ) := by
    simp only [cTwoG, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e]
  simp only [faceId_hess_center, Finset.mul_sum, Finset.sum_mul]
  rw [← QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.sum_comm4]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **The `eS 0` quartic contraction along a slice.** -/
theorem faceId_cFourG_eS0_slice {y : Fin 4 → ℝ}
    (h : ∀ ℓ₀ : Fin 4 → ℝ, R.eval ![ℓ₀, y] = P.eval ![ℓ₀, 0]) :
    cFourG R (eS 0) = cFourG P (eS 0) := by
  have hK : ∀ d : Fin 4 → ℝ,
      ∑ c, ∑ e, (∑ a, ∑ b, R.quartSym a b c e * ((gMet (eS 0) a b : ℝ) : ℂ)) *
        (loopComp ![d, 0] c * loopComp ![d, 0] e) =
      ∑ c, ∑ e, (∑ a, ∑ b, P.quartSym a b c e * ((gMet (eS 0) a b : ℝ) : ℂ)) *
        (loopComp ![d, 0] c * loopComp ![d, 0] e) := by
    intro d
    have kR := faceId_cTwoG_center R (eS 0) (loopComp ![0, y]) (loopComp ![d, 0])
    have kP := faceId_cTwoG_center P (eS 0) (loopComp ![0, 0]) (loopComp ![d, 0])
    have p1 := faceId_loopComp_slice_add 0 y d 1 (Or.inl rfl)
    have p2 := faceId_loopComp_slice_sub 0 y d 1 (Or.inl rfl)
    have q1 := faceId_loopComp_slice_add 0 0 d 1 (Or.inl rfl)
    have q2 := faceId_loopComp_slice_sub 0 0 d 1 (Or.inl rfl)
    rw [one_smul] at p1 p2 q1 q2
    rw [p1, p2, faceId_cTwoG_eS0_slice h, faceId_cTwoG_eS0_slice h,
      faceId_cTwoG_eS0_slice h] at kR
    rw [q1, q2] at kP
    linear_combination (kP - kR) / 2
  have hp := faceId_polar_eS0 hK
  have e1 := faceId_two_mul_c4 R (gMet (eS 0))
  have e2 := faceId_two_mul_c4 P (gMet (eS 0))
  have : (2 : ℂ) * cFourG R (eS 0) = 2 * cFourG P (eS 0) := by
    change 2 * faceIdC4 R (gMet (eS 0)) = 2 * faceIdC4 P (gMet (eS 0))
    rw [e1, e2]
    exact hp
  exact mul_left_cancel₀ two_ne_zero this

/-- **The reduced bracket at `(x, y)` depends only on the slice `ℓ₀ ↦ R(ℓ₀, y)`.** -/
theorem faceId_faceIdRedBr_slice {y : Fin 4 → ℝ}
    (h : ∀ ℓ₀ : Fin 4 → ℝ, R.eval ![ℓ₀, y] = P.eval ![ℓ₀, 0]) (n : ℕ) (x : Fin 4 → ℝ)
    (v : ℝ) : faceIdRedBr n R (loopComp ![x, y]) v = faceIdRedBr n P (loopComp ![x, 0]) v := by
  have h0 : R.evalC (loopComp ![x, y]) = P.evalC (loopComp ![x, 0]) := h x
  simp only [faceIdRedBr, h0, faceId_cTwoG_eS0_slice h, faceId_cFourG_eS0_slice h]

open QED.TwoLoop.LimitCovariance (lmap actC evalC_lmap) in
theorem faceId_eval_lmap_faceIdMb (Q : LoopQuartic) (b : ℝ) (ℓ₀ y : Fin 4 → ℝ) :
    (lmap (faceIdM (faceIdMb b)) Q).eval ![ℓ₀, y] = Q.eval ![ℓ₀, y - b • ℓ₀] := by
  simp only [LoopQuartic.eval]
  rw [evalC_lmap]
  congr 1
  funext a
  obtain ⟨a1, a2⟩ := a
  simp only [actC, faceIdM, Fintype.sum_prod_type]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), ofReal_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Fin.sum_univ_two]
  fin_cases a1 <;> simp [faceIdMb, loopComp, sub_eq_add_neg, add_comm]

open QED.Integration.Feynman (simplexSet simplexPoint) in
open QED.TwoLoop.LimitCovariance (lmap) in
/-- **The self-energy face value with the loop-`1` point removed**: for any family `T W` of
quartics with `T W (ℓ₀, 0) = Q(ℓ₀, -b₁(W) - b(W) ℓ₀)` (`b = -θ`), the face value is the
integral of the reduced bracket of `T W` at `(-P₀(V), 0)`. -/
theorem faceId_faceIdVal_se_slice {q n : ℕ} (S : FaceShape (0 + 1) q) {Q : LoopQuartic}
    (hQ : LoopDegLe 1 1 Q) (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0))
    (T : (Fin (0 + 1) → ℝ) → LoopQuartic)
    (hT : ∀ W ℓ₀, (T W).eval ![ℓ₀, 0] = Q.eval ![ℓ₀, -S.b₁ (simplexPoint W) -
      S.b (simplexPoint W) • ℓ₀]) :
    faceIdVal n S Q = ∫ x in simplexSet (0 + 1) ×ˢ simplexSet q,
      faceIdRedBr (n - 2) (T x.1) (faceIdX0 (S.P0 (simplexPoint x.2)))
        (S.mR (simplexPoint x.2) -
          Minkowski.dot (S.P0 (simplexPoint x.2)) (S.P0 (simplexPoint x.2))) := by
  rw [faceId_faceIdVal_se S hQ hn]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine faceId_faceIdRedBr_slice (fun ℓ₀ => ?_) _ _ _
  rw [faceId_eval_lmap_faceIdMb, hT]

end QED.GradedProof.RPi4

end
