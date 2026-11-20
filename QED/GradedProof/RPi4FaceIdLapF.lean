/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdVtx
public import QED.GradedProof.RPi4LoopSwap

/-!
# (R-Π₄) step L6d3: the half loop Laplacian as second differences

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The vertex face
of a piece is the reduced one-loop functional of `faceIdLap Q`, the half loop-`1` Laplacian of
the numerator (`faceId_faceIdVal_vtx`). For the Dirac algebra it is computed on the numerator
*function*: `faceIdLapF s F ℓ = ¼ Σ_a η_aa (F(ℓ + e_{s,a}) + F(ℓ - e_{s,a}) - 2F(ℓ))`.

* `faceIdE`, **`faceIdLapF`**; **`faceId_eval_faceIdLap`**: `(faceIdLap Q).eval = faceIdLapF 1
  Q.eval` when `LoopDegLe 1 2 Q`;
* linearity (`faceId_lapF_add`, `_sub`, `_const_mul`), `faceId_lapF_eq_zero` (a function constant
  along loop `s`);
* the exchange of the loops: `faceId_eval_swapQ`, `faceId_lapF_comp_lsw`,
  **`faceId_eval_faceIdLap_swapQ`** (the loop-`0` faces, numerator `swapQ Q`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

/-! ### Second differences along a loop -/

/-- The unit vector of component `a` of loop `s`. -/
def faceIdE (s : Fin 2) (a : Fin 4) : Fin 2 → Fin 4 → ℝ := Pi.single s (Pi.single a 1)

/-- **The function-level half Laplacian along loop `s`**: `¼ Σ_a η_aa` times the second difference
of `F` along the unit vector `(s, a)`. -/
noncomputable def faceIdLapF (s : Fin 2) (F : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  1 / 4 * ∑ a, ((Minkowski.metric a a : ℝ) : ℂ) *
    (F (ℓ + faceIdE s a) + F (ℓ - faceIdE s a) - 2 * F ℓ)

theorem faceId_sum_gMet_eS1 (H : LoopIndex → LoopIndex → ℂ) :
    ∑ a, ∑ b, H a b * (gMet (eS 1) a b : ℂ) =
      ∑ μ, ((Minkowski.metric μ μ : ℝ) : ℂ) * H (1, μ) (1, μ) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, gMet, eS]
  simp
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_eq_single μ]
  · ring
  · intro ν _ hν
    simp [Minkowski.metric, Ne.symm hν]
  · simp

theorem faceId_sum_loopComp_E (H : LoopIndex → LoopIndex → ℂ) (s : Fin 2) (a : Fin 4) :
    ∑ x, ∑ y, H x y * (loopComp (faceIdE s a) x * loopComp (faceIdE s a) y) = H (s, a) (s, a) := by
  have hx : ∀ x : LoopIndex, loopComp (faceIdE s a) x = if x = (s, a) then 1 else 0 := by
    rintro ⟨t, ν⟩
    by_cases ht : t = s
    · subst ht
      by_cases hν : ν = a
      · subst hν; simp [loopComp, faceIdE]
      · simp [loopComp, faceIdE, hν]
    · simp [loopComp, faceIdE, ht]
  simp only [hx, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **The half loop-`1` Laplacian is the function-level one** (loop-`1` degree at most two). -/
theorem faceId_eval_faceIdLap {Q : LoopQuartic} (hQ : LoopDegLe 1 2 Q)
    (ℓ : Fin 2 → Fin 4 → ℝ) : (faceIdLap Q).eval ℓ = faceIdLapF 1 Q.eval ℓ := by
  have h4 : ∀ a, Q.quartPart (loopComp (faceIdE 1 a)) = 0 := by
    intro a
    simp only [LoopQuartic.quartPart]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ =>
      Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun w _ => ?_
    by_cases hall : x.1 = 1 ∧ y.1 = 1 ∧ z.1 = 1 ∧ w.1 = 1
    · rw [hQ.quart x y z w (by
        simp only [loopInd_of_eq hall.1, loopInd_of_eq hall.2.1, loopInd_of_eq hall.2.2.1,
          loopInd_of_eq hall.2.2.2]; norm_num), zero_mul]
    · have h0 : ∀ v : LoopIndex, v.1 ≠ 1 → loopComp (faceIdE 1 a) v = 0 := fun v hv => by
        simp [loopComp, faceIdE, hv]
      by_cases hx : x.1 = 1
      · by_cases hy : y.1 = 1
        · by_cases hz : z.1 = 1
          · rw [h0 w fun hw => hall ⟨hx, hy, hz, hw⟩]; ring
          · rw [h0 z hz]; ring
        · rw [h0 y hy]; ring
      · rw [h0 x hx]; ring
  have hd : ∀ a, Q.eval (ℓ + faceIdE 1 a) + Q.eval (ℓ - faceIdE 1 a) - 2 * Q.eval ℓ =
      2 * Q.hess (loopComp ℓ) (1, a) (1, a) := by
    intro a
    rw [LoopQuartic.eval_add_add_eval_sub, faceId_sum_loopComp_E, h4]
    ring
  rw [LoopQuartic.eval, faceId_evalC_faceIdLap, faceIdLapF, cTwoG, faceId_sum_gMet_eS1]
  simp only [hd, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-! ### Linearity and the exchange of the loops -/

section Lin

variable (s : Fin 2) (F G : (Fin 2 → Fin 4 → ℝ) → ℂ) (ℓ : Fin 2 → Fin 4 → ℝ)

theorem faceId_lapF_add : faceIdLapF s (fun ℓ => F ℓ + G ℓ) ℓ =
    faceIdLapF s F ℓ + faceIdLapF s G ℓ := by
  simp only [faceIdLapF, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by ring

theorem faceId_lapF_sub : faceIdLapF s (fun ℓ => F ℓ - G ℓ) ℓ =
    faceIdLapF s F ℓ - faceIdLapF s G ℓ := by
  simp only [faceIdLapF, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by ring

theorem faceId_lapF_const_mul (c : ℂ) : faceIdLapF s (fun ℓ => c * F ℓ) ℓ =
    c * faceIdLapF s F ℓ := by
  simp only [faceIdLapF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- A function that does not move along loop `s` has vanishing half Laplacian there. -/
theorem faceId_lapF_eq_zero
    (h : ∀ a, F (ℓ + faceIdE s a) = F ℓ ∧ F (ℓ - faceIdE s a) = F ℓ) :
    faceIdLapF s F ℓ = 0 := by
  simp only [faceIdLapF, (h _).1, (h _).2, show F ℓ + F ℓ - 2 * F ℓ = 0 by ring, mul_zero,
    Finset.sum_const_zero]

theorem faceId_add_E_comp_lsw (a : Fin 4) :
    (ℓ + faceIdE 1 a) ∘ lsw = ℓ ∘ lsw + faceIdE 0 a ∧
      (ℓ - faceIdE 1 a) ∘ lsw = ℓ ∘ lsw - faceIdE 0 a := by
  constructor <;> funext t μ <;> fin_cases t <;> simp [faceIdE, lsw]

/-- The half loop-`1` Laplacian after the exchange of the loops is the half loop-`0` one. -/
theorem faceId_lapF_comp_lsw : faceIdLapF 1 (fun ℓ => F (ℓ ∘ lsw)) ℓ =
    faceIdLapF 0 F (ℓ ∘ lsw) := by
  simp only [faceIdLapF, (faceId_add_E_comp_lsw ℓ _).1, (faceId_add_E_comp_lsw ℓ _).2]

end Lin

theorem faceId_eval_swapQ (Q : LoopQuartic) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (swapQ Q).eval ℓ = Q.eval (ℓ ∘ lsw) := by
  have h : loopComp (ℓ ∘ lsw) ∘ swI = loopComp ℓ := by
    funext a
    simp [loopComp, swI_apply, lsw]
  rw [LoopQuartic.eval, ← h, evalC_swapQ, LoopQuartic.eval]

/-- **The half loop-`1` Laplacian of the exchanged numerator** (loop-`0` degree at most two) is
the function-level half loop-`0` Laplacian at the exchanged point. -/
theorem faceId_eval_faceIdLap_swapQ {Q : LoopQuartic} (hQ : LoopDegLe 0 2 Q)
    (ℓ : Fin 2 → Fin 4 → ℝ) : (faceIdLap (swapQ Q)).eval ℓ = faceIdLapF 0 Q.eval (ℓ ∘ lsw) := by
  rw [faceId_eval_faceIdLap (loopDegLe_swapQ hQ), ← faceId_lapF_comp_lsw]
  congr 1
  funext ℓ'
  exact faceId_eval_swapQ Q ℓ'

theorem faceId_add_E_one (ℓ : Fin 2 → Fin 4 → ℝ) (a : Fin 4) :
    (ℓ + faceIdE 1 a) 0 = ℓ 0 ∧ (ℓ + faceIdE 1 a) 1 = ℓ 1 + Pi.single a 1 := by
  simp [faceIdE]

theorem faceId_sub_E_one (ℓ : Fin 2 → Fin 4 → ℝ) (a : Fin 4) :
    (ℓ - faceIdE 1 a) 0 = ℓ 0 ∧ (ℓ - faceIdE 1 a) 1 = ℓ 1 - Pi.single a 1 := by
  simp [faceIdE]

theorem faceId_add_E_zero (ℓ : Fin 2 → Fin 4 → ℝ) (a : Fin 4) :
    (ℓ + faceIdE 0 a) 0 = ℓ 0 + Pi.single a 1 ∧ (ℓ + faceIdE 0 a) 1 = ℓ 1 := by
  simp [faceIdE]

theorem faceId_sub_E_zero (ℓ : Fin 2 → Fin 4 → ℝ) (a : Fin 4) :
    (ℓ - faceIdE 0 a) 0 = ℓ 0 - Pi.single a 1 ∧ (ℓ - faceIdE 0 a) 1 = ℓ 1 := by
  simp [faceIdE]

end QED.GradedProof.RPi4

end
