/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdShift
public import QED.GradedProof.RPi4FaceScale

/-!
# (R-Π₄) step L6d3: the self-energy representative

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The
self-energy face wrappers (`faceId_face1_se_five`, `faceId_face1_se_four`) need a quartic `P`
of loop-`1` degree `≤ 1` with `P(ℓ) = N(ℓ₀)`, where `N(ℓ₀) = Q(ℓ₀, ½(ℓ₀ + b))` is the
numerator at the face midpoint. It is `faceIdSERep Q b`: the shift of `Q` by `(0, b/2)`
composed with the linear map `(ℓ₀, ℓ₁) ↦ (ℓ₀, ℓ₀/2)`. Its loop-`1` coefficients vanish
(the map kills `ℓ₁`), and it has no quartic part when `Q` has none.

* `faceIdHalfM`, **`faceIdSERep`**, **`faceId_se_rep`**.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.TwoLoop.LimitCovariance (lmap actC evalC_lmap)

/-- The linear map `(ℓ₀, ℓ₁) ↦ (ℓ₀, ℓ₀/2)` on loop momenta. -/
noncomputable def faceIdHalfM : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1 / 2, 0]

/-- **The self-energy representative** `ℓ ↦ Q(ℓ₀, ½(ℓ₀ + b))`. -/
noncomputable def faceIdSERep (Q : LoopQuartic) (b : Fin 4 → ℝ) : LoopQuartic :=
  lmap (faceIdM faceIdHalfM) (faceIdShift Q (loopComp ![0, (1 / 2 : ℝ) • b]))

theorem faceId_halfM_loop1 (a b : LoopIndex) (hb : b.1 = 1) :
    faceIdM faceIdHalfM a b = 0 := by
  obtain ⟨i, μ⟩ := a
  obtain ⟨j, ν⟩ := b
  simp only at hb
  subst hb
  simp only [faceIdM]
  split_ifs
  · fin_cases i <;> simp [faceIdHalfM]
  · rfl

theorem faceId_actC_halfM (ℓ : Fin 2 → Fin 4 → ℝ) :
    actC (faceIdM faceIdHalfM) (loopComp ℓ) =
      loopComp ![ℓ 0, (1 / 2 : ℝ) • ℓ 0] := by
  funext a
  obtain ⟨i, μ⟩ := a
  simp only [actC, faceIdM, Fintype.sum_prod_type]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), ofReal_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Fin.sum_univ_two]
  fin_cases i <;> simp [faceIdHalfM, loopComp]

/-- **The self-energy representative**: loop-`1` degree `≤ 1` (indeed `0`), value
`Q(ℓ₀, ½(ℓ₀ + b))`, and no quartic part when `Q` has none. -/
theorem faceId_se_rep (Q : LoopQuartic) (b : Fin 4 → ℝ) :
    LoopDegLe 1 1 (faceIdSERep Q b) ∧
      (∀ ℓ, (faceIdSERep Q b).eval ℓ = Q.eval ![ℓ 0, (1 / 2 : ℝ) • (ℓ 0 + b)]) ∧
      (Q.quart = 0 → (faceIdSERep Q b).quart = 0) := by
  have h0 : ∀ a b, b.1 = 1 → (faceIdM faceIdHalfM a b : ℂ) = 0 := fun a b hb => by
    rw [faceId_halfM_loop1 a b hb, ofReal_zero]
  have hi : ∀ b : LoopIndex, 0 < loopInd 1 b → b.1 = 1 := fun b hb => by
    by_contra h
    simp [loopInd, h] at hb
  have hD : LoopDegLe 1 0 (faceIdSERep Q b) := by
    refine ⟨fun x hx => ?_, fun x y hx => ?_, fun x y z hx => ?_, fun x y z w hx => ?_⟩
    · simp only [faceIdSERep, lmap]
      exact Finset.sum_eq_zero fun a _ => by rw [h0 a x (hi x hx), mul_zero]
    · simp only [faceIdSERep, lmap]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun a' _ => ?_
      rcases Nat.eq_zero_or_pos (loopInd 1 x) with h | h
      · rw [h0 a' y (hi y (by omega))]; ring
      · rw [h0 a x (hi x h)]; ring
    · simp only [faceIdSERep, lmap]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun a' _ =>
        Finset.sum_eq_zero fun a'' _ => ?_
      rcases Nat.eq_zero_or_pos (loopInd 1 x) with h | h
      · rcases Nat.eq_zero_or_pos (loopInd 1 y) with h' | h'
        · rw [h0 a'' z (hi z (by omega))]; ring
        · rw [h0 a' y (hi y h')]; ring
      · rw [h0 a x (hi x h)]; ring
    · simp only [faceIdSERep, lmap]
      refine Finset.sum_eq_zero fun a₁ _ => Finset.sum_eq_zero fun a₂ _ =>
        Finset.sum_eq_zero fun a₃ _ => Finset.sum_eq_zero fun a₄ _ => ?_
      rcases Nat.eq_zero_or_pos (loopInd 1 x) with h | h
      · rcases Nat.eq_zero_or_pos (loopInd 1 y) with h' | h'
        · rcases Nat.eq_zero_or_pos (loopInd 1 z) with h'' | h''
          · rw [h0 a₄ w (hi w (by omega))]; ring
          · rw [h0 a₃ z (hi z h'')]; ring
        · rw [h0 a₂ y (hi y h')]; ring
      · rw [h0 a₁ x (hi x h)]; ring
  refine ⟨hD.mono (by norm_num), fun ℓ => ?_, fun hq => ?_⟩
  · have e : loopComp ![0, (1 / 2 : ℝ) • b] + loopComp ![ℓ 0, (1 / 2 : ℝ) • ℓ 0] =
        loopComp ![ℓ 0, (1 / 2 : ℝ) • (ℓ 0 + b)] := by
      rw [← loopComp_add]
      congr 1
      funext i
      fin_cases i
      · simp
      · simp [smul_add, add_comm]
    rw [faceIdSERep, LoopQuartic.eval, evalC_lmap, faceId_actC_halfM, faceId_evalC_shift, e,
      LoopQuartic.eval]
  · simp only [faceIdSERep, lmap, faceId_quart_shift, hq]
    funext x y z w
    simp
