/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.RoutingChange
public import QED.TwoLoop.JointIntegralInvariance

/-!
# (X₁) piece C: the value through any unimodular conserved routing

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C2. The canonical routing (T₄) of a glued contraction is not the
concatenation of the routings of its pieces (the chords (T₁) depend on the labels). It need not
be: any family `k ℓ` of momentum assignments that is conserved at every vertex, integer affine in
`ℓ`, and gives each loop momentum `ℓ r` to some line, is the canonical routing after an integer
unimodular affine change of the loop momenta, so the joint energy-first integral (T₉) of any
function of the line momenta is the same for both.

* `exists_routing_change_of_isConserved`: `k ℓ = lineMomentum₂ C (M ℓ + a)` with `det M = ±1`.
* `jointEnergyFirstIntegral_eq_of_isConserved`: `∫ F (lineMomentum₂ C ℓ) = ∫ F (k ℓ)`.

No connectedness or condition on the external momenta is needed: both are hidden in the
existence of the conserved family.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line loopCount lineMomentum₂ IsChord chordMomentum)
open QED.TwoLoop.Routing (IsConserved eq_lineMomentum₂_of_isConserved)
open QED.TwoLoop.Relabel (IsIntAffine matAct matAct_add matAct_matAct eq_one_of_matAct
  chordValues chordMomentum_chordValues chordValues_lineMomentum₂)

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **Changing to a conserved routing.** A family of momentum assignments of `C`, conserved at
every vertex, integer affine in the loop momenta, and giving each loop momentum to some line, is
the canonical routing at `M ℓ + a` with an integer matrix `M` of determinant `±1`. -/
theorem exists_routing_change_of_isConserved {C : Contraction nf nA κ}
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ} {L : ℕ} (hL : loopCount C = L)
    (k : (Fin L → Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (k ℓ)) (haff : ∀ f, IsIntAffine fun ℓ => k ℓ f)
    (hrec : ∀ r : Fin L, ∃ f, ∀ ℓ, k ℓ f = ℓ r) :
    ∃ M : Matrix (Fin L) (Fin L) ℤ, IsUnit M.det ∧ ∃ a : Fin L → Fin 4 → ℝ,
      ∀ ℓ, k ℓ = lineMomentum₂ C pOut pIn kIn (matAct M ℓ + a) := by
  -- the chord values of `k ℓ` are integer affine in `ℓ`
  have hch : ∀ s : Fin L, IsIntAffine fun ℓ => chordValues hL (k ℓ) s := fun s => haff _
  choose m b hmb using hch
  have hval : ∀ ℓ, chordValues hL (k ℓ) = matAct (Matrix.of m) ℓ + fun s => b s := fun ℓ => by
    funext s
    exact hmb s ℓ
  have hk : ∀ ℓ, k ℓ = lineMomentum₂ C pOut pIn kIn (matAct (Matrix.of m) ℓ + fun s => b s) :=
    fun ℓ => by
      rw [← hval]
      funext f
      exact eq_lineMomentum₂_of_isConserved (hcons ℓ)
        (fun g hg => (chordMomentum_chordValues hL _ hg).symm) f
  refine ⟨Matrix.of m, ?_, fun s => b s, hk⟩
  -- the loop momenta are integer affine in the chord values
  choose f hf using hrec
  have hinv : ∀ r : Fin L, IsIntAffine fun ν : Fin L → Fin 4 → ℝ =>
      lineMomentum₂ C pOut pIn kIn ν (f r) := fun r => IsIntAffine.lineMomentum₂ C _ _ _ _
  choose m' b' hmb' using hinv
  have hid : ∀ ℓ, matAct (Matrix.of m') (matAct (Matrix.of m) ℓ + fun s => b s) +
      (fun r => b' r) = ℓ := fun ℓ => by
    funext r
    have h1 := hmb' r (matAct (Matrix.of m) ℓ + fun s => b s)
    simp only at h1
    rw [← hk, hf] at h1
    simpa [matAct] using h1.symm
  have h0 := hid 0
  have hMM : ∀ ℓ, matAct (Matrix.of m' * Matrix.of m) ℓ = ℓ := fun ℓ => by
    have := hid ℓ
    rw [matAct_add, matAct_matAct, add_assoc] at this
    rw [show matAct (Matrix.of m) (0 : Fin L → Fin 4 → ℝ) = 0 by funext s; simp [matAct],
      zero_add] at h0
    rwa [h0, add_zero] at this
  have hdet : (Matrix.of m').det * (Matrix.of m).det = 1 := by
    rw [← Matrix.det_mul, eq_one_of_matAct hMM, Matrix.det_one]
  exact IsUnit.of_mul_eq_one_right _ hdet

/-- **The joint energy-first integral through a conserved routing**: under the hypotheses of
`exists_routing_change_of_isConserved`, any function of the line momenta has the same integral
(T₉) at the canonical routing and at `k`. -/
theorem jointEnergyFirstIntegral_eq_of_isConserved {C : Contraction nf nA κ}
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ} {L : ℕ} (hL : loopCount C = L)
    (k : (Fin L → Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (k ℓ)) (haff : ∀ f, IsIntAffine fun ℓ => k ℓ f)
    (hrec : ∀ r : Fin L, ∃ f, ∀ ℓ, k ℓ f = ℓ r) (F : (Line C → Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => F (lineMomentum₂ C pOut pIn kIn ℓ)) =
      QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => F (k ℓ)) := by
  obtain ⟨M, hM, a, h⟩ := exists_routing_change_of_isConserved hL k hcons haff hrec
  simp only [h]
  exact (QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add L
    (fun ℓ => F (lineMomentum₂ C pOut pIn kIn ℓ)) M hM a).symm

end QED.GradedProof.X1C

end
