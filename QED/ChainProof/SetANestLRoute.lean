/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.ContractionValue
public import QED.TwoLoop.Routing
public import QED.TwoLoop.JointIntegralInvariance
public import QED.TwoLoop.NestedVP

/-!
# Set (a), obligation (N): a change of routing, at any loop number

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink` (the nested form of
the loop classes, `QED.ChainProof.SetANest.LoopNested`), shared by the two-loop and the
three-loop classes.

A routing `mom ℓ` of the lines of a contraction `C` with `L = loopCount C` loop momenta, conserved
at every vertex and giving each chord the loop momentum of the frozen routing (T₄) at an integer
unimodular affine image `M ℓ + a`, is the frozen routing at `M ℓ + a`
(`QED.TwoLoop.Routing.eq_lineMomentum₂_of_isConserved`). Hence:

* **`contractionValue_eq_of_routing`**: the value (G₅) of `C` is the joint energy-first integral
  (T₉) of `(2π)^{-4L}` times the regulated amplitude (G₄) at the routing `mom` (no integrability
  needed: `QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add`);
* **`jointEnergyFirstIntegrable_of_routing`**: the integrability (T₉′) of both stages passes from
  the frozen routing to `mom` (`QED.TwoLoop.NestedVP.jointEnergyFirstIntegrable_comp_matrix_add`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetANest

open QED.WickModel QED.TwoLoop.Routing

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Graded.Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The integrand of the value (G₅) at a routing `k`. -/
noncomputable def routedIntegrand (C : Contraction nf nA κ) (g : Graded.Grading κ) (L : ℕ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  (((2 * Real.pi) ^ (4 * L) : ℝ) : ℂ)⁻¹ *
    Graded.regulatedAmplitude P Φ D C g pIn kIn k αOut βIn μ

/-- A routing that is conserved and agrees on the chords with the frozen routing at an affine
image is the frozen routing there. -/
theorem lineMomentum₂_of_routing {C : Contraction nf nA κ} {L : ℕ}
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (mom : (Fin L → Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (mom ℓ))
    (M : Matrix (Fin L) (Fin L) ℤ) (a : Fin L → Fin 4 → ℝ)
    (hchord : ∀ ℓ f, IsChord f → mom ℓ f = chordMomentum ((fun s => ∑ r, M s r • ℓ r) + a) f)
    (ℓ : Fin L → Fin 4 → ℝ) :
    mom ℓ = lineMomentum₂ C pOut pIn kIn ((fun s => ∑ r, M s r • ℓ r) + a) :=
  funext fun f => eq_lineMomentum₂_of_isConserved (hcons ℓ) (hchord ℓ) f

/-- **The value in another routing.** If `mom` is conserved and puts on each chord the loop
momentum of `M ℓ + a`, `M` integer with unit determinant, then the value (G₅) of `C` is the joint
energy-first integral of the integrand at `mom`. No integrability is needed. -/
theorem contractionValue_eq_of_routing (C : Contraction nf nA κ) (g : Graded.Grading κ)
    {L : ℕ} (hL : loopCount C = L) {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (mom : (Fin L → Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (mom ℓ))
    (M : Matrix (Fin L) (Fin L) ℤ) (hM : IsUnit M.det) (a : Fin L → Fin 4 → ℝ)
    (hchord : ∀ ℓ f, IsChord f → mom ℓ f = chordMomentum ((fun s => ∑ r, M s r • ℓ r) + a) f)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.contractionValue P Φ D C g pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral L fun ℓ =>
        routedIntegrand P Φ D C g L pIn kIn (mom ℓ) αOut βIn μ := by
  subst hL
  have h := QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add
    (loopCount C) (fun ℓ => routedIntegrand P Φ D C g (loopCount C) pIn kIn
      (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) M hM a
  simp only [← lineMomentum₂_of_routing mom hcons M a hchord] at h
  exact h.symm

/-- **The integrability in another routing**: (T₉′) for the integrand of the value (G₅) in the
frozen routing gives (T₉′) for the integrand at `mom`. -/
theorem jointEnergyFirstIntegrable_of_routing (C : Contraction nf nA κ) (g : Graded.Grading κ)
    {L : ℕ} (hL : loopCount C = L) {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (mom : (Fin L → Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (mom ℓ))
    (M : Matrix (Fin L) (Fin L) ℤ) (hM : IsUnit M.det) (a : Fin L → Fin 4 → ℝ)
    (hchord : ∀ ℓ f, IsChord f → mom ℓ f = chordMomentum ((fun s => ∑ r, M s r • ℓ r) + a) f)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4)
    (hJ : QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ) :
    QED.TwoLoop.jointEnergyFirstIntegrable L fun ℓ =>
      routedIntegrand P Φ D C g L pIn kIn (mom ℓ) αOut βIn μ := by
  subst hL
  have h := QED.TwoLoop.NestedVP.jointEnergyFirstIntegrable_comp_matrix_add (loopCount C)
    (fun ℓ => routedIntegrand P Φ D C g (loopCount C) pIn kIn
      (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) M hM a hJ
  simp only [← lineMomentum₂_of_routing mom hcons M a hchord] at h
  exact h

end QED.ChainProof.SetANest

end
