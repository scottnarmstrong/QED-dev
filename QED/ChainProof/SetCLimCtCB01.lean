/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLimCtCB

/-!
# Set (c): the classes `CB0`, `CB1` as T1 values

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The classes
`repCB0`, `repCB1` are the one-loop vertex with a level-`0` `fermionCt` vertex on its outgoing,
resp. incoming, internal electron line and the bubble (a closed fermion loop) on its photon line.
Their graded value (G₅) at the set (c) data is T1's value (T₁₀) at the parameters `cbParams`,
which carry the level-`0` electron counterterms `δ₂ = e² d₂(e⁻, 0)`, `δ_m = e² d_m(e⁻, 0)`
(`QED.GradedProof.contractionValue_zero_eq`: the `fermionCt` vertex is on the open line, so the
graded flavourings reduce to T1's; then the relabelling `Fin 3 ⊕ Fin 0 × Fin 3 ≃ Fin 3`).

* `ctReaches_repCB0`, `ctReaches_repCB1`: the counterterm vertex is on the open line;
* **`cb01Val_apply`**: the values of `CB0`, `CB1` in `QED.ChainProof.SetCPauli.cbVal`.
-/

@[expose] public section

open Complex Matrix
open QED.WickModel (Params Contraction contractionValue₂)

namespace QED.ChainProof.SetCPauli

open QED.ChainProof.SetCLink
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### The counterterm vertex is on the open line -/

theorem kCB0_kinds : ∀ t, kCB0 t ≠ .gaugeCt ∧ kCB0 t ≠ .photonCt := by decide

theorem kCB1_kinds : ∀ t, kCB1 t ≠ .gaugeCt ∧ kCB1 t ≠ .photonCt := by decide

theorem ctReaches_repCB0 : QED.GradedProof.CtReaches repCB0 := by
  have h : ∀ t : Wick.FermionVertex kCB0, kCB0 t.1 ≠ .gauge →
      repCB0.1.1.SameCycle (.inl 0) (.inr t) := by
    decide +kernel
  exact fun t ht => ⟨0, h t ht⟩

theorem ctReaches_repCB1 : QED.GradedProof.CtReaches repCB1 := by
  have h : ∀ t : Wick.FermionVertex kCB1, kCB1 t.1 ≠ .gauge →
      repCB1.1.1.SameCycle (.inl 0) (.inr t) := by
    decide +kernel
  exact fun t ht => ⟨0, h t ht⟩

/-! ### The values -/

/-- The T1 parameters of the classes `CB0`, `CB1` at the set (c) data and prescription `ε`: the
level-`0` electron counterterms of the open line. -/
abbrev cbParams (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (s : ℝ × ℝ × ℝ) (ε : ℝ) :
    Params :=
  { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with
    ε := ε
    δ₂ := P₀.e ^ 2 * (shareCt D s).d₂ (.inl 0) 0
    δm := P₀.e ^ 2 * (shareCt D s).dm (.inl 0) 0 }

/-- The graded value of a contraction with no `gaugeCt` or `photonCt` vertex and its
`fermionCt` vertices on the open line, at the set (c) data, is T1's value at `cbParams`. -/
theorem contractionValue_fermionCt_regFlavors (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt)
    (s : ℝ × ℝ × ℝ) (ε : ℝ) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (hκ : ∀ t, κ t ≠ .gaugeCt ∧ κ t ≠ .photonCt) (C : Contraction 1 1 κ)
    (hR : QED.GradedProof.CtReaches C) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.contractionValue { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s) C 0 pOut pIn kIn αOut βIn μ =
      contractionValue₂ (cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s ε) C pOut pIn kIn αOut βIn μ := by
  set P : Params := { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
  set P' := cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s ε
  rw [QED.GradedProof.contractionValue_zero_eq P P' _ _ C hR rfl rfl rfl rfl
    (fun t ht => absurd ht (hκ t).1) (fun _ _ => ⟨rfl, rfl, rfl⟩)
    (fun t ht => absurd ht (hκ t).2)]
  rw [QED.Lepton.Proof.contractionValue₂_relabel QED.Lepton.Proof.leptonFlavorsZeroEquiv
    (Ψ := QED.Lepton.Proof.HM.t1F P') rfl P' ?_ ?_ C]
  · rfl
  · rintro (i | ⟨j, _⟩)
    · rfl
    · exact j.elim0
  · rintro (i | ⟨j, _⟩)
    · rfl
    · exact j.elim0

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-- **The values of `CB0`, `CB1`**: T1's values of `repCB0`, `repCB1` at `cbParams`, at the
set (c) data and every `ε`. -/
theorem cb01Val_apply (ε : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    cbVal { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) p' p μ 0 i j =
      contractionValue₂ (cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s ε) repCB0 (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) ∧
    cbVal { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) p' p μ 1 i j =
      contractionValue₂ (cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s ε) repCB1 (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) :=
  ⟨contractionValue_fermionCt_regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ D s ε kCB0_kinds repCB0
      ctReaches_repCB0 _ _ _ _ _ _,
    contractionValue_fermionCt_regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ D s ε kCB1_kinds repCB1
      ctReaches_repCB1 _ _ _ _ _ _⟩

end QED.ChainProof.SetCPauli

end
