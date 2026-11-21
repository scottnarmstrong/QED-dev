/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.GEx2Solve
public import QED.Frozen.ThreeLoop.IsVPShareOnShell
public import QED.Frozen.Graded.FamilyVertex

/-!
# Set (c), model link: the tree graphs of the VP-share conditions

Helper for (G-ex-s) `QED.ThreeLoop.existsUnique_isVPShareOnShell` and (WI-s)
`QED.ThreeLoop.isVPShareOnShell_d₁_eq_d₂` (decision D-58). The conditions (Sc₂) restrict the
order-`e⁴` self-energy to `selSE` (1PI, and the vacuum-polarization family (Sc₁) or no `gauge`
vertex) and the order-`e⁵` vertex to `selV` (1PI, and `IsVPChain 1` or no `gauge` vertex).

* `selectedPart_sub_eq_of_nonzero`: if two selections agree on the contractions with a nonzero
  grading of graded order `K`, the difference of their order-`K` parts at two data agreeing at
  level `0` is the same (the zero-grading terms read only level `0`).
* The 1PI one-fermion contractions with a nonzero grading of graded order `4`, and the 1PI vertex
  contractions with a nonzero grading of graded order `5`, have no `gauge` vertex (they are the
  level-`1` trees), so `selSE`, `selV` agree there with `IsOnePI`.
* Hence **`selfEnergySelPart_two_sub`**: the selected order-`4` self-energies of two data agreeing
  at level `0` differ by the difference of the level-`1` `fermionCt` trees `seTree`; and
  **`familyVertex_five_sub`**: the selected order-`5` vertices differ by the difference of the
  level-`1` `gaugeCt` trees, as for the full 1PI parts (`GEx2.selfEnergyPart_two_add_tree`,
  `GEx2.vertexPart_two_sub`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.Graded
open QED.WickModel (Params Contraction IsOnePI fermionSign)

/-- The self-energy selection of (Sc₂). -/
abbrev selSE : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 0 κ → Grading κ → Prop :=
  fun {_ κ} C _ => IsOnePI C ∧ (ThreeLoop.IsVPSelfEnergy C ∨ ∀ t, κ t ≠ .gauge)

/-- The vertex selection of (Sc₂). -/
abbrev selV : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Grading κ → Prop :=
  fun {_ κ} C _ => IsOnePI C ∧ (VPChain.IsVPChain 1 C ∨ ∀ t, κ t ≠ .gauge)

open scoped Classical in
/-- **Selections agreeing off the zero grading have the same level-`0` differences.** -/
theorem selectedPart_sub_eq_of_nonzero (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D' : Counterterms F) (h₁ : ∀ f, D.d₁ f 0 = D'.d₁ f 0)
    (h₂ : ∀ f, D.d₂ f 0 = D'.d₂ f 0) (hm : ∀ f, D.dm f 0 = D'.dm f 0) (h₃ : D.d₃ 0 = D'.d₃ 0)
    (nf nA : ℕ) (Sel Sel' : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Prop)
    (K : ℕ) (h : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Grading κ), g ≠ 0 →
      gradedOrder κ g = K → ∀ C : Contraction nf nA κ, Sel C ↔ Sel' C)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    selectedPart P Φ D nf nA (fun C _ => Sel C) K pOut pIn kIn αOut βIn μ -
        selectedPart P Φ D' nf nA (fun C _ => Sel C) K pOut pIn kIn αOut βIn μ =
      selectedPart P Φ D nf nA (fun C _ => Sel' C) K pOut pIn kIn αOut βIn μ -
        selectedPart P Φ D' nf nA (fun C _ => Sel' C) K pOut pIn kIn αOut βIn μ := by
  simp only [QED.GradedProof.VP2.selectedPart_split]
  have hz : ∀ (S : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Prop),
      (∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
            (fun κ => ∑ t, (κ t).order = K),
          ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter (fun C => S C),
            ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ D C 0 pOut pIn kIn αOut βIn μ) =
      ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
            (fun κ => ∑ t, (κ t).order = K),
          ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter (fun C => S C),
            ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ D' C 0 pOut pIn kIn αOut βIn μ :=
    fun S => Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ _ =>
      Finset.sum_congr rfl fun C _ => by
        rw [QED.GradedProof.contractionValue_zero_congr P Φ D D' h₁ h₂ hm h₃])
  have hnz : ∀ E : Counterterms F,
      (∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ : Fin N → Wick.VertexKind,
          ∑ g ∈ (Fintype.piFinset fun _ : CtVertex κ => Finset.range (K + 1)).filter
              (fun g => gradedOrder κ g = K ∧ g ≠ 0),
            ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter (fun C => Sel C),
              ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ E C g pOut pIn kIn αOut βIn μ) =
      ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ : Fin N → Wick.VertexKind,
          ∑ g ∈ (Fintype.piFinset fun _ : CtVertex κ => Finset.range (K + 1)).filter
              (fun g => gradedOrder κ g = K ∧ g ≠ 0),
            ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter (fun C => Sel' C),
              ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ E C g pOut pIn kIn αOut βIn μ :=
    fun E => Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ _ =>
      Finset.sum_congr rfl fun g hg => by
        obtain ⟨-, hgK, hg0⟩ := Finset.mem_filter.1 hg
        rw [Finset.filter_congr fun C _ => h g hg0 hgK C])
  rw [hz Sel, hz Sel', hnz D, hnz D']
  ring

/-- The 1PI one-fermion contractions with a nonzero grading of graded order `4` have no `gauge`
vertex: they are the level-`1` `fermionCt` tree. -/
theorem noGauge_of_grading_ne_zero_se {N : ℕ} {κ : Fin N → Wick.VertexKind} {g : Grading κ}
    (hg0 : g ≠ 0) (hg : gradedOrder κ g = 4) (C : Contraction 1 0 κ) (hC : IsOnePI C) :
    ∀ t, κ t ≠ .gauge := by
  obtain rfl := QED.GradedProof.GEx2.eq_one_of_grading_ne_zero_se hg0 hg
  obtain ⟨k0, rfl⟩ : ∃ k0, κ = QED.WickModel.oneVertex k0 :=
    ⟨κ 0, QED.WickModel.eq_oneVertex κ⟩
  by_cases hk : k0 = .fermionCt
  · subst hk
    intro t h
    exact Wick.VertexKind.noConfusion h
  · exact absurd hC (QED.WickModel.not_isOnePI_oneVertex_selfEnergy hk C)

/-- The 1PI vertex contractions with a nonzero grading of graded order `5` have no `gauge`
vertex: they are the level-`1` `gaugeCt` tree. -/
theorem noGauge_of_grading_ne_zero_v {N : ℕ} {κ : Fin N → Wick.VertexKind} {g : Grading κ}
    (hg0 : g ≠ 0) (hg : gradedOrder κ g = 5) (C : Contraction 1 1 κ) (hC : IsOnePI C) :
    ∀ t, κ t ≠ .gauge := by
  obtain rfl := QED.GradedProof.eq_one_of_level hg0 hg C hC
  obtain rfl := QED.GradedProof.eq_gaugeCt_of_level hg0 hg
  intro t h
  exact Wick.VertexKind.noConfusion h

/-- **The selected order-`4` self-energies of data agreeing at level `0` differ by the
level-`1` trees.** -/
theorem selfEnergySelPart_two_sub (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D' : Counterterms F) (h₁ : ∀ f, D.d₁ f 0 = D'.d₁ f 0)
    (h₂ : ∀ f, D.d₂ f 0 = D'.d₂ f 0) (hm : ∀ f, D.dm f 0 = D'.dm f 0) (h₃ : D.d₃ 0 = D'.d₃ 0)
    (f : F) (p : Fin 4 → ℝ) (α β : Fin 4) :
    selfEnergySelPart P Φ D selSE f 2 p α β + GradedProof.GEx2.seTree P Φ D f p α β =
      selfEnergySelPart P Φ D' selSE f 2 p α β + GradedProof.GEx2.seTree P Φ D' f p α β := by
  have hsel := selectedPart_sub_eq_of_nonzero P { Φ with openLine := f } D D' h₁ h₂ hm h₃ 1 0
    (fun {_ κ} C => IsOnePI C ∧ (ThreeLoop.IsVPSelfEnergy C ∨ ∀ t, κ t ≠ .gauge))
    (fun C => IsOnePI C) 4
    (fun g hg0 hg C => ⟨fun h => h.1, fun h => ⟨h, Or.inr (noGauge_of_grading_ne_zero_se hg0 hg C
      h)⟩⟩) ![p] ![p] ![] ![α] ![β] ![]
  have hfull := GradedProof.GEx2.selfEnergyPart_two_add_tree P Φ D D' h₁ h₂ hm h₃ f p α β
  simp only [selfEnergyPart, selfEnergySelPart, onePIPart, Matrix.of_apply] at hfull ⊢
  rw [show 2 * 2 = 4 from rfl] at hfull ⊢
  linear_combination (1 / I) * hsel + hfull

/-- The selected vertex reads only `e, ε, m_γ, Λ` of the parameters. -/
theorem familyVertex_params_congr {P Q : Params} (he : P.e = Q.e) (hε : P.ε = Q.ε)
    (hmγ : P.mγ = Q.mγ) (hΛ : P.Λ = Q.Λ) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Grading κ → Prop)
    (K : ℕ) : familyVertex P Φ D Sel K = familyVertex Q Φ D Sel K := by
  unfold familyVertex selectedPart
  simp only [GradedProof.GEx2.contractionValue_params_congr he hε hmγ hΛ]

/-- **The selected order-`5` vertices of data agreeing at level `0` differ by the level-`1`
trees.** -/
theorem familyVertex_five_sub (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D' : Counterterms F) (h₁ : D.d₁ Φ.openLine 0 = D'.d₁ Φ.openLine 0)
    (h₂ : D.d₂ Φ.openLine 0 = D'.d₂ Φ.openLine 0) (hm : D.dm Φ.openLine 0 = D'.dm Φ.openLine 0)
    (h₃ : D.d₃ 0 = D'.d₃ 0) (h₁' : ∀ f, D.d₁ f 0 = D'.d₁ f 0)
    (h₂' : ∀ f, D.d₂ f 0 = D'.d₂ f 0) (hm' : ∀ f, D.dm f 0 = D'.dm f 0)
    (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    familyVertex P Φ D selV 5 p' p μ =
      familyVertex P Φ D' selV 5 p' p μ +
        ((P.e ^ 4 * (D.d₁ Φ.openLine 1 - D'.d₁ Φ.openLine 1) * P.e : ℝ) : ℂ) •
          Dirac.gamma μ := by
  have hfull := GradedProof.GEx2.vertexPart_two_sub P Φ D D' Φ.openLine h₁ h₂ hm h₃ p' p μ
  ext i j
  have hsel := selectedPart_sub_eq_of_nonzero P Φ D D' h₁' h₂' hm' h₃ 1 1
    (fun {_ κ} C => IsOnePI C ∧ (VPChain.IsVPChain 1 C ∨ ∀ t, κ t ≠ .gauge))
    (fun C => IsOnePI C) 5
    (fun g hg0 hg C => ⟨fun h => h.1, fun h => ⟨h, Or.inr (noGauge_of_grading_ne_zero_v hg0 hg C
      h)⟩⟩) (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)
  have hij := congrFun (congrFun hfull i) j
  simp only [vertexPart, onePIPart, Matrix.add_apply, Matrix.of_apply] at hij
  simp only [familyVertex, Matrix.add_apply, Matrix.of_apply]
  rw [show 2 * 2 + 1 = 5 from rfl] at hij
  linear_combination (1 / I) * hsel + hij

end QED.ChainProof.SetCLink

end
