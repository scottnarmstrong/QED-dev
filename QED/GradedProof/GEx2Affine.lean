/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.GEx2SE
public import QED.Frozen.Graded.VertexPartTwoEq

/-!
# The order-`e⁴` vertex and vacuum polarization are affine in the level-`1` data

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57).

* `vertexPart_params_congr`: the graded vertex (G₈ᵥ) reads only the fields `e, ε, m_γ, Λ` of the
  parameters.
* `vertexPart_two_sub`: for data agreeing at level `0` on the flavour `f` and the photon, the
  order-`5` vertices differ by the tree `e⁴ (d₁ - d₁') e γ^μ` (from (E-G₃)).
* `vacuumPolarizationPart_two_add_tree`: for data agreeing at level `0`, the order-`4` vacuum
  polarization plus `e⁴ d₃(1) (k² g - k k)` is the same (from the class split of (G-Π₂)).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.GEx2

open QED.Graded
open QED.WickModel (Params Contraction IsOnePI fermionSign)

/-- The graded value (G₅) reads only `e, ε, m_γ, Λ` of the parameters. -/
theorem contractionValue_params_congr {P Q : Params} (he : P.e = Q.e) (hε : P.ε = Q.ε)
    (hmγ : P.mγ = Q.mγ) (hΛ : P.Λ = Q.Λ) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (g : Grading κ) :
    contractionValue P Φ D C g = contractionValue Q Φ D C g := by
  unfold contractionValue regulatedAmplitude contractionAmplitude
  simp only [he, hε, hmγ, hΛ]

/-- The graded vertex (G₈ᵥ) reads only `e, ε, m_γ, Λ` of the parameters. -/
theorem vertexPart_params_congr {P Q : Params} (he : P.e = Q.e) (hε : P.ε = Q.ε)
    (hmγ : P.mγ = Q.mγ) (hΛ : P.Λ = Q.Λ) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (n : ℕ) :
    vertexPart P Φ D f n = vertexPart Q Φ D f n := by
  unfold vertexPart onePIPart selectedPart
  simp only [contractionValue_params_congr he hε hmγ hΛ]

/-- The parameters at which (E-G₃) applies to flavour `f`. -/
def vParams (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) :
    Params :=
  { P with
    m := Φ.mass f
    δ₁ := P.e ^ 2 * D.d₁ f 0
    δ₂ := P.e ^ 2 * D.d₂ f 0
    δm := P.e ^ 2 * D.dm f 0
    δ₃ := P.e ^ 2 * D.d₃ 0 }

/-- **The order-`5` vertex is the order-`5` vertex (F₉) at `vParams` plus the level-`1` tree.** -/
theorem vertexPart_two_eq_vParams (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    vertexPart P Φ D f 2 p' p μ =
      Lepton.vertexOrderFive (vParams P Φ D f) { Φ with openLine := f } p' p μ +
        ((P.e ^ 4 * D.d₁ f 1 * P.e : ℝ) : ℂ) • Dirac.gamma μ := by
  rw [vertexPart_params_congr (P := P) (Q := vParams P Φ D f) rfl rfl rfl rfl]
  exact vertexPart_two_eq (vParams P Φ D f) { Φ with openLine := f } D rfl rfl rfl rfl rfl p' p μ

/-- **The order-`5` vertices of data agreeing at level `0` differ by the level-`1` tree.** -/
theorem vertexPart_two_sub (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D' : Counterterms F) (f : F) (h₁ : D.d₁ f 0 = D'.d₁ f 0)
    (h₂ : D.d₂ f 0 = D'.d₂ f 0) (hm : D.dm f 0 = D'.dm f 0) (h₃ : D.d₃ 0 = D'.d₃ 0)
    (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    vertexPart P Φ D f 2 p' p μ =
      vertexPart P Φ D' f 2 p' p μ +
        ((P.e ^ 4 * (D.d₁ f 1 - D'.d₁ f 1) * P.e : ℝ) : ℂ) • Dirac.gamma μ := by
  have hv : vParams P Φ D f = vParams P Φ D' f := by simp only [vParams, h₁, h₂, hm, h₃]
  rw [vertexPart_two_eq_vParams, vertexPart_two_eq_vParams, hv, add_assoc, ← add_smul]
  congr 2
  push_cast
  ring

/-- The transverse tensor `k² g^{μν} - k^μ k^ν`. -/
noncomputable def vpT (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν

/-- **The order-`4` vacuum polarization plus the level-`1` tree reads only the level-`0`
data.** -/
theorem vacuumPolarizationPart_two_add_tree (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D' : Counterterms F) (h₁ : ∀ f, D.d₁ f 0 = D'.d₁ f 0)
    (h₂ : ∀ f, D.d₂ f 0 = D'.d₂ f 0) (hm : ∀ f, D.dm f 0 = D'.dm f 0) (h₃ : D.d₃ 0 = D'.d₃ 0)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    vacuumPolarizationPart P Φ D 2 k μ ν + ((P.e ^ 4 * D.d₃ 1 * vpT k μ ν : ℝ) : ℂ) =
      vacuumPolarizationPart P Φ D' 2 k μ ν + ((P.e ^ 4 * D'.d₃ 1 * vpT k μ ν : ℝ) : ℂ) := by
  have hv : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 0 2 κ),
      QED.GradedProof.VP2.val0 P Φ D k μ ν C = QED.GradedProof.VP2.val0 P Φ D' k μ ν C :=
    fun C => contractionValue_zero_congr P Φ D D' h₁ h₂ hm h₃ C _ _ _ _ _ _
  rw [QED.GradedProof.VP2.vacuumPolarizationPart_two_eq,
    QED.GradedProof.VP2.vacuumPolarizationPart_two_eq]
  simp only [hv, vpT]
  ring

end QED.GradedProof.GEx2

end
