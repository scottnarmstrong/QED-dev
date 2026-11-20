/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.HeadlinePair
public import QED.WickModel.HeadlineSpinor
public import QED.Algebra.Spinor
public import QED.Frozen.Graded.IsSpinFormFactorPair

/-!
# (X₂) piece F: form-factor pairs of a shifted amplitude

Helper level for the Phase 5 Stage 2 goal (X₂)
`QED.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit` (decision D-57), piece F. At the
LSZ limit the order-`e⁵` amplitude is, on the spinor bases, the sandwich of the 1PI vertex `V`
plus a multiple `e c` of `ū' γ^μ u` (tree times photon legs, the level-`1` vertex counterterm)
plus a multiple `κ` of the sandwich of a vertex `W` with a form-factor pair `G` (the order-`e³`
vertex times the order-`e²` photon leg). Since the on-shell spinors span the Dirac solution spaces
(`QED.WickModel.Headline.sandwich_eq_zero_of_spinor`), the spin form-factor pairs (G-L₂) of the
amplitude are exactly the form-factor pairs (G₀) of `V` shifted by `(c + κ G₁, κ G₂)`.

* `isSpinFormFactorPair_iff_shift`.
-/

@[expose] public section

open Matrix Complex

namespace QED.GradedProof.X2

/-- **The spin form-factor pairs of a shifted amplitude.** If on the spinor bases
`M = ū' V u + e c ū' γ^μ u + κ ū' W u` and `W` has the form-factor pair `G`, then `F` is a spin
form-factor pair of `M` if and only if `(F₁ - c - κ G₁, F₂ - κ G₂)` is a form-factor pair of `V`. -/
theorem isSpinFormFactorPair_iff_shift {e m : ℝ} (hm : 0 < m) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) {M : Fin 2 → Fin 2 → Fin 4 → ℂ} {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {c κ : ℂ} {G : ℂ × ℂ}
    (hM : ∀ s' s μ, M s' s μ =
      Dirac.bar (Dirac.spinor m p' s') ⬝ᵥ (V μ *ᵥ Dirac.spinor m p s) +
        (e : ℂ) * c * (Dirac.bar (Dirac.spinor m p' s') ⬝ᵥ
          (Dirac.gamma μ *ᵥ Dirac.spinor m p s)) +
        κ * (Dirac.bar (Dirac.spinor m p' s') ⬝ᵥ (W μ *ᵥ Dirac.spinor m p s)))
    (hW : QED.OneLoop.IsFormFactorPair e m p' p W G) (F : ℂ × ℂ) :
    QED.Graded.IsSpinFormFactorPair e m p' p M F ↔
      QED.OneLoop.IsFormFactorPair e m p' p V (F.1 - c - κ * G.1, F.2 - κ * G.2) := by
  set S : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
    fun μ => ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν with hS
  have hu : ∀ s, Dirac.slash p *ᵥ Dirac.spinor m p s = -((m : ℂ) • Dirac.spinor m p s) :=
    fun s => Dirac.slash_mulVec_spinor m p hp s
  have hw : ∀ s', Dirac.bar (Dirac.spinor m p' s') ᵥ* Dirac.slash p' =
      -((m : ℂ) • Dirac.bar (Dirac.spinor m p' s')) :=
    fun s' => Dirac.bar_vecMul_slash m p' _ (Dirac.slash_mulVec_spinor m p' hp' s')
  constructor
  · intro h μ u w hu' hw'
    have key := WickModel.Headline.sandwich_eq_zero_of_spinor hm hp' hp hp0' hp0
      (X := V μ - (e : ℂ) • (((F.1 - c - κ * G.1) • Dirac.gamma μ -
        (I / (m : ℂ) * (F.2 - κ * G.2)) • S μ)))
      (fun s' s => by
        have h1 := h s' s μ
        have h2 := hW μ _ _ (hu s) (hw s')
        rw [hM, WickModel.Headline.dotProduct_formFactor_mulVec] at h1
        rw [WickModel.Headline.dotProduct_formFactor_mulVec] at h2
        rw [sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
          WickModel.Headline.dotProduct_formFactor_mulVec]
        linear_combination h1 - κ * h2) hu' hw'
    rw [sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      sub_eq_zero] at key
    exact key
  · intro h s' s μ
    have h1 := h μ _ _ (hu s) (hw s')
    have h2 := hW μ _ _ (hu s) (hw s')
    rw [WickModel.Headline.dotProduct_formFactor_mulVec] at h1 h2
    rw [hM, WickModel.Headline.dotProduct_formFactor_mulVec, h1, h2]
    ring

end QED.GradedProof.X2

end
