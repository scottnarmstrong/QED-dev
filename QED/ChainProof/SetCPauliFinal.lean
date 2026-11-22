/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliSumCB01

/-!
# Set (c): the remaining interface of (HS₆)

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(`QED/Frozen/ThreeLoop/VertexSetCPauliLimit.lean`, `DRAFT_SORRY`, not imported). The proposition
of (HS₆), verbatim, from inputs about the 36 two-loop-outer (main) classes and one regulator
limit:

* **`isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp`**: from the limit, covariance and
  per-class Pauli links of the main classes, canonical per-class values `βᴹ`
  (`QED.ChainProof.SetCPauli.ClsCanon`, e.g. `ClsLow`), `♯`-odd main-class limits
  (`QED.ChainProof.SetCPauli.SetCClassSharp`), and the regulator limit of the canonical
  fixed-regulator Pauli value `b = setCPauliB P₀ βᴹ` (`SetCRegLimitB`);
* **`isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp_disp`**: the same with the regulator
  limit towards the Stage K dispersion integral (`SetCRegLimitDisp`).

All 20 counterterm and VP-share classes are discharged unconditionally: their links and Pauli
limits by `QED.ChainProof.SetCPauli.isFormFactorPair_vertexSetC_pauli_limit_of_mainB`, their
reality by `QED.ChainProof.SetCPauli.setCClassSharp_ct_all`.
-/

@[expose] public section

open QED.WickModel (Params IsOnePI)
open QED.ChainProof.SetCPauli (MainIdx ClsPauliVal mainFam SetCClassLim SetCClassCov
  SetCClassPauli SetCClassSharp ClsCanon SetCRegLimitB SetCRegLimitDisp setCPauliB)

namespace QED.ThreeLoop

/-- **The remaining interface of set (c)**: (HS₆) from main-class inputs alone. For per-class
values `βᴹ` of the 36 main classes with limit, covariance and per-class Pauli links, canonical
(`ClsCanon`) and with `♯`-odd class limits, and the regulator limit of `b = setCPauliB P₀ βᴹ`,
the proposition of (HS₆) holds. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp (P₀ : Params)
    {βM : MainIdx → ClsPauliVal}
    (hM : ∀ r, SetCClassLim mainFam P₀ r) (hMc : ∀ r, SetCClassCov mainFam P₀ r)
    (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r)) (hcan : ∀ r, ClsCanon P₀ (βM r))
    (hSM : ∀ r, SetCClassSharp mainFam P₀ r) (hreg : SetCRegLimitB P₀ (setCPauliB P₀ βM))
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          (∃ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s) ∧
          ∀ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (a1SixSetC : ℂ)‖ < η :=
  QED.ChainProof.SetCPauli.isFormFactorPair_vertexSetC_pauli_limit_of_mainB P₀ hM hMc hPM
    (QED.ChainProof.SetCPauli.setCPauliB_hsum_of_mainSharp he hcan hM hPM hSM) hreg he hm η hη

/-- **The remaining interface of set (c), dispersion form**: as
`isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp`, with the regulator limit of
`b = setCPauliB P₀ βᴹ` towards the Stage K dispersion integral. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp_disp (P₀ : Params)
    {βM : MainIdx → ClsPauliVal}
    (hM : ∀ r, SetCClassLim mainFam P₀ r) (hMc : ∀ r, SetCClassCov mainFam P₀ r)
    (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r)) (hcan : ∀ r, ClsCanon P₀ (βM r))
    (hSM : ∀ r, SetCClassSharp mainFam P₀ r) (hreg : SetCRegLimitDisp P₀ (setCPauliB P₀ βM))
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          (∃ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s) ∧
          ∀ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (a1SixSetC : ℂ)‖ < η :=
  isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp P₀ hM hMc hPM hcan hSM
    (QED.ChainProof.SetCPauli.setCRegLimitB_of_disp hreg) he hm η hη

end QED.ThreeLoop

end
