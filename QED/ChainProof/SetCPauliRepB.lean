/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliMainDK
public import QED.ChainProof.SetCMainDPauli

/-!
# Set (c): the remaining interface reduced to the `repB` classes

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The links of the
twenty-four `repD` classes are discharged: the limit and covariance links
(`QED.ChainProof.SetCMain.setCClassLim_inr`, `setCClassCov_inr`), the Pauli link with the
canonical value `clsPauliLim` (`QED.ChainProof.SetCMain.setCClassPauli_inr`), and the `♯`-law of
the longitudinal parts (`QED.ChainProof.SetCMain.dkSharpLink`).

* `setCBetaM`: the Pauli values of the main classes, `βᴮ i` on `repB i` and `clsPauliLim` on
  `repD i t`;
* **`isFormFactorPair_vertexSetC_pauli_limit_of_repB`**: (HS₆) from the limit, covariance, Pauli
  and `♯` links of the twelve `repB` classes and the regulator limit of
  `setCPauliB P₀ (setCBetaM P₀ βᴮ)`.
-/

@[expose] public section

open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCMain

open QED.ChainProof.SetCPauli (MainIdx ClsPauliVal mainFam clsPauliLim SetCClassLim SetCClassCov
  SetCClassPauli)

/-- The Pauli values of the main classes: `βᴮ i` on the class `repB i`, and the canonical value
`clsPauliLim` on the class `repD i t`. -/
noncomputable def setCBetaM (P₀ : Params) (βB : Fin 12 → ClsPauliVal) : MainIdx → ClsPauliVal
  | .inl i => βB i
  | .inr r => clsPauliLim mainFam P₀ (.inr r)

/-- The limit links of all main classes from those of the `repB` classes. -/
theorem setCClassLim_main_of_repB {P₀ : Params} (hB : ∀ i, SetCClassLim mainFam P₀ (.inl i)) :
    ∀ r, SetCClassLim mainFam P₀ r
  | .inl i => hB i
  | .inr (i, t) => setCClassLim_inr P₀ i t

/-- The covariance links of all main classes from those of the `repB` classes. -/
theorem setCClassCov_main_of_repB {P₀ : Params} (hB : ∀ i, SetCClassCov mainFam P₀ (.inl i)) :
    ∀ r, SetCClassCov mainFam P₀ r
  | .inl i => hB i
  | .inr (i, t) => setCClassCov_inr P₀ i t

/-- The Pauli links of all main classes, with the values `setCBetaM P₀ βᴮ`, from those of the
`repB` classes. -/
theorem setCClassPauli_main_of_repB {P₀ : Params} {βB : Fin 12 → ClsPauliVal}
    (hB : ∀ i, SetCClassPauli mainFam P₀ (.inl i) (βB i)) :
    ∀ r, SetCClassPauli mainFam P₀ r (setCBetaM P₀ βB r)
  | .inl i => hB i
  | .inr (i, t) => setCClassPauli_inr P₀ i t

end QED.ChainProof.SetCMain

namespace QED.ThreeLoop

open QED.ChainProof.SetCPauli (ClsPauliVal mainFam SetCClassLim SetCClassCov SetCClassPauli
  SetCClassSharp SetCRegLimitB setCPauliB)
open QED.ChainProof.SetCMain (setCBetaM)

/-- **The remaining interface of set (c), on the `repB` classes**: (HS₆) from the limit,
covariance, Pauli and `♯` links of the twelve `repB` classes, with Pauli values `βᴮ`, and the
regulator limit of `b = setCPauliB P₀ (setCBetaM P₀ βᴮ)`; the links of the twenty-four `repD`
classes are discharged. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_repB (P₀ : Params)
    {βB : Fin 12 → ClsPauliVal}
    (hB : ∀ i, SetCClassLim mainFam P₀ (.inl i)) (hBc : ∀ i, SetCClassCov mainFam P₀ (.inl i))
    (hPB : ∀ i, SetCClassPauli mainFam P₀ (.inl i) (βB i))
    (hSB : ∀ i, SetCClassSharp mainFam P₀ (.inl i))
    (hreg : SetCRegLimitB P₀ (setCPauliB P₀ (setCBetaM P₀ βB)))
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
  isFormFactorPair_vertexSetC_pauli_limit_of_repBSharp P₀
    (QED.ChainProof.SetCMain.setCClassLim_main_of_repB hB)
    (QED.ChainProof.SetCMain.setCClassCov_main_of_repB hBc)
    (QED.ChainProof.SetCMain.setCClassPauli_main_of_repB hPB) hSB hreg he hm η hη

end QED.ThreeLoop

end
