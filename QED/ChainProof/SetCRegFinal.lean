/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegFront
public import QED.ChainProof.SetCRegMainBDK

/-!
# Set (c): the regulator limit reduced to the counterterm leaves and the Stage L limit

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The main classes
are in dispersion form (`QED.ChainProof.SetCRegDisp.isDispPV_mainBD`, kernels `uBD P₀ i`), so the
regulator limit `SetCRegLimitB` of `b = setCPauliB P₀ (setCBetaM P₀ βᴮ)`,
`βᴮ i = clsPauliLim mainFam P₀ (.inl i)`, follows from three inputs:

* `hS : ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀)`: the VP-share classes (`hCtS`);
* `hB : CBLoBEq P₀`: the mass part of the counterterm placements `k = 0, 1` (`hCtCB`);
* `hReg`: the regulator limit of the total kernel, `IsRegPiece (setCKerRe P₀ (uBD P₀))
  setCKKernelPairSum` (pointwise in `T ≥ 4` towards the Stage K kernel sum, uniformly
  `O(T^{-1/2})`), or in its split form the matching `hMatch` with the five regulated pieces.

## Main statements

* **`setCRegLimitB_of_shell_cbLo`**, **`setCRegLimitB_of_shell_cbLo_match`**;
* **`QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit_of_shell_cbLo`**: the proposition of
  (HS₆) from `hS`, `hB` and `hReg`.
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCK QED.ChainProof.SetCPauli QED.ChainProof.SetCMain

/-- **The regulator limit of set (c) from the counterterm leaves and the Stage L limit.** -/
theorem setCRegLimitB_of_shell_cbLo {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hS : ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀)) (hB : CBLoBEq P₀)
    (hReg : IsRegPiece (setCKerRe P₀ (uBD P₀)) setCKKernelPairSum) :
    SetCRegLimitB P₀ (setCPauliB P₀ (setCBetaM P₀ fun i => clsPauliLim mainFam P₀ (.inl i))) :=
  setCRegLimitB_of_leaves he hm (fun _ _ _ _ _ _ _ _ hA i => isDispPV_mainBD hA i) hS hB hReg

/-- **The regulator limit of set (c) from the counterterm leaves and the matching** against the
five regulated Stage K pieces. -/
theorem setCRegLimitB_of_shell_cbLo_match {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    {aL aSI aCI aX aSC : ℝ → ℝ → ℝ → ℝ}
    (hS : ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀)) (hB : CBLoBEq P₀)
    (hMatch : ∀ mγ Λ T : ℝ, 0 < mγ → mγ < Λ → 4 ≤ T →
      (1 / I) * (∑ i, uBD P₀ i mγ Λ T + ∑ k, uCBC P₀ k mγ Λ T + ∑ k, uSC P₀ k mγ Λ T) =
        ((P₀.e ^ 6 / (64 * π ^ 6) *
          (aL mγ Λ T + aSI mγ Λ T + aCI mγ Λ T + aX mγ Λ T + aSC mγ Λ T) : ℝ) : ℂ))
    (hL : IsRegPiece aL SetCK.lPair) (hSI : IsRegPiece aSI SetCK.selfIn)
    (hCI : IsRegPiece aCI SetCK.cornIn)
    (hX : IsRegPiece aX fun T => SetCK.crossUnit 0 T + SetCK.crossUnit T 0)
    (hSC : IsRegPiece aSC fun T => SetCK.scOutS T + SetCK.scOutC T) :
    SetCRegLimitB P₀ (setCPauliB P₀ (setCBetaM P₀ fun i => clsPauliLim mainFam P₀ (.inl i))) :=
  setCRegLimitB_of_match he hm (fun _ _ _ _ _ _ _ _ hA i => isDispPV_mainBD hA i) hS hB hMatch
    hL hSI hCI hX hSC

end QED.ChainProof.SetCRegDisp

namespace QED.ThreeLoop

open QED.ChainProof.SetCRegDisp QED.ChainProof.SetCK

/-- **(HS₆) from the counterterm leaves and the Stage L limit**: the VP-share leaf `hS`, the mass
part `hB` of the counterterm placements `k = 0, 1`, and the regulator limit `hReg` of the total
kernel. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_shell_cbLo (P₀ : Params)
    (hS : ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀))
    (hB : CBLoBEq P₀) (hReg : IsRegPiece (setCKerRe P₀ (uBD P₀)) setCKKernelPairSum)
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
  isFormFactorPair_vertexSetC_pauli_limit_of_regB P₀
    (setCRegLimitB_of_shell_cbLo he hm hS hB hReg) he hm η hη

end QED.ThreeLoop

end
