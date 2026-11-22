/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopSESector
public import QED.DimReg.SectorForms
public import QED.DimReg.LPCont
public import QED.DimReg.TwoLoopSEForms

/-!
# The two-loop self-energy family: certified sector data and its continuation

The sector trees of `QED.DimReg.TwoLoopSESector` are packaged as `QED.DimReg.LPSectorData` for the
Lee–Pomeransky polynomial `G = U + F` of `QED.Algebra.IBPCert.Pilot.twoLoopSE`
(`QED.DimReg.TwoLoopSESector.sectorData`). The box polynomials are the ones of
`QED.DimReg.Sector.boxPolyF` with `D = (1, 1, 2, 2, 2)`, and the checker is re-run on them for all
`2⁵` flag lists by `decide +kernel` (`QED.DimReg.TwoLoopSESector.check_flags`).
-/

@[expose] public section

namespace QED.DimReg.TwoLoopSESector

open QED.DimReg.Sector

/-- The partial-degree bounds `D = (1, 1, 2, 2, 2)`. -/
def degD : List ℕ := [1, 1, 2, 2, 2]

/-- The splitting tree of a flag list (the empty tree if the flags are not listed). -/
def treeOfFlags (fl : List Bool) : SplitTree 5 := (boxTrees.lookup fl).getD .leaf

theorem deg_lpPoly : ∀ t ∈ lpPoly, ∀ i : Fin 5, t.1.getD i 0 ≤ degD.getD i 0 := by
  decide +kernel

/-- **The sector checker passes on every box**, for the box polynomials `boxPolyF`. -/
theorem check_flags : ∀ b₀ b₁ b₂ b₃ b₄ : Bool,
    (⟨treeOfFlags [b₀, b₁, b₂, b₃, b₄],
      [boxPolyF (flagSet (N := 5) [b₀, b₁, b₂, b₃, b₄]) degD lpPoly]⟩ : SDCert 5).check = true := by
  decide +kernel

/-- The leaf minima of the box with flags `fl`. -/
def minOfFlags (fl : List Bool) (ps : List (Fin 5 × Fin 5)) : List ℕ :=
  NPoly.minE ((boxPolyF (flagSet (N := 5) fl) degD lpPoly).pull ps)

/-- **The generated leaf exponents are the computed ones**, on every box. -/
theorem leafFormTable_eq : ∀ b₀ b₁ b₂ b₃ b₄ : Bool,
    ((leafFormTable.lookup [b₀, b₁, b₂, b₃, b₄]).getD []) =
      (treeOfFlags [b₀, b₁, b₂, b₃, b₄]).paths.map fun ps =>
        leafForms degD [b₀, b₁, b₂, b₃, b₄] ps (minOfFlags [b₀, b₁, b₂, b₃, b₄] ps) := by
  decide +kernel

/-- **Every leaf exponent increases along the line** `ν = 1 + λ`, `d / 2 = d₀ / 2 + 2λ`: its slope
`Σᵢ aᵢ + 2 c_d` lies in `[1, 4]`. -/
theorem slope_leafFormTable : ∀ e ∈ leafFormTable, ∀ leaf ∈ e.2, ∀ f ∈ leaf,
    1 ≤ f.2.1.sum + 2 * f.2.2 ∧ f.2.1.sum + 2 * f.2.2 ≤ 4 := by
  decide +kernel

theorem flagsOf_eq (T : Finset (Fin 5)) : flagsOf T =
    [decide (0 ∈ T), decide (1 ∈ T), decide (2 ∈ T), decide (3 ∈ T), decide (4 ∈ T)] := rfl

/-- **The certified sector data of the two-loop self-energy family.** -/
def sectorData : LPSectorData 5 where
  G := lpPoly
  D := degD
  tree T := treeOfFlags (flagsOf T)
  deg := deg_lpPoly
  check T := by
    have h := check_flags (decide (0 ∈ T)) (decide (1 ∈ T)) (decide (2 ∈ T)) (decide (3 ∈ T))
      (decide (4 ∈ T))
    rwa [← flagsOf_eq, flagSet_flagsOf] at h

end QED.DimReg.TwoLoopSESector
