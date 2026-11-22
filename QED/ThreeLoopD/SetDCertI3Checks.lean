/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDCertFamily
public import QED.Algebra.IBPCertSym
public import QED.Algebra.IBPCertSectorSound
public import QED.ThreeLoopD.SetDCertI3All

/-!
# The set (d) dotted integral: checks of the constants and the master list

The checks that do not depend on the parts: the merged template is the template of
`QED.ThreeLoopD.SetDCert.lbl` (`QED.Algebra.IBPCert.Sector.mtOk`), the factors of the common
denominator, the scaleless sectors, all seed blocks, the ranges of the labels, the norm bound
at `x₀`, and the master list of the checker as the five masters plus the symmetry
terms (`QED.ThreeLoopD.SetDCertI3.symTerms`).
-/

@[expose] public section

namespace QED.ThreeLoopD.SetDCertI3

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Sector QED.ThreeLoopD.SetDCert

theorem sdMT_ok : mtOk lbl sdCtx 132 27 = true := by decide +kernel

theorem sdFac_ok : facOk sdCtx sdFac sdQE sdNF = true := by decide +kernel

theorem sdZS_eq : sdZS = lbl.zeroSectors.map fun S => S.map fun a => (a, sdCtx.B ^ a) := by
  decide +kernel

theorem sdBlocks_ok :
    sdBlocks.all (GBlock.ok sdCtx 3 4 9 4 sdQE sdYb sdNF sdZS) = true := by
  simp only [sdBlocks, rApp_eq, List.all_append, sdB0_ok, sdB1_ok, Bool.and_self]

theorem sdClaim_range : (sdTarget ++ sdMs).all (fun t => inRange 8 3 9 t.1) = true := by
  decide +kernel

theorem sdBound : (sdBlocks.map fun b => b.seeds.length).sum * (27 * (sdYb * 132)) +
    Poly.norm1 sdDen * (sdTarget.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum +
      (sdMs.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum < sdCtx.x0 := by
  decide +kernel

theorem sdTargetL_lt : sdTargetL.length < 4 := by decide +kernel

theorem sdMsL_lt : sdMsL.length < 4 := by decide +kernel

theorem sdDen_ne_zero : Poly.isZero sdDen = false := by decide +kernel

/-- The terms of symmetry entries `(σ, ν, ζ)`: `(ν, ζ)` and `(permLabel σ ν, -ζ)`. -/
def symTerms (S : List (List ℕ × List ℤ × Poly)) : List (List ℤ × Poly) :=
  S.flatMap fun e => [(e.2.1, e.2.2), (permLabel e.1 e.2.1, Poly.neg e.2.2)]

/-- The master list of the checker is the five masters plus the symmetry terms: their
difference normalizes to the empty combination. -/
theorem sdMs_comb :
    LinComb.ofTerms (sdMs ++ LinComb.smul [-1] (sdMasters ++ symTerms sdSyms)) = [] := by
  decide +kernel

end QED.ThreeLoopD.SetDCertI3
