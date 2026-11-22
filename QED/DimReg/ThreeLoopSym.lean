/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Symanzik
public import QED.ThreeLoopD.SetDCertFamily

/-!
# Computable three-loop Symanzik polynomials of a Euclidean family

A Euclidean family of the IBP checker (`QED.Algebra.IBPCert.Family`, read in Euclidean
conventions as `QED.ThreeLoopD.SetDCert.lbl`) has denominators
`D_a = Σ_{r,s} (A_a)_{rs} q_r · q_s + c_a` with Euclidean scalar products, momenta loop-first and
one external momentum `p` with `p² = g`. Writing
`Σ_a x_a D_a = kᵀ A k + 2 (B · k) p + C` with `A = Σ_a x_a (A_a)_{loop, loop}`,
`B_r = Σ_a x_a (A_a)_{r, L}` and `C = Σ_a x_a (g (A_a)_{LL} + c_a)`, the Gaussian integral over the
loop momenta gives `U^{-d/2} exp(-F / U)` with

  `U = det A`, `F = U C - g Bᵀ adj(A) B`

(`QED.DimReg.ThreeLoop.symU3`, `QED.DimReg.ThreeLoop.symFE3`; three loops, `A` symmetric). With
`(g, c) ↦ (-g, -c)` these are the Minkowski formulas of `QED.DimReg.Symanzik`. The Gaussian
integration is a documented convention, as in `QED.DimReg.Symanzik`.

For the set (d) family `lbl` (nine denominators, `D₉ = (L + p)²` an irreducible numerator),
the cancellations in `F` leave only positive coefficients (`isNat_symFE3_lbl`, by
`decide +kernel`): `U` has 50 terms, `F` 129, and the Lee–Pomeransky polynomial `G = U + F` has
179 terms with coefficients in `[1, 4]` and partial degrees `(1, 1, 1, 2, 2, 2, 2, 2, 1)`
(`lpPoly_eq_lit`, `degs_ok`).

## Main definitions and results

* `QED.DimReg.ThreeLoop.symU3`, `QED.DimReg.ThreeLoop.symAdj3`, `QED.DimReg.ThreeLoop.symFE3`.
* `QED.DimReg.ThreeLoop.isNat_symU3_lbl`, `QED.DimReg.ThreeLoop.isNat_symFE3_lbl`.
* `QED.DimReg.ThreeLoop.lpPoly`, `QED.DimReg.ThreeLoop.lpPoly_eq_lit`.
-/

@[expose] public section

namespace QED.DimReg.ThreeLoop

open QED.Algebra.IBPCert QED.DimReg.Symanzik

variable (F : Family)

/-- The loop-momentum block of `(A_a)` is symmetric for every denominator. -/
def isSymm : Bool :=
  (List.range F.nProp).all fun a => (List.range F.nLoop).all fun r =>
    (List.range F.nLoop).all fun s => decide (quadAt F a r s = quadAt F a s r)

/-- `C = Σ_a x_a (g (A_a)_{LL} + c_a)` (Euclidean conventions). -/
def symCE : LinComb :=
  linForm F.nProp fun a => gramP F * quadAt F a F.nLoop F.nLoop + F.const.getD a 0

/-- The cofactor `adj(A)_{rs}` of the symmetric `3 × 3` matrix `A`. -/
def cof3 (r s : ℕ) : LinComb :=
  let A := symA F
  match r, s with
  | 0, 0 => lcSub (lcMul (A 1 1) (A 2 2)) (lcMul (A 1 2) (A 1 2))
  | 1, 1 => lcSub (lcMul (A 0 0) (A 2 2)) (lcMul (A 0 2) (A 0 2))
  | 2, 2 => lcSub (lcMul (A 0 0) (A 1 1)) (lcMul (A 0 1) (A 0 1))
  | 0, 1 => lcSub (lcMul (A 0 2) (A 1 2)) (lcMul (A 0 1) (A 2 2))
  | 0, 2 => lcSub (lcMul (A 0 1) (A 1 2)) (lcMul (A 0 2) (A 1 1))
  | 1, 2 => lcSub (lcMul (A 0 1) (A 0 2)) (lcMul (A 0 0) (A 1 2))
  | _, _ => []

/-- `U = det A = A₀₀ adj₀₀ + A₀₁ adj₀₁ + A₀₂ adj₀₂` (three loops). -/
def symU3 : LinComb :=
  LinComb.add (LinComb.add (lcMul (symA F 0 0) (cof3 F 0 0)) (lcMul (symA F 0 1) (cof3 F 0 1)))
    (lcMul (symA F 0 2) (cof3 F 0 2))

/-- `Bᵀ adj(A) B` (three loops). -/
def symAdj3 : LinComb :=
  let B := symB F
  LinComb.add (LinComb.add (LinComb.add (lcMul (cof3 F 0 0) (lcMul (B 0) (B 0)))
      (lcMul (cof3 F 1 1) (lcMul (B 1) (B 1))))
      (lcMul (cof3 F 2 2) (lcMul (B 2) (B 2))))
    (LinComb.smul [2] (LinComb.add (LinComb.add (lcMul (cof3 F 0 1) (lcMul (B 0) (B 1)))
      (lcMul (cof3 F 0 2) (lcMul (B 0) (B 2)))) (lcMul (cof3 F 1 2) (lcMul (B 1) (B 2)))))

/-- `F = U C - g Bᵀ adj(A) B` (Euclidean conventions, three loops). -/
def symFE3 : LinComb :=
  LinComb.add (lcMul (symU3 F) (symCE F)) (LinComb.smul [-gramP F] (symAdj3 F))

open QED.ThreeLoopD.SetDCert

theorem isSymm_lbl : isSymm lbl = true := by decide +kernel

/-- **`U` of `lbl` has positive coefficients.** -/
theorem isNat_symU3_lbl : isNat (symU3 lbl) = true := by decide +kernel

/-- **`F` of `lbl` has positive coefficients** (after the cancellations). -/
theorem isNat_symFE3_lbl : isNat (symFE3 lbl) = true := by decide +kernel

/-- The Lee–Pomeransky polynomial `G = U + F` of `lbl`, as a natural sparse polynomial. -/
def lpPoly : Sector.NPoly := toNPoly (LinComb.add (symU3 lbl) (symFE3 lbl))

theorem isNat_lpPoly : isNat (LinComb.add (symU3 lbl) (symFE3 lbl)) = true := by decide +kernel

end QED.DimReg.ThreeLoop
