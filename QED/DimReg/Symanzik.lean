/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.IBPCertPilotData
public import QED.DimReg.SectorCert

/-!
# Computable Symanzik polynomials of an IBP family, checked by the kernel

The families of the IBP checker (`QED.Algebra.IBPCert.Family`) are given in momentum space:
`D_a = Σ_{r,s} (A_a)_{rs} q_r · q_s + c_a` (Minkowski, momenta loop-first, one external momentum
`p` with `p² = g`). After Wick rotation `D_a = -D_a^E` with
`D_a^E = Σ (A_a)_{rs} q_r^E · q_s^E - c_a` and `(p^E)² = -g`. Writing
`Σ_a x_a D_a^E = kᵀ A k + 2 (B · k) p + Σ_a x_a ((A_a)_{LL} (p^E)² - c_a)` and completing the
square,
the Symanzik polynomials are

  `U = det A`, `F = U · Σ_a x_a (-g (A_a)_{LL} - c_a) + g · Bᵀ adj(A) B`

(`QED.DimReg.Symanzik.symU`, `QED.DimReg.Symanzik.symF`, for one and two loops). They are
computed here with the sparse integer arithmetic of the IBP checker
(`QED.Algebra.IBPCert.LinComb`, labels = exponent vectors), so that cancellations are carried
out by the kernel. The Wick rotation and the Gaussian loop integration are a documented
convention, as in `QED.DimReg.OneLoopSchwinger`.

## Main results

* `QED.DimReg.Symanzik.symF_oneLoopSE`: `F = x₁²` at one loop (the kernel of
  `QED.DimReg.OneLoopSchwinger`).
* `QED.DimReg.Symanzik.isNat_symU_twoLoopSE`, `QED.DimReg.Symanzik.isNat_symF_twoLoopSE`: for
  the two-loop on-shell self-energy family `QED.Algebra.IBPCert.Pilot.twoLoopSE`, `U` and `F`
  have only positive coefficients once the cancellations are carried out (`decide +kernel`), and
  their explicit expansions.
-/

@[expose] public section

namespace QED.DimReg.Symanzik

open QED.Algebra.IBPCert

/-- The exponent vector of the variable `x_a` among `n`. -/
def unitLabel (n a : ℕ) : List ℤ := (List.range n).map fun k => if k = a then 1 else 0

/-- The product of two sparse polynomials (labels added entrywise). -/
def lcMul (l m : LinComb) : LinComb :=
  LinComb.ofTerms (l.flatMap fun t => m.map fun u => (List.zipWith (· + ·) t.1 u.1,
    Poly.mul t.2 u.2))

/-- The linear form `Σ_a w(a) x_a` in `n` variables. -/
def linForm (n : ℕ) (w : ℕ → ℤ) : LinComb :=
  LinComb.ofTerms ((List.range n).map fun a => (unitLabel n a, [w a]))

/-- The difference of two sparse polynomials. -/
def lcSub (l m : LinComb) : LinComb := LinComb.add l (LinComb.smul [-1] m)

variable (F : Family)

/-- The entry `(A_a)_{rs}`. -/
def quadAt (a r s : ℕ) : ℤ := ((F.quad.getD a []).getD r []).getD s 0

/-- `p² = g`. -/
def gramP : ℤ := (F.gram.getD 0 []).getD 0 0

/-- `A_{rs} = Σ_a x_a (A_a)_{rs}`. -/
def symA (r s : ℕ) : LinComb := linForm F.nProp fun a => quadAt F a r s

/-- `B_r = Σ_a x_a (A_a)_{rL}`. -/
def symB (r : ℕ) : LinComb := symA F r F.nLoop

/-- `C = Σ_a x_a (-g (A_a)_{LL} - c_a)`. -/
def symC : LinComb :=
  linForm F.nProp fun a => -(gramP F * quadAt F a F.nLoop F.nLoop) - F.const.getD a 0

/-- `U = det A` (one and two loops). -/
def symU : LinComb :=
  match F.nLoop with
  | 1 => symA F 0 0
  | 2 => lcSub (lcMul (symA F 0 0) (symA F 1 1)) (lcMul (symA F 0 1) (symA F 0 1))
  | _ => []

/-- `Bᵀ adj(A) B` (one and two loops). -/
def symAdj : LinComb :=
  match F.nLoop with
  | 1 => lcMul (symB F 0) (symB F 0)
  | 2 => LinComb.add (lcSub (lcMul (lcMul (symB F 0) (symB F 0)) (symA F 1 1))
      (LinComb.smul [2] (lcMul (lcMul (symB F 0) (symB F 1)) (symA F 0 1))))
      (lcMul (lcMul (symB F 1) (symB F 1)) (symA F 0 0))
  | _ => []

/-- `F = U C + g Bᵀ adj(A) B`. -/
def symF : LinComb := LinComb.add (lcMul (symU F) (symC F)) (LinComb.smul [gramP F] (symAdj F))

/-- Every exponent is nonnegative and every coefficient is a positive constant. -/
def isNat (l : LinComb) : Bool :=
  l.all fun t => t.1.all (fun e => decide (0 ≤ e)) &&
    match t.2 with
    | [c] => decide (0 < c)
    | _ => false

/-- The conversion to a sparse polynomial with natural coefficients. -/
def toNPoly (l : LinComb) : Sector.NPoly := l.map fun t => (t.1.map Int.toNat, (t.2.headD 0).toNat)

/-- At one loop, `U = x₀ + x₁` and `F = x₁²`. -/
theorem symU_oneLoopSE : symU Pilot.oneLoopSE = [([0, 1], [1]), ([1, 0], [1])] := by
  decide +kernel

theorem symF_oneLoopSE : symF Pilot.oneLoopSE = [([0, 2], [1])] := by
  decide +kernel

/-- **`U` of `twoLoopSE` has positive coefficients.** -/
theorem isNat_symU_twoLoopSE : isNat (symU Pilot.twoLoopSE) = true := by
  decide +kernel

/-- **`F` of `twoLoopSE` has positive coefficients** (after the cancellations). -/
theorem isNat_symF_twoLoopSE : isNat (symF Pilot.twoLoopSE) = true := by
  decide +kernel

/-- The expansion of `U` for `twoLoopSE`:
`x₃x₄ + x₂x₄ + x₂x₃ + x₁x₄ + x₁x₂ + x₀x₄ + x₀x₃ + x₀x₁`. -/
theorem symU_twoLoopSE : symU Pilot.twoLoopSE =
    [([0, 0, 0, 1, 1], [1]), ([0, 0, 1, 0, 1], [1]), ([0, 0, 1, 1, 0], [1]),
      ([0, 1, 0, 0, 1], [1]), ([0, 1, 1, 0, 0], [1]), ([1, 0, 0, 0, 1], [1]),
      ([1, 0, 0, 1, 0], [1]), ([1, 1, 0, 0, 0], [1])] := by
  decide +kernel

/-- The expansion of `F` for `twoLoopSE`:
`x₀(x₃ + x₄)² + x₁(x₂ + x₄)² + x₂²x₃ + x₂²x₄ + x₂x₃² + 2x₂x₃x₄ + x₂x₄² + x₃²x₄ + x₃x₄²`. -/
theorem symF_twoLoopSE : symF Pilot.twoLoopSE =
    [([0, 0, 0, 1, 2], [1]), ([0, 0, 0, 2, 1], [1]), ([0, 0, 1, 0, 2], [1]),
      ([0, 0, 1, 1, 1], [2]), ([0, 0, 1, 2, 0], [1]), ([0, 0, 2, 0, 1], [1]),
      ([0, 0, 2, 1, 0], [1]), ([0, 1, 0, 0, 2], [1]), ([0, 1, 1, 0, 1], [2]),
      ([0, 1, 2, 0, 0], [1]), ([1, 0, 0, 0, 2], [1]), ([1, 0, 0, 1, 1], [2]),
      ([1, 0, 0, 2, 0], [1])] := by
  decide +kernel

end QED.DimReg.Symanzik
