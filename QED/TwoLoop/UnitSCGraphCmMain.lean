/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphCmData
public import QED.TwoLoop.UnitSCGraphCpMain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The pointwise second-order coefficients of the `C₋` numerator

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half, the analogue of
`QED/TwoLoop/UnitSCGraphCpMain.lean` for the corner class `C₋`. At a point `z` of the eight line
parameters, with the outer electron pair `z_o = z₂ + z₃` (split `z₂`), the inner electrons
`y₃ = z₁`, `y₄ = z₀`, the outer photon `z_a = z₅ + z₇` and the inner photon `z_b = z₄ + z₆`
(`cmza`, `cmzb`; for `C₋` the rows `4, 6` of the loop matrix are the inner photon),
`U = (z₀ + z₁ + z_b)(z₀ + z₂ + z₃ + z_b + z_a) - (z₀ + z_b)²` (`cmU`) and
`W = y₃ z_b + (y₃ + y₄ + z_b) z_o` (`cmW`), at `m = 1`, `e = 1`:

* `secondCoeff_cmT1`: `c₂[T₁] = (Λ² - m_γ²)² (6/K) · W M₁/(2U⁶)`;
* `secondCoeff_cmT2`: `c₂[T₂] = (Λ² - m_γ²)² (2/K) · (-M₂/(2U⁵))`;
* `secondCoeff_cmT3`: `c₂[T₃] = 0`,

with the explicit polynomials `M₁` (`cmM1`) and `M₂` (`cmM2`): the formulas of `C₊` under the
relabelling of the mirror symmetry. Hence (`openZero_Cm_eq`)
`openZero .Cm P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴`. Checked against exact Dirac traces
(`scripts/numerics/sc_graph/cm_planar.py`, `c_identities.py`).
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitSCGraph

open Filter Topology
open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace
open QED.TwoLoop.Bridge QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexPoint)
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikU symanzikV symanzikVector
  symanzikMatrix)
open Pl

/-! ### The parameters -/

section Params

variable (z : Fin 8 → ℝ)

/-- The outer photon `z_a = z₅ + z₇` of `C₋`. -/
def cmza : ℝ := z 5 + z 7
/-- The inner photon `z_b = z₄ + z₆` of `C₋`. -/
def cmzb : ℝ := z 4 + z 6

/-- The first Symanzik function of `C₋`. -/
def cmU : ℝ :=
  (z 0 + z 1 + cmzb z) * (z 0 + z 2 + z 3 + cmzb z + cmza z) - (z 0 + cmzb z) ^ 2

/-- `W = y₃ z_b + (y₃ + y₄ + z_b) z_o`. -/
def cmW : ℝ := z 0*z 2 + z 0*z 3 + z 1*z 2 + z 1*z 3 + z 1*cmzb z + z 2*cmzb z + z 3*cmzb z

/-- Part 1 of `cmM1p`. -/
def cmM1pa (a b c d e f : ℝ) : ℝ :=
  a ^ 3 * b ^ 3 + 2 * a ^ 3 * b ^ 2 * c + a ^ 3 * b * c ^ 2 - 2 * a ^ 3 * b * d ^ 2 - a ^ 3 * c
    ^ 2 * d + a ^ 3 * c ^ 2 * e - 2 * a ^ 3 * c * d ^ 2 + 2 * a ^ 3 * c * e ^ 2 - a ^ 3 * d ^ 3
    - 2 * a ^ 3 * d ^ 2 * e + a ^ 3 * e ^ 3 + 2 * a ^ 2 * b ^ 3 * c - a ^ 2 * b * d ^ 3 - 3 * a
    ^ 2 * d ^ 3 * f + a * b ^ 3 * c ^ 2 + a * b ^ 3 * f ^ 2 + a * b ^ 2 * d ^ 3 - 3 * a * d ^ 3
    * f ^ 2 + 2 * a * e ^ 3 * f ^ 2 + b ^ 3 * c ^ 2 * d + b ^ 3 * c ^ 2 * e + b ^ 3 * d ^ 3 + b
    ^ 3 * d * f ^ 2 + b ^ 3 * e ^ 3 + b ^ 3 * e * f ^ 2 + b ^ 2 * d ^ 3 * f - b ^ 2 * d * f ^ 3
    + b ^ 2 * e * f ^ 3 - b * d ^ 3 * f ^ 2 - 2 * b * d ^ 2 * f ^ 3 + 2 * b * e ^ 3 * f ^ 2 + b
    * e ^ 2 * f ^ 3 - c ^ 2 * d * f ^ 3 + c ^ 2 * e * f ^ 3 - 2 * c * d ^ 2 * f ^ 3 + c * e ^ 2
    * f ^ 3 - d ^ 3 * f ^ 3 - 2 * d ^ 2 * e * f ^ 3 - d * e ^ 2 * f ^ 3

/-- Part 2 of `cmM1p`. -/
def cmM1pb (a b c d e f : ℝ) : ℝ :=
  3 * a ^ 3 * b ^ 2 * e - a ^ 3 * b * c * d + 3 * a ^ 3 * b * e ^ 2 - a ^ 3 * c * d * e + 4 * a
    ^ 2 * b ^ 3 * d + 3 * a ^ 2 * b ^ 3 * e + 2 * a ^ 2 * b ^ 3 * f + 3 * a ^ 2 * b ^ 2 * c ^ 2
    + 3 * a ^ 2 * b ^ 2 * d ^ 2 + 6 * a ^ 2 * b ^ 2 * e ^ 2 - a ^ 2 * b * c ^ 2 * d + a ^ 2 * b
    * d ^ 2 * e - 5 * a ^ 2 * b * d ^ 2 * f + 3 * a ^ 2 * b * e ^ 3 - 6 * a ^ 2 * c * d ^ 2 * f
    - 5 * a ^ 2 * d ^ 2 * e * f + a ^ 2 * d * e ^ 2 * f + 3 * a ^ 2 * e ^ 3 * f + 4 * a * b ^ 3
    * d ^ 2 + 3 * a * b ^ 3 * e ^ 2 + a * b ^ 2 * c ^ 2 * d + 3 * a * b ^ 2 * e ^ 3 + a * b * c
    ^ 2 * f ^ 2 - 6 * a * b * d ^ 2 * f ^ 2 - 3 * a * c ^ 2 * d * f ^ 2 - 6 * a * c * d ^ 2 * f
    ^ 2 - 5 * a * d ^ 2 * e * f ^ 2 + 2 * b ^ 3 * c * d ^ 2 + 2 * b ^ 3 * c * e ^ 2 + 4 * b ^ 3
    * d ^ 2 * e + 2 * b ^ 3 * d ^ 2 * f + 4 * b ^ 3 * d * e ^ 2 + 2 * b ^ 3 * e ^ 2 * f + b ^ 2
    * c ^ 2 * d * f + 3 * b ^ 2 * e ^ 3 * f + 3 * b ^ 2 * e ^ 2 * f ^ 2 - b * c ^ 2 * d * f ^ 2
    - b * d * e * f ^ 3 - c * d * e * f ^ 3

/-- Part 3 of `cmM1p`. -/
def cmM1pc (a b c d e f : ℝ) : ℝ :=
  4 * a ^ 3 * b * c * e + 5 * a ^ 2 * b ^ 2 * c * f + 4 * a ^ 2 * b * c ^ 2 * e + 3 * a ^ 2 * b
    * c ^ 2 * f - 2 * a ^ 2 * b * c * d ^ 2 + 4 * a ^ 2 * b * d * e ^ 2 - 3 * a ^ 2 * c ^ 2 * d
    * f + 4 * a ^ 2 * c ^ 2 * e * f + 5 * a * b ^ 3 * c * d + 4 * a * b ^ 3 * c * e + 2 * a * b
    ^ 3 * c * f + 5 * a * b ^ 3 * d * f + 4 * a * b ^ 3 * e * f + 4 * a * b ^ 2 * c ^ 2 * e + 2
    * a * b ^ 2 * c ^ 2 * f + 2 * a * b ^ 2 * c * d ^ 2 + 2 * a * b ^ 2 * c * f ^ 2 + 2 * a * b
    ^ 2 * d ^ 2 * f - 2 * a * b ^ 2 * d * f ^ 2 + 4 * a * b ^ 2 * e * f ^ 2 - 2 * a * b * d ^ 3
    * f + 6 * a * b * e ^ 3 * f + 5 * a * b * e ^ 2 * f ^ 2 + 4 * a * c ^ 2 * e * f ^ 2 + 5 * b
    ^ 3 * c * d * e + 2 * b ^ 3 * c * d * f + 2 * b ^ 3 * c * e * f + 5 * b ^ 3 * d * e * f + 3
    * b ^ 2 * c ^ 2 * e * f + 2 * b ^ 2 * c * d ^ 2 * f + 5 * b ^ 2 * c * e ^ 2 * f + 4 * b ^ 2
    * c * e * f ^ 2 + 4 * b ^ 2 * d * e * f ^ 2 + 3 * b * c ^ 2 * e * f ^ 2 - 2 * b * c * d ^ 2
    * f ^ 2 - 2 * b * c * d * f ^ 3 + 4 * b * c * e ^ 2 * f ^ 2 + 2 * b * c * e * f ^ 3 + 2 * b
    * d * e ^ 2 * f ^ 2

/-- Part 4 of `cmM1p`. -/
def cmM1pd (a b c d e f : ℝ) : ℝ :=
  6 * a ^ 2 * b ^ 2 * c * d + 8 * a ^ 2 * b ^ 2 * c * e + 8 * a ^ 2 * b ^ 2 * d * e + 7 * a ^ 2
    * b ^ 2 * e * f + 5 * a ^ 2 * b * c * d * e - 2 * a ^ 2 * b * c * d * f + 6 * a ^ 2 * b * c
    * e ^ 2 + 12 * a ^ 2 * b * c * e * f + a ^ 2 * b * d * e * f + 8 * a ^ 2 * b * e ^ 2 * f - a
    ^ 2 * c * d * e * f + 7 * a ^ 2 * c * e ^ 2 * f + 8 * a * b ^ 3 * d * e + 11 * a * b ^ 2 * c
    * d * e + 4 * a * b ^ 2 * c * d * f + 6 * a * b ^ 2 * c * e ^ 2 + 12 * a * b ^ 2 * c * e * f
    + 7 * a * b ^ 2 * d ^ 2 * e + 8 * a * b ^ 2 * d * e ^ 2 + 12 * a * b ^ 2 * d * e * f + 10 *
    a * b ^ 2 * e ^ 2 * f - 2 * a * b * c ^ 2 * d * f + 8 * a * b * c ^ 2 * e * f - 4 * a * b *
    c * d ^ 2 * f + 10 * a * b * c * d * e * f - 5 * a * b * c * d * f ^ 2 + 12 * a * b * c * e
    ^ 2 * f + 8 * a * b * c * e * f ^ 2 + 2 * a * b * d ^ 2 * e * f + 8 * a * b * d * e ^ 2 * f
    - 2 * a * b * d * e * f ^ 2 - a * c * d * e * f ^ 2 + 6 * a * c * e ^ 2 * f ^ 2 + 9 * b ^ 2
    * c * d * e * f + 6 * b ^ 2 * d ^ 2 * e * f + 7 * b ^ 2 * d * e ^ 2 * f + 3 * b * c * d * e
    * f ^ 2

/-- Part 1 of `cmM2p`. -/
def cmM2pa (a b c d e f : ℝ) : ℝ :=
  -a ^ 3 * b ^ 2 + a ^ 3 * b * d - a ^ 3 * c ^ 2 + a ^ 3 * c * d + 2 * a ^ 3 * d ^ 2 + a ^ 3 * d
    * e - a ^ 3 * e ^ 2 + a ^ 2 * b ^ 3 - a ^ 2 * b * e ^ 2 - a ^ 2 * c * e ^ 2 - a * b ^ 3 * d
    - a * b ^ 2 * c ^ 2 + a * b ^ 2 * e ^ 2 + b ^ 3 * c ^ 2 - b ^ 3 * c * d - 2 * b ^ 3 * d ^ 2
    + b ^ 3 * e ^ 2 + b ^ 3 * f ^ 2 + b ^ 2 * c ^ 2 * f - b ^ 2 * c * e ^ 2 + b ^ 2 * e * f ^ 2
    - b ^ 2 * f ^ 3 - b * c ^ 2 * f ^ 2 + b * d * f ^ 3 - c ^ 2 * f ^ 3 + c * d * f ^ 3 - c * e
    ^ 2 * f ^ 2 + 2 * d ^ 2 * f ^ 3 - 2 * e ^ 2 * f ^ 3

/-- Part 2 of `cmM2p`. -/
def cmM2pb (a b c d e f : ℝ) : ℝ :=
  -2 * a ^ 3 * b * c - 2 * a ^ 3 * b * e - 2 * a ^ 3 * c * e - 3 * a ^ 2 * b ^ 2 * f - 3 * a ^ 2
    * b * c ^ 2 - a ^ 2 * c ^ 2 * e - 2 * a ^ 2 * c ^ 2 * f - a ^ 2 * d ^ 2 * e - a ^ 2 * d * e
    ^ 2 - 3 * a ^ 2 * e ^ 2 * f + 2 * a * b ^ 3 * c - 4 * a * b ^ 2 * d ^ 2 - 3 * a * b ^ 2 * f
    ^ 2 - 2 * a * c ^ 2 * f ^ 2 - 4 * a * e ^ 2 * f ^ 2 - b ^ 3 * d * e - b ^ 3 * d * f - b ^ 2
    * c ^ 2 * e - b ^ 2 * d ^ 2 * e - 2 * b ^ 2 * d ^ 2 * f - b ^ 2 * d * e ^ 2 - 2 * b ^ 2 * e
    ^ 2 * f - 2 * b * c * f ^ 3 - 5 * b * e ^ 2 * f ^ 2 - 3 * b * e * f ^ 3 - c ^ 2 * e * f ^ 2
    - 3 * c * e * f ^ 3 - d ^ 2 * e * f ^ 2 - d * e ^ 2 * f ^ 2

/-- Part 3 of `cmM2p`. -/
def cmM2pc (a b c d e f : ℝ) : ℝ :=
  2 * a ^ 2 * b ^ 2 * c + 2 * a ^ 2 * b ^ 2 * d - 3 * a ^ 2 * b * c * d - a ^ 2 * b * c * e - 5
    * a ^ 2 * b * c * f - 6 * a ^ 2 * b * e * f - 5 * a ^ 2 * c * e * f + 7 * a ^ 2 * d ^ 2 * f
    + 2 * a * b ^ 3 * e + 2 * a * b ^ 3 * f - 5 * a * b ^ 2 * c * d - 3 * a * b ^ 2 * e * f - 2
    * a * b * c ^ 2 * e - 3 * a * b * c ^ 2 * f - 2 * a * b * c * e ^ 2 - 5 * a * b * c * f ^ 2
    - 2 * a * b * d * e ^ 2 - 5 * a * b * e ^ 2 * f - 7 * a * b * e * f ^ 2 - 6 * a * c * e * f
    ^ 2 + 7 * a * d ^ 2 * f ^ 2 + 2 * b ^ 3 * c * e + 2 * b ^ 3 * c * f + 2 * b ^ 3 * e * f - b
    ^ 2 * c * d * f - b ^ 2 * d * e * f + b * c * d * f ^ 2 - 3 * b * c * e * f ^ 2 + 2 * b * d
    ^ 2 * f ^ 2

/-- Part 4 of `cmM2p`. -/
def cmM2pd (a b c d e f : ℝ) : ℝ :=
  2 * a ^ 2 * b * d * e + 4 * a ^ 2 * b * d * f - 2 * a ^ 2 * c * d * e + 5 * a ^ 2 * c * d * f
    + 4 * a ^ 2 * d * e * f + 3 * a * b ^ 2 * c * e - 2 * a * b ^ 2 * c * f - 2 * a * b ^ 2 * d
    * f - 4 * a * b * c * d * e - 2 * a * b * c * e * f - 2 * a * b * d ^ 2 * e + 3 * a * b * d
    ^ 2 * f + 4 * a * b * d * e * f + 4 * a * b * d * f ^ 2 - 2 * a * c ^ 2 * e * f - 4 * a * c
    * d * e * f + 5 * a * c * d * f ^ 2 - 2 * a * c * e ^ 2 * f - 2 * a * d ^ 2 * e * f - 2 * a
    * d * e ^ 2 * f + 3 * a * d * e * f ^ 2 - 2 * b ^ 2 * c * d * e + 2 * b ^ 2 * c * e * f - 2
    * b * c ^ 2 * e * f - 4 * b * c * d * e * f - 2 * b * c * e ^ 2 * f - 2 * b * d ^ 2 * e * f
    - 2 * b * d * e ^ 2 * f - 2 * c * d * e * f ^ 2

/-- The polynomial `M₁` of `c₂[T₁]` of `C₋` (`z₀, z₁, z₂, z₃, z_a, z_b` = `a, …, f`). -/
def cmM1 : ℝ :=
  cmM1pa (z 0) (z 1) (z 2) (z 3) (cmza z) (cmzb z) +
    cmM1pb (z 0) (z 1) (z 2) (z 3) (cmza z) (cmzb z) +
    cmM1pc (z 0) (z 1) (z 2) (z 3) (cmza z) (cmzb z) +
    cmM1pd (z 0) (z 1) (z 2) (z 3) (cmza z) (cmzb z)

/-- The polynomial `M₂` of `c₂[T₂]` of `C₋`. -/
def cmM2 : ℝ :=
  cmM2pa (z 0) (z 1) (z 2) (z 3) (cmza z) (cmzb z) +
    cmM2pb (z 0) (z 1) (z 2) (z 3) (cmza z) (cmzb z) +
    cmM2pc (z 0) (z 1) (z 2) (z 3) (cmza z) (cmzb z) +
    cmM2pd (z 0) (z 1) (z 2) (z 3) (cmza z) (cmzb z)

theorem symanzikMatrix_Cm :
    symanzikMatrix (classAlpha .Cm) z =
      !![z 0 + z 1 + cmzb z, -(z 0 + cmzb z);
        -(z 0 + cmzb z), z 0 + z 2 + z 3 + cmzb z + cmza z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symanzikMatrix, Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, cmza, cmzb]
  all_goals ring

theorem symanzikU_Cm : symanzikU (classAlpha .Cm) z = cmU z := by
  rw [symanzikU, symanzikMatrix_Cm, Matrix.det_fin_two_of, cmU]
  ring

theorem inv_symanzikMatrix_Cm (s t : Fin 2) :
    (symanzikMatrix (classAlpha .Cm) z)⁻¹ s t =
      (cmU z)⁻¹ * !![z 0 + z 2 + z 3 + cmzb z + cmza z, z 0 + cmzb z;
        z 0 + cmzb z, z 0 + z 1 + cmzb z] s t := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', ← symanzikU, symanzikU_Cm, symanzikMatrix_Cm,
    Matrix.adjugate_fin_two_of, Matrix.smul_apply, smul_eq_mul]
  fin_cases s <;> fin_cases t <;> simp

/-- `S₀ = σ₀ + τ₀`. -/
noncomputable def cmS0 : ℝ := cmSigP z 0 + cmSigQ z 0
/-- `S₁ = σ₁ + τ₁`. -/
noncomputable def cmS1 : ℝ := cmSigP z 1 + cmSigQ z 1
/-- `T₀ = τ₀`. -/
noncomputable def cmT0 : ℝ := cmSigQ z 0
/-- `T₁ = τ₁`. -/
noncomputable def cmT1 : ℝ := cmSigQ z 1

/-- The numerator of `S₀`. -/
def cmS0n : ℝ := z 0*z 1 + 2*z 0*z 2 + 2*z 0*z 3 + z 0*cmza z + z 1*z 2 + z 1*z 3 + z 1*cmza z + z 1*cmzb z + z 2*cmzb z + z 3*cmzb z
/-- The numerator of `S₁`. -/
def cmS1n : ℝ := z 0*z 2 + z 0*z 3 + z 1*z 2 + z 1*z 3 + z 1*cmzb z + z 2*cmzb z + z 3*cmzb z
/-- The numerator of `T₀`. -/
def cmT0n : ℝ := z 0*z 3 + z 3*cmzb z
/-- The numerator of `T₁`. -/
def cmT1n : ℝ := z 0*z 3 + z 1*z 3 + z 3*cmzb z

theorem cmS0_eq : cmS0 z = (cmU z)⁻¹ * cmS0n z := by
  simp only [cmS0, cmSigP, cmSigQ, inv_symanzikMatrix_Cm, cmS0n]
  simp
  ring

theorem cmS1_eq : cmS1 z = (cmU z)⁻¹ * cmS1n z := by
  simp only [cmS1, cmSigP, cmSigQ, inv_symanzikMatrix_Cm, cmS1n]
  simp
  ring

theorem cmT0_eq : cmT0 z = (cmU z)⁻¹ * cmT0n z := by
  simp only [cmT0, cmSigQ, inv_symanzikMatrix_Cm, cmT0n]
  simp
  ring

theorem cmT1_eq : cmT1 z = (cmU z)⁻¹ * cmT1n z := by
  simp only [cmT1, cmSigQ, inv_symanzikMatrix_Cm, cmT1n]
  simp
  ring

end Params

/-! ### The rational identities -/

/-- The homogeneous form of the identity of `c₂[T₁]` (a polynomial identity). -/
theorem cmHom1_identity (z : Fin 8 → ℝ) :
    512 * cmS0n z ^ 2 * cmS1n z ^ 2 - 512 * cmS0n z ^ 2 * cmS1n z * cmU z - 512 * cmS0n z *
    cmS1n z ^ 3 - 512 * cmS0n z * cmS1n z ^ 2 * cmU z + 1024 * cmS0n z * cmS1n z * cmU z ^ 2 +
    512 * cmS1n z ^ 3 * cmU z + 1024 * cmS1n z ^ 2 * cmT0n z * cmU z - 512 * cmS1n z ^ 2 * cmT1n
    z * cmU z - 512 * cmS1n z ^ 2 * cmU z ^ 2 - 2048 * cmS1n z * cmT0n z * cmU z ^ 2 + 1024 *
    cmS1n z * cmT1n z * cmU z ^ 2 =
      512 * cmW z * cmM1 z := by
  simp only [cmS0n, cmS1n, cmT0n, cmT1n, cmU, cmW, cmM1, cmM1pa, cmM1pb, cmM1pc, cmM1pd]
  ring

/-- The rational identity of `c₂[T₁]` of `C₋`. -/
theorem cmPsi1_identity {z : Fin 8 → ℝ} (hU : cmU z ≠ 0) :
      512 * cmS0 z ^ 2 * cmS1 z ^ 2 - 512 * cmS0 z ^ 2 * cmS1 z - 512 * cmS0 z * cmS1 z ^ 3 -
      512 * cmS0 z * cmS1 z ^ 2 + 1024 * cmS0 z * cmS1 z + 512 * cmS1 z ^ 3 + 1024 * cmS1 z ^ 2
      * cmT0 z - 512 * cmS1 z ^ 2 * cmT1 z - 512 * cmS1 z ^ 2 - 2048 * cmS1 z * cmT0 z + 1024 *
      cmS1 z * cmT1 z =
      512 * cmW z * cmM1 z / cmU z ^ 4 := by
  rw [cmS0_eq, cmS1_eq, cmT0_eq, cmT1_eq, div_eq_mul_inv, ← inv_pow]
  have hpoly := cmHom1_identity z
  generalize hu' : (cmU z)⁻¹ = u
  have hu : cmU z * u = 1 := by rw [← hu']; exact mul_inv_cancel₀ hU
  linear_combination (-(
      -512 * cmS0n z ^ 2 * cmS1n z * u ^ 3 - 512 * cmS0n z * cmS1n z ^ 2 * u ^ 3 + 1024 * cmS0n
      z * cmS1n z * cmU z * u ^ 3 + 1024 * cmS0n z * cmS1n z * u ^ 2 + 512 * cmS1n z ^ 3 * u ^ 3
      + 1024 * cmS1n z ^ 2 * cmT0n z * u ^ 3 - 512 * cmS1n z ^ 2 * cmT1n z * u ^ 3 - 512 * cmS1n
      z ^ 2 * cmU z * u ^ 3 - 512 * cmS1n z ^ 2 * u ^ 2 - 2048 * cmS1n z * cmT0n z * cmU z * u ^
      3 - 2048 * cmS1n z * cmT0n z * u ^ 2 + 1024 * cmS1n z * cmT1n z * cmU z * u ^ 3 + 1024 *
      cmS1n z * cmT1n z * u ^ 2)) * hu + u ^ 4 * hpoly

/-- The homogeneous form of the identity of `c₂[T₂]` (a polynomial identity). -/
theorem cmHom2_identity (z : Fin 8 → ℝ) :
    1024 * cmS0n z ^ 2 * (z 0 + z 1 + cmzb z) - 1024 * cmS0n z * cmS1n z * (z 0 + z 1 + cmzb z)
    - 2048 * cmS0n z * cmS1n z * (-z 1) - 2048 * cmS0n z * cmS1n z * (-z 1) - 1024 * cmS0n z *
    cmT1n z * (z 0 + cmzb z) + 1024 * cmS0n z * cmT1n z * (z 0 + cmzb z) - 2048 * cmS0n z * cmU
    z * (z 0 + cmzb z) + 2048 * cmS0n z * cmU z * (-z 1) + 2048 * cmS0n z * cmU z * (-z 1) -
    1024 * cmS1n z ^ 2 * (z 2 + z 3 + cmza z) + 1024 * cmS1n z * cmT0n z * (z 0 + cmzb z) - 1024
    * cmS1n z * cmT0n z * (z 0 + cmzb z) + 2048 * cmS1n z * cmU z * (z 0 + cmzb z) + 2048 *
    cmS1n z * cmU z * (-z 1) - 1024 * cmS1n z * cmU z * (z 0 + cmzb z) + 1024 * cmS1n z * cmU z
    * (-z 1) + 1024 * cmS1n z * cmU z * (z 2 + z 3 + cmza z) - 2048 * cmT0n z * cmU z * (z 0 + z
    1 + cmzb z) + 1024 * cmT0n z * cmU z * (z 0 + cmzb z) + 1024 * cmT0n z * cmU z * (-z 1) -
    2048 * cmT0n z * cmU z * (-z 1) + 1024 * cmT1n z * cmU z * (z 0 + z 1 + cmzb z) - 2048 *
    cmT1n z * cmU z * (z 0 + cmzb z) - 2048 * cmT1n z * cmU z * (-z 1) - 1024 * cmT1n z * cmU z
    * (z 0 + cmzb z) - 1024 * cmU z ^ 2 * (z 0 + z 1 + cmzb z) + 2048 * cmU z ^ 2 * (z 0 + cmzb
    z) - 2048 * cmU z ^ 2 * (-z 1) + 1024 * cmU z ^ 2 * (z 0 + cmzb z) - 1024 * cmU z ^ 2 * (-z
    1) =
      -1024 * cmM2 z := by
  simp only [cmS0n, cmS1n, cmT0n, cmT1n, cmU, cmM2, cmM2pa, cmM2pb, cmM2pc, cmM2pd]
  ring

/-- The rational identity of `c₂[T₂]` of `C₋`. -/
theorem cmPsi2_identity {z : Fin 8 → ℝ} (hU : cmU z ≠ 0) :
      1024 * cmS0 z ^ 2 * ((z 0 + z 1 + cmzb z) / cmU z) - 1024 * cmS0 z * cmS1 z * ((z 0 + z 1
      + cmzb z) / cmU z) - 2048 * cmS0 z * cmS1 z * ((-z 1) / cmU z) - 2048 * cmS0 z * cmS1 z *
      ((-z 1) / cmU z) - 1024 * cmS0 z * cmT1 z * ((z 0 + cmzb z) / cmU z) + 1024 * cmS0 z *
      cmT1 z * ((z 0 + cmzb z) / cmU z) - 2048 * cmS0 z * ((z 0 + cmzb z) / cmU z) + 2048 * cmS0
      z * ((-z 1) / cmU z) + 2048 * cmS0 z * ((-z 1) / cmU z) - 1024 * cmS1 z ^ 2 * ((z 2 + z 3
      + cmza z) / cmU z) + 1024 * cmS1 z * cmT0 z * ((z 0 + cmzb z) / cmU z) - 1024 * cmS1 z *
      cmT0 z * ((z 0 + cmzb z) / cmU z) + 2048 * cmS1 z * ((z 0 + cmzb z) / cmU z) + 2048 * cmS1
      z * ((-z 1) / cmU z) - 1024 * cmS1 z * ((z 0 + cmzb z) / cmU z) + 1024 * cmS1 z * ((-z 1)
      / cmU z) + 1024 * cmS1 z * ((z 2 + z 3 + cmza z) / cmU z) - 2048 * cmT0 z * ((z 0 + z 1 +
      cmzb z) / cmU z) + 1024 * cmT0 z * ((z 0 + cmzb z) / cmU z) + 1024 * cmT0 z * ((-z 1) /
      cmU z) - 2048 * cmT0 z * ((-z 1) / cmU z) + 1024 * cmT1 z * ((z 0 + z 1 + cmzb z) / cmU z)
      - 2048 * cmT1 z * ((z 0 + cmzb z) / cmU z) - 2048 * cmT1 z * ((-z 1) / cmU z) - 1024 *
      cmT1 z * ((z 0 + cmzb z) / cmU z) - 1024 * ((z 0 + z 1 + cmzb z) / cmU z) + 2048 * ((z 0 +
      cmzb z) / cmU z) - 2048 * ((-z 1) / cmU z) + 1024 * ((z 0 + cmzb z) / cmU z) - 1024 * ((-z
      1) / cmU z) =
      -1024 * cmM2 z / cmU z ^ 3 := by
  rw [cmS0_eq, cmS1_eq, cmT0_eq, cmT1_eq]
  simp only [div_eq_mul_inv, ← inv_pow]
  have hpoly := cmHom2_identity z
  generalize hu' : (cmU z)⁻¹ = u
  have hu : cmU z * u = 1 := by rw [← hu']; exact mul_inv_cancel₀ hU
  linear_combination (-(
      -2048 * cmS0n z * (z 0 + cmzb z) * u ^ 2 + 2048 * cmS0n z * (-z 1) * u ^ 2 + 2048 * cmS0n
      z * (-z 1) * u ^ 2 + 2048 * cmS1n z * (z 0 + cmzb z) * u ^ 2 + 2048 * cmS1n z * (-z 1) * u
      ^ 2 - 1024 * cmS1n z * (z 0 + cmzb z) * u ^ 2 + 1024 * cmS1n z * (-z 1) * u ^ 2 + 1024 *
      cmS1n z * (z 2 + z 3 + cmza z) * u ^ 2 - 2048 * cmT0n z * (z 0 + z 1 + cmzb z) * u ^ 2 +
      1024 * cmT0n z * (z 0 + cmzb z) * u ^ 2 + 1024 * cmT0n z * (-z 1) * u ^ 2 - 2048 * cmT0n z
      * (-z 1) * u ^ 2 + 1024 * cmT1n z * (z 0 + z 1 + cmzb z) * u ^ 2 - 2048 * cmT1n z * (z 0 +
      cmzb z) * u ^ 2 - 2048 * cmT1n z * (-z 1) * u ^ 2 - 1024 * cmT1n z * (z 0 + cmzb z) * u ^
      2 - 1024 * cmU z * (z 0 + z 1 + cmzb z) * u ^ 2 + 2048 * cmU z * (z 0 + cmzb z) * u ^ 2 -
      2048 * cmU z * (-z 1) * u ^ 2 + 1024 * cmU z * (z 0 + cmzb z) * u ^ 2 - 1024 * cmU z * (-z
      1) * u ^ 2 - 1024 * (z 0 + z 1 + cmzb z) * u + 2048 * (z 0 + cmzb z) * u - 2048 * (-z 1) *
      u + 1024 * (z 0 + cmzb z) * u - 1024 * (-z 1) * u)) * hu + u ^ 3 * hpoly

/-! ### The second-order coefficients -/

/-- The jet of the slot numerator `k` of `C₋`. -/
noncomputable def cmSlotJ (z : Fin 8 → ℝ) (k : Fin 4) : PJ :=
  eJ ((cmSlotA z k : ℂ) + (cmSlotB z k : ℂ)) (cmSlotB z k : ℂ)

theorem ppJ_cmSlot_T1 (z : Fin 8 → ℝ) :
    -ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (cmSlotJ z 3)).mul (PJ.c g0L)).mul (pjRev (cmSlotJ z 2))).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c g1)).mul (pjRev (cmSlotJ z 2))).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c 1)).mul (pjRev (cmSlotJ z 2)).bar).gamT (pjRev (cmSlotJ z 1)) (pjRev (cmSlotJ z 0)) =
      ((
      512 * cmS0 z ^ 2 * cmS1 z ^ 2 - 512 * cmS0 z ^ 2 * cmS1 z - 512 * cmS0 z * cmS1 z ^ 3 -
      512 * cmS0 z * cmS1 z ^ 2 + 1024 * cmS0 z * cmS1 z + 512 * cmS1 z ^ 3 + 1024 * cmS1 z ^ 2
      * cmT0 z - 512 * cmS1 z ^ 2 * cmT1 z - 512 * cmS1 z ^ 2 - 2048 * cmS1 z * cmT0 z + 1024 *
      cmS1 z * cmT1 z : ℝ) : ℂ) := by
  simp only [cmSlotJ, ppJ_Cm_T1, cmSlotA, cmSlotB, cmS0, cmS1, cmT0, cmT1, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  ring

theorem jets_Cm {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasPJ (fun u => revPl (lQ0 P u)) (pjRev qJ0) ∧ HasPJ (fun u => revPl (lQ1 P u)) (pjRev qJ1) ∧
      HasPJ (fun u => revR (lR P u)) (pjRevR rJ) ∧
      ∀ k, HasPJ (fun u => revPl (cmE P z u k)) (pjRev (cmSlotJ z k)) :=
  ⟨hasPJ_rev (x := qJ0) (jet_lQ0 hm), hasPJ_rev (x := qJ1) (jet_lQ1 hm),
    hasPJ_revR (x := rJ) (jet_lR hm), fun k => hasPJ_rev (jet_cmE hm z k)⟩

/-- **The jet of `T₁` of `C₋`**. -/
theorem hasJet2_cmT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : cmU z ≠ 0) :
    HasJet2 (classT1 .Cm permCm P z) 0 0 (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
      ((cmW z * cmM1 z / (2 * cmU z ^ 6) : ℝ) : ℂ)) := by
  obtain ⟨hq0, hq1, hr, hE⟩ := jets_Cm hm z
  have h := hasJet2_ppPl hq0 hq1 hr
    (((hE 3).mul (HasPJ.const g0L)).mul (hE 2)).gam (((hE 3).mul (HasPJ.const g1)).mul (hE 2)).gam
    (((hE 3).mul (HasPJ.const 1)).mul (hE 2).bar).gamT (hE 1) (hE 0)
  have h' := (h.neg.const_mul 6).const_mul
    (ladderK P * ((symanzikU (classAlpha .Cm) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h'.congr fun u => classT1_Cm_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp [cmSlotJ]
  · simp [cmSlotJ]
  rw [ppJ_cmSlot_T1, cmPsi1_identity hU, ladderK_eq he, symanzikU_Cm, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (cmU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₁` of `C₋`**. -/
theorem secondCoeff_cmT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : cmU z ≠ 0) :
    secondCoeff (classT1 .Cm permCm P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
      ((cmW z * cmM1 z / (2 * cmU z ^ 6) : ℝ) : ℂ) :=
  (hasJet2_cmT1 hm he hU).secondCoeff_eq

theorem classC_Cm_val (z : Fin 8 → ℝ) :
    classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 1 = (((z 0 + z 1 + cmzb z) / cmU z : ℝ) : ℂ) ∧
    classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 2 = (((z 0 + cmzb z) / cmU z : ℝ) : ℂ) ∧
    classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 3 = (((-z 1) / cmU z : ℝ) : ℂ) ∧
    classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 2 = (((z 0 + cmzb z) / cmU z : ℝ) : ℂ) ∧
    classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 3 = (((-z 1) / cmU z : ℝ) : ℂ) ∧
    classC .Cm (symanzikMatrix (classAlpha .Cm) z) 2 3 = (((z 2 + z 3 + cmza z) / cmU z : ℝ) : ℂ) := by
  simp only [classC, contrC, Fin.sum_univ_two, inv_symanzikMatrix_Cm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix, ladderLines]
  all_goals ring

theorem cmT2_combination (z : Fin 8 → ℝ) :
    classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 1 *
        -(2 * ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (cmSlotJ z 3)).mul (PJ.c g0L)).mul (pjRev (cmSlotJ z 2))).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c g1)).mul (pjRev (cmSlotJ z 2))).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c 1)).mul (pjRev (cmSlotJ z 2)).bar).gamT (PJ.c 1) (PJ.c 1)) +
      classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 2 *
        -(ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (cmSlotJ z 3)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (pjRev (cmSlotJ z 1)).gam (PJ.c 1) +
          2 * ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (cmSlotJ z 3)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (pjRev (cmSlotJ z 1)) +
          2 * ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (cmSlotJ z 3)).mul (PJ.c g0L)).mul (pjRev (cmSlotJ z 1))).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c g1)).mul (pjRev (cmSlotJ z 1))).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c 1)).mul (pjRev (cmSlotJ z 1)).bar).gamT (PJ.c 1) (PJ.c 1) +
          4 * pwJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (PJ.c 1) ((pjRev (cmSlotJ z 3)).mul (pjRev (cmSlotJ z 1)).gam)) +
      classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 3 *
        -(ppJ (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT (((PJ.c 1).mul (PJ.c g0L)).mul (pjRev (cmSlotJ z 2))).gam (((PJ.c 1).mul (PJ.c g1)).mul (pjRev (cmSlotJ z 2))).gam (((PJ.c 1).mul (PJ.c 1)).mul (pjRev (cmSlotJ z 2)).bar).gamT (pjRev (cmSlotJ z 1)) (PJ.c 1) +
          4 * pwJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((pjRev (cmSlotJ z 2)).gam.mul (pjRev (cmSlotJ z 1))) (PJ.c 1) +
          2 * pwJ (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT ((pjRev (cmSlotJ z 2)).mul (pjRev (cmSlotJ z 1)).gam) (PJ.c 1) +
          4 * pwJ (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT (pjRev (cmSlotJ z 2)) (pjRev (cmSlotJ z 1))) +
      classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 2 *
        -(2 * ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (cmSlotJ z 3)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (cmSlotJ z 3)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (pjRev (cmSlotJ z 0))) +
      classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 3 *
        -(-ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((PJ.c g0L).mul (pjRev (cmSlotJ z 2))).gam.gam ((PJ.c g1).mul (pjRev (cmSlotJ z 2))).gam.gam ((PJ.c 1).mul (pjRev (cmSlotJ z 2)).bar).gamT.gamT (PJ.c 1) (pjRev (cmSlotJ z 0)) +
          8 * ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((PJ.c g0L).mul (pjRev (cmSlotJ z 2))) ((PJ.c g1).mul (pjRev (cmSlotJ z 2))) ((PJ.c 1).mul (pjRev (cmSlotJ z 2)).bar) (PJ.c 1) (pjRev (cmSlotJ z 0))) +
      classC .Cm (symanzikMatrix (classAlpha .Cm) z) 2 3 *
        -(4 * ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (PJ.c g0L) (PJ.c g1) (PJ.c 1) (pjRev (cmSlotJ z 1)) (pjRev (cmSlotJ z 0))) =
    ((
      1024 * cmS0 z ^ 2 * ((z 0 + z 1 + cmzb z) / cmU z) - 1024 * cmS0 z * cmS1 z * ((z 0 + z 1
      + cmzb z) / cmU z) - 2048 * cmS0 z * cmS1 z * ((-z 1) / cmU z) - 2048 * cmS0 z * cmS1 z *
      ((-z 1) / cmU z) - 1024 * cmS0 z * cmT1 z * ((z 0 + cmzb z) / cmU z) + 1024 * cmS0 z *
      cmT1 z * ((z 0 + cmzb z) / cmU z) - 2048 * cmS0 z * ((z 0 + cmzb z) / cmU z) + 2048 * cmS0
      z * ((-z 1) / cmU z) + 2048 * cmS0 z * ((-z 1) / cmU z) - 1024 * cmS1 z ^ 2 * ((z 2 + z 3
      + cmza z) / cmU z) + 1024 * cmS1 z * cmT0 z * ((z 0 + cmzb z) / cmU z) - 1024 * cmS1 z *
      cmT0 z * ((z 0 + cmzb z) / cmU z) + 2048 * cmS1 z * ((z 0 + cmzb z) / cmU z) + 2048 * cmS1
      z * ((-z 1) / cmU z) - 1024 * cmS1 z * ((z 0 + cmzb z) / cmU z) + 1024 * cmS1 z * ((-z 1)
      / cmU z) + 1024 * cmS1 z * ((z 2 + z 3 + cmza z) / cmU z) - 2048 * cmT0 z * ((z 0 + z 1 +
      cmzb z) / cmU z) + 1024 * cmT0 z * ((z 0 + cmzb z) / cmU z) + 1024 * cmT0 z * ((-z 1) /
      cmU z) - 2048 * cmT0 z * ((-z 1) / cmU z) + 1024 * cmT1 z * ((z 0 + z 1 + cmzb z) / cmU z)
      - 2048 * cmT1 z * ((z 0 + cmzb z) / cmU z) - 2048 * cmT1 z * ((-z 1) / cmU z) - 1024 *
      cmT1 z * ((z 0 + cmzb z) / cmU z) - 1024 * ((z 0 + z 1 + cmzb z) / cmU z) + 2048 * ((z 0 +
      cmzb z) / cmU z) - 2048 * ((-z 1) / cmU z) + 1024 * ((z 0 + cmzb z) / cmU z) - 1024 * ((-z
      1) / cmU z) : ℝ) : ℂ) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := classC_Cm_val z
  rw [h01, h02, h03, h12, h13, h23]
  simp only [cmSlotJ, ppJ_Cm_01, ppJ_Cm_02a, ppJ_Cm_02b, pwJ_Cm_02d, ppJ_Cm_03a,
    pwJ_Cm_03b, pwJ_Cm_03c, pwJ_Cm_03d, ppJ_Cm_13a, ppJ_Cm_13b, ppJ_Cm_23, cmSlotA,
    cmSlotB, cmS0, cmS1, cmT0, cmT1, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring
/-- **The jet of `T₂` of `C₋`**. -/
theorem hasJet2_cmT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : cmU z ≠ 0) :
    HasJet2 (classT2 .Cm permCm P z) 0 0 (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
      ((-cmM2 z / (2 * cmU z ^ 5) : ℝ) : ℂ)) := by
  obtain ⟨hq0, hq1, hr, hE⟩ := jets_Cm hm z
  have c1 := HasPJ.const (1 : Pl)
  have cL := HasPJ.const g0L
  have c1' := HasPJ.const g1
  have h01 := hasJet2_ppPl hq0 hq1 hr (((hE 3).mul cL).mul (hE 2)).gam
    (((hE 3).mul c1').mul (hE 2)).gam (((hE 3).mul c1).mul (hE 2).bar).gamT c1 c1
  have hH0 := (((hE 3).mul cL).mul c1).gam
  have hH1 := (((hE 3).mul c1').mul c1).gam
  have hHB := (((hE 3).mul c1).mul c1.bar).gamT
  have h02a := hasJet2_ppPl hq0 hq1 hr hH0 hH1 hHB (hE 1).gam c1
  have h02b := hasJet2_ppPl hq0 hq1 hr hH0 hH1 hHB c1 (hE 1)
  have h02c := hasJet2_ppPl hq0 hq1 hr (((hE 3).mul cL).mul (hE 1)).gam
    (((hE 3).mul c1').mul (hE 1)).gam (((hE 3).mul c1).mul (hE 1).bar).gamT c1 c1
  have h02d := hasJet2_pwPl hq0 hq1 hr c1 ((hE 3).mul (hE 1).gam)
  have h03a := hasJet2_ppPl hq0.gam hq1.gam hr.gamT ((c1.mul cL).mul (hE 2)).gam
    ((c1.mul c1').mul (hE 2)).gam ((c1.mul c1).mul (hE 2).bar).gamT (hE 1) c1
  have h03b := hasJet2_pwPl hq0 hq1 hr ((hE 2).gam.mul (hE 1)) c1
  have h03c := hasJet2_pwPl hq0.gam hq1.gam hr.gamT ((hE 2).mul (hE 1).gam) c1
  have h03d := hasJet2_pwPl hq0.gam hq1.gam hr.gamT (hE 2) (hE 1)
  have h12 := hasJet2_ppPl hq0 hq1 hr hH0 hH1 hHB c1 (hE 0)
  have h13a := hasJet2_ppPl hq0 hq1 hr (cL.mul (hE 2)).gam.gam (c1'.mul (hE 2)).gam.gam
    (c1.mul (hE 2).bar).gamT.gamT c1 (hE 0)
  have h13b := hasJet2_ppPl hq0 hq1 hr (cL.mul (hE 2)) (c1'.mul (hE 2)) (c1.mul (hE 2).bar) c1
    (hE 0)
  have h23 := hasJet2_ppPl hq0 hq1 hr cL c1' c1 (hE 1) (hE 0)
  have g1 := (h01.const_mul 2).neg.const_mul
    (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 1)
  have g2 := (((h02a.add (h02b.const_mul 2)).add (h02c.const_mul 2)).add
    (h02d.const_mul 4)).neg.const_mul (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 2)
  have g3 := (((h03a.add (h03b.const_mul 4)).add (h03c.const_mul 2)).add
    (h03d.const_mul 4)).neg.const_mul (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 3)
  have g4 := (h12.const_mul 2).neg.const_mul
    (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 2)
  have g5 := (h13a.neg.add (h13b.const_mul 8)).neg.const_mul
    (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 3)
  have g6 := (h23.const_mul 4).neg.const_mul
    (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 2 3)
  have h := (((((g1.add g2).add g3).add g4).add g5).add g6).const_mul
    (ladderK P * ((symanzikU (classAlpha .Cm) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => classT2_Cm_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp [cmSlotJ]
  · simp [cmSlotJ]
  have hc := cmT2_combination z
  rw [hc, cmPsi2_identity hU, ladderK_eq he, symanzikU_Cm, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (cmU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₂` of `C₋`**. -/
theorem secondCoeff_cmT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : cmU z ≠ 0) :
    secondCoeff (classT2 .Cm permCm P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
      ((-cmM2 z / (2 * cmU z ^ 5) : ℝ) : ℂ) :=
  (hasJet2_cmT2 hm he hU).secondCoeff_eq

/-- **The jet of `T₃` of `C₋` vanishes**. -/
theorem hasJet2_cmT3 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasJet2 (classT3 .Cm permCm P z) 0 0 0 := by
  obtain ⟨hq0, hq1, hr, -⟩ := jets_Cm hm z
  have h₁ := hasJet2_pwPl hq0 hq1 hr (HasPJ.const 1) (HasPJ.const 1)
  have h := (((((h₁.const_mul 16).neg.const_mul
      (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 1 *
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 2 3)).add
    ((h₁.const_mul 32).const_mul (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 2 *
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 3))).add
    ((h₁.const_mul 32).const_mul (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 3 *
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 2))).const_mul (1 / 4)).const_mul
    (ladderK P * ((symanzikU (classAlpha .Cm) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => classT3_Cm_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp
  · simp
  · simp [pwJ_Cm_T3]

/-- **The second-order coefficient of `T₃` of `C₋` vanishes.** -/
theorem secondCoeff_cmT3 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    secondCoeff (classT3 .Cm permCm P z) = 0 :=
  (hasJet2_cmT3 hm z).secondCoeff_eq

/-! ### The second-order coefficient of the projected numerator -/

@[fun_prop] theorem continuous_pvMomentaE_Cm (r : Fin 4 → ℝ) (i : Fin 8) (μ : Fin 4) :
    Continuous fun p' : Fin 4 → ℝ => pvMomentaE .Cm r p' i μ := by
  fin_cases i <;>
    simp [pvMomentaE, extMomenta, QED.Integration.TwoLoop.classCmSmMomenta,
      QED.Integration.TwoLoop.pvLines] <;> fun_prop

theorem continuous_cmV (r : Fin 4 → ℝ) (M z : Fin 8 → ℝ) :
    Continuous fun p' : Fin 4 → ℝ => symanzikV (classAlpha .Cm) (pvMomentaE .Cm r p') M z := by
  unfold symanzikV symanzikVector QED.Minkowski.dot
  fun_prop

/-- The second Symanzik function of `C₋` along the curve tends to its value at `q = 0`. -/
theorem tendsto_cmV (P : Params) (x : Fin 7 → ℝ) :
    Tendsto (fun u => ((symanzikV (classAlpha .Cm) (classMom .Cm P u) (pvMasses P)
        (simplexPoint x) : ℝ) : ℂ))
      (𝓝 0) (𝓝 ((openV .Cm P x : ℝ) : ℂ)) := by
  have h := ((continuous_cmV (restMomentum P.m) (pvMasses P) (simplexPoint x)).tendsto
    (restMomentum P.m)).comp (tendsto_curveMomentum P.m)
  exact (Complex.continuous_ofReal.tendsto _).comp h

theorem Cm_mem_openClasses : Class5.Cm ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide

/-- **The jet of the projected `C₋` numerator**: `N(x, u) = c₂ u² + o(u²)` with
`c₂ = c₂[T₁] + c₂[T₂] V(x)`. -/
theorem hasJet2_openNum_Cm {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : cmU (simplexPoint x) ≠ 0) :
    HasJet2 (openNum .Cm P x) 0 0
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((cmW (simplexPoint x) * cmM1 (simplexPoint x) / (2 * cmU (simplexPoint x) ^ 6) : ℝ) :
            ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((-cmM2 (simplexPoint x) / (2 * cmU (simplexPoint x) ^ 5) : ℝ) : ℂ) *
            ((openV .Cm P x : ℝ) : ℂ)) := by
  have hV := tendsto_cmV P x
  have h := ((hasJet2_cmT1 hm he hU).add (hasJet2_mul_tendsto (hasJet2_cmT2 hm he hU) hV)).add
    (hasJet2_mul_tendsto (hasJet2_cmT3 hm (simplexPoint x)) (hV.pow 2))
  exact h.of_eq (fun u => openNum_eq_T_of_chain isChainForm_Cm classMomE_Cm_eq Cm_mem_openClasses
    P x u) (by ring) (by ring) (by ring)

/-- **The second-order coefficient of the projected `C₋` numerator.** -/
theorem secondCoeff_openNum_Cm {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : cmU (simplexPoint x) ≠ 0) :
    secondCoeff (openNum .Cm P x) =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((cmW (simplexPoint x) * cmM1 (simplexPoint x) / (2 * cmU (simplexPoint x) ^ 6) : ℝ) :
            ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((-cmM2 (simplexPoint x) / (2 * cmU (simplexPoint x) ^ 5) : ℝ) : ℂ) *
            ((openV .Cm P x : ℝ) : ℂ) :=
  (hasJet2_openNum_Cm hm he x hU).secondCoeff_eq

/-- Almost every point of the simplex has `U ≠ 0` (for `C₋`). -/
theorem ae_cmU_ne_zero : ∀ᵐ x ∂(MeasureTheory.volume.restrict
    (QED.Integration.Feynman.simplexSet 7)),
    cmU (simplexPoint x) ≠ 0 := by
  have hspan : ∃ i j, classAlpha .Cm i 0 * classAlpha .Cm j 1 -
      classAlpha .Cm i 1 * classAlpha .Cm j 0 ≠ 0 :=
    ⟨1, 2, by simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix]⟩
  filter_upwards [QED.Integration.TwoLoop.ae_posDef (classAlpha .Cm) (by norm_num) hspan] with x hx
  rw [← symanzikU_Cm]
  exact hx.2.det_pos.ne'

/-- **The `C₋` class value with the explicit integrand**: at `m = 1`, `e = 1`,
`openZero .Cm P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴` with
`c₂[T₁] = (Λ² - m_γ²)² (6/K) W M₁/(2U⁶)` and `c₂[T₂] = (Λ² - m_γ²)² (2/K) (-M₂/(2U⁵))`. -/
theorem openZero_Cm_eq {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .Cm P = ∫ x in QED.Integration.Feynman.simplexSet 7,
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((cmW (simplexPoint x) * cmM1 (simplexPoint x) / (2 * cmU (simplexPoint x) ^ 6) : ℝ) :
            ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((-cmM2 (simplexPoint x) / (2 * cmU (simplexPoint x) ^ 5) : ℝ) : ℂ) *
            ((openV .Cm P x : ℝ) : ℂ)) /
        ((openV .Cm P x : ℝ) : ℂ) ^ 4 := by
  unfold openZero
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_cmU_ne_zero] with x hx
  rw [secondCoeff_openNum_Cm hm he x hx]

end QED.TwoLoop.UnitSCGraph

end
