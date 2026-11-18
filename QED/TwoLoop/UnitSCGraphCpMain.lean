/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphCpData
public import QED.TwoLoop.UnitSCGraphSpMain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The pointwise second-order coefficients of the `C₊` numerator

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half, the analogue of
`QED/TwoLoop/UnitSCGraphSpMain.lean` for the corner class `C₊`. With the projected numerator
`N = T₁ + T₂ V + T₃ V²` (`QED.TwoLoop.UnitSCGraph.openNum_eq_T_of_chain`) and, at a point `z` of
the eight line parameters, the outer electron pair `z_o = z₀ + z₁` (split `t = z₁`), the inner
electrons `y₃ = z₂`, `y₄ = z₃` (the lines of the vertex subgraph), `z_a = z₄ + z₆`,
`z_b = z₅ + z₇` (the outer and inner photon, each a Pauli–Villars pair),
`U = (z_o + y₃ + z_a)(z_o + y₄ + z_a + z_b) - (z_o + z_a)²` (`cpU`) and
`W = (y₃ + y₄ + z_b) z_o + y₃ z_b` (`cpW`), at `m = 1`, `e = 1`:

* `secondCoeff_cpT1`: `c₂[T₁] = (Λ² - m_γ²)² (6/K) · W M₁/(2U⁶)`;
* `secondCoeff_cpT2`: `c₂[T₂] = (Λ² - m_γ²)² (2/K) · (-M₂/(2U⁵))`;
* `secondCoeff_cpT3`: `c₂[T₃] = 0`,

with `K = 16π⁴/(64 i)` and the explicit polynomials `M₁` (`cpM1`, of degree 6) and `M₂` (`cpM2`,
of degree 5) in `z₀, t, y₃, y₄, z_a, z_b`, affine in the split `t` (for fixed `z_o`), for every
`z` with `U ≠ 0`. Hence (`openZero_Cp_eq`) `openZero .Cp P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴`.

The polynomials were obtained in exact arithmetic and checked against exact Dirac traces of
the class (`scripts/numerics/sc_graph/symbolic_c2.py`, `cp_planar.py`,
`c_identities.py`); after merging the split and the Pauli–Villars pairs they reproduce the
engine integrand of `scripts/numerics/two_loop_units.py`, graph `C+` (`engine_check.py`).
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

/-- The first Symanzik function of `C₊`. -/
def cpU : ℝ :=
  (z 0 + z 1 + z 2 + spza z) * (z 0 + z 1 + z 3 + spza z + spzb z) - (z 0 + z 1 + spza z) ^ 2

/-- `W = (y₃ + y₄ + z_b) z_o + y₃ z_b`. -/
def cpW : ℝ := (z 2 + z 3 + spzb z) * (z 0 + z 1) + z 2 * spzb z

/-- Part 1 of `cpM1p`. -/
def cpM1pa (a b c d e f : ℝ) : ℝ :=
  b ^ 2 * c ^ 3 * d + b ^ 2 * c ^ 3 * a + b ^ 2 * c ^ 3 * e + b ^ 2 * c * d ^ 3 - b ^ 2 * d ^ 3
    * a + b ^ 2 * d ^ 3 * e - b ^ 2 * a * f ^ 3 + b ^ 2 * e * f ^ 3 + 2 * b * c ^ 3 * d ^ 2 + 2
    * b * c ^ 3 * a ^ 2 + 2 * b * c ^ 3 * e ^ 2 + 2 * b * c ^ 2 * d ^ 3 - 2 * b * d ^ 3 * a ^ 2
    + 2 * b * d ^ 3 * e ^ 2 - 2 * b * a ^ 2 * f ^ 3 + b * e ^ 2 * f ^ 3 + c ^ 3 * d ^ 3 + c ^ 3
    * d * f ^ 2 + c ^ 3 * a ^ 3 + c ^ 3 * a * f ^ 2 + c ^ 3 * e ^ 3 + c ^ 3 * e * f ^ 2 + c ^ 2
    * d * a ^ 3 + c ^ 2 * a ^ 3 * f - c ^ 2 * a * f ^ 3 + c ^ 2 * e * f ^ 3 - 2 * c * d ^ 3 * a
    ^ 2 - c * d ^ 2 * a ^ 3 - c * a ^ 3 * f ^ 2 - 2 * c * a ^ 2 * f ^ 3 + c * e ^ 2 * f ^ 3 - d
    ^ 3 * a ^ 3 - 2 * d ^ 3 * a ^ 2 * e + d ^ 3 * e ^ 3 - 3 * d ^ 2 * a ^ 3 * f - 3 * d * a ^ 3
    * f ^ 2 - a ^ 3 * f ^ 3 - 2 * a ^ 2 * e * f ^ 3 - a * e ^ 2 * f ^ 3

/-- Part 2 of `cpM1p`. -/
def cpM1pb (a b c d e f : ℝ) : ℝ :=
  3 * b ^ 2 * c ^ 2 * d ^ 2 + b ^ 2 * c ^ 2 * d * a + b ^ 2 * c ^ 2 * a * f - b ^ 2 * c * d ^ 2
    * a + b ^ 2 * c * d * f ^ 2 - b ^ 2 * c * a * f ^ 2 - 3 * b ^ 2 * d * a * f ^ 2 - b * c * d
    ^ 3 * a - b * d ^ 3 * a * e - 6 * b * d ^ 2 * a ^ 2 * f - 6 * b * d * a ^ 2 * f ^ 2 - b * a
    * e * f ^ 3 + 4 * c ^ 3 * d ^ 2 * a + 3 * c ^ 3 * d ^ 2 * e + 2 * c ^ 3 * d ^ 2 * f + 4 * c
    ^ 3 * d * a ^ 2 + 3 * c ^ 3 * d * e ^ 2 + 4 * c ^ 3 * a ^ 2 * e + 2 * c ^ 3 * a ^ 2 * f + 4
    * c ^ 3 * a * e ^ 2 + 2 * c ^ 3 * e ^ 2 * f + 3 * c ^ 2 * d ^ 3 * e + 3 * c ^ 2 * d ^ 2 * a
    ^ 2 + 6 * c ^ 2 * d ^ 2 * e ^ 2 + 3 * c ^ 2 * d * e ^ 3 + 3 * c ^ 2 * e ^ 3 * f + 3 * c ^ 2
    * e ^ 2 * f ^ 2 + 3 * c * d ^ 3 * e ^ 2 + c * d ^ 2 * a ^ 2 * e - 5 * c * d ^ 2 * a ^ 2 * f
    + 3 * c * d ^ 2 * e ^ 3 - 6 * c * d * a ^ 2 * f ^ 2 - c * a * e * f ^ 3 + 2 * c * e ^ 3 * f
    ^ 2 - 5 * d ^ 2 * a ^ 2 * e * f + d ^ 2 * a * e ^ 2 * f + 3 * d ^ 2 * e ^ 3 * f - 5 * d * a
    ^ 2 * e * f ^ 2 + 2 * d * e ^ 3 * f ^ 2

/-- Part 3 of `cpM1p`. -/
def cpM1pc (a b c d e f : ℝ) : ℝ :=
  4 * b ^ 2 * c ^ 2 * d * e + 2 * b ^ 2 * c ^ 2 * d * f + 3 * b ^ 2 * c ^ 2 * e * f + 4 * b ^ 2
    * c * d ^ 2 * e + 3 * b ^ 2 * c * d ^ 2 * f + 3 * b ^ 2 * c * e * f ^ 2 - 3 * b ^ 2 * d ^ 2
    * a * f + 4 * b ^ 2 * d ^ 2 * e * f + 4 * b ^ 2 * d * e * f ^ 2 + 5 * b * c ^ 3 * d * a + 4
    * b * c ^ 3 * d * e + 2 * b * c ^ 3 * d * f + 5 * b * c ^ 3 * a * e + 2 * b * c ^ 3 * a * f
    + 2 * b * c ^ 3 * e * f + 5 * b * c ^ 2 * d ^ 2 * f + 2 * b * c ^ 2 * d * a ^ 2 + 2 * b * c
    ^ 2 * d * f ^ 2 + 2 * b * c ^ 2 * a ^ 2 * f + 5 * b * c ^ 2 * e ^ 2 * f + 4 * b * c ^ 2 * e
    * f ^ 2 + 4 * b * c * d ^ 3 * e - 2 * b * c * d ^ 2 * a ^ 2 + 6 * b * c * d ^ 2 * e ^ 2 - 2
    * b * c * a ^ 2 * f ^ 2 - 2 * b * c * a * f ^ 3 + 4 * b * c * e ^ 2 * f ^ 2 + 2 * b * c * e
    * f ^ 3 + 5 * c ^ 3 * d * a * f + 4 * c ^ 3 * d * e * f + 5 * c ^ 3 * a * e * f + 2 * c ^ 2
    * d * a ^ 2 * f - 2 * c ^ 2 * d * a * f ^ 2 + 4 * c ^ 2 * d * e * f ^ 2 + 4 * c ^ 2 * a * e
    * f ^ 2 + 4 * c * d ^ 2 * a * e ^ 2 - 2 * c * d * a ^ 3 * f + 5 * c * d * e ^ 2 * f ^ 2 + 2
    * c * a * e ^ 2 * f ^ 2

/-- Part 4 of `cpM1p`. -/
def cpM1pd (a b c d e f : ℝ) : ℝ :=
  -2 * b ^ 2 * c * d * a * f + 8 * b ^ 2 * c * d * e * f + 6 * b * c ^ 2 * d ^ 2 * a + 8 * b * c
    ^ 2 * d ^ 2 * e + 11 * b * c ^ 2 * d * a * e + 4 * b * c ^ 2 * d * a * f + 6 * b * c ^ 2 * d
    * e ^ 2 + 12 * b * c ^ 2 * d * e * f + 9 * b * c ^ 2 * a * e * f + 5 * b * c * d ^ 2 * a * e
    - 2 * b * c * d ^ 2 * a * f + 12 * b * c * d ^ 2 * e * f - 4 * b * c * d * a ^ 2 * f + 10 *
    b * c * d * a * e * f - 5 * b * c * d * a * f ^ 2 + 12 * b * c * d * e ^ 2 * f + 8 * b * c *
    d * e * f ^ 2 + 3 * b * c * a * e * f ^ 2 - b * d ^ 2 * a * e * f + 7 * b * d ^ 2 * e ^ 2 *
    f - b * d * a * e * f ^ 2 + 6 * b * d * e ^ 2 * f ^ 2 + 8 * c ^ 3 * d * a * e + 8 * c ^ 2 *
    d ^ 2 * a * e + 7 * c ^ 2 * d ^ 2 * e * f + 7 * c ^ 2 * d * a ^ 2 * e + 8 * c ^ 2 * d * a *
    e ^ 2 + 12 * c ^ 2 * d * a * e * f + 10 * c ^ 2 * d * e ^ 2 * f + 6 * c ^ 2 * a ^ 2 * e * f
    + 7 * c ^ 2 * a * e ^ 2 * f + c * d ^ 2 * a * e * f + 8 * c * d ^ 2 * e ^ 2 * f + 2 * c * d
    * a ^ 2 * e * f + 8 * c * d * a * e ^ 2 * f - 2 * c * d * a * e * f ^ 2 + 6 * c * d * e ^ 3
    * f

/-- Part 1 of `cpM2p`. -/
def cpM2pa (a b c d e f : ℝ) : ℝ :=
  b ^ 2 * c ^ 3 - b ^ 2 * c ^ 2 * d + b ^ 2 * c ^ 2 * f - b ^ 2 * c * f ^ 2 - b ^ 2 * d ^ 3 - b
    ^ 2 * f ^ 3 - b * c ^ 3 * a - b * c ^ 2 * e ^ 2 + b * d ^ 3 * a - b * d ^ 2 * e ^ 2 + b * a
    * f ^ 3 - b * e ^ 2 * f ^ 2 + c ^ 3 * d ^ 2 - c ^ 3 * d * a - 2 * c ^ 3 * a ^ 2 + c ^ 3 * e
    ^ 2 + c ^ 3 * f ^ 2 - c ^ 2 * d ^ 3 + c ^ 2 * d * e ^ 2 + c ^ 2 * e * f ^ 2 - c ^ 2 * f ^ 3
    + c * d ^ 3 * a - c * d ^ 2 * e ^ 2 + c * a * f ^ 3 + 2 * d ^ 3 * a ^ 2 + d ^ 3 * a * e - d
    ^ 3 * e ^ 2 + 2 * a ^ 2 * f ^ 3 - 2 * e ^ 2 * f ^ 3

/-- Part 2 of `cpM2p`. -/
def cpM2pb (a b c d e f : ℝ) : ℝ :=
  -b ^ 2 * c ^ 2 * e - 3 * b ^ 2 * c * d ^ 2 - b ^ 2 * d ^ 2 * e - 2 * b ^ 2 * d ^ 2 * f - 2 * b
    ^ 2 * d * f ^ 2 - b ^ 2 * e * f ^ 2 + 2 * b * c ^ 3 * d - 2 * b * c * d ^ 3 - 2 * b * c * f
    ^ 3 - 2 * b * d ^ 3 * e - 3 * b * e * f ^ 3 - c ^ 3 * a * e - c ^ 3 * a * f - 3 * c ^ 2 * d
    ^ 2 * f - 4 * c ^ 2 * d * a ^ 2 - 3 * c ^ 2 * d * f ^ 2 - c ^ 2 * a ^ 2 * e - 2 * c ^ 2 * a
    ^ 2 * f - c ^ 2 * a * e ^ 2 - 2 * c ^ 2 * e ^ 2 * f - 2 * c * d ^ 3 * e - 5 * c * e ^ 2 * f
    ^ 2 - 3 * c * e * f ^ 3 - d ^ 2 * a ^ 2 * e - d ^ 2 * a * e ^ 2 - 3 * d ^ 2 * e ^ 2 * f - 4
    * d * e ^ 2 * f ^ 2 - a ^ 2 * e * f ^ 2 - a * e ^ 2 * f ^ 2

/-- Part 3 of `cpM2p`. -/
def cpM2pc (a b c d e f : ℝ) : ℝ :=
  -3 * b ^ 2 * c * d * f + 2 * b * c ^ 3 * e + 2 * b * c ^ 3 * f + 2 * b * c ^ 2 * d ^ 2 - 5 * b
    * c ^ 2 * d * a - 2 * b * c ^ 2 * d * f - b * c ^ 2 * a * f - 3 * b * c * d ^ 2 * a - b * c
    * d ^ 2 * e - 5 * b * c * d ^ 2 * f - 2 * b * c * d * e ^ 2 - 5 * b * c * d * f ^ 2 + b * c
    * a * f ^ 2 - 2 * b * c * e ^ 2 * f - 3 * b * c * e * f ^ 2 - 5 * b * d ^ 2 * e * f - 6 * b
    * d * e * f ^ 2 + 2 * c ^ 3 * d * e + 2 * c ^ 3 * d * f + 2 * c ^ 3 * e * f + 2 * c ^ 2 * d
    ^ 2 * a - 3 * c ^ 2 * d * e * f - c ^ 2 * a * e * f - 6 * c * d ^ 2 * e * f - 5 * c * d * e
    ^ 2 * f - 7 * c * d * e * f ^ 2 + 2 * c * a ^ 2 * f ^ 2 + 7 * d ^ 2 * a ^ 2 * f + 7 * d * a
    ^ 2 * f ^ 2

/-- Part 4 of `cpM2p`. -/
def cpM2pd (a b c d e f : ℝ) : ℝ :=
  -2 * b ^ 2 * c * d * e - 2 * b ^ 2 * c * e * f - 2 * b ^ 2 * d * e * f + 3 * b * c ^ 2 * d * e
    - 2 * b * c ^ 2 * a * e + 2 * b * c ^ 2 * e * f - 4 * b * c * d * a * e - 2 * b * c * d * e
    * f - 4 * b * c * a * e * f - 2 * b * d ^ 2 * a * e + 5 * b * d ^ 2 * a * f - 4 * b * d * a
    * e * f + 5 * b * d * a * f ^ 2 - 2 * b * d * e ^ 2 * f - 2 * b * a * e * f ^ 2 - 2 * c ^ 2
    * d * a * f + 2 * c * d ^ 2 * a * e + 4 * c * d ^ 2 * a * f - 2 * c * d * a ^ 2 * e + 3 * c
    * d * a ^ 2 * f - 2 * c * d * a * e ^ 2 + 4 * c * d * a * e * f + 4 * c * d * a * f ^ 2 - 2
    * c * a ^ 2 * e * f - 2 * c * a * e ^ 2 * f + 4 * d ^ 2 * a * e * f - 2 * d * a ^ 2 * e * f
    - 2 * d * a * e ^ 2 * f + 3 * d * a * e * f ^ 2

/-- The polynomial `M₁` of `c₂[T₁]` of `C₊` (`z₀, t, y₃, y₄, z_a, z_b` = `a, …, f`). -/
def cpM1 : ℝ :=
  cpM1pa (z 0) (z 1) (z 2) (z 3) (spza z) (spzb z) +
    cpM1pb (z 0) (z 1) (z 2) (z 3) (spza z) (spzb z) +
    cpM1pc (z 0) (z 1) (z 2) (z 3) (spza z) (spzb z) +
    cpM1pd (z 0) (z 1) (z 2) (z 3) (spza z) (spzb z)

/-- The polynomial `M₂` of `c₂[T₂]` of `C₊`. -/
def cpM2 : ℝ :=
  cpM2pa (z 0) (z 1) (z 2) (z 3) (spza z) (spzb z) +
    cpM2pb (z 0) (z 1) (z 2) (z 3) (spza z) (spzb z) +
    cpM2pc (z 0) (z 1) (z 2) (z 3) (spza z) (spzb z) +
    cpM2pd (z 0) (z 1) (z 2) (z 3) (spza z) (spzb z)

theorem symanzikMatrix_Cp :
    symanzikMatrix (classAlpha .Cp) z =
      !![z 0 + z 1 + z 2 + spza z, z 0 + z 1 + spza z;
        z 0 + z 1 + spza z, z 0 + z 1 + z 3 + spza z + spzb z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symanzikMatrix, Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, spza, spzb]
  all_goals ring

theorem symanzikU_Cp : symanzikU (classAlpha .Cp) z = cpU z := by
  rw [symanzikU, symanzikMatrix_Cp, Matrix.det_fin_two_of, cpU]
  ring

theorem inv_symanzikMatrix_Cp (s t : Fin 2) :
    (symanzikMatrix (classAlpha .Cp) z)⁻¹ s t =
      (cpU z)⁻¹ * !![z 0 + z 1 + z 3 + spza z + spzb z, -(z 0 + z 1 + spza z);
        -(z 0 + z 1 + spza z), z 0 + z 1 + z 2 + spza z] s t := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', ← symanzikU, symanzikU_Cp, symanzikMatrix_Cp,
    Matrix.adjugate_fin_two_of, Matrix.smul_apply, smul_eq_mul]

/-- `S₀ = σ₀ + τ₀`. -/
noncomputable def cpS0 : ℝ := cpSigP z 0 + cpSigQ z 0
/-- `S₁ = σ₁ + τ₁`. -/
noncomputable def cpS1 : ℝ := cpSigP z 1 + cpSigQ z 1
/-- `T₀ = τ₀`. -/
noncomputable def cpT0 : ℝ := cpSigQ z 0
/-- `T₁ = τ₁`. -/
noncomputable def cpT1 : ℝ := cpSigQ z 1

/-- The numerator of `S₀`. -/
def cpS0n : ℝ := z 1 * z 2 + 2 * z 1 * z 3 + z 1 * spzb z + z 2 * z 3 + z 2 * z 0 + z 2 * spza z +
  z 2 * spzb z + 2 * z 3 * z 0 + z 3 * spza z + z 0 * spzb z
/-- The numerator of `S₁`. -/
def cpS1n : ℝ := -z 1 * z 3 - z 2 * z 3 - z 2 * spza z - z 3 * z 0 - z 3 * spza z
/-- The numerator of `T₀`. -/
def cpT0n : ℝ := z 1 * z 2 + 2 * z 1 * z 3 + z 1 * spzb z + z 2 * z 3 + z 2 * z 0 + z 2 * spza z +
  z 2 * spzb z + z 3 * z 0 + z 3 * spza z
/-- The numerator of `T₁`. -/
def cpT1n : ℝ := -z 1 * z 3 - z 2 * z 3 - z 2 * z 0 - z 2 * spza z - z 3 * z 0 - z 3 * spza z

theorem cpS0_eq : cpS0 z = (cpU z)⁻¹ * cpS0n z := by
  simp only [cpS0, cpSigP, cpSigQ, inv_symanzikMatrix_Cp, cpS0n]
  simp
  ring

theorem cpS1_eq : cpS1 z = (cpU z)⁻¹ * cpS1n z := by
  simp only [cpS1, cpSigP, cpSigQ, inv_symanzikMatrix_Cp, cpS1n]
  simp
  ring

theorem cpT0_eq : cpT0 z = (cpU z)⁻¹ * cpT0n z := by
  simp only [cpT0, cpSigQ, inv_symanzikMatrix_Cp, cpT0n]
  simp
  ring

theorem cpT1_eq : cpT1 z = (cpU z)⁻¹ * cpT1n z := by
  simp only [cpT1, cpSigQ, inv_symanzikMatrix_Cp, cpT1n]
  simp
  ring

end Params

/-! ### The rational identities -/

/-- The homogeneous form of the identity of `c₂[T₁]` (a polynomial identity). -/
theorem cpHom1_identity (z : Fin 8 → ℝ) :
    -512 * cpS0n z ^ 3 * cpS1n z - 1024 * cpS0n z ^ 2 * cpS1n z ^ 2 + 512 * cpS0n z ^ 2 * cpS1n
    z * cpU z - 512 * cpS0n z ^ 2 * cpT0n z * cpU z + 512 * cpS0n z ^ 2 * cpT1n z * cpU z - 512
    * cpS0n z ^ 2 * cpU z ^ 2 - 512 * cpS0n z * cpS1n z ^ 3 + 512 * cpS0n z * cpS1n z ^ 2 * cpU
    z - 1024 * cpS0n z * cpS1n z * cpT0n z * cpU z + 1024 * cpS0n z * cpS1n z * cpT1n z * cpU z
    + 1024 * cpS0n z * cpT0n z * cpU z ^ 2 - 1024 * cpS0n z * cpT1n z * cpU z ^ 2 - 512 * cpS1n
    z ^ 2 * cpT0n z * cpU z + 512 * cpS1n z ^ 2 * cpT1n z * cpU z + 512 * cpS1n z ^ 2 * cpU z ^
    2 + 1024 * cpS1n z * cpT0n z * cpU z ^ 2 - 1024 * cpS1n z * cpT1n z * cpU z ^ 2 =
      512 * cpW z * cpM1 z := by
  simp only [cpS0n, cpS1n, cpT0n, cpT1n, cpU, cpW, cpM1, cpM1pa, cpM1pb, cpM1pc, cpM1pd]
  ring

/-- The rational identity of `c₂[T₁]` of `C₊`. -/
theorem cpPsi1_identity {z : Fin 8 → ℝ} (hU : cpU z ≠ 0) :
      -512*cpS0 z ^ 3*cpS1 z - 1024*cpS0 z ^ 2*cpS1 z ^ 2 + 512*cpS0 z ^ 2*cpS1 z - 512*cpS0 z ^
      2*cpT0 z + 512*cpS0 z ^ 2*cpT1 z - 512*cpS0 z ^ 2 - 512*cpS0 z*cpS1 z ^ 3 + 512*cpS0
      z*cpS1 z ^ 2 - 1024*cpS0 z*cpS1 z*cpT0 z + 1024*cpS0 z*cpS1 z*cpT1 z + 1024*cpS0 z*cpT0 z
      - 1024*cpS0 z*cpT1 z - 512*cpS1 z ^ 2*cpT0 z + 512*cpS1 z ^ 2*cpT1 z + 512*cpS1 z ^ 2 +
      1024*cpS1 z*cpT0 z - 1024*cpS1 z*cpT1 z =
      512 * cpW z * cpM1 z / cpU z ^ 4 := by
  rw [cpS0_eq, cpS1_eq, cpT0_eq, cpT1_eq, div_eq_mul_inv, ← inv_pow]
  have hpoly := cpHom1_identity z
  generalize hu' : (cpU z)⁻¹ = u
  have hu : cpU z * u = 1 := by rw [← hu']; exact mul_inv_cancel₀ hU
  linear_combination (-(
      512 * cpS0n z ^ 2 * cpS1n z * u ^ 3 - 512 * cpS0n z ^ 2 * cpT0n z * u ^ 3 + 512 * cpS0n z
      ^ 2 * cpT1n z * u ^ 3 - 512 * cpS0n z ^ 2 * cpU z * u ^ 3 - 512 * cpS0n z ^ 2 * u ^ 2 +
      512 * cpS0n z * cpS1n z ^ 2 * u ^ 3 - 1024 * cpS0n z * cpS1n z * cpT0n z * u ^ 3 + 1024 *
      cpS0n z * cpS1n z * cpT1n z * u ^ 3 + 1024 * cpS0n z * cpT0n z * cpU z * u ^ 3 + 1024 *
      cpS0n z * cpT0n z * u ^ 2 - 1024 * cpS0n z * cpT1n z * cpU z * u ^ 3 - 1024 * cpS0n z *
      cpT1n z * u ^ 2 - 512 * cpS1n z ^ 2 * cpT0n z * u ^ 3 + 512 * cpS1n z ^ 2 * cpT1n z * u ^
      3 + 512 * cpS1n z ^ 2 * cpU z * u ^ 3 + 512 * cpS1n z ^ 2 * u ^ 2 + 1024 * cpS1n z * cpT0n
      z * cpU z * u ^ 3 + 1024 * cpS1n z * cpT0n z * u ^ 2 - 1024 * cpS1n z * cpT1n z * cpU z *
      u ^ 3 - 1024 * cpS1n z * cpT1n z * u ^ 2)) * hu + u ^ 4 * hpoly

/-- The homogeneous form of the identity of `c₂[T₂]` (a polynomial identity). -/
theorem cpHom2_identity (z : Fin 8 → ℝ) :
    -1024 * cpS0n z ^ 2 * (z 0 + z 1 + spza z) - 2048 * cpS0n z ^ 2 * (-z 2) - 2048 * cpS0n z ^
    2 * (-z 2) - 2048 * cpS0n z * cpS1n z * (z 0 + z 1 + spza z) - 2048 * cpS0n z * cpS1n z *
    (-z 2) - 2048 * cpS0n z * cpS1n z * (-z 2) - 1024 * cpS0n z * cpS1n z * (z 2 + z 3 + spzb z)
    - 1024 * cpS0n z * cpT1n z * (z 3 + spzb z) + 1024 * cpS0n z * cpT1n z * (z 3 + spzb z) +
    1024 * cpS0n z * cpU z * (z 0 + z 1 + spza z) + 1024 * cpS0n z * cpU z * (-z 2) + 3072 *
    cpS0n z * cpU z * (-z 2) - 2048 * cpS0n z * cpU z * (z 3 + spzb z) - 1024 * cpS0n z * cpU z
    * (z 3 + spzb z) - 1024 * cpS0n z * cpU z * (z 2 + z 3 + spzb z) - 1024 * cpS1n z ^ 2 * (z 0
    + z 1 + spza z) + 1024 * cpS1n z * cpT0n z * (z 3 + spzb z) - 1024 * cpS1n z * cpT0n z * (z
    3 + spzb z) + 1024 * cpS1n z * cpU z * (z 0 + z 1 + spza z) + 1024 * cpS1n z * cpU z * (-z
    2) - 2048 * cpS1n z * cpU z * (z 3 + spzb z) + 1024 * cpS1n z * cpU z * (z 2 + z 3 + spzb z)
    + 2048 * cpT0n z * cpU z * (-z 2) + 1024 * cpT0n z * cpU z * (-z 2) + 1024 * cpT0n z * cpU z
    * (z 3 + spzb z) + 1024 * cpT0n z * cpU z * (z 3 + spzb z) + 1024 * cpT0n z * cpU z * (z 2 +
    z 3 + spzb z) + 2048 * cpT1n z * cpU z * (-z 2) + 1024 * cpT1n z * cpU z * (z 3 + spzb z) +
    2048 * cpT1n z * cpU z * (z 3 + spzb z) - 1024 * cpT1n z * cpU z * (z 2 + z 3 + spzb z) -
    1024 * cpU z ^ 2 * (-z 2) - 2048 * cpU z ^ 2 * (-z 2) + 1024 * cpU z ^ 2 * (z 3 + spzb z) +
    2048 * cpU z ^ 2 * (z 3 + spzb z) - 1024 * cpU z ^ 2 * (z 2 + z 3 + spzb z) =
      -1024 * cpM2 z := by
  simp only [cpS0n, cpS1n, cpT0n, cpT1n, cpU, cpM2, cpM2pa, cpM2pb, cpM2pc, cpM2pd]
  ring

/-- The rational identity of `c₂[T₂]` of `C₊`, with the contraction coefficients
`C₀₁ = (z_o + z_a)/U`, `C₀₂ = C₀₃ = -y₃/U`, `C₁₂ = C₁₃ = (y₄ + z_b)/U`, `C₂₃ = (y₃ + y₄ + z_b)/U`. -/
theorem cpPsi2_identity {z : Fin 8 → ℝ} (hU : cpU z ≠ 0) :
      -1024*((z 0 + z 1 + spza z) / cpU z)*cpS0 z ^ 2 - 2048*((z 0 + z 1 + spza z) / cpU z)*cpS0
      z*cpS1 z + 1024*((z 0 + z 1 + spza z) / cpU z)*cpS0 z - 1024*((z 0 + z 1 + spza z) / cpU
      z)*cpS1 z ^ 2 + 1024*((z 0 + z 1 + spza z) / cpU z)*cpS1 z - 2048*(-z 2 / cpU z)*cpS0 z ^
      2 - 2048*(-z 2 / cpU z)*cpS0 z*cpS1 z + 1024*(-z 2 / cpU z)*cpS0 z + 1024*(-z 2 / cpU
      z)*cpS1 z + 2048*(-z 2 / cpU z)*cpT0 z - 1024*(-z 2 / cpU z) - 2048*(-z 2 / cpU z)*cpS0 z
      ^ 2 - 2048*(-z 2 / cpU z)*cpS0 z*cpS1 z + 3072*(-z 2 / cpU z)*cpS0 z + 1024*(-z 2 / cpU
      z)*cpT0 z + 2048*(-z 2 / cpU z)*cpT1 z - 2048*(-z 2 / cpU z) - 1024*((z 3 + spzb z) / cpU
      z)*cpS0 z*cpT1 z - 2048*((z 3 + spzb z) / cpU z)*cpS0 z + 1024*((z 3 + spzb z) / cpU
      z)*cpS1 z*cpT0 z - 2048*((z 3 + spzb z) / cpU z)*cpS1 z + 1024*((z 3 + spzb z) / cpU
      z)*cpT0 z + 1024*((z 3 + spzb z) / cpU z)*cpT1 z + 1024*((z 3 + spzb z) / cpU z) +
      1024*((z 3 + spzb z) / cpU z)*cpS0 z*cpT1 z - 1024*((z 3 + spzb z) / cpU z)*cpS0 z -
      1024*((z 3 + spzb z) / cpU z)*cpS1 z*cpT0 z + 1024*((z 3 + spzb z) / cpU z)*cpT0 z +
      2048*((z 3 + spzb z) / cpU z)*cpT1 z + 2048*((z 3 + spzb z) / cpU z) - 1024*((z 2 + z 3 +
      spzb z) / cpU z)*cpS0 z*cpS1 z - 1024*((z 2 + z 3 + spzb z) / cpU z)*cpS0 z + 1024*((z 2 +
      z 3 + spzb z) / cpU z)*cpS1 z + 1024*((z 2 + z 3 + spzb z) / cpU z)*cpT0 z - 1024*((z 2 +
      z 3 + spzb z) / cpU z)*cpT1 z - 1024*((z 2 + z 3 + spzb z) / cpU z) =
      -1024 * cpM2 z / cpU z ^ 3 := by
  rw [cpS0_eq, cpS1_eq, cpT0_eq, cpT1_eq]
  simp only [div_eq_mul_inv, ← inv_pow]
  have hpoly := cpHom2_identity z
  generalize hu' : (cpU z)⁻¹ = u
  have hu : cpU z * u = 1 := by rw [← hu']; exact mul_inv_cancel₀ hU
  linear_combination (-(
      1024 * cpS0n z * (z 0 + z 1 + spza z) * u ^ 2 + 1024 * cpS0n z * (-z 2) * u ^ 2 + 3072 *
      cpS0n z * (-z 2) * u ^ 2 - 2048 * cpS0n z * (z 3 + spzb z) * u ^ 2 - 1024 * cpS0n z * (z 3
      + spzb z) * u ^ 2 - 1024 * cpS0n z * (z 2 + z 3 + spzb z) * u ^ 2 + 1024 * cpS1n z * (z 0
      + z 1 + spza z) * u ^ 2 + 1024 * cpS1n z * (-z 2) * u ^ 2 - 2048 * cpS1n z * (z 3 + spzb
      z) * u ^ 2 + 1024 * cpS1n z * (z 2 + z 3 + spzb z) * u ^ 2 + 2048 * cpT0n z * (-z 2) * u ^
      2 + 1024 * cpT0n z * (-z 2) * u ^ 2 + 1024 * cpT0n z * (z 3 + spzb z) * u ^ 2 + 1024 *
      cpT0n z * (z 3 + spzb z) * u ^ 2 + 1024 * cpT0n z * (z 2 + z 3 + spzb z) * u ^ 2 + 2048 *
      cpT1n z * (-z 2) * u ^ 2 + 1024 * cpT1n z * (z 3 + spzb z) * u ^ 2 + 2048 * cpT1n z * (z 3
      + spzb z) * u ^ 2 - 1024 * cpT1n z * (z 2 + z 3 + spzb z) * u ^ 2 - 1024 * cpU z * (-z 2)
      * u ^ 2 - 2048 * cpU z * (-z 2) * u ^ 2 + 1024 * cpU z * (z 3 + spzb z) * u ^ 2 + 2048 *
      cpU z * (z 3 + spzb z) * u ^ 2 - 1024 * cpU z * (z 2 + z 3 + spzb z) * u ^ 2 - 1024 * (-z
      2) * u - 2048 * (-z 2) * u + 1024 * (z 3 + spzb z) * u + 2048 * (z 3 + spzb z) * u - 1024
      * (z 2 + z 3 + spzb z) * u)) * hu + u ^ 3 * hpoly


/-! ### The second-order coefficients -/

/-- The jet of the slot numerator `k` of `C₊`. -/
noncomputable def cpSlotJ (z : Fin 8 → ℝ) (k : Fin 4) : PJ :=
  eJ ((cpSlotA z k : ℂ) + (cpSlotB z k : ℂ)) (cpSlotB z k : ℂ)

theorem ppJ_cpSlot_T1 (z : Fin 8 → ℝ) :
    ppJ qJ0 qJ1 rJ (((cpSlotJ z 0).mul (PJ.c g0L)).mul (cpSlotJ z 1)).gam (((cpSlotJ z 0).mul (PJ.c g1)).mul (cpSlotJ z 1)).gam (((cpSlotJ z 0).mul (PJ.c 1)).mul (cpSlotJ z 1).bar).gamT (cpSlotJ z 2) (cpSlotJ z 3) =
      ((
      -512*cpS0 z ^ 3*cpS1 z - 1024*cpS0 z ^ 2*cpS1 z ^ 2 + 512*cpS0 z ^ 2*cpS1 z - 512*cpS0 z ^
      2*cpT0 z + 512*cpS0 z ^ 2*cpT1 z - 512*cpS0 z ^ 2 - 512*cpS0 z*cpS1 z ^ 3 + 512*cpS0
      z*cpS1 z ^ 2 - 1024*cpS0 z*cpS1 z*cpT0 z + 1024*cpS0 z*cpS1 z*cpT1 z + 1024*cpS0 z*cpT0 z
      - 1024*cpS0 z*cpT1 z - 512*cpS1 z ^ 2*cpT0 z + 512*cpS1 z ^ 2*cpT1 z + 512*cpS1 z ^ 2 +
      1024*cpS1 z*cpT0 z - 1024*cpS1 z*cpT1 z : ℝ) : ℂ) := by
  simp only [cpSlotJ, ppJ_Cp_T1, cpSlotA, cpSlotB, cpS0, cpS1, cpT0, cpT1, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  ring

/-- **The jet of `T₁` of `C₊`**. -/
theorem hasJet2_cpT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : cpU z ≠ 0) :
    HasJet2 (classT1 .Cp permCp P z) 0 0 (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
      ((cpW z * cpM1 z / (2 * cpU z ^ 6) : ℝ) : ℂ)) := by
  have hE := jet_cpE hm z
  have hq0 : HasPJ (fun u => lQ0 P u) qJ0 := jet_lQ0 hm
  have hq1 : HasPJ (fun u => lQ1 P u) qJ1 := jet_lQ1 hm
  have hr : HasPJ (fun u => lR P u) rJ := jet_lR hm
  have h := hasJet2_ppPl hq0 hq1 hr
    (((hE 0).mul (HasPJ.const g0L)).mul (hE 1)).gam (((hE 0).mul (HasPJ.const g1)).mul (hE 1)).gam
    (((hE 0).mul (HasPJ.const 1)).mul (hE 1).bar).gamT (hE 2) (hE 3)
  have h' := (h.const_mul 6).const_mul
    (ladderK P * ((symanzikU (classAlpha .Cp) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h'.congr fun u => classT1_Cp_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp
  · simp
  have e := ppJ_cpSlot_T1 z
  simp only [cpSlotJ] at e
  rw [e, cpPsi1_identity hU, ladderK_eq he, symanzikU_Cp, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (cpU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₁` of `C₊`**. -/
theorem secondCoeff_cpT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : cpU z ≠ 0) :
    secondCoeff (classT1 .Cp permCp P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
      ((cpW z * cpM1 z / (2 * cpU z ^ 6) : ℝ) : ℂ) :=
  (hasJet2_cpT1 hm he hU).secondCoeff_eq

theorem classC_Cp_val (z : Fin 8 → ℝ) :
    classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 1 = (((z 0 + z 1 + spza z) / cpU z : ℝ) : ℂ) ∧
    classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 2 = ((-z 2 / cpU z : ℝ) : ℂ) ∧
    classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 3 = ((-z 2 / cpU z : ℝ) : ℂ) ∧
    classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 2 = (((z 3 + spzb z) / cpU z : ℝ) : ℂ) ∧
    classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 3 = (((z 3 + spzb z) / cpU z : ℝ) : ℂ) ∧
    classC .Cp (symanzikMatrix (classAlpha .Cp) z) 2 3 = (((z 2 + z 3 + spzb z) / cpU z : ℝ) : ℂ) := by
  simp only [classC, contrC, Fin.sum_univ_two, inv_symanzikMatrix_Cp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix, ladderLines]
  all_goals ring

theorem cpT2_combination (z : Fin 8 → ℝ) :
    classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 1 *
        (4 * ppJ qJ0 qJ1 rJ (PJ.c g0L) (PJ.c g1) (PJ.c 1) (cpSlotJ z 2) (cpSlotJ z 3)) +
      classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 2 *
        (-ppJ qJ0 qJ1 rJ ((PJ.c g0L).mul (cpSlotJ z 1)).gam.gam ((PJ.c g1).mul (cpSlotJ z 1)).gam.gam ((PJ.c 1).mul (cpSlotJ z 1).bar).gamT.gamT (PJ.c 1) (cpSlotJ z 3) +
          8 * ppJ qJ0 qJ1 rJ ((PJ.c g0L).mul (cpSlotJ z 1)) ((PJ.c g1).mul (cpSlotJ z 1)) ((PJ.c 1).mul (cpSlotJ z 1).bar) (PJ.c 1) (cpSlotJ z 3)) +
      classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 3 *
        (ppJ qJ0.gam qJ1.gam rJ.gamT (((PJ.c 1).mul (PJ.c g0L)).mul (cpSlotJ z 1)).gam (((PJ.c 1).mul (PJ.c g1)).mul (cpSlotJ z 1)).gam (((PJ.c 1).mul (PJ.c 1)).mul (cpSlotJ z 1).bar).gamT (cpSlotJ z 2) (PJ.c 1) +
          4 * pwJ qJ0 qJ1 rJ ((cpSlotJ z 1).gam.mul (cpSlotJ z 2)) (PJ.c 1) +
          2 * pwJ qJ0.gam qJ1.gam rJ.gamT ((cpSlotJ z 1).mul (cpSlotJ z 2).gam) (PJ.c 1) +
          4 * pwJ qJ0.gam qJ1.gam rJ.gamT (cpSlotJ z 1) (cpSlotJ z 2)) +
      classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 2 *
        (2 * ppJ qJ0 qJ1 rJ (((cpSlotJ z 0).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((cpSlotJ z 0).mul (PJ.c g1)).mul (PJ.c 1)).gam (((cpSlotJ z 0).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (cpSlotJ z 3)) +
      classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 3 *
        (ppJ qJ0 qJ1 rJ (((cpSlotJ z 0).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((cpSlotJ z 0).mul (PJ.c g1)).mul (PJ.c 1)).gam (((cpSlotJ z 0).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (cpSlotJ z 2).gam (PJ.c 1) +
          2 * ppJ qJ0 qJ1 rJ (((cpSlotJ z 0).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((cpSlotJ z 0).mul (PJ.c g1)).mul (PJ.c 1)).gam (((cpSlotJ z 0).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (cpSlotJ z 2) +
          2 * ppJ qJ0 qJ1 rJ (((cpSlotJ z 0).mul (PJ.c g0L)).mul (cpSlotJ z 2)).gam (((cpSlotJ z 0).mul (PJ.c g1)).mul (cpSlotJ z 2)).gam (((cpSlotJ z 0).mul (PJ.c 1)).mul (cpSlotJ z 2).bar).gamT (PJ.c 1) (PJ.c 1) +
          4 * pwJ qJ0 qJ1 rJ (PJ.c 1) ((cpSlotJ z 0).mul (cpSlotJ z 2).gam)) +
      classC .Cp (symanzikMatrix (classAlpha .Cp) z) 2 3 *
        (2 * ppJ qJ0 qJ1 rJ (((cpSlotJ z 0).mul (PJ.c g0L)).mul (cpSlotJ z 1)).gam (((cpSlotJ z 0).mul (PJ.c g1)).mul (cpSlotJ z 1)).gam (((cpSlotJ z 0).mul (PJ.c 1)).mul (cpSlotJ z 1).bar).gamT (PJ.c 1) (PJ.c 1)) =
    ((
      -1024*((z 0 + z 1 + spza z) / cpU z)*cpS0 z ^ 2 - 2048*((z 0 + z 1 + spza z) / cpU z)*cpS0
      z*cpS1 z + 1024*((z 0 + z 1 + spza z) / cpU z)*cpS0 z - 1024*((z 0 + z 1 + spza z) / cpU
      z)*cpS1 z ^ 2 + 1024*((z 0 + z 1 + spza z) / cpU z)*cpS1 z - 2048*(-z 2 / cpU z)*cpS0 z ^
      2 - 2048*(-z 2 / cpU z)*cpS0 z*cpS1 z + 1024*(-z 2 / cpU z)*cpS0 z + 1024*(-z 2 / cpU
      z)*cpS1 z + 2048*(-z 2 / cpU z)*cpT0 z - 1024*(-z 2 / cpU z) - 2048*(-z 2 / cpU z)*cpS0 z
      ^ 2 - 2048*(-z 2 / cpU z)*cpS0 z*cpS1 z + 3072*(-z 2 / cpU z)*cpS0 z + 1024*(-z 2 / cpU
      z)*cpT0 z + 2048*(-z 2 / cpU z)*cpT1 z - 2048*(-z 2 / cpU z) - 1024*((z 3 + spzb z) / cpU
      z)*cpS0 z*cpT1 z - 2048*((z 3 + spzb z) / cpU z)*cpS0 z + 1024*((z 3 + spzb z) / cpU
      z)*cpS1 z*cpT0 z - 2048*((z 3 + spzb z) / cpU z)*cpS1 z + 1024*((z 3 + spzb z) / cpU
      z)*cpT0 z + 1024*((z 3 + spzb z) / cpU z)*cpT1 z + 1024*((z 3 + spzb z) / cpU z) +
      1024*((z 3 + spzb z) / cpU z)*cpS0 z*cpT1 z - 1024*((z 3 + spzb z) / cpU z)*cpS0 z -
      1024*((z 3 + spzb z) / cpU z)*cpS1 z*cpT0 z + 1024*((z 3 + spzb z) / cpU z)*cpT0 z +
      2048*((z 3 + spzb z) / cpU z)*cpT1 z + 2048*((z 3 + spzb z) / cpU z) - 1024*((z 2 + z 3 +
      spzb z) / cpU z)*cpS0 z*cpS1 z - 1024*((z 2 + z 3 + spzb z) / cpU z)*cpS0 z + 1024*((z 2 +
      z 3 + spzb z) / cpU z)*cpS1 z + 1024*((z 2 + z 3 + spzb z) / cpU z)*cpT0 z - 1024*((z 2 +
      z 3 + spzb z) / cpU z)*cpT1 z - 1024*((z 2 + z 3 + spzb z) / cpU z) : ℝ) : ℂ) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := classC_Cp_val z
  rw [h01, h02, h03, h12, h13, h23]
  simp only [cpSlotJ, ppJ_Cp_01, ppJ_Cp_02a, ppJ_Cp_02b, ppJ_Cp_03a, pwJ_Cp_03b, pwJ_Cp_03c,
    pwJ_Cp_03d, ppJ_Cp_12, ppJ_Cp_13a, ppJ_Cp_13c, pwJ_Cp_13d, cpSlotA,
    cpSlotB, cpS0, cpS1, cpT0, cpT1, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

/-- **The jet of `T₂` of `C₊`**. -/
theorem hasJet2_cpT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : cpU z ≠ 0) :
    HasJet2 (classT2 .Cp permCp P z) 0 0 (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
      ((-cpM2 z / (2 * cpU z ^ 5) : ℝ) : ℂ)) := by
  have hq0 : HasPJ (fun u => lQ0 P u) qJ0 := jet_lQ0 hm
  have hq1 : HasPJ (fun u => lQ1 P u) qJ1 := jet_lQ1 hm
  have hr : HasPJ (fun u => lR P u) rJ := jet_lR hm
  have hE := jet_cpE hm z
  have c1 := HasPJ.const (1 : Pl)
  have cL := HasPJ.const g0L
  have c1' := HasPJ.const g1
  have h01 := hasJet2_ppPl hq0 hq1 hr cL c1' c1 (hE 2) (hE 3)
  have h02a := hasJet2_ppPl hq0 hq1 hr (cL.mul (hE 1)).gam.gam (c1'.mul (hE 1)).gam.gam
    (c1.mul (hE 1).bar).gamT.gamT c1 (hE 3)
  have h02b := hasJet2_ppPl hq0 hq1 hr (cL.mul (hE 1)) (c1'.mul (hE 1)) (c1.mul (hE 1).bar) c1 (hE 3)
  have h03a := hasJet2_ppPl hq0.gam hq1.gam hr.gamT ((c1.mul cL).mul (hE 1)).gam
    ((c1.mul c1').mul (hE 1)).gam ((c1.mul c1).mul (hE 1).bar).gamT (hE 2) c1
  have h03b := hasJet2_pwPl hq0 hq1 hr ((hE 1).gam.mul (hE 2)) c1
  have h03c := hasJet2_pwPl hq0.gam hq1.gam hr.gamT ((hE 1).mul (hE 2).gam) c1
  have h03d := hasJet2_pwPl hq0.gam hq1.gam hr.gamT (hE 1) (hE 2)
  have hH0 := (((hE 0).mul cL).mul c1).gam
  have hH1 := (((hE 0).mul c1').mul c1).gam
  have hHB := (((hE 0).mul c1).mul c1.bar).gamT
  have h12 := hasJet2_ppPl hq0 hq1 hr hH0 hH1 hHB c1 (hE 3)
  have h13a := hasJet2_ppPl hq0 hq1 hr hH0 hH1 hHB (hE 2).gam c1
  have h13b := hasJet2_ppPl hq0 hq1 hr hH0 hH1 hHB c1 (hE 2)
  have h13c := hasJet2_ppPl hq0 hq1 hr (((hE 0).mul cL).mul (hE 2)).gam
    (((hE 0).mul c1').mul (hE 2)).gam (((hE 0).mul c1).mul (hE 2).bar).gamT c1 c1
  have h13d := hasJet2_pwPl hq0 hq1 hr c1 ((hE 0).mul (hE 2).gam)
  have h23 := hasJet2_ppPl hq0 hq1 hr (((hE 0).mul cL).mul (hE 1)).gam
    (((hE 0).mul c1').mul (hE 1)).gam (((hE 0).mul c1).mul (hE 1).bar).gamT c1 c1
  have g1 := (h01.const_mul 4).const_mul
    (classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 1)
  have g2 := (h02a.neg.add (h02b.const_mul 8)).const_mul
    (classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 2)
  have g3 := (((h03a.add (h03b.const_mul 4)).add (h03c.const_mul 2)).add
    (h03d.const_mul 4)).const_mul
    (classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 3)
  have g4 := (h12.const_mul 2).const_mul
    (classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 2)
  have g5 := (((h13a.add (h13b.const_mul 2)).add (h13c.const_mul 2)).add
    (h13d.const_mul 4)).const_mul
    (classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 3)
  have g6 := (h23.const_mul 2).const_mul
    (classC .Cp (symanzikMatrix (classAlpha .Cp) z) 2 3)
  have h := (((((g1.add g2).add g3).add g4).add g5).add g6).const_mul
    (ladderK P * ((symanzikU (classAlpha .Cp) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => classT2_Cp_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp
  · simp
  have hc := cpT2_combination z
  simp only [cpSlotJ] at hc
  rw [hc, cpPsi2_identity hU, ladderK_eq he, symanzikU_Cp, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (cpU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₂` of `C₊`**. -/
theorem secondCoeff_cpT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : cpU z ≠ 0) :
    secondCoeff (classT2 .Cp permCp P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
      ((-cpM2 z / (2 * cpU z ^ 5) : ℝ) : ℂ) :=
  (hasJet2_cpT2 hm he hU).secondCoeff_eq

/-- **The jet of `T₃` of `C₊` vanishes**. -/
theorem hasJet2_cpT3 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasJet2 (classT3 .Cp permCp P z) 0 0 0 := by
  have hq0 : HasPJ (fun u => lQ0 P u) qJ0 := jet_lQ0 hm
  have hq1 : HasPJ (fun u => lQ1 P u) qJ1 := jet_lQ1 hm
  have hr : HasPJ (fun u => lR P u) rJ := jet_lR hm
  have h₁ := hasJet2_pwPl hq0 hq1 hr (HasPJ.const 1) (HasPJ.const 1)
  set C := fun k l => classC .Cp (symanzikMatrix (classAlpha .Cp) z) k l
  have h := (((((h₁.const_mul 16).const_mul (C 0 1 * C 2 3)).add
    ((h₁.const_mul (-32)).const_mul (C 0 2 * C 1 3))).add
    ((h₁.const_mul (-32)).const_mul (C 0 3 * C 1 2))).const_mul (1 / 4)).const_mul
    (ladderK P * ((symanzikU (classAlpha .Cp) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => classT3_Cp_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp
  · simp
  · simp [pwJ_Cp_T3]

/-- **The second-order coefficient of `T₃` of `C₊` vanishes.** -/
theorem secondCoeff_cpT3 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    secondCoeff (classT3 .Cp permCp P z) = 0 :=
  (hasJet2_cpT3 hm z).secondCoeff_eq

/-! ### The second-order coefficient of the projected numerator -/

@[fun_prop] theorem continuous_pvMomentaE_Cp (r : Fin 4 → ℝ) (i : Fin 8) (μ : Fin 4) :
    Continuous fun p' : Fin 4 → ℝ => pvMomentaE .Cp r p' i μ := by
  fin_cases i <;>
    simp [pvMomentaE, extMomenta, QED.Integration.TwoLoop.classCpSpMomenta,
      QED.Integration.TwoLoop.pvLines] <;> fun_prop

theorem continuous_cpV (r : Fin 4 → ℝ) (M z : Fin 8 → ℝ) :
    Continuous fun p' : Fin 4 → ℝ => symanzikV (classAlpha .Cp) (pvMomentaE .Cp r p') M z := by
  unfold symanzikV symanzikVector QED.Minkowski.dot
  fun_prop

/-- The second Symanzik function of `C₊` along the curve tends to its value at `q = 0`. -/
theorem tendsto_cpV (P : Params) (x : Fin 7 → ℝ) :
    Tendsto (fun u => ((symanzikV (classAlpha .Cp) (classMom .Cp P u) (pvMasses P)
        (simplexPoint x) : ℝ) : ℂ))
      (𝓝 0) (𝓝 ((openV .Cp P x : ℝ) : ℂ)) := by
  have h := ((continuous_cpV (restMomentum P.m) (pvMasses P) (simplexPoint x)).tendsto
    (restMomentum P.m)).comp (tendsto_curveMomentum P.m)
  exact (Complex.continuous_ofReal.tendsto _).comp h

theorem Cp_mem_openClasses : Class5.Cp ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide

/-- **The jet of the projected `C₊` numerator**: `N(x, u) = c₂ u² + o(u²)` with
`c₂ = c₂[T₁] + c₂[T₂] V(x)`. -/
theorem hasJet2_openNum_Cp {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : cpU (simplexPoint x) ≠ 0) :
    HasJet2 (openNum .Cp P x) 0 0
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((cpW (simplexPoint x) * cpM1 (simplexPoint x) / (2 * cpU (simplexPoint x) ^ 6) : ℝ) :
            ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((-cpM2 (simplexPoint x) / (2 * cpU (simplexPoint x) ^ 5) : ℝ) : ℂ) *
            ((openV .Cp P x : ℝ) : ℂ)) := by
  have hV := tendsto_cpV P x
  have h := ((hasJet2_cpT1 hm he hU).add (hasJet2_mul_tendsto (hasJet2_cpT2 hm he hU) hV)).add
    (hasJet2_mul_tendsto (hasJet2_cpT3 hm (simplexPoint x)) (hV.pow 2))
  exact h.of_eq (fun u => openNum_eq_T_of_chain isChainForm_Cp classMomE_Cp_eq Cp_mem_openClasses
    P x u) (by ring) (by ring) (by ring)

/-- **The second-order coefficient of the projected `C₊` numerator.** -/
theorem secondCoeff_openNum_Cp {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : cpU (simplexPoint x) ≠ 0) :
    secondCoeff (openNum .Cp P x) =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((cpW (simplexPoint x) * cpM1 (simplexPoint x) / (2 * cpU (simplexPoint x) ^ 6) : ℝ) :
            ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((-cpM2 (simplexPoint x) / (2 * cpU (simplexPoint x) ^ 5) : ℝ) : ℂ) *
            ((openV .Cp P x : ℝ) : ℂ) :=
  (hasJet2_openNum_Cp hm he x hU).secondCoeff_eq

/-- Almost every point of the simplex has `U ≠ 0` (for `C₊`). -/
theorem ae_cpU_ne_zero : ∀ᵐ x ∂(MeasureTheory.volume.restrict
    (QED.Integration.Feynman.simplexSet 7)),
    cpU (simplexPoint x) ≠ 0 := by
  have hspan : ∃ i j, classAlpha .Cp i 0 * classAlpha .Cp j 1 -
      classAlpha .Cp i 1 * classAlpha .Cp j 0 ≠ 0 :=
    ⟨2, 3, by simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix]⟩
  filter_upwards [QED.Integration.TwoLoop.ae_posDef (classAlpha .Cp) (by norm_num) hspan] with x hx
  rw [← symanzikU_Cp]
  exact hx.2.det_pos.ne'

/-- **The `C₊` class value with the explicit integrand**: at `m = 1`, `e = 1`,
`openZero .Cp P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴` with
`c₂[T₁] = (Λ² - m_γ²)² (6/K) W M₁/(2U⁶)` and `c₂[T₂] = (Λ² - m_γ²)² (2/K) (-M₂/(2U⁵))`. -/
theorem openZero_Cp_eq {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .Cp P = ∫ x in QED.Integration.Feynman.simplexSet 7,
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((cpW (simplexPoint x) * cpM1 (simplexPoint x) / (2 * cpU (simplexPoint x) ^ 6) : ℝ) :
            ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((-cpM2 (simplexPoint x) / (2 * cpU (simplexPoint x) ^ 5) : ℝ) : ℂ) *
            ((openV .Cp P x : ℝ) : ℂ)) /
        ((openV .Cp P x : ℝ) : ℂ) ^ 4 := by
  unfold openZero
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_cpU_ne_zero] with x hx
  rw [secondCoeff_openNum_Cp hm he x hx]

end QED.TwoLoop.UnitSCGraph

end
