/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphTraceJet
public import QED.TwoLoop.UnitLGraphTraceMain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The pointwise second-order coefficients of the crossed-ladder numerator

Section 8 of `docs/TWO-LOOP-UNITS.md`, the graph half of the X unit, item (i). With the
projected crossed numerator `N = T₁ + T₂ V + T₃ V²`
(`QED.TwoLoop.UnitXGraph.openNum_X_eq_T`) and, at a point `z` of the eight line parameters,
`z_A = z₀` (the outer electron), `t = z₁`, `z_M = z₁ + z₂` (the electron pair and its split),
`z_c = z₃`, `z_a = z₄ + z₆`, `z_b = z₅ + z₇` (the outer and inner photon, each a Pauli–Villars
pair) and
`U = z_A z_M + z_A z_c + z_A z_b + z_M z_c + z_M z_a + z_M z_b + z_c z_a + z_a z_b` (`xU`), the
slot data of the four electron lines are `αₖ = ãₖ/U`, `βₖ = b̃ₖ/U` with the quadratic polynomials
`ãₖ` (`xan`), `b̃ₖ` (`xbn`), and the contraction coefficients are `C_{kl} = C̃_{kl}/U` (`xCn`).
At `m = 1`, `e = 1`:

* `secondCoeff_crossedT1`: `c₂[T₁] = (Λ² - m_γ²)² (3/K) Ψ₁/U⁶`,
  `Ψ₁ = psiT1h(ã, b̃, U)` the explicit quartic of `psiT1h`;
* `secondCoeff_crossedT2`: `c₂[T₂] = -(Λ² - m_γ²)² (1/K) Ψ₂/U⁵`,
  `Ψ₂ = psiT2h(ã, b̃, C̃, U)` the explicit cubic of `psiT2h`;
* `secondCoeff_crossedT3`: `c₂[T₃] = 0`,

with `K = 16π⁴/(64 i)` (`QED.TwoLoop.UnitLGraphTrace.kConst`), for every `z` with `U ≠ 0`. The
`b̃ₖ` are affine in the split `t` and `Ψ₁`, `Ψ₂` are affine in the `b̃ₖ`, so both coefficients are
affine in the split. More precisely `T₁, T₂, T₃` vanish to first order at `u = 0`, so
`c₂[N(x, ·)] = c₂[T₁] + c₂[T₂] V(x)` (`secondCoeff_openNum_X`) and
`openZero .X P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴` (`openZero_X_eq`).

The second coefficients were checked against the finite-difference model of `openNum .X`
(`scripts/numerics/crossed_graph/target_check.py`, which also checks the exact identities
`A₂ = z_M Ψ₁(z_M/2)/(2U⁶)`, `A₁ = -z_M Ψ₂(z_M/2)/(2U⁵)` with the coefficients of the engine of
`scripts/numerics/two_loop_unit_integrals.py`, `integrand_parts('X', …)`).
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitXGraph

open Filter Topology
open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexPoint)
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikU symanzikV symanzikVector
  symanzikMatrix)
open Pl

/-! ### The parameters -/

section Params

variable (z : Fin 8 → ℝ)

/-- The outer electron `z_A = z₀`. -/
def xA : ℝ := z 0
/-- The split `t = z₁` of the electron pair. -/
def xt : ℝ := z 1
/-- The electron pair `z_M = z₁ + z₂`. -/
def xM : ℝ := z 1 + z 2
/-- The electron line `z_c = z₃`. -/
def xc : ℝ := z 3
/-- The outer photon pair `z_a = z₄ + z₆`. -/
def xa : ℝ := z 4 + z 6
/-- The inner photon pair `z_b = z₅ + z₇`. -/
def xb : ℝ := z 5 + z 7

/-- `U` in the group sums. -/
def gXU (A M c a b : ℝ) : ℝ := A * M + A * c + A * b + M * c + M * a + M * b + c * a + a * b

/-- `U = z_A z_M + z_A z_c + z_A z_b + z_M z_c + z_M z_a + z_M z_b + z_c z_a + z_a z_b`. -/
def xU : ℝ := gXU (xA z) (xM z) (xc z) (xa z) (xb z)

/-- The numerators `ãₖ = U αₖ` of the slot data. -/
def gXan (A M c a b : ℝ) : Fin 4 → ℝ :=
  ![A * M + A * b + M * b + a * b, -(A * c) + a * b, -(A * c) + a * b, M * c + M * a + c * a + a * b]

/-- The numerators `b̃ₖ = U βₖ` of the slot data (affine in the split `t`). -/
def gXbn (A t M c a b : ℝ) : Fin 4 → ℝ :=
  ![A * t + A * b + M * b + t * a + a * b, A * t + A * b + t * c + t * a + t * b + a * b,
    -(A * M - A * t + A * c + M * c + M * a + M * b - t * c - t * a - t * b + c * a),
    -(M * b) + t * c + t * b]

/-- The numerators `ãₖ` at the point `z`. -/
def xan : Fin 4 → ℝ := gXan (xA z) (xM z) (xc z) (xa z) (xb z)
/-- The numerators `b̃ₖ` at the point `z`. -/
def xbn : Fin 4 → ℝ := gXbn (xA z) (xt z) (xM z) (xc z) (xa z) (xb z)

theorem symanzikMatrix_crossed :
    symanzikMatrix crossedAlpha z =
      !![xA z + xM z + xa z, -(xA z + xa z); -(xA z + xa z), xA z + xc z + xa z + xb z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symanzikMatrix, Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, xA, xM, xc, xa, xb] <;> ring

theorem symanzikU_crossed : symanzikU crossedAlpha z = xU z := by
  rw [symanzikU, symanzikMatrix_crossed, Matrix.det_fin_two_of]
  simp only [xU, gXU]
  ring

theorem inv_symanzikMatrix_crossed (s r : Fin 2) :
    (symanzikMatrix crossedAlpha z)⁻¹ s r =
      (xU z)⁻¹ * !![xA z + xc z + xa z + xb z, xA z + xa z; xA z + xa z, xA z + xM z + xa z] s r := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', ← symanzikU, symanzikU_crossed, symanzikMatrix_crossed,
    Matrix.adjugate_fin_two_of, Matrix.smul_apply, smul_eq_mul]
  fin_cases s <;> fin_cases r <;> simp

end Params

/-! ### The slot data and the contraction coefficients -/

theorem xU_ne_zero_aux {z : Fin 8 → ℝ} (hU : xU z ≠ 0) :
    (xA z + xM z + xa z) * (xA z + xc z + xa z + xb z) - (xA z + xa z) ^ 2 ≠ 0 := by
  convert hU using 1
  simp only [xU, gXU]
  ring

/-- **The slot data**: `αₖ = aₖ + bₖ = ãₖ/U`. -/
theorem xslot_alpha {z : Fin 8 → ℝ} (hU : xU z ≠ 0) (k : Fin 4) :
    xslotA z k + xslotB z k = (xU z)⁻¹ * xan z k := by
  have hU' : (xA z + xM z + xa z) * (xA z + xc z + xa z + xb z) - (xA z + xa z) ^ 2 ≠ 0 :=
    xU_ne_zero_aux hU
  have e : xU z = (xA z + xM z + xa z) * (xA z + xc z + xa z + xb z) - (xA z + xa z) ^ 2 := by
    simp only [xU, gXU]; ring
  simp only [xslotA, xslotB, xsigP, xsigQ, inv_symanzikMatrix_crossed, xan, gXan, e]
  fin_cases k <;> simp [xA, xM, xc, xa, xb] at hU' ⊢ <;> field_simp <;> ring

/-- **The slot data**: `βₖ = bₖ = b̃ₖ/U`. -/
theorem xslot_beta {z : Fin 8 → ℝ} (hU : xU z ≠ 0) (k : Fin 4) :
    xslotB z k = (xU z)⁻¹ * xbn z k := by
  have hU' : (xA z + xM z + xa z) * (xA z + xc z + xa z + xb z) - (xA z + xa z) ^ 2 ≠ 0 :=
    xU_ne_zero_aux hU
  have e : xU z = (xA z + xM z + xa z) * (xA z + xc z + xa z + xb z) - (xA z + xa z) ^ 2 := by
    simp only [xU, gXU]; ring
  simp only [xslotB, xsigQ, inv_symanzikMatrix_crossed, xbn, gXbn, e]
  fin_cases k <;> simp [xA, xt, xM, xc, xa, xb] at hU' ⊢ <;> field_simp <;> ring

/-- The numerators `C̃_{kl} = U C_{kl}` of the contraction coefficients, in the order
`(01), (02), (03), (12), (13), (23)`. -/
def xCn (z : Fin 8 → ℝ) : Fin 6 → ℝ :=
  ![xA z + xa z, xA z + xa z, -xM z, xA z + xc z + xa z + xb z, xc z + xb z, xc z + xb z]

theorem crossedC_val (z : Fin 8 → ℝ) :
    crossedC (symanzikMatrix crossedAlpha z) 0 1 = (((xU z)⁻¹ * xCn z 0 : ℝ) : ℂ) ∧
    crossedC (symanzikMatrix crossedAlpha z) 0 2 = (((xU z)⁻¹ * xCn z 1 : ℝ) : ℂ) ∧
    crossedC (symanzikMatrix crossedAlpha z) 0 3 = (((xU z)⁻¹ * xCn z 2 : ℝ) : ℂ) ∧
    crossedC (symanzikMatrix crossedAlpha z) 1 2 = (((xU z)⁻¹ * xCn z 3 : ℝ) : ℂ) ∧
    crossedC (symanzikMatrix crossedAlpha z) 1 3 = (((xU z)⁻¹ * xCn z 4 : ℝ) : ℂ) ∧
    crossedC (symanzikMatrix crossedAlpha z) 2 3 = (((xU z)⁻¹ * xCn z 5 : ℝ) : ℂ) := by
  simp only [crossedC, contrC, Fin.sum_univ_two, inv_symanzikMatrix_crossed]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix,
      crossedLines, xCn] <;> ring

/-! ### The explicit polynomials -/

/-- **The quartic of `c₂[T₁]`**, homogeneous of degree `4` in the slot data and `u = U`. -/
def psiT1h (a0 a1 a2 a3 b0 b1 b2 b3 u : ℝ) : ℝ :=
  2 * a0 * a1 * a2 * a3 - a0 * a1 * a2 * u - 2 * a0 * a1 * a3 * b2 + a0 * a1 * b2 * u -
    a0 * a1 * b3 * u - a0 * a1 * u ^ 2 + 2 * a0 * a2 * a3 * b1 - a0 * a2 * a3 * u -
    a0 * a2 * b1 * u + a0 * a2 * b3 * u + a0 * a3 * b1 * u - a0 * a3 * b2 * u - a0 * b1 * u ^ 2 +
    a0 * b2 * u ^ 2 + a1 * a2 * b0 * u - a1 * a2 * b3 * u - a1 * a2 * u ^ 2 - a1 * a3 * b0 * u +
    a1 * a3 * b2 * u + a1 * b0 * u ^ 2 - a1 * b2 * u ^ 2 + a1 * b3 * u ^ 2 + a2 * a3 * b0 * u -
    a2 * a3 * b1 * u - a2 * a3 * u ^ 2 - a2 * b0 * u ^ 2 + a2 * b1 * u ^ 2 - a2 * b3 * u ^ 2 +
    2 * a2 * u ^ 3 - a3 * b1 * u ^ 2 + a3 * b2 * u ^ 2 - a3 * u ^ 3 - b0 * u ^ 3 + 2 * b1 * u ^ 3 -
    2 * b2 * u ^ 3 + b3 * u ^ 3

/-- **The cubic of `c₂[T₂]`**: `∑_{kl} C̃_{kl} ψ_{kl}` with the quadratics `ψ_{kl}` of the six
single contractions, homogeneous in the slot data and `u = U`. -/
def psiT2h (a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u : ℝ) : ℝ :=
  c01 * (a2 * a3 + a2 * b3 - 2 * a2 * u - a3 * b2 + a3 * u + 2 * b2 * u - b3 * u) +
    c02 * (a1 * a3 - a1 * b3 - a1 * u + a3 * b1 - 2 * a3 * u + 2 * b3 * u) +
    c03 * (4 * a1 * a2 - 4 * a1 * b2 - a1 * u + 4 * a2 * b1 - a2 * u) +
    c12 * (a3 * u + b0 * u - b3 * u) +
    c13 * (a0 * a2 - a0 * b2 + a2 * b0 - a2 * u - 2 * b0 * u) +
    c23 * (a0 * a1 + a0 * b1 - a1 * b0 + b0 * u - 2 * b1 * u)

/-- `Ψ₁` at the point `z`. -/
def xPsi1 (z : Fin 8 → ℝ) : ℝ :=
  psiT1h (xan z 0) (xan z 1) (xan z 2) (xan z 3) (xbn z 0) (xbn z 1) (xbn z 2) (xbn z 3) (xU z)

/-- `Ψ₂` at the point `z`. -/
def xPsi2 (z : Fin 8 → ℝ) : ℝ :=
  psiT2h (xan z 0) (xan z 1) (xan z 2) (xan z 3) (xbn z 0) (xbn z 1) (xbn z 2) (xbn z 3)
    (xCn z 0) (xCn z 1) (xCn z 2) (xCn z 3) (xCn z 4) (xCn z 5) (xU z)

/-! ### The jets of the three coefficients -/

/-- The jet of the slot numerator `k`. -/
noncomputable def xslotJ (z : Fin 8 → ℝ) (k : Fin 4) : PJ :=
  eJ ((xslotA z k : ℂ) + (xslotB z k : ℂ)) (xslotB z k : ℂ)

/-- The jet of the slash of the slot momentum `k`. -/
noncomputable def xslotS (z : Fin 8 → ℝ) (k : Fin 4) : PJ :=
  sJ ((xslotA z k : ℂ) + (xslotB z k : ℂ)) (xslotB z k : ℂ)

theorem hasJet2_xT1 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasJet2 (fun u => -lwPl (lQ0 P u) (lQ1 P u) (lR P u) 1 (bar (xE P z u 0) * xE P z u 1)
        (xE P z u 2) (xE P z u 3) -
      2 * bsPl (lQ0 P u) (lQ1 P u) (lR P u) (bar (xE P z u 0) * xE P z u 1) (xE P z u 2)
        (xE P z u 3) +
      2 * hgPl (lQ0 P u) (lQ1 P u) (lR P u) (xE P z u 1) (xE P z u 2) (xE P z u 3 * xS P z u 0))
      (xT1k PJ.s0 (xslotJ z 0) (xslotJ z 1) (xslotJ z 2) (xslotJ z 3) (xslotS z 0))
      (xT1k PJ.s1 (xslotJ z 0) (xslotJ z 1) (xslotJ z 2) (xslotJ z 3) (xslotS z 0))
      (xT1k PJ.s2 (xslotJ z 0) (xslotJ z 1) (xslotJ z 2) (xslotJ z 3) (xslotS z 0)) := by
  have e₀ := jet_xE hm z 0
  have e₁ := jet_xE hm z 1
  have e₂ := jet_xE hm z 2
  have e₃ := jet_xE hm z 3
  have s₀ := jet_xS hm z 0
  have h₁ := hasJet2_lwPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) (jet_lQ0 hm) (jet_lQ1 hm) (jet_lR hm)
    (HasPJ.const 1) (e₀.bar.mul e₁) e₂ e₃
  have h₂ := hasJet2_bsPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) (jet_lQ0 hm) (jet_lQ1 hm) (jet_lR hm)
    (e₀.bar.mul e₁) e₂ e₃
  have h₃ := hasJet2_hgPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) (jet_lQ0 hm) (jet_lQ1 hm) (jet_lR hm)
    e₁ e₂ (e₃.mul s₀)
  exact (h₁.neg.sub (h₂.const_mul 2)).add (h₃.const_mul 2)

/-! ### Homogeneity of the explicit polynomials -/

theorem psiT1h_smul (c a0 a1 a2 a3 b0 b1 b2 b3 u : ℝ) :
    psiT1h (c * a0) (c * a1) (c * a2) (c * a3) (c * b0) (c * b1) (c * b2) (c * b3) (c * u) =
      c ^ 4 * psiT1h a0 a1 a2 a3 b0 b1 b2 b3 u := by
  simp only [psiT1h]; ring

theorem psiT2h_smul (c a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u : ℝ) :
    psiT2h (c * a0) (c * a1) (c * a2) (c * a3) (c * b0) (c * b1) (c * b2) (c * b3) (c * c01)
        (c * c02) (c * c03) (c * c12) (c * c13) (c * c23) (c * u) =
      c ^ 3 * psiT2h a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u := by
  simp only [psiT2h]; ring

/-- `Ψ₁` dehomogenized: `Ψ₁(α, β, 1) = Ψ₁(ã, b̃, U)/U⁴`. -/
theorem psiT1h_slot {z : Fin 8 → ℝ} (hU : xU z ≠ 0) :
    psiT1h (xslotA z 0 + xslotB z 0) (xslotA z 1 + xslotB z 1) (xslotA z 2 + xslotB z 2)
        (xslotA z 3 + xslotB z 3) (xslotB z 0) (xslotB z 1) (xslotB z 2) (xslotB z 3) 1 =
      xPsi1 z / xU z ^ 4 := by
  have h := psiT1h_smul (xU z)⁻¹ (xan z 0) (xan z 1) (xan z 2) (xan z 3) (xbn z 0) (xbn z 1)
    (xbn z 2) (xbn z 3) (xU z)
  rw [inv_mul_cancel₀ hU] at h
  rw [xslot_alpha hU, xslot_alpha hU, xslot_alpha hU, xslot_alpha hU, xslot_beta hU,
    xslot_beta hU, xslot_beta hU, xslot_beta hU, h, xPsi1]
  field_simp

/-- `Ψ₂` dehomogenized: `Ψ₂(α, β, C, 1) = Ψ₂(ã, b̃, C̃, U)/U³`. -/
theorem psiT2h_slot {z : Fin 8 → ℝ} (hU : xU z ≠ 0) :
    psiT2h (xslotA z 0 + xslotB z 0) (xslotA z 1 + xslotB z 1) (xslotA z 2 + xslotB z 2)
        (xslotA z 3 + xslotB z 3) (xslotB z 0) (xslotB z 1) (xslotB z 2) (xslotB z 3)
        ((xU z)⁻¹ * xCn z 0) ((xU z)⁻¹ * xCn z 1) ((xU z)⁻¹ * xCn z 2) ((xU z)⁻¹ * xCn z 3)
        ((xU z)⁻¹ * xCn z 4) ((xU z)⁻¹ * xCn z 5) 1 =
      xPsi2 z / xU z ^ 3 := by
  have h := psiT2h_smul (xU z)⁻¹ (xan z 0) (xan z 1) (xan z 2) (xan z 3) (xbn z 0) (xbn z 1)
    (xbn z 2) (xbn z 3) (xCn z 0) (xCn z 1) (xCn z 2) (xCn z 3) (xCn z 4) (xCn z 5) (xU z)
  rw [inv_mul_cancel₀ hU] at h
  rw [xslot_alpha hU, xslot_alpha hU, xslot_alpha hU, xslot_alpha hU, xslot_beta hU,
    xslot_beta hU, xslot_beta hU, xslot_beta hU, h, xPsi2]
  field_simp

/-! ### The second-order coefficient of `T₁` -/

theorem xT1_slot (z : Fin 8 → ℝ) :
    xT1k PJ.s2 (xslotJ z 0) (xslotJ z 1) (xslotJ z 2) (xslotJ z 3) (xslotS z 0) =
      512 * ((psiT1h (xslotA z 0 + xslotB z 0) (xslotA z 1 + xslotB z 1)
        (xslotA z 2 + xslotB z 2) (xslotA z 3 + xslotB z 3) (xslotB z 0) (xslotB z 1)
        (xslotB z 2) (xslotB z 3) 1 : ℝ) : ℂ) := by
  simp only [xslotJ, xslotS, xT1_s2, psiT1h]
  push_cast
  ring

/-- **The jet of `T₁`**: `T₁(u) = c₂[T₁] u² + o(u²)`, `c₂[T₁] = (Λ² - m_γ²)² (3/K) Ψ₁/U⁶`. -/
theorem hasJet2_crossedT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : xU z ≠ 0) :
    HasJet2 (crossedT1 P z) 0 0 (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (3 / kConst) *
      ((xPsi1 z / xU z ^ 6 : ℝ) : ℂ)) := by
  have h := ((hasJet2_xT1 hm z).const_mul 6).const_mul
    (ladderK P * ((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => crossedT1_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp only [xslotJ, xslotS, xT1_s0, mul_zero]
  · simp only [xslotJ, xslotS, xT1_s1, mul_zero]
  rw [xT1_slot, psiT1h_slot hU, ladderK_eq he, symanzikU_crossed, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (xU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₁`**: `c₂[T₁] = (Λ² - m_γ²)² (3/K) Ψ₁/U⁶`. -/
theorem secondCoeff_crossedT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : xU z ≠ 0) :
    secondCoeff (crossedT1 P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (3 / kConst) *
      ((xPsi1 z / xU z ^ 6 : ℝ) : ℂ) :=
  (hasJet2_crossedT1 hm he hU).secondCoeff_eq

/-! ### The second-order coefficient of `T₂` -/

theorem xT2_slot (z : Fin 8 → ℝ) :
    crossedC (symanzikMatrix crossedAlpha z) 0 1 * x01k PJ.s2 (xslotJ z 2) (xslotJ z 3) +
        crossedC (symanzikMatrix crossedAlpha z) 0 2 * x02k PJ.s2 (xslotS z 1) (xslotJ z 3) +
        crossedC (symanzikMatrix crossedAlpha z) 0 3 * x03k PJ.s2 (xslotJ z 1) (xslotJ z 2) +
        crossedC (symanzikMatrix crossedAlpha z) 1 2 *
          x12k PJ.s2 (xslotJ z 0) (xslotJ z 3) (xslotS z 0) +
        crossedC (symanzikMatrix crossedAlpha z) 1 3 *
          x13k PJ.s2 (xslotJ z 0) (xslotS z 0) (xslotS z 2) +
        crossedC (symanzikMatrix crossedAlpha z) 2 3 *
          x23k PJ.s2 (xslotJ z 0) (xslotJ z 1) (xslotS z 0) =
      -1024 * ((psiT2h (xslotA z 0 + xslotB z 0) (xslotA z 1 + xslotB z 1)
        (xslotA z 2 + xslotB z 2) (xslotA z 3 + xslotB z 3) (xslotB z 0) (xslotB z 1)
        (xslotB z 2) (xslotB z 3) ((xU z)⁻¹ * xCn z 0) ((xU z)⁻¹ * xCn z 1)
        ((xU z)⁻¹ * xCn z 2) ((xU z)⁻¹ * xCn z 3) ((xU z)⁻¹ * xCn z 4) ((xU z)⁻¹ * xCn z 5)
        1 : ℝ) : ℂ) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := crossedC_val z
  rw [h01, h02, h03, h12, h13, h23]
  simp only [xslotJ, xslotS, x01_s2, x02_s2, x03_s2, x12_s2, x13_s2, x23_s2, psiT2h]
  push_cast
  ring

/-- **The jet of `T₂`**: `T₂(u) = c₂[T₂] u² + o(u²)`, `c₂[T₂] = -(Λ² - m_γ²)² (1/K) Ψ₂/U⁵`. -/
theorem hasJet2_crossedT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : xU z ≠ 0) :
    HasJet2 (crossedT2 P z) 0 0 (-(((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (1 / kConst) *
      ((xPsi2 z / xU z ^ 5 : ℝ) : ℂ))) := by
  have j0 := jet_lQ0 hm
  have j1 := jet_lQ1 hm
  have jr := jet_lR hm
  have h01 : HasJet2 _ (x01k PJ.s0 (xslotJ z 2) (xslotJ z 3)) (x01k PJ.s1 (xslotJ z 2) (xslotJ z 3))
      (x01k PJ.s2 (xslotJ z 2) (xslotJ z 3)) :=
    (hasJet2_lwPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const 1)
      (HasPJ.const two₂) (jet_xE hm z 2) (jet_xE hm z 3)).neg.sub
      ((hasJet2_bsPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const two₂)
        (jet_xE hm z 2) (jet_xE hm z 3)).const_mul 2)
  have h02 : HasJet2 _ (x02k PJ.s0 (xslotS z 1) (xslotJ z 3)) (x02k PJ.s1 (xslotS z 1) (xslotJ z 3))
      (x02k PJ.s2 (xslotS z 1) (xslotJ z 3)) :=
    ((hasJet2_om0Pl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (jet_xE hm z 3)
      (HasPJ.const 1)).const_mul (-16)).sub
      ((hasJet2_omGPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (jet_xS hm z 1)
        (jet_xE hm z 3)).const_mul 4)
  have h03 : HasJet2 _ (x03k PJ.s0 (xslotJ z 1) (xslotJ z 2)) (x03k PJ.s1 (xslotJ z 1) (xslotJ z 2))
      (x03k PJ.s2 (xslotJ z 1) (xslotJ z 2)) :=
    (((hasJet2_hgPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (jet_xE hm z 1) (jet_xE hm z 2)
      (HasPJ.const 1)).const_mul 4).add
      ((hasJet2_omGPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (jet_xE hm z 1)
        (jet_xE hm z 2)).const_mul 16)).sub
      (hasJet2_f3Pl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (jet_xE hm z 1) (jet_xE hm z 2))
  have h12 : HasJet2 _ (x12k PJ.s0 (xslotJ z 0) (xslotJ z 3) (xslotS z 0))
      (x12k PJ.s1 (xslotJ z 0) (xslotJ z 3) (xslotS z 0))
      (x12k PJ.s2 (xslotJ z 0) (xslotJ z 3) (xslotS z 0)) :=
    ((hasJet2_lwPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const 1)
      ((jet_xE hm z 0).bar.mul (HasPJ.const two₂)) (HasPJ.const 1) (jet_xE hm z 3)).neg.sub
      ((hasJet2_bsPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr
        ((jet_xE hm z 0).bar.mul (HasPJ.const two₂)) (HasPJ.const 1)
        (jet_xE hm z 3)).const_mul 2)).add
      ((hasJet2_hgPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const two₂)
        (HasPJ.const 1) ((jet_xE hm z 3).mul (jet_xS hm z 0))).const_mul 2)
  have h13 : HasJet2 _ (x13k PJ.s0 (xslotJ z 0) (xslotS z 0) (xslotS z 2))
      (x13k PJ.s1 (xslotJ z 0) (xslotS z 0) (xslotS z 2))
      (x13k PJ.s2 (xslotJ z 0) (xslotS z 0) (xslotS z 2)) :=
    (((hasJet2_om0Pl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const 1)
      (jet_xE hm z 0)).const_mul (-16)).sub
      ((hasJet2_omGPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (jet_xS hm z 2)
        (HasPJ.const 1)).const_mul 4)).add
      ((hasJet2_om0Pl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (jet_xS hm z 2)
        (jet_xS hm z 0)).const_mul 8)
  have h23 : HasJet2 _ (x23k PJ.s0 (xslotJ z 0) (xslotJ z 1) (xslotS z 0))
      (x23k PJ.s1 (xslotJ z 0) (xslotJ z 1) (xslotS z 0))
      (x23k PJ.s2 (xslotJ z 0) (xslotJ z 1) (xslotS z 0)) :=
    ((hasJet2_lwPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const 1)
      ((jet_xE hm z 0).bar.mul (jet_xE hm z 1)) (HasPJ.const two₂) (HasPJ.const 1)).neg.sub
      ((hasJet2_bsPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr
        ((jet_xE hm z 0).bar.mul (jet_xE hm z 1)) (HasPJ.const two₂)
        (HasPJ.const 1)).const_mul 2)).add
      ((hasJet2_hgPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (jet_xE hm z 1)
        (HasPJ.const two₂) (jet_xS hm z 0)).const_mul 2)
  have h := ((((((h01.const_mul (crossedC (symanzikMatrix crossedAlpha z) 0 1)).add
    (h02.const_mul (crossedC (symanzikMatrix crossedAlpha z) 0 2))).add
    (h03.const_mul (crossedC (symanzikMatrix crossedAlpha z) 0 3))).add
    (h12.const_mul (crossedC (symanzikMatrix crossedAlpha z) 1 2))).add
    (h13.const_mul (crossedC (symanzikMatrix crossedAlpha z) 1 3))).add
    (h23.const_mul (crossedC (symanzikMatrix crossedAlpha z) 2 3))).const_mul
    (ladderK P * ((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹)
  refine h.of_eq (fun u => ?_) ?_ ?_ ?_
  · rw [crossedT2_planar, hm, Complex.ofReal_one]
    ring
  · simp only [xslotJ, xslotS, x01_s0, x02_s0, x03_s0, x12_s0, x13_s0, x23_s0, mul_zero,
      add_zero]
  · simp only [xslotJ, xslotS, x01_s1, x02_s1, x03_s1, x12_s1, x13_s1, x23_s1, mul_zero,
      add_zero]
  rw [xT2_slot, psiT2h_slot hU, ladderK_eq he, symanzikU_crossed, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (xU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₂`**: `c₂[T₂] = -(Λ² - m_γ²)² (1/K) Ψ₂/U⁵`. -/
theorem secondCoeff_crossedT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : xU z ≠ 0) :
    secondCoeff (crossedT2 P z) = -(((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (1 / kConst) *
      ((xPsi2 z / xU z ^ 5 : ℝ) : ℂ)) :=
  (hasJet2_crossedT2 hm he hU).secondCoeff_eq

/-! ### `T₃` -/

/-- **The jet of `T₃` vanishes**: `T₃(u) = o(u²)`. -/
theorem hasJet2_crossedT3 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasJet2 (crossedT3 P z) 0 0 0 := by
  have j0 := jet_lQ0 hm
  have j1 := jet_lQ1 hm
  have jr := jet_lR hm
  have d1 : HasJet2 _ (xd1k PJ.s0) (xd1k PJ.s1) (xd1k PJ.s2) :=
    (hasJet2_lwPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const 1)
      (HasPJ.const two₂) (HasPJ.const two₂) (HasPJ.const 1)).neg.sub
      ((hasJet2_bsPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const two₂)
        (HasPJ.const two₂) (HasPJ.const 1)).const_mul 2)
  have d2 : HasJet2 _ (xd2k PJ.s0) (xd2k PJ.s1) (xd2k PJ.s2) :=
    (hasJet2_omGPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const 1)
      (HasPJ.const 1)).const_mul 8
  have d3 : HasJet2 _ (xd3k PJ.s0) (xd3k PJ.s1) (xd3k PJ.s2) :=
    (((hasJet2_hgPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const two₂)
      (HasPJ.const 1) (HasPJ.const 1)).const_mul 4).add
      ((hasJet2_omGPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const two₂)
        (HasPJ.const 1)).const_mul 16)).sub
      (hasJet2_f3Pl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) j0 j1 jr (HasPJ.const two₂)
        (HasPJ.const 1))
  have h := ((((d1.const_mul (crossedC (symanzikMatrix crossedAlpha z) 0 1 *
      crossedC (symanzikMatrix crossedAlpha z) 2 3)).add
    (d2.const_mul (crossedC (symanzikMatrix crossedAlpha z) 0 2 *
      crossedC (symanzikMatrix crossedAlpha z) 1 3))).add
    (d3.const_mul (crossedC (symanzikMatrix crossedAlpha z) 0 3 *
      crossedC (symanzikMatrix crossedAlpha z) 1 2))).const_mul (1 / 4)).const_mul
    (ladderK P * ((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => crossedT3_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · rw [xd1_eq _ (Or.inl rfl), xd2_eq _ (Or.inl rfl), xd3_eq _ (Or.inl rfl)]; ring
  · rw [xd1_eq _ (Or.inr (Or.inl rfl)), xd2_eq _ (Or.inr (Or.inl rfl)),
      xd3_eq _ (Or.inr (Or.inl rfl))]; ring
  · rw [xd1_eq _ (Or.inr (Or.inr rfl)), xd2_eq _ (Or.inr (Or.inr rfl)),
      xd3_eq _ (Or.inr (Or.inr rfl))]; ring

/-! ### The second-order coefficient of the projected numerator -/

@[fun_prop] theorem continuous_pvMomentaE_X (r : Fin 4 → ℝ) (i : Fin 8) (μ : Fin 4) :
    Continuous fun p' : Fin 4 → ℝ => pvMomentaE .X r p' i μ := by
  fin_cases i <;>
    simp [pvMomentaE, extMomenta, QED.Integration.TwoLoop.classLXMomenta,
      QED.Integration.TwoLoop.pvLines] <;> fun_prop

theorem continuous_crossedV (r : Fin 4 → ℝ) (M z : Fin 8 → ℝ) :
    Continuous fun p' : Fin 4 → ℝ => symanzikV crossedAlpha (pvMomentaE .X r p') M z := by
  unfold symanzikV symanzikVector QED.Minkowski.dot
  fun_prop

/-- The second Symanzik function along the curve tends to its value at `q = 0`. -/
theorem tendsto_crossedV (P : Params) (x : Fin 7 → ℝ) :
    Tendsto (fun u => ((symanzikV crossedAlpha (crossedMom P u) (pvMasses P) (simplexPoint x) : ℝ) :
        ℂ))
      (𝓝 0) (𝓝 ((openV .X P x : ℝ) : ℂ)) := by
  have h := ((continuous_crossedV (restMomentum P.m) (pvMasses P) (simplexPoint x)).tendsto
    (restMomentum P.m)).comp (tendsto_curveMomentum P.m)
  exact (Complex.continuous_ofReal.tendsto _).comp h

/-- **The jet of the projected crossed numerator**: `N(x, u) = c₂ u² + o(u²)` with
`c₂ = c₂[T₁] + c₂[T₂] V(x)`. -/
theorem hasJet2_openNum_X {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : xU (simplexPoint x) ≠ 0) :
    HasJet2 (openNum .X P x) 0 0
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (3 / kConst) *
          ((xPsi1 (simplexPoint x) / xU (simplexPoint x) ^ 6 : ℝ) : ℂ) +
        -(((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (1 / kConst) *
          ((xPsi2 (simplexPoint x) / xU (simplexPoint x) ^ 5 : ℝ) : ℂ)) *
          ((openV .X P x : ℝ) : ℂ)) := by
  have hV := tendsto_crossedV P x
  have h := ((hasJet2_crossedT1 hm he hU).add (hasJet2_mul_tendsto
      (hasJet2_crossedT2 hm he hU) hV)).add
    (hasJet2_mul_tendsto (hasJet2_crossedT3 hm (simplexPoint x)) (hV.pow 2))
  exact h.of_eq (fun u => openNum_X_eq_T P x u) (by ring) (by ring) (by ring)

/-- **The second-order coefficient of the projected crossed numerator.** -/
theorem secondCoeff_openNum_X {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : xU (simplexPoint x) ≠ 0) :
    secondCoeff (openNum .X P x) =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (3 / kConst) *
          ((xPsi1 (simplexPoint x) / xU (simplexPoint x) ^ 6 : ℝ) : ℂ) +
        -(((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (1 / kConst) *
          ((xPsi2 (simplexPoint x) / xU (simplexPoint x) ^ 5 : ℝ) : ℂ)) *
          ((openV .X P x : ℝ) : ℂ) :=
  (hasJet2_openNum_X hm he x hU).secondCoeff_eq

/-- Almost every point of the simplex has `U ≠ 0`. -/
theorem ae_xU_ne_zero : ∀ᵐ x ∂(MeasureTheory.volume.restrict
    (QED.Integration.Feynman.simplexSet 7)),
    xU (simplexPoint x) ≠ 0 := by
  have hspan :
      ∃ i j, crossedAlpha i 0 * crossedAlpha j 1 - crossedAlpha i 1 * crossedAlpha j 0 ≠ 0 :=
    ⟨1, 3, by simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix]⟩
  filter_upwards [QED.Integration.TwoLoop.ae_posDef crossedAlpha (by norm_num) hspan] with x hx
  rw [← symanzikU_crossed]
  exact hx.2.det_pos.ne'

/-- **The crossed-ladder class value with the explicit integrand**: at `m = 1`, `e = 1`,
`openZero .X P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴`. -/
theorem openZero_X_eq {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .X P = ∫ x in QED.Integration.Feynman.simplexSet 7,
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (3 / kConst) *
          ((xPsi1 (simplexPoint x) / xU (simplexPoint x) ^ 6 : ℝ) : ℂ) +
        -(((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (1 / kConst) *
          ((xPsi2 (simplexPoint x) / xU (simplexPoint x) ^ 5 : ℝ) : ℂ)) *
          ((openV .X P x : ℝ) : ℂ)) /
        ((openV .X P x : ℝ) : ℂ) ^ 4 := by
  unfold openZero
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_xU_ne_zero] with x hx
  rw [secondCoeff_openNum_X hm he x hx]

end QED.TwoLoop.UnitXGraph

end
