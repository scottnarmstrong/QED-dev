/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L3
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 4

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_56_eq`, `QED.ThreeLoopD.tendsto_i8L4RG4` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽56⁾` at `ξ = 0`. -/
noncomputable def i8L4S56 (x : ℝ) : ℝ :=
    17 / 4 - Real.log x ^ 2 / 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽56⁾`. -/
noncomputable def i8L4Q56_0 (x r_000m r_00m r_00m0m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -1 - r_0mm - 23 / 16 * x - 3 / 8 * x ^ 4 + x ^ 3 / 16 + x ^ 5 / 16 + 3 / 2 * x ^ 2 +
      r_00m * x ^ 2 / 2 + r_0m * x ^ 3 / 2 + r_0m * x ^ 5 / 2 + r_m * x ^ 5 / 2 -
      r_000m * x ^ 2 - r_0mm * x ^ 4 - 4 * r_00m0m * x ^ 2 + 2 * r_0m * x + 2 * r_0mm * x ^ 2 +
      3 * r_m * x - 7 / 2 * r_m * x ^ 3 - 5 / 2 * r_0m * x ^ 2 - r_m * x ^ 2 / 2 -
      r_0m * x ^ 6 / 4 - r_m * x ^ 6 / 8 + 5 / 8 * r_m * x ^ 4 + r_0m * r_m * x ^ 3 / 2 +
      r_0m * r_m * x ^ 7 / 2 - r_0m * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽56⁾`. -/
noncomputable def i8L4Q56_1 (x _r_000m r_00m _r_00m0m r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    1 / 2 - x ^ 2 - 2 * r_0mm - 3 / 8 * x ^ 3 - x ^ 5 / 8 + 3 / 4 * x ^ 4 + r_00m * x ^ 2 +
      r_m * x ^ 3 + r_0m * x ^ 6 / 2 - r_0m * x ^ 5 - r_m * x ^ 5 - 8 * r_00mm * x ^ 2 +
      2 * r_0m * x + 2 * r_0mm * x ^ 4 + 2 * r_m * x + 2 * r_m * x ^ 2 + 2 * r_0m ^ 2 * x ^ 5 +
      3 * r_0m * x ^ 3 - r_0m * x ^ 2 / 2 - r_0m * x ^ 4 / 2 - r_m * x ^ 4 / 4 +
      r_m * x ^ 6 / 4 + r_0m * r_m * x ^ 3 - r_0m * r_m * x ^ 7

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽56⁾`. -/
noncomputable def i8L4Q56_2 (_x _r_000m _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽56⁾`. -/
noncomputable def i8L4Q56_3 (_x _r_000m _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽56⁾`. -/
noncomputable def i8L4Q56_4 (_x _r_000m _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_56_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s56 x = i8L4S56 x + x * (i8L4Q56_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q56_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q56_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q56_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q56_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s56 i8Psi4s56N0 i8Psi4s56N1 i8Psi4s56N2 i8Psi4s56N3 i8Psi4s56N4 i8Psi4s56W
  simp only [hpl_zero, i13hw_00, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m0m hx, i13hw_0m0m0 hx,
    i13hw_m0 hx, i13hw_m00m hx, i13hw_m0m hx, i13hw_m0m0 hx, i8hw_0m00m hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_00m0m h0, i13hpl_rho_00mm h0,
    i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S56 i8L4Q56_0 i8L4Q56_1 i8L4Q56_2 i8L4Q56_3 i8L4Q56_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽56⁾`. -/
noncomputable def i8L4R56 (x : ℝ) : ℝ :=
  x * (i8L4Q56_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q56_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q56_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q56_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q56_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R56 : Tendsto i8L4R56 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q56_0 (v 0) (v 6) (v 18) (v 20) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q56_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q56_1 (v 0) (v 6) (v 18) (v 20) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q56_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q56_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q56_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R56
  unfold i8L4Q56_2 i8L4Q56_3 i8L4Q56_4
  ring

/-- The singular part of `Ψ₄⁽57⁾` at `ξ = 0`. -/
noncomputable def i8L4S57 (x : ℝ) : ℝ :=
    11 / 8 - Real.log x ^ 2 / 4

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽57⁾`. -/
noncomputable def i8L4Q57_0 (x r_000mm r_00m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -1 / 4 + r_0mm / 2 - 5 / 16 * x ^ 3 - 3 / 4 * x - x ^ 5 / 16 + x ^ 4 / 4 + 7 / 8 * x ^ 2 +
      r_0mm * x ^ 2 + r_0mm * x ^ 4 / 2 - r_m * x ^ 3 - 4 * r_000mm * x ^ 2 -
      5 / 8 * r_m * x ^ 2 - 3 / 4 * r_0m * x ^ 2 - r_00m * x ^ 2 / 2 - r_m * x ^ 5 / 2 -
      r_m ^ 2 * x ^ 7 / 4 + r_m * x ^ 6 / 4 + r_m ^ 2 * x ^ 3 / 4 + 3 / 2 * r_m * x +
      3 / 8 * r_m * x ^ 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽57⁾`. -/
noncomputable def i8L4Q57_1 (x _r_000mm _r_00m r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    1 / 2 + r_0mm - x ^ 4 / 4 - x / 16 + x ^ 5 / 16 + r_m * x + r_m * x ^ 2 + r_0m * x ^ 2 / 2 +
      r_m * x ^ 5 / 2 - r_0mm * x ^ 4 + 4 * r_00mm * x ^ 2 - r_m * x ^ 3 / 2 -
      r_m ^ 2 * x ^ 5 / 2 - r_m * x ^ 6 / 4 + r_m * x ^ 4 / 4 + r_m ^ 2 * x ^ 3 / 4 +
      r_m ^ 2 * x ^ 7 / 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽57⁾`. -/
noncomputable def i8L4Q57_2 (_x _r_000mm _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽57⁾`. -/
noncomputable def i8L4Q57_3 (_x _r_000mm _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽57⁾`. -/
noncomputable def i8L4Q57_4 (_x _r_000mm _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_57_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s57 x = i8L4S57 x + x * (i8L4Q57_0 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q57_1 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q57_2 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q57_3 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q57_4 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s57 i8Psi4s57N0 i8Psi4s57N1 i8Psi4s57N2 i8Psi4s57N3 i8Psi4s57N4 i8Psi4s57W
  simp only [hpl_zero, i13hw_00, i13hw_00mm0 hx, i13hw_0m0 hx, i13hw_0m0m hx, i13hw_0mm0 hx,
    i13hw_m0 hx, i13hw_m0m hx, i13hw_mm hx, i13hw_mm0 hx]
  simp only [i13hpl_rho_000mm h0, i13hpl_rho_00m h0, i13hpl_rho_00mm h0, i13hpl_rho_0m h0,
    i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S57 i8L4Q57_0 i8L4Q57_1 i8L4Q57_2 i8L4Q57_3 i8L4Q57_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽57⁾`. -/
noncomputable def i8L4R57 (x : ℝ) : ℝ :=
  x * (i8L4Q57_0 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x) + Real.log x * i8L4Q57_1 x (i13Rho [zero, zero, zero, negOne, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne]
    x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q57_2 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q57_3 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q57_4 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R57 : Tendsto i8L4R57 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q57_0 (v 0) (v 8) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q57_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q57_1 (v 0) (v 8) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q57_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q57_0 x (i13Rho [zero, zero,
    zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q57_1 x (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R57
  unfold i8L4Q57_2 i8L4Q57_3 i8L4Q57_4
  ring

/-- The singular part of `Ψ₄⁽58⁾` at `ξ = 0`. -/
noncomputable def i8L4S58 (x : ℝ) : ℝ :=
    (-1 - Real.log x + 3 / 16 * x - x * Real.log x ^ 2 / 16) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽58⁾`. -/
noncomputable def i8L4Q58_0 (x r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    33 / 16 - 3 / 16 * r_m - 3 / 16 * x ^ 2 - r_00m / 4 - r_0m / 4 - x / 8 + x ^ 3 / 16 +
      2 * r_0000m * x ^ 2 - 3 / 16 * r_m * x ^ 4 - r_00m * x ^ 4 / 4 + r_0m * x ^ 4 / 4 +
      3 / 8 * r_m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽58⁾`. -/
noncomputable def i8L4Q58_1 (x _r_0000m r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -15 / 8 - r_00m / 2 - r_0m / 4 - r_m / 8 - x ^ 3 / 16 + x / 16 + 3 / 8 * x ^ 2 +
      r_00m * x ^ 4 / 2 - 2 * r_000m * x ^ 2 - r_0m * x ^ 4 / 4 + r_m * x ^ 4 / 8

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽58⁾`. -/
noncomputable def i8L4Q58_2 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽58⁾`. -/
noncomputable def i8L4Q58_3 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽58⁾`. -/
noncomputable def i8L4Q58_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_58_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s58 x = i8L4S58 x + x * (i8L4Q58_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [negOne] x) + Real.log x * i8L4Q58_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q58_2 x (i13Rho [zero, zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q58_3 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q58_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s58 i8Psi4s58N0 i8Psi4s58N1 i8Psi4s58N2 i8Psi4s58N3 i8Psi4s58N4 i8Psi4s58W
  simp only [hpl_zero, i13hw_00, i13hw_000m0 hx, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_m0 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S58 i8L4Q58_0 i8L4Q58_1 i8L4Q58_2 i8L4Q58_3 i8L4Q58_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽58⁾`. -/
noncomputable def i8L4R58 (x : ℝ) : ℝ :=
  x * (i8L4Q58_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q58_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q58_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q58_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q58_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R58 : Tendsto i8L4R58 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q58_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q58_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q58_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q58_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q58_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q58_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R58
  unfold i8L4Q58_2 i8L4Q58_3 i8L4Q58_4
  ring

/-- The singular part of `Ψ₄⁽59⁾` at `ξ = 0`. -/
noncomputable def i8L4S59 (x : ℝ) : ℝ :=
    8 - 8 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽59⁾`. -/
noncomputable def i8L4Q59_0 (x r_01 r_1 : ℝ) : ℝ :=
    4 - 2 * x ^ 3 + 2 * x - 12 * r_1 * x ^ 2 - 4 * r_1 * x ^ 4 + 8 * r_01 * x ^ 2 + 8 * r_1 * x +
      8 * r_1 * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽59⁾`. -/
noncomputable def i8L4Q59_1 (_x _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽59⁾`. -/
noncomputable def i8L4Q59_2 (_x _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽59⁾`. -/
noncomputable def i8L4Q59_3 (_x _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽59⁾`. -/
noncomputable def i8L4Q59_4 (_x _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_59_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s59 x = i8L4S59 x + x * (i8L4Q59_0 x (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q59_1 x (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q59_2 x (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q59_3 x (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q59_4 x (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s59 i8Psi4s59N0 i8Psi4s59N1 i8Psi4s59N2 i8Psi4s59N3 i8Psi4s59N4 i8Psi4s59W
  simp only [hpl_zero]
  simp only [i13hpl_rho_01 h0, i13hpl_rho_1 h0]
  unfold i8L4S59 i8L4Q59_0 i8L4Q59_1 i8L4Q59_2 i8L4Q59_3 i8L4Q59_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽59⁾`. -/
noncomputable def i8L4R59 (x : ℝ) : ℝ :=
  x * (i8L4Q59_0 x (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q59_1 x (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q59_2 x (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q59_3 x (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q59_4 x (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R59 : Tendsto i8L4R59 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q59_0 (v 0) (v 27) (v 65)) (by
      unfold i8L4Q59_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q59_0 x (i13Rho [zero, one] x)
    (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R59
  unfold i8L4Q59_1 i8L4Q59_2 i8L4Q59_3 i8L4Q59_4
  ring

/-- The singular part of `Ψ₄⁽60⁾` at `ξ = 0`. -/
noncomputable def i8L4S60 (x : ℝ) : ℝ :=
    -6 + 4 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽60⁾`. -/
noncomputable def i8L4Q60_0 (x r_01 r_01m r_0m r_0m1 r_1 r_m : ℝ) : ℝ :=
    x ^ 3 - x / 2 - x ^ 5 / 2 + r_m * x ^ 4 + r_m * x ^ 6 - r_1 * x ^ 4 - r_1 * x ^ 6 -
      8 * r_01m * x ^ 2 - 8 * r_0m1 * x ^ 2 - 4 * r_1 * x - 4 * r_m * x - 2 * r_01 * x ^ 2 -
      2 * r_m * x ^ 2 + 2 * r_0m * x ^ 2 + 2 * r_1 * x ^ 2 + 2 * r_1 * x ^ 3 + 2 * r_1 * x ^ 5 +
      2 * r_m * x ^ 3 + 2 * r_m * x ^ 5 - 2 * r_1 * r_m * x ^ 3 + 2 * r_1 * r_m * x ^ 7

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽60⁾`. -/
noncomputable def i8L4Q60_1 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽60⁾`. -/
noncomputable def i8L4Q60_2 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽60⁾`. -/
noncomputable def i8L4Q60_3 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽60⁾`. -/
noncomputable def i8L4Q60_4 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

theorem i8L4_60_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s60 x = i8L4S60 x + x * (i8L4Q60_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      + Real.log x * i8L4Q60_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q60_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q60_3 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q60_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s60 i8Psi4s60N0 i8Psi4s60N1 i8Psi4s60N2 i8Psi4s60N3 i8Psi4s60N4 i8Psi4s60W
  simp only [hpl_zero, i13hw_1m hx]
  simp only [i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1
    h0, i13hpl_rho_m h0]
  unfold i8L4S60 i8L4Q60_0 i8L4Q60_1 i8L4Q60_2 i8L4Q60_3 i8L4Q60_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽60⁾`. -/
noncomputable def i8L4R60 (x : ℝ) : ℝ :=
  x * (i8L4Q60_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q60_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q60_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q60_3 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q60_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R60 : Tendsto i8L4R60 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q60_0 (v 0) (v 27) (v 36) (v 43) (v 49) (v 65) (v 66)) (by
      unfold i8L4Q60_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q60_0 x (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R60
  unfold i8L4Q60_1 i8L4Q60_2 i8L4Q60_3 i8L4Q60_4
  ring

/-- The singular part of `Ψ₄⁽61⁾` at `ξ = 0`. -/
noncomputable def i8L4S61 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽61⁾`. -/
noncomputable def i8L4Q61_0 (x r_01 r_01m r_01mm r_0m r_0m1 r_0m1m r_0mm r_0mm1 r_1 r_m : ℝ) : ℝ :=
    -2 + x / 2 - 2 * x ^ 2 - x ^ 4 / 4 - x ^ 7 / 8 + x ^ 6 / 4 + x ^ 5 / 8 + 5 / 4 * x ^ 3 +
      r_1 * x ^ 7 + r_m ^ 2 * x ^ 5 + r_1 * x ^ 2 / 2 + r_m * x ^ 8 / 2 - r_m * x ^ 6 -
      r_m ^ 2 * x ^ 6 - r_m ^ 2 * x ^ 8 - 4 * r_0m * x ^ 2 - 2 * r_01 * x ^ 2 -
      2 * r_0mm * x ^ 2 + 2 * r_01m * x ^ 2 + 2 * r_0m1 * x ^ 2 + 2 * r_1 * x ^ 5 +
      2 * r_m ^ 2 * x ^ 4 + 5 * r_m * x ^ 2 + 8 * r_01mm * x ^ 2 + 8 * r_0m1m * x ^ 2 +
      8 * r_0mm1 * x ^ 2 - 9 / 2 * r_m * x ^ 4 - 7 / 4 * r_1 * x ^ 4 - 3 / 2 * r_1 * x ^ 6 -
      r_m ^ 2 * x ^ 7 / 2 - r_m ^ 2 * x ^ 9 / 2 - r_1 * x ^ 8 / 4 + r_1 * r_m * x ^ 7 +
      r_1 * r_m * x ^ 9 + r_1 * r_m ^ 2 * x ^ 6 - r_1 * r_m ^ 2 * x ^ 10 - 2 * r_1 * r_m * x ^ 5 -
      2 * r_1 * r_m * x ^ 6 - 2 * r_1 * r_m * x ^ 8 + 4 * r_1 * r_m * x ^ 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽61⁾`. -/
noncomputable def i8L4Q61_1 (_x _r_01 _r_01m _r_01mm _r_0m _r_0m1 _r_0m1m _r_0mm _r_0mm1 _r_1 _r_m :
    ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽61⁾`. -/
noncomputable def i8L4Q61_2 (_x _r_01 _r_01m _r_01mm _r_0m _r_0m1 _r_0m1m _r_0mm _r_0mm1 _r_1 _r_m :
    ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽61⁾`. -/
noncomputable def i8L4Q61_3 (_x _r_01 _r_01m _r_01mm _r_0m _r_0m1 _r_0m1m _r_0mm _r_0mm1 _r_1 _r_m :
    ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽61⁾`. -/
noncomputable def i8L4Q61_4 (_x _r_01 _r_01m _r_01mm _r_0m _r_0m1 _r_0m1m _r_0mm _r_0mm1 _r_1 _r_m :
    ℝ) : ℝ :=
    0

theorem i8L4_61_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s61 x = i8L4S61 x + x * (i8L4Q61_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one]
      x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q61_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q61_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q61_3 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q61_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s61 i8Psi4s61N0 i8Psi4s61N1 i8Psi4s61N2 i8Psi4s61N3 i8Psi4s61N4 i8Psi4s61W
  simp only [i13hw_1m hx, i13hw_1mm hx, i13hw_mm hx, i8hw_m1m hx]
  simp only [i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_01mm h0, i13hpl_rho_0m h0,
    i13hpl_rho_0m1 h0, i13hpl_rho_0m1m h0, i13hpl_rho_0mm h0, i13hpl_rho_0mm1 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0]
  unfold i8L4S61 i8L4Q61_0 i8L4Q61_1 i8L4Q61_2 i8L4Q61_3 i8L4Q61_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽61⁾`. -/
noncomputable def i8L4R61 (x : ℝ) : ℝ :=
  x * (i8L4Q61_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) + Real.log x * i8L4Q61_1 x (i13Rho [zero, one] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
    [zero, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q61_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q61_3 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q61_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R61 : Tendsto i8L4R61 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q61_0 (v 0) (v 27) (v 36) (v 40) (v 43) (v 49) (v 54) (v 57) (v
      59) (v 65) (v 66)) (by
      unfold i8L4Q61_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q61_0 x (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R61
  unfold i8L4Q61_1 i8L4Q61_2 i8L4Q61_3 i8L4Q61_4
  ring

/-- The singular part of `Ψ₄⁽62⁾` at `ξ = 0`. -/
noncomputable def i8L4S62 (x : ℝ) : ℝ :=
    -9 / 2 + 2 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽62⁾`. -/
noncomputable def i8L4Q62_0 (x r_001m r_00m r_00m1 r_01 r_0m r_0m01 r_1 r_m : ℝ) : ℝ :=
    1 / 2 + x ^ 2 / 2 - x / 8 + x ^ 4 / 4 + 3 / 4 * x ^ 3 + r_00m * x ^ 2 + r_01 * x ^ 4 +
      r_0m * x ^ 5 + r_0m * x ^ 6 / 2 + r_1 * x ^ 3 / 2 + r_1 * x ^ 5 / 2 - 4 * r_01 * x ^ 3 -
      3 * r_0m * x ^ 3 - 2 * r_0m * x - 2 * r_1 * x - 2 * r_m * x + 4 * r_001m * x ^ 2 +
      4 * r_00m1 * x ^ 2 + 4 * r_0m01 * x ^ 2 - 11 / 4 * r_m * x ^ 2 - r_01 * x ^ 2 / 2 -
      r_0m * x ^ 4 / 2 - r_m * x ^ 3 / 2 - r_m * x ^ 5 / 2 - r_1 * x ^ 4 / 4 - r_m * x ^ 6 / 4 +
      5 / 4 * r_1 * x ^ 2 + r_0m * r_1 * x ^ 7 + r_1 * r_m * x ^ 5 - r_0m * r_1 * x ^ 3 -
      4 * r_01 * r_0m * x ^ 5 - r_1 * r_m * x ^ 3 / 2 - r_1 * r_m * x ^ 7 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽62⁾`. -/
noncomputable def i8L4Q62_1 (_x _r_001m _r_00m _r_00m1 _r_01 _r_0m _r_0m01 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽62⁾`. -/
noncomputable def i8L4Q62_2 (_x _r_001m _r_00m _r_00m1 _r_01 _r_0m _r_0m01 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽62⁾`. -/
noncomputable def i8L4Q62_3 (_x _r_001m _r_00m _r_00m1 _r_01 _r_0m _r_0m01 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽62⁾`. -/
noncomputable def i8L4Q62_4 (_x _r_001m _r_00m _r_00m1 _r_01 _r_0m _r_0m01 _r_1 _r_m : ℝ) : ℝ :=
    0

theorem i8L4_62_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s62 x = i8L4S62 x + x * (i8L4Q62_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q62_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q62_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q62_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q62_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s62 i8Psi4s62N0 i8Psi4s62N1 i8Psi4s62N2 i8Psi4s62N3 i8Psi4s62N4 i8Psi4s62W
  simp only [hpl_zero, i13hw_010m hx, i13hw_10m hx, i13hw_1m hx]
  simp only [i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0,
    i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0]
  unfold i8L4S62 i8L4Q62_0 i8L4Q62_1 i8L4Q62_2 i8L4Q62_3 i8L4Q62_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽62⁾`. -/
noncomputable def i8L4R62 (x : ℝ) : ℝ :=
  x * (i8L4Q62_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q62_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q62_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q62_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q62_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R62 : Tendsto i8L4R62 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q62_0 (v 0) (v 15) (v 18) (v 21) (v 27) (v 43) (v 44) (v 65) (v
      66)) (by
      unfold i8L4Q62_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q62_0 x (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R62
  unfold i8L4Q62_1 i8L4Q62_2 i8L4Q62_3 i8L4Q62_4
  ring

/-- The singular part of `Ψ₄⁽63⁾` at `ξ = 0`. -/
noncomputable def i8L4S63 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽63⁾`. -/
noncomputable def i8L4Q63_0 (x r_01m r_01mm r_01mmm r_0m1 r_0m1m r_0m1mm r_0mm r_0mm1 r_0mm1m r_0mmm
    r_0mmm1 r_1 r_m r_m1 : ℝ) : ℝ :=
    -x ^ 4 - x ^ 7 / 6 - x ^ 9 / 24 + x ^ 8 / 6 + 2 / 3 * x + 2 / 3 * x ^ 3 + 3 / 8 * x ^ 5 +
      13 / 3 * x ^ 2 + r_m * x ^ 4 + r_m ^ 2 * x ^ 9 + r_1 * x ^ 9 / 2 + r_m * x ^ 7 / 2 -
      16 * r_01mmm * x ^ 2 - 16 * r_0m1mm * x ^ 2 - 16 * r_0mm1m * x ^ 2 - 16 * r_0mmm1 * x ^ 2 -
      12 * r_m1 * x ^ 2 - 8 * r_m * x ^ 3 - 5 * r_1 * x ^ 4 - 5 * r_m ^ 2 * x ^ 5 -
      4 * r_01mm * x ^ 2 - 4 * r_0m1m * x ^ 2 - 4 * r_0mm1 * x ^ 2 + 4 * r_01m * x ^ 2 +
      4 * r_0m1 * x ^ 2 + 4 * r_0mmm * x ^ 2 + 4 * r_1 * x ^ 5 + 4 * r_m * x ^ 5 +
      8 * r_0mm * x ^ 2 - 19 / 6 * r_1 * x ^ 6 - 17 / 2 * r_m * x ^ 2 - 13 / 2 * r_1 * x ^ 2 -
      5 / 2 * r_m * x ^ 6 - 5 / 4 * r_1 * x ^ 8 - 4 / 3 * r_m ^ 3 * x ^ 7 -
      2 / 3 * r_m ^ 3 * x ^ 8 - r_m * x ^ 9 / 2 - r_m ^ 2 * x ^ 11 / 2 - r_m * x ^ 8 / 4 -
      r_1 * x ^ 10 / 12 + r_m ^ 3 * x ^ 10 / 3 + r_m ^ 3 * x ^ 12 / 3 + r_m * x ^ 10 / 4 +
      2 / 3 * r_m ^ 3 * x ^ 9 + 2 / 3 * r_m ^ 3 * x ^ 11 + 9 / 2 * r_m ^ 2 * x ^ 7 +
      13 / 6 * r_1 * x ^ 7 + 28 / 3 * r_1 * x ^ 3 + r_1 * r_m * x ^ 11 / 2 - r_1 * r_m * x ^ 5 -
      r_1 * r_m ^ 2 * x ^ 10 - r_1 * r_m ^ 2 * x ^ 12 - 4 * r_1 * r_m * x ^ 8 -
      4 * r_1 * r_m ^ 2 * x ^ 7 - 2 * r_1 * r_m * x ^ 10 + 2 * r_1 * r_m ^ 2 * x ^ 8 +
      2 * r_1 * r_m ^ 2 * x ^ 9 + 2 * r_1 * r_m ^ 2 * x ^ 11 + 3 * r_1 * r_m * x ^ 9 -
      2 / 3 * r_1 * r_m ^ 3 * x ^ 9 + 2 / 3 * r_1 * r_m ^ 3 * x ^ 13 + 7 / 2 * r_1 * r_m * x ^ 7

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽63⁾`. -/
noncomputable def i8L4Q63_1 (_x _r_01m _r_01mm _r_01mmm _r_0m1 _r_0m1m _r_0m1mm _r_0mm _r_0mm1
    _r_0mm1m _r_0mmm _r_0mmm1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽63⁾`. -/
noncomputable def i8L4Q63_2 (_x _r_01m _r_01mm _r_01mmm _r_0m1 _r_0m1m _r_0m1mm _r_0mm _r_0mm1
    _r_0mm1m _r_0mmm _r_0mmm1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽63⁾`. -/
noncomputable def i8L4Q63_3 (_x _r_01m _r_01mm _r_01mmm _r_0m1 _r_0m1m _r_0m1mm _r_0mm _r_0mm1
    _r_0mm1m _r_0mmm _r_0mmm1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽63⁾`. -/
noncomputable def i8L4Q63_4 (_x _r_01m _r_01mm _r_01mmm _r_0m1 _r_0m1m _r_0m1mm _r_0mm _r_0mm1
    _r_0mm1m _r_0mmm _r_0mmm1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_63_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s63 x = i8L4S63 x + x * (i8L4Q63_0 x (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, negOne] x) (i13Rho [zero, one, negOne, negOne, negOne] x) (i13Rho [zero, negOne, one]
      x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, one, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero,
      negOne, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)
      + Real.log x * i8L4Q63_1 x (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne]
      x) (i13Rho [zero, one, negOne, negOne, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, one, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one,
      negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q63_2 x (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
      negOne] x) (i13Rho [zero, one, negOne, negOne, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, one, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne,
      negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne,
      negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q63_3 x (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
      negOne] x) (i13Rho [zero, one, negOne, negOne, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, one, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne,
      negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne,
      negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q63_4 x (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
      negOne] x) (i13Rho [zero, one, negOne, negOne, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, one, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne,
      negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne,
      negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s63 i8Psi4s63N0 i8Psi4s63N1 i8Psi4s63N2 i8Psi4s63N3 i8Psi4s63N4 i8Psi4s63W
  simp only [i13hw_1m hx, i13hw_1mm hx, i13hw_mm hx, i13hw_mmm hx, i8hw_1mmm hx, i8hw_m1m
    hx, i8hw_m1mm hx, i8hw_mm1m hx]
  simp only [i13hpl_rho_01m h0, i13hpl_rho_01mm h0, i8hpl_rho_01mmm h0, i13hpl_rho_0m1 h0,
    i13hpl_rho_0m1m h0, i8hpl_rho_0m1mm h0, i13hpl_rho_0mm h0, i13hpl_rho_0mm1 h0, i8hpl_rho_0mm1m
    h0, i13hpl_rho_0mmm h0, i8hpl_rho_0mmm1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S63 i8L4Q63_0 i8L4Q63_1 i8L4Q63_2 i8L4Q63_3 i8L4Q63_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽63⁾`. -/
noncomputable def i8L4R63 (x : ℝ) : ℝ :=
  x * (i8L4Q63_0 x (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
    [zero, one, negOne, negOne, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    one, negOne] x) (i13Rho [zero, negOne, one, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, negOne] x) (i13Rho
    [zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne, one] x) (i13Rho [one]
    x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q63_1 x (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
    (i13Rho [zero, one, negOne, negOne, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, one, negOne] x) (i13Rho [zero, negOne, one, negOne, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q63_2 x (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne]
    x) (i13Rho [zero, one, negOne, negOne, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, one, negOne] x) (i13Rho [zero, negOne, one, negOne, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q63_3 x (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne]
    x) (i13Rho [zero, one, negOne, negOne, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, one, negOne] x) (i13Rho [zero, negOne, one, negOne, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q63_4 x (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne]
    x) (i13Rho [zero, one, negOne, negOne, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, one, negOne] x) (i13Rho [zero, negOne, one, negOne, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R63 : Tendsto i8L4R63 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q63_0 (v 0) (v 36) (v 40) (v 42) (v 49) (v 54) (v 56) (v 57) (v
      59) (v 61) (v 62) (v 63) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q63_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q63_0 x (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, one, negOne, negOne, negOne] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
    one, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, one] x)
    (i13Rho [zero, negOne, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho
    [zero, negOne, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R63
  unfold i8L4Q63_1 i8L4Q63_2 i8L4Q63_3 i8L4Q63_4
  ring

/-- The singular part of `Ψ₄⁽64⁾` at `ξ = 0`. -/
noncomputable def i8L4S64 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽64⁾`. -/
noncomputable def i8L4Q64_0 (x r_001m r_00m r_00m1 r_00mm r_01 r_01m r_0m r_0m01 r_0m01m r_0m0m1
    r_0m1 r_0mm r_0mm01 r_1 r_m r_m1 : ℝ) : ℝ :=
    -2 + x ^ 6 / 2 - x - 4 * x ^ 2 - x ^ 4 / 2 - x ^ 7 / 8 + 5 / 16 * x ^ 3 + 7 / 8 * x ^ 5 +
      r_01m * x ^ 2 + r_0m1 * x ^ 2 + r_0m * x ^ 4 / 2 + r_0m * x ^ 8 / 2 - r_0m * x ^ 6 -
      r_1 * x ^ 6 - r_0m ^ 2 * x ^ 5 - 12 * r_0mm * x ^ 3 - 10 * r_1 * x ^ 3 - 8 * r_0mm * x -
      4 * r_00m * x ^ 2 - 4 * r_0mm * x ^ 2 - 3 * r_m * x ^ 4 - 2 * r_001m * x ^ 2 -
      2 * r_00m1 * x ^ 2 - 2 * r_01 * x ^ 2 - 2 * r_01m * x ^ 4 - 2 * r_0m01 * x ^ 2 -
      2 * r_0m1 * x ^ 4 - 2 * r_0mm * x ^ 4 - 2 * r_m * x ^ 6 + 2 * r_01 * x ^ 3 +
      2 * r_0mm * x ^ 6 + 4 * r_00mm * x ^ 2 + 4 * r_0m * x ^ 2 + 4 * r_0mm * x ^ 5 +
      8 * r_01m * x ^ 3 + 8 * r_0m01m * x ^ 2 + 8 * r_0m0m1 * x ^ 2 + 8 * r_0m1 * x ^ 3 +
      8 * r_m1 * x ^ 2 + 16 * r_0mm01 * x ^ 2 - 9 / 2 * r_01 * x ^ 4 - r_m * x ^ 7 / 2 -
      r_1 * x ^ 8 / 4 + r_m * x ^ 8 / 4 + 3 / 2 * r_1 * x ^ 7 + 5 / 2 * r_1 * x ^ 4 +
      29 / 4 * r_1 * x ^ 2 + 33 / 4 * r_m * x ^ 2 + r_0m * r_1 * x ^ 7 + r_0m * r_1 * x ^ 9 +
      r_1 * r_m * x ^ 9 / 2 - r_0m * r_m * x ^ 7 - r_0m * r_m * x ^ 9 -
      16 * r_01 * r_0mm * x ^ 5 - 4 * r_0mm * r_1 * x ^ 3 - 4 * r_1 * r_m * x ^ 5 -
      2 * r_0m * r_1 * x ^ 5 - 2 * r_0m * r_1 * x ^ 6 - 2 * r_0m * r_1 * x ^ 8 -
      2 * r_0m * r_m * x ^ 6 - 2 * r_0m * r_m * x ^ 8 - 2 * r_1 * r_m * x ^ 8 +
      2 * r_01 * r_0m * x ^ 5 + 2 * r_0m * r_m * x ^ 5 + 2 * r_1 * r_m * x ^ 6 +
      4 * r_0m * r_1 * x ^ 4 + 4 * r_0m * r_m * x ^ 4 + 4 * r_0mm * r_1 * x ^ 7 +
      4 * r_1 * r_m * x ^ 4 + 8 * r_01m * r_0m * x ^ 5 + 8 * r_0m * r_0m1 * x ^ 5 -
      r_1 * r_m * x ^ 7 / 2 - 2 * r_0m * r_1 * r_m * x ^ 10 + 2 * r_0m * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽64⁾`. -/
noncomputable def i8L4Q64_1 (_x _r_001m _r_00m _r_00m1 _r_00mm _r_01 _r_01m _r_0m _r_0m01 _r_0m01m
    _r_0m0m1 _r_0m1 _r_0mm _r_0mm01 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽64⁾`. -/
noncomputable def i8L4Q64_2 (_x _r_001m _r_00m _r_00m1 _r_00mm _r_01 _r_01m _r_0m _r_0m01 _r_0m01m
    _r_0m0m1 _r_0m1 _r_0mm _r_0mm01 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽64⁾`. -/
noncomputable def i8L4Q64_3 (_x _r_001m _r_00m _r_00m1 _r_00mm _r_01 _r_01m _r_0m _r_0m01 _r_0m01m
    _r_0m0m1 _r_0m1 _r_0mm _r_0mm01 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽64⁾`. -/
noncomputable def i8L4Q64_4 (_x _r_001m _r_00m _r_00m1 _r_00mm _r_01 _r_01m _r_0m _r_0m01 _r_0m01m
    _r_0m0m1 _r_0m1 _r_0mm _r_0mm01 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_64_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s64 x = i8L4S64 x + x * (i8L4Q64_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne,
      zero, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x) + Real.log x * i8L4Q64_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne,
      zero, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x) + Real.log x ^ 2 * i8L4Q64_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne,
      zero, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x) + Real.log x ^ 3 * i8L4Q64_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne,
      zero, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x) + Real.log x ^ 4 * i8L4Q64_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne,
      zero, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s64 i8Psi4s64N0 i8Psi4s64N1 i8Psi4s64N2 i8Psi4s64N3 i8Psi4s64N4 i8Psi4s64W
  simp only [i13hw_010m hx, i13hw_0m0m hx, i13hw_10m hx, i13hw_1m hx, i13hw_1m0m hx,
    i13hw_m01m hx, i13hw_m0m hx, i8hw_01m0m hx, i8hw_0m10m hx, i8hw_m0m1 hx, i8hw_m10m hx]
  simp only [i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1 h0, i13hpl_rho_00mm h0,
    i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i8hpl_rho_0m01m h0,
    i8hpl_rho_0m0m1 h0, i13hpl_rho_0m1 h0, i13hpl_rho_0mm h0, i13hpl_rho_0mm01 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S64 i8L4Q64_0 i8L4Q64_1 i8L4Q64_2 i8L4Q64_3 i8L4Q64_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽64⁾`. -/
noncomputable def i8L4R64 (x : ℝ) : ℝ :=
  x * (i8L4Q64_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne,
    zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q64_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one]
    x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne,
    zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q64_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one]
    x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne,
    negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q64_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one]
    x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne,
    negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q64_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one]
    x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne,
    negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R64 : Tendsto i8L4R64 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q64_0 (v 0) (v 15) (v 18) (v 21) (v 24) (v 27) (v 36) (v 43) (v
      44) (v 46) (v 47) (v 49) (v 57) (v 58) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q64_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q64_0 x (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, negOne]
    x) (i13Rho [zero, negOne, zero, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R64
  unfold i8L4Q64_1 i8L4Q64_2 i8L4Q64_3 i8L4Q64_4
  ring

/-- The singular part of `Ψ₄⁽65⁾` at `ξ = 0`. -/
noncomputable def i8L4S65 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽65⁾`. -/
noncomputable def i8L4Q65_0 (x r_001mm r_00m1m r_00mm r_00mm1 r_01 r_01m r_0m r_0m01m r_0m0m1 r_0m1
    r_0mm r_0mm01 r_1 r_m r_m1 : ℝ) : ℝ :=
    -1 - 3 / 8 * x ^ 5 - x ^ 4 / 8 - x ^ 6 / 8 + x ^ 7 / 16 + 3 / 4 * x + 13 / 16 * x ^ 3 +
      r_01m * x ^ 2 + r_0m1 * x ^ 2 + r_0mm * x ^ 4 + r_m * x ^ 3 + r_m ^ 2 * x ^ 6 / 2 +
      r_m ^ 2 * x ^ 8 / 2 - r_01 * x ^ 2 - r_0mm * x ^ 6 - 8 * r_001mm * x ^ 2 -
      8 * r_00m1m * x ^ 2 - 8 * r_00mm1 * x ^ 2 - 8 * r_0m01m * x ^ 2 - 8 * r_0m0m1 * x ^ 2 -
      8 * r_0mm01 * x ^ 2 - 4 * r_0m * x ^ 2 - 4 * r_1 * x ^ 3 - 2 * r_00mm * x ^ 2 -
      2 * r_0mm * x ^ 5 + 2 * r_01 * x ^ 4 + 2 * r_m ^ 2 * x ^ 4 + 4 * r_0mm * x +
      4 * r_m1 * x ^ 2 + 6 * r_0mm * x ^ 3 - 9 / 4 * r_m * x ^ 4 - r_1 * x ^ 7 / 2 -
      r_m * x ^ 5 / 2 - r_m * x ^ 8 / 4 + r_m ^ 2 * x ^ 9 / 4 + r_1 * x ^ 8 / 8 +
      3 / 4 * r_m * x ^ 6 + 9 / 8 * r_1 * x ^ 4 + 11 / 4 * r_m ^ 2 * x ^ 5 +
      13 / 4 * r_1 * x ^ 2 + 17 / 4 * r_m * x ^ 2 + r_1 * r_m * x ^ 8 + r_1 * r_m * x ^ 7 / 2 +
      r_1 * r_m ^ 2 * x ^ 6 / 2 + r_1 * r_m ^ 2 * x ^ 10 / 2 - r_1 * r_m * x ^ 6 -
      r_1 * r_m ^ 2 * x ^ 8 - 2 * r_0mm * r_1 * x ^ 7 - 2 * r_1 * r_m * x ^ 5 +
      2 * r_0mm * r_1 * x ^ 3 + 2 * r_1 * r_m * x ^ 4 + 8 * r_01 * r_0mm * x ^ 5 -
      r_1 * r_m * x ^ 9 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽65⁾`. -/
noncomputable def i8L4Q65_1 (_x _r_001mm _r_00m1m _r_00mm _r_00mm1 _r_01 _r_01m _r_0m _r_0m01m
    _r_0m0m1 _r_0m1 _r_0mm _r_0mm01 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽65⁾`. -/
noncomputable def i8L4Q65_2 (_x _r_001mm _r_00m1m _r_00mm _r_00mm1 _r_01 _r_01m _r_0m _r_0m01m
    _r_0m0m1 _r_0m1 _r_0mm _r_0mm01 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽65⁾`. -/
noncomputable def i8L4Q65_3 (_x _r_001mm _r_00m1m _r_00mm _r_00mm1 _r_01 _r_01m _r_0m _r_0m01m
    _r_0m0m1 _r_0m1 _r_0mm _r_0mm01 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽65⁾`. -/
noncomputable def i8L4Q65_4 (_x _r_001mm _r_00m1m _r_00mm _r_00mm1 _r_01 _r_01m _r_0m _r_0m01m
    _r_0m0m1 _r_0m1 _r_0mm _r_0mm01 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_65_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s65 x = i8L4S65 x + x * (i8L4Q65_0 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho
      [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
      zero, negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero,
      negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x) + Real.log x * i8L4Q65_1 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero,
      zero, negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero,
      negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne,
      one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q65_2 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero, zero,
      negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne,
      negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q65_3 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero, zero,
      negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne,
      negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q65_4 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero, zero,
      negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne,
      negOne, zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s65 i8Psi4s65N0 i8Psi4s65N1 i8Psi4s65N2 i8Psi4s65N3 i8Psi4s65N4 i8Psi4s65W
  simp only [i13hw_10mm hx, i13hw_1m hx, i13hw_1mm hx, i13hw_mm hx, i8hw_010mm hx,
    i8hw_m1m hx]
  simp only [i8hpl_rho_001mm h0, i8hpl_rho_00m1m h0, i13hpl_rho_00mm h0, i8hpl_rho_00mm1 h0,
    i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i8hpl_rho_0m01m h0, i8hpl_rho_0m0m1 h0,
    i13hpl_rho_0m1 h0, i13hpl_rho_0mm h0, i13hpl_rho_0mm01 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0,
    i13hpl_rho_m1 h0]
  unfold i8L4S65 i8L4Q65_0 i8L4Q65_1 i8L4Q65_2 i8L4Q65_3 i8L4Q65_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽65⁾`. -/
noncomputable def i8L4R65 (x : ℝ) : ℝ :=
  x * (i8L4Q65_0 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero, zero, negOne, one,
    negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q65_1 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero, zero,
    negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne,
    zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q65_2 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero, zero,
    negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne,
    zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q65_3 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero, zero,
    negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne,
    zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q65_4 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero, zero,
    negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, zero, negOne, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne,
    zero, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R65 : Tendsto i8L4R65 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q65_0 (v 0) (v 17) (v 23) (v 24) (v 25) (v 27) (v 36) (v 43) (v
      46) (v 47) (v 49) (v 57) (v 58) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q65_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q65_0 x (i13Rho [zero, zero,
    one, negOne, negOne] x) (i13Rho [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
    (i13Rho [zero, negOne, zero, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R65
  unfold i8L4Q65_1 i8L4Q65_2 i8L4Q65_3 i8L4Q65_4
  ring

/-- The singular part of `Ψ₄⁽66⁾` at `ξ = 0`. -/
noncomputable def i8L4S66 (x : ℝ) : ℝ :=
    -25 / 4 + 2 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽66⁾`. -/
noncomputable def i8L4Q66_0 (x r_0001m r_000m r_000m1 r_0010m r_00m r_00m01 r_01 r_01m r_0m r_0m1
    r_1 r_m : ℝ) : ℝ :=
    3 / 4 - x ^ 2 / 2 - x / 16 - x ^ 5 / 16 + x ^ 4 / 4 + 9 / 16 * x ^ 3 + r_000m * x ^ 2 +
      r_00m * x ^ 5 + r_00m * x ^ 6 / 2 + r_01 * x ^ 4 / 2 + r_1 * x ^ 2 / 2 - r_01m * x ^ 2 -
      r_0m1 * x ^ 2 - 4 * r_01 * x ^ 3 - 3 * r_00m * x ^ 3 - 2 * r_00m * x - 2 * r_0m * x -
      2 * r_1 * x - 2 * r_m * x + 4 * r_0010m * x ^ 2 + 4 * r_00m01 * x ^ 2 +
      8 * r_0001m * x ^ 2 + 8 * r_000m1 * x ^ 2 - 3 / 8 * r_1 * x ^ 4 - r_00m * x ^ 4 / 2 -
      r_0m * x ^ 3 / 2 - r_0m * x ^ 5 / 2 - r_m * x ^ 2 / 2 - r_01 * x ^ 2 / 4 -
      r_0m * x ^ 6 / 4 - r_1 * x ^ 6 / 8 + r_m * x ^ 5 / 4 + r_m * x ^ 6 / 8 +
      3 / 4 * r_1 * x ^ 5 + 3 / 8 * r_m * x ^ 4 + 5 / 4 * r_1 * x ^ 3 + 7 / 4 * r_m * x ^ 3 +
      r_00m * r_1 * x ^ 7 + r_0m * r_1 * x ^ 5 - r_00m * r_1 * x ^ 3 -
      4 * r_00m * r_01 * x ^ 5 - r_0m * r_1 * x ^ 3 / 2 - r_0m * r_1 * x ^ 7 / 2 -
      r_1 * r_m * x ^ 3 / 4 + r_1 * r_m * x ^ 7 / 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽66⁾`. -/
noncomputable def i8L4Q66_1 (_x _r_0001m _r_000m _r_000m1 _r_0010m _r_00m _r_00m01 _r_01 _r_01m
    _r_0m _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽66⁾`. -/
noncomputable def i8L4Q66_2 (_x _r_0001m _r_000m _r_000m1 _r_0010m _r_00m _r_00m01 _r_01 _r_01m
    _r_0m _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽66⁾`. -/
noncomputable def i8L4Q66_3 (_x _r_0001m _r_000m _r_000m1 _r_0010m _r_00m _r_00m01 _r_01 _r_01m
    _r_0m _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽66⁾`. -/
noncomputable def i8L4Q66_4 (_x _r_0001m _r_000m _r_000m1 _r_0010m _r_00m _r_00m01 _r_01 _r_01m
    _r_0m _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

theorem i8L4_66_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s66 x = i8L4S66 x + x * (i8L4Q66_0 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero,
      one, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q66_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, zero, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one]
      x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q66_2 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q66_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q66_4 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s66 i8Psi4s66N0 i8Psi4s66N1 i8Psi4s66N2 i8Psi4s66N3 i8Psi4s66N4 i8Psi4s66W
  simp only [hpl_zero, i13hw_010m hx, i13hw_100m hx, i13hw_10m hx, i13hw_1m hx, i8hw_0100m hx]
  simp only [i13hpl_rho_0001m h0, i13hpl_rho_000m h0, i13hpl_rho_000m1 h0, i13hpl_rho_0010m h0,
    i13hpl_rho_00m h0, i13hpl_rho_00m01 h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0,
    i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0]
  unfold i8L4S66 i8L4Q66_0 i8L4Q66_1 i8L4Q66_2 i8L4Q66_3 i8L4Q66_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽66⁾`. -/
noncomputable def i8L4R66 (x : ℝ) : ℝ :=
  x * (i8L4Q66_0 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) + Real.log x * i8L4Q66_1 x (i13Rho [zero, zero, zero, one, negOne]
    x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    zero, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q66_2 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q66_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q66_4 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R66 : Tendsto i8L4R66 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q66_0 (v 0) (v 5) (v 6) (v 7) (v 11) (v 18) (v 19) (v 27) (v 36)
      (v 43) (v 49) (v 65) (v 66)) (by
      unfold i8L4Q66_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q66_0 x (i13Rho [zero, zero,
    zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
    one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, zero, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R66
  unfold i8L4Q66_1 i8L4Q66_2 i8L4Q66_3 i8L4Q66_4
  ring

/-- The singular part of `Ψ₄⁽67⁾` at `ξ = 0`. -/
noncomputable def i8L4S67 (x : ℝ) : ℝ :=
    (16 + 4 * Real.log x ^ 2 + 16 * Real.log x + 4 * x * Real.log x ^ 2 -
      4 / 3 * x * Real.log x ^ 3) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽67⁾`. -/
noncomputable def i8L4Q67_0 (x : ℝ) : ℝ :=
    3 * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽67⁾`. -/
noncomputable def i8L4Q67_1 (x : ℝ) : ℝ :=
    -6 * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽67⁾`. -/
noncomputable def i8L4Q67_2 (x : ℝ) : ℝ :=
    4 + 2 * x

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽67⁾`. -/
noncomputable def i8L4Q67_3 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽67⁾`. -/
noncomputable def i8L4Q67_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_67_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s67 x = i8L4S67 x + x * (i8L4Q67_0 x + Real.log x * i8L4Q67_1 x +
      Real.log x ^ 2 * i8L4Q67_2 x + Real.log x ^ 3 * i8L4Q67_3 x +
      Real.log x ^ 4 * i8L4Q67_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s67 i8Psi4s67N0 i8Psi4s67N1 i8Psi4s67N2 i8Psi4s67N3 i8Psi4s67N4 i8Psi4s67W
  simp only [hpl_zero, i13hw_00, i13hw_000]

  unfold i8L4S67 i8L4Q67_0 i8L4Q67_1 i8L4Q67_2 i8L4Q67_3 i8L4Q67_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽67⁾`. -/
noncomputable def i8L4R67 (x : ℝ) : ℝ :=
  x * (i8L4Q67_0 x + Real.log x * i8L4Q67_1 x + Real.log x ^ 2 * i8L4Q67_2 x +
    Real.log x ^ 3 * i8L4Q67_3 x + Real.log x ^ 4 * i8L4Q67_4 x)

theorem tendsto_i8L4R67 : Tendsto i8L4R67 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q67_0 (v 0)) (by
      unfold i8L4Q67_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q67_1 (v 0)) (by
      unfold i8L4Q67_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q67_2 (v 0)) (by
      unfold i8L4Q67_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q67_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q67_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q67_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R67
  unfold i8L4Q67_3 i8L4Q67_4
  ring

/-- The singular part of `Ψ₄⁽68⁾` at `ξ = 0`. -/
noncomputable def i8L4S68 (x : ℝ) : ℝ :=
    (-8 - 8 * Real.log x - 2 * Real.log x ^ 2 - 29 / 4 * x + x * Real.log x ^ 3 -
      x * Real.log x ^ 2) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽68⁾`. -/
noncomputable def i8L4Q68_0 (x r_00m _r_0m r_m : ℝ) : ℝ :=
    9 / 2 - 3 / 2 * r_m + 3 / 4 * x + 3 / 4 * x ^ 3 + 5 / 2 * x ^ 2 - 13 * r_m * x ^ 2 -
      8 * r_m * x - 8 * r_m * x ^ 3 - 4 * r_00m * x ^ 2 - 3 / 2 * r_m * x ^ 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽68⁾`. -/
noncomputable def i8L4Q68_1 (x _r_00m r_0m r_m : ℝ) : ℝ :=
    -3 - x ^ 2 - 3 * r_m + 5 * x - 3 / 2 * x ^ 3 - 8 * r_m * x + 3 * r_m * x ^ 4 +
      4 * r_0m * x ^ 2 + 8 * r_m * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽68⁾`. -/
noncomputable def i8L4Q68_2 (x _r_00m _r_0m r_m : ℝ) : ℝ :=
    -1 + x ^ 2 + x ^ 3 / 2 - r_m - x / 2 - r_m * x ^ 4 - 6 * r_m * x ^ 2 - 4 * r_m * x -
      4 * r_m * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽68⁾`. -/
noncomputable def i8L4Q68_3 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽68⁾`. -/
noncomputable def i8L4Q68_4 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_68_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s68 x = i8L4S68 x + x * (i8L4Q68_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q68_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q68_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q68_3 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q68_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s68 i8Psi4s68N0 i8Psi4s68N1 i8Psi4s68N2 i8Psi4s68N3 i8Psi4s68N4 i8Psi4s68W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0m0 hx, i13hw_m0 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S68 i8L4Q68_0 i8L4Q68_1 i8L4Q68_2 i8L4Q68_3 i8L4Q68_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽68⁾`. -/
noncomputable def i8L4R68 (x : ℝ) : ℝ :=
  x * (i8L4Q68_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q68_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q68_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q68_3 x (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q68_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x))

theorem tendsto_i8L4R68 : Tendsto i8L4R68 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q68_0 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q68_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q68_1 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q68_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q68_2 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q68_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q68_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q68_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q68_2 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R68
  unfold i8L4Q68_3 i8L4Q68_4
  ring

/-- The regular parts of group 4. -/
noncomputable def i8L4RG4 (x : ℝ) : ℝ :=
  i8L4R56 x + i8L4R57 x + i8L4R58 x + i8L4R59 x + i8L4R60 x + i8L4R61 x + i8L4R62 x +
    i8L4R63 x + i8L4R64 x + i8L4R65 x + i8L4R66 x + i8L4R67 x + i8L4R68 x

theorem tendsto_i8L4RG4 : Tendsto i8L4RG4 (𝓝[>] 0) (𝓝 0) := by
  have H := ((((((((((((tendsto_i8L4R56.add tendsto_i8L4R57).add tendsto_i8L4R58).add
    tendsto_i8L4R59).add tendsto_i8L4R60).add tendsto_i8L4R61).add tendsto_i8L4R62).add
    tendsto_i8L4R63).add tendsto_i8L4R64).add tendsto_i8L4R65).add tendsto_i8L4R66).add
    tendsto_i8L4R67).add tendsto_i8L4R68)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
