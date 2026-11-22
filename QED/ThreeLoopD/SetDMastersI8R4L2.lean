/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L1
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 2

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_27_eq`, `QED.ThreeLoopD.tendsto_i8L4RG2` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽27⁾` at `ξ = 0`. -/
noncomputable def i8L4S27 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽27⁾`. -/
noncomputable def i8L4Q27_0 (x r_0m r_0mm r_m : ℝ) : ℝ :=
    2 / 3 * π ^ 2 - π ^ 2 * x ^ 3 / 12 - π ^ 2 * x ^ 5 / 12 + π ^ 2 * x ^ 2 / 6 +
      π ^ 2 * x ^ 4 / 6 - π ^ 2 * r_m * x ^ 2 - π ^ 2 * r_m ^ 2 * x ^ 5 -
      2 / 3 * π ^ 2 * r_m * x ^ 3 - 2 / 3 * π ^ 2 * r_m ^ 2 * x ^ 4 -
      2 / 3 * π ^ 2 * r_m ^ 2 * x ^ 6 - π ^ 2 * r_m ^ 2 * x ^ 7 / 3 + π ^ 2 * r_m * x ^ 6 / 3 +
      4 / 3 * π ^ 2 * r_0m * x ^ 2 + 4 / 3 * π ^ 2 * r_0mm * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽27⁾`. -/
noncomputable def i8L4Q27_1 (_x _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽27⁾`. -/
noncomputable def i8L4Q27_2 (_x _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽27⁾`. -/
noncomputable def i8L4Q27_3 (_x _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽27⁾`. -/
noncomputable def i8L4Q27_4 (_x _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_27_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s27 x = i8L4S27 x + x * (i8L4Q27_0 x (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q27_1 x (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q27_2 x (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q27_3 x (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [negOne] x) + Real.log x ^ 4 * i8L4Q27_4 x (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s27 i8Psi4s27N0 i8Psi4s27N1 i8Psi4s27N2 i8Psi4s27N3 i8Psi4s27N4 i8Psi4s27W
  simp only [i13hw_mm hx]
  simp only [i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S27 i8L4Q27_0 i8L4Q27_1 i8L4Q27_2 i8L4Q27_3 i8L4Q27_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽27⁾`. -/
noncomputable def i8L4R27 (x : ℝ) : ℝ :=
  x * (i8L4Q27_0 x (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q27_1 x (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q27_2 x (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q27_3 x (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q27_4 x (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
    [negOne] x))

theorem tendsto_i8L4R27 : Tendsto i8L4R27 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q27_0 (v 0) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q27_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q27_0 x (i13Rho [zero, negOne]
    x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R27
  unfold i8L4Q27_1 i8L4Q27_2 i8L4Q27_3 i8L4Q27_4
  ring

/-- The singular part of `Ψ₄⁽28⁾` at `ξ = 0`. -/
noncomputable def i8L4S28 (x : ℝ) : ℝ :=
    4 / 3 * π ^ 2 - 2 / 3 * Real.log x * π ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽28⁾`. -/
noncomputable def i8L4Q28_0 (x r_00m r_0m r_m : ℝ) : ℝ :=
    -π ^ 2 / 2 + π ^ 2 * x ^ 2 / 3 + π ^ 2 * x / 12 - 2 / 3 * π ^ 2 * r_00m * x ^ 2 -
      2 / 3 * π ^ 2 * r_m * x ^ 3 - π ^ 2 * r_m * x ^ 4 / 6 + π ^ 2 * r_0m * x ^ 4 / 3 +
      π ^ 2 * r_m * x ^ 2 / 6 + 2 / 3 * π ^ 2 * r_0m * x + 2 / 3 * π ^ 2 * r_0m * x ^ 3 +
      2 / 3 * π ^ 2 * r_m * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽28⁾`. -/
noncomputable def i8L4Q28_1 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽28⁾`. -/
noncomputable def i8L4Q28_2 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽28⁾`. -/
noncomputable def i8L4Q28_3 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽28⁾`. -/
noncomputable def i8L4Q28_4 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_28_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s28 x = i8L4S28 x + x * (i8L4Q28_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q28_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q28_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q28_3 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q28_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s28 i8Psi4s28N0 i8Psi4s28N1 i8Psi4s28N2 i8Psi4s28N3 i8Psi4s28N4 i8Psi4s28W
  simp only [hpl_zero]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S28 i8L4Q28_0 i8L4Q28_1 i8L4Q28_2 i8L4Q28_3 i8L4Q28_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽28⁾`. -/
noncomputable def i8L4R28 (x : ℝ) : ℝ :=
  x * (i8L4Q28_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q28_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q28_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q28_3 x (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q28_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x))

theorem tendsto_i8L4R28 : Tendsto i8L4R28 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q28_0 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q28_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q28_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R28
  unfold i8L4Q28_1 i8L4Q28_2 i8L4Q28_3 i8L4Q28_4
  ring

/-- The singular part of `Ψ₄⁽29⁾` at `ξ = 0`. -/
noncomputable def i8L4S29 (x : ℝ) : ℝ :=
    24 - 12 * Real.log x + 2 * Real.log x ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽29⁾`. -/
noncomputable def i8L4Q29_0 (x r_0000m r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    -59 / 4 - x ^ 3 / 4 + 13 / 2 * x + 15 / 4 * x ^ 2 + r_0m * x ^ 4 / 2 - 16 * r_0000m * x ^ 2 -
      8 * r_00m * x ^ 3 - 2 * r_00m * x ^ 4 + 4 * r_0m * x + 4 * r_0m * x ^ 3 +
      6 * r_000m * x ^ 4 + 8 * r_00m * x + 12 * r_000m * x + 12 * r_000m * x ^ 3 +
      15 / 2 * r_0m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽29⁾`. -/
noncomputable def i8L4Q29_1 (x _r_0000m r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    7 / 2 - x / 4 + x ^ 3 / 4 + r_0m * x ^ 4 - 4 * r_00m * x - 4 * r_00m * x ^ 3 - 4 * r_0m * x -
      4 * r_m * x - 4 * r_m * x ^ 3 - 2 * r_00m * x ^ 4 + 4 * r_000m * x ^ 2 + 4 * r_0m * x ^ 3 -
      15 / 2 * r_m * x ^ 2 - r_m * x ^ 4 / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽29⁾`. -/
noncomputable def i8L4Q29_2 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽29⁾`. -/
noncomputable def i8L4Q29_3 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽29⁾`. -/
noncomputable def i8L4Q29_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_29_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s29 x = i8L4S29 x + x * (i8L4Q29_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [negOne] x) + Real.log x * i8L4Q29_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q29_2 x (i13Rho [zero, zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q29_3 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q29_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s29 i8Psi4s29N0 i8Psi4s29N1 i8Psi4s29N2 i8Psi4s29N3 i8Psi4s29N4 i8Psi4s29W
  simp only [hpl_zero, i13hw_00, i13hw_000m0 hx, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_m0 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S29 i8L4Q29_0 i8L4Q29_1 i8L4Q29_2 i8L4Q29_3 i8L4Q29_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽29⁾`. -/
noncomputable def i8L4R29 (x : ℝ) : ℝ :=
  x * (i8L4Q29_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q29_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q29_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q29_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q29_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R29 : Tendsto i8L4R29 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q29_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q29_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q29_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q29_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q29_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q29_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R29
  unfold i8L4Q29_2 i8L4Q29_3 i8L4Q29_4
  ring

/-- The singular part of `Ψ₄⁽30⁾` at `ξ = 0`. -/
noncomputable def i8L4S30 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽30⁾`. -/
noncomputable def i8L4Q30_0 (x r_000m r_000mm r_00m r_00m0m r_00mm r_0m _r_0mm r_m : ℝ) : ℝ :=
    14 - 7 / 4 * x ^ 2 - 3 / 8 * x ^ 5 + 5 / 2 * x + 13 / 4 * x ^ 4 + 17 / 8 * x ^ 3 +
      r_m * x ^ 6 - r_0m * x ^ 6 - 96 * r_000mm * x ^ 2 - 32 * r_00m0m * x ^ 2 -
      22 * r_m * x ^ 3 - 16 * r_00m * x ^ 2 - 16 * r_m * x ^ 2 - 13 * r_m * x ^ 4 -
      6 * r_m * x ^ 5 - 4 * r_00m * x ^ 4 + 2 * r_0m * x ^ 4 + 2 * r_0m * x ^ 5 +
      2 * r_0m ^ 2 * x ^ 7 + 4 * r_00m * x ^ 6 + 4 * r_0m ^ 2 * x ^ 4 + 4 * r_0m ^ 2 * x ^ 6 +
      5 * r_0m * x ^ 2 + 6 * r_0m ^ 2 * x ^ 5 + 8 * r_00m * x ^ 3 + 8 * r_00mm * x ^ 4 +
      16 * r_00mm * x + 16 * r_00mm * x ^ 3 + 22 * r_0m * x ^ 3 + 24 * r_000m * x ^ 2 +
      24 * r_00mm * x ^ 2 - 24 * r_00m * r_m * x ^ 5 - 16 * r_00m * r_m * x ^ 4 -
      16 * r_00m * r_m * x ^ 6 - 8 * r_00m * r_m * x ^ 7 + 16 * r_00m * r_0m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽30⁾`. -/
noncomputable def i8L4Q30_1 (x _r_000m _r_000mm r_00m _r_00m0m r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -4 + x ^ 5 / 2 - 4 * x ^ 2 - 3 * x - 2 * x ^ 4 - 11 / 4 * x ^ 3 - r_m * x ^ 6 -
      24 * r_0mm * x ^ 2 - 16 * r_0mm * x - 16 * r_0mm * x ^ 3 - 8 * r_00m * x ^ 2 -
      8 * r_0mm * x ^ 4 - 4 * r_0m * x ^ 3 - 4 * r_0m ^ 2 * x ^ 5 - 2 * r_0m * x ^ 6 +
      2 * r_0m * x ^ 4 + 2 * r_m * x ^ 5 + 6 * r_m * x ^ 4 + 8 * r_0m * x ^ 2 +
      11 * r_m * x ^ 2 + 14 * r_m * x ^ 3 + 16 * r_00mm * x ^ 2 + 4 * r_0m * r_m * x ^ 7 +
      8 * r_0m * r_m * x ^ 4 + 8 * r_0m * r_m * x ^ 6 + 12 * r_0m * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽30⁾`. -/
noncomputable def i8L4Q30_2 (_x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ
    :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽30⁾`. -/
noncomputable def i8L4Q30_3 (_x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ
    :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽30⁾`. -/
noncomputable def i8L4Q30_4 (_x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ
    :=
    0

theorem i8L4_30_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s30 x = i8L4S30 x + x * (i8L4Q30_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q30_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q30_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q30_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q30_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s30 i8Psi4s30N0 i8Psi4s30N1 i8Psi4s30N2 i8Psi4s30N3 i8Psi4s30N4 i8Psi4s30W
  simp only [hpl_zero, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m0m0 hx, i13hw_m0 hx, i13hw_m0m0 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_000mm h0, i13hpl_rho_00m h0, i13hpl_rho_00m0m h0,
    i13hpl_rho_00mm h0, i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S30 i8L4Q30_0 i8L4Q30_1 i8L4Q30_2 i8L4Q30_3 i8L4Q30_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽30⁾`. -/
noncomputable def i8L4R30 (x : ℝ) : ℝ :=
  x * (i8L4Q30_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero,
    zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
    [negOne] x) + Real.log x * i8L4Q30_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
    zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q30_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q30_3 x (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q30_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x))

theorem tendsto_i8L4R30 : Tendsto i8L4R30 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q30_0 (v 0) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v
      66)) (by
      unfold i8L4Q30_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q30_1 (v 0) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v
      66)) (by
      unfold i8L4Q30_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q30_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q30_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R30
  unfold i8L4Q30_2 i8L4Q30_3 i8L4Q30_4
  ring

/-- The singular part of `Ψ₄⁽31⁾` at `ξ = 0`. -/
noncomputable def i8L4S31 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽31⁾`. -/
noncomputable def i8L4Q31_0 (x r_00mmm r_0m r_0m0mm r_0mm r_0mmm r_m : ℝ) : ℝ :=
    -4 * x - 4 * x ^ 2 - 5 / 4 * x ^ 5 - 3 / 2 * x ^ 3 - x ^ 7 / 4 + 3 / 2 * x ^ 4 +
      3 / 2 * x ^ 6 + r_0m * x ^ 6 + r_0m * x ^ 8 + r_m * x ^ 8 - r_m * x ^ 4 - r_m ^ 2 * x ^ 9 -
      24 * r_0mm * x ^ 3 - 12 * r_0mm * x ^ 2 - 8 * r_0m * x ^ 3 - 8 * r_0m ^ 2 * x ^ 5 -
      6 * r_m * x ^ 5 - 4 * r_m * x ^ 7 - 2 * r_0m * x ^ 5 - 2 * r_0m * x ^ 7 - 2 * r_m * x ^ 6 +
      2 * r_0m * x ^ 2 + 2 * r_m ^ 2 * x ^ 8 + 4 * r_0mm * x ^ 4 + 4 * r_0mm * x ^ 6 +
      5 * r_m ^ 2 * x ^ 7 + 8 * r_0mmm * x ^ 4 + 8 * r_m * x ^ 3 + 8 * r_m ^ 2 * x ^ 5 +
      10 * r_m ^ 2 * x ^ 6 + 16 * r_0mmm * x + 16 * r_0mmm * x ^ 3 + 24 * r_0mmm * x ^ 2 +
      32 * r_0m0mm * x ^ 2 + 64 * r_00mmm * x ^ 2 - 24 * r_0mm * r_m * x ^ 5 -
      16 * r_0m * r_0mm * x ^ 5 - 16 * r_0mm * r_m * x ^ 4 - 16 * r_0mm * r_m * x ^ 6 -
      8 * r_0mm * r_m * x ^ 7 - 4 * r_0m * r_m * x ^ 9 + 4 * r_0m * r_m ^ 2 * x ^ 10 +
      8 * r_0m * r_m * x ^ 6 + 8 * r_0m * r_m ^ 2 * x ^ 7 + 8 * r_0m * r_m ^ 2 * x ^ 9 +
      12 * r_0m * r_m * x ^ 5 + 12 * r_0m * r_m ^ 2 * x ^ 8

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽31⁾`. -/
noncomputable def i8L4Q31_1 (x _r_00mmm _r_0m _r_0m0mm r_0mm r_0mmm r_m : ℝ) : ℝ :=
    x ^ 5 - x ^ 4 + 2 * x ^ 2 - 2 / 3 * x ^ 6 + x ^ 7 / 6 + 4 / 3 * x + 5 / 6 * x ^ 3 -
      r_m * x ^ 6 - r_m * x ^ 8 - 8 * r_m * x ^ 3 - 6 * r_m ^ 2 * x ^ 5 - 4 * r_m ^ 2 * x ^ 6 -
      4 * r_m ^ 3 * x ^ 8 - 2 * r_m * x ^ 2 + 2 * r_m * x ^ 5 + 2 * r_m * x ^ 7 +
      2 * r_m ^ 2 * x ^ 9 + 16 * r_0mm * x ^ 2 + 16 * r_0mmm * x ^ 2 - 8 / 3 * r_m ^ 3 * x ^ 7 -
      8 / 3 * r_m ^ 3 * x ^ 9 - 4 / 3 * r_m ^ 3 * x ^ 10

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽31⁾`. -/
noncomputable def i8L4Q31_2 (_x _r_00mmm _r_0m _r_0m0mm _r_0mm _r_0mmm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽31⁾`. -/
noncomputable def i8L4Q31_3 (_x _r_00mmm _r_0m _r_0m0mm _r_0mm _r_0mmm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽31⁾`. -/
noncomputable def i8L4Q31_4 (_x _r_00mmm _r_0m _r_0m0mm _r_0mm _r_0mmm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_31_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s31 x = i8L4S31 x + x * (i8L4Q31_0 x (i13Rho [zero, zero, negOne, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q31_1 x (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q31_2 x (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q31_3 x (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q31_4 x (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s31 i8Psi4s31N0 i8Psi4s31N1 i8Psi4s31N2 i8Psi4s31N3 i8Psi4s31N4 i8Psi4s31W
  simp only [hpl_zero, i13hw_0mm0 hx, i13hw_0mmm0 hx, i13hw_m0 hx, i13hw_mm0 hx, i13hw_mmm0 hx]
  simp only [i13hpl_rho_00mmm h0, i13hpl_rho_0m h0, i13hpl_rho_0m0mm h0, i13hpl_rho_0mm h0,
    i13hpl_rho_0mmm h0, i13hpl_rho_m h0]
  unfold i8L4S31 i8L4Q31_0 i8L4Q31_1 i8L4Q31_2 i8L4Q31_3 i8L4Q31_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽31⁾`. -/
noncomputable def i8L4R31 (x : ℝ) : ℝ :=
  x * (i8L4Q31_0 x (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne,
    negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q31_1 x (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne]
    x) (i13Rho [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
    [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q31_2 x (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q31_3 x (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q31_4 x (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R31 : Tendsto i8L4R31 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q31_0 (v 0) (v 26) (v 43) (v 48) (v 57) (v 62) (v 66)) (by
      unfold i8L4Q31_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q31_1 (v 0) (v 26) (v 43) (v 48) (v 57) (v 62) (v 66)) (by
      unfold i8L4Q31_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q31_0 x (i13Rho [zero, zero,
    negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho
    [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q31_1 x (i13Rho [zero, zero, negOne,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne]
      x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R31
  unfold i8L4Q31_2 i8L4Q31_3 i8L4Q31_4
  ring

/-- The singular part of `Ψ₄⁽32⁾` at `ξ = 0`. -/
noncomputable def i8L4S32 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽32⁾`. -/
noncomputable def i8L4Q32_0 (x r_000mm r_00m r_00m0m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    6 - 9 / 2 * x ^ 3 + x ^ 4 / 4 + x ^ 5 / 8 + 5 / 2 * x + 11 / 4 * x ^ 2 - 21 * r_0m * x ^ 2 -
      8 * r_0mm * x ^ 3 - 8 * r_m * x ^ 2 - 4 * r_0m * x ^ 5 - 4 * r_0m ^ 2 * x ^ 4 -
      4 * r_0m ^ 2 * x ^ 6 - 2 * r_0m * x ^ 3 - 2 * r_0mm * x ^ 4 - 2 * r_0m ^ 2 * x ^ 7 +
      2 * r_0mm * x ^ 2 + 8 * r_00m0m * x ^ 2 + 8 * r_0mm * x + 16 * r_00m * x ^ 2 +
      24 * r_000mm * x ^ 2 - r_m * x ^ 6 / 2 + 17 / 2 * r_m * x ^ 4 - 8 * r_0m * r_m * x ^ 4 -
      2 * r_0m * r_m * x ^ 5 + 2 * r_0m * r_m * x ^ 7 + 8 * r_0m * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽32⁾`. -/
noncomputable def i8L4Q32_1 (x _r_000mm _r_00m _r_00m0m r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -2 + x - 4 * x ^ 2 - x ^ 5 / 4 + 15 / 4 * x ^ 3 + r_m * x ^ 6 + r_m ^ 2 * x ^ 5 -
      r_m ^ 2 * x ^ 7 - 8 * r_00mm * x ^ 2 - 8 * r_0m * x ^ 2 - 8 * r_m * x ^ 4 -
      4 * r_m ^ 2 * x ^ 6 + 2 * r_m * x ^ 5 + 4 * r_0mm * x ^ 4 + 4 * r_m * x ^ 3 +
      4 * r_m ^ 2 * x ^ 4 + 8 * r_0mm * x + 8 * r_0mm * x ^ 3 + 13 * r_m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽32⁾`. -/
noncomputable def i8L4Q32_2 (_x _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽32⁾`. -/
noncomputable def i8L4Q32_3 (_x _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽32⁾`. -/
noncomputable def i8L4Q32_4 (_x _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_32_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s32 x = i8L4S32 x + x * (i8L4Q32_0 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x * i8L4Q32_1 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q32_2 x (i13Rho [zero, zero, zero, negOne, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 3 * i8L4Q32_3 x (i13Rho [zero, zero, zero, negOne, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 4 * i8L4Q32_4 x (i13Rho [zero, zero, zero, negOne, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s32 i8Psi4s32N0 i8Psi4s32N1 i8Psi4s32N2 i8Psi4s32N3 i8Psi4s32N4 i8Psi4s32W
  simp only [hpl_zero, i13hw_00mm0 hx, i13hw_0m0 hx, i13hw_0mm0 hx, i13hw_m0 hx, i13hw_mm0 hx]
  simp only [i13hpl_rho_000mm h0, i13hpl_rho_00m h0, i13hpl_rho_00m0m h0, i13hpl_rho_00mm h0,
    i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S32 i8L4Q32_0 i8L4Q32_1 i8L4Q32_2 i8L4Q32_3 i8L4Q32_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽32⁾`. -/
noncomputable def i8L4R32 (x : ℝ) : ℝ :=
  x * (i8L4Q32_0 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q32_1 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q32_2 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q32_3 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q32_4 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R32 : Tendsto i8L4R32 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q32_0 (v 0) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q32_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q32_1 (v 0) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q32_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q32_0 x (i13Rho [zero, zero,
    zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero,
    negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q32_1 x (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R32
  unfold i8L4Q32_2 i8L4Q32_3 i8L4Q32_4
  ring

/-- The singular part of `Ψ₄⁽33⁾` at `ξ = 0`. -/
noncomputable def i8L4S33 (x : ℝ) : ℝ :=
    (2 + Real.log x ^ 2 + 2 * Real.log x + Real.log x ^ 3 / 3 + Real.log x ^ 4 / 12 -
      x * Real.log x ^ 5 / 60) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽33⁾`. -/
noncomputable def i8L4Q33_0 (x : ℝ) : ℝ :=
    2 + x / 16

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽33⁾`. -/
noncomputable def i8L4Q33_1 (x : ℝ) : ℝ :=
    -2 - x / 8

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽33⁾`. -/
noncomputable def i8L4Q33_2 (x : ℝ) : ℝ :=
    1 + x / 8

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽33⁾`. -/
noncomputable def i8L4Q33_3 (x : ℝ) : ℝ :=
    -1 / 3 - x / 12

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽33⁾`. -/
noncomputable def i8L4Q33_4 (x : ℝ) : ℝ :=
    1 / 12 + x / 24

theorem i8L4_33_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s33 x = i8L4S33 x + x * (i8L4Q33_0 x + Real.log x * i8L4Q33_1 x +
      Real.log x ^ 2 * i8L4Q33_2 x + Real.log x ^ 3 * i8L4Q33_3 x +
      Real.log x ^ 4 * i8L4Q33_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s33 i8Psi4s33N0 i8Psi4s33N1 i8Psi4s33N2 i8Psi4s33N3 i8Psi4s33N4 i8Psi4s33W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00000]

  unfold i8L4S33 i8L4Q33_0 i8L4Q33_1 i8L4Q33_2 i8L4Q33_3 i8L4Q33_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽33⁾`. -/
noncomputable def i8L4R33 (x : ℝ) : ℝ :=
  x * (i8L4Q33_0 x + Real.log x * i8L4Q33_1 x + Real.log x ^ 2 * i8L4Q33_2 x +
    Real.log x ^ 3 * i8L4Q33_3 x + Real.log x ^ 4 * i8L4Q33_4 x)

theorem tendsto_i8L4R33 : Tendsto i8L4R33 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q33_0 (v 0)) (by
      unfold i8L4Q33_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q33_1 (v 0)) (by
      unfold i8L4Q33_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q33_2 (v 0)) (by
      unfold i8L4Q33_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q33_3 (v 0)) (by
      unfold i8L4Q33_3
      fun_prop)
  obtain ⟨M4, hM4⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q33_4 (v 0)) (by
      unfold i8L4Q33_4
      fun_prop)
  have H := (((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q33_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q33_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q33_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q33_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 4) (f := fun x => i8L4Q33_4 x)
      ⟨M4, fun x hx => hM4 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R33
  ring

/-- The singular part of `Ψ₄⁽34⁾` at `ξ = 0`. -/
noncomputable def i8L4S34 (x : ℝ) : ℝ :=
    4 - 4 * Real.log x + 2 * Real.log x ^ 2 - 2 / 3 * Real.log x ^ 3 + Real.log x ^ 4 / 6

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽34⁾`. -/
noncomputable def i8L4Q34_0 (x r_0000m r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    -49 / 4 + 4 * x - x ^ 3 / 8 + 7 / 4 * x ^ 2 - 16 * r_0000m * x ^ 2 + 2 * r_000m * x ^ 4 +
      4 * r_000m * x + 4 * r_000m * x ^ 3 + 6 * r_000m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽34⁾`. -/
noncomputable def i8L4Q34_1 (x _r_0000m r_000m r_00m _r_0m _r_m : ℝ) : ℝ :=
    17 / 2 - 15 / 4 * x - 3 / 2 * x ^ 2 + x ^ 3 / 4 - 6 * r_00m * x ^ 2 - 4 * r_00m * x -
      4 * r_00m * x ^ 3 - 2 * r_00m * x ^ 4 + 12 * r_000m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽34⁾`. -/
noncomputable def i8L4Q34_2 (x _r_0000m _r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    -5 / 2 + x ^ 2 / 2 - x ^ 3 / 4 + 3 / 2 * x + r_0m * x ^ 4 - 4 * r_00m * x ^ 2 + 2 * r_0m * x +
      2 * r_0m * x ^ 3 + 3 * r_0m * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽34⁾`. -/
noncomputable def i8L4Q34_3 (x _r_0000m _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    1 / 3 - x / 6 + x ^ 3 / 6 - r_m * x ^ 2 - 2 / 3 * r_m * x - 2 / 3 * r_m * x ^ 3 -
      r_m * x ^ 4 / 3 + 2 / 3 * r_0m * x ^ 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽34⁾`. -/
noncomputable def i8L4Q34_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_34_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s34 x = i8L4S34 x + x * (i8L4Q34_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [negOne] x) + Real.log x * i8L4Q34_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q34_2 x (i13Rho [zero, zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q34_3 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q34_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s34 i8Psi4s34N0 i8Psi4s34N1 i8Psi4s34N2 i8Psi4s34N3 i8Psi4s34N4 i8Psi4s34W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_0m000 hx, i13hw_m000 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S34 i8L4Q34_0 i8L4Q34_1 i8L4Q34_2 i8L4Q34_3 i8L4Q34_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽34⁾`. -/
noncomputable def i8L4R34 (x : ℝ) : ℝ :=
  x * (i8L4Q34_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q34_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q34_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q34_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q34_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R34 : Tendsto i8L4R34 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q34_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q34_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q34_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q34_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q34_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q34_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q34_3 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q34_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q34_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q34_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q34_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q34_3 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R34
  unfold i8L4Q34_4
  ring

/-- The singular part of `Ψ₄⁽35⁾` at `ξ = 0`. -/
noncomputable def i8L4S35 (x : ℝ) : ℝ :=
    -16 - 4 * Real.log x ^ 2 + 12 * Real.log x + 2 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽35⁾`. -/
noncomputable def i8L4Q35_0 (x r_0000m r_000m r_00m _r_0m _r_m : ℝ) : ℝ :=
    85 / 4 - 35 / 4 * x - 19 / 4 * x ^ 2 + x ^ 3 / 4 + r_00m * x ^ 4 - r_00m * x ^ 2 -
      12 * r_000m * x - 12 * r_000m * x ^ 3 - 6 * r_000m * x ^ 4 - 4 * r_00m * x +
      4 * r_00m * x ^ 3 + 24 * r_0000m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽35⁾`. -/
noncomputable def i8L4Q35_1 (x _r_0000m r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    -10 + 3 * x ^ 2 - x ^ 3 / 4 + 19 / 4 * x + r_0m * x ^ 2 - r_0m * x ^ 4 - 12 * r_000m * x ^ 2 -
      4 * r_0m * x ^ 3 + 4 * r_00m * x ^ 4 + 4 * r_0m * x + 8 * r_00m * x + 8 * r_00m * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽35⁾`. -/
noncomputable def i8L4Q35_2 (x _r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    3 / 2 - x ^ 2 - x / 4 + r_m * x ^ 4 / 2 - r_0m * x ^ 4 - 2 * r_0m * x - 2 * r_0m * x ^ 3 -
      2 * r_m * x + 2 * r_00m * x ^ 2 + 2 * r_m * x ^ 3 - r_m * x ^ 2 / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽35⁾`. -/
noncomputable def i8L4Q35_3 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽35⁾`. -/
noncomputable def i8L4Q35_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_35_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s35 x = i8L4S35 x + x * (i8L4Q35_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [negOne] x) + Real.log x * i8L4Q35_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q35_2 x (i13Rho [zero, zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q35_3 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q35_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s35 i8Psi4s35N0 i8Psi4s35N1 i8Psi4s35N2 i8Psi4s35N3 i8Psi4s35N4 i8Psi4s35W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m00 hx, i13hw_0m00 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S35 i8L4Q35_0 i8L4Q35_1 i8L4Q35_2 i8L4Q35_3 i8L4Q35_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽35⁾`. -/
noncomputable def i8L4R35 (x : ℝ) : ℝ :=
  x * (i8L4Q35_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q35_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q35_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q35_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q35_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R35 : Tendsto i8L4R35 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q35_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q35_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q35_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q35_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q35_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q35_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q35_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q35_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q35_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R35
  unfold i8L4Q35_3 i8L4Q35_4
  ring

/-- The singular part of `Ψ₄⁽36⁾` at `ξ = 0`. -/
noncomputable def i8L4S36 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽36⁾`. -/
noncomputable def i8L4Q36_0 (x r_000m r_000mm r_00m r_00m0m r_00mm r_0m _r_0mm r_m : ℝ) : ℝ :=
    -17 - 2 * x - 2 * x ^ 4 - 3 / 4 * x ^ 3 + x ^ 5 / 4 + 3 / 2 * x ^ 2 + r_0m * x ^ 4 -
      24 * r_000m * x ^ 2 - 12 * r_00mm * x ^ 2 - 8 * r_00mm * x - 8 * r_00mm * x ^ 3 -
      8 * r_0m * x ^ 3 - 4 * r_00m * x ^ 3 - 4 * r_00mm * x ^ 4 - 2 * r_00m * x ^ 6 +
      2 * r_00m * x ^ 4 + 3 * r_m * x ^ 5 + 6 * r_00m * x ^ 2 + 8 * r_00m0m * x ^ 2 +
      8 * r_m * x ^ 2 + 11 * r_m * x ^ 3 + 24 * r_000mm * x ^ 2 - r_m * x ^ 6 / 2 +
      13 / 2 * r_m * x ^ 4 - 8 * r_00m * r_0m * x ^ 5 + 4 * r_00m * r_m * x ^ 7 +
      8 * r_00m * r_m * x ^ 4 + 8 * r_00m * r_m * x ^ 6 + 12 * r_00m * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽36⁾`. -/
noncomputable def i8L4Q36_1 (x _r_000m _r_000mm r_00m _r_00m0m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    10 + x ^ 2 + 2 * x + 2 * x ^ 4 - x ^ 5 / 2 + 5 / 4 * x ^ 3 + r_m * x ^ 6 - 10 * r_m * x ^ 3 -
      8 * r_m * x ^ 2 - 6 * r_0m * x ^ 2 - 5 * r_m * x ^ 4 - 2 * r_0m * x ^ 4 - 2 * r_m * x ^ 5 +
      2 * r_0m * x ^ 6 + 4 * r_0m * x ^ 3 + 4 * r_0mm * x ^ 4 + 4 * r_0m ^ 2 * x ^ 5 +
      8 * r_0mm * x + 8 * r_0mm * x ^ 3 + 12 * r_0mm * x ^ 2 + 16 * r_00m * x ^ 2 -
      12 * r_0m * r_m * x ^ 5 - 8 * r_0m * r_m * x ^ 4 - 8 * r_0m * r_m * x ^ 6 -
      4 * r_0m * r_m * x ^ 7

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽36⁾`. -/
noncomputable def i8L4Q36_2 (x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -2 - x ^ 2 / 2 - x ^ 4 / 2 + x ^ 3 / 4 + x ^ 5 / 4 + r_m ^ 2 * x ^ 7 - r_m * x ^ 6 -
      4 * r_0m * x ^ 2 - 4 * r_0mm * x ^ 2 + 2 * r_m * x ^ 3 + 2 * r_m ^ 2 * x ^ 4 +
      2 * r_m ^ 2 * x ^ 6 + 3 * r_m * x ^ 2 + 3 * r_m ^ 2 * x ^ 5

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽36⁾`. -/
noncomputable def i8L4Q36_3 (_x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ
    :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽36⁾`. -/
noncomputable def i8L4Q36_4 (_x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ
    :=
    0

theorem i8L4_36_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s36 x = i8L4S36 x + x * (i8L4Q36_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q36_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q36_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q36_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q36_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s36 i8Psi4s36N0 i8Psi4s36N1 i8Psi4s36N2 i8Psi4s36N3 i8Psi4s36N4 i8Psi4s36W
  simp only [hpl_zero, i13hw_00, i13hw_0m00 hx, i13hw_0mm00 hx, i13hw_m00 hx, i13hw_mm00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_000mm h0, i13hpl_rho_00m h0, i13hpl_rho_00m0m h0,
    i13hpl_rho_00mm h0, i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S36 i8L4Q36_0 i8L4Q36_1 i8L4Q36_2 i8L4Q36_3 i8L4Q36_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽36⁾`. -/
noncomputable def i8L4R36 (x : ℝ) : ℝ :=
  x * (i8L4Q36_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero,
    zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
    [negOne] x) + Real.log x * i8L4Q36_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
    zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q36_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q36_3 x (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q36_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x))

theorem tendsto_i8L4R36 : Tendsto i8L4R36 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q36_0 (v 0) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v
      66)) (by
      unfold i8L4Q36_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q36_1 (v 0) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v
      66)) (by
      unfold i8L4Q36_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q36_2 (v 0) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v
      66)) (by
      unfold i8L4Q36_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q36_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q36_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q36_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R36
  unfold i8L4Q36_3 i8L4Q36_4
  ring

/-- The singular part of `Ψ₄⁽37⁾` at `ξ = 0`. -/
noncomputable def i8L4S37 (x : ℝ) : ℝ :=
    24 - 16 * Real.log x + 4 * Real.log x ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽37⁾`. -/
noncomputable def i8L4Q37_0 (x r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    -20 + 6 * x ^ 2 - x ^ 3 / 2 + 19 / 2 * x - 24 * r_000m * x ^ 2 - 8 * r_0m * x ^ 3 -
      2 * r_0m * x ^ 4 + 2 * r_0m * x ^ 2 + 8 * r_00m * x ^ 4 + 8 * r_0m * x + 16 * r_00m * x +
      16 * r_00m * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽37⁾`. -/
noncomputable def i8L4Q37_1 (x _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    6 - x - 4 * x ^ 2 - 8 * r_0m * x - 8 * r_0m * x ^ 3 - 8 * r_m * x - 4 * r_0m * x ^ 4 -
      2 * r_m * x ^ 2 + 2 * r_m * x ^ 4 + 8 * r_00m * x ^ 2 + 8 * r_m * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽37⁾`. -/
noncomputable def i8L4Q37_2 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽37⁾`. -/
noncomputable def i8L4Q37_3 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽37⁾`. -/
noncomputable def i8L4Q37_4 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_37_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s37 x = i8L4S37 x + x * (i8L4Q37_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q37_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q37_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q37_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q37_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s37 i8Psi4s37N0 i8Psi4s37N1 i8Psi4s37N2 i8Psi4s37N3 i8Psi4s37N4 i8Psi4s37W
  simp only [hpl_zero, i13hw_00, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_m0 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S37 i8L4Q37_0 i8L4Q37_1 i8L4Q37_2 i8L4Q37_3 i8L4Q37_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽37⁾`. -/
noncomputable def i8L4R37 (x : ℝ) : ℝ :=
  x * (i8L4Q37_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q37_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q37_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q37_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q37_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R37 : Tendsto i8L4R37 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q37_0 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q37_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q37_1 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q37_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q37_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q37_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R37
  unfold i8L4Q37_2 i8L4Q37_3 i8L4Q37_4
  ring

/-- The singular part of `Ψ₄⁽38⁾` at `ξ = 0`. -/
noncomputable def i8L4S38 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽38⁾`. -/
noncomputable def i8L4Q38_0 (x r_00m r_0m r_0mm r_m : ℝ) : ℝ :=
    20 - x ^ 5 + 2 * x ^ 2 + 4 * x + 4 * x ^ 4 + 5 / 2 * x ^ 3 - 20 * r_m * x ^ 3 -
      16 * r_m * x ^ 2 - 12 * r_0m * x ^ 2 - 10 * r_m * x ^ 4 - 4 * r_0m * x ^ 4 -
      4 * r_m * x ^ 5 + 2 * r_m * x ^ 6 + 4 * r_0m * x ^ 6 + 8 * r_0m * x ^ 3 +
      8 * r_0mm * x ^ 4 + 8 * r_0m ^ 2 * x ^ 5 + 16 * r_0mm * x + 16 * r_0mm * x ^ 3 +
      24 * r_0mm * x ^ 2 + 32 * r_00m * x ^ 2 - 24 * r_0m * r_m * x ^ 5 -
      16 * r_0m * r_m * x ^ 4 - 16 * r_0m * r_m * x ^ 6 - 8 * r_0m * r_m * x ^ 7

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽38⁾`. -/
noncomputable def i8L4Q38_1 (x _r_00m r_0m r_0mm r_m : ℝ) : ℝ :=
    -8 + x ^ 3 + x ^ 5 - 2 * x ^ 2 - 2 * x ^ 4 - 16 * r_0m * x ^ 2 - 16 * r_0mm * x ^ 2 -
      4 * r_m * x ^ 6 + 4 * r_m ^ 2 * x ^ 7 + 8 * r_m * x ^ 3 + 8 * r_m ^ 2 * x ^ 4 +
      8 * r_m ^ 2 * x ^ 6 + 12 * r_m * x ^ 2 + 12 * r_m ^ 2 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽38⁾`. -/
noncomputable def i8L4Q38_2 (_x _r_00m _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽38⁾`. -/
noncomputable def i8L4Q38_3 (_x _r_00m _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽38⁾`. -/
noncomputable def i8L4Q38_4 (_x _r_00m _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_38_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s38 x = i8L4S38 x + x * (i8L4Q38_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q38_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q38_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q38_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q38_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s38 i8Psi4s38N0 i8Psi4s38N1 i8Psi4s38N2 i8Psi4s38N3 i8Psi4s38N4 i8Psi4s38W
  simp only [hpl_zero, i13hw_0m0 hx, i13hw_0mm0 hx, i13hw_m0 hx, i13hw_mm0 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S38 i8L4Q38_0 i8L4Q38_1 i8L4Q38_2 i8L4Q38_3 i8L4Q38_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽38⁾`. -/
noncomputable def i8L4R38 (x : ℝ) : ℝ :=
  x * (i8L4Q38_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q38_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q38_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q38_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q38_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R38 : Tendsto i8L4R38 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q38_0 (v 0) (v 18) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q38_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q38_1 (v 0) (v 18) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q38_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q38_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q38_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R38
  unfold i8L4Q38_2 i8L4Q38_3 i8L4Q38_4
  ring

/-- The singular part of `Ψ₄⁽39⁾` at `ξ = 0`. -/
noncomputable def i8L4S39 (x : ℝ) : ℝ :=
    -8 - 4 * Real.log x ^ 2 + 8 * Real.log x + 4 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽39⁾`. -/
noncomputable def i8L4Q39_0 (x r_000m r_00m _r_0m _r_m : ℝ) : ℝ :=
    17 + x ^ 3 / 2 - 3 * x ^ 2 - 15 / 2 * x - 12 * r_00m * x ^ 2 - 8 * r_00m * x -
      8 * r_00m * x ^ 3 - 4 * r_00m * x ^ 4 + 24 * r_000m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽39⁾`. -/
noncomputable def i8L4Q39_1 (x _r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    -10 - x ^ 3 + 2 * x ^ 2 + 6 * x - 16 * r_00m * x ^ 2 + 4 * r_0m * x ^ 4 + 8 * r_0m * x +
      8 * r_0m * x ^ 3 + 12 * r_0m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽39⁾`. -/
noncomputable def i8L4Q39_2 (x _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    2 + x ^ 3 - x - 6 * r_m * x ^ 2 - 4 * r_m * x - 4 * r_m * x ^ 3 - 2 * r_m * x ^ 4 +
      4 * r_0m * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽39⁾`. -/
noncomputable def i8L4Q39_3 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽39⁾`. -/
noncomputable def i8L4Q39_4 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_39_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s39 x = i8L4S39 x + x * (i8L4Q39_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q39_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q39_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q39_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q39_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s39 i8Psi4s39N0 i8Psi4s39N1 i8Psi4s39N2 i8Psi4s39N3 i8Psi4s39N4 i8Psi4s39W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0m00 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S39 i8L4Q39_0 i8L4Q39_1 i8L4Q39_2 i8L4Q39_3 i8L4Q39_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽39⁾`. -/
noncomputable def i8L4R39 (x : ℝ) : ℝ :=
  x * (i8L4Q39_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q39_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q39_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q39_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q39_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R39 : Tendsto i8L4R39 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q39_0 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q39_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q39_1 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q39_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q39_2 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q39_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q39_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q39_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q39_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R39
  unfold i8L4Q39_3 i8L4Q39_4
  ring

/-- The singular part of `Ψ₄⁽40⁾` at `ξ = 0`. -/
noncomputable def i8L4S40 (x : ℝ) : ℝ :=
    (4 + 2 * Real.log x ^ 2 + 4 * Real.log x + 2 / 3 * Real.log x ^ 3 -
      x * Real.log x ^ 4 / 6) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽40⁾`. -/
noncomputable def i8L4Q40_0 (x : ℝ) : ℝ :=
    -4 - x / 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽40⁾`. -/
noncomputable def i8L4Q40_1 (x : ℝ) : ℝ :=
    4 + x / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽40⁾`. -/
noncomputable def i8L4Q40_2 (x : ℝ) : ℝ :=
    -2 - x / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽40⁾`. -/
noncomputable def i8L4Q40_3 (x : ℝ) : ℝ :=
    2 / 3 + x / 3

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽40⁾`. -/
noncomputable def i8L4Q40_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_40_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s40 x = i8L4S40 x + x * (i8L4Q40_0 x + Real.log x * i8L4Q40_1 x +
      Real.log x ^ 2 * i8L4Q40_2 x + Real.log x ^ 3 * i8L4Q40_3 x +
      Real.log x ^ 4 * i8L4Q40_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s40 i8Psi4s40N0 i8Psi4s40N1 i8Psi4s40N2 i8Psi4s40N3 i8Psi4s40N4 i8Psi4s40W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000]

  unfold i8L4S40 i8L4Q40_0 i8L4Q40_1 i8L4Q40_2 i8L4Q40_3 i8L4Q40_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽40⁾`. -/
noncomputable def i8L4R40 (x : ℝ) : ℝ :=
  x * (i8L4Q40_0 x + Real.log x * i8L4Q40_1 x + Real.log x ^ 2 * i8L4Q40_2 x +
    Real.log x ^ 3 * i8L4Q40_3 x + Real.log x ^ 4 * i8L4Q40_4 x)

theorem tendsto_i8L4R40 : Tendsto i8L4R40 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q40_0 (v 0)) (by
      unfold i8L4Q40_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q40_1 (v 0)) (by
      unfold i8L4Q40_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q40_2 (v 0)) (by
      unfold i8L4Q40_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q40_3 (v 0)) (by
      unfold i8L4Q40_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q40_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q40_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q40_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q40_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R40
  unfold i8L4Q40_4
  ring

/-- The singular part of `Ψ₄⁽41⁾` at `ξ = 0`. -/
noncomputable def i8L4S41 (x : ℝ) : ℝ :=
    (48 - 12 * zeta3 - 2 * π ^ 2 + 16 * Real.log x - 8 * x * Real.log x ^ 2 -
      4 * Real.log x * zeta3 + 32 * Real.log x * x - 2 / 3 * Real.log x * π ^ 2 +
      π ^ 2 * x * Real.log x ^ 2 + 6 * x * zeta3 * Real.log x ^ 2 + 8 * Real.log x * x * zeta3 +
      4 / 3 * Real.log x * π ^ 2 * x) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽41⁾`. -/
noncomputable def i8L4Q41_0 (x : ℝ) : ℝ :=
    16 - 20 * x - 20 * zeta3 - 10 / 3 * π ^ 2 - 5 * x * zeta3 - 5 / 6 * π ^ 2 * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽41⁾`. -/
noncomputable def i8L4Q41_1 (x : ℝ) : ℝ :=
    16 + 2 * π ^ 2 + 8 * x + 12 * zeta3 + 2 * x * zeta3 + π ^ 2 * x / 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽41⁾`. -/
noncomputable def i8L4Q41_2 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽41⁾`. -/
noncomputable def i8L4Q41_3 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽41⁾`. -/
noncomputable def i8L4Q41_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_41_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s41 x = i8L4S41 x + x * (i8L4Q41_0 x + Real.log x * i8L4Q41_1 x +
      Real.log x ^ 2 * i8L4Q41_2 x + Real.log x ^ 3 * i8L4Q41_3 x +
      Real.log x ^ 4 * i8L4Q41_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s41 i8Psi4s41N0 i8Psi4s41N1 i8Psi4s41N2 i8Psi4s41N3 i8Psi4s41N4 i8Psi4s41W
  simp only [hpl_zero, i13hw_00]

  unfold i8L4S41 i8L4Q41_0 i8L4Q41_1 i8L4Q41_2 i8L4Q41_3 i8L4Q41_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽41⁾`. -/
noncomputable def i8L4R41 (x : ℝ) : ℝ :=
  x * (i8L4Q41_0 x + Real.log x * i8L4Q41_1 x + Real.log x ^ 2 * i8L4Q41_2 x +
    Real.log x ^ 3 * i8L4Q41_3 x + Real.log x ^ 4 * i8L4Q41_4 x)

theorem tendsto_i8L4R41 : Tendsto i8L4R41 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q41_0 (v 0)) (by
      unfold i8L4Q41_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q41_1 (v 0)) (by
      unfold i8L4Q41_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q41_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q41_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R41
  unfold i8L4Q41_2 i8L4Q41_3 i8L4Q41_4
  ring

/-- The regular parts of group 2. -/
noncomputable def i8L4RG2 (x : ℝ) : ℝ :=
  i8L4R27 x + i8L4R28 x + i8L4R29 x + i8L4R30 x + i8L4R31 x + i8L4R32 x + i8L4R33 x +
    i8L4R34 x + i8L4R35 x + i8L4R36 x + i8L4R37 x + i8L4R38 x + i8L4R39 x + i8L4R40 x + i8L4R41 x

theorem tendsto_i8L4RG2 : Tendsto i8L4RG2 (𝓝[>] 0) (𝓝 0) := by
  have H := ((((((((((((((tendsto_i8L4R27.add tendsto_i8L4R28).add tendsto_i8L4R29).add
    tendsto_i8L4R30).add tendsto_i8L4R31).add tendsto_i8L4R32).add tendsto_i8L4R33).add
    tendsto_i8L4R34).add tendsto_i8L4R35).add tendsto_i8L4R36).add tendsto_i8L4R37).add
    tendsto_i8L4R38).add tendsto_i8L4R39).add tendsto_i8L4R40).add tendsto_i8L4R41)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
