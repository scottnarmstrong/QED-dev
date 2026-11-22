/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L0

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 1

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_11_eq`, `QED.ThreeLoopD.tendsto_i8L4RG1` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽11⁾` at `ξ = 0`. -/
noncomputable def i8L4S11 (x : ℝ) : ℝ :=
    (-16 + 4 * x + 4 * zeta3 + 2 / 3 * π ^ 2 - 8 * Real.log x * x + 7 * x * zeta3 +
      7 / 6 * π ^ 2 * x - Real.log x * π ^ 2 * x - 6 * Real.log x * x * zeta3) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽11⁾`. -/
noncomputable def i8L4Q11_0 (x r_0m r_m : ℝ) : ℝ :=
    -24 - 8 * r_m - 4 * x ^ 3 + 2 * zeta3 + 4 * x + 8 * x ^ 2 + π ^ 2 / 3 + x * zeta3 -
      zeta3 * x ^ 3 - 32 * r_0m * x ^ 2 - 2 * zeta3 * x ^ 2 + 2 * r_m * zeta3 + 8 * r_m * x ^ 4 -
      π ^ 2 * x ^ 2 / 3 - π ^ 2 * x ^ 3 / 6 + π ^ 2 * r_m / 3 + π ^ 2 * x / 6 +
      2 * π ^ 2 * r_m * x ^ 2 + 2 * r_m * zeta3 * x ^ 4 + 8 * r_m * x * zeta3 +
      8 * r_m * zeta3 * x ^ 3 + 12 * r_m * zeta3 * x ^ 2 + π ^ 2 * r_m * x ^ 4 / 3 +
      4 / 3 * π ^ 2 * r_m * x + 4 / 3 * π ^ 2 * r_m * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽11⁾`. -/
noncomputable def i8L4Q11_1 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽11⁾`. -/
noncomputable def i8L4Q11_2 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽11⁾`. -/
noncomputable def i8L4Q11_3 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽11⁾`. -/
noncomputable def i8L4Q11_4 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_11_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s11 x = i8L4S11 x + x * (i8L4Q11_0 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q11_1 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q11_2 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q11_3 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q11_4 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s11 i8Psi4s11N0 i8Psi4s11N1 i8Psi4s11N2 i8Psi4s11N3 i8Psi4s11N4 i8Psi4s11W
  simp only [hpl_zero]
  simp only [i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S11 i8L4Q11_0 i8L4Q11_1 i8L4Q11_2 i8L4Q11_3 i8L4Q11_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽11⁾`. -/
noncomputable def i8L4R11 (x : ℝ) : ℝ :=
  x * (i8L4Q11_0 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q11_1 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q11_2 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q11_3 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q11_4 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R11 : Tendsto i8L4R11 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q11_0 (v 0) (v 43) (v 66)) (by
      unfold i8L4Q11_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q11_0 x (i13Rho [zero, negOne]
    x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R11
  unfold i8L4Q11_1 i8L4Q11_2 i8L4Q11_3 i8L4Q11_4
  ring

/-- The singular part of `Ψ₄⁽12⁾` at `ξ = 0`. -/
noncomputable def i8L4S12 (x : ℝ) : ℝ :=
    (-8 - 15 * x - 8 * Real.log x + π ^ 2 / 3 + 6 * x * Real.log x ^ 2 + Real.log x * π ^ 2 / 3 +
      5 / 8 * π ^ 2 * x - π ^ 2 * x * Real.log x ^ 2 / 4) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽12⁾`. -/
noncomputable def i8L4Q12_0 (x r_0m r_m : ℝ) : ℝ :=
    6 - x ^ 3 - 6 * x ^ 2 - 2 * r_m + 8 * x - π ^ 2 / 4 - 16 * r_m * x + 2 * r_m * x ^ 4 +
      16 * r_m * x ^ 3 + 24 * r_0m * x ^ 2 - π ^ 2 * x / 3 + π ^ 2 * x ^ 2 / 4 +
      π ^ 2 * r_m / 12 + π ^ 2 * x ^ 3 / 24 - π ^ 2 * r_0m * x ^ 2 - 2 / 3 * π ^ 2 * r_m * x ^ 3 -
      π ^ 2 * r_m * x ^ 4 / 12 + 2 / 3 * π ^ 2 * r_m * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽12⁾`. -/
noncomputable def i8L4Q12_1 (x _r_0m r_m : ℝ) : ℝ :=
    -4 - 4 * r_m - 2 * x + 2 * x ^ 3 + 4 * x ^ 2 + π ^ 2 / 6 - 24 * r_m * x ^ 2 - 16 * r_m * x -
      16 * r_m * x ^ 3 - 4 * r_m * x ^ 4 - π ^ 2 * x ^ 2 / 6 - π ^ 2 * x ^ 3 / 12 +
      π ^ 2 * r_m / 6 + π ^ 2 * x / 12 + π ^ 2 * r_m * x ^ 2 + π ^ 2 * r_m * x ^ 4 / 6 +
      2 / 3 * π ^ 2 * r_m * x + 2 / 3 * π ^ 2 * r_m * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽12⁾`. -/
noncomputable def i8L4Q12_2 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽12⁾`. -/
noncomputable def i8L4Q12_3 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽12⁾`. -/
noncomputable def i8L4Q12_4 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_12_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s12 x = i8L4S12 x + x * (i8L4Q12_0 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q12_1 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q12_2 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q12_3 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q12_4 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s12 i8Psi4s12N0 i8Psi4s12N1 i8Psi4s12N2 i8Psi4s12N3 i8Psi4s12N4 i8Psi4s12W
  simp only [hpl_zero, i13hw_00, i13hw_m0 hx]
  simp only [i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S12 i8L4Q12_0 i8L4Q12_1 i8L4Q12_2 i8L4Q12_3 i8L4Q12_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽12⁾`. -/
noncomputable def i8L4R12 (x : ℝ) : ℝ :=
  x * (i8L4Q12_0 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q12_1 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q12_2 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q12_3 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q12_4 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R12 : Tendsto i8L4R12 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q12_0 (v 0) (v 43) (v 66)) (by
      unfold i8L4Q12_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q12_1 (v 0) (v 43) (v 66)) (by
      unfold i8L4Q12_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q12_0 x (i13Rho [zero, negOne]
    x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q12_1 x (i13Rho [zero, negOne] x)
      (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R12
  unfold i8L4Q12_2 i8L4Q12_3 i8L4Q12_4
  ring

/-- The singular part of `Ψ₄⁽13⁾` at `ξ = 0`. -/
noncomputable def i8L4S13 (x : ℝ) : ℝ :=
    -π ^ 2 + 2 / 3 * Real.log x * π ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽13⁾`. -/
noncomputable def i8L4Q13_0 (x r_0m r_m : ℝ) : ℝ :=
    2 / 3 * π ^ 2 - π ^ 2 * x ^ 2 / 3 - π ^ 2 * x ^ 5 / 12 + π ^ 2 * x ^ 3 / 3 + π ^ 2 * x / 12 -
      2 * π ^ 2 * r_m ^ 2 * x ^ 5 + 2 * π ^ 2 * r_0m * x ^ 2 - 4 / 3 * π ^ 2 * r_m * x -
      4 / 3 * π ^ 2 * r_m * x ^ 2 - 4 / 3 * π ^ 2 * r_m ^ 2 * x ^ 4 -
      4 / 3 * π ^ 2 * r_m ^ 2 * x ^ 6 - 2 / 3 * π ^ 2 * r_m * x ^ 3 - π ^ 2 * r_m * x ^ 4 / 3 -
      π ^ 2 * r_m ^ 2 * x ^ 3 / 3 - π ^ 2 * r_m ^ 2 * x ^ 7 / 3 + π ^ 2 * r_m * x ^ 6 / 3 +
      2 / 3 * π ^ 2 * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽13⁾`. -/
noncomputable def i8L4Q13_1 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽13⁾`. -/
noncomputable def i8L4Q13_2 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽13⁾`. -/
noncomputable def i8L4Q13_3 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽13⁾`. -/
noncomputable def i8L4Q13_4 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_13_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s13 x = i8L4S13 x + x * (i8L4Q13_0 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q13_1 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q13_2 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q13_3 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q13_4 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s13 i8Psi4s13N0 i8Psi4s13N1 i8Psi4s13N2 i8Psi4s13N3 i8Psi4s13N4 i8Psi4s13W
  simp only [hpl_zero, i13hw_mm hx]
  simp only [i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S13 i8L4Q13_0 i8L4Q13_1 i8L4Q13_2 i8L4Q13_3 i8L4Q13_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽13⁾`. -/
noncomputable def i8L4R13 (x : ℝ) : ℝ :=
  x * (i8L4Q13_0 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q13_1 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q13_2 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q13_3 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q13_4 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R13 : Tendsto i8L4R13 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q13_0 (v 0) (v 43) (v 66)) (by
      unfold i8L4Q13_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q13_0 x (i13Rho [zero, negOne]
    x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R13
  unfold i8L4Q13_1 i8L4Q13_2 i8L4Q13_3 i8L4Q13_4
  ring

/-- The singular part of `Ψ₄⁽14⁾` at `ξ = 0`. -/
noncomputable def i8L4S14 (x : ℝ) : ℝ :=
    -11 - 2 * Real.log x ^ 2 + 8 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽14⁾`. -/
noncomputable def i8L4Q14_0 (x r_000m r_00m r_00mm r_0m _r_0mm r_m : ℝ) : ℝ :=
    16 + 8 * x ^ 2 - 17 / 8 * x - x ^ 5 / 8 + 7 / 4 * x ^ 4 - 30 * r_0m * x ^ 2 -
      29 * r_m * x ^ 2 - 27 * r_m * x ^ 3 - 8 * r_00m * x - 4 * r_00m * x ^ 3 - 4 * r_0m * x -
      4 * r_m * x - 3 * r_0m * x ^ 5 - 3 * r_m * x ^ 5 - 2 * r_00m * x ^ 4 + 2 * r_00m * x ^ 6 +
      3 * r_0m * x ^ 3 + 4 * r_00m * x ^ 5 + 4 * r_0m * x ^ 4 + 6 * r_0m ^ 2 * x ^ 5 +
      7 * r_00m * x ^ 2 + 18 * r_000m * x ^ 2 + 24 * r_00mm * x ^ 2 - 21 / 4 * r_m * x ^ 4 -
      r_0m * x ^ 6 / 2 + r_m * x ^ 6 / 4 + r_0m * r_m * x ^ 7 - r_0m * r_m * x ^ 3 -
      24 * r_00m * r_m * x ^ 5 - 16 * r_00m * r_m * x ^ 4 - 16 * r_00m * r_m * x ^ 6 -
      8 * r_0m * r_m * x ^ 4 - 4 * r_00m * r_m * x ^ 3 - 4 * r_00m * r_m * x ^ 7 +
      8 * r_0m * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽14⁾`. -/
noncomputable def i8L4Q14_1 (x _r_000m r_00m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -5 - 14 * x ^ 2 + 4 * x ^ 3 - 5 / 4 * x - 3 / 2 * x ^ 4 + r_0m * x ^ 4 + r_m ^ 2 * x ^ 3 +
      r_m * x ^ 6 / 2 - r_0m * x ^ 6 - r_m ^ 2 * x ^ 7 - 24 * r_0mm * x ^ 2 -
      8 * r_m ^ 2 * x ^ 6 - 7 * r_0m * x ^ 2 - 6 * r_00m * x ^ 2 - 2 * r_0m * x ^ 5 +
      2 * r_0m * x ^ 3 + 4 * r_0m * x + 6 * r_m * x ^ 5 + 8 * r_m * x + 8 * r_m ^ 2 * x ^ 4 +
      22 * r_m * x ^ 3 + 45 * r_m * x ^ 2 - 19 / 2 * r_m * x ^ 4 + 2 * r_0m * r_m * x ^ 3 +
      2 * r_0m * r_m * x ^ 7 + 8 * r_0m * r_m * x ^ 4 + 8 * r_0m * r_m * x ^ 6 +
      12 * r_0m * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽14⁾`. -/
noncomputable def i8L4Q14_2 (_x _r_000m _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽14⁾`. -/
noncomputable def i8L4Q14_3 (_x _r_000m _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽14⁾`. -/
noncomputable def i8L4Q14_4 (_x _r_000m _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_14_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s14 x = i8L4S14 x + x * (i8L4Q14_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q14_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q14_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q14_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q14_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s14 i8Psi4s14N0 i8Psi4s14N1 i8Psi4s14N2 i8Psi4s14N3 i8Psi4s14N4 i8Psi4s14W
  simp only [hpl_zero, i13hw_00, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m0m hx, i13hw_0mm0 hx, i13hw_m0
    hx, i13hw_m0m hx, i13hw_m0m0 hx, i13hw_mm0 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_00mm h0, i13hpl_rho_0m h0,
    i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S14 i8L4Q14_0 i8L4Q14_1 i8L4Q14_2 i8L4Q14_3 i8L4Q14_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽14⁾`. -/
noncomputable def i8L4R14 (x : ℝ) : ℝ :=
  x * (i8L4Q14_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [negOne] x) + Real.log x * i8L4Q14_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q14_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q14_3 x (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q14_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R14 : Tendsto i8L4R14 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q14_0 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q14_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q14_1 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q14_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q14_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q14_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R14
  unfold i8L4Q14_2 i8L4Q14_3 i8L4Q14_4
  ring

/-- The singular part of `Ψ₄⁽15⁾` at `ξ = 0`. -/
noncomputable def i8L4S15 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽15⁾`. -/
noncomputable def i8L4Q15_0 (x r_00m r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -10 + x ^ 6 - 4 * x - 4 * x ^ 4 - 21 / 2 * x ^ 2 - x ^ 7 / 4 + 3 / 2 * x ^ 5 +
      17 / 4 * x ^ 3 + r_0m * x ^ 8 + r_m * x ^ 8 - r_0m * x ^ 4 - r_m ^ 2 * x ^ 9 -
      24 * r_00mm * x ^ 2 - 20 * r_00m * x ^ 2 - 12 * r_0m ^ 2 * x ^ 5 - 10 * r_m * x ^ 6 -
      8 * r_0m * x ^ 3 - 8 * r_0mm * x - 8 * r_0mm * x ^ 2 - 4 * r_0m * x ^ 6 -
      4 * r_0mm * x ^ 3 - 2 * r_0mm * x ^ 4 - 2 * r_m * x ^ 5 - 2 * r_m * x ^ 7 +
      2 * r_0mm * x ^ 6 + 4 * r_0m * x ^ 5 + 4 * r_0mm * x ^ 5 + 4 * r_m ^ 2 * x ^ 4 +
      10 * r_m ^ 2 * x ^ 7 + 15 * r_m ^ 2 * x ^ 5 + 18 * r_m * x ^ 3 + 20 * r_m ^ 2 * x ^ 6 +
      39 * r_0m * x ^ 2 - 3 / 2 * r_m * x ^ 4 + 49 / 2 * r_m * x ^ 2 - 24 * r_0mm * r_m * x ^ 5 -
      16 * r_0mm * r_m * x ^ 4 - 16 * r_0mm * r_m * x ^ 6 - 8 * r_0m * r_m * x ^ 8 -
      4 * r_0m * r_m * x ^ 9 - 4 * r_0mm * r_m * x ^ 3 - 4 * r_0mm * r_m * x ^ 7 +
      4 * r_0m * r_m * x ^ 7 + 4 * r_0m * r_m ^ 2 * x ^ 6 + 4 * r_0m * r_m ^ 2 * x ^ 10 +
      8 * r_0m * r_m * x ^ 6 + 16 * r_0m * r_m * x ^ 4 + 16 * r_0m * r_m * x ^ 5 +
      16 * r_0m * r_m ^ 2 * x ^ 7 + 16 * r_0m * r_m ^ 2 * x ^ 9 + 24 * r_0m * r_m ^ 2 * x ^ 8

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽15⁾`. -/
noncomputable def i8L4Q15_1 (x _r_00m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    4 + x - 7 * x ^ 3 + 18 * x ^ 2 - 3 / 4 * x ^ 5 - x ^ 6 / 2 + x ^ 7 / 4 + 7 / 2 * x ^ 4 -
      45 * r_m * x ^ 2 - 24 * r_m * x ^ 3 - 12 * r_m ^ 2 * x ^ 4 - 12 * r_m ^ 2 * x ^ 5 -
      12 * r_m ^ 3 * x ^ 8 - 8 * r_m ^ 3 * x ^ 7 - 8 * r_m ^ 3 * x ^ 9 - 6 * r_m * x ^ 5 -
      6 * r_m ^ 2 * x ^ 6 - 3 * r_m ^ 2 * x ^ 7 - 2 * r_m ^ 3 * x ^ 6 - 2 * r_m ^ 3 * x ^ 10 +
      3 * r_m ^ 2 * x ^ 9 + 6 * r_m * x ^ 6 + 6 * r_m ^ 2 * x ^ 8 + 12 * r_0m * x ^ 2 +
      36 * r_0mm * x ^ 2 - 3 / 2 * r_m * x ^ 8 + 21 / 2 * r_m * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽15⁾`. -/
noncomputable def i8L4Q15_2 (_x _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽15⁾`. -/
noncomputable def i8L4Q15_3 (_x _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽15⁾`. -/
noncomputable def i8L4Q15_4 (_x _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_15_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s15 x = i8L4S15 x + x * (i8L4Q15_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x * i8L4Q15_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q15_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 3 * i8L4Q15_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 4 * i8L4Q15_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s15 i8Psi4s15N0 i8Psi4s15N1 i8Psi4s15N2 i8Psi4s15N3 i8Psi4s15N4 i8Psi4s15W
  simp only [hpl_zero, i13hw_0m0 hx, i13hw_0m0m hx, i13hw_0mm0 hx, i13hw_m0 hx, i13hw_m0m hx,
    i13hw_mm0 hx, i13hw_mmm0 hx, i8hw_mm0m hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_00mm h0, i13hpl_rho_0m h0, i13hpl_rho_0mm h0,
    i13hpl_rho_m h0]
  unfold i8L4S15 i8L4Q15_0 i8L4Q15_1 i8L4Q15_2 i8L4Q15_3 i8L4Q15_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽15⁾`. -/
noncomputable def i8L4R15 (x : ℝ) : ℝ :=
  x * (i8L4Q15_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q15_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q15_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q15_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q15_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R15 : Tendsto i8L4R15 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q15_0 (v 0) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q15_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q15_1 (v 0) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q15_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q15_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q15_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R15
  unfold i8L4Q15_2 i8L4Q15_3 i8L4Q15_4
  ring

/-- The singular part of `Ψ₄⁽16⁾` at `ξ = 0`. -/
noncomputable def i8L4S16 (x : ℝ) : ℝ :=
    (-2 - Real.log x ^ 2 - 2 * Real.log x - 63 / 16 * x - Real.log x ^ 3 / 3 +
      x * Real.log x ^ 4 / 8) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽16⁾`. -/
noncomputable def i8L4Q16_0 (x r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    11 / 8 - 15 / 8 * x ^ 2 - r_m / 8 - x ^ 3 / 16 + 3 / 2 * x - 4 * r_m * x + 4 * r_m * x ^ 3 +
      6 * r_000m * x ^ 2 + r_m * x ^ 4 / 8 + 15 / 2 * r_0m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽16⁾`. -/
noncomputable def i8L4Q16_1 (x _r_000m r_00m _r_0m r_m : ℝ) : ℝ :=
    -5 / 4 - r_m / 4 + x ^ 3 / 8 + 7 / 4 * x ^ 2 + 7 / 8 * x - 6 * r_00m * x ^ 2 - 4 * r_m * x -
      4 * r_m * x ^ 3 - 15 / 2 * r_m * x ^ 2 - r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽16⁾`. -/
noncomputable def i8L4Q16_2 (x _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    3 / 4 + x - 3 / 4 * x ^ 2 - r_m / 4 - x ^ 3 / 8 - 2 * r_m * x + 2 * r_m * x ^ 3 +
      3 * r_0m * x ^ 2 + r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽16⁾`. -/
noncomputable def i8L4Q16_3 (x _r_000m _r_00m _r_0m r_m : ℝ) : ℝ :=
    -1 / 6 - r_m / 6 - x / 12 + x ^ 2 / 6 + x ^ 3 / 12 - r_m * x ^ 2 - 2 / 3 * r_m * x -
      2 / 3 * r_m * x ^ 3 - r_m * x ^ 4 / 6

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽16⁾`. -/
noncomputable def i8L4Q16_4 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_16_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s16 x = i8L4S16 x + x * (i8L4Q16_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q16_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q16_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q16_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q16_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s16 i8Psi4s16N0 i8Psi4s16N1 i8Psi4s16N2 i8Psi4s16N3 i8Psi4s16N4 i8Psi4s16W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx,
    i13hw_m0 hx, i13hw_m00 hx, i13hw_m000 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S16 i8L4Q16_0 i8L4Q16_1 i8L4Q16_2 i8L4Q16_3 i8L4Q16_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽16⁾`. -/
noncomputable def i8L4R16 (x : ℝ) : ℝ :=
  x * (i8L4Q16_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q16_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q16_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q16_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q16_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R16 : Tendsto i8L4R16 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q16_0 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q16_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q16_1 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q16_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q16_2 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q16_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q16_3 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q16_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q16_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q16_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q16_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q16_3 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R16
  unfold i8L4Q16_4
  ring

/-- The singular part of `Ψ₄⁽17⁾` at `ξ = 0`. -/
noncomputable def i8L4S17 (x : ℝ) : ℝ :=
    6 - 4 * Real.log x + 2 * Real.log x ^ 2 - 2 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽17⁾`. -/
noncomputable def i8L4Q17_0 (x r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -29 / 2 - 2 * x ^ 3 - 3 / 4 * x ^ 4 + x ^ 5 / 8 + 7 / 2 * x ^ 2 + 13 / 8 * x +
      r_00m * x ^ 2 + r_00m * x ^ 4 + r_m * x ^ 5 - r_00m * x ^ 6 - 24 * r_000m * x ^ 2 -
      2 * r_00m * x ^ 5 + 2 * r_00m * x ^ 3 + 4 * r_00m * x + 4 * r_m * x + 4 * r_m * x ^ 2 +
      5 * r_m * x ^ 3 - 15 / 2 * r_0m * x ^ 2 - r_m * x ^ 6 / 4 + 25 / 4 * r_m * x ^ 4 +
      2 * r_00m * r_m * x ^ 3 + 2 * r_00m * r_m * x ^ 7 + 8 * r_00m * r_m * x ^ 4 +
      8 * r_00m * r_m * x ^ 6 + 12 * r_00m * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽17⁾`. -/
noncomputable def i8L4Q17_1 (x _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    9 + x ^ 4 / 2 - 3 * x ^ 2 + 2 * x ^ 3 - 5 / 2 * x - x ^ 5 / 4 + r_0m * x ^ 6 +
      r_m * x ^ 6 / 2 - r_0m * x ^ 2 - r_0m * x ^ 4 - 4 * r_0m * x - 4 * r_m * x ^ 3 -
      2 * r_0m * x ^ 3 + 2 * r_0m * x ^ 5 + 18 * r_00m * x ^ 2 - 9 / 2 * r_m * x ^ 4 -
      12 * r_0m * r_m * x ^ 5 - 8 * r_0m * r_m * x ^ 4 - 8 * r_0m * r_m * x ^ 6 -
      2 * r_0m * r_m * x ^ 3 - 2 * r_0m * r_m * x ^ 7

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽17⁾`. -/
noncomputable def i8L4Q17_2 (x _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    -2 + x ^ 2 - x ^ 3 - x / 4 + x ^ 5 / 4 + r_m * x ^ 4 + r_m ^ 2 * x ^ 3 + r_m ^ 2 * x ^ 7 -
      r_m * x ^ 6 - 6 * r_0m * x ^ 2 - 2 * r_m * x ^ 5 + 2 * r_m * x ^ 3 + 4 * r_m * x +
      4 * r_m * x ^ 2 + 4 * r_m ^ 2 * x ^ 4 + 4 * r_m ^ 2 * x ^ 6 + 6 * r_m ^ 2 * x ^ 5

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽17⁾`. -/
noncomputable def i8L4Q17_3 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽17⁾`. -/
noncomputable def i8L4Q17_4 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_17_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s17 x = i8L4S17 x + x * (i8L4Q17_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q17_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q17_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q17_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q17_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s17 i8Psi4s17N0 i8Psi4s17N1 i8Psi4s17N2 i8Psi4s17N3 i8Psi4s17N4 i8Psi4s17W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_m0 hx,
    i13hw_m00 hx, i13hw_m00m hx, i13hw_m0m0 hx, i13hw_mm00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S17 i8L4Q17_0 i8L4Q17_1 i8L4Q17_2 i8L4Q17_3 i8L4Q17_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽17⁾`. -/
noncomputable def i8L4R17 (x : ℝ) : ℝ :=
  x * (i8L4Q17_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q17_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q17_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q17_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q17_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R17 : Tendsto i8L4R17 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q17_0 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q17_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q17_1 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q17_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q17_2 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q17_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q17_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q17_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q17_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R17
  unfold i8L4Q17_3 i8L4Q17_4
  ring

/-- The singular part of `Ψ₄⁽18⁾` at `ξ = 0`. -/
noncomputable def i8L4S18 (x : ℝ) : ℝ :=
    -4 - 4 * Real.log x ^ 2 + 8 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽18⁾`. -/
noncomputable def i8L4Q18_0 (x r_00m r_0m r_m : ℝ) : ℝ :=
    18 + x ^ 4 - 6 * x ^ 2 - 5 * x + 4 * x ^ 3 - x ^ 5 / 2 + r_m * x ^ 6 - 9 * r_m * x ^ 4 -
      8 * r_0m * x - 8 * r_m * x ^ 3 - 4 * r_0m * x ^ 3 - 2 * r_0m * x ^ 2 - 2 * r_0m * x ^ 4 +
      2 * r_0m * x ^ 6 + 4 * r_0m * x ^ 5 + 36 * r_00m * x ^ 2 - 24 * r_0m * r_m * x ^ 5 -
      16 * r_0m * r_m * x ^ 4 - 16 * r_0m * r_m * x ^ 6 - 4 * r_0m * r_m * x ^ 3 -
      4 * r_0m * r_m * x ^ 7

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽18⁾`. -/
noncomputable def i8L4Q18_1 (x _r_00m r_0m r_m : ℝ) : ℝ :=
    -8 + x ^ 5 - x - 4 * x ^ 3 + 4 * x ^ 2 - 24 * r_0m * x ^ 2 - 8 * r_m * x ^ 5 -
      4 * r_m * x ^ 6 + 4 * r_m * x ^ 4 + 4 * r_m ^ 2 * x ^ 3 + 4 * r_m ^ 2 * x ^ 7 +
      8 * r_m * x ^ 3 + 16 * r_m * x + 16 * r_m * x ^ 2 + 16 * r_m ^ 2 * x ^ 4 +
      16 * r_m ^ 2 * x ^ 6 + 24 * r_m ^ 2 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽18⁾`. -/
noncomputable def i8L4Q18_2 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽18⁾`. -/
noncomputable def i8L4Q18_3 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽18⁾`. -/
noncomputable def i8L4Q18_4 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_18_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s18 x = i8L4S18 x + x * (i8L4Q18_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q18_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q18_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q18_3 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q18_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s18 i8Psi4s18N0 i8Psi4s18N1 i8Psi4s18N2 i8Psi4s18N3 i8Psi4s18N4 i8Psi4s18W
  simp only [hpl_zero, i13hw_00, i13hw_0m0 hx, i13hw_m0 hx, i13hw_m0m hx, i13hw_mm0 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S18 i8L4Q18_0 i8L4Q18_1 i8L4Q18_2 i8L4Q18_3 i8L4Q18_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽18⁾`. -/
noncomputable def i8L4R18 (x : ℝ) : ℝ :=
  x * (i8L4Q18_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q18_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q18_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q18_3 x (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q18_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x))

theorem tendsto_i8L4R18 : Tendsto i8L4R18 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q18_0 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q18_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q18_1 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q18_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q18_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q18_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R18
  unfold i8L4Q18_2 i8L4Q18_3 i8L4Q18_4
  ring

/-- The singular part of `Ψ₄⁽19⁾` at `ξ = 0`. -/
noncomputable def i8L4S19 (x : ℝ) : ℝ :=
    (-4 - 4 * Real.log x - 2 * Real.log x ^ 2 - 31 / 4 * x + x * Real.log x ^ 3) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽19⁾`. -/
noncomputable def i8L4Q19_0 (x r_00m _r_0m r_m : ℝ) : ℝ :=
    -5 / 2 - r_m / 2 + x ^ 3 / 4 + 7 / 2 * x ^ 2 + 7 / 4 * x - 15 * r_m * x ^ 2 -
      12 * r_00m * x ^ 2 - 8 * r_m * x - 8 * r_m * x ^ 3 - r_m * x ^ 4 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽19⁾`. -/
noncomputable def i8L4Q19_1 (x _r_00m r_0m r_m : ℝ) : ℝ :=
    3 - r_m - 3 * x ^ 2 + 4 * x - x ^ 3 / 2 + r_m * x ^ 4 - 8 * r_m * x + 8 * r_m * x ^ 3 +
      12 * r_0m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽19⁾`. -/
noncomputable def i8L4Q19_2 (x _r_00m _r_0m r_m : ℝ) : ℝ :=
    -1 + x ^ 2 + x ^ 3 / 2 - r_m - x / 2 - r_m * x ^ 4 - 6 * r_m * x ^ 2 - 4 * r_m * x -
      4 * r_m * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽19⁾`. -/
noncomputable def i8L4Q19_3 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽19⁾`. -/
noncomputable def i8L4Q19_4 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_19_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s19 x = i8L4S19 x + x * (i8L4Q19_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q19_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q19_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q19_3 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q19_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s19 i8Psi4s19N0 i8Psi4s19N1 i8Psi4s19N2 i8Psi4s19N3 i8Psi4s19N4 i8Psi4s19W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0m0 hx, i13hw_m0 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S19 i8L4Q19_0 i8L4Q19_1 i8L4Q19_2 i8L4Q19_3 i8L4Q19_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽19⁾`. -/
noncomputable def i8L4R19 (x : ℝ) : ℝ :=
  x * (i8L4Q19_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q19_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q19_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q19_3 x (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q19_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x))

theorem tendsto_i8L4R19 : Tendsto i8L4R19 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q19_0 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q19_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q19_1 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q19_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q19_2 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q19_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q19_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q19_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q19_2 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R19
  unfold i8L4Q19_3 i8L4Q19_4
  ring

/-- The singular part of `Ψ₄⁽20⁾` at `ξ = 0`. -/
noncomputable def i8L4S20 (x : ℝ) : ℝ :=
    (50 + Real.log x ^ 3 - π ^ 2 + 9 * Real.log x ^ 2 + 12 * x + 34 * Real.log x -
      6 * x * Real.log x ^ 2 + 8 * Real.log x * x - 10 / 3 * x * Real.log x ^ 3 -
      3 / 4 * x * Real.log x ^ 4 - Real.log x * π ^ 2 / 3 + π ^ 2 * x * Real.log x ^ 2 / 2 +
      2 / 3 * Real.log x * π ^ 2 * x) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽20⁾`. -/
noncomputable def i8L4Q20_0 (x r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    19 - 19 / 8 * x - 5 / 3 * π ^ 2 - 5 / 4 * x ^ 3 - 4 * r_00m * x ^ 2 + 5 * r_0m * x ^ 4 +
      12 * r_0m * x + 20 * r_0m * x ^ 3 + 27 * r_0m * x ^ 2 + 36 * r_000m * x ^ 2 -
      5 / 12 * π ^ 2 * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽20⁾`. -/
noncomputable def i8L4Q20_1 (x _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -9 + π ^ 2 + 3 * x ^ 3 + 6 * x ^ 2 - 5 / 4 * x - 36 * r_00m * x ^ 2 - 27 * r_m * x ^ 2 -
      20 * r_m * x ^ 3 - 12 * r_0m * x ^ 3 - 12 * r_m * x - 5 * r_m * x ^ 4 - 4 * r_0m * x ^ 2 -
      2 * r_0m * x ^ 4 + 4 * r_0m * x + π ^ 2 * x / 6

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽20⁾`. -/
noncomputable def i8L4Q20_2 (x _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    9 - x ^ 3 - 4 * x ^ 2 + 19 / 4 * x - 4 * r_m * x + 2 * r_m * x ^ 4 + 6 * r_m * x ^ 2 +
      12 * r_0m * x ^ 2 + 12 * r_m * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽20⁾`. -/
noncomputable def i8L4Q20_3 (x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    -3 - x / 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽20⁾`. -/
noncomputable def i8L4Q20_4 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_20_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s20 x = i8L4S20 x + x * (i8L4Q20_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q20_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q20_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q20_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q20_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s20 i8Psi4s20N0 i8Psi4s20N1 i8Psi4s20N2 i8Psi4s20N3 i8Psi4s20N4 i8Psi4s20W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx,
    i13hw_m0 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S20 i8L4Q20_0 i8L4Q20_1 i8L4Q20_2 i8L4Q20_3 i8L4Q20_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽20⁾`. -/
noncomputable def i8L4R20 (x : ℝ) : ℝ :=
  x * (i8L4Q20_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q20_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q20_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q20_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q20_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R20 : Tendsto i8L4R20 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q20_0 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q20_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q20_1 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q20_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q20_2 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q20_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q20_3 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q20_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q20_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q20_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q20_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q20_3 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R20
  unfold i8L4Q20_4
  ring

/-- The singular part of `Ψ₄⁽21⁾` at `ξ = 0`. -/
noncomputable def i8L4S21 (x : ℝ) : ℝ :=
    (-50 + π ^ 2 - Real.log x ^ 3 - 34 * Real.log x - 9 * Real.log x ^ 2 - 1473 / 16 * x +
      10 * x * Real.log x ^ 2 + Real.log x * π ^ 2 / 3 + 7 / 8 * x * Real.log x ^ 4 +
      13 / 3 * x * Real.log x ^ 3 + 59 / 24 * π ^ 2 * x - Real.log x * π ^ 2 * x -
      7 / 12 * π ^ 2 * x * Real.log x ^ 2) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽21⁾`. -/
noncomputable def i8L4Q21_0 (x r_0000m r_000m r_000mm r_00m r_00m0m _r_00mm r_0m _r_0mm r_m : ℝ) : ℝ
    :=
    -195 / 8 + 29 * x - 259 / 8 * x ^ 2 - 111 / 8 * r_m - 5 / 8 * x ^ 5 - x ^ 4 / 4 +
      7 / 4 * π ^ 2 + 73 / 16 * x ^ 3 - 144 * r_000mm * x ^ 2 - 92 * r_m * x -
      36 * r_0000m * x ^ 2 - 24 * r_00m0m * x ^ 2 - 22 * r_000m * x ^ 2 - 12 * r_0m * x -
      2 * r_0m * x ^ 4 + 3 * r_0m * x ^ 3 + 3 * r_m * x ^ 5 + 11 * r_0m * x ^ 5 +
      41 * r_m * x ^ 3 + 84 * r_00m * x ^ 2 + 120 * r_0m * x ^ 2 - 123 / 4 * r_m * x ^ 2 -
      37 / 8 * r_m * x ^ 4 - 11 / 12 * π ^ 2 * x ^ 2 - 5 / 24 * π ^ 2 * x ^ 3 - π ^ 2 * x / 12 +
      5 / 2 * r_0m * x ^ 6 + 5 / 4 * r_m * x ^ 6 + 5 / 12 * π ^ 2 * r_m -
      54 * r_0m * r_m * x ^ 5 - 32 * r_0m * r_m * x ^ 4 - 32 * r_0m * r_m * x ^ 6 -
      5 * r_0m * r_m * x ^ 3 - 5 * r_0m * r_m * x ^ 7 + 2 * π ^ 2 * r_00m * x ^ 2 +
      5 / 12 * π ^ 2 * r_m * x ^ 4 + 8 / 3 * π ^ 2 * r_m * x + 8 / 3 * π ^ 2 * r_m * x ^ 3 +
      9 / 2 * π ^ 2 * r_m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽21⁾`. -/
noncomputable def i8L4Q21_1 (x _r_0000m r_000m _r_000mm r_00m _r_00m0m r_00mm r_0m _r_0mm r_m : ℝ) :
    ℝ :=
    65 / 4 - 121 / 8 * x ^ 3 - 47 / 4 * r_m - 3 / 2 * π ^ 2 + 3 / 2 * x ^ 5 + 7 / 2 * x ^ 4 +
      183 / 4 * x ^ 2 + 201 / 8 * x + π ^ 2 * x ^ 2 / 2 - r_0m * x ^ 6 - 138 * r_m * x ^ 2 -
      72 * r_0m * x ^ 2 - 72 * r_m * x - 48 * r_m * x ^ 3 - 24 * r_m * x ^ 5 - 6 * r_0m * x ^ 5 -
      4 * r_0m * x + 5 * r_m ^ 2 * x ^ 3 + 5 * r_m ^ 2 * x ^ 7 + 9 * r_0m * x ^ 4 +
      12 * r_0m ^ 2 * x ^ 5 + 18 * r_0m * x ^ 3 + 22 * r_00m * x ^ 2 + 32 * r_m ^ 2 * x ^ 4 +
      32 * r_m ^ 2 * x ^ 6 + 36 * r_000m * x ^ 2 + 54 * r_m ^ 2 * x ^ 5 + 96 * r_00mm * x ^ 2 -
      11 / 2 * r_m * x ^ 6 - 3 / 4 * π ^ 2 * x + π ^ 2 * r_m / 6 + π ^ 2 * x ^ 3 / 12 +
      45 / 4 * r_m * x ^ 4 - 16 * r_0m * r_m * x ^ 4 - 2 * π ^ 2 * r_0m * x ^ 2 -
      2 * r_0m * r_m * x ^ 3 + 2 * r_0m * r_m * x ^ 7 + 16 * r_0m * r_m * x ^ 6 -
      4 / 3 * π ^ 2 * r_m * x ^ 3 - π ^ 2 * r_m * x ^ 4 / 6 + 4 / 3 * π ^ 2 * r_m * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽21⁾`. -/
noncomputable def i8L4Q21_2 (x _r_0000m _r_000m _r_000mm r_00m _r_00m0m _r_00mm r_0m r_0mm r_m : ℝ)
    : ℝ :=
    -31 / 4 - 2 * x ^ 4 - 95 / 4 * x ^ 2 - 15 / 4 * r_m - x ^ 5 / 2 + 9 / 4 * x +
      103 / 8 * x ^ 3 - 48 * r_0mm * x ^ 2 - 24 * r_m * x - 18 * r_00m * x ^ 2 -
      16 * r_m ^ 2 * x ^ 6 - 4 * r_0m * x ^ 2 - 2 * r_m ^ 2 * x ^ 7 + 2 * r_m * x ^ 6 +
      2 * r_m ^ 2 * x ^ 3 + 12 * r_m * x ^ 3 + 12 * r_m * x ^ 5 + 16 * r_m ^ 2 * x ^ 4 -
      119 / 4 * r_m * x ^ 4 + 63 / 2 * r_m * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽21⁾`. -/
noncomputable def i8L4Q21_3 (x _r_0000m _r_000m _r_000mm _r_00m _r_00m0m _r_00mm r_0m _r_0mm r_m :
    ℝ) : ℝ :=
    9 / 2 - 3 / 2 * x ^ 2 - r_m / 2 - x ^ 3 / 4 + 9 / 4 * x + r_m * x ^ 4 / 2 - 4 * r_m * x +
      4 * r_m * x ^ 3 + 6 * r_0m * x ^ 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽21⁾`. -/
noncomputable def i8L4Q21_4 (_x _r_0000m _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m
    : ℝ) : ℝ :=
    0

theorem i8L4_21_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s21 x = i8L4S21 x + x * (i8L4Q21_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q21_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q21_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q21_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q21_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s21 i8Psi4s21N0 i8Psi4s21N1 i8Psi4s21N2 i8Psi4s21N3 i8Psi4s21N4 i8Psi4s21W
    i8Psi4s21N1c0 i8Psi4s21N1c1 i8Psi4s21N3c0 i8Psi4s21N3c1 i8Psi4s21N4c0 i8Psi4s21N4c1
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_000m0 hx, i13hw_00m0 hx, i13hw_00m00
    hx, i13hw_00mm0 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_0m000 hx, i13hw_0m0m hx, i13hw_0m0m0 hx,
    i13hw_0mm0 hx, i13hw_0mm00 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_m000 hx, i13hw_m00m hx,
    i13hw_m0m hx, i13hw_m0m0 hx, i13hw_mm0 hx, i13hw_mm00 hx, i8hw_0m00m hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_000mm h0, i13hpl_rho_00m h0,
    i13hpl_rho_00m0m h0, i13hpl_rho_00mm h0, i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S21 i8L4Q21_0 i8L4Q21_1 i8L4Q21_2 i8L4Q21_3 i8L4Q21_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽21⁾`. -/
noncomputable def i8L4R21 (x : ℝ) : ℝ :=
  x * (i8L4Q21_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q21_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q21_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q21_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q21_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R21 : Tendsto i8L4R21 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q21_0 (v 0) (v 2) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57)
      (v 66)) (by
      unfold i8L4Q21_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q21_1 (v 0) (v 2) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57)
      (v 66)) (by
      unfold i8L4Q21_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q21_2 (v 0) (v 2) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57)
      (v 66)) (by
      unfold i8L4Q21_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q21_3 (v 0) (v 2) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57)
      (v 66)) (by
      unfold i8L4Q21_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q21_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho
    [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q21_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q21_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q21_3 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R21
  unfold i8L4Q21_4
  ring

/-- The singular part of `Ψ₄⁽22⁾` at `ξ = 0`. -/
noncomputable def i8L4S22 (x : ℝ) : ℝ :=
    (32 - 8 * zeta3 - 4 / 3 * π ^ 2 - π ^ 2 ^ 2 / 20 + 32 * Real.log x * x +
      8 * Real.log x * x * zeta3 + Real.log x * x * π ^ 2 ^ 2 / 20 +
      4 / 3 * Real.log x * π ^ 2 * x) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽22⁾`. -/
noncomputable def i8L4Q22_0 (x : ℝ) : ℝ :=
    32 - 16 * x - 8 * zeta3 - 4 / 3 * π ^ 2 - π ^ 2 ^ 2 / 20 - 4 * x * zeta3 - 2 / 3 * π ^ 2 * x -
      x * π ^ 2 ^ 2 / 40

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽22⁾`. -/
noncomputable def i8L4Q22_1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽22⁾`. -/
noncomputable def i8L4Q22_2 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽22⁾`. -/
noncomputable def i8L4Q22_3 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽22⁾`. -/
noncomputable def i8L4Q22_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_22_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s22 x = i8L4S22 x + x * (i8L4Q22_0 x + Real.log x * i8L4Q22_1 x +
      Real.log x ^ 2 * i8L4Q22_2 x + Real.log x ^ 3 * i8L4Q22_3 x +
      Real.log x ^ 4 * i8L4Q22_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s22 i8Psi4s22N0 i8Psi4s22N1 i8Psi4s22N2 i8Psi4s22N3 i8Psi4s22N4 i8Psi4s22W
  simp only [hpl_zero]

  unfold i8L4S22 i8L4Q22_0 i8L4Q22_1 i8L4Q22_2 i8L4Q22_3 i8L4Q22_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽22⁾`. -/
noncomputable def i8L4R22 (x : ℝ) : ℝ :=
  x * (i8L4Q22_0 x + Real.log x * i8L4Q22_1 x + Real.log x ^ 2 * i8L4Q22_2 x +
    Real.log x ^ 3 * i8L4Q22_3 x + Real.log x ^ 4 * i8L4Q22_4 x)

theorem tendsto_i8L4R22 : Tendsto i8L4R22 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q22_0 (v 0)) (by
      unfold i8L4Q22_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q22_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R22
  unfold i8L4Q22_1 i8L4Q22_2 i8L4Q22_3 i8L4Q22_4
  ring

/-- The singular part of `Ψ₄⁽23⁾` at `ξ = 0`. -/
noncomputable def i8L4S23 (x : ℝ) : ℝ :=
    (16 - 4 * zeta3 + 16 * Real.log x - 2 / 3 * π ^ 2 - 8 * x * Real.log x ^ 2 -
      4 * Real.log x * zeta3 - 2 / 3 * Real.log x * π ^ 2 + 2 * x * zeta3 * Real.log x ^ 2 +
      π ^ 2 * x * Real.log x ^ 2 / 3) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽23⁾`. -/
noncomputable def i8L4Q23_0 (x : ℝ) : ℝ :=
    -16 - 4 * x + 4 * zeta3 + 2 / 3 * π ^ 2 + x * zeta3 + π ^ 2 * x / 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽23⁾`. -/
noncomputable def i8L4Q23_1 (x : ℝ) : ℝ :=
    16 - 4 * zeta3 + 8 * x - 2 / 3 * π ^ 2 - 2 * x * zeta3 - π ^ 2 * x / 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽23⁾`. -/
noncomputable def i8L4Q23_2 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽23⁾`. -/
noncomputable def i8L4Q23_3 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽23⁾`. -/
noncomputable def i8L4Q23_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_23_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s23 x = i8L4S23 x + x * (i8L4Q23_0 x + Real.log x * i8L4Q23_1 x +
      Real.log x ^ 2 * i8L4Q23_2 x + Real.log x ^ 3 * i8L4Q23_3 x +
      Real.log x ^ 4 * i8L4Q23_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s23 i8Psi4s23N0 i8Psi4s23N1 i8Psi4s23N2 i8Psi4s23N3 i8Psi4s23N4 i8Psi4s23W
  simp only [hpl_zero, i13hw_00]

  unfold i8L4S23 i8L4Q23_0 i8L4Q23_1 i8L4Q23_2 i8L4Q23_3 i8L4Q23_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽23⁾`. -/
noncomputable def i8L4R23 (x : ℝ) : ℝ :=
  x * (i8L4Q23_0 x + Real.log x * i8L4Q23_1 x + Real.log x ^ 2 * i8L4Q23_2 x +
    Real.log x ^ 3 * i8L4Q23_3 x + Real.log x ^ 4 * i8L4Q23_4 x)

theorem tendsto_i8L4R23 : Tendsto i8L4R23 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q23_0 (v 0)) (by
      unfold i8L4Q23_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q23_1 (v 0)) (by
      unfold i8L4Q23_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q23_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q23_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R23
  unfold i8L4Q23_2 i8L4Q23_3 i8L4Q23_4
  ring

/-- The singular part of `Ψ₄⁽24⁾` at `ξ = 0`. -/
noncomputable def i8L4S24 (x : ℝ) : ℝ :=
    8 * zeta3 + 4 / 3 * π ^ 2 - 8 * Real.log x * zeta3 - 4 / 3 * Real.log x * π ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽24⁾`. -/
noncomputable def i8L4Q24_0 (x r_0m r_m : ℝ) : ℝ :=
    -4 * zeta3 - 2 / 3 * π ^ 2 - 2 * zeta3 * x ^ 3 + 2 * x * zeta3 - π ^ 2 * x ^ 3 / 3 +
      π ^ 2 * x / 3 - 8 * r_0m * zeta3 * x ^ 2 + 2 * π ^ 2 * r_m * x ^ 2 +
      4 * r_m * zeta3 * x ^ 4 + 8 * r_m * x * zeta3 + 8 * r_m * zeta3 * x ^ 3 +
      12 * r_m * zeta3 * x ^ 2 - 4 / 3 * π ^ 2 * r_0m * x ^ 2 + 2 / 3 * π ^ 2 * r_m * x ^ 4 +
      4 / 3 * π ^ 2 * r_m * x + 4 / 3 * π ^ 2 * r_m * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽24⁾`. -/
noncomputable def i8L4Q24_1 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽24⁾`. -/
noncomputable def i8L4Q24_2 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽24⁾`. -/
noncomputable def i8L4Q24_3 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽24⁾`. -/
noncomputable def i8L4Q24_4 (_x _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_24_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s24 x = i8L4S24 x + x * (i8L4Q24_0 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q24_1 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q24_2 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q24_3 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q24_4 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s24 i8Psi4s24N0 i8Psi4s24N1 i8Psi4s24N2 i8Psi4s24N3 i8Psi4s24N4 i8Psi4s24W
  simp only [hpl_zero]
  simp only [i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S24 i8L4Q24_0 i8L4Q24_1 i8L4Q24_2 i8L4Q24_3 i8L4Q24_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽24⁾`. -/
noncomputable def i8L4R24 (x : ℝ) : ℝ :=
  x * (i8L4Q24_0 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q24_1 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q24_2 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q24_3 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q24_4 x (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R24 : Tendsto i8L4R24 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q24_0 (v 0) (v 43) (v 66)) (by
      unfold i8L4Q24_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q24_0 x (i13Rho [zero, negOne]
    x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R24
  unfold i8L4Q24_1 i8L4Q24_2 i8L4Q24_3 i8L4Q24_4
  ring

/-- The singular part of `Ψ₄⁽25⁾` at `ξ = 0`. -/
noncomputable def i8L4S25 (x : ℝ) : ℝ :=
    (8 + 4 * Real.log x ^ 2 + 8 * Real.log x - π ^ 2 / 3 - 4 / 3 * x * Real.log x ^ 3 -
      Real.log x * π ^ 2 / 3 - π ^ 2 * Real.log x ^ 2 / 6 + π ^ 2 * x * Real.log x ^ 3 / 18) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽25⁾`. -/
noncomputable def i8L4Q25_0 (x : ℝ) : ℝ :=
    8 + x - π ^ 2 / 3 - π ^ 2 * x / 24

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽25⁾`. -/
noncomputable def i8L4Q25_1 (x : ℝ) : ℝ :=
    -8 - 2 * x + π ^ 2 / 3 + π ^ 2 * x / 12

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽25⁾`. -/
noncomputable def i8L4Q25_2 (x : ℝ) : ℝ :=
    4 + 2 * x - π ^ 2 / 6 - π ^ 2 * x / 12

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽25⁾`. -/
noncomputable def i8L4Q25_3 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽25⁾`. -/
noncomputable def i8L4Q25_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_25_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s25 x = i8L4S25 x + x * (i8L4Q25_0 x + Real.log x * i8L4Q25_1 x +
      Real.log x ^ 2 * i8L4Q25_2 x + Real.log x ^ 3 * i8L4Q25_3 x +
      Real.log x ^ 4 * i8L4Q25_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s25 i8Psi4s25N0 i8Psi4s25N1 i8Psi4s25N2 i8Psi4s25N3 i8Psi4s25N4 i8Psi4s25W
  simp only [hpl_zero, i13hw_00, i13hw_000]

  unfold i8L4S25 i8L4Q25_0 i8L4Q25_1 i8L4Q25_2 i8L4Q25_3 i8L4Q25_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽25⁾`. -/
noncomputable def i8L4R25 (x : ℝ) : ℝ :=
  x * (i8L4Q25_0 x + Real.log x * i8L4Q25_1 x + Real.log x ^ 2 * i8L4Q25_2 x +
    Real.log x ^ 3 * i8L4Q25_3 x + Real.log x ^ 4 * i8L4Q25_4 x)

theorem tendsto_i8L4R25 : Tendsto i8L4R25 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q25_0 (v 0)) (by
      unfold i8L4Q25_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q25_1 (v 0)) (by
      unfold i8L4Q25_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q25_2 (v 0)) (by
      unfold i8L4Q25_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q25_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q25_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q25_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R25
  unfold i8L4Q25_3 i8L4Q25_4
  ring

/-- The singular part of `Ψ₄⁽26⁾` at `ξ = 0`. -/
noncomputable def i8L4S26 (x : ℝ) : ℝ :=
    16 - 16 * Real.log x + 8 * Real.log x ^ 2 - 2 / 3 * π ^ 2 - π ^ 2 * Real.log x ^ 2 / 3 +
      2 / 3 * Real.log x * π ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽26⁾`. -/
noncomputable def i8L4Q26_0 (x r_00m r_0m _r_m : ℝ) : ℝ :=
    -20 - 2 * x ^ 3 + 4 * x ^ 2 + 12 * x + 5 / 6 * π ^ 2 - 32 * r_00m * x ^ 2 +
      8 * r_0m * x ^ 4 + 16 * r_0m * x + 16 * r_0m * x ^ 3 + 24 * r_0m * x ^ 2 - π ^ 2 * x / 2 -
      π ^ 2 * x ^ 2 / 6 + π ^ 2 * x ^ 3 / 12 - π ^ 2 * r_0m * x ^ 2 - 2 / 3 * π ^ 2 * r_0m * x -
      2 / 3 * π ^ 2 * r_0m * x ^ 3 - π ^ 2 * r_0m * x ^ 4 / 3 + 4 / 3 * π ^ 2 * r_00m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽26⁾`. -/
noncomputable def i8L4Q26_1 (x _r_00m r_0m r_m : ℝ) : ℝ :=
    8 - 4 * x + 4 * x ^ 3 - π ^ 2 / 3 - 24 * r_m * x ^ 2 - 16 * r_m * x - 16 * r_m * x ^ 3 -
      8 * r_m * x ^ 4 + 16 * r_0m * x ^ 2 - π ^ 2 * x ^ 3 / 6 + π ^ 2 * x / 6 +
      π ^ 2 * r_m * x ^ 2 - 2 / 3 * π ^ 2 * r_0m * x ^ 2 + π ^ 2 * r_m * x ^ 4 / 3 +
      2 / 3 * π ^ 2 * r_m * x + 2 / 3 * π ^ 2 * r_m * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽26⁾`. -/
noncomputable def i8L4Q26_2 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽26⁾`. -/
noncomputable def i8L4Q26_3 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽26⁾`. -/
noncomputable def i8L4Q26_4 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_26_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s26 x = i8L4S26 x + x * (i8L4Q26_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q26_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q26_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q26_3 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q26_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s26 i8Psi4s26N0 i8Psi4s26N1 i8Psi4s26N2 i8Psi4s26N3 i8Psi4s26N4 i8Psi4s26W
  simp only [hpl_zero, i13hw_00, i13hw_0m0 hx, i13hw_m0 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S26 i8L4Q26_0 i8L4Q26_1 i8L4Q26_2 i8L4Q26_3 i8L4Q26_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽26⁾`. -/
noncomputable def i8L4R26 (x : ℝ) : ℝ :=
  x * (i8L4Q26_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q26_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q26_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q26_3 x (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q26_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x))

theorem tendsto_i8L4R26 : Tendsto i8L4R26 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q26_0 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q26_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q26_1 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q26_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q26_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q26_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R26
  unfold i8L4Q26_2 i8L4Q26_3 i8L4Q26_4
  ring

/-- The regular parts of group 1. -/
noncomputable def i8L4RG1 (x : ℝ) : ℝ :=
  i8L4R11 x + i8L4R12 x + i8L4R13 x + i8L4R14 x + i8L4R15 x + i8L4R16 x + i8L4R17 x +
    i8L4R18 x + i8L4R19 x + i8L4R20 x + i8L4R21 x + i8L4R22 x + i8L4R23 x + i8L4R24 x +
    i8L4R25 x + i8L4R26 x

theorem tendsto_i8L4RG1 : Tendsto i8L4RG1 (𝓝[>] 0) (𝓝 0) := by
  have H := (((((((((((((((tendsto_i8L4R11.add tendsto_i8L4R12).add tendsto_i8L4R13).add
    tendsto_i8L4R14).add tendsto_i8L4R15).add tendsto_i8L4R16).add tendsto_i8L4R17).add
    tendsto_i8L4R18).add tendsto_i8L4R19).add tendsto_i8L4R20).add tendsto_i8L4R21).add
    tendsto_i8L4R22).add tendsto_i8L4R23).add tendsto_i8L4R24).add tendsto_i8L4R25).add
    tendsto_i8L4R26)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
