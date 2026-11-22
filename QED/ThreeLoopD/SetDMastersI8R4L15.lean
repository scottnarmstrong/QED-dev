/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L14
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 15

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_140k2_eq`, `QED.ThreeLoopD.tendsto_i8L4RG15` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽140k2⁾` at `ξ = 0`. -/
noncomputable def i8L4S140k2 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽140k2⁾`. -/
noncomputable def i8L4Q140k2_0 (x r_00011 r_001 r_00101 r_0011 r_01 _r_011 r_1 : ℝ) : ℝ :=
    -3 + x ^ 5 / 8 + 3 / 2 * x + 9 / 4 * x ^ 4 + 31 / 4 * x ^ 2 + 85 / 8 * x ^ 3 +
      r_1 * x ^ 6 / 2 - r_01 * x ^ 6 - 216 * r_00011 * x ^ 2 - 72 * r_00101 * x ^ 2 -
      24 * r_0011 * x ^ 3 - 21 * r_1 * x ^ 3 - 17 * r_01 * x ^ 4 - 12 * r_01 ^ 2 * x ^ 6 -
      10 * r_01 * x ^ 5 - 8 * r_1 * x ^ 2 - 4 * r_0011 * x ^ 4 - 2 * r_01 ^ 2 * x ^ 7 +
      2 * r_001 * x ^ 6 + 4 * r_01 ^ 2 * x ^ 4 + 7 * r_1 * x ^ 5 + 8 * r_0011 * x +
      10 * r_01 ^ 2 * x ^ 5 + 16 * r_001 * x ^ 5 + 18 * r_01 * x ^ 3 + 20 * r_0011 * x ^ 2 +
      22 * r_001 * x ^ 2 + 22 * r_001 * x ^ 4 + 28 * r_001 * x ^ 3 + 37 * r_01 * x ^ 2 +
      43 / 2 * r_1 * x ^ 4 - 20 * r_001 * r_1 * x ^ 5 - 8 * r_001 * r_1 * x ^ 4 +
      4 * r_001 * r_1 * x ^ 7 + 24 * r_001 * r_01 * x ^ 5 + 24 * r_001 * r_1 * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽140k2⁾`. -/
noncomputable def i8L4Q140k2_1 (x _r_00011 r_001 _r_00101 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    6 + 9 * x + 21 * x ^ 2 + 3 / 2 * x ^ 3 + r_1 * x ^ 4 - 30 * r_01 * x ^ 2 - 29 * r_1 * x ^ 2 -
      20 * r_011 * x ^ 2 - 8 * r_011 * x + 4 * r_011 * x ^ 4 + 8 * r_001 * x ^ 2 +
      24 * r_011 * x ^ 3 + 28 * r_1 * x ^ 3 + 48 * r_0011 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽140k2⁾`. -/
noncomputable def i8L4Q140k2_2 (x _r_00011 _r_001 _r_00101 _r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -2 - 4 * x - 25 / 4 * x ^ 3 - 17 / 2 * x ^ 2 - 5 / 2 * x ^ 4 - x ^ 5 / 4 - r_1 * x ^ 6 -
      r_1 ^ 2 * x ^ 7 - 12 * r_011 * x ^ 2 - 8 * r_1 * x ^ 4 - 8 * r_1 * x ^ 5 -
      6 * r_1 ^ 2 * x ^ 6 - 4 * r_01 * x ^ 2 - 2 * r_1 * x ^ 3 + 2 * r_1 ^ 2 * x ^ 4 +
      5 * r_1 ^ 2 * x ^ 5 + 19 * r_1 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽140k2⁾`. -/
noncomputable def i8L4Q140k2_3 (_x _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽140k2⁾`. -/
noncomputable def i8L4Q140k2_4 (_x _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_140k2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s140k2 x = i8L4S140k2 x + x * (i8L4Q140k2_0 x (i13Rho [zero, zero, zero, one, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q140k2_1 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one]
      x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q140k2_2 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
      one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q140k2_3 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
      one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q140k2_4 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
      one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s140k2 i8Psi4s140k2N0 i8Psi4s140k2N1 i8Psi4s140k2N2 i8Psi4s140k2N3 i8Psi4s140k2N4
    i8Psi4s140k2W
  simp only [hpl_zero, i13hw_00, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_01010 hx,
    i13hw_01100 hx, i13hw_10 hx, i13hw_100 hx, i13hw_1010 hx, i13hw_1100 hx]
  simp only [i13hpl_rho_00011 h0, i13hpl_rho_001 h0, i8hpl_rho_00101 h0, i13hpl_rho_0011 h0,
    i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L4S140k2 i8L4Q140k2_0 i8L4Q140k2_1 i8L4Q140k2_2 i8L4Q140k2_3 i8L4Q140k2_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽140k2⁾`. -/
noncomputable def i8L4R140k2 (x : ℝ) : ℝ :=
  x * (i8L4Q140k2_0 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q140k2_1 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q140k2_2 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q140k2_3 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q140k2_4 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R140k2 : Tendsto i8L4R140k2 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q140k2_0 (v 0) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v 65))
      (by
      unfold i8L4Q140k2_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q140k2_1 (v 0) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v 65))
      (by
      unfold i8L4Q140k2_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q140k2_2 (v 0) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v 65))
      (by
      unfold i8L4Q140k2_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q140k2_0 x (i13Rho [zero,
    zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x)
    (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
    [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q140k2_1 x (i13Rho [zero, zero, zero,
      one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho
      [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q140k2_2 x (i13Rho [zero, zero, zero,
      one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho
      [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R140k2
  unfold i8L4Q140k2_3 i8L4Q140k2_4
  ring

/-- The singular part of `Ψ₄⁽141⁾` at `ξ = 0`. -/
noncomputable def i8L4S141 (x : ℝ) : ℝ :=
    (1 + Real.log x + Real.log x ^ 2 / 2 + Real.log x ^ 3 / 6 + x * Real.log x ^ 4 / 24) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽141⁾`. -/
noncomputable def i8L4Q141_0 (x : ℝ) : ℝ :=
    -1 + x / 16

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽141⁾`. -/
noncomputable def i8L4Q141_1 (x : ℝ) : ℝ :=
    1 - x / 8

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽141⁾`. -/
noncomputable def i8L4Q141_2 (x : ℝ) : ℝ :=
    -1 / 2 + x / 8

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽141⁾`. -/
noncomputable def i8L4Q141_3 (x : ℝ) : ℝ :=
    1 / 6 - x / 12

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽141⁾`. -/
noncomputable def i8L4Q141_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_141_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s141 x = i8L4S141 x + x * (i8L4Q141_0 x + Real.log x * i8L4Q141_1 x +
      Real.log x ^ 2 * i8L4Q141_2 x + Real.log x ^ 3 * i8L4Q141_3 x +
      Real.log x ^ 4 * i8L4Q141_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s141 i8Psi4s141N0 i8Psi4s141N1 i8Psi4s141N2 i8Psi4s141N3 i8Psi4s141N4 i8Psi4s141W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000]

  unfold i8L4S141 i8L4Q141_0 i8L4Q141_1 i8L4Q141_2 i8L4Q141_3 i8L4Q141_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽141⁾`. -/
noncomputable def i8L4R141 (x : ℝ) : ℝ :=
  x * (i8L4Q141_0 x + Real.log x * i8L4Q141_1 x + Real.log x ^ 2 * i8L4Q141_2 x +
    Real.log x ^ 3 * i8L4Q141_3 x + Real.log x ^ 4 * i8L4Q141_4 x)

theorem tendsto_i8L4R141 : Tendsto i8L4R141 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q141_0 (v 0)) (by
      unfold i8L4Q141_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q141_1 (v 0)) (by
      unfold i8L4Q141_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q141_2 (v 0)) (by
      unfold i8L4Q141_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q141_3 (v 0)) (by
      unfold i8L4Q141_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q141_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q141_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q141_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q141_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R141
  unfold i8L4Q141_4
  ring

/-- The singular part of `Ψ₄⁽142⁾` at `ξ = 0`. -/
noncomputable def i8L4S142 (x : ℝ) : ℝ :=
    (-1 - Real.log x - Real.log x ^ 2 / 2 - Real.log x ^ 3 / 6 + x / 32 -
      x * Real.log x ^ 4 / 48) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽142⁾`. -/
noncomputable def i8L4Q142_0 (x r_0000m _r_000m r_00m _r_0m r_m : ℝ) : ℝ :=
    27 / 16 - r_m / 16 - x / 16 - x ^ 2 / 16 + x ^ 3 / 32 + r_00m * x ^ 2 / 2 +
      2 * r_0000m * x ^ 2 - r_m * x ^ 4 / 16 + r_m * x ^ 2 / 8

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽142⁾`. -/
noncomputable def i8L4Q142_1 (x _r_0000m r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    -13 / 8 - r_m / 8 - x ^ 3 / 16 + x ^ 2 / 8 + x / 16 - 2 * r_000m * x ^ 2 -
      r_0m * x ^ 2 / 2 + r_m * x ^ 4 / 8

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽142⁾`. -/
noncomputable def i8L4Q142_2 (x _r_0000m _r_000m r_00m _r_0m r_m : ℝ) : ℝ :=
    7 / 8 - r_m / 8 - x / 8 - x ^ 2 / 8 + x ^ 3 / 16 + r_00m * x ^ 2 - r_m * x ^ 4 / 8 +
      r_m * x ^ 2 / 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽142⁾`. -/
noncomputable def i8L4Q142_3 (x _r_0000m _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    -1 / 4 - r_m / 12 - x ^ 3 / 24 + x ^ 2 / 12 + x / 24 - r_0m * x ^ 2 / 3 + r_m * x ^ 4 / 12

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽142⁾`. -/
noncomputable def i8L4Q142_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_142_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s142 x = i8L4S142 x + x * (i8L4Q142_0 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x * i8L4Q142_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q142_2 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q142_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)
      + Real.log x ^ 4 * i8L4Q142_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s142 i8Psi4s142N0 i8Psi4s142N1 i8Psi4s142N2 i8Psi4s142N3 i8Psi4s142N4 i8Psi4s142W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_000m0 hx, i13hw_00m0 hx, i13hw_00m00
    hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_0m000 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_m000 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S142 i8L4Q142_0 i8L4Q142_1 i8L4Q142_2 i8L4Q142_3 i8L4Q142_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽142⁾`. -/
noncomputable def i8L4R142 (x : ℝ) : ℝ :=
  x * (i8L4Q142_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q142_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q142_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q142_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q142_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R142 : Tendsto i8L4R142 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q142_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q142_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q142_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q142_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q142_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q142_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q142_3 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q142_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q142_0 x (i13Rho [zero,
    zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q142_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q142_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q142_3 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R142
  unfold i8L4Q142_4
  ring

/-- The singular part of `Ψ₄⁽143⁾` at `ξ = 0`. -/
noncomputable def i8L4S143 (x : ℝ) : ℝ :=
    2 - Real.log x ^ 3 / 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽143⁾`. -/
noncomputable def i8L4Q143_0 (x r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    1 - 3 / 8 * x - x ^ 3 / 8 + 3 / 4 * x ^ 2 + r_01 * x ^ 2 / 2 - 3 * r_001 * x ^ 2 +
      2 * r_0001 * x ^ 2 + 2 * r_1 * x + 2 * r_1 * x ^ 3 - 15 / 4 * r_1 * x ^ 2 - r_1 * x ^ 4 / 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽143⁾`. -/
noncomputable def i8L4Q143_1 (x _r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    -1 - 5 / 4 * x - x ^ 2 / 2 + x ^ 3 / 4 + r_1 * x ^ 4 / 2 - 2 * r_001 * x ^ 2 -
      2 * r_1 * x ^ 3 + 2 * r_1 * x + 3 * r_01 * x ^ 2 - r_1 * x ^ 2 / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽143⁾`. -/
noncomputable def i8L4Q143_2 (x _r_0001 _r_001 r_01 r_1 : ℝ) : ℝ :=
    1 / 2 - x ^ 3 / 4 + x / 4 + r_01 * x ^ 2 + r_1 * x + r_1 * x ^ 3 - 3 / 2 * r_1 * x ^ 2 -
      r_1 * x ^ 4 / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽143⁾`. -/
noncomputable def i8L4Q143_3 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽143⁾`. -/
noncomputable def i8L4Q143_4 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_143_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s143 x = i8L4S143 x + x * (i8L4Q143_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero,
      zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q143_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q143_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q143_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q143_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s143 i8Psi4s143N0 i8Psi4s143N1 i8Psi4s143N2 i8Psi4s143N3 i8Psi4s143N4 i8Psi4s143W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_10 hx,
    i13hw_100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0, i13hpl_rho_1 h0]
  unfold i8L4S143 i8L4Q143_0 i8L4Q143_1 i8L4Q143_2 i8L4Q143_3 i8L4Q143_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽143⁾`. -/
noncomputable def i8L4R143 (x : ℝ) : ℝ :=
  x * (i8L4Q143_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    one] x) (i13Rho [one] x) + Real.log x * i8L4Q143_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q143_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q143_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q143_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R143 : Tendsto i8L4R143 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q143_0 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q143_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q143_1 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q143_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q143_2 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q143_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q143_0 x (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q143_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q143_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R143
  unfold i8L4Q143_3 i8L4Q143_4
  ring

/-- The singular part of `Ψ₄⁽144k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S144k0 (x : ℝ) : ℝ :=
    -21 / 8 - Real.log x ^ 2 / 4 + Real.log x ^ 3 / 6 + 3 / 4 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽144k0⁾`. -/
noncomputable def i8L4Q144k0_0 (x r_0001 r_000m1 _r_001 r_00m01 r_00m1 r_01 r_01m r_0m01 r_0m1 r_1
    r_m _r_m1 : ℝ) : ℝ :=
    -3 / 4 + r_01m / 2 + r_0m1 / 2 - r_00m1 - r_0m01 - 5 / 16 * x - x ^ 3 / 16 + x ^ 4 / 8 +
      x ^ 5 / 16 + 3 / 8 * x ^ 2 + r_00m1 * x ^ 4 + r_0m01 * x ^ 4 + r_m * x ^ 3 +
      r_01 * x ^ 3 / 2 + r_01m * x ^ 4 / 2 + r_0m1 * x ^ 4 / 2 - r_0001 * x ^ 2 - r_01 * x -
      r_01m * x ^ 2 - r_0m1 * x ^ 2 - 12 * r_000m1 * x ^ 2 - 4 * r_00m01 * x ^ 2 -
      3 / 2 * r_01 * x ^ 2 - 3 / 2 * r_1 * x - r_01 * x ^ 5 / 2 - r_m * x / 2 -
      r_m * x ^ 5 / 2 - r_01 * x ^ 4 / 4 - r_1 * x ^ 4 / 4 - r_m * x ^ 2 / 8 -
      r_m * x ^ 6 / 8 + r_01 * x ^ 6 / 4 + r_1 * x ^ 2 / 4 + r_m * x ^ 4 / 4 +
      3 / 2 * r_1 * x ^ 3 + r_01 * r_m * x ^ 5 - r_01 * r_m * x ^ 3 / 2 - r_01 * r_m * x ^ 7 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽144k0⁾`. -/
noncomputable def i8L4Q144k0_1 (x _r_0001 _r_000m1 r_001 _r_00m01 r_00m1 r_01 _r_01m _r_0m01 r_0m1
    r_1 _r_m _r_m1 : ℝ) : ℝ :=
    1 / 2 + r_0m1 - x ^ 2 / 4 - x ^ 3 / 8 + 9 / 8 * x + r_001 * x ^ 2 - r_0m1 * x ^ 4 -
      r_1 * x - r_1 * x ^ 3 + 8 * r_00m1 * x ^ 2 - r_01 * x ^ 2 / 2 + r_1 * x ^ 4 / 4 +
      7 / 4 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽144k0⁾`. -/
noncomputable def i8L4Q144k0_2 (x _r_0001 _r_000m1 _r_001 _r_00m01 _r_00m1 r_01 _r_01m _r_0m01 r_0m1
    r_1 _r_m r_m1 : ℝ) : ℝ :=
    -1 / 4 - r_m1 / 2 - x / 8 + x ^ 3 / 8 + r_1 * x ^ 3 / 2 + r_m1 * x ^ 4 / 2 -
      2 * r_0m1 * x ^ 2 - r_01 * x ^ 2 / 2 - r_1 * x / 2 - r_1 * x ^ 4 / 4 + r_1 * x ^ 2 / 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽144k0⁾`. -/
noncomputable def i8L4Q144k0_3 (_x _r_0001 _r_000m1 _r_001 _r_00m01 _r_00m1 _r_01 _r_01m _r_0m01
    _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽144k0⁾`. -/
noncomputable def i8L4Q144k0_4 (_x _r_0001 _r_000m1 _r_001 _r_00m01 _r_00m1 _r_01 _r_01m _r_0m01
    _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_144k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s144k0 x = i8L4S144k0 x + x * (i8L4Q144k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne,
      zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q144k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q144k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q144k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q144k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s144k0 i8Psi4s144k0N0 i8Psi4s144k0N1 i8Psi4s144k0N2 i8Psi4s144k0N3 i8Psi4s144k0N4
    i8Psi4s144k0W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_0m001
    hx, i13hw_0m010 hx, i13hw_0m100 hx, i13hw_10 hx, i13hw_100 hx, i13hw_m001 hx, i13hw_m01 hx,
    i13hw_m010 hx, i13hw_m100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_000m1 h0, i13hpl_rho_001 h0, i13hpl_rho_00m01 h0,
    i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0,
    i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S144k0 i8L4Q144k0_0 i8L4Q144k0_1 i8L4Q144k0_2 i8L4Q144k0_3 i8L4Q144k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽144k0⁾`. -/
noncomputable def i8L4R144k0 (x : ℝ) : ℝ :=
  x * (i8L4Q144k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne,
    zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) + Real.log x * i8L4Q144k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero,
    zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q144k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 3 * i8L4Q144k0_3 x (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q144k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x))

theorem tendsto_i8L4R144k0 : Tendsto i8L4R144k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q144k0_0 (v 0) (v 3) (v 7) (v 9) (v 19) (v 21) (v 27) (v 36) (v
      44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q144k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q144k0_1 (v 0) (v 3) (v 7) (v 9) (v 19) (v 21) (v 27) (v 36) (v
      44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q144k0_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q144k0_2 (v 0) (v 3) (v 7) (v 9) (v 19) (v 21) (v 27) (v 36) (v
      44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q144k0_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q144k0_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q144k0_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q144k0_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R144k0
  unfold i8L4Q144k0_3 i8L4Q144k0_4
  ring

/-- The singular part of `Ψ₄⁽144k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S144k1 (x : ℝ) : ℝ :=
    3 / 2 + Real.log x ^ 2 / 2 - 3 / 2 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽144k1⁾`. -/
noncomputable def i8L4Q144k1_0 (x r_0001m r_000m1 r_001 r_0010m r_001m r_00m r_00m01 r_00m1 r_01
    r_01m r_0m r_0m1 r_1 r_m : ℝ) : ℝ :=
    -r_001m - r_00m1 - r_01m - r_0m1 - x ^ 5 / 8 + 3 / 2 * x + r_001 * x ^ 2 +
      r_001m * x ^ 4 + r_00m1 * x ^ 4 + r_01m * x ^ 2 + r_0m1 * x ^ 2 - r_00m * x ^ 2 -
      r_01m * x ^ 4 - r_0m1 * x ^ 4 + 2 * r_01 * x + 2 * r_0m * x + 4 * r_0010m * x ^ 2 +
      4 * r_00m01 * x ^ 2 + 8 * r_0001m * x ^ 2 + 8 * r_000m1 * x ^ 2 - 3 / 2 * r_01 * x ^ 2 -
      3 / 4 * r_1 * x ^ 3 - 3 / 4 * r_m * x ^ 3 - r_01 * x ^ 3 / 2 - r_01 * x ^ 5 / 2 -
      r_0m * x ^ 3 / 2 - r_0m * x ^ 5 / 2 - r_0m * x ^ 4 / 4 - r_1 * x ^ 6 / 4 -
      r_m * x ^ 2 / 8 - r_m * x ^ 4 / 8 + r_01 * x ^ 4 / 4 + r_m * x ^ 6 / 4 + r_1 * x ^ 2 / 8 +
      r_1 * x ^ 4 / 8 + 3 / 2 * r_0m * x ^ 2 + 3 / 4 * r_1 * x ^ 5 + 3 / 4 * r_m * x ^ 5 +
      r_01 * r_0m * x ^ 3 + r_01 * r_m * x ^ 3 / 2 + r_01 * r_m * x ^ 7 / 2 +
      r_0m * r_1 * x ^ 3 / 2 + r_0m * r_1 * x ^ 7 / 2 - r_01 * r_0m * x ^ 7 -
      r_01 * r_m * x ^ 5 - r_0m * r_1 * x ^ 5 - r_1 * r_m * x ^ 3 / 4 + r_1 * r_m * x ^ 7 / 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽144k1⁾`. -/
noncomputable def i8L4Q144k1_1 (x _r_0001m _r_000m1 _r_001 _r_0010m r_001m _r_00m _r_00m01 r_00m1
    r_01 r_01m r_0m r_0m1 r_1 r_m : ℝ) : ℝ :=
    -r_01m - r_0m1 - x / 8 + x ^ 5 / 8 + r_01m * x ^ 4 + r_0m1 * x ^ 4 + r_1 * x ^ 2 +
      r_0m * x ^ 2 / 2 + r_1 * x ^ 3 / 2 + r_m * x ^ 3 / 2 - r_1 * x - r_m * x - r_m * x ^ 2 -
      4 * r_001m * x ^ 2 - 4 * r_00m1 * x ^ 2 - r_01 * x ^ 2 / 2 - r_1 * x ^ 5 / 2 -
      r_m * x ^ 5 / 2 - r_1 * x ^ 4 / 4 - r_m * x ^ 6 / 4 + r_1 * x ^ 6 / 4 + r_m * x ^ 4 / 4 +
      r_1 * r_m * x ^ 5 - r_1 * r_m * x ^ 3 / 2 - r_1 * r_m * x ^ 7 / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽144k1⁾`. -/
noncomputable def i8L4Q144k1_2 (_x _r_0001m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m01 _r_00m1
    _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽144k1⁾`. -/
noncomputable def i8L4Q144k1_3 (_x _r_0001m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m01 _r_00m1
    _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽144k1⁾`. -/
noncomputable def i8L4Q144k1_4 (_x _r_0001m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m01 _r_00m1
    _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

theorem i8L4_144k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s144k1 x = i8L4S144k1 x + x * (i8L4Q144k1_0 x (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
      one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one]
      x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q144k1_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q144k1_2 x (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
      [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q144k1_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
      zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q144k1_4 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
      zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s144k1 i8Psi4s144k1N0 i8Psi4s144k1N1 i8Psi4s144k1N2 i8Psi4s144k1N3 i8Psi4s144k1N4
    i8Psi4s144k1W
  simp only [hpl_zero, i13hw_00, i13hw_001m0 hx, i13hw_00m10 hx, i13hw_010 hx, i13hw_01m0 hx,
    i13hw_0m0 hx, i13hw_0m10 hx, i13hw_10 hx, i13hw_1m hx, i13hw_1m0 hx, i13hw_m0 hx, i13hw_m10 hx]
  simp only [i13hpl_rho_0001m h0, i13hpl_rho_000m1 h0, i13hpl_rho_001 h0, i13hpl_rho_0010m h0,
    i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m01 h0, i13hpl_rho_00m1 h0, i13hpl_rho_01
    h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0]
  unfold i8L4S144k1 i8L4Q144k1_0 i8L4Q144k1_1 i8L4Q144k1_2 i8L4Q144k1_3 i8L4Q144k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽144k1⁾`. -/
noncomputable def i8L4R144k1 (x : ℝ) : ℝ :=
  x * (i8L4Q144k1_0 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero,
    zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q144k1_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x)
    (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q144k1_2 x (i13Rho [zero, zero, zero, one, negOne] x)
    (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q144k1_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x)
    (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) + Real.log x ^ 4 * i8L4Q144k1_4 x (i13Rho [zero, zero, zero, one, negOne] x)
    (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R144k1 : Tendsto i8L4R144k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q144k1_0 (v 0) (v 5) (v 7) (v 9) (v 11) (v 15) (v 18) (v 19) (v
      21) (v 27) (v 36) (v 43) (v 49) (v 65) (v 66)) (by
      unfold i8L4Q144k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q144k1_1 (v 0) (v 5) (v 7) (v 9) (v 11) (v 15) (v 18) (v 19) (v
      21) (v 27) (v 36) (v 43) (v 49) (v 65) (v 66)) (by
      unfold i8L4Q144k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q144k1_0 x (i13Rho [zero,
    zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one]
    x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q144k1_1 x (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R144k1
  unfold i8L4Q144k1_2 i8L4Q144k1_3 i8L4Q144k1_4
  ring

/-- The singular part of `Ψ₄⁽144k2⁾` at `ξ = 0`. -/
noncomputable def i8L4S144k2 (x : ℝ) : ℝ :=
    -21 / 8 - Real.log x ^ 2 / 4 + Real.log x ^ 3 / 6 + 3 / 4 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽144k2⁾`. -/
noncomputable def i8L4Q144k2_0 (x r_0001m r_000m r_0010m r_001m _r_00m r_00m1 r_01 r_01m r_0m r_0m01
    r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ :=
    3 / 4 + r_001m + r_0m01 + r_01m / 2 + r_0m1 / 2 + 2 * r_00m1 - 3 / 8 * x ^ 2 - x / 4 -
      x ^ 4 / 8 - x ^ 3 / 16 + r_000m * x ^ 2 + r_01 * x ^ 5 + r_1 * x ^ 3 +
      r_01m * x ^ 4 / 2 + r_0m * x ^ 3 / 2 + r_0m * x ^ 5 / 2 + r_0m1 * x ^ 4 / 2 -
      r_001m * x ^ 4 - r_01 * x - r_01m * x ^ 2 - r_0m01 * x ^ 4 - r_0m1 * x ^ 2 -
      12 * r_0001m * x ^ 2 - 4 * r_0010m * x ^ 2 - 2 * r_00m1 * x ^ 4 - 2 * r_0m * x -
      3 / 2 * r_m * x - r_1 * x / 2 - r_1 * x ^ 5 / 2 - r_01 * x ^ 6 / 4 - r_1 * x ^ 4 / 4 -
      r_m * x ^ 2 / 4 + r_01 * x ^ 2 / 4 + r_0m * x ^ 4 / 4 + r_m * x ^ 4 / 4 +
      r_1 * x ^ 2 / 8 + r_1 * x ^ 6 / 8 + 3 / 2 * r_m * x ^ 3 + 5 / 4 * r_0m * x ^ 2 +
      r_01 * r_0m * x ^ 7 + r_0m * r_1 * x ^ 5 - r_01 * r_0m * x ^ 3 - r_0m * r_1 * x ^ 3 / 2 -
      r_0m * r_1 * x ^ 7 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽144k2⁾`. -/
noncomputable def i8L4Q144k2_1 (x _r_0001m _r_000m _r_0010m r_001m r_00m _r_00m1 _r_01 r_01m r_0m
    _r_0m01 _r_0m1 _r_1 r_m _r_m1 : ℝ) : ℝ :=
    -1 / 2 + r_01m - x ^ 3 / 8 + x ^ 2 / 4 + 9 / 8 * x + r_0m * x ^ 2 / 2 - r_00m * x ^ 2 -
      r_01m * x ^ 4 - r_m * x - r_m * x ^ 3 + 8 * r_001m * x ^ 2 - 7 / 4 * r_m * x ^ 2 -
      r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽144k2⁾`. -/
noncomputable def i8L4Q144k2_2 (x _r_0001m _r_000m _r_0010m _r_001m _r_00m _r_00m1 _r_01 r_01m r_0m
    _r_0m01 _r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    1 / 4 + r_m1 / 2 - x ^ 5 / 8 + x ^ 3 / 8 + r_0m * x ^ 2 / 2 + r_1 * x ^ 5 / 2 +
      r_m * x ^ 3 / 2 + r_m * x ^ 5 / 2 - r_m * x - 2 * r_01m * x ^ 2 - r_1 * x / 2 -
      r_m * x ^ 2 / 2 - r_m1 * x ^ 4 / 2 - r_1 * x ^ 6 / 4 + r_1 * x ^ 2 / 4 + r_m * x ^ 4 / 4 +
      r_m * x ^ 6 / 4 + r_1 * r_m * x ^ 7 / 2 - r_1 * r_m * x ^ 3 / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽144k2⁾`. -/
noncomputable def i8L4Q144k2_3 (_x _r_0001m _r_000m _r_0010m _r_001m _r_00m _r_00m1 _r_01 _r_01m
    _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽144k2⁾`. -/
noncomputable def i8L4Q144k2_4 (_x _r_0001m _r_000m _r_0010m _r_001m _r_00m _r_00m1 _r_01 _r_01m
    _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_144k2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s144k2 x = i8L4S144k2 x + x * (i8L4Q144k2_0 x (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho
      [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x) + Real.log x * i8L4Q144k2_1 x (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q144k2_2 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
      one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x) + Real.log x ^ 3 * i8L4Q144k2_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 4 * i8L4Q144k2_4 x (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho
      [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s144k2 i8Psi4s144k2N0 i8Psi4s144k2N1 i8Psi4s144k2N2 i8Psi4s144k2N3 i8Psi4s144k2N4
    i8Psi4s144k2W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_010m hx, i13hw_010m0 hx,
    i13hw_01m00 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_100m hx, i13hw_10m hx, i13hw_10m0 hx,
    i13hw_1m00 hx, i13hw_m0 hx, i13hw_m00 hx, i8hw_0100m hx]
  simp only [i13hpl_rho_0001m h0, i13hpl_rho_000m h0, i13hpl_rho_0010m h0, i13hpl_rho_001m h0,
    i13hpl_rho_00m h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0,
    i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S144k2 i8L4Q144k2_0 i8L4Q144k2_1 i8L4Q144k2_2 i8L4Q144k2_3 i8L4Q144k2_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽144k2⁾`. -/
noncomputable def i8L4R144k2 (x : ℝ) : ℝ :=
  x * (i8L4Q144k2_0 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q144k2_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q144k2_2 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q144k2_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q144k2_4 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R144k2 : Tendsto i8L4R144k2 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q144k2_0 (v 0) (v 5) (v 6) (v 11) (v 15) (v 18) (v 21) (v 27) (v
      36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q144k2_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q144k2_1 (v 0) (v 5) (v 6) (v 11) (v 15) (v 18) (v 21) (v 27) (v
      36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q144k2_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q144k2_2 (v 0) (v 5) (v 6) (v 11) (v 15) (v 18) (v 21) (v 27) (v
      36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q144k2_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q144k2_0 x (i13Rho [zero,
    zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one,
    zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q144k2_1 x (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne]
      x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q144k2_2 x (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne]
      x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R144k2
  unfold i8L4Q144k2_3 i8L4Q144k2_4
  ring

/-- The singular part of `Ψ₄⁽145⁾` at `ξ = 0`. -/
noncomputable def i8L4S145 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽145⁾`. -/
noncomputable def i8L4Q145_0 (x r_001 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    2 - 9 / 8 * x ^ 3 - 7 / 2 * x ^ 2 + x ^ 5 / 8 + r_1 * x ^ 6 / 2 + r_1 ^ 2 * x ^ 7 / 2 -
      r_1 * x ^ 5 - 4 * r_0011 * x ^ 2 - 4 * r_1 * x ^ 3 - 3 * r_01 * x ^ 2 -
      2 * r_1 ^ 2 * x ^ 6 + 2 * r_1 ^ 2 * x ^ 4 + 4 * r_001 * x ^ 2 + 6 * r_011 * x ^ 2 +
      8 * r_1 * x ^ 2 - 7 / 2 * r_1 * x ^ 4 - r_1 ^ 2 * x ^ 5 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽145⁾`. -/
noncomputable def i8L4Q145_1 (x _r_001 _r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -2 - x ^ 2 / 2 - x ^ 4 / 2 - x ^ 3 / 4 - x ^ 5 / 4 - r_1 * x ^ 6 - r_1 ^ 2 * x ^ 7 -
      4 * r_01 * x ^ 2 - 3 * r_1 ^ 2 * x ^ 5 - 2 * r_1 * x ^ 3 + 2 * r_1 ^ 2 * x ^ 4 +
      2 * r_1 ^ 2 * x ^ 6 + 3 * r_1 * x ^ 2 + 4 * r_011 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽145⁾`. -/
noncomputable def i8L4Q145_2 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽145⁾`. -/
noncomputable def i8L4Q145_3 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽145⁾`. -/
noncomputable def i8L4Q145_4 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_145_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s145 x = i8L4S145 x + x * (i8L4Q145_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
      one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q145_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q145_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q145_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q145_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s145 i8Psi4s145N0 i8Psi4s145N1 i8Psi4s145N2 i8Psi4s145N3 i8Psi4s145N4 i8Psi4s145W
  simp only [hpl_zero, i13hw_010 hx, i13hw_0101 hx, i13hw_0110 hx, i13hw_10 hx, i13hw_101 hx,
    i13hw_11 hx, i13hw_110 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_0011 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0,
    i13hpl_rho_1 h0]
  unfold i8L4S145 i8L4Q145_0 i8L4Q145_1 i8L4Q145_2 i8L4Q145_3 i8L4Q145_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽145⁾`. -/
noncomputable def i8L4R145 (x : ℝ) : ℝ :=
  x * (i8L4Q145_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q145_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q145_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q145_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q145_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R145 : Tendsto i8L4R145 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q145_0 (v 0) (v 9) (v 12) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q145_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q145_1 (v 0) (v 9) (v 12) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q145_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q145_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q145_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R145
  unfold i8L4Q145_2 i8L4Q145_3 i8L4Q145_4
  ring

/-- The singular part of `Ψ₄⁽146k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S146k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽146k0⁾`. -/
noncomputable def i8L4Q146k0_0 (x r_001 r_0011 r_00m11 r_01 r_011 _r_0m11 r_1 r_m11 : ℝ) : ℝ :=
    -1 / 2 - r_m11 - x ^ 2 / 8 + x ^ 4 / 8 + x ^ 5 / 8 + r_1 * x ^ 3 / 2 + r_1 * x ^ 6 / 2 +
      r_1 ^ 2 * x ^ 7 / 2 - r_m11 * x ^ 4 - 2 * r_001 * x ^ 2 - 2 * r_011 * x ^ 2 +
      2 * r_0011 * x ^ 2 + 2 * r_m11 * x ^ 2 + 8 * r_00m11 * x ^ 2 - 3 / 2 * r_1 ^ 2 * x ^ 4 -
      3 / 2 * r_1 ^ 2 * x ^ 6 - 3 / 4 * r_1 * x ^ 2 - r_1 * x ^ 5 / 2 + r_1 * x ^ 4 / 4 +
      5 / 2 * r_1 ^ 2 * x ^ 5 + 7 / 2 * r_01 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽146k0⁾`. -/
noncomputable def i8L4Q146k0_1 (x _r_001 _r_0011 _r_00m11 r_01 r_011 r_0m11 r_1 r_m11 : ℝ) : ℝ :=
    1 - 2 * r_m11 - x ^ 4 / 4 - x ^ 5 / 8 + 3 / 8 * x ^ 3 + 5 / 4 * x ^ 2 + r_1 * x ^ 3 +
      r_1 ^ 2 * x ^ 6 + r_1 ^ 2 * x ^ 5 / 2 - r_1 ^ 2 * x ^ 4 - 8 * r_0m11 * x ^ 2 -
      2 * r_011 * x ^ 2 + 2 * r_01 * x ^ 2 + 2 * r_1 * x ^ 4 + 2 * r_m11 * x ^ 4 -
      5 / 2 * r_1 * x ^ 2 - r_1 * x ^ 6 / 2 - r_1 ^ 2 * x ^ 7 / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽146k0⁾`. -/
noncomputable def i8L4Q146k0_2 (_x _r_001 _r_0011 _r_00m11 _r_01 _r_011 _r_0m11 _r_1 _r_m11 : ℝ) : ℝ
    :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽146k0⁾`. -/
noncomputable def i8L4Q146k0_3 (_x _r_001 _r_0011 _r_00m11 _r_01 _r_011 _r_0m11 _r_1 _r_m11 : ℝ) : ℝ
    :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽146k0⁾`. -/
noncomputable def i8L4Q146k0_4 (_x _r_001 _r_0011 _r_00m11 _r_01 _r_011 _r_0m11 _r_1 _r_m11 : ℝ) : ℝ
    :=
    0

theorem i8L4_146k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s146k0 x = i8L4S146k0 x + x * (i8L4Q146k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one,
      one] x) + Real.log x * i8L4Q146k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one,
      one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 2 * i8L4Q146k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 3 * i8L4Q146k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 4 * i8L4Q146k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s146k0 i8Psi4s146k0N0 i8Psi4s146k0N1 i8Psi4s146k0N2 i8Psi4s146k0N3 i8Psi4s146k0N4
    i8Psi4s146k0W
  simp only [hpl_zero, i13hw_010 hx, i13hw_0101 hx, i13hw_0110 hx, i13hw_0m110 hx, i13hw_10 hx,
    i13hw_101 hx, i13hw_11 hx, i13hw_110 hx, i13hw_m011 hx, i13hw_m101 hx, i13hw_m110 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_0011 h0, i8hpl_rho_00m11 h0, i13hpl_rho_01 h0,
    i13hpl_rho_011 h0, i13hpl_rho_0m11 h0, i13hpl_rho_1 h0, i8hpl_rho_m11 h0]
  unfold i8L4S146k0 i8L4Q146k0_0 i8L4Q146k0_1 i8L4Q146k0_2 i8L4Q146k0_3 i8L4Q146k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽146k0⁾`. -/
noncomputable def i8L4R146k0 (x : ℝ) : ℝ :=
  x * (i8L4Q146k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
    negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x) +
    Real.log x * i8L4Q146k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 2 * i8L4Q146k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 3 * i8L4Q146k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 4 * i8L4Q146k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x))

theorem tendsto_i8L4R146k0 : Tendsto i8L4R146k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q146k0_0 (v 0) (v 9) (v 12) (v 22) (v 27) (v 29) (v 51) (v 65)
      (v 68)) (by
      unfold i8L4Q146k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q146k0_1 (v 0) (v 9) (v 12) (v 22) (v 27) (v 29) (v 51) (v 65)
      (v 68)) (by
      unfold i8L4Q146k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q146k0_0 x (i13Rho [zero,
    zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, negOne, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne, one, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q146k0_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x)
      (i13Rho [negOne, one, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R146k0
  unfold i8L4Q146k0_2 i8L4Q146k0_3 i8L4Q146k0_4
  ring

/-- The singular part of `Ψ₄⁽146k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S146k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽146k1⁾`. -/
noncomputable def i8L4Q146k1_0 (x r_001 r_0011m r_001m1 r_00m1 r_00m11 r_01 r_011m r_01m r_01m1 r_0m
    r_0m011 r_0m1 r_0m101 r_0m11 r_1 r_m r_m1 r_m11 : ℝ) : ℝ :=
    -1 / 2 + r_m11 - x ^ 4 - 4 * r_0m11 - 2 * r_011m - 2 * r_01m1 - x ^ 5 / 2 + x / 4 +
      x ^ 6 / 8 + x ^ 3 / 16 + x ^ 7 / 16 + 29 / 8 * x ^ 2 + r_01m * x ^ 2 + r_0m * x ^ 2 +
      r_0m1 * x ^ 4 + r_m11 * x ^ 4 + r_1 ^ 2 * x ^ 6 + r_1 * x ^ 4 / 2 - r_0m1 * x ^ 6 -
      32 * r_00m11 * x ^ 2 - 16 * r_0m011 * x ^ 2 - 8 * r_0011m * x ^ 2 - 8 * r_001m1 * x ^ 2 -
      8 * r_0m101 * x ^ 2 - 4 * r_00m1 * x ^ 2 - 4 * r_m1 * x ^ 2 - 2 * r_001 * x ^ 2 -
      2 * r_0m1 * x ^ 5 - 2 * r_m11 * x ^ 2 + 2 * r_01 * x ^ 4 + 2 * r_011m * x ^ 4 +
      2 * r_01m1 * x ^ 4 + 3 * r_0m1 * x ^ 2 + 4 * r_0m1 * x + 4 * r_0m11 * x ^ 4 +
      6 * r_0m1 * x ^ 3 - 11 / 4 * r_m * x ^ 2 - 7 / 2 * r_1 * x ^ 2 - 7 / 4 * r_1 * x ^ 6 -
      r_01 * x ^ 2 / 2 - r_m * x ^ 6 / 2 - r_m * x ^ 7 / 2 - r_1 ^ 2 * x ^ 4 / 2 -
      r_1 ^ 2 * x ^ 7 / 2 - r_1 ^ 2 * x ^ 8 / 2 - r_m * x ^ 8 / 8 + r_1 * x ^ 8 / 4 +
      r_1 ^ 2 * x ^ 5 / 4 + r_1 ^ 2 * x ^ 9 / 4 + 7 / 8 * r_m * x ^ 4 + 9 / 2 * r_1 * x ^ 3 +
      r_1 * r_m * x ^ 6 + r_m * r_1 ^ 2 * x ^ 8 + r_1 * r_m * x ^ 7 / 2 - r_1 * r_m * x ^ 8 -
      2 * r_0m1 * r_1 * x ^ 7 - 2 * r_1 * r_m * x ^ 4 + 2 * r_0m1 * r_1 * x ^ 3 +
      2 * r_1 * r_m * x ^ 5 + 8 * r_01 * r_0m1 * x ^ 5 - r_1 * r_m * x ^ 9 / 2 -
      r_m * r_1 ^ 2 * x ^ 6 / 2 - r_m * r_1 ^ 2 * x ^ 10 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽146k1⁾`. -/
noncomputable def i8L4Q146k1_1 (x _r_001 _r_0011m _r_001m1 _r_00m1 _r_00m11 r_01 _r_011m _r_01m
    r_01m1 _r_0m _r_0m011 r_0m1 _r_0m101 _r_0m11 r_1 _r_m r_m1 r_m11 : ℝ) : ℝ :=
    x ^ 4 + x ^ 5 / 2 + 4 * r_m11 - x / 2 + x ^ 3 / 4 + r_1 * x ^ 6 + r_m1 * x ^ 4 +
      r_m1 * x ^ 6 + r_1 * x ^ 2 / 2 - r_1 * x ^ 3 - 8 * r_01m1 * x ^ 2 - 4 * r_m1 * x -
      4 * r_m11 * x ^ 4 - 2 * r_m1 * x ^ 2 + 2 * r_01 * x ^ 2 + 2 * r_0m1 * x ^ 2 +
      2 * r_m1 * x ^ 3 + 2 * r_m1 * x ^ 5 - r_1 * x ^ 4 / 2 - 2 * r_1 * r_m1 * x ^ 3 +
      2 * r_1 * r_m1 * x ^ 7

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽146k1⁾`. -/
noncomputable def i8L4Q146k1_2 (_x _r_001 _r_0011m _r_001m1 _r_00m1 _r_00m11 _r_01 _r_011m _r_01m
    _r_01m1 _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽146k1⁾`. -/
noncomputable def i8L4Q146k1_3 (_x _r_001 _r_0011m _r_001m1 _r_00m1 _r_00m11 _r_01 _r_011m _r_01m
    _r_01m1 _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽146k1⁾`. -/
noncomputable def i8L4Q146k1_4 (_x _r_001 _r_0011m _r_001m1 _r_00m1 _r_00m11 _r_01 _r_011m _r_01m
    _r_01m1 _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

theorem i8L4_146k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s146k1 x = i8L4S146k1 x + x * (i8L4Q146k1_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x * i8L4Q146k1_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one,
      negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one,
      negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 2 * i8L4Q146k1_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one,
      negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one,
      negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 3 * i8L4Q146k1_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one,
      negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one,
      negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 4 * i8L4Q146k1_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one,
      negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one,
      negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s146k1 i8Psi4s146k1N0 i8Psi4s146k1N1 i8Psi4s146k1N2 i8Psi4s146k1N3 i8Psi4s146k1N4
    i8Psi4s146k1W
  simp only [hpl_zero, i13hw_010 hx, i13hw_01m01 hx, i13hw_01m10 hx, i13hw_0m10 hx, i13hw_10 hx,
    i13hw_11m hx, i13hw_1m hx, i13hw_1m01 hx, i13hw_1m1 hx, i13hw_1m10 hx, i13hw_m01 hx, i13hw_m10
    hx]
  simp only [i13hpl_rho_001 h0, i8hpl_rho_0011m h0, i8hpl_rho_001m1 h0, i13hpl_rho_00m1 h0,
    i8hpl_rho_00m11 h0, i13hpl_rho_01 h0, i13hpl_rho_011m h0, i13hpl_rho_01m h0, i13hpl_rho_01m1 h0,
    i13hpl_rho_0m h0, i13hpl_rho_0m011 h0, i13hpl_rho_0m1 h0, i8hpl_rho_0m101 h0, i13hpl_rho_0m11
    h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0, i8hpl_rho_m11 h0]
  unfold i8L4S146k1 i8L4Q146k1_0 i8L4Q146k1_1 i8L4Q146k1_2 i8L4Q146k1_3 i8L4Q146k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽146k1⁾`. -/
noncomputable def i8L4R146k1 (x : ℝ) : ℝ :=
  x * (i8L4Q146k1_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one, negOne] x) (i13Rho
    [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero,
    negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one]
    x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x) (i13Rho [negOne, one, one] x) +
    Real.log x * i8L4Q146k1_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one, negOne]
    x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one,
    zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 2 * i8L4Q146k1_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one,
    negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 3 * i8L4Q146k1_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one,
    negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 4 * i8L4Q146k1_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one,
    negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x))

theorem tendsto_i8L4R146k1 : Tendsto i8L4R146k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q146k1_0 (v 0) (v 9) (v 14) (v 16) (v 21) (v 22) (v 27) (v 33)
      (v 36) (v 37) (v 43) (v 45) (v 49) (v 50) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q146k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q146k1_1 (v 0) (v 9) (v 14) (v 16) (v 21) (v 22) (v 27) (v 33)
      (v 36) (v 37) (v 43) (v 45) (v 49) (v 50) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q146k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q146k1_0 x (i13Rho [zero,
    zero, one] x) (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, one, negOne, one]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one]
    x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q146k1_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho
      [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
      one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R146k1
  unfold i8L4Q146k1_2 i8L4Q146k1_3 i8L4Q146k1_4
  ring

/-- The regular parts of group 15. -/
noncomputable def i8L4RG15 (x : ℝ) : ℝ :=
  i8L4R140k2 x + i8L4R141 x + i8L4R142 x + i8L4R143 x + i8L4R144k0 x + i8L4R144k1 x +
    i8L4R144k2 x + i8L4R145 x + i8L4R146k0 x + i8L4R146k1 x

theorem tendsto_i8L4RG15 : Tendsto i8L4RG15 (𝓝[>] 0) (𝓝 0) := by
  have H := (((((((((tendsto_i8L4R140k2.add tendsto_i8L4R141).add tendsto_i8L4R142).add
    tendsto_i8L4R143).add tendsto_i8L4R144k0).add tendsto_i8L4R144k1).add tendsto_i8L4R144k2).add
    tendsto_i8L4R145).add tendsto_i8L4R146k0).add tendsto_i8L4R146k1)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
