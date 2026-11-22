/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L6
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 7

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_83_eq`, `QED.ThreeLoopD.tendsto_i8L4RG7` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽83⁾` at `ξ = 0`. -/
noncomputable def i8L4S83 (x : ℝ) : ℝ :=
    (18 + Real.log x ^ 3 + 7 * Real.log x ^ 2 + 18 * Real.log x + 2 * x * Real.log x ^ 2 -
      4 / 3 * x * Real.log x ^ 3 - 3 / 4 * x * Real.log x ^ 4) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽83⁾`. -/
noncomputable def i8L4Q83_0 (x : ℝ) : ℝ :=
    22 + 19 / 8 * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽83⁾`. -/
noncomputable def i8L4Q83_1 (x : ℝ) : ℝ :=
    -22 - 19 / 4 * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽83⁾`. -/
noncomputable def i8L4Q83_2 (x : ℝ) : ℝ :=
    13 + 11 / 4 * x

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽83⁾`. -/
noncomputable def i8L4Q83_3 (x : ℝ) : ℝ :=
    -3 - x / 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽83⁾`. -/
noncomputable def i8L4Q83_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_83_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s83 x = i8L4S83 x + x * (i8L4Q83_0 x + Real.log x * i8L4Q83_1 x +
      Real.log x ^ 2 * i8L4Q83_2 x + Real.log x ^ 3 * i8L4Q83_3 x +
      Real.log x ^ 4 * i8L4Q83_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s83 i8Psi4s83N0 i8Psi4s83N1 i8Psi4s83N2 i8Psi4s83N3 i8Psi4s83N4 i8Psi4s83W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000]

  unfold i8L4S83 i8L4Q83_0 i8L4Q83_1 i8L4Q83_2 i8L4Q83_3 i8L4Q83_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽83⁾`. -/
noncomputable def i8L4R83 (x : ℝ) : ℝ :=
  x * (i8L4Q83_0 x + Real.log x * i8L4Q83_1 x + Real.log x ^ 2 * i8L4Q83_2 x +
    Real.log x ^ 3 * i8L4Q83_3 x + Real.log x ^ 4 * i8L4Q83_4 x)

theorem tendsto_i8L4R83 : Tendsto i8L4R83 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q83_0 (v 0)) (by
      unfold i8L4Q83_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q83_1 (v 0)) (by
      unfold i8L4Q83_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q83_2 (v 0)) (by
      unfold i8L4Q83_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q83_3 (v 0)) (by
      unfold i8L4Q83_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q83_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q83_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q83_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q83_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R83
  unfold i8L4Q83_4
  ring

/-- The singular part of `Ψ₄⁽84⁾` at `ξ = 0`. -/
noncomputable def i8L4S84 (x : ℝ) : ℝ :=
    (-18 - Real.log x ^ 3 - 18 * Real.log x - 7 * Real.log x ^ 2 - 621 / 16 * x -
      x * Real.log x ^ 2 + 2 * x * Real.log x ^ 3 + 7 / 8 * x * Real.log x ^ 4) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽84⁾`. -/
noncomputable def i8L4Q84_0 (x r_0000m _r_000m r_00m _r_0m r_m : ℝ) : ℝ :=
    -191 / 8 - 19 / 8 * r_m + 19 / 16 * x ^ 3 + 77 / 8 * x + 141 / 8 * x ^ 2 -
      61 * r_00m * x ^ 2 - 40 * r_m * x - 40 * r_m * x ^ 3 - 36 * r_0000m * x ^ 2 -
      301 / 4 * r_m * x ^ 2 - 19 / 8 * r_m * x ^ 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽84⁾`. -/
noncomputable def i8L4Q84_1 (x _r_0000m r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    105 / 4 - 61 / 4 * x ^ 2 - 19 / 4 * r_m - 19 / 8 * x ^ 3 + 147 / 8 * x - 40 * r_m * x +
      36 * r_000m * x ^ 2 + 40 * r_m * x ^ 3 + 61 * r_0m * x ^ 2 + 19 / 4 * r_m * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽84⁾`. -/
noncomputable def i8L4Q84_2 (x _r_0000m _r_000m r_00m _r_0m r_m : ℝ) : ℝ :=
    -59 / 4 - 11 / 4 * r_m + 5 / 4 * x + 11 / 8 * x ^ 3 + 29 / 4 * x ^ 2 - 20 * r_m * x -
      20 * r_m * x ^ 3 - 18 * r_00m * x ^ 2 - 69 / 2 * r_m * x ^ 2 - 11 / 4 * r_m * x ^ 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽84⁾`. -/
noncomputable def i8L4Q84_3 (x _r_0000m _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    9 / 2 - 3 / 2 * x ^ 2 - r_m / 2 - x ^ 3 / 4 + 9 / 4 * x + r_m * x ^ 4 / 2 - 4 * r_m * x +
      4 * r_m * x ^ 3 + 6 * r_0m * x ^ 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽84⁾`. -/
noncomputable def i8L4Q84_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_84_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s84 x = i8L4S84 x + x * (i8L4Q84_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [negOne] x) + Real.log x * i8L4Q84_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q84_2 x (i13Rho [zero, zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q84_3 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q84_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s84 i8Psi4s84N0 i8Psi4s84N1 i8Psi4s84N2 i8Psi4s84N3 i8Psi4s84N4 i8Psi4s84W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_000m0 hx, i13hw_00m0 hx, i13hw_00m00
    hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_0m000 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_m000 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S84 i8L4Q84_0 i8L4Q84_1 i8L4Q84_2 i8L4Q84_3 i8L4Q84_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽84⁾`. -/
noncomputable def i8L4R84 (x : ℝ) : ℝ :=
  x * (i8L4Q84_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q84_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q84_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q84_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q84_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R84 : Tendsto i8L4R84 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q84_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q84_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q84_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q84_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q84_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q84_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q84_3 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q84_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q84_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q84_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q84_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q84_3 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R84
  unfold i8L4Q84_4
  ring

/-- The singular part of `Ψ₄⁽85⁾` at `ξ = 0`. -/
noncomputable def i8L4S85 (x : ℝ) : ℝ :=
    20 - 8 * Real.log x - 4 * Real.log x ^ 2 - 2 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽85⁾`. -/
noncomputable def i8L4Q85_0 (x r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    2 - 25 / 2 * x ^ 2 - 19 / 4 * x - 13 / 4 * x ^ 3 - 12 * r_0001 * x ^ 2 - 12 * r_1 * x ^ 3 +
      18 * r_001 * x ^ 2 + 20 * r_1 * x + 45 * r_01 * x ^ 2 - 13 / 2 * r_1 * x ^ 4 -
      3 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽85⁾`. -/
noncomputable def i8L4Q85_1 (x _r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    2 + 15 * x ^ 2 + 3 / 2 * x + 5 / 2 * x ^ 3 - 37 * r_1 * x ^ 2 - 18 * r_01 * x ^ 2 +
      5 * r_1 * x ^ 4 + 12 * r_001 * x ^ 2 + 12 * r_1 * x + 20 * r_1 * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽85⁾`. -/
noncomputable def i8L4Q85_2 (x _r_0001 _r_001 r_01 r_1 : ℝ) : ℝ :=
    -7 - 4 * x ^ 2 - 11 / 2 * x - x ^ 3 / 2 - r_1 * x ^ 4 - 6 * r_01 * x ^ 2 - 6 * r_1 * x ^ 3 +
      2 * r_1 * x + 5 * r_1 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽85⁾`. -/
noncomputable def i8L4Q85_3 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽85⁾`. -/
noncomputable def i8L4Q85_4 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_85_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s85 x = i8L4S85 x + x * (i8L4Q85_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero,
      zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q85_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q85_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q85_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q85_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s85 i8Psi4s85N0 i8Psi4s85N1 i8Psi4s85N2 i8Psi4s85N3 i8Psi4s85N4 i8Psi4s85W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_10 hx,
    i13hw_100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0, i13hpl_rho_1 h0]
  unfold i8L4S85 i8L4Q85_0 i8L4Q85_1 i8L4Q85_2 i8L4Q85_3 i8L4Q85_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽85⁾`. -/
noncomputable def i8L4R85 (x : ℝ) : ℝ :=
  x * (i8L4Q85_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    one] x) (i13Rho [one] x) + Real.log x * i8L4Q85_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q85_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q85_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q85_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R85 : Tendsto i8L4R85 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q85_0 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q85_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q85_1 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q85_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q85_2 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q85_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q85_0 x (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q85_1 x (i13Rho [zero, zero, zero, one]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q85_2 x (i13Rho [zero, zero, zero, one]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R85
  unfold i8L4Q85_3 i8L4Q85_4
  ring

/-- The singular part of `Ψ₄⁽86⁾` at `ξ = 0`. -/
noncomputable def i8L4S86 (x : ℝ) : ℝ :=
    -19 + 2 * Real.log x ^ 2 + 8 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽86⁾`. -/
noncomputable def i8L4Q86_0 (x r_001 r_00m r_01 r_01m r_0m r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ :=
    -8 - 6 * x ^ 2 - 2 * x ^ 4 + 2 * x ^ 3 - 5 / 4 * x ^ 5 + 5 / 4 * x + r_1 * x ^ 5 -
      36 * r_01m * x ^ 2 - 12 * r_1 * x - 12 * r_m * x - 10 * r_00m * x ^ 2 - 6 * r_001 * x ^ 2 -
      5 * r_1 * x ^ 3 - 4 * r_0m1 * x ^ 2 + 5 * r_1 * x ^ 4 + 8 * r_01 * x ^ 2 +
      9 * r_m * x ^ 5 + 11 * r_m * x ^ 4 + 19 * r_m * x ^ 3 + 24 * r_0m * x ^ 2 -
      5 / 2 * r_1 * x ^ 6 + 5 / 2 * r_m * x ^ 2 + 5 / 2 * r_m * x ^ 6 + 27 / 2 * r_1 * x ^ 2 -
      8 * r_1 * r_m * x ^ 4 - 5 * r_1 * r_m * x ^ 3 + 5 * r_1 * r_m * x ^ 7 + 8 * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽86⁾`. -/
noncomputable def i8L4Q86_1 (x _r_001 _r_00m r_01 _r_01m r_0m _r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    8 + x ^ 5 / 2 - 6 * x ^ 3 + 2 * x ^ 2 + 2 * x ^ 4 + 7 / 2 * x + r_1 * x ^ 6 + r_m * x ^ 4 -
      r_m * x ^ 6 - 32 * r_m1 * x ^ 2 - 20 * r_m * x ^ 2 - 17 * r_1 * x ^ 4 - 12 * r_1 * x ^ 2 -
      6 * r_m * x ^ 5 - 4 * r_1 * x - 4 * r_m * x + 2 * r_1 * x ^ 5 + 6 * r_01 * x ^ 2 +
      6 * r_m * x ^ 3 + 10 * r_0m * x ^ 2 + 30 * r_1 * x ^ 3 - 8 * r_1 * r_m * x ^ 4 -
      8 * r_1 * r_m * x ^ 6 - 2 * r_1 * r_m * x ^ 3 - 2 * r_1 * r_m * x ^ 7 + 20 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽86⁾`. -/
noncomputable def i8L4Q86_2 (_x _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽86⁾`. -/
noncomputable def i8L4Q86_3 (_x _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽86⁾`. -/
noncomputable def i8L4Q86_4 (_x _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_86_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s86 x = i8L4S86 x + x * (i8L4Q86_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q86_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q86_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q86_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q86_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s86 i8Psi4s86N0 i8Psi4s86N1 i8Psi4s86N2 i8Psi4s86N3 i8Psi4s86N4 i8Psi4s86W
  simp only [hpl_zero, i13hw_00, i13hw_010 hx, i13hw_0m0 hx, i13hw_10 hx, i13hw_10m hx, i13hw_1m hx,
    i13hw_1m0 hx, i13hw_m0 hx, i13hw_m01 hx, i13hw_m10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_00m h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0,
    i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S86 i8L4Q86_0 i8L4Q86_1 i8L4Q86_2 i8L4Q86_3 i8L4Q86_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽86⁾`. -/
noncomputable def i8L4R86 (x : ℝ) : ℝ :=
  x * (i8L4Q86_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one]
    x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q86_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q86_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q86_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q86_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R86 : Tendsto i8L4R86 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q86_0 (v 0) (v 9) (v 18) (v 27) (v 36) (v 43) (v 49) (v 65) (v
      66) (v 67)) (by
      unfold i8L4Q86_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q86_1 (v 0) (v 9) (v 18) (v 27) (v 36) (v 43) (v 49) (v 65) (v
      66) (v 67)) (by
      unfold i8L4Q86_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q86_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q86_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R86
  unfold i8L4Q86_2 i8L4Q86_3 i8L4Q86_4
  ring

/-- The singular part of `Ψ₄⁽87k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S87k0 (x : ℝ) : ℝ :=
    -11 / 2 + Real.log x + Real.log x ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽87k0⁾`. -/
noncomputable def i8L4Q87k0_0 (x r_001 r_01 r_01m r_0m r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ :=
    -1 - 2 * r_01m - 2 * x ^ 4 + 3 * x - 7 / 2 * x ^ 2 - x ^ 3 / 4 - x ^ 5 / 4 +
      r_m * x ^ 6 / 2 - r_m * x ^ 2 - 9 * r_1 * x ^ 3 - 8 * r_01m * x - 8 * r_01m * x ^ 3 -
      6 * r_001 * x ^ 2 - 4 * r_1 * x - 3 * r_1 * x ^ 5 - 2 * r_01m * x ^ 4 - 2 * r_m * x +
      5 * r_m * x ^ 3 + 5 * r_m * x ^ 5 + 7 * r_1 * x ^ 4 + 9 * r_0m * x ^ 2 +
      12 * r_01 * x ^ 2 + 12 * r_0m1 * x ^ 2 - r_1 * x ^ 6 / 2 + 17 / 2 * r_m * x ^ 4 +
      19 / 2 * r_1 * x ^ 2 + r_1 * r_m * x ^ 7 - r_1 * r_m * x ^ 3 - 8 * r_1 * r_m * x ^ 4 +
      8 * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽87k0⁾`. -/
noncomputable def i8L4Q87k0_1 (x _r_001 r_01 _r_01m _r_0m _r_0m1 r_1 _r_m r_m1 : ℝ) : ℝ :=
    3 - 2 * r_m1 - x / 2 - x ^ 3 / 2 + r_1 * x ^ 4 - 12 * r_m1 * x ^ 2 - 8 * r_m1 * x -
      8 * r_m1 * x ^ 3 - 5 * r_1 * x ^ 2 - 2 * r_1 * x - 2 * r_m1 * x ^ 4 + 6 * r_01 * x ^ 2 +
      6 * r_1 * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽87k0⁾`. -/
noncomputable def i8L4Q87k0_2 (_x _r_001 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽87k0⁾`. -/
noncomputable def i8L4Q87k0_3 (_x _r_001 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽87k0⁾`. -/
noncomputable def i8L4Q87k0_4 (_x _r_001 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_87k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s87k0 x = i8L4S87k0 x + x * (i8L4Q87k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one]
      x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q87k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q87k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q87k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q87k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s87k0 i8Psi4s87k0N0 i8Psi4s87k0N1 i8Psi4s87k0N2 i8Psi4s87k0N3 i8Psi4s87k0N4
    i8Psi4s87k0W
  simp only [hpl_zero, i13hw_00, i13hw_010 hx, i13hw_10 hx, i13hw_1m hx, i13hw_m01 hx, i13hw_m10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0,
    i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S87k0 i8L4Q87k0_0 i8L4Q87k0_1 i8L4Q87k0_2 i8L4Q87k0_3 i8L4Q87k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽87k0⁾`. -/
noncomputable def i8L4R87k0 (x : ℝ) : ℝ :=
  x * (i8L4Q87k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x * i8L4Q87k0_1 x (i13Rho [zero, zero, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q87k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q87k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q87k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R87k0 : Tendsto i8L4R87k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k0_0 (v 0) (v 9) (v 27) (v 36) (v 43) (v 49) (v 65) (v 66) (v
      67)) (by
      unfold i8L4Q87k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k0_1 (v 0) (v 9) (v 27) (v 36) (v 43) (v 49) (v 65) (v 66) (v
      67)) (by
      unfold i8L4Q87k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q87k0_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q87k0_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R87k0
  unfold i8L4Q87k0_2 i8L4Q87k0_3 i8L4Q87k0_4
  ring

/-- The singular part of `Ψ₄⁽87k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S87k1 (x : ℝ) : ℝ :=
    -4 * Real.log x + 2 * Real.log x ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽87k1⁾`. -/
noncomputable def i8L4Q87k1_0 (x r_0001 r_0001m r_000m1 r_001 r_0010m r_001m r_00m r_00m1 r_01 r_01m
    r_0m _r_0m01 _r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ :=
    -49 / 2 - 17 * x ^ 2 - 2 * r_001m - 2 * r_00m1 + 2 * r_01m - 77 / 8 * x + x ^ 5 / 8 +
      7 / 4 * x ^ 4 + 11 / 2 * x ^ 3 + r_001 * x ^ 6 - 28 * r_0001 * x ^ 2 - 24 * r_0m * x ^ 3 -
      20 * r_01m * x ^ 2 - 18 * r_001 * x ^ 3 - 16 * r_001m * x - 16 * r_00m1 * x -
      14 * r_1 * x ^ 3 - 10 * r_00m * x ^ 2 - 9 * r_001 * x ^ 4 - 4 * r_m * x ^ 5 -
      3 * r_0m * x ^ 4 - 2 * r_1 * x + 2 * r_001m * x ^ 4 + 2 * r_00m1 * x ^ 4 +
      2 * r_01m * x ^ 4 + 4 * r_001 * x + 6 * r_001 * x ^ 5 + 8 * r_01m * x + 8 * r_01m * x ^ 3 +
      11 * r_0m * x ^ 2 + 12 * r_m * x ^ 3 + 15 * r_001 * x ^ 2 + 16 * r_001m * x ^ 3 +
      16 * r_00m1 * x ^ 3 + 24 * r_0010m * x ^ 2 + 72 * r_0001m * x ^ 2 + 72 * r_000m1 * x ^ 2 -
      31 / 2 * r_m * x ^ 4 - r_1 * x ^ 4 / 4 - r_m * x ^ 6 / 4 + 25 / 2 * r_01 * x ^ 2 +
      65 / 4 * r_1 * x ^ 2 + 95 / 4 * r_m * x ^ 2 - 24 * r_001 * r_0m * x ^ 5 -
      16 * r_001 * r_m * x ^ 6 - 2 * r_001 * r_m * x ^ 7 + 2 * r_001 * r_m * x ^ 3 +
      16 * r_001 * r_m * x ^ 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽87k1⁾`. -/
noncomputable def i8L4Q87k1_1 (x _r_0001 _r_0001m _r_000m1 r_001 _r_0010m _r_001m _r_00m _r_00m1
    r_01 r_01m r_0m r_0m01 r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    12 + 2 * r_01m + 2 * r_0m1 + 2 * r_m1 + 10 * x + 15 * x ^ 2 - 17 / 2 * x ^ 3 - x ^ 4 / 2 +
      x ^ 5 / 4 + r_1 * x ^ 6 - r_01 * x ^ 6 - 20 * r_m1 * x ^ 2 - 16 * r_01m * x ^ 3 -
      16 * r_0m1 * x ^ 3 - 15 * r_01 * x ^ 2 - 6 * r_01 * x ^ 3 - 6 * r_01 * x ^ 5 - 6 * r_m * x -
      4 * r_01 * x - 4 * r_1 * x - 2 * r_01m * x ^ 4 - 2 * r_0m1 * x ^ 4 + 2 * r_1 * x ^ 5 +
      2 * r_m * x ^ 3 + 2 * r_m1 * x ^ 4 + 8 * r_m1 * x + 8 * r_m1 * x ^ 3 + 10 * r_0m * x ^ 2 +
      14 * r_001 * x ^ 2 + 15 * r_01 * x ^ 4 + 16 * r_01m * x + 16 * r_0m1 * x +
      17 * r_m * x ^ 4 + 24 * r_0m01 * x ^ 2 + 38 * r_1 * x ^ 3 - 73 / 2 * r_m * x ^ 2 -
      39 / 2 * r_1 * x ^ 2 - 35 / 2 * r_1 * x ^ 4 - r_m * x ^ 6 / 2 - 16 * r_01 * r_m * x ^ 4 -
      8 * r_1 * r_m * x ^ 4 - 8 * r_1 * r_m * x ^ 6 - 2 * r_01 * r_m * x ^ 3 -
      2 * r_1 * r_m * x ^ 3 - 2 * r_1 * r_m * x ^ 7 + 2 * r_01 * r_m * x ^ 7 +
      16 * r_01 * r_m * x ^ 6 + 20 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽87k1⁾`. -/
noncomputable def i8L4Q87k1_2 (_x _r_0001 _r_0001m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m1
    _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽87k1⁾`. -/
noncomputable def i8L4Q87k1_3 (_x _r_0001 _r_0001m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m1
    _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽87k1⁾`. -/
noncomputable def i8L4Q87k1_4 (_x _r_0001 _r_0001m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m1
    _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_87k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s87k1 x = i8L4S87k1 x + x * (i8L4Q87k1_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero,
      zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q87k1_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
      [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q87k1_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q87k1_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q87k1_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s87k1 i8Psi4s87k1N0 i8Psi4s87k1N1 i8Psi4s87k1N2 i8Psi4s87k1N3 i8Psi4s87k1N4
    i8Psi4s87k1W
  simp only [hpl_zero, i13hw_00, i13hw_0010 hx, i13hw_010 hx, i13hw_0m0 hx, i13hw_0m001 hx,
    i13hw_0m010 hx, i13hw_10 hx, i13hw_10m hx, i13hw_1m0 hx, i13hw_m0 hx, i13hw_m001 hx, i13hw_m010
    hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_0001m h0, i13hpl_rho_000m1 h0, i13hpl_rho_001 h0,
    i13hpl_rho_0010m h0, i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1 h0, i13hpl_rho_01
    h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S87k1 i8L4Q87k1_0 i8L4Q87k1_1 i8L4Q87k1_2 i8L4Q87k1_3 i8L4Q87k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽87k1⁾`. -/
noncomputable def i8L4R87k1 (x : ℝ) : ℝ :=
  x * (i8L4Q87k1_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x)
    (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q87k1_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one,
    negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q87k1_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q87k1_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q87k1_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R87k1 : Tendsto i8L4R87k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k1_0 (v 0) (v 3) (v 5) (v 7) (v 9) (v 11) (v 15) (v 18) (v
      21) (v 27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q87k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k1_1 (v 0) (v 3) (v 5) (v 7) (v 9) (v 11) (v 15) (v 18) (v
      21) (v 27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q87k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q87k1_0 x (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne, one]
    x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q87k1_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R87k1
  unfold i8L4Q87k1_2 i8L4Q87k1_3 i8L4Q87k1_4
  ring

/-- The singular part of `Ψ₄⁽87k2⁾` at `ξ = 0`. -/
noncomputable def i8L4S87k2 (x : ℝ) : ℝ :=
    -21 / 4 - Real.log x ^ 2 + 3 * Real.log x + Real.log x ^ 3 / 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽87k2⁾`. -/
noncomputable def i8L4Q87k2_0 (x r_0001 r_0001m r_000m1 r_001 r_0010m r_001m r_00m1 r_01 _r_01m r_0m
    _r_0m01 r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    99 / 4 + 2 * r_001m + 2 * r_00m1 - 43 / 8 * x ^ 3 - 7 / 4 * x ^ 4 - r_m1 / 2 - x ^ 2 / 2 -
      x ^ 5 / 8 + 35 / 4 * x + r_m1 * x ^ 4 / 2 - r_001 * x ^ 6 - 72 * r_0001m * x ^ 2 -
      48 * r_000m1 * x ^ 2 - 24 * r_0010m * x ^ 2 - 16 * r_001m * x ^ 3 - 16 * r_00m1 * x ^ 3 -
      16 * r_m1 * x - 13 * r_001 * x ^ 2 - 6 * r_001 * x ^ 5 - 4 * r_001 * x -
      2 * r_001m * x ^ 4 - 2 * r_00m1 * x ^ 4 - 2 * r_m * x - 2 * r_m * x ^ 3 + 3 * r_0m * x ^ 4 +
      4 * r_m * x ^ 5 + 9 * r_001 * x ^ 4 + 16 * r_001m * x + 16 * r_00m1 * x +
      16 * r_m * x ^ 4 + 16 * r_m1 * x ^ 3 + 18 * r_001 * x ^ 3 + 24 * r_0m * x ^ 3 +
      30 * r_01 * x ^ 2 + 30 * r_0m1 * x ^ 2 + 42 * r_0001 * x ^ 2 - 65 / 4 * r_m * x ^ 2 -
      61 / 2 * r_1 * x ^ 3 - 3 / 2 * r_1 * x - r_1 * x ^ 4 / 2 + r_m * x ^ 6 / 4 +
      65 / 2 * r_1 * x ^ 2 - 16 * r_001 * r_m * x ^ 4 - 2 * r_001 * r_m * x ^ 3 +
      2 * r_001 * r_m * x ^ 7 + 16 * r_001 * r_m * x ^ 6 + 24 * r_001 * r_0m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽87k2⁾`. -/
noncomputable def i8L4Q87k2_1 (x _r_0001 _r_0001m _r_000m1 r_001 _r_0010m _r_001m r_00m1 r_01 r_01m
    _r_0m r_0m01 r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    -29 / 2 - r_m1 - 10 * x - 2 * r_01m - 2 * r_0m1 + 3 * x ^ 3 - 11 / 2 * x ^ 2 + x ^ 5 / 4 +
      5 / 2 * x ^ 4 + r_01 * x ^ 6 + r_1 * x ^ 4 / 2 - r_1 * x - r_m1 * x ^ 4 -
      30 * r_m1 * x ^ 2 - 28 * r_001 * x ^ 2 - 24 * r_00m1 * x ^ 2 - 24 * r_0m01 * x ^ 2 -
      16 * r_01m * x - 16 * r_0m1 * x - 16 * r_m * x ^ 4 - 16 * r_m1 * x - 16 * r_m1 * x ^ 3 -
      15 * r_01 * x ^ 4 - 6 * r_m * x ^ 5 + 2 * r_01m * x ^ 4 + 2 * r_0m1 * x ^ 4 + 2 * r_m * x +
      4 * r_01 * x + 4 * r_m * x ^ 3 + 6 * r_01 * x ^ 3 + 6 * r_01 * x ^ 5 + 13 * r_01 * x ^ 2 +
      15 * r_1 * x ^ 3 + 16 * r_01m * x ^ 3 + 16 * r_0m1 * x ^ 3 - 29 / 2 * r_1 * x ^ 2 -
      r_m * x ^ 6 / 2 + 33 / 2 * r_m * x ^ 2 - 16 * r_01 * r_m * x ^ 6 - 2 * r_01 * r_m * x ^ 7 +
      2 * r_01 * r_m * x ^ 3 + 16 * r_01 * r_m * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽87k2⁾`. -/
noncomputable def i8L4Q87k2_2 (x _r_0001 _r_0001m _r_000m1 _r_001 _r_0010m _r_001m _r_00m1 r_01
    _r_01m _r_0m _r_0m01 r_0m1 r_1 _r_m r_m1 : ℝ) : ℝ :=
    7 / 2 - r_m1 + x ^ 3 / 4 + 7 / 4 * x + r_m1 * x ^ 4 - r_1 * x - 8 * r_m1 * x -
      7 * r_1 * x ^ 3 + 7 * r_01 * x ^ 2 + 8 * r_m1 * x ^ 3 + 12 * r_0m1 * x ^ 2 -
      r_1 * x ^ 4 / 2 + 17 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽87k2⁾`. -/
noncomputable def i8L4Q87k2_3 (_x _r_0001 _r_0001m _r_000m1 _r_001 _r_0010m _r_001m _r_00m1 _r_01
    _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽87k2⁾`. -/
noncomputable def i8L4Q87k2_4 (_x _r_0001 _r_0001m _r_000m1 _r_001 _r_0010m _r_001m _r_00m1 _r_01
    _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_87k2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s87k2 x = i8L4S87k2 x + x * (i8L4Q87k2_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero,
      zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q87k2_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
      [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q87k2_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q87k2_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q87k2_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s87k2 i8Psi4s87k2N0 i8Psi4s87k2N1 i8Psi4s87k2N2 i8Psi4s87k2N3 i8Psi4s87k2N4
    i8Psi4s87k2W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m10 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_0m10
    hx, i13hw_0m100 hx, i13hw_10 hx, i13hw_100 hx, i13hw_m01 hx, i13hw_m10 hx, i13hw_m100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_0001m h0, i13hpl_rho_000m1 h0, i13hpl_rho_001 h0,
    i13hpl_rho_0010m h0, i13hpl_rho_001m h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_01m
    h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0,
    i13hpl_rho_m1 h0]
  unfold i8L4S87k2 i8L4Q87k2_0 i8L4Q87k2_1 i8L4Q87k2_2 i8L4Q87k2_3 i8L4Q87k2_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽87k2⁾`. -/
noncomputable def i8L4R87k2 (x : ℝ) : ℝ :=
  x * (i8L4Q87k2_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x)
    (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x * i8L4Q87k2_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
    [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero,
    zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q87k2_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q87k2_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q87k2_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R87k2 : Tendsto i8L4R87k2 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k2_0 (v 0) (v 3) (v 5) (v 7) (v 9) (v 11) (v 15) (v 21) (v
      27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q87k2_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k2_1 (v 0) (v 3) (v 5) (v 7) (v 9) (v 11) (v 15) (v 21) (v
      27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q87k2_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k2_2 (v 0) (v 3) (v 5) (v 7) (v 9) (v 11) (v 15) (v 21) (v
      27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q87k2_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q87k2_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero,
    negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho
    [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q87k2_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q87k2_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R87k2
  unfold i8L4Q87k2_3 i8L4Q87k2_4
  ring

/-- The singular part of `Ψ₄⁽87k3⁾` at `ξ = 0`. -/
noncomputable def i8L4S87k3 (x : ℝ) : ℝ :=
    -21 / 4 - Real.log x ^ 2 + 3 * Real.log x + Real.log x ^ 3 / 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽87k3⁾`. -/
noncomputable def i8L4Q87k3_0 (x r_0001m r_000m r_000m1 r_001m r_00m r_00m01 r_00m1 r_01 r_01m r_0m
    _r_0m01 _r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    125 / 4 + r_m1 / 2 + 2 * r_001m + 2 * r_00m1 - 17 / 4 * x ^ 4 - x ^ 5 / 4 + 21 / 2 * x ^ 2 +
      53 / 8 * x ^ 3 + 183 / 8 * x + r_00m * x ^ 6 - 72 * r_000m1 * x ^ 2 -
      48 * r_0001m * x ^ 2 - 34 * r_01m * x ^ 2 - 24 * r_00m01 * x ^ 2 - 19 * r_00m * x ^ 2 -
      16 * r_001m * x ^ 3 - 16 * r_00m1 * x ^ 3 - 16 * r_m1 * x ^ 3 - 4 * r_00m * x -
      3 * r_01 * x ^ 4 - 2 * r_001m * x ^ 4 - 2 * r_00m1 * x ^ 4 - 2 * r_m * x +
      10 * r_00m * x ^ 5 + 10 * r_1 * x ^ 3 + 16 * r_001m * x + 16 * r_00m1 * x + 16 * r_m1 * x +
      23 * r_00m * x ^ 4 + 24 * r_01 * x ^ 3 + 32 * r_1 * x ^ 4 + 34 * r_00m * x ^ 3 +
      34 * r_0m * x ^ 2 + 54 * r_000m * x ^ 2 - 63 / 2 * r_1 * x ^ 2 - 15 / 2 * r_1 * x ^ 5 -
      5 / 2 * r_1 * x - r_1 * x ^ 6 / 2 - r_m1 * x ^ 4 / 2 + r_m * x ^ 6 / 4 +
      17 / 2 * r_m * x ^ 5 + 33 / 2 * r_m * x ^ 4 + 51 / 2 * r_m * x ^ 3 +
      61 / 4 * r_m * x ^ 2 + r_1 * r_m * x ^ 7 / 2 - 16 * r_00m * r_1 * x ^ 4 -
      16 * r_1 * r_m * x ^ 4 - 2 * r_00m * r_1 * x ^ 3 + 2 * r_00m * r_1 * x ^ 7 +
      16 * r_00m * r_1 * x ^ 6 + 16 * r_1 * r_m * x ^ 6 + 24 * r_00m * r_01 * x ^ 5 -
      r_1 * r_m * x ^ 3 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽87k3⁾`. -/
noncomputable def i8L4Q87k3_1 (x _r_0001m _r_000m _r_000m1 r_001m r_00m _r_00m01 r_00m1 r_01 r_01m
    r_0m r_0m01 r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    -35 / 2 + r_m1 + x ^ 5 / 2 - 12 * x ^ 3 - 2 * r_01m - 2 * r_0m1 - 39 / 4 * x -
      5 / 2 * x ^ 2 + 11 / 2 * x ^ 4 + r_1 * x + r_1 * x ^ 6 + r_m1 * x ^ 4 + r_m * x ^ 4 / 2 -
      r_0m * x ^ 6 - 49 * r_1 * x ^ 4 - 36 * r_00m * x ^ 2 - 34 * r_0m * x ^ 3 -
      34 * r_m * x ^ 2 - 34 * r_m1 * x ^ 2 - 24 * r_01 * x ^ 3 - 23 * r_0m * x ^ 4 -
      16 * r_01m * x - 16 * r_0m1 * x - 10 * r_0m * x ^ 5 - 9 * r_m * x ^ 5 - 2 * r_m * x +
      2 * r_01m * x ^ 4 + 2 * r_0m1 * x ^ 4 + 4 * r_0m * x + 6 * r_01 * x ^ 4 + 9 * r_1 * x ^ 5 +
      9 * r_m * x ^ 3 + 16 * r_01m * x ^ 3 + 16 * r_0m1 * x ^ 3 + 16 * r_m1 * x +
      16 * r_m1 * x ^ 3 + 19 * r_0m * x ^ 2 + 24 * r_001m * x ^ 2 + 24 * r_0m01 * x ^ 2 +
      38 * r_1 * x ^ 3 + 48 * r_00m1 * x ^ 2 - r_m * x ^ 6 / 2 - r_1 * r_m * x ^ 3 -
      r_1 * r_m * x ^ 7 - 24 * r_01 * r_0m * x ^ 5 - 16 * r_0m * r_1 * x ^ 6 -
      16 * r_1 * r_m * x ^ 4 - 16 * r_1 * r_m * x ^ 6 - 2 * r_0m * r_1 * x ^ 7 +
      2 * r_0m * r_1 * x ^ 3 + 16 * r_0m * r_1 * x ^ 4 + 34 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽87k3⁾`. -/
noncomputable def i8L4Q87k3_2 (x _r_0001m _r_000m _r_000m1 _r_001m _r_00m _r_00m01 _r_00m1 _r_01
    r_01m r_0m _r_0m01 _r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    9 / 2 + r_m1 - 2 * x ^ 4 + 2 * x ^ 2 + 6 * x - x ^ 5 / 4 + x ^ 3 / 4 + r_m * x ^ 6 / 2 -
      r_1 * x - r_m * x ^ 2 - r_m1 * x ^ 4 - 8 * r_m1 * x ^ 3 - 3 * r_1 * x ^ 5 - 2 * r_m * x +
      4 * r_1 * x ^ 3 + 5 * r_m * x ^ 3 + 5 * r_m * x ^ 5 + 8 * r_1 * x ^ 4 + 8 * r_m1 * x +
      9 * r_0m * x ^ 2 + 12 * r_01m * x ^ 2 - 15 / 2 * r_1 * x ^ 2 - r_1 * x ^ 6 / 2 +
      17 / 2 * r_m * x ^ 4 + r_1 * r_m * x ^ 7 - r_1 * r_m * x ^ 3 - 8 * r_1 * r_m * x ^ 4 +
      8 * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽87k3⁾`. -/
noncomputable def i8L4Q87k3_3 (_x _r_0001m _r_000m _r_000m1 _r_001m _r_00m _r_00m01 _r_00m1 _r_01
    _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽87k3⁾`. -/
noncomputable def i8L4Q87k3_4 (_x _r_0001m _r_000m _r_000m1 _r_001m _r_00m _r_00m01 _r_00m1 _r_01
    _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_87k3_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s87k3 x = i8L4S87k3 x + x * (i8L4Q87k3_0 x (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho
      [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
      zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q87k3_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q87k3_2 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q87k3_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q87k3_4 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s87k3 i8Psi4s87k3N0 i8Psi4s87k3N1 i8Psi4s87k3N2 i8Psi4s87k3N3 i8Psi4s87k3N4
    i8Psi4s87k3W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_001m0 hx, i13hw_010m hx, i13hw_01m0 hx,
    i13hw_01m00 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_10m hx, i13hw_1m hx, i13hw_1m0 hx, i13hw_1m00
    hx, i13hw_m0 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_0001m h0, i13hpl_rho_000m h0, i13hpl_rho_000m1 h0, i13hpl_rho_001m h0,
    i13hpl_rho_00m h0, i13hpl_rho_00m01 h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0,
    i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0,
    i13hpl_rho_m1 h0]
  unfold i8L4S87k3 i8L4Q87k3_0 i8L4Q87k3_1 i8L4Q87k3_2 i8L4Q87k3_3 i8L4Q87k3_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽87k3⁾`. -/
noncomputable def i8L4R87k3 (x : ℝ) : ℝ :=
  x * (i8L4Q87k3_0 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x * i8L4Q87k3_1 x (i13Rho [zero, zero, zero, one, negOne] x)
    (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero,
    zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q87k3_2 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q87k3_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q87k3_4 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R87k3 : Tendsto i8L4R87k3 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k3_0 (v 0) (v 5) (v 6) (v 7) (v 15) (v 18) (v 19) (v 21) (v
      27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q87k3_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k3_1 (v 0) (v 5) (v 6) (v 7) (v 15) (v 18) (v 19) (v 21) (v
      27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q87k3_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k3_2 (v 0) (v 5) (v 6) (v 7) (v 15) (v 18) (v 19) (v 21) (v
      27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q87k3_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q87k3_0 x (i13Rho [zero,
    zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q87k3_1 x (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one]
      x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q87k3_2 x (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one]
      x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R87k3
  unfold i8L4Q87k3_3 i8L4Q87k3_4
  ring

/-- The singular part of `Ψ₄⁽87k4⁾` at `ξ = 0`. -/
noncomputable def i8L4S87k4 (x : ℝ) : ℝ :=
    3 / 2 + Real.log x ^ 2 - 3 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽87k4⁾`. -/
noncomputable def i8L4Q87k4_0 (x r_0001m r_000m r_000m1 r_001m r_00m r_00m01 r_00m1 r_01 _r_01m r_0m
    _r_0m01 _r_0m1 r_1 r_m : ℝ) : ℝ :=
    -45 / 2 - 2 * r_001m - 2 * r_00m1 - 135 / 8 * x - 47 / 2 * x ^ 2 - 27 / 4 * x ^ 3 +
      x ^ 4 / 4 + x ^ 5 / 8 - r_00m * x ^ 6 - 36 * r_000m * x ^ 2 - 34 * r_00m * x ^ 3 -
      24 * r_01 * x ^ 3 - 23 * r_00m * x ^ 4 - 16 * r_001m * x - 16 * r_00m1 * x -
      16 * r_1 * x ^ 4 - 10 * r_00m * x ^ 5 - 2 * r_1 * x ^ 3 - 2 * r_m * x + 2 * r_001m * x ^ 4 +
      2 * r_00m1 * x ^ 4 + 2 * r_1 * x + 3 * r_01 * x ^ 4 + 4 * r_00m * x + 16 * r_001m * x ^ 3 +
      16 * r_00m1 * x ^ 3 + 17 * r_00m * x ^ 2 + 18 * r_m * x ^ 3 + 24 * r_00m01 * x ^ 2 +
      72 * r_0001m * x ^ 2 + 72 * r_000m1 * x ^ 2 + r_1 * x ^ 6 / 4 + r_m * x ^ 4 / 4 +
      39 / 2 * r_0m * x ^ 2 + 63 / 4 * r_1 * x ^ 2 + 63 / 4 * r_m * x ^ 2 -
      24 * r_00m * r_01 * x ^ 5 - 16 * r_00m * r_1 * x ^ 6 - 2 * r_00m * r_1 * x ^ 7 +
      2 * r_00m * r_1 * x ^ 3 + 16 * r_00m * r_1 * x ^ 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽87k4⁾`. -/
noncomputable def i8L4Q87k4_1 (x _r_0001m _r_000m _r_000m1 r_001m r_00m _r_00m01 r_00m1 r_01 r_01m
    r_0m r_0m01 r_0m1 r_1 r_m : ℝ) : ℝ :=
    9 + 2 * r_01m + 2 * r_0m1 + 10 * x + 15 * x ^ 2 - 3 / 2 * x ^ 4 - x ^ 5 / 4 +
      7 / 2 * x ^ 3 + r_0m * x ^ 6 - 48 * r_001m * x ^ 2 - 48 * r_00m1 * x ^ 2 -
      24 * r_0m01 * x ^ 2 - 18 * r_m * x ^ 3 - 17 * r_0m * x ^ 2 - 16 * r_01m * x ^ 3 -
      16 * r_0m1 * x ^ 3 - 6 * r_01 * x ^ 4 - 4 * r_0m * x - 2 * r_01m * x ^ 4 -
      2 * r_0m1 * x ^ 4 - 2 * r_1 * x - 2 * r_1 * x ^ 5 - 2 * r_m * x + 4 * r_1 * x ^ 3 +
      10 * r_0m * x ^ 5 + 16 * r_01m * x + 16 * r_0m1 * x + 16 * r_1 * x ^ 4 +
      18 * r_00m * x ^ 2 + 23 * r_0m * x ^ 4 + 24 * r_01 * x ^ 3 + 34 * r_0m * x ^ 3 -
      39 / 2 * r_m * x ^ 2 - 31 / 2 * r_1 * x ^ 2 - r_1 * x ^ 6 / 2 - r_m * x ^ 4 / 2 -
      16 * r_0m * r_1 * x ^ 4 - 2 * r_0m * r_1 * x ^ 3 + 2 * r_0m * r_1 * x ^ 7 +
      16 * r_0m * r_1 * x ^ 6 + 24 * r_01 * r_0m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽87k4⁾`. -/
noncomputable def i8L4Q87k4_2 (_x _r_0001m _r_000m _r_000m1 _r_001m _r_00m _r_00m01 _r_00m1 _r_01
    _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽87k4⁾`. -/
noncomputable def i8L4Q87k4_3 (_x _r_0001m _r_000m _r_000m1 _r_001m _r_00m _r_00m01 _r_00m1 _r_01
    _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽87k4⁾`. -/
noncomputable def i8L4Q87k4_4 (_x _r_0001m _r_000m _r_000m1 _r_001m _r_00m _r_00m01 _r_00m1 _r_01
    _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

theorem i8L4_87k4_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s87k4 x = i8L4S87k4 x + x * (i8L4Q87k4_0 x (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho
      [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
      zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q87k4_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q87k4_2 x (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q87k4_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) + Real.log x ^ 4 * i8L4Q87k4_4 x (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s87k4 i8Psi4s87k4N0 i8Psi4s87k4N1 i8Psi4s87k4N2 i8Psi4s87k4N3 i8Psi4s87k4N4
    i8Psi4s87k4W
  simp only [hpl_zero, i13hw_00, i13hw_00m0 hx, i13hw_010m0 hx, i13hw_0m0 hx, i13hw_100m hx,
    i13hw_10m0 hx, i13hw_m0 hx, i8hw_0100m hx]
  simp only [i13hpl_rho_0001m h0, i13hpl_rho_000m h0, i13hpl_rho_000m1 h0, i13hpl_rho_001m h0,
    i13hpl_rho_00m h0, i13hpl_rho_00m01 h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0,
    i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0]
  unfold i8L4S87k4 i8L4Q87k4_0 i8L4Q87k4_1 i8L4Q87k4_2 i8L4Q87k4_3 i8L4Q87k4_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽87k4⁾`. -/
noncomputable def i8L4R87k4 (x : ℝ) : ℝ :=
  x * (i8L4Q87k4_0 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    + Real.log x * i8L4Q87k4_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q87k4_2 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho
    [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q87k4_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) + Real.log x ^ 4 * i8L4Q87k4_4 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho
    [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R87k4 : Tendsto i8L4R87k4 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k4_0 (v 0) (v 5) (v 6) (v 7) (v 15) (v 18) (v 19) (v 21) (v
      27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66)) (by
      unfold i8L4Q87k4_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q87k4_1 (v 0) (v 5) (v 6) (v 7) (v 15) (v 18) (v 19) (v 21) (v
      27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66)) (by
      unfold i8L4Q87k4_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q87k4_0 x (i13Rho [zero, zero,
    zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
    one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q87k4_1 x (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one]
      x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R87k4
  unfold i8L4Q87k4_2 i8L4Q87k4_3 i8L4Q87k4_4
  ring

/-- The singular part of `Ψ₄⁽88⁾` at `ξ = 0`. -/
noncomputable def i8L4S88 (x : ℝ) : ℝ :=
    (16 - 4 * zeta3 + 16 * Real.log x - 2 / 3 * π ^ 2 - 4 * Real.log x * zeta3 +
      8 * x * Real.log x ^ 2 - 2 / 3 * Real.log x * π ^ 2 + 2 * x * zeta3 * Real.log x ^ 2 +
      π ^ 2 * x * Real.log x ^ 2 / 3) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽88⁾`. -/
noncomputable def i8L4Q88_0 (x : ℝ) : ℝ :=
    -16 + 4 * x + 4 * zeta3 + 2 / 3 * π ^ 2 + x * zeta3 + π ^ 2 * x / 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽88⁾`. -/
noncomputable def i8L4Q88_1 (x : ℝ) : ℝ :=
    16 - 8 * x - 4 * zeta3 - 2 / 3 * π ^ 2 - 2 * x * zeta3 - π ^ 2 * x / 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽88⁾`. -/
noncomputable def i8L4Q88_2 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽88⁾`. -/
noncomputable def i8L4Q88_3 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽88⁾`. -/
noncomputable def i8L4Q88_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_88_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s88 x = i8L4S88 x + x * (i8L4Q88_0 x + Real.log x * i8L4Q88_1 x +
      Real.log x ^ 2 * i8L4Q88_2 x + Real.log x ^ 3 * i8L4Q88_3 x +
      Real.log x ^ 4 * i8L4Q88_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s88 i8Psi4s88N0 i8Psi4s88N1 i8Psi4s88N2 i8Psi4s88N3 i8Psi4s88N4 i8Psi4s88W
  simp only [hpl_zero, i13hw_00]

  unfold i8L4S88 i8L4Q88_0 i8L4Q88_1 i8L4Q88_2 i8L4Q88_3 i8L4Q88_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽88⁾`. -/
noncomputable def i8L4R88 (x : ℝ) : ℝ :=
  x * (i8L4Q88_0 x + Real.log x * i8L4Q88_1 x + Real.log x ^ 2 * i8L4Q88_2 x +
    Real.log x ^ 3 * i8L4Q88_3 x + Real.log x ^ 4 * i8L4Q88_4 x)

theorem tendsto_i8L4R88 : Tendsto i8L4R88 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q88_0 (v 0)) (by
      unfold i8L4Q88_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q88_1 (v 0)) (by
      unfold i8L4Q88_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q88_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q88_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R88
  unfold i8L4Q88_2 i8L4Q88_3 i8L4Q88_4
  ring

/-- The regular parts of group 7. -/
noncomputable def i8L4RG7 (x : ℝ) : ℝ :=
  i8L4R83 x + i8L4R84 x + i8L4R85 x + i8L4R86 x + i8L4R87k0 x + i8L4R87k1 x +
    i8L4R87k2 x + i8L4R87k3 x + i8L4R87k4 x + i8L4R88 x

theorem tendsto_i8L4RG7 : Tendsto i8L4RG7 (𝓝[>] 0) (𝓝 0) := by
  have H := (((((((((tendsto_i8L4R83.add tendsto_i8L4R84).add tendsto_i8L4R85).add
    tendsto_i8L4R86).add tendsto_i8L4R87k0).add tendsto_i8L4R87k1).add tendsto_i8L4R87k2).add
    tendsto_i8L4R87k3).add tendsto_i8L4R87k4).add tendsto_i8L4R88)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
