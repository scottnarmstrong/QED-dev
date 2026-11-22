/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L7
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 8

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_89_eq`, `QED.ThreeLoopD.tendsto_i8L4RG8` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽89⁾` at `ξ = 0`. -/
noncomputable def i8L4S89 (x : ℝ) : ℝ :=
    (16 + 8 * Real.log x ^ 2 + 16 * Real.log x - 2 / 3 * π ^ 2 - 8 / 3 * x * Real.log x ^ 3 -
      2 / 3 * Real.log x * π ^ 2 - π ^ 2 * Real.log x ^ 2 / 3 +
      π ^ 2 * x * Real.log x ^ 3 / 9) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽89⁾`. -/
noncomputable def i8L4Q89_0 (x : ℝ) : ℝ :=
    16 + 2 * x - 2 / 3 * π ^ 2 - π ^ 2 * x / 12

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽89⁾`. -/
noncomputable def i8L4Q89_1 (x : ℝ) : ℝ :=
    -16 - 4 * x + 2 / 3 * π ^ 2 + π ^ 2 * x / 6

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽89⁾`. -/
noncomputable def i8L4Q89_2 (x : ℝ) : ℝ :=
    8 + 4 * x - π ^ 2 / 3 - π ^ 2 * x / 6

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽89⁾`. -/
noncomputable def i8L4Q89_3 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽89⁾`. -/
noncomputable def i8L4Q89_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_89_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s89 x = i8L4S89 x + x * (i8L4Q89_0 x + Real.log x * i8L4Q89_1 x +
      Real.log x ^ 2 * i8L4Q89_2 x + Real.log x ^ 3 * i8L4Q89_3 x +
      Real.log x ^ 4 * i8L4Q89_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s89 i8Psi4s89N0 i8Psi4s89N1 i8Psi4s89N2 i8Psi4s89N3 i8Psi4s89N4 i8Psi4s89W
  simp only [hpl_zero, i13hw_00, i13hw_000]

  unfold i8L4S89 i8L4Q89_0 i8L4Q89_1 i8L4Q89_2 i8L4Q89_3 i8L4Q89_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽89⁾`. -/
noncomputable def i8L4R89 (x : ℝ) : ℝ :=
  x * (i8L4Q89_0 x + Real.log x * i8L4Q89_1 x + Real.log x ^ 2 * i8L4Q89_2 x +
    Real.log x ^ 3 * i8L4Q89_3 x + Real.log x ^ 4 * i8L4Q89_4 x)

theorem tendsto_i8L4R89 : Tendsto i8L4R89 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q89_0 (v 0)) (by
      unfold i8L4Q89_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q89_1 (v 0)) (by
      unfold i8L4Q89_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q89_2 (v 0)) (by
      unfold i8L4Q89_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q89_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q89_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q89_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R89
  unfold i8L4Q89_3 i8L4Q89_4
  ring

/-- The singular part of `Ψ₄⁽90⁾` at `ξ = 0`. -/
noncomputable def i8L4S90 (x : ℝ) : ℝ :=
    2 / 3 * π ^ 2 - π ^ 2 * Real.log x ^ 2 / 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽90⁾`. -/
noncomputable def i8L4Q90_0 (x r_00m r_0m r_m : ℝ) : ℝ :=
    π ^ 2 / 3 - 5 / 12 * π ^ 2 * x + π ^ 2 * x ^ 2 / 6 + π ^ 2 * x ^ 3 / 12 -
      π ^ 2 * r_0m * x ^ 2 - 2 / 3 * π ^ 2 * r_m * x ^ 3 - π ^ 2 * r_m * x ^ 4 / 6 +
      π ^ 2 * r_m * x ^ 2 / 6 + 2 / 3 * π ^ 2 * r_00m * x ^ 2 + 2 / 3 * π ^ 2 * r_m * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽90⁾`. -/
noncomputable def i8L4Q90_1 (x _r_00m r_0m r_m : ℝ) : ℝ :=
    -π ^ 2 / 3 - π ^ 2 * x ^ 3 / 6 + π ^ 2 * x / 6 + π ^ 2 * r_m * x ^ 2 -
      2 / 3 * π ^ 2 * r_0m * x ^ 2 + π ^ 2 * r_m * x ^ 4 / 3 + 2 / 3 * π ^ 2 * r_m * x +
      2 / 3 * π ^ 2 * r_m * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽90⁾`. -/
noncomputable def i8L4Q90_2 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽90⁾`. -/
noncomputable def i8L4Q90_3 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽90⁾`. -/
noncomputable def i8L4Q90_4 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_90_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s90 x = i8L4S90 x + x * (i8L4Q90_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q90_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q90_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q90_3 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q90_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s90 i8Psi4s90N0 i8Psi4s90N1 i8Psi4s90N2 i8Psi4s90N3 i8Psi4s90N4 i8Psi4s90W
  simp only [hpl_zero, i13hw_00, i13hw_0m0 hx, i13hw_m0 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S90 i8L4Q90_0 i8L4Q90_1 i8L4Q90_2 i8L4Q90_3 i8L4Q90_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽90⁾`. -/
noncomputable def i8L4R90 (x : ℝ) : ℝ :=
  x * (i8L4Q90_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q90_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q90_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q90_3 x (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q90_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x))

theorem tendsto_i8L4R90 : Tendsto i8L4R90 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q90_0 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q90_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q90_1 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q90_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q90_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q90_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R90
  unfold i8L4Q90_2 i8L4Q90_3 i8L4Q90_4
  ring

/-- The singular part of `Ψ₄⁽91⁾` at `ξ = 0`. -/
noncomputable def i8L4S91 (x : ℝ) : ℝ :=
    16 - 4 * Real.log x ^ 2 + 4 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽91⁾`. -/
noncomputable def i8L4Q91_0 (x r_0000m _r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    13 - 2 * x ^ 2 - 9 / 2 * x + r_0m * x ^ 4 - 8 * r_00m * x ^ 3 - 2 * r_00m * x ^ 2 -
      2 * r_00m * x ^ 4 + 8 * r_00m * x + 8 * r_0m * x + 8 * r_0m * x ^ 3 + 15 * r_0m * x ^ 2 +
      16 * r_0000m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽91⁾`. -/
noncomputable def i8L4Q91_1 (x _r_0000m r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -13 + 6 * x ^ 2 + 9 * x - r_m * x ^ 4 - 16 * r_000m * x ^ 2 - 15 * r_m * x ^ 2 - 8 * r_m * x -
      8 * r_m * x ^ 3 + 2 * r_0m * x ^ 2 + 4 * r_00m * x ^ 4 + 8 * r_00m * x + 8 * r_00m * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽91⁾`. -/
noncomputable def i8L4Q91_2 (x _r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    3 - 2 * x ^ 2 - x / 2 + r_m * x ^ 4 - r_m * x ^ 2 - 4 * r_0m * x - 4 * r_0m * x ^ 3 -
      4 * r_m * x - 2 * r_0m * x ^ 4 + 4 * r_00m * x ^ 2 + 4 * r_m * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽91⁾`. -/
noncomputable def i8L4Q91_3 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽91⁾`. -/
noncomputable def i8L4Q91_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_91_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s91 x = i8L4S91 x + x * (i8L4Q91_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [negOne] x) + Real.log x * i8L4Q91_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q91_2 x (i13Rho [zero, zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q91_3 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q91_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s91 i8Psi4s91N0 i8Psi4s91N1 i8Psi4s91N2 i8Psi4s91N3 i8Psi4s91N4 i8Psi4s91W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_000m0 hx, i13hw_00m0 hx, i13hw_00m00 hx, i13hw_0m0
    hx, i13hw_0m00 hx, i13hw_m0 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S91 i8L4Q91_0 i8L4Q91_1 i8L4Q91_2 i8L4Q91_3 i8L4Q91_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽91⁾`. -/
noncomputable def i8L4R91 (x : ℝ) : ℝ :=
  x * (i8L4Q91_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q91_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q91_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q91_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q91_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R91 : Tendsto i8L4R91 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q91_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q91_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q91_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q91_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q91_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q91_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q91_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q91_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q91_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R91
  unfold i8L4Q91_3 i8L4Q91_4
  ring

/-- The singular part of `Ψ₄⁽92⁾` at `ξ = 0`. -/
noncomputable def i8L4S92 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽92⁾`. -/
noncomputable def i8L4Q92_0 (x r_000m r_000mm r_00m r_00m0m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -14 + x + 4 * x ^ 2 - 31 / 8 * x ^ 3 - x ^ 4 / 2 + x ^ 5 / 4 - r_0m * x ^ 6 -
      24 * r_000m * x ^ 2 - 24 * r_000mm * x ^ 2 - 16 * r_0m * x ^ 2 - 8 * r_00m0m * x ^ 2 -
      8 * r_0mm * x ^ 3 - 8 * r_m * x ^ 2 - 2 * r_0m * x ^ 5 - 2 * r_0mm * x ^ 4 +
      2 * r_0mm * x ^ 2 + 4 * r_0m * x ^ 3 + 4 * r_0m * x ^ 4 + 6 * r_0m ^ 2 * x ^ 5 +
      8 * r_0mm * x + 12 * r_00m * x ^ 2 - r_m * x ^ 6 / 2 + 17 / 2 * r_m * x ^ 4 -
      8 * r_0m * r_m * x ^ 4 - 2 * r_0m * r_m * x ^ 5 + 2 * r_0m * r_m * x ^ 7 +
      8 * r_0m * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽92⁾`. -/
noncomputable def i8L4Q92_1 (x _r_000m _r_000mm r_00m _r_00m0m r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    14 - 6 * x ^ 2 + 2 * x + 2 * x ^ 4 - 3 / 4 * x ^ 5 + 7 / 2 * x ^ 3 + r_m ^ 2 * x ^ 5 -
      r_m ^ 2 * x ^ 7 - 12 * r_0m * x ^ 2 - 12 * r_m * x ^ 4 - 4 * r_m ^ 2 * x ^ 6 -
      2 * r_0m * x ^ 4 - 2 * r_m * x ^ 3 + 2 * r_0m * x ^ 6 + 2 * r_m * x ^ 6 + 4 * r_0m * x ^ 3 +
      4 * r_0mm * x ^ 4 + 4 * r_0m ^ 2 * x ^ 5 + 4 * r_m ^ 2 * x ^ 4 + 8 * r_00mm * x ^ 2 +
      8 * r_0mm * x + 8 * r_0mm * x ^ 3 + 8 * r_m * x ^ 2 + 24 * r_00m * x ^ 2 -
      12 * r_0m * r_m * x ^ 5 - 8 * r_0m * r_m * x ^ 4 - 8 * r_0m * r_m * x ^ 6 -
      4 * r_0m * r_m * x ^ 7

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽92⁾`. -/
noncomputable def i8L4Q92_2 (x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -4 + x ^ 3 / 2 + x ^ 5 / 2 - x ^ 2 - x ^ 4 - 8 * r_0m * x ^ 2 - 8 * r_0mm * x ^ 2 -
      2 * r_m * x ^ 6 + 2 * r_m ^ 2 * x ^ 7 + 4 * r_m * x ^ 3 + 4 * r_m ^ 2 * x ^ 4 +
      4 * r_m ^ 2 * x ^ 6 + 6 * r_m * x ^ 2 + 6 * r_m ^ 2 * x ^ 5

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽92⁾`. -/
noncomputable def i8L4Q92_3 (_x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ
    :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽92⁾`. -/
noncomputable def i8L4Q92_4 (_x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ
    :=
    0

theorem i8L4_92_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s92 x = i8L4S92 x + x * (i8L4Q92_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q92_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q92_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q92_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q92_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s92 i8Psi4s92N0 i8Psi4s92N1 i8Psi4s92N2 i8Psi4s92N3 i8Psi4s92N4 i8Psi4s92W
  simp only [hpl_zero, i13hw_00, i13hw_00m0 hx, i13hw_00mm0 hx, i13hw_0m0 hx, i13hw_0m00 hx,
    i13hw_0m0m0 hx, i13hw_0mm0 hx, i13hw_0mm00 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_m0m0 hx,
    i13hw_mm0 hx, i13hw_mm00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_000mm h0, i13hpl_rho_00m h0, i13hpl_rho_00m0m h0,
    i13hpl_rho_00mm h0, i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S92 i8L4Q92_0 i8L4Q92_1 i8L4Q92_2 i8L4Q92_3 i8L4Q92_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽92⁾`. -/
noncomputable def i8L4R92 (x : ℝ) : ℝ :=
  x * (i8L4Q92_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero,
    zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
    [negOne] x) + Real.log x * i8L4Q92_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
    zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q92_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q92_3 x (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q92_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x))

theorem tendsto_i8L4R92 : Tendsto i8L4R92 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q92_0 (v 0) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v
      66)) (by
      unfold i8L4Q92_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q92_1 (v 0) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v
      66)) (by
      unfold i8L4Q92_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q92_2 (v 0) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v
      66)) (by
      unfold i8L4Q92_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q92_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q92_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q92_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R92
  unfold i8L4Q92_3 i8L4Q92_4
  ring

/-- The singular part of `Ψ₄⁽93⁾` at `ξ = 0`. -/
noncomputable def i8L4S93 (x : ℝ) : ℝ :=
    (8 + 4 * Real.log x ^ 2 + 8 * Real.log x + Real.log x ^ 4 / 3 + 4 / 3 * Real.log x ^ 3 -
      x * Real.log x ^ 5 / 15) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽93⁾`. -/
noncomputable def i8L4Q93_0 (x : ℝ) : ℝ :=
    8 + x / 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽93⁾`. -/
noncomputable def i8L4Q93_1 (x : ℝ) : ℝ :=
    -8 - x / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽93⁾`. -/
noncomputable def i8L4Q93_2 (x : ℝ) : ℝ :=
    4 + x / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽93⁾`. -/
noncomputable def i8L4Q93_3 (x : ℝ) : ℝ :=
    -4 / 3 - x / 3

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽93⁾`. -/
noncomputable def i8L4Q93_4 (x : ℝ) : ℝ :=
    1 / 3 + x / 6

theorem i8L4_93_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s93 x = i8L4S93 x + x * (i8L4Q93_0 x + Real.log x * i8L4Q93_1 x +
      Real.log x ^ 2 * i8L4Q93_2 x + Real.log x ^ 3 * i8L4Q93_3 x +
      Real.log x ^ 4 * i8L4Q93_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s93 i8Psi4s93N0 i8Psi4s93N1 i8Psi4s93N2 i8Psi4s93N3 i8Psi4s93N4 i8Psi4s93W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00000]

  unfold i8L4S93 i8L4Q93_0 i8L4Q93_1 i8L4Q93_2 i8L4Q93_3 i8L4Q93_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽93⁾`. -/
noncomputable def i8L4R93 (x : ℝ) : ℝ :=
  x * (i8L4Q93_0 x + Real.log x * i8L4Q93_1 x + Real.log x ^ 2 * i8L4Q93_2 x +
    Real.log x ^ 3 * i8L4Q93_3 x + Real.log x ^ 4 * i8L4Q93_4 x)

theorem tendsto_i8L4R93 : Tendsto i8L4R93 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q93_0 (v 0)) (by
      unfold i8L4Q93_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q93_1 (v 0)) (by
      unfold i8L4Q93_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q93_2 (v 0)) (by
      unfold i8L4Q93_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q93_3 (v 0)) (by
      unfold i8L4Q93_3
      fun_prop)
  obtain ⟨M4, hM4⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q93_4 (v 0)) (by
      unfold i8L4Q93_4
      fun_prop)
  have H := (((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q93_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q93_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q93_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q93_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 4) (f := fun x => i8L4Q93_4 x)
      ⟨M4, fun x hx => hM4 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R93
  ring

/-- The singular part of `Ψ₄⁽94⁾` at `ξ = 0`. -/
noncomputable def i8L4S94 (x : ℝ) : ℝ :=
    -4 + Real.log x ^ 4 / 2 + 2 * Real.log x ^ 2 - 4 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽94⁾`. -/
noncomputable def i8L4Q94_0 (x r_0000m r_000m r_00m _r_0m _r_m : ℝ) : ℝ :=
    -31 / 2 + x ^ 2 / 2 - x ^ 3 / 8 + 13 / 4 * x + r_00m * x ^ 4 - r_00m * x ^ 2 -
      24 * r_0000m * x ^ 2 - 4 * r_00m * x + 4 * r_00m * x ^ 3 + 18 * r_000m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽94⁾`. -/
noncomputable def i8L4Q94_1 (x _r_0000m r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    31 / 2 + x ^ 3 / 2 - 13 / 2 * x - 3 / 2 * x ^ 2 + r_0m * x ^ 2 - r_0m * x ^ 4 -
      18 * r_00m * x ^ 2 - 4 * r_00m * x - 4 * r_00m * x ^ 3 - 4 * r_0m * x ^ 3 -
      2 * r_00m * x ^ 4 + 4 * r_0m * x + 24 * r_000m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽94⁾`. -/
noncomputable def i8L4Q94_2 (x _r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -6 + x ^ 2 / 2 - 3 / 4 * x ^ 3 + 17 / 4 * x + r_m * x ^ 4 / 2 - 10 * r_00m * x ^ 2 -
      2 * r_m * x + 2 * r_0m * x ^ 4 + 2 * r_m * x ^ 3 + 4 * r_0m * x + 4 * r_0m * x ^ 3 +
      9 * r_0m * x ^ 2 - r_m * x ^ 2 / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽94⁾`. -/
noncomputable def i8L4Q94_3 (x _r_0000m _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    1 + x ^ 3 / 2 - x / 2 - r_m * x ^ 4 - 3 * r_m * x ^ 2 - 2 * r_m * x - 2 * r_m * x ^ 3 +
      2 * r_0m * x ^ 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽94⁾`. -/
noncomputable def i8L4Q94_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_94_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s94 x = i8L4S94 x + x * (i8L4Q94_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [negOne] x) + Real.log x * i8L4Q94_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q94_2 x (i13Rho [zero, zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q94_3 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q94_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s94 i8Psi4s94N0 i8Psi4s94N1 i8Psi4s94N2 i8Psi4s94N3 i8Psi4s94N4 i8Psi4s94W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00m00 hx, i13hw_0m00 hx, i13hw_0m000
    hx, i13hw_m00 hx, i13hw_m000 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S94 i8L4Q94_0 i8L4Q94_1 i8L4Q94_2 i8L4Q94_3 i8L4Q94_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽94⁾`. -/
noncomputable def i8L4R94 (x : ℝ) : ℝ :=
  x * (i8L4Q94_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q94_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q94_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q94_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q94_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R94 : Tendsto i8L4R94 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q94_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q94_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q94_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q94_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q94_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q94_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q94_3 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q94_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q94_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q94_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q94_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q94_3 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R94
  unfold i8L4Q94_4
  ring

/-- The singular part of `Ψ₄⁽95⁾` at `ξ = 0`. -/
noncomputable def i8L4S95 (x : ℝ) : ℝ :=
    8 - 4 * Real.log x ^ 2 + 8 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽95⁾`. -/
noncomputable def i8L4Q95_0 (x r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    14 + x ^ 3 / 2 - 11 / 2 * x - 24 * r_00m * x ^ 2 - 8 * r_0m * x ^ 3 - 2 * r_0m * x ^ 4 +
      2 * r_0m * x ^ 2 + 8 * r_0m * x + 24 * r_000m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽95⁾`. -/
noncomputable def i8L4Q95_1 (x _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -14 - 2 * x ^ 3 + 11 * x - 24 * r_00m * x ^ 2 - 8 * r_m * x - 2 * r_m * x ^ 2 +
      2 * r_m * x ^ 4 + 4 * r_0m * x ^ 4 + 8 * r_0m * x + 8 * r_0m * x ^ 3 + 8 * r_m * x ^ 3 +
      24 * r_0m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽95⁾`. -/
noncomputable def i8L4Q95_2 (x _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    4 - 2 * x + 2 * x ^ 3 - 12 * r_m * x ^ 2 - 8 * r_m * x - 8 * r_m * x ^ 3 - 4 * r_m * x ^ 4 +
      8 * r_0m * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽95⁾`. -/
noncomputable def i8L4Q95_3 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽95⁾`. -/
noncomputable def i8L4Q95_4 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_95_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s95 x = i8L4S95 x + x * (i8L4Q95_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q95_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q95_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q95_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q95_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s95 i8Psi4s95N0 i8Psi4s95N1 i8Psi4s95N2 i8Psi4s95N3 i8Psi4s95N4 i8Psi4s95W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_m0 hx,
    i13hw_m00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S95 i8L4Q95_0 i8L4Q95_1 i8L4Q95_2 i8L4Q95_3 i8L4Q95_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽95⁾`. -/
noncomputable def i8L4R95 (x : ℝ) : ℝ :=
  x * (i8L4Q95_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q95_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q95_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q95_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q95_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R95 : Tendsto i8L4R95 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q95_0 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q95_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q95_1 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q95_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q95_2 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q95_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q95_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q95_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q95_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R95
  unfold i8L4Q95_3 i8L4Q95_4
  ring

/-- The singular part of `Ψ₄⁽96⁾` at `ξ = 0`. -/
noncomputable def i8L4S96 (x : ℝ) : ℝ :=
    (12 + 2 * Real.log x ^ 3 + 6 * Real.log x ^ 2 + 12 * Real.log x -
      x * Real.log x ^ 4 / 2) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽96⁾`. -/
noncomputable def i8L4Q96_0 (x : ℝ) : ℝ :=
    -12 - 3 / 4 * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽96⁾`. -/
noncomputable def i8L4Q96_1 (x : ℝ) : ℝ :=
    12 + 3 / 2 * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽96⁾`. -/
noncomputable def i8L4Q96_2 (x : ℝ) : ℝ :=
    -6 - 3 / 2 * x

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽96⁾`. -/
noncomputable def i8L4Q96_3 (x : ℝ) : ℝ :=
    2 + x

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽96⁾`. -/
noncomputable def i8L4Q96_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_96_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s96 x = i8L4S96 x + x * (i8L4Q96_0 x + Real.log x * i8L4Q96_1 x +
      Real.log x ^ 2 * i8L4Q96_2 x + Real.log x ^ 3 * i8L4Q96_3 x +
      Real.log x ^ 4 * i8L4Q96_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s96 i8Psi4s96N0 i8Psi4s96N1 i8Psi4s96N2 i8Psi4s96N3 i8Psi4s96N4 i8Psi4s96W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000]

  unfold i8L4S96 i8L4Q96_0 i8L4Q96_1 i8L4Q96_2 i8L4Q96_3 i8L4Q96_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽96⁾`. -/
noncomputable def i8L4R96 (x : ℝ) : ℝ :=
  x * (i8L4Q96_0 x + Real.log x * i8L4Q96_1 x + Real.log x ^ 2 * i8L4Q96_2 x +
    Real.log x ^ 3 * i8L4Q96_3 x + Real.log x ^ 4 * i8L4Q96_4 x)

theorem tendsto_i8L4R96 : Tendsto i8L4R96 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q96_0 (v 0)) (by
      unfold i8L4Q96_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q96_1 (v 0)) (by
      unfold i8L4Q96_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q96_2 (v 0)) (by
      unfold i8L4Q96_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q96_3 (v 0)) (by
      unfold i8L4Q96_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q96_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q96_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q96_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q96_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R96
  unfold i8L4Q96_4
  ring

/-- The singular part of `Ψ₄⁽97⁾` at `ξ = 0`. -/
noncomputable def i8L4S97 (x : ℝ) : ℝ :=
    32 - 32 * Real.log x - 8 * zeta3 - 4 / 3 * π ^ 2 + 8 * Real.log x * zeta3 +
      4 / 3 * Real.log x * π ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽97⁾`. -/
noncomputable def i8L4Q97_0 (x r_01 r_1 : ℝ) : ℝ :=
    16 - 8 * x ^ 3 + 2 * π ^ 2 + 8 * x + 12 * zeta3 - 48 * r_1 * x ^ 2 - 16 * r_1 * x ^ 4 -
      8 * zeta3 * x ^ 2 - 2 * zeta3 * x ^ 3 + 2 * x * zeta3 + 32 * r_01 * x ^ 2 + 32 * r_1 * x +
      32 * r_1 * x ^ 3 - 4 / 3 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 3 / 3 + π ^ 2 * x / 3 -
      8 * r_1 * x * zeta3 - 8 * r_1 * zeta3 * x ^ 3 - 4 * r_1 * zeta3 * x ^ 4 +
      8 * r_01 * zeta3 * x ^ 2 + 20 * r_1 * zeta3 * x ^ 2 - 4 / 3 * π ^ 2 * r_1 * x -
      4 / 3 * π ^ 2 * r_1 * x ^ 3 - 2 / 3 * π ^ 2 * r_1 * x ^ 4 + 4 / 3 * π ^ 2 * r_01 * x ^ 2 +
      10 / 3 * π ^ 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽97⁾`. -/
noncomputable def i8L4Q97_1 (_x _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽97⁾`. -/
noncomputable def i8L4Q97_2 (_x _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽97⁾`. -/
noncomputable def i8L4Q97_3 (_x _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽97⁾`. -/
noncomputable def i8L4Q97_4 (_x _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_97_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s97 x = i8L4S97 x + x * (i8L4Q97_0 x (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q97_1 x (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q97_2 x (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q97_3 x (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q97_4 x (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s97 i8Psi4s97N0 i8Psi4s97N1 i8Psi4s97N2 i8Psi4s97N3 i8Psi4s97N4 i8Psi4s97W
  simp only [hpl_zero]
  simp only [i13hpl_rho_01 h0, i13hpl_rho_1 h0]
  unfold i8L4S97 i8L4Q97_0 i8L4Q97_1 i8L4Q97_2 i8L4Q97_3 i8L4Q97_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽97⁾`. -/
noncomputable def i8L4R97 (x : ℝ) : ℝ :=
  x * (i8L4Q97_0 x (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q97_1 x (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q97_2 x (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q97_3 x (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q97_4 x (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R97 : Tendsto i8L4R97 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q97_0 (v 0) (v 27) (v 65)) (by
      unfold i8L4Q97_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q97_0 x (i13Rho [zero, one] x)
    (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R97
  unfold i8L4Q97_1 i8L4Q97_2 i8L4Q97_3 i8L4Q97_4
  ring

/-- The singular part of `Ψ₄⁽98⁾` at `ξ = 0`. -/
noncomputable def i8L4S98 (x : ℝ) : ℝ :=
    16 - 8 * Real.log x ^ 2 - 2 / 3 * π ^ 2 + π ^ 2 * Real.log x ^ 2 / 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽98⁾`. -/
noncomputable def i8L4Q98_0 (x r_001 r_01 r_1 : ℝ) : ℝ :=
    24 - π ^ 2 - 12 * x ^ 2 - 6 * x - 2 * x ^ 3 + π ^ 2 * x ^ 2 / 2 - 16 * r_1 * x ^ 3 -
      4 * r_1 * x ^ 4 + 4 * r_1 * x ^ 2 + 16 * r_001 * x ^ 2 + 16 * r_1 * x + 40 * r_01 * x ^ 2 +
      π ^ 2 * x / 4 + π ^ 2 * x ^ 3 / 12 - 5 / 3 * π ^ 2 * r_01 * x ^ 2 -
      2 / 3 * π ^ 2 * r_001 * x ^ 2 - 2 / 3 * π ^ 2 * r_1 * x - π ^ 2 * r_1 * x ^ 2 / 6 +
      π ^ 2 * r_1 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * r_1 * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽98⁾`. -/
noncomputable def i8L4Q98_1 (x _r_001 r_01 r_1 : ℝ) : ℝ :=
    -24 + π ^ 2 - 4 * x + 4 * x ^ 3 + 16 * x ^ 2 - 40 * r_1 * x ^ 2 - 16 * r_01 * x ^ 2 +
      8 * r_1 * x ^ 4 + 16 * r_1 * x + 16 * r_1 * x ^ 3 - 2 / 3 * π ^ 2 * x ^ 2 -
      π ^ 2 * x ^ 3 / 6 + π ^ 2 * x / 6 - 2 / 3 * π ^ 2 * r_1 * x - 2 / 3 * π ^ 2 * r_1 * x ^ 3 -
      π ^ 2 * r_1 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * r_01 * x ^ 2 + 5 / 3 * π ^ 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽98⁾`. -/
noncomputable def i8L4Q98_2 (_x _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽98⁾`. -/
noncomputable def i8L4Q98_3 (_x _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽98⁾`. -/
noncomputable def i8L4Q98_4 (_x _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_98_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s98 x = i8L4S98 x + x * (i8L4Q98_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x)
      (i13Rho [one] x) + Real.log x * i8L4Q98_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one]
      x) (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q98_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q98_3 x (i13Rho [zero, zero, one] x) (i13Rho
      [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q98_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s98 i8Psi4s98N0 i8Psi4s98N1 i8Psi4s98N2 i8Psi4s98N3 i8Psi4s98N4 i8Psi4s98W
  simp only [hpl_zero, i13hw_00, i13hw_010 hx, i13hw_10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_01 h0, i13hpl_rho_1 h0]
  unfold i8L4S98 i8L4Q98_0 i8L4Q98_1 i8L4Q98_2 i8L4Q98_3 i8L4Q98_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽98⁾`. -/
noncomputable def i8L4R98 (x : ℝ) : ℝ :=
  x * (i8L4Q98_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q98_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q98_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one]
    x) + Real.log x ^ 3 * i8L4Q98_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
    [one] x) + Real.log x ^ 4 * i8L4Q98_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x)
    (i13Rho [one] x))

theorem tendsto_i8L4R98 : Tendsto i8L4R98 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q98_0 (v 0) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q98_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q98_1 (v 0) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q98_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q98_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q98_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R98
  unfold i8L4Q98_2 i8L4Q98_3 i8L4Q98_4
  ring

/-- The singular part of `Ψ₄⁽99⁾` at `ξ = 0`. -/
noncomputable def i8L4S99 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽99⁾`. -/
noncomputable def i8L4Q99_0 (x r_01 r_01m r_0m r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    -4 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x - π ^ 2 * x ^ 2 / 3 - π ^ 2 * x ^ 4 / 3 -
      π ^ 2 * x ^ 5 / 6 + 7 / 6 * π ^ 2 * x ^ 3 + 3 * π ^ 2 * r_m * x ^ 2 -
      14 / 3 * π ^ 2 * r_1 * x ^ 3 - 4 / 3 * π ^ 2 * r_01 * x ^ 2 -
      4 / 3 * π ^ 2 * r_01m * x ^ 2 - 4 / 3 * π ^ 2 * r_0m * x ^ 2 -
      4 / 3 * π ^ 2 * r_0m1 * x ^ 2 - 2 / 3 * π ^ 2 * r_m * x ^ 3 - π ^ 2 * r_1 * x ^ 6 / 3 +
      π ^ 2 * r_m * x ^ 6 / 3 + 4 / 3 * π ^ 2 * r_m * x ^ 5 + 7 / 3 * π ^ 2 * r_1 * x ^ 2 +
      8 / 3 * π ^ 2 * r_1 * x ^ 4 + 16 / 3 * π ^ 2 * r_m1 * x ^ 2 -
      10 / 3 * π ^ 2 * r_1 * r_m * x ^ 5 + 2 / 3 * π ^ 2 * r_1 * r_m * x ^ 7 +
      4 / 3 * π ^ 2 * r_1 * r_m * x ^ 4 + 4 / 3 * π ^ 2 * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽99⁾`. -/
noncomputable def i8L4Q99_1 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽99⁾`. -/
noncomputable def i8L4Q99_2 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽99⁾`. -/
noncomputable def i8L4Q99_3 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽99⁾`. -/
noncomputable def i8L4Q99_4 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_99_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s99 x = i8L4S99 x + x * (i8L4Q99_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x * i8L4Q99_1 x (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q99_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 3 * i8L4Q99_3 x (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q99_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s99 i8Psi4s99N0 i8Psi4s99N1 i8Psi4s99N2 i8Psi4s99N3 i8Psi4s99N4 i8Psi4s99W
  simp only [i13hw_1m hx]
  simp only [i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1
    h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S99 i8L4Q99_0 i8L4Q99_1 i8L4Q99_2 i8L4Q99_3 i8L4Q99_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽99⁾`. -/
noncomputable def i8L4R99 (x : ℝ) : ℝ :=
  x * (i8L4Q99_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q99_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x) + Real.log x ^ 2 * i8L4Q99_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 3 * i8L4Q99_3 x (i13Rho [zero, one] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q99_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x))

theorem tendsto_i8L4R99 : Tendsto i8L4R99 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q99_0 (v 0) (v 27) (v 36) (v 43) (v 49) (v 65) (v 66) (v 67))
      (by
      unfold i8L4Q99_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q99_0 x (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R99
  unfold i8L4Q99_1 i8L4Q99_2 i8L4Q99_3 i8L4Q99_4
  ring

/-- The singular part of `Ψ₄⁽100⁾` at `ξ = 0`. -/
noncomputable def i8L4S100 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽100⁾`. -/
noncomputable def i8L4Q100_0 (x r_0001m r_000m r_000m1 r_001 r_0010m _r_001m r_00m r_00m01 _r_00m1
    r_01 _r_01m r_0m r_0m01 _r_0m1 r_1 _r_m : ℝ) : ℝ :=
    -24 - 27 / 2 * x - 5 / 2 * x ^ 2 - x ^ 5 / 4 + 5 / 2 * x ^ 4 + 47 / 4 * x ^ 3 -
      r_0m * x ^ 6 - 36 * r_1 * x ^ 3 - 24 * r_000m * x ^ 2 - 24 * r_00m * x ^ 3 -
      20 * r_0m01 * x ^ 2 - 12 * r_0m * x ^ 2 - 8 * r_001 * x ^ 2 - 7 * r_01 * x ^ 2 -
      6 * r_0m * x ^ 5 - 4 * r_00m * x ^ 4 - 4 * r_0m * x ^ 4 - 3 * r_01 * x ^ 4 +
      4 * r_00m * x ^ 6 + 4 * r_01 * x ^ 3 + 4 * r_0m * x ^ 3 + 6 * r_1 * x ^ 5 +
      8 * r_0010m * x ^ 2 + 13 * r_1 * x ^ 4 + 16 * r_00m * x ^ 5 + 16 * r_00m01 * x ^ 2 +
      24 * r_0001m * x ^ 2 + 24 * r_000m1 * x ^ 2 - r_1 * x ^ 6 / 2 + 35 / 2 * r_1 * x ^ 2 -
      40 * r_00m * r_1 * x ^ 5 - 16 * r_00m * r_01 * x ^ 5 - 8 * r_0m * r_1 * x ^ 6 -
      2 * r_0m * r_1 * x ^ 7 + 2 * r_0m * r_1 * x ^ 5 + 8 * r_00m * r_1 * x ^ 7 +
      8 * r_0m * r_1 * x ^ 4 + 16 * r_00m * r_1 * x ^ 4 + 16 * r_00m * r_1 * x ^ 6 +
      20 * r_01 * r_0m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽100⁾`. -/
noncomputable def i8L4Q100_1 (x _r_0001m _r_000m _r_000m1 _r_001 _r_0010m r_001m r_00m _r_00m01
    r_00m1 r_01 r_01m r_0m r_0m01 r_0m1 r_1 r_m : ℝ) : ℝ :=
    8 - 4 * x ^ 2 - 2 * x ^ 4 + 5 * x - 15 / 2 * x ^ 3 + r_m * x ^ 6 - 20 * r_01m * x ^ 2 -
      20 * r_0m1 * x ^ 2 - 9 * r_1 * x ^ 2 - 8 * r_001m * x ^ 2 - 8 * r_00m1 * x ^ 2 -
      8 * r_0m * x ^ 5 - 8 * r_0m01 * x ^ 2 - 5 * r_1 * x ^ 4 - 4 * r_1 * x ^ 5 -
      2 * r_01 * x ^ 4 - 2 * r_0m * x ^ 6 + 2 * r_0m * x ^ 4 + 6 * r_m * x ^ 5 +
      8 * r_00m * x ^ 2 + 8 * r_01 * x ^ 2 + 8 * r_01 * x ^ 3 + 9 * r_m * x ^ 4 +
      12 * r_0m * x ^ 3 + 12 * r_m * x ^ 2 + 16 * r_m * x ^ 3 + 18 * r_1 * x ^ 3 -
      8 * r_0m * r_1 * x ^ 4 - 8 * r_0m * r_1 * x ^ 6 - 8 * r_1 * r_m * x ^ 4 -
      4 * r_0m * r_1 * x ^ 7 - 2 * r_1 * r_m * x ^ 5 + 2 * r_1 * r_m * x ^ 7 +
      8 * r_01 * r_0m * x ^ 5 + 8 * r_1 * r_m * x ^ 6 + 20 * r_0m * r_1 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽100⁾`. -/
noncomputable def i8L4Q100_2 (_x _r_0001m _r_000m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m01
    _r_00m1 _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽100⁾`. -/
noncomputable def i8L4Q100_3 (_x _r_0001m _r_000m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m01
    _r_00m1 _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽100⁾`. -/
noncomputable def i8L4Q100_4 (_x _r_0001m _r_000m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m01
    _r_00m1 _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m : ℝ) : ℝ :=
    0

theorem i8L4_100_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s100 x = i8L4S100 x + x * (i8L4Q100_0 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero,
      one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) + Real.log x * i8L4Q100_1 x (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho
      [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
      [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q100_2 x (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q100_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x) + Real.log x ^ 4 * i8L4Q100_4 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s100 i8Psi4s100N0 i8Psi4s100N1 i8Psi4s100N2 i8Psi4s100N3 i8Psi4s100N4 i8Psi4s100W
  simp only [hpl_zero, i13hw_001m0 hx, i13hw_00m0 hx, i13hw_00m10 hx, i13hw_010 hx, i13hw_010m0 hx,
    i13hw_01m0 hx, i13hw_0m0 hx, i13hw_0m10 hx, i13hw_10 hx, i13hw_10m0 hx, i13hw_1m0 hx, i13hw_m0
    hx, i13hw_m01 hx, i13hw_m10 hx]
  simp only [i13hpl_rho_0001m h0, i13hpl_rho_000m h0, i13hpl_rho_000m1 h0, i13hpl_rho_001 h0,
    i13hpl_rho_0010m h0, i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m01 h0, i13hpl_rho_00m1
    h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1
    h0, i13hpl_rho_1 h0, i13hpl_rho_m h0]
  unfold i8L4S100 i8L4Q100_0 i8L4Q100_1 i8L4Q100_2 i8L4Q100_3 i8L4Q100_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽100⁾`. -/
noncomputable def i8L4R100 (x : ℝ) : ℝ :=
  x * (i8L4Q100_0 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q100_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q100_2 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q100_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q100_4 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R100 : Tendsto i8L4R100 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q100_0 (v 0) (v 5) (v 6) (v 7) (v 9) (v 11) (v 15) (v 18) (v 19)
      (v 21) (v 27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66)) (by
      unfold i8L4Q100_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q100_1 (v 0) (v 5) (v 6) (v 7) (v 9) (v 11) (v 15) (v 18) (v 19)
      (v 21) (v 27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66)) (by
      unfold i8L4Q100_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q100_0 x (i13Rho [zero, zero,
    zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero,
    zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q100_1 x (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R100
  unfold i8L4Q100_2 i8L4Q100_3 i8L4Q100_4
  ring

/-- The regular parts of group 8. -/
noncomputable def i8L4RG8 (x : ℝ) : ℝ :=
  i8L4R89 x + i8L4R90 x + i8L4R91 x + i8L4R92 x + i8L4R93 x + i8L4R94 x + i8L4R95 x +
    i8L4R96 x + i8L4R97 x + i8L4R98 x + i8L4R99 x + i8L4R100 x

theorem tendsto_i8L4RG8 : Tendsto i8L4RG8 (𝓝[>] 0) (𝓝 0) := by
  have H := (((((((((((tendsto_i8L4R89.add tendsto_i8L4R90).add tendsto_i8L4R91).add
    tendsto_i8L4R92).add tendsto_i8L4R93).add tendsto_i8L4R94).add tendsto_i8L4R95).add
    tendsto_i8L4R96).add tendsto_i8L4R97).add tendsto_i8L4R98).add tendsto_i8L4R99).add
    tendsto_i8L4R100)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
