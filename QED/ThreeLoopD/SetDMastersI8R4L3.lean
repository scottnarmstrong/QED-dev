/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L2
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 3

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_42_eq`, `QED.ThreeLoopD.tendsto_i8L4RG3` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽42⁾` at `ξ = 0`. -/
noncomputable def i8L4S42 (x : ℝ) : ℝ :=
    (32 + 8 * Real.log x ^ 2 + 32 * Real.log x - 4 / 3 * π ^ 2 - 8 * x * Real.log x ^ 2 -
      8 * x * Real.log x ^ 3 - 4 / 3 * Real.log x * π ^ 2 - π ^ 2 * Real.log x ^ 2 / 3 +
      π ^ 2 * x * Real.log x ^ 2 / 3 + π ^ 2 * x * Real.log x ^ 3 / 3) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽42⁾`. -/
noncomputable def i8L4Q42_0 (x : ℝ) : ℝ :=
    -64 - 6 * x + 8 / 3 * π ^ 2 + π ^ 2 * x / 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽42⁾`. -/
noncomputable def i8L4Q42_1 (x : ℝ) : ℝ :=
    64 + 12 * x - 8 / 3 * π ^ 2 - π ^ 2 * x / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽42⁾`. -/
noncomputable def i8L4Q42_2 (x : ℝ) : ℝ :=
    -24 + π ^ 2 - 4 * x + π ^ 2 * x / 6

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽42⁾`. -/
noncomputable def i8L4Q42_3 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽42⁾`. -/
noncomputable def i8L4Q42_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_42_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s42 x = i8L4S42 x + x * (i8L4Q42_0 x + Real.log x * i8L4Q42_1 x +
      Real.log x ^ 2 * i8L4Q42_2 x + Real.log x ^ 3 * i8L4Q42_3 x +
      Real.log x ^ 4 * i8L4Q42_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s42 i8Psi4s42N0 i8Psi4s42N1 i8Psi4s42N2 i8Psi4s42N3 i8Psi4s42N4 i8Psi4s42W
  simp only [hpl_zero, i13hw_00, i13hw_000]

  unfold i8L4S42 i8L4Q42_0 i8L4Q42_1 i8L4Q42_2 i8L4Q42_3 i8L4Q42_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽42⁾`. -/
noncomputable def i8L4R42 (x : ℝ) : ℝ :=
  x * (i8L4Q42_0 x + Real.log x * i8L4Q42_1 x + Real.log x ^ 2 * i8L4Q42_2 x +
    Real.log x ^ 3 * i8L4Q42_3 x + Real.log x ^ 4 * i8L4Q42_4 x)

theorem tendsto_i8L4R42 : Tendsto i8L4R42 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q42_0 (v 0)) (by
      unfold i8L4Q42_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q42_1 (v 0)) (by
      unfold i8L4Q42_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q42_2 (v 0)) (by
      unfold i8L4Q42_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q42_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q42_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q42_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R42
  unfold i8L4Q42_3 i8L4Q42_4
  ring

/-- The singular part of `Ψ₄⁽43⁾` at `ξ = 0`. -/
noncomputable def i8L4S43 (x : ℝ) : ℝ :=
    2 * π ^ 2 - 4 / 3 * Real.log x * π ^ 2 - π ^ 2 * Real.log x ^ 2 / 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽43⁾`. -/
noncomputable def i8L4Q43_0 (x r_00m r_0m r_m : ℝ) : ℝ :=
    π ^ 2 - 5 / 6 * π ^ 2 * x ^ 2 - 5 / 12 * π ^ 2 * x ^ 3 + 5 / 12 * π ^ 2 * x +
      2 * π ^ 2 * r_00m * x ^ 2 + 2 * π ^ 2 * r_m * x - π ^ 2 * r_0m * x ^ 2 / 3 +
      5 / 6 * π ^ 2 * r_m * x ^ 4 + 9 / 2 * π ^ 2 * r_m * x ^ 2 + 10 / 3 * π ^ 2 * r_m * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽43⁾`. -/
noncomputable def i8L4Q43_1 (x _r_00m r_0m r_m : ℝ) : ℝ :=
    -5 / 3 * π ^ 2 - 5 / 6 * π ^ 2 * x + π ^ 2 * x ^ 3 / 6 + 2 / 3 * π ^ 2 * x ^ 2 -
      π ^ 2 * r_m * x ^ 2 - 2 * π ^ 2 * r_0m * x ^ 2 - 2 * π ^ 2 * r_m * x ^ 3 -
      π ^ 2 * r_m * x ^ 4 / 3 + 2 / 3 * π ^ 2 * r_m * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽43⁾`. -/
noncomputable def i8L4Q43_2 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽43⁾`. -/
noncomputable def i8L4Q43_3 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽43⁾`. -/
noncomputable def i8L4Q43_4 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_43_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s43 x = i8L4S43 x + x * (i8L4Q43_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q43_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q43_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q43_3 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q43_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s43 i8Psi4s43N0 i8Psi4s43N1 i8Psi4s43N2 i8Psi4s43N3 i8Psi4s43N4 i8Psi4s43W
  simp only [hpl_zero, i13hw_00, i13hw_0m0 hx, i13hw_m0 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S43 i8L4Q43_0 i8L4Q43_1 i8L4Q43_2 i8L4Q43_3 i8L4Q43_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽43⁾`. -/
noncomputable def i8L4R43 (x : ℝ) : ℝ :=
  x * (i8L4Q43_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q43_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q43_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q43_3 x (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q43_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x))

theorem tendsto_i8L4R43 : Tendsto i8L4R43 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q43_0 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q43_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q43_1 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q43_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q43_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q43_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R43
  unfold i8L4Q43_2 i8L4Q43_3 i8L4Q43_4
  ring

/-- The singular part of `Ψ₄⁽44⁾` at `ξ = 0`. -/
noncomputable def i8L4S44 (x : ℝ) : ℝ :=
    40 - 16 * Real.log x + 4 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽44⁾`. -/
noncomputable def i8L4Q44_0 (x r_0000m r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    25 + 10 * x ^ 2 + 16 * x - x ^ 3 / 2 - 32 * r_0m * x ^ 3 - 30 * r_00m * x ^ 2 -
      24 * r_000m * x ^ 2 - 13 * r_0m * x ^ 2 - 3 * r_0m * x ^ 4 + 10 * r_00m * x ^ 4 +
      16 * r_0m * x + 24 * r_00m * x + 40 * r_00m * x ^ 3 + 48 * r_0000m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽44⁾`. -/
noncomputable def i8L4Q44_1 (x _r_0000m r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -39 - 16 * x ^ 2 - 14 * x - 48 * r_000m * x ^ 2 - 24 * r_00m * x ^ 3 - 16 * r_m * x -
      8 * r_0m * x - 8 * r_0m * x ^ 3 - 4 * r_00m * x ^ 4 - 4 * r_0m * x ^ 4 + 3 * r_m * x ^ 4 +
      8 * r_00m * x + 8 * r_00m * x ^ 2 + 13 * r_m * x ^ 2 + 30 * r_0m * x ^ 2 + 32 * r_m * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽44⁾`. -/
noncomputable def i8L4Q44_2 (x _r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    11 + 4 * x ^ 2 + 13 / 2 * x - r_m * x ^ 4 - 15 * r_m * x ^ 2 - 12 * r_m * x ^ 3 -
      4 * r_0m * x - 4 * r_m * x + 2 * r_0m * x ^ 4 + 12 * r_00m * x ^ 2 + 12 * r_0m * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽44⁾`. -/
noncomputable def i8L4Q44_3 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽44⁾`. -/
noncomputable def i8L4Q44_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_44_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s44 x = i8L4S44 x + x * (i8L4Q44_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [negOne] x) + Real.log x * i8L4Q44_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q44_2 x (i13Rho [zero, zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q44_3 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q44_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s44 i8Psi4s44N0 i8Psi4s44N1 i8Psi4s44N2 i8Psi4s44N3 i8Psi4s44N4 i8Psi4s44W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_000m0 hx, i13hw_00m0 hx, i13hw_00m00 hx, i13hw_0m0
    hx, i13hw_0m00 hx, i13hw_m0 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S44 i8L4Q44_0 i8L4Q44_1 i8L4Q44_2 i8L4Q44_3 i8L4Q44_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽44⁾`. -/
noncomputable def i8L4R44 (x : ℝ) : ℝ :=
  x * (i8L4Q44_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q44_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q44_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q44_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q44_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R44 : Tendsto i8L4R44 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q44_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q44_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q44_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q44_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q44_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q44_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q44_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q44_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q44_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R44
  unfold i8L4Q44_3 i8L4Q44_4
  ring

/-- The singular part of `Ψ₄⁽45⁾` at `ξ = 0`. -/
noncomputable def i8L4S45 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽45⁾`. -/
noncomputable def i8L4Q45_0 (x r_000m r_000mm r_00m r_00m0m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    6 - 5 / 4 * x ^ 5 + 5 / 2 * x ^ 4 + 115 / 8 * x ^ 3 - 72 * r_000mm * x ^ 2 -
      48 * r_m * x ^ 3 - 24 * r_000m * x ^ 2 - 24 * r_00m0m * x ^ 2 - 24 * r_m * x ^ 2 -
      8 * r_0m * x ^ 4 + 2 * r_0m ^ 2 * x ^ 5 + 5 * r_0m * x ^ 6 + 10 * r_0m * x ^ 5 +
      10 * r_0mm * x ^ 4 + 12 * r_0m * x ^ 3 + 20 * r_0m * x ^ 2 + 24 * r_0mm * x +
      40 * r_0mm * x ^ 3 + 54 * r_0mm * x ^ 2 + 84 * r_00m * x ^ 2 - 53 / 2 * r_m * x ^ 4 +
      5 / 2 * r_m * x ^ 6 - 54 * r_0m * r_m * x ^ 5 - 40 * r_0m * r_m * x ^ 6 -
      24 * r_0m * r_m * x ^ 4 - 10 * r_0m * r_m * x ^ 7

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽45⁾`. -/
noncomputable def i8L4Q45_1 (x _r_000m _r_000mm r_00m _r_00m0m r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    6 + 12 * x + 20 * x ^ 2 - 35 / 2 * x ^ 3 + 7 / 4 * x ^ 5 - 68 * r_0m * x ^ 2 -
      28 * r_m * x ^ 2 - 24 * r_0mm * x ^ 3 - 16 * r_0mm * x ^ 2 - 12 * r_m * x ^ 5 -
      8 * r_0m * x ^ 5 - 6 * r_m * x ^ 6 - 4 * r_0mm * x ^ 4 - 2 * r_0m * x ^ 6 +
      5 * r_m ^ 2 * x ^ 7 + 6 * r_m * x ^ 3 + 8 * r_0mm * x + 10 * r_0m * x ^ 4 +
      12 * r_0m ^ 2 * x ^ 5 + 12 * r_m ^ 2 * x ^ 4 + 20 * r_0m * x ^ 3 + 20 * r_m ^ 2 * x ^ 6 +
      24 * r_00m * x ^ 2 + 24 * r_00mm * x ^ 2 + 27 * r_m ^ 2 * x ^ 5 + 28 * r_m * x ^ 4 -
      8 * r_0m * r_m * x ^ 4 + 4 * r_0m * r_m * x ^ 7 + 12 * r_0m * r_m * x ^ 5 +
      24 * r_0m * r_m * x ^ 6

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽45⁾`. -/
noncomputable def i8L4Q45_2 (x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -4 - x ^ 4 - 13 * x ^ 2 - 4 * x - x ^ 5 / 2 + 15 / 2 * x ^ 3 - 24 * r_0mm * x ^ 2 -
      16 * r_m * x ^ 4 - 12 * r_m ^ 2 * x ^ 6 - 8 * r_0m * x ^ 2 - 6 * r_m ^ 2 * x ^ 5 -
      2 * r_m ^ 2 * x ^ 7 + 2 * r_m * x ^ 6 + 4 * r_m * x ^ 3 + 4 * r_m ^ 2 * x ^ 4 +
      8 * r_m * x ^ 5 + 26 * r_m * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽45⁾`. -/
noncomputable def i8L4Q45_3 (_x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ
    :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽45⁾`. -/
noncomputable def i8L4Q45_4 (_x _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ
    :=
    0

theorem i8L4_45_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s45 x = i8L4S45 x + x * (i8L4Q45_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q45_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q45_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q45_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q45_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s45 i8Psi4s45N0 i8Psi4s45N1 i8Psi4s45N2 i8Psi4s45N3 i8Psi4s45N4 i8Psi4s45W
  simp only [hpl_zero, i13hw_00, i13hw_00m0 hx, i13hw_00mm0 hx, i13hw_0m0 hx, i13hw_0m00 hx,
    i13hw_0m0m0 hx, i13hw_0mm0 hx, i13hw_0mm00 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_m0m0 hx,
    i13hw_mm0 hx, i13hw_mm00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_000mm h0, i13hpl_rho_00m h0, i13hpl_rho_00m0m h0,
    i13hpl_rho_00mm h0, i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S45 i8L4Q45_0 i8L4Q45_1 i8L4Q45_2 i8L4Q45_3 i8L4Q45_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽45⁾`. -/
noncomputable def i8L4R45 (x : ℝ) : ℝ :=
  x * (i8L4Q45_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero,
    zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
    [negOne] x) + Real.log x * i8L4Q45_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
    zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q45_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q45_3 x (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q45_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x))

theorem tendsto_i8L4R45 : Tendsto i8L4R45 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q45_0 (v 0) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v
      66)) (by
      unfold i8L4Q45_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q45_1 (v 0) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v
      66)) (by
      unfold i8L4Q45_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q45_2 (v 0) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v
      66)) (by
      unfold i8L4Q45_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q45_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q45_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q45_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R45
  unfold i8L4Q45_3 i8L4Q45_4
  ring

/-- The singular part of `Ψ₄⁽46⁾` at `ξ = 0`. -/
noncomputable def i8L4S46 (x : ℝ) : ℝ :=
    (12 + 2 * Real.log x ^ 3 + 6 * Real.log x ^ 2 + 12 * Real.log x + Real.log x ^ 4 / 3 -
      x * Real.log x ^ 5 / 5 - x * Real.log x ^ 4 / 6) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽46⁾`. -/
noncomputable def i8L4Q46_0 (x : ℝ) : ℝ :=
    -28 - x / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽46⁾`. -/
noncomputable def i8L4Q46_1 (x : ℝ) : ℝ :=
    28 + x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽46⁾`. -/
noncomputable def i8L4Q46_2 (x : ℝ) : ℝ :=
    -14 - x

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽46⁾`. -/
noncomputable def i8L4Q46_3 (x : ℝ) : ℝ :=
    14 / 3 + 2 / 3 * x

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽46⁾`. -/
noncomputable def i8L4Q46_4 (x : ℝ) : ℝ :=
    -1 - x / 6

theorem i8L4_46_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s46 x = i8L4S46 x + x * (i8L4Q46_0 x + Real.log x * i8L4Q46_1 x +
      Real.log x ^ 2 * i8L4Q46_2 x + Real.log x ^ 3 * i8L4Q46_3 x +
      Real.log x ^ 4 * i8L4Q46_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s46 i8Psi4s46N0 i8Psi4s46N1 i8Psi4s46N2 i8Psi4s46N3 i8Psi4s46N4 i8Psi4s46W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00000]

  unfold i8L4S46 i8L4Q46_0 i8L4Q46_1 i8L4Q46_2 i8L4Q46_3 i8L4Q46_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽46⁾`. -/
noncomputable def i8L4R46 (x : ℝ) : ℝ :=
  x * (i8L4Q46_0 x + Real.log x * i8L4Q46_1 x + Real.log x ^ 2 * i8L4Q46_2 x +
    Real.log x ^ 3 * i8L4Q46_3 x + Real.log x ^ 4 * i8L4Q46_4 x)

theorem tendsto_i8L4R46 : Tendsto i8L4R46 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q46_0 (v 0)) (by
      unfold i8L4Q46_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q46_1 (v 0)) (by
      unfold i8L4Q46_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q46_2 (v 0)) (by
      unfold i8L4Q46_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q46_3 (v 0)) (by
      unfold i8L4Q46_3
      fun_prop)
  obtain ⟨M4, hM4⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q46_4 (v 0)) (by
      unfold i8L4Q46_4
      fun_prop)
  have H := (((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q46_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q46_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q46_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q46_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 4) (f := fun x => i8L4Q46_4 x)
      ⟨M4, fun x hx => hM4 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R46
  ring

/-- The singular part of `Ψ₄⁽47⁾` at `ξ = 0`. -/
noncomputable def i8L4S47 (x : ℝ) : ℝ :=
    -12 + Real.log x ^ 4 / 2 - 2 * Real.log x ^ 2 + 8 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽47⁾`. -/
noncomputable def i8L4Q47_0 (x r_0000m r_000m r_00m _r_0m _r_m : ℝ) : ℝ :=
    -93 / 2 - 55 / 4 * x - 5 / 2 * x ^ 2 + 5 / 8 * x ^ 3 - 72 * r_0000m * x ^ 2 -
      27 * r_00m * x ^ 2 - 20 * r_00m * x ^ 3 - 12 * r_00m * x - 5 * r_00m * x ^ 4 +
      6 * r_000m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽47⁾`. -/
noncomputable def i8L4Q47_1 (x _r_0000m r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    107 / 2 + x ^ 2 / 2 - 3 / 2 * x ^ 3 + 37 / 2 * x - 4 * r_00m * x + 2 * r_00m * x ^ 2 +
      2 * r_00m * x ^ 4 + 5 * r_0m * x ^ 4 + 12 * r_00m * x ^ 3 + 12 * r_0m * x +
      20 * r_0m * x ^ 3 + 27 * r_0m * x ^ 2 + 72 * r_000m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽47⁾`. -/
noncomputable def i8L4Q47_2 (x _r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -24 - 33 / 4 * x + 7 / 2 * x ^ 2 + 7 / 4 * x ^ 3 - 30 * r_00m * x ^ 2 - 12 * r_0m * x ^ 3 -
      10 * r_m * x ^ 3 - 6 * r_m * x - 5 * r_0m * x ^ 2 - 2 * r_0m * x ^ 4 + 4 * r_0m * x -
      27 / 2 * r_m * x ^ 2 - 5 / 2 * r_m * x ^ 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽47⁾`. -/
noncomputable def i8L4Q47_3 (x _r_0000m _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    5 - 2 * x ^ 2 - x ^ 3 / 2 + 5 / 2 * x + r_m * x ^ 4 - 2 * r_m * x + 3 * r_m * x ^ 2 +
      6 * r_0m * x ^ 2 + 6 * r_m * x ^ 3

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽47⁾`. -/
noncomputable def i8L4Q47_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_47_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s47 x = i8L4S47 x + x * (i8L4Q47_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [negOne] x) + Real.log x * i8L4Q47_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q47_2 x (i13Rho [zero, zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q47_3 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q47_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s47 i8Psi4s47N0 i8Psi4s47N1 i8Psi4s47N2 i8Psi4s47N3 i8Psi4s47N4 i8Psi4s47W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00m00 hx, i13hw_0m00 hx, i13hw_0m000
    hx, i13hw_m00 hx, i13hw_m000 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S47 i8L4Q47_0 i8L4Q47_1 i8L4Q47_2 i8L4Q47_3 i8L4Q47_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽47⁾`. -/
noncomputable def i8L4R47 (x : ℝ) : ℝ :=
  x * (i8L4Q47_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q47_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q47_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q47_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q47_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R47 : Tendsto i8L4R47 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q47_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q47_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q47_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q47_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q47_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q47_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q47_3 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q47_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q47_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q47_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q47_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q47_3 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R47
  unfold i8L4Q47_4
  ring

/-- The singular part of `Ψ₄⁽48⁾` at `ξ = 0`. -/
noncomputable def i8L4S48 (x : ℝ) : ℝ :=
    24 - 16 * Real.log x + 4 * Real.log x ^ 2 + 8 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽48⁾`. -/
noncomputable def i8L4Q48_0 (x r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    42 - 5 / 2 * x ^ 3 + 39 / 2 * x - 8 * r_00m * x ^ 2 + 10 * r_0m * x ^ 4 + 24 * r_0m * x +
      40 * r_0m * x ^ 3 + 54 * r_0m * x ^ 2 + 72 * r_000m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽48⁾`. -/
noncomputable def i8L4Q48_1 (x _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -54 - 19 * x + 6 * x ^ 3 + 12 * x ^ 2 - 72 * r_00m * x ^ 2 - 54 * r_m * x ^ 2 -
      40 * r_m * x ^ 3 - 24 * r_0m * x ^ 3 - 24 * r_m * x - 10 * r_m * x ^ 4 - 8 * r_0m * x ^ 2 -
      4 * r_0m * x ^ 4 + 8 * r_0m * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽48⁾`. -/
noncomputable def i8L4Q48_2 (x _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    20 - 8 * x ^ 2 - 2 * x ^ 3 + 10 * x - 8 * r_m * x + 4 * r_m * x ^ 4 + 12 * r_m * x ^ 2 +
      24 * r_0m * x ^ 2 + 24 * r_m * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽48⁾`. -/
noncomputable def i8L4Q48_3 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽48⁾`. -/
noncomputable def i8L4Q48_4 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_48_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s48 x = i8L4S48 x + x * (i8L4Q48_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q48_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q48_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q48_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q48_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s48 i8Psi4s48N0 i8Psi4s48N1 i8Psi4s48N2 i8Psi4s48N3 i8Psi4s48N4 i8Psi4s48W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_m0 hx,
    i13hw_m00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S48 i8L4Q48_0 i8L4Q48_1 i8L4Q48_2 i8L4Q48_3 i8L4Q48_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽48⁾`. -/
noncomputable def i8L4R48 (x : ℝ) : ℝ :=
  x * (i8L4Q48_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q48_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q48_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q48_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q48_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R48 : Tendsto i8L4R48 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q48_0 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q48_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q48_1 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q48_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q48_2 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q48_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q48_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q48_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q48_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R48
  unfold i8L4Q48_3 i8L4Q48_4
  ring

/-- The singular part of `Ψ₄⁽49⁾` at `ξ = 0`. -/
noncomputable def i8L4S49 (x : ℝ) : ℝ :=
    (20 + 2 * Real.log x ^ 3 + 10 * Real.log x ^ 2 + 20 * Real.log x -
      4 / 3 * x * Real.log x ^ 3 - 3 / 2 * x * Real.log x ^ 4) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽49⁾`. -/
noncomputable def i8L4Q49_0 (x : ℝ) : ℝ :=
    44 + 7 / 4 * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽49⁾`. -/
noncomputable def i8L4Q49_1 (x : ℝ) : ℝ :=
    -44 - 7 / 2 * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽49⁾`. -/
noncomputable def i8L4Q49_2 (x : ℝ) : ℝ :=
    22 + 7 / 2 * x

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽49⁾`. -/
noncomputable def i8L4Q49_3 (x : ℝ) : ℝ :=
    -6 - x

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽49⁾`. -/
noncomputable def i8L4Q49_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_49_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s49 x = i8L4S49 x + x * (i8L4Q49_0 x + Real.log x * i8L4Q49_1 x +
      Real.log x ^ 2 * i8L4Q49_2 x + Real.log x ^ 3 * i8L4Q49_3 x +
      Real.log x ^ 4 * i8L4Q49_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s49 i8Psi4s49N0 i8Psi4s49N1 i8Psi4s49N2 i8Psi4s49N3 i8Psi4s49N4 i8Psi4s49W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000]

  unfold i8L4S49 i8L4Q49_0 i8L4Q49_1 i8L4Q49_2 i8L4Q49_3 i8L4Q49_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽49⁾`. -/
noncomputable def i8L4R49 (x : ℝ) : ℝ :=
  x * (i8L4Q49_0 x + Real.log x * i8L4Q49_1 x + Real.log x ^ 2 * i8L4Q49_2 x +
    Real.log x ^ 3 * i8L4Q49_3 x + Real.log x ^ 4 * i8L4Q49_4 x)

theorem tendsto_i8L4R49 : Tendsto i8L4R49 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q49_0 (v 0)) (by
      unfold i8L4Q49_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q49_1 (v 0)) (by
      unfold i8L4Q49_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q49_2 (v 0)) (by
      unfold i8L4Q49_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q49_3 (v 0)) (by
      unfold i8L4Q49_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q49_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q49_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q49_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q49_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R49
  unfold i8L4Q49_4
  ring

/-- The singular part of `Ψ₄⁽50⁾` at `ξ = 0`. -/
noncomputable def i8L4S50 (x : ℝ) : ℝ :=
    (66 + 3 * Real.log x ^ 3 + 17 * Real.log x ^ 2 + 28 * x + 50 * Real.log x -
      7 / 3 * π ^ 2 + Real.log x ^ 4 / 4 + π ^ 2 ^ 2 / 36 - Real.log x * π ^ 2 -
      x * Real.log x ^ 4 - 4 * x * Real.log x ^ 2 - 10 / 3 * x * Real.log x ^ 3 -
      3 / 20 * x * Real.log x ^ 5 - 2 / 3 * π ^ 2 * x - π ^ 2 * Real.log x ^ 2 / 6 +
      2 * Real.log x * π ^ 2 * x - Real.log x * x * π ^ 2 ^ 2 / 12 +
      π ^ 2 * x * Real.log x ^ 3 / 6 + 2 / 3 * π ^ 2 * x * Real.log x ^ 2) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽50⁾`. -/
noncomputable def i8L4Q50_0 (x r_0000m r_000m r_000mm r_00m r_00m0m _r_00mm r_0m _r_0mm _r_m : ℝ) :
    ℝ :=
    -17 + x ^ 3 - 103 / 16 * x - 41 / 4 * x ^ 2 - x ^ 5 / 8 - π ^ 2 ^ 2 / 12 + x ^ 4 / 4 +
      7 / 6 * π ^ 2 + r_0m * x ^ 6 - 144 * r_000mm * x ^ 2 - 48 * r_0000m * x ^ 2 -
      48 * r_00m0m * x ^ 2 - 12 * r_0m ^ 2 * x ^ 6 - 6 * r_0m ^ 2 * x ^ 5 - 2 * r_00m * x ^ 2 -
      2 * r_0m ^ 2 * x ^ 7 + 2 * r_0m * x ^ 5 + 4 * r_0m ^ 2 * x ^ 4 + 28 * r_0m * x +
      30 * r_000m * x ^ 2 + 34 * r_0m * x ^ 3 - 21 / 2 * r_0m * x ^ 4 - π ^ 2 * x ^ 2 / 6 -
      π ^ 2 * x ^ 3 / 12 - x * π ^ 2 ^ 2 / 72 + 3 / 8 * π ^ 2 * x + 147 / 2 * r_0m * x ^ 2 +
      π ^ 2 * r_0m * x ^ 2 + 2 * π ^ 2 * r_0m * x ^ 3 + 4 * π ^ 2 * r_00m * x ^ 2 -
      2 / 3 * π ^ 2 * r_0m * x + π ^ 2 * r_0m * x ^ 4 / 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽50⁾`. -/
noncomputable def i8L4Q50_1 (x _r_0000m r_000m _r_000mm r_00m _r_00m0m r_00mm r_0m _r_0mm r_m : ℝ) :
    ℝ :=
    17 + x ^ 5 / 2 - 21 / 4 * x ^ 3 - 2 / 3 * π ^ 2 + 49 / 2 * x ^ 2 + 55 / 8 * x - r_m * x ^ 6 -
      34 * r_m * x ^ 3 - 30 * r_00m * x ^ 2 - 28 * r_m * x - 22 * r_0m * x ^ 2 -
      8 * r_0m * x ^ 5 - 2 * r_0m * x ^ 6 - 2 * r_m * x ^ 5 + 7 * r_0m * x ^ 4 +
      8 * r_0m * x ^ 3 + 12 * r_0m * x + 12 * r_0m ^ 2 * x ^ 5 + 48 * r_000m * x ^ 2 +
      48 * r_00mm * x ^ 2 - 147 / 2 * r_m * x ^ 2 - 7 / 12 * π ^ 2 * x + π ^ 2 * x ^ 3 / 6 +
      2 / 3 * π ^ 2 * x ^ 2 + 21 / 2 * r_m * x ^ 4 - π ^ 2 * r_m * x ^ 2 -
      8 * r_0m * r_m * x ^ 4 - 2 * π ^ 2 * r_0m * x ^ 2 - 2 * π ^ 2 * r_m * x ^ 3 +
      4 * r_0m * r_m * x ^ 7 + 12 * r_0m * r_m * x ^ 5 + 24 * r_0m * r_m * x ^ 6 -
      π ^ 2 * r_m * x ^ 4 / 3 + 2 / 3 * π ^ 2 * r_m * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽50⁾`. -/
noncomputable def i8L4Q50_2 (x _r_0000m _r_000m _r_000mm r_00m _r_00m0m _r_00mm r_0m r_0mm r_m : ℝ)
    : ℝ :=
    -7 / 2 + π ^ 2 / 2 - x ^ 4 - 31 / 2 * x ^ 2 - x ^ 5 / 2 + 25 / 4 * x ^ 3 + 25 / 8 * x -
      r_0m * x ^ 4 - 24 * r_00m * x ^ 2 - 24 * r_0mm * x ^ 2 - 13 * r_m * x ^ 4 - 12 * r_m * x -
      12 * r_m ^ 2 * x ^ 6 - 6 * r_0m * x ^ 3 - 6 * r_m ^ 2 * x ^ 5 - 2 * r_m ^ 2 * x ^ 7 +
      2 * r_0m * x + 2 * r_m * x ^ 6 + 4 * r_m ^ 2 * x ^ 4 + 7 * r_0m * x ^ 2 + 8 * r_m * x ^ 5 +
      16 * r_m * x ^ 3 + 23 * r_m * x ^ 2 + π ^ 2 * x / 12

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽50⁾`. -/
noncomputable def i8L4Q50_3 (x _r_0000m _r_000m _r_000mm _r_00m _r_00m0m _r_00mm r_0m _r_0mm r_m :
    ℝ) : ℝ :=
    2 - 2 * x ^ 2 - x ^ 3 / 2 + 7 / 4 * x + r_m * x ^ 4 - 2 * r_m * x + 3 * r_m * x ^ 2 +
      6 * r_0m * x ^ 2 + 6 * r_m * x ^ 3

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽50⁾`. -/
noncomputable def i8L4Q50_4 (x _r_0000m _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m :
    ℝ) : ℝ :=
    -3 / 4 - x / 8

theorem i8L4_50_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s50 x = i8L4S50 x + x * (i8L4Q50_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q50_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q50_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q50_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q50_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s50 i8Psi4s50N0 i8Psi4s50N1 i8Psi4s50N2 i8Psi4s50N3 i8Psi4s50N4 i8Psi4s50W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00000, i13hw_000m0 hx, i13hw_00m0 hx,
    i13hw_00m00 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_0m000 hx, i13hw_0m0m0 hx, i13hw_0mm00 hx,
    i13hw_m0 hx, i13hw_m00 hx, i13hw_m000 hx, i13hw_m0m0 hx, i13hw_mm00 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_000mm h0, i13hpl_rho_00m h0,
    i13hpl_rho_00m0m h0, i13hpl_rho_00mm h0, i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S50 i8L4Q50_0 i8L4Q50_1 i8L4Q50_2 i8L4Q50_3 i8L4Q50_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽50⁾`. -/
noncomputable def i8L4R50 (x : ℝ) : ℝ :=
  x * (i8L4Q50_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q50_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q50_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q50_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q50_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R50 : Tendsto i8L4R50 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q50_0 (v 0) (v 2) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57)
      (v 66)) (by
      unfold i8L4Q50_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q50_1 (v 0) (v 2) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57)
      (v 66)) (by
      unfold i8L4Q50_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q50_2 (v 0) (v 2) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57)
      (v 66)) (by
      unfold i8L4Q50_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q50_3 (v 0) (v 2) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57)
      (v 66)) (by
      unfold i8L4Q50_3
      fun_prop)
  obtain ⟨M4, hM4⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q50_4 (v 0) (v 2) (v 6) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57)
      (v 66)) (by
      unfold i8L4Q50_4
      fun_prop)
  have H := (((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q50_0 x (i13Rho [zero,
    zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q50_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q50_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q50_3 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 4) (f := fun x => i8L4Q50_4 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M4, fun x hx => hM4 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R50
  ring

/-- The singular part of `Ψ₄⁽51⁾` at `ξ = 0`. -/
noncomputable def i8L4S51 (x : ℝ) : ℝ :=
    (4 + 4 * Real.log x + 2 * x * Real.log x ^ 2) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽51⁾`. -/
noncomputable def i8L4Q51_0 (x : ℝ) : ℝ :=
    -4 + x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽51⁾`. -/
noncomputable def i8L4Q51_1 (x : ℝ) : ℝ :=
    4 - 2 * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽51⁾`. -/
noncomputable def i8L4Q51_2 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽51⁾`. -/
noncomputable def i8L4Q51_3 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽51⁾`. -/
noncomputable def i8L4Q51_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_51_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s51 x = i8L4S51 x + x * (i8L4Q51_0 x + Real.log x * i8L4Q51_1 x +
      Real.log x ^ 2 * i8L4Q51_2 x + Real.log x ^ 3 * i8L4Q51_3 x +
      Real.log x ^ 4 * i8L4Q51_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s51 i8Psi4s51N0 i8Psi4s51N1 i8Psi4s51N2 i8Psi4s51N3 i8Psi4s51N4 i8Psi4s51W
  simp only [hpl_zero, i13hw_00]

  unfold i8L4S51 i8L4Q51_0 i8L4Q51_1 i8L4Q51_2 i8L4Q51_3 i8L4Q51_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽51⁾`. -/
noncomputable def i8L4R51 (x : ℝ) : ℝ :=
  x * (i8L4Q51_0 x + Real.log x * i8L4Q51_1 x + Real.log x ^ 2 * i8L4Q51_2 x +
    Real.log x ^ 3 * i8L4Q51_3 x + Real.log x ^ 4 * i8L4Q51_4 x)

theorem tendsto_i8L4R51 : Tendsto i8L4R51 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q51_0 (v 0)) (by
      unfold i8L4Q51_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q51_1 (v 0)) (by
      unfold i8L4Q51_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q51_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q51_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R51
  unfold i8L4Q51_2 i8L4Q51_3 i8L4Q51_4
  ring

/-- The singular part of `Ψ₄⁽52⁾` at `ξ = 0`. -/
noncomputable def i8L4S52 (x : ℝ) : ℝ :=
    (-2 - 2 * Real.log x + x / 4 - x * Real.log x ^ 2 / 2) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽52⁾`. -/
noncomputable def i8L4Q52_0 (x r_00m _r_0m r_m : ℝ) : ℝ :=
    7 / 2 - r_m / 2 - x / 2 - x ^ 2 / 2 + x ^ 3 / 4 + r_m * x ^ 2 + 4 * r_00m * x ^ 2 -
      r_m * x ^ 4 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽52⁾`. -/
noncomputable def i8L4Q52_1 (x _r_00m r_0m r_m : ℝ) : ℝ :=
    -3 + x ^ 2 + x / 2 - r_m - x ^ 3 / 2 + r_m * x ^ 4 - 4 * r_0m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽52⁾`. -/
noncomputable def i8L4Q52_2 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽52⁾`. -/
noncomputable def i8L4Q52_3 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽52⁾`. -/
noncomputable def i8L4Q52_4 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_52_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s52 x = i8L4S52 x + x * (i8L4Q52_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q52_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q52_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q52_3 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q52_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s52 i8Psi4s52N0 i8Psi4s52N1 i8Psi4s52N2 i8Psi4s52N3 i8Psi4s52N4 i8Psi4s52W
  simp only [hpl_zero, i13hw_00, i13hw_0m0 hx, i13hw_m0 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S52 i8L4Q52_0 i8L4Q52_1 i8L4Q52_2 i8L4Q52_3 i8L4Q52_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽52⁾`. -/
noncomputable def i8L4R52 (x : ℝ) : ℝ :=
  x * (i8L4Q52_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q52_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q52_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q52_3 x (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q52_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x))

theorem tendsto_i8L4R52 : Tendsto i8L4R52 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q52_0 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q52_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q52_1 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q52_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q52_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q52_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R52
  unfold i8L4Q52_2 i8L4Q52_3 i8L4Q52_4
  ring

/-- The singular part of `Ψ₄⁽53⁾` at `ξ = 0`. -/
noncomputable def i8L4S53 (x : ℝ) : ℝ :=
    7 / 4 - Real.log x ^ 2 / 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽53⁾`. -/
noncomputable def i8L4Q53_0 (x r_00m r_00mm r_0m _r_0mm r_m : ℝ) : ℝ :=
    -1 - 15 / 16 * x - 3 / 4 * x ^ 2 - x ^ 4 / 4 + x ^ 5 / 16 + 3 / 8 * x ^ 3 + r_0m * x ^ 2 +
      r_m * x ^ 3 / 2 + r_m * x ^ 5 / 2 - r_00m * x ^ 2 - 4 * r_00mm * x ^ 2 + 2 * r_m * x -
      r_m ^ 2 * x ^ 5 / 2 - r_m * x ^ 6 / 4 + r_m ^ 2 * x ^ 3 / 4 + r_m ^ 2 * x ^ 7 / 4 +
      13 / 4 * r_m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽53⁾`. -/
noncomputable def i8L4Q53_1 (x _r_00m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    1 + x ^ 2 + x ^ 4 / 2 - 3 / 4 * x ^ 3 - x / 8 - x ^ 5 / 8 + r_0m * x ^ 2 + r_m * x ^ 4 / 2 +
      r_m * x ^ 6 / 2 + r_m ^ 2 * x ^ 3 / 2 - r_m * x ^ 2 - r_m * x ^ 3 - r_m * x ^ 5 +
      2 * r_m * x + 4 * r_0mm * x ^ 2 - r_m ^ 2 * x ^ 7 / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽53⁾`. -/
noncomputable def i8L4Q53_2 (_x _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽53⁾`. -/
noncomputable def i8L4Q53_3 (_x _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽53⁾`. -/
noncomputable def i8L4Q53_4 (_x _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_53_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s53 x = i8L4S53 x + x * (i8L4Q53_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x * i8L4Q53_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 2 * i8L4Q53_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 3 * i8L4Q53_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 4 * i8L4Q53_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s53 i8Psi4s53N0 i8Psi4s53N1 i8Psi4s53N2 i8Psi4s53N3 i8Psi4s53N4 i8Psi4s53W
  simp only [hpl_zero, i13hw_00, i13hw_0m0 hx, i13hw_0m0m hx, i13hw_0mm0 hx, i13hw_m0 hx, i13hw_m0m
    hx, i13hw_mm hx, i13hw_mm0 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_00mm h0, i13hpl_rho_0m h0, i13hpl_rho_0mm h0,
    i13hpl_rho_m h0]
  unfold i8L4S53 i8L4Q53_0 i8L4Q53_1 i8L4Q53_2 i8L4Q53_3 i8L4Q53_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽53⁾`. -/
noncomputable def i8L4R53 (x : ℝ) : ℝ :=
  x * (i8L4Q53_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q53_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q53_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q53_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q53_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R53 : Tendsto i8L4R53 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q53_0 (v 0) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q53_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q53_1 (v 0) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q53_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q53_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q53_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R53
  unfold i8L4Q53_2 i8L4Q53_3 i8L4Q53_4
  ring

/-- The singular part of `Ψ₄⁽54⁾` at `ξ = 0`. -/
noncomputable def i8L4S54 (x : ℝ) : ℝ :=
    (-1 - Real.log x + 3 / 16 * x - x * Real.log x ^ 2 / 8) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽54⁾`. -/
noncomputable def i8L4Q54_0 (x r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    2 - 3 / 16 * x - r_0m / 4 - r_m / 4 - x ^ 3 / 16 + 2 * r_000m * x ^ 2 - r_0m * x ^ 2 / 2 -
      r_0m * x ^ 4 / 4 + r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽54⁾`. -/
noncomputable def i8L4Q54_1 (x _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -7 / 4 - r_0m / 2 - r_m / 4 + x ^ 2 / 4 + x / 8 + r_0m * x ^ 4 / 2 + r_m * x ^ 2 / 2 -
      2 * r_00m * x ^ 2 - r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽54⁾`. -/
noncomputable def i8L4Q54_2 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽54⁾`. -/
noncomputable def i8L4Q54_3 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽54⁾`. -/
noncomputable def i8L4Q54_4 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_54_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s54 x = i8L4S54 x + x * (i8L4Q54_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q54_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q54_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q54_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q54_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s54 i8Psi4s54N0 i8Psi4s54N1 i8Psi4s54N2 i8Psi4s54N3 i8Psi4s54N4 i8Psi4s54W
  simp only [hpl_zero, i13hw_00, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_m0 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S54 i8L4Q54_0 i8L4Q54_1 i8L4Q54_2 i8L4Q54_3 i8L4Q54_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽54⁾`. -/
noncomputable def i8L4R54 (x : ℝ) : ℝ :=
  x * (i8L4Q54_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q54_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q54_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q54_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q54_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R54 : Tendsto i8L4R54 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q54_0 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q54_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q54_1 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q54_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q54_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q54_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R54
  unfold i8L4Q54_2 i8L4Q54_3 i8L4Q54_4
  ring

/-- The singular part of `Ψ₄⁽55⁾` at `ξ = 0`. -/
noncomputable def i8L4S55 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽55⁾`. -/
noncomputable def i8L4Q55_0 (x r_00m r_00mm r_00mmm r_0m r_0mm _r_0mmm r_m : ℝ) : ℝ :=
    -2 / 3 - 29 / 12 * x ^ 2 - 19 / 24 * x ^ 4 - x ^ 6 / 8 + x ^ 5 / 3 + x / 4 + x ^ 7 / 48 +
      49 / 48 * x ^ 3 + r_m * x ^ 7 / 2 - 2 * r_00m * x ^ 2 - 2 * r_0mm * x ^ 2 -
      2 * r_m ^ 2 * x ^ 4 + 2 * r_00mm * x ^ 2 + 2 * r_m * x ^ 3 + 8 * r_00mmm * x ^ 2 -
      13 / 4 * r_m ^ 2 * x ^ 5 - 3 / 4 * r_m * x ^ 6 - r_m ^ 2 * x ^ 6 / 2 -
      r_m ^ 2 * x ^ 8 / 2 - r_m ^ 3 * x ^ 6 / 6 - r_m ^ 3 * x ^ 10 / 6 - r_m * x ^ 8 / 8 +
      r_m ^ 3 * x ^ 8 / 3 + r_m ^ 2 * x ^ 9 / 4 + 3 / 2 * r_m * x ^ 5 + 5 / 8 * r_m * x ^ 4 +
      13 / 2 * r_0m * x ^ 2 + 17 / 4 * r_m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽55⁾`. -/
noncomputable def i8L4Q55_1 (x _r_00m _r_00mm _r_00mmm r_0m r_0mm r_0mmm r_m : ℝ) : ℝ :=
    2 / 3 + 2 * x ^ 2 - 19 / 12 * x ^ 3 - 5 / 8 * x ^ 5 - x / 2 - x ^ 7 / 24 + x ^ 6 / 4 +
      13 / 12 * x ^ 4 + r_m ^ 2 * x ^ 5 + r_m ^ 2 * x ^ 6 + r_m ^ 2 * x ^ 8 - r_m * x ^ 7 -
      8 * r_0mmm * x ^ 2 - 2 * r_0mm * x ^ 2 - 2 * r_m * x ^ 5 - 2 * r_m ^ 2 * x ^ 4 +
      2 * r_0m * x ^ 2 - 13 / 2 * r_m * x ^ 2 - r_m ^ 2 * x ^ 7 / 2 - r_m ^ 2 * x ^ 9 / 2 -
      r_m ^ 3 * x ^ 6 / 3 + r_m ^ 3 * x ^ 10 / 3 + r_m * x ^ 8 / 4 + 3 / 2 * r_m * x ^ 6 +
      7 / 4 * r_m * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽55⁾`. -/
noncomputable def i8L4Q55_2 (_x _r_00m _r_00mm _r_00mmm _r_0m _r_0mm _r_0mmm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽55⁾`. -/
noncomputable def i8L4Q55_3 (_x _r_00m _r_00mm _r_00mmm _r_0m _r_0mm _r_0mmm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽55⁾`. -/
noncomputable def i8L4Q55_4 (_x _r_00m _r_00mm _r_00mmm _r_0m _r_0mm _r_0mmm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_55_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s55 x = i8L4S55 x + x * (i8L4Q55_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne]
      x) + Real.log x * i8L4Q55_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q55_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q55_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q55_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s55 i8Psi4s55N0 i8Psi4s55N1 i8Psi4s55N2 i8Psi4s55N3 i8Psi4s55N4 i8Psi4s55W
  simp only [hpl_zero, i13hw_0m0 hx, i13hw_0m0m hx, i13hw_0mm0 hx, i13hw_0mmm0 hx, i13hw_m0 hx,
    i13hw_m0m hx, i13hw_m0mm hx, i13hw_mm hx, i13hw_mm0 hx, i13hw_mmm hx, i13hw_mmm0 hx, i8hw_0mm0m
    hx, i8hw_mm0m hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_00mm h0, i13hpl_rho_00mmm h0, i13hpl_rho_0m h0,
    i13hpl_rho_0mm h0, i13hpl_rho_0mmm h0, i13hpl_rho_m h0]
  unfold i8L4S55 i8L4Q55_0 i8L4Q55_1 i8L4Q55_2 i8L4Q55_3 i8L4Q55_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽55⁾`. -/
noncomputable def i8L4R55 (x : ℝ) : ℝ :=
  x * (i8L4Q55_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q55_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q55_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q55_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q55_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R55 : Tendsto i8L4R55 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q55_0 (v 0) (v 18) (v 24) (v 26) (v 43) (v 57) (v 62) (v 66))
      (by
      unfold i8L4Q55_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q55_1 (v 0) (v 18) (v 24) (v 26) (v 43) (v 57) (v 62) (v 66))
      (by
      unfold i8L4Q55_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q55_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne,
    negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q55_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R55
  unfold i8L4Q55_2 i8L4Q55_3 i8L4Q55_4
  ring

/-- The regular parts of group 3. -/
noncomputable def i8L4RG3 (x : ℝ) : ℝ :=
  i8L4R42 x + i8L4R43 x + i8L4R44 x + i8L4R45 x + i8L4R46 x + i8L4R47 x + i8L4R48 x +
    i8L4R49 x + i8L4R50 x + i8L4R51 x + i8L4R52 x + i8L4R53 x + i8L4R54 x + i8L4R55 x

theorem tendsto_i8L4RG3 : Tendsto i8L4RG3 (𝓝[>] 0) (𝓝 0) := by
  have H := (((((((((((((tendsto_i8L4R42.add tendsto_i8L4R43).add tendsto_i8L4R44).add
    tendsto_i8L4R45).add tendsto_i8L4R46).add tendsto_i8L4R47).add tendsto_i8L4R48).add
    tendsto_i8L4R49).add tendsto_i8L4R50).add tendsto_i8L4R51).add tendsto_i8L4R52).add
    tendsto_i8L4R53).add tendsto_i8L4R54).add tendsto_i8L4R55)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
