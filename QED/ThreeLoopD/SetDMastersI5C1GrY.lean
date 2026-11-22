/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1AtY
public import QED.ThreeLoopD.SetDMastersI5C1Der
public import QED.ThreeLoopD.SetDMastersI5C1Kx

/-!
# Set (d), master `I₅`: the limit of the primitive at `x = (1 - ξ)⁻`

As a polynomial in `log (1 - ξ - x)`, the primitive is `P = R_y + log (1 - ξ - x) · C₁`
(`QED.ThreeLoopD.i5C1E_PB_eqy`); `R_y` tends to `QED.ThreeLoopD.i5C1E_Vy` by the atom limits
of `QED.ThreeLoopD.SetDMastersI5C1AtY`, and `C₁` is differentiable at `1 - ξ` and vanishes
there, so `log (1 - ξ - x) · C₁ → 0` (`QED.ThreeLoopD.i5C1E_tendsto_log_mul_y`).

## Main results

* `QED.ThreeLoopD.i5C1E_PB_eqy`, `QED.ThreeLoopD.tendsto_i5C1PB_sub`.
-/

@[expose] public section

open Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- `log (1 - ξ - x) · C(x) → 0` as `x → (1 - ξ)⁻` when `C` is differentiable at `1 - ξ` with
`C (1 - ξ) = 0`. -/
theorem i5C1E_tendsto_log_mul_y {ξ : ℝ} {C : ℝ → ℝ} (hC : DifferentiableAt ℝ C (1 - ξ))
    (h0 : C (1 - ξ) = 0) :
    Tendsto (fun x => log (1 - ξ - x) * C x) (𝓝[<] (1 - ξ)) (𝓝 0) := by
  have hA : DifferentiableAt ℝ (fun t => C (1 - ξ - t)) 0 := by
    have hC' : DifferentiableAt ℝ C (1 - ξ - 0) := by rwa [sub_zero]
    exact hC'.comp 0 (by fun_prop)
  have h := i5C1_tendsto_log_pow_mul 1 hA (by simpa using h0)
  have hφ : Tendsto (fun x => 1 - ξ - x) (𝓝[<] (1 - ξ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Tendsto (fun x => 1 - ξ - x) (𝓝 (1 - ξ)) (𝓝 (1 - ξ - (1 - ξ))) :=
        ((continuous_const.sub continuous_id).tendsto _)
      rw [sub_self] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1 - ξ)
      simp only [mem_Ioi]
      linarith
  refine (h.comp hφ).congr fun x => ?_
  simp only [Function.comp, pow_one, sub_sub_cancel]

/-- Part `a` of the regular part of the primitive at `x = 1 - ξ`. -/
noncomputable def i5C1E_Rya (ξ x : ℝ) : ℝ :=
  (-1 / 3) * (π * π * log (ξ * x + (1 - ξ))) + 1 * (π * π * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
      (1 / 2) * (π * π * log (ξ * x + (1 - ξ) ^ 2)) + 3 * (log x * log x * log (ξ * x + (1 - ξ))) +
      (-3) * (log x * log x * log (1 - ξ)) + (-9 / 2) * (log x * log (ξ * x + (1 - ξ)) *
      log (ξ * x + (1 - ξ))) + 6 * (log x * log (ξ * x + (1 - ξ)) * log (1 + ξ)) + (-6) *
      (log x * log (ξ * x + (1 - ξ)) * log (1 - x)) + (-3) * (log x * log (ξ * x + (1 - ξ))) +
      (25 / 2) * (log x * log (1 - ξ) * log (1 - ξ)) + 10 * (log x * log (1 - ξ) * log (1 - x)) +
      (-4) * (log x * log (1 - ξ) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-4) *
      (log x * log (1 - ξ) * log (ξ * x + (1 - ξ) ^ 2)) + 3 * (log x * log (1 - ξ)) + (-2) *
      (log x * log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 *
      (log x * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2)) + 6 *
      (log x * Li₂ (x / (1 - ξ))) + 3 * (log x * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) + (-6) *
      (log x * Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) + 3 * (log x *
      Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))))

/-- The limit of `i5C1E_Rya`. -/
noncomputable def i5C1E_Vya (ξ : ℝ) : ℝ :=
  (-1 / 3) * (π * π * (log (1 - ξ) + log (1 + ξ))) + 1 * (π * π *
      (2 * log (1 - ξ) + log (1 + ξ))) + (1 / 2) * (π * π * (log (1 - ξ))) + 3 *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 - ξ) + log (1 + ξ))) + (-3) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 - ξ))) + (-9 / 2) *
      ((log (1 - ξ)) * (log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ) + log (1 + ξ))) + 6 *
      ((log (1 - ξ)) * (log (1 - ξ) + log (1 + ξ)) * (log (1 + ξ))) + (-6) *
      ((log (1 - ξ)) * (log (1 - ξ) + log (1 + ξ)) * (log ξ)) + (-3) *
      ((log (1 - ξ)) * (log (1 - ξ) + log (1 + ξ))) + (25 / 2) * ((log (1 - ξ)) * (log (1 - ξ)) *
      (log (1 - ξ))) + 10 * ((log (1 - ξ)) * (log (1 - ξ)) * (log ξ)) + (-4) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (2 * log (1 - ξ) + log (1 + ξ))) + (-4) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 - ξ))) + 3 * ((log (1 - ξ)) * (log (1 - ξ))) +
      (-2) * ((log (1 - ξ)) * (log ξ) * (2 * log (1 - ξ) + log (1 + ξ))) + 2 *
      ((log (1 - ξ)) * (2 * log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ))) + 6 *
      ((log (1 - ξ)) * (π ^ 2 / 6)) + 3 * ((log (1 - ξ)) * (Li₂ (-ξ))) + (-6) *
      ((log (1 - ξ)) * (π ^ 2 / 6)) + 3 * ((log (1 - ξ)) * (0))

theorem i5C1E_tRya {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_Rya ξ) (𝓝[<] (1 - ξ)) (𝓝 (i5C1E_Vya ξ)) := by
  have cπ : Tendsto (fun _ : ℝ => π) (𝓝[<] (1 - ξ)) (𝓝 π) := tendsto_const_nhds
  have t0 := i5C1E_ty_0 hξ
  have t1 := i5C1E_ty_1 hξ
  have c2 : Tendsto (fun _ : ℝ => log (1 - ξ)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 - ξ))) :=
    tendsto_const_nhds
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_ty_5 hξ
  have t6 := i5C1E_ty_6 hξ
  have t7 := i5C1E_ty_7 hξ
  have t10 := i5C1E_ty_10 hξ
  have t15 := i5C1E_ty_15 hξ
  have t17 := i5C1E_ty_17 hξ
  have t20 := i5C1E_ty_20 hξ
  have h := ((((((((((((((((((((((cπ.mul cπ).mul t1).const_mul (-1 / 3)).add
      (((cπ.mul cπ).mul t6).const_mul 1)).add (((cπ.mul cπ).mul t7).const_mul (1 / 2))).add
      (((t0.mul t0).mul t1).const_mul 3)).add (((t0.mul t0).mul c2).const_mul (-3))).add
      (((t0.mul t1).mul t1).const_mul (-9 / 2))).add (((t0.mul t1).mul c4).const_mul 6)).add
      (((t0.mul t1).mul t5).const_mul (-6))).add ((t0.mul t1).const_mul (-3))).add
      (((t0.mul c2).mul c2).const_mul (25 / 2))).add (((t0.mul c2).mul t5).const_mul 10)).add
      (((t0.mul c2).mul t6).const_mul (-4))).add (((t0.mul c2).mul t7).const_mul (-4))).add
      ((t0.mul c2).const_mul 3)).add (((t0.mul t5).mul t6).const_mul (-2))).add
      (((t0.mul t6).mul t7).const_mul 2)).add ((t0.mul t10).const_mul 6)).add
      ((t0.mul t15).const_mul 3)).add ((t0.mul t17).const_mul (-6))).add ((t0.mul t20).const_mul 3))
  exact h

/-- Part `b` of the regular part of the primitive at `x = 1 - ξ`. -/
noncomputable def i5C1E_Ryb (ξ x : ℝ) : ℝ :=
  (-3) * (log x * Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) + (-1 / 3) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ))) + (19 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (1 - ξ)) + (5 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (1 + ξ)) + (15 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (1 - x)) + 1 *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-3 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2)) + (-3) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log ξ) + (-1 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ))) + (-14) * (log (ξ * x + (1 - ξ)) *
      log (1 - ξ) * log (1 + ξ)) + 1 * (log (ξ * x + (1 - ξ)) * log (1 - ξ) * log (1 - x)) +
      (-12) * (log (ξ * x + (1 - ξ)) * log (1 - ξ) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 5 *
      (log (ξ * x + (1 - ξ)) * log (1 - ξ) * log ξ) + 4 * (log (ξ * x + (1 - ξ)) * log (1 - ξ)) +
      (-1) * (log (ξ * x + (1 - ξ)) * log (1 + ξ) * log (1 + ξ)) + (-5) *
      (log (ξ * x + (1 - ξ)) * log (1 + ξ) * log (1 - x)) + (-1) *
      (log (ξ * x + (1 - ξ)) * log (1 + ξ) * log (ξ * x + (1 - ξ) ^ 2)) + 1 *
      (log (ξ * x + (1 - ξ)) * log (1 + ξ) * log ξ) + (-3 / 2) * (log (ξ * x + (1 - ξ)) *
      log (1 - x) * log (1 - x)) + (-6) * (log (ξ * x + (1 - ξ)) * log (1 - x) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2))

/-- The limit of `i5C1E_Ryb`. -/
noncomputable def i5C1E_Vyb (ξ : ℝ) : ℝ :=
  (-3) * ((log (1 - ξ)) * (0)) + (-1 / 3) * ((log (1 - ξ) + log (1 + ξ)) *
      (log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ) + log (1 + ξ))) + (19 / 2) *
      ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ))) + (5 / 2) *
      ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ) + log (1 + ξ)) * (log (1 + ξ))) + (15 / 2) *
      ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ) + log (1 + ξ)) * (log ξ)) + 1 *
      ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ) + log (1 + ξ)) *
      (2 * log (1 - ξ) + log (1 + ξ))) + (-3 / 2) * ((log (1 - ξ) + log (1 + ξ)) *
      (log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ))) + (-3) * ((log (1 - ξ) + log (1 + ξ)) *
      (log (1 - ξ) + log (1 + ξ)) * (log ξ)) + (-1 / 2) * ((log (1 - ξ) + log (1 + ξ)) *
      (log (1 - ξ) + log (1 + ξ))) + (-14) * ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ)) *
      (log (1 + ξ))) + 1 * ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ)) * (log ξ)) + (-12) *
      ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ)) * (2 * log (1 - ξ) + log (1 + ξ))) + 5 *
      ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ)) * (log ξ)) + 4 *
      ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ))) + (-1) * ((log (1 - ξ) + log (1 + ξ)) *
      (log (1 + ξ)) * (log (1 + ξ))) + (-5) * ((log (1 - ξ) + log (1 + ξ)) * (log (1 + ξ)) *
      (log ξ)) + (-1) * ((log (1 - ξ) + log (1 + ξ)) * (log (1 + ξ)) * (log (1 - ξ))) + 1 *
      ((log (1 - ξ) + log (1 + ξ)) * (log (1 + ξ)) * (log ξ)) + (-3 / 2) *
      ((log (1 - ξ) + log (1 + ξ)) * (log ξ) * (log ξ)) + (-6) * ((log (1 - ξ) + log (1 + ξ)) *
      (log ξ) * (2 * log (1 - ξ) + log (1 + ξ)))

theorem i5C1E_tRyb {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_Ryb ξ) (𝓝[<] (1 - ξ)) (𝓝 (i5C1E_Vyb ξ)) := by
  have t0 := i5C1E_ty_0 hξ
  have t1 := i5C1E_ty_1 hξ
  have c2 : Tendsto (fun _ : ℝ => log (1 - ξ)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 - ξ))) :=
    tendsto_const_nhds
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_ty_5 hξ
  have t6 := i5C1E_ty_6 hξ
  have t7 := i5C1E_ty_7 hξ
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[<] (1 - ξ)) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have t21 := i5C1E_ty_21 hξ
  have h := (((((((((((((((((((((t0.mul t21).const_mul (-3)).add (((t1.mul t1).mul t1).const_mul
      (-1 / 3))).add (((t1.mul t1).mul c2).const_mul (19 / 2))).add
      (((t1.mul t1).mul c4).const_mul (5 / 2))).add (((t1.mul t1).mul t5).const_mul (15 / 2))).add
      (((t1.mul t1).mul t6).const_mul 1)).add (((t1.mul t1).mul t7).const_mul (-3 / 2))).add
      (((t1.mul t1).mul c8).const_mul (-3))).add ((t1.mul t1).const_mul (-1 / 2))).add
      (((t1.mul c2).mul c4).const_mul (-14))).add (((t1.mul c2).mul t5).const_mul 1)).add
      (((t1.mul c2).mul t6).const_mul (-12))).add (((t1.mul c2).mul c8).const_mul 5)).add
      ((t1.mul c2).const_mul 4)).add (((t1.mul c4).mul c4).const_mul (-1))).add
      (((t1.mul c4).mul t5).const_mul (-5))).add (((t1.mul c4).mul t7).const_mul (-1))).add
      (((t1.mul c4).mul c8).const_mul 1)).add (((t1.mul t5).mul t5).const_mul (-3 / 2))).add
      (((t1.mul t5).mul t6).const_mul (-6)))
  exact h

/-- Part `c` of the regular part of the primitive at `x = 1 - ξ`. -/
noncomputable def i5C1E_Ryc (ξ x : ℝ) : ℝ :=
  1 * (log (ξ * x + (1 - ξ)) * log (1 - x)) + 4 * (log (ξ * x + (1 - ξ)) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log ξ) + 1 *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2)) + 3 *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) * log ξ) + (-1 / 2) *
      (log (ξ * x + (1 - ξ)) * log ξ * log ξ) + (-1) * (log (ξ * x + (1 - ξ)) * log ξ) + 2 *
      (log (ξ * x + (1 - ξ)) * Li₂ (x)) + (-3) * (log (ξ * x + (1 - ξ)) * Li₂ (x / (1 - ξ))) +
      (-1) * (log (ξ * x + (1 - ξ)) * Li₂ (ξ / (1 - x))) + 4 * (log (ξ * x + (1 - ξ)) *
      Li₂ (-(ξ * x / (1 - ξ)))) + (-2) * (log (ξ * x + (1 - ξ)) * Li₂ (x / (ξ * x + (1 - ξ)))) +
      1 * (log (ξ * x + (1 - ξ)) * Li₂ (ξ * (1 - ξ - x) / (1 - ξ))) + 2 *
      (log (ξ * x + (1 - ξ)) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + (-3 / 2) *
      (log (1 - ξ) * log (1 - ξ) * log (1 - x)) + 7 * (log (1 - ξ) * log (1 - ξ) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-5 / 2) * (log (1 - ξ) * log (1 - ξ) *
      log (ξ * x + (1 - ξ) ^ 2)) + 3 * (log (1 - ξ) * log (1 + ξ) * log (1 - x)) + 1 *
      (log (1 - ξ) * log (1 - x) * log (1 - x)) + (-2) * (log (1 - ξ) * log (1 - x) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2))

/-- The limit of `i5C1E_Ryc`. -/
noncomputable def i5C1E_Vyc (ξ : ℝ) : ℝ :=
  1 * ((log (1 - ξ) + log (1 + ξ)) * (log ξ)) + 4 * ((log (1 - ξ) + log (1 + ξ)) *
      (2 * log (1 - ξ) + log (1 + ξ)) * (2 * log (1 - ξ) + log (1 + ξ))) + (-2) *
      ((log (1 - ξ) + log (1 + ξ)) * (2 * log (1 - ξ) + log (1 + ξ)) * (log ξ)) + 1 *
      ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ)) * (log (1 - ξ))) + 3 *
      ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ)) * (log ξ)) + (-1 / 2) *
      ((log (1 - ξ) + log (1 + ξ)) * (log ξ) * (log ξ)) + (-1) * ((log (1 - ξ) + log (1 + ξ)) *
      (log ξ)) + 2 * ((log (1 - ξ) + log (1 + ξ)) * (π ^ 2 / 6 - Li₂ ξ - log ξ * log (1 - ξ))) +
      (-3) * ((log (1 - ξ) + log (1 + ξ)) * (π ^ 2 / 6)) + (-1) *
      ((log (1 - ξ) + log (1 + ξ)) * (π ^ 2 / 6)) + 4 * ((log (1 - ξ) + log (1 + ξ)) *
      (Li₂ (-ξ))) + (-2) * ((log (1 - ξ) + log (1 + ξ)) * (π ^ 2 / 6 + Li₂ (-ξ) +
      log (1 + ξ) ^ 2 / 2 + log (1 + ξ) * (log ξ - log (1 + ξ)))) + 1 *
      ((log (1 - ξ) + log (1 + ξ)) * (0)) + 2 * ((log (1 - ξ) + log (1 + ξ)) *
      (-Li₂ (-ξ) - log (1 + ξ) ^ 2 / 2)) + (-3 / 2) * ((log (1 - ξ)) * (log (1 - ξ)) * (log ξ)) +
      7 * ((log (1 - ξ)) * (log (1 - ξ)) * (2 * log (1 - ξ) + log (1 + ξ))) + (-5 / 2) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 - ξ))) + 3 * ((log (1 - ξ)) * (log (1 + ξ)) *
      (log ξ)) + 1 * ((log (1 - ξ)) * (log ξ) * (log ξ)) + (-2) *
      ((log (1 - ξ)) * (log ξ) * (2 * log (1 - ξ) + log (1 + ξ)))

theorem i5C1E_tRyc {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_Ryc ξ) (𝓝[<] (1 - ξ)) (𝓝 (i5C1E_Vyc ξ)) := by
  have t1 := i5C1E_ty_1 hξ
  have c2 : Tendsto (fun _ : ℝ => log (1 - ξ)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 - ξ))) :=
    tendsto_const_nhds
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_ty_5 hξ
  have t6 := i5C1E_ty_6 hξ
  have t7 := i5C1E_ty_7 hξ
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[<] (1 - ξ)) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have t9 := i5C1E_ty_9 hξ
  have t10 := i5C1E_ty_10 hξ
  have t11 := i5C1E_ty_11 hξ
  have t13 := i5C1E_ty_13 hξ
  have t14 := i5C1E_ty_14 hξ
  have t16 := i5C1E_ty_16 hξ
  have t19 := i5C1E_ty_19 hξ
  have h := (((((((((((((((((((((t1.mul t5).const_mul 1).add (((t1.mul t6).mul t6).const_mul
      4)).add (((t1.mul t6).mul c8).const_mul (-2))).add (((t1.mul t7).mul t7).const_mul 1)).add
      (((t1.mul t7).mul c8).const_mul 3)).add (((t1.mul c8).mul c8).const_mul (-1 / 2))).add
      ((t1.mul c8).const_mul (-1))).add ((t1.mul t9).const_mul 2)).add
      ((t1.mul t10).const_mul (-3))).add ((t1.mul t11).const_mul (-1))).add
      ((t1.mul t13).const_mul 4)).add ((t1.mul t14).const_mul (-2))).add
      ((t1.mul t16).const_mul 1)).add ((t1.mul t19).const_mul 2)).add
      (((c2.mul c2).mul t5).const_mul (-3 / 2))).add (((c2.mul c2).mul t6).const_mul 7)).add
      (((c2.mul c2).mul t7).const_mul (-5 / 2))).add (((c2.mul c4).mul t5).const_mul 3)).add
      (((c2.mul t5).mul t5).const_mul 1)).add (((c2.mul t5).mul t6).const_mul (-2)))
  exact h

/-- Part `d` of the regular part of the primitive at `x = 1 - ξ`. -/
noncomputable def i5C1E_Ryd (ξ x : ℝ) : ℝ :=
  (-1) * (log (1 - ξ) * log (1 - x) * log ξ) + 2 * (log (1 - ξ) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 3 * (log (1 - ξ) * log (ξ * x + (1 - ξ) ^ 2) *
      log (ξ * x + (1 - ξ) ^ 2)) + (-1) * (log (1 - ξ) * log (ξ * x + (1 - ξ) ^ 2) * log ξ) + 4 *
      (log (1 - ξ) * Li₂ (x)) + (-25) * (log (1 - ξ) * Li₂ (x / (1 - ξ))) + (-3) *
      (log (1 - ξ) * Li₂ (ξ / (1 - x))) + 3 * (log (1 - ξ) * Li₂ (ξ * (1 - x))) + (-9) *
      (log (1 - ξ) * Li₂ (-(ξ * x / (1 - ξ)))) + (-4) * (log (1 - ξ) *
      Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) + (-1) * (log (1 - ξ) * Li₂ (ξ * (1 - ξ - x) / (1 - ξ))) +
      12 * (log (1 - ξ) * Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) + 4 *
      (log (1 - ξ) * Li₂ (x / (ξ * x + (1 - ξ) ^ 2))) + (-3) * (log (1 - ξ) *
      Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + 4 * (log (1 - ξ) *
      Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) + (3 / 2) *
      (log (1 + ξ) * log (1 + ξ) * log (1 - x)) + 1 * (log (1 + ξ) * log (1 - x) * log (1 - x)) +
      (-1) * (log (1 + ξ) * log (1 - x) * log ξ) + 2 * (log (1 + ξ) * log (ξ * x + (1 - ξ) ^ 2) *
      log ξ) + (-3) * (log (1 + ξ) * Li₂ (x / (1 - ξ)))

/-- The limit of `i5C1E_Ryd`. -/
noncomputable def i5C1E_Vyd (ξ : ℝ) : ℝ :=
  (-1) * ((log (1 - ξ)) * (log ξ) * (log ξ)) + 2 * ((log (1 - ξ)) *
      (2 * log (1 - ξ) + log (1 + ξ)) * (2 * log (1 - ξ) + log (1 + ξ))) + 3 *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 - ξ))) + (-1) * ((log (1 - ξ)) * (log (1 - ξ)) *
      (log ξ)) + 4 * ((log (1 - ξ)) * (π ^ 2 / 6 - Li₂ ξ - log ξ * log (1 - ξ))) + (-25) *
      ((log (1 - ξ)) * (π ^ 2 / 6)) + (-3) * ((log (1 - ξ)) * (π ^ 2 / 6)) + 3 *
      ((log (1 - ξ)) * (2 * Li₂ ξ + 2 * Li₂ (-ξ))) + (-9) * ((log (1 - ξ)) * (Li₂ (-ξ))) + (-4) *
      ((log (1 - ξ)) * (Li₂ (-ξ))) + (-1) * ((log (1 - ξ)) * (0)) + 12 *
      ((log (1 - ξ)) * (π ^ 2 / 6)) + 4 * ((log (1 - ξ)) * (π ^ 2 / 6)) + (-3) *
      ((log (1 - ξ)) * (-Li₂ (-ξ) - log (1 + ξ) ^ 2 / 2)) + 4 * ((log (1 - ξ)) * (0)) + (3 / 2) *
      ((log (1 + ξ)) * (log (1 + ξ)) * (log ξ)) + 1 * ((log (1 + ξ)) * (log ξ) * (log ξ)) + (-1) *
      ((log (1 + ξ)) * (log ξ) * (log ξ)) + 2 * ((log (1 + ξ)) * (log (1 - ξ)) * (log ξ)) + (-3) *
      ((log (1 + ξ)) * (π ^ 2 / 6))

theorem i5C1E_tRyd {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_Ryd ξ) (𝓝[<] (1 - ξ)) (𝓝 (i5C1E_Vyd ξ)) := by
  have c2 : Tendsto (fun _ : ℝ => log (1 - ξ)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 - ξ))) :=
    tendsto_const_nhds
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_ty_5 hξ
  have t6 := i5C1E_ty_6 hξ
  have t7 := i5C1E_ty_7 hξ
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[<] (1 - ξ)) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have t9 := i5C1E_ty_9 hξ
  have t10 := i5C1E_ty_10 hξ
  have t11 := i5C1E_ty_11 hξ
  have t12 := i5C1E_ty_12 hξ
  have t13 := i5C1E_ty_13 hξ
  have t15 := i5C1E_ty_15 hξ
  have t16 := i5C1E_ty_16 hξ
  have t17 := i5C1E_ty_17 hξ
  have t18 := i5C1E_ty_18 hξ
  have t19 := i5C1E_ty_19 hξ
  have t21 := i5C1E_ty_21 hξ
  have h := ((((((((((((((((((((((c2.mul t5).mul c8).const_mul (-1)).add
      (((c2.mul t6).mul t6).const_mul 2)).add (((c2.mul t7).mul t7).const_mul 3)).add
      (((c2.mul t7).mul c8).const_mul (-1))).add ((c2.mul t9).const_mul 4)).add
      ((c2.mul t10).const_mul (-25))).add ((c2.mul t11).const_mul (-3))).add
      ((c2.mul t12).const_mul 3)).add ((c2.mul t13).const_mul (-9))).add
      ((c2.mul t15).const_mul (-4))).add ((c2.mul t16).const_mul (-1))).add
      ((c2.mul t17).const_mul 12)).add ((c2.mul t18).const_mul 4)).add
      ((c2.mul t19).const_mul (-3))).add ((c2.mul t21).const_mul 4)).add
      (((c4.mul c4).mul t5).const_mul (3 / 2))).add (((c4.mul t5).mul t5).const_mul 1)).add
      (((c4.mul t5).mul c8).const_mul (-1))).add (((c4.mul t7).mul c8).const_mul 2)).add
      ((c4.mul t10).const_mul (-3)))
  exact h

/-- Part `e` of the regular part of the primitive at `x = 1 - ξ`. -/
noncomputable def i5C1E_Rye (ξ x : ℝ) : ℝ :=
  (-1) * (log (1 + ξ) * Li₂ (ξ / (1 - x))) + (-1) * (log (1 + ξ) * Li₂ (ξ * (1 - x))) + 3 *
      (log (1 + ξ) * Li₂ (-(ξ * x / (1 - ξ)))) + 1 * (log (1 + ξ) *
      Li₂ (ξ * (1 - ξ - x) / (1 - ξ))) + 1 * (log (1 + ξ) * Li₂ (ξ *
      (1 - ξ) / (ξ * x + (1 - ξ)))) + 1 * (log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-2) * (log (1 - x) * Li₂ (x)) + (-3) *
      (log (1 - x) * Li₂ (x / (1 - ξ))) + (-1) * (log (1 - x) * Li₂ (-(ξ * x / (1 - ξ)))) + 2 *
      (log (1 - x) * Li₂ (x / (ξ * x + (1 - ξ)))) + (-1) * (log (1 - x) *
      Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) + 3 * (log (1 - x) * Li₂ ((1 + ξ) *
      x / (ξ * x + (1 - ξ)))) + (-2) * (log (1 - x) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + 1 *
      (log (1 - x) * Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) + (-5 / 3) *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 1 * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2)) + (-2) *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2)) +
      (-4) * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (x)) + 8 * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
      Li₂ (x / (1 - ξ))) + 2 * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (ξ / (1 - x)))

/-- The limit of `i5C1E_Rye`. -/
noncomputable def i5C1E_Vye (ξ : ℝ) : ℝ :=
  (-1) * ((log (1 + ξ)) * (π ^ 2 / 6)) + (-1) * ((log (1 + ξ)) * (2 * Li₂ ξ + 2 * Li₂ (-ξ))) + 3 *
      ((log (1 + ξ)) * (Li₂ (-ξ))) + 1 * ((log (1 + ξ)) * (0)) + 1 *
      ((log (1 + ξ)) * (-Li₂ (-ξ) - log (1 + ξ) ^ 2 / 2)) + 1 * ((log ξ) *
      (2 * log (1 - ξ) + log (1 + ξ)) * (2 * log (1 - ξ) + log (1 + ξ))) + (-2) *
      ((log ξ) * (π ^ 2 / 6 - Li₂ ξ - log ξ * log (1 - ξ))) + (-3) * ((log ξ) * (π ^ 2 / 6)) +
      (-1) * ((log ξ) * (Li₂ (-ξ))) + 2 * ((log ξ) * (π ^ 2 / 6 + Li₂ (-ξ) + log (1 + ξ) ^ 2 / 2 +
      log (1 + ξ) * (log ξ - log (1 + ξ)))) + (-1) * ((log ξ) * (Li₂ (-ξ))) + 3 *
      ((log ξ) * (π ^ 2 / 6)) + (-2) * ((log ξ) * (-Li₂ (-ξ) - log (1 + ξ) ^ 2 / 2)) + 1 *
      ((log ξ) * (0)) + (-5 / 3) * ((2 * log (1 - ξ) + log (1 + ξ)) *
      (2 * log (1 - ξ) + log (1 + ξ)) * (2 * log (1 - ξ) + log (1 + ξ))) + 1 *
      ((2 * log (1 - ξ) + log (1 + ξ)) * (2 * log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ))) + (-2) *
      ((2 * log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ)) * (log (1 - ξ))) + (-4) *
      ((2 * log (1 - ξ) + log (1 + ξ)) * (π ^ 2 / 6 - Li₂ ξ - log ξ * log (1 - ξ))) + 8 *
      ((2 * log (1 - ξ) + log (1 + ξ)) * (π ^ 2 / 6)) + 2 * ((2 * log (1 - ξ) + log (1 + ξ)) *
      (π ^ 2 / 6))

theorem i5C1E_tRye {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_Rye ξ) (𝓝[<] (1 - ξ)) (𝓝 (i5C1E_Vye ξ)) := by
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_ty_5 hξ
  have t6 := i5C1E_ty_6 hξ
  have t7 := i5C1E_ty_7 hξ
  have t9 := i5C1E_ty_9 hξ
  have t10 := i5C1E_ty_10 hξ
  have t11 := i5C1E_ty_11 hξ
  have t12 := i5C1E_ty_12 hξ
  have t13 := i5C1E_ty_13 hξ
  have t14 := i5C1E_ty_14 hξ
  have t15 := i5C1E_ty_15 hξ
  have t16 := i5C1E_ty_16 hξ
  have t17 := i5C1E_ty_17 hξ
  have t19 := i5C1E_ty_19 hξ
  have t21 := i5C1E_ty_21 hξ
  have h := (((((((((((((((((((((c4.mul t11).const_mul (-1)).add ((c4.mul t12).const_mul (-1))).add
      ((c4.mul t13).const_mul 3)).add ((c4.mul t16).const_mul 1)).add
      ((c4.mul t19).const_mul 1)).add (((t5.mul t6).mul t6).const_mul 1)).add
      ((t5.mul t9).const_mul (-2))).add ((t5.mul t10).const_mul (-3))).add
      ((t5.mul t13).const_mul (-1))).add ((t5.mul t14).const_mul 2)).add
      ((t5.mul t15).const_mul (-1))).add ((t5.mul t17).const_mul 3)).add
      ((t5.mul t19).const_mul (-2))).add ((t5.mul t21).const_mul 1)).add
      (((t6.mul t6).mul t6).const_mul (-5 / 3))).add (((t6.mul t6).mul t7).const_mul 1)).add
      (((t6.mul t7).mul t7).const_mul (-2))).add ((t6.mul t9).const_mul (-4))).add
      ((t6.mul t10).const_mul 8)).add ((t6.mul t11).const_mul 2))
  exact h

/-- Part `f` of the regular part of the primitive at `x = 1 - ξ`. -/
noncomputable def i5C1E_Ryf (ξ x : ℝ) : ℝ :=
  (-4) * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (ξ * (1 - x))) + 8 *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (-(ξ * x / (1 - ξ)))) + 2 *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (x / (ξ * x + (1 - ξ)))) + (-2) *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (x / (ξ * x + (1 - ξ) ^ 2))) + 2 *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + (-1) *
      (log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2) * log ξ) + (-2) *
      (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (x)) + 2 * (log (ξ * x + (1 - ξ) ^ 2) *
      Li₂ (-(ξ * x / (1 - ξ)))) + 2 * (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (x / (ξ * x + (1 - ξ)))) +
      1 * (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) + (-2) *
      (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + 3 *
      (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))) + (-1) *
      (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) + 3 *
      (log ξ * Li₂ (x / (1 - ξ))) + (-3) * (log ξ * Li₂ (-(ξ * x / (1 - ξ)))) + 1 *
      (log ξ * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) + (-3) * (log ξ *
      Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) + (-1) * (log ξ * Li₂ (-(ξ *
      (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) + 1 * Li₂ (ξ * (1 - x)) + (-3) *
      Li₂ (-(ξ * x / (1 - ξ)))

/-- The limit of `i5C1E_Ryf`. -/
noncomputable def i5C1E_Vyf (ξ : ℝ) : ℝ :=
  (-4) * ((2 * log (1 - ξ) + log (1 + ξ)) * (2 * Li₂ ξ + 2 * Li₂ (-ξ))) + 8 *
      ((2 * log (1 - ξ) + log (1 + ξ)) * (Li₂ (-ξ))) + 2 * ((2 * log (1 - ξ) + log (1 + ξ)) *
      (π ^ 2 / 6 + Li₂ (-ξ) + log (1 + ξ) ^ 2 / 2 + log (1 + ξ) * (log ξ - log (1 + ξ)))) + (-2) *
      ((2 * log (1 - ξ) + log (1 + ξ)) * (π ^ 2 / 6)) + 2 * ((2 * log (1 - ξ) + log (1 + ξ)) *
      (-Li₂ (-ξ) - log (1 + ξ) ^ 2 / 2)) + (-1) * ((log (1 - ξ)) * (log (1 - ξ)) * (log ξ)) +
      (-2) * ((log (1 - ξ)) * (π ^ 2 / 6 - Li₂ ξ - log ξ * log (1 - ξ))) + 2 *
      ((log (1 - ξ)) * (Li₂ (-ξ))) + 2 * ((log (1 - ξ)) * (π ^ 2 / 6 + Li₂ (-ξ) +
      log (1 + ξ) ^ 2 / 2 + log (1 + ξ) * (log ξ - log (1 + ξ)))) + 1 *
      ((log (1 - ξ)) * (Li₂ (-ξ))) + (-2) * ((log (1 - ξ)) * (-Li₂ (-ξ) - log (1 + ξ) ^ 2 / 2)) +
      3 * ((log (1 - ξ)) * (0)) + (-1) * ((log (1 - ξ)) * (0)) + 3 * ((log ξ) * (π ^ 2 / 6)) +
      (-3) * ((log ξ) * (Li₂ (-ξ))) + 1 * ((log ξ) * (Li₂ (-ξ))) + (-3) * ((log ξ) * (π ^ 2 / 6)) +
      (-1) * ((log ξ) * (0)) + 1 * (2 * Li₂ ξ + 2 * Li₂ (-ξ)) + (-3) * (Li₂ (-ξ))

theorem i5C1E_tRyf {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_Ryf ξ) (𝓝[<] (1 - ξ)) (𝓝 (i5C1E_Vyf ξ)) := by
  have t6 := i5C1E_ty_6 hξ
  have t7 := i5C1E_ty_7 hξ
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[<] (1 - ξ)) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have t9 := i5C1E_ty_9 hξ
  have t10 := i5C1E_ty_10 hξ
  have t12 := i5C1E_ty_12 hξ
  have t13 := i5C1E_ty_13 hξ
  have t14 := i5C1E_ty_14 hξ
  have t15 := i5C1E_ty_15 hξ
  have t17 := i5C1E_ty_17 hξ
  have t18 := i5C1E_ty_18 hξ
  have t19 := i5C1E_ty_19 hξ
  have t20 := i5C1E_ty_20 hξ
  have t21 := i5C1E_ty_21 hξ
  have h := (((((((((((((((((((((t6.mul t12).const_mul (-4)).add ((t6.mul t13).const_mul 8)).add
      ((t6.mul t14).const_mul 2)).add ((t6.mul t18).const_mul (-2))).add
      ((t6.mul t19).const_mul 2)).add (((t7.mul t7).mul c8).const_mul (-1))).add
      ((t7.mul t9).const_mul (-2))).add ((t7.mul t13).const_mul 2)).add
      ((t7.mul t14).const_mul 2)).add ((t7.mul t15).const_mul 1)).add
      ((t7.mul t19).const_mul (-2))).add ((t7.mul t20).const_mul 3)).add
      ((t7.mul t21).const_mul (-1))).add ((c8.mul t10).const_mul 3)).add
      ((c8.mul t13).const_mul (-3))).add ((c8.mul t15).const_mul 1)).add
      ((c8.mul t17).const_mul (-3))).add ((c8.mul t21).const_mul (-1))).add (t12.const_mul 1)).add
      (t13.const_mul (-3)))
  exact h

/-- Part `g` of the regular part of the primitive at `x = 1 - ξ`. -/
noncomputable def i5C1E_Ryg (ξ x : ℝ) : ℝ :=
  (-1) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) + (-8) * Li₃ ((1 - x)) + (-9) * Li₃ (x / (1 - ξ)) +
      4 * Li₃ (ξ / (1 - x)) + 3 * Li₃ (ξ * (1 - x)) + (-18) * Li₃ (-(ξ * x / (1 - ξ))) + (-1) *
      Li₃ ((ξ * x + (1 - ξ))) + 1 * Li₃ ((1 - ξ - x) / (1 - x)) + (-6) *
      Li₃ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) + 3 * Li₃ ((1 - ξ - x) / (1 - ξ)) + 1 *
      Li₃ (ξ * (1 - ξ - x) / (1 - ξ)) + 3 * Li₃ ((1 + ξ) * x / (ξ * x + (1 - ξ))) + 4 *
      Li₃ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) + (-3) * Li₃ ((1 - ξ - x) / (ξ * x + (1 - ξ))) + 6 *
      Li₃ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) + 6 * Li₃ ((1 - ξ) *
      (1 - x) / (ξ * x + (1 - ξ))) + (-3) * Li₃ ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ)) + (-3) *
      Li₃ ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) + (-2) * Li₃ ((ξ * x ^ 2 +
      (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)) + (-15) * Li₃ (ξ * x / (ξ * x + (1 - ξ)))

/-- The limit of `i5C1E_Ryg`. -/
noncomputable def i5C1E_Vyg (ξ : ℝ) : ℝ :=
  (-1) * (-Li₂ (-ξ) - log (1 + ξ) ^ 2 / 2) + (-8) * (Li₃ ξ) + (-9) * (zeta3) + 4 * (zeta3) + 3 *
      (Li₃ (ξ ^ 2)) + (-18) * (Li₃ (-ξ)) + (-1) * (Li₃ (1 - ξ ^ 2)) + 1 * (0) + (-6) * (Li₃ (-ξ)) +
      3 * (0) + 1 * (0) + 3 * (zeta3) + 4 * (Li₃ (ξ / (1 + ξ))) + (-3) * (0) + 6 * (0) + 6 *
      (Li₃ (ξ / (1 + ξ))) + (-3) * (zeta3) + (-3) * (Li₃ (1 / (1 + ξ))) + (-2) *
      (Li₃ (1 - ξ ^ 2)) + (-15) * (Li₃ (ξ / (1 + ξ)))

theorem i5C1E_tRyg {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_Ryg ξ) (𝓝[<] (1 - ξ)) (𝓝 (i5C1E_Vyg ξ)) := by
  have t19 := i5C1E_ty_19 hξ
  have t22 := i5C1E_ty_22 hξ
  have t23 := i5C1E_ty_23 hξ
  have t24 := i5C1E_ty_24 hξ
  have t25 := i5C1E_ty_25 hξ
  have t26 := i5C1E_ty_26 hξ
  have t27 := i5C1E_ty_27 hξ
  have t28 := i5C1E_ty_28 hξ
  have t29 := i5C1E_ty_29 hξ
  have t30 := i5C1E_ty_30 hξ
  have t31 := i5C1E_ty_31 hξ
  have t32 := i5C1E_ty_32 hξ
  have t33 := i5C1E_ty_33 hξ
  have t34 := i5C1E_ty_34 hξ
  have t35 := i5C1E_ty_35 hξ
  have t36 := i5C1E_ty_36 hξ
  have t37 := i5C1E_ty_37 hξ
  have t38 := i5C1E_ty_38 hξ
  have t39 := i5C1E_ty_39 hξ
  have t40 := i5C1E_ty_40 hξ
  have h := ((((((((((((((((((((t19.const_mul (-1)).add (t22.const_mul (-8))).add
      (t23.const_mul (-9))).add (t24.const_mul 4)).add (t25.const_mul 3)).add
      (t26.const_mul (-18))).add (t27.const_mul (-1))).add (t28.const_mul 1)).add
      (t29.const_mul (-6))).add (t30.const_mul 3)).add (t31.const_mul 1)).add
      (t32.const_mul 3)).add (t33.const_mul 4)).add (t34.const_mul (-3))).add
      (t35.const_mul 6)).add (t36.const_mul 6)).add (t37.const_mul (-3))).add
      (t38.const_mul (-3))).add (t39.const_mul (-2))).add (t40.const_mul (-15)))
  exact h

/-- Part `h` of the regular part of the primitive at `x = 1 - ξ`. -/
noncomputable def i5C1E_Ryh (ξ x : ℝ) : ℝ :=
  3 * Li₃ (ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ))) + (-1) * Li₃ (ξ ^ 2 *
      (1 - ξ - x) / (ξ * x + (1 - ξ))) + (-6) * Li₃ (ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 *
      Li₃ ((1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2)) + (-1) * Li₃ ((1 - ξ - x) / ((1 - ξ) * (1 + ξ) *
      (1 - x))) + 6 * Li₃ (ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))) + (-2) *
      Li₃ (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))) + 6 *
      Li₃ (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 6 *
      Li₃ (-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) + 2 *
      Li₃ ((1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 1 *
      Li₃ ((1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) + (-2) *
      Li₃ (ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ)) * (1 - x))) + 2 *
      Li₃ ((ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2))

/-- The limit of `i5C1E_Ryh`. -/
noncomputable def i5C1E_Vyh (ξ : ℝ) : ℝ :=
  3 * (0) + (-1) * (0) + (-6) * (Li₃ (ξ / (1 + ξ))) + 2 * (Li₃ (1 - ξ)) + (-1) * (0) + 6 * (0) +
      (-2) * (zeta3) + 6 * (zeta3) + 6 * (0) + 2 * (Li₃ (ξ / (1 + ξ))) + 1 * (zeta3) + (-2) *
      (zeta3) + 2 * (zeta3)

theorem i5C1E_tRyh {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_Ryh ξ) (𝓝[<] (1 - ξ)) (𝓝 (i5C1E_Vyh ξ)) := by
  have t41 := i5C1E_ty_41 hξ
  have t42 := i5C1E_ty_42 hξ
  have t43 := i5C1E_ty_43 hξ
  have t44 := i5C1E_ty_44 hξ
  have t45 := i5C1E_ty_45 hξ
  have t46 := i5C1E_ty_46 hξ
  have t47 := i5C1E_ty_47 hξ
  have t48 := i5C1E_ty_48 hξ
  have t49 := i5C1E_ty_49 hξ
  have t50 := i5C1E_ty_50 hξ
  have t51 := i5C1E_ty_51 hξ
  have t52 := i5C1E_ty_52 hξ
  have t53 := i5C1E_ty_53 hξ
  have h := (((((((((((((t41.const_mul 3).add (t42.const_mul (-1))).add (t43.const_mul (-6))).add
      (t44.const_mul 2)).add (t45.const_mul (-1))).add (t46.const_mul 6)).add
      (t47.const_mul (-2))).add (t48.const_mul 6)).add (t49.const_mul 6)).add
      (t50.const_mul 2)).add (t51.const_mul 1)).add (t52.const_mul (-2))).add (t53.const_mul 2))
  exact h

/-- The limit of the primitive at `x = 1 - ξ`. -/
noncomputable def i5C1E_Vy (ξ : ℝ) : ℝ :=
  i5C1E_Vya ξ + i5C1E_Vyb ξ + i5C1E_Vyc ξ + i5C1E_Vyd ξ + i5C1E_Vye ξ + i5C1E_Vyf ξ + i5C1E_Vyg ξ +
      i5C1E_Vyh ξ

/-- The coefficient of `log (1 - ξ - x) ^ 1` in the primitive. -/
noncomputable def i5C1E_C1 (ξ x : ℝ) : ℝ :=
  9 * (log x * log (ξ * x + (1 - ξ))) + (-9) * (log x * log (1 - ξ)) + (-6) *
      (log x * log (1 + ξ)) + (7 / 2) * (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ))) + (-11) *
      (log (ξ * x + (1 - ξ)) * log (1 - ξ)) + (-2) * (log (ξ * x + (1 - ξ)) * log (1 + ξ)) + (-1) *
      (log (ξ * x + (1 - ξ)) * log (1 - x)) + (-6) * (log (ξ * x + (1 - ξ)) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 1 * (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2)) +
      3 * (log (ξ * x + (1 - ξ)) * log ξ) + (39 / 2) * (log (1 - ξ) * log (1 - ξ)) + 13 *
      (log (1 - ξ) * log (1 + ξ)) + 2 * (log (1 - ξ) * log (1 - x)) + (-6) *
      (log (1 - ξ) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-1) * (log (1 - ξ) *
      log (ξ * x + (1 - ξ) ^ 2)) + (-2) * (log (1 - ξ) * log ξ) + 1 * (log (1 + ξ) * log (1 + ξ)) +
      2 * (log (1 + ξ) * log (1 - x)) + 1 * (log (1 + ξ) * log (ξ * x + (1 - ξ) ^ 2)) + (-2) *
      (log (1 + ξ) * log ξ) + 3 * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
      2 * Li₂ (x) + 1 * Li₂ (ξ * (1 - x)) + 1 * Li₂ (-(ξ * x / (1 - ξ))) + (-2) *
      Li₂ (x / (ξ * x + (1 - ξ))) + 1 * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))

theorem i5C1E_tC1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_C1 ξ) (𝓝[<] (1 - ξ)) (𝓝 (9 * ((log (1 - ξ)) * (log (1 - ξ) + log (1 + ξ))) +
        (-9) * ((log (1 - ξ)) * (log (1 - ξ))) + (-6) * ((log (1 - ξ)) * (log (1 + ξ))) + (7 / 2) *
        ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ) + log (1 + ξ))) + (-11) *
        ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ))) + (-2) * ((log (1 - ξ) + log (1 + ξ)) *
        (log (1 + ξ))) + (-1) * ((log (1 - ξ) + log (1 + ξ)) * (log ξ)) + (-6) *
        ((log (1 - ξ) + log (1 + ξ)) * (2 * log (1 - ξ) + log (1 + ξ))) + 1 *
        ((log (1 - ξ) + log (1 + ξ)) * (log (1 - ξ))) + 3 * ((log (1 - ξ) + log (1 + ξ)) *
        (log ξ)) + (39 / 2) * ((log (1 - ξ)) * (log (1 - ξ))) + 13 *
        ((log (1 - ξ)) * (log (1 + ξ))) + 2 * ((log (1 - ξ)) * (log ξ)) + (-6) *
        ((log (1 - ξ)) * (2 * log (1 - ξ) + log (1 + ξ))) + (-1) *
        ((log (1 - ξ)) * (log (1 - ξ))) + (-2) * ((log (1 - ξ)) * (log ξ)) + 1 *
        ((log (1 + ξ)) * (log (1 + ξ))) + 2 * ((log (1 + ξ)) * (log ξ)) + 1 *
        ((log (1 + ξ)) * (log (1 - ξ))) + (-2) * ((log (1 + ξ)) * (log ξ)) + 3 *
        ((2 * log (1 - ξ) + log (1 + ξ)) * (2 * log (1 - ξ) + log (1 + ξ))) + 2 *
        (π ^ 2 / 6 - Li₂ ξ - log ξ * log (1 - ξ)) + 1 * (2 * Li₂ ξ + 2 * Li₂ (-ξ)) + 1 *
        (Li₂ (-ξ)) + (-2) * (π ^ 2 / 6 + Li₂ (-ξ) + log (1 + ξ) ^ 2 / 2 + log (1 + ξ) *
        (log ξ - log (1 + ξ))) + 1 * (-Li₂ (-ξ) - log (1 + ξ) ^ 2 / 2))) := by
  have t0 := i5C1E_ty_0 hξ
  have t1 := i5C1E_ty_1 hξ
  have c2 : Tendsto (fun _ : ℝ => log (1 - ξ)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 - ξ))) :=
    tendsto_const_nhds
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_ty_5 hξ
  have t6 := i5C1E_ty_6 hξ
  have t7 := i5C1E_ty_7 hξ
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[<] (1 - ξ)) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have t9 := i5C1E_ty_9 hξ
  have t12 := i5C1E_ty_12 hξ
  have t13 := i5C1E_ty_13 hξ
  have t14 := i5C1E_ty_14 hξ
  have t19 := i5C1E_ty_19 hξ
  have h := (((((((((((((((((((((((((((t0.mul t1).const_mul 9).add
      ((t0.mul c2).const_mul (-9))).add ((t0.mul c4).const_mul (-6))).add
      ((t1.mul t1).const_mul (7 / 2))).add ((t1.mul c2).const_mul (-11))).add
      ((t1.mul c4).const_mul (-2))).add ((t1.mul t5).const_mul (-1))).add
      ((t1.mul t6).const_mul (-6))).add ((t1.mul t7).const_mul 1)).add
      ((t1.mul c8).const_mul 3)).add ((c2.mul c2).const_mul (39 / 2))).add
      ((c2.mul c4).const_mul 13)).add ((c2.mul t5).const_mul 2)).add
      ((c2.mul t6).const_mul (-6))).add ((c2.mul t7).const_mul (-1))).add
      ((c2.mul c8).const_mul (-2))).add ((c4.mul c4).const_mul 1)).add
      ((c4.mul t5).const_mul 2)).add ((c4.mul t7).const_mul 1)).add
      ((c4.mul c8).const_mul (-2))).add ((t6.mul t6).const_mul 3)).add (t9.const_mul 2)).add
      (t12.const_mul 1)).add (t13.const_mul 1)).add (t14.const_mul (-2))).add (t19.const_mul 1))
  exact h

theorem i5C1E_dC1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (i5C1E_C1 ξ) (1 - ξ) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have d0 : DifferentiableAt ℝ (fun x => log x) (1 - ξ) := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have d1 : DifferentiableAt ℝ (fun x => log (ξ * x + (1 - ξ))) (1 - ξ) := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have dc2 : DifferentiableAt ℝ (fun _ : ℝ => log (1 - ξ)) (1 - ξ) :=
    differentiableAt_const _
  have dc4 : DifferentiableAt ℝ (fun _ : ℝ => log (1 + ξ)) (1 - ξ) :=
    differentiableAt_const _
  have d5 : DifferentiableAt ℝ (fun x => log (1 - x)) (1 - ξ) := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have d6 : DifferentiableAt ℝ (fun x => log (ξ * x ^ 2 + (1 - ξ) ^ 2)) (1 - ξ) := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have d7 : DifferentiableAt ℝ (fun x => log (ξ * x + (1 - ξ) ^ 2)) (1 - ξ) := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have dc8 : DifferentiableAt ℝ (fun _ : ℝ => log ξ) (1 - ξ) :=
    differentiableAt_const _
  have d9 := i5C1E_dy_9 hξ
  have d12 := i5C1E_dy_12 hξ
  have d13 := i5C1E_dy_13 hξ
  have d14 := i5C1E_dy_14 hξ
  have d19 := i5C1E_dy_19 hξ
  have h := (((((((((((((((((((((((((((d0.mul d1).const_mul 9).add
      ((d0.mul dc2).const_mul (-9))).add ((d0.mul dc4).const_mul (-6))).add
      ((d1.mul d1).const_mul (7 / 2))).add ((d1.mul dc2).const_mul (-11))).add
      ((d1.mul dc4).const_mul (-2))).add ((d1.mul d5).const_mul (-1))).add
      ((d1.mul d6).const_mul (-6))).add ((d1.mul d7).const_mul 1)).add
      ((d1.mul dc8).const_mul 3)).add ((dc2.mul dc2).const_mul (39 / 2))).add
      ((dc2.mul dc4).const_mul 13)).add ((dc2.mul d5).const_mul 2)).add
      ((dc2.mul d6).const_mul (-6))).add ((dc2.mul d7).const_mul (-1))).add
      ((dc2.mul dc8).const_mul (-2))).add ((dc4.mul dc4).const_mul 1)).add
      ((dc4.mul d5).const_mul 2)).add ((dc4.mul d7).const_mul 1)).add
      ((dc4.mul dc8).const_mul (-2))).add ((d6.mul d6).const_mul 3)).add (d9.const_mul 2)).add
      (d12.const_mul 1)).add (d13.const_mul 1)).add (d14.const_mul (-2))).add (d19.const_mul 1))
  exact h

theorem i5C1E_zC1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : i5C1E_C1 ξ (1 - ξ) = 0 := by
  have h1 := (i5C1E_dC1 hξ).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Iio (1 - ξ)))
  rw [tendsto_nhds_unique h1 (i5C1E_tC1 hξ)]
  ring

theorem i5C1E_PB_eqy (ξ x : ℝ) :
    i5C1PB ξ x = i5C1E_Rya ξ x + i5C1E_Ryb ξ x + i5C1E_Ryc ξ x + i5C1E_Ryd ξ x + i5C1E_Rye ξ x +
        i5C1E_Ryf ξ x + i5C1E_Ryg ξ x + i5C1E_Ryh ξ x + log (1 - ξ - x) * i5C1E_C1 ξ x := by
  simp only [i5C1PB, i5C1Q0, i5C1Q1, i5C1Q2, i5C1Q3, i5C1Q4, i5C1Q5, i5C1Q6, i5C1Q7, i5C1Q8,
      i5C1Q9, i5C1Q10, i5C1Q11, i5C1Q12, i5C1Q13, i5C1Q14, i5C1Q15, i5C1Q16, i5C1Q17, i5C1Q18,
      i5C1Q19, i5C1Q20, i5C1Q21, i5C1Q22, i5C1Q23, i5C1Q24, i5C1Q25, i5C1Q26, i5C1Q27, i5C1Q28,
      i5C1Q29, i5C1Q30, i5C1Q31, i5C1Q32, i5C1Q33, i5C1Q34, i5C1Q35, i5C1Q36, i5C1Q37, i5C1Q38,
      i5C1Q39, i5C1Q40, i5C1Q41, i5C1E_Rya, i5C1E_Ryb, i5C1E_Ryc, i5C1E_Ryd, i5C1E_Rye, i5C1E_Ryf,
      i5C1E_Ryg, i5C1E_Ryh, i5C1E_C1]
  ring

/-- **The limit of the primitive at `x = (1 - ξ)⁻`.** -/
theorem tendsto_i5C1PB_sub {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1PB ξ) (𝓝[<] (1 - ξ)) (𝓝 (i5C1E_Vy ξ)) := by
  have hC1 := i5C1E_tendsto_log_mul_y (i5C1E_dC1 hξ) (i5C1E_zC1 hξ)
  have h := (((((((((i5C1E_tRya hξ).add (i5C1E_tRyb hξ)).add (i5C1E_tRyc hξ)).add
      (i5C1E_tRyd hξ)).add (i5C1E_tRye hξ)).add (i5C1E_tRyf hξ)).add (i5C1E_tRyg hξ)).add
      (i5C1E_tRyh hξ))).add hC1
  rw [add_zero] at h
  exact h.congr fun x => (i5C1E_PB_eqy ξ x).symm

end QED.ThreeLoopD
