/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondT2Prim
public import QED.ThreeLoopD.SetDMastersI12RSecondT
public import QED.ThreeLoopD.SetDMastersI12RFirst

/-!
# Set (d), master `I₁₂`: the `θ`-integral of the second derivatives of the face terms

Write `k = 2u / (1 - u)` (`QED.ThreeLoopD.i12Rk`) and `ℓ = log 2`. On the faces `H = 1/2`, and
the pointwise second derivatives `QED.ThreeLoopD.i12Tdd` of the integrands of `T_A`, `T_B` are

  `(4/θ) (h(kθ) - (ℓ + log u) g(kθ))`,   `(4/θ) (h(θ/k) - log (1 - u) g(θ/k))`

with `g = QED.ThreeLoopD.i12Rg`, `h = QED.ThreeLoopD.i12Th`. Both have the shape
`i12Tdd θ H P (rY) Y = (2/(θH)) (h(r) + (λ - 3 log Y - 2 log r) g(r))`. With the antiderivatives
`Hh` of `h(r)/r` and `Φ` of `g(r)/r`, both vanishing at `0⁺`, the `θ`-integral of their sum is

  `4 (Hh(k) + Hh(1/k) - (ℓ + log u) Φ(k) - log (1 - u) Φ(1/k))`.

## Main results

* `QED.ThreeLoopD.i12Tdd_TA_eq`, `QED.ThreeLoopD.i12Tdd_TB_eq`.
* `QED.ThreeLoopD.integral_i12T2In`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The generic face value with `X = rY`. -/
theorem i12Tdd_mul_left {θ H P Y r : ℝ} (hθ : 0 < θ) (hH : 0 < H) (hY : 0 < Y) (hr : 0 < r) :
    i12Tdd θ H P (r * Y) Y =
      2 / (θ * H) * (i12Th r + (i12Lam θ H P - 3 * log Y - 2 * log r) * i12Rg r) := by
  have h1 : 0 < 1 + r := by linarith
  rw [i12Tdd, i12Th, i12Rg, show r * Y + Y = (1 + r) * Y by ring, log_mul h1.ne' hY.ne',
    log_mul hr.ne' hY.ne']
  generalize i12Lam θ H P = Λ
  generalize log Y = lY
  generalize log r = l
  generalize log (1 + r) = L
  field_simp
  ring

/-- **The face value of `T_A''`.** -/
theorem i12Tdd_TA_eq {θ u : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i12Tdd θ (i12H 0) (u * (1 - u)) (u * θ) ((1 - u) * i12H 0) =
      4 / θ * (i12Th (i12Rk u * θ) - (log 2 + log u) * i12Rg (i12Rk u * θ)) := by
  obtain ⟨hθ0, -⟩ := hθ
  obtain ⟨hu0, hu1⟩ := hu
  have h1u : 0 < 1 - u := by linarith
  have hk := i12Rk_pos ⟨hu0, hu1⟩
  rw [i12H_zero, show u * θ = i12Rk u * θ * ((1 - u) * (1 / 2)) by
    unfold i12Rk; field_simp]
  rw [i12Tdd_mul_left hθ0 (by norm_num) (by positivity) (by positivity)]
  have e1 : log (i12Rk u * θ) = log 2 + log u - log (1 - u) + log θ := by
    unfold i12Rk
    rw [log_mul (by positivity) hθ0.ne', log_div (by positivity) h1u.ne',
      log_mul (by norm_num) hu0.ne']
  have e2 : log ((1 - u) * (1 / 2)) = log (1 - u) - log 2 := by
    rw [log_mul h1u.ne' (by norm_num), one_div, log_inv]
    ring
  rw [i12Lam, e1, e2, log_mul hu0.ne' h1u.ne', one_div, log_inv]
  field_simp
  ring

/-- **The face value of `T_B''`.** -/
theorem i12Tdd_TB_eq {θ u : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i12Tdd θ (i12H 0) (u * (1 - u)) ((1 - u) * θ * i12H 0) u =
      4 / θ * (i12Th (θ / i12Rk u) - log (1 - u) * i12Rg (θ / i12Rk u)) := by
  obtain ⟨hθ0, -⟩ := hθ
  obtain ⟨hu0, hu1⟩ := hu
  have h1u : 0 < 1 - u := by linarith
  have hk := i12Rk_pos ⟨hu0, hu1⟩
  rw [i12H_zero, show (1 - u) * θ * (1 / 2) = θ / i12Rk u * u by
    unfold i12Rk; field_simp]
  rw [i12Tdd_mul_left hθ0 (by norm_num) hu0 (by positivity)]
  have e1 : log (θ / i12Rk u) = log θ - log 2 - log u + log (1 - u) := by
    unfold i12Rk
    rw [log_div hθ0.ne' (by positivity), log_div (by positivity) h1u.ne',
      log_mul (by norm_num) hu0.ne']
    ring
  rw [i12Lam, e1, log_mul hu0.ne' h1u.ne', one_div, log_inv]
  field_simp
  ring

/-- The `θ`-integrand of `T_A''(0) + T_B''(0)` at fixed `u`. -/
noncomputable def i12T2In (u θ : ℝ) : ℝ :=
  4 / θ * (i12Th (i12Rk u * θ) - (log 2 + log u) * i12Rg (i12Rk u * θ)) +
    4 / θ * (i12Th (θ / i12Rk u) - log (1 - u) * i12Rg (θ / i12Rk u))

/-- The value of the `θ`-integral at fixed `u`. -/
noncomputable def i12T2Out (u : ℝ) : ℝ :=
  4 * (i12ThPrim (i12Rk u) + i12ThPrim (1 / i12Rk u) - (log 2 + log u) * i12RPhi (i12Rk u) -
    log (1 - u) * i12RPhi (1 / i12Rk u))

/-- **The `θ`-integral at fixed `u`**, given integrability. -/
theorem integral_i12T2In {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hint : IntervalIntegrable (i12T2In u) volume 0 1) :
    ∫ θ in (0 : ℝ)..1, i12T2In u θ = i12T2Out u := by
  have hk := i12Rk_pos hu
  set k := i12Rk u with hkdef
  set c₁ := log 2 + log u
  set c₂ := log (1 - u)
  set F : ℝ → ℝ := fun θ => 4 * (i12ThPrim (k * θ) + i12ThPrim (θ / k) -
    c₁ * i12RPhi (k * θ) - c₂ * i12RPhi (θ / k)) with hF
  have hd : ∀ θ : ℝ, 0 < θ → HasDerivAt F (i12T2In u θ) θ := by
    intro θ hθ
    have hA := (hasDerivAt_i12ThPrim (mul_pos hk hθ)).comp θ ((hasDerivAt_id' θ).const_mul k)
    have hB := (hasDerivAt_i12ThPrim (div_pos hθ hk)).comp θ ((hasDerivAt_id' θ).div_const k)
    have hC := (hasDerivAt_i12RPhi (mul_pos hk hθ)).comp θ ((hasDerivAt_id' θ).const_mul k)
    have hD := (hasDerivAt_i12RPhi (div_pos hθ hk)).comp θ ((hasDerivAt_id' θ).div_const k)
    refine ((((hA.add hB).sub (hC.const_mul c₁)).sub (hD.const_mul c₂)).const_mul 4).congr_deriv
      ?_
    simp only [i12T2In, ← hkdef]
    field_simp
    ring
  have hmapA : Tendsto (fun θ : ℝ => k * θ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_const_mul k).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with θ (hθ : 0 < θ)
      exact mul_pos hk hθ
  have hmapB : Tendsto (fun θ : ℝ => θ / k) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_id.div_const k).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with θ (hθ : 0 < θ)
      exact div_pos hθ hk
  have h0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have := ((((tendsto_i12ThPrim_zero.comp hmapA).add (tendsto_i12ThPrim_zero.comp hmapB)).sub
      ((tendsto_i12RPhi_zero.comp hmapA).const_mul c₁)).sub
      ((tendsto_i12RPhi_zero.comp hmapB).const_mul c₂)).const_mul 4
    simpa using this
  have h1 : Tendsto F (𝓝[<] 1) (𝓝 (F 1)) :=
    (hd 1 one_pos).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun θ hθ => hd θ hθ.1) hint h0 h1, hF]
  simp only [mul_one, sub_zero, i12T2Out, ← hkdef]
  rfl

end QED.ThreeLoopD
