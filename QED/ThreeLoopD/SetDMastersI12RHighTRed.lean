/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighTPt
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Set (d), master `I₁₂`: the face terms of all orders as one-dimensional integrals

For every `N`, the sum of the two face integrals `∫∫ i12TAd N + ∫∫ i12TBd N` over `(0, 1)²`
(which is `T_A⁽ᴺ⁾(0) + T_B⁽ᴺ⁾(0)`, `QED.ThreeLoopD.iteratedDeriv_i12TA_eq_integral`) equals
`∫₀¹ J_N(s) ds`, where `J_N` (`QED.ThreeLoopD.i12TJ`) is a polynomial in `log s`,
`log (1 - s)`, `log (1 + s)`, `log 2` with rational coefficients:

  `J_N(s) = 2/(s(1 - s)) (E_N[e_A](k) + E_N[e_B](1/k))`,   `k = 2s/(1 - s)`,

  `E_N[e](r) = (1 + r)²/r e_N(2 log r - 3 log (1 + r)) - r e_N(-log r)`
    `- (1/r + 2) e_N(2 log r) + 3N e_{N-1}(2 log r)`   (`QED.ThreeLoopD.i12TE`),

  `e_A,N(X) = P_N(X - log 2) - s P_N(X - log 2 - log s)`   (`QED.ThreeLoopD.i12TeA`),
  `e_B,N(X) = P_N(X) - (1 - s) P_N(X - log (1 - s))`   (`QED.ThreeLoopD.i12TeB`).

## Proof

By `QED.ThreeLoopD.i12TAd_eq`, at fixed `t` the face integrand of `T_A` is
`(2/θ) f_N(k(t)θ; c_A(t))`, `c_A(t) = -log 2 - log t`. The substitution `θ = k(s)/k(t)`,
`s ∈ (0, t)`, has `dθ/θ = ds/(s(1 - s))`, so the `θ`-slice equals the `s`-slice over `(0, t)` of
`g_A(s, t) = 2 f_N(k(s); c_A(t))/(s(1 - s))` (with absolute values too, by the one-dimensional
change of variables `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`). Hence `g_A`
restricted to the triangle `s < t` is integrable on `(0, 1)²` (`MeasureTheory.integrable_prod_iff'`)
with the same integral, and Fubini in the other order integrates out `t ∈ (s, 1)`, which by the
logarithmic moments `QED.ThreeLoopD.integral_Ioo_sub_log_pow` gives `2 E_N[e_A](k(s))/(s(1-s))`.
`T_B` is the same with `θ = k(t)/k(s)`, `s ∈ (t, 1)`, `c_B(t) = -log (1 - t)` and
`QED.ThreeLoopD.integral_Ioo_sub_log_one_sub_pow`. No bound on the integrands is needed: every
integrability statement is transported from that of the two-dimensional face integrands.

## Main results

* `QED.ThreeLoopD.i12T_slice`, `QED.ThreeLoopD.i12T_transfer`: the slice change of variables
  and the transfer of integrability and integral to the triangle.
* `QED.ThreeLoopD.integral_i12TAd_add_integral_i12TBd`: the reduction, for every `N`.
* `QED.ThreeLoopD.iteratedDeriv_i12TA_add_i12TB_eq_integral_i12TJ`:
  `T_A⁽ᴺ⁾(0) + T_B⁽ᴺ⁾(0) = ∫₀¹ J_N`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.ThreeLoopD

/-! ### The one-dimensional integrand -/

/-- `e_A,N(X) = ∫_s^1 (X - log 2 - log t)ᴺ dt`. -/
noncomputable def i12TeA (s : ℝ) (N : ℕ) (X : ℝ) : ℝ :=
  i12TPn N (X - log 2) - s * i12TPn N (X - log 2 - log s)

/-- `e_B,N(X) = ∫_0^s (X - log (1 - t))ᴺ dt`. -/
noncomputable def i12TeB (s : ℝ) (N : ℕ) (X : ℝ) : ℝ :=
  i12TPn N X - (1 - s) * i12TPn N (X - log (1 - s))

/-- `E_N[e](r)`: `f_N(r; c)` with each power `(c + X)ᴹ` replaced by `e_M(X)`. -/
noncomputable def i12TE (e : ℕ → ℝ → ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  (1 + r) ^ 2 / r * e N (2 * log r - 3 * log (1 + r)) - r * e N (-log r) -
    (1 / r + 2) * e N (2 * log r) + 3 * N * e (N - 1) (2 * log r)

/-- **The one-dimensional integrand `J_N(s)` of the face terms of order `N`.** -/
noncomputable def i12TJ (N : ℕ) (s : ℝ) : ℝ :=
  2 / (s * (1 - s)) * (i12TE (i12TeA s) N (i12Rk s) + i12TE (i12TeB s) N (1 / i12Rk s))

/-- Integrating `f_N(r; c₀ - φ(t))` in `t`, given the moments of `φ`. -/
theorem i12Tf_integral_gen (N : ℕ) (r c₀ : ℝ) {A : Set ℝ} {φ : ℝ → ℝ} {e : ℕ → ℝ → ℝ}
    (he : ∀ (M : ℕ) (X : ℝ), IntegrableOn (fun t => (X + c₀ - φ t) ^ M) A ∧
      ∫ t in A, (X + c₀ - φ t) ^ M = e M X) :
    IntegrableOn (fun t => i12Tf N (c₀ - φ t) r) A ∧
      ∫ t in A, i12Tf N (c₀ - φ t) r = i12TE e N r := by
  have hpt : (fun t => i12Tf N (c₀ - φ t) r) = fun t =>
      (1 + r) ^ 2 / r * (2 * log r - 3 * log (1 + r) + c₀ - φ t) ^ N -
        r * (-log r + c₀ - φ t) ^ N - (1 / r + 2) * (2 * log r + c₀ - φ t) ^ N +
        3 * N * (2 * log r + c₀ - φ t) ^ (N - 1) := by
    funext t
    unfold i12Tf
    rw [show c₀ - φ t + 2 * log r - 3 * log (1 + r) =
        2 * log r - 3 * log (1 + r) + c₀ - φ t by ring,
      show c₀ - φ t - log r = -log r + c₀ - φ t by ring,
      show c₀ - φ t + 2 * log r = 2 * log r + c₀ - φ t by ring]
  obtain ⟨i1, v1⟩ := he N (2 * log r - 3 * log (1 + r))
  obtain ⟨i2, v2⟩ := he N (-log r)
  obtain ⟨i3, v3⟩ := he N (2 * log r)
  obtain ⟨i4, v4⟩ := he (N - 1) (2 * log r)
  have hi := (((i1.const_mul ((1 + r) ^ 2 / r)).sub (i2.const_mul r)).sub
    (i3.const_mul (1 / r + 2))).add (i4.const_mul (3 * N))
  rw [hpt]
  refine ⟨hi, ?_⟩
  rw [integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, v1, v2, v3, v4]
  all_goals first
    | rfl
    | exact i1.const_mul _ | exact i2.const_mul _ | exact i3.const_mul _
    | exact i4.const_mul _ | exact (i1.const_mul _).sub (i2.const_mul _)
    | exact ((i1.const_mul _).sub (i2.const_mul _)).sub (i3.const_mul _)

/-- The `t`-integral of the `T_A` integrand over `(s, 1)`. -/
theorem i12Tf_integral_A (N : ℕ) (r : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun t => i12Tf N (-log 2 - log t) r) (Ioo s 1) ∧
      ∫ t in Ioo s 1, i12Tf N (-log 2 - log t) r = i12TE (i12TeA s) N r :=
  i12Tf_integral_gen N r (-log 2) fun M X => by
    simp only [← sub_eq_add_neg]
    exact integral_Ioo_sub_log_pow M (X - log 2) hs.1 hs.2

/-- The `t`-integral of the `T_B` integrand over `(0, s)`. -/
theorem i12Tf_integral_B (N : ℕ) (r : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun t => i12Tf N (-log (1 - t)) r) (Ioo 0 s) ∧
      ∫ t in Ioo 0 s, i12Tf N (-log (1 - t)) r = i12TE (i12TeB s) N r := by
  have h := i12Tf_integral_gen N r 0 (A := Ioo 0 s) (φ := fun t => log (1 - t))
    (e := i12TeB s) fun M X => by
      simp only [add_zero]
      exact integral_Ioo_sub_log_one_sub_pow M X hs.1 hs.2
  simpa only [zero_sub] using h

/-! ### Change of variables in a slice, and transfer to the triangle -/

/-- **The slice change of variables**: a diffeomorphism `σ` of `(a, b)` onto `(0, 1)` with
`|σ'| · h ∘ σ = g` transports integrability, the integral and the integral of the norm. -/
theorem i12T_slice {a b : ℝ} {σ σ' h g : ℝ → ℝ} (hσ : ∀ s ∈ Ioo a b, HasDerivAt σ (σ' s) s)
    (hinj : InjOn σ (Ioo a b)) (himg : σ '' Ioo a b = Ioo 0 1)
    (hg : ∀ s ∈ Ioo a b, |σ' s| * h (σ s) = g s) :
    (IntegrableOn h (Ioo 0 1) ↔ IntegrableOn g (Ioo a b)) ∧
      ∫ θ in Ioo 0 1, h θ = ∫ s in Ioo a b, g s ∧
      ∫ θ in Ioo 0 1, ‖h θ‖ = ∫ s in Ioo a b, ‖g s‖ := by
  have hd : ∀ s ∈ Ioo a b, HasDerivWithinAt σ (σ' s) (Ioo a b) s :=
    fun s hs => (hσ s hs).hasDerivWithinAt
  refine ⟨?_, ?_, ?_⟩
  · rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj]
    exact integrableOn_congr_fun (fun s hs => by simpa [smul_eq_mul] using hg s hs)
      measurableSet_Ioo
  · rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj]
    exact setIntegral_congr_fun measurableSet_Ioo fun s hs => by
      simpa [smul_eq_mul] using hg s hs
  · rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    rw [← hg s hs, smul_eq_mul, norm_mul, Real.norm_eq_abs |σ' s|, abs_abs]

/-- Extension by zero from `B = A ∩ (0, 1)` to `(0, 1)`. -/
theorem i12T_indicator {A B : Set ℝ} (hA : MeasurableSet A) (hB : A ∩ Ioo 0 1 = B)
    {g : ℝ → ℝ} (hg : IntegrableOn g B) :
    IntegrableOn (A.indicator g) (Ioo 0 1) ∧
      ∫ s in Ioo 0 1, A.indicator g s = ∫ s in B, g s ∧
      ∫ s in Ioo 0 1, ‖A.indicator g s‖ = ∫ s in B, ‖g s‖ := by
  refine ⟨?_, ?_, ?_⟩
  · refine (integrable_indicator_iff hA).2 ?_
    rw [IntegrableOn, Measure.restrict_restrict hA, hB]
    exact hg
  · rw [setIntegral_indicator hA, inter_comm, hB]
  · simp_rw [norm_indicator_eq_indicator_norm]
    rw [setIntegral_indicator hA, inter_comm, hB]

/-- **Transfer to the triangle**: if the slices of `G` match those of an integrable `F`
(integrability, integral and integral of the norm), then `G` is integrable with the same
integral. -/
theorem i12T_transfer {F G : ℝ × ℝ → ℝ}
    (hF : Integrable F ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))))
    (hG : AEStronglyMeasurable G
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))))
    (hsl : ∀ t ∈ Ioo (0 : ℝ) 1, IntegrableOn (fun θ => F (θ, t)) (Ioo 0 1) →
      IntegrableOn (fun s => G (s, t)) (Ioo 0 1) ∧
        ∫ s in Ioo 0 1, G (s, t) = ∫ θ in Ioo 0 1, F (θ, t) ∧
        ∫ s in Ioo 0 1, ‖G (s, t)‖ = ∫ θ in Ioo 0 1, ‖F (θ, t)‖) :
    Integrable G ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) ∧
      ∫ z, G z ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) =
        ∫ z, F z ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      t ∈ Ioo (0 : ℝ) 1 ∧ IntegrableOn (fun θ => F (θ, t)) (Ioo 0 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hF.prod_left_ae] with t ht hi
    exact ⟨ht, hi⟩
  have hGi : Integrable G
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    refine (integrable_prod_iff' hG).2 ⟨?_, ?_⟩
    · filter_upwards [hae] with t ht
      exact (hsl t ht.1 ht.2).1
    · refine hF.integral_norm_prod_right.congr ?_
      filter_upwards [hae] with t ht
      exact ((hsl t ht.1 ht.2).2.2).symm
  refine ⟨hGi, ?_⟩
  rw [integral_prod_symm G hGi, integral_prod_symm F hF]
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  exact (hsl t ht.1 ht.2).2.1

/-! ### The two triangles -/

/-- `g_A(s, t) = 2 f_N(k(s); -log 2 - log t) / (s(1 - s))`. -/
noncomputable def i12TgA (N : ℕ) (s t : ℝ) : ℝ :=
  2 / (s * (1 - s)) * i12Tf N (-log 2 - log t) (i12Rk s)

/-- `g_B(s, t) = 2 f_N(1/k(s); -log (1 - t)) / (s(1 - s))`. -/
noncomputable def i12TgB (N : ℕ) (s t : ℝ) : ℝ :=
  2 / (s * (1 - s)) * i12Tf N (-log (1 - t)) (1 / i12Rk s)

/-- `g_A` on the triangle `s < t`, zero elsewhere. -/
noncomputable def i12TGA (N : ℕ) (z : ℝ × ℝ) : ℝ := if z.1 < z.2 then i12TgA N z.1 z.2 else 0

/-- `g_B` on the triangle `t < s`, zero elsewhere. -/
noncomputable def i12TGB (N : ℕ) (z : ℝ × ℝ) : ℝ := if z.2 < z.1 then i12TgB N z.1 z.2 else 0

theorem measurable_i12TGA (N : ℕ) : Measurable (i12TGA N) := by
  unfold i12TGA i12TgA i12Tf i12Rk
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) (by fun_prop)
    measurable_const

theorem measurable_i12TGB (N : ℕ) : Measurable (i12TGB N) := by
  unfold i12TGB i12TgB i12Tf i12Rk
  exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst) (by fun_prop)
    measurable_const

/-- The `θ`-slice of `T_A` at `t` is the `s`-slice of `G_A`. -/
theorem i12T_sliceA (N : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hi : IntegrableOn (fun θ => i12TAd N θ t) (Ioo 0 1)) :
    IntegrableOn (fun s => i12TGA N (s, t)) (Ioo 0 1) ∧
      ∫ s in Ioo 0 1, i12TGA N (s, t) = ∫ θ in Ioo 0 1, i12TAd N θ t ∧
      ∫ s in Ioo 0 1, ‖i12TGA N (s, t)‖ = ∫ θ in Ioo 0 1, ‖i12TAd N θ t‖ := by
  obtain ⟨ht0, ht1⟩ := ht
  have h1t : 0 < 1 - t := by linarith
  have hsl := i12T_slice (a := 0) (b := t) (σ := fun s => s * (1 - t) / (t * (1 - s)))
    (σ' := fun s => (1 - t) / (t * (1 - s) ^ 2)) (h := fun θ => i12TAd N θ t)
    (g := fun s => i12TgA N s t)
    (fun s hs => by
      have h1s : 1 - s ≠ 0 := by linarith [hs.2]
      have := ((hasDerivAt_id' s).mul_const (1 - t)).div
        (((hasDerivAt_id' s).const_sub 1).const_mul t) (mul_ne_zero ht0.ne' h1s)
      refine this.congr_deriv ?_
      field_simp
      ring)
    (fun s₁ hs₁ s₂ hs₂ he => by
      have h1 : 1 - s₁ ≠ 0 := by linarith [hs₁.2]
      have h2 : 1 - s₂ ≠ 0 := by linarith [hs₂.2]
      simp only at he
      field_simp at he
      linarith)
    (by
      ext θ
      simp only [mem_image, mem_Ioo]
      constructor
      · rintro ⟨s, ⟨hs0, hst⟩, rfl⟩
        have h1s : 0 < 1 - s := by linarith
        refine ⟨by positivity, ?_⟩
        rw [div_lt_one (by positivity)]
        nlinarith
      · rintro ⟨hθ0, hθ1⟩
        have hd : 0 < 1 - t + θ * t := by nlinarith
        refine ⟨θ * t / (1 - t + θ * t), ⟨by positivity, ?_⟩, ?_⟩
        · rw [div_lt_iff₀ hd]; nlinarith [mul_pos (mul_pos ht0 h1t) (sub_pos.2 hθ1)]
        · have : 1 - θ * t / (1 - t + θ * t) = (1 - t) / (1 - t + θ * t) := by
            field_simp; ring
          rw [this]
          field_simp)
    (fun s hs => by
      obtain ⟨hs0, hst⟩ := hs
      have h1s : 0 < 1 - s := by linarith
      have hσ : s * (1 - t) / (t * (1 - s)) ∈ Ioo (0 : ℝ) 1 := by
        refine ⟨by positivity, ?_⟩
        rw [div_lt_one (by positivity)]
        nlinarith
      rw [abs_of_pos (by positivity), i12TAd_eq N hσ ⟨ht0, ht1⟩, i12TgA]
      have hk : i12Rk t * (s * (1 - t) / (t * (1 - s))) = i12Rk s := by
        unfold i12Rk; field_simp
      rw [hk]
      field_simp)
  have hB : Iio t ∩ Ioo 0 1 = Ioo 0 t := by
    ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  have hfun : (fun s => i12TGA N (s, t)) = (Iio t).indicator (fun s => i12TgA N s t) := by
    funext s
    simp [i12TGA, indicator_apply]
  obtain ⟨i1, v1, n1⟩ := i12T_indicator measurableSet_Iio hB (hsl.1.1 hi)
  rw [hfun]
  exact ⟨i1, v1.trans hsl.2.1.symm, n1.trans hsl.2.2.symm⟩

/-- The `θ`-slice of `T_B` at `t` is the `s`-slice of `G_B`. -/
theorem i12T_sliceB (N : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hi : IntegrableOn (fun θ => i12TBd N θ t) (Ioo 0 1)) :
    IntegrableOn (fun s => i12TGB N (s, t)) (Ioo 0 1) ∧
      ∫ s in Ioo 0 1, i12TGB N (s, t) = ∫ θ in Ioo 0 1, i12TBd N θ t ∧
      ∫ s in Ioo 0 1, ‖i12TGB N (s, t)‖ = ∫ θ in Ioo 0 1, ‖i12TBd N θ t‖ := by
  obtain ⟨ht0, ht1⟩ := ht
  have h1t : 0 < 1 - t := by linarith
  have hsl := i12T_slice (a := t) (b := 1) (σ := fun s => t * (1 - s) / (s * (1 - t)))
    (σ' := fun s => -(t / ((1 - t) * s ^ 2))) (h := fun θ => i12TBd N θ t)
    (g := fun s => i12TgB N s t)
    (fun s hs => by
      have hs0 : s ≠ 0 := by linarith [hs.1]
      have := (((hasDerivAt_id' s).const_sub 1).const_mul t).div
        ((hasDerivAt_id' s).mul_const (1 - t)) (mul_ne_zero hs0 h1t.ne')
      refine this.congr_deriv ?_
      field_simp
      ring)
    (fun s₁ hs₁ s₂ hs₂ he => by
      have h1 : s₁ ≠ 0 := by linarith [hs₁.1]
      have h2 : s₂ ≠ 0 := by linarith [hs₂.1]
      simp only at he
      field_simp at he
      linarith)
    (by
      ext θ
      simp only [mem_image, mem_Ioo]
      constructor
      · rintro ⟨s, ⟨hts, hs1⟩, rfl⟩
        have hs0 : 0 < s := by linarith
        have h1s : 0 < 1 - s := by linarith
        refine ⟨by positivity, ?_⟩
        rw [div_lt_one (by positivity)]
        nlinarith
      · rintro ⟨hθ0, hθ1⟩
        have hd : 0 < t + θ * (1 - t) := by nlinarith
        refine ⟨t / (t + θ * (1 - t)), ⟨?_, ?_⟩, ?_⟩
        · rw [lt_div_iff₀ hd]; nlinarith [mul_pos (mul_pos ht0 h1t) (sub_pos.2 hθ1)]
        · rw [div_lt_one hd]; nlinarith
        · have : 1 - t / (t + θ * (1 - t)) = θ * (1 - t) / (t + θ * (1 - t)) := by
            field_simp; ring
          rw [this]
          field_simp)
    (fun s hs => by
      obtain ⟨hts, hs1⟩ := hs
      have hs0 : 0 < s := by linarith
      have h1s : 0 < 1 - s := by linarith
      have hσ : t * (1 - s) / (s * (1 - t)) ∈ Ioo (0 : ℝ) 1 := by
        refine ⟨by positivity, ?_⟩
        rw [div_lt_one (by positivity)]
        nlinarith
      rw [abs_neg, abs_of_pos (by positivity), i12TBd_eq N hσ ⟨ht0, ht1⟩, i12TgB]
      have hk : t * (1 - s) / (s * (1 - t)) / i12Rk t = 1 / i12Rk s := by
        unfold i12Rk; field_simp
      rw [hk]
      field_simp)
  have hB : Ioi t ∩ Ioo 0 1 = Ioo t 1 := by
    ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  have hfun : (fun s => i12TGB N (s, t)) = (Ioi t).indicator (fun s => i12TgB N s t) := by
    funext s
    simp [i12TGB, indicator_apply]
  obtain ⟨i1, v1, n1⟩ := i12T_indicator measurableSet_Ioi hB (hsl.1.1 hi)
  rw [hfun]
  exact ⟨i1, v1.trans hsl.2.1.symm, n1.trans hsl.2.2.symm⟩

/-- The `t`-slice of `G_A` at `s`. -/
theorem integral_i12TGA_slice (N : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∫ t in Ioo 0 1, i12TGA N (s, t) =
      2 / (s * (1 - s)) * i12TE (i12TeA s) N (i12Rk s) := by
  have hB : Ioi s ∩ Ioo 0 1 = Ioo s 1 := by
    ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [hs.1], h2⟩
  have hfun : (fun t => i12TGA N (s, t)) = (Ioi s).indicator (fun t => i12TgA N s t) := by
    funext t
    simp [i12TGA, indicator_apply]
  obtain ⟨hi, hv⟩ := i12Tf_integral_A N (i12Rk s) hs
  rw [hfun, (i12T_indicator (g := fun t => i12TgA N s t) measurableSet_Ioi hB
    (hi.const_mul (2 / (s * (1 - s))))).2.1]
  simp only [i12TgA]
  rw [integral_const_mul, hv]

/-- The `t`-slice of `G_B` at `s`. -/
theorem integral_i12TGB_slice (N : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∫ t in Ioo 0 1, i12TGB N (s, t) =
      2 / (s * (1 - s)) * i12TE (i12TeB s) N (1 / i12Rk s) := by
  have hB : Iio s ∩ Ioo 0 1 = Ioo 0 s := by
    ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [hs.2]⟩
  have hfun : (fun t => i12TGB N (s, t)) = (Iio s).indicator (fun t => i12TgB N s t) := by
    funext t
    simp [i12TGB, indicator_apply]
  obtain ⟨hi, hv⟩ := i12Tf_integral_B N (1 / i12Rk s) hs
  rw [hfun, (i12T_indicator (g := fun t => i12TgB N s t) measurableSet_Iio hB
    (hi.const_mul (2 / (s * (1 - s))))).2.1]
  simp only [i12TgB]
  rw [integral_const_mul, hv]

/-! ### The reduction -/

/-- **The face terms of order `N` as a one-dimensional integral**:
`∫∫ i12TAd N + ∫∫ i12TBd N = ∫₀¹ J_N`, with `J_N` integrable on `(0, 1)`. -/
theorem integral_i12TAd_add_integral_i12TBd (N : ℕ) :
    IntegrableOn (i12TJ N) (Ioo 0 1) ∧
      (∫ z in i12Sq, (i12TAd N z.1 z.2 : ℂ)) + ∫ z in i12Sq, (i12TBd N z.1 z.2 : ℂ) =
        ((∫ s in Ioo (0 : ℝ) 1, i12TJ N s : ℝ) : ℂ) := by
  obtain ⟨hA, -⟩ := iteratedDeriv_i12TA_eq_integral N
  obtain ⟨hB, -⟩ := iteratedDeriv_i12TB_eq_integral N
  have e2 := volume_restrict_prod2 (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1)
  have hAr : Integrable (fun z : ℝ × ℝ => i12TAd N z.1 z.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [← e2]; simpa using hA.re
  have hBr : Integrable (fun z : ℝ × ℝ => i12TBd N z.1 z.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [← e2]; simpa using hB.re
  obtain ⟨hGA, eA⟩ := i12T_transfer hAr (measurable_i12TGA N).aestronglyMeasurable
    fun t ht hi => i12T_sliceA N ht hi
  obtain ⟨hGB, eB⟩ := i12T_transfer hBr (measurable_i12TGB N).aestronglyMeasurable
    fun t ht hi => i12T_sliceB N ht hi
  have hJ : ∀ s ∈ Ioo (0 : ℝ) 1, (∫ t in Ioo 0 1, i12TGA N (s, t)) +
      ∫ t in Ioo 0 1, i12TGB N (s, t) = i12TJ N s := fun s hs => by
    rw [integral_i12TGA_slice N hs, integral_i12TGB_slice N hs, i12TJ]
    ring
  have hint := hGA.integral_prod_left.add hGB.integral_prod_left
  refine ⟨hint.congr (ae_restrict_of_forall_mem measurableSet_Ioo hJ), ?_⟩
  rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_add]
  congr 1
  rw [e2, ← eA, ← eB, integral_prod _ hGA, integral_prod _ hGB,
    ← integral_add hGA.integral_prod_left hGB.integral_prod_left]
  exact setIntegral_congr_fun measurableSet_Ioo hJ

/-- **`T_A⁽ᴺ⁾(0) + T_B⁽ᴺ⁾(0) = ∫₀¹ J_N`.** -/
theorem iteratedDeriv_i12TA_add_i12TB_eq_integral_i12TJ (N : ℕ) :
    iteratedDeriv N i12TA 0 + iteratedDeriv N i12TB 0 =
      ((∫ s in Ioo (0 : ℝ) 1, i12TJ N s : ℝ) : ℂ) := by
  rw [(iteratedDeriv_i12TA_eq_integral N).2, (iteratedDeriv_i12TB_eq_integral N).2]
  exact (integral_i12TAd_add_integral_i12TBd N).2

end QED.ThreeLoopD
