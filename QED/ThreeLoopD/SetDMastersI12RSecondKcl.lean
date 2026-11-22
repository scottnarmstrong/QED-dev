/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondK
import QED.Polylog.Deriv
import QED.Polylog.ExtraIntegrals
import QED.Polylog.Reflection

/-!
# Set (d), master `I₁₂`: the closed form of `K` on `(0, 1)`

For `0 < m < 1` the weight-two function `K(m) = ∫₀¹ Φ(m u / (1 - u)) du`
(`QED.ThreeLoopD.i12RK`) is

  `K(m) = -3 + 3 log m - (3m/2) log² m - m π² + 3 ((1 - m)² / m) (log m log (1 - m) + Li₂ m)`.

**Proof.** With `a = 1 - m`, `D = 1 - a u` and `r = m u / (1 - u)` we have `1 + r = D / (1 - u)`
and `r' / r = 1 / (u (1 - u))`, so `(u - 1) Φ(r)` has derivative `Φ(r) - g(r) / u`. The function
`g(r) / u` is elementary in the letters `u, 1 - u, D`, with the antiderivative
(`QED.ThreeLoopD.i12RKH`)

  `H(u) = (3/m) (log D - log (1 - u)) / u - (3a/m) log D + (3/m) log (1 - u)
      - (3/m) (2m - 1) (Li₂ u - Li₂ (a u)) + 3m (Li₂ (1 - u) + Li₂ (a (1 - u) / D)
      + (log D - log m)² / 2)`;

all four `Li₂` arguments lie in `(0, 1)`. The limits `H(0⁺) = 3 + 3m (π²/6 + Li₂ a + log² m / 2)`
and `H(1⁻) = 3 log m - (3/m) (2m - 1) (π²/6 - Li₂ a)`, and the reflection
`Li₂ a + Li₂ m = π²/6 - log m log a`, give the closed form.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i12RKH`, `QED.ThreeLoopD.hasDerivAt_i12RKPrim`.
* `QED.ThreeLoopD.i12RK_eq`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The antiderivative of `g(m u / (1 - u)) / u` on `(0, 1)`. -/
noncomputable def i12RKH (m u : ℝ) : ℝ :=
  3 / m * ((log (1 - (1 - m) * u) - log (1 - u)) / u) -
    3 * (1 - m) / m * log (1 - (1 - m) * u) + 3 / m * log (1 - u) -
    3 / m * (2 * m - 1) * (Li₂ u - Li₂ ((1 - m) * u)) +
    3 * m * (Li₂ (1 - u) + Li₂ ((1 - m) * (1 - u) / (1 - (1 - m) * u)) +
      (log (1 - (1 - m) * u) - log m) ^ 2 / 2)

/-- The antiderivative of the integrand of `K(m)` on `(0, 1)`. -/
noncomputable def i12RKPrim (m u : ℝ) : ℝ :=
  (u - 1) * i12RPhi (m * u / (1 - u)) + i12RKH m u

/-- The closed form of `K` on `(0, 1)`. -/
noncomputable def i12RKcl (m : ℝ) : ℝ :=
  -3 + 3 * log m - 3 * m / 2 * log m ^ 2 - m * π ^ 2 +
    3 * ((1 - m) ^ 2 / m) * (log m * log (1 - m) + Li₂ m)

theorem i12RK_mem {m u : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < 1 - (1 - m) * u ∧ (1 - m) * u ∈ Ioo (0 : ℝ) 1 ∧
      (1 - m) * (1 - u) / (1 - (1 - m) * u) ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨hm0, hm1⟩ := hm
  obtain ⟨hu0, hu1⟩ := hu
  have ha : 0 < 1 - m := by linarith
  have hau : (1 - m) * u < 1 - m := mul_lt_of_lt_one_right ha hu1
  have hD : 0 < 1 - (1 - m) * u := by linarith
  refine ⟨hD, ⟨mul_pos ha hu0, by linarith⟩, div_pos (mul_pos ha (by linarith)) hD, ?_⟩
  rw [div_lt_one hD]
  nlinarith

theorem hasDerivAt_i12RKH {m u : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i12RKH m) (i12Rg (m * u / (1 - u)) / u) u := by
  obtain ⟨hD, hau, hq⟩ := i12RK_mem hm hu
  obtain ⟨hm0, hm1⟩ := hm
  obtain ⟨hu0, hu1⟩ := hu
  have h1u : 0 < 1 - u := by linarith
  have hi := hasDerivAt_id u
  have hDd : HasDerivAt (fun u => 1 - (1 - m) * u) (-(1 - m)) u := by
    simpa using (hi.const_mul (1 - m)).const_sub 1
  have h1d : HasDerivAt (fun u : ℝ => 1 - u) (-1) u := by simpa using hi.const_sub 1
  have hlD := hDd.log hD.ne'
  have hl1 := h1d.log h1u.ne'
  have hLu := hasDerivAt_Li₂' ⟨hu0, hu1⟩
  have hLau := (hasDerivAt_Li₂' hau).comp u (by simpa using hi.const_mul (1 - m) :
    HasDerivAt (fun u : ℝ => (1 - m) * u) (1 - m) u)
  have hL1u := (hasDerivAt_Li₂' (show 1 - u ∈ Ioo (0 : ℝ) 1 from ⟨h1u, by linarith⟩)).comp u h1d
  have hqd : HasDerivAt (fun u => (1 - m) * (1 - u) / (1 - (1 - m) * u))
      (-(1 - m) * m / (1 - (1 - m) * u) ^ 2) u := by
    have := (h1d.const_mul (1 - m)).div hDd hD.ne'
    refine this.congr_deriv ?_
    field_simp
    ring
  have hLq := (hasDerivAt_Li₂' hq).comp u hqd
  have h := (((((hlD.sub hl1).div hi hu0.ne').const_mul (3 / m)).sub
    (hlD.const_mul (3 * (1 - m) / m))).add (hl1.const_mul (3 / m))).sub
    ((hLu.sub hLau).const_mul (3 / m * (2 * m - 1)))
  have h' := h.add (((hL1u.add hLq).add ((hlD.sub_const (log m)).pow 2 |>.div_const 2)).const_mul
    (3 * m))
  convert h' using 1
  · funext v; simp [i12RKH, Function.comp]
  have e1 : 1 - (1 - m) * (1 - u) / (1 - (1 - m) * u) = m / (1 - (1 - m) * u) := by
    field_simp; ring
  have e2 : 1 + m * u / (1 - u) = (1 - (1 - m) * u) / (1 - u) := by field_simp; ring
  have e3 : (1 : ℝ) - (1 - u) = u := by ring
  simp only [i12Rg, e1, e2, e3, id, Pi.sub_apply]
  rw [Real.log_div hm0.ne' hD.ne', Real.log_div hD.ne' h1u.ne',
    Real.log_div (mul_pos hm0 hu0).ne' h1u.ne', Real.log_mul hm0.ne' hu0.ne']
  have := hD.ne'
  have := h1u.ne'
  have := hu0.ne'
  have := hm0.ne'
  have : (1 - m) * u ≠ 0 := hau.1.ne'
  have : (1 - m) * (1 - u) ≠ 0 := (mul_pos (by linarith) h1u).ne'
  generalize log (1 - (1 - m) * u) = LD
  generalize log (1 - u) = L1
  generalize log u = Lu
  generalize log m = Lm
  field_simp
  ring

theorem hasDerivAt_i12RKPrim {m u : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i12RKPrim m) (i12RPhi (m * u / (1 - u))) u := by
  have h1u : 0 < 1 - u := by linarith [hu.2]
  have hr : 0 < m * u / (1 - u) := div_pos (mul_pos hm.1 hu.1) h1u
  have hrd : HasDerivAt (fun u => m * u / (1 - u)) (m / (1 - u) ^ 2) u := by
    have := ((hasDerivAt_id u).const_mul m).div ((hasDerivAt_id u).const_sub 1) h1u.ne'
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hP := (hasDerivAt_i12RPhi hr).comp u hrd
  have h := (((hasDerivAt_id u).sub_const 1).mul hP).add (hasDerivAt_i12RKH hm hu)
  convert h using 1
  · funext v; simp [i12RKPrim, Function.comp]
  simp only [id, Function.comp_apply]
  have := h1u.ne'
  have := hu.1.ne'
  have := hm.1.ne'
  field_simp
  ring

theorem tendsto_i12RKH_zero {m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i12RKH m) (𝓝[>] 0)
      (𝓝 (3 + 3 * m * (π ^ 2 / 6 + Li₂ (1 - m) + log m ^ 2 / 2))) := by
  obtain ⟨hm0, hm1⟩ := hm
  have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT zero_lt_one
  have hS : Tendsto (fun u => (log (1 - (1 - m) * u) - log (1 - u)) / u) (𝓝[>] 0) (𝓝 m) := by
    have hd : HasDerivAt (fun u : ℝ => log (1 - (1 - m) * u) - log (1 - u)) m 0 := by
      have h1 := (((hasDerivAt_id' (0 : ℝ)).const_mul (1 - m)).const_sub 1).log (by norm_num)
      have h2 := ((hasDerivAt_id' (0 : ℝ)).const_sub 1).log (by norm_num)
      convert h1.sub h2 using 1
      norm_num
    refine hd.tendsto_slope_zero_right.congr fun t => ?_
    simp only [zero_add, mul_zero, sub_zero, log_one, smul_eq_mul]
    ring
  have hc : ∀ f : ℝ → ℝ, ContinuousAt f 0 → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := fun f hf =>
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have hc' := hc
  have hlD : Tendsto (fun u : ℝ => log (1 - (1 - m) * u)) (𝓝[>] 0) (𝓝 0) := by
    have h := hc (fun u : ℝ => log (1 - (1 - m) * u)) (by fun_prop (disch := norm_num))
    simpa using h
  have hl1 : Tendsto (fun u : ℝ => log (1 - u)) (𝓝[>] 0) (𝓝 0) := by
    have h := hc' (fun u : ℝ => log (1 - u)) (by fun_prop (disch := norm_num))
    simpa using h
  have hL1 : Tendsto (fun u : ℝ => Li₂ u) (𝓝[>] 0) (𝓝 (Li₂ 0)) :=
    tendsto_Li₂_comp (g := fun u : ℝ => u) (by norm_num) (hc (fun u : ℝ => u) (by fun_prop))
      (by filter_upwards [hev] with u hu; exact ⟨by linarith [hu.1], hu.2.le⟩)
  have hL2 : Tendsto (fun u : ℝ => Li₂ ((1 - m) * u)) (𝓝[>] 0) (𝓝 (Li₂ 0)) :=
    tendsto_Li₂_comp (g := fun u : ℝ => (1 - m) * u) (by norm_num)
      (by have h := hc (fun u : ℝ => (1 - m) * u) (by fun_prop); simp only [mul_zero] at h; exact h)
      (by
        filter_upwards [hev] with u hu
        obtain ⟨-, h, -⟩ := i12RK_mem ⟨hm0, hm1⟩ hu
        exact ⟨by linarith [h.1], h.2.le⟩)
  have hL3 : Tendsto (fun u : ℝ => Li₂ (1 - u)) (𝓝[>] 0) (𝓝 (Li₂ 1)) :=
    tendsto_Li₂_comp (g := fun u : ℝ => 1 - u) (by norm_num)
      (by have h := hc (fun u : ℝ => 1 - u) (by fun_prop); simp only [sub_zero] at h; exact h)
      (by filter_upwards [hev] with u hu; exact ⟨by linarith [hu.2], by linarith [hu.1]⟩)
  have hq : Tendsto (fun u : ℝ => (1 - m) * (1 - u) / (1 - (1 - m) * u)) (𝓝[>] 0)
      (𝓝 (1 - m)) := by
    have h := hc (fun u : ℝ => (1 - m) * (1 - u) / (1 - (1 - m) * u))
      (by fun_prop (disch := norm_num))
    simpa using h
  have hL4 : Tendsto (fun u : ℝ => Li₂ ((1 - m) * (1 - u) / (1 - (1 - m) * u))) (𝓝[>] 0)
      (𝓝 (Li₂ (1 - m))) :=
    tendsto_Li₂_comp ⟨by linarith, by linarith⟩ hq
      (by
        filter_upwards [hev] with u hu
        obtain ⟨-, -, h⟩ := i12RK_mem ⟨hm0, hm1⟩ hu
        exact ⟨by linarith [h.1], h.2.le⟩)
  have h := ((((hS.const_mul (3 / m)).sub (hlD.const_mul (3 * (1 - m) / m))).add
    (hl1.const_mul (3 / m))).sub ((hL1.sub hL2).const_mul (3 / m * (2 * m - 1)))).add
    (((hL3.add hL4).add ((hlD.sub_const (log m)).pow 2 |>.div_const 2)).const_mul (3 * m))
  rw [Li₂_zero, Li₂_one] at h
  have e : 3 + 3 * m * (π ^ 2 / 6 + Li₂ (1 - m) + log m ^ 2 / 2) =
      3 / m * m - 3 * (1 - m) / m * 0 + 3 / m * 0 - 3 / m * (2 * m - 1) * (0 - 0) +
        3 * m * (π ^ 2 / 6 + Li₂ (1 - m) + (0 - log m) ^ 2 / 2) := by
    have := hm0.ne'
    field_simp
    ring
  rw [e]
  exact h

theorem tendsto_i12RKPrim_zero {m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i12RKPrim m) (𝓝[>] 0)
      (𝓝 (3 + 3 * m * (π ^ 2 / 6 + Li₂ (1 - m) + log m ^ 2 / 2))) := by
  have hr : Tendsto (fun u : ℝ => m * u / (1 - u)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (by fun_prop (disch := norm_num) : ContinuousAt (fun u : ℝ => m * u / (1 - u))
        0).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with u hu
      exact div_pos (mul_pos hm.1 hu.1) (by linarith [hu.2])
  have h1 : Tendsto (fun u : ℝ => u - 1) (𝓝[>] 0) (𝓝 (0 - 1)) :=
    ((continuous_id.sub continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  have h := (h1.mul (tendsto_i12RPhi_zero.comp hr)).add (tendsto_i12RKH_zero hm)
  rw [mul_zero, zero_add] at h
  exact h

theorem tendsto_i12RKH_one {m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i12RKH m) (𝓝[<] 1)
      (𝓝 (3 * log m - 3 / m * (2 * m - 1) * (π ^ 2 / 6 - Li₂ (1 - m)))) := by
  obtain ⟨hm0, hm1⟩ := hm
  have hev : ∀ᶠ u in 𝓝[<] (1 : ℝ), u ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsLT zero_lt_one
  have hc : ∀ f : ℝ → ℝ, ContinuousAt f 1 → Tendsto f (𝓝[<] 1) (𝓝 (f 1)) := fun f hf =>
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have hm' : (1 : ℝ) - (1 - m) * 1 ≠ 0 := by rw [mul_one, sub_sub_cancel]; exact hm0.ne'
  have hlD : Tendsto (fun u : ℝ => log (1 - (1 - m) * u)) (𝓝[<] 1) (𝓝 (log m)) := by
    have h := hc (fun u : ℝ => log (1 - (1 - m) * u)) (by fun_prop (disch := exact hm'))
    simpa using h
  have hu : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := hc (fun u : ℝ => u) (by fun_prop)
  have hml : Tendsto (fun u : ℝ => (1 - u) * log (1 - u)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one
  have hL2 : Tendsto (fun u : ℝ => Li₂ ((1 - m) * u)) (𝓝[<] 1) (𝓝 (Li₂ (1 - m))) :=
    tendsto_Li₂_comp (g := fun u : ℝ => (1 - m) * u) ⟨by linarith, by linarith⟩
      (by have h := hc (fun u : ℝ => (1 - m) * u) (by fun_prop); simp only [mul_one] at h; exact h)
      (by
        filter_upwards [hev] with u hu
        obtain ⟨-, h, -⟩ := i12RK_mem ⟨hm0, hm1⟩ hu
        exact ⟨by linarith [h.1], h.2.le⟩)
  have hL3 : Tendsto (fun u : ℝ => Li₂ (1 - u)) (𝓝[<] 1) (𝓝 (Li₂ 0)) :=
    tendsto_Li₂_comp (g := fun u : ℝ => 1 - u) (by norm_num)
      (by have h := hc (fun u : ℝ => 1 - u) (by fun_prop); simp only [sub_self] at h; exact h)
      (by filter_upwards [hev] with u hu; exact ⟨by linarith [hu.2], by linarith [hu.1]⟩)
  have hq : Tendsto (fun u : ℝ => (1 - m) * (1 - u) / (1 - (1 - m) * u)) (𝓝[<] 1) (𝓝 0) := by
    have h := hc (fun u : ℝ => (1 - m) * (1 - u) / (1 - (1 - m) * u))
      (by fun_prop (disch := exact hm'))
    simpa using h
  have hL4 : Tendsto (fun u : ℝ => Li₂ ((1 - m) * (1 - u) / (1 - (1 - m) * u))) (𝓝[<] 1)
      (𝓝 (Li₂ 0)) :=
    tendsto_Li₂_comp (by norm_num) hq
      (by
        filter_upwards [hev] with u hu
        obtain ⟨-, -, h⟩ := i12RK_mem ⟨hm0, hm1⟩ hu
        exact ⟨by linarith [h.1], h.2.le⟩)
  have h := (((((hlD.div hu one_ne_zero).const_mul (3 / m)).sub
    ((hml.div hu one_ne_zero).const_mul (3 / m))).sub
    (hlD.const_mul (3 * (1 - m) / m))).sub
    ((tendsto_Li₂_one_left.sub hL2).const_mul (3 / m * (2 * m - 1)))).add
    (((hL3.add hL4).add ((hlD.sub_const (log m)).pow 2 |>.div_const 2)).const_mul (3 * m))
  rw [Li₂_zero] at h
  have e : i12RKH m =ᶠ[𝓝[<] 1] fun u => 3 / m * (log (1 - (1 - m) * u) / u) -
      3 / m * ((1 - u) * log (1 - u) / u) - 3 * (1 - m) / m * log (1 - (1 - m) * u) -
      3 / m * (2 * m - 1) * (Li₂ u - Li₂ ((1 - m) * u)) +
      3 * m * (Li₂ (1 - u) + Li₂ ((1 - m) * (1 - u) / (1 - (1 - m) * u)) +
        (log (1 - (1 - m) * u) - log m) ^ 2 / 2) := by
    filter_upwards [hev] with u hu
    have := hu.1.ne'
    simp only [i12RKH]
    field_simp
    ring
  refine Tendsto.congr' e.symm ?_
  convert h using 2
  have := hm0.ne'
  field_simp
  ring

theorem tendsto_i12RKPrim_one {m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i12RKPrim m) (𝓝[<] 1)
      (𝓝 (3 * log m - 3 / m * (2 * m - 1) * (π ^ 2 / 6 - Li₂ (1 - m)))) := by
  have hev : ∀ᶠ u in 𝓝[<] (1 : ℝ), u ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  have hm1 : 0 ≤ log (1 + m) := log_nonneg (by linarith [hm.1])
  have hb : Tendsto (fun u : ℝ => (1 - u) * (9 + π ^ 2 + 6 * log (1 + m) ^ 2) +
      6 * ((1 - u) * log (1 - u) ^ 2)) (𝓝[<] 1) (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => 1 - u) (𝓝[<] 1) (𝓝 0) := by
      have := (by fun_prop : Continuous fun u : ℝ => 1 - u).tendsto (1 : ℝ) |>.mono_left
        (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      simpa using this
    have h2 := tendsto_mul_log_sq_zero.comp tendsto_one_sub_nhdsLT_one
    simpa using (h1.mul_const (9 + π ^ 2 + 6 * log (1 + m) ^ 2)).add (h2.const_mul 6)
  have hP : Tendsto (fun u : ℝ => (u - 1) * i12RPhi (m * u / (1 - u))) (𝓝[<] 1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hev] with u hu
    have h1u : 0 < 1 - u := by linarith [hu.2]
    have hr : 0 < m * u / (1 - u) := div_pos (mul_pos hm.1 hu.1) h1u
    have h := abs_i12RPhi_le hr
    obtain ⟨hl0, hl1⟩ := i12_log_one_add_le hm.1 hu
    have hu0 : log (1 - u) ≤ 0 := log_nonpos h1u.le (by linarith [hu.1])
    have hsq : log (1 + m * u / (1 - u)) ^ 2 ≤ 2 * log (1 + m) ^ 2 + 2 * log (1 - u) ^ 2 := by
      nlinarith [sq_nonneg (log (1 + m) + log (1 - u))]
    rw [Real.norm_eq_abs, abs_mul, abs_of_neg (by linarith : u - 1 < 0)]
    have : |i12RPhi (m * u / (1 - u))| ≤ 9 + π ^ 2 + 6 * log (1 + m) ^ 2 +
        6 * log (1 - u) ^ 2 := by linarith
    calc -(u - 1) * |i12RPhi (m * u / (1 - u))|
        ≤ (1 - u) * (9 + π ^ 2 + 6 * log (1 + m) ^ 2 + 6 * log (1 - u) ^ 2) := by
          rw [show -(u - 1) = 1 - u by ring]
          exact mul_le_mul_of_nonneg_left this h1u.le
      _ = _ := by ring
  have h := hP.add (tendsto_i12RKH_one hm)
  rw [zero_add] at h
  exact h

/-- **The closed form of `K` on `(0, 1)`.** -/
theorem i12RK_eq {m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) : i12RK m = i12RKcl m := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun u hu => hasDerivAt_i12RKPrim hm hu) (intervalIntegrable_i12RK hm.1)
    (tendsto_i12RKPrim_zero hm) (tendsto_i12RKPrim_one hm)
  have hrefl := Li₂_add_Li₂_one_sub hm.1.le hm.2.le
  simp only [i12RK, i12RKcl, h]
  have := hm.1.ne'
  have e : Li₂ (1 - m) = π ^ 2 / 6 - log m * log (1 - m) - Li₂ m := by linarith
  rw [e]
  field_simp
  ring

end QED.ThreeLoopD
