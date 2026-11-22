/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5Beta

/-!
# Set (d), master `I₅`: the large-`t` expansion of one fibre of the triangle

In the coordinates `a = c r`, `c = s / (1 + r)` the on-shell triangle at `w = t` becomes
`∫₀^∞ (1 + r)⁻² Φ(t, (1 + r)⁻²) dr` with the fibre

  `Φ(t, m) = ∫₀^∞ (1 + s) ^ (-1 + 2ε) s ^ (-ε) (t + m s) ^ (-1 - ε) ds`
  (`QED.ThreeLoopD.i5Fib`).

For `t ≥ 1`, `0 < m ≤ 1`, `0 < ‖ε‖ ≤ 1/10`,

  `‖Φ(t, m) - (t⁻¹ (m⁻¹) ^ ε / ε - (G / ε) t ^ (-1 - ε))‖ ≤ C t ^ (-7/5)`
  (`QED.ThreeLoopD.norm_i5Fib_sub_le`).

Proof: split `(0, ∞)` at `s = 1` and write `h = h₁ + s ^ (-1 + ε)` on `(1, ∞)`. Replacing
`(t + m s) ^ (-1 - ε)` by `t ^ (-1 - ε)` against `h` on `(0, 1)` and `h₁` on `(1, ∞)` costs
`O(t ^ (-7/5))` (`QED.ThreeLoopD.norm_i5P_sub_le`: the difference is at most `2 √s t ^ (-7/5)`)
and leaves `t ^ (-1 - ε) H = t ^ (-1 - ε) (1 - G) / ε` (`QED.ThreeLoopD.i5Hc_eq`). The rest has
the antiderivative `s ^ ε (t + m s) ^ (-ε) / (ε t)`
(`QED.ThreeLoopD.integral_i5_tail`), whose value differs from `t⁻¹ (m⁻¹) ^ ε / ε - t ^ (-1 - ε) / ε`
by `O(t ^ (-19/10))`.

## Main results

* `QED.ThreeLoopD.integral_i5_tail`, `QED.ThreeLoopD.norm_i5Fib_sub_le`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.ThreeLoopD

/-- The propagator factor `(t + m s) ^ (-1 - ε)` of the fibre. -/
noncomputable def i5P (ε : ℂ) (t m s : ℝ) : ℂ := ((t + m * s : ℝ) : ℂ) ^ (-1 - ε)

/-- **The fibre** `Φ(t, m) = ∫₀^∞ (1 + s) ^ (-1 + 2ε) s ^ (-ε) (t + m s) ^ (-1 - ε) ds`. -/
noncomputable def i5Fib (ε : ℂ) (t m : ℝ) : ℂ := ∫ s in Ioi (0 : ℝ), i5h ε s * i5P ε t m s

theorem measurable_i5P (ε : ℂ) (t m : ℝ) : Measurable (i5P ε t m) :=
  i5_measurable_cpow_affine t m _

theorem norm_i5P_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht : 1 ≤ t) {m s : ℝ} (hm : 0 ≤ m)
    (hs : 0 ≤ s) : ‖i5P ε t m s‖ ≤ t ^ (-(9 / 10 : ℝ)) := by
  obtain ⟨-, h1, h2⟩ := i5_re_facts hε
  have ht0 : 0 < t := by linarith
  have hts : t ≤ t + m * s := by nlinarith
  rw [i5P, norm_cpow_eq_rpow_re_of_pos (by linarith)]
  have e : (-1 - ε).re = -1 - ε.re := by simp
  rw [e]
  exact (Real.rpow_le_rpow_of_nonpos ht0 hts (by linarith)).trans
    (Real.rpow_le_rpow_of_exponent_le ht (by linarith))

theorem norm_i5T_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht : 1 ≤ t) :
    ‖(t : ℂ) ^ (-1 - ε)‖ ≤ t ^ (-(9 / 10 : ℝ)) := by
  have := norm_i5P_le hε ht le_rfl le_rfl (m := 0) (s := 0)
  simpa [i5P] using this

/-- **Replacing `(t + m s) ^ (-1 - ε)` by `t ^ (-1 - ε)`** costs at most `2 √s t ^ (-7/5)`. -/
theorem norm_i5P_sub_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht : 1 ≤ t) {m s : ℝ} (hm0 : 0 ≤ m)
    (hm1 : m ≤ 1) (hs : 0 ≤ s) :
    ‖i5P ε t m s - (t : ℂ) ^ (-1 - ε)‖ ≤ 2 * s ^ (1 / 2 : ℝ) * t ^ (-(7 / 5 : ℝ)) := by
  obtain ⟨-, h1, h2⟩ := i5_re_facts hε
  have ht0 : 0 < t := by linarith
  have hms : 0 ≤ m * s := mul_nonneg hm0 hs
  have hre : (-1 - ε).re = -1 - ε.re := by simp
  have hMV := i5_norm_ofReal_cpow_sub_le ht0 (by linarith : t ≤ t + m * s) (c := -1 - ε)
    (by rw [hre]; linarith)
  rw [hre, show t + m * s - t = m * s by ring] at hMV
  have hn : ‖-1 - ε‖ ≤ 11 / 10 := by
    have := norm_sub_le (-1 : ℂ) ε
    rw [norm_neg, norm_one] at this
    linarith
  have hp1 : t ^ (-1 - ε.re - 1) ≤ t ^ (-(19 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have hA : ‖i5P ε t m s - (t : ℂ) ^ (-1 - ε)‖ ≤ 11 / 10 * (m * s) * t ^ (-(19 / 10 : ℝ)) := by
    refine hMV.trans ?_
    gcongr
  have hB : ‖i5P ε t m s - (t : ℂ) ^ (-1 - ε)‖ ≤ 2 * t ^ (-(9 / 10 : ℝ)) := by
    refine (norm_sub_le _ _).trans ?_
    linarith [norm_i5P_le hε ht hm0 hs, norm_i5T_le hε ht]
  have hst : s ^ (1 / 2 : ℝ) = Real.sqrt s := (Real.sqrt_eq_rpow s).symm
  have htt : t ^ (1 / 2 : ℝ) = Real.sqrt t := (Real.sqrt_eq_rpow t).symm
  have k1 : Real.sqrt t * t ^ (-(19 / 10 : ℝ)) = t ^ (-(7 / 5 : ℝ)) := by
    rw [← htt, ← Real.rpow_add ht0]; norm_num
  have k2 : Real.sqrt t * t ^ (-(7 / 5 : ℝ)) = t ^ (-(9 / 10 : ℝ)) := by
    rw [← htt, ← Real.rpow_add ht0]; norm_num
  have hT0 : 0 ≤ t ^ (-(7 / 5 : ℝ)) := Real.rpow_nonneg ht0.le _
  have hT1 : 0 ≤ t ^ (-(19 / 10 : ℝ)) := Real.rpow_nonneg ht0.le _
  rw [hst]
  rcases le_or_gt (m * s) t with hc | hc
  · have hsq : m * s ≤ Real.sqrt s * Real.sqrt t := by
      rw [← Real.sqrt_mul hs]
      refine Real.le_sqrt_of_sq_le ?_
      have : m * s ≤ s := by nlinarith
      nlinarith
    calc _ ≤ 11 / 10 * (m * s) * t ^ (-(19 / 10 : ℝ)) := hA
      _ ≤ 11 / 10 * (Real.sqrt s * Real.sqrt t) * t ^ (-(19 / 10 : ℝ)) := by gcongr
      _ = 11 / 10 * Real.sqrt s * (Real.sqrt t * t ^ (-(19 / 10 : ℝ))) := by ring
      _ ≤ 2 * Real.sqrt s * t ^ (-(7 / 5 : ℝ)) := by
          rw [k1]; gcongr; norm_num
  · have hsq : Real.sqrt t ≤ Real.sqrt s :=
      Real.sqrt_le_sqrt (by nlinarith)
    calc _ ≤ 2 * t ^ (-(9 / 10 : ℝ)) := hB
      _ = 2 * (Real.sqrt t * t ^ (-(7 / 5 : ℝ))) := by rw [k2]
      _ ≤ 2 * (Real.sqrt s * t ^ (-(7 / 5 : ℝ))) := by gcongr
      _ = _ := by ring

/-! ### The exact tail -/

theorem i5_cpow_div_eq {ε : ℂ} {t m s : ℝ} (hs : 0 < s) (hd : 0 < t + m * s) :
    (((s / (t + m * s)) : ℝ) : ℂ) ^ ε = (s : ℂ) ^ ε * ((t + m * s : ℝ) : ℂ) ^ (-ε) := by
  rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hs.le (inv_nonneg.mpr hd.le),
    QED.DimReg.ofReal_inv_cpow hd]

theorem integrableOn_i5_tail {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ (-1 + ε) * i5P ε t m s) (Ioi 1) := by
  obtain ⟨-, h1, h2⟩ := i5_re_facts hε
  refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul
    (m ^ (-1 - ε.re))).mono'
    ((i5_measurable_cpow _).mul (measurable_i5P ε t m)).aestronglyMeasurable.restrict
    (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hms : 0 < m * s := mul_pos hm hs0
  rw [norm_mul, i5P, norm_cpow_eq_rpow_re_of_pos hs0, norm_cpow_eq_rpow_re_of_pos (by linarith)]
  have e1 : (-1 + ε).re = -1 + ε.re := by simp
  have e2 : (-1 - ε).re = -1 - ε.re := by simp
  rw [e1, e2]
  have hle : (t + m * s) ^ (-1 - ε.re) ≤ (m * s) ^ (-1 - ε.re) :=
    Real.rpow_le_rpow_of_nonpos hms (by linarith) (by linarith)
  rw [Real.mul_rpow hm.le hs0.le] at hle
  calc s ^ (-1 + ε.re) * (t + m * s) ^ (-1 - ε.re) ≤
        s ^ (-1 + ε.re) * (m ^ (-1 - ε.re) * s ^ (-1 - ε.re)) :=
        mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hs0.le _)
    _ = m ^ (-1 - ε.re) * (s ^ (-1 + ε.re) * s ^ (-1 - ε.re)) := by ring
    _ = m ^ (-1 - ε.re) * s ^ (-2 : ℝ) := by rw [← Real.rpow_add hs0]; ring_nf

/-- **The exact tail**: `∫₁^∞ s ^ (-1 + ε) (t + m s) ^ (-1 - ε) ds
= ((m⁻¹) ^ ε - (t + m) ^ (-ε)) / (ε t)`. -/
theorem integral_i5_tail {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) (h0 : ε ≠ 0) {t m : ℝ} (ht : 0 < t)
    (hm : 0 < m) :
    ∫ s in Ioi (1 : ℝ), (s : ℂ) ^ (-1 + ε) * i5P ε t m s =
      (((m⁻¹ : ℝ) : ℂ) ^ ε - ((t + m : ℝ) : ℂ) ^ (-ε)) / (ε * t) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  set Q : ℝ → ℂ := fun s => (s : ℂ) ^ ε * ((t + m * s : ℝ) : ℂ) ^ (-ε) / (ε * t) with hQ
  have hd : ∀ s ∈ Ioi (1 : ℝ), HasDerivAt Q ((s : ℂ) ^ (-1 + ε) * i5P ε t m s) s := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans hs
    have hts : 0 < t + m * s := by positivity
    have hs1 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs0.ne'
    have hts1 : ((t + m * s : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hts.ne'
    refine (((hasDerivAt_ofReal_cpow_const hs0.ne' h0).mul
      (i5_hasDerivAt_cpow_affine t m (-ε) hts)).div_const (ε * t)).congr_deriv ?_
    have e1 : (s : ℂ) ^ ε = (s : ℂ) ^ (-1 + ε) * s := by
      rw [← i5_cpow_add_one hs1]; ring_nf
    have e2 : (s : ℂ) ^ (ε - 1) = (s : ℂ) ^ (-1 + ε) := by ring_nf
    have e3 : ((t + m * s : ℝ) : ℂ) ^ (-ε) = i5P ε t m s * ((t + m * s : ℝ) : ℂ) := by
      rw [i5P, ← i5_cpow_add_one hts1]; ring_nf
    have e4 : ((t + m * s : ℝ) : ℂ) ^ (-ε - 1) = i5P ε t m s := by rw [i5P]; ring_nf
    rw [e1, e2, e3, e4]
    push_cast
    field_simp
    ring
  have hc : ContinuousWithinAt Q (Ici 1) 1 := by
    have h1 := ((hasDerivAt_ofReal_cpow_const one_ne_zero h0).mul
      (i5_hasDerivAt_cpow_affine t m (-ε) (by positivity : (0 : ℝ) < t + m * 1))).div_const
        (ε * t)
    exact h1.continuousAt.continuousWithinAt
  have hlim : Tendsto Q atTop (𝓝 (((m⁻¹ : ℝ) : ℂ) ^ ε / (ε * t))) := by
    have hr : Tendsto (fun s : ℝ => s / (t + m * s)) atTop (𝓝 m⁻¹) := by
      have h1 : Tendsto (fun s : ℝ => (t / s + m)⁻¹) atTop (𝓝 (0 + m)⁻¹) :=
        ((tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds).inv₀
          (by rw [zero_add]; exact hm.ne')
      rw [zero_add] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with s hs
      field_simp
    have hc := ((continuousAt_ofReal_cpow_const m⁻¹ ε
      (Or.inr (inv_ne_zero hm.ne'))).tendsto.comp hr).div_const (ε * t)
    refine hc.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [Function.comp, hQ]
    rw [i5_cpow_div_eq hs (by positivity)]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hc hd (integrableOn_i5_tail hε ht hm) hlim
  rw [h, hQ]
  simp only [ofReal_one, one_cpow, one_mul, mul_one]
  ring

/-! ### The expansion of the fibre -/

/-- The constant of the fibre bound. -/
noncomputable def i5CF : ℝ :=
  2 * (∫ s in Ioo (0 : ℝ) 1, s ^ (2 / 5 : ℝ)) +
    12 / 5 * (∫ s in Ioi (1 : ℝ), s ^ (-(6 / 5) : ℝ)) + 1

theorem integrableOn_i5hP {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t m : ℝ} (ht : 1 ≤ t) (hm0 : 0 ≤ m) :
    IntegrableOn (fun s => i5h ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε))) (Ioo 0 1) ∧
      IntegrableOn (fun s => i5h ε s * i5P ε t m s) (Ioo 0 1) := by
  have hb : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ ≤ 2 * t ^ (-(9 / 10 : ℝ)) →
      ‖i5h ε s * z‖ ≤ 2 * t ^ (-(9 / 10 : ℝ)) * s ^ (-(1 / 10 : ℝ)) := fun s hs z hz => by
    rw [norm_mul, mul_comm]
    exact mul_le_mul hz (norm_i5h_le hε hs) (norm_nonneg _) (by positivity)
  have hI := (integrableOn_rpow_Ioo (by norm_num : (-1 : ℝ) < -(1 / 10))).const_mul
    (2 * t ^ (-(9 / 10 : ℝ)))
  refine ⟨hI.mono' (((measurable_i5h ε).mul ((measurable_i5P ε t m).sub
    measurable_const)).aestronglyMeasurable.restrict) (ae_restrict_of_forall_mem
      measurableSet_Ioo fun s hs => hb s hs _ ?_), hI.mono' (((measurable_i5h ε).mul
    (measurable_i5P ε t m)).aestronglyMeasurable.restrict) (ae_restrict_of_forall_mem
      measurableSet_Ioo fun s hs => hb s hs _ ?_)⟩
  · exact (norm_sub_le _ _).trans (by
      linarith [norm_i5P_le hε ht hm0 hs.1.le, norm_i5T_le hε ht])
  · linarith [norm_i5P_le hε ht hm0 hs.1.le, Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ t)
      (-(9 / 10 : ℝ))]

theorem integrableOn_i5h1P {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t m : ℝ} (ht : 1 ≤ t) (hm0 : 0 ≤ m) :
    IntegrableOn (fun s => i5h1 ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε))) (Ioi 1) ∧
      IntegrableOn (fun s => i5h1 ε s * i5P ε t m s) (Ioi 1) := by
  have hb : ∀ s ∈ Ioi (1 : ℝ), ∀ z : ℂ, ‖z‖ ≤ 2 * t ^ (-(9 / 10 : ℝ)) →
      ‖i5h1 ε s * z‖ ≤ 2 * t ^ (-(9 / 10 : ℝ)) * (6 / 5 * s ^ (-(17 / 10 : ℝ))) :=
    fun s hs z hz => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul hz (norm_i5h1_le hε hs.le) (norm_nonneg _) (by positivity)
  have hI := ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(17 / 10 : ℝ) < -1)
    one_pos).const_mul (6 / 5)).const_mul (2 * t ^ (-(9 / 10 : ℝ)))
  refine ⟨hI.mono' (((measurable_i5h1 ε).mul ((measurable_i5P ε t m).sub
    measurable_const)).aestronglyMeasurable.restrict) (ae_restrict_of_forall_mem
      measurableSet_Ioi fun s hs => hb s hs _ ?_), hI.mono' (((measurable_i5h1 ε).mul
    (measurable_i5P ε t m)).aestronglyMeasurable.restrict) (ae_restrict_of_forall_mem
      measurableSet_Ioi fun s hs => hb s hs _ ?_)⟩
  · exact (norm_sub_le _ _).trans (by
      linarith [norm_i5P_le hε ht hm0 (zero_le_one.trans hs.le), norm_i5T_le hε ht])
  · linarith [norm_i5P_le hε ht hm0 (zero_le_one.trans hs.le),
      Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ t) (-(9 / 10 : ℝ))]

/-- The fibre as the hard constant plus three remainders. -/
theorem i5Fib_eq {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t m : ℝ} (ht : 1 ≤ t) (hm : 0 < m) :
    i5Fib ε t m = (t : ℂ) ^ (-1 - ε) * i5Hc ε +
      (∫ s in Ioo (0 : ℝ) 1, i5h ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε))) +
      (∫ s in Ioi (1 : ℝ), i5h1 ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε))) +
      ∫ s in Ioi (1 : ℝ), (s : ℂ) ^ (-1 + ε) * i5P ε t m s := by
  have ht0 : 0 < t := by linarith
  obtain ⟨A1, A2⟩ := integrableOn_i5hP hε ht hm.le
  obtain ⟨B1, B2⟩ := integrableOn_i5h1P hε ht hm.le
  have C := integrableOn_i5_tail hε ht0 hm
  have hT1 := (integrableOn_i5h hε).mul_const ((t : ℂ) ^ (-1 - ε))
  have hT2 := (integrableOn_i5h1 hε).mul_const ((t : ℂ) ^ (-1 - ε))
  have hR : IntegrableOn (fun s => i5h ε s * i5P ε t m s) (Ioi 1) :=
    (B2.add C).congr_fun (fun s hs => by
      simp only [Pi.add_apply, i5h_eq_h1_add (zero_lt_one.trans hs)]; ring) measurableSet_Ioi
  have hL : IntegrableOn (fun s => i5h ε s * i5P ε t m s) (Ioc 0 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).mpr A2
  rw [i5Fib, ← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi hL hR, integral_Ioc_eq_integral_Ioo]
  have e1 : ∫ s in Ioo (0 : ℝ) 1, i5h ε s * i5P ε t m s =
      (∫ s in Ioo (0 : ℝ) 1, i5h ε s * (t : ℂ) ^ (-1 - ε)) +
        ∫ s in Ioo (0 : ℝ) 1, i5h ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε)) := by
    rw [← integral_add hT1 A1]; congr 1; funext s; ring
  have e2 : ∫ s in Ioi (1 : ℝ), i5h ε s * i5P ε t m s =
      (∫ s in Ioi (1 : ℝ), i5h1 ε s * (t : ℂ) ^ (-1 - ε)) +
        (∫ s in Ioi (1 : ℝ), i5h1 ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε))) +
        ∫ s in Ioi (1 : ℝ), (s : ℂ) ^ (-1 + ε) * i5P ε t m s := by
    have e := integral_add (hT2.add B1) C
    simp only [Pi.add_apply] at e
    rw [← integral_add hT2 B1, ← e]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    simp only [i5h_eq_h1_add (zero_lt_one.trans hs)]; ring
  rw [e1, e2, integral_mul_const, integral_mul_const, i5Hc]
  ring

/-- **The large-`t` expansion of the fibre.** -/
theorem norm_i5Fib_sub_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) (h0 : ε ≠ 0) {t : ℝ} (ht : 1 ≤ t) {m : ℝ}
    (hm0 : 0 < m) (hm1 : m ≤ 1) :
    ‖i5Fib ε t m - ((t : ℂ)⁻¹ * ((m⁻¹ : ℝ) : ℂ) ^ ε / ε - i13G ε / ε * (t : ℂ) ^ (-1 - ε))‖ ≤
      i5CF * t ^ (-(7 / 5 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  have hH : i5Hc ε = (1 - i13G ε) / ε := by
    rw [eq_div_iff h0, mul_comm]; exact i5Hc_eq hε h0
  have hTe : (t : ℂ) ^ (-1 - ε) = (t : ℂ) ^ (-ε) / t := by
    rw [show (-1 : ℂ) - ε = -ε + -1 by ring, cpow_add _ _ htc, cpow_neg_one, div_eq_mul_inv]
  have hkey : i5Fib ε t m - ((t : ℂ)⁻¹ * ((m⁻¹ : ℝ) : ℂ) ^ ε / ε -
      i13G ε / ε * (t : ℂ) ^ (-1 - ε)) =
      (∫ s in Ioo (0 : ℝ) 1, i5h ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε))) +
      (∫ s in Ioi (1 : ℝ), i5h1 ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε))) +
      ((t : ℂ) ^ (-ε) - ((t + m : ℝ) : ℂ) ^ (-ε)) / (ε * t) := by
    rw [i5Fib_eq hε ht hm0, integral_i5_tail hε h0 ht0 hm0, hH]
    generalize (∫ s in Ioo (0 : ℝ) 1, i5h ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε))) = X
    generalize (∫ s in Ioi (1 : ℝ), i5h1 ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε))) = Y
    rw [hTe]
    field_simp
    ring
  set E1 := ∫ s in Ioo (0 : ℝ) 1, i5h ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε))
  set E2 := ∫ s in Ioi (1 : ℝ), i5h1 ε s * (i5P ε t m s - (t : ℂ) ^ (-1 - ε))
  -- the three bounds
  have hE1 : ‖E1‖ ≤ 2 * t ^ (-(7 / 5 : ℝ)) * ∫ s in Ioo (0 : ℝ) 1, s ^ (2 / 5 : ℝ) := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le
      ((integrableOn_rpow_Ioo (by norm_num : (-1 : ℝ) < 2 / 5)).const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_)
    rw [norm_mul]
    calc ‖i5h ε s‖ * ‖i5P ε t m s - (t : ℂ) ^ (-1 - ε)‖ ≤
          s ^ (-(1 / 10 : ℝ)) * (2 * s ^ (1 / 2 : ℝ) * t ^ (-(7 / 5 : ℝ))) :=
          mul_le_mul (norm_i5h_le hε hs) (norm_i5P_sub_le hε ht hm0.le hm1 hs.1.le)
            (norm_nonneg _) (Real.rpow_nonneg hs.1.le _)
      _ = 2 * t ^ (-(7 / 5 : ℝ)) * (s ^ (-(1 / 10 : ℝ)) * s ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hs.1]; norm_num
  have hE2 : ‖E2‖ ≤ 12 / 5 * t ^ (-(7 / 5 : ℝ)) * ∫ s in Ioi (1 : ℝ), s ^ (-(6 / 5) : ℝ) := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(6 / 5 : ℝ) < -1) one_pos).const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
    have hs0 : 0 < s := zero_lt_one.trans hs
    rw [norm_mul]
    calc ‖i5h1 ε s‖ * ‖i5P ε t m s - (t : ℂ) ^ (-1 - ε)‖ ≤
          6 / 5 * s ^ (-(17 / 10 : ℝ)) * (2 * s ^ (1 / 2 : ℝ) * t ^ (-(7 / 5 : ℝ))) :=
          mul_le_mul (norm_i5h1_le hε hs.le) (norm_i5P_sub_le hε ht hm0.le hm1 hs0.le)
            (norm_nonneg _) (by positivity)
      _ = 12 / 5 * t ^ (-(7 / 5 : ℝ)) * (s ^ (-(17 / 10 : ℝ)) * s ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hs0]; norm_num
  have hE3 : ‖((t : ℂ) ^ (-ε) - ((t + m : ℝ) : ℂ) ^ (-ε)) / (ε * t)‖ ≤ t ^ (-(7 / 5 : ℝ)) := by
    obtain ⟨-, h1, h2⟩ := i5_re_facts hε
    have hMV := i5_norm_ofReal_cpow_sub_le ht0 (by linarith : t ≤ t + m) (c := -ε)
      (by simp; linarith)
    rw [norm_neg] at hMV
    rw [norm_div, norm_sub_rev, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hεn : 0 < ‖ε‖ := norm_pos_iff.mpr h0
    rw [div_le_iff₀ (by positivity)]
    have hp : t ^ ((-ε).re - 1) ≤ t ^ (-(9 / 10 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le ht (by simp; linarith)
    have hp3 : t ^ (-(9 / 10 : ℝ)) ≤ t ^ (-(7 / 5 : ℝ)) * t := by
      rw [← Real.rpow_add_one ht0.ne']
      exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
    calc _ ≤ ‖ε‖ * (t + m - t) * t ^ ((-ε).re - 1) := hMV
      _ ≤ ‖ε‖ * 1 * t ^ (-(9 / 10 : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hεn.le) hp (by positivity)
            (by positivity)
      _ = ‖ε‖ * t ^ (-(9 / 10 : ℝ)) := by ring
      _ ≤ ‖ε‖ * (t ^ (-(7 / 5 : ℝ)) * t) := mul_le_mul_of_nonneg_left hp3 hεn.le
      _ = _ := by ring
  rw [hkey]
  have hi0 : 0 ≤ ∫ s in Ioo (0 : ℝ) 1, s ^ (2 / 5 : ℝ) :=
    setIntegral_nonneg measurableSet_Ioo fun s hs => Real.rpow_nonneg hs.1.le _
  calc _ ≤ ‖E1‖ + ‖E2‖ + ‖((t : ℂ) ^ (-ε) - ((t + m : ℝ) : ℂ) ^ (-ε)) / (ε * t)‖ :=
        norm_add₃_le
    _ ≤ _ := by
        unfold i5CF
        nlinarith [hE1, hE2, hE3]

end QED.ThreeLoopD
