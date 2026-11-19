/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutCId

/-!
# Set (c), Stage K, group G4: an absolute bound for the outer-massive corner weight

Helper level (no frozen statement). For `m, e, w, u > 0`, `s ≥ 0`, `M = m - e u ≠ 0`,
`β = w (s + e)`, `z₀ = (s + e) u` and `a = m + s u = M + z₀`
(**`scOutCTg_abs_integral_le`**):

`∫₀^∞ |T(v)|/(u + v)² dv ≤ A_c log(1 + M/z₀)/M + A_a (w/u)/a
  + |c₀| w (log a - log m)/u + |c₀ w log m|/u`,

with `A_c = |c₁| + |c₂|/β + |c₃|/β²`, `A_a = |a₀| + |a₁|/β + |a₂|/β²` and
`T = scOutCTg a₀ a₁ a₂ c₀ c₁ c₂ c₃ m e w s`. Proof: `|K(v)| ≤ ∫₀^v |k|`, then
`∫ (∫₀^v |k|)/(u + v)² = ∫ |k|/(u + v)` (`scOutC_ibp`); on the threshold set the node change of
variables `scOutC_cv` turns `|k|/(u + v)` and `|κ|/(u + v)²` into the absolute values of the
master integrands, bounded by `z ≥ z₀`; beyond the threshold `|k| = |c₀| w/v`.

Also **`scOutC_J1_le`**: `log(1 + M/z₀)/M ≤ 2 (1 + log(1 + a/z₀))/a` for `a = M + z₀ > 0`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

section

variable {m e w s u : ℝ}

/-- The size of a `ρ`-quadratic: `|c₁ + c₂ ρ + c₃ ρ²| ≤ |c₁| + |c₂|/β + |c₃|/β²`
for `0 < ρ ≤ 1/β`. -/
theorem scOutC_abs_quad_le {β ρ : ℝ} (hρ : 0 < ρ) (hρβ : ρ ≤ 1 / β)
    (c₁ c₂ c₃ : ℝ) :
    |c₁ + c₂ * ρ + c₃ * ρ ^ 2| ≤ |c₁| + |c₂| / β + |c₃| / β ^ 2 := by
  have h2 : ρ ^ 2 ≤ 1 / β ^ 2 := by
    rw [one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ hρ.le hρβ 2
  calc |c₁ + c₂ * ρ + c₃ * ρ ^ 2| ≤ |c₁| + |c₂| * ρ + |c₃| * ρ ^ 2 := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
        · rw [abs_mul, abs_of_pos hρ]
        · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ρ ^ 2)]
    _ ≤ |c₁| + |c₂| * (1 / β) + |c₃| * (1 / β ^ 2) := by
        gcongr
    _ = _ := by ring

/-- The `k`-part on the threshold set, in absolute value. -/
theorem scOutC_abs_k_S (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u) (hs : 0 ≤ s)
    (hM : m - e * u ≠ 0) (c₀ c₁ c₂ c₃ : ℝ) :
    ∫ v in scOutCS m s, |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)| ≤
      (|c₁| + |c₂| / (w * (s + e)) + |c₃| / (w * (s + e)) ^ 2) *
        (log (1 + (m - e * u) / ((s + e) * u)) / (m - e * u)) := by
  have hc : 0 < (s + e) * u := by positivity
  have hMc : 0 < m - e * u + (s + e) * u := by nlinarith [mul_nonneg hs hu.le]
  obtain ⟨j1, w1⟩ := scOutCJ1 hM hc hMc
  obtain ⟨-, hval⟩ := scOutC_cv (e := e) hm hu hs
    (fun v => |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)|)
  rw [hval, ← w1, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ (j1.const_mul _) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have : 0 < z - e * u := by rw [mem_Ioi] at hz; nlinarith
    positivity
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz' : (s + e) * u < z := hz
    have hz0 : 0 < z := hc.trans hz'
    have hD : 0 < m - e * u + z := by linarith
    have hpos : 0 < u * m / (z - e * u) ^ 2 := by
      have : 0 < z - e * u := by nlinarith
      positivity
    have hcv := scOutC_k_cv hm he hw hu hs c₀ c₁ c₂ c₃ hz
    rw [← abs_of_pos hpos, ← abs_mul, hcv]
    set f := 1 / (z * (m - e * u + z)) with hf
    have hf0 : 0 < f := by positivity
    have e2 : 1 / (z ^ 2 * (m - e * u + z)) = f * (1 / z) := by rw [hf]; field_simp
    have e3 : 1 / (z ^ 3 * (m - e * u + z)) = f * (1 / z) ^ 2 := by rw [hf]; field_simp
    have hβ : 0 < w * (s + e) := by positivity
    have hρ : 0 < u / w * (1 / z) := by positivity
    have hρβ : u / w * (1 / z) ≤ 1 / (w * (s + e)) := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) hβ, one_mul]
      nlinarith [mul_lt_mul_of_pos_left hz' hw]
    have key := scOutC_abs_quad_le hρ hρβ c₁ c₂ c₃
    rw [e2, e3]
    calc |c₁ * f + c₂ * (u / w) * (f * (1 / z)) + c₃ * (u / w) ^ 2 * (f * (1 / z) ^ 2)| =
          |c₁ + c₂ * (u / w * (1 / z)) + c₃ * (u / w * (1 / z)) ^ 2| * f := by
          rw [← abs_of_pos hf0, ← abs_mul, abs_of_pos hf0]
          ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right key hf0.le

/-- The `κ`-part in absolute value. -/
theorem scOutC_abs_kap (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u) (hs : 0 ≤ s)
    (hM : m - e * u ≠ 0) (a₀ a₁ a₂ : ℝ) :
    ∫ v in Ioi 0, |scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2| ≤
      (|a₀| + |a₁| / (w * (s + e)) + |a₂| / (w * (s + e)) ^ 2) * (w / u) *
        (1 / (m + s * u)) := by
  have hc : 0 < (s + e) * u := by positivity
  have hMc : 0 < m - e * u + (s + e) * u := by nlinarith [mul_nonneg hs hu.le]
  have hA : m - e * u + (s + e) * u = m + s * u := by ring
  obtain ⟨j0, w0⟩ := scOutCI0 hMc
  have hI : IntegrableOn (fun v => |scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2|) (Ioi 0) :=
    Integrable.abs (scOutC_kap_int hm he hw hu hs hM a₀ a₁ a₂).1
  have hS : IntegrableOn (fun v => |scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2|)
      (scOutCS m s) := hI.mono_set fun v hv => hv.1
  have hR : IntegrableOn (fun v => |scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2|)
      (scOutCR m s) := hI.mono_set fun v hv => hv.1
  have hR0 : EqOn (fun v => |scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2|) 0 (scOutCR m s) :=
    fun v hv => by
      have h' : ¬ s * v < m := not_lt.2 hv.2
      simp [scOutCkap, h']
  rw [← scOutCS_union, setIntegral_union scOutCS_disjoint (measurableSet_scOutCR m s) hS hR,
    setIntegral_congr_fun (measurableSet_scOutCR m s) hR0]
  simp only [Pi.zero_apply, integral_zero, add_zero]
  obtain ⟨-, hval⟩ := scOutC_cv (e := e) hm hu hs
    (fun v => |scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2|)
  rw [hval, ← hA, ← w0, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ (j0.const_mul _) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have : 0 < z - e * u := by rw [mem_Ioi] at hz; nlinarith
    positivity
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz' : (s + e) * u < z := hz
    have hz0 : 0 < z := hc.trans hz'
    have hD : 0 < m - e * u + z := by linarith
    have hpos : 0 < u * m / (z - e * u) ^ 2 := by
      have : 0 < z - e * u := by nlinarith
      positivity
    have hcv := scOutC_kap_cv hm he hw hu hs a₀ a₁ a₂ hz
    rw [← abs_of_pos hpos, ← abs_mul, hcv]
    set f := 1 / (m - e * u + z) ^ 2 with hf
    have hf0 : 0 < f := by positivity
    have e1 : 1 / (z * (m - e * u + z) ^ 2) = w / u * (u / w * (1 / z)) * f := by
      rw [hf]; field_simp
    have e2 : u / w * (1 / (z ^ 2 * (m - e * u + z) ^ 2)) =
        w / u * (u / w * (1 / z)) ^ 2 * f := by
      rw [hf]; field_simp
    have hβ : 0 < w * (s + e) := by positivity
    have hρ : 0 < u / w * (1 / z) := by positivity
    have hρβ : u / w * (1 / z) ≤ 1 / (w * (s + e)) := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) hβ, one_mul]
      nlinarith [mul_lt_mul_of_pos_left hz' hw]
    have key := scOutC_abs_quad_le hρ hρβ a₀ a₁ a₂
    have hwu : 0 < w / u := by positivity
    calc |a₀ * (w / u) * f + a₁ * (1 / (z * (m - e * u + z) ^ 2)) +
          a₂ * (u / w) * (1 / (z ^ 2 * (m - e * u + z) ^ 2))| =
          |a₀ + a₁ * (u / w * (1 / z)) + a₂ * (u / w * (1 / z)) ^ 2| * (w / u) * f := by
          have h : a₀ * (w / u) * f + a₁ * (1 / (z * (m - e * u + z) ^ 2)) +
              a₂ * (u / w) * (1 / (z ^ 2 * (m - e * u + z) ^ 2)) =
              (a₀ + a₁ * (u / w * (1 / z)) + a₂ * (u / w * (1 / z)) ^ 2) * (w / u * f) := by
            rw [e1, mul_assoc a₂, e2]; ring
          rw [h, abs_mul, abs_of_pos (mul_pos hwu hf0)]
          ring
      _ ≤ _ := by gcongr

/-- The `k`-part beyond the threshold, in absolute value. -/
theorem scOutC_abs_k_R (hm : 0 < m) (hw : 0 < w) (hu : 0 < u) (hs : 0 ≤ s)
    (c₀ c₁ c₂ c₃ : ℝ) :
    ∫ v in scOutCR m s, |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)| =
      |c₀| * w * ((log (m + s * u) - log m) / u) := by
  obtain ⟨-, vR⟩ := scOutC_k_R (e := e) (w := w) hm hu hs (-|c₀|) c₁ c₂ c₃
  have hcg : EqOn (fun v => |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)|)
      (fun v => scOutCk (-|c₀|) c₁ c₂ c₃ m e w s v / (u + v)) (scOutCR m s) := fun v hv => by
    have h' : ¬ s * v < m := not_lt.2 hv.2
    have hv0 : 0 < v := hv.1
    simp only [scOutCk, h', ↓reduceIte]
    rw [abs_div, abs_neg, abs_div, abs_mul, abs_of_pos hw, abs_of_pos hv0,
      abs_of_pos (by linarith : 0 < u + v)]
    ring
  rw [setIntegral_congr_fun (measurableSet_scOutCR m s) hcg, vR]
  ring

/-- **The absolute bound for the outer-massive corner weight.** -/
theorem scOutCTg_abs_integral_le (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u)
    (hs : 0 ≤ s) (hM : m - e * u ≠ 0) (a₀ a₁ a₂ c₀ c₁ c₂ c₃ : ℝ) :
    ∫ v in Ioi 0, |scOutCTg a₀ a₁ a₂ c₀ c₁ c₂ c₃ m e w s v / (u + v) ^ 2| ≤
      (|c₁| + |c₂| / (w * (s + e)) + |c₃| / (w * (s + e)) ^ 2) *
          (log (1 + (m - e * u) / ((s + e) * u)) / (m - e * u)) +
        (|a₀| + |a₁| / (w * (s + e)) + |a₂| / (w * (s + e)) ^ 2) * (w / u) *
          (1 / (m + s * u)) +
        |c₀| * w * ((log (m + s * u) - log m) / u) + |c₀ * w * log m| * (1 / u) := by
  set k := scOutCk c₀ c₁ c₂ c₃ m e w s with hk
  set κ := scOutCkap a₀ a₁ a₂ m e w s with hκ
  set P := c₀ * w * log m with hP
  have hkm : Measurable fun v => |k v| := continuous_abs.measurable.comp
    (measurable_scOutCk c₀ c₁ c₂ c₃ m e w s)
  have hkI : IntegrableOn (fun v => |k v / (u + v)|) (Ioi 0) :=
    Integrable.abs (scOutC_k_int hm he hw hu hs hM c₀ c₁ c₂ c₃).1
  have hkI' : IntegrableOn (fun v => |k v| / (u + v)) (Ioi 0) := by
    refine hkI.congr_fun (fun v hv => ?_) measurableSet_Ioi
    have : 0 < u + v := by linarith [mem_Ioi.1 hv]
    simp only [hk]
    rw [abs_div, abs_of_pos this]
  obtain ⟨iK, vK⟩ := scOutC_ibp hu hkm hkI'
  have iκ : IntegrableOn (fun v => |κ v / (u + v) ^ 2|) (Ioi 0) :=
    Integrable.abs (scOutC_kap_int hm he hw hu hs hM a₀ a₁ a₂).1
  obtain ⟨i0, v0⟩ := scOutCI0 (M := u) (c := 0) (by simpa using hu)
  have i0' : IntegrableOn (fun v => |P| * (1 / (u + v) ^ 2)) (Ioi 0) := i0.const_mul _
  obtain ⟨i3, e3⟩ := scOutC_add3 iK iκ i0'
  have hle : ∫ v in Ioi 0, |scOutCTg a₀ a₁ a₂ c₀ c₁ c₂ c₃ m e w s v / (u + v) ^ 2| ≤
      ∫ v in Ioi 0, ((∫ v' in Ioc 0 v, |k v'|) / (u + v) ^ 2 + |κ v / (u + v) ^ 2| +
        |P| * (1 / (u + v) ^ 2)) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) i3 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have huv0 : 0 < u + v := by linarith [mem_Ioi.1 hv]
    have huv : 0 < (u + v) ^ 2 := by positivity
    have hK : |∫ v' in Ioc 0 v, k v'| ≤ ∫ v' in Ioc 0 v, |k v'| := abs_integral_le_integral_abs
    unfold scOutCTg scOutCK
    rw [← hk, ← hκ, abs_div, abs_of_pos huv, abs_div, abs_of_pos huv, ← hP]
    have : |(∫ v' in Ioc 0 v, k v') + κ v + -P| ≤ (∫ v' in Ioc 0 v, |k v'|) + |κ v| + |P| := by
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
      · exact add_le_add hK le_rfl
      · rw [abs_neg]
    calc |(∫ v' in Ioc 0 v, k v') + κ v + -P| / (u + v) ^ 2 ≤
          ((∫ v' in Ioc 0 v, |k v'|) + |κ v| + |P|) / (u + v) ^ 2 := by gcongr
      _ = _ := by ring
  refine hle.trans ?_
  rw [e3, vK, integral_const_mul, v0, add_zero]
  have hkk : ∫ v in Ioi 0, |k v| / (u + v) = ∫ v in Ioi 0, |k v / (u + v)| := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have : 0 < u + v := by linarith [mem_Ioi.1 hv]
    rw [abs_div, abs_of_pos this]
  have hS : IntegrableOn (fun v => |k v / (u + v)|) (scOutCS m s) := hkI.mono_set fun v hv => hv.1
  have hR : IntegrableOn (fun v => |k v / (u + v)|) (scOutCR m s) := hkI.mono_set fun v hv => hv.1
  have hsplit : ∫ v in Ioi 0, |k v / (u + v)| =
      (∫ v in scOutCS m s, |k v / (u + v)|) + ∫ v in scOutCR m s, |k v / (u + v)| := by
    rw [← scOutCS_union, setIntegral_union scOutCS_disjoint (measurableSet_scOutCR m s) hS hR]
  rw [hkk, hsplit, hk, scOutC_abs_k_R hm hw hu hs]
  have h1 := scOutC_abs_k_S hm he hw hu hs hM c₀ c₁ c₂ c₃
  have h2 := scOutC_abs_kap hm he hw hu hs hM a₀ a₁ a₂
  rw [← hκ] at h2
  linarith

/-- **The master bound**: `log(1 + M/z₀)/M ≤ 2 (1 + log(1 + a/z₀))/a`, `a = M + z₀`. -/
theorem scOutC_J1_le {M z : ℝ} (hz : 0 < z) (ha : 0 < M + z) (hM : M ≠ 0) :
    log (1 + M / z) / M ≤ 2 * (1 + log (1 + (M + z) / z)) / (M + z) := by
  set a := M + z with hadef
  have hr : 1 + M / z = a / z := by rw [hadef]; field_simp; ring
  have hr0 : 0 < a / z := div_pos ha hz
  have hL0 : 0 ≤ log (1 + a / z) := log_nonneg (by linarith)
  rw [hr]
  rcases lt_or_gt_of_ne hM with hneg | hpos
  · -- `a < z`: `log(a/z)/M ≤ 1/a`.
    have h1 : log (a / z) / M ≤ 1 / a := by
      rw [div_le_iff_of_neg hneg]
      have hlog : 1 - z / a ≤ log (a / z) := by
        have := log_le_sub_one_of_pos (div_pos hz ha)
        rw [log_div hz.ne' ha.ne'] at this
        rw [log_div ha.ne' hz.ne']
        linarith
      have hMa : M = a - z := by rw [hadef]; ring
      have : 1 / a * M = 1 - z / a := by rw [hMa]; field_simp
      rw [this]
      exact hlog
    calc log (a / z) / M ≤ 1 / a := h1
      _ ≤ 2 * (1 + log (1 + a / z)) / a := by
        rw [div_le_div_iff_of_pos_right ha]; linarith
  · -- `a > z`: `log(a/z) ≤ M/z`.
    have hlog : log (a / z) ≤ M / z := by
      have := log_le_sub_one_of_pos hr0
      have e : a / z - 1 = M / z := by rw [hadef]; field_simp; ring
      linarith
    by_cases h2 : a ≤ 2 * z
    · calc log (a / z) / M ≤ M / z / M := by gcongr
        _ = 1 / z := by field_simp
        _ ≤ 2 / a := by rw [div_le_div_iff₀ hz ha]; linarith
        _ ≤ 2 * (1 + log (1 + a / z)) / a := by
          rw [div_le_div_iff_of_pos_right ha]; linarith
    · have hMa : a / 2 ≤ M := by rw [hadef] at h2 ⊢; linarith
      have hl0 : 0 ≤ log (a / z) := log_nonneg (by rw [le_div_iff₀ hz]; linarith)
      have hl1 : log (a / z) ≤ log (1 + a / z) := log_le_log hr0 (by linarith)
      calc log (a / z) / M ≤ log (a / z) / (a / 2) := div_le_div_of_nonneg_left hl0
            (by positivity) hMa
        _ = 2 * log (a / z) / a := by field_simp
        _ ≤ 2 * (1 + log (1 + a / z)) / a := by
          rw [div_le_div_iff_of_pos_right ha]; linarith

end

end QED.ChainProof.SetCK

end
