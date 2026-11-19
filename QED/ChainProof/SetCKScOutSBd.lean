/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutW
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the size of the self-energy `(u + v)⁻²`-weight

Helper level (no frozen statement). For the weight `scOutTg α β V p` of `SetCKScOutW` and
`u, V > 0` (**`scOutTg_abs_integral_le`**):

`∫₀^∞ |T(v)|/(u + v)² dv ≤ (5|α|/2 + |p|)/u + 3|β|/u² + (3|α|/2 + |p|)/(u + V)
  + |α| log(1 + u/V)/u + |β| log(1 + u/V)/u²`.

On `(0, V]` the weight is bounded by `5|α|/2 + 3|β|/V + |p|`; beyond `V` it is bounded by
`3|α|/2 + |α| log(v/V) + |β|/v + |p|`, whose integrals are the masters of `SetCKCrossTW`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

section

variable {α β V p u : ℝ}

theorem abs_scOutTg_le_of_le {v : ℝ} (hV : 0 < V) (hv0 : 0 < v) (hv : v ≤ V) :
    |scOutTg α β V p v| ≤ 5 / 2 * |α| + 3 * |β| / V + |p| := by
  simp only [scOutTg, hv, ↓reduceIte]
  have h1 : |v ^ 2 / (2 * V ^ 2) - 2 * v / V| ≤ 5 / 2 := by
    have a1 : 0 ≤ v ^ 2 / (2 * V ^ 2) := by positivity
    have a2 : v ^ 2 / (2 * V ^ 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have a3 : 0 ≤ 2 * v / V := by positivity
    have a4 : 2 * v / V ≤ 2 := by
      rw [div_le_iff₀ hV]
      linarith
    rw [abs_le]
    constructor <;> linarith
  have h2 : |v / V ^ 2 - 2 / V| ≤ 3 / V := by
    have a1 : 0 ≤ v / V ^ 2 := by positivity
    have a2 : v / V ^ 2 ≤ 1 / V := by
      rw [div_le_div_iff₀ (by positivity) hV]
      nlinarith
    have a3 : 2 / V = 2 * (1 / V) := by ring
    have a4 : 3 / V = 3 * (1 / V) := by ring
    have a5 : 0 < 1 / V := by positivity
    rw [abs_le, a3, a4]
    constructor <;> linarith
  calc |α * (v ^ 2 / (2 * V ^ 2) - 2 * v / V) + β * (v / V ^ 2 - 2 / V) + p|
      ≤ |α * (v ^ 2 / (2 * V ^ 2) - 2 * v / V)| + |β * (v / V ^ 2 - 2 / V)| + |p| :=
        abs_add_three _ _ _
    _ ≤ |α| * (5 / 2) + |β| * (3 / V) + |p| := by
        rw [abs_mul, abs_mul]
        gcongr
    _ = 5 / 2 * |α| + 3 * |β| / V + |p| := by ring

theorem abs_scOutTg_le_of_lt {v : ℝ} (hV : 0 < V) (hv : V < v) :
    |scOutTg α β V p v| ≤ (3 / 2 * |α| + |p|) + |α| * log (v / V) + |β| * (1 / v) := by
  rw [scOutTg_of_lt hv]
  have hv0 : 0 < v := hV.trans hv
  have hl : 0 ≤ log (v / V) := log_nonneg (by rw [le_div_iff₀ hV]; linarith)
  have hs : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  have h32 : |(3 / 2 : ℝ)| = 3 / 2 := abs_of_pos (by norm_num)
  calc |-(3 / 2 * α) - α * log (v / V) - β / v + p|
      ≤ |-(3 / 2 * α) - α * log (v / V) - β / v| + |p| := abs_add_le _ _
    _ ≤ |-(3 / 2 * α) - α * log (v / V)| + |β / v| + |p| := by gcongr; exact hs _ _
    _ ≤ |-(3 / 2 * α)| + |α * log (v / V)| + |β / v| + |p| := by gcongr; exact hs _ _
    _ = (3 / 2 * |α| + |p|) + |α| * log (v / V) + |β| * (1 / v) := by
        rw [abs_neg, abs_mul, abs_mul, abs_div β v, abs_of_nonneg hl, abs_of_pos hv0, h32]
        ring

/-- **The size of the self-energy weight.** -/
theorem scOutTg_abs_integral_le (hu : 0 < u) (hV : 0 < V) :
    ∫ v in Ioi 0, |scOutTg α β V p v / (u + v) ^ 2| ≤
      (5 / 2 * |α| + |p|) / u + 3 * |β| / u ^ 2 + (3 / 2 * |α| + |p|) / (u + V) +
        |α| * (log (1 + u / V) / u) + |β| * (log (1 + u / V) / u ^ 2) := by
  have hI : IntegrableOn (fun v => |scOutTg α β V p v / (u + v) ^ 2|) (Ioi 0) :=
    (integrableOn_scOutTg hu hV).abs
  rw [← Ioc_union_Ioi_eq_Ioi hV.le] at hI ⊢
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hI.mono_set subset_union_left) (hI.mono_set subset_union_right)]
  -- the part `(0, V]`
  set K := 5 / 2 * |α| + 3 * |β| / V + |p| with hK
  obtain ⟨iq, vq⟩ := scOut_integral_quad hu hV K 0 0
  have hq : ∀ v, (K + 0 * v + 0 * v ^ 2) / (u + v) ^ 2 = K / (u + v) ^ 2 := fun v => by ring
  simp only [hq] at iq vq
  have b1 : ∫ v in Ioc 0 V, |scOutTg α β V p v / (u + v) ^ 2| ≤
      ∫ v in Ioc 0 V, K / (u + v) ^ 2 := by
    refine setIntegral_mono_on (hI.mono_set subset_union_left) iq measurableSet_Ioc
      fun v hv => ?_
    have huv : 0 < u + v := by linarith [hv.1]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (u + v) ^ 2)]
    exact div_le_div_of_nonneg_right (abs_scOutTg_le_of_le hV hv.1 hv.2) (by positivity)
  have e1 : ∫ v in Ioc 0 V, K / (u + v) ^ 2 =
      (5 / 2 * |α| + |p|) * (1 / u - 1 / (u + V)) + 3 * |β| / (u * (u + V)) := by
    rw [vq, hK]
    have := hu.ne'
    have := hV.ne'
    have : u + V ≠ 0 := by positivity
    field_simp
    ring
  -- the part `(V, ∞)`
  obtain ⟨i0, v0⟩ := crossTIoi0 hu hV
  obtain ⟨i1, v1⟩ := crossTIoi1 hu hV
  obtain ⟨iL, vL⟩ := crossTIoiL hu hV
  have j0 := i0.const_mul (3 / 2 * |α| + |p|)
  have jL := iL.const_mul |α|
  have j1 := i1.const_mul |β|
  have j01 : IntegrableOn (fun v => (3 / 2 * |α| + |p|) * (1 / (u + v) ^ 2) +
      |α| * (log (v / V) / (u + v) ^ 2)) (Ioi V) := j0.add jL
  have b2 : ∫ v in Ioi V, |scOutTg α β V p v / (u + v) ^ 2| ≤
      ∫ v in Ioi V, ((3 / 2 * |α| + |p|) * (1 / (u + v) ^ 2) +
        |α| * (log (v / V) / (u + v) ^ 2) + |β| * (1 / (v * (u + v) ^ 2))) := by
    refine setIntegral_mono_on (hI.mono_set subset_union_right) (j01.add j1) measurableSet_Ioi
      fun v hv => ?_
    have hv0 : 0 < v := hV.trans hv
    have huv : 0 < u + v := by linarith
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (u + v) ^ 2)]
    calc |scOutTg α β V p v| / (u + v) ^ 2
        ≤ ((3 / 2 * |α| + |p|) + |α| * log (v / V) + |β| * (1 / v)) / (u + v) ^ 2 :=
          div_le_div_of_nonneg_right (abs_scOutTg_le_of_lt hV hv) (by positivity)
      _ = _ := by
          have := hv0.ne'
          have := huv.ne'
          field_simp
  have e2 : ∫ v in Ioi V, ((3 / 2 * |α| + |p|) * (1 / (u + v) ^ 2) +
      |α| * (log (v / V) / (u + v) ^ 2) + |β| * (1 / (v * (u + v) ^ 2))) =
      (3 / 2 * |α| + |p|) * (1 / (u + V)) + |α| * (log (1 + u / V) / u) +
        |β| * (log (1 + u / V) / u ^ 2 - 1 / (u * (u + V))) := by
    rw [integral_add j01 j1, integral_add j0 jL, integral_const_mul, integral_const_mul,
      integral_const_mul, v0, v1, vL]
  have hpos : 0 ≤ (5 / 2 * |α| + |p|) * (1 / (u + V)) := by positivity
  have hb : 0 ≤ |β| := abs_nonneg β
  have hβu : 3 * |β| / (u * (u + V)) ≤ 3 * |β| / u ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have hβu' : 0 ≤ |β| * (1 / (u * (u + V))) := by positivity
  have hsplit : (5 / 2 * |α| + |p|) * (1 / u - 1 / (u + V)) =
      (5 / 2 * |α| + |p|) / u - (5 / 2 * |α| + |p|) * (1 / (u + V)) := by ring
  calc _ ≤ (∫ v in Ioc 0 V, K / (u + v) ^ 2) + ∫ v in Ioi V, ((3 / 2 * |α| + |p|) *
        (1 / (u + v) ^ 2) + |α| * (log (v / V) / (u + v) ^ 2) +
          |β| * (1 / (v * (u + v) ^ 2))) := add_le_add b1 b2
    _ ≤ _ := by
        rw [e1, e2, hsplit]
        have : |β| * (log (1 + u / V) / u ^ 2 - 1 / (u * (u + V))) =
            |β| * (log (1 + u / V) / u ^ 2) - |β| * (1 / (u * (u + V))) := by ring
        rw [this]
        have h3 : (3 / 2 * |α| + |p|) * (1 / (u + V)) = (3 / 2 * |α| + |p|) / (u + V) := by ring
        rw [h3]
        linarith

end

end QED.ChainProof.SetCK

end
