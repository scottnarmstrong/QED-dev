/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutCMast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the corner weight of the outer-massive corner

Helper level (no frozen statement). In the corner with the outer photon of mass² `t`
(`cornerGm (√t) 0`) the `b`-denominator is `M + b h = m + s u` with `u = Q(x) + t`,
`m = Y² + e Q(x)` (independent of `t`), `w = x/(1-x)`, `s = b/w - e`. Substituting
`v = m/s` (so `M + b h = s (u + v)`, `1/b = r = v/(w (m + e v))`), the `b`-integral over
`b > β` becomes a `v`-integral over `{v > 0 : s₀ v < m}`, `s₀ = β/w - e ≥ 0`, of
`k(v)/(u + v) + κ(v)/(u + v)²`, plus the large-`b` logarithm as a weight `-c₀ w/v` beyond the
threshold and a pole `P/u`, `P = -c₀ w log m`:

* `k(v) = c₁/(m + e v) + c₂ v/(w (m + e v)²) + c₃ v²/(w² (m + e v)³)` if `s₀ v < m`,
  `k(v) = -c₀ w/v` otherwise (`scOutCk`);
* `κ(v) = (w/m)(a₀ + a₁ r + a₂ r²)` if `s₀ v < m`, `0` otherwise (`scOutCkap`).

The branch test `s₀ v < m` (no division) is the branch of `betaG`: on its second branch
`s₀ = 0` and the threshold is absent.

**The `(u + v)⁻²`-weight** is `T(v) = K(v) + κ(v) + P` with `K(v) = ∫₀^v k` (`scOutCTg`):
by Fubini (**`scOutC_ibp`**), `∫₀^∞ K(v)/(u + v)² dv = ∫₀^∞ k(v)/(u + v) dv` whenever the
right side converges absolutely (an integration by parts without boundary terms).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

/-- The `(u + v)⁻¹`-weight `k` of the outer-massive corner. -/
noncomputable def scOutCk (c₀ c₁ c₂ c₃ m e w s v : ℝ) : ℝ :=
  if s * v < m then
    c₁ / (m + e * v) + c₂ * v / (w * (m + e * v) ^ 2) + c₃ * v ^ 2 / (w ^ 2 * (m + e * v) ^ 3)
  else -(c₀ * w / v)

/-- The `(u + v)⁻²`-weight `κ` of the outer-massive corner. -/
noncomputable def scOutCkap (a₀ a₁ a₂ m e w s v : ℝ) : ℝ :=
  if s * v < m then
    w / m * (a₀ + a₁ * (v / (w * (m + e * v))) + a₂ * (v / (w * (m + e * v))) ^ 2)
  else 0

/-- `K(v) = ∫₀^v k`. -/
noncomputable def scOutCK (c₀ c₁ c₂ c₃ m e w s v : ℝ) : ℝ :=
  ∫ v' in Ioc 0 v, scOutCk c₀ c₁ c₂ c₃ m e w s v'

/-- **The `(u + v)⁻²`-weight of the outer-massive corner**: `T = K + κ + P`. -/
noncomputable def scOutCTg (a₀ a₁ a₂ c₀ c₁ c₂ c₃ m e w s v : ℝ) : ℝ :=
  scOutCK c₀ c₁ c₂ c₃ m e w s v + scOutCkap a₀ a₁ a₂ m e w s v + -(c₀ * w * log m)

theorem measurable_scOutCk (c₀ c₁ c₂ c₃ m e w s : ℝ) :
    Measurable (scOutCk c₀ c₁ c₂ c₃ m e w s) := by
  unfold scOutCk
  exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop)
    (by fun_prop)

section

variable {u : ℝ}

/-- A cut-off section: `∫_{v > 0} 1{v' < v} a/(u + v)² dv = a/(u + v')`. -/
theorem scOutC_cut (hu : 0 < u) {v' : ℝ} (hv' : 0 < v') (a : ℝ) :
    IntegrableOn (fun v => (if v' < v then a else 0) * (1 / (u + v) ^ 2)) (Ioi 0) ∧
      ∫ v in Ioi 0, (if v' < v then a else 0) * (1 / (u + v) ^ 2) = a * (1 / (u + v')) := by
  obtain ⟨i0, v0⟩ := crossTIoi0 hu hv'
  have he : (fun v => (if v' < v then a else 0) * (1 / (u + v) ^ 2)) =
      (Ioi v').indicator fun v => a * (1 / (u + v) ^ 2) := by
    funext v
    by_cases h : v' < v
    · simp [h]
    · simp [h]
  have hsub : Ioi (0 : ℝ) ∩ Ioi v' = Ioi v' := inter_eq_right.2 (Ioi_subset_Ioi hv'.le)
  rw [he]
  have i1 : IntegrableOn (fun v => a * (1 / (u + v) ^ 2)) (Ioi v') := i0.const_mul a
  refine ⟨(i1.integrable_indicator measurableSet_Ioi).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ioi, hsub, integral_const_mul, v0]

/-- **The integration by parts by Fubini**: `∫₀^∞ (∫₀^v k)/(u + v)² dv = ∫₀^∞ k/(u + v) dv`. -/
theorem scOutC_ibp (hu : 0 < u) {k : ℝ → ℝ} (hkm : Measurable k)
    (hk : IntegrableOn (fun v => k v / (u + v)) (Ioi 0)) :
    IntegrableOn (fun v => (∫ v' in Ioc 0 v, k v') / (u + v) ^ 2) (Ioi 0) ∧
      ∫ v in Ioi 0, (∫ v' in Ioc 0 v, k v') / (u + v) ^ 2 = ∫ v in Ioi 0, k v / (u + v) := by
  set μ := volume.restrict (Ioi (0 : ℝ))
  set F : ℝ × ℝ → ℝ := fun q => (if q.1 < q.2 then k q.1 else 0) * (1 / (u + q.2) ^ 2)
    with hF
  have hFm : Measurable F :=
    (Measurable.ite (measurableSet_lt measurable_fst measurable_snd) (hkm.comp measurable_fst)
      measurable_const).mul (measurable_const.div
        ((measurable_const.add measurable_snd).pow_const 2))
  have hsec : ∀ v' ∈ Ioi (0 : ℝ), Integrable (fun v => F (v', v)) μ ∧
      ∫ v, F (v', v) ∂μ = k v' / (u + v') := fun v' hv' => by
    obtain ⟨hi, hv⟩ := scOutC_cut hu hv' (k v')
    exact ⟨hi, hv.trans (by ring)⟩
  have hnorm : ∀ v' ∈ Ioi (0 : ℝ), ∫ v, ‖F (v', v)‖ ∂μ = |k v'| / (u + v') := fun v' hv' => by
    have e : (fun v => ‖F (v', v)‖) =
        fun v => (if v' < v then |k v'| else 0) * (1 / (u + v) ^ 2) := by
      funext v
      simp only [hF, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (u + v) ^ 2)]
      split_ifs <;> simp
    rw [e, (scOutC_cut hu hv' |k v'|).2]
    ring
  have H : Integrable F (μ.prod μ) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v' hv'
      exact (hsec v' hv').1
    · refine hk.norm.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v' hv'
      have : 0 < u + v' := by linarith [mem_Ioi.1 hv']
      rw [hnorm v' hv', Real.norm_eq_abs, abs_div, abs_of_pos this]
  have hK : ∀ v ∈ Ioi (0 : ℝ), ∫ v', F (v', v) ∂μ =
      (∫ v' in Ioc 0 v, k v') / (u + v) ^ 2 := fun v hv => by
    have e : (fun v' => F (v', v)) = fun v' => (Iio v).indicator k v' * (1 / (u + v) ^ 2) := by
      funext v'
      simp only [hF, indicator, mem_Iio]
    rw [e, integral_mul_const, integral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio]
    have : Iio v ∩ Ioi (0 : ℝ) = Ioo 0 v := by
      ext y; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]; tauto
    rw [this, ← integral_Ioc_eq_integral_Ioo]
    ring
  refine ⟨H.integral_prod_right.congr ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hK v hv
  · have hswap := integral_integral_swap (f := fun v' v => F (v', v)) H
    have l : ∫ v', ∫ v, F (v', v) ∂μ ∂μ = ∫ v in Ioi 0, k v / (u + v) :=
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v' hv'
        exact (hsec v' hv').2)
    have r : ∫ v, ∫ v', F (v', v) ∂μ ∂μ =
        ∫ v in Ioi 0, (∫ v' in Ioc 0 v, k v') / (u + v) ^ 2 :=
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        exact hK v hv)
    rw [← l, ← r, hswap]

end

end QED.ChainProof.SetCK

end
