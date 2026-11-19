/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfSub
public import QED.OneLoop.FormFactorSmooth
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-loop Pauli functional of a photon function at `q² = s`, and its limit `s → 0⁺`

Helper level, Phase 5 Stage 1a, toward `QED.ChainProof.ChainPauliAtLink` (obligations O3-9 and
O3-10 of `docs/HIGHER-LOOP-PLAN.md`). The vertex of an open line of mass `m` with one photon line
whose propagator is replaced by a photon function `R(k²)` (Euclidean `k²`) has, at `q² = s`, the
Pauli form factor `e² outerAt m s R` at charge `e`, with

`outerAt m s R = (1/(8π²)) ∫ 2 y² m² R(K) dx dy`, `K = y² (m² + x(1-x) s)/(1-y)`

over the Feynman square (`QED.TwoLoop.VPHalf.vpK`). This is the normalization of the fixed-`q`
outer form of the two-loop VP class (`QED.TwoLoop.VPHalf.vpHalfSubAt_iff_outer`, photon function
`Π_loop(k²) k² D(k²)²`). Nothing here refers to a vertex: the statements are about the explicit
functional.

## Main statements

* `outerAt_zero`: `outerAt m 0 R = m² (1/(4π²)) ∫₀¹ y² R(m² y²/(1-y)) dy`; at `m = 1` it is
  `QED.TwoLoop.UnitVPLink.outerF2 R` (`outerAt_one_zero`).
* `tendsto_outerAt` (**the `q² → 0⁺` step at fixed regulators**): for `m > 0` and a measurable
  photon function `R` that is continuous on `(0, ∞)` and bounded on `[0, ∞)`,
  `outerAt m s R → outerAt m 0 R` as `s → 0⁺` (dominated convergence on the square).
* `outerAt_congr`: `outerAt m s` only reads `R` on `[0, ∞)` (for `s ≥ 0`).
* `outerAt_add`, `outerAt_const_mul`, `outerAt_sum`: linearity, given integrability of the
  integrands (`IntegrableAt`); `integrableAt_of_bound` gives it from a bound on `[0, ∞)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.HCValue

open QED.TwoLoop.UnitVPLink QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalf
open QED.Integration (feynmanMeasure)

/-- **The one-loop Pauli functional at `q² = s` for the photon function `R`** (unit charge):
`(1/(8π²)) ∫ 2 y² m² R(K) dx dy` over the Feynman square, `K = y² (m² + x(1-x) s)/(1-y)`. -/
noncomputable def outerAt (m s : ℝ) (R : ℝ → ℝ) : ℝ :=
  1 / (8 * π ^ 2) * ∫ z, 2 * (z.2 ^ 2 * m ^ 2 * R (vpK m s z)) ∂feynmanMeasure

/-- At `q² = 0` the photon variable is `m² y²/(1-y)`. -/
theorem vpK_zero (m : ℝ) (z : ℝ × ℝ) : vpK m 0 z = m ^ 2 * photonVar z.2 := by
  simp only [vpK, kC, photonVar]
  ring

/-- `K ≥ 0` on the closed square for `s ≥ 0`. -/
theorem vpK_nonneg {m s : ℝ} (hs : 0 ≤ s) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) : 0 ≤ vpK m s z := by
  unfold vpK kC
  have h0 : 0 ≤ z.1 * (1 - z.1) := mul_nonneg hz.1.1 (by linarith [hz.1.2])
  have h1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  positivity

/-- `K > 0` on the open square for `s ≥ 0` and `m ≠ 0`. -/
theorem vpK_pos {m s : ℝ} (hm : m ≠ 0) (hs : 0 ≤ s) {z : ℝ × ℝ}
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) : 0 < vpK m s z := by
  unfold vpK kC
  have h0 : 0 ≤ z.1 * (1 - z.1) := mul_nonneg hz.1.1.le (by linarith [hz.1.2])
  have h1 : 0 < 1 - z.2 := by linarith [hz.2.2]
  have hy : 0 < z.2 := hz.2.1
  have hm2 : 0 < m ^ 2 := by positivity
  positivity

theorem ae_mem_square :
    ∀ᵐ z ∂feynmanMeasure, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  have h1 : ∀ᵐ z ∂feynmanMeasure, z.2 ≠ 1 := by
    rw [QED.Integration.feynmanMeasure]
    have : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) 1)), y ≠ 1 :=
      ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
    exact (Measure.quasiMeasurePreserving_snd).ae this
  filter_upwards [QED.OneLoop.VertexLimit.ae_feynmanMeasure, h1] with z hz h
  exact ⟨hz.1, hz.2.1, lt_of_le_of_ne hz.2.2 h⟩

/-- **The functional at `q² = 0`**: `outerAt m 0 R = m² (1/(4π²)) ∫₀¹ y² R(m² y²/(1-y)) dy`. -/
theorem outerAt_zero (m : ℝ) (R : ℝ → ℝ) :
    outerAt m 0 R =
      m ^ 2 * (1 / (4 * π ^ 2) * ∫ y in (0 : ℝ)..1, y ^ 2 * R (m ^ 2 * photonVar y)) := by
  unfold outerAt
  have h : (fun z : ℝ × ℝ => 2 * (z.2 ^ 2 * m ^ 2 * R (vpK m 0 z))) =
      fun z => (fun y => (2 * m ^ 2) * (y ^ 2 * R (m ^ 2 * photonVar y))) z.2 := by
    funext z
    rw [vpK_zero]
    ring
  have key := integral_fun_snd (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (fun y => (2 * m ^ 2) * (y ^ 2 * R (m ^ 2 * photonVar y)))
  rw [h, QED.Integration.feynmanMeasure, key, integral_const_mul,
    ← intervalIntegral.integral_of_le zero_le_one]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal zero_le_one, one_smul]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- At `m = 1`, `q² = 0` the functional is the one-loop `F₂(0)` functional `outerF2`. -/
theorem outerAt_one_zero (R : ℝ → ℝ) : outerAt 1 0 R = outerF2 R := by
  rw [outerAt_zero]
  simp only [one_pow, one_mul, outerF2]

/-- `outerAt m s` reads `R` only on `[0, ∞)`, for `s ≥ 0`. -/
theorem outerAt_congr {m s : ℝ} (hs : 0 ≤ s) {R R' : ℝ → ℝ} (h : ∀ t, 0 ≤ t → R t = R' t) :
    outerAt m s R = outerAt m s R' := by
  unfold outerAt
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [QED.OneLoop.VertexLimit.ae_feynmanMeasure_mem_Icc] with z hz
  rw [h _ (vpK_nonneg hs hz)]

/-- **The `q² → 0⁺` limit at fixed regulators.** For `m > 0` and a measurable photon function
`R`, continuous on `(0, ∞)` and bounded by `C` on `[0, ∞)`, `outerAt m s R → outerAt m 0 R` as
`s → 0⁺`. -/
theorem tendsto_outerAt {m C : ℝ} {R : ℝ → ℝ} (hm : 0 < m) (hR : Measurable R)
    (hc : ContinuousOn R (Ioi 0)) (hb : ∀ t, 0 ≤ t → |R t| ≤ C) :
    Tendsto (fun s => outerAt m s R) (𝓝[>] 0) (𝓝 (outerAt m 0 R)) := by
  unfold outerAt
  refine Tendsto.const_mul _ ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * m ^ 2 * C) ?_ ?_
    (integrable_const _) ?_
  · refine Eventually.of_forall fun s => ?_
    have : Measurable fun z : ℝ × ℝ => 2 * (z.2 ^ 2 * m ^ 2 * R (vpK m s z)) := by
      unfold vpK kC
      fun_prop
    exact this.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    filter_upwards [QED.OneLoop.VertexLimit.ae_feynmanMeasure_mem_Icc] with z hz
    have hK := hb _ (vpK_nonneg (m := m) hs.le hz)
    have hy : z.2 ^ 2 ≤ 1 := by nlinarith [hz.2.1, hz.2.2]
    have hC : 0 ≤ C := (abs_nonneg _).trans hK
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg z.2),
      abs_of_nonneg (sq_nonneg m), abs_two]
    have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
    calc 2 * (z.2 ^ 2 * m ^ 2 * |R (vpK m s z)|) ≤ 2 * (1 * m ^ 2 * C) := by
          gcongr
    _ = 2 * m ^ 2 * C := by ring
  · filter_upwards [ae_mem_square] with z hz
    have hK0 : 0 < vpK m 0 z := vpK_pos hm.ne' le_rfl hz
    have hcont : ContinuousAt (fun s => vpK m s z) 0 := by
      unfold vpK kC
      fun_prop
    have hR0 : ContinuousAt R (vpK m 0 z) := hc.continuousAt (Ioi_mem_nhds hK0)
    have hT : Tendsto (fun s => R (vpK m s z)) (𝓝 0) (𝓝 (R (vpK m 0 z))) :=
      (ContinuousAt.comp (f := fun s => vpK m s z) hR0 hcont).tendsto
    exact ((hT.const_mul (z.2 ^ 2 * m ^ 2)).const_mul 2).mono_left nhdsWithin_le_nhds

/-! ### Linearity -/

/-- The integrand of `outerAt m s R` is integrable on the square. -/
def IntegrableAt (m s : ℝ) (R : ℝ → ℝ) : Prop :=
  Integrable (fun z : ℝ × ℝ => 2 * (z.2 ^ 2 * m ^ 2 * R (vpK m s z))) feynmanMeasure

/-- A measurable photon function bounded on `[0, ∞)` gives an integrable integrand (`s ≥ 0`). -/
theorem integrableAt_of_bound {m s C : ℝ} (hs : 0 ≤ s) {R : ℝ → ℝ}
    (hR : AEStronglyMeasurable (fun z : ℝ × ℝ => R (vpK m s z)) feynmanMeasure)
    (hb : ∀ t, 0 ≤ t → |R t| ≤ C) : IntegrableAt m s R := by
  refine Integrable.mono' (integrable_const (2 * m ^ 2 * C)) ?_ ?_
  · exact (aestronglyMeasurable_const.mul
      ((by fun_prop : Measurable fun z : ℝ × ℝ => z.2 ^ 2 * m ^ 2).aestronglyMeasurable.mul hR))
  · filter_upwards [QED.OneLoop.VertexLimit.ae_feynmanMeasure_mem_Icc] with z hz
    have hK := hb _ (vpK_nonneg (m := m) hs hz)
    have hy : z.2 ^ 2 ≤ 1 := by nlinarith [hz.2.1, hz.2.2]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg z.2),
      abs_of_nonneg (sq_nonneg m), abs_two]
    have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
    calc 2 * (z.2 ^ 2 * m ^ 2 * |R (vpK m s z)|) ≤ 2 * (1 * m ^ 2 * C) := by
          gcongr
    _ = 2 * m ^ 2 * C := by ring

theorem outerAt_add {m s : ℝ} {R R' : ℝ → ℝ} (h : IntegrableAt m s R)
    (h' : IntegrableAt m s R') :
    outerAt m s (fun t => R t + R' t) = outerAt m s R + outerAt m s R' := by
  unfold outerAt
  rw [← mul_add, ← integral_add h h']
  congr 2
  funext z
  ring

theorem outerAt_const_mul (m s c : ℝ) (R : ℝ → ℝ) :
    outerAt m s (fun t => c * R t) = c * outerAt m s R := by
  unfold outerAt
  have e : (fun z : ℝ × ℝ => 2 * (z.2 ^ 2 * m ^ 2 * (c * R (vpK m s z)))) =
      fun z => c * (2 * (z.2 ^ 2 * m ^ 2 * R (vpK m s z))) := by
    funext z
    ring
  rw [e, integral_const_mul]
  ring

theorem integrableAt_const_mul {m s : ℝ} (c : ℝ) {R : ℝ → ℝ} (h : IntegrableAt m s R) :
    IntegrableAt m s (fun t => c * R t) := by
  unfold IntegrableAt at h ⊢
  have e : (fun z : ℝ × ℝ => 2 * (z.2 ^ 2 * m ^ 2 * (c * R (vpK m s z)))) =
      fun z => c * (2 * (z.2 ^ 2 * m ^ 2 * R (vpK m s z))) := by
    funext z
    ring
  rw [e]
  exact h.const_mul c

theorem outerAt_sum {ι : Type*} (S : Finset ι) {m s : ℝ} {R : ι → ℝ → ℝ}
    (h : ∀ r ∈ S, IntegrableAt m s (R r)) :
    outerAt m s (fun t => ∑ r ∈ S, R r t) = ∑ r ∈ S, outerAt m s (R r) := by
  unfold outerAt
  rw [← Finset.mul_sum, ← integral_finsetSum S h]
  congr 2
  funext z
  rw [Finset.mul_sum, Finset.mul_sum]

end QED.ChainProof.HCValue

end
