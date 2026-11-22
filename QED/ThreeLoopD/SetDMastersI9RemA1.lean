/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemY
public import QED.ThreeLoopD.SetDMastersI9RemA1Kernel
public import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Set (d), master `I₉`: the value of `∫ F₁`

`QED.ThreeLoopD.integral_i9RemF1_eq` writes `∫ F₁` as an iterated `(x, w)`-integral of
`-3/(c w) · (w (π²/6 - Li₂ q) + P₀/2 · log² (P₁/P₀))`, with `c = x (1 - x)`, `u = 1 - w`,
`P₀ = c u²`, `P₁ = P₀ + w = (1 - x u)(1 - (1 - x) u)` and `q = w / P₁`.

The substitution `Ψ(x, w) = (p, s) = (P₀ / P₁, x u)` maps `(0, 1)²` onto itself (inverse
`x = s E / M`, `w = s (1 - p)(1 - s) / E`, `E = s + p (1 - s)`, `M = p + s² (1 - p)`), with
Jacobian `x u² (1 - x u) / P₁²`. In the new variables the integrand is `-3 k(s, p) g(p)`
(`QED.ThreeLoopD.SetDMastersI9RemA1Kernel`), so the `s`-integral gives `K(p)` and

  `∫ F₁ = -3 ∫₀¹ g K = -3 (π²/6 + 3 ζ(3)) = -π²/2 - 9 ζ(3)`.

## Main results

* `QED.ThreeLoopD.integral_i9RemF1_value`: `∫_cube F₁ = -π²/2 - 9 ζ(3)`.
-/

@[expose] public section

open MeasureTheory Set Real QED.Polylog

namespace QED.ThreeLoopD

/-! ### The substitution -/

/-- `P₁ = c (1 - w)² + w`. -/
def i9A1P (z : ℝ × ℝ) : ℝ := z.1 * (1 - z.1) * (1 - z.2) ^ 2 + z.2

/-- `Ψ(x, w) = (P₀ / P₁, x (1 - w))`. -/
noncomputable def i9A1Map (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 * (1 - z.1) * (1 - z.2) ^ 2 / (z.1 * (1 - z.1) * (1 - z.2) ^ 2 + z.2), z.1 * (1 - z.2))

/-- The inverse of `Ψ`: `(p, s) ↦ (s E / M, s (1 - p)(1 - s) / E)`. -/
noncomputable def i9A1Inv (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.2 * (q.2 + q.1 * (1 - q.2)) / (q.1 + q.2 ^ 2 * (1 - q.1)),
    q.2 * (1 - q.1) * (1 - q.2) / (q.2 + q.1 * (1 - q.2)))

/-- `∂p/∂x`. -/
noncomputable def i9A1Jx (z : ℝ × ℝ) : ℝ := (1 - 2 * z.1) * (1 - z.2) ^ 2 * z.2 / i9A1P z ^ 2

/-- `∂p/∂w`. -/
noncomputable def i9A1Jw (z : ℝ × ℝ) : ℝ :=
  -(z.1 * (1 - z.1) * (1 - z.2) * (1 + z.2)) / i9A1P z ^ 2

/-- The derivative of `Ψ`. -/
noncomputable def i9A1Deriv (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (i9A1Jx z • ContinuousLinearMap.fst ℝ ℝ ℝ + i9A1Jw z • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((1 - z.2) • ContinuousLinearMap.fst ℝ ℝ ℝ - z.1 • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem i9A1P_pos {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) : 0 < i9A1P z := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  unfold i9A1P
  have : 0 < z.1 * (1 - z.1) := mul_pos h1 (by linarith)
  positivity

theorem i9A1P_eq (z : ℝ × ℝ) :
    i9A1P z = (1 - z.1 * (1 - z.2)) * (1 - (1 - z.1) * (1 - z.2)) := by
  unfold i9A1P; ring

theorem hasFDerivAt_i9A1Map {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    HasFDerivAt i9A1Map (i9A1Deriv z) z := by
  have hP := i9A1P_pos hz
  have hx := hasFDerivAt_fst (𝕜 := ℝ) (p := z) (E := ℝ) (F := ℝ)
  have hw := hasFDerivAt_snd (𝕜 := ℝ) (p := z) (E := ℝ) (F := ℝ)
  have h1 := (hasFDerivAt_const (1 : ℝ) z).sub hx
  have h2 := (hasFDerivAt_const (1 : ℝ) z).sub hw
  have hN := (hx.mul h1).mul (h2.pow 2)
  have hD := hN.add hw
  have hDz : z.1 * (1 - z.1) * (1 - z.2) ^ 2 + z.2 ≠ 0 := hP.ne'
  have hI := (hasDerivAt_inv hDz).comp_hasFDerivAt z hD
  have h := (hN.mul hI).prodMk (hx.mul h2)
  convert h using 1
  · funext t
    simp only [i9A1Map, div_eq_mul_inv]
    rfl
  · refine ContinuousLinearMap.ext fun v => ?_
    refine Prod.ext ?_ ?_
    · simp [i9A1Deriv, i9A1Jx, i9A1Jw, i9A1P]
      field_simp
      ring
    · simp [i9A1Deriv]
      ring

theorem det_i9A1Deriv (z : ℝ × ℝ) :
    (i9A1Deriv z).det = -(i9A1Jx z * z.1) - i9A1Jw z * (1 - z.2) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, i9A1Deriv]

theorem abs_det_i9A1Deriv {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    |(i9A1Deriv z).det| = z.1 * (1 - z.2) ^ 2 * (1 - z.1 * (1 - z.2)) / i9A1P z ^ 2 := by
  have hP := i9A1P_pos hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  have e : (i9A1Deriv z).det = z.1 * (1 - z.2) ^ 2 * (1 - z.1 * (1 - z.2)) / i9A1P z ^ 2 := by
    rw [det_i9A1Deriv, i9A1Jx, i9A1Jw]
    field_simp
    ring
  rw [e, abs_of_nonneg]
  have : 0 < 1 - z.1 * (1 - z.2) := by nlinarith
  have : 0 < 1 - z.2 := by linarith
  positivity

theorem i9A1Map_mem {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i9A1Map z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  have hP := i9A1P_pos hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  have hc : 0 < z.1 * (1 - z.1) * (1 - z.2) ^ 2 := by
    have : 0 < 1 - z.2 := by linarith
    have : 0 < 1 - z.1 := by linarith
    positivity
  unfold i9A1P at hP
  refine ⟨⟨div_pos hc hP, (div_lt_one hP).2 (by linarith)⟩, ?_, ?_⟩
  · have : 0 < 1 - z.2 := by linarith
    show 0 < z.1 * (1 - z.2)
    positivity
  · show z.1 * (1 - z.2) < 1
    nlinarith

theorem i9A1Inv_mem {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i9A1Inv q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
  have hE : 0 < q.2 + q.1 * (1 - q.2) := by nlinarith
  have hM : 0 < q.1 + q.2 ^ 2 * (1 - q.1) := by nlinarith
  refine ⟨⟨by unfold i9A1Inv; positivity, ?_⟩, ?_, ?_⟩
  · simp only [i9A1Inv]
    rw [div_lt_one hM]
    nlinarith [mul_pos h1 (by linarith : (0 : ℝ) < 1 - q.2)]
  · simp only [i9A1Inv]
    have : 0 < 1 - q.1 := by linarith
    have : 0 < 1 - q.2 := by linarith
    positivity
  · simp only [i9A1Inv]
    rw [div_lt_one hE]
    nlinarith [mul_pos h1 (by linarith : (0 : ℝ) < 1 - q.2),
      mul_pos (mul_pos h3 (by linarith : (0 : ℝ) < 1 - q.1)) (by linarith : (0 : ℝ) < 1 - q.2)]

theorem i9A1Inv_map {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i9A1Inv (i9A1Map z) = z := by
  have hP := i9A1P_pos hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  obtain ⟨x, w⟩ := z
  simp only at h1 h2 h3 h4
  have hP' : x * (1 - x) * (1 - w) ^ 2 + w ≠ 0 := hP.ne'
  have ha : 0 < 1 - x * (1 - w) := by nlinarith
  have hu : 0 < 1 - w := by linarith
  have hE : x * (1 - w) + x * (1 - x) * (1 - w) ^ 2 / (x * (1 - x) * (1 - w) ^ 2 + w) *
      (1 - x * (1 - w)) =
      x * (1 - w) * (1 - x * (1 - w)) / (x * (1 - x) * (1 - w) ^ 2 + w) := by
    field_simp
    ring
  have hM : x * (1 - x) * (1 - w) ^ 2 / (x * (1 - x) * (1 - w) ^ 2 + w) +
      (x * (1 - w)) ^ 2 * (1 - x * (1 - x) * (1 - w) ^ 2 / (x * (1 - x) * (1 - w) ^ 2 + w)) =
      x * (1 - w) ^ 2 * (1 - x * (1 - w)) / (x * (1 - x) * (1 - w) ^ 2 + w) := by
    field_simp
    ring
  have h1p : 1 - x * (1 - x) * (1 - w) ^ 2 / (x * (1 - x) * (1 - w) ^ 2 + w) =
      w / (x * (1 - x) * (1 - w) ^ 2 + w) := by
    field_simp
    ring
  simp only [i9A1Inv, i9A1Map]
  rw [hE, hM, h1p]
  refine Prod.ext ?_ ?_
  · simp only
    rw [div_eq_iff (by positivity)]
    ring
  · simp only
    rw [div_eq_iff (by positivity)]
    ring

theorem i9A1Map_inv {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i9A1Map (i9A1Inv q) = q := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
  obtain ⟨p, s⟩ := q
  simp only at h1 h2 h3 h4
  have hE : s + p * (1 - s) ≠ 0 := by nlinarith
  have hM : p + s ^ 2 * (1 - p) ≠ 0 := by nlinarith
  have hs : s ≠ 0 := h3.ne'
  have hs1 : 1 - s ≠ 0 := by linarith
  have e1 : 1 - s * (s + p * (1 - s)) / (p + s ^ 2 * (1 - p)) =
      p * (1 - s) / (p + s ^ 2 * (1 - p)) := by field_simp; ring
  have e2 : 1 - s * (1 - p) * (1 - s) / (s + p * (1 - s)) =
      (p + s ^ 2 * (1 - p)) / (s + p * (1 - s)) := by field_simp; ring
  have eN : s * (s + p * (1 - s)) / (p + s ^ 2 * (1 - p)) *
      (p * (1 - s) / (p + s ^ 2 * (1 - p))) *
      ((p + s ^ 2 * (1 - p)) / (s + p * (1 - s))) ^ 2 = s * p * (1 - s) / (s + p * (1 - s)) := by
    field_simp
  have eD : s * p * (1 - s) / (s + p * (1 - s)) + s * (1 - p) * (1 - s) / (s + p * (1 - s)) =
      s * (1 - s) / (s + p * (1 - s)) := by field_simp; ring
  simp only [i9A1Map, i9A1Inv]
  rw [e1, e2, eN, eD]
  refine Prod.ext ?_ ?_
  · simp only
    field_simp
  · simp only
    field_simp

theorem injOn_i9A1Map : InjOn i9A1Map (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  intro z hz z' hz' h
  rw [← i9A1Inv_map hz, ← i9A1Inv_map hz', h]

theorem image_i9A1Map :
    i9A1Map '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) = Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact i9A1Map_mem hz
  · intro hq
    exact ⟨i9A1Inv q, i9A1Inv_mem hq, i9A1Map_inv hq⟩

/-! ### The integrand in the new variables -/

/-- The `(x, w)`-integrand of `QED.ThreeLoopD.integral_i9RemF1_eq`. -/
noncomputable def i9A1Dens (z : ℝ × ℝ) : ℝ :=
  -3 / (z.1 * (1 - z.1) * z.2) * (z.2 * (π ^ 2 / 6 - Li₂ (z.2 / i9Poly z.1 z.2 1)) +
    i9Poly z.1 z.2 0 / 2 * Real.log (i9Poly z.1 z.2 1 / i9Poly z.1 z.2 0) ^ 2)

/-- The integrand in the variables `(p, s)`: `k(s, p) g(p)`. -/
noncomputable def i9A1G (q : ℝ × ℝ) : ℝ := i9A1k q.2 q.1 * i9A1g q.1

/-- **The integrand after the substitution**: `i9A1Dens = -3 |det Ψ'| (k g) ∘ Ψ`. -/
theorem i9A1Dens_eq {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i9A1Dens z = -3 * (|(i9A1Deriv z).det| • i9A1G (i9A1Map z)) := by
  rw [abs_det_i9A1Deriv hz]
  have hP := i9A1P_pos hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  obtain ⟨x, w⟩ := z
  simp only at h1 h2 h3 h4
  unfold i9A1P at hP
  have hP' : x * (1 - x) * (1 - w) ^ 2 + w ≠ 0 := hP.ne'
  have ha : 0 < 1 - x * (1 - w) := by nlinarith
  have hu : 0 < 1 - w := by linarith
  have hx1 : 0 < 1 - x := by linarith
  have hN : 0 < x * (1 - x) * (1 - w) ^ 2 := by positivity
  have hE : x * (1 - w) + x * (1 - x) * (1 - w) ^ 2 / (x * (1 - x) * (1 - w) ^ 2 + w) *
      (1 - x * (1 - w)) =
      x * (1 - w) * (1 - x * (1 - w)) / (x * (1 - x) * (1 - w) ^ 2 + w) := by
    field_simp
    ring
  have h1p : 1 - x * (1 - x) * (1 - w) ^ 2 / (x * (1 - x) * (1 - w) ^ 2 + w) =
      w / (x * (1 - x) * (1 - w) ^ 2 + w) := by
    field_simp
    ring
  simp only [i9A1Dens, i9A1G, i9A1Map, i9A1k, i9A1g, i9Poly, i9A1P, mul_one, mul_zero, add_zero,
    smul_eq_mul]
  rw [hE, h1p, Real.log_div hN.ne' hP', Real.log_div hP' hN.ne']
  generalize Li₂ (w / (x * (1 - x) * (1 - w) ^ 2 + w)) = L
  generalize Real.log (x * (1 - x) * (1 - w) ^ 2) = lN
  generalize Real.log (x * (1 - x) * (1 - w) ^ 2 + w) = lP
  field_simp
  ring

theorem continuousOn_i9A1g : ContinuousOn i9A1g (Ioo 0 1) := by
  have hL : ContinuousOn (fun p => Li₂ (1 - p)) (Ioo 0 1) :=
    continuousOn_Li₂.comp (continuousOn_const.sub continuousOn_id)
      (fun p hp => ⟨by linarith [hp.2], by linarith [hp.1]⟩)
  have hl : ContinuousOn Real.log (Ioo 0 1) :=
    Real.continuousOn_log.mono fun p hp => ne_of_gt hp.1
  unfold i9A1g
  exact ((continuousOn_const.sub hL).div continuousOn_id fun p hp => hp.1.ne').add
    ((hl.pow 2).div (by fun_prop) fun p hp => by linarith [hp.2])

theorem continuousOn_i9A1G : ContinuousOn i9A1G (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hk : ContinuousOn (fun q : ℝ × ℝ => i9A1k q.2 q.1) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    unfold i9A1k
    refine continuousOn_const.add (ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq => ?_)
    exact (pow_pos (i9A1_E_pos hq.1 ⟨hq.2.1.le, hq.2.2.le⟩) 2).ne'
  exact hk.mul (continuousOn_i9A1g.comp continuousOn_fst fun q hq => hq.1)

theorem integrableOn_i9A1G : IntegrableOn i9A1G (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hm : AEStronglyMeasurable i9A1G (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    continuousOn_i9A1G.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioo)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hm
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, integrable_prod_iff hm]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    have : IntegrableOn (fun s => i9A1k s p) (Icc 0 1) := (continuousOn_i9A1k hp).integrableOn_Icc
    exact (this.mono_set Ioo_subset_Icc_self).mul_const (i9A1g p)
  · have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
      intervalIntegrable_and_integral_i9A1gK.1
    refine hi.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    have e : ∀ s ∈ Ioo (0 : ℝ) 1, ‖i9A1G (p, s)‖ = i9A1k s p * i9A1g p := fun s _ =>
      Real.norm_of_nonneg (mul_nonneg (i9A1k_nonneg hp) (i9A1g_nonneg hp))
    rw [setIntegral_congr_fun measurableSet_Ioo e, integral_mul_const,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_i9A1k hp]
    ring

theorem integral_i9A1G :
    ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9A1G q = π ^ 2 / 6 + 3 * zeta3 := by
  have hI := integrableOn_i9A1G
  rw [IntegrableOn, Measure.volume_eq_prod] at hI
  rw [Measure.volume_eq_prod, setIntegral_prod _ hI]
  have e : ∀ p ∈ Ioo (0 : ℝ) 1, ∫ s in Ioo (0 : ℝ) 1, i9A1G (p, s) = i9A1g p * i9A1K p := by
    intro p hp
    simp only [i9A1G]
    rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one, integral_i9A1k hp]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo e, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, intervalIntegrable_and_integral_i9A1gK.2]

/-! ### The value -/

/-- **`∫_cube F₁ = -π²/2 - 9 ζ(3)`**, the order-`ε` coefficient of `Rem`. -/
theorem integral_i9RemF1_value :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemF1 z =
      -π ^ 2 / 2 - 9 * zeta3 := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hd : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      HasFDerivWithinAt i9A1Map (i9A1Deriv z) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) z :=
    fun z hz => (hasFDerivAt_i9A1Map hz).hasFDerivWithinAt
  have hI : IntegrableOn (fun z => |(i9A1Deriv z).det| • i9A1G (i9A1Map z))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS hd injOn_i9A1Map
      i9A1G).1 (by rw [image_i9A1Map]; exact integrableOn_i9A1G)
  have hDens : IntegrableOn i9A1Dens (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    IntegrableOn.congr_fun (hI.const_mul (-3)) (fun z hz => (i9A1Dens_eq hz).symm) hS
  rw [IntegrableOn, Measure.volume_eq_prod] at hDens
  calc _ = ∫ x in Ioo (0 : ℝ) 1, ∫ w in Ioo (0 : ℝ) 1, i9A1Dens (x, w) := integral_i9RemF1_eq
    _ = ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9A1Dens z := by
      rw [Measure.volume_eq_prod, setIntegral_prod _ hDens]
    _ = -3 * ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, |(i9A1Deriv z).det| • i9A1G (i9A1Map z) := by
      rw [setIntegral_congr_fun hS fun z hz => i9A1Dens_eq hz, integral_const_mul]
    _ = -3 * ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9A1G q := by
      rw [← integral_image_eq_integral_abs_det_fderiv_smul volume hS hd injOn_i9A1Map,
        image_i9A1Map]
    _ = -π ^ 2 / 2 - 9 * zeta3 := by
      rw [integral_i9A1G]
      ring

end QED.ThreeLoopD
