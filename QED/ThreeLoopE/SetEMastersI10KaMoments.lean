/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10KaBubbleVal
public import QED.Polylog.ExtraIntegrals
import QED.ThreeLoopE.SetEMastersI10KabVal
import QED.ThreeLoopD.SetDMastersI9Analytic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.LHopital
import QED.Polylog.ExtraIntegralsC
import QED.Polylog.Reflection
import QED.Polylog.Deriv
public import QED.Polylog.HPLLowWeight
import QED.Polylog.HPLShuffle
import QED.Polylog.HPLRegular
import QED.Polylog.HPLValues4
import QED.Polylog.HPLValues
public import QED.ThreeLoopE.SetEMastersI10Asm

/-!
# The two affine logarithmic moments in the cubic coefficient of `Kₐ`

Integrating by parts against the primitive of the affine logarithm, and
then against that of its square, reduces the moments to polylogarithms.
The values are checked in `scripts/numerics/three_loop_masters/i10momentchecks.py`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ThreeLoopE

private noncomputable def kaMomentL₁ (y : ℝ) : ℝ := -(1 - y) * log (1 - y) - y

private noncomputable def kaMomentL₂ (y : ℝ) : ℝ :=
  2 * y - (1 - y) * (log (1 - y) ^ 2 - 2 * log (1 - y))

private noncomputable def kaMomentC₁ (y : ℝ) : ℝ := Li₂ y + kaMomentL₁ y - y

private noncomputable def kaMomentC₂ (y : ℝ) : ℝ :=
  -logOneSubSqPrim y - 2 * zeta3 + kaMomentL₂ y + 4 * y - 2 * Li₂ y +
    2 * (1 - y) * log (1 - y)

private theorem kaMomentLogDeriv {y : ℝ} (hy : y < 1) :
    HasDerivAt (fun x : ℝ => log (1 - x)) (-1 / (1 - y)) y := by
  have h := ((hasDerivAt_id y).const_sub 1).log (sub_pos.mpr hy).ne'
  simpa only [id_eq, div_eq_mul_inv] using h

private theorem kaMomentL₁_deriv {y : ℝ} (hy : y < 1) :
    HasDerivAt kaMomentL₁ (log (1 - y)) y := by
  have h := ((((hasDerivAt_id y).const_sub 1).neg).mul (kaMomentLogDeriv hy)).sub
    (hasDerivAt_id y)
  refine h.congr_deriv ?_
  dsimp [id]
  field_simp [(sub_pos.mpr hy).ne']
  ring

private theorem kaMomentL₂_deriv {y : ℝ} (hy : y < 1) :
    HasDerivAt kaMomentL₂ (log (1 - y) ^ 2) y := by
  have h := ((hasDerivAt_id y).const_mul 2).sub
    (((hasDerivAt_id y).const_sub 1).mul
      (((kaMomentLogDeriv hy).pow 2).sub ((kaMomentLogDeriv hy).const_mul 2)))
  refine h.congr_deriv ?_
  dsimp [id]
  field_simp [(sub_pos.mpr hy).ne']
  ring

private theorem kaMomentC₁_deriv {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt kaMomentC₁ (kaMomentL₁ y / y) y := by
  refine (((hasDerivAt_Li₂' hy).add (kaMomentL₁_deriv hy.2)).sub
    (hasDerivAt_id y)).congr_deriv ?_
  unfold kaMomentL₁
  field_simp [hy.1.ne']
  ring

private theorem kaMomentC₂_deriv {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt kaMomentC₂ (kaMomentL₂ y / y) y := by
  have h := ((((((hasDerivAt_logOneSubSqPrim hy).neg).sub_const (2 * zeta3)).add
    (kaMomentL₂_deriv hy.2)).add ((hasDerivAt_id y).const_mul 4)).sub
    ((hasDerivAt_Li₂' hy).const_mul 2)).add
    ((((hasDerivAt_id y).const_sub 1).const_mul 2).mul (kaMomentLogDeriv hy.2))
  refine h.congr_deriv ?_
  dsimp only [id_eq, kaMomentL₂]
  field_simp [hy.1.ne', (sub_pos.mpr hy.2).ne']
  ring

private theorem kaMoment_mul_zero {L : ℝ → ℝ} {d : ℝ}
    (hL : HasDerivAt L d 0) (hL₀ : L 0 = 0) :
    Tendsto (fun x => -log x * L x) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_mul_log_zero.neg.mul hL.tendsto_slope_zero_right
  rw [neg_zero, zero_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  simp only [hL₀, sub_zero, smul_eq_mul, zero_add]
  field_simp [hx.ne']

private theorem kaMoment_mul_left {z : ℝ} (hz : 0 < z) :
    Tendsto (fun x : ℝ => z * x) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa only [id_eq, mul_zero] using
      (((continuous_id.const_mul z).tendsto 0).mono_left nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact mul_pos hz hx

private theorem kaMoment_aux {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) {f L C : ℝ → ℝ}
    {B Lend : ℝ} (hL : ∀ y < 1, HasDerivAt L (f y) y)
    (hL₀ : L 0 = 0) (hC : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt C (L y / y) y)
    (hC₀ : Tendsto C (𝓝[>] 0) (𝓝 0))
    (hL₁ : Tendsto (fun x => L (z * x)) (𝓝[<] 1) (𝓝 Lend))
    (hC₁ : Tendsto (fun x => C (z * x)) (𝓝[<] 1) (𝓝 B))
    (hsign : (∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ -log x * f (z * x)) ∨
      (∀ x ∈ Ioo (0 : ℝ) 1, -log x * f (z * x) ≤ 0)) :
    IntervalIntegrable (fun x => -log x * f (z * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, -log x * f (z * x) = B / z := by
  let P := fun x => (-log x * L (z * x) + C (z * x)) / z
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt P (-log x * f (z * x)) x := by
    intro x hx
    have hy : z * x ∈ Ioo 0 1 :=
      ⟨mul_pos hz.1 hx.1, (mul_lt_mul_of_pos_left hx.2 hz.1).trans_le
        (by simpa only [mul_one] using hz.2)⟩
    have hzx : HasDerivAt (fun y : ℝ => z * y) z x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul z
    have h := ((((hasDerivAt_log hx.1.ne').neg).mul ((hL _ hy.2).comp x hzx)).add
      ((hC _ hy).comp x hzx)).div_const z
    refine h.congr_deriv ?_
    change ((-x⁻¹ * L (z * x) + -log x * (f (z * x) * z) +
      L (z * x) / (z * x) * z) / z) = _
    field_simp [hz.1.ne', hx.1.ne']
    ring
  have h0 : Tendsto P (𝓝[>] 0) (𝓝 0) := by
    have hLz : HasDerivAt L (f 0) (z * 0) := by rw [mul_zero]; exact hL 0 zero_lt_one
    have hzx : HasDerivAt (fun x : ℝ => z * x) z 0 := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul z
    have h : HasDerivAt (fun x => L (z * x)) (f 0 * z) 0 := hLz.comp 0 hzx
    have hl := kaMoment_mul_zero h (by simpa only [mul_zero] using hL₀)
    simpa only [P, Function.comp_def, zero_add, zero_div] using
      (hl.add (hC₀.comp (kaMoment_mul_left hz.1))).div_const z
  have h1 : Tendsto P (𝓝[<] 1) (𝓝 (B / z)) := by
    have hl := ((continuousAt_log one_ne_zero).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))).neg
    simpa only [P, log_one, neg_zero, zero_mul, zero_add] using
      ((hl.mul hL₁).add hC₁).div_const z
  rcases hsign with hp | hn
  · simpa only [sub_zero] using intervalIntegrable_and_integral_eq_of_nonneg hd hp h0 h1
  · simpa only [sub_zero] using intervalIntegrable_and_integral_eq_of_nonpos hd hn h0 h1

private theorem kaMoment_at_interior {z : ℝ} {F : ℝ → ℝ} (h : ContinuousAt F z) :
    Tendsto (fun x => F (z * x)) (𝓝[<] 1) (𝓝 (F z)) := by
  have hz : Tendsto (fun x : ℝ => z * x) (𝓝[<] 1) (𝓝 z) := by
    simpa only [id_eq, mul_one] using
      (((continuous_id.const_mul z).tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Iio (1 : ℝ))) :
        Tendsto (fun x : ℝ => z * x) (𝓝[<] 1) (𝓝 (z * 1)))
  exact h.tendsto.comp hz

private theorem kaMomentC₁_zero : Tendsto kaMomentC₁ (𝓝[>] 0) (𝓝 0) := by
  have hl := ((kaMomentL₁_deriv zero_lt_one).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hx := (continuous_id.tendsto (0 : ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  unfold kaMomentC₁ kaMomentL₁
  simpa only [kaMomentL₁, id_eq, sub_zero, log_one, mul_zero, zero_add] using
    (tendsto_Li₂_zero_right.add hl).sub hx

private theorem kaMomentC₂_zero : Tendsto kaMomentC₂ (𝓝[>] 0) (𝓝 0) := by
  have hl := ((kaMomentL₂_deriv zero_lt_one).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hx := (continuous_id.tendsto (0 : ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h := (((tendsto_logOneSubSqPrim_zero.neg.sub_const (2 * zeta3)).add hl).add
    (hx.const_mul 4)).sub (tendsto_Li₂_zero_right.const_mul 2)
  have hm := (((hx.const_sub 1).const_mul 2).mul tendsto_log_one_sub_zero)
  unfold kaMomentC₂ kaMomentL₂
  simpa only [kaMomentL₂, id_eq, sub_zero, log_one, mul_zero, zero_pow
    two_ne_zero, zero_sub, neg_mul, neg_neg, sub_self, zero_add] using h.add hm

private theorem kaMomentL₁_one : Tendsto kaMomentL₁ (𝓝[<] 1) (𝓝 (-1)) := by
  have hx := (continuous_id.tendsto (1 : ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  have h := (tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one).neg.sub hx
  unfold kaMomentL₁
  simpa only [Function.comp_def, id_eq, neg_mul, neg_zero, zero_sub] using h

private theorem kaMomentL₂_one : Tendsto kaMomentL₂ (𝓝[<] 1) (𝓝 2) := by
  have hx := (continuous_id.tendsto (1 : ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  have h := (hx.const_mul 2).sub ((tendsto_mul_log_sq_zero.comp
    tendsto_one_sub_nhdsLT_one).sub ((tendsto_mul_log_zero.comp
      tendsto_one_sub_nhdsLT_one).const_mul 2))
  have h' : Tendsto kaMomentL₂ (𝓝[<] 1) (𝓝 (2 * id 1 - (0 - 2 * 0))) :=
    h.congr (fun x => by simp only [kaMomentL₂, Function.comp_def, id_eq]; ring)
  norm_num [id] at h'
  exact h'

private theorem kaMomentC₁_one : Tendsto kaMomentC₁ (𝓝[<] 1) (𝓝 (π ^ 2 / 6 - 2)) := by
  have hx := (continuous_id.tendsto (1 : ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  have h := (tendsto_Li₂_one_left.add kaMomentL₁_one).sub hx
  change Tendsto kaMomentC₁ _ (𝓝 (π ^ 2 / 6 + -1 - 1)) at h
  convert h using 2
  ring

private theorem kaMomentC₂_one :
    Tendsto kaMomentC₂ (𝓝[<] 1) (𝓝 (6 - 2 * zeta3 - 2 * (π ^ 2 / 6))) := by
  have hx := (continuous_id.tendsto (1 : ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  have h := (((tendsto_logOneSubSqPrim_one.neg.sub_const (2 * zeta3)).add kaMomentL₂_one).add
    (hx.const_mul 4)).sub (tendsto_Li₂_one_left.const_mul 2)
  have hm := (tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one).const_mul 2
  have h' : Tendsto kaMomentC₂ (𝓝[<] 1)
      (𝓝 (-0 - 2 * zeta3 + 2 + 4 * id 1 - 2 * (π ^ 2 / 6) + 2 * 0)) :=
    (h.add hm).congr (fun x => by
      simp only [kaMomentC₂, Function.comp_def, id_eq]
      ring)
  convert h' using 2
  simp only [id_eq]
  ring

private theorem kaMoment_param_mem {z x : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : z * x ∈ Ioo (0 : ℝ) 1 :=
  ⟨mul_pos hz.1 hx.1, (mul_lt_mul_of_pos_left hx.2 hz.1).trans_le
    (by simpa only [mul_one] using hz.2)⟩

/-- First affine log moment, including the endpoint parameter. -/
theorem intervalIntegrable_and_integral_i10Ka_affine_log {z : ℝ}
    (hz : z ∈ Ioc (0 : ℝ) 1) :
    IntervalIntegrable (fun x => -log x * log (1 - z * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, -log x * log (1 - z * x) =
        (Li₂ z - (1 - z) * log (1 - z)) / z - 2 := by
  have hs : ∀ x ∈ Ioo (0 : ℝ) 1, -log x * log (1 - z * x) ≤ 0 := by
    intro x hx
    have hy := kaMoment_param_mem hz hx
    exact mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr (log_nonpos hx.1.le hx.2.le))
      (log_nonpos (sub_pos.mpr hy.2).le (sub_le_self _ hy.1.le))
  have hL₀ : kaMomentL₁ 0 = 0 := by simp [kaMomentL₁]
  rcases hz.2.lt_or_eq with hz' | rfl
  · have h := kaMoment_aux hz (fun _ => kaMomentL₁_deriv) hL₀
      (fun _ => kaMomentC₁_deriv) kaMomentC₁_zero
      (kaMoment_at_interior (kaMomentL₁_deriv hz').continuousAt)
      (kaMoment_at_interior (kaMomentC₁_deriv ⟨hz.1, hz'⟩).continuousAt) (Or.inr hs)
    refine ⟨h.1, h.2.trans ?_⟩
    unfold kaMomentC₁ kaMomentL₁
    field_simp [hz.1.ne']
    ring
  · have h := kaMoment_aux hz (fun _ => kaMomentL₁_deriv) hL₀
      (fun _ => kaMomentC₁_deriv) kaMomentC₁_zero
      (by simpa only [one_mul] using kaMomentL₁_one)
      (by simpa only [one_mul] using kaMomentC₁_one) (Or.inr hs)
    simpa only [Li₂_one, sub_self, zero_mul, sub_zero, div_one] using h

/-- Second affine log moment on the open unit interval. -/
theorem intervalIntegrable_and_integral_i10Ka_affine_log_sq {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => -log x * log (1 - z * x) ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, -log x * log (1 - z * x) ^ 2 =
        6 + (-(1 - z) * log (1 - z) ^ 2 + 4 * (1 - z) * log (1 - z) -
          (logOneSubSqPrim z + 2 * zeta3) - 2 * Li₂ z) / z := by
  have hs : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ -log x * log (1 - z * x) ^ 2 := fun x hx =>
    mul_nonneg (neg_nonneg.mpr (log_nonpos hx.1.le hx.2.le)) (sq_nonneg _)
  have h := kaMoment_aux ⟨hz.1, hz.2.le⟩ (fun _ => kaMomentL₂_deriv)
    (by simp [kaMomentL₂]) (fun _ => kaMomentC₂_deriv) kaMomentC₂_zero
    (kaMoment_at_interior (kaMomentL₂_deriv hz.2).continuousAt)
    (kaMoment_at_interior (kaMomentC₂_deriv hz).continuousAt) (Or.inl hs)
  refine ⟨h.1, h.2.trans ?_⟩
  unfold kaMomentC₂ kaMomentL₂
  field_simp [hz.1.ne']
  ring

/-- Second affine log moment at the endpoint parameter. -/
theorem intervalIntegrable_and_integral_i10Ka_affine_log_sq_one :
    IntervalIntegrable (fun x => -log x * log (1 - x) ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, -log x * log (1 - x) ^ 2 =
        6 - 2 * zeta3 - 2 * (π ^ 2 / 6) := by
  have hs : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ -log x * log (1 - 1 * x) ^ 2 := fun x hx =>
    mul_nonneg (neg_nonneg.mpr (log_nonpos hx.1.le hx.2.le)) (sq_nonneg _)
  have h := kaMoment_aux (z := 1) ⟨zero_lt_one, le_rfl⟩ (fun _ => kaMomentL₂_deriv)
    (by simp [kaMomentL₂]) (fun _ => kaMomentC₂_deriv) kaMomentC₂_zero
    (by simpa only [one_mul] using kaMomentL₂_one)
    (by simpa only [one_mul] using kaMomentC₂_one) (Or.inl hs)
  simpa only [one_mul, div_one] using h

/-- The cubic integrand after separating the derivative of the bubble factor. -/
noncomputable def i10KaCubicResidual (z r : ℝ) : ℝ :=
  let A := log (1 - z * (1 - r))
  let B := log (z * r)
  let L := log (z * (1 - z))
  (-log (1 - r)) * ((A ^ 2 / 2 + L * A) / z +
    (1 / (1 - z) + 1 / (1 - z) ^ 2) * ((A ^ 2 - B ^ 2) / 2 + L * (A - B)) -
    (log r + L) / ((1 - z) * r))

/-- The first affine logarithmic moment. -/
noncomputable def i10KaCubicF (z : ℝ) : ℝ :=
  (Li₂ z - (1 - z) * log (1 - z)) / z - 2

/-- The second affine logarithmic moment. -/
noncomputable def i10KaCubicG (z : ℝ) : ℝ :=
  6 + (-(1 - z) * log (1 - z) ^ 2 + 4 * (1 - z) * log (1 - z) -
    (logOneSubSqPrim z + 2 * zeta3) - 2 * Li₂ z) / z

/-- The grouped one-dimensional cubic integrand for the residual term. -/
noncomputable def i10KaCubicReduced (z : ℝ) : ℝ :=
  let a := log z
  let c := 1 - z
  let L := log (z * c)
  let F := i10KaCubicF z
  let G := i10KaCubicG z
  let F₁ := π ^ 2 / 6 - 2
  let G₁ := 6 - 2 * zeta3 - 2 * (π ^ 2 / 6)
  (G / 2 + L * F) / z +
    (1 / c + 1 / c ^ 2) * ((G - a ^ 2 - 2 * a * F₁ - G₁) / 2 + L * (F - a - F₁)) +
    (zeta3 - (π ^ 2 / 6) * L) / c

private theorem kaMoment_reflect {f : ℝ → ℝ} {v : ℝ}
    (h : IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = v) :
    IntervalIntegrable (fun x => f (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, f (1 - x) = v := by
  refine ⟨?_, ?_⟩
  · simpa only [sub_self, sub_zero] using h.1.symm.comp_sub_left 1
  · rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero, h.2]

private theorem kaMoment_negLog_one_sub :
    IntervalIntegrable (fun r : ℝ => -log (1 - r)) volume 0 1 ∧
      ∫ r in (0 : ℝ)..1, -log (1 - r) = 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, integral_neg,
    i10_integral_log_one_sub, neg_neg]
  exact ⟨i10_integrableOn_log_one_sub.neg, rfl⟩

private theorem kaMoment_integral_lin {f g : ℝ → ℝ} {s : Set ℝ} {a b : ℝ}
    (hf : IntegrableOn f s) (hg : IntegrableOn g s) :
    IntegrableOn (fun x => a * f x + b * g x) s ∧
      ∫ x in s, a * f x + b * g x =
        a * (∫ x in s, f x) + b * ∫ x in s, g x := by
  refine ⟨(hf.const_mul _).add (hg.const_mul _), ?_⟩
  rw [show (∫ x in s, a * f x + b * g x) =
    (∫ x in s, a * f x) + ∫ x in s, b * g x from
      integral_add (hf.const_mul _) (hg.const_mul _), integral_const_mul, integral_const_mul]

/-- At a fixed joining parameter, integrating over the bubble gives the reduced integrand. -/
theorem integral_i10KaCubicResidual {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (i10KaCubicResidual z) (Ioo 0 1) ∧
      ∫ r in Ioo (0 : ℝ) 1, i10KaCubicResidual z r = i10KaCubicReduced z := by
  let S := Ioo (0 : ℝ) 1
  let a := log z
  let c := 1 - z
  let L := log (z * c)
  let D := fun r : ℝ => -log (1 - r)
  let A := fun r : ℝ => log (1 - z * (1 - r))
  let b := fun r : ℝ => log r
  have hF₀ := i10_ioo_of_interval kaMoment_negLog_one_sub
  have hF₁ := i10_ioo_of_interval (kaMoment_reflect (by
    simpa only [Li₂_one, sub_self, zero_mul, sub_zero, div_one, one_mul] using
      intervalIntegrable_and_integral_i10Ka_affine_log (z := 1) ⟨zero_lt_one, le_rfl⟩))
  have hF₂ := i10_ioo_of_interval
    (kaMoment_reflect intervalIntegrable_and_integral_i10Ka_affine_log_sq_one)
  have hA₁ := i10_ioo_of_interval
    (kaMoment_reflect (intervalIntegrable_and_integral_i10Ka_affine_log ⟨hz.1, hz.2.le⟩))
  have hA₂ := i10_ioo_of_interval
    (kaMoment_reflect (intervalIntegrable_and_integral_i10Ka_affine_log_sq hz))
  have hE₀ := i10_ioo_of_interval intervalIntegrable_and_integral_log_one_sub_div
  have hE₁ := i10_ioo_of_interval intervalIntegrable_and_integral_log_mul_log_one_sub_div
  change IntegrableOn D S ∧ _ at hF₀
  have eF₁ (r : ℝ) : -log (1 - r) * log (1 - (1 - r)) = D r * b r := by
    rw [sub_sub_cancel]
  have eF₂ (r : ℝ) : -log (1 - r) * log (1 - (1 - r)) ^ 2 = D r * b r ^ 2 := by
    rw [sub_sub_cancel]
  simp only [eF₁] at hF₁
  simp only [eF₂] at hF₂
  change IntegrableOn (fun r => D r * A r) S ∧ _ at hA₁
  change IntegrableOn (fun r => D r * A r ^ 2) S ∧ _ at hA₂
  let U := fun r => (1 / 2) * (D r * A r ^ 2) + L * (D r * A r)
  let V := fun r => (1 / 2) * (D r * b r ^ 2) + (a + L) * (D r * b r)
  let P := fun r => V r + (a ^ 2 / 2 + L * a) * D r
  let E := fun r : ℝ => (1 / c) * (b r * log (1 - r) / r) +
    (L / c) * (log (1 - r) / r)
  have hU := kaMoment_integral_lin (a := 1 / 2) (b := L) hA₂.1 hA₁.1
  have hV := kaMoment_integral_lin (a := 1 / 2) (b := a + L) hF₂.1 hF₁.1
  have hP := kaMoment_integral_lin (a := 1) (b := a ^ 2 / 2 + L * a) hV.1 hF₀.1
  have hE := kaMoment_integral_lin (a := 1 / c) (b := L / c) hE₁.1 hE₀.1
  have hQ := kaMoment_integral_lin
    (a := 1 / z + (1 / c + 1 / c ^ 2)) (b := -(1 / c + 1 / c ^ 2)) hU.1 hP.1
  let Q := fun r => (1 / z + (1 / c + 1 / c ^ 2)) * U r + (-(1 / c + 1 / c ^ 2)) * (1 * V r +
    (a ^ 2 / 2 + L * a) * D r)
  have he : EqOn (i10KaCubicResidual z) (fun r => Q r + E r) S := by
    intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) 1 := hr
    dsimp [i10KaCubicResidual, Q, U, P, V, E, D, A, b, L, a, c]
    rw [log_mul hz.1.ne' hr'.1.ne']
    simp only [sub_eq_add_neg, neg_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  have hae : (i10KaCubicResidual z) =ᵐ[volume.restrict S] (fun r => Q r + E r) :=
    ae_restrict_of_forall_mem measurableSet_Ioo he
  have hQi : IntegrableOn Q S := hQ.1
  have hQeq : (∫ r in S, Q r) =
      (1 / z + (1 / c + 1 / c ^ 2)) * (∫ r in S, U r) -
        (1 / c + 1 / c ^ 2) * ∫ r in S, P r := by
    simpa only [Q, sub_eq_add_neg, neg_mul, one_mul] using hQ.2
  have hPeq : (∫ r in S, P r) =
      (∫ r in S, V r) + (a ^ 2 / 2 + L * a) * ∫ r in S, D r := by
    simpa only [P, one_mul] using hP.2
  have hEq : (∫ r in S, E r) = (1 / c) * zeta3 + (L / c) * -(π ^ 2 / 6) := by
    exact hE.2.trans (by rw [hE₁.2, hE₀.2])
  have hUeq : (∫ r in S, U r) = (1 / 2) * i10KaCubicG z + L * i10KaCubicF z := by
    exact hU.2.trans (by rw [hA₂.2, hA₁.2]; rfl)
  refine ⟨?_, ?_⟩
  · exact (hQi.add hE.1).congr hae.symm
  · rw [integral_congr_ae hae]
    rw [show (∫ r in S, Q r + E r) = (∫ r in S, Q r) + ∫ r in S, E r from
      integral_add hQi hE.1]
    rw [hQeq, hPeq, hEq, hUeq, show (∫ r in S, V r) = _ from hV.2,
      hF₀.2, hF₁.2, hF₂.2]
    have hc : c ≠ 0 := (sub_pos.mpr hz.2).ne'
    unfold i10KaCubicReduced
    change _ = (i10KaCubicG z / 2 + L * i10KaCubicF z) / z +
      (1 / c + 1 / c ^ 2) * ((i10KaCubicG z - a ^ 2 -
        2 * a * (π ^ 2 / 6 - 2) - (6 - 2 * zeta3 - 2 * (π ^ 2 / 6))) / 2 +
        L * (i10KaCubicF z - a - (π ^ 2 / 6 - 2))) + (zeta3 - π ^ 2 / 6 * L) / c
    field_simp [hc, hz.1.ne']
    ring

private noncomputable def kaBubbleTerm (q : ℝ × ℝ) : ℂ :=
  ((-log (1 - q.2) / 2 : ℝ) : ℂ) * i10KaH 0 q

private theorem kaCubic_pointwise {q : ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    deriv (fun ε => i10KaH ε q) 0 = (i10KaCubicResidual q.1 q.2 : ℂ) + kaBubbleTerm q := by
  obtain ⟨hz, hr⟩ := hq
  have hz' := hz.1.ne'
  have hc := (sub_pos.mpr hz.2).ne'
  have hr' := hr.1.ne'
  rw [(hasDerivAt_i10KaH_zero ⟨hz, hr⟩).deriv]
  dsimp only [i10KaCubicResidual, kaBubbleTerm, i10KaH]
  rw [i10D_zero hr.2, i10W, zero_sub, Complex.cpow_neg_one]
  rw [i10KaB_zero hz hr]
  push_cast
  have hzC : (q.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz'
  have hcC : (1 - (q.1 : ℂ)) ≠ 0 := by exact_mod_cast hc
  have hrC : (q.2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr'
  field_simp [hzC, hcC, hrC]
  ring

private theorem kaCubic_bubble_integrable :
    IntegrableOn kaBubbleTerm (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  let S := Ioo (0 : ℝ) 1
  have hB : IntegrableOn (fun q : ℝ × ℝ => 136 * ((q.1 * (1 - q.1)) ^ (-(3 / 5) : ℝ) *
      (q.2 * (1 - q.2)) ^ (-(4 / 5) : ℝ))) (S ×ˢ S) := by
    rw [IntegrableOn, QED.ThreeLoopD.volume_restrict_prod2]
    exact ((QED.ThreeLoopD.integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      (QED.ThreeLoopD.integrableOn_mul_one_sub_rpow_Ioo (by norm_num))).const_mul 136
  refine hB.mono' ?_ (ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo)
    fun q hq => ?_)
  · unfold kaBubbleTerm
    exact ((by fun_prop : Measurable
      (fun q : ℝ × ℝ => ((-log (1 - q.2) / 2 : ℝ) : ℂ))).mul
        (measurable_i10KaH 0)).aestronglyMeasurable
  · have hr : q.2 ∈ Ioo (0 : ℝ) 1 := hq.2
    have hc := sub_pos.mpr hr.2
    have hd := log_le_sub_one_of_pos (rpow_pos_of_pos hc (-(1 / 4) : ℝ))
    rw [log_rpow hc] at hd
    have hlog : 0 ≤ -log (1 - q.2) := neg_nonneg.mpr
      (log_nonpos hc.le (sub_le_self _ hr.1.le))
    have hb : ‖((-log (1 - q.2) / 2 : ℝ) : ℂ)‖ ≤
        2 * (q.2 * (1 - q.2)) ^ (-(1 / 4) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlog (by norm_num))]
      have hm : (1 - q.2) ^ (-(1 / 4) : ℝ) ≤
          (q.2 * (1 - q.2)) ^ (-(1 / 4) : ℝ) :=
        rpow_le_rpow_of_nonpos (mul_pos hr.1 hc)
          (mul_le_of_le_one_left hc.le hr.2.le) (by norm_num)
      linarith
    unfold kaBubbleTerm
    rw [norm_mul]
    refine (mul_le_mul hb (norm_i10KaH_le (by norm_num) hq)
      (norm_nonneg _) (mul_nonneg (by norm_num) (rpow_nonneg (mul_pos hr.1 hc).le _))).trans_eq ?_
    rw [show (-(4 / 5) : ℝ) = -(1 / 4) + -(11 / 20) by norm_num,
      rpow_add (mul_pos hr.1 hc)]
    ring

/-- The cubic coefficient integral of `Kₐ` is the bubble value plus the grouped residual. -/
theorem integral_deriv_i10KaH_zero_reduced :
    IntegrableOn i10KaCubicReduced (Ioo (0 : ℝ) 1) ∧
    (∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, deriv (fun w => i10KaH w q) 0) =
      ((∫ z in Ioo (0 : ℝ) 1, i10KaCubicReduced z) +
        (6 - π ^ 2 / 6 - zeta3 - π ^ 4 / 180) : ℝ) := by
  let S := Ioo (0 : ℝ) 1
  let T := S ×ˢ S
  let R : ℝ × ℝ → ℝ := fun q => i10KaCubicResidual q.1 q.2
  let F : ℝ × ℝ → ℂ := fun q => deriv (fun w => i10KaH w q) 0
  have hS : MeasurableSet S := measurableSet_Ioo
  have hT : MeasurableSet T := hS.prod hS
  have hpoint : F =ᵐ[volume.restrict T] fun q => (R q : ℂ) + kaBubbleTerm q :=
    ae_restrict_of_forall_mem hT fun _ => kaCubic_pointwise
  have hR : Measurable R := by unfold R i10KaCubicResidual; fun_prop
  have hB := kaCubic_bubble_integrable
  let b : ℝ × ℝ → ℝ := fun q => 68 * ((q.1 * (1 - q.1)) ^ (-(3 / 5) : ℝ) *
    (q.2 * (1 - q.2)) ^ (-(11 / 20) : ℝ))
  have hb : IntegrableOn b T := by
    rw [IntegrableOn, QED.ThreeLoopD.volume_restrict_prod2]
    exact ((QED.ThreeLoopD.integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      (QED.ThreeLoopD.integrableOn_mul_one_sub_rpow_Ioo (by norm_num))).const_mul 68
  have hFe : AEStronglyMeasurable F (volume.restrict T) :=
    ((Complex.continuous_ofReal.measurable.comp hR).aestronglyMeasurable.add hB.1).congr
      hpoint.symm
  have hF : IntegrableOn F T := (hb.div_const (1 / 40)).mono' hFe
    (ae_restrict_of_forall_mem hT fun q hq => by
      apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
      · exact (differentiable_i10KaH hq).differentiableOn.diffContOnCl_ball (Subset.rfl)
      · intro w hw
        apply norm_i10KaH_le _ hq
        rw [Metric.mem_sphere, dist_zero_right] at hw
        linarith)
  have hRi : IntegrableOn (fun q => (R q : ℂ)) T :=
    (hF.sub hB).congr (by
      filter_upwards [hpoint] with q hq
      change F q - kaBubbleTerm q = _
      rw [hq, add_sub_cancel_right])
  have hReal : Integrable R ((volume.restrict S).prod (volume.restrict S)) := by
    rw [← QED.ThreeLoopD.volume_restrict_prod2]
    change Integrable R (volume.restrict T)
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using
      Complex.reCLM.integrable_comp hRi
  have hSection : (fun z => ∫ r in S, R (z, r)) =ᵐ[volume.restrict S] i10KaCubicReduced :=
    ae_restrict_of_forall_mem hS fun z hz => (integral_i10KaCubicResidual hz).2
  refine ⟨hReal.integral_prod_left.congr hSection, ?_⟩
  have hOuter : (∫ q in T, R q) = ∫ z in S, i10KaCubicReduced z := by
    rw [show T = S ×ˢ S from rfl, QED.ThreeLoopD.volume_restrict_prod2, integral_prod]
    · exact setIntegral_congr_fun hS fun z hz => (integral_i10KaCubicResidual hz).2
    · exact hReal
  change (∫ q in T, F q) = _
  rw [integral_congr_ae hpoint]
  rw [show (∫ q in T, (R q : ℂ) + kaBubbleTerm q) =
    (∫ q in T, (R q : ℂ)) + ∫ q in T, kaBubbleTerm q from integral_add hRi hB]
  rw [integral_complex_ofReal, hOuter, show (∫ q in T, kaBubbleTerm q) = _ from
    integral_i10Ka_cubic_bubble_prod, Complex.ofReal_add]


section Primitive

open QED.Polylog.HPL Letter

/-- Evaluation of a finite linear combination of HPL words. -/
noncomputable def kaHplSum (x : ℝ) : List (ℝ × List Letter) → ℝ
  | [] => 0
  | (a, w) :: terms => a * hpl w x + kaHplSum x terms

private noncomputable def kaHplTermDeriv (x : ℝ) : List Letter → ℝ
  | [] => 0
  | a :: w => a.kernel x * hpl w x

private noncomputable def kaHplSumDeriv (x : ℝ) : List (ℝ × List Letter) → ℝ
  | [] => 0
  | (a, w) :: terms => a * kaHplTermDeriv x w + kaHplSumDeriv x terms

private theorem hasDerivAt_kaHplSum {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (terms : List (ℝ × List Letter)) :
    HasDerivAt (kaHplSum · terms) (kaHplSumDeriv x terms) x := by
  induction terms with
  | nil => exact hasDerivAt_const x 0
  | cons head tail ih =>
    obtain ⟨a, w⟩ := head
    have hd : HasDerivAt (hpl w) (kaHplTermDeriv x w) x := by
      cases w with
      | nil =>
        have e : hpl [] = fun _ => (1 : ℝ) := by funext y; rw [hpl]
        rw [e]
        exact hasDerivAt_const x 1
      | cons b v => exact hasDerivAt_hpl_cons b v hx
    exact (hd.const_mul a).add ih

noncomputable def kaPrimitiveRegular : List (ℝ × List Letter) :=
  [(2 * (π ^ 2 / 6) + 2, [zero]), (3, [zero, zero]),
   (4, [zero, zero, zero, one]), (-4, [zero, zero, one]),
   (2, [zero, zero, one, zero]), (-6, [zero, zero, one, one]),
   (-7, [zero, one]), (-2, [zero, one, zero, one]),
   (3 * (π ^ 2 / 6) + 2 * zeta3 - 1, [one]), (7 - 3 * (π ^ 2 / 6), [one, zero]),
   (-3, [one, zero, zero]), (4, [one, zero, zero, one]),
   (-3, [one, zero, one]), (2, [one, zero, one, zero]),
   (-6, [one, zero, one, one]), (2 * (π ^ 2 / 6) - 9, [one, one]),
   (1, [one, one, zero]), (-2, [one, one, zero, one])]

noncomputable def kaPrimitiveLeft : List (ℝ × List Letter) :=
  [(-2, [zero, zero, one]), (-2, [zero, one]),
   (-1, [zero, one, zero]), (3, [zero, one, one]),
   (-2, [one, zero]), (1, [one, zero, one]),
   (6, [one, one])]

noncomputable def kaPrimitiveRight : List (ℝ × List Letter) :=
  [(zeta3, []), (1 - 2 * (π ^ 2 / 6), [zero]),
   (-3, [zero, zero]), (2, [zero, zero, one]),
   (1, [zero, one]), (1, [zero, one, zero]),
   (-3, [zero, one, one]), ((π ^ 2 / 6), [one]),
   (1, [one, zero]), (-1, [one, zero, one])]

/-- An HPL primitive of the residual cubic integrand, grouped by its rational poles. -/
noncomputable def i10KaCubicPrimitive (x : ℝ) : ℝ :=
  kaHplSum x kaPrimitiveRegular + kaHplSum x kaPrimitiveLeft / x +
    kaHplSum x kaPrimitiveRight / (1 - x)

private theorem kaPrimitive_j₂ {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    logOneSubSqPrim x + 2 * zeta3 = 2 * hpl [zero, one, one] x := by
  have h : ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun y => (logOneSubSqPrim y + 2 * zeta3) / 2)
        (zero.kernel y * hpl [one, one] y) y := by
    intro y hy
    rw [hpl_one_one hy, Letter.kernel]
    exact (((hasDerivAt_logOneSubSqPrim hy).add_const _).div_const 2).congr_deriv (by ring)
  have h0 : Filter.Tendsto (fun y => (logOneSubSqPrim y + 2 * zeta3) / 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [neg_mul, neg_add_cancel, zero_div] using
      (tendsto_logOneSubSqPrim_zero.add_const (2 * zeta3)).div_const 2
  have e := eq_hpl_cons_of_hasDerivAt (a := zero) (w := [one, one])
    (fun ha => by have := ha one (by simp); cases this) h h0 x hx
  linarith only [e]

private theorem kaPrimitive_shuffle {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero] x * hpl [one] x = hpl [zero, one] x + hpl [one, zero] x ∧
    hpl [zero] x * hpl [zero, one] x = 2 * hpl [zero, zero, one] x + hpl [zero, one, zero] x ∧
    hpl [one] x * hpl [zero, one] x = hpl [one, zero, one] x + 2 * hpl [zero, one, one] x := by
  have h₁ := hpl_mul_hpl [zero] [one] hx
  have h₂ := hpl_mul_hpl [zero] [zero, one] hx
  have h₃ := hpl_mul_hpl [one] [zero, one] hx
  simp only [shuffle, shuffleAux, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.sum_cons, List.sum_nil, add_zero] at h₁ h₂ h₃
  exact ⟨h₁, by linarith only [h₂], by linarith only [h₃]⟩

/-- The derivative of the grouped HPL primitive is the reduced cubic integrand. -/
theorem hasDerivAt_i10KaCubicPrimitive {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i10KaCubicPrimitive (i10KaCubicReduced x) x := by
  have hc := (sub_pos.mpr hx.2).ne'
  have hL := (hasDerivAt_kaHplSum hx kaPrimitiveLeft).div (hasDerivAt_id' x) hx.1.ne'
  have hR := (hasDerivAt_kaHplSum hx kaPrimitiveRight).div
    ((hasDerivAt_id' x).const_sub 1) hc
  refine (((hasDerivAt_kaHplSum hx kaPrimitiveRegular).add hL).add hR).congr_deriv ?_
  dsimp only [kaPrimitiveRegular, kaPrimitiveLeft, kaPrimitiveRight, kaHplSum, kaHplSumDeriv,
    kaHplTermDeriv, Letter.kernel]
  rw [show hpl [] x = 1 by rw [hpl]]
  unfold i10KaCubicReduced i10KaCubicF i10KaCubicG
  dsimp only
  rw [log_mul hx.1.ne' hc, kaPrimitive_j₂ hx]
  have ⟨h₁, h₂, h₃⟩ := kaPrimitive_shuffle hx
  have h₄ := hpl_zero_zero x
  have h₅ := hpl_one_one hx
  have hU := hpl_zero_one hx
  change hpl [zero, one] x = Li₂ x at hU
  have hb : log (1 - x) = -hpl [one] x := by rw [hpl_one hx, neg_neg]
  rw [← hU, ← hpl_zero x, hb]
  rw [← hpl_zero x] at h₄
  rw [hb, neg_sq] at h₅
  let c := 1 - x
  let A := 2 / c + 1 / c ^ 2 + 1 / x + 1 / x ^ 2
  let B := A + 1 / x
  linear_combination (norm := (dsimp [A, B, c]; field_simp [hx.1.ne', hc]; ring))
    -A * h₁ - B * h₂ + B * h₃ - (3 / c + 3 / c ^ 2) * h₄ -
      (3 / c + 3 / x + 3 / x ^ 2) * h₅

private theorem kaHplSum_tendsto_zero (terms : List (ℝ × List Letter))
    (ht : ∀ e ∈ terms, ¬AllZero e.2) :
    Tendsto (kaHplSum · terms) (𝓝[>] 0) (𝓝 0) := by
  induction terms with
  | nil => exact tendsto_const_nhds
  | cons e l ih =>
    obtain ⟨a, w⟩ := e
    have h₁ := (tendsto_hpl_zero (ht (a, w) (List.mem_cons_self))).const_mul a
    have h₂ := ih (fun e he => ht e (List.mem_cons_of_mem _ he))
    simpa only [kaHplSum, mul_zero, add_zero] using h₁.add h₂

private theorem kaPrimitive_eventually_zero : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0 :=
  Ioo_mem_nhdsGT zero_lt_one

private theorem kaPrimitive_id_zero : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

private theorem kaPrimitive_sq_deriv (x : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
  simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hasDerivAt_pow 2 x

private theorem kaPrimitive_one_div_zero :
    Tendsto (fun x => hpl [one] x / x) (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_log_one_sub_div_zero'.neg
  rw [neg_neg] at h
  refine h.congr' ?_
  filter_upwards [kaPrimitive_eventually_zero] with x hx
  rw [hpl_one hx, neg_div]

private theorem kaPrimitive_one_remainder_zero :
    Tendsto (fun x => (hpl [one] x - x) / x ^ 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have h₀ : Tendsto (fun x => hpl [one] x - x) (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_zero] using (tendsto_hpl_zero (w := [one]) (by simp [AllZero])).sub
      kaPrimitive_id_zero
  have hc : Tendsto (fun x : ℝ => 2 * (1 - x)) (𝓝[>] 0) (𝓝 2) := by
    have h : Continuous (fun x : ℝ => 2 * (1 - x)) := by fun_prop
    simpa only [sub_zero, mul_one] using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have hv : Tendsto (fun x : ℝ => ((1 - x)⁻¹ - 1) / (2 * x)) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    refine (tendsto_const_nhds.div hc two_ne_zero).congr' ?_
    filter_upwards [kaPrimitive_eventually_zero] with x hx
    change 1 / (2 * (1 - x)) = _
    field_simp [hx.1.ne', (sub_pos.mpr hx.2).ne']
    ring
  exact HasDerivAt.lhopital_zero_right_on_Ioo zero_lt_one
    (fun x hx => ((hasDerivAt_hpl_cons one [] hx).sub (hasDerivAt_id' x)).congr_deriv
      (by rw [hpl_nil, Letter.kernel, mul_one])) (fun x _ => kaPrimitive_sq_deriv x)
    (fun x hx => mul_ne_zero two_ne_zero hx.1.ne') h₀
    (by simpa only [zero_pow two_ne_zero] using
      kaPrimitive_id_zero.pow 2) hv

private theorem kaPrimitive_zero_one_div_zero :
    Tendsto (fun x => hpl [zero, one] x / x) (𝓝[>] 0) (𝓝 1) := by
  refine tendsto_Li₂_div_zero.congr' ?_
  filter_upwards [kaPrimitive_eventually_zero] with x hx
  rw [hpl_zero_one hx]
  rfl

private theorem kaPrimitive_zero_one_remainder_zero :
    Tendsto (fun x => (hpl [zero, one] x - x) / x ^ 2) (𝓝[>] 0) (𝓝 (1 / 4)) := by
  have h₀ : Tendsto (fun x => hpl [zero, one] x - x) (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_zero] using (tendsto_hpl_zero (w := [zero, one]) (by simp [AllZero])).sub
      kaPrimitive_id_zero
  have hv : Tendsto (fun x => (x⁻¹ * hpl [one] x - 1) / (2 * x)) (𝓝[>] 0)
      (𝓝 (1 / 4)) := by
    have h := kaPrimitive_one_remainder_zero.div_const 2
    rw [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [kaPrimitive_eventually_zero] with x hx
    field_simp [hx.1.ne']
  exact HasDerivAt.lhopital_zero_right_on_Ioo zero_lt_one
    (fun x hx => (hasDerivAt_hpl_cons zero [one] hx).sub (hasDerivAt_id' x))
    (fun x _ => kaPrimitive_sq_deriv x) (fun x hx => mul_ne_zero two_ne_zero hx.1.ne') h₀
    (by simpa only [zero_pow two_ne_zero] using
      kaPrimitive_id_zero.pow 2) hv

private theorem kaPrimitive_one_one_div_zero :
    Tendsto (fun x => hpl [one, one] x / x) (𝓝[>] 0) (𝓝 0) := by
  have h₀ := tendsto_hpl_zero (w := [one]) (by simp [AllZero])
  have h := (kaPrimitive_one_div_zero.mul h₀).div_const 2
  rw [mul_zero, zero_div] at h
  refine h.congr' ?_
  filter_upwards [kaPrimitive_eventually_zero] with x hx
  have he : log (1 - x) = -hpl [one] x := by rw [hpl_one hx, neg_neg]
  rw [hpl_one_one hx, he, neg_sq]
  ring

private theorem kaPrimitive_zero_one_one_div_zero :
    Tendsto (fun x => hpl [zero, one, one] x / x) (𝓝[>] 0) (𝓝 0) := by
  have hv : Tendsto (fun x => (x⁻¹ * hpl [one, one] x) / 1) (𝓝[>] 0) (𝓝 0) :=
    kaPrimitive_one_one_div_zero.congr (fun x => by rw [div_one, div_eq_inv_mul])
  exact HasDerivAt.lhopital_zero_right_on_Ioo zero_lt_one
    (fun x hx => hasDerivAt_hpl_cons zero [one, one] hx) (fun x _ => hasDerivAt_id' x)
    (fun _ _ => one_ne_zero) (tendsto_hpl_zero (by simp [AllZero]))
    (tendsto_id.mono_left nhdsWithin_le_nhds) hv

/-- The left endpoint value of the residual cubic primitive. -/
theorem tendsto_i10KaCubicPrimitive_zero :
    Tendsto i10KaCubicPrimitive (𝓝[>] 0) (𝓝 zeta3) := by
  let R := fun x => kaHplSum x (kaPrimitiveRegular.drop 2)
  let Q := fun x => kaHplSum x (kaPrimitiveRight.drop 3)
  have hR : Tendsto R (𝓝[>] 0) (𝓝 0) := kaHplSum_tendsto_zero _ (by
    simp [kaPrimitiveRegular, List.mem_cons, AllZero])
  have hQ : Tendsto Q (𝓝[>] 0) (𝓝 0) := kaHplSum_tendsto_zero _ (by
    simp [kaPrimitiveRight, List.mem_cons, AllZero])
  have hX : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝 1) := by
    simpa only [sub_zero] using hX.const_sub 1
  have hA := ((hR.add ((hQ.add_const zeta3).div hc one_ne_zero)).add
    (((tendsto_mul_log_zero.const_mul (1 - 2 * (π ^ 2 / 6))).div hc one_ne_zero).sub
      ((tendsto_mul_log_sq_zero.const_mul (3 / 2)).div hc one_ne_zero))).sub
    (tendsto_mul_log_zero.mul (kaPrimitive_zero_one_remainder_zero.add
      (kaPrimitive_one_remainder_zero.const_mul 2)))
  have hB := ((kaPrimitive_zero_one_one_div_zero.add
    ((tendsto_hpl_zero (w := [one]) (by simp [AllZero])).mul kaPrimitive_zero_one_div_zero)).add
      (kaPrimitive_one_one_div_zero.const_mul 6))
  have h := hA.add hB
  simp only [zero_add, div_one, mul_zero, sub_zero, zero_mul, add_zero] at h
  refine h.congr' ?_
  filter_upwards [kaPrimitive_eventually_zero] with x hx
  have ⟨h₁, h₂, h₃⟩ := kaPrimitive_shuffle hx
  unfold i10KaCubicPrimitive
  dsimp only [kaPrimitiveRegular, kaPrimitiveRight, kaPrimitiveLeft, kaHplSum, hpl_nil]
  simp only [R, Q, Pi.div_apply, kaPrimitiveRegular, kaPrimitiveRight, List.drop,
    kaHplSum]
  rw [← hpl_zero x, show hpl [zero] x ^ 2 = 2 * hpl [zero, zero] x by
    rw [hpl_zero, hpl_zero_zero]; ring]
  linear_combination (norm := (field_simp [hx.1.ne', (sub_pos.mpr hx.2).ne']; ring))
    -2 / x * h₁ - 1 / x * h₂ + 1 / x * h₃

private noncomputable def kaPrimitive_logOneSubSq (x : ℝ) : ℝ :=
  log x * log (1 - x) ^ 2 + 2 * log (1 - x) * Li₂ (1 - x) - 2 * Li₃ (1 - x)

private theorem kaPrimitive_logOneSubSq_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    logOneSubSqPrim x = kaPrimitive_logOneSubSq x := by
  have hD (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt kaPrimitive_logOneSubSq (log (1 - y) ^ 2 / y) y := by
    have hc : 1 - y ∈ Ioo (0 : ℝ) 1 :=
      ⟨sub_pos.mpr hy.2, sub_lt_self 1 hy.1⟩
    have hdc := (hasDerivAt_id' y).const_sub 1
    have hl := kaMomentLogDeriv hy.2
    have h₂ := (hasDerivAt_Li₂' hc).comp y hdc
    have h₃ := (hasDerivAt_Li₃' hc).comp y hdc
    refine ((((hasDerivAt_log hy.1.ne').mul (hl.pow 2)).add ((hl.const_mul 2).mul h₂)).sub
      (h₃.const_mul 2)).congr_deriv ?_
    dsimp only [Function.comp_def, Pi.pow_apply]
    rw [sub_sub_cancel]
    field_simp [hy.1.ne', hc.1.ne']
    ring
  have h₁ : Tendsto kaPrimitive_logOneSubSq (𝓝[<] 1) (𝓝 0) := by
    have h := (((tendsto_log_one_sub_div_zero'.mul tendsto_mul_log_sq_zero).add
      (tendsto_log_mul_Li₂_zero.const_mul 2)).sub (tendsto_Li₃_zero_right.const_mul 2)).comp
      tendsto_one_sub_nhdsLT_one
    simp only [mul_zero, zero_add, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with y hy
    simp only [Function.comp_def, sub_sub_cancel, kaPrimitive_logOneSubSq]
    field_simp [(sub_pos.mpr hy.2).ne']
  have hf := eq_of_hasDerivAt_zero_of_tendsto_left
    (F := fun y => logOneSubSqPrim y - kaPrimitive_logOneSubSq y) (c := 0) zero_lt_one
    (fun y hy => by
      have h := (hasDerivAt_logOneSubSqPrim hy).sub (hD y hy)
      rwa [sub_self] at h)
    (by simpa only [sub_self] using tendsto_logOneSubSqPrim_one.sub h₁)
  exact sub_eq_zero.mp (hf x hx)

private theorem kaPrimitive_right_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    kaHplSum x kaPrimitiveRight = (
      let c := 1 - x
      let a := log x
      let b := log c
      (-(3 / 2)) * a * b ^ 2 - 2 * b * Li₂ c - a * b + Li₃ c +
        (1 - 2 * (π ^ 2 / 6)) * a - 3 / 2 * a ^ 2 + a * Li₂ x) := by
  have ⟨h₁, h₂, h₃⟩ := kaPrimitive_shuffle hx
  have h₄ := hpl_zero_zero x
  have hz := hpl_zero x
  have hb := hpl_one hx
  have hU : hpl [zero, one] x = Li₂ x := hpl_zero_one hx
  have hJ := kaPrimitive_j₂ hx
  have hRef := Li₂_add_Li₂_one_sub hx.1.le hx.2.le
  rw [kaPrimitive_logOneSubSq_eq hx] at hJ
  unfold kaPrimitive_logOneSubSq at hJ
  dsimp only [kaPrimitiveRight, kaHplSum, hpl_nil]
  rw [← hU, ← hz, show log (1 - x) = -hpl [one] x by rw [hb, neg_neg]]
  rw [← hz, show log (1 - x) = -hpl [one] x by rw [hb, neg_neg]] at hJ hRef
  rw [← hU] at hRef
  rw [← hz] at h₄
  linear_combination -h₁ - h₂ + h₃ - 3 * h₄ + hJ / 2 -
    hpl [one] x * hRef

private theorem kaPrimitive_Li₃_div_zero :
    Tendsto (fun y => Li₃ y / y) (𝓝[>] 0) (𝓝 1) := by
  refine hasDerivAt_Li₃_zero.tendsto_slope_zero_right.congr fun y => ?_
  simp only [zero_add, Li₃_zero, sub_zero, smul_eq_mul, div_eq_inv_mul]

private theorem kaPrimitive_log_remainder_zero :
    Tendsto (fun y => (log (1 - y) + y) / y ^ 2) (𝓝[>] 0) (𝓝 (-(1 / 2))) := by
  refine kaPrimitive_one_remainder_zero.neg.congr' ?_
  filter_upwards [kaPrimitive_eventually_zero] with y hy
  rw [hpl_one hy, ← neg_div]
  congr 1
  ring

private theorem kaPrimitive_Li₂_remainder_zero :
    Tendsto (fun y => (Li₂ y - y) / y ^ 2) (𝓝[>] 0) (𝓝 (1 / 4)) := by
  refine kaPrimitive_zero_one_remainder_zero.congr' ?_
  filter_upwards [kaPrimitive_eventually_zero] with y hy
  rw [hpl_zero_one hy]
  rfl

/-- After removing its explicit logarithmic terms, the right-pole quotient tends to zero. -/
theorem tendsto_i10KaCubicPrimitive_right_pole :
    Tendsto (fun x =>
      kaHplSum x kaPrimitiveRight / (1 - x) -
        (3 / 2 * log (1 - x) ^ 2 - log (1 - x) + π ^ 2 / 6)) (𝓝[<] 1) (𝓝 0) := by
  have hsub := tendsto_one_sub_nhdsLT_one
  have hlogs := kaPrimitive_log_remainder_zero.comp hsub
  have hLi₂ := kaPrimitive_Li₂_remainder_zero.comp hsub
  have hlog := tendsto_log_one_sub_div_zero'.comp hsub
  have hlog₀ : Tendsto log (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    simpa only [log_one] using
      (continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
  have hA := (hlogs.mul (tendsto_mul_log_sq_zero.comp hsub)).const_mul (-(3 / 2 : ℝ))
  have hB := (hLi₂.mul (tendsto_mul_log_zero.comp hsub)).const_mul (-2)
  have hC := hlogs.mul (tendsto_mul_log_zero.comp hsub)
  have hD := kaPrimitive_Li₃_div_zero.comp hsub
  have hE := hlog.const_mul (1 - 2 * (π ^ 2 / 6))
  have hF := (hlog.mul hlog₀).const_mul (3 / 2)
  have hG := hlog.mul tendsto_Li₂_one_left
  have h := ((((((hA.add hB).sub hC).add hD).add hE).sub hF).add hG).sub_const (π ^ 2 / 6)
  have hv : -(3 / 2 : ℝ) * (-(1 / 2) * 0) + (-2) * (1 / 4 * 0) - (-(1 / 2)) * 0 + 1 +
      (1 - 2 * (π ^ 2 / 6)) * (-1) - 3 / 2 * ((-1) * 0) + (-1) * (π ^ 2 / 6) -
        π ^ 2 / 6 = 0 := by ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with x hx
  rw [kaPrimitive_right_eq hx]
  simp only [Function.comp_def, sub_sub_cancel]
  field_simp [(sub_pos.mpr hx.2).ne']
  ring

private theorem kaPrimitive_hpl_scaled_zero (w : List Letter) :
    Tendsto (fun y => y ^ (1 / 2 : ℝ) * hpl w (1 - y)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, h⟩ := abs_hpl_le_one_sub_rpow w (ε := 1 / 4) (by norm_num)
  refine tendsto_zero_of_abs_le_rpow (C := C) (r := 1 / 4) (b := 1 / 2)
    (by norm_num) (by norm_num) fun y hy => ?_
  have h' := h (1 - y) ⟨by linarith only [hy.2], sub_lt_self 1 hy.1⟩
  rw [sub_sub_cancel] at h'
  rw [abs_mul, abs_of_nonneg (rpow_nonneg hy.1.le _)]
  calc
    _ ≤ y ^ (1 / 2 : ℝ) * (C * y ^ (-(1 / 4) : ℝ)) :=
      mul_le_mul_of_nonneg_left h' (rpow_nonneg hy.1.le _)
    _ = C * y ^ (1 / 4 : ℝ) := by
      rw [mul_left_comm, ← rpow_add hy.1]
      norm_num

private theorem kaPrimitive_scaled_regular {w : List Letter} :
    Tendsto (fun y => (hpl (zero :: w) (1 - y) - hpl (zero :: w) 1) /
      y ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have hf := ((tendsto_hpl_one (a := zero) (by decide) w).comp
    tendsto_one_sub_nhdsGT_zero).sub_const (hpl (zero :: w) 1)
  rw [sub_self] at hf
  have hg : Tendsto (fun y : ℝ => y ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h := continuousAt_rpow_const (0 : ℝ) (1 / 2 : ℝ) (Or.inr (by norm_num))
    simpa only [zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using
      h.tendsto.mono_left nhdsWithin_le_nhds
  have hD (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun y => hpl (zero :: w) (1 - y) - hpl (zero :: w) 1)
        (-(hpl w (1 - y) / (1 - y))) y := by
    have hh := (hasDerivAt_hpl_cons zero w ⟨sub_pos.mpr hy.2, sub_lt_self 1 hy.1⟩).comp y
      ((hasDerivAt_id' y).const_sub 1)
    refine (hh.sub_const _).congr_deriv ?_
    simp only [Letter.kernel]
    ring
  have hG (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun y : ℝ => y ^ (1 / 2 : ℝ)) ((1 / 2) * y ^ (-(1 / 2) : ℝ)) y := by
    simpa only [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num] using
      (hasDerivAt_rpow_const (x := y) (p := (1 / 2 : ℝ)) (Or.inl hy.1.ne'))
  have h₁ : Tendsto (fun y : ℝ => 1 - y) (𝓝[>] 0) (𝓝 1) := by
    simpa only [sub_zero] using kaPrimitive_id_zero.const_sub 1
  have hv : Tendsto (fun y => -(hpl w (1 - y) / (1 - y)) /
        ((1 / 2) * y ^ (-(1 / 2) : ℝ))) (𝓝[>] 0) (𝓝 0) := by
    have h := ((kaPrimitive_hpl_scaled_zero w).const_mul (-2 : ℝ)).div h₁ one_ne_zero
    rw [mul_zero, zero_div] at h
    refine h.congr' ?_
    filter_upwards [kaPrimitive_eventually_zero] with y hy
    simp only [Pi.div_apply, rpow_neg hy.1.le, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  exact HasDerivAt.lhopital_zero_right_on_Ioo zero_lt_one hD hG
    (fun y hy => mul_ne_zero (by norm_num) (rpow_pos_of_pos hy.1 _).ne') hf hg hv

private theorem kaPrimitive_logpow_scaled_zero (n : ℕ) :
    Tendsto (fun y => y ^ (1 / 2 : ℝ) * (-log y) ^ n) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, h⟩ := abs_log_pow_le n (δ := 1 / 4) (by norm_num)
  refine tendsto_zero_of_abs_le_rpow (C := C) (r := 1 / 4) (b := 1)
    (by norm_num) zero_lt_one fun y hy => ?_
  rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg (rpow_nonneg hy.1.le _)]
  calc
    _ ≤ y ^ (1 / 2 : ℝ) * (C * y ^ (-(1 / 4) : ℝ)) :=
      mul_le_mul_of_nonneg_left (h y hy) (rpow_nonneg hy.1.le _)
    _ = C * y ^ (1 / 4 : ℝ) := by
      rw [mul_left_comm, ← rpow_add hy.1]
      norm_num

private theorem kaPrimitive_regular_logpow (w : List Letter)
    (hw : w = [] ∨ w.head? = some zero) (n : ℕ) :
    Tendsto (fun x => (hpl w x - hpl w 1) * hpl [one] x ^ n) (𝓝[<] 1) (𝓝 0) := by
  rcases w with _ | ⟨a, w⟩
  · simp only [hpl_nil, sub_self, zero_mul, tendsto_const_nhds]
  · have ha : a = zero := by simpa only [List.cons_ne_nil, List.head?_cons, Option.some.injEq,
      false_or] using hw
    subst a
    have h := ((kaPrimitive_scaled_regular (w := w)).mul
      (kaPrimitive_logpow_scaled_zero n)).comp tendsto_one_sub_nhdsLT_one
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with x hx
    simp only [Function.comp_def, sub_sub_cancel, hpl_one hx]
    have hu := (rpow_pos_of_pos (sub_pos.mpr hx.2) (1 / 2 : ℝ)).ne'
    generalize (1 - x) ^ (1 / 2 : ℝ) = u at hu ⊢
    field_simp [hu]

private noncomputable def kaPrimitiveReg₀ : List (ℝ × List Letter) :=
  [(2 * (π ^ 2 / 6 + 1), [zero]), (3, [zero, zero]), (4, [zero, zero, zero, one]),
   (-3, [zero, zero, one]), (2, [zero, zero, one, zero]), (-14, [zero, zero, one, one]),
   (3 * (π ^ 2 / 6) - 14, [zero, one]), (2, [zero, one, zero]), (-8, [zero, one, zero, one]),
   (8, [zero, one, one]), (-4, [zero, one, one, zero]), (12, [zero, one, one, one])]

private noncomputable def kaPrimitiveReg₁ : List (ℝ × List Letter) :=
  [(3 * (π ^ 2 / 6) + 2 * zeta3 - 1, []), (5 - 3 * (π ^ 2 / 6), [zero]),
   (-3, [zero, zero]), (4, [zero, zero, one]), (-3, [zero, one]),
   (2, [zero, one, zero]), (-2, [zero, one, one])]

private noncomputable def kaPrimitiveReg₂ : List (ℝ × List Letter) :=
  [((2 * (π ^ 2 / 6) - 3) / 2, []), (1 / 2, [zero]), (-1, [zero, one])]

private theorem kaPrimitive_regularity {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    kaHplSum x kaPrimitiveRegular + kaHplSum x kaPrimitiveLeft =
      kaHplSum x kaPrimitiveReg₀ + hpl [one] x * kaHplSum x kaPrimitiveReg₁ +
        hpl [one] x ^ 2 * kaHplSum x kaPrimitiveReg₂ := by
  have h₁ := hpl_eq_regExpand [one, zero] hx
  have h₂ := hpl_eq_regExpand [one, zero, zero] hx
  have h₃ := hpl_eq_regExpand [one, zero, zero, one] hx
  have h₄ := hpl_eq_regExpand [one, zero, one] hx
  have h₅ := hpl_eq_regExpand [one, zero, one, zero] hx
  have h₆ := hpl_eq_regExpand [one, zero, one, one] hx
  have h₇ := hpl_eq_regExpand [one, one] hx
  have h₈ := hpl_eq_regExpand [one, one, zero] hx
  have h₉ := hpl_eq_regExpand [one, one, zero, one] hx
  simp [regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux,
    evalExp] at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  dsimp only [kaHplSum, kaPrimitiveRegular, kaPrimitiveLeft, kaPrimitiveReg₀,
    kaPrimitiveReg₁, kaPrimitiveReg₂, hpl_nil]
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉]
  norm_num
  ring

private theorem kaPrimitive_regular_sum_logpow (terms : List (ℝ × List Letter))
    (ht : ∀ e ∈ terms, e.2 = [] ∨ e.2.head? = some zero) (n : ℕ) :
    Tendsto (fun x => (kaHplSum x terms - kaHplSum 1 terms) * hpl [one] x ^ n)
      (𝓝[<] 1) (𝓝 0) := by
  induction terms with
  | nil => simp only [kaHplSum, sub_self, zero_mul, tendsto_const_nhds]
  | cons e l ih =>
    obtain ⟨a, w⟩ := e
    have h₁ := (kaPrimitive_regular_logpow w (ht (a, w) List.mem_cons_self) n).const_mul a
    have h₂ := ih (fun e he => ht e (List.mem_cons_of_mem _ he))
    have h := h₁.add h₂
    rw [mul_zero, zero_add] at h
    exact h.congr fun x => by simp only [kaHplSum]; ring

private theorem kaPrimitive_scaled_sum_one (terms : List (ℝ × List Letter)) :
    Tendsto (fun x => (1 - x) ^ (1 / 2 : ℝ) * kaHplSum x terms) (𝓝[<] 1) (𝓝 0) := by
  induction terms with
  | nil => simp only [kaHplSum, mul_zero, tendsto_const_nhds]
  | cons e l ih =>
    obtain ⟨a, w⟩ := e
    have h := ((kaPrimitive_hpl_scaled_zero w).comp tendsto_one_sub_nhdsLT_one).const_mul a
    have h' := h.add ih
    rw [mul_zero, zero_add] at h'
    exact h'.congr fun x => by simp only [Function.comp_def, sub_sub_cancel, kaHplSum]; ring

private theorem kaPrimitive_left_div_one :
    Tendsto (fun x => kaHplSum x kaPrimitiveLeft / x - kaHplSum x kaPrimitiveLeft)
      (𝓝[<] 1) (𝓝 0) := by
  have hr : Tendsto (fun x : ℝ => (1 - x) ^ (1 / 2 : ℝ)) (𝓝[<] 1) (𝓝 0) := by
    have h := (continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto.comp
      (tendsto_one_sub_nhdsLT_one.mono_right nhdsWithin_le_nhds)
    simpa only [Function.comp_def, zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using h
  have hX : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := (hr.mul (kaPrimitive_scaled_sum_one kaPrimitiveLeft)).div hX one_ne_zero
  rw [zero_mul, zero_div] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with x hx
  have e : (1 - x) ^ (1 / 2 : ℝ) * (1 - x) ^ (1 / 2 : ℝ) = 1 - x := by
    rw [← rpow_add (sub_pos.mpr hx.2)]
    norm_num
  simp only [Pi.div_apply, ← mul_assoc, e]
  field_simp [hx.1.ne']

private theorem kaPrimitive_reg_values :
    kaHplSum 1 kaPrimitiveReg₀ = 3 * (π ^ 2 / 6) ^ 2 - 14 * (π ^ 2 / 6) + zeta3 +
      11 * (π ^ 4 / 90) / 2 ∧
    kaHplSum 1 kaPrimitiveReg₁ = -1 ∧ kaHplSum 1 kaPrimitiveReg₂ = -(3 / 2) := by
  simp only [kaHplSum, kaPrimitiveReg₀, kaPrimitiveReg₁, kaPrimitiveReg₂, hpl_nil, hpl_zero,
    hpl_zero_zero, log_one, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_zero_one_one_at_one, hpl_zero_one_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_one_zero_one_at_one, hpl_zero_one_one_at_one,
    hpl_zero_one_one_zero_at_one, hpl_zero_one_one_one_at_one]
  constructor
  · ring
  · constructor <;> ring

/-- The finite value of the residual cubic primitive at the right endpoint. -/
theorem tendsto_i10KaCubicPrimitive_one :
    Tendsto i10KaCubicPrimitive (𝓝[<] 1)
      (𝓝 (3 * (π ^ 2 / 6) ^ 2 - 13 * (π ^ 2 / 6) + zeta3 + 11 * (π ^ 4 / 90) / 2)) := by
  obtain ⟨hv₀, hv₁, hv₂⟩ := kaPrimitive_reg_values
  have h₀ := kaPrimitive_regular_sum_logpow kaPrimitiveReg₀ (by simp [kaPrimitiveReg₀]) 0
  have h₁ := kaPrimitive_regular_sum_logpow kaPrimitiveReg₁ (by simp [kaPrimitiveReg₁]) 1
  have h₂ := kaPrimitive_regular_sum_logpow kaPrimitiveReg₂ (by simp [kaPrimitiveReg₂]) 2
  simp only [pow_zero, mul_one] at h₀
  rw [hv₁] at h₁
  rw [hv₂] at h₂
  have h := ((((h₀.add_const (kaHplSum 1 kaPrimitiveReg₀)).add h₁).add h₂).add
    kaPrimitive_left_div_one).add (tendsto_i10KaCubicPrimitive_right_pole.add_const (π ^ 2 / 6))
  have h' := h.congr' (f₂ := i10KaCubicPrimitive) (by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with x hx
    have he := kaPrimitive_regularity hx
    unfold i10KaCubicPrimitive
    simp only [pow_one, hpl_one hx] at he ⊢
    linear_combination -he)
  rw [hv₀] at h'
  convert h' using 2
  ring

/-- The residual cubic coefficient in closed form. -/
theorem integral_i10KaCubicReduced :
    ∫ z in Ioo (0 : ℝ) 1, i10KaCubicReduced z = 13 * (π ^ 4 / 90 - π ^ 2 / 6) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
    integral_deriv_i10KaH_zero_reduced.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun _ => hasDerivAt_i10KaCubicPrimitive) hi tendsto_i10KaCubicPrimitive_zero
    tendsto_i10KaCubicPrimitive_one]
  ring

/-- The complete Laurent truncation of the first subtracted remainder. -/
theorem hasTruncLaurent_i10Ka : QED.ThreeLoopD.HasTruncLaurent i10Ka i10KaLaurent 4 := by
  have h := hasTruncLaurent_i10Ka_leading
  rw [integral_deriv_i10KaH_zero_reduced.2, integral_i10KaCubicReduced] at h
  convert h using 2 with ε
  unfold i10KaLaurent
  push_cast
  ring

end Primitive

end QED.ThreeLoopE
