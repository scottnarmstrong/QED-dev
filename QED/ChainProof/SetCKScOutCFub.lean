/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutC
public import QED.ChainProof.SetCKScOutSFub
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the Fubini swap for the outer-massive corner

Helper level (no frozen statement). On the cube `(Y, y₃, x) ∈ (0, 1)³` times the outer node
`X ∈ (0, 1)` the kernel of the outer-massive corner is
`1{y₃ < Y, x < X} T(Y, y₃, x, Q(X) - Q(x)) · Q'(X)/(Q(X) + t)²` (`scOutCKerT`). Each
`(Y, y₃, x)`-section is, by the node change of variables `scOutS_section`, the
`(u + v)⁻²`-integral of the weight, which is `cornerGm (√t) 0 y₃ (Y - y₃) x` wherever
`M = Y² - t y₃ (Y - y₃) ≠ 0`, i.e. almost everywhere (`ae_scOutC_mass_ne`: for fixed `Y`
the zero set is the root set of a nonzero quadratic in `y₃`).

Given a dominating function for `∫₀^∞ |T|/(u + v)² dv` on the cube (**`ScOutCBound t`**),
one Fubini swap gives (**`scOutCH_isScOutCHDensity_of_bound`**)

`C(0, t) = ∫₀¹ H_C(X) Q'(X)/(Q(X) + t)² dX`,
`H_C(X) = 2 ∫_{(0,1)³} 1{y₃ < Y, x < X} T(Y, y₃, x, Q(X) - Q(x))` (`scOutCH`).

The domination `ScOutCBound` is the remaining analytic input of G4C (see the status notes).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The corner kernel `1{y₃ < Y, x < X} T(Y, y₃, x, Q(X) - Q(x))`. -/
noncomputable def scOutCKer (Y y3 x X : ℝ) : ℝ :=
  if y3 < Y ∧ x < X then scOutCT Y y3 x (scOutVX x X) else 0

/-- The corner kernel with the weight `Q'(X)/(Q(X) + t)²`, on `(Y, (y₃, x)) × X`. -/
noncomputable def scOutCKerT (t : ℝ) (q : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  scOutCKer q.1.1 q.1.2.1 q.1.2.2 q.2 * (setCKdQ q.2 / (setCKQ q.2 + t) ^ 2)

/-- **The G4C weight** `H_C(X)`: twice a triple integral over the cube. -/
noncomputable def scOutCH (X : ℝ) : ℝ :=
  2 * ∫ p, scOutCKer p.1 p.2.1 p.2.2 X ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
    ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))))

/-- **The domination hypothesis for G4C** at `t`. -/
def ScOutCBound (t : ℝ) : Prop :=
  ∃ D : ℝ × ℝ × ℝ → ℝ, Integrable D ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) ∧
    ∀ᵐ p ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))),
      0 ≤ D p ∧ (p.2.1 < p.1 →
        ∫ v in Ioi 0, |scOutCT p.1 p.2.1 p.2.2 v / (setCKQ p.2.2 + t + v) ^ 2| ≤ D p)

/-- The zero set of `M = Y² - t y₃ (Y - y₃)` in `y₃` is finite (`Y ≠ 0`). -/
theorem scOutC_mass_zero_finite {t Y : ℝ} (hY : Y ≠ 0) :
    {y3 : ℝ | Y ^ 2 - t * (y3 * (Y - y3)) = 0}.Finite := by
  open Polynomial in
  set p : ℝ[X] := C t * X ^ 2 - C (t * Y) * X + C (Y ^ 2) with hp
  have hev : ∀ y, p.eval y = Y ^ 2 - t * (y * (Y - y)) := fun y => by
    simp only [hp, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    ring
  have hp0 : p ≠ 0 := fun h => by
    have := hev 0
    rw [h, eval_zero] at this
    exact hY (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
  refine (p.rootSet_finite ℝ).subset fun y hy => ?_
  rw [mem_rootSet]
  refine ⟨hp0, ?_⟩
  rw [Polynomial.coe_aeval_eq_eval, hev]
  exact hy

/-- **`M ≠ 0` almost everywhere on the cube.** -/
theorem ae_scOutC_mass_ne (t : ℝ) : ∀ᵐ p ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
    ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))),
    p.1 ^ 2 - t * (p.2.1 * (p.1 - p.2.1)) ≠ 0 := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hs : MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ^ 2 - t * (p.2.1 * (p.1 - p.2.1)) ≠ 0} :=
    (measurableSet_eq_fun (by fun_prop) measurable_const).compl
  refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).2 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with Y hY
  have h1 : ∀ᵐ y3 ∂μ, Y ^ 2 - t * (y3 * (Y - y3)) ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact (scOutC_mass_zero_finite hY.1.ne').measure_zero _
  exact (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h1

theorem measurable_scOutCT : Measurable fun q : ℝ × ℝ × ℝ × ℝ =>
    scOutCT q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hk : Measurable fun r : (ℝ × ℝ × ℝ × ℝ) × ℝ =>
      if 0 < r.2 ∧ r.2 ≤ r.1.2.2.2 then
        scOutCk (cornerC0 r.1.2.2.1) (cornerC1 r.1.2.2.1 r.1.2.1 (r.1.1 - r.1.2.1))
          (cornerC2 r.1.2.2.1 r.1.2.1 (r.1.1 - r.1.2.1))
          (cornerC3 r.1.2.2.1 r.1.2.1 (r.1.1 - r.1.2.1)) (scOutCm r.1.1 r.1.2.1 r.1.2.2.1)
          (r.1.2.1 * (r.1.1 - r.1.2.1)) (scOutRho r.1.2.2.1)
          (scOutCs r.1.1 r.1.2.1 r.1.2.2.1) r.2
      else 0 := by
    refine Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop))) ?_ measurable_const
    unfold scOutCk scOutCs betaG cornerC0 cornerC1 cornerC2 cornerC3
      QED.TwoLoop.UnitSCReduce.cornerP2 cornerG cornerR scOutCm scOutRho setCKQ
    refine Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop)
      (by fun_prop)
  have hK := hk.stronglyMeasurable.integral_prod_right' (ν := volume)
  have hKe : (fun q : ℝ × ℝ × ℝ × ℝ => scOutCK (cornerC0 q.2.2.1)
      (cornerC1 q.2.2.1 q.2.1 (q.1 - q.2.1)) (cornerC2 q.2.2.1 q.2.1 (q.1 - q.2.1))
      (cornerC3 q.2.2.1 q.2.1 (q.1 - q.2.1)) (scOutCm q.1 q.2.1 q.2.2.1) (q.2.1 * (q.1 - q.2.1))
      (scOutRho q.2.2.1) (scOutCs q.1 q.2.1 q.2.2.1) q.2.2.2) = fun q => ∫ v', (if 0 < v' ∧
        v' ≤ q.2.2.2 then scOutCk (cornerC0 q.2.2.1) (cornerC1 q.2.2.1 q.2.1 (q.1 - q.2.1))
          (cornerC2 q.2.2.1 q.2.1 (q.1 - q.2.1)) (cornerC3 q.2.2.1 q.2.1 (q.1 - q.2.1))
          (scOutCm q.1 q.2.1 q.2.2.1) (q.2.1 * (q.1 - q.2.1)) (scOutRho q.2.2.1)
          (scOutCs q.1 q.2.1 q.2.2.1) v' else 0) := by
    funext q
    unfold scOutCK
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
    funext v'
    simp only [indicator, mem_Ioc]
  have hkap : Measurable fun q : ℝ × ℝ × ℝ × ℝ => scOutCkap (cornerA0 q.2.2.1 q.2.1 (q.1 - q.2.1))
      (cornerA1 q.2.2.1 q.2.1 (q.1 - q.2.1)) (cornerA2 q.2.2.1 q.2.1 (q.1 - q.2.1))
      (scOutCm q.1 q.2.1 q.2.2.1) (q.2.1 * (q.1 - q.2.1)) (scOutRho q.2.2.1)
      (scOutCs q.1 q.2.1 q.2.2.1) q.2.2.2 := by
    unfold scOutCkap scOutCs betaG cornerA0 cornerA1 cornerA2
      QED.TwoLoop.UnitSCReduce.cornerP1 cornerG cornerQ scOutCm scOutRho setCKQ
    exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop)
      (by fun_prop)
  have hP : Measurable fun q : ℝ × ℝ × ℝ × ℝ =>
      -(cornerC0 q.2.2.1 * scOutRho q.2.2.1 * log (scOutCm q.1 q.2.1 q.2.2.1)) := by
    unfold cornerC0 scOutRho scOutCm setCKQ
    fun_prop
  unfold scOutCT scOutCTg
  exact (hKe ▸ hK.measurable).add hkap |>.add hP

section

variable {t : ℝ}

theorem scOutC_hM {Y y3 x : ℝ} (hM : Y ^ 2 - t * (y3 * (Y - y3)) ≠ 0) :
    scOutCm Y y3 x - y3 * (Y - y3) * (setCKQ x + t) ≠ 0 := by
  unfold scOutCm
  convert hM using 1
  ring

theorem integrableOn_scOutCT (ht : 0 < t) {Y y3 x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM : Y ^ 2 - t * (y3 * (Y - y3)) ≠ 0) :
    IntegrableOn (fun v => scOutCT Y y3 x v / (setCKQ x + t + v) ^ 2) (Ioi 0) :=
  (scOutCTg_integral (scOutCm_pos hY h3 hx) (mul_pos h3.1 (by linarith [h3.2]))
    (scOutRho_pos hx) (scOutSu_pos ht hx) (scOutCs_nonneg hx) (scOutC_hM hM) _ _ _ _ _ _ _).1

theorem scOutCKerT_eq_ite {p : ℝ × ℝ × ℝ} (h : p.2.1 < p.1) (X : ℝ) :
    scOutCKerT t (p, X) = (if p.2.2 < X then scOutCT p.1 p.2.1 p.2.2 (scOutVX p.2.2 X) else 0) *
      (setCKdQ X / (setCKQ X + t) ^ 2) := by
  simp only [scOutCKerT, scOutCKer, h, true_and]

theorem scOutCKerT_eq_zero {p : ℝ × ℝ × ℝ} (h : ¬p.2.1 < p.1) (X : ℝ) :
    scOutCKerT t (p, X) = 0 := by
  simp only [scOutCKerT, scOutCKer, h, false_and, ↓reduceIte, zero_mul]

/-- The sections of the kernel over the cube (where `M ≠ 0`). -/
theorem scOutCKerT_section (ht : 0 < t) {p : ℝ × ℝ × ℝ}
    (hp : p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2.2 ∈ Ioo (0 : ℝ) 1)
    (hM : p.1 ^ 2 - t * (p.2.1 * (p.1 - p.2.1)) ≠ 0) :
    Integrable (fun X => scOutCKerT t (p, X)) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      ∫ X in Ioo (0 : ℝ) 1, scOutCKerT t (p, X) =
        if p.2.1 < p.1 then cornerGm (√t) 0 p.2.1 (p.1 - p.2.1) p.2.2 else 0 := by
  by_cases h : p.2.1 < p.1
  · have h3 : p.2.1 ∈ Ioo (0 : ℝ) p.1 := ⟨hp.2.1.1, h⟩
    obtain ⟨hi, hv⟩ := scOutS_section hp.2.2 (integrableOn_scOutCT ht hp.1 h3 hp.2.2 hM)
    simp only [scOutCKerT_eq_ite h, h, ↓reduceIte]
    exact ⟨hi, hv.trans (scOutC_cornerGm_eq ht hp.1 h3 hp.2.2 hM).symm⟩
  · simp only [scOutCKerT_eq_zero h, h, ↓reduceIte, integral_zero]
    exact ⟨integrable_zero _ _ _, trivial⟩

theorem measurable_scOutCKerT (t : ℝ) : Measurable (scOutCKerT t) := by
  have hQ := measurable_setCKQ
  have hv : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => scOutVX q.1.2.2 q.2 := by
    unfold scOutVX
    exact (hQ.comp measurable_snd).sub (hQ.comp measurable_fst.snd.snd)
  have hK : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ =>
      scOutCT q.1.1 q.1.2.1 q.1.2.2 (scOutVX q.1.2.2 q.2) :=
    measurable_scOutCT.comp (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
      (measurable_fst.snd.snd.prodMk hv)))
  have hc : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => setCKdQ q.2 / (setCKQ q.2 + t) ^ 2 := by
    unfold setCKdQ
    exact (by fun_prop : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => q.2 * (2 - q.2) / (1 - q.2) ^ 2).div
      (((hQ.comp measurable_snd).add measurable_const).pow_const 2)
  have hs : MeasurableSet {q : (ℝ × ℝ × ℝ) × ℝ | q.1.2.1 < q.1.1 ∧ q.1.2.2 < q.2} :=
    (measurableSet_lt measurable_fst.snd.fst measurable_fst.fst).inter
      (measurableSet_lt measurable_fst.snd.snd measurable_snd)
  unfold scOutCKerT scOutCKer
  exact (Measurable.ite hs hK measurable_const).mul hc

/-- **The Fubini hypothesis for G4C**, given the domination. -/
theorem integrable_scOutCKerT (ht : 0 < t) (hB : ScOutCBound t) :
    Integrable (scOutCKerT t) (((volume.restrict (Ioo (0 : ℝ) 1)).prod
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  obtain ⟨D, hD, hB⟩ := hB
  have hm := measurable_scOutCKerT t
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_mem_cube, ae_scOutC_mass_ne t] with p hp hM
    exact (scOutCKerT_section ht hp hM).1
  refine Integrable.mono' hD hm.norm.aestronglyMeasurable.integral_prod_right' ?_
  filter_upwards [ae_mem_cube, ae_scOutC_mass_ne t, hB] with p hp hM hb
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  by_cases h : p.2.1 < p.1
  · have h3 : p.2.1 ∈ Ioo (0 : ℝ) p.1 := ⟨hp.2.1.1, h⟩
    have hk : IntegrableOn (fun v => |scOutCT p.1 p.2.1 p.2.2 v| /
        (setCKQ p.2.2 + t + v) ^ 2) (Ioi 0) := by
      refine IntegrableOn.congr_fun (integrableOn_scOutCT ht hp.1 h3 hp.2.2 hM).abs
        (fun v _ => ?_) measurableSet_Ioi
      rw [abs_div, abs_sq]
    obtain ⟨-, hv⟩ := scOutS_section (t := t) hp.2.2 hk
    have e : ∫ X in Ioo (0 : ℝ) 1, ‖scOutCKerT t (p, X)‖ =
        ∫ X in Ioo (0 : ℝ) 1, (if p.2.2 < X then |scOutCT p.1 p.2.1 p.2.2 (scOutVX p.2.2 X)|
          else 0) * (setCKdQ X / (setCKQ X + t) ^ 2) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun X hX => ?_
      rw [scOutCKerT_eq_ite h, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (crossTdQ_div_nonneg ht hX)]
      split_ifs
      · rfl
      · simp
    rw [e, hv]
    refine le_trans (le_of_eq (setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_))
      (hb.2 h)
    rw [abs_div, abs_sq]
  · simp only [scOutCKerT_eq_zero h, norm_zero, integral_zero]
    exact hb.1

/-- A `Y`-node of the unit as an integral over the square. -/
theorem scOutC_node_eq (f : ℝ → ℝ → ℝ → ℝ) (Y : ℝ) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hG : Integrable (fun q : ℝ × ℝ => if q.1 < Y then f q.1 (Y - q.1) q.2 else 0)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) :
    ∫ y3 in (0 : ℝ)..Y, ∫ x in (0 : ℝ)..1, f y3 (Y - y3) x =
      ∫ q, (if q.1 < Y then f q.1 (Y - q.1) q.2 else 0)
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  rw [integral_prod _ hG]
  set I : ℝ → ℝ := fun y3 => ∫ x in Ioo (0 : ℝ) 1, f y3 (Y - y3) x with hI
  have hJ : ∀ y3, ∫ x, (if y3 < Y then f y3 (Y - y3) x else 0)
      ∂(volume.restrict (Ioo (0 : ℝ) 1)) = (Iio Y).indicator I y3 := by
    intro y3
    by_cases h : y3 < Y
    · simp only [h, ↓reduceIte, indicator, mem_Iio, hI]
    · simp [h, indicator]
  simp only [hJ]
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have e : Iio Y ∩ Ioo 0 1 = Ioo 0 Y := by
    ext y; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨h, h0, -⟩; exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩; exact ⟨h, h0, h.trans hY.2⟩
  rw [e, intervalIntegral.integral_of_le hY.1.le, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun y3 _ => ?_
  rw [hI, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

end

/-- **G4C (Stage K), `Q`-derivative form, given the domination**: for every `t > 0` with
`ScOutCBound t`, `C(0, t) = ∫₀¹ H_C(X) Q'(X)/(Q(X) + t)² dX`. -/
theorem scOutC_eq_of_bound {t : ℝ} (ht : 0 < t) (hB : ScOutCBound t) :
    scOutC t = ∫ X in (0 : ℝ)..1, scOutCH X * (setCKdQ X / (setCKQ X + t) ^ 2) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have H := integrable_scOutCKerT ht hB
  set Gi : ℝ × ℝ × ℝ → ℝ := fun p =>
    if p.2.1 < p.1 then cornerGm (√t) 0 p.2.1 (p.1 - p.2.1) p.2.2 else 0 with hGidef
  have hGe : (fun p => ∫ X, scOutCKerT t (p, X) ∂μ) =ᵐ[μ.prod (μ.prod μ)] Gi := by
    filter_upwards [ae_mem_cube, ae_scOutC_mass_ne t] with p hp hM
    exact (scOutCKerT_section ht hp hM).2
  have hGi : Integrable Gi (μ.prod (μ.prod μ)) := H.integral_prod_left.congr hGe
  have hnode : ∀ᵐ Y ∂μ, (∫ y3 in (0 : ℝ)..Y, ∫ x in (0 : ℝ)..1,
      cornerGm (√t) 0 y3 (Y - y3) x) = ∫ q, Gi (Y, q) ∂(μ.prod μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hGi.prod_right_ae] with Y hY hs
    exact scOutC_node_eq (fun y3 y4 x => cornerGm (√t) 0 y3 y4 x) Y hY hs
  have hswap := integral_integral_swap (f := fun p X => scOutCKerT t (p, X)) H
  rw [scOutC, ← setIntegral_Ioo_eq_intervalIntegral, ← setIntegral_Ioo_eq_intervalIntegral,
    integral_congr_ae hnode, ← integral_prod Gi hGi, ← integral_congr_ae hGe, hswap,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [scOutCKerT, scOutCH]
  rw [integral_mul_const]
  ring

/-- **G4C (Stage K), `Q`-derivative form**, conditional on the domination for every `t > 0`. -/
theorem scOutCH_isScOutCHDensity_of_bound (hB : ∀ t : ℝ, 0 < t → ScOutCBound t) :
    IsScOutCHDensity scOutCH := fun t ht => scOutC_eq_of_bound ht (hB t ht)

end QED.ChainProof.SetCK

end
