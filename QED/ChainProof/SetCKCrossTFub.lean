/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCrossTBd
public import QED.ChainProof.SetCKCornInFub
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G3: the Stieltjes identity for `X(t, 0)` in `Q`-derivative form

Helper level (no frozen statement). On the cube `(Y, y₃, x) ∈ (0, 1)³` times the outer node
`X ∈ (0, 1)` the G3 kernel is `1{y₃ < Y < X} T(Y, y₃, x, w_Y(X))/(1 - Y) · Q'(X)/(Q(X) + t)²`
(`crossTKerT`), `w_Y(X) = (1-Y)(Q(X) - Q(Y))`. Since `M_t(Y) + w_Y(X) = (1-Y)(Q(X) + t)`, each
`(Y, y₃, x)`-section is, by the node change of variables (`cornIn_cv`), the `(M + v)⁻²`-integral
`∫₀^∞ T/(M + v)² dv = crossTGm 0 (√t) y₃ (Y - y₃) x` (`crossT_section`,
`crossTGm_eq_integral`). The bound `crossT_exists_bound` and the integrability of `crossTDom`
on the cube (`integrable_crossTDom`) make the kernel integrable on the product
(`integrable_crossTKerT`), and one Fubini swap gives

**`crossTH_isCrossTHDensity`**: `X(t, 0) = ∫₀¹ H(X) Q'(X)/(Q(X) + t)² dX` for every `t > 0`,

with `H(X) = ∫_{(0,1)³} 1{y₃ < Y < X} T(Y, y₃, x, (1-Y)(Q(X) - Q(Y)))/(1 - Y) dY dy₃ dx`
(`crossTH`). No pole term and no integration by parts occur.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The G3 kernel `1{y₃ < Y < X} T(Y, y₃, x, w_Y(X))/(1 - Y)`. -/
noncomputable def crossTKer (Y y3 x X : ℝ) : ℝ :=
  if y3 < Y ∧ Y < X then crossTT Y y3 x (cornInWX Y X) / (1 - Y) else 0

/-- The G3 kernel with the weight `Q'(X)/(Q(X) + t)²`, on `(Y, (y₃, x)) × X`. -/
noncomputable def crossTKerT (t : ℝ) (q : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  crossTKer q.1.1 q.1.2.1 q.1.2.2 q.2 * (setCKdQ q.2 / (setCKQ q.2 + t) ^ 2)

/-- **The G3 weight** `H(X)`, a triple integral over the cube `(0, 1)³`. -/
noncomputable def crossTH (X : ℝ) : ℝ :=
  ∫ p, crossTKer p.1 p.2.1 p.2.2 X ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
    ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))))

/-- **The dominating function is integrable on the cube.** -/
theorem integrable_crossTDom {t : ℝ} (C : ℝ) :
    Integrable (fun p : ℝ × ℝ × ℝ => crossTDom t C p.1 p.2.1 p.2.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have iL : Integrable (fun x => -log x) μ := integrableOn_neg_log_Ioo
  have iL1 : Integrable (fun x => -log (1 - x)) μ :=
    cornIn_integrableOn_one_sub integrableOn_neg_log_Ioo
  have iS1 : Integrable (fun x => (√(1 - x))⁻¹) μ :=
    cornIn_integrableOn_one_sub integrableOn_inv_sqrt_Ioo
  have a : Integrable (fun p : ℝ × ℝ × ℝ => -log p.2.1) (μ.prod (μ.prod μ)) :=
    (iL.comp_fst μ).comp_snd μ
  have b : Integrable (fun p : ℝ × ℝ × ℝ => -log (1 - p.1)) (μ.prod (μ.prod μ)) :=
    iL1.comp_fst (μ.prod μ)
  have c : Integrable (fun p : ℝ × ℝ × ℝ => -log p.2.2) (μ.prod (μ.prod μ)) :=
    (iL.comp_snd μ).comp_snd μ
  have d : Integrable (fun p : ℝ × ℝ × ℝ => (√(1 - p.1))⁻¹ * (√(1 - p.2.1))⁻¹)
      (μ.prod (μ.prod μ)) :=
    iS1.mul_prod (iS1.comp_fst μ)
  have hs := ((((integrable_const (1 : ℝ)).add a).add b).add c |>.add d).const_mul
    (C * (1 + 1 / cornInM0 t) ^ 2)
  refine hs.congr (Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply, crossTDom]
  ring

theorem measurable_crossTT :
    Measurable fun p : ℝ × ℝ × ℝ × ℝ => crossTT p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hW0 : Measurable fun p : ℝ × ℝ × ℝ × ℝ =>
      betaG (cornerG p.2.1 (p.1 - p.2.1)) (p.2.1 * (p.1 - p.2.1)) p.2.2.1 * p.2.2.1 := by
    unfold betaG cornerG
    fun_prop
  have hw : Measurable fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2 := by fun_prop
  have hE : Measurable fun p : ℝ × ℝ × ℝ × ℝ =>
      (crossTA1 p.2.2.1 p.2.1 (p.1 - p.2.1) - crossTC2 p.2.2.1 p.2.1 (p.1 - p.2.1) * p.2.2.1) /
          p.2.2.2 +
        (crossTA2 p.2.2.1 p.2.1 (p.1 - p.2.1) * p.2.2.1 -
          crossTC3 p.2.2.1 p.2.1 (p.1 - p.2.1) * p.2.2.1 ^ 2 / 2) / p.2.2.2 ^ 2 +
        crossTC1 p.2.2.1 p.2.1 (p.1 - p.2.1) * log (p.2.2.2 /
          (betaG (cornerG p.2.1 (p.1 - p.2.1)) (p.2.1 * (p.1 - p.2.1)) p.2.2.1 * p.2.2.1)) +
        (crossTC2 p.2.2.1 p.2.1 (p.1 - p.2.1) /
            betaG (cornerG p.2.1 (p.1 - p.2.1)) (p.2.1 * (p.1 - p.2.1)) p.2.2.1 +
          crossTC3 p.2.2.1 p.2.1 (p.1 - p.2.1) /
            (2 * betaG (cornerG p.2.1 (p.1 - p.2.1)) (p.2.1 * (p.1 - p.2.1)) p.2.2.1 ^ 2)) := by
    unfold crossTA1 crossTN1 crossTA2 crossTPa crossTC1 crossTC2 crossTN2 crossTC3 crossTP3
      betaG cornerG
    fun_prop
  unfold crossTT crossTTg
  exact Measurable.ite (measurableSet_lt hW0 hw) hE measurable_const

section

variable {t Y : ℝ}

/-- The node form of a `(M + v)⁻²`-integrand. -/
theorem crossT_cv_integrand (hY : Y < 1) (ht : 0 < t) {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1)
    (k : ℝ) :
    (1 - Y) * setCKdQ X * (k / ((1 - Y) * (setCKQ Y + t) + cornInWX Y X) ^ 2) =
      k / (1 - Y) * (setCKdQ X / (setCKQ X + t) ^ 2) := by
  rw [cornInWX_add]
  have h1 : 1 - Y ≠ 0 := by linarith
  have h2 : setCKQ X + t ≠ 0 := by
    have := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩
    linarith
  field_simp

/-- **A section of the kernel** by the node change of variables. -/
theorem crossT_section (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) {k : ℝ → ℝ}
    (hk : IntegrableOn (fun v => k v / (massIn t Y + v) ^ 2) (Ioi 0)) :
    Integrable (fun X => (if Y < X then k (cornInWX Y X) / (1 - Y) else 0) *
        (setCKdQ X / (setCKQ X + t) ^ 2)) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      ∫ X in Ioo (0 : ℝ) 1, (if Y < X then k (cornInWX Y X) / (1 - Y) else 0) *
        (setCKdQ X / (setCKQ X + t) ^ 2) = ∫ v in Ioi 0, k v / (massIn t Y + v) ^ 2 := by
  have hMe : massIn t Y = (1 - Y) * (setCKQ Y + t) := by
    rw [massIn, ladderInnerMass_sqrt_eq ht.le hY.2]
  obtain ⟨hiff, hval⟩ := cornIn_cv hY (fun v => k v / (massIn t Y + v) ^ 2)
  set g : ℝ → ℝ := fun X => k (cornInWX Y X) / (1 - Y) * (setCKdQ X / (setCKQ X + t) ^ 2)
    with hgdef
  have hg : ∀ X ∈ Ioo Y 1,
      (1 - Y) * setCKdQ X * (k (cornInWX Y X) / (massIn t Y + cornInWX Y X) ^ 2) = g X := by
    intro X hX
    rw [hMe]
    exact crossT_cv_integrand hY.2 ht ⟨hY.1.trans hX.1, hX.2⟩ _
  have hgi : IntegrableOn g (Ioo Y 1) := (hiff.1 hk).congr_fun hg measurableSet_Ioo
  have he : ∀ X ∈ Ioo (0 : ℝ) 1, (if Y < X then k (cornInWX Y X) / (1 - Y) else 0) *
      (setCKdQ X / (setCKQ X + t) ^ 2) = (Ioo Y 1).indicator g X := by
    intro X hX
    by_cases h : Y < X
    · simp only [h, ↓reduceIte]
      rw [indicator_of_mem (show X ∈ Ioo Y 1 from ⟨h, hX.2⟩)]
    · simp only [h, ↓reduceIte, zero_mul]
      rw [indicator_of_notMem (show X ∉ Ioo Y 1 from fun h' => h h'.1)]
  have hsub : Ioo (0 : ℝ) 1 ∩ Ioo Y 1 = Ioo Y 1 :=
    inter_eq_right.2 (Ioo_subset_Ioo_left hY.1.le)
  refine ⟨?_, ?_⟩
  · have := (hgi.integrable_indicator measurableSet_Ioo).integrableOn (s := Ioo (0 : ℝ) 1)
    exact this.congr_fun (fun X hX => (he X hX).symm) measurableSet_Ioo
  · rw [setIntegral_congr_fun measurableSet_Ioo he, setIntegral_indicator measurableSet_Ioo,
      hsub, hval]
    exact (setIntegral_congr_fun measurableSet_Ioo hg).symm

theorem crossTKerT_eq_ite {p : ℝ × ℝ × ℝ} (h : p.2.1 < p.1) (X : ℝ) :
    crossTKerT t (p, X) =
      (if p.1 < X then crossTT p.1 p.2.1 p.2.2 (cornInWX p.1 X) / (1 - p.1) else 0) *
        (setCKdQ X / (setCKQ X + t) ^ 2) := by
  simp only [crossTKerT, crossTKer, h, true_and]

theorem crossTKerT_eq_zero {p : ℝ × ℝ × ℝ} (h : ¬p.2.1 < p.1) (X : ℝ) :
    crossTKerT t (p, X) = 0 := by
  simp only [crossTKerT, crossTKer, h, false_and, ↓reduceIte, zero_mul]

theorem integrableOn_crossTT (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) {y3 x : ℝ}
    (h3 : 0 < y3) (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun v => crossTT Y y3 x v / (massIn t Y + v) ^ 2) (Ioi 0) :=
  integrableOn_crossTTg (massIn_pos ht ⟨hY.1.le, hY.2.le⟩)
    (mul_pos (betaG_pos (cornerG_pos hY.2 h3)) hx.1)

/-- The sections of the kernel over the cube: integrable, with integral the unit integrand. -/
theorem crossTKerT_section (ht : 0 < t) {p : ℝ × ℝ × ℝ}
    (hp : p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2.2 ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun X => crossTKerT t (p, X)) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      ∫ X in Ioo (0 : ℝ) 1, crossTKerT t (p, X) =
        if p.2.1 < p.1 then crossTGm 0 (√t) p.2.1 (p.1 - p.2.1) p.2.2 else 0 := by
  by_cases h : p.2.1 < p.1
  · obtain ⟨hi, hv⟩ := crossT_section ht hp.1 (integrableOn_crossTT ht hp.1 hp.2.1.1 hp.2.2)
    simp only [crossTKerT_eq_ite h, h, ↓reduceIte]
    exact ⟨hi, hv.trans (crossTGm_eq_integral ht hp.1 hp.2.1.1 hp.2.2).symm⟩
  · simp only [crossTKerT_eq_zero h, h, ↓reduceIte, integral_zero]
    exact ⟨integrable_zero _ _ _, trivial⟩

theorem crossTDom_nonneg (ht : 0 < t) {C y3 x : ℝ} (hC : 0 ≤ C)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (h3 : y3 ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ crossTDom t C Y y3 x := by
  have hm := cornInM0_pos ht
  have lY := log_nonpos (by linarith [hY.2] : (0 : ℝ) ≤ 1 - Y) (by linarith [hY.1])
  have l3 := log_nonpos h3.1.le h3.2.le
  have lx := log_nonpos hx.1.le hx.2.le
  have hL : 0 ≤ 1 + (-log y3 - log (1 - Y) - log x) := by linarith
  unfold crossTDom
  positivity

theorem measurable_crossTKerT (t : ℝ) : Measurable (crossTKerT t) := by
  have hQ := measurable_setCKQ
  have hw : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => cornInWX q.1.1 q.2 := by
    unfold cornInWX
    exact measurable_const.sub measurable_fst.fst |>.mul ((hQ.comp measurable_snd).sub
      (hQ.comp measurable_fst.fst))
  have hK : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ =>
      crossTT q.1.1 q.1.2.1 q.1.2.2 (cornInWX q.1.1 q.2) / (1 - q.1.1) :=
    (measurable_crossTT.comp (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
      (measurable_fst.snd.snd.prodMk hw)))).div (measurable_const.sub measurable_fst.fst)
  have hc : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => setCKdQ q.2 / (setCKQ q.2 + t) ^ 2 := by
    unfold setCKdQ
    exact (by fun_prop : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => q.2 * (2 - q.2) / (1 - q.2) ^ 2).div
      (((hQ.comp measurable_snd).add measurable_const).pow_const 2)
  have hs : MeasurableSet {q : (ℝ × ℝ × ℝ) × ℝ | q.1.2.1 < q.1.1 ∧ q.1.1 < q.2} :=
    (measurableSet_lt measurable_fst.snd.fst measurable_fst.fst).inter
      (measurableSet_lt measurable_fst.fst measurable_snd)
  unfold crossTKerT crossTKer
  exact (Measurable.ite hs hK measurable_const).mul hc

theorem crossTdQ_div_nonneg (_ht : 0 < t) {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    0 ≤ setCKdQ X / (setCKQ X + t) ^ 2 :=
  div_nonneg (setCKdQ_pos hX).le (sq_nonneg _)

/-- **The Fubini hypothesis for G3**: the kernel is integrable on the cube times `(0, 1)`. -/
theorem integrable_crossTKerT (ht : 0 < t) :
    Integrable (crossTKerT t) (((volume.restrict (Ioo (0 : ℝ) 1)).prod
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  obtain ⟨C, hC, hB⟩ := crossT_exists_bound
  have hm := measurable_crossTKerT t
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_mem_cube] with p hp
    exact (crossTKerT_section ht hp).1
  refine Integrable.mono' (integrable_crossTDom (t := t) C)
    hm.norm.aestronglyMeasurable.integral_prod_right' ?_
  filter_upwards [ae_mem_cube] with p hp
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  by_cases h : p.2.1 < p.1
  · have hk : IntegrableOn (fun v => |crossTT p.1 p.2.1 p.2.2 v| /
        (massIn t p.1 + v) ^ 2) (Ioi 0) := by
      refine IntegrableOn.congr_fun (integrableOn_crossTT ht hp.1 hp.2.1.1 hp.2.2).abs
        (fun v _ => ?_) measurableSet_Ioi
      rw [abs_div, abs_sq]
    obtain ⟨-, hv⟩ := crossT_section ht hp.1 hk
    have h1Y : 0 < 1 - p.1 := by linarith [hp.1.2]
    have e : ∫ X in Ioo (0 : ℝ) 1, ‖crossTKerT t (p, X)‖ =
        ∫ X in Ioo (0 : ℝ) 1, (if p.1 < X then |crossTT p.1 p.2.1 p.2.2 (cornInWX p.1 X)| /
          (1 - p.1) else 0) * (setCKdQ X / (setCKQ X + t) ^ 2) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun X hX => ?_
      rw [crossTKerT_eq_ite h, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (crossTdQ_div_nonneg ht hX)]
      split_ifs
      · rw [abs_div, abs_of_pos h1Y]
      · simp
    rw [e, hv]
    refine le_trans (le_of_eq (setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_))
      (hB ht hp.2.1.1 h hp.1.2 hp.2.2)
    rw [abs_div, abs_sq]
  · simp only [crossTKerT_eq_zero h, norm_zero, integral_zero]
    exact crossTDom_nonneg ht hC hp.1 hp.2.1 hp.2.2

/-- The unit's `Y`-integrand as an integral over the square. -/
theorem crossTIntegrand_eq (Y : ℝ) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hG : Integrable (fun q : ℝ × ℝ => if q.1 < Y then crossTGm 0 (√t) q.1 (Y - q.1) q.2 else 0)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) :
    crossTIntegrand t Y = ∫ q, (if q.1 < Y then crossTGm 0 (√t) q.1 (Y - q.1) q.2 else 0)
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  rw [integral_prod _ hG]
  set I : ℝ → ℝ := fun y3 => ∫ x in Ioo (0 : ℝ) 1, crossTGm 0 (√t) y3 (Y - y3) x with hI
  have hJ : ∀ y3, ∫ x, (if y3 < Y then crossTGm 0 (√t) y3 (Y - y3) x else 0)
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
  rw [e, crossTIntegrand, intervalIntegral.integral_of_le hY.1.le, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun y3 _ => ?_
  rw [hI, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- The unit by Fubini on the cube times `(0, 1)`. -/
theorem integral_crossTIntegrand (ht : 0 < t) :
    ∫ Y in Ioo (0 : ℝ) 1, crossTIntegrand t Y =
      ∫ X in Ioo (0 : ℝ) 1, crossTH X * (setCKdQ X / (setCKQ X + t) ^ 2) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have H := integrable_crossTKerT ht
  set Gi : ℝ × ℝ × ℝ → ℝ := fun p =>
    if p.2.1 < p.1 then crossTGm 0 (√t) p.2.1 (p.1 - p.2.1) p.2.2 else 0 with hGidef
  have hGe : (fun p => ∫ X, crossTKerT t (p, X) ∂μ) =ᵐ[μ.prod (μ.prod μ)] Gi := by
    filter_upwards [ae_mem_cube] with p hp
    exact (crossTKerT_section ht hp).2
  have hGi : Integrable Gi (μ.prod (μ.prod μ)) := H.integral_prod_left.congr hGe
  have hnode : ∀ᵐ Y ∂μ, crossTIntegrand t Y = ∫ q, Gi (Y, q) ∂(μ.prod μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hGi.prod_right_ae] with Y hY hs
    exact crossTIntegrand_eq Y hY hs
  have hswap := integral_integral_swap (f := fun p X => crossTKerT t (p, X)) H
  rw [integral_congr_ae hnode, ← integral_prod Gi hGi, ← integral_congr_ae hGe, hswap]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [crossTKerT, crossTH]
  exact integral_mul_const _ _

/-- **G3 (Stage K), `Q`-derivative form**: `X(t, 0) = ∫₀¹ H(X) Q'(X)/(Q(X) + t)² dX` for every
`t > 0`. -/
theorem crossTH_isCrossTHDensity : IsCrossTHDensity crossTH := fun t ht => by
  rw [crossT, ← setIntegral_Ioo_eq_intervalIntegral, integral_crossTIntegrand ht,
    setIntegral_Ioo_eq_intervalIntegral]

end

end QED.ChainProof.SetCK

end
