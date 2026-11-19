/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCornInDomInt
public import QED.ChainProof.SetCKCornInNode
public import QED.ChainProof.SetCKPairFub
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G2: the Stieltjes identity for `C(t, 0)`

Helper level (no frozen statement). On the cube `(Y, y₃, x) ∈ (0, 1)³` times the outer node
`X ∈ (0, 1)` the G2 kernel is `1{y₃ < Y < X} K_tot(Y, y₃, x, w_Y(X)) Q'(X)/(Q(X) + t)`
(`cornInKerT`). Each `(Y, y₃, x)`-section is, by the change of variables `w = w_Y(X)`
(`cornIn_cv`), the node weight `G = ∫₀^∞ K_tot/(M + w) dw` (`cornIn_section`), and the
`w`-integral of `|K_tot|/(M + w)` is bounded by the integrable `cornInDom`
(`cornIn_exists_bound`, `integrable_cornInDom`), so the kernel is integrable on the product
(`integrable_cornInKerT`). With the per-node identity `cornInIntegrand_eq` and one Fubini swap,

**`rhoCornIn_isCornInDensity`**: `C(t, 0) = ∫₀¹ ρ_C(X) Q(X)/(Q(X) + t) dX` for every `t > 0`,

where `ρ_C(X) = 2 (e₁(X) + Q'(X) σ_C(X))/Q(X)` (`rhoCornIn`), `e₁(X) = e₁M(X)/(1-X)`, and the
inner node integral is the triple integral (`cornInSig`)
`σ_C(X) = ∫_{(0,1)³} 1{y₃ < Y < X} K_tot(Y, y₃, x, (1-Y)(Q(X) - Q(Y))) dY dy₃ dx`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The G2 kernel `1{y₃ < Y < X} K_tot(Y, y₃, x, w_Y(X))`. -/
noncomputable def cornInKer (Y y3 x X : ℝ) : ℝ :=
  if y3 < Y ∧ Y < X then cornInKt Y y3 x (cornInWX Y X) else 0

/-- The G2 kernel with the Stieltjes weight `Q'(X)/(Q(X) + t)`, on `(Y, (y₃, x)) × X`. -/
noncomputable def cornInKerT (t : ℝ) (q : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  cornInKer q.1.1 q.1.2.1 q.1.2.2 q.2 * (setCKdQ q.2 / (setCKQ q.2 + t))

/-- **The inner node integral** `σ_C(X)`, a triple integral over the cube `(0, 1)³`. -/
noncomputable def cornInSig (X : ℝ) : ℝ :=
  ∫ p, cornInKer p.1 p.2.1 p.2.2 X ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
    ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))))

/-- The pole residue `e₁(X) = e₁M(X)/(1 - X)` in `u = Q(X) + t`. -/
noncomputable def cornInE1 (X : ℝ) : ℝ := cornInE1M X / (1 - X)

/-- **The fibre density of G2**: `ρ_C(X) = 2 (e₁(X) + Q'(X) σ_C(X))/Q(X)`. -/
noncomputable def rhoCornIn (X : ℝ) : ℝ := 2 * (cornInE1 X + setCKdQ X * cornInSig X) / setCKQ X

section

variable {t Y : ℝ}

theorem ae_mem_cube : ∀ᵐ p ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
    ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))),
    p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2.2 ∈ Ioo (0 : ℝ) 1 := by
  rw [Measure.prod_restrict, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod (measurableSet_Ioo.prod
    measurableSet_Ioo))] with p hp
  exact ⟨hp.1, hp.2.1, hp.2.2⟩

theorem setCKdQ_div_nonneg (ht : 0 < t) {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    0 ≤ setCKdQ X / (setCKQ X + t) :=
  div_nonneg (setCKdQ_pos hX).le (by linarith [setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩])

/-- **A section of the kernel** by the node change of variables. -/
theorem cornIn_section (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) {k : ℝ → ℝ}
    (hk : IntegrableOn (fun w => k w / (massIn t Y + w)) (Ioi 0)) :
    Integrable (fun X => (if Y < X then k (cornInWX Y X) else 0) *
        (setCKdQ X / (setCKQ X + t))) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      ∫ X in Ioo (0 : ℝ) 1, (if Y < X then k (cornInWX Y X) else 0) *
        (setCKdQ X / (setCKQ X + t)) = ∫ w in Ioi 0, k w / (massIn t Y + w) := by
  have hMe : massIn t Y = (1 - Y) * (setCKQ Y + t) := by
    rw [massIn, ladderInnerMass_sqrt_eq ht.le hY.2]
  obtain ⟨hiff, hval⟩ := cornIn_cv hY (fun w => k w / (massIn t Y + w))
  set g : ℝ → ℝ := fun X => k (cornInWX Y X) * (setCKdQ X / (setCKQ X + t)) with hgdef
  have hg : ∀ X ∈ Ioo Y 1,
      (1 - Y) * setCKdQ X * (k (cornInWX Y X) / (massIn t Y + cornInWX Y X)) = g X := by
    intro X hX
    rw [hMe]
    exact cornIn_cv_integrand hY.2 ht ⟨hY.1.trans hX.1, hX.2⟩ _
  have hgi : IntegrableOn g (Ioo Y 1) := (hiff.1 hk).congr_fun hg measurableSet_Ioo
  have he : ∀ X ∈ Ioo (0 : ℝ) 1, (if Y < X then k (cornInWX Y X) else 0) *
      (setCKdQ X / (setCKQ X + t)) = (Ioo Y 1).indicator g X := by
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

theorem cornInKerT_eq_ite {p : ℝ × ℝ × ℝ} (h : p.2.1 < p.1) (X : ℝ) :
    cornInKerT t (p, X) = (if p.1 < X then cornInKt p.1 p.2.1 p.2.2 (cornInWX p.1 X) else 0) *
      (setCKdQ X / (setCKQ X + t)) := by
  simp only [cornInKerT, cornInKer, h, true_and]

theorem cornInKerT_eq_zero {p : ℝ × ℝ × ℝ} (h : ¬p.2.1 < p.1) (X : ℝ) :
    cornInKerT t (p, X) = 0 := by
  simp only [cornInKerT, cornInKer, h, false_and, ↓reduceIte, zero_mul]

theorem integrableOn_abs_cornInKt (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) {y3 x : ℝ}
    (h3 : 0 < y3) (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun w => |cornInKt Y y3 x w| / (massIn t Y + w)) (Ioi 0) := by
  have hM := massIn_pos ht ⟨hY.1.le, hY.2.le⟩
  have h0 : IntegrableOn (fun w => |cornInKt Y y3 x w / (massIn t Y + w)|) (Ioi 0) :=
    (cornInKt_integral hM h3 hY.2 hx).1.abs
  refine h0.congr_fun (fun w hw => ?_) measurableSet_Ioi
  have : 0 < massIn t Y + w := by linarith [mem_Ioi.1 hw]
  simp only [abs_div, abs_of_pos this]

/-- The sections of the kernel over the cube: integrable, with integral the node weight. -/
theorem cornInKerT_section (ht : 0 < t) {p : ℝ × ℝ × ℝ}
    (hp : p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2.2 ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun X => cornInKerT t (p, X)) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      ∫ X in Ioo (0 : ℝ) 1, cornInKerT t (p, X) =
        if p.2.1 < p.1 then cornInGn t p.1 p.2.1 p.2.2 else 0 := by
  by_cases h : p.2.1 < p.1
  · have hM := massIn_pos ht ⟨hp.1.1.le, hp.1.2.le⟩
    obtain ⟨hi, hv⟩ := cornIn_section ht hp.1 (cornInKt_integral hM hp.2.1.1 hp.1.2 hp.2.2).1
    simp only [cornInKerT_eq_ite h, h, ↓reduceIte]
    exact ⟨hi, hv⟩
  · simp only [cornInKerT_eq_zero h, h, ↓reduceIte, integral_zero]
    exact ⟨integrable_zero _ _ _, trivial⟩

theorem cornInDom_nonneg (ht : 0 < t) {C₁ C₂ y3 x : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (h3 : y3 ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ cornInDom t C₁ C₂ Y y3 x := by
  have hm := cornInM0_pos ht
  have lY := log_nonpos (by linarith [hY.2] : (0 : ℝ) ≤ 1 - Y) (by linarith [hY.1])
  have l3 := log_nonpos h3.1.le h3.2.le
  have lx := log_nonpos hx.1.le hx.2.le
  have hL : 0 ≤ (-log y3 - log (1 - Y) - log x) / cornInM0 t := div_nonneg (by linarith) hm.le
  unfold cornInDom
  positivity

theorem measurable_cornInKerT (t : ℝ) : Measurable (cornInKerT t) := by
  have hQ := measurable_setCKQ
  have hw : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => cornInWX q.1.1 q.2 := by
    unfold cornInWX
    exact measurable_const.sub measurable_fst.fst |>.mul ((hQ.comp measurable_snd).sub
      (hQ.comp measurable_fst.fst))
  have hK : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ =>
      cornInKt q.1.1 q.1.2.1 q.1.2.2 (cornInWX q.1.1 q.2) :=
    measurable_cornInKt.comp (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
      (measurable_fst.snd.snd.prodMk hw)))
  have hc : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => setCKdQ q.2 / (setCKQ q.2 + t) := by
    unfold setCKdQ
    exact (by fun_prop : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => q.2 * (2 - q.2) / (1 - q.2) ^ 2).div
      ((hQ.comp measurable_snd).add measurable_const)
  have hs : MeasurableSet {q : (ℝ × ℝ × ℝ) × ℝ | q.1.2.1 < q.1.1 ∧ q.1.1 < q.2} :=
    (measurableSet_lt measurable_fst.snd.fst measurable_fst.fst).inter
      (measurableSet_lt measurable_fst.fst measurable_snd)
  unfold cornInKerT cornInKer
  exact (Measurable.ite hs hK measurable_const).mul hc

/-- **The Fubini hypothesis for G2**: the kernel is integrable on the cube times `(0, 1)`. -/
theorem integrable_cornInKerT (ht : 0 < t) :
    Integrable (cornInKerT t) (((volume.restrict (Ioo (0 : ℝ) 1)).prod
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hB⟩ := cornIn_exists_bound
  have hm := measurable_cornInKerT t
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_mem_cube] with p hp
    exact (cornInKerT_section ht hp).1
  refine Integrable.mono' (integrable_cornInDom (t := t) C₁ C₂)
    hm.norm.aestronglyMeasurable.integral_prod_right' ?_
  filter_upwards [ae_mem_cube] with p hp
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  by_cases h : p.2.1 < p.1
  · have hk := integrableOn_abs_cornInKt ht hp.1 hp.2.1.1 hp.2.2
    obtain ⟨-, hv⟩ := cornIn_section ht hp.1 hk
    have e : ∫ X in Ioo (0 : ℝ) 1, ‖cornInKerT t (p, X)‖ =
        ∫ X in Ioo (0 : ℝ) 1, (if p.1 < X then |cornInKt p.1 p.2.1 p.2.2 (cornInWX p.1 X)|
          else 0) * (setCKdQ X / (setCKQ X + t)) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun X hX => ?_
      rw [cornInKerT_eq_ite h, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (setCKdQ_div_nonneg ht hX)]
      split_ifs <;> simp
    rw [e, hv]
    have hM := massIn_pos ht ⟨hp.1.1.le, hp.1.2.le⟩
    refine le_trans (le_of_eq (setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_))
      (hB ht hp.2.1.1 h hp.1.2 hp.2.2)
    have : 0 < massIn t p.1 + w := by linarith [mem_Ioi.1 hw]
    simp only [abs_div, abs_of_pos this]
  · simp only [cornInKerT_eq_zero h, norm_zero, integral_zero]
    exact cornInDom_nonneg ht hC₁ hC₂ hp.1 hp.2.1 hp.2.2

theorem integrableOn_cornInE1 (ht : 0 < t) :
    IntegrableOn (fun X => cornInE1 X / (setCKQ X + t)) (Ioo 0 1) := by
  have hc : ContinuousOn (fun X : ℝ => cornInE1M X / (X ^ 2 + (1 - X) * t)) (Icc 0 1) :=
    ContinuousOn.div (by unfold cornInE1M; fun_prop) (by fun_prop) fun X hX =>
      (pos_denom ht hX).ne'
  refine (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun (fun X hX => ?_)
    measurableSet_Ioo
  have h1 : 1 - X ≠ 0 := by linarith [hX.2]
  have hd := (pos_denom ht (Ioo_subset_Icc_self hX)).ne'
  unfold cornInE1
  rw [show setCKQ X + t = (X ^ 2 + (1 - X) * t) / (1 - X) by unfold setCKQ; field_simp]
  field_simp

/-- The node integral of the per-node function, by Fubini on the cube times `(0, 1)`. -/
theorem integral_cornInIntegrand (ht : 0 < t) :
    2 * ∫ Y in Ioo (0 : ℝ) 1, cornInIntegrand t Y =
      ∫ X in Ioo (0 : ℝ) 1, rhoCornIn X * (setCKQ X / (setCKQ X + t)) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have H := integrable_cornInKerT ht
  set Gi : ℝ × ℝ × ℝ → ℝ := fun p => if p.2.1 < p.1 then cornInGn t p.1 p.2.1 p.2.2 else 0
    with hGidef
  have hGe : (fun p => ∫ X, cornInKerT t (p, X) ∂μ) =ᵐ[μ.prod (μ.prod μ)] Gi := by
    filter_upwards [ae_mem_cube] with p hp
    exact (cornInKerT_section ht hp).2
  have hGi : Integrable Gi (μ.prod (μ.prod μ)) := H.integral_prod_left.congr hGe
  have hnode : ∀ᵐ Y ∂μ, cornInIntegrand t Y =
      cornInE1 Y / (setCKQ Y + t) + ∫ q, Gi (Y, q) ∂(μ.prod μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hGi.prod_right_ae] with Y hY hs
    rw [cornInIntegrand_eq ht hY hs, massIn, ladderInnerMass_sqrt_eq ht.le hY.2]
    congr 1
    have h1 : 1 - Y ≠ 0 := by linarith [hY.2]
    have h2 : setCKQ Y + t ≠ 0 := by
      have := setCKQ_nonneg ⟨hY.1.le, hY.2.le⟩
      linarith
    unfold cornInE1
    field_simp
  have hE := integrableOn_cornInE1 ht
  have hGq : Integrable (fun Y => ∫ q, Gi (Y, q) ∂(μ.prod μ)) μ := hGi.integral_prod_left
  have hS : Integrable (fun X => cornInSig X * (setCKdQ X / (setCKQ X + t))) μ := by
    refine H.integral_prod_right.congr (Eventually.of_forall fun X => ?_)
    simp only [cornInKerT, cornInSig]
    exact integral_mul_const _ _
  have hswap := integral_integral_swap (f := fun p X => cornInKerT t (p, X)) H
  have hL : ∫ Y, ∫ q, Gi (Y, q) ∂(μ.prod μ) ∂μ =
      ∫ X, cornInSig X * (setCKdQ X / (setCKQ X + t)) ∂μ := by
    rw [← integral_prod Gi hGi, ← integral_congr_ae hGe, hswap]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [cornInKerT, cornInSig]
    exact integral_mul_const _ _
  rw [integral_congr_ae hnode, integral_add hE hGq, hL]
  have e2 : ∫ X, rhoCornIn X * (setCKQ X / (setCKQ X + t)) ∂μ =
      ∫ X, (2 * (cornInE1 X / (setCKQ X + t)) +
        2 * (cornInSig X * (setCKdQ X / (setCKQ X + t)))) ∂μ := by
    refine setIntegral_congr_fun measurableSet_Ioo fun X hX => ?_
    have hQ : 0 < setCKQ X := by
      unfold setCKQ
      exact div_pos (pow_pos hX.1 2) (by linarith [hX.2])
    have hu : setCKQ X + t ≠ 0 := by linarith
    unfold rhoCornIn
    field_simp
  rw [e2, integral_add (hE.const_mul 2) (hS.const_mul 2), integral_const_mul,
    integral_const_mul]
  ring

/-- **G2 (Stage K)**: `ρ_C` is the Stieltjes density of the inner-massive corner unit,
`C(t, 0) = ∫₀¹ ρ_C(X) Q(X)/(Q(X) + t) dX` for every `t > 0`. -/
theorem rhoCornIn_isCornInDensity : IsCornInDensity rhoCornIn := fun t ht => by
  rw [cornIn, ← setIntegral_Ioo_eq_intervalIntegral, integral_cornInIntegrand ht,
    setIntegral_Ioo_eq_intervalIntegral]
  rfl

end

end QED.ChainProof.SetCK

end
