/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBPauli
import QED.OneLoop.VertexSpatial
import QED.Integration.TwoLoopParametricAlgebra
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The undoubled vertex with an affine numerator and two photon denominators

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), layer 5 of the
plan. On the doubled line `d` the merged counterterm insertion at `cbBParams` is
`b (1/D_d - 2m A_d/D_d²)`; the doubled part is treated in
`QED/ChainProof/SetCRegDispCtLoBPauli.lean`. The undoubled part replaces `A_d` by `1`, so the
numerator of the outer vertex is **affine** in the loop momentum. Its engine limit
(`QED.TwoLoop.VPHalfAtLimit.prodLimit` with energy coefficient `0`) is evaluated here for two
photon denominators: the spatial integral at order one
(`QED.ChainProof.CtLoB.integral_spatialW_zero`, `QED.ChainProof.CtLoB.dblTimeY_zero`), then the
simplex integral over the mixed mass, `∫₀¹ (t A + (1-t) B)⁻² dt = (A B)⁻¹`.

* `affN c₀ c ℓ = c₀ + Σ_i ℓ_i c_i`, with `continuous_affN`, `norm_affN_le`, `affN_cons`,
  `affN_shift` (the hypotheses of the engine and of the spatial integral);
* `integral_inv_sq_affine`: `∫₀¹ (t A + (1-t) B)⁻² dt = (A B)⁻¹` for `A, B > 0`;
* **`prodLimit_affN_two`**: `prodLimit 0 (affN c₀ c) m ![a, b] =
  ∫ 6 y (1-y) i (π²/6) affN(-K) / (Δ_a Δ_b)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set intervalIntegral
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.TwoLoop.VPHalfAtLimit
open QED.Integration.Feynman

/-! ### Affine numerators -/

/-- The affine numerator `c₀ + Σ_i ℓ_i c_i`. -/
noncomputable def affN (c₀ : ℂ) (c : Fin 4 → ℂ) (ℓ : Fin 4 → ℝ) : ℂ :=
  c₀ + ∑ i, (ℓ i : ℂ) * c i

theorem continuous_affN (c₀ : ℂ) (c : Fin 4 → ℂ) : Continuous (affN c₀ c) := by
  unfold affN
  fun_prop

theorem norm_affN_le (c₀ : ℂ) (c : Fin 4 → ℂ) (ℓ : Fin 4 → ℝ) :
    ‖affN c₀ c ℓ‖ ≤ (‖c₀‖ + ∑ i, ‖c i‖) * (1 + ‖ℓ‖) ^ 2 := by
  have h1 : ‖affN c₀ c ℓ‖ ≤ ‖c₀‖ + ∑ i, ‖c i‖ * ‖ℓ‖ := by
    unfold affN
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm ℓ i) (norm_nonneg _)
  have hl : 0 ≤ ‖ℓ‖ := norm_nonneg _
  have hS : 0 ≤ ∑ i, ‖c i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h0 : 0 ≤ ‖c₀‖ := norm_nonneg _
  rw [← Finset.sum_mul] at h1
  refine h1.trans ?_
  nlinarith [mul_nonneg hS hl, mul_nonneg h0 hl, mul_nonneg (mul_nonneg hS hl) hl,
    mul_nonneg (mul_nonneg h0 hl) hl]

theorem affN_cons (c₀ : ℂ) (c : Fin 4 → ℂ) (v : Fin 3 → ℝ) :
    ∃ β γ : ℂ, ∀ t : ℝ, affN c₀ c (Fin.cons t v : Fin 4 → ℝ) = 0 * (t : ℂ) ^ 2 + β * t + γ :=
  ⟨c 0, c₀ + ∑ k, (v k : ℂ) * c k.succ, fun t => by
    simp only [affN, Fin.sum_univ_succ (n := 3), Fin.cons_zero, Fin.cons_succ]
    ring⟩

theorem affN_shift (c₀ : ℂ) (c : Fin 4 → ℂ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) (w : Fin 3 → ℝ) :
    affN c₀ c (Fin.cons (-shiftK p' p z 0) (w - shiftKs p' p z) : Fin 4 → ℝ) =
      affN c₀ c (-shiftK p' p z) + ∑ k, (w k : ℂ) * c k.succ +
        ∑ k, ∑ l, ((w k * w l : ℝ) : ℂ) * (0 : ℂ) := by
  rw [cons_sub_shiftKs]
  simp only [affN, Fin.sum_univ_succ (n := 3), Pi.sub_apply, Fin.cons_zero, Fin.cons_succ,
    Pi.neg_apply, mul_zero, Finset.sum_const_zero, add_zero]
  push_cast
  simp only [sub_eq_add_neg, add_mul, neg_mul, Finset.sum_add_distrib]
  ring

/-! ### The simplex integral -/

theorem affine_pos {t A B : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hA : 0 < A) (hB : 0 < B) :
    0 < t * A + (1 - t) * B := by
  have h2 : 0 ≤ (1 - t) * B := mul_nonneg (by linarith [ht.2]) hB.le
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h
    simpa using hB
  · nlinarith [mul_pos h hA]

/-- `∫₀¹ (t A + (1-t) B)⁻² dt = (A B)⁻¹`. -/
theorem integral_inv_sq_affine {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫ t in (0 : ℝ)..1, ((t * A + (1 - t) * B) ^ 2)⁻¹ = (A * B)⁻¹ := by
  have hpos : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < t * A + (1 - t) * B := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact affine_pos ht hA hB
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => t / (B * (t * A + (1 - t) * B)))
      (((t * A + (1 - t) * B) ^ 2)⁻¹) t := by
    intro t ht
    have h0 := (hpos t ht).ne'
    have hden : HasDerivAt (fun t => B * (t * A + (1 - t) * B)) (B * (1 * A + (0 - 1) * B)) t :=
      (((hasDerivAt_id t).mul_const A).add
        (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const B)).const_mul B
    convert (hasDerivAt_id' t).div hden (mul_ne_zero hB.ne' h0) using 1
    field_simp
    ring
  have hc : ContinuousOn (fun t => ((t * A + (1 - t) * B) ^ 2)⁻¹) (uIcc (0 : ℝ) 1) :=
    ContinuousOn.inv₀ (by fun_prop) fun t ht => pow_ne_zero 2 (hpos t ht).ne'
  rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  field_simp
  ring

/-! ### The value for two photon denominators -/

/-- **The undoubled vertex with an affine numerator and two photon denominators.** -/
theorem prodLimit_affN_two {m a b : ℝ} (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (c₀ : ℂ) (c : Fin 4 → ℂ) :
    prodLimit 0 (affN c₀ c) m ![a, b] p' p =
      ∫ z, feynWt 1 z * (I * ((π ^ 2 / 6 : ℝ) : ℂ) * affN c₀ c (-shiftK p' p z) /
        ((feynmanMass m a z.1 z.2 p' p : ℂ) * (feynmanMass m b z.1 z.2 p' p : ℂ)))
        ∂feynmanMeasure := by
  set M₀ := min a b
  have hM₀ : 0 < M₀ := lt_min ha hb
  have hMs : ∀ j, M₀ ≤ (![a, b] : Fin 2 → ℝ) j := by
    intro j
    fin_cases j
    exacts [min_le_left _ _, min_le_right _ _]
  set Fa : ℝ × ℝ → ℝ := fun z => feynmanMass m a z.1 z.2 p' p
  set Fb : ℝ × ℝ → ℝ := fun z => feynmanMass m b z.1 z.2 p' p
  set Kz : ℝ × ℝ → ℂ := fun z =>
    feynWt 1 z * (I * ((π ^ 2 / 6 : ℝ) : ℂ) * affN c₀ c (-shiftK p' p z))
  set G : ℝ → ℝ × ℝ → ℂ := fun t z =>
    Kz z * ((((t * Fa z + (1 - t) * Fb z) ^ 2)⁻¹ : ℝ) : ℂ)
  have hFa : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, 0 < Fa z :=
    fun z hz => feynmanMass_pos_of_pos hm ha hp' hp hp0' hp0 hz
  have hFb : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, 0 < Fb z :=
    fun z hz => feynmanMass_pos_of_pos hm hb hp' hp hp0' hp0 hz
  have hmix : ∀ u ∈ simplexSet 1, ∀ z : ℝ × ℝ,
      feynmanMass m (mixMass ![a, b] u) z.1 z.2 p' p = u 0 * Fa z + (1 - u 0) * Fb z := by
    intro u hu z
    have hsq : mixMass ![a, b] u ^ 2 = u 0 * a ^ 2 + (1 - u 0) * b ^ 2 := by
      rw [mixMass, Real.sq_sqrt (mixMassSq_nonneg _ hu)]
      simp [mixMassSq, QED.Integration.TwoLoop.simplexPoint_eq_snoc, Fin.sum_univ_two, Fin.snoc]
    simp only [Fa, Fb, feynmanMass]
    rw [hsq]
    ring
  -- the spatial integral at fixed simplex point
  have h1 : ∀ u ∈ simplexSet 1,
      ∫ v, spatialP 0 (affN c₀ c) m (mixMass ![a, b] u) 1 0 0 p' p v =
        ∫ z, G (u 0) z ∂feynmanMeasure := by
    intro u hu
    have hM := mixMass_ge hM₀.le hMs hu
    have hΔ : ∀ z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1,
        0 < feynmanMass m (mixMass ![a, b] u) z.1 z.2 p' p :=
      fun z hz => feynmanMass_pos_of_pos hm (hM₀.trans_le hM) hp' hp hp0' hp0
        (Ioc_prod_subset hz)
    have hs := integral_spatialW_zero (continuous_feynWt 1)
      (fun z hz => (feynWt_norm_le hz.2).trans (le_refl _)) hm hM₀ hp' hp hp0' hp0
      (continuous_affN c₀ c) 0 (norm_affN_le c₀ c) hM 0
      (fun z => affN c₀ c (-shiftK p' p z)) (fun _ k => c k.succ) (fun _ _ _ => 0) hΔ
      (fun z _ w => affN_shift c₀ c p' p z w)
    refine hs.trans (integral_congr_ae (ae_feynmanMeasure.mono fun z hz => ?_))
    simp only [G, Kz]
    rw [dblTimeY_zero _ _ _ (hΔ z hz), hmix u hu z]
    simp only [Finset.sum_const_zero, sub_zero, zero_div, zero_add, mul_zero]
    push_cast
    ring
  have hS : ∫ u in simplexSet 1, ∫ v, spatialP 0 (affN c₀ c) m (mixMass ![a, b] u) 1 0 0 p' p v =
      ∫ u in simplexSet 1, (fun t => ∫ z, G t z ∂feynmanMeasure) (u 0) :=
    setIntegral_congr_fun (measurableSet_simplexSet 1) h1
  have hset : simplexSet 1 = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Icc 0 1 := by
    ext W
    have hW : W = Fin.snoc (Fin.elim0 : Fin 0 → ℝ) (W 0) := by
      funext i
      fin_cases i
      rfl
    conv_lhs => rw [hW]
    rw [snoc_mem_simplexSet_iff]
    simp [MeasurableEquiv.funUnique]
  have e1 : ∫ u in simplexSet 1, (fun t => ∫ z, G t z ∂feynmanMeasure) (u 0) =
      ∫ t in (0 : ℝ)..1, (∫ z, G t z ∂feynmanMeasure) := by
    rw [hset, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    exact (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
      (fun t => ∫ z, G t z ∂feynmanMeasure) (Icc 0 1)
  -- Fubini between the simplex parameter and the Feynman square
  have hKz : Continuous Kz :=
    (continuous_feynWt 1).mul (continuous_const.mul
      ((continuous_affN c₀ c).comp (continuous_shiftK p' p).neg))
  have hFa' : Continuous Fa := continuous_feynmanMass m a p' p
  have hFb' : Continuous Fb := continuous_feynmanMass m b p' p
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod feynmanMeasure) := by
    rw [feynmanMeasure_eq, Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    refine (ContinuousOn.integrableOn_compact hK ?_).mono_set
      (prod_mono Ioc_subset_Icc_self (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
    show ContinuousOn (fun q : ℝ × (ℝ × ℝ) => G q.1 q.2) _
    refine (hKz.comp continuous_snd).continuousOn.mul
      (Complex.continuous_ofReal.comp_continuousOn ?_)
    refine ContinuousOn.inv₀ (((continuous_fst.mul (hFa'.comp continuous_snd)).add
      ((continuous_const.sub continuous_fst).mul (hFb'.comp continuous_snd))).pow 2).continuousOn
      fun q hq => pow_ne_zero 2 (affine_pos hq.1 (hFa q.2 hq.2) (hFb q.2 hq.2)).ne'
  have hswap : ∫ t in (0 : ℝ)..1, (∫ z, G t z ∂feynmanMeasure) =
      ∫ z, (∫ t in (0 : ℝ)..1, G t z) ∂feynmanMeasure := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_integral_swap hint
  simp only [prodLimit, zero_add, Nat.factorial_one, Nat.cast_one, one_mul]
  rw [hS, e1, hswap]
  refine integral_congr_ae (ae_feynmanMeasure.mono fun z hz => ?_)
  have hz' := Ioc_prod_subset hz
  simp only [G]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_inv_sq_affine (hFa z hz') (hFb z hz')]
  simp only [Kz, Fa, Fb]
  push_cast
  ring

end QED.ChainProof.CtLoB

end
