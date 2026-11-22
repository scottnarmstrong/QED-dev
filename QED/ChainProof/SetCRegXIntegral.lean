/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXDeriv
public import QED.ChainProof.SetCRegBubblePF
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The squared-mass derivative of the crossed unit

The separate monomial bounds from `QED/TwoLoop/UnitXCloseBound.lean` dominate
the mass-scaled derivative. On a neighborhood of a positive mass this also
dominates the unscaled derivative, permitting differentiation under the integral.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetCK

open QED.ChainProof.SetCRegBubble
open QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitXClose
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- The pointwise derivative in the second photon's squared mass. -/
noncomputable def crossDerivAt (a b : ℝ) (z : Fin 5 → ℝ) : ℝ :=
  let U := gXU (z 0) (z 1) (z 2) (z 3) (z 4)
  let V := gXE (z 0) (z 1) (z 2) (z 3) (z 4) + a * z 3 + b * z 4
  let F := z 1 * gPsi1 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) / (2 * U ^ 6)
  let G := z 1 * gPsi2 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) / (2 * U ^ 5)
  (z 4 / V) * (-2 * (F / V ^ 2) + G / V)

private theorem measurable_evalTerms (L : List Term) : Measurable (evalTerms L) := by
  induction L with
  | nil => exact measurable_const
  | cons t L ih =>
    have ht : Measurable fun z : Fin 5 → ℝ => (t.1 : ℝ) * ∏ k, z k ^ t.2.1 k := by
      exact Measurable.const_mul (Finset.measurable_prod _ fun k _ =>
        (measurable_pi_apply k).pow_const _) _
    exact ht.add ih

theorem measurable_crossDerivAt (a b : ℝ) : Measurable (crossDerivAt a b) := by
  have hU : Measurable fun z : Fin 5 → ℝ => gXU (z 0) (z 1) (z 2) (z 3) (z 4) := by
    unfold gXU
    fun_prop
  have hE : Measurable fun z : Fin 5 → ℝ => gXE (z 0) (z 1) (z 2) (z 3) (z 4) := by
    unfold gXE gXEn
    fun_prop
  unfold crossDerivAt
  simp only [mul_gPsi1_eq, mul_gPsi2_eq, gz_eq]
  have h₁ : Measurable (evalTerms domTerms₁) := measurable_evalTerms _
  have h₂ : Measurable (evalTerms domTerms₂) := measurable_evalTerms _
  fun_prop

private noncomputable def crossDerivMajorant (z : Fin 5 → ℝ) : ℝ :=
  (5 * absSum domTerms₁ + 5 * absSum domTerms₂) *
    ∏ k, z k ^ (-((domS : ℝ) / domN))

private theorem integrable_crossDerivMajorant :
    IntegrableOn (fun y => crossDerivMajorant (simplexPoint y)) (simplexSet 4) := by
  have hs0 : 0 ≤ (domS : ℝ) / domN := by positivity
  have hs1 : (domS : ℝ) / domN < 1 := by norm_num [domS, domN]
  have h := QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow
    (m := 4) Finset.univ hs0 hs1
  exact h.const_mul _

private theorem crossDerivAt_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {z : Fin 5 → ℝ} (hz : ∀ k, 0 < z k) (hsum : ∑ k, z k = 1) :
    ‖b * crossDerivAt a b z‖ ≤ crossDerivMajorant z := by
  let U := gXU (z 0) (z 1) (z 2) (z 3) (z 4)
  let E := gXE (z 0) (z 1) (z 2) (z 3) (z 4)
  let En := gXEn (z 0) (z 1) (z 2) (z 3) (z 4)
  let V := E + a * z 3 + b * z 4
  let P₁ := z 1 * gPsi1 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4)
  let P₂ := z 1 * gPsi2 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4)
  have hU : 0 < U := gXU_pos (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
  have hE : 0 < E := gXE_pos (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
  have he : En = U * E := by
    change En = U * (En / U)
    field_simp
  have hUV : En ≤ U * V := by
    rw [he]
    apply mul_le_mul_of_nonneg_left _ hU.le
    exact (le_add_of_nonneg_right (mul_nonneg ha (hz 3).le)).trans
      (le_add_of_nonneg_right (mul_nonneg hb (hz 4).le))
  have hEn : 0 < En := he ▸ mul_pos hU hE
  have hab : 0 ≤ a * z 3 := mul_nonneg ha (hz 3).le
  have hbb : 0 ≤ b * z 4 := mul_nonneg hb (hz 4).le
  have hV : 0 < V := add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hE hab) hbb
  have hzle (k : Fin 5) : z k ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => (hz j).le) (Finset.mem_univ k)
  have hN : 0 < domN := by norm_num [domN]
  have h₁ := listBound (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
    (by simpa only [gz_eq] using hzle) (by simpa only [gz_eq] using hsum) hN domTerms₁_ok
  have h₂ := listBound (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
    (by simpa only [gz_eq] using hzle) (by simpa only [gz_eq] using hsum) hN domTerms₂_ok
  have a₁ := abs_evalTerms_le (fun k => (hz k).le) domTerms₁
  have a₂ := abs_evalTerms_le (fun k => (hz k).le) domTerms₂
  rw [← gz_eq z, ← mul_gPsi1_eq, gz_eq] at a₁
  rw [← gz_eq z, ← mul_gPsi2_eq, gz_eq] at a₂
  simp only [gz_eq, mono, pow_one] at h₁ h₂
  have d₁ : U ^ 4 * En ^ 2 ≤ U ^ 6 * V ^ 2 := by
    calc
      U ^ 4 * En ^ 2 ≤ U ^ 4 * (U * V) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hEn.le hUV 2) (by positivity)
      _ = _ := by ring
  have d₂ : U ^ 4 * En ≤ 2 * U ^ 5 * V := by
    calc
      U ^ 4 * En ≤ U ^ 4 * (U * V) := mul_le_mul_of_nonneg_left hUV (by positivity)
      _ ≤ 2 * U ^ 5 * V := by
        rw [show U ^ 4 * (U * V) = U ^ 5 * V by ring, mul_assoc]
        exact le_mul_of_one_le_left (by positivity) (by norm_num)
  have b₁ : |P₁| / (U ^ 6 * V ^ 2) ≤ _ :=
    ((div_le_div_of_nonneg_left (abs_nonneg P₁) (by positivity) d₁).trans
      (div_le_div_of_nonneg_right a₁ (by positivity))).trans h₁
  have b₂ : |P₂| / (2 * U ^ 5 * V) ≤ _ :=
    ((div_le_div_of_nonneg_left (abs_nonneg P₂) (by positivity) d₂).trans
      (div_le_div_of_nonneg_right a₂ (by positivity))).trans h₂
  change ‖b * (z 4 / V * (-2 * (P₁ / (2 * U ^ 6) / V ^ 2) +
    P₂ / (2 * U ^ 5) / V))‖ ≤ _
  rw [← mul_assoc, ← mul_div_assoc, norm_mul, Real.norm_of_nonneg (div_nonneg hbb hV.le)]
  apply (mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hV).2
    (le_add_of_nonneg_left (add_nonneg hE.le hab)))).trans
  have e : -2 * (P₁ / (2 * U ^ 6) / V ^ 2) + P₂ / (2 * U ^ 5) / V =
      -(P₁ / (U ^ 6 * V ^ 2)) + P₂ / (2 * U ^ 5 * V) := by
    rw [div_div, div_div]
    ring_nf
  rw [e, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_div, abs_div, abs_of_pos (by positivity : 0 < U ^ 6 * V ^ 2),
    abs_of_pos (by positivity : 0 < 2 * U ^ 5 * V), crossDerivMajorant, add_mul]
  exact add_le_add b₁ b₂

/-- At positive squared mass, the derivative of the unit is the integral of
the pointwise derivative. -/
theorem hasDerivAt_crossUnit_right {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    HasDerivAt (crossUnit a)
      (∫ y in simplexSet 4, crossDerivAt a b (simplexPoint y)) b := by
  have hsp := QED.Integration.TwoLoop.continuous_simplexPoint' (m := 4)
  have hpos := QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos (by norm_num : 0 < 4)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t y => crossedAt a t (simplexPoint y))
    (F' := fun t y => crossDerivAt a t (simplexPoint y))
    (s := Ioi (b / 2)) (bound := fun y => (2 / b) * crossDerivMajorant (simplexPoint y))
    (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun t =>
      ((measurable_crossedAt a t).comp hsp.measurable).aestronglyMeasurable)
    (integrableOn_crossedAt ha hb.le)
    ((measurable_crossDerivAt a b).comp hsp.measurable).aestronglyMeasurable
    ?_ (integrable_crossDerivMajorant.const_mul _) ?_).2
  · filter_upwards [hpos] with y hy t ht
    have ht' : b / 2 < t := ht
    have hp : 0 < t := by linarith
    have h := crossDerivAt_bound ha hp.le hy (sum_simplexPoint y)
    rw [norm_mul, Real.norm_of_nonneg hp.le] at h
    have hm : (b / 2) * ‖crossDerivAt a t (simplexPoint y)‖ ≤
        crossDerivMajorant (simplexPoint y) :=
      (mul_le_mul_of_nonneg_right ht'.le (norm_nonneg _)).trans h
    have hbp : 0 < b / 2 := by positivity
    rw [show 2 / b = (b / 2)⁻¹ by rw [inv_div], ← div_eq_inv_mul]
    exact (le_div_iff₀ hbp).2 (by rw [mul_comm]; exact hm)
  · filter_upwards [hpos] with y hy t ht
    exact hasDerivAt_crossedAt_right a t (simplexPoint y) ha
      (le_trans (by positivity : 0 ≤ b / 2) ht.le) hy

/-- A common bound for the absolute mass-scaled derivative of the integrated
unit on the nonnegative half-line of spectator masses. -/
theorem exists_bound_mul_deriv_crossUnit_right :
    ∃ C : ℝ, ∀ a b : ℝ, 0 ≤ a → 0 < b → ‖b * deriv (crossUnit a) b‖ ≤ C := by
  refine ⟨∫ y in simplexSet 4, crossDerivMajorant (simplexPoint y), fun a b ha hb => ?_⟩
  rw [(hasDerivAt_crossUnit_right ha hb).deriv, ← integral_const_mul]
  refine norm_integral_le_of_norm_le integrable_crossDerivMajorant ?_
  filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos (by norm_num : 0 < 4)]
    with y hy
  exact crossDerivAt_bound ha hb.le hy (sum_simplexPoint y)

/-- The squared mass times the derivative vanishes when that mass tends to infinity. -/
theorem tendsto_mul_deriv_crossUnit_right {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {a b : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 ≤ a i) (hb : Tendsto b l atTop) :
    Tendsto (fun i => b i * deriv (crossUnit (a i)) (b i)) l (𝓝 0) := by
  have hsp := QED.Integration.TwoLoop.continuous_simplexPoint' (m := 4)
  have hpos := QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos (by norm_num : 0 < 4)
  have hb' := hb.eventually_gt_atTop 0
  let F (i : ι) (y : Fin 4 → ℝ) := b i * crossDerivAt (a i) (b i) (simplexPoint y)
  have hlim : Tendsto (fun i => ∫ y in simplexSet 4, F i y) l
      (𝓝 (∫ _ : Fin 4 → ℝ in simplexSet 4, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      integrable_crossDerivMajorant ?_
    · exact Eventually.of_forall fun i =>
        (((measurable_crossDerivAt _ _).comp hsp.measurable).const_mul _).aestronglyMeasurable
    · filter_upwards [ha, hb'] with i hai hbi
      filter_upwards [hpos] with y hy
      exact crossDerivAt_bound hai hbi.le hy (sum_simplexPoint y)
    · filter_upwards [hpos] with y hy
      refine (tendsto_mul_deriv_crossedAt_right ha hb hy).congr' ?_
      filter_upwards [ha, hb'] with i hai hbi
      rw [(hasDerivAt_crossedAt_right _ _ _ hai hbi.le hy).deriv]
      rfl
  rw [integral_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [ha, hb'] with i hai hbi
  rw [(hasDerivAt_crossUnit_right hai hbi).deriv]
  exact integral_const_mul _ _

/-- The squared-mass partial fractions of the dressed crossed photon, with
spectator squared mass `μ`. -/
noncomputable def crossPF (μ a b c : ℝ) : ℝ :=
  bubCoefC a b c * crossUnit μ c + bubCoefA a b c * crossUnit μ a +
    bubCoefB a b c * crossUnit μ b -
    bubCoefA2 a c * deriv (crossUnit μ) a - bubCoefB2 b c * deriv (crossUnit μ) b

/-- Exchanging the photon slots transports the derivatives to the first slot. -/
theorem crossPF_mirror (μ a b c : ℝ) :
    crossPF μ a b c =
      bubCoefC a b c * crossUnit c μ + bubCoefA a b c * crossUnit a μ +
        bubCoefB a b c * crossUnit b μ -
        bubCoefA2 a c * deriv (fun t => crossUnit t μ) a -
        bubCoefB2 b c * deriv (fun t => crossUnit t μ) b := by
  have h : (fun t => crossUnit t μ) = crossUnit μ :=
    funext fun t => crossUnit_mirror t μ
  rw [h, crossPF, crossUnit_mirror c μ, crossUnit_mirror a μ, crossUnit_mirror b μ]

/-- The two placements of the crossed partial fractions with the spectator's
Pauli–Villars difference. Photon exchange makes the two placements equal. -/
noncomputable def xExact (c lam Lam : ℝ) : ℝ :=
  2 * (crossPF (lam ^ 2) (lam ^ 2) (Lam ^ 2) c -
    crossPF (Lam ^ 2) (lam ^ 2) (Lam ^ 2) c)

private theorem tendsto_bubCoefs {ι : Type*} {l : Filter ι} {a b : ι → ℝ} {c : ℝ}
    (hc : 0 < c) (ha : Tendsto a l (𝓝 0)) (hb : Tendsto b l atTop) :
    Tendsto (fun i => bubCoefC (a i) (b i) c) l (𝓝 1) ∧
    Tendsto (fun i => bubCoefA (a i) (b i) c) l (𝓝 0) ∧
    Tendsto (fun i => bubCoefB (a i) (b i) c) l (𝓝 (-1)) ∧
    Tendsto (fun i => -a i / (a i - c)) l (𝓝 0) ∧
    Tendsto (fun i => bubCoefB2 (b i) c / b i) l (𝓝 (-1)) := by
  have hi := tendsto_inv_atTop_zero.comp hb
  have hd := (ha.mul hi).sub_const 1
  have hbc := (hi.const_mul c).const_sub 1
  have hac := ha.sub_const c
  have hb' := hb.eventually_gt_atTop 0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := ((hd.pow 2).const_mul (c ^ 2)).div ((hac.pow 2).mul (hbc.pow 2))
      (by simp [hc.ne'])
    have h' : Tendsto (fun i => c ^ 2 * (a i * (b i)⁻¹ - 1) ^ 2 /
        ((a i - c) ^ 2 * (1 - c * (b i)⁻¹) ^ 2)) l (𝓝 1) := by
      simpa [Pi.div_def, hc.ne'] using h
    refine h'.congr' ?_
    filter_upwards [hb'] with i hbi
    unfold bubCoefC
    field_simp [hbi.ne']
  · have hn := (((ha.pow 2).mul hi).add ha).sub_const (2 * c)
    have h := (ha.neg.mul hn).div (hd.mul (hac.pow 2)) (by simp [hc.ne'])
    have h' : Tendsto (fun i => -a i * (a i ^ 2 * (b i)⁻¹ + a i - 2 * c) /
        ((a i * (b i)⁻¹ - 1) * (a i - c) ^ 2)) l (𝓝 0) := by
      simpa [Pi.div_def] using h
    refine h'.congr' ?_
    filter_upwards [hb'] with i hbi
    unfold bubCoefA
    field_simp [hbi.ne']
  · have hn := (((ha.mul hi).sub ((ha.mul (hi.pow 2)).const_mul (2 * c))).add_const 1)
    have h := hn.div (hd.mul (hbc.pow 2)) (by norm_num)
    have h' : Tendsto (fun i => (a i * (b i)⁻¹ - (2 * c) * (a i * ((b i)⁻¹) ^ 2) + 1) /
        ((a i * (b i)⁻¹ - 1) * (1 - c * (b i)⁻¹) ^ 2)) l (𝓝 (-1)) := by
      simpa [Pi.div_def] using h
    refine h'.congr' ?_
    filter_upwards [hb'] with i hbi
    unfold bubCoefB
    field_simp [hbi.ne']
  · simpa [Pi.div_def] using ha.neg.div hac (by simp [hc.ne'])
  · have h := (tendsto_const_nhds (x := (-1 : ℝ))).div hbc (by norm_num)
    have h' : Tendsto (fun i => -1 / (1 - c * (b i)⁻¹)) l (𝓝 (-1)) := by
      simpa [Pi.div_def] using h
    refine h'.congr' ?_
    filter_upwards [hb'] with i hbi
    unfold bubCoefB2
    field_simp [hbi.ne']

private theorem bound_crossUnit :
    ∃ C : ℝ, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ‖crossUnit a b‖ ≤ C := by
  obtain ⟨C, s, hs0, hs1, hC⟩ := crossedDom
  refine ⟨∫ y in simplexSet 4, C * ∏ k, simplexPoint y k ^ (-s), fun a b ha hb => ?_⟩
  have hint := QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow
    (m := 4) Finset.univ hs0 hs1
  refine norm_integral_le_of_norm_le (hint.const_mul C) ?_
  filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos (by norm_num : 0 < 4)]
    with y hy
  rw [Real.norm_eq_abs]
  exact hC a b ha hb _ hy (sum_simplexPoint y)

private theorem tendsto_mul_zero_of_norm_bound {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (hf : Tendsto f l (𝓝 0)) {C : ℝ} (hg : ∀ᶠ i in l, ‖g i‖ ≤ C) :
    Tendsto (fun i => f i * g i) l (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (by simpa using hf.norm.mul_const C)
  filter_upwards [hg] with i hi
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)

/-- At fixed positive spectral mass, the exact partial fractions differ from
the single spectral-mass unit by a term tending to zero. The spectator mass can
vary arbitrarily in the nonnegative half-line. -/
theorem tendsto_crossPF_sub_crossUnit {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μ a b : ι → ℝ} {c : ℝ} (hc : 0 < c)
    (hμ : ∀ᶠ i in l, 0 ≤ μ i) (ha' : ∀ᶠ i in l, 0 < a i)
    (ha : Tendsto a l (𝓝 0)) (hb : Tendsto b l atTop) :
    Tendsto (fun i => crossPF (μ i) (a i) (b i) c - crossUnit (μ i) c) l (𝓝 0) := by
  obtain ⟨hC, hA, hB, hA2, hB2⟩ := tendsto_bubCoefs hc ha hb
  obtain ⟨D, hD⟩ := bound_crossUnit
  obtain ⟨E, hE⟩ := exists_bound_mul_deriv_crossUnit_right
  have hcuC : ∀ᶠ i in l, ‖crossUnit (μ i) c‖ ≤ D := hμ.mono fun i hi => hD _ _ hi hc.le
  have hcuA : ∀ᶠ i in l, ‖crossUnit (μ i) (a i)‖ ≤ D :=
    (hμ.and ha').mono fun i hi => hD _ _ hi.1 hi.2.le
  have hdA : ∀ᶠ i in l, ‖a i * deriv (crossUnit (μ i)) (a i)‖ ≤ E :=
    (hμ.and ha').mono fun i hi => hE _ _ hi.1 hi.2
  have h₁ := tendsto_mul_zero_of_norm_bound (by simpa using hC.sub_const 1) hcuC
  have h₂ := tendsto_mul_zero_of_norm_bound hA hcuA
  have h₃ := hB.mul (tendsto_crossUnit_atTop_right hμ hb)
  have h₄ := tendsto_mul_zero_of_norm_bound hA2 hdA
  have h₅ := hB2.mul (tendsto_mul_deriv_crossUnit_right hμ hb)
  have h := (((h₁.add h₂).add h₃).sub h₄).sub h₅
  simp only [mul_zero, add_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [ha', hb.eventually_gt_atTop 0] with i hai hbi
  have eA : -a i / (a i - c) * a i = bubCoefA2 (a i) c := by
    unfold bubCoefA2
    ring
  have eB : bubCoefB2 (b i) c / b i * b i = bubCoefB2 (b i) c :=
    div_mul_cancel₀ _ hbi.ne'
  simp only [crossPF, ← mul_assoc, eA, eB]
  ring

/-- The difference between the exact crossed partial fractions and the
regulator plan vanishes at fixed positive spectral mass. -/
theorem tendsto_xExact_sub_xReg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun p : ℝ × ℝ => xExact c p.1 p.2 - xReg c p.1 p.2)
      (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  have hf : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[>] 0 ×ˢ atTop) (𝓝[>] 0) := tendsto_fst
  have ha : Tendsto (fun p : ℝ × ℝ => p.1 ^ 2) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_pow 2).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact h.comp hf
  have hb : Tendsto (fun p : ℝ × ℝ => p.2 ^ 2) (𝓝[>] 0 ×ˢ atTop) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_snd
  have ha' : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, 0 < p.1 ^ 2 :=
    (hf.eventually self_mem_nhdsWithin).mono fun p hp => pow_pos hp 2
  have h₁ := tendsto_crossPF_sub_crossUnit (μ := fun p : ℝ × ℝ => p.1 ^ 2) hc
    (Eventually.of_forall fun _ => sq_nonneg _) ha' ha hb
  have h₂ := tendsto_crossPF_sub_crossUnit (μ := fun p : ℝ × ℝ => p.2 ^ 2) hc
    (Eventually.of_forall fun _ => sq_nonneg _) ha' ha hb
  have h := (h₁.sub h₂).const_mul 2
  simp only [sub_zero, mul_zero] at h
  refine h.congr fun p => ?_
  rw [xExact, xReg, crossUnit_mirror c (p.1 ^ 2), crossUnit_mirror c (p.2 ^ 2)]
  ring

/-- The crossed partial fractions tend to the same fixed-spectral-mass kernel
as the Pauli–Villars expression. -/
theorem tendsto_xExact {c : ℝ} (hc : 0 < c) :
    Tendsto (fun p : ℝ × ℝ => xExact c p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (crossUnit 0 c + crossUnit c 0)) := by
  have h := (tendsto_xExact_sub_xReg hc).add (tendsto_xReg hc.le)
  rw [zero_add] at h
  exact h.congr fun p => sub_add_cancel _ _

end QED.ChainProof.SetCK

end
