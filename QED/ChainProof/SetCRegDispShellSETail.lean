/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEExp
public import QED.ChainProof.SetCRegDispShellSEBlk
public import QED.ChainProof.SetCRegDispShellConv
public import QED.ChainProof.SetCRegBubblePF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The affine blocks of the class `V` limit as the tail of the dressed photon

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (b1c). The tail
`Tail_R(w) = ∫_w^∞ R` of the dressed photon `R = vpPhotonT m m_γ Λ T` has a closed form from its
partial fractions (`QED.ChainProof.SetCRegBubble.vpPhotonT_partialFractions`; the simple-pole
coefficients add to zero, so the logarithms pair). With it, the affine blocks of one flavour
piece of the class `V` limit (`QED.ChainProof.SetCRegDisp.seAffBlk`) are a single Feynman-parameter
integral of the tail at the self-energy argument `w = seArg m s y`:

`seAffBlk (c + b ℓ̸) m a b μ P = ∫₀¹ 2 G(y) (μ²/(a² - b²)²) Tail_{R}(seArg m s y) dy`,
`R = vpPhotonT m a b (μ²/m²)`, `G = seAffG`.

* `photonTailVP`: the closed form `-C log(w+U) - A log(w+a²) - B log(w+b²) + A₂/(w+a²) +
  B₂/(w+b²)` (`U = T m²`; `C, A, B, A₂, B₂` = `bubCoef*`);
* **`photonTail_vpPhotonT_eq`**: `Tail_R(w) = photonTailVP` whenever `w + a², w + b², w + U > 0`
  and `a², b², U` are pairwise distinct;
* **`seAffBlk_eq_tail`**: the affine blocks as one integral of the tail.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.WickModel.SelfEnergyLimit QED.OneLoop
open QED.ChainProof.SetCRegDispSE (seWt seProdLim)
open QED.ChainProof.SetCRegBubble (bubCoefC bubCoefA bubCoefB bubCoefA2 bubCoefB2
  bubCoef_simple_sum vpPhotonT_partialFractions)

/-! ### The closed form of the tail -/

/-- The closed form of the tail of the dressed photon at `w` (`U = T m²`). -/
noncomputable def photonTailVP (m mγ Λ T w : ℝ) : ℝ :=
  -bubCoefC (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) * Real.log (w + T * m ^ 2) -
    bubCoefA (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) * Real.log (w + mγ ^ 2) -
    bubCoefB (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) * Real.log (w + Λ ^ 2) +
    bubCoefA2 (mγ ^ 2) (T * m ^ 2) / (w + mγ ^ 2) +
    bubCoefB2 (Λ ^ 2) (T * m ^ 2) / (w + Λ ^ 2)

theorem tendsto_log_sub_log (a X Y : ℝ) :
    Tendsto (fun u : ℝ => Real.log (a + u + X) - Real.log (a + u + Y)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun u : ℝ => (a + u + Y)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right _ _
      (tendsto_atTop_add_const_left _ _ tendsto_id)).inv_tendsto_atTop
  have hr : Tendsto (fun u : ℝ => (a + u + X) / (a + u + Y)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add (hinv.const_mul (X - Y))
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (|a| + |Y|)] with u hu
    have : a + u + Y ≠ 0 := by
      have := neg_abs_le a; have := neg_abs_le Y; intro h; linarith
    field_simp
    ring
  have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hr
  rw [Real.log_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (|a| + |X| + |Y|)] with u hu
  have p1 : a + u + X ≠ 0 := by
    have := neg_abs_le a; have := neg_abs_le X; have := abs_nonneg Y; intro h; linarith
  have p2 : a + u + Y ≠ 0 := by
    have := neg_abs_le a; have := neg_abs_le Y; have := abs_nonneg X; intro h; linarith
  simp only [Function.comp]
  rw [Real.log_div p1 p2]

theorem tendsto_inv_add (a X : ℝ) : Tendsto (fun u : ℝ => (a + u + X)⁻¹) atTop (𝓝 0) :=
  (tendsto_atTop_add_const_right _ _
    (tendsto_atTop_add_const_left _ _ tendsto_id)).inv_tendsto_atTop

/-- **The tail of the dressed photon in closed form.** -/
theorem photonTail_vpPhotonT_eq {m mγ Λ T w : ℝ} (hab : mγ ^ 2 ≠ Λ ^ 2)
    (hac : mγ ^ 2 ≠ T * m ^ 2) (hbc : Λ ^ 2 ≠ T * m ^ 2) (ha : 0 < w + mγ ^ 2)
    (hb : 0 < w + Λ ^ 2) (hc : 0 < w + T * m ^ 2) :
    photonTail (vpPhotonT m mγ Λ T) w = photonTailVP m mγ Λ T w := by
  set C := bubCoefC (mγ ^ 2) (Λ ^ 2) (T * m ^ 2)
  set A := bubCoefA (mγ ^ 2) (Λ ^ 2) (T * m ^ 2)
  set B := bubCoefB (mγ ^ 2) (Λ ^ 2) (T * m ^ 2)
  set A₂ := bubCoefA2 (mγ ^ 2) (T * m ^ 2)
  set B₂ := bubCoefB2 (Λ ^ 2) (T * m ^ 2)
  have hsum : C + A + B = 0 := bubCoef_simple_sum hab hac hbc
  set g : ℝ → ℝ := fun u => C * Real.log (w + u + T * m ^ 2) +
    A * Real.log (w + u + mγ ^ 2) + B * Real.log (w + u + Λ ^ 2) -
    A₂ * (w + u + mγ ^ 2)⁻¹ - B₂ * (w + u + Λ ^ 2)⁻¹ with hg
  have hderiv : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (vpPhotonT m mγ Λ T (w + u)) u := by
    intro u hu
    have p1 : 0 < w + u + T * m ^ 2 := by linarith
    have p2 : 0 < w + u + mγ ^ 2 := by linarith
    have p3 : 0 < w + u + Λ ^ 2 := by linarith
    have l1 := (((hasDerivAt_id u).const_add w).add_const (T * m ^ 2)).log p1.ne'
    have l2 := (((hasDerivAt_id u).const_add w).add_const (mγ ^ 2)).log p2.ne'
    have l3 := (((hasDerivAt_id u).const_add w).add_const (Λ ^ 2)).log p3.ne'
    have i2 := (((hasDerivAt_id u).const_add w).add_const (mγ ^ 2)).inv p2.ne'
    have i3 := (((hasDerivAt_id u).const_add w).add_const (Λ ^ 2)).inv p3.ne'
    have h := ((((l1.const_mul C).add (l2.const_mul A)).add (l3.const_mul B)).sub
      (i2.const_mul A₂)).sub (i3.const_mul B₂)
    refine h.congr_deriv ?_
    rw [vpPhotonT_partialFractions hab hac hbc p2.ne' p3.ne' p1.ne']
    simp only [id]
    field_simp
    ring
  have hpos : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ vpPhotonT m mγ Λ T (w + u) := by
    intro u hu
    have hu' : 0 < u := hu
    unfold vpPhotonT
    have : 0 < w + u + T * m ^ 2 := by linarith
    positivity
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h1 := (tendsto_log_sub_log w (T * m ^ 2) (Λ ^ 2)).const_mul C
    have h2 := (tendsto_log_sub_log w (mγ ^ 2) (Λ ^ 2)).const_mul A
    have h3 := (tendsto_inv_add w (mγ ^ 2)).const_mul A₂
    have h4 := (tendsto_inv_add w (Λ ^ 2)).const_mul B₂
    have h := ((h1.add h2).sub h3).sub h4
    simp only [mul_zero, add_zero, sub_zero] at h
    refine h.congr' (Eventually.of_forall fun u => ?_)
    have e : B = -C - A := by linear_combination hsum
    simp only [hg, e]
    ring
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hderiv 0 le_rfl).continuousAt.continuousWithinAt) (fun u hu => hderiv u (le_of_lt hu))
    hpos hlim
  unfold photonTail
  rw [h]
  simp only [hg, add_zero, photonTailVP]
  ring

/-! ### The affine blocks -/

theorem continuous_seAffG (c b : ℂ) (α β : Fin 4) (P : Fin 4 → ℝ) :
    Continuous fun y : ℝ => seAffG c b α β P y := by
  unfold seAffG
  have h : Continuous fun y : ℝ => seAff c b α β (-(y • P)) :=
    (continuous_seAff c b α β).comp (by fun_prop)
  fun_prop

theorem continuous_selfEnergyFeynmanMass_y (m M s : ℝ) :
    Continuous fun y : ℝ => selfEnergyFeynmanMass m M s y := by
  unfold selfEnergyFeynmanMass; fun_prop

section Affine

variable {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {P : Fin 4 → ℝ}
  (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)

include hM₀ hc₀ hP in
theorem selfEnergyFeynmanMass_pos_of_le {M y : ℝ} (hM : M₀ ≤ M) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 < selfEnergyFeynmanMass m M (Minkowski.dot P P) y :=
  hc₀.trans_le ((hP y hy).trans (SetCRegDispSE.selfEnergyFeynmanMass_mono hM₀ hM hy))

include hM₀ hc₀ hP in
theorem integrableOn_affLog {μ ν : ℝ} (hμ : M₀ ≤ μ) (hν : M₀ ≤ ν) (c b : ℂ) (α β : Fin 4) :
    IntegrableOn (fun y => 2 * seAffG c b α β P y *
      (((Real.log (selfEnergyFeynmanMass m μ (Minkowski.dot P P) y) -
        Real.log (selfEnergyFeynmanMass m ν (Minkowski.dot P P) y)) / (μ ^ 2 - ν ^ 2) : ℝ) :
          ℂ)) (Ioc (0 : ℝ) 1) := by
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  refine ((continuous_const.mul (continuous_seAffG c b α β P)).continuousOn).mul
    (Complex.continuous_ofReal.comp_continuousOn ?_)
  refine ContinuousOn.div_const (ContinuousOn.sub ?_ ?_) _
  · exact ((continuous_selfEnergyFeynmanMass_y _ _ _).continuousOn).log fun y hy =>
      (selfEnergyFeynmanMass_pos_of_le hM₀ hc₀ hP hμ hy).ne'
  · exact ((continuous_selfEnergyFeynmanMass_y _ _ _).continuousOn).log fun y hy =>
      (selfEnergyFeynmanMass_pos_of_le hM₀ hc₀ hP hν hy).ne'

include hM₀ hc₀ hP in
theorem integrableOn_affInv {μ : ℝ} (hμ : M₀ ≤ μ) (c b : ℂ) (α β : Fin 4) :
    IntegrableOn (fun y => seWt 1 y * (seAffG c b α β P y *
      (((selfEnergyFeynmanMass m μ (Minkowski.dot P P) y)⁻¹ : ℝ) : ℂ))) (Ioc (0 : ℝ) 1) := by
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  have hw : Continuous fun y : ℝ => seWt 1 y := by unfold seWt; fun_prop
  refine hw.continuousOn.mul ((continuous_seAffG c b α β P).continuousOn.mul
    (Complex.continuous_ofReal.comp_continuousOn ?_))
  exact ((continuous_selfEnergyFeynmanMass_y _ _ _).continuousOn).inv₀ fun y hy =>
    (selfEnergyFeynmanMass_pos_of_le hM₀ hc₀ hP hμ hy).ne'

include hM₀ hc₀ hP in
/-- **The affine blocks of a flavour piece as one integral of the tail of the dressed photon**:
`seAffBlk (c + b ℓ̸) m a b μ P = ∫₀¹ 2 G(y) (μ²/(a² - b²)²) Tail_R(seArg m s y) dy` with
`R = vpPhotonT m a b (μ²/m²)`. -/
theorem seAffBlk_eq_tail (hm : m ≠ 0) {a b μ : ℝ} (ha : M₀ ≤ a) (hb : M₀ ≤ b) (hμ : M₀ ≤ μ)
    (hAB : a ^ 2 ≠ b ^ 2) (hAU : a ^ 2 ≠ μ ^ 2) (hBU : b ^ 2 ≠ μ ^ 2) (c cb : ℂ)
    (α β : Fin 4) :
    seAffBlk (seAff c cb α β) m a b μ P = ∫ y in Ioc (0 : ℝ) 1, 2 * seAffG c cb α β P y *
      ((μ ^ 2 / (a ^ 2 - b ^ 2) ^ 2 *
        photonTail (vpPhotonT m a b (μ ^ 2 / m ^ 2)) (seArg m (Minkowski.dot P P) y) : ℝ) :
          ℂ) := by
  set s := Minkowski.dot P P with hs
  unfold seAffBlk
  rw [seProdLim_seAff_double hM₀ hc₀ hP ha, seProdLim_seAff_double hM₀ hc₀ hP hb,
    seProdLim_seAff_two hM₀ hc₀ hP ha hb hAB, seProdLim_seAff_two hM₀ hc₀ hP ha hμ hAU,
    seProdLim_seAff_two hM₀ hc₀ hP hb hμ hBU]
  have i1 := integrableOn_affInv hM₀ hc₀ hP ha c cb α β
  have i2 := integrableOn_affInv hM₀ hc₀ hP hb c cb α β
  have i3 := integrableOn_affLog hM₀ hc₀ hP ha hb c cb α β
  have i4 := integrableOn_affLog hM₀ hc₀ hP ha hμ c cb α β
  have i5 := integrableOn_affLog hM₀ hc₀ hP hb hμ c cb α β
  set k1 : ℂ := -((a : ℂ) ^ 4 * μ ^ 2 / ((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (a ^ 2 - μ ^ 2 : ℂ)))
  set k2 : ℂ := (b : ℂ) ^ 4 * μ ^ 2 / ((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (b ^ 2 - μ ^ 2 : ℂ))
  set k3 : ℂ := 2 * (a : ℂ) ^ 2 * b ^ 2 / (a ^ 2 - b ^ 2 : ℂ) ^ 2
  set k4 : ℂ := (a : ℂ) ^ 4 * (2 * a ^ 2 * b ^ 2 + a ^ 2 * μ ^ 2 - 3 * b ^ 2 * μ ^ 2) /
    ((a ^ 2 - b ^ 2 : ℂ) ^ 3 * (a ^ 2 - μ ^ 2 : ℂ))
  set k5 : ℂ := (b : ℂ) ^ 4 * (2 * a ^ 2 * b ^ 2 - 3 * a ^ 2 * μ ^ 2 + b ^ 2 * μ ^ 2) /
    ((a ^ 2 - b ^ 2 : ℂ) ^ 3 * (b ^ 2 - μ ^ 2 : ℂ))
  have j1 := i1.const_mul k1
  have j2 := i2.const_mul k2
  have j3 := i3.const_mul k3
  have j4 := i4.const_mul k4
  have j5 := i5.const_mul k5
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_const_mul]
  have j12 := j1.sub j2
  simp only [Pi.sub_def] at j12
  have j123 := j12.sub j3
  simp only [Pi.sub_def] at j123
  have j1234 := j123.add j4
  simp only [Pi.add_def] at j1234
  rw [← integral_sub j1 j2, ← integral_sub j12 j3, ← integral_add j123 j4,
    ← integral_sub j1234 j5, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  have hyI : y ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hy
  set w := seArg m s y with hw
  have hD : ∀ M : ℝ, M₀ ≤ M → selfEnergyFeynmanMass m M s y = (1 - y) * (w + M ^ 2) ∧
      0 < w + M ^ 2 := by
    intro M hM
    have e := selfEnergyFeynmanMass_eq_seArg m M s hy.2.ne
    have p := selfEnergyFeynmanMass_pos_of_le hM₀ hc₀ hP hM hyI
    rw [e] at p
    exact ⟨e, pos_of_mul_pos_right p hy1.le⟩
  obtain ⟨ea, pa⟩ := hD a ha
  obtain ⟨eb, pb⟩ := hD b hb
  obtain ⟨eu, pu⟩ := hD μ hμ
  have hT : μ ^ 2 / m ^ 2 * m ^ 2 = μ ^ 2 := by field_simp
  have htail := photonTail_vpPhotonT_eq (m := m) (mγ := a) (Λ := b) (T := μ ^ 2 / m ^ 2) (w := w)
    hAB (by rw [hT]; exact hAU) (by rw [hT]; exact hBU) pa pb (by rw [hT]; exact pu)
  set Da := selfEnergyFeynmanMass m a s y
  set Db := selfEnergyFeynmanMass m b s y
  set Du := selfEnergyFeynmanMass m μ s y
  have hreal :
      -(a ^ 4 * μ ^ 2 / ((a ^ 2 - b ^ 2) ^ 2 * (a ^ 2 - μ ^ 2))) * ((1 - y) * Da⁻¹) -
        b ^ 4 * μ ^ 2 / ((a ^ 2 - b ^ 2) ^ 2 * (b ^ 2 - μ ^ 2)) * ((1 - y) * Db⁻¹) -
        2 * a ^ 2 * b ^ 2 / (a ^ 2 - b ^ 2) ^ 2 * ((Real.log Da - Real.log Db) / (a ^ 2 - b ^ 2)) +
        a ^ 4 * (2 * a ^ 2 * b ^ 2 + a ^ 2 * μ ^ 2 - 3 * b ^ 2 * μ ^ 2) /
            ((a ^ 2 - b ^ 2) ^ 3 * (a ^ 2 - μ ^ 2)) *
          ((Real.log Da - Real.log Du) / (a ^ 2 - μ ^ 2)) -
        b ^ 4 * (2 * a ^ 2 * b ^ 2 - 3 * a ^ 2 * μ ^ 2 + b ^ 2 * μ ^ 2) /
            ((a ^ 2 - b ^ 2) ^ 3 * (b ^ 2 - μ ^ 2)) *
          ((Real.log Db - Real.log Du) / (b ^ 2 - μ ^ 2)) =
      μ ^ 2 / (a ^ 2 - b ^ 2) ^ 2 * photonTail (vpPhotonT m a b (μ ^ 2 / m ^ 2)) w := by
    rw [htail, ea, eb, eu, Real.log_mul hy1.ne' pa.ne', Real.log_mul hy1.ne' pb.ne',
      Real.log_mul hy1.ne' pu.ne']
    unfold photonTailVP
    simp only [hT, bubCoefC, bubCoefA, bubCoefB, bubCoefA2, bubCoefB2]
    have r1 : a ^ 2 - b ^ 2 ≠ 0 := sub_ne_zero.2 hAB
    have r2 : a ^ 2 - μ ^ 2 ≠ 0 := sub_ne_zero.2 hAU
    have r3 : b ^ 2 - μ ^ 2 ≠ 0 := sub_ne_zero.2 hBU
    have r4 : b ^ 2 - a ^ 2 ≠ 0 := fun h => r1 (by linear_combination -h)
    have r5 : μ ^ 2 - a ^ 2 ≠ 0 := fun h => r2 (by linear_combination -h)
    have r6 : μ ^ 2 - b ^ 2 ≠ 0 := fun h => r3 (by linear_combination -h)
    field_simp
    ring
  rw [← hreal]
  simp only [seWt]
  push_cast
  ring

end Affine

end QED.ChainProof.SetCRegDisp

end
