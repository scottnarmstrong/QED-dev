/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKPairS

/-!
# Set (c), Stage K: the L pair as a Stieltjes transform (Fubini on the node triangle)

Helper level (no frozen statement). For `t > 0` the L pair is a single node integral of the pair
integrand, `lPair t = ∫₀¹ F(x, Q(x) + t) dx` (`lPair_eq_integral_pairF`, given the integrability of
the pair kernel). Each `F(x, Q(x) + t)` is `e₁(x)/(Q(x) + t)` plus the integral over the outer
node `X ∈ (x, 1)` of the pair kernel (`integral_pairKer`); exchanging the two node integrals on
the triangle `0 < x < X < 1` and doing the inner node integral in closed form
(`integral_dispSig_X`, `pairGX_add_pairWB_sub`) leaves `∫₀¹ (e₁ + Q' S)/(Q + t) dX`, which is the
Stieltjes transform of `ρ_L` (`rhoL_mul_setCKQ`).

The one analytic input not proved here is the absolute integrability of the pair kernel on the
triangle (`PairKerIntegrable`), the hypothesis of Fubini's theorem.
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set Filter Topology MeasureTheory QED.TwoLoop.UnitLLink

/-- The pair kernel on the node triangle `0 < x < X < 1`, extended by zero. -/
noncomputable def pairKerT (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 then pairKer t p.1 p.2 else 0

/-- **The Fubini hypothesis**: the pair kernel is absolutely integrable on the node triangle. -/
def PairKerIntegrable (t : ℝ) : Prop :=
  Integrable (pairKerT t) ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))

section

variable {t x X : ℝ}

theorem pairKerT_x_eq (x : ℝ) :
    (fun X => pairKerT t (x, X)) = (Ioi x).indicator (pairKer t x) := by
  funext X
  simp only [pairKerT, indicator, mem_Ioi]

theorem pairKerT_X_eq (X : ℝ) :
    (fun x => pairKerT t (x, X)) = (Iio X).indicator (fun x => pairKer t x X) := by
  funext x
  simp only [pairKerT, indicator, mem_Iio]

theorem restrict_Ioi_Ioo (hx : x ∈ Ioo (0 : ℝ) 1) :
    (volume.restrict (Ioo (0 : ℝ) 1)).restrict (Ioi x) = volume.restrict (Ioo x 1) := by
  rw [Measure.restrict_restrict measurableSet_Ioi]
  congr 1
  ext y
  simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, hx.1.trans h1, h2⟩

theorem restrict_Iio_Ioo (hX : X ∈ Ioo (0 : ℝ) 1) :
    (volume.restrict (Ioo (0 : ℝ) 1)).restrict (Iio X) = volume.restrict (Ioo 0 X) := by
  rw [Measure.restrict_restrict measurableSet_Iio]
  congr 1
  ext y
  simp only [mem_inter_iff, mem_Iio, mem_Ioo]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hX.2⟩

/-- An `x`-section of the triangle kernel: the per-node dispersion integral. -/
theorem integral_pairKerT_x (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ≠ t)
    (hint : Integrable (fun X => pairKerT t (x, X)) (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∫ X, pairKerT t (x, X) ∂(volume.restrict (Ioo (0 : ℝ) 1)) =
      pairF x (setCKQ x + t) - dispE1 x / (setCKQ x + t) := by
  rw [pairKerT_x_eq] at hint ⊢
  rw [integral_indicator measurableSet_Ioi, restrict_Ioi_Ioo hx]
  rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn, restrict_Ioi_Ioo hx] at hint
  have hii : IntervalIntegrable (pairKer t x) volume x 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.2.le).2 hint
  have hQ : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hup : x - (setCKQ x + t) + (setCKQ x + t) * x ≠ 0 := by
    intro h
    have e := setCKQ_add_self hx.2
    have h1 : 1 - x ≠ 0 := by linarith [hx.2]
    apply hxt
    have : (setCKQ x + t) * (1 - x) = x := by linarith
    have e2 : (setCKQ x + x) * (1 - x) = x := by rw [e]; field_simp
    have : (t - x) * (1 - x) = 0 := by linarith
    rcases mul_eq_zero.1 this with h2 | h2
    · linarith
    · exact absurd h2 h1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.2.le,
    integral_pairKer hx ht hxt hii, pairF_eq hx (by positivity) hup]

/-- An `X`-section of the triangle kernel: the inner node integral. -/
theorem integral_pairKerT_X (ht : 0 < t) (hX : X ∈ Ioo (0 : ℝ) 1)
    (hint : Integrable (fun x => pairKerT t (x, X)) (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∫ x, pairKerT t (x, X) ∂(volume.restrict (Ioo (0 : ℝ) 1)) =
      pairS X * (setCKdQ X / (setCKQ X + t)) := by
  rw [pairKerT_X_eq] at hint ⊢
  rw [integral_indicator measurableSet_Iio, restrict_Iio_Ioo hX]
  rw [integrable_indicator_iff measurableSet_Iio, IntegrableOn, restrict_Iio_Ioo hX] at hint
  have hQ : 0 ≤ setCKQ X := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩
  have hc : setCKdQ X / (setCKQ X + t) ≠ 0 := by
    have h1 : 0 < 1 - X := by linarith [hX.2]
    have : 0 < setCKdQ X := by
      unfold setCKdQ; have : 0 < 2 - X := by linarith [hX.2]
      have := hX.1; positivity
    exact (div_pos this (by linarith)).ne'
  simp only [pairKer] at hint ⊢
  have hs : IntegrableOn (fun x => dispSig x (setCKQ X - setCKQ x)) (Ioo 0 X) := by
    have := hint.mul_const (setCKdQ X / (setCKQ X + t))⁻¹
    have e : (fun x => dispSig x (setCKQ X - setCKQ x) * (setCKdQ X / (setCKQ X + t)) *
        (setCKdQ X / (setCKQ X + t))⁻¹) = fun x => dispSig x (setCKQ X - setCKQ x) := by
      funext x; rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
    rw [e] at this
    exact this
  have hii : IntervalIntegrable (fun x => dispSig x (setCKQ X - setCKQ x)) volume 0 X :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hX.1.le).2 hs
  rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hX.1.le, integral_dispSig_X hX hii,
    pairGX_add_pairWB_sub hX]


theorem pos_denom (ht : 0 < t) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < x ^ 2 + (1 - x) * t := by
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h; simpa using ht
  · have : 0 ≤ (1 - x) * t := mul_nonneg (by linarith [hx.2]) ht.le
    have : 0 < x ^ 2 := by positivity
    linarith

theorem integrableOn_dispE1 (ht : 0 < t) :
    IntegrableOn (fun x => dispE1 x / (setCKQ x + t)) (Ioo 0 1) := by
  have hc : ContinuousOn (fun x : ℝ => (-(x ^ 2 * negMulLog (1 - x)) +
      x ^ 2 * (3 * x ^ 2 - 18 * x + 14) / 4) / (x ^ 2 + (1 - x) * t)) (Icc 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (pos_denom ht hx).ne'
  refine (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun (fun x hx => ?_)
    measurableSet_Ioo
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hd := (pos_denom ht (Ioo_subset_Icc_self hx)).ne'
  have hu : setCKQ x + t ≠ 0 := by
    have := setCKQ_nonneg (Ioo_subset_Icc_self hx); linarith
  have hx1 : x - 1 ≠ 0 := by linarith [hx.2]
  unfold dispE1 negMulLog
  rw [show setCKQ x + t = (x ^ 2 + (1 - x) * t) / (1 - x) by unfold setCKQ; field_simp]
  field_simp
  ring

theorem integrableOn_oneLoop (ht : 0 < t) :
    IntegrableOn (fun x => (1 - x) * (setCKQ x / (setCKQ x + t))) (Ioo 0 1) := by
  have hc : ContinuousOn (fun x : ℝ => (1 - x) * (x ^ 2 / (x ^ 2 + (1 - x) * t))) (Icc 0 1) :=
    continuousOn_const.sub continuousOn_id |>.mul
      (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (pos_denom ht hx).ne')
  refine (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun (fun x hx => ?_)
    measurableSet_Ioo
  rw [setCKQ_div_eq hx.2]

theorem integrableOn_phiOut (ht : 0 < t) :
    IntegrableOn (fun x => phiOut x (hOut t x)) (Ioo 0 1) := by
  have h := (integrable_ladderGm_zero ht).integral_prod_right
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (Measure.ae_ne volume t)] with x hx hxt
  simp only [Function.uncurry_apply_pair]
  rw [setIntegral_Ioo_eq_intervalIntegral, integral_ladderGm_zero_Y ht hx hxt]

/-- The node integral of the pair integrand, by Fubini on the node triangle. -/
theorem integral_pairF (ht : 0 < t) (H : PairKerIntegrable t) :
    ∫ x in Ioo (0 : ℝ) 1, pairF x (setCKQ x + t) =
      ∫ X in Ioo (0 : ℝ) 1, rhoL X * (setCKQ X / (setCKQ X + t)) := by
  have hg := H.integral_prod_left
  have hh := H.integral_prod_right
  have hE := integrableOn_dispE1 ht
  have e1 : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), pairF x (setCKQ x + t) =
      dispE1 x / (setCKQ x + t) + ∫ X, pairKerT t (x, X) ∂(volume.restrict (Ioo (0 : ℝ) 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (Measure.ae_ne volume t), H.prod_right_ae] with x hx hxt hs
    rw [integral_pairKerT_x ht hx hxt hs]
    ring
  have e2 : ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ x, pairKerT t (x, X) ∂(volume.restrict (Ioo (0 : ℝ) 1)) =
        pairS X * (setCKdQ X / (setCKQ X + t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, H.prod_left_ae] with X hX hs
    exact integral_pairKerT_X ht hX hs
  have hswap := integral_integral_swap (f := fun x X => pairKerT t (x, X)) H
  rw [integral_congr_ae e1, integral_add hE hg, hswap, integral_congr_ae e2,
    ← integral_add hE (hh.congr e2)]
  refine setIntegral_congr_fun measurableSet_Ioo fun X hX => ?_
  have h := rhoL_mul_setCKQ hX
  have hu : setCKQ X + t ≠ 0 := by
    have := setCKQ_nonneg (Ioo_subset_Icc_self hX); linarith
  field_simp
  linear_combination -h

/-- **The L pair as a single node integral** of the pair integrand. -/
theorem lPair_eq_integral_pairF (ht : 0 < t) (H : PairKerIntegrable t) :
    lPair t = ∫ x in Ioo (0 : ℝ) 1, pairF x (setCKQ x + t) := by
  have hB := integrableOn_phiOut ht
  have hC := integrableOn_oneLoop ht
  have hF : IntegrableOn (fun x => pairF x (setCKQ x + t)) (Ioo 0 1) := by
    have hg := H.integral_prod_left
    refine ((integrableOn_dispE1 ht).add hg).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (Measure.ae_ne volume t), H.prod_right_ae] with x hx hxt hs
    simp only [Pi.add_apply]
    rw [integral_pairKerT_x ht hx hxt hs]
    ring
  have hpt : ∀ x ∈ Ioo (0 : ℝ) 1, pairF x (setCKQ x + t) =
      psiIn x (x * (1 - x)) (massIn t x) + phiOut x (hOut t x) -
        3 / 2 * ((1 - x) * (setCKQ x / (setCKQ x + t))) := by
    intro x hx
    have hu : setCKQ x + t ≠ 0 := by
      have := setCKQ_nonneg (Ioo_subset_Icc_self hx); linarith
    have h1 : 1 - x ≠ 0 := by linarith [hx.2]
    rw [massIn, ladderInnerMass_sqrt_eq ht.le hx.2, hOut, ladderInnerMass_sqrt_div_eq ht.le hx,
      pairF]
    congr 1
    unfold setCKQ
    field_simp
  have hA : IntegrableOn (fun x => psiIn x (x * (1 - x)) (massIn t x)) (Ioo 0 1) := by
    refine ((hF.sub hB).add (hC.const_mul (3 / 2))).congr_fun (fun x hx => ?_) measurableSet_Ioo
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hpt x hx]
    ring
  have hAB : IntegrableOn (fun x => psiIn x (x * (1 - x)) (massIn t x) + phiOut x (hOut t x))
      (Ioo 0 1) := hA.add hB
  rw [lPair, lInner_eq ht, lOuter_eq ht, oneLoopF2_sqrt_eq_setCKStieltjes ht, setCKStieltjes,
    ← setIntegral_Ioo_eq_intervalIntegral, ← setIntegral_Ioo_eq_intervalIntegral,
    ← setIntegral_Ioo_eq_intervalIntegral, ← integral_const_mul, add_sub_assoc',
    ← integral_add hA hB, ← integral_sub hAB (hC.const_mul (3 / 2))]
  exact setIntegral_congr_fun measurableSet_Ioo fun x hx => (hpt x hx).symm

/-- **The pilot (S_L) for `ρ_L`**, conditional on the Fubini hypothesis. -/
theorem isLPairDensity_rhoL_of_pairKerIntegrable (H : ∀ t : ℝ, 0 < t → PairKerIntegrable t) :
    IsLPairDensity rhoL := fun t ht => by
  rw [lPair_eq_integral_pairF ht (H t ht), integral_pairF ht (H t ht),
    setIntegral_Ioo_eq_intervalIntegral]
  rfl

end

end QED.ChainProof.SetCK
