/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutSDom
public import QED.ChainProof.SetCKCrossTFub
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the Fubini swap for the self-energy part

Helper level (no frozen statement). On the square `(Y, x) ∈ (0, 1)²` times the outer node
`X ∈ (0, 1)` the kernel of the self-energy part of G4 is
`1{x < X} W(Y, x, Q(X) - Q(x)) · Q'(X)/(Q(X) + t)²` (`scOutSKerT`), `W = 2T + A` the weight
`scOutSW` of `SetCKScOutSDom`. Each `(Y, x)`-section is, by the node change of variables
(`scOutS_section`), the `(u + v)⁻²`-integral `∫₀^∞ W(Y, x, v)/(Q(x) + t + v)² dv`. The bound
`scOutSW_abs_integral_le` and the integrability of `scOutSDom` on the square make the kernel
integrable on the product (`integrable_scOutSKerT`), and one Fubini swap gives
(**`integral_scOutSKerT`**)

`∫_{(0,1)²} ∫₀^∞ W(Y, x, v)/(Q(x) + t + v)² dv d(Y, x) = ∫₀¹ H_k(X) Q'(X)/(Q(X) + t)² dX`,

with `H_k(X) = ∫_{(0,1)²} 1{x < X} W(Y, x, Q(X) - Q(x)) d(Y, x)` (`scOutSHk`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The self-energy kernel `1{x < X} W(Y, x, Q(X) - Q(x))`. -/
noncomputable def scOutSKer (Y x X : ℝ) : ℝ :=
  if x < X then scOutSW Y x (scOutVX x X) else 0

/-- The self-energy kernel with the weight `Q'(X)/(Q(X) + t)²`, on `(Y, x) × X`. -/
noncomputable def scOutSKerT (t : ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ :=
  scOutSKer q.1.1 q.1.2 q.2 * (setCKdQ q.2 / (setCKQ q.2 + t) ^ 2)

/-- **The kernel part of the G4S weight** `H_k(X)`, a double integral over the square. -/
noncomputable def scOutSHk (X : ℝ) : ℝ :=
  ∫ p, scOutSKer p.1 p.2 X ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
    (volume.restrict (Ioo (0 : ℝ) 1)))

/-- The node integral of the kernel weight at `(Y, x)`. -/
noncomputable def scOutSGW (t Y x : ℝ) : ℝ :=
  ∫ v in Ioi 0, scOutSW Y x v / (setCKQ x + t + v) ^ 2

theorem ae_mem_square_Ioo : ∀ᵐ p ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
    (volume.restrict (Ioo (0 : ℝ) 1))), p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  exact ⟨hp.1, hp.2⟩

/-- **The dominating function is integrable on the square.** -/
theorem integrable_scOutSDom (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => scOutSDom t p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have iL : Integrable (fun x => -log x) μ := integrableOn_neg_log_Ioo
  have a : Integrable (fun p : ℝ × ℝ => -log p.1) (μ.prod μ) := iL.comp_fst μ
  have b : Integrable (fun p : ℝ × ℝ => -log p.2) (μ.prod μ) := iL.comp_snd μ
  have hs := (((integrable_const (1 : ℝ)).add a).add b).const_mul (40 * (1 + 1 / t))
  refine hs.congr (Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply, scOutSDom]

theorem measurable_scOutSW : Measurable fun p : ℝ × ℝ × ℝ => scOutSW p.1 p.2.1 p.2.2 := by
  unfold scOutSW scOutTg selfK1 selfK2 scOutRho scOutSA
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop)
    (by fun_prop)

theorem measurable_scOutSKerT (t : ℝ) : Measurable (scOutSKerT t) := by
  have hQ := measurable_setCKQ
  have hv : Measurable fun q : (ℝ × ℝ) × ℝ => scOutVX q.1.2 q.2 := by
    unfold scOutVX
    exact (hQ.comp measurable_snd).sub (hQ.comp measurable_fst.snd)
  have hK : Measurable fun q : (ℝ × ℝ) × ℝ => scOutSW q.1.1 q.1.2 (scOutVX q.1.2 q.2) :=
    measurable_scOutSW.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk hv))
  have hc : Measurable fun q : (ℝ × ℝ) × ℝ => setCKdQ q.2 / (setCKQ q.2 + t) ^ 2 := by
    unfold setCKdQ
    exact (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => q.2 * (2 - q.2) / (1 - q.2) ^ 2).div
      (((hQ.comp measurable_snd).add measurable_const).pow_const 2)
  have hs : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.2 < q.2} :=
    measurableSet_lt measurable_fst.snd measurable_snd
  unfold scOutSKerT scOutSKer
  exact (Measurable.ite hs hK measurable_const).mul hc

section

variable {t : ℝ}

/-- The sections of the kernel over the square: integrable, with integral `scOutSGW`. -/
theorem scOutSKerT_section (ht : 0 < t) {p : ℝ × ℝ}
    (hp : p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun X => scOutSKerT t (p, X)) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      ∫ X in Ioo (0 : ℝ) 1, scOutSKerT t (p, X) = scOutSGW t p.1 p.2 :=
  scOutS_section hp.2 (integrableOn_scOutSW ht hp.1 hp.2)

/-- **The Fubini hypothesis for G4S**: the kernel is integrable on the square times `(0, 1)`. -/
theorem integrable_scOutSKerT (ht : 0 < t) :
    Integrable (scOutSKerT t) (((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hm := measurable_scOutSKerT t
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_mem_square_Ioo] with p hp
    exact (scOutSKerT_section ht hp).1
  refine Integrable.mono' (integrable_scOutSDom t)
    hm.norm.aestronglyMeasurable.integral_prod_right' ?_
  filter_upwards [ae_mem_square_Ioo] with p hp
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hk : IntegrableOn (fun v => |scOutSW p.1 p.2 v| / (setCKQ p.2 + t + v) ^ 2) (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_scOutSW ht hp.1 hp.2).abs
      (fun v _ => ?_) measurableSet_Ioi
    rw [abs_div, abs_sq]
  obtain ⟨-, hv⟩ := scOutS_section (t := t) hp.2 hk
  have e : ∫ X in Ioo (0 : ℝ) 1, ‖scOutSKerT t (p, X)‖ =
      ∫ X in Ioo (0 : ℝ) 1, (if p.2 < X then |scOutSW p.1 p.2 (scOutVX p.2 X)| else 0) *
        (setCKdQ X / (setCKQ X + t) ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun X hX => ?_
    rw [scOutSKerT, scOutSKer, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (crossTdQ_div_nonneg ht hX)]
    split_ifs
    · rfl
    · simp
  rw [e, hv]
  refine le_trans (le_of_eq (setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_))
    (scOutSW_abs_integral_le ht hp.1 hp.2)
  rw [abs_div, abs_sq]

/-- **The Fubini swap for G4S**: `scOutSGW` is integrable on the square and
`∫ scOutSGW = ∫₀¹ H_k(X) Q'(X)/(Q(X) + t)² dX`. -/
theorem integral_scOutSKerT (ht : 0 < t) :
    Integrable (fun p : ℝ × ℝ => scOutSGW t p.1 p.2)
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) ∧
      ∫ p, scOutSGW t p.1 p.2 ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
        ∫ X in Ioo (0 : ℝ) 1, scOutSHk X * (setCKdQ X / (setCKQ X + t) ^ 2) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have H := integrable_scOutSKerT ht
  have hGe : (fun p => ∫ X, scOutSKerT t (p, X) ∂μ) =ᵐ[μ.prod μ]
      fun p : ℝ × ℝ => scOutSGW t p.1 p.2 := by
    filter_upwards [ae_mem_square_Ioo] with p hp
    exact (scOutSKerT_section ht hp).2
  refine ⟨H.integral_prod_left.congr hGe, ?_⟩
  have hswap := integral_integral_swap (f := fun p X => scOutSKerT t (p, X)) H
  rw [← integral_congr_ae hGe, hswap]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [scOutSKerT, scOutSHk]
  exact integral_mul_const _ _

end

end QED.ChainProof.SetCK

end
