/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI4P1ST
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Set (e), master I₄: the region swap `(l, t) ↦ (t, l)` and the outer `(a, b)` integral

At fixed `(a, b, c)` with `a + b + c = 1`, the substitution `n ↦ t` of
`QED.ThreeLoopE.SetEMastersI4P1ST` maps the quadrant `l, n > 0` onto the region
`i4SR = {(l, t) | 0 < l, i4STmin l < t < l}`. Integrability transfers fiber by fiber (the
substitution preserves the integral of the absolute value), and Fubini on the region gives

  `∫_{l, n > 0} i4SMVal U₁ U₂ = ∫_t ∫_{l ∈ i4SLSec t} i4STDens l t = i4SOmega a b c`

(`QED.ThreeLoopE.i4ST_swap`), where `i4SLSec t = {l | 0 < l, i4STmin l < t < l}`. Together with
`QED.ThreeLoopE.i4P1_SM` and Fubini in `(a, b)`, `P'(0)` is the integral of `i4SOmega` over the
triangle `0 < a, 0 < b, a + b < 1` (`QED.ThreeLoopE.i4P1_Omega`).

## Main definitions

* `QED.ThreeLoopE.i4SR`, `QED.ThreeLoopE.i4SLSec`, `QED.ThreeLoopE.i4SG`,
  `QED.ThreeLoopE.i4SOmega`, `QED.ThreeLoopE.i4STri`.

## Main results

* `QED.ThreeLoopE.i4ST_swap`.
* `QED.ThreeLoopE.i4P1_Omega`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace QED.ThreeLoopE

/-- The image region `{(l, t) | 0 < l, i4STmin l < t < l}`. -/
def i4SR (a b c : ℝ) : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ i4STmin a b c p.1 < p.2 ∧ p.2 < p.1}

/-- The `l`-section of `i4SR` at fixed `t`. -/
def i4SLSec (a b c t : ℝ) : Set ℝ := {l | 0 < l ∧ i4STmin a b c l < t ∧ t < l}

/-- The `m`-integrated density as a function of `(l, n)`. -/
noncomputable def i4SG (a b c : ℝ) (p : ℝ × ℝ) : ℝ :=
  i4SMVal (i4SU1 a b c p.1 p.2) (i4SU2 a b c p.1 p.2)

/-- The `(l, n)`-integral in the variables `(t, l)`. -/
noncomputable def i4SOmega (a b c : ℝ) : ℝ := ∫ t, ∫ l in i4SLSec a b c t, i4STDens a b c l t

/-- The triangle `0 < a, 0 < b, a + b < 1`. -/
def i4STri : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}

theorem measurableSet_i4SR (a b c : ℝ) : MeasurableSet (i4SR a b c) := by
  unfold i4SR i4STmin i4SN i4SD
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop)))

theorem measurableSet_i4SLSec (a b c t : ℝ) : MeasurableSet (i4SLSec a b c t) := by
  unfold i4SLSec i4STmin i4SN i4SD
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) measurable_const).inter
      (measurableSet_lt measurable_const (by fun_prop)))

theorem measurableSet_i4STri : MeasurableSet i4STri := by
  unfold i4STri
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const (by fun_prop)).inter
    ((measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const))

theorem measurable_i4STDens (a b c : ℝ) :
    Measurable fun p : ℝ × ℝ => i4STDens a b c p.1 p.2 := by
  unfold i4STDens i4SN
  fun_prop

/-- **The region swap at fixed `(a, b, c)`.** -/
theorem i4ST_swap {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1)
    (hG : IntegrableOn (i4SG a b c) (Ioi 0 ×ˢ Ioi 0)) :
    (∀ᵐ t, IntegrableOn (fun l => i4STDens a b c l t) (i4SLSec a b c t)) ∧
      Integrable (fun t => ∫ l in i4SLSec a b c t, i4STDens a b c l t) ∧
      ∫ p in Ioi 0 ×ˢ Ioi 0, i4SG a b c p = i4SOmega a b c := by
  set Gt := (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator (i4SG a b c) with hGt_def
  set Ft := (i4SR a b c).indicator (fun p : ℝ × ℝ => i4STDens a b c p.1 p.2) with hFt_def
  have hmQ : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hGt : Integrable Gt (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact (integrable_indicator_iff hmQ).2 hG
  have hsecG : ∀ l, 0 < l → ∀ n, Gt (l, n) = (Ioi 0).indicator (fun n => i4SG a b c (l, n)) n :=
    fun l hl n => by
      by_cases hn : 0 < n
      · simp [hGt_def, indicator, hl, hn]
      · simp [hGt_def, hn]
  have hsecG0 : ∀ l, ¬ 0 < l → ∀ n, Gt (l, n) = 0 := fun l hl n => by
    simp [hGt_def, hl]
  have hsecF : ∀ l, 0 < l → ∀ t, Ft (l, t) =
      (Ioo (i4STmin a b c l) l).indicator (fun t => i4STDens a b c l t) t := fun l hl t => by
    simp only [hFt_def, indicator, i4SR, mem_ofPred_eq, mem_Ioo, hl, true_and]
  have hsecF0 : ∀ l, ¬ 0 < l → ∀ t, Ft (l, t) = 0 := fun l hl t => by
    simp [hFt_def, i4SR, hl]
  have hcolF : ∀ l t, Ft (l, t) =
      (i4SLSec a b c t).indicator (fun l => i4STDens a b c l t) l := fun l t => by
    by_cases h : 0 < l ∧ i4STmin a b c l < t ∧ t < l <;>
      simp [hFt_def, indicator, i4SR, i4SLSec, h]
  have hmF : AEStronglyMeasurable Ft (volume.prod volume) :=
    ((measurable_i4STDens a b c).indicator (measurableSet_i4SR a b c)).aestronglyMeasurable
  obtain ⟨hG1, hG2⟩ := (integrable_prod_iff hGt.aestronglyMeasurable).1 hGt
  have hnorm : ∀ l, ∫ n, ‖Gt (l, n)‖ = ∫ t, ‖Ft (l, t)‖ := fun l => by
    by_cases hl : 0 < l
    · simp_rw [hsecG l hl, hsecF l hl, norm_indicator_eq_indicator_norm]
      rw [integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioo]
      exact (i4ST_fiber ha hb hc habc hl).2.2
    · simp [hsecG0 l hl, hsecF0 l hl]
  have hFt : Integrable Ft (volume.prod volume) := by
    rw [integrable_prod_iff hmF]
    refine ⟨hG1.mono fun l hl => ?_, hG2.congr (ae_of_all _ hnorm)⟩
    by_cases hl0 : 0 < l
    · have e : (fun t => Ft (l, t)) =
          (Ioo (i4STmin a b c l) l).indicator (fun t => i4STDens a b c l t) :=
        funext (hsecF l hl0)
      have eG : (fun n => Gt (l, n)) = (Ioi 0).indicator (fun n => i4SG a b c (l, n)) :=
        funext (hsecG l hl0)
      rw [e, integrable_indicator_iff measurableSet_Ioo]
      rw [eG, integrable_indicator_iff measurableSet_Ioi] at hl
      exact (i4ST_fiber ha hb hc habc hl0).1.1 hl
    · have e : (fun t => Ft (l, t)) = 0 := funext (hsecF0 l hl0)
      rw [e]; exact integrable_zero _ _ _
  have hrow : ∀ l, ∫ n, Gt (l, n) = ∫ t, Ft (l, t) := fun l => by
    by_cases hl : 0 < l
    · simp_rw [hsecG l hl, hsecF l hl]
      rw [integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioo]
      exact (i4ST_fiber ha hb hc habc hl).2.1
    · simp [hsecG0 l hl, hsecF0 l hl]
  have hcol : ∀ t, ∫ l, Ft (l, t) = ∫ l in i4SLSec a b c t, i4STDens a b c l t := fun t => by
    simp_rw [hcolF]
    rw [integral_indicator (measurableSet_i4SLSec a b c t)]
  refine ⟨hFt.prod_left_ae.mono fun t ht => ?_, ?_, ?_⟩
  · have e : (fun l => Ft (l, t)) = (i4SLSec a b c t).indicator (fun l => i4STDens a b c l t) :=
      funext fun l => hcolF l t
    rw [e, integrable_indicator_iff (measurableSet_i4SLSec a b c t)] at ht
    exact ht
  · simp_rw [← hcol]
    exact hFt.integral_prod_right
  · rw [← integral_indicator hmQ, Measure.volume_eq_prod, integral_prod _ hGt]
    simp_rw [hrow]
    rw [integral_integral_swap (f := fun l t => Ft (l, t)) hFt]
    unfold i4SOmega
    simp_rw [hcol]

private theorem preimage_prodAssoc :
    MeasurableEquiv.prodAssoc ⁻¹' i4SDom4 = i4STri ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  ext ⟨⟨a, b⟩, l, n⟩
  simp only [mem_preimage, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply,
    i4SDom4, i4STri, mem_prod, mem_ofPred_eq, mem_Ioi]
  tauto

/-- **`P'(0)` as an integral of `i4SOmega` over the triangle**, with the integrability facts that
the evaluation of `i4SOmega` needs. -/
theorem i4P1_Omega :
    (∀ᵐ q ∂(volume.restrict i4STri), IntegrableOn (i4SG q.1 q.2 (1 - q.1 - q.2))
        (Ioi 0 ×ˢ Ioi 0)) ∧
      (∀ᵐ q ∂(volume.restrict i4STri), (∀ᵐ t, IntegrableOn
        (fun l => i4STDens q.1 q.2 (1 - q.1 - q.2) l t) (i4SLSec q.1 q.2 (1 - q.1 - q.2) t)) ∧
        Integrable (fun t => ∫ l in i4SLSec q.1 q.2 (1 - q.1 - q.2) t,
          i4STDens q.1 q.2 (1 - q.1 - q.2) l t)) ∧
      IntegrableOn (fun q : ℝ × ℝ => i4SOmega q.1 q.2 (1 - q.1 - q.2)) i4STri ∧
      iteratedDeriv 1 i4PInt 0 = ((∫ q in i4STri, i4SOmega q.1 q.2 (1 - q.1 - q.2) : ℝ) : ℂ) := by
  obtain ⟨hI, hE⟩ := i4P1_SM
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc :
      (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ ℝ × ℝ × (ℝ × ℝ)) := volume_preserving_prodAssoc
  set f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z => i4SG z.1.1 z.1.2 (1 - z.1.1 - z.1.2) z.2 with hf
  have hcomp : i4SMDens ∘ MeasurableEquiv.prodAssoc = f := rfl
  have hfI : IntegrableOn f (i4STri ×ˢ (Ioi 0 ×ˢ Ioi 0)) := by
    rw [← hcomp, ← preimage_prodAssoc,
      hmp.integrableOn_comp_preimage MeasurableEquiv.prodAssoc.measurableEmbedding]
    exact hI
  have hfE : ∫ y in i4SDom4, i4SMDens y = ∫ z in i4STri ×ˢ (Ioi 0 ×ˢ Ioi 0), f z := by
    rw [← hcomp, ← preimage_prodAssoc]
    exact (hmp.setIntegral_preimage_emb MeasurableEquiv.prodAssoc.measurableEmbedding
      i4SMDens i4SDom4).symm
  have hfI' := hfI
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hfI'
  have hae : ∀ᵐ q ∂(volume.restrict i4STri), IntegrableOn (i4SG q.1 q.2 (1 - q.1 - q.2))
      (Ioi 0 ×ˢ Ioi 0) := hfI'.prod_right_ae
  have hae2 : ∀ᵐ q ∂(volume.restrict i4STri),
      ∫ p in Ioi 0 ×ˢ Ioi 0, i4SG q.1 q.2 (1 - q.1 - q.2) p = i4SOmega q.1 q.2 (1 - q.1 - q.2) ∧
      ((∀ᵐ t, IntegrableOn (fun l => i4STDens q.1 q.2 (1 - q.1 - q.2) l t)
        (i4SLSec q.1 q.2 (1 - q.1 - q.2) t)) ∧
        Integrable (fun t => ∫ l in i4SLSec q.1 q.2 (1 - q.1 - q.2) t,
          i4STDens q.1 q.2 (1 - q.1 - q.2) l t)) := by
    filter_upwards [hae, ae_restrict_mem measurableSet_i4STri] with q hq hT
    obtain ⟨h1, h2, h3⟩ := hT
    have hs := i4ST_swap h1 h2 (by linarith) (by ring) hq
    exact ⟨hs.2.2, hs.1, hs.2.1⟩
  have hInner : IntegrableOn (fun q : ℝ × ℝ => ∫ p in Ioi 0 ×ˢ Ioi 0, f (q, p)) i4STri :=
    hfI'.integral_prod_left
  refine ⟨hae, hae2.mono fun q hq => hq.2, ?_, ?_⟩
  · exact hInner.congr_fun_ae (hae2.mono fun q hq => hq.1)
  · rw [hE, hfE, Measure.volume_eq_prod, setIntegral_prod f
      (by rwa [← Measure.volume_eq_prod]), integral_congr_ae (hae2.mono fun q hq => hq.1)]

end QED.ThreeLoopE

end
