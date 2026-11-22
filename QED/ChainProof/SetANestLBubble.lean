/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestLFubini
public import QED.GradedProof.VP2ClassG

/-!
# Set (a), obligation (N): the inner bound for a block-summed bubble

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`, the nested form
`QED.ChainProof.SetANest.LoopNested` of the `gaugeCt` classes `GW`, `GU`, whose inner integrand
is the integrand of a two-photon class `G0` or `G1`: a block-summed single-flavour bubble
`∑_f c_f d(rep f) W_{M_f}(-k, q)` (`QED.GradedProof.VP2.bubbleW`) at the photon momentum `-k`.

* `blockBubbleNeg`: that inner integrand.
* `integral_blockBubbleNeg_time`: by the three-flavour reduction
  (`QED.GradedProof.VP2.sum_block_eq_sum_triple`, `vacuumPolarizationIntegrand_triParams`), its
  energy integral is `∑_f c_f (-d(rep f)) G_f(-k, v⃗)`, `G_f` the energy integral
  `QED.WickModel.VacuumPolarizationLimit.spatialG` of the vacuum polarization integrand of the
  three-flavour parameters `(M_f, X, X + 1)`, `X = 1 + ∑ M`.
* **`oneLoopInnerBound_blockBubbleNeg`**: the hypotheses `OneLoopInnerBound (17/2) (7/2)` of
  `QED.ChainProof.SetANest.jointEnergyFirstIntegral_outerInner`, from the bound
  `‖G_f(k, v⃗)‖ ≤ C (1 + ‖k‖)^{17/2} (1 + ‖v⃗‖)^{-7/2}`
  (`QED.TwoLoop.NestedVPFubiniBound.exists_norm_spatialG_le_poly`), at fixed `ε > 0`, under the
  Pauli–Villars block conditions.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.ChainProof.SetANest

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.GradedProof.VP2

/-- The block-summed bubble at the photon momentum `-k`: `∑_f c_f d(rep f) W_{M_f}(-k, q)`. -/
noncomputable def blockBubbleNeg (P : Params) {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (rep : F → F) (d : F → ℂ) (k q : Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (d (rep f) * bubbleW P.e (Φ.mass f) P.ε (-k) q a b)

/-- Joint measurability of the energy integral of the vacuum polarization integrand along
`-k`, `k = (t, w)`. -/
theorem aestronglyMeasurable_spatialG_neg_cons (P : Params) (hε : 0 < P.ε) (w : Fin 3 → ℝ)
    (ρ σ : Fin 4) : AEStronglyMeasurable
      (fun x : ℝ × (Fin 3 → ℝ) => spatialG P P.ε (-(Fin.cons x.1 w : Fin 4 → ℝ)) ρ σ x.2)
      volume := by
  have hk : Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ => (Fin.cons z.1.1 w : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) (continuous_fst.comp continuous_fst)
      continuous_const
  have h2 : Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ =>
      (-(Fin.cons z.1.1 w : Fin 4 → ℝ), z.1.2, z.2) :=
    hk.neg.prodMk ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hc : Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ =>
      kappa P.e * timeSum P P.ε (-(Fin.cons z.1.1 w : Fin 4 → ℝ)) ρ σ z.2 z.1.2 := by
    have h3 := (QED.TwoLoop.NestedVPFubiniBound.continuous_timeSum_joint hε P ρ σ).comp h2
    exact continuous_const.mul h3
  have e : (fun x : ℝ × (Fin 3 → ℝ) => spatialG P P.ε (-(Fin.cons x.1 w : Fin 4 → ℝ)) ρ σ x.2) =
      fun x => ∫ y in Ioc (0 : ℝ) 1,
        kappa P.e * timeSum P P.ε (-(Fin.cons x.1 w : Fin 4 → ℝ)) ρ σ y x.2 := rfl
  rw [e]
  exact (hc.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).aestronglyMeasurable

section Bound

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (hε : 0 < P.ε) (d : F → ℂ)

/-- The heavy mass `X = 1 + ∑ M` of the three-flavour reduction. -/
noncomputable def heavyX : ℝ := 1 + ∑ g, Φ.mass g

include hrep hPV₁ hPV₂ in
/-- The three-flavour reduction of the block-summed bubble. -/
theorem blockBubbleNeg_eq (k q : Fin 4 → ℝ) (a b : Fin 4) :
    blockBubbleNeg P Φ rep d k q a b = ∑ f, (Φ.coeff f : ℂ) * (-d (rep f) *
      vacuumPolarizationIntegrand (triParams P (Φ.mass f) (heavyX Φ) (heavyX Φ + 1)) P.ε (-k) q
        a b) := by
  rw [blockBubbleNeg, sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ (heavyX Φ) (heavyX Φ + 1)
    (fun r M => d r * bubbleW P.e M P.ε (-k) q a b)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [vacuumPolarizationIntegrand_triParams]
  ring

omit [DecidableEq F] in
include hm₀ hmass in
theorem mass_lt_heavyX (g : F) : 0 < Φ.mass g ∧ Φ.mass g < heavyX Φ := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
  exact ⟨hpos g, by unfold heavyX; linarith⟩

omit [DecidableEq F] in
include hm₀ hmass in
/-- The Pauli–Villars conditions of the three-flavour parameters. -/
theorem triParams_pv (f : F) :
    let T := triParams P (Φ.mass f) (heavyX Φ) (heavyX Φ + 1)
    0 < T.m ∧ T.m < T.M₁ ∧ T.m < T.M₂ ∧ 1 + T.c₁ + T.c₂ = 0 ∧
      T.m ^ 2 + T.c₁ * T.M₁ ^ 2 + T.c₂ * T.M₂ ^ 2 = 0 := by
  obtain ⟨h0, h1⟩ := mass_lt_heavyX Φ hm₀ hmass f
  have hne : heavyX Φ ^ 2 - (heavyX Φ + 1) ^ 2 ≠ 0 := by nlinarith
  exact ⟨h0, h1, by simp only [triParams]; linarith, triA_triB_pv₁ _ _ _ hne,
    triA_triB_pv₂ _ _ _ hne⟩

include hrep hPV₁ hPV₂ hε in
/-- **The energy integral of the block-summed bubble** is the block sum of the energy integrals
of the three-flavour vacuum polarization integrands. -/
theorem integral_blockBubbleNeg_time (k : Fin 4 → ℝ) (a b : Fin 4) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, blockBubbleNeg P Φ rep d k (Fin.cons t v) a b =
      ∑ f, (Φ.coeff f : ℂ) * (-d (rep f) *
        spatialG (triParams P (Φ.mass f) (heavyX Φ) (heavyX Φ + 1)) P.ε (-k) a b v) := by
  simp only [blockBubbleNeg_eq P Φ rep hrep hPV₁ hPV₂ d]
  rw [integral_finsetSum _ fun f _ => ((integrable_vacuumPolarizationIntegrand_time hε _ _ a b
    v).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_const_mul, integral_const_mul, integral_vacuumPolarizationIntegrand_time hε]

include hm₀ hmass hrep hPV₁ hPV₂ hε in
/-- **The inner bound for the block-summed bubble**: the hypotheses
`OneLoopInnerBound (17/2) (7/2)` of `jointEnergyFirstIntegral_outerInner`. -/
theorem oneLoopInnerBound_blockBubbleNeg :
    OneLoopInnerBound (17 / 2) (7 / 2) (blockBubbleNeg P Φ rep d) := by
  refine ⟨fun k a b v => ?_, fun k a b => ?_, fun w a b => ?_, fun a b => ?_⟩
  · exact (energyFirst_blockBubble P Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ d hε (-k) a b).1 v
  · exact (energyFirst_blockBubble P Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ d hε (-k) a b).2
  · simp only [integral_blockBubbleNeg_time P Φ rep hrep hPV₁ hPV₂ hε d]
    refine Finset.aestronglyMeasurable_fun_sum _ fun f _ => ?_
    exact ((aestronglyMeasurable_spatialG_neg_cons
      (triParams P (Φ.mass f) (heavyX Φ) (heavyX Φ + 1)) hε w a b).const_mul _).const_mul _
  · have hC : ∀ f, ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin 4 → ℝ) (v : Fin 3 → ℝ),
        ‖spatialG (triParams P (Φ.mass f) (heavyX Φ) (heavyX Φ + 1)) P.ε k a b v‖ ≤
          C * (1 + ‖k‖) ^ (17 / 2 : ℝ) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ)) := fun f => by
      obtain ⟨h0, h1, h2, h3, h4⟩ := triParams_pv P Φ hm₀ hmass f
      exact QED.TwoLoop.NestedVPFubiniBound.exists_norm_spatialG_le_poly h0 h1 h2 h3 h4 hε a b
    choose C hC0 hC using hC
    refine ⟨∑ f, ‖(Φ.coeff f : ℂ) * -d (rep f)‖ * C f, fun k v => ?_⟩
    rw [integral_blockBubbleNeg_time P Φ rep hrep hPV₁ hPV₂ hε d, Finset.sum_mul,
      Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
    rw [← mul_assoc, norm_mul, mul_assoc (‖_‖ * C f), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have := hC f (-k) v
    rw [norm_neg] at this
    linarith

end Bound

end QED.ChainProof.SetANest

end
