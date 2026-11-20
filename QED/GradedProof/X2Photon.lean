/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1EPhoton
public import QED.GradedProof.X1EPiTwo
public import QED.GradedProof.X2PiF
public import QED.GradedProof.X2PiV

/-!
# (X₂) piece D: the photon legs near a spacelike photon momentum

Helper level for the Phase 5 Stage 2 goal (X₂)
`QED.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit` (decision D-57), piece D. At the
LSZ limit of (X₂) the photon momentum `r' - r` tends to `q = p' - p` with `q² > 0` (spacelike in
the mostly-plus metric). Every photon leg `QED.GradedProof.X1C.photonLeg` of order `2d ≤ 4` has
an `ε → 0⁺` limit at every `k` near `q`, continuous at `q` (`QED.GradedProof.X1E.ZLim`), with the
explicit value `legLim d q ν μ` built from the `ε = 0` photon propagator and the vacuum
polarization limits `QED.GradedProof.X1E.piOneLim`, `QED.GradedProof.X1E.piTwoLim`.

* `continuousAt_photonPropagator_spacelike`, `zLim_photonProp_spacelike`;
* `continuousAt_piOneLim_spacelike`, `continuousAt_polBlock_of_nonneg`,
  `continuousAt_piTwoLim_spacelike`;
* `zLim_piOne`, `zLim_piTwo`, `legLim`, `zLim_photonLeg_spacelike`.
-/

@[expose] public section

open Complex Filter Topology Set
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X2

open QED.GradedProof.VP2 QED.GradedProof.RPi4 QED.GradedProof.X1C
open QED.GradedProof.PhotonSplit QED.Lepton.Proof.HM
open QED.GradedProof.X1E (ZLim piOneLim piTwoLim oneParams continuous_dot_self)

variable {q : Fin 4 → ℝ} (hq : 0 ≤ Minkowski.dot q q)
include hq

theorem eventually_dot_gt_of_nonneg {T : ℝ} (hT : 0 < T) :
    ∀ᶠ k in 𝓝 q, -T < Minkowski.dot k k :=
  (isOpen_lt continuous_const continuous_dot_self).mem_nhds (by
    show -T < Minkowski.dot q q
    linarith)

/-- The `ε = 0` photon propagator is continuous at a spacelike `q`. -/
theorem continuousAt_photonPropagator_spacelike {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (ν ρ : Fin 4) :
    ContinuousAt (fun k => QED.OneLoop.photonPropagator mγ Λ 0 k ν ρ) q := by
  have h : ∀ M : ℝ, 0 < M → ContinuousAt (fun k : Fin 4 → ℝ =>
      (((Minkowski.dot k k + M ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)⁻¹) q := fun M hM => by
    refine ContinuousAt.inv₀ ?_ ?_
    · exact ((continuous_ofReal.comp (continuous_dot_self.add continuous_const)).sub
        continuous_const).continuousAt
    · have hpos : 0 < Minkowski.dot q q + M ^ 2 := by positivity
      simp only [ofReal_zero, zero_mul, sub_zero]
      exact ofReal_ne_zero.mpr hpos.ne'
  unfold QED.OneLoop.photonPropagator
  exact continuousAt_const.mul ((h mγ hmγ).sub (h Λ hΛ))

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

theorem zLim_photonProp_spacelike (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (ν ρ : Fin 4) :
    ZLim (fun ε k => photonProp { P with ε := ε } k ν ρ) q
      (QED.OneLoop.photonPropagator P.mγ P.Λ 0 q ν ρ) := by
  have hγ := eventually_dot_gt_of_nonneg hq (pow_pos hmγ 2)
  have hL := eventually_dot_gt_of_nonneg hq (pow_pos hΛ 2)
  refine ⟨fun k => QED.OneLoop.photonPropagator P.mγ P.Λ 0 k ν ρ, ?_,
    continuousAt_photonPropagator_spacelike hq hmγ hΛ ν ρ, rfl⟩
  filter_upwards [hγ, hL] with k h1 h2
  exact QED.WickModel.tendsto_photonPropagator_zero h1.ne' h2.ne' ν ρ

/-- The one-loop vacuum-polarization function of a model with `m < M₁, M₂` is continuous at a
spacelike `q`. -/
theorem continuousAt_loop_spacelike {Q : Params} (hm : 0 < Q.m) (hM₁ : Q.m < Q.M₁)
    (hM₂ : Q.m < Q.M₂) :
    ContinuousAt (fun k : Fin 4 → ℝ =>
      QED.WickModel.vacuumPolarizationLoop Q (Minkowski.dot k k)) q := by
  have h1 : ContinuousAt (QED.WickModel.vacuumPolarizationLoop Q) (Minkowski.dot q q) :=
    (QED.WickModel.continuousOn_vacuumPolarizationLoop hm hM₁ hM₂).continuousAt
      (Ioi_mem_nhds (by have := pow_pos hm 2; linarith))
  exact ContinuousAt.comp (g := QED.WickModel.vacuumPolarizationLoop Q)
    (f := fun k : Fin 4 → ℝ => Minkowski.dot k k) h1 continuous_dot_self.continuousAt

omit [DecidableEq F] in
theorem continuousAt_piOneLim_spacelike {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (μ ν : Fin 4) : ContinuousAt (fun k => piOneLim P Φ D k μ ν) q := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hX := four_le_bigX Φ
  have href : ContinuousAt (fun k : Fin 4 → ℝ => QED.WickModel.vacuumPolarizationLoop
      (refParams (oneParams P D)) (Minkowski.dot k k)) q :=
    continuousAt_loop_spacelike hq (by norm_num [refParams]) (by norm_num [refParams])
      (by norm_num [refParams])
  have hblk : ∀ i, ContinuousAt (fun k : Fin 4 → ℝ => QED.WickModel.vacuumPolarizationLoop
      (blockParams (oneParams P D) Φ i) (Minkowski.dot k k)) q := fun i =>
    continuousAt_loop_spacelike hq (atomMass_pos Φ hpos i) (atomMass_lt_bigX Φ i)
      (by show atomMass Φ i < bigX Φ + 1; linarith [atomMass_lt_bigX Φ i])
  have hT := (X1E.continuous_vpT μ ν).continuousAt (x := q)
  exact ((continuous_ofReal.continuousAt.comp (continuousAt_const.add href)).mul hT).add
    (tendsto_finsetSum _ fun i _ => continuousAt_const.mul
      ((continuous_ofReal.continuousAt.comp (continuousAt_const.add (hblk i))).mul hT))

omit hq in
omit [DecidableEq F] in
/-- The block-summed one-loop coefficient is continuous at every `s ≥ 0`. -/
theorem continuousAt_polBlock_of_nonneg (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (d : F → ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousAt (polBlock P Φ rep d) s := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hlt : ∀ g, Φ.mass g < auxX Φ := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    simp only [auxX]
    linarith
  unfold polBlock
  refine tendsto_finsetSum _ fun f _ => ?_
  have hL : ContinuousAt (QED.WickModel.vacuumPolarizationLoop
      (triParams P (Φ.mass f) (auxX Φ) (auxX Φ + 1))) s :=
    (QED.WickModel.continuousOn_vacuumPolarizationLoop (P := triParams P (Φ.mass f) (auxX Φ)
      (auxX Φ + 1)) (hpos f) (hlt f) (by show Φ.mass f < auxX Φ + 1; linarith [hlt f])
      ).continuousAt (Ioi_mem_nhds (by
        show -(4 * Φ.mass f ^ 2) < s
        have := pow_pos (hpos f) 2; linarith))
  exact ((continuous_ofReal.continuousAt.comp hL).const_mul I |>.const_mul _).const_mul _

theorem continuousAt_piTwoLim_spacelike (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (μ ν : Fin 4) :
    ContinuousAt (fun k => piTwoLim P Φ D rep m₀ k μ ν) q := by
  have hpol : ContinuousAt (fun k : Fin 4 → ℝ => polG P Φ D rep (Minkowski.dot k k) * vpT k μ ν)
      q :=
    (ContinuousAt.comp_of_eq (continuousAt_polBlock_of_nonneg P Φ rep hm₀ hmass _ hq)
      continuous_dot_self.continuousAt rfl).mul (X1E.continuous_vpT μ ν).continuousAt
  have hct : Continuous fun k : Fin 4 → ℝ =>
      -((P.e ^ 4 * D.d₃ 1 * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ) : ℂ) :=
    (continuous_ofReal.comp (continuous_const.mul ((continuous_dot_self.mul continuous_const).sub
      ((continuous_apply μ).mul (continuous_apply ν))))).neg
  exact hct.continuousAt.add (continuousAt_const.mul
    (((((((continuousAt_vVal_VA hq Φ hm₀ hmass P.e hmγ hΛ μ ν).add
      (continuousAt_vVal_VB hq Φ hm₀ hmass P.e hmγ hΛ μ ν)).add
      (continuousAt_vVal_VC hq Φ hm₀ hmass P.e hmγ hΛ μ ν)).add hpol).add hpol).add
      (continuousAt_fbVal hq P Φ D rep hm₀ hmass true true false μ ν)).add
      (continuousAt_fbVal hq P Φ D rep hm₀ hmass false false true μ ν)))

/-- **The order-`2` vacuum polarization near a spacelike `q`.** -/
theorem zLim_piOne {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hPV₁ : ∑ f, Φ.coeff f = 0) (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) (μ ν : Fin 4) :
    ZLim (fun ε k => vacuumPolarizationPart { P with ε := ε } Φ D 1 k μ ν) q
      (piOneLim P Φ D q μ ν) := by
  have hc0 : 0 < min 1 m₀ := lt_min one_pos hm₀
  refine ⟨fun k => piOneLim P Φ D k μ ν, ?_,
    continuousAt_piOneLim_spacelike hq P Φ D hm₀ hmass μ ν, rfl⟩
  filter_upwards [eventually_dot_gt_of_nonneg hq (by positivity : 0 < 4 * min 1 m₀ ^ 2)]
    with k hk
  exact X1E.tendsto_piOne P Φ D hm₀ hmass hPV₁ hPV₂ hk μ ν

/-- **The order-`4` vacuum polarization near a spacelike `q`**, in the block scheme with
level-`0` constancy. -/
theorem zLim_piTwo (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD₁ : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0)
    (hD₂ : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) (μ ν : Fin 4) :
    ZLim (fun ε k => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) q
      (piTwoLim P Φ D rep m₀ q μ ν) := by
  refine ⟨fun k => piTwoLim P Φ D rep m₀ k μ ν, ?_,
    continuousAt_piTwoLim_spacelike hq P Φ D rep hm₀ hmass hmγ hΛ μ ν, rfl⟩
  filter_upwards [eventually_dot_gt_of_nonneg hq (by positivity : 0 < 4 * m₀ ^ 2)] with k hk
  exact X1E.tendsto_piTwo P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD₁ hD₂ hk μ ν

omit hq

/-- The value of the photon leg of order `2d` at the LSZ limit, from the `ε = 0` propagator and
the vacuum-polarization limits. -/
noncomputable def legLim (rep : F → F) (m₀ : ℝ) (d : ℕ) (q : Fin 4 → ℝ) (ν μ : Fin 4) : ℂ :=
  match d with
  | 0 => if ν = μ then 1 else 0
  | 1 => ∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ 0 q ν ρ * piOneLim P Φ D q μ ρ
  | 2 => ∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ 0 q ν ρ * piTwoLim P Φ D rep m₀ q μ ρ +
      ∑ ρ, ∑ l, ∑ k, QED.OneLoop.photonPropagator P.mγ P.Λ 0 q ν ρ * piOneLim P Φ D q l ρ *
        (QED.OneLoop.photonPropagator P.mγ P.Λ 0 q l k * piOneLim P Φ D q μ k)
  | _ => 0

include hq in
/-- **The photon legs near a spacelike `q`**: under the hypotheses of (X₁) (block
Pauli–Villars conditions, renormalized through order `e⁴`), every photon leg of order `2d ≤ 4`
has an `ε → 0⁺` limit near `q`, continuous at `q`, with value `legLim d q ν μ`. -/
theorem zLim_photonLeg_spacelike (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 2) {d : ℕ} (hd : d < 3) (ν μ : Fin 4) :
    ZLim (fun ε k => photonLeg { P with ε := ε } Φ D d k ν μ) q
      (legLim P Φ D rep m₀ d q ν μ) := by
  have h₁ := GEx2.sum_eq_zero_of_blocks rep hrep Φ.coeff hPV₁
  have h₂ := GEx2.sum_eq_zero_of_blocks rep hrep (fun f => Φ.coeff f * Φ.mass f ^ 2) hPV₂
  have hD₁ : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 := fun f => (hD.1 f 0 (by norm_num)).1
  have hD₂ : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 :=
    fun f => (hD.1 f 0 (by norm_num)).2
  have Δ := zLim_photonProp_spacelike hq P hmγ hΛ
  have P1 := zLim_piOne hq P Φ D hm₀ hmass h₁ h₂
  have P2 := zLim_piTwo hq P Φ D rep hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD₁ hD₂
  interval_cases d
  · by_cases h : ν = μ
    · simpa [photonLeg, legLim, h] using
        (ZLim.const 1 : ZLim (fun _ (_ : Fin 4 → ℝ) => (1 : ℂ)) q 1)
    · simpa [photonLeg, legLim, h] using
        (ZLim.const 0 : ZLim (fun _ (_ : Fin 4 → ℝ) => (0 : ℂ)) q 0)
  · exact ZLim.sum Finset.univ fun ρ _ => (Δ ν ρ).mul (P1 μ ρ)
  · exact (ZLim.sum Finset.univ fun ρ _ => (Δ ν ρ).mul (P2 μ ρ)).add
      (ZLim.sum Finset.univ fun ρ _ => ZLim.sum Finset.univ fun l _ =>
        ZLim.sum Finset.univ fun k _ => ((Δ ν ρ).mul (P1 l ρ)).mul ((Δ l k).mul (P1 μ k)))

end QED.GradedProof.X2

end
