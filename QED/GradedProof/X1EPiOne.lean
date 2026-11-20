/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1EPiTwo
public import QED.GradedProof.LevelZeroPhotonSplit
public import QED.GradedProof.GEx2Inputs

/-!
# (X₁) piece E: the order-`e²` vacuum polarization near `k = 0`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece E. At order `e²` the vacuum polarization part is the multi-flavour
two-photon function with `δ₃ = e² d₃(0)` (`QED.GradedProof.onePIPart_two_photon`), which splits
at `ε > 0` into a reference T1 function and T1 blocks
(`QED.GradedProof.PhotonSplit.onePIFunction₂_photon_split`). Each T1 piece converges on
`k² > -4 m²` to `(-δ₃ + Π_loop(k²)) (k² g - k k)` (the frozen (Z₇′)), and the one-loop function is
continuous at `0`.

* `tendsto_t1_photon`: the limit of a T1 two-photon function at a general `k`;
* `vpZeroLim_one`: `VPZeroLim P Φ D 1` under the hypotheses of (X₁).
-/

@[expose] public section

open Complex Filter Topology Set
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X1E

open QED.GradedProof.VP2 QED.GradedProof.PhotonSplit QED.Lepton.Proof.HM

/-- **The T1 two-photon function converges** on `k² > -4 m²` to
`(-δ₃ + Π_loop(k²)) (k² g - k k)`. -/
theorem tendsto_t1_photon (Q : Params) (hm : 0 < Q.m) (hM₁ : Q.m < Q.M₁) (hM₂ : Q.m < Q.M₂)
    (hPV₁ : 1 + Q.c₁ + Q.c₂ = 0) (hPV₂ : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0)
    {k : Fin 4 → ℝ} (hk : -(4 * Q.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => (1 / I) * Lepton.onePIFunction₂ { Q with ε := ε } (t1F { Q with ε := ε })
        0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν]) (𝓝[>] 0)
      (𝓝 (((-Q.δ₃ + QED.WickModel.vacuumPolarizationLoop Q (Minkowski.dot k k) : ℝ) : ℂ) *
        vpT k μ ν)) := by
  have h := (QED.WickModel.vacuumPolarization_spec Q hm hM₁ hM₂ hPV₁ hPV₂).1 k hk μ ν
  rw [QED.WickModel.vacuumPolarization_eq_loop] at h
  have e : ∀ ε : ℝ, Lepton.onePIFunction₂ { Q with ε := ε } (t1F { Q with ε := ε }) 0 2 2 ![]
      ![] ![k, -k] ![] ![] ![μ, ν] = QED.WickModel.onePIFunction { Q with ε := ε } 0 2 2 ![] ![]
        ![k, -k] ![] ![] ![μ, ν] := fun ε =>
    QED.WickModel.onePIFunction₂_eq_onePIFunction _ 0 2 2 (by norm_num) _ _ _ _ _ _
  simp only [e]
  convert h using 2
  unfold vpT
  push_cast
  ring

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- The parameters of the order-`e²` function: `δ₃ = e² d₃(0)`. -/
noncomputable def oneParams : Params := { P with δ₃ := P.e ^ 2 * D.d₃ 0 }

/-- The limit of the order-`e²` vacuum polarization part on `k² > -4 min(1, m₀)²`. -/
noncomputable def piOneLim (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ((-(oneParams P D).δ₃ + QED.WickModel.vacuumPolarizationLoop (refParams (oneParams P D))
      (Minkowski.dot k k) : ℝ) : ℂ) * vpT k μ ν +
    ∑ i, (atomCoeff Φ i : ℂ) * (((-(oneParams P D).δ₃ + QED.WickModel.vacuumPolarizationLoop
      (blockParams (oneParams P D) Φ i) (Minkowski.dot k k) : ℝ) : ℂ) * vpT k μ ν)

theorem continuousAt_loop_zero {Q : Params} (hm : 0 < Q.m) (hM₁ : Q.m < Q.M₁)
    (hM₂ : Q.m < Q.M₂) :
    ContinuousAt (fun k : Fin 4 → ℝ =>
      QED.WickModel.vacuumPolarizationLoop Q (Minkowski.dot k k)) 0 := by
  have h1 : ContinuousAt (QED.WickModel.vacuumPolarizationLoop Q)
      (Minkowski.dot (0 : Fin 4 → ℝ) 0) := by
    rw [dot_zero_self]
    exact (QED.WickModel.continuousOn_vacuumPolarizationLoop hm hM₁ hM₂).continuousAt
      (Ioi_mem_nhds (by have := pow_pos hm 2; linarith))
  exact ContinuousAt.comp (g := QED.WickModel.vacuumPolarizationLoop Q)
    (f := fun k : Fin 4 → ℝ => Minkowski.dot k k) h1 continuous_dot_self.continuousAt

section One

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
include hm₀ hmass

omit [Fintype F] [DecidableEq F] hm₀ in
theorem min_le_atomMass (i : F ⊕ Fin 3) : min 1 m₀ ≤ atomMass Φ i := by
  rcases i with f | j
  · exact (min_le_right _ _).trans (hmass f)
  · refine (min_le_left _ _).trans ?_
    fin_cases j <;> norm_num [atomMass]

omit [DecidableEq F] in
theorem continuousAt_piOneLim (μ ν : Fin 4) :
    ContinuousAt (fun k => piOneLim P Φ D k μ ν) 0 := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hX := four_le_bigX Φ
  have href : ContinuousAt (fun k : Fin 4 → ℝ => QED.WickModel.vacuumPolarizationLoop
      (refParams (oneParams P D)) (Minkowski.dot k k)) 0 :=
    continuousAt_loop_zero (by norm_num [refParams]) (by norm_num [refParams])
      (by norm_num [refParams])
  have hblk : ∀ i, ContinuousAt (fun k : Fin 4 → ℝ => QED.WickModel.vacuumPolarizationLoop
      (blockParams (oneParams P D) Φ i) (Minkowski.dot k k)) 0 := fun i =>
    continuousAt_loop_zero (atomMass_pos Φ hpos i) (atomMass_lt_bigX Φ i)
      (by show atomMass Φ i < bigX Φ + 1; linarith [atomMass_lt_bigX Φ i])
  have hT := (continuous_vpT μ ν).continuousAt (x := 0)
  refine ((continuous_ofReal.continuousAt.comp (continuousAt_const.add href)).mul hT).add
    (tendsto_finsetSum _ fun i _ => continuousAt_const.mul
      ((continuous_ofReal.continuousAt.comp (continuousAt_const.add (hblk i))).mul hT))

variable (hPV₁ : ∑ f, Φ.coeff f = 0) (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0)
include hPV₁ hPV₂

theorem tendsto_piOne {k : Fin 4 → ℝ} (hk : -(4 * min 1 m₀ ^ 2) < Minkowski.dot k k)
    (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 1 k μ ν) (𝓝[>] 0)
      (𝓝 (piOneLim P Φ D k μ ν)) := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hX := four_le_bigX Φ
  have hc0 : 0 < min 1 m₀ := lt_min one_pos hm₀
  have hkm : ∀ a : ℝ, min 1 m₀ ≤ a → -(4 * a ^ 2) < Minkowski.dot k k := fun a ha => by
    have := pow_le_pow_left₀ hc0.le ha 2; linarith
  set Q := oneParams P D with hQ
  have Tref := tendsto_t1_photon (refParams Q) (by norm_num [refParams])
    (by norm_num [refParams]) (by norm_num [refParams]) (refParams_PV₁ Q) (refParams_PV₂ Q)
    (hkm 1 (min_le_left _ _)) μ ν
  have Tblk := fun i => tendsto_t1_photon (blockParams Q Φ i) (atomMass_pos Φ hpos i)
    (atomMass_lt_bigX Φ i) (by show atomMass Φ i < bigX Φ + 1; linarith [atomMass_lt_bigX Φ i])
    (blockParams_PV₁ Q Φ i) (blockParams_PV₂ Q Φ i)
    (hkm _ (min_le_atomMass Φ hmass i)) μ ν
  have hsum := Tref.add (tendsto_finsetSum Finset.univ fun i _ => (Tblk i).const_mul
    (atomCoeff Φ i : ℂ))
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hsplit := onePIFunction₂_photon_split { Q with ε := ε } hε Φ hpos hPV₁ hPV₂ k μ ν
  have hPi : vacuumPolarizationPart { P with ε := ε } Φ D 1 k μ ν = (1 / I) *
      Lepton.onePIFunction₂ { Q with ε := ε } Φ 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν] := by
    unfold vacuumPolarizationPart
    rw [show 2 * 1 = 2 from rfl, onePIPart_two_photon]
    rfl
  rw [hPi, hsplit, mul_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
  rw [mul_left_comm]
  rfl

end One

/-- **(X₁) piece E, order `e²`**: the vacuum polarization part of order `2` has a limit near
`k = 0`, continuous at `0`, with value `0`. -/
theorem vpZeroLim_one (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 2) : VPZeroLim P Φ D 1 := by
  have h₁ := GEx2.sum_eq_zero_of_blocks rep hrep Φ.coeff hPV₁
  have h₂ := GEx2.sum_eq_zero_of_blocks rep hrep (fun f => Φ.coeff f * Φ.mass f ^ 2) hPV₂
  have hc0 : 0 < min 1 m₀ := lt_min one_pos hm₀
  exact vpZeroLim_of P Φ D (by positivity : 0 < 4 * min 1 m₀ ^ 2) (piOneLim P Φ D)
    (fun k hk μ ν => tendsto_piOne P Φ D hm₀ hmass h₁ h₂ (by linarith) μ ν)
    (continuousAt_piOneLim P Φ D hm₀ hmass) (hD.2 1 le_rfl (by norm_num)).2

end QED.GradedProof.X1E

end
