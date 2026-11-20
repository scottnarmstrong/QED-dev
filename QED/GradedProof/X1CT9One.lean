/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CT9Base
public import QED.GradedProof.LevelOneElectron
public import QED.GradedProof.LevelZeroPhotonSplit
public import QED.Frozen.WickModel.SelfEnergyExistsUnique
import QED.TwoLoop.LoopBound

/-!
# (X₁) piece C: (T₉′) of the order-`e²` self-energy and vacuum-polarization pieces

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C. At graded order `2` the grading is `0` and the 1PI pieces are the
one-loop self-energy (or the `fermionCt` tree) and the one-loop bubble (or the `photonCt` tree).

* `t9_selfEnergy_two`: the self-energy piece has no closed fermion line
  (`QED.Lepton.Proof.reaches_of_one_zero`), so its integrand is the single-flavour (T1) integrand
  at the open-line mass with the open-line level-`0` counterterms (`seParams`), and the sealed
  T1 self-energy theorem (Z₁) (`QED.WickModel.selfEnergy_existsUnique`, first clause) gives its
  two stages; `QED.Lepton.Proof.HM.jointIntegrable_of_oneLoop` turns them into (T₉′).
* `t9_vacuumPolarization_two`: the flavour sum of the bubble splits into T1 bubbles
  (`QED.GradedProof.PhotonSplit.regulatedAmplitude₂_split`), each of which satisfies (T₉′) by
  the sealed (Z₂) (`QED.Lepton.Proof.HM.jointIntegrable_photon`).

Both are stated in the form of `hT₂` of the value lemmas, from the hypotheses of (X₁).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction loopCount lineMomentum₂ IsOnePI)
open QED.Graded

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}
  (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- **(T₉′) of a 1PI self-energy piece of graded order `2`**, in the form of `hT₂` of
`contractionValue_glueIn` and `contractionValue_glueOut`. -/
theorem t9_selfEnergy_two (hε : 0 < P.ε) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (C : Contraction 1 0 κ) (hC : IsOnePI C) (g : Grading κ)
    (hg : gradedOrder κ g = 2) (p : Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![p] ![]
        (lineMomentum₂ C ![p] ![p] ![] ℓ) αOut βIn ![] := by
  obtain rfl := t9_grading_eq_zero (g := g) (by omega)
  have h2 : ∑ t, (κ t).order = 2 := by rw [← X0.gradedOrder_zero]; exact hg
  have hle := QED.TwoLoop.LoopBound.loopCount_le_one_of_order h2.le (by norm_num) C hC
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · exact X0.jointEnergyFirstIntegrable_of_loopCount_eq_zero _ h0
  have hcl := QED.GradedProof.gauge_or_fermionCt_of_selfEnergy h2 C hC
  have hr := QED.Lepton.Proof.reaches_of_one_zero (h2.trans_le (by norm_num)) C hC
  have hm : 0 < Φ.mass Φ.openLine := hm₀.trans_le (hmass _)
  have hamp := fun (k : QED.WickModel.Line C → Fin 4 → ℝ) =>
    QED.GradedProof.regulatedAmplitude_zero_eq P (QED.GradedProof.seParams P Φ D) Φ D C
      (fun t _ => hr t) rfl rfl rfl rfl
      (fun t h => absurd h (by rcases hcl t with h' | h' <;> rw [h'] <;> decide))
      (fun _ _ => ⟨rfl, rfl, rfl⟩)
      (fun t h => absurd h (by rcases hcl t with h' | h' <;> rw [h'] <;> decide))
      ![p] ![] k αOut βIn ![]
  simp only [hamp]
  rw [QED.Lepton.Proof.regulatedAmplitude₂_eq_of_reaches (QED.GradedProof.seParams P Φ D) Φ
    (QED.Lepton.Proof.HM.t1F (QED.GradedProof.seParams P Φ D)) rfl hr]
  obtain ⟨h₁, h₂⟩ := (QED.WickModel.selfEnergy_existsUnique (QED.GradedProof.seParams P Φ D) hm
    hmγ hΛ).1 P.ε hε N κ h2.le C hC
    (QED.Lepton.Proof.HM.exists_isLoopLine_of_loopCount_eq_one h1) p (αOut 0) (βIn 0)
  rw [t9_fin_one_eq αOut, t9_fin_one_eq βIn]
  exact QED.Lepton.Proof.HM.jointIntegrable_of_oneLoop (QED.GradedProof.seParams P Φ D) C h1
    ![p] ![p] ![] ![αOut 0] ![βIn 0] ![] h₁ h₂

/-- **(T₉′) of a 1PI vacuum-polarization piece of graded order `2`**, in the form of `hT₂` of
`contractionValue_glueP`. -/
theorem t9_vacuumPolarization_two (hε : 0 < P.ε) (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (C : Contraction 0 2 κ) (hC : IsOnePI C) (g : Grading κ) (hg : gradedOrder κ g = 2)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![] ![k, -k]
        (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![] ![μ, ν] := by
  obtain rfl := t9_grading_eq_zero (g := g) (by omega)
  have h2 : ∑ t, (κ t).order = 2 := by rw [← X0.gradedOrder_zero]; exact hg
  have hle := QED.TwoLoop.LoopBound.loopCount_le_one_of_order h2.le (by norm_num) C hC
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · exact X0.jointEnergyFirstIntegrable_of_loopCount_eq_zero _ h0
  have hcl := QED.GradedProof.gauge_or_photonCt_of_two_photon h2 C hC
  have hR : QED.GradedProof.CtReaches C := fun t ht => by
    rcases hcl t.1 with h' | h'
    · exact absurd h' ht
    · exact absurd h' t.2
  have hpos : ∀ f, 0 < Φ.mass f := fun f => hm₀.trans_le (hmass f)
  set P' : Params := { P with δ₃ := P.e ^ 2 * D.d₃ 0 } with hP'
  have hamp := fun (kk : QED.WickModel.Line C → Fin 4 → ℝ) =>
    QED.GradedProof.regulatedAmplitude_zero_eq P P' Φ D C hR rfl rfl rfl rfl
      (fun t h => absurd h (by rcases hcl t with h' | h' <;> rw [h'] <;> decide))
      (fun t h => absurd h (by rcases hcl t with h' | h' <;> rw [h'] <;> decide))
      (fun _ _ => rfl) ![] ![k, -k] kk ![] ![] ![μ, ν]
  simp only [hamp]
  have hS := QED.Lepton.Proof.HM.isSimple_of_photon h2.le C hC
  have hκ := QED.GradedProof.PhotonSplit.ne_fermionCt_of_photon h2.le C hC
  have hsplit := QED.GradedProof.PhotonSplit.regulatedAmplitude₂_split P' Φ
    (t9_sum_coeff rep hrep Φ hPV₁) (t9_sum_coeff_mass rep hrep Φ hPV₂) hS hκ ![] ![k, -k]
  have hA := QED.Lepton.Proof.HM.jointIntegrable_photon (QED.GradedProof.PhotonSplit.refParams P')
    hε (by norm_num [QED.GradedProof.PhotonSplit.refParams])
    (by norm_num [QED.GradedProof.PhotonSplit.refParams])
    (by norm_num [QED.GradedProof.PhotonSplit.refParams])
    (QED.GradedProof.PhotonSplit.refParams_PV₁ P') (QED.GradedProof.PhotonSplit.refParams_PV₂ P')
    h2.le C hC h1 k μ ν
  have hB := fun i => QED.Lepton.Proof.HM.jointIntegrable_const_mul
    (QED.GradedProof.PhotonSplit.atomCoeff Φ i : ℂ)
    (QED.Lepton.Proof.HM.jointIntegrable_photon (QED.GradedProof.PhotonSplit.blockParams P' Φ i)
      hε (QED.GradedProof.PhotonSplit.atomMass_pos Φ hpos i)
      (QED.GradedProof.PhotonSplit.atomMass_lt_bigX Φ i)
      ((QED.GradedProof.PhotonSplit.atomMass_lt_bigX Φ i).trans (lt_add_one _))
      (QED.GradedProof.PhotonSplit.blockParams_PV₁ P' Φ i)
      (QED.GradedProof.PhotonSplit.blockParams_PV₂ P' Φ i) h2.le C hC h1 k μ ν)
  have h := QED.Lepton.Proof.HM.jointIntegrable_add hA
    (QED.Lepton.Proof.HM.jointIntegrable_sum Finset.univ fun i _ => hB i)
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [hsplit, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end QED.GradedProof.X1C

end
