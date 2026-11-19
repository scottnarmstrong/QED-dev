/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.LevelZeroPhotonSplit
import Mathlib.Tactic.FieldSimp

/-!
# The flavour-summed photon condition (F₁₁) for arbitrary flavour data

Helper level for the Phase 5 Stage 2 goal (G-ex₁) `QED.Graded.existsUnique_withLevel_zero`
(decision D-57). For flavour data `Φ` with positive masses and the two Pauli–Villars conditions,
the order-`e²` two-photon function at a lightlike `k` tends to `(-δ₃ + Π_Φ(0)) (-k^μ k^ν)`
(`tendsto_photon`), by the split `onePIFunction₂_photon_split` into T1 two-photon functions and
the sealed (Z₇′) for each of them (`QED.Lepton.Proof.HM.tendsto_photon_t1`); the weights of the
split sum to `0`, so `δ₃` enters once. Hence

* `isPhotonOnShell_iff`: **(F₁₁) holds iff `δ₃ = Π_Φ(0)`**;
* `existsUnique_isPhotonOnShell`: for `e ≠ 0` there is exactly one `y` with (F₁₁) at
  `δ₃ = e² y`.
-/

@[expose] public section

open Complex Finset Filter Topology
open QED.WickModel (Params vacuumPolarizationLoop)
open QED.Lepton QED.Lepton.Proof.HM

namespace QED.GradedProof.PhotonSplit

variable {F : Type} [Fintype F] [DecidableEq F]

/-- **`Π_Φ(0)`**: the weighted sum of the T1 loop functions at `0`. -/
noncomputable def photonPi0 (P : Params) (Φ : Flavors F) : ℝ :=
  vacuumPolarizationLoop (refParams P) 0 +
    ∑ i, atomCoeff Φ i * vacuumPolarizationLoop (blockParams P Φ i) 0

omit [DecidableEq F] in
theorem photonPi0_δ₃ (P : Params) (Φ : Flavors F) (d : ℝ) :
    photonPi0 { P with δ₃ := d } Φ = photonPi0 P Φ := rfl

/-- **The two-photon function of `Φ` at a lightlike `k`** tends to `(-δ₃ + Π_Φ(0)) (-k^μ k^ν)`. -/
theorem tendsto_photon (P : Params) (Φ : Flavors F) (hmass : ∀ f, 0 < Φ.mass f)
    (hPV₁ : ∑ f, Φ.coeff f = 0) (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0)
    {k : Fin 4 → ℝ} (hk : QED.Minkowski.dot k k = 0) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => (1 / I) * onePIFunction₂ { P with ε := ε } Φ
        0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν]) (𝓝[>] 0)
      (𝓝 (((-P.δ₃ + photonPi0 P Φ : ℝ) : ℂ) * ((-(k μ * k ν) : ℝ) : ℂ))) := by
  have hT := (tendsto_photon_t1 (refParams P) (by norm_num [refParams])
    (by norm_num [refParams]) (by norm_num [refParams]) (refParams_PV₁ P) (refParams_PV₂ P) hk
    μ ν).add (tendsto_finsetSum univ fun i _ =>
      (tendsto_photon_t1 (blockParams P Φ i) (atomMass_pos Φ hmass i) (atomMass_lt_bigX Φ i)
        ((atomMass_lt_bigX Φ i).trans (lt_add_one _)) (blockParams_PV₁ P Φ i)
        (blockParams_PV₂ P Φ i) hk μ ν).const_mul (atomCoeff Φ i : ℂ))
  have hw : ∑ i, (atomCoeff Φ i : ℂ) = 0 := by exact_mod_cast sum_atomCoeff Φ hPV₁
  convert hT.congr' ?_ using 2
  · have h1 : (refParams P).δ₃ = P.δ₃ := rfl
    have h2 : ∀ i, (blockParams P Φ i).δ₃ = P.δ₃ := fun _ => rfl
    simp only [h1, h2, photonPi0]
    push_cast
    have e : ∀ i, (atomCoeff Φ i : ℂ) * ((-(P.δ₃ : ℂ) +
        (vacuumPolarizationLoop (blockParams P Φ i) 0 : ℂ)) * (-((k μ : ℂ) * k ν))) =
        (-(P.δ₃ : ℂ) * (-((k μ : ℂ) * k ν))) * atomCoeff Φ i +
          (atomCoeff Φ i * (vacuumPolarizationLoop (blockParams P Φ i) 0 : ℂ)) *
            (-((k μ : ℂ) * k ν)) := fun i => by ring
    rw [sum_congr rfl fun i _ => e i, sum_add_distrib, ← mul_sum, ← sum_mul, hw]
    ring
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hs := onePIFunction₂_photon_split { P with ε := ε } hε Φ hmass hPV₁ hPV₂ k μ ν
    have e0 : refParams { P with ε := ε } = { refParams P with ε := ε } := rfl
    have eb : ∀ i, blockParams { P with ε := ε } Φ i = { blockParams P Φ i with ε := ε } :=
      fun _ => rfl
    simp only [e0, eb] at hs
    rw [hs, mul_add, mul_sum]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    ring

/-- **The flavour-summed photon condition (F₁₁) in closed form**: `δ₃ = Π_Φ(0)`. -/
theorem isPhotonOnShell_iff (P : Params) (Φ : Flavors F) (hmass : ∀ f, 0 < Φ.mass f)
    (hPV₁ : ∑ f, Φ.coeff f = 0) (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) :
    IsPhotonOnShell P Φ ↔ P.δ₃ = photonPi0 P Φ := by
  constructor
  · intro h
    have h1 := tendsto_nhds_unique (tendsto_photon P Φ hmass hPV₁ hPV₂ dot_lightlike 0 0)
      (h ![1, 1, 0, 0] dot_lightlike 0 0)
    have h2 : (-P.δ₃ + photonPi0 P Φ) * (-1) = 0 := by
      have : ((-(((![1, 1, 0, 0] : Fin 4 → ℝ) 0) * ((![1, 1, 0, 0] : Fin 4 → ℝ) 0)) : ℝ) : ℂ) =
          ((-1 : ℝ) : ℂ) := by simp
      rw [this, ← Complex.ofReal_mul] at h1
      exact_mod_cast h1
    linarith
  · intro h k hk μ ν
    have hT := tendsto_photon P Φ hmass hPV₁ hPV₂ hk μ ν
    have h0 : -P.δ₃ + photonPi0 P Φ = 0 := by linarith
    rw [h0] at hT
    simpa using hT

/-- **The order-`e²` photon counterterm exists and is unique**: for `e ≠ 0` there is exactly one
`y` with (F₁₁) at `δ₃ = e² y`, namely `Π_Φ(0) / e²`. -/
theorem existsUnique_isPhotonOnShell (P : Params) (he : P.e ≠ 0) (Φ : Flavors F)
    (hmass : ∀ f, 0 < Φ.mass f) (hPV₁ : ∑ f, Φ.coeff f = 0)
    (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) :
    ∃! y : ℝ, IsPhotonOnShell { P with δ₃ := P.e ^ 2 * y } Φ := by
  have he2 : P.e ^ 2 ≠ 0 := pow_ne_zero 2 he
  refine ⟨photonPi0 P Φ / P.e ^ 2, ?_, fun y hy => ?_⟩
  · beta_reduce
    rw [isPhotonOnShell_iff _ Φ hmass hPV₁ hPV₂, photonPi0_δ₃]
    show P.e ^ 2 * (photonPi0 P Φ / P.e ^ 2) = photonPi0 P Φ
    field_simp
  · beta_reduce at hy
    rw [isPhotonOnShell_iff _ Φ hmass hPV₁ hPV₂, photonPi0_δ₃] at hy
    change P.e ^ 2 * y = photonPi0 P Φ at hy
    rw [← hy]
    field_simp

end QED.GradedProof.PhotonSplit

end
