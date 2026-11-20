/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4PairF

/-!
# (R-Π₄) step L7: linearity of the limit of the weighted mass-derivative block

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L7 (mass part). The
named limit `fLim Φ rep e δ` is linear in the block weight `δ` on the region:

* `fLim_smul`: `fLim (c • δ) = c fLim δ`;
* `fLim_sum`: `fLim (∑ᵢ δᵢ) = ∑ᵢ fLim δᵢ`;
* `fLim_eq_sum_single`: `fLim δ = ∑_g δ g · fLim (Pi.single g 1)`.

So at the photon pair `(a, b)` the mass part is a combination of the unit-weight limits with the
coefficients `ctPair e M_g a b`, which are `O(√b)` (`QED.GradedProof.RPi4.abs_ctPair_le`).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2

namespace QED.GradedProof.RPi4

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

omit [DecidableEq F] in
theorem dBlockD_smul (e c : ℝ) (δ : F → ℝ) (ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    dBlockD Φ rep e (c • δ) ε k q μ ν = (c : ℂ) * dBlockD Φ rep e δ ε k q μ ν := by
  simp only [dBlockD, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun f _ => ?_
  push_cast
  ring

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The limit is homogeneous in the weight.** -/
theorem fLim_smul (P : Params) (he : P.e ≠ 0) (c : ℝ) (δ : F → ℝ) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    fLim Φ rep P.e (c • δ) k μ ν = (c : ℂ) * fLim Φ rep P.e δ k μ ν := by
  have h := (tendsto_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he δ hk μ ν).const_mul (c : ℂ)
  refine limT_eq (h.congr fun ε => ?_)
  rw [← QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  exact congrArg _ (funext fun q => (dBlockD_smul Φ rep P.e c δ ε k q μ ν).symm)

/-- **The limit is additive over finite sums of weights.** -/
theorem fLim_sum (P : Params) (he : P.e ≠ 0) {ι : Type*} (s : Finset ι) (δ : ι → F → ℝ)
    {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    fLim Φ rep P.e (∑ i ∈ s, δ i) k μ ν = ∑ i ∈ s, fLim Φ rep P.e (δ i) k μ ν := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := fLim_smul Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he 0 0 hk μ ν
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      fLim_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he _ _ hk μ ν, ih]

/-- **The limit is the combination of the unit-weight limits.** -/
theorem fLim_eq_sum_single (P : Params) (he : P.e ≠ 0) (δ : F → ℝ) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    fLim Φ rep P.e δ k μ ν =
      ∑ g, (δ g : ℂ) * fLim Φ rep P.e (Pi.single g 1) k μ ν := by
  have hδ : δ = ∑ g, δ g • (Pi.single g 1 : F → ℝ) := by
    funext f
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hδ]
  rw [fLim_sum Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he _ _ hk μ ν]
  exact Finset.sum_congr rfl fun g _ => fLim_smul Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he _ _ hk μ ν

end QED.GradedProof.RPi4

end
