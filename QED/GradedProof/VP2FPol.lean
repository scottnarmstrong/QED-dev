/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2FWard

/-!
# The classes `F0 + F1`: the transverse limit

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. From the
integrated Ward identity `QED.GradedProof.VP2.efi_wardF`, the `k`-contraction of the values of
`F0 + F1` tends to `0` below `-(2 m₀)²` (`tendsto_wardF`): the bubble term tends to
`k_μ Π_B(k²) (k² g^{μν} - k^μ k^ν) = 0` and the remainder term is `iε` times a convergent family.
With the covariant, null-continuous limits `hasVPLim_repF0`, `hasVPLim_repF1` this gives the
transverse form `Π_F(k²) (k² g - k k)` of the limit (`exists_pol_F`).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit QED.TwoLoop.LimitCovariance
open QED.WickModel (Params)

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0)
include hm₀ hmass hrep hPV₁ hPV₂ hD

/-- **The `k`-contraction of `F0 + F1` tends to `0`** below `-(2 m₀)²`. -/
theorem tendsto_wardF {k : Fin 4 → ℝ} (hk : -(m₀ + m₀) ^ 2 < Minkowski.dot k k) (ν : Fin 4) :
    Tendsto (fun ε : ℝ => ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
        (val0 { P with ε := ε } Φ D k μ ν repF0 + val0 { P with ε := ε } Φ D k μ ν repF1))
      (𝓝[>] 0) (𝓝 0) := by
  have hk4 : -(4 * m₀ ^ 2) < Minkowski.dot k k := by nlinarith
  have hB : Tendsto (fun ε : ℝ => ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
      QED.OneLoop.energyFirstIntegral (fun q => fwB P Φ D rep ν μ ε k q)) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ fun μ _ =>
      (tendsto_blockBubble P Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (dB P D) hk4 μ ν).const_mul
        ((Minkowski.lower k μ : ℝ) : ℂ)
    have hz : ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
        (polBlock P Φ rep (dB P D) (Minkowski.dot k k) * vpT k μ ν) = 0 := by
      simp_rw [mul_left_comm _ (polBlock P Φ rep (dB P D) (Minkowski.dot k k))]
      rw [← Finset.mul_sum, sum_lower_vpT, mul_zero]
    rw [hz] at h
    exact h
  obtain ⟨W, hW, -, -⟩ := (vpf_fwR P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂).hasVPLim
  have hR : Tendsto (fun ε : ℝ => ((ε : ℂ) * I) * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
      QED.OneLoop.energyFirstIntegral (fun q => traceT 1 1 ν μ * fwR P Φ D rep ε k q))
      (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_epsI.mul (tendsto_finsetSum Finset.univ fun μ _ =>
      (hW k hk ν μ).const_mul ((Minkowski.lower k μ : ℝ) : ℂ))
    rwa [zero_mul] at h
  have h := hB.add hR
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [val0_repF0 _ Φ D rep hD, val0_repF1 _ Φ D rep hD]
  exact (efi_wardF P Φ D rep ν m₀ hm₀ hmass hrep hPV₁ hPV₂ hε k).symm

/-- **The classes `F0 + F1` converge to `Π_F(k²) (k² g - k k)`** below `-(2 m₀)²`. -/
theorem exists_pol_F :
    ∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -(m₀ + m₀) ^ 2 < Minkowski.dot k k → ∀ μ ν : Fin 4,
      Tendsto (fun ε : ℝ => val0 { P with ε := ε } Φ D k μ ν repF0 +
          val0 { P with ε := ε } Φ D k μ ν repF1) (𝓝[>] 0)
        (𝓝 (Pol (Minkowski.dot k k) * vpT k μ ν)) :=
  ((hasVPLim_repF0 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD).add
    (hasVPLim_repF1 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD)).exists_pol fun _ hk ν =>
    tendsto_wardF P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD hk ν

end QED.GradedProof.VP2

end
