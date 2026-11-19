/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VWardLim
public import QED.GradedProof.VP2VLim

/-!
# The two-loop Ward identity for the classes `VA`, `VB`, `VC`: transversality

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. Below `-(2 m₀)²`
the `k`-contraction of `VA + VB + VC` tends to zero (`tendsto_wardV`): it is `iε` times the
contraction of the remainders (`QED.GradedProof.VP2.ward_int` and the cancellations
`int_A1`, `int_A2`, `int_C1`), whose integrals converge (`vpj_rVA`, `vpj_rVB`, `vpj_rVC`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2
open QED.WickModel (Params)

section Values

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : QED.Graded.Counterterms F)

/-- **The `k`-contraction of the two-loop classes tends to zero.** -/
theorem tendsto_wardV (P : Params) (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {k : Fin 4 → ℝ}
    (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (ν : Fin 4) :
    Tendsto (fun ε : ℝ => ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
        (val0 { P with ε := ε } Φ D k μ ν repVA + val0 { P with ε := ε } Φ D k μ ν repVB +
          val0 { P with ε := ε } Φ D k μ ν repVC)) (𝓝[>] 0) (𝓝 0) := by
  have vA := vpj_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ
  have vB := vpj_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ
  have vC := vpj_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ
  have rA := vpj_rVA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ
  have rB := vpj_rVB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ
  have rC := vpj_rVC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ
  have lim : ∀ G, VPJ (2 * m₀) G → ∃ L, Tendsto (fun ε : ℝ => ∑ μ,
      ((Minkowski.lower k μ : ℝ) : ℂ) * QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => G ε k ℓ μ ν)) (𝓝[>] 0) (𝓝 L) := fun G hG => by
    obtain ⟨W, hW, -, -⟩ := hG.1 (fun _ => 1) 1 tendsto_const_nhds
    refine ⟨∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * W k μ ν,
      tendsto_finsetSum _ fun μ _ => ?_⟩
    have h := hW k hk μ ν
    simp only [one_mul] at h
    exact h.const_mul _
  obtain ⟨LA, hLA⟩ := lim _ rA
  obtain ⟨LB, hLB⟩ := lim _ rB
  obtain ⟨LC, hLC⟩ := lim _ rC
  have hε0 : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝 0) (𝓝 (((0 : ℝ) : ℂ) * I)) :=
      (Complex.continuous_ofReal.tendsto 0).mul_const I
    simpa using h.mono_left nhdsWithin_le_nhds
  have hT := hε0.mul ((hLA.add hLB).add hLC)
  rw [zero_mul] at hT
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [val0_repVA Φ D P hε.ne', val0_repVB Φ D P hε.ne', val0_repVC Φ D P hε.ne',
    mul_add, Finset.sum_add_distrib]
  rw [ward_int Φ P.e P.mγ P.Λ aVA bVA baseVA cVA aVA_eq hl_VA hε vA rA k ν
      (jef_pS Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e P.mγ P.Λ _ (isOddG_bt1 isOddG_bVA ν) _ _ _
        crit3A_VA1 crit3B_VA1 hε)
      (jef_pS Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e P.mγ P.Λ _ (isOddG_bVA ν) _ _ _
        crit3A_VA2 crit3B_VA2 hε),
    ward_int Φ P.e P.mγ P.Λ aVB bVB baseVB cVB aVB_eq hl_VB hε vB rB k ν
      (jef_pS Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e P.mγ P.Λ _ (isOddG_bt1 isOddG_bVB ν) _ _ _
        crit3A_VB1 crit3B_VB1 hε)
      (jef_pS Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e P.mγ P.Λ _ (isOddG_bVB ν) _ _ _
        crit3A_VB2 crit3B_VB2 hε),
    ward_int Φ P.e P.mγ P.Λ aVC bVC baseVC cVC aVC_eq hl_VC hε vC rC k ν
      (jef_pS Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e P.mγ P.Λ _ (isOddG_bt1 isOddG_bVC ν) _ _ _
        crit3A_VC1 crit3B_VC1 hε)
      (jef_pS Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e P.mγ P.Λ _ (isOddG_bVC ν) _ _ _
        crit3A_VC2 crit3B_VC2 hε),
    int_A1, int_A2, int_C1]
  ring

end Values

end QED.GradedProof.VP2

end
