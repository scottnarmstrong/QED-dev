/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MassIns

/-!
# (R-Π₄) step L3, limit: the mass insertions converge to the limit of the mass-derivative block

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L3.

By `QED.GradedProof.RPi4.fBubble_ctδ_F0_add_F1`, pointwise in the loop momentum,
`F0[ctδ] + F1[ctδ] = dBlock - iε remMBlock`, with the block-summed mass derivative of the bubble
`dBlock = ∑_f c_f δ_f M_f ∂_M bubbleW(M_f)` and the three-propagator remainder `remMBlock`. The
remainder converges flavour by flavour (constant numerator, three propagators: `vpf_remM`), so its
`iε` multiple tends to `0`:

* `vpf_remM`, `vpf_remMBlock`: covariant, null-continuous limits (`VPF`);
* `tendsto_dBlock` (**L3, limit form**): `∫ dBlock → W_F0[ctδ] + W_F1[ctδ]` as `ε → 0⁺`, at every
  `k` of the region.

What remains of L3 is the interchange of `lim_ε` with `∂_M` in `dBlock`, i.e. the identification
of this limit with `∑_f c_f δ_f M_f ∂_M` of the closed-form block bubble.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2

namespace QED.GradedProof.RPi4

open QED.TwoLoop.Bridge (propDenom IsLoopPoly)

/-! ### The remainder -/

section Remainder

variable {m₀ : ℝ} (hm₀ : 0 < m₀)
include hm₀

/-- **The remainder of one flavour has a covariant, null-continuous limit.** -/
theorem vpf_remM (e M : ℝ) (hM : m₀ ≤ M) :
    VPF (m₀ + m₀) fun ε k q μ ν => remM e M ε k q μ ν := by
  have p1 := vpf_three hm₀ M M M ⟨hM, hM, hM⟩ true true false (tRc 1)
    (fun p i j => isLoopPoly_tRc 1 p 0 i j) (tcovN_tRc 1)
    (fun q i j => isLoopPoly_tRc (n := 0) 1 0 q i j)
  have p2 := vpf_three hm₀ M M M ⟨hM, hM, hM⟩ true false false (tRc 1)
    (fun p i j => isLoopPoly_tRc 1 p 0 i j) (tcovN_tRc 1)
    (fun q i j => isLoopPoly_tRc (n := 0) 1 0 q i j)
  refine ((p1.add p2).const_mul (kF e * (M : ℂ) ^ 2)).congr fun ε _ k q i j => ?_
  have ht : (Dirac.gamma j * Dirac.gamma i).trace = (Dirac.gamma i * Dirac.gamma j).trace :=
    Matrix.trace_mul_comm _ _
  simp only [remM, tRc, QED.TwoLoop.LimitCovariance.traceT, gAF, gBF, ite_true, Matrix.mul_one,
    ht]
  push_cast
  ring

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (rep : F → F)

/-- The block-summed remainder `∑_f c_f δ_f remM(M_f)` of the two mass insertions. -/
noncomputable def remMBlock (ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (((P.e ^ 2 * (D.dm (rep f) 0 - D.d₂ (rep f) 0) : ℝ) : ℂ) *
    remM P.e (Φ.mass f) ε k q μ ν)

omit [DecidableEq F] in
theorem vpf_remMBlock (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    VPF (m₀ + m₀) fun ε k q μ ν => remMBlock P Φ D rep ε k q μ ν :=
  VPF.sum Finset.univ (fun f _ => (vpf_remM hm₀ P.e (Φ.mass f) (hmass f)).const_mul
    ((Φ.coeff f : ℂ) * ((P.e ^ 2 * (D.dm (rep f) 0 - D.d₂ (rep f) 0) : ℝ) : ℂ)))
    (by nlinarith) |>.congr fun ε _ k q μ ν => by
      simp only [remMBlock]
      refine Finset.sum_congr rfl fun f _ => ?_
      ring

end Remainder

/-! ### The mass-derivative block -/

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (rep : F → F)

/-- **The block-summed mass derivative of the bubble**
`∑_f c_f δ_f M_f ∂_M bubbleW(M_f)`, `δ_f = e² (d_m - d₂)(rep f)`. -/
noncomputable def dBlock (ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * ((((P.e ^ 2 * (D.dm (rep f) 0 - D.d₂ (rep f) 0)) * Φ.mass f : ℝ) :
    ℂ) * dBubbleW P.e (Φ.mass f) ε k q μ ν)

omit [DecidableEq F] in
theorem dBlock_eq {ε : ℝ} (hε : ε ≠ 0) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    dBlock P Φ D rep ε k q μ ν = fBubble P Φ (ctδ D) rep true true false ε k q μ ν +
      fBubble P Φ (ctδ D) rep false false true ε k q μ ν +
        (ε * I) * remMBlock P Φ D rep ε k q μ ν := by
  rw [fBubble_ctδ_F0_add_F1 P Φ D rep hε, dBlock, remMBlock]
  ring

section Limit

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0)

include hm₀ hmass hrep hPV₁ hPV₂ hD

/-- The integral of the mass-derivative block is the sum of the values of the classes `F0`, `F1`
at the pure mass insertion, up to `iε`. -/
theorem efi_dBlock_eq {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    (QED.OneLoop.energyFirstIntegral fun q => dBlock P Φ D rep ε k q μ ν) =
      val0 { P with ε := ε } Φ (ctδ D) k μ ν repF0 +
        val0 { P with ε := ε } Φ (ctδ D) k μ ν repF1 +
        (ε * I) * QED.OneLoop.energyFirstIntegral fun q => remMBlock P Φ D rep ε k q μ ν := by
  have h0 := (vpf_fBubble P Φ (ctδ D) rep m₀ hm₀ hmass hrep hPV₁ hPV₂ true true false).2 ε hε k μ ν
  have h1 :=
    (vpf_fBubble P Φ (ctδ D) rep m₀ hm₀ hmass hrep hPV₁ hPV₂ false false true).2 ε hε k μ ν
  have hR := (vpf_remMBlock hm₀ P Φ D rep hmass).2 ε hε k μ ν
  rw [val0_repF0 _ Φ (ctδ D) rep (hD_ctδ D rep hD), val0_repF1 _ Φ (ctδ D) rep (hD_ctδ D rep hD)]
  rw [show (fun q => dBlock P Φ D rep ε k q μ ν) = fun q =>
      (fBubble P Φ (ctδ D) rep true true false ε k q μ ν +
        fBubble P Φ (ctδ D) rep false false true ε k q μ ν) +
        (ε * I) * remMBlock P Φ D rep ε k q μ ν from
      funext fun q => dBlock_eq P Φ D rep hε.ne' k q μ ν,
    efi_add (h0.add h1) (hR.const_mul _), efi_add h0 h1,
    QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  rfl

/-- **(L3, limit form) The integral of the mass-derivative block converges to the sum of the class
limits of `F0`, `F1` at the pure mass insertion**, at every `k` of the region. -/
theorem tendsto_dBlock {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun q => dBlock P Φ D rep ε k q μ ν)
      (𝓝[>] 0) (𝓝 (wCl P Φ (ctδ D) repF0 k μ ν + wCl P Φ (ctδ D) repF1 k μ ν)) := by
  have hk' : -(m₀ + m₀) ^ 2 < Minkowski.dot k k := by nlinarith
  obtain ⟨W, hW, -, -⟩ := (vpf_remMBlock hm₀ P Φ D rep hmass).hasVPLim
  have hr := tendsto_epsI.mul (hW k hk' μ ν)
  rw [zero_mul] at hr
  have h := ((tendsto_wCl_F0 P Φ (ctδ D) rep hm₀ hmass hrep hPV₁ hPV₂ (hD_ctδ D rep hD) hk μ
    ν).add (tendsto_wCl_F1 P Φ (ctδ D) rep hm₀ hmass hrep hPV₁ hPV₂ (hD_ctδ D rep hD) hk μ
    ν)).add hr
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [efi_dBlock_eq P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD hε k μ ν]

end Limit

end QED.GradedProof.RPi4

end
