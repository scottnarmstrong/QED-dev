/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ClassC
public import QED.Integration.EnergyFirstShift

/-!
# The classes `C1`, `C2`: the `ε → 0⁺` limit

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2, step L1. For a contraction with a single chord whose integrand, in a
conserved routing, is a shifted one-loop integrand `G(ℓ - s)`, the value (T₁₀) is the
energy-first integral (D) of `G` (`contractionValue₂_of_one_chord`; translation invariance
needs no integrability). For the representatives `repC1`, `repC2` (a `δ₁` vertex on the
one-loop self-energy) `G` is `δ₁` times the integrand of (62.28), so below both photon
thresholds the value converges to `δ₁ i (A(p²) p̸ + B(p²) m)` with the one-loop coefficients
`QED.WickModel.selfEnergyLoopA`, `selfEnergyLoopB` (`tendsto_contractionValue₂_repC1`,
`tendsto_contractionValue₂_repC2`).
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open Complex Filter Topology

section OneChord

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **The value of a contraction with one chord** is the energy-first integral of the shifted
one-loop integrand of its routing. -/
theorem contractionValue₂_of_one_chord (P : Params) {nf : ℕ} {C : Contraction nf nA κ}
    {c : Line C} (hc : ∀ g, IsChord g ↔ g = c) {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} (mom : (Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (mom ℓ)) (hchord : ∀ ℓ, mom ℓ c = ℓ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) (G : (Fin 4 → ℝ) → ℂ) (s : Fin 4 → ℝ)
    (hpt : ∀ ℓ, (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (mom ℓ) αOut βIn μ = G (ℓ - s)) :
    contractionValue₂ P C pOut pIn kIn αOut βIn μ = QED.OneLoop.energyFirstIntegral G := by
  unfold contractionValue₂
  rw [loopCount_eq_one_of_unique hc]
  have hfun : (fun ℓ : Fin 1 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 1) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) =
      fun ℓ => G (ℓ 0 - s) := by
    funext ℓ
    rw [QED.TwoLoop.IntegrableOrderFive.lineMomentum₂_eq_of_unique hc mom hcons hchord, mul_one,
      hpt]
  rw [hfun, QED.TwoLoop.jointEnergyFirstIntegral_one_eq (fun q => G (q - s)),
    QED.OneLoop.energyFirstIntegral_sub_right_eq_self]

end OneChord

/-- The one-loop self-energy limit `i (A(p²) p̸ + B(p²) m)` of (62.28) at the parameters `Q`. -/
noncomputable def seOneLoopLimit (Q : Params) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  I • ((selfEnergyLoopA Q (Minkowski.dot p p)) • Dirac.slash p
    + (selfEnergyLoopB Q (Minkowski.dot p p) * Q.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ))

/-- The value of `δ₁` times the one-loop self-energy integrand converges below both thresholds. -/
theorem tendsto_delta_one_mul_selfEnergy {Q : Params} (hm : 0 < Q.m) (hmγ : 0 < Q.mγ)
    (hΛ : 0 < Q.Λ) {p : Fin 4 → ℝ} (hpγ : -(Q.m + Q.mγ) ^ 2 < Minkowski.dot p p)
    (hpΛ : -(Q.m + Q.Λ) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun q =>
        (Q.δ₁ : ℂ) * selfEnergyIntegrand { Q with ε := ε } ε p q α β)
      (𝓝[>] 0) (𝓝 ((Q.δ₁ : ℂ) * seOneLoopLimit Q p α β)) := by
  have h := (tendsto_energyFirstIntegral_selfEnergyIntegrand hm hmγ hΛ hpγ hpΛ α β).const_mul
    (Q.δ₁ : ℂ)
  refine h.congr fun ε => ?_
  rw [QED.OneLoop.energyFirstIntegral_const_mul]
  rfl

/-- **The limit of the class `C1`** (`δ₁` at the incoming vertex). -/
theorem tendsto_contractionValue₂_repC1 {Q : Params} (hm : 0 < Q.m) (hmγ : 0 < Q.mγ)
    (hΛ : 0 < Q.Λ) {p : Fin 4 → ℝ} (hpγ : -(Q.m + Q.mγ) ^ 2 < Minkowski.dot p p)
    (hpΛ : -(Q.m + Q.Λ) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    Tendsto (fun ε : ℝ =>
        contractionValue₂ { Q with ε := ε } repC1 ![p] ![p] ![] ![α] ![β] ![])
      (𝓝[>] 0) (𝓝 ((Q.δ₁ : ℂ) * seOneLoopLimit Q p α β)) := by
  refine (tendsto_delta_one_mul_selfEnergy hm hmγ hΛ hpγ hpΛ α β).congr fun ε => ?_
  exact (contractionValue₂_of_one_chord _ c1_isChord_iff (c1Mom p) (c1_isConserved p)
    (fun ℓ => (c1Mom_apply p ℓ).1) ![α] ![β] ![] _ p
    (fun ℓ => c1_integrand { Q with ε := ε } p ℓ α β)).symm

/-- **The limit of the class `C2`** (`δ₁` at the outgoing vertex). -/
theorem tendsto_contractionValue₂_repC2 {Q : Params} (hm : 0 < Q.m) (hmγ : 0 < Q.mγ)
    (hΛ : 0 < Q.Λ) {p : Fin 4 → ℝ} (hpγ : -(Q.m + Q.mγ) ^ 2 < Minkowski.dot p p)
    (hpΛ : -(Q.m + Q.Λ) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    Tendsto (fun ε : ℝ =>
        contractionValue₂ { Q with ε := ε } repC2 ![p] ![p] ![] ![α] ![β] ![])
      (𝓝[>] 0) (𝓝 ((Q.δ₁ : ℂ) * seOneLoopLimit Q p α β)) := by
  refine (tendsto_delta_one_mul_selfEnergy hm hmγ hΛ hpγ hpΛ α β).congr fun ε => ?_
  exact (contractionValue₂_of_one_chord _ c2_isChord_iff (c2Mom p) (c2_isConserved p)
    (fun ℓ => (c2Mom_apply p ℓ).1) ![α] ![β] ![] _ p
    (fun ℓ => c2_integrand { Q with ε := ε } p ℓ α β)).symm

end QED.GradedProof.SE2

end
