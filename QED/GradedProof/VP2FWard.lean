/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2FWardR

/-!
# The classes `F0 + F1` are transverse in the limit

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. Summing the
one-flavour Ward identity `wardF_mass` over the flavours with the block coefficients
(`wardF_block`), the `k`-contraction of the block-summed inserted bubbles of `F0` and `F1` is

`T(q) - T(k + q) + k_μ B^μ(q) + iε k_μ Tr[γ^ν γ^μ] R(q)`,

with block sums `T` (`fwT`), `B^μ` the block-summed one-loop bubble (`fwB`) and `R` (`fwR`).
Every term is integrable in both stages at `ε > 0` (`QED.GradedProof.VP2.ef_twoBlock`,
`QED.GradedProof.VP2.vpf_rBlock`), the energy-first integral is translation invariant, so the
`T` terms cancel (`efi_wardF`). As `ε → 0⁺` the bubble term tends to
`k_μ Π_B(k²) (k² g^{μν} - k^μ k^ν) = 0` (`QED.GradedProof.VP2.tendsto_blockBubble`) and the
remainder term to `0` (it has a limit times `iε`): `tendsto_wardF`. With the covariant limits of
`QED.GradedProof.VP2.hasVPLim_repF0`, `hasVPLim_repF1` this gives the transverse form
(`exists_pol_F`).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit QED.TwoLoop.LimitCovariance
open QED.WickModel (Params)

/-- The contraction `k_μ (k² g^{μν} - k^μ k^ν) = 0`. -/
theorem sum_lower_vpT (k : Fin 4 → ℝ) (ν : Fin 4) :
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * vpT k μ ν = 0 := by
  simp only [vpT]
  rw [← Complex.ofReal_zero]
  push_cast
  simp only [Minkowski.lower, Minkowski.dot, Minkowski.metric, Fin.sum_univ_four]
  fin_cases ν <;> simp
  all_goals ring

/-- `κ_F = -e² (2π)⁻⁴`, the constant of the bubble with the opposite sign. -/
theorem kF_eq (e : ℝ) :
    kF e = -((I * e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) := by
  simp only [kF]
  have hI : I ≠ 0 := I_ne_zero
  field_simp

theorem bubbleW_eq (e M ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    bubbleW e M ε k q μ ν = ((I * e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) *
      wfB ν μ M ε (zk k true q) (zk k false q) := by
  simp only [bubbleW, wfB, zk, ite_true, Bool.false_eq_true, ite_false]
  rw [add_comm q k,
    show QED.OneLoop.electronPropagator M ε (k + q) =
      (propDenom M ε (k + q))⁻¹ • electronNumerator M (k + q) from rfl,
    show QED.OneLoop.electronPropagator M ε q = (propDenom M ε q)⁻¹ • electronNumerator M q
      from rfl]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Matrix.trace_mul_comm _ (Dirac.gamma ν)]
  simp only [Matrix.mul_assoc]
  ring

section Block

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (rep : F → F) (ν : Fin 4)

/-- The block sum of `T`. -/
noncomputable def fwT (ε : ℝ) (p : Fin 4 → ℝ) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (kF P.e * wfT ν (P.e ^ 2 * D.d₂ (rep f) 0) (P.e ^ 2 * D.dm (rep f) 0)
    (Φ.mass f) ε p)

/-- The coefficient `-e² δ₂` of the bubble term. -/
noncomputable def dB (r : F) : ℂ := -((P.e ^ 2 * D.d₂ r 0 : ℝ) : ℂ)

/-- The block-summed bubble of the bubble term. -/
noncomputable def fwB (μ : Fin 4) (ε : ℝ) (k q : Fin 4 → ℝ) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (dB P D (rep f) * bubbleW P.e (Φ.mass f) ε k q μ ν)

/-- The block sum of the remainder. -/
noncomputable def fwR (ε : ℝ) (k q : Fin 4 → ℝ) : ℂ :=
  (∑ f, (Φ.coeff f : ℂ) * (kF P.e * wfR (P.e ^ 2 * D.d₂ (rep f) 0) (P.e ^ 2 * D.dm (rep f) 0)
    (Φ.mass f) ε (zk k true q) (zk k false q))) +
  ∑ f, (Φ.coeff f : ℂ) * (kF P.e * wfR (P.e ^ 2 * D.d₂ (rep f) 0) (P.e ^ 2 * D.dm (rep f) 0)
    (Φ.mass f) ε (zk k false q) (zk k true q))

theorem traceT_one_one (μ : Fin 4) :
    traceT 1 1 ν μ = (Dirac.gamma ν * Dirac.gamma μ).trace := by
  simp only [traceT, Matrix.mul_one]

omit [DecidableEq F] in
/-- **The block-summed Ward identity of the inserted bubbles.** -/
theorem wardF_block {ε : ℝ} (hε : 0 < ε) (k q : Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * (fBubble P Φ D rep true true false ε k q μ ν +
        fBubble P Φ D rep false false true ε k q μ ν) =
      fwT P Φ D rep ν ε (zk k false q) - fwT P Φ D rep ν ε (zk k true q) +
        ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * fwB P Φ D rep ν μ ε k q +
        ((ε : ℂ) * I) * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
          (traceT 1 1 ν μ * fwR P Φ D rep ε k q) := by
  set lk : Fin 4 → ℂ := fun μ => ((Minkowski.lower k μ : ℝ) : ℂ) with hlk
  set cG := ∑ μ, lk μ * (Dirac.gamma ν * Dirac.gamma μ).trace with hcG
  have e1 : ∑ μ, lk μ * (fBubble P Φ D rep true true false ε k q μ ν +
      fBubble P Φ D rep false false true ε k q μ ν) =
      ∑ f, (Φ.coeff f : ℂ) * (kF P.e * ∑ μ, lk μ *
        (insG (gAF true μ ν) (gBF true μ ν) (P.e ^ 2 * D.d₂ (rep f) 0)
          (P.e ^ 2 * D.dm (rep f) 0) (Φ.mass f) ε (zk k true q) (zk k false q) +
         insG (gAF false μ ν) (gBF false μ ν) (P.e ^ 2 * D.d₂ (rep f) 0)
          (P.e ^ 2 * D.dm (rep f) 0) (Φ.mass f) ε (zk k false q) (zk k true q))) := by
    simp only [fBubble, ← Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun μ _ => by ring
  have hB : ∑ μ, lk μ * fwB P Φ D rep ν μ ε k q = ∑ f, (Φ.coeff f : ℂ) *
      (kF P.e * (((P.e ^ 2 * D.d₂ (rep f) 0 : ℝ) : ℂ) *
        ∑ μ, lk μ * wfB ν μ (Φ.mass f) ε (zk k true q) (zk k false q))) := by
    simp only [fwB, bubbleW_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [kF_eq, dB]
    ring
  have hR : ∑ μ, lk μ * (traceT 1 1 ν μ * fwR P Φ D rep ε k q) = cG * fwR P Φ D rep ε k q := by
    rw [hcG, Finset.sum_mul]
    exact Finset.sum_congr rfl fun μ _ => by rw [traceT_one_one]; ring
  rw [e1, hB, hR]
  have hf : ∀ f, (Φ.coeff f : ℂ) * (kF P.e * ∑ μ, lk μ *
        (insG (gAF true μ ν) (gBF true μ ν) (P.e ^ 2 * D.d₂ (rep f) 0)
          (P.e ^ 2 * D.dm (rep f) 0) (Φ.mass f) ε (zk k true q) (zk k false q) +
         insG (gAF false μ ν) (gBF false μ ν) (P.e ^ 2 * D.d₂ (rep f) 0)
          (P.e ^ 2 * D.dm (rep f) 0) (Φ.mass f) ε (zk k false q) (zk k true q))) =
      (Φ.coeff f : ℂ) * (kF P.e * wfT ν (P.e ^ 2 * D.d₂ (rep f) 0) (P.e ^ 2 * D.dm (rep f) 0)
          (Φ.mass f) ε (zk k false q)) -
        (Φ.coeff f : ℂ) * (kF P.e * wfT ν (P.e ^ 2 * D.d₂ (rep f) 0)
          (P.e ^ 2 * D.dm (rep f) 0) (Φ.mass f) ε (zk k true q)) +
        (Φ.coeff f : ℂ) * (kF P.e * (((P.e ^ 2 * D.d₂ (rep f) 0 : ℝ) : ℂ) *
          ∑ μ, lk μ * wfB ν μ (Φ.mass f) ε (zk k true q) (zk k false q))) +
        ((ε : ℂ) * I * cG) * ((Φ.coeff f : ℂ) * (kF P.e * wfR (P.e ^ 2 * D.d₂ (rep f) 0)
            (P.e ^ 2 * D.dm (rep f) 0) (Φ.mass f) ε (zk k true q) (zk k false q)) +
          (Φ.coeff f : ℂ) * (kF P.e * wfR (P.e ^ 2 * D.d₂ (rep f) 0)
            (P.e ^ 2 * D.dm (rep f) 0) (Φ.mass f) ε (zk k false q) (zk k true q))) := by
    intro f
    rw [wardF_mass ν _ _ _ hε k q]
    ring
  rw [Finset.sum_congr rfl fun f _ => hf f, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
  simp only [fwT, fwR]
  ring

/-! ### Both stages at `ε > 0` -/

variable (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
include hm₀ hmass hrep hPV₁ hPV₂

theorem ef_fwT {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (b : Bool) :
    EF fun q => fwT P Φ D rep ν ε (zk k b q) := by
  have hz := isLoopAffine_zk k b
  have h0 : ∀ r : F, IsLoopPoly 2 3 fun ℓ => ((P.e ^ 2 * D.d₂ r 0 : ℝ) : ℂ) *
      (Dirac.gamma ν * (Dirac.slash (zk k b (ℓ 0)) * (Dirac.slash (zk k b (ℓ 0)) *
        Dirac.slash (zk k b (ℓ 0))))).trace := fun r =>
    (((IsLoopPolyMat.const _).mul ((isLoopPolyMat_slash' hz).mul ((isLoopPolyMat_slash' hz).mul
      (isLoopPolyMat_slash' hz)))).trace.const_mul _).mono (by norm_num)
  have h2 : ∀ r : F, IsLoopPoly 2 1 fun ℓ => (((P.e ^ 2 * D.d₂ r 0 : ℝ) : ℂ) -
      2 * ((P.e ^ 2 * D.dm r 0 : ℝ) : ℂ)) *
      (Dirac.gamma ν * Dirac.slash (zk k b (ℓ 0))).trace := fun r =>
    (((IsLoopPolyMat.const _).mul (isLoopPolyMat_slash' hz)).trace.const_mul _).mono
      (by norm_num)
  refine (ef_twoBlock Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂
    (fun r q => ((P.e ^ 2 * D.d₂ r 0 : ℝ) : ℂ) * (Dirac.gamma ν * (Dirac.slash (zk k b q) *
      (Dirac.slash (zk k b q) * Dirac.slash (zk k b q)))).trace)
    (fun r q => (((P.e ^ 2 * D.d₂ r 0 : ℝ) : ℂ) - 2 * ((P.e ^ 2 * D.dm r 0 : ℝ) : ℂ)) *
      (Dirac.gamma ν * Dirac.slash (zk k b q)).trace) h0 h2 hε k b b (kF P.e)).congr
    fun q => ?_
  simp only [fwT, wfT_eq]

theorem ef_fwB {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ : Fin 4) :
    EF fun q => fwB P Φ D rep ν μ ε k q := by
  have hx := isLoopAffine_zk k true
  have hy := isLoopAffine_zk k false
  have h0 : ∀ r : F, IsLoopPoly 2 3 fun ℓ => dB P D r *
      (Dirac.gamma ν * (Dirac.slash (zk k true (ℓ 0)) * (Dirac.gamma μ *
        Dirac.slash (zk k false (ℓ 0))))).trace := fun r =>
    (((IsLoopPolyMat.const _).mul ((isLoopPolyMat_slash' hx).mul ((IsLoopPolyMat.const _).mul
      (isLoopPolyMat_slash' hy)))).trace.const_mul _).mono (by norm_num)
  have h2 : ∀ r : F, IsLoopPoly 2 1 fun _ => dB P D r *
      (Dirac.gamma ν * Dirac.gamma μ).trace := fun r =>
    (IsLoopPoly.const (n := 0) _).mono (by norm_num)
  refine (ef_twoBlock Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂
    (fun r q => dB P D r * (Dirac.gamma ν * (Dirac.slash (zk k true q) * (Dirac.gamma μ *
      Dirac.slash (zk k false q)))).trace)
    (fun r _ => dB P D r * (Dirac.gamma ν * Dirac.gamma μ).trace) h0 h2 hε k true false
    ((I * P.e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹)).congr fun q => ?_
  simp only [fwB, bubbleW_eq, wfB_eq, tw]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-- The remainder, times `Tr[γ^i γ^j]`, is a `VPF` family. -/
theorem vpf_fwR : VPF (m₀ + m₀) fun ε k q i j => traceT 1 1 i j * fwR P Φ D rep ε k q := by
  have h := (vpf_rBlock Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (fun r => P.e ^ 2 * D.d₂ r 0)
    (fun r => P.e ^ 2 * D.dm r 0) (kF P.e) true false).add
    (vpf_rBlock Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (fun r => P.e ^ 2 * D.d₂ r 0)
      (fun r => P.e ^ 2 * D.dm r 0) (kF P.e) false true)
  refine h.congr fun ε _ k q i j => ?_
  simp only [fwR]
  ring

omit hm₀ hmass hrep hPV₁ hPV₂ in
theorem efi_sum_lower (k : Fin 4 → ℝ) (G : Fin 4 → (Fin 4 → ℝ) → ℂ) (hG : ∀ μ, EF (G μ)) :
    QED.OneLoop.energyFirstIntegral (fun q => ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * G μ q) =
      ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * QED.OneLoop.energyFirstIntegral (G μ) := by
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_finsetSum _ _ fun μ _ =>
    ⟨((hG μ).const_mul _).1, ((hG μ).const_mul _).2⟩]
  exact Finset.sum_congr rfl fun μ _ =>
    QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul _ (G μ)

omit hm₀ hmass hrep hPV₁ hPV₂ in
theorem ef_sum_lower (k : Fin 4 → ℝ) (G : Fin 4 → (Fin 4 → ℝ) → ℂ) (hG : ∀ μ, EF (G μ)) :
    EF fun q => ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * G μ q :=
  EF.sum Finset.univ fun μ _ => (hG μ).const_mul _

/-- **The integrated Ward identity**: the `T` terms cancel by translation invariance. -/
theorem efi_wardF {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
        (QED.OneLoop.energyFirstIntegral (fun q => fBubble P Φ D rep true true false ε k q μ ν) +
          QED.OneLoop.energyFirstIntegral
            (fun q => fBubble P Φ D rep false false true ε k q μ ν)) =
      ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
          QED.OneLoop.energyFirstIntegral (fun q => fwB P Φ D rep ν μ ε k q) +
        ((ε : ℂ) * I) * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
          QED.OneLoop.energyFirstIntegral (fun q => traceT 1 1 ν μ * fwR P Φ D rep ε k q) := by
  have hF0 := fun μ => (vpf_fBubble P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ true true false).2
    ε hε k μ ν
  have hF1 := fun μ => (vpf_fBubble P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ false false true).2
    ε hε k μ ν
  have hT0 := ef_fwT P Φ D rep ν m₀ hm₀ hmass hrep hPV₁ hPV₂ hε k false
  have hT1 := (ef_fwT P Φ D rep ν m₀ hm₀ hmass hrep hPV₁ hPV₂ hε k true).const_mul (-1)
  have hB := ef_sum_lower k _ fun μ => ef_fwB P Φ D rep ν m₀ hm₀ hmass hrep hPV₁ hPV₂ hε k μ
  have hR := (ef_sum_lower k _ fun μ =>
    ((vpf_fwR P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂).2 ε hε k ν μ)).const_mul ((ε : ℂ) * I)
  have hL : ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
      (QED.OneLoop.energyFirstIntegral (fun q => fBubble P Φ D rep true true false ε k q μ ν) +
        QED.OneLoop.energyFirstIntegral (fun q => fBubble P Φ D rep false false true ε k q μ ν)) =
      QED.OneLoop.energyFirstIntegral fun q => ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
        (fBubble P Φ D rep true true false ε k q μ ν +
          fBubble P Φ D rep false false true ε k q μ ν) := by
    rw [efi_sum_lower k _ fun μ => (hF0 μ).add (hF1 μ)]
    exact Finset.sum_congr rfl fun μ _ => by rw [efi_add (hF0 μ) (hF1 μ)]
  have hpt : (fun q => ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
        (fBubble P Φ D rep true true false ε k q μ ν +
          fBubble P Φ D rep false false true ε k q μ ν)) =
      fun q => ((fwT P Φ D rep ν ε (zk k false q) + -1 * fwT P Φ D rep ν ε (zk k true q)) +
        ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * fwB P Φ D rep ν μ ε k q) +
        ((ε : ℂ) * I) * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
          (traceT 1 1 ν μ * fwR P Φ D rep ε k q) := by
    funext q
    rw [wardF_block P Φ D rep ν hε k q]
    ring
  have hshift : QED.OneLoop.energyFirstIntegral (fun q => fwT P Φ D rep ν ε (zk k true q)) =
      QED.OneLoop.energyFirstIntegral (fun q => fwT P Φ D rep ν ε (zk k false q)) := by
    simp only [zk, ite_true, Bool.false_eq_true, ite_false]
    simp_rw [add_comm k]
    exact QED.OneLoop.energyFirstIntegral_add_right_eq_self _ k
  rw [hL, hpt, efi_add ((hT0.add hT1).add hB) hR, efi_add (hT0.add hT1) hB, efi_add hT0 hT1,
    QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul,
    QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul, hshift,
    efi_sum_lower k _ fun μ => ef_fwB P Φ D rep ν m₀ hm₀ hmass hrep hPV₁ hPV₂ hε k μ,
    efi_sum_lower k _ fun μ => (vpf_fwR P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂).2 ε hε k ν μ]
  ring

end Block

end QED.GradedProof.VP2

end
