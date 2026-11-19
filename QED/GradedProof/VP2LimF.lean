/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2FTriple
public import QED.GradedProof.VP2LimG
public import QED.GradedProof.VP2ClassF

/-!
# The classes `F0`, `F1`: a covariant, null-continuous limit

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. The value of
`repF0` (`repF1`) is the energy-first integral of the block-summed inserted bubble
(`val0_repF0`, `val0_repF1`); by the block hypotheses it is a sum over flavours of three-flavour
Pauli–Villars sets (`QED.GradedProof.VP2.sum_block_eq_sum_triple`), each of which has a covariant,
null-continuous limit below `-(2 m₀)²` (`vpf_insTriple`). Hence (`hasVPLim_repF0`,
`hasVPLim_repF1`) the values have such limits (`HasVPLim`); transversality is a separate (Ward)
step.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Insertion
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂ Line IsChord)
open QED.TwoLoop.Bridge

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (rep : F → F)

/-- The block-summed inserted bubble of `F0` (`sw = true`, `x = k + q`, `y = q`) and `F1`
(`sw = false`, `x = q`, `y = k + q`). -/
noncomputable def fBubble (sw bx bY : Bool) (ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (kF P.e * insG (gAF sw μ ν) (gBF sw μ ν) (P.e ^ 2 * D.d₂ (rep f) 0)
    (P.e ^ 2 * D.dm (rep f) 0) (Φ.mass f) ε (zk k bx q) (zk k bY q))

theorem val0_repF0 (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    val0 P Φ D k μ ν repF0 =
      QED.OneLoop.energyFirstIntegral fun q => fBubble P Φ D rep true true false P.ε k q μ ν :=
  contractionValue_of_one_chord P Φ D 0 f0_isChord_iff (f0Mom k) (f0_isConserved k)
    (fun ℓ => (f0Mom_apply k ℓ).1) ![] ![] ![μ, ν] _ 0
    (fun ℓ => (f0_integrand P Φ D rep hD k ℓ μ ν).trans (by rw [sub_zero]; rfl))

theorem val0_repF1 (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    val0 P Φ D k μ ν repF1 =
      QED.OneLoop.energyFirstIntegral fun q => fBubble P Φ D rep false false true P.ε k q μ ν :=
  contractionValue_of_one_chord P Φ D 0 f1_isChord_iff (f1Mom k) (f1_isConserved k)
    (fun ℓ => (f1Mom_apply k ℓ).1) ![] ![] ![μ, ν] _ 0
    (fun ℓ => (f1_integrand P Φ D rep hD k ℓ μ ν).trans (by rw [sub_zero]; rfl))

/-- **The block-summed inserted bubble has a covariant, null-continuous limit.** -/
theorem vpf_fBubble (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (sw bx bY : Bool) :
    VPF (m₀ + m₀) fun ε k q μ ν => fBubble P Φ D rep sw bx bY ε k q μ ν := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set X : ℝ := auxX Φ with hX
  have hlt : ∀ g, Φ.mass g < X := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    simp only [hX, auxX]
    linarith
  have hX0 : 0 < X := by
    have := Finset.sum_nonneg (s := Finset.univ) fun g (_ : g ∈ Finset.univ) => (hpos g).le
    simp only [hX, auxX]
    linarith
  have hXY : X ^ 2 - (X + 1) ^ 2 ≠ 0 := by nlinarith
  refine (VPF.sum Finset.univ (fun f _ => (vpf_insTriple hm₀ sw (P.e ^ 2 * D.d₂ (rep f) 0)
    (P.e ^ 2 * D.dm (rep f) 0) bx bY (Φ.mass f) X (X + 1) (hmass f)
    (by linarith [hlt f, hmass f]) (by linarith [hlt f, hmass f]) hXY).const_mul
      ((Φ.coeff f : ℂ) * kF P.e)) (by nlinarith)).congr fun ε _ k q μ ν => ?_
  simp only [fBubble]
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1) (fun r M => kF P.e *
    insG (gAF sw μ ν) (gBF sw μ ν) (P.e ^ 2 * D.d₂ r 0) (P.e ^ 2 * D.dm r 0) M ε (zk k bx q)
      (zk k bY q))]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-- **The class `F0` has a covariant, null-continuous limit.** -/
theorem hasVPLim_repF0 (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) :
    HasVPLim (m₀ + m₀) fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν repF0 :=
  (vpf_fBubble P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ true true false).hasVPLim.congr
    fun k _ μ ν => Eventually.of_forall fun ε =>
      (val0_repF0 { P with ε := ε } Φ D rep hD k μ ν).symm

/-- **The class `F1` has a covariant, null-continuous limit.** -/
theorem hasVPLim_repF1 (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) :
    HasVPLim (m₀ + m₀) fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν repF1 :=
  (vpf_fBubble P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ false false true).hasVPLim.congr
    fun k _ μ ν => Eventually.of_forall fun ε =>
      (val0_repF1 { P with ε := ε } Φ D rep hD k μ ν).symm

end QED.GradedProof.VP2

end
