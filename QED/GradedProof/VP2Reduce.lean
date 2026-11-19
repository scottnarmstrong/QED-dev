/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2Classes
public import QED.GradedProof.VP2Relabel
public import QED.GradedProof.SE2Reduce

/-!
# The integrability clause of (G-Π₂) from seven class obligations

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), steps 1–2. The first clause
of (G-Π₂) asserts (T₉′) for the integrand of every 1PI two-photon contraction `C` of graded order
exactly `4` at any grading `g`, for flavour data `Φ` with masses at least `m₀ > 0`, an idempotent
scheme map `rep` whose classes are Pauli–Villars blocks, and counterterm data `D` constant on the
blocks at level `0`. This file reduces it to the class obligation `ClassInt2` (the same (T₉′),
at grading `0`, under the same hypotheses `VPHyp`) for the seven representatives of
`QED/GradedProof/VP2Classes.lean`: `jointEnergyFirstIntegrable_of_classes2`.

## Proof

* **Nonzero grading.** A counterterm vertex of level `≥ 1` has graded order `≥ 4`, so the vertex
  orders sum to at most `2`; a counterterm vertex costs two orders
  (`QED.GradedProof.two_mul_loopCount_add_le_sum_order`), so `C` has no loop and (T₉′) is
  trivial (`QED.GradedProof.SE2.jointEnergyFirstIntegrable_zero`). This is the level-`1`
  `photonCt` tree.
* **Zero grading.** The vertex orders sum to `4`, so `C` is a relabelling of a representative
  (`induction_of_order_four2`), and the class obligation passes to relabellings at grading `0`
  (`jointEnergyFirstIntegrable_relabelK_graded`, with `gradMap π hκ 0 = 0` and momentum
  conservation `0 = 0 + (k + (-k))`).
-/

@[expose] public section

open Complex MeasureTheory
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Relabel

/-- **The standing hypotheses of (G-Π₂)**: masses at least `m₀ > 0`, positive photon regulators,
an idempotent scheme map `rep` whose classes satisfy the two Pauli–Villars conditions, and
level-`0` counterterm data constant on the classes. -/
structure VPHyp (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (m₀ : ℝ) : Prop where
  hm₀ : 0 < m₀
  hmass : ∀ g, m₀ ≤ Φ.mass g
  hmγ : 0 < P.mγ
  hΛ : 0 < P.Λ
  hrep : ∀ f, rep (rep f) = rep f
  hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0
  hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0
  hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
    D.dm f 0 = D.dm (rep f) 0

/-- **The class obligation**: (T₉′) for the integrand of a two-photon contraction at grading `0`,
at the two-photon kinematics `kIn = (k, -k)`, under the hypotheses of (G-Π₂). -/
def ClassInt2 {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 0 2 κ) : Prop :=
  ∀ (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (m₀ : ℝ), VPHyp P Φ D rep m₀ →
    ∀ ε > 0, ∀ (k : Fin 4 → ℝ) (μ ν : Fin 4),
      QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
        (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude { P with ε := ε } Φ D C 0 ![] ![k, -k]
            (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![] ![μ, ν]

/-- The class obligation passes to relabellings of 1PI contractions. -/
theorem classInt2_relabelK {N : ℕ} {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 0 2 κ) (hC : IsOnePI C) (h : ClassInt2 C) :
    ClassInt2 (relabelK π hκ C) := by
  intro P F _ _ Φ D rep m₀ hH ε hε k μ ν
  have := jointEnergyFirstIntegrable_relabelK_graded Φ { P with ε := ε } D π hκ hC 0
    (pOut := ![]) (pIn := ![]) (kIn := ![k, -k]) (by simp) ![] ![] ![μ, ν]
    (h P Φ D rep m₀ hH ε hε k μ ν)
  rwa [gradMap_zero] at this

/-- **The seven class obligations give (T₉′) for every 1PI two-photon contraction of total
order `4`.** -/
theorem classInt2_of_order_four (hVA : ClassInt2 repVA) (hVB : ClassInt2 repVB)
    (hVC : ClassInt2 repVC) (hG0 : ClassInt2 repG0) (hG1 : ClassInt2 repG1)
    (hF0 : ClassInt2 repF0) (hF1 : ClassInt2 repF1) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (h : ∑ t, (κ t).order = 4) (C : Contraction 0 2 κ) (hC : IsOnePI C) : ClassInt2 C :=
  induction_of_order_four2 (fun C => ClassInt2 C)
    (fun π hκ C hC h => classInt2_relabelK π hκ C hC h) hVA hVB hVC hG0 hG1 hF0 hF1 h C hC

/-- **The first clause of (G-Π₂) from the seven class obligations**, with exactly the hypotheses
and first conclusion of `QED.Graded.vacuumPolarizationPart_two_existsUnique`. -/
theorem jointEnergyFirstIntegrable_of_classes2 (hVA : ClassInt2 repVA) (hVB : ClassInt2 repVB)
    (hVC : ClassInt2 repVC) (hG0 : ClassInt2 repG0) (hG1 : ClassInt2 repG1)
    (hF0 : ClassInt2 repF0) (hF1 : ClassInt2 repF1) (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) :
    ∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = 4 →
      ∀ C : Contraction 0 2 κ, IsOnePI C → ∀ (k : Fin 4 → ℝ) (μ ν : Fin 4),
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude { P with ε := ε } Φ D C g ![] ![k, -k]
              (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![] ![μ, ν] := by
  intro ε hε N κ g hg C hC k μ ν
  by_cases hg0 : g = 0
  · subst hg0
    have h4 : ∑ t, (κ t).order = 4 := by rwa [gradedOrder_zero] at hg
    exact classInt2_of_order_four hVA hVB hVC hG0 hG1 hF0 hF1 h4 C hC P Φ D rep m₀
      ⟨hm₀, hmass, hmγ, hΛ, hrep, hPV₁, hPV₂, hD⟩ ε hε k μ ν
  · obtain ⟨t, ht⟩ : ∃ t : CtVertex κ, 1 ≤ g t := by
      obtain ⟨t, ht⟩ := Function.ne_iff.1 hg0
      exact ⟨t, Nat.one_le_iff_ne_zero.2 ht⟩
    have h2 := Finset.single_le_sum (f := fun t : CtVertex κ => 2 * g t)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have h4 := hg
    unfold gradedOrder at h4
    have hL := two_mul_loopCount_add_le_sum_order hC.1 hC.2.1 t.1 t.2
    have hL0 : loopCount C = 0 := by omega
    have key : ∀ (L : ℕ) (G : (Fin L → Fin 4 → ℝ) → ℂ), L = 0 →
        QED.TwoLoop.jointEnergyFirstIntegrable L G := by
      rintro L G rfl
      exact SE2.jointEnergyFirstIntegrable_zero G
    exact key _ _ hL0

end QED.GradedProof.VP2

end
