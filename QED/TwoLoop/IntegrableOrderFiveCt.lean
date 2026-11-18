/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.IntegrableOrderFiveTransfer
public import QED.TwoLoop.CountertermLimit
public import QED.TwoLoop.CountertermInsertionD1
public import QED.TwoLoop.CountertermInsertionD2
public import QED.TwoLoop.CountertermInsertionD3
public import QED.OneLoop.VertexOffShellIntegrable
public import QED.Integration.TwoLoopRefinedBoundFubini

/-!
# (T₉′) for the seven counterterm classes of the order-`e⁵` vertex

Part of (HV₀) (obligation O2-7, decision D-44 item 2). For each of the seven counterterm class
representatives `c.rep` (`QED.TwoLoop.Relabel.CtClass`: `δ₂, δ_m` on either internal electron
line, `δ₃` on the internal photon with either slot pairing, `δ₁` at each of the three vertices),
every `ε > 0`, all masses and cutoffs, and momentum conservation, the integrand of the value (T₁₀)
in the frozen routing (T₄) satisfies (T₉′) (`jointEnergyFirstIntegrable_ctClass`).

## Proof

* Each representative has one chord, so one loop (`loopCount_eq_one_of_unique`), and its frozen
  line momenta are the explicit conserved routing of `QED/TwoLoop/CountertermInsertionD*.lean`
  (`lineMomentum₂_eq_of_unique`). In that routing the integrand is, pointwise, the one-loop
  integrand of the insertion identities shifted by an external momentum (`integrand_d2In`, …;
  the computations of `contractionValue₂_repD2In`, …, without the integral).
* **`δ₁`**: the one-loop integrand is `δ₁` times the regulated one-loop vertex integrand (C),
  whose two stages are integrable at `ε > 0` for all momenta and masses
  (`QED.OneLoop.VertexOffShell.integrable_energyFirst_of_pos`).
* **`δ₂, δ_m`, `δ₃`**: the one-loop integrand times an auxiliary loop `(ℓ₁² + m² - iε)⁻³` is a
  two-loop integrand with a polynomial numerator of degree at most four and eight (`δ₂`),
  resp. nine (`δ₃`), propagators (`QED.TwoLoop.CountertermLimit.integrand_d2In_eq`, …, the line
  kinds `kindsD2In`, `kindsD2Out`, `kindsD3`). The numerator-aware criterion holds (decided) and
  the numerator bound is `refinedBound_of_dependsOnZero`, so the two-loop criterion
  `jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined` gives (T₉′) of the
  product at any masses, and the factor `F` is recovered
  (`energyFirst_of_jointEnergyFirstIntegrable_mul_aux`).
* (T₉′) of the shifted one-loop integrand with one loop momentum is
  `jointEnergyFirstIntegrable_one_sub`.
-/

public section

open MeasureTheory Complex

namespace QED.TwoLoop.IntegrableOrderFive

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Relabel
  QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.Integration.TwoLoop (lineDenom castLoopMatrix RefinedBound IntNoSubdivergenceRefined
  noSubdivergenceRefined_castLoopMatrix_iff
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined)

/-! ### One chord -/

section OneChord

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

open scoped Classical in
/-- With exactly one chord `c` and a conserved routing `mom` giving `c` the loop momentum, the
frozen line momenta (T₄) are `mom (ℓ 0)`. -/
theorem lineMomentum₂_eq_of_unique {nf : ℕ} {C : Contraction nf nA κ} {c : Line C}
    (hc : ∀ g, IsChord g ↔ g = c) {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (mom : (Fin 4 → ℝ) → Line C → Fin 4 → ℝ) (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (mom ℓ))
    (hchord : ∀ ℓ, mom ℓ c = ℓ) (ℓ : Fin 1 → Fin 4 → ℝ) :
    lineMomentum₂ C pOut pIn kIn ℓ = mom (ℓ 0) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (hcons (ℓ 0)) (fun g hg => ?_) f).symm
  rw [(hc g).mp hg, hchord, chordMomentum_of_unique hc]

/-- **(T₉′) for a contraction with one chord**, from a pointwise identity of its integrand in a
conserved routing with a shifted one-loop integrand `G` whose two stages are integrable. -/
theorem jointEnergyFirstIntegrable_of_one_chord (P : Params) {nf : ℕ} {C : Contraction nf nA κ}
    {c : Line C} (hc : ∀ g, IsChord g ↔ g = c) {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} (mom : (Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (mom ℓ)) (hchord : ∀ ℓ, mom ℓ c = ℓ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) (G : (Fin 4 → ℝ) → ℂ) (s : Fin 4 → ℝ)
    (hpt : ∀ ℓ, (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (mom ℓ) αOut βIn μ = G (ℓ - s))
    (h₁ : ∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => G (Fin.cons t v))
    (h₂ : Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, G (Fin.cons t v)) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  rw [loopCount_eq_one_of_unique hc]
  have hfun : (fun ℓ : Fin 1 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 1) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) =
      fun ℓ => G (ℓ 0 - s) := by
    funext ℓ
    rw [lineMomentum₂_eq_of_unique hc mom hcons hchord, mul_one, hpt]
  rw [hfun]
  exact jointEnergyFirstIntegrable_one_sub h₁ h₂ s

end OneChord

/-! ### One-loop integrability through product data -/

/-- **Both stages of the energy-first integral of a one-loop integrand given by line kinds**:
if `N(ℓ₀) ∏ᵢ Dᵢ⁻¹ = F(ℓ₀) (ℓ₁² + M² - iε)⁻³` for product data given by kinds with at least eight
lines, the numerator lines `{0, 1, 2, 3}` and the refined criterion, then both stages of the
energy-first integral (D) of `F` converge absolutely at `ε > 0`, for all masses. -/
theorem energyFirst_of_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) (mass : ℝ) {ε : ℝ} (hε : 0 < ε) (p p' : Fin 4 → ℝ)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → ℂ) (hN : IsLoopPoly 2 4 fun ℓ => N (ℓ 0)) (F : (Fin 4 → ℝ) → ℂ)
    (hfac : ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      N (ℓ 0) * ∏ i, (propDenom (Ms i) ε ((κ i).lineMom p p' ℓ))⁻¹ =
        F (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => F (Fin.cons t v)) ∧
      Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v) := by
  obtain ⟨Q, hQ⟩ := hN.exists_loopQuartic
  have hα : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))),
      (castLoopMatrix fun i => (κ i).dir) e = ![1, 0] := by
    intro e he
    have h := hE e he
    funext s
    rcases hk : κ e with _ | _ | _ | _
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · exact absurd hk h
  have hB : RefinedBound (castLoopMatrix fun i => (κ i).dir) {0, 1, 2, 3} 4 Q.eval :=
    refinedBound_of_dependsOnZero _ hcard hα Q fun ℓ => by simp only [hQ, Matrix.cons_val_zero]
  have hJ := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined Q
    (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p') Ms hm7 hε
    ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit) hB
  refine energyFirst_of_jointEnergyFirstIntegrable_mul_aux mass hε ?_
  have hfun : (fun ℓ : Fin 2 → Fin 4 → ℝ => Q.eval ℓ * ∏ i,
      (lineDenom (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p') Ms ε i ℓ)⁻¹) =
      fun ℓ => F (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3 := by
    funext ℓ
    rw [hQ, prod_lineDenom_kinds]
    exact hfac ℓ
  rwa [hfun] at hJ

/-! ### The one-loop integrands -/

section Integrands

variable (P : Params) (hε : 0 < P.ε) (pOut pIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
include hε

/-- Both stages for the one-loop integrand of `δ₂, δ_m` on the incoming line. -/
theorem energyFirst_d2In :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
      vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + Fin.cons t v))
        (electronInsertion P.m P.ε P.δ₂ P.δm (pIn 0 + Fin.cons t v))
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (Fin.cons t v)) (αOut 0) (βIn 0)) ∧
      Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
        vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + Fin.cons t v))
          (electronInsertion P.m P.ε P.δ₂ P.δm (pIn 0 + Fin.cons t v))
          (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (Fin.cons t v)) (αOut 0) (βIn 0) :=
  energyFirst_of_kinds (by norm_num) kindsD2In (massesD2In P) P.m hε (pIn 0) (pOut 0)
    (by decide) (by decide) (by decide)
    (fun k => numD2In P (pOut 0) (pIn 0) (μ 0) k (αOut 0) (βIn 0))
    (isLoopPoly_numD2In P _ _ _ _ _)
    (fun k => vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + k))
      (electronInsertion P.m P.ε P.δ₂ P.δm (pIn 0 + k))
      (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k) (αOut 0) (βIn 0))
    (fun ℓ => by
      rw [integrand_d2In_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD2In, massesD2In,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)

/-- Both stages for the one-loop integrand of `δ₂, δ_m` on the outgoing line. -/
theorem energyFirst_d2Out :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
      vertexChain P.e (μ 0) (electronInsertion P.m P.ε P.δ₂ P.δm (pOut 0 + Fin.cons t v))
        (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + Fin.cons t v))
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (Fin.cons t v)) (αOut 0) (βIn 0)) ∧
      Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
        vertexChain P.e (μ 0) (electronInsertion P.m P.ε P.δ₂ P.δm (pOut 0 + Fin.cons t v))
          (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + Fin.cons t v))
          (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (Fin.cons t v)) (αOut 0) (βIn 0) :=
  energyFirst_of_kinds (by norm_num) kindsD2Out (massesD2In P) P.m hε (pIn 0) (pOut 0)
    (by decide) (by decide) (by decide)
    (fun k => numD2Out P (pOut 0) (pIn 0) (μ 0) k (αOut 0) (βIn 0))
    (isLoopPoly_numD2Out P _ _ _ _ _)
    (fun k => vertexChain P.e (μ 0) (electronInsertion P.m P.ε P.δ₂ P.δm (pOut 0 + k))
      (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + k))
      (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k) (αOut 0) (βIn 0))
    (fun ℓ => by
      rw [integrand_d2Out_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD2Out, massesD2In,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)

/-- Both stages for the one-loop integrand of `δ₃` (either slot pairing). -/
theorem energyFirst_d3 :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
      vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + Fin.cons t v))
        (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + Fin.cons t v))
        (photonInsertion P.δ₃ P.mγ P.Λ P.ε (Fin.cons t v)) (αOut 0) (βIn 0)) ∧
      Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
        vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + Fin.cons t v))
          (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + Fin.cons t v))
          (photonInsertion P.δ₃ P.mγ P.Λ P.ε (Fin.cons t v)) (αOut 0) (βIn 0) :=
  energyFirst_of_kinds (by norm_num) kindsD3 (massesD3 P) P.m hε (pIn 0) (pOut 0)
    (by decide) (by decide) (by decide)
    (fun k => numD3 P (pOut 0) (pIn 0) (μ 0) k (αOut 0) (βIn 0))
    (isLoopPoly_numD3 P _ _ _ _ _)
    (fun k => vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + k))
      (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + k))
      (photonInsertion P.δ₃ P.mγ P.Λ P.ε k) (αOut 0) (βIn 0))
    (fun ℓ => by
      rw [integrand_d3_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD3, massesD3,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)

/-- Both stages for `δ₁` times the one-loop vertex integrand (C). -/
theorem energyFirst_d1 :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => (P.δ₁ : ℂ) *
      QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε (pOut 0) (pIn 0) (μ 0) (Fin.cons t v)
        (αOut 0) (βIn 0)) ∧
      Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, (P.δ₁ : ℂ) *
        QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε (pOut 0) (pIn 0) (μ 0) (Fin.cons t v)
          (αOut 0) (βIn 0) := by
  obtain ⟨h₁, h₂⟩ := QED.OneLoop.VertexOffShell.integrable_energyFirst_of_pos hε P.e P.m P.mγ P.Λ
    (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)
  refine ⟨fun v => (h₁ v).const_mul _, ?_⟩
  simp only [integral_const_mul]
  exact h₂.const_mul _

end Integrands

/-! ### The pointwise identities in the conserved routing -/

section Pointwise

variable (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
  (αOut βIn μ : Fin 1 → Fin 4)
include hmom

theorem integrand_d1At1 (ℓ : Fin 4 → ℝ) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repD1At1 pIn kIn (d1c1Mom (pIn 0) (kIn 0) ℓ) αOut βIn μ =
      (P.δ₁ : ℂ) * QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε (pOut 0) (pIn 0) (μ 0)
        (ℓ - pIn 0) (αOut 0) (βIn 0) := by
  obtain ⟨m1, m2, m3⟩ := d1c1Mom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 4) (by decide +kernel)),
    d1c1_amplitude, m1, m2, m3, QED.OneLoop.vertexIntegrand, hmom,
    show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [photonPropagator_comm']
  push_cast
  ring

theorem integrand_d1At2 (ℓ : Fin 4 → ℝ) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repD1At2 pIn kIn (d1c2Mom (pIn 0) (kIn 0) ℓ) αOut βIn μ =
      (P.δ₁ : ℂ) * QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε (pOut 0) (pIn 0) (μ 0)
        (ℓ - (pIn 0 + kIn 0)) (αOut 0) (βIn 0) := by
  obtain ⟨m1, m2, m3⟩ := d1c2Mom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 4) (by decide +kernel)),
    d1c2_amplitude, m1, m2, m3, QED.OneLoop.vertexIntegrand, hmom,
    show pIn 0 + kIn 0 - ℓ = -(ℓ - (pIn 0 + kIn 0)) by abel,
    show pIn 0 + kIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ by abel,
    show pIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ - kIn 0 by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

theorem integrand_d1At3 (ℓ : Fin 4 → ℝ) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repD1At3 pIn kIn (d1c3Mom (pIn 0) (kIn 0) ℓ) αOut βIn μ =
      (P.δ₁ : ℂ) * QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε (pOut 0) (pIn 0) (μ 0)
        (ℓ - pIn 0) (αOut 0) (βIn 0) := by
  obtain ⟨m1, m2, m3⟩ := d1c3Mom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 4) (by decide +kernel)),
    d1c3_amplitude, m1, m2, m3, QED.OneLoop.vertexIntegrand, hmom,
    show pIn 0 - ℓ = -(ℓ - pIn 0) by abel, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

theorem integrand_d2In (ℓ : Fin 4 → ℝ) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repD2In pIn kIn (d2iMom (pIn 0) (kIn 0) ℓ) αOut βIn μ =
      vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + (ℓ - pIn 0)))
        (electronInsertion P.m P.ε P.δ₂ P.δm (pIn 0 + (ℓ - pIn 0)))
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - pIn 0)) (αOut 0) (βIn 0) := by
  obtain ⟨m1, m2, m3, m4⟩ := d2iMom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 5) (by decide +kernel)),
    d2i_amplitude, m1, m2, m3, m4, vertexChain, electronInsertion, hmom,
    show pIn 0 - ℓ = -(ℓ - pIn 0) by abel, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_assoc]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  field_simp

theorem integrand_d2Out (ℓ : Fin 4 → ℝ) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repD2Out pIn kIn (d2oMom (pIn 0) (kIn 0) ℓ) αOut βIn μ =
      vertexChain P.e (μ 0) (electronInsertion P.m P.ε P.δ₂ P.δm (pOut 0 + (ℓ - pIn 0)))
        (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + (ℓ - pIn 0)))
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - pIn 0)) (αOut 0) (βIn 0) := by
  obtain ⟨m1, m2, m3, m4⟩ := d2oMom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 5) (by decide +kernel)),
    d2o_amplitude, m1, m2, m3, m4, vertexChain, electronInsertion, hmom,
    show pIn 0 - ℓ = -(ℓ - pIn 0) by abel, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_assoc]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  field_simp

theorem integrand_d3Slot0 (ℓ : Fin 4 → ℝ) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repD3Slot0 pIn kIn (d3s0Mom (pIn 0) (kIn 0) ℓ) αOut βIn μ =
      vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + (ℓ - pIn 0)))
        (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + (ℓ - pIn 0)))
        (photonInsertion P.δ₃ P.mγ P.Λ P.ε (ℓ - pIn 0)) (αOut 0) (βIn 0) := by
  obtain ⟨m1, m2, m3, m4⟩ := d3s0Mom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 4) (by decide +kernel)),
    d3s0_amplitude, m1, m2, m3, m4, vertexChain, hmom,
    show pIn 0 - ℓ = -(ℓ - pIn 0) by abel, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [photonPropagator_neg', photonCtFactor_neg, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Finset.mul_sum, photonInsertion]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem integrand_d3Slot1 (ℓ : Fin 4 → ℝ) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repD3Slot1 pIn kIn (d3s1Mom (pIn 0) (kIn 0) ℓ) αOut βIn μ =
      vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + (ℓ - pIn 0)))
        (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + (ℓ - pIn 0)))
        (photonInsertion P.δ₃ P.mγ P.Λ P.ε (ℓ - pIn 0)) (αOut 0) (βIn 0) := by
  obtain ⟨m1, m2, m3, m4⟩ := d3s1Mom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 4) (by decide +kernel)),
    d3s1_amplitude, m1, m2, m3, m4, vertexChain, hmom,
    show pIn 0 - ℓ = -(ℓ - pIn 0) by abel, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Finset.mul_sum, photonInsertion]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm (f := fun x i => 1 / I *
    (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - pIn 0) _ i *
      photonCtFactor P.δ₃ (ℓ - pIn 0) x i *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - pIn 0) _ x))]
  simp only [photonCtFactor_comm P.δ₃ (ℓ - pIn 0) _ _]
  ring

end Pointwise

/-! ### The seven classes -/

section Classes

variable (P : Params) (hε : 0 < P.ε) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
  (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
include hε hmom

/-- **(T₉′) for every counterterm class representative** at `ε > 0`, for all masses, cutoffs and
counterterms, under momentum conservation. -/
theorem jointEnergyFirstIntegrable_ctClass (c : CtClass) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount c.rep) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount c.rep) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P c.rep pIn kIn (lineMomentum₂ c.rep pOut pIn kIn ℓ) αOut βIn μ := by
  cases c
  · obtain ⟨h₁, h₂⟩ := energyFirst_d2In P hε pOut pIn αOut βIn μ
    exact jointEnergyFirstIntegrable_of_one_chord P d2i_isChord_iff (d2iMom (pIn 0) (kIn 0))
      (d2i_isConserved hmom) (fun ℓ => (d2iMom_apply _ _ ℓ).2.1) αOut βIn μ
      (fun k => vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + k))
        (electronInsertion P.m P.ε P.δ₂ P.δm (pIn 0 + k))
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k) (αOut 0) (βIn 0)) (pIn 0)
      (integrand_d2In P hmom αOut βIn μ) h₁ h₂
  · obtain ⟨h₁, h₂⟩ := energyFirst_d2Out P hε pOut pIn αOut βIn μ
    exact jointEnergyFirstIntegrable_of_one_chord P d2o_isChord_iff (d2oMom (pIn 0) (kIn 0))
      (d2o_isConserved hmom) (fun ℓ => (d2oMom_apply _ _ ℓ).1) αOut βIn μ
      (fun k => vertexChain P.e (μ 0) (electronInsertion P.m P.ε P.δ₂ P.δm (pOut 0 + k))
        (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + k))
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k) (αOut 0) (βIn 0)) (pIn 0)
      (integrand_d2Out P hmom αOut βIn μ) h₁ h₂
  · obtain ⟨h₁, h₂⟩ := energyFirst_d3 P hε pOut pIn αOut βIn μ
    exact jointEnergyFirstIntegrable_of_one_chord P d3s0_isChord_iff (d3s0Mom (pIn 0) (kIn 0))
      (d3s0_isConserved hmom) (fun ℓ => (d3s0Mom_apply _ _ ℓ).1) αOut βIn μ
      (fun k => vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + k))
        (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + k))
        (photonInsertion P.δ₃ P.mγ P.Λ P.ε k) (αOut 0) (βIn 0)) (pIn 0)
      (integrand_d3Slot0 P hmom αOut βIn μ) h₁ h₂
  · obtain ⟨h₁, h₂⟩ := energyFirst_d3 P hε pOut pIn αOut βIn μ
    exact jointEnergyFirstIntegrable_of_one_chord P d3s1_isChord_iff (d3s1Mom (pIn 0) (kIn 0))
      (d3s1_isConserved hmom) (fun ℓ => (d3s1Mom_apply _ _ ℓ).1) αOut βIn μ
      (fun k => vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + k))
        (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + k))
        (photonInsertion P.δ₃ P.mγ P.Λ P.ε k) (αOut 0) (βIn 0)) (pIn 0)
      (integrand_d3Slot1 P hmom αOut βIn μ) h₁ h₂
  · obtain ⟨h₁, h₂⟩ := energyFirst_d1 P hε pOut pIn αOut βIn μ
    exact jointEnergyFirstIntegrable_of_one_chord P d1c1_isChord_iff (d1c1Mom (pIn 0) (kIn 0))
      (d1c1_isConserved hmom) (fun ℓ => (d1c1Mom_apply _ _ ℓ).1) αOut βIn μ
      (fun k => (P.δ₁ : ℂ) * QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε (pOut 0) (pIn 0)
        (μ 0) k (αOut 0) (βIn 0)) (pIn 0)
      (integrand_d1At1 P hmom αOut βIn μ) h₁ h₂
  · obtain ⟨h₁, h₂⟩ := energyFirst_d1 P hε pOut pIn αOut βIn μ
    exact jointEnergyFirstIntegrable_of_one_chord P d1c2_isChord_iff (d1c2Mom (pIn 0) (kIn 0))
      (d1c2_isConserved hmom) (fun ℓ => (d1c2Mom_apply _ _ ℓ).1) αOut βIn μ
      (fun k => (P.δ₁ : ℂ) * QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε (pOut 0) (pIn 0)
        (μ 0) k (αOut 0) (βIn 0)) (pIn 0 + kIn 0)
      (integrand_d1At2 P hmom αOut βIn μ) h₁ h₂
  · obtain ⟨h₁, h₂⟩ := energyFirst_d1 P hε pOut pIn αOut βIn μ
    exact jointEnergyFirstIntegrable_of_one_chord P d1c3_isChord_iff (d1c3Mom (pIn 0) (kIn 0))
      (d1c3_isConserved hmom) (fun ℓ => (d1c3Mom_apply _ _ ℓ).1) αOut βIn μ
      (fun k => (P.δ₁ : ℂ) * QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε (pOut 0) (pIn 0)
        (μ 0) k (αOut 0) (βIn 0)) (pIn 0)
      (integrand_d1At3 P hmom αOut βIn μ) h₁ h₂

end Classes

end QED.TwoLoop.IntegrableOrderFive

end
