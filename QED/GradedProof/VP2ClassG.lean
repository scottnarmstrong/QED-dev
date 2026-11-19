/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2Loop
public import QED.GradedProof.SE2ClassC
public import QED.WickModel.VacuumPolarizationEnergyFirst

/-!
# The classes `G0`, `G1`: the one-loop bubble with a `δ₁` vertex

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 2: the class
obligations `ClassInt2 repG0` and `ClassInt2 repG1`. The representatives have a `gauge` vertex
`0` and a `gaugeCt` vertex `1` on a closed loop with the two electron lines `l0` (tail `1`, head
`0`) and `l1` (tail `0`, head `1`), and no internal photon. For each:

* the lines, their ends, the unique chord `l1` and an explicit conserved routing (`decide +kernel`):
  `l1` carries `ℓ`, `l0` carries `ℓ ± k`;
* the amplitude (G₃) at the constant flavouring `f` is `(ie)(i e³ d₁ f 0)(1/i)²` times the trace
  of the bubble (`g0_amplitude`, `g1_amplitude`);
* with the block hypotheses the flavour sum is `∑_f c_f e² d₁ (rep f) 0` times minus the
  one-loop vacuum-polarization integrand (62.12) of the three-flavour set
  `(M_f, X, Y)` with its Pauli–Villars coefficients (`VP2.sum_block_eq_sum_triple`), whose two
  stages are integrable (`QED.WickModel.VacuumPolarizationLimit.integrable_*`).
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Insertion
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂ Line FermionLine
  PhotonLine IsChord externalMomentum vacuumPolarizationIntegrand)

/-! ### Spinor sums around a loop of two vertices -/

section Loop2

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The spinor sum around a closed loop through two vertices** is a trace. -/
theorem sum_spinor_loop2 {x₁ x₂ : X} (h12 : x₁ ≠ x₂) (hX : ∀ x, x = x₁ ∨ x = x₂)
    (A B S T : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4,
      A (α x₁) (β x₁) * S (β x₁) (α x₂) * B (α x₂) (β x₂) * T (β x₂) (α x₁) =
      Matrix.trace (A * S * B * T) := by
  have hs := fun (g : (X → Fin 4) → ℂ) => SE2.sum_pi_two h12 hX g
  simp only [hs, h12.symm, ite_false, ite_true]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a1 _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a2 _ => ?_
  conv_rhs => rw [Finset.sum_comm]

end Loop2

/-- The external momenta (X₁₉) of a two-photon contraction. -/
theorem externalMomentum_zero_two {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 0 2 κ}
    (pOut pIn : Fin 0 → Fin 4 → ℝ) (kIn : Fin 2 → Fin 4 → ℝ) (v : Fin N) :
    externalMomentum C pOut pIn kIn v =
      (if ∃ a : Wick.PhotonSlot κ, a.1 = v ∧ C.1.2 (.inl 0) = .inr a then kIn 0 else 0) +
        (if ∃ a : Wick.PhotonSlot κ, a.1 = v ∧ C.1.2 (.inl 1) = .inr a then kIn 1 else 0) := by
  unfold externalMomentum
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_two, zero_add, sub_zero]

/-- The single-flavour bubble `(ie)² (1/i)² (2π)⁻⁴ Tr[S̃_M(ℓ + k) γ^μ S̃_M(ℓ) γ^ν]`. -/
noncomputable def bubbleW (e M ε : ℝ) (k ℓ : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  (I * e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
    Matrix.trace (QED.OneLoop.electronPropagator M ε (ℓ + k) * Dirac.gamma μ *
      QED.OneLoop.electronPropagator M ε ℓ * Dirac.gamma ν)

/-- The three-flavour parameters `(M, X, Y)` with their Pauli–Villars coefficients. -/
noncomputable def triParams (P : Params) (M X Y : ℝ) : Params :=
  { P with m := M, M₁ := X, M₂ := Y, c₁ := triA M X Y, c₂ := triB M X Y }

/-- The one-loop vacuum-polarization integrand of `triParams` is minus the three-flavour
combination of bubbles. -/
theorem vacuumPolarizationIntegrand_triParams (P : Params) (M X Y ε : ℝ) (k ℓ : Fin 4 → ℝ)
    (μ ν : Fin 4) :
    vacuumPolarizationIntegrand (triParams P M X Y) ε k ℓ μ ν =
      -(bubbleW P.e M ε k ℓ μ ν + (triA M X Y : ℂ) * bubbleW P.e X ε k ℓ μ ν +
        (triB M X Y : ℂ) * bubbleW P.e Y ε k ℓ μ ν) := by
  simp only [vacuumPolarizationIntegrand, bubbleW, Fin.sum_univ_three, triParams,
    QED.WickModel.Params.loopCoeff, QED.WickModel.Params.mass, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Complex.ofReal_one]
  ring

/-- **The two stages of the block-summed bubble are integrable.** For block data `d` and flavour
data with the block hypotheses, `∑_f c_f d (rep f) W(M_f)` is integrable in both stages of the
energy-first integral (D). -/
theorem energyFirst_blockBubble (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (d : F → ℂ) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
      ∑ f, (Φ.coeff f : ℂ) * (d (rep f) * bubbleW P.e (Φ.mass f) ε k (Fin.cons t v) μ ν)) ∧
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
      ∑ f, (Φ.coeff f : ℂ) * (d (rep f) * bubbleW P.e (Φ.mass f) ε k (Fin.cons t v) μ ν) := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set X : ℝ := 1 + ∑ g, Φ.mass g with hX
  have hlt : ∀ g, Φ.mass g < X := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    linarith
  have hXY : ∀ g, Φ.mass g < X + 1 := fun g => (hlt g).trans (by linarith)
  have hsplit : ∀ ℓ, ∑ f, (Φ.coeff f : ℂ) * (d (rep f) * bubbleW P.e (Φ.mass f) ε k ℓ μ ν) =
      ∑ f, (Φ.coeff f : ℂ) * (-d (rep f) *
        vacuumPolarizationIntegrand (triParams P (Φ.mass f) X (X + 1)) ε k ℓ μ ν) := fun ℓ => by
    rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
      (fun b M => d b * bubbleW P.e M ε k ℓ μ ν)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [vacuumPolarizationIntegrand_triParams]
    ring
  have hpv : ∀ f, 1 + (triParams P (Φ.mass f) X (X + 1)).c₁ +
      (triParams P (Φ.mass f) X (X + 1)).c₂ = 0 := fun f =>
    triA_triB_pv₁ _ _ _ (by nlinarith [hlt f, hpos f])
  have hpv₂ : ∀ f, (triParams P (Φ.mass f) X (X + 1)).m ^ 2 +
      (triParams P (Φ.mass f) X (X + 1)).c₁ * (triParams P (Φ.mass f) X (X + 1)).M₁ ^ 2 +
      (triParams P (Φ.mass f) X (X + 1)).c₂ * (triParams P (Φ.mass f) X (X + 1)).M₂ ^ 2 = 0 :=
    fun f => triA_triB_pv₂ _ _ _ (by nlinarith [hlt f, hpos f])
  have h1 : ∀ f (v : Fin 3 → ℝ), Integrable fun t : ℝ =>
      vacuumPolarizationIntegrand (triParams P (Φ.mass f) X (X + 1)) ε k (Fin.cons t v) μ ν :=
    fun f v => QED.WickModel.VacuumPolarizationLimit.integrable_vacuumPolarizationIntegrand_time
      hε _ k μ ν v
  have h2 : ∀ f, Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
      vacuumPolarizationIntegrand (triParams P (Φ.mass f) X (X + 1)) ε k (Fin.cons t v) μ ν :=
    fun f => QED.WickModel.VacuumPolarizationLimit.integrable_integral_vacuumPolarizationIntegrand
      (P := triParams P (Φ.mass f) X (X + 1)) (hpos f) (hlt f) (hXY f) (hpv f) (hpv₂ f) hε k μ ν
  simp only [hsplit]
  refine ⟨fun v => integrable_finsetSum _ fun f _ => ((h1 f v).const_mul _).const_mul _, ?_⟩
  have hint : ∀ v : Fin 3 → ℝ, (∫ t : ℝ, ∑ f, (Φ.coeff f : ℂ) * (-d (rep f) *
      vacuumPolarizationIntegrand (triParams P (Φ.mass f) X (X + 1)) ε k (Fin.cons t v) μ ν)) =
      ∑ f, (Φ.coeff f : ℂ) * (-d (rep f) * ∫ t : ℝ,
        vacuumPolarizationIntegrand (triParams P (Φ.mass f) X (X + 1)) ε k (Fin.cons t v) μ ν) :=
    fun v => by
      rw [integral_finsetSum _ fun f _ => ((h1 f v).const_mul _).const_mul _]
      simp only [integral_const_mul]
  simp only [hint]
  exact integrable_finsetSum _ fun f _ => ((h2 f).const_mul _).const_mul _

end QED.GradedProof.VP2

end
