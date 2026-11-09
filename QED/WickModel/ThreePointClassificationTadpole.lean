/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassificationBasic
import QED.Algebra.Dirac
import QED.Integration.EnergyFirstShift

/-!
# Tadpoles vanish

A contraction may contract the `Ψ` of a vertex with the `Ψ̄` of the same vertex: a one-vertex
closed fermion loop, a tadpole. When this self-loop is the loop line of the canonical routing
(decision D-19) and the vertex is a gauge vertex, the contraction has value `0` at every `ε`,
whether or not its loop integrand is integrable.

The self-loop carries the loop momentum `ℓ`, and every other line carries a momentum independent
of `ℓ`: the loop momentum enters and leaves at the same vertex. The loop factor is the spinor
trace `Tr[γ^ν S̃_f(ℓ)]` (summed with the rest of the amplitude), and
`S̃_f(ℓ) + S̃_f(-ℓ) = 2 M_f (ℓ² + M_f² - iε)⁻¹ 1` is diagonal while `γ^ν` has zero diagonal in the
Weyl representation. So the amplitude of every flavoring is odd in `ℓ`, and the energy-first
integral of an odd function is `0` (its Bochner integrals are invariant under `ℓ ↦ -ℓ`).

## Main statements

* `QED.OneLoop.energyFirstIntegral_eq_zero_of_odd`: the energy-first integral of an odd function
  vanishes.
* `contractionAmplitude_add_neg_of_selfLoop`: the amplitude of a tadpole is odd in `ℓ`.
* `contractionValue_eq_zero_of_selfLoop`: a tadpole has value `0`.
-/

@[expose] public section

open Complex

namespace QED.OneLoop

/-- The energy-first integral commutes with negation, for every integrand. -/
theorem energyFirstIntegral_neg (F : (Fin 4 → ℝ) → ℂ) :
    energyFirstIntegral (fun ℓ => -F ℓ) = -energyFirstIntegral F := by
  unfold energyFirstIntegral
  simp only [MeasureTheory.integral_neg]

/-- **The energy-first integral of an odd function vanishes**, for every integrand: both Bochner
integrals are invariant under the reflection `ℓ ↦ -ℓ`. -/
theorem energyFirstIntegral_eq_zero_of_odd (F : (Fin 4 → ℝ) → ℂ) (hF : ∀ ℓ, F (-ℓ) = -F ℓ) :
    energyFirstIntegral F = 0 := by
  have h := energyFirstIntegral_neg_eq_self F
  simp only [hF, energyFirstIntegral_neg] at h
  linear_combination (-(1 / 2 : ℂ)) * h

/-- The sum of the electron propagators at `ℓ` and `-ℓ` is diagonal: its off-diagonal entries
vanish. -/
theorem electronPropagator_add_neg_apply_of_ne (M ε : ℝ) (ℓ : Fin 4 → ℝ) {i j : Fin 4}
    (hij : i ≠ j) : electronPropagator M ε ℓ i j + electronPropagator M ε (-ℓ) i j = 0 := by
  have hdot : Minkowski.dot (-ℓ) (-ℓ) = Minkowski.dot ℓ ℓ := by simp [Minkowski.dot]
  have hslash : Dirac.slash (-ℓ) = -Dirac.slash ℓ := by
    rw [← neg_one_smul ℝ ℓ, Dirac.slash_smul]
    simp
  simp only [electronPropagator, hdot, hslash, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.neg_apply, Matrix.one_apply_ne hij, smul_eq_mul]
  ring

end QED.OneLoop

namespace QED.WickModel

/-- The gamma matrices have zero diagonal in the Weyl representation. -/
theorem gamma_apply_self (ν i : Fin 4) : Dirac.gamma ν i i = 0 := by
  fin_cases ν <;> fin_cases i <;> rfl

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

/-- If the loop line is a self-loop, every other line carries a momentum independent of the loop
momentum: the loop momentum enters and leaves at the same vertex. -/
theorem lineMomentum_eq_of_selfLoop {l : Line C} (hl : IsLoopLine l) (hself : l.ends.1 = l.ends.2)
    {f : Line C} (hf : f ≠ l) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ ℓ' : Fin 4 → ℝ) :
    lineMomentum C pOut pIn kIn ℓ f = lineMomentum C pOut pIn kIn ℓ' f := by
  have hf' : ¬ IsLoopLine f := fun h => hf ((hl.isLoopLine_iff f).mp h)
  rw [lineMomentum, lineMomentum, ite_eq_right hf', ite_eq_right hf']
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [sum_isLoopLine_eq hl, sum_isLoopLine_eq hl, hself]
  simp

/-- With all vertices gauge vertices, the vertex factors do not depend on the momenta. -/
theorem prod_vertexFactor_of_forall_gauge (hκ : ∀ t, κ t = .gauge) (e δ₁ δ₂ δm δ₃ m : ℝ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ kψ' : Wick.FermionVertex κ → Fin 4 → ℝ) (kA kA' : Wick.PhotonSlot κ → Fin 4 → ℝ) :
    ∏ t, Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      ∏ t, Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ' kA' t :=
  Finset.prod_congr rfl fun t _ => by
    rw [vertexFactor_of_gauge _ _ _ _ _ _ _ _ _ _ _ (hκ t),
      vertexFactor_of_gauge _ _ _ _ _ _ _ _ _ _ _ (hκ t)]

/-- With all vertices gauge vertices, the vertex factors vanish when the two spinor indices of a
vertex agree. -/
theorem prod_vertexFactor_eq_zero (hκ : ∀ t, κ t = .gauge) (e δ₁ δ₂ δm δ₃ m : ℝ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ)
    {s : Wick.FermionVertex κ} (hs : β s = α s) :
    ∏ t, Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ s.1) ?_
  rw [vertexFactor_of_gauge _ _ _ _ _ _ _ _ _ _ _ (hκ s.1)]
  change I * e * Dirac.gamma _ (α s) (β s) = 0
  rw [hs, gamma_apply_self, mul_zero]

/-- **The amplitude of a tadpole is odd in the loop momentum.** If the loop line is a fermion line
`l` from a gauge vertex to itself (all vertices being gauge vertices), the amplitude of every
flavoring at `ℓ` and at `-ℓ` add to `0`. -/
theorem contractionAmplitude_add_neg_of_selfLoop (P : Params) (hκ : ∀ t, κ t = .gauge)
    {l : FermionLine C} (hl : IsLoopLine (.inl l : Line C)) (hself : l.tail = l.1)
    (φ : Flavoring κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude P C φ pOut pIn kIn ℓ αOut βIn μ +
      contractionAmplitude P C φ pOut pIn kIn (-ℓ) αOut βIn μ = 0 := by
  classical
  have hends : (Line.ends (.inl l : Line C)).1 = (Line.ends (.inl l : Line C)).2 := by
    change l.tail.1 = l.1.1
    rw [hself]
  have hm : ∀ (ℓ' : Fin 4 → ℝ) (g : Line C), g ≠ .inl l →
      lineMomentum C pOut pIn kIn ℓ' g = lineMomentum C pOut pIn kIn 0 g := fun ℓ' g hg =>
    lineMomentum_eq_of_selfLoop hl hends hg _ _ _ _ _
  have hloop : ∀ ℓ', lineMomentum C pOut pIn kIn ℓ' (.inl l) = ℓ' := fun ℓ' =>
    lineMomentum_of_isLoopLine hl _ _ _ _
  have hF : ∀ (ℓ' : Fin 4 → ℝ) (α β : Wick.FermionVertex κ → Fin 4),
      ∏ f : FermionLine C, (1 / I) *
          QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε
            (lineMomentum C pOut pIn kIn ℓ' (.inl f)) (β f.1) (α f.tail) =
        ((1 / I) * QED.OneLoop.electronPropagator (P.mass (φ.1 l.1)) P.ε ℓ' (β l.1) (α l.1)) *
          ∏ f ∈ Finset.univ.erase l, (1 / I) *
            QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε
              (lineMomentum C pOut pIn kIn 0 (.inl f)) (β f.1) (α f.tail) := by
    intro ℓ' α β
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l), hloop, hself]
    refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun f hf => ?_)
    rw [hm ℓ' (.inl f) fun h => (Finset.mem_erase.mp hf).1 (Sum.inl_injective h)]
  have hG : ∀ (ℓ' : Fin 4 → ℝ) (lor : Wick.PhotonSlot κ → Fin 4),
      ∏ g : PhotonLine C, (1 / I) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (lineMomentum C pOut pIn kIn ℓ' (.inr g))
            (lor g.1) (lor g.head) =
        ∏ g : PhotonLine C, (1 / I) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (lineMomentum C pOut pIn kIn 0 (.inr g))
            (lor g.1) (lor g.head) := fun ℓ' lor =>
    Finset.prod_congr rfl fun g _ => by rw [hm ℓ' (.inr g) Sum.inr_ne_inl]
  rw [contractionAmplitude, contractionAmplitude, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun β _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun lor _ => ?_
  rw [hF ℓ α β, hF (-ℓ) α β, hG ℓ lor, hG (-ℓ) lor,
    prod_vertexFactor_of_forall_gauge hκ _ _ _ _ _ _ α β lor
      (psiMomentum C pOut pIn kIn (-ℓ)) (psiMomentum C pOut pIn kIn ℓ)
      (photonMomentum C pOut pIn kIn (-ℓ)) (photonMomentum C pOut pIn kIn ℓ)]
  by_cases hs : β l.1 = α l.1
  · rw [prod_vertexFactor_eq_zero hκ _ _ _ _ _ _ α β lor _ _ hs]
    ring
  · have h0 := QED.OneLoop.electronPropagator_add_neg_apply_of_ne (P.mass (φ.1 l.1)) P.ε ℓ hs
    linear_combination
      (((if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
          (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
          (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
        (∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
          (psiMomentum C pOut pIn kIn ℓ) (photonMomentum C pOut pIn kIn ℓ) t) *
        (1 / I) *
        (∏ f ∈ Finset.univ.erase l, (1 / I) *
            QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε
              (lineMomentum C pOut pIn kIn 0 (.inl f)) (β f.1) (α f.tail)) *
        ∏ g : PhotonLine C, (1 / I) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (lineMomentum C pOut pIn kIn 0 (.inr g))
            (lor g.1) (lor g.head)) : ℂ) * h0

open scoped Classical in
/-- The regulated amplitude of a tadpole is odd in the loop momentum. -/
theorem regulatedAmplitude_neg_of_selfLoop (P : Params) (hκ : ∀ t, κ t = .gauge)
    {l : FermionLine C} (hl : IsLoopLine (.inl l : Line C)) (hself : l.tail = l.1)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P C pOut pIn kIn (-ℓ) αOut βIn μ =
      -regulatedAmplitude P C pOut pIn kIn ℓ αOut βIn μ := by
  rw [regulatedAmplitude, regulatedAmplitude, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [eq_neg_of_add_eq_zero_right
    (contractionAmplitude_add_neg_of_selfLoop P hκ hl hself φ pOut pIn kIn ℓ αOut βIn μ)]
  ring

/-- **A tadpole has value `0`**, at every `ε` and for all momenta: if the loop line is a fermion
line from a gauge vertex to itself (all vertices being gauge vertices), the loop integrand is odd
and its energy-first integral vanishes. -/
theorem contractionValue_eq_zero_of_selfLoop (P : Params) (hκ : ∀ t, κ t = .gauge)
    {l : FermionLine C} (hl : IsLoopLine (.inl l : Line C)) (hself : l.tail = l.1)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) : contractionValue P C pOut pIn kIn αOut βIn μ = 0 := by
  rw [contractionValue_of_isLoopLine P hl]
  refine QED.OneLoop.energyFirstIntegral_eq_zero_of_odd _ fun ℓ => ?_
  rw [regulatedAmplitude_neg_of_selfLoop P hκ hl hself]
  ring

end QED.WickModel

end
