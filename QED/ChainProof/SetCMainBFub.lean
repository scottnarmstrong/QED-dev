/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Set (c), the bubble classes: the two Fubini steps of the bubble at fixed `ε`

Helper level for set (c), the bubble classes `QED.ChainProof.SetCLink.repB i` (a two-loop
skeleton with the one-loop bubble on one photon line, three loops). At fixed `ε > 0` the value of
such a class is reduced to the transverse units of `QED/ChainProof/SetCUnitMDispEps.lean` in two
measure-theoretic steps, both proved here for a general integrand.

**Nested equals joint, inner bubble.** With the bubble momentum `ℓ 0 = q` and the two outer loop
momenta `ℓ' = (ℓ 1, ℓ 2)`, the joint energy-first integral (T₉) at three loops is the joint
energy-first integral at two loops of the one-loop energy-first integral (D) in `q`:

`∫ d⁹v ∫ d³t F = ∫ d⁶v' ∫ d²t' (∫ d³w ∫ dt₀ F)`.

* `bubbleT F t' v' w`: the energy integral in `t₀` at the outer energies `t'`, the outer spatial
  momenta `v'` and the bubble spatial momentum `w`;
* **`jointEnergyFirstIntegral_three_eq_inner`**: the two agree when both stages of (T₉) at three
  loops are integrable (`hF`) and, for almost every `v'`, `bubbleT F` is integrable jointly in
  `(t', w)` (`hK`, the Fubini condition: the bound of the bubble energy integral, polynomial in
  the photon momentum, against the decay of the outer factor in the outer energies);
* **`jointEnergyFirstIntegrable_inner`**: with `hK` at every `v'`, the outer integrand is
  integrable in both stages of (T₉) at two loops.

The energy `t₀` is always integrated first; `w` is exchanged only with the outer energies `t'`.

**The Feynman parameter of the bubble.** For a family `G x` of `L`-loop integrands indexed by a
parameter `x ∈ S` (the Feynman parameter of the bubble, `S = (0, 1)`):

* **`jointEnergyFirstIntegral_setIntegral`**: the joint energy-first integral of
  `ℓ ↦ ∫_S G x ℓ dx` is `∫_S` of the joint energy-first integrals, and the former integrand is
  integrable in both stages, when at every spatial `v` the integrand is integrable jointly in
  `(x, t)` (`h₁`) and the energy integrals are integrable jointly in `(x, v)` (`h₂`).
-/

@[expose] public section

open MeasureTheory

namespace QED.ChainProof.SetCMainB

/-! ### Splitting off the first loop momentum -/

section Split

variable {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)] {n : ℕ}

omit [MeasureSpace α] [SigmaFinite (volume : Measure α)] in
theorem insertNth_zero_eq_cons (a : α) (g : Fin n → α) :
    (Fin.insertNth 0 a g : Fin (n + 1) → α) = Fin.cons a g := by
  funext s
  refine Fin.cases ?_ (fun j => ?_) s
  · simp
  · simp only [Fin.cons_succ]
    exact Fin.insertNth_apply_succAbove (α := fun _ => α) 0 a g j

/-- An integral over `Fin (n + 1) → α` is an integral over `α × (Fin n → α)`, the first factor
being the entry `0`. -/
theorem integral_fin_cons (g : (Fin (n + 1) → α) → ℂ) :
    ∫ x, g x = ∫ p : α × (Fin n → α), g (Fin.cons p.1 p.2) := by
  rw [← (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm.integral_comp'
    (g := g)]
  congr 1
  funext p
  exact congrArg g (insertNth_zero_eq_cons p.1 p.2)

/-- Integrability over `Fin (n + 1) → α` is integrability over `α × (Fin n → α)`. -/
theorem integrable_fin_cons_iff (g : (Fin (n + 1) → α) → ℂ) :
    Integrable g ↔ Integrable fun p : α × (Fin n → α) => g (Fin.cons p.1 p.2) := by
  rw [← (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm.integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  refine integrable_congr (Filter.Eventually.of_forall fun p => ?_)
  exact congrArg g (insertNth_zero_eq_cons p.1 p.2)

end Split

/-! ### Nested equals joint, inner bubble -/

/-- The family of three loop momenta with energies `cons t₀ t'` and spatial momenta
`cons w v'`. -/
theorem cons_cons (t₀ : ℝ) (t' : Fin 2 → ℝ) (w : Fin 3 → ℝ) (v' : Fin 2 → Fin 3 → ℝ) :
    (fun s => (Fin.cons ((Fin.cons t₀ t' : Fin 3 → ℝ) s)
      ((Fin.cons w v' : Fin 3 → Fin 3 → ℝ) s) : Fin 4 → ℝ)) =
      Fin.cons (Fin.cons t₀ w : Fin 4 → ℝ) fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ) := by
  funext s
  refine Fin.cases ?_ (fun j => ?_) s <;> rfl

/-- The energy integral of the bubble, in `t₀`, at the outer energies `t'`, the outer spatial
momenta `v'` and the bubble spatial momentum `w`. -/
noncomputable def bubbleT (F : (Fin 3 → Fin 4 → ℝ) → ℂ) (t' : Fin 2 → ℝ)
    (v' : Fin 2 → Fin 3 → ℝ) (w : Fin 3 → ℝ) : ℂ :=
  ∫ t₀ : ℝ, F (Fin.cons (Fin.cons t₀ w : Fin 4 → ℝ) fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ))

/-- The one-loop energy-first integral of the bubble at the outer momenta `ℓ'`. -/
noncomputable def bubbleJ (F : (Fin 3 → Fin 4 → ℝ) → ℂ) (ℓ' : Fin 2 → Fin 4 → ℝ) : ℂ :=
  QED.OneLoop.energyFirstIntegral fun q => F (Fin.cons q ℓ')

theorem bubbleJ_cons (F : (Fin 3 → Fin 4 → ℝ) → ℂ) (t' : Fin 2 → ℝ) (v' : Fin 2 → Fin 3 → ℝ) :
    bubbleJ F (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) =
      ∫ w : Fin 3 → ℝ, bubbleT F t' v' w := rfl

/-- The two stages of (T₉) at three loops, with the bubble momentum split off. -/
theorem joint3_split_inner (F : (Fin 3 → Fin 4 → ℝ) → ℂ)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 F) :
    (∀ w v', ∫ t : Fin 3 → ℝ, F (fun s => (Fin.cons (t s)
      ((Fin.cons w v' : Fin 3 → Fin 3 → ℝ) s) : Fin 4 → ℝ)) =
      ∫ t' : Fin 2 → ℝ, bubbleT F t' v' w) ∧
    Integrable fun p : (Fin 3 → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      ∫ t' : Fin 2 → ℝ, bubbleT F t' p.2 p.1 := by
  obtain ⟨hF₁, hF₂⟩ := hF
  have hin : ∀ w v', ∫ t : Fin 3 → ℝ, F (fun s => (Fin.cons (t s)
      ((Fin.cons w v' : Fin 3 → Fin 3 → ℝ) s) : Fin 4 → ℝ)) =
      ∫ t' : Fin 2 → ℝ, bubbleT F t' v' w := by
    intro w v'
    have hint := (integrable_fin_cons_iff _).mp (hF₁ (Fin.cons w v'))
    rw [integral_fin_cons]
    simp only [cons_cons] at hint ⊢
    exact integral_prod_symm _ hint
  refine ⟨hin, ?_⟩
  have hout := (integrable_fin_cons_iff _).mp hF₂
  simp only [hin] at hout
  exact hout

/-- **Nested equals joint at three loops, inner bubble.** If both stages of the joint
energy-first integral (T₉) of `F` are integrable and, for almost every outer spatial momentum
`v'`, the bubble energy integral is integrable jointly in the outer energies and the bubble
spatial momentum (`hK`), then the joint integral at three loops is the joint integral at two
loops in `(ℓ 1, ℓ 2)` of the energy-first integral (D) in `ℓ 0`. -/
theorem jointEnergyFirstIntegral_three_eq_inner (F : (Fin 3 → Fin 4 → ℝ) → ℂ)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 F)
    (hK : ∀ᵐ v' : Fin 2 → Fin 3 → ℝ,
      Integrable fun p : (Fin 2 → ℝ) × (Fin 3 → ℝ) => bubbleT F p.1 v' p.2) :
    QED.TwoLoop.jointEnergyFirstIntegral 3 F =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (bubbleJ F) := by
  obtain ⟨hin, hout⟩ := joint3_split_inner F hF
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  rw [integral_fin_cons]
  simp only [hin]
  refine (integral_prod_symm _ hout).trans (integral_congr_ae (hK.mono fun v' hv' => ?_))
  simp only [bubbleJ_cons]
  exact (integral_integral_swap (f := fun (t' : Fin 2 → ℝ) (w : Fin 3 → ℝ) =>
    bubbleT F t' v' w) hv').symm

/-- **The outer integrand is integrable in both stages**, given both stages of the joint
prescription at three loops and the condition `hK` at every outer spatial momentum. -/
theorem jointEnergyFirstIntegrable_inner (F : (Fin 3 → Fin 4 → ℝ) → ℂ)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 F)
    (hK : ∀ v' : Fin 2 → Fin 3 → ℝ,
      Integrable fun p : (Fin 2 → ℝ) × (Fin 3 → ℝ) => bubbleT F p.1 v' p.2) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (bubbleJ F) := by
  obtain ⟨-, hout⟩ := joint3_split_inner F hF
  refine ⟨fun v' => ?_, ?_⟩
  · simp only [bubbleJ_cons]
    exact (hK v').integral_prod_left
  · refine hout.integral_prod_right.congr (Filter.Eventually.of_forall fun v' => ?_)
    simp only [bubbleJ_cons]
    exact integral_integral_swap (f := fun (w : Fin 3 → ℝ) (t' : Fin 2 → ℝ) =>
      bubbleT F t' v' w) (hK v').swap

/-! ### The Feynman parameter of the bubble -/

/-- **The joint energy-first integral commutes with an integral over a parameter**, for a family
`G x` of `L`-loop integrands: if at every spatial `v` the integrand is integrable jointly in the
parameter and the energies (`h₁`), and the energy integrals are integrable jointly in the
parameter and the spatial momenta (`h₂`), then the integrand `∫_S G x · dx` is integrable in both
stages of (T₉) and its joint integral is `∫_S` of the joint integrals of `G x`. -/
theorem jointEnergyFirstIntegral_setIntegral {L : ℕ} {S : Set ℝ}
    (G : ℝ → (Fin L → Fin 4 → ℝ) → ℂ)
    (h₁ : ∀ v : Fin L → Fin 3 → ℝ, Integrable (fun p : ℝ × (Fin L → ℝ) =>
      G p.1 fun s => (Fin.cons (p.2 s) (v s) : Fin 4 → ℝ)) ((volume.restrict S).prod volume))
    (h₂ : Integrable (fun p : ℝ × (Fin L → Fin 3 → ℝ) => ∫ t : Fin L → ℝ,
      G p.1 fun s => (Fin.cons (t s) (p.2 s) : Fin 4 → ℝ)) ((volume.restrict S).prod volume)) :
    QED.TwoLoop.jointEnergyFirstIntegrable L (fun ℓ => ∫ x in S, G x ℓ) ∧
      QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => ∫ x in S, G x ℓ) =
        ∫ x in S, QED.TwoLoop.jointEnergyFirstIntegral L (G x) := by
  have hin : ∀ v : Fin L → Fin 3 → ℝ, ∫ t : Fin L → ℝ, (∫ x in S,
      G x fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) =
      ∫ x in S, ∫ t : Fin L → ℝ, G x fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) := fun v =>
    (integral_integral_swap (h₁ v)).symm
  refine ⟨⟨fun v => (h₁ v).integral_prod_right, ?_⟩, ?_⟩
  · simp only [hin]
    exact h₂.integral_prod_right
  · unfold QED.TwoLoop.jointEnergyFirstIntegral
    simp only [hin]
    exact (integral_integral_swap h₂).symm

end QED.ChainProof.SetCMainB

end
