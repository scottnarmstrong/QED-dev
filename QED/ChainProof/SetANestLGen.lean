/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestLFubini
public import QED.ChainProof.SetANestVOuter
public import QED.ChainProof.SetANestSum
public import QED.TwoLoop.CountertermInsertionChain
public import QED.GradedProof.VP2ClassG

/-!
# Set (a), obligation (N): the nested form of a two-loop class from its Wick factorization

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`, the nested form
`QED.ChainProof.SetANest.LoopNested` of the two-loop classes `GW`, `GU`, `FA`, `FB` (an outer
one-loop vertex with a one-loop insertion on its photon line).

* `sum_pi_sum_equiv`, **`sum_spinor_chain3_loop2`**: the spinor sum of an open chain through
  three vertices and a closed loop through two is the chain entry times the loop trace.
* `lOuter`: `(1/i)` times the outer factor `QED.ChainProof.SetANestV.nestOuter` of a photon slot;
  continuous and decaying like `(1 + |t|)⁻¹⁰` along `k = (t, w)` (`decaysLike_nestOuter`).
* **`loopNested_of_lOuter`**: if the value (G₅) of a class is the joint integral of
  `outerInner lOuter G` (the routing and Wick steps), both stages of that joint integral are
  integrable ((HA₀) in the nested routing) and `G` has `OneLoopInnerBound a b` with
  `0 ≤ a < 9`, `3 < b`, then the class is in nested form with the photon tensor
  `X(k)^{ab} = (1/i) ∫_D G(k, ·)^{ab}`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANest

open QED.OneLoop QED.TwoLoop.VPUnitNested QED.WickModel
open QED.TwoLoop.NestedVPFubiniBound (DecaysLike)

/-! ### Spinor sums -/

section Spin

variable {X R M : Type*} [Fintype X] [DecidableEq X] [Fintype R] [AddCommMonoid M]
  {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- A sum over the functions on `X ≃ A ⊕ B` splits into the sums over the two restrictions. -/
theorem sum_pi_sum_equiv (e : X ≃ A ⊕ B) (g : (X → R) → M) :
    ∑ α, g α = ∑ α₁ : A → R, ∑ α₂ : B → R, g fun x => Sum.elim α₁ α₂ (e x) := by
  rw [← ((e.arrowCongr (Equiv.refl R)).trans
    (Equiv.sumArrowEquivProdArrow A B R)).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- **The spinor sum of an open chain through three vertices and a closed loop through two**:
with `α x₁` and `β x₃` fixed, the sum of `c · A₁ S₁ A₂ S₂ A₃ · B₁ T₁ B₂ T₂` over the spinor
indices is `c` times the loop trace times the entry of the chain. -/
theorem sum_spinor_chain3_loop2 (e : X ≃ Fin 3 ⊕ Fin 2) {x₁ x₂ x₃ y₁ y₂ : X}
    (h₁ : e x₁ = .inl 0) (h₂ : e x₂ = .inl 1) (h₃ : e x₃ = .inl 2) (h₄ : e y₁ = .inr 0)
    (h₅ : e y₂ = .inr 1) (c : ℂ)
    (A₁ A₂ A₃ S₁ S₂ B₁ B₂ T₁ T₂ : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4,
      (if α x₁ = a ∧ β x₃ = b then (1 : ℂ) else 0) *
        (c * (A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
          A₃ (α x₃) (β x₃)) *
          (B₁ (α y₁) (β y₁) * T₁ (β y₁) (α y₂) * B₂ (α y₂) (β y₂) * T₂ (β y₂) (α y₁))) =
      c * Matrix.trace (B₁ * T₁ * B₂ * T₂) * (A₁ * S₁ * A₂ * S₂ * A₃) a b := by
  rw [sum_pi_sum_equiv e]
  simp only [sum_pi_sum_equiv e (g := fun β => _ * _), h₁, h₂, h₃, h₄, h₅, Sum.elim_inl,
    Sum.elim_inr]
  have hL := QED.GradedProof.VP2.sum_spinor_loop2 (X := Fin 2) (x₁ := 0) (x₂ := 1)
    (by decide) (by decide) B₁ B₂ T₁ T₂
  have hC := QED.TwoLoop.Insertion.sum_spinor_chain3 (X := Fin 3) (x₁ := 0) (x₂ := 1)
    (x₃ := 2) (by decide) (by decide) (by decide) (by decide)
    (c * Matrix.trace (B₁ * T₁ * B₂ * T₂)) A₁ A₂ A₃ S₁ S₂ a b
  rw [← hC]
  refine Finset.sum_congr rfl fun α₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β₁ _ => ?_
  rw [← hL]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α₂ _ => Finset.sum_congr rfl fun β₂ _ => ?_
  ring

end Spin

theorem ite_and_eq_mul_ite (p q : Prop) [Decidable p] [Decidable q] :
    (if p ∧ q then (1 : ℂ) else 0) = (if p then 1 else 0) * (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem sum_comm_out_two {F : Type} [Fintype F] (g : F → Fin 4 → Fin 4 → ℂ) :
    ∑ f, ∑ a, ∑ b, g f a b = ∑ a, ∑ b, ∑ f, g f a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-! ### The outer factor -/

/-- `(1/i)` times the outer factor of the photon slot `(a, b)`, the `(i, j)` entry of the vertex
chain with photon factor `Δ(k)_{ν a} Δ(-k)_{ρ b}`. -/
noncomputable def lOuter (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (k : Fin 4 → ℝ)
    (a b : Fin 4) : ℂ :=
  (1 / I) * QED.ChainProof.SetANestV.nestOuter e m mγ Λ ε p' p μ i j k a b

theorem continuous_lOuter {ε : ℝ} (hε : 0 < ε) (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) (w : Fin 3 → ℝ) (a b : Fin 4) :
    Continuous fun t => lOuter e m mγ Λ ε p' p μ i j (Fin.cons t w) a b :=
  continuous_const.mul (QED.ChainProof.SetANestV.continuous_nestOuter hε e m mγ Λ p' p μ i j w a b)

theorem decaysLike_lOuter {ε : ℝ} (hε : 0 < ε) (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) (w : Fin 3 → ℝ) (a b : Fin 4) :
    DecaysLike (fun t => lOuter e m mγ Λ ε p' p μ i j (Fin.cons t w) a b) 10 :=
  ((QED.TwoLoop.NestedVPFubiniBound.DecaysLike.const (1 / I)).mul
    (QED.ChainProof.SetANestV.decaysLike_nestOuter hε e m mγ Λ p' p μ i j w a b)).mono
    (by norm_num)

/-- The outer integrand with the inner integral done is the outer integrand of the photon tensor
`(1/i) ∫_D G(k, ·)`. -/
theorem outerOf_lOuter (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (G : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (k : Fin 4 → ℝ) :
    outerOf (lOuter e m mγ Λ ε p' p μ i j) G k =
      nestInt e m mγ Λ ε p' p (fun k a b => (1 / I) * energyFirstIntegral fun q => G k q a b)
        μ i j k := by
  rw [outerOf, QED.ChainProof.SetANestV.nestInt_eq_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [lOuter]
  ring

/-! ### The nested form -/

/-- **The nested form of a two-loop class from its Wick factorization.** At `ε > 0`: if for
every entry the value (G₅) of `C` is the joint energy-first integral (T₉) of
`outerInner lOuter G`, both stages of which are integrable, and `G` satisfies
`OneLoopInnerBound a b` with `0 ≤ a < 9`, `3 < b`, then `C` is in nested form with the photon
tensor `X(k)^{ab} = (1/i) ∫_D G(k, ·)^{ab}`. -/
theorem loopNested_of_lOuter (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) (p' p : Fin 4 → ℝ) (hε : 0 < P.ε)
    {G : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} {a b : ℝ} (ha0 : 0 ≤ a) (ha : a < 9)
    (hb : 3 < b) (hG : OneLoopInnerBound a b G)
    (hval : ∀ μ i j : Fin 4, Graded.contractionValue P Φ D C 0 (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 2
        (outerInner (lOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j) G))
    (hF : ∀ μ i j : Fin 4, QED.TwoLoop.jointEnergyFirstIntegrable 2
        (outerInner (lOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j) G)) :
    LoopNested P Φ D C (fun k a b => (1 / I) * energyFirstIntegral fun q => G k q a b) p' p := by
  intro μ i j
  obtain ⟨h1, h2⟩ := jointEnergyFirstIntegral_outerInner ha0 ha hb _ hG
    (continuous_lOuter hε _ _ _ _ p' p μ i j) (decaysLike_lOuter hε _ _ _ _ p' p μ i j)
    (hF μ i j)
  have e := funext (outerOf_lOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j G)
  rw [e] at h1 h2
  exact ⟨h2, (hval μ i j).trans h1⟩

end QED.ChainProof.SetANest

end
