/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.TwoPointClassificationBasic

/-!
# Two gauge vertices

Names and index sums for the vertex sequence `gauge2` of two `gauge` vertices, which carries the
one-loop parts of the two-point 1PI functions of the general Wick model (decisions D-23, D-24,
D-25): the electron self-energy loop and the vacuum polarization loop.

* `eq_gauge2_of_sum_order_le`: two vertices of total order at most `2` are two gauge vertices.
* `fv2 t`, `ps2 t`: the fermion vertex and the photon field of vertex `t`.
* `sum_selfEnergy_index`: the spinor and Lorentz index sum of the self-energy loop is
  `∑_{μν} D_{μν} (γ^μ S γ^ν)`.
* `sum_polarization_index`: the spinor index sum of the vacuum polarization loop is the trace
  `Tr[γ^μ S₀ γ^ν S₁]`.
-/

@[expose] public section

open Complex

namespace QED.WickModel

/-- The vertex sequence of two `gauge` vertices. -/
abbrev gauge2 : Fin 2 → Wick.VertexKind := fun _ => .gauge

/-- Two vertices of total order at most `2` are two gauge vertices: every vertex has order at
least `1`, with equality only for `gauge`. -/
theorem eq_gauge2_of_sum_order_le {κ : Fin 2 → Wick.VertexKind} (h : ∑ t, (κ t).order ≤ 2) :
    κ = gauge2 := by
  have key : ∀ k₀ k₁ : Wick.VertexKind, k₀.order + k₁.order ≤ 2 →
      k₀ = .gauge ∧ k₁ = .gauge := by
    decide
  rw [Fin.sum_univ_two] at h
  obtain ⟨h0, h1⟩ := key _ _ h
  funext t
  fin_cases t <;> assumption

/-- Vertex `t` of `gauge2` as a fermion vertex. -/
def fv2 (t : Fin 2) : Wick.FermionVertex gauge2 := ⟨t, nofun⟩

/-- The photon field of vertex `t` of `gauge2`. -/
def ps2 (t : Fin 2) : Wick.PhotonSlot gauge2 := ⟨t, ⟨0, Nat.zero_lt_one⟩⟩

/-- Every fermion vertex of `gauge2` is `fv2 t`. -/
theorem fv2_val_eq (x : Wick.FermionVertex gauge2) : fv2 x.1 = x := rfl

/-- Every photon field of `gauge2` is `ps2 t`. -/
theorem ps2_fst_eq (x : Wick.PhotonSlot gauge2) : ps2 x.1 = x := by
  obtain ⟨t, k⟩ := x
  exact Sigma.ext rfl (heq_of_eq (Subsingleton.elim (α := Fin 1) _ _))

/-- The vertex of `fv2 t` is `t`. -/
@[simp]
theorem fv2_val (t : Fin 2) : (fv2 t).1 = t := rfl

/-- The vertex of `ps2 t` is `t`. -/
@[simp]
theorem ps2_fst (t : Fin 2) : (ps2 t).1 = t := rfl

/-- The key of the photon field of vertex `t`. -/
@[simp]
theorem photonKey_ps2 (t : Fin 2) : Wick.photonKey (ps2 t) = 2 * t.val := rfl

/-- `fv2` is injective. -/
theorem fv2_injective : Function.Injective fv2 := fun _ _ h => congrArg Subtype.val h

/-- `ps2` is injective. -/
theorem ps2_injective : Function.Injective ps2 := fun _ _ h => congrArg Sigma.fst h

/-- `fv2` is injective. -/
@[simp]
theorem fv2_inj {s t : Fin 2} : fv2 s = fv2 t ↔ s = t := fv2_injective.eq_iff

/-- `ps2` is injective. -/
@[simp]
theorem ps2_inj {s t : Fin 2} : ps2 s = ps2 t ↔ s = t := ps2_injective.eq_iff

/-- The fermion vertices of `gauge2` are `fv2 a` and `fv2 b`, for `a ≠ b`. -/
theorem fv2_eq_or : ∀ a b : Fin 2, a ≠ b → ∀ x : Wick.FermionVertex gauge2,
    x = fv2 a ∨ x = fv2 b := by
  decide

/-- The photon fields of `gauge2` are `ps2 a` and `ps2 b`, for `a ≠ b`. -/
theorem ps2_eq_or : ∀ a b : Fin 2, a ≠ b → ∀ x : Wick.PhotonSlot gauge2,
    x = ps2 a ∨ x = ps2 b := by
  decide

/-- `gauge2` has two fermion vertices. -/
theorem card_fermionVertex_gauge2 : Fintype.card (Wick.FermionVertex gauge2) = 2 := by
  decide

/-- The factor of a gauge vertex of `gauge2`. -/
theorem vertexFactor_gauge2 (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex gauge2 → Fin 4)
    (lor : Wick.PhotonSlot gauge2 → Fin 4) (kψ : Wick.FermionVertex gauge2 → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot gauge2 → Fin 4 → ℝ) (t : Fin 2) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * Dirac.gamma (lor (ps2 t)) (α (fv2 t)) (β (fv2 t)) := rfl

/-! ### Index sums -/

section IndexSums

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {xa xb : X} {ya yb : Y}

/-- **The index sum of the self-energy loop.** The sum over the spinor indices `α, β` and the
Lorentz indices `lor` of the fields at two vertices, with the spinor index `αe` of the `Ψ̄` of the
first vertex and the spinor index `βe` of the `Ψ` of the second vertex fixed, is the matrix
product `γ^μ S γ^ν` contracted with `D_{μν}`. -/
theorem sum_selfEnergy_index (hx : xa ≠ xb) (hX : ∀ x, x = xa ∨ x = xb) (hy : ya ≠ yb)
    (hY : ∀ y, y = ya ∨ y = yb) (G : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (S : Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 4 → Fin 4 → ℂ) (c₁ c₂ : ℂ) (αe βe : Fin 4) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4, ∑ lor : Y → Fin 4,
      (if α xa = αe ∧ β xb = βe then 1 else 0) *
        (c₁ * G (lor ya) (α xa) (β xa) * (c₁ * G (lor yb) (α xb) (β xb)) *
          (c₂ * S (β xa) (α xb)) * (c₂ * D (lor ya) (lor yb))) =
      c₁ ^ 2 * c₂ ^ 2 * ∑ μ, ∑ ν, D μ ν * (G μ * S * G ν) αe βe := by
  rw [show (∑ α : X → Fin 4, ∑ β : X → Fin 4, ∑ lor : Y → Fin 4, _) =
      ∑ lor : Y → Fin 4, ∑ α : X → Fin 4, ∑ β : X → Fin 4, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  have hXs := fun (g : (X → Fin 4) → ℂ) => sum_pi_eq_of_forall_eq_or_eq hx hX g
  have hYs := fun (g : (Y → Fin 4) → ℂ) => sum_pi_eq_of_forall_eq_or_eq hy hY g
  simp only [hXs, hYs, ite_true, hx.symm, hy.symm, ite_false]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **The index sum of the vacuum polarization loop.** The sum over the spinor indices `α, β` of
the fields at two vertices joined by two fermion lines is the trace `Tr[G₀ S₀ G₁ S₁]`. -/
theorem sum_polarization_index (hx : xa ≠ xb) (hX : ∀ x, x = xa ∨ x = xb)
    (G₀ G₁ S₀ S₁ : Matrix (Fin 4) (Fin 4) ℂ) (c₁ c₂ : ℂ) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4,
      c₁ * G₀ (α xa) (β xa) * (c₁ * G₁ (α xb) (β xb)) *
        ((c₂ * S₀ (β xa) (α xb)) * (c₂ * S₁ (β xb) (α xa))) =
      c₁ ^ 2 * c₂ ^ 2 * Matrix.trace (G₀ * S₀ * G₁ * S₁) := by
  have hXs := fun (g : (X → Fin 4) → ℂ) => sum_pi_eq_of_forall_eq_or_eq hx hX g
  simp only [hXs, ite_true, hx.symm, ite_false]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

end IndexSums

end QED.WickModel

end
