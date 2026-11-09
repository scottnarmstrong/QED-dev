/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Basic.Complex.Basic

/-!
# Index sums of the leg corrections

Spinor and Lorentz index sums that arise in the amplitudes of the connected contractions of three
gauge vertices (packet 6a, decision D-24), rewritten as matrix products. The summation variables
are the indices of the vertex fields left free by the external indices; the factors are the
vertex factors `c₁ G^μ`, the fermion propagators `c₂ S` and the photon propagator `c₂ D_{μν}`.

* `sum_chain_index_in`: a self-energy loop on the incoming leg,
  `[c₁ G^μ c₂ S₁]_{αγ} [c₁² c₂² ∑ D_{μ'ν'} G^{μ'} S₂ G^{ν'}]_{γβ}`.
* `sum_chain_index_out`: a self-energy loop on the outgoing leg,
  `[c₁² c₂² ∑ D_{μ'ν'} G^{μ'} S₁ G^{ν'}]_{αγ} [c₂ S₂ c₁ G^μ]_{γβ}`.
* `sum_polarization_index3`: a vacuum polarization loop,
  `∑_{νρ} c₁ G^ν_{αβ} c₂ D_{νρ} c₁² c₂² Tr[G^μ S₁ G^ρ S₂]`.
-/

@[expose] public section

namespace QED.WickModel

variable (G : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (S₁ S₂ : Matrix (Fin 4) (Fin 4) ℂ)
  (D : Fin 4 → Fin 4 → ℂ) (c₁ c₂ : ℂ) (αe βe μe : Fin 4)

/-- **The index sum of a self-energy loop on the incoming leg.** -/
theorem sum_chain_index_in :
    ∑ zb : Fin 4, ∑ zc : Fin 4, ∑ xb : Fin 4, ∑ xc : Fin 4, ∑ ya : Fin 4, ∑ yb : Fin 4,
      c₁ * G μe αe ya * (c₁ * G zb xb yb) * (c₁ * G zc xc βe) *
        ((c₂ * S₁ ya xb) * (c₂ * S₂ yb xc)) * (c₂ * D zb zc) =
      ∑ γ, ((c₁ • G μe) * (c₂ • S₁)) αe γ *
        (c₁ ^ 2 * c₂ ^ 2 * ∑ μ', ∑ ν', D μ' ν' * (G μ' * S₂ * G ν') γ βe) := by
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, zb]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, xb, 2, zb, 2, zc, 2, xc]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **The index sum of a self-energy loop on the outgoing leg.** -/
theorem sum_chain_index_out :
    ∑ za : Fin 4, ∑ zb : Fin 4, ∑ xb : Fin 4, ∑ xc : Fin 4, ∑ ya : Fin 4, ∑ yb : Fin 4,
      c₁ * G za αe ya * (c₁ * G zb xb yb) * (c₁ * G μe xc βe) *
        ((c₂ * S₁ ya xb) * (c₂ * S₂ yb xc)) * (c₂ * D za zb) =
      ∑ γ, (c₁ ^ 2 * c₂ ^ 2 * ∑ μ', ∑ ν', D μ' ν' * (G μ' * S₁ * G ν') αe γ) *
        ((c₂ • S₂) * (c₁ • G μe)) γ βe := by
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, za, 2, zb, 2, xb, 2, xc]; rw [Finset.sum_comm]
  conv_lhs => enter [2, za, 2, zb, 2, xb]; rw [Finset.sum_comm]
  conv_lhs => enter [2, za, 2, zb]; rw [Finset.sum_comm]
  conv_lhs => enter [2, za]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, yb, 2, za, 2, zb]; rw [Finset.sum_comm]
  conv_lhs => enter [2, yb, 2, za]; rw [Finset.sum_comm]
  conv_lhs => enter [2, yb]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **The index sum of a vacuum polarization loop on the photon leg.** -/
theorem sum_polarization_index3 :
    ∑ za : Fin 4, ∑ zw : Fin 4, ∑ xv : Fin 4, ∑ xw : Fin 4, ∑ yv : Fin 4, ∑ yw : Fin 4,
      c₁ * G za αe βe * (c₁ * G μe xv yv) * (c₁ * G zw xw yw) *
        ((c₂ * S₁ yv xw) * (c₂ * S₂ yw xv)) * (c₂ * D za zw) =
      ∑ ν, ∑ ρ, c₁ * G ν αe βe * (c₂ * D ν ρ) *
        (c₁ ^ 2 * c₂ ^ 2 * Matrix.trace (G μe * S₁ * G ρ * S₂)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, za, 2, zw, 2, xv, 2, xw]; rw [Finset.sum_comm]
  conv_lhs => enter [2, za, 2, zw, 2, xv]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end QED.WickModel

end
