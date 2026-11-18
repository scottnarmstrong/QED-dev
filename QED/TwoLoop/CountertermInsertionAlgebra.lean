/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Dirac
public import QED.Frozen.OneLoop.VertexIntegrand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The counterterm insertions as identities of integrands at fixed `ε`

Section 5.1 of `docs/TWO-LOOP-DERIVATION.md` (obligation O2-13), at the level of the integrands
and at fixed `ε`. Everything here is algebra of `4 × 4` matrices and scalars; no integral occurs.

* `vertexChain e μ S_out S_in D`: the one-loop vertex integrand
  `(ie)³ (1/i)³ (2π)⁻⁴ ∑_{ν ρ} D_{νρ} γ^ρ S_out γ^μ S_in γ^ν` with arbitrary outgoing and incoming
  electron factors and photon factor. The frozen integrand (C) is
  `vertexChain e μ S̃(p' + ℓ) S̃(p + ℓ) Δ̃(ℓ)` (`vertexIntegrand_eq_vertexChain`, by `rfl`).
  It is linear in each of its three slots.
* **The `fermionCt` insertion** (`electronInsertion_eq`): for `ε ≠ 0`, with
  `D = k·k + m² - iε`,
  `-S̃(k) (δ₂ k̸ + δ_m m) S̃(k) = -δ₂ S̃(k) + (δ₂ - δ_m) m S̃(k)² - δ₂ (iε / D) S̃(k)`.
  The last term is the `O(ε)` defect of section 5.1: it is not zero at any `ε ≠ 0`; it comes from
  `S̃(k) (k̸ + m) = 1 + iε / D`.
* **The `photonCt` insertion** (`photonInsertion_eq`): the photon factor of one slot pairing,
  `(1/i) ∑_{a b} Δ̃_{νa}(k) [-(i/2) δ₃ (k² g^{ab} - k^a k^b)] Δ̃_{ρb}(k)`, is exactly
  `-(δ₃/2) g_{νρ} k² d(k)² + (δ₃/2) d(k)² k_ν k_ρ`, with `d(k)` the scalar Pauli–Villars photon
  factor (`Δ̃_{μν} = g_{μν} d`). The first (transverse) term is `-(δ₃/2)` times the photon factor
  with `d → k² d²`; the second is the longitudinal `k_ν k_ρ` term of O2-14. No `ε` defect occurs.
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.Insertion

/-! ### The one-loop vertex chain -/

/-- The one-loop vertex integrand with outgoing electron factor `Sout`, incoming electron factor
`Sin` and photon factor `D`: `(ie)³ (1/i)³ (2π)⁻⁴ ∑_{ν ρ} D_{νρ} γ^ρ Sout γ^μ Sin γ^ν`. -/
noncomputable def vertexChain (e : ℝ) (μ : Fin 4) (Sout Sin : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) •
    ∑ ν, ∑ ρ, D ν ρ • (Dirac.gamma ρ * Sout * Dirac.gamma μ * Sin * Dirac.gamma ν)

/-- The frozen one-loop vertex integrand (C) is the vertex chain of the propagators. -/
theorem vertexIntegrand_eq_vertexChain (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) :
    QED.OneLoop.vertexIntegrand e m mγ Λ ε p' p μ ℓ =
      vertexChain e μ (QED.OneLoop.electronPropagator m ε (p' + ℓ))
        (QED.OneLoop.electronPropagator m ε (p + ℓ)) (QED.OneLoop.photonPropagator mγ Λ ε ℓ) :=
  rfl

section Linear

variable (e : ℝ) (μ : Fin 4)

theorem vertexChain_add_in (Sout Sin Sin' : Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ Sout (Sin + Sin') D = vertexChain e μ Sout Sin D + vertexChain e μ Sout Sin' D := by
  simp only [vertexChain, Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]

theorem vertexChain_smul_in (c : ℂ) (Sout Sin : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ Sout (c • Sin) D = c • vertexChain e μ Sout Sin D := by
  simp only [vertexChain, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, smul_comm c]

theorem vertexChain_sub_in (Sout Sin Sin' : Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ Sout (Sin - Sin') D = vertexChain e μ Sout Sin D - vertexChain e μ Sout Sin' D := by
  rw [sub_eq_add_neg, vertexChain_add_in, ← neg_one_smul ℂ Sin', vertexChain_smul_in, neg_one_smul,
    ← sub_eq_add_neg]

theorem vertexChain_add_out (Sout Sout' Sin : Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ (Sout + Sout') Sin D =
      vertexChain e μ Sout Sin D + vertexChain e μ Sout' Sin D := by
  simp only [vertexChain, Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]

theorem vertexChain_smul_out (c : ℂ) (Sout Sin : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ (c • Sout) Sin D = c • vertexChain e μ Sout Sin D := by
  simp only [vertexChain, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, smul_comm c]

theorem vertexChain_sub_out (Sout Sout' Sin : Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ (Sout - Sout') Sin D =
      vertexChain e μ Sout Sin D - vertexChain e μ Sout' Sin D := by
  rw [sub_eq_add_neg, vertexChain_add_out, ← neg_one_smul ℂ Sout', vertexChain_smul_out,
    neg_one_smul, ← sub_eq_add_neg]

theorem vertexChain_add_photon (Sout Sin : Matrix (Fin 4) (Fin 4) ℂ) (D D' : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ Sout Sin (fun ν ρ => D ν ρ + D' ν ρ) =
      vertexChain e μ Sout Sin D + vertexChain e μ Sout Sin D' := by
  simp only [vertexChain, add_smul, Finset.sum_add_distrib, smul_add]

theorem vertexChain_smul_photon (c : ℂ) (Sout Sin : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ Sout Sin (fun ν ρ => c * D ν ρ) = c • vertexChain e μ Sout Sin D := by
  simp only [vertexChain, mul_smul, Finset.smul_sum, smul_comm c]

end Linear

/-! ### The `fermionCt` insertion on an electron line -/

/-- The matrix `δ₂ k̸ + δ_m m` of the `fermionCt` vertex factor `-i (δ₂ k̸ + δ_m m)` (V₁₉). -/
noncomputable def fermionCtMatrix (δ₂ δm m : ℝ) (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (δ₂ : ℂ) • Dirac.slash k + ((δm * m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The electron line with a `fermionCt` insertion, in the normalization of an incoming or
outgoing slot of `vertexChain`: `(1/i) (-i) S̃(k) (δ₂ k̸ + δ_m m) S̃(k) = -S̃ (δ₂ k̸ + δ_m m) S̃`. -/
noncomputable def electronInsertion (m ε δ₂ δm : ℝ) (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  -(QED.OneLoop.electronPropagator m ε k * fermionCtMatrix δ₂ δm m k *
    QED.OneLoop.electronPropagator m ε k)

/-- The electron denominator `k·k + m² - iε`. -/
noncomputable def electronDenom (m ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot k k + m ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I

theorem im_electronDenom (m ε : ℝ) (k : Fin 4 → ℝ) : (electronDenom m ε k).im = -ε := by
  simp only [electronDenom, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one,
    add_zero, zero_sub]

theorem electronDenom_ne_zero {m ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) : electronDenom m ε k ≠ 0 := by
  intro h
  have := im_electronDenom m ε k
  rw [h, zero_im] at this
  exact hε (by linarith)

/-- **The `fermionCt` insertion at fixed `ε`** (section 5.1): for `ε ≠ 0`,
`-S̃(k) (δ₂ k̸ + δ_m m) S̃(k) = -δ₂ S̃(k) + (δ₂ - δ_m) m S̃(k)² - δ₂ (iε / D(k)) S̃(k)`, with
`D(k) = k·k + m² - iε`. Exact; the last term is the `O(ε)` defect. -/
theorem electronInsertion_eq (m δ₂ δm : ℝ) {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) :
    electronInsertion m ε δ₂ δm k =
      (-(δ₂ : ℂ)) • QED.OneLoop.electronPropagator m ε k +
        (((δ₂ - δm) * m : ℝ) : ℂ) •
          (QED.OneLoop.electronPropagator m ε k * QED.OneLoop.electronPropagator m ε k) -
        ((δ₂ : ℂ) * ((ε : ℂ) * I / electronDenom m ε k)) • QED.OneLoop.electronPropagator m ε k := by
  have hD := electronDenom_ne_zero (m := m) hε k
  rw [electronInsertion, fermionCtMatrix]
  have hS : QED.OneLoop.electronPropagator m ε k =
      (electronDenom m ε k)⁻¹ • ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash k) :=
    rfl
  rw [hS]
  set D := electronDenom m ε k with hDdef
  set K := Dirac.slash k
  have hKK : K * K = ((-Minkowski.dot k k : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
    Dirac.slash_mul_slash k
  have hdot : ((Minkowski.dot k k : ℝ) : ℂ) = D + (ε : ℂ) * I - (m : ℂ) ^ 2 := by
    simp only [hDdef, electronDenom]
    push_cast
    ring
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, smul_smul, hKK,
    smul_sub, smul_add, neg_sub]
  rw [show ((-Minkowski.dot k k : ℝ) : ℂ) = -(D + (ε : ℂ) * I - (m : ℂ) ^ 2) by
    rw [Complex.ofReal_neg, hdot]]
  push_cast
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-! ### The `photonCt` insertion on the photon line -/

/-- The scalar Pauli–Villars photon factor `d(k) = (k² + m_γ² - iε)⁻¹ - (k² + Λ² - iε)⁻¹`, so
that `Δ̃_{μν}(k) = g_{μν} d(k)`. -/
noncomputable def photonScalar (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  (((Minkowski.dot k k + mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ -
    (((Minkowski.dot k k + Λ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹

theorem photonPropagator_eq_metric_mul (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε k μ ν =
      ((Minkowski.metric μ ν : ℝ) : ℂ) * photonScalar mγ Λ ε k :=
  rfl

/-- The `photonCt` vertex factor (V₁₉) for the momentum `k` entering through slot `0` and the
Lorentz indices `a` (slot `0`) and `b` (slot `1`): `-(i/2) δ₃ (k² g^{ab} - k^a k^b)`. -/
noncomputable def photonCtFactor (δ₃ : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  -(I / 2) * ((δ₃ * (Minkowski.dot k k * Minkowski.metric a b - k a * k b) : ℝ) : ℂ)

theorem photonCtFactor_neg (δ₃ : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    photonCtFactor δ₃ (-k) a b = photonCtFactor δ₃ k a b := by
  simp [photonCtFactor, Minkowski.dot]

theorem photonCtFactor_comm (δ₃ : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    photonCtFactor δ₃ k a b = photonCtFactor δ₃ k b a := by
  simp only [photonCtFactor, QED.Minkowski.metric_symm a b, mul_comm (k a) (k b)]

/-- The photon line with a `photonCt` insertion (one slot pairing), in the normalization of the
photon slot of `vertexChain`: `(1/i) ∑_{a b} Δ̃_{νa}(k) V^{ab}(k) Δ̃_{ρb}(k)`. -/
noncomputable def photonInsertion (δ₃ mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  (1 / I) * ∑ a, ∑ b, QED.OneLoop.photonPropagator mγ Λ ε k ν a * photonCtFactor δ₃ k a b *
    QED.OneLoop.photonPropagator mγ Λ ε k ρ b

/-- The transverse photon factor `g_{νρ} k² d(k)²`: the propagator with `d → k² d²`. -/
noncomputable def transversePhoton (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  ((Minkowski.metric ν ρ : ℝ) : ℂ) * (((Minkowski.dot k k : ℝ) : ℂ) * photonScalar mγ Λ ε k ^ 2)

/-- The longitudinal photon factor `d(k)² k_ν k_ρ` (obligation O2-14). -/
noncomputable def longitudinalPhoton (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  photonScalar mγ Λ ε k ^ 2 * ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)

/-- **The `photonCt` insertion, exactly** (section 5.1; no `ε` defect): one slot pairing of the
`photonCt` vertex between two photon propagators of momentum `k` is `-(δ₃/2)` times the
transverse factor plus `δ₃/2` times the longitudinal factor. -/
theorem photonInsertion_eq (δ₃ mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    photonInsertion δ₃ mγ Λ ε k ν ρ =
      (-(δ₃ / 2 : ℂ)) * transversePhoton mγ Λ ε k ν ρ +
        ((δ₃ / 2 : ℂ)) * longitudinalPhoton mγ Λ ε k ν ρ := by
  simp only [photonInsertion, photonPropagator_eq_metric_mul, transversePhoton,
    longitudinalPhoton, photonCtFactor, Minkowski.lower, Fin.sum_univ_four, Minkowski.metric]
  fin_cases ν <;> fin_cases ρ <;> simp <;> field_simp <;> ring_nf <;> simp only [I_sq] <;> ring

end QED.TwoLoop.Insertion

end
