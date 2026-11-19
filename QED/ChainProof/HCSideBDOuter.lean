/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDNestedGen
public import QED.ChainProof.HCSideBDRepLimit
public import QED.ChainProof.HCSideBDPauli

/-!
# The outer factors of the bubble–`δ₃` and `δ₃`–bubble classes

Helper for the nested form of `QED.ChainProof.Enum.repBD s` and `repDB s`. In the nested routing
(loop momentum `q`, photon momentum `k`) the value integrand of either class factorizes as an
outer factor `O(k)^{ρσ}` contracted with the one-loop vacuum polarization integrand
`Π^{ρσ}_ε(k, q)`:

* `bdOuter`, `dbOuter`: the open-line chain with, on the two photon legs, the photon propagator
  and the `δ₃` insertion `photonInsertion` (in the two orders);
* `bd_integrand_eq`, `db_integrand_eq`: **the factorization**
  `(2π)⁻⁸ A(repBD s) = nestedF P (bdOuter …) ![q, k]`, resp. for `repDB s`;
* `outerF_bdOuter`, `outerF_dbOuter`: **contracted with the closed-form inner loop**
  `T = A (k² g - k k) + B g`, either outer factor gives the one-loop vertex chain with the photon
  chain `bdChain` (`Δ T Δ V Δ`; `dbChain = bdChain` since both are symmetric), at the reflected
  photon momentum.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
  QED.ChainProof.Enum QED.ChainProof.RepsInt
open QED.TwoLoop.VPHalfAtAssembly (vpT)
open QED.TwoLoop.VPHalfAt (vpLoopEps vpExtraEps)

/-! ### Sums -/

theorem sum4_reindex (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F d c a b = ∑ a, ∑ b, ∑ c, ∑ d, F a b c d := by
  conv_lhs => enter [2, x1, 2, x2]; rw [Finset.sum_comm]
  conv_lhs => enter [2, x1]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, x4, 2, x1]; rw [Finset.sum_comm]
  conv_lhs => enter [2, x4]; rw [Finset.sum_comm]

theorem photonPropagator_symm (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε k a b = QED.OneLoop.photonPropagator mγ Λ ε k b a := by
  simp only [QED.OneLoop.photonPropagator, QED.Minkowski.metric_symm a b]

/-! ### The outer factors -/

/-- The outer factor of `repBD s`: the `δ₃` insertion on the leg `ρ` (vertex `c`), the photon
propagator on the leg `σ` (vertex `a`). -/
noncomputable def bdOuter (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (k : Fin 4 → ℝ)
    (ρ σ : Fin 4) : ℂ :=
  -(((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 3 * (1 / I) ^ 4 *
    ∑ l0 : Fin 4, ∑ l2 : Fin 4, QED.TwoLoop.NestedVP.outerChain P p kext k μ l0 l2 α β *
      photonInsertion P.δ₃ P.mγ P.Λ P.ε k ρ l0 * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k l2 σ

/-- The outer factor of `repDB s`: the photon propagator on the leg `ρ`, the `δ₃` insertion on
the leg `σ`. -/
noncomputable def dbOuter (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (k : Fin 4 → ℝ)
    (ρ σ : Fin 4) : ℂ :=
  -(((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 3 * (1 / I) ^ 4 *
    ∑ l0 : Fin 4, ∑ l2 : Fin 4, QED.TwoLoop.NestedVP.outerChain P p kext k μ l0 l2 α β *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k l0 ρ * photonInsertion P.δ₃ P.mγ P.Λ P.ε k l2 σ

/-- **The factorization of the integrand of `repBD s`** in the nested routing. -/
theorem bd_integrand_eq (s : Fin 2) (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (q k : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P (repBD s) pIn kIn (bdMom s (pIn 0) (kIn 0) q k) αOut βIn μ =
      nestedF P (bdOuter P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0)) ![q, k] := by
  rw [regulatedAmplitude₂_repBD]
  simp only [bd_amplitude]
  unfold nestedF bdOuter vacuumPolarizationIntegrand
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    QED.TwoLoop.NestedVP.trace_rotate (Dirac.gamma _)]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b, 2, c]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_rhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_rhs => enter [2, a, 2, b, 2, c]; rw [Finset.sum_comm]
  conv_rhs => enter [2, a]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_rhs => enter [2, a]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

/-- **The factorization of the integrand of `repDB s`** in the nested routing. -/
theorem db_integrand_eq (s : Fin 2) (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (q k : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P (repDB s) pIn kIn (dbMom s (pIn 0) (kIn 0) q k) αOut βIn μ =
      nestedF P (dbOuter P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0)) ![q, k] := by
  rw [regulatedAmplitude₂_repDB]
  simp only [db_amplitude]
  unfold nestedF dbOuter vacuumPolarizationIntegrand
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    QED.TwoLoop.NestedVP.trace_rotate (Dirac.gamma _)]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b, 2, c]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_rhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_rhs => enter [2, a, 2, b, 2, c]; rw [Finset.sum_comm]
  conv_rhs => enter [2, a]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_rhs => enter [2, a]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

/-! ### Contraction with the inner loop -/

/-- **The outer factor of `repBD s` contracted with a tensor `T`** is `-(1/i)` times the one-loop
vertex chain with the photon factor `∑ a b, (Δ V Δ)_{aν} T^{ab} Δ_{ρ'b}`. -/
theorem bdOuter_contract (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (k : Fin 4 → ℝ)
    (T : Fin 4 → Fin 4 → ℂ) :
    ∑ ρ, ∑ σ, bdOuter P p kext α β μ k ρ σ * T ρ σ =
      -(1 / I) * vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p + kext - k))
        (QED.OneLoop.electronPropagator P.m P.ε (p - k))
        (fun ν ρ' => ∑ a, ∑ b, photonInsertion P.δ₃ P.mγ P.Λ P.ε k a ν * T a b *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k ρ' b) α β := by
  simp only [vertexChain, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, bdOuter,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, ρ]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, l0, 2, ρ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, l0]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [QED.TwoLoop.NestedVP.outerChain, photonPropagator_symm _ _ _ k l2 b]
  ring

/-- **The outer factor of `repDB s` contracted with a tensor `T`**. -/
theorem dbOuter_contract (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (k : Fin 4 → ℝ)
    (T : Fin 4 → Fin 4 → ℂ) :
    ∑ ρ, ∑ σ, dbOuter P p kext α β μ k ρ σ * T ρ σ =
      -(1 / I) * vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p + kext - k))
        (QED.OneLoop.electronPropagator P.m P.ε (p - k))
        (fun ν ρ' => ∑ a, ∑ b, QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k ν a * T a b *
          photonInsertion P.δ₃ P.mγ P.Λ P.ε k ρ' b) α β := by
  simp only [vertexChain, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, dbOuter,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, ρ]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, l0, 2, ρ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, l0]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [QED.TwoLoop.NestedVP.outerChain, photonPropagator_symm _ _ _ k l0 a]
  ring

/-- The photon factor of `bdOuter_contract` with `T = vpT A B k` is `(1/i) dbChain`. -/
theorem bd_photon_chain (mγ Λ ε δ₃ : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) (ν ρ' : Fin 4) :
    ∑ a, ∑ b, photonInsertion δ₃ mγ Λ ε k a ν * vpT A B k a b *
        QED.OneLoop.photonPropagator mγ Λ ε k ρ' b =
      (1 / I) * dbChain mγ Λ ε δ₃ A B k ν ρ' := by
  unfold photonInsertion dbChain
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Eq.trans ?_ (sum4_reindex _)
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [photonPropagator_symm _ _ _ k a c, photonCtFactor_comm _ _ c d,
    photonPropagator_symm _ _ _ k ρ' b]
  ring

/-- The photon factor of `dbOuter_contract` with `T = vpT A B k` is `(1/i) bdChain`. -/
theorem db_photon_chain (mγ Λ ε δ₃ : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) (ν ρ' : Fin 4) :
    ∑ a, ∑ b, QED.OneLoop.photonPropagator mγ Λ ε k ν a * vpT A B k a b *
        photonInsertion δ₃ mγ Λ ε k ρ' b =
      (1 / I) * bdChain mγ Λ ε δ₃ A B k ν ρ' := by
  unfold photonInsertion bdChain
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [photonPropagator_symm _ _ _ k ρ' d, photonCtFactor_comm _ _ d c]
  ring

theorem dbChain_eq_bdChain (mγ Λ ε δ₃ : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) :
    dbChain mγ Λ ε δ₃ A B k = bdChain mγ Λ ε δ₃ A B k := by
  funext ν ρ
  rw [dbChain_eq, bdChain_eq]

theorem neg_one_div_I_mul_one_div_I : -(1 / I) * (1 / I) = (1 : ℂ) := by
  rw [neg_mul, div_mul_div_comm, one_mul, I_mul_I]
  norm_num

/-- **The outer integrand of `repBD s` with the inner loop in closed form** is the one-loop vertex
chain with the photon chain `bdChain`, at the momenta `p + kext - k`, `p - k`. -/
theorem outerF_bdOuter (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (k : Fin 4 → ℝ) :
    outerF P (bdOuter P p kext α β μ) k =
      vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p + kext - k))
        (QED.OneLoop.electronPropagator P.m P.ε (p - k))
        (bdChain P.mγ P.Λ P.ε P.δ₃ (I * vpLoopEps P P.ε (Minkowski.dot k k))
          ((P.ε : ℂ) * vpExtraEps P P.ε (Minkowski.dot k k)) k) α β := by
  unfold outerF
  rw [bdOuter_contract]
  simp only [bd_photon_chain, dbChain_eq_bdChain]
  rw [vertexChain_smul_photon, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
    neg_one_div_I_mul_one_div_I, one_mul]

/-- **The outer integrand of `repDB s` with the inner loop in closed form**, as
`outerF_bdOuter`. -/
theorem outerF_dbOuter (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (k : Fin 4 → ℝ) :
    outerF P (dbOuter P p kext α β μ) k =
      vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p + kext - k))
        (QED.OneLoop.electronPropagator P.m P.ε (p - k))
        (bdChain P.mγ P.Λ P.ε P.δ₃ (I * vpLoopEps P P.ε (Minkowski.dot k k))
          ((P.ε : ℂ) * vpExtraEps P P.ε (Minkowski.dot k k)) k) α β := by
  unfold outerF
  rw [dbOuter_contract]
  simp only [db_photon_chain]
  rw [vertexChain_smul_photon, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
    neg_one_div_I_mul_one_div_I, one_mul]

end QED.ChainProof.HCSide

end
