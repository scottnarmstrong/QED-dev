/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBPF
public import QED.ChainProof.SetCRegDispCtLoBRadial
public import QED.TwoLoop.VPHalfAtLimitPauli
import QED.OneLoop.VertexSpatial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The doubled vertex with one photon denominator: the Feynman-parameter form of its value

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), layer 5 of the
plan (the value of the doubled vertex). By the partial fractions of
`QED/ChainProof/SetCRegDispCtLoBPF.lean`, the limits of the doubled vertex reduce to
`QED.ChainProof.CtLoB.dblOneLimit`, the doubled vertex with **one** photon denominator. For a
numerator built from the frozen one-loop vertex numerator `N_{μij}`
(`vChain c = Σ c_{μij} N_{μij}`, e.g. the Pauli-projected Feynman-gauge chain,
`pauliChain_eq_vChain`), the spatial integral of `QED/ChainProof/SetCRegDispCtLoBRadial.lean` at
order one and the covariant contraction `-vF(E₀, E₀) + Σₖ vF(Eₖ, Eₖ) = 4 γ^μ` give the value
as an explicit integral over the Feynman square, with no loop integral left:

`dblOneLimit = ∫ 6 x_d y² (i (π²/12) 4 Σ c_{μij} γ^μ_{ij} / Δ + i (π²/6) vChain c (-K) / Δ²)`,

`Δ = feynmanMass m M x y p' p`, `K = y (x p' + (1 - x) p)` (`dblOneLimit_vChain`). This is the
doubled analogue of the closed form `QED.OneLoop.VertexLimit.integral_timeT_zero_sub` of the
one-loop vertex: formally `-∂/∂m_d²` of it, `x_d y` being `∂Δ/∂m_d²`.

* `sum_quad_aux`, `cons_sub_shiftKs`, `vChain_cons_sub_shiftKs`: the quadratic decomposition;
* `sum_vertexForm_diag_sub_alphaN`: the covariant contraction for a vertex chain;
* **`dblOneLimit_vChain`**: the value above;
* `pauliChain_eq_vChain`: the Pauli-projected chain as a vertex chain.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.TwoLoop.VPHalfAtLimit

theorem sum_quad_aux {X : Type*} [Fintype X] (c a : X → ℂ) (b : X → Fin 3 → ℂ)
    (d : X → Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℝ) :
    ∑ x, c x * (a x - ∑ k, (w k : ℂ) * b x k + ∑ k, ∑ l, ((w k * w l : ℝ) : ℂ) * d x k l) =
      ∑ x, c x * a x + ∑ k, (w k : ℂ) * ∑ x, c x * -b x k +
        ∑ k, ∑ l, ((w k * w l : ℝ) : ℂ) * ∑ x, c x * d x k l := by
  simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun x i => c x * ((w i : ℂ) * b x i))]
  have h3 : ∑ x, ∑ x_1, ∑ i, c x * (((w x_1 * w i : ℝ) : ℂ) * d x x_1 i) =
      ∑ x_1, ∑ i, ∑ x, c x * (((w x_1 * w i : ℝ) : ℂ) * d x x_1 i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [h3, sub_eq_add_neg]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl (congrArg _ ?_)) ?_
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring


theorem cons_sub_shiftKs (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) (w : Fin 3 → ℝ) :
    (Fin.cons (-shiftK p' p z 0) (w - shiftKs p' p z) : Fin 4 → ℝ) =
      (Fin.cons 0 w : Fin 4 → ℝ) - shiftK p' p z := by
  funext q
  refine Fin.cases ?_ (fun k => ?_) q <;> simp [shiftKs]

/-- The index set  of the entries of the vertex numerator. -/
abbrev VIdx : Type := Fin 4 × Fin 4 × Fin 4

/-- A combination of entries of the frozen vertex numerator. -/
noncomputable def vChain (m : ℝ) (p' p : Fin 4 → ℝ) (c : VIdx → ℂ) (ℓ : Fin 4 → ℝ) : ℂ :=
  ∑ x, c x * vertexNumerator m p' p x.1 ℓ x.2.1 x.2.2

theorem continuous_vChain (m : ℝ) (p' p : Fin 4 → ℝ) (c : VIdx → ℂ) :
    Continuous (vChain m p' p c) :=
  continuous_finsetSum _ fun x _ =>
    continuous_const.mul (continuous_vertexNumerator m p' p x.1 x.2.1 x.2.2)

theorem exists_norm_vChain_le (m : ℝ) (p' p : Fin 4 → ℝ) (c : VIdx → ℂ) :
    ∃ C : ℝ, ∀ ℓ, ‖vChain m p' p c ℓ‖ ≤ C * (1 + ‖ℓ‖) ^ 2 := by
  choose C hC using fun x : VIdx => exists_norm_vertexNumerator_le m p' p x.1 x.2.1 x.2.2
  refine ⟨∑ x, ‖c x‖ * C x, fun ℓ => ?_⟩
  unfold vChain
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x ℓ) (norm_nonneg _)

theorem vChain_cons_sub_shiftKs (m : ℝ) (p' p : Fin 4 → ℝ) (c : VIdx → ℂ) (z : ℝ × ℝ)
    (w : Fin 3 → ℝ) :
    vChain m p' p c (Fin.cons (-shiftK p' p z 0) (w - shiftKs p' p z) : Fin 4 → ℝ) =
      vChain m p' p c (-shiftK p' p z) +
        ∑ k, (w k : ℂ) * ∑ x, c x *
          -(vertexForm x.1 ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
              Dirac.slash (p' - shiftK p' p z)) (Dirac.slash (Pi.single k.succ 1)) x.2.1 x.2.2 +
            vertexForm x.1 (Dirac.slash (Pi.single k.succ 1))
              ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p - shiftK p' p z))
              x.2.1 x.2.2) +
        ∑ k, ∑ l, ((w k * w l : ℝ) : ℂ) * ∑ x, c x *
          vertexForm x.1 (Dirac.slash (Pi.single k.succ 1)) (Dirac.slash (Pi.single l.succ 1))
            x.2.1 x.2.2 := by
  unfold vChain
  simp only [cons_sub_shiftKs, vertexNumerator_cons_zero_sub]
  exact sum_quad_aux _ _ _ _ w

theorem sum_vertexForm_diag_sub_alphaN (m : ℝ) (p' p : Fin 4 → ℝ) (c : VIdx → ℂ) :
    (∑ k : Fin 3, ∑ x, c x * vertexForm x.1 (Dirac.slash (Pi.single k.succ 1))
        (Dirac.slash (Pi.single k.succ 1)) x.2.1 x.2.2) -
      ∑ x, c x * alphaN m p' p x.1 x.2.1 x.2.2 =
      4 * ∑ x, c x * Dirac.gamma x.1 x.2.1 x.2.2 := by
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := neg_vertexForm_time_add_sum_vertexForm_space x.1 x.2.1 x.2.2
  rw [alphaN_eq, cons_one_zero_eq_single, ← Finset.mul_sum]
  linear_combination c x * h

/-- **The doubled vertex with one photon denominator and a vertex-chain numerator.** -/
theorem dblOneLimit_vChain {m M : ℝ} (hm : 0 < m) (hM : 0 < M) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (c : VIdx → ℂ) (d : Fin 2) :
    dblOneLimit (∑ x, c x * alphaN m p' p x.1 x.2.1 x.2.2) (vChain m p' p c) m M d p' p =
      ∫ z, dblWt d 0 z *
        (I * ((π ^ 2 / 12 : ℝ) : ℂ) * (4 * ∑ x, c x * Dirac.gamma x.1 x.2.1 x.2.2) /
            (feynmanMass m M z.1 z.2 p' p : ℂ) +
          I * ((π ^ 2 / 6 : ℝ) : ℂ) * vChain m p' p c (-shiftK p' p z) /
            (feynmanMass m M z.1 z.2 p' p : ℂ) ^ 2) ∂feynmanMeasure := by
  obtain ⟨CN, hNb⟩ := exists_norm_vChain_le m p' p c
  have hΔ : ∀ z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1, 0 < feynmanMass m M z.1 z.2 p' p :=
    fun z hz => feynmanMass_pos_of_pos hm hM hp' hp hp0' hp0 (Ioc_prod_subset hz)
  unfold dblOneLimit
  rw [integral_spatialW_zero (continuous_dblWt d 0) (fun z hz => dblWt_norm_le d 0 hz) hm hM
    hp' hp hp0' hp0 (continuous_vChain m p' p c) _ hNb le_rfl 0 _ _ _ hΔ
    (fun z _ w => vChain_cons_sub_shiftKs m p' p c z w)]
  refine integral_congr_ae (ae_feynmanMeasure.mono fun z hz => ?_)
  dsimp only
  rw [dblTimeY_zero _ _ _ (hΔ z hz), sum_vertexForm_diag_sub_alphaN]


open QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit in
/-- The Pauli-projected Feynman-gauge chain is a vertex chain. -/
theorem pauliChain_eq_vChain (e m : ℝ) (p' p : Fin 4 → ℝ) :
    pauliChain e m p' p =
      vChain m p' p (fun x => pauliWt m p' p x.1 x.2.1 x.2.2 * kappa e) := by
  funext k
  rw [QED.TwoLoop.VPHalfAtLimit.pauliChain_eq_sum, vChain]
  simp only [Fintype.sum_prod_type]

end QED.ChainProof.CtLoB

end
