/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.ChargeRenormalization
public import QED.OneLoop.PauliLimit
import QED.Integration.ParametricSmooth
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Smoothness of the one-loop form factors in the momentum transfer

At fixed regulators `m, m_γ, Λ > 0` the on-shell form factors `A` and `B` of the one-loop
vertex are Feynman-parameter integrals of `formIntegrandAq m m_γ Λ s` and
`pauliIntegrand m (m_γ, Λ, s)` (`formFactorA_eq_q`, `formFactorB_eq`), where `s = q²`. This
module shows that both integrals are `C^∞` in `s` on `(-4m², ∞)`.

On the closed unit square, `x(1 - x) ∈ [0, 1/4]`, so `m² + x(1 - x)s > 0` when `s > -4m²`; hence
the Feynman mass `massDq m M s z` is positive for `M ≠ 0`. The integrands are therefore `C^∞` on
the open set where both Feynman masses are positive, and that set contains
`(-4m², ∞) ×ˢ [0, 1]²`. The result follows from
`QED.Integration.contDiffOn_integral_of_contDiffOn_prod`.

## Main statements

* `QED.OneLoop.VertexLimit.massDq_pos_of_neg_four_mul_sq_lt`: positivity of the Feynman mass.
* `QED.OneLoop.VertexLimit.contDiffOn_integral_formIntegrandAq`: smoothness of `A`.
* `QED.OneLoop.VertexLimit.contDiffOn_integral_pauliIntegrand`: smoothness of `B`.
-/

public section

open MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped ContDiff

namespace QED.OneLoop.VertexLimit

/-- For `s > -4m²` and `M ≠ 0`, the Feynman mass `massDq m M s z` is positive on the closed
unit square. -/
theorem massDq_pos_of_neg_four_mul_sq_lt {m M s : ℝ} (hm : m ≠ 0) (hM : M ≠ 0)
    (hs : -(4 * m ^ 2) < s) {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    0 < massDq m M s z := by
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
  have hm2 : 0 < m ^ 2 := by positivity
  have hxx0 : 0 ≤ z.1 * (1 - z.1) := mul_nonneg hx0 (by linarith)
  have hxx1 : z.1 * (1 - z.1) ≤ 1 / 4 := by nlinarith [sq_nonneg (z.1 - 1 / 2)]
  have hc : 0 < m ^ 2 + z.1 * (1 - z.1) * s := by
    rcases le_or_gt 0 s with h | h
    · have := mul_nonneg hxx0 h
      linarith
    · have : 1 / 4 * s ≤ z.1 * (1 - z.1) * s := mul_le_mul_of_nonpos_right hxx1 h.le
      linarith
  have h1 : 0 ≤ (1 - z.2) * M ^ 2 := mul_nonneg (by linarith) (sq_nonneg M)
  unfold massDq
  rcases eq_or_lt_of_le hy0 with h0 | hpos
  · rw [← h0]
    have : 0 < M ^ 2 := by positivity
    linarith
  · have : 0 < z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * s) := by positivity
    linarith

/-- The Feynman mass is a polynomial in `(s, z)`. -/
theorem contDiff_massDq (m M : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => massDq m M p.1 p.2) := by
  unfold massDq
  fun_prop

/-- The open set of `(s, z)` where both Feynman masses `massDq m m_γ` and `massDq m Λ` are
positive. -/
theorem isOpen_massDq_pos (m mγ Λ : ℝ) :
    IsOpen {p : ℝ × (ℝ × ℝ) | 0 < massDq m mγ p.1 p.2 ∧ 0 < massDq m Λ p.1 p.2} :=
  (isOpen_lt continuous_const (contDiff_massDq m mγ).continuous).inter
    (isOpen_lt continuous_const (contDiff_massDq m Λ).continuous)

/-- For `m, m_γ, Λ ≠ 0`, the set where both Feynman masses are positive contains
`(-4m², ∞) ×ˢ [0, 1]²`. -/
theorem Ioi_prod_subset_massDq_pos {m mγ Λ : ℝ} (hm : m ≠ 0) (hmγ : mγ ≠ 0) (hΛ : Λ ≠ 0) :
    Ioi (-(4 * m ^ 2)) ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      ⊆ {p : ℝ × (ℝ × ℝ) | 0 < massDq m mγ p.1 p.2 ∧ 0 < massDq m Λ p.1 p.2} :=
  fun _ hp => ⟨massDq_pos_of_neg_four_mul_sq_lt hm hmγ hp.1 hp.2,
    massDq_pos_of_neg_four_mul_sq_lt hm hΛ hp.1 hp.2⟩

/-- `feynmanMeasure` is carried by the closed unit square. -/
theorem ae_feynmanMeasure_mem_Icc :
    ∀ᵐ z ∂feynmanMeasure, z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
  ae_feynmanMeasure.mono fun _ hz => Ioc_prod_subset hz

/-- **Smoothness of `A(q²)`.** At fixed regulators `m, m_γ, Λ > 0`, the Feynman-parameter
integral of `formIntegrandAq` is `C^∞` in `s = q²` on `(-4m², ∞)`. -/
theorem contDiffOn_integral_formIntegrandAq {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) :
    ContDiffOn ℝ ∞ (fun s => ∫ z, formIntegrandAq m mγ Λ s z ∂feynmanMeasure)
      (Ioi (-(4 * m ^ 2))) := by
  set W := {p : ℝ × (ℝ × ℝ) | 0 < massDq m mγ p.1 p.2 ∧ 0 < massDq m Λ p.1 p.2}
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => massDq m mγ p.1 p.2) W :=
    (contDiff_massDq m mγ).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => massDq m Λ p.1 p.2) W :=
    (contDiff_massDq m Λ).contDiffOn
  have hne1 : ∀ p ∈ W, massDq m mγ p.1 p.2 ≠ 0 := fun p hp => hp.1.ne'
  have hne2 : ∀ p ∈ W, massDq m Λ p.1 p.2 ≠ 0 := fun p hp => hp.2.ne'
  have hlog : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => Real.log (massDq m Λ p.1 p.2 / massDq m mγ p.1 p.2)) W :=
    (h2.div h1 hne1).log fun p hp => (div_pos hp.2 hp.1).ne'
  have hinv : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => (massDq m mγ p.1 p.2)⁻¹ - (massDq m Λ p.1 p.2)⁻¹) W :=
    (h1.inv hne1).sub (h2.inv hne2)
  have hg : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => formIntegrandAq m mγ Λ p.1 p.2) W := by
    unfold formIntegrandAq
    have hpoly : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
        2 * ((1 - 4 * (1 - p.2.2) + (1 - p.2.2) ^ 2) * m ^ 2
          - ((1 - p.2.2) + (p.2.2 * p.2.1) * (p.2.2 * (1 - p.2.1))) * p.1)) := by
      fun_prop
    have hy : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => 2 * p.2.2) := by fun_prop
    exact hy.contDiffOn.mul (hlog.add ((contDiffOn_const.mul hinv).mul hpoly.contDiffOn))
  exact contDiffOn_integral_of_contDiffOn_prod (isCompact_Icc.prod isCompact_Icc)
    ae_feynmanMeasure_mem_Icc isOpen_Ioi (isOpen_massDq_pos m mγ Λ)
    (Ioi_prod_subset_massDq_pos hm.ne' hmγ.ne' hΛ.ne') hg

/-- **Smoothness of `B(q²)`.** At fixed regulators `m, m_γ, Λ > 0`, the Feynman-parameter
integral of `pauliIntegrand` is `C^∞` in `s = q²` on `(-4m², ∞)`. -/
theorem contDiffOn_integral_pauliIntegrand {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) :
    ContDiffOn ℝ ∞ (fun s => ∫ z, pauliIntegrand m (mγ, Λ, s) z ∂feynmanMeasure)
      (Ioi (-(4 * m ^ 2))) := by
  set W := {p : ℝ × (ℝ × ℝ) | 0 < massDq m mγ p.1 p.2 ∧ 0 < massDq m Λ p.1 p.2}
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => massDq m mγ p.1 p.2) W :=
    (contDiff_massDq m mγ).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => massDq m Λ p.1 p.2) W :=
    (contDiff_massDq m Λ).contDiffOn
  have hinv : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => (massDq m mγ p.1 p.2)⁻¹ - (massDq m Λ p.1 p.2)⁻¹) W :=
    (h1.inv fun p hp => hp.1.ne').sub (h2.inv fun p hp => hp.2.ne')
  have hc : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
      2 * p.2.2 * ((1 - p.2.2) - (1 - p.2.2) ^ 2) * m ^ 2) := by
    fun_prop
  have hg : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => pauliIntegrand m (mγ, Λ, p.1) p.2) W :=
    hc.contDiffOn.mul hinv
  exact contDiffOn_integral_of_contDiffOn_prod (isCompact_Icc.prod isCompact_Icc)
    ae_feynmanMeasure_mem_Icc isOpen_Ioi (isOpen_massDq_pos m mγ Λ)
    (Ioi_prod_subset_massDq_pos hm.ne' hmγ.ne' hΛ.ne') hg

end QED.OneLoop.VertexLimit

end
