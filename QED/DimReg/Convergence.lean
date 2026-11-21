/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Power counting on the orthant: a convergence criterion

A seed for the generic convergence theorem of layer L1. The orthant `(0, ∞)^N` is the union
of the `2^N` boxes `B_T = {x | xᵢ > 1 for i ∈ T, 0 < xᵢ ≤ 1 for i ∉ T}`, `T ⊆ Fin N`. If on
each box a function is dominated by a monomial `C ∏ᵢ xᵢ ^ e_{T,i}` whose exponents satisfy
the one-dimensional power counting (`e_{T,i} > -1` where `xᵢ → 0` is allowed, `e_{T,i} < -1`
where `xᵢ → ∞` is allowed), then the function is integrable on the orthant.

For a Feynman integral the monomial bounds hold only after a sector decomposition
(Hepp sectors and their blow-ups, which turn the overlapping singularities into monomial
ones); this file supplies the last step, which is the same for every sector. The general
sector criterion then reads: if after each sector map the pulled-back integrand has monomial
box bounds of this kind, the integral converges. The campaign's `NoSubdivergence` criteria are
instances of such power counting at fixed `d = 4`.

## Main results

* `QED.DimReg.posOrthant_subset_iUnion_box`: the boxes cover the orthant.
* `QED.DimReg.integrableOn_box_monomial`: a monomial is integrable on a box under power counting.
* `QED.DimReg.integrableOn_posOrthant_of_box_bound`: the criterion.
* `QED.DimReg.lpConvergent_of_box_bound`: its Lee–Pomeransky form.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.DimReg

variable {N : ℕ}

/-- The side of a box in coordinate `i`: `(1, ∞)` if `i ∈ T` and `(0, 1]` otherwise. -/
def boxSide (T : Finset (Fin N)) (i : Fin N) : Set ℝ := if i ∈ T then Ioi 1 else Ioc 0 1

/-- The box `B_T` of the orthant: `xᵢ > 1` for `i ∈ T` and `0 < xᵢ ≤ 1` for `i ∉ T`. -/
def box (T : Finset (Fin N)) : Set (Fin N → ℝ) := univ.pi (boxSide T)

theorem measurableSet_boxSide (T : Finset (Fin N)) (i : Fin N) :
    MeasurableSet (boxSide T i) := by
  unfold boxSide; split_ifs <;> measurability

theorem measurableSet_box (T : Finset (Fin N)) : MeasurableSet (box T) :=
  MeasurableSet.univ_pi (measurableSet_boxSide T)

/-- The boxes cover the open orthant. -/
theorem posOrthant_subset_iUnion_box : posOrthant N ⊆ ⋃ T : Finset (Fin N), box T := by
  intro x hx
  rw [mem_posOrthant] at hx
  classical
  refine mem_iUnion.mpr ⟨Finset.univ.filter fun i => 1 < x i, ?_⟩
  simp only [box, mem_pi, mem_univ, forall_const, boxSide, Finset.mem_filter, Finset.mem_univ,
    true_and]
  intro i
  split_ifs with h
  · exact h
  · exact ⟨hx i, not_lt.mp h⟩

/-- One-dimensional power counting on a side of a box. -/
theorem integrableOn_boxSide_rpow {T : Finset (Fin N)} {i : Fin N} {e : ℝ}
    (hsmall : i ∉ T → -1 < e) (hlarge : i ∈ T → e < -1) :
    IntegrableOn (fun t : ℝ => t ^ e) (boxSide T i) := by
  unfold boxSide
  split_ifs with h
  · exact integrableOn_Ioi_rpow_of_lt (hlarge h) zero_lt_one
  · rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (hsmall h)

/-- A monomial `∏ᵢ xᵢ ^ eᵢ` is integrable on the box `B_T` when `eᵢ > -1` for `i ∉ T` and
`eᵢ < -1` for `i ∈ T`. -/
theorem integrableOn_box_monomial {T : Finset (Fin N)} {e : Fin N → ℝ}
    (hsmall : ∀ i, i ∉ T → -1 < e i) (hlarge : ∀ i, i ∈ T → e i < -1) :
    IntegrableOn (fun x : Fin N → ℝ => ∏ i, x i ^ e i) (box T) := by
  unfold IntegrableOn box
  rw [volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod_dep (f := fun i (t : ℝ) => t ^ e i)
    fun i => integrableOn_boxSide_rpow (hsmall i) (hlarge i)

/-- **Box power counting.** A function on the orthant that is a.e. strongly measurable and is
dominated on each box `B_T` by `C_T ∏ᵢ xᵢ ^ e_{T,i}`, with `e_{T,i} > -1` for `i ∉ T` and
`e_{T,i} < -1` for `i ∈ T`, is integrable on the orthant. -/
theorem integrableOn_posOrthant_of_box_bound {E : Type*} [NormedAddCommGroup E]
    {f : (Fin N → ℝ) → E} (hf : AEStronglyMeasurable f (volume.restrict (posOrthant N)))
    (C : Finset (Fin N) → ℝ) (e : Finset (Fin N) → Fin N → ℝ)
    (hsmall : ∀ T i, i ∉ T → -1 < e T i) (hlarge : ∀ T i, i ∈ T → e T i < -1)
    (hbound : ∀ T, ∀ x ∈ box T ∩ posOrthant N, ‖f x‖ ≤ C T * ∏ i, x i ^ e T i) :
    IntegrableOn f (posOrthant N) := by
  have hcover : posOrthant N = ⋃ T : Finset (Fin N), box T ∩ posOrthant N := by
    rw [← iUnion_inter, inter_eq_right.mpr posOrthant_subset_iUnion_box]
  rw [hcover, integrableOn_finite_iUnion]
  intro T
  have hmeas : MeasurableSet (box T ∩ posOrthant N) :=
    (measurableSet_box T).inter (measurableSet_posOrthant N)
  refine Integrable.mono' (((integrableOn_box_monomial (hsmall T) (hlarge T)).mono_set
    inter_subset_left).const_mul (C T)) ?_ ?_
  · exact hf.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  · exact (ae_restrict_iff' hmeas).mpr (Filter.Eventually.of_forall fun x hx => hbound T x hx)

/-- **Box power counting, Lee–Pomeransky form.** If `G` is measurable and positive on the
orthant and the real integrand `∏ᵢ xᵢ ^ (re νᵢ - 1) · G(x) ^ (-re d / 2)` is dominated on each
box by a monomial obeying box power counting, then the Lee–Pomeransky integral converges
absolutely at `(ν, d)`. -/
theorem lpConvergent_of_box_bound {G : (Fin N → ℝ) → ℝ} (hG : Measurable G)
    (hpos : ∀ x ∈ posOrthant N, 0 < G x) (ν : Fin N → ℂ) (d : ℂ)
    (C : Finset (Fin N) → ℝ) (e : Finset (Fin N) → Fin N → ℝ)
    (hsmall : ∀ T i, i ∉ T → -1 < e T i) (hlarge : ∀ T i, i ∈ T → e T i < -1)
    (hbound : ∀ T, ∀ x ∈ box T ∩ posOrthant N,
      (∏ i, x i ^ ((ν i).re - 1)) * G x ^ (-(d.re / 2)) ≤ C T * ∏ i, x i ^ e T i) :
    LPConvergent G ν d :=
  integrableOn_posOrthant_of_box_bound (measurable_lpIntegrand hG ν d).aestronglyMeasurable
    C e hsmall hlarge fun T x hx => by
      rw [norm_lpIntegrand G ν d hx.2 (hpos x hx.2)]
      exact hbound T x hx

end QED.DimReg
