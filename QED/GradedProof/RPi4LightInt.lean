/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SimplexMerge
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# (R-Π₄) step L7: an integrable power of the fermion parameter sum

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L7. The corner bound
of the light photon pair is a negative power of the sum `y` of the first `n` simplex
coordinates. Since `y ≥ xᵢ` for each of them, `y^{-q} ≤ ∏_{i<n} xᵢ^{-q/n}` off a null set, and
the product is integrable on the unit box for `q < n`.

* `headSum n x`: the sum of the first `n` coordinates;
* `headProd`, `integrableOn_headProd`: the product majorant;
* `integrableOn_headSum_rpow`: `y^{-q}` is integrable on the simplex for `0 ≤ q < n ≤ m`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.Integration.Feynman (simplexSet)

/-- The sum of the first `n` coordinates. -/
noncomputable def headSum {m : ℕ} (n : ℕ) (x : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, if (i : ℕ) < n then x i else 0

theorem continuous_headSum {m : ℕ} (n : ℕ) : Continuous (headSum (m := m) n) := by
  unfold headSum
  refine continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact continuous_apply i
  · exact continuous_const

theorem headSum_nonneg {m n : ℕ} {x : Fin m → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ headSum n x :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hx i]

theorem le_headSum {m n : ℕ} {x : Fin m → ℝ} (hx : ∀ i, 0 ≤ x i) {i : Fin m} (hi : (i : ℕ) < n) :
    x i ≤ headSum n x := by
  have h := Finset.single_le_sum (f := fun j : Fin m => if (j : ℕ) < n then x j else 0)
    (fun j _ => by split_ifs <;> simp [hx j]) (Finset.mem_univ i)
  simp only [hi, ite_true] at h
  exact h

/-- The product majorant `∏_{i < n} xᵢ^{-e}`. -/
noncomputable def headProd {m : ℕ} (n : ℕ) (e : ℝ) (x : Fin m → ℝ) : ℝ :=
  ∏ i : Fin m, if (i : ℕ) < n then x i ^ (-e) else 1

theorem integrableOn_headProd {m : ℕ} (n : ℕ) {e : ℝ} (he : e < 1) :
    IntegrableOn (headProd (m := m) n e) (Set.univ.pi fun _ => Icc (0 : ℝ) 1) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-e)) (Icc 0 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hf : ∀ i : Fin m, Integrable (fun t : ℝ => if (i : ℕ) < n then t ^ (-e) else 1)
      (volume.restrict (Icc (0 : ℝ) 1)) := fun i => by
    split_ifs
    · exact h1
    · exact integrable_const _
  have h := Integrable.fintype_prod hf
  rw [← Measure.restrict_pi_pi] at h
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [headProd]

/-- **`(∑_{i<n} xᵢ)^{-q}` is integrable on the simplex** for `0 ≤ q < n ≤ m`. -/
theorem integrableOn_headSum_rpow {m n : ℕ} (hn : n ≤ m) (hn0 : 0 < n) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q < n) : IntegrableOn (fun x : Fin m → ℝ => headSum n x ^ (-q)) (simplexSet m) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  set e := q / n with he_def
  have he1 : e < 1 := by rw [div_lt_one hn']; exact hq
  have he0 : 0 ≤ e := div_nonneg hq0 hn'.le
  have hm0 : 0 < m := by omega
  have hsub : simplexSet m ⊆ Set.univ.pi fun _ => Icc (0 : ℝ) 1 := fun x hx' i _ => by
    have hx := (QED.Integration.SimplexMerge.mem_simplexSet_iff_le hm0 x).mp hx'
    refine ⟨hx.1 i, ?_⟩
    calc x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
      _ ≤ 1 := hx.2
  have hP := (integrableOn_headProd (m := m) n he1).mono_set hsub
  refine hP.mono' (((continuous_headSum n).measurable.pow_const _).aestronglyMeasurable) ?_
  have hae : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ∀ i : Fin m, x i ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_all_iff]
    intro i
    exact Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) i 0
  filter_upwards [hae, ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet m)]
    with x hx hxS'
  have hxS := (QED.Integration.SimplexMerge.mem_simplexSet_iff_le hm0 x).mp hxS'
  have hpos : ∀ i, 0 < x i := fun i => lt_of_le_of_ne (hxS.1 i) (hx i).symm
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin m, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have hS : 0 < headSum n x := (hpos i₀).trans_le (le_headSum hxS.1 (by omega))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hS.le _)]
  have e1 : headSum n x ^ (-q) = ∏ i : Fin m, if (i : ℕ) < n then headSum n x ^ (-e) else 1 := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hc : (Finset.univ.filter fun i : Fin m => (i : ℕ) < n).card = n := by
      rw [Fin.card_filter_val_lt]
      omega
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hS.le]
    congr 1
    rw [he_def]
    field_simp
  rw [e1, headProd]
  refine Finset.prod_le_prod₀ (fun i _ => by split_ifs <;> positivity) (fun i _ => ?_)
  split_ifs with hi
  · exact Real.rpow_le_rpow_of_nonpos (hpos i) (le_headSum hxS.1 hi) (by linarith)
  · exact le_rfl

end QED.GradedProof.RPi4

end
