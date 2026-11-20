/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2TensorForm

/-!
# (R-Π₄) step L9, D3a: the null readout is homogeneous of degree two along the null ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D3a. The readout at `s = 0` of a class limit is the entry `(0, 1)` at the null vector
`n₀ = (1, 1, 0, 0)`. A dilation moves `n₀` along its ray, so the scaling of the class sum at
`s = 0` needs: **for a reflection-covariant tensor `W` (no transversality) that is continuous at
the origin along the null ray, `W(t n₀)⁰¹ = t² W(n₀)⁰¹` for `t > 0`** (`dec_null_smul`).

Proof: the boost `B_t` with `B_t n₀ = t n₀` is the product of the reflections in `e₁` and in
`a_t = (1 - t, -1 - t, 0, 0)`; with `p = (1 + t²)/2t`, `q = (t² - 1)/2t` its `(0, 1)` block is
`[[p, q], [q, p]]`. Boundedness of `W(t n₀)⁰⁰` as `t → 0⁺` forces
`X⁰⁰ + X¹¹ = X⁰¹ + X¹⁰ =: σ` (`X = W(n₀)`), then `W(t n₀)⁰¹ = t² σ/2 + (X⁰¹ - X¹⁰)/2`, and
`W(0)⁰¹ = 0` (the reflection in `e₀` fixes the origin) forces `X⁰¹ = X¹⁰`.
-/

@[expose] public section

open Complex Filter Topology
open QED.Dirac

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2
open QED.GradedProof.SE2 (nullVec dot_nullVec)

/-- The reflection vector `a_t = (1 - t, -1 - t, 0, 0)` of the boost. -/
def decBoostVec (t : ℝ) : Fin 4 → ℝ := ![1 - t, -1 - t, 0, 0]

theorem dec_dot_boostVec (t : ℝ) : Minkowski.dot (decBoostVec t) (decBoostVec t) = 4 * t := by
  simp only [Minkowski.dot_eq, decBoostVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem dec_reflectMatrix_boostVec {t : ℝ} (ht : t ≠ 0) :
    reflectMatrix (decBoostVec t) =
      !![(1 + t ^ 2) / (2 * t), (1 - t ^ 2) / (2 * t), 0, 0;
        -((1 - t ^ 2) / (2 * t)), -((1 + t ^ 2) / (2 * t)), 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext μ α
  simp only [reflectMatrix, Matrix.of_apply, dec_dot_boostVec]
  fin_cases μ <;> fin_cases α <;>
    simp [Minkowski.lower_eq, decBoostVec] <;>
    field_simp <;> ring

/-- The first reflection: `R_{e₁} n₀ = (1, -1, 0, 0)`. -/
theorem dec_reflect_e1_nullVec :
    reflect (Pi.single 1 1) nullVec = (![1, -1, 0, 0] : Fin 4 → ℝ) := by
  funext μ
  fin_cases μ <;> norm_num [reflect, Minkowski.dot_eq, nullVec]

/-- The second reflection: `R_{a_t} (1, -1, 0, 0) = t n₀`. -/
theorem dec_reflect_boostVec {t : ℝ} (ht : t ≠ 0) :
    reflect (decBoostVec t) (![1, -1, 0, 0] : Fin 4 → ℝ) = t • nullVec := by
  funext μ
  simp only [reflect, dec_dot_boostVec]
  fin_cases μ <;> simp [Minkowski.dot_eq, nullVec, decBoostVec] <;>
    field_simp <;> ring

variable {T : ℝ} {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

/-- **The boost formula** for the entries `00` and `01` of `W(t n₀)`. -/
theorem dec_boost_entries (hcov : TCov T W) (hT : -T ^ 2 < 0) {t : ℝ} (ht : 0 < t) :
    (4 * t ^ 2 : ℂ) * W (t • nullVec) 0 0 =
        (1 + t ^ 2) ^ 2 * W nullVec 0 0 + (t ^ 2 - 1) * (1 + t ^ 2) *
          (W nullVec 0 1 + W nullVec 1 0) + (t ^ 2 - 1) ^ 2 * W nullVec 1 1 ∧
      (4 * t ^ 2 : ℂ) * W (t • nullVec) 0 1 =
        (1 + t ^ 2) * (t ^ 2 - 1) * (W nullVec 0 0 + W nullVec 1 1) +
          (1 + t ^ 2) ^ 2 * W nullVec 0 1 + (t ^ 2 - 1) ^ 2 * W nullVec 1 0 := by
  have hn : -T ^ 2 < Minkowski.dot nullVec nullVec := by rwa [dot_nullVec]
  have hn' : -T ^ 2 < Minkowski.dot (![1, -1, 0, 0] : Fin 4 → ℝ) ![1, -1, 0, 0] := by
    simpa [Minkowski.dot_eq] using hT
  have h1 := hcov _ (dot_single_self 1) _ hn
  rw [dec_reflect_e1_nullVec] at h1
  have ha : Minkowski.dot (decBoostVec t) (decBoostVec t) ≠ 0 := by
    rw [dec_dot_boostVec]; positivity
  have h2 := hcov _ ha _ hn'
  rw [dec_reflect_boostVec ht.ne', h1] at h2
  rw [h2]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  simp only [rAct_of_eq (dec_reflectMatrix_boostVec ht.ne'), rAct_single, Fin.sum_univ_four]
  simp [VP2.flip]
  constructor <;> field_simp <;> ring

/-- **The null readout is homogeneous of degree two along the null ray.** -/
theorem dec_null_smul (hcov : TCov T W) (hT : -T ^ 2 < 0)
    (hcont : ∀ μ ν : Fin 4, Tendsto (fun t : ℝ => W (t • nullVec) μ ν) (𝓝[>] 0)
      (𝓝 (W 0 μ ν))) {t : ℝ} (ht : 0 < t) :
    W (t • nullVec) 0 1 = ((t ^ 2 : ℝ) : ℂ) * W nullVec 0 1 := by
  set X := W nullVec
  have hB := fun {t : ℝ} (ht : 0 < t) => dec_boost_entries hcov hT ht
  -- the cone: `X⁰⁰ - X⁰¹ - X¹⁰ + X¹¹ = 0`
  have hcone : X 0 0 - X 0 1 - X 1 0 + X 1 1 = 0 := by
    have hl : Tendsto (fun t : ℝ => (4 * (t : ℂ) ^ 2) * W (t • nullVec) 0 0) (𝓝[>] 0)
        (𝓝 ((4 * ((0 : ℝ) : ℂ) ^ 2) * W 0 0 0)) := by
      refine Tendsto.mul (Tendsto.const_mul _ (Tendsto.pow ?_ 2)) (hcont 0 0)
      exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hr : Tendsto (fun t : ℝ => (1 + (t : ℂ) ^ 2) ^ 2 * X 0 0 + ((t : ℂ) ^ 2 - 1) *
        (1 + (t : ℂ) ^ 2) * (X 0 1 + X 1 0) + ((t : ℂ) ^ 2 - 1) ^ 2 * X 1 1) (𝓝[>] 0)
        (𝓝 ((1 + ((0 : ℝ) : ℂ) ^ 2) ^ 2 * X 0 0 + (((0 : ℝ) : ℂ) ^ 2 - 1) *
          (1 + ((0 : ℝ) : ℂ) ^ 2) * (X 0 1 + X 1 0) + (((0 : ℝ) : ℂ) ^ 2 - 1) ^ 2 * X 1 1)) :=
      ((by fun_prop : Continuous fun t : ℝ => (1 + (t : ℂ) ^ 2) ^ 2 * X 0 0 +
        ((t : ℂ) ^ 2 - 1) * (1 + (t : ℂ) ^ 2) * (X 0 1 + X 1 0) +
        ((t : ℂ) ^ 2 - 1) ^ 2 * X 1 1).tendsto 0).mono_left nhdsWithin_le_nhds
    have e := tendsto_nhds_unique hl (hr.congr' (by
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact (hB ht).1.symm))
    simp only [ofReal_zero] at e
    linear_combination -e
  -- the constant part: `W(t n₀)⁰¹ - t² σ/2 = (X⁰¹ - X¹⁰)/2`
  have hconst : ∀ t : ℝ, 0 < t → W (t • nullVec) 0 1 - (t : ℂ) ^ 2 * (X 0 1 + X 1 0) / 2 =
      (X 0 1 - X 1 0) / 2 := by
    intro t ht
    have h := (hB ht).2
    have ht' : (4 * (t : ℂ) ^ 2) ≠ 0 := by
      have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 this)
    refine mul_left_cancel₀ ht' ?_
    linear_combination h + ((1 + (t : ℂ) ^ 2) * ((t : ℂ) ^ 2 - 1)) * hcone
  have h00 : W 0 0 1 = 0 := by
    refine eq_zero_of_flip hcov 0 rfl (by simpa [Minkowski.dot_eq] using hT) (Or.inl ?_)
    exact ⟨rfl, by decide⟩
  have hdiff : X 0 1 - X 1 0 = 0 := by
    have hl : Tendsto (fun t : ℝ => W (t • nullVec) 0 1 - (t : ℂ) ^ 2 * (X 0 1 + X 1 0) / 2)
        (𝓝[>] 0) (𝓝 (W 0 0 1 - ((0 : ℝ) : ℂ) ^ 2 * (X 0 1 + X 1 0) / 2)) := by
      refine (hcont 0 1).sub (Tendsto.div_const (Tendsto.mul_const _ (Tendsto.pow ?_ 2)) _)
      exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have e := tendsto_nhds_unique hl (tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact (hconst t ht).symm))
    rw [h00] at e
    simp only [ofReal_zero] at e
    linear_combination -2 * e
  have h2 := hconst t ht
  push_cast
  linear_combination h2 + (1 - (t : ℂ) ^ 2) / 2 * hdiff

end QED.GradedProof.RPi4

end
