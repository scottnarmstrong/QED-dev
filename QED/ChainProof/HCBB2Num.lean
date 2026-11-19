/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.VertexAlgebra
public import QED.OneLoop.VertexEnergyFirst
public import QED.Algebra.Dirac
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix

/-!
# The numerators of the bubble–bubble vertex entries

Helper level, Phase 5 Stage 1a, toward `QED.ChainProof.HCBB.BBInsertionLimit`. The engine of
`QED/TwoLoop/VPHalfAt*.lean` takes a numerator `N` that is continuous, quadratic in the loop
energy with leading coefficient independent of the spatial momentum, and of quadratic growth
(`QuadN`). Every matrix entry of the one-loop vertex with the double insertion splits into four
such numerators, once the longitudinal part `k_ν k_ρ` of the insertion is reduced with
`ℓ̸ ℓ̸ = -ℓ²`:

* `numG`: the Feynman-gauge entry `∑ g_{νρ} (γ^ρ (m - (p'+ℓ)̸) γ^μ (m - (p+ℓ)̸) γ^ν)_{ij}` (the
  frozen vertex numerator);
* `numS`: `ℓ² γ^μ_{ij}`;
* `numL`: `(ℓ̸ (m - p̸') γ^μ + γ^μ (m - p̸) ℓ̸)_{ij}`;
* `numQ`: `(ℓ̸ (m - p̸') γ^μ (m - p̸) ℓ̸)_{ij}`.

`quadN_numG`, `quadN_numS`, `quadN_numL`, `quadN_numQ` prove `QuadN` for each;
`slash_mul_massSub`, `massSub_mul_slash` are the reductions
`ℓ̸ (m - (p'+ℓ)̸) = ℓ² + ℓ̸ (m - p̸')` and `(m - (p+ℓ)̸) ℓ̸ = ℓ² + (m - p̸) ℓ̸`.
-/

@[expose] public section

open Complex Matrix

namespace QED.ChainProof.HCBB2

open QED.OneLoop

/-! ### The predicate -/

/-- **A numerator admissible for the engine**: continuous, quadratic in the loop energy with
constant leading coefficient, and of quadratic growth. -/
structure QuadN (N : (Fin 4 → ℝ) → ℂ) : Prop where
  cont : Continuous N
  quad : ∃ α : ℂ, ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
    N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ
  bound : ∃ C : ℝ, ∀ ℓ, ‖N ℓ‖ ≤ C * (1 + ‖ℓ‖) ^ 2

/-- `QuadN` for the entries of a matrix-valued function of the loop momentum. -/
theorem quadN_entry {F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (hc : Continuous F)
    (hq : ∃ A : Matrix (Fin 4) (Fin 4) ℂ, ∀ v : Fin 3 → ℝ, ∃ B C : Matrix (Fin 4) (Fin 4) ℂ,
      ∀ t : ℝ, F (Fin.cons t v : Fin 4 → ℝ) = ((t : ℂ) ^ 2) • A + (t : ℂ) • B + C)
    (hb : ∃ K : ℝ, ∀ ℓ i j, ‖F ℓ i j‖ ≤ K * (1 + ‖ℓ‖) ^ 2) (i j : Fin 4) :
    QuadN fun ℓ => F ℓ i j := by
  refine ⟨hc.matrix_elem i j, ?_, ?_⟩
  · obtain ⟨A, hA⟩ := hq
    refine ⟨A i j, fun v => ?_⟩
    obtain ⟨B, C, h⟩ := hA v
    refine ⟨B i j, C i j, fun t => ?_⟩
    rw [h t]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · obtain ⟨K, hK⟩ := hb
    exact ⟨K, fun ℓ => hK ℓ i j⟩

/-! ### Norm bounds -/

section Norms

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem norm_entry_le (A : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) : ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (f := fun j => ‖A i j‖₊) (fun _ _ => zero_le)
      (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i))
  exact_mod_cast h

theorem norm_lower_le' (ℓ : Fin 4 → ℝ) (κ : Fin 4) : ‖Minkowski.lower ℓ κ‖ ≤ ‖ℓ‖ := by
  have h := norm_le_pi_norm ℓ
  rw [Minkowski.lower_eq]
  fin_cases κ
  · simpa using h 0
  · simpa using h 1
  · simpa using h 2
  · simpa using h 3

private theorem norm_slash_le' (ℓ : Fin 4 → ℝ) :
    ‖Dirac.slash ℓ‖ ≤ (∑ κ, ‖Dirac.gamma κ‖) * ‖ℓ‖ := by
  rw [Dirac.slash, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
  rw [norm_smul, Complex.norm_real, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_lower_le' ℓ κ) (norm_nonneg _)

/-- `‖ℓ̸ K ℓ̸‖ ≤ G² ‖K‖ (1 + ‖ℓ‖)²`. -/
private theorem exists_norm_slash_mul_mul_slash_le (K : Matrix (Fin 4) (Fin 4) ℂ) :
    ∃ C : ℝ, ∀ ℓ, ‖Dirac.slash ℓ * K * Dirac.slash ℓ‖ ≤ C * (1 + ‖ℓ‖) ^ 2 := by
  set G := ∑ κ, ‖Dirac.gamma κ‖
  have hG : 0 ≤ G := Finset.sum_nonneg fun κ _ => norm_nonneg _
  refine ⟨G * ‖K‖ * G, fun ℓ => ?_⟩
  have h1 := norm_slash_le' ℓ
  have hℓ : ‖ℓ‖ ≤ 1 + ‖ℓ‖ := by linarith
  calc ‖Dirac.slash ℓ * K * Dirac.slash ℓ‖ ≤ ‖Dirac.slash ℓ‖ * ‖K‖ * ‖Dirac.slash ℓ‖ := by
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        exact norm_mul_le _ _
    _ ≤ (G * ‖ℓ‖) * ‖K‖ * (G * ‖ℓ‖) := by gcongr
    _ ≤ (G * (1 + ‖ℓ‖)) * ‖K‖ * (G * (1 + ‖ℓ‖)) := by gcongr
    _ = G * ‖K‖ * G * (1 + ‖ℓ‖) ^ 2 := by ring

/-- `‖ℓ̸ K₁ + K₂ ℓ̸‖ ≤ G (‖K₁‖ + ‖K₂‖) (1 + ‖ℓ‖)²`. -/
private theorem exists_norm_slash_mul_add_mul_slash_le (K₁ K₂ : Matrix (Fin 4) (Fin 4) ℂ) :
    ∃ C : ℝ, ∀ ℓ, ‖Dirac.slash ℓ * K₁ + K₂ * Dirac.slash ℓ‖ ≤ C * (1 + ‖ℓ‖) ^ 2 := by
  set G := ∑ κ, ‖Dirac.gamma κ‖
  have hG : 0 ≤ G := Finset.sum_nonneg fun κ _ => norm_nonneg _
  refine ⟨G * (‖K₁‖ + ‖K₂‖), fun ℓ => ?_⟩
  have h1 := norm_slash_le' ℓ
  have hℓ : ‖ℓ‖ ≤ (1 + ‖ℓ‖) ^ 2 := by nlinarith [norm_nonneg ℓ]
  calc ‖Dirac.slash ℓ * K₁ + K₂ * Dirac.slash ℓ‖
      ≤ ‖Dirac.slash ℓ‖ * ‖K₁‖ + ‖K₂‖ * ‖Dirac.slash ℓ‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ (G * ‖ℓ‖) * ‖K₁‖ + ‖K₂‖ * (G * ‖ℓ‖) := by gcongr
    _ = G * (‖K₁‖ + ‖K₂‖) * ‖ℓ‖ := by ring
    _ ≤ G * (‖K₁‖ + ‖K₂‖) * (1 + ‖ℓ‖) ^ 2 := by gcongr

end Norms

theorem norm_dot_le (ℓ : Fin 4 → ℝ) : ‖Minkowski.dot ℓ ℓ‖ ≤ 4 * (1 + ‖ℓ‖) ^ 2 := by
  have h := norm_le_pi_norm ℓ
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  rw [Real.norm_eq_abs] at h0 h1 h2 h3 ⊢
  rw [Minkowski.dot_eq]
  have hn := norm_nonneg ℓ
  have e0 : ℓ 0 * ℓ 0 ≤ ‖ℓ‖ ^ 2 := by nlinarith [abs_mul_abs_self (ℓ 0), abs_nonneg (ℓ 0)]
  have e1 : ℓ 1 * ℓ 1 ≤ ‖ℓ‖ ^ 2 := by nlinarith [abs_mul_abs_self (ℓ 1), abs_nonneg (ℓ 1)]
  have e2 : ℓ 2 * ℓ 2 ≤ ‖ℓ‖ ^ 2 := by nlinarith [abs_mul_abs_self (ℓ 2), abs_nonneg (ℓ 2)]
  have e3 : ℓ 3 * ℓ 3 ≤ ‖ℓ‖ ^ 2 := by nlinarith [abs_mul_abs_self (ℓ 3), abs_nonneg (ℓ 3)]
  have f0 := mul_self_nonneg (ℓ 0)
  have f1 := mul_self_nonneg (ℓ 1)
  have f2 := mul_self_nonneg (ℓ 2)
  have f3 := mul_self_nonneg (ℓ 3)
  rw [abs_le]
  constructor <;> nlinarith

theorem dot_cons_self' (t : ℝ) (v : Fin 3 → ℝ) :
    Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) = -t ^ 2 + ∑ k, v k ^ 2 := by
  rw [Minkowski.dot_eq]
  simp only [Fin.sum_univ_three]
  change -(t * t) + v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = _
  ring

theorem continuous_slash : Continuous Dirac.slash := by
  unfold Dirac.slash Minkowski.lower
  fun_prop

/-- `ℓ̸ = t E + V` at `ℓ = (t, v⃗)`. -/
theorem slash_cons (t : ℝ) (v : Fin 3 → ℝ) :
    Dirac.slash (Fin.cons t v : Fin 4 → ℝ) =
      (t : ℂ) • Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ) + Dirac.slash (Fin.cons 0 v : Fin 4 → ℝ) := by
  have h := slash_add_cons 0 t v
  simp only [zero_add] at h
  rw [h, add_comm]

/-! ### The four numerators -/

/-- The Feynman-gauge entry (the frozen vertex numerator). -/
noncomputable def numG (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) : ℂ :=
  vertexNumerator m p' p μ ℓ i j

/-- `ℓ² γ^μ_{ij}`. -/
noncomputable def numS (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * Dirac.gamma μ i j

/-- `(ℓ̸ (m - p̸') γ^μ + γ^μ (m - p̸) ℓ̸)_{ij}`. -/
noncomputable def numL (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) : ℂ :=
  (Dirac.slash ℓ * (((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p') * Dirac.gamma μ) +
    (Dirac.gamma μ * ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p)) *
      Dirac.slash ℓ) i j

/-- `(ℓ̸ (m - p̸') γ^μ (m - p̸) ℓ̸)_{ij}`. -/
noncomputable def numQ (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) : ℂ :=
  (Dirac.slash ℓ * (((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p') * Dirac.gamma μ *
    ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p)) * Dirac.slash ℓ) i j

theorem quadN_numG (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) : QuadN (numG m p' p μ i j) :=
  ⟨continuous_vertexNumerator m p' p μ i j, exists_vertexNumerator_quadratic m p' p μ i j,
    exists_norm_vertexNumerator_le m p' p μ i j⟩

theorem quadN_numS (μ i j : Fin 4) : QuadN (numS μ i j) := by
  have e : numS μ i j = fun ℓ =>
      ((((Minkowski.dot ℓ ℓ : ℝ) : ℂ)) • Dirac.gamma μ) i j := by
    funext ℓ
    simp [numS, Matrix.smul_apply]
  rw [e]
  refine quadN_entry ?_ ?_ ?_ i j
  · exact (Complex.continuous_ofReal.comp (VertexLimit.continuous_dot_comp continuous_id
      continuous_id)).smul continuous_const
  · refine ⟨-Dirac.gamma μ, fun v => ⟨0, ((∑ k, v k ^ 2 : ℝ) : ℂ) • Dirac.gamma μ, fun t => ?_⟩⟩
    rw [dot_cons_self']
    push_cast
    rw [smul_zero, add_zero, smul_neg, add_smul, neg_smul, ← neg_smul]
  · refine ⟨4 * ∑ a, ∑ b, ‖Dirac.gamma μ a b‖, fun ℓ a b => ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real]
    have h1 := norm_dot_le ℓ
    have h2 : ‖Dirac.gamma μ a b‖ ≤ ∑ a, ∑ b, ‖Dirac.gamma μ a b‖ :=
      (Finset.single_le_sum (f := fun b => ‖Dirac.gamma μ a b‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ b)).trans (Finset.single_le_sum
          (f := fun a => ∑ b, ‖Dirac.gamma μ a b‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))
    calc ‖Minkowski.dot ℓ ℓ‖ * ‖Dirac.gamma μ a b‖
        ≤ (4 * (1 + ‖ℓ‖) ^ 2) * ∑ a, ∑ b, ‖Dirac.gamma μ a b‖ :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring

theorem quadN_numL (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) : QuadN (numL m p' p μ i j) := by
  set K₁ := ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p') * Dirac.gamma μ
  set K₂ := Dirac.gamma μ * ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p)
  refine quadN_entry (F := fun ℓ => Dirac.slash ℓ * K₁ + K₂ * Dirac.slash ℓ) ?_ ?_ ?_ i j
  · exact (continuous_slash.matrix_mul continuous_const).add
      (continuous_const.matrix_mul continuous_slash)
  · set E := Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ)
    refine ⟨0, fun v => ⟨E * K₁ + K₂ * E, Dirac.slash (Fin.cons 0 v : Fin 4 → ℝ) * K₁ +
      K₂ * Dirac.slash (Fin.cons 0 v : Fin 4 → ℝ), fun t => ?_⟩⟩
    rw [slash_cons t v]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_zero,
      zero_add, smul_add]
    abel
  · obtain ⟨C, hC⟩ := exists_norm_slash_mul_add_mul_slash_le K₁ K₂
    refine ⟨C, fun ℓ a b => ?_⟩
    let _ := Matrix.linftyOpNormedRing (n := Fin 4) (α := ℂ)
    exact (norm_entry_le _ a b).trans (hC ℓ)

theorem quadN_numQ (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) : QuadN (numQ m p' p μ i j) := by
  set K := ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p') * Dirac.gamma μ *
    ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p)
  refine quadN_entry (F := fun ℓ => Dirac.slash ℓ * K * Dirac.slash ℓ) ?_ ?_ ?_ i j
  · exact (continuous_slash.matrix_mul continuous_const).matrix_mul continuous_slash
  · set E := Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ)
    refine ⟨E * K * E, fun v => ?_⟩
    set V := Dirac.slash (Fin.cons 0 v : Fin 4 → ℝ)
    refine ⟨E * K * V + V * K * E, V * K * V, fun t => ?_⟩
    rw [slash_cons t v]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul, ← pow_two]
    abel
  · obtain ⟨C, hC⟩ := exists_norm_slash_mul_mul_slash_le K
    refine ⟨C, fun ℓ a b => ?_⟩
    let _ := Matrix.linftyOpNormedRing (n := Fin 4) (α := ℂ)
    exact (norm_entry_le _ a b).trans (hC ℓ)

/-! ### The reductions `ℓ̸ ℓ̸ = -ℓ²` -/

/-- `ℓ̸ (m - (p' + ℓ)̸) = ℓ² + ℓ̸ (m - p̸')`. -/
theorem slash_mul_massSub (m : ℝ) (p' ℓ : Fin 4 → ℝ) :
    Dirac.slash ℓ * ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p' + ℓ)) =
      ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
        Dirac.slash ℓ * ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p') := by
  rw [Dirac.slash_add, ← sub_sub, Matrix.mul_sub, Dirac.slash_mul_slash]
  push_cast
  rw [neg_smul]
  abel

/-- `(m - (p + ℓ)̸) ℓ̸ = ℓ² + (m - p̸) ℓ̸`. -/
theorem massSub_mul_slash (m : ℝ) (p ℓ : Fin 4 → ℝ) :
    ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p + ℓ)) * Dirac.slash ℓ =
      ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
        ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p) * Dirac.slash ℓ := by
  rw [Dirac.slash_add, ← sub_sub, Matrix.sub_mul, Dirac.slash_mul_slash]
  push_cast
  rw [neg_smul]
  abel

end QED.ChainProof.HCBB2

end
