/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2Positivity

/-!
# (R-Π₄) step P0: `V` controls the fermion parameters below the pair threshold

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), steps L6d and L7. In the
photon-pair limits the photon masses are sent to `0` or to `∞`, so the bound
`QED.GradedProof.VP2.symanzikV_vp_ge` (`V ≥ c` with `c` a lower bound of *all* squared masses) is
not uniform. Here the lower bound is by the total weight of the fermion lines alone, with no
condition on the photon masses:

* `symanzikV_vp_ge_fermion`: for a shape of a vacuum-polarization routing with the two arcs of
  `symanzikV_vp_ge`, fermion masses at least `m₀`, arbitrary photon masses and `k² > -(2m₀)²`,
  `V ≥ min(1, 1 + k²/(2m₀)²) m₀² ∑_{fermion lines} zᵢ`.

The proof is that of `QED.GradedProof.SE2.symanzikV_smul_ge` with the capacities `m₀` on the
fermion lines and `0` on the photon lines (`QED.GradedProof.SE2.sq_mul_remainder_le`).
-/

@[expose] public section

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.GradedProof.SE2 QED.GradedProof.VP2

/-- **`V` is at least a multiple of the fermion weight below the pair threshold** (photon masses
arbitrary). -/
theorem symanzikV_vp_ge_fermion (base : Fin 5 → Fin 2 → ℤ) (a : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
    (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + a j| + |∑ s, (base j s : ℝ) * y₂ s + a j|
      ≤ if j = 4 then 0 else 1)
    {n : ℕ} (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hf : ∀ i, sh i ≠ 4 → m₀ ≤ Ms i) {k : Fin 4 → ℝ}
    (hs : -(2 * m₀) ^ 2 < Minkowski.dot k k) {z : Fin (n + 1) → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU (castLoopMatrix fun i => base (sh i)) z ≠ 0) :
    min 1 (1 + Minkowski.dot k k / (2 * m₀) ^ 2) * m₀ ^ 2 *
        ∑ i ∈ Finset.univ.filter (fun i => sh i ≠ 4), z i ≤
      symanzikV (castLoopMatrix fun i => base (sh i)) (fun i => a (sh i) • k) Ms z := by
  set α := castLoopMatrix fun i => base (sh i)
  set cap : Fin (n + 1) → ℝ := fun i => if sh i = 4 then 0 else m₀ with hcap_def
  have hdot0 : Minkowski.dot k 0 = 0 := by simp [Minkowski.dot_eq]
  have h := symanzikV_smul_add_smul α Ms z (fun i => a (sh i)) (fun _ => 0) hdot0
  simp only [smul_zero, add_zero] at h
  rw [h]
  have hd00 : Minkowski.dot (0 : Fin 4 → ℝ) 0 = 0 := by simp [Minkowski.dot_eq]
  rw [hd00, zero_mul, add_zero]
  set s := Minkowski.dot k k
  set Z := ∑ i ∈ Finset.univ.filter (fun i => sh i ≠ 4), z i
  have hZ : ∑ i, z i * cap i ^ 2 = m₀ ^ 2 * Z := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h4 : sh i = 4 <;> simp [cap, h4, mul_comm]
  have hW : m₀ ^ 2 * Z ≤ ∑ i, z i * Ms i ^ 2 := by
    rw [← hZ]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hz i)
    by_cases h4 : sh i = 4
    · simp only [cap, h4, ite_true]
      nlinarith [sq_nonneg (Ms i)]
    · simp only [cap, h4, ite_false]
      exact pow_le_pow_left₀ hm₀.le (hf i h4) 2
  have hR0 := remainder_nonneg α hz hU (fun i => a (sh i))
  have hRle := sq_mul_remainder_le α hz hU (fun i => a (sh i)) cap ![y₁, y₂] ![m₀, m₀]
    (fun P => by fin_cases P <;> simp [hm₀.le]) (by positivity : (0 : ℝ) < 2 * m₀)
    (by simp [Fin.sum_univ_two]; ring) (fun i => by
      have hfl := hflow (sh i)
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, α,
        castLoopMatrix] at hfl ⊢
      by_cases h4 : sh i = 4
      · simp only [cap, h4, ite_true] at hfl ⊢
        nlinarith [abs_nonneg ((base 4 0 : ℝ) * y₁ 0 + (base 4 1 : ℝ) * y₁ 1 + a 4),
          abs_nonneg ((base 4 0 : ℝ) * y₂ 0 + (base 4 1 : ℝ) * y₂ 1 + a 4)]
      · simp only [cap, h4, ite_false] at hfl ⊢
        nlinarith)
  rw [hZ] at hRle
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun i _ => hz i
  have hT2 : 0 < (2 * m₀) ^ 2 := by positivity
  rcases le_or_gt 0 s with hs0 | hs0
  · calc min 1 (1 + s / (2 * m₀) ^ 2) * m₀ ^ 2 * Z ≤ 1 * m₀ ^ 2 * Z := by
          gcongr
          exact min_le_left _ _
      _ ≤ ∑ i, z i * Ms i ^ 2 + s * remainder α z fun i => a (sh i) := by nlinarith
  · have hRW : remainder α z (fun i => a (sh i)) ≤ m₀ ^ 2 * Z / (2 * m₀) ^ 2 := by
      rw [le_div_iff₀ hT2]
      linarith
    have hδ : 0 ≤ 1 + s / (2 * m₀) ^ 2 := by
      have h1 : 0 < (2 * m₀) ^ 2 + s := by linarith
      have : 1 + s / (2 * m₀) ^ 2 = ((2 * m₀) ^ 2 + s) / (2 * m₀) ^ 2 := by field_simp
      rw [this]
      positivity
    calc min 1 (1 + s / (2 * m₀) ^ 2) * m₀ ^ 2 * Z ≤ (1 + s / (2 * m₀) ^ 2) * (m₀ ^ 2 * Z) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = m₀ ^ 2 * Z + s * (m₀ ^ 2 * Z / (2 * m₀) ^ 2) := by field_simp
      _ ≤ ∑ i, z i * Ms i ^ 2 + s * remainder α z fun i => a (sh i) := by nlinarith

end QED.GradedProof.RPi4

end
