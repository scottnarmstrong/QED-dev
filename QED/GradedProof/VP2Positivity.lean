/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2PositivityTwo
public import QED.GradedProof.VP2ClassVA
public import QED.GradedProof.VP2ClassVB
public import QED.GradedProof.VP2ClassVC

/-!
# Positivity of `V` below the pair threshold for the vacuum-polarization shapes

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, step L3. In
two-photon kinematics every external line momentum is a multiple `aᵢ k` of `k`. A cut separating
the two external vertices crosses the closed fermion loop twice, so the threshold is `2 m₀`: the
path certificate of `QED.GradedProof.SE2.symanzikV_smul_ge` consists of the two arcs of the loop,
each of value `m₀`, through fermion lines only (`symanzikV_vp_ge`). The arcs of the classes
`VA`, `VB`, `VC` (external coefficients `cVA`, `cVB`, `cVC`) are `flowVA`, `flowVB`, `flowVC`.
-/

@[expose] public section

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.GradedProof.SE2 Matrix

/-- **`V` below the pair threshold** for a shape of a vacuum-polarization routing `base` with
external coefficients `a`, from two arcs `y₁`, `y₂` avoiding the photon row `4` and covering every
fermion row at most once; the rows `sh i ≠ 4` have masses at least `m₀`. -/
theorem symanzikV_vp_ge (base : Fin 5 → Fin 2 → ℤ) (a : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
    (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + a j| + |∑ s, (base j s : ℝ) * y₂ s + a j|
      ≤ if j = 4 then 0 else 1)
    {n : ℕ} (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hf : ∀ i, sh i ≠ 4 → m₀ ≤ Ms i) (h0 : ∀ i, 0 ≤ Ms i) {c : ℝ} (hc : 0 < c)
    (hMc : ∀ i, c ≤ Ms i ^ 2) {k : Fin 4 → ℝ} (hs : -(2 * m₀) ^ 2 < Minkowski.dot k k)
    {z : Fin (n + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix fun i => base (sh i)) z ≠ 0) :
    min 1 (1 + Minkowski.dot k k / (2 * m₀) ^ 2) * c ≤
      symanzikV (castLoopMatrix fun i => base (sh i)) (fun i => a (sh i) • k) Ms z := by
  refine symanzikV_smul_ge _ hz hz1 hU (fun i => a (sh i)) Ms ![y₁, y₂] ![m₀, m₀]
    (fun P => by fin_cases P <;> simp [hm₀.le]) (by positivity)
    (by simp [Fin.sum_univ_two]; ring) ?_ hc hMc hs
  intro i
  have h := hflow (sh i)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, castLoopMatrix] at h ⊢
  by_cases h4 : sh i = 4
  · simp only [h4, ite_true] at h ⊢
    have := h0 i
    have e1 := abs_nonneg ((base 4 0 : ℝ) * y₁ 0 + (base 4 1 : ℝ) * y₁ 1 + a 4)
    have e2 := abs_nonneg ((base 4 0 : ℝ) * y₂ 0 + (base 4 1 : ℝ) * y₂ 1 + a 4)
    nlinarith
  · simp only [h4, ite_false] at h
    have := hf i h4
    nlinarith

/-- The external coefficients of the rows of `VA`. -/
def cVA : Fin 5 → ℝ := ![0, 0, 0, 1, 0]

/-- The external coefficients of the rows of `VB`. -/
def cVB : Fin 5 → ℝ := ![0, -1, 0, 1, 1]

/-- The external coefficients of the rows of `VC`. -/
def cVC : Fin 5 → ℝ := ![0, 1, 0, 1, 1]

theorem ppVA_eq (k : Fin 4 → ℝ) (j : Fin 5) : ppVA k j = cVA j • k := by
  fin_cases j <;> simp [ppVA, cVA]

theorem ppVB_eq (k : Fin 4 → ℝ) (j : Fin 5) : ppVB k j = cVB j • k := by
  fin_cases j <;> simp [ppVB, cVB]

theorem ppVC_eq (k : Fin 4 → ℝ) (j : Fin 5) : ppVC k j = cVC j • k := by
  fin_cases j <;> simp [ppVC, cVC]

theorem flowVA : ∀ j : Fin 5,
    |∑ s, (baseVA j s : ℝ) * ![0, 0] s + cVA j| + |∑ s, (baseVA j s : ℝ) * ![-1, -1] s + cVA j|
      ≤ if j = 4 then 0 else 1 := by
  intro j
  fin_cases j <;> simp [baseVA, cVA, Fin.sum_univ_two]

theorem flowVB : ∀ j : Fin 5,
    |∑ s, (baseVB j s : ℝ) * ![0, 1] s + cVB j| + |∑ s, (baseVB j s : ℝ) * ![-1, 0] s + cVB j|
      ≤ if j = 4 then 0 else 1 := by
  intro j
  fin_cases j <;> simp [baseVB, cVB, Fin.sum_univ_two]

theorem flowVC : ∀ j : Fin 5,
    |∑ s, (baseVC j s : ℝ) * ![0, 1] s + cVC j| + |∑ s, (baseVC j s : ℝ) * ![-1, 0] s + cVC j|
      ≤ if j = 4 then 0 else 1 := by
  intro j
  fin_cases j <;> simp [baseVC, cVC, Fin.sum_univ_two]

end QED.GradedProof.VP2

end
