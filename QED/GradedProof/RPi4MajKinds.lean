/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajTilt
public import QED.GradedProof.RPi4FV
public import QED.TwoLoop.UnitSCCtIntegral

/-!
# (R-Π₄) step L10: the Symanzik data of the eight-line one-loop pieces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The one-loop
pieces `QED.GradedProof.RPi4.fVal5` are eight-line parametric values with the line kinds
`QED.GradedProof.VP2.kinds5 b`: five lines on loop `0` (momentum `q` or `k + q`), three on the
auxiliary loop `1`. With `a = z₀ + ⋯ + z₄`, `b = z₅ + z₆ + z₇` and `c = ∑_{bᵢ} zᵢ` (the lines
carrying `k`):

* `maj_symanzikMatrix_kinds5`, `maj_symanzikU_kinds5`: `A = diag(a, b)`, `U = a b`;
* `maj_mom_kinds5`: the line momenta are `cᵢ k` (`majKCs b`);
* `maj_loopShift_kinds5`: the loop shift is `S₀ = (c/a) k`, `S₁ = 0`;
* `maj_remainder_kinds5`, `maj_remainder_pos`: the remainder of the column is `c (a - c) / a`,
  positive inside the simplex if `b` takes both values;
* `majProbe`, `maj_integrableOn_probe`: `1 / (U² a)` is integrable on the simplex (the second
  coefficient of the probe numerator `(ℓ₀⁰)²`, `QED.TwoLoop.ClassLimit.integrableOn_coeff`).
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.CountertermLimit
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### The data -/

/-- The momentum coefficients of the lines: `1` on the lines carrying `k`, else `0`. -/
noncomputable def majKCs (b : Fin 5 → Bool) : Fin 8 → ℝ :=
  ![if b 0 then 1 else 0, if b 1 then 1 else 0, if b 2 then 1 else 0, if b 3 then 1 else 0,
    if b 4 then 1 else 0, 0, 0, 0]

/-- The total parameter `a = z₀ + ⋯ + z₄` of loop `0`. -/
def majKA (z : Fin 8 → ℝ) : ℝ := z 0 + z 1 + z 2 + z 3 + z 4

/-- The total parameter `b = z₅ + z₆ + z₇` of the auxiliary loop. -/
def majKB (z : Fin 8 → ℝ) : ℝ := z 5 + z 6 + z 7

/-- The parameter `c = ∑_{bᵢ} zᵢ` of the lines carrying `k`. -/
noncomputable def majKC (b : Fin 5 → Bool) (z : Fin 8 → ℝ) : ℝ := ∑ i, z i * majKCs b i

/-- The loop matrix of the pieces. -/
noncomputable def majKAlpha (b : Fin 5 → Bool) : Fin 8 → Fin 2 → ℝ :=
  castLoopMatrix fun l => (kinds5 b l).dir

theorem maj_dir_kd (c : Bool) : (kd c).dir = ![1, 0] := by cases c <;> rfl

theorem maj_dir_aux : LineKind.aux.dir = ![0, 1] := rfl

theorem maj_mom_aux (k : Fin 4 → ℝ) : LineKind.aux.mom k k = 0 := rfl

theorem maj_mom_kd (c : Bool) (k : Fin 4 → ℝ) :
    (kd c).mom k k = (if c then (1 : ℝ) else 0) • k := by
  cases c <;> simp [kd, LineKind.mom]

theorem maj_mom_kinds5 (b : Fin 5 → Bool) (k : Fin 4 → ℝ) (l : Fin 8) :
    (kinds5 b l).mom k k = majKCs b l • k := by
  fin_cases l <;> simp [kinds5, majKCs, maj_mom_kd, maj_mom_aux]

theorem maj_majKC_eq (b : Fin 5 → Bool) (z : Fin 8 → ℝ) :
    majKC b z = (if b 0 then z 0 else 0) + (if b 1 then z 1 else 0) + (if b 2 then z 2 else 0) +
      (if b 3 then z 3 else 0) + (if b 4 then z 4 else 0) := by
  simp [majKC, majKCs, Fin.sum_univ_eight]

/-! ### The Symanzik functions -/

theorem maj_symanzikMatrix_kinds5 (b : Fin 5 → Bool) (z : Fin 8 → ℝ) :
    symanzikMatrix (majKAlpha b) z = !![majKA z, 0; 0, majKB z] := by
  ext s t
  fin_cases s <;> fin_cases t <;>
    simp [symanzikMatrix, majKAlpha, castLoopMatrix, kinds5, maj_dir_kd, maj_dir_aux,
      Fin.sum_univ_eight, majKA, majKB]

theorem maj_symanzikU_kinds5 (b : Fin 5 → Bool) (z : Fin 8 → ℝ) :
    symanzikU (majKAlpha b) z = majKA z * majKB z := by
  rw [symanzikU, maj_symanzikMatrix_kinds5, Matrix.det_fin_two_of]
  ring

theorem maj_inv_symanzikMatrix_kinds5 (b : Fin 5 → Bool) (z : Fin 8 → ℝ) (s t : Fin 2) :
    (symanzikMatrix (majKAlpha b) z)⁻¹ s t =
      (majKA z * majKB z)⁻¹ * !![majKB z, 0; 0, majKA z] s t := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', maj_symanzikMatrix_kinds5,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two_of, Matrix.smul_apply, smul_eq_mul]
  fin_cases s <;> fin_cases t <;> simp

/-- **The loop shift of the pieces**: `S₀ = (c/a) k`. -/
theorem maj_loopShift_kinds5 (b : Fin 5 → Bool) (k : Fin 4 → ℝ) {z : Fin 8 → ℝ}
    (ha : majKA z ≠ 0) (hb : majKB z ≠ 0) :
    loopShift (majKAlpha b) (fun i => majKCs b i • k) z 0 = (majKC b z / majKA z) • k := by
  funext μ
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply]
  simp only [Fin.sum_univ_two, maj_inv_symanzikMatrix_kinds5]
  simp [Fin.sum_univ_eight, majKAlpha, castLoopMatrix, kinds5, maj_dir_kd, maj_dir_aux, majKC,
    majKCs]
  field_simp
  split_ifs <;> ring

/-- **The remainder of the column of the pieces**: `c - c²/a`. -/
theorem maj_remainder_kinds5 (b : Fin 5 → Bool) {z : Fin 8 → ℝ} (ha : majKA z ≠ 0)
    (hb : majKB z ≠ 0) :
    remainder (majKAlpha b) z (majKCs b) = majKC b z - majKC b z ^ 2 / majKA z := by
  have hc : coefVec (majKAlpha b) z (majKCs b) = ![majKC b z, 0] := by
    funext s
    fin_cases s <;>
      simp [coefVec, Fin.sum_univ_eight, majKAlpha, castLoopMatrix, kinds5, maj_dir_kd,
        maj_dir_aux, majKC, majKCs]
  have hq : ∑ i, z i * majKCs b i ^ 2 = majKC b z := by
    simp only [majKC]
    refine Finset.sum_congr rfl fun i _ => ?_
    fin_cases i <;> simp [majKCs]
  rw [remainder, hq, hc]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, maj_inv_symanzikMatrix_kinds5]
  field_simp

/-- **The remainder is positive inside the simplex** if `b` takes both values. -/
theorem maj_remainder_pos (b : Fin 5 → Bool) {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i)
    {i j : Fin 5} (hi : b i = true) (hj : b j = false) :
    0 < remainder (majKAlpha b) z (majKCs b) := by
  have ha : 0 < majKA z := by
    have := hz 0; have := hz 1; have := hz 2; have := hz 3; have := hz 4
    unfold majKA; linarith
  have hb : 0 < majKB z := by
    have := hz 5; have := hz 6; have := hz 7
    unfold majKB; linarith
  rw [maj_remainder_kinds5 b ha.ne' hb.ne']
  have e : majKC b z - majKC b z ^ 2 / majKA z = majKC b z * (majKA z - majKC b z) / majKA z := by
    field_simp
  rw [e]
  have hCs : ∀ l : Fin 5, majKCs b (Fin.castAdd 3 l) = if b l then 1 else 0 := fun l => by
    fin_cases l <;> rfl
  have hCs0 : ∀ l, 0 ≤ majKCs b l := fun l => by
    fin_cases l <;> simp [majKCs] <;> split_ifs <;> norm_num
  have hC : 0 < majKC b z := by
    have h := Finset.single_le_sum (f := fun l => z l * majKCs b l)
      (fun l _ => mul_nonneg (hz l).le (hCs0 l)) (Finset.mem_univ (Fin.castAdd 3 i))
    simp only [hCs, hi, ite_true, mul_one] at h
    exact (hz _).trans_le h
  have hAC : 0 < majKA z - majKC b z := by
    have e : majKA z - majKC b z = ∑ l : Fin 5, z (Fin.castAdd 3 l) * (1 - majKCs b
        (Fin.castAdd 3 l)) := by
      simp only [majKA, majKC, Fin.sum_univ_eight, Fin.sum_univ_five]
      simp [majKCs]
      split_ifs <;> ring
    have h := Finset.single_le_sum (f := fun l : Fin 5 => z (Fin.castAdd 3 l) *
      (1 - majKCs b (Fin.castAdd 3 l))) (fun l _ => mul_nonneg (hz _).le (by
        rw [hCs]; split_ifs <;> norm_num)) (Finset.mem_univ j)
    simp only [hCs, hj] at h
    rw [e]
    simp only [Bool.false_eq_true, ite_false, sub_zero, mul_one] at h
    exact (hz _).trans_le h
  positivity

/-! ### The criterion and the probe numerator -/

theorem maj_crit_kinds5 (b : Fin 5 → Bool) :
    NoSubdivergenceRefined 2 ({0, 1, 2, 3} : Finset (Fin 8)) (majKAlpha b) :=
  (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (crit_kinds5 b)

theorem maj_alpha_kinds5 (b : Fin 5 → Bool) :
    ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin 8)), majKAlpha b e = ![1, 0] := by
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> funext s <;> fin_cases s <;>
    simp [majKAlpha, castLoopMatrix, kinds5, maj_dir_kd]

/-- The probe numerator `(ℓ₀⁰)²`. -/
def majProbe : LoopQuartic where
  const := 0
  lin := 0
  quad a b := if a = (0, 0) then if b = (0, 0) then 1 else 0 else 0
  cub := 0
  quart := 0

theorem maj_probe_eval (ℓ : Fin 2 → Fin 4 → ℝ) : majProbe.eval ℓ = ((ℓ 0 0 : ℝ) : ℂ) ^ 2 := by
  simp [LoopQuartic.eval, LoopQuartic.evalC, majProbe, loopComp, sq]

theorem maj_probe_dep (ℓ : Fin 2 → Fin 4 → ℝ) : majProbe.eval ℓ = majProbe.eval ![ℓ 0, 0] := by
  simp [maj_probe_eval]

/-- The second coefficient of the probe: `-1 / (U² a)`. -/
theorem maj_coeffTwo_probe (b : Fin 5 → Bool) (p : Fin 8 → Fin 4 → ℝ) (x : Fin 7 → ℝ) :
    coeffTwo majProbe (majKAlpha b) p x =
      -((((majKA (simplexPoint x) * majKB (simplexPoint x)) ^ 2 * majKA (simplexPoint x) : ℝ)
        : ℂ))⁻¹ := by
  simp only [coeffTwo, LoopQuartic.contractTwo, LoopQuartic.hess, LoopQuartic.quartSym,
    majProbe, maj_symanzikU_kinds5, loopMetricInv, maj_inv_symanzikMatrix_kinds5]
  simp [Minkowski.metric]
  field_simp

/-- **`1 / (U² a)` is integrable on the simplex.** -/
theorem maj_integrableOn_probe (b : Fin 5 → Bool) :
    IntegrableOn (fun x : Fin 7 → ℝ => 1 / ((majKA (simplexPoint x) * majKB (simplexPoint x)) ^ 2 *
      majKA (simplexPoint x))) (simplexSet 7) := by
  have h := (integrableOn_coeff majProbe (majKAlpha b) 0 le_rfl (maj_crit_kinds5 b)
    (refinedBound_of_dependsOnZero (majKAlpha b) (by decide) (maj_alpha_kinds5 b) majProbe
      maj_probe_dep)).2.1
  refine Integrable.congr h.norm ?_
  filter_upwards [QED.TwoLoop.UnitSCCt.ae_mem_openSimplex' (by norm_num : 0 < 7)] with x hx
  have hz := QED.TwoLoop.UnitSCCt.simplexPoint_pos_of_mem_openSimplex' hx
  have ha : 0 < majKA (simplexPoint x) := by
    have := hz 0; have := hz 1; have := hz 2; have := hz 3; have := hz 4
    unfold majKA; linarith
  have hb : 0 < majKB (simplexPoint x) := by
    have := hz 5; have := hz 6; have := hz 7
    unfold majKB; linarith
  rw [maj_coeffTwo_probe b 0 x, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity), one_div]

end QED.GradedProof.RPi4

end
