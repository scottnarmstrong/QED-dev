/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajLTop
public import QED.GradedProof.RPi4MajSplit

/-!
# (R-Π₄) step L10, two loops: a vacuum-polarization piece along the ray, light pairs

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.IR). A piece
of a class `VA`, `VB`, `VC` (photon lines last, photon factor `b² - a²` in the numerator) is
`MajLRay` (`‖G a b (k(s))‖ ≤ C √b s w(s)`) once its numerator along the ray is
`∑_{t<3} r^{2t} Q_t(ℓ/r)` and its top monomial is controlled. The corner bounds
`U ≥ (1 - y) y` and `V₀ ≥ m₀² y + (1 - y) a²` (at zero momentum, from the masses) are proved as
at step L7 (`QED.GradedProof.RPi4.lightBdd_vpPiece`).

* `maj_eval_ray`: the quartic along the ray;
* **`maj_lray_vpPiece`**: the piece is `MajLRay`.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.TwoLoop.MassScaling QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- The quartic of the numerator along the ray. -/
theorem maj_eval_ray {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ} {Q : Fin 3 → LoopQuartic}
    (hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, N (r • majRayVec 1) ℓ =
      ∑ t : Fin 3, ((r : ℂ) ^ 2) ^ (t : ℕ) * (Q t).eval (r⁻¹ • ℓ)) {s : ℝ} (hs : 1 ≤ s) :
    ∃ R : LoopQuartic, R.eval = N (majRayVec s) := by
  have hs0 : 0 ≤ s := by linarith
  set r := Real.sqrt s with hr_def
  have hr1 : 1 ≤ r := by rw [hr_def, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hs
  refine ⟨qsum Finset.univ (fun t : Fin 3 => ((r : ℂ) ^ 2) ^ (t : ℕ))
    (fun t => dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)), ?_⟩
  funext ℓ
  rw [maj_majRayVec_eq hs0, hN r hr1]
  simp only [eval_qsum, eval_dilateQ, one_mul]

/-- **A vacuum-polarization piece at light comparable photon pairs along the ray.** -/
theorem maj_lray_vpPiece (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
    (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
    (hrow4 : base 4 = ![1, -1]) {n : ℕ} (hn : n = 6 ∨ n = 7) (sh : Fin (n + 1) → Fin 5)
    (hsh : ∀ l : Fin (n + 1), sh l = 4 ↔ n - 1 ≤ (l : ℕ)) (Ms : ℝ → ℝ → Fin (n + 1) → ℝ)
    (hMs : ∀ a b l, Ms a b l ^ 2 = Ms 0 0 l ^ 2 + (if (l : ℕ) = n - 1 then a ^ 2 else 0) +
      (if (l : ℕ) = n then b ^ 2 else 0))
    {E : Finset (Fin (n + 1))} (hcrit : IntNoSubdivergenceRefined 2 E fun i => base (sh i))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (Q : Fin 3 → LoopQuartic)
    (hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, N (r • majRayVec 1) ℓ =
      ∑ t : Fin 3, ((r : ℂ) ^ 2) ^ (t : ℕ) * (Q t).eval (r⁻¹ • ℓ))
    (hq : ∀ t, 7 ≤ n ∨ (Q t).quart = 0)
    (hB : ∀ t, RefinedBound (castLoopMatrix fun i => base (sh i)) E 4 (Q t).eval)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hf : ∀ l, sh l ≠ 4 → m₀ ≤ Ms 0 0 l)
    (hTop : (∀ x ∈ simplexSet n, (1 - headSum (n - 1) x) * headSum (n - 1) x ≤
        symanzikU (castLoopMatrix fun i => base (sh i)) (simplexPoint x)) →
      (∀ a b : ℝ, 0 < a → a ≤ b → ∀ x ∈ simplexSet n,
        m₀ ^ 2 * headSum (n - 1) x + (1 - headSum (n - 1) x) * a ^ 2 ≤
          ∑ i, simplexPoint x i * Ms a b i ^ 2) →
      ∃ G H : (Fin n → ℝ) → ℝ, IntegrableOn G (simplexSet n) ∧
        IntegrableOn H (simplexSet n) ∧ ∀ᵐ x ∂(volume.restrict (simplexSet n)),
          ∀ s : ℝ, 1 ≤ s → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a →
            ‖coeffOne (Q 2) (castLoopMatrix fun i => base (sh i))
                (fun i => c (sh i) • majRayVec 1) x‖ * s ^ 2 /
              (∑ i, simplexPoint x i * Ms a b i ^ 2 +
                s * remainder (castLoopMatrix fun i => base (sh i)) (simplexPoint x)
                  (fun i => c (sh i))) ^ (n - 3) ≤ s * (G x + H x / b)) :
    MajLRay fun a b k => pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * N k ℓ)
      (castLoopMatrix fun l => base (sh l)) (fun l => c (sh l) • k) (Ms a b) := by
  set α := castLoopMatrix fun l => base (sh l) with hα_def
  have hcrit' : NoSubdivergenceRefined 2 E α :=
    (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit
  have hrows := castLoopMatrix_rows base hrow hrow4 sh
  have hrows3 : ∀ i, α i = ![1, 0] ∨ α i = ![0, 1] ∨ α i = ![1, -1] := fun i => by
    by_cases h4 : sh i = 4
    · exact Or.inr (Or.inr ((hrows i).2 h4))
    · rcases (hrows i).1 h4 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hsums : ∀ x ∈ simplexSet n,
      ∑ i, (if sh i = 4 then 0 else simplexPoint x i) = headSum (n - 1) x ∧
        ∑ i, (if sh i = 4 then simplexPoint x i else 0) = 1 - headSum (n - 1) x := by
    intro x hx
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
    have h1 := sum_fermion_simplexPoint sh hsh x
    refine ⟨h1, ?_⟩
    have h2 : ∑ i, simplexPoint x i = ∑ i, (if sh i = 4 then 0 else simplexPoint x i) +
        ∑ i, (if sh i = 4 then simplexPoint x i else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
    rw [hz.2, h1] at h2
    linarith
  have hU : ∀ x ∈ simplexSet n,
      (1 - headSum (n - 1) x) * headSum (n - 1) x ≤ symanzikU α (simplexPoint x) := by
    intro x hx
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
    obtain ⟨e1, e2⟩ := chainZ_rows α (simplexPoint x) sh hrows
    have h := symanzikU_ge_chain α hz.1 hrows3
    rw [e1, e2, (hsums x hx).1, (hsums x hx).2] at h
    exact h
  have hV : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ x ∈ simplexSet n,
      m₀ ^ 2 * headSum (n - 1) x + (1 - headSum (n - 1) x) * a ^ 2 ≤
        ∑ i, simplexPoint x i * Ms a b i ^ 2 := by
    intro a b ha hab x hx
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
    rw [← (hsums x hx).2, ← (hsums x hx).1, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hzi := hz.1 i
    rw [hMs a b i]
    by_cases h4 : sh i = 4
    · simp only [h4, ite_true, mul_zero, zero_add]
      have hi := (hsh i).mp h4
      have hin : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
      have hM0 := sq_nonneg (Ms 0 0 i)
      rcases Nat.eq_or_lt_of_le hi with h | h
      · have h1 : (i : ℕ) = n - 1 := h.symm
        have h2 : ¬ (i : ℕ) = n := by omega
        rw [ite_eq_left h1, ite_eq_right h2]
        nlinarith
      · have h1 : ¬ (i : ℕ) = n - 1 := by omega
        have h2 : (i : ℕ) = n := by omega
        rw [ite_eq_right h1, ite_eq_left h2]
        nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hab 2) hzi]
    · simp only [h4, ite_false]
      have h1 : 0 ≤ (if (i : ℕ) = n - 1 then a ^ 2 else 0) := by split_ifs <;> positivity
      have h2 : 0 ≤ (if (i : ℕ) = n then b ^ 2 else 0) := by split_ifs <;> positivity
      have hm := pow_le_pow_left₀ hm₀.le (hf i h4) 2
      nlinarith [mul_le_mul_of_nonneg_left hm hzi]
  obtain ⟨C₁, C₂, hC⟩ := maj_pvOf_lray hn α hcrit' (fun l => c (sh l)) Ms N Q hN hq hB hU
    (pow_pos hm₀ 2) hV (hTop hU hV)
  refine ⟨|C₁| + |C₂|, fun s hs a b ha hab hb2 hb1 => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨R, hRe⟩ := maj_eval_ray hN hs
  dsimp only
  rw [pvOf_const_mul hRe, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by nlinarith)]
  have h := hC s hs a b ha hab hb2
  have hpv := norm_nonneg (pvOf (N (majRayVec s)) α (fun i => c (sh i) • majRayVec s) (Ms a b))
  have hsb : b ≤ Real.sqrt b := by
    have h := Real.sqrt_le_sqrt hb1
    rw [Real.sqrt_one] at h
    calc b = Real.sqrt b * Real.sqrt b := (Real.mul_self_sqrt hb.le).symm
      _ ≤ Real.sqrt b * 1 := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg b)
      _ = Real.sqrt b := mul_one _
  have hw := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ s)
    (maj_one_le_majW (s := s) (by linarith))
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hb2' : b ^ 2 ≤ b := by nlinarith
  calc (b ^ 2 - a ^ 2) * ‖pvOf (N (majRayVec s)) α (fun i => c (sh i) • majRayVec s) (Ms a b)‖
      ≤ b ^ 2 * (s * (|C₁| + |C₂| / b)) := by
        refine mul_le_mul (by nlinarith) (h.trans ?_) hpv (sq_nonneg b)
        refine mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) ?_) hs0
        exact div_le_div_of_nonneg_right (le_abs_self _) hb.le
    _ = s * (b ^ 2 * |C₁| + b * |C₂|) := by field_simp
    _ ≤ s * (Real.sqrt b * |C₁| + Real.sqrt b * |C₂|) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hs0
        · exact mul_le_mul_of_nonneg_right (hb2'.trans hsb) (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_right hsb (abs_nonneg _)
    _ ≤ (|C₁| + |C₂|) * Real.sqrt b * (s * majW s) := by
        have := Real.sqrt_nonneg b
        have hC0 : 0 ≤ (|C₁| + |C₂|) * Real.sqrt b := by positivity
        calc s * (Real.sqrt b * |C₁| + Real.sqrt b * |C₂|) = (|C₁| + |C₂|) * Real.sqrt b * s := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hw hC0

end QED.GradedProof.RPi4

end
