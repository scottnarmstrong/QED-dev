/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4LightVP
public import QED.GradedProof.RPi4MajRayPv
public import QED.GradedProof.RPi4MajLWt

/-!
# (R-Π₄) step L10, two loops: a piece at a light photon pair along the ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.IR). Along
the ray `k = r v` (`v = majRayVec 1`, `r = √s ≥ 1`) let the numerator of a piece be
`N(r v)(ℓ) = ∑_{t < 3} r^{2t} Q_t(ℓ/r)`. By the dilation of the coefficients the parametric
integrand is `∑_t s^t (T₁(Q_t)/V^{m-3} + s⁻¹ T₂(Q_t)/V^{m-4} + s⁻² T₃(Q_t)/V^{m-5})` with the
coefficients `T_j` at `r = 1` and `V = V₀ + s B ≥ V₀ = ∑ zᵢ Mᵢ²`. Except for the top monomial
`s² T₁(Q₂)/V^{m-3}` every term is at most `s` times an absolute coefficient sum at `V₀`, which
is bounded as at step L7: by integrable coefficients where the fermion parameters sum to
`y ≥ 1/2`, by the soft-photon corner bound `y^{-(m-3/2)}/b` where `y < 1/2`.

* `maj_abs_corner_le`: the corner bound for the absolute coefficient sum with any base `W`;
* `majAbs3`, `majAbs3_anti`, `maj_norm_paramIntegrand_dilate_le`;
* **`maj_pvOf_lray`**: given a bound `s (G + H/b)` of the top monomial with integrable
  `G`, `H`, the parametric value along the ray is at most `s (C₁ + C₂/b)` for `s ≥ 1` and light
  comparable photon pairs.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.MassScaling Matrix
open QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)

section Corner

variable {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)

/-- **The absolute coefficients near the soft-photon corner**, with any denominator base
`W ≥ c₀ y` (the bound of `QED.GradedProof.RPi4.norm_paramIntegrand_le_corner` before the
coefficients are recombined). -/
theorem maj_abs_corner_le (hm : m = 6 ∨ m = 7) (hq : 7 ≤ m ∨ Q.quart = 0)
    (x : Fin m → ℝ) {y K τ c₀ W : ℝ} (hy : 0 < y) (hK : 0 ≤ K) (hc₀ : 0 < c₀)
    (hA : (symanzikMatrix α (simplexPoint x)).PosDef)
    (hU : y / 2 ≤ symanzikU α (simplexPoint x))
    (htr : (symanzikMatrix α (simplexPoint x)).trace ≤ τ)
    (hX : ∀ a, ‖loopComp (-loopShift α p (simplexPoint x)) a‖ ≤ K)
    (hV : c₀ * y ≤ W) :
    ‖coeffOne Q α p x‖ / W ^ (m - 3) + ‖coeffTwo Q α p x‖ / W ^ (m - 4) +
        ‖coeffThree Q α x‖ / W ^ (m - 5) ≤ lightB Q K τ c₀ / (y ^ (m - 3) * W ^ 2) := by
  set A := symanzikMatrix α (simplexPoint x)
  set U := symanzikU α (simplexPoint x)
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < W := lt_of_lt_of_le (by positivity) hV
  have hdet : A.det = U := rfl
  have hτ : 0 ≤ τ := (trace_div_det_nonneg hA |> fun h => by
    have := mul_nonneg h hA.det_pos.le
    rw [div_mul_cancel₀ _ hA.det_pos.ne'] at this
    linarith)
  have hg : ∀ s r, |A⁻¹ s r| ≤ 2 * τ / y := fun s r => by
    refine (abs_inv_apply_le hA s r).trans ?_
    rw [hdet, div_le_div_iff₀ hU0 hy]
    have := (trace_div_det_nonneg hA)
    nlinarith
  have hUi : ‖((U ^ 2 : ℝ) : ℂ)⁻¹‖ * y ^ 2 ≤ 4 := by
    rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_le_iff₀
      (by positivity)]
    nlinarith
  have hUi0 : 0 ≤ ‖((U ^ 2 : ℝ) : ℂ)⁻¹‖ := norm_nonneg _
  -- the three coefficients
  have n1 : ‖coeffOne Q α p x‖ * y ^ 2 ≤ 4 * ((m - 4).factorial * (lqNorm Q * (1 + K) ^ 4)) := by
    have he := norm_evalC_le_lqNorm Q _ hK hX
    simp only [coeffOne, norm_mul, LoopQuartic.eval, Complex.norm_natCast]
    calc ‖((U ^ 2 : ℝ) : ℂ)⁻¹‖ * ((m - 4).factorial *
          ‖Q.evalC (loopComp (-loopShift α p (simplexPoint x)))‖) * y ^ 2
        = (‖((U ^ 2 : ℝ) : ℂ)⁻¹‖ * y ^ 2) * ((m - 4).factorial *
          ‖Q.evalC (loopComp (-loopShift α p (simplexPoint x)))‖) := by ring
      _ ≤ 4 * ((m - 4).factorial * (lqNorm Q * (1 + K) ^ 4)) :=
          mul_le_mul hUi (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
            (by norm_num)
  have n2 : ‖coeffTwo Q α p x‖ * y ^ 3 ≤
      4 * ((m - 5).factorial / 2 * (lqHess Q * (1 + (K + K ^ 2)) * (2 * τ))) := by
    have he := norm_contractTwo_le Q A _ hK hX hg
    have he' : ‖Q.contractTwo A (loopComp (-loopShift α p (simplexPoint x)))‖ * y ≤
        lqHess Q * (1 + (K + K ^ 2)) * (2 * τ) := by
      calc _ ≤ lqHess Q * (1 + (K + K ^ 2)) * (2 * τ / y) * y :=
            mul_le_mul_of_nonneg_right he hy.le
        _ = _ := by field_simp
    simp only [coeffTwo, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_ofNat]
    calc ‖((U ^ 2 : ℝ) : ℂ)⁻¹‖ * ((m - 5).factorial / 2 *
          ‖Q.contractTwo A (loopComp (-loopShift α p (simplexPoint x)))‖) * y ^ 3
        = (‖((U ^ 2 : ℝ) : ℂ)⁻¹‖ * y ^ 2) * ((m - 5).factorial / 2 *
          (‖Q.contractTwo A (loopComp (-loopShift α p (simplexPoint x)))‖ * y)) := by ring
      _ ≤ _ := mul_le_mul hUi (mul_le_mul_of_nonneg_left he' (by positivity)) (by positivity)
            (by norm_num)
  have n3 : ‖coeffThree Q α x‖ * y ^ 4 ≤
      4 * ((m - 6).factorial / 4 * (lqQuart Q * (3 * (2 * τ) ^ 2))) := by
    have he := norm_contractFour_le Q A hg
    have he' : ‖Q.contractFour A‖ * y ^ 2 ≤ lqQuart Q * (3 * (2 * τ) ^ 2) := by
      calc _ ≤ lqQuart Q * (3 * (2 * τ / y) ^ 2) * y ^ 2 :=
            mul_le_mul_of_nonneg_right he (by positivity)
        _ = _ := by field_simp
    simp only [coeffThree, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_ofNat]
    calc ‖((U ^ 2 : ℝ) : ℂ)⁻¹‖ * ((m - 6).factorial / 4 * ‖Q.contractFour A‖) * y ^ 4
        = (‖((U ^ 2 : ℝ) : ℂ)⁻¹‖ * y ^ 2) * ((m - 6).factorial / 4 *
          (‖Q.contractFour A‖ * y ^ 2)) := by ring
      _ ≤ _ := mul_le_mul hUi (mul_le_mul_of_nonneg_left he' (by positivity)) (by positivity)
            (by norm_num)
  have hr : y / W ≤ 1 / c₀ := by
    rw [div_le_div_iff₀ hV0 hc₀]
    linarith
  have hB1 : 0 ≤ lqNorm Q * (1 + K) ^ 4 := mul_nonneg (lqNorm_nonneg Q) (by positivity)
  have hB2 : 0 ≤ lqHess Q * (1 + (K + K ^ 2)) * (2 * τ) :=
    mul_nonneg (mul_nonneg (lqHess_nonneg Q) (by positivity)) (by positivity)
  have hB3 : 0 ≤ lqQuart Q := lqQuart_nonneg Q
  have hc1 : 1 / c₀ ≤ 1 + 1 / c₀ := by linarith
  have hc2 : (1 / c₀) ^ 2 ≤ (1 + 1 / c₀) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hc1 2
  rcases hm with rfl | rfl
  · have hq0 : Q.quart = 0 := hq.resolve_left (by norm_num)
    have h3 : coeffThree Q α x = 0 := by
      simp [coeffThree, contractFour_eq_zero_of_quart Q _ hq0]
    simp only [h3, norm_zero, zero_div, add_zero]
    norm_num at n1 n2 ⊢
    have := two_term_le (t₁ := ‖coeffOne Q α p x‖) (t₂ := ‖coeffTwo Q α p x‖) hy hV0 hr n1 n2
      (norm_nonneg _)
    refine this.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    unfold lightB
    nlinarith [lqQuart_nonneg Q, sq_nonneg τ]
  · norm_num at n1 n2 n3 ⊢
    have := three_term_le (t₁ := ‖coeffOne Q α p x‖) (t₂ := ‖coeffTwo Q α p x‖)
      (t₃ := ‖coeffThree Q α x‖) hy hV0 hr n1 n2 n3 (norm_nonneg _) (norm_nonneg _)
    refine (le_of_eq (by ring)).trans (this.trans (div_le_div_of_nonneg_right ?_ (by positivity)))
    unfold lightB
    nlinarith [lqQuart_nonneg Q, sq_nonneg τ]

end Corner

section Gen

variable {m : ℕ}

/-- The absolute coefficient sum `‖T₁‖/W^{m-3} + ‖T₂‖/W^{m-4} + ‖T₃‖/W^{m-5}`. -/
noncomputable def majAbs3 (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (x : Fin m → ℝ) (W : ℝ) : ℝ :=
  ‖coeffOne Q α p x‖ / W ^ (m - 3) + ‖coeffTwo Q α p x‖ / W ^ (m - 4) +
    ‖coeffThree Q α x‖ / W ^ (m - 5)

theorem majAbs3_anti (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (x : Fin m → ℝ) {W W' : ℝ} (hW : 0 < W) (hWW : W ≤ W') :
    majAbs3 Q α p x W' ≤ majAbs3 Q α p x W := by
  have h := fun (T : ℝ) (n : ℕ) (hT : 0 ≤ T) => div_le_div_of_nonneg_left hT (pow_pos hW n)
    (pow_le_pow_left₀ hW.le hWW n)
  exact add_le_add (add_le_add (h _ _ (norm_nonneg _)) (h _ _ (norm_nonneg _)))
    (h _ _ (norm_nonneg _))

theorem majAbs3_nonneg (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (x : Fin m → ℝ) {W : ℝ} (hW : 0 < W) :
    0 ≤ majAbs3 Q α p x W := by
  unfold majAbs3
  positivity

/-- **One dilated quartic at scaled momenta**: the integrand of `ℓ ↦ Q(ℓ/r)` at the momenta
`r p` is at most `‖T₁‖/V^{m-3} + (‖T₂‖/V^{m-4} + ‖T₃‖/V^{m-5})/r²`, `r ≥ 1`. -/
theorem maj_norm_paramIntegrand_dilate_le (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (x : Fin m → ℝ) {r : ℝ} (hr : 1 ≤ r)
    (hV : 0 < symanzikV α (r • p) M (simplexPoint x)) :
    ‖paramIntegrand (dilateQ 1 ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) M 0 x‖ ≤
      ‖coeffOne Q α p x‖ / symanzikV α (r • p) M (simplexPoint x) ^ (m - 3) +
        (‖coeffTwo Q α p x‖ / symanzikV α (r • p) M (simplexPoint x) ^ (m - 4) +
          ‖coeffThree Q α x‖ / symanzikV α (r • p) M (simplexPoint x) ^ (m - 5)) / r ^ 2 := by
  have hr0 : 0 < r := by linarith
  set V := symanzikV α (r • p) M (simplexPoint x) with hVd
  have hW : wBase α (r • p) M 0 x = ((V : ℝ) : ℂ) := by simp [wBase, hVd]
  rw [paramIntegrand_eq, maj_coeffOne_dilateQ _ _ hr0.ne', maj_coeffTwo_dilateQ _ _ hr0.ne',
    maj_coeffThree_dilateQ, hW]
  refine (norm_add₃_le).trans ?_
  have hn : ∀ n : ℕ, ‖((((V : ℝ) : ℂ)) ^ n)⁻¹‖ = 1 / V ^ n := fun n => by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV, one_div]
  have hρ : ‖(((r⁻¹ : ℝ) : ℂ))‖ = r⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
  simp only [norm_mul, norm_pow, hn, hρ, one_mul]
  have hρ1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
  have hρ0 : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have h4 : r⁻¹ ^ 4 ≤ r⁻¹ ^ 2 := pow_le_pow_of_le_one hρ0 hρ1 (by norm_num)
  have e2 : r⁻¹ ^ 2 = 1 / r ^ 2 := by rw [inv_pow, one_div]
  have hA := norm_nonneg (coeffTwo Q α p x)
  have hB := norm_nonneg (coeffThree Q α x)
  have hV5 : 0 ≤ 1 / V ^ (m - 5) := by positivity
  have hV4 : 0 ≤ 1 / V ^ (m - 4) := by positivity
  calc ‖coeffOne Q α p x‖ * (1 / V ^ (m - 3)) + r⁻¹ ^ 2 * ‖coeffTwo Q α p x‖ * (1 / V ^ (m - 4)) +
        r⁻¹ ^ 4 * ‖coeffThree Q α x‖ * (1 / V ^ (m - 5))
      ≤ ‖coeffOne Q α p x‖ * (1 / V ^ (m - 3)) + r⁻¹ ^ 2 * ‖coeffTwo Q α p x‖ *
          (1 / V ^ (m - 4)) + r⁻¹ ^ 2 * ‖coeffThree Q α x‖ * (1 / V ^ (m - 5)) := by
        gcongr
    _ = _ := by rw [e2]; ring

/-- **A piece at a light comparable photon pair along the ray** is at most `s (C₁ + C₂/b)` for
`s ≥ 1`. Hypotheses: the numerator along the ray is `∑_{t<3} r^{2t} Q_t(ℓ/r)` with bounded
`Q_t`, the corner lower bounds `U ≥ (1 - y) y` and `V₀ ≥ c₀ y + (1 - y) a²` for the sum `y` of
the first `m - 1` (fermion) parameters, and a bound `s (G + H/b)` of the top monomial with
integrable `G`, `H`. -/
theorem maj_pvOf_lray (hm : m = 6 ∨ m = 7) (α : Fin (m + 1) → Fin 2 → ℝ)
    {E : Finset (Fin (m + 1))} (hcrit : NoSubdivergenceRefined 2 E α)
    (cs : Fin (m + 1) → ℝ) (Ms : ℝ → ℝ → Fin (m + 1) → ℝ)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (Q : Fin 3 → LoopQuartic)
    (hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, N (r • majRayVec 1) ℓ =
      ∑ t : Fin 3, (((r : ℂ)) ^ 2) ^ (t : ℕ) * (Q t).eval (r⁻¹ • ℓ))
    (hq : ∀ t, 7 ≤ m ∨ (Q t).quart = 0) (hB : ∀ t, RefinedBound α E 4 (Q t).eval)
    (hU : ∀ x ∈ simplexSet m,
      (1 - headSum (m - 1) x) * headSum (m - 1) x ≤ symanzikU α (simplexPoint x))
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hV : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ x ∈ simplexSet m,
      c₀ * headSum (m - 1) x + (1 - headSum (m - 1) x) * a ^ 2 ≤
        ∑ i, simplexPoint x i * Ms a b i ^ 2)
    (hTop : ∃ G H : (Fin m → ℝ) → ℝ, IntegrableOn G (simplexSet m) ∧
      IntegrableOn H (simplexSet m) ∧ ∀ᵐ x ∂(volume.restrict (simplexSet m)),
        ∀ s : ℝ, 1 ≤ s → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a →
          ‖coeffOne (Q 2) α (fun i => cs i • majRayVec 1) x‖ * s ^ 2 /
            (∑ i, simplexPoint x i * Ms a b i ^ 2 +
              s * remainder α (simplexPoint x) cs) ^ (m - 3) ≤ s * (G x + H x / b)) :
    ∃ C₁ C₂ : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a →
      ‖pvOf (N (majRayVec s)) α (fun i => cs i • majRayVec s) (Ms a b)‖ ≤
        s * (C₁ + C₂ / b) := by
  classical
  obtain ⟨G', H', hG', hH', hTop⟩ := hTop
  have hm6 : 6 ≤ m := by omega
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  set v := majRayVec 1 with hv
  set p₁ : Fin (m + 1) → Fin 4 → ℝ := fun i => cs i • v with hp₁
  have hmom : ∀ s : ℝ, 0 ≤ s → (fun i => cs i • majRayVec s) = Real.sqrt s • p₁ :=
    fun s hs => by
      funext i
      simp only [hp₁, Pi.smul_apply, maj_majRayVec_eq hs, hv]
      exact smul_comm _ _ _
  have hI : ∀ t, IntegrableOn (coeffOne (Q t) α p₁) (simplexSet m) ∧
      IntegrableOn (coeffTwo (Q t) α p₁) (simplexSet m) ∧
      IntegrableOn (coeffThree (Q t) α) (simplexSet m) := fun t => by
    rcases hq t with h7 | hq0
    · exact integrableOn_coeff (Q t) α p₁ h7 hcrit (hB t)
    · exact integrableOn_coeff_cubic (Q t) α p₁ hq0 hm6 hcrit (hB t)
  obtain ⟨CS, hCS0, hCS⟩ := exists_abs_loopShift_smul_le α cs
  have hv1 : ∀ μ, |v μ| ≤ 1 := by
    have e : v = ![1, 0, 1, 1] := by
      simp only [hv, majRayVec, tiltVec, Real.sqrt_one]
      norm_num
    intro μ
    rw [e]
    fin_cases μ <;> simp
  set τ := ∑ i, (α i 0 ^ 2 + α i 1 ^ 2) with hτ
  set c := c₀ / 2 with hc_def
  have hc : 0 < c := by positivity
  set q : ℝ := ((m - 3 : ℕ) : ℝ) + 3 / 2 with hq_def
  set H : (Fin m → ℝ) → ℝ := fun x => headSum (m - 1) x ^ (-q) with hH_def
  have hH : IntegrableOn H (simplexSet m) := by
    refine integrableOn_headSum_rpow (by omega) (by omega) (by positivity) ?_
    have : ((m - 3 : ℕ) : ℝ) + 2 = ((m - 1 : ℕ) : ℝ) := by
      rw [show m - 1 = (m - 3) + 2 by omega]; push_cast; ring
    simp only [q]
    linarith
  set β : Fin 3 → ℝ := fun t => lightB (Q t) CS τ c₀ * (Real.sqrt 8 / c₀ ^ (3 / 2 : ℝ))
    with hβ_def
  set G : Fin 3 → (Fin m → ℝ) → ℝ := fun t x =>
    ‖coeffOne (Q t) α p₁ x‖ / c ^ (m - 3) + ‖coeffTwo (Q t) α p₁ x‖ / c ^ (m - 4) +
      ‖coeffThree (Q t) α x‖ / c ^ (m - 5) with hG_def
  have hG : ∀ t, IntegrableOn (G t) (simplexSet m) := fun t =>
    ((((hI t).1.norm).div_const _).add (((hI t).2.1.norm).div_const _)).add
      (((hI t).2.2.norm).div_const _)
  have hβ0 : ∀ t, 0 ≤ β t := fun t => by
    have h1 := lqNorm_nonneg (Q t); have h2 := lqHess_nonneg (Q t)
    have h3 := lqQuart_nonneg (Q t)
    have hτ0 : 0 ≤ τ := by positivity
    simp only [β, lightB]
    positivity
  have hae0 : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ∀ i : Fin m, x i ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_all_iff]
    exact fun i => Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) i 0
  -- the absolute coefficient sums at `V₀`
  have hpt : ∀ᵐ x ∂(volume.restrict (simplexSet m)), x ∈ simplexSet m ∧
      (symanzikMatrix α (simplexPoint x)).PosDef ∧ ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a →
        0 < ∑ i, simplexPoint x i * Ms a b i ^ 2 ∧ ∀ t, majAbs3 (Q t) α p₁ x
          (∑ i, simplexPoint x i * Ms a b i ^ 2) ≤ G t x + β t * H x / b := by
    filter_upwards [ae_posDef α hm0 hspan, hae0] with x ⟨hxS, hPD⟩ hx0
    refine ⟨hxS, hPD, fun a b ha hab hb2 => ?_⟩
    have hb : 0 < b := ha.trans_le hab
    have hxle := (QED.Integration.SimplexMerge.mem_simplexSet_iff_le hm0 x).mp hxS
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    have hU0 : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
    set y := headSum (m - 1) x with hy_def
    have hy1 : y ≤ 1 := headSum_le_one hxle.1 hxle.2
    have hy0 : 0 < y := by
      have h0 : 0 < x ⟨0, hm0⟩ := lt_of_le_of_ne (hxle.1 _) (hx0 _).symm
      exact h0.trans_le (le_headSum hxle.1 (by simp; omega))
    set W := ∑ i, simplexPoint x i * Ms a b i ^ 2 with hW_def
    have hVx : c₀ * y + (1 - y) * a ^ 2 ≤ W := hV a b ha hab x hxS
    have ha2 : 0 ≤ (1 - y) * a ^ 2 := mul_nonneg (by linarith) (sq_nonneg a)
    have hW0 : 0 < W := by nlinarith
    refine ⟨hW0, fun t => ?_⟩
    have hHb : 0 ≤ β t * H x / b :=
      div_nonneg (mul_nonneg (hβ0 t) (Real.rpow_nonneg hy0.le _)) hb.le
    by_cases hyc : 1 / 2 ≤ y
    · have hVc : c ≤ W := by simp only [c]; nlinarith
      have h := majAbs3_anti (Q t) α p₁ x hc hVc
      exact h.trans (le_add_of_nonneg_right hHb)
    · replace hyc := not_le.mp hyc
      have hUy : y / 2 ≤ symanzikU α (simplexPoint x) := by
        have := hU x hxS
        nlinarith
      have htr := trace_symanzikMatrix_le α hz.1 hz.2
      have hX : ∀ a', ‖loopComp (-loopShift α p₁ (simplexPoint x)) a'‖ ≤ CS := fun a' => by
        simp only [loopComp, Pi.neg_apply, ofReal_neg, norm_neg, Complex.norm_real,
          Real.norm_eq_abs]
        exact (hCS _ hz.1 hU0.ne' v a'.1 a'.2).trans
          (by simpa using mul_le_mul_of_nonneg_left (hv1 a'.2) hCS0)
      have hcy : c₀ * y ≤ W := by linarith
      have hb8 : b ^ 2 / 8 ≤ W := by nlinarith
      have h1 := maj_abs_corner_le (Q t) α p₁ hm (hq t) x hy0 hCS0 hc₀ hPD hUy htr hX hcy
      have h2 := one_div_corner_le (m - 3) hy0 hb hc₀ hcy hb8
      refine h1.trans (le_trans ?_ (le_add_of_nonneg_left (by
        simp only [G]; positivity)))
      have hB0 : 0 ≤ lightB (Q t) CS τ c₀ := by
        have := hβ0 t
        simp only [β] at this
        exact nonneg_of_mul_nonneg_left this (by positivity)
      calc lightB (Q t) CS τ c₀ / (y ^ (m - 3) * W ^ 2)
          = lightB (Q t) CS τ c₀ * (1 / (y ^ (m - 3) * W ^ 2)) := by ring
        _ ≤ lightB (Q t) CS τ c₀ * (Real.sqrt 8 / c₀ ^ (3 / 2 : ℝ) * (y ^ (-q) / b)) :=
            mul_le_mul_of_nonneg_left h2 hB0
        _ = β t * H x / b := by simp only [β, H]; ring
  -- the majorant
  set Gs : (Fin m → ℝ) → ℝ := fun x => G' x + ∑ t, G t x with hGs
  set Hs : (Fin m → ℝ) → ℝ := fun x => H' x + ∑ t, β t * H x with hHs
  have hGsi : IntegrableOn Gs (simplexSet m) :=
    hG'.add (integrable_finsetSum _ fun t _ => hG t)
  have hHsi : IntegrableOn Hs (simplexSet m) :=
    hH'.add (integrable_finsetSum _ fun t _ => hH.const_mul (β t))
  refine ⟨π ^ 4 * ∫ x in simplexSet m, Gs x, π ^ 4 * ∫ x in simplexSet m, Hs x,
    fun s hs a b ha hab hb2 => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  have hs0 : 0 ≤ s := by linarith
  set r := Real.sqrt s with hr_def
  have hr1 : 1 ≤ r := by rw [hr_def, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hs
  have hr2 : r ^ 2 = s := Real.sq_sqrt hs0
  -- the quartic along the ray
  set R : LoopQuartic := qsum Finset.univ (fun t : Fin 3 => ((s : ℂ)) ^ (t : ℕ))
    (fun t => dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) with hR
  have hRe : R.eval = N (majRayVec s) := by
    funext ℓ
    rw [maj_majRayVec_eq hs0, hN r hr1]
    simp only [hR, eval_qsum, eval_dilateQ, one_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 2
    rw [← hr2]; push_cast; ring
  rw [pvOf_eq hRe, hmom s hs0, norm_mul, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  set g : (Fin m → ℝ) → ℝ := fun x => s * (Gs x + Hs x * b⁻¹) with hg_def
  have hg : IntegrableOn g (simplexSet m) :=
    (hGsi.add (hHsi.mul_const b⁻¹)).const_mul s
  have hint : ‖∫ x in simplexSet m, paramIntegrand R α (r • p₁) (Ms a b) 0 x‖ ≤
      ∫ x in simplexSet m, g x := by
    refine norm_integral_le_of_norm_le hg ?_
    filter_upwards [hpt, hTop] with x ⟨hxS, hPD, hx⟩ hT
    obtain ⟨hW0, hA⟩ := hx a b ha hab hb2
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    set W := ∑ i, simplexPoint x i * Ms a b i ^ 2 with hW_def
    set Bx := remainder α (simplexPoint x) cs with hBx
    have hB0 : 0 ≤ Bx := remainder_nonneg α hz.1 hPD.det_pos.ne' cs
    have hVe : symanzikV α (r • p₁) (Ms a b) (simplexPoint x) = W + s * Bx := by
      rw [← hmom s hs0]
      exact maj_symanzikV_ray α (Ms a b) _ cs hs0
    have hWV : W ≤ W + s * Bx := le_add_of_nonneg_right (mul_nonneg hs0 hB0)
    have hV0 : 0 < symanzikV α (r • p₁) (Ms a b) (simplexPoint x) := by
      rw [hVe]; linarith
    have hP := fun t => maj_norm_paramIntegrand_dilate_le (Q t) α p₁ (Ms a b) x hr1 hV0
    rw [hVe] at hP
    have hM := fun t => majAbs3_anti (Q t) α p₁ x hW0 hWV
    simp only [majAbs3] at hM hA
    rw [hR, paramIntegrand_qsum, Fin.sum_univ_three]
    refine (norm_add₃_le).trans ?_
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0,
      Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_mul, pow_one]
    have hT2 := hT s hs a b ha hab hb2
    have hsq : (r ^ 2)⁻¹ ≤ 1 := by rw [hr2]; exact inv_le_one_of_one_le₀ hs
    set e₁ := fun t : Fin 3 => ‖coeffOne (Q t) α p₁ x‖ / (W + s * Bx) ^ (m - 3)
    set e₂ := fun t : Fin 3 => ‖coeffTwo (Q t) α p₁ x‖ / (W + s * Bx) ^ (m - 4) +
      ‖coeffThree (Q t) α x‖ / (W + s * Bx) ^ (m - 5)
    have he₁ : ∀ t, 0 ≤ e₁ t := fun t => by simp only [e₁]; positivity
    have he₂ : ∀ t, 0 ≤ e₂ t := fun t => by simp only [e₂]; positivity
    have hP' : ∀ t, ‖paramIntegrand (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) α (r • p₁) (Ms a b) 0 x‖
        ≤ e₁ t + e₂ t / s := fun t => by rw [← hr2]; exact hP t
    have hS : ∀ t, e₁ t + e₂ t ≤ G t x + β t * H x / b := fun t =>
      ((add_assoc _ _ _).symm.le.trans (hM t)).trans (hA t)
    have hT2' : e₁ 2 * s ^ 2 ≤ s * (G' x + H' x / b) := by
      have := hT2
      simp only [e₁]
      rw [div_mul_eq_mul_div]
      exact this
    have k0 := hP' 0
    have k1 := mul_le_mul_of_nonneg_left (hP' 1) hs0
    have k2 := mul_le_mul_of_nonneg_left (hP' 2) (sq_nonneg s)
    have hs1 : (1 : ℝ) ≤ s := hs
    have q0 : e₁ 0 + e₂ 0 / s ≤ s * (e₁ 0 + e₂ 0) := by
      have : e₂ 0 / s ≤ e₂ 0 := div_le_self (he₂ 0) hs1
      have h1 : e₁ 0 ≤ s * e₁ 0 := le_mul_of_one_le_left (he₁ 0) hs1
      have h2 : e₂ 0 ≤ s * e₂ 0 := le_mul_of_one_le_left (he₂ 0) hs1
      calc e₁ 0 + e₂ 0 / s ≤ s * e₁ 0 + s * e₂ 0 := by linarith
        _ = s * (e₁ 0 + e₂ 0) := by ring
    have q1 : s * (e₁ 1 + e₂ 1 / s) ≤ s * (e₁ 1 + e₂ 1) := by
      have : e₂ 1 / s ≤ e₂ 1 := div_le_self (he₂ 1) hs1
      exact mul_le_mul_of_nonneg_left (by linarith) hs0
    have q2 : s ^ 2 * (e₁ 2 + e₂ 2 / s) = e₁ 2 * s ^ 2 + s * e₂ 2 := by
      field_simp
    have hsum : s * (e₁ 0 + e₂ 0) + s * (e₁ 1 + e₂ 1) + s * e₂ 2 ≤
        s * ((G 0 x + β 0 * H x / b) + (G 1 x + β 1 * H x / b) + (G 2 x + β 2 * H x / b)) := by
      have h2 : e₂ 2 ≤ G 2 x + β 2 * H x / b := (le_add_of_nonneg_left (he₁ 2)).trans (hS 2)
      have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hS 0) (hS 1)) h2) hs0
      calc s * (e₁ 0 + e₂ 0) + s * (e₁ 1 + e₂ 1) + s * e₂ 2
          = s * (e₁ 0 + e₂ 0 + (e₁ 1 + e₂ 1) + e₂ 2) := by ring
        _ ≤ _ := this
    have hfin : s * ((G 0 x + β 0 * H x / b) + (G 1 x + β 1 * H x / b) +
        (G 2 x + β 2 * H x / b)) + s * (G' x + H' x / b) = g x := by
      simp only [hg_def, hGs, hHs, Fin.sum_univ_three]
      ring
    rw [← hfin]
    calc _ ≤ (e₁ 0 + e₂ 0 / s) + s * (e₁ 1 + e₂ 1 / s) + s ^ 2 * (e₁ 2 + e₂ 2 / s) :=
          add_le_add (add_le_add k0 k1) k2
      _ ≤ s * (e₁ 0 + e₂ 0) + s * (e₁ 1 + e₂ 1) + (e₁ 2 * s ^ 2 + s * e₂ 2) := by
          rw [q2]; exact add_le_add (add_le_add q0 q1) le_rfl
      _ = (s * (e₁ 0 + e₂ 0) + s * (e₁ 1 + e₂ 1) + s * e₂ 2) + e₁ 2 * s ^ 2 := by ring
      _ ≤ _ := add_le_add hsum hT2'
  have hgi : ∫ x in simplexSet m, g x =
      s * ((∫ x in simplexSet m, Gs x) + (∫ x in simplexSet m, Hs x) / b) := by
    simp only [hg_def]
    rw [integral_const_mul, integral_add hGsi (hHsi.mul_const b⁻¹), integral_mul_const]
    ring
  rw [hgi] at hint
  calc π ^ 4 * ‖∫ x in simplexSet m, paramIntegrand R α (r • p₁) (Ms a b) 0 x‖
      ≤ π ^ 4 * (s * ((∫ x in simplexSet m, Gs x) + (∫ x in simplexSet m, Hs x) / b)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by ring

end Gen

end QED.GradedProof.RPi4

end
