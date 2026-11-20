/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Chain
public import QED.TwoLoop.ClassLimitParametric

/-!
# (R-Π₄) step L7: the parametric integrand near the soft-photon corner

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L7 (light photon
pair). Near the corner where the fermion parameters are small (`y = ∑_ferm zᵢ → 0`), the
parametric integrand of a piece with seven or eight lines is bounded explicitly: with `U ≥ y/2`,
`|(A⁻¹)ₛᵣ| ≤ tr A / det A ≤ 2τ/y`, a bounded shift and `V ≥ c₀ y`, the three terms
`Tⱼ V^{-nⱼ}` of `QED.TwoLoop.ClassLimit.paramIntegrand_eq` are at most `B / (y^{m-3} V²)`.

* `lqNorm`, `lqHess`, `lqQuart`: coefficient norms of a quartic;
  `norm_evalC_le_lqNorm`, `norm_contractTwo_le`, `norm_contractFour_le`: the numerator
  contractions bounded by them;
* `loopShift_eq_mulVec`, `exists_abs_loopShift_smul_le`: for external momenta `csᵢ k` the shift
  is at most `C |k^μ|`, uniformly on the simplex (Cauchy–Binet bound of
  `QED.Integration.TwoLoop.exists_abs_mulVec_coefVec_le`);
* `lightB`, `norm_paramIntegrand_le_corner`: the corner bound.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit Matrix
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### Coefficient bounds for a numerator of degree at most four -/

section Coeff

variable (Q : LoopQuartic)

/-- The sum of the norms of all coefficients of a quartic. -/
noncomputable def lqNorm : ℝ :=
  ‖Q.const‖ + ∑ a, ‖Q.lin a‖ + ∑ a, ∑ b, ‖Q.quad a b‖ + ∑ a, ∑ b, ∑ c, ‖Q.cub a b c‖ +
    ∑ a, ∑ b, ∑ c, ∑ d, ‖Q.quart a b c d‖

/-- The sum of the bounds `hessBound` of the coefficients `Hₐ_b`. -/
noncomputable def lqHess : ℝ := ∑ a, ∑ b, Q.hessBound a b

/-- The sum of the norms of the quartic coefficients. -/
noncomputable def lqQuart : ℝ := ∑ a, ∑ b, ∑ c, ∑ d, ‖Q.quart a b c d‖

theorem lqNorm_nonneg : 0 ≤ lqNorm Q := by unfold lqNorm; positivity

theorem lqHess_nonneg : 0 ≤ lqHess Q :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Q.hessBound_nonneg a b

theorem lqQuart_nonneg : 0 ≤ lqQuart Q := by unfold lqQuart; positivity

theorem pow_le_one_add_pow_four {K : ℝ} (hK : 0 ≤ K) {j : ℕ} (hj : j ≤ 4) :
    K ^ j ≤ (1 + K) ^ 4 :=
  (pow_le_pow_left₀ hK (by linarith) j).trans (pow_le_pow_right₀ (by linarith) hj)

/-- `‖P(X)‖ ≤ ‖P‖ (1 + K)⁴` for `‖Xₐ‖ ≤ K`. -/
theorem norm_evalC_le_lqNorm (X : LoopIndex → ℂ) {K : ℝ} (hK : 0 ≤ K) (hX : ∀ a, ‖X a‖ ≤ K) :
    ‖Q.evalC X‖ ≤ lqNorm Q * (1 + K) ^ 4 := by
  have h4 := fun j (hj : j ≤ 4) => pow_le_one_add_pow_four hK hj
  have hp : 0 ≤ (1 + K) ^ 4 := by positivity
  have e1 : ‖∑ a, Q.lin a * X a‖ ≤ (∑ a, ‖Q.lin a‖) * (1 + K) ^ 4 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((hX a).trans (by simpa using h4 1 (by norm_num)))
      (norm_nonneg _)
  have e2 : ‖∑ a, ∑ b, Q.quad a b * (X a * X b)‖ ≤
      (∑ a, ∑ b, ‖Q.quad a b‖) * (1 + K) ^ 4 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖X a‖ * ‖X b‖ ≤ K ^ 2 := by
          rw [sq]; exact mul_le_mul (hX a) (hX b) (norm_nonneg _) hK
      _ ≤ _ := h4 2 (by norm_num)
  have e3 : ‖∑ a, ∑ b, ∑ c, Q.cub a b c * (X a * X b * X c)‖ ≤
      (∑ a, ∑ b, ∑ c, ‖Q.cub a b c‖) * (1 + K) ^ 4 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul, norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖X a‖ * ‖X b‖ * ‖X c‖ ≤ K * K * K :=
          mul_le_mul (mul_le_mul (hX a) (hX b) (norm_nonneg _) hK) (hX c) (norm_nonneg _)
            (by positivity)
      _ = K ^ 3 := by ring
      _ ≤ _ := h4 3 (by norm_num)
  have e4 : ‖∑ a, ∑ b, ∑ c, ∑ d, Q.quart a b c d * (X a * X b * X c * X d)‖ ≤
      lqQuart Q * (1 + K) ^ 4 := by
    unfold lqQuart
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖X a‖ * ‖X b‖ * ‖X c‖ * ‖X d‖ ≤ K * K * K * K :=
          mul_le_mul (mul_le_mul (mul_le_mul (hX a) (hX b) (norm_nonneg _) hK) (hX c)
            (norm_nonneg _) (by positivity)) (hX d) (norm_nonneg _) (by positivity)
      _ = K ^ 4 := by ring
      _ ≤ _ := h4 4 le_rfl
  have e0 : ‖Q.const‖ ≤ ‖Q.const‖ * (1 + K) ^ 4 :=
    le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (by linarith))
  unfold LoopQuartic.evalC
  set c := Q.const
  set L := ∑ a, Q.lin a * X a
  set Qd := ∑ a, ∑ b, Q.quad a b * (X a * X b)
  set Cu := ∑ a, ∑ b, ∑ c, Q.cub a b c * (X a * X b * X c)
  set R := ∑ a, ∑ b, ∑ c, ∑ d, Q.quart a b c d * (X a * X b * X c * X d)
  have n1 := norm_add_le (c + L + Qd + Cu) R
  have n2 := norm_add_le (c + L + Qd) Cu
  have n3 := norm_add_le (c + L) Qd
  have n4 := norm_add_le c L
  unfold lqNorm
  unfold lqQuart at e4
  nlinarith

/-- `‖∑ₐ_b Hₐ_b(X) Gₐ_b‖ ≤ (∑ hessBound) (1 + K + K²) g` for `‖Xₐ‖ ≤ K`, `|(A⁻¹)ₛᵣ| ≤ g`. -/
theorem norm_contractTwo_le (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) {K g : ℝ}
    (hK : 0 ≤ K) (hX : ∀ a, ‖X a‖ ≤ K) (hg : ∀ s r, |A⁻¹ s r| ≤ g) :
    ‖Q.contractTwo A X‖ ≤ lqHess Q * (1 + (K + K ^ 2)) * g := by
  have h1 : ∀ a, ‖X a‖ ≤ 1 + (K + K ^ 2) := fun a => by nlinarith [hX a]
  have h2 : ∀ a b, ‖X a * X b‖ ≤ K + K ^ 2 := fun a b => by
    rw [norm_mul]
    nlinarith [mul_le_mul (hX a) (hX b) (norm_nonneg _) hK]
  have hG : ∀ a b : LoopIndex, |loopMetricInv A a b| ≤ g := fun a b => by
    simp only [loopMetricInv, abs_mul]
    have hm : |Minkowski.metric a.2 b.2| ≤ 1 := by
      unfold Minkowski.metric; split_ifs <;> simp
    calc |Minkowski.metric a.2 b.2| * |A⁻¹ a.1 b.1| ≤ 1 * g :=
          mul_le_mul hm (hg _ _) (abs_nonneg _) zero_le_one
      _ = g := one_mul g
  unfold LoopQuartic.contractTwo lqHess
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  exact mul_le_mul (Q.norm_hess_le X h1 h2 (by positivity) a b) (hG a b) (abs_nonneg _)
    (mul_nonneg (Q.hessBound_nonneg _ _) (by positivity))

/-- `‖∑ Rₐ_bcd Πₐ_bcd(G)‖ ≤ (∑ ‖R‖) 3 g²` for `|(A⁻¹)ₛᵣ| ≤ g`. -/
theorem norm_contractFour_le (A : Matrix (Fin 2) (Fin 2) ℝ) {g : ℝ}
    (hg : ∀ s r, |A⁻¹ s r| ≤ g) : ‖Q.contractFour A‖ ≤ lqQuart Q * (3 * g ^ 2) := by
  have hg0 : 0 ≤ g := (abs_nonneg _).trans (hg 0 0)
  have hG : ∀ a b : LoopIndex, |loopMetricInv A a b| ≤ g := fun a b => by
    simp only [loopMetricInv, abs_mul]
    have hm : |Minkowski.metric a.2 b.2| ≤ 1 := by
      unfold Minkowski.metric; split_ifs <;> simp
    calc |Minkowski.metric a.2 b.2| * |A⁻¹ a.1 b.1| ≤ 1 * g :=
          mul_le_mul hm (hg _ _) (abs_nonneg _) zero_le_one
      _ = g := one_mul g
  have hp : ∀ a b c d, |matPair (loopMetricInv A) a b c d| ≤ 3 * g ^ 2 := fun a b c d => by
    have hq : ∀ a b c d : LoopIndex,
        |loopMetricInv A a b * loopMetricInv A c d| ≤ g ^ 2 := fun a b c d => by
      rw [abs_mul, sq]
      exact mul_le_mul (hG a b) (hG c d) (abs_nonneg _) hg0
    unfold matPair
    calc _ ≤ |loopMetricInv A a b * loopMetricInv A c d| +
          |loopMetricInv A a c * loopMetricInv A b d| +
          |loopMetricInv A a d * loopMetricInv A b c| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ _ := by linarith [hq a b c d, hq a c b d, hq a d b c]
  unfold LoopQuartic.contractFour lqQuart
  simp only [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hp a b c d) (norm_nonneg _)

theorem contractFour_eq_zero_of_quart (A : Matrix (Fin 2) (Fin 2) ℝ) (hq : Q.quart = 0) :
    Q.contractFour A = 0 := by
  simp [LoopQuartic.contractFour, hq]

end Coeff

/-! ### The loop shift along external momenta proportional to one vector -/

section Shift

variable {m : ℕ}

theorem loopShift_eq_mulVec (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) (s : Fin 2) (μ : Fin 4) :
    loopShift α p z s μ = ((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z (fun i => p i μ)) s := by
  refine Fin.cases ?_ (fun c => ?_) μ
  · simp [loopShift, loopMomenta, energyShift]
  · simp [loopShift, loopMomenta, spatialShift]

/-- **The shift is bounded by the external vector**: `|S(z)ₛ^μ| ≤ C |k^μ|` for external line
momenta `csᵢ k`, uniformly on `z ≥ 0` with `U ≠ 0`. -/
theorem exists_abs_loopShift_smul_le (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → symanzikU α z ≠ 0 →
      ∀ (k : Fin 4 → ℝ) s μ, |loopShift α (fun i => cs i • k) z s μ| ≤ C * |k μ| := by
  obtain ⟨C, hC⟩ := exists_abs_mulVec_coefVec_le α cs
  refine ⟨max C 0, le_max_right _ _, fun z hz hU k s μ => ?_⟩
  have e : coefVec α z (fun i => (cs i • k) μ) = k μ • coefVec α z cs := by
    funext t
    simp only [coefVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [loopShift_eq_mulVec, e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hC z hz hU s).trans (le_max_left _ _)) (abs_nonneg _)

end Shift

/-! ### The integrand near the soft-photon corner -/

section Corner

theorem three_term_le {y V ρ t₁ t₂ t₃ a₁ a₂ a₃ : ℝ} (hy : 0 < y) (hV : 0 < V) (hr : y / V ≤ ρ)
    (h1 : t₁ * y ^ 2 ≤ a₁) (h2 : t₂ * y ^ 3 ≤ a₂) (h3 : t₃ * y ^ 4 ≤ a₃) (ht₁ : 0 ≤ t₁)
    (ht₂ : 0 ≤ t₂) :
    t₁ / V ^ 4 + t₂ / V ^ 3 + t₃ / V ^ 2 ≤ (a₁ * ρ ^ 2 + a₂ * ρ + a₃) / (y ^ 4 * V ^ 2) := by
  have hr0 : 0 ≤ y / V := by positivity
  have e : t₁ / V ^ 4 + t₂ / V ^ 3 + t₃ / V ^ 2 =
      ((t₁ * y ^ 2) * (y / V) ^ 2 + (t₂ * y ^ 3) * (y / V) + t₃ * y ^ 4) / (y ^ 4 * V ^ 2) := by
    field_simp
  rw [e]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have q1 : (t₁ * y ^ 2) * (y / V) ^ 2 ≤ a₁ * ρ ^ 2 :=
    mul_le_mul h1 (pow_le_pow_left₀ hr0 hr 2) (by positivity)
      ((by positivity : (0:ℝ) ≤ t₁ * y ^ 2).trans h1)
  have q2 : (t₂ * y ^ 3) * (y / V) ≤ a₂ * ρ :=
    mul_le_mul h2 hr hr0 ((by positivity : (0:ℝ) ≤ t₂ * y ^ 3).trans h2)
  linarith

theorem two_term_le {y V ρ t₁ t₂ a₁ a₂ : ℝ} (hy : 0 < y) (hV : 0 < V) (hr : y / V ≤ ρ)
    (h1 : t₁ * y ^ 2 ≤ a₁) (h2 : t₂ * y ^ 3 ≤ a₂) (ht₁ : 0 ≤ t₁) :
    t₁ / V ^ 3 + t₂ / V ^ 2 ≤ (a₁ * ρ + a₂) / (y ^ 3 * V ^ 2) := by
  have hr0 : 0 ≤ y / V := by positivity
  have e : t₁ / V ^ 3 + t₂ / V ^ 2 = ((t₁ * y ^ 2) * (y / V) + t₂ * y ^ 3) / (y ^ 3 * V ^ 2) := by
    field_simp
  rw [e]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have q1 : (t₁ * y ^ 2) * (y / V) ≤ a₁ * ρ :=
    mul_le_mul h1 hr hr0 ((by positivity : (0:ℝ) ≤ t₁ * y ^ 2).trans h1)
  linarith

/-- The constant of the soft-photon-corner bound of a quartic. -/
noncomputable def lightB (Q : LoopQuartic) (K τ c₀ : ℝ) : ℝ :=
  24 * lqNorm Q * (1 + K) ^ 4 * (1 + 1 / c₀) ^ 2 +
    8 * τ * lqHess Q * (1 + (K + K ^ 2)) * (1 + 1 / c₀) + 12 * τ ^ 2 * lqQuart Q

variable {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ)

/-- **The parametric integrand near the soft-photon corner.** At a point where `U ≥ y/2`,
`tr A ≤ τ`, the shift is bounded by `K` and `V ≥ c₀ y`, the integrand with seven or eight lines is
at most `B / (y^{m-3} V²)`. -/
theorem norm_paramIntegrand_le_corner (hm : m = 6 ∨ m = 7) (hq : 7 ≤ m ∨ Q.quart = 0)
    (x : Fin m → ℝ) {y K τ c₀ : ℝ} (hy : 0 < y) (hK : 0 ≤ K) (hc₀ : 0 < c₀)
    (hA : (symanzikMatrix α (simplexPoint x)).PosDef)
    (hU : y / 2 ≤ symanzikU α (simplexPoint x))
    (htr : (symanzikMatrix α (simplexPoint x)).trace ≤ τ)
    (hX : ∀ a, ‖loopComp (-loopShift α p (simplexPoint x)) a‖ ≤ K)
    (hV : c₀ * y ≤ symanzikV α p M (simplexPoint x)) :
    ‖paramIntegrand Q α p M 0 x‖ ≤
      lightB Q K τ c₀ / (y ^ (m - 3) * symanzikV α p M (simplexPoint x) ^ 2) := by
  set A := symanzikMatrix α (simplexPoint x)
  set U := symanzikU α (simplexPoint x)
  set V := symanzikV α p M (simplexPoint x)
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
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
  have hW : ∀ n : ℕ, ‖(wBase α p M 0 x ^ n)⁻¹‖ = 1 / V ^ n := fun n => by
    simp only [wBase, zero_mul, ofReal_zero, sub_zero, norm_inv, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, one_div]
    exact congrArg (fun t => (t ^ n)⁻¹) (abs_of_pos hV0)
  have hr : y / V ≤ 1 / c₀ := by
    rw [div_le_div_iff₀ hV0 hc₀]
    linarith
  have hB1 : 0 ≤ lqNorm Q * (1 + K) ^ 4 := mul_nonneg (lqNorm_nonneg Q) (by positivity)
  have hB2 : 0 ≤ lqHess Q * (1 + (K + K ^ 2)) * (2 * τ) :=
    mul_nonneg (mul_nonneg (lqHess_nonneg Q) (by positivity)) (by positivity)
  have hB3 : 0 ≤ lqQuart Q := lqQuart_nonneg Q
  have hc1 : 1 / c₀ ≤ 1 + 1 / c₀ := by linarith
  have hc2 : (1 / c₀) ^ 2 ≤ (1 + 1 / c₀) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hc1 2
  rw [paramIntegrand_eq]
  refine (norm_add₃_le).trans ?_
  simp only [norm_mul, hW]
  rcases hm with rfl | rfl
  · -- seven lines: no quartic part
    have hq0 : Q.quart = 0 := hq.resolve_left (by norm_num)
    have h3 : coeffThree Q α x = 0 := by
      simp [coeffThree, contractFour_eq_zero_of_quart Q _ hq0]
    simp only [h3, norm_zero, zero_mul, add_zero]
    norm_num at n1 n2 ⊢
    have := two_term_le (t₁ := ‖coeffOne Q α p x‖) (t₂ := ‖coeffTwo Q α p x‖) hy hV0 hr n1 n2
      (norm_nonneg _)
    refine (le_of_eq (by ring)).trans (this.trans (div_le_div_of_nonneg_right ?_ (by positivity)))
    unfold lightB
    nlinarith [lqQuart_nonneg Q, sq_nonneg τ]
  · norm_num at n1 n2 n3 ⊢
    have := three_term_le (t₁ := ‖coeffOne Q α p x‖) (t₂ := ‖coeffTwo Q α p x‖)
      (t₃ := ‖coeffThree Q α x‖) hy hV0 hr n1 n2 n3 (norm_nonneg _) (norm_nonneg _)
    refine (le_of_eq (by ring)).trans (this.trans (div_le_div_of_nonneg_right ?_ (by positivity)))
    unfold lightB
    nlinarith [lqQuart_nonneg Q, sq_nonneg τ]

end Corner

end QED.GradedProof.RPi4

end
