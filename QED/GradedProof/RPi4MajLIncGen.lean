/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajLGen

/-!
# (R-Π₄) step L10, two loops: increments of a piece at a light photon pair along the ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.IR,
increments). The increment counterpart of `QED.GradedProof.RPi4.maj_pvOf_lray`. Along the ray
the parametric integrand is a sum of monomials `T s^{t-j} / (W + s B)^n` with coefficients `T`
independent of `s`, `t, j ≤ 2`, `n ≤ m - 3`. For `1 ≤ s' ≤ s ≤ 2s'` each monomial moves by at
most `(3 + n) ε` times its value at `s'`, `ε = (s - s')/s'` (the power `s^{t-j}` by `3 ε`, the
denominator by `n ε` since `s B ≤ W + s B`). So the increment of the integrand is at most
`m ε` times the absolute coefficient sum at `s'`, which the value proof bounds by
`s' (G + H/b)` with integrable `G`, `H` (including the top monomial, by the same hypothesis).

* `majInc_phi_sub_le`, `majInc_pow_div_sub_le`: the one-monomial increments;
* `majIncX`, `majIncA`: one dilated quartic times `s^t` and its absolute coefficient sum;
  `majIncX_norm_le`, `majIncX_sub_le`, `maj_paramIntegrand_dilate_eq_majIncX`;
* **`maj_pvOf_lrayInc`**: under the hypotheses of `maj_pvOf_lray`, the parametric value along
  the ray has increments at most `(s - s') (C₁ + C₂/b)` for `1 ≤ s' ≤ s ≤ 2s'` and light
  comparable photon pairs.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.MassScaling Matrix
open QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### One monomial -/

/-- `|a/Vⁿ - a'/V'ⁿ| ≤ (3 + n) ε a'/V'ⁿ` with `V = W + s B`, `ε = (s - s')/s'`, if
`|a - a'| ≤ 3 ε a'`. -/
theorem majInc_phi_sub_le {W B s s' a a' : ℝ} (hW : 0 < W) (hB : 0 ≤ B) (hs' : 1 ≤ s')
    (hss : s' ≤ s) (ha' : 0 ≤ a') (ha : |a - a'| ≤ 3 * ((s - s') / s') * a') (n : ℕ) :
    |a / (W + s * B) ^ n - a' / (W + s' * B) ^ n| ≤
      (3 + n) * ((s - s') / s') * (a' / (W + s' * B) ^ n) := by
  have hs0 : 0 < s' := by linarith
  have hsB : s' * B ≤ s * B := mul_le_mul_of_nonneg_right hss hB
  have hV' : 0 < W + s' * B := by nlinarith
  have hVV : W + s' * B ≤ W + s * B := by linarith
  have hV : 0 < W + s * B := hV'.trans_le hVV
  have h1 := maj_phi_split hV' hVV a ha' n
  have h2 := maj_phi_second hB hV' hss ha' n
  have hd : 0 ≤ s - s' := by linarith
  have hε : 0 ≤ (s - s') / s' := div_nonneg hd hs0.le
  have hq : 0 ≤ a' / (W + s' * B) ^ n := div_nonneg ha' (pow_pos hV' n).le
  have k1 : |a - a'| / (W + s * B) ^ n ≤ 3 * ((s - s') / s') * (a' / (W + s' * B) ^ n) := by
    calc |a - a'| / (W + s * B) ^ n ≤ |a - a'| / (W + s' * B) ^ n :=
          div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hV' n)
            (pow_le_pow_left₀ hV'.le hVV n)
      _ ≤ (3 * ((s - s') / s') * a') / (W + s' * B) ^ n :=
          div_le_div_of_nonneg_right ha (pow_pos hV' n).le
      _ = _ := by ring
  have hBV : (s - s') * (B / (W + s * B)) ≤ (s - s') / s' := by
    have : B / (W + s * B) ≤ 1 / s' := by
      rw [div_le_div_iff₀ hV hs0]
      nlinarith
    calc (s - s') * (B / (W + s * B)) ≤ (s - s') * (1 / s') := mul_le_mul_of_nonneg_left this hd
      _ = _ := by ring
  have k2 : n * (s - s') * (B / (W + s * B)) * a' / (W + s' * B) ^ n ≤
      n * ((s - s') / s') * (a' / (W + s' * B) ^ n) := by
    have e : n * (s - s') * (B / (W + s * B)) * a' / (W + s' * B) ^ n =
        n * ((s - s') * (B / (W + s * B))) * (a' / (W + s' * B) ^ n) := by ring
    rw [e]
    gcongr
  calc _ ≤ _ := h1
    _ ≤ 3 * ((s - s') / s') * (a' / (W + s' * B) ^ n) +
        n * ((s - s') / s') * (a' / (W + s' * B) ^ n) := add_le_add k1 (h2.trans k2)
    _ = _ := by ring

/-- `|s^t/s^j - s'^t/s'^j| ≤ 3 ε s'^t/s'^j` for `t, j ≤ 2`, `1 ≤ s' ≤ s ≤ 2s'`. -/
theorem majInc_pow_div_sub_le {s s' : ℝ} (hs' : 1 ≤ s') (hss : s' ≤ s) (hs2 : s ≤ 2 * s')
    {t j : ℕ} (ht : t ≤ 2) (hj : j ≤ 2) :
    |s ^ t / s ^ j - s' ^ t / s' ^ j| ≤ 3 * ((s - s') / s') * (s' ^ t / s' ^ j) := by
  have hs0 : 0 < s' := by linarith
  have hs : 0 < s := by linarith
  have hd : 0 ≤ s - s' := by linarith
  rw [abs_le]
  interval_cases t <;> interval_cases j <;> constructor <;>
    · rw [← sub_nonneg]
      field_simp
      ring_nf
      nlinarith [mul_pos hs hs0, mul_pos (mul_pos hs hs0) hs0, mul_pos (mul_pos hs hs0) hs,
        mul_nonneg (mul_nonneg hd hd) hs.le, mul_nonneg (mul_nonneg hd hd) hs0.le,
        mul_nonneg hd (mul_nonneg hs0.le hs0.le), mul_nonneg hd (mul_nonneg hs.le hs0.le),
        mul_nonneg hd (mul_nonneg hs.le hs.le)]

/-! ### One dilated quartic along the ray -/

/-- One dilated quartic times `s^t` along the ray, at the denominator base `V`: the integrand
`s^t I(ℓ ↦ Q(ℓ/√s))` at the momenta `√s p` in the coefficients `T₁, T₂, T₃` at `p`. -/
noncomputable def majIncX (m t : ℕ) (T₁ T₂ T₃ : ℂ) (V s : ℝ) : ℂ :=
  (s : ℂ) ^ t * (1 * T₁ * ((V : ℂ) ^ (m - 3))⁻¹ +
    1 * (((Real.sqrt s)⁻¹ : ℝ) : ℂ) ^ 2 * T₂ * ((V : ℂ) ^ (m - 4))⁻¹ +
    1 * (((Real.sqrt s)⁻¹ : ℝ) : ℂ) ^ 4 * T₃ * ((V : ℂ) ^ (m - 5))⁻¹)

/-- Its absolute coefficient sum `s^t (‖T₁‖/V^{m-3} + (‖T₂‖/V^{m-4} + ‖T₃‖/V^{m-5})/s)`. -/
noncomputable def majIncA (m t : ℕ) (T₁ T₂ T₃ : ℂ) (V s : ℝ) : ℝ :=
  s ^ t * (‖T₁‖ / V ^ (m - 3) + (‖T₂‖ / V ^ (m - 4) + ‖T₃‖ / V ^ (m - 5)) / s)

theorem majIncX_eq (m t : ℕ) (T₁ T₂ T₃ : ℂ) (V : ℝ) {s : ℝ} (hs : 0 < s) :
    majIncX m t T₁ T₂ T₃ V s = T₁ * ((s ^ t / s ^ 0 / V ^ (m - 3) : ℝ) : ℂ) +
      T₂ * ((s ^ t / s ^ 1 / V ^ (m - 4) : ℝ) : ℂ) +
        T₃ * ((s ^ t / s ^ 2 / V ^ (m - 5) : ℝ) : ℂ) := by
  have hρ : ((((Real.sqrt s)⁻¹ : ℝ)) : ℂ) ^ 2 = (s : ℂ)⁻¹ := by
    rw [← ofReal_pow, inv_pow, Real.sq_sqrt hs.le, ofReal_inv]
  have hρ4 : ((((Real.sqrt s)⁻¹ : ℝ)) : ℂ) ^ 4 = ((s : ℂ)⁻¹) ^ 2 := by
    rw [← hρ]; ring
  simp only [majIncX, hρ, hρ4]
  push_cast
  ring

theorem majIncA_ge (m t : ℕ) (T₁ T₂ T₃ : ℂ) {V s : ℝ} (hV : 0 < V) (hs : 1 ≤ s) :
    ‖T₁‖ * (s ^ t / s ^ 0 / V ^ (m - 3)) + ‖T₂‖ * (s ^ t / s ^ 1 / V ^ (m - 4)) +
      ‖T₃‖ * (s ^ t / s ^ 2 / V ^ (m - 5)) ≤ majIncA m t T₁ T₂ T₃ V s := by
  have hs0 : 0 < s := by linarith
  have h3 : ‖T₃‖ * (s ^ t / s ^ 2 / V ^ (m - 5)) ≤ s ^ t * (‖T₃‖ / V ^ (m - 5)) / s := by
    have e : ‖T₃‖ * (s ^ t / s ^ 2 / V ^ (m - 5)) =
        s ^ t * (‖T₃‖ / V ^ (m - 5)) / s * (1 / s) := by
      field_simp
    rw [e]
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [div_le_one hs0]; exact hs
  have e : majIncA m t T₁ T₂ T₃ V s = ‖T₁‖ * (s ^ t / s ^ 0 / V ^ (m - 3)) +
      ‖T₂‖ * (s ^ t / s ^ 1 / V ^ (m - 4)) + s ^ t * (‖T₃‖ / V ^ (m - 5)) / s := by
    simp only [majIncA]
    field_simp
    ring
  rw [e]
  linarith

theorem majIncX_norm_le (m t : ℕ) (T₁ T₂ T₃ : ℂ) {V s : ℝ} (hV : 0 < V) (hs : 1 ≤ s) :
    ‖majIncX m t T₁ T₂ T₃ V s‖ ≤ majIncA m t T₁ T₂ T₃ V s := by
  have hs0 : 0 < s := by linarith
  rw [majIncX_eq m t T₁ T₂ T₃ V hs0]
  refine (norm_add₃_le).trans (le_trans (le_of_eq ?_) (majIncA_ge m t T₁ T₂ T₃ hV hs))
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]

theorem majIncX_sub_le {m : ℕ} (hm : 6 ≤ m) {t : ℕ} (ht : t ≤ 2) (T₁ T₂ T₃ : ℂ) {W B s s' : ℝ}
    (hW : 0 < W) (hB : 0 ≤ B) (hs' : 1 ≤ s') (hss : s' ≤ s) (hs2 : s ≤ 2 * s') :
    ‖majIncX m t T₁ T₂ T₃ (W + s * B) s - majIncX m t T₁ T₂ T₃ (W + s' * B) s'‖ ≤
      m * ((s - s') / s') * majIncA m t T₁ T₂ T₃ (W + s' * B) s' := by
  have hs0 : 0 < s' := by linarith
  have hV' : 0 < W + s' * B := by nlinarith
  have hε : 0 ≤ (s - s') / s' := div_nonneg (by linarith) hs0.le
  rw [majIncX_eq m t T₁ T₂ T₃ _ (hs0.trans_le hss), majIncX_eq m t T₁ T₂ T₃ _ hs0]
  set φ : ℕ → ℕ → ℝ → ℝ := fun j n σ => σ ^ t / σ ^ j / (W + σ * B) ^ n with hφ
  have hd : ∀ j n, j ≤ 2 → |φ j n s - φ j n s'| ≤ (3 + n) * ((s - s') / s') * φ j n s' :=
    fun j n hj => by
      simp only [hφ]
      refine (majInc_phi_sub_le hW hB hs' hss (by positivity)
        (majInc_pow_div_sub_le hs' hss hs2 ht hj) n).trans (le_of_eq ?_)
      ring
  have e : T₁ * ((s ^ t / s ^ 0 / (W + s * B) ^ (m - 3) : ℝ) : ℂ) +
      T₂ * ((s ^ t / s ^ 1 / (W + s * B) ^ (m - 4) : ℝ) : ℂ) +
        T₃ * ((s ^ t / s ^ 2 / (W + s * B) ^ (m - 5) : ℝ) : ℂ) -
      (T₁ * ((s' ^ t / s' ^ 0 / (W + s' * B) ^ (m - 3) : ℝ) : ℂ) +
        T₂ * ((s' ^ t / s' ^ 1 / (W + s' * B) ^ (m - 4) : ℝ) : ℂ) +
          T₃ * ((s' ^ t / s' ^ 2 / (W + s' * B) ^ (m - 5) : ℝ) : ℂ)) =
      T₁ * ((φ 0 (m - 3) s - φ 0 (m - 3) s' : ℝ) : ℂ) +
        T₂ * ((φ 1 (m - 4) s - φ 1 (m - 4) s' : ℝ) : ℂ) +
          T₃ * ((φ 2 (m - 5) s - φ 2 (m - 5) s' : ℝ) : ℂ) := by
    simp only [hφ]; push_cast; ring
  rw [e]
  refine (norm_add₃_le).trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := mul_le_mul_of_nonneg_left (hd 0 (m - 3) (by norm_num)) (norm_nonneg T₁)
  have h2 := mul_le_mul_of_nonneg_left (hd 1 (m - 4) (by norm_num)) (norm_nonneg T₂)
  have h3 := mul_le_mul_of_nonneg_left (hd 2 (m - 5) (by norm_num)) (norm_nonneg T₃)
  have hA := majIncA_ge m t T₁ T₂ T₃ hV' hs'
  have c3 : (3 + ((m - 3 : ℕ) : ℝ)) ≤ m := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have c4 : (3 + ((m - 4 : ℕ) : ℝ)) ≤ m := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have c5 : (3 + ((m - 5 : ℕ) : ℝ)) ≤ m := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have p1 : 0 ≤ ‖T₁‖ * φ 0 (m - 3) s' := by simp only [hφ]; positivity
  have p2 : 0 ≤ ‖T₂‖ * φ 1 (m - 4) s' := by simp only [hφ]; positivity
  have p3 : 0 ≤ ‖T₃‖ * φ 2 (m - 5) s' := by simp only [hφ]; positivity
  have g1 : ‖T₁‖ * ((3 + ((m - 3 : ℕ) : ℝ)) * ((s - s') / s') * φ 0 (m - 3) s') ≤
      m * ((s - s') / s') * (‖T₁‖ * φ 0 (m - 3) s') := by
    have := mul_le_mul_of_nonneg_right c3 (mul_nonneg hε p1)
    nlinarith
  have g2 : ‖T₂‖ * ((3 + ((m - 4 : ℕ) : ℝ)) * ((s - s') / s') * φ 1 (m - 4) s') ≤
      m * ((s - s') / s') * (‖T₂‖ * φ 1 (m - 4) s') := by
    have := mul_le_mul_of_nonneg_right c4 (mul_nonneg hε p2)
    nlinarith
  have g3 : ‖T₃‖ * ((3 + ((m - 5 : ℕ) : ℝ)) * ((s - s') / s') * φ 2 (m - 5) s') ≤
      m * ((s - s') / s') * (‖T₃‖ * φ 2 (m - 5) s') := by
    have := mul_le_mul_of_nonneg_right c5 (mul_nonneg hε p3)
    nlinarith
  have hA' : ‖T₁‖ * φ 0 (m - 3) s' + ‖T₂‖ * φ 1 (m - 4) s' + ‖T₃‖ * φ 2 (m - 5) s' ≤
      majIncA m t T₁ T₂ T₃ (W + s' * B) s' := hA
  have hm0 : (0 : ℝ) ≤ m * ((s - s') / s') := by positivity
  have := mul_le_mul_of_nonneg_left hA' hm0
  nlinarith

/-- The dilated integrand along the ray in the form `majIncX`. -/
theorem maj_paramIntegrand_dilate_eq_majIncX {m : ℕ} (Q : LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (x : Fin m → ℝ) {s : ℝ} (hs : 0 < s) (t : ℕ) :
    (s : ℂ) ^ t * paramIntegrand (dilateQ 1 (((Real.sqrt s)⁻¹ : ℝ) : ℂ) Q) α
        (Real.sqrt s • p) M 0 x =
      majIncX m t (coeffOne Q α p x) (coeffTwo Q α p x) (coeffThree Q α x)
        (symanzikV α (Real.sqrt s • p) M (simplexPoint x)) s := by
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  rw [paramIntegrand_eq, maj_coeffOne_dilateQ _ _ hr, maj_coeffTwo_dilateQ _ _ hr,
    maj_coeffThree_dilateQ]
  simp only [majIncX, wBase, ofReal_zero, zero_mul, sub_zero]

/-! ### The increments of a piece -/

/-- **Increments of a piece at a light comparable photon pair along the ray**: under the
hypotheses of `maj_pvOf_lray`, `‖pv(s) - pv(s')‖ ≤ (s - s') (C₁ + C₂/b)` for
`1 ≤ s' ≤ s ≤ 2s'`. -/
theorem maj_pvOf_lrayInc {m : ℕ} (hm : m = 6 ∨ m = 7) (α : Fin (m + 1) → Fin 2 → ℝ)
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
    ∃ C₁ C₂ : ℝ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' → ∀ a b : ℝ, 0 < a → a ≤ b →
      b ≤ 2 * a →
      ‖pvOf (N (majRayVec s)) α (fun i => cs i • majRayVec s) (Ms a b) -
          pvOf (N (majRayVec s')) α (fun i => cs i • majRayVec s') (Ms a b)‖ ≤
        (s - s') * (C₁ + C₂ / b) := by
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
  -- the absolute coefficient sums along the ray
  set A : ℝ → ℝ → ℝ → (Fin m → ℝ) → ℝ := fun a b σ x => ∑ t : Fin 3,
    majIncA m t (coeffOne (Q t) α p₁ x) (coeffTwo (Q t) α p₁ x) (coeffThree (Q t) α x)
      (∑ i, simplexPoint x i * Ms a b i ^ 2 + σ * remainder α (simplexPoint x) cs) σ with hA_def
  have hAg : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ∀ σ : ℝ, 1 ≤ σ → ∀ a b : ℝ, 0 < a →
      a ≤ b → b ≤ 2 * a → A a b σ x ≤ σ * (Gs x + Hs x * b⁻¹) := by
    filter_upwards [hpt, hTop] with x ⟨hxS, hPD, hx⟩ hT σ hσ a b ha hab hb2
    obtain ⟨hW0, hA⟩ := hx a b ha hab hb2
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    have hσ0 : 0 ≤ σ := by linarith
    set W := ∑ i, simplexPoint x i * Ms a b i ^ 2 with hW_def
    set Bx := remainder α (simplexPoint x) cs with hBx
    have hB0 : 0 ≤ Bx := remainder_nonneg α hz.1 hPD.det_pos.ne' cs
    have hWV : W ≤ W + σ * Bx := le_add_of_nonneg_right (mul_nonneg hσ0 hB0)
    have hM := fun t => majAbs3_anti (Q t) α p₁ x hW0 hWV
    simp only [majAbs3] at hM hA
    set e₁ := fun t : Fin 3 => ‖coeffOne (Q t) α p₁ x‖ / (W + σ * Bx) ^ (m - 3)
    set e₂ := fun t : Fin 3 => ‖coeffTwo (Q t) α p₁ x‖ / (W + σ * Bx) ^ (m - 4) +
      ‖coeffThree (Q t) α x‖ / (W + σ * Bx) ^ (m - 5)
    have hAe : A a b σ x = σ ^ 0 * (e₁ 0 + e₂ 0 / σ) + σ ^ 1 * (e₁ 1 + e₂ 1 / σ) +
        σ ^ 2 * (e₁ 2 + e₂ 2 / σ) := by
      rw [hA_def]
      simp only [Fin.sum_univ_three]
      rfl
    rw [hAe, pow_zero, one_mul, pow_one]
    have he₁ : ∀ t, 0 ≤ e₁ t := fun t => by simp only [e₁]; positivity
    have he₂ : ∀ t, 0 ≤ e₂ t := fun t => by simp only [e₂]; positivity
    have hS : ∀ t, e₁ t + e₂ t ≤ G t x + β t * H x / b := fun t =>
      ((add_assoc _ _ _).symm.le.trans (hM t)).trans (hA t)
    have hT2' : e₁ 2 * σ ^ 2 ≤ σ * (G' x + H' x / b) := by
      have := hT σ hσ a b ha hab hb2
      simp only [e₁]
      rw [div_mul_eq_mul_div]
      exact this
    have q0 : e₁ 0 + e₂ 0 / σ ≤ σ * (e₁ 0 + e₂ 0) := by
      have : e₂ 0 / σ ≤ e₂ 0 := div_le_self (he₂ 0) hσ
      have h1 : e₁ 0 ≤ σ * e₁ 0 := le_mul_of_one_le_left (he₁ 0) hσ
      have h2 : e₂ 0 ≤ σ * e₂ 0 := le_mul_of_one_le_left (he₂ 0) hσ
      calc e₁ 0 + e₂ 0 / σ ≤ σ * e₁ 0 + σ * e₂ 0 := by linarith
        _ = σ * (e₁ 0 + e₂ 0) := by ring
    have q1 : σ * (e₁ 1 + e₂ 1 / σ) ≤ σ * (e₁ 1 + e₂ 1) := by
      have : e₂ 1 / σ ≤ e₂ 1 := div_le_self (he₂ 1) hσ
      exact mul_le_mul_of_nonneg_left (by linarith) hσ0
    have q2 : σ ^ 2 * (e₁ 2 + e₂ 2 / σ) = e₁ 2 * σ ^ 2 + σ * e₂ 2 := by
      have : σ ≠ 0 := by positivity
      field_simp
    have hsum : σ * (e₁ 0 + e₂ 0) + σ * (e₁ 1 + e₂ 1) + σ * e₂ 2 ≤
        σ * ((G 0 x + β 0 * H x / b) + (G 1 x + β 1 * H x / b) + (G 2 x + β 2 * H x / b)) := by
      have h2 : e₂ 2 ≤ G 2 x + β 2 * H x / b := (le_add_of_nonneg_left (he₁ 2)).trans (hS 2)
      have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hS 0) (hS 1)) h2) hσ0
      calc σ * (e₁ 0 + e₂ 0) + σ * (e₁ 1 + e₂ 1) + σ * e₂ 2
          = σ * (e₁ 0 + e₂ 0 + (e₁ 1 + e₂ 1) + e₂ 2) := by ring
        _ ≤ _ := this
    have hfin : σ * ((G 0 x + β 0 * H x / b) + (G 1 x + β 1 * H x / b) +
        (G 2 x + β 2 * H x / b)) + σ * (G' x + H' x / b) = σ * (Gs x + Hs x * b⁻¹) := by
      simp only [hGs, hHs, Fin.sum_univ_three]
      ring
    rw [← hfin]
    calc _ ≤ σ * (e₁ 0 + e₂ 0) + σ * (e₁ 1 + e₂ 1) + (e₁ 2 * σ ^ 2 + σ * e₂ 2) := by
          rw [← q2]; exact add_le_add (add_le_add q0 q1) le_rfl
      _ = (σ * (e₁ 0 + e₂ 0) + σ * (e₁ 1 + e₂ 1) + σ * e₂ 2) + e₁ 2 * σ ^ 2 := by ring
      _ ≤ _ := add_le_add hsum hT2'
  refine ⟨π ^ 4 * m * ∫ x in simplexSet m, Gs x, π ^ 4 * m * ∫ x in simplexSet m, Hs x,
    fun s s' hs' hss hs2 a b ha hab hb2 => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  have hs : 1 ≤ s := hs'.trans hss
  -- the quartic along the ray and the integrand
  set R : ℝ → LoopQuartic := fun σ => qsum Finset.univ (fun t : Fin 3 => ((σ : ℂ)) ^ (t : ℕ))
    (fun t => dilateQ 1 (((Real.sqrt σ)⁻¹ : ℝ) : ℂ) (Q t)) with hR
  have hRe : ∀ σ : ℝ, 1 ≤ σ → (R σ).eval = N (majRayVec σ) := fun σ hσ => by
    have hσ0 : 0 ≤ σ := by linarith
    have hr1 : 1 ≤ Real.sqrt σ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hσ
    have hr2 : Real.sqrt σ ^ 2 = σ := Real.sq_sqrt hσ0
    funext ℓ
    rw [maj_majRayVec_eq hσ0, hN _ hr1]
    simp only [hR, eval_qsum, eval_dilateQ, one_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 2
    simp only [← ofReal_pow, hr2]
  set f : ℝ → (Fin m → ℝ) → ℂ := fun σ x =>
    paramIntegrand (R σ) α (Real.sqrt σ • p₁) (Ms a b) 0 x with hf
  have hfX : ∀ σ : ℝ, 0 < σ → ∀ x, f σ x = ∑ t : Fin 3,
      majIncX m t (coeffOne (Q t) α p₁ x) (coeffTwo (Q t) α p₁ x) (coeffThree (Q t) α x)
        (symanzikV α (Real.sqrt σ • p₁) (Ms a b) (simplexPoint x)) σ := fun σ hσ x => by
    simp only [hf, hR, paramIntegrand_qsum]
    exact Finset.sum_congr rfl fun t _ =>
      maj_paramIntegrand_dilate_eq_majIncX (Q t) α p₁ (Ms a b) x hσ t
  have hVe : ∀ σ : ℝ, 0 ≤ σ → ∀ x, symanzikV α (Real.sqrt σ • p₁) (Ms a b) (simplexPoint x) =
      ∑ i, simplexPoint x i * Ms a b i ^ 2 + σ * remainder α (simplexPoint x) cs :=
    fun σ hσ x => by
      rw [← hmom σ hσ]
      exact maj_symanzikV_ray α (Ms a b) _ cs hσ
  -- measurability and integrability
  have hmeas : ∀ σ : ℝ, 0 < σ → AEStronglyMeasurable (f σ) (volume.restrict (simplexSet m)) :=
    fun σ hσ => by
      rw [show f σ = fun x => ∑ t : Fin 3,
          majIncX m t (coeffOne (Q t) α p₁ x) (coeffTwo (Q t) α p₁ x) (coeffThree (Q t) α x)
            (symanzikV α (Real.sqrt σ • p₁) (Ms a b) (simplexPoint x)) σ from
        funext (hfX σ hσ)]
      have hVm : Measurable fun x : Fin m → ℝ =>
          ((symanzikV α (Real.sqrt σ • p₁) (Ms a b) (simplexPoint x) : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp ((measurable_symanzikV α _ (Ms a b)).comp
          continuous_simplexPoint'.measurable)
      have hw : ∀ k : ℕ, AEStronglyMeasurable (fun x : Fin m → ℝ =>
          (((symanzikV α (Real.sqrt σ • p₁) (Ms a b) (simplexPoint x) : ℝ) : ℂ) ^ k)⁻¹)
          (volume.restrict (simplexSet m)) := fun k =>
        (hVm.pow_const k).inv.aestronglyMeasurable
      refine Finset.aestronglyMeasurable_fun_sum _ fun t _ => ?_
      simp only [majIncX]
      exact (((((hI t).1.aestronglyMeasurable.const_mul 1).mul (hw _)).add
        (((hI t).2.1.aestronglyMeasurable.const_mul _).mul (hw _))).add
        (((hI t).2.2.aestronglyMeasurable.const_mul _).mul (hw _))).const_mul _
  have hpt2 : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ∀ σ : ℝ, 1 ≤ σ →
      ‖f σ x‖ ≤ A a b σ x ∧ (1 ≤ s' → s' ≤ σ → σ ≤ 2 * s' →
        ‖f σ x - f s' x‖ ≤ m * ((σ - s') / s') * A a b s' x) := by
    filter_upwards [hpt] with x ⟨hxS, hPD, hx⟩ σ hσ
    obtain ⟨hW0, -⟩ := hx a b ha hab hb2
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    have hB0 : 0 ≤ remainder α (simplexPoint x) cs :=
      remainder_nonneg α hz.1 hPD.det_pos.ne' cs
    have hσ0 : 0 < σ := by linarith
    have hVσ : 0 < ∑ i, simplexPoint x i * Ms a b i ^ 2 +
        σ * remainder α (simplexPoint x) cs := by
      have := mul_nonneg hσ0.le hB0; linarith
    refine ⟨?_, fun hs'1 hσs hσ2 => ?_⟩
    · rw [hfX σ hσ0, hVe σ hσ0.le]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ =>
        majIncX_norm_le m t _ _ _ hVσ hσ)
    · have hs'0 : 0 < s' := by linarith
      rw [hfX σ hσ0, hfX s' hs'0, hVe σ hσ0.le, hVe s' hs'0.le, ← Finset.sum_sub_distrib]
      simp only [hA_def, Finset.mul_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ =>
        majIncX_sub_le hm6 (by omega) _ _ _ hW0 hB0 hs'1 hσs hσ2)
  have hg : ∀ σ : ℝ, IntegrableOn (fun x => σ * (Gs x + Hs x * b⁻¹)) (simplexSet m) :=
    fun σ => (hGsi.add (hHsi.mul_const b⁻¹)).const_mul σ
  have hint : ∀ σ : ℝ, 1 ≤ σ → IntegrableOn (f σ) (simplexSet m) := fun σ hσ =>
    (hg σ).mono' (hmeas σ (by linarith)) (by
      filter_upwards [hpt2, hAg] with x h1 h2
      exact (h1 σ hσ).1.trans (h2 σ hσ a b ha hab hb2))
  -- the increment
  have hs0 : 0 ≤ s := by linarith
  have hs'0 : 0 ≤ s' := by linarith
  have hε : 0 ≤ (m : ℝ) * ((s - s') / s') := by
    have : 0 ≤ (s - s') / s' := div_nonneg (by linarith) hs'0
    positivity
  rw [pvOf_eq (hRe s hs), pvOf_eq (hRe s' hs'), hmom s hs0, hmom s' hs'0, ← mul_sub,
    ← integral_sub (hint s hs) (hint s' hs'), norm_mul, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have hbd : ‖∫ x in simplexSet m, (f s x - f s' x)‖ ≤
      ∫ x in simplexSet m, m * ((s - s') / s') * (s' * (Gs x + Hs x * b⁻¹)) := by
    refine norm_integral_le_of_norm_le ((hg s').const_mul _) ?_
    filter_upwards [hpt2, hAg] with x h1 h2
    exact ((h1 s hs).2 hs' hss hs2).trans
      (mul_le_mul_of_nonneg_left (h2 s' hs' a b ha hab hb2) hε)
  have hgi : ∫ x in simplexSet m, m * ((s - s') / s') * (s' * (Gs x + Hs x * b⁻¹)) =
      m * (s - s') * ((∫ x in simplexSet m, Gs x) + (∫ x in simplexSet m, Hs x) / b) := by
    rw [integral_const_mul, integral_const_mul, integral_add hGsi (hHsi.mul_const b⁻¹),
      integral_mul_const]
    have : s' ≠ 0 := by positivity
    field_simp
  rw [hgi] at hbd
  calc π ^ 4 * ‖∫ x in simplexSet m, (f s x - f s' x)‖
      ≤ π ^ 4 * (m * (s - s') * ((∫ x in simplexSet m, Gs x) +
          (∫ x in simplexSet m, Hs x) / b)) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = _ := by ring

end QED.GradedProof.RPi4

end
