/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Form
public import QED.Algebra.SandwichReduction
public import QED.Algebra.ChargeConjugation

/-!
# Reflection-covariant matrix functions have the form `a(p²) p̸ + b(p²)`

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2, step L3. Let `W` be a `4 × 4`-matrix-valued function of a
four-vector on the region `p² > -T²`, covariant under every reflection `R_a` (`a² ≠ 0`) with its
spinor representative `S_a = a̸ Γ` (`QED.Dirac.reflSpin`):
`S_a W(R_a p) S_a⁻¹ = W(p)` (`SECov`). If moreover `W(t n₀) → W(0)` as `t → 0⁺` along the null
vector `n₀ = (1, 1, 0, 0)`, then `W(p) = a(p²) p̸ + b(p²)` on the region for some functions
`a, b` (`exists_seMat_of_cov`).

## Proof

* **Canonical vectors.** For `s < 0`, `s > 0`, `s = 0` let `c_s = (√-s, 0, 0, 0)`,
  `(0, √s, 0, 0)`, `n₀`. The reflections in `e₂`, `e₃` and in a third vector orthogonal to
  `c_s` (`e₁`, `e₀`, `(1, 1, 1, 0)`) fix `c_s`, so `W(c_s)` commutes with their spinor
  representatives; the commutant of `γ²Γ, γ³Γ` is spanned by `1, γ⁰, γ¹, γ⁰γ¹`
  (`QED.Dirac.eq_of_commute_gamma_two_three`), and the third commutation leaves `1, c̸_s`.
* **Transport.** `W(R_a q) = S_a W(q) S_a⁻¹`, and `S_a q̸ S_a⁻¹ = (R_a q)̸`, so the form passes
  from `q` to `R_a q` with the same coefficients (`seMat_reflect`). For `c² = p² ≠ 0` one or two
  reflections carry `c` to `p` (`R_{c-p} c = p` if `(c - p)² ≠ 0`, else `R_p R_{c+p} c = p`); for
  a nonzero null `p`, the same from `n₀` or from `R_{e₁} n₀ = (1, -1, 0, 0)`.
* **The origin.** `W(t n₀) = a₀ + b₀ t n̸₀ → a₀` as `t → 0⁺`, so `W(0) = a₀ = a(0)·0̸ + b(0)`.
-/

@[expose] public section

open Complex Filter Topology
open QED.Dirac

local notation "Γ" => Matrix.diagonal ![(-1 : ℂ), -1, 1, 1]

namespace QED.GradedProof.SE2

/-- **Covariance under reflections** on the region `p² > -T²`. -/
def SECov (T : ℝ) (W : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ a : Fin 4 → ℝ, Minkowski.dot a a ≠ 0 → ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p →
    reflSpin a * W (reflect a p) * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) = W p

variable {T : ℝ} {W : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}

/-! ### Transport along reflections -/

theorem seMat_reflect (hcov : SECov T W) {a q : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0)
    (hq : -T ^ 2 < Minkowski.dot q q) {x y : ℂ} (hW : W q = seMat x y q) :
    W (reflect a q) = seMat x y (reflect a q) := by
  have h := hcov a ha (reflect a q) (by rw [dot_reflect ha]; exact hq)
  rw [reflect_reflect ha, hW] at h
  rw [← h]
  have e1 := reflSpin_mul_slash_mul_inv ha q
  have e2 := reflSpin_mul_inv ha
  generalize (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) = S' at e1 e2 ⊢
  simp only [seMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, e1, e2]

theorem commute_of_cov (hcov : SECov T W) {a c : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0)
    (hac : Minkowski.dot a c = 0) (hc : -T ^ 2 < Minkowski.dot c c) :
    reflSpin a * W c = W c * reflSpin a := by
  have h := hcov a ha c hc
  rw [reflect_of_dot_eq_zero hac] at h
  calc reflSpin a * W c
      = reflSpin a * W c * ((((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) * reflSpin a) := by
        rw [inv_mul_reflSpin ha, Matrix.mul_one]
    _ = W c * reflSpin a := by rw [← Matrix.mul_assoc, h]

/-! ### Reflections between vectors of equal square -/

theorem reflect_sub_self {c p : Fin 4 → ℝ} (hs : Minkowski.dot c c = Minkowski.dot p p)
    (h : Minkowski.dot (c - p) (c - p) ≠ 0) : reflect (c - p) c = p := by
  have hk : 2 * Minkowski.dot (c - p) c / Minkowski.dot (c - p) (c - p) = 1 := by
    rw [div_eq_one_iff_eq h]
    simp only [Minkowski.dot_eq, Pi.sub_apply] at hs h ⊢
    linarith
  unfold reflect
  rw [hk, one_smul, sub_sub_cancel]

theorem reflect_add_self {c p : Fin 4 → ℝ} (hs : Minkowski.dot c c = Minkowski.dot p p)
    (hs0 : Minkowski.dot c c ≠ 0) (h : Minkowski.dot (c - p) (c - p) = 0) :
    reflect (c + p) c = -p := by
  have hcp : Minkowski.dot (c + p) (c + p) = 4 * Minkowski.dot c c := by
    simp only [Minkowski.dot_eq, Pi.sub_apply, Pi.add_apply] at hs h ⊢
    linarith
  have hk : 2 * Minkowski.dot (c + p) c / Minkowski.dot (c + p) (c + p) = 1 := by
    rw [hcp, div_eq_one_iff_eq (by positivity)]
    simp only [Minkowski.dot_eq, Pi.sub_apply, Pi.add_apply] at hs h ⊢
    linarith
  unfold reflect
  rw [hk, one_smul]
  abel

theorem reflect_self_neg {p : Fin 4 → ℝ} (hp : Minkowski.dot p p ≠ 0) : reflect p (-p) = p := by
  unfold reflect
  have : 2 * Minkowski.dot p (-p) / Minkowski.dot p p = -2 := by
    have e : Minkowski.dot p (-p) = -Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.neg_apply]
      ring
    rw [e, mul_neg, neg_div, mul_div_assoc, div_self hp, mul_one]
  rw [this]
  funext μ
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem dot_neg_neg (p : Fin 4 → ℝ) : Minkowski.dot (-p) (-p) = Minkowski.dot p p := by
  simp only [Minkowski.dot_eq, Pi.neg_apply]
  ring

/-- **Transport between vectors of equal nonzero square.** -/
theorem seMat_of_dot_eq (hcov : SECov T W) {c p : Fin 4 → ℝ}
    (hs : Minkowski.dot c c = Minkowski.dot p p) (hs0 : Minkowski.dot c c ≠ 0)
    (hc : -T ^ 2 < Minkowski.dot c c) {x y : ℂ} (hW : W c = seMat x y c) :
    W p = seMat x y p := by
  by_cases h : Minkowski.dot (c - p) (c - p) = 0
  · have hcp : Minkowski.dot (c + p) (c + p) ≠ 0 := by
      have : Minkowski.dot (c + p) (c + p) = 4 * Minkowski.dot c c := by
        simp only [Minkowski.dot_eq, Pi.sub_apply, Pi.add_apply] at hs h ⊢
        linarith
      rw [this]
      exact mul_ne_zero (by norm_num) hs0
    have h1 := seMat_reflect hcov hcp hc hW
    rw [reflect_add_self hs hs0 h] at h1
    have h2 := seMat_reflect hcov (hs ▸ hs0) (by rw [dot_neg_neg, ← hs]; exact hc) h1
    rwa [reflect_self_neg (hs ▸ hs0)] at h2
  · have h1 := seMat_reflect hcov h hc hW
    rwa [reflect_sub_self hs h] at h1

/-! ### The canonical vectors -/

/-- The null vector `n₀ = (1, 1, 0, 0)`. -/
def nullVec : Fin 4 → ℝ := ![1, 1, 0, 0]

theorem dot_nullVec : Minkowski.dot nullVec nullVec = 0 := by
  simp [Minkowski.dot_eq, nullVec]

theorem slash_e₀ : slash ![1, 0, 0, 0] = -gamma 0 := by
  simp [slash, Minkowski.lower_eq, Fin.sum_univ_four]

theorem slash_e₁ : slash ![0, 1, 0, 0] = gamma 1 := by
  simp [slash, Minkowski.lower_eq, Fin.sum_univ_four]

theorem slash_e₁₁₁ : slash ![1, 1, 1, 0] = -gamma 0 + gamma 1 + gamma 2 := by
  simp [slash, Minkowski.lower_eq, Fin.sum_univ_four]

/-- The commutant of `γ²Γ` and `γ³Γ`, from the covariance at a vector of the `(t, x)` plane. -/
theorem eq_basis_of_cov (hcov : SECov T W) {c : Fin 4 → ℝ} (h2 : c 2 = 0) (h3 : c 3 = 0)
    (hc : -T ^ 2 < Minkowski.dot c c) :
    W c = W c 3 3 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + W c 3 1 • gamma 0 + (-W c 3 0) • gamma 1 +
      W c 3 2 • (gamma 0 * gamma 1) := by
  have k2 := commute_of_cov hcov (a := ![0, 0, 1, 0]) (by simp [Minkowski.dot_eq])
    (by simp [Minkowski.dot_eq, h2]) hc
  have k3 := commute_of_cov hcov (a := ![0, 0, 0, 1]) (by simp [Minkowski.dot_eq])
    (by simp [Minkowski.dot_eq, h3]) hc
  rw [reflSpin, slash_e₂] at k2
  rw [reflSpin, slash_e₃] at k3
  exact eq_of_commute_gamma_two_three _ k2 k3

/-- The two entries of a commutation relation that the three canonical cases need. -/
theorem entries_of_commute {A Y : Matrix (Fin 4) (Fin 4) ℂ} (h : A * Y = Y * A) :
    (A * Y - Y * A) 0 0 = 0 ∧ (A * Y - Y * A) 0 2 = 0 := by
  rw [h, sub_self]
  exact ⟨rfl, rfl⟩

theorem gamma_one_mul_chirality :
    gamma 1 * Γ = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [gamma]

theorem gamma_zero_mul_chirality :
    gamma 0 * Γ = !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0] := by
  ext i j
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [gamma]

theorem slash_e₁₁₁_mul_chirality :
    (-gamma 0 + gamma 1 + gamma 2) * Γ =
      !![0, 0, -1, 1 - I; 0, 0, 1 + I, -1; 1, 1 - I, 0, 0; 1 + I, 1, 0, 0] := by
  ext i j
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [gamma] <;> ring

theorem basis_entries {Y : Matrix (Fin 4) (Fin 4) ℂ}
    (hY : Y = Y 3 3 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Y 3 1 • gamma 0 + (-Y 3 0) • gamma 1 +
      Y 3 2 • (gamma 0 * gamma 1)) :
    Y 0 0 = Y 3 3 ∧ Y 0 1 = -Y 3 2 ∧ Y 0 2 = Y 3 1 ∧ Y 0 3 = -Y 3 0 ∧ Y 2 0 = Y 3 1 ∧
      Y 2 2 = Y 3 3 ∧ Y 2 3 = Y 3 2 := by
  have e := fun i j => congrFun (congrFun hY i) j
  have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2; have e03 := e 0 3
  have e20 := e 2 0; have e22 := e 2 2; have e23 := e 2 3
  simp [gamma] at e00 e01 e02 e03 e20 e22 e23
  exact ⟨e00, e01, e02, e03, e20, e22, e23⟩

theorem exists_seMat_rest (hcov : SECov T W) {x : ℝ} (hx : x ≠ 0)
    (hc : -T ^ 2 < Minkowski.dot ![x, 0, 0, 0] ![x, 0, 0, 0]) :
    ∃ a b : ℂ, W ![x, 0, 0, 0] = seMat a b ![x, 0, 0, 0] := by
  have hY := eq_basis_of_cov hcov (c := ![x, 0, 0, 0]) rfl rfl hc
  have k := commute_of_cov hcov (a := ![0, 1, 0, 0]) (by simp [Minkowski.dot_eq])
    (by simp [Minkowski.dot_eq]) hc
  rw [reflSpin, slash_e₁, gamma_one_mul_chirality] at k
  set Y := W ![x, 0, 0, 0]
  obtain ⟨b00, b01, b02, b03, b20, b22, -⟩ := basis_entries hY
  have k00 := congrFun (congrFun k 0) 0
  have k02 := congrFun (congrFun k 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four] at k00 k02
  have h30 : Y 3 0 = 0 := by linear_combination k00 / 2 + b03 / 2
  have h32 : Y 3 2 = 0 := by linear_combination k02 / 2 + b01 / 2
  refine ⟨-Y 3 1 / x, Y 3 3, ?_⟩
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  conv_lhs => rw [hY]
  rw [h30, h32]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [seMat, slash, Minkowski.lower_eq, Fin.sum_univ_four, gamma] <;>
    field_simp

theorem exists_seMat_space (hcov : SECov T W) {x : ℝ} (hx : x ≠ 0)
    (hc : -T ^ 2 < Minkowski.dot ![0, x, 0, 0] ![0, x, 0, 0]) :
    ∃ a b : ℂ, W ![0, x, 0, 0] = seMat a b ![0, x, 0, 0] := by
  have hY := eq_basis_of_cov hcov (c := ![0, x, 0, 0]) rfl rfl hc
  have k := commute_of_cov hcov (a := ![1, 0, 0, 0]) (by simp [Minkowski.dot_eq])
    (by simp [Minkowski.dot_eq]) hc
  rw [reflSpin, slash_e₀, Matrix.neg_mul, gamma_zero_mul_chirality] at k
  set Y := W ![0, x, 0, 0]
  obtain ⟨b00, b01, b02, b03, b20, b22, b23⟩ := basis_entries hY
  have k00 := congrFun (congrFun k 0) 0
  have k03 := congrFun (congrFun k 0) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at k00 k03
  have h31 : Y 3 1 = 0 := by linear_combination -(k00 + b20 + b02) / 2
  have h32 : Y 3 2 = 0 := by linear_combination (k03 + b01 - b23) / 2
  refine ⟨-Y 3 0 / x, Y 3 3, ?_⟩
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  conv_lhs => rw [hY]
  rw [h31, h32]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [seMat, slash, Minkowski.lower_eq, Fin.sum_univ_four, gamma] <;>
    field_simp

theorem exists_seMat_null (hcov : SECov T W) (hc : -T ^ 2 < Minkowski.dot nullVec nullVec) :
    ∃ a b : ℂ, W nullVec = seMat a b nullVec := by
  have hY := eq_basis_of_cov hcov (c := nullVec) rfl rfl hc
  have k := commute_of_cov hcov (a := ![1, 1, 1, 0]) (by simp [Minkowski.dot_eq])
    (by simp [Minkowski.dot_eq, nullVec]) hc
  rw [reflSpin, slash_e₁₁₁, slash_e₁₁₁_mul_chirality] at k
  set Y := W nullVec
  obtain ⟨b00, b01, b02, b03, b20, b22, b23⟩ := basis_entries hY
  have k00 := congrFun (congrFun k 0) 0
  have k02 := congrFun (congrFun k 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four] at k00 k02
  have h30 : Y 3 0 = Y 3 1 := by linear_combination (k00 + b20 + b02 + (1 + I) * b03) / 2
  have h32 : Y 3 2 = 0 := by linear_combination (k02 + b22 - b00 + (1 + I) * b01) / 2
  refine ⟨-Y 3 1, Y 3 3, ?_⟩
  conv_lhs => rw [hY]
  rw [h30, h32]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [seMat, slash, Minkowski.lower_eq, Fin.sum_univ_four, gamma, nullVec]

/-! ### The theorem -/

/-- The canonical vector of square `s`. -/
noncomputable def canonVec (s : ℝ) : Fin 4 → ℝ :=
  if s < 0 then ![Real.sqrt (-s), 0, 0, 0] else if 0 < s then ![0, Real.sqrt s, 0, 0]
  else nullVec

theorem dot_canonVec (s : ℝ) : Minkowski.dot (canonVec s) (canonVec s) = s := by
  unfold canonVec
  split_ifs with h1 h2
  · simp only [Minkowski.dot_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [Real.mul_self_sqrt (by linarith)]
    ring
  · simp only [Minkowski.dot_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [Real.mul_self_sqrt h2.le]
    ring
  · rw [dot_nullVec]
    linarith [not_lt.mp h1, not_lt.mp h2]

theorem exists_seMat_canonVec (hcov : SECov T W) {s : ℝ} (hs : -T ^ 2 < s) :
    ∃ a b : ℂ, W (canonVec s) = seMat a b (canonVec s) := by
  have hc : -T ^ 2 < Minkowski.dot (canonVec s) (canonVec s) := by rwa [dot_canonVec]
  unfold canonVec at hc ⊢
  split_ifs at hc ⊢ with h1 h2
  · exact exists_seMat_rest hcov (Real.sqrt_ne_zero'.mpr (by linarith)) hc
  · exact exists_seMat_space hcov (Real.sqrt_ne_zero'.mpr h2) hc
  · exact exists_seMat_null hcov hc

/-- **Transport from `n₀` to a nonzero null vector.** -/
theorem seMat_of_null (hcov : SECov T W) (hT : -T ^ 2 < 0) {p : Fin 4 → ℝ} (hp0 : p ≠ 0)
    (hpp : Minkowski.dot p p = 0) {x y : ℂ} (hW : W nullVec = seMat x y nullVec) :
    W p = seMat x y p := by
  have hn : -T ^ 2 < Minkowski.dot nullVec nullVec := by rwa [dot_nullVec]
  have hs : Minkowski.dot nullVec nullVec = Minkowski.dot p p := by rw [dot_nullVec, hpp]
  by_cases h : Minkowski.dot (nullVec - p) (nullVec - p) = 0
  · -- `p` is a multiple of `n₀`; start from `R_{e₁} n₀ = (1, -1, 0, 0)`
    have he : Minkowski.dot (![0, 1, 0, 0] : Fin 4 → ℝ) ![0, 1, 0, 0] ≠ 0 := by
      simp [Minkowski.dot_eq]
    have h1 := seMat_reflect hcov he hn hW
    have hc' : reflect ![0, 1, 0, 0] nullVec = ![1, -1, 0, 0] := by
      funext μ
      fin_cases μ <;> norm_num [reflect, Minkowski.dot_eq, nullVec]
    rw [hc'] at h1
    have hc'' : -T ^ 2 < Minkowski.dot (![1, -1, 0, 0] : Fin 4 → ℝ) ![1, -1, 0, 0] := by
      simpa [Minkowski.dot_eq] using hT
    have hs' : Minkowski.dot (![1, -1, 0, 0] : Fin 4 → ℝ) ![1, -1, 0, 0] =
        Minkowski.dot p p := by
      rw [hpp]
      simp [Minkowski.dot_eq]
    have hne : Minkowski.dot ((![1, -1, 0, 0] : Fin 4 → ℝ) - p) (![1, -1, 0, 0] - p) ≠ 0 := by
      simp only [Minkowski.dot_eq, Pi.sub_apply, nullVec, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons] at h hpp ⊢
      intro h'
      have e01 : p 1 = p 0 := by nlinarith
      have e0 : p 0 = 0 := by nlinarith
      have e23 : p 2 ^ 2 + p 3 ^ 2 = 0 := by nlinarith
      have e2 : p 2 = 0 := by nlinarith [sq_nonneg (p 2), sq_nonneg (p 3)]
      have e3 : p 3 = 0 := by nlinarith [sq_nonneg (p 2), sq_nonneg (p 3)]
      apply hp0
      funext μ
      fin_cases μ <;> simp [e0, e01, e2, e3]
    have h2 := seMat_reflect hcov hne hc'' h1
    rwa [reflect_sub_self hs' hne] at h2
  · have h1 := seMat_reflect hcov h hn hW
    rwa [reflect_sub_self hs h] at h1

theorem seMat_apply (a b : ℂ) (p : Fin 4 → ℝ) (α β : Fin 4) :
    seMat a b p α β = a * slash p α β + b * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β := by
  simp [seMat]

/-- **Reflection-covariant functions with a limit at the origin along `n₀` have the form
`a(p²) p̸ + b(p²)`.** -/
theorem exists_seMat_of_cov (hcov : SECov T W)
    (hcont : ∀ α β : Fin 4, Tendsto (fun t : ℝ => W (t • nullVec) α β) (𝓝[>] 0)
      (𝓝 (W 0 α β))) :
    ∃ a b : ℝ → ℂ, ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p →
      W p = seMat (a (Minkowski.dot p p)) (b (Minkowski.dot p p)) p := by
  classical
  choose! a b hab using fun s (hs : -T ^ 2 < s) => exists_seMat_canonVec hcov hs
  refine ⟨a, b, fun p hp => ?_⟩
  have hc := hab _ hp
  by_cases hs0 : Minkowski.dot p p = 0
  · have hT : -T ^ 2 < 0 := hs0 ▸ hp
    have hn : W nullVec = seMat (a 0) (b 0) nullVec := by
      have h := hab 0 hT
      rwa [show canonVec 0 = nullVec by simp [canonVec]] at h
    rw [hs0]
    by_cases hp0 : p = 0
    · subst hp0
      ext α β
      have hlim : Tendsto (fun t : ℝ => seMat (a 0) (b 0) (t • nullVec) α β) (𝓝[>] 0)
          (𝓝 (seMat (a 0) (b 0) 0 α β)) := by
        simp only [seMat_apply, slash_smul]
        refine Tendsto.add (Tendsto.const_mul _ ?_) tendsto_const_nhds
        have : Tendsto (fun t : ℝ => ((t : ℂ) • slash nullVec) α β) (𝓝[>] 0)
            (𝓝 ((((0 : ℝ) : ℂ) • slash nullVec) α β)) := by
          simp only [Matrix.smul_apply, smul_eq_mul]
          exact ((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds).mul_const _
        simpa [slash, Minkowski.lower] using this
      refine tendsto_nhds_unique (hcont α β) (hlim.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      refine (congrFun (congrFun (seMat_of_null hcov hT ?_ ?_ hn) α) β).symm
      · intro h0
        have := congrFun h0 0
        simp [nullVec] at this
        linarith
      · simp [Minkowski.dot_eq, nullVec]
    · exact seMat_of_null hcov hT hp0 hs0 hn
  · exact seMat_of_dot_eq hcov (dot_canonVec _) (by rw [dot_canonVec]; exact hs0)
      (by rw [dot_canonVec]; exact hp) hc

/-- **A family converging to a reflection-covariant limit has the covariant form.** -/
theorem hasSEForm_of_cov {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hlim : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε => G ε p α β) (𝓝[>] 0) (𝓝 (W p α β)))
    (hcov : SECov T W)
    (hcont : ∀ α β : Fin 4, Tendsto (fun t : ℝ => W (t • nullVec) α β) (𝓝[>] 0)
      (𝓝 (W 0 α β))) :
    HasSEForm T G := by
  obtain ⟨a, b, hab⟩ := exists_seMat_of_cov hcov hcont
  exact ⟨a, b, fun p hp α β => by rw [← hab p hp]; exact hlim p hp α β⟩

end QED.GradedProof.SE2

end
