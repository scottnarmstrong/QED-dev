/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKFactor
public import QED.GradedProof.SE2FormLemma
public import QED.Algebra.FormFactorProjector

/-!
# Set (c): the self-energy-type doubly pinched values have no Pauli part

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSumGe` (`QED/ChainProof/SetCRegKKGe.lean`).
By `QED/ChainProof/SetCRegKKFactor.lean`, `Q(4, 1, 3)^μ = γ^μ X(p)` and
`Q(9, 2, 0)^μ = Y(p') γ^μ`. The pointwise limits are covariant under spinor-lifted Lorentz maps
(`QED.ChainProof.SetCMainB.pieceGood_kkT`), so:

* at the rest momentum `p₀`, the reflections in `e₁`, `e₂`, `e₃` fix `p₀` and `X(p₀)`,
  `Y(p₀)` commute with their spinor representatives; the commutant is spanned by `1`, `γ⁰`
  (`eq_of_commute_refl`), and `γ⁰ A(p₀) = A(p₀) γ⁰ = A(p₀)`, `A(k) = m - k̸`;
* the reflection in `p₀ - p'` exchanges `p₀` and `p'`, and carries `Y(p')` to `Y(p₀)`.

Hence `X(p₀) A(p₀) = c A(p₀)` and `A(p') Y(p') = c' A(p')`, and the Pauli weights, which contract
`V` as `tr(A(p') V A(p) Γ)`, see only `c γ^μ` and `c' γ^μ`, whose Pauli numerator vanishes. So
along the curve the Pauli-weighted sum of the three survivors is that of `Q(5, 1, 0)` alone.

* `pauliSum_gamma`: `γ^μ` has zero Pauli numerator;
* `pauliSum_mul_left`, `pauliSum_mul_right`: on-shell scalar factors at the ends;
* `eq_of_commute_refl`, `mul_rest_of_commute`: the rest-frame commutant;
* `eq_of_cov_gamma_mul`, `eq_of_cov_mul_gamma`: cancelling `γ^μ` in a covariance relation;
* `pieceGood_kkQ`: a doubly pinched value is a covariant piece;
* **`kkQX_rest`**, **`kkQY_rest`**, **`kkQY_curve`**: the scalar forms;
* **`kkPW_kkQ_four`**, **`kkPW_kkQ_nine`**: zero Pauli-weighted sums along the curve;
* **`tendsto_kkQ_five`**: `kkSumP` is the Pauli limit of `kCst · Q(5, 1, 0)` for `T ≥ 4`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Matrix
open QED.WickModel (Params)
open QED.Dirac (gamma slash reflSpin reflect reflectMatrix vecAct vecAct_smul)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.Bridge (electronNumerator)
open QED.GradedProof.SE2Real (sharp sharp_smul)

/-! ### The Pauli weights -/

/-- **`γ^μ` has zero Pauli numerator** for on-shell momenta with `q² > 0`. -/
theorem pauliSum_gamma {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    ∑ j : Idx, pauliWt m p' p j.1 j.2.1 j.2.2 * gamma j.1 j.2.1 j.2.2 = 0 := by
  have h := (QED.OneLoop.formFactorProj_eq_of_sandwich (e := 1) one_ne_zero hm hp' hp hq
    (V := fun μ => gamma μ) (a := 1) (b := 0) (c := 0) (d := 0)
    (fun μ u w _ _ => by simp)).2.1
  rw [formFactorProj₂_eq_pauliNum, pauliNum_eq_sum_idx] at h
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hq' : (Minkowski.dot (p' - p) (p' - p) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hD : 4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 4 * m ^ 2 + Minkowski.dot (p' - p) (p' - p) := by positivity
    exact_mod_cast this.ne'
  simp only [mul_zero, sub_zero, zero_div, div_eq_zero_iff, mul_eq_zero, hm', false_or,
    Complex.ofReal_one, one_mul, hq', pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, hD, or_false] at h
  exact h

theorem pauliSum_mul_left {m : ℝ} {p' p : Fin 4 → ℝ} (μ : Fin 4) {Y V : Matrix (Fin 4) (Fin 4) ℂ}
    {c : ℂ} (hY : electronNumerator m p' * Y = c • electronNumerator m p') :
    ∑ a, ∑ b, pauliWt m p' p μ a b * (Y * V) a b =
      c * ∑ a, ∑ b, pauliWt m p' p μ a b * V a b := by
  have e : ∀ Z : Matrix (Fin 4) (Fin 4) ℂ,
      electronNumerator m p' * Y * Z = c • (electronNumerator m p' * Z) := fun Z => by
    rw [hY, Matrix.smul_mul]
  rw [pauliWt_sum_eq, pauliWt_sum_eq]
  simp only [← Matrix.mul_assoc, e, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem pauliSum_mul_right {m : ℝ} {p' p : Fin 4 → ℝ} (μ : Fin 4) {X V : Matrix (Fin 4) (Fin 4) ℂ}
    {c : ℂ} (hX : X * electronNumerator m p = c • electronNumerator m p) :
    ∑ a, ∑ b, pauliWt m p' p μ a b * (V * X) a b =
      c * ∑ a, ∑ b, pauliWt m p' p μ a b * V a b := by
  have e : ∀ Z : Matrix (Fin 4) (Fin 4) ℂ,
      Z * X * electronNumerator m p = c • (Z * electronNumerator m p) := fun Z => by
    rw [Matrix.mul_assoc, hX, Matrix.mul_smul]
  rw [pauliWt_sum_eq, pauliWt_sum_eq]
  simp only [← Matrix.mul_assoc, e, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ring

/-! ### The rest-frame commutant -/

/-- **The commutant of the three spatial reflections** is spanned by `1` and `γ⁰`. -/
theorem eq_of_commute_refl {W : Matrix (Fin 4) (Fin 4) ℂ}
    (h1 : reflSpin ![0, 1, 0, 0] * W = W * reflSpin ![0, 1, 0, 0])
    (h2 : reflSpin ![0, 0, 1, 0] * W = W * reflSpin ![0, 0, 1, 0])
    (h3 : reflSpin ![0, 0, 0, 1] * W = W * reflSpin ![0, 0, 0, 1]) :
    W = W 3 3 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + W 3 1 • gamma 0 := by
  rw [reflSpin, QED.Dirac.slash_e₂] at h2
  rw [reflSpin, QED.Dirac.slash_e₃] at h3
  have hY := QED.Dirac.eq_of_commute_gamma_two_three W h2 h3
  rw [reflSpin, QED.GradedProof.SE2.slash_e₁, QED.GradedProof.SE2.gamma_one_mul_chirality] at h1
  obtain ⟨-, b01, -, b03, -, -, -⟩ := QED.GradedProof.SE2.basis_entries hY
  have k00 := congrFun (congrFun h1 0) 0
  have k02 := congrFun (congrFun h1 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four] at k00 k02
  have h30 : W 3 0 = 0 := by linear_combination k00 / 2 + b03 / 2
  have h32 : W 3 2 = 0 := by linear_combination k02 / 2 + b01 / 2
  conv_lhs => rw [hY]
  rw [h30, h32]
  simp

theorem slash_restMomentum (m : ℝ) : slash (restMomentum m) = -((m : ℂ) • gamma 0) := by
  ext a b
  simp [slash, restMomentum, Minkowski.lower_eq, Fin.sum_univ_four]

theorem gamma_zero_mul_rest (m : ℝ) :
    gamma 0 * electronNumerator m (restMomentum m) = electronNumerator m (restMomentum m) := by
  simp only [electronNumerator, slash_restMomentum, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_neg, QED.Dirac.gamma_zero_mul_gamma_zero]
  abel

theorem rest_mul_gamma_zero (m : ℝ) :
    electronNumerator m (restMomentum m) * gamma 0 = electronNumerator m (restMomentum m) := by
  simp only [electronNumerator, slash_restMomentum, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.neg_mul, QED.Dirac.gamma_zero_mul_gamma_zero]
  abel

/-- A matrix commuting with the three spatial reflections is a scalar on `A(p₀)`, from either
side. -/
theorem mul_rest_of_commute {W : Matrix (Fin 4) (Fin 4) ℂ} (m : ℝ)
    (h1 : reflSpin ![0, 1, 0, 0] * W = W * reflSpin ![0, 1, 0, 0])
    (h2 : reflSpin ![0, 0, 1, 0] * W = W * reflSpin ![0, 0, 1, 0])
    (h3 : reflSpin ![0, 0, 0, 1] * W = W * reflSpin ![0, 0, 0, 1]) :
    W * electronNumerator m (restMomentum m) =
        (W 3 3 + W 3 1) • electronNumerator m (restMomentum m) ∧
      electronNumerator m (restMomentum m) * W =
        (W 3 3 + W 3 1) • electronNumerator m (restMomentum m) := by
  have hW := eq_of_commute_refl h1 h2 h3
  constructor
  · conv_lhs => rw [hW]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, gamma_zero_mul_rest,
      add_smul]
  · conv_lhs => rw [hW]
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, rest_mul_gamma_zero,
      add_smul]

/-! ### Cancelling `γ^μ` in a covariance relation -/

section Cancel

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

theorem sq_mul_gamma_zero_mul (h : IsSpinLift L S T) : S * gamma 0 * T * (S * gamma 0 * T) = 1 := by
  rw [← h.mul_mul_mul, QED.Dirac.gamma_zero_mul_gamma_zero, Matrix.mul_one, h.mul_eq_one]

theorem eq_of_cov_gamma_mul (h : IsSpinLift L S T) {W W' : Matrix (Fin 4) (Fin 4) ℂ}
    (hc : ∀ μ, S * (gamma μ * W') * T = vecAct L (fun ν => gamma ν * W) μ) : S * W' * T = W := by
  have e := hc 0
  have hv : vecAct L (fun ν => gamma ν * W) 0 = S * gamma 0 * T * W := by
    rw [h.mul_gamma_mul]
    simp only [vecAct, Finset.sum_mul, Matrix.smul_mul]
  rw [hv, h.mul_mul_mul] at e
  calc S * W' * T = S * gamma 0 * T * (S * gamma 0 * T) * (S * W' * T) := by
        rw [sq_mul_gamma_zero_mul h, Matrix.one_mul]
    _ = W := by rw [Matrix.mul_assoc, e, ← Matrix.mul_assoc, sq_mul_gamma_zero_mul h,
        Matrix.one_mul]

theorem eq_of_cov_mul_gamma (h : IsSpinLift L S T) {W W' : Matrix (Fin 4) (Fin 4) ℂ}
    (hc : ∀ μ, S * (W' * gamma μ) * T = vecAct L (fun ν => W * gamma ν) μ) : S * W' * T = W := by
  have e := hc 0
  have hv : vecAct L (fun ν => W * gamma ν) 0 = W * (S * gamma 0 * T) := by
    rw [h.mul_gamma_mul]
    simp only [vecAct, Finset.mul_sum, Matrix.mul_smul]
  rw [hv, h.mul_mul_mul] at e
  calc S * W' * T = S * W' * T * (S * gamma 0 * T * (S * gamma 0 * T)) := by
        rw [sq_mul_gamma_zero_mul h, Matrix.mul_one]
    _ = W := by rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, sq_mul_gamma_zero_mul h,
        Matrix.mul_one]

theorem commute_of_conj (h : IsSpinLift L S T) {W : Matrix (Fin 4) (Fin 4) ℂ}
    (hW : S * W * T = W) : S * W = W * S := by
  calc S * W = S * W * (T * S) := by rw [h.mul_eq_one', Matrix.mul_one]
    _ = W * S := by rw [← Matrix.mul_assoc, hW]

end Cancel

/-! ### The reflections used -/

theorem dot_restMomentum_of_zero {K : Fin 4 → ℝ} (hK : K 0 = 0) (m : ℝ) :
    Minkowski.dot K (restMomentum m) = 0 := by
  simp [Minkowski.dot_eq, restMomentum, hK]

theorem reflect_apply_zero {K : Fin 4 → ℝ} (hK : K 0 = 0) (v : Fin 4 → ℝ) :
    reflect K v 0 = v 0 := by
  simp [reflect, hK]

theorem isPairQ_swap {m : ℝ} {p' p : Fin 4 → ℝ} (h : IsPairQ m p' p) : IsPairQ m p p' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h2, h1, h4, h3, ?_⟩
  rw [← neg_sub, dot_neg_neg']
  exact h5

theorem isPairQ_curve' {m : ℝ} (hm : 0 < m) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hu0 : u ≠ 0) :
    IsPairQ m (curveMomentum m u) (restMomentum m) := by
  refine ⟨dot_curveMomentum m hu, dot_restMomentum (m := m), curveMomentum_pos hm hu,
    restMomentum_pos hm, ?_⟩
  rw [dot_curveMomentum_sub m hu]
  have h1 := one_sub_sq_pos hu
  have h2 : 0 < u ^ 2 := lt_of_le_of_ne (sq_nonneg u) (Ne.symm (pow_ne_zero 2 hu0))
  unfold curveQ
  positivity

theorem half_mem_Ioo_neg_one : (1 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

/-- A spatial reflection fixes `p₀`, moves an admissible partner to an admissible partner, and
has a spinor lift. -/
theorem spatial_refl {K : Fin 4 → ℝ} (hK0 : K 0 = 0) (hKK : Minkowski.dot K K ≠ 0) :
    IsSpinLift (reflectMatrix K) (reflSpin K) (((Minkowski.dot K K : ℝ) : ℂ)⁻¹ • reflSpin K) ∧
      (∀ m : ℝ, reflectMatrix K *ᵥ restMomentum m = restMomentum m) ∧
      ∀ v : Fin 4 → ℝ, (reflectMatrix K *ᵥ v) 0 = v 0 := by
  refine ⟨QED.TwoLoop.ReflCovariance.isSpinLift_reflect hKK, fun m => ?_, fun v => ?_⟩
  · rw [QED.Dirac.reflectMatrix_mulVec]
    exact QED.Dirac.reflect_of_dot_eq_zero (dot_restMomentum_of_zero hK0 _)
  · rw [QED.Dirac.reflectMatrix_mulVec]
    exact reflect_apply_zero hK0 v

theorem dot_e₁ : Minkowski.dot ![(0 : ℝ), 1, 0, 0] ![0, 1, 0, 0] ≠ 0 := by
  simp [Minkowski.dot_eq]

theorem dot_e₂ : Minkowski.dot ![(0 : ℝ), 0, 1, 0] ![0, 0, 1, 0] ≠ 0 := by
  simp [Minkowski.dot_eq]

theorem dot_e₃ : Minkowski.dot ![(0 : ℝ), 0, 0, 1] ![0, 0, 0, 1] ≠ 0 := by
  simp [Minkowski.dot_eq]

theorem pauliSum_split (m : ℝ) (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ j : Idx, pauliWt m p' p j.1 j.2.1 j.2.2 * V j.1 j.2.1 j.2.2 =
      ∑ μ, ∑ a, ∑ b, pauliWt m p' p μ a b * V μ a b := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun μ _ => Fintype.sum_prod_type _

/-! ### The doubly pinched values are covariant -/

section Cov

variable {R : Params} {t x : ℝ} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
  (ht : R.m ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1)
include hm hγ hγΛ ht hx

/-- **A doubly pinched value is a covariant, `♯`-fixed piece.** -/
theorem pieceGood_kkQ {i : Fin 12} {d d' : Fin 4} (hd : d ≠ d') (hok : QOk i d d') :
    PieceGood R.m fun p' p μ => Matrix.of fun a b => kkQ i R p p' t d d' μ a b x := by
  have hK := card_erase_erase_le d d' hd
  have hdisj : Disjoint (kSet .one .one ((Finset.univ.erase d).erase d')) {8, 9} := by
    refine Finset.disjoint_left.2 fun q hq hq' => ?_
    simp only [kSet, kSlotS, Finset.union_empty, Finset.mem_image] at hq
    obtain ⟨j, -, rfl⟩ := hq
    revert hq'
    revert j
    decide
  refine pieceGood_kkT hm hγ hγΛ ht hx le_rfl hok.1 (fun p p' μ ℓ => Matrix.of fun a b =>
      kNi i R p p' .one .one ((Finset.univ.erase d).erase d') μ ℓ a b *
        elemSq (repBClass i) (repBSlot i) p p' ℓ)
    (fun p p' μ a b => (isLoopPolyMat_kNum_one_one _ _ _ _ _ _ μ hK a b).mul
      (isLoopPoly_elemSq _ _ p p'))
    (fun p p' μ a b => (refinedBoundMat_kNum_one_one _ _ _ _ _ _ μ hK a b).mul
      (refinedBound_elemSq _ _ p p') hdisj) (fun L S T h p p' μ ℓ => ?_)
    (fun p p' μ ℓ => ?_)
  · simp only [of_mul_scalar]
    rw [elemSq_map h, Matrix.mul_smul, Matrix.smul_mul, kNum_map _ _ _ _ p p' _ _ _ μ h ℓ,
      vecAct_smul]
  · simp only [of_mul_scalar]
    rw [sharp_smul, elemSq, Complex.conj_ofReal, sharp_kNum]

/-- **`X(p₀)` commutes with a spatial reflection.** -/
theorem kkQX_commute {K : Fin 4 → ℝ} (hK0 : K 0 = 0) (hKK : Minkowski.dot K K ≠ 0)
    (p' : Fin 4 → ℝ) :
    reflSpin K * kkQX R (restMomentum R.m) p' t x =
      kkQX R (restMomentum R.m) p' t x * reflSpin K := by
  obtain ⟨h, hL0, hLt⟩ := spatial_refl hK0 hKK
  replace hL0 := hL0 R.m
  have hpq := isPairQ_curve' hm half_mem_Ioo_neg_one (by norm_num)
  set p₁ := curveMomentum R.m (1 / 2)
  set p₀ := restMomentum R.m
  obtain ⟨hp₁, hp₀, hp₁0, hp₀0, hq⟩ := hpq
  have hG := (pieceGood_kkQ hm hγ hγΛ ht hx (i := 4) (by decide : (1 : Fin 4) ≠ 3)
    (by decide +kernel)).1 _ _ _ h p₁ p₀ ⟨hp₁, hp₀, hp₁0, hp₀0, hq⟩ (by rw [hLt]; exact hp₁0)
    (by rw [hLt]; exact hp₀0)
  have hLp₁ : Minkowski.dot (reflectMatrix K *ᵥ p₁) (reflectMatrix K *ᵥ p₁) = -R.m ^ 2 := by
    rw [h.dot_mulVec, hp₁]
  have hLq : 0 ≤ Minkowski.dot (reflectMatrix K *ᵥ p₁ - p₀) (reflectMatrix K *ᵥ p₁ - p₀) := by
    rw [show reflectMatrix K *ᵥ p₁ - p₀ = reflectMatrix K *ᵥ (p₁ - p₀) by
      rw [Matrix.mulVec_sub, hL0], h.dot_mulVec]
    exact hq.le
  have hc : ∀ μ, reflSpin K * (gamma μ * kkQX R p₀ (reflectMatrix K *ᵥ p₁) t x) *
      (((Minkowski.dot K K : ℝ) : ℂ)⁻¹ • reflSpin K) =
        vecAct (reflectMatrix K) (fun ν => gamma ν * kkQX R p₀ p₁ t x) μ := fun μ => by
    have e := hG μ
    beta_reduce at e
    rw [hL0] at e
    have e₁ : (Matrix.of fun a b => kkQ 4 R p₀ (reflectMatrix K *ᵥ p₁) t 1 3 μ a b x) =
        gamma μ * kkQX R p₀ (reflectMatrix K *ᵥ p₁) t x := by
      ext a b
      exact kkQ_four_eq hm hγ hγΛ hp₀ hLp₁ hLq ht hx μ a b
    have e₂ : (fun ν => Matrix.of fun a b => kkQ 4 R p₀ p₁ t 1 3 ν a b x) =
        fun ν => gamma ν * kkQX R p₀ p₁ t x := funext fun ν => by
      ext a b
      exact kkQ_four_eq hm hγ hγΛ hp₀ hp₁ hq.le ht hx ν a b
    rw [e₁, e₂] at e
    exact e
  have hX := eq_of_cov_gamma_mul h hc
  rw [kkQX_indep R p₀ (reflectMatrix K *ᵥ p₁) p₁] at hX
  rw [kkQX_indep R p₀ p' p₁]
  exact commute_of_conj h hX

/-- **`Y(p₀)` commutes with a spatial reflection.** -/
theorem kkQY_commute {K : Fin 4 → ℝ} (hK0 : K 0 = 0) (hKK : Minkowski.dot K K ≠ 0)
    (p : Fin 4 → ℝ) :
    reflSpin K * kkQY R p (restMomentum R.m) t x =
      kkQY R p (restMomentum R.m) t x * reflSpin K := by
  obtain ⟨h, hL0, hLt⟩ := spatial_refl hK0 hKK
  replace hL0 := hL0 R.m
  have hpq := isPairQ_swap (isPairQ_curve' hm half_mem_Ioo_neg_one (by norm_num))
  set p₁ := curveMomentum R.m (1 / 2)
  set p₀ := restMomentum R.m
  obtain ⟨hp₀, hp₁, hp₀0, hp₁0, hq⟩ := hpq
  have hG := (pieceGood_kkQ hm hγ hγΛ ht hx (i := 9) (by decide : (2 : Fin 4) ≠ 0)
    (by decide +kernel)).1 _ _ _ h p₀ p₁ ⟨hp₀, hp₁, hp₀0, hp₁0, hq⟩ (by rw [hLt]; exact hp₀0)
    (by rw [hLt]; exact hp₁0)
  have hLp₁ : Minkowski.dot (reflectMatrix K *ᵥ p₁) (reflectMatrix K *ᵥ p₁) = -R.m ^ 2 := by
    rw [h.dot_mulVec, hp₁]
  have hLq : 0 ≤ Minkowski.dot (p₀ - reflectMatrix K *ᵥ p₁) (p₀ - reflectMatrix K *ᵥ p₁) := by
    rw [show p₀ - reflectMatrix K *ᵥ p₁ = reflectMatrix K *ᵥ (p₀ - p₁) by
      rw [Matrix.mulVec_sub, hL0], h.dot_mulVec]
    exact hq.le
  have hc : ∀ μ, reflSpin K * (kkQY R (reflectMatrix K *ᵥ p₁) p₀ t x * gamma μ) *
      (((Minkowski.dot K K : ℝ) : ℂ)⁻¹ • reflSpin K) =
        vecAct (reflectMatrix K) (fun ν => kkQY R p₁ p₀ t x * gamma ν) μ := fun μ => by
    have e := hG μ
    beta_reduce at e
    rw [hL0] at e
    have e₁ : (Matrix.of fun a b => kkQ 9 R (reflectMatrix K *ᵥ p₁) p₀ t 2 0 μ a b x) =
        kkQY R (reflectMatrix K *ᵥ p₁) p₀ t x * gamma μ := by
      ext a b
      exact kkQ_nine_eq hm hγ hγΛ hLp₁ hp₀ hLq ht hx μ a b
    have e₂ : (fun ν => Matrix.of fun a b => kkQ 9 R p₁ p₀ t 2 0 ν a b x) =
        fun ν => kkQY R p₁ p₀ t x * gamma ν := funext fun ν => by
      ext a b
      exact kkQ_nine_eq hm hγ hγΛ hp₁ hp₀ hq.le ht hx ν a b
    rw [e₁, e₂] at e
    exact e
  have hY := eq_of_cov_mul_gamma h hc
  rw [kkQY_indep R (reflectMatrix K *ᵥ p₁) p₁ p₀] at hY
  rw [kkQY_indep R p p₁ p₀]
  exact commute_of_conj h hY

/-- **`X(p₀) A(p₀) = c A(p₀)`.** -/
theorem kkQX_rest (p' : Fin 4 → ℝ) : ∃ c : ℂ,
    kkQX R (restMomentum R.m) p' t x * electronNumerator R.m (restMomentum R.m) =
      c • electronNumerator R.m (restMomentum R.m) :=
  ⟨_, (mul_rest_of_commute R.m (kkQX_commute hm hγ hγΛ ht hx rfl dot_e₁ p')
    (kkQX_commute hm hγ hγΛ ht hx rfl dot_e₂ p')
    (kkQX_commute hm hγ hγΛ ht hx rfl dot_e₃ p')).1⟩

/-- **`A(p₀) Y(p₀) = c A(p₀)`.** -/
theorem kkQY_rest (p : Fin 4 → ℝ) : ∃ c : ℂ,
    electronNumerator R.m (restMomentum R.m) * kkQY R p (restMomentum R.m) t x =
      c • electronNumerator R.m (restMomentum R.m) :=
  ⟨_, (mul_rest_of_commute R.m (kkQY_commute hm hγ hγΛ ht hx rfl dot_e₁ p)
    (kkQY_commute hm hγ hγΛ ht hx rfl dot_e₂ p)
    (kkQY_commute hm hγ hγΛ ht hx rfl dot_e₃ p)).2⟩

/-- **`A(p') Y(p') = c A(p')`** at an admissible outgoing momentum `p'` against `p₀`: the
reflection in `p₀ - p'` exchanges the two. -/
theorem kkQY_curve {p' : Fin 4 → ℝ} (hpq : IsPairQ R.m p' (restMomentum R.m)) : ∃ c : ℂ,
    electronNumerator R.m p' * kkQY R (restMomentum R.m) p' t x = c • electronNumerator R.m p' := by
  set p₀ := restMomentum R.m
  obtain ⟨hp', hp₀, hp'0, hp₀0, hq⟩ := hpq
  set K := p₀ - p'
  have hKK : Minkowski.dot K K ≠ 0 := by
    rw [show K = -(p' - p₀) from (neg_sub _ _).symm, dot_neg_neg']
    exact hq.ne'
  have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect hKK
  set S := reflSpin K
  set T := ((Minkowski.dot K K : ℝ) : ℂ)⁻¹ • reflSpin K
  have hL0 : reflectMatrix K *ᵥ p₀ = p' := by
    rw [QED.Dirac.reflectMatrix_mulVec]
    exact QED.GradedProof.SE2.reflect_sub_self (hp₀.trans hp'.symm) hKK
  have hL' : reflectMatrix K *ᵥ p' = p₀ := by
    rw [← hL0, QED.Dirac.reflectMatrix_mulVec, QED.Dirac.reflectMatrix_mulVec,
      QED.Dirac.reflect_reflect hKK]
  have hpq' : IsPairQ R.m p₀ p' := isPairQ_swap ⟨hp', hp₀, hp'0, hp₀0, hq⟩
  have hG := (pieceGood_kkQ hm hγ hγΛ ht hx (i := 9) (by decide : (2 : Fin 4) ≠ 0)
    (by decide +kernel)).1 _ _ _ h p₀ p' hpq' (by rw [hL0]; exact hp'0)
    (by rw [hL']; exact hp₀0)
  have hc : ∀ μ, S * (kkQY R p₀ p' t x * gamma μ) * T =
      vecAct (reflectMatrix K) (fun ν => kkQY R p' p₀ t x * gamma ν) μ := fun μ => by
    have e := hG μ
    beta_reduce at e
    rw [hL0, hL'] at e
    have e₁ : (Matrix.of fun a b => kkQ 9 R p₀ p' t 2 0 μ a b x) =
        kkQY R p₀ p' t x * gamma μ := by
      ext a b
      exact kkQ_nine_eq hm hγ hγΛ hp₀ hp' hq.le ht hx μ a b
    have e₂ : (fun ν => Matrix.of fun a b => kkQ 9 R p' p₀ t 2 0 ν a b x) =
        fun ν => kkQY R p' p₀ t x * gamma ν := funext fun ν => by
      ext a b
      exact kkQ_nine_eq hm hγ hγΛ hp' hp₀ hpq'.2.2.2.2.le ht hx ν a b
    rw [e₁, e₂] at e
    exact e
  have hY := eq_of_cov_mul_gamma h hc
  obtain ⟨c, hc₀⟩ := kkQY_rest hm hγ hγΛ ht hx p'
  refine ⟨c, ?_⟩
  have hA : S * electronNumerator R.m p₀ * T = electronNumerator R.m p' := by
    rw [← h.mul_electronNumerator_mul R.m p', hL']
  have hswap : ∀ Z : Matrix (Fin 4) (Fin 4) ℂ, T * Z * S = S * Z * T := fun Z => by
    simp only [T, Matrix.smul_mul, Matrix.mul_smul]
    rfl
  have hY' : kkQY R p₀ p' t x = S * kkQY R p' p₀ t x * T := by
    rw [← hswap, ← hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.mul_eq_one', Matrix.one_mul,
      Matrix.mul_assoc, h.mul_eq_one', Matrix.mul_one]
  rw [hY', ← hA, ← h.mul_mul_mul, hc₀]
  simp only [T, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  rfl

/-! ### Zero Pauli-weighted sums along the curve -/

/-- **`Q(4, 1, 3)` has zero Pauli-weighted sum along the curve.** -/
theorem kkPW_kkQ_four {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hu0 : u ≠ 0) :
    kkPW R.m (fun j => kkQ 4 R (restMomentum R.m) (curveMomentum R.m u) t 1 3 j.1 j.2.1 j.2.2 x)
      u = 0 := by
  have hpq := isPairQ_curve' hm hu hu0
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  obtain ⟨c, hc⟩ := kkQX_rest hm hγ hγΛ ht hx (curveMomentum R.m u)
  have e : ∀ μ a b, kkQ 4 R (restMomentum R.m) (curveMomentum R.m u) t 1 3 μ a b x =
      (gamma μ * kkQX R (restMomentum R.m) (curveMomentum R.m u) t x) a b := fun μ a b =>
    kkQ_four_eq hm hγ hγΛ hp hp' hq.le ht hx μ a b
  simp only [kkPW, e]
  rw [pauliSum_split R.m _ _
    (fun μ => gamma μ * kkQX R (restMomentum R.m) (curveMomentum R.m u) t x)]
  simp only [pauliSum_mul_right _ hc]
  rw [← Finset.mul_sum, ← pauliSum_split (V := fun μ => gamma μ),
    pauliSum_gamma hm.ne' hp' hp hq, mul_zero]

/-- **`Q(9, 2, 0)` has zero Pauli-weighted sum along the curve.** -/
theorem kkPW_kkQ_nine {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hu0 : u ≠ 0) :
    kkPW R.m (fun j => kkQ 9 R (restMomentum R.m) (curveMomentum R.m u) t 2 0 j.1 j.2.1 j.2.2 x)
      u = 0 := by
  have hpq := isPairQ_curve' hm hu hu0
  obtain ⟨c, hc⟩ := kkQY_curve hm hγ hγΛ ht hx hpq
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have e : ∀ μ a b, kkQ 9 R (restMomentum R.m) (curveMomentum R.m u) t 2 0 μ a b x =
      (kkQY R (restMomentum R.m) (curveMomentum R.m u) t x * gamma μ) a b := fun μ a b =>
    kkQ_nine_eq hm hγ hγΛ hp hp' hq.le ht hx μ a b
  simp only [kkPW, e]
  rw [pauliSum_split R.m _ _
    (fun μ => kkQY R (restMomentum R.m) (curveMomentum R.m u) t x * gamma μ)]
  simp only [pauliSum_mul_left _ hc]
  rw [← Finset.mul_sum, ← pauliSum_split (V := fun μ => gamma μ),
    pauliSum_gamma hm.ne' hp' hp hq, mul_zero]

end Cov

/-! ### The Pauli limit of `Q(5, 1, 0)` -/

/-- The Pauli-weighted `Q(5, 1, 0)` at `x = 1/2` along the curve. -/
noncomputable def kkQ5 (R : Params) (t u : ℝ) : ℂ :=
  kkPW R.m (fun j => kkQ 5 R (restMomentum R.m) (curveMomentum R.m u) t 1 0 j.1 j.2.1 j.2.2
    (1 / 2)) u

theorem kkQS_eq_kkQ5 {R : Params} {t : ℝ} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
    (ht : R.m ≤ t) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hu0 : u ≠ 0) :
    kkQS R t u = kkQ5 R t u := by
  have h4 := kkPW_kkQ_four hm hγ hγΛ ht half_mem_Ioo hu hu0
  have h9 := kkPW_kkQ_nine hm hγ hγΛ ht half_mem_Ioo hu hu0
  simp only [kkQS, kkQ5, kkPW, mul_add, Finset.sum_add_distrib] at h4 h9 ⊢
  rw [h4, h9, add_zero, add_zero]

/-- **The sum of the twelve longitudinal Pauli limits is the Pauli limit of `kCst · Q(5, 1, 0)`**
for every spectral mass `T ≥ 4`. -/
theorem tendsto_kkQ_five (P₀ : Params) (hm : 0 < P₀.m) {mγ Λ T : ℝ} (hmγ : 0 < mγ)
    (hΛ : mγ < Λ) (hT : 4 ≤ T) :
    Tendsto (evenQuot fun u => kCst { P₀ with mγ := mγ, Λ := Λ } *
        kkQ5 { P₀ with mγ := mγ, Λ := Λ } (√(P₀.m ^ 2 * T) / 2) u) (𝓝[≠] 0)
      (𝓝 (kkSumP P₀ mγ Λ T)) := by
  refine (tendsto_kkQS P₀ hm hmγ hΛ hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioo_mem_nhds
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))] with u (hu0 : u ≠ 0) hu
  have ht := le_half_sqrt hm hT
  simp only [evenQuot]
  rw [kkQS_eq_kkQ5 (R := { P₀ with mγ := mγ, Λ := Λ }) hm hmγ hΛ.le ht hu hu0,
    kkQS_eq_kkQ5 (R := { P₀ with mγ := mγ, Λ := Λ }) hm hmγ hΛ.le ht (neg_mem_Ioo_one' hu)
      (neg_ne_zero.2 hu0)]

end QED.ChainProof.SetCRegDisp

end
