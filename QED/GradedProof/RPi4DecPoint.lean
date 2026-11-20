/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecMajSec
public import QED.GradedProof.RPi4DecTwoW
public import QED.GradedProof.RPi4DecLipBase
public import QED.GradedProof.RPi4DecTwoInt

/-!
# (R-Π₄) step L9: the second differences of a collapsed integrand at one Feynman point

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (second
differences in `s`, the class inputs `QED.GradedProof.RPi4.DecVTwo`). At a Feynman point `z` and
photon mass `t ≥ 0`, the collapsed integrand `z_γ paramAtV(V + z_γ t)` at the tilted momenta
`cᵢ k'(s)` is of class `QED.GradedProof.RPi4.DecTwoReg` on `[-δ, δ]` with all three constants at
most `Λ ∑ₗ decMajF(kₗ)`, the absolute-term majorant at the interpolation nodes `kₗ` of the tilted
segment (`dec_twoReg_point`). The constant `Λ` depends only on the segment and the degrees, not
on `z` or `t`:

* `dec_twoReg_div_wt_nodes`: a polynomial family over `wtᵃ` has constants linear in a bound of
  its node values;
* `dec_cOneAt_congr`, `dec_cTwoAt_congr`, `dec_cThreeAt_congr`: the coefficients depend on the
  numerator only through its values;
* `dec_isUPoly_jointCoeff`: the coefficients of the joint quartic along a line, times
  `wt^{d+4}`, are polynomial of degree `2d + 8`;
* `dec_symanzikV_smul`: `V` at momenta proportional to one vector `k` is `∑ zᵢMᵢ² + k² R`;
* **`dec_twoReg_point`**.
-/

@[expose] public section

open Complex MeasureTheory Set Polynomial
open scoped Real

namespace QED.GradedProof.RPi4

open QED.TwoLoop.PauliZeroLimit QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.TwoLoop.PauliZeroExplicit (numQuartic eval_numQuartic)

/-! ### Polynomial families over a power of `wt` -/

/-- **A polynomial family over `wtᵃ` has constants linear in a bound of its node values.** -/
theorem dec_twoReg_div_wt_nodes {ι : Type*} (D a : ℕ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (f : ι → ℝ → ℂ), IsUPoly D f → ∀ (x : ι) (B : ℝ), 0 ≤ B →
      (∀ k, ‖f x (node D k)‖ ≤ B) →
      DecTwoReg (-(1 / 2)) (1 / 2) (fun u => f x u / wt u ^ a) (Λ * B) (Λ * B) (Λ * B) := by
  choose Mj Lj Kj hj using dec_twoReg_pow_ofReal
  obtain ⟨Mw, Lw, Kw, hw⟩ := dec_twoReg_wt a
  have hlow : ∀ u ∈ Icc (-(1 / 2) : ℝ) (1 / 2), (3 / 4 : ℝ) ^ a ≤ ‖wt u ^ a‖ := fun u hu => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (by norm_num) (norm_wt_ge (abs_le.mpr hu)) a
  have hinv := hw.inv (by positivity : (0 : ℝ) < (3 / 4) ^ a) hlow
  set Mi := ((3 / 4 : ℝ) ^ a)⁻¹
  set Li := Lw / ((3 / 4 : ℝ) ^ a) ^ 2
  set Ki := (2 * Lw ^ 2 + Mw * Kw) / ((3 / 4 : ℝ) ^ a) ^ 3
  obtain ⟨hMi, hLi, hKi⟩ := hinv.nonneg
  set lb : ℕ → ℝ := fun j => ∑ k : Fin (D + 1), ‖(lbasis D k).coeff j‖
  set βM := ∑ j ∈ Finset.range (D + 1), lb j * Mj j with hβMd
  set βL := ∑ j ∈ Finset.range (D + 1), lb j * Lj j with hβLd
  set βK := ∑ j ∈ Finset.range (D + 1), lb j * Kj j with hβKd
  have hβM : 0 ≤ βM := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hj j).nonneg.1
  have hβL : 0 ≤ βL := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hj j).nonneg.2.1
  have hβK : 0 ≤ βK := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hj j).nonneg.2.2
  refine ⟨βM * Mi + (βL * Mi + βM * Li) + (βK * Mi + βM * Ki + 2 * (βL * Li)), by positivity,
    fun f hf x B hB hnode => ?_⟩
  have hc : ∀ j, ‖(interp D f x).coeff j‖ ≤ B * lb j := fun j => dec_norm_interp_coeff_le x hnode j
  have hP := (dec_twoReg_upoly hf hj x).mono
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (hj j).nonneg.1)
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (hj j).nonneg.2.1)
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (hj j).nonneg.2.2)
  simp only [mul_assoc, ← Finset.mul_sum] at hP
  rw [← hβMd, ← hβLd, ← hβKd] at hP
  have hR := (hP.mul hinv).congr fun u _ => (div_eq_mul_inv (f x u) (wt u ^ a)).symm
  set T := βM * Mi + (βL * Mi + βM * Li) + (βK * Mi + βM * Ki + 2 * (βL * Li)) with hT
  have p1 := mul_nonneg hβM hMi
  have p2 := mul_nonneg hβL hMi
  have p3 := mul_nonneg hβM hLi
  have p4 := mul_nonneg hβK hMi
  have p5 := mul_nonneg hβM hKi
  have p6 := mul_nonneg hβL hLi
  have t1 : βM * Mi ≤ T := by rw [hT]; linarith
  have t2 : βL * Mi + βM * Li ≤ T := by rw [hT]; linarith
  have t3 : βK * Mi + βM * Ki + 2 * (βL * Li) ≤ T := by rw [hT]; linarith
  refine hR.mono ?_ ?_ ?_
  · linarith [mul_le_mul_of_nonneg_left t1 hB]
  · linarith [mul_le_mul_of_nonneg_left t2 hB]
  · linarith [mul_le_mul_of_nonneg_left t3 hB]

/-! ### The coefficients depend on the numerator only through its values -/

section Congr

variable {m : ℕ} (n : ℕ) {Q Q' : LoopQuartic} (α : Fin (m + 1) → Fin 2 → ℝ)
  (p : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → ℝ)

theorem dec_cOneAt_congr (h : Q.eval = Q'.eval) : cOneAt n Q α p z = cOneAt n Q' α p z := by
  have h1 : Q.evalC (loopComp (-loopShift α p z)) = Q'.evalC (loopComp (-loopShift α p z)) :=
    congrFun h _
  simp only [cOneAt, h1]

theorem dec_cTwoAt_congr (h : Q.eval = Q'.eval) : cTwoAt n Q α p z = cTwoAt n Q' α p z := by
  simp only [cTwoAt, QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.contractTwo_congr h
    (QED.TwoLoop.LimitCovariance.symanzikMatrix_transpose α _)]

theorem dec_cThreeAt_congr (h : Q.eval = Q'.eval) : cThreeAt n Q α z = cThreeAt n Q' α z := by
  simp only [cThreeAt, QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.contractFour_congr h
    (QED.TwoLoop.LimitCovariance.symanzikMatrix_transpose α _)]

end Congr

/-! ### The joint coefficients along a line -/

section Joint

variable {m : ℕ} (n d : ℕ) (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ)
  (k₀ w : Fin 4 → ℝ) (Qk : Fin (2 * d + 1) → LoopQuartic)

/-- **The coefficients of the joint quartic along a line are polynomial after `wt^{d+4}`.** -/
theorem dec_isUPoly_jointCoeff :
    IsUPoly (2 * d + 8) (fun (z : Fin (m + 1) → ℝ) u => wt u ^ (d + 4) *
      cOneAt n (jointQuartic (2 * d) d Qk u) α (fun i => cs i • lineK k₀ w u) z) ∧
    IsUPoly (2 * d + 8) (fun (z : Fin (m + 1) → ℝ) u => wt u ^ (d + 4) *
      cTwoAt n (jointQuartic (2 * d) d Qk u) α (fun i => cs i • lineK k₀ w u) z) ∧
    IsUPoly (2 * d + 8) (fun (z : Fin (m + 1) → ℝ) u => wt u ^ (d + 4) *
      cThreeAt n (jointQuartic (2 * d) d Qk u) α z) := by
  set mom : ℝ → Fin (m + 1) → Fin 4 → ℝ := fun u i => cs i • lineK k₀ w u with hmom_def
  have hmom : ∀ i ν, IsUPoly (ι := Fin (m + 1) → ℝ) 2 fun _ u => wt u * ((mom u i ν : ℝ) : ℂ) :=
    fun i ν => isUPoly_lineK (cs i) k₀ w ν
  have hS := isUPoly_loopShift α mom (fun z => z) hmom
  have hX : ∀ a : LoopIndex, IsUPoly 2 fun (z : Fin (m + 1) → ℝ) u =>
      wt u * loopComp (-loopShift α (mom u) z) a := fun a => by
    have e : ∀ (z : Fin (m + 1) → ℝ) u, wt u * loopComp (-loopShift α (mom u) z) a =
        -(wt u * ((loopShift α (mom u) z a.1 a.2 : ℝ) : ℂ)) := by
      intro z u
      simp [loopComp]
    exact (hS a.1 a.2).neg.congr fun z u _ => (e z u).symm
  have hL : ∀ k : Fin (2 * d + 1), IsUPoly (ι := Fin (m + 1) → ℝ) (2 * d) fun _ u =>
      wt (node (2 * d) k) ^ d * (lbasis (2 * d) k).eval (u : ℂ) := fun k =>
    (isUPoly_lbasis (2 * d) k).const_mul _
  have e : ∀ (F : LoopQuartic → (Fin (m + 1) → ℝ) → ℝ → ℂ) (j : ℕ),
      (∀ z u, F (jointQuartic (2 * d) d Qk u) z u =
        ∑ k, lam (2 * d) d u k * F (Qk k) z u) →
      ∀ (z : Fin (m + 1) → ℝ), ∀ u ∈ Ioo (-1 : ℝ) 1,
        ∑ k, wt (node (2 * d) k) ^ d * (lbasis (2 * d) k).eval (u : ℂ) *
          (wt u ^ (j + 4) * F (Qk k) z u) =
        wt u ^ (d + 4) * (wt u ^ j * F (jointQuartic (2 * d) d Qk u) z u) := by
    intro F j hF z u hu
    have hw := wt_ne_zero hu
    rw [hF, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [lam]
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ∀ k : Fin (2 * d + 1), IsUPoly 8 fun (z : Fin (m + 1) → ℝ) u =>
        wt u ^ (0 + 4) * cOneAt n (Qk k) α (mom u) z := fun k =>
      ((isUPoly_evalC (Qk k) _ hX).const_mul (fun z =>
        ((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ * ((n - 4).factorial : ℂ))).congr
        fun z u _ => by simp only [cOneAt]; ring
    refine (IsUPoly.sum Finset.univ fun k _ => (hL k).mul (h1 k)).congr fun z u hu => ?_
    have := e (fun Q z u => cOneAt n Q α (mom u) z) 0 (fun z u => by
      simp only [cOneAt, jointQuartic, evalC_qsum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring) z u hu
    simp only [pow_zero, one_mul, mul_assoc] at this ⊢
    exact this
  · have h2 : ∀ k : Fin (2 * d + 1), IsUPoly 8 fun (z : Fin (m + 1) → ℝ) u =>
        wt u ^ (0 + 4) * cTwoAt n (Qk k) α (mom u) z := fun k =>
      ((isUPoly_wt_pow 2).mul ((isUPoly_contractTwo (Qk k) _ (fun z => symanzikMatrix α z)
        hX).const_mul (fun z => ((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ *
          (((n - 5).factorial : ℂ) / 2)))).congr
        fun z u _ => by simp only [cTwoAt]; ring
    refine (IsUPoly.sum Finset.univ fun k _ => (hL k).mul (h2 k)).congr fun z u hu => ?_
    have := e (fun Q z u => cTwoAt n Q α (mom u) z) 0 (fun z u => by
      simp only [cTwoAt, jointQuartic, contractTwo_qsum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring) z u hu
    rw [pow_zero, one_mul] at this
    exact this
  · have h3 : ∀ k : Fin (2 * d + 1), IsUPoly 8 fun (z : Fin (m + 1) → ℝ) u =>
        wt u ^ (0 + 4) * cThreeAt n (Qk k) α z := fun k =>
      (isUPoly_wt_pow 4).mul_const fun z => cThreeAt n (Qk k) α z
    refine (IsUPoly.sum Finset.univ fun k _ => (hL k).mul (h3 k)).congr fun z u hu => ?_
    have := e (fun Q z _ => cThreeAt n Q α z) 0 (fun z u => by
      simp only [cThreeAt, jointQuartic, contractFour_qsum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring) z u hu
    rw [pow_zero, one_mul] at this
    exact this

end Joint

/-- **`V` at momenta proportional to one vector**: `V = ∑ zᵢ Mᵢ² + k² R`. -/
theorem dec_symanzikV_smul {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (M : Fin (m + 1) → ℝ)
    (z : Fin (m + 1) → ℝ) (cs : Fin (m + 1) → ℝ) (k : Fin 4 → ℝ) :
    symanzikV α (fun i => cs i • k) M z =
      ∑ i, z i * M i ^ 2 + Minkowski.dot k k * remainder α z cs := by
  have h := symanzikV_smul_add_smul α M z cs 0 (P := k) (K := 0) (by simp [Minkowski.dot_eq])
  simp only [Pi.zero_apply, smul_zero, add_zero] at h
  rw [h]
  simp [Minkowski.dot_eq]

/-! ### Relative constants -/

/-- **A product with relative inverse-power constants**: if `g` has constants `P, P, P` and `h`
has `ω, N κ ω, N (N + 1) κ² ω` with `N ≤ n`, the product has constants at most
`2 (1 + n κ + n (n + 1) κ²) P ω`. -/
theorem dec_twoReg_mul_rel {a b P ω κ : ℝ} {N n : ℕ} {g h : ℝ → ℂ}
    (hg : DecTwoReg a b g P P P) (hh : DecTwoReg a b h ω (N * κ * ω) (N * (N + 1) * κ ^ 2 * ω))
    (hN : N ≤ n) (hκ : 0 ≤ κ) :
    DecTwoReg a b (fun s => g s * h s) (2 * (1 + n * κ + n * (n + 1) * κ ^ 2) * (P * ω))
      (2 * (1 + n * κ + n * (n + 1) * κ ^ 2) * (P * ω))
      (2 * (1 + n * κ + n * (n + 1) * κ ^ 2) * (P * ω)) := by
  have hP := hg.nonneg.1
  have hω := hh.nonneg.1
  have hPω : 0 ≤ P * ω := mul_nonneg hP hω
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : (N : ℝ) * κ ≤ n * κ := mul_le_mul_of_nonneg_right hNn hκ
  have h2 : (N : ℝ) * (N + 1) * κ ^ 2 ≤ n * (n + 1) * κ ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul hNn (by linarith) (by positivity) (by linarith))
      (sq_nonneg κ)
  have h3 : 0 ≤ (N : ℝ) * κ := mul_nonneg hN0 hκ
  have h4 : 0 ≤ (N : ℝ) * (N + 1) * κ ^ 2 := by positivity
  refine (hg.mul hh).mono ?_ ?_ ?_
  · nlinarith
  · have : P * ω + P * (N * κ * ω) ≤ (1 + n * κ) * (P * ω) := by nlinarith
    nlinarith
  · have : P * ω + P * (N * (N + 1) * κ ^ 2 * ω) + 2 * (P * (N * κ * ω)) ≤
        (1 + n * (n + 1) * κ ^ 2 + 2 * (n * κ)) * (P * ω) := by nlinarith
    nlinarith

/-- `W⁻ᴺ ≤ ρⁿ v⁻ᴺ` for `0 < v ≤ ρ W`, `1 ≤ ρ`, `N ≤ n`. -/
theorem dec_inv_pow_le_rel {v W ρ : ℝ} {N n : ℕ} (hv : 0 < v) (hvW : v ≤ ρ * W) (hρ : 1 ≤ ρ)
    (hN : N ≤ n) : W⁻¹ ^ N ≤ ρ ^ n * (v ^ N)⁻¹ := by
  have hW : 0 < W := by
    by_contra h
    have h' := not_lt.mp h
    nlinarith
  have h1 : W⁻¹ ≤ ρ * v⁻¹ := by
    rw [inv_le_comm₀ hW (by positivity), mul_inv, inv_inv]
    calc ρ⁻¹ * v ≤ ρ⁻¹ * (ρ * W) := mul_le_mul_of_nonneg_left hvW (by positivity)
      _ = W := by field_simp
  calc W⁻¹ ^ N ≤ (ρ * v⁻¹) ^ N := pow_le_pow_left₀ (by positivity) h1 N
    _ = ρ ^ N * (v ^ N)⁻¹ := by rw [mul_pow, inv_pow]
    _ ≤ ρ ^ n * (v ^ N)⁻¹ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hρ hN) (by positivity)

/-- **`V + τ` at a node below the top of the segment**: with `V = m₂ + σ R` (`R ≥ 0`),
`m₂ + S₀ R ≥ 0`, `W = m₂ - δ R + τ > 0` and `S₀ < σ ≤ S`: `0 < m₂ + σ R + τ ≤ ρ W`,
`ρ = 1 + (S + δ) / (-δ - S₀)`. -/
theorem dec_node_le_rel {m₂ R S₀ S δ σ τ : ℝ} (hR : 0 ≤ R) (h0 : 0 ≤ m₂ + S₀ * R)
    (hS₀ : S₀ < -δ) (hτ : 0 ≤ τ) (hW : 0 < m₂ + -δ * R + τ) (hσ : S₀ < σ) (hσS : σ ≤ S)
    (hδS : -δ ≤ S) :
    0 < m₂ + σ * R + τ ∧ m₂ + σ * R + τ ≤ (1 + (S + δ) / (-δ - S₀)) * (m₂ + -δ * R + τ) := by
  have hd : 0 < -δ - S₀ := by linarith
  have hRle : R ≤ (-δ - S₀)⁻¹ * (m₂ + -δ * R + τ) := by
    have := dec_rem_le_of_nonneg h0 hR hS₀ le_rfl hτ
    linarith
  constructor
  · rcases lt_or_eq_of_le (add_nonneg h0 hτ) with h | h
    · nlinarith
    · have hRp : 0 < R := by nlinarith
      nlinarith
  · have e : (1 + (S + δ) / (-δ - S₀)) * (m₂ + -δ * R + τ) =
        (m₂ + -δ * R + τ) + (S + δ) * ((-δ - S₀)⁻¹ * (m₂ + -δ * R + τ)) := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hRle (by linarith : 0 ≤ S + δ)
    nlinarith

/-! ### The collapsed integrand at one Feynman point -/

/-- The interpolation nodes of the tilted segment `lineK (tiltBase c S₀ S) (tiltDir c S₀ S)`. -/
noncomputable def decKNode (c S₀ S : ℝ) (D : ℕ) (l : Fin (D + 1)) : Fin 4 → ℝ :=
  lineK (tiltBase c S₀ S) (tiltDir c S₀ S) (node D l)

/-- **The node majorant**: the sum over the interpolation nodes of the absolute-term majorant. -/
noncomputable def decNodeMaj {m : ℕ} (n : ℕ) (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ) (M : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (c S₀ S : ℝ) (D : ℕ) (t : ℝ) (z : Fin (m + 1) → ℝ) : ℝ :=
  ∑ l : Fin (D + 1), decMajF n (numQuartic (N (decKNode c S₀ S D l))) α
    (fun i => cs i • decKNode c S₀ S D l) M γ t z

/-- **Second differences of the collapsed integrand at one Feynman point.** For a numerator
`N k` polynomial of degree `d` in `k`, at a point `z` with `U ≠ 0` where `V ≥ 0` at the tilted
momentum `S₀ < -δ`, and every photon mass `t ≥ 0` with `V + z_γ t > 0` at `-δ`, the integrand
`s ↦ z_γ paramAtV(V(s) + z_γ t)` at the tilted momenta is of class `DecTwoReg` on `[-δ, δ]` with
all constants `Λ · decNodeMaj`, where `Λ` does not depend on `z` or `t`. The interpolation nodes
are those of the tilted segment over `[Sl, S] ⊇ [-δ, δ]`; their squares lie in `(S₀, S]`. -/
theorem dec_twoReg_point {m n : ℕ} (hn : 5 ≤ n) (α : Fin (m + 1) → Fin 2 → ℝ) (γ : Fin (m + 1))
    (cs : Fin (m + 1) → ℝ) (M : Fin (m + 1) → ℝ)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) {d : ℕ}
    (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) (hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k)
    {c S₀ Sl S δ : ℝ} (hδ : 0 < δ) (hS₀ : S₀ < -δ) (hSl : Sl ≤ -δ) (hS : δ ≤ S)
    (hSc : S < 2 * c ^ 2)
    (hnode : ∀ l, S₀ < Minkowski.dot (decKNode c Sl S (2 * d + 8) l)
        (decKNode c Sl S (2 * d + 8) l) ∧
      Minkowski.dot (decKNode c Sl S (2 * d + 8) l) (decKNode c Sl S (2 * d + 8) l) ≤ S) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → symanzikU α z ≠ 0 →
      0 ≤ symanzikV α (fun i => cs i • tiltVec c S₀) M z → ∀ t : ℝ, 0 ≤ t →
      0 < symanzikV α (fun i => cs i • tiltVec c (-δ)) M z + z γ * t →
      DecTwoReg (-δ) δ (fun s => (z γ : ℂ) * paramAtV n (numQuartic (N (tiltVec c s))) α
          (fun i => cs i • tiltVec c s) z
          (symanzikV α (fun i => cs i • tiltVec c s) M z + z γ * t))
        (Λ * decNodeMaj n N α cs M γ c Sl S (2 * d + 8) t z)
        (Λ * decNodeMaj n N α cs M γ c Sl S (2 * d + 8) t z)
        (Λ * decNodeMaj n N α cs M γ c Sl S (2 * d + 8) t z) := by
  classical
  set D := 2 * d + 8 with hD
  set base := tiltBase c Sl S
  set dir := tiltDir c Sl S
  obtain ⟨Λ₁, hΛ₁, hdiv⟩ := dec_twoReg_div_wt_nodes (ι := Fin (m + 1) → ℝ) D (d + 4)
  obtain ⟨Lu, Ku, hLu, hKu, htilt⟩ := dec_twoReg_tilt_lin (c := c) (by linarith : Sl < S) hSc
  set F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ := fun u ℓ => N (lineK base dir u) ℓ
  have hF : IsUPoly (2 * d) fun ℓ u => wt u ^ d * F u ℓ := fun ℓ => by
    have h := isUPoly_eval_of_isLoopPoly (hk ℓ) (ι := Unit)
      (ℓ := fun _ u _ => lineK base dir u) fun _ ν => by
        simpa using isUPoly_lineK (ι := Unit) 1 base dir ν
    exact h ()
  set Qk : Fin (2 * d + 1) → LoopQuartic := fun k =>
    numQuartic (N (lineK base dir (node (2 * d) k)))
  have hQk : ∀ k, (Qk k).eval = F (node (2 * d) k) := fun k => eval_numQuartic (hQ _)
  set J : ℝ → LoopQuartic := fun u => jointQuartic (2 * d) d Qk u
  have hJ : ∀ u ∈ Ioo (-1 : ℝ) 1, (J u).eval = (numQuartic (N (lineK base dir u))).eval :=
    fun u hu => (eval_jointQuartic hF hQk hu).trans (eval_numQuartic (hQ _)).symm
  obtain ⟨hP1, hP2, hP3⟩ := dec_isUPoly_jointCoeff (m := m) n d α cs base dir Qk
  set κ := (-δ - S₀)⁻¹ with hκ
  have hκ0 : 0 ≤ κ := inv_nonneg.mpr (by linarith)
  set ρ := 1 + (S + δ) / (-δ - S₀) with hρ
  have hρ1 : 1 ≤ ρ := by
    have : 0 ≤ (S + δ) / (-δ - S₀) := div_nonneg (by linarith) (by linarith)
    linarith
  set Λ₂ := Λ₁ * (1 + Lu + Lu ^ 2 + Ku) with hΛ₂
  have hΛ₂0 : 0 ≤ Λ₂ := by positivity
  set Λ₃ := 2 * (1 + n * κ + n * (n + 1) * κ ^ 2) with hΛ₃
  have hΛ₃0 : 0 ≤ Λ₃ := by positivity
  refine ⟨Λ₃ * Λ₂ * ρ ^ n, by positivity, fun z hz hU h0 t ht hW => ?_⟩
  set τ := z γ * t with hτdef
  have hτ : 0 ≤ τ := mul_nonneg (hz γ) ht
  set W := symanzikV α (fun i => cs i • tiltVec c (-δ)) M z + τ with hWdef
  -- the numerator factors along the tilt
  have step : ∀ (G : (Fin 4 → ℝ) → ℂ) (f : (Fin (m + 1) → ℝ) → ℝ → ℂ), IsUPoly D f →
      (∀ u ∈ Ioo (-1 : ℝ) 1, f z u / wt u ^ (d + 4) = G (lineK base dir u)) →
      ∀ B : ℝ, 0 ≤ B → (∀ l, ‖f z (node D l)‖ ≤ B) →
      DecTwoReg (-δ) δ (fun s => G (tiltVec c s)) (Λ₂ * B) (Λ₂ * B) (Λ₂ * B) := by
    intro G f hf hfG B hB hfn
    have h1 := (hdiv f hf z B hB hfn).congr fun u hu => hfG u (dec_Icc_half_mem_Ioo hu)
    have h2 := (htilt G _ _ _ h1).subinterval hSl hS
    have hB1 : 0 ≤ Λ₁ * B := mul_nonneg hΛ₁ hB
    refine h2.mono ?_ ?_ ?_
    · have : Λ₁ * B ≤ Λ₁ * B * (1 + Lu + Lu ^ 2 + Ku) := le_mul_of_one_le_right hB1
        (by nlinarith)
      linarith
    · have : Λ₁ * B * Lu ≤ Λ₁ * B * (1 + Lu + Lu ^ 2 + Ku) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hB1
      linarith
    · have : Λ₁ * B * Lu ^ 2 + Λ₁ * B * Ku ≤ Λ₁ * B * (1 + Lu + Lu ^ 2 + Ku) := by
        nlinarith
      linarith
  -- the inverse powers of `W`
  have hinv : ∀ Nj : ℕ, DecTwoReg (-δ) δ (fun s => ((symanzikV α (fun i => cs i • tiltVec c s)
      M z + τ : ℝ) : ℂ)⁻¹ ^ Nj) (W⁻¹ ^ Nj) (Nj * κ * W⁻¹ ^ Nj)
      (Nj * (Nj + 1) * κ ^ 2 * W⁻¹ ^ Nj) := fun Nj =>
    dec_twoReg_inv_pow_tilt Nj α M z cs hz hU (by linarith) (by linarith) hS₀ h0 hτ hW
  -- the nodes
  set kn : Fin (D + 1) → Fin 4 → ℝ := fun l => decKNode c Sl S D l with hkn
  set Qn : Fin (D + 1) → LoopQuartic := fun l => numQuartic (N (kn l)) with hQn
  have hzγ := hz γ
  have hJn : ∀ l, (J (node D l)).eval = (Qn l).eval := fun l => hJ _ (node_mem D l)
  have hwn : ∀ l, ‖wt (node D l) ^ (d + 4)‖ ≤ 1 := fun l => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (dec_norm_wt_le_one' (node_mem D l))
  -- one coefficient
  have term : ∀ (cf : LoopQuartic → (Fin 4 → ℝ) → (Fin (m + 1) → ℝ) → ℂ),
      (∀ Q Q' k, Q.eval = Q'.eval → cf Q k z = cf Q' k z) →
      IsUPoly D (fun z' u => wt u ^ (d + 4) * cf (J u) (lineK base dir u) z') →
      ∀ Nj : ℕ, Nj ≤ n →
      DecTwoReg (-δ) δ (fun s => (z γ : ℂ) * cf (numQuartic (N (tiltVec c s))) (tiltVec c s) z *
          ((symanzikV α (fun i => cs i • tiltVec c s) M z + τ : ℝ) : ℂ)⁻¹ ^ Nj)
        (Λ₃ * (Λ₂ * (∑ l, z γ * ‖cf (Qn l) (kn l) z‖) * W⁻¹ ^ Nj))
        (Λ₃ * (Λ₂ * (∑ l, z γ * ‖cf (Qn l) (kn l) z‖) * W⁻¹ ^ Nj))
        (Λ₃ * (Λ₂ * (∑ l, z γ * ‖cf (Qn l) (kn l) z‖) * W⁻¹ ^ Nj)) := by
    intro cf hcf hPf Nj hNj
    set Bf := ∑ l, z γ * ‖cf (Qn l) (kn l) z‖
    have hBf : 0 ≤ Bf := Finset.sum_nonneg fun l _ => by positivity
    have hG := step (fun k => (z γ : ℂ) * cf (numQuartic (N k)) k z)
      (fun z' u => (z' γ : ℂ) * (wt u ^ (d + 4) * cf (J u) (lineK base dir u) z'))
      (hPf.const_mul fun z' => (z' γ : ℂ))
      (fun u hu => by
        rw [hcf _ _ _ (hJ u hu), mul_div_assoc,
          mul_div_cancel_left₀ _ (pow_ne_zero _ (wt_ne_zero hu))])
      Bf hBf (fun l => by
        rw [hcf _ _ _ (hJn l), norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hzγ]
        calc z γ * (‖wt (node D l) ^ (d + 4)‖ * ‖cf (Qn l) (lineK base dir (node D l)) z‖)
            ≤ z γ * ‖cf (Qn l) (kn l) z‖ :=
              mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (hwn l)) hzγ
          _ ≤ Bf := Finset.single_le_sum (f := fun l => z γ * ‖cf (Qn l) (kn l) z‖)
              (fun l _ => by positivity) (Finset.mem_univ l))
    exact dec_twoReg_mul_rel hG (hinv Nj) hNj hκ0
  have T1 := term (fun Q k z' => cOneAt n Q α (fun i => cs i • k) z')
    (fun Q Q' k h => dec_cOneAt_congr n α _ z h) hP1 (n - 3) (by omega)
  have T2 := term (fun Q k z' => cTwoAt n Q α (fun i => cs i • k) z')
    (fun Q Q' k h => dec_cTwoAt_congr n α _ z h) hP2 (n - 4) (by omega)
  have T3 := term (fun Q _ z' => cThreeAt n Q α z')
    (fun Q Q' k h => dec_cThreeAt_congr n α z h) hP3 (n - 5) (by omega)
  -- the comparison with the node majorant
  set m₂ := ∑ i, z i * M i ^ 2
  set R := remainder α z cs
  have hR : 0 ≤ R := remainder_nonneg α hz hU cs
  have h0' : 0 ≤ m₂ + S₀ * R := by
    rw [dec_symanzikV_tilt α M z cs (by linarith)] at h0; exact h0
  have hWe : W = m₂ + -δ * R + τ := by
    rw [hWdef, dec_symanzikV_tilt α M z cs (by linarith)]
  have hW' : 0 < m₂ + -δ * R + τ := hWe ▸ hW
  have key : ∀ l, z γ * ‖cOneAt n (Qn l) α (fun i => cs i • kn l) z‖ * W⁻¹ ^ (n - 3) +
      z γ * ‖cTwoAt n (Qn l) α (fun i => cs i • kn l) z‖ * W⁻¹ ^ (n - 4) +
      z γ * ‖cThreeAt n (Qn l) α z‖ * W⁻¹ ^ (n - 5) ≤
      ρ ^ n * decMajF n (Qn l) α (fun i => cs i • kn l) M γ t z := fun l => by
    obtain ⟨hv, hvW⟩ := dec_node_le_rel hR h0' hS₀ hτ hW' (hnode l).1 (hnode l).2
      (by linarith)
    rw [← hWe] at hvW
    have eV : symanzikV α (fun i => cs i • kn l) M z =
        m₂ + Minkowski.dot (kn l) (kn l) * R := dec_symanzikV_smul α M z cs (kn l)
    rw [← eV] at hv hvW
    have e1 := dec_inv_pow_le_rel hv hvW hρ1 (N := n - 3) (n := n) (by omega)
    have e2 := dec_inv_pow_le_rel hv hvW hρ1 (N := n - 4) (n := n) (by omega)
    have e3 := dec_inv_pow_le_rel hv hvW hρ1 (N := n - 5) (n := n) (by omega)
    have a1 := mul_le_mul_of_nonneg_left e1
      (by positivity : 0 ≤ z γ * ‖cOneAt n (Qn l) α (fun i => cs i • kn l) z‖)
    have a2 := mul_le_mul_of_nonneg_left e2
      (by positivity : 0 ≤ z γ * ‖cTwoAt n (Qn l) α (fun i => cs i • kn l) z‖)
    have a3 := mul_le_mul_of_nonneg_left e3
      (by positivity : 0 ≤ z γ * ‖cThreeAt n (Qn l) α z‖)
    simp only [decMajF, decMajP]
    rw [← hτdef]
    linarith only [a1, a2, a3]
  have hfin : (∑ l, z γ * ‖cOneAt n (Qn l) α (fun i => cs i • kn l) z‖) * W⁻¹ ^ (n - 3) +
      (∑ l, z γ * ‖cTwoAt n (Qn l) α (fun i => cs i • kn l) z‖) * W⁻¹ ^ (n - 4) +
      (∑ l, z γ * ‖cThreeAt n (Qn l) α z‖) * W⁻¹ ^ (n - 5) ≤
      ρ ^ n * decNodeMaj n N α cs M γ c Sl S D t z := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, decNodeMaj, Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ => key l
  have hfin' := mul_le_mul_of_nonneg_left hfin (mul_nonneg hΛ₃0 hΛ₂0)
  refine (((T1.add T2).add T3).congr fun s _ => ?_).mono ?_ ?_ ?_
  · rw [paramAtV_eq, inv_pow, inv_pow, inv_pow]
    push_cast
    ring
  all_goals exact le_trans (le_of_eq (by ring)) (hfin'.trans_eq (by ring))

end QED.GradedProof.RPi4

end
