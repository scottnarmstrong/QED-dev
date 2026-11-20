/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajPiece

/-!
# (R-Π₄) step L10: the numerators of the one-loop pieces along the ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The `²³` entries
of the pure-mass-insertion numerators (`d₂ = 0`) of the pieces `eVal0`, `eVal2`, `eVal4` of the
inserted bubble, along the ray `k = r v` (`v = majRayVec 1`, `v·v = 1`):

* homogeneity: `n₀`, `n₁` are homogeneous of degree `4`, `2` in `(x, y)`
  (`maj_nT0_smul`, `maj_nT1_smul`), and so `tnS₀`, `tnS₁` in `(k, q)`;
* the values on the ray (`v̸ v̸ = -1`, `Tr[γ²γ³] = 0`): with `T = Tr[A v̸ B v̸]`,
  `n₀(α v, β v) = -2 d_m α β³ T`, `n₁(α v, β v) = 2 d_m α β T` (`maj_nT0_val`, `maj_nT1_val`);
  at the shift `ℓ₀ = -σ v` the momenta are `x = α v`, `y = β v` with `{α, β} = {1 - σ, -σ}`
  (`bx ≠ bY`), so `α β = -σ (1 - σ)`: **the degree-four part vanishes like `σ (1 - σ)`**, the
  factor that `QED.GradedProof.RPi4.maj_piece_ray` needs;
* the `²³` entry of the `eVal4` numerator is `d_m Tr[γ²γ³] (…) = 0`.

* **`maj_tiltRay_eVal0`**, **`maj_tiltRay_eVal2`**, **`maj_tiltRay_eVal4`**: `MajTiltRay` of the
  three kinds of pieces (with `b₀ = bx ≠ bY = b₄`).
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.CountertermLimit
open QED.TwoLoop.Bridge (propDenom IsLoopPoly)
open QED.Integration.Feynman (simplexSet simplexPoint)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Traces and homogeneity -/

theorem maj_trace_gamma_mul {a b : Fin 4} (h : Minkowski.metric a b = 0) :
    (Dirac.gamma a * Dirac.gamma b).trace = 0 := by
  have e := congrArg Matrix.trace (Dirac.gamma_anticomm a b)
  rw [Matrix.trace_add, Matrix.trace_mul_comm (Dirac.gamma b), h] at e
  simp only [mul_zero, Complex.ofReal_zero, zero_smul, Matrix.trace_zero] at e
  linear_combination e / 2

theorem maj_trace_gAB (sw : Bool) : (gAF sw 2 3 * gBF sw 2 3).trace = 0 := by
  cases sw <;> simp only [gAF, gBF, Bool.false_eq_true, ite_true, ite_false] <;>
    exact maj_trace_gamma_mul (by simp [Minkowski.metric])

theorem maj_zk_smul (r : ℝ) (k : Fin 4 → ℝ) (c : Bool) (q : Fin 4 → ℝ) :
    zk (r • k) c (r • q) = r • zk k c q := by
  cases c <;> simp [zk, smul_add]

theorem maj_v0_smul (r : ℝ) (y : Fin 4 → ℝ) : v0 (r • y) = (r : ℂ) ^ 2 * v0 y := by
  simp only [v0, propDenom, QED.TwoLoop.MassScaling.dot_smul]
  push_cast
  ring

theorem maj_nT0_smul (A B : Mat) (d₂ dm r : ℝ) (x y : Fin 4 → ℝ) :
    nT0 A B d₂ dm (r • x) (r • y) = (r : ℂ) ^ 4 * nT0 A B d₂ dm x y := by
  simp only [nT0, insT0, insT2, insT4, maj_v0_smul, Dirac.slash_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem maj_nT1_smul (A B : Mat) (d₂ dm r : ℝ) (x y : Fin 4 → ℝ) :
    nT1 A B d₂ dm (r • x) (r • y) = (r : ℂ) ^ 2 * nT1 A B d₂ dm x y := by
  simp only [nT1, insT2, insT4, maj_v0_smul, Dirac.slash_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem maj_tnS0_smul (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (r : ℝ) (k q : Fin 4 → ℝ)
    (μ ν : Fin 4) :
    tnS sw 0 d₂ dm bx bY (r • k) (r • q) μ ν = (r : ℂ) ^ 4 * tnS sw 0 d₂ dm bx bY k q μ ν := by
  rw [← nT0_gAB, ← nT0_gAB, maj_zk_smul, maj_zk_smul, maj_nT0_smul]

theorem maj_tnS1_smul (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (r : ℝ) (k q : Fin 4 → ℝ)
    (μ ν : Fin 4) :
    tnS sw 1 d₂ dm bx bY (r • k) (r • q) μ ν = (r : ℂ) ^ 2 * tnS sw 1 d₂ dm bx bY k q μ ν := by
  rw [← nT1_gAB, ← nT1_gAB, maj_zk_smul, maj_zk_smul, maj_nT1_smul]

/-- The padded `n₁` numerator of `eVal2` splits into degrees `4` and `2`. -/
theorem maj_padN_tnS1_smul (sw : Bool) (dm m0 : ℝ) (bx bY : Bool) (r : ℝ) (k q : Fin 4 → ℝ) :
    padN (tnS sw 1 0 dm bx bY) m0 bx (r • k) (r • q) 2 3 =
      (r : ℂ) ^ 4 * (tnS sw 1 0 dm bx bY k q 2 3 * propDenom 0 0 (zk k bx q)) +
        (r : ℂ) ^ 2 * (tnS sw 1 0 dm bx bY k q 2 3 * (m0 : ℂ) ^ 2) := by
  simp only [padN]
  rw [maj_tnS1_smul, maj_zk_smul]
  simp only [propDenom, QED.TwoLoop.MassScaling.dot_smul]
  push_cast
  ring

/-! ### The values on the ray -/

section Values

variable (A B : Mat) (dm α β : ℝ) {v : Fin 4 → ℝ} (hv : Minkowski.dot v v = 1)
include hv

theorem maj_slash_sq : Dirac.slash v * Dirac.slash v = -1 := by
  rw [Dirac.slash_mul_slash, hv]
  simp

theorem maj_insT2_val :
    insT2 A B 0 dm (α • v) (β • v) =
      -(dm * β ^ 2 : ℂ) * (A * B).trace +
        2 * dm * α * β * (A * (Dirac.slash v * (B * Dirac.slash v))).trace := by
  simp only [insT2, Dirac.slash_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, maj_slash_sq hv, Matrix.mul_neg, Matrix.mul_one, Matrix.trace_neg]
  push_cast
  ring

theorem maj_v0_val : v0 (α • v) = (α : ℂ) ^ 2 := by
  rw [maj_v0_smul]
  simp [v0, propDenom, hv]

/-- `n₀(α v, β v) = 2 d_m β⁴ Tr[AB] - 2 d_m α β³ Tr[A v̸ B v̸]` (`d₂ = 0`). -/
theorem maj_nT0_val :
    nT0 A B 0 dm (α • v) (β • v) = 2 * dm * β ^ 4 * (A * B).trace -
      2 * dm * α * β ^ 3 * (A * (Dirac.slash v * (B * Dirac.slash v))).trace := by
  simp only [nT0, maj_insT2_val A B dm α β hv, maj_v0_val β hv, insT0, insT4]
  push_cast
  ring

/-- `n₁(α v, β v) = -3 d_m β² Tr[AB] + 2 d_m α β Tr[A v̸ B v̸]` (`d₂ = 0`). -/
theorem maj_nT1_val :
    nT1 A B 0 dm (α • v) (β • v) = -3 * dm * β ^ 2 * (A * B).trace +
      2 * dm * α * β * (A * (Dirac.slash v * (B * Dirac.slash v))).trace := by
  simp only [nT1, maj_insT2_val A B dm α β hv, maj_v0_val β hv, insT4]
  ring

end Values

theorem maj_dot_v : Minkowski.dot (majRayVec 1) (majRayVec 1) = 1 :=
  dot_majRayVec zero_le_one

/-- The momenta at the shift `ℓ₀ = -σ v`. -/
theorem maj_zk_shift (v : Fin 4 → ℝ) (c : Bool) (σ : ℝ) :
    zk v c (-(σ • v)) = (if c then 1 - σ else -σ) • v := by
  cases c
  · simp [zk]
  · simp only [zk, ite_true]
    rw [sub_smul, one_smul, sub_eq_add_neg]

/-- `|α β| = σ (1 - σ)`, `|α|, |β| ≤ 1` at the shift, if `bx ≠ bY`. -/
theorem maj_shift_abs {bx bY : Bool} (h : bx ≠ bY) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    |(if bx then 1 - σ else -σ) * (if bY then 1 - σ else -σ)| = σ * (1 - σ) ∧
      |(if bx then 1 - σ else -σ)| ≤ 1 ∧ |(if bY then 1 - σ else -σ)| ≤ 1 := by
  have a1 : |1 - σ| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have a2 : |-σ| ≤ 1 := by rw [abs_neg]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  have e : |(1 - σ) * -σ| = σ * (1 - σ) := by
    rw [abs_mul, abs_neg, abs_of_nonneg h0, abs_of_nonneg (by linarith)]; ring
  cases bx <;> cases bY <;> simp only [ne_eq, not_true_eq_false] at h <;>
    simp only [Bool.false_eq_true, ite_true, ite_false]
  · exact ⟨by rw [mul_comm]; exact e, a2, a1⟩
  · exact ⟨e, a1, a2⟩

/-! ### From the bounds to `MajTiltRay` -/

/-- One piece value as an auxiliary-loop multiple of a parametric value with the momenta of
`QED.GradedProof.RPi4.maj_piece_ray`. -/
theorem maj_fVal5_eq (m₀ : ℝ) (Ms : Fin 5 → ℝ) (b : Fin 5 → Bool)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (k : Fin 4 → ℝ) (i j : Fin 4) :
    fVal5 m₀ Ms b N k i j = (auxLimit m₀)⁻¹ * pvOf (fun ℓ => N k (ℓ 0) i j) (majKAlpha b)
      (fun l => majKCs b l • k) ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] := by
  have e : (fun l => (kinds5 b l).mom k k) = fun l => majKCs b l • k :=
    funext fun l => maj_mom_kinds5 b k l
  simp only [fVal5, majKAlpha, e]

theorem maj_tiltRay_of_bounds {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} {w : ℝ → ℂ} (a : ℂ)
    (hW : ∀ s : ℝ, 1 ≤ s → W (majRayVec s) 2 3 = a * w s)
    (h : ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ‖w s‖ ≤ C * s ∧
      ∀ s' : ℝ, 1 ≤ s' → s' ≤ s → ‖w s - w s'‖ ≤ C * (s - s')) : MajTiltRay W := by
  obtain ⟨C, hC⟩ := h
  refine ⟨‖a‖ * C, fun s hs => ⟨?_, fun s' hs' hss => ?_⟩⟩
  · rw [hW s hs, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC s hs).1 (norm_nonneg _)
  · rw [hW s hs, hW s' hs', ← mul_sub, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hC s hs).2 s' hs' hss) (norm_nonneg _)

theorem maj_inv_smul_zero (r : ℝ) (hr : r ≠ 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    r • (r⁻¹ • ℓ) 0 = ℓ 0 := by
  rw [Pi.smul_apply, smul_smul, mul_inv_cancel₀ hr, one_smul]

/-! ### The three kinds of pieces -/

section Pieces

variable (sw : Bool) (dm : ℝ) {bx bY : Bool} (h : bx ≠ bY) {m₀ : ℝ} (hm₀ : 0 < m₀)
include h hm₀

/-- **`MajTiltRay` of a piece `eVal0`** (`b₀ = bx`, `b₄ = bY`). -/
theorem maj_tiltRay_eVal0 {m0 m1 m2 m3 m4 : ℝ}
    (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4) (c1 c2 c3 : Bool) :
    MajTiltRay (eVal0 m₀ sw 0 dm bx bY m0 m1 m2 m3 m4 bx c1 c2 c3 bY) := by
  set v := majRayVec 1 with hv
  obtain ⟨Q₄, hQ₄⟩ := (isLoopPoly_tnS0 sw 0 dm bx bY v 2 3).exists_loopQuartic
  set Q₂ : LoopQuartic := ⟨0, 0, 0, 0, 0⟩ with hQ₂d
  have hQ₂ : ∀ ℓ, Q₂.eval ℓ = 0 := fun ℓ => by
    simp [hQ₂d, LoopQuartic.eval, LoopQuartic.evalC]
  set T : ℂ := (gAF sw 2 3 * (Dirac.slash v * (gBF sw 2 3 * Dirac.slash v))).trace
  obtain ⟨hmA, hmB, hmC, hmD, hmE⟩ := hm
  have hb : (![bx, c1, c2, c3, bY] : Fin 5 → Bool) 0 ≠ ![bx, c1, c2, c3, bY] 4 := by simpa using h
  refine maj_tiltRay_of_bounds (auxLimit m₀)⁻¹ (fun s _ => maj_fVal5_eq _ _ _ _ _ _ _) ?_
  refine maj_piece_ray (b := ![bx, c1, c2, c3, bY]) (Ms := ![m0, m1, m2, m3, m4])
    (N := fun k ℓ => tnS sw 0 0 dm bx bY k (ℓ 0) 2 3) (Q₄ := Q₄) (Q₂ := Q₂)
    (K := 2 * |dm| * ‖T‖) hb hm₀ (fun i => by fin_cases i <;> simp [hmA, hmB, hmC, hmD, hmE])
    (fun ℓ => by simp only [hQ₄, Matrix.cons_val_zero]) (fun ℓ => by simp only [hQ₂]) rfl
    (fun r hr ℓ => ?_) (fun σ h0 h1 => ?_)
  · rw [hQ₄, hQ₂, mul_zero, add_zero]
    conv_lhs => rw [← maj_inv_smul_zero r hr.ne' ℓ]
    exact maj_tnS0_smul sw 0 dm bx bY r v _ 2 3
  · rw [hQ₄]
    simp only [Matrix.cons_val_zero]
    rw [← nT0_gAB, maj_zk_shift, maj_zk_shift, maj_nT0_val _ _ _ _ _ maj_dot_v, maj_trace_gAB]
    obtain ⟨e1, -, e3⟩ := maj_shift_abs h h0 h1
    set α := if bx then 1 - σ else -σ
    set β := if bY then 1 - σ else -σ
    have e : (2 : ℂ) * dm * β ^ 4 * 0 - 2 * dm * α * β ^ 3 * T =
        ((-2 * dm * (α * β) * β ^ 2 : ℝ) : ℂ) * T := by push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_neg, abs_two, e1, abs_pow]
    have hβ2 : |β| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) e3
    have hσ : 0 ≤ σ * (1 - σ) := mul_nonneg h0 (by linarith)
    calc 2 * |dm| * (σ * (1 - σ)) * |β| ^ 2 * ‖T‖ ≤ 2 * |dm| * (σ * (1 - σ)) * 1 * ‖T‖ := by
          gcongr
      _ = 2 * |dm| * ‖T‖ * (σ * (1 - σ)) := by ring

/-- **`MajTiltRay` of a piece `eVal2`** (`b₀ = bx`, `b₄ = bY`). -/
theorem maj_tiltRay_eVal2 {m0 m1 m2 m3 : ℝ} (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c1 c2 : Bool) :
    MajTiltRay (eVal2 m₀ sw 0 dm bx bY m0 m1 m2 m3 bx c1 c2 bY) := by
  set v := majRayVec 1 with hv
  have hP := isLoopPoly_tnS1 sw 0 dm bx bY v 2 3
  obtain ⟨Q₄, hQ₄⟩ := ((hP.mul ((isLoopAffine_zk v bx).isLoopPoly_propDenom 0 0)).mono
    (by norm_num)).exists_loopQuartic
  obtain ⟨Q₂, hq₂, hQ₂⟩ := SE2.IsLoopPoly.exists_loopQuartic_cubic
    ((hP.mul (IsLoopPoly.const (n := 0) ((m0 : ℂ) ^ 2))).mono (by norm_num))
  set T : ℂ := (gAF sw 2 3 * (Dirac.slash v * (gBF sw 2 3 * Dirac.slash v))).trace
  obtain ⟨hmA, hmB, hmC, hmD⟩ := hm
  have hb : (![bx, bx, c1, c2, bY] : Fin 5 → Bool) 0 ≠ ![bx, bx, c1, c2, bY] 4 := by simpa using h
  refine maj_tiltRay_of_bounds (auxLimit m₀)⁻¹ (fun s _ => maj_fVal5_eq _ _ _ _ _ _ _) ?_
  refine maj_piece_ray (b := ![bx, bx, c1, c2, bY]) (Ms := ![m0, m0, m1, m2, m3])
    (N := fun k ℓ => padN (tnS sw 1 0 dm bx bY) m0 bx k (ℓ 0) 2 3) (Q₄ := Q₄) (Q₂ := Q₂)
    (K := 2 * |dm| * ‖T‖) hb hm₀ (fun i => by fin_cases i <;> simp [hmA, hmB, hmC, hmD])
    (fun ℓ => by simp only [hQ₄, Matrix.cons_val_zero])
    (fun ℓ => by simp only [hQ₂, Matrix.cons_val_zero]) hq₂ (fun r hr ℓ => ?_)
    (fun σ h0 h1 => ?_)
  · rw [hQ₄, hQ₂]
    conv_lhs => rw [← maj_inv_smul_zero r hr.ne' ℓ]
    exact maj_padN_tnS1_smul sw dm m0 bx bY r v _
  · rw [hQ₄]
    simp only [Matrix.cons_val_zero]
    rw [← nT1_gAB, maj_zk_shift, maj_zk_shift, maj_nT1_val _ _ _ _ _ maj_dot_v, maj_trace_gAB,
      show propDenom 0 0 = v0 from rfl, maj_v0_val _ maj_dot_v]
    obtain ⟨e1, e2, -⟩ := maj_shift_abs h h0 h1
    set α := if bx then 1 - σ else -σ
    set β := if bY then 1 - σ else -σ
    have e : (-3 * dm * β ^ 2 * 0 + 2 * dm * α * β * T) * (α : ℂ) ^ 2 =
        ((2 * dm * (α * β) * α ^ 2 : ℝ) : ℂ) * T := by push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_two, e1, abs_pow]
    have hα2 : |α| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) e2
    have hσ : 0 ≤ σ * (1 - σ) := mul_nonneg h0 (by linarith)
    calc 2 * |dm| * (σ * (1 - σ)) * |α| ^ 2 * ‖T‖ ≤ 2 * |dm| * (σ * (1 - σ)) * 1 * ‖T‖ := by
          gcongr
      _ = 2 * |dm| * ‖T‖ * (σ * (1 - σ)) := by ring

end Pieces

/-- The parametric value of the zero numerator vanishes. -/
theorem maj_pvOf_zero {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) : pvOf (fun _ => 0) α p M = 0 := by
  have hQ : (⟨0, 0, 0, 0, 0⟩ : LoopQuartic).eval = fun _ => 0 := by
    funext ℓ
    simp [LoopQuartic.eval, LoopQuartic.evalC]
  rw [pvOf_eq hQ]
  simp [paramIntegrand, LoopQuartic.eval, LoopQuartic.evalC, LoopQuartic.contractTwo,
    LoopQuartic.hess, LoopQuartic.quartSym, LoopQuartic.contractFour]

/-- **`MajTiltRay` of a piece `eVal4`**: its `²³` entry vanishes. -/
theorem maj_tiltRay_eVal4 (m₀ : ℝ) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (m0 m1 m2 : ℝ)
    (c0 c1 c2 : Bool) : MajTiltRay (eVal4 m₀ sw d₂ dm bx bY m0 m1 m2 c0 c1 c2) := by
  refine MajTiltRay.zero.congr fun s _ => ?_
  have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => padN (padN (tnS sw 2 d₂ dm bx bY) m0 c0) m0 c0
      (majRayVec s) (ℓ 0) 2 3) = fun _ => 0 := by
    funext ℓ
    simp only [padN]
    rw [← nT2_gAB, nT2, insT4, maj_trace_gAB]
    ring
  simp only [eVal4, fVal5, e, maj_pvOf_zero, mul_zero]

end QED.GradedProof.RPi4

end
