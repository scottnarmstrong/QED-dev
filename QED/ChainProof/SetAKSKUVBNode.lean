/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVBAnti
public import QED.ChainProof.SetAKSKUVAExp

/-!
# Set (a), stage D: moment bounds and the node interchange for the `VB` class

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral of the `VB` class). In the
coordinates `(ρ, β)` of the inner vertex (`SetAKSKUVBCov`) the `VB` slope is
`b = b₀ + u/ρ`, `b₀ = ρ A(β)/(1 - ρ) > 0`, and the photon-line range is `0 < Y ≤ 1`. The
moments `ksDJ1`, `ksDJ2` are nonnegative, bounded by `A⁻¹`, `A⁻²` and antitone in `b`, so at
a fixed node `(ρ, β)` the `VB` integrand is bounded on `(0, Λ] × (0, 1)` and the photon-mass
integral is taken node by node with the antiderivative `ksUPsiB`.

Main results:

* `ksU_J1_nonneg`, `ksU_J1_le`, `ksU_J2_le`, `ksU_J1_anti`, `ksU_J1_le_ref`;
* `ksU_ksDbB_ptB`, `ksU_ksDbB_zero_ptB`: the slope in the coordinates `(ρ, β)`;
* `ksU_abs_ksUYBg_le`: `|ksUYBg| ≤ ksUYBg` with absolute coefficients;
* **`ksU_node_swap_B`**: at a fixed node the photon-mass and `w` integrals commute, and the
  photon-mass integral is the node difference `ksUDB`.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

/-! ### The moments -/

section Moments

variable {A b Y : ℝ}

theorem ksU_measurable_J {γ : Type*} [MeasurableSpace γ] {A b Y : γ → ℝ} (hA : Measurable A)
    (hb : Measurable b) (hY : Measurable Y) (p : ℕ) :
    Measurable (fun z => ksDJ1 (A z) (b z) (Y z) p) ∧
      Measurable (fun z => ksDJ2 (A z) (b z) (Y z) p) := by
  induction p with
  | zero => simp only [ksDJ1, ksDJ2]; exact ⟨by fun_prop, by fun_prop⟩
  | succ p ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [ksDJ1, ksDJ2]
    exact ⟨by fun_prop, by fun_prop⟩

theorem ksU_J_integrand_nonneg (hA : 0 < A) (hb : 0 < b) (_hY : 0 ≤ Y) (p k : ℕ) :
    ∀ v ∈ Icc (0 : ℝ) Y, 0 ≤ v ^ p / (A + b * v) ^ k := fun v hv => by
  have := mul_nonneg hb.le hv.1
  have : 0 < A + b * v := by linarith
  have := hv.1
  positivity

theorem ksU_J1_nonneg (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) (p : ℕ) : 0 ≤ ksDJ1 A b Y p := by
  rw [← ksD_integral_J1 hA hb hY]
  refine intervalIntegral.integral_nonneg hY fun v hv => ?_
  simpa using ksU_J_integrand_nonneg hA hb hY p 1 v hv

theorem ksU_J2_nonneg (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) (p : ℕ) : 0 ≤ ksDJ2 A b Y p := by
  rw [← ksD_integral_J2 hA hb hY]
  exact intervalIntegral.integral_nonneg hY fun v hv => ksU_J_integrand_nonneg hA hb hY p 2 v hv

theorem ksU_J1_le (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) (hY1 : Y ≤ 1) (p : ℕ) :
    ksDJ1 A b Y p ≤ A⁻¹ := by
  rw [← ksD_integral_J1 hA hb hY]
  have h := intervalIntegral.integral_mono_on hY
    (by simpa using ksD_intervalIntegrable_J hA hb hY p 1)
    (intervalIntegrable_const (c := A⁻¹)) fun v hv => by
      have hv0 := hv.1
      have hv1 : v ≤ 1 := hv.2.trans hY1
      have hD : A ≤ A + b * v := by nlinarith
      rw [div_le_iff₀ (by linarith)]
      calc v ^ p ≤ 1 := pow_le_one₀ hv0 hv1
        _ = A⁻¹ * A := (inv_mul_cancel₀ hA.ne').symm
        _ ≤ A⁻¹ * (A + b * v) := by gcongr
  refine h.trans ?_
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have := inv_pos.2 hA
  nlinarith

theorem ksU_J2_le (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) (hY1 : Y ≤ 1) (p : ℕ) :
    ksDJ2 A b Y p ≤ (A ^ 2)⁻¹ := by
  rw [← ksD_integral_J2 hA hb hY]
  have h := intervalIntegral.integral_mono_on hY (ksD_intervalIntegrable_J hA hb hY p 2)
    (intervalIntegrable_const (c := (A ^ 2)⁻¹)) fun v hv => by
      have hv0 := hv.1
      have hv1 : v ≤ 1 := hv.2.trans hY1
      have hD : A ≤ A + b * v := by nlinarith
      rw [div_le_iff₀ (by positivity)]
      calc v ^ p ≤ 1 := pow_le_one₀ hv0 hv1
        _ = (A ^ 2)⁻¹ * A ^ 2 := (inv_mul_cancel₀ (by positivity)).symm
        _ ≤ (A ^ 2)⁻¹ * (A + b * v) ^ 2 := by gcongr
  refine h.trans ?_
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have : 0 < (A ^ 2)⁻¹ := by positivity
  nlinarith

theorem ksU_J1_anti {b₀ B : ℝ} (hA : 0 < A) (hb₀ : 0 < b₀) (hB : b₀ ≤ B) (hY : 0 ≤ Y)
    (p : ℕ) : ksDJ1 A B Y p ≤ ksDJ1 A b₀ Y p := by
  have hB0 : 0 < B := hb₀.trans_le hB
  rw [← ksD_integral_J1 hA hb₀ hY, ← ksD_integral_J1 hA hB0 hY]
  refine intervalIntegral.integral_mono_on hY
    (by simpa using ksD_intervalIntegrable_J hA hB0 hY p 1)
    (by simpa using ksD_intervalIntegrable_J hA hb₀ hY p 1) fun v hv => ?_
  have hv0 := hv.1
  have h1 : 0 < A + b₀ * v := by nlinarith
  have := pow_nonneg hv0 p
  exact div_le_div_of_nonneg_left (by positivity) h1 (by nlinarith)

/-- Comparison with a reference moment: `J1ₚ(A, b, Y) ≤ J1₀(kA, b₁, 1)` for `kA ≤ A`,
`b₁ ≤ b`, `Y ≤ 1`. -/
theorem ksU_J1_le_ref {kA b₁ : ℝ} (hkA : 0 < kA) (hkAA : kA ≤ A) (hb₁ : 0 < b₁) (hb : b₁ ≤ b)
    (hY : 0 ≤ Y) (hY1 : Y ≤ 1) (p : ℕ) : ksDJ1 A b Y p ≤ ksDJ1 kA b₁ 1 0 := by
  have hA : 0 < A := hkA.trans_le hkAA
  have hb0 : 0 < b := hb₁.trans_le hb
  rw [← ksD_integral_J1 hA hb0 hY, ← ksD_integral_J1 hkA hb₁ zero_le_one]
  have I1 := ksD_intervalIntegrable_J hkA hb₁ zero_le_one 0 1
  have I2 := ksD_intervalIntegrable_J hA hb0 hY p 1
  have I3 := ksD_intervalIntegrable_J hkA hb₁ hY 0 1
  simp only [pow_one] at I1 I2 I3
  refine (intervalIntegral.integral_mono_on hY I2 I3 fun v hv => ?_).trans ?_
  · have hv0 := hv.1
    have hv1 : v ≤ 1 := hv.2.trans hY1
    have h1 : 0 < kA + b₁ * v := by nlinarith
    rw [pow_zero, div_le_div_iff₀ (by nlinarith) h1, one_mul]
    have := pow_le_one₀ hv0 hv1 (n := p)
    have : kA + b₁ * v ≤ A + b * v := by nlinarith
    nlinarith [pow_nonneg hv0 p]
  · refine intervalIntegral.integral_mono_interval le_rfl hY hY1 ?_ I1
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun v hv => ?_)
    have := mul_nonneg hb₁.le hv.1.le
    have : 0 < kA + b₁ * v := by linarith
    positivity

/-- The `VB` integrand with absolute coefficients. -/
noncomputable def ksUYBa (A b Y τ c : ℝ) (E H : Fin 3 → ℝ) : ℝ :=
  ksUYBg A b Y τ |c| (fun i => |E i|) (fun i => |H i|)

theorem ksU_abs_ksUYBg_le {τ c : ℝ} {E H : Fin 3 → ℝ} (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y)
    (hτ : 0 < τ) : |ksUYBg A b Y τ c E H| ≤ ksUYBa A b Y τ c E H := by
  have j1 := ksU_J1_nonneg hA hb hY
  have j2 := ksU_J2_nonneg hA hb hY
  have hτ' : 0 < (2 * τ)⁻¹ := by positivity
  simp only [ksUYBa, ksUYBg]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul, abs_of_pos (inv_pos.2 hτ)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hτ).le
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
      rw [abs_mul, abs_of_nonneg (j2 _)]
  · rw [abs_mul, abs_of_pos hτ']
    refine mul_le_mul_of_nonneg_left ?_ hτ'.le
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
      rw [abs_mul, abs_of_nonneg (j1 _)]
  · rw [abs_mul, abs_of_nonneg (j1 _)]

theorem ksU_ksUYBa_nonneg {τ c : ℝ} {E H : Fin 3 → ℝ} (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y)
    (hτ : 0 < τ) : 0 ≤ ksUYBa A b Y τ c E H := by
  have j1 := ksU_J1_nonneg hA hb hY
  have j2 := ksU_J2_nonneg hA hb hY
  simp only [ksUYBa, ksUYBg]
  have := inv_pos.2 hτ
  have : 0 < (2 * τ)⁻¹ := by positivity
  have := j1 0; have := j1 1; have := j1 2; have := j1 3
  have := j2 1; have := j2 2; have := j2 3
  positivity

theorem ksU_ksUYBa_le {kA τ c : ℝ} {E H : Fin 3 → ℝ} (hkA : 0 < kA) (hkAA : kA ≤ A) (hb : 0 < b)
    (hY : 0 ≤ Y) (hY1 : Y ≤ 1) (hτ : 0 < τ) :
    ksUYBa A b Y τ c E H ≤ (τ⁻¹ + 1) * (|E 0| + |E 1| + |E 2| + |H 0| + |H 1| + |H 2| + |c|) *
      (1 + kA⁻¹) ^ 2 := by
  have hA : 0 < A := hkA.trans_le hkAA
  have hAi : A⁻¹ ≤ kA⁻¹ := inv_anti₀ hkA hkAA
  have hki : 0 < kA⁻¹ := inv_pos.2 hkA
  set Q := (1 + kA⁻¹) ^ 2 with hQ
  have q1 : ∀ p, ksDJ1 A b Y p ≤ Q := fun p => by
    have := ksU_J1_le hA hb hY hY1 p
    nlinarith
  have q2 : ∀ p, ksDJ2 A b Y p ≤ Q := fun p => by
    have := ksU_J2_le hA hb hY hY1 p
    have : (A ^ 2)⁻¹ = A⁻¹ ^ 2 := by rw [inv_pow]
    have : A⁻¹ ^ 2 ≤ kA⁻¹ ^ 2 := pow_le_pow_left₀ (inv_pos.2 hA).le hAi 2
    nlinarith
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  have h2τ : (2 * τ)⁻¹ ≤ τ⁻¹ := inv_anti₀ hτ (by linarith)
  have h2τ0 : 0 < (2 * τ)⁻¹ := by positivity
  simp only [ksUYBa, ksUYBg]
  have e1 : τ⁻¹ * (|E 0| * ksDJ2 A b Y 1 + |E 1| * ksDJ2 A b Y 2 + |E 2| * ksDJ2 A b Y 3) ≤
      τ⁻¹ * ((|E 0| + |E 1| + |E 2|) * Q) := by
    refine mul_le_mul_of_nonneg_left ?_ hτi.le
    nlinarith [q2 1, q2 2, q2 3, abs_nonneg (E 0), abs_nonneg (E 1), abs_nonneg (E 2),
      mul_le_mul_of_nonneg_left (q2 1) (abs_nonneg (E 0)),
      mul_le_mul_of_nonneg_left (q2 2) (abs_nonneg (E 1)),
      mul_le_mul_of_nonneg_left (q2 3) (abs_nonneg (E 2))]
  have e2 : (2 * τ)⁻¹ * (|H 0| * ksDJ1 A b Y 1 + |H 1| * ksDJ1 A b Y 2 + |H 2| * ksDJ1 A b Y 3)
      ≤ τ⁻¹ * ((|H 0| + |H 1| + |H 2|) * Q) := by
    have hS : |H 0| * ksDJ1 A b Y 1 + |H 1| * ksDJ1 A b Y 2 + |H 2| * ksDJ1 A b Y 3 ≤
        (|H 0| + |H 1| + |H 2|) * Q := by
      nlinarith [mul_le_mul_of_nonneg_left (q1 1) (abs_nonneg (H 0)),
        mul_le_mul_of_nonneg_left (q1 2) (abs_nonneg (H 1)),
        mul_le_mul_of_nonneg_left (q1 3) (abs_nonneg (H 2))]
    have h0 : 0 ≤ |H 0| * ksDJ1 A b Y 1 + |H 1| * ksDJ1 A b Y 2 + |H 2| * ksDJ1 A b Y 3 := by
      have := ksU_J1_nonneg hA hb hY 1; have := ksU_J1_nonneg hA hb hY 2
      have := ksU_J1_nonneg hA hb hY 3
      positivity
    calc _ ≤ (2 * τ)⁻¹ * ((|H 0| + |H 1| + |H 2|) * Q) := mul_le_mul_of_nonneg_left hS h2τ0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h2τ (by positivity)
  have e3 : |c| * ksDJ1 A b Y 0 ≤ |c| * Q := mul_le_mul_of_nonneg_left (q1 0) (abs_nonneg c)
  have hQ0 : 0 ≤ Q := by positivity
  nlinarith [abs_nonneg (E 0), abs_nonneg (E 1), abs_nonneg (E 2), abs_nonneg (H 0),
    abs_nonneg (H 1), abs_nonneg (H 2), abs_nonneg c, mul_nonneg hτi.le hQ0]

end Moments

/-! ### The node data in the coordinates `(ρ, β)` -/

theorem ksU_ksUPtB_two (ρ β : ℝ) : 1 - ksUPtB ρ β 2 = ρ := by simp [ksUPtB]

theorem ksU_ksDbB_ptB {M u s ρ β : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    ksDbB M u (ksUPtB ρ β) s = ksDbB M 0 (ksUPtB ρ β) s + u / ρ := by
  have h2 : ksUPtB ρ β 2 ≠ 0 := by simp [ksUPtB]; linarith [hρ.2]
  have h2' : 1 - ksUPtB ρ β 2 ≠ 0 := by rw [ksU_ksUPtB_two]; exact hρ.1.ne'
  rw [ksD_ksDbB_eq M u _ s (ksU_ksUPtB_sum ρ β) h2 h2',
    ksD_ksDbB_eq M 0 _ s (ksU_ksUPtB_sum ρ β) h2 h2', ksU_ksUPtB_two]
  ring

theorem ksU_ksDbB_zero_ptB {M s ρ β : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    ksDbB M 0 (ksUPtB ρ β) s = ρ * ksDA M s β / (1 - ρ) := by
  have h2 : ksUPtB ρ β 2 ≠ 0 := by simp [ksUPtB]; linarith [hρ.2]
  have h2' : 1 - ksUPtB ρ β 2 ≠ 0 := by rw [ksU_ksUPtB_two]; exact hρ.1.ne'
  rw [ksD_ksDbB_eq M 0 _ s (ksU_ksUPtB_sum ρ β) h2 h2', ksU_ksUPtB_two]
  have h1 : 1 - ρ ≠ 0 := by linarith [hρ.2]
  have h0 : ρ ≠ 0 := hρ.1.ne'
  simp only [ksUPtB, ksDA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

theorem ksU_ksDbB_zero_pos {M s ρ β : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1) : 0 < ksDbB M 0 (ksUPtB ρ β) s := by
  rw [ksU_ksDbB_zero_ptB hρ]
  have := ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hβ)
  have := hρ.1
  have : 0 < 1 - ρ := by linarith [hρ.2]
  positivity

theorem ksU_ksDbB_ptB_pos {M s ρ β u : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) :
    0 < ksDbB M u (ksUPtB ρ β) s := by
  rw [ksU_ksDbB_ptB hρ]
  have := ksU_ksDbB_zero_pos hM hs hρ hβ
  have := div_nonneg hu hρ.1.le
  linarith

theorem ksU_ksUPtB_beta' {ρ β : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    ksUPtB ρ β 1 / (1 - ksUPtB ρ β 2) = β := ksU_ksUPtB_beta hρ.1.ne'

theorem ksU_ksDYmax_pos {β w : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 < ksDYmax β w :=
  lt_min (div_pos hw.1 hβ.1) (div_pos (by linarith [hw.2]) (by linarith [hβ.2]))

theorem ksU_ksDYmax_le_one {β w : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) : ksDYmax β w ≤ 1 := by
  rcases le_or_gt w β with h | h
  · exact (min_le_left _ _).trans ((div_le_one hβ.1).2 h)
  · exact (min_le_right _ _).trans ((div_le_one (by linarith [hβ.2])).2 (by linarith))

/-! ### Coefficient bounds -/

theorem ksU_abs_ksDcv_le (a₀ a₁ a₂ c₀ c₁ : ℝ) (i : Fin 3) :
    |ksDcv a₀ a₁ a₂ c₀ c₁ i| ≤ 2 * (|a₀| + |a₁| + |a₂|) * (1 + |c₀| + |c₁|) ^ 2 := by
  have hc0 := abs_nonneg c₀
  have hc1 := abs_nonneg c₁
  have h0 := abs_nonneg a₀
  have h1 := abs_nonneg a₁
  have h2 := abs_nonneg a₂
  have hT : 1 ≤ (1 + |c₀| + |c₁|) ^ 2 := by nlinarith
  fin_cases i <;> simp only [ksDcv, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk]
  · calc |a₀ + a₁ * c₀ + a₂ * c₀ ^ 2| ≤ |a₀ + a₁ * c₀| + |a₂ * c₀ ^ 2| := abs_add_le _ _
      _ ≤ |a₀| + |a₁ * c₀| + |a₂ * c₀ ^ 2| := by linarith [abs_add_le a₀ (a₁ * c₀)]
      _ = |a₀| + |a₁| * |c₀| + |a₂| * |c₀| ^ 2 := by rw [abs_mul, abs_mul, abs_pow]
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : |c₀| ≤ (1 + |c₀| + |c₁|) ^ 2) h1,
          mul_le_mul_of_nonneg_left (by nlinarith : |c₀| ^ 2 ≤ (1 + |c₀| + |c₁|) ^ 2) h2,
          mul_le_mul_of_nonneg_left hT h0]
  · calc |a₁ * c₁ + 2 * a₂ * c₀ * c₁| ≤ |a₁ * c₁| + |2 * a₂ * c₀ * c₁| := abs_add_le _ _
      _ = |a₁| * |c₁| + 2 * |a₂| * |c₀| * |c₁| := by simp only [abs_mul, abs_two]
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : |c₁| ≤ (1 + |c₀| + |c₁|) ^ 2) h1,
          mul_le_mul_of_nonneg_left (by nlinarith : |c₀| * |c₁| ≤ (1 + |c₀| + |c₁|) ^ 2) h2,
          mul_le_mul_of_nonneg_left hT h0]
  · rw [abs_mul, abs_pow]
    nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : |c₁| ^ 2 ≤ (1 + |c₀| + |c₁|) ^ 2) h2,
      mul_le_mul_of_nonneg_left hT h0, mul_le_mul_of_nonneg_left hT h1]

/-- In the coordinates `(ρ, β)` the photon-line coordinate `σ₁` is constant: `c₁ = 0`. -/
theorem ksU_ksDc1_ptB {ρ β : ℝ} (hρ : ρ ≠ 0) : ksDc1 (ksUPtB ρ β) = 0 := by
  have e2 := ksU_ksUPtB_two ρ β
  simp only [ksDc1, e2]
  simp only [ksUPtB, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

theorem ksU_c_bounds {ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) :
    |ksDc0 (ksUPtB ρ β) w| ≤ 1 ∧ |ksDc1 (ksUPtB ρ β)| ≤ 3 := by
  rw [ksU_ksDc1_ptB hρ.1.ne']
  obtain ⟨r0, r1⟩ := hρ
  obtain ⟨b0, b1⟩ := hβ
  obtain ⟨w0, w1⟩ := hw
  simp only [ksDc0, ksUPtB, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨?_, by norm_num⟩
  rw [abs_le]; constructor <;> nlinarith [mul_pos r0 b0, mul_pos r0 (sub_pos.2 b1),
    mul_pos (sub_pos.2 w1) w0, mul_pos (mul_pos r0 b0) (sub_pos.2 w1),
    mul_pos (mul_pos r0 (sub_pos.2 b1)) w0]

/-- The coefficient bound `|Eᵢ| + |Hᵢ| ≤ KB = 5600 M² + 8000`. -/
noncomputable def ksUKB (M : ℝ) : ℝ := 5600 * M ^ 2 + 8000

theorem ksU_coef_le {M ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    |ksDEc M (ksUPtB ρ β) w i| ≤ 5600 * M ^ 2 ∧ |ksDHc (ksUPtB ρ β) w i| ≤ 8000 := by
  obtain ⟨hc0, hc1⟩ := ksU_c_bounds hρ hβ hw
  have hT : (1 + |ksDc0 (ksUPtB ρ β) w| + |ksDc1 (ksUPtB ρ β)|) ^ 2 ≤ 25 := by
    have := abs_nonneg (ksDc0 (ksUPtB ρ β) w)
    have := abs_nonneg (ksDc1 (ksUPtB ρ β))
    nlinarith
  obtain ⟨w0, w1⟩ := hw
  have x2 : ksUPtB ρ β 2 = 1 - ρ := by simp [ksUPtB]
  have hx0 : 0 ≤ 1 - ρ := by linarith [hρ.2]
  have hx1 : 1 - ρ ≤ 1 := by linarith [hρ.1]
  have hM2 := sq_nonneg M
  constructor
  · refine (ksU_abs_ksDcv_le _ _ _ _ _ i).trans ?_
    have ha : |16 * M ^ 2 * (w ^ 2 - 3 * w + 1)| + |16 * M ^ 2 * (4 * w - 3)| + |16 * M ^ 2| ≤
        112 * M ^ 2 := by
      have e1 : |16 * M ^ 2 * (w ^ 2 - 3 * w + 1)| = 16 * M ^ 2 * |w ^ 2 - 3 * w + 1| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * M ^ 2)]
      have e2 : |16 * M ^ 2 * (4 * w - 3)| = 16 * M ^ 2 * |4 * w - 3| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * M ^ 2)]
      rw [e1, e2, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * M ^ 2)]
      have : |w ^ 2 - 3 * w + 1| ≤ 3 := by rw [abs_le]; constructor <;> nlinarith
      have : |4 * w - 3| ≤ 3 := by rw [abs_le]; constructor <;> nlinarith
      nlinarith
    have := mul_le_mul ha hT (by positivity) (by positivity)
    nlinarith
  · refine (ksU_abs_ksDcv_le _ _ _ _ _ i).trans ?_
    rw [x2]
    have ha : |-32 * (1 - ρ) * w + 32 * (1 - ρ) ^ 2 * w * (w - 1)| +
        |-32 + 32 * (1 - ρ) * (2 * w - 1)| + |(32 : ℝ)| ≤ 160 := by
      have : |-32 * (1 - ρ) * w + 32 * (1 - ρ) ^ 2 * w * (w - 1)| ≤ 64 := by
        rw [abs_le]; constructor <;> nlinarith [mul_nonneg hx0 w0.le,
          mul_nonneg (mul_nonneg hx0 hx0) (mul_nonneg w0.le (by linarith : (0 : ℝ) ≤ 1 - w))]
      have : |-32 + 32 * (1 - ρ) * (2 * w - 1)| ≤ 64 := by
        rw [abs_le]; constructor <;> nlinarith [mul_nonneg hx0 w0.le,
          mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 1 - w)]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 32)]
      linarith
    have := mul_le_mul ha hT (by positivity) (by positivity)
    nlinarith

end QED.ChainProof.SetAKS

end
