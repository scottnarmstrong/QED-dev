/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBZero
public import QED.TwoLoop.VPHalfAtGenPow
public import QED.ChainProof.SetCRegDispCtLoBGen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The power-weighted Pauli values of the mass part

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), layer 5. The
engine limits with the absorbed weight `ℓ^(2j)` (the `k²` absorption of layer 3) are defined by
the recursion `X (j+1) Ms = X j (tail Ms) - M₀² X j Ms`; here they are evaluated.

* `undKernJ`: the undoubled kernel with weight `K^j`, `6 y K^j g` in the radial variable;
* `dblKernJ`: the doubled kernel with weight `K^j`,
  `6 x_d y³/(1-y) (K^j g Σ_i (K + M_i²)⁻¹ - j K^(j-1) g)`, `g = ∏_i (K + M_i²)⁻¹`. The second
  term (the `t`-derivative of `(K+t)^j` in `-∂_t [(K+t)^j ∏_i (K+t+M_i²)⁻¹]`) is forced by the
  recursion (`dblKernJ_succ`);
* uniform bounds for `j ≤ k + 2` and masses `≥ M₀ > 0`, integrability;
* **`powLimit_undChain_eq`**, **`dblPowLimit_pauliChain_eq`**: for `j ≤ k` and positive masses
  (repeated allowed) the power-weighted limits equal `undValJ`, `dblValJ`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtGen

/-! ### The kernels -/

/-- The undoubled kernel with the weight `K^j`: `6 y kC^j (1-y)^(k+2-j)/∏ Δ_i`. -/
noncomputable def undKernJ (m s : ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (z : ℝ × ℝ) : ℝ :=
  6 * z.2 * kC m s z ^ j * (1 - z.2) ^ (k + 2 - j) / ∏ i, kDen m (Ms i) s z

/-- First part of the doubled kernel with weight `K^j`. -/
noncomputable def dblKernA (m s : ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (d : Fin 2)
    (z : ℝ × ℝ) : ℝ :=
  6 * dblLineWt d z.1 * z.2 ^ 3 * (1 - z.2) ^ (k + 2 - j) * kC m s z ^ j *
    (∑ i, (kDen m (Ms i) s z)⁻¹) / ∏ i, kDen m (Ms i) s z

/-- Second part of the doubled kernel with weight `K^j` (the derivative of `K^j`). -/
noncomputable def dblKernB (m s : ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (d : Fin 2)
    (z : ℝ × ℝ) : ℝ :=
  6 * dblLineWt d z.1 * z.2 ^ 3 * (1 - z.2) ^ (k + 2 - j) * ((j : ℝ) * kC m s z ^ (j - 1)) /
    ∏ i, kDen m (Ms i) s z

/-- The doubled kernel with weight `K^j`: in the radial variable it is
`6 x_d y³/(1-y) (K^j g Σ_i (K + M_i²)⁻¹ - j K^(j-1) g)`, `g = ∏_i (K + M_i²)⁻¹`. -/
noncomputable def dblKernJ (m s : ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (d : Fin 2)
    (z : ℝ × ℝ) : ℝ :=
  dblKernA m s j Ms d z - dblKernB m s j Ms d z

theorem undKernJ_zero (m s : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    undKernJ m s 0 Ms = undKern m s Ms := by
  funext z
  simp [undKernJ, undKern]

theorem dblKernJ_zero (m s : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (d : Fin 2) :
    dblKernJ m s 0 Ms d = dblKern m s Ms d := by
  funext z
  simp only [dblKernJ, dblKernA, dblKernB, dblKern, Nat.sub_zero, pow_zero, CharP.cast_eq_zero,
    zero_mul, mul_zero, zero_div, sub_zero, mul_one]
  rw [pow_succ (1 - z.2) (k + 1)]
  ring

/-! ### The absorption recursion -/

theorem undKernJ_succ (m s : ℝ) (j : ℕ) {k : ℕ} (hj : j ≤ k) (Ms : Fin (k + 1 + 2) → ℝ)
    {z : ℝ × ℝ} (hD : ∀ i, kDen m (Ms i) s z ≠ 0) :
    undKernJ m s (j + 1) Ms z =
      undKernJ m s j (Fin.tail Ms) z - Ms 0 ^ 2 * undKernJ m s j Ms z := by
  have hP : ∏ i, kDen m (Ms i) s z = kDen m (Ms 0) s z * ∏ i, kDen m (Fin.tail Ms i) s z := by
    rw [Fin.prod_univ_succ]
    rfl
  have h0 := hD 0
  have hR : ∏ i, kDen m (Fin.tail Ms i) s z ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hD _
  have e1 : k + 1 + 2 - (j + 1) = k + 2 - j := by omega
  have e2 : k + 1 + 2 - j = k + 2 - j + 1 := by omega
  have hD0 : kDen m (Ms 0) s z = (1 - z.2) * Ms 0 ^ 2 + kC m s z := rfl
  unfold undKernJ
  rw [hP, e1, e2]
  rw [hD0] at h0 ⊢
  field_simp
  ring

theorem dblKernJ_succ (m s : ℝ) (j : ℕ) {k : ℕ} (hj : j ≤ k) (Ms : Fin (k + 1 + 2) → ℝ)
    (d : Fin 2) {z : ℝ × ℝ} (hD : ∀ i, kDen m (Ms i) s z ≠ 0) :
    dblKernJ m s (j + 1) Ms d z =
      dblKernJ m s j (Fin.tail Ms) d z - Ms 0 ^ 2 * dblKernJ m s j Ms d z := by
  have hP : ∏ i, kDen m (Ms i) s z = kDen m (Ms 0) s z * ∏ i, kDen m (Fin.tail Ms i) s z := by
    rw [Fin.prod_univ_succ]
    rfl
  have hS : ∑ i, (kDen m (Ms i) s z)⁻¹ =
      (kDen m (Ms 0) s z)⁻¹ + ∑ i, (kDen m (Fin.tail Ms i) s z)⁻¹ := by
    rw [Fin.sum_univ_succ]
    rfl
  have h0 := hD 0
  have hR : ∏ i, kDen m (Fin.tail Ms i) s z ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hD _
  have e1 : k + 1 + 2 - (j + 1) = k + 2 - j := by omega
  have e2 : k + 1 + 2 - j = k + 2 - j + 1 := by omega
  have hD0 : kDen m (Ms 0) s z = (1 - z.2) * Ms 0 ^ 2 + kC m s z := rfl
  unfold dblKernJ dblKernA dblKernB
  rw [hP, hS, e1, e2]
  rw [hD0] at h0 ⊢
  generalize ∑ i, (kDen m (Fin.tail Ms i) s z)⁻¹ = S
  generalize ∏ i, kDen m (Fin.tail Ms i) s z = R at hR ⊢
  generalize kC m s z = c at h0 ⊢
  cases j with
  | zero =>
    simp only [Nat.cast_zero, zero_add, Nat.cast_one, pow_zero, zero_mul, Nat.sub_self,
      mul_one]
    field_simp
    ring
  | succ j =>
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

/-! ### Uniform bounds -/

theorem kC_nonneg {m s : ℝ} (hs : 0 ≤ s) {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    0 ≤ kC m s z := by
  obtain ⟨⟨hx0, hx1⟩, -, -⟩ := hz
  unfold kC
  have : 0 ≤ z.1 * (1 - z.1) * s := mul_nonneg (mul_nonneg hx0 (by linarith)) hs
  positivity

theorem kDen_ge_mu {m s M₀ M : ℝ} (hs : 0 ≤ s) (hM₀ : 0 ≤ M₀) (hM : M₀ ≤ M) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    min (M₀ ^ 2) 1 * ((1 - z.2) + kC m s z) ≤ kDen m M s z := by
  have hc := kC_nonneg (m := m) hs hz
  obtain ⟨-, -, hy1⟩ := hz
  have h1 := min_le_left (M₀ ^ 2) 1
  have h2 := min_le_right (M₀ ^ 2) 1
  have h3 : M₀ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hM₀ hM 2
  have hy : 0 ≤ 1 - z.2 := by linarith
  unfold kDen
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h3) hy, mul_le_mul_of_nonneg_left h2 hc]

theorem tSum_ge {m s : ℝ} (hs : 0 ≤ s) {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    3 / 4 * min (1 ^ 2) (m ^ 2) ≤ (1 - z.2) + kC m s z := by
  have := kDen_ge_min (m := m) hs zero_le_one le_rfl hz
  unfold kDen at this
  linarith

theorem pow_mul_pow_le_tSum {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) (a b : ℕ) :
    c ^ a * t ^ b ≤ (t + c) ^ (a + b) := by
  rw [pow_add]
  exact mul_le_mul (pow_le_pow_left₀ hc (by linarith) a) (pow_le_pow_left₀ ht (by linarith) b)
    (by positivity) (by positivity)

theorem prod_kDen_ge {m s M₀ : ℝ} (hs : 0 ≤ s) (hM₀ : 0 ≤ M₀) {k : ℕ} {Ms : Fin (k + 2) → ℝ}
    (hMs : ∀ i, M₀ ≤ Ms i) {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    (hT : 0 ≤ (1 - z.2) + kC m s z) :
    (min (M₀ ^ 2) 1 * ((1 - z.2) + kC m s z)) ^ (k + 2) ≤ ∏ i, kDen m (Ms i) s z := by
  have hμ : 0 ≤ min (M₀ ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
  calc _ = ∏ _i : Fin (k + 2), min (M₀ ^ 2) 1 * ((1 - z.2) + kC m s z) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => mul_nonneg hμ hT) fun i _ =>
        kDen_ge_mu hs hM₀ (hMs i) hz

section Bounds

variable {m s M₀ : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (hM₀ : 0 < M₀) {k : ℕ}
  {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) {z : ℝ × ℝ}
  (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
include hm hs hM₀ hMs hz

theorem abs_undKernJ_le {j : ℕ} (hj : j ≤ k + 2) :
    |undKernJ m s j Ms z| ≤ 6 / min (M₀ ^ 2) 1 ^ (k + 2) := by
  set μ := min (M₀ ^ 2) 1
  set T := (1 - z.2) + kC m s z
  have hμ : 0 < μ := lt_min (by positivity) one_pos
  have hc₁ : 0 < 3 / 4 * min (1 ^ 2 : ℝ) (m ^ 2) := by positivity
  have hT : 0 < T := hc₁.trans_le (tSum_ge hs hz)
  have hc := kC_nonneg (m := m) hs hz
  have hP := prod_kDen_ge hs hM₀.le hMs hz hT.le
  have hPp : 0 < ∏ i, kDen m (Ms i) s z := (pow_pos (mul_pos hμ hT) _).trans_le hP
  obtain ⟨-, hy0, hy1⟩ := hz
  have hy : 0 ≤ 1 - z.2 := by linarith
  have hN := pow_mul_pow_le_tSum hc hy j (k + 2 - j)
  rw [Nat.add_sub_cancel' hj] at hN
  unfold undKernJ
  rw [abs_of_nonneg (div_nonneg (by positivity) hPp.le), div_le_div_iff₀ hPp (by positivity)]
  calc 6 * z.2 * kC m s z ^ j * (1 - z.2) ^ (k + 2 - j) * μ ^ (k + 2)
      ≤ 6 * 1 * (kC m s z ^ j * (1 - z.2) ^ (k + 2 - j)) * μ ^ (k + 2) := by
        rw [mul_assoc (6 * z.2)]; gcongr
    _ ≤ 6 * 1 * T ^ (k + 2) * μ ^ (k + 2) := by gcongr
    _ = 6 * (μ * T) ^ (k + 2) := by ring_nf
    _ ≤ 6 * ∏ i, kDen m (Ms i) s z := by gcongr

theorem abs_dblKernA_le {j : ℕ} (hj : j ≤ k + 2) (d : Fin 2) :
    |dblKernA m s j Ms d z| ≤
      6 * (k + 2) / (min (M₀ ^ 2) 1 ^ (k + 3) * (3 / 4 * min (1 ^ 2) (m ^ 2))) := by
  set μ := min (M₀ ^ 2) 1
  set T := (1 - z.2) + kC m s z
  set c₁ := 3 / 4 * min (1 ^ 2 : ℝ) (m ^ 2)
  have hμ : 0 < μ := lt_min (by positivity) one_pos
  have hc₁ : 0 < c₁ := by positivity
  have hT1 : c₁ ≤ T := tSum_ge hs hz
  have hT : 0 < T := hc₁.trans_le hT1
  have hc := kC_nonneg (m := m) hs hz
  have hD : ∀ i, μ * T ≤ kDen m (Ms i) s z := fun i => kDen_ge_mu hs hM₀.le (hMs i) hz
  have hDp : ∀ i, 0 < kDen m (Ms i) s z := fun i => (mul_pos hμ hT).trans_le (hD i)
  have hP := prod_kDen_ge hs hM₀.le hMs hz hT.le
  have hPp : 0 < ∏ i, kDen m (Ms i) s z := (pow_pos (mul_pos hμ hT) _).trans_le hP
  have hS0 : 0 ≤ ∑ i, (kDen m (Ms i) s z)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.2 (hDp i)).le
  have hS1 : ∑ i, (kDen m (Ms i) s z)⁻¹ ≤ (k + 2) / (μ * T) := by
    calc ∑ i, (kDen m (Ms i) s z)⁻¹ ≤ ∑ _i : Fin (k + 2), (μ * T)⁻¹ :=
          Finset.sum_le_sum fun i _ => inv_anti₀ (mul_pos hμ hT) (hD i)
      _ = (k + 2) / (μ * T) := by simp [div_eq_mul_inv]
  have hw : 0 ≤ dblLineWt d z.1 ∧ dblLineWt d z.1 ≤ 1 :=
    dblLineWt_mem_Icc d hz.1
  obtain ⟨-, hy0, hy1⟩ := hz
  have hy : 0 ≤ 1 - z.2 := by linarith
  have hN := pow_mul_pow_le_tSum hc hy j (k + 2 - j)
  rw [Nat.add_sub_cancel' hj] at hN
  have hw3 : 6 * dblLineWt d z.1 * z.2 ^ 3 ≤ 6 := by
    have : z.2 ^ 3 ≤ 1 := pow_le_one₀ hy0 hy1
    have := hw.1
    nlinarith [mul_le_mul hw.2 this (by positivity) zero_le_one]
  have hw0 : 0 ≤ 6 * dblLineWt d z.1 * z.2 ^ 3 := by have := hw.1; positivity
  unfold dblKernA
  rw [abs_of_nonneg (div_nonneg (by positivity) hPp.le), div_le_div_iff₀ hPp (by positivity)]
  calc 6 * dblLineWt d z.1 * z.2 ^ 3 * (1 - z.2) ^ (k + 2 - j) * kC m s z ^ j *
        (∑ i, (kDen m (Ms i) s z)⁻¹) * (μ ^ (k + 3) * c₁)
      = (6 * dblLineWt d z.1 * z.2 ^ 3) * (kC m s z ^ j * (1 - z.2) ^ (k + 2 - j)) *
        (∑ i, (kDen m (Ms i) s z)⁻¹) * (μ ^ (k + 3) * c₁) := by ring
    _ ≤ 6 * T ^ (k + 2) * ((k + 2) / (μ * T)) * (μ ^ (k + 3) * c₁) := by gcongr
    _ ≤ 6 * T ^ (k + 2) * ((k + 2) / (μ * T)) * (μ ^ (k + 3) * T) := by gcongr
    _ = 6 * (k + 2) * (μ * T) ^ (k + 2) := by field_simp; ring_nf
    _ ≤ 6 * (k + 2) * ∏ i, kDen m (Ms i) s z := by gcongr

theorem abs_dblKernB_le {j : ℕ} (hj : j ≤ k + 2) (d : Fin 2) :
    |dblKernB m s j Ms d z| ≤
      6 * j / (min (M₀ ^ 2) 1 ^ (k + 2) * (3 / 4 * min (1 ^ 2) (m ^ 2))) := by
  set μ := min (M₀ ^ 2) 1
  set T := (1 - z.2) + kC m s z
  set c₁ := 3 / 4 * min (1 ^ 2 : ℝ) (m ^ 2)
  have hμ : 0 < μ := lt_min (by positivity) one_pos
  have hc₁ : 0 < c₁ := by positivity
  have hT1 : c₁ ≤ T := tSum_ge hs hz
  have hT : 0 < T := hc₁.trans_le hT1
  have hc := kC_nonneg (m := m) hs hz
  have hP := prod_kDen_ge hs hM₀.le hMs hz hT.le
  have hPp : 0 < ∏ i, kDen m (Ms i) s z := (pow_pos (mul_pos hμ hT) _).trans_le hP
  have hw : 0 ≤ dblLineWt d z.1 ∧ dblLineWt d z.1 ≤ 1 :=
    dblLineWt_mem_Icc d hz.1
  obtain ⟨-, hy0, hy1⟩ := hz
  have hy : 0 ≤ 1 - z.2 := by linarith
  have hN : (j : ℝ) * (kC m s z ^ (j - 1) * (1 - z.2) ^ (k + 2 - j)) ≤ j * T ^ (k + 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · have := pow_mul_pow_le_tSum hc hy (j - 1) (k + 2 - j)
      rw [show j - 1 + (k + 2 - j) = k + 1 by omega] at this
      gcongr
  have hw3 : 6 * dblLineWt d z.1 * z.2 ^ 3 ≤ 6 := by
    have : z.2 ^ 3 ≤ 1 := pow_le_one₀ hy0 hy1
    have := hw.1
    nlinarith [mul_le_mul hw.2 this (by positivity) zero_le_one]
  have hw0 : 0 ≤ 6 * dblLineWt d z.1 * z.2 ^ 3 := by have := hw.1; positivity
  unfold dblKernB
  rw [abs_of_nonneg (div_nonneg (by positivity) hPp.le), div_le_div_iff₀ hPp (by positivity)]
  calc 6 * dblLineWt d z.1 * z.2 ^ 3 * (1 - z.2) ^ (k + 2 - j) * ((j : ℝ) * kC m s z ^ (j - 1)) *
        (μ ^ (k + 2) * c₁)
      = (6 * dblLineWt d z.1 * z.2 ^ 3) * ((j : ℝ) * (kC m s z ^ (j - 1) *
        (1 - z.2) ^ (k + 2 - j))) * (μ ^ (k + 2) * c₁) := by ring
    _ ≤ 6 * (j * T ^ (k + 1)) * (μ ^ (k + 2) * c₁) := by gcongr
    _ ≤ 6 * (j * T ^ (k + 1)) * (μ ^ (k + 2) * T) := by gcongr
    _ = 6 * j * (μ * T) ^ (k + 2) := by ring_nf
    _ ≤ 6 * j * ∏ i, kDen m (Ms i) s z := by gcongr

end Bounds

/-! ### Integrability -/

theorem measurable_undKernJ (m s : ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    Measurable (undKernJ m s j Ms) := by
  unfold undKernJ kDen kC
  exact Measurable.div (by fun_prop) (Finset.measurable_prod _ fun i _ => by fun_prop)

theorem measurable_dblKernJ (m s : ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (d : Fin 2) :
    Measurable (dblKernJ m s j Ms d) := by
  unfold dblKernJ dblKernA dblKernB dblLineWt kDen kC
  split_ifs
  all_goals
    refine Measurable.sub (Measurable.div (Measurable.mul (by fun_prop)
      (Finset.measurable_sum _ fun i _ => (by fun_prop : Measurable _).inv))
      (Finset.measurable_prod _ fun i _ => by fun_prop))
      (Measurable.div (by fun_prop) (Finset.measurable_prod _ fun i _ => by fun_prop))

theorem integrable_undKernJ {m s M₀ : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (hM₀ : 0 < M₀) {k j : ℕ}
    (hj : j ≤ k + 2) {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) :
    Integrable (undKernJ m s j Ms) feynmanMeasure := by
  refine Integrable.mono' (integrable_const (6 / min (M₀ ^ 2) 1 ^ (k + 2)))
    (measurable_undKernJ m s j Ms).aestronglyMeasurable ?_
  filter_upwards [ae_feynmanMeasure] with z hz
  rw [Real.norm_eq_abs]
  exact abs_undKernJ_le hm hs hM₀ hMs (Ioc_prod_subset hz) hj

theorem integrable_dblKernJ {m s M₀ : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (hM₀ : 0 < M₀) {k j : ℕ}
    (hj : j ≤ k + 2) {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) (d : Fin 2) :
    Integrable (dblKernJ m s j Ms d) feynmanMeasure := by
  refine Integrable.mono' (integrable_const
    (6 * (k + 2) / (min (M₀ ^ 2) 1 ^ (k + 3) * (3 / 4 * min (1 ^ 2) (m ^ 2))) +
      6 * j / (min (M₀ ^ 2) 1 ^ (k + 2) * (3 / 4 * min (1 ^ 2) (m ^ 2)))))
    (measurable_dblKernJ m s j Ms d).aestronglyMeasurable ?_
  filter_upwards [ae_feynmanMeasure] with z hz
  rw [Real.norm_eq_abs]
  exact (abs_sub _ _).trans (add_le_add (abs_dblKernA_le hm hs hM₀ hMs (Ioc_prod_subset hz) hj d)
    (abs_dblKernB_le hm hs hM₀ hMs (Ioc_prod_subset hz) hj d))

/-! ### The values -/

/-- The undoubled value with the weight `K^j`. -/
noncomputable def undValJ (e m : ℝ) (p' p : Fin 4 → ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    ℂ :=
  I * ((π ^ 2 / 6 : ℝ) : ℂ) * (4 * kappa e * ((Minkowski.dot (p' - p) (p' - p) : ℂ) *
    (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2)) *
    ((∫ z, undKernJ m (Minkowski.dot (p' - p) (p' - p)) j Ms z ∂feynmanMeasure : ℝ) : ℂ)

/-- The doubled value with the weight `K^j`. -/
noncomputable def dblValJ (e m : ℝ) (p' p : Fin 4 → ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    (d : Fin 2) : ℂ :=
  I * ((π ^ 2 / 6 : ℝ) : ℂ) * kappa e *
    (4 * (m : ℂ) * ((Minkowski.dot (p' - p) (p' - p) : ℂ) *
      (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2)) *
    ((∫ z, dblKernJ m (Minkowski.dot (p' - p) (p' - p)) j Ms d z ∂feynmanMeasure : ℝ) : ℂ)

theorem undValJ_zero (e m : ℝ) (p' p : Fin 4 → ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    undValJ e m p' p 0 Ms = undVal e m p' p Ms := by
  rw [undValJ, undKernJ_zero, undVal]

theorem dblValJ_zero (e m : ℝ) (p' p : Fin 4 → ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (d : Fin 2) :
    dblValJ e m p' p 0 Ms d = dblVal e m p' p Ms d := by
  rw [dblValJ, dblKernJ_zero, dblVal]

theorem kDen_ne_zero_of_le {m s M₀ : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (hM₀ : 0 < M₀) {M : ℝ}
    (hM : M₀ ≤ M) {z : ℝ × ℝ} (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) : kDen m M s z ≠ 0 :=
  ((by positivity : (0 : ℝ) < 3 / 4 * min (M₀ ^ 2) (m ^ 2)).trans_le
    (kDen_ge_min hs hM₀.le hM (Ioc_prod_subset hz))).ne'

theorem undValJ_succ (e : ℝ) {m : ℝ} (hm : 0 < m) (p' p : Fin 4 → ℝ)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (j : ℕ) {k : ℕ} (hj : j ≤ k)
    (Ms : Fin (k + 1 + 2) → ℝ) (hpos : ∀ i, 0 < Ms i) :
    undValJ e m p' p (j + 1) Ms =
      undValJ e m p' p j (Fin.tail Ms) - ((Ms 0 ^ 2 : ℝ) : ℂ) * undValJ e m p' p j Ms := by
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  set q := Minkowski.dot (p' - p) (p' - p)
  have hI : ∫ z, undKernJ m q (j + 1) Ms z ∂feynmanMeasure =
      (∫ z, undKernJ m q j (Fin.tail Ms) z ∂feynmanMeasure) -
        Ms 0 ^ 2 * ∫ z, undKernJ m q j Ms z ∂feynmanMeasure := by
    rw [← integral_const_mul, ← integral_sub
      (integrable_undKernJ hm hq hM₀ (by omega) (Ms := Fin.tail Ms) fun i => hMs _)
      ((integrable_undKernJ hm hq hM₀ (by omega) hMs).const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [ae_feynmanMeasure] with z hz
    exact undKernJ_succ m q j hj Ms fun i => kDen_ne_zero_of_le hm hq hM₀ (hMs i) hz
  have hI' := congrArg (fun x : ℝ => (x : ℂ)) hI
  push_cast at hI'
  rw [undValJ, undValJ, undValJ, hI']
  push_cast
  ring

theorem dblValJ_succ (e : ℝ) {m : ℝ} (hm : 0 < m) (p' p : Fin 4 → ℝ)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (j : ℕ) {k : ℕ} (hj : j ≤ k)
    (Ms : Fin (k + 1 + 2) → ℝ) (hpos : ∀ i, 0 < Ms i) (d : Fin 2) :
    dblValJ e m p' p (j + 1) Ms d =
      dblValJ e m p' p j (Fin.tail Ms) d - ((Ms 0 ^ 2 : ℝ) : ℂ) * dblValJ e m p' p j Ms d := by
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  set q := Minkowski.dot (p' - p) (p' - p)
  have hI : ∫ z, dblKernJ m q (j + 1) Ms d z ∂feynmanMeasure =
      (∫ z, dblKernJ m q j (Fin.tail Ms) d z ∂feynmanMeasure) -
        Ms 0 ^ 2 * ∫ z, dblKernJ m q j Ms d z ∂feynmanMeasure := by
    rw [← integral_const_mul, ← integral_sub
      (integrable_dblKernJ hm hq hM₀ (by omega) (Ms := Fin.tail Ms) (fun i => hMs _) d)
      ((integrable_dblKernJ hm hq hM₀ (by omega) hMs d).const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [ae_feynmanMeasure] with z hz
    exact dblKernJ_succ m q j hj Ms d fun i => kDen_ne_zero_of_le hm hq hM₀ (hMs i) hz
  have hI' := congrArg (fun x : ℝ => (x : ℂ)) hI
  push_cast at hI'
  rw [dblValJ, dblValJ, dblValJ, hI']
  push_cast
  ring

/-! ### The power-weighted engine limits -/

section Value

variable {e m : ℝ} {p' p : Fin 4 → ℝ} (hm : 0 < m) (hp' : Minkowski.dot p' p' = -m ^ 2)
  (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
  (hq : 0 < Minkowski.dot (p' - p) (p' - p))
include hm hp' hp hp0' hp0 hq

/-- **The undoubled piece with weight `ℓ^(2j)`**: `powLimit j Ms = undValJ j Ms`, `j ≤ k`. -/
theorem powLimit_undChain_eq (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (hj : j ≤ k)
    (hpos : ∀ i, 0 < Ms i) (d : Fin 2) :
    powLimit 0 (undChain e m d p' p) m p' p j Ms = undValJ e m p' p j Ms := by
  induction j generalizing k with
  | zero =>
    rw [powLimit_zero, undValJ_zero]
    exact prodLimit_undChain_eq hm hp' hp hp0' hp0 hq Ms hpos d
  | succ j ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [powLimit_succ, ih (Fin.tail Ms) (by omega) fun i => hpos _, ih Ms (by omega) hpos,
        undValJ_succ e hm p' p hq.le j (by omega) Ms hpos]

/-- **The doubled piece with weight `ℓ^(2j)`**: `dblPowLimit j Ms = dblValJ j Ms`, `j ≤ k`. -/
theorem dblPowLimit_pauliChain_eq {α : ℂ} (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
    pauliChain e m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (hj : j ≤ k) (hpos : ∀ i, 0 < Ms i) (d : Fin 2) :
    dblPowLimit α (pauliChain e m p' p) m d p' p j Ms = dblValJ e m p' p j Ms d := by
  induction j generalizing k with
  | zero =>
    rw [dblPowLimit_zero, dblValJ_zero]
    exact dblProdLimit_pauliChain_eq hm hp' hp hp0' hp0 hq hα Ms hpos d
  | succ j ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [dblPowLimit_succ, ih (Fin.tail Ms) (by omega) fun i => hpos _, ih Ms (by omega) hpos,
        dblValJ_succ e hm p' p hq.le j (by omega) Ms hpos d]

end Value

end QED.ChainProof.CtLoB

end
