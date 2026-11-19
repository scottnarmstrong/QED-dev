/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ClassV
public import QED.GradedProof.SE2Positivity

/-!
# Positivity of `V` below threshold for the two-loop self-energy classes

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2. In self-energy kinematics every external line momentum is a multiple
`aᵢ p` of the one external momentum, so `V = ∑ᵢ zᵢ Mᵢ² + p² R(a)` with `R(a)` the remainder
(`symanzikV_smul_add_smul`). This file bounds `R(a)` by a path (max-flow) certificate.

## The bound (`sq_mul_remainder_le`)

Let `πₚ = α yₚ + a` (`P` in a finite family) be flows with the external routing, with weights
`λₚ ≥ 0` summing to `T > 0`, and let the capacities hold: `∑ₚ λₚ |πₚᵢ| ≤ Mᵢ` for every line.
Then `T² R(a) ≤ ∑ᵢ zᵢ Mᵢ²`.

Proof: let `y*` minimize `∑ᵢ zᵢ (αᵢ·y + aᵢ)²`, `f = α y* + a`, `w = z f`. The normal equations
`∑ᵢ wᵢ αᵢ = 0` give `∑ᵢ πᵢ wᵢ = ∑ᵢ aᵢ wᵢ = R` for every flow `π = α y + a`. Hence
`T R = ∑ₚ λₚ ∑ᵢ πₚᵢ wᵢ ≤ ∑ᵢ Mᵢ |wᵢ| = ∑ᵢ zᵢ Mᵢ |fᵢ| ≤ ∑ᵢ zᵢ (Mᵢ²/(2T) + T fᵢ²/2)`, i.e.
`T R ≤ W/(2T) + T R/2`. This is the two-loop form of the threshold condition: the certificate is
a flow of value `T` through the lines with capacities `Mᵢ`, which exists exactly when every cut
has mass at least `T`. Numerically (scratch `pos.py`) the bound is sharp for `R`, `X`, `V`.

## Consequence (`symanzikV_smul_ge`)

With `Mᵢ² ≥ c > 0`, `∑ zᵢ = 1` and `p² > -T²`: `V ≥ min(1, 1 + p²/T²) c`.

The certificates for the classes (`T = m + ν`):
* `R` (`ν ≤ min(m_γ, Λ)`): the photon path and the electron path.
* `X` (`ν ≤ min(m_γ, Λ)`, `ν ≤ 2m`): the electron path, the two electron-photon paths and the
  photon-electron-photon path, with weights depending on `min(ν, m)`.
* `V` (`ν ≤ min(m_γ, Λ)`, `ν ≤ 2 m₀`, loop masses `≥ m₀`): the open line and the path through the
  photons and the bubble, split evenly between its two lines.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.Integration.TwoLoop Matrix

section General

variable {m : ℕ}

/-- **The path bound for the remainder.** -/
theorem sq_mul_remainder_le {k : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hU : symanzikU α z ≠ 0) (a M : Fin (m + 1) → ℝ)
    (yP : Fin k → Fin 2 → ℝ) (lam : Fin k → ℝ) (hlam : ∀ P, 0 ≤ lam P) {T : ℝ} (hT : 0 < T)
    (hsum : ∑ P, lam P = T)
    (hcap : ∀ i, ∑ P, lam P * |∑ s, α i s * yP P s + a i| ≤ M i) :
    T ^ 2 * remainder α z a ≤ ∑ i, z i * M i ^ 2 := by
  set A := symanzikMatrix α z with hAdef
  set β := coefVec α z a with hβ
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hU
  set ys : Fin 2 → ℝ := -(A⁻¹ *ᵥ β) with hys
  set f : Fin (m + 1) → ℝ := fun i => ∑ s, α i s * ys s + a i with hf
  have hR : ∑ i, z i * f i ^ 2 = remainder α z a := by
    have h := sum_mul_sq_eq_shift α z hU a ys
    rw [show ys + A⁻¹ *ᵥ β = 0 by simp [hys], zero_dotProduct, zero_add] at h
    exact h
  have hAys : A *ᵥ ys = -β := by
    rw [hys, mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
  have hnorm : ∀ s, ∑ i, z i * α i s * f i = 0 := by
    intro s
    have h1 : ∑ i, z i * α i s * f i = (A *ᵥ ys) s + β s := by
      simp only [hf, hAdef, hβ, mulVec, dotProduct, symanzikMatrix, coefVec, of_apply,
        Fin.sum_univ_two, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, hAys]
    simp
  have hpath : ∀ y : Fin 2 → ℝ,
      ∑ i, (∑ s, α i s * y s + a i) * (z i * f i) = ∑ i, a i * (z i * f i) := by
    intro y
    have h0 := hnorm 0
    have h1 := hnorm 1
    have : ∑ i, (∑ s, α i s * y s + a i) * (z i * f i) =
        y 0 * ∑ i, z i * α i 0 * f i + y 1 * ∑ i, z i * α i 1 * f i +
          ∑ i, a i * (z i * f i) := by
      simp only [Fin.sum_univ_two, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h0, h1]
    ring
  have hRa : remainder α z a = ∑ i, a i * (z i * f i) := by
    rw [← hR, ← hpath ys]
    exact Finset.sum_congr rfl fun i _ => by simp only [hf]; ring
  -- `T R ≤ ∑ Mᵢ |wᵢ|`
  have hTR : T * remainder α z a ≤ ∑ i, M i * (z i * |f i|) := by
    calc T * remainder α z a = ∑ P, lam P * ∑ i, (∑ s, α i s * yP P s + a i) * (z i * f i) := by
          simp only [hpath, ← hRa, ← Finset.sum_mul, hsum]
      _ ≤ ∑ P, lam P * ∑ i, |∑ s, α i s * yP P s + a i| * (z i * |f i|) := by
          refine Finset.sum_le_sum fun P _ => mul_le_mul_of_nonneg_left ?_ (hlam P)
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← abs_of_nonneg (hz i), ← abs_mul, ← abs_mul, abs_of_nonneg (hz i)]
          exact le_abs_self _
      _ = ∑ i, (∑ P, lam P * |∑ s, α i s * yP P s + a i|) * (z i * |f i|) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun P _ => by ring
      _ ≤ ∑ i, M i * (z i * |f i|) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hcap i) (mul_nonneg (hz i) (abs_nonneg _))
  -- `∑ Mᵢ zᵢ |fᵢ| ≤ W/(2T) + T R/2`
  have hAM : ∑ i, M i * (z i * |f i|) ≤
      (∑ i, z i * M i ^ 2) / (2 * T) + T * remainder α z a / 2 := by
    rw [← hR, Finset.sum_div, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hsq : 0 ≤ (M i - T * |f i|) ^ 2 := sq_nonneg _
    have h2 : 2 * T * (M i * |f i|) ≤ M i ^ 2 + T ^ 2 * f i ^ 2 := by
      nlinarith [sq_abs (f i)]
    rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (hz i)]
  have hfin : T * remainder α z a ≤ (∑ i, z i * M i ^ 2) / (2 * T) + T * remainder α z a / 2 :=
    hTR.trans hAM
  have : T * remainder α z a / 2 ≤ (∑ i, z i * M i ^ 2) / (2 * T) := by linarith
  rw [le_div_iff₀ (by positivity)] at this
  nlinarith

/-- **`V` below threshold** from a path certificate. -/
theorem symanzikV_smul_ge {k : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU α z ≠ 0) (a M : Fin (m + 1) → ℝ)
    (yP : Fin k → Fin 2 → ℝ) (lam : Fin k → ℝ) (hlam : ∀ P, 0 ≤ lam P) {T : ℝ} (hT : 0 < T)
    (hsum : ∑ P, lam P = T)
    (hcap : ∀ i, ∑ P, lam P * |∑ s, α i s * yP P s + a i| ≤ M i) {c : ℝ} (hc : 0 < c)
    (hMc : ∀ i, c ≤ M i ^ 2) {p : Fin 4 → ℝ} (hs : -T ^ 2 < Minkowski.dot p p) :
    min 1 (1 + Minkowski.dot p p / T ^ 2) * c ≤ symanzikV α (fun i => a i • p) M z := by
  have hdot0 : Minkowski.dot p 0 = 0 := by simp [Minkowski.dot_eq]
  have h := symanzikV_smul_add_smul α M z a (fun _ => 0) hdot0
  simp only [smul_zero, add_zero] at h
  rw [h]
  have hd00 : Minkowski.dot (0 : Fin 4 → ℝ) 0 = 0 := by simp [Minkowski.dot_eq]
  rw [hd00, zero_mul, add_zero]
  set s := Minkowski.dot p p
  set W := ∑ i, z i * M i ^ 2
  have hWc : c ≤ W := by
    rw [← mul_one c, ← hz1, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hMc i) (hz i)
  have hR0 := remainder_nonneg α hz hU a
  have hRle := sq_mul_remainder_le α hz hU a M yP lam hlam hT hsum hcap
  rcases le_or_gt 0 s with hs0 | hs0
  · calc min 1 (1 + s / T ^ 2) * c ≤ 1 * c := mul_le_mul_of_nonneg_right (min_le_left _ _) hc.le
      _ ≤ W + s * remainder α z a := by nlinarith
  · have hT2 : 0 < T ^ 2 := by positivity
    have hδ : 0 < 1 + s / T ^ 2 := by
      have h1 : 0 < T ^ 2 + s := by linarith
      calc (0 : ℝ) < (T ^ 2 + s) / T ^ 2 := by positivity
        _ = 1 + s / T ^ 2 := by field_simp
    have hRW : remainder α z a ≤ W / T ^ 2 := by
      rw [le_div_iff₀ hT2]
      linarith
    calc min 1 (1 + s / T ^ 2) * c ≤ (1 + s / T ^ 2) * c :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hc.le
      _ ≤ (1 + s / T ^ 2) * W := mul_le_mul_of_nonneg_left hWc hδ.le
      _ = W + s * (W / T ^ 2) := by ring
      _ ≤ W + s * remainder α z a := by nlinarith

end General

/-! ### The certificates of the classes -/

/-- The external coefficients of the lines of `R`. -/
def aRc : Fin 7 → ℝ := ![0, 0, 0, 1, 1, 0, 0]

/-- The external coefficients of the lines of `X`. -/
def aXc : Fin 7 → ℝ := ![0, 0, 1, 1, 1, 0, 0]

/-- The external coefficients of the rows of `V`. -/
def aVc : Fin 5 → ℝ := ![0, 0, 1, 1, -1]

theorem ppR_eq (p : Fin 4 → ℝ) : ppR p = fun i => aRc i • p := by
  funext i; fin_cases i <;> simp [ppR, aRc]

theorem ppX_eq (p : Fin 4 → ℝ) : ppX p = fun i => aXc i • p := by
  funext i; fin_cases i <;> simp [ppX, aXc]

theorem basePP_eq (p : Fin 4 → ℝ) (j : Fin 5) : basePP p j = aVc j • p := by
  fin_cases j <;> simp [basePP, aVc]

/-- **`V` below threshold for `R`.** -/
theorem symanzikV_R_ge (Q : QED.WickModel.Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) {p : Fin 4 → ℝ} (hs : -(Q.m + ν) ^ 2 < Minkowski.dot p p)
    {z : Fin 7 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix aR) z ≠ 0) :
    min 1 (1 + Minkowski.dot p p / (Q.m + ν) ^ 2) * min (Q.m ^ 2) (ν ^ 2) ≤
      symanzikV (castLoopMatrix aR) (ppR p) (massesSE Q) z := by
  have h1 : ν ≤ Q.mγ := hν.trans (min_le_left _ _)
  have h2 : ν ≤ Q.Λ := hν.trans (min_le_right _ _)
  rw [ppR_eq]
  refine symanzikV_smul_ge _ hz hz1 hU aRc (massesSE Q) ![![0, 0], ![1, 1]] ![ν, Q.m]
    (fun P => by fin_cases P <;> simp [hν0.le, hm.le]) (by positivity)
    (by simp [Fin.sum_univ_two]; ring) ?_ (lt_min (by positivity) (by positivity)) ?_ hs
  · intro i
    fin_cases i <;> simp [castLoopMatrix, aR, aRc, massesSE, Fin.sum_univ_two] <;> linarith
  · intro i
    have e1 : ν ^ 2 ≤ Q.mγ ^ 2 := pow_le_pow_left₀ hν0.le h1 2
    have e2 : ν ^ 2 ≤ Q.Λ ^ 2 := pow_le_pow_left₀ hν0.le h2 2
    fin_cases i <;> simp [massesSE] <;> simp [e1, e2]

/-- **`V` below threshold for `X`.** -/
theorem symanzikV_X_ge (Q : QED.WickModel.Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (hν2 : ν ≤ 2 * Q.m) {p : Fin 4 → ℝ}
    (hs : -(Q.m + ν) ^ 2 < Minkowski.dot p p)
    {z : Fin 7 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix aX) z ≠ 0) :
    min 1 (1 + Minkowski.dot p p / (Q.m + ν) ^ 2) * min (Q.m ^ 2) (ν ^ 2) ≤
      symanzikV (castLoopMatrix aX) (ppX p) (massesSE Q) z := by
  have h1 : ν ≤ Q.mγ := hν.trans (min_le_left _ _)
  have h2 : ν ≤ Q.Λ := hν.trans (min_le_right _ _)
  set t := min ν Q.m with ht
  have t1 : t ≤ ν := min_le_left _ _
  have t2 : t ≤ Q.m := min_le_right _ _
  have t3 : ν ≤ 2 * t := by
    rcases min_cases ν Q.m with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [ht, h] <;> linarith
  have t0 : 0 ≤ t := le_min hν0.le hm.le
  rw [ppX_eq]
  refine symanzikV_smul_ge _ hz hz1 hU aXc (massesSE Q)
    ![![1, 1], ![0, 0], ![1, 0], ![0, -1]] ![Q.m - t, t, t, ν - t]
    (fun P => by fin_cases P <;> (simp; try linarith)) (by positivity)
    (by simp [Fin.sum_univ_four]) ?_ (lt_min (by positivity) (by positivity)) ?_ hs
  · intro i
    fin_cases i <;> simp [castLoopMatrix, aX, aXc, massesSE, Fin.sum_univ_four,
      Fin.sum_univ_two, abs_of_nonneg] <;> linarith
  · intro i
    have e1 : ν ^ 2 ≤ Q.mγ ^ 2 := pow_le_pow_left₀ hν0.le h1 2
    have e2 : ν ^ 2 ≤ Q.Λ ^ 2 := pow_le_pow_left₀ hν0.le h2 2
    fin_cases i <;> simp [massesSE] <;> simp [e1, e2]

/-- **`V` below threshold for the shapes of `V`**: rows of `baseA`, the open line (row `0`) of
mass at least `m`, the bubble lines (rows `1`, `2`) of mass at least `m₀`, the photon lines
(rows `3`, `4`) of mass at least `ν`, `ν ≤ 2 m₀`. -/
theorem symanzikV_vShape_ge {n : ℕ} (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
    {m m₀ ν : ℝ} (hm : 0 < m) (hν0 : 0 < ν) (hν2 : ν ≤ 2 * m₀)
    (h0 : ∀ i, sh i = 0 → m ≤ Ms i) (h12 : ∀ i, sh i = 1 ∨ sh i = 2 → m₀ ≤ Ms i)
    (h34 : ∀ i, sh i = 3 ∨ sh i = 4 → ν ≤ Ms i) {c : ℝ} (hc : 0 < c) (hMc : ∀ i, c ≤ Ms i ^ 2)
    {p : Fin 4 → ℝ} (hs : -(m + ν) ^ 2 < Minkowski.dot p p)
    {z : Fin (n + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix fun i => baseA (sh i)) z ≠ 0) :
    min 1 (1 + Minkowski.dot p p / (m + ν) ^ 2) * c ≤
      symanzikV (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) Ms z := by
  simp only [basePP_eq]
  refine symanzikV_smul_ge _ hz hz1 hU (fun i => aVc (sh i)) Ms ![![1, 0], ![0, -1 / 2]]
    ![m, ν] (fun P => by fin_cases P <;> simp [hm.le, hν0.le]) (by positivity)
    (by simp [Fin.sum_univ_two]) ?_ hc hMc hs
  intro i
  have a0 := h0 i
  have a12 := h12 i
  have a34 := h34 i
  rw [show (castLoopMatrix fun i => baseA (sh i)) i = castLoopMatrix baseA (sh i) from rfl]
  generalize sh i = j at a0 a12 a34 ⊢
  fin_cases j <;> simp [castLoopMatrix, baseA, aVc, Fin.sum_univ_two] at a0 a12 a34 ⊢ <;>
    norm_num [abs_of_pos] <;> linarith

end QED.GradedProof.SE2

end
