/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecTwoAlg
public import QED.GradedProof.RPi4Cov
public import QED.Integration.SymanzikPositivity
public import QED.GradedProof.RPi4DecTwoClass

/-!
# (R-Π₄) step L9: relative second differences of the inverse powers of `V` at the tilt

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (second
differences in `s`, the class inputs `QED.GradedProof.RPi4.DecVTwo`). At the tilted momenta
`cᵢ k'(s)`, `k'(s) = tiltVec c s`, the remainder `V` is affine in `s`:
`V(s) = ∑ zᵢ Mᵢ² + s R` with `R ≥ 0` (`dec_symanzikV_tilt`). If `V` is nonnegative at some
`S₀ < S₁` (below threshold), then `R ≤ (S₁ - S₀)⁻¹ (V(s) + τ)` for `s ≥ S₁`, `τ ≥ 0`
(`dec_rem_le_of_nonneg`). An affine positive `W` with slope at most `κ W` has inverse powers
whose constants of class `QED.GradedProof.RPi4.DecTwoReg` are multiples of the value at the left
end (`dec_twoReg_inv_pow_affine`): **no uniform lower bound on `W` is needed**, so the photon
weight `W = V₀ + z_γ t` is covered for every photon mass `t > 0` at once
(`dec_twoReg_inv_pow_tilt`).

* `DecTwoReg.pow_rel`: powers with relative constants;
* `dec_symanzikV_tilt`, `dec_rem_le_of_nonneg`;
* **`dec_twoReg_inv_pow_affine`**, **`dec_twoReg_inv_pow_tilt`**;
* `dec_twoReg_tilt_lin`: the tilt chain rule with constants linear in those along the segment
  (so that pointwise constants stay integrable majorants);
* `dec_vTwo_of_twoReg`: `QED.GradedProof.RPi4.DecVTwo` from a second-difference constant of the
  class density on `[-δ, δ]` that is `O((t^{q/2} + t^{-q/2})/t)`.
-/

@[expose] public section

open Set

namespace QED.GradedProof.RPi4

/-- **Powers with relative constants**: if `‖g‖ ≤ r`, `L ≤ λ r` and `K ≤ 2 λ² r`, then `gⁿ` has
the constants `rⁿ`, `n λ rⁿ`, `n (n + 1) λ² rⁿ`. -/
theorem DecTwoReg.pow_rel {𝕜 : Type*} [RCLike 𝕜] {lo hi : ℝ} {g : ℝ → 𝕜} {r L K lam : ℝ}
    (hg : DecTwoReg lo hi g r L K) (hlam : 0 ≤ lam) (hL : L ≤ lam * r)
    (hK : K ≤ 2 * lam ^ 2 * r) (n : ℕ) :
    DecTwoReg lo hi (fun u => g u ^ n) (r ^ n) (n * lam * r ^ n)
      (n * (n + 1) * lam ^ 2 * r ^ n) := by
  have hr := hg.nonneg.1
  have hL0 := hg.nonneg.2.1
  induction n with
  | zero =>
    refine ((DecTwoReg.const (lo := lo) (hi := hi) (1 : 𝕜)).congr fun u _ =>
      (pow_zero _).symm).mono ?_ ?_ ?_ <;> simp
  | succ n ih =>
    have hm := (ih.mul hg).congr fun u _ => (pow_succ (g u) n).symm
    refine hm.mono (le_of_eq (pow_succ r n).symm) ?_ ?_
    · have hrn : 0 ≤ r ^ n := pow_nonneg hr n
      have h1 : r ^ n * L ≤ r ^ n * (lam * r) := mul_le_mul_of_nonneg_left hL hrn
      rw [pow_succ r n]
      push_cast
      nlinarith
    · have hrn : 0 ≤ r ^ n := pow_nonneg hr n
      have hK0 := hg.nonneg.2.2
      have h1 : r ^ n * K ≤ r ^ n * (2 * lam ^ 2 * r) := mul_le_mul_of_nonneg_left hK hrn
      have h2 : (n : ℝ) * lam * r ^ n * L ≤ n * lam * r ^ n * (lam * r) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      rw [pow_succ r n]
      push_cast
      nlinarith

/-- **Inverse powers of an affine positive function with relative slope**: on `[a, b]`, if
`W(s) = A + s φ` with `0 ≤ φ ≤ κ W(a)` and `W(a) > 0`, then `W⁻ᴺ` has the constants
`W(a)⁻ᴺ`, `N κ W(a)⁻ᴺ`, `N (N + 1) κ² W(a)⁻ᴺ`. -/
theorem dec_twoReg_inv_pow_affine (N : ℕ) {A φ κ a b : ℝ} (hφ : 0 ≤ φ) (hκ0 : 0 ≤ κ)
    (hW : 0 < A + a * φ) (hκ : φ ≤ κ * (A + a * φ)) :
    DecTwoReg a b (fun s => (((A + s * φ : ℝ) : ℂ))⁻¹ ^ N) ((A + a * φ)⁻¹ ^ N)
      (N * κ * (A + a * φ)⁻¹ ^ N) (N * (N + 1) * κ ^ 2 * (A + a * φ)⁻¹ ^ N) := by
  set m := A + a * φ with hm
  have hWr : DecTwoReg a b (fun s => A + s * φ) (|A| + max |a| |b| * φ) φ 0 :=
    { nonneg := ⟨by positivity, hφ, le_rfl⟩
      bound := fun u hu => by
        rw [Real.norm_eq_abs]
        refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
        rw [abs_mul, abs_of_nonneg hφ]
        exact mul_le_mul_of_nonneg_right (abs_le_max_abs_abs hu.1 hu.2) hφ
      lip := fun u _ v _ => by
        rw [Real.norm_eq_abs, show A + u * φ - (A + v * φ) = (u - v) * φ by ring, abs_mul,
          abs_of_nonneg hφ, mul_comm]
      two := fun u h _ _ => by
        rw [show A + (u + 2 * h) * φ - 2 * (A + (u + h) * φ) + (A + u * φ) = 0 by ring]
        simp }
  have hlow : ∀ u ∈ Icc a b, m ≤ ‖((A + u * φ : ℝ) : ℂ)‖ := fun u hu => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have : m ≤ A + u * φ := by
      have := mul_le_mul_of_nonneg_right hu.1 hφ
      linarith
    exact this.trans (le_abs_self _)
  have hinv := (hWr.ofReal (𝕜 := ℂ)).inv hW hlow
  have hmi : 0 ≤ m⁻¹ := (inv_pos.mpr hW).le
  have hL : φ / m ^ 2 ≤ κ * m⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    calc φ ≤ κ * m := hκ
      _ = κ * m⁻¹ * m ^ 2 := by field_simp
  have hK : (2 * φ ^ 2 + (|A| + max |a| |b| * φ) * 0) / m ^ 3 ≤ 2 * κ ^ 2 * m⁻¹ := by
    rw [mul_zero, add_zero, div_le_iff₀ (by positivity)]
    have h2 : φ ^ 2 ≤ (κ * m) ^ 2 := pow_le_pow_left₀ hφ hκ 2
    calc 2 * φ ^ 2 ≤ 2 * (κ * m) ^ 2 := by linarith
      _ = 2 * κ ^ 2 * m⁻¹ * m ^ 3 := by field_simp
  have := hinv.pow_rel hκ0 hL hK N
  rw [inv_pow] at this ⊢
  exact this

/-- **`V` at the tilted momenta is affine in `s`**: `V = ∑ zᵢ Mᵢ² + s R` with `R` the scalar
remainder of the coefficients. -/
theorem dec_symanzikV_tilt {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (M : Fin (m + 1) → ℝ)
    (z : Fin (m + 1) → ℝ) (cs : Fin (m + 1) → ℝ) {c s : ℝ} (hs : s ≤ 2 * c ^ 2) :
    QED.Integration.TwoLoop.symanzikV α (fun i => cs i • tiltVec c s) M z =
      ∑ i, z i * M i ^ 2 + s * QED.Integration.TwoLoop.remainder α z cs := by
  have h := QED.Integration.TwoLoop.symanzikV_smul_add_smul α M z cs 0
    (P := tiltVec c s) (K := 0) (by simp [Minkowski.dot_eq])
  simp only [zero_smul, add_zero, Pi.zero_apply] at h
  rw [h, dot_tiltVec hs]
  simp [Minkowski.dot_eq]

/-- **The remainder is controlled by `V` above a nonnegative point**: if `m + S₀ R ≥ 0`,
`R ≥ 0`, `S₀ < S₁ ≤ s` and `τ ≥ 0`, then `R ≤ (S₁ - S₀)⁻¹ (m + s R + τ)`. -/
theorem dec_rem_le_of_nonneg {m R S₀ S₁ s τ : ℝ} (h0 : 0 ≤ m + S₀ * R) (hR : 0 ≤ R)
    (hS : S₀ < S₁) (hs : S₁ ≤ s) (hτ : 0 ≤ τ) :
    R ≤ (S₁ - S₀)⁻¹ * (m + s * R + τ) := by
  have hd : 0 < S₁ - S₀ := by linarith
  rw [← div_eq_inv_mul, le_div_iff₀ hd]
  have : S₁ * R ≤ s * R := mul_le_mul_of_nonneg_right hs hR
  nlinarith

/-- **Inverse powers of `V + τ` at the tilt**: on `[a, b]` (`b ≤ 2c²`), if `V` is nonnegative at
the tilted momentum `S₀ < a` and `τ ≥ 0`, `W = V + τ` is positive at `a`, then `s ↦ W(s)⁻ᴺ` has
constants that are multiples of `W(a)⁻ᴺ`, with `κ = (a - S₀)⁻¹`. -/
theorem dec_twoReg_inv_pow_tilt {m : ℕ} (N : ℕ) (α : Fin (m + 1) → Fin 2 → ℝ)
    (M : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) (cs : Fin (m + 1) → ℝ) {c a b S₀ τ : ℝ}
    (hz : ∀ i, 0 ≤ z i) (hU : QED.Integration.TwoLoop.symanzikU α z ≠ 0) (hab : a ≤ b)
    (hb : b ≤ 2 * c ^ 2) (hS₀ : S₀ < a)
    (h0 : 0 ≤ QED.Integration.TwoLoop.symanzikV α (fun i => cs i • tiltVec c S₀) M z)
    (hτ : 0 ≤ τ)
    (hW : 0 < QED.Integration.TwoLoop.symanzikV α (fun i => cs i • tiltVec c a) M z + τ) :
    DecTwoReg a b (fun s => ((QED.Integration.TwoLoop.symanzikV α
        (fun i => cs i • tiltVec c s) M z + τ : ℝ) : ℂ)⁻¹ ^ N)
      ((QED.Integration.TwoLoop.symanzikV α (fun i => cs i • tiltVec c a) M z + τ)⁻¹ ^ N)
      (N * (a - S₀)⁻¹ *
        (QED.Integration.TwoLoop.symanzikV α (fun i => cs i • tiltVec c a) M z + τ)⁻¹ ^ N)
      (N * (N + 1) * ((a - S₀)⁻¹) ^ 2 *
        (QED.Integration.TwoLoop.symanzikV α (fun i => cs i • tiltVec c a) M z + τ)⁻¹ ^ N) := by
  set R := QED.Integration.TwoLoop.remainder α z cs
  set m₂ := ∑ i, z i * M i ^ 2
  have hR : 0 ≤ R := QED.Integration.TwoLoop.remainder_nonneg α hz hU cs
  have ha2 : a ≤ 2 * c ^ 2 := hab.trans hb
  have hS2 : S₀ ≤ 2 * c ^ 2 := hS₀.le.trans ha2
  have eV : ∀ s, s ≤ 2 * c ^ 2 →
      QED.Integration.TwoLoop.symanzikV α (fun i => cs i • tiltVec c s) M z + τ =
        (m₂ + τ) + s * R := fun s hs => by
    rw [dec_symanzikV_tilt α M z cs hs]; ring
  rw [dec_symanzikV_tilt α M z cs hS2] at h0
  rw [eV a ha2] at hW ⊢
  have hκ : R ≤ (a - S₀)⁻¹ * ((m₂ + τ) + a * R) := by
    have := dec_rem_le_of_nonneg h0 hR hS₀ le_rfl hτ
    rwa [show m₂ + a * R + τ = (m₂ + τ) + a * R by ring] at this
  refine (dec_twoReg_inv_pow_affine N hR (inv_nonneg.mpr (by linarith)) hW hκ).congr
    fun s hs => ?_
  rw [eV s (hs.2.trans hb)]

/-- **The tilt chain rule with linear constants**: there are `Lu, Ku ≥ 0` (depending only on
`c, S₀, S`) such that every `G` of class `DecTwoReg` along the segment with constants `M, L, K`
is of class `DecTwoReg` at the tilted vectors on `[S₀, S]` with `M, L Lu, K Lu² + L Ku`. -/
theorem dec_twoReg_tilt_lin {c S₀ S : ℝ} (hS₀S : S₀ < S) (hS : S < 2 * c ^ 2) :
    ∃ Lu Ku : ℝ, 0 ≤ Lu ∧ 0 ≤ Ku ∧ ∀ (G : (Fin 4 → ℝ) → ℂ) (M L K : ℝ),
      DecTwoReg (-(1 / 2)) (1 / 2)
        (fun u => G (lineK (tiltBase c S₀ S) (tiltDir c S₀ S) u)) M L K →
      DecTwoReg S₀ S (fun s => G (tiltVec c s)) M (L * Lu) (K * Lu ^ 2 + L * Ku) := by
  obtain ⟨Mu, Lu, Ku, hu⟩ := dec_twoReg_tiltU hS₀S hS
  refine ⟨Lu, Ku, hu.nonneg.2.1, hu.nonneg.2.2, fun G M L K hG => ?_⟩
  have hmap : ∀ s ∈ Icc S₀ S, decTiltU c S₀ S s ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := fun s hs =>
    dec_mem_Icc_half.mpr (dec_tiltVec_eq_lineK hS₀S hS hs.1 hs.2).1
  refine (hG.comp hu hmap).congr fun s hs => ?_
  simp only [← (dec_tiltVec_eq_lineK hS₀S hS hs.1 hs.2).2]

/-- **`DecVTwo` from the class constants**: if for every photon mass `t > 0` the class density
at the tilted vectors is of class `DecTwoReg` on `[-δ, δ]` with second-difference constant
`K t ≤ B (t^{q/2} + t^{-q/2}) / t`, then `DecVTwo` holds. -/
theorem dec_vTwo_of_twoReg
    {A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {base : Fin 5 → Fin 2 → ℤ} {cv : Fin 5 → ℝ} {F : Type} [Fintype F]
    {Φ : Lepton.Flavors F} {e m₀ c δ B q : ℝ} {K : ℝ → ℝ} (hB : 0 ≤ B) (hq0 : 0 ≤ q)
    (hq : q < 1 / 2)
    (hreg : ∀ t : ℝ, 0 < t → ∃ M L : ℝ, DecTwoReg (-δ) δ
      (fun s => vDens A base cv Φ e m₀ t (tiltVec c s) 2 3) M L (K t))
    (hK : ∀ t : ℝ, 0 < t → K t ≤ B * (t ^ (q / 2) + t ^ (-(q / 2))) / t) :
    DecVTwo A base cv Φ e m₀ c δ := by
  refine ⟨B, q, hB, hq0, hq, fun s h hs hs2 t ht => ?_⟩
  obtain ⟨M, L, hr⟩ := hreg t ht
  exact (hr.two s h (abs_le.mp hs) (abs_le.mp hs2)).trans
    (mul_le_mul_of_nonneg_right (hK t ht) (sq_nonneg h))

end QED.GradedProof.RPi4

end
