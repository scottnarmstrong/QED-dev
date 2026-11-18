/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXCloseMono
public import QED.TwoLoop.UnitXGraphReduceV
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# Newton-polytope lower bounds for `U` and `Ẽ` of the crossed ladder

For the five group sums `z = (z_A, z_M, z_c, z_a, z_b)` of the crossed ladder, `U = gXU z` is a
sum of `8` monomials with coefficient `1` and `Ẽ = gXEn z` a sum of `13` monomials with
positive coefficients. Each monomial is at most the sum (`mono_UExp_le`, `mono_EExp_le`), so by
the Newton-polytope bound (`QED.TwoLoop.UnitXClose.mono_sum_smul_le`) `U ≥ mono z p` and
`Ẽ ≥ mono z q` for every `p`, `q` in the convex hulls of the exponents.

* `term_le`: for `z ∈ (0, 1]⁵`, natural exponents `n`, an index `i`, `d ∈ ℕ` and `p`, `q` with
  `U ≥ mono z p`, `Ẽ ≥ mono z q`: if `nₖ + [k = i] - 4 pₖ - d qₖ ≥ -s` for all `k`, then
  `zᵢ ∏ₖ zₖ^{nₖ} / (U⁴ Ẽᵈ) ≤ ∏ₖ zₖ^{-s}`.
-/

@[expose] public section

namespace QED.TwoLoop.UnitXClose

open QED.TwoLoop.UnitXGraph

/-- The point `(z_A, z_M, z_c, z_a, z_b)` as a function on `Fin 5`. -/
def gz (A M c a b : ℝ) : Fin 5 → ℝ := ![A, M, c, a, b]

/-- The exponents of the `8` monomials of `U`. -/
def UExp : Fin 8 → Fin 5 → ℕ :=
  ![![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 0, 1], ![0, 1, 1, 0, 0], ![0, 1, 0, 1, 0],
    ![0, 1, 0, 0, 1], ![0, 0, 1, 1, 0], ![0, 0, 0, 1, 1]]

/-- The exponents of the `13` monomials of `Ẽ`. -/
def EExp : Fin 13 → Fin 5 → ℕ :=
  ![![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 0, 1], ![1, 2, 0, 0, 0], ![1, 1, 1, 0, 0],
    ![1, 1, 0, 0, 1], ![1, 0, 2, 0, 0], ![0, 2, 1, 0, 0], ![0, 2, 0, 1, 0], ![0, 2, 0, 0, 1],
    ![0, 1, 2, 0, 0], ![0, 1, 1, 1, 0], ![0, 0, 2, 1, 0]]

/-- The real exponent vectors of `U`. -/
noncomputable def UExpR (j : Fin 8) : Fin 5 → ℝ := fun k => (UExp j k : ℝ)

/-- The real exponent vectors of `Ẽ`. -/
noncomputable def EExpR (j : Fin 13) : Fin 5 → ℝ := fun k => (EExp j k : ℝ)

variable {A M c a b : ℝ}

theorem gz_pos (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    ∀ k, 0 < gz A M c a b k := by
  intro k; fin_cases k <;> simp [gz] <;> assumption

theorem mono_UExp_le (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (j : Fin 8) : mono (gz A M c a b) (UExpR j) ≤ gXU A M c a b := by
  unfold UExpR
  rw [mono_natCast]
  have := mul_pos hA hM; have := mul_pos hA hc; have := mul_pos hA hb; have := mul_pos hM hc
  have := mul_pos hM ha; have := mul_pos hM hb; have := mul_pos hc ha; have := mul_pos ha hb
  fin_cases j <;> simp [Fin.prod_univ_five, UExp, gz, gXU] <;> nlinarith

theorem mono_EExp_le (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (j : Fin 13) : mono (gz A M c a b) (EExpR j) ≤ gXEn A M c a b := by
  unfold EExpR
  rw [mono_natCast]
  have h1 : 0 < c ^ 2 * a := by positivity
  have h2 : 0 < M * c * a := by positivity
  have h3 : 0 < M * c ^ 2 := by positivity
  have h4 : 0 < M ^ 2 * b := by positivity
  have h5 : 0 < M ^ 2 * a := by positivity
  have h6 : 0 < M ^ 2 * c := by positivity
  have h7 : 0 < A * c ^ 2 := by positivity
  have h8 : 0 < A * M * b := by positivity
  have h9 : 0 < A * M * c := by positivity
  have h10 : 0 < A * M ^ 2 := by positivity
  have h11 : 0 < A ^ 2 * b := by positivity
  have h12 : 0 < A ^ 2 * c := by positivity
  have h13 : 0 < A ^ 2 * M := by positivity
  have e : gXEn A M c a b = c ^ 2 * a + 2 * (M * c * a) + M * c ^ 2 + M ^ 2 * b + M ^ 2 * a +
      M ^ 2 * c + A * c ^ 2 + 2 * (A * M * b) + 2 * (A * M * c) + A * M ^ 2 + A ^ 2 * b +
      A ^ 2 * c + A ^ 2 * M := by unfold gXEn; ring
  rw [e]
  fin_cases j <;> simp [Fin.prod_univ_five, EExp, gz] <;> nlinarith

/-- `U ≥ mono z p` for `p` a convex combination of the exponents of `U`. -/
theorem mono_le_gXU (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (θ : Fin 8 → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hθ1 : ∑ j, θ j = 1) :
    mono (gz A M c a b) (∑ j, θ j • UExpR j) ≤ gXU A M c a b :=
  mono_sum_smul_le (gz_pos hA hM hc ha hb) _ θ hθ hθ1 (mono_UExp_le hA hM hc ha hb)

/-- `Ẽ ≥ mono z q` for `q` a convex combination of the exponents of `Ẽ`. -/
theorem mono_le_gXEn (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (φ : Fin 13 → ℝ) (hφ : ∀ j, 0 ≤ φ j) (hφ1 : ∑ j, φ j = 1) :
    mono (gz A M c a b) (∑ j, φ j • EExpR j) ≤ gXEn A M c a b :=
  mono_sum_smul_le (gz_pos hA hM hc ha hb) _ φ hφ hφ1 (mono_EExp_le hA hM hc ha hb)

/-- **The bound of one term**: `zᵢ ∏ₖ zₖ^{nₖ} / (U⁴ Ẽᵈ) ≤ ∏ₖ zₖ^{-s}` when the exponents
`nₖ + [k = i] - 4 pₖ - d qₖ` are at least `-s`. -/
theorem term_le {z : Fin 5 → ℝ} (hz : ∀ k, 0 < z k) (hz1 : ∀ k, z k ≤ 1) {U E : ℝ}
    {p q : Fin 5 → ℝ} (hU : mono z p ≤ U) (hE : mono z q ≤ E) (d : ℕ) (m : Fin 5 → ℕ)
    (i : Fin 5) {s : ℝ}
    (hexp : ∀ k, -s ≤ (m k : ℝ) + (if k = i then 1 else 0) - 4 * p k - d * q k) :
    z i * (∏ k, z k ^ m k) / (U ^ 4 * E ^ d) ≤ mono z (fun _ => -s) := by
  have hp := mono_pos hz p
  have hq := mono_pos hz q
  have hnum : z i * (∏ k, z k ^ m k) = mono z (fun k => (m k : ℝ) + if k = i then 1 else 0) := by
    rw [show (fun k => (m k : ℝ) + if k = i then 1 else 0) =
        (fun k => (m k : ℝ)) + (fun k => if k = i then (1 : ℝ) else 0) from rfl,
      mono_add hz, mono_natCast, mul_comm]
    congr 1
    unfold mono
    rw [Finset.prod_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have hden : mono z ((4 : ℝ) • p + (d : ℝ) • q) ≤ U ^ 4 * E ^ d := by
    rw [mono_add hz, mono_smul hz, mono_smul hz, Real.rpow_natCast, Real.rpow_ofNat]
    exact mul_le_mul (pow_le_pow_left₀ hp.le hU 4) (pow_le_pow_left₀ hq.le hE d)
      (pow_nonneg hq.le _) (pow_nonneg (hp.le.trans hU) _)
  have hden0 := mono_pos hz ((4 : ℝ) • p + (d : ℝ) • q)
  rw [hnum]
  calc mono z (fun k => (m k : ℝ) + if k = i then 1 else 0) / (U ^ 4 * E ^ d)
      ≤ mono z (fun k => (m k : ℝ) + if k = i then 1 else 0) /
          mono z ((4 : ℝ) • p + (d : ℝ) • q) :=
        div_le_div_of_nonneg_left (mono_pos hz _).le hden0 hden
    _ = mono z ((fun k => (m k : ℝ) + if k = i then 1 else 0) - ((4 : ℝ) • p + (d : ℝ) • q)) := by
        rw [div_eq_iff hden0.ne', ← mono_add hz, sub_add_cancel]
    _ ≤ mono z (fun _ => -s) := mono_le_of_le_one hz hz1 fun k => by
        simpa [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_add_eq_sub_sub]
          using hexp k

end QED.TwoLoop.UnitXClose

end
