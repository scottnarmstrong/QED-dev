/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceLoop0
public import QED.GradedProof.RPi4LightInt
public import QED.GradedProof.RPi4FaceBound

/-!
# (R-Π₄) step L6d1: the bulk sector of a heavy-photon density, with rate `u^{-1/2}`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d1. In the chain
sums `Z₁` (rows `(1, 0)`), `Z₂` (rows `(0, 1)`), `Z₃` (the photon, row `(1, -1)`) of a collapsed
piece, the bulk is the part of the simplex away from the three corners: the two faces
(`faceSum = Z₂ + Z₃ > ρ₀`, `faceSum0 = Z₁ + Z₃ > ρ₀`) and the loop-UV corner
(`ferSum = Z₁ + Z₂ > ρ₀`). There `U ≥ (Z₁+Z₂)(Z₁+Z₃)(Z₂+Z₃) > ρ₀³`, so the coefficients of the
integrand are bounded, and with `V₀ ≥ c₁` the collapsed integrand is `≤ C t (c₁ + t u)^{-2}`,
`t = Z₃`; `(c₁ + tu)^{-2} ≤ c₁^{-1/2}(tu)^{-3/2}` and the integrability of `t^{-1/2}` on the
simplex give the rate `u^{-1/2}` for `u` times the bulk integral:

* `ferSum`, `bulkSet`, `faceSum_chain`, `faceSum0_chain`, `ferSum_chain`, `symanzikU_ge_bulk`;
* `lqNorm_le`, `lqHess_le`, `lqQuart_le` (from `LQBdd`);
* `norm_paramAtV_le_bulk`, `integrableOn_simplexPoint_rpow`;
* **`bulk_rate`**: `‖u ∫_{bulk} pieceF‖ ≤ C u^{-1/2}`, uniformly over the family.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)
open QED.Integration.SimplexMerge (integrableOn_simplex_comp_perm_iff)

variable {m : ℕ}

/-- The weight of the fermion lines (rows other than `(1, -1)`). -/
noncomputable def ferSum (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l => α l ≠ ![1, -1]), z l

/-- **The bulk of a piece**: away from both faces and from the loop-UV corner. -/
def bulkSet (α : Fin (m + 1) → Fin 2 → ℝ) (ρ₀ : ℝ) : Set (Fin (m + 1) → ℝ) :=
  {z | ρ₀ < faceSum α z ∧ ρ₀ < faceSum0 α z ∧ ρ₀ < ferSum α z}

theorem ite_ne_eq_add {α : Fin (m + 1) → Fin 2 → ℝ} (z : Fin (m + 1) → ℝ)
    {r r₁ r₂ : Fin 2 → ℝ} (h01 : r ≠ r₁) (h02 : r ≠ r₂) (h12 : r₁ ≠ r₂)
    (hr : ∀ l, α l = r ∨ α l = r₁ ∨ α l = r₂) (l : Fin (m + 1)) :
    (if α l ≠ r then z l else 0) =
      (if α l = r₁ then z l else 0) + (if α l = r₂ then z l else 0) := by
  rcases hr l with h | h | h <;> rw [h] <;> simp [h01, h02, h12, h01.symm, h02.symm, h12.symm]

theorem row10_ne_row01 : (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := fun h => by
  have := congrFun h 0
  norm_num at this

section Chain

variable {α : Fin (m + 1) → Fin 2 → ℝ}
  (hα : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1]) (z : Fin (m + 1) → ℝ)
include hα

theorem faceSum_chain : faceSum α z = chainZ α z ![0, 1] + chainZ α z ![1, -1] := by
  rw [faceSum, Finset.sum_filter, chainZ, chainZ, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => ite_ne_eq_add z row10_ne_row01 row10_ne_row1m1
    row01_ne_row1m1 hα l

theorem faceSum0_chain : faceSum0 α z = chainZ α z ![1, 0] + chainZ α z ![1, -1] := by
  rw [faceSum0, Finset.sum_filter, chainZ, chainZ, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => ite_ne_eq_add z (Ne.symm row10_ne_row01)
    row01_ne_row1m1 row10_ne_row1m1 (fun l => by rcases hα l with h | h | h <;> simp [h]) l

theorem ferSum_chain : ferSum α z = chainZ α z ![1, 0] + chainZ α z ![0, 1] := by
  rw [ferSum, Finset.sum_filter, chainZ, chainZ, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => ite_ne_eq_add z row10_ne_row1m1.symm
    row01_ne_row1m1.symm row10_ne_row01 (fun l => by rcases hα l with h | h | h <;> simp [h]) l

theorem sum_chain : ∑ l, z l = chainZ α z ![1, 0] + chainZ α z ![0, 1] + chainZ α z ![1, -1] := by
  rw [chainZ, chainZ, chainZ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases hα l with h | h | h <;> rw [h] <;>
    simp [Ne.symm row10_ne_row01, Ne.symm row10_ne_row1m1, Ne.symm row01_ne_row1m1]

/-- **`U` is bounded below on the bulk**: `U ≥ (Z₁+Z₂)(Z₁+Z₃)(Z₂+Z₃) > ρ₀³`. -/
theorem symanzikU_ge_bulk {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hz : ∀ l, 0 ≤ z l) (hz1 : ∑ l, z l = 1)
    (hb : z ∈ bulkSet α ρ₀) : ρ₀ ^ 3 ≤ symanzikU α z := by
  obtain ⟨h1, h2, h3⟩ := hb
  rw [faceSum_chain hα] at h1
  rw [faceSum0_chain hα] at h2
  rw [ferSum_chain hα] at h3
  rw [sum_chain hα] at hz1
  rw [symanzikU_chain α z hα]
  set Z₁ := chainZ α z ![1, 0]
  set Z₂ := chainZ α z ![0, 1]
  set Z₃ := chainZ α z ![1, -1]
  have hZ₁ := chainZ_nonneg α hz ![1, 0]
  have hZ₂ := chainZ_nonneg α hz ![0, 1]
  have hZ₃ := chainZ_nonneg α hz ![1, -1]
  have key : Z₁ * Z₂ + Z₃ * (Z₁ + Z₂) =
      (Z₁ + Z₂) * (Z₁ + Z₃) * (Z₂ + Z₃) + Z₁ * Z₂ * Z₃ := by
    have e : Z₁ * Z₂ + Z₃ * (Z₁ + Z₂) = (Z₁ + Z₂ + Z₃) * (Z₁ * Z₂ + Z₃ * (Z₁ + Z₂)) := by
      rw [hz1, one_mul]
    rw [e]
    ring
  rw [key]
  have hp : ρ₀ ^ 3 ≤ (Z₁ + Z₂) * (Z₁ + Z₃) * (Z₂ + Z₃) := by
    rw [pow_three, ← mul_assoc]
    exact mul_le_mul (mul_le_mul h3.le h2.le hρ₀.le (by positivity)) h1.le hρ₀.le
      (by positivity)
  have : 0 ≤ Z₁ * Z₂ * Z₃ := by positivity
  linarith

end Chain

/-! ### Numerator norms from `LQBdd` -/

section Norms

theorem sum_le_eight {f : LoopIndex → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c) : ∑ a, f a ≤ 8 * c := by
  refine (Finset.sum_le_sum fun a _ => h a).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, show Fintype.card LoopIndex = 8 from rfl]
  norm_num

variable {ι : Type*} {Q : ι → LoopQuartic} {B : ℝ} (h : LQBdd Q B) (i : ι)
include h

theorem lqQuart_le : lqQuart (Q i) ≤ 4096 * B := by
  unfold lqQuart
  have := sum_le_eight fun a => sum_le_eight fun b => sum_le_eight fun c =>
    sum_le_eight fun d => h.quart i a b c d
  linarith

theorem lqNorm_le : lqNorm (Q i) ≤ 4681 * B := by
  unfold lqNorm
  have h1 := sum_le_eight fun a => h.lin i a
  have h2 := sum_le_eight fun a => sum_le_eight fun b => h.quad i a b
  have h3 := sum_le_eight fun a => sum_le_eight fun b => sum_le_eight fun c => h.cub i a b c
  have h4 := lqQuart_le h i
  unfold lqQuart at h4
  linarith [h.const i]

theorem hessBound_le (a b : LoopIndex) : (Q i).hessBound a b ≤ 409 * B := by
  unfold LoopQuartic.hessBound
  have h1 := sum_le_eight fun c => (norm_add₃_le (a := (Q i).cub a b c) (b := (Q i).cub a c b)
    (c := (Q i).cub c a b)).trans (add_le_add (add_le_add (h.cub i a b c) (h.cub i a c b))
      (h.cub i c a b))
  have hq : ∀ c d, ‖(Q i).quartSym a b c d‖ ≤ 6 * B := fun c d => by
    unfold LoopQuartic.quartSym
    have e1 := norm_add_le ((Q i).quart a b c d) ((Q i).quart a c b d)
    have e2 := norm_add_le ((Q i).quart a b c d + (Q i).quart a c b d) ((Q i).quart a c d b)
    have e3 := norm_add_le ((Q i).quart a b c d + (Q i).quart a c b d + (Q i).quart a c d b)
      ((Q i).quart c a b d)
    have e4 := norm_add_le ((Q i).quart a b c d + (Q i).quart a c b d + (Q i).quart a c d b +
      (Q i).quart c a b d) ((Q i).quart c a d b)
    have e5 := norm_add_le ((Q i).quart a b c d + (Q i).quart a c b d + (Q i).quart a c d b +
      (Q i).quart c a b d + (Q i).quart c a d b) ((Q i).quart c d a b)
    linarith [h.quart i a b c d, h.quart i a c b d, h.quart i a c d b, h.quart i c a b d,
      h.quart i c a d b, h.quart i c d a b]
  have h2 := sum_le_eight fun c => sum_le_eight fun d => hq c d
  linarith [h.quad i a b]

theorem lqHess_le : lqHess (Q i) ≤ 26176 * B := by
  unfold lqHess
  have := sum_le_eight fun a => sum_le_eight fun b => hessBound_le h i a b
  linarith

end Norms

/-! ### The integrand on the bulk -/

section Pointwise

variable {α : Fin (m + 1) → Fin 2 → ℝ}
  (hα : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
  {pp : Fin (m + 1) → Fin 4 → ℝ} {z : Fin (m + 1) → ℝ} {KP : ℝ}
include hα

theorem abs_row_le_one (l : Fin (m + 1)) (s : Fin 2) : |α l s| ≤ 1 := by
  rcases hα l with h | h | h <;> rw [h] <;> fin_cases s <;> simp

theorem abs_loopShift_le_bulk {g : ℝ} (hz : ∀ l, 0 ≤ z l) (hz1 : ∑ l, z l = 1)
    (hP : ∀ l, ‖pp l‖ ≤ KP) (hg : ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ g) (s : Fin 2)
    (μ : Fin 4) : |loopShift α pp z s μ| ≤ 2 * g * KP := by
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply]
  have hb : ∀ t, |∑ i, z i * α i t * pp i μ| ≤ KP := fun t => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |z i * α i t * pp i μ| ≤ ∑ i, z i * KP := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_mul, abs_of_nonneg (hz i), mul_assoc]
          exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (abs_nonneg _)
            (abs_row_le_one hα i t)).trans ((norm_le_pi_norm (pp i) μ).trans (hP i))) (hz i)
      _ = KP := by rw [← Finset.sum_mul, hz1, one_mul]
  have hKP : 0 ≤ KP := (abs_nonneg _).trans (hb 0)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Fin.sum_univ_two]
  have e : ∀ t, |(symanzikMatrix α z)⁻¹ s t * ∑ i, z i * α i t * pp i μ| ≤ g * KP := fun t => by
    rw [abs_mul]
    exact mul_le_mul (hg s t) (hb t) (abs_nonneg _) ((abs_nonneg _).trans (hg s t))
  linarith [e 0, e 1]

end Pointwise

theorem inv_pow_le_sq {v c : ℝ} (hc : 0 < c) (hv : c ≤ v) {k : ℕ} (hk : 2 ≤ k) (hk4 : k ≤ 4) :
    (v ^ k)⁻¹ ≤ (1 + c⁻¹) ^ 2 * (v ^ 2)⁻¹ := by
  have hv0 : 0 < v := hc.trans_le hv
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [pow_add, mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h1 : (v ^ j)⁻¹ ≤ (c ^ j)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hv j)
  refine h1.trans ?_
  rw [← inv_pow]
  have hc1 : 0 ≤ c⁻¹ := by positivity
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> nlinarith

/-! ### The bulk rate -/

/-- **The integrability of `t^{-1/2}` on the simplex**, `t` any barycentric coordinate. -/
theorem integrableOn_simplexPoint_rpow (hm : 0 < m) (γ : Fin (m + 1)) :
    IntegrableOn (fun x => simplexPoint x γ ^ (-(1 / 2) : ℝ)) (simplexSet m) := by
  have h0 : (0 : Fin (m + 1)) = (⟨0, hm⟩ : Fin m).castSucc := rfl
  refine (integrableOn_simplex_comp_perm_iff (Equiv.swap γ 0)
    (fun w : Fin (m + 1) → ℝ => w γ ^ (-(1 / 2) : ℝ))).mp ?_
  have hh := integrableOn_headSum_rpow (m := m) (n := 1) (by omega) one_pos
    (q := 1 / 2) (by norm_num) (by norm_num)
  refine hh.congr_fun (fun x _ => ?_) (measurableSet_simplexSet m)
  simp only [Function.comp, Equiv.swap_apply_left, h0, simplexPoint_castSucc, headSum]
  congr 1
  rw [Finset.sum_eq_single ⟨0, hm⟩ (fun b _ hb => ite_eq_right_iff.mpr fun h =>
    absurd (Fin.ext (by simp only at h ⊢; omega)) hb) (by simp)]
  simp

end QED.GradedProof.RPi4

end
