/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncW2
public import QED.GradedProof.RPi4FaceIdRayBPiece

/-!
# (R-Π₄) step L10, B-inc: corner and bulk of the derivative terms

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, the rate (B) of
the face-rate increment. In the scaled frame the `σ`-derivative of a collapsed piece of exponent
`n` contains the two terms `z_γ v paramAtV (n + 1) v` (`pieceFd`) and
`B(z) z_γ paramAtV (n + 1) v` (`pieceFw (n + 1)`), `B(z) = symanzikV α pp 0 z`. Since
`cX(n + 1) = kX cX(n)` (the exponents `kX ≤ n - 3` of `paramAtV n`) and `0 ≤ B ≤ v`, both are
bounded by `(n - 3) z_γ absBr`, where `absBr = ∑ ‖cX(n)‖ v^{-kX}` is the absolute bracket of the
exponent `n`. The power counting of `norm_pieceF_le_corner` and `faceIdRayB_norm_pieceF_le_bulk`
only bounds the coefficients, so it carries over to `absBr`:

* `faceIdRayD_symanzikV_eq`: `V(M) = V(0) + ∑ zᵢ Mᵢ²`;
* `faceIdRayD_cOneAt_succ`, `…_cTwoAt_succ`, `…_cThreeAt_succ`: `cX(n + 1) = kX cX(n)`;
* `absBr`, `faceIdRayD_norm_mul_paramAtV_succ_le`, `faceIdRayD_norm_pieceFd_le`,
  `faceIdRayD_norm_pieceFw_le`: the domination by `(n - 3) z_γ absBr`;
* `faceIdRayD_absBr_le_corner`, `faceIdRayD_absBr_le_bulk`: the two majorants;
* **`faceIdRayD_corner_rate`**, **`faceIdRayD_bulk_rate`**: the corner (`C u^{-1}`) and bulk
  (`C (1 + c₁⁻¹)³ u^{-1/2}`) sectors of any family dominated by `K z_γ absBr`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

variable {m : ℕ}

/-! ### The two derivative terms and their domination -/

/-- **The "times `v`" term** `z_γ v paramAtV (n + 1) v` of the derivative of a piece. -/
noncomputable def pieceFd (n : ℕ) (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) (u : ℝ)
    (z : Fin (m + 1) → ℝ) : ℂ :=
  (z γ : ℂ) * (((symanzikV α pp M z + z γ * u : ℝ) : ℂ) *
    paramAtV (n + 1) Q α pp z (symanzikV α pp M z + z γ * u))

/-- `V(M) = V(0) + ∑ zᵢ Mᵢ²`. -/
theorem faceIdRayD_symanzikV_eq (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ)
    (M z : Fin (m + 1) → ℝ) :
    symanzikV α pp M z = symanzikV α pp 0 z + ∑ i, z i * M i ^ 2 := by
  simp [symanzikV, mul_add, Finset.sum_add_distrib]
  ring

section Coeff

variable (n : ℕ) (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (z : Fin (m + 1) → ℝ)

theorem faceIdRayD_cOneAt_succ (hn : 4 ≤ n) :
    cOneAt (n + 1) Q α p z = ((n - 3 : ℕ) : ℂ) * cOneAt n Q α p z := by
  rw [cOneAt, cOneAt, show n + 1 - 4 = (n - 4) + 1 by omega, Nat.factorial_succ, Nat.cast_mul,
    show n - 4 + 1 = n - 3 by omega]
  ring

theorem faceIdRayD_cTwoAt_succ (hn : 5 ≤ n) :
    cTwoAt (n + 1) Q α p z = ((n - 4 : ℕ) : ℂ) * cTwoAt n Q α p z := by
  rw [cTwoAt, cTwoAt, show n + 1 - 5 = (n - 5) + 1 by omega, Nat.factorial_succ, Nat.cast_mul,
    show n - 5 + 1 = n - 4 by omega]
  ring

theorem faceIdRayD_cThreeAt_succ (hn : 6 ≤ n) :
    cThreeAt (n + 1) Q α z = ((n - 5 : ℕ) : ℂ) * cThreeAt n Q α z := by
  rw [cThreeAt, cThreeAt, show n + 1 - 6 = (n - 6) + 1 by omega, Nat.factorial_succ,
    Nat.cast_mul, show n - 6 + 1 = n - 5 by omega]
  ring

/-- **The absolute bracket** `∑ ‖cX(n)‖ v^{-kX}` of the exponent `n`. -/
noncomputable def absBr (v : ℝ) : ℝ :=
  ‖cOneAt n Q α p z‖ * (v ^ (n - 3))⁻¹ + ‖cTwoAt n Q α p z‖ * (v ^ (n - 4))⁻¹ +
    ‖cThreeAt n Q α z‖ * (v ^ (n - 5))⁻¹

variable {n Q α p z}

theorem faceIdRayD_absBr_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ absBr n Q α p z v := by
  unfold absBr; positivity

theorem faceIdRayD_absBr_eq_zero (hU : symanzikU α z = 0) {v : ℝ} : absBr n Q α p z v = 0 := by
  unfold absBr; simp [cOneAt, cTwoAt, cThreeAt, hU]

theorem faceIdRayD_absBr_le_of_coeff {v a b c : ℝ} (hv : 0 < v)
    (h1 : ‖cOneAt n Q α p z‖ ≤ a) (h2 : ‖cTwoAt n Q α p z‖ ≤ b) (h3 : ‖cThreeAt n Q α z‖ ≤ c) :
    absBr n Q α p z v ≤ a * (v ^ (n - 3))⁻¹ + b * (v ^ (n - 4))⁻¹ + c * (v ^ (n - 5))⁻¹ := by
  unfold absBr
  have := hv.le
  gcongr

/-- `w v^{-(k+1)} ≤ v^{-k}` for `0 ≤ w ≤ v`. -/
theorem faceIdRayD_mul_inv_pow_le {w v : ℝ} (hw : 0 ≤ w) (hwv : w ≤ v) (k : ℕ) :
    w * (v ^ (k + 1))⁻¹ ≤ (v ^ k)⁻¹ := by
  rcases (hw.trans hwv).eq_or_lt with h | h
  · rw [← h] at hwv ⊢
    have : w = 0 := le_antisymm hwv hw
    rw [this, zero_mul]
    positivity
  · rw [pow_succ, mul_inv, ← mul_assoc, mul_comm w, mul_assoc]
    have : w * v⁻¹ ≤ 1 := by rw [← div_eq_mul_inv]; exact (div_le_one h).2 hwv
    calc (v ^ k)⁻¹ * (w * v⁻¹) ≤ (v ^ k)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _

/-- **The domination** `‖w paramAtV (n + 1) v‖ ≤ (n - 3) absBr n v` for `0 ≤ w ≤ v`, `n ≥ 6`. -/
theorem faceIdRayD_norm_mul_paramAtV_succ_le (hn : 6 ≤ n) {w v : ℝ} (hw : 0 ≤ w)
    (hwv : w ≤ v) :
    ‖(w : ℂ) * paramAtV (n + 1) Q α p z v‖ ≤ ((n - 3 : ℕ) : ℝ) * absBr n Q α p z v := by
  have hv : 0 ≤ v := hw.trans hwv
  have key : ∀ (c : ℂ) (k : ℕ), ‖(w : ℂ) * (c * ((v : ℂ) ^ (k + 1))⁻¹)‖ ≤ ‖c‖ * (v ^ k)⁻¹ :=
    fun c k => by
      rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hw, Real.norm_of_nonneg hv]
      have := faceIdRayD_mul_inv_pow_le hw hwv k
      calc w * (‖c‖ * (v ^ (k + 1))⁻¹) = ‖c‖ * (w * (v ^ (k + 1))⁻¹) := by ring
        _ ≤ ‖c‖ * (v ^ k)⁻¹ := mul_le_mul_of_nonneg_left this (norm_nonneg _)
  rw [paramAtV_eq, mul_add, mul_add]
  have e1 : n + 1 - 3 = (n - 3) + 1 := by omega
  have e2 : n + 1 - 4 = (n - 4) + 1 := by omega
  have e3 : n + 1 - 5 = (n - 5) + 1 := by omega
  rw [e1, e2, e3, faceIdRayD_cOneAt_succ n Q α p z (by omega),
    faceIdRayD_cTwoAt_succ n Q α p z (by omega), faceIdRayD_cThreeAt_succ n Q α z hn]
  have k1 := key (((n - 3 : ℕ) : ℂ) * cOneAt n Q α p z) (n - 3)
  have k2 := key (((n - 4 : ℕ) : ℂ) * cTwoAt n Q α p z) (n - 4)
  have k3 := key (((n - 5 : ℕ) : ℂ) * cThreeAt n Q α z) (n - 5)
  have nc : ∀ (j : ℕ) (c : ℂ), ‖(j : ℂ) * c‖ = (j : ℝ) * ‖c‖ := fun j c => by
    rw [norm_mul, Complex.norm_natCast]
  rw [nc] at k1 k2 k3
  have f2 : ((n - 4 : ℕ) : ℝ) ≤ ((n - 3 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have f3 : ((n - 5 : ℕ) : ℝ) ≤ ((n - 3 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have g2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right f2 (norm_nonneg
    (cTwoAt n Q α p z))) (show 0 ≤ (v ^ (n - 4))⁻¹ by positivity)
  have g3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right f3 (norm_nonneg
    (cThreeAt n Q α z))) (show 0 ≤ (v ^ (n - 5))⁻¹ by positivity)
  refine (norm_add₃_le).trans ?_
  unfold absBr
  nlinarith

end Coeff

/-- **The "times `v`" term is dominated by the absolute bracket** (`0 ≤ V(0)` when `U ≠ 0`). -/
theorem faceIdRayD_norm_pieceFd_le {n : ℕ} (hn : 6 ≤ n) {Q : LoopQuartic}
    {α : Fin (m + 1) → Fin 2 → ℝ} {pp : Fin (m + 1) → Fin 4 → ℝ} {M : Fin (m + 1) → ℝ}
    {γ : Fin (m + 1)} {u : ℝ} (hu : 0 ≤ u) {z : Fin (m + 1) → ℝ} (hz : ∀ l, 0 ≤ z l)
    (hB : symanzikU α z ≠ 0 → 0 ≤ symanzikV α pp 0 z) :
    ‖pieceFd n Q α pp M γ u z‖ ≤ ((n - 3 : ℕ) : ℝ) *
      (z γ * absBr n Q α pp z (symanzikV α pp M z + z γ * u)) := by
  set v := symanzikV α pp M z + z γ * u
  by_cases hU : symanzikU α z = 0
  · have : paramAtV (n + 1) Q α pp z v = 0 := by simp [paramAtV, hU]
    rw [pieceFd, this, mul_zero, mul_zero, norm_zero]
    have : 0 ≤ absBr n Q α pp z v := by
      unfold absBr; simp [cOneAt, cTwoAt, cThreeAt, hU]
    have := hz γ
    positivity
  · have hM : 0 ≤ ∑ i, z i * M i ^ 2 := Finset.sum_nonneg fun i _ => by
      have := hz i; positivity
    have hv : 0 ≤ v := by
      have := hB hU
      have := mul_nonneg (hz γ) hu
      simp only [v, faceIdRayD_symanzikV_eq α pp M z]
      linarith
    rw [pieceFd, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hz γ)]
    have h := faceIdRayD_norm_mul_paramAtV_succ_le (Q := Q) (α := α) (p := pp) (z := z) hn hv
      le_rfl
    calc z γ * ‖((v : ℝ) : ℂ) * paramAtV (n + 1) Q α pp z v‖
        ≤ z γ * (((n - 3 : ℕ) : ℝ) * absBr n Q α pp z v) := mul_le_mul_of_nonneg_left h (hz γ)
      _ = _ := by ring

/-- **The weighted term is dominated by the absolute bracket** (`0 ≤ V(0)` when `U ≠ 0`). -/
theorem faceIdRayD_norm_pieceFw_le {n : ℕ} (hn : 6 ≤ n) {Q : LoopQuartic}
    {α : Fin (m + 1) → Fin 2 → ℝ} {pp : Fin (m + 1) → Fin 4 → ℝ} {M : Fin (m + 1) → ℝ}
    {γ : Fin (m + 1)} {u : ℝ} (hu : 0 ≤ u) {z : Fin (m + 1) → ℝ} (hz : ∀ l, 0 ≤ z l)
    (hB : symanzikU α z ≠ 0 → 0 ≤ symanzikV α pp 0 z) :
    ‖pieceFw (n + 1) Q α pp M γ u z‖ ≤ ((n - 3 : ℕ) : ℝ) *
      (z γ * absBr n Q α pp z (symanzikV α pp M z + z γ * u)) := by
  set v := symanzikV α pp M z + z γ * u
  by_cases hU : symanzikU α z = 0
  · have : paramAtV (n + 1) Q α pp z v = 0 := by simp [paramAtV, hU]
    rw [pieceFw, pieceF, this, mul_zero, mul_zero, norm_zero]
    have : 0 ≤ absBr n Q α pp z v := by
      unfold absBr; simp [cOneAt, cTwoAt, cThreeAt, hU]
    have := hz γ
    positivity
  · have hM : 0 ≤ ∑ i, z i * M i ^ 2 := Finset.sum_nonneg fun i _ => by
      have := hz i; positivity
    have hB0 := hB hU
    have hBv : symanzikV α pp 0 z ≤ v := by
      have := mul_nonneg (hz γ) hu
      simp only [v, faceIdRayD_symanzikV_eq α pp M z]
      linarith
    have h := faceIdRayD_norm_mul_paramAtV_succ_le (Q := Q) (α := α) (p := pp) (z := z) hn hB0
      hBv
    rw [pieceFw, pieceF, show ((symanzikV α pp 0 z : ℝ) : ℂ) * ((z γ : ℂ) *
        paramAtV (n + 1) Q α pp z v) = (z γ : ℂ) * (((symanzikV α pp 0 z : ℝ) : ℂ) *
        paramAtV (n + 1) Q α pp z v) by ring, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (hz γ)]
    calc z γ * ‖((symanzikV α pp 0 z : ℝ) : ℂ) * paramAtV (n + 1) Q α pp z v‖
        ≤ z γ * (((n - 3 : ℕ) : ℝ) * absBr n Q α pp z v) := mul_le_mul_of_nonneg_left h (hz γ)
      _ = _ := by ring

/-! ### The corner majorant of the absolute bracket -/

/-- **The absolute bracket on the corner**: `absBr ≤ E u^{-2} ferSum^{-(n-3)}` for `u ≥ 1`, with
`E` uniform over the family (the power counting of `norm_pieceF_le_corner`). -/
theorem faceIdRayD_absBr_le_corner {ι : Type*} (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1)) (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (cs : Fin (m + 1) → ℝ) (k : ι → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hk : ∀ s μ, |k s μ| ≤ KP) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ s (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      z ∈ cornerSet α ρ₀ →
      (symanzikU α z ≠ 0 → 0 ≤ symanzikV α (fun i => cs i • k s) (M s) z) →
      ∀ u : ℝ, 1 ≤ u →
      absBr n (Q s) α (fun i => cs i • k s) z
          (symanzikV α (fun i => cs i • k s) (M s) z + z γ₀ * u) ≤
        E * (u ^ 2)⁻¹ * (ferSum α z ^ (n - 3))⁻¹ := by
  have hγ : α γ₀ = ![1, -1] := (huniq γ₀).mpr rfl
  obtain ⟨C, hC0, hC⟩ := exists_abs_loopShift_smul_le α cs
  set B' := max BQ 0 with hB'
  have hB0 : 0 ≤ B' := le_max_right _ _
  have hQ' : LQBdd Q B' := ⟨fun i => (hQ.const i).trans (le_max_left _ _),
    fun i a => (hQ.lin i a).trans (le_max_left _ _),
    fun i a b => (hQ.quad i a b).trans (le_max_left _ _),
    fun i a b c => (hQ.cub i a b c).trans (le_max_left _ _),
    fun i a b c d => (hQ.quart i a b c d).trans (le_max_left _ _)⟩
  set K : ℝ := C * max KP 0 with hK
  have hK0 : 0 ≤ K := by positivity
  set a : ℝ := 6 * (4681 * B' * (1 + K) ^ 4)
  set b : ℝ := 26176 * B' * (1 + (K + K ^ 2))
  set c : ℝ := 4096 * B' * 3
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  set ε : ℝ := 1 - ρ₀ with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  set D : ℝ := ε⁻¹ with hD
  have hD1 : 1 ≤ D := one_le_inv₀ hε0 |>.mpr hε1
  refine ⟨(a + b + c) * D ^ 8, by positivity, fun s z hz hz1 hcorner hV u hu => ?_⟩
  set pp : Fin (m + 1) → Fin 4 → ℝ := fun i => cs i • k s
  set y := ferSum α z with hy
  have hy0 : 0 ≤ y := Finset.sum_nonneg fun l _ => hz l
  have hyρ : y ≤ ρ₀ := hcorner
  have hq3 : 3 ≤ n - 3 := by rcases hn with rfl | ⟨rfl, -⟩ <;> norm_num
  rcases hy0.eq_or_lt with hy0' | hypos
  · have hU0 := symanzikU_eq_zero_of_ferSum hrow hz hy0'.symm
    rw [← hy0', zero_pow (by omega), inv_zero, mul_zero]
    unfold absBr
    simp [cOneAt, cTwoAt, cThreeAt, hU0]
  have ht : z γ₀ = 1 - y := by rw [hy, ferSum_eq_one_sub huniq hz1]; ring
  have htε : ε ≤ z γ₀ := by rw [ht, hε]; linarith
  have hU1 := symanzikU_ge_corner hγ hrow hz (z := z)
  have hεy : 0 < ε * y := mul_pos hε0 hypos
  have hUε : ε * y ≤ symanzikU α z := (mul_le_mul_of_nonneg_right htε hy0).trans hU1
  have hU : 0 < symanzikU α z := hεy.trans_le hUε
  set X := (symanzikU α z)⁻¹ with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXP : X ≤ (ε * y)⁻¹ := inv_anti₀ hεy hUε
  have hP1 : 1 ≤ (ε * y)⁻¹ := one_le_inv₀ hεy |>.mpr ((mul_le_mul hε1 (show y ≤ 1 by linarith) hy0
    zero_le_one).trans_eq (one_mul 1))
  have hgent : ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ X := fun r t => by
    refine (abs_inv_le_chain (α := α) (hα := hrow) (hz := hz) (hU := hU.ne') r t).trans ?_
    rw [← sum_chain hrow z, hz1, one_div]
  have hX : ∀ a, ‖loopComp (-loopShift α pp z) a‖ ≤ K := fun a => by
    simp only [loopComp, Complex.norm_real, Real.norm_eq_abs, Pi.neg_apply, abs_neg]
    refine (hC z hz hU.ne' (k s) a.1 a.2).trans ?_
    exact mul_le_mul_of_nonneg_left ((hk s a.2).trans (le_max_left _ _)) hC0
  have hn7 : (n - 4).factorial ≤ (6 : ℝ) ∧ ((n - 5).factorial : ℝ) / 2 ≤ 1 := by
    rcases hn with rfl | ⟨rfl, -⟩ <;> norm_num [Nat.factorial]
  have eU : ∀ x : ℝ, x / symanzikU α z ^ 2 = x * X ^ 2 := fun x => by
    rw [hXdef, inv_pow, div_eq_mul_inv]
  have h1 : ‖cOneAt n (Q s) α pp z‖ ≤ a * X ^ 2 := by
    refine (norm_cOneAt_le (n := n) (α := α) (z := z) (hK := hK0) (hX := hX) (hU := hU)).trans ?_
    rw [eU]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul hn7.1 (mul_le_mul_of_nonneg_right (lqNorm_le hQ' s) (by positivity))
      (mul_nonneg (lqNorm_nonneg _) (by positivity)) (by norm_num)
  have h2 : ‖cTwoAt n (Q s) α pp z‖ ≤ b * X ^ 3 := by
    refine (norm_cTwoAt_le (n := n) (α := α) (z := z) (hK := hK0) (hX := hX) (hU := hU)
      (hg := hgent)).trans ?_
    rw [eU]
    have e : ((n - 5).factorial : ℝ) / 2 * (lqHess (Q s) * (1 + (K + K ^ 2)) * X) ≤
        1 * (26176 * B' * (1 + (K + K ^ 2)) * X) :=
      mul_le_mul hn7.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (lqHess_le hQ' s) (by positivity)) hX0)
        (mul_nonneg (mul_nonneg (lqHess_nonneg _) (by positivity)) hX0) (by norm_num)
    calc ((n - 5).factorial : ℝ) / 2 * (lqHess (Q s) * (1 + (K + K ^ 2)) * X) * X ^ 2
        ≤ 1 * (26176 * B' * (1 + (K + K ^ 2)) * X) * X ^ 2 :=
          mul_le_mul_of_nonneg_right e (by positivity)
      _ = b * X ^ 3 := by ring
  have hu0 : 0 < u := one_pos.trans_le hu
  have hv0 : 0 < ε * u := by positivity
  have hv : ε * u ≤ symanzikV α pp (M s) z + z γ₀ * u := by
    have := mul_le_mul_of_nonneg_right htε hu0.le
    have := hV hU.ne'
    linarith
  have hvp : 0 < symanzikV α pp (M s) z + z γ₀ * u := hv0.trans_le hv
  set v := symanzikV α pp (M s) z + z γ₀ * u with hvdef
  set w := v⁻¹ with hwdef
  have hw0 : 0 ≤ w := by positivity
  have hwR : w ≤ (ε * u)⁻¹ := inv_anti₀ hv0 hv
  have hRD : (ε * u)⁻¹ ≤ D := by
    rw [hD]; exact inv_anti₀ hε0 (le_mul_of_one_le_right hε0.le hu)
  have ew : ∀ j, (v ^ j)⁻¹ = w ^ j := fun j => by rw [hwdef, inv_pow]
  set Z := (ε * y)⁻¹ ^ (n - 3) * ((ε * u)⁻¹ ^ 2 * D ^ 2) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have T : ∀ j i : ℕ, j ≤ n - 3 → 2 ≤ i → i ≤ 4 → X ^ j * w ^ i ≤ Z :=
    fun j i hj hi2 hi4 => corner_term hX0 hXP hP1 hw0 hwR hRD hD1 hj hi2 hi4
  have hpar : absBr n (Q s) α pp z v ≤ (a + b + c) * Z := by
    rcases hn with hn7 | ⟨hn6, hq0⟩
    · have h3 : ‖cThreeAt n (Q s) α z‖ ≤ c * X ^ 4 := by
        refine (norm_cThreeAt_le (n := n) (α := α) (z := z) (hU := hU) (hg := hgent)).trans ?_
        rw [eU, show n - 6 = 1 by omega]
        have hq := lqQuart_le hQ' s
        have hBX : 0 ≤ B' * X ^ 4 := mul_nonneg hB0 (pow_nonneg hX0 4)
        have e : ((Nat.factorial 1 : ℕ) : ℝ) / 4 * (lqQuart (Q s) * (3 * X ^ 2)) * X ^ 2 =
            3 / 4 * (lqQuart (Q s) * X ^ 4) := by
          norm_num [Nat.factorial]; ring
        rw [e]
        have := mul_le_mul_of_nonneg_right hq (pow_nonneg hX0 4)
        linarith
      refine (faceIdRayD_absBr_le_of_coeff (hv := hvp) (h1 := h1) (h2 := h2) (h3 := h3)).trans ?_
      rw [ew, ew, ew, show n - 3 = 4 by omega, show n - 4 = 3 by omega,
        show n - 5 = 2 by omega]
      have f1 := mul_le_mul_of_nonneg_left (T 2 4 (by omega) (by norm_num) (by norm_num)) ha
      have f2 := mul_le_mul_of_nonneg_left (T 3 3 (by omega) (by norm_num) (by norm_num)) hb
      have f3 := mul_le_mul_of_nonneg_left (T 4 2 (by omega) (by norm_num) (by norm_num)) hc
      linarith
    · have h3 : ‖cThreeAt n (Q s) α z‖ ≤ 0 := by
        refine (norm_cThreeAt_le (n := n) (α := α) (z := z) (hU := hU) (hg := hgent)).trans
          (le_of_eq ?_)
        simp [lqQuart, hq0 s]
      refine (faceIdRayD_absBr_le_of_coeff (hv := hvp) (h1 := h1) (h2 := h2) (h3 := h3)).trans ?_
      rw [ew, ew, ew, show n - 3 = 3 by omega, show n - 4 = 2 by omega]
      have f1 := mul_le_mul_of_nonneg_left (T 2 3 (by omega) (by norm_num) (by norm_num)) ha
      have f2 := mul_le_mul_of_nonneg_left (T 3 2 (by omega) (by norm_num) (by norm_num)) hb
      have f3 : 0 ≤ c * Z := mul_nonneg hc hZ0
      have f4 : 0 * w ^ (n - 5) = 0 := zero_mul _
      linarith
  have hZle : Z ≤ D ^ 8 * (u ^ 2)⁻¹ * (y ^ (n - 3))⁻¹ := by
    have e1 : (ε * y)⁻¹ ^ (n - 3) = D ^ (n - 3) * (y ^ (n - 3))⁻¹ := by
      rw [hD, mul_inv, mul_pow, inv_pow y]
    have e2 : (ε * u)⁻¹ ^ 2 = D ^ 2 * (u ^ 2)⁻¹ := by rw [hD, mul_inv, mul_pow, inv_pow u]
    have hDn : D ^ (n - 3) ≤ D ^ 4 :=
      pow_le_pow_right₀ hD1 (by rcases hn with rfl | ⟨rfl, -⟩ <;> norm_num)
    rw [hZ, e1, e2]
    have : D ^ 8 * (u ^ 2)⁻¹ * (y ^ (n - 3))⁻¹ =
        D ^ 4 * (y ^ (n - 3))⁻¹ * (D ^ 2 * (u ^ 2)⁻¹ * D ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDn (by positivity))
      (by positivity)
  calc absBr n (Q s) α pp z v ≤ (a + b + c) * Z := hpar
    _ ≤ (a + b + c) * (D ^ 8 * (u ^ 2)⁻¹ * (y ^ (n - 3))⁻¹) :=
        mul_le_mul_of_nonneg_left hZle (by positivity)
    _ = _ := by ring

/-! ### The bulk majorant of the absolute bracket -/

/-- **The absolute bracket on the bulk, with the lower bound tracked**:
`absBr ≤ D (1 + c₁⁻¹)² (c₁ + t u)^{-2}`, `t = z_γ`, for every `c₁ ≤ V₀` (the power counting of
`faceIdRayB_norm_pieceF_le_bulk`). -/
theorem faceIdRayD_absBr_le_bulk {ι : Type*} (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1))
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP : ℝ} (hρ₀ : 0 < ρ₀) (hP : ∀ s l, ‖pp s l‖ ≤ KP) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      z ∈ bulkSet α ρ₀ → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ symanzikV α (pp s) (M s) z → ∀ u : ℝ, 0 ≤ u →
      absBr n (Q s) α (pp s) z (symanzikV α (pp s) (M s) z + z γ₀ * u) ≤
        D * (1 + c₁⁻¹) ^ 2 * ((c₁ + z γ₀ * u) ^ 2)⁻¹ := by
  set B' := max BQ 0 with hB'
  have hB0 : 0 ≤ B' := le_max_right _ _
  have hQ' : LQBdd Q B' := ⟨fun i => (hQ.const i).trans (le_max_left _ _),
    fun i a => (hQ.lin i a).trans (le_max_left _ _),
    fun i a b => (hQ.quad i a b).trans (le_max_left _ _),
    fun i a b c => (hQ.cub i a b c).trans (le_max_left _ _),
    fun i a b c d => (hQ.quart i a b c d).trans (le_max_left _ _)⟩
  set g : ℝ := (ρ₀ ^ 3)⁻¹ with hg
  have hg0 : 0 ≤ g := by positivity
  set K : ℝ := 2 * g * max KP 0 with hK
  have hK0 : 0 ≤ K := by positivity
  set a : ℝ := 6 * (4681 * B' * (1 + K) ^ 4) * g ^ 2
  set b : ℝ := 26176 * B' * (1 + (K + K ^ 2)) * g * g ^ 2
  set c : ℝ := 4096 * B' * (3 * g ^ 2) * g ^ 2
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  refine ⟨a + b + c, by positivity, fun s z hz hz1 hbulk c₁ hc₁ hV u hu => ?_⟩
  have hU3 := symanzikU_ge_bulk hrow z hρ₀ hz hz1 hbulk
  have hU : 0 < symanzikU α z := lt_of_lt_of_le (by positivity) hU3
  have hUi : (symanzikU α z ^ 2)⁻¹ ≤ g ^ 2 := by
    rw [hg, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hU3 2)
  have hgent : ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ g := fun r t => by
    refine (abs_inv_le_chain (α := α) (hα := hrow) (hz := hz) (hU := hU.ne') r t).trans ?_
    rw [← sum_chain hrow z, hz1, hg, one_div]
    exact inv_anti₀ (by positivity) hU3
  have hP' : ∀ l, ‖pp s l‖ ≤ max KP 0 := fun l => (hP s l).trans (le_max_left _ _)
  have hX : ∀ a, ‖loopComp (-loopShift α (pp s) z) a‖ ≤ K := fun a => by
    simp only [loopComp, Complex.norm_real, Real.norm_eq_abs, Pi.neg_apply, abs_neg]
    exact abs_loopShift_le_bulk hrow hz hz1 hP' hgent a.1 a.2
  have key : ∀ {x y : ℝ}, 0 ≤ y → x ≤ y → x / symanzikU α z ^ 2 ≤ y * g ^ 2 := fun hy hxy => by
    rw [div_eq_mul_inv]
    exact mul_le_mul hxy hUi (by positivity) hy
  have hn7 : (n - 4).factorial ≤ (6 : ℝ) ∧ ((n - 5).factorial : ℝ) / 2 ≤ 1 := by
    rcases hn with rfl | ⟨rfl, -⟩ <;> norm_num [Nat.factorial]
  have h1 : ‖cOneAt n (Q s) α (pp s) z‖ ≤ a := by
    refine (norm_cOneAt_le (n := n) (α := α) (z := z) (hK := hK0) (hX := hX) (hU := hU)).trans
      (key (by positivity) ?_)
    exact mul_le_mul hn7.1 (mul_le_mul_of_nonneg_right (lqNorm_le hQ' s) (by positivity))
      (mul_nonneg (lqNorm_nonneg _) (by positivity)) (by norm_num)
  have h2 : ‖cTwoAt n (Q s) α (pp s) z‖ ≤ b := by
    refine (norm_cTwoAt_le (n := n) (α := α) (z := z) (hK := hK0) (hX := hX) (hU := hU)
      (hg := hgent)).trans (key (by positivity) ?_)
    have e : ((n - 5).factorial : ℝ) / 2 * (lqHess (Q s) * (1 + (K + K ^ 2)) * g) ≤
        1 * (26176 * B' * (1 + (K + K ^ 2)) * g) :=
      mul_le_mul hn7.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (lqHess_le hQ' s) (by positivity)) hg0)
        (mul_nonneg (mul_nonneg (lqHess_nonneg _) (by positivity)) hg0) (by norm_num)
    linarith
  have hv0 : 0 < c₁ + z γ₀ * u := by have := hz γ₀; positivity
  have hv : c₁ + z γ₀ * u ≤ symanzikV α (pp s) (M s) z + z γ₀ * u := by linarith
  have hvp : 0 < symanzikV α (pp s) (M s) z + z γ₀ * u := hv0.trans_le hv
  set v := symanzikV α (pp s) (M s) z + z γ₀ * u with hvdef
  have hcv : c₁ ≤ v := by have := hz γ₀; nlinarith
  have hpar : absBr n (Q s) α (pp s) z v ≤ (a + b + c) * (1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹ := by
    rcases hn with rfl | ⟨rfl, hq0⟩
    · have h3 : ‖cThreeAt 7 (Q s) α z‖ ≤ c := by
        refine (norm_cThreeAt_le (n := 7) (α := α) (z := z) (hU := hU) (hg := hgent)).trans
          (key (by positivity) ?_)
        have := lqQuart_le hQ' s
        norm_num [Nat.factorial]
        nlinarith [sq_nonneg g, lqQuart_nonneg (Q s)]
      refine (faceIdRayD_absBr_le_of_coeff (hv := hvp) (h1 := h1) (h2 := h2) (h3 := h3)).trans ?_
      have e4 := inv_pow_le_sq hc₁ hcv (k := 7 - 3) (by norm_num) (by norm_num)
      have e3 := inv_pow_le_sq hc₁ hcv (k := 7 - 4) (by norm_num) (by norm_num)
      have e2 := inv_pow_le_sq hc₁ hcv (k := 7 - 5) (by norm_num) (by norm_num)
      have f4 := mul_le_mul_of_nonneg_left e4 ha
      have f3 := mul_le_mul_of_nonneg_left e3 hb
      have f2 := mul_le_mul_of_nonneg_left e2 hc
      rw [mul_assoc]
      have : (a + b + c) * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) = a * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) +
          b * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) + c * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) := by ring
      linarith
    · have h3 : ‖cThreeAt 6 (Q s) α z‖ ≤ 0 := by
        refine (norm_cThreeAt_le (n := 6) (α := α) (z := z) (hU := hU) (hg := hgent)).trans
          (le_of_eq ?_)
        simp [lqQuart, hq0 s]
      refine (faceIdRayD_absBr_le_of_coeff (hv := hvp) (h1 := h1) (h2 := h2) (h3 := h3)).trans ?_
      have e3 := inv_pow_le_sq hc₁ hcv (k := 6 - 3) (by norm_num) (by norm_num)
      have e2 := inv_pow_le_sq hc₁ hcv (k := 6 - 4) (by norm_num) (by norm_num)
      have hw : 0 ≤ (1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹ := by positivity
      have f3 := mul_le_mul_of_nonneg_left e3 ha
      have f2 := mul_le_mul_of_nonneg_left e2 hb
      have fc : 0 ≤ c * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) := mul_nonneg hc hw
      rw [mul_assoc, zero_mul, add_zero]
      have : (a + b + c) * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) = a * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) +
          b * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) + c * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) := by ring
      linarith
  have hvv : (v ^ 2)⁻¹ ≤ ((c₁ + z γ₀ * u) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hv0.le hv 2)
  exact hpar.trans (mul_le_mul_of_nonneg_left hvv (by positivity))

/-! ### The corner and bulk sectors of a dominated family -/

/-- **The loop-UV corner of a family dominated by `K z_γ absBr`, with rate `u^{-1}`**. -/
theorem faceIdRayD_corner_rate {ι : Type*} {n : ℕ} (hm : n - 3 < m)
    (α : Fin (m + 1) → Fin 2 → ℝ) (γ₀ : Fin (m + 1)) (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (cs : Fin (m + 1) → ℝ) (k : ι → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hk : ∀ s μ, |k s μ| ≤ KP)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → w ∈ cornerSet α ρ₀ →
      symanzikU α w ≠ 0 → 0 ≤ symanzikV α (fun i => cs i • k s) (M s) w)
    (F : ι → ℝ → (Fin (m + 1) → ℝ) → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ s u (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → 1 ≤ u →
      ‖F s u w‖ ≤ K * (w γ₀ * absBr n (Q s) α (fun i => cs i • k s) w
        (symanzikV α (fun i => cs i • k s) (M s) w + w γ₀ * u))) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 1 ≤ u →
      ‖u • ∫ x in simplexSet m, (cornerSet α ρ₀).indicator (F s u) (simplexPoint x)‖ ≤
        C * u⁻¹ := by
  obtain ⟨E, hE, hEb⟩ := faceIdRayD_absBr_le_corner α γ₀ huniq hrow cs k M n Q hQ hn hρ₀ hρ₁ hk
  have hm0 : 0 < m := by omega
  have hI := integrableOn_one_sub_simplexPoint_rpow hm0 γ₀ (q := ((n - 3 : ℕ) : ℝ))
    (Nat.cast_nonneg _) (by exact_mod_cast hm)
  set I := ∫ x in simplexSet m, (1 - simplexPoint x γ₀) ^ (-((n - 3 : ℕ) : ℝ))
  refine ⟨K * E * I, fun s u hu => ?_⟩
  have hu0 : 0 < u := one_pos.trans_le hu
  have hg : ∀ x ∈ simplexSet m, ‖u • (cornerSet α ρ₀).indicator (F s u) (simplexPoint x)‖ ≤
      K * E * u⁻¹ * (1 - simplexPoint x γ₀) ^ (-((n - 3 : ℕ) : ℝ)) := by
    intro x hx
    obtain ⟨hz, hz1⟩ := simplexPoint_mem_stdSimplex hx
    have hy : ferSum α (simplexPoint x) = 1 - simplexPoint x γ₀ := ferSum_eq_one_sub huniq hz1
    have hy0 : 0 ≤ 1 - simplexPoint x γ₀ := by
      rw [← hy]; exact Finset.sum_nonneg fun l _ => hz l
    have hR : 0 ≤ K * E * u⁻¹ * (1 - simplexPoint x γ₀) ^ (-((n - 3 : ℕ) : ℝ)) := by
      positivity
    by_cases hb : simplexPoint x ∈ cornerSet α ρ₀
    · rw [indicator_of_mem hb, norm_smul, Real.norm_of_nonneg hu0.le]
      have ht1 : simplexPoint x γ₀ ≤ 1 := by linarith
      set zx := simplexPoint x
      set A := absBr n (Q s) α (fun i => cs i • k s) zx
        (symanzikV α (fun i => cs i • k s) (M s) zx + zx γ₀ * u)
      have hA := hEb s _ hz hz1 hb (hV s _ hz hz1 hb) u hu
      have hA0 : 0 ≤ A := by
        by_cases hU : symanzikU α zx = 0
        · exact (faceIdRayD_absBr_eq_zero hU).symm.le
        · refine faceIdRayD_absBr_nonneg ?_
          have := hV s _ hz hz1 hb hU
          have := mul_nonneg (hz γ₀) hu0.le
          linarith
      have h1 := hF s u _ hz hz1 hu
      have h2 : zx γ₀ * A ≤ A := mul_le_of_le_one_left hA0 ht1
      calc u * ‖F s u zx‖ ≤ u * (K * (E * (u ^ 2)⁻¹ * (ferSum α zx ^ (n - 3))⁻¹)) :=
            mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left (h2.trans hA) hK))
              hu0.le
        _ = _ := by
            rw [hy, Real.rpow_neg hy0, Real.rpow_natCast]
            field_simp
    · rw [indicator_of_notMem hb, smul_zero, norm_zero]
      exact hR
  rw [← integral_smul]
  refine (norm_integral_le_of_norm_le (hI.const_mul (K * E * u⁻¹))
    (ae_restrict_of_forall_mem (measurableSet_simplexSet m) hg)).trans (le_of_eq ?_)
  rw [integral_const_mul]
  ring

/-- **The bulk sector of a family dominated by `K z_γ absBr`, with rate
`C (1 + c₁⁻¹)³ u^{-1/2}`** (`V₀ ≥ c₁ s` on the bulk, per member). -/
theorem faceIdRayD_bulk_rate {ι : Type*} (hm : 0 < m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1)) (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP : ℝ} (hρ₀ : 0 < ρ₀) (hP : ∀ s l, ‖pp s l‖ ≤ KP) (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → w ∈ bulkSet α ρ₀ →
      c₁ s ≤ symanzikV α (pp s) (M s) w)
    (F : ι → ℝ → (Fin (m + 1) → ℝ) → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ s u (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → 0 < u →
      ‖F s u w‖ ≤ K * (w γ₀ * absBr n (Q s) α (pp s) w
        (symanzikV α (pp s) (M s) w + w γ₀ * u))) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      ‖u • ∫ x in simplexSet m, (bulkSet α ρ₀).indicator (F s u) (simplexPoint x)‖ ≤
        C * (1 + (c₁ s)⁻¹) ^ 3 * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨D, hD, hDb⟩ := faceIdRayD_absBr_le_bulk α γ₀ hrow pp M n Q hQ hn hρ₀ hP
  have hI := integrableOn_simplexPoint_rpow hm γ₀
  set I := ∫ x in simplexSet m, simplexPoint x γ₀ ^ (-(1 / 2) : ℝ)
  refine ⟨K * D * |I|, fun s u hu => ?_⟩
  set c := c₁ s
  have hc := hc₁ s
  set D' := K * D * (1 + c⁻¹) ^ 2
  have hD' : 0 ≤ D' := by positivity
  have hg : ∀ x ∈ simplexSet m, ‖u • (bulkSet α ρ₀).indicator (F s u) (simplexPoint x)‖ ≤
      D' * c ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) * simplexPoint x γ₀ ^ (-(1 / 2) : ℝ) := by
    intro x hx
    obtain ⟨hz, hz1⟩ := simplexPoint_mem_stdSimplex hx
    have hR : 0 ≤ D' * c ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) *
        simplexPoint x γ₀ ^ (-(1 / 2) : ℝ) := by
      have := hz γ₀
      positivity
    by_cases hb : simplexPoint x ∈ bulkSet α ρ₀
    · rw [indicator_of_mem hb, norm_smul, Real.norm_of_nonneg hu.le]
      have h1 := hF s u _ hz hz1 hu
      rcases (hz γ₀).eq_or_lt with ht | ht
      · rw [← ht, zero_mul, mul_zero] at h1
        rw [le_antisymm h1 (norm_nonneg _), mul_zero]
        exact hR
      · have h2 := hDb s _ hz hz1 hb c hc (hV s _ hz hz1 hb) u hu.le
        have h3 : ‖F s u (simplexPoint x)‖ ≤ simplexPoint x γ₀ *
            (D' * ((c + simplexPoint x γ₀ * u) ^ 2)⁻¹) := by
          refine h1.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h2 ht.le) hK) ?_)
          simp only [D']; ring
        refine (mul_le_mul_of_nonneg_left h3 hu.le).trans ?_
        have := bulk_scalar ht hu hc hD'
        linarith
    · rw [indicator_of_notMem hb, smul_zero, norm_zero]
      exact hR
  rw [← integral_smul]
  refine (norm_integral_le_of_norm_le ((hI.const_mul (D' * c ^ (-(1 / 2) : ℝ) *
    u ^ (-(1 / 2) : ℝ)))) (ae_restrict_of_forall_mem (measurableSet_simplexSet m) hg)).trans ?_
  rw [integral_const_mul]
  have hr := faceIdRayB_rpow_le hc
  have hu' : 0 ≤ u ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hu.le _
  have hc' : 0 ≤ c ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hc.le _
  have h1 : D' * c ^ (-(1 / 2) : ℝ) ≤ K * D * (1 + c⁻¹) ^ 3 :=
    (mul_le_mul_of_nonneg_left hr hD').trans (le_of_eq (by simp only [D']; ring))
  calc D' * c ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) * I
      ≤ D' * c ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) * |I| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ ≤ K * D * (1 + c⁻¹) ^ 3 * u ^ (-(1 / 2) : ℝ) * |I| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hu') (abs_nonneg _)
    _ = K * D * |I| * (1 + c⁻¹) ^ 3 * u ^ (-(1 / 2) : ℝ) := by ring

end QED.GradedProof.RPi4

end
