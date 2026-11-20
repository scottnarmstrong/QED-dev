/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4BulkRate

/-!
# (R-Π₄) step L6d1: the loop-UV corner, with rate `u^{-1}`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d1. In the corner
`cornerSet α ρ₀ = {ferSum ≤ ρ₀}` of a collapsed piece with a unique photon line `γ₀` the photon
weight is `t = 1 - y ≥ 1 - ρ₀` (`y = ferSum`), so `U ≥ t y ≥ (1 - ρ₀) y`, every entry of `A⁻¹` is
at most `1/U`, the shift is bounded (momenta proportional to one external momentum) and
`v = V₀ + t u ≥ (1 - ρ₀) u` when `V₀ ≥ 0`. Power counting then gives
`‖pieceF‖ ≤ E u^{-2} y^{-(n-3)}` for `u ≥ 1` (`norm_pieceF_le_corner`), and `y^{-(n-3)}` is
integrable on the simplex when `n - 3 < m`, so `u` times the corner integral is `O(u^{-1})`
(`corner_rate`). No subtraction at `s = 0` is needed at the level of the density.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)
open QED.Integration.SimplexMerge (integrableOn_simplex_comp_perm_iff)

variable {m : ℕ}

/-- **The loop-UV corner of a piece**: the fermion lines carry weight at most `ρ₀`. -/
def cornerSet (α : Fin (m + 1) → Fin 2 → ℝ) (ρ₀ : ℝ) : Set (Fin (m + 1) → ℝ) :=
  {z | ferSum α z ≤ ρ₀}

/-- With a unique photon line `γ₀`, `ferSum = 1 - z_γ` on the simplex. -/
theorem ferSum_eq_one_sub {α : Fin (m + 1) → Fin 2 → ℝ} {γ₀ : Fin (m + 1)}
    (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀) {z : Fin (m + 1) → ℝ} (hz1 : ∑ l, z l = 1) :
    ferSum α z = 1 - z γ₀ := by
  have e : ∀ l, z l = (if α l ≠ ![1, -1] then z l else 0) + (if γ₀ = l then z l else 0) :=
    fun l => by
      by_cases h : l = γ₀
      · subst h; simp [(huniq l).mpr rfl]
      · simp [(huniq l).not.mpr h, Ne.symm h]
  have hs : ∑ l, z l = ferSum α z + z γ₀ :=
    calc ∑ l, z l = ∑ l, ((if α l ≠ ![1, -1] then z l else 0) + (if γ₀ = l then z l else 0)) :=
          Finset.sum_congr rfl fun l _ => e l
      _ = ferSum α z + z γ₀ := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ferSum, Finset.sum_filter]
          simp
  linarith

/-- **`U` on the corner**: `U ≥ z_γ · ferSum`. -/
theorem symanzikU_ge_corner {α : Fin (m + 1) → Fin 2 → ℝ} {γ₀ : Fin (m + 1)}
    (hγ : α γ₀ = ![1, -1]) (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    {z : Fin (m + 1) → ℝ} (hz : ∀ l, 0 ≤ z l) : z γ₀ * ferSum α z ≤ symanzikU α z := by
  have h3 : z γ₀ ≤ chainZ α z ![1, -1] := by
    rw [chainZ]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i =>
      if α i = ![1, -1] then z i else 0) (fun i _ => by split_ifs <;> simp [hz i])
      (Finset.mem_univ γ₀))
    simp [hγ]
  have hU := symanzikU_ge_chain α hz hrow
  rw [ferSum_chain hrow]
  have := add_nonneg (chainZ_nonneg α hz ![1, 0]) (chainZ_nonneg α hz ![0, 1])
  nlinarith

/-- `U = 0` where the fermion weight vanishes. -/
theorem symanzikU_eq_zero_of_ferSum {α : Fin (m + 1) → Fin 2 → ℝ}
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    {z : Fin (m + 1) → ℝ} (hz : ∀ l, 0 ≤ z l) (h : ferSum α z = 0) : symanzikU α z = 0 := by
  rw [ferSum_chain hrow] at h
  have h1 := chainZ_nonneg α hz ![1, 0]
  have h2 := chainZ_nonneg α hz ![0, 1]
  have e1 : chainZ α z ![1, 0] = 0 := by linarith
  have e2 : chainZ α z ![0, 1] = 0 := by linarith
  rw [symanzikU_chain α z hrow, e1, e2]
  ring

theorem pieceF_eq_zero_of_U {n : ℕ} {Q : LoopQuartic} {α : Fin (m + 1) → Fin 2 → ℝ}
    {pp : Fin (m + 1) → Fin 4 → ℝ} {M : Fin (m + 1) → ℝ} {γ₀ : Fin (m + 1)} {u : ℝ}
    {z : Fin (m + 1) → ℝ} (h : symanzikU α z = 0) : pieceF n Q α pp M γ₀ u z = 0 := by
  rw [pieceF, paramAtV_eq]
  simp [cOneAt, cTwoAt, cThreeAt, h]

/-- The scalar power-counting step: `X^j w^i ≤ P^N R² D²` for `X ≤ P`, `1 ≤ P`, `j ≤ N`,
`w ≤ R ≤ D`, `1 ≤ D`, `2 ≤ i ≤ 4`. -/
theorem corner_term {X P w R D : ℝ} (hX0 : 0 ≤ X) (hXP : X ≤ P) (hP : 1 ≤ P) (hw0 : 0 ≤ w)
    (hwR : w ≤ R) (hRD : R ≤ D) (hD : 1 ≤ D) {i j N : ℕ} (hj : j ≤ N) (hi2 : 2 ≤ i)
    (hi4 : i ≤ 4) : X ^ j * w ^ i ≤ P ^ N * (R ^ 2 * D ^ 2) := by
  have hR0 : 0 ≤ R := hw0.trans hwR
  have h1 : X ^ j ≤ P ^ N :=
    (pow_le_pow_left₀ hX0 hXP j).trans (pow_le_pow_right₀ hP hj)
  obtain ⟨l, rfl⟩ : ∃ l, i = 2 + l := ⟨i - 2, by omega⟩
  have h2 : w ^ (2 + l) ≤ R ^ 2 * D ^ 2 := by
    rw [pow_add]
    refine mul_le_mul (pow_le_pow_left₀ hw0 hwR 2) ((pow_le_pow_left₀ hw0 (hwR.trans hRD) l).trans
      (pow_le_pow_right₀ hD (by omega))) (by positivity) (by positivity)
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **The collapsed integrand on the corner**: `‖pieceF‖ ≤ E u^{-2} ferSum^{-(n-3)}` for
`u ≥ 1`, with `E` uniform over the family (momenta `cs • k`, `|k| ≤ KP`). -/
theorem norm_pieceF_le_corner {ι : Type*} (α : Fin (m + 1) → Fin 2 → ℝ) (γ₀ : Fin (m + 1))
    (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (cs : Fin (m + 1) → ℝ) (k : ι → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hk : ∀ s μ, |k s μ| ≤ KP) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ s (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      z ∈ cornerSet α ρ₀ →
      (symanzikU α z ≠ 0 → 0 ≤ symanzikV α (fun i => cs i • k s) (M s) z) →
      ∀ u : ℝ, 1 ≤ u →
      ‖pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u z‖ ≤
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
  · rw [pieceF_eq_zero_of_U (symanzikU_eq_zero_of_ferSum hrow hz hy0'.symm), norm_zero, ← hy0',
      zero_pow (by omega), inv_zero, mul_zero]
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
  have hpar : ‖paramAtV n (Q s) α pp z v‖ ≤ (a + b + c) * Z := by
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
      refine (norm_paramAtV_le_of_coeff (hv := hvp) (h1 := h1) (h2 := h2) (h3 := h3)).trans ?_
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
      refine (norm_paramAtV_le_of_coeff (hv := hvp) (h1 := h1) (h2 := h2) (h3 := h3)).trans ?_
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
  have ht1 : z γ₀ ≤ 1 := by rw [ht]; linarith
  rw [pieceF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hz γ₀)]
  calc z γ₀ * ‖paramAtV n (Q s) α pp z v‖ ≤ 1 * ((a + b + c) * Z) :=
        mul_le_mul ht1 hpar (norm_nonneg _) zero_le_one
    _ ≤ (a + b + c) * (D ^ 8 * (u ^ 2)⁻¹ * (y ^ (n - 3))⁻¹) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_left hZle (by positivity)
    _ = _ := by ring

/-- `(1 - z_γ)^{-q}` is integrable on the simplex for `q < m`. -/
theorem integrableOn_one_sub_simplexPoint_rpow (hm : 0 < m) (γ : Fin (m + 1)) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q < m) :
    IntegrableOn (fun x => (1 - simplexPoint x γ) ^ (-q)) (simplexSet m) := by
  refine (integrableOn_simplex_comp_perm_iff (Equiv.swap γ (Fin.last m))
    (fun w : Fin (m + 1) → ℝ => (1 - w γ) ^ (-q))).mp ?_
  have hh := integrableOn_headSum_rpow (m := m) (n := m) le_rfl hm hq0 hq
  refine hh.congr_fun (fun x _ => ?_) (measurableSet_simplexSet m)
  simp only [Function.comp, Equiv.swap_apply_left, simplexPoint_last, headSum, Fin.is_lt,
    ite_true]
  ring_nf

/-- **The loop-UV corner of a family of collapsed pieces, with rate `u^{-1}` uniform over the
family**: `‖u ∫_{corner} pieceF‖ ≤ C u^{-1}` for `u ≥ 1` (`n - 3 < m`; `V₀ ≥ 0` on the
corner). -/
theorem corner_rate {ι : Type*} {n : ℕ} (hm : n - 3 < m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1)) (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (cs : Fin (m + 1) → ℝ) (k : ι → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hk : ∀ s μ, |k s μ| ≤ KP)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → w ∈ cornerSet α ρ₀ →
      symanzikU α w ≠ 0 → 0 ≤ symanzikV α (fun i => cs i • k s) (M s) w) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 1 ≤ u →
      ‖u • ∫ x in simplexSet m, (cornerSet α ρ₀).indicator
          (pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u) (simplexPoint x)‖ ≤ C * u⁻¹ := by
  obtain ⟨E, hE, hEb⟩ := norm_pieceF_le_corner α γ₀ huniq hrow cs k M n Q hQ hn hρ₀ hρ₁ hk
  have hm0 : 0 < m := by omega
  have hI := integrableOn_one_sub_simplexPoint_rpow hm0 γ₀ (q := ((n - 3 : ℕ) : ℝ))
    (Nat.cast_nonneg _) (by exact_mod_cast hm)
  set I := ∫ x in simplexSet m, (1 - simplexPoint x γ₀) ^ (-((n - 3 : ℕ) : ℝ))
  refine ⟨E * I, fun s u hu => ?_⟩
  have hu0 : 0 < u := one_pos.trans_le hu
  have hg : ∀ x ∈ simplexSet m, ‖u • (cornerSet α ρ₀).indicator
      (pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u) (simplexPoint x)‖ ≤
      E * u⁻¹ * (1 - simplexPoint x γ₀) ^ (-((n - 3 : ℕ) : ℝ)) := by
    intro x hx
    obtain ⟨hz, hz1⟩ := simplexPoint_mem_stdSimplex hx
    have hy : ferSum α (simplexPoint x) = 1 - simplexPoint x γ₀ := ferSum_eq_one_sub huniq hz1
    have hy0 : 0 ≤ 1 - simplexPoint x γ₀ := by
      rw [← hy]; exact Finset.sum_nonneg fun l _ => hz l
    have hR : 0 ≤ E * u⁻¹ * (1 - simplexPoint x γ₀) ^ (-((n - 3 : ℕ) : ℝ)) := by positivity
    by_cases hb : simplexPoint x ∈ cornerSet α ρ₀
    · rw [indicator_of_mem hb, norm_smul, Real.norm_of_nonneg hu0.le]
      refine (mul_le_mul_of_nonneg_left (hEb s _ hz hz1 hb (hV s _ hz hz1 hb) u hu)
        hu0.le).trans (le_of_eq ?_)
      rw [hy, Real.rpow_neg hy0, Real.rpow_natCast]
      field_simp
    · rw [indicator_of_notMem hb, smul_zero, norm_zero]
      exact hR
  rw [← integral_smul]
  refine (norm_integral_le_of_norm_le (hI.const_mul (E * u⁻¹))
    (ae_restrict_of_forall_mem (measurableSet_simplexSet m) hg)).trans (le_of_eq ?_)
  rw [integral_const_mul]
  ring

end QED.GradedProof.RPi4

end
