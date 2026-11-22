/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntVMaj
public import QED.GradedProof.X0NsAmp

/-!
# Line factors at complex momenta

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58), classes `VA`, `VB`, `VC`. A line factor of the three-loop line theorem is
`N(k) ∏_{M ∈ ms} D_M(k)⁻¹` with `N` an `AffPoly d` numerator
(`QED.GradedProof.X0.AffPoly`). This file extends it to complex momenta and bounds it at the
energies rotated by `z` (`QED.ChainProof.RepsIntBB`):

* `AffPoly.exists_cx`: `N` is the restriction of an entire `N^c` with
  `‖N^c(w)‖ ≤ C (1 + ‖w‖)^d`;
* `dProdC`: the product of inverse complex denominators `denC M ε`; `dProdC_cv` (real
  momenta), `differentiableAt_dProdC`, `norm_dProdC_le`;
* `norm_factor_rect`: on the rectangle `rotRect h`, at fixed spatial momentum, the factor at
  energy `z t + a` is `≤ K (1 + |t|)^{-(2|ms| - d)}`;
* `norm_factor_rot`: at `z = 1 + s i` it is `≤ K (1 + ‖(t, ŷ)‖)^{-(2|ms| - d)}` for all
  `t` and spatial `ŷ` (shifted by `q⃗`), with `K` independent of both.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetALinkV

open QED.ChainProof.RepsIntBB QED.GradedProof.X0 QED.Integration.ThreeLoop

/-! ### Complex numerators -/

theorem norm_apply_le_one_add (w : Fin 4 → ℂ) (ν : Fin 4) : ‖w ν‖ ≤ 1 + ‖w‖ := by
  linarith [norm_le_pi_norm w ν]

/-- **An `AffPoly` numerator extends to complex momenta**, polynomially bounded. -/
theorem AffPoly.exists_cx {d : ℕ} {N : (Fin 4 → ℝ) → ℂ} (h : AffPoly d N) :
    ∃ Nc : (Fin 4 → ℂ) → ℂ, (∀ k, Nc (cv k) = N k) ∧ Differentiable ℂ Nc ∧
      ∃ C, 0 ≤ C ∧ ∀ w, ‖Nc w‖ ≤ C * (1 + ‖w‖) ^ d := by
  induction h with
  | const z => exact ⟨fun _ => z, fun _ => rfl, differentiable_const _, ‖z‖, norm_nonneg _,
      fun w => by simp⟩
  | aff u w =>
    refine ⟨fun v => u + ∑ ν, w ν * v ν, fun k => by simp [cv], ?_, ‖u‖ + ∑ ν, ‖w ν‖,
      by positivity, fun v => ?_⟩
    · exact (differentiable_const _).add (Differentiable.fun_sum fun ν _ =>
        (differentiable_const _).mul (differentiable_apply ν))
    · have hs : ‖∑ ν, w ν * v ν‖ ≤ ∑ ν, ‖w ν‖ * (1 + ‖v‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_apply_le_one_add v ν) (norm_nonneg _))
      have h1 : ‖u + ∑ ν, w ν * v ν‖ ≤ ‖u‖ + ∑ ν, ‖w ν‖ * (1 + ‖v‖) :=
        (norm_add_le _ _).trans (by linarith)
      have h2 : 1 ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
      show ‖u + ∑ ν, w ν * v ν‖ ≤ _
      rw [pow_one, add_mul, Finset.sum_mul]
      nlinarith [norm_nonneg u]
  | mul _ _ ih ih' =>
    obtain ⟨N₁, e₁, d₁, C₁, hC₁, b₁⟩ := ih
    obtain ⟨N₂, e₂, d₂, C₂, hC₂, b₂⟩ := ih'
    refine ⟨fun v => N₁ v * N₂ v, fun k => by simp [e₁, e₂], d₁.mul d₂, C₁ * C₂,
      mul_nonneg hC₁ hC₂, fun v => ?_⟩
    rw [norm_mul, pow_add]
    calc ‖N₁ v‖ * ‖N₂ v‖ ≤ (C₁ * (1 + ‖v‖) ^ _) * (C₂ * (1 + ‖v‖) ^ _) :=
          mul_le_mul (b₁ v) (b₂ v) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  | add _ _ ih ih' =>
    obtain ⟨N₁, e₁, d₁, C₁, hC₁, b₁⟩ := ih
    obtain ⟨N₂, e₂, d₂, C₂, hC₂, b₂⟩ := ih'
    refine ⟨fun v => N₁ v + N₂ v, fun k => by simp [e₁, e₂], d₁.add d₂, C₁ + C₂,
      add_nonneg hC₁ hC₂, fun v => ?_⟩
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add (b₁ v) (b₂ v))
  | mono hd _ ih =>
    obtain ⟨N₁, e₁, d₁, C₁, hC₁, b₁⟩ := ih
    refine ⟨N₁, e₁, d₁, C₁, hC₁, fun v => (b₁ v).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg v]) hd) hC₁

/-! ### Complex denominators -/

/-- The product of the inverse complex denominators with the masses of a list. -/
noncomputable def dProdC (ε : ℝ) (ms : List ℝ) (w : Fin 4 → ℂ) : ℂ :=
  (ms.map fun M => (denC M ε w)⁻¹).prod

theorem dProdC_cv (ε : ℝ) (ms : List ℝ) (k : Fin 4 → ℝ) :
    dProdC ε ms (cv k) = dProd ε ms k := by
  induction ms with
  | nil => simp [dProdC, dProd]
  | cons M ms ih =>
    simp only [dProdC, dProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, denC_cv]
    rfl

theorem differentiable_denC (M ε : ℝ) : Differentiable ℂ (denC M ε) := by
  unfold denC
  exact (differentiable_dotC.add (differentiable_const _)).sub (differentiable_const _)

theorem differentiableAt_dProdC (ε : ℝ) (ms : List ℝ) {w : Fin 4 → ℂ}
    (h : ∀ M, denC M ε w ≠ 0) : DifferentiableAt ℂ (dProdC ε ms) w := by
  induction ms with
  | nil =>
    have e : dProdC ε [] = fun _ => 1 := by funext w; simp [dProdC]
    rw [e]
    exact differentiableAt_const _
  | cons M ms ih =>
    have e : dProdC ε (M :: ms) = fun w => (denC M ε w)⁻¹ * dProdC ε ms w := by
      funext w; simp [dProdC]
    rw [e]
    exact ((differentiable_denC M ε w).inv (h M)).mul ih

theorem norm_dProdC_le (ε : ℝ) (ms : List ℝ) (w : Fin 4 → ℂ) (K : ℝ → ℝ) {u : ℝ}
    (hu : 0 ≤ u) (hK : ∀ M, 0 ≤ K M) (h : ∀ M, ‖(denC M ε w)⁻¹‖ ≤ K M * u) :
    ‖dProdC ε ms w‖ ≤ (ms.map K).prod * u ^ ms.length := by
  induction ms with
  | nil => simp [dProdC]
  | cons M ms ih =>
    simp only [dProdC, List.map_cons, List.prod_cons, List.length_cons, pow_succ] at ih ⊢
    rw [norm_mul]
    have hP : 0 ≤ (ms.map K).prod := List.prod_nonneg fun x hx => by
      obtain ⟨M', -, rfl⟩ := List.mem_map.mp hx
      exact hK M'
    calc ‖(denC M ε w)⁻¹‖ * ‖(ms.map fun M => (denC M ε w)⁻¹).prod‖
        ≤ (K M * u) * ((ms.map K).prod * u ^ ms.length) :=
          mul_le_mul (h M) ih (norm_nonneg _) (mul_nonneg (hK M) hu)
      _ = _ := by ring

theorem prod_map_nonneg (ms : List ℝ) {K : ℝ → ℝ} (hK : ∀ M, 0 ≤ K M) :
    0 ≤ (ms.map K).prod := List.prod_nonneg fun x hx => by
  obtain ⟨M', -, rfl⟩ := List.mem_map.mp hx
  exact hK M'

/-! ### Norms of complex momenta -/

theorem norm_mk_le (X : ℂ) (y : Fin 3 → ℝ) : ‖mk X y‖ ≤ ‖X‖ + ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [mk_zero]
    linarith [norm_nonneg y]
  · have : ‖mk X y j.succ‖ = ‖y j‖ := by simp [RepsIntBB.mk, Real.norm_eq_abs]
    rw [this]
    linarith [norm_le_pi_norm y j, norm_nonneg X]

theorem norm_le_three_of_mem_rotRect {z : ℂ} {h : ℝ} (hz : z ∈ rotRect h) (hh : h ≤ 1) :
    ‖z‖ ≤ 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg (by linarith), abs_of_nonneg h3] at this
  linarith

theorem one_add_abs_sq_le (t : ℝ) : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
  nlinarith [sq_abs t, sq_nonneg (1 - |t|)]

/-! ### The factor bounds -/

theorem inv_pow_sub_mul {u : ℝ} (hu : 0 < u) {d n : ℕ} (hd : d ≤ n) :
    u ^ d * (u ^ n)⁻¹ = (u ^ (n - d))⁻¹ := by
  rw [show n = d + (n - d) by omega, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀
    (pow_pos hu _).ne', one_mul, Nat.add_sub_cancel_left]

/-- **The factor on the rectangle** at fixed spatial momentum. -/
theorem norm_factor_rect {Nc : (Fin 4 → ℂ) → ℂ} {C : ℝ} {d : ℕ} (hC0 : 0 ≤ C)
    (hN : ∀ w, ‖Nc w‖ ≤ C * (1 + ‖w‖) ^ d) (ms : List ℝ) (hd : d ≤ 2 * ms.length)
    {h a ε : ℝ} (hh : h ≤ 1) (hε : 0 < ε) (ha : h * a ^ 2 ≤ ε / 4) (y : Fin 3 → ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ z ∈ rotRect h, ∀ t : ℝ,
      ‖Nc (mk (z * t + a) y) * dProdC ε ms (mk (z * t + a) y)‖ ≤
        K * ((1 + |t|) ^ (2 * ms.length - d))⁻¹ := by
  set B := 4 + |a| + ‖y‖
  set Kd : ℝ → ℝ := fun M => 2 * kRect a (sq3 y + M ^ 2) ε
  have hKd : ∀ M, 0 ≤ Kd M := fun M => by
    have := kRect_pos (a := a) (add_nonneg (sq3_nonneg y) (sq_nonneg M)) hε
    simp only [Kd]
    positivity
  refine ⟨C * B ^ d * (ms.map Kd).prod, by
    have := prod_map_nonneg ms hKd; positivity, fun z hz t => ?_⟩
  have ht : 0 < 1 + |t| := by positivity
  have hm : 1 + ‖mk (z * t + a) y‖ ≤ B * (1 + |t|) := by
    have h1 := norm_mk_le (z * t + a) y
    have h2 : ‖z * t + a‖ ≤ 3 * |t| + |a| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      nlinarith [norm_le_three_of_mem_rotRect hz hh, abs_nonneg t]
    have : 0 ≤ ‖y‖ := norm_nonneg y
    nlinarith [abs_nonneg t, abs_nonneg a]
  have hden : ∀ M, ‖(denC M ε (mk (z * t + a) y))⁻¹‖ ≤ Kd M * ((1 + |t|) ^ 2)⁻¹ := by
    intro M
    refine (norm_inv_denC_rect hz hε ha M y t rfl).trans ?_
    have hk := kRect_pos (a := a) (add_nonneg (sq3_nonneg y) (sq_nonneg M)) hε
    have h2 : (1 + t ^ 2)⁻¹ ≤ 2 * ((1 + |t|) ^ 2)⁻¹ := by
      calc (1 + t ^ 2)⁻¹ ≤ ((1 + |t|) ^ 2 / 2)⁻¹ :=
            inv_anti₀ (by positivity) (by linarith [one_add_abs_sq_le t])
        _ = 2 * ((1 + |t|) ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
    rw [div_eq_mul_inv]
    have := mul_le_mul_of_nonneg_left h2 hk.le
    simp only [Kd]
    linarith
  have hD := norm_dProdC_le ε ms (mk (z * t + a) y) Kd (by positivity) hKd hden
  rw [norm_mul]
  calc ‖Nc (mk (z * t + a) y)‖ * ‖dProdC ε ms (mk (z * t + a) y)‖
      ≤ (C * (B * (1 + |t|)) ^ d) * ((ms.map Kd).prod * ((1 + |t|) ^ 2)⁻¹ ^ ms.length) :=
        mul_le_mul ((hN _).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hm _) hC0)) hD (norm_nonneg _)
          (by have := prod_map_nonneg ms hKd; positivity)
    _ = C * B ^ d * (ms.map Kd).prod * ((1 + |t|) ^ d * ((1 + |t|) ^ (2 * ms.length))⁻¹) := by
        rw [mul_pow, inv_pow, ← pow_mul]
        ring
    _ = _ := by rw [inv_pow_sub_mul ht hd]

/-- **The factor at the rotated energies** `(1 + s i) t`, for all momenta. -/
theorem norm_factor_rot {Nc : (Fin 4 → ℂ) → ℂ} {C : ℝ} {d : ℕ} (hC0 : 0 ≤ C)
    (hN : ∀ w, ‖Nc w‖ ≤ C * (1 + ‖w‖) ^ d) (ms : List ℝ) (hd : d ≤ 2 * ms.length)
    {s a ε : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 < ε) (ha : s * a ^ 2 ≤ ε / 4)
    (qs : Fin 3 → ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ (t : ℝ) (yh : Fin 3 → ℝ),
      ‖Nc (mk ((1 + s * I) * t + a) (yh + qs)) * dProdC ε ms (mk ((1 + s * I) * t + a)
        (yh + qs))‖ ≤ K * ((1 + ‖(Fin.cons t yh : Fin 4 → ℝ)‖) ^ (2 * ms.length - d))⁻¹ := by
  set Q := 1 + ‖qs‖
  set Kd : ℝ → ℝ := fun _ => 3 * kRot s a ε
  have hKd : ∀ M, 0 ≤ Kd M := fun M => by
    have := kRot_pos (a := a) hs hε; simp only [Kd]; positivity
  have hQ : 1 ≤ Q := by simp only [Q]; linarith [norm_nonneg qs]
  refine ⟨C * (2 + |a|) ^ d * (ms.map Kd).prod * Q ^ (2 * ms.length - d), by
    have := prod_map_nonneg ms hKd; positivity, fun t yh => ?_⟩
  set y := yh + qs
  set S := 1 + |t| + ‖y‖
  have hS : 0 < S := by positivity
  have hm : 1 + ‖mk ((1 + s * I) * t + a) y‖ ≤ (2 + |a|) * S := by
    have h1 := norm_mk_le ((1 + s * I) * t + a) y
    have hz : ‖(1 + s * I : ℂ)‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_of_pos hs]
      linarith
    have h2 : ‖(1 + s * I) * t + a‖ ≤ 2 * |t| + |a| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      nlinarith [abs_nonneg t]
    have : 0 ≤ ‖y‖ := norm_nonneg y
    simp only [S]
    nlinarith [abs_nonneg t, abs_nonneg a]
  have hden : ∀ M, ‖(denC M ε (mk ((1 + s * I) * t + a) y))⁻¹‖ ≤ Kd M * (S ^ 2)⁻¹ := by
    intro M
    refine (norm_inv_denC_rot hs hε ha M y t rfl).trans (le_of_eq ?_)
    simp only [Kd, S, div_eq_mul_inv]
  have hD := norm_dProdC_le ε ms (mk ((1 + s * I) * t + a) y) Kd (by positivity) hKd hden
  have hν : 1 + ‖(Fin.cons t yh : Fin 4 → ℝ)‖ ≤ Q * S := by
    have h1 := norm_cons_le t yh
    have h2 : ‖yh‖ ≤ ‖y‖ + ‖qs‖ := by
      have := norm_sub_le y qs
      simpa [y] using this
    have : 0 ≤ ‖y‖ := norm_nonneg y
    simp only [Q, S]
    nlinarith [abs_nonneg t, norm_nonneg qs]
  have hn : 0 < 1 + ‖(Fin.cons t yh : Fin 4 → ℝ)‖ := by positivity
  rw [norm_mul]
  calc ‖Nc (mk ((1 + s * I) * t + a) y)‖ * ‖dProdC ε ms (mk ((1 + s * I) * t + a) y)‖
      ≤ (C * ((2 + |a|) * S) ^ d) * ((ms.map Kd).prod * (S ^ 2)⁻¹ ^ ms.length) :=
        mul_le_mul ((hN _).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hm _) hC0)) hD (norm_nonneg _)
          (by have := prod_map_nonneg ms hKd; positivity)
    _ = C * (2 + |a|) ^ d * (ms.map Kd).prod * (S ^ d * (S ^ (2 * ms.length))⁻¹) := by
        rw [mul_pow, inv_pow, ← pow_mul]
        ring
    _ = C * (2 + |a|) ^ d * (ms.map Kd).prod * (S ^ (2 * ms.length - d))⁻¹ := by
        rw [inv_pow_sub_mul hS hd]
    _ ≤ C * (2 + |a|) ^ d * (ms.map Kd).prod *
          (Q ^ (2 * ms.length - d) * ((1 + ‖(Fin.cons t yh : Fin 4 → ℝ)‖) ^
            (2 * ms.length - d))⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ (by have := prod_map_nonneg ms hKd; positivity)
        rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity),
          one_mul, ← mul_pow]
        exact pow_le_pow_left₀ hn.le hν _
    _ = _ := by ring

end QED.ChainProof.SetALinkV

end
