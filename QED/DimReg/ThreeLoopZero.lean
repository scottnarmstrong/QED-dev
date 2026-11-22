/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopRelFar

/-!
# The scaleless sectors of set (d) for the face values `val3`

Let `S` be a declared scaleless sector of `QED.ThreeLoopD.SetDCert.lbl`. On the face `x_S = 0`
the polynomial `G` is quasi-homogeneous: for weights `w ∈ ℕ⁹` and `h ≥ 1`,
`Σ_k w_k x_k ∂_k G = h G + r` where every monomial of `r` is divisible by some `x_a`, `a ∈ S`
(`r = Σ_t c_t (w·α_t - h) x^{α_t}` over the monomials of `G`). Eleven sectors have `w = e_c`,
`h = 1`; the three sectors `{3,4,6,7}`, `{3,4,5,7,8}`, `{3,4,5,6,8}` need `w = e₀ + e₁ + e₂`,
`h = 2` (data `zeroData`, checked by the kernel against `QED.DimReg.ThreeLoop.lpPolyLit`).

* `euler_lp`: at a convergent point with `re d > 0`, the Euler relation
  `(w·ν - h d/2) J(ν, d) = (d/2) Σ_t c_t J(ν + α_t, d + 2)` of
  `QED.DimReg.lpIntegral_annihilator`, normalized: the coefficient of `N(ν + α, d + 2)` is
  `c (2d - |ν|)_{4-|α|} ∏_k (ν_k)_{α_k}` (`normLP_dimShift`).
* `val3_eq_zero_of_euler`: by `QED.DimReg.ThreeLoop.rel_val3` the relation holds for `val3` at
  every label with `n₇, n₈ ≤ 0` and `d₀ ∉ ℚ`; every term either has coefficient `0`, or a
  vanishing Pochhammer factor `(n_b)_{α_b}` (`n_b ≤ 0 < n_b + α_b`), or a label in the sector of
  smaller depth, and `w·n - h d₀/2 ≠ 0`, so `val3 n d₀ = 0` by induction on the depth.
* `val3_zero_of_sector`, `val3_zero_of_zeroPred`: every declared zero sector of `lbl` vanishes
  for `val3`, at labels with `ν₇, ν₈ ≤ 0`.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory QED.DimReg QED.DimReg.Sector QED.DimReg.LineCont
open QED.Algebra.IBPCert QED.ThreeLoopD.SetDCert
open QED.DimReg.TwoLoopSESector (poch Irr inv_Gamma_eq_poch poch_eq_zero)

namespace QED.DimReg.ThreeLoop

/-! ### Euler identities for sparse polynomials -/

theorem mul_eval_diff (P : ZPoly) (y : Fin 9 → ℝ) (b : Fin 9) :
    y b * ZPoly.eval (ZPoly.diff b P) y =
      ZPoly.eval (P.map fun t => (t.1, t.2 * (t.1.getD b 0 : ℤ))) y := by
  induction P with
  | nil => simp [ZPoly.diff]
  | cons t P ih =>
    simp only [ZPoly.diff, List.map_cons, ZPoly.eval_cons] at ih ⊢
    rw [mul_add, ih]
    congr 1
    rcases Nat.eq_zero_or_pos (t.1.getD b 0) with h0 | hpos
    · rw [h0]; push_cast; ring
    · obtain ⟨k, hk⟩ : ∃ k, t.1.getD b 0 = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      have hm : mono t.1 y = mono t.1 (Function.update y b (y b)) := by simp
      rw [ZPoly.mono_diffExp, hm, ZPoly.mono_update, hk, Nat.add_sub_cancel]
      push_cast
      ring

theorem sum_mul_eval_diff (P : ZPoly) (w : Fin 9 → ℤ) (y : Fin 9 → ℝ) :
    ∑ b, (w b : ℝ) * (y b * ZPoly.eval (ZPoly.diff b P) y) =
      ZPoly.eval (P.map fun t => (t.1, t.2 * ∑ b, w b * (t.1.getD b 0 : ℤ))) y := by
  simp only [mul_eval_diff]
  induction P with
  | nil => simp
  | cons t P ih =>
    simp only [List.map_cons, ZPoly.eval_cons, mul_add, Finset.sum_add_distrib, ih]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring

theorem eval_map_split (P : ZPoly) (f : List ℕ → ℤ) (h : ℤ) (y : Fin 9 → ℝ) :
    ZPoly.eval (P.map fun t => (t.1, t.2 * f t.1)) y =
      h * ZPoly.eval P y + ZPoly.eval (P.map fun t => (t.1, t.2 * (f t.1 - h))) y := by
  induction P with
  | nil => simp
  | cons t P ih =>
    simp only [List.map_cons, ZPoly.eval_cons, ih]
    push_cast
    ring

theorem polyEval_single_mul (c : ℤ) (b : Fin 9) (x : Fin 9 → ℝ) :
    polyEval [(c, (Pi.single b 1 : Fin 9 → ℕ))] x = c * x b := by
  simp only [polyEval, monoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  rw [Finset.prod_eq_single b (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-! ### The Euler data -/

/-- The weighted degree `w · α` of an exponent list (nine variables). -/
def wdot (wL α : List ℕ) : ℕ := ((List.finRange 9).map fun k => wL.getD k 0 * α.getD k 0).sum

theorem wdot_eq (wL α : List ℕ) :
    (wdot wL α : ℤ) = ∑ k : Fin 9, (wL.getD k 0 : ℤ) * α.getD k 0 := by
  rw [wdot, Fin.sum_univ_def, Nat.cast_list_sum, List.map_map]
  rfl

/-- The vector field `x ↦ Σ_b w_b x_b e_b`. -/
def pE (wL : List ℕ) (b : Fin 9) : MonoList 9 := [((wL.getD b 0 : ℤ), Pi.single b 1)]

/-- The remainder `r = Σ_t c_t (w·α_t - h) x^{α_t}` of `Σ_k w_k x_k ∂_k G - h G`. -/
def rZ (wL : List ℕ) (h : ℕ) : ZPoly :=
  (ZPoly.ofN lpPoly).map fun t => (t.1, t.2 * ((wdot wL t.1 : ℤ) - h))

/-- The products `w_b x_b ∂_b G`. -/
def eZ (wL : List ℕ) (b : Fin 9) : ZPoly :=
  ZPoly.smul (wL.getD b 0) ((ZPoly.ofN lpPoly).map fun t => (t.1, t.2 * (t.1.getD b 0 : ℤ)))

theorem euler_syz (wL : List ℕ) (h : ℕ) (x : Fin 9 → ℝ) :
    ∑ b, polyEval (pE wL b) x * gD b x =
      polyEval [((h : ℤ), (0 : Fin 9 → ℕ))] x * lpPoly.eval x +
        polyEval (ZPoly.toML (rZ wL h)) x := by
  simp only [pE, polyEval_single_mul, gD, mul_assoc]
  rw [sum_mul_eval_diff, eval_map_split _
    (fun α => ∑ b : Fin 9, (wL.getD b 0 : ℤ) * α.getD b 0) h, ZPoly.polyEval_toML,
    ZPoly.eval_ofN]
  simp only [polyEval, monoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one, rZ, wdot_eq]

theorem euler_e (wL : List ℕ) (b : Fin 9) (x : Fin 9 → ℝ) :
    polyEval (pE wL b) x * gD b x = polyEval (ZPoly.toML (eZ wL b)) x := by
  rw [pE, polyEval_single_mul, gD, ZPoly.polyEval_toML, eZ, ZPoly.eval_smul, mul_assoc,
    mul_eval_diff]

/-! ### The normalization under `d → d + 2` -/

/-- **The normalization under `d → d + 2`, `ν → ν + α`** (`|α| ≤ 4`). -/
theorem normLP_dimShift (ν : Fin 9 → ℂ) (d : ℂ) (α : Fin 9 → ℕ) (hα : ∑ k, α k ≤ 4)
    (hd : d / 2 ≠ 0) :
    d / 2 * normLP ν d = poch (2 * d - ∑ k, ν k) (4 - ∑ k, α k) * (∏ k, poch (ν k) (α k)) *
      normLP (ν + fun k => (α k : ℂ)) (d + 2) := by
  have h1 : Gamma ((d + 2) / 2) = d / 2 * Gamma (d / 2) := by
    rw [show (d + 2) / 2 = d / 2 + 1 by ring, Gamma_add_one _ hd]
  have h2 : 2 * (d + 2) - ∑ k, (ν + fun k => (α k : ℂ)) k =
      2 * d - ∑ k, ν k + ((4 - ∑ k, α k : ℕ) : ℂ) := by
    rw [Nat.cast_sub hα]
    simp only [Pi.add_apply, Finset.sum_add_distrib, Nat.cast_sum]
    ring
  have h3 : ∏ k, (Gamma (ν k))⁻¹ =
      (∏ k, poch (ν k) (α k)) * ∏ k, (Gamma (ν k + α k))⁻¹ :=
    (Finset.prod_congr rfl fun k _ => inv_Gamma_eq_poch _ _).trans Finset.prod_mul_distrib
  unfold normLP
  rw [h1, h2, h3, inv_Gamma_eq_poch (2 * d - ∑ k, ν k) (4 - ∑ k, α k)]
  simp only [Pi.add_apply]
  ring

/-! ### The Euler relation at a convergent point -/

/-- The terms of the Euler relation: the main term and one term per monomial of `r`. -/
def eulT (wL : List ℕ) (h : ℕ) : List (Option (List ℕ × ℤ)) := none :: (rZ wL h).map some

/-- The label shifts of the Euler relation. -/
def eulσ : Option (List ℕ × ℤ) → Fin 9 → ℤ
  | none => 0
  | some t => fun k => (t.1.getD k 0 : ℤ)

/-- The dimension shifts (in units of `2`) of the Euler relation. -/
def eulj : Option (List ℕ × ℤ) → ℕ
  | none => 0
  | some _ => 1

/-- The coefficients of the normalized Euler relation. -/
noncomputable def eula (wL : List ℕ) (h : ℕ) : Option (List ℕ × ℤ) → (Fin 9 → ℂ) → ℂ → ℂ
  | none => fun ν d => (∑ k : Fin 9, (wL.getD k 0 : ℂ) * ν k) - h * d / 2
  | some t => fun ν d => -((t.2 : ℂ) * poch (2 * d - ∑ k, ν k) (4 - ∑ k : Fin 9, t.1.getD k 0) *
      ∏ k : Fin 9, poch (ν k) (t.1.getD k 0))

/-- The total degree of `G` is at most `4`. -/
theorem degOk4 : lpPolyLit.all (fun t => wdot [1, 1, 1, 1, 1, 1, 1, 1, 1] t.1 ≤ 4) = true := by
  decide +kernel

theorem deg_le_four {t : List ℕ × ℕ} (ht : t ∈ lpPoly) : ∑ k : Fin 9, t.1.getD k 0 ≤ 4 := by
  have h := degOk4
  rw [List.all_eq_true] at h
  have h' := of_decide_eq_true (h t (lpPoly_eq_lit ▸ ht))
  have e := wdot_eq [1, 1, 1, 1, 1, 1, 1, 1, 1] t.1
  have e1 : ∀ k : Fin 9, ([1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℕ).getD k 0 = 1 := by decide
  simp only [e1, Nat.cast_one, one_mul] at e
  have : ((∑ k : Fin 9, t.1.getD k 0 : ℕ) : ℤ) ≤ 4 := by push_cast; rw [← e]; exact_mod_cast h'
  exact_mod_cast this

theorem exp_le_two {t : List ℕ × ℕ} (ht : t ∈ lpPoly) (k : Fin 9) : t.1.getD k 0 ≤ 2 :=
  (deg_lpPoly t ht k).trans (degs_le k k.isLt)

theorem mem_rZ {wL : List ℕ} {h : ℕ} {t : List ℕ × ℤ} (ht : t ∈ rZ wL h) :
    ∃ u ∈ lpPoly, t = (u.1, (u.2 : ℤ) * ((wdot wL u.1 : ℤ) - h)) := by
  simp only [rZ, ZPoly.ofN, List.map_map, List.mem_map, Function.comp_apply] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact ⟨u, hu, rfl⟩

theorem shifted_self (ν : Fin 9 → ℂ) (d : ℂ) : Shifted ν d ν d :=
  ⟨fun k => ⟨0, by norm_num, Or.inl (by simp)⟩, Or.inl rfl⟩

theorem shifted_exp {ν : Fin 9 → ℂ} {d : ℂ} {u : List ℕ × ℕ} (hu : u ∈ lpPoly) :
    Shifted ν d (natShift ν fun k => u.1.getD k 0) (d + 2) :=
  ⟨fun k => ⟨u.1.getD k 0, (exp_le_two hu k).trans (by norm_num), Or.inl rfl⟩, Or.inr rfl⟩

theorem lowerAt_natShift_single (ν : Fin 9 → ℂ) (b : Fin 9) :
    lowerAt (natShift ν (Pi.single b 1)) b = ν := by
  funext k
  by_cases hk : k = b
  · subst hk; simp [lowerAt, natShift]
  · simp [lowerAt, natShift, hk]

theorem natShift_zero9 (ν : Fin 9 → ℂ) : natShift ν (0 : Fin 9 → ℕ) = ν := by
  funext k; simp [natShift]

theorem natShift_eq_add_shZ (ν : Fin 9 → ℂ) (α : List ℕ) :
    natShift ν (fun k => α.getD k 0) = ν + shZ (eulσ (some (α, 0))) := by
  funext k; simp [natShift, shZ, eulσ]

/-- The nine-variable Lee–Pomeransky integral of set (d). -/
noncomputable def J9 (μ : Fin 9 → ℂ) (e : ℂ) : ℂ := lpIntegral (fun x => lpPoly.eval x) μ e

/-- **The normalized Euler relation at a convergent point.** -/
theorem euler_lp (wL : List ℕ) (h : ℕ) (ν : Fin 9 → ℂ) (d : ℂ) (hd : 0 < d.re)
    (hconv : ∀ μ e, Shifted ν d μ e → LPConvergent (fun x => lpPoly.eval x) μ e) :
    ((eulT wL h).map fun t => eula wL h t ν d * (normLP (ν + shZ (eulσ t)) (d + 2 * eulj t) *
      lpIntegral (fun x => lpPoly.eval x) (ν + shZ (eulσ t)) (d + 2 * eulj t))).sum = 0 := by
  have A := lpIntegral_annihilator (G := fun x => lpPoly.eval x) (fun x hx => G_pos hx)
    (fun b x _ => hasDerivAt_G b x) (pE wL) [((h : ℤ), 0)] (ZPoly.toML (rZ wL h))
    (fun b => ZPoly.toML (eZ wL b)) (fun x _ => euler_syz wL h x) (fun b x _ => euler_e wL b x)
    ν d
    (fun b t ht => by
      simp only [pE, List.mem_singleton] at ht
      subst ht
      rw [lowerAt_natShift_single]
      exact hconv _ _ (shifted_self ν d))
    (fun t ht => by
      simp only [List.mem_singleton] at ht
      subst ht
      rw [natShift_zero9]
      exact hconv _ _ (shifted_self ν d))
    (fun t ht => by
      simp only [ZPoly.toML, List.mem_map] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      obtain ⟨u, hu, rfl⟩ := mem_rZ hs
      exact hconv _ _ (shifted_exp hu))
    (fun b t ht => by
      simp only [ZPoly.toML, eZ, ZPoly.smul, ZPoly.ofN, List.map_map, List.mem_map,
        Function.comp_apply] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      exact hconv _ _ (shifted_exp hu))
  have hd2 : d / 2 ≠ 0 := by
    intro h0
    have : d = 0 := by linear_combination 2 * h0
    rw [this, zero_re] at hd
    exact lt_irrefl _ hd
  change ((eulT wL h).map fun t => eula wL h t ν d * (normLP (ν + shZ (eulσ t))
    (d + 2 * eulj t) * J9 (ν + shZ (eulσ t)) (d + 2 * eulj t))).sum = 0
  change ∑ b, ((pE wL b).map fun t => (t.1 : ℂ) * (ν b + t.2 b - 1) *
      J9 (lowerAt (natShift ν t.2) b) d).sum -
    d / 2 * (([((h : ℤ), (0 : Fin 9 → ℕ))].map fun t => (t.1 : ℂ) * J9 (natShift ν t.2) d).sum +
      ((ZPoly.toML (rZ wL h)).map fun t => (t.1 : ℂ) * J9 (natShift ν t.2) (d + 2)).sum) = 0
    at A
  -- simplify the annihilator relation
  simp only [pE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Pi.single_eq_same, Nat.cast_one, add_sub_cancel_right, lowerAt_natShift_single] at A
  rw [natShift_zero9] at A
  have hr : ((ZPoly.toML (rZ wL h)).map fun t => (t.1 : ℂ) * J9 (natShift ν t.2) (d + 2)).sum =
      ((rZ wL h).map fun t => (t.2 : ℂ) * J9 (ν + shZ (eulσ (some t))) (d + 2)).sum := by
    simp only [ZPoly.toML, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    simp only [Function.comp_apply]
    congr 2
  rw [hr] at A
  -- the normalized terms
  have hrest : ((rZ wL h).map fun t => eula wL h (some t) ν d *
      (normLP (ν + shZ (eulσ (some t))) (d + 2 * eulj (some t)) *
        J9 (ν + shZ (eulσ (some t))) (d + 2 * eulj (some t)))).sum =
      ((rZ wL h).map fun t => -(normLP ν d * (d / 2 *
        ((t.2 : ℂ) * J9 (ν + shZ (eulσ (some t))) (d + 2))))).sum := by
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    obtain ⟨u, hu, rfl⟩ := mem_rZ ht
    have hN := normLP_dimShift ν d (fun k => u.1.getD k 0) (deg_le_four hu) hd2
    have hsh : ν + shZ (eulσ (some (u.1, (u.2 : ℤ) * ((wdot wL u.1 : ℤ) - h)))) =
        ν + fun k : Fin 9 => ((u.1.getD k 0 : ℕ) : ℂ) := by
      funext k; simp [shZ, eulσ]
    simp only [eula, eulj, Nat.cast_one, mul_one]
    rw [hsh]
    linear_combination ((((u.2 : ℤ) * ((wdot wL u.1 : ℤ) - h) : ℤ) : ℂ) *
      J9 (ν + fun k : Fin 9 => ((u.1.getD k 0 : ℕ) : ℂ)) (d + 2)) * hN
  simp only [eulT, List.map_cons, List.sum_cons, List.map_map]
  rw [show ((rZ wL h).map ((fun t => eula wL h t ν d * (normLP (ν + shZ (eulσ t))
      (d + 2 * eulj t) * J9 (ν + shZ (eulσ t)) (d + 2 * eulj t))) ∘ some)).sum =
      ((rZ wL h).map fun t => eula wL h (some t) ν d *
      (normLP (ν + shZ (eulσ (some t))) (d + 2 * eulj (some t)) *
        J9 (ν + shZ (eulσ (some t))) (d + 2 * eulj (some t)))).sum from rfl, hrest,
    lsum_map_neg, list_sum_map_mul_left, list_sum_map_mul_left]
  have h0 : ν + shZ (eulσ none) = ν := by funext k; simp [shZ, eulσ]
  simp only [h0, eula, eulj, Nat.cast_zero, mul_zero, add_zero]
  have hw : ∑ b : Fin 9, ((wL.getD b 0 : ℤ) : ℂ) * ν b * J9 ν d =
      (∑ k : Fin 9, (wL.getD k 0 : ℂ) * ν k) * J9 ν d := by
    rw [Finset.sum_mul]; push_cast; rfl
  rw [hw] at A
  simp only [Int.cast_natCast] at A
  linear_combination normLP ν d * A

/-! ### The relation for `val3` and the induction on the depth -/

theorem differentiable_finset_prod {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : Finset ι) {g : ι → E → ℂ} (hg : ∀ i ∈ u, Differentiable ℂ (g i)) :
    Differentiable ℂ fun x => ∏ i ∈ u, g i x := by
  classical
  exact fun x => (HasFDerivAt.finsetProd fun i hi => (hg i hi x).hasFDerivAt).differentiableAt

theorem differentiable_poch {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ}
    (hf : Differentiable ℂ f) (k : ℕ) : Differentiable ℂ fun x => poch (f x) k := by
  unfold poch
  exact differentiable_finset_prod _ fun j _ => hf.add_const _

theorem differentiable_eula (wL : List ℕ) (h : ℕ) (t : Option (List ℕ × ℤ)) :
    Differentiable ℂ fun p : (Fin 9 → ℂ) × ℂ => eula wL h t p.1 p.2 := by
  cases t with
  | none => simp only [eula]; fun_prop
  | some t =>
    simp only [eula]
    refine (((differentiable_const _).mul (differentiable_poch (by fun_prop) _)).mul ?_).neg
    exact differentiable_finset_prod _ fun k _ => differentiable_poch (by fun_prop) _

theorem mem_eulT {wL : List ℕ} {h : ℕ} {t : Option (List ℕ × ℤ)} (ht : t ∈ eulT wL h) :
    t = none ∨ ∃ s ∈ rZ wL h, t = some s := by
  simp only [eulT, List.mem_cons, List.mem_map] at ht
  rcases ht with rfl | ⟨s, hs, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨s, hs, rfl⟩

theorem eulσ_bounds (wL : List ℕ) (h : ℕ) :
    ∀ t ∈ eulT wL h, ∀ k, -1 ≤ eulσ t k ∧ eulσ t k ≤ ((2 : ℕ) : ℤ) := by
  intro t ht k
  rcases mem_eulT ht with rfl | ⟨s, hs, rfl⟩
  · simp [eulσ]
  · obtain ⟨u, hu, rfl⟩ := mem_rZ hs
    have := exp_le_two hu k
    simp only [eulσ]
    constructor <;> omega

/-- A term raising `ν_k` from `n_k ≤ 0` to a positive value has coefficient `0` at `ν_k = n_k`
(the factor `(n_k)_{α_k}`). -/
theorem eula_some_eq_zero (wL : List ℕ) (h : ℕ) (s : List ℕ × ℤ) {n : Fin 9 → ℤ} {k : Fin 9}
    (hk : n k ≤ 0) (hpos : 0 < n k + eulσ (some s) k) {ν : Fin 9 → ℂ} (hν : ν k = (n k : ℂ))
    (d : ℂ) : eula wL h (some s) ν d = 0 := by
  simp only [eulσ] at hpos
  simp only [eula]
  rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hν]; exact poch_eq_zero hk (by omega)),
    mul_zero, neg_zero]

theorem eula_zero (wL : List ℕ) (h : ℕ) (n : Fin 9 → ℤ) :
    ∀ t ∈ eulT wL h, ∀ k : Fin 9, (k = 7 ∨ k = 8) → n k ≤ 0 → 0 < n k + eulσ t k →
      ∀ ν d, ν k = (n k : ℂ) → eula wL h t ν d = 0 := by
  intro t ht k _ hk hpos ν d hν
  rcases mem_eulT ht with rfl | ⟨s, -, rfl⟩
  · simp only [eulσ, Pi.zero_apply, add_zero] at hpos; omega
  · exact eula_some_eq_zero wL h s hk hpos hν d

/-- The depth of a label in the sector `S`. -/
def depth9 (S : Finset (Fin 9)) (n : Fin 9 → ℤ) : ℕ := ∑ a ∈ S, (-n a).toNat

/-- **A scaleless sector vanishes for `val3`**: if `w·α = h` for every monomial `x^α` of `G`
not divisible by any `x_a`, `a ∈ S`, then `val3 n d₀ = 0` whenever `n_a ≤ 0` on `S`,
`n₇, n₈ ≤ 0` and `d₀ ∉ ℚ`. -/
theorem val3_eq_zero_of_euler (S : Finset (Fin 9)) (wL : List ℕ) (h : ℕ) (hh : 0 < h)
    (hspec : ∀ t ∈ lpPoly, wdot wL t.1 = h ∨ ∃ a ∈ S, 1 ≤ t.1.getD a 0)
    (n : Fin 9 → ℤ) (hn : ∀ a ∈ S, n a ≤ 0) (hn7 : n 7 ≤ 0) (hn8 : n 8 ≤ 0) {d₀ : ℂ}
    (hd : Irr d₀) : val3 n d₀ = 0 := by
  suffices H : ∀ k, ∀ n : Fin 9 → ℤ, depth9 S n ≤ k → (∀ a ∈ S, n a ≤ 0) → n 7 ≤ 0 →
      n 8 ≤ 0 → ∀ d₀, Irr d₀ → val3 n d₀ = 0 from H _ n le_rfl hn hn7 hn8 d₀ hd
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro n hk hn hn7 hn8 d₀ hd
  have hrel := rel_val3 (eulT wL h) eulσ eulj (eula wL h) 2 (eulσ_bounds wL h)
    (fun t _ => differentiable_eula wL h t) (fun ν d hd' hc => euler_lp wL h ν d hd' hc) n
    hn7 hn8 (eula_zero wL h n) hd
  simp only [eulT, List.map_cons, List.sum_cons, List.map_map] at hrel
  have hsum : ((rZ wL h).map ((fun t => eula wL h t (fun k => (n k : ℂ)) d₀ *
      val3 (n + eulσ t) (d₀ + 2 * eulj t)) ∘ some)).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    obtain ⟨u, hu, rfl⟩ := mem_rZ hs
    simp only [Function.comp_apply]
    rcases hspec u hu with hw | ⟨a, haS, ha⟩
    · simp [eula, hw]
    · set m := n + eulσ (some (u.1, (u.2 : ℤ) * ((wdot wL u.1 : ℤ) - h))) with hm
      have hma : ∀ b, m b = n b + u.1.getD b 0 := fun b => by simp [hm, eulσ]
      by_cases hin : (∀ b ∈ S, m b ≤ 0) ∧ m 7 ≤ 0 ∧ m 8 ≤ 0
      · have hlt : depth9 S m < depth9 S n := by
          refine Finset.sum_lt_sum (fun b hb => ?_) ⟨a, haS, ?_⟩
          · have := hin.1 b hb
            rw [hma] at this ⊢
            omega
          · have := hin.1 a haS
            rw [hma] at this ⊢
            omega
        have hd2 : Irr (d₀ + 2 * ((eulj (some (u.1, (u.2 : ℤ) * ((wdot wL u.1 : ℤ) - h))) : ℕ) :
            ℂ)) := by
          simpa [eulj] using hd.add_two
        rw [ih _ (by omega) m le_rfl hin.1 hin.2.1 hin.2.2 _ hd2, mul_zero]
      · rw [not_and_or, not_and_or] at hin
        obtain ⟨b, hb, hbm⟩ : ∃ b, n b ≤ 0 ∧ 0 < m b := by
          rcases hin with hin | hin | hin
          · push Not at hin
            obtain ⟨b, hbS, hb⟩ := hin
            exact ⟨b, hn b hbS, hb⟩
          · exact ⟨7, hn7, by omega⟩
          · exact ⟨8, hn8, by omega⟩
        rw [eula_some_eq_zero wL h _ hb hbm rfl d₀, zero_mul]
  rw [hsum, add_zero] at hrel
  have h0 : n + eulσ none = n := by funext k; simp [eulσ]
  simp only [h0, eula, eulj, Nat.cast_zero, mul_zero, add_zero] at hrel
  have hne : (∑ k : Fin 9, (wL.getD k 0 : ℂ) * (n k : ℂ)) - h * d₀ / 2 ≠ 0 := by
    intro h0
    have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    apply hd (2 * (∑ k : Fin 9, (wL.getD k 0 : ℤ) * n k : ℤ) / h)
    push_cast
    rw [eq_div_iff hh']
    linear_combination -2 * h0
  exact (mul_eq_zero.1 hrel).resolve_left hne

/-! ### The declared scaleless sectors of `lbl` -/

/-- The Euler data `(S, w, h)` of the declared scaleless sectors of `lbl`, in the order of
`QED.ThreeLoopD.SetDCert.lbl`: `w = e_c`, `h = 1`, or `w = e₀ + e₁ + e₂`, `h = 2`. -/
def zeroData : List (List ℕ × List ℕ × ℕ) := [
    ([5, 6, 7], [0, 0, 0, 0, 0, 0, 0, 0, 1], 1),
    ([2, 4, 7], [0, 1, 0, 0, 0, 0, 0, 0, 0], 1),
    ([1, 4, 7], [0, 0, 1, 0, 0, 0, 0, 0, 0], 1),
    ([1, 3, 6], [1, 0, 0, 0, 0, 0, 0, 0, 0], 1),
    ([0, 3, 6], [0, 1, 0, 0, 0, 0, 0, 0, 0], 1),
    ([3, 4, 6, 7], [1, 1, 1, 0, 0, 0, 0, 0, 0], 2),
    ([3, 4, 5, 7, 8], [1, 1, 1, 0, 0, 0, 0, 0, 0], 2),
    ([3, 4, 5, 6, 8], [1, 1, 1, 0, 0, 0, 0, 0, 0], 2),
    ([2, 4, 5, 6, 8], [0, 1, 0, 0, 0, 0, 0, 0, 0], 1),
    ([2, 3, 4, 5, 8], [1, 0, 0, 0, 0, 0, 0, 0, 0], 1),
    ([1, 4, 5, 6, 8], [0, 0, 1, 0, 0, 0, 0, 0, 0], 1),
    ([1, 3, 5, 7, 8], [1, 0, 0, 0, 0, 0, 0, 0, 0], 1),
    ([1, 2, 4, 5, 6], [0, 0, 0, 0, 0, 0, 0, 0, 1], 1),
    ([0, 3, 5, 7, 8], [0, 1, 0, 0, 0, 0, 0, 0, 0], 1),
    ([0, 3, 4, 5, 8], [0, 0, 1, 0, 0, 0, 0, 0, 0], 1),
    ([0, 2, 3, 4, 5], [0, 0, 0, 0, 0, 0, 0, 0, 1], 1),
    ([0, 1, 3, 5, 7], [0, 0, 0, 0, 0, 0, 0, 0, 1], 1)]

/-- The Euler check of `(S, w, h)` on the monomials of `G`. -/
def eulOk (S wL : List ℕ) (h : ℕ) : Bool :=
  lpPolyLit.all fun t => (wdot wL t.1 == h) || S.any fun a => Nat.blt 0 (t.1.getD a 0)

theorem zeroData_ok : zeroData.all (fun e => (eulOk e.1 e.2.1 e.2.2 && Nat.blt 0 e.2.2) &&
    e.1.all (Nat.blt · 9)) = true := by
  decide +kernel

theorem zeroSectors_eq : lbl.zeroSectors = zeroData.map (·.1) := rfl

/-- **The declared scaleless sectors of `lbl` vanish for `val3`**, at labels with
`ν₇, ν₈ ≤ 0` and `d₀ ∉ ℚ`. -/
theorem val3_zero_of_sector {d₀ : ℂ} (hd : Irr d₀) {S : List ℕ} (hS : S ∈ lbl.zeroSectors)
    (ν : Fin 9 → ℤ) (hν : ∀ a ∈ S, vecGet ν a ≤ 0) (h7 : ν 7 ≤ 0) (h8 : ν 8 ≤ 0) :
    val3 ν d₀ = 0 := by
  rw [zeroSectors_eq, List.mem_map] at hS
  obtain ⟨e, he, rfl⟩ := hS
  have h1 := List.all_eq_true.1 zeroData_ok e he
  simp only [Bool.and_eq_true, Nat.blt_eq] at h1
  obtain ⟨⟨hE, hpos⟩, hlt⟩ := h1
  refine val3_eq_zero_of_euler (Finset.univ.filter fun a : Fin 9 => (a : ℕ) ∈ e.1) e.2.1 e.2.2
    hpos ?_ ν ?_ h7 h8 hd
  · intro t ht
    have := List.all_eq_true.1 hE t (lpPoly_eq_lit ▸ ht)
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Nat.blt_eq] at this
    rcases this with hw | ⟨a, haS, ha⟩
    · exact Or.inl hw
    · right
      have ha9 : a < 9 := by simpa using List.all_eq_true.1 hlt a haS
      exact ⟨⟨a, ha9⟩, by simp [haS], ha⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simpa [vecGet, a.isLt] using hν a ha

/-- The zero predicate of the certificate checkers, for `val3`: a label in a declared scaleless
sector with `ν₇, ν₈ ≤ 0` has `val3 = 0` (`d₀ ∉ ℚ`). -/
theorem val3_zero_of_zeroPred {d₀ : ℂ} (hd : Irr d₀) {l : List ℤ} (hl : lbl.zeroPred l = true)
    (h7 : l.getD 7 0 ≤ 0) (h8 : l.getD 8 0 ≤ 0) : val3 (toVec 9 l) d₀ = 0 := by
  simp only [Family.zeroPred, List.any_eq_true, List.all_eq_true] at hl
  obtain ⟨S, hS, hall⟩ := hl
  exact val3_zero_of_sector hd hS _
    (fun a ha => vecGet_toVec_nonpos (nonpos_of_intNonpos (hall a ha))) h7 h8

end QED.DimReg.ThreeLoop
