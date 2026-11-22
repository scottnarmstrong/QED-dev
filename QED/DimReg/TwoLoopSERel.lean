/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopSEVal

/-!
# Normalized relations and finiteness at every integer label

* `normF_dimShift`, `normF_raise_lower`, `normF_raise`: how the normalization changes under the
  label shifts that occur (`d → d + 2` with `ν → ν + γ`; `ν → ν + e_a - e_b`; `ν → ν + e_a`).
* `eventually_normalized`, `nhdsNE_normalized`: a dimension-shift relation for `Jline` gives a
  relation for `Iline` with polynomial coefficients, first for `re λ` large and then, by the
  identity theorem, near `λ = 0`.
* `tendsto_Iline` (**item 4**): for `d₀ ∉ ℚ` the normalized integral has a limit at `λ = 0` at
  every integer label, by the raising relation (`x_i ∂_i G`, data `rRaise`) and induction on the
  deficiency `Σⱼ (1 - nⱼ)⁺`.
-/

@[expose] public section

open Complex Filter Topology Set QED.DimReg

namespace QED.DimReg.TwoLoopSESector

/-! ### Generated data -/

/-- The monomials of `x_0 ∂_0 G` (generated). -/
def rRaise0 : MonoList 5 :=
  [(1, ![1, 1, 0, 0, 0]), (1, ![1, 0, 0, 2, 0]), (2, ![1, 0, 0, 1, 1]), (1, ![1, 0, 0, 1, 0]),
    (1, ![1, 0, 0, 0, 2]), (1, ![1, 0, 0, 0, 1])]

/-- The monomials of `x_1 ∂_1 G` (generated). -/
def rRaise1 : MonoList 5 :=
  [(1, ![1, 1, 0, 0, 0]), (1, ![0, 1, 2, 0, 0]), (2, ![0, 1, 1, 0, 1]), (1, ![0, 1, 1, 0, 0]),
    (1, ![0, 1, 0, 0, 2]), (1, ![0, 1, 0, 0, 1])]

/-- The monomials of `x_2 ∂_2 G` (generated). -/
def rRaise2 : MonoList 5 :=
  [(2, ![0, 1, 2, 0, 0]), (2, ![0, 1, 1, 0, 1]), (1, ![0, 1, 1, 0, 0]), (2, ![0, 0, 2, 1, 0]),
    (2, ![0, 0, 2, 0, 1]), (1, ![0, 0, 1, 2, 0]), (2, ![0, 0, 1, 1, 1]), (1, ![0, 0, 1, 1, 0]),
    (1, ![0, 0, 1, 0, 2]), (1, ![0, 0, 1, 0, 1])]

/-- The monomials of `x_3 ∂_3 G` (generated). -/
def rRaise3 : MonoList 5 :=
  [(2, ![1, 0, 0, 2, 0]), (2, ![1, 0, 0, 1, 1]), (1, ![1, 0, 0, 1, 0]), (1, ![0, 0, 2, 1, 0]),
    (2, ![0, 0, 1, 2, 0]), (2, ![0, 0, 1, 1, 1]), (1, ![0, 0, 1, 1, 0]), (2, ![0, 0, 0, 2, 1]),
    (1, ![0, 0, 0, 1, 2]), (1, ![0, 0, 0, 1, 1])]

/-- The monomials of `x_4 ∂_4 G` (generated). -/
def rRaise4 : MonoList 5 :=
  [(2, ![1, 0, 0, 1, 1]), (2, ![1, 0, 0, 0, 2]), (1, ![1, 0, 0, 0, 1]), (2, ![0, 1, 1, 0, 1]),
    (2, ![0, 1, 0, 0, 2]), (1, ![0, 1, 0, 0, 1]), (1, ![0, 0, 2, 0, 1]), (2, ![0, 0, 1, 1, 1]),
    (2, ![0, 0, 1, 0, 2]), (1, ![0, 0, 1, 0, 1]), (1, ![0, 0, 0, 2, 1]), (2, ![0, 0, 0, 1, 2]),
    (1, ![0, 0, 0, 1, 1])]

/-- The monomials of `x_1 ∂_1 G - G` (generated), for the sector `[3, 4]`. -/
def rZero0 : MonoList 5 :=
  [(-1, ![1, 0, 0, 2, 0]), (-2, ![1, 0, 0, 1, 1]), (-1, ![1, 0, 0, 1, 0]),
    (-1, ![1, 0, 0, 0, 2]), (-1, ![1, 0, 0, 0, 1]), (-1, ![0, 0, 2, 1, 0]),
    (-1, ![0, 0, 2, 0, 1]), (-1, ![0, 0, 1, 2, 0]), (-2, ![0, 0, 1, 1, 1]),
    (-1, ![0, 0, 1, 1, 0]), (-1, ![0, 0, 1, 0, 2]), (-1, ![0, 0, 1, 0, 1]),
    (-1, ![0, 0, 0, 2, 1]), (-1, ![0, 0, 0, 1, 2]), (-1, ![0, 0, 0, 1, 1])]

/-- The monomials of `x_0 ∂_0 G - G` (generated), for the sector `[2, 4]`. -/
def rZero1 : MonoList 5 :=
  [(-1, ![0, 1, 2, 0, 0]), (-2, ![0, 1, 1, 0, 1]), (-1, ![0, 1, 1, 0, 0]),
    (-1, ![0, 1, 0, 0, 2]), (-1, ![0, 1, 0, 0, 1]), (-1, ![0, 0, 2, 1, 0]),
    (-1, ![0, 0, 2, 0, 1]), (-1, ![0, 0, 1, 2, 0]), (-2, ![0, 0, 1, 1, 1]),
    (-1, ![0, 0, 1, 1, 0]), (-1, ![0, 0, 1, 0, 2]), (-1, ![0, 0, 1, 0, 1]),
    (-1, ![0, 0, 0, 2, 1]), (-1, ![0, 0, 0, 1, 2]), (-1, ![0, 0, 0, 1, 1])]

/-- The monomials of `x_0 ∂_0 G - G` (generated), for the sector `[1, 2, 3]`. -/
def rZero2 : MonoList 5 :=
  [(-1, ![0, 1, 2, 0, 0]), (-2, ![0, 1, 1, 0, 1]), (-1, ![0, 1, 1, 0, 0]),
    (-1, ![0, 1, 0, 0, 2]), (-1, ![0, 1, 0, 0, 1]), (-1, ![0, 0, 2, 1, 0]),
    (-1, ![0, 0, 2, 0, 1]), (-1, ![0, 0, 1, 2, 0]), (-2, ![0, 0, 1, 1, 1]),
    (-1, ![0, 0, 1, 1, 0]), (-1, ![0, 0, 1, 0, 2]), (-1, ![0, 0, 1, 0, 1]),
    (-1, ![0, 0, 0, 2, 1]), (-1, ![0, 0, 0, 1, 2]), (-1, ![0, 0, 0, 1, 1])]

/-- The monomials of `x_1 ∂_1 G - G` (generated), for the sector `[0, 2, 3]`. -/
def rZero3 : MonoList 5 :=
  [(-1, ![1, 0, 0, 2, 0]), (-2, ![1, 0, 0, 1, 1]), (-1, ![1, 0, 0, 1, 0]),
    (-1, ![1, 0, 0, 0, 2]), (-1, ![1, 0, 0, 0, 1]), (-1, ![0, 0, 2, 1, 0]),
    (-1, ![0, 0, 2, 0, 1]), (-1, ![0, 0, 1, 2, 0]), (-2, ![0, 0, 1, 1, 1]),
    (-1, ![0, 0, 1, 1, 0]), (-1, ![0, 0, 1, 0, 2]), (-1, ![0, 0, 1, 0, 1]),
    (-1, ![0, 0, 0, 2, 1]), (-1, ![0, 0, 0, 1, 2]), (-1, ![0, 0, 0, 1, 1])]

/-- The monomials of `x_i ∂_i G`. -/
def rRaise (i : Fin 5) : MonoList 5 := ![rRaise0, rRaise1, rRaise2, rRaise3, rRaise4] i

theorem rRaise_spec : ∀ i : Fin 5, ∀ t ∈ rRaise i,
    1 ≤ t.2 i ∧ t.2 0 + t.2 1 + t.2 2 + t.2 3 + t.2 4 ≤ 3 := by decide +kernel

theorem polyEval_rRaise (i : Fin 5) (x : Fin 5 → ℝ) : x i * gD i x = polyEval (rRaise i) x := by
  fin_cases i <;>
  · simp [rRaise, rRaise0, rRaise1, rRaise2, rRaise3, rRaise4, polyEval, monoEval,
      Fin.prod_univ_five, gD]
    ring

/-! ### The normalization under label shifts -/

/-- The coefficient of `normF_dimShift`. -/
noncomputable def rho (m : Fin 5 → ℤ) (d₀ : ℂ) (γ : Fin 5 → ℕ) (l : ℂ) : ℂ :=
  (-1 : ℂ) ^ (∑ j, γ j) * poch (3 * lineD d₀ l / 2 - ∑ j, lineNu m l j) (3 - ∑ j, γ j) *
    ∏ j, poch (lineNu m l j) (γ j)

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

/-- **The normalization under `d → d + 2`, `ν → ν + γ`** (`|γ| ≤ 3`). -/
theorem normF_dimShift (m : Fin 5 → ℤ) (γ : Fin 5 → ℕ) (hγ : ∑ j, γ j ≤ 3) (d₀ l : ℂ)
    (hd : lineD d₀ l / 2 ≠ 0) :
    lineD d₀ l / 2 * normF m d₀ l = rho m d₀ γ l * normF (m + natZ γ) (d₀ + 2) l := by
  rw [← one_mul (lineD d₀ l / 2 * normF m d₀ l), ← neg_one_pow_mul_self (∑ j, γ j)]
  set z := 3 * lineD d₀ l / 2 - ∑ j, lineNu m l j
  have h1 : (-1 : ℂ) ^ (∑ j, (m + natZ γ) j) = (-1) ^ (∑ j, m j) * (-1) ^ (∑ j, γ j) := by
    rw [show ∑ j, (m + natZ γ) j = ∑ j, m j + ((∑ j, γ j : ℕ) : ℤ) by
      simp [natZ, Finset.sum_add_distrib], zpow_add₀ (by norm_num), zpow_natCast]
  have h2 : Gamma (lineD (d₀ + 2) l / 2) = lineD d₀ l / 2 * Gamma (lineD d₀ l / 2) := by
    rw [show lineD (d₀ + 2) l / 2 = lineD d₀ l / 2 + 1 by simp only [lineD]; ring,
      Gamma_add_one _ hd]
  have h3 : 3 * lineD (d₀ + 2) l / 2 - ∑ j, lineNu (m + natZ γ) l j =
      z + ((3 - ∑ j, γ j : ℕ) : ℂ) := by
    rw [Nat.cast_sub hγ]
    simp only [z, lineD, lineNu, natZ, Pi.add_apply, Int.cast_add, Int.cast_natCast,
      Finset.sum_add_distrib, Nat.cast_sum]
    ring
  have h5 : ∏ j, (Gamma (lineNu m l j))⁻¹ = (∏ j, poch (lineNu m l j) (γ j)) *
      ∏ j, (Gamma (lineNu (m + natZ γ) l j))⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [inv_Gamma_eq_poch (lineNu m l j) (γ j)]
    congr 3
    simp [lineNu, natZ]
    ring
  simp only [normF, rho, h1, h2, h3]
  rw [h5, inv_Gamma_eq_poch z (3 - ∑ j, γ j)]
  ring

theorem prod_split {a b : Fin 5} (hab : a ≠ b) (f : Fin 5 → ℂ) :
    ∏ j, f j = f a * (f b * ∏ j ∈ (Finset.univ.erase a).erase b, f j) := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a),
    ← Finset.mul_prod_erase (Finset.univ.erase a) f (Finset.mem_erase.2 ⟨hab.symm,
      Finset.mem_univ b⟩)]

/-- **The normalization under `ν → ν + e_a - e_b`.** -/
theorem normF_raise_lower {a b : Fin 5} (hab : a ≠ b) {m m' : Fin 5 → ℤ}
    (hm : ∀ j, m' j = m j + (if j = a then 1 else 0) - (if j = b then 1 else 0)) (d₀ l : ℂ) :
    lineNu m l a * normF m' d₀ l = (lineNu m l b - 1) * normF m d₀ l := by
  have hs : ∑ j, m' j = ∑ j, m j := by
    simp only [hm, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  have hs' : ∑ j, lineNu m' l j = ∑ j, lineNu m l j := by
    simp only [lineNu, Finset.sum_add_distrib]
    congr 1
    exact_mod_cast hs
  have ha : lineNu m' l a = lineNu m l a + 1 := by
    simp [lineNu, hm, hab]; ring
  have hb : lineNu m' l b = lineNu m l b - 1 := by
    simp [lineNu, hm, Ne.symm hab]; ring
  have hr : ∏ j ∈ (Finset.univ.erase a).erase b, (Gamma (lineNu m' l j))⁻¹ =
      ∏ j ∈ (Finset.univ.erase a).erase b, (Gamma (lineNu m l j))⁻¹ :=
    Finset.prod_congr rfl fun j hj => by
      have hjb := Finset.ne_of_mem_erase hj
      have hja := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
      simp [lineNu, hm, hja, hjb]
  simp only [normF, hs, hs', prod_split hab (fun j => (Gamma (lineNu m' l j))⁻¹),
    prod_split hab (fun j => (Gamma (lineNu m l j))⁻¹), hr, ha, hb]
  have e1 := mul_inv_Gamma_add_one (lineNu m l a)
  have e2 := mul_inv_Gamma_add_one (lineNu m l b - 1)
  rw [sub_add_cancel] at e2
  rw [← e2, ← e1]
  ring

/-- **The normalization under `ν → ν + e_a`.** -/
theorem normF_raise {a : Fin 5} {m m' : Fin 5 → ℤ} (hm : ∀ j, m' j = m j + if j = a then 1 else 0)
    (d₀ l : ℂ) : lineNu m l a * normF m' d₀ l =
      -(3 * lineD d₀ l / 2 - ∑ j, lineNu m l j - 1) * normF m d₀ l := by
  have hs : ∑ j, m' j = ∑ j, m j + 1 := by
    simp only [hm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hs' : 3 * lineD d₀ l / 2 - ∑ j, lineNu m' l j =
      (3 * lineD d₀ l / 2 - ∑ j, lineNu m l j - 1) := by
    simp only [lineNu, Finset.sum_add_distrib]
    rw [show (∑ j, (m' j : ℂ)) = ∑ j, (m j : ℂ) + 1 by exact_mod_cast hs]
    ring
  have ha : lineNu m' l a = lineNu m l a + 1 := by simp [lineNu, hm]; ring
  have hr : ∏ j ∈ Finset.univ.erase a, (Gamma (lineNu m' l j))⁻¹ =
      ∏ j ∈ Finset.univ.erase a, (Gamma (lineNu m l j))⁻¹ :=
    Finset.prod_congr rfl fun j hj => by simp [lineNu, hm, Finset.ne_of_mem_erase hj]
  simp only [normF, hs, hs', ← Finset.mul_prod_erase Finset.univ
    (fun j => (Gamma (lineNu m' l j))⁻¹) (Finset.mem_univ a),
    ← Finset.mul_prod_erase Finset.univ (fun j => (Gamma (lineNu m l j))⁻¹) (Finset.mem_univ a),
    hr, ha]
  have e1 := mul_inv_Gamma_add_one (lineNu m l a)
  have e2 := mul_inv_Gamma_add_one (3 * lineD d₀ l / 2 - ∑ j, lineNu m l j - 1)
  rw [sub_add_cancel] at e2
  rw [← e2, ← e1, zpow_add₀ (by norm_num)]
  ring

/-! ### Normalized relations -/

theorem eventually_lineD_ne (d₀ : ℂ) : ∀ᶠ l in atRe, lineD d₀ l / 2 ≠ 0 := by
  filter_upwards [eventually_re_gt (|d₀.re| + 1)] with l hl h
  have h' := congrArg Complex.re h
  simp only [lineD, div_ofNat_re, add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero,
    zero_re] at h'
  have := neg_abs_le d₀.re
  have := abs_nonneg d₀.re
  linarith

/-- **A dimension-shift relation for `Jline` gives one for `Iline`**, for `re λ` large:
`P · J(n, d) = (d/2) Σ_t c_t J(n + γ_t, d + 2)` becomes
`P · I(n, d) = Σ_t c_t ρ_t I(n + γ_t, d + 2)`. -/
theorem eventually_normalized {n : Fin 5 → ℤ} {d₀ : ℂ} {P : ℂ → ℂ} (r : MonoList 5)
    (hr : ∀ t ∈ r, ∑ j, t.2 j ≤ 3)
    (hJ : ∀ᶠ l in atRe, P l * Jline n d₀ l -
      lineD d₀ l / 2 * (r.map fun t => (t.1 : ℂ) * Jline (n + natZ t.2) (d₀ + 2) l).sum = 0) :
    ∀ᶠ l in atRe, P l * Iline n d₀ l =
      (r.map fun t => (t.1 : ℂ) * rho n d₀ t.2 l * Iline (n + natZ t.2) (d₀ + 2) l).sum := by
  filter_upwards [hJ, eventually_lineD_ne d₀] with l h hd
  calc P l * Iline n d₀ l = normF n d₀ l * (lineD d₀ l / 2 *
        (r.map fun t => (t.1 : ℂ) * Jline (n + natZ t.2) (d₀ + 2) l).sum) := by
        rw [Iline]; linear_combination normF n d₀ l * h
    _ = _ := by
      rw [← list_sum_map_mul_left, ← list_sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
      have e := normF_dimShift n t.2 (hr t ht) d₀ l hd
      rw [Iline]
      linear_combination (t.1 : ℂ) * Jline (n + natZ t.2) (d₀ + 2) l * e

theorem meromorphicOn_list_sum {β : Type*} (L : List β) {f : β → ℂ → ℂ} {U : Set ℂ}
    (h : ∀ t ∈ L, MeromorphicOn (f t) U) :
    MeromorphicOn (fun l => (L.map fun t => f t l).sum) U := by
  induction L with
  | nil => simpa using MeromorphicOn.const 0
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun b hb => h b (List.mem_cons_of_mem a hb))

theorem analyticAt_rho (m : Fin 5 → ℤ) (d₀ : ℂ) (γ : Fin 5 → ℕ) (z : ℂ) :
    AnalyticAt ℂ (rho m d₀ γ) z := by
  unfold rho
  refine (analyticAt_const.mul (analyticAt_poch (by unfold lineD lineNu; fun_prop) _)).mul ?_
  exact Finset.analyticAt_fun_prod _ fun j _ => analyticAt_poch (by unfold lineNu; fun_prop) _

/-- **The normalized relation near `λ = 0`** (identity theorem). -/
theorem nhdsNE_normalized {n : Fin 5 → ℤ} {d₀ : ℂ} {P : ℂ → ℂ} (hP : Differentiable ℂ P)
    (r : MonoList 5) (h : ∀ᶠ l in atRe, P l * Iline n d₀ l =
      (r.map fun t => (t.1 : ℂ) * rho n d₀ t.2 l * Iline (n + natZ t.2) (d₀ + 2) l).sum) :
    ∀ᶠ l in 𝓝[≠] (0 : ℂ), P l * Iline n d₀ l =
      (r.map fun t => (t.1 : ℂ) * rho n d₀ t.2 l * Iline (n + natZ t.2) (d₀ + 2) l).sum :=
  eventuallyEq_nhdsNE_of_atRe
    (fun z hz => (hP.analyticAt z).meromorphicAt.mul (meromorphicOn_Iline n d₀ z hz))
    (meromorphicOn_list_sum r fun t _ z hz =>
      ((analyticAt_const.mul (analyticAt_rho n d₀ t.2 z)).meromorphicAt).mul
        (meromorphicOn_Iline _ _ z hz)) h zero_mem_halfPlane

/-! ### The raising relation and finiteness (item 4) -/

theorem polyEval_single (i : Fin 5) (x : Fin 5 → ℝ) :
    polyEval [((1 : ℤ), Pi.single i 1)] x = x i := by
  simp only [polyEval, monoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Int.cast_one, one_mul, add_zero]
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem lowZ_single (i : Fin 5) : lowZ (Pi.single i 1) i = 0 := by
  funext j
  by_cases h : j = i
  · subst h; simp [lowZ]
  · simp [lowZ, h]

/-- **The raising relation** `νᵢ J(ν, d) = (d/2) Σ c_γ(xᵢ ∂ᵢ G) J(ν + γ, d + 2)` along the line,
for `re λ` large. -/
theorem eventually_raise (i : Fin 5) (n : Fin 5 → ℤ) (d₀ : ℂ) :
    ∀ᶠ l in atRe, lineNu n l i * Jline n d₀ l - lineD d₀ l / 2 *
      ((rRaise i).map fun t => (t.1 : ℂ) * Jline (n + natZ t.2) (d₀ + 2) l).sum = 0 := by
  have h := eventually_annihilator (fun b => if b = i then [((1 : ℤ), Pi.single i 1)] else [])
    [] (rRaise i) (fun b => if b = i then rRaise i else [])
    (fun x => by
      rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb, polyEval]) (by simp)]
      simp only [eq_self, ↓reduceIte]
      rw [polyEval_single, polyEval_rRaise]
      simp [polyEval])
    (fun b x => by
      by_cases hb : b = i
      · subst hb
        simp only [eq_self, ↓reduceIte]
        rw [polyEval_single, polyEval_rRaise]
      · simp [hb, polyEval]) n d₀
  filter_upwards [h] with l hl
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)] at hl
  simpa [lowZ_single] using hl

/-- `rho` without its factor `νᵢ` (for `γᵢ ≥ 1`). -/
noncomputable def rho' (i : Fin 5) (m : Fin 5 → ℤ) (d₀ : ℂ) (γ : Fin 5 → ℕ) (l : ℂ) : ℂ :=
  (-1 : ℂ) ^ (∑ j, γ j) * poch (3 * lineD d₀ l / 2 - ∑ j, lineNu m l j) (3 - ∑ j, γ j) *
    (poch (lineNu m l i + 1) (γ i - 1) * ∏ j ∈ Finset.univ.erase i, poch (lineNu m l j) (γ j))

theorem rho_eq_mul (i : Fin 5) (m : Fin 5 → ℤ) (d₀ : ℂ) {γ : Fin 5 → ℕ} (hγ : 1 ≤ γ i) (l : ℂ) :
    rho m d₀ γ l = lineNu m l i * rho' i m d₀ γ l := by
  unfold rho rho'
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  obtain ⟨k, hk⟩ : ∃ k, γ i = k + 1 := ⟨γ i - 1, by omega⟩
  rw [hk, poch_succ, Nat.add_sub_cancel]
  ring

theorem analyticAt_rho' (i : Fin 5) (m : Fin 5 → ℤ) (d₀ : ℂ) (γ : Fin 5 → ℕ) (z : ℂ) :
    AnalyticAt ℂ (rho' i m d₀ γ) z := by
  unfold rho'
  refine (analyticAt_const.mul (analyticAt_poch (by unfold lineD lineNu; fun_prop) _)).mul
    ((analyticAt_poch (by unfold lineNu; fun_prop) _).mul ?_)
  exact Finset.analyticAt_fun_prod _ fun j _ => analyticAt_poch (by unfold lineNu; fun_prop) _

/-- The deficiency `Σⱼ (1 - nⱼ)⁺` of a label. -/
def defic (n : Fin 5 → ℤ) : ℕ := ∑ j, (1 - n j).toNat

theorem defic_lt {n : Fin 5 → ℤ} {i : Fin 5} (hi : n i ≤ 0) {γ : Fin 5 → ℕ} (hγ : 1 ≤ γ i) :
    defic (n + natZ γ) < defic n :=
  Finset.sum_lt_sum (fun j _ => by simp only [Pi.add_apply, natZ]; omega)
    ⟨i, Finset.mem_univ _, by simp only [Pi.add_apply, natZ]; omega⟩

theorem tendsto_list_sum {β : Type*} (L : List β) {f : β → ℂ → ℂ} {v : β → ℂ} {F : Filter ℂ}
    (h : ∀ t ∈ L, Tendsto (f t) F (𝓝 (v t))) :
    Tendsto (fun l => (L.map fun t => f t l).sum) F (𝓝 (L.map v).sum) := by
  induction L with
  | nil => simpa using tendsto_const_nhds
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun b hb => h b (List.mem_cons_of_mem a hb))

theorem eventually_lineNu_ne (n : Fin 5 → ℤ) (i : Fin 5) :
    ∀ᶠ l in 𝓝[≠] (0 : ℂ), lineNu n l i ≠ 0 := by
  rcases eq_or_ne (n i) 0 with h0 | h0
  · exact eventually_nhdsWithin_of_forall fun l hl => by simpa [lineNu, h0] using hl
  · refine nhdsWithin_le_nhds ((?_ : ContinuousAt (fun l => lineNu n l i) 0).eventually_ne ?_)
    · unfold lineNu; fun_prop
    · simpa [lineNu] using h0

theorem eventually_rRaise_sum (i : Fin 5) : ∀ t ∈ rRaise i, ∑ j, t.2 j ≤ 3 := fun t ht => by
  simpa [Fin.sum_univ_five] using (rRaise_spec i t ht).2

/-- **Finiteness at every integer label** (item 4): for `d₀ ∉ ℚ` the normalized continued
integral along the line through any label `n ∈ ℤ⁵` tends to `val n d₀` as `λ → 0`. -/
theorem tendsto_Iline (n : Fin 5 → ℤ) {d₀ : ℂ} (hd : Irr d₀) :
    Tendsto (Iline n d₀) (𝓝[≠] 0) (𝓝 (val n d₀)) := by
  suffices h : ∀ k, ∀ n : Fin 5 → ℤ, defic n ≤ k → ∀ d₀, Irr d₀ →
      ∃ v, Tendsto (Iline n d₀) (𝓝[≠] 0) (𝓝 v) by
    exact tendsto_nhds_limUnder (h _ n le_rfl d₀ hd)
  intro k
  induction k with
  | zero =>
    intro n hn d₀ hd
    have hpos : ∀ j, 1 ≤ n j := fun j => by
      have := (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hn)) j (Finset.mem_univ j)
      omega
    exact ⟨_, (continuousAt_Iline_pos hpos hd).tendsto.mono_left nhdsWithin_le_nhds⟩
  | succ k ih =>
    intro n hn d₀ hd
    by_cases hpos : ∀ j, 1 ≤ n j
    · exact ⟨_, (continuousAt_Iline_pos hpos hd).tendsto.mono_left nhdsWithin_le_nhds⟩
    push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have hi' : n i ≤ 0 := by omega
    have hrel := nhdsNE_normalized (P := fun l => lineNu n l i) (by unfold lineNu; fun_prop)
      (rRaise i) (eventually_normalized (rRaise i) (eventually_rRaise_sum i)
        (eventually_raise i n d₀))
    have hIH : ∀ t ∈ rRaise i, Tendsto (Iline (n + natZ t.2) (d₀ + 2)) (𝓝[≠] 0)
        (𝓝 (val (n + natZ t.2) (d₀ + 2))) := fun t ht =>
      tendsto_nhds_limUnder (ih _ (by have := defic_lt hi' (rRaise_spec i t ht).1; omega) _
        hd.add_two)
    refine ⟨_, (tendsto_list_sum (rRaise i) (f := fun t l => (t.1 : ℂ) * rho' i n d₀ t.2 l *
      Iline (n + natZ t.2) (d₀ + 2) l) fun t ht => (tendsto_const_nhds.mul
        ((analyticAt_rho' i n d₀ t.2 0).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds)).mul (hIH t ht)).congr' ?_⟩
    filter_upwards [hrel, eventually_lineNu_ne n i] with l h1 h2
    apply mul_left_cancel₀ h2
    rw [h1, ← list_sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [rho_eq_mul i n d₀ (rRaise_spec i t ht).1]
    ring

end QED.DimReg.TwoLoopSESector
