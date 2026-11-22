/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopLineVal

/-!
# Lee–Pomeransky families along lines: relations and finiteness at every label

The `Fin N` version of `QED.DimReg.TwoLoopSERel` and of the generic part of
`QED.DimReg.TwoLoopSEZero`, for a `QED.DimReg.LineCont.LineFamily`.

* `normF_dimShift`, `normF_raise_lower`, `normF_raise`: the normalization under label shifts.
* `eventually_normalized`, `nhdsNE_normalized`: dimension-shift relations for `Jline` give
  relations for `Iline` with polynomial coefficients, for `re λ` large and near `λ = 0`.
* `tendsto_Iline`: for `d₀ ∉ ℚ` the normalized integral has a limit at `λ = 0` at every integer
  label (raising relation `xᵢ ∂ᵢ G`, induction on the deficiency `Σⱼ (1 - nⱼ)⁺`).
* `val_relation`: a dimension-shift relation at `λ = 0`.
* `val_eq_zero_of_sector`: scaleless sectors vanish.
-/

@[expose] public section

open Complex Filter Topology Set QED.DimReg QED.DimReg.Sector
open QED.DimReg.TwoLoopSESector (atRe halfPlane zero_mem_halfPlane poch Irr Irr.add_two
  inv_Gamma_eq_poch poch_succ analyticAt_poch mul_inv_Gamma_add_one eventually_re_gt
  eventuallyEq_nhdsNE_of_atRe meromorphicOn_list_sum prod_split
  polyEval_single poch_eq_zero polyEval_one)

namespace QED.DimReg.LineCont

variable {N : ℕ}

namespace LineFamily

variable (F : LineFamily N)

/-! ### The normalization under label shifts -/

/-- The coefficient of `normF_dimShift`. -/
noncomputable def rho (m : Fin N → ℤ) (d₀ : ℂ) (γ : Fin N → ℕ) (l : ℂ) : ℂ :=
  poch (F.Lp * lineD F.h d₀ l / 2 - ∑ j, lineNu F.w m l j) (F.Lp - ∑ j, γ j) *
    ∏ j, poch (lineNu F.w m l j) (γ j)

/-- **The normalization under `d → d + 2`, `ν → ν + γ`** (`|γ| ≤ Lp`). -/
theorem normF_dimShift (m : Fin N → ℤ) (γ : Fin N → ℕ) (hγ : ∑ j, γ j ≤ F.Lp) (d₀ l : ℂ)
    (hd : lineD F.h d₀ l / 2 ≠ 0) :
    lineD F.h d₀ l / 2 * F.normF m d₀ l = F.rho m d₀ γ l * F.normF (m + natZ γ) (d₀ + 2) l := by
  set z := F.Lp * lineD F.h d₀ l / 2 - ∑ j, lineNu F.w m l j
  have h2 : Gamma (lineD F.h (d₀ + 2) l / 2) = lineD F.h d₀ l / 2 * Gamma (lineD F.h d₀ l / 2) := by
    rw [show lineD F.h (d₀ + 2) l / 2 = lineD F.h d₀ l / 2 + 1 by simp only [lineD]; ring,
      Gamma_add_one _ hd]
  have h3 : F.Lp * lineD F.h (d₀ + 2) l / 2 - ∑ j, lineNu F.w (m + natZ γ) l j =
      z + ((F.Lp - ∑ j, γ j : ℕ) : ℂ) := by
    rw [Nat.cast_sub hγ]
    simp only [z, lineD, lineNu, natZ, Pi.add_apply, Int.cast_add, Int.cast_natCast,
      Finset.sum_add_distrib, Nat.cast_sum]
    ring
  have h5 : ∏ j, (Gamma (lineNu F.w m l j))⁻¹ = (∏ j, poch (lineNu F.w m l j) (γ j)) *
      ∏ j, (Gamma (lineNu F.w (m + natZ γ) l j))⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [inv_Gamma_eq_poch (lineNu F.w m l j) (γ j)]
    congr 3
    simp [lineNu, natZ]
    ring
  simp only [normF, rho, h2, h3]
  rw [h5, inv_Gamma_eq_poch z (F.Lp - ∑ j, γ j)]
  ring

/-- **The normalization under `ν → ν + e_a - e_b`.** -/
theorem normF_raise_lower {a b : Fin N} (hab : a ≠ b) {m m' : Fin N → ℤ}
    (hm : ∀ j, m' j = m j + (if j = a then 1 else 0) - (if j = b then 1 else 0)) (d₀ l : ℂ) :
    lineNu F.w m l a * F.normF m' d₀ l = (lineNu F.w m l b - 1) * F.normF m d₀ l := by
  have hs : ∑ j, m' j = ∑ j, m j := by
    simp only [hm, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  have hs' : ∑ j, lineNu F.w m' l j = ∑ j, lineNu F.w m l j := by
    simp only [lineNu, Finset.sum_add_distrib]
    congr 1
    exact_mod_cast hs
  have ha : lineNu F.w m' l a = lineNu F.w m l a + 1 := by
    simp [lineNu, hm, hab]; ring
  have hb : lineNu F.w m' l b = lineNu F.w m l b - 1 := by
    simp [lineNu, hm, Ne.symm hab]; ring
  have hr : ∏ j ∈ (Finset.univ.erase a).erase b, (Gamma (lineNu F.w m' l j))⁻¹ =
      ∏ j ∈ (Finset.univ.erase a).erase b, (Gamma (lineNu F.w m l j))⁻¹ :=
    Finset.prod_congr rfl fun j hj => by
      have hjb := Finset.ne_of_mem_erase hj
      have hja := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
      simp [lineNu, hm, hja, hjb]
  have hsplit : ∀ f : Fin N → ℂ, ∏ j, f j = f a * (f b * ∏ j ∈ (Finset.univ.erase a).erase b,
      f j) := fun f => by
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a),
      ← Finset.mul_prod_erase (Finset.univ.erase a) f (Finset.mem_erase.2 ⟨hab.symm,
        Finset.mem_univ b⟩)]
  simp only [normF, hs', hsplit (fun j => (Gamma (lineNu F.w m' l j))⁻¹),
    hsplit (fun j => (Gamma (lineNu F.w m l j))⁻¹), hr, ha, hb]
  have e1 := mul_inv_Gamma_add_one (lineNu F.w m l a)
  have e2 := mul_inv_Gamma_add_one (lineNu F.w m l b - 1)
  rw [sub_add_cancel] at e2
  rw [← e2, ← e1]
  ring

/-- **The normalization under `ν → ν + e_a`.** -/
theorem normF_raise {a : Fin N} {m m' : Fin N → ℤ}
    (hm : ∀ j, m' j = m j + if j = a then 1 else 0) (d₀ l : ℂ) :
    lineNu F.w m l a * F.normF m' d₀ l =
      (F.Lp * lineD F.h d₀ l / 2 - ∑ j, lineNu F.w m l j - 1) * F.normF m d₀ l := by
  have hs : ∑ j, m' j = ∑ j, m j + 1 := by
    simp only [hm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hs' : F.Lp * lineD F.h d₀ l / 2 - ∑ j, lineNu F.w m' l j =
      (F.Lp * lineD F.h d₀ l / 2 - ∑ j, lineNu F.w m l j - 1) := by
    simp only [lineNu, Finset.sum_add_distrib]
    rw [show (∑ j, (m' j : ℂ)) = ∑ j, (m j : ℂ) + 1 by exact_mod_cast hs]
    ring
  have ha : lineNu F.w m' l a = lineNu F.w m l a + 1 := by simp [lineNu, hm]; ring
  have hr : ∏ j ∈ Finset.univ.erase a, (Gamma (lineNu F.w m' l j))⁻¹ =
      ∏ j ∈ Finset.univ.erase a, (Gamma (lineNu F.w m l j))⁻¹ :=
    Finset.prod_congr rfl fun j hj => by simp [lineNu, hm, Finset.ne_of_mem_erase hj]
  simp only [normF, hs', ← Finset.mul_prod_erase Finset.univ
    (fun j => (Gamma (lineNu F.w m' l j))⁻¹) (Finset.mem_univ a),
    ← Finset.mul_prod_erase Finset.univ (fun j => (Gamma (lineNu F.w m l j))⁻¹) (Finset.mem_univ a),
    hr, ha]
  have e1 := mul_inv_Gamma_add_one (lineNu F.w m l a)
  have e2 := mul_inv_Gamma_add_one (F.Lp * lineD F.h d₀ l / 2 - ∑ j, lineNu F.w m l j - 1)
  rw [sub_add_cancel] at e2
  rw [← e2, ← e1]
  ring

/-! ### Normalized relations -/

theorem eventually_lineD_ne (d₀ : ℂ) : ∀ᶠ l in atRe, lineD F.h d₀ l / 2 ≠ 0 := by
  filter_upwards [eventually_re_gt (|d₀.re| + 1)] with l hl h
  have h' := congrArg Complex.re h
  simp only [lineD, div_ofNat_re, add_re, mul_re, re_ofNat, im_ofNat, sub_zero,
    zero_re, natCast_re, natCast_im, mul_zero, show ((2 : ℂ) * F.h).im = 0 by simp,
    zero_mul] at h'
  have := neg_abs_le d₀.re
  have := abs_nonneg d₀.re
  have hh : (1 : ℝ) ≤ F.h := by exact_mod_cast F.one_le_h
  nlinarith

/-- **A dimension-shift relation for `Jline` gives one for `Iline`**, for `re λ` large. -/
theorem eventually_normalized {n : Fin N → ℤ} {d₀ : ℂ} {P : ℂ → ℂ} (r : MonoList N)
    (hr : ∀ t ∈ r, ∑ j, t.2 j ≤ F.Lp)
    (hJ : ∀ᶠ l in atRe, P l * F.Jline n d₀ l -
      lineD F.h d₀ l / 2 * (r.map fun t => (t.1 : ℂ) * F.Jline (n + natZ t.2) (d₀ + 2) l).sum
        = 0) :
    ∀ᶠ l in atRe, P l * F.Iline n d₀ l =
      (r.map fun t => (t.1 : ℂ) * F.rho n d₀ t.2 l * F.Iline (n + natZ t.2) (d₀ + 2) l).sum := by
  filter_upwards [hJ, F.eventually_lineD_ne d₀] with l h hd
  calc P l * F.Iline n d₀ l = F.normF n d₀ l * (lineD F.h d₀ l / 2 *
        (r.map fun t => (t.1 : ℂ) * F.Jline (n + natZ t.2) (d₀ + 2) l).sum) := by
        rw [Iline]; linear_combination F.normF n d₀ l * h
    _ = _ := by
      rw [← list_sum_map_mul_left, ← list_sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
      have e := F.normF_dimShift n t.2 (hr t ht) d₀ l hd
      rw [Iline]
      linear_combination (t.1 : ℂ) * F.Jline (n + natZ t.2) (d₀ + 2) l * e

theorem analyticAt_rho (m : Fin N → ℤ) (d₀ : ℂ) (γ : Fin N → ℕ) (z : ℂ) :
    AnalyticAt ℂ (F.rho m d₀ γ) z := by
  unfold rho
  refine (analyticAt_poch (by unfold lineD lineNu; fun_prop) _).mul ?_
  exact Finset.analyticAt_fun_prod _ fun j _ => analyticAt_poch (by unfold lineNu; fun_prop) _

/-- **The normalized relation near `λ = 0`** (identity theorem). -/
theorem nhdsNE_normalized {n : Fin N → ℤ} {d₀ : ℂ} {P : ℂ → ℂ} (hP : Differentiable ℂ P)
    (r : MonoList N) (h : ∀ᶠ l in atRe, P l * F.Iline n d₀ l =
      (r.map fun t => (t.1 : ℂ) * F.rho n d₀ t.2 l * F.Iline (n + natZ t.2) (d₀ + 2) l).sum) :
    ∀ᶠ l in 𝓝[≠] (0 : ℂ), P l * F.Iline n d₀ l =
      (r.map fun t => (t.1 : ℂ) * F.rho n d₀ t.2 l * F.Iline (n + natZ t.2) (d₀ + 2) l).sum :=
  eventuallyEq_nhdsNE_of_atRe
    (fun z hz => (hP.analyticAt z).meromorphicAt.mul (F.meromorphicOn_Iline n d₀ z hz))
    (meromorphicOn_list_sum r fun t _ z hz =>
      ((analyticAt_const.mul (F.analyticAt_rho n d₀ t.2 z)).meromorphicAt).mul
        (F.meromorphicOn_Iline _ _ z hz)) h zero_mem_halfPlane

/-! ### The raising relation and finiteness -/

theorem lowZ_single (i : Fin N) : lowZ (Pi.single i 1) i = 0 := by
  funext j
  by_cases h : j = i
  · subst h; simp [lowZ]
  · simp [lowZ, h]

theorem polyEval_single' (i : Fin N) (x : Fin N → ℝ) :
    polyEval [((1 : ℤ), Pi.single i 1)] x = x i := by
  simp only [polyEval, monoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Int.cast_one, one_mul, add_zero]
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- **The raising relation** `νᵢ J(ν, d) = (d/2) Σ c_γ(xᵢ ∂ᵢ G) J(ν + γ, d + 2)` along the line,
for `re λ` large. -/
theorem eventually_raise (i : Fin N) (n : Fin N → ℤ) (d₀ : ℂ) :
    ∀ᶠ l in atRe, lineNu F.w n l i * F.Jline n d₀ l - lineD F.h d₀ l / 2 *
      ((F.R i).map fun t => (t.1 : ℂ) * F.Jline (n + natZ t.2) (d₀ + 2) l).sum = 0 := by
  have h := F.eventually_annihilator
    (fun b => if b = i then [((1 : ℤ), Pi.single i 1)] else [])
    [] (F.R i) (fun b => if b = i then F.R i else [])
    (fun x => by
      rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb, polyEval]) (by simp)]
      simp only [↓reduceIte]
      rw [polyEval_single', F.raise]
      simp [polyEval])
    (fun b x => by
      by_cases hb : b = i
      · subst hb
        simp only [↓reduceIte]
        rw [polyEval_single', F.raise]
      · simp [hb, polyEval]) n d₀
  filter_upwards [h] with l hl
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)] at hl
  simpa [lowZ_single] using hl

/-- `rho` without its factor `νᵢ` (for `γᵢ ≥ 1`). -/
noncomputable def rho' (i : Fin N) (m : Fin N → ℤ) (d₀ : ℂ) (γ : Fin N → ℕ) (l : ℂ) : ℂ :=
  poch (F.Lp * lineD F.h d₀ l / 2 - ∑ j, lineNu F.w m l j) (F.Lp - ∑ j, γ j) *
    (poch (lineNu F.w m l i + 1) (γ i - 1) *
      ∏ j ∈ Finset.univ.erase i, poch (lineNu F.w m l j) (γ j))

theorem rho_eq_mul (i : Fin N) (m : Fin N → ℤ) (d₀ : ℂ) {γ : Fin N → ℕ} (hγ : 1 ≤ γ i)
    (l : ℂ) : F.rho m d₀ γ l = lineNu F.w m l i * F.rho' i m d₀ γ l := by
  unfold rho rho'
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  obtain ⟨k, hk⟩ : ∃ k, γ i = k + 1 := ⟨γ i - 1, by omega⟩
  rw [hk, poch_succ, Nat.add_sub_cancel]
  ring

theorem analyticAt_rho' (i : Fin N) (m : Fin N → ℤ) (d₀ : ℂ) (γ : Fin N → ℕ) (z : ℂ) :
    AnalyticAt ℂ (F.rho' i m d₀ γ) z := by
  unfold rho'
  refine (analyticAt_poch (by unfold lineD lineNu; fun_prop) _).mul
    ((analyticAt_poch (by unfold lineNu; fun_prop) _).mul ?_)
  exact Finset.analyticAt_fun_prod _ fun j _ => analyticAt_poch (by unfold lineNu; fun_prop) _

/-- The deficiency `Σⱼ (1 - nⱼ)⁺` of a label. -/
def defic (n : Fin N → ℤ) : ℕ := ∑ j, (1 - n j).toNat

theorem defic_lt {n : Fin N → ℤ} {i : Fin N} (hi : n i ≤ 0) {γ : Fin N → ℕ} (hγ : 1 ≤ γ i) :
    defic (n + natZ γ) < defic n :=
  Finset.sum_lt_sum (fun j _ => by simp only [Pi.add_apply, natZ]; omega)
    ⟨i, Finset.mem_univ _, by simp only [Pi.add_apply, natZ]; omega⟩

theorem eventually_lineNu_ne (n : Fin N → ℤ) (i : Fin N) :
    ∀ᶠ l in 𝓝[≠] (0 : ℂ), lineNu F.w n l i ≠ 0 := by
  rcases eq_or_ne (n i) 0 with h0 | h0
  · have hw : (F.w i : ℂ) ≠ 0 := by have := F.one_le_w i; exact_mod_cast (by omega : F.w i ≠ 0)
    exact eventually_nhdsWithin_of_forall fun l hl => by simpa [lineNu, h0, hw] using hl
  · refine nhdsWithin_le_nhds ((?_ : ContinuousAt (fun l => lineNu F.w n l i) 0).eventually_ne ?_)
    · unfold lineNu; fun_prop
    · simpa [lineNu] using h0

/-- **Finiteness at every integer label**: for `d₀ ∉ ℚ` the normalized continued integral along
the line through any label `n ∈ ℤᴺ` tends to `val n d₀` as `λ → 0`. -/
theorem tendsto_Iline (n : Fin N → ℤ) {d₀ : ℂ} (hd : Irr d₀) :
    Tendsto (F.Iline n d₀) (𝓝[≠] 0) (𝓝 (F.val n d₀)) := by
  suffices h : ∀ k, ∀ n : Fin N → ℤ, defic n ≤ k → ∀ d₀, Irr d₀ →
      ∃ v, Tendsto (F.Iline n d₀) (𝓝[≠] 0) (𝓝 v) by
    exact tendsto_nhds_limUnder (h _ n le_rfl d₀ hd)
  intro k
  induction k with
  | zero =>
    intro n hn d₀ hd
    have hpos : ∀ j, 1 ≤ n j := fun j => by
      have := (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hn)) j (Finset.mem_univ j)
      omega
    exact ⟨_, (F.continuousAt_Iline_pos hpos hd).tendsto.mono_left nhdsWithin_le_nhds⟩
  | succ k ih =>
    intro n hn d₀ hd
    by_cases hpos : ∀ j, 1 ≤ n j
    · exact ⟨_, (F.continuousAt_Iline_pos hpos hd).tendsto.mono_left nhdsWithin_le_nhds⟩
    push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have hi' : n i ≤ 0 := by omega
    have hrel := F.nhdsNE_normalized (P := fun l => lineNu F.w n l i) (by unfold lineNu; fun_prop)
      (F.R i) (F.eventually_normalized (F.R i) (fun t ht => (F.raise_spec i t ht).2)
        (F.eventually_raise i n d₀))
    have hIH : ∀ t ∈ F.R i, Tendsto (F.Iline (n + natZ t.2) (d₀ + 2)) (𝓝[≠] 0)
        (𝓝 (F.val (n + natZ t.2) (d₀ + 2))) := fun t ht =>
      tendsto_nhds_limUnder (ih _ (by have := defic_lt hi' (F.raise_spec i t ht).1; omega) _
        hd.add_two)
    refine ⟨_, (TwoLoopSESector.tendsto_list_sum (F.R i)
      (f := fun t l => (t.1 : ℂ) * F.rho' i n d₀ t.2 l *
      F.Iline (n + natZ t.2) (d₀ + 2) l) fun t ht => (tendsto_const_nhds.mul
        ((F.analyticAt_rho' i n d₀ t.2 0).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds)).mul (hIH t ht)).congr' ?_⟩
    filter_upwards [hrel, F.eventually_lineNu_ne n i] with l h1 h2
    apply mul_left_cancel₀ h2
    rw [h1, ← list_sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [F.rho_eq_mul i n d₀ (F.raise_spec i t ht).1]
    ring

/-! ### Relations at `λ = 0` and scaleless sectors -/

/-- **A dimension-shift relation at `λ = 0`.** -/
theorem val_relation {n : Fin N → ℤ} {d₀ : ℂ} (hd : Irr d₀) {P : ℂ → ℂ}
    (hP : Differentiable ℂ P) (r : MonoList N) (hr : ∀ t ∈ r, ∑ j, t.2 j ≤ F.Lp)
    (hJ : ∀ᶠ l in atRe, P l * F.Jline n d₀ l -
      lineD F.h d₀ l / 2 * (r.map fun t => (t.1 : ℂ) * F.Jline (n + natZ t.2) (d₀ + 2) l).sum
        = 0) :
    P 0 * F.val n d₀ =
      (r.map fun t => (t.1 : ℂ) * F.rho n d₀ t.2 0 * F.val (n + natZ t.2) (d₀ + 2)).sum := by
  have h := F.nhdsNE_normalized hP r (F.eventually_normalized r hr hJ)
  have T1 : Tendsto (fun l => P l * F.Iline n d₀ l) (𝓝[≠] 0) (𝓝 (P 0 * F.val n d₀)) :=
    ((hP 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul (F.tendsto_Iline n hd)
  have T2 := TwoLoopSESector.tendsto_list_sum r (f := fun t l => (t.1 : ℂ) * F.rho n d₀ t.2 l *
    F.Iline (n + natZ t.2) (d₀ + 2) l) fun t _ => (tendsto_const_nhds.mul
      ((F.analyticAt_rho n d₀ t.2 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).mul
      (F.tendsto_Iline _ hd.add_two)
  exact tendsto_nhds_unique (T1.congr' h) T2

theorem natZ_zero : natZ (0 : Fin N → ℕ) = 0 := by funext j; simp [natZ]

/-- The scaling relation `(ν_c - d/2) J(ν, d) = (d/2) Σ c_γ(r) J(ν + γ, d + 2)` along the line,
from `x_c ∂_c G = G + r`. -/
theorem eventually_scaling (c : Fin N) (r : MonoList N)
    (hr : ∀ x, x c * F.G' c x = F.S.G.eval x + polyEval r x) (n : Fin N → ℤ) (d₀ : ℂ) :
    ∀ᶠ l in atRe, (lineNu F.w n l c - lineD F.h d₀ l / 2) * F.Jline n d₀ l - lineD F.h d₀ l / 2 *
      (r.map fun t => (t.1 : ℂ) * F.Jline (n + natZ t.2) (d₀ + 2) l).sum = 0 := by
  have h := F.eventually_annihilator
    (fun b => if b = c then [((1 : ℤ), Pi.single c 1)] else [])
    [((1 : ℤ), (0 : Fin N → ℕ))] r (fun b => if b = c then F.R c else [])
    (fun x => by
      rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb, polyEval]) (by simp)]
      simp only [↓reduceIte]
      rw [polyEval_single', hr]
      simp [polyEval, monoEval])
    (fun b x => by
      by_cases hb : b = c
      · subst hb
        simp only [↓reduceIte]
        rw [polyEval_single', F.raise]
      · simp [hb, polyEval]) n d₀
  filter_upwards [h] with l hl
  rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)] at hl
  simp only [↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    lowZ_single, natZ_zero, add_zero, Int.cast_one, one_mul] at hl
  rw [Pi.single_eq_same] at hl
  linear_combination hl

theorem rho_zero_eq_zero {m : Fin N → ℤ} {d₀ : ℂ} {γ : Fin N → ℕ} {a : Fin N} (ha : m a ≤ 0)
    (hγ : 1 ≤ m a + γ a) : F.rho m d₀ γ 0 = 0 := by
  unfold rho
  rw [Finset.prod_eq_zero (Finset.mem_univ a) (by simpa [lineNu] using poch_eq_zero ha hγ),
    mul_zero]

/-- The depth of a label in the sector `S`. -/
def depth (S : Finset (Fin N)) (n : Fin N → ℤ) : ℕ := ∑ a ∈ S, (-n a).toNat

/-- **A scaleless sector vanishes**: if `x_c ∂_c G = G + r` with every monomial of `r` divisible
by some `x_a`, `a ∈ S`, then `val n d₀ = 0` whenever `n_a ≤ 0` for all `a ∈ S` and `d₀ ∉ ℚ`. -/
theorem val_eq_zero_of_sector (S : Finset (Fin N)) (c : Fin N) (r : MonoList N)
    (hr : ∀ x, x c * F.G' c x = F.S.G.eval x + polyEval r x)
    (hspec : ∀ t ∈ r, ∑ j, t.2 j ≤ F.Lp ∧ ∃ a ∈ S, 1 ≤ t.2 a) (n : Fin N → ℤ)
    (hn : ∀ a ∈ S, n a ≤ 0) {d₀ : ℂ} (hd : Irr d₀) : F.val n d₀ = 0 := by
  suffices h : ∀ k, ∀ n : Fin N → ℤ, depth S n ≤ k → (∀ a ∈ S, n a ≤ 0) → ∀ d₀, Irr d₀ →
      F.val n d₀ = 0 from h _ n le_rfl hn d₀ hd
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro n hk hn d₀ hd
  have hrel := F.val_relation hd (P := fun l => lineNu F.w n l c - lineD F.h d₀ l / 2)
    (by unfold lineNu lineD; fun_prop) r (fun t ht => (hspec t ht).1)
    (F.eventually_scaling c r hr n d₀)
  have hsum : (r.map fun t => (t.1 : ℂ) * F.rho n d₀ t.2 0 *
      F.val (n + natZ t.2) (d₀ + 2)).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    obtain ⟨a, haS, hta⟩ := (hspec t ht).2
    by_cases hin : ∀ b ∈ S, (n + natZ t.2) b ≤ 0
    · have hlt : depth S (n + natZ t.2) < depth S n := by
        refine Finset.sum_lt_sum (fun b hb => ?_) ⟨a, haS, ?_⟩
        · have := hin b hb
          simp only [Pi.add_apply, natZ] at this ⊢
          omega
        · have := hin a haS
          simp only [Pi.add_apply, natZ] at this ⊢
          omega
      rw [ih _ (by omega) _ le_rfl hin _ hd.add_two, mul_zero]
    · push Not at hin
      obtain ⟨b, hbS, hb⟩ := hin
      simp only [Pi.add_apply, natZ] at hb
      rw [F.rho_zero_eq_zero (hn b hbS) (by omega), mul_zero, zero_mul]
  rw [hsum] at hrel
  have hne : lineNu F.w n 0 c - lineD F.h d₀ 0 / 2 ≠ 0 := by
    intro h
    apply hd (2 * n c)
    simp only [lineNu, lineD, add_zero, mul_zero] at h
    push_cast
    linear_combination -2 * h
  exact (mul_eq_zero.1 hrel).resolve_left hne

end LineFamily

end QED.DimReg.LineCont
