/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceDeriv

/-!
# The face theorem at large exponent: `Iline3` as an integral over the face

At a label `n` with `n₇ = -k₇ ≤ 0`, `n₈ = -k₈ ≤ 0` (`K = k₇ + k₈`), the nine-variable integral
continued in `(ν₇, ν₈)` to `(-k₇, -k₈)` is
`(-1)^K N₉ ∫_{(0,∞)^7} x'^{ν'-1} (∂₇^{k₇} ∂₈^{k₈} G^{-d/2})(x', 0, 0) dx'`, where `N₉` is the
normalization of the nine-variable integral without its factor `1/(Γ(ν₇) Γ(ν₈))`
(the one-variable statement: `(1/Γ(s)) ∫₀^∞ x^{s-1} g → (-1)^k g^{(k)}(0)` as `s → -k`).
Here the right side is identified with `QED.DimReg.ThreeLoop.Iline3`, exactly, on the lines
`λ ↦ (n' + λw₇, d₀ + 6λ)` for `re λ` large (no limit is taken):

* `norm9`: `N₉ = Γ(d/2) / (Γ(2d - |ν'| + K) ∏_{b < 7} Γ(ν'_b))`;
* `coef3_mul_normF`: the coefficient of a term `(j, c x^β)` of `Iline3` times the normalization
  of its seven-variable integral is `(-1)^K c (-d/2)↓ⱼ N₉`;
* **`eventually_Iline3_eq`**: for `re λ` large,
  `Iline3 n d₀ λ = (-1)^K N₉ ∫_{(0,∞)^7} x^{ν'-1} faceDeriv (aPolys k₇ k₈) d (x, 0, 0) dx`,
  with `faceDeriv (aPolys k₇ k₈) d = ∂₇^{k₇} ∂₈^{k₈} G^{-d/2}`
  (`QED.DimReg.ThreeLoop.hasDerivAt_faceDeriv`);
* `mellin_step`, `mellin_step_norm`: one partial integration in `x_b` over `(0,∞)^9`, exact
  where the two integrals converge:
  `(1/Γ(ν_b)) ∫ x^{ν-1} ∂^A G^{-d/2} = -(1/Γ(ν_b + 1)) ∫ x_b x^{ν-1} ∂_b ∂^A G^{-d/2}`.

Not here: the convergence of the nine-variable integrals near the face (the integrability
hypotheses of `mellin_step` at `re ν₇, re ν₈ > 0` small and `re λ` large) and the last step
`∫₀^∞ ∂_b Ψ dx_b = -Ψ|_{x_b = 0}` at `ν_b = -k_b`, which together give the continuation of the
normalized nine-variable integral in `(ν₇, ν₈)` and its value `Iline3` at `(-k₇, -k₈)`.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory QED.DimReg QED.DimReg.Sector QED.DimReg.LineCont
open QED.DimReg.TwoLoopSESector (poch atRe eventually_re_gt eventually_list inv_Gamma_eq_poch)

namespace QED.DimReg.ThreeLoop

/-! ### Small facts -/

theorem F7_h : F7.h = h7 := rfl

theorem F7_w : F7.w = w7 := rfl

theorem F7_Lp : F7.Lp = 4 := rfl

theorem F7_G : (fun x : Fin 7 → ℝ => F7.S.G.eval x) = fun x => g7.eval x := by
  rw [show F7.S = S7 from rfl, S7_G]

theorem sum_getD_fin : ∀ (N : ℕ) (β : List ℕ), β.length ≤ N → ∑ b : Fin N, β.getD b 0 = β.sum
  | 0, β, h => by simp [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]
  | N + 1, [], _ => by simp
  | N + 1, x :: β, h => by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ,
      List.sum_cons]
    rw [sum_getD_fin N β (by simpa using h)]

theorem sum_take_le (α : List ℕ) (m : ℕ) : (α.take m).sum ≤ α.sum := by
  conv_rhs => rw [← List.take_append_drop m α]
  rw [List.sum_append]
  omega

theorem sum_range_list (f : ℕ → ℂ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem lbl3_nil (n : Fin 9 → ℤ) (b : Fin 7) : lbl3 n [] b = n (Fin.castLE (by omega) b) := by
  simp [lbl3]

theorem lineNu_lbl3 (n : Fin 9 → ℤ) (β : List ℕ) (l : ℂ) (b : Fin 7) :
    lineNu w7 (lbl3 n β) l b = lineNu w7 (lbl3 n []) l b + (β.getD b 0 : ℕ) := by
  simp only [lineNu, lbl3, List.getD_nil, Nat.cast_zero, add_zero]
  push_cast; ring

theorem lineD_add (d₀ l : ℂ) (j : ℕ) : lineD h7 (d₀ + 2 * j) l = lineD h7 d₀ l + 2 * j := by
  simp only [lineD]; ring

/-! ### The normalization -/

/-- The normalization of the nine-variable integral at `(ν', -k₇, -k₈)` without its factor
`1/(Γ(ν₇) Γ(ν₈))`: `Γ(d/2) / (Γ(2d - |ν'| + K) ∏_{b < 7} Γ(ν'_b))`, along the line. -/
noncomputable def norm9 (n : Fin 9 → ℤ) (d₀ l : ℂ) : ℂ :=
  Gamma (lineD h7 d₀ l / 2) *
    (Gamma (2 * lineD h7 d₀ l - ∑ b : Fin 7, lineNu w7 (lbl3 n []) l b + (ord7 n + ord8 n)))⁻¹ *
    ∏ b : Fin 7, (Gamma (lineNu w7 (lbl3 n []) l b))⁻¹

theorem Gamma_add_nat_eq {s : ℂ} (hs : 0 < s.re) (j : ℕ) : Gamma (s + j) = poch s j * Gamma s := by
  have h := inv_Gamma_eq_poch s j
  have h1 : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have h2 : Gamma (s + j) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [add_re, natCast_re]; positivity)
  field_simp at h
  linear_combination h

/-- **The coefficients of `Iline3` against the nine-variable normalization.** -/
theorem coef3_mul_normF (n : Fin 9 → ℤ) {d₀ l : ℂ} (hre : 0 < (lineD h7 d₀ l / 2).re) (j : ℕ)
    (β : List ℕ) (c : ℤ) (hβ : β.length ≤ 7) (hdeg : β.sum + (ord7 n + ord8 n) ≤ 4 * j) :
    coef3 n d₀ j β c l * F7.normF (lbl3 n β) (d₀ + 2 * j) l =
      (-1) ^ (ord7 n + ord8 n) * c * fallC (-(lineD h7 d₀ l / 2)) j * norm9 n d₀ l := by
  set ν : Fin 7 → ℂ := lineNu w7 (lbl3 n []) l with hν
  set d : ℂ := lineD h7 d₀ l with hd
  set K : ℕ := ord7 n + ord8 n with hK
  set z : ℂ := 2 * d - ∑ b : Fin 7, ν b + (ord7 n + ord8 n) with hz
  have hm : ((4 * j - β.sum - K : ℕ) : ℂ) = 4 * j - β.sum - K := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hsβ : ∑ b : Fin 7, ((β.getD b 0 : ℕ) : ℂ) = β.sum := by
    rw [← Nat.cast_sum, sum_getD_fin 7 β hβ]
  have hGam : Gamma (lineD h7 (d₀ + 2 * j) l / 2) = poch (d / 2) j * Gamma (d / 2) := by
    rw [lineD_add, show (d + 2 * j) / 2 = d / 2 + j by ring, Gamma_add_nat_eq hre]
  have hz' : ((4 : ℕ) : ℂ) * lineD h7 (d₀ + 2 * j) l / 2 -
      ∑ b, lineNu w7 (lbl3 n β) l b = z + ((4 * j - β.sum - K : ℕ) : ℂ) := by
    rw [lineD_add, hm]
    simp only [lineNu_lbl3 n β l, Finset.sum_add_distrib, hsβ, hz, hK]
    push_cast; ring
  have hprod : (∏ b : Fin 7, poch (ν b) (β.getD b 0)) *
      ∏ b : Fin 7, (Gamma (lineNu w7 (lbl3 n β) l b))⁻¹ = ∏ b : Fin 7, (Gamma (ν b))⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [lineNu_lbl3, inv_Gamma_eq_poch (ν b) (β.getD b 0)]
  have hzp := inv_Gamma_eq_poch z (4 * j - β.sum - K)
  unfold coef3 LineFamily.normF
  rw [F7_h, F7_w, F7_Lp, hGam, hz', fallC_neg, norm9]
  simp only [← hν, ← hd]
  rw [← hz]
  calc _ = (-1) ^ (K + j) * c * poch (d / 2) j * Gamma (d / 2) *
        (poch z (4 * j - β.sum - K) * (Gamma (z + ((4 * j - β.sum - K : ℕ) : ℂ)))⁻¹) *
        ((∏ b : Fin 7, poch (ν b) (β.getD b 0)) *
          ∏ b : Fin 7, (Gamma (lineNu w7 (lbl3 n β) l b))⁻¹) := by ring
    _ = _ := by rw [← hzp, hprod, pow_add]; ring

/-! ### The face theorem at large exponent -/

theorem mem_terms3 {n : Fin 9 → ℤ} {t : ℕ × (List ℕ × ℤ)} (ht : t ∈ terms3 n) :
    t.2.1.length ≤ 7 ∧ (t.2.2 ≠ 0 → t.2.1.sum + (ord7 n + ord8 n) ≤ 4 * t.1) := by
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hj
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
  refine ⟨List.length_take_le _ _, fun h0 => ?_⟩
  have := aPolys_deg (ord7 n) (ord8 n) j u (List.mem_filter.mp hu).1 h0
  have := sum_take_le u.1 7
  simp only at *
  omega

theorem lpIntegrand_term (n : Fin 9 → ℤ) (d₀ l : ℂ) (j : ℕ) (β : List ℕ) {x : Fin 7 → ℝ}
    (hx : x ∈ posOrthant 7) :
    lpIntegrand (fun x => F7.S.G.eval x) (lineNu F7.w (lbl3 n β) l) (lineD F7.h (d₀ + 2 * j) l) x =
      (mono β x : ℂ) * ((∏ b, (x b : ℂ) ^ (lineNu w7 (lbl3 n []) l b - 1)) *
        ((g7.eval x : ℝ) : ℂ) ^ (-(lineD h7 d₀ l / 2) - j)) := by
  have hnu : lineNu F7.w (lbl3 n β) l =
      natShift (lineNu w7 (lbl3 n []) l) fun b => β.getD b 0 := by
    funext b; rw [natShift, F7_w, lineNu_lbl3]
  rw [hnu, lpIntegrand_natShift _ _ _ _ hx, F7_G, F7_h, lineD_add]
  simp only [lpIntegrand, monoEval]
  congr 3
  ring

theorem map_sum_eval (Q : ZPoly) (a B : ℂ) (x : Fin 7 → ℝ) :
    (Q.map fun s => a * s.2 * ((mono s.1 x : ℂ) * B)).sum = a * (ZPoly.eval Q x : ℂ) * B := by
  induction Q with
  | nil => simp
  | cons s Q ih =>
    simp only [List.map_cons, List.sum_cons, ih, ZPoly.eval_cons]
    push_cast; ring

/-- **The face theorem at large exponent.** For `re λ` large, on the line through `n`,
`Iline3 n d₀ λ = (-1)^K N₉ ∫_{(0,∞)^7} x^{ν'-1} (∂₇^{k₇} ∂₈^{k₈} G^{-d/2})(x, 0, 0) dx`. -/
theorem eventually_Iline3_eq (n : Fin 9 → ℤ) (d₀ : ℂ) :
    ∀ᶠ l in atRe, Iline3 n d₀ l = (-1) ^ (ord7 n + ord8 n) * norm9 n d₀ l *
      ∫ x in posOrthant 7, (∏ b, (x b : ℂ) ^ (lineNu w7 (lbl3 n []) l b - 1)) *
        faceDeriv (aPolys (ord7 n) (ord8 n)) (lineD h7 d₀ l) (ext7 x) := by
  filter_upwards [eventually_list (terms3 n) fun t =>
      F7.eventually_Jline_eq (lbl3 n t.2.1) (d₀ + 2 * t.1), eventually_re_gt |d₀.re|]
    with l hJ hl
  have hre : 0 < (lineD h7 d₀ l / 2).re := by
    have := neg_abs_le d₀.re
    have := abs_nonneg d₀.re
    simp only [lineD, h7, div_ofNat_re, add_re, mul_re, re_ofNat, im_ofNat, natCast_re,
      natCast_im]
    norm_num
    linarith
  set K := ord7 n + ord8 n
  set A := aPolys (ord7 n) (ord8 n)
  set P : (Fin 7 → ℝ) → ℂ := fun x => ∏ b, (x b : ℂ) ^ (lineNu w7 (lbl3 n []) l b - 1)
  set f : ℕ × (List ℕ × ℤ) → (Fin 7 → ℝ) → ℂ := fun t x =>
    fallC (-(lineD h7 d₀ l / 2)) t.1 * t.2.2 *
    lpIntegrand (fun x => F7.S.G.eval x) (lineNu F7.w (lbl3 n t.2.1) l)
      (lineD F7.h (d₀ + 2 * t.1) l) x
  have hint : ∀ t ∈ terms3 n, IntegrableOn (f t) (posOrthant 7) :=
    fun t ht => (hJ t ht).1.const_mul _
  -- each term
  have hterm : ∀ t ∈ terms3 n, coef3 n d₀ t.1 t.2.1 t.2.2 l * F7.Iline (lbl3 n t.2.1)
      (d₀ + 2 * t.1) l = (-1) ^ K * norm9 n d₀ l * ∫ x in posOrthant 7, f t x := by
    intro t ht
    obtain ⟨hβ, hdeg⟩ := mem_terms3 ht
    rw [LineFamily.Iline, ← mul_assoc, ← (hJ t ht).2, lpIntegral]
    simp only [f]
    rw [integral_const_mul]
    rcases eq_or_ne t.2.2 0 with h0 | h0
    · simp [coef3, h0]
    · rw [coef3_mul_normF n hre t.1 t.2.1 t.2.2 hβ (hdeg h0)]
      ring
  unfold Iline3
  rw [List.map_congr_left hterm, list_sum_map_mul_left,
    ← integral_list_sum _ hint]
  congr 1
  refine setIntegral_congr_fun (measurableSet_posOrthant 7) fun x hx => ?_
  simp only [f, lpIntegrand_term n d₀ l _ _ hx]
  rw [faceDeriv, lpPoly_eval_ext7, length_aPolys, ← sum_range_list, ← list_sum_map_mul_left]
  simp only [terms3, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, List.map_map]
  simp only [Function.comp_def, eval_ext7]
  rw [map_sum_eval]
  ring

/-! ### The Mellin step in the nine-variable orthant -/

/-- The Mellin weight `∏ᵢ xᵢ^{νᵢ-1}` in nine variables. -/
noncomputable def wt9 (ν : Fin 9 → ℂ) (x : Fin 9 → ℝ) : ℂ := ∏ i, (x i : ℂ) ^ (ν i - 1)

theorem wt9_update (ν : Fin 9 → ℂ) (x : Fin 9 → ℝ) (b : Fin 9) (t : ℝ) :
    wt9 ν (Function.update x b t) =
      (t : ℂ) ^ (ν b - 1) * ∏ i ∈ Finset.univ.erase b, (x i : ℂ) ^ (ν i - 1) := by
  rw [wt9, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
  simp only [Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- **One Mellin step in the coordinate `x_b`** (exact, in the region of convergence): if
`x^{ν-1} ∂^A G^{-d/2}` and `x^{ν+e_b-1} ∂_b ∂^A G^{-d/2}` are integrable over `(0,∞)^9`, then
`ν_b ∫ x^{ν-1} ∂^A G^{-d/2} = -∫ x_b x^{ν-1} ∂_b ∂^A G^{-d/2}`. -/
theorem mellin_step (A : List ZPoly) (d : ℂ) (ν : Fin 9 → ℂ) (b : Fin 9)
    (h1 : IntegrableOn (fun x => wt9 ν x * faceDeriv A d x) (posOrthant 9))
    (h2 : IntegrableOn (fun x => (x b : ℂ) * wt9 ν x * faceDeriv (derivStep b A) d x)
      (posOrthant 9)) :
    ν b * ∫ x in posOrthant 9, wt9 ν x * faceDeriv A d x =
      -∫ x in posOrthant 9, (x b : ℂ) * wt9 ν x * faceDeriv (derivStep b A) d x := by
  set φ : (Fin 9 → ℝ) → ℂ := fun x => (x b : ℂ) * wt9 ν x * faceDeriv A d x
  set φ' : (Fin 9 → ℝ) → ℂ := fun x => ν b * (wt9 ν x * faceDeriv A d x) +
    (x b : ℂ) * wt9 ν x * faceDeriv (derivStep b A) d x
  have hd : ∀ x ∈ posOrthant 9,
      HasDerivAt (fun t => φ (Function.update x b t)) (φ' x) (x b) := by
    intro x hx
    have hx' := mem_posOrthant.mp hx
    set R : ℂ := ∏ i ∈ Finset.univ.erase b, (x i : ℂ) ^ (ν i - 1)
    have hxb : (x b : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr (hx' b)
    have hxb0 : (x b : ℂ) ≠ 0 := slitPlane_ne_zero hxb
    have hP := ((hasDerivAt_id (x b : ℂ)).cpow_const (c := ν b - 1) hxb).comp_ofReal
    have hI := (hasDerivAt_id (x b)).ofReal_comp
    have hF := hasDerivAt_faceDeriv A d (G_pos hx) b
    have := ((hI.fun_mul hP).mul_const R).fun_mul hF
    have hfun : (fun t => φ (Function.update x b t)) = fun t : ℝ =>
        ((t : ℂ) * (t : ℂ) ^ (ν b - 1)) * R * faceDeriv A d (Function.update x b t) := by
      funext t
      simp only [φ, wt9_update, Function.update_self, R]
      ring
    have hpow : (x b : ℂ) ^ (ν b - 1) = (x b : ℂ) ^ (ν b - 1 - 1) * x b := by
      have h := cpow_add (x := (x b : ℂ)) (ν b - 1 - 1) 1 hxb0
      rw [cpow_one, sub_add_cancel] at h
      exact h
    have hw : wt9 ν x = (x b : ℂ) ^ (ν b - 1) * R := by
      rw [← wt9_update, Function.update_eq_self]
    rw [hfun]
    convert this using 1
    · rfl
    · simp only [φ', hw, id, ofReal_one, Function.update_eq_self]
      rw [hpow]
      ring
  have hφ' : IntegrableOn φ' (posOrthant 9) := (h1.const_mul (ν b)).add h2
  have hφ : IntegrableOn (fun x => (x b)⁻¹ • φ x) (posOrthant 9) := by
    refine h1.congr_fun (fun x hx => ?_) (measurableSet_posOrthant 9)
    have hxb0 : (x b : ℂ) ≠ 0 := ofReal_ne_zero.mpr (mem_posOrthant.mp hx b).ne'
    simp only [φ, Complex.real_smul, ofReal_inv]
    field_simp
  have h0 := integral_posOrthant_eq_zero_of_hasDerivAt b hd hφ' hφ
  simp only [φ'] at h0
  rw [integral_add (h1.const_mul _) h2, integral_const_mul] at h0
  linear_combination h0

/-- **One normalized Mellin step**: under the hypotheses of `mellin_step`,
`(1/Γ(ν_b)) ∫ x^{ν-1} ∂^A G^{-d/2} = -(1/Γ(ν_b + 1)) ∫ x_b x^{ν-1} ∂_b ∂^A G^{-d/2}`. -/
theorem mellin_step_norm (A : List ZPoly) (d : ℂ) (ν : Fin 9 → ℂ) (b : Fin 9)
    (h1 : IntegrableOn (fun x => wt9 ν x * faceDeriv A d x) (posOrthant 9))
    (h2 : IntegrableOn (fun x => (x b : ℂ) * wt9 ν x * faceDeriv (derivStep b A) d x)
      (posOrthant 9)) :
    (Gamma (ν b))⁻¹ * ∫ x in posOrthant 9, wt9 ν x * faceDeriv A d x =
      -((Gamma (ν b + 1))⁻¹ *
        ∫ x in posOrthant 9, (x b : ℂ) * wt9 ν x * faceDeriv (derivStep b A) d x) := by
  rw [← TwoLoopSESector.mul_inv_Gamma_add_one, mul_comm (ν b), mul_assoc,
    mellin_step A d ν b h1 h2]
  ring

end QED.DimReg.ThreeLoop
