/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceFTC

/-!
# The face theorem: `Iline3` is the nine-variable integral continued in `(ν₇, ν₈)`

Let `n` be a label with `n₇ = -k₇ ≤ 0`, `n₈ = -k₈ ≤ 0`, and take the line
`λ ↦ (ν', d) = (n' + λw₇, d₀ + 6λ)` of `QED.DimReg.ThreeLoop.F7`. For `(s₇, s₈)` with
`re s₇, re s₈ > 0` the nine-variable Lee–Pomeransky integral at `(ν', s₇, s₈)` converges near the
face (`QED.DimReg.ThreeLoop.eventually_integrableOn_faceDeriv`), and `k_b + 1` partial
integrations in `x₇`, then in `x₈` (`mellin_iter`) give

  `(1/Γ(s₇)Γ(s₈)) ∫ x^{ν-1} G^{-d/2} = cont9 n d₀ λ s₇ s₈`,

where `cont9` is `(-1)^K / (Γ(s₇+k₇+1) Γ(s₈+k₈+1))` times
`∫ x'^{ν'-1} x₇^{s₇+k₇} x₈^{s₈+k₈} ∂₇^{k₇+1} ∂₈^{k₈+1} G^{-d/2}`
(`eventually_lpIntegral_eq_cont9`). The integral in `cont9` converges for bounded
`re s_b > -k_b - 1` (`eventually_integrableOn_faceDeriv`), so `cont9` is the continuation of
the normalized integral in `(ν₇, ν₈)` (its holomorphy in `(s₇, s₈)` is not proved here).
At `(s₇, s₈) = (-k₇, -k₈)` the weights in `x₇, x₈` are `1`, and integrating `∂₈`, then (after
commuting, `faceDeriv_iterate_comm`) `∂₇`, to the boundary (`integral_posOrthant_deriv_last`)
gives the face integral; with `QED.DimReg.ThreeLoop.eventually_Iline3_eq`:

* **`eventually_norm9_mul_cont9`**: `norm9 n d₀ λ · cont9 n d₀ λ (-k₇) (-k₈) = Iline3 n d₀ λ` for
  `re λ` large, where `norm9 n d₀ λ` is the Γ-prefactor of the nine-variable integral without
  `1/(Γ(ν₇)Γ(ν₈))`, at `(ν₇, ν₈) = (-k₇, -k₈)`.

All statements are exact for `re λ` large (no limit in `λ`).
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory QED.DimReg QED.DimReg.Sector QED.DimReg.LineCont
open QED.DimReg.TwoLoopSESector (atRe eventually_re_gt eventually_list)

namespace QED.DimReg.ThreeLoop

/-! ### Iterated Mellin steps -/

theorem wt9_update_succ (ν : Fin 9 → ℂ) (b : Fin 9) {x : Fin 9 → ℝ} (hx : x ∈ posOrthant 9) :
    (x b : ℂ) * wt9 ν x = wt9 (Function.update ν b (ν b + 1)) x := by
  have hx0 : (x b : ℂ) ≠ 0 := ofReal_ne_zero.mpr (mem_posOrthant.mp hx b).ne'
  unfold wt9
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b),
    ← Finset.mul_prod_erase Finset.univ (fun i => (x i : ℂ) ^ (Function.update ν b (ν b + 1) i - 1))
      (Finset.mem_univ b)]
  have hrest : ∏ i ∈ Finset.univ.erase b, (x i : ℂ) ^ (Function.update ν b (ν b + 1) i - 1) =
      ∏ i ∈ Finset.univ.erase b, (x i : ℂ) ^ (ν i - 1) :=
    Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hrest, Function.update_self, show ν b + 1 - 1 = (ν b - 1) + 1 by ring,
    cpow_add _ _ hx0, cpow_one]
  ring

theorem update_update_add (ν : Fin 9 → ℂ) (b : Fin 9) (m : ℕ) :
    Function.update (Function.update ν b (ν b + m)) b
      (Function.update ν b (ν b + m) b + 1) = Function.update ν b (ν b + ((m + 1 : ℕ) : ℂ)) := by
  rw [Function.update_idem, Function.update_self]
  push_cast; ring_nf

/-- **`m` Mellin steps in the coordinate `x_b`**, given the integrability of all intermediate
integrands: `(1/Γ(ν_b)) ∫ x^{ν-1} ∂^A G^{-d/2} =
(-1)^m (1/Γ(ν_b + m)) ∫ x^{ν + m e_b - 1} ∂_b^m ∂^A G^{-d/2}`. -/
theorem mellin_iter (b : Fin 9) (A : List ZPoly) (d : ℂ) (ν : Fin 9 → ℂ) :
    ∀ m : ℕ, (∀ i ≤ m, IntegrableOn (fun x => wt9 (Function.update ν b (ν b + i)) x *
        faceDeriv ((derivStep b)^[i] A) d x) (posOrthant 9)) →
      (Gamma (ν b))⁻¹ * ∫ x in posOrthant 9, wt9 ν x * faceDeriv A d x =
        (-1) ^ m * ((Gamma (ν b + m))⁻¹ * ∫ x in posOrthant 9,
          wt9 (Function.update ν b (ν b + m)) x * faceDeriv ((derivStep b)^[m] A) d x)
  | 0, _ => by simp
  | m + 1, h => by
    rw [mellin_iter b A d ν m fun i hi => h i (by omega)]
    set νm := Function.update ν b (ν b + m)
    have hνm : νm b = ν b + m := Function.update_self _ _ _
    have h2 : IntegrableOn (fun x => (x b : ℂ) * wt9 νm x *
        faceDeriv (derivStep b ((derivStep b)^[m] A)) d x) (posOrthant 9) := by
      refine (h (m + 1) le_rfl).congr_fun (fun x hx => ?_) (measurableSet_posOrthant 9)
      rw [wt9_update_succ νm b hx, update_update_add, Function.iterate_succ_apply']
    have hs := mellin_step_norm ((derivStep b)^[m] A) d νm b (h m (by omega)) h2
    rw [hνm] at hs
    rw [hs, pow_succ]
    have hI : ∫ x in posOrthant 9, (x b : ℂ) * wt9 νm x *
        faceDeriv (derivStep b ((derivStep b)^[m] A)) d x =
        ∫ x in posOrthant 9, wt9 (Function.update ν b (ν b + ((m + 1 : ℕ) : ℂ))) x *
          faceDeriv ((derivStep b)^[m + 1] A) d x :=
      setIntegral_congr_fun (measurableSet_posOrthant 9) fun x hx => by
        rw [wt9_update_succ νm b hx, update_update_add, Function.iterate_succ_apply']
    rw [hI, show ν b + (m : ℂ) + 1 = ν b + ((m + 1 : ℕ) : ℂ) by push_cast; ring]
    ring

/-! ### Points and weights near the face -/

@[simp] theorem snoc_nine_eight {α : Type*} (w : Fin 8 → α) (t : α) :
    (Fin.snoc w t : Fin 9 → α) 8 = t := Fin.snoc_last (α := fun _ => α) _ _

@[simp] theorem snoc_nine_seven {α : Type*} (w : Fin 8 → α) (t : α) :
    (Fin.snoc w t : Fin 9 → α) 7 = w 7 := Fin.snoc_castSucc (α := fun _ => α) (i := 7) _ _

@[simp] theorem snoc_eight_seven {α : Type*} (v : Fin 7 → α) (t : α) :
    (Fin.snoc v t : Fin 8 → α) 7 = t := Fin.snoc_last (α := fun _ => α) _ _

theorem update_nu9_seven (ν : Fin 7 → ℂ) (a c a' : ℂ) :
    Function.update (nu9 ν a c) 7 a' = nu9 ν a' c := by
  unfold nu9
  rw [show (7 : Fin 9) = Fin.castSucc (Fin.last 7) from rfl, ← Fin.snoc_update,
    Fin.update_snoc_last]

theorem update_nu9_eight (ν : Fin 7 → ℂ) (a c c' : ℂ) :
    Function.update (nu9 ν a c) 8 c' = nu9 ν a c' :=
  Fin.update_snoc_last _ _ _

theorem res7_snoc {w : Fin 8 → ℝ} {t : ℝ} : res7 (Fin.snoc w t) = Fin.init w := by
  simp [res7, Fin.init_snoc]

theorem update_snoc_snoc (v : Fin 7 → ℝ) (t s : ℝ) :
    Function.update (Fin.snoc (Fin.snoc v t) 0 : Fin 9 → ℝ) 7 s = Fin.snoc (Fin.snoc v s) 0 := by
  rw [show (7 : Fin 9) = Fin.castSucc (Fin.last 7) from rfl, ← Fin.snoc_update,
    Fin.update_snoc_last]

theorem snoc_snoc_zero (v : Fin 7 → ℝ) : (Fin.snoc (Fin.snoc v 0) 0 : Fin 9 → ℝ) = ext7 v := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [ext7]
  | cast j =>
    induction j using Fin.lastCases with
    | last => simp [ext7]
    | cast k => simp [ext7]

/-- The weight at `ν₇ = ν₈ = 1` does not see `x₇, x₈`. -/
theorem wt9_nu9_one (ν : Fin 7 → ℂ) (x : Fin 9 → ℝ) :
    wt9 (nu9 ν 1 1) x = ∏ b, ((res7 x b : ℝ) : ℂ) ^ (ν b - 1) := by
  rw [wt9, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp [nu9, res7, Fin.init]

theorem G_pos_snoc {w : Fin 8 → ℝ} (hw : w ∈ posOrthant 8) {t : ℝ} (ht : 0 ≤ t) :
    0 < lpPoly.eval (Fin.snoc w t) := by
  have hnn : ∀ k, 0 ≤ (Fin.snoc w t : Fin 9 → ℝ) k := by
    intro k
    induction k using Fin.lastCases with
    | last => simpa using ht
    | cast j => simpa using (mem_posOrthant.mp hw j).le
  have := g7_le_G hnn
  rw [res7_snoc] at this
  exact (g7_pos (init_mem_posOrthant hw)).trans_le this

theorem snoc_mem_posOrthant' {v : Fin 7 → ℝ} (hv : v ∈ posOrthant 7) {t : ℝ} (ht : 0 ≤ t) :
    ∀ k, 0 ≤ (Fin.snoc (Fin.snoc v t) 0 : Fin 9 → ℝ) k := by
  intro k
  induction k using Fin.lastCases with
  | last => simp
  | cast j =>
    induction j using Fin.lastCases with
    | last => simpa using ht
    | cast i => simpa using (mem_posOrthant.mp hv i).le

/-- The derivative in the last coordinate of `x'^{ν'-1} ∂^A G^{-d/2}` at `ν₇ = ν₈ = 1`. -/
theorem hasDerivAt_last (ν : Fin 7 → ℂ) (A : List ZPoly) (d : ℂ) {w : Fin 8 → ℝ}
    (hw : w ∈ posOrthant 8) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => wt9 (nu9 ν 1 1) (Fin.snoc w s) * faceDeriv A d (Fin.snoc w s))
      (wt9 (nu9 ν 1 1) (Fin.snoc w t) * faceDeriv (derivStep 8 A) d (Fin.snoc w t)) t := by
  have h := hasDerivAt_faceDeriv A d (G_pos_snoc hw ht) 8
  have hu : ∀ s, Function.update (Fin.snoc w t : Fin 9 → ℝ) 8 s = Fin.snoc w s :=
    fun s => Fin.update_snoc_last _ _ _
  simp only [hu] at h
  rw [show (Fin.snoc w t : Fin 9 → ℝ) 8 = t from Fin.snoc_last _ _] at h
  simp only [wt9_nu9_one, res7_snoc]
  exact h.const_mul _

/-! ### The face theorem -/

/-- The derivative polynomials `∂₈^{k₈+1} ∂₇^{k₇+1} G^{-d/2}` of the continuation. -/
def bPolys (k₇ k₈ : ℕ) : List ZPoly := (derivStep 8)^[k₈ + 1] ((derivStep 7)^[k₇ + 1] [[([], 1)]])

/-- **The continuation in `(ν₇, ν₈)`** of the normalized nine-variable integral along the line
through `n` (`K = k₇ + k₈`, `k_b = -n_b`):
`(-1)^K (1/Γ(s₇+k₇+1)Γ(s₈+k₈+1)) ∫ x'^{ν'-1} x₇^{s₇+k₇} x₈^{s₈+k₈} ∂₇^{k₇+1}∂₈^{k₈+1}G^{-d/2}`. -/
noncomputable def cont9 (n : Fin 9 → ℤ) (d₀ l s₇ s₈ : ℂ) : ℂ :=
  (-1) ^ (ord7 n + ord8 n) * ((Gamma (s₇ + ((ord7 n + 1 : ℕ) : ℂ)))⁻¹ *
    (Gamma (s₈ + ((ord8 n + 1 : ℕ) : ℂ)))⁻¹ *
    ∫ x in posOrthant 9, wt9 (nu9 (lineNu w7 (lbl3 n []) l) (s₇ + ((ord7 n + 1 : ℕ) : ℂ))
      (s₈ + ((ord8 n + 1 : ℕ) : ℂ))) x * faceDeriv (bPolys (ord7 n) (ord8 n)) (lineD h7 d₀ l) x)

theorem lpIntegral_eq_wt9 (ν : Fin 9 → ℂ) (d : ℂ) :
    lpIntegral (fun x => lpPoly.eval x) ν d =
      ∫ x in posOrthant 9, wt9 ν x * faceDeriv [[([], 1)]] d x := by
  simp only [lpIntegral, lpIntegrand, faceDeriv_init, wt9]

/-- **The normalized nine-variable integral is `cont9`** for `0 < re s₇, re s₈ ≤ M`, at every
`λ` with `re λ` large. -/
theorem eventually_lpIntegral_eq_cont9 (n : Fin 9 → ℤ) (d₀ : ℂ) (M : ℝ) :
    ∀ᶠ l in atRe, ∀ s₇ s₈ : ℂ, 0 < s₇.re → s₇.re ≤ M → 0 < s₈.re → s₈.re ≤ M →
      (Gamma s₇)⁻¹ * (Gamma s₈)⁻¹ * lpIntegral (fun x => lpPoly.eval x)
        (nu9 (lineNu w7 (lbl3 n []) l) s₇ s₈) (lineD h7 d₀ l) = cont9 n d₀ l s₇ s₈ := by
  set k₇ := ord7 n
  set k₈ := ord8 n
  set B7 := (derivStep 7)^[k₇ + 1] [[([], 1)]]
  set L : List (List ZPoly) := (List.range (k₇ + 2)).map (fun i => (derivStep 7)^[i] [[([], 1)]]) ++
    (List.range (k₈ + 2)).map (fun i => (derivStep 8)^[i] B7)
  filter_upwards [eventually_list L fun A =>
    eventually_integrableOn_faceDeriv (lbl3 n []) d₀ A (M + k₇ + k₈ + 2)]
    with l hl s₇ s₈ h1 h2 h3 h4
  set ν' := lineNu w7 (lbl3 n []) l
  set d := lineD h7 d₀ l
  have hk7 : (0 : ℝ) ≤ k₇ := Nat.cast_nonneg _
  have hk8 : (0 : ℝ) ≤ k₈ := Nat.cast_nonneg _
  -- the steps in `x₇`
  have e7 := mellin_iter 7 [[([], 1)]] d (nu9 ν' s₇ s₈) (k₇ + 1) fun i hi => by
    rw [nu9_seven, update_nu9_seven]
    have hi' : (i : ℝ) ≤ k₇ + 1 := by exact_mod_cast hi
    refine hl _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega),
      rfl⟩)) _ _ ?_ ?_ h3 (by linarith)
    · simp only [add_re, natCast_re]; positivity
    · simp only [add_re, natCast_re]; linarith
  -- the steps in `x₈`
  have e8 := mellin_iter 8 B7 d (nu9 ν' (s₇ + ((k₇ + 1 : ℕ) : ℂ)) s₈) (k₈ + 1) fun i hi => by
    rw [nu9_eight, update_nu9_eight]
    have hi' : (i : ℝ) ≤ k₈ + 1 := by exact_mod_cast hi
    refine hl _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega),
      rfl⟩)) _ _ ?_ ?_ ?_ ?_
    · simp only [add_re, natCast_re]; push_cast; positivity
    · simp only [add_re, natCast_re]; push_cast; linarith
    · simp only [add_re, natCast_re]; positivity
    · simp only [add_re, natCast_re]; linarith
  rw [nu9_seven, update_nu9_seven, show ((7 : Fin 9) : ℕ) = 7 from rfl] at e7
  rw [nu9_eight, update_nu9_eight, show ((8 : Fin 9) : ℕ) = 8 from rfl] at e8
  rw [lpIntegral_eq_wt9, mul_comm (Gamma s₇)⁻¹, mul_assoc, e7, cont9]
  rw [show (Gamma s₈)⁻¹ * ((-1) ^ (k₇ + 1) * ((Gamma (s₇ + ((k₇ + 1 : ℕ) : ℂ)))⁻¹ *
      ∫ x in posOrthant 9, wt9 (nu9 ν' (s₇ + ((k₇ + 1 : ℕ) : ℂ)) s₈) x * faceDeriv B7 d x)) =
      (-1) ^ (k₇ + 1) * (Gamma (s₇ + ((k₇ + 1 : ℕ) : ℂ)))⁻¹ * ((Gamma s₈)⁻¹ *
      ∫ x in posOrthant 9, wt9 (nu9 ν' (s₇ + ((k₇ + 1 : ℕ) : ℂ)) s₈) x * faceDeriv B7 d x) by
    ring, e8, bPolys, pow_succ, pow_succ, pow_add]
  ring

/-- **The face theorem at large exponent.** At `(s₇, s₈) = (-k₇, -k₈)` the continuation times
the nine-variable normalization `norm9` is `Iline3`, for `re λ` large. -/
theorem eventually_norm9_mul_cont9 (n : Fin 9 → ℤ) (d₀ : ℂ) :
    ∀ᶠ l in atRe, norm9 n d₀ l * cont9 n d₀ l (-(ord7 n : ℂ)) (-(ord8 n : ℂ)) = Iline3 n d₀ l := by
  set k₇ := ord7 n
  set k₈ := ord8 n
  set C8 := (derivStep 8)^[k₈] ((derivStep 7)^[k₇ + 1] [[([], 1)]])
  set C := aPolys k₇ k₈
  filter_upwards [eventually_Iline3_eq n d₀, eventually_list [C8, derivStep 8 C8, C,
    derivStep 8 C] fun A => eventually_integrableOn_faceDeriv (lbl3 n []) d₀ A 1] with l hI hl
  set ν' := lineNu w7 (lbl3 n []) l
  set d := lineD h7 d₀ l
  have hint : ∀ A ∈ [C8, derivStep 8 C8, C, derivStep 8 C],
      IntegrableOn (fun x => wt9 (nu9 ν' 1 1) x * faceDeriv A d x) (posOrthant 9) :=
    fun A hA => hl A hA 1 1 (by simp) (by simp) (by simp) (by simp)
  have hone7 : -(k₇ : ℂ) + ((k₇ + 1 : ℕ) : ℂ) = 1 := by push_cast; ring
  have hone8 : -(k₈ : ℂ) + ((k₈ + 1 : ℕ) : ℂ) = 1 := by push_cast; ring
  have hb : bPolys k₇ k₈ = derivStep 8 C8 := by
    rw [bPolys, Function.iterate_succ_apply']
  -- the boundary value in `x₈`
  obtain ⟨int1, eq1⟩ := integral_posOrthant_deriv_last
    (fun w hw t ht => hasDerivAt_last ν' C8 d hw ht) (hint C8 (by simp)) (hint _ (by simp))
  obtain ⟨int2, -⟩ := integral_posOrthant_deriv_last
    (fun w hw t ht => hasDerivAt_last ν' C d hw ht) (hint C (by simp)) (hint _ (by simp))
  -- the boundary value in `x₇`
  have hcomm : faceDeriv C8 d = faceDeriv (derivStep 7 C) d := by
    rw [show C8 = (derivStep 8)^[k₈] (derivStep 7 ((derivStep 7)^[k₇] [[([], 1)]])) by
      rw [← Function.iterate_succ_apply' (derivStep 7)], faceDeriv_iterate_comm]
    rfl
  have hd2 : ∀ v ∈ posOrthant 7, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => wt9 (nu9 ν' 1 1) (Fin.snoc (Fin.snoc v s) 0) *
        faceDeriv C d (Fin.snoc (Fin.snoc v s) 0))
      (wt9 (nu9 ν' 1 1) (Fin.snoc (Fin.snoc v t) 0) *
        faceDeriv C8 d (Fin.snoc (Fin.snoc v t) 0)) t := by
    intro v hv t ht
    have hG : 0 < lpPoly.eval (Fin.snoc (Fin.snoc v t) 0 : Fin 9 → ℝ) := by
      have := g7_le_G (snoc_mem_posOrthant' hv ht)
      simp only [res7_snoc, Fin.init_snoc] at this
      exact (g7_pos hv).trans_le this
    have h := hasDerivAt_faceDeriv C d hG 7
    simp only [update_snoc_snoc] at h
    rw [show (Fin.snoc (Fin.snoc v t) 0 : Fin 9 → ℝ) 7 = t by
      rw [show (7 : Fin 9) = Fin.castSucc (Fin.last 7) from rfl, Fin.snoc_castSucc,
        Fin.snoc_last]] at h
    rw [hcomm]
    simp only [wt9_nu9_one, res7_snoc, Fin.init_snoc]
    exact h.const_mul _
  have eq3 := (integral_posOrthant_deriv_last (n := 7) hd2 int2 int1).2
  -- assemble
  rw [hI, cont9, hone7, hone8, Complex.Gamma_one, inv_one, one_mul, one_mul, hb, eq1, eq3]
  simp only [wt9_nu9_one, res7_snoc, Fin.init_snoc]
  simp only [snoc_snoc_zero, neg_neg]
  ring

end QED.DimReg.ThreeLoop
