/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopLine

/-!
# Lee–Pomeransky families along lines: the normalized integral and its value

The `Fin N` version of `QED.DimReg.TwoLoopSEVal`, for a `QED.DimReg.LineCont.LineFamily`, in the
Euclidean normalization (no sign): the Feynman integral is
`Γ(d/2) / (Γ(Lp·d/2 - |ν|) ∏ₐ Γ(νₐ)) · J(ν, d)` with `J(ν, d) = ∫ x^{ν-1} G^{-d/2}`.

* `normF`, `Iline = normF · Jline`, `val n d₀ = lim_{λ → 0} Iline n d₀ λ`;
* `continuousAt_Iline_pos`: at positive labels and `d₀ ∉ ℚ`, `Iline` is continuous at `0`;
* `eventually_annihilator`: an annihilator relation of `G` along the line, for `re λ` large.
-/

@[expose] public section

open Complex Filter Topology Set QED.DimReg QED.DimReg.Sector
open QED.DimReg.TwoLoopSESector (atRe halfPlane zero_mem_halfPlane poch Irr
  analyticAt_inv_Gamma_comp eventually_list)

namespace QED.DimReg.LineCont

variable {N : ℕ}

namespace LineFamily

variable (F : LineFamily N)

/-! ### The normalization -/

/-- `Γ(d/2) / (Γ(Lp·d/2 - |ν|) ∏ₐ Γ(νₐ))` along the line. -/
noncomputable def normF (m : Fin N → ℤ) (d₀ l : ℂ) : ℂ :=
  Gamma (lineD F.h d₀ l / 2) * (Gamma (F.Lp * lineD F.h d₀ l / 2 - ∑ j, lineNu F.w m l j))⁻¹ *
    ∏ j, (Gamma (lineNu F.w m l j))⁻¹

/-- **The normalized integral along the line** through the label `m`. -/
noncomputable def Iline (m : Fin N → ℤ) (d₀ : ℂ) (l : ℂ) : ℂ := F.normF m d₀ l * F.Jline m d₀ l

/-- **The integral at the integer label `m`**: the limit at `λ = 0` of the normalized continued
integral along the line `λ ↦ (m + λ, d + 2hλ)`. -/
noncomputable def val (m : Fin N → ℤ) (d : ℂ) : ℂ := limUnder (𝓝[≠] 0) (F.Iline m d)

theorem meromorphicOn_normF (m : Fin N → ℤ) (d₀ : ℂ) :
    MeromorphicOn (F.normF m d₀) univ := fun z _ => by
  have hG : MeromorphicAt (fun l => Gamma (lineD F.h d₀ l / 2)) z :=
    (Meromorphic.Gamma _).comp_analyticAt (by unfold lineD; fun_prop)
  have h3 : AnalyticAt ℂ (fun l => (Gamma (F.Lp * lineD F.h d₀ l / 2 -
      ∑ j, lineNu F.w m l j))⁻¹) z :=
    analyticAt_inv_Gamma_comp (by unfold lineD lineNu; fun_prop)
  have hP : AnalyticAt ℂ (fun l => ∏ j, (Gamma (lineNu F.w m l j))⁻¹) z :=
    Finset.analyticAt_fun_prod _ fun j _ => analyticAt_inv_Gamma_comp (by unfold lineNu; fun_prop)
  exact (hG.mul h3.meromorphicAt).mul hP.meromorphicAt

theorem meromorphicOn_Iline (m : Fin N → ℤ) (d₀ : ℂ) :
    MeromorphicOn (F.Iline m d₀) halfPlane :=
  fun z hz => (F.meromorphicOn_normF m d₀ z (mem_univ z)).mul (F.meromorphicOn_Jline m d₀ z hz)

/-! ### Continuity at positive labels -/

theorem eval_lineNu_zero (f : AffForm) (m : Fin N → ℤ) (d₀ : ℂ) :
    f.eval (lineNu F.w m 0) (lineD F.h d₀ 0) =
      ((f.1 + ∑ i : Fin N, f.2.1.getD i 0 * m i : ℤ) : ℂ) + f.2.2 * (d₀ / 2) := by
  simp only [AffForm.eval, lineNu, lineD, add_zero, mul_zero]
  push_cast
  ring

theorem leafS_ne_neg {m : Fin N → ℤ} (hm : ∀ j, 1 ≤ m j) {d₀ : ℂ} (hd : Irr d₀)
    {T : Finset (Fin N)} {ps : List (Fin N × Fin N)} (hps : ps ∈ (F.S.tree T).paths)
    (k : Fin N) (j : ℕ) : F.S.leafS T ps (lineNu F.w m) (lineD F.h d₀) 0 k + j ≠ 0 := by
  have hdf := F.dfree hps k
  rw [leafS_eq]
  generalize leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k = f at hdf ⊢
  rw [eval_lineNu_zero]
  set A : ℤ := f.1 + ∑ i : Fin N, f.2.1.getD i 0 * m i
  intro h
  rcases eq_or_ne f.2.2 0 with h0 | h0
  · obtain ⟨hnn, h1⟩ := hdf h0
    have hA : 1 ≤ A := by
      have : ∑ i : Fin N, f.2.1.getD i 0 ≤ ∑ i : Fin N, f.2.1.getD i 0 * m i :=
        Finset.sum_le_sum fun i _ => le_mul_of_one_le_right (hnn i) (hm i)
      simp only [A]; omega
    rw [h0, Int.cast_zero, zero_mul, add_zero] at h
    have : ((A + j : ℤ) : ℂ) = 0 := by push_cast; exact h
    have : A + j = 0 := by exact_mod_cast this
    omega
  · apply hd (-2 * (A + j) / f.2.2)
    have hc : (f.2.2 : ℂ) ≠ 0 := by exact_mod_cast h0
    push_cast
    field_simp
    linear_combination 2 * h

theorem continuousAt_Jline_pos {m : Fin N → ℤ} (hm : ∀ j, 1 ≤ m j) {d₀ : ℂ} (hd : Irr d₀) :
    ContinuousAt (F.Jline m d₀) 0 :=
  (F.S.analyticAt_lpCont _ (differentiable_lineNu F.w m) (differentiable_lineD F.h d₀)
    (F.reGt_Kof m d₀ zero_mem_halfPlane)
    fun _ _ hps k j => F.leafS_ne_neg hm hd hps k j).continuousAt

theorem continuousAt_normF {m : Fin N → ℤ} {d₀ : ℂ} (hd : Irr d₀) :
    ContinuousAt (F.normF m d₀) 0 := by
  have hG : ContinuousAt (fun l => Gamma (lineD F.h d₀ l / 2)) 0 := by
    refine ((differentiableAt_Gamma _ fun k hk => hd (-2 * k) ?_).continuousAt).comp
      (f := fun l => lineD F.h d₀ l / 2) (by unfold lineD; fun_prop)
    simp only [lineD, mul_zero, add_zero] at hk
    push_cast
    linear_combination 2 * hk
  have h3 : ContinuousAt (fun l => (Gamma (F.Lp * lineD F.h d₀ l / 2 -
      ∑ j, lineNu F.w m l j))⁻¹) 0 :=
    (analyticAt_inv_Gamma_comp (by unfold lineD lineNu; fun_prop)).continuousAt
  have hP : ContinuousAt (fun l => ∏ j, (Gamma (lineNu F.w m l j))⁻¹) 0 :=
    (Finset.analyticAt_fun_prod _ fun j _ =>
      analyticAt_inv_Gamma_comp (by unfold lineNu; fun_prop)).continuousAt
  exact (hG.mul h3).mul hP

/-- **At positive labels the normalized integral is continuous at `λ = 0`.** -/
theorem continuousAt_Iline_pos {m : Fin N → ℤ} (hm : ∀ j, 1 ≤ m j) {d₀ : ℂ} (hd : Irr d₀) :
    ContinuousAt (F.Iline m d₀) 0 :=
  (F.continuousAt_normF hd).mul (F.continuousAt_Jline_pos hm hd)

/-! ### Annihilator relations along the line -/

/-- The label shift `α - e_b`. -/
def lowZ (α : Fin N → ℕ) (b : Fin N) : Fin N → ℤ := fun j => α j - if j = b then 1 else 0

/-- The label shift `α`. -/
def natZ (α : Fin N → ℕ) : Fin N → ℤ := fun j => α j

theorem lowerAt_natShift_lineNu (w : Fin N → ℕ) (n : Fin N → ℤ) (α : Fin N → ℕ) (b : Fin N)
    (l : ℂ) : lowerAt (natShift (lineNu w n l) α) b = lineNu w (n + lowZ α b) l := by
  funext j
  simp only [lowerAt, natShift, lineNu, lowZ, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

theorem natShift_lineNu (w : Fin N → ℕ) (n : Fin N → ℤ) (α : Fin N → ℕ) (l : ℂ) :
    natShift (lineNu w n l) α = lineNu w (n + natZ α) l := by
  funext j
  simp only [natShift, lineNu, natZ, Pi.add_apply]
  push_cast
  ring

theorem lineD_add_two (h : ℕ) (d₀ l : ℂ) : lineD h d₀ l + 2 = lineD h (d₀ + 2) l := by
  simp only [lineD]; ring

/-- The relation of `QED.DimReg.lpIntegral_annihilator` for the family, along the line, in terms
of the continued integrals `Jline`, for `re λ` large. -/
theorem eventually_annihilator (p : Fin N → MonoList N) (q r : MonoList N)
    (e : Fin N → MonoList N)
    (hsyz : ∀ x, ∑ b, polyEval (p b) x * F.G' b x = polyEval q x * F.S.G.eval x + polyEval r x)
    (he : ∀ b x, polyEval (p b) x * F.G' b x = polyEval (e b) x) (n : Fin N → ℤ) (d₀ : ℂ) :
    ∀ᶠ l in atRe, ∑ b, ((p b).map fun t => (t.1 : ℂ) * (lineNu F.w n l b + t.2 b - 1) *
        F.Jline (n + lowZ t.2 b) d₀ l).sum -
      lineD F.h d₀ l / 2 * ((q.map fun t => (t.1 : ℂ) * F.Jline (n + natZ t.2) d₀ l).sum +
        (r.map fun t => (t.1 : ℂ) * F.Jline (n + natZ t.2) (d₀ + 2) l).sum) = 0 := by
  have hp := eventually_all.2 fun b => eventually_list (p b) fun t =>
    F.eventually_Jline_eq (n + lowZ t.2 b) d₀
  have hq := eventually_list q fun t => F.eventually_Jline_eq (n + natZ t.2) d₀
  have hr := eventually_list r fun t => F.eventually_Jline_eq (n + natZ t.2) (d₀ + 2)
  have hev := eventually_all.2 fun b => eventually_list (e b) fun t =>
    F.eventually_Jline_eq (n + natZ t.2) (d₀ + 2)
  filter_upwards [hp, hq, hr, hev] with l hp hq hr hev
  have h := lpIntegral_annihilator (G := fun x => F.S.G.eval x) (G' := F.G')
    (fun x hx => F.pos x hx) (fun b x hx => F.deriv b x hx) p q r e
    (fun x _ => hsyz x) (fun b x _ => he b x) (lineNu F.w n l) (lineD F.h d₀ l)
    (fun b t ht => by rw [lowerAt_natShift_lineNu]; exact (hp b t ht).1)
    (fun t ht => by rw [natShift_lineNu]; exact (hq t ht).1)
    (fun t ht => by rw [natShift_lineNu, lineD_add_two]; exact (hr t ht).1)
    (fun b t ht => by rw [natShift_lineNu, lineD_add_two]; exact (hev b t ht).1)
  rw [← h]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [lowerAt_natShift_lineNu, (hp b t ht).2]
  · congr 2
    · exact congrArg List.sum (List.map_congr_left fun t ht => by
        rw [natShift_lineNu, (hq t ht).2])
    · exact congrArg List.sum (List.map_congr_left fun t ht => by
        rw [natShift_lineNu, lineD_add_two, (hr t ht).2])

end LineFamily

end QED.DimReg.LineCont
