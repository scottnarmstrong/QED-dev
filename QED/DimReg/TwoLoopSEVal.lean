/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopSELine
public import QED.DimReg.TwoLoopSEPoly
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.Meromorphic.Complex

/-!
# The two-loop self-energy integrals at integer labels

**Normalization.** The Feynman integral of the Minkowski family
`QED.Algebra.IBPCert.Pilot.twoLoopSE` is, by the Lee–Pomeransky formula and the Wick-rotation
sign, `(-1)^{|ν|} Γ(d/2) / (Γ(3d/2 - |ν|) ∏ₐ Γ(νₐ)) · J(ν, d)` with
`J(ν, d) = ∫ x^{ν-1} G^{-d/2}`. Along the line `λ ↦ (n + λ, d₀ + 4λ)` this is
`Iline n d₀ = normF n d₀ · Jline n d₀`, a meromorphic function on `re λ > -1`
(`meromorphicOn_Iline`), and the **value at the integer label** `n` is its limit at `λ = 0`
(`QED.DimReg.TwoLoopSESector.val`).

**Relations along the line.** An annihilator relation (`QED.DimReg.lpIntegral_annihilator`)
holds for `re λ` large, where every integral converges (`eventually_annihilator`); multiplied by
the normalization it becomes a relation among the `Iline` with polynomial coefficients
(`eventually_normalized`, via `normF_dimShift`), and the identity theorem carries it to a
punctured neighbourhood of `λ = 0` (`QED.DimReg.TwoLoopSESector.eventuallyEq_nhdsNE_of_atRe`).

**Finiteness (item 4).** At positive labels and `d₀ ∉ ℚ` no leaf exponent is a pole, so `Iline`
is continuous at `0` (`continuousAt_Iline_pos`). At other labels the raising relation
`νᵢ J(ν, d) = (d/2) Σ c_γ(xᵢ ∂ᵢ G) J(ν + γ, d + 2)` expresses `Iline n d₀` through labels with
`nᵢ` raised at `d₀ + 2`, with coefficients that stay polynomial after dividing by `νᵢ`; induction
on the deficiency `Σⱼ (1 - nⱼ)⁺` gives the limit at every label (`tendsto_Iline`). Pole counting
alone fails at 28 of the certificate's labels, so the induction is needed.
-/

@[expose] public section

open Complex Filter Topology Set QED.DimReg QED.DimReg.Sector

namespace QED.DimReg.TwoLoopSESector

/-! ### `Γ⁻¹` and Pochhammer symbols -/

theorem mul_inv_Gamma_add_one (s : ℂ) : s * (Gamma (s + 1))⁻¹ = (Gamma s)⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Gamma_zero]
  · rw [Gamma_add_one s hs, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- The rising factorial `s (s + 1) ⋯ (s + k - 1)`. -/
noncomputable def poch (s : ℂ) (k : ℕ) : ℂ := ∏ j ∈ Finset.range k, (s + j)

theorem inv_Gamma_eq_poch (s : ℂ) (k : ℕ) : (Gamma s)⁻¹ = poch s k * (Gamma (s + k))⁻¹ := by
  induction k with
  | zero => simp [poch]
  | succ k ih =>
    rw [ih, ← mul_inv_Gamma_add_one (s + k), show s + ((k + 1 : ℕ) : ℂ) = s + k + 1 by
      push_cast; ring]
    simp only [poch, Finset.prod_range_succ]
    ring

theorem poch_succ (s : ℂ) (k : ℕ) : poch s (k + 1) = s * poch (s + 1) k := by
  simp only [poch, Finset.prod_range_succ', Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun _ _ => by ring

theorem analyticAt_poch {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (k : ℕ) :
    AnalyticAt ℂ (fun l => poch (f l) k) z :=
  Finset.analyticAt_fun_prod _ fun _ _ => hf.add analyticAt_const

/-! ### The normalization -/

/-- `(-1)^{|ν|} Γ(d/2) / (Γ(3d/2 - |ν|) ∏ₐ Γ(νₐ))` along the line. -/
noncomputable def normF (m : Fin 5 → ℤ) (d₀ l : ℂ) : ℂ :=
  (-1 : ℂ) ^ (∑ j, m j) * Gamma (lineD d₀ l / 2) *
    (Gamma (3 * lineD d₀ l / 2 - ∑ j, lineNu m l j))⁻¹ * ∏ j, (Gamma (lineNu m l j))⁻¹

/-- **The normalized integral along the line** through the label `m`. -/
noncomputable def Iline (m : Fin 5 → ℤ) (d₀ : ℂ) (l : ℂ) : ℂ := normF m d₀ l * Jline m d₀ l

/-- **The two-loop self-energy integral at the integer label `m`**: the limit at `λ = 0` of the
normalized continued integral along the line `λ ↦ (m + λ, d + 4λ)`. -/
noncomputable def val (m : Fin 5 → ℤ) (d : ℂ) : ℂ := limUnder (𝓝[≠] 0) (Iline m d)

theorem analyticAt_inv_Gamma_comp {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (fun l => (Gamma (f l))⁻¹) z :=
  (differentiable_one_div_Gamma.analyticAt _).comp hf

theorem meromorphicOn_normF (m : Fin 5 → ℤ) (d₀ : ℂ) :
    MeromorphicOn (normF m d₀) univ := fun z _ => by
  have hG : MeromorphicAt (fun l => Gamma (lineD d₀ l / 2)) z :=
    (Meromorphic.Gamma _).comp_analyticAt (by unfold lineD; fun_prop)
  have h3 : AnalyticAt ℂ (fun l => (Gamma (3 * lineD d₀ l / 2 - ∑ j, lineNu m l j))⁻¹) z :=
    analyticAt_inv_Gamma_comp (by unfold lineD lineNu; fun_prop)
  have hP : AnalyticAt ℂ (fun l => ∏ j, (Gamma (lineNu m l j))⁻¹) z :=
    Finset.analyticAt_fun_prod _ fun j _ => analyticAt_inv_Gamma_comp (by unfold lineNu; fun_prop)
  exact ((analyticAt_const.meromorphicAt.mul hG).mul h3.meromorphicAt).mul hP.meromorphicAt

theorem meromorphicOn_Iline (m : Fin 5 → ℤ) (d₀ : ℂ) : MeromorphicOn (Iline m d₀) halfPlane :=
  fun z hz => (meromorphicOn_normF m d₀ z (mem_univ z)).mul (meromorphicOn_Jline m d₀ z hz)

/-! ### Continuity at positive labels -/

/-- `d` is not rational. -/
def Irr (d : ℂ) : Prop := ∀ q : ℚ, d ≠ q

theorem Irr.add_two {d : ℂ} (hd : Irr d) : Irr (d + 2) := fun q h =>
  hd (q - 2) (by push_cast; rw [← h]; ring)

theorem eval_lineNu_zero (f : Sector.AffForm) (m : Fin 5 → ℤ) (d₀ : ℂ) :
    f.eval (lineNu m 0) (lineD d₀ 0) =
      ((f.1 + ∑ i : Fin 5, f.2.1.getD i 0 * m i : ℤ) : ℂ) + f.2.2 * (d₀ / 2) := by
  simp only [Sector.AffForm.eval, lineNu, lineD, add_zero, mul_zero]
  push_cast
  ring

theorem leafS_ne_neg {m : Fin 5 → ℤ} (hm : ∀ j, 1 ≤ m j) {d₀ : ℂ} (hd : Irr d₀)
    {T : Finset (Fin 5)} {ps : List (Fin 5 × Fin 5)} (hps : ps ∈ (sectorData.tree T).paths)
    (k : Fin 5) (j : ℕ) : sectorData.leafS T ps (lineNu m) (lineD d₀) 0 k + j ≠ 0 := by
  have hf := mem_allForms hps k
  rw [leafS_eq]
  generalize leafForm degD (flagsOf T) ps (minOfFlags (flagsOf T) ps) k = f at hf ⊢
  rw [eval_lineNu_zero]
  set A : ℤ := f.1 + ∑ i : Fin 5, f.2.1.getD i 0 * m i
  intro h
  rcases eq_or_ne f.2.2 0 with h0 | h0
  · obtain ⟨hnn, h1⟩ := dfree_allForms f hf h0
    rw [Sector.sum_map_finRange] at h1
    have hA : 1 ≤ A := by
      have : ∑ i : Fin 5, f.2.1.getD i 0 ≤ ∑ i : Fin 5, f.2.1.getD i 0 * m i :=
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

theorem continuousAt_Jline_pos {m : Fin 5 → ℤ} (hm : ∀ j, 1 ≤ m j) {d₀ : ℂ} (hd : Irr d₀) :
    ContinuousAt (Jline m d₀) 0 :=
  (sectorData.analyticAt_lpCont _ (differentiable_lineNu m) (differentiable_lineD d₀)
    (reGt_Kof m d₀ zero_mem_halfPlane)
    fun _ _ hps k j => leafS_ne_neg hm hd hps k j).continuousAt

theorem continuousAt_normF {m : Fin 5 → ℤ} {d₀ : ℂ} (hd : Irr d₀) :
    ContinuousAt (normF m d₀) 0 := by
  have hG : ContinuousAt (fun l => Gamma (lineD d₀ l / 2)) 0 := by
    refine ((differentiableAt_Gamma _ fun k hk => hd (-2 * k) ?_).continuousAt).comp
      (f := fun l => lineD d₀ l / 2) (by unfold lineD; fun_prop)
    simp only [lineD, mul_zero, add_zero] at hk
    push_cast
    linear_combination 2 * hk
  have h3 : ContinuousAt (fun l => (Gamma (3 * lineD d₀ l / 2 - ∑ j, lineNu m l j))⁻¹) 0 :=
    (analyticAt_inv_Gamma_comp (by unfold lineD lineNu; fun_prop)).continuousAt
  have hP : ContinuousAt (fun l => ∏ j, (Gamma (lineNu m l j))⁻¹) 0 :=
    (Finset.analyticAt_fun_prod _ fun j _ =>
      analyticAt_inv_Gamma_comp (by unfold lineNu; fun_prop)).continuousAt
  exact ((continuousAt_const.mul hG).mul h3).mul hP

/-- **At positive labels the normalized integral is continuous at `λ = 0`.** -/
theorem continuousAt_Iline_pos {m : Fin 5 → ℤ} (hm : ∀ j, 1 ≤ m j) {d₀ : ℂ} (hd : Irr d₀) :
    ContinuousAt (Iline m d₀) 0 :=
  (continuousAt_normF hd).mul (continuousAt_Jline_pos hm hd)

/-! ### Annihilator relations along the line -/

/-- The label shift `α - e_b`. -/
def lowZ (α : Fin 5 → ℕ) (b : Fin 5) : Fin 5 → ℤ := fun j => α j - if j = b then 1 else 0

/-- The label shift `α`. -/
def natZ (α : Fin 5 → ℕ) : Fin 5 → ℤ := fun j => α j

theorem lowerAt_natShift_lineNu (n : Fin 5 → ℤ) (α : Fin 5 → ℕ) (b : Fin 5) (l : ℂ) :
    lowerAt (natShift (lineNu n l) α) b = lineNu (n + lowZ α b) l := by
  funext j
  simp only [lowerAt, natShift, lineNu, lowZ, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

theorem natShift_lineNu (n : Fin 5 → ℤ) (α : Fin 5 → ℕ) (l : ℂ) :
    natShift (lineNu n l) α = lineNu (n + natZ α) l := by
  funext j
  simp only [natShift, lineNu, natZ, Pi.add_apply]
  push_cast
  ring

theorem lineD_add_two (d₀ l : ℂ) : lineD d₀ l + 2 = lineD (d₀ + 2) l := by
  simp only [lineD]; ring

theorem eventually_list {β : Type*} (L : List β) {P : β → ℂ → Prop}
    (h : ∀ t, ∀ᶠ l in atRe, P t l) : ∀ᶠ l in atRe, ∀ t ∈ L, P t l :=
  (eventually_all_finite L.finite_toSet).2 fun t _ => h t

/-- The relation of `QED.DimReg.lpIntegral_annihilator` for the family, along the line, in terms
of the continued integrals `Jline`, for `re λ` large. -/
theorem eventually_annihilator (p : Fin 5 → MonoList 5) (q r : MonoList 5)
    (e : Fin 5 → MonoList 5)
    (hsyz : ∀ x, ∑ b, polyEval (p b) x * gD b x = polyEval q x * Gx x + polyEval r x)
    (he : ∀ b x, polyEval (p b) x * gD b x = polyEval (e b) x) (n : Fin 5 → ℤ) (d₀ : ℂ) :
    ∀ᶠ l in atRe, ∑ b, ((p b).map fun t => (t.1 : ℂ) * (lineNu n l b + t.2 b - 1) *
        Jline (n + lowZ t.2 b) d₀ l).sum -
      lineD d₀ l / 2 * ((q.map fun t => (t.1 : ℂ) * Jline (n + natZ t.2) d₀ l).sum +
        (r.map fun t => (t.1 : ℂ) * Jline (n + natZ t.2) (d₀ + 2) l).sum) = 0 := by
  have hp := eventually_all.2 fun b => eventually_list (p b) fun t =>
    eventually_Jline_eq (n + lowZ t.2 b) d₀
  have hq := eventually_list q fun t => eventually_Jline_eq (n + natZ t.2) d₀
  have hr := eventually_list r fun t => eventually_Jline_eq (n + natZ t.2) (d₀ + 2)
  have hev := eventually_all.2 fun b => eventually_list (e b) fun t =>
    eventually_Jline_eq (n + natZ t.2) (d₀ + 2)
  filter_upwards [hp, hq, hr, hev] with l hp hq hr hev
  have h := lpIntegral_annihilator (G := fun x => sectorData.G.eval x) (G' := gD)
    (fun x hx => G_pos hx) (fun b x _ => hasDerivAt_G b x) p q r e
    (fun x _ => by simp only [eval_G]; exact hsyz x) (fun b x _ => he b x) (lineNu n l)
    (lineD d₀ l)
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

end QED.DimReg.TwoLoopSESector
