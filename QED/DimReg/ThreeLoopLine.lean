/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopSEZero

/-!
# Lee–Pomeransky families along lines, for any number of lines

This is the `Fin N` version of `QED.DimReg.TwoLoopSELine`. A family is given by certified sector
data `S : LPSectorData N` for its Lee–Pomeransky polynomial `G`, the degree `Lp = L + 1` of `F`,
and a direction `h`: the line through an integer label `n` is
`λ ↦ (ν, d) = (n + λw, d₀ + 2hλ)` (`QED.DimReg.LineCont.lineNu`, `QED.DimReg.LineCont.lineD`).
Along it every leaf exponent is affine in `λ` with integer slope (`re_leafS_line`); the family
data require the slope to be `≥ 1` and the `d`-free exponents to be positive at positive labels
(`QED.DimReg.LineCont.formOk`, checked by the kernel on the generated data).

* `QED.DimReg.LineCont.Jline`: the continued integral along the line, meromorphic on
  `re λ > -1` (`meromorphicOn_Jline`);
* `eventually_Jline_eq`: for `re λ` large the integral converges and equals `Jline`.
-/

@[expose] public section

open Complex Filter Topology Set QED.DimReg QED.DimReg.Sector
open QED.DimReg.TwoLoopSESector (atRe eventually_re_gt halfPlane zero_mem_halfPlane)

namespace QED.DimReg.LineCont

variable {N : ℕ}

/-- The slope `Σᵢ aᵢ wᵢ + h c_d` of a form along the line `(n + λw, d₀ + 2hλ)`. -/
def slopeZ (w : Fin N → ℕ) (h : ℕ) (f : AffForm) : ℤ :=
  ((List.finRange N).map fun i : Fin N => f.2.1.getD i 0 * w i).sum + h * f.2.2

/-- The line condition on one leaf form: slope `≥ 1`, and if the form has no `d`-term then its
`ν`-coefficients are nonnegative. It does not look at the constant `c₀`. -/
def formOk (w : Fin N → ℕ) (h : ℕ) (f : AffForm) : Bool :=
  decide (1 ≤ slopeZ w h f) &&
    (f.2.2 != 0 || (List.finRange N).all fun i : Fin N => decide (0 ≤ f.2.1.getD i 0))

/-- For a leaf form with nonnegative `ν`-coefficients, `c₀ + Σᵢ aᵢ = 1 + jₖ ≥ 1`. -/
theorem one_le_leafForm (D : List ℕ) (fl : List Bool) (ps : List (Fin N × Fin N)) (m : List ℕ)
    (k : Fin N) (hnn : ∀ i : Fin N, 0 ≤ (leafForm D fl ps m k).2.1.getD i 0) :
    1 ≤ (leafForm D fl ps m k).1 + ∑ i : Fin N, (leafForm D fl ps m k).2.1.getD i 0 := by
  have he : ∀ i : Fin N, (leafForm D fl ps m k).2.1.getD i 0 = pullZ ps k i := by
    intro i
    have h1 := hnn i
    simp only [leafForm, getD_map_finRange] at h1 ⊢
    have h2 : 0 ≤ pullZ ps k i := by simp [pullZ]
    split_ifs at h1 ⊢ <;> omega
  rw [Finset.sum_congr rfl fun i _ => he i]
  simp only [leafForm, sum_map_finRange]
  have : ∑ i : Fin N, pullZ ps k i = Finset.univ.sum (pullZ ps k) := rfl
  omega

/-- **The data of a Lee–Pomeransky family along lines.** -/
structure LineFamily (N : ℕ) where
  /-- Certified sector data of the Lee–Pomeransky polynomial. -/
  S : LPSectorData N
  /-- The direction in `ν`: `ν = n + λw`. -/
  w : Fin N → ℕ
  one_le_w : ∀ i, 1 ≤ w i
  /-- The direction in `d`: `d = d₀ + 2hλ`. -/
  h : ℕ
  one_le_h : 1 ≤ h
  /-- The degree `L + 1` of `F`. -/
  Lp : ℕ
  /-- The partial derivatives of `G`. -/
  G' : Fin N → (Fin N → ℝ) → ℝ
  pos : ∀ x ∈ posOrthant N, 0 < S.G.eval x
  deriv : ∀ b, ∀ x ∈ posOrthant N,
    HasDerivAt (fun t => S.G.eval (Function.update x b t)) (G' b x) (x b)
  /-- The monomials of `xᵢ ∂ᵢ G`. -/
  R : Fin N → MonoList N
  raise : ∀ i x, x i * G' i x = polyEval (R i) x
  raise_spec : ∀ i, ∀ t ∈ R i, 1 ≤ t.2 i ∧ ∑ j, t.2 j ≤ Lp
  line : ∀ T, ∀ ps ∈ (S.tree T).paths, ∀ k,
    formOk w h (leafForm S.D (flagsOf T) ps (S.leafMin T ps) k) = true

namespace LineFamily

variable (F : LineFamily N)

theorem leafS_eq (T : Finset (Fin N)) (ps : List (Fin N × Fin N)) (ν : ℂ → Fin N → ℂ)
    (d : ℂ → ℂ) (l : ℂ) (k : Fin N) :
    F.S.leafS T ps ν d l k =
      (leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k).eval (ν l) (d l) := by
  rw [← leafExp_eq_eval_leafForm, flagSet_flagsOf]
  rfl

theorem slope_ge {T : Finset (Fin N)} {ps : List (Fin N × Fin N)}
    (hps : ps ∈ (F.S.tree T).paths) (k : Fin N) :
    1 ≤ slopeZ F.w F.h (leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k) := by
  have := F.line T ps hps k
  simp only [formOk, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

theorem dfree {T : Finset (Fin N)} {ps : List (Fin N × Fin N)}
    (hps : ps ∈ (F.S.tree T).paths) (k : Fin N)
    (h0 : (leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k).2.2 = 0) :
    (∀ i : Fin N, 0 ≤ (leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k).2.1.getD i 0) ∧
      1 ≤ (leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k).1 +
        ∑ i : Fin N, (leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k).2.1.getD i 0 := by
  have := F.line T ps hps k
  simp only [formOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
    h0, not_true_eq_false, false_or, List.all_eq_true, List.mem_finRange, true_implies] at this
  exact ⟨this.2, one_le_leafForm _ _ _ _ _ this.2⟩

end LineFamily

/-! ### Lines -/

/-- The exponents `ν = n + λw` on the line through the label `n`. -/
def lineNu (w : Fin N → ℕ) (n : Fin N → ℤ) (l : ℂ) : Fin N → ℂ := fun i => n i + w i * l

/-- The dimension `d = d₀ + 2hλ` on the line. -/
def lineD (h : ℕ) (d₀ l : ℂ) : ℂ := d₀ + 2 * h * l

theorem differentiable_lineNu (w : Fin N → ℕ) (n : Fin N → ℤ) (i : Fin N) :
    Differentiable ℂ fun l => lineNu w n l i := by
  unfold lineNu; fun_prop

theorem differentiable_lineD (h : ℕ) (d₀ : ℂ) : Differentiable ℂ (lineD h d₀) := by
  unfold lineD; fun_prop

/-- The value of a form at `λ = 0` (its real part). -/
noncomputable def baseRe (f : AffForm) (n : Fin N → ℤ) (d₀ : ℂ) : ℝ :=
  f.1 + ∑ i : Fin N, (f.2.1.getD i 0 : ℝ) * n i + f.2.2 * (d₀.re / 2)

theorem re_eval_line (w : Fin N → ℕ) (h : ℕ) (f : AffForm) (n : Fin N → ℤ) (d₀ l : ℂ) :
    (f.eval (lineNu w n l) (lineD h d₀ l)).re = baseRe f n d₀ + slopeZ w h f * l.re := by
  simp only [AffForm.eval, lineNu, lineD, baseRe, slopeZ, sum_map_finRange, add_re, re_sum,
    mul_re, intCast_re, intCast_im, zero_mul, sub_zero, div_ofNat_re, re_ofNat, im_ofNat,
    natCast_re, natCast_im, mul_zero]
  push_cast
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [show ((2 : ℂ) * h).im = 0 by simp, zero_mul, sub_zero]
  rw [add_mul (∑ x : Fin N, _), Finset.sum_mul]
  simp only [mul_assoc]
  ring

namespace LineFamily

variable (F : LineFamily N)

theorem re_leafS_line {T : Finset (Fin N)} {ps : List (Fin N × Fin N)}
    (hps : ps ∈ (F.S.tree T).paths) (k : Fin N) (n : Fin N → ℤ) (d₀ : ℂ) :
    ∃ f : AffForm, 1 ≤ slopeZ F.w F.h f ∧ ∀ l,
      (F.S.leafS T ps (lineNu F.w n) (lineD F.h d₀) l k).re =
        baseRe f n d₀ + slopeZ F.w F.h f * l.re :=
  ⟨_, F.slope_ge hps k, fun l => by rw [leafS_eq, re_eval_line]⟩

/-- A common bound for finitely many leaf quantities. -/
theorem exists_bound (B : Finset (Fin N) → List (Fin N × Fin N) → Fin N → ℕ) :
    ∃ K : ℕ, ∀ T, ∀ ps ∈ (F.S.tree T).paths, ∀ k, B T ps k ≤ K := by
  refine ⟨∑ T : Finset (Fin N), ((F.S.tree T).paths.map fun ps => ∑ k, B T ps k).sum,
    fun T ps hps k => ?_⟩
  calc B T ps k ≤ ∑ k, B T ps k := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    _ ≤ ((F.S.tree T).paths.map fun ps => ∑ k, B T ps k).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem hps)
    _ ≤ _ := Finset.single_le_sum (f := fun T => ((F.S.tree T).paths.map fun ps =>
        ∑ k, B T ps k).sum) (fun _ _ => Nat.zero_le _) (Finset.mem_univ T)

/-- A `K` for which all leaf exponents have `re > -K` on the half-plane `re λ > -1`. -/
theorem exists_K (n : Fin N → ℤ) (d₀ : ℂ) :
    ∃ K : ℕ, ∀ l ∈ halfPlane, F.S.ReGt (lineNu F.w n) (lineD F.h d₀) (-K) l := by
  obtain ⟨K, hK⟩ := F.exists_bound fun T ps k =>
    ⌈|baseRe (leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k) n d₀|⌉₊ +
      (slopeZ F.w F.h (leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k)).toNat + 1
  refine ⟨K, fun l hl T ps hps k => ?_⟩
  rw [leafS_eq, re_eval_line]
  set f := leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k
  have hb := hK T ps hps k
  have s1 : 1 ≤ slopeZ F.w F.h f := F.slope_ge hps k
  have h2 : (|baseRe f n d₀| : ℝ) ≤ ⌈|baseRe f n d₀|⌉₊ := Nat.le_ceil _
  have h3 : ((⌈|baseRe f n d₀|⌉₊ + (slopeZ F.w F.h f).toNat + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hb
  have h4 : ((slopeZ F.w F.h f).toNat : ℝ) = (slopeZ F.w F.h f : ℝ) := by
    have : ((slopeZ F.w F.h f).toNat : ℤ) = slopeZ F.w F.h f := Int.toNat_of_nonneg
      (by omega)
    exact_mod_cast this
  have s1' : (1 : ℝ) ≤ slopeZ F.w F.h f := by exact_mod_cast s1
  have hl' : -1 < l.re := hl
  have hb' := neg_abs_le (baseRe f n d₀)
  push_cast at h3
  rw [h4] at h3
  nlinarith

/-! ### The continuation along a line -/

/-- The `K` of `exists_K`. -/
noncomputable def Kof (n : Fin N → ℤ) (d₀ : ℂ) : ℕ := Classical.choose (F.exists_K n d₀)

theorem reGt_Kof (n : Fin N → ℤ) (d₀ : ℂ) {l : ℂ} (hl : l ∈ halfPlane) :
    F.S.ReGt (lineNu F.w n) (lineD F.h d₀) (-(F.Kof n d₀)) l :=
  Classical.choose_spec (F.exists_K n d₀) l hl

/-- **The continued Lee–Pomeransky integral along the line** `λ ↦ (n + λ, d₀ + 2hλ)`. -/
noncomputable def Jline (n : Fin N → ℤ) (d₀ : ℂ) : ℂ → ℂ :=
  F.S.lpCont (F.Kof n d₀) (lineNu F.w n) (lineD F.h d₀)

theorem meromorphicOn_Jline (n : Fin N → ℤ) (d₀ : ℂ) :
    MeromorphicOn (F.Jline n d₀) halfPlane := fun _ hl =>
  F.S.meromorphicAt_lpCont _ (differentiable_lineNu F.w n) (differentiable_lineD F.h d₀)
    (F.reGt_Kof n d₀ hl)

/-- For `re λ` large, all leaf exponents have real part `> c`. -/
theorem eventually_reGt (n : Fin N → ℤ) (d₀ : ℂ) (c : ℝ) :
    ∀ᶠ l in atRe, F.S.ReGt (lineNu F.w n) (lineD F.h d₀) c l := by
  simp only [LPSectorData.ReGt]
  refine eventually_all.2 fun T => ?_
  have hfin : {ps | ps ∈ (F.S.tree T).paths}.Finite := (F.S.tree T).paths.finite_toSet
  have := (eventually_all_finite hfin (l := atRe)
    (p := fun ps l => ∀ k, c < (F.S.leafS T ps (lineNu F.w n) (lineD F.h d₀) l k).re)).2
    fun ps hps => eventually_all.2 fun k => by
      obtain ⟨f, s1, he⟩ := F.re_leafS_line hps k n d₀
      filter_upwards [eventually_re_gt |c - baseRe f n d₀|] with l hl
      rw [he l]
      have s1' : (1 : ℝ) ≤ slopeZ F.w F.h f := by exact_mod_cast s1
      have h0 := abs_nonneg (c - baseRe f n d₀)
      have h1 := le_abs_self (c - baseRe f n d₀)
      nlinarith
  exact this.mono fun _ hl ps hps => hl ps hps

/-- **For `re λ` large the integral converges and equals the continuation.** -/
theorem eventually_Jline_eq (n : Fin N → ℤ) (d₀ : ℂ) :
    ∀ᶠ l in atRe, LPConvergent (fun x => F.S.G.eval x) (lineNu F.w n l) (lineD F.h d₀ l) ∧
      lpIntegral (fun x => F.S.G.eval x) (lineNu F.w n l) (lineD F.h d₀ l) = F.Jline n d₀ l :=
  (F.eventually_reGt n d₀ 0).mono fun _ hl =>
    ⟨F.S.lpConvergent_of_re (differentiable_lineD F.h d₀) hl,
      F.S.lpIntegral_eq_lpCont _ (differentiable_lineD F.h d₀) hl⟩

end LineFamily

end QED.DimReg.LineCont
