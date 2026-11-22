/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopSELeaves
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Convex

/-!
# The two-loop self-energy family along lines: continuation, uniqueness, convergence

For an integer label `n ∈ ℤ⁵` and a base dimension `d₀ ∈ ℂ`, consider the line
`λ ↦ (ν, d) = (n + λ, d₀ + 4λ)` (all five exponents shifted by `λ`). Along it every leaf exponent
of the certified sector data `QED.DimReg.TwoLoopSESector.sectorData` is affine in `λ` with integer
slope in `[1, 4]`, which is now an integer check on the generated table:

* `QED.DimReg.TwoLoopSESector.leafS_eq`, `mem_allForms`: the leaf exponents of `sectorData` are
  the forms of `leafFormTable` (item 1);
* `slope_allForms`, `dfree_allForms`: kernel checks on the 55 distinct forms.

Hence (`Jline n d₀`, the continuation along the line with a `K` that works on the half-plane
`re λ > -1`):

* `meromorphicOn_Jline`: `Jline` is meromorphic on the half-plane;
* `eventually_Jline_eq`: for `re λ` large the integral converges and equals `Jline`;
* `lpCont_eventuallyEq_Jline`, `lpCont_eq_Jline`: any other admissible `K` gives the same
  function off a discrete set, and the same value wherever both are continuous (item 2);
* `eventually_nhdsNE_of_atRe`: a meromorphic function on the half-plane that vanishes for
  `re λ` large vanishes in a punctured neighbourhood of `λ = 0`. This is the identity theorem in
  the form used to carry relations to `λ = 0`.
-/

@[expose] public section

open Complex Filter Topology Set

namespace QED.DimReg

/-- **The identity theorem on a preconnected set.** Two functions meromorphic on a preconnected
set `U` that agree on a nonempty open subset agree in a punctured neighbourhood of each point
of `U`. -/
theorem eventuallyEq_nhdsNE_of_meromorphicOn {f g : ℂ → ℂ} {U V : Set ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : IsPreconnected U) (hVU : V ⊆ U)
    (hV : IsOpen V) (hne : V.Nonempty) (h : EqOn f g V) {y : ℂ} (hy : y ∈ U) :
    f =ᶠ[𝓝[≠] y] g := by
  obtain ⟨x, hx⟩ := hne
  have hm : MeromorphicOn (f - g) U := fun z hz => (hf z hz).sub (hg z hz)
  have hx0 : meromorphicOrderAt (f - g) x = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds hx)] with z hz
    simp [h hz]
  have hy' := hm.meromorphicOrderAt_eq_top_of_isPreconnected hU (hVU hx) hy hx0
  rw [meromorphicOrderAt_eq_top_iff] at hy'
  filter_upwards [hy'] with z hz
  exact sub_eq_zero.mp hz

end QED.DimReg

namespace QED.DimReg.TwoLoopSESector

open QED.DimReg.Sector

/-! ### The leaf exponents are the tabulated forms (item 1) -/

/-- All leaf forms of the table. -/
def allForms : List AffForm := leafFormTable.flatMap fun e => e.2.flatten

theorem mem_of_mem_getD_lookup {fl : List Bool} {x : List AffForm} :
    ∀ {L : List (List Bool × List (List AffForm))}, x ∈ (L.lookup fl).getD [] →
      ∃ e ∈ L, x ∈ e.2
  | [], h => by simp at h
  | (a, b) :: L, h => by
    simp only [List.lookup] at h
    split at h
    · exact ⟨(a, b), List.mem_cons_self, by simpa using h⟩
    · obtain ⟨e, he, hx⟩ := mem_of_mem_getD_lookup h
      exact ⟨e, List.mem_cons_of_mem _ he, hx⟩

/-- **The leaf exponents of `sectorData` are the generated forms.** -/
theorem leafS_eq (T : Finset (Fin 5)) (ps : List (Fin 5 × Fin 5)) (ν : ℂ → Fin 5 → ℂ)
    (d : ℂ → ℂ) (l : ℂ) (k : Fin 5) :
    sectorData.leafS T ps ν d l k =
      (leafForm degD (flagsOf T) ps (minOfFlags (flagsOf T) ps) k).eval (ν l) (d l) := by
  rw [← leafExp_eq_eval_leafForm, flagSet_flagsOf]
  simp only [minOfFlags, flagSet_flagsOf]
  rfl

theorem mem_allForms {T : Finset (Fin 5)} {ps : List (Fin 5 × Fin 5)}
    (hps : ps ∈ (sectorData.tree T).paths) (k : Fin 5) :
    leafForm degD (flagsOf T) ps (minOfFlags (flagsOf T) ps) k ∈ allForms := by
  have h := leafFormTable_eq (decide (0 ∈ T)) (decide (1 ∈ T)) (decide (2 ∈ T))
    (decide (3 ∈ T)) (decide (4 ∈ T))
  rw [← flagsOf_eq] at h
  have hx : leafForms degD (flagsOf T) ps (minOfFlags (flagsOf T) ps) ∈
      (leafFormTable.lookup (flagsOf T)).getD [] := by
    rw [h]
    exact List.mem_map_of_mem hps
  obtain ⟨e, he, hxe⟩ := mem_of_mem_getD_lookup hx
  simp only [allForms, List.mem_flatMap, List.mem_flatten]
  exact ⟨e, he, _, hxe, List.mem_map_of_mem (List.mem_finRange k)⟩

/-- The slope `Σᵢ aᵢ + 2 c_d` of a form along the line `(n + λ, d₀ + 4λ)`. -/
def slopeZ (f : AffForm) : ℤ := ((List.finRange 5).map fun i : Fin 5 => f.2.1.getD i 0).sum +
  2 * f.2.2

/-- **Every leaf exponent increases along the lines**, with slope in `[1, 4]`. -/
theorem slope_allForms : ∀ f ∈ allForms, 1 ≤ slopeZ f ∧ slopeZ f ≤ 4 := by decide +kernel

/-- **The `d`-free forms are positive at positive labels**: their `ν`-coefficients are
nonnegative and `c₀ + Σᵢ aᵢ ≥ 1`. -/
theorem dfree_allForms : ∀ f ∈ allForms, f.2.2 = 0 →
    (∀ i : Fin 5, 0 ≤ f.2.1.getD i 0) ∧
      1 ≤ f.1 + ((List.finRange 5).map fun i : Fin 5 => f.2.1.getD i 0).sum := by
  decide +kernel

/-! ### Lines -/

/-- The exponents `ν = n + λ` on the line through the label `n`. -/
def lineNu (n : Fin 5 → ℤ) (l : ℂ) : Fin 5 → ℂ := fun i => n i + l

/-- The dimension `d = d₀ + 4λ` on the line. -/
def lineD (d₀ l : ℂ) : ℂ := d₀ + 4 * l

theorem differentiable_lineNu (n : Fin 5 → ℤ) (i : Fin 5) :
    Differentiable ℂ fun l => lineNu n l i := by
  unfold lineNu; fun_prop

theorem differentiable_lineD (d₀ : ℂ) : Differentiable ℂ (lineD d₀) := by
  unfold lineD; fun_prop

/-- The value of a form at `λ = 0` (its real part). -/
noncomputable def baseRe (f : AffForm) (n : Fin 5 → ℤ) (d₀ : ℂ) : ℝ :=
  f.1 + ∑ i : Fin 5, (f.2.1.getD i 0 : ℝ) * n i + f.2.2 * (d₀.re / 2)

theorem re_eval_line (f : AffForm) (n : Fin 5 → ℤ) (d₀ l : ℂ) :
    (f.eval (lineNu n l) (lineD d₀ l)).re = baseRe f n d₀ + slopeZ f * l.re := by
  simp only [AffForm.eval, lineNu, lineD, baseRe, slopeZ, sum_map_finRange, add_re, re_sum,
    mul_re, intCast_re, intCast_im, zero_mul, sub_zero, div_ofNat_re, re_ofNat, im_ofNat]
  push_cast
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem re_leafS_line {T : Finset (Fin 5)} {ps : List (Fin 5 × Fin 5)}
    (hps : ps ∈ (sectorData.tree T).paths) (k : Fin 5) (n : Fin 5 → ℤ) (d₀ : ℂ) :
    ∃ f ∈ allForms, ∀ l, (sectorData.leafS T ps (lineNu n) (lineD d₀) l k).re =
      baseRe f n d₀ + slopeZ f * l.re :=
  ⟨_, mem_allForms hps k, fun l => by rw [leafS_eq, re_eval_line]⟩

/-- The half-plane `re λ > -1`. -/
def halfPlane : Set ℂ := {l | -1 < l.re}

theorem isOpen_halfPlane : IsOpen halfPlane := isOpen_lt continuous_const continuous_re

theorem isPreconnected_halfPlane : IsPreconnected halfPlane :=
  (convex_halfSpace_re_gt (-1)).isPreconnected

theorem zero_mem_halfPlane : (0 : ℂ) ∈ halfPlane := by simp [halfPlane]

/-- A `K` for which all leaf exponents have `re > -K` on the half-plane. -/
theorem exists_K (n : Fin 5 → ℤ) (d₀ : ℂ) :
    ∃ K : ℕ, ∀ l ∈ halfPlane, sectorData.ReGt (lineNu n) (lineD d₀) (-K) l := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ f ∈ allForms, ⌈|baseRe f n d₀|⌉₊ + 5 ≤ K :=
    ⟨(allForms.map fun f => ⌈|baseRe f n d₀|⌉₊ + 5).sum, fun f hf =>
      List.le_sum_of_mem (List.mem_map_of_mem (f := fun f => ⌈|baseRe f n d₀|⌉₊ + 5) hf)⟩
  refine ⟨K, fun l hl T ps hps k => ?_⟩
  obtain ⟨f, hf, he⟩ := re_leafS_line hps k n d₀
  rw [he]
  have h2 : (|baseRe f n d₀| : ℝ) ≤ ⌈|baseRe f n d₀|⌉₊ := Nat.le_ceil _
  have h3 : ((⌈|baseRe f n d₀|⌉₊ + 5 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK f hf
  obtain ⟨s1, s4⟩ := slope_allForms f hf
  have s1' : (1 : ℝ) ≤ slopeZ f := by exact_mod_cast s1
  have s4' : (slopeZ f : ℝ) ≤ 4 := by exact_mod_cast s4
  have hl' : -1 < l.re := hl
  have hb := neg_abs_le (baseRe f n d₀)
  push_cast at h3
  nlinarith

/-! ### The continuation along a line -/

/-- The `K` of `exists_K`. -/
noncomputable def Kof (n : Fin 5 → ℤ) (d₀ : ℂ) : ℕ := Classical.choose (exists_K n d₀)

theorem reGt_Kof (n : Fin 5 → ℤ) (d₀ : ℂ) {l : ℂ} (hl : l ∈ halfPlane) :
    sectorData.ReGt (lineNu n) (lineD d₀) (-(Kof n d₀)) l :=
  Classical.choose_spec (exists_K n d₀) l hl

/-- **The continued Lee–Pomeransky integral of the two-loop family along the line**
`λ ↦ (n + λ, d₀ + 4λ)`. -/
noncomputable def Jline (n : Fin 5 → ℤ) (d₀ : ℂ) : ℂ → ℂ :=
  sectorData.lpCont (Kof n d₀) (lineNu n) (lineD d₀)

theorem meromorphicOn_lpCont {n : Fin 5 → ℤ} {d₀ : ℂ} {K : ℕ}
    (hK : ∀ l ∈ halfPlane, sectorData.ReGt (lineNu n) (lineD d₀) (-K) l) :
    MeromorphicOn (sectorData.lpCont K (lineNu n) (lineD d₀)) halfPlane := fun l hl =>
  sectorData.meromorphicAt_lpCont K (differentiable_lineNu n) (differentiable_lineD d₀) (hK l hl)

theorem meromorphicOn_Jline (n : Fin 5 → ℤ) (d₀ : ℂ) : MeromorphicOn (Jline n d₀) halfPlane :=
  meromorphicOn_lpCont fun _ hl => reGt_Kof n d₀ hl

/-- The filter of `re λ → +∞`. -/
def atRe : Filter ℂ := comap re atTop

theorem eventually_re_gt (M : ℝ) : ∀ᶠ l in atRe, M < l.re :=
  tendsto_comap.eventually (eventually_gt_atTop M)

/-- For `re λ` large, all leaf exponents have real part `> c`. -/
theorem eventually_reGt (n : Fin 5 → ℤ) (d₀ : ℂ) (c : ℝ) :
    ∀ᶠ l in atRe, sectorData.ReGt (lineNu n) (lineD d₀) c l := by
  simp only [LPSectorData.ReGt]
  refine eventually_all.2 fun T => ?_
  have hfin : {ps | ps ∈ (sectorData.tree T).paths}.Finite := (sectorData.tree T).paths.finite_toSet
  have := (eventually_all_finite hfin (l := atRe)
    (p := fun ps l => ∀ k, c < (sectorData.leafS T ps (lineNu n) (lineD d₀) l k).re)).2
    fun ps hps => eventually_all.2 fun k => by
      obtain ⟨f, hf, he⟩ := re_leafS_line hps k n d₀
      filter_upwards [eventually_re_gt |c - baseRe f n d₀|] with l hl
      rw [he]
      have s1 : (1 : ℝ) ≤ slopeZ f := by exact_mod_cast (slope_allForms f hf).1
      have h0 := abs_nonneg (c - baseRe f n d₀)
      have h1 := le_abs_self (c - baseRe f n d₀)
      nlinarith
  exact this.mono fun l hl ps hps => hl ps hps

/-- **For `re λ` large the integral converges and equals the continuation.** -/
theorem eventually_Jline_eq (n : Fin 5 → ℤ) (d₀ : ℂ) :
    ∀ᶠ l in atRe, LPConvergent (fun x => sectorData.G.eval x) (lineNu n l) (lineD d₀ l) ∧
      lpIntegral (fun x => sectorData.G.eval x) (lineNu n l) (lineD d₀ l) = Jline n d₀ l :=
  (eventually_reGt n d₀ 0).mono fun _ hl =>
    ⟨sectorData.lpConvergent_of_re (differentiable_lineD d₀) hl,
      sectorData.lpIntegral_eq_lpCont _ (differentiable_lineD d₀) hl⟩

/-- A property holding for `re λ` large holds on a nonempty open subset of the half-plane. -/
theorem exists_open_of_atRe {P : ℂ → Prop} (h : ∀ᶠ l in atRe, P l) :
    ∃ V : Set ℂ, IsOpen V ∧ V.Nonempty ∧ V ⊆ halfPlane ∧ ∀ l ∈ V, P l := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_comap.1 h)
  refine ⟨{l | max M 0 < l.re}, isOpen_lt continuous_const continuous_re,
    ⟨(max M 0 + 1 : ℝ), by simp only [mem_ofPred_eq, ofReal_re]; linarith⟩, fun l hl => ?_,
    fun l hl => hM l.re ?_ l rfl⟩
  · have : max M 0 < l.re := hl
    show -1 < l.re
    linarith [le_max_right M 0]
  · exact (le_max_left M 0).trans (le_of_lt hl)

/-- **Relations are carried from `re λ → ∞` to every point of the half-plane** (identity
theorem): two functions meromorphic on the half-plane that agree for `re λ` large agree in a
punctured neighbourhood of each point of it. -/
theorem eventuallyEq_nhdsNE_of_atRe {F G : ℂ → ℂ} (hF : MeromorphicOn F halfPlane)
    (hG : MeromorphicOn G halfPlane) (h : ∀ᶠ l in atRe, F l = G l) {y : ℂ}
    (hy : y ∈ halfPlane) : F =ᶠ[𝓝[≠] y] G := by
  obtain ⟨V, hV, hne, hVU, hFG⟩ := exists_open_of_atRe h
  exact eventuallyEq_nhdsNE_of_meromorphicOn hF hG isPreconnected_halfPlane hVU hV hne hFG hy

/-- **Independence of `K`** (off a discrete set): any `K` admissible on the half-plane gives the
same continuation. -/
theorem lpCont_eventuallyEq_Jline {n : Fin 5 → ℤ} {d₀ : ℂ} {K : ℕ}
    (hK : ∀ l ∈ halfPlane, sectorData.ReGt (lineNu n) (lineD d₀) (-K) l) {y : ℂ}
    (hy : y ∈ halfPlane) : sectorData.lpCont K (lineNu n) (lineD d₀) =ᶠ[𝓝[≠] y] Jline n d₀ := by
  refine eventuallyEq_nhdsNE_of_atRe (meromorphicOn_lpCont hK) (meromorphicOn_Jline n d₀) ?_ hy
  filter_upwards [eventually_reGt n d₀ 0, eventually_Jline_eq n d₀] with l hl hJ
  rw [← hJ.2, sectorData.lpIntegral_eq_lpCont _ (differentiable_lineD d₀) hl]

/-- **Independence of `K`** at every point where both continuations are continuous. -/
theorem lpCont_eq_Jline {n : Fin 5 → ℤ} {d₀ : ℂ} {K : ℕ}
    (hK : ∀ l ∈ halfPlane, sectorData.ReGt (lineNu n) (lineD d₀) (-K) l) {y : ℂ}
    (hy : y ∈ halfPlane) (h₁ : ContinuousAt (sectorData.lpCont K (lineNu n) (lineD d₀)) y)
    (h₂ : ContinuousAt (Jline n d₀) y) : sectorData.lpCont K (lineNu n) (lineD d₀) y =
      Jline n d₀ y :=
  tendsto_nhds_unique (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    ((h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' (lpCont_eventuallyEq_Jline hK hy).symm)

end QED.DimReg.TwoLoopSESector
