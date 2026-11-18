/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The second-order limit of an integral of polynomial families

Analytic core of obligation O2-22 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). Along a curve of
external momenta with parameter `u ∈ (-1, 1)` the parametric integrands of the order-`e⁵` vertex,
projected onto the Pauli numerator, have the form `A(x, u) / ((1 - u²)ᵃ V(x, u)ᴺ)` with
`u ↦ A(x, u)` a polynomial of bounded degree for every Feynman-parameter point `x`, `A(x, 0) = 0`,
and `V ≥ c > 0` even in `u`. This file proves the limit of the even part divided by `u²`.

* `IsUPoly D f`: for every `x`, `u ↦ f x u` agrees on `(-1, 1)` with a polynomial of degree at
  most `D`. Closed under sums, products and constants in `u` (`IsUPoly.add`, `IsUPoly.mul`, …).
* `IsUPoly.eq_interp`: such a family is its Lagrange interpolant at the nodes `k / (D + 1)`, whose
  coefficients are fixed linear combinations of the values at the nodes
  (`interp_coeff`). Hence **the coefficients are integrable in `x` as soon as the values at the
  nodes are** (`integrable_interp_coeff`); no joint structure in `x` is needed.
* `tendsto_even_div_sq`: under the hypotheses above,
  `(∫ f(u) + ∫ f(-u)) / (2u²) → ∫ a₂(x) / V(x, 0)ᴺ` as `u → 0`, `u ≠ 0`, where `a₂(x)` is the
  coefficient of `u²` of `A(x, ·)`. The proof writes the even part of `A(x, ·)` as
  `a₀(x) + u² B(x, u)` with `a₀ = A(·, 0) = 0` and `|B| ≤ ∑ⱼ |aⱼ|`, and uses dominated
  convergence.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Set

namespace QED.TwoLoop.PauliZeroLimit

/-! ### Families of polynomials in one real variable -/

/-- For every parameter `x`, `u ↦ f x u` agrees on `(-1, 1)` with a complex polynomial of degree
at most `D`. -/
def IsUPoly {ι : Type*} (D : ℕ) (f : ι → ℝ → ℂ) : Prop :=
  ∀ x, ∃ P : ℂ[X], P.natDegree ≤ D ∧ ∀ u ∈ Ioo (-1 : ℝ) 1, f x u = P.eval (u : ℂ)

namespace IsUPoly

variable {ι : Type*} {D E : ℕ} {f g : ι → ℝ → ℂ}

theorem mono (h : IsUPoly D f) (hDE : D ≤ E) : IsUPoly E f := fun x => by
  obtain ⟨P, hP, hf⟩ := h x
  exact ⟨P, hP.trans hDE, hf⟩

theorem congr (h : IsUPoly D f) (hfg : ∀ x, ∀ u ∈ Ioo (-1 : ℝ) 1, f x u = g x u) :
    IsUPoly D g := fun x => by
  obtain ⟨P, hP, hf⟩ := h x
  exact ⟨P, hP, fun u hu => by rw [← hfg x u hu, hf u hu]⟩

theorem const (c : ι → ℂ) : IsUPoly D fun x _ => c x := fun x =>
  ⟨C (c x), by rw [natDegree_C]; exact Nat.zero_le _, fun _ _ => by rw [eval_C]⟩

theorem var : IsUPoly 1 fun (_ : ι) u => (u : ℂ) := fun _ =>
  ⟨X, natDegree_X_le, fun _ _ => by rw [eval_X]⟩

theorem add (hf : IsUPoly D f) (hg : IsUPoly D g) : IsUPoly D fun x u => f x u + g x u :=
  fun x => by
    obtain ⟨P, hP, hf⟩ := hf x
    obtain ⟨Q, hQ, hg⟩ := hg x
    exact ⟨P + Q, (natDegree_add_le _ _).trans (max_le hP hQ), fun u hu => by
      rw [eval_add, ← hf u hu, ← hg u hu]⟩

theorem neg (hf : IsUPoly D f) : IsUPoly D fun x u => -f x u := fun x => by
  obtain ⟨P, hP, hf⟩ := hf x
  exact ⟨-P, by rw [natDegree_neg]; exact hP, fun u hu => by rw [eval_neg, ← hf u hu]⟩

theorem sub (hf : IsUPoly D f) (hg : IsUPoly D g) : IsUPoly D fun x u => f x u - g x u := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : IsUPoly D f) (hg : IsUPoly E g) : IsUPoly (D + E) fun x u => f x u * g x u :=
  fun x => by
    obtain ⟨P, hP, hf⟩ := hf x
    obtain ⟨Q, hQ, hg⟩ := hg x
    exact ⟨P * Q, natDegree_mul_le.trans (Nat.add_le_add hP hQ), fun u hu => by
      rw [eval_mul, ← hf u hu, ← hg u hu]⟩

theorem const_mul (c : ι → ℂ) (hf : IsUPoly D f) : IsUPoly D fun x u => c x * f x u := by
  simpa using (const (D := 0) c).mul hf

theorem mul_const (c : ι → ℂ) (hf : IsUPoly D f) : IsUPoly D fun x u => f x u * c x := by
  simpa using hf.mul (const (D := 0) c)

theorem sum {κ : Type*} (s : Finset κ) {F : κ → ι → ℝ → ℂ} (h : ∀ k ∈ s, IsUPoly D (F k)) :
    IsUPoly D fun x u => ∑ k ∈ s, F k x u := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (ι := ι) (D := D) fun _ => 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem prod {κ : Type*} (s : Finset κ) {F : κ → ι → ℝ → ℂ} (d : κ → ℕ)
    (h : ∀ k ∈ s, IsUPoly (d k) (F k)) :
    IsUPoly (∑ k ∈ s, d k) fun x u => ∏ k ∈ s, F k x u := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (ι := ι) (D := 0) fun _ => 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem pow (hf : IsUPoly D f) (n : ℕ) : IsUPoly (n * D) fun x u => f x u ^ n := by
  induction n with
  | zero => simpa using const (ι := ι) (D := 0) fun _ => 1
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using ih.mul hf

end IsUPoly

/-! ### Lagrange interpolation at fixed nodes -/

/-- The nodes `k / (D + 1)`, `k ≤ D`, in `[0, 1)`. -/
noncomputable def node (D : ℕ) (k : Fin (D + 1)) : ℝ := (k : ℝ) / (D + 1)

theorem node_mem (D : ℕ) (k : Fin (D + 1)) : node D k ∈ Ioo (-1 : ℝ) 1 := by
  have hk : (k : ℝ) < D + 1 := by exact_mod_cast k.isLt
  have hD : (0 : ℝ) < D + 1 := by positivity
  constructor
  · have : 0 ≤ node D k := div_nonneg (Nat.cast_nonneg _) hD.le
    linarith
  · exact (div_lt_one hD).mpr hk

theorem node_injOn (D : ℕ) :
    Set.InjOn (fun k : Fin (D + 1) => ((node D k : ℝ) : ℂ))
      ((Finset.univ : Finset (Fin (D + 1))) : Set (Fin (D + 1))) := by
  intro a _ b _ h
  have h' : node D a = node D b := Complex.ofReal_injective h
  have hD : (D + 1 : ℝ) ≠ 0 := by positivity
  simp only [node, div_left_inj' hD] at h'
  exact Fin.ext (by exact_mod_cast h')

/-- The Lagrange interpolant of `f x` at the nodes `k / (D + 1)`. -/
noncomputable def interp {ι : Type*} (D : ℕ) (f : ι → ℝ → ℂ) (x : ι) : ℂ[X] :=
  Lagrange.interpolate Finset.univ (fun k : Fin (D + 1) => ((node D k : ℝ) : ℂ))
    (fun k => f x (node D k))

section Interp

variable {ι : Type*} {D : ℕ} {f : ι → ℝ → ℂ}

theorem natDegree_interp_le (x : ι) : (interp D f x).natDegree ≤ D := by
  have h := Lagrange.degree_interpolate_lt (fun k => f x (node D k)) (node_injOn D)
  rw [Finset.card_univ, Fintype.card_fin] at h
  by_cases hp : interp D f x = 0
  · rw [hp, natDegree_zero]
    exact Nat.zero_le _
  · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hp).mpr h)

/-- **A polynomial family is its interpolant at the nodes.** -/
theorem IsUPoly.eq_interp (h : IsUPoly D f) (x : ι) :
    ∀ u ∈ Ioo (-1 : ℝ) 1, f x u = (interp D f x).eval (u : ℂ) := by
  obtain ⟨P, hP, hf⟩ := h x
  have hdeg : P.degree < (Finset.univ : Finset (Fin (D + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact (degree_le_of_natDegree_le hP).trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))
  have hPI : P = interp D f x :=
    Lagrange.eq_interpolate_of_eval_eq _ (node_injOn D) hdeg fun k _ =>
      (hf _ (node_mem D k)).symm
  intro u hu
  rw [hf u hu, hPI]

/-- The coefficients of the interpolant are fixed linear combinations of the node values. -/
theorem interp_coeff (x : ι) (j : ℕ) :
    (interp D f x).coeff j = ∑ k, f x (node D k) *
      (Lagrange.basis Finset.univ (fun k : Fin (D + 1) => ((node D k : ℝ) : ℂ)) k).coeff j := by
  simp only [interp, Lagrange.interpolate_apply, finsetSum_coeff, coeff_C_mul]

/-- **The coefficients are integrable** when the values at the nodes are. -/
theorem integrable_interp_coeff [MeasurableSpace ι] {μ : Measure ι} (hf : ∀ k, Integrable (fun x => f x (node D k)) μ)
    (j : ℕ) : Integrable (fun x => (interp D f x).coeff j) μ := by
  simp only [interp_coeff]
  exact integrable_finsetSum _ fun k _ => (hf k).mul_const _

theorem eval_interp_eq_sum (x : ι) (z : ℂ) :
    (interp D f x).eval z = ∑ j ∈ Finset.range (D + 1), (interp D f x).coeff j * z ^ j :=
  eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_interp_le x)) z

end Interp

/-! ### The even part divided by `u²` -/

/-- The weight `1 - u²`. -/
def wt (u : ℝ) : ℂ := 1 - (u : ℂ) ^ 2

theorem wt_neg (u : ℝ) : wt (-u) = wt u := by simp [wt]

theorem wt_zero : wt 0 = 1 := by simp [wt]

/-- The even part of `u^j`, over `u²`: `u^{j-2}` for even `j ≥ 2`, else `0`. -/
noncomputable def evenCoeff (j : ℕ) (u : ℝ) : ℂ :=
  if Even j ∧ 2 ≤ j then (u : ℂ) ^ (j - 2) else 0

theorem pow_add_neg_pow (j : ℕ) (u : ℝ) :
    (u : ℂ) ^ j + ((-u : ℝ) : ℂ) ^ j =
      (if j = 0 then 2 else 0) + 2 * (u : ℂ) ^ 2 * evenCoeff j u := by
  rcases Nat.even_or_odd j with he | ho
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [evenCoeff]
      norm_num
    · have h2 : 2 ≤ j := by
        obtain ⟨r, rfl⟩ := he
        omega
      have hj0 : j ≠ 0 := by omega
      simp only [evenCoeff, he, h2, and_self, ite_true, hj0, ite_false, zero_add]
      push_cast
      rw [neg_pow, he.neg_one_pow, one_mul, mul_assoc, ← pow_add,
        show 2 + (j - 2) = j by omega]
      ring
  · have hj0 : j ≠ 0 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr ho) ⟨0, rfl⟩
    have hne : ¬ Even j := Nat.not_even_iff_odd.mpr ho
    simp only [evenCoeff, hne, false_and, ite_false, hj0, mul_zero, add_zero]
    push_cast
    rw [neg_pow, ho.neg_one_pow]
    ring

theorem norm_evenCoeff_le (j : ℕ) {u : ℝ} (hu : |u| ≤ 1) : ‖evenCoeff j u‖ ≤ 1 := by
  unfold evenCoeff
  split_ifs
  · rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg u) hu
  · simp

theorem tendsto_evenCoeff (j : ℕ) :
    Tendsto (evenCoeff j) (𝓝 0) (𝓝 (if j = 2 then 1 else 0)) := by
  have hc : Continuous (evenCoeff j) := by
    unfold evenCoeff
    split_ifs <;> fun_prop
  have h := hc.tendsto 0
  convert h using 2
  unfold evenCoeff
  by_cases h2 : j = 2
  · subst h2
    simp
  · simp only [h2, ite_false]
    split_ifs with h
    · have : j - 2 ≠ 0 := by omega
      simp [this]
    · rfl

section EvenLimit

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι} {D a N : ℕ} {A : ι → ℝ → ℂ} {V : ι → ℝ → ℝ} {c : ℝ}
  {f : ℝ → ι → ℂ}

theorem norm_wt_ge {u : ℝ} (hu : |u| ≤ 1 / 2) : (3 / 4 : ℝ) ≤ ‖wt u‖ := by
  have hu2 : u ^ 2 ≤ 1 / 4 := by
    have := sq_abs u ▸ pow_le_pow_left₀ (abs_nonneg u) hu 2
    linarith
  have e : wt u = ((1 - u ^ 2 : ℝ) : ℂ) := by simp [wt]
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

/-- **The second-order limit.** Let `A(x, ·)` be polynomials of degree at most `D` on `(-1, 1)`
whose values at the nodes are integrable in `x`, with `A(x, 0) = 0` a.e.; let `V ≥ c > 0` on
`(-1, 1)`, even and continuous at `0` in `u`, measurable in `x`; and let
`f(u) = A(·, u) / ((1 - u²)ᵃ V(·, u)ᴺ)` a.e. for `u ∈ (-1, 1)`. Then every `f(u)` is integrable and
`(∫ f(u) + ∫ f(-u)) / (2u²) → ∫ a₂ / V(·, 0)ᴺ` as `u → 0`, `u ≠ 0`, with `a₂(x)` the coefficient of
`u²` of `A(x, ·)`. -/
theorem tendsto_even_div_sq (hA : IsUPoly D A)
    (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) (hA0 : ∀ᵐ x ∂μ, A x 0 = 0)
    (hc : 0 < c) (hV : ∀ᵐ x ∂μ, ∀ u ∈ Ioo (-1 : ℝ) 1, c ≤ V x u)
    (hVeven : ∀ᵐ x ∂μ, ∀ u, V x (-u) = V x u) (hVcont : ∀ᵐ x ∂μ, ContinuousAt (V x) 0)
    (hVmeas : ∀ u, AEStronglyMeasurable (fun x => V x u) μ)
    (hf : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ᵐ x ∂μ, f u x = A x u / (wt u ^ a * (V x u : ℂ) ^ N)) :
    (∀ u ∈ Ioo (-1 : ℝ) 1, Integrable (f u) μ) ∧
      Tendsto (fun u => ((∫ x, f u x ∂μ) + ∫ x, f (-u) x ∂μ) / (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0)
        (𝓝 (∫ x, (interp D A x).coeff 2 / (V x 0 : ℂ) ^ N ∂μ)) := by
  have hcf : ∀ j, Integrable (fun x => (interp D A x).coeff j) μ := integrable_interp_coeff hAi
  -- the bound `∑ⱼ ‖aⱼ‖`
  set K : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ with hK
  have hKi : Integrable K μ := integrable_finsetSum _ fun j _ => (hcf j).norm
  have hK0 : ∀ x, 0 ≤ K x := fun x => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hAeq : ∀ x, ∀ u ∈ Ioo (-1 : ℝ) 1,
      A x u = ∑ j ∈ Finset.range (D + 1), (interp D A x).coeff j * (u : ℂ) ^ j := fun x u hu => by
    rw [hA.eq_interp x u hu, eval_interp_eq_sum]
  have hnormA : ∀ x, ∀ u ∈ Ioo (-1 : ℝ) 1, ‖A x u‖ ≤ K x := fun x u hu => by
    rw [hAeq x u hu]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have : |u| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg u) (abs_le.mpr ⟨hu.1.le, hu.2.le⟩)
    exact mul_le_of_le_one_right (norm_nonneg _) this
  have hAmeas : ∀ u ∈ Ioo (-1 : ℝ) 1, AEStronglyMeasurable (fun x => A x u) μ := fun u hu => by
    have h : (fun x => A x u) =
        fun x => ∑ j ∈ Finset.range (D + 1), (interp D A x).coeff j * (u : ℂ) ^ j :=
      funext fun x => hAeq x u hu
    rw [h]
    exact (integrable_finsetSum _ fun j _ => (hcf j).mul_const _).aestronglyMeasurable
  have hVc : ∀ u, AEStronglyMeasurable (fun x => ((V x u : ℝ) : ℂ)) μ := fun u =>
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (hVmeas u))
  -- integrability of `f u`
  have hfi : ∀ u ∈ Ioo (-1 : ℝ) 1, Integrable (f u) μ := fun u hu => by
    have hw : wt u ≠ 0 := by
      have e : wt u = ((1 - u ^ 2 : ℝ) : ℂ) := by simp [wt]
      rw [e, ofReal_ne_zero]
      nlinarith [hu.1, hu.2]
    have hwn : 0 < ‖wt u‖ ^ a := pow_pos (norm_pos_iff.mpr hw) a
    refine Integrable.congr ?_ (show f u =ᵐ[μ] _ from hf u hu).symm
    refine Integrable.mono' (hKi.div_const (‖wt u‖ ^ a * c ^ N)) ?_ ?_
    · exact (hAmeas u hu).div₀ ((aestronglyMeasurable_const.mul ((hVc u).pow N)))
    · filter_upwards [hV] with x hx
      have hcx := hx u hu
      rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hc.trans_le hcx)]
      exact div_le_div₀ (hK0 x) (hnormA x u hu) (mul_pos hwn (pow_pos hc N))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hcx N) hwn.le)
  refine ⟨hfi, ?_⟩
  -- the even part as `u² B`
  set B : ℝ → ι → ℂ := fun u x =>
    ∑ j ∈ Finset.range (D + 1), (interp D A x).coeff j * evenCoeff j u with hB
  have h0 : ∀ᵐ x ∂μ, (interp D A x).coeff 0 = 0 := by
    filter_upwards [hA0] with x hx
    have := hA.eq_interp x 0 ⟨by norm_num, by norm_num⟩
    rw [hx, ofReal_zero, ← coeff_zero_eq_eval_zero] at this
    exact this.symm
  -- off a null set, for `0 < |u| < 1`, the symmetrized integrand is `B / (wᵃ Vᴺ)`
  have hsym : ∀ u ∈ Ioo (-1 : ℝ) 1, u ≠ 0 →
      ((∫ x, f u x ∂μ) + ∫ x, f (-u) x ∂μ) / (2 * (u : ℂ) ^ 2) =
        ∫ x, B u x / (wt u ^ a * (V x u : ℂ) ^ N) ∂μ := fun u hu hu0 => by
    have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    rw [← integral_add (hfi u hu) (hfi (-u) hu'), div_eq_mul_inv, mul_comm,
      ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hf u hu, hf (-u) hu', hVeven, h0] with x hx hx' hev hx0
    rw [hx, hx', hev, wt_neg]
    have hsum : A x u + A x (-u) = 2 * (u : ℂ) ^ 2 * B u x := by
      rw [hAeq x u hu, hAeq x (-u) hu', ← Finset.sum_add_distrib]
      simp only [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_add, pow_add_neg_pow]
      split_ifs with hj
      · subst hj
        rw [hx0]
        ring
      · ring
    have hu2 : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.mpr hu0)
    have h2u : (2 * (u : ℂ) ^ 2) ≠ 0 := mul_ne_zero two_ne_zero hu2
    rw [← add_div, hsum, mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ h2u, one_mul]
  -- dominated convergence
  have hlim : Tendsto (fun u => ∫ x, B u x / (wt u ^ a * (V x u : ℂ) ^ N) ∂μ) (𝓝[≠] 0)
      (𝓝 (∫ x, (interp D A x).coeff 2 / (V x 0 : ℂ) ^ N ∂μ)) := by
    have hnear : ∀ᶠ u in 𝓝[≠] (0 : ℝ), |u| ≤ 1 / 2 := by
      refine nhdsWithin_le_nhds ?_
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)]
        with u hu
      simpa [Real.dist_eq] using hu
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => K x / ((3 / 4 : ℝ) ^ a * c ^ N)) ?_ ?_ (hKi.div_const _) ?_
    · refine Eventually.of_forall fun u => ?_
      refine AEStronglyMeasurable.div₀ ?_ (aestronglyMeasurable_const.mul ((hVc u).pow N))
      exact (integrable_finsetSum _ fun j _ => (hcf j).mul_const _).aestronglyMeasurable
    · filter_upwards [hnear] with u hu
      have hu1 : u ∈ Ioo (-1 : ℝ) 1 := by
        rw [abs_le] at hu
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      filter_upwards [hV] with x hx
      have hcx := hx u hu1
      have hBn : ‖B u x‖ ≤ K x := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (norm_evenCoeff_le j (hu.trans (by norm_num)))
      have hw := norm_wt_ge hu
      rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hc.trans_le hcx)]
      exact div_le_div₀ (hK0 x) hBn (by positivity)
        (mul_le_mul (pow_le_pow_left₀ (by norm_num) hw a) (pow_le_pow_left₀ hc.le hcx N)
          (by positivity) (by positivity))
    · filter_upwards [hVcont, hV] with x hxc hxV
      have hV0 : (V x 0 : ℂ) ≠ 0 :=
        ofReal_ne_zero.mpr (hc.trans_le (hxV 0 ⟨by norm_num, by norm_num⟩)).ne'
      have hBl : Tendsto (fun u => B u x) (𝓝 0) (𝓝 ((interp D A x).coeff 2)) := by
        have h := tendsto_finsetSum (Finset.range (D + 1)) fun j _ =>
          (tendsto_evenCoeff j).const_mul ((interp D A x).coeff j)
        convert h using 2
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
        split_ifs with hD
        · rfl
        · symm
          exact (coeff_eq_zero_of_natDegree_lt
            ((natDegree_interp_le x).trans_lt (show D < 2 by omega))).symm
      have hwl : Tendsto wt (𝓝 0) (𝓝 1) := by
        have : Continuous wt := by unfold wt; fun_prop
        simpa [wt_zero] using this.tendsto 0
      have hVl : Tendsto (fun u => ((V x u : ℝ) : ℂ)) (𝓝 0) (𝓝 (V x 0 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp hxc.tendsto
      have h := hBl.div ((hwl.pow a).mul (hVl.pow N)) (by simpa using pow_ne_zero N hV0)
      have h2 : Tendsto (fun u => B u x / (wt u ^ a * (V x u : ℂ) ^ N)) (𝓝 0)
          (𝓝 ((interp D A x).coeff 2 / (1 ^ a * (V x 0 : ℂ) ^ N))) := h
      rw [one_pow, one_mul] at h2
      exact h2.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hnear : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 ∧ u ≠ 0 :=
    h1.and self_mem_nhdsWithin
  filter_upwards [hnear] with u hu
  exact (hsym u hu.1 hu.2).symm

end EvenLimit

end QED.TwoLoop.PauliZeroLimit

end
