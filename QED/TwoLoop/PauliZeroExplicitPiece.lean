/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroExplicitQuartic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The explicit second-order limit of a projected parametric value

Part of the explicit form of the `q² → 0⁺` limit of obligation O2-22
(`docs/TWO-LOOP-DERIVATION.md`, section 5.4). `QED.TwoLoop.PauliZeroLimit.tendsto_piece` proves
that the even part over `u²` of a projected parametric value along the curve converges; this file
identifies the limit (`tendsto_piece_explicit`):

`(S(u) + S(-u)) / (2u²) → ∫_Δ c₂[N(x, ·)] / V(x, 0)^{m-3} dx`,

where `S(u) = ∑ⱼ ω(u, j) v(u, j)`, `N(x, u) = ∑ⱼ ω(u, j) (-π⁴) paramNumOf (F u j) α p(u) M x` is
the projected parametric numerator along the curve, `V(x, 0)` is `V` at `u = 0` (that is, at
`q = 0`), and `c₂[g] = secondCoeff g` is the second-order coefficient of `g` at `0`:
`lim_{u → 0} (g(u) + g(-u) - 2 g(0)) / (2u²)`, which is `g''(0)/2` for `g` twice differentiable.

* `secondCoeff`, `tendsto_secondCoeff_of_poly`, `secondCoeff_eq_coeff`: if `(1 - u²)ᵃ g(u)` agrees
  on `(-1, 1)` with a polynomial `P` with `P(0) = 0`, then the second-order quotient of `g`
  converges to the coefficient of `u²` of `P`, and `secondCoeff g` is that coefficient.
* `tendsto_piece_explicit`: the explicit limit.

The numerator `paramNumOf (F u j)` is canonical: it depends only on the numerator function `F u j`
(`QED.TwoLoop.PauliZeroExplicit.paramNumOf_eq`), so `N(x, u)` is an explicit function of the
Feynman parameters `x` and the curve parameter `u`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.PauliZeroExplicit

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### The second-order coefficient -/

/-- **The second-order coefficient of `g` at `0`**: the limit of `(g(u) + g(-u) - 2 g(0)) / (2u²)`
as `u → 0`, `u ≠ 0`. For `g` twice differentiable at `0` this is `g''(0)/2`; for `g` a polynomial
divided by a power of `1 - u²` it is the Taylor coefficient of `u²` (`secondCoeff_eq_coeff`). -/
noncomputable def secondCoeff (g : ℝ → ℂ) : ℂ :=
  limUnder (𝓝[≠] (0 : ℝ)) fun u => (g u + g (-u) - 2 * g 0) / (2 * (u : ℂ) ^ 2)

theorem tendsto_secondCoeff_of_poly {g : ℝ → ℂ} {a : ℕ} {P : ℂ[X]}
    (hg : ∀ u ∈ Ioo (-1 : ℝ) 1, wt u ^ a * g u = P.eval (u : ℂ)) (h0 : P.coeff 0 = 0) :
    Tendsto (fun u => (g u + g (-u) - 2 * g 0) / (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0)
      (𝓝 (P.coeff 2)) := by
  set N := P.natDegree
  set B : ℝ → ℂ := fun u => ∑ j ∈ Finset.range (N + 1), P.coeff j * evenCoeff j u with hB_def
  have hB : Tendsto B (𝓝 0) (𝓝 (P.coeff 2)) := by
    have h := tendsto_finsetSum (Finset.range (N + 1)) fun j _ =>
      (tendsto_evenCoeff j).const_mul (P.coeff j)
    convert h using 2
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hN
    · rfl
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hw : Tendsto (fun u => wt u ^ a) (𝓝 0) (𝓝 1) := by
    have : Continuous wt := by unfold wt; fun_prop
    simpa [wt_zero] using (this.tendsto 0).pow a
  have hlim := hB.div hw one_ne_zero
  rw [div_one] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h1.and self_mem_nhdsWithin] with u ⟨hu, hu0⟩
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hw0 : wt u ^ a ≠ 0 := pow_ne_zero a (wt_ne_zero hu)
  have hg0 : g 0 = 0 := by
    have := hg 0 ⟨by norm_num, by norm_num⟩
    rw [wt_zero, one_pow, one_mul, ofReal_zero, ← coeff_zero_eq_eval_zero, h0] at this
    exact this
  have hgu : g u = P.eval (u : ℂ) / wt u ^ a := by
    rw [← hg u hu, mul_div_cancel_left₀ _ hw0]
  have hgnu : g (-u) = P.eval ((-u : ℝ) : ℂ) / wt u ^ a := by
    rw [← hg (-u) hu', wt_neg, mul_div_cancel_left₀ _ hw0]
  have hsum : P.eval (u : ℂ) + P.eval ((-u : ℝ) : ℂ) = 2 * (u : ℂ) ^ 2 * B u := by
    rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_add_distrib, hB_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_add, pow_add_neg_pow]
    split_ifs with hj
    · subst hj
      rw [h0]
      ring
    · ring
  have hu2 : (2 * (u : ℂ) ^ 2) ≠ 0 :=
    mul_ne_zero two_ne_zero (pow_ne_zero 2 (ofReal_ne_zero.mpr hu0))
  have hu0' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0
  rw [hgu, hgnu, hg0, mul_zero, sub_zero, ← add_div, hsum, Pi.div_apply]
  field_simp

theorem secondCoeff_eq_coeff {g : ℝ → ℂ} {a : ℕ} {P : ℂ[X]}
    (hg : ∀ u ∈ Ioo (-1 : ℝ) 1, wt u ^ a * g u = P.eval (u : ℂ)) (h0 : P.coeff 0 = 0) :
    secondCoeff g = P.coeff 2 :=
  (tendsto_secondCoeff_of_poly hg h0).limUnder_eq

/-! ### The explicit limit of one piece -/

/-- The projected parametric numerator along the curve:
`N(x, u) = ∑ⱼ ω(u, j) (-π⁴) paramNumOf (F u j) α p(u) M x`. -/
noncomputable def projNum (C : CurveData) {J : Type*} [Fintype J]
    (F : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ) (ω : ℝ → J → ℂ) (x : Fin C.m → ℝ) (u : ℝ) : ℂ :=
  ∑ j, ω u j * (-((π : ℂ) ^ 4) * paramNumOf (F u j) C.α (C.mom u) C.M x)

/-- **The explicit second-order limit of a projected parametric value along a curve.** Under the
hypotheses of `QED.TwoLoop.PauliZeroLimit.tendsto_piece`, the even part of
`S(u) = ∑ⱼ ω u j v u j` divided by `u²` converges to
`∫_Δ c₂[N(x, ·)] / V(x, 0)^{m-3} dx`, with `N = projNum C F ω` the projected parametric numerator
along the curve and `c₂ = secondCoeff`. -/
theorem tendsto_piece_explicit (C : CurveData) {J : Type*} [Fintype J] {D n r Dω : ℕ}
    (F : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hFpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * F u j ℓ)
    (hFq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = F u j)
    (hFB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (F u j))
    (v : ℝ → J → ℂ)
    (hv : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) j, IsParamValue (C.toParamData hu) (F u j) (v u j))
    (ω : ℝ → J → ℂ) (hω : ∀ j, IsUPoly (ι := Fin C.m → ℝ) Dω fun _ u => wt u ^ r * ω u j)
    (hω0 : ∀ Y : J → ℂ, ∑ j, ω 0 j * Y j = 0) :
    Tendsto (fun u => ((∑ j, ω u j * v u j) + ∑ j, ω (-u) j * v (-u) j) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 (∫ x in simplexSet C.m,
        secondCoeff (projNum C F ω x) / ((C.vfun x 0 : ℝ) : ℂ) ^ (C.m - 3))) := by
  classical
  have hnode : ∀ k : Fin (D + 1), node D k ∈ Ioo (-1 : ℝ) 1 := node_mem D
  choose Qk hQk using fun j k => hFq (node D k) (hnode k) j
  have hBk : ∀ j k, RefinedBound C.α C.E 4 (Qk j k).eval := fun j k => by
    rw [hQk]
    exact hFB _ (hnode k) j
  -- the integrand and its numerator
  set f : ℝ → (Fin C.m → ℝ) → ℂ := fun u x => ∑ j, ω u j * (-((π : ℂ) ^ 4) *
    ∑ k, lam D n u k * paramIntegrand (Qk j k) C.α (C.mom u) C.M 0 x) with hf_def
  set A : (Fin C.m → ℝ) → ℝ → ℂ := fun x u => ∑ j, (wt u ^ r * ω u j) * (-((π : ℂ) ^ 4) *
    ∑ k, (wt (node D k) ^ n * (lbasis D k).eval (u : ℂ)) *
      (wt u ^ 4 * paramNum (Qk j k) C.α (C.mom u) C.M x)) with hA_def
  have hA : IsUPoly (Dω + (D + 8)) A :=
    IsUPoly.sum _ fun j _ => (hω j).mul (IsUPoly.const_mul _ (IsUPoly.sum _ fun k _ =>
      ((isUPoly_lbasis D k).const_mul _).mul (isUPoly_paramNum (Qk j k) C.α C.M C.mom C.hmom)))
  have hAi : ∀ t, Integrable (fun x => A x (node (Dω + (D + 8)) t))
      (volume.restrict (simplexSet C.m)) := fun t => by
    refine integrable_finsetSum _ fun j _ => Integrable.const_mul ?_ _
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun k _ => Integrable.const_mul ?_ _
    exact (integrableOn_paramNum (Qk j k) C.α _ C.M C.hm C.hcrit (hBk j k)).const_mul _
  have hA0 : ∀ x, A x 0 = 0 := fun x => by
    simp only [hA_def, wt_zero, one_pow, one_mul]
    exact hω0 _
  have hf : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ᵐ x ∂(volume.restrict (simplexSet C.m)),
      f u x = A x u / (wt u ^ (r + n + 4) * ((C.vfun x u : ℝ) : ℂ) ^ (C.m - 3)) := by
    intro u hu
    filter_upwards [C.ae_le_vfun] with x hx
    have hV0 : C.vfun x u ≠ 0 := (C.hc.trans_le (hx u hu)).ne'
    have hV0' : ((C.vfun x u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hV0
    have hw := wt_ne_zero hu
    simp only [hf_def, hA_def, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [paramIntegrand_zero_eq (Qk j k) C.α (C.mom u) C.M (by have := C.hm; omega) hV0]
    simp only [lam, CurveData.vfun] at hV0' ⊢
    field_simp
    ring
  obtain ⟨-, hlim⟩ := tendsto_even_div_sq (μ := volume.restrict (simplexSet C.m)) (f := f)
    (a := r + n + 4) (N := C.m - 3) hA hAi (ae_of_all _ hA0) C.hc C.ae_le_vfun
    (ae_of_all _ fun x u => C.hVeven u _) (ae_of_all _ C.continuousAt_vfun)
    (fun u => (C.measurable_vfun u).aestronglyMeasurable) hf
  -- the projected values as integrals of `f`
  have hS : ∀ u ∈ Ioo (-1 : ℝ) 1, ∑ j, ω u j * v u j = ∫ x in simplexSet C.m, f u x := by
    intro u hu
    have hI : ∀ j k, IntegrableOn (paramIntegrand (Qk j k) C.α (C.mom u) C.M 0)
        (simplexSet C.m) := fun j k =>
      integrableOn_paramIntegrand_zero (Qk j k) C.α (C.mom u) C.M C.hm C.hcrit (hBk j k) C.hc
        (C.hV u hu)
    have hvj : ∀ j, v u j = -((π : ℂ) ^ 4) * ∫ x in simplexSet C.m,
        ∑ k, lam D n u k * paramIntegrand (Qk j k) C.α (C.mom u) C.M 0 x := fun j => by
      have h' : IsParamValue (C.toParamData hu) (F u j) (-((π : ℂ) ^ 4) *
          ∫ x in simplexSet C.m, paramIntegrand (jointQuartic D n (Qk j) u) C.α (C.mom u) C.M 0 x) :=
        ⟨jointQuartic D n (Qk j) u, eval_jointQuartic (hFpoly j) (hQk j) hu, hFB u hu j, rfl⟩
      rw [(hv u hu j).unique h', jointQuartic]
      simp only [paramIntegrand_qsum]
    simp only [hvj, hf_def]
    rw [integral_finsetSum _ fun j _ => (((integrable_finsetSum _ fun k _ =>
      (hI j k).const_mul _).const_mul _).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_const_mul]
  -- the numerator `A` is `(1 - u²)^{r+n+4}` times the canonical projected numerator
  have hAN : ∀ x, ∀ u ∈ Ioo (-1 : ℝ) 1, A x u = wt u ^ (r + n + 4) * projNum C F ω x u := by
    intro x u hu
    have hw : wt u ^ n ≠ 0 := pow_ne_zero n (wt_ne_zero hu)
    simp only [hA_def, projNum]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [paramNumOf_eq (eval_jointQuartic (hFpoly j) (hQk j) hu), jointQuartic, paramNum_qsum]
    have e1 : ∑ k, wt (node D k) ^ n * (lbasis D k).eval (u : ℂ) *
        (wt u ^ 4 * paramNum (Qk j k) C.α (C.mom u) C.M x) =
        wt u ^ 4 * ∑ k, wt (node D k) ^ n * (lbasis D k).eval (u : ℂ) *
          paramNum (Qk j k) C.α (C.mom u) C.M x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, lam D n u k * paramNum (Qk j k) C.α (C.mom u) C.M x =
        (wt u ^ n)⁻¹ * ∑ k, wt (node D k) ^ n * (lbasis D k).eval (u : ℂ) *
          paramNum (Qk j k) C.α (C.mom u) C.M x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [lam]; ring
    rw [e1, e2]
    field_simp
    ring
  have hval : ∫ x in simplexSet C.m, (interp (Dω + (D + 8)) A x).coeff 2 /
        ((C.vfun x 0 : ℝ) : ℂ) ^ (C.m - 3) =
      ∫ x in simplexSet C.m, secondCoeff (projNum C F ω x) /
        ((C.vfun x 0 : ℝ) : ℂ) ^ (C.m - 3) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have h0 : (interp (Dω + (D + 8)) A x).coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero, ← ofReal_zero, ← hA.eq_interp x 0 ⟨by norm_num, by norm_num⟩,
        hA0, ofReal_zero]
    have hg : ∀ u ∈ Ioo (-1 : ℝ) 1, wt u ^ (r + n + 4) * projNum C F ω x u =
        (interp (Dω + (D + 8)) A x).eval (u : ℂ) := fun u hu => by
      rw [← hAN x u hu, hA.eq_interp x u hu]
    dsimp only
    rw [secondCoeff_eq_coeff hg h0]
  rw [← hval]
  refine hlim.congr' ?_
  have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h1] with u hu
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rw [hS u hu, hS (-u) hu']

end QED.TwoLoop.PauliZeroExplicit

end
