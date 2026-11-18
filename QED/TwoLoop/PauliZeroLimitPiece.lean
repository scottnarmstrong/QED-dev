/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroLimitParam
public import QED.TwoLoop.LimitCovarianceQuartic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The second-order limit of a projected parametric value along a curve

Part of obligation O2-22 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). This file combines the
analytic core (`QED/TwoLoop/PauliZeroLimitCore.lean`) with the parametric integrand along a curve
(`QED/TwoLoop/PauliZeroLimitParam.lean`) for one parametric representation ("piece").

**Data.** `CurveData`: a loop matrix `α`, masses `M`, numerator lines `E` with the criterion,
external line momenta `mom u` for `u ∈ (-1, 1)` with `(1 - u²) mom u` polynomial of degree at most
`2`, a lower bound `V ≥ c > 0` uniform in `u`, and `V(mom (-u)) = V(mom u)`.

**Joint numerators without joint coefficients.** A family of numerators `F u` such that, at each
fixed loop momentum, `(1 - u²)ⁿ F u` is polynomial in `u` of degree at most `D`, equals at every
`u` the quartic `∑ₖ λₖ(u) Qₖ` (`jointQuartic`), where `Qₖ` represents `F` at the node `k/(D+1)`
and `λₖ(u) = (1 - u²)⁻ⁿ (1 - tₖ²)ⁿ ℓₖ(u)` with `ℓₖ` the Lagrange basis (`eval_jointQuartic`). So
the numerator quartics need only exist at fixed external momenta (`exists_loopQuartic`); the
dependence of their coefficients on `u` is supplied by interpolation.

**Result.** `tendsto_piece`: for such numerators `F u j` with parametric values `v u j`
(indexed by a finite type `J`) and weights `ω u j` with `(1 - u²)ʳ ω u j` polynomial and
`∑ⱼ ω 0 j Y j = 0` for every `Y`, the even part of `S(u) = ∑ⱼ ω u j v u j` divided by `u²` has a
limit as `u → 0`, `u ≠ 0`. In the application `ω` is the Pauli numerator of the projector, which
vanishes identically at `q = 0`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.PauliZeroLimit

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### Joint quartics by interpolation -/

/-- The Lagrange basis at the nodes `k / (D + 1)`. -/
noncomputable def lbasis (D : ℕ) (k : Fin (D + 1)) : ℂ[X] :=
  Lagrange.basis Finset.univ (fun k : Fin (D + 1) => ((node D k : ℝ) : ℂ)) k

theorem natDegree_lbasis_le (D : ℕ) (k : Fin (D + 1)) : (lbasis D k).natDegree ≤ D := by
  unfold lbasis
  rw [Lagrange.natDegree_basis (node_injOn D) (Finset.mem_univ k), Finset.card_univ,
    Fintype.card_fin]
  omega

theorem isUPoly_lbasis {ι : Type*} (D : ℕ) (k : Fin (D + 1)) :
    IsUPoly (ι := ι) D fun _ u => (lbasis D k).eval (u : ℂ) := fun _ =>
  ⟨lbasis D k, natDegree_lbasis_le D k, fun _ _ => rfl⟩

theorem interp_eval_eq {ι : Type*} (D : ℕ) (f : ι → ℝ → ℂ) (x : ι) (z : ℂ) :
    (interp D f x).eval z = ∑ k, f x (node D k) * (lbasis D k).eval z := by
  simp only [interp, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, lbasis]

/-- The interpolation weights `λₖ(u) = (1 - u²)⁻ⁿ (1 - tₖ²)ⁿ ℓₖ(u)`. -/
noncomputable def lam (D n : ℕ) (u : ℝ) (k : Fin (D + 1)) : ℂ :=
  (wt u ^ n)⁻¹ * (wt (node D k) ^ n * (lbasis D k).eval (u : ℂ))

/-- The joint quartic `∑ₖ λₖ(u) Qₖ`. -/
noncomputable def jointQuartic (D n : ℕ) (Qk : Fin (D + 1) → LoopQuartic) (u : ℝ) : LoopQuartic :=
  qsum Finset.univ (lam D n u) Qk

theorem wt_ne_zero {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : wt u ≠ 0 := by
  have e : wt u = ((1 - u ^ 2 : ℝ) : ℂ) := by simp [wt]
  rw [e, ofReal_ne_zero]
  nlinarith [hu.1, hu.2]

/-- **The joint quartic represents the numerator at every `u ∈ (-1, 1)`.** -/
theorem eval_jointQuartic {D n : ℕ} {F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hF : IsUPoly D fun ℓ u => wt u ^ n * F u ℓ) {Qk : Fin (D + 1) → LoopQuartic}
    (hQk : ∀ k, (Qk k).eval = F (node D k)) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    (jointQuartic D n Qk u).eval = F u := by
  funext ℓ
  have h := hF.eq_interp ℓ u hu
  rw [interp_eval_eq] at h
  have hw : wt u ^ n ≠ 0 := pow_ne_zero n (wt_ne_zero hu)
  rw [jointQuartic, eval_qsum]
  simp only [hQk, lam]
  calc ∑ k, (wt u ^ n)⁻¹ * (wt (node D k) ^ n * (lbasis D k).eval (u : ℂ)) * F (node D k) ℓ
      = (wt u ^ n)⁻¹ * ∑ k, wt (node D k) ^ n * F (node D k) ℓ * (lbasis D k).eval (u : ℂ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = (wt u ^ n)⁻¹ * (wt u ^ n * F u ℓ) := by rw [h]
    _ = F u ℓ := by rw [← mul_assoc, inv_mul_cancel₀ hw, one_mul]

/-! ### Data along a curve -/

/-- A parametric representation along a curve of external momenta, `u ∈ (-1, 1)`. -/
structure CurveData where
  /-- The number of lines minus one. -/
  m : ℕ
  /-- The loop matrix. -/
  α : Fin (m + 1) → Fin 2 → ℝ
  /-- The external line momenta along the curve. -/
  mom : ℝ → Fin (m + 1) → Fin 4 → ℝ
  /-- The masses. -/
  M : Fin (m + 1) → ℝ
  /-- The numerator lines. -/
  E : Finset (Fin (m + 1))
  hm : 7 ≤ m
  hcrit : NoSubdivergenceRefined 2 E α
  /-- A positive lower bound for `V`, uniform along the curve. -/
  c : ℝ
  hc : 0 < c
  hV : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
    symanzikU α z ≠ 0 → c ≤ symanzikV α (mom u) M z
  hmom : ∀ i μ, IsUPoly (ι := Fin m → ℝ) 2 fun _ u => wt u * ((mom u i μ : ℝ) : ℂ)
  hVeven : ∀ u z, symanzikV α (mom (-u)) M z = symanzikV α (mom u) M z

namespace CurveData

variable (C : CurveData)

/-- The parametric data at a point of the curve. -/
noncomputable def toParamData {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : ParamData where
  m := C.m
  α := C.α
  p := C.mom u
  M := C.M
  E := C.E
  hm := C.hm
  hcrit := C.hcrit
  c := C.c
  hc := C.hc
  hV := C.hV u hu

theorem hspan : ∃ i j, C.α i 0 * C.α j 1 - C.α i 1 * C.α j 0 ≠ 0 :=
  NoSubdivergence.span (α := C.α) fun i => by have := C.hcrit.noSubdivergenceOfOrder i; omega

/-- `V` along the curve, at the simplex point of `x`. -/
noncomputable def vfun (x : Fin C.m → ℝ) (u : ℝ) : ℝ :=
  symanzikV C.α (C.mom u) C.M (simplexPoint x)

theorem ae_le_vfun : ∀ᵐ x ∂(volume.restrict (simplexSet C.m)),
    ∀ u ∈ Ioo (-1 : ℝ) 1, C.c ≤ C.vfun x u := by
  filter_upwards [ae_posDef C.α (by have := C.hm; omega) C.hspan] with x ⟨hxS, hPD⟩
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  exact fun u hu => C.hV u hu _ hz.1 hz.2 hPD.det_pos.ne'

theorem continuousAt_vfun (x : Fin C.m → ℝ) : ContinuousAt (C.vfun x) 0 := by
  obtain ⟨P, -, hP⟩ := isUPoly_symanzikV C.α C.mom C.M (fun x => simplexPoint x) C.hmom x
  -- near `0`, `V = P(u) / (1 - u²)²`
  have hev : ∀ᶠ u in 𝓝 (0 : ℝ), ((C.vfun x u : ℝ) : ℂ) = P.eval (u : ℂ) / wt u ^ 2 := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
      with u hu
    rw [← hP u hu, mul_div_cancel_left₀ _ (pow_ne_zero 2 (wt_ne_zero hu))]
    rfl
  have hc : ContinuousAt (fun u : ℝ => P.eval (u : ℂ) / wt u ^ 2) 0 := by
    refine ContinuousAt.div (P.continuous.comp Complex.continuous_ofReal).continuousAt
      (by unfold wt; fun_prop) ?_
    simp [wt_zero]
  have h2 : ContinuousAt (fun u => ((C.vfun x u : ℝ) : ℂ)) 0 :=
    hc.congr (by filter_upwards [hev] with u hu; exact hu.symm)
  have h3 := (Complex.continuous_re.continuousAt).comp h2
  convert h3 using 1
  funext u
  simp

theorem measurable_vfun (u : ℝ) : Measurable fun x => C.vfun x u :=
  (measurable_symanzikV C.α (C.mom u) C.M).comp continuous_simplexPoint'.measurable

end CurveData

/-! ### The second-order limit of one piece -/

/-- **The second-order limit of a projected parametric value along a curve.** Let `F u j`
(`j` in a finite type) be numerators with `(1 - u²)ⁿ F u j` polynomial of degree at most `D` in
`u` at every loop momentum, each `F u j` a quartic with the refined bound for `u ∈ (-1, 1)`, with
parametric values `v u j` along the curve; let `ω u j` be weights with `(1 - u²)ʳ ω u j`
polynomial and `∑ⱼ ω 0 j Y j = 0` for every `Y`. Then
`(S(u) + S(-u)) / (2u²)`, `S(u) = ∑ⱼ ω u j v u j`, has a limit as `u → 0`, `u ≠ 0`. -/
theorem tendsto_piece (C : CurveData) {J : Type*} [Fintype J] {D n r Dω : ℕ}
    (F : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hFpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * F u j ℓ)
    (hFq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = F u j)
    (hFB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (F u j))
    (v : ℝ → J → ℂ)
    (hv : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) j, IsParamValue (C.toParamData hu) (F u j) (v u j))
    (ω : ℝ → J → ℂ) (hω : ∀ j, IsUPoly (ι := Fin C.m → ℝ) Dω fun _ u => wt u ^ r * ω u j)
    (hω0 : ∀ Y : J → ℂ, ∑ j, ω 0 j * Y j = 0) :
    ∃ L, Tendsto (fun u => ((∑ j, ω u j * v u j) + ∑ j, ω (-u) j * v (-u) j) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 L) := by
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
  refine ⟨_, hlim.congr' ?_⟩
  have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h1] with u hu
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rw [hS u hu, hS (-u) hu']

end QED.TwoLoop.PauliZeroLimit

end
