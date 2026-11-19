/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2RayCore

/-!
# The parametric derivative identity in the reparametrized variable

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A2. Pointwise in the Feynman point:

* `hasDerivAt_paramIntegrand_tpar`: if the line momenta are `p + tpar(u) q` on `(-1, 1)` and the
  numerators `J u` form, in the variable `s = tpar u`, a differentiable path `s ↦ J (upar s)`, the
  derivative at `u = 0` of the parametric integrand is that of the parametric derivative identity
  (`hasDerivAt_paramIntegrand_line`) at `s = 0`, with the combined insertion split into lines
  (`ehat_mulLin_sum`);
* `differentiableAt_lam_upar`: the interpolation weights `lam D n u k` of a joint quartic are
  differentiable in `s` at `0` along `u = upar s`.
-/

@[expose] public section

open Complex Filter Topology Set

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 (tpar upar upar_mem tpar_upar differentiableAt_upar)
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexPoint)

/-- **The parametric derivative identity along `p + tpar(u) q`**, at `u = 0`, with the combined
insertion split into lines. -/
theorem hasDerivAt_paramIntegrand_tpar (n : ℕ) {J : ℝ → LoopQuartic} {J' : LoopQuartic}
    (hJ : HasQDerivAt (fun s => J (upar s)) J' 0) (hq : (J 0).quart = 0)
    (α : Fin (n + 6 + 1) → Fin 2 → ℝ) {mom : ℝ → Fin (n + 6 + 1) → Fin 4 → ℝ}
    (p q : Fin (n + 6 + 1) → Fin 4 → ℝ) (hmom : ∀ u ∈ Ioo (-1 : ℝ) 1, mom u = p + tpar u • q)
    (M : Fin (n + 6 + 1) → ℝ) (x : Fin (n + 6) → ℝ)
    (hW : ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I ≠ 0) :
    HasDerivAt (fun u => paramIntegrand (J u) α (mom u) M 0 x)
      (paramIntegrand J' α p M 0 x - ∑ i, (simplexPoint x i : ℂ) *
        paramAt (n + 7) (Cubic.mulLin (J 0) (dLineC (p i) (q i)) (dLineL (α i) (q i))) α p M 0
          (simplexPoint x)) 0 := by
  have hup : upar 0 = 0 := by simp [upar]
  have hq' : (J (upar 0)).quart = 0 := by rw [hup]; exact hq
  have hW' : ((symanzikV α (p + (0 : ℝ) • q) M (simplexPoint x) : ℝ) : ℂ) -
      ((0 : ℝ) : ℂ) * I ≠ 0 := by
    rwa [zero_smul, add_zero]
  have h := hasDerivAt_paramIntegrand_line n hJ hq' α p q M 0 x hW'
  simp only [zero_smul, add_zero, hup] at h
  refine hasDerivAt_of_eq_comp_tpar (φ := fun s => paramIntegrand (J (upar s)) α (p + s • q) M 0 x)
    (fun u hu => ?_) ?_
  · simp only [upar_tpar hu, hmom u hu]
  · convert h using 1
    rw [ehat_mulLin_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [paramAt]
    ring

theorem differentiableAt_lam_upar (D n : ℕ) (k : Fin (D + 1)) :
    DifferentiableAt ℝ (fun s => lam D n (upar s) k) 0 := by
  have hup : upar 0 = 0 := by simp [upar]
  have hwt : DifferentiableAt ℝ (fun u : ℝ => wt u) 0 :=
    ((((hasDerivAt_id' (((0 : ℝ)) : ℂ)).fun_pow 2).const_sub 1).comp_ofReal).differentiableAt
  have hb : ∀ u : ℝ, DifferentiableAt ℝ (fun u : ℝ => (lbasis D k).eval (u : ℂ)) u := fun u =>
    ((Polynomial.hasDerivAt (lbasis D k) (u : ℂ)).comp_ofReal).differentiableAt
  have hl : DifferentiableAt ℝ (fun u => lam D n u k) (upar 0) := by
    rw [hup]
    unfold lam
    refine ((hwt.pow n).inv (by simp [wt_zero])).mul
      ((differentiableAt_const _).mul (hb 0))
  exact hl.comp (0 : ℝ) differentiableAt_upar

end QED.GradedProof.WI2

end
