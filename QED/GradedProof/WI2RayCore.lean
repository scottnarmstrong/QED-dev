/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Dbl
public import QED.GradedProof.SE2DiffPiece

/-!
# The parametrization of a line, and paths of interpolated numerators

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A2. The reparametrization `t = t₀ + tpar u`, `tpar u = u / (1 - u²)`, of
`QED.GradedProof.SE2.SEPiece.differentiableAt_line`:

* `hasDerivAt_tpar`, `hasDerivAt_upar`: both `tpar` and its inverse `upar` have derivative `1`
  at `0`;
* `upar_tpar`: `upar` inverts `tpar` on `(-1, 1)` (`tpar` is injective there);
* `hasDerivAt_of_eq_comp_tpar`: a function equal on `(-1, 1)` to `φ ∘ tpar` has at `0` the
  derivative of `φ` at `0`;
* `hasQDerivAt_qsum`: a combination of fixed numerators with differentiable coefficients is a
  differentiable path of numerators.
-/

@[expose] public section

open Complex Filter Topology Set

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 (tpar upar upar_mem tpar_upar)
open QED.Integration.TwoLoop QED.TwoLoop.LimitCovariance

theorem hasDerivAt_tpar : HasDerivAt tpar 1 0 := by
  have h := (hasDerivAt_id' (0 : ℝ)).fun_div ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_sub
    ((hasDerivAt_id' (0 : ℝ)).fun_pow 2)) (by norm_num)
  unfold tpar
  convert h using 1
  · norm_num

theorem hasDerivAt_upar : HasDerivAt upar 1 0 := by
  have h2 : HasDerivAt (fun t : ℝ => 1 + 4 * t ^ 2) 0 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).fun_pow 2).const_mul 4).const_add 1
    convert this using 1
    · norm_num
  have h3 := h2.sqrt (by norm_num)
  have h := ((hasDerivAt_id' (0 : ℝ)).const_mul 2).fun_div (h3.const_add 1)
    (by positivity)
  unfold upar
  convert h using 1
  · norm_num

theorem tpar_injOn {u v : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hv : v ∈ Ioo (-1 : ℝ) 1)
    (h : tpar u = tpar v) : u = v := by
  unfold tpar at h
  have h1 : 1 - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  have h2 : 1 - v ^ 2 ≠ 0 := by nlinarith [hv.1, hv.2]
  rw [div_eq_div_iff h1 h2] at h
  have h3 : 0 < 1 + u * v := by
    nlinarith [mul_pos (sub_pos.2 hu.2) (sub_pos.2 hv.2),
      mul_pos (neg_lt_iff_pos_add.mp hu.1) (neg_lt_iff_pos_add.mp hv.1)]
  have h4 : (u - v) * (1 + u * v) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h4 with h5 | h5
  · linarith
  · linarith

theorem upar_tpar {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : upar (tpar u) = u :=
  tpar_injOn (upar_mem _) hu (tpar_upar _)

theorem tpar_zero : tpar 0 = 0 := by simp [tpar]

/-- A function equal on `(-1, 1)` to `φ ∘ tpar` has at `0` the derivative of `φ` at `0`. -/
theorem hasDerivAt_of_eq_comp_tpar {f φ : ℝ → ℂ} {φ' : ℂ}
    (h : ∀ u ∈ Ioo (-1 : ℝ) 1, f u = φ (tpar u)) (hφ : HasDerivAt φ φ' 0) :
    HasDerivAt f φ' 0 := by
  have hφ' : HasDerivAt φ φ' (tpar 0) := by rw [tpar_zero]; exact hφ
  have hc := hφ'.scomp (0 : ℝ) hasDerivAt_tpar
  rw [one_smul] at hc
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
    with u hu
  exact h u hu

/-- **A combination of fixed numerators with differentiable coefficients is a differentiable
path.** -/
theorem hasQDerivAt_qsum {ι : Type*} (s : Finset ι) {c : ι → ℝ → ℂ} {c' : ι → ℂ} {t : ℝ}
    (hc : ∀ k ∈ s, HasDerivAt (c k) (c' k) t) (Q : ι → LoopQuartic) :
    HasQDerivAt (fun u => qsum s (fun k => c k u) Q) (qsum s c' Q) t := by
  refine ⟨?_, fun a => ?_, fun a b => ?_, fun a b e => ?_, fun a b e d => ?_⟩ <;>
  · simp only [qsum]
    exact HasDerivAt.fun_sum fun k hk => (hc k hk).mul_const _

end QED.GradedProof.WI2

end
