/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXB2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: branch-2 partial fractions in `u`

Helper level (no frozen statement). Step 4 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 24+). At fixed `(X, s)` the branch-2 integrand of `I(X)` is a rational function of `u`
with poles at `B = u - X(1 - s)` (order 2), `C = X(1 - s) + (1 - X)u` (order 2) and
`D = coordD X u s` (order 3) and a linear polynomial part. For a coefficient vector
`k : Fin 9 → ℝ`,

`formXPF k X s u = k₀ + k₁ u + k₂/B + k₃/B² + k₄/C + k₅/C² + k₆/D + k₇/D² + k₈/D³`,

linear in `k` (`formXPF_add`, `formXPF_smul`), with the antiderivative `formXPFA`
(**`hasDerivAt_formXPFA`**; `dB/du = 1`, `dC/du = 1 - X`, `dD/du = (1 - X)(2 - s)`) and

**`integral_formXPF`**: `∫_{(1-s, X)} formXPF k X s u du = A(X) - A(1 - s)` for `1 - X < s < 1`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

/-- **The partial-fraction sum** in `u`. -/
noncomputable def formXPF (k : Fin 9 → ℝ) (X s u : ℝ) : ℝ :=
  k 0 + k 1 * u + k 2 / formXLb X u s + k 3 / formXLb X u s ^ 2 + k 4 / formXLc X u s +
    k 5 / formXLc X u s ^ 2 + k 6 / coordD X u s + k 7 / coordD X u s ^ 2 +
    k 8 / coordD X u s ^ 3

/-- **Its antiderivative in `u`.** -/
noncomputable def formXPFA (k : Fin 9 → ℝ) (X s u : ℝ) : ℝ :=
  k 0 * u + k 1 * u ^ 2 / 2 + k 2 * log (formXLb X u s) - k 3 / formXLb X u s +
    (k 4 * log (formXLc X u s) - k 5 / formXLc X u s) / (1 - X) +
    (k 6 * log (coordD X u s) - k 7 / coordD X u s - k 8 / (2 * coordD X u s ^ 2)) /
      ((1 - X) * (2 - s))

theorem formXPF_add (k k' : Fin 9 → ℝ) (X s u : ℝ) :
    formXPF (k + k') X s u = formXPF k X s u + formXPF k' X s u := by
  simp only [formXPF, Pi.add_apply]
  ring

theorem formXPF_smul (c : ℝ) (k : Fin 9 → ℝ) (X s u : ℝ) :
    formXPF (c • k) X s u = c * formXPF k X s u := by
  simp only [formXPF, Pi.smul_apply, smul_eq_mul]
  ring

theorem formXPFA_add (k k' : Fin 9 → ℝ) (X s u : ℝ) :
    formXPFA (k + k') X s u = formXPFA k X s u + formXPFA k' X s u := by
  simp only [formXPFA, Pi.add_apply]
  ring

theorem formXPFA_smul (c : ℝ) (k : Fin 9 → ℝ) (X s u : ℝ) :
    formXPFA (c • k) X s u = c * formXPFA k X s u := by
  simp only [formXPFA, Pi.smul_apply, smul_eq_mul]
  ring

theorem hasDerivAt_formXPFA (k : Fin 9 → ℝ) {X s u : ℝ} (hX : 1 - X ≠ 0) (hs : 2 - s ≠ 0)
    (hB : formXLb X u s ≠ 0) (hC : formXLc X u s ≠ 0) (hD : coordD X u s ≠ 0) :
    HasDerivAt (formXPFA k X s) (formXPF k X s u) u := by
  have hBd : HasDerivAt (fun u => formXLb X u s) 1 u := by
    unfold formXLb
    exact (hasDerivAt_id' u).sub_const _
  have hCd : HasDerivAt (fun u => formXLc X u s) (1 - X) u := by
    unfold formXLc
    exact ((hasDerivAt_id' u).const_mul (1 - X)).const_add _ |>.congr_deriv (by ring)
  have hDd : HasDerivAt (fun u => coordD X u s) ((1 - X) * (2 - s)) u := by
    unfold coordD
    exact ((hasDerivAt_id' u).const_mul ((1 - X) * (2 - s))).const_add _ |>.congr_deriv
      (by ring)
  have h := (((((hasDerivAt_id' u).const_mul (k 0)).add
    (((hasDerivAt_pow 2 u).const_mul (k 1)).div_const 2)).add
    ((hBd.log hB).const_mul (k 2))).sub ((hBd.inv hB).const_mul (k 3))).add
    ((((hCd.log hC).const_mul (k 4)).sub ((hCd.inv hC).const_mul (k 5))).div_const
      (1 - X)) |>.add (((((hDd.log hD).const_mul (k 6)).sub
      ((hDd.inv hD).const_mul (k 7))).sub
      ((((hDd.pow 2).const_mul 2).inv (by simp [hD])).const_mul (k 8))).div_const
      ((1 - X) * (2 - s)))
  convert h using 1
  · funext v
    simp only [formXPFA, Pi.add_apply, Pi.sub_apply, Pi.inv_apply, Pi.pow_apply]
    ring
  · simp only [formXPF, Pi.pow_apply]
    field_simp
    ring

/-- **The branch-2 `u`-integral of a partial-fraction sum.** -/
theorem integral_formXPF (k : Fin 9 → ℝ) {X s : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (1 - X) 1) :
    ∫ u in Ioo (1 - s) X, formXPF k X s u = formXPFA k X s X - formXPFA k X s (1 - s) := by
  have hab : 1 - s ≤ X := by linarith [hs.1]
  have h1X : 0 < 1 - X := by linarith [hX.2]
  have h2s : 0 < 2 - s := by linarith [hs.2]
  have hpos : ∀ u ∈ uIcc (1 - s) X,
      0 < formXLb X u s ∧ 0 < formXLc X u s ∧ 0 < coordD X u s := by
    intro u hu
    rw [uIcc_of_le hab] at hu
    have hu0 : 0 < u := by linarith [hu.1, hs.2]
    have hs0 : 0 < s := by linarith [hs.1, hX.2]
    refine ⟨?_, ?_, ?_⟩
    · unfold formXLb; nlinarith [hu.1, hX.1]
    · unfold formXLc
      have : 0 < 1 - s := by linarith [hs.2]
      nlinarith [mul_pos hX.1 this, mul_pos h1X hu0]
    · unfold coordD
      have : 0 < 1 - s := by linarith [hs.2]
      positivity
  have hc : ContinuousOn (formXPF k X s) (uIcc (1 - s) X) := by
    intro u hu
    obtain ⟨hB, hC, hD⟩ := hpos u hu
    unfold formXLb at hB
    unfold formXLc at hC
    unfold coordD at hD
    have hB' := hB.ne'
    have hC' := hC.ne'
    have hD' := hD.ne'
    apply ContinuousAt.continuousWithinAt
    unfold formXPF formXLb formXLc coordD
    fun_prop (disch := first | assumption | exact pow_ne_zero _ ‹_›)
  rw [integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le hab]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => ?_)
    hc.intervalIntegrable
  obtain ⟨hB, hC, hD⟩ := hpos u hu
  exact hasDerivAt_formXPFA k h1X.ne' h2s.ne' hB.ne' hC.ne' hD.ne'

end QED.ChainProof.SetCK

end
