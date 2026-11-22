/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3Vb

/-!
# Set (d), master `I₈`: the primitive `F₃` of `p₃` and its value at `t = 0`

`Ψ₃ = ∑ Ψ₃⁽ᵍ⁾` over the seven pieces of `QED.ThreeLoopD.SetDMastersI8R3Pa`, ...,
`QED.ThreeLoopD.SetDMastersI8R3Ph` is a primitive of `p₃ dt/dξ`, so `F₃(t) = Ψ₃(ξ(t))` is a
primitive of `p₃` on `t > 0` (`QED.ThreeLoopD.hasDerivAt_i8F3`). It is continuous on `t ≥ 0`, and
`F₃(0) = Ψ₃(1) = -16 π² log 2 + 25π⁴/72 + 163π²/6 + 68ζ(3) - 90`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8F3`.
* `QED.ThreeLoopD.continuousOn_i8F3`, `QED.ThreeLoopD.i8F3_zero`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The primitive `Ψ₃` of `p₃ dt/dξ`, as a function of `ξ`. -/
noncomputable def i8Psi3 (x : ℝ) : ℝ :=
  i8Psi3a x + i8Psi3b x + i8Psi3d x + i8Psi3e x + i8Psi3f x + i8Psi3g x + i8Psi3h x

/-- `p₃` in the variable `ξ`. -/
noncomputable def i8P3x (x : ℝ) : ℝ :=
  i8P3xa x + i8P3xb x + i8P3xd x + i8P3xe x + i8P3xf x + i8P3xg x + i8P3xh x

theorem i8P3_eq {t : ℝ} (ht : 0 < t) : i8P3 t = i8P3x (i13Xi t) := by
  have hT := (i13Xi_t ht.le).symm
  have hlog := (i8_log_eq ht).symm
  unfold i8P3 i8P3x i8P3xa i8P3xb i8P3xd i8P3xe i8P3xf i8P3xg i8P3xh i13Be3r i13Be1r
  rw [i13Be2r_eq, hT, hlog]
  ring

theorem hasDerivAt_i8Psi3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3 (i8Psi3aD x + i8Psi3bD x + i8Psi3dD x + i8Psi3eD x + i8Psi3fD x +
      i8Psi3gD x + i8Psi3hD x) x := by
  unfold i8Psi3
  exact ((((((hasDerivAt_i8Psi3a hx).add (hasDerivAt_i8Psi3b hx)).add
    (hasDerivAt_i8Psi3d hx)).add (hasDerivAt_i8Psi3e hx)).add (hasDerivAt_i8Psi3f hx)).add
    (hasDerivAt_i8Psi3g hx)).add (hasDerivAt_i8Psi3h hx)

theorem i8Psi3D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (i8Psi3aD x + i8Psi3bD x + i8Psi3dD x + i8Psi3eD x + i8Psi3fD x + i8Psi3gD x +
      i8Psi3hD x) * (-x ^ 2 / (1 - x ^ 2)) = i8P3x x := by
  unfold i8P3x
  rw [← i8Psi3aD_mul hx, ← i8Psi3bD_mul hx, ← i8Psi3dD_mul hx, ← i8Psi3eD_mul hx,
    ← i8Psi3fD_mul hx, ← i8Psi3gD_mul hx, ← i8Psi3hD_mul hx]
  ring

/-- `F₃(t) = Ψ₃(ξ(t))`. -/
noncomputable def i8F3 (t : ℝ) : ℝ := i8Psi3 (i13Xi t)

theorem hasDerivAt_i8F3 {t : ℝ} (ht : 0 < t) : HasDerivAt i8F3 (i8P3 t) t := by
  have e := (hasDerivAt_i8Psi3 (i8_xi_mem ht)).comp t (hasDerivAt_i13Xi ht)
  rw [i8Psi3D_mul (i8_xi_mem ht), ← i8P3_eq ht] at e
  exact e

theorem continuousOn_i8Psi3 : ContinuousOn i8Psi3 (Ioc 0 1) := by
  unfold i8Psi3
  exact (((((continuousOn_i8Psi3a.add continuousOn_i8Psi3b).add continuousOn_i8Psi3d).add
    continuousOn_i8Psi3e).add continuousOn_i8Psi3f).add continuousOn_i8Psi3g).add
    continuousOn_i8Psi3h

theorem continuousOn_i8F3 : ContinuousOn i8F3 (Ici 0) :=
  continuousOn_i8Psi3.comp continuous_i13Xi.continuousOn fun _ ht =>
    ⟨i13Xi_pos ht, i13Xi_le_one ht⟩

/-- **`Ψ₃(1) = -16 π² log 2 + 25π⁴/72 + 163π²/6 + 68ζ(3) - 90`.** -/
theorem i8Psi3_one : i8Psi3 1 =
    -16 * π ^ 2 * Real.log 2 + 25 * π ^ 4 / 72 + 163 * π ^ 2 / 6 + 68 * zeta3 - 90 := by
  unfold i8Psi3
  rw [i8Psi3a_one, i8Psi3b_one, i8Psi3d_one, i8Psi3e_one, i8Psi3f_one, i8Psi3g_one, i8Psi3h_one]
  ring

theorem i8F3_zero : i8F3 0 =
    -16 * π ^ 2 * Real.log 2 + 25 * π ^ 4 / 72 + 163 * π ^ 2 / 6 + 68 * zeta3 - 90 := by
  unfold i8F3
  rw [i13Xi_zero, i8Psi3_one]

end QED.ThreeLoopD
