/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4T

/-!
# Set (d), master `I₈`: the primitive `F₄` of `p₄` and its value at `t = 0`

`Ψ₄`, the sum of its fifteen `(i, j, l)` parts, is a primitive of `p₄ dt/dξ`: each part of `p₄`
in compact form (`QED.ThreeLoopD.i8P4c400` and its companions, with `β₃`, `β₄` split by word
through `QED.ThreeLoopD.i8Be3_split`, `QED.ThreeLoopD.i8Be4_split`) is the sum of its sub-pieces.
Hence `F₄(t) = Ψ₄(ξ(t))` is a primitive of `p₄` on `t > 0`, continuous on `t ≥ 0`, and
`F₄(0) = Ψ₄(1)`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8F4`.
* `QED.ThreeLoopD.continuousOn_i8F4`, `QED.ThreeLoopD.i8F4_zero`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The primitive `Ψ₄` of `p₄ dt/dξ`, as a function of `ξ`. -/
noncomputable def i8Psi4 (x : ℝ) : ℝ :=
  i8Psi4X040 x + i8Psi4X130 x + i8Psi4X220 x + i8Psi4X310 x + i8Psi4X400 x +
    i8Psi4X031 x + i8Psi4X121 x + i8Psi4X211 x + i8Psi4X301 x + i8Psi4X022 x +
    i8Psi4X112 x + i8Psi4X202 x + i8Psi4X013 x + i8Psi4X103 x + i8Psi4X004 x

/-- The derivative of `i8Psi4`. -/
noncomputable def i8Psi4D (x : ℝ) : ℝ :=
  i8Psi4X040D x + i8Psi4X130D x + i8Psi4X220D x + i8Psi4X310D x + i8Psi4X400D x +
    i8Psi4X031D x + i8Psi4X121D x + i8Psi4X211D x + i8Psi4X301D x + i8Psi4X022D x +
    i8Psi4X112D x + i8Psi4X202D x + i8Psi4X013D x + i8Psi4X103D x + i8Psi4X004D x

/-- The part of `p₄` in `ξ` matching `i8Psi4`. -/
noncomputable def i8P4x (x : ℝ) : ℝ :=
  i8P4X040 x + i8P4X130 x + i8P4X220 x + i8P4X310 x + i8P4X400 x + i8P4X031 x +
    i8P4X121 x + i8P4X211 x + i8P4X301 x + i8P4X022 x + i8P4X112 x + i8P4X202 x +
    i8P4X013 x + i8P4X103 x + i8P4X004 x

theorem hasDerivAt_i8Psi4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4 (i8Psi4D x) x := by
  unfold i8Psi4 i8Psi4D
  exact (((((((((((((((hasDerivAt_i8Psi4X040 hx).add (hasDerivAt_i8Psi4X130 hx)).add
    (hasDerivAt_i8Psi4X220 hx)).add (hasDerivAt_i8Psi4X310 hx)).add (hasDerivAt_i8Psi4X400 hx)).add
    (hasDerivAt_i8Psi4X031 hx)).add (hasDerivAt_i8Psi4X121 hx)).add (hasDerivAt_i8Psi4X211 hx)).add
    (hasDerivAt_i8Psi4X301 hx)).add (hasDerivAt_i8Psi4X022 hx)).add (hasDerivAt_i8Psi4X112 hx)).add
    (hasDerivAt_i8Psi4X202 hx)).add (hasDerivAt_i8Psi4X013 hx)).add (hasDerivAt_i8Psi4X103 hx)).add
    (hasDerivAt_i8Psi4X004 hx))

theorem i8Psi4D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4x x := by
  unfold i8Psi4D i8P4x
  rw [← i8Psi4X040D_mul hx, ← i8Psi4X130D_mul hx, ← i8Psi4X220D_mul hx, ← i8Psi4X310D_mul hx, ←
    i8Psi4X400D_mul hx, ← i8Psi4X031D_mul hx, ← i8Psi4X121D_mul hx, ← i8Psi4X211D_mul hx, ←
    i8Psi4X301D_mul hx, ← i8Psi4X022D_mul hx, ← i8Psi4X112D_mul hx, ← i8Psi4X202D_mul hx, ←
    i8Psi4X013D_mul hx, ← i8Psi4X103D_mul hx, ← i8Psi4X004D_mul hx]
  ring

theorem continuousOn_i8Psi4 : ContinuousOn i8Psi4 (Ioc 0 1) := by
  unfold i8Psi4
  exact ((((((((((((((continuousOn_i8Psi4X040.add continuousOn_i8Psi4X130).add
    continuousOn_i8Psi4X220).add continuousOn_i8Psi4X310).add continuousOn_i8Psi4X400).add
    continuousOn_i8Psi4X031).add continuousOn_i8Psi4X121).add continuousOn_i8Psi4X211).add
    continuousOn_i8Psi4X301).add continuousOn_i8Psi4X022).add continuousOn_i8Psi4X112).add
    continuousOn_i8Psi4X202).add continuousOn_i8Psi4X013).add continuousOn_i8Psi4X103).add
    continuousOn_i8Psi4X004)

theorem i8Psi4_one : i8Psi4 1 = -1026 + 126 * zeta5 + 164 * π ^ 2 + 512 * Li 4 (1 / 2) +
    710 * zeta3 - 331 / 120 * π ^ 4 + 64 / 3 * Real.log 2 ^ 4 - 152 * Real.log 2 * π ^ 2 -
    62 / 3 * π ^ 2 * zeta3 + 80 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4
  rw [i8Psi4X040_one, i8Psi4X130_one, i8Psi4X220_one, i8Psi4X310_one, i8Psi4X400_one,
    i8Psi4X031_one, i8Psi4X121_one, i8Psi4X211_one, i8Psi4X301_one, i8Psi4X022_one, i8Psi4X112_one,
    i8Psi4X202_one, i8Psi4X013_one, i8Psi4X103_one, i8Psi4X004_one]
  ring

theorem i8Be1_split {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (2 + Real.log x * (1 + x) / (1 - x)) = ((1 + x) / (1 - x) * ((2 + ((-2) * x)) / (1 + x))) +
      ((1 + x) / (1 - x) * (1 * hpl [zero] x)) := by
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  simp only [hpl_zero]
  field_simp
  ring

theorem i8Be2_split {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i13Be2x x = ((1 + x) / (1 - x) * ((24 + ((-1) * π ^ 2) + ((-24) * x) +
      ((-1) * π ^ 2 * x)) / (6 + (6 * x)))) + ((1 + x) / (1 -
      x) * ((-2) * hpl [negOne, zero] x)) + ((1 + x) / (1 - x) * (1 * hpl [zero, zero] x)) +
      ((1 + x) / (1 - x) * (2 * hpl [zero] x)) := by
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i13Be2x
  simp only [i13_Li₂_neg_eq hx, i13_log_one_add_eq hx, hpl_zero, i13hw_00, i13hw_m0 hx]
  field_simp
  ring

theorem i8Be3_split {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ((1 + x) / (1 - x) * (i13PB x - i13P1c)) = ((1 + x) / (1 - x) * ((24 + ((-1) * π ^ 2) +
      ((-24) * x) + ((-6) * zeta3) + ((-1) * π ^ 2 * x) + ((-6) * x * zeta3)) / (3 +
      (3 * x)))) + ((1 + x) / (1 - x) * (((24 + ((-1) * π ^ 2)) / 6) * hpl [zero] x)) + ((1 +
      x) / (1 - x) * ((π ^ 2 / 3) * hpl [negOne] x)) + ((1 + x) / (1 -
      x) * ((-2) * hpl [zero, negOne, zero] x)) + ((1 + x) / (1 -
      x) * (4 * hpl [negOne, negOne, zero] x)) + ((1 + x) / (1 -
      x) * (1 * hpl [zero, zero, zero] x)) + ((1 + x) / (1 -
      x) * ((-2) * hpl [negOne, zero, zero] x)) + ((1 + x) / (1 -
      x) * ((-4) * hpl [negOne, zero] x)) + ((1 + x) / (1 - x) * (2 * hpl [zero, zero] x)) := by
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 3 + 3 * x ≠ 0 := by linarith [hx.1]
  unfold i13PB i13PBH i13P1c
  field_simp
  ring

theorem i8Be4_split {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ((1 + x) / (1 - x) * (i13PB4 x - i13P4c)) = ((1 + x) / (1 - x) * ((1920 +
      ((-1920) * x) + ((-480) * zeta3) + ((-80) * π ^ 2) + ((-3) * (π ^ 2 ^ 2)) +
      ((-480) * x * zeta3) + ((-80) * π ^ 2 * x) + ((-3) * x * (π ^ 2 ^ 2))) / (120 +
      (120 * x)))) + ((1 + x) / (1 - x) * (((24 + ((-1) * π ^ 2) +
      ((-6) * zeta3)) / 3) * hpl [zero] x)) + ((1 + x) / (1 - x) * ((((2 * π ^ 2) +
      (12 * zeta3)) / 3) * hpl [negOne] x)) + ((1 + x) / (1 - x) * (((24 +
      ((-1) * π ^ 2)) / 6) * hpl [zero, zero] x)) + ((1 + x) / (1 - x) * ((((-24) +
      π ^ 2) / 3) * hpl [negOne, zero] x)) + ((1 + x) / (1 -
      x) * ((((-2) * π ^ 2) / 3) * hpl [negOne, negOne] x)) + ((1 + x) / (1 -
      x) * ((π ^ 2 / 3) * hpl [zero, negOne] x)) + ((1 + x) / (1 -
      x) * ((-2) * hpl [zero, zero, negOne, zero] x)) + ((1 + x) / (1 -
      x) * (4 * hpl [negOne, zero, negOne, zero] x)) + ((1 + x) / (1 -
      x) * ((-8) * hpl [negOne, negOne, negOne, zero] x)) + ((1 + x) / (1 -
      x) * (4 * hpl [zero, negOne, negOne, zero] x)) + ((1 + x) / (1 -
      x) * (1 * hpl [zero, zero, zero, zero] x)) + ((1 + x) / (1 -
      x) * ((-2) * hpl [negOne, zero, zero, zero] x)) + ((1 + x) / (1 -
      x) * ((-2) * hpl [zero, negOne, zero, zero] x)) + ((1 + x) / (1 -
      x) * (4 * hpl [negOne, negOne, zero, zero] x)) + ((1 + x) / (1 -
      x) * ((-4) * hpl [zero, negOne, zero] x)) + ((1 + x) / (1 -
      x) * (8 * hpl [negOne, negOne, zero] x)) + ((1 + x) / (1 -
      x) * ((-4) * hpl [negOne, zero, zero] x)) + ((1 + x) / (1 -
      x) * (2 * hpl [zero, zero, zero] x)) := by
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h4 : 120 + 120 * x ≠ 0 := by linarith [hx.1]
  unfold i13PB4 i13PB4H i13P4c
  field_simp
  ring

/-- The `(i, j, l) = (0, 4, 0)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c040 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (1) * i8A4x x

theorem i8P4c040_eq {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c040 x = i8P4X040 x := by
  unfold i8P4c040 i8P4X040 i8P4s0 i8A4x
  ring

/-- The `(i, j, l) = (1, 3, 0)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c130 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * (2 + Real.log x * (1 + x) / (1 - x))) * i8A3x x

theorem i8P4c130_eq {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c130 x = i8P4X130 x := by
  unfold i8P4c130 i8P4X130 i8P4s1 i8A3x
  ring

/-- The `(i, j, l) = (2, 2, 0)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c220 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * i13Be2x x + (2 + Real.log x * (1 + x) / (1 - x)) * (2 +
    Real.log x * (1 + x) / (1 - x))) * i8A2x x

theorem i8P4c220_eq {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c220 x = i8P4X220 x := by
  unfold i8P4c220 i8P4X220 i8P4s2 i8P4s3 i8P4s4 i8P4s5 i8P4s6 i8P4s7 i8P4s8 i8P4s9 i8A2x
  ring

/-- The `(i, j, l) = (3, 1, 0)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c310 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * ((1 + x) / (1 - x) * (i13PB x - i13P1c)) + 2 * (2 + Real.log x * (1 +
    x) / (1 - x)) * i13Be2x x) * i8A1x x

theorem i8P4c310_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c310 x = i8P4X310 x := by
  unfold i8P4c310 i8P4X310 i8P4X310c0 i8P4X310c1 i8P4s10 i8P4s11 i8P4s12 i8P4s13 i8P4s14 i8P4s15
    i8P4s16 i8P4s17 i8P4s18 i8P4s19 i8P4s20 i8P4s21 i8A1x
  rw [i8Be3_split hx]
  ring

/-- The `(i, j, l) = (4, 0, 0)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c400 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * ((1 + x) / (1 - x) * (i13PB4 x - i13P4c)) + 2 * (2 + Real.log x * (1 +
    x) / (1 - x)) * ((1 + x) / (1 - x) * (i13PB x - i13P1c)) +
    i13Be2x x * i13Be2x x) * (x / (1 - x))

theorem i8P4c400_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c400 x = i8P4X400 x := by
  unfold i8P4c400 i8P4X400 i8P4X400c0 i8P4X400c1 i8P4X400c2 i8P4s22 i8P4s23 i8P4s24 i8P4s25 i8P4s26
    i8P4s27 i8P4s28 i8P4s29 i8P4s30 i8P4s31 i8P4s32 i8P4s33 i8P4s34 i8P4s35 i8P4s36 i8P4s37 i8P4s38
    i8P4s39 i8P4s40 i8P4s41 i8P4s42 i8P4s43 i8P4s44 i8P4s45 i8P4s46 i8P4s47 i8P4s48 i8P4s49 i8P4s50
  rw [i8Be3_split hx, i8Be4_split hx]
  ring

/-- The `(i, j, l) = (0, 3, 1)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c031 (x : ℝ) : ℝ :=
  -((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 1 / 1 * (1) * i8A3x x)

theorem i8P4c031_eq {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c031 x = i8P4X031 x := by
  unfold i8P4c031 i8P4X031 i8P4X031c0 i8P4X031c1 i8P4s51 i8P4s52 i8P4s53 i8P4s54 i8P4s55 i8P4s56
    i8P4s57 i8P4s58 i8P4s59 i8P4s60 i8P4s61 i8P4s62 i8P4s63 i8P4s64 i8P4s65 i8P4s66 i8A3x
  ring

/-- The `(i, j, l) = (1, 2, 1)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c121 (x : ℝ) : ℝ :=
  -((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 1 / 1 * (2 * (2 + Real.log x * (1 +
    x) / (1 - x))) * i8A2x x)

theorem i8P4c121_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c121 x = i8P4X121 x := by
  unfold i8P4c121 i8P4X121 i8P4s67 i8P4s68 i8P4s69 i8P4s70 i8P4s71 i8P4s72 i8P4s73 i8P4s74 i8P4s75
    i8A2x
  rw [i8Be1_split hx]
  ring

/-- The `(i, j, l) = (2, 1, 1)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c211 (x : ℝ) : ℝ :=
  -((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 1 / 1 * (2 * i13Be2x x + (2 +
    Real.log x * (1 + x) / (1 - x)) * (2 + Real.log x * (1 + x) / (1 - x))) * i8A1x x)

theorem i8P4c211_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c211 x = i8P4X211 x := by
  unfold i8P4c211 i8P4X211 i8P4X211c0 i8P4X211c1 i8P4s76 i8P4s77 i8P4s78 i8P4s79 i8P4s80 i8P4s81
    i8P4s82 i8P4s83 i8P4s84 i8P4s85 i8P4s86 i8P4s87 i8A1x
  rw [i8Be1_split hx, i8Be2_split hx]
  ring

/-- The `(i, j, l) = (3, 0, 1)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c301 (x : ℝ) : ℝ :=
  -((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 1 / 1 * (2 * ((1 + x) / (1 -
    x) * (i13PB x - i13P1c)) + 2 * (2 + Real.log x * (1 + x) / (1 -
    x)) * i13Be2x x) * (x / (1 - x)))

theorem i8P4c301_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c301 x = i8P4X301 x := by
  unfold i8P4c301 i8P4X301 i8P4X301c0 i8P4X301c1 i8P4X301c2 i8P4s88 i8P4s89 i8P4s90 i8P4s91 i8P4s92
    i8P4s93 i8P4s94 i8P4s95 i8P4s96 i8P4s97 i8P4s98 i8P4s99 i8P4s100 i8P4s101 i8P4s102 i8P4s103
    i8P4s104 i8P4s105 i8P4s106 i8P4s107 i8P4s108
  rw [i8Be1_split hx, i8Be3_split hx]
  ring

/-- The `(i, j, l) = (0, 2, 2)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c022 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 2 / 2 * (1) * i8A2x x

theorem i8P4c022_eq {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c022 x = i8P4X022 x := by
  unfold i8P4c022 i8P4X022 i8P4X022c0 i8P4X022c1 i8P4s109 i8P4s110 i8P4s111 i8P4s112 i8P4s113
    i8P4s114 i8P4s115 i8P4s116 i8P4s117 i8P4s118 i8P4s119 i8P4s120 i8A2x
  ring

/-- The `(i, j, l) = (1, 1, 2)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c112 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 2 / 2 * (2 * (2 + Real.log x * (1 +
    x) / (1 - x))) * i8A1x x

theorem i8P4c112_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c112 x = i8P4X112 x := by
  unfold i8P4c112 i8P4X112 i8P4s121 i8P4s122 i8P4s123 i8P4s124 i8P4s125 i8P4s126 i8P4s127 i8P4s128
    i8A1x
  rw [i8Be1_split hx]
  ring

/-- The `(i, j, l) = (2, 0, 2)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c202 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 2 / 2 * (2 * i13Be2x x + (2 +
    Real.log x * (1 + x) / (1 - x)) * (2 + Real.log x * (1 + x) / (1 - x))) * (x / (1 - x))

theorem i8P4c202_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c202 x = i8P4X202 x := by
  unfold i8P4c202 i8P4X202 i8P4X202c0 i8P4X202c1 i8P4s129 i8P4s130 i8P4s131 i8P4s132 i8P4s133
    i8P4s134 i8P4s135 i8P4s136 i8P4s137 i8P4s138 i8P4s139 i8P4s140
  rw [i8Be2_split hx]
  ring

/-- The `(i, j, l) = (0, 1, 3)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c013 (x : ℝ) : ℝ :=
  -((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 3 / 6 * (1) * i8A1x x)

theorem i8P4c013_eq {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c013 x = i8P4X013 x := by
  unfold i8P4c013 i8P4X013 i8P4s141 i8P4s142 i8P4s143 i8P4s144 i8P4s145 i8P4s146 i8P4s147 i8P4s148
    i8A1x
  ring

/-- The `(i, j, l) = (1, 0, 3)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c103 (x : ℝ) : ℝ :=
  -((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 3 / 6 * (2 * (2 + Real.log x * (1 +
    x) / (1 - x))) * (x / (1 - x)))

theorem i8P4c103_eq {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c103 x = i8P4X103 x := by
  unfold i8P4c103 i8P4X103 i8P4s149 i8P4s150 i8P4s151 i8P4s152
  ring

/-- The `(i, j, l) = (0, 0, 4)` part `t Bᵢ Aⱼ (-λ)^l/l!` of `p₄`, in `ξ`. -/
noncomputable def i8P4c004 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 4 / 24 * (1) * (x / (1 - x))

theorem i8P4c004_eq {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) : i8P4c004 x = i8P4X004 x := by
  unfold i8P4c004 i8P4X004 i8P4s153 i8P4s154 i8P4s155 i8P4s156 i8P4s157
  ring

theorem i8P4_eq_c {t : ℝ} (ht : 0 < t) : i8P4 t = i8P4c040 (i13Xi t) + i8P4c130 (i13Xi t) +
    i8P4c220 (i13Xi t) + i8P4c310 (i13Xi t) + i8P4c400 (i13Xi t) + i8P4c031 (i13Xi t) +
    i8P4c121 (i13Xi t) + i8P4c211 (i13Xi t) + i8P4c301 (i13Xi t) + i8P4c022 (i13Xi t) +
    i8P4c112 (i13Xi t) + i8P4c202 (i13Xi t) + i8P4c013 (i13Xi t) + i8P4c103 (i13Xi t) +
    i8P4c004 (i13Xi t) := by
  have hT := i13Xi_t ht.le
  unfold i8P4 i8P4c040 i8P4c130 i8P4c220 i8P4c310 i8P4c400 i8P4c031 i8P4c121 i8P4c211 i8P4c301
    i8P4c022 i8P4c112 i8P4c202 i8P4c013 i8P4c103 i8P4c004 i13Be4r i13Be3r i13Be1r
  rw [i13Be2r_eq, i8_log_eq ht]
  generalize i13Xi t = ξ at hT ⊢
  subst hT
  ring

theorem i8P4_eq {t : ℝ} (ht : 0 < t) : i8P4 t = i8P4x (i13Xi t) := by
  have hx := i8_xi_mem ht
  rw [i8P4_eq_c ht, i8P4c040_eq hx, i8P4c130_eq hx, i8P4c220_eq hx, i8P4c310_eq hx, i8P4c400_eq hx,
    i8P4c031_eq hx, i8P4c121_eq hx, i8P4c211_eq hx, i8P4c301_eq hx, i8P4c022_eq hx, i8P4c112_eq hx,
    i8P4c202_eq hx, i8P4c013_eq hx, i8P4c103_eq hx, i8P4c004_eq hx]
  unfold i8P4x
  ring

/-! ### `F₄` -/

/-- `F₄(t) = Ψ₄(ξ(t))`. -/
noncomputable def i8F4 (t : ℝ) : ℝ := i8Psi4 (i13Xi t)

theorem hasDerivAt_i8F4 {t : ℝ} (ht : 0 < t) : HasDerivAt i8F4 (i8P4 t) t := by
  have e := (hasDerivAt_i8Psi4 (i8_xi_mem ht)).comp t (hasDerivAt_i13Xi ht)
  rw [i8Psi4D_mul (i8_xi_mem ht), ← i8P4_eq ht] at e
  exact e

theorem continuousOn_i8F4 : ContinuousOn i8F4 (Ici 0) :=
  continuousOn_i8Psi4.comp continuous_i13Xi.continuousOn fun _ ht =>
    ⟨i13Xi_pos ht, i13Xi_le_one ht⟩

theorem i8F4_zero : i8F4 0 = -1026 + 126 * zeta5 + 164 * π ^ 2 + 512 * Li 4 (1 / 2) +
    710 * zeta3 - 331 / 120 * π ^ 4 + 64 / 3 * Real.log 2 ^ 4 - 152 * Real.log 2 * π ^ 2 -
    62 / 3 * π ^ 2 * zeta3 + 80 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8F4
  rw [i13Xi_zero, i8Psi4_one]

end QED.ThreeLoopD
