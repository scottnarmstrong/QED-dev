/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutC

/-!
# Set (c), Stage K, closed forms: the threshold of the outer-massive corner is rational

Helper level (no frozen statement). The `(u + v)⁻²`-weight `T = scOutCT` of the outer-massive
corner switches branch where `s v = m` (`scOutCk`, `scOutCkap`: branch one for `s v < m`), with
`s = β/ρ - e`, `m = Y² + e Q(x)`, `e = y₃ (Y - y₃)`. In the coordinates `y₃ = a Y`
(`a ∈ (0, 1)`) at fixed `(a, x, v)` the switch is at the **rational** point

`Y_c = a v (1 - x)/((1 - a x)(x + a (Q(x) + v)))` (`formOCYc`):

**`formOC_branch_iff`**: `s v < m ↔ Y_c < Y` (for `Y > 0`, `v > 0`).

Proof: with `s_g = g/ρ - e` (`g = y₃(1 - Y)`) one has `s = max s_g 0`
(**`formOC_scOutCs_eq`**), and `s_g v - m = Y (a v/ρ - Y E)` with
`E = (1 - a x)(x + a (Q(x) + v))/x > 0`. In the coordinates `(Y, y₃)` the same switch is a cubic
in `x`; this is the change of order that makes the outer-corner density computable (Session 27+
of the Stage K notes).
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The branch switch** `Y_c(a, x, v)` of the outer-massive corner in the coordinates
`y₃ = a Y`. -/
noncomputable def formOCYc (a x v : ℝ) : ℝ :=
  a * v * (1 - x) / ((1 - a * x) * (x + a * (setCKQ x + v)))

section

variable {a x v Y : ℝ}

/-- `s = max (g/ρ - e) 0` at `y₃ = a Y`. -/
theorem formOC_scOutCs_eq (hx : x ∈ Ioo (0 : ℝ) 1) :
    scOutCs Y (a * Y) x =
      max (a * Y * (1 - Y) / scOutRho x - a * Y * (Y - a * Y)) 0 := by
  have hρ := scOutRho_pos hx
  have h1 : (1 - x) ≠ 0 := by linarith [hx.2]
  have h0 : x ≠ 0 := hx.1.ne'
  have e1 : a * Y * (Y - a * Y) * x / (1 - x) / scOutRho x = a * Y * (Y - a * Y) := by
    unfold scOutRho
    field_simp
  unfold scOutCs betaG cornerG
  rw [show a * Y * (1 - a * Y - (Y - a * Y)) = a * Y * (1 - Y) by ring,
    ← max_div_div_right hρ.le, e1, ← max_sub_sub_right, sub_self]

/-- **The branch switch is rational**: `s v < m ↔ Y_c < Y`. -/
theorem formOC_branch_iff (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v)
    (hY : 0 < Y) :
    scOutCs Y (a * Y) x * v < scOutCm Y (a * Y) x ↔ formOCYc a x v < Y := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hx0, hx1⟩ := hx
  have hρ := scOutRho_pos ⟨hx0, hx1⟩
  have hQ : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx0.le, hx1.le⟩
  have hax : 0 < 1 - a * x := by nlinarith
  have hxa : 0 < x + a * (setCKQ x + v) := by positivity
  have h1x : 0 < 1 - x := by linarith
  have hm : 0 < scOutCm Y (a * Y) x := by
    unfold scOutCm
    have : 0 ≤ a * Y * (Y - a * Y) := by
      have : 0 ≤ Y - a * Y := by nlinarith
      positivity
    positivity
  set sg := a * Y * (1 - Y) / scOutRho x - a * Y * (Y - a * Y) with hsg
  have hiff : max sg 0 * v < scOutCm Y (a * Y) x ↔ sg * v < scOutCm Y (a * Y) x := by
    rcases le_total sg 0 with h | h
    · rw [max_eq_right h, zero_mul]
      exact ⟨fun _ => (mul_nonpos_of_nonpos_of_nonneg h hv.le).trans_lt hm, fun _ => hm⟩
    · rw [max_eq_left h]
  have key : sg * v - scOutCm Y (a * Y) x =
      Y * (a * v * (1 - x) / x - Y * ((1 - a * x) * (x + a * (setCKQ x + v)) / x)) := by
    rw [hsg]
    unfold scOutCm scOutRho setCKQ
    field_simp
    ring
  have hE : 0 < (1 - a * x) * (x + a * (setCKQ x + v)) / x := by positivity
  have hYc : formOCYc a x v =
      a * v * (1 - x) / x / ((1 - a * x) * (x + a * (setCKQ x + v)) / x) := by
    unfold formOCYc
    field_simp
  rw [formOC_scOutCs_eq ⟨hx0, hx1⟩, hiff, ← sub_neg, key, mul_neg_iff, hYc,
    div_lt_iff₀ hE]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨hY, by linarith⟩

end

end QED.ChainProof.SetCK

end
