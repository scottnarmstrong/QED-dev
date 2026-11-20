/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXThr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the threshold coordinates of the inner `(Y, y₃)` triangle

Helper level (no frozen statement). Shared layer of the closed forms of `ρ_C` and `ρ_X`. Fix an
outer node `X ∈ (0, 1)`. On the triangle `T = {0 < y₃ < Y < X}` (`coordT`), let `m = w_Y(X)`
(`cornInWX`), `s ∈ (0, 1)` the threshold `w₀(s) = m` (`cornInW0`) and `u = Y - s y₃`. The map
`(Y, y₃) ↦ (u, s)` is inverted by two rational maps (parameters ordered `(u, s)`):

* branch 1 (`s + u ≤ 1`, i.e. `s ≤ x*`): `coordPsi1`,
  `Y = (X² + (1-X)u)/M`, `M = X² + (1-X)(1+u)`, `y₃ = (Y - u)/s`, on
  `coordR1 = {u ∈ (0, X), s ∈ (s_lo(u), 1 - u]}`, `s_lo = (X-u)(X+u-Xu)/(X² + (1-X)u)`;
* branch 2 (`s + u > 1`): `coordPsi2`, `Y = (X²(1-s) + (1-X)u²)/D`,
  `y₃ = (X-u)(1-s)(X+u-Xu)/(s D)`, `D = X²(1-s) + (1-X)(2-s)u`, on
  `coordR2 = {u ∈ (0, X), s ∈ (1 - u, 1)}`.

Main results: on `R_b` the image lies in `T` and `s` is its threshold (`coordPsi1_spec`,
`coordPsi2_spec`); every point of `T` is hit (`coordT_subset`); the coordinates are recovered
from the image (`coord_eq_of_psi`), hence each map is injective and the images are disjoint
(`coord_injOn1`, `coord_injOn2`, `coord_disjoint`). With the explicit threshold, **`coord_thr1`**,
**`coord_thr2`**: `formXThr Y y₃ (w_Y(X)) = s` at `(Y, y₃) = Ψ_b(u, s)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The triangle** `T = {(Y, y₃) : 0 < y₃ < Y < X}`. -/
def coordT (X : ℝ) : Set (ℝ × ℝ) := {q | q.1 ∈ Ioo 0 X ∧ q.2 ∈ Ioo 0 q.1}

/-- `M = X² + (1 - X)(1 + u)`. -/
def coordM (X u : ℝ) : ℝ := X ^ 2 + (1 - X) * (1 + u)

/-- Branch 1: `Y` as a function of `u`. -/
noncomputable def coordY1 (X u : ℝ) : ℝ := (X ^ 2 + (1 - X) * u) / coordM X u

/-- The lower end `s_lo(u) = 1 - u/Y(u)` of the branch-1 range of `s`. -/
noncomputable def coordSLo (X u : ℝ) : ℝ := (X - u) * (X + u - X * u) / (X ^ 2 + (1 - X) * u)

/-- **The branch-1 map** `(u, s) ↦ (Y, y₃)`. -/
noncomputable def coordPsi1 (X : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (coordY1 X p.1, (coordY1 X p.1 - p.1) / p.2)

/-- `D = X²(1 - s) + (1 - X)(2 - s) u`. -/
def coordD (X u s : ℝ) : ℝ := X ^ 2 * (1 - s) + (1 - X) * (2 - s) * u

/-- Branch 2: `Y`. -/
noncomputable def coordY2 (X u s : ℝ) : ℝ := (X ^ 2 * (1 - s) + (1 - X) * u ^ 2) / coordD X u s

/-- Branch 2: `y₃`. -/
noncomputable def coordZ2 (X u s : ℝ) : ℝ :=
  (X - u) * (1 - s) * (X + u - X * u) / (s * coordD X u s)

/-- **The branch-2 map** `(u, s) ↦ (Y, y₃)`. -/
noncomputable def coordPsi2 (X : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (coordY2 X p.1 p.2, coordZ2 X p.1 p.2)

/-- **The branch-1 region** `u ∈ (0, X)`, `s ∈ (s_lo(u), 1 - u]`. -/
def coordR1 (X : ℝ) : Set (ℝ × ℝ) := {p | p.1 ∈ Ioo 0 X ∧ p.2 ∈ Ioc (coordSLo X p.1) (1 - p.1)}

/-- **The branch-2 region** `u ∈ (0, X)`, `s ∈ (1 - u, 1)`. -/
def coordR2 (X : ℝ) : Set (ℝ × ℝ) := {p | p.1 ∈ Ioo 0 X ∧ p.2 ∈ Ioo (1 - p.1) 1}

/-- The pair `(Y, y₃)` lies in `T`, `s ∈ (0, 1)` is its threshold and `u = Y - s y₃`. -/
def CoordSpec (X : ℝ) (q p : ℝ × ℝ) : Prop :=
  q ∈ coordT X ∧ p.2 ∈ Ioo (0 : ℝ) 1 ∧ cornInW0 q.1 q.2 p.2 = cornInWX q.1 X ∧
    q.1 - p.2 * q.2 = p.1

section

variable {X : ℝ}

theorem coordM_pos (hX : X ∈ Ioo (0 : ℝ) 1) {u : ℝ} (hu : 0 ≤ u) : 0 < coordM X u := by
  have := hX.2
  unfold coordM
  have : 0 < 1 - X := by linarith
  positivity

theorem coordD_pos (hX : X ∈ Ioo (0 : ℝ) 1) {u s : ℝ} (hu : 0 < u) (hs : s < 1) :
    0 < coordD X u s := by
  have := hX.1
  unfold coordD
  have : 0 < 1 - X := by linarith [hX.2]
  have : 0 < 1 - s := by linarith
  have : 0 < 2 - s := by linarith
  positivity

theorem cornerG_eq (Y y3 : ℝ) : cornerG y3 (Y - y3) = y3 * (1 - Y) := by
  unfold cornerG; ring

theorem cornInWX_eq (Y X : ℝ) (hY : Y ≠ 1) (hX : X ≠ 1) :
    cornInWX Y X = (X - Y) * (X + Y - X * Y) / (1 - X) := by
  have h1 : 1 - Y ≠ 0 := sub_ne_zero.2 (Ne.symm hY)
  have h2 : 1 - X ≠ 0 := sub_ne_zero.2 (Ne.symm hX)
  unfold cornInWX setCKQ
  field_simp
  ring

/-- Branch 1 lands in `T` with threshold `s`. -/
theorem coordPsi1_spec (hX : X ∈ Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ coordR1 X) :
    CoordSpec X (coordPsi1 X p) p := by
  obtain ⟨u, s⟩ := p
  obtain ⟨⟨hu0, huX⟩, hsl, hsu⟩ := hp
  simp only at hu0 huX hsl hsu
  have h1X : 0 < 1 - X := by linarith [hX.2]
  have hM := coordM_pos hX hu0.le
  have hN : 0 < X ^ 2 + (1 - X) * u := by have := hX.1; positivity
  have hXu : 0 < X - u := by linarith
  have hA : 0 < X + u - X * u := by nlinarith
  have hlo : 0 < coordSLo X u := by unfold coordSLo; positivity
  have hs0 : 0 < s := hlo.trans hsl
  have hs1 : s < 1 := by linarith
  have hY0 : 0 < coordY1 X u := by unfold coordY1; positivity
  have hXY : X - coordY1 X u = (X - u) * (1 - X) ^ 2 / coordM X u := by
    unfold coordY1; field_simp; unfold coordM; ring
  have hYu : coordY1 X u - u = (X - u) * (X + u - X * u) / coordM X u := by
    unfold coordY1; field_simp; unfold coordM; ring
  have hYX : coordY1 X u < X := by
    have : 0 < (X - u) * (1 - X) ^ 2 / coordM X u := by positivity
    linarith
  have hYu0 : 0 < coordY1 X u - u := by rw [hYu]; positivity
  -- `s_lo = (Y - u)/Y`
  have hlo' : coordSLo X u = (coordY1 X u - u) / coordY1 X u := by
    rw [hYu]; unfold coordY1 coordSLo; field_simp
  have hz0 : 0 < (coordY1 X u - u) / s := div_pos hYu0 hs0
  have hzY : (coordY1 X u - u) / s < coordY1 X u := by
    rw [div_lt_iff₀ hs0]
    rw [hlo', div_lt_iff₀ hY0] at hsl
    linarith
  have hY1 : coordY1 X u < 1 := hYX.trans hX.2
  refine ⟨⟨⟨hY0, hYX⟩, hz0, hzY⟩, ⟨hs0, hs1⟩, ?_, ?_⟩
  · simp only [coordPsi1]
    have hb : s * (1 - (coordY1 X u - u) / s) ≤ 1 - coordY1 X u := by
      rw [mul_sub, mul_div_cancel₀ _ hs0.ne']; linarith
    rw [cornInW0, betaG_of_branch1 hz0 hs1 hb, cornerG_eq,
      cornInWX_eq _ _ hY1.ne hX.2.ne]
    have hM0 := hM.ne'
    unfold coordY1 at hYu ⊢
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hs0.ne' h1X.ne']
    field_simp
    unfold coordM
    ring
  · simp only [coordPsi1]
    field_simp
    ring

/-- Branch 2 lands in `T` with threshold `s`. -/
theorem coordPsi2_spec (hX : X ∈ Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ coordR2 X) :
    CoordSpec X (coordPsi2 X p) p := by
  obtain ⟨u, s⟩ := p
  obtain ⟨⟨hu0, huX⟩, hsl, hs1⟩ := hp
  simp only at hu0 huX hsl hs1
  have hX0 := hX.1
  have h1X : 0 < 1 - X := by linarith [hX.2]
  have hD := coordD_pos hX hu0 hs1
  have hs0 : 0 < s := by linarith
  have h1s : 0 < 1 - s := by linarith
  have hXu : 0 < X - u := by linarith
  have hA : 0 < X + u - X * u := by nlinarith
  have hB : 0 < u - X * (1 - s) := by nlinarith
  have hC : 0 < X * (1 - s) + u * (1 - X) := by positivity
  have hY0 : 0 < coordY2 X u s := by unfold coordY2; positivity
  have hXY : X - coordY2 X u s = (X - u) * (1 - X) * (u - X * (1 - s)) / coordD X u s := by
    unfold coordY2; field_simp; unfold coordD; ring
  have hYX : coordY2 X u s < X := by
    have : 0 < (X - u) * (1 - X) * (u - X * (1 - s)) / coordD X u s := by positivity
    linarith
  have hz0 : 0 < coordZ2 X u s := by unfold coordZ2; positivity
  have hYz : coordY2 X u s - coordZ2 X u s =
      (u - X * (1 - s)) * (X * (1 - s) + u * (1 - X)) / (s * coordD X u s) := by
    unfold coordY2 coordZ2; field_simp; ring
  have hzY : coordZ2 X u s < coordY2 X u s := by
    have : 0 < (u - X * (1 - s)) * (X * (1 - s) + u * (1 - X)) / (s * coordD X u s) := by
      positivity
    linarith
  have hY1 : coordY2 X u s < 1 := hYX.trans hX.2
  have hrec : coordY2 X u s - s * coordZ2 X u s = u := by
    unfold coordY2 coordZ2; field_simp; unfold coordD; ring
  refine ⟨⟨⟨hY0, hYX⟩, hz0, hzY⟩, ⟨hs0, hs1⟩, ?_, hrec⟩
  simp only [coordPsi2]
  have hb : 1 - coordY2 X u s ≤ s * (1 - coordZ2 X u s) := by nlinarith
  rw [cornInW0_of_branch2 hz0 hs1 hb, cornInWX_eq _ _ hY1.ne hX.2.ne,
    div_eq_div_iff h1s.ne' h1X.ne']
  unfold coordY2 coordZ2
  field_simp
  unfold coordD
  ring

/-- **Recovery of the coordinates**: two parameter points with a common image coincide. -/
theorem coord_eq_of_psi (hX : X ∈ Ioo (0 : ℝ) 1) {q p p' : ℝ × ℝ} (h : CoordSpec X q p)
    (h' : CoordSpec X q p') : p = p' := by
  obtain ⟨⟨⟨hY0, hYX⟩, hz0, hzY⟩, hs, hw, hu⟩ := h
  obtain ⟨-, hs', hw', hu'⟩ := h'
  have hY1 : q.1 < 1 := hYX.trans hX.2
  have hss : p.2 = p'.2 := by
    rcases lt_trichotomy p.2 p'.2 with hlt | heq | hgt
    · exact absurd (hw.trans hw'.symm) (cornInW0_lt_of_lt hz0 hzY hY1 hs.1 hlt hs'.2).ne
    · exact heq
    · exact absurd (hw'.trans hw.symm) (cornInW0_lt_of_lt hz0 hzY hY1 hs'.1 hgt hs.2).ne
  exact Prod.ext (by rw [← hu, ← hu', hss]) hss

theorem coord_injOn1 (hX : X ∈ Ioo (0 : ℝ) 1) : InjOn (coordPsi1 X) (coordR1 X) :=
  fun _ hp _ hp' he => coord_eq_of_psi hX (coordPsi1_spec hX hp) (he ▸ coordPsi1_spec hX hp')

theorem coord_injOn2 (hX : X ∈ Ioo (0 : ℝ) 1) : InjOn (coordPsi2 X) (coordR2 X) :=
  fun _ hp _ hp' he => coord_eq_of_psi hX (coordPsi2_spec hX hp) (he ▸ coordPsi2_spec hX hp')

theorem coord_disjoint (hX : X ∈ Ioo (0 : ℝ) 1) :
    Disjoint (coordPsi1 X '' coordR1 X) (coordPsi2 X '' coordR2 X) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ ⟨p', hp', he⟩
  have := coord_eq_of_psi hX (coordPsi1_spec hX hp) (he ▸ coordPsi2_spec hX hp')
  subst this
  exact absurd hp'.2.1 (not_lt.2 (by linarith [hp.2.2]))

theorem coord_image1_subset (hX : X ∈ Ioo (0 : ℝ) 1) : coordPsi1 X '' coordR1 X ⊆ coordT X := by
  rintro _ ⟨p, hp, rfl⟩
  exact (coordPsi1_spec hX hp).1

theorem coord_image2_subset (hX : X ∈ Ioo (0 : ℝ) 1) : coordPsi2 X '' coordR2 X ⊆ coordT X := by
  rintro _ ⟨p, hp, rfl⟩
  exact (coordPsi2_spec hX hp).1

/-- **Every point of the triangle is hit** by one of the two maps. -/
theorem coordT_subset (hX : X ∈ Ioo (0 : ℝ) 1) :
    coordT X ⊆ coordPsi1 X '' coordR1 X ∪ coordPsi2 X '' coordR2 X := by
  rintro ⟨Y, y3⟩ ⟨⟨hY0, hYX⟩, hz0, hzY⟩
  simp only at hY0 hYX hz0 hzY
  have hY1 : Y < 1 := hYX.trans hX.2
  have h1X : 0 < 1 - X := by linarith [hX.2]
  have h1Y : 0 < 1 - Y := by linarith
  have hw := cornInWX_pos ⟨hY0, hY1⟩ ⟨hYX, hX.2⟩
  obtain ⟨⟨hs0, hs1⟩, hm⟩ := formXThr_spec hz0 hzY hY1 hw
  set s := formXThr Y y3 (cornInWX Y X)
  set u := Y - s * y3 with hu
  have hu0 : 0 < u := by nlinarith
  have huX : u < X := by nlinarith
  rw [cornInWX_eq _ _ hY1.ne hX.2.ne] at hm
  by_cases hb : s + u ≤ 1
  · left
    have hb' : s * (1 - y3) ≤ 1 - Y := by linarith
    rw [cornInW0, betaG_of_branch1 hz0 hs1 hb', cornerG_eq, eq_div_iff h1X.ne'] at hm
    have hMu := coordM_pos hX hu0.le
    have hYe : coordY1 X u = Y := by
      unfold coordY1
      rw [div_eq_iff hMu.ne']
      unfold coordM
      nlinarith
    refine ⟨(u, s), ⟨⟨hu0, huX⟩, ?_, by simp only; linarith⟩, ?_⟩
    · simp only
      have hN : 0 < X ^ 2 + (1 - X) * u := by have := hX.1; positivity
      have hlo : coordSLo X u = (Y - u) / Y := by
        rw [← hYe]; unfold coordY1 coordSLo coordM; field_simp; ring
      rw [hlo, div_lt_iff₀ hY0]
      nlinarith
    · simp only [coordPsi1, hYe]
      refine Prod.ext rfl ?_
      simp only
      rw [hu]
      field_simp
      ring
  · right
    have hb' : 1 - Y ≤ s * (1 - y3) := by linarith
    rw [cornInW0_of_branch2 hz0 hs1 hb', div_eq_div_iff (by linarith) h1X.ne'] at hm
    have hD := coordD_pos hX hu0 hs1
    refine ⟨(u, s), ⟨⟨hu0, huX⟩, by simp only; linarith, hs1⟩, ?_⟩
    simp only [coordPsi2]
    refine Prod.ext ?_ ?_
    · simp only
      unfold coordY2
      rw [div_eq_iff hD.ne']
      unfold coordD
      rw [hu]
      linear_combination -hm
    · simp only
      unfold coordZ2
      rw [div_eq_iff (mul_pos hs0 hD).ne']
      unfold coordD
      rw [hu]
      linear_combination -hm

/-- **The triangle is the disjoint union of the two images.** -/
theorem coordT_eq (hX : X ∈ Ioo (0 : ℝ) 1) :
    coordT X = coordPsi1 X '' coordR1 X ∪ coordPsi2 X '' coordR2 X :=
  (coordT_subset hX).antisymm (union_subset (coord_image1_subset hX) (coord_image2_subset hX))

/-- **The explicit threshold** at a point of `T` with coordinates `p` is `s = p.2`. -/
theorem coord_thr (hX : X ∈ Ioo (0 : ℝ) 1) {q p : ℝ × ℝ} (h : CoordSpec X q p) :
    formXThr q.1 q.2 (cornInWX q.1 X) = p.2 := by
  obtain ⟨⟨⟨hY0, hYX⟩, hz0, hzY⟩, -, -, -⟩ := id h
  obtain ⟨hs, hm⟩ := formXThr_spec hz0 hzY (hYX.trans hX.2)
    (cornInWX_pos ⟨hY0, hYX.trans hX.2⟩ ⟨hYX, hX.2⟩)
  exact congrArg Prod.snd (coord_eq_of_psi (p := (q.1 - formXThr q.1 q.2 (cornInWX q.1 X) * q.2,
    formXThr q.1 q.2 (cornInWX q.1 X))) hX ⟨h.1, hs, hm, rfl⟩ h)

theorem coord_thr1 (hX : X ∈ Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ coordR1 X) :
    formXThr (coordPsi1 X p).1 (coordPsi1 X p).2 (cornInWX (coordPsi1 X p).1 X) = p.2 :=
  coord_thr hX (coordPsi1_spec hX hp)

theorem coord_thr2 (hX : X ∈ Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ coordR2 X) :
    formXThr (coordPsi2 X p).1 (coordPsi2 X p).2 (cornInWX (coordPsi2 X p).1 X) = p.2 :=
  coord_thr hX (coordPsi2_spec hX hp)

end

end QED.ChainProof.SetCK

end
