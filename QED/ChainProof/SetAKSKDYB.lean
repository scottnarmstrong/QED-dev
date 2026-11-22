/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKDShear
public import QED.ChainProof.SetAKSKDElem

/-!
# Set (a), stage D: the inner `y`-integral of the `VB` outer integrand

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification). The reduced outer `VB` integrand `ksDGB` (`SetAKSKDRed`) at an
inner vertex point `x` (`β = x₁/(1 - x₂)`, `γ = x₀/(1 - x₂)`, `τ = x₂(1 - x₂)`) is integrated over
its outer simplex in the sheared coordinates `w = y₁ + βy₂`, `v = y₂` (`SetAKSKDShear`). There
`σ₀ = w`, `σ₁ = c₀ + c₁v` and the denominator is `D = A(w) + bv`, `A(w) = M² + w(1 - w)s`,
`b = E - βs - M²` (`E` the vertex mass `ksNEB`); the numerators are cubic in `v`, so the
`v`-integral is a combination of the moments `ksDJ1`, `ksDJ2` (`SetAKSKDElem`).

Main results:

* `ksD_ksDGB_eq`: the integrand on the simplex in the coordinates `(w, v)`;
* **`ksD_integral_ksDGB`**: `∫_{Δ₂} ksDGB M u x s = ∫₀¹ ksDYB M u x s w dw` for `x` in the open
  simplex, `M > 0`, `s > -4M²`, `u > 0`;
* **`ksD_ksDNestB`**: the nested `VB` integral with the outer simplex integrated out, flavour
  sum inside the `w`-integral.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

open QED.Integration.Feynman (simplexSet simplexPoint isCompact_simplexSet
  measurableSet_simplexSet)
open QED.Integration.ChengWu (openSimplex mem_openSimplex)
open QED.GradedProof.RPi4

/-! ### The data in the sheared coordinates -/

/-- The slope `b = E - βs - M²` of the `VB` denominator in `v = y₂`. -/
noncomputable def ksDbB (M u : ℝ) (x : Fin 3 → ℝ) (s : ℝ) : ℝ :=
  ksNEB M u x s - x 1 / (1 - x 2) * s - M ^ 2

/-- A quadratic `a₀ + a₁σ + a₂σ²` at `σ = c₀ + c₁v`, as coefficients in `v`. -/
def ksDcv (a₀ a₁ a₂ c₀ c₁ : ℝ) : Fin 3 → ℝ :=
  ![a₀ + a₁ * c₀ + a₂ * c₀ ^ 2, a₁ * c₁ + 2 * a₂ * c₀ * c₁, a₂ * c₁ ^ 2]

/-- `σ₁ = c₀ + c₁v`: the constant term. -/
def ksDc0 (x : Fin 3 → ℝ) (w : ℝ) : ℝ := (1 - x 1) * (1 - w) + x 0 * w

/-- `σ₁ = c₀ + c₁v`: the slope. -/
noncomputable def ksDc1 (x : Fin 3 → ℝ) : ℝ :=
  -(1 - x 1) * (1 - x 1 / (1 - x 2)) - x 0 * (x 1 / (1 - x 2)) + x 0 / (1 - x 2)

/-- The coefficients in `v` of the moment `e`. -/
noncomputable def ksDEc (M : ℝ) (x : Fin 3 → ℝ) (w : ℝ) : Fin 3 → ℝ :=
  ksDcv (16 * M ^ 2 * (w ^ 2 - 3 * w + 1)) (16 * M ^ 2 * (4 * w - 3)) (16 * M ^ 2)
    (ksDc0 x w) (ksDc1 x)

/-- The coefficients in `v` of `h₀₀ + 2x₂h₀₁ + x₂²h₁₁`. -/
noncomputable def ksDHc (x : Fin 3 → ℝ) (w : ℝ) : Fin 3 → ℝ :=
  ksDcv (-32 * x 2 * w + 32 * x 2 ^ 2 * w * (w - 1)) (-32 + 32 * x 2 * (2 * w - 1)) 32
    (ksDc0 x w) (ksDc1 x)

/-- **The `VB` integrand in the sheared coordinates** `(w, v)`. -/
noncomputable def ksDYBi (M u : ℝ) (x : Fin 3 → ℝ) (s w v : ℝ) : ℝ :=
  (x 2 * (1 - x 2))⁻¹ * (ksDEc M x w 0 * (v ^ 1 / (ksDA M s w + ksDbB M u x s * v) ^ 2) +
      ksDEc M x w 1 * (v ^ 2 / (ksDA M s w + ksDbB M u x s * v) ^ 2) +
      ksDEc M x w 2 * (v ^ 3 / (ksDA M s w + ksDbB M u x s * v) ^ 2)) +
    (2 * (x 2 * (1 - x 2)))⁻¹ * (ksDHc x w 0 * (v ^ 1 / (ksDA M s w + ksDbB M u x s * v)) +
      ksDHc x w 1 * (v ^ 2 / (ksDA M s w + ksDbB M u x s * v)) +
      ksDHc x w 2 * (v ^ 3 / (ksDA M s w + ksDbB M u x s * v))) +
    16 * w * (w - 1) * (v ^ 0 / (ksDA M s w + ksDbB M u x s * v))

/-- **The `VB` integrand after the inner `y`-integral**, at the outer fraction `w`. -/
noncomputable def ksDYB (M u : ℝ) (x : Fin 3 → ℝ) (s w : ℝ) : ℝ :=
  (x 2 * (1 - x 2))⁻¹ *
      (ksDEc M x w 0 * ksDJ2 (ksDA M s w) (ksDbB M u x s) (ksDYmax (x 1 / (1 - x 2)) w) 1 +
        ksDEc M x w 1 * ksDJ2 (ksDA M s w) (ksDbB M u x s) (ksDYmax (x 1 / (1 - x 2)) w) 2 +
        ksDEc M x w 2 * ksDJ2 (ksDA M s w) (ksDbB M u x s) (ksDYmax (x 1 / (1 - x 2)) w) 3) +
    (2 * (x 2 * (1 - x 2)))⁻¹ *
      (ksDHc x w 0 * ksDJ1 (ksDA M s w) (ksDbB M u x s) (ksDYmax (x 1 / (1 - x 2)) w) 1 +
        ksDHc x w 1 * ksDJ1 (ksDA M s w) (ksDbB M u x s) (ksDYmax (x 1 / (1 - x 2)) w) 2 +
        ksDHc x w 2 * ksDJ1 (ksDA M s w) (ksDbB M u x s) (ksDYmax (x 1 / (1 - x 2)) w) 3) +
    16 * w * (w - 1) * ksDJ1 (ksDA M s w) (ksDbB M u x s) (ksDYmax (x 1 / (1 - x 2)) w) 0

/-! ### The integrand on the simplex -/

theorem ksD_ksDDB_pt (M u : ℝ) (x : Fin 3 → ℝ) (s r t : ℝ) :
    ksDDB M u x s ![r, t, 1 - (r + t)] =
      ksDA M s (t + x 1 / (1 - x 2) * (1 - (r + t))) + ksDbB M u x s * (1 - (r + t)) := by
  simp only [ksDDB, ksDA, ksDbB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hS : r + t + (1 - (r + t)) = 1 := by ring
  rw [hS, div_one]
  ring

theorem ksD_ksDGB_pt (M u : ℝ) (x : Fin 3 → ℝ) (s r t : ℝ) (hx2 : x 2 ≠ 0)
    (hx2' : 1 - x 2 ≠ 0)
    (hD : ksDA M s (t + x 1 / (1 - x 2) * (1 - (r + t))) + ksDbB M u x s * (1 - (r + t)) ≠ 0) :
    ksDGB M u x s ![r, t, 1 - (r + t)] =
      ksDYBi M u x s (t + x 1 / (1 - x 2) * (1 - (r + t))) (1 - (r + t)) := by
  have hDB := ksD_ksDDB_pt M u x s r t
  simp only [ksDGB]
  rw [hDB]
  simp only [ksNSigB0, ksNSigB1, ksNeB, ksNh00, ksNh01, ksNh11, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hS : r + t + (1 - (r + t)) = 1 := by ring
  rw [hS]
  simp only [ksDYBi, ksDEc, ksDHc, ksDcv, ksDc0, ksDc1, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  set D := ksDA M s (t + x 1 / (1 - x 2) * (1 - (r + t))) + ksDbB M u x s * (1 - (r + t))
  field_simp
  ring

/-- On `Δ₂` the `VB` integrand is `ksDYBi` at `w = y₁ + βy₂`, `v = y₂`. -/
theorem ksD_ksDGB_eq (M u : ℝ) (x : Fin 3 → ℝ) (s : ℝ) (y : Fin 2 → ℝ) (hx2 : x 2 ≠ 0)
    (hx2' : 1 - x 2 ≠ 0)
    (hD : ksDA M s (y 1 + x 1 / (1 - x 2) * (1 - (y 0 + y 1))) +
      ksDbB M u x s * (1 - (y 0 + y 1)) ≠ 0) :
    ksDGB M u x s (simplexPoint y) =
      ksDYBi M u x s (y 1 + x 1 / (1 - x 2) * (1 - (y 0 + y 1))) (1 - (y 0 + y 1)) := by
  have hy : y = ![y 0, y 1] := by ext i; fin_cases i <;> rfl
  rw [hy, ksD_simplexPoint_two]
  exact ksD_ksDGB_pt M u x s (y 0) (y 1) hx2 hx2' hD

/-! ### Positivity on the open simplex -/

theorem ksD_pt_sum (q : Fin 2 → ℝ) :
    simplexPoint q 0 + simplexPoint q 1 + simplexPoint q 2 = 1 := by
  have h := QED.Integration.TwoLoop.sum_simplexPoint q
  rw [Fin.sum_univ_three] at h
  exact h

theorem ksD_ksDbB_eq (M u : ℝ) (x : Fin 3 → ℝ) (s : ℝ) (hsum : x 0 + x 1 + x 2 = 1)
    (hx2 : x 2 ≠ 0) (hx2' : 1 - x 2 ≠ 0) :
    ksDbB M u x s = (M ^ 2 * (1 - x 2) ^ 2 + x 0 * x 1 * s) / (x 2 * (1 - x 2)) +
      u / (1 - x 2) := by
  simp only [ksDbB, ksNEB]
  have hx0 : x 0 = 1 - x 1 - x 2 := by linarith
  rw [hx0]
  field_simp
  ring

section Pos

variable {q : Fin 2 → ℝ} (hq : q ∈ openSimplex 2)
include hq

theorem ksD_pt_pos (i : Fin 3) : 0 < simplexPoint q i := by
  obtain ⟨h0, h1⟩ := mem_openSimplex.1 hq
  rw [Fin.sum_univ_two] at h1
  fin_cases i
  · exact (QED.Integration.TwoLoop.simplexPoint_castSucc q 0).symm ▸ h0 0
  · exact (QED.Integration.TwoLoop.simplexPoint_castSucc q 1).symm ▸ h0 1
  · have h := QED.Integration.TwoLoop.simplexPoint_last q
    simp only [Fin.sum_univ_two] at h
    show 0 < simplexPoint q (Fin.last 2)
    rw [h]
    linarith

theorem ksD_beta_mem : simplexPoint q 1 / (1 - simplexPoint q 2) ∈ Ioo (0 : ℝ) 1 := by
  have h0 := ksD_pt_pos hq 0
  have h1 := ksD_pt_pos hq 1
  have hs := ksD_pt_sum q
  have h2 : 0 < 1 - simplexPoint q 2 := by linarith
  exact ⟨div_pos h1 h2, (div_lt_one h2).2 (by linarith)⟩

theorem ksD_ksDbB_pos {M u s : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) (hu : 0 < u) :
    0 < ksDbB M u (simplexPoint q) s := by
  have h0 := ksD_pt_pos hq 0
  have h1 := ksD_pt_pos hq 1
  have h2 := ksD_pt_pos hq 2
  have hsum := ksD_pt_sum q
  have he := ksD_ksDbB_eq M u (simplexPoint q) s hsum h2.ne' (by linarith)
  set x0 := simplexPoint q 0
  set x1 := simplexPoint q 1
  set x2 := simplexPoint q 2
  have h12 : 0 < 1 - x2 := by linarith
  rw [he]
  have hN : 0 < M ^ 2 * (1 - x2) ^ 2 + x0 * x1 * s := by
    have hq4 : x0 * x1 ≤ (1 - x2) ^ 2 / 4 := by nlinarith [sq_nonneg (x0 - x1)]
    have hp : 0 < M ^ 2 * (1 - x2) ^ 2 := by positivity
    rcases le_or_gt 0 s with hs0 | hs0
    · nlinarith [mul_nonneg (mul_nonneg h0.le h1.le) hs0]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (1 - x2) ^ 2 / 4 - x0 * x1)
        (by linarith : 0 ≤ -s)]
  have := div_pos hN (mul_pos h2 h12)
  have := div_pos hu h12
  linarith

end Pos

/-! ### The inner integral -/

theorem ksD_integral_ksDYBi {M u s w : ℝ} (x : Fin 3 → ℝ) {Y : ℝ} (hA : 0 < ksDA M s w)
    (hb : 0 < ksDbB M u x s) (hY : 0 ≤ Y) :
    ∫ v in (0 : ℝ)..Y, ksDYBi M u x s w v =
      (x 2 * (1 - x 2))⁻¹ *
          (ksDEc M x w 0 * ksDJ2 (ksDA M s w) (ksDbB M u x s) Y 1 +
            ksDEc M x w 1 * ksDJ2 (ksDA M s w) (ksDbB M u x s) Y 2 +
            ksDEc M x w 2 * ksDJ2 (ksDA M s w) (ksDbB M u x s) Y 3) +
        (2 * (x 2 * (1 - x 2)))⁻¹ *
          (ksDHc x w 0 * ksDJ1 (ksDA M s w) (ksDbB M u x s) Y 1 +
            ksDHc x w 1 * ksDJ1 (ksDA M s w) (ksDbB M u x s) Y 2 +
            ksDHc x w 2 * ksDJ1 (ksDA M s w) (ksDbB M u x s) Y 3) +
        16 * w * (w - 1) * ksDJ1 (ksDA M s w) (ksDbB M u x s) Y 0 := by
  have I := ksD_intervalIntegrable_J hA hb hY
  have I1 : ∀ p, IntervalIntegrable
      (fun v : ℝ => v ^ p / (ksDA M s w + ksDbB M u x s * v)) volume 0 Y := fun p => by
    simpa using I p 1
  have e1 := (I 1 2).const_mul (ksDEc M x w 0)
  have e2 := (I 2 2).const_mul (ksDEc M x w 1)
  have e3 := (I 3 2).const_mul (ksDEc M x w 2)
  have h1 := (I1 1).const_mul (ksDHc x w 0)
  have h2 := (I1 2).const_mul (ksDHc x w 1)
  have h3 := (I1 3).const_mul (ksDHc x w 2)
  have hl := (I1 0).const_mul (16 * w * (w - 1))
  have hE := ((e1.add e2).add e3).const_mul (x 2 * (1 - x 2))⁻¹
  have hH := ((h1.add h2).add h3).const_mul (2 * (x 2 * (1 - x 2)))⁻¹
  simp only [ksDYBi]
  rw [intervalIntegral.integral_add (hE.add hH) hl, intervalIntegral.integral_add hE hH,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (e1.add e2) e3, intervalIntegral.integral_add e1 e2,
    intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul, ksD_integral_J1 hA hb hY,
    ksD_integral_J2 hA hb hY]

/-- The point `(w - βv, v)` of the sheared coordinates has `w(y) = w` and `v(y) = v`. -/
theorem ksD_ksDPt_coords (β w v : ℝ) :
    (ksDPt (w - β * v) v) 1 + β * (1 - ((ksDPt (w - β * v) v) 0 + (ksDPt (w - β * v) v) 1)) =
      w ∧ 1 - ((ksDPt (w - β * v) v) 0 + (ksDPt (w - β * v) v) 1) = v := by
  simp only [ksDPt, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> ring

theorem ksD_w_mem {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) {y : Fin 2 → ℝ} (hy : y ∈ simplexSet 2) :
    y 1 + β * (1 - (y 0 + y 1)) ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ 1 - (y 0 + y 1) := by
  rw [QED.Integration.SimplexMerge.mem_simplexSet_iff_le (by norm_num), Fin.sum_univ_two] at hy
  obtain ⟨h0, h1⟩ := hy
  have hv : 0 ≤ 1 - (y 0 + y 1) := by linarith
  have := mul_nonneg hβ.1.le hv
  have : β * (1 - (y 0 + y 1)) ≤ 1 - (y 0 + y 1) := by nlinarith [hβ.2]
  exact ⟨⟨by linarith [h0 1], by linarith [h0 0]⟩, hv⟩

/-- The `VB` integrand is continuous on `Δ₂`, and its inner `y`-integral in closed form. -/
theorem ksD_ksDGB_aux {M u s : ℝ} {q : Fin 2 → ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hq : q ∈ openSimplex 2) (hu : 0 < u) :
    ContinuousOn (fun y => ksDGB M u (simplexPoint q) s (simplexPoint y)) (simplexSet 2) ∧
    ∫ y in simplexSet 2, ksDGB M u (simplexPoint q) s (simplexPoint y) =
      ∫ w in (0 : ℝ)..1, ksDYB M u (simplexPoint q) s w := by
  set x := simplexPoint q with hxdef
  have hx2 : x 2 ≠ 0 := (ksD_pt_pos hq 2).ne'
  have hx2' : 1 - x 2 ≠ 0 := by
    have := ksD_pt_pos hq 0; have := ksD_pt_pos hq 1; have := ksD_pt_sum q
    simp only [hxdef] at *; linarith
  have hβ := ksD_beta_mem hq
  have hb := ksD_ksDbB_pos hq hM hs hu
  set β := x 1 / (1 - x 2) with hβdef
  -- the denominator is positive on the simplex
  have hDpos : ∀ y ∈ simplexSet 2, 0 < ksDA M s (y 1 + β * (1 - (y 0 + y 1))) +
      ksDbB M u x s * (1 - (y 0 + y 1)) := fun y hy => by
    obtain ⟨hw, hv⟩ := ksD_w_mem hβ hy
    have := ksD_ksDA_pos hM hs hw
    have := mul_nonneg hb.le hv
    linarith
  have hcont : ContinuousOn (fun y => ksDGB M u x s (simplexPoint y)) (simplexSet 2) := by
    refine ContinuousOn.congr (f := fun y : Fin 2 → ℝ =>
      ksDYBi M u x s (y 1 + β * (1 - (y 0 + y 1))) (1 - (y 0 + y 1))) ?_
      fun y hy => ksD_ksDGB_eq M u x s y hx2 hx2' (hDpos y hy).ne'
    intro y hy
    have hD := (hDpos y hy).ne'
    refine ContinuousAt.continuousWithinAt ?_
    have cD : Continuous fun y : Fin 2 → ℝ => ksDA M s (y 1 + β * (1 - (y 0 + y 1))) +
        ksDbB M u x s * (1 - (y 0 + y 1)) := by simp only [ksDA]; fun_prop
    have cw : Continuous fun y : Fin 2 → ℝ => y 1 + β * (1 - (y 0 + y 1)) := by fun_prop
    have cv : Continuous fun y : Fin 2 → ℝ => 1 - (y 0 + y 1) := by fun_prop
    have cE : ∀ i, Continuous fun y : Fin 2 → ℝ => ksDEc M x (y 1 + β * (1 - (y 0 + y 1))) i :=
      fun i => by fin_cases i <;> simp [ksDEc, ksDcv, ksDc0] <;> fun_prop
    have cH : ∀ i, Continuous fun y : Fin 2 → ℝ => ksDHc x (y 1 + β * (1 - (y 0 + y 1))) i :=
      fun i => by fin_cases i <;> simp [ksDHc, ksDcv, ksDc0] <;> fun_prop
    have cq : ∀ (p k : ℕ), ContinuousAt (fun y : Fin 2 → ℝ => (1 - (y 0 + y 1)) ^ p /
        (ksDA M s (y 1 + β * (1 - (y 0 + y 1))) + ksDbB M u x s * (1 - (y 0 + y 1))) ^ k) y :=
      fun p k => (cv.pow p).continuousAt.div (cD.pow k).continuousAt (pow_ne_zero k hD)
    have cq1 : ∀ p : ℕ, ContinuousAt (fun y : Fin 2 → ℝ => (1 - (y 0 + y 1)) ^ p /
        (ksDA M s (y 1 + β * (1 - (y 0 + y 1))) + ksDbB M u x s * (1 - (y 0 + y 1)))) y :=
      fun p => (cv.pow p).continuousAt.div cD.continuousAt hD
    show ContinuousAt (fun y : Fin 2 → ℝ =>
      ksDYBi M u x s (y 1 + β * (1 - (y 0 + y 1))) (1 - (y 0 + y 1))) y
    simp only [ksDYBi]
    refine ((continuousAt_const.mul ((((cE 0).continuousAt.mul (cq 1 2)).add
      ((cE 1).continuousAt.mul (cq 2 2))).add ((cE 2).continuousAt.mul (cq 3 2)))).add
      (continuousAt_const.mul ((((cH 0).continuousAt.mul (cq1 1)).add
      ((cH 1).continuousAt.mul (cq1 2))).add ((cH 2).continuousAt.mul (cq1 3))))).add
      (((continuousAt_const.mul cw.continuousAt).mul (cw.continuousAt.sub
        continuousAt_const)).mul (cq1 0))
  refine ⟨hcont, ?_⟩
  rw [ksD_integral_simplexTwo_shear hcont hβ]
  refine intervalIntegral.integral_congr fun w hw => ?_
  rw [uIcc_of_le zero_le_one] at hw
  have hY := ksD_ksDYmax_nonneg hβ hw
  have hA := ksD_ksDA_pos hM hs hw
  have hin : ∀ v ∈ uIcc (0 : ℝ) (ksDYmax β w),
      ksDGB M u x s (simplexPoint (ksDPt (w - β * v) v)) = ksDYBi M u x s w v := by
    intro v hv
    rw [uIcc_of_le hY] at hv
    obtain ⟨c1, c2⟩ := ksD_ksDPt_coords β w v
    have hD : 0 < ksDA M s w + ksDbB M u x s * v := by
      have := mul_nonneg hb.le hv.1; linarith
    rw [ksD_ksDGB_eq M u x s _ hx2 hx2' (by rw [c1, c2]; exact hD.ne'), c1, c2]
  rw [intervalIntegral.integral_congr hin, ksD_integral_ksDYBi x hA hb hY]
  rfl

/-- **The inner `y`-integral of `VB`** in closed form, at an inner point of the open simplex. -/
theorem ksD_integral_ksDGB {M u s : ℝ} {q : Fin 2 → ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hq : q ∈ openSimplex 2) (hu : 0 < u) :
    ∫ y in simplexSet 2, ksDGB M u (simplexPoint q) s (simplexPoint y) =
      ∫ w in (0 : ℝ)..1, ksDYB M u (simplexPoint q) s w :=
  (ksD_ksDGB_aux hM hs hq hu).2

/-- **The nested `VB` integral with the outer simplex integrated out** (flavour sum inside the
`q`-integral). -/
theorem ksD_ksDNestB {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {u s : ℝ}
    (hM : ∀ f, 0 < Φ.mass f) (hs : ∀ f, -(4 * Φ.mass f ^ 2) < s) (hu : 0 < u) :
    ksDNestB Φ u s = ∫ q in simplexSet 2, (1 - simplexPoint q 2)⁻¹ *
      ∑ f, Φ.coeff f * ∫ w in (0 : ℝ)..1, ksDYB (Φ.mass f) u (simplexPoint q) s w := by
  refine setIntegral_congr_ae (measurableSet_simplexSet 2) ?_
  have h := QED.Integration.ChengWu.simplexSet_ae_eq_openSimplex (⟨0, two_pos⟩ : Fin 2)
  filter_upwards [h.mem_iff] with q hq hqs
  have hq' : q ∈ openSimplex 2 := hq.mp hqs
  congr 1
  rw [integral_finsetSum _ fun f _ =>
    ((ksD_ksDGB_aux (hM f) (hs f) hq' hu).1.integrableOn_compact
      (isCompact_simplexSet 2)).const_mul _]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MeasureTheory.integral_const_mul, ksD_integral_ksDGB (hM f) (hs f) hq' hu]

/-- The same at the configuration `decCfg μ x`, for `s > -4μ²`. -/
theorem ksD_ksDNestB_cfg {μ x u s : ℝ} (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) (hs : -(4 * μ ^ 2) < s)
    (hu : 0 < u) :
    ksDNestB (decCfg μ x) u s = ∫ q in simplexSet 2, (1 - simplexPoint q 2)⁻¹ *
      ∑ f, (decCfg μ x).coeff f * ∫ w in (0 : ℝ)..1,
        ksDYB ((decCfg μ x).mass f) u (simplexPoint q) s w := by
  refine ksD_ksDNestB _ (fun f => hμ.trans_le (ksK_mass hμ hx f)) (fun f => ?_) hu
  have h := ksK_mass hμ hx f
  nlinarith

end QED.ChainProof.SetAKS

end
