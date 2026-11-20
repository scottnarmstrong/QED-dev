/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCoordMaps
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the Jacobians of the threshold coordinates

Helper level (no frozen statement). The two inverse maps `coordPsi1`, `coordPsi2` of the
threshold coordinates `(u, s)` (`SetCKCoordMaps`) are differentiable on their regions, with
derivatives `coordDer1`, `coordDer2` written as `2 × 2` matrices of partial derivatives
(`coordMat`, `coord_hasFDerivAt_of_partials`). Their Jacobians are, in absolute value,

`J₁ = (X-u)(1-X)²(X+u-Xu)/(s² M³)` (`coordJ1`) and
`J₂ = (X-u)(1-X)(2-s)(u-X(1-s))(X+u-Xu)(X(1-s)+(1-X)u)/(s² D³)` (`coordJ2`):

**`abs_det_coordDer1`**, **`abs_det_coordDer2`**, with **`hasFDerivAt_coordPsi1`**,
**`hasFDerivAt_coordPsi2`**.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

/-- The linear map of `ℝ × ℝ` with matrix `[[a, b], [c, d]]`. -/
noncomputable def coordMat (a b c d : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (c • ContinuousLinearMap.fst ℝ ℝ ℝ + d • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem det_coordMat (a b c d : ℝ) : (coordMat a b c d).det = a * d - b * c := by
  unfold coordMat
  rw [← Matrix.toLin_finTwoProd_toContinuousLinearMap, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin, Matrix.det_fin_two_of]

/-- **Fréchet derivative from partial derivatives** for a differentiable `f : ℝ × ℝ → ℝ`. -/
theorem coord_hasFDerivAt_of_partials {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {a b : ℝ}
    (hf : DifferentiableAt ℝ f p) (ha : HasDerivAt (fun u => f (u, p.2)) a p.1)
    (hb : HasDerivAt (fun s => f (p.1, s)) b p.2) :
    HasFDerivAt f (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have h := hf.hasFDerivAt
  have h1 : HasDerivAt (fun u => f (u, p.2)) (fderiv ℝ f p (1, 0)) p.1 :=
    h.comp_hasDerivAt (x := p.1) (f := fun u => (u, p.2))
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have h2 : HasDerivAt (fun s => f (p.1, s)) (fderiv ℝ f p (0, 1)) p.2 :=
    h.comp_hasDerivAt (x := p.2) (f := fun s => (p.1, s))
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  rw [ha.unique h1, hb.unique h2]
  convert h using 1
  refine ContinuousLinearMap.ext fun q => ?_
  have e : q = q.1 • ((1 : ℝ), (0 : ℝ)) + q.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_rhs => rw [e, map_add, map_smul, map_smul]
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- The `2 × 2` version: both components through their partial derivatives. -/
theorem coord_hasFDerivAt_mat {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {a b c d : ℝ}
    (hf : DifferentiableAt ℝ f p) (ha : HasDerivAt (fun u => f (u, p.2)) a p.1)
    (hb : HasDerivAt (fun s => f (p.1, s)) b p.2) (hg : DifferentiableAt ℝ g p)
    (hc : HasDerivAt (fun u => g (u, p.2)) c p.1) (hd : HasDerivAt (fun s => g (p.1, s)) d p.2) :
    HasFDerivAt (fun q => (f q, g q)) (coordMat a b c d) p :=
  (coord_hasFDerivAt_of_partials hf ha hb).prodMk (coord_hasFDerivAt_of_partials hg hc hd)

/-- **The branch-1 Jacobian** `J₁`. -/
noncomputable def coordJ1 (X u s : ℝ) : ℝ :=
  (X - u) * (1 - X) ^ 2 * (X + u - X * u) / (s ^ 2 * coordM X u ^ 3)

/-- **The branch-2 Jacobian** `J₂`. -/
noncomputable def coordJ2 (X u s : ℝ) : ℝ :=
  (X - u) * (1 - X) * (2 - s) * (u - X * (1 - s)) * (X + u - X * u) *
    (X * (1 - s) + (1 - X) * u) / (s ^ 2 * coordD X u s ^ 3)

/-- `dY/du` on branch 1. -/
noncomputable def coordDY1 (X u : ℝ) : ℝ := (1 - X) ^ 2 / coordM X u ^ 2

theorem hasDerivAt_coordY1 {X u : ℝ} (hM : coordM X u ≠ 0) :
    HasDerivAt (coordY1 X) (coordDY1 X u) u := by
  have hN : HasDerivAt (fun u : ℝ => X ^ 2 + (1 - X) * u) (1 - X) u := by
    simpa using ((hasDerivAt_id u).const_mul (1 - X)).const_add (X ^ 2)
  have hD : HasDerivAt (fun u : ℝ => coordM X u) (1 - X) u := by
    unfold coordM
    simpa using (((hasDerivAt_id u).const_add 1).const_mul (1 - X)).const_add (X ^ 2)
  refine (hN.div hD hM).congr_deriv ?_
  unfold coordDY1
  field_simp
  unfold coordM
  ring

/-- **The derivative of the branch-1 map.** -/
noncomputable def coordDer1 (X : ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  coordMat (coordDY1 X p.1) 0 ((coordDY1 X p.1 - 1) / p.2) (-((coordY1 X p.1 - p.1) / p.2 ^ 2))

theorem hasFDerivAt_coordPsi1 {X : ℝ} {p : ℝ × ℝ} (hM : coordM X p.1 ≠ 0) (hs : p.2 ≠ 0) :
    HasFDerivAt (coordPsi1 X) (coordDer1 X p) p := by
  have hY := hasDerivAt_coordY1 hM
  have hYd : DifferentiableAt ℝ (fun q : ℝ × ℝ => coordY1 X q.1) p :=
    DifferentiableAt.comp (x := p) hY.differentiableAt differentiableAt_fst
  refine coord_hasFDerivAt_mat hYd hY (hasDerivAt_const p.2 (coordY1 X p.1)) ?_ ?_ ?_
  · have := hY.differentiableAt
    fun_prop (disch := exact hs)
  · exact (hY.sub (hasDerivAt_id _)).div_const _
  · simpa [div_eq_mul_inv, pow_two, mul_inv] using
      (hasDerivAt_inv hs).const_mul (coordY1 X p.1 - p.1)

theorem abs_det_coordDer1 {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ coordR1 X) :
    |(coordDer1 X p).det| = coordJ1 X p.1 p.2 := by
  obtain ⟨⟨hu0, huX⟩, hsl, hsu⟩ := hp
  have hsp := (coordPsi1_spec hX ⟨⟨hu0, huX⟩, hsl, hsu⟩).2.1
  have hM := coordM_pos hX hu0.le
  have hJ : 0 ≤ coordJ1 X p.1 p.2 := by
    unfold coordJ1
    have : 0 < X + p.1 - X * p.1 := by nlinarith [hX.2]
    have : 0 < X - p.1 := by linarith
    positivity
  rw [coordDer1, det_coordMat, ← abs_of_nonneg hJ, abs_eq_abs]
  right
  unfold coordJ1 coordDY1 coordY1
  field_simp
  unfold coordM
  ring

/-- A quadratic in one variable, for the partial derivatives of the branch-2 map. -/
theorem coord_hasDerivAt_quad {f : ℝ → ℝ} {f' a b c x : ℝ}
    (hf : ∀ t, f t = a + b * t + c * t ^ 2) (hf' : f' = b + 2 * c * x) : HasDerivAt f f' x := by
  have h := (((hasDerivAt_id x).const_mul b).const_add a).add ((hasDerivAt_pow 2 x).const_mul c)
  rw [show f = fun t => a + b * id t + c * t ^ 2 from funext hf, hf']
  convert h using 1
  simp only [Nat.cast_ofNat]
  ring

/-- **The derivative of the branch-2 map**, by the quotient rule in each variable. -/
noncomputable def coordDer2 (X : ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  let u := p.1
  let s := p.2
  let N := X ^ 2 * (1 - s) + (1 - X) * u ^ 2
  let P := (X - u) * (1 - s) * (X + u - X * u)
  let D := coordD X u s
  coordMat ((2 * (1 - X) * u * D - N * ((1 - X) * (2 - s))) / D ^ 2)
    ((-X ^ 2 * D - N * (-X ^ 2 - (1 - X) * u)) / D ^ 2)
    (((1 - s) * ((X - u) * (1 - X) - (X + u - X * u)) * (s * D) -
      P * (s * ((1 - X) * (2 - s)))) / (s * D) ^ 2)
    ((-((X - u) * (X + u - X * u)) * (s * D) - P * (D + s * (-X ^ 2 - (1 - X) * u))) /
      (s * D) ^ 2)

theorem hasFDerivAt_coordPsi2 {X : ℝ} {p : ℝ × ℝ} (hD : coordD X p.1 p.2 ≠ 0)
    (hs : p.2 ≠ 0) : HasFDerivAt (coordPsi2 X) (coordDer2 X p) p := by
  obtain ⟨u, s⟩ := p
  simp only at hD hs
  have hsD : s * coordD X u s ≠ 0 := mul_ne_zero hs hD
  -- `u`-derivatives at fixed `s`
  have hNu : HasDerivAt (fun u => X ^ 2 * (1 - s) + (1 - X) * u ^ 2) (2 * (1 - X) * u) u :=
    coord_hasDerivAt_quad (a := X ^ 2 * (1 - s)) (b := 0) (c := 1 - X) (fun t => by ring)
      (by ring)
  have hDu : HasDerivAt (fun u => coordD X u s) ((1 - X) * (2 - s)) u :=
    coord_hasDerivAt_quad (a := X ^ 2 * (1 - s)) (b := (1 - X) * (2 - s)) (c := 0)
      (fun t => by unfold coordD; ring) (by ring)
  have hPu : HasDerivAt (fun u => (X - u) * (1 - s) * (X + u - X * u))
      ((1 - s) * ((X - u) * (1 - X) - (X + u - X * u))) u :=
    coord_hasDerivAt_quad (a := X ^ 2 * (1 - s)) (b := -(1 - s) * X ^ 2)
      (c := -(1 - s) * (1 - X)) (fun t => by ring) (by ring)
  have hsDu : HasDerivAt (fun u => s * coordD X u s) (s * ((1 - X) * (2 - s))) u :=
    hDu.const_mul s
  -- `s`-derivatives at fixed `u`
  have hNs : HasDerivAt (fun s => X ^ 2 * (1 - s) + (1 - X) * u ^ 2) (-X ^ 2) s :=
    coord_hasDerivAt_quad (a := X ^ 2 + (1 - X) * u ^ 2) (b := -X ^ 2) (c := 0)
      (fun t => by ring) (by ring)
  have hDs : HasDerivAt (fun s => coordD X u s) (-X ^ 2 - (1 - X) * u) s :=
    coord_hasDerivAt_quad (a := X ^ 2 + 2 * (1 - X) * u) (b := -X ^ 2 - (1 - X) * u) (c := 0)
      (fun t => by unfold coordD; ring) (by ring)
  have hPs : HasDerivAt (fun s => (X - u) * (1 - s) * (X + u - X * u))
      (-((X - u) * (X + u - X * u))) s :=
    coord_hasDerivAt_quad (a := (X - u) * (X + u - X * u)) (b := -((X - u) * (X + u - X * u)))
      (c := 0) (fun t => by ring) (by ring)
  have hsDs : HasDerivAt (fun s => s * coordD X u s)
      (coordD X u s + s * (-X ^ 2 - (1 - X) * u)) s :=
    ((hasDerivAt_id' s).mul hDs).congr_deriv (by ring)
  have hY : DifferentiableAt ℝ (fun q : ℝ × ℝ => coordY2 X q.1 q.2) (u, s) := by
    unfold coordY2 coordD
    unfold coordD at hD
    fun_prop (disch := exact hD)
  have hZ : DifferentiableAt ℝ (fun q : ℝ × ℝ => coordZ2 X q.1 q.2) (u, s) := by
    unfold coordZ2 coordD
    unfold coordD at hsD
    fun_prop (disch := exact hsD)
  exact coord_hasFDerivAt_mat hY (hNu.div hDu hD) (hNs.div hDs hD) hZ (hPu.div hsDu hsD)
    (hPs.div hsDs hsD)

theorem abs_det_coordDer2 {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ coordR2 X) :
    |(coordDer2 X p).det| = coordJ2 X p.1 p.2 := by
  obtain ⟨u, s⟩ := p
  obtain ⟨⟨hu0, huX⟩, hsl, hs1⟩ := hp
  simp only at hu0 huX hsl hs1
  have hX0 := hX.1
  have h1X : 0 < 1 - X := by linarith [hX.2]
  have hD := coordD_pos hX hu0 hs1
  have hs0 : 0 < s := by linarith
  have hXu : 0 < X - u := by linarith
  have hA : 0 < X + u - X * u := by nlinarith
  have hB : 0 < u - X * (1 - s) := by nlinarith
  have hC : 0 < X * (1 - s) + (1 - X) * u := by positivity
  have h2s : 0 < 2 - s := by linarith
  have hJ : 0 ≤ coordJ2 X u s := by unfold coordJ2; positivity
  rw [coordDer2, det_coordMat, ← abs_of_nonneg hJ, abs_eq_abs]
  right
  simp only
  unfold coordJ2
  have := hD.ne'
  field_simp
  unfold coordD
  ring

end QED.ChainProof.SetCK

end
