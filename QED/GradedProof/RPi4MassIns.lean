/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4WWard

/-!
# (R-Π₄) step L3, pointwise: the mass insertion is the mass derivative of the bubble

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L3.

After L2 the insertion classes enter only at the pure mass insertion `ctδ D`
(`QED.GradedProof.RPi4.pol_eq_piCl_ctδ`), with the block constant `δ = e² (d_m - d₂)`. The class
`F0` inserts `δ M` on the line `q`, the class `F1` on the line `k + q` of the same loop momentum
`q`. With `N = M - p̸`, `N² = 2M N - (p² + M²)` and `p² + M² = D + iε`, the sum of the two is,
pointwise in `q`, the mass derivative of the bubble up to `iε`:

* `hasDerivAt_bub`, `hasDerivAt_bubbleW`: `∂_M` of the bubble `Tr[A N_x B N_y] D_x⁻¹ D_y⁻¹`
  (explicit, `dBub`, `dBubbleW`);
* `kF_insG_F0_add_F1`: per flavour,
  `κ_F (insG_F0 + insG_F1)[d₂ = 0, d_m = d] = d M ∂_M bubbleW - iε d remM`, with the
  three-propagator remainder `remM = κ_F M² Tr[A B] (D_x⁻² D_y⁻¹ + D_x⁻¹ D_y⁻²)`;
* `fBubble_ctδ_F0_add_F1` (**L3, pointwise**): the block-summed integrands,
  `F0[ctδ] + F1[ctδ] = ∑_f c_f δ_f M_f ∂_M bubbleW(M_f) - iε ∑_f c_f δ_f remM(M_f)`.

Checked numerically (scratchpad `l3num.py`): the projected, subtracted block integral of the
unit mass insertion is `-(1/4) ∑ c_f M_f ∂_{M_f} Π̂₂(s/M_f²)` in `(α/π)` units, to four digits at
`s = 0.3 … 8` for the blocks `(1, 4, 7)` and `(1, 2.5, 3)`.
-/

@[expose] public section

open Complex
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2

namespace QED.GradedProof.RPi4

open QED.TwoLoop.Bridge (electronNumerator propDenom propDenom_ne_zero)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### One bubble -/

/-- `Tr[A (M - x̸) B] = M Tr[A B]` for odd `A`, `B`. -/
theorem trace_num_mid {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (M : ℝ) (x : Fin 4 → ℝ) :
    (A * electronNumerator M x * B).trace = (M : ℂ) * (A * B).trace := by
  have h : (A * (Dirac.slash x * B)).trace = 0 := IsOddG.trace3 hA (isOddG_slash x) hB
  simp only [electronNumerator, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, Matrix.mul_assoc,
    smul_eq_mul, h, sub_zero]

/-- `Tr[A B (M - y̸)] = M Tr[A B]` for odd `A`, `B`. -/
theorem trace_mul_num {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (M : ℝ) (y : Fin 4 → ℝ) :
    (A * B * electronNumerator M y).trace = (M : ℂ) * (A * B).trace := by
  have h : (A * (B * Dirac.slash y)).trace = 0 := IsOddG.trace3 hA hB (isOddG_slash y)
  simp only [electronNumerator, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.mul_assoc, smul_eq_mul, h, sub_zero]

/-- `N² = 2M N - (y² + M²)` for `N = M - y̸`. -/
theorem num_mul_num (M : ℝ) (y : Fin 4 → ℝ) :
    electronNumerator M y * electronNumerator M y =
      ((2 * M : ℝ) : ℂ) • electronNumerator M y -
        ((Minkowski.dot y y + M ^ 2 : ℝ) : ℂ) • (1 : Mat) := by
  have hs := QED.Dirac.slash_mul_slash y
  simp only [electronNumerator, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hs]
  push_cast
  module

/-- **The mass insertion on the line `y`**: `Tr[A N_x B N_y²] = 2M Tr[A N_x B N_y] - (y² + M²)
M Tr[A B]`. -/
theorem massTr_eq {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (M : ℝ) (x y : Fin 4 → ℝ) :
    massTr A B M x y = 2 * (M : ℂ) * bubTr A B M x y -
      ((Minkowski.dot y y + M ^ 2 : ℝ) : ℂ) * ((M : ℂ) * (A * B).trace) := by
  rw [massTr, num_mul_num, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.mul_one, trace_num_mid hA hB, smul_eq_mul,
    smul_eq_mul, bubTr]
  push_cast
  ring

/-- The `M`-derivative of the bubble `Tr[A N_x B N_y] D_x⁻¹ D_y⁻¹`. -/
noncomputable def dBub (A B : Mat) (M ε : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  2 * (M : ℂ) * (A * B).trace * (propDenom M ε x)⁻¹ * (propDenom M ε y)⁻¹ -
    2 * (M : ℂ) * bubTr A B M x y * ((propDenom M ε x)⁻¹ ^ 2 * (propDenom M ε y)⁻¹ +
      (propDenom M ε x)⁻¹ * (propDenom M ε y)⁻¹ ^ 2)

theorem propDenom_eq_add (M ε : ℝ) (p : Fin 4 → ℝ) :
    propDenom M ε p = ((Minkowski.dot p p : ℝ) : ℂ) - (ε : ℂ) * I + (M : ℂ) ^ 2 := by
  simp only [propDenom]
  push_cast
  ring

/-- **The mass derivative of the bubble** at `ε ≠ 0`. -/
theorem hasDerivAt_bub {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) {ε : ℝ} (hε : ε ≠ 0)
    (x y : Fin 4 → ℝ) (M : ℝ) :
    HasDerivAt (fun M : ℝ => bubTr A B M x y * (propDenom M ε x)⁻¹ * (propDenom M ε y)⁻¹)
      (dBub A B M ε x y) M := by
  set T₀ := (A * (Dirac.slash x * (B * Dirac.slash y))).trace
  set t := (A * B).trace
  set a : ℂ := ((Minkowski.dot x x : ℝ) : ℂ) - (ε : ℂ) * I
  set b : ℂ := ((Minkowski.dot y y : ℝ) : ℂ) - (ε : ℂ) * I
  have hfun : (fun M : ℝ => bubTr A B M x y * (propDenom M ε x)⁻¹ * (propDenom M ε y)⁻¹) =
      fun M : ℝ => (fun z : ℂ => (T₀ + z ^ 2 * t) * (a + z ^ 2)⁻¹ * (b + z ^ 2)⁻¹) (M : ℂ) := by
    funext M
    simp only [bubTr_eq hA hB, propDenom_eq_add]
    ring
  have ha : a + (M : ℂ) ^ 2 ≠ 0 := by
    rw [show a + (M : ℂ) ^ 2 = propDenom M ε x from (propDenom_eq_add M ε x).symm]
    exact propDenom_ne_zero hε x
  have hb : b + (M : ℂ) ^ 2 ≠ 0 := by
    rw [show b + (M : ℂ) ^ 2 = propDenom M ε y from (propDenom_eq_add M ε y).symm]
    exact propDenom_ne_zero hε y
  have h1 : HasDerivAt (fun z : ℂ => T₀ + z ^ 2 * t) (2 * (M : ℂ) * t) (M : ℂ) := by
    simpa using ((hasDerivAt_pow 2 (M : ℂ)).mul_const t).const_add T₀
  have h2 : HasDerivAt (fun z : ℂ => (a + z ^ 2)⁻¹)
      (-(2 * (M : ℂ)) * ((a + (M : ℂ) ^ 2)⁻¹) ^ 2) (M : ℂ) := by
    exact (((hasDerivAt_pow 2 (M : ℂ)).const_add a).inv ha).congr_deriv
      (by simp only [div_eq_mul_inv, ← inv_pow]; push_cast; ring)
  have h3 : HasDerivAt (fun z : ℂ => (b + z ^ 2)⁻¹)
      (-(2 * (M : ℂ)) * ((b + (M : ℂ) ^ 2)⁻¹) ^ 2) (M : ℂ) := by
    exact (((hasDerivAt_pow 2 (M : ℂ)).const_add b).inv hb).congr_deriv
      (by simp only [div_eq_mul_inv, ← inv_pow]; push_cast; ring)
  rw [hfun]
  refine (HasDerivAt.comp_ofReal ((h1.mul h2).mul h3)).congr_deriv ?_
  rw [dBub, bubTr_eq hA hB, show propDenom M ε x = a + (M : ℂ) ^ 2 from propDenom_eq_add M ε x,
    show propDenom M ε y = b + (M : ℂ) ^ 2 from propDenom_eq_add M ε y]
  simp only [Pi.mul_apply]
  ring

/-! ### The two insertions of the classes `F0`, `F1` -/

/-- **The mass derivative of the bubble `bubbleW`** (the bubble of the classes `G0`, `G1`). -/
noncomputable def dBubbleW (e M ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  -(kF e * dBub (gAF true μ ν) (gBF true μ ν) M ε (zk k true q) (zk k false q))

theorem hasDerivAt_bubbleW (e : ℝ) {ε : ℝ} (hε : ε ≠ 0) (k q : Fin 4 → ℝ) (μ ν : Fin 4)
    (M : ℝ) : HasDerivAt (fun M => bubbleW e M ε k q μ ν) (dBubbleW e M ε k q μ ν) M := by
  have h := ((hasDerivAt_bub (isOddG_gamma _ : IsOddG (gAF true μ ν))
    (isOddG_gamma _ : IsOddG (gBF true μ ν)) hε (zk k true q) (zk k false q) M).const_mul
    (kF e)).neg
  have e' : (fun M => bubbleW e M ε k q μ ν) = fun M => -(kF e *
      (bubTr (gAF true μ ν) (gBF true μ ν) M (zk k true q) (zk k false q) *
        (propDenom M ε (zk k true q))⁻¹ * (propDenom M ε (zk k false q))⁻¹)) :=
    funext fun M => by rw [kF_bubTr_F0, neg_neg]
  rw [e']
  exact h

/-- The three-propagator remainder `κ_F M² Tr[A B] (D_x⁻² D_y⁻¹ + D_x⁻¹ D_y⁻²)` of the two
insertions. -/
noncomputable def remM (e M ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  kF e * ((M : ℂ) ^ 2 * (gAF true μ ν * gBF true μ ν).trace *
    ((propDenom M ε (zk k true q))⁻¹ ^ 2 * (propDenom M ε (zk k false q))⁻¹ +
      (propDenom M ε (zk k true q))⁻¹ * (propDenom M ε (zk k false q))⁻¹ ^ 2))

/-- **The two mass insertions of one flavour are the mass derivative of its bubble**, up to
`iε`. -/
theorem kF_insG_F0_add_F1 (e d M : ℝ) {ε : ℝ} (hε : ε ≠ 0) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    kF e * insG (gAF true μ ν) (gBF true μ ν) 0 d M ε (zk k true q) (zk k false q) +
        kF e * insG (gAF false μ ν) (gBF false μ ν) 0 d M ε (zk k false q) (zk k true q) =
      ((d * M : ℝ) : ℂ) * dBubbleW e M ε k q μ ν - (ε * I) * ((d : ℂ) * remM e M ε k q μ ν) := by
  set x := zk k true q with hxd
  set y := zk k false q with hyd
  have hx : propDenom M ε x ≠ 0 := propDenom_ne_zero hε x
  have hy : propDenom M ε y ≠ 0 := propDenom_ne_zero hε y
  have hA : IsOddG (Dirac.gamma μ) := isOddG_gamma _
  have hB : IsOddG (Dirac.gamma ν) := isOddG_gamma _
  have hcyc : bubTr (Dirac.gamma μ) (Dirac.gamma ν) M y x =
      bubTr (Dirac.gamma ν) (Dirac.gamma μ) M x y := by
    simp only [bubTr]
    rw [Matrix.mul_assoc _ (Dirac.gamma ν), Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have htr : (Dirac.gamma μ * Dirac.gamma ν).trace = (Dirac.gamma ν * Dirac.gamma μ).trace :=
    Matrix.trace_mul_comm _ _
  have hDx : ((Minkowski.dot x x + M ^ 2 : ℝ) : ℂ) = propDenom M ε x + (ε : ℂ) * I := by
    simp only [propDenom]
    ring
  have hDy : ((Minkowski.dot y y + M ^ 2 : ℝ) : ℂ) = propDenom M ε y + (ε : ℂ) * I := by
    simp only [propDenom]
    ring
  rw [insG_eq _ _ _ hε, insG_eq _ _ _ hε]
  simp only [gAF, gBF, ite_true, Bool.false_eq_true, ite_false, ofReal_zero, zero_mul, zero_add,
    sub_zero]
  rw [massTr_eq hB hA, massTr_eq hA hB, hcyc, htr, hDx, hDy]
  simp only [dBubbleW, dBub, remM, gAF, gBF, ite_true]
  rw [← hxd, ← hyd]
  push_cast
  field_simp
  ring

/-! ### The block -/

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (rep : F → F)

omit [DecidableEq F] in
/-- **(L3, pointwise) The pure mass insertions are the mass derivative of the block bubble**:
`F0[ctδ] + F1[ctδ] = ∑_f c_f δ_f M_f ∂_M bubbleW(M_f) - iε ∑_f c_f δ_f remM(M_f)`,
`δ_f = e² (d_m - d₂)(rep f)`. -/
theorem fBubble_ctδ_F0_add_F1 {ε : ℝ} (hε : ε ≠ 0) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    fBubble P Φ (ctδ D) rep true true false ε k q μ ν +
        fBubble P Φ (ctδ D) rep false false true ε k q μ ν =
      ∑ f, (Φ.coeff f : ℂ) * ((((P.e ^ 2 * (D.dm (rep f) 0 - D.d₂ (rep f) 0)) * Φ.mass f :
        ℝ) : ℂ) * dBubbleW P.e (Φ.mass f) ε k q μ ν) -
      (ε * I) * ∑ f, (Φ.coeff f : ℂ) * (((P.e ^ 2 * (D.dm (rep f) 0 - D.d₂ (rep f) 0) : ℝ) :
        ℂ) * remM P.e (Φ.mass f) ε k q μ ν) := by
  simp only [fBubble, ctδ, mul_zero, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h := kF_insG_F0_add_F1 P.e (P.e ^ 2 * (D.dm (rep f) 0 - D.d₂ (rep f) 0)) (Φ.mass f) hε
    k q μ ν
  linear_combination (Φ.coeff f : ℂ) * h

end QED.GradedProof.RPi4

end
