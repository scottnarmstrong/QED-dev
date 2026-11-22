/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.BoxInversion
public import QED.DimReg.SectorCert
public import QED.DimReg.CubeMellin

/-!
# The Lee–Pomeransky integrand on a sector: monomial times a power of a positive polynomial

Let `G` be a polynomial with natural coefficients (`QED.DimReg.Sector.NPoly`) and partial degrees
at most `D`. On the box `B_T` the inversion `xᵢ = 1 / yᵢ` (`i ∈ T`) gives
`G(boxInv T y) = P_T(y) / ∏_{i ∈ T} yᵢ ^ Dᵢ` with `P_T` the box polynomial (`αᵢ ↦ Dᵢ - αᵢ` for
`i ∈ T`, `QED.DimReg.Sector.boxPolyF`, `QED.DimReg.Sector.eval_boxPolyF`). On a leaf `σ` of a
sector decomposition of the unit cube, `P_T(φ_σ(y)) = y ^ m · P̃(y)` with `P̃ > 0`. Then the pulled
back Lee–Pomeransky integrand is

  `J_σ(y) · J_T(φ_σ y) · lpIntegrand G ν d (boxInv T (φ_σ y)) = ∏ₖ yₖ ^ (ℓₖ - 1) · P̃(y) ^ (-d / 2)`

on the unit cube (`QED.DimReg.Sector.leafIntegrand_lp`), with the leaf exponents

  `ℓₖ = 1 + jₖ + Σᵢ eᵢ πᵢₖ - (d / 2) mₖ`,  `eᵢ = νᵢ - 1` (`i ∉ T`),
  `eᵢ = -νᵢ - 1 + Dᵢ d / 2` (`i ∈ T`),

where `y ^ j` is the Jacobian of the leaf and `πᵢₖ` the exponent of `yₖ` in `(φ_σ y)ᵢ`
(`QED.DimReg.Sector.leafExp`). The `ℓₖ` are affine in `(ν, d / 2)` with integer coefficients
(`QED.DimReg.Sector.leafForm`, `QED.DimReg.Sector.leafExp_eq_form`), so they can be emitted as
data and compared by `decide`.

The proof works with logarithms: every factor is a positive real to a complex power, hence
`exp` of a linear form in `log yₖ` and `log P̃`, and the identity reduces to a linear identity of
the coefficients (`QED.DimReg.Sector.leaf_log_identity`).
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.DimReg

variable {N : ℕ}

theorem splitMap_mem_unitCube {i j : Fin N} (hij : i ≠ j) {y : Fin N → ℝ}
    (hy : y ∈ unitCube N) : splitMap i j y ∈ unitCube N :=
  (image_splitMap hij ▸ mem_image_of_mem _ hy : splitMap i j y ∈ {y ∈ unitCube N | _}).1

theorem leafMap_mem_unitCube : ∀ {ps : List (Fin N × Fin N)}, (∀ p ∈ ps, p.1 ≠ p.2) →
    ∀ {y : Fin N → ℝ}, y ∈ unitCube N → leafMap ps y ∈ unitCube N
  | [], _, _, hy => hy
  | p :: _, h, _, hy => splitMap_mem_unitCube (h p List.mem_cons_self)
      (leafMap_mem_unitCube (fun q hq => h q (List.mem_cons_of_mem p hq)) hy)

theorem SplitTree.paths_ne : ∀ (T : SplitTree N), T.Valid → ∀ ps ∈ T.paths, ∀ p ∈ ps, p.1 ≠ p.2
  | .leaf, _, ps, hps, p, hp => by simp [SplitTree.paths] at hps; subst hps; simp at hp
  | .node i j l r, ⟨hij, hl, hr⟩, ps, hps, p, hp => by
    simp only [SplitTree.paths, List.mem_append, List.mem_map] at hps
    rcases hps with ⟨qs, hqs, rfl⟩ | ⟨qs, hqs, rfl⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact hij
      · exact SplitTree.paths_ne l hl qs hqs p hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact hij.symm
      · exact SplitTree.paths_ne r hr qs hqs p hp

namespace Sector

/-! ### The box polynomial -/

/-- The exponent on the box `T`: `αᵢ ↦ Dᵢ - αᵢ` for `i ∈ T`. -/
def boxExpF (T : Finset (Fin N)) (D α : List ℕ) : List ℕ :=
  (List.finRange N).map fun i => if i ∈ T then D.getD i 0 - α.getD i 0 else α.getD i 0

/-- The box polynomial `P_T`. -/
def boxPolyF (T : Finset (Fin N)) (D : List ℕ) (P : NPoly) : NPoly :=
  P.map fun t => (boxExpF T D t.1, t.2)

theorem getD_boxExpF (T : Finset (Fin N)) (D α : List ℕ) (k : Fin N) :
    (boxExpF T D α).getD k 0 = if k ∈ T then D.getD k 0 - α.getD k 0 else α.getD k 0 := by
  simp [boxExpF, List.getD_eq_getElem?_getD]

theorem mono_boxExpF {T : Finset (Fin N)} {D α : List ℕ} (hα : ∀ i ∈ T, α.getD i 0 ≤ D.getD i 0)
    {x : Fin N → ℝ} (hx : ∀ i, x i ≠ 0) :
    mono (boxExpF T D α) x = mono α (boxInv T x) * ∏ i ∈ T, x i ^ D.getD i 0 := by
  rw [mono, mono, show ∏ i ∈ T, x i ^ D.getD i 0 =
      ∏ i, if i ∈ T then x i ^ D.getD i 0 else 1 by
    rw [Finset.prod_ite_mem, Finset.univ_inter], ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [getD_boxExpF]
  by_cases hk : k ∈ T
  · simp only [hk, ite_true, boxInv, inv_pow]
    rw [pow_sub₀ _ (hx k) (hα k hk)]
    ring
  · simp [hk, boxInv]

theorem eval_boxPolyF {T : Finset (Fin N)} {D : List ℕ} {P : NPoly}
    (hP : ∀ t ∈ P, ∀ i ∈ T, t.1.getD i 0 ≤ D.getD i 0) {x : Fin N → ℝ} (hx : ∀ i, x i ≠ 0) :
    (boxPolyF T D P).eval x = P.eval (boxInv T x) * ∏ i ∈ T, x i ^ D.getD i 0 := by
  simp only [NPoly.eval, boxPolyF, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_right]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [mono_boxExpF (hP t ht) hx, mul_assoc]

/-! ### The leaf exponents -/

/-- The exponent of `xᵢ` on the box `T` after inversion, Jacobian included:
`νᵢ - 1` for `i ∉ T` and `-νᵢ - 1 + Dᵢ d / 2` for `i ∈ T`. -/
noncomputable def boxE (D : List ℕ) (T : Finset (Fin N)) (ν : Fin N → ℂ) (d : ℂ) (i : Fin N) :
    ℂ :=
  if i ∈ T then -ν i - 1 + (D.getD i 0 : ℂ) * (d / 2) else ν i - 1

/-- The exponent of `yₖ` in `(φ_σ y)ᵢ`. -/
def pullE (ps : List (Fin N × Fin N)) (i k : Fin N) : ℕ := (pullExp ps (unitExp i)).getD k 0

/-- **The leaf exponents** `ℓₖ = 1 + jₖ + Σᵢ eᵢ πᵢₖ - (d / 2) mₖ`. -/
noncomputable def leafExp (D : List ℕ) (T : Finset (Fin N)) (ps : List (Fin N × Fin N))
    (m : List ℕ) (ν : Fin N → ℂ) (d : ℂ) (k : Fin N) : ℂ :=
  1 + ((jacExp ps).getD k 0 : ℂ) + ∑ i, boxE D T ν d i * (pullE ps i k : ℂ) -
    d / 2 * (m.getD k 0 : ℂ)

/-! ### Logarithms -/

theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (c : ℂ) :
    (r : ℂ) ^ c = cexp ((Real.log r : ℂ) * c) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ofReal_log hr.le]

theorem ofReal_eq_exp {r : ℝ} (hr : 0 < r) : (r : ℂ) = cexp (Real.log r : ℂ) := by
  rw [← ofReal_exp, Real.exp_log hr]

theorem mono_pos (α : List ℕ) {y : Fin N → ℝ} (hy : ∀ k, 0 < y k) : 0 < mono α y :=
  Finset.prod_pos fun k _ => pow_pos (hy k) _

theorem log_mono (α : List ℕ) {y : Fin N → ℝ} (hy : ∀ k, 0 < y k) :
    Real.log (mono α y) = ∑ k : Fin N, (α.getD k 0 : ℝ) * Real.log (y k) := by
  rw [mono, Real.log_prod fun k _ => (pow_pos (hy k) _).ne']
  exact Finset.sum_congr rfl fun k _ => Real.log_pow _ _

theorem leafMap_apply_eq_mono (ps : List (Fin N × Fin N)) (i : Fin N) (y : Fin N → ℝ) :
    leafMap ps y i = mono (pullExp ps (unitExp i)) y := by
  rw [mono_pullExp, mono_unitExp]

/-- The linear identity behind the leaf form. -/
theorem leaf_log_identity (L : Fin N → ℂ) (lQ : ℂ) (jac m : Fin N → ℂ)
    (pull : Fin N → Fin N → ℂ) (T : Finset (Fin N)) (Dv : Fin N → ℂ) (ν : Fin N → ℂ) (d : ℂ) :
    (∑ k, jac k * L k) + ((∑ i, (if i ∈ T then -2 * ∑ k, pull i k * L k else 0)) +
      ((∑ i, (if i ∈ T then -∑ k, pull i k * L k else ∑ k, pull i k * L k) * (ν i - 1)) +
      ((∑ k, m k * L k) + lQ - ∑ i, (if i ∈ T then Dv i * ∑ k, pull i k * L k else 0)) *
        (-(d / 2)))) =
    ∑ k, L k * ((1 + jac k + ∑ i, (if i ∈ T then -ν i - 1 + Dv i * (d / 2) else ν i - 1) *
      pull i k - d / 2 * m k) - 1) + lQ * (-(d / 2)) := by
  set E : Fin N → ℂ := fun i => if i ∈ T then -ν i - 1 + Dv i * (d / 2) else ν i - 1 with hE
  have e1 : ∀ k, L k * ((1 + jac k + ∑ i, E i * pull i k - d / 2 * m k) - 1) =
      jac k * L k + ∑ i, E i * (pull i k * L k) - d / 2 * (m k * L k) := by
    intro k
    rw [show ∑ i, E i * (pull i k * L k) = L k * ∑ i, E i * pull i k by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    ring
  have hR : ∑ k, L k * ((1 + jac k + ∑ i, E i * pull i k - d / 2 * m k) - 1) =
      ∑ k, jac k * L k + ∑ i, E i * ∑ k, pull i k * L k - d / 2 * ∑ k, m k * L k := by
    rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_comm (f := fun k i => E i * (pull i k * L k))]
    simp only [Finset.mul_sum]
  rw [hR]
  have hI : ∑ i, E i * ∑ k, pull i k * L k =
      (∑ i, (if i ∈ T then -2 * ∑ k, pull i k * L k else 0)) +
      (∑ i, (if i ∈ T then -∑ k, pull i k * L k else ∑ k, pull i k * L k) * (ν i - 1)) +
      (∑ i, (if i ∈ T then Dv i * ∑ k, pull i k * L k else 0)) * (d / 2) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hE]
    split_ifs <;> ring
  rw [hI]
  ring

/-! ### The leaf form -/

/-- **The Lee–Pomeransky integrand on a leaf.** Let `G` have partial degrees at most `D` in the
coordinates of `T`, let `ps` be a leaf path of distinct pairs, and let the box polynomial factor
on the leaf as `P_T(φ_σ y) = y ^ m · Q(y)`. Then at every point of the unit cube with `Q(y) > 0`
the pulled-back integrand is `∏ₖ yₖ ^ (ℓₖ - 1) · Q(y) ^ (-d / 2)`. -/
theorem leafIntegrand_lp {Gp : NPoly} {D : List ℕ} {T : Finset (Fin N)}
    (hdeg : ∀ t ∈ Gp, ∀ i ∈ T, t.1.getD i 0 ≤ D.getD i 0) {ps : List (Fin N × Fin N)}
    (hps : ∀ p ∈ ps, p.1 ≠ p.2) {m : List ℕ} {Q : NPoly}
    (hfac : ∀ y, (boxPolyF T D Gp).eval (leafMap ps y) = mono m y * Q.eval y) (ν : Fin N → ℂ)
    (d : ℂ) {y : Fin N → ℝ} (hy : y ∈ unitCube N) (hQ : 0 < Q.eval y) :
    leafIntegrand (fun u => boxJac T u • lpIntegrand (fun x => Gp.eval x) ν d (boxInv T u)) ps y =
      cubeWeight (leafExp D T ps m ν d) y * ((Q.eval y : ℝ) : ℂ) ^ (-(d / 2)) := by
  have hyp : ∀ k, 0 < y k := fun k => ((mem_unitCube.mp hy) k).1
  set u := leafMap ps y with hu_def
  have hu : u ∈ unitCube N := leafMap_mem_unitCube hps hy
  have hup : ∀ i, 0 < u i := fun i => ((mem_unitCube.mp hu) i).1
  set x := boxInv T u with hx_def
  have hxp : ∀ i, 0 < x i := by
    intro i; simp only [hx_def, boxInv]; split_ifs
    · exact inv_pos.mpr (hup i)
    · exact hup i
  -- logarithms of the real factors
  have hlogu : ∀ i, Real.log (u i) = ∑ k, (pullE ps i k : ℝ) * Real.log (y k) := by
    intro i; rw [hu_def, leafMap_apply_eq_mono, log_mono _ hyp]; rfl
  have hlogx : ∀ i, Real.log (x i) = if i ∈ T then -Real.log (u i) else Real.log (u i) := by
    intro i; simp only [hx_def, boxInv]; split_ifs
    · exact Real.log_inv _
    · rfl
  have hJp : 0 < leafJac ps y := by rw [leafJac_eq_mono]; exact mono_pos _ hyp
  have hlogJ : Real.log (leafJac ps y) =
      ∑ k : Fin N, ((jacExp ps).getD k 0 : ℝ) * Real.log (y k) := by
    rw [leafJac_eq_mono, log_mono _ hyp]
  have hBp : 0 < boxJac T u := Finset.prod_pos fun i _ => inv_pos.mpr (pow_pos (hup i) 2)
  have hlogB : Real.log (boxJac T u) =
      ∑ i, if i ∈ T then -2 * Real.log (u i) else 0 := by
    rw [boxJac, Real.log_prod fun i _ => (inv_pos.mpr (pow_pos (hup i) 2)).ne',
      Finset.sum_ite_mem, Finset.univ_inter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_inv, Real.log_pow]; push_cast; ring
  have hG := eval_boxPolyF hdeg (x := u) fun i => (hup i).ne'
  rw [hfac] at hG
  have hDp : 0 < ∏ i ∈ T, u i ^ D.getD i 0 := Finset.prod_pos fun i _ => pow_pos (hup i) _
  have hGp : 0 < Gp.eval x := by
    have h1 : 0 < mono m y * Q.eval y := mul_pos (mono_pos _ hyp) hQ
    rw [hG] at h1
    exact pos_of_mul_pos_left h1 hDp.le
  have hlogG : Real.log (Gp.eval x) = (∑ k : Fin N, (m.getD k 0 : ℝ) * Real.log (y k)) +
      Real.log (Q.eval y) - ∑ i, if i ∈ T then (D.getD i 0 : ℝ) * Real.log (u i) else 0 := by
    have h2 := congrArg Real.log hG
    rw [Real.log_mul (mono_pos _ hyp).ne' hQ.ne', Real.log_mul hGp.ne' hDp.ne',
      Real.log_prod fun i _ => (pow_pos (hup i) _).ne', log_mono _ hyp] at h2
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp only [Real.log_pow] at h2
    linarith
  -- the complex computation
  have hxi : ∀ i, (x i : ℂ) ^ (ν i - 1) = cexp ((Real.log (x i) : ℂ) * (ν i - 1)) :=
    fun i => ofReal_cpow_eq_exp (hxp i) _
  have hyk : ∀ k, (y k : ℂ) ^ (leafExp D T ps m ν d k - 1) =
      cexp ((Real.log (y k) : ℂ) * (leafExp D T ps m ν d k - 1)) :=
    fun k => ofReal_cpow_eq_exp (hyp k) _
  simp only [leafIntegrand, lpIntegrand, cubeWeight, Complex.real_smul]
  rw [ofReal_eq_exp hJp, ofReal_eq_exp hBp, ofReal_cpow_eq_exp hGp, ofReal_cpow_eq_exp hQ]
  simp only [← hx_def, ← hu_def, hxi, hyk, ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  rw [hlogJ, hlogB, hlogG]
  simp only [hlogx, hlogu]
  push_cast
  have := leaf_log_identity (fun k => (Real.log (y k) : ℂ)) (Real.log (Q.eval y) : ℂ)
    (fun k => ((jacExp ps).getD k 0 : ℂ)) (fun k => (m.getD k 0 : ℂ))
    (fun i k => (pullE ps i k : ℂ)) T (fun i => (D.getD i 0 : ℂ)) ν d
  simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_zero, Complex.ofReal_ofNat]
  simp only [leafExp, boxE]
  exact this

end Sector

end QED.DimReg
