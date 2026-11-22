/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMPauli
public import QED.ChainProof.SetCUnitMEvenBd

/-!
# Multi-denominator two-loop vertex units: the `q → 0` bound uniform in the masses

Helper level for set (c) (gap 4 of stage L1). `QED.TwoLoop.PauliZeroExplicit.tendsto_piece_explicit`
writes the even quotient `(S(u) + S(-u))/(2u²)` of a projected parametric value along the curve as
`∫ (A(x, u) + A(x, -u)) / (2u² (1 - u²)ᵃ V(x, u)ᴺ) dx` with
`A(x, u) = ∑ⱼ (1 - u²)ʳ ωⱼ(u) (-π⁴) ∑ₖ λₖ(u) (1 - u²)⁴ paramNum(Qⱼₖ, x, u)`, and
`paramNum = c₁ + c₂ V + c₃ V²` with coefficients `cᵢ` that do not involve the masses. So with
`|V| ≤ K` at the interpolation nodes, `‖A(x, node)‖ ≤ g(x) (1 + K)²` for a mass-free integrable
`g`, and `QED.ChainProof.SetCUnitM.norm_evenQuot_le_nodes` bounds the quotient.

* `pieceDom`, `pieceConst`: the mass-free majorant and constant of a piece;
* `norm_paramNum_le`: `‖paramNum‖ ≤ (‖c₁‖ + ‖c₂‖ + ‖c₃‖) (1 + K)²` where `|V| ≤ K`;
* **`norm_evenQuot_piece_le`**: for `0 < |u| ≤ 1/2`,
  `‖(S(u) + S(-u))/(2u²)‖ ≤ pieceConst · (1 + K)² / ((3/4)ᵃ cᴺ)`;
* **`norm_unitMPauliQuot_le`**, **`norm_unitMPauliZero_le`**: for the multi-denominator unit
  (`n = 0`, the scales fixed), one constant `C` with
  `‖(S(u) + S(-u))/(2u²)‖ ≤ C (1 + ∑ᵢ Mᵢ²)²` for `0 < |u| ≤ 1/2` and
  `‖unitMPauliZero‖ ≤ C (1 + ∑ᵢ Mᵢ²)²`, for all photon and extra masses `≥ μ₀` (`Mᵢ` the masses of
  all `r + 8` lines);
* **`norm_unitMPauliZeroPow_le`**: with the power `(k²)ⁿ` (the last `n` extra lines unscaled),
  `‖unitMPauliZeroPow n‖ ≤ C (1 + ∑ᵢ Mᵢ²)ⁿ⁺²`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.Integration.TwoLoop (LoopQuartic RefinedBound symanzikV)
open QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.PauliZeroExplicit
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### The mass-free majorant -/

section Generic

/-- The mass-free majorant of `A(·, u)` of a piece, before the factor `(1 + K)²`. -/
noncomputable def pieceDom {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (mom : ℝ → Fin (m + 1) → Fin 4 → ℝ) {J : Type*} [Fintype J] (D n r : ℕ)
    (Qk : J → Fin (D + 1) → LoopQuartic) (ω : ℝ → J → ℂ) (u : ℝ) (x : Fin m → ℝ) : ℝ :=
  ∑ j, ‖wt u ^ r * ω u j‖ * (π ^ 4 * ∑ k, ‖wt (node D k) ^ n * (lbasis D k).eval (u : ℂ)‖ *
    (‖wt u ^ 4‖ * (‖coeffOne (Qk j k) α (mom u) x‖ + ‖coeffTwo (Qk j k) α (mom u) x‖ +
      ‖coeffThree (Qk j k) α x‖)))

/-- The mass-free constant of a piece. -/
noncomputable def pieceConst {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (mom : ℝ → Fin (m + 1) → Fin 4 → ℝ) {J : Type*} [Fintype J] (D n r Dω : ℕ)
    (Qk : J → Fin (D + 1) → LoopQuartic) (ω : ℝ → J → ℂ) : ℝ :=
  lagConst (Dω + (D + 8)) * ∑ t : Fin (Dω + (D + 8) + 1),
    ∫ x in simplexSet m, pieceDom α mom D n r Qk ω (node (Dω + (D + 8)) t) x

theorem norm_paramNum_le {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (x : Fin m → ℝ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : |symanzikV α p M (simplexPoint x)| ≤ K) :
    ‖paramNum Q α p M x‖ ≤
      (‖coeffOne Q α p x‖ + ‖coeffTwo Q α p x‖ + ‖coeffThree Q α x‖) * (1 + K) ^ 2 := by
  set V := symanzikV α p M (simplexPoint x)
  have hV : ‖((V : ℝ) : ℂ)‖ ≤ K := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hK
  have h1 : (1 : ℝ) ≤ (1 + K) ^ 2 := by nlinarith
  have h2 : K ≤ (1 + K) ^ 2 := by nlinarith
  have h3 : K ^ 2 ≤ (1 + K) ^ 2 := by nlinarith
  have hV2 : ‖((V : ℝ) : ℂ) ^ 2‖ ≤ K ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hV 2
  unfold paramNum
  refine (norm_add₃_le).trans ?_
  rw [norm_mul, norm_mul]
  have a1 := norm_nonneg (coeffOne Q α p x)
  have a2 := norm_nonneg (coeffTwo Q α p x)
  have a3 := norm_nonneg (coeffThree Q α x)
  have b1 : ‖coeffTwo Q α p x‖ * ‖((V : ℝ) : ℂ)‖ ≤ ‖coeffTwo Q α p x‖ * (1 + K) ^ 2 :=
    mul_le_mul_of_nonneg_left (hV.trans h2) a2
  have b2 : ‖coeffThree Q α x‖ * ‖((V : ℝ) : ℂ) ^ 2‖ ≤ ‖coeffThree Q α x‖ * (1 + K) ^ 2 :=
    mul_le_mul_of_nonneg_left (hV2.trans h3) a3
  nlinarith

variable (C : CurveData) {J : Type*} [Fintype J] {D n r Dω : ℕ}

theorem integrableOn_pieceDom (Qk : J → Fin (D + 1) → LoopQuartic)
    (hBk : ∀ j k, RefinedBound C.α C.E 4 (Qk j k).eval) (ω : ℝ → J → ℂ) (u : ℝ) :
    IntegrableOn (pieceDom C.α C.mom D n r Qk ω u) (simplexSet C.m) := by
  refine integrable_finsetSum _ fun j _ => Integrable.const_mul ?_ _
  refine Integrable.const_mul ?_ _
  refine integrable_finsetSum _ fun k _ => Integrable.const_mul ?_ _
  refine Integrable.const_mul ?_ _
  obtain ⟨h1, h2, h3⟩ := integrableOn_coeff (Qk j k) C.α (C.mom u) C.hm C.hcrit (hBk j k)
  exact (h1.norm.add h2.norm).add h3.norm

/-- **The even quotient of a piece is bounded by a mass-free constant times `(1 + K)²`**, `K` a
bound for `|V|` at the interpolation nodes, for `0 < |u| ≤ 1/2`. The quartics `Qk` at the nodes
are fixed in advance, so `pieceConst` involves only the loop matrix, the momenta along the curve,
the quartics and the weights. -/
theorem norm_evenQuot_piece_le (F : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hFpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * F u j ℓ)
    (Qk : J → Fin (D + 1) → LoopQuartic) (hQk : ∀ j k, (Qk j k).eval = F (node D k) j)
    (hFB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (F u j))
    (v : ℝ → J → ℂ)
    (hv : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) j, IsParamValue (C.toParamData hu) (F u j) (v u j))
    (ω : ℝ → J → ℂ) (hω : ∀ j, IsUPoly (ι := Fin C.m → ℝ) Dω fun _ u => wt u ^ r * ω u j)
    (hω0 : ∀ Y : J → ℂ, ∑ j, ω 0 j * Y j = 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t : Fin (Dω + (D + 8) + 1), ∀ᵐ x ∂(volume.restrict (simplexSet C.m)),
      |C.vfun x (node (Dω + (D + 8)) t)| ≤ K)
    {u : ℝ} (hu0 : u ≠ 0) (hu : |u| ≤ 1 / 2) :
    ‖((∑ j, ω u j * v u j) + ∑ j, ω (-u) j * v (-u) j) / (2 * (u : ℂ) ^ 2)‖ ≤
      pieceConst C.α C.mom D n r Dω Qk ω * (1 + K) ^ 2 /
        ((3 / 4 : ℝ) ^ (r + n + 4) * C.c ^ (C.m - 3)) := by
  classical
  have hnode : ∀ k : Fin (D + 1), node D k ∈ Ioo (-1 : ℝ) 1 := node_mem D
  have hBk : ∀ j k, RefinedBound C.α C.E 4 (Qk j k).eval := fun j k => by
    rw [hQk]
    exact hFB _ (hnode k) j
  set f : ℝ → (Fin C.m → ℝ) → ℂ := fun u x => ∑ j, ω u j * (-((π : ℂ) ^ 4) *
    ∑ k, lam D n u k * paramIntegrand (Qk j k) C.α (C.mom u) C.M 0 x) with hf_def
  set A : (Fin C.m → ℝ) → ℝ → ℂ := fun x u => ∑ j, (wt u ^ r * ω u j) * (-((π : ℂ) ^ 4) *
    ∑ k, (wt (node D k) ^ n * (lbasis D k).eval (u : ℂ)) *
      (wt u ^ 4 * paramNum (Qk j k) C.α (C.mom u) C.M x)) with hA_def
  have hA : IsUPoly (Dω + (D + 8)) A :=
    IsUPoly.sum _ fun j _ => (hω j).mul (IsUPoly.const_mul _ (IsUPoly.sum _ fun k _ =>
      ((isUPoly_lbasis D k).const_mul _).mul (isUPoly_paramNum (Qk j k) C.α C.M C.mom C.hmom)))
  have hAi : ∀ t, Integrable (fun x => A x (node (Dω + (D + 8)) t))
      (volume.restrict (simplexSet C.m)) := fun t => by
    refine integrable_finsetSum _ fun j _ => Integrable.const_mul ?_ _
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun k _ => Integrable.const_mul ?_ _
    exact (integrableOn_paramNum (Qk j k) C.α _ C.M C.hm C.hcrit (hBk j k)).const_mul _
  have hA0 : ∀ x, A x 0 = 0 := fun x => by
    simp only [hA_def, wt_zero, one_pow, one_mul]
    exact hω0 _
  have hf : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ᵐ x ∂(volume.restrict (simplexSet C.m)),
      f u x = A x u / (wt u ^ (r + n + 4) * ((C.vfun x u : ℝ) : ℂ) ^ (C.m - 3)) := by
    intro u hu
    filter_upwards [C.ae_le_vfun] with x hx
    have hV0 : C.vfun x u ≠ 0 := (C.hc.trans_le (hx u hu)).ne'
    have hV0' : ((C.vfun x u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hV0
    have hw := wt_ne_zero hu
    simp only [hf_def, hA_def, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [paramIntegrand_zero_eq (Qk j k) C.α (C.mom u) C.M (by have := C.hm; omega) hV0]
    simp only [lam, CurveData.vfun] at hV0' ⊢
    field_simp
    ring
  have hS : ∀ u ∈ Ioo (-1 : ℝ) 1, ∑ j, ω u j * v u j = ∫ x in simplexSet C.m, f u x := by
    intro u hu
    have hI : ∀ j k, IntegrableOn (paramIntegrand (Qk j k) C.α (C.mom u) C.M 0)
        (simplexSet C.m) := fun j k =>
      integrableOn_paramIntegrand_zero (Qk j k) C.α (C.mom u) C.M C.hm C.hcrit (hBk j k) C.hc
        (C.hV u hu)
    have hvj : ∀ j, v u j = -((π : ℂ) ^ 4) * ∫ x in simplexSet C.m,
        ∑ k, lam D n u k * paramIntegrand (Qk j k) C.α (C.mom u) C.M 0 x := fun j => by
      have h' : IsParamValue (C.toParamData hu) (F u j) (-((π : ℂ) ^ 4) *
          ∫ x in simplexSet C.m,
            paramIntegrand (jointQuartic D n (Qk j) u) C.α (C.mom u) C.M 0 x) :=
        ⟨jointQuartic D n (Qk j) u, eval_jointQuartic (hFpoly j) (hQk j) hu, hFB u hu j, rfl⟩
      rw [(hv u hu j).unique h', jointQuartic]
      simp only [paramIntegrand_qsum]
    simp only [hvj, hf_def]
    rw [integral_finsetSum _ fun j _ => (((integrable_finsetSum _ fun k _ =>
      (hI j k).const_mul _).const_mul _).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_const_mul]
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := by
    rw [abs_le] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu1.2], by linarith [hu1.1]⟩
  rw [hS u hu1, hS (-u) hu']
  refine (norm_evenQuot_le_nodes (μ := volume.restrict (simplexSet C.m)) hA hAi
    (ae_of_all _ hA0) C.hc C.ae_le_vfun (ae_of_all _ fun x u => C.hVeven u _)
    (ae_of_all _ C.continuousAt_vfun) (fun u => (C.measurable_vfun u).aestronglyMeasurable) hf
    hu0 hu).trans ?_
  refine div_le_div_of_nonneg_right ?_ (by have := C.hc; positivity)
  unfold pieceConst
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (lagConst_nonneg _)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun t _ => ?_
  set w := node (Dω + (D + 8)) t
  rw [← integral_mul_const]
  refine integral_mono_ae (hAi t).norm
    ((integrableOn_pieceDom C Qk hBk ω w).mul_const _) ?_
  filter_upwards [hK t] with x hx
  have hP : ∀ j k, ‖paramNum (Qk j k) C.α (C.mom w) C.M x‖ ≤
      (‖coeffOne (Qk j k) C.α (C.mom w) x‖ + ‖coeffTwo (Qk j k) C.α (C.mom w) x‖ +
        ‖coeffThree (Qk j k) C.α x‖) * (1 + K) ^ 2 := fun j k =>
    norm_paramNum_le (Qk j k) C.α (C.mom w) C.M x hK0 hx
  simp only [hA_def, pieceDom, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul (wt w ^ r * ω w j), norm_mul (-((π : ℂ) ^ 4)), norm_neg, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hsum : ‖∑ k, wt (node D k) ^ n * (lbasis D k).eval (w : ℂ) *
      (wt w ^ 4 * paramNum (Qk j k) C.α (C.mom w) C.M x)‖ ≤
      ∑ k, ‖wt (node D k) ^ n * (lbasis D k).eval (w : ℂ)‖ * (‖wt w ^ 4‖ *
        ((‖coeffOne (Qk j k) C.α (C.mom w) x‖ + ‖coeffTwo (Qk j k) C.α (C.mom w) x‖ +
          ‖coeffThree (Qk j k) C.α x‖) * (1 + K) ^ 2)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul (wt w ^ 4)]
    gcongr
    exact hP j k
  have e : ∑ k, ‖wt (node D k) ^ n * (lbasis D k).eval (w : ℂ)‖ * (‖wt w ^ 4‖ *
        ((‖coeffOne (Qk j k) C.α (C.mom w) x‖ + ‖coeffTwo (Qk j k) C.α (C.mom w) x‖ +
          ‖coeffThree (Qk j k) C.α x‖) * (1 + K) ^ 2)) =
      (∑ k, ‖wt (node D k) ^ n * (lbasis D k).eval (w : ℂ)‖ * (‖wt w ^ 4‖ *
        (‖coeffOne (Qk j k) C.α (C.mom w) x‖ + ‖coeffTwo (Qk j k) C.α (C.mom w) x‖ +
          ‖coeffThree (Qk j k) C.α x‖))) * (1 + K) ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  calc _ ≤ ‖wt w ^ r * ω w j‖ * (π ^ 4 * ∑ k, ‖wt (node D k) ^ n * (lbasis D k).eval (w : ℂ)‖ *
        (‖wt w ^ 4‖ * ((‖coeffOne (Qk j k) C.α (C.mom w) x‖ +
          ‖coeffTwo (Qk j k) C.α (C.mom w) x‖ + ‖coeffThree (Qk j k) C.α x‖) * (1 + K) ^ 2))) := by
        gcongr
    _ = _ := by rw [e]; ring

end Generic

/-! ### The multi-denominator unit -/

section Unit

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.PauliZero QED.ChainProof.SetCUnit

variable {r : ℕ}

/-- The Pauli numerators of the unit along the curve. -/
noncomputable def unitMPauliF (c : Class5) (P : Params) (u : ℝ) (j : Idx)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (twoLoopNorm • classNumM c P (restMomentum P.m) (curveMomentum P.m u) j.1 ℓ) j.2.1 j.2.2

theorem unitMPauliF_eq (c : Class5) (P : Params) (u : ℝ) (j : Idx) :
    unitMPauliF c P u j = fun ℓ => twoLoopNorm * classNumeratorE c P
      (fun _ => curveMomentum P.m u) (fun _ => restMomentum P.m)
      (fun _ => curveMomentum P.m u - restMomentum P.m) (fun _ => j.2.1) (fun _ => j.2.2)
      (fun _ => j.1) ℓ :=
  funext fun ℓ => by
    simp only [unitMPauliF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul]

theorem exists_quartic_unitMPauliF {c : Class5} (hc : c ∈ openClasses) (P : Params) (u : ℝ)
    (j : Idx) : ∃ Q : LoopQuartic, Q.eval = unitMPauliF c P u j := by
  rw [unitMPauliF_eq]
  exact ((isLoopPoly_classNumeratorE hc P _ _ _ _ _ _).const_mul _).exists_loopQuartic

/-- Quartics of the Pauli numerators at the nine nodes, chosen once for all masses. -/
noncomputable def unitMQk {c : Class5} (hc : c ∈ openClasses) (P : Params) :
    Idx → Fin (8 + 1) → LoopQuartic :=
  fun j k => Classical.choose (exists_quartic_unitMPauliF hc P (node 8 k) j)

/-- The Pauli weights along the curve. -/
noncomputable def unitMPauliW (P : Params) (u : ℝ) (j : Idx) : ℂ :=
  pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2

/-- **The mass-free constant of the unit**: it involves the class, the parameters, the element
line `s` and the scales, not the masses. -/
noncomputable def unitMPauliConst {c : Class5} (hc : c ∈ openClasses) (P : Params) (s : Fin 8)
    (κ : Fin r → ℝ) : ℝ :=
  pieceConst (unitMMatrix c s κ)
    (fun u => unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m u)) 8 4 4 8
    (unitMQk hc P) (unitMPauliW P)

theorem pieceConst_nonneg {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (mom : ℝ → Fin (m + 1) → Fin 4 → ℝ) {J : Type*} [Fintype J] (D n r Dω : ℕ)
    (Qk : J → Fin (D + 1) → LoopQuartic) (ω : ℝ → J → ℂ) :
    0 ≤ pieceConst α mom D n r Dω Qk ω :=
  mul_nonneg (lagConst_nonneg _) (Finset.sum_nonneg fun t _ =>
    setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun x => by unfold pieceDom; positivity))

/-- The momentum part of the bound for `|V|` at the nodes. -/
noncomputable def unitMMomK (c : Class5) (P : Params) (s : Fin 8) (κ : Fin r → ℝ) : ℝ :=
  ∑ t : Fin (8 + (8 + 8) + 1), ∑ i, ∑ μ,
    unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m (node (8 + (8 + 8)) t)) i μ ^ 2

/-- **The `q → 0` even quotient of the unit, bounded uniformly in the masses** (`n = 0`, the
scales fixed): one constant `C` with `‖(S(u) + S(-u))/(2u²)‖ ≤ C (1 + ∑ᵢ Mᵢ²)²` for
`0 < |u| ≤ 1/2` and all photon and extra masses `≥ μ₀`. -/
theorem norm_unitMPauliQuot_le {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {κ : Fin r → ℝ}
    (hκ : ∀ j, 0 < κ j ∧ κ j ≤ 1) :
    ∃ C : ℝ, ∀ (a A b B : ℝ) (cs : Fin r → ℝ), MassesGe μ₀ a A b B → (∀ j, μ₀ ≤ cs j) →
      ∀ u : ℝ, u ≠ 0 → |u| ≤ 1 / 2 →
        ‖(unitMPauliS c P s κ (unitMMasses P.m a A b B cs) 0 u +
            unitMPauliS c P s κ (unitMMasses P.m a A b B cs) 0 (-u)) / (2 * (u : ℂ) ^ 2)‖ ≤
          C * (1 + ∑ i, unitMMasses P.m a A b B cs i ^ 2) ^ 2 := by
  set Km := unitMMomK c P s κ with hKm
  have hKm0 : 0 ≤ Km := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  set L : ℝ := 26 + Km
  have hc0 := unitConst_pos hm hμ₀ (μ₀ := μ₀)
  refine ⟨unitMPauliConst hc P s κ * L ^ 2 /
    ((3 / 4 : ℝ) ^ (4 + 4 + 4) * unitConst P.m μ₀ ^ (r + 7 - 3)),
    fun a A b B cs hM hcs u hu0 hu => ?_⟩
  have hX : ExtraGe μ₀ κ cs := fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩
  set Cd := unitMCurve hc P hm hs hμ₀ hM hX with hCd
  set S := ∑ i, unitMMasses P.m a A b B cs i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set K : ℝ := 25 * S + Km with hK
  have hK0 : 0 ≤ K := by positivity
  have hKb : ∀ t : Fin (8 + (8 + 8) + 1), ∀ᵐ x ∂(volume.restrict (simplexSet Cd.m)),
      |Cd.vfun x (node (8 + (8 + 8)) t)| ≤ K := fun t => by
    filter_upwards [ae_abs_symanzikV_le (α := Cd.α) (p := Cd.mom (node (8 + (8 + 8)) t))
      (M := Cd.M) (by have := Cd.hm; omega) Cd.hspan] with x hx
    refine hx.trans ?_
    have h1 : ∑ i, ∑ μ, Cd.mom (node (8 + (8 + 8)) t) i μ ^ 2 ≤ Km :=
      Finset.single_le_sum (f := fun t : Fin (8 + (8 + 8) + 1) => ∑ i, ∑ μ,
        unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m (node (8 + (8 + 8)) t)) i μ ^ 2)
        (fun t _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (Finset.mem_univ t)
    rw [Finset.sum_add_distrib]
    have h2 : ∑ i, Cd.M i ^ 2 = S := rfl
    linarith
  have h := norm_evenQuot_piece_le Cd (J := Idx) (D := 8) (n := 4) (r := 4) (Dω := 8)
    (unitMPauliF c P)
    (fun j => by
      have h := isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
        (G := fun ℓ y => twoLoopNorm * classNumeratorE c P (fun _ => y 0)
          (fun _ => restMomentum P.m) (fun _ => y 0 - restMomentum P.m) (fun _ => j.2.1)
          (fun _ => j.2.2) (fun _ => j.1) ℓ)
        (fun ℓ => (isLoopPoly_classNumeratorE_out hc P _ _ _ _ ℓ).const_mul _)
        (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν
      refine h.congr fun ℓ u _ => ?_
      simp only [unitMPauliF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul])
    (unitMQk hc P)
    (fun j k => Classical.choose_spec (exists_quartic_unitMPauliF hc P (node 8 k) j))
    (fun u _ j => by
      rw [unitMPauliF_eq]
      exact refinedBound_unitM hc P s κ _ _ _ _ _)
    (fun u j => unitMLimitV c P s κ (unitMMasses P.m a A b B cs) (restMomentum P.m)
      (curveMomentum P.m u) 0 j.1 j.2.1 j.2.2)
    (fun u hu j => by
      obtain ⟨Q, hQ, -, hv⟩ := exists_quartic_unitMLimitV hc P hm hs hμ₀ hM
        (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
        ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) hX j.1 j.2.1 j.2.2
      refine ⟨Q, hQ, ?_, hv⟩
      rw [unitMPauliF_eq]
      exact refinedBound_unitM hc P s κ _ _ _ _ _)
    (unitMPauliW P) (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m) hK0 hKb hu0 hu
  have eS : ∀ u, unitMPauliS c P s κ (unitMMasses P.m a A b B cs) 0 u =
      ∑ j : Idx, unitMPauliW P u j * unitMLimitV c P s κ (unitMMasses P.m a A b B cs)
        (restMomentum P.m) (curveMomentum P.m u) 0 j.1 j.2.1 j.2.2 := fun u => by
    simp only [unitMPauliS, pauliNum_eq_sum_idx, unitMPauliW]
  rw [eS u, eS (-u)]
  refine h.trans ?_
  have hpc := pieceConst_nonneg (unitMMatrix c s κ)
    (fun u => unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m u)) 8 4 4 8
    (unitMQk hc P) (unitMPauliW P)
  have hL : (1 + K) ^ 2 ≤ L ^ 2 * (1 + S) ^ 2 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    nlinarith
  have hden : 0 < (3 / 4 : ℝ) ^ (4 + 4 + 4) * unitConst P.m μ₀ ^ (r + 7 - 3) := by positivity
  change unitMPauliConst hc P s κ * (1 + K) ^ 2 /
      ((3 / 4 : ℝ) ^ (4 + 4 + 4) * unitConst P.m μ₀ ^ (r + 7 - 3)) ≤ _
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hden, mul_assoc]
  exact mul_le_mul_of_nonneg_left hL hpc

/-- **The `q → 0` value of the unit, bounded uniformly in the masses** (`n = 0`, the scales
fixed): `‖unitMPauliZero‖ ≤ C (1 + ∑ᵢ Mᵢ²)²` for all photon and extra masses `≥ μ₀`. -/
theorem norm_unitMPauliZero_le {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {κ : Fin r → ℝ}
    (hκ : ∀ j, 0 < κ j ∧ κ j ≤ 1) :
    ∃ C : ℝ, ∀ (a A b B : ℝ) (cs : Fin r → ℝ), MassesGe μ₀ a A b B → (∀ j, μ₀ ≤ cs j) →
      ‖unitMPauliZero c P s κ (unitMMasses P.m a A b B cs)‖ ≤
        C * (1 + ∑ i, unitMMasses P.m a A b B cs i ^ 2) ^ 2 := by
  obtain ⟨C, hC⟩ := norm_unitMPauliQuot_le hc P hm hs hμ₀ hκ
  refine ⟨C, fun a A b B cs hM hcs => ?_⟩
  have hX : ExtraGe μ₀ κ cs := fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩
  have hT := (tendsto_unitM_explicit hc P hm hs hμ₀ hM hX).norm
  refine le_of_tendsto hT ?_
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), |u| ≤ 1 / 2 :=
    Filter.Eventually.mono (nhdsWithin_le_nhds (Icc_mem_nhds
      (by norm_num : (-(1 / 2) : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 2)))
      fun u hu => abs_le.2 hu
  filter_upwards [h0, self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
  exact hC a A b B cs hM hcs u hu0 hu

theorem sum_sq_unitMMasses_succ {r : ℕ} (m a A b B : ℝ) (cs : Fin (r + 1) → ℝ) :
    ∑ i, unitMMasses m a A b B cs i ^ 2 =
      ∑ i, unitMMasses m a A b B (Fin.init cs) i ^ 2 + cs (Fin.last r) ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  congr 1

/-- **The `q → 0` values with powers of `k²`, bounded uniformly in the masses**: if the last
`n ≤ r` extra lines are unscaled, one constant `C` with
`‖unitMPauliZeroPow n‖ ≤ C (1 + ∑ᵢ Mᵢ²)ⁿ⁺²` for all photon and extra masses `≥ μ₀`. -/
theorem norm_unitMPauliZeroPow_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) (n : ℕ) :
    ∀ {r : ℕ} {κ : Fin r → ℝ}, n ≤ r → TrailOne n κ → (∀ j, 0 < κ j ∧ κ j ≤ 1) →
    ∃ C : ℝ, ∀ (a A b B : ℝ) (cs : Fin r → ℝ), MassesGe μ₀ a A b B → (∀ j, μ₀ ≤ cs j) →
      ‖unitMPauliZeroPow c P s κ (unitMMasses P.m a A b B cs) n‖ ≤
        C * (1 + ∑ i, unitMMasses P.m a A b B cs i ^ 2) ^ (n + 2) := by
  induction n with
  | zero =>
    intro r κ _ _ hκ
    obtain ⟨C, hC⟩ := norm_unitMPauliZero_le hc P hm hs hμ₀ hκ
    refine ⟨C, fun a A b B cs hM hcs => ?_⟩
    rw [unitMPauliZeroPow_zero hc P hm hs hμ₀ hM fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩]
    exact hC a A b B cs hM hcs
  | succ n ih =>
    intro r κ hnr hT hκ
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨C₁, hC₁⟩ := ih (r := r) (κ := Fin.init κ) (by omega) hT.init fun j => hκ _
    obtain ⟨C₂, hC₂⟩ := ih (r := r + 1) (κ := κ) (by omega) hT.of_succ hκ
    refine ⟨|C₁| + |C₂|, fun a A b B cs hM hcs => ?_⟩
    have hX : ExtraGe μ₀ κ cs := fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩
    rw [unitMPauliZeroPow_succ hc P hm hs hμ₀ hM hnr hT hX]
    set S := ∑ i, unitMMasses P.m a A b B cs i ^ 2 with hS
    have hS₁ := sum_sq_unitMMasses_succ P.m a A b B cs
    rw [← hS] at hS₁
    have hS₁0 : 0 ≤ ∑ i, unitMMasses P.m a A b B (Fin.init cs) i ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have hl0 : 0 ≤ cs (Fin.last r) ^ 2 := sq_nonneg _
    have h1 := hC₁ a A b B (Fin.init cs) hM fun j => hcs _
    have h2 := hC₂ a A b B cs hM hcs
    have hpow₁ : (1 + ∑ i, unitMMasses P.m a A b B (Fin.init cs) i ^ 2) ^ (n + 2) ≤
        (1 + S) ^ (n + 2) := pow_le_pow_left₀ (by positivity) (by linarith) _
    have hpow : (1 + S) ^ (n + 2) ≤ (1 + S) ^ (n + 1 + 2) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hP0 : 0 ≤ (1 + S) ^ (n + 2) := pow_nonneg (by linarith) _
    have hn1 : ‖unitMPauliZeroPow c P s (Fin.init κ)
        (unitMMasses P.m a A b B (Fin.init cs)) n‖ ≤ |C₁| * (1 + S) ^ (n + 1 + 2) :=
      h1.trans ((mul_le_mul_of_nonneg_left hpow₁ (abs_nonneg _)).trans'
        (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (by positivity) _)) |>.trans
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)))
    have hn2 : ‖((cs (Fin.last r) ^ 2 : ℝ) : ℂ) *
        unitMPauliZeroPow c P s κ (unitMMasses P.m a A b B cs) n‖ ≤
          |C₂| * (1 + S) ^ (n + 1 + 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0,
        show n + 1 + 2 = n + 2 + 1 by omega, pow_succ]
      have h3 : C₂ * (1 + S) ^ (n + 2) ≤ |C₂| * (1 + S) ^ (n + 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hP0
      have h4 : cs (Fin.last r) ^ 2 ≤ 1 + S := by linarith
      calc cs (Fin.last r) ^ 2 * ‖unitMPauliZeroPow c P s κ (unitMMasses P.m a A b B cs) n‖
          ≤ (1 + S) * (|C₂| * (1 + S) ^ (n + 2)) :=
            mul_le_mul h4 (h2.trans h3) (norm_nonneg _) (by linarith)
        _ = |C₂| * ((1 + S) ^ (n + 2) * (1 + S)) := by ring
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ |C₁| * (1 + S) ^ (n + 1 + 2) + |C₂| * (1 + S) ^ (n + 1 + 2) := add_le_add hn1 hn2
      _ = (|C₁| + |C₂|) * (1 + S) ^ (n + 1 + 2) := by ring

end Unit

end QED.ChainProof.SetCUnitM

end
