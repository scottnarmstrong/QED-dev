/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliAtCt
public import QED.ChainProof.SetCLimCtCD01
public import QED.TwoLoop.PauliZeroExplicitCt

/-!
# Set (c): the canonical Pauli limits of the four classes `CD0 t`, `CD1 t`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The limit of
`CD1 t` (`CD0 t`) is `cdInLim` (`cdOutLim`), the sum of the limits `pieceLim` of two products of
product data (`QED/ChainProof/SetCLimCtCD01.lean`). Each is a parametric value divided by
`auxLimit m`, so Phase 4's explicit second-order limit of product data
(`QED.TwoLoop.PauliZeroExplicit.tendsto_kinds_explicit`) identifies the limit of the even quotient
of its Pauli numerator along the curve as `kindsZero`. The Pauli numerator of the class limit is
even along the curve (`cdInLim_map`, `cdOutLim_map` with the reflection), so the quotient itself
converges, and `QED.ChainProof.SetCUnit.tendsto_formFactorProj₂_of` gives the canonical limit.

## Main statements

* `tendsto_evenQuot_pieceLim`: the even quotient of the Pauli numerator of `pieceLim` along the
  curve tends to `kindsZero`;
* `cdInZero`, `cdOutZero`: the `q → 0` values of the limits of `CD1 t`, `CD0 t`;
* **`setCClassPauli_CD01`**: the per-class Pauli limits of the four classes `CDₖ t`, `k < 2`,
  with the values `cd01PauliVal k = cd{Out,In}Zero (cdParams …) / (64 e m⁵)`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set
open QED.WickModel (Params)

namespace QED.ChainProof.SetCPauli

open QED.Dirac QED.TwoLoop.CountertermLimit QED.TwoLoop.Insertion QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.TwoLoop.ReflCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.Integration.TwoLoop (IntNoSubdivergenceRefined)
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### The even quotient of a product limit -/

/-- **The explicit second-order limit of a product limit** `pieceLim` along the curve. -/
theorem tendsto_evenQuot_pieceLim {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) (P : Params) (hm : 0 < P.m) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = P.m ^ 2) (hMp : ∀ i, κ i = .pho → μ₀ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (d : (Fin 4 → ℝ) → ℝ → (Fin 4 → ℝ) → ℂ)
    (N : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hN : ∀ p' μ i j, IsLoopPoly 2 4 fun ℓ => N p' μ (ℓ 0) i j)
    (hNp : ∀ μ i j k, IsLoopPoly 1 4 fun y => N (y 0) μ k i j)
    (hfac : ∀ p' (ε : ℝ), 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      ∏ i, (propDenom (Ms i) ε ((κ i).lineMom (restMomentum P.m) p' ℓ))⁻¹ =
        d p' ε (ℓ 0) * ((propDenom P.m ε (ℓ 1))⁻¹) ^ 3) :
    Tendsto (evenQuot fun u => pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
        (pieceLim (d (curveMomentum P.m u)) (N (curveMomentum P.m u))))
      (𝓝[≠] 0) (𝓝 (kindsZero κ Ms P N)) :=
  tendsto_kinds_explicit hm7 κ Ms P hm hμ₀ hMe hMp hcrit N hNp
    (fun p' => pieceLim (d p') (N p')) fun u hu μ i j => by
      obtain ⟨v, hv, -, hV⟩ := pieceLim_entry hm7 κ Ms hm hμ₀ hMe hMp hcrit hcard hE
        (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
        ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) (d (curveMomentum P.m u))
        (N (curveMomentum P.m u)) (hN _) (hfac _) μ i j
      exact ⟨v, hv, hV⟩

/-! ### The numerators as polynomials in `p'` -/

section Poly

variable (P : Params) (p : Fin 4 → ℝ) (μ i j : Fin 4) (k : Fin 4 → ℝ)

theorem isLoopPolyMat_electronNumerator_out (m : ℝ) :
    IsLoopPolyMat 1 1 fun y : Fin 1 → Fin 4 → ℝ => electronNumerator m (y 0 + k) :=
  (isLoopAffine_out_add k).isLoopPolyMat_electronNumerator m

theorem isLoopPolyMat_mergeY_out (m δ₂ δm : ℝ) :
    IsLoopPolyMat 1 1 fun y : Fin 1 → Fin 4 → ℝ => mergeY m δ₂ δm (y 0 + k) := by
  unfold mergeY
  exact isLoopPolyMat_add (isLoopPolyMat_smul _ (isLoopPolyMat_electronNumerator_out k m))
    (isLoopPolyMat_mono (isLoopPolyMat_smul _ (IsLoopPolyMat.const _)) (by norm_num))

theorem isLoopPoly_numIn₁_out : IsLoopPoly 1 4 fun y => numIn₁ P (y 0) p μ k i j := by
  have h := isLoopPolyMat_vertexChain (L := 1) (a := 1) (b := 0) (d := 0) P.e μ
    (A := fun y => electronNumerator P.m (y 0 + k))
    (B := fun _ => -mergeY P.m P.δ₂ P.δm (p + k)) (D := fun _ => photonNum P.δ₃ P.mγ P.Λ k)
    (isLoopPolyMat_electronNumerator_out k P.m) (IsLoopPolyMat.const _)
    (fun _ _ => IsLoopPoly.const _)
  exact (h i j).mono (by norm_num)

theorem isLoopPoly_numIn₂_out : IsLoopPoly 1 4 fun y => numIn₂ P (y 0) p μ k i j := by
  have h := isLoopPolyMat_vertexChain (L := 1) (a := 1) (b := 0) (d := 0) P.e μ
    (A := fun y => electronNumerator P.m (y 0 + k))
    (B := fun _ => -(mergeC P.m P.δ₂ P.δm • electronNumerator P.m (p + k)))
    (D := fun _ => photonNum P.δ₃ P.mγ P.Λ k)
    (isLoopPolyMat_electronNumerator_out k P.m) (IsLoopPolyMat.const _)
    (fun _ _ => IsLoopPoly.const _)
  exact (h i j).mono (by norm_num)

theorem isLoopPoly_numOut₁_out : IsLoopPoly 1 4 fun y => numOut₁ P (y 0) p μ k i j := by
  have h := isLoopPolyMat_vertexChain (L := 1) (a := 1) (b := 0) (d := 0) P.e μ
    (A := fun y => -mergeY P.m P.δ₂ P.δm (y 0 + k))
    (B := fun _ => electronNumerator P.m (p + k)) (D := fun _ => photonNum P.δ₃ P.mγ P.Λ k)
    (isLoopPolyMat_neg (isLoopPolyMat_mergeY_out k P.m P.δ₂ P.δm)) (IsLoopPolyMat.const _)
    (fun _ _ => IsLoopPoly.const _)
  exact (h i j).mono (by norm_num)

theorem isLoopPoly_numOut₂_out : IsLoopPoly 1 4 fun y => numOut₂ P (y 0) p μ k i j := by
  have h := isLoopPolyMat_vertexChain (L := 1) (a := 1) (b := 0) (d := 0) P.e μ
    (A := fun y => -(mergeC P.m P.δ₂ P.δm • electronNumerator P.m (y 0 + k)))
    (B := fun _ => electronNumerator P.m (p + k)) (D := fun _ => photonNum P.δ₃ P.mγ P.Λ k)
    (isLoopPolyMat_neg (isLoopPolyMat_smul _ (isLoopPolyMat_electronNumerator_out k P.m)))
    (IsLoopPolyMat.const _) (fun _ _ => IsLoopPoly.const _)
  exact (h i j).mono (by norm_num)

end Poly

/-! ### The `q → 0` values of `CD0 t`, `CD1 t` -/

/-- The `q → 0` value of the limit of `CD1 t`. -/
noncomputable def cdInZero (Q : Params) : ℂ :=
  kindsZero kindsD3 (massesD3 Q) Q (fun p' => numIn₁ Q p' (restMomentum Q.m)) +
    kindsZero kindsIn₂ (massesD₂ Q) Q (fun p' => numIn₂ Q p' (restMomentum Q.m))

/-- The `q → 0` value of the limit of `CD0 t`. -/
noncomputable def cdOutZero (Q : Params) : ℂ :=
  kindsZero kindsD3 (massesD3 Q) Q (fun p' => numOut₁ Q p' (restMomentum Q.m)) +
    kindsZero kindsOut₂ (massesD₂ Q) Q (fun p' => numOut₂ Q p' (restMomentum Q.m))

section Zero

variable (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ)
include hm hmγ hΛ

theorem tendsto_evenQuot_cdIn :
    Tendsto (evenQuot fun u => pauliNum Q.m (curveMomentum Q.m u) (restMomentum Q.m)
        (cdInLim Q (curveMomentum Q.m u) (restMomentum Q.m))) (𝓝[≠] 0) (𝓝 (cdInZero Q)) := by
  have h₁ := tendsto_evenQuot_pieceLim (by norm_num) kindsD3 (massesD3 Q) Q hm (lt_min hmγ hΛ)
    (massesD3_sq_of_ne_pho Q) (min_sq_le_massesD3_sq Q hmγ hΛ) intNoSubdivergenceRefined_kindsD3
    (by decide) (by decide) (fun p' => den₁ Q p' (restMomentum Q.m))
    (fun p' => numIn₁ Q p' (restMomentum Q.m))
    (fun p' μ i j => (affMat_numIn₁ Q p' _ μ i j).isLoopPoly)
    (fun μ i j k => isLoopPoly_numIn₁_out Q _ μ i j k)
    (fun p' ε _ ℓ => den₁_fac Q _ p' ε ℓ)
  have h₂ := tendsto_evenQuot_pieceLim (by norm_num) kindsIn₂ (massesD₂ Q) Q hm (lt_min hmγ hΛ)
    (massesD₂_sq_of_ne_pho_in Q) (min_sq_le_massesD₂_sq_in Q hmγ hΛ)
    intNoSubdivergenceRefined_kindsIn₂ (by decide) (by decide)
    (fun p' => denIn₂ Q p' (restMomentum Q.m)) (fun p' => numIn₂ Q p' (restMomentum Q.m))
    (fun p' μ i j => (affMat_numIn₂ Q p' _ μ i j).isLoopPoly)
    (fun μ i j k => isLoopPoly_numIn₂_out Q _ μ i j k)
    (fun p' ε _ ℓ => denIn₂_fac Q _ p' ε ℓ)
  refine (h₁.add h₂).congr fun u => ?_
  simp only [evenQuot, cdInLim]
  rw [show (pieceLim (den₁ Q (curveMomentum Q.m u) (restMomentum Q.m))
      (numIn₁ Q (curveMomentum Q.m u) (restMomentum Q.m)) +
      pieceLim (denIn₂ Q (curveMomentum Q.m u) (restMomentum Q.m))
      (numIn₂ Q (curveMomentum Q.m u) (restMomentum Q.m))) = fun μ => _ + _ from rfl,
    show (pieceLim (den₁ Q (curveMomentum Q.m (-u)) (restMomentum Q.m))
      (numIn₁ Q (curveMomentum Q.m (-u)) (restMomentum Q.m)) +
      pieceLim (denIn₂ Q (curveMomentum Q.m (-u)) (restMomentum Q.m))
      (numIn₂ Q (curveMomentum Q.m (-u)) (restMomentum Q.m))) = fun μ => _ + _ from rfl,
    pauliNum_add, pauliNum_add]
  ring

theorem tendsto_evenQuot_cdOut :
    Tendsto (evenQuot fun u => pauliNum Q.m (curveMomentum Q.m u) (restMomentum Q.m)
        (cdOutLim Q (curveMomentum Q.m u) (restMomentum Q.m))) (𝓝[≠] 0)
      (𝓝 (cdOutZero Q)) := by
  have h₁ := tendsto_evenQuot_pieceLim (by norm_num) kindsD3 (massesD3 Q) Q hm (lt_min hmγ hΛ)
    (massesD3_sq_of_ne_pho Q) (min_sq_le_massesD3_sq Q hmγ hΛ) intNoSubdivergenceRefined_kindsD3
    (by decide) (by decide) (fun p' => den₁ Q p' (restMomentum Q.m))
    (fun p' => numOut₁ Q p' (restMomentum Q.m))
    (fun p' μ i j => (affMat_numOut₁ Q p' _ μ i j).isLoopPoly)
    (fun μ i j k => isLoopPoly_numOut₁_out Q _ μ i j k)
    (fun p' ε _ ℓ => den₁_fac Q _ p' ε ℓ)
  have h₂ := tendsto_evenQuot_pieceLim (by norm_num) kindsOut₂ (massesD₂ Q) Q hm (lt_min hmγ hΛ)
    (massesD₂_sq_of_ne_pho_out Q) (min_sq_le_massesD₂_sq_out Q hmγ hΛ)
    intNoSubdivergenceRefined_kindsOut₂ (by decide) (by decide)
    (fun p' => denOut₂ Q p' (restMomentum Q.m)) (fun p' => numOut₂ Q p' (restMomentum Q.m))
    (fun p' μ i j => (affMat_numOut₂ Q p' _ μ i j).isLoopPoly)
    (fun μ i j k => isLoopPoly_numOut₂_out Q _ μ i j k)
    (fun p' ε _ ℓ => denOut₂_fac Q _ p' ε ℓ)
  refine (h₁.add h₂).congr fun u => ?_
  simp only [evenQuot, cdOutLim]
  rw [show (pieceLim (den₁ Q (curveMomentum Q.m u) (restMomentum Q.m))
      (numOut₁ Q (curveMomentum Q.m u) (restMomentum Q.m)) +
      pieceLim (denOut₂ Q (curveMomentum Q.m u) (restMomentum Q.m))
      (numOut₂ Q (curveMomentum Q.m u) (restMomentum Q.m))) = fun μ => _ + _ from rfl,
    show (pieceLim (den₁ Q (curveMomentum Q.m (-u)) (restMomentum Q.m))
      (numOut₁ Q (curveMomentum Q.m (-u)) (restMomentum Q.m)) +
      pieceLim (denOut₂ Q (curveMomentum Q.m (-u)) (restMomentum Q.m))
      (numOut₂ Q (curveMomentum Q.m (-u)) (restMomentum Q.m))) = fun μ => _ + _ from rfl,
    pauliNum_add, pauliNum_add]
  ring

/-! ### Evenness along the curve -/

theorem cdNum_neg (k : Fin 5) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    pauliNum Q.m (curveMomentum Q.m (-u)) (restMomentum Q.m)
        ((if k = 0 then cdOutLim Q else cdInLim Q) (curveMomentum Q.m (-u))
          (restMomentum Q.m)) =
      pauliNum Q.m (curveMomentum Q.m u) (restMomentum Q.m)
        ((if k = 0 then cdOutLim Q else cdInLim Q) (curveMomentum Q.m u)
          (restMomentum Q.m)) := by
  have h := isSpinLift_reflect (K := axisOne) (by rw [dot_axisOne]; exact one_ne_zero)
  have hq := (dot_curveMomentum_sub Q.m hu).symm ▸ curveQ_nonneg Q.m hu
  have hW : ∀ μ, _ * (if k = 0 then cdOutLim Q else cdInLim Q)
      (_ *ᵥ curveMomentum Q.m u) (_ *ᵥ restMomentum Q.m) μ * _ =
      vecAct _ ((if k = 0 then cdOutLim Q else cdInLim Q) (curveMomentum Q.m u)
        (restMomentum Q.m)) μ := fun μ => by
    split_ifs
    · exact cdOutLim_map Q hm hmγ hΛ h (dot_restMomentum (m := Q.m))
        (dot_curveMomentum Q.m hu) hq μ
    · exact cdInLim_map Q hm hmγ hΛ h (dot_restMomentum (m := Q.m))
        (dot_curveMomentum Q.m hu) hq μ
  have e := pauliNum_map h Q.m (curveMomentum Q.m u) (restMomentum Q.m) hW
  rw [reflectMatrix_curveMomentum, reflectMatrix_restMomentum] at e
  exact e

end Zero

/-! ### The per-class Pauli limits -/

variable {P₀ : Params}

/-- The per-class Pauli values of `CD0 t` (`k = 0`) and `CD1 t` (`k = 1`). -/
noncomputable def cd01PauliVal (P₀ : Params) (k : Fin 5) : ClsPauliVal :=
  fun M₁ M₂ c₁ c₂ mγ Λ D s =>
    (if k = 0 then cdOutZero (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s)
      else cdInZero (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s)) / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)

/-- **The canonical Pauli limits of the four classes `CDₖ t`, `k < 2`.** -/
theorem setCClassPauli_CD01 (k : Fin 5) (hk : k < 2) (t : Fin 2) :
    SetCClassPauli ctFam P₀ (.inr (.inl (k, t))) (cd01PauliVal P₀ k) := by
  refine setCClassPauli_of_tendsto
    (fun M₁ M₂ c₁ c₂ mγ Λ D s p' p => cd01Lim P₀ M₁ M₂ c₁ c₂ mγ Λ D s k p' p)
    (fun M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq => isClassLimC_CD01 hA k hk t hpq)
    fun M₁ M₂ c₁ c₂ mγ Λ D s hA => ?_
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  set Q := cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s
  have hL : Tendsto (evenQuot fun u => pauliNum Q.m (curveMomentum Q.m u) (restMomentum Q.m)
      ((if k = 0 then cdOutLim Q else cdInLim Q) (curveMomentum Q.m u) (restMomentum Q.m)))
      (𝓝[≠] 0) (𝓝 (if k = 0 then cdOutZero Q else cdInZero Q)) := by
    split_ifs
    · exact tendsto_evenQuot_cdOut Q hm hmγ hΛ
    · exact tendsto_evenQuot_cdIn Q hm hmγ hΛ
  have h := QED.ChainProof.SetCUnit.tendsto_formFactorProj₂_of hm P₀.e
    (fun p' => (if k = 0 then cdOutLim Q else cdInLim Q) p' (restMomentum Q.m))
    (tendsto_div_of_evenQuot (fun _ hu => cdNum_neg Q hm hmγ hΛ k hu) hL)
  refine h.congr fun x => ?_
  simp only [cd01Lim]
  split_ifs <;> rfl

end QED.ChainProof.SetCPauli

end
