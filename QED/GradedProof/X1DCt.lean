/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1DOpen
public import QED.TwoLoop.CountertermLimit
public import QED.OneLoop.VertexOffShell

/-!
# (X₁) piece D: the counterterm classes off the mass shell

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece D. For each of the seven counterterm classes of the order-`e⁵` vertex,
at external momenta `y = (r', r)` near an on-shell pair `(p', p)` with `(p' - p)² ≥ 0` (and, for
the `δ₁` classes, positive energies), the class value converges as `ε → 0⁺`, to a limit
continuous at `(p', p)` (`offLim_contractionValue₂_ctClass`).

* `δ₂`, `δ_m`, `δ₃` classes: the one-loop value times the auxiliary integral
  `∫ (k² + m² - iε)⁻³` is a two-loop integral with the product line data of
  `QED.TwoLoop.CountertermLimit.LineKind` (`offLim_of_kinds`); the two-loop integral is handled
  by `QED.GradedProof.X1D.exists_tendsto_cont`, the auxiliary integral converges to
  `auxLimit m ≠ 0` independently of `y`.
* `δ₁` classes: `δ₁` times the one-loop vertex, whose off-shell limit and its continuity are
  `QED.OneLoop.VertexOffShell.exists_tendsto_vertexIntegral_offShell` (`offLim_vertexValue`).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.Bridge QED.TwoLoop.Relabel
open QED.TwoLoop.CountertermLimit
open QED.Integration.TwoLoop (lineDenom castLoopMatrix RefinedBound
  IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff symanzikU symanzikV)

namespace QED.GradedProof.X1D

/-! ### Product data by kinds, off the shell -/

theorem isLoopPoly_kindMom (k : LineKind) (ν : Fin 4) :
    IsLoopPoly 2 1 fun y : Fin 2 → Fin 4 → ℝ => ((k.mom (y 1) (y 0) ν : ℝ) : ℂ) := by
  rcases k with _ | _ | _ | _ <;> simp only [LineKind.mom]
  · exact IsLoopPoly.coord 0 ν le_rfl
  · exact IsLoopPoly.coord 1 ν le_rfl
  · simpa using IsLoopPoly.const (L := 2) (n := 1) (0 : ℂ)
  · simpa using IsLoopPoly.const (L := 2) (n := 1) (0 : ℂ)

theorem continuous_kindMom (k : LineKind) :
    Continuous fun y : Fin 2 → Fin 4 → ℝ => k.mom (y 1) (y 0) := by
  rcases k with _ | _ | _ | _ <;> simp only [LineKind.mom]
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_const
  · exact continuous_const

/-- **The one-loop limit through the product with the auxiliary loop, off the shell.** The
hypotheses of `QED.TwoLoop.CountertermLimit.exists_tendsto_of_kinds` at the on-shell pair
`(p', p)`, with a numerator polynomial in the external data `y = (r', r)` and the factorization
at every `y`. -/
theorem offLim_of_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) {mass μ : ℝ} (hmass : 0 < mass) (hμ : 0 < μ) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = mass ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 2 → Fin 4 → ℝ) → (Fin 4 → ℝ) → ℂ) {n : ℕ}
    (hNy : ∀ k, IsLoopPoly 2 n fun y => N y k) (hN : ∀ y, IsLoopPoly 2 4 fun ℓ => N y (ℓ 0))
    (F : ℝ → (Fin 2 → Fin 4 → ℝ) → (Fin 4 → ℝ) → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ y ℓ,
      N y (ℓ 0) * ∏ i, (propDenom (Ms i) ε ((κ i).lineMom (y 1) (y 0) ℓ))⁻¹ =
        F ε y (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    OffLim (fun ε y => QED.OneLoop.energyFirstIntegral (F ε y)) (pairY p' p) := by
  set α := castLoopMatrix fun i => (κ i).dir
  set mom : (Fin 2 → Fin 4 → ℝ) → Fin (m + 1) → Fin 4 → ℝ := fun y i => (κ i).mom (y 1) (y 0)
  have hmomc : ContinuousAt mom (pairY p' p) :=
    (continuous_pi fun i => continuous_kindMom (κ i)).continuousAt
  have hα : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), α e = ![1, 0] := by
    intro e he
    have h := hE e he
    funext s
    rcases hk : κ e with _ | _ | _ | _
    · fin_cases s <;> simp [α, castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [α, castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [α, castLoopMatrix, hk, LineKind.dir]
    · exact absurd hk h
  have hNB : ∀ y, RefinedBound α {0, 1, 2, 3} 4 fun ℓ => N y (ℓ 0) := fun y => by
    obtain ⟨Q, hQ⟩ := (hN y).exists_loopQuartic
    rw [← hQ]
    exact refinedBound_of_dependsOnZero _ hcard hα Q fun ℓ => by
      simp only [hQ, Matrix.cons_val_zero]
  have hc : 0 < 3 / 4 * min (mass ^ 2) (μ ^ 2) := by positivity
  have hV := eventually_symanzikV_ge (α := α) hmomc Ms hc fun z hz hz1 hU => by
    have h := symanzikV_kinds_ge κ Ms hp hp' hq hMe hMp hz hz1 hU
    simpa [mom, pairY] using h
  obtain ⟨G, hG, hGc⟩ := exists_tendsto_cont α Ms hm7
    ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit)
    (fun i ν => isLoopPoly_kindMom (κ i) ν) (N := fun y ℓ => N y (ℓ 0)) (fun ℓ => hNy (ℓ 0))
    hN hNB (half_pos hc) hV
  have hH := tendsto_energyFirstIntegral_aux hmass
  have hH0 := auxLimit_ne_zero hmass
  refine ⟨fun y => G y / auxLimit mass, ?_, hGc.div_const _⟩
  filter_upwards [hG] with y hy
  refine (hy.div hH hH0).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hH.eventually_ne hH0] with ε (hε : 0 < ε) hne
  have e : (fun ℓ => N y (ℓ 0) * ∏ i, (lineDenom α (mom y) Ms ε i ℓ)⁻¹) =
      fun ℓ => F ε y (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3 := funext fun ℓ => by
    rw [prod_lineDenom_kinds]
    exact hfac ε hε y ℓ
  rw [Pi.div_apply, e, jointEnergyFirstIntegral_two_mul (F ε y)
    (fun k => ((propDenom mass ε k)⁻¹) ^ 3)]
  exact mul_div_cancel_right₀ _ hne

/-! ### The numerators as polynomials in `(r', r)` -/

theorem isLoopAffine_y_add (j : Fin 2) (k : Fin 4 → ℝ) :
    IsLoopAffine fun y : Fin 2 → Fin 4 → ℝ => y j + k := by
  fin_cases j
  · exact ⟨![1, 0], k, fun y => by funext σ; simp [Fin.sum_univ_two, add_comm]⟩
  · exact ⟨![0, 1], k, fun y => by funext σ; simp [Fin.sum_univ_two, add_comm]⟩

theorem isLoopPolyMat_insertion_y (m δ₂ δm : ℝ) (j : Fin 2) (k : Fin 4 → ℝ) :
    IsLoopPolyMat 2 3 fun y => -(electronNumerator m (y j + k) *
      fermionCtMatrix δ₂ δm m (y j + k) * electronNumerator m (y j + k)) := by
  have hA := isLoopAffine_y_add j k
  have hC : IsLoopPolyMat 2 1 fun y => fermionCtMatrix δ₂ δm m (y j + k) := by
    simp only [fermionCtMatrix_eq]
    exact isLoopPolyMat_add (isLoopPolyMat_smul _ (hA.isLoopPolyMat_electronNumerator 0))
      (isLoopPolyMat_mono (isLoopPolyMat_smul _
        (IsLoopPolyMat.const (1 : Matrix (Fin 4) (Fin 4) ℂ))) (Nat.zero_le _))
  exact isLoopPolyMat_neg (((hA.isLoopPolyMat_electronNumerator m).mul hC).mul
    (hA.isLoopPolyMat_electronNumerator m))

theorem isLoopPoly_numD2In_y (P : Params) (μ i j : Fin 4) (k : Fin 4 → ℝ) :
    IsLoopPoly 2 4 fun y : Fin 2 → Fin 4 → ℝ => numD2In P (y 0) (y 1) μ k i j :=
  isLoopPolyMat_vertexChain (L := 2) (a := 1) (b := 3) (d := 0) P.e μ
    (A := fun y => electronNumerator P.m (y 0 + k))
    (B := fun y => -(electronNumerator P.m (y 1 + k) * fermionCtMatrix P.δ₂ P.δm P.m (y 1 + k) *
      electronNumerator P.m (y 1 + k)))
    (D := fun _ => pvPhotonNum P.mγ P.Λ)
    ((isLoopAffine_y_add 0 k).isLoopPolyMat_electronNumerator P.m)
    (isLoopPolyMat_insertion_y P.m P.δ₂ P.δm 1 k) (fun _ _ => IsLoopPoly.const _) i j

theorem isLoopPoly_numD2Out_y (P : Params) (μ i j : Fin 4) (k : Fin 4 → ℝ) :
    IsLoopPoly 2 4 fun y : Fin 2 → Fin 4 → ℝ => numD2Out P (y 0) (y 1) μ k i j :=
  isLoopPolyMat_vertexChain (L := 2) (a := 3) (b := 1) (d := 0) P.e μ
    (A := fun y => -(electronNumerator P.m (y 0 + k) *
      fermionCtMatrix P.δ₂ P.δm P.m (y 0 + k) * electronNumerator P.m (y 0 + k)))
    (B := fun y => electronNumerator P.m (y 1 + k))
    (D := fun _ => pvPhotonNum P.mγ P.Λ)
    (isLoopPolyMat_insertion_y P.m P.δ₂ P.δm 0 k)
    ((isLoopAffine_y_add 1 k).isLoopPolyMat_electronNumerator P.m)
    (fun _ _ => IsLoopPoly.const _) i j

theorem isLoopPoly_numD3_y (P : Params) (μ i j : Fin 4) (k : Fin 4 → ℝ) :
    IsLoopPoly 2 2 fun y : Fin 2 → Fin 4 → ℝ => numD3 P (y 0) (y 1) μ k i j :=
  isLoopPolyMat_vertexChain (L := 2) (a := 1) (b := 1) (d := 0) P.e μ
    (A := fun y => electronNumerator P.m (y 0 + k))
    (B := fun y => electronNumerator P.m (y 1 + k))
    (D := fun _ => photonNum P.δ₃ P.mγ P.Λ k)
    ((isLoopAffine_y_add 0 k).isLoopPolyMat_electronNumerator P.m)
    ((isLoopAffine_y_add 1 k).isLoopPolyMat_electronNumerator P.m)
    (fun _ _ => IsLoopPoly.const _) i j

/-! ### The seven classes -/

section Classes

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (αOut βIn μ : Fin 1 → Fin 4)
include hm hmγ hΛ hp hp' hq

theorem offLim_contractionValue₂_d2In :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => contractionValue₂ { P with ε := ε } repD2In
      (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ) (pairY p' p) := by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  refine (offLim_of_kinds (by norm_num) kindsD2In (massesD2In P) hm (lt_min hmγ hΛ) hp hp' hq
    (fun i hi => by fin_cases i <;> simp_all [kindsD2In, massesD2In])
    (fun i hi => by fin_cases i <;> simp_all [kindsD2In, massesD2In])
    (by decide) (by decide) (by decide)
    (fun y k => numD2In P (y 0) (y 1) (μ 0) k (αOut 0) (βIn 0))
    (fun k => isLoopPoly_numD2In_y P _ _ _ k)
    (fun y => isLoopPoly_numD2In P _ _ _ _ _)
    (fun ε y k => vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m ε (y 0 + k))
      (electronInsertion P.m ε P.δ₂ P.δm (y 1 + k))
      (QED.OneLoop.photonPropagator P.mγ P.Λ ε k) (αOut 0) (βIn 0))
    (fun ε hε y ℓ => by
      rw [integrand_d2In_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD2In, massesD2In,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)).congr fun y ε _ => ?_
  exact (contractionValue₂_repD2In { P with ε := ε }
    (pOut := fun _ => y 0) (pIn := fun _ => y 1) (kIn := fun _ => y 0 - y 1)
    (by simp) αOut βIn μ).symm

theorem offLim_contractionValue₂_d2Out :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => contractionValue₂ { P with ε := ε } repD2Out
      (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ) (pairY p' p) := by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  refine (offLim_of_kinds (by norm_num) kindsD2Out (massesD2In P) hm (lt_min hmγ hΛ) hp hp' hq
    (fun i hi => by fin_cases i <;> simp_all [kindsD2Out, massesD2In])
    (fun i hi => by fin_cases i <;> simp_all [kindsD2Out, massesD2In])
    (by decide) (by decide) (by decide)
    (fun y k => numD2Out P (y 0) (y 1) (μ 0) k (αOut 0) (βIn 0))
    (fun k => isLoopPoly_numD2Out_y P _ _ _ k)
    (fun y => isLoopPoly_numD2Out P _ _ _ _ _)
    (fun ε y k => vertexChain P.e (μ 0) (electronInsertion P.m ε P.δ₂ P.δm (y 0 + k))
      (QED.OneLoop.electronPropagator P.m ε (y 1 + k))
      (QED.OneLoop.photonPropagator P.mγ P.Λ ε k) (αOut 0) (βIn 0))
    (fun ε hε y ℓ => by
      rw [integrand_d2Out_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD2Out, massesD2In,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)).congr fun y ε _ => ?_
  exact (contractionValue₂_repD2Out { P with ε := ε }
    (pOut := fun _ => y 0) (pIn := fun _ => y 1) (kIn := fun _ => y 0 - y 1)
    (by simp) αOut βIn μ).symm

theorem offLim_contractionValue₂_d3Slot0 :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => contractionValue₂ { P with ε := ε } repD3Slot0
      (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ) (pairY p' p) := by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  refine (offLim_of_kinds (by norm_num) kindsD3 (massesD3 P) hm (lt_min hmγ hΛ) hp hp' hq
    (fun i hi => by fin_cases i <;> simp_all [kindsD3, massesD3])
    (fun i hi => by fin_cases i <;> simp_all [kindsD3, massesD3])
    (by decide) (by decide) (by decide)
    (fun y k => numD3 P (y 0) (y 1) (μ 0) k (αOut 0) (βIn 0))
    (fun k => isLoopPoly_numD3_y P _ _ _ k)
    (fun y => isLoopPoly_numD3 P _ _ _ _ _)
    (fun ε y k => vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m ε (y 0 + k))
      (QED.OneLoop.electronPropagator P.m ε (y 1 + k))
      (photonInsertion P.δ₃ P.mγ P.Λ ε k) (αOut 0) (βIn 0))
    (fun ε hε y ℓ => by
      rw [integrand_d3_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD3, massesD3,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)).congr fun y ε _ => ?_
  exact (contractionValue₂_repD3Slot0 { P with ε := ε }
    (pOut := fun _ => y 0) (pIn := fun _ => y 1) (kIn := fun _ => y 0 - y 1)
    (by simp) αOut βIn μ).symm

theorem offLim_contractionValue₂_d3Slot1 :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => contractionValue₂ { P with ε := ε } repD3Slot1
      (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ) (pairY p' p) :=
  (offLim_contractionValue₂_d3Slot0 P hm hmγ hΛ hp hp' hq αOut βIn μ).congr fun y ε _ =>
    contractionValue₂_d3Slot0_eq_d3Slot1 { P with ε := ε }
    (pOut := fun _ => y 0) (pIn := fun _ => y 1) (kIn := fun _ => y 0 - y 1)
    (by simp) αOut βIn μ

end Classes

/-! ### The `δ₁` classes -/

/-- **The one-loop vertex off the shell**, as an `OffLim` in `y = (r', r)`. -/
theorem offLim_vertexValue (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (μ i j : Fin 4) :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => vertexValue { P with ε := ε } (y 0) (y 1) μ i j)
      (pairY p' p) := by
  obtain ⟨δ, hδ, V, hV, hVc⟩ := QED.OneLoop.VertexOffShell.exists_tendsto_vertexIntegral_offShell
    (e := P.e) hm hmγ hΛ hp' hp hp0' hp0 μ i j
  have hpair : ContinuousAt (fun y : Fin 2 → Fin 4 → ℝ => (y 0, y 1)) (pairY p' p) :=
    ((continuous_apply 0).prodMk (continuous_apply 1)).continuousAt
  have h0 : ∀ᶠ y in 𝓝 (pairY p' p), dist (y 0) p' < δ :=
    ((continuous_apply 0).tendsto (pairY p' p)).eventually (Metric.ball_mem_nhds p' hδ)
  have h1 : ∀ᶠ y in 𝓝 (pairY p' p), dist (y 1) p < δ :=
    ((continuous_apply 1).tendsto (pairY p' p)).eventually (Metric.ball_mem_nhds p hδ)
  refine ⟨fun y => V (y 0) (y 1), ?_, ?_⟩
  · filter_upwards [h0, h1] with y hy0 hy1
    exact hV _ _ hy0 hy1
  · exact ContinuousAt.comp (f := fun y : Fin 2 → Fin 4 → ℝ => (y 0, y 1))
      (g := fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => V x.1 x.2) (by simpa [pairY] using hVc) hpair

section D1

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (αOut βIn μ : Fin 1 → Fin 4)
include hm hmγ hΛ hp hp' hp0 hp0'

theorem offLim_contractionValue₂_d1At1 :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => contractionValue₂ { P with ε := ε } repD1At1
      (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ) (pairY p' p) :=
  ((offLim_vertexValue P hm hmγ hΛ hp hp' hp0 hp0' (μ 0) (αOut 0) (βIn 0)).const_mul
    (P.δ₁ : ℂ)).congr fun y ε _ =>
      (contractionValue₂_d1At1 { P with ε := ε }
    (pOut := fun _ => y 0) (pIn := fun _ => y 1) (kIn := fun _ => y 0 - y 1)
    (by simp) αOut βIn μ).symm

theorem offLim_contractionValue₂_d1At2 :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => contractionValue₂ { P with ε := ε } repD1At2
      (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ) (pairY p' p) :=
  ((offLim_vertexValue P hm hmγ hΛ hp hp' hp0 hp0' (μ 0) (αOut 0) (βIn 0)).const_mul
    (P.δ₁ : ℂ)).congr fun y ε _ =>
      (contractionValue₂_d1At2 { P with ε := ε }
    (pOut := fun _ => y 0) (pIn := fun _ => y 1) (kIn := fun _ => y 0 - y 1)
    (by simp) αOut βIn μ).symm

theorem offLim_contractionValue₂_d1At3 :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => contractionValue₂ { P with ε := ε } repD1At3
      (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ) (pairY p' p) :=
  ((offLim_vertexValue P hm hmγ hΛ hp hp' hp0 hp0' (μ 0) (αOut 0) (βIn 0)).const_mul
    (P.δ₁ : ℂ)).congr fun y ε _ =>
      (contractionValue₂_d1At3 { P with ε := ε }
    (pOut := fun _ => y 0) (pIn := fun _ => y 1) (kIn := fun _ => y 0 - y 1)
    (by simp) αOut βIn μ).symm

end D1

/-- **Every counterterm class off the shell**: for `m, m_γ, Λ > 0` and an on-shell
positive-energy pair `(p', p)` with `(p' - p)² ≥ 0`, the class value at `y = (r', r)` converges
as `ε → 0⁺` for `y` near `(p', p)`, to a limit continuous at `(p', p)`. -/
theorem offLim_contractionValue₂_ctClass (c : CtClass) (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (αOut βIn μ : Fin 1 → Fin 4) :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => contractionValue₂ { P with ε := ε } c.rep
      (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ) (pairY p' p) := by
  cases c
  · exact offLim_contractionValue₂_d2In P hm hmγ hΛ hp hp' hq αOut βIn μ
  · exact offLim_contractionValue₂_d2Out P hm hmγ hΛ hp hp' hq αOut βIn μ
  · exact offLim_contractionValue₂_d3Slot0 P hm hmγ hΛ hp hp' hq αOut βIn μ
  · exact offLim_contractionValue₂_d3Slot1 P hm hmγ hΛ hp hp' hq αOut βIn μ
  · exact offLim_contractionValue₂_d1At1 P hm hmγ hΛ hp hp' hp0 hp0' αOut βIn μ
  · exact offLim_contractionValue₂_d1At2 P hm hmγ hΛ hp hp' hp0 hp0' αOut βIn μ
  · exact offLim_contractionValue₂_d1At3 P hm hmγ hΛ hp hp' hp0 hp0' αOut βIn μ

end QED.GradedProof.X1D

end
