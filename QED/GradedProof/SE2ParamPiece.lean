/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2FormLemma
public import QED.TwoLoop.ReflCovarianceParam
public import QED.Integration.TwoLoopClassLimitCubic

/-!
# Self-energy pieces with a parametric limit: the limit and its reflection covariance

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2, step L2. A **self-energy piece** is a two-loop joint energy-first
integral `∫ N_p(ℓ) ∏ᵢ Dᵢ(ℓ)⁻¹` whose parametric data (`SEData`) has external line momenta
`cᵢ p` (multiples of the self-energy momentum `p`), at least seven lines, and numerators `N_p`
that are quartics (cubics for seven lines) with the refined bound.

* `SEData.pv`: the parametric value `-π⁴ ∫_Δ paramIntegrand Q α q M 0` of a quartic `Q`; it is the
  limit of the joint integral where `V ≥ c > 0` (`SEData.tendsto_pv`, for eight or more lines by
  `QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_refined`, for seven lines and a
  cubic by `…_of_cubic`), so it depends only on the values of `Q` (`SEData.pv_unique`).
* `SEPiece`: a numerator family `N_p` with quartics at every `p`, the positivity of `V` on the
  region `p² > -T²`, and **spinor covariance** `S N_{Lp}(Lℓ) T = N_p(ℓ)` for every spinor lift
  `(S, T)` of `L` (`QED.TwoLoop.LimitCovariance.IsSpinLift`).
* `SEPiece.W`: the matrix of limits; `SEPiece.tendsto`: the joint integrals converge to it;
  `SEPiece.secov`: it is reflection covariant (`SECov`). The proof is that of
  `QED.TwoLoop.ReflCovariance.conj_eq_vecAct_of_paramValue` without the vector index: the value at
  `Lp` of the quartic `Q₂` equals the value at `p` of `ℓ ↦ Q₂(Lℓ)`
  (`QED.TwoLoop.ReflCovariance.paramIntegrand_map`), and the combination `S N_{Lp}(L·) T` of these
  quartics has the values of `N_p`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Matrix
open scoped Real

namespace QED.GradedProof.SE2

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.ReflCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- **Parametric data of a self-energy piece**: loop matrix, external line momenta `cᵢ p`,
masses, numerator lines, at least seven lines, and the criterion. -/
structure SEData where
  /-- The number of lines minus one. -/
  m : ℕ
  /-- The loop matrix. -/
  α : Fin (m + 1) → Fin 2 → ℝ
  /-- The external line momenta are `cs i • p`. -/
  cs : Fin (m + 1) → ℝ
  /-- The masses. -/
  M : Fin (m + 1) → ℝ
  /-- The numerator lines. -/
  E : Finset (Fin (m + 1))
  hm : 6 ≤ m
  hcrit : NoSubdivergenceRefined 2 E α

namespace SEData

variable (D : SEData)

/-- The external line momenta at the self-energy momentum `p`. -/
def mom (p : Fin 4 → ℝ) : Fin (D.m + 1) → Fin 4 → ℝ := fun i => D.cs i • p

theorem mom_mulVec (L : Matrix (Fin 4) (Fin 4) ℝ) (p : Fin 4 → ℝ) :
    D.mom (L *ᵥ p) = fun i => L *ᵥ D.mom p i := by
  funext i
  simp only [mom, Matrix.mulVec_smul]

/-- An admissible numerator quartic: quartic for eight or more lines, cubic for seven, with the
refined bound. -/
def Good (Q : LoopQuartic) : Prop :=
  (7 ≤ D.m ∨ Q.quart = 0) ∧ RefinedBound D.α D.E 4 Q.eval

/-- A positive lower bound for `V` at the external line momenta `q`. -/
def VPos (q : Fin (D.m + 1) → Fin 4 → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ z : Fin (D.m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
    symanzikU D.α z ≠ 0 → c ≤ symanzikV D.α q D.M z

/-- The parametric value of a quartic at the external line momenta `q`. -/
noncomputable def pv (Q : LoopQuartic) (q : Fin (D.m + 1) → Fin 4 → ℝ) : ℂ :=
  -((π : ℂ) ^ 4) * ∫ x in simplexSet D.m, paramIntegrand Q D.α q D.M 0 x

variable {D}

theorem tendsto_pv {Q : LoopQuartic} (hQ : D.Good Q) {q : Fin (D.m + 1) → Fin 4 → ℝ}
    (hV : D.VPos q) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => Q.eval ℓ * ∏ i, (lineDenom D.α q D.M ε i ℓ)⁻¹)) (𝓝[>] 0) (𝓝 (D.pv Q q)) := by
  obtain ⟨c, hc, hV⟩ := hV
  rcases hQ.1 with h7 | hq
  · exact tendsto_jointEnergyFirstIntegral_of_refined Q D.α q D.M h7 D.hcrit hQ.2 hc hV
  · exact tendsto_jointEnergyFirstIntegral_of_cubic Q D.α q D.M hq D.hm D.hcrit hQ.2 hc hV

theorem integrableOn_pv {Q : LoopQuartic} (hQ : D.Good Q) {q : Fin (D.m + 1) → Fin 4 → ℝ}
    (hV : D.VPos q) : IntegrableOn (paramIntegrand Q D.α q D.M 0) (simplexSet D.m) := by
  obtain ⟨c, hc, hV⟩ := hV
  rcases hQ.1 with h7 | hq
  · exact integrableOn_paramIntegrand_zero Q D.α q D.M h7 D.hcrit hQ.2 hc hV
  · exact integrableOn_paramIntegrand_zero_cubic Q D.α q D.M hq D.hm D.hcrit hQ.2 hc hV

/-- **The parametric value depends only on the values of the quartic.** -/
theorem pv_unique {Q Q' : LoopQuartic} (hQ : D.Good Q) (hQ' : D.Good Q') (he : Q.eval = Q'.eval)
    {q : Fin (D.m + 1) → Fin 4 → ℝ} (hV : D.VPos q) : D.pv Q q = D.pv Q' q := by
  have h := tendsto_pv hQ' hV
  rw [← he] at h
  exact tendsto_nhds_unique (tendsto_pv hQ hV) h

theorem quart_qsum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Q : ι → LoopQuartic)
    (h : ∀ k ∈ s, (Q k).quart = 0) : (qsum s c Q).quart = 0 := by
  funext a b d e
  simp only [qsum, Pi.zero_apply]
  exact Finset.sum_eq_zero fun k hk => by rw [h k hk]; simp

theorem quart_lmap (L : Matrix LoopIndex LoopIndex ℝ) (Q : LoopQuartic) (h : Q.quart = 0) :
    (lmap L Q).quart = 0 := by
  funext a b d e
  simp [lmap, h]

/-- The parametric value is linear on admissible quartics. -/
theorem pv_qsum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Q : ι → LoopQuartic)
    {q : Fin (D.m + 1) → Fin 4 → ℝ}
    (hI : ∀ k ∈ s, IntegrableOn (paramIntegrand (Q k) D.α q D.M 0) (simplexSet D.m)) :
    D.pv (qsum s c Q) q = ∑ k ∈ s, c k * D.pv (Q k) q := by
  simp only [pv, paramIntegrand_qsum]
  rw [integral_finsetSum _ fun k hk => (hI k hk).const_mul (c k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  ring

/-- The value at `L q` of `Q` is the value at `q` of `ℓ ↦ Q(L ℓ)`. -/
theorem pv_map {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S T) (Q : LoopQuartic) (q : Fin (D.m + 1) → Fin 4 → ℝ) :
    D.pv Q (fun i => L *ᵥ q i) = D.pv (lmap (blockL L) Q) q := by
  simp only [pv, paramIntegrand_map h]

end SEData

/-- **A self-energy piece**: parametric data, a numerator family with admissible quartics at
every momentum, the positivity of `V` on the region `p² > -T²`, and spinor covariance. -/
structure SEPiece (T : ℝ) where
  /-- The parametric data. -/
  D : SEData
  /-- The numerator at the momentum `p`. -/
  N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ
  hQ : ∀ p i j, ∃ Q : LoopQuartic, D.Good Q ∧ Q.eval = fun ℓ => N p ℓ i j
  hV : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → D.VPos (D.mom p)
  hcov : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S S' →
    ∀ p ℓ, S * N (L *ᵥ p) (QED.TwoLoop.LimitCovariance.loopAct L ℓ) * S' = N p ℓ

namespace SEPiece

variable {T : ℝ} (P : SEPiece T)

/-- The chosen quartic of the entry `(i, j)` at `p`. -/
noncomputable def quartic (p : Fin 4 → ℝ) (i j : Fin 4) : LoopQuartic :=
  Classical.choose (P.hQ p i j)

theorem good_quartic (p : Fin 4 → ℝ) (i j : Fin 4) : P.D.Good (P.quartic p i j) :=
  (Classical.choose_spec (P.hQ p i j)).1

theorem eval_quartic (p : Fin 4 → ℝ) (i j : Fin 4) :
    (P.quartic p i j).eval = fun ℓ => P.N p ℓ i j :=
  (Classical.choose_spec (P.hQ p i j)).2

/-- **The limit matrix** of the piece. -/
noncomputable def W (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => P.D.pv (P.quartic p i j) (P.D.mom p)

/-- **The joint integrals converge to `W`** on the region. -/
theorem tendsto {p : Fin 4 → ℝ} (hp : -T ^ 2 < Minkowski.dot p p) (i j : Fin 4) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.N p ℓ i j * ∏ k, (lineDenom P.D.α (P.D.mom p) P.D.M ε k ℓ)⁻¹)) (𝓝[>] 0)
      (𝓝 (P.W p i j)) := by
  have h := SEData.tendsto_pv (P.good_quartic p i j) (P.hV p hp)
  rw [P.eval_quartic] at h
  exact h

/-- Any admissible quartic with the values of an entry has the value of that entry. -/
theorem W_eq_pv {p : Fin 4 → ℝ} (hp : -T ^ 2 < Minkowski.dot p p) {i j : Fin 4}
    {Q : LoopQuartic} (hQ : P.D.Good Q) (he : Q.eval = fun ℓ => P.N p ℓ i j) :
    P.W p i j = P.D.pv Q (P.D.mom p) :=
  SEData.pv_unique (P.good_quartic p i j) hQ (by rw [P.eval_quartic, he]) (P.hV p hp)

/-- **Spinor covariance of the limit** between `p` and `L p`, both in the region. -/
theorem conj_W {L : Matrix (Fin 4) (Fin 4) ℝ} {S S' : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S S') {p : Fin 4 → ℝ} (hp : -T ^ 2 < Minkowski.dot p p)
    (hLp : -T ^ 2 < Minkowski.dot (L *ᵥ p) (L *ᵥ p)) :
    S * P.W (L *ᵥ p) * S' = P.W p := by
  classical
  ext i j
  set Q₂ := P.quartic (L *ᵥ p)
  set c : Fin 4 × Fin 4 → ℂ := fun kl => S i kl.1 * S' kl.2 j
  set Qs := qsum Finset.univ c (fun kl => lmap (blockL L) (Q₂ kl.1 kl.2))
  have hI : ∀ kl ∈ (Finset.univ : Finset (Fin 4 × Fin 4)),
      IntegrableOn (paramIntegrand (lmap (blockL L) (Q₂ kl.1 kl.2)) P.D.α (P.D.mom p) P.D.M 0)
        (simplexSet P.D.m) := fun kl _ => by
    have := SEData.integrableOn_pv (P.good_quartic (L *ᵥ p) kl.1 kl.2) (P.hV _ hLp)
    rw [P.D.mom_mulVec] at this
    exact this.congr_fun (fun x _ => paramIntegrand_map h _ _ _ _ _ x)
      (QED.Integration.Feynman.measurableSet_simplexSet _)
  have hev : Qs.eval = fun ℓ => P.N p ℓ i j := by
    funext ℓ
    rw [eval_qsum, ← P.hcov L S S' h p ℓ]
    simp only [eval_lmap_blockL, Q₂, P.eval_quartic, Matrix.mul_apply, Finset.sum_mul, c]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hgood : P.D.Good Qs := by
    refine ⟨?_, by rw [hev]; rw [← P.eval_quartic]; exact (P.good_quartic p i j).2⟩
    rcases Nat.lt_or_ge P.D.m 7 with h7 | h7
    · refine Or.inr (SEData.quart_qsum _ _ _ fun kl _ => SEData.quart_lmap _ _ ?_)
      rcases (P.good_quartic (L *ᵥ p) kl.1 kl.2).1 with h' | h'
      · omega
      · exact h'
    · exact Or.inl h7
  rw [P.W_eq_pv hp hgood hev, SEData.pv_qsum _ _ _ hI]
  simp only [W, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, c, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [P.D.mom_mulVec, SEData.pv_map h]
  ring

/-- **The limit is reflection covariant** on the region. -/
theorem secov : SECov T P.W := by
  intro a ha p hp
  have h := isSpinLift_reflect ha
  have hLp : -T ^ 2 < Minkowski.dot (QED.Dirac.reflectMatrix a *ᵥ p)
      (QED.Dirac.reflectMatrix a *ᵥ p) := by
    rw [QED.Dirac.reflectMatrix_mulVec, QED.Dirac.dot_reflect ha]
    exact hp
  have := P.conj_W h hp hLp
  rwa [QED.Dirac.reflectMatrix_mulVec] at this

end SEPiece

end QED.GradedProof.SE2

end
