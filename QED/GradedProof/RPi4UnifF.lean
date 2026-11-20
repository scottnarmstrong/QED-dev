/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Unif
public import QED.GradedProof.RPi4FVBlock
public import QED.GradedProof.RPi4FLin
public import QED.GradedProof.RPi4CtBound

/-!
# (R-Π₄) step L7: the mass insertions, uniformly in `s`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), steps U (uniformity in `s`)
and L7 (light photon pair). The mass insertions enter the class sum `qPair` as
`fLim (ctPair(a, b))`, linear in the weight, with `|ctPair(a, b)| = O(√b)`. What was missing is a
bound on `fLim` at a unit weight that is uniform for `s` in a compact below threshold. By
`QED.GradedProof.RPi4.qPair_eq_tilt` it is read at the tilted vectors `k'(s)`, which fill a
segment (`QED.GradedProof.RPi4.exists_tiltVec_eq_lineK`), and `fLim = fbVal` there
(`QED.GradedProof.RPi4.fLim_eq_fbVal`) is a finite sum of eight-line parametric values.

* `SegBdd k₀ w G`: `G` is bounded on the segment `|u| ≤ 1/2`; closed under sums and constants.
* `segBdd_kinds`: eight-line kinds (`QED.GradedProof.SE2.kindsData`) along a segment with
  `k² ≥ S₀ > -(m_e + μ)²`; from `exists_norm_pvOf_line_le`, the quartics of
  `refinedBound_of_dependsOnZero` and the uniform positivity `symanzikV_kinds_se_ge`.
* `segBdd_fVal5`, `segBdd_eVal0/2/4`, `segBdd_insVal`, `segBdd_fbVal`: the one-loop pieces of
  `QED.GradedProof.RPi4.fbVal`, in the order of their construction.
* `exists_norm_fLim_tilt_le`: `‖fLim δ (k'(s))‖ ≤ C` for `s ∈ [S₀, S]`, `S₀ > -4m₀²`.
* `exists_norm_fLim_ctPair_tilt_le` (**L7, mass part**): the mass term of `qPair` at the
  photon pair `(a, b)`, `0 < a ≤ b`, is at most `C √b` at `k'(s)`, uniformly for `s ∈ [S₀, S]`.
-/

@[expose] public section
open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.CountertermLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.PauliZeroLimit (paramNum)
open QED.Graded (Counterterms)

/-! ### Bounded along the segment -/

/-- `G` is bounded on the points `|u| ≤ 1/2` of the segment `lineK k₀ w`. -/
def SegBdd (k₀ w : Fin 4 → ℝ) (G : (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, |u| ≤ 1 / 2 → ‖G (lineK k₀ w u)‖ ≤ C

namespace SegBdd

variable {k₀ w : Fin 4 → ℝ} {G H : (Fin 4 → ℝ) → ℂ}

theorem add (hG : SegBdd k₀ w G) (hH : SegBdd k₀ w H) : SegBdd k₀ w fun k => G k + H k := by
  obtain ⟨C, hC⟩ := hG
  obtain ⟨D, hD⟩ := hH
  exact ⟨C + D, fun u hu => (norm_add_le _ _).trans (add_le_add (hC u hu) (hD u hu))⟩

theorem const_mul (hG : SegBdd k₀ w G) (a : ℂ) : SegBdd k₀ w fun k => a * G k := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨‖a‖ * C, fun u hu => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC u hu) (norm_nonneg _)

theorem sum {ι : Type*} (s : Finset ι) {G : ι → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, SegBdd k₀ w (G i)) : SegBdd k₀ w fun k => ∑ i ∈ s, G i k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun u _ => by simp⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : SegBdd k₀ w G)
    (e : ∀ u : ℝ, |u| ≤ 1 / 2 → G (lineK k₀ w u) = H (lineK k₀ w u)) :
    SegBdd k₀ w H := by
  obtain ⟨C, hC⟩ := hG
  exact ⟨C, fun u hu => e u hu ▸ hC u hu⟩

end SegBdd

/-! ### Eight-line kinds along the segment -/

/-- **The parametric value of eight-line kinds is bounded along a segment below threshold.** -/
theorem segBdd_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind) (hκ : ∀ i, κ i ≠ .out)
    (Ms : Fin (m + 1) → ℝ) {me μ : ℝ} (hme : 0 < me) (hμ : 0 < μ)
    (hMe : ∀ i, κ i ≠ .pho → me ^ 2 ≤ Ms i ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j)
    {k₀ w : Fin 4 → ℝ} {S₀ : ℝ} (hS₀ : -(me + μ) ^ 2 < S₀)
    (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
    (i j : Fin 4) :
    SegBdd k₀ w fun k => pvOf (fun ℓ => N k (ℓ 0) i j) (castLoopMatrix fun i => (κ i).dir)
      (fun l => (κ l).mom k k) Ms := by
  set D := kindsData hm7 κ Ms hcrit
  have hmom := kindsData_mom hm7 κ hκ Ms hcrit
  have hα : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))),
      (castLoopMatrix fun i => (κ i).dir) e = ![1, 0] := by
    intro e he
    have h := hE e he
    funext s
    rcases hk : κ e with _ | _ | _ | _
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · exact absurd hk h
  have hT : 0 < (me + μ) ^ 2 := by positivity
  have hc1 : 0 < 1 + S₀ / (me + μ) ^ 2 := by
    have : -1 < S₀ / (me + μ) ^ 2 := by rw [lt_div_iff₀ hT]; linarith
    linarith
  have hc : 0 < min 1 (1 + S₀ / (me + μ) ^ 2) * min (me ^ 2) (μ ^ 2) :=
    mul_pos (lt_min one_pos hc1) (lt_min (by positivity) (by positivity))
  have hm0 : 0 < D.m := by have := D.hm; omega
  have hspan : ∃ a b, D.α a 0 * D.α b 1 - D.α a 1 * D.α b 0 ≠ 0 :=
    NoSubdivergence.span (α := D.α) fun k => by
      have := D.hcrit.noSubdivergenceOfOrder k; have := D.hm; omega
  have hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = (fun ℓ => N k (ℓ 0) i j) ∧
      ∀ q, IntegrableOn (paramNum Q D.α q D.M) (simplexSet D.m) := fun k => by
    obtain ⟨Q, hQ⟩ := (hN k i j).exists_loopQuartic
    have hgood : D.Good Q := ⟨Or.inl hm7, refinedBound_of_dependsOnZero _ hcard hα Q fun ℓ => by
      simp only [hQ, Matrix.cons_val_zero]⟩
    exact ⟨Q, hQ, fun q => integrableOn_paramNum_good hgood q⟩
  have hV : ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ᵐ x ∂(volume.restrict (simplexSet D.m)),
      min 1 (1 + S₀ / (me + μ) ^ 2) * min (me ^ 2) (μ ^ 2) ≤
        symanzikV D.α (fun i => D.cs i • lineK k₀ w u) D.M (simplexPoint x) := by
    intro u hu
    have hs := hseg u hu
    filter_upwards [ae_posDef D.α hm0 hspan] with x ⟨hxS, hPD⟩
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    have hb := symanzikV_kinds_se_ge κ hκ Ms hme hμ (p := lineK k₀ w u) (by linarith) hMe hMp
      hz.1 hz.2 hPD.det_pos.ne'
    rw [show (fun i => D.cs i • lineK k₀ w u) = D.mom (lineK k₀ w u) from rfl, hmom]
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_min_left _ ?_) (by positivity)) hb
    have := div_le_div_of_nonneg_right hs hT.le
    linarith
  obtain ⟨C, hC⟩ := exists_norm_pvOf_line_le (by have := D.hm; omega) D.α D.cs D.M k₀ w
    (fun k ℓ => N k (ℓ 0) i j) (fun ℓ => hpoly (ℓ 0) i j) hQ hc hV
  refine ⟨C, fun u hu => ?_⟩
  have h := hC u hu
  rwa [show (fun i => D.cs i • lineK k₀ w u) = D.mom (lineK k₀ w u) from rfl, hmom] at h

/-! ### The one-loop pieces along the segment -/

section Pieces

variable {m₀ : ℝ} (hm₀ : 0 < m₀) {k₀ w : Fin 4 → ℝ} {S₀ : ℝ} (hS₀ : -(4 * m₀ ^ 2) < S₀)
  (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
include hm₀ hS₀ hseg

theorem segBdd_fVal5 (Ms : Fin 5 → ℝ) (hMs : ∀ l, m₀ ≤ Ms l) (b : Fin 5 → Bool)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) (i j : Fin 4) :
    SegBdd k₀ w fun k => fVal5 m₀ Ms b N k i j := by
  have hsq : ∀ l, m₀ ^ 2 ≤ Ms l ^ 2 := fun l => pow_le_pow_left₀ hm₀.le (hMs l) 2
  have hM : ∀ i, m₀ ^ 2 ≤ (![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] : Fin 8 → ℝ) i ^ 2 := by
    intro i
    fin_cases i
    exacts [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4, le_rfl, le_rfl, le_rfl]
  have hout : ∀ c : Bool, kd c ≠ .out := fun c => by cases c <;> decide
  have h := segBdd_kinds (by norm_num) (kinds5 b) (fun i => by
      fin_cases i <;> simp [kinds5, hout])
    ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] hm₀ hm₀ (fun i _ => hM i) (fun i _ => hM i)
    (crit_kinds5 _) (by decide) (ne_aux_kinds5 _) N hN hpoly
    (by nlinarith : -(m₀ + m₀) ^ 2 < S₀) hseg i j
  exact (h.const_mul (auxLimit m₀)⁻¹).congr fun u _ => rfl

variable (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)

theorem segBdd_eVal0 (m0 m1 m2 m3 m4 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4)
    (c0 c1 c2 c3 c4 : Bool) (i j : Fin 4) :
    SegBdd k₀ w fun k => eVal0 m₀ sw d₂ dm bx bY m0 m1 m2 m3 m4 c0 c1 c2 c3 c4 k i j := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hm
  exact segBdd_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _
    (isLoopPoly_tnS0 sw d₂ dm bx bY) (isLoopPoly_tnS_k sw 0 d₂ dm bx bY) i j

theorem segBdd_eVal2 (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) (i j : Fin 4) :
    SegBdd k₀ w fun k => eVal2 m₀ sw d₂ dm bx bY m0 m1 m2 m3 c0 c1 c2 c3 k i j := by
  obtain ⟨h0, h1, h2, h3⟩ := hm
  have hN' : ∀ p i j, IsLoopPoly 2 4 fun ℓ => padN (tnS sw 1 d₂ dm bx bY) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((isLoopPoly_tnS1 sw d₂ dm bx bY p i j).mul
      ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono (by norm_num)
  have hpoly' := fun q i j => (isLoopPoly_tnS_k sw 1 d₂ dm bx bY q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  exact segBdd_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _ hN' hpoly' i j

theorem segBdd_eVal4 (m0 m1 m2 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2) (c0 c1 c2 : Bool)
    (i j : Fin 4) :
    SegBdd k₀ w fun k => eVal4 m₀ sw d₂ dm bx bY m0 m1 m2 c0 c1 c2 k i j := by
  obtain ⟨h0, h1, h2⟩ := hm
  have hN' : ∀ p i j, IsLoopPoly 2 2 fun ℓ => padN (tnS sw 2 d₂ dm bx bY) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((isLoopPoly_tnS2 sw d₂ dm bx bY p i j).mul
      ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono (by norm_num)
  have hN'' : ∀ p i j, IsLoopPoly 2 4 fun ℓ =>
      padN (padN (tnS sw 2 d₂ dm bx bY) m0 c0) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((hN' p i j).mul ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono
      (by norm_num)
  have hpoly' := fun q i j => (isLoopPoly_tnS_k sw 2 d₂ dm bx bY q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  have hpoly'' := fun q i j => (hpoly' q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  exact segBdd_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _ hN'' hpoly'' i j

theorem segBdd_insVal (M X Y : ℝ) (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (i j : Fin 4) :
    SegBdd k₀ w fun k => insVal m₀ sw d₂ dm bx bY M X Y k i j := by
  have E0 := fun m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 =>
    segBdd_eVal0 hm₀ hS₀ hseg sw d₂ dm bx bY m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 i j
  have E2 := fun m0 m1 m2 m3 hm c0 c1 c2 c3 =>
    segBdd_eVal2 hm₀ hS₀ hseg sw d₂ dm bx bY m0 m1 m2 m3 hm c0 c1 c2 c3 i j
  have E4 := segBdd_eVal4 hm₀ hS₀ hseg sw d₂ dm bx bY M X Y ⟨hM, hX, hY⟩ bx bx bx i j
  exact (((((((((((E0 M M X Y M ⟨hM, hM, hX, hY, hM⟩ bx bY bY bY bY).add
    (E0 M M X Y X ⟨hM, hM, hX, hY, hX⟩ bx bY bY bY bY)).add
    (E0 M M X Y Y ⟨hM, hM, hX, hY, hY⟩ bx bY bY bY bY)).add
    (E0 M X X Y X ⟨hM, hX, hX, hY, hX⟩ bx bx bY bY bY)).add
    (E0 M X X Y Y ⟨hM, hX, hX, hY, hY⟩ bx bx bY bY bY)).add
    (E0 M X Y Y Y ⟨hM, hX, hY, hY, hY⟩ bx bx bx bY bY)).add
    (E2 M M X Y ⟨hM, hM, hX, hY⟩ bx bY bY bY)).add
    (E2 M X X Y ⟨hM, hX, hX, hY⟩ bx bx bY bY)).add
    (E2 M X Y Y ⟨hM, hX, hY, hY⟩ bx bx bx bY)).add E4).const_mul _).congr fun u _ => rfl

end Pieces

/-! ### The limit of the weighted block at the tilted vectors -/

section Block

variable (P : QED.WickModel.Params) {F : Type} [Fintype F] [DecidableEq F]
  (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

omit [DecidableEq F] in
theorem segBdd_fbVal (D : Counterterms F) {k₀ w : Fin 4 → ℝ} {S₀ : ℝ}
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hS₀ : -(4 * m₀ ^ 2) < S₀)
    (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
    (sw bx bY : Bool) (i j : Fin 4) :
    SegBdd k₀ w fun k => fbVal P Φ D rep m₀ sw bx bY k i j := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hlt : ∀ g, Φ.mass g < auxX Φ := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    simp only [auxX]
    linarith
  exact (SegBdd.sum Finset.univ fun f _ => (segBdd_insVal hm₀ hS₀ hseg sw _ _ bx bY
    (Φ.mass f) (auxX Φ) (auxX Φ + 1) (hmass f) (by linarith [hlt f, hmass f])
    (by linarith [hlt f, hmass f]) i j).const_mul ((Φ.coeff f : ℂ) * kF P.e)).congr
    fun u _ => rfl

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The limit of the weighted block is bounded at the tilted vectors of a compact interval
below threshold.** -/
theorem exists_norm_fLim_tilt_le (he : P.e ≠ 0) (δ : F → ℝ) {c S₀ S : ℝ}
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀S : S₀ ≤ S) (hS : S < 2 * c ^ 2) (i j : Fin 4) :
    ∃ C : ℝ, ∀ s : ℝ, S₀ ≤ s → s ≤ S → ‖fLim Φ rep P.e δ (tiltVec c s) i j‖ ≤ C := by
  have hseg := fun u (hu : |u| ≤ 1 / 2) => (dot_lineK_tilt_mem (c := c) hS hS₀S hu).1
  obtain ⟨C, hC⟩ := ((segBdd_fbVal P Φ rep _ hm₀ hmass hS₀ hseg true true false i j).add
    (segBdd_fbVal P Φ rep _ hm₀ hmass hS₀ hseg false false true i j)).congr
    (H := fun k => fLim Φ rep P.e δ k i j) fun u hu =>
      (fLim_eq_fbVal P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he δ (by linarith [hseg u hu]) i j).symm
  refine ⟨C, fun s h₀ h₁ => ?_⟩
  obtain ⟨u, hu, he'⟩ := exists_tiltVec_eq_lineK (c := c) h₀ h₁
  rw [he']
  exact hC u hu

/-- **The mass part of the light pair (L7)**: the mass-insertion term of `qPair` at the photon
pair `(a, b)` is `O(√b)` at the tilted vectors, uniformly for `s ∈ [S₀, S]`. -/
theorem exists_norm_fLim_ctPair_tilt_le (he : P.e ≠ 0) {c S₀ S : ℝ}
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀S : S₀ ≤ S) (hS : S < 2 * c ^ 2) (i j : Fin 4) :
    ∃ C : ℝ, ∀ a b s : ℝ, 0 < a → a ≤ b → S₀ ≤ s → s ≤ S →
      ‖fLim Φ rep P.e (fun g => ctPair P.e (Φ.mass g) a b) (tiltVec c s) i j‖ ≤
        C * Real.sqrt b := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  choose C hC using fun g => exists_norm_fLim_tilt_le P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he
    (Pi.single g 1) hS₀ hS₀S hS i j
  refine ⟨∑ g, 3 * P.e ^ 2 / Real.pi ^ 2 / Real.sqrt (Φ.mass g) * max (C g) 0,
    fun a b s ha hab h₀ h₁ => ?_⟩
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot (tiltVec c s) (tiltVec c s) := by
    rw [dot_tiltVec (by linarith)]
    linarith
  rw [fLim_eq_sum_single Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he _ hk, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hct := abs_ctPair_le P.e (hpos g) ha hab
  rw [Real.sqrt_div' b (hpos g).le] at hct
  have hsg := Real.sqrt_pos.mpr (hpos g)
  have hb := Real.sqrt_nonneg b
  calc |ctPair P.e (Φ.mass g) a b| * ‖fLim Φ rep P.e (Pi.single g 1) (tiltVec c s) i j‖
      ≤ (3 * P.e ^ 2 * (Real.sqrt b / Real.sqrt (Φ.mass g)) / Real.pi ^ 2) * max (C g) 0 :=
        mul_le_mul hct ((hC g s h₀ h₁).trans (le_max_left _ _)) (norm_nonneg _)
          (by positivity)
    _ = 3 * P.e ^ 2 / Real.pi ^ 2 / Real.sqrt (Φ.mass g) * max (C g) 0 * Real.sqrt b := by
        field_simp

end Block

end QED.GradedProof.RPi4

end
