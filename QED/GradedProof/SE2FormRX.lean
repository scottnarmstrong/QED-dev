/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2FormP
public import QED.GradedProof.SE2Chain4
public import QED.GradedProof.SE2LimRX
public import QED.TwoLoop.CountertermInsertionChain

/-!
# The class obligations of clause 2 for `R`, `X`

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2.

* `hasSEForm_gggg`: a two-loop self-energy contraction of four `gauge` vertices with seven-line
  cubic parametric data (as in `exists_tendsto_contractionValue₂_gggg`) whose numerator matrix
  `numG` is spinor covariant has the covariant form on the region where `V` is positive. The
  numerator does not read `ε`, so the value at `ε > 0` is the joint integral of the cubic
  numerator over the denominators, a self-energy piece (`SEPiece`).
* `amplitudeNumerator_repR`, `amplitudeNumerator_repX`: the numerators are the open chains
  `(ie)⁴ (1/i)³ chain4 w (E₃, E₂, E₁)` with the rainbow and crossed photon weights; they are
  covariant by `mul_chain4_mul`.
* `classForm_repR`, `classForm_repX`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix RefinedBound
  IntNoSubdivergenceRefined symanzikU symanzikV noSubdivergenceRefined_castLoopMatrix_iff)

/-! ### Generic facts for four `gauge` vertices -/

/-- The amplitude numerator of a contraction of `k_gggg` does not read the external momenta. -/
theorem amplitudeNumerator_gggg_pIn (P : Params) {nf nA : ℕ} (C : Contraction nf nA k_gggg)
    (φ : Flavoring k_gggg) (pIn pIn' : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    amplitudeNumerator P C φ pIn kIn k αOut βIn μ =
      amplitudeNumerator P C φ pIn' kIn k αOut βIn μ := by
  unfold amplitudeNumerator
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  rw [Finset.prod_congr rfl fun t _ => vertexFactor_gggg P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
    (psiMomentum₂ C pIn k) (psiMomentum₂ C pIn' k) (photonMomentum₂ C kIn k)
    (photonMomentum₂ C kIn k) t]

/-- The numerator matrix of a self-energy contraction of `k_gggg`. -/
noncomputable def numG (Q : Params) (C : Contraction 1 0 k_gggg) (p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => amplitudeNumerator Q C (zeroFlavoring k_gggg) ![p] ![]
    (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![]

theorem lineMomentum_smul_eq {m : ℕ} (a : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ)
    (j : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) (y : Fin 1 → Fin 4 → ℝ) :
    lineMomentum a (fun i => cs i • y 0) j ℓ =
      ∑ s, ![cs j] s • y s + lineMomentum a 0 j ℓ := by
  funext μ
  simp [QED.Integration.TwoLoop.lineMomentum]
  ring

theorem lineMomentum_loopAct_smul {m : ℕ} (L : Matrix (Fin 4) (Fin 4) ℝ)
    (a : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum a (fun i => cs i • (L *ᵥ p)) j (loopAct L ℓ) =
      L *ᵥ lineMomentum a (fun i => cs i • p) j ℓ := by
  funext μ
  simp only [QED.Integration.TwoLoop.lineMomentum, loopAct, Matrix.mulVec, dotProduct,
    Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Two-loop self-energy contractions of four `gauge` vertices with covariant numerators have
the covariant form.** -/
theorem hasSEForm_gggg (C : Contraction 1 0 k_gggg)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hL : loopCount C = 2)
    (hcard : Fintype.card (FermionLine C) = 3) (a : Fin 7 → Fin 2 → ℤ)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2} a) (Q : Params) (cs : Fin 7 → ℝ)
    (e : FermionLine C → Fin 7) (he : Function.Injective e)
    (hE : ∀ f, e f ∈ ({0, 1, 2} : Finset (Fin 7)))
    (hk : ∀ p ℓ f, lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f) =
      lineMomentum (castLoopMatrix a) (fun i => cs i • p) (e f) ℓ)
    (hden : ∀ (ε : ℝ) p ℓ, amplitudeDenominator { Q with ε := ε } C (zeroFlavoring k_gggg)
      (lineMomentum₂ C ![p] ![p] ![] ℓ) =
        ∏ i, (lineDenom (castLoopMatrix a) (fun i => cs i • p) (massesSE Q) ε i ℓ)⁻¹)
    {T : ℝ} (hT : 0 < T)
    (hV : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∃ c : ℝ, 0 < c ∧
      ∀ z : Fin 7 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU (castLoopMatrix a) z ≠ 0 →
        c ≤ symanzikV (castLoopMatrix a) (fun i => cs i • p) (massesSE Q) z)
    (hcov : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Matrix (Fin 4) (Fin 4) ℂ),
      IsSpinLift L S S' → ∀ p ℓ, S * numG Q C (L *ᵥ p) (loopAct L ℓ) * S' = numG Q C p ℓ) :
    HasSEForm T fun ε p α β =>
      contractionValue₂ { Q with ε := ε } C ![p] ![p] ![] ![α] ![β] ![] := by
  set κ : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ with hκ
  let D : SEData :=
    { m := 6
      α := castLoopMatrix a
      cs := cs
      M := massesSE Q
      E := {0, 1, 2}
      hm := le_refl _
      hcrit := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit }
  have haff : ∀ p (f : FermionLine C),
      IsLoopAffine fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f) := fun p f => by
    rw [show (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f)) =
      lineMomentum (castLoopMatrix a) (fun i => cs i • p) (e f) from funext fun ℓ => hk p ℓ f]
    exact isLoopAffine_lineMomentum _ _ _
  let P : SEPiece T :=
    { D := D
      N := fun p ℓ => κ • numG Q C p ℓ
      hQ := fun p i j => by
        have hpoly := isLoopPoly_amplitudeNumerator_gggg Q C (zeroFlavoring k_gggg) ![p] ![]
          (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ) (haff p) ![i] ![j] ![]
        rw [hcard] at hpoly
        obtain ⟨P', hq, hP⟩ := IsLoopPoly.exists_loopQuartic_cubic (hpoly.const_mul κ)
        refine ⟨P', ⟨Or.inr hq, ?_⟩, ?_⟩
        · rw [hP]
          have h := (refinedBound_amplitudeNumerator_gggg Q C (zeroFlavoring k_gggg) ![p] ![]
            (castLoopMatrix a) (fun i => cs i • p) (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ)
            e he (fun ℓ f => hk p ℓ f) ![i] ![j] ![]).const_mul κ
          rw [hcard] at h
          refine h.mono ?_ (by norm_num)
          intro x hx
          obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hx
          exact hE f
        · rw [hP]
          rfl
      hV := hV
      hcov := fun L S S' h p ℓ => by
        rw [Matrix.mul_smul, Matrix.smul_mul, hcov L S S' h p ℓ] }
  refine P.hasSEForm (by nlinarith) (d := 3) (fun ℓ i j => ?_) (h := fun _ => 1)
    tendsto_const_nhds fun p _ i j => ?_
  · show IsLoopPoly 1 3 fun y => κ * amplitudeNumerator Q C (zeroFlavoring k_gggg) ![y 0] ![]
      (lineMomentum₂ C ![y 0] ![y 0] ![] ℓ) ![i] ![j] ![]
    have hpoly := isLoopPoly_amplitudeNumerator_gggg Q C (zeroFlavoring k_gggg) ![0] ![]
      (fun y : Fin 1 → Fin 4 → ℝ => lineMomentum₂ C ![y 0] ![y 0] ![] ℓ) (fun f => by
        rw [show (fun y : Fin 1 → Fin 4 → ℝ => lineMomentum₂ C ![y 0] ![y 0] ![] ℓ (.inl f)) =
          fun y => lineMomentum (castLoopMatrix a) (fun i => cs i • y 0) (e f) ℓ from
            funext fun y => hk (y 0) ℓ f]
        exact ⟨![cs (e f)], lineMomentum (castLoopMatrix a) 0 (e f) ℓ,
          lineMomentum_smul_eq _ _ _ ℓ⟩) ![i] ![j] ![]
    rw [hcard] at hpoly
    refine (congrArg (IsLoopPoly 1 3) (funext fun y => ?_)).mp (hpoly.const_mul κ)
    rw [amplitudeNumerator_gggg_pIn Q C _ ![0] ![y 0]]
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    show contractionValue₂ { Q with ε := ε } C ![p] ![p] ![] ![i] ![j] ![] =
      1 * QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
        κ * amplitudeNumerator Q C (zeroFlavoring k_gggg) ![p] ![]
          (lineMomentum₂ C ![p] ![p] ![] ℓ) ![i] ![j] ![] *
        ∏ k, (lineDenom (castLoopMatrix a) (fun i => cs i • p) (massesSE Q) ε k ℓ)⁻¹)
    rw [one_mul]
    unfold contractionValue₂
    rw [hL]
    congr 1
    funext ℓ
    rw [regulatedAmplitude₂_eq_zeroFlavoring _ hcyc,
      contractionAmplitude₂_eq { Q with ε := ε } hε.ne', hden ε p ℓ, hκ, ← mul_assoc]
    rfl

/-! ### The open chain through four `gauge` vertices -/

theorem slots_gggg : ∀ s : Wick.PhotonSlot k_gggg, s.2.val = 0 := by decide +kernel

theorem slots_gggg_pos (t : Fin 4) : 0 < (k_gggg t).photonSlots := by
  fin_cases t <;> decide

/-- Sums over the photon slots of `k_gggg` are sums over functions on the vertices. -/
theorem sum_slots_gggg {M : Type*} [AddCommMonoid M] (g : (Wick.PhotonSlot k_gggg → Fin 4) → M) :
    ∑ lor, g lor = ∑ l : Fin 4 → Fin 4, g (fun s => l s.1) := by
  let e : (Fin 4 → Fin 4) ≃ (Wick.PhotonSlot k_gggg → Fin 4) :=
    { toFun := fun l s => l s.1
      invFun := fun lor t => lor ⟨t, ⟨0, slots_gggg_pos t⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun lor => funext fun s =>
        congrArg lor (Sigma.ext rfl (heq_of_eq (Fin.ext (slots_gggg s).symm))) }
  exact (e.sum_comp g).symm

theorem r_tails : rf1.tail = fvK k_gggg 0 ∧ rf2.tail = fvK k_gggg 1 ∧
    rf3.tail = fvK k_gggg 2 ∧ rg1.head = psK k_gggg 3 0 ∧ rg2.head = psK k_gggg 2 0 := by
  decide +kernel

theorem r_cond (a b : Wick.FermionVertex k_gggg → Fin 4) (lor : Wick.PhotonSlot k_gggg → Fin 4)
    (α β : Fin 4) (μ : Fin 0 → Fin 4) :
    ((∀ i t, repR.1.1 (.inl i) = .inr t → a t = ![α] i) ∧
        (∀ t i, repR.1.1 (.inr t) = .inl i → b t = ![β] i) ∧
        (∀ j s, repR.1.2 (.inl j) = .inr s → lor s = μ j)) ↔
      a (fvK k_gggg 3) = α ∧ b (fvK k_gggg 0) = β := by
  have h1 : ∀ t, repR.1.1 (.inl 0) = .inr t ↔ t = fvK k_gggg 3 := by decide +kernel
  have h2 : ∀ t, repR.1.1 (.inr t) = .inl 0 ↔ t = fvK k_gggg 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, forall_eq, IsEmpty.forall_iff, and_true,
    Matrix.cons_val_zero]

/-- **The numerator of the rainbow `R` as an open chain.** -/
theorem amplitudeNumerator_repR (P : Params) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 0 → Fin 4 → ℝ) (k : Line repR → Fin 4 → ℝ) (α β : Fin 4) (μ : Fin 0 → Fin 4) :
    amplitudeNumerator P repR (zeroFlavoring k_gggg) pIn kIn k ![α] ![β] μ =
      ((I * P.e) ^ 4 * (1 / I) ^ 3) * chain4 (wR P) (electronNumerator P.m (k (.inl rf3)))
        (electronNumerator P.m (k (.inl rf2))) (electronNumerator P.m (k (.inl rf1))) α β := by
  obtain ⟨t1, t2, t3, h1, h2⟩ := r_tails
  obtain ⟨n12, n13, n23, n45⟩ := r_fermion_ne
  unfold amplitudeNumerator
  rw [(Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm, sum_slots_gggg]
  simp only [chain4, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (I * P.e) ^ 4 * (1 / I) ^ 3 * (wR P l * chainG (fun t => Dirac.gamma (l t))
      (electronNumerator P.m (k (.inl rf3))) (electronNumerator P.m (k (.inl rf2)))
      (electronNumerator P.m (k (.inl rf1))) α β) =
      ((I * P.e) ^ 4 * (1 / I) ^ 3 * wR P l) * (Dirac.gamma (l 3) *
        electronNumerator P.m (k (.inl rf3)) * Dirac.gamma (l 2) *
        electronNumerator P.m (k (.inl rf2)) * Dirac.gamma (l 1) *
        electronNumerator P.m (k (.inl rf1)) * Dirac.gamma (l 0)) α β by
      rw [chainG]; ring,
    ← sum_spinor_chain4 (x₁ := fvK k_gggg 3) (x₂ := fvK k_gggg 2) (x₃ := fvK k_gggg 1)
      (x₄ := fvK k_gggg 0) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide +kernel)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [r_cond, Fin.prod_univ_four, prod_eq_of_three n12 n13 n23 r_fermionLine_cases,
    prod_eq_of_two n45 r_photonLine_cases,
    vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggg 0 = .gauge from rfl),
    vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggg 1 = .gauge from rfl),
    vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggg 2 = .gauge from rfl),
    vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggg 3 = .gauge from rfl),
    t1, t2, t3, h1, h2]
  simp only [show rf1.1 = fvK k_gggg 1 from rfl, show rf2.1 = fvK k_gggg 2 from rfl,
    show rf3.1 = fvK k_gggg 3 from rfl, show rg1.1 = psK k_gggg 0 0 from rfl,
    show rg2.1 = psK k_gggg 1 0 from rfl, psK, fvK, QED.TwoLoop.Insertion.zeroFlavoring,
    Params.mass,
    Matrix.cons_val_zero, wR, pvEta]
  ring


theorem x_tails : xf1.tail = fvK k_gggg 0 ∧ xf2.tail = fvK k_gggg 1 ∧
    xf3.tail = fvK k_gggg 2 ∧ xg1.head = psK k_gggg 2 0 ∧ xg2.head = psK k_gggg 3 0 := by
  decide +kernel

theorem x_cond (a b : Wick.FermionVertex k_gggg → Fin 4) (lor : Wick.PhotonSlot k_gggg → Fin 4)
    (α β : Fin 4) (μ : Fin 0 → Fin 4) :
    ((∀ i t, repX.1.1 (.inl i) = .inr t → a t = ![α] i) ∧
        (∀ t i, repX.1.1 (.inr t) = .inl i → b t = ![β] i) ∧
        (∀ j s, repX.1.2 (.inl j) = .inr s → lor s = μ j)) ↔
      a (fvK k_gggg 3) = α ∧ b (fvK k_gggg 0) = β := by
  have h1 : ∀ t, repX.1.1 (.inl 0) = .inr t ↔ t = fvK k_gggg 3 := by decide +kernel
  have h2 : ∀ t, repX.1.1 (.inr t) = .inl 0 ↔ t = fvK k_gggg 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, forall_eq, IsEmpty.forall_iff, and_true,
    Matrix.cons_val_zero]

/-- **The numerator of the crossed `X` as an open chain.** -/
theorem amplitudeNumerator_repX (P : Params) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 0 → Fin 4 → ℝ) (k : Line repX → Fin 4 → ℝ) (α β : Fin 4) (μ : Fin 0 → Fin 4) :
    amplitudeNumerator P repX (zeroFlavoring k_gggg) pIn kIn k ![α] ![β] μ =
      ((I * P.e) ^ 4 * (1 / I) ^ 3) * chain4 (wX P) (electronNumerator P.m (k (.inl xf3)))
        (electronNumerator P.m (k (.inl xf2))) (electronNumerator P.m (k (.inl xf1))) α β := by
  obtain ⟨t1, t2, t3, h1, h2⟩ := x_tails
  obtain ⟨n12, n13, n23, n45⟩ := x_fermion_ne
  unfold amplitudeNumerator
  rw [(Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm, sum_slots_gggg]
  simp only [chain4, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (I * P.e) ^ 4 * (1 / I) ^ 3 * (wX P l * chainG (fun t => Dirac.gamma (l t))
      (electronNumerator P.m (k (.inl xf3))) (electronNumerator P.m (k (.inl xf2)))
      (electronNumerator P.m (k (.inl xf1))) α β) =
      ((I * P.e) ^ 4 * (1 / I) ^ 3 * wX P l) * (Dirac.gamma (l 3) *
        electronNumerator P.m (k (.inl xf3)) * Dirac.gamma (l 2) *
        electronNumerator P.m (k (.inl xf2)) * Dirac.gamma (l 1) *
        electronNumerator P.m (k (.inl xf1)) * Dirac.gamma (l 0)) α β by
      rw [chainG]; ring,
    ← sum_spinor_chain4 (x₁ := fvK k_gggg 3) (x₂ := fvK k_gggg 2) (x₃ := fvK k_gggg 1)
      (x₄ := fvK k_gggg 0) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide +kernel)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [x_cond, Fin.prod_univ_four, prod_eq_of_three n12 n13 n23 x_fermionLine_cases,
    prod_eq_of_two n45 x_photonLine_cases,
    vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggg 0 = .gauge from rfl),
    vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggg 1 = .gauge from rfl),
    vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggg 2 = .gauge from rfl),
    vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggg 3 = .gauge from rfl),
    t1, t2, t3, h1, h2]
  simp only [show xf1.1 = fvK k_gggg 1 from rfl, show xf2.1 = fvK k_gggg 2 from rfl,
    show xf3.1 = fvK k_gggg 3 from rfl, show xg1.1 = psK k_gggg 0 0 from rfl,
    show xg2.1 = psK k_gggg 1 0 from rfl, psK, fvK, QED.TwoLoop.Insertion.zeroFlavoring,
    Params.mass,
    Matrix.cons_val_zero, wX, pvEta]
  ring


/-! ### The classes `R`, `X` -/

theorem numG_repR (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    numG Q repR p ℓ = ((I * Q.e) ^ 4 * (1 / I) ^ 3) •
      chain4 (wR Q) (electronNumerator Q.m (rMom p ℓ (.inl rf3)))
        (electronNumerator Q.m (rMom p ℓ (.inl rf2)))
        (electronNumerator Q.m (rMom p ℓ (.inl rf1))) := by
  ext α β
  simp only [numG, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [amplitudeNumerator_repR, lineMomentum₂_repR]

theorem numG_repX (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    numG Q repX p ℓ = ((I * Q.e) ^ 4 * (1 / I) ^ 3) •
      chain4 (wX Q) (electronNumerator Q.m (xMom p ℓ (.inl xf3)))
        (electronNumerator Q.m (xMom p ℓ (.inl xf2)))
        (electronNumerator Q.m (xMom p ℓ (.inl xf1))) := by
  ext α β
  simp only [numG, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [amplitudeNumerator_repX, lineMomentum₂_repX]

theorem rMom_loopAct (L : Matrix (Fin 4) (Fin 4) ℝ) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (f : Line repR) : rMom (L *ᵥ p) (loopAct L ℓ) f = L *ᵥ rMom p ℓ f := by
  rw [rMom, rMom, ppR_eq, ppR_eq, lineMomentum_loopAct_smul]

theorem xMom_loopAct (L : Matrix (Fin 4) (Fin 4) ℝ) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (f : Line repX) : xMom (L *ᵥ p) (loopAct L ℓ) f = L *ᵥ xMom p ℓ f := by
  rw [xMom, xMom, ppX_eq, ppX_eq, lineMomentum_loopAct_smul]

theorem cov_numG_repR (Q : Params) {L : Matrix (Fin 4) (Fin 4) ℝ}
    {S S' : Matrix (Fin 4) (Fin 4) ℂ} (h : IsSpinLift L S S') (p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : S * numG Q repR (L *ᵥ p) (loopAct L ℓ) * S' = numG Q repR p ℓ := by
  rw [numG_repR, numG_repR, Matrix.mul_smul, Matrix.smul_mul, mul_chain4_mul h (weightCov_wR h Q),
    rMom_loopAct, rMom_loopAct, rMom_loopAct, h.mul_electronNumerator_mul,
    h.mul_electronNumerator_mul, h.mul_electronNumerator_mul]

theorem cov_numG_repX (Q : Params) {L : Matrix (Fin 4) (Fin 4) ℝ}
    {S S' : Matrix (Fin 4) (Fin 4) ℂ} (h : IsSpinLift L S S') (p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : S * numG Q repX (L *ᵥ p) (loopAct L ℓ) * S' = numG Q repX p ℓ := by
  rw [numG_repX, numG_repX, Matrix.mul_smul, Matrix.smul_mul, mul_chain4_mul h (weightCov_wX h Q),
    xMom_loopAct, xMom_loopAct, xMom_loopAct, h.mul_electronNumerator_mul,
    h.mul_electronNumerator_mul, h.mul_electronNumerator_mul]

theorem classForm_repR : ClassForm repR := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  have hm := hQ.hm
  obtain ⟨i1, i2, i3, -, -⟩ := idxR_apply
  refine hasSEForm_gggg repR (sameCycle_of_pow (n := 5) (by decide +kernel)) loopCount_repR
    (by decide +kernel) aR intCrit_R Q aRc (fun f => idxR (.inl f)) ?_ ?_
    (fun p ℓ f => by rw [lineMomentum₂_repR, rMom, ppR_eq])
    (fun ε p ℓ => by rw [← ppR_eq]; exact r_denominator { Q with ε := ε } p ℓ)
    (by positivity) (fun p hp => ⟨min 1 (1 + Minkowski.dot p p / (Q.m + ν) ^ 2) *
      min (Q.m ^ 2) (ν ^ 2), min_one_mul_pos (by positivity)
      (lt_min (by positivity) (by positivity)) hp, fun z hz hz1 hU => by
        rw [← ppR_eq]; exact symanzikV_R_ge Q hm hν0 hν hp hz hz1 hU⟩)
    fun L S S' h p ℓ => cov_numG_repR Q h p ℓ
  · intro f g h
    rcases r_fermionLine_cases f with rfl | rfl | rfl <;>
      rcases r_fermionLine_cases g with rfl | rfl | rfl <;>
      simp_all
  · intro f
    rcases r_fermionLine_cases f with rfl | rfl | rfl <;> simp [i1, i2, i3]

theorem classForm_repX : ClassForm repX := by
  intro Q hQ m₀ ν _ hm₀ _ _ hν0 hν hν2
  have hm := hQ.hm
  have hν2' : ν ≤ 2 * Q.m := hν2.trans (by linarith)
  obtain ⟨i1, i2, i3, -, -⟩ := idxX_apply
  refine hasSEForm_gggg repX (sameCycle_of_pow (n := 5) (by decide +kernel)) loopCount_repX
    (by decide +kernel) aX intCrit_X Q aXc (fun f => idxX (.inl f)) ?_ ?_
    (fun p ℓ f => by rw [lineMomentum₂_repX, xMom, ppX_eq])
    (fun ε p ℓ => by rw [← ppX_eq]; exact x_denominator { Q with ε := ε } p ℓ)
    (by positivity) (fun p hp => ⟨min 1 (1 + Minkowski.dot p p / (Q.m + ν) ^ 2) *
      min (Q.m ^ 2) (ν ^ 2), min_one_mul_pos (by positivity)
      (lt_min (by positivity) (by positivity)) hp, fun z hz hz1 hU => by
        rw [← ppX_eq]; exact symanzikV_X_ge Q hm hν0 hν hν2' hp hz hz1 hU⟩)
    fun L S S' h p ℓ => cov_numG_repX Q h p ℓ
  · intro f g h
    rcases x_fermionLine_cases f with rfl | rfl | rfl <;>
      rcases x_fermionLine_cases g with rfl | rfl | rfl <;>
      simp_all
  · intro f
    rcases x_fermionLine_cases f with rfl | rfl | rfl <;> simp [i1, i2, i3]

end QED.GradedProof.SE2

end
