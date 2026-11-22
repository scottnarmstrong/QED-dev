/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBKKData
public import QED.ChainProof.SetCMainBKKLink
public import QED.ChainProof.SetCMainBPauli

/-!
# Set (c), the bubble classes: covariance and `♯`-law of the longitudinal dispersive limit

Helper level for the open link `QED.ChainProof.SetCMainB.MainBKKLinkP`. The limit
`QED.ChainProof.SetCMainB.kkLimB` of the longitudinal dispersive part is
`-2c · wKD 1 · ∑_f ∫₀¹ w_f(x) K_x dx`, `K_x` the pointwise `ε → 0⁺` limit. At each `x ∈ (0, 1)`
the scalar and `k²` reductions write `K_x` as a combination with real coefficients of parametric
values of the doubled unit (`QED.ChainProof.SetCMainB.isParamValue_kkLimX_kkT`), whose numerators
are covariant and `♯`-fixed; the `x`-integral keeps both properties.

* `PieceFix`, `PieceGood`: `♯`-fixed pieces, covariant `♯`-fixed pieces, and their closure;
* **`pieceGood_kkT`**: the pointwise limit of a term with a covariant `♯`-fixed numerator;
* `kkLimX_kNum_sq`, `kkLimX_kNum_sq_scalar`, `kkLimX_ext_three`, **`kkLimX_kkH_int`**,
  **`kkLimX_kkH_ext`**: the pointwise limits through the reductions;
* **`pieceGood_kkH`**: the pointwise limit `K_x` is covariant and `♯`-fixed;
* `kkLimB_eq`, `sharp_dispMat_fix`, `pieceGood_dispMat`: `kkLimB` as dispersion integrals;
* **`pieceCov_kkLimB`**, **`pieceSharp_kkLimB`**: covariance and `♯`-law of `kkLimB`;
* `MainBKKPauli` (open: the Pauli limit of `kkLimB`), **`mainBKKLinkP_of_pauli`**:
  `MainBKKLinkP P₀ i` from it.
-/

@[expose] public section

open Complex Matrix MeasureTheory Set Filter Topology
open QED.WickModel (Params)

namespace QED.ChainProof.SetCMainB

open QED.Dirac QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM QED.TwoLoop.Enumeration
open QED.TwoLoop.LimitCovariance QED.ChainProof.SetCPauli
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.Integration.TwoLoop (RefinedBound lineMomentum)
open QED.GradedProof.SE2Real (sharp sharp_add sharp_smul)
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### Covariant `♯`-fixed pieces -/

section Good

/-- **A `♯`-fixed piece** on the pairs `IsPairQ m`. -/
def PieceFix (m : ℝ) (G : Piece) : Prop :=
  ∀ p' p, IsPairQ m p' p → ∀ μ, sharp (G p' p μ) = G p' p μ

/-- A covariant `♯`-fixed piece. -/
def PieceGood (m : ℝ) (G : Piece) : Prop := PieceCov m G ∧ PieceFix m G

variable {m : ℝ} {G H : Piece}

theorem PieceGood.congr (h : PieceGood m G)
    (hGH : ∀ p' p, IsPairQ m p' p → G p' p = H p' p) : PieceGood m H := by
  refine ⟨fun L S T hL p' p hpq h0 h1 μ => ?_, fun p' p hpq μ => ?_⟩
  · rw [← hGH _ _ (isPairQ_map hL hpq h0 h1), ← hGH _ _ hpq]
    exact h.1 L S T hL p' p hpq h0 h1 μ
  · rw [← hGH _ _ hpq]
    exact h.2 p' p hpq μ

theorem PieceGood.add (hG : PieceGood m G) (hH : PieceGood m H) :
    PieceGood m fun p' p μ => G p' p μ + H p' p μ :=
  ⟨hG.1.add hH.1, fun p' p hpq μ => by rw [sharp_add, hG.2 p' p hpq μ, hH.2 p' p hpq μ]⟩

theorem PieceGood.smul {c : ℂ} (hc : starRingEnd ℂ c = c) (hG : PieceGood m G) :
    PieceGood m fun p' p μ => c • G p' p μ :=
  ⟨hG.1.smul c, fun p' p hpq μ => by rw [sharp_smul, hc, hG.2 p' p hpq μ]⟩

/-- A `♯`-fixed piece times a `♯`-odd constant is `♯`-odd. -/
theorem PieceFix.sharp_smul {c : ℂ} (hc : starRingEnd ℂ c = -c) (hG : PieceFix m G) :
    PieceSharp m fun p' p μ => c • G p' p μ := fun p' p hpq μ => by
  rw [QED.GradedProof.SE2Real.sharp_smul, hc, hG p' p hpq μ, neg_smul]

theorem kkLimX_eq_of_kkVal {w : ℝ → ℂ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    {H H₁ : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ} (_h : KKVal w H₁)
    (hH : ∀ ε : ℝ, 0 < ε → ∀ x ∈ Ioo (0 : ℝ) 1, ∀ ℓ, H₁ ε x ℓ = H ε x ℓ) :
    kkLimX H x = kkLimX H₁ x :=
  (KKVal.limX_congr hH hx).symm

end Good

/-! ### The terms -/

section Term

variable {i : Fin 12} {R : Params} {t : ℝ} {k : ℕ} {ι : Fin (k + 1) → Fin 10}
  {Sl : Finset (Fin 10)}

/-- **The pointwise limit of a term with a covariant, `♯`-fixed numerator** is a covariant,
`♯`-fixed piece. -/
theorem pieceGood_kkT (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (ht : R.m ≤ t) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hk : 7 ≤ k) (hok : KKOk i ι Sl)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hP : ∀ p p' μ a b, IsLoopPoly 2 4 fun ℓ => N p p' μ ℓ a b)
    (hB : ∀ p p' μ a b, RefinedBound (unitMMatrix (repBClass i) (repBSlot i)
      (![1, 1] : Fin 2 → ℝ)) Sl 4 fun ℓ => N p p' μ ℓ a b)
    (hN : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
      ∀ p p' μ ℓ, S * N (L *ᵥ p) (L *ᵥ p') μ (loopAct L ℓ) * T = vecAct L (fun ν => N p p' ν ℓ) μ)
    (hNs : ∀ p p' μ ℓ, sharp (N p p' μ ℓ) = N p p' μ ℓ) :
    PieceGood R.m fun p' p μ => Matrix.of fun a b =>
      kkLimX (kkT i R p p' t ι fun ℓ => N p p' μ ℓ a b) x := by
  refine ⟨fun L S T h p' p hpq h0 h1 μ => ?_, fun p' p hpq μ => ?_⟩
  · obtain ⟨hpL', hpL, -, -, hqL⟩ := isPairQ_map h hpq h0 h1
    obtain ⟨hp', hp, -, -, hq⟩ := hpq
    refine QED.TwoLoop.ReflCovariance.conj_eq_vecAct_of_paramValue
      (kkDataT hk hok hm hγ hγΛ p p' hp hp' hq.le ht hx) h
      (kkDataT hk hok hm hγ hγΛ (L *ᵥ p) (L *ᵥ p') hpL hpL' hqL.le ht hx).p ?_
      (N p p') (N (L *ᵥ p) (L *ᵥ p')) (hN L S T h p p') _ _
      (fun μ a b => isParamValue_kkLimX_kkT hk hok hm hγ hγΛ hp hp' hq.le ht hx (hP p p' μ a b)
        (hB p p' μ a b))
      (fun μ a b => QED.TwoLoop.ReflCovariance.IsParamValue.exists_integrableOn
        (isParamValue_kkLimX_kkT hk hok hm hγ hγΛ hpL hpL' hqL.le ht hx
          (hP (L *ᵥ p) (L *ᵥ p') μ a b) (hB (L *ᵥ p) (L *ᵥ p') μ a b))) μ
    funext q
    simp only [kkDataT, kkData, unitMMomenta_map, Matrix.mulVec_smul]
  · obtain ⟨hp', hp, -, -, hq⟩ := hpq
    have h := QED.GradedProof.V5Zero.Sharp.sharp_eq_smul_of_isParamValue_vertex
      (D := kkDataT hk hok hm hγ hγΛ p p' hp hp' hq.le ht hx) (N p p')
      (fun μ => Matrix.of fun a b => kkLimX (kkT i R p p' t ι fun ℓ => N p p' μ ℓ a b) x) 1
      (fun μ ℓ => by rw [one_smul]; exact hNs p p' μ ℓ)
      (fun μ a b => isParamValue_kkLimX_kkT hk hok hm hγ hγΛ hp hp' hq.le ht hx (hP p p' μ a b)
        (hB p p' μ a b)) μ
    rwa [one_smul] at h

end Term

/-! ### The numerators -/

section Num

variable {i : Fin 12} {R : Params} {t : ℝ} {k : ℕ} {ι : Fin (k + 1) → Fin 10} {x : ℝ}

/-- `k²` is invariant under a spinor-lifted `L`. -/
theorem elemSq_map {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S T) (c : Class5) (σ : Fin 8) (p p' : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    elemSq c σ (L *ᵥ p) (L *ᵥ p') (loopAct L ℓ) = elemSq c σ p p' ℓ := by
  unfold elemSq elemMom
  rw [QED.TwoLoop.ReflCovariance.pvMomentaE_map, QED.TwoLoop.ReflCovariance.lineMomentum_map,
    h.dot_mulVec]

theorem of_mul_scalar (A : Matrix (Fin 4) (Fin 4) ℂ) (z : ℂ) :
    (Matrix.of fun a b => A a b * z) = z • A := by
  ext a b
  simp [mul_comm]

variable (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (ht : R.m ≤ t)
  (hx : x ∈ Ioo (0 : ℝ) 1)
include hm hγ hγΛ ht hx

/-- **The pointwise limit of a term `kNum`** is a covariant, `♯`-fixed piece. -/
theorem pieceGood_kNi (X Y : KSlot) (K : Finset (Fin 4)) (hXY : Disjoint (kSlotS X) (kSlotS Y))
    (hd : kSlotD X + kSlotD Y + K.card ≤ 4) (hk : 7 ≤ k) (hok : KKOk i ι (kSet X Y K)) :
    PieceGood R.m fun p' p μ => Matrix.of fun a b =>
      kkLimX (kkT i R p p' t ι fun ℓ => kNi i R p p' X Y K μ ℓ a b) x :=
  pieceGood_kkT hm hγ hγΛ ht hx hk hok (fun p p' μ ℓ => kNi i R p p' X Y K μ ℓ)
    (fun _ _ μ a b => isLoopPolyMat_kNum _ _ _ _ _ _ _ _ _ μ hd a b)
    (fun _ _ μ a b => refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ μ hXY hd a b)
    (fun _ _ _ h p p' μ ℓ => kNum_map _ _ _ _ p p' _ _ _ μ h ℓ)
    (fun _ _ μ ℓ => sharp_kNum _ _ _ _ _ _ _ _ _ μ ℓ)

/-- **The pointwise limit of the term with `k²` in its numerator** (both lines `0`, `3` deleted)
is a covariant, `♯`-fixed piece. -/
theorem pieceGood_kNi_sq (hW : kWardD i = 4) :
    PieceGood R.m fun p' p μ => Matrix.of fun a b =>
      kkLimX (kkT i R p p' t (fun a : Fin 8 => (eIdx 0).succAbove ((2 : Fin 9).succAbove a))
        fun ℓ => kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b *
          elemSq (repBClass i) (repBSlot i) p p' ℓ) x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h03⟩ := kkOk_ext i hW
  refine pieceGood_kkT hm hγ hγΛ ht hx le_rfl h03 (fun p p' μ ℓ => Matrix.of fun a b =>
      kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b *
        elemSq (repBClass i) (repBSlot i) p p' ℓ)
    (fun p p' μ a b => (isLoopPolyMat_kNum_two _ _ _ _ _ _ μ a b).mul (isLoopPoly_elemSq _ _ p p'))
    (fun p p' μ a b => (refinedBoundMat_kNum_two _ _ _ _ _ _ μ a b).mul
      (refinedBound_elemSq _ _ p p') (by decide)) (fun L S T h p p' μ ℓ => ?_)
    (fun p p' μ ℓ => ?_)
  · simp only [of_mul_scalar]
    rw [elemSq_map h, Matrix.mul_smul, Matrix.smul_mul, kNum_map _ _ _ _ p p' _ _ _ μ h ℓ,
      vecAct_smul]
  · simp only [of_mul_scalar]
    rw [sharp_smul, elemSq, Complex.conj_ofReal, sharp_kNum]

end Num

/-! ### The pointwise limits through the reductions -/

section Values

variable {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t : ℝ} {w : ℝ → ℂ} {x : ℝ}
  (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
  (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
  (ht : R.m ≤ t) (hw : IntegrableOn w (Ioo 0 1)) (hx : x ∈ Ioo (0 : ℝ) 1)

section Gen

variable {F : (Fin 2 → Fin 4 → ℝ) → ℂ} {S : Finset (Fin 10)} (hP : IsLoopPoly 2 4 F)
  (hB : RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ)) S 4 F)
include hm hγ hγΛ hp hp' hq ht hw hx hP hB

/-- The pointwise limit of a term with `k²` and no scalar. -/
theorem kkLimX_kNum_sq (h₀ : KKOk i (fun a : Fin 10 => a) S)
    (h₉ : KKOk i (fun a : Fin 9 => (9 : Fin 10).succAbove a) S) :
    kkLimX (kkT i R p p' t (fun a : Fin 10 => a)
      fun ℓ => F ℓ * elemSq (repBClass i) (repBSlot i) p p' ℓ) x =
      kkLimX (kkT i R p p' t (fun a : Fin 9 => (9 : Fin 10).succAbove a) F) x -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (fun a : Fin 10 => a) F) x :=
  kkLimX_sq (fun a : Fin 10 => a) 9 rfl
    (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) h₉ hP hB)
    (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) h₀ hP hB) hx

/-- The pointwise limit of a term with `k²` and the scalar of the electron line `d`. -/
theorem kkLimX_kNum_sq_scalar (d : Fin 4) (h₀ : KKOk i (fun a : Fin 10 => a) S)
    (h₉ : KKOk i (fun a : Fin 9 => (9 : Fin 10).succAbove a) S)
    (hd : KKOk i (fun a : Fin 9 => (eIdx d).succAbove a) S)
    (hd₉ : KKOk i (fun a : Fin 8 => (eIdx d).succAbove ((8 : Fin 9).succAbove a)) S) :
    kkLimX (kkT i R p p' t (fun a : Fin 10 => a)
      fun ℓ => F ℓ * elemSq (repBClass i) (repBSlot i) p p' ℓ * kkA i R p p' (eIdx d) ℓ) x =
      kkLimX (kkT i R p p' t (fun a : Fin 8 => (eIdx d).succAbove ((8 : Fin 9).succAbove a)) F)
          x -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (fun a : Fin 9 => (eIdx d).succAbove a) F)
          x :=
  (kkLimX_scalar (fun a : Fin 10 => a) (eIdx d)
    (kkVal_sq (fun a : Fin 9 => (eIdx d).succAbove a) 8 (eIdx_succAbove_eight d)
      (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) hd₉ hP hB)
      (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) hd hP hB))
    (kkVal_kNum_sq hm hγ hγΛ hp hp' hq ht hw hP hB h₀ h₉) hx).trans
  (kkLimX_sq (fun a : Fin 9 => (eIdx d).succAbove a) 8 (eIdx_succAbove_eight d)
    (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) hd₉ hP hB)
    (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) hd hP hB) hx)

end Gen

include hm hγ hγΛ hp hp' hq ht hw hx

/-- The pointwise limit of the term with `k²` and the two scalars of the lines `3`, `0`. -/
theorem kkLimX_ext_three (hW : kWardD i = 4) (μ a b : Fin 4) :
    kkLimX (kkT i R p p' t (fun a : Fin 10 => a) fun ℓ =>
      kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b *
        elemSq (repBClass i) (repBSlot i) p p' ℓ * kkA i R p p' (eIdx 3) ℓ *
        kkA i R p p' (eIdx 0) ℓ) x =
      kkLimX (kkT i R p p' t (fun a : Fin 8 => (eIdx 0).succAbove ((2 : Fin 9).succAbove a))
        fun ℓ => kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b *
          elemSq (repBClass i) (repBSlot i) p p' ℓ) x := by
  obtain ⟨hall, -, -, -, -, hd0, hd09, hd3, hd39, h03⟩ := kkOk_ext i hW
  have hP : IsLoopPoly 2 4 fun ℓ =>
      kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b :=
    (isLoopPolyMat_kNum _ _ _ _ _ _ _ _ _ μ (by decide) a b)
  have hB : RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
      (kSetE 3) 4 fun ℓ => kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b :=
    refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ μ (by simp [kSlotS]) (by decide) a b
  have hP2 : IsLoopPoly 2 4 fun ℓ =>
      kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b *
        elemSq (repBClass i) (repBSlot i) p p' ℓ :=
    (isLoopPolyMat_kNum_two _ _ _ _ _ _ μ a b).mul (isLoopPoly_elemSq _ _ p p')
  have hB2 : RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
      (kSetE 3 ∪ {8, 9}) 4 fun ℓ =>
        kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b *
          elemSq (repBClass i) (repBSlot i) p p' ℓ :=
    (refinedBoundMat_kNum_two _ _ _ _ _ _ μ a b).mul (refinedBound_elemSq _ _ p p')
      (by decide)
  have h₁ := kkVal_kkT hm hγ hγΛ hp hp' hq ht hw le_rfl h03 hP2 hB2
  have h₂ := kkVal_sq (fun a : Fin 9 => (eIdx 0).succAbove a) 8 (eIdx_succAbove_eight 0)
    (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) hd09 hP hB)
    (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) hd0 hP hB)
  have hdel := kkVal_scalar (fun a : Fin 9 => (eIdx 0).succAbove a) 2 h₁ h₂
  have e2 := kkLimX_scalar (fun a : Fin 9 => (eIdx 0).succAbove a) 2 h₁ h₂ hx
  beta_reduce at hdel e2
  rw [eIdx_zero_succAbove_two] at hdel e2
  exact (kkLimX_scalar (fun a : Fin 10 => a) (eIdx 0) hdel
    (kkVal_kNum_sq_scalar hm hγ hγΛ hp hp' hq ht hw hP hB 3 (hall 3).1 (hall 3).2 hd3 hd39)
    hx).trans e2

/-- **The pointwise limit at an internal Ward vertex**, through the reductions. -/
theorem kkLimX_kkH_int (j : Fin 3) (hj : kWardD i = j.succ.castSucc) (μ a b : Fin 4) :
    kkLimX (kkH i R p p' t μ a b) x = kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ) *
      ((kkLimX (kkT i R p p' t
          (fun a : Fin 8 => (eIdx j.succ).succAbove ((8 : Fin 9).succAbove a))
          fun ℓ => kNi i R p p' .one .q (Finset.univ.erase j.succ) μ ℓ a b) x -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t
          (fun a : Fin 9 => (eIdx j.succ).succAbove a)
          fun ℓ => kNi i R p p' .one .q (Finset.univ.erase j.succ) μ ℓ a b) x) +
      -1 * (kkLimX (kkT i R p p' t
          (fun a : Fin 8 => (eIdx j.castSucc).succAbove ((8 : Fin 9).succAbove a))
          fun ℓ => kNi i R p p' .one .q (Finset.univ.erase j.castSucc) μ ℓ a b) x -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t
          (fun a : Fin 9 => (eIdx j.castSucc).succAbove a)
          fun ℓ => kNi i R p p' .one .q (Finset.univ.erase j.castSucc) μ ℓ a b) x)) := by
  have hT : ∀ d ∈ ({j.succ, j.castSucc} : Finset (Fin 4)), KKVal w
      (kkT i R p p' t (fun a : Fin 10 => a) fun ℓ =>
        kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b *
          elemSq (repBClass i) (repBSlot i) p p' ℓ * kkA i R p p' (eIdx d) ℓ) := fun d hd => by
    obtain ⟨h0, hdl, h9, hd9⟩ := kkOk_int i j hj d hd
    exact kkVal_kNum_sq_scalar hm hγ hγΛ hp hp' hq ht hw
      (isLoopPolyMat_kNum _ _ _ _ _ _ _ _ _ μ (kDeg_int d) a b)
      (refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ μ kSlot_one_q (kDeg_int d) a b) d h0 h9 hdl hd9
  have hV : ∀ d ∈ ({j.succ, j.castSucc} : Finset (Fin 4)),
      kkLimX (kkT i R p p' t (fun a : Fin 10 => a) fun ℓ =>
        kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b *
          elemSq (repBClass i) (repBSlot i) p p' ℓ * kkA i R p p' (eIdx d) ℓ) x =
      kkLimX (kkT i R p p' t (fun a : Fin 8 => (eIdx d).succAbove ((8 : Fin 9).succAbove a))
          fun ℓ => kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b) x -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (fun a : Fin 9 => (eIdx d).succAbove a)
          fun ℓ => kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b) x := fun d hd => by
    obtain ⟨h0, hdl, h9, hd9⟩ := kkOk_int i j hj d hd
    exact kkLimX_kNum_sq_scalar hm hγ hγΛ hp hp' hq ht hw hx
      (isLoopPolyMat_kNum _ _ _ _ _ _ _ _ _ μ (kDeg_int d) a b)
      (refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ μ kSlot_one_q (kDeg_int d) a b) d h0 h9 hdl hd9
  have h₁ := hT _ (mem_pair_left j)
  have h₂ := (hT _ (mem_pair_right j)).const_mul (-1)
  rw [KKVal.limX_congr (H₁ := fun ε x ℓ => kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ) *
      ((kkT i R p p' t (fun a : Fin 10 => a) fun ℓ =>
        kNi i R p p' .one .q (Finset.univ.erase j.succ) μ ℓ a b *
          elemSq (repBClass i) (repBSlot i) p p' ℓ * kkA i R p p' (eIdx j.succ) ℓ) ε x ℓ +
      -1 * (kkT i R p p' t (fun a : Fin 10 => a) fun ℓ =>
        kNi i R p p' .one .q (Finset.univ.erase j.castSucc) μ ℓ a b *
          elemSq (repBClass i) (repBSlot i) p p' ℓ * kkA i R p p' (eIdx j.castSucc) ℓ) ε x ℓ))
      (fun ε _ x _ ℓ => ?_) hx,
    KKVal.limX_const_mul _ (h₁.add h₂) hx, KKVal.limX_add h₁ h₂ hx,
    KKVal.limX_const_mul _ (hT _ (mem_pair_right j)) hx, hV _ (mem_pair_left j),
    hV _ (mem_pair_right j)]
  simp only [kkH]
  rw [dKUnit_int i 0 R p p' μ a b j hj ε ℓ]
  simp only [kkT, kkA_eIdx, kkDen_id]
  ring

/-- **The pointwise limit with the Ward identities at both ends**, through the reductions. -/
theorem kkLimX_kkH_ext (hW : kWardD i = 4) (μ a b : Fin 4) :
    kkLimX (kkH i R p p' t μ a b) x =
      kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ)) *
      ((((kkLimX (kkT i R p p' t (fun a : Fin 9 => (9 : Fin 10).succAbove a)
          fun ℓ => kNi i R p p' .out .inn Finset.univ μ ℓ a b) x -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (fun a : Fin 10 => a)
          fun ℓ => kNi i R p p' .out .inn Finset.univ μ ℓ a b) x) +
      (kkLimX (kkT i R p p' t (fun a : Fin 8 => (eIdx 0).succAbove ((8 : Fin 9).succAbove a))
          fun ℓ => kNi i R p p' .out .one (Finset.univ.erase 0) μ ℓ a b) x -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (fun a : Fin 9 => (eIdx 0).succAbove a)
          fun ℓ => kNi i R p p' .out .one (Finset.univ.erase 0) μ ℓ a b) x)) +
      -1 * (kkLimX (kkT i R p p' t
          (fun a : Fin 8 => (eIdx 3).succAbove ((8 : Fin 9).succAbove a))
          fun ℓ => kNi i R p p' .one .inn (Finset.univ.erase 3) μ ℓ a b) x -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (fun a : Fin 9 => (eIdx 3).succAbove a)
          fun ℓ => kNi i R p p' .one .inn (Finset.univ.erase 3) μ ℓ a b) x)) +
      -1 * kkLimX (kkT i R p p' t
          (fun a : Fin 8 => (eIdx 0).succAbove ((2 : Fin 9).succAbove a))
          fun ℓ => kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b *
            elemSq (repBClass i) (repBSlot i) p p' ℓ) x) := by
  obtain ⟨hall, h1d, h1d9, h2d, h2d9, -⟩ := kkOk_ext i hW
  have hP₀ := isLoopPolyMat_kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .out .inn
    Finset.univ μ (by decide) a b
  have hB₀ := refinedBoundMat_kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .out .inn
    Finset.univ μ (by simp [kSlotS]) (by decide) a b
  have hP₁ := isLoopPolyMat_kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .out .one
    (Finset.univ.erase 0) μ (by decide) a b
  have hB₁ := refinedBoundMat_kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .out .one
    (Finset.univ.erase 0) μ (by simp [kSlotS]) (by decide) a b
  have hP₂ := isLoopPolyMat_kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .one .inn
    (Finset.univ.erase 3) μ (by decide) a b
  have hB₂ := refinedBoundMat_kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .one .inn
    (Finset.univ.erase 3) μ (by simp [kSlotS]) (by decide) a b
  have h₀ := kkVal_kNum_sq hm hγ hγΛ hp hp' hq ht hw hP₀ hB₀ (hall 0).1 (hall 0).2
  have h₁ := kkVal_kNum_sq_scalar hm hγ hγΛ hp hp' hq ht hw hP₁ hB₁ 0 (hall 1).1 (hall 1).2
    h1d h1d9
  have h₂ := kkVal_kNum_sq_scalar hm hγ hγΛ hp hp' hq ht hw hP₂ hB₂ 3 (hall 2).1 (hall 2).2
    h2d h2d9
  have h₃ := kkVal_ext_three hm hγ hγΛ hp hp' hq ht hw hW μ a b
  have hK := (((h₀.add h₁).add (h₂.const_mul (-1))).add (h₃.const_mul (-1))).const_mul
    (kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ)))
  rw [kkLimX_eq_of_kkVal hx hK (fun ε _ x _ ℓ => ?_),
    KKVal.limX_const_mul _ (((h₀.add h₁).add (h₂.const_mul (-1))).add (h₃.const_mul (-1))) hx,
    KKVal.limX_add ((h₀.add h₁).add (h₂.const_mul (-1))) (h₃.const_mul (-1)) hx,
    KKVal.limX_add (h₀.add h₁) (h₂.const_mul (-1)) hx, KKVal.limX_add h₀ h₁ hx,
    KKVal.limX_const_mul _ h₂ hx, KKVal.limX_const_mul _ h₃ hx,
    kkLimX_kNum_sq hm hγ hγΛ hp hp' hq ht hw hx hP₀ hB₀ (hall 0).1 (hall 0).2,
    kkLimX_kNum_sq_scalar hm hγ hγΛ hp hp' hq ht hw hx hP₁ hB₁ 0 (hall 1).1 (hall 1).2 h1d h1d9,
    kkLimX_kNum_sq_scalar hm hγ hγΛ hp hp' hq ht hw hx hP₂ hB₂ 3 (hall 2).1 (hall 2).2 h2d h2d9,
    kkLimX_ext_three hm hγ hγΛ hp hp' hq ht hw hx hW μ a b]
  simp only [kkH]
  rw [dKUnit_ext i 0 R p p' μ a b hW ε ℓ]
  simp only [kkT, kkA_eIdx, kkDen_id]
  ring

end Values

/-! ### The pointwise limit is covariant and `♯`-fixed -/

section KKH

variable {i : Fin 12} {R : Params} {t : ℝ} {x : ℝ}

theorem conj_neg_sq (a : ℝ) : starRingEnd ℂ (-((a ^ 2 : ℝ) : ℂ)) = -((a ^ 2 : ℝ) : ℂ) := by
  rw [map_neg, Complex.conj_ofReal]

theorem conj_neg_one : starRingEnd ℂ (-1 : ℂ) = -1 := by simp

/-- **The pointwise limit of the longitudinal dispersive integrand is covariant and
`♯`-fixed**, at every `x ∈ (0, 1)` and spectral mass `t ≥ m`. -/
theorem pieceGood_kkH (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (ht : R.m ≤ t)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    PieceGood R.m fun p' p μ => Matrix.of fun a b => kkLimX (kkH i R p p' t μ a b) x := by
  have hΛ := conj_neg_sq R.Λ
  rcases kWardD_cases i with hW | ⟨j, hj⟩
  · obtain ⟨hall, h1d, h1d9, h2d, h2d9, -⟩ := kkOk_ext i hW
    have hc : starRingEnd ℂ (kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ))) =
        kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ)) := by
      rw [map_mul, map_mul, conj_kCst, Complex.conj_ofReal, Complex.conj_ofReal]
    have g₀ := (pieceGood_kNi hm hγ hγΛ ht hx .out .inn Finset.univ (by simp [kSlotS])
      (by decide) (by norm_num) (hall 0).2).add
      ((pieceGood_kNi hm hγ hγΛ ht hx .out .inn Finset.univ (by simp [kSlotS])
        (by decide) (by norm_num) (hall 0).1).smul hΛ)
    have g₁ := (pieceGood_kNi hm hγ hγΛ ht hx .out .one (Finset.univ.erase 0) (by simp [kSlotS])
      (by decide) (by norm_num) h1d9).add
      ((pieceGood_kNi hm hγ hγΛ ht hx .out .one (Finset.univ.erase 0) (by simp [kSlotS])
        (by decide) (by norm_num) h1d).smul hΛ)
    have g₂ := (pieceGood_kNi hm hγ hγΛ ht hx .one .inn (Finset.univ.erase 3) (by simp [kSlotS])
      (by decide) (by norm_num) h2d9).add
      ((pieceGood_kNi hm hγ hγΛ ht hx .one .inn (Finset.univ.erase 3) (by simp [kSlotS])
        (by decide) (by norm_num) h2d).smul hΛ)
    have g₃ := pieceGood_kNi_sq hm hγ hγΛ ht hx hW
    refine ((((g₀.add g₁).add (g₂.smul conj_neg_one)).add (g₃.smul conj_neg_one)).smul
      hc).congr fun p' p hpq => ?_
    obtain ⟨hp', hp, -, -, hq⟩ := hpq
    funext μ
    ext a b
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
    rw [kkLimX_kkH_ext hm hγ hγΛ hp hp' hq.le ht (integrableOn_dispWt R 0) hx hW μ a b]
    ring
  · have hc : starRingEnd ℂ (kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ)) =
        kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ) := by
      rw [map_mul, conj_kCst, Complex.conj_ofReal]
    have g : ∀ d ∈ ({j.succ, j.castSucc} : Finset (Fin 4)), PieceGood R.m fun p' p μ =>
        Matrix.of (fun a b => kkLimX (kkT i R p p' t
          (fun a : Fin 8 => (eIdx d).succAbove ((8 : Fin 9).succAbove a))
          fun ℓ => kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b) x) +
        -((R.Λ ^ 2 : ℝ) : ℂ) • Matrix.of (fun a b => kkLimX (kkT i R p p' t
          (fun a : Fin 9 => (eIdx d).succAbove a)
          fun ℓ => kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b) x) := fun d hd => by
      obtain ⟨-, hdl, -, hd9⟩ := kkOk_int i j hj d hd
      exact (pieceGood_kNi hm hγ hγΛ ht hx .one .q (Finset.univ.erase d) kSlot_one_q
        (kDeg_int d) (by norm_num) hd9).add ((pieceGood_kNi hm hγ hγΛ ht hx .one .q
          (Finset.univ.erase d) kSlot_one_q (kDeg_int d) (by norm_num) hdl).smul hΛ)
    refine (((g _ (mem_pair_left j)).add ((g _ (mem_pair_right j)).smul conj_neg_one)).smul
      hc).congr fun p' p hpq => ?_
    obtain ⟨hp', hp, -, -, hq⟩ := hpq
    funext μ
    ext a b
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
    rw [kkLimX_kkH_int hm hγ hγΛ hp hp' hq.le ht (integrableOn_dispWt R 0) hx j hj μ a b]
    ring

end KKH

/-! ### The `x`-integral -/

section Limit

theorem PieceGood.sum {m : ℝ} {ι : Type*} [Fintype ι] {F : ι → Piece}
    (hF : ∀ f, PieceGood m (F f)) : PieceGood m fun p' p μ => ∑ f, F f p' p μ :=
  ⟨PieceCov.sum fun f => (hF f).1, fun p' p hpq μ => by
    rw [QED.GradedProof.SE2Real.sharp_sum]
    exact Finset.sum_congr rfl fun f _ => (hF f).2 p' p hpq μ⟩

/-- **A dispersion integral of a `♯`-fixed family against a real weight is `♯`-fixed.** -/
theorem sharp_dispMat_fix {w : ℝ → ℂ} {F : ℝ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hw : ∀ x, starRingEnd ℂ (w x) = w x)
    (hF : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ μ, sharp (F x μ) = F x μ) (μ : Fin 4) :
    sharp (dispMat w F μ) = dispMat w F μ := by
  ext i j
  simp only [dispMat, QED.GradedProof.V5Zero.Sharp.sharp_apply, Matrix.of_apply]
  rw [← integral_conj, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have h := congrFun (congrFun (hF x hx μ) i) j
  rw [QED.GradedProof.V5Zero.Sharp.sharp_apply] at h
  simp only [map_mul, hw]
  rw [mul_left_comm, h]

/-- **A dispersion integral of covariant `♯`-fixed pieces** against a real weight, with
integrable entries, is a covariant `♯`-fixed piece. -/
theorem pieceGood_dispMat {m : ℝ} {w : ℝ → ℂ} (hw : ∀ x, starRingEnd ℂ (w x) = w x)
    {X : ℝ → Piece} (hX : ∀ x ∈ Ioo (0 : ℝ) 1, PieceGood m (X x))
    (hI : ∀ p' p, IsPairQ m p' p → ∀ μ a b,
      IntegrableOn (fun x => w x * X x p' p μ a b) (Ioo 0 1)) :
    PieceGood m fun p' p μ => dispMat w (fun x => X x p' p) μ :=
  ⟨fun L S T h p' p hpq h0 h1 μ => pieceCov_dispMat
      (fun x hx μ => (hX x hx).1 L S T h p' p hpq h0 h1 μ) (hI _ _ (isPairQ_map h hpq h0 h1))
      (hI _ _ hpq) μ,
    fun p' p hpq μ => sharp_dispMat_fix hw (fun x hx μ => (hX x hx).2 p' p hpq μ) μ⟩

/-- `kkLimB` as a combination of dispersion integrals. -/
theorem kkLimB_eq (R : Params) (i : Fin 12) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    kkLimB R i p' p μ = (-2 * vpCst R * wKD R 1) • ∑ f, dispMat (dispWt R f)
      (fun x μ => Matrix.of fun a b => kkLimX (kkH i R p p' (R.mass f) μ a b) x) μ := by
  ext a b
  simp only [kkLimB, dispMat, Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply, smul_eq_mul]

theorem conj_kkCst (R : Params) :
    starRingEnd ℂ (-2 * vpCst R * wKD R 1) = -(-2 * vpCst R * wKD R 1) := by
  rw [map_mul, map_mul, conj_wKD, vpCst, Complex.conj_ofReal, map_neg, map_ofNat]
  ring

variable {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
  (hMf : ∀ f, R.m ≤ R.mass f) (i : Fin 12)
include hm hγ hγΛ hMf

theorem pieceGood_kkSum : PieceGood R.m fun p' p μ => ∑ f, dispMat (dispWt R f)
    (fun x μ => Matrix.of fun a b => kkLimX (kkH i R p p' (R.mass f) μ a b) x) μ :=
  PieceGood.sum fun f => pieceGood_dispMat (conj_dispWt R f)
    (fun x hx => pieceGood_kkH hm hγ hγΛ (hMf f) hx) fun p' p hpq μ a b => by
      obtain ⟨hp', hp, -, -, hq⟩ := hpq
      exact (kkVal_dKUnit μ a b hm hγ hγΛ hp hp' hq.le (hMf f)
        (integrableOn_dispWt R f)).integrableOn_limX

omit hm hγ hγΛ hMf in
theorem kkLimB_fun : kkLimB R i = fun p' p μ => (-2 * vpCst R * wKD R 1) • ∑ f,
    dispMat (dispWt R f)
      (fun x μ => Matrix.of fun a b => kkLimX (kkH i R p p' (R.mass f) μ a b) x) μ :=
  funext fun p' => funext fun p => funext fun μ => kkLimB_eq R i p' p μ

/-- **Covariance of the limit of the longitudinal dispersive part.** -/
theorem pieceCov_kkLimB : PieceCov R.m (kkLimB R i) := by
  rw [kkLimB_fun i]
  exact (pieceGood_kkSum hm hγ hγΛ hMf i).1.smul _

/-- **The `♯`-law of the limit of the longitudinal dispersive part.** -/
theorem pieceSharp_kkLimB : PieceSharp R.m (kkLimB R i) := by
  rw [kkLimB_fun i]
  exact (pieceGood_kkSum hm hγ hγΛ hMf i).2.sharp_smul (conj_kkCst R)

end Limit

/-! ### The strengthened link from the Pauli limit -/

open QED.ChainProof.SetCLink QED.ChainProof.SetALink

/-- **The Pauli limit of the longitudinal dispersive part** of `repB i` at the set (c) data (open):
the even quotient of the Pauli numerator of `kkLimB` along the curve has a limit. -/
def MainBKKPauli (P₀ : Params) (i : Fin 12) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∃ Z : ℂ, PiecePauli P₀.m (kkLimB (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) i) Z

/-- **`MainBKKLinkP` from the Pauli limit of `kkLimB`**: the limit is `kkLimB`
(`tendsto_kkB`), covariant (`pieceCov_kkLimB`) and `♯`-odd (`pieceSharp_kkLimB`). -/
theorem mainBKKLinkP_of_pauli {P₀ : Params} {i : Fin 12} (hZ : MainBKKPauli P₀ i) :
    MainBKKLinkP P₀ i := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  obtain ⟨Z, hZ⟩ := hZ M₁ M₂ c₁ c₂ mγ Λ D s hA
  refine ⟨kkLimB (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) i, Z, fun p' p hpq μ α β => ?_,
    pieceCov_kkLimB (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ (setCAdm_mass hA) i,
    pieceSharp_kkLimB (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ (setCAdm_mass hA) i, hZ⟩
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  exact tendsto_kkB (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl hm hγ
    hγΛ (setCAdm_mass hA) hp hp' hq.le i μ α β

end QED.ChainProof.SetCMainB

end
