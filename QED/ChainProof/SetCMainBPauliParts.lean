/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBPauliPiece
public import QED.ChainProof.SetCMainBSplitLim
public import QED.ChainProof.SetCMainDPauli
public import QED.ChainProof.SetCPauliMainDK
public import QED.ChainProof.SetCUnitMDispLim

/-!
# Set (c), the bubble classes: covariance, `♯`-law and Pauli limits of the explicit parts

Helper level for the per-class links `SetCClassCov`, `SetCClassPauli`, `SetCClassSharp` of the
twelve bubble classes `repB i`. The limit of `repB i` is (`setCClassLim_inl_of`)
`-(c L₀/3 · (dG + dK) + disp + kk)`; here the first three parts are pieces
(`QED.ChainProof.SetCMainB.Piece`) with the three properties.

* `pieceG`: the transverse part `dGLimD R 1 i` of `repD i 0` at `δ₃ = 1`, from `dGLimD_map`,
  `sharp_dGLimD`, `tendsto_evenQuot_dG`;
* `dKLimB`, `pieceK`: the longitudinal part `wKD R 1 · lim J(dKUnitIntegrandD)` at `δ₃ = 1`;
  from the Ward reductions `hasLimJ_dKUnit_int`, `hasLimJ_dKUnit_ext`, a combination of
  parametric values (`kTerm_conj`, `sharp_of_paramValue_kNum`, `tendsto_evenQuot_dkTerm`), with
  the explicit Pauli values `kZInt`, `kZExt`;
* `pieceD`: the transverse dispersive part `-2c wD 1 ∑_f ∫₀¹ w_f L(x) dx`, from the
  dispersion integrals of `QED/ChainProof/SetCMainBPauliPiece.lean` (`unitMLimitV_map`,
  `sharp_unitMDispRepB`) and the `q → 0` limit `tendsto_pauliNum_div_unitMDispRepB`;
* `conj_logW_zero`: the log constant `c L₀ / 3` is real.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCMainB

open QED.Dirac QED.TwoLoop.Enumeration QED.ChainProof.SetCUnitM QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ClassIntegrable (openClasses)
open QED.ChainProof.SetCMain QED.ChainProof.SetCPauli
open QED.ChainProof.SetCPauli.CB01 (HasLimJ)
open QED.ChainProof.SetCUnit (MassesGe)
open QED.GradedProof.SE2Real (sharp sharp_sub sharp_add)

/-! ### The constants -/

theorem conj_logW_zero (R : Params) : starRingEnd ℂ (logW R 0) = logW R 0 := by
  have h : ∀ f, log (((R.mass f ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) =
      ((Real.log (R.mass f ^ 2) : ℝ) : ℂ) := fun f => by
    rw [ofReal_zero, zero_mul, sub_zero, Complex.ofReal_log (sq_nonneg _)]
  simp only [logW, bubLogSum, vpCst, h, map_div₀, map_mul, map_sum, Complex.conj_ofReal,
    map_ofNat]

theorem conj_dispCst (R : Params) :
    starRingEnd ℂ (-2 * vpCst R * wD R 1) = -2 * vpCst R * wD R 1 := by
  rw [map_mul, map_mul, conj_wD, vpCst, Complex.conj_ofReal, map_neg, map_ofNat]

theorem conj_dispWt (R : Params) (f : Fin 3) (x : ℝ) :
    starRingEnd ℂ (dispWt R f x) = dispWt R f x := by
  simp only [dispWt, map_mul, Complex.conj_ofReal]

section Pieces

variable {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (i : Fin 12)
include hm hγ hγΛ

/-! ### The transverse part -/

/-- The transverse part of `repD i 0` at `δ₃ = 1`. -/
noncomputable abbrev pieceG (R : Params) (i : Fin 12) : Piece := fun p' p => dGLimD R 1 i p p'

theorem pieceCov_G : PieceCov R.m (pieceG R i) := by
  intro L S T h p' p hpq _ _ μ
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  exact dGLimD_map hm hγ hγΛ hp hp' hq.le h 1 i μ

theorem pieceSharp_G : PieceSharp R.m (pieceG R i) := by
  intro p' p hpq μ
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  exact sharp_dGLimD hm hγ hγΛ hp hp' hq.le 1 i μ

theorem piecePauli_G : PiecePauli R.m (pieceG R i)
    (wD R 1 * unitMPauliZeroPow (repBClass i) R (repBSlot i) ![1, 1] (dkMasses R) 1) :=
  tendsto_evenQuot_dG R hm hγ hγΛ 1 i

end Pieces

/-! ### The longitudinal part -/

/-- The `ε → 0⁺` limit of the joint integral of the longitudinal unit integrand of `repD i 0`. -/
noncomputable def dKLimB (R : Params) (i : Fin 12) : Piece := fun p' p μ =>
  Matrix.of fun α β => limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    QED.TwoLoop.jointEnergyFirstIntegral 2 (dKUnitIntegrandD i 0 R (dkMasses R) ε p p' μ α β)

/-- The longitudinal part of `repD i 0` at `δ₃ = 1`. -/
noncomputable def pieceK (R : Params) (i : Fin 12) : Piece := fun p' p μ =>
  wKD R 1 • dKLimB R i p' p μ

theorem dKLimB_eq {R : Params} {i : Fin 12} {p' p : Fin 4 → ℝ} {μ α β : Fin 4} {v : ℂ}
    (hv : HasLimJ (fun ε => dKUnitIntegrandD i 0 R (dkMasses R) ε p p' μ α β) v) :
    dKLimB R i p' p μ α β = v :=
  hv.2.limUnder_eq

section KPiece

variable {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (i : Fin 12)
include hm hγ hγΛ

/-- The `HasLimJ` limit of the longitudinal unit integrand at a pair. -/
theorem hasLimJ_dKLimB {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (μ α β : Fin 4) :
    HasLimJ (fun ε => dKUnitIntegrandD i 0 R (dkMasses R) ε p p' μ α β)
      (dKLimB R i p' p μ α β) := by
  obtain ⟨v, hv⟩ : ∃ v, HasLimJ (fun ε => dKUnitIntegrandD i 0 R (dkMasses R) ε p p' μ α β) v :=
    by
    rcases kWard_cases i with ⟨j, hj⟩ | hW
    · obtain ⟨_, _, _, _, h⟩ := hasLimJ_dKUnit_int i 0 R hm hγ hγΛ p p' hp hp' hq j hj μ α β
      exact ⟨_, h⟩
    · obtain ⟨_, _, _, _, _, _, _, _, h⟩ :=
        hasLimJ_dKUnit_ext i 0 R hm hγ hγΛ p p' hp hp' hq hW μ α β
      exact ⟨_, h⟩
  rwa [dKLimB_eq hv]

theorem pieceCov_K : PieceCov R.m (pieceK R i) := by
  refine PieceCov.smul (G := dKLimB R i) _ ?_
  intro L S T h p' p hpq h0 h1 μ
  obtain ⟨hpL', hpL, -, -, hqL⟩ := isPairQ_map h hpq h0 h1
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  rcases kWard_cases i with ⟨j, hj⟩ | hW
  · choose w₁ w₂ hw₁ hw₂ hl using
      hasLimJ_dKUnit_int i 0 R hm hγ hγΛ p p' hp hp' hq.le j hj
    choose u₁ u₂ hu₁ hu₂ hu using
      hasLimJ_dKUnit_int i 0 R hm hγ hγΛ (L *ᵥ p) (L *ᵥ p') hpL hpL' hqL.le j hj
    set c := kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ)
    refine dkConj_comb ![c, -c] ![fun μ => Matrix.of (w₁ μ), fun μ => Matrix.of (w₂ μ)]
      ![fun μ => Matrix.of (u₁ μ), fun μ => Matrix.of (u₂ μ)] (fun r μ => ?_) (fun μ => ?_)
      (fun μ => ?_) μ
    · fin_cases r
      · exact kTerm_conj h i R hm hγ hγΛ hp hp' hq.le hpL hpL' hqL.le _ _ _ _ _ _ _ _ _
          hw₁ hu₁ μ
      · exact kTerm_conj h i R hm hγ hγΛ hp hp' hq.le hpL hpL' hqL.le _ _ _ _ _ _ _ _ _
          hw₂ hu₂ μ
    · ext α β
      rw [dKLimB_eq (hl μ α β)]
      simp [Fin.sum_univ_two, c]
      ring
    · ext α β
      rw [dKLimB_eq (hu μ α β)]
      simp [Fin.sum_univ_two, c]
      ring
  · choose w₀ w₁ w₂ w₃ hw₀ hw₁ hw₂ hw₃ hl using
      hasLimJ_dKUnit_ext i 0 R hm hγ hγΛ p p' hp hp' hq.le hW
    choose u₀ u₁ u₂ u₃ hu₀ hu₁ hu₂ hu₃ hu using
      hasLimJ_dKUnit_ext i 0 R hm hγ hγΛ (L *ᵥ p) (L *ᵥ p') hpL hpL' hqL.le hW
    set c := kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ))
    refine dkConj_comb ![c, c, -c, -c] ![fun μ => Matrix.of (w₀ μ), fun μ => Matrix.of (w₁ μ),
      fun μ => Matrix.of (w₂ μ), fun μ => Matrix.of (w₃ μ)] ![fun μ => Matrix.of (u₀ μ),
      fun μ => Matrix.of (u₁ μ), fun μ => Matrix.of (u₂ μ), fun μ => Matrix.of (u₃ μ)]
      (fun r μ => ?_) (fun μ => ?_) (fun μ => ?_) μ
    · fin_cases r
      · exact kTerm_conj h i R hm hγ hγΛ hp hp' hq.le hpL hpL' hqL.le _ _ _ _ _ _ _ _ _
          hw₀ hu₀ μ
      · exact kTerm_conj h i R hm hγ hγΛ hp hp' hq.le hpL hpL' hqL.le _ _ _ _ _ _ _ _ _
          hw₁ hu₁ μ
      · exact kTerm_conj h i R hm hγ hγΛ hp hp' hq.le hpL hpL' hqL.le _ _ _ _ _ _ _ _ _
          hw₂ hu₂ μ
      · exact kTerm_conj h i R hm hγ hγΛ hp hp' hq.le hpL hpL' hqL.le _ _ _ _ _ _ _ _ _
          hw₃ hu₃ μ
    · ext α β
      rw [dKLimB_eq (hl μ α β)]
      simp [Fin.sum_univ_four, c]
      ring
    · ext α β
      rw [dKLimB_eq (hu μ α β)]
      simp [Fin.sum_univ_four, c]
      ring

theorem pieceSharp_K : PieceSharp R.m (pieceK R i) := by
  intro p' p hpq μ
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  rcases kWard_cases i with ⟨j, hj⟩ | hW
  · choose w₁ w₂ hw₁ hw₂ hl using
      hasLimJ_dKUnit_int i 0 R hm hγ hγΛ p p' hp hp' hq.le j hj
    refine sharp_eq_neg_of_smul (conj_wKD_mul_kCst R 1 ((kSgnW i : ℤ) : ℝ))
      (W := Matrix.of (w₁ μ) - Matrix.of (w₂ μ)) ?_ ?_
    · rw [sharp_sub, sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₁,
        sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₂]
    · ext α β
      simp only [pieceK, Matrix.smul_apply, smul_eq_mul]
      rw [dKLimB_eq (hl μ α β)]
      simp
      ring
  · choose w₀ w₁ w₂ w₃ hw₀ hw₁ hw₂ hw₃ hl using
      hasLimJ_dKUnit_ext i 0 R hm hγ hγΛ p p' hp hp' hq.le hW
    refine sharp_eq_neg_of_smul
      (conj_wKD_mul_kCst R 1 (((kSgnW i : ℤ) : ℝ) * ((kSgnO i : ℤ) : ℝ)))
      (W := Matrix.of (w₀ μ) + Matrix.of (w₁ μ) - Matrix.of (w₂ μ) - Matrix.of (w₃ μ)) ?_ ?_
    · rw [sharp_sub, sharp_sub, sharp_add, sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₀,
        sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₁,
        sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₂,
        sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₃]
    · ext α β
      simp only [pieceK, Matrix.smul_apply, smul_eq_mul]
      rw [dKLimB_eq (hl μ α β)]
      simp
      ring

/-- The Phase 4 value of a term of `repB i` along `ι`. -/
noncomputable def dkZR {k : ℕ} (ι : Fin (k + 1) → Fin 10) (hk : 7 ≤ k) (X Y : KSlot)
    (K : Finset (Fin 4)) (hcrit : KCrit i ι (kSet X Y K)) : ℂ :=
  pauliCurveZero (dkCurve (repBClass i) (repBClass_mem i) (repBSlot i) (four_le_repBSlot i)
    R hm hγ hγΛ ι hk _ hcrit) R.m (dkF (kPermD i) (repBClass i) (repBSlot i) R X Y K)

/-- **The Pauli value of the longitudinal part at an internal Ward vertex.** -/
noncomputable def kZInt (j : Fin 3) (hj : kWardD i = j.succ.castSucc) : ℂ :=
  wKD R 1 * (kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ)) *
    (dkZR hm hγ hγΛ i (eIdx j.succ).succAbove (by norm_num) .one .q (Finset.univ.erase j.succ)
        (kCrit_int_del hj (mem_pair_left j)) -
      dkZR hm hγ hγΛ i (eIdx j.castSucc).succAbove (by norm_num) .one .q
        (Finset.univ.erase j.castSucc) (kCrit_int_del hj (mem_pair_right j)))

/-- **The Pauli value of the longitudinal part with the Ward identities at both ends.** -/
noncomputable def kZExt (hW : kWardD i = 4) : ℂ :=
  wKD R 1 * (kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ))) *
    (dkZR hm hγ hγΛ i id (by norm_num) .out .inn Finset.univ (kCrit_ext_id hW 0) +
      dkZR hm hγ hγΛ i (eIdx 0).succAbove (by norm_num) .out .one (Finset.univ.erase 0)
        (kCrit_ext_1 hW) -
      dkZR hm hγ hγΛ i (eIdx 3).succAbove (by norm_num) .one .inn (Finset.univ.erase 3)
        (kCrit_ext_2 hW) -
      dkZR hm hγ hγΛ i dk03 le_rfl .one .one ((Finset.univ.erase 3).erase 0) (kCrit_ext_3 hW))

theorem hasLimJ_curve {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (x : Idx) :
    HasLimJ (fun ε => dKUnitIntegrandD i 0 R (dkMasses R) ε (restMomentum R.m)
      (curveMomentum R.m u) x.1 x.2.1 x.2.2)
      (dKLimB R i (curveMomentum R.m u) (restMomentum R.m) x.1 x.2.1 x.2.2) :=
  hasLimJ_dKLimB hm hγ hγΛ i (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
    ((dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu) x.1 x.2.1 x.2.2

/-- **The Pauli limit of the longitudinal part at an internal Ward vertex.** -/
theorem piecePauli_K_int (j : Fin 3) (hj : kWardD i = j.succ.castSucc) :
    PiecePauli R.m (pieceK R i) (kZInt hm hγ hγΛ i j hj) := by
  have key := fun u (hu : u ∈ Ioo (-1 : ℝ) 1) (x : Idx) =>
    hasLimJ_dKUnit_int i 0 R hm hγ hγΛ (restMomentum R.m) (curveMomentum R.m u)
      (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
      ((dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu) j hj x.1 x.2.1 x.2.2
  choose w₁ w₂ hw₁ hw₂ hl using key
  let v₁ : ℝ → Idx → ℂ := fun u x => if hu : u ∈ Ioo (-1 : ℝ) 1 then w₁ u hu x else 0
  let v₂ : ℝ → Idx → ℂ := fun u x => if hu : u ∈ Ioo (-1 : ℝ) 1 then w₂ u hu x else 0
  have hv₁ : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) x, v₁ u x = w₁ u hu x := fun u hu x =>
    dite_eq_left_of_eq_true (eq_true hu)
  have hv₂ : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) x, v₂ u x = w₂ u hu x := fun u hu x =>
    dite_eq_left_of_eq_true (eq_true hu)
  have hT₁ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := R) hm hγ hγΛ kSlot_one_q (kDeg_int _) (eIdx j.succ).succAbove
    (by norm_num) Fin.succAbove_right_injective (exists_succAbove_eIdx .one .q _ (by simp))
    (kCrit_int_del hj (mem_pair_left j)) v₁ (fun u hu x => by rw [hv₁ u hu x]; exact hw₁ u hu x)
  have hT₂ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := R) hm hγ hγΛ kSlot_one_q (kDeg_int _) (eIdx j.castSucc).succAbove
    (by norm_num) Fin.succAbove_right_injective (exists_succAbove_eIdx .one .q _ (by simp))
    (kCrit_int_del hj (mem_pair_right j)) v₂ (fun u hu x => by rw [hv₂ u hu x]; exact hw₂ u hu x)
  set c := wKD R 1 * (kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ))
  have hS : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1),
      pauliNum R.m (curveMomentum R.m u) (restMomentum R.m)
        (pieceK R i (curveMomentum R.m u) (restMomentum R.m)) =
      c * (pauliSum R.m v₁ u - pauliSum R.m v₂ u) := by
    intro u hu
    rw [pauliNum_eq_sum_idx]
    unfold pauliSum
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [pieceK, Matrix.smul_apply, smul_eq_mul]
    rw [dKLimB_eq (hl u hu x), hv₁ u hu x, hv₂ u hu x]
    ring
  refine ((hT₁.sub hT₂).const_mul c).congr' ?_
  filter_upwards [eventually_mem_Ioo] with u hu
  simp only [evenQuot]
  rw [hS u hu, hS (-u) (neg_mem_Ioo_one hu)]
  ring

/-- **The Pauli limit of the longitudinal part with the Ward identities at both ends.** -/
theorem piecePauli_K_ext (hW : kWardD i = 4) :
    PiecePauli R.m (pieceK R i) (kZExt hm hγ hγΛ i hW) := by
  have key := fun u (hu : u ∈ Ioo (-1 : ℝ) 1) (x : Idx) =>
    hasLimJ_dKUnit_ext i 0 R hm hγ hγΛ (restMomentum R.m) (curveMomentum R.m u)
      (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
      ((dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu) hW x.1 x.2.1 x.2.2
  choose w₀ w₁ w₂ w₃ hw₀ hw₁ hw₂ hw₃ hl using key
  let vOf : ((u : ℝ) → u ∈ Ioo (-1 : ℝ) 1 → Idx → ℂ) → ℝ → Idx → ℂ := fun w u x =>
    if hu : u ∈ Ioo (-1 : ℝ) 1 then w u hu x else 0
  have hv : ∀ w u (hu : u ∈ Ioo (-1 : ℝ) 1) x, vOf w u x = w u hu x := fun w u hu x =>
    dite_eq_left_of_eq_true (eq_true hu)
  have hT₀ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := R) hm hγ hγΛ (by simp [kSlotS])
    (by decide) id (by norm_num) Function.injective_id (fun x _ => ⟨x, rfl⟩)
    (kCrit_ext_id hW 0) (vOf w₀) (fun u hu x => by rw [hv w₀ u hu x]; exact hw₀ u hu x)
  have hT₁ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := R) hm hγ hγΛ (by simp [kSlotS])
    (by decide) (eIdx 0).succAbove (by norm_num) Fin.succAbove_right_injective
    (exists_succAbove_eIdx .out .one _ (by simp)) (kCrit_ext_1 hW) (vOf w₁)
    (fun u hu x => by rw [hv w₁ u hu x]; exact hw₁ u hu x)
  have hT₂ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := R) hm hγ hγΛ (by simp [kSlotS])
    (by decide) (eIdx 3).succAbove (by norm_num) Fin.succAbove_right_injective
    (exists_succAbove_eIdx .one .inn _ (by simp)) (kCrit_ext_2 hW) (vOf w₂)
    (fun u hu x => by rw [hv w₂ u hu x]; exact hw₂ u hu x)
  have hT₃ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := R) hm hγ hγΛ (by simp [kSlotS])
    (by decide) dk03 le_rfl dk03_injective (exists_dk03 .one .one _ (by simp) (by simp))
    (kCrit_ext_3 hW) (vOf w₃) (fun u hu x => by rw [hv w₃ u hu x]; exact hw₃ u hu x)
  set c := wKD R 1 * (kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ)))
  have hS : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1),
      pauliNum R.m (curveMomentum R.m u) (restMomentum R.m)
        (pieceK R i (curveMomentum R.m u) (restMomentum R.m)) =
      c * (pauliSum R.m (vOf w₀) u + pauliSum R.m (vOf w₁) u - pauliSum R.m (vOf w₂) u -
        pauliSum R.m (vOf w₃) u) := by
    intro u hu
    rw [pauliNum_eq_sum_idx]
    unfold pauliSum
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [pieceK, Matrix.smul_apply, smul_eq_mul]
    rw [dKLimB_eq (hl u hu x), hv w₀ u hu x, hv w₁ u hu x, hv w₂ u hu x, hv w₃ u hu x]
    ring
  refine ((((hT₀.add hT₁).sub hT₂).sub hT₃).const_mul c).congr' ?_
  filter_upwards [eventually_mem_Ioo] with u hu
  simp only [evenQuot]
  rw [hS u hu, hS (-u) (neg_mem_Ioo_one hu)]
  ring

theorem exists_piecePauli_K : ∃ Z, PiecePauli R.m (pieceK R i) Z := by
  rcases kWard_cases i with ⟨j, hj⟩ | hW
  · exact ⟨_, piecePauli_K_int hm hγ hγΛ i j hj⟩
  · exact ⟨_, piecePauli_K_ext hm hγ hγΛ i hW⟩

end KPiece

/-! ### The transverse dispersive part -/

section DispLim

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ M mγ Λ : ℝ} (hμ₀ : 0 < μ₀) (hM : μ₀ ≤ M) (hmγ : μ₀ ≤ mγ)
  (hΛ : μ₀ ≤ Λ) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1))
include hc hm hs hμ₀ hM hmγ hΛ hw

/-- **The `q → 0` quotient of the Pauli numerator of the `repB` dispersion integral**: along the
curve, `S(u)/u² → ∫₀¹ w(x) Z(x) dx`. -/
theorem tendsto_pauliNum_div_unitMDispRepB :
    Tendsto (fun u => pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
        (unitMDispRepB c P s w M mγ Λ (restMomentum P.m) (curveMomentum P.m u)) / (u : ℂ) ^ 2)
      (𝓝[≠] 0) (𝓝 (unitMDispPauliRepB c P s w M mγ Λ)) := by
  obtain ⟨C, hC⟩ := norm_unitMPauliS_repB_div_le hc P hm hs hμ₀
  set B := C * (1 + ∑ i, unitMMasses P.m mγ Λ mγ Λ (![mγ, Λ] : Fin 2 → ℝ) i ^ 2) ^ 5 / M ^ 2
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ≠ 0 ∧ |u| ≤ 1 / 2 := by
    have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), |u| ≤ 1 / 2 :=
      Filter.Eventually.mono (nhdsWithin_le_nhds (Icc_mem_nhds
        (by norm_num : (-(1 / 2) : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 2)))
        fun u hu => abs_le.2 hu
    filter_upwards [h1, self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
    exact ⟨hu0, hu⟩
  have hlim : Tendsto (fun u => ∫ x in Ioo (0 : ℝ) 1, w x * (unitMPauliS c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2 u / (u : ℂ) ^ 2)) (𝓝[≠] 0)
      (𝓝 (unitMDispPauliRepB c P s w M mγ Λ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖w x‖ * B) ?_ ?_
      (hw.norm.mul_const _) ?_
    · filter_upwards [h0] with u hu
      exact hw.aestronglyMeasurable.mul (((continuousOn_unitMPauliS_repB hc P hm hs hμ₀ hM hmγ
        hΛ (mem_Ioo_of_abs_le_half hu.2)).div_const _).aestronglyMeasurable measurableSet_Ioo)
    · filter_upwards [h0] with u hu
      refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC x hx M mγ Λ hM hmγ hΛ u hu.1 hu.2) (norm_nonneg _)
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
      exact (tendsto_unitMPauliS_div_pow hc P hm hs hμ₀ (massesGe_repB hmγ hΛ) 2 (by norm_num)
        (trailOne_repBKappa x) (extraGe_repB hx hM hmγ hΛ)).const_mul _
  refine hlim.congr' ?_
  filter_upwards [h0] with u hu
  rw [pauliNum_unitMDispRepB hc P hm hs hμ₀ hM hmγ hΛ hw (mem_Ioo_of_abs_le_half hu.2),
    ← integral_div]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

/-- **Covariance of the `repB` dispersion integral.** -/
theorem pieceCov_unitMDispRepB :
    PieceCov P.m fun p' p => unitMDispRepB c P s w M mγ Λ p p' := by
  intro L S T h p' p hpq h0 h1 μ
  obtain ⟨hpL', hpL, -, -, hqL⟩ := isPairQ_map h hpq h0 h1
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  exact pieceCov_dispMat (fun x hx μ => unitMLimitV_map hc P hm hs hμ₀ (massesGe_repB hmγ hΛ)
      hp hp' hq.le h 2 (by norm_num) (trailOne_repBKappa x) (extraGe_repB hx hM hmγ hΛ) μ)
    (fun μ i j => integrableOn_unitMLimitV_repB_mul hc P hm hs hμ₀ hpL hpL' hqL.le hw hM hmγ hΛ
      μ i j)
    (fun μ i j => integrableOn_unitMLimitV_repB_mul hc P hm hs hμ₀ hp hp' hq.le hw hM hmγ hΛ
      μ i j) μ

end DispLim

section DPiece

variable {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
  (hMf : ∀ f, R.m ≤ R.mass f) (i : Fin 12)
include hm hγ hγΛ hMf

/-- The transverse dispersive part of `repB i`. -/
noncomputable def pieceD (R : Params) (i : Fin 12) : Piece := fun p' p μ =>
  (-2 * vpCst R * wD R 1) • ∑ f, unitMDispRepB (repBClass i) R (repBSlot i) (dispWt R f)
    (R.mass f) R.mγ R.Λ p p' μ

theorem pieceCov_D : PieceCov R.m (pieceD R i) := by
  have hμ₀ : 0 < min R.mγ R.m := lt_min hγ hm
  exact PieceCov.smul _ (PieceCov.sum fun f => pieceCov_unitMDispRepB (repBClass_mem i) R hm
    (four_le_repBSlot i) hμ₀ ((min_le_right _ _).trans (hMf f)) (min_le_left _ _)
    ((min_le_left _ _).trans hγΛ) (integrableOn_dispWt R f))

theorem pieceSharp_D : PieceSharp R.m (pieceD R i) := by
  have hμ₀ : 0 < min R.mγ R.m := lt_min hγ hm
  refine PieceSharp.smul (conj_dispCst R) (PieceSharp.sum fun f => ?_)
  intro p' p hpq μ
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  exact sharp_unitMDispRepB (repBClass_mem i) R hm (four_le_repBSlot i) hμ₀ (min_le_left _ _)
    ((min_le_left _ _).trans hγΛ) hp hp' hq.le ((min_le_right _ _).trans (hMf f))
    (conj_dispWt R f) μ

theorem piecePauli_D : PiecePauli R.m (pieceD R i) ((-2 * vpCst R * wD R 1) *
    ∑ f, unitMDispPauliRepB (repBClass i) R (repBSlot i) (dispWt R f) (R.mass f) R.mγ R.Λ) := by
  have hμ₀ : 0 < min R.mγ R.m := lt_min hγ hm
  exact PiecePauli.smul _ (PiecePauli.sum fun f => tendsto_evenQuot_of_div
    (tendsto_pauliNum_div_unitMDispRepB (repBClass_mem i) R hm (four_le_repBSlot i) hμ₀
      ((min_le_right _ _).trans (hMf f)) (min_le_left _ _) ((min_le_left _ _).trans hγΛ)
      (integrableOn_dispWt R f)))

end DPiece

end QED.ChainProof.SetCMainB

end
