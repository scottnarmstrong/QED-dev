/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainDPCurve

/-!
# Set (c), the `δ₃` classes: the canonical Pauli limits of the 24 classes `repD i t`

Helper level for (HS₆): the input `hPM` of
`QED.ChainProof.SetCPauli.isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp` at `.inr (i, t)`.

The limit of `repD i t` along the curve `p'(u)`, `p = (m, 0, 0, 0)` is the transverse part
`dGLimD = w_D · L₁` (a multi-denominator unit with one power of `k²`) plus `w_K` times the limit of
the longitudinal part, a combination, with coefficients independent of `u`, of the parametric
values of two (internal Ward vertex) or four (`i = 0, 6, 10`) terms on the unit with electron
lines deleted. The even quotient of the Pauli numerator converges part by part:

* `tendsto_evenQuot_dG`: the transverse part, to `w_D · unitMPauliZeroPow … 1`
  (`QED.ChainProof.SetCUnitM.tendsto_unitMPauliS_div_pow`);
* `clsLimAt_repD_eq`: at each point of the curve the class limit is `dGLimD` plus `w_K` times
  the limit of the longitudinal integrand;
* the terms, to their Phase 4 values `dkZ = pauliCurveZero (dkCurve …) m (dkF …)`
  (`QED.ChainProof.SetCMain.tendsto_evenQuot_dkTerm`); the transverse value `dGZ`;
* **`tendsto_evenQuot_repD_int`**, **`tendsto_evenQuot_repD_ext`**: the class, with the explicit
  limits `repDLimInt`, `repDLimExt`;
* **`setCClassPauli_inr`**: `SetCClassPauli mainFam P₀ (.inr (i, t))` with the value
  `clsPauliLim mainFam P₀ (.inr (i, t))`; `clsPauliLim_inr_int`, `clsPauliLim_inr_ext`: that value
  is the explicit limit over `64 e m⁵`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.Enumeration QED.ChainProof.SetCUnitM QED.TwoLoop.LimitCovariance
open QED.WickModel (Params)
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.ChainProof.SetCUnit (MassesGe)

/-! ### The transverse part -/

/-- **The even quotient of the transverse part** along the curve. -/
theorem tendsto_evenQuot_dG (R : Params) (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
    (δ₃ : ℝ) (i : Fin 12) :
    Tendsto (evenQuot fun u => pauliNum R.m (curveMomentum R.m u) (restMomentum R.m)
        (dGLimD R δ₃ i (restMomentum R.m) (curveMomentum R.m u))) (𝓝[≠] 0)
      (𝓝 (wD R δ₃ * unitMPauliZeroPow (repBClass i) R (repBSlot i) ![1, 1] (dkMasses R) 1)) := by
  have hM : MassesGe R.mγ R.mγ R.Λ R.mγ R.Λ := ⟨le_rfl, hγΛ, le_rfl, hγΛ⟩
  have h := (tendsto_unitMPauliS_div_pow (repBClass_mem i) R hm (four_le_repBSlot i) hγ hM 1
    (r := 2) (κ := ![1, 1]) (cs := ![R.mγ, R.Λ]) (by norm_num) trailOne_one_two
    (extraGe_two hγΛ)).const_mul (wD R δ₃)
  refine h.congr' ?_
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h0, self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
  have e : ∀ v, pauliNum R.m (curveMomentum R.m v) (restMomentum R.m)
      (dGLimD R δ₃ i (restMomentum R.m) (curveMomentum R.m v)) =
      wD R δ₃ * unitMPauliS (repBClass i) R (repBSlot i) ![1, 1] (dkMasses R) 1 v := fun v =>
    pauliNum_smul _ _ _ _ _
  have hn := unitMPauliS_neg (repBClass_mem i) R hm (four_le_repBSlot i) hγ hM (r := 2)
    (n := 1) (κ := ![1, 1]) (cs := ![R.mγ, R.Λ]) (by norm_num) trailOne_one_two
    (extraGe_two hγΛ) hu
  have hu2 : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.mpr hu0)
  simp only [evenQuot, e, hn]
  field_simp
  ring

/-! ### The class value along the curve -/

section Class

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-- The class limit at a point of the curve is the transverse limit plus `w_K` times the limit of
the longitudinal integrand. -/
theorem clsLimAt_repD_eq (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (i : Fin 12) (t : Fin 2)
    {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (x : QED.TwoLoop.PauliZeroLimit.Idx) {v : ℂ}
    (hl : QED.ChainProof.SetCPauli.CB01.HasLimJ (fun ε => dKUnitIntegrandD i t
      (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (dkMasses (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)) ε
      (restMomentum P₀.m) (curveMomentum P₀.m u) x.1 x.2.1 x.2.2) v) :
    clsLimAt mainFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inr (i, t)) (curveMomentum P₀.m u)
        (restMomentum P₀.m) x.1 x.2.1 x.2.2 =
      dGLimD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) i
          (restMomentum P₀.m) (curveMomentum P₀.m u) x.1 x.2.1 x.2.2 +
        wKD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) * v := by
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  have hG := tendsto_dG_repD (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ
    (dot_restMomentum (m := P₀.m)) (dot_curveMomentum P₀.m hu)
    ((dot_curveMomentum_sub P₀.m hu).symm ▸ curveQ_nonneg P₀.m hu)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl (P₀.e ^ 2 * (shareCt D s).d₃ 0) i t x.1 x.2.1 x.2.2
  have hK := tendsto_dKValD_of_hasLimJ (P₀ := P₀) (D := D) (s := s) hl
  have hT : Tendsto (fun ε => mainFam { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
      (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s) (curveMomentum P₀.m u) (restMomentum P₀.m)
      x.1 (.inr (i, t)) x.2.1 x.2.2) (𝓝[>] 0) (𝓝 (dGLimD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (P₀.e ^ 2 * (shareCt D s).d₃ 0) i (restMomentum P₀.m) (curveMomentum P₀.m u) x.1 x.2.1
        x.2.2 + wKD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) * v)) := by
    refine (hG.add hK).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have e := mainVal_inr_eq_dG_add (P₀ := P₀) (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂)
      (mγ := mγ) (Λ := Λ) (D := D) (s := s) hε (curveMomentum P₀.m u)
      (restMomentum P₀.m) x.1 i t x.2.1 x.2.2
    exact e.symm
  exact hT.limUnder_eq

/-! ### The explicit limits -/

variable (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (i : Fin 12)

/-- The Phase 4 value of a term of `repD i ·` along `ι`. -/
noncomputable def dkZ {k : ℕ} (ι : Fin (k + 1) → Fin 10) (hk : 7 ≤ k) (X Y : KSlot)
    (K : Finset (Fin 4)) (hcrit : KCrit i ι (kSet X Y K)) : ℂ :=
  pauliCurveZero (dkCurve (repBClass i) (repBClass_mem i) (repBSlot i) (four_le_repBSlot i)
    (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (setCAdm_masses hA).1 (setCAdm_masses hA).2.1
    (setCAdm_masses hA).2.2 ι hk _ hcrit) P₀.m
    (dkF (kPermD i) (repBClass i) (repBSlot i) (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) X Y K)

/-- The transverse value `w_D · unitMPauliZeroPow … 1`. -/
noncomputable def dGZ : ℂ :=
  wD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) *
    unitMPauliZeroPow (repBClass i) (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (repBSlot i) ![1, 1]
      (dkMasses (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)) 1

/-- **The limit of the even quotient of `repD i t` at an internal Ward vertex**
`kWardD i = j + 1`: `Z_G + w_K kCst σ (Z₁ - Z₂)`. -/
noncomputable def repDLimInt (j : Fin 3) (hj : kWardD i = j.succ.castSucc) : ℂ :=
  dGZ (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂) (mγ := mγ) (Λ := Λ) (P₀ := P₀) (D := D)
      (s := s) i +
    wKD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) *
      (kCst (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) * (((kSgnW i : ℤ) : ℝ) : ℂ)) *
      (dkZ hA i (eIdx j.succ).succAbove (by norm_num) .one .q (Finset.univ.erase j.succ)
          (kCrit_int_del hj (mem_pair_left j)) -
        dkZ hA i (eIdx j.castSucc).succAbove (by norm_num) .one .q (Finset.univ.erase j.castSucc)
          (kCrit_int_del hj (mem_pair_right j)))

/-- **The limit of the even quotient of `repD i t` with the Ward identities at both ends**
(`kWardD i = 4`): `Z_G + w_K kCst σ σ' (Z₀ + Z₁ - Z₂ - Z₃)`. -/
noncomputable def repDLimExt (hW : kWardD i = 4) : ℂ :=
  dGZ (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂) (mγ := mγ) (Λ := Λ) (P₀ := P₀) (D := D)
      (s := s) i +
    wKD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) *
      (kCst (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) *
        ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ))) *
      (dkZ hA i id (by norm_num) .out .inn Finset.univ (kCrit_ext_id hW 0) +
        dkZ hA i (eIdx 0).succAbove (by norm_num) .out .one (Finset.univ.erase 0)
          (kCrit_ext_1 hW) -
        dkZ hA i (eIdx 3).succAbove (by norm_num) .one .inn (Finset.univ.erase 3)
          (kCrit_ext_2 hW) -
        dkZ hA i dk03 le_rfl .one .one ((Finset.univ.erase 3).erase 0) (kCrit_ext_3 hW))

theorem eventually_mem_Ioo : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
  nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))

/-- **The even quotient of the Pauli numerator of `repD i t` at an internal Ward vertex
converges**, to `repDLimInt`. -/
theorem tendsto_evenQuot_repD_int (t : Fin 2) (j : Fin 3) (hj : kWardD i = j.succ.castSucc) :
    Tendsto (evenQuot fun u => pauliNum P₀.m (curveMomentum P₀.m u) (restMomentum P₀.m)
      (clsLimAt mainFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inr (i, t)) (curveMomentum P₀.m u)
        (restMomentum P₀.m))) (𝓝[≠] 0) (𝓝 (repDLimInt hA i j hj)) := by
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  have key := fun u (hu : u ∈ Ioo (-1 : ℝ) 1) (x : QED.TwoLoop.PauliZeroLimit.Idx) =>
    hasLimJ_dKUnit_int i t (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ (restMomentum P₀.m)
      (curveMomentum P₀.m u) (dot_restMomentum (m := P₀.m)) (dot_curveMomentum P₀.m hu)
      ((dot_curveMomentum_sub P₀.m hu).symm ▸ curveQ_nonneg P₀.m hu) j hj x.1 x.2.1 x.2.2
  choose w₁ w₂ hw₁ hw₂ hl using key
  let v₁ : ℝ → QED.TwoLoop.PauliZeroLimit.Idx → ℂ := fun u x =>
    if hu : u ∈ Ioo (-1 : ℝ) 1 then w₁ u hu x else 0
  let v₂ : ℝ → QED.TwoLoop.PauliZeroLimit.Idx → ℂ := fun u x =>
    if hu : u ∈ Ioo (-1 : ℝ) 1 then w₂ u hu x else 0
  have hv₁ : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) x, v₁ u x = w₁ u hu x := fun u hu x => by
    exact dite_eq_left_of_eq_true (eq_true hu)
  have hv₂ : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) x, v₂ u x = w₂ u hu x := fun u hu x => by
    exact dite_eq_left_of_eq_true (eq_true hu)
  have hT₁ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ kSlot_one_q (kDeg_int _)
    (eIdx j.succ).succAbove
    (by norm_num) Fin.succAbove_right_injective (exists_succAbove_eIdx .one .q _ (by simp))
    (kCrit_int_del hj (mem_pair_left j)) v₁
    (fun u hu x => by rw [hv₁ u hu x]; exact hw₁ u hu x)
  have hT₂ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ kSlot_one_q (kDeg_int _)
    (eIdx j.castSucc).succAbove
    (by norm_num) Fin.succAbove_right_injective (exists_succAbove_eIdx .one .q _ (by simp))
    (kCrit_int_del hj (mem_pair_right j)) v₂
    (fun u hu x => by rw [hv₂ u hu x]; exact hw₂ u hu x)
  have hG := tendsto_evenQuot_dG (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ
    (P₀.e ^ 2 * (shareCt D s).d₃ 0) i
  set c := wKD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) *
    (kCst (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) * (((kSgnW i : ℤ) : ℝ) : ℂ))
  have hS : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1),
      pauliNum P₀.m (curveMomentum P₀.m u) (restMomentum P₀.m)
        (clsLimAt mainFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inr (i, t)) (curveMomentum P₀.m u)
          (restMomentum P₀.m)) =
      pauliNum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m
          (curveMomentum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m u)
          (restMomentum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m)
          (dGLimD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) i
            (restMomentum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m)
            (curveMomentum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m u)) +
        c * (pauliSum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m v₁ u -
          pauliSum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m v₂ u) := by
    intro u hu
    rw [pauliNum_eq_sum_idx, pauliNum_eq_sum_idx]
    unfold pauliSum
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [clsLimAt_repD_eq hA i t hu x (hl u hu x), hv₁ u hu x, hv₂ u hu x]
    ring
  refine (hG.add ((hT₁.sub hT₂).const_mul c)).congr' ?_
  filter_upwards [eventually_mem_Ioo] with u hu
  simp only [evenQuot]
  rw [hS u hu, hS (-u) (neg_mem_Ioo_one hu)]
  ring

/-- **The even quotient of the Pauli numerator of `repD i t` with the Ward identities at both
ends converges**, to `repDLimExt`. -/
theorem tendsto_evenQuot_repD_ext (t : Fin 2) (hW : kWardD i = 4) :
    Tendsto (evenQuot fun u => pauliNum P₀.m (curveMomentum P₀.m u) (restMomentum P₀.m)
      (clsLimAt mainFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inr (i, t)) (curveMomentum P₀.m u)
        (restMomentum P₀.m))) (𝓝[≠] 0) (𝓝 (repDLimExt hA i hW)) := by
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  have key := fun u (hu : u ∈ Ioo (-1 : ℝ) 1) (x : QED.TwoLoop.PauliZeroLimit.Idx) =>
    hasLimJ_dKUnit_ext i t (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ (restMomentum P₀.m)
      (curveMomentum P₀.m u) (dot_restMomentum (m := P₀.m)) (dot_curveMomentum P₀.m hu)
      ((dot_curveMomentum_sub P₀.m hu).symm ▸ curveQ_nonneg P₀.m hu) hW x.1 x.2.1 x.2.2
  choose w₀ w₁ w₂ w₃ hw₀ hw₁ hw₂ hw₃ hl using key
  let vOf : ((u : ℝ) → u ∈ Ioo (-1 : ℝ) 1 → QED.TwoLoop.PauliZeroLimit.Idx → ℂ) →
      ℝ → QED.TwoLoop.PauliZeroLimit.Idx → ℂ := fun w u x =>
    if hu : u ∈ Ioo (-1 : ℝ) 1 then w u hu x else 0
  have hv : ∀ w u (hu : u ∈ Ioo (-1 : ℝ) 1) x, vOf w u x = w u hu x := fun w u hu x =>
    dite_eq_left_of_eq_true (eq_true hu)
  have hT₀ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ (by simp [kSlotS])
    (by decide) id (by norm_num) Function.injective_id (fun x _ => ⟨x, rfl⟩)
    (kCrit_ext_id hW 0) (vOf w₀) (fun u hu x => by rw [hv w₀ u hu x]; exact hw₀ u hu x)
  have hT₁ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ (by simp [kSlotS])
    (by decide) (eIdx 0).succAbove (by norm_num) Fin.succAbove_right_injective
    (exists_succAbove_eIdx .out .one _ (by simp)) (kCrit_ext_1 hW) (vOf w₁)
    (fun u hu x => by rw [hv w₁ u hu x]; exact hw₁ u hu x)
  have hT₂ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ (by simp [kSlotS])
    (by decide) (eIdx 3).succAbove (by norm_num) Fin.succAbove_right_injective
    (exists_succAbove_eIdx .one .inn _ (by simp)) (kCrit_ext_2 hW) (vOf w₂)
    (fun u hu x => by rw [hv w₂ u hu x]; exact hw₂ u hu x)
  have hT₃ := tendsto_evenQuot_dkTerm (kPermD i) (repBSlot i) (repBClass_mem i)
    (four_le_repBSlot i) (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ (by simp [kSlotS])
    (by decide) dk03 le_rfl dk03_injective (exists_dk03 .one .one _ (by simp) (by simp))
    (kCrit_ext_3 hW) (vOf w₃) (fun u hu x => by rw [hv w₃ u hu x]; exact hw₃ u hu x)
  have hG := tendsto_evenQuot_dG (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ
    (P₀.e ^ 2 * (shareCt D s).d₃ 0) i
  set c := wKD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) *
    (kCst (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) *
      ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ)))
  have hS : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1),
      pauliNum P₀.m (curveMomentum P₀.m u) (restMomentum P₀.m)
        (clsLimAt mainFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inr (i, t)) (curveMomentum P₀.m u)
          (restMomentum P₀.m)) =
      pauliNum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m
          (curveMomentum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m u)
          (restMomentum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m)
          (dGLimD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) i
            (restMomentum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m)
            (curveMomentum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m u)) +
        c * (pauliSum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m (vOf w₀) u +
          pauliSum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m (vOf w₁) u -
          pauliSum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m (vOf w₂) u -
          pauliSum (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m (vOf w₃) u) := by
    intro u hu
    rw [pauliNum_eq_sum_idx, pauliNum_eq_sum_idx]
    unfold pauliSum
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [clsLimAt_repD_eq hA i t hu x (hl u hu x), hv w₀ u hu x, hv w₁ u hu x, hv w₂ u hu x,
      hv w₃ u hu x]
    ring
  refine (hG.add ((((hT₀.add hT₁).sub hT₂).sub hT₃).const_mul c)).congr' ?_
  filter_upwards [eventually_mem_Ioo] with u hu
  simp only [evenQuot]
  rw [hS u hu, hS (-u) (neg_mem_Ioo_one hu)]
  ring

end Class

/-! ### The Pauli limits of the classes -/

section Pauli

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-- The canonical Pauli value of `repD i t` at an internal Ward vertex. -/
theorem clsPauliLim_inr_int (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (i : Fin 12) (t : Fin 2)
    (j : Fin 3) (hj : kWardD i = j.succ.castSucc) :
    clsPauliLim mainFam P₀ (.inr (i, t)) M₁ M₂ c₁ c₂ mγ Λ D s =
      repDLimInt hA i j hj / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5) := by
  rw [clsPauliLim, (tendsto_evenQuot_repD_int hA i t j hj).limUnder_eq]

/-- The canonical Pauli value of `repD i t` with the Ward identities at both ends. -/
theorem clsPauliLim_inr_ext (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (i : Fin 12) (t : Fin 2)
    (hW : kWardD i = 4) :
    clsPauliLim mainFam P₀ (.inr (i, t)) M₁ M₂ c₁ c₂ mγ Λ D s =
      repDLimExt hA i hW / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5) := by
  rw [clsPauliLim, (tendsto_evenQuot_repD_ext hA i t hW).limUnder_eq]

/-- **The canonical Pauli limits of the 24 classes `repD i t`**, with the values
`clsPauliLim mainFam P₀ (.inr (i, t))`. -/
theorem setCClassPauli_inr (P₀ : Params) (i : Fin 12) (t : Fin 2) :
    SetCClassPauli mainFam P₀ (.inr (i, t)) (clsPauliLim mainFam P₀ (.inr (i, t))) :=
  setCClassPauli_of_evenQuot (setCClassLim_inr P₀ i t) (setCClassCov_inr P₀ i t)
    fun _ _ _ _ _ _ _ _ hA => by
      rcases kWard_cases i with ⟨j, hj⟩ | hW
      · exact ⟨_, tendsto_evenQuot_repD_int hA i t j hj⟩
      · exact ⟨_, tendsto_evenQuot_repD_ext hA i t hW⟩

end Pauli

end QED.ChainProof.SetCMain

end
