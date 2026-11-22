/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBKKCurve

/-!
# Set (c), the bubble classes: the Pauli limit of the longitudinal dispersive part

Proves `QED.ChainProof.SetCMainB.MainBKKPauli P₀ i` for all twelve classes `repB i`: the even
quotient of the Pauli numerator of `kkLimB` along the curve converges. At each `x ∈ (0, 1)` the
reductions write the pointwise limit as a combination, with coefficients independent of `p'`, of
values of terms with the spectral line on the unit along a line map; their Pauli quotients
converge and are bounded uniformly in `x` (`QED/ChainProof/SetCMainBKKCurve.lean`, with the data
`kkCurveB` of the unit along the curve), and dominated convergence in `x` gives the limit.

* `KKPauliX`, `KKPauliW`: families whose Pauli quotients converge pointwise in `x` and are
  bounded uniformly; closure under sums and constant multiples;
* **`tendsto_evenQuot_setIntegral`**: dominated convergence in `x`;
* `pauliNum_dispMat`: the Pauli numerator of a dispersion integral;
* `kkCurveB`, **`kkPauliW_kkT`**: a term along the curve;
* **`kkPauliW_kkH`**: the pointwise limit of the longitudinal integrand, for all `i`;
* **`mainBKKPauli`**, **`mainBKKLinkP`**; the consequence
  `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit_of_regB`: (HS₆) from the regulator
  limit `SetCRegLimitB` alone.
-/

@[expose] public section

open Complex Matrix MeasureTheory Set Filter Topology
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM QED.TwoLoop.Enumeration
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.Bridge (IsLoopPoly IsLoopAffine extMomenta pvMomentaE)
open QED.Integration.TwoLoop (RefinedBound lineMomentum pvLines LoopQuartic symanzikU symanzikV)
open QED.Dirac (reflectMatrix)
open QED.ChainProof.SetCUnit (unitConst unitConst_pos)

/-! ### Families with a uniform Pauli limit -/

section Fam

/-- **A family with a uniform Pauli limit**: for each `x ∈ (0, 1)` the even quotient of
`u ↦ T x u` converges, and the quotients are bounded uniformly in `x` and `0 < |u| ≤ 1/2`. -/
def KKPauliX (T : ℝ → ℝ → ℂ) : Prop :=
  (∀ x ∈ Ioo (0 : ℝ) 1, ∃ Z : ℂ, Tendsto (evenQuot (T x)) (𝓝[≠] 0) (𝓝 Z)) ∧
    ∃ B : ℝ, ∀ u : ℝ, u ≠ 0 → |u| ≤ 1 / 2 → ∀ x ∈ Ioo (0 : ℝ) 1, ‖evenQuot (T x) u‖ ≤ B

theorem evenQuot_congr {S S' : ℝ → ℂ} (h : ∀ u ∈ Ioo (-1 : ℝ) 1, S u = S' u) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) : evenQuot S u = evenQuot S' u := by
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  simp only [evenQuot, h u hu, h (-u) hu']

namespace KKPauliX

variable {T T₁ T₂ : ℝ → ℝ → ℂ}

theorem congr (h : KKPauliX T)
    (hT : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (-1 : ℝ) 1, T x u = T₁ x u) : KKPauliX T₁ := by
  obtain ⟨hL, B, hB⟩ := h
  refine ⟨fun x hx => ?_, B, fun u hu0 hu x hx => ?_⟩
  · obtain ⟨Z, hZ⟩ := hL x hx
    refine ⟨Z, hZ.congr' ?_⟩
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1))] with u hu
    exact evenQuot_congr (hT x hx) hu
  · rw [← evenQuot_congr (hT x hx) (mem_Ioo_of_abs_le_half hu)]
    exact hB u hu0 hu x hx

theorem add (h₁ : KKPauliX T₁) (h₂ : KKPauliX T₂) : KKPauliX fun x u => T₁ x u + T₂ x u := by
  obtain ⟨hL₁, B₁, hB₁⟩ := h₁
  obtain ⟨hL₂, B₂, hB₂⟩ := h₂
  have e : ∀ x u, evenQuot (fun u => T₁ x u + T₂ x u) u =
      evenQuot (T₁ x) u + evenQuot (T₂ x) u := fun x u => by
    simp only [evenQuot]; ring
  refine ⟨fun x hx => ?_, B₁ + B₂, fun u hu0 hu x hx => ?_⟩
  · obtain ⟨Z₁, hZ₁⟩ := hL₁ x hx
    obtain ⟨Z₂, hZ₂⟩ := hL₂ x hx
    exact ⟨Z₁ + Z₂, (hZ₁.add hZ₂).congr fun u => (e x u).symm⟩
  · rw [e]
    exact (norm_add_le _ _).trans (add_le_add (hB₁ u hu0 hu x hx) (hB₂ u hu0 hu x hx))

theorem const_mul (c : ℂ) (h : KKPauliX T) : KKPauliX fun x u => c * T x u := by
  obtain ⟨hL, B, hB⟩ := h
  have e : ∀ x u, evenQuot (fun u => c * T x u) u = c * evenQuot (T x) u := fun x u => by
    simp only [evenQuot]; ring
  refine ⟨fun x hx => ?_, ‖c‖ * B, fun u hu0 hu x hx => ?_⟩
  · obtain ⟨Z, hZ⟩ := hL x hx
    exact ⟨c * Z, (hZ.const_mul c).congr fun u => (e x u).symm⟩
  · rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_left (hB u hu0 hu x hx) (norm_nonneg _)

end KKPauliX

/-- **Dominated convergence in the Feynman parameter**: for a family with a uniform Pauli limit
and a weight `w` integrable on `(0, 1)` with `w(x) T(x, u)` integrable, the even quotient of
`u ↦ ∫₀¹ w(x) T(x, u) dx` converges. -/
theorem tendsto_evenQuot_setIntegral {T : ℝ → ℝ → ℂ} (hT : KKPauliX T) {w : ℝ → ℂ}
    (hw : IntegrableOn w (Ioo 0 1))
    (hint : ∀ u ∈ Ioo (-1 : ℝ) 1, IntegrableOn (fun x => w x * T x u) (Ioo 0 1)) :
    ∃ Z : ℂ, Tendsto (evenQuot fun u => ∫ x in Ioo (0 : ℝ) 1, w x * T x u) (𝓝[≠] 0) (𝓝 Z) := by
  obtain ⟨hL, B, hB⟩ := hT
  have hev : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ≠ 0 ∧ |u| ≤ 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Icc_mem_nhds
      (by norm_num : (-(1 / 2) : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 2))] with u hu0 hu
    exact ⟨hu0, abs_le.mpr hu⟩
  have hfun : ∀ u : ℝ, (fun x => w x * evenQuot (T x) u) =
      fun x => (w x * T x u + w x * T x (-u)) / (2 * (u : ℂ) ^ 2) := fun u => funext fun x => by
    simp only [evenQuot]; ring
  refine ⟨∫ x in Ioo (0 : ℝ) 1, w x * limUnder (𝓝[≠] (0 : ℝ)) (evenQuot (T x)),
    (tendsto_integral_filter_of_dominated_convergence (F := fun u x => w x * evenQuot (T x) u)
      (fun x => ‖w x‖ * B) ?_ ?_
      (hw.norm.mul_const _) ?_).congr' ?_⟩
  · filter_upwards [hev] with u hu'
    have hu := hu'.2
    have hu1 := mem_Ioo_of_abs_le_half hu
    have hu1' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu1.2], by linarith [hu1.1]⟩
    rw [hfun u]
    exact (((hint u hu1).add (hint (-u) hu1')).div_const _).aestronglyMeasurable
  · filter_upwards [hev] with u hu'
    obtain ⟨hu0, hu⟩ := hu'
    refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB u hu0 hu x hx) (norm_nonneg _)
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
    exact (tendsto_nhds_limUnder (hL x hx)).const_mul (w x)
  · filter_upwards [hev] with u hu'
    have hu := hu'.2
    have hu1 := mem_Ioo_of_abs_le_half hu
    have hu1' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu1.2], by linarith [hu1.1]⟩
    rw [hfun u, integral_div, integral_add (hint u hu1) (hint (-u) hu1')]
    rfl

/-- The Pauli-weighted entries of a family of vertices. -/
def KKPauliW (m : ℝ) (A : Idx → ℝ → ℝ → ℂ) : Prop :=
  KKPauliX fun x u => ∑ j : Idx, pauliWt m (curveMomentum m u) (restMomentum m) j.1 j.2.1 j.2.2 *
    A j x u

namespace KKPauliW

variable {m : ℝ} {A A₁ A₂ : Idx → ℝ → ℝ → ℂ}

theorem congr (h : KKPauliW m A)
    (hA : ∀ j, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (-1 : ℝ) 1, A j x u = A₁ j x u) :
    KKPauliW m A₁ :=
  KKPauliX.congr h fun x hx u hu => Finset.sum_congr rfl fun j _ => by rw [hA j x hx u hu]

theorem add (h₁ : KKPauliW m A₁) (h₂ : KKPauliW m A₂) :
    KKPauliW m fun j x u => A₁ j x u + A₂ j x u :=
  KKPauliX.congr (KKPauliX.add h₁ h₂) fun x _ u _ => by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem const_mul (c : ℂ) (h : KKPauliW m A) : KKPauliW m fun j x u => c * A j x u :=
  KKPauliX.congr (KKPauliX.const_mul c h) fun x _ u _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

end KKPauliW

/-- **The Pauli numerator of a dispersion integral** is the dispersion integral of the Pauli
numerators. -/
theorem pauliNum_dispMat (m : ℝ) (p' p : Fin 4 → ℝ) {w : ℝ → ℂ}
    {X : ℝ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hI : ∀ μ a b, IntegrableOn (fun x => w x * X x μ a b) (Ioo 0 1)) :
    pauliNum m p' p (dispMat w X) = ∫ x in Ioo (0 : ℝ) 1, w x * pauliNum m p' p (X x) := by
  simp only [pauliNum_eq_sum_idx, dispMat, Matrix.of_apply]
  have hpt : ∀ x, w x * ∑ j : Idx, pauliWt m p' p j.1 j.2.1 j.2.2 * X x j.1 j.2.1 j.2.2 =
      ∑ j : Idx, pauliWt m p' p j.1 j.2.1 j.2.2 * (w x * X x j.1 j.2.1 j.2.2) := fun x => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hpt]
  rw [integral_finsetSum _ fun j _ => (hI j.1 j.2.1 j.2.2).const_mul _]
  simp only [integral_const_mul]

end Fam

/-! ### A term along the curve -/

section Term

variable {i : Fin 12} {R : Params} {t : ℝ} {k : ℕ} {ι : Fin (k + 1) → Fin 10}
  {Sl : Finset (Fin 10)}

/-- **The unit along the line map `ι`, along the curve** `p'(u)`, `p = (m, 0, 0, 0)`. -/
noncomputable def kkCurveB (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hk : 7 ≤ k)
    (hok : KKOk i ι Sl) : CurveData where
  m := k
  α := fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a)
  mom u := fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] (restMomentum R.m)
    (curveMomentum R.m u) (ι a)
  M := fun a => dkMasses R (ι a)
  E := Finset.univ.filter fun a => ι a ∈ Sl
  hm := hk
  hcrit := kkT_crit hok
  c := unitConst R.m (min R.mγ R.m)
  hc := unitConst_pos hm (lt_min hγ hm)
  hV := fun u hu z hz hz1 hU => by
    have h := kkT_V hm hγ hγΛ (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
      ((dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu) (kkJ_spec hok)
      (dkMasses R (ι (kkJ hok))) (kkT_ge hγΛ _) z hz hz1 hU
    rwa [Function.update_eq_self] at h
  hmom := fun a μ => by
    have h := isUPoly_ext_curve (ι := Fin k → ℝ) R.m
      (fun p' => extMomenta (repBClass i) (restMomentum R.m) p'
        (pvLines (mLine (repBSlot i) (ι a)))) (by
        rcases extMomenta_cases (repBClass i) (restMomentum R.m)
          (pvLines (mLine (repBSlot i) (ι a))) with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)) μ
    refine (h.const_mul fun _ => ((mScale (![1, 1] : Fin 2 → ℝ) (ι a) : ℝ) : ℂ)).congr
      fun _ u _ => ?_
    simp only [unitMMomenta, pvMomentaE, Pi.smul_apply, smul_eq_mul, ofReal_mul]
    ring
  hVeven := fun u z => by
    have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
      (by rw [dot_axisOne]; exact one_ne_zero)
    have e := QED.TwoLoop.ReflCovariance.symanzikV_map h
      (fun a => unitMMatrix (repBClass i) (repBSlot i) ![1, 1] (ι a))
      (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] (restMomentum R.m)
        (curveMomentum R.m u) (ι a))
      (fun a => dkMasses R (ι a)) z
    have e2 : (fun a => reflectMatrix axisOne *ᵥ unitMMomenta (repBClass i) (repBSlot i) ![1, 1]
        (restMomentum R.m) (curveMomentum R.m u) (ι a)) =
        fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] (restMomentum R.m)
          (curveMomentum R.m (-u)) (ι a) := by
      rw [← reflectMatrix_curveMomentum, ← reflectMatrix_restMomentum (m := R.m),
        unitMMomenta_map]
      simp only [reflectMatrix_restMomentum]
    rw [e2] at e
    exact e

/-- **A term along the curve has a uniform Pauli limit**: for a numerator of loop degree four
obeying the refined bound on the numerator lines, polynomial in `u` after multiplying by a power
of the weight, the Pauli quotients of the pointwise limits converge at every `x ∈ (0, 1)` and are
bounded uniformly in `x`. -/
theorem kkPauliW_kkT (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (ht : R.m ≤ t)
    (hk : 7 ≤ k) (hok : KKOk i ι Sl) {D n : ℕ}
    (N : (Fin 4 → ℝ) → Idx → (Fin 2 → Fin 4 → ℝ) → ℂ) (hP : ∀ p' j, IsLoopPoly 2 4 (N p' j))
    (hB : ∀ p' j, RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
      Sl 4 (N p' j))
    (hU : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * N (curveMomentum R.m u) j ℓ) :
    KKPauliW R.m fun j x u =>
      kkLimX (kkT i R (restMomentum R.m) (curveMomentum R.m u) t ι
        (N (curveMomentum R.m u) j)) x := by
  let C := kkCurveB hm hγ hγΛ hk hok
  let Qf : ℝ → Idx → LoopQuartic := fun u j =>
    (hP (curveMomentum R.m u) j).exists_loopQuartic.choose
  have hQf : ∀ u j, (Qf u j).eval = N (curveMomentum R.m u) j := fun u j =>
    (hP (curveMomentum R.m u) j).exists_loopQuartic.choose_spec
  have hFB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (N (curveMomentum R.m u) j) :=
    fun u _ j => RefinedBound.comp_filter (m := 9)
      (α := unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ)) ι hok.2.1 hok.2.2.1
      (hB _ j)
  have hμ₀ : 0 < min R.mγ R.m := lt_min hγ hm
  have hV : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ a : ℝ, min R.mγ R.m ≤ a → ∀ z : Fin (C.m + 1) → ℝ,
      (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU C.α z ≠ 0 →
        C.c ≤ symanzikV C.α (C.mom u) (Function.update C.M (kkJ hok) a) z :=
    fun u hu => kkT_V hm hγ hγΛ (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
      ((dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu) (kkJ_spec hok)
  have ht' : min R.mγ R.m ≤ t := (min_le_right _ _).trans ht
  have e : ∀ x ∈ Ioo (0 : ℝ) 1, (fun u => ∑ j : Idx,
      pauliWt R.m (curveMomentum R.m u) (restMomentum R.m) j.1 j.2.1 j.2.2 *
        kkLimX (kkT i R (restMomentum R.m) (curveMomentum R.m u) t ι
          (N (curveMomentum R.m u) j)) x) =
      kkCurveS C (kkJ hok) t Qf
        (fun u j => pauliWt R.m (curveMomentum R.m u) (restMomentum R.m) j.1 j.2.1 j.2.2)
        √(x * (1 - x)) := fun x hx => by
    funext u
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    unfold kkLimX kkV
    congr 1
    funext ε
    rw [funext (kkT_eq_kkInt (kkJ_spec hok) (hQf u j) hx ε)]
    rfl
  obtain ⟨B, hB⟩ := norm_evenQuot_kkCurve_le C (kkJ hok) hμ₀ (kkT_ge hγΛ _) unitConst_le_sq hV
    ht' (fun u j => N (curveMomentum R.m u) j) hU Qf (fun u _ j => hQf u j) hFB
    (fun u j => pauliWt R.m (curveMomentum R.m u) (restMomentum R.m) j.1 j.2.1 j.2.2)
    (fun _ j => isUPoly_pauliWt R.m j) (sum_pauliWt_zero R.m)
  refine ⟨fun x hx => ?_, B, fun u hu0 hu x hx => ?_⟩
  · have h := tendsto_evenQuot_kkCurve C (kkJ hok) hμ₀ (kkT_ge hγΛ _) unitConst_le_sq hV
      ht' (fun u j => N (curveMomentum R.m u) j) hU Qf (fun u _ j => hQf u j) hFB
      (fun u j => pauliWt R.m (curveMomentum R.m u) (restMomentum R.m) j.1 j.2.1 j.2.2)
      (fun _ j => isUPoly_pauliWt R.m j) (sum_pauliWt_zero R.m) (kkScale_mem hx).1
      (kkScale_mem hx).2
    rw [← e x hx] at h
    exact h
  · have h := hB u hu0 hu _ (kkScale_mem hx).1 (kkScale_mem hx).2
    rw [← e x hx] at h
    exact h

end Term

/-! ### The pointwise limit of the longitudinal integrand -/

section KKH

variable {i : Fin 12} {R : Params} {t : ℝ} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
  (ht : R.m ≤ t)
include hm hγ hγΛ ht

/-- A term `kNum` along the curve has a uniform Pauli limit. -/
theorem kkPauliW_kNi {k : ℕ} {ι : Fin (k + 1) → Fin 10} (X Y : KSlot) (K : Finset (Fin 4))
    (hXY : Disjoint (kSlotS X) (kSlotS Y)) (hd : kSlotD X + kSlotD Y + K.card ≤ 4)
    (hk : 7 ≤ k) (hok : KKOk i ι (kSet X Y K)) :
    KKPauliW R.m fun j x u => kkLimX (kkT i R (restMomentum R.m) (curveMomentum R.m u) t ι
      fun ℓ => kNi i R (restMomentum R.m) (curveMomentum R.m u) X Y K j.1 ℓ j.2.1 j.2.2) x :=
  kkPauliW_kkT hm hγ hγΛ ht hk hok
    (fun p' j ℓ => kNi i R (restMomentum R.m) p' X Y K j.1 ℓ j.2.1 j.2.2)
    (fun _ j => isLoopPolyMat_kNum _ _ _ _ _ _ _ _ _ j.1 hd j.2.1 j.2.2)
    (fun _ j => refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ j.1 hXY hd j.2.1 j.2.2)
    (fun j => isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 6)
      (G := fun ℓ y => kNum (kPermD i) (repBClass i) (repBSlot i) R.m (restMomentum R.m) (y 0)
        X Y K j.1 ℓ j.2.1 j.2.2)
      (fun ℓ => isLoopPoly_kNum_out (repBClass i) (repBSlot i) R.m _ ℓ (kPermD i) X Y K j.1
        j.2.1 j.2.2)
      (ℓ := fun _ u => fun _ => curveMomentum R.m u) fun _ ν => isUPoly_curveMomentum R.m ν)

omit hm hγ hγΛ ht in
/-- `k²` is a polynomial of degree two in `p'`. -/
theorem isLoopPoly_elemSq_out (c : Class5) (σ : Fin 8) (p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 1 2 fun y : Fin 1 → Fin 4 → ℝ => elemSq c σ p (y 0) ℓ := by
  have h := (isLoopAffine_unitM_out c σ p ℓ (mEmb 2 σ)).isLoopPoly_propDenom 0 0
  refine (congrArg (IsLoopPoly 1 2) (funext fun y => ?_)).mp h
  rw [lineMomentum_unit_of_mLine _ _ _ _ (mLine_mEmb _)]
  simp [QED.TwoLoop.Bridge.propDenom, elemSq]

/-- The term with `k²` in its numerator along the curve has a uniform Pauli limit. -/
theorem kkPauliW_kNi_sq (hW : kWardD i = 4) :
    KKPauliW R.m fun j x u => kkLimX (kkT i R (restMomentum R.m) (curveMomentum R.m u) t
      (fun a : Fin 8 => (eIdx 0).succAbove ((2 : Fin 9).succAbove a))
      fun ℓ => kNi i R (restMomentum R.m) (curveMomentum R.m u) .one .one
        ((Finset.univ.erase 3).erase 0) j.1 ℓ j.2.1 j.2.2 *
        elemSq (repBClass i) (repBSlot i) (restMomentum R.m) (curveMomentum R.m u) ℓ) x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h03⟩ := kkOk_ext i hW
  exact kkPauliW_kkT hm hγ hγΛ ht le_rfl h03
    (fun p' j ℓ => kNi i R (restMomentum R.m) p' .one .one ((Finset.univ.erase 3).erase 0) j.1 ℓ
      j.2.1 j.2.2 * elemSq (repBClass i) (repBSlot i) (restMomentum R.m) p' ℓ)
    (fun p' j => (isLoopPolyMat_kNum_two _ _ _ _ _ _ j.1 j.2.1 j.2.2).mul
      (isLoopPoly_elemSq _ _ _ p'))
    (fun p' j => (refinedBoundMat_kNum_two _ _ _ _ _ _ j.1 j.2.1 j.2.2).mul
      (refinedBound_elemSq _ _ _ p') (by decide))
    (fun j => isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 8)
      (G := fun ℓ y => kNum (kPermD i) (repBClass i) (repBSlot i) R.m (restMomentum R.m) (y 0)
        .one .one ((Finset.univ.erase 3).erase 0) j.1 ℓ j.2.1 j.2.2 *
        elemSq (repBClass i) (repBSlot i) (restMomentum R.m) (y 0) ℓ)
      (fun ℓ => (isLoopPoly_kNum_out (repBClass i) (repBSlot i) R.m _ ℓ (kPermD i) .one .one
        ((Finset.univ.erase 3).erase 0) j.1 j.2.1 j.2.2).mul
        (isLoopPoly_elemSq_out (repBClass i) (repBSlot i) _ ℓ))
      (ℓ := fun _ u => fun _ => curveMomentum R.m u) fun _ ν => isUPoly_curveMomentum R.m ν)

/-- **The pointwise limit of the longitudinal integrand along the curve has a uniform Pauli
limit**, for every class `repB i` and spectral mass `t ≥ m`. -/
theorem kkPauliW_kkH :
    KKPauliW R.m fun j x u =>
      kkLimX (kkH i R (restMomentum R.m) (curveMomentum R.m u) t j.1 j.2.1 j.2.2) x := by
  have hq : ∀ u ∈ Ioo (-1 : ℝ) 1, 0 ≤ Minkowski.dot (curveMomentum R.m u - restMomentum R.m)
      (curveMomentum R.m u - restMomentum R.m) := fun u hu =>
    (dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu
  rcases kWardD_cases i with hW | ⟨j, hj⟩
  · obtain ⟨hall, h1d, h1d9, h2d, h2d9, -⟩ := kkOk_ext i hW
    have g₀ := (kkPauliW_kNi hm hγ hγΛ ht .out .inn Finset.univ (by simp [kSlotS])
      (by decide) (by norm_num) (hall 0).2).add
      ((kkPauliW_kNi hm hγ hγΛ ht .out .inn Finset.univ (by simp [kSlotS])
        (by decide) (by norm_num) (hall 0).1).const_mul (-((R.Λ ^ 2 : ℝ) : ℂ)))
    have g₁ := (kkPauliW_kNi hm hγ hγΛ ht .out .one (Finset.univ.erase 0) (by simp [kSlotS])
      (by decide) (by norm_num) h1d9).add
      ((kkPauliW_kNi hm hγ hγΛ ht .out .one (Finset.univ.erase 0) (by simp [kSlotS])
        (by decide) (by norm_num) h1d).const_mul (-((R.Λ ^ 2 : ℝ) : ℂ)))
    have g₂ := (kkPauliW_kNi hm hγ hγΛ ht .one .inn (Finset.univ.erase 3) (by simp [kSlotS])
      (by decide) (by norm_num) h2d9).add
      ((kkPauliW_kNi hm hγ hγΛ ht .one .inn (Finset.univ.erase 3) (by simp [kSlotS])
        (by decide) (by norm_num) h2d).const_mul (-((R.Λ ^ 2 : ℝ) : ℂ)))
    have g₃ := kkPauliW_kNi_sq hm hγ hγΛ ht hW
    refine (KKPauliW.const_mul (kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) *
      (((kSgnO i : ℤ) : ℝ) : ℂ))) (((g₀.add g₁).add (g₂.const_mul (-1))).add
        (g₃.const_mul (-1)))).congr fun jj x hx u hu => ?_
    rw [kkLimX_kkH_ext hm hγ hγΛ (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
      (hq u hu) ht (integrableOn_dispWt R 0) hx hW jj.1 jj.2.1 jj.2.2]
    ring
  · have g : ∀ d ∈ ({j.succ, j.castSucc} : Finset (Fin 4)), KKPauliW R.m fun jj x u =>
        kkLimX (kkT i R (restMomentum R.m) (curveMomentum R.m u) t
          (fun a : Fin 8 => (eIdx d).succAbove ((8 : Fin 9).succAbove a))
          fun ℓ => kNi i R (restMomentum R.m) (curveMomentum R.m u) .one .q
            (Finset.univ.erase d) jj.1 ℓ jj.2.1 jj.2.2) x +
        -((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R (restMomentum R.m) (curveMomentum R.m u) t
          (fun a : Fin 9 => (eIdx d).succAbove a)
          fun ℓ => kNi i R (restMomentum R.m) (curveMomentum R.m u) .one .q
            (Finset.univ.erase d) jj.1 ℓ jj.2.1 jj.2.2) x := fun d hd => by
      obtain ⟨-, hdl, -, hd9⟩ := kkOk_int i j hj d hd
      exact (kkPauliW_kNi hm hγ hγΛ ht .one .q (Finset.univ.erase d) kSlot_one_q
        (kDeg_int d) (by norm_num) hd9).add ((kkPauliW_kNi hm hγ hγΛ ht .one .q
          (Finset.univ.erase d) kSlot_one_q (kDeg_int d) (by norm_num) hdl).const_mul _)
    refine (KKPauliW.const_mul (kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ))
      ((g _ (mem_pair_left j)).add ((g _ (mem_pair_right j)).const_mul (-1)))).congr
      fun jj x hx u hu => ?_
    rw [kkLimX_kkH_int hm hγ hγΛ (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
      (hq u hu) ht (integrableOn_dispWt R 0) hx j hj jj.1 jj.2.1 jj.2.2]
    ring

/-- The Pauli numerator of a dispersion integral of the pointwise limit along the curve. -/
theorem pauliNum_kkDisp (f : Fin 3) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    pauliNum R.m (curveMomentum R.m u) (restMomentum R.m) (dispMat (dispWt R f)
      (fun x μ => Matrix.of fun a b =>
        kkLimX (kkH i R (restMomentum R.m) (curveMomentum R.m u) t μ a b) x)) =
      ∫ x in Ioo (0 : ℝ) 1, dispWt R f x * ∑ j : Idx,
        pauliWt R.m (curveMomentum R.m u) (restMomentum R.m) j.1 j.2.1 j.2.2 *
          kkLimX (kkH i R (restMomentum R.m) (curveMomentum R.m u) t j.1 j.2.1 j.2.2) x := by
  have hI : ∀ μ a b, IntegrableOn (fun x => dispWt R f x *
      (fun x μ => Matrix.of fun a b =>
        kkLimX (kkH i R (restMomentum R.m) (curveMomentum R.m u) t μ a b) x) x μ a b)
      (Ioo 0 1) := fun μ a b =>
    (kkVal_dKUnit (i := i) μ a b hm hγ hγΛ (dot_restMomentum (m := R.m))
      (dot_curveMomentum R.m hu) ((dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu)
      ht (integrableOn_dispWt R f)).integrableOn_limX
  rw [pauliNum_dispMat _ _ _ hI]
  simp only [pauliNum_eq_sum_idx, Matrix.of_apply]

/-- **The Pauli limit of one dispersion integral** of the pointwise limit. -/
theorem piecePauli_kkDisp (f : Fin 3) : ∃ Z : ℂ, PiecePauli R.m (fun p' p μ =>
    dispMat (dispWt R f) (fun x μ => Matrix.of fun a b => kkLimX (kkH i R p p' t μ a b) x) μ)
    Z := by
  obtain ⟨Z, hZ⟩ := tendsto_evenQuot_setIntegral (kkPauliW_kkH hm hγ hγΛ ht)
    (integrableOn_dispWt R f) fun u hu => by
      have e : (fun x => dispWt R f x * ∑ j : Idx,
          pauliWt R.m (curveMomentum R.m u) (restMomentum R.m) j.1 j.2.1 j.2.2 *
            kkLimX (kkH i R (restMomentum R.m) (curveMomentum R.m u) t j.1 j.2.1 j.2.2) x) =
          fun x => ∑ j : Idx, pauliWt R.m (curveMomentum R.m u) (restMomentum R.m) j.1 j.2.1
            j.2.2 * (dispWt R f x *
              kkLimX (kkH i R (restMomentum R.m) (curveMomentum R.m u) t j.1 j.2.1 j.2.2) x) :=
        funext fun x => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      exact integrable_finsetSum _ fun j _ => ((kkVal_dKUnit (i := i) j.1 j.2.1 j.2.2 hm hγ hγΛ
        (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
        ((dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu) ht
        (integrableOn_dispWt R f)).integrableOn_limX).const_mul _
  refine ⟨Z, hZ.congr' ?_⟩
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1))] with u hu
  exact evenQuot_congr (fun v hv => (pauliNum_kkDisp hm hγ hγΛ ht f hv).symm) hu

end KKH

/-! ### The Pauli limit of `kkLimB` -/

open QED.ChainProof.SetCLink QED.ChainProof.SetALink
open QED.ChainProof.SetAPauli (regParams)

/-- **The Pauli limit of the longitudinal dispersive part** of every class `repB i` at the
set (c) data. -/
theorem mainBKKPauli (P₀ : Params) (i : Fin 12) : MainBKKPauli P₀ i := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  choose Z hZ using fun f => piecePauli_kkDisp (i := i) (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    hm hγ hγΛ (setCAdm_mass hA f) f
  rw [kkLimB_fun i]
  exact ⟨_, (PiecePauli.sum hZ).smul _⟩

/-- **The strengthened kk link of every class `repB i`.** -/
theorem mainBKKLinkP (P₀ : Params) (i : Fin 12) : MainBKKLinkP P₀ i :=
  mainBKKLinkP_of_pauli (mainBKKPauli P₀ i)

end QED.ChainProof.SetCMainB

namespace QED.ThreeLoop

open QED.ChainProof.SetCPauli (mainFam clsPauliLim SetCRegLimitB setCPauliB)
open QED.ChainProof.SetCMain (setCBetaM)

/-- **(HS₆) from the regulator limit alone**: the strengthened kk links of the twelve `repB`
classes hold (`QED.ChainProof.SetCMainB.mainBKKLinkP`), so only the regulator limit of
`b = setCPauliB P₀ (setCBetaM P₀ βᴮ)`, `βᴮ i = clsPauliLim mainFam P₀ (.inl i)`, remains. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_regB (P₀ : Params)
    (hreg : SetCRegLimitB P₀
      (setCPauliB P₀ (setCBetaM P₀ fun i => clsPauliLim mainFam P₀ (.inl i))))
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          (∃ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s) ∧
          ∀ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (a1SixSetC : ℂ)‖ < η :=
  isFormFactorPair_vertexSetC_pauli_limit_of_kkLinkP P₀
    (fun i => QED.ChainProof.SetCMainB.mainBKKLinkP P₀ i) hreg he hm η hη

end QED.ThreeLoop

end
