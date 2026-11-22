/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBKKPauli

/-!
# Set (c), the bubble classes: descaling the longitudinal dispersive integrand to `x = 1/2`

Helper level for the input `hMainBD` of `QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces`.
At the Feynman parameter `x` of the bubble, a term of the pointwise limit of the longitudinal
dispersive integrand is `κ⁻²` times a function of `t/κ`, `κ = √(x(1-x))`
(`QED.ChainProof.SetCMainB.kkCurveS_descale`). Comparing with `x = 1/2` (`κ = 1/2`), the
Pauli-weighted integrand at `(x, t)` is `(4x(1-x))⁻¹` times that at `(1/2, t/(2κ))`. This holds
term by term and so for the whole integrand `kkH` of every class `repB i`, and passes to the
Pauli limit `kkLimP` at each `x`.

* `KKDesc`: families with this descaling; closure under sums and constant multiples;
* **`kkDesc_kkT`**: one term along the curve;
* **`kkDesc_kkH`**: the pointwise limit of the longitudinal integrand, for all `i`;
* `kkLimP`, **`kkLimP_descale`**: the Pauli limit at `x`, and
  `kkLimP R i t x = (4x(1-x))⁻¹ kkLimP R i (t/(2√(x(1-x)))) (1/2)`.
-/

@[expose] public section

open Complex Matrix MeasureTheory Set Filter Topology
open QED.WickModel (Params)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM QED.TwoLoop.Enumeration
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.Bridge (IsLoopPoly IsLoopAffine extMomenta pvMomentaE)
open QED.Integration.TwoLoop (RefinedBound lineMomentum pvLines LoopQuartic symanzikU symanzikV)
open QED.ChainProof.SetCUnit (unitConst unitConst_pos)

/-- The spectral mass at `x = 1/2` matching `t` at `x`: `t/(2√(x(1-x)))`. -/
noncomputable def kkHalfMass (t x : ℝ) : ℝ := t / (2 * √(x * (1 - x)))

theorem two_sqrt_mem {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < 2 * √(x * (1 - x)) ∧ 2 * √(x * (1 - x)) ≤ 1 := by
  refine ⟨by linarith [(kkScale_mem hx).1], ?_⟩
  have h : 2 * √(x * (1 - x)) = √(4 * (x * (1 - x))) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h]
  exact (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (2 * x - 1)])).trans_eq Real.sqrt_one

theorem le_kkHalfMass {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1) : t ≤ kkHalfMass t x :=
  le_div_self ht (two_sqrt_mem hx).1 (two_sqrt_mem hx).2

theorem half_mem_Ioo : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

theorem sqrt_quarter : √((1 / 2 : ℝ) * (1 - 1 / 2)) = 1 / 2 := by
  rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- The Pauli-weighted sum of a family of vertex entries. -/
noncomputable abbrev kkPW (m : ℝ) (A : Idx → ℂ) (u : ℝ) : ℂ :=
  ∑ j : Idx, pauliWt m (curveMomentum m u) (restMomentum m) j.1 j.2.1 j.2.2 * A j

/-- **Descaling to `x = 1/2`**: for `t ≥ m`, `x ∈ (0, 1)`, `u ∈ (-1, 1)`, the Pauli-weighted
entries at `(t, x)` are `(4x(1-x))⁻¹` times those at `(t/(2√(x(1-x))), 1/2)`. -/
def KKDesc (m : ℝ) (A : ℝ → Idx → ℝ → ℝ → ℂ) : Prop :=
  ∀ t, m ≤ t → ∀ x ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (-1 : ℝ) 1,
    kkPW m (fun j => A t j x u) u =
      ((4 * (x * (1 - x)) : ℝ) : ℂ)⁻¹ * kkPW m (fun j => A (kkHalfMass t x) j (1 / 2) u) u

namespace KKDesc

variable {m : ℝ} {A A₁ A₂ : ℝ → Idx → ℝ → ℝ → ℂ}

theorem congr (hm : 0 < m) (h : KKDesc m A)
    (hA : ∀ t, m ≤ t → ∀ j, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (-1 : ℝ) 1, A t j x u = A₁ t j x u) :
    KKDesc m A₁ := by
  intro t ht x hx u hu
  have ht' : m ≤ kkHalfMass t x := ht.trans (le_kkHalfMass (hm.le.trans ht) hx)
  have e₁ : (fun j => A₁ t j x u) = fun j => A t j x u := funext fun j => (hA t ht j x hx u hu).symm
  have e₂ : (fun j => A₁ (kkHalfMass t x) j (1 / 2) u) =
      fun j => A (kkHalfMass t x) j (1 / 2) u :=
    funext fun j => (hA _ ht' j _ half_mem_Ioo u hu).symm
  rw [e₁, e₂]
  exact h t ht x hx u hu

theorem add (h₁ : KKDesc m A₁) (h₂ : KKDesc m A₂) :
    KKDesc m fun t j x u => A₁ t j x u + A₂ t j x u := by
  intro t ht x hx u hu
  have e : ∀ B₁ B₂ : Idx → ℂ, kkPW m (fun j => B₁ j + B₂ j) u =
      kkPW m B₁ u + kkPW m B₂ u := fun B₁ B₂ => by
    simp only [kkPW, mul_add, Finset.sum_add_distrib]
  rw [e, e, h₁ t ht x hx u hu, h₂ t ht x hx u hu]
  ring

theorem const_mul (c : ℂ) (h : KKDesc m A) : KKDesc m fun t j x u => c * A t j x u := by
  intro t ht x hx u hu
  have e : ∀ B : Idx → ℂ, kkPW m (fun j => c * B j) u = c * kkPW m B u := fun B => by
    simp only [kkPW, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, e, h t ht x hx u hu]
  ring

end KKDesc

/-! ### One term -/

section Term

variable {i : Fin 12} {R : Params} {k : ℕ} {ι : Fin (k + 1) → Fin 10} {Sl : Finset (Fin 10)}

/-- **A term along the curve descales to `x = 1/2`.** -/
theorem kkDesc_kkT (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hk : 7 ≤ k)
    (hok : KKOk i ι Sl) (N : (Fin 4 → ℝ) → Idx → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hP : ∀ p' j, IsLoopPoly 2 4 (N p' j))
    (hB : ∀ p' j, RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
      Sl 4 (N p' j)) :
    KKDesc R.m fun t j x u =>
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
  have e : ∀ t, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ u, kkPW R.m (fun j =>
      kkLimX (kkT i R (restMomentum R.m) (curveMomentum R.m u) t ι
        (N (curveMomentum R.m u) j)) x) u = kkCurveS C (kkJ hok) t Qf
        (fun u j => pauliWt R.m (curveMomentum R.m u) (restMomentum R.m) j.1 j.2.1 j.2.2)
        √(x * (1 - x)) u :=
    fun t x hx u => by
      show (∑ j : Idx, _) = ∑ j : Idx, _
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      dsimp only
      unfold kkLimX kkV
      congr 1
      funext ε
      rw [funext (kkT_eq_kkInt (kkJ_spec hok) (hQf u j) hx ε)]
      rfl
  intro t ht x hx u hu
  have ht₀ : min R.mγ R.m ≤ t := (min_le_right _ _).trans ht
  have ht₁ : min R.mγ R.m ≤ kkHalfMass t x := ht₀.trans (le_kkHalfMass (hm.le.trans ht) hx)
  have hκ := kkScale_mem hx
  rw [e t x hx u, e _ _ half_mem_Ioo u,
    kkCurveS_descale C (kkJ hok) hμ₀ (kkT_ge hγΛ _) unitConst_le_sq hV ht₀ _ Qf
      (fun u _ j => hQf u j) hFB _ hκ.1 hκ.2 hu,
    kkCurveS_descale C (kkJ hok) hμ₀ (kkT_ge hγΛ _) unitConst_le_sq hV ht₁ _ Qf
      (fun u _ j => hQf u j) hFB _ (kkScale_mem half_mem_Ioo).1 (kkScale_mem half_mem_Ioo).2 hu,
    sqrt_quarter]
  have hκ0 : √(x * (1 - x)) ≠ 0 := hκ.1.ne'
  have hm1 : kkHalfMass t x / (1 / 2) = t / √(x * (1 - x)) := by
    unfold kkHalfMass
    field_simp
  have hsq : √(x * (1 - x)) ^ 2 = x * (1 - x) :=
    Real.sq_sqrt (QED.TwoLoop.VPHalfAtAssembly.mem_Ioo_mul_pos hx).le
  rw [hm1, hsq]
  have hx0 : x * (1 - x) ≠ 0 := (QED.TwoLoop.VPHalfAtAssembly.mem_Ioo_mul_pos hx).ne'
  push_cast
  field_simp
  ring

end Term

/-! ### The pointwise limit of the longitudinal integrand -/

section KKH

variable {i : Fin 12} {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
include hm hγ hγΛ

/-- A term `kNum` along the curve descales. -/
theorem kkDesc_kNi {k : ℕ} {ι : Fin (k + 1) → Fin 10} (X Y : KSlot) (K : Finset (Fin 4))
    (hXY : Disjoint (kSlotS X) (kSlotS Y)) (hd : kSlotD X + kSlotD Y + K.card ≤ 4)
    (hk : 7 ≤ k) (hok : KKOk i ι (kSet X Y K)) :
    KKDesc R.m fun t j x u => kkLimX (kkT i R (restMomentum R.m) (curveMomentum R.m u) t ι
      fun ℓ => kNi i R (restMomentum R.m) (curveMomentum R.m u) X Y K j.1 ℓ j.2.1 j.2.2) x :=
  kkDesc_kkT hm hγ hγΛ hk hok
    (fun p' j ℓ => kNi i R (restMomentum R.m) p' X Y K j.1 ℓ j.2.1 j.2.2)
    (fun _ j => isLoopPolyMat_kNum _ _ _ _ _ _ _ _ _ j.1 hd j.2.1 j.2.2)
    (fun _ j => refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ j.1 hXY hd j.2.1 j.2.2)

/-- The term with `k²` in its numerator descales. -/
theorem kkDesc_kNi_sq (hW : kWardD i = 4) :
    KKDesc R.m fun t j x u => kkLimX (kkT i R (restMomentum R.m) (curveMomentum R.m u) t
      (fun a : Fin 8 => (eIdx 0).succAbove ((2 : Fin 9).succAbove a))
      fun ℓ => kNi i R (restMomentum R.m) (curveMomentum R.m u) .one .one
        ((Finset.univ.erase 3).erase 0) j.1 ℓ j.2.1 j.2.2 *
        elemSq (repBClass i) (repBSlot i) (restMomentum R.m) (curveMomentum R.m u) ℓ) x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h03⟩ := kkOk_ext i hW
  exact kkDesc_kkT hm hγ hγΛ le_rfl h03
    (fun p' j ℓ => kNi i R (restMomentum R.m) p' .one .one ((Finset.univ.erase 3).erase 0) j.1 ℓ
      j.2.1 j.2.2 * elemSq (repBClass i) (repBSlot i) (restMomentum R.m) p' ℓ)
    (fun p' j => (isLoopPolyMat_kNum_two _ _ _ _ _ _ j.1 j.2.1 j.2.2).mul
      (isLoopPoly_elemSq _ _ _ p'))
    (fun p' j => (refinedBoundMat_kNum_two _ _ _ _ _ _ j.1 j.2.1 j.2.2).mul
      (refinedBound_elemSq _ _ _ p') (by decide))

/-- **The pointwise limit of the longitudinal integrand descales to `x = 1/2`**, for every class
`repB i`. -/
theorem kkDesc_kkH :
    KKDesc R.m fun t j x u =>
      kkLimX (kkH i R (restMomentum R.m) (curveMomentum R.m u) t j.1 j.2.1 j.2.2) x := by
  have hq : ∀ u ∈ Ioo (-1 : ℝ) 1, 0 ≤ Minkowski.dot (curveMomentum R.m u - restMomentum R.m)
      (curveMomentum R.m u - restMomentum R.m) := fun u hu =>
    (dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu
  rcases kWardD_cases i with hW | ⟨j, hj⟩
  · obtain ⟨hall, h1d, h1d9, h2d, h2d9, -⟩ := kkOk_ext i hW
    have g₀ := (kkDesc_kNi hm hγ hγΛ .out .inn Finset.univ (by simp [kSlotS])
      (by decide) (by norm_num) (hall 0).2).add
      ((kkDesc_kNi hm hγ hγΛ .out .inn Finset.univ (by simp [kSlotS])
        (by decide) (by norm_num) (hall 0).1).const_mul (-((R.Λ ^ 2 : ℝ) : ℂ)))
    have g₁ := (kkDesc_kNi hm hγ hγΛ .out .one (Finset.univ.erase 0) (by simp [kSlotS])
      (by decide) (by norm_num) h1d9).add
      ((kkDesc_kNi hm hγ hγΛ .out .one (Finset.univ.erase 0) (by simp [kSlotS])
        (by decide) (by norm_num) h1d).const_mul (-((R.Λ ^ 2 : ℝ) : ℂ)))
    have g₂ := (kkDesc_kNi hm hγ hγΛ .one .inn (Finset.univ.erase 3) (by simp [kSlotS])
      (by decide) (by norm_num) h2d9).add
      ((kkDesc_kNi hm hγ hγΛ .one .inn (Finset.univ.erase 3) (by simp [kSlotS])
        (by decide) (by norm_num) h2d).const_mul (-((R.Λ ^ 2 : ℝ) : ℂ)))
    have g₃ := kkDesc_kNi_sq hm hγ hγΛ hW
    refine (KKDesc.const_mul (kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) *
      (((kSgnO i : ℤ) : ℝ) : ℂ))) (((g₀.add g₁).add (g₂.const_mul (-1))).add
        (g₃.const_mul (-1)))).congr hm fun t ht jj x hx u hu => ?_
    rw [kkLimX_kkH_ext hm hγ hγΛ (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
      (hq u hu) ht (integrableOn_dispWt R 0) hx hW jj.1 jj.2.1 jj.2.2]
    ring
  · have g : ∀ d ∈ ({j.succ, j.castSucc} : Finset (Fin 4)), KKDesc R.m fun t jj x u =>
        kkLimX (kkT i R (restMomentum R.m) (curveMomentum R.m u) t
          (fun a : Fin 8 => (eIdx d).succAbove ((8 : Fin 9).succAbove a))
          fun ℓ => kNi i R (restMomentum R.m) (curveMomentum R.m u) .one .q
            (Finset.univ.erase d) jj.1 ℓ jj.2.1 jj.2.2) x +
        -((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R (restMomentum R.m) (curveMomentum R.m u) t
          (fun a : Fin 9 => (eIdx d).succAbove a)
          fun ℓ => kNi i R (restMomentum R.m) (curveMomentum R.m u) .one .q
            (Finset.univ.erase d) jj.1 ℓ jj.2.1 jj.2.2) x := fun d hd => by
      obtain ⟨-, hdl, -, hd9⟩ := kkOk_int i j hj d hd
      exact (kkDesc_kNi hm hγ hγΛ .one .q (Finset.univ.erase d) kSlot_one_q
        (kDeg_int d) (by norm_num) hd9).add ((kkDesc_kNi hm hγ hγΛ .one .q
          (Finset.univ.erase d) kSlot_one_q (kDeg_int d) (by norm_num) hdl).const_mul _)
    refine (KKDesc.const_mul (kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ))
      ((g _ (mem_pair_left j)).add ((g _ (mem_pair_right j)).const_mul (-1)))).congr hm
      fun t ht jj x hx u hu => ?_
    rw [kkLimX_kkH_int hm hγ hγΛ (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
      (hq u hu) ht (integrableOn_dispWt R 0) hx j hj jj.1 jj.2.1 jj.2.2]
    ring

end KKH

/-! ### The Pauli limit at `x` -/

/-- The Pauli-weighted pointwise limit of the longitudinal integrand along the curve. -/
noncomputable abbrev kkPT (R : Params) (i : Fin 12) (t x u : ℝ) : ℂ :=
  kkPW R.m (fun j => kkLimX (kkH i R (restMomentum R.m) (curveMomentum R.m u) t j.1 j.2.1 j.2.2)
    x) u

/-- **The Pauli limit of the longitudinal integrand at `x`**: the limit of the even quotient of
the Pauli-weighted pointwise limit along the curve. -/
noncomputable def kkLimP (R : Params) (i : Fin 12) (t x : ℝ) : ℂ :=
  limUnder (𝓝[≠] (0 : ℝ)) (evenQuot (kkPT R i t x))

theorem neg_mem_Ioo_one' {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : -u ∈ Ioo (-1 : ℝ) 1 :=
  ⟨by linarith [hu.2], by linarith [hu.1]⟩

/-- **The Pauli limit at `x` descales to `x = 1/2`**:
`kkLimP R i t x = (4x(1-x))⁻¹ kkLimP R i (t/(2√(x(1-x)))) (1/2)` for `t ≥ m`. -/
theorem kkLimP_descale {i : Fin 12} {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ)
    (hγΛ : R.mγ ≤ R.Λ) {t : ℝ} (ht : R.m ≤ t) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    kkLimP R i t x =
      ((4 * (x * (1 - x)) : ℝ) : ℂ)⁻¹ * kkLimP R i (kkHalfMass t x) (1 / 2) := by
  have ht' : R.m ≤ kkHalfMass t x := ht.trans (le_kkHalfMass (hm.le.trans ht) hx)
  obtain ⟨Z, hZ⟩ := (kkPauliW_kkH (i := i) hm hγ hγΛ ht').1 (1 / 2) half_mem_Ioo
  have hD := kkDesc_kkH (i := i) hm hγ hγΛ t ht x hx
  have hlim : Tendsto (evenQuot (kkPT R i t x)) (𝓝[≠] 0)
      (𝓝 (((4 * (x * (1 - x)) : ℝ) : ℂ)⁻¹ * Z)) := by
    refine (hZ.const_mul _).congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1))] with u hu
    simp only [evenQuot, kkPT]
    rw [hD u hu, hD (-u) (neg_mem_Ioo_one' hu)]
    ring
  unfold kkLimP
  rw [hlim.limUnder_eq, hZ.limUnder_eq]

end QED.ChainProof.SetCMainB

end
