/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBKKVal
public import QED.ChainProof.SetCMainBRestS

/-!
# Set (c), the bubble classes: the terms of the longitudinal dispersive part

Helper level for the open link `QED.ChainProof.SetCMainB.MainBKKLink`. After the Ward identities
(`QED.ChainProof.SetCMain.dKUnit_int`, `dKUnit_ext`) the longitudinal dispersive integrand of
`repB i` is a combination of terms `F · ∏_ι D⁻¹ · (M_f² + x(1-x)k² - iε)⁻¹`: a numerator `F`
over the ten-line unit restricted along a line map `ι`, times the spectral factor of the
inserted bubble. Here every such term with the engine hypotheses is shown to have a dispersive
limit with its value (`QED.ChainProof.SetCMainB.KKVal`), and the scalars of the terms are removed
line by line.

* `kkDen`, `kkSpec`, `kkT`: the unit denominators along `ι`, the spectral factor, the term;
* `KKOk`: the kernel-decidable hypotheses on `ι` and the numerator lines `S`;
* **`kkVal_kkT`**: a term has a dispersive limit (an instance of
  `QED.ChainProof.SetCMainB.kkVal_kkInt`, the line `j₀` the element line `s` of the unit);
* **`kkVal_scalar`**: the scalar `k² + M²` of a line `ι j` is its denominator plus `iε`;
* **`kkVal_sq`**: the factor `k²` cancels against the extra line `9` of mass `Λ`;
* `isLoopPoly_elemSq`, `refinedBound_elemSq`: `k²` as a numerator on the lines `8`, `9`;
* `kkOk_int`, `kkOk_ext`: the hypotheses of the terms used, by kernel evaluation.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open QED.WickModel (Params vacuumPolarizationFeynmanMass)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM QED.ChainProof.SetCUnit
open QED.TwoLoop.Enumeration
open QED.TwoLoop.Bridge (IsLoopPoly isLoopAffine_lineMomentum)
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat)
open QED.Integration.TwoLoop (lineDenom lineMomentum IntNoSubdivergenceRefined
  NoSubdivergenceRefined RefinedBound noSubdivergenceRefined_castLoopMatrix_iff
  refinedBound_lineMomentum)

/-! ### The lines of the unit -/

theorem mScale_one_one (q : Fin 10) : mScale (![1, 1] : Fin 2 → ℝ) q = 1 := by
  rcases mem_mEmb_or_mExtra q with ⟨j, hj⟩ | ⟨j, hj⟩ <;> rw [hj]
  · simp [mScale, mExt_mEmb]
  · simp only [mScale, mExt_mExtra]; fin_cases j <;> rfl

/-- A line of the unit repeating the element line `s` carries the element momentum. -/
theorem lineMomentum_unit_of_mLine (c : Class5) (σ : Fin 8) (p p' : Fin 4 → ℝ) {q : Fin 10}
    (hq : mLine (r := 2) σ q = σ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) (unitMMomenta c σ ![1, 1] p p') q ℓ =
      elemMom c σ p p' ℓ := by
  funext ν
  simp only [lineMomentum, unitMMatrix, unitMMomenta, mScale_one_one, one_smul, hq, elemMom]

theorem mLine_nine : ∀ σ : Fin 8, mLine (r := 2) σ 9 = σ := by
  decide

theorem mLine_mEmb (σ : Fin 8) : mLine (r := 2) σ (mEmb 2 σ) = σ := by
  simp [mLine, mExt_mEmb]

theorem dkMasses_nine (R : Params) : dkMasses R 9 = R.Λ := rfl

/-- The masses of the comparison unit (all photon masses `μ₀`) against those of the unit. -/
theorem unitMMasses_cmp (R : Params) (μ₀ : ℝ) (q : Fin 10) :
    (unitMMasses R.m μ₀ μ₀ μ₀ μ₀ ![μ₀, μ₀] q = R.m ∧ dkMasses R q = R.m) ∨
      (unitMMasses R.m μ₀ μ₀ μ₀ μ₀ ![μ₀, μ₀] q = μ₀ ∧
        (dkMasses R q = R.mγ ∨ dkMasses R q = R.Λ)) := by
  fin_cases q <;> simp [unitMMasses, mExt, unitMasses, QED.Integration.TwoLoop.classPVMasses]

theorem unitMMasses_mEmb_photon (m μ₀ : ℝ) {σ : Fin 8} (hσ : 4 ≤ (σ : ℕ)) :
    unitMMasses m μ₀ μ₀ μ₀ μ₀ ![μ₀, μ₀] (mEmb 2 σ) = μ₀ := by
  rw [unitMMasses, mExt_mEmb]
  revert hσ
  fin_cases σ <;> simp [unitMasses, QED.Integration.TwoLoop.classPVMasses]

/-! ### The terms -/

section Terms

variable (i : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ)

/-- The inverse denominators of the unit along the line map `ι`. -/
noncomputable def kkDen {k : ℕ} (ι : Fin (k + 1) → Fin 10) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ℂ :=
  ∏ a, (lineDenom (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a))
    (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p' (ι a))
    (fun a => dkMasses R (ι a)) ε a ℓ)⁻¹

/-- The spectral factor `(t² + x(1-x)k² - iε)⁻¹` of the inserted bubble, `k` the element
momentum. -/
noncomputable def kkSpec (ε x : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (((vacuumPolarizationFeynmanMass t (Minkowski.dot (elemMom (repBClass i) (repBSlot i) p p' ℓ)
    (elemMom (repBClass i) (repBSlot i) p p' ℓ)) x : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹

/-- **A term**: the numerator `F` over the unit along `ι`, times the spectral factor. -/
noncomputable def kkT {k : ℕ} (ι : Fin (k + 1) → Fin 10) (F : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (ε x : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  F ℓ * kkDen i R p p' ι ε ℓ * kkSpec i p p' t ε x ℓ

/-- The scalar `k_q² + M_q²` of the line `q` of the unit. -/
noncomputable def kkA (q : Fin 10) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot (lineMomentum (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
      (unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p') q ℓ)
    (lineMomentum (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
      (unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p') q ℓ) + dkMasses R q ^ 2 : ℝ) : ℂ)

theorem kkA_eIdx (d : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkA i R p p' (eIdx d) ℓ = dkA (repBClass i) (repBSlot i) R p p' d ℓ := by
  rw [kkA, dkMasses_eIdx]
  rfl

theorem kkA_nine (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkA i R p p' 9 ℓ = elemSq (repBClass i) (repBSlot i) p p' ℓ + ((R.Λ ^ 2 : ℝ) : ℂ) := by
  rw [kkA, lineMomentum_unit_of_mLine _ _ p p' (mLine_nine _), dkMasses_nine, elemSq]
  push_cast
  ring

/-- **The kernel-decidable hypotheses of a term**: the numerator-aware criterion of the unit
along `ι` with the numerator lines `S`, `ι` injective with `S` in its range, the element line
`s` in its range but not in `S`, and the line count of the engine. -/
def KKOk {k : ℕ} (ι : Fin (k + 1) → Fin 10) (S : Finset (Fin 10)) : Prop :=
  IntNoSubdivergenceRefined 2 (Finset.univ.filter fun a => ι a ∈ S)
      (fun a => unitZ (repBClass i) (repBSlot i) (ι a)) ∧
    Function.Injective ι ∧ (∀ x ∈ S, ∃ a, ι a = x) ∧ mEmb 2 (repBSlot i) ∉ S ∧
    (∃ a, ι a = mEmb 2 (repBSlot i)) ∧
    (Finset.univ.filter fun a => ι a ∈ S).card + 4 ≤ k + 1

instance {k : ℕ} (ι : Fin (k + 1) → Fin 10) (S : Finset (Fin 10)) : Decidable (KKOk i ι S) := by
  unfold KKOk; infer_instance

variable {i R p p' t} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
  (hp : Minkowski.dot p p = -R.m ^ 2) (hp' : Minkowski.dot p' p' = -R.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (ht : R.m ≤ t) {w : ℝ → ℂ}
  (hw : IntegrableOn w (Ioo 0 1))
include hm hγ hγΛ hp hp' hq ht hw

/-- **A term has a dispersive limit**: the graph with the spectral line
(`QED.ChainProof.SetCMainB.kkVal_kkInt`) on the unit along `ι`, with the line `j₀` the element
line `s`, the scale `√(x(1-x))`, the spectral mass `t ≥ m` and the lower bound
`μ₀ = min(m_γ, m)` of the masses. -/
theorem kkVal_kkT {k : ℕ} (hk : 7 ≤ k) {ι : Fin (k + 1) → Fin 10} {S : Finset (Fin 10)}
    (hok : KKOk i ι S) {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hP : IsLoopPoly 2 4 F)
    (hB : RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ)) S 4 F) :
    KKVal w (kkT i R p p' t ι F) := by
  obtain ⟨hcrit, hι, hS, hσS, ⟨j₀, hj₀⟩, hcard⟩ := hok
  obtain ⟨Qq, hQ⟩ := hP.exists_loopQuartic
  set μ₀ := min R.mγ R.m with hμ₀def
  have hμ₀ : 0 < μ₀ := lt_min hγ hm
  have hcrit' : NoSubdivergenceRefined 2 (Finset.univ.filter fun a => ι a ∈ S)
      (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a)) := by
    rw [unitMMatrix_comp_eq]
    exact (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr hcrit
  have hB' := RefinedBound.comp_filter ι hι hS (hQ ▸ hB)
  have hj₀E : j₀ ∉ Finset.univ.filter fun a => ι a ∈ S := by simp [hj₀, hσS]
  have hge : ∀ q, μ₀ ≤ dkMasses R q := fun q => by
    rcases unitMMasses_cmp R μ₀ q with ⟨-, h⟩ | ⟨-, h | h⟩ <;> rw [h]
    · exact min_le_right _ _
    · exact min_le_left _ _
    · exact (min_le_left _ _).trans hγΛ
  have sq : ∀ {x : ℝ}, μ₀ ≤ x → μ₀ ^ 2 ≤ x ^ 2 := fun h => pow_le_pow_left₀ hμ₀.le h 2
  have hV : ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (k + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      QED.Integration.TwoLoop.symanzikU
        (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a)) z ≠ 0 →
      unitConst R.m μ₀ ≤ QED.Integration.TwoLoop.symanzikV
        (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a))
        (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p' (ι a))
        (Function.update (fun a => dkMasses R (ι a)) j₀ a) z := fun a ha z hz hz1 hU =>
    QED.Integration.TwoLoop.le_symanzikV_comp_of (σ := ι)
      (fun _ hw hw1 hUw => symanzikV_unitM_ge (repBClass_mem i) (four_le_repBSlot i) hμ₀
        ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩ (extraGe_two le_rfl) hp hp' hq hw hw1 hUw)
      (fun b => by
        by_cases hb : b = j₀
        · subst hb
          rw [Function.update_self, hj₀, unitMMasses_mEmb_photon _ _ (four_le_repBSlot i)]
          exact sq ha
        · rw [Function.update_of_ne hb]
          rcases unitMMasses_cmp R μ₀ (ι b) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]
          · rw [h1]; exact sq (hge _)) hz hz1 hU
  have hkx : Continuous fun x : ℝ => √(x * (1 - x)) := by fun_prop
  have hkx01 : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < √(x * (1 - x)) ∧ √(x * (1 - x)) ≤ 1 := fun x hx =>
    ⟨Real.sqrt_pos.2 (QED.TwoLoop.VPHalfAtAssembly.mem_Ioo_mul_pos hx),
      (Real.sqrt_le_sqrt (by nlinarith [hx.1, hx.2] : x * (1 - x) ≤ 1)).trans_eq Real.sqrt_one⟩
  have hK := kkVal_kkInt (j₀ := j₀) hk hcrit' hB' hcard hj₀E hμ₀ (unitConst_pos hm hμ₀)
    unitConst_le_sq (by rw [hj₀]; exact hge _) hV hkx hkx01
    ((min_le_right _ _).trans ht) hw
  refine hK.congr fun ε _ x hx ℓ => ?_
  have hKk : kkK (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a))
      (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p' (ι a)) j₀ ℓ =
      Minkowski.dot (elemMom (repBClass i) (repBSlot i) p p' ℓ)
        (elemMom (repBClass i) (repBSlot i) p p' ℓ) := by
    show Minkowski.dot (lineMomentum _ _ (ι j₀) ℓ) (lineMomentum _ _ (ι j₀) ℓ) = _
    rw [hj₀, lineMomentum_unit_of_mLine _ _ p p' (mLine_mEmb _)]
  rw [kkInt_eq, hQ, hKk, Real.sq_sqrt (QED.TwoLoop.VPHalfAtAssembly.mem_Ioo_mul_pos hx).le]
  unfold kkT kkDen kkSpec vacuumPolarizationFeynmanMass
  rw [add_comm (x * (1 - x) * _) (t ^ 2)]

end Terms

/-! ### Removing the scalars -/

section Scalars

variable {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t : ℝ} {w : ℝ → ℂ}

theorem tendsto_ofReal_mul_I : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝[>] 0) (𝓝 0) := by
  have h := ((Complex.continuous_ofReal.tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).mul_const I
  simpa using h

/-- **The scalar of a line** `ι j`: `k² + M² = D + iε`, so the term with the scalar is the term
with the line deleted plus `iε` times the term. -/
theorem kkVal_scalar {k : ℕ} (ι : Fin (k + 2) → Fin 10) (j : Fin (k + 2))
    {G : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h₁ : KKVal w (kkT i R p p' t (fun a => ι (j.succAbove a)) G))
    (h₂ : KKVal w (kkT i R p p' t ι G)) :
    KKVal w (kkT i R p p' t ι fun ℓ => G ℓ * kkA i R p p' (ι j) ℓ) := by
  refine (h₁.add (h₂.coef (fun ε => (ε : ℂ) * I) tendsto_ofReal_mul_I (A := 1)
    fun ε hε hε1 => by simpa [abs_of_pos hε] using hε1)).congr
    fun ε hε x _ ℓ => ?_
  have hD := prod_inv_succAbove
    (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a))
    (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p' (ι a))
    (fun a => dkMasses R (ι a)) hε.ne' j ℓ
  have hA := sq_add_eq_lineDenom
    (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a))
    (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p' (ι a))
    (fun a => dkMasses R (ι a)) ε j ℓ
  beta_reduce at hD hA
  simp only [kkT, kkDen]
  rw [hD, show kkA i R p p' (ι j) ℓ = _ from hA]
  ring

/-- **The factor `k²` cancels against the extra line `9`** (`k² = D₉ - Λ² + iε`). -/
theorem kkVal_sq {k : ℕ} (ι : Fin (k + 2) → Fin 10) (j : Fin (k + 2)) (hj : ι j = 9)
    {G : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h₁ : KKVal w (kkT i R p p' t (fun a => ι (j.succAbove a)) G))
    (h₂ : KKVal w (kkT i R p p' t ι G)) :
    KKVal w (kkT i R p p' t ι fun ℓ => G ℓ * elemSq (repBClass i) (repBSlot i) p p' ℓ) := by
  refine ((kkVal_scalar ι j h₁ h₂).add (h₂.const_mul (-((R.Λ ^ 2 : ℝ) : ℂ)))).congr
    fun ε _ x _ ℓ => ?_
  simp only [kkT]
  rw [hj, kkA_nine]
  ring

end Scalars

/-! ### `k²` as a numerator -/

section ElemSq

variable (c : Class5) (σ : Fin 8) (p p' : Fin 4 → ℝ)

theorem elemSq_eq_sum (ℓ : Fin 2 → Fin 4 → ℝ) :
    elemSq c σ p p' ℓ = ∑ μ, ∑ ν, ((Minkowski.metric μ ν : ℝ) : ℂ) *
      (((lineMomentum (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) (unitMMomenta c σ ![1, 1] p p')
          8 ℓ μ : ℝ) : ℂ) *
        ((lineMomentum (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) (unitMMomenta c σ ![1, 1] p p')
          9 ℓ ν : ℝ) : ℂ)) := by
  rw [lineMomentum_unit_of_mLine c σ p p' (mLine_eight σ),
    lineMomentum_unit_of_mLine c σ p p' (mLine_nine σ), elemSq, Minkowski.dot]
  push_cast
  simp only [mul_assoc]

theorem isLoopPoly_elemSq : IsLoopPoly 2 2 (elemSq c σ p p') := by
  rw [show elemSq c σ p p' = _ from funext (elemSq_eq_sum c σ p p')]
  refine IsLoopPoly.sum _ fun μ _ => IsLoopPoly.sum _ fun ν _ => IsLoopPoly.const_mul _ ?_
  exact ((isLoopAffine_lineMomentum _ _ 8).isLoopPoly_coord μ).mul
    ((isLoopAffine_lineMomentum _ _ 9).isLoopPoly_coord ν)

theorem refinedBound_elemSq :
    RefinedBound (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) {8, 9} 2 (elemSq c σ p p') := by
  rw [show elemSq c σ p p' = _ from funext (elemSq_eq_sum c σ p p'),
    show ({8, 9} : Finset (Fin 10)) = {8} ∪ {9} from rfl]
  refine RefinedBound.sum _ fun μ _ => RefinedBound.sum _ fun ν _ => RefinedBound.const_mul _ ?_
  exact (refinedBound_lineMomentum _ _ 8 μ).mul (refinedBound_lineMomentum _ _ 9 ν)
    (by decide)

end ElemSq

/-! ### The hypotheses of the terms -/

/-- The hypotheses of the terms at an internal Ward vertex, by kernel evaluation. -/
theorem kkOk_int : ∀ (i : Fin 12) (j : Fin 3), kWardD i = j.succ.castSucc →
    ∀ d ∈ ({j.succ, j.castSucc} : Finset (Fin 4)),
      KKOk i (fun a : Fin 10 => a) (kSet .one .q (Finset.univ.erase d)) ∧
      KKOk i (fun a : Fin 9 => (eIdx d).succAbove a) (kSet .one .q (Finset.univ.erase d)) ∧
      KKOk i (fun a : Fin 9 => (9 : Fin 10).succAbove a) (kSet .one .q (Finset.univ.erase d)) ∧
      KKOk i (fun a : Fin 8 => (eIdx d).succAbove ((8 : Fin 9).succAbove a))
        (kSet .one .q (Finset.univ.erase d)) := by
  decide +kernel

/-- The hypotheses of the terms with the Ward identities at both ends, by kernel evaluation;
the term with both lines `0`, `3` deleted carries `k²` in its numerator (lines `8`, `9`). -/
theorem kkOk_ext : ∀ i : Fin 12, kWardD i = 4 →
    (∀ r, KKOk i (fun a : Fin 10 => a) (kSetE r) ∧
      KKOk i (fun a : Fin 9 => (9 : Fin 10).succAbove a) (kSetE r)) ∧
    KKOk i (fun a : Fin 9 => (eIdx 0).succAbove a) (kSetE 1) ∧
    KKOk i (fun a : Fin 8 => (eIdx 0).succAbove ((8 : Fin 9).succAbove a)) (kSetE 1) ∧
    KKOk i (fun a : Fin 9 => (eIdx 3).succAbove a) (kSetE 2) ∧
    KKOk i (fun a : Fin 8 => (eIdx 3).succAbove ((8 : Fin 9).succAbove a)) (kSetE 2) ∧
    KKOk i (fun a : Fin 9 => (eIdx 0).succAbove a) (kSetE 3) ∧
    KKOk i (fun a : Fin 8 => (eIdx 0).succAbove ((8 : Fin 9).succAbove a)) (kSetE 3) ∧
    KKOk i (fun a : Fin 9 => (eIdx 3).succAbove a) (kSetE 3) ∧
    KKOk i (fun a : Fin 8 => (eIdx 3).succAbove ((8 : Fin 9).succAbove a)) (kSetE 3) ∧
    KKOk i (fun a : Fin 8 => (eIdx 0).succAbove ((2 : Fin 9).succAbove a))
      (kSetE 3 ∪ {8, 9}) := by
  decide +kernel

theorem eIdx_succAbove_eight : ∀ d : Fin 4, (eIdx d).succAbove (8 : Fin 9) = 9 := by
  decide

theorem eIdx_zero_succAbove_two : (eIdx 0).succAbove (2 : Fin 9) = eIdx 3 := by
  decide

end QED.ChainProof.SetCMainB

end
