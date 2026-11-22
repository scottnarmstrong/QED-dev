/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBKKTerm

/-!
# Set (c), the bubble classes: the pointwise dispersive limits as parametric values

Helper level for the open link `QED.ChainProof.SetCMainB.MainBKKLinkP`. At a fixed Feynman
parameter `x ∈ (0, 1)` the `ε → 0⁺` limit of a graph with the spectral line is the parametric
value of the doubled graph (`QED.ChainProof.SetCMainB.tendsto_kkInt`); here that graph is named,
and the pointwise limits `kkLimX` are computed through the scalar and `k²` reductions.

* `kkData`, **`isParamValue_kkData`**: the doubled graph as parametric data, and the limit of the
  graph with the spectral line as its parametric value;
* `KKVal.limX_congr`, `KKVal.limX_add`, `KKVal.limX_coef`, `KKVal.integrableOn_limX`: the pointwise
  limits under the operations of `QED.ChainProof.SetCMainB.KKVal`;
* `kkJ`, `kkDataT`, **`isParamValue_kkLimX_kkT`**: the pointwise limit of a term of the unit is the
  parametric value of its numerator on the doubled unit;
* **`kkLimX_scalar`**, **`kkLimX_sq`**: the pointwise limits through the scalar and `k²` steps.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open QED.WickModel (Params vacuumPolarizationFeynmanMass)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM QED.ChainProof.SetCUnit
open QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.Integration.TwoLoop (symanzikU symanzikV LoopQuartic NoSubdivergenceRefined
  RefinedBound lineDenom lineMomentum noSubdivergenceRefined_castLoopMatrix_iff)
open QED.Integration.Feynman (simplexSet)

/-! ### The doubled graph -/

section Data

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {p : Fin (m + 1) → Fin 4 → ℝ} {j₀ : Fin (m + 1)}
  {M : Fin (m + 1) → ℝ} {E : Finset (Fin (m + 1))}

/-- **The doubled graph as parametric data**: the graph `G` with the line `j₀` doubled, the new
line `0` rescaled by `κ` and of mass `t` (the data of `tendsto_kkInt`). -/
noncomputable def kkData (hm : 7 ≤ m) (hcrit : NoSubdivergenceRefined 2 E α) {μ₀ c : ℝ}
    (hμ₀ : 0 < μ₀) (hc : 0 < c) (hM0 : μ₀ ≤ M j₀)
    (hV : ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α p (Function.update M j₀ a) z)
    (hcμ : c ≤ μ₀ ^ 2) {κ t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ht : μ₀ ≤ t) : ParamData where
  m := m + 1
  α := fun k => kkSig κ k • α (kkRho j₀ k)
  p := fun k => kkSig κ k • p (kkRho j₀ k)
  M := Fin.cons t M
  E := E.map (Fin.succEmb (m + 1))
  hm := by omega
  hcrit := kk_crit hcrit hκ.ne'
  c := c
  hc := hc
  hV := fun z hz hz1 hU =>
    le_symanzikV_scale_comp_of (σ := kkRho j₀) (hV μ₀ le_rfl) (kkSig_ne_zero hκ.ne') (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [kkSig_zero, kkRho_zero, Function.update_self, Fin.cons_zero]
        have h1 : κ ^ 2 ≤ 1 := by nlinarith
        nlinarith [pow_le_pow_left₀ hμ₀.le ht 2]
      · simp only [kkSig_succ, kkRho_succ, Fin.cons_succ, one_pow, sub_self, zero_mul, add_zero,
          one_mul]
        by_cases hj : j = j₀
        · subst hj; simp only [Function.update_self]
          exact pow_le_pow_left₀ hμ₀.le hM0 2
        · rw [Function.update_of_ne hj]) hz hz1 hU

/-- **The limit of the graph with the spectral line is a parametric value** of the doubled
graph. -/
theorem isParamValue_kkData {Q : LoopQuartic} (hm : 7 ≤ m) (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 Q.eval) {μ₀ c : ℝ} (hμ₀ : 0 < μ₀) (hc : 0 < c) (hM0 : μ₀ ≤ M j₀)
    (hV : ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α p (Function.update M j₀ a) z)
    (hcμ : c ≤ μ₀ ^ 2) {κ t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ht : μ₀ ≤ t) :
    IsParamValue (kkData hm hcrit hμ₀ hc hM0 hV hcμ hκ hκ1 ht) Q.eval
      (limUnder (𝓝[>] (0 : ℝ)) fun ε =>
        QED.TwoLoop.jointEnergyFirstIntegral 2 (kkInt α p j₀ Q M κ t ε)) := by
  have hP : IsParamValue (kkData hm hcrit hμ₀ hc hM0 hV hcμ hκ hκ1 ht) Q.eval
      (-((π : ℂ) ^ 4) * ∫ x in simplexSet (m + 1), QED.TwoLoop.ClassLimit.paramIntegrand Q
        (kkData hm hcrit hμ₀ hc hM0 hV hcμ hκ hκ1 ht).α
        (kkData hm hcrit hμ₀ hc hM0 hV hcμ hκ hκ1 ht).p
        (kkData hm hcrit hμ₀ hc hM0 hV hcμ hκ hκ1 ht).M 0 x) :=
    ⟨Q, rfl, kk_bound hB (kkSig_succ κ), rfl⟩
  have hT : Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (kkInt α p j₀ Q M κ t ε))
      (𝓝[>] 0) (𝓝 _) := hP.tendsto
  rwa [hT.limUnder_eq]

end Data

/-! ### The pointwise limits under the operations -/

namespace KKVal

variable {w : ℝ → ℂ} {H H₁ H₂ : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}

theorem limX_congr (hH : ∀ ε : ℝ, 0 < ε → ∀ x ∈ Ioo (0 : ℝ) 1, ∀ ℓ, H ε x ℓ = H₁ ε x ℓ)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : kkLimX H x = kkLimX H₁ x := by
  unfold kkLimX limUnder
  congr 1
  refine Filter.map_congr ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [funext (hH ε hε x hx)]

theorem limX_add (h₁ : KKVal w H₁) (h₂ : KKVal w H₂) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    kkLimX (fun ε x ℓ => H₁ ε x ℓ + H₂ ε x ℓ) x = kkLimX H₁ x + kkLimX H₂ x := by
  refine Tendsto.limUnder_eq (((h₁.tendsto_limX hx).add (h₂.tendsto_limX hx)).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add (h₁.2.2.2.1 ε hε x hx)
    (h₂.2.2.2.1 ε hε x hx)).symm

theorem limX_coef (a : ℝ → ℂ) {a₀ : ℂ} (ha : Tendsto a (𝓝[>] 0) (𝓝 a₀)) (h : KKVal w H)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    kkLimX (fun ε x ℓ => a ε * H ε x ℓ) x = a₀ * kkLimX H x := by
  refine Tendsto.limUnder_eq ((ha.mul (h.tendsto_limX hx)).congr fun ε => ?_)
  exact (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul _ _).symm

theorem limX_const_mul (c : ℂ) (h : KKVal w H) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    kkLimX (fun ε x ℓ => c * H ε x ℓ) x = c * kkLimX H x :=
  limX_coef (fun _ => c) tendsto_const_nhds h hx

/-- **The weighted pointwise limits are integrable** on `(0, 1)`. -/
theorem integrableOn_limX (h : KKVal w H) :
    IntegrableOn (fun x => w x * kkLimX H x) (Ioo 0 1) := by
  have h' := h
  obtain ⟨hw, -, -, -, -, hM, ⟨C, hC⟩, -⟩ := h
  obtain ⟨u, -, hu0, hu⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have hu' : Tendsto u atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hu, Eventually.of_forall hu0⟩
  have hmeas : AEStronglyMeasurable (kkLimX H) (volume.restrict (Ioo 0 1)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => hM (u n) (hu0 n)) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
    exact (h'.tendsto_limX hx).comp hu'
  have hb : ∀ x ∈ Ioo (0 : ℝ) 1, ‖kkLimX H x‖ ≤ C := fun x hx => by
    refine le_of_tendsto ((h'.tendsto_limX hx).norm) ?_
    filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε
    exact hC ε hε.1 hε.2 x hx
  refine (hw.norm.mul_const C).mono' (hw.aestronglyMeasurable.mul hmeas)
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb x hx) (norm_nonneg _)

end KKVal

/-! ### The terms of the unit -/

section Terms

variable {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t : ℝ} {k : ℕ} {ι : Fin (k + 1) → Fin 10}
  {S : Finset (Fin 10)}

/-- The line of the term repeating the element line `s`. -/
noncomputable def kkJ (hok : KKOk i ι S) : Fin (k + 1) := hok.2.2.2.2.1.choose

theorem kkJ_spec (hok : KKOk i ι S) : ι (kkJ hok) = mEmb 2 (repBSlot i) :=
  hok.2.2.2.2.1.choose_spec

theorem kkT_crit (hok : KKOk i ι S) :
    NoSubdivergenceRefined 2 (Finset.univ.filter fun a => ι a ∈ S)
      (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a)) := by
  rw [unitMMatrix_comp_eq]
  exact (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr hok.1

theorem kkT_ge (hγΛ : R.mγ ≤ R.Λ) (q : Fin 10) : min R.mγ R.m ≤ dkMasses R q := by
  rcases unitMMasses_cmp R (min R.mγ R.m) q with ⟨-, h⟩ | ⟨-, h | h⟩ <;> rw [h]
  · exact min_le_right _ _
  · exact min_le_left _ _
  · exact (min_le_left _ _).trans hγΛ

theorem kkT_V (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
    (hp : Minkowski.dot p p = -R.m ^ 2) (hp' : Minkowski.dot p' p' = -R.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {j₀ : Fin (k + 1)}
    (hj₀ : ι j₀ = mEmb 2 (repBSlot i)) :
    ∀ a : ℝ, min R.mγ R.m ≤ a → ∀ z : Fin (k + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a)) z
        ≠ 0 →
      unitConst R.m (min R.mγ R.m) ≤ symanzikV
        (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a))
        (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p' (ι a))
        (Function.update (fun a => dkMasses R (ι a)) j₀ a) z := by
  have hμ₀ : 0 < min R.mγ R.m := lt_min hγ hm
  have sq : ∀ {x : ℝ}, min R.mγ R.m ≤ x → min R.mγ R.m ^ 2 ≤ x ^ 2 := fun h =>
    pow_le_pow_left₀ hμ₀.le h 2
  intro a ha z hz hz1 hU
  exact QED.Integration.TwoLoop.le_symanzikV_comp_of (σ := ι)
    (fun _ hw hw1 hUw => symanzikV_unitM_ge (repBClass_mem i) (four_le_repBSlot i) hμ₀
      ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩ (extraGe_two le_rfl) hp hp' hq hw hw1 hUw)
    (fun b => by
      by_cases hb : b = j₀
      · subst hb
        rw [Function.update_self, hj₀, unitMMasses_mEmb_photon _ _ (four_le_repBSlot i)]
        exact sq ha
      · rw [Function.update_of_ne hb]
        rcases unitMMasses_cmp R (min R.mγ R.m) (ι b) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1]; exact sq (kkT_ge hγΛ _)) hz hz1 hU

theorem kkScale_mem {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < √(x * (1 - x)) ∧ √(x * (1 - x)) ≤ 1 :=
  ⟨Real.sqrt_pos.2 (QED.TwoLoop.VPHalfAtAssembly.mem_Ioo_mul_pos hx),
    (Real.sqrt_le_sqrt (by nlinarith [hx.1, hx.2] : x * (1 - x) ≤ 1)).trans_eq Real.sqrt_one⟩

/-- **The doubled unit along `ι` at the parameter `x`**: the parametric data of a term. -/
noncomputable def kkDataT (hk : 7 ≤ k) (hok : KKOk i ι S) (hm : 0 < R.m) (hγ : 0 < R.mγ)
    (hγΛ : R.mγ ≤ R.Λ) (p p' : Fin 4 → ℝ) (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (ht : R.m ≤ t) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : ParamData :=
  kkData (j₀ := kkJ hok) hk (kkT_crit hok) (lt_min hγ hm) (unitConst_pos hm (lt_min hγ hm))
    (kkT_ge hγΛ _) (kkT_V hm hγ hγΛ hp hp' hq (kkJ_spec hok)) unitConst_le_sq
    (kkScale_mem hx).1 (kkScale_mem hx).2 ((min_le_right _ _).trans ht)

/-- A term is the graph with the spectral line on the unit along `ι`. -/
theorem kkT_eq_kkInt {j₀ : Fin (k + 1)} (hj₀ : ι j₀ = mEmb 2 (repBSlot i)) {Qq : LoopQuartic}
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hQ : Qq.eval = F) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkT i R p p' t ι F ε x ℓ =
      kkInt (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a))
        (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p' (ι a)) j₀ Qq
        (fun a => dkMasses R (ι a)) √(x * (1 - x)) t ε ℓ := by
  have hKk : kkK (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a))
      (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p' (ι a)) j₀ ℓ =
      Minkowski.dot (elemMom (repBClass i) (repBSlot i) p p' ℓ)
        (elemMom (repBClass i) (repBSlot i) p p' ℓ) := by
    show Minkowski.dot (lineMomentum _ _ (ι j₀) ℓ) (lineMomentum _ _ (ι j₀) ℓ) = _
    rw [hj₀, lineMomentum_unit_of_mLine _ _ p p' (mLine_mEmb _)]
  rw [kkInt_eq, hQ, hKk, Real.sq_sqrt (QED.TwoLoop.VPHalfAtAssembly.mem_Ioo_mul_pos hx).le]
  unfold kkT kkDen kkSpec vacuumPolarizationFeynmanMass
  rw [add_comm (x * (1 - x) * _) (t ^ 2)]

/-- **The pointwise limit of a term is the parametric value of its numerator** on the doubled
unit. -/
theorem isParamValue_kkLimX_kkT (hk : 7 ≤ k) (hok : KKOk i ι S) (hm : 0 < R.m) (hγ : 0 < R.mγ)
    (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (ht : R.m ≤ t) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hP : IsLoopPoly 2 4 F)
    (hB : RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ)) S 4 F) :
    IsParamValue (kkDataT hk hok hm hγ hγΛ p p' hp hp' hq ht hx) F
      (kkLimX (kkT i R p p' t ι F) x) := by
  obtain ⟨Qq, hQ⟩ := hP.exists_loopQuartic
  have hB' := RefinedBound.comp_filter ι hok.2.1 hok.2.2.1 (hQ ▸ hB)
  have h := isParamValue_kkData (j₀ := kkJ hok) (Q := Qq) hk (kkT_crit hok) hB' (lt_min hγ hm)
    (unitConst_pos hm (lt_min hγ hm)) (kkT_ge hγΛ _) (kkT_V hm hγ hγΛ hp hp' hq (kkJ_spec hok))
    unitConst_le_sq (kkScale_mem hx).1 (kkScale_mem hx).2 ((min_le_right _ _).trans ht)
  rw [hQ] at h
  have e : kkLimX (kkT i R p p' t ι F) x = limUnder (𝓝[>] (0 : ℝ)) fun ε =>
      QED.TwoLoop.jointEnergyFirstIntegral 2
        (kkInt (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a))
          (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p' (ι a)) (kkJ hok) Qq
          (fun a => dkMasses R (ι a)) √(x * (1 - x)) t ε) := by
    unfold kkLimX
    congr 1
    funext ε
    rw [funext (kkT_eq_kkInt (kkJ_spec hok) hQ hx ε)]
  rw [e]
  exact h

end Terms

/-! ### The pointwise limits through the reductions -/

section Reductions

variable {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t : ℝ} {w : ℝ → ℂ} {x : ℝ}

/-- **The scalar step**: the pointwise limit of the term with the scalar of the line `ι j` is
that of the term with the line deleted. -/
theorem kkLimX_scalar {k : ℕ} (ι : Fin (k + 2) → Fin 10) (j : Fin (k + 2))
    {G : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h₁ : KKVal w (kkT i R p p' t (fun a => ι (j.succAbove a)) G))
    (h₂ : KKVal w (kkT i R p p' t ι G)) (hx : x ∈ Ioo (0 : ℝ) 1) :
    kkLimX (kkT i R p p' t ι fun ℓ => G ℓ * kkA i R p p' (ι j) ℓ) x =
      kkLimX (kkT i R p p' t (fun a => ι (j.succAbove a)) G) x := by
  have h₃ := h₂.coef (fun ε => (ε : ℂ) * I) tendsto_ofReal_mul_I (A := 1)
    fun ε hε hε1 => by simpa [abs_of_pos hε] using hε1
  rw [KKVal.limX_congr (H₁ := fun ε x ℓ => kkT i R p p' t (fun a => ι (j.succAbove a)) G ε x ℓ +
      (ε : ℂ) * I * kkT i R p p' t ι G ε x ℓ) (fun ε hε x _ ℓ => ?_) hx,
    KKVal.limX_add h₁ h₃ hx, KKVal.limX_coef _ tendsto_ofReal_mul_I h₂ hx, zero_mul, add_zero]
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

/-- **The `k²` step**: `k² = D₉ - Λ² + iε` at the line `ι j = 9`. -/
theorem kkLimX_sq {k : ℕ} (ι : Fin (k + 2) → Fin 10) (j : Fin (k + 2)) (hj : ι j = 9)
    {G : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h₁ : KKVal w (kkT i R p p' t (fun a => ι (j.succAbove a)) G))
    (h₂ : KKVal w (kkT i R p p' t ι G)) (hx : x ∈ Ioo (0 : ℝ) 1) :
    kkLimX (kkT i R p p' t ι fun ℓ => G ℓ * elemSq (repBClass i) (repBSlot i) p p' ℓ) x =
      kkLimX (kkT i R p p' t (fun a => ι (j.succAbove a)) G) x -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t ι G) x := by
  rw [KKVal.limX_congr (H₁ := fun ε x ℓ =>
      kkT i R p p' t ι (fun ℓ => G ℓ * kkA i R p p' (ι j) ℓ) ε x ℓ +
        -((R.Λ ^ 2 : ℝ) : ℂ) * kkT i R p p' t ι G ε x ℓ) (fun ε _ x _ ℓ => ?_) hx,
    KKVal.limX_add (kkVal_scalar ι j h₁ h₂) (h₂.const_mul _) hx, KKVal.limX_const_mul _ h₂ hx,
    kkLimX_scalar ι j h₁ h₂ hx]
  · ring
  simp only [kkT]
  rw [hj, kkA_nine]
  ring

end Reductions

end QED.ChainProof.SetCMainB

end
