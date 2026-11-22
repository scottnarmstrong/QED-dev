/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBSplit

/-!
# Set (c), the bubble classes: the limits of the pieces and the class limit

Helper level for the per-class link `QED.ChainProof.SetCPauli.SetCClassLim` of the twelve
bubble classes `repB i` (`QED.ChainProof.SetCPauli.mainVal (.inl i)`). At fixed `ε > 0` the
value of the outer integrand splits into three parts
(`QED.ChainProof.SetCMainB.jointEnergyFirstIntegral_outerBub_split`); here the `ε → 0⁺` limits
of the first two are proved and the class limit is reduced to two open links.

* `tendsto_logW`: the log constant `c L_ε / 3` tends to `c L_0 / 3`, `L_0 = ∑_f c_f log M_f²`;
* `exists_tendsto_dK_repD`: the longitudinal part of `repD i t` converges at any `δ₃` (from the
  Ward reductions `QED.ChainProof.SetCMain.hasLimJ_dKUnit_int`, `hasLimJ_dKUnit_ext`); with
  `QED.ChainProof.SetCMain.tendsto_dG_repD` the piece (i) converges;
* **`tendsto_dispVal`**: the piece (ii) tends to `-2c · wD 1 · ∑_f unitMDispRepB(w_f, M_f)`
  (`QED.ChainProof.SetCUnitM.tendsto_integral_unitMValue_repB`).

**The open links.**

* `MainBOuterLink P₀ i`: at the set (c) data and every `ε > 0`, the three-loop value of
  `nestB` is the two-loop value of the outer integrand `outerBub`, which is integrable in both
  stages; this is the conclusion of `QED.ChainProof.SetCMainB.jointEnergyFirstIntegral_nestB`,
  and **`mainBOuterLink_of`** gives it from the two hypotheses of that theorem, the integrability
  `MainBNestInt` (`hF`) and the decay `MainBOuterDecay` (`OuterDecay`); the continuity of the
  outer factor and of the photon momentum is proved (`continuous_outerBC`, `continuous_kBC`);
* `MainBRestLink P₀ i`: the rest (the longitudinal dispersive part and the `ε S_ε` part) has an
  `ε → 0⁺` limit.

**`setCClassLim_inl_of`**: `SetCClassLim mainFam P₀ (.inl i)` from `MainBOuterLink` and
`MainBRestLink`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open QED.WickModel (Params)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCLink QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.ChainProof.SetCPauli.CB01 (HasLimJ)

/-! ### The limits of the pieces -/

/-- The log constant is continuous in `ε` when the masses are nonzero. -/
theorem tendsto_bubLogSum (R : Params) (hM : ∀ f, 0 < R.mass f) :
    Tendsto (fun ε => bubLogSum R ε) (𝓝[>] 0) (𝓝 (bubLogSum R 0)) := by
  have hc : Continuous fun ε : ℝ => bubLogSum R ε := by
    unfold bubLogSum
    refine continuous_finsetSum _ fun f _ => continuous_const.mul ?_
    refine Continuous.clog (by fun_prop) fun ε => ?_
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    have := pow_pos (hM f) 2
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]
    linarith
  exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_logW (R : Params) (hM : ∀ f, 0 < R.mass f) :
    Tendsto (fun ε => logW { R with ε := ε } ε) (𝓝[>] 0) (𝓝 (logW R 0)) :=
  ((tendsto_bubLogSum R hM).const_mul (vpCst R)).div_const 3

section Lim

variable {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -R.m ^ 2) (hp' : Minkowski.dot p' p' = -R.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hm hγ hγΛ hp hp' hq

/-- **The longitudinal part of `repD i t` converges** as `ε → 0⁺`, at any `δ₃`. -/
theorem exists_tendsto_dK_repD {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (hΦ : Φ.mass Φ.openLine = R.m) (δ₃ : ℝ) (i : Fin 12) (t : Fin 2) (μ α β : Fin 4) :
    ∃ v : ℂ, Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (dKIntegrand
        { R with ε := ε } Φ δ₃ (repD i t) (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => α) (fun _ => β) (fun _ => μ))) (𝓝[>] 0) (𝓝 (wKD R δ₃ * v)) := by
  have key : ∃ v, HasLimJ (fun ε => dKUnitIntegrandD i t R (dkMasses R) ε p p' μ α β) v := by
    rcases kWard_cases i with ⟨j, hj⟩ | hW
    · obtain ⟨_, _, _, _, h⟩ := hasLimJ_dKUnit_int i t R hm hγ hγΛ p p' hp hp' hq j hj μ α β
      exact ⟨_, h⟩
    · obtain ⟨_, _, _, _, _, _, _, _, h⟩ :=
        hasLimJ_dKUnit_ext i t R hm hγ hγΛ p p' hp hp' hq hW μ α β
      exact ⟨_, h⟩
  obtain ⟨v, hv⟩ := key
  exact ⟨v, (hv.2.const_mul (wKD R δ₃)).congr fun ε =>
    (dK_repD_value { R with ε := ε } R Φ hΦ rfl rfl rfl δ₃ i t p p' μ α β).symm⟩

/-- **The piece (ii) converges** as `ε → 0⁺`, to `-2c · wD 1 · ∑_f unitMDispRepB(w_f, M_f)`. -/
theorem tendsto_dispVal (hMf : ∀ f, R.m ≤ R.mass f) (i : Fin 12) (μ α β : Fin 4) :
    Tendsto (fun ε => -2 * vpCst R * wD R 1 * ∑ f, ∫ x in Ioo (0 : ℝ) 1, dispWt R f x *
        unitMValue (repBClass i) R (repBSlot i) (repBKappa x)
          (unitMMasses R.m R.mγ R.Λ R.mγ R.Λ (repBExtra (R.mass f) R.mγ R.Λ)) ε p p' 2 μ α β)
      (𝓝[>] 0) (𝓝 (-2 * vpCst R * wD R 1 * ∑ f, unitMDispRepB (repBClass i) R (repBSlot i)
        (dispWt R f) (R.mass f) R.mγ R.Λ p p' μ α β)) := by
  have hμ₀ : 0 < min R.mγ R.m := lt_min hγ hm
  refine (tendsto_finsetSum _ fun f _ => ?_).const_mul _
  exact tendsto_integral_unitMValue_repB (repBClass_mem i) R hm (four_le_repBSlot i) hμ₀ hp hp'
    hq (integrableOn_dispWt R f) ((min_le_right _ _).trans (hMf f)) (min_le_left _ _)
    ((min_le_left _ _).trans hγΛ) μ α β

end Lim

/-! ### The open links and the class limit -/

/-- The outer factor of `repB i` at the set (c) momenta. -/
noncomputable abbrev outerBC (Q : Params) {F : Type} (Φ : Lepton.Flavors F) (i : Fin 12)
    (p' p : Fin 4 → ℝ) (μ α β : Fin 4) : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
  outerBW Q Φ i (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
    (fun _ => μ)

/-- The photon momentum through the bubble of `repB i` at the set (c) momenta. -/
noncomputable abbrev kBC (i : Fin 12) (p' p : Fin 4 → ℝ) : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ :=
  kBW i (fun _ => p') (fun _ => p) (fun _ => p' - p)

/-- **The nested-to-joint link of `repB i`** (open): at the set (c) data and every `ε > 0`, the
three-loop value of `nestB` is the two-loop value of `outerBub`, which is integrable in both
stages. -/
def MainBOuterLink (P₀ : Params) (i : Fin 12) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ p' p, IsPairQ P₀.m p' p → ∀ ε : ℝ, 0 < ε → ∀ μ α β : Fin 4,
      QED.TwoLoop.jointEnergyFirstIntegral 3 (nestB { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
          (outerBC { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
            i p' p μ α β) (kBC i p' p)) =
        QED.TwoLoop.jointEnergyFirstIntegral 2
          (outerBub { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
            (outerBC { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
              (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p' p μ α β) (kBC i p' p)) ∧
      QED.TwoLoop.jointEnergyFirstIntegrable 2
        (outerBub { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
          (outerBC { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
            (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p' p μ α β) (kBC i p' p))

/-- **The integrability hypothesis `hF`** (open): both stages of (T₉) at three loops for `nestB`
of `repB i`, at the set (c) data and every `ε > 0`. -/
def MainBNestInt (P₀ : Params) (i : Fin 12) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ p' p, IsPairQ P₀.m p' p → ∀ ε : ℝ, 0 < ε → ∀ μ α β : Fin 4,
      QED.TwoLoop.jointEnergyFirstIntegrable 3 (nestB { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        (outerBC { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
          i p' p μ α β) (kBC i p' p))

/-- **The decay hypothesis `OuterDecay`** (open) of the outer factor of `repB i`, at the set (c)
data and every `ε > 0`. -/
def MainBOuterDecay (P₀ : Params) (i : Fin 12) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ p' p, IsPairQ P₀.m p' p → ∀ ε : ℝ, 0 < ε → ∀ μ α β : Fin 4,
      OuterDecay (outerBC { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p' p μ α β) (kBC i p' p)

/-- **The rest link of `repB i`** (open): at the set (c) data the value of the rest (the
longitudinal dispersive part and the `ε S_ε` part) has an `ε → 0⁺` limit. -/
def MainBRestLink (P₀ : Params) (i : Fin 12) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ p' p, IsPairQ P₀.m p' p → ∃ Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ, ∀ μ α β,
      Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        (restB { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
          i p p' μ α β)) (𝓝[>] 0) (𝓝 (Y μ α β))


/-! ### Continuity of the outer factor -/

section Cont

open QED.TwoLoop.Bridge (electronNumerator electronNumerator_apply propDenom propDenom_ne_zero)
open QED.GradedProof.X0 (dProd)
open QED.ChainProof.Enum (pc)

theorem continuous_mvReal_loop (p q : Fin 4 → ℝ) (v : Fin 4 → ℤ) :
    Continuous fun ℓ : Fin 2 → Fin 4 → ℝ => mvReal ℓ p q v := by
  simp only [mvReal, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  fun_prop

theorem continuous_lineMomentum₂_repD (i : Fin 12) (p' p : Fin 4 → ℝ)
    (l : QED.WickModel.Line (repD i 0)) :
    Continuous fun ℓ : Fin 2 → Fin 4 → ℝ => QED.WickModel.lineMomentum₂ (repD i 0) (fun _ => p')
      (fun _ => p) (fun _ => p' - p) ℓ l := by
  have h : ∀ ℓ, QED.WickModel.lineMomentum₂ (repD i 0) (fun _ => p') (fun _ => p)
      (fun _ => p' - p) ℓ l = mvReal ℓ p (p' - p) (mv (repD i 0) l) := fun ℓ =>
    lineMomentum₂_eq_mv _ _ _ _ (by simp) ℓ l
  simp only [h]
  exact continuous_mvReal_loop _ _ _

/-- **The photon momentum through the bubble is continuous.** -/
theorem continuous_kBC (i : Fin 12) (p' p : Fin 4 → ℝ) : Continuous (kBC i p' p) := by
  have h : ∀ ℓ, kBC i p' p ℓ = mvReal ℓ p (p' - p) (pmv (repD i 0) (pc kD 5 0)) := fun ℓ =>
    photonMomentum₂_eq_pmv _ _ _ _ (by simp) ℓ _
  rw [show kBC i p' p = fun ℓ => mvReal ℓ p (p' - p) (pmv (repD i 0) (pc kD 5 0)) from
    funext h]
  exact continuous_mvReal_loop _ _ _

theorem continuous_dProd_comp {X : Type*} [TopologicalSpace X] {f : X → Fin 4 → ℝ}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) (ms : List ℝ) :
    Continuous fun x => dProd ε ms (f x) := by
  unfold dProd
  refine continuous_list_prod _ fun M _ => Continuous.inv₀ ?_ fun x =>
    propDenom_ne_zero hε.ne' _
  simp only [propDenom, Minkowski.dot]
  have := fun ν => (continuous_apply ν).comp hf
  fun_prop

/-- **The outer factor of `repB i` is continuous** at every `ε > 0`. -/
theorem continuous_outerBC (Q : Params) {F : Type} (Φ : Lepton.Flavors F) (hε : 0 < Q.ε)
    (i : Fin 12) (p' p : Fin 4 → ℝ) (μ α β ρ σ : Fin 4) :
    Continuous fun ℓ' => outerBC Q Φ i p' p μ α β ℓ' ρ σ := by
  unfold outerBC outerBW insD
  refine (continuous_const.mul (continuous_finsetSum _ fun a _ => continuous_finsetSum _
    fun b _ => continuous_finsetSum _ fun lor _ => continuous_const.mul
      (continuous_const.mul (continuous_const.mul ?_)))).neg
  unfold lineProd
  refine continuous_finsetProd _ fun l _ => Continuous.mul ?_
    (continuous_dProd_comp (continuous_lineMomentum₂_repD i p' p l) hε _)
  rcases l with f | g
  · have hk := continuous_lineMomentum₂_repD i p' p (.inl f)
    simp only [dNum, electronNumerator_apply]
    have := fun ν => (continuous_apply ν).comp hk
    fun_prop
  · exact continuous_const

end Cont

variable {P₀ : Params}

theorem setCAdm_mass {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (f : Fin 3) :
    P₀.m ≤ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).mass f := by
  obtain ⟨h1, h2, -⟩ := hA
  fin_cases f
  · exact le_rfl
  · exact h1.le
  · exact h2.le

/-- **The nested-to-joint link from the hypotheses of `jointEnergyFirstIntegral_nestB`**. -/
theorem mainBOuterLink_of {i : Fin 12} (hF : MainBNestInt P₀ i) (hd : MainBOuterDecay P₀ i) :
    MainBOuterLink P₀ i := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq ε hε μ α β
  obtain ⟨hm, -, -⟩ := setCAdm_masses hA
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, -⟩ := id hA
  exact jointEnergyFirstIntegral_nestB (P := { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }) hm
    hM₁ hM₂ hPV₁ hPV₂ hε (continuous_outerBC _ _ hε i p' p μ α β) (continuous_kBC i p' p)
    (hd M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq ε hε μ α β)
    (hF M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq ε hε μ α β)

/-- **The limit link of `repB i`** from the nested-to-joint link and the rest link. -/
theorem setCClassLim_inl_of {i : Fin 12} (hN : MainBOuterLink P₀ i) (hR : MainBRestLink P₀ i) :
    SetCClassLim mainFam P₀ (.inl i) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  obtain ⟨Y, hY⟩ := hR M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  have hpq' := hpq
  obtain ⟨hp', hp, -, -, hq⟩ := hpq'
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with hRdef
  have hMf : ∀ f, R.m ≤ R.mass f := setCAdm_mass hA
  have hMp : ∀ f, 0 < R.mass f := fun f => hm.trans_le (hMf f)
  have hv : ∀ μ α β : Fin 4, ∃ v : ℂ, Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
      (dKIntegrand { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) 1 (repD i 0)
        (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)))
      (𝓝[>] 0) (𝓝 (wKD R 1 * v)) := fun μ α β =>
    exists_tendsto_dK_repD (R := R) hm hγ hγΛ hp hp' hq.le _ rfl 1 i 0 μ α β
  choose v hv using hv
  refine ⟨fun μ => Matrix.of fun α β => -(logW R 0 * (dGLimD R 1 i p p' μ α β +
    wKD R 1 * v μ α β) + -2 * vpCst R * wD R 1 * ∑ f, unitMDispRepB (repBClass i) R (repBSlot i)
      (dispWt R f) (R.mass f) R.mγ R.Λ p p' μ α β + Y μ α β), fun μ α β => ?_⟩
  have hI := (tendsto_logW R hMp).mul ((tendsto_dG_repD (R := R) hm hγ hγΛ hp hp' hq.le
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl 1 i 0 μ α β).add (hv μ α β))
  have hII := tendsto_dispVal (R := R) hm hγ hγΛ hp hp' hq.le hMf i μ α β
  refine (((hI.add hII).add (hY μ α β)).neg).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  obtain ⟨hnest, hO⟩ := hN M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq ε hε μ α β
  have hval := (jointEnergyFirstIntegral_outerBub_split { R with ε := ε } R
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl rfl rfl rfl i p p' μ α β hε hMp hO).2
  have hcv := contractionValue_repB_eq { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (shareCt D s) hε.ne' (flavorsLoop_lepton _) i (pOut := fun _ => p') (pIn := fun _ => p)
    (kIn := fun _ => p' - p) (by simp) (fun _ => α) (fun _ => β) (fun _ => μ)
  simp only [mainFam, mainVal, clsVal, Matrix.neg_apply, Matrix.of_apply]
  rw [hcv, hnest, hval]
  simp only [vpCst, wD, dispWt, QED.WickModel.Params.mass, QED.WickModel.Params.loopCoeff]

end QED.ChainProof.SetCMainB

end
