/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainDKLim
public import QED.TwoLoop.ReflCovarianceParam

/-!
# Set (c), the `δ₃` classes: the links of the longitudinal part

The open links `QED.ChainProof.SetCMain.DKLimLink`, `DKCovLink` of the longitudinal part of the
24 classes `repD i t`, and with them the class links `SetCClassLim`, `SetCClassCov` of `mainFam`
at `.inr (i, t)`.

* `dKValD_eq`: the longitudinal value at the set (c) data is `wKD` times the joint integral of
  `dKUnitIntegrandD` (`QED.ChainProof.SetCMain.dK_repD_value`);
* `kTerm_conj`: the parametric values of a term `kNum` at `(p, p')` and `(Lp, Lp')` are
  covariant (`QED.TwoLoop.ReflCovariance.conj_eq_vecAct_of_paramValue` with `kNum_map`);
* **`dkLimLink`**, **`dkCovLink`**: the two links, from `hasLimJ_dKUnit_int` (nine classes with
  an internal Ward vertex) and `hasLimJ_dKUnit_ext` (`i = 0, 6, 10`); the limit is a combination
  of parametric values with coefficients independent of the external momenta, so the limits at
  `(p', p)` and `(Lp', Lp)` are related term by term;
* **`setCClassLim_inr`**, **`setCClassCov_inr`**.
-/

@[expose] public section
open Complex Matrix Filter Topology
open QED.Dirac (vecAct)

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.Enumeration QED.ChainProof.SetCUnitM QED.TwoLoop.LimitCovariance
open QED.ChainProof.SetCPauli.CB01 (HasLimJ)
open QED.WickModel (Params)
open QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### Covariance of the terms -/

section Conj

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-- **Covariance of the parametric values of a term.** -/
theorem kTerm_conj (h : IsSpinLift L S T) (i : Fin 12) (R : Params) (hm : 0 < R.m)
    (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -R.m ^ 2)
    (hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -R.m ^ 2)
    (hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p)) {k : ℕ}
    (ι : Fin (k + 1) → Fin 10) (hk : 7 ≤ k) (Sl : Finset (Fin 10)) (hcrit : KCrit i ι Sl)
    (X Y : KSlot) (K : Finset (Fin 4)) (W W₂ : Fin 4 → Fin 4 → Fin 4 → ℂ)
    (hW : ∀ μ a b, IsParamValue (dkDi i R hm hγ hγΛ p p' hp hp' hq ι hk Sl hcrit)
      (fun ℓ => kNi i R p p' X Y K μ ℓ a b) (W μ a b))
    (hW₂ : ∀ μ a b, IsParamValue (dkDi i R hm hγ hγΛ (L *ᵥ p) (L *ᵥ p') hpL hpL' hqL ι hk Sl
      hcrit) (fun ℓ => kNi i R (L *ᵥ p) (L *ᵥ p') X Y K μ ℓ a b) (W₂ μ a b)) (μ : Fin 4) :
    S * Matrix.of (W₂ μ) * T = vecAct L (fun ν => Matrix.of (W ν)) μ :=
  QED.TwoLoop.ReflCovariance.conj_eq_vecAct_of_paramValue
    (dkDi i R hm hγ hγΛ p p' hp hp' hq ι hk Sl hcrit) h
    (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] (L *ᵥ p) (L *ᵥ p') (ι a))
    (funext fun a => congrFun (unitMMomenta_map _ _ _ p p') (ι a))
    (fun μ ℓ => kNi i R p p' X Y K μ ℓ) (fun μ ℓ => kNi i R (L *ᵥ p) (L *ᵥ p') X Y K μ ℓ)
    (fun μ ℓ => kNum_map (kPermD i) (repBClass i) (repBSlot i) R.m p p' X Y K μ h ℓ)
    (fun μ => Matrix.of (W μ)) (fun μ => Matrix.of (W₂ μ)) hW
    (fun μ a b => QED.TwoLoop.ReflCovariance.IsParamValue.exists_integrableOn (hW₂ μ a b)) μ

/-- Covariance of a combination of covariant families with fixed coefficients. -/
theorem dkConj_comb {n : ℕ} (coef : Fin n → ℂ) (W W₂ : Fin n → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hk : ∀ r μ, S * W₂ r μ * T = vecAct L (W r) μ) {Y Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ μ, Y μ = ∑ r, coef r • W r μ) (hZ : ∀ μ, Z μ = ∑ r, coef r • W₂ r μ) (μ : Fin 4) :
    S * Z μ * T = vecAct L Y μ := by
  rw [hZ, show Y = fun μ => ∑ r, coef r • W r μ from funext hY]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hk, vecAct,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun r _ => smul_comm _ _ _

end Conj

/-! ### The links -/

theorem kWard_cases : ∀ i : Fin 12, (∃ j : Fin 3, kWardD i = j.succ.castSucc) ∨ kWardD i = 4 := by
  decide

section Links

variable {P₀ : Params}

/-- The longitudinal value at the set (c) data in the class routing. -/
theorem dKValD_eq (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (s : ℝ × ℝ × ℝ) (i : Fin 12)
    (t : Fin 2) (p' p : Fin 4 → ℝ) (μ α β : Fin 4) (ε : ℝ) :
    dKValD P₀ M₁ M₂ c₁ c₂ mγ Λ D s i t p' p μ α β ε =
      wKD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) *
        QED.TwoLoop.jointEnergyFirstIntegral 2 (dKUnitIntegrandD i t
          (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (dkMasses (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)) ε p p' μ
          α β) :=
  dK_repD_value { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl rfl rfl rfl _ i t p p' μ α β

theorem tendsto_dKValD_of_hasLimJ {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    {i : Fin 12} {t : Fin 2} {p' p : Fin 4 → ℝ} {μ α β : Fin 4} {v : ℂ}
    (h : HasLimJ (fun ε => dKUnitIntegrandD i t (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (dkMasses (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)) ε p p' μ α β) v) :
    Tendsto (dKValD P₀ M₁ M₂ c₁ c₂ mγ Λ D s i t p' p μ α β) (𝓝[>] 0)
      (𝓝 (wKD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) * v)) :=
  (h.2.const_mul _).congr fun ε => (dKValD_eq P₀ M₁ M₂ c₁ c₂ mγ Λ D s i t p' p μ α β ε).symm

/-- **The limit link of the longitudinal part of `repD i t`.** -/
theorem dkLimLink (P₀ : Params) (i : Fin 12) (t : Fin 2) : DKLimLink P₀ i t := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ
  have key : ∀ μ α β, ∃ v, HasLimJ (fun ε => dKUnitIntegrandD i t R (dkMasses R) ε p p' μ α β)
      v := fun μ α β => by
    rcases kWard_cases i with ⟨j, hj⟩ | hW
    · obtain ⟨_, _, _, _, h⟩ := hasLimJ_dKUnit_int i t R hm hγ hγΛ p p' hp hp' hq.le j hj μ α β
      exact ⟨_, h⟩
    · obtain ⟨_, _, _, _, _, _, _, _, h⟩ :=
        hasLimJ_dKUnit_ext i t R hm hγ hγΛ p p' hp hp' hq.le hW μ α β
      exact ⟨_, h⟩
  choose v hv using key
  exact ⟨fun μ => Matrix.of fun α β => wKD R (P₀.e ^ 2 * (shareCt D s).d₃ 0) * v μ α β,
    fun μ α β => tendsto_dKValD_of_hasLimJ (hv μ α β)⟩

/-- **The covariance link of the longitudinal part of `repD i t`.** -/
theorem dkCovLink (P₀ : Params) (i : Fin 12) (t : Fin 2) : DKCovLink P₀ i t := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA L S T h p' p hpq h0 h1 Y Z hY hZ μ
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  obtain ⟨hpL', hpL, -, -, hqL⟩ := isPairQ_map h hpq h0 h1
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ
  set w := wKD R (P₀.e ^ 2 * (shareCt D s).d₃ 0)
  rcases kWard_cases i with ⟨j, hj⟩ | hW
  · choose w₁ w₂ hw₁ hw₂ hl using
      hasLimJ_dKUnit_int i t R hm hγ hγΛ p p' hp hp' hq.le j hj
    choose u₁ u₂ hu₁ hu₂ hu using
      hasLimJ_dKUnit_int i t R hm hγ hγΛ (L *ᵥ p) (L *ᵥ p') hpL hpL' hqL.le j hj
    set c := w * (kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ))
    refine dkConj_comb ![c, -c] ![fun μ => Matrix.of (w₁ μ), fun μ => Matrix.of (w₂ μ)]
      ![fun μ => Matrix.of (u₁ μ), fun μ => Matrix.of (u₂ μ)] (fun r μ => ?_) (fun μ => ?_)
      (fun μ => ?_) μ
    · fin_cases r
      · exact kTerm_conj h i R hm hγ hγΛ hp hp' hq.le hpL hpL' hqL.le _ _ _ _ _ _ _ _ _
          hw₁ hu₁ μ
      · exact kTerm_conj h i R hm hγ hγΛ hp hp' hq.le hpL hpL' hqL.le _ _ _ _ _ _ _ _ _
          hw₂ hu₂ μ
    · ext α β
      rw [tendsto_nhds_unique (hY μ α β) (tendsto_dKValD_of_hasLimJ (hl μ α β))]
      simp [Fin.sum_univ_two, c]
      ring
    · ext α β
      rw [tendsto_nhds_unique (hZ μ α β) (tendsto_dKValD_of_hasLimJ (hu μ α β))]
      simp [Fin.sum_univ_two, c]
      ring
  · choose w₀ w₁ w₂ w₃ hw₀ hw₁ hw₂ hw₃ hl using
      hasLimJ_dKUnit_ext i t R hm hγ hγΛ p p' hp hp' hq.le hW
    choose u₀ u₁ u₂ u₃ hu₀ hu₁ hu₂ hu₃ hu using
      hasLimJ_dKUnit_ext i t R hm hγ hγΛ (L *ᵥ p) (L *ᵥ p') hpL hpL' hqL.le hW
    set c := w * (kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ)))
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
      rw [tendsto_nhds_unique (hY μ α β) (tendsto_dKValD_of_hasLimJ (hl μ α β))]
      simp [Fin.sum_univ_four, c]
      ring
    · ext α β
      rw [tendsto_nhds_unique (hZ μ α β) (tendsto_dKValD_of_hasLimJ (hu μ α β))]
      simp [Fin.sum_univ_four, c]
      ring

/-- **The limit link of `repD i t`.** -/
theorem setCClassLim_inr (P₀ : Params) (i : Fin 12) (t : Fin 2) :
    SetCClassLim mainFam P₀ (.inr (i, t)) :=
  setCClassLim_inr_of_dK (dkLimLink P₀ i t)

/-- **The covariance link of `repD i t`.** -/
theorem setCClassCov_inr (P₀ : Params) (i : Fin 12) (t : Fin 2) :
    SetCClassCov mainFam P₀ (.inr (i, t)) :=
  setCClassCov_inr_of_dK (dkCovLink P₀ i t)

end Links

end QED.ChainProof.SetCMain

end
