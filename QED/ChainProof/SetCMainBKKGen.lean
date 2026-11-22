/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMAbsFub
public import QED.ChainProof.SetCLimCtCB01Lim

/-!
# Set (c), the bubble classes: a graph with one spectral line, uniformly in the scale

Helper level for the open link `QED.ChainProof.SetCMainB.MainBKKLink` (the longitudinal
dispersive part of the twelve bubble classes `repB i`). After the Ward identities of
`QED/ChainProof/SetCMainDKLim.lean`, every term of that part is a two-loop graph `G` (lines `α`,
`p`, masses `M`, a quartic numerator `Q` with the refined bound on the lines `E`) times the
spectral line `κ² k² + t² - iε` of the inserted bubble, `k` the momentum of a line `j₀ ∉ E` of
`G` and `κ² = x(1-x)`. This file proves, for any such graph, the facts the transverse chain
(`QED/ChainProof/SetCUnitMDispEps.lean`, `SetCUnitMAbsDisp.lean`, `SetCUnitMAbsFub.lean`) proves
for the transverse unit, with the numerator and the graph as parameters.

* `kkRho`, `kkSig`, `kkInt`: the graph with the spectral line as the new line `0`, a copy of
  `j₀` rescaled by `κ`; **`kkInt_eq`**: the integrand is that of `G` times the spectral factor;
* **`norm_kkInt_light_le`**: the rescaled-line bound `κ⁻² C` (the doubled graph);
* **`kkInt_pf`**: the partial fraction against the line `j₀` at fixed `ε ≠ 0`;
* **`exists_norm_kkInt_le`**: the value is bounded uniformly in `κ ∈ (0, 1]` and `ε > 0`;
* **`exists_absL1_kkInt_le`**: at fixed `ε`, the spatial `L¹` norm uniformly in `κ ∈ (0, 1]`;
* **`tendsto_kkInt`**: the `ε → 0⁺` limit at a fixed scale (parametric data of the engine);
* `continuous_kkInt`, `integrable_kkInt_energy`, `integrableOn_kkInt`;
  **`jointEnergyFirstIntegral_setIntegral_kkInt`**: the `x`-Fubini for a weight `w`;
  **`tendsto_setIntegral_kkInt`**: dominated convergence in `x`;
* `KKLim` (a family with a dispersive limit) and its closure under sums, coefficients with a
  limit and pointwise congruence; **`kkLim_kkInt`**: every graph with the spectral line is one.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCUnitM
open QED.Integration.TwoLoop (symanzikU symanzikV LoopQuartic NoSubdivergenceRefined
  RefinedBound lineDenom lineMomentum
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined)
open QED.Integration.Feynman (simplexSet)

section Gen

variable {m : ℕ}

/-- The line map of the graph with the line `j₀` doubled: the new line `0` is a copy of `j₀`. -/
def kkRho (j₀ : Fin (m + 1)) : Fin (m + 1 + 1) → Fin (m + 1) := Fin.cons j₀ id

/-- The scales: `κ` on the new line `0`, `1` on the others. -/
def kkSig (κ : ℝ) : Fin (m + 1 + 1) → ℝ := Fin.cons κ 1

@[simp] theorem kkRho_zero (j₀ : Fin (m + 1)) : kkRho j₀ 0 = j₀ := rfl

@[simp] theorem kkRho_succ (j₀ : Fin (m + 1)) (k : Fin (m + 1)) : kkRho j₀ k.succ = k := by
  simp [kkRho]

@[simp] theorem kkSig_zero (κ : ℝ) : kkSig (m := m) κ 0 = κ := rfl

@[simp] theorem kkSig_succ (κ : ℝ) (k : Fin (m + 1)) : kkSig κ k.succ = 1 := by
  simp [kkSig]

theorem kkSig_ne_zero {κ : ℝ} (hκ : κ ≠ 0) (k : Fin (m + 1 + 1)) : kkSig κ k ≠ 0 := by
  refine Fin.cases ?_ (fun k => ?_) k
  · simpa using hκ
  · simp

variable (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (j₀ : Fin (m + 1))
  (Q : LoopQuartic) (M : Fin (m + 1) → ℝ)

/-- **The graph `G` with the spectral line**: the new line `0` is the line `j₀` with momentum
`κ k` and mass `t`, so its denominator is `κ² k² + t² - iε`. -/
noncomputable def kkInt (κ t ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  Q.eval ℓ * ∏ k, (lineDenom (fun k => kkSig κ k • α (kkRho j₀ k))
    (fun k => kkSig κ k • p (kkRho j₀ k)) (Fin.cons t M) ε k ℓ)⁻¹

/-- The squared momentum of the line `j₀`. -/
noncomputable abbrev kkK (ℓ : Fin 2 → Fin 4 → ℝ) : ℝ :=
  Minkowski.dot (lineMomentum α p j₀ ℓ) (lineMomentum α p j₀ ℓ)

theorem lineDenom_kk_succ (κ t ε : ℝ) (k : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (fun k => kkSig κ k • α (kkRho j₀ k)) (fun k => kkSig κ k • p (kkRho j₀ k))
      (Fin.cons t M) ε k.succ ℓ = lineDenom α p M ε k ℓ :=
  lineDenom_congr (by simp) (by simp) (by simp) ε ℓ

theorem lineDenom_kk_zero (κ t ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (fun k => kkSig κ k • α (kkRho j₀ k)) (fun k => kkSig κ k • p (kkRho j₀ k))
      (Fin.cons t M : Fin (m + 1 + 1) → ℝ) ε 0 ℓ =
      ((κ ^ 2 * kkK α p j₀ ℓ + t ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I := by
  rw [lineDenom_scale]
  rfl

/-- **The integrand** is that of `G` times the spectral factor `(κ² k² + t² - iε)⁻¹`. -/
theorem kkInt_eq (κ t ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkInt α p j₀ Q M κ t ε ℓ = Q.eval ℓ * (∏ k, (lineDenom α p M ε k ℓ)⁻¹) *
      (((κ ^ 2 * kkK α p j₀ ℓ + t ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ := by
  unfold kkInt
  rw [Fin.prod_univ_succ, lineDenom_kk_zero]
  simp only [lineDenom_kk_succ]
  ring

/-- The graph `G` with the line `j₀` rescaled by `κ`, of entry mass `a` (mass `κ a`). -/
noncomputable def kkScaled (κ a ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  Q.eval ℓ * ∏ k, (lineDenom (fun k => Function.update (1 : Fin (m + 1) → ℝ) j₀ κ k • α k)
    (fun k => Function.update (1 : Fin (m + 1) → ℝ) j₀ κ k • p k)
    (fun k => Function.update (1 : Fin (m + 1) → ℝ) j₀ κ k * Function.update M j₀ a k) ε k ℓ)⁻¹

/-- The integrand of the graph `G`. -/
noncomputable def kkG (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  Q.eval ℓ * ∏ k, (lineDenom α p M ε k ℓ)⁻¹

theorem kkScaled_one (a ε : ℝ) (ha : a = M j₀) : kkScaled α p j₀ Q M 1 a ε = kkG α p Q M ε := by
  have e1 : Function.update (1 : Fin (m + 1) → ℝ) j₀ 1 = 1 := by simp
  subst ha
  funext ℓ
  simp only [kkScaled, kkG, e1, Function.update_eq_self, Pi.one_apply, one_smul, one_mul]

/-! ### The engine hypotheses for the doubled and the rescaled graphs -/

variable {α p j₀ Q M} {E : Finset (Fin (m + 1))}

theorem kk_crit (hcrit : NoSubdivergenceRefined 2 E α) {κ : ℝ} (hκ : κ ≠ 0) :
    NoSubdivergenceRefined 2 (E.map (Fin.succEmb (m + 1)))
      (fun k => kkSig κ k • α (kkRho j₀ k)) :=
  noSubdivergenceRefined_scale_comp hcrit (kkRho j₀) (Fin.succEmb (m + 1)) (fun j => by simp)
    (kkSig κ) (kkSig_ne_zero hκ)

theorem kk_crit_one (hcrit : NoSubdivergenceRefined 2 E α) :
    NoSubdivergenceRefined 2 (E.map (Fin.succEmb (m + 1))) (fun k => α (kkRho j₀ k)) := by
  have h := noSubdivergenceRefined_scale_comp hcrit (kkRho j₀) (Fin.succEmb (m + 1))
    (fun j => by simp) (fun _ => (1 : ℝ)) (fun _ => one_ne_zero)
  simpa using h

theorem kk_bound (hB : RefinedBound α E 4 Q.eval) {σ : Fin (m + 1 + 1) → ℝ}
    (hσ : ∀ k : Fin (m + 1), σ k.succ = 1) :
    RefinedBound (fun k => σ k • α (kkRho j₀ k)) (E.map (Fin.succEmb (m + 1))) 4 Q.eval :=
  refinedBound_map (Fin.succEmb (m + 1)) (fun e _ => by simp [hσ e]) hB

theorem zero_not_mem_kkE : (0 : Fin (m + 1 + 1)) ∉ E.map (Fin.succEmb (m + 1)) := by
  simp [Fin.succ_ne_zero]

/-- `V` of the doubled graph, the new line of mass `a ≥ μ₀`, from `V` of `G` with any mass
`≥ μ₀` on the line `j₀`. -/
theorem kk_symanzikV_ge {μ₀ c : ℝ} (hM0 : μ₀ ≤ M j₀)
    (hV : ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α p (Function.update M j₀ a) z)
    {a : ℝ} (ha : μ₀ ≤ a) (hμ₀ : 0 ≤ μ₀) {z : Fin (m + 1 + 1) → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hz1 : ∑ i, z i = 1) (hU : symanzikU (fun k => α (kkRho j₀ k)) z ≠ 0) :
    c ≤ symanzikV (fun k => α (kkRho j₀ k)) (fun k => p (kkRho j₀ k))
      (Fin.cons a M) z := by
  refine QED.Integration.TwoLoop.le_symanzikV_comp_of (σ := kkRho j₀)
    (hV (min a (M j₀)) (le_min ha hM0)) (fun i => ?_) hz hz1 hU
  have h0 : 0 ≤ min a (M j₀) := hμ₀.trans (le_min ha hM0)
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [kkRho_zero, Function.update_self, Fin.cons_zero]
    exact pow_le_pow_left₀ h0 (min_le_left _ _) 2
  · simp only [kkRho_succ, Fin.cons_succ]
    by_cases hj : j = j₀
    · subst hj
      simp only [Function.update_self]
      exact pow_le_pow_left₀ h0 (min_le_right _ _) 2
    · rw [Function.update_of_ne hj]

/-! ### The value bounds -/

variable (hm : 7 ≤ m) (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval)
  {μ₀ c : ℝ} (hμ₀ : 0 < μ₀) (hc : 0 < c) (hM0 : μ₀ ≤ M j₀)
  (hV : ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
    symanzikU α z ≠ 0 → c ≤ symanzikV α p (Function.update M j₀ a) z) (hj₀ : j₀ ∉ E)
include hm hcrit hB hμ₀ hc hM0 hV hj₀

omit hj₀ in
/-- **The rescaled-line bound** (light dispersion mass): one constant `C` with
`‖∫ kkInt‖ ≤ κ⁻² C` for `κ ∈ (0, 1]`, `t ≥ μ₀` and `ε > 0`. -/
theorem norm_kkInt_light_le : ∃ C : ℝ, ∀ κ t ε : ℝ, 0 < κ → κ ≤ 1 → μ₀ ≤ t → 0 < ε →
    ‖QED.TwoLoop.jointEnergyFirstIntegral 2 (kkInt α p j₀ Q M κ t ε)‖ ≤ (κ ^ 2)⁻¹ * C := by
  refine ⟨π ^ 4 * ∫ x in simplexSet (m + 1), QED.ChainProof.SetCUnit.domFun Q
    (fun k => α (kkRho j₀ (Equiv.swap (Fin.castSucc (⟨0, by omega⟩ : Fin (m + 1))) 0 k)))
    (fun k => p (kkRho j₀ (Equiv.swap (Fin.castSucc (⟨0, by omega⟩ : Fin (m + 1))) 0 k))) c x,
    fun κ t ε hκ hκ1 ht hε => ?_⟩
  have htκ : μ₀ ≤ t / κ := ht.trans (le_div_self (hμ₀.le.trans ht) hκ hκ1)
  have h := norm_jointEnergyFirstIntegral_scale_le' (m := m + 1) (Q := Q)
    (α := fun k => α (kkRho j₀ k)) (p := fun k => p (kkRho j₀ k))
    (M := (Fin.cons (t / κ) M : Fin (m + 1 + 1) → ℝ)) (by omega) (kk_crit_one hcrit)
    (by simpa using kk_bound (j₀ := j₀) hB (σ := fun _ => 1) (fun _ => rfl)) hc
    (fun z hz hz1 hU => kk_symanzikV_ge hM0 hV htκ hμ₀.le hz hz1 hU) zero_not_mem_kkE hκ.ne'
    (σ := kkSig κ) (kkSig_zero κ) (fun k hk => by
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hk
      exact kkSig_succ κ j) hε
  have eM : (fun k => kkSig κ k * (Fin.cons (t / κ) M : Fin (m + 1 + 1) → ℝ) k) =
      (Fin.cons t M : Fin (m + 1 + 1) → ℝ) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [kkSig_zero, Fin.cons_zero]
      field_simp
    · simp
  rw [eM] at h
  exact h

omit hμ₀ hM0 in
/-- **The graph `G` with the line `j₀` rescaled**, bounded by `κ⁻² C` uniformly in the mass
`t/κ ≥ μ₀` of the unscaled line and in `ε`. -/
theorem norm_kkScaled_le : ∃ C : ℝ, ∀ κ a ε : ℝ, κ ≠ 0 → μ₀ ≤ a → 0 < ε →
    ‖QED.TwoLoop.jointEnergyFirstIntegral 2 (kkScaled α p j₀ Q M κ a ε)‖ ≤ (κ ^ 2)⁻¹ * C := by
  refine ⟨π ^ 4 * ∫ x in simplexSet m, QED.ChainProof.SetCUnit.domFun Q
    (fun k => α (Equiv.swap (Fin.castSucc (⟨0, by omega⟩ : Fin m)) j₀ k))
    (fun k => p (Equiv.swap (Fin.castSucc (⟨0, by omega⟩ : Fin m)) j₀ k)) c x,
    fun κ a ε hκ ha hε => ?_⟩
  exact norm_jointEnergyFirstIntegral_scale_le' hm hcrit hB hc (hV a ha) hj₀ hκ
    (Function.update_self _ _ _) (fun k hk => Function.update_of_ne hk _ _) hε

omit hm hcrit hB hμ₀ hc hM0 hV hj₀ in
/-- **Partial fractions against the line `j₀`** at fixed `ε ≠ 0`: with `u = M j₀`,
`kkInt = c⁻¹ (κ² F₁ - F₂)`, `c = κ² u² - t² + iε(1 - κ²)`, `F₁` the graph `G` with the line `j₀`
rescaled by `κ` and of mass `t` (entry `t/κ`), `F₂` the graph `G`. -/
theorem kkInt_pf {κ t ε : ℝ} (hκ : κ ≠ 0) (hε : ε ≠ 0) (hcc : κ ^ 2 * M j₀ ^ 2 ≠ t ^ 2) :
    kkInt α p j₀ Q M κ t ε = fun ℓ => (pfConst κ (M j₀) t ε)⁻¹ *
      (((κ ^ 2 : ℝ) : ℂ) * kkScaled α p j₀ Q M κ (t / κ) ε ℓ - kkG α p Q M ε ℓ) := by
  funext ℓ
  rw [kkInt_eq]
  unfold kkScaled kkG
  set X := ∏ k ∈ Finset.univ.erase j₀, (lineDenom α p M ε k ℓ)⁻¹
  have h1 : ∏ k, (lineDenom α p M ε k ℓ)⁻¹ = (lineDenom α p M ε j₀ ℓ)⁻¹ * X :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j₀)).symm
  have h2 : ∏ k, (lineDenom (fun k => Function.update (1 : Fin (m + 1) → ℝ) j₀ κ k • α k)
      (fun k => Function.update (1 : Fin (m + 1) → ℝ) j₀ κ k • p k)
      (fun k => Function.update (1 : Fin (m + 1) → ℝ) j₀ κ k * Function.update M j₀ (t / κ) k)
        ε k ℓ)⁻¹ = (((κ ^ 2 * kkK α p j₀ ℓ + t ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ * X := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀)]
    congr 1
    · rw [lineDenom_scale]
      simp only [Function.update_self]
      rw [mul_div_cancel₀ _ hκ]
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hk' := Finset.ne_of_mem_erase hk
      refine congrArg Inv.inv (lineDenom_congr ?_ ?_ ?_ ε ℓ)
      · simp [Function.update_of_ne hk']
      · simp [Function.update_of_ne hk']
      · simp [Function.update_of_ne hk']
  have hD : lineDenom α p M ε j₀ ℓ = ((kkK α p j₀ ℓ + M j₀ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I := rfl
  rw [h1, h2, hD, mul_assoc]
  exact pf_alg_scaled hε hcc _ _

/-- **The value with the spectral line, uniformly in the scale and in `ε`**: for a fixed mass
`t ≥ μ₀` one constant `C` with `‖∫ kkInt‖ ≤ C` for all `κ ∈ (0, 1]` and `ε > 0`. Light
dispersion mass (`t² < 2 κ² u²`, `u = M j₀`): the rescaled-line bound, `κ⁻² < 2 u² / t²`;
heavy: the partial fraction `kkInt_pf`, `|c| ≥ t²/2`. -/
theorem exists_norm_kkInt_le {t : ℝ} (ht : μ₀ ≤ t) : ∃ C : ℝ, ∀ κ ε : ℝ, 0 < κ → κ ≤ 1 →
    0 < ε → ‖QED.TwoLoop.jointEnergyFirstIntegral 2 (kkInt α p j₀ Q M κ t ε)‖ ≤ C := by
  obtain ⟨CB, hCB⟩ := norm_kkInt_light_le hm hcrit hB hμ₀ hc hM0 hV
  obtain ⟨CG, hCG⟩ := norm_kkScaled_le hm hcrit hB hc hV hj₀
  set u := M j₀ with hu
  have ht0 : 0 < t := hμ₀.trans_le ht
  have ht2 : 0 < t ^ 2 := by positivity
  refine ⟨2 * u ^ 2 / t ^ 2 * |CB| + 2 / t ^ 2 * (|CG| + |CG|), fun κ ε hκ hκ1 hε => ?_⟩
  have hC0 : 0 ≤ 2 * u ^ 2 / t ^ 2 * |CB| := by positivity
  have hC1 : 0 ≤ 2 / t ^ 2 * (|CG| + |CG|) := by positivity
  by_cases hcase : 2 * (κ ^ 2 * u ^ 2) ≤ t ^ 2
  · -- heavy dispersion mass: partial fractions
    have hcc : κ ^ 2 * u ^ 2 ≠ t ^ 2 := by intro h; nlinarith
    have htκ : μ₀ ≤ t / κ := ht.trans (le_div_self ht0.le hκ hκ1)
    rw [kkInt_pf hκ.ne' hε.ne' hcc]
    have hσ0 : ∀ k, Function.update (1 : Fin (m + 1) → ℝ) j₀ κ k ≠ 0 := fun k => by
      by_cases hk : k = j₀
      · subst hk; simpa using hκ.ne'
      · simp [Function.update_of_ne hk]
    have hJ1 := jointEnergyFirstIntegrable_lineScale (p := p) hm hcrit hB hσ0
      (fun e he => Function.update_of_ne (fun h : e = j₀ => hj₀ (h ▸ he)) _ _)
      (fun k => Function.update (1 : Fin (m + 1) → ℝ) j₀ κ k * Function.update M j₀ (t / κ) k) hε
    have hJ2 := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
      Q α p M hm hε hcrit hB
    set k := pfConst κ u t ε
    have hlin := jointEnergyFirstIntegrable_mul_add_mul (F := kkScaled α p j₀ Q M κ (t / κ) ε)
      (G := kkG α p Q M ε) hJ1 hJ2 (k⁻¹ * ((κ ^ 2 : ℝ) : ℂ)) (-k⁻¹)
    have e : (fun ℓ => k⁻¹ * (((κ ^ 2 : ℝ) : ℂ) * kkScaled α p j₀ Q M κ (t / κ) ε ℓ -
        kkG α p Q M ε ℓ)) = fun ℓ => k⁻¹ * ((κ ^ 2 : ℝ) : ℂ) * kkScaled α p j₀ Q M κ (t / κ) ε ℓ +
          -k⁻¹ * kkG α p Q M ε ℓ := funext fun ℓ => by ring
    rw [e, hlin.2]
    have hJb := hCG κ (t / κ) ε hκ.ne' htκ hε
    have hBb := hCG 1 u ε one_ne_zero hM0 hε
    rw [kkScaled_one α p j₀ Q M u ε hu, one_pow, inv_one, one_mul] at hBb
    have hkn : t ^ 2 / 2 ≤ ‖k‖ := by
      refine le_trans ?_ (abs_re_le_norm_pfConst κ u t ε)
      rw [abs_of_neg (by nlinarith)]
      linarith
    have hk0 : 0 < ‖k‖ := lt_of_lt_of_le (by positivity) hkn
    have hκ2 : (0 : ℝ) < κ ^ 2 := by positivity
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hκ2.le]
    have hb1 : κ ^ 2 * ‖QED.TwoLoop.jointEnergyFirstIntegral 2
        (kkScaled α p j₀ Q M κ (t / κ) ε)‖ ≤ |CG| := by
      calc _ ≤ κ ^ 2 * ((κ ^ 2)⁻¹ * CG) := mul_le_mul_of_nonneg_left hJb hκ2.le
        _ = CG := by field_simp
        _ ≤ |CG| := le_abs_self _
    have hb2 := hBb.trans (le_abs_self CG)
    have hki : ‖k‖⁻¹ ≤ 2 / t ^ 2 := by
      rw [inv_le_comm₀ hk0 (by positivity), inv_div]; exact hkn
    calc ‖k‖⁻¹ * κ ^ 2 * ‖QED.TwoLoop.jointEnergyFirstIntegral 2
            (kkScaled α p j₀ Q M κ (t / κ) ε)‖ +
          ‖k‖⁻¹ * ‖QED.TwoLoop.jointEnergyFirstIntegral 2 (kkG α p Q M ε)‖
        = ‖k‖⁻¹ * (κ ^ 2 * ‖QED.TwoLoop.jointEnergyFirstIntegral 2
            (kkScaled α p j₀ Q M κ (t / κ) ε)‖ +
          ‖QED.TwoLoop.jointEnergyFirstIntegral 2 (kkG α p Q M ε)‖) := by ring
      _ ≤ 2 / t ^ 2 * (|CG| + |CG|) :=
          mul_le_mul hki (add_le_add hb1 hb2) (by positivity) (by positivity)
      _ ≤ _ := le_add_of_nonneg_left hC0
  · -- light dispersion mass: the rescaled-line bound and `κ⁻² ≤ 2 u² / t²`
    push Not at hcase
    refine (hCB κ t ε hκ hκ1 ht hε).trans ?_
    have hκinv : (κ ^ 2)⁻¹ ≤ 2 * u ^ 2 / t ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ ht2]
      nlinarith
    calc (κ ^ 2)⁻¹ * CB ≤ (κ ^ 2)⁻¹ * |CB| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ 2 * u ^ 2 / t ^ 2 * |CB| := mul_le_mul_of_nonneg_right hκinv (abs_nonneg _)
      _ ≤ _ := le_add_of_nonneg_right hC1

/-! ### The spatial `L¹` norm at fixed `ε` -/

omit hμ₀ hc hM0 hV in
/-- **The spatial `L¹` norm with the spectral line, uniformly in the scale**: for a fixed mass
`t > 0` and fixed `ε > 0`, one constant `C` with both stages integrable and
`∫ d⁶v |∫ dt kkInt| ≤ C` for all `κ ∈ (0, 1]` (as `exists_norm_kkInt_le`, with the rescaled-line
`L¹` bound `integral_norm_energyIntegral_scale_le'`). -/
theorem exists_absL1_kkInt_le (hE : E.card + 4 ≤ m + 1) {t : ℝ} (ht : 0 < t) {ε : ℝ}
    (hε : 0 < ε) : ∃ C : ℝ, ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (kkInt α p j₀ Q M κ t ε) ∧
        absL1 (kkInt α p j₀ Q M κ t ε) ≤ C := by
  have hEB : (E.map (Fin.succEmb (m + 1))).card + 4 ≤ m + 1 + 1 := by
    rw [Finset.card_map]; omega
  obtain ⟨C₃, -, hC₃⟩ := integral_norm_energyIntegral_scale_le' (m := m + 1) Q
    (fun k => α (kkRho j₀ k)) (fun k => p (kkRho j₀ k)) (by omega) (kk_crit_one hcrit)
    (by simpa using kk_bound (j₀ := j₀) hB (σ := fun _ => 1) (fun _ => rfl)) hEB
    zero_not_mem_kkE (K := ∑ i, ((Fin.cons t M : Fin (m + 1 + 1) → ℝ) i ^ 2 +
      ∑ μ, p (kkRho j₀ i) μ ^ 2)) le_rfl hε
  obtain ⟨C₁, -, hC₁⟩ := integral_norm_energyIntegral_scale_le' Q α p hm hcrit hB hE hj₀
    (K := ∑ i, (Function.update M j₀ t i ^ 2 + ∑ μ, p i μ ^ 2)) le_rfl hε
  obtain ⟨C₂, -, hC₂⟩ := integral_norm_energyIntegral_scale_le' Q α p hm hcrit hB hE hj₀
    (K := ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2)) le_rfl hε
  set u := M j₀ with hu
  have ht2 : 0 < t ^ 2 := by positivity
  refine ⟨2 * u ^ 2 / t ^ 2 * |C₃| + 2 / t ^ 2 * (|C₁| + |C₂|), fun κ hκ hκ1 => ?_⟩
  have hC0 : 0 ≤ 2 * u ^ 2 / t ^ 2 * |C₃| := by positivity
  have hC1 : 0 ≤ 2 / t ^ 2 * (|C₁| + |C₂|) := by positivity
  -- the light bound, valid for every `κ`
  obtain ⟨h31, h32, h33⟩ := hC₃ κ (kkSig κ) (Fin.cons t M) hκ hκ1 (kkSig_zero κ)
    (fun k hk => by obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hk; exact kkSig_succ κ j) le_rfl
  have hI : QED.TwoLoop.jointEnergyFirstIntegrable 2 (kkInt α p j₀ Q M κ t ε) := ⟨h31, h32⟩
  refine ⟨hI, ?_⟩
  have hL : absL1 (kkInt α p j₀ Q M κ t ε) ≤ (κ ^ 2)⁻¹ * C₃ := h33
  by_cases hcase : 2 * (κ ^ 2 * u ^ 2) ≤ t ^ 2
  · -- heavy dispersion mass: partial fractions
    have hcc : κ ^ 2 * u ^ 2 ≠ t ^ 2 := by intro h; nlinarith
    have eM : ∀ k, Function.update (1 : Fin (m + 1) → ℝ) j₀ κ k *
        Function.update M j₀ (t / κ) k = Function.update M j₀ t k := fun k => by
      by_cases hk : k = j₀
      · subst hk; simp only [Function.update_self]; field_simp
      · simp [Function.update_of_ne hk]
    obtain ⟨h11, h12, h13⟩ := hC₁ κ (Function.update 1 j₀ κ)
      (fun k => Function.update (1 : Fin (m + 1) → ℝ) j₀ κ k * Function.update M j₀ (t / κ) k)
      hκ hκ1 (Function.update_self _ _ _) (fun k hk => Function.update_of_ne hk _ _)
      (by simp only [eM]; exact le_rfl)
    obtain ⟨h21, h22, h23⟩ := hC₂ 1 (Function.update 1 j₀ 1) M one_pos le_rfl
      (Function.update_self _ _ _) (fun k hk => Function.update_of_ne hk _ _) le_rfl
    have e1 : Function.update (1 : Fin (m + 1) → ℝ) j₀ 1 = 1 := by simp
    simp only [e1, Pi.one_apply, one_smul, one_pow, inv_one, one_mul] at h21 h22 h23
    have hJ1 : QED.TwoLoop.jointEnergyFirstIntegrable 2 (kkScaled α p j₀ Q M κ (t / κ) ε) :=
      ⟨h11, h12⟩
    have hJ2 : QED.TwoLoop.jointEnergyFirstIntegrable 2 (kkG α p Q M ε) := ⟨h21, h22⟩
    have hL1 : absL1 (kkScaled α p j₀ Q M κ (t / κ) ε) ≤ (κ ^ 2)⁻¹ * C₁ := h13
    have hL2 : absL1 (kkG α p Q M ε) ≤ C₂ := h23
    set k := pfConst κ u t ε
    have e : kkInt α p j₀ Q M κ t ε = fun ℓ => k⁻¹ * ((κ ^ 2 : ℝ) : ℂ) *
        kkScaled α p j₀ Q M κ (t / κ) ε ℓ + -k⁻¹ * kkG α p Q M ε ℓ := by
      rw [kkInt_pf hκ.ne' hε.ne' hcc]
      funext ℓ; ring
    have hkn : t ^ 2 / 2 ≤ ‖k‖ := by
      refine le_trans ?_ (abs_re_le_norm_pfConst κ u t ε)
      rw [abs_of_neg (by nlinarith)]
      linarith
    have hk0 : 0 < ‖k‖ := lt_of_lt_of_le (by positivity) hkn
    have hκ2 : (0 : ℝ) < κ ^ 2 := by positivity
    have hki : ‖k‖⁻¹ ≤ 2 / t ^ 2 := by
      rw [inv_le_comm₀ hk0 (by positivity), inv_div]; exact hkn
    rw [e]
    refine (absL1_mul_add_mul_le hJ1 hJ2 _ _).trans ?_
    rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hκ2.le]
    have hb1 : κ ^ 2 * absL1 (kkScaled α p j₀ Q M κ (t / κ) ε) ≤ |C₁| := by
      calc _ ≤ κ ^ 2 * ((κ ^ 2)⁻¹ * C₁) := mul_le_mul_of_nonneg_left hL1 hκ2.le
        _ = C₁ := by field_simp
        _ ≤ |C₁| := le_abs_self _
    calc ‖k‖⁻¹ * κ ^ 2 * absL1 (kkScaled α p j₀ Q M κ (t / κ) ε) +
          ‖k‖⁻¹ * absL1 (kkG α p Q M ε)
        = ‖k‖⁻¹ * (κ ^ 2 * absL1 (kkScaled α p j₀ Q M κ (t / κ) ε) +
          absL1 (kkG α p Q M ε)) := by ring
      _ ≤ 2 / t ^ 2 * (|C₁| + |C₂|) :=
          mul_le_mul hki (add_le_add hb1 (hL2.trans (le_abs_self _)))
            (add_nonneg (mul_nonneg hκ2.le (absL1_nonneg _)) (absL1_nonneg _)) (by positivity)
      _ ≤ _ := le_add_of_nonneg_left hC0
  · push Not at hcase
    refine hL.trans ?_
    have hκinv : (κ ^ 2)⁻¹ ≤ 2 * u ^ 2 / t ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ ht2]
      nlinarith
    calc (κ ^ 2)⁻¹ * C₃ ≤ (κ ^ 2)⁻¹ * |C₃| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ 2 * u ^ 2 / t ^ 2 * |C₃| := mul_le_mul_of_nonneg_right hκinv (abs_nonneg _)
      _ ≤ _ := le_add_of_nonneg_right hC1

/-! ### The limit at a fixed scale -/

omit hj₀ in
/-- **The `ε → 0⁺` limit at a fixed scale** `κ ∈ (0, 1]`, for `t ≥ μ₀` and `c ≤ μ₀²`: the graph
with the spectral line is parametric data of the engine (criterion by
`noSubdivergenceRefined_scale_comp`, `V ≥ c` by `le_symanzikV_scale_comp_of`). -/
theorem tendsto_kkInt (hcμ : c ≤ μ₀ ^ 2) {κ t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ht : μ₀ ≤ t) :
    ∃ L : ℂ, Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (kkInt α p j₀ Q M κ t ε))
      (𝓝[>] 0) (𝓝 L) := by
  have hVs : ∀ z : Fin (m + 1 + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (fun k => kkSig κ k • α (kkRho j₀ k)) z ≠ 0 →
      c ≤ symanzikV (fun k => kkSig κ k • α (kkRho j₀ k)) (fun k => kkSig κ k • p (kkRho j₀ k))
        (Fin.cons t M) z := fun z hz hz1 hU =>
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
  let D : QED.TwoLoop.LimitCovariance.ParamData :=
    { m := m + 1, α := fun k => kkSig κ k • α (kkRho j₀ k),
      p := fun k => kkSig κ k • p (kkRho j₀ k), M := Fin.cons t M,
      E := E.map (Fin.succEmb (m + 1)), hm := by omega, hcrit := kk_crit hcrit hκ.ne', c := c,
      hc := hc, hV := hVs }
  have hP : QED.TwoLoop.LimitCovariance.IsParamValue D Q.eval
      (-((π : ℂ) ^ 4) * ∫ x in simplexSet D.m,
        QED.TwoLoop.ClassLimit.paramIntegrand Q D.α D.p D.M 0 x) :=
    ⟨Q, rfl, kk_bound hB (kkSig_succ κ), rfl⟩
  exact ⟨_, hP.tendsto⟩

end Gen

/-! ### The Feynman parameter: continuity, the `x`-Fubini and dominated convergence -/

section Param

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {p : Fin (m + 1) → Fin 4 → ℝ} {j₀ : Fin (m + 1)}
  {Q : LoopQuartic} {M : Fin (m + 1) → ℝ} {kx : ℝ → ℝ}

theorem continuous_kkSig_apply (hkx : Continuous kx) (k : Fin (m + 1 + 1)) :
    Continuous fun x => kkSig (kx x) k := by
  cases k using Fin.cases with
  | zero => simpa using hkx
  | succ j => simpa using continuous_const

/-- The integrand with the spectral line is jointly continuous in the Feynman parameter and the
loop momenta at every `ε ≠ 0`. -/
theorem continuous_kkInt (hkx : Continuous kx) (t : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    Continuous fun q : ℝ × (Fin 2 → Fin 4 → ℝ) => kkInt α p j₀ Q M (kx q.1) t ε q.2 := by
  unfold kkInt
  refine (Q.continuous_eval.comp continuous_snd).mul (continuous_finsetProd _ fun k _ => ?_)
  exact continuous_inv_lineDenom_scale (fun x => kkSig (kx x)) (continuous_kkSig_apply hkx)
    (fun k => α (kkRho j₀ k)) (fun k => p (kkRho j₀ k)) (Fin.cons t M) hε k

/-- Dropping the spectral line costs at most `ε⁻¹`. -/
theorem norm_kkInt_le (κ t : ℝ) {ε : ℝ} (hε : 0 < ε) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ‖kkInt α p j₀ Q M κ t ε ℓ‖ ≤ ε⁻¹ * ‖kkG α p Q M ε ℓ‖ := by
  rw [kkInt_eq, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_inv_ofReal_sub_mul_I_le _ hε) (norm_nonneg _)

variable {E : Finset (Fin (m + 1))} (hm : 7 ≤ m) (hcrit : NoSubdivergenceRefined 2 E α)
  (hB : RefinedBound α E 4 Q.eval)
include hm hcrit hB

/-- **Condition `h₁`** of the `x`-Fubini: at every spatial `v`, `w(x) kkInt(κ(x))` is
integrable jointly in `x ∈ (0, 1)` and the energies. -/
theorem integrable_kkInt_energy (hkx : Continuous kx) (t : ℝ) {ε : ℝ} (hε : 0 < ε) {w : ℝ → ℂ}
    (hw : IntegrableOn w (Ioo 0 1)) (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun q : ℝ × (Fin 2 → ℝ) => w q.1 * kkInt α p j₀ Q M (kx q.1) t ε
        fun s => (Fin.cons (q.2 s) (v s) : Fin 4 → ℝ))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  have hg := ((jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
    Q α p M hm hε hcrit hB).1 v).norm
  exact integrable_mul_of_norm_le (G := fun x tt => kkInt α p j₀ Q M (kx x) t ε
      fun s => (Fin.cons (tt s) (v s) : Fin 4 → ℝ))
    (continuous_energy_slice (G := fun x ℓ => kkInt α p j₀ Q M (kx x) t ε ℓ)
      (continuous_kkInt hkx t hε.ne') v) hw hg (fun x tt => norm_kkInt_le _ t hε _)

omit hm hcrit hB in
/-- At fixed `ε > 0` and `ℓ`, `w(x) kkInt(κ(x))` is integrable in `x ∈ (0, 1)`. -/
theorem integrableOn_kkInt (hkx : Continuous kx) (t : ℝ) {ε : ℝ} (hε : 0 < ε) {w : ℝ → ℂ}
    (hw : IntegrableOn w (Ioo 0 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IntegrableOn (fun x => w x * kkInt α p j₀ Q M (kx x) t ε ℓ) (Ioo 0 1) := by
  refine (hw.norm.mul_const (ε⁻¹ * ‖kkG α p Q M ε ℓ‖)).mono'
    (hw.aestronglyMeasurable.mul ((continuous_kkInt hkx t hε.ne').comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_kkInt_le _ t hε ℓ) (norm_nonneg _)

variable (hj₀ : j₀ ∉ E) (hkx : Continuous kx)
  (hkx01 : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < kx x ∧ kx x ≤ 1)
include hj₀ hkx hkx01

/-- **The Feynman parameter through the joint energy-first integral**: for a weight `w`
integrable on `(0, 1)`, `t > 0` and `ε > 0`, the integrand `∫₀¹ w(x) kkInt(κ(x)) dx` is
integrable in both stages and its joint integral is `∫₀¹ w(x) ∫ kkInt(κ(x)) dx`. -/
theorem jointEnergyFirstIntegral_setIntegral_kkInt (hE : E.card + 4 ≤ m + 1) {t : ℝ}
    (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1)) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ => ∫ x in Ioo (0 : ℝ) 1,
        w x * kkInt α p j₀ Q M (kx x) t ε ℓ) ∧
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => ∫ x in Ioo (0 : ℝ) 1,
        w x * kkInt α p j₀ Q M (kx x) t ε ℓ) =
        ∫ x in Ioo (0 : ℝ) 1, w x *
          QED.TwoLoop.jointEnergyFirstIntegral 2 (kkInt α p j₀ Q M (kx x) t ε) := by
  obtain ⟨C, hC⟩ := exists_absL1_kkInt_le (M := M) hm hcrit hB hj₀ hE ht hε
  obtain ⟨h1, h2⟩ := jointEnergyFirstIntegral_setIntegral (S := Ioo (0 : ℝ) 1)
    (fun x ℓ => w x * kkInt α p j₀ Q M (kx x) t ε ℓ)
    (integrable_kkInt_energy hm hcrit hB hkx t hε hw)
    (integrable_energyIntegral_of_absL1_le (G := fun x ℓ => kkInt α p j₀ Q M (kx x) t ε ℓ)
      (continuous_kkInt hkx t hε.ne') measurableSet_Ioo hw
      (fun x hx => hC (kx x) (hkx01 x hx).1 (hkx01 x hx).2))
  exact ⟨h1, h2.trans (integral_congr_ae (ae_of_all _ fun x =>
    jointEnergyFirstIntegral_two_const_mul _ _))⟩

/-- **Dominated convergence in the Feynman parameter**: `∫₀¹ w(x) ∫ kkInt(κ(x)) dx` has an
`ε → 0⁺` limit (the bound `exists_norm_kkInt_le` uniform in `x` and `ε`, the limits
`tendsto_kkInt` at fixed `x`). -/
theorem tendsto_setIntegral_kkInt {μ₀ c : ℝ} (hμ₀ : 0 < μ₀) (hc : 0 < c) (hcμ : c ≤ μ₀ ^ 2)
    (hM0 : μ₀ ≤ M j₀)
    (hV : ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α p (Function.update M j₀ a) z)
    {t : ℝ} (ht : μ₀ ≤ t) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1)) :
    ∃ Y : ℂ, Tendsto (fun ε => ∫ x in Ioo (0 : ℝ) 1, w x *
      QED.TwoLoop.jointEnergyFirstIntegral 2 (kkInt α p j₀ Q M (kx x) t ε)) (𝓝[>] 0) (𝓝 Y) := by
  obtain ⟨C, hC⟩ := exists_norm_kkInt_le hm hcrit hB hμ₀ hc hM0 hV hj₀ ht
  refine ⟨∫ x in Ioo (0 : ℝ) 1, w x * limUnder (𝓝[>] (0 : ℝ))
      (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (kkInt α p j₀ Q M (kx x) t ε)),
    tendsto_integral_filter_of_dominated_convergence (fun x => ‖w x‖ * C) ?_ ?_
      (hw.norm.mul_const _) ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact hw.aestronglyMeasurable.mul (stronglyMeasurable_jointEnergyFirstIntegral
      (continuous_kkInt hkx t hε.ne')).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _ ε (hkx01 x hx).1 (hkx01 x hx).2 hε) (norm_nonneg _)
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
    obtain ⟨L, hL⟩ := tendsto_kkInt hm hcrit hB hμ₀ hc hM0 hV hcμ (hkx01 x hx).1
      (hkx01 x hx).2 ht
    exact (tendsto_nhds_limUnder ⟨L, hL⟩).const_mul (w x)

end Param

/-! ### Families with a dispersive limit -/

/-- **A family with a dispersive limit**: for `ε > 0` the weighted integrand `w(x) H_ε(x, ℓ)` is
integrable in `x ∈ (0, 1)` at every `ℓ`, its `x`-integral is integrable in both stages of (T₉),
and the joint integral of the `x`-integral has an `ε → 0⁺` limit. -/
def KKLim (w : ℝ → ℂ) (H : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∀ ℓ, IntegrableOn (fun x => w x * H ε x ℓ) (Ioo 0 1)) ∧
    (∀ ε : ℝ, 0 < ε → QED.TwoLoop.jointEnergyFirstIntegrable 2
      (fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * H ε x ℓ)) ∧
    ∃ Y : ℂ, Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
      (fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * H ε x ℓ)) (𝓝[>] 0) (𝓝 Y)

namespace KKLim

variable {w : ℝ → ℂ} {H H₁ H₂ : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}

theorem add (h₁ : KKLim w H₁) (h₂ : KKLim w H₂) :
    KKLim w (fun ε x ℓ => H₁ ε x ℓ + H₂ ε x ℓ) := by
  obtain ⟨i₁, j₁, Y₁, hY₁⟩ := h₁
  obtain ⟨i₂, j₂, Y₂, hY₂⟩ := h₂
  have e : ∀ ε, 0 < ε → (fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * (H₁ ε x ℓ + H₂ ε x ℓ)) =
      fun ℓ => (∫ x in Ioo (0 : ℝ) 1, w x * H₁ ε x ℓ) + ∫ x in Ioo (0 : ℝ) 1, w x * H₂ ε x ℓ :=
    fun ε hε => funext fun ℓ => by
      simp_rw [mul_add]; exact integral_add (i₁ ε hε ℓ) (i₂ ε hε ℓ)
  refine ⟨fun ε hε ℓ => ((i₁ ε hε ℓ).add (i₂ ε hε ℓ)).congr_fun
      (fun x _ => by simp only [Pi.add_apply, mul_add]) measurableSet_Ioo,
    fun ε hε => ?_, Y₁ + Y₂, (hY₁.add hY₂).congr' ?_⟩
  · rw [e ε hε]
    exact QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add (j₁ ε hε) (j₂ ε hε)
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [e ε hε, QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add (j₁ ε hε) (j₂ ε hε)]

/-- A coefficient with an `ε → 0⁺` limit. -/
theorem coef (a : ℝ → ℂ) {a₀ : ℂ} (ha : Tendsto a (𝓝[>] 0) (𝓝 a₀)) (h : KKLim w H) :
    KKLim w (fun ε x ℓ => a ε * H ε x ℓ) := by
  obtain ⟨i, j, Y, hY⟩ := h
  have e : ∀ ε, (fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * (a ε * H ε x ℓ)) =
      fun ℓ => a ε * ∫ x in Ioo (0 : ℝ) 1, w x * H ε x ℓ := fun ε => funext fun ℓ => by
    simp_rw [mul_left_comm (w _)]; exact integral_const_mul _ _
  refine ⟨fun ε hε ℓ => ?_, fun ε hε => ?_, a₀ * Y, (ha.mul hY).congr fun ε => ?_⟩
  · have := (i ε hε ℓ).const_mul (a ε)
    simp_rw [mul_left_comm (w _)]
    exact this
  · rw [e ε]
    exact QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul _ (j ε hε)
  · rw [e ε, QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]

theorem const_mul (a : ℂ) (h : KKLim w H) : KKLim w (fun ε x ℓ => a * H ε x ℓ) :=
  coef (fun _ => a) tendsto_const_nhds h

theorem congr (h : KKLim w H)
    (hH : ∀ ε : ℝ, 0 < ε → ∀ x ∈ Ioo (0 : ℝ) 1, ∀ ℓ, H ε x ℓ = H₁ ε x ℓ) : KKLim w H₁ := by
  obtain ⟨i, j, Y, hY⟩ := h
  have e : ∀ ε, 0 < ε → (fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * H ε x ℓ) =
      fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * H₁ ε x ℓ := fun ε hε => funext fun ℓ =>
    setIntegral_congr_fun measurableSet_Ioo fun x hx => by simp only [hH ε hε x hx ℓ]
  refine ⟨fun ε hε ℓ => (i ε hε ℓ).congr_fun (fun x hx => by simp only [hH ε hε x hx ℓ])
    measurableSet_Ioo, fun ε hε => e ε hε ▸ j ε hε, Y, hY.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [e ε hε]

theorem zero : KKLim w (fun _ _ _ => 0) := by
  refine ⟨fun _ _ _ => by simp, fun _ _ => ?_, 0, ?_⟩
  · simp only [mul_zero, integral_zero]
    exact ⟨fun _ => integrable_zero _ _ _, by simp⟩
  · simp only [mul_zero, integral_zero, QED.TwoLoop.jointEnergyFirstIntegral]
    exact tendsto_const_nhds

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h : ∀ k ∈ s, KKLim w (F k)) : KKLim w (fun ε x ℓ => ∑ k ∈ s, F k ε x ℓ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : KKLim w _)
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (h k (Finset.mem_insert_self k s)).add
      (ih fun k' hk' => h k' (Finset.mem_insert_of_mem hk'))

end KKLim

section Term

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {p : Fin (m + 1) → Fin 4 → ℝ} {j₀ : Fin (m + 1)}
  {Q : LoopQuartic} {M : Fin (m + 1) → ℝ} {kx : ℝ → ℝ} {E : Finset (Fin (m + 1))}

/-- **A graph with the spectral line has a dispersive limit**, for every weight integrable on
`(0, 1)`: the engine hypotheses for `G` (criterion and refined bound on `E`, `|E| + 4 ≤ m + 1`,
`V ≥ c` for every mass `≥ μ₀` on the line `j₀ ∉ E`), a scale `κ(x) ∈ (0, 1]` continuous in `x`,
and a mass `t ≥ μ₀`. -/
theorem kkLim_kkInt (hm : 7 ≤ m) (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 Q.eval) (hE : E.card + 4 ≤ m + 1) (hj₀ : j₀ ∉ E)
    {μ₀ c : ℝ} (hμ₀ : 0 < μ₀) (hc : 0 < c) (hcμ : c ≤ μ₀ ^ 2) (hM0 : μ₀ ≤ M j₀)
    (hV : ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α p (Function.update M j₀ a) z)
    (hkx : Continuous kx) (hkx01 : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < kx x ∧ kx x ≤ 1)
    {t : ℝ} (ht : μ₀ ≤ t) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1)) :
    KKLim w (fun ε x ℓ => kkInt α p j₀ Q M (kx x) t ε ℓ) := by
  have ht0 : 0 < t := hμ₀.trans_le ht
  obtain ⟨Y, hY⟩ := tendsto_setIntegral_kkInt hm hcrit hB hj₀ hkx hkx01 hμ₀ hc hcμ hM0 hV ht hw
  refine ⟨fun ε hε ℓ => integrableOn_kkInt hkx t hε hw ℓ, fun ε hε =>
    (jointEnergyFirstIntegral_setIntegral_kkInt hm hcrit hB hj₀ hkx hkx01 hE ht0 hε hw).1, Y,
    hY.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (jointEnergyFirstIntegral_setIntegral_kkInt hm hcrit hB hj₀ hkx hkx01 hE ht0 hε hw).2.symm

end Term

end QED.ChainProof.SetCMainB

end
