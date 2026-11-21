/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkVInput
public import QED.ChainProof.SetCLinkSESplit
public import QED.GradedProof.WI2Core

/-!
# Set (c), model link: the Ward input (I3) of the VP share

Helper for (WI-s) `QED.ThreeLoop.isVPShareOnShell_d₁_eq_d₂` (decision D-58): the input
`QED.ChainProof.SetCLink.VPWardInput`, the restriction of `WI2.charge_eq_neg_e_mul_slope` to the
vacuum-polarization classes.

* `seVPLim Q p`: the `ε → 0⁺` limit of `seVPValue = -V + P0 + P1` near the shell
  (`tendsto_seVPValue`, from `tendsto_repV_wt`, `tendsto_repP0_wt`, `tendsto_repP1_wt`).
* `hasDerivAt_seVPLim_apply`: **the Ward identity of the family for one T1 parameter set**,
  `d/dt|₁ seVPLim(t p) = -(i/e) ∑_μ p_μ famLim(p)^μ` on the shell: the pieces `hV`
  (`hasDerivAt_vPV_wt`) and `hP` (`hasDerivAt_dP_wt`) of `WI2.hasDerivAt_seLimNC`, paired with the
  vertex classes `VP` (`sum_lower_classLimitV_VP`) and `d3Slot0`, `d3Slot1`
  (`sum_lower_ctLimitV_d3Slot0`, `_d3Slot1`). No `δ₁` class enters.
* **`vpWardInput`**: under the hypotheses of (G-Σ₂) and `e ≠ 0`, `VPWardInput P Φ (dZero D)`:
  both sides are split into the same T1 parameter sets with the same real weights
  (`selfEnergySelPart_split`, `familyVertex_split`), and the shell function is differentiated at
  `t = 1` in the rest frame, as in `WI2.charge_eq_neg_e_mul_slope`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.ChainProof.SetCLink

open QED.Graded QED.GradedProof QED.GradedProof.V5Zero QED.GradedProof.SE2
open QED.GradedProof.WI2 (vPV vInsV tendsto_repV_wt tendsto_repP0_wt tendsto_repP1_wt
  hasDerivAt_vPV_wt hasDerivAt_dP_wt sum_lower_classLimitV_VP sum_lower_ctLimitV_d3Slot0
  sum_lower_ctLimitV_d3Slot1 sum_mul_sandwich eventually_region sum_lower_sandwich_gamma)
open QED.GradedProof.WI2 (dP aSlotP bSlotP cSlotP dbl)
open QED.WickModel (Params)
open QED.TwoLoop.LimitCovariance (classLimitV ctLimitV)
open QED.TwoLoop.CountertermLimit (auxLimit)
open QED.TwoLoop.Enumeration (Class5)

/-- The limit of each of `P0`, `P1` (`tendsto_repP0_wt`). -/
noncomputable def dPVal (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  (auxLimit Q.m)⁻¹ * (kappaSE Q.e *
    (dP Q).pvF (fun ℓ => (dP Q).slotN 0 Q.m aSlotP bSlotP (cSlotP Q) p ℓ α β) ((dP Q).mom p))

/-- **The `ε → 0⁺` limit of the T1 vacuum-polarization family self-energy.** -/
noncomputable def seVPLim (Q : Params) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => -vPV Q p α β + dPVal Q p α β + dPVal Q p α β

section T1

variable (Q : Params) {m₀ : ℝ} (h : Adm m₀ Q)
include h

theorem tendsto_seVPValue {p : Fin 4 → ℝ}
    (hs : -(Q.m + min (min Q.mγ Q.Λ) (2 * m₀)) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    Tendsto (fun ε : ℝ => seVPValue { Q with ε := ε } p α β) (𝓝[>] 0)
      (𝓝 (seVPLim Q p α β)) := by
  have hm : 0 < Q.m := h.hm₀.trans_le h.hm
  set ν : ℝ := min (min Q.mγ Q.Λ) (2 * m₀)
  have hν0 : 0 < ν := lt_min (lt_min h.hmγ h.hΛ) (by linarith [h.hm₀])
  have hν : ν ≤ min Q.mγ Q.Λ := min_le_left _ _
  have hν2 : ν ≤ 2 * m₀ := min_le_right _ _
  have hV := tendsto_repV_wt h.hc₁ h.hc₂ h.hm₀ h.hm h.hM₁ h.hM₂ hν0 hν hν2 hs α β
  have hP0 := tendsto_repP0_wt Q hm hν0 hν hs α β
  have hP1 := tendsto_repP1_wt Q hm hν0 hν hs α β
  simpa only [seVPValue, seVPLim, dPVal, Matrix.of_apply] using (hV.neg.add hP0).add hP1

/-- The contracted family vertex limit by classes. -/
theorem sum_lower_famLim {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Q.m ^ 2)
    (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * famLim Q p μ α β = (1 / I) * (-(Q.e * vInsV Q p r α β) +
      2 * (Q.e * kappaSE Q.e * (auxLimit Q.m)⁻¹ * ((dP Q).dup 0).pvF
        (fun ℓ => (dP Q).slotV 0 Q.m aSlotP bSlotP (cSlotP Q) p r ℓ α β)
        (dbl 0 ((dP Q).mom p)))) := by
  have hm : 0 < Q.m := h.hm₀.trans_le h.hm
  set ν : ℝ := min (min Q.mγ Q.Λ) (2 * m₀)
  have hν0 : 0 < ν := lt_min (lt_min h.hmγ h.hΛ) (by linarith [h.hm₀])
  have hν : ν ≤ min Q.mγ Q.Λ := min_le_left _ _
  have hν2 : ν ≤ 2 * m₀ := min_le_right _ _
  have hs : ((Class5.VP.sign : ℤ) : ℂ) = -1 := by simp [Class5.sign]
  have e : ∀ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * famLim Q p μ α β =
      (1 / I) * (((Class5.VP.sign : ℤ) : ℂ) *
        (((Minkowski.lower r μ : ℝ) : ℂ) * classLimitV .VP Q p p μ α β)) +
      (1 / I) * (((Minkowski.lower r μ : ℝ) : ℂ) * ctLimitV .d3Slot0 Q p p μ α β) +
      (1 / I) * (((Minkowski.lower r μ : ℝ) : ℂ) * ctLimitV .d3Slot1 Q p p μ α β) := by
    intro μ
    simp only [famLim, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun μ _ => e μ, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_lower_classLimitV_VP h.hc₁ h.hc₂ h.hm₀ h.hm h.hM₁ h.hM₂ hν0 hν hν2 hp r α β,
    sum_lower_ctLimitV_d3Slot0 Q hm h.hmγ h.hΛ hp r α β,
    sum_lower_ctLimitV_d3Slot1 Q hm h.hmγ h.hΛ hp r α β, hs]
  ring

/-- **The Ward identity of the vacuum-polarization family for one T1 parameter set**,
entrywise. -/
theorem hasDerivAt_seVPLim_apply (he : Q.e ≠ 0) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -Q.m ^ 2) (α β : Fin 4) :
    HasDerivAt (fun t : ℝ => seVPLim Q (t • p) α β)
      (-(I / Q.e) * ∑ μ, ((Minkowski.lower p μ : ℝ) : ℂ) * famLim Q p μ α β) 1 := by
  have hm : 0 < Q.m := h.hm₀.trans_le h.hm
  set ν : ℝ := min (min Q.mγ Q.Λ) (2 * m₀)
  have hν0 : 0 < ν := lt_min (lt_min h.hmγ h.hΛ) (by linarith [h.hm₀])
  have hν : ν ≤ min Q.mγ Q.Λ := min_le_left _ _
  have hν2 : ν ≤ 2 * m₀ := min_le_right _ _
  have hν2' : ν ≤ 2 * Q.m := hν2.trans (by linarith [h.hm])
  have hr : -(Q.m + ν) ^ 2 < Minkowski.dot ((1 : ℝ) • p) ((1 : ℝ) • p) := by
    rw [one_smul, hp]
    nlinarith
  have hV := hasDerivAt_vPV_wt h.hm₀ h.hm h.hM₁ h.hM₂ hν0 hν hν2 p hr α β
  have hP := ((hasDerivAt_dP_wt Q hm hν0 hν p hr α β).const_mul (kappaSE Q.e)).const_mul
    (auxLimit Q.m)⁻¹
  have H := (hV.neg.add hP).add hP
  convert H using 1
  · rfl
  rw [sum_lower_famLim Q h hp p α β]
  simp only [one_smul]
  have he' : (Q.e : ℂ) ≠ 0 := by exact_mod_cast he
  field_simp
  ring

/-- **The Ward identity of the vacuum-polarization family for one T1 parameter set**, between
spinors. -/
theorem hasDerivAt_sandwich_seVPLim (he : Q.e ≠ 0) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -Q.m ^ 2) (u w : Fin 4 → ℂ) :
    HasDerivAt (fun t : ℝ => w ⬝ᵥ (seVPLim Q (t • p) *ᵥ u))
      (-(I / Q.e) * ∑ μ, ((Minkowski.lower p μ : ℝ) : ℂ) * (w ⬝ᵥ (famLim Q p μ *ᵥ u))) 1 := by
  have hf : (fun t : ℝ => w ⬝ᵥ (seVPLim Q (t • p) *ᵥ u)) = fun t =>
      ∑ α, ∑ β, w α * (seVPLim Q (t • p) α β * u β) := by
    funext t
    simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [hf]
  have H := HasDerivAt.fun_sum (u := Finset.univ) fun α _ => HasDerivAt.fun_sum
    (u := Finset.univ) fun β _ =>
      ((hasDerivAt_seVPLim_apply Q h he hp α β).mul_const (u β)).const_mul (w α)
  convert H using 1
  rw [Finset.mul_sum, Finset.sum_congr rfl fun μ _ => (mul_assoc _ _ _).symm, sum_mul_sandwich]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.mul_sum]
  simp only [mul_assoc]

end T1

/-- **Input (I3).** Under the hypotheses of (G-Σ₂) and `e ≠ 0`, the family Ward identity
`c = -e σ₁` for the data `dZero D`. -/
theorem vpWardInput (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hPV₁ : ∑ g, Φ.coeff g = 0)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) (he : P.e ≠ 0) :
    VPWardInput P Φ (dZero D) := by
  classical
  intro r hr A B hlim σ₁ hσ₁ c hc
  set M := Φ.mass Φ.openLine with hMdef
  have hM : 0 < M := hm₀.trans_le (hmass _)
  set D₁ := levelZero (dZero D) with hD₁
  have hD : ∀ f k, 1 ≤ k → D₁.d₁ f k = 0 ∧ D₁.d₂ f k = 0 ∧ D₁.dm f k = 0 := fun f k hk => by
    simp [hD₁, levelZero, show k ≠ 0 by omega]
  have hD₃ : ∀ k, 1 ≤ k → D₁.d₃ k = 0 := fun k hk => by
    simp [hD₁, levelZero, show k ≠ 0 by omega]
  have hfv : ∀ (Q : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4),
      familyVertex Q Φ (dZero D) selV 5 p' p μ = familyVertex Q Φ D₁ selV 5 p' p μ := by
    intro Q p' p μ
    rw [familyVertex_five_sub Q Φ (dZero D) D₁ (by simp [hD₁, levelZero])
      (by simp [hD₁, levelZero]) (by simp [hD₁, levelZero]) (by simp [hD₁, levelZero])
      (fun _ => by simp [hD₁, levelZero]) (fun _ => by simp [hD₁, levelZero])
      (fun _ => by simp [hD₁, levelZero])]
    simp [hD₁, levelZero, dZero, Counterterms.withLevel]
  set Q := GEx2.vParams P Φ D₁ Φ.openLine with hQ
  obtain ⟨X, -, hmX, -, hlt, -, hXm, hX⟩ := Split.exists_aux Q.m Φ.mass
  let S : Option F → Params := fun k => k.elim (Split.zParams Q X) (Split.gParams Q Φ X)
  let a : Option F → ℝ := fun k => k.elim 1 (Split.weight Q Φ X)
  have hmf : m₀ ≤ Q.m := hmass _
  have hadm : ∀ k, Adm m₀ (S k) := by
    rintro (_ | g)
    · exact ⟨hm₀, hmf, hmγ, hΛ, hmf, hmf.trans hmX.le, Split.zParams_PV₁ Q X,
        Split.zParams_PV₂ Q X⟩
    · exact ⟨hm₀, hmf, hmγ, hΛ, hmass g, hmf.trans hmX.le, Split.gParams_PV₁ Q Φ X g,
        Split.gParams_PV₂ Q Φ X g (hX g)⟩
  have hSm : ∀ k, (S k).m = M := by rintro (_ | _) <;> rfl
  have hSe : ∀ k, (S k).e ≠ 0 := by rintro (_ | _) <;> exact he
  have hSe' : ∀ k, (S k).e = P.e := by rintro (_ | _) <;> rfl
  have hSγ : ∀ k, (S k).mγ = P.mγ := by rintro (_ | _) <;> rfl
  have hSΛ : ∀ k, (S k).Λ = P.Λ := by rintro (_ | _) <;> rfl
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  obtain ⟨u, w, hu, hw, hwu⟩ := WI2.exists_rest_sandwich_ne_zero hM
  set p := V5Zero.Dirac.restVec M
  have hp : Minkowski.dot p p = -M ^ 2 := V5Zero.Dirac.dot_restVec M
  have hp0 : 0 < p 0 := by simp [p, V5Zero.Dirac.restVec, hM]
  have hpk : ∀ k, Minkowski.dot p p = -(S k).m ^ 2 := fun k => by rw [hSm k]; exact hp
  -- the vertex side
  set comb : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun μ => ∑ k, (a k : ℂ) • famLim (S k) p μ
    with hcomb
  have hVc : ∀ μ, (c : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) = w ⬝ᵥ (comb μ *ᵥ u) := by
    intro μ
    have key : ∀ ε : ℝ, 0 < ε → familyVertex { P with ε := ε } Φ (dZero D) selV 5 p p μ =
        ∑ k, (a k : ℂ) • famT1 { S k with ε := ε } p p μ := by
      intro ε hε
      rw [hfv, familyVertex_split (P := { P with ε := ε }) (X := X) hε hPV₁ hPV₂ hXm hX hD hD₃,
        Fintype.sum_option]
      simp only [S, a, Option.elim, Complex.ofReal_one, one_smul]
      rfl
    have hS : Tendsto (fun ε : ℝ => ∑ k, (a k : ℂ) • famT1 { S k with ε := ε } p p μ)
        (𝓝[>] 0) (𝓝 (comb μ)) :=
      tendsto_finsetSum _ fun k _ => (tendsto_famT1 (hadm k) (hpk k) hp0 μ).const_smul _
    have hcont : Continuous fun N : Matrix (Fin 4) (Fin 4) ℂ => w ⬝ᵥ (N *ᵥ u) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    refine tendsto_nhds_unique (hc p hp hp0 μ u w hu hw) (((hcont.tendsto _).comp hS).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [Function.comp_apply, key ε hε]
  -- the self-energy side near `t = 1`
  have hsplit : ∀ ε : ℝ, 0 < ε → ∀ q : Fin 4 → ℝ, ∀ α β : Fin 4,
      selfEnergySelPart { P with ε := ε } Φ (dZero D) selSE Φ.openLine 2 q α β =
        (1 / I) * ∑ k, (a k : ℂ) * seVPValue { S k with ε := ε } q α β := by
    intro ε hε q α β
    have h2 := selfEnergySelPart_two_sub { P with ε := ε } Φ (dZero D) D₁
      (fun _ => by simp [hD₁, levelZero]) (fun _ => by simp [hD₁, levelZero])
      (fun _ => by simp [hD₁, levelZero]) (by simp [hD₁, levelZero]) Φ.openLine q α β
    have t0 : GEx2.seTree { P with ε := ε } Φ (dZero D) Φ.openLine q α β = 0 := by
      simp [GEx2.seTree, dZero, Counterterms.withLevel]
    have t1 : GEx2.seTree { P with ε := ε } Φ D₁ Φ.openLine q α β = 0 := by
      simp [GEx2.seTree, hD₁, levelZero]
    rw [t0, t1, add_zero, add_zero] at h2
    rw [h2, selfEnergySelPart_split { P with ε := ε } Φ D₁ Φ.openLine hε hmγ hΛ hpos hPV₁ hPV₂
      hlt hD hD₃ q α β, Fintype.sum_option]
    simp only [S, a, Option.elim, Complex.ofReal_one, one_mul]
    rfl
  set ν : ℝ := min (min P.mγ P.Λ) (2 * m₀)
  have hν0 : 0 < ν := lt_min (lt_min hmγ hΛ) (by linarith)
  have hreg : ∀ T : ℝ, 0 < T → ∀ᶠ t in 𝓝 (1 : ℝ), -(M + T) ^ 2 < Minkowski.dot (t • p) (t • p) :=
    fun T hT => eventually_region p (by rw [one_smul, hp]; nlinarith)
  have hEq : ∀ᶠ t in 𝓝 (1 : ℝ), GEx2.shellFun A B M (-(t * M)) * (w ⬝ᵥ u) =
      (1 / I) * ∑ k, (a k : ℂ) * (w ⬝ᵥ (seVPLim (S k) (t • p) *ᵥ u)) := by
    filter_upwards [hreg r hr, hreg ν hν0] with t h1 h2
    have hmat : A (Minkowski.dot (t • p) (t • p)) • Dirac.slash (t • p) +
        (B (Minkowski.dot (t • p) (t • p)) * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ) =
        (1 / I) • ∑ k, (a k : ℂ) • seVPLim (S k) (t • p) := by
      ext α β
      refine tendsto_nhds_unique (hlim (t • p) h1 α β) ?_
      have hT : ∀ k, Tendsto (fun ε => seVPValue { S k with ε := ε } (t • p) α β) (𝓝[>] 0)
          (𝓝 (seVPLim (S k) (t • p) α β)) := fun k =>
        tendsto_seVPValue (S k) (hadm k) (by rw [hSm k, hSγ k, hSΛ k]; exact h2) α β
      have hsum := (tendsto_finsetSum Finset.univ fun k _ =>
        (hT k).const_mul (a k : ℂ)).const_mul (1 / I)
      rw [show ((1 / I) • ∑ k, (a k : ℂ) • seVPLim (S k) (t • p)) α β =
          (1 / I) * ∑ k, (a k : ℂ) * seVPLim (S k) (t • p) α β by
        simp [Matrix.sum_apply]]
      refine hsum.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      rw [hsplit ε hε]
    rw [← WI2.sandwich_shell A B hp hu w t, hmat, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, Matrix.sum_mulVec, dotProduct_sum]
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hH : HasDerivAt (fun t : ℝ => GEx2.shellFun A B M (-(t * M)) * (w ⬝ᵥ u))
      (((-M : ℝ) • (σ₁ : ℂ)) * (w ⬝ᵥ u)) 1 := by
    have hc' : HasDerivAt (fun t : ℝ => -(t * M)) (-M) 1 := by
      have := ((hasDerivAt_id (1 : ℝ)).mul_const M).neg
      simp only [id, one_mul] at this
      exact this
    have hs : HasDerivAt (GEx2.shellFun A B M) (σ₁ : ℂ) (-(1 * M)) := by
      rw [one_mul]
      exact hσ₁
    exact (hs.scomp 1 hc').mul_const (w ⬝ᵥ u)
  have hG := (HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (hasDerivAt_sandwich_seVPLim (S k) (hadm k) (hSe k) (hpk k) u w).const_mul
      (a k : ℂ)).const_mul (1 / I)
  have huniq := hH.unique (hG.congr_of_eventuallyEq hEq)
  simp only [hSe'] at huniq
  -- the vertex side contracted with `p`
  have hcomb' : ∑ μ, ((Minkowski.lower p μ : ℝ) : ℂ) * (w ⬝ᵥ (comb μ *ᵥ u)) =
      (c : ℂ) * (-(M : ℂ) * (w ⬝ᵥ u)) := by
    simp only [← hVc, mul_left_comm _ (c : ℂ), ← Finset.mul_sum, sum_lower_sandwich_gamma, hu,
      dotProduct_neg, dotProduct_smul, smul_eq_mul]
    ring
  simp only [hcomb, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    smul_eq_mul] at hcomb'
  have hG' : (1 / I) * ∑ k, (a k : ℂ) * (-(I / (P.e : ℂ)) * ∑ μ,
      ((Minkowski.lower p μ : ℝ) : ℂ) * (w ⬝ᵥ (famLim (S k) p μ *ᵥ u))) =
      -(1 / (P.e : ℂ)) * ∑ μ, ((Minkowski.lower p μ : ℝ) : ℂ) *
        ∑ k, (a k : ℂ) * (w ⬝ᵥ (famLim (S k) p μ *ᵥ u)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [hG', hcomb', Complex.real_smul] at huniq
  have he' : (P.e : ℂ) ≠ 0 := by exact_mod_cast he
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast at huniq
  field_simp at huniq
  have : ((c : ℝ) : ℂ) = ((-(P.e * σ₁) : ℝ) : ℂ) := by
    push_cast
    linear_combination -huniq
  exact_mod_cast this

end QED.ChainProof.SetCLink

end
