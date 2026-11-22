/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLimCtCB01Cov
public import QED.ChainProof.SetCLimCtCB01

/-!
# Set (c): the links of the classes `CB0`, `CB1`, and the links of (HS₆) from the main classes

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The class values
of `CB0`, `CB1` in `QED.ChainProof.SetCPauli.ctFam` are minus T1's values of `repCB0`, `repCB1` at
`cbParams` (`cb01Val_apply`); these converge and their limits are covariant
(`QED/ChainProof/SetCLimCtCB01Lim.lean`, `QED/ChainProof/SetCLimCtCB01Cov.lean`).

* **`setCClassLim_CB01`**, **`setCClassCov_CB01`**: the limit and covariance links of the classes
  `.inl k` of `ctFam`, `k < 2`;
* **`setCLimitLink_of_main`**, **`setCCovLink_of_main`**: the limit and covariance links of (HS₆)
  from the per-class links of the 36 two-loop-outer classes alone.
-/

@[expose] public section

open Complex Matrix Filter Topology
open QED.WickModel (Params contractionValue₂)

namespace QED.ChainProof.SetCPauli

open QED.ChainProof.SetCLink
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.ChainProof.SetCPauli.CB01

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-! ### The class values -/

theorem ctFam_cb0_eq (ε : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    ctFam { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) p' p μ (.inl 0) i j =
      -contractionValue₂ { cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0 with ε := ε } repCB0
        (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) := by
  rw [← (cb01Val_apply (P₀ := P₀) (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂) (mγ := mγ)
    (Λ := Λ) (D := D) (s := s) ε p' p μ i j).1]
  rfl

theorem ctFam_cb1_eq (ε : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    ctFam { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) p' p μ (.inl 1) i j =
      -contractionValue₂ { cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0 with ε := ε } repCB1
        (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) := by
  rw [← (cb01Val_apply (P₀ := P₀) (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂) (mγ := mγ)
    (Λ := Λ) (D := D) (s := s) ε p' p μ i j).2]
  rfl

/-- The class values of `CB0`, `CB1` (`d = 1`, `0`) at `ε > 0` as joint integrals of the
integrand in shape form. -/
theorem ctFam_cb01_eq (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (k : Fin 5) (hk : k < 2)
    (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (ε : ℝ) (hε : 0 < ε) :
    ctFam { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) p' p μ (.inl k) i j =
      -QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * cbIntegrand
          { cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0 with ε := ε } (if k = 0 then 1 else 0) p' p i j μ
            ℓ := by
  obtain ⟨-, -, hc₁, hc₂, -⟩ := hA
  rcases lt_two_cases hk with rfl | rfl
  · rw [ctFam_cb0_eq, contractionValue₂_cb0_shapes _ hε.ne' hc₁ hc₂]
    rfl
  · rw [ctFam_cb1_eq, contractionValue₂_cb1_shapes _ hε.ne' hc₁ hc₂]
    rfl

/-! ### The links -/

/-- **The limit links of the two classes `CB0`, `CB1`.** -/
theorem setCClassLim_CB01 (k : Fin 5) (hk : k < 2) : SetCClassLim ctFam P₀ (.inl k) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  have hA' := hA
  obtain ⟨hM₁, hM₂, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA'
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  set Pc := cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0
  have h₁ : Pc.m ^ 2 ≤ Pc.M₁ ^ 2 := pow_le_pow_left₀ hm.le hM₁.le 2
  have h₂ : Pc.m ^ 2 ≤ Pc.M₂ ^ 2 := pow_le_pow_left₀ hm.le hM₂.le 2
  choose vA vB _hvA _hvB hT using fun μ i j => tendsto_cbIntegrand Pc hmγ hΛ hm h₁ h₂ hp hp' hq.le
    (if k = 0 then 1 else 0) i j μ
  refine ⟨fun μ => Matrix.of fun i j =>
    ∑ k, vA μ i j k + mergeC Pc.m Pc.δ₂ Pc.δm * ∑ k, vB μ i j k, fun μ i j => ?_⟩
  have h := (hT μ i j).2.neg
  rw [neg_neg] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (ctFam_cb01_eq hA k hk p' p μ i j ε hε).symm

/-- **The covariance links of the two classes `CB0`, `CB1`.** -/
theorem setCClassCov_CB01 (k : Fin 5) (hk : k < 2) : SetCClassCov ctFam P₀ (.inl k) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA L S T h p' p hpq h0 h1 Y Z hY hZ μ
  have hpq' := isPairQ_map h hpq h0 h1
  have hA' := hA
  obtain ⟨hM₁, hM₂, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA'
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  obtain ⟨hpL', hpL, -, -, hqL⟩ := hpq'
  have hm : 0 < P₀.m := by linarith
  set Pc := cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0
  have h₁ : Pc.m ^ 2 ≤ Pc.M₁ ^ 2 := pow_le_pow_left₀ hm.le hM₁.le 2
  have h₂ : Pc.m ^ 2 ≤ Pc.M₂ ^ 2 := pow_le_pow_left₀ hm.le hM₂.le 2
  exact conj_cbLim Pc hmγ hΛ hm h₁ h₂ h hp hp' hq.le hpL hpL' hqL.le _ Y Z
    (cb_char Pc hmγ hΛ hm h₁ h₂ hp hp' hq.le _ _
      (fun μ i j ε hε => ctFam_cb01_eq hA k hk p' p μ i j ε hε) hY)
    (cb_char Pc hmγ hΛ hm h₁ h₂ hpL hpL' hqL.le _ _
      (fun μ i j ε hε => ctFam_cb01_eq hA k hk (L *ᵥ p') (L *ᵥ p) μ i j ε hε) hZ) μ

/-! ### The links of (HS₆) from the main classes -/

/-- **The limit link of (HS₆)** from the limit links of the 36 two-loop-outer classes. -/
theorem setCLimitLink_of_main (hM : ∀ r, SetCClassLim mainFam P₀ r) : SetCLimitLink P₀ :=
  setCLimitLink_of_main_cb01 hM fun k hk => setCClassLim_CB01 k hk

/-- **The covariance link of (HS₆)** from the limit and covariance links of the 36
two-loop-outer classes. -/
theorem setCCovLink_of_main (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hMc : ∀ r, SetCClassCov mainFam P₀ r) : SetCCovLink P₀ :=
  setCCovLink_of_main_cb01 hM (fun k hk => setCClassLim_CB01 k hk) hMc
    fun k hk => setCClassCov_CB01 k hk

end QED.ChainProof.SetCPauli

end
