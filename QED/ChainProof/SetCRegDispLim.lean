/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispPV
public import QED.ChainProof.SetCPauliSum

/-!
# Set (c), regulator limit: fixed regulator fermions and dominated convergence

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, regulator limit
`QED.ChainProof.SetCPauli.SetCRegLimitDisp` (the input of
`isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp_disp`, `QED/ChainProof/SetCPauliFinal.lean`).
The limit is taken in two steps: `(mγ, Λ) → (0⁺, ∞)` at fixed regulator fermions, then the
regulator fermions decouple (`QED/ChainProof/SetCRegDispPV.lean`).

**Regulated pieces.** `IsRegPiece a A`: `a mγ Λ T → A T` for every `T ≥ 4` as
`(mγ, Λ) → (0⁺, ∞)`, `a mγ Λ` measurable, and `|a mγ Λ T| ≤ C/√T` uniformly for small `mγ`,
large `Λ` (implied by the plan's `C(1 + ln T)/T`).

## Main statements

* `exists_setCAdm`: admissible set (c) data exist over every `m < M₁, M₂`, `0 < mγ < Λ`,
  `mγ < 2m` with PV coefficients;
* `SetCRegFixLim P₀ b`: at fixed admissible regulator fermions, `b → e⁶ K_PV/(64π⁶)`, with
  `K_PV = K(1) + c₁ K(M₁²/m²) + c₂ K(M₂²/m²)` (`kDispPV`);
* **`setCRegLimitDisp_of_fixLim`**: `SetCRegFixLim P₀ b → SetCRegLimitDisp P₀ b` (the regulator
  fermions decouple, `QED.ChainProof.SetCRegDisp.kDisp_decouple`);
* `IsRegPiece`, `IsRegPiece.add`, `rho_div_sqrt_le` (`ρ(v)/√(s t_v) ≤ (1 - v)^{-1/2}`);
* **`tendsto_jDisp`**: dominated convergence in `v`: for a regulated kernel `a` of the kernel sum
  `setCKKernelPairSum`, `∫₀¹ ρ(v)[a(t_v) + c₁ a(s₁ t_v) + c₂ a(s₂ t_v)] dv → K(1) + c₁ K(s₁) +
  c₂ K(s₂)` (`jDisp`).
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCK QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### Admissible data exist -/

/-- **Admissible set (c) data exist** at PV regulator fermions and `0 < mγ < Λ`, `mγ < 2m`. -/
theorem exists_setCAdm {P₀ : Params} (he : P₀.e ≠ 0) {M₁ M₂ c₁ c₂ mγ Λ : ℝ} (hM₁ : P₀.m < M₁)
    (hM₂ : P₀.m < M₂) (hc : 1 + c₁ + c₂ = 0) (hc' : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0)
    (hmγ : 0 < mγ) (hmΛ : mγ < Λ) (hm2 : mγ < 2 * P₀.m) :
    ∃ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s := by
  have hm : 0 < P₀.m := by linarith
  have hΛ : 0 < Λ := hmγ.trans hmΛ
  obtain ⟨D, hD⟩ := QED.GradedProof.RPi4.exists_renormalized (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) he hm hmγ hΛ hM₁ hM₂ (fun ℓ => ℓ.elim0)
    (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) hc hc' (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0)
  have hb₁ := QED.GradedProof.RPi4.leptonFlavors_blockPV₁ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) hc (fun ℓ => ℓ.elim0)
  have hb₂ := QED.GradedProof.RPi4.leptonFlavors_blockPV₂ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) hc' (fun ℓ => ℓ.elim0)
  obtain ⟨s, hs, -⟩ := SetCLink.existsUnique_isVPShareOnShell_c (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep P₀.m he hm
    (regFlavors_mass_ge_c hM₁ hM₂) hmγ hΛ QED.GradedProof.RPi4.leptonRep_idem hb₁ hb₂
    (isRenormalizedThrough_one_of_two hD)
  exact ⟨D, s, hM₁, hM₂, hc, hc', hmγ, hΛ, hmΛ, hm2, hD, hs⟩

/-! ### The limit at fixed regulator fermions -/

/-- The flavour sum `K(1) + c₁ K(M₁²/m²) + c₂ K(M₂²/m²)` of the dispersion integrals. -/
noncomputable def kDispPV (m M₁ M₂ c₁ c₂ : ℝ) : ℝ :=
  kDisp 1 + c₁ * kDisp (M₁ ^ 2 / m ^ 2) + c₂ * kDisp (M₂ ^ 2 / m ^ 2)

/-- **The regulator limit at fixed regulator fermions** (open for a given `b`): for admissible
`M₁, M₂, c₁, c₂`, `b → e⁶ K_PV/(64π⁶)` as `(mγ, Λ) → (0⁺, ∞)`. -/
def SetCRegFixLim (P₀ : Params) (b : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → 1 + c₁ + c₂ = 0 →
    P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 → ∀ η > 0, ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ →
        |b mγ Λ M₁ M₂ - P₀.e ^ 6 * kDispPV P₀.m M₁ M₂ c₁ c₂ / (64 * π ^ 6)| < η

theorem one_le_sq_div {m M : ℝ} (hm : 0 < m) (hM : m < M) : 1 ≤ M ^ 2 / m ^ 2 := by
  rw [le_div_iff₀ (by positivity), one_mul]
  exact pow_le_pow_left₀ hm.le hM.le 2

theorem pv_div {m M₁ M₂ c₁ c₂ : ℝ} (hm : 0 < m) (hc' : m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) :
    1 + c₁ * (M₁ ^ 2 / m ^ 2) + c₂ * (M₂ ^ 2 / m ^ 2) = 0 := by
  have hm2 : m ^ 2 ≠ 0 := by positivity
  field_simp
  linear_combination hc'

/-- **The regulator fermions decouple**: the limit at fixed regulator fermions gives the
regulator limit towards the dispersion integral. -/
theorem setCRegLimitDisp_of_fixLim {P₀ : Params} {b : ℝ → ℝ → ℝ → ℝ → ℝ} (hm : 0 < P₀.m)
    (h : SetCRegFixLim P₀ b) : SetCRegLimitDisp P₀ b := by
  intro η hη
  set K : ℝ := P₀.e ^ 6 / (64 * π ^ 6) with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨R, hR1, hR⟩ := kDisp_decouple (η := η / 2 / (K + 1)) (by positivity)
  refine ⟨P₀.m * R, fun M₁ M₂ h₁ h₂ hne => ?_⟩
  have hmR : P₀.m ≤ P₀.m * R := le_mul_of_one_le_right hm.le hR1
  have hM₁ : P₀.m < M₁ := hmR.trans_lt h₁
  have hM₂ : P₀.m < M₂ := hmR.trans_lt h₂
  have hsq : M₁ ^ 2 - M₂ ^ 2 ≠ 0 := by
    intro e
    have : (M₁ - M₂) * (M₁ + M₂) = 0 := by linear_combination e
    rcases mul_eq_zero.1 this with e' | e'
    · exact hne (by linarith)
    · linarith
  set c₁ : ℝ := (M₂ ^ 2 - P₀.m ^ 2) / (M₁ ^ 2 - M₂ ^ 2)
  set c₂ : ℝ := (P₀.m ^ 2 - M₁ ^ 2) / (M₁ ^ 2 - M₂ ^ 2)
  have hc : 1 + c₁ + c₂ = 0 := by
    simp only [c₁, c₂]
    field_simp
    ring
  have hc' : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 := by
    simp only [c₁, c₂]
    field_simp
    ring
  have hs : ∀ M, P₀.m * R < M → R ≤ M ^ 2 / P₀.m ^ 2 := fun M hM => by
    have h1 : R < M / P₀.m := by rw [lt_div_iff₀ hm]; linarith
    have h2 : 1 ≤ M / P₀.m := hR1.trans h1.le
    rw [← div_pow]
    nlinarith
  have hdec := hR _ _ c₁ c₂ (hs M₁ h₁) (hs M₂ h₂) hc (pv_div hm hc')
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := h M₁ M₂ c₁ c₂ hM₁ hM₂ hc hc' (η / 2) (half_pos hη)
  refine ⟨δ, hδ, Λ₀, fun mγ Λ h0 h1 h2 => ?_⟩
  have hb := hΛ₀ mγ Λ h0 h1 h2
  have e : b mγ Λ M₁ M₂ - P₀.e ^ 6 * setCKDisp / (64 * π ^ 6) =
      (b mγ Λ M₁ M₂ - P₀.e ^ 6 * kDispPV P₀.m M₁ M₂ c₁ c₂ / (64 * π ^ 6)) +
        K * (c₁ * kDisp (M₁ ^ 2 / P₀.m ^ 2) + c₂ * kDisp (M₂ ^ 2 / P₀.m ^ 2)) := by
    rw [hK, kDispPV, kDisp_one]
    ring
  have hKη : K * (η / 2 / (K + 1)) ≤ η / 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  rw [e]
  calc |(b mγ Λ M₁ M₂ - P₀.e ^ 6 * kDispPV P₀.m M₁ M₂ c₁ c₂ / (64 * π ^ 6)) +
        K * (c₁ * kDisp (M₁ ^ 2 / P₀.m ^ 2) + c₂ * kDisp (M₂ ^ 2 / P₀.m ^ 2))|
      ≤ |b mγ Λ M₁ M₂ - P₀.e ^ 6 * kDispPV P₀.m M₁ M₂ c₁ c₂ / (64 * π ^ 6)| +
        |K * (c₁ * kDisp (M₁ ^ 2 / P₀.m ^ 2) + c₂ * kDisp (M₂ ^ 2 / P₀.m ^ 2))| :=
        abs_add_le _ _
    _ < η / 2 + η / 2 := by
        refine add_lt_add_of_lt_of_le hb ?_
        rw [abs_mul, abs_of_nonneg hK0]
        exact (mul_le_mul_of_nonneg_left hdec.le hK0).trans hKη
    _ = η := add_halves η

/-! ### Regulated pieces and dominated convergence -/

/-- **A regulated Stage K piece**: `a mγ Λ` is measurable, `a mγ Λ T → A T` for every `T ≥ 4` as
`(mγ, Λ) → (0⁺, ∞)`, and `|a mγ Λ T| ≤ C/√T` for `T ≥ 4`, `0 < mγ < δ`, `Λ > Λ₀`. -/
structure IsRegPiece (a : ℝ → ℝ → ℝ → ℝ) (A : ℝ → ℝ) : Prop where
  meas : ∀ mγ Λ, Measurable (a mγ Λ)
  lim : ∀ T, 4 ≤ T → Tendsto (fun p : ℝ × ℝ => a p.1 p.2 T) (𝓝[>] 0 ×ˢ atTop) (𝓝 (A T))
  bound : ∃ C δ Λ₀ : ℝ, 0 < δ ∧ ∀ mγ Λ, 0 < mγ → mγ < δ → Λ₀ < Λ → ∀ T, 4 ≤ T →
    |a mγ Λ T| ≤ C / √T

theorem eventually_regRange {δ : ℝ} (hδ : 0 < δ) (Λ₀ : ℝ) :
    ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, 0 < p.1 ∧ p.1 < δ ∧ Λ₀ < p.2 := by
  filter_upwards [prod_mem_prod (Ioo_mem_nhdsGT hδ) (Ioi_mem_atTop Λ₀)] with p hp
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

theorem exists_of_eventually_regRange {P : ℝ × ℝ → Prop}
    (h : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, P p) :
    ∃ δ > 0, ∃ Λ₀ : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ → P (mγ, Λ) := by
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := mem_prod_iff.1 h
  obtain ⟨u, hu, hut⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ht₁
  obtain ⟨Λ₀, hΛ₀⟩ := mem_atTop_sets.1 ht₂
  exact ⟨u, hu, Λ₀, fun mγ Λ h0 h1 h2 => hsub ⟨hut ⟨h0, h1⟩, hΛ₀ Λ h2.le⟩⟩

theorem IsRegPiece.add {a a' : ℝ → ℝ → ℝ → ℝ} {A A' : ℝ → ℝ} (h : IsRegPiece a A)
    (h' : IsRegPiece a' A') :
    IsRegPiece (fun mγ Λ T => a mγ Λ T + a' mγ Λ T) (fun T => A T + A' T) where
  meas mγ Λ := (h.meas mγ Λ).add (h'.meas mγ Λ)
  lim T hT := (h.lim T hT).add (h'.lim T hT)
  bound := by
    obtain ⟨C, δ, Λ₀, hδ, hC⟩ := h.bound
    obtain ⟨C', δ', Λ₀', hδ', hC'⟩ := h'.bound
    refine ⟨C + C', min δ δ', max Λ₀ Λ₀', lt_min hδ hδ', fun mγ Λ h0 h1 h2 T hT => ?_⟩
    have b₁ := hC mγ Λ h0 (h1.trans_le (min_le_left _ _)) ((le_max_left _ _).trans_lt h2) T hT
    have b₂ := hC' mγ Λ h0 (h1.trans_le (min_le_right _ _)) ((le_max_right _ _).trans_lt h2) T hT
    rw [add_div]
    exact (abs_add_le _ _).trans (add_le_add b₁ b₂)

theorem four_le_mul_setCKSpecMass {s v : ℝ} (hs : 1 ≤ s) (hv : v ∈ Ioo (0 : ℝ) 1) :
    4 ≤ s * setCKSpecMass v := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have ht : 4 ≤ setCKSpecMass v := by
    unfold setCKSpecMass
    rw [le_div_iff₀ h1]
    nlinarith [sq_nonneg v]
  nlinarith

/-- `ρ(v)/√(s t_v) ≤ (1 - v)^{-1/2}` for `s ≥ 1`. -/
theorem rho_div_sqrt_le {s v : ℝ} (hs : 1 ≤ s) (hv : v ∈ Ioo (0 : ℝ) 1) :
    setCKSpecRho v / √(s * setCKSpecMass v) ≤ (1 - v) ^ (-(1 / 2 : ℝ)) := by
  have hw : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have h1v : 0 < 1 - v := by linarith [hv.2]
  have hT := four_le_mul_setCKSpecMass hs hv
  have hsq : 0 < √(s * setCKSpecMass v) := Real.sqrt_pos.2 (by linarith)
  have hr : 0 < √(1 - v) := Real.sqrt_pos.2 h1v
  rw [Real.rpow_neg h1v.le, ← Real.sqrt_eq_rpow, ← one_div, div_le_div_iff₀ hsq hr, one_mul]
  have hρ0 := setCKSpecRho_nonneg hv
  have hρ : setCKSpecRho v ≤ 1 / (1 - v ^ 2) := by
    unfold setCKSpecRho
    refine div_le_div_of_nonneg_right ?_ hw.le
    nlinarith [sq_nonneg v, hv.1, hv.2]
  rw [Real.le_sqrt (mul_nonneg hρ0 hr.le) (by linarith), mul_pow, Real.sq_sqrt h1v.le]
  have hρ2 : setCKSpecRho v ^ 2 ≤ (1 / (1 - v ^ 2)) ^ 2 := pow_le_pow_left₀ hρ0 hρ 2
  have hw1 : 1 - v ≤ 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have key : (1 / (1 - v ^ 2)) ^ 2 * (1 - v) ≤ setCKSpecMass v := by
    unfold setCKSpecMass
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hw]
    nlinarith
  have ht0 : 0 < setCKSpecMass v := setCKSpecMass_pos hv
  calc setCKSpecRho v ^ 2 * (1 - v) ≤ (1 / (1 - v ^ 2)) ^ 2 * (1 - v) :=
        mul_le_mul_of_nonneg_right hρ2 h1v.le
    _ ≤ setCKSpecMass v := key
    _ ≤ s * setCKSpecMass v := le_mul_of_one_le_left ht0.le hs

theorem integrableOn_one_sub_rpow :
    IntegrableOn (fun v : ℝ => (1 - v) ^ (-(1 / 2 : ℝ))) (Ioo 0 1) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := 0)
    (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left 1
  rw [sub_self, sub_zero] at h
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h

theorem rho_mul_abs_le {a : ℝ → ℝ} {C s v : ℝ} (hs : 1 ≤ s) (hv : v ∈ Ioo (0 : ℝ) 1)
    (hC : |a (s * setCKSpecMass v)| ≤ C / √(s * setCKSpecMass v)) :
    setCKSpecRho v * |a (s * setCKSpecMass v)| ≤ |C| * (1 - v) ^ (-(1 / 2 : ℝ)) := by
  have hρ := setCKSpecRho_nonneg hv
  calc setCKSpecRho v * |a (s * setCKSpecMass v)| ≤
        setCKSpecRho v * (|C| / √(s * setCKSpecMass v)) :=
        mul_le_mul_of_nonneg_left (hC.trans (div_le_div_of_nonneg_right (le_abs_self C)
          (Real.sqrt_nonneg _))) hρ
    _ = |C| * (setCKSpecRho v / √(s * setCKSpecMass v)) := by ring
    _ ≤ |C| * (1 - v) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (rho_div_sqrt_le hs hv) (abs_nonneg _)

theorem abs_add3_le (x y z c₁ c₂ : ℝ) :
    |x + c₁ * y + c₂ * z| ≤ |x| + |c₁| * |y| + |c₂| * |z| := by
  calc |x + c₁ * y + c₂ * z| ≤ |x + c₁ * y| + |c₂ * z| := abs_add_le _ _
    _ ≤ |x| + |c₁ * y| + |c₂ * z| := by gcongr; exact abs_add_le _ _
    _ = |x| + |c₁| * |y| + |c₂| * |z| := by rw [abs_mul, abs_mul]

/-- The regulated flavour-summed dispersion integral of a kernel `a`. -/
noncomputable def jDisp (a : ℝ → ℝ → ℝ → ℝ) (s₁ s₂ c₁ c₂ mγ Λ : ℝ) : ℝ :=
  ∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * (a mγ Λ (setCKSpecMass v) +
    c₁ * a mγ Λ (s₁ * setCKSpecMass v) + c₂ * a mγ Λ (s₂ * setCKSpecMass v))

/-- **Dominated convergence in the spectral variable**: for a regulated kernel of the set (c) kernel
sum, the regulated dispersion integral tends to `K(1) + c₁ K(s₁) + c₂ K(s₂)`. -/
theorem tendsto_jDisp {a : ℝ → ℝ → ℝ → ℝ} (h : IsRegPiece a setCKKernelPairSum) {s₁ s₂ : ℝ}
    (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (c₁ c₂ : ℝ) :
    Tendsto (fun p : ℝ × ℝ => jDisp a s₁ s₂ c₁ c₂ p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (kDisp 1 + c₁ * kDisp s₁ + c₂ * kDisp s₂)) := by
  obtain ⟨C, δ, Λ₀, hδ, hC⟩ := h.bound
  have hmt : Measurable setCKSpecMass := by unfold setCKSpecMass; fun_prop
  have hmρ : Measurable setCKSpecRho := by unfold setCKSpecRho; fun_prop
  have hk : ∀ s, kDisp s = ∫ v in Ioo (0 : ℝ) 1,
      setCKSpecRho v * setCKKernelPairSum (s * setCKSpecMass v) := fun s => by
    rw [kDisp, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have i₀ := integrableOn_kDisp (s := 1) le_rfl
  have i₁ := integrableOn_kDisp hs₁
  have i₂ := integrableOn_kDisp hs₂
  have i01 : IntegrableOn (fun v => setCKSpecRho v * setCKKernelPairSum (1 * setCKSpecMass v) +
      c₁ * (setCKSpecRho v * setCKKernelPairSum (s₁ * setCKSpecMass v))) (Ioo 0 1) :=
    i₀.add (i₁.const_mul c₁)
  have hlimv : kDisp 1 + c₁ * kDisp s₁ + c₂ * kDisp s₂ = ∫ v in Ioo (0 : ℝ) 1,
      setCKSpecRho v * (setCKKernelPairSum (setCKSpecMass v) +
        c₁ * setCKKernelPairSum (s₁ * setCKSpecMass v) +
        c₂ * setCKKernelPairSum (s₂ * setCKSpecMass v)) := by
    have e : ∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * (setCKKernelPairSum (setCKSpecMass v) +
        c₁ * setCKKernelPairSum (s₁ * setCKSpecMass v) +
        c₂ * setCKKernelPairSum (s₂ * setCKSpecMass v)) = ∫ v in Ioo (0 : ℝ) 1,
        ((setCKSpecRho v * setCKKernelPairSum (1 * setCKSpecMass v) +
          c₁ * (setCKSpecRho v * setCKKernelPairSum (s₁ * setCKSpecMass v))) +
          c₂ * (setCKSpecRho v * setCKKernelPairSum (s₂ * setCKSpecMass v))) :=
      setIntegral_congr_fun measurableSet_Ioo fun v _ => by simp only [one_mul]; ring
    rw [e, integral_add i01 (i₂.const_mul c₂), integral_add i₀ (i₁.const_mul c₁),
      integral_const_mul, integral_const_mul, hk, hk, hk]
  rw [hlimv]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun v => |C| * (1 + |c₁| + |c₂|) * (1 - v) ^ (-(1 / 2 : ℝ))) ?_ ?_
    (integrableOn_one_sub_rpow.const_mul _) ?_
  · refine Eventually.of_forall fun p => ?_
    have ha := h.meas p.1 p.2
    exact (hmρ.mul (((ha.comp hmt).add (measurable_const.mul
      (ha.comp (measurable_const.mul hmt)))).add (measurable_const.mul
      (ha.comp (measurable_const.mul hmt))))).aestronglyMeasurable
  · filter_upwards [eventually_regRange hδ Λ₀] with p hp
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hρ := setCKSpecRho_nonneg hv
    have b₀ := rho_mul_abs_le (a := a p.1 p.2) le_rfl hv
      (hC p.1 p.2 hp.1 hp.2.1 hp.2.2 _ (four_le_mul_setCKSpecMass le_rfl hv))
    have b₁ := rho_mul_abs_le (a := a p.1 p.2) hs₁ hv
      (hC p.1 p.2 hp.1 hp.2.1 hp.2.2 _ (four_le_mul_setCKSpecMass hs₁ hv))
    have b₂ := rho_mul_abs_le (a := a p.1 p.2) hs₂ hv
      (hC p.1 p.2 hp.1 hp.2.1 hp.2.2 _ (four_le_mul_setCKSpecMass hs₂ hv))
    simp only [one_mul] at b₀
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ]
    have tri := abs_add3_le (a p.1 p.2 (setCKSpecMass v)) (a p.1 p.2 (s₁ * setCKSpecMass v))
      (a p.1 p.2 (s₂ * setCKSpecMass v)) c₁ c₂
    calc setCKSpecRho v * |a p.1 p.2 (setCKSpecMass v) +
          c₁ * a p.1 p.2 (s₁ * setCKSpecMass v) + c₂ * a p.1 p.2 (s₂ * setCKSpecMass v)|
        ≤ setCKSpecRho v * |a p.1 p.2 (setCKSpecMass v)| +
          |c₁| * (setCKSpecRho v * |a p.1 p.2 (s₁ * setCKSpecMass v)|) +
          |c₂| * (setCKSpecRho v * |a p.1 p.2 (s₂ * setCKSpecMass v)|) := by
          nlinarith [mul_le_mul_of_nonneg_left tri hρ]
      _ ≤ |C| * (1 - v) ^ (-(1 / 2 : ℝ)) + |c₁| * (|C| * (1 - v) ^ (-(1 / 2 : ℝ))) +
          |c₂| * (|C| * (1 - v) ^ (-(1 / 2 : ℝ))) := by
          gcongr
      _ = |C| * (1 + |c₁| + |c₂|) * (1 - v) ^ (-(1 / 2 : ℝ)) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact (((h.lim _ (four_le_mul_setCKSpecMass le_rfl hv |>.trans_eq (one_mul _))).add
      ((h.lim _ (four_le_mul_setCKSpecMass hs₁ hv)).const_mul c₁)).add
      ((h.lim _ (four_le_mul_setCKSpecMass hs₂ hv)).const_mul c₂)).const_mul _

end QED.ChainProof.SetCRegDisp

end
