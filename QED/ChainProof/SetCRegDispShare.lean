/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShareVal
public import QED.ChainProof.SetCLinkFinal
public import QED.ChainProof.SetCLinkVInput
public import QED.ChainProof.SetCPauliSum

/-!
# Set (c): the five VP-share classes in dispersion form, from the dispersion form of the share

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS` of
`QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces`. The class values are linear in the share
(`QED/ChainProof/SetCRegDispShareVal.lean`), and the share is affine in the analytic data of
`QED/ChainProof/SetCLinkShareAlg.lean`: with `σ₀, σ₁` the shell value and slope of the selected
order-`4` self-energy of `dZero D` (the VP-inserted two-loop self-energy and its two `δ₃`
classes), (Sc₂) reads `e⁴ s₂ = σ₁`, `e⁴ s_m m = σ₀ + σ₁ m`, and (WI-s) gives `s₁ = s₂`. So the
dispersion form passes from `σ₀, σ₁` to the share and from the share to the five classes, by
linearity (`IsDispPV.const_mul`, `IsDispPV.add`).

## Main statements

* `ShareDisp P₀ w₂ wm`: at every admissible datum, `e⁴ s₂` and `e⁴ s_m` are in dispersion form
  with kernels `w₂ m_γ Λ`, `wm m_γ Λ`;
* `uShare P₀ w₂ wm k`: the kernel of `Sₖ`, `i e²/(4π²) (ΔV_k w₂ + ΔV_m wm)` for `k = 0, 1` and
  `i e² B(0)/(8π²) w₂` for `k = 2, 3, 4`;
* `setCAdm_share_fst`: (WI-s) at an admissible datum, `s₁ = s₂`;
* **`isDispPV_S_of_share`**: `hCtS` with kernels `uShare P₀ w₂ wm`, from `ShareDisp P₀ w₂ wm`;
* `ShellDisp P₀ w₀ w₁`: at every admissible datum, the shell value `σ₀` and the shell slope `σ₁`
  of the selected self-energy of `dZero D` are in dispersion form with kernels `w₀`, `w₁`;
* `shareDisp_of_shellDisp`: `ShareDisp P₀ w₁ (w₀/m + w₁)`;
* **`isDispPV_S_of_shell`**: `hCtS` with kernels `uShare P₀ w₁ (w₀/m + w₁)` from
  `ShellDisp P₀ w₀ w₁`.

## The expected kernels (not proved here)

By the spectral form of the bubble (`QED.TwoLoop.VPHalfAt.vpLoopEps_eq_spectral`), the
subtracted VP insertion is the `ρ`-superposition of a photon of mass² `T m²`, so `w₀`, `w₁`
should be `e⁴` times the shell value and slope of the one-loop self-energy with photon function
`(e²/(4π²)) k⁴/(k² + T m²) D(k²)²`, `D` the Pauli–Villars photon. Proving `ShellDisp` is the
exchange of the spectral integral with the `ε → 0⁺` limit of the selected self-energy and with
the derivative on the shell (the self-energy analogue of the fixed-`q` route
`QED.TwoLoop.VPHalfAt*`).
-/

@[expose] public section

open Complex Real Set Filter Topology
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-- **The share in dispersion form**, kernels `w₂` for `e⁴ s₂` and `wm` for `e⁴ s_m`. -/
def ShareDisp (P₀ : Params) (w₂ wm : ℝ → ℝ → ℝ → ℂ) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    IsDispPV P₀.m M₁ M₂ c₁ c₂ (w₂ mγ Λ) ((P₀.e ^ 4 * s.2.1 : ℝ) : ℂ) ∧
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (wm mγ Λ) ((P₀.e ^ 4 * s.2.2 : ℝ) : ℂ)

/-- **The kernel of the VP-share class `Sₖ`** from the share kernels `w₂`, `wm`. -/
noncomputable def uShare (P₀ : Params) (w₂ wm : ℝ → ℝ → ℝ → ℂ) (k : Fin 5) (mγ Λ T : ℝ) : ℂ :=
  if (k : ℕ) < 2 then
    sCoefLine P₀ * ((dVk P₀.m mγ Λ : ℂ) * w₂ mγ Λ T + (dVm P₀.m mγ Λ : ℂ) * wm mγ Λ T)
  else sCoefVtx P₀ mγ Λ * w₂ mγ Λ T

variable {P₀ : Params}

/-- **(WI-s) at an admissible datum**: `s₁ = s₂`. -/
theorem setCAdm_share_fst (he : P₀.e ≠ 0) {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt}
    {s : ℝ × ℝ × ℝ} (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) : s.1 = s.2.1 := by
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, -, hm2, hD, hs⟩ := hA
  have hm : 0 < P₀.m := by linarith
  have hb₁ := QED.GradedProof.RPi4.leptonFlavors_blockPV₁ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) hPV₁ (fun ℓ => ℓ.elim0)
  have hb₂ := QED.GradedProof.RPi4.leptonFlavors_blockPV₂ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) hPV₂ (fun ℓ => ℓ.elim0)
  exact SetCLink.isVPShareOnShell_d₁_eq_d₂_c (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep P₀.m he hm
    (regFlavors_mass_ge_c hM₁ hM₂) hmγ hΛ QED.GradedProof.RPi4.leptonRep_idem hb₁ hb₂
    (isRenormalizedThrough_one_of_two hD) s hs

/-- **`hCtS` from the dispersion form of the share**: every VP-share class `Sₖ` is in dispersion
form with kernel `uShare P₀ w₂ wm k`. -/
theorem isDispPV_S_of_share (he : P₀.e ≠ 0) {w₂ wm : ℝ → ℝ → ℝ → ℂ}
    (hS : ShareDisp P₀ w₂ wm) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uShare P₀ w₂ wm k mγ Λ)
        (ctPauliAll P₀ (.inr (.inr k)) M₁ M₂ c₁ c₂ mγ Λ D s) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA k
  obtain ⟨h₂, hm'⟩ := hS M₁ M₂ c₁ c₂ mγ Λ D s hA
  obtain ⟨-, -, -, -, hmγ, -, hmΛ, hm2, -, -⟩ := id hA
  have hm : 0 < P₀.m := by linarith
  by_cases hk : (k : ℕ) < 2
  · have e : uShare P₀ w₂ wm k mγ Λ = fun T => sCoefLine P₀ *
        ((dVk P₀.m mγ Λ : ℂ) * w₂ mγ Λ T + (dVm P₀.m mγ Λ : ℂ) * wm mγ Λ T) := by
      funext T
      simp only [uShare, hk, ite_true]
    rw [e, ctPauliAll_S_line he hm hmγ hmΛ k hk]
    exact ((h₂.const_mul _).add (hm'.const_mul _)).const_mul _
  · have e : uShare P₀ w₂ wm k mγ Λ = fun T => sCoefVtx P₀ mγ Λ * w₂ mγ Λ T := by
      funext T
      simp only [uShare, hk, ite_false]
    rw [e, ctPauliAll_S_vtx he hm k (by omega), setCAdm_share_fst he hA]
    exact h₂.const_mul _

/-! ### The share from the shell value and slope of the self-energy -/

/-- **The shell data of the VP-inserted self-energy in dispersion form**: at every admissible
datum, the shell value `σ₀` and slope `σ₁` of every near-shell limit `A p̸ + B m` of the selected
order-`4` self-energy of `dZero D` are in dispersion form with kernels `w₀ m_γ Λ`, `w₁ m_γ Λ`. -/
def ShellDisp (P₀ : Params) (w₀ w₁ : ℝ → ℝ → ℝ → ℂ) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ r : ℝ, 0 < r →
    ∀ A B : ℝ → ℂ, SetCLink.SELimitSel (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (SetCLink.dZero D) r A B → ∀ σ₀ σ₁ : ℝ,
    A (-P₀.m ^ 2) * ((-P₀.m : ℝ) : ℂ) + B (-P₀.m ^ 2) * P₀.m = σ₀ →
    HasDerivAt (QED.GradedProof.GEx2.shellFun A B P₀.m) σ₁ (-P₀.m) →
    IsDispPV P₀.m M₁ M₂ c₁ c₂ (w₀ mγ Λ) σ₀ ∧ IsDispPV P₀.m M₁ M₂ c₁ c₂ (w₁ mγ Λ) σ₁

/-- The mass-share kernel `w₀/m + w₁` (from `e⁴ s_m = σ₀/m + σ₁`). -/
noncomputable def massKer (P₀ : Params) (w₀ w₁ : ℝ → ℝ → ℝ → ℂ) (mγ Λ T : ℝ) : ℂ :=
  1 / (P₀.m : ℂ) * w₀ mγ Λ T + w₁ mγ Λ T

/-- **The share in dispersion form from the shell data**: `e⁴ s₂ = σ₁`, `e⁴ s_m = σ₀/m + σ₁`. -/
theorem shareDisp_of_shellDisp {w₀ w₁ : ℝ → ℝ → ℝ → ℂ} (hS : ShellDisp P₀ w₀ w₁) :
    ShareDisp P₀ w₁ (massKer P₀ w₀ w₁) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, -, hm2, -, hs⟩ := id hA
  have hm : 0 < P₀.m := by linarith
  have hb₁ := QED.GradedProof.RPi4.leptonFlavors_blockPV₁ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) hPV₁ (fun ℓ => ℓ.elim0)
  have hb₂ := QED.GradedProof.RPi4.leptonFlavors_blockPV₂ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) hPV₂ (fun ℓ => ℓ.elim0)
  have h₁ := QED.GradedProof.GEx2.sum_eq_zero_of_blocks Graded.leptonRep
    QED.GradedProof.RPi4.leptonRep_idem _ hb₁
  have h₂ := QED.GradedProof.GEx2.sum_eq_zero_of_blocks Graded.leptonRep
    QED.GradedProof.RPi4.leptonRep_idem _ hb₂
  have hmass := regFlavors_mass_ge_c (mγ := mγ) (Λ := Λ) (c₁ := c₁) (c₂ := c₂) hM₁ hM₂
  obtain ⟨r, hr, A, B, hlim, σ₀, σ₁, hσ₀, hσ₁⟩ := SetCLink.vpSEInput
    (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (SetCLink.dZero D) P₀.m hm
    hmass hmγ hΛ h₁ h₂
  obtain ⟨c, hc⟩ := SetCLink.vpVInput (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D P₀.m hm hmass hmγ hΛ h₁ h₂
  obtain ⟨⟨e2, e3⟩, -⟩ := (SetCLink.isVPShareOnShell_iff (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D hm hr hlim hσ₀ hσ₁ hc s).1 hs
  obtain ⟨d₀, d₁⟩ := hS M₁ M₂ c₁ c₂ mγ Λ D s hA r hr A B hlim σ₀ σ₁ hσ₀ hσ₁
  have e2' : P₀.e ^ 4 * s.2.1 = σ₁ := e2
  have e3' : P₀.e ^ 4 * s.2.2 * P₀.m = σ₀ + σ₁ * P₀.m := e3
  refine ⟨by rw [e2']; exact d₁, ?_⟩
  have hv : ((P₀.e ^ 4 * s.2.2 : ℝ) : ℂ) = 1 / (P₀.m : ℂ) * σ₀ + σ₁ := by
    have hm' : (P₀.m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
    have : ((P₀.e ^ 4 * s.2.2 : ℝ) : ℂ) * P₀.m = σ₀ + σ₁ * P₀.m := by exact_mod_cast e3'
    field_simp
    linear_combination this
  rw [hv]
  exact (d₀.const_mul _).add d₁

/-- **`hCtS` from the dispersion form of the shell data**: every VP-share class `Sₖ` is in
dispersion form with kernel `uShare P₀ w₁ (w₀/m + w₁) k`. -/
theorem isDispPV_S_of_shell (he : P₀.e ≠ 0) {w₀ w₁ : ℝ → ℝ → ℝ → ℂ}
    (hS : ShellDisp P₀ w₀ w₁) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uShare P₀ w₁ (massKer P₀ w₀ w₁) k mγ Λ)
        (ctPauliAll P₀ (.inr (.inr k)) M₁ M₂ c₁ c₂ mγ Λ D s) :=
  isDispPV_S_of_share he (shareDisp_of_shellDisp hS)

end QED.ChainProof.SetCRegDisp

end
