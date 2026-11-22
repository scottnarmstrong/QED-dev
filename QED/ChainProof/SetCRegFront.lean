/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLo
public import QED.ChainProof.SetCRegDispShellKerC
public import QED.ChainProof.SetCPauliRepB

/-!
# Set (c): the regulator limit from the class kernels, and its frontier

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The regulator
limit `SetCRegLimitB P₀ b` of `b = setCPauliB P₀ (setCBetaM P₀ βᴮ)` follows from the dispersion
form of the class values (`QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces`). The
counterterm kernels are fixed: `uCBOf P₀ (fun _ => cb01KerC P₀)` (the corrected sign of the
placements `k = 0, 1`) and `uShare P₀ (shellKer₁C P₀) (massKer P₀ (shellKer₀ P₀) (shellKer₁C P₀))`
(the shell slope with its longitudinal part).

**Only the real part matters.** `setCPauliB` is the real part of the class sum, so the matching
of `setCRegLimitDisp_of_pieces` (a real identity for the kernel sum) can be replaced by the
regulator limit of the real part of the total kernel, `setCKerRe` (`setCRegLimitDisp_of_kernels`).

## Main statements

* `kerRe`: `64π⁶/e⁶ · Re[(1/i)(∑ uBD + ∑ uCB + ∑ uS)]`;
* **`setCRegLimitDisp_of_kernels`**: the regulator limit from the dispersion form of the class
  values and the regulator limit `IsRegPiece (kerRe …) setCKKernelPairSum` of the total kernel;
* `uCBC`, `uSC`, `setCKerRe`: the fixed counterterm kernels and the total kernel;
* **`setCRegLimitB_of_leaves`**: `SetCRegLimitB P₀ (setCPauliB P₀ (setCBetaM P₀ βᴮ))` from
  `hMainBD` (main classes), `ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀)` (the VP-share leaf
  `hCtS`), `CBLoBEq P₀` (the mass part of `hCtCB`) and the regulator limit of `setCKerRe`;
* **`setCRegLimitB_of_match`**: the same with the matching `hMatch` against the five regulated
  Stage K pieces in place of the last input.
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCK QED.ChainProof.SetCPauli QED.ChainProof.SetCMain

/-! ### The regulator limit from the real part of the total kernel -/

/-- The real part of the total kernel in the normalization of the Stage K kernel sum:
`64π⁶/e⁶ · Re[(1/i)(∑ uBD + ∑ uCB + ∑ uS)]`. -/
noncomputable def kerRe (P₀ : Params) (uBD : Fin 12 → ℝ → ℝ → ℝ → ℂ)
    (uCB uS : Fin 5 → ℝ → ℝ → ℝ → ℂ) (mγ Λ T : ℝ) : ℝ :=
  64 * π ^ 6 / P₀.e ^ 6 *
    ((1 / I) * (∑ i, uBD i mγ Λ T + ∑ k, uCB k mγ Λ T + ∑ k, uS k mγ Λ T)).re

section Kernels

variable {P₀ : Params} {βM : MainIdx → ClsPauliVal} {uBD : Fin 12 → ℝ → ℝ → ℝ → ℂ}
  {uCB uS : Fin 5 → ℝ → ℝ → ℝ → ℂ}

theorem re_dispPVF (m M₁ M₂ c₁ c₂ : ℝ) (u : ℝ → ℂ) (v : ℝ) :
    (dispPVF m M₁ M₂ c₁ c₂ u v).re = setCKSpecRho v * ((u (setCKSpecMass v)).re +
      c₁ * (u (M₁ ^ 2 / m ^ 2 * setCKSpecMass v)).re +
      c₂ * (u (M₂ ^ 2 / m ^ 2 * setCKSpecMass v)).re) := by
  simp only [dispPVF, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, zero_mul, sub_zero, add_zero]

/-- **The canonical value from the real part of the total kernel**: over admissible data,
`setCPauliB P₀ βᴹ = e⁶/(64π⁶) jDisp (kerRe …)`. -/
theorem setCPauliB_eq_kerRe
    (hMainBD : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ i : Fin 12,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBD i mγ Λ) (βM (.inl i) M₁ M₂ c₁ c₂ mγ Λ D s +
        βM (.inr (i, 0)) M₁ M₂ c₁ c₂ mγ Λ D s + βM (.inr (i, 1)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtCB : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uCB k mγ Λ) (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtS : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uS k mγ Λ) (ctPauliAll P₀ (.inr (.inr k)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (he : P₀.e ≠ 0) {M₁ M₂ c₁ c₂ mγ Λ : ℝ} (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂)
    (hc : 1 + c₁ + c₂ = 0) (hc' : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (hmγ : 0 < mγ)
    (hmΛ : mγ < Λ) (hm2 : mγ < 2 * P₀.m) :
    setCPauliB P₀ βM mγ Λ M₁ M₂ = P₀.e ^ 6 / (64 * π ^ 6) *
      jDisp (kerRe P₀ uBD uCB uS) (M₁ ^ 2 / P₀.m ^ 2) (M₂ ^ 2 / P₀.m ^ 2) c₁ c₂ mγ Λ := by
  have hm : 0 < P₀.m := by linarith
  obtain ⟨D, s, hA⟩ := exists_setCAdm he hM₁ hM₂ hc hc' hmγ hmΛ hm2
  have hex : ∃ x, SetCAdmAt P₀ mγ Λ M₁ M₂ x := ⟨(c₁, c₂, D, s), hA⟩
  have hx : SetCAdm P₀ M₁ M₂ hex.choose.1 hex.choose.2.1 mγ Λ hex.choose.2.2.1
      hex.choose.2.2.2 := hex.choose_spec
  obtain ⟨e₁, e₂⟩ := QED.ChainProof.SetANestedAt.pvCoeffs_unique hm hM₁ hx.2.2.1 hx.2.2.2.1 hc hc'
  simp only [setCPauliB, hex, ↓reduceDIte]
  set x := hex.choose
  have hB := IsDispPV.sum Finset.univ fun i _ =>
    hMainBD M₁ M₂ x.1 x.2.1 mγ Λ x.2.2.1 x.2.2.2 hx i
  have hC := IsDispPV.sum Finset.univ fun k _ =>
    hCtCB M₁ M₂ x.1 x.2.1 mγ Λ x.2.2.1 x.2.2.2 hx k
  have hS := IsDispPV.sum Finset.univ fun k _ =>
    hCtS M₁ M₂ x.1 x.2.1 mγ Λ x.2.2.1 x.2.2.2 hx k
  have hT := ((hB.add hC).add hS).const_mul (1 / I)
  unfold setCClassSum
  rw [sum_mainIdx, sum_ctIdx, ← add_assoc, hT.2, ← RCLike.re_to_complex, ← integral_re hT.1,
    e₁, e₂, jDisp, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
  rw [RCLike.re_to_complex, re_dispPVF]
  simp only [kerRe]
  have he6 : P₀.e ^ 6 ≠ 0 := pow_ne_zero 6 he
  have hπ : (64 * π ^ 6 : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The regulator limit from the dispersion form of the class values and the regulator limit
of the real part of the total kernel.** -/
theorem setCRegLimitDisp_of_kernels (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hMainBD : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ i : Fin 12,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBD i mγ Λ) (βM (.inl i) M₁ M₂ c₁ c₂ mγ Λ D s +
        βM (.inr (i, 0)) M₁ M₂ c₁ c₂ mγ Λ D s + βM (.inr (i, 1)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtCB : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uCB k mγ Λ) (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtS : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uS k mγ Λ) (ctPauliAll P₀ (.inr (.inr k)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hReg : IsRegPiece (kerRe P₀ uBD uCB uS) setCKKernelPairSum) :
    SetCRegLimitDisp P₀ (setCPauliB P₀ βM) := by
  refine setCRegLimitDisp_of_fixLim hm fun M₁ M₂ c₁ c₂ hM₁ hM₂ hc hc' η hη => ?_
  set K : ℝ := P₀.e ^ 6 / (64 * π ^ 6) with hK
  have hlim := (tendsto_jDisp hReg (one_le_sq_div hm hM₁) (one_le_sq_div hm hM₂) c₁ c₂).const_mul K
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := exists_of_eventually_regRange (Metric.tendsto_nhds.1 hlim η hη)
  refine ⟨min δ (min 1 (2 * P₀.m)), lt_min hδ (lt_min one_pos (by linarith)), max Λ₀ 1,
    fun mγ Λ h0 h1 h2 => ?_⟩
  have hδ' : mγ < δ := h1.trans_le (min_le_left _ _)
  have h1' : mγ < 1 := h1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h2m : mγ < 2 * P₀.m := h1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hΛ : Λ₀ < Λ := (le_max_left _ _).trans_lt h2
  have hmΛ : mγ < Λ := h1'.trans ((le_max_right _ _).trans_lt h2)
  have hd := hΛ₀ mγ Λ h0 hδ' hΛ
  rw [Real.dist_eq] at hd
  rw [setCPauliB_eq_kerRe hMainBD hCtCB hCtS he hM₁ hM₂ hc hc' h0 hmΛ h2m]
  have e : P₀.e ^ 6 * kDispPV P₀.m M₁ M₂ c₁ c₂ / (64 * π ^ 6) =
      K * (kDisp 1 + c₁ * kDisp (M₁ ^ 2 / P₀.m ^ 2) + c₂ * kDisp (M₂ ^ 2 / P₀.m ^ 2)) := by
    rw [hK, kDispPV]
    ring
  rw [e]
  exact hd

end Kernels

/-! ### The fixed counterterm kernels and the frontier -/

/-- The kernels of the placements `CBₖ + CDₖ,₀ + CDₖ,₁`: `cbVPKer` for `k ≥ 2`, the corrected
`cb01KerC` for `k = 0, 1`. -/
noncomputable abbrev uCBC (P₀ : Params) : Fin 5 → ℝ → ℝ → ℝ → ℂ :=
  uCBOf P₀ fun _ => cb01KerC P₀

/-- The kernels of the VP-share classes `Sₖ`, with the shell slope `shellKer₁C`. -/
noncomputable abbrev uSC (P₀ : Params) : Fin 5 → ℝ → ℝ → ℝ → ℂ :=
  uShare P₀ (shellKer₁C P₀) (massKer P₀ (shellKer₀ P₀) (shellKer₁C P₀))

/-- The real part of the total kernel with the fixed counterterm kernels. -/
noncomputable abbrev setCKerRe (P₀ : Params) (uBD : Fin 12 → ℝ → ℝ → ℝ → ℂ) :
    ℝ → ℝ → ℝ → ℝ :=
  kerRe P₀ uBD (uCBC P₀) (uSC P₀)

/-- **The regulator limit of set (c) from its leaves.** Inputs: `hMainBD` (the dispersion form
of the main classes `repB i + repD i 0 + repD i 1`, kernels `uBD i`), `hS` (the VP-share leaf
`hCtS`: the shell value and slope in dispersion form), `hB` (the mass part `CBLoBEq` of `hCtCB`),
and `hReg` (the regulator limit of the total kernel towards the Stage K kernel sum). -/
theorem setCRegLimitB_of_leaves {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    {βB : Fin 12 → ClsPauliVal} {uBD : Fin 12 → ℝ → ℝ → ℝ → ℂ}
    (hMainBD : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ i : Fin 12,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBD i mγ Λ) (βB i M₁ M₂ c₁ c₂ mγ Λ D s +
        clsPauliLim mainFam P₀ (.inr (i, 0)) M₁ M₂ c₁ c₂ mγ Λ D s +
        clsPauliLim mainFam P₀ (.inr (i, 1)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hS : ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀)) (hB : CBLoBEq P₀)
    (hReg : IsRegPiece (setCKerRe P₀ uBD) setCKKernelPairSum) :
    SetCRegLimitB P₀ (setCPauliB P₀ (setCBetaM P₀ βB)) :=
  setCRegLimitB_of_disp (setCRegLimitDisp_of_kernels he hm (βM := setCBetaM P₀ βB)
    (fun M₁ M₂ c₁ c₂ mγ Λ D s hA i => hMainBD M₁ M₂ c₁ c₂ mγ Λ D s hA i)
    (isDispPV_CB_of_loB he hB) (isDispPV_S_of_shell he hS) hReg)

/-- **The regulator limit of set (c) from its leaves, with the matching against the five
regulated Stage K pieces.** -/
theorem setCRegLimitB_of_match {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    {βB : Fin 12 → ClsPauliVal} {uBD : Fin 12 → ℝ → ℝ → ℝ → ℂ}
    {aL aSI aCI aX aSC : ℝ → ℝ → ℝ → ℝ}
    (hMainBD : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ i : Fin 12,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBD i mγ Λ) (βB i M₁ M₂ c₁ c₂ mγ Λ D s +
        clsPauliLim mainFam P₀ (.inr (i, 0)) M₁ M₂ c₁ c₂ mγ Λ D s +
        clsPauliLim mainFam P₀ (.inr (i, 1)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hS : ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀)) (hB : CBLoBEq P₀)
    (hMatch : ∀ mγ Λ T : ℝ, 0 < mγ → mγ < Λ → 4 ≤ T →
      (1 / I) * (∑ i, uBD i mγ Λ T + ∑ k, uCBC P₀ k mγ Λ T + ∑ k, uSC P₀ k mγ Λ T) =
        ((P₀.e ^ 6 / (64 * π ^ 6) *
          (aL mγ Λ T + aSI mγ Λ T + aCI mγ Λ T + aX mγ Λ T + aSC mγ Λ T) : ℝ) : ℂ))
    (hL : IsRegPiece aL SetCK.lPair) (hSI : IsRegPiece aSI SetCK.selfIn)
    (hCI : IsRegPiece aCI SetCK.cornIn)
    (hX : IsRegPiece aX fun T => SetCK.crossUnit 0 T + SetCK.crossUnit T 0)
    (hSC : IsRegPiece aSC fun T => SetCK.scOutS T + SetCK.scOutC T) :
    SetCRegLimitB P₀ (setCPauliB P₀ (setCBetaM P₀ βB)) :=
  setCRegLimitB_of_disp (setCRegLimitDisp_of_pieces he hm (βM := setCBetaM P₀ βB)
    (fun M₁ M₂ c₁ c₂ mγ Λ D s hA i => hMainBD M₁ M₂ c₁ c₂ mγ Λ D s hA i)
    (isDispPV_CB_of_loB he hB) (isDispPV_S_of_shell he hS) hMatch hL hSI hCI hX hSC)

end QED.ChainProof.SetCRegDisp

end
