/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegLimCt
public import QED.ChainProof.SetANestedAtValUniq
public import QED.GradedProof.RPi4Reduce

/-!
# Set (c): the class sum of the Pauli limit does not depend on the admissible data

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hsum` of
`QED.ChainProof.SetCPauli.isFormFactorPair_vertexSetC_pauli_limit_of_mainB`. The per-class Pauli
values are functions of the full set (c) data `M₁ M₂ c₁ c₂ m_γ Λ D s`, while `b` may depend on
`m_γ, Λ, M₁, M₂` only. At fixed `m_γ, Λ, M₁, M₂` the admissible data (`SetCAdm`) are unique up to
the levels `≥ 2` of `D`:

* `c₁`, `c₂` by the Pauli–Villars conditions (`QED.ChainProof.SetANestedAt.pvCoeffs_unique`);
* the levels `0` and `1` of `D` by the uniqueness halves of the sealed (G-ex₁) and (G-ex₂)
  (`QED.ChainProof.SetANestedAt.agreeBelow_two`, through `QED.Graded.existsUnique_withLevel_zero`
  and `QED.Graded.existsUnique_withLevel_one`);
* `s` by (G-ex-s) (`QED.ChainProof.SetCLink.existsUnique_isVPShareOnShell_c`), since the share
  conditions read only the levels `0` and `1` (`isVPShareOnShell_congr`, by (G-loc)).

## Main statements

* **`setCAdm_unique`**: two admissible data at the same `m_γ, Λ, M₁, M₂` have the same `c₁`,
  `c₂`, `s`, and agree on the levels `0`, `1` of `D`;
* `ClsCanon P₀ β`: the class value `β` is the same at all admissible data with the same
  `m_γ, Λ, M₁, M₂`; `ClsLow β`: `β` reads `D` only through its levels `0`, `1`
  (`ClsLow.canon`);
* **`ctPauliAll_canon`**: the 20 counterterm values `ctPauliAll P₀ r` are canonical (`CB0`,
  `CB1` through their explicit Phase 4 value `cb01Zero`);
* `setCClassSum`, **`setCPauliB`**: the class sum `(1/i)(∑ βᴹ + ∑ ctPauliAll)` and its real part
  at a chosen admissible datum (`0` if there is none);
* **`setCPauliB_hsum`**: for canonical main values `βᴹ` and a class sum with vanishing real part
  `∑ βᴹ + ∑ ctPauliAll` (reality, `QED/ChainProof/SetCPauliSumReal.lean`), the input `hsum` holds
  with `b = setCPauliB P₀ βᴹ`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params Contraction)

namespace QED.ChainProof.SetCPauli

open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.ChainProof.SetANestedAt (AgreeBelow agreeBelow_two pvCoeffs_unique)

/-! ### The VP share reads only the levels `0` and `1` -/

section Share

variable {F : Type} [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem agreeBelow_withLevel_one {D D' : Graded.Counterterms F} (h : AgreeBelow D D' 2)
    (s : ℝ × ℝ × ℝ) :
    AgreeBelow (D.withLevel 1 (fun _ => s) (D.d₃ 1)) (D'.withLevel 1 (fun _ => s) (D'.d₃ 1)) 2 := by
  refine ⟨fun f k hk => ?_, fun k hk => ?_⟩
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · obtain ⟨a, b, c⟩ := h.1 f 0 (by norm_num)
      simp [Graded.Counterterms.withLevel, a, b, c]
    · simp [Graded.Counterterms.withLevel]
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · simp [Graded.Counterterms.withLevel, h.2 0 (by norm_num)]
    · simp [Graded.Counterterms.withLevel, h.2 1 (by norm_num)]

/-- **The share conditions read only the levels `0`, `1`** (by (G-loc)). -/
theorem isVPShareOnShell_congr (P : Params) (Φ : Lepton.Flavors F) {D D' : Graded.Counterterms F}
    (h : AgreeBelow D D' 2) (s : ℝ × ℝ × ℝ) :
    ThreeLoop.IsVPShareOnShell P Φ D s ↔ ThreeLoop.IsVPShareOnShell P Φ D' s := by
  have h' := agreeBelow_withLevel_one h s
  have eS : ∀ (P' : Params)
      (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 0 κ → Graded.Grading κ → Prop)
      (p : Fin 4 → ℝ),
      Graded.selfEnergySelPart P' Φ (D.withLevel 1 (fun _ => s) (D.d₃ 1)) Sel Φ.openLine 2 p =
        Graded.selfEnergySelPart P' Φ (D'.withLevel 1 (fun _ => s) (D'.d₃ 1)) Sel Φ.openLine 2
          p := by
    intro P' Sel p
    ext α β
    simp only [Graded.selfEnergySelPart, Matrix.of_apply]
    rw [Graded.selectedPart_congr P' _ _ _ 1 0 _ (2 * 2) (fun f k hk => h'.1 f k (by omega))
      (fun k hk => h'.2 k (by omega))]
  have eV : ∀ (P' : Params) (Φ' : Lepton.Flavors F)
      (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Graded.Grading κ → Prop)
      (p : Fin 4 → ℝ) (μ : Fin 4),
      Graded.familyVertex P' Φ' (D.withLevel 1 (fun _ => s) (D.d₃ 1)) Sel (2 * 2 + 1) p p μ =
        Graded.familyVertex P' Φ' (D'.withLevel 1 (fun _ => s) (D'.d₃ 1)) Sel (2 * 2 + 1) p p
          μ := by
    intro P' Φ' Sel p μ
    ext i j
    simp only [Graded.familyVertex, Matrix.of_apply]
    rw [Graded.selectedPart_congr P' _ _ _ 1 1 _ (2 * 2 + 1) (fun f k hk => h'.1 f k (by omega))
      (fun k hk => h'.2 k (by omega))]
  simp only [ThreeLoop.IsVPShareOnShell, Graded.IsOnShellSelAt, Graded.IsChargeNormalizedSelAt,
    eS, eV]

end Share

/-! ### Uniqueness of the admissible data -/

variable {P₀ : Params}

theorem regFlavors_mass_ge_c {M₁ M₂ c₁ c₂ mγ Λ : ℝ} (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) :
    ∀ g, P₀.m ≤ (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).mass g :=
  QED.GradedProof.RPi4.le_leptonFlavors_mass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hM₁ hM₂
    (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0)

/-- **Two admissible data at the same `m_γ, Λ, M₁, M₂`** have the same `c₁`, `c₂`, `s`, and
their counterterms agree on the levels `0`, `1`. -/
theorem setCAdm_unique (he : P₀.e ≠ 0) {M₁ M₂ c₁ c₂ c₁' c₂' mγ Λ : ℝ} {D D' : RegCt}
    {s s' : ℝ × ℝ × ℝ} (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s)
    (hA' : SetCAdm P₀ M₁ M₂ c₁' c₂' mγ Λ D' s') :
    c₁ = c₁' ∧ c₂ = c₂' ∧ AgreeBelow D D' 2 ∧ s = s' := by
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, -, hm2, hD, hs⟩ := hA
  obtain ⟨-, -, hPV₁', hPV₂', -, -, -, -, hD', hs'⟩ := hA'
  have hm : 0 < P₀.m := by linarith
  obtain ⟨rfl, rfl⟩ := pvCoeffs_unique hm hM₁ hPV₁ hPV₂ hPV₁' hPV₂'
  have hb₁ := QED.GradedProof.RPi4.leptonFlavors_blockPV₁ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) hPV₁ (fun ℓ => ℓ.elim0)
  have hb₂ := QED.GradedProof.RPi4.leptonFlavors_blockPV₂ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) hPV₂ (fun ℓ => ℓ.elim0)
  have hAg : AgreeBelow D D' 2 := agreeBelow_two (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) Graded.leptonRep P₀.m he hm (regFlavors_mass_ge_c hM₁ hM₂)
    hmγ hΛ QED.GradedProof.RPi4.leptonRep_idem
    (QED.GradedProof.RPi4.leptonFlavors_sum_coeff _ _ hPV₁ fun ℓ => ℓ.elim0)
    (QED.GradedProof.RPi4.leptonFlavors_sum_coeff_mass _ _ hPV₂ fun ℓ => ℓ.elim0) hb₁ hb₂ hD hD'
  refine ⟨rfl, rfl, hAg, ?_⟩
  have hs'' := (isVPShareOnShell_congr _ _ hAg s').2 hs'
  exact (SetCLink.existsUnique_isVPShareOnShell_c (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep P₀.m he hm
    (regFlavors_mass_ge_c hM₁ hM₂) hmγ hΛ QED.GradedProof.RPi4.leptonRep_idem hb₁ hb₂
    (isRenormalizedThrough_one_of_two hD)).unique hs hs''

/-! ### Canonical class values -/

/-- **A canonical class value**: `β` takes the same value at all admissible data with the same
`m_γ, Λ, M₁, M₂`. -/
def ClsCanon (P₀ : Params) (β : ClsPauliVal) : Prop :=
  ∀ M₁ M₂ c₁ c₂ c₁' c₂' mγ Λ D D' s s', SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    SetCAdm P₀ M₁ M₂ c₁' c₂' mγ Λ D' s' →
      β M₁ M₂ c₁ c₂ mγ Λ D s = β M₁ M₂ c₁' c₂' mγ Λ D' s'

/-- The class value `β` reads the counterterms `D` only through their levels `0` and `1`. -/
def ClsLow (β : ClsPauliVal) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ (D D' : RegCt) s, AgreeBelow D D' 2 →
    β M₁ M₂ c₁ c₂ mγ Λ D s = β M₁ M₂ c₁ c₂ mγ Λ D' s

/-- **A class value reading only the levels `0`, `1` of `D` is canonical.** -/
theorem ClsLow.canon (he : P₀.e ≠ 0) {β : ClsPauliVal} (h : ClsLow β) : ClsCanon P₀ β := by
  intro M₁ M₂ c₁ c₂ c₁' c₂' mγ Λ D D' s s' hA hA'
  obtain ⟨rfl, rfl, hAg, rfl⟩ := setCAdm_unique he hA hA'
  exact h M₁ M₂ c₁ c₂ mγ Λ D D' s hAg

section Params

variable {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D D' : RegCt} (h : AgreeBelow D D' 2) (s : ℝ × ℝ × ℝ)
include h

theorem ctParamsLevel_shareCt_congr {n : ℕ} (hn : n < 2) :
    SetCLink.ctParamsLevel (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) n =
      SetCLink.ctParamsLevel (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D' s) n := by
  have h' := agreeBelow_withLevel_one h s
  obtain ⟨a, b, c⟩ := h'.1 (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).openLine n hn
  unfold SetCLink.ctParamsLevel
  rw [a, b, c, h'.2 n hn]

theorem sParams_congr : sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s = sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D' s :=
  ctParamsLevel_shareCt_congr h s (by norm_num)

theorem cdParams_congr :
    cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s = cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D' s :=
  ctParamsLevel_shareCt_congr h s (by norm_num)

theorem cbW_congr : cbW P₀ D s = cbW P₀ D' s := by
  obtain ⟨a, -, -⟩ := (agreeBelow_withLevel_one h s).1 (.inl 0) 0 (by norm_num)
  unfold cbW
  rw [a]

theorem cbParams_congr (ε : ℝ) :
    cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s ε = cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D' s ε := by
  obtain ⟨-, b, c⟩ := (agreeBelow_withLevel_one h s).1 (.inl 0) 0 (by norm_num)
  unfold cbParams
  rw [b, c]

end Params

/-! ### The classes `CB0`, `CB1` -/

/-- The Phase 4 value of the even quotient of `CB0` (`d = 1`), `CB1` (`d = 0`) at the parameters
`Pc` (`QED.ChainProof.SetCPauli.tendsto_evenQuot_cb01`). -/
noncomputable def cb01Zero (Pc : Params) (hm : 0 < Pc.m) (hmγ : 0 < Pc.mγ) (hΛ : 0 < Pc.Λ)
    (hM₁ : Pc.m ≤ Pc.M₁) (hM₂ : Pc.m ≤ Pc.M₂) (m : ℝ) (d : Fin 2) : ℂ :=
  ∑ j, pauliCurveZero (vpCurve Pc hm hmγ hΛ hM₁ hM₂ j) m (cbFA Pc d j) +
    mergeC m Pc.δ₂ Pc.δm *
      ∑ j, pauliCurveZero (cbCurve Pc hm hmγ hΛ hM₁ hM₂ d j) m (cbFB Pc j)

theorem cb01Zero_congr {Pc Pc' : Params} (e : Pc = Pc') (hm : 0 < Pc.m) (hmγ : 0 < Pc.mγ)
    (hΛ : 0 < Pc.Λ) (hM₁ : Pc.m ≤ Pc.M₁) (hM₂ : Pc.m ≤ Pc.M₂) (hm' : 0 < Pc'.m)
    (hmγ' : 0 < Pc'.mγ) (hΛ' : 0 < Pc'.Λ) (hM₁' : Pc'.m ≤ Pc'.M₁) (hM₂' : Pc'.m ≤ Pc'.M₂)
    (m : ℝ) (d : Fin 2) :
    cb01Zero Pc hm hmγ hΛ hM₁ hM₂ m d = cb01Zero Pc' hm' hmγ' hΛ' hM₁' hM₂' m d := by
  subst e
  rfl

theorem clsPauliLim_cb01_eq {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (k : Fin 5) (hk : k < 2) (hm : 0 < P₀.m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    clsPauliLim ctFam P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s =
      cb01Zero (cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0) hm hmγ hΛ (le_of_lt hA.1)
        (le_of_lt hA.2.1) P₀.m (if k = 0 then 1 else 0) / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5) := by
  obtain ⟨hm', hmγ', hΛ', hT⟩ := tendsto_evenQuot_cb01 hA k hk
  unfold clsPauliLim
  rw [Filter.Tendsto.limUnder_eq hT]
  rfl

/-! ### The 20 counterterm classes are canonical -/

/-- **The counterterm values `ctPauliAll P₀ r` are canonical.** -/
theorem ctPauliAll_canon (he : P₀.e ≠ 0) (r : CtIdx) : ClsCanon P₀ (ctPauliAll P₀ r) := by
  rcases r with k | ⟨k, t⟩ | k
  · by_cases hk : 2 ≤ k
    · refine ClsLow.canon he fun M₁ M₂ c₁ c₂ mγ Λ D D' s h => ?_
      simp only [ctPauliAll, ctPauliVal, hk, ite_true, cbW_congr h s]
    · intro M₁ M₂ c₁ c₂ c₁' c₂' mγ Λ D D' s s' hA hA'
      obtain ⟨rfl, rfl, hAg, rfl⟩ := setCAdm_unique he hA hA'
      have hk' : k < 2 := not_le.mp hk
      obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := id hA
      have hm : 0 < P₀.m := by linarith
      simp only [ctPauliAll, ctPauliVal, hk, ite_false, ctPauliX]
      rw [clsPauliLim_cb01_eq hA k hk' hm hmγ hΛ, clsPauliLim_cb01_eq hA' k hk' hm hmγ hΛ,
        cb01Zero_congr (cbParams_congr hAg s 0)]
  · refine ClsLow.canon he fun M₁ M₂ c₁ c₂ mγ Λ D D' s h => ?_
    by_cases hk : 2 ≤ k
    · simp only [ctPauliAll, ctPauliVal, hk, ite_true, cdParams_congr h s]
    · simp only [ctPauliAll, ctPauliVal, hk, ite_false, ctPauliX, cd01PauliVal,
        cdParams_congr h s]
  · refine ClsLow.canon he fun M₁ M₂ c₁ c₂ mγ Λ D D' s h => ?_
    simp only [ctPauliAll, ctPauliVal, sParams_congr h s]

/-! ### The canonical value `b` and `hsum` -/

/-- The class sum `(1/i)(∑ βᴹ + ∑ ctPauliAll)` at the set (c) data. -/
noncomputable def setCClassSum (P₀ : Params) (βM : MainIdx → ClsPauliVal) (M₁ M₂ c₁ c₂ mγ Λ : ℝ)
    (D : RegCt) (s : ℝ × ℝ × ℝ) : ℂ :=
  (1 / I) * (∑ r, βM r M₁ M₂ c₁ c₂ mγ Λ D s + ∑ r, ctPauliAll P₀ r M₁ M₂ c₁ c₂ mγ Λ D s)

/-- The admissible data `(c₁, c₂, D, s)` over `m_γ, Λ, M₁, M₂`. -/
def SetCAdmAt (P₀ : Params) (mγ Λ M₁ M₂ : ℝ) (x : ℝ × ℝ × RegCt × (ℝ × ℝ × ℝ)) : Prop :=
  SetCAdm P₀ M₁ M₂ x.1 x.2.1 mγ Λ x.2.2.1 x.2.2.2

open Classical in
/-- **The canonical fixed-regulator Pauli value of set (c)**: the real part of the class sum at a
chosen admissible datum over `m_γ, Λ, M₁, M₂`, and `0` if there is none (e.g. `M₁ = M₂`). By
`setCAdm_unique` the choice does not matter for canonical class values. -/
noncomputable def setCPauliB (P₀ : Params) (βM : MainIdx → ClsPauliVal) : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun mγ Λ M₁ M₂ =>
    if h : ∃ x, SetCAdmAt P₀ mγ Λ M₁ M₂ x then
      (setCClassSum P₀ βM M₁ M₂ h.choose.1 h.choose.2.1 mγ Λ h.choose.2.2.1
        h.choose.2.2.2).re
    else 0

/-- **The class sum is the same at all admissible data over `m_γ, Λ, M₁, M₂`.** -/
theorem setCClassSum_canon (he : P₀.e ≠ 0) {βM : MainIdx → ClsPauliVal}
    (hcan : ∀ r, ClsCanon P₀ (βM r)) {M₁ M₂ c₁ c₂ c₁' c₂' mγ Λ : ℝ} {D D' : RegCt}
    {s s' : ℝ × ℝ × ℝ} (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s)
    (hA' : SetCAdm P₀ M₁ M₂ c₁' c₂' mγ Λ D' s') :
    setCClassSum P₀ βM M₁ M₂ c₁ c₂ mγ Λ D s = setCClassSum P₀ βM M₁ M₂ c₁' c₂' mγ Λ D' s' := by
  unfold setCClassSum
  rw [Finset.sum_congr rfl fun r _ => hcan r _ _ _ _ _ _ _ _ _ _ _ _ hA hA',
    Finset.sum_congr rfl fun r _ => ctPauliAll_canon he r _ _ _ _ _ _ _ _ _ _ _ _ hA hA']

/-- `(1/i) w` is real when `Re w = 0`. -/
theorem one_div_I_mul_eq_ofReal_re {w : ℂ} (hw : w.re = 0) :
    (1 / I) * w = (((1 / I) * w).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [hw]

/-- **The input `hsum`**: for canonical main values `βᴹ` and a class sum `∑ βᴹ + ∑ ctPauliAll`
with vanishing real part at every admissible datum, `(1/i)(∑ βᴹ + ∑ ctPauliAll) = b` with
`b = setCPauliB P₀ βᴹ`. -/
theorem setCPauliB_hsum (he : P₀.e ≠ 0) {βM : MainIdx → ClsPauliVal}
    (hcan : ∀ r, ClsCanon P₀ (βM r))
    (hre : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (∑ r, βM r M₁ M₂ c₁ c₂ mγ Λ D s + ∑ r, ctPauliAll P₀ r M₁ M₂ c₁ c₂ mγ Λ D s).re = 0) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (1 / I) * (∑ r, βM r M₁ M₂ c₁ c₂ mγ Λ D s +
        ∑ r, ctPauliAll P₀ r M₁ M₂ c₁ c₂ mγ Λ D s) = ((setCPauliB P₀ βM mγ Λ M₁ M₂ : ℝ) : ℂ) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA
  have hex : ∃ x, SetCAdmAt P₀ mγ Λ M₁ M₂ x := ⟨(c₁, c₂, D, s), hA⟩
  have e := setCClassSum_canon he hcan hA hex.choose_spec
  simp only [setCPauliB, hex, ↓reduceDIte]
  rw [← e]
  exact one_div_I_mul_eq_ofReal_re (hre M₁ M₂ c₁ c₂ mγ Λ D s hA)

end QED.ChainProof.SetCPauli

end
