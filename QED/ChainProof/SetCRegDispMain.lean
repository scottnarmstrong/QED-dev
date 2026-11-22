/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispLim

/-!
# Set (c): the regulator limit from the class values in dispersion form

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`: the input
`SetCRegLimitDisp P₀ (setCPauliB P₀ βᴹ)` of
`QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp_disp`, from separately named
hypotheses on the class values and five regulated Stage K pieces.

**Dispersion form.** A bubble flavour (electron, coefficient `1`; regulators `c₁`, `c₂`) carries
the spectral weight `ρ(v)` at mass² `(M_f²/m²) t_v` in units of `m²`. A class value `z` is in
dispersion form with per-mass kernel `u` (`IsDispPV m M₁ M₂ c₁ c₂ u z`) if the integrand
`ρ(v) [u(t_v) + c₁ u(M₁² t_v/m²) + c₂ u(M₂² t_v/m²)]` is integrable on `(0, 1)` and `z` is its
integral. The bubble class `Bᵢ` alone is not (it lacks the subtraction `Π_loop(0)`); the
placement sum `Bᵢ + Dᵢ,₀ + Dᵢ,₁` with its two `δ₃` classes is.

## Main statements

* `IsDispPV`, `IsDispPV.add`, `IsDispPV.sum`, `IsDispPV.const_mul`;
* `setCClassSum_eq`: under the dispersion form of the class values and the matching `hMatch`,
  the class sum `(1/i)(∑ βᴹ + ∑ ctPauliAll)` at an admissible datum is
  `e⁶/(64π⁶) ∫₀¹ ρ(v) [a(t_v) + c₁ a(s₁ t_v) + c₂ a(s₂ t_v)] dv` (`jDisp`), `a` the sum of the
  five regulated pieces;
* **`setCRegLimitDisp_of_pieces`**: `SetCRegLimitDisp P₀ (setCPauliB P₀ βᴹ)` from
  - `hMainBD`: `βᴹ(Bᵢ) + βᴹ(Dᵢ,₀) + βᴹ(Dᵢ,₁)` in dispersion form, kernels `uBD i mγ Λ`;
  - `hCtCB`: `CBₖ + CDₖ,₀ + CDₖ,₁` (values `ctPauliAll`) in dispersion form, kernels `uCB k mγ Λ`;
  - `hCtS`: the VP-share classes `Sₖ` in dispersion form, kernels `uS k mγ Λ`;
  - `hMatch`: `(1/i)(∑ uBD + ∑ uCB + ∑ uS)(T) = e⁶/(64π⁶) (aL + aSI + aCI + aX + aSC)(T)`
    for `T ≥ 4`, `0 < mγ < Λ`;
  - `hL`, `hSI`, `hCI`, `hX`, `hSC`: the regulated pieces `aL`, `aSI`, `aCI`, `aX`, `aSC` tend to
    `lPair`, `selfIn`, `cornIn`, `crossUnit 0 T + crossUnit T 0`, `scOutS + scOutC`
    (`IsRegPiece`).
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCK QED.ChainProof.SetCPauli

/-! ### Dispersion form -/

/-- The flavour-summed dispersion integrand of a per-mass kernel `u` (mass² in units of `m²`). -/
noncomputable def dispPVF (m M₁ M₂ c₁ c₂ : ℝ) (u : ℝ → ℂ) (v : ℝ) : ℂ :=
  (setCKSpecRho v : ℂ) * (u (setCKSpecMass v) + c₁ * u (M₁ ^ 2 / m ^ 2 * setCKSpecMass v) +
    c₂ * u (M₂ ^ 2 / m ^ 2 * setCKSpecMass v))

/-- **`z` is the flavour-summed dispersion integral of the kernel `u`**:
`z = ∫₀¹ ρ(v) [u(t_v) + c₁ u(M₁² t_v/m²) + c₂ u(M₂² t_v/m²)] dv`, the integrand integrable. -/
def IsDispPV (m M₁ M₂ c₁ c₂ : ℝ) (u : ℝ → ℂ) (z : ℂ) : Prop :=
  IntegrableOn (dispPVF m M₁ M₂ c₁ c₂ u) (Ioo 0 1) ∧
    z = ∫ v in Ioo (0 : ℝ) 1, dispPVF m M₁ M₂ c₁ c₂ u v

section Disp

variable {m M₁ M₂ c₁ c₂ : ℝ}

theorem IsDispPV.add {u w : ℝ → ℂ} {z z' : ℂ} (h : IsDispPV m M₁ M₂ c₁ c₂ u z)
    (h' : IsDispPV m M₁ M₂ c₁ c₂ w z') :
    IsDispPV m M₁ M₂ c₁ c₂ (fun T => u T + w T) (z + z') := by
  have e : dispPVF m M₁ M₂ c₁ c₂ (fun T => u T + w T) =
      fun v => dispPVF m M₁ M₂ c₁ c₂ u v + dispPVF m M₁ M₂ c₁ c₂ w v := by
    funext v
    simp only [dispPVF]
    ring
  rw [IsDispPV, e]
  exact ⟨h.1.add h'.1, by rw [integral_add h.1 h'.1, ← h.2, ← h'.2]⟩

theorem IsDispPV.zero : IsDispPV m M₁ M₂ c₁ c₂ (fun _ => 0) 0 := by
  have e : dispPVF m M₁ M₂ c₁ c₂ (fun _ => 0) = fun _ => 0 := by
    funext v
    simp [dispPVF]
  rw [IsDispPV, e]
  exact ⟨integrableOn_zero, by simp⟩

theorem IsDispPV.sum {ι : Type*} (s : Finset ι) {u : ι → ℝ → ℂ} {z : ι → ℂ}
    (h : ∀ i ∈ s, IsDispPV m M₁ M₂ c₁ c₂ (u i) (z i)) :
    IsDispPV m M₁ M₂ c₁ c₂ (fun T => ∑ i ∈ s, u i T) (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsDispPV.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsDispPV.const_mul {u : ℝ → ℂ} {z : ℂ} (h : IsDispPV m M₁ M₂ c₁ c₂ u z) (c : ℂ) :
    IsDispPV m M₁ M₂ c₁ c₂ (fun T => c * u T) (c * z) := by
  have e : dispPVF m M₁ M₂ c₁ c₂ (fun T => c * u T) =
      fun v => c * dispPVF m M₁ M₂ c₁ c₂ u v := by
    funext v
    simp only [dispPVF]
    ring
  rw [IsDispPV, e]
  exact ⟨h.1.const_mul c, by rw [integral_const_mul, ← h.2]⟩

end Disp

/-! ### The class sum in dispersion form -/

theorem sum_mainIdx (f : MainIdx → ℂ) :
    ∑ r, f r = ∑ i : Fin 12, (f (.inl i) + f (.inr (i, 0)) + f (.inr (i, 1))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib, add_assoc]

theorem sum_ctIdx (f : CtIdx → ℂ) :
    ∑ r, f r = ∑ k : Fin 5, (f (.inl k) + f (.inr (.inl (k, 0))) + f (.inr (.inl (k, 1)))) +
      ∑ k : Fin 5, f (.inr (.inr k)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib, add_assoc]

section ClassSum

variable {P₀ : Params} {βM : MainIdx → ClsPauliVal}
  {uBD : Fin 12 → ℝ → ℝ → ℝ → ℂ} {uCB uS : Fin 5 → ℝ → ℝ → ℝ → ℂ}
  {aL aSI aCI aX aSC : ℝ → ℝ → ℝ → ℝ}

/-- The total regulated kernel: the sum of the five regulated pieces. -/
noncomputable abbrev aTot (aL aSI aCI aX aSC : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun mγ Λ T => aL mγ Λ T + aSI mγ Λ T + aCI mγ Λ T + aX mγ Λ T + aSC mγ Λ T

/-- **The class sum in dispersion form**: at an admissible datum,
`(1/i)(∑ βᴹ + ∑ ctPauliAll) = e⁶/(64π⁶) ∫₀¹ ρ(v) [a(t_v) + c₁ a(s₁ t_v) + c₂ a(s₂ t_v)] dv`. -/
theorem setCClassSum_eq
    (hMainBD : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ i : Fin 12,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBD i mγ Λ) (βM (.inl i) M₁ M₂ c₁ c₂ mγ Λ D s +
        βM (.inr (i, 0)) M₁ M₂ c₁ c₂ mγ Λ D s + βM (.inr (i, 1)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtCB : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uCB k mγ Λ) (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtS : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uS k mγ Λ) (ctPauliAll P₀ (.inr (.inr k)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hMatch : ∀ mγ Λ T : ℝ, 0 < mγ → mγ < Λ → 4 ≤ T →
      (1 / I) * (∑ i, uBD i mγ Λ T + ∑ k, uCB k mγ Λ T + ∑ k, uS k mγ Λ T) =
        ((P₀.e ^ 6 / (64 * π ^ 6) * aTot aL aSI aCI aX aSC mγ Λ T : ℝ) : ℂ))
    {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) :
    setCClassSum P₀ βM M₁ M₂ c₁ c₂ mγ Λ D s =
      ((P₀.e ^ 6 / (64 * π ^ 6) * jDisp (aTot aL aSI aCI aX aSC) (M₁ ^ 2 / P₀.m ^ 2)
        (M₂ ^ 2 / P₀.m ^ 2) c₁ c₂ mγ Λ : ℝ) : ℂ) := by
  obtain ⟨hM₁, hM₂, -, -, hmγ, -, hmΛ, hm2, -, -⟩ := id hA
  have hm : 0 < P₀.m := by linarith
  have hB := IsDispPV.sum Finset.univ fun i _ => hMainBD M₁ M₂ c₁ c₂ mγ Λ D s hA i
  have hC := IsDispPV.sum Finset.univ fun k _ => hCtCB M₁ M₂ c₁ c₂ mγ Λ D s hA k
  have hS := IsDispPV.sum Finset.univ fun k _ => hCtS M₁ M₂ c₁ c₂ mγ Λ D s hA k
  have hT := ((hB.add hC).add hS).const_mul (1 / I)
  unfold setCClassSum
  rw [sum_mainIdx, sum_ctIdx, ← add_assoc, hT.2]
  set K : ℝ := P₀.e ^ 6 / (64 * π ^ 6)
  have hs : ∀ M : ℝ, P₀.m < M → ∀ v ∈ Ioo (0 : ℝ) 1, 4 ≤ M ^ 2 / P₀.m ^ 2 * setCKSpecMass v :=
    fun M hM v hv => four_le_mul_setCKSpecMass (one_le_sq_div hm hM) hv
  have h4 : ∀ v ∈ Ioo (0 : ℝ) 1, 4 ≤ setCKSpecMass v := fun v hv => by
    simpa using four_le_mul_setCKSpecMass le_rfl hv
  rw [jDisp, ← integral_const_mul, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  simp only [dispPVF]
  rw [hMatch mγ Λ _ hmγ hmΛ (h4 v hv), hMatch mγ Λ _ hmγ hmΛ (hs M₁ hM₁ v hv),
    hMatch mγ Λ _ hmγ hmΛ (hs M₂ hM₂ v hv)]
  push_cast
  ring

/-- **The canonical value in dispersion form**: over admissible data with coefficients `c₁, c₂`,
`setCPauliB P₀ βᴹ = e⁶/(64π⁶) jDisp`. -/
theorem setCPauliB_eq
    (hMainBD : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ i : Fin 12,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBD i mγ Λ) (βM (.inl i) M₁ M₂ c₁ c₂ mγ Λ D s +
        βM (.inr (i, 0)) M₁ M₂ c₁ c₂ mγ Λ D s + βM (.inr (i, 1)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtCB : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uCB k mγ Λ) (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtS : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uS k mγ Λ) (ctPauliAll P₀ (.inr (.inr k)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hMatch : ∀ mγ Λ T : ℝ, 0 < mγ → mγ < Λ → 4 ≤ T →
      (1 / I) * (∑ i, uBD i mγ Λ T + ∑ k, uCB k mγ Λ T + ∑ k, uS k mγ Λ T) =
        ((P₀.e ^ 6 / (64 * π ^ 6) * aTot aL aSI aCI aX aSC mγ Λ T : ℝ) : ℂ))
    (he : P₀.e ≠ 0) {M₁ M₂ c₁ c₂ mγ Λ : ℝ} (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂)
    (hc : 1 + c₁ + c₂ = 0) (hc' : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (hmγ : 0 < mγ)
    (hmΛ : mγ < Λ) (hm2 : mγ < 2 * P₀.m) :
    setCPauliB P₀ βM mγ Λ M₁ M₂ = P₀.e ^ 6 / (64 * π ^ 6) *
      jDisp (aTot aL aSI aCI aX aSC) (M₁ ^ 2 / P₀.m ^ 2) (M₂ ^ 2 / P₀.m ^ 2) c₁ c₂ mγ Λ := by
  have hm : 0 < P₀.m := by linarith
  obtain ⟨D, s, hA⟩ := exists_setCAdm he hM₁ hM₂ hc hc' hmγ hmΛ hm2
  have hex : ∃ x, SetCAdmAt P₀ mγ Λ M₁ M₂ x := ⟨(c₁, c₂, D, s), hA⟩
  have hx : SetCAdm P₀ M₁ M₂ hex.choose.1 hex.choose.2.1 mγ Λ hex.choose.2.2.1
      hex.choose.2.2.2 := hex.choose_spec
  obtain ⟨e₁, e₂⟩ := QED.ChainProof.SetANestedAt.pvCoeffs_unique hm hM₁ hx.2.2.1 hx.2.2.2.1 hc hc'
  simp only [setCPauliB, hex, ↓reduceDIte]
  rw [setCClassSum_eq hMainBD hCtCB hCtS hMatch hx, Complex.ofReal_re, e₁, e₂]

end ClassSum

/-! ### The regulator limit -/

/-- **The regulator limit of set (c) from the dispersion form of the class values and the
regulated Stage K pieces.** Named inputs: `hMainBD` (main classes), `hCtCB`, `hCtS` (counterterm
classes), `hMatch` (the per-mass class kernels against the pieces), and `hL`, `hSI`, `hCI`,
`hX`, `hSC` (the regulated pieces and their limits `lPair`, `selfIn`, `cornIn`, the crossed
pair and `scOutS + scOutC`). -/
theorem setCRegLimitDisp_of_pieces {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    {βM : MainIdx → ClsPauliVal} {uBD : Fin 12 → ℝ → ℝ → ℝ → ℂ}
    {uCB uS : Fin 5 → ℝ → ℝ → ℝ → ℂ} {aL aSI aCI aX aSC : ℝ → ℝ → ℝ → ℝ}
    (hMainBD : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ i : Fin 12,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBD i mγ Λ) (βM (.inl i) M₁ M₂ c₁ c₂ mγ Λ D s +
        βM (.inr (i, 0)) M₁ M₂ c₁ c₂ mγ Λ D s + βM (.inr (i, 1)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtCB : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uCB k mγ Λ) (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtS : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uS k mγ Λ) (ctPauliAll P₀ (.inr (.inr k)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hMatch : ∀ mγ Λ T : ℝ, 0 < mγ → mγ < Λ → 4 ≤ T →
      (1 / I) * (∑ i, uBD i mγ Λ T + ∑ k, uCB k mγ Λ T + ∑ k, uS k mγ Λ T) =
        ((P₀.e ^ 6 / (64 * π ^ 6) *
          (aL mγ Λ T + aSI mγ Λ T + aCI mγ Λ T + aX mγ Λ T + aSC mγ Λ T) : ℝ) : ℂ))
    (hL : IsRegPiece aL SetCK.lPair) (hSI : IsRegPiece aSI SetCK.selfIn)
    (hCI : IsRegPiece aCI SetCK.cornIn)
    (hX : IsRegPiece aX fun T => SetCK.crossUnit 0 T + SetCK.crossUnit T 0)
    (hSC : IsRegPiece aSC fun T => SetCK.scOutS T + SetCK.scOutC T) :
    SetCRegLimitDisp P₀ (setCPauliB P₀ βM) := by
  have hTot : IsRegPiece (aTot aL aSI aCI aX aSC) setCKKernelPairSum := by
    have h := ((((hL.add hSI).add hCI).add hX).add hSC)
    have e : (fun T => SetCK.lPair T + SetCK.selfIn T + SetCK.cornIn T +
        (SetCK.crossUnit 0 T + SetCK.crossUnit T 0) + (SetCK.scOutS T + SetCK.scOutC T)) =
        setCKKernelPairSum := by
      funext T
      simp only [setCKKernelPairSum]
      ring
    rw [e] at h
    exact h
  refine setCRegLimitDisp_of_fixLim hm fun M₁ M₂ c₁ c₂ hM₁ hM₂ hc hc' η hη => ?_
  set K : ℝ := P₀.e ^ 6 / (64 * π ^ 6) with hK
  have hK0 : 0 ≤ K := by positivity
  have hlim := tendsto_jDisp hTot (one_le_sq_div hm hM₁) (one_le_sq_div hm hM₂) c₁ c₂
  have hlimK := hlim.const_mul K
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := exists_of_eventually_regRange (Metric.tendsto_nhds.1 hlimK η hη)
  refine ⟨min δ (min 1 (2 * P₀.m)), lt_min hδ (lt_min one_pos (by linarith)), max Λ₀ 1,
    fun mγ Λ h0 h1 h2 => ?_⟩
  have hδ' : mγ < δ := h1.trans_le (min_le_left _ _)
  have h1' : mγ < 1 := h1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h2m : mγ < 2 * P₀.m := h1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hΛ : Λ₀ < Λ := (le_max_left _ _).trans_lt h2
  have hmΛ : mγ < Λ := h1'.trans ((le_max_right _ _).trans_lt h2)
  have hd := hΛ₀ mγ Λ h0 hδ' hΛ
  rw [Real.dist_eq] at hd
  rw [setCPauliB_eq (aL := aL) (aSI := aSI) (aCI := aCI) (aX := aX) (aSC := aSC) hMainBD hCtCB
    hCtS hMatch he hM₁ hM₂ hc hc' h0 hmΛ h2m]
  have e : P₀.e ^ 6 * kDispPV P₀.m M₁ M₂ c₁ c₂ / (64 * π ^ 6) =
      K * (kDisp 1 + c₁ * kDisp (M₁ ^ 2 / P₀.m ^ 2) + c₂ * kDisp (M₂ ^ 2 / P₀.m ^ 2)) := by
    rw [hK, kDispPV]
    ring
  rw [e]
  exact hd

end QED.ChainProof.SetCRegDisp

end
