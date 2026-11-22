/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBKKPauli
public import QED.ChainProof.SetCRegDispCtVP
public import QED.WickModel.PhotonCounterterm

/-!
# Set (c), a main placement: the subtraction `Π_loop(0)` of the bubble by its two `δ₃` classes

Helper level for the input `hMainBD` of `QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces`.
The canonical Pauli value of the bubble class `repB i`
(`QED.ChainProof.SetCMainB.clsPauliLim_inl_eq`) is
`-(L(Z_G + Z_K) + Z_D + Z) / (64 e m⁵)`: `L = logW R 0 = (e²/6π²) ∑_f c_f log M_f²` times the
transverse and longitudinal values `Z_G`, `Z_K` of the unit, the transverse dispersive part `Z_D`
and the Pauli limit `Z` of the longitudinal dispersive part `kkLimB`. The two classes `repD i t`
carry the photon counterterm `δ = e² d₃(0)` in place of the bubble and have the value
`δ (Z_G + Z_K) / (64 e m⁵)` each (`QED.ChainProof.SetCMain.clsPauliLim_inr_int`, `_ext`). At
the set (c) data `δ = Π_loop(0) = L/2` (`setCAdm_d3_zero`, `vacuumPolarizationLoop_zero`), so the
three classes sum to `-(Z_D + Z)/(64 e m⁵)`: the subtracted bubble `Π − Π(0)`.

* `logW_zero_eq`: `L = (e²/6π²) ∑_f c_f log M_f²` (as a complex number);
* `logW_setCAdm`: `L = 2 e² d₃(0)` at the set (c) data;
* `wD_eq_mul`, `wKD_eq_mul`: the transverse and longitudinal weights are linear in `δ₃`;
* **`clsPauliLim_mainBD_eq`**: `repB i + repD i 0 + repD i 1 = -(Z_D + Z)/(64 e m⁵)`.
-/

@[expose] public section

open Complex Filter Topology Set
open scoped Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.ChainProof.SetCPauli QED.ChainProof.SetCLink QED.ChainProof.SetALink
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-- The log constant at `ε = 0`: `L = (e²/6π²) ∑_f c_f log M_f²`. -/
theorem logW_zero_eq (R : Params) :
    logW R 0 = ((R.e ^ 2 / (6 * π ^ 2) *
      ∑ f, R.loopCoeff f * Real.log (R.mass f ^ 2) : ℝ) : ℂ) := by
  have hl : ∀ f, Complex.log (((R.mass f ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) =
      ((Real.log (R.mass f ^ 2) : ℝ) : ℂ) := fun f => by
    rw [ofReal_zero, zero_mul, sub_zero, ← Complex.ofReal_log (sq_nonneg _)]
  simp only [logW, bubLogSum, vpCst, hl]
  push_cast
  rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  field_simp
  ring

/-- **The log constant is twice the photon counterterm** at the set (c) data. -/
theorem logW_setCAdm {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) :
    logW (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) 0 =
      2 * ((P₀.e ^ 2 * (shareCt D s).d₃ 0 : ℝ) : ℂ) := by
  have h3 : (shareCt D s).d₃ 0 = D.d₃ 0 := by
    simp [shareCt, Graded.Counterterms.withLevel]
  rw [h3, setCAdm_d3_zero hA, QED.WickModel.vacuumPolarizationLoop_zero, logW_zero_eq]
  push_cast
  ring

theorem wD_eq_mul (R : Params) (δ : ℝ) : wD R δ = (δ : ℂ) * wD R 1 := by
  simp only [wD]
  push_cast
  ring

theorem wKD_eq_mul (R : Params) (δ : ℝ) : wKD R δ = (δ : ℂ) * wKD R 1 := by
  simp only [wKD]
  push_cast
  ring

/-- **The bubble with its two `δ₃` classes is the subtracted bubble**: at the set (c) data, for
any Pauli limit `Z` of the longitudinal dispersive part,
`repB i + repD i 0 + repD i 1 = -(Z_D + Z)/(64 e m⁵)`,
`Z_D = -2c w_D ∑_f unitMDispPauliRepB(w_f, M_f)` the transverse dispersive part. -/
theorem clsPauliLim_mainBD_eq {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt}
    {s : ℝ × ℝ × ℝ} (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (i : Fin 12) {Z : ℂ}
    (hZ : PiecePauli P₀.m (kkLimB (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) i) Z) :
    clsPauliLim mainFam P₀ (.inl i) M₁ M₂ c₁ c₂ mγ Λ D s +
        clsPauliLim mainFam P₀ (.inr (i, 0)) M₁ M₂ c₁ c₂ mγ Λ D s +
        clsPauliLim mainFam P₀ (.inr (i, 1)) M₁ M₂ c₁ c₂ mγ Λ D s =
      -((-2 * vpCst (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) * wD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) 1) *
          ∑ f, unitMDispPauliRepB (repBClass i) (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (repBSlot i)
            (dispWt (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) f)
            ((regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).mass f) mγ Λ + Z) /
        (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5) := by
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  have hKl : ∀ p' p, IsPairQ P₀.m p' p → ∀ μ α β,
      Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        (kkB { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
          i p p' μ α β)) (𝓝[>] 0)
        (𝓝 (kkLimB (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) i p' p μ α β)) := fun p' p hpq μ α β => by
    obtain ⟨hp', hp, -, -, hq⟩ := hpq
    exact tendsto_kkB (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl hm hγ
      hγΛ (setCAdm_mass hA) hp hp' hq.le i μ α β
  have hlog := logW_setCAdm hA
  rcases kWard_cases i with ⟨j, hj⟩ | hW
  · rw [clsPauliLim_inl_eq hA hKl hZ
      (piecePauli_K_int (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ i j hj),
      clsPauliLim_inr_int hA i 0 j hj, clsPauliLim_inr_int hA i 1 j hj]
    simp only [repDLimInt, dGZ, kZInt, dkZ, dkZR]
    rw [hlog, wD_eq_mul _ (P₀.e ^ 2 * (shareCt D s).d₃ 0),
      wKD_eq_mul _ (P₀.e ^ 2 * (shareCt D s).d₃ 0)]
    ring
  · rw [clsPauliLim_inl_eq hA hKl hZ
      (piecePauli_K_ext (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ i hW),
      clsPauliLim_inr_ext hA i 0 hW, clsPauliLim_inr_ext hA i 1 hW]
    simp only [repDLimExt, dGZ, kZExt, dkZ, dkZR]
    rw [hlog, wD_eq_mul _ (P₀.e ^ 2 * (shareCt D s).d₃ 0),
      wKD_eq_mul _ (P₀.e ^ 2 * (shareCt D s).d₃ 0)]
    ring

end QED.ChainProof.SetCRegDisp

end
