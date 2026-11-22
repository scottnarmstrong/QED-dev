/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBRestS
public import QED.ChainProof.SetCMainBDecay

/-!
# Set (c), the bubble classes: the nested-to-joint link and the rest link

Helper level for the per-class link `QED.ChainProof.SetCPauli.SetCClassLim` of the twelve
bubble classes `repB i`.

* `intHypA_setC`: the hypotheses `QED.ChainProof.SetALink.IntHypA` at the set (c) data;
* **`mainBOuterLink`**: the open link `QED.ChainProof.SetCMainB.MainBOuterLink` for all twelve
  orbits, from `QED.ChainProof.SetCMainB.jointEnergyFirstIntegral_nestB'` with the decay
  `outerDecay'_outerBW` and (T₉′) in the nested routing `jointEnergyFirstIntegrable_nestB_repB`;
* `MainBKKLink` (open): the longitudinal dispersive part `kkB` of the rest has an `ε → 0⁺`
  limit;
* **`mainBRestLink_of_kk`**: `MainBRestLink` from `MainBKKLink` (the `ε S_ε` part tends to zero,
  `QED.ChainProof.SetCMainB.tendsto_sB`; the integrability of `kkB` at fixed `ε` from that of the
  rest and of the `ε S_ε` part);
* **`setCClassLim_inl_of_kk`**: `SetCClassLim mainFam P₀ (.inl i)` from `MainBKKLink` alone.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open QED.WickModel (Params)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCLink QED.ChainProof.SetALink QED.ChainProof.SetCMain
open QED.ChainProof.SetCPauli
open QED.ChainProof.SetCUnitM (jointEnergyFirstIntegrable_sub_mul)
open QED.ChainProof.SetAPauli (regParams regFlavors)

variable {P₀ : Params}

/-- **The hypotheses `IntHypA` at the set (c) data**, with the counterterms `shareCt D s`. -/
theorem intHypA_setC {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) {ε : ℝ} (hε : 0 < ε) :
    IntHypA { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (shareCt D s) Graded.leptonRep := by
  obtain ⟨-, -, hPV₁, hPV₂, -, -, -, -, hD, -⟩ := hA
  refine ⟨hε, QED.GradedProof.RPi4.leptonRep_idem,
    QED.GradedProof.RPi4.leptonFlavors_blockPV₁ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hPV₁
      fun ℓ => ℓ.elim0,
    QED.GradedProof.RPi4.leptonFlavors_blockPV₂ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hPV₂
      fun ℓ => ℓ.elim0, fun f => ?_⟩
  simpa [Graded.Counterterms.withLevel] using QED.GradedProof.RPi4.hD_of_renormalized _ _ _ hD f

/-- **The nested-to-joint link of `repB i`** (all twelve orbits). -/
theorem mainBOuterLink (P₀ : Params) (i : Fin 12) : MainBOuterLink P₀ i := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p _ ε hε μ α β
  obtain ⟨hm, -, -⟩ := setCAdm_masses hA
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, -⟩ := id hA
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 :=
    by simp
  have hH := intHypA_setC hA hε
  exact jointEnergyFirstIntegral_nestB' (P := { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }) hm
    hM₁ hM₂ hPV₁ hPV₂ hε (continuous_outerBW _ _ hε hmom i _ _ _) (continuous_kBW hmom i)
    (outerDecay'_outerBW _ _ hε hmom i _ _ _)
    (jointEnergyFirstIntegrable_nestB_repB _ _ _ _ hH (flavorsLoop_lepton _) i hmom _ _ _)

/-- **The longitudinal dispersive link of `repB i`** (open): at the set (c) data the value of
the longitudinal dispersive part `(-2c J_ε(k²)) · ctKD 1` of the rest has an `ε → 0⁺` limit. -/
def MainBKKLink (P₀ : Params) (i : Fin 12) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ p' p, IsPairQ P₀.m p' p → ∃ Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ, ∀ μ α β,
      Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        (kkB { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
          i p p' μ α β)) (𝓝[>] 0) (𝓝 (Y μ α β))

/-- **The rest link from the longitudinal dispersive link**: the `ε S_ε` part tends to zero
(`tendsto_sB`), and at every `ε > 0` the longitudinal dispersive part is integrable in both
stages, as the rest (`jointEnergyFirstIntegral_outerBub_split`, with `mainBOuterLink`) minus the
`ε S_ε` part (`jointEnergyFirstIntegral_sB`). -/
theorem mainBRestLink_of_kk {i : Fin 12} (hK : MainBKKLink P₀ i) : MainBRestLink P₀ i := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  obtain ⟨Y, hY⟩ := hK M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  have hpq' := hpq
  obtain ⟨hp', hp, -, -, hq⟩ := hpq'
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with hRdef
  have hMf : ∀ f, R.m ≤ R.mass f := setCAdm_mass hA
  have hMp : ∀ f, 0 < R.mass f := fun f => hm.trans_le (hMf f)
  refine ⟨Y, fun μ α β => ?_⟩
  have hS := tendsto_sB (R := R) hm hγ hγΛ hp hp' hq.le (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl hMf
    i μ α β
  refine (((hY μ α β).sub (hS.const_mul 1)).congr' ?_).trans (by simp)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  obtain ⟨-, hO⟩ := mainBOuterLink P₀ i M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq ε hε μ α β
  have hR := (jointEnergyFirstIntegral_outerBub_split { R with ε := ε } R
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl rfl rfl rfl i p p' μ α β hε hMp hO).1
  have hSi := (jointEnergyFirstIntegral_sB { R with ε := ε } R (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (hm := rfl) (he := rfl) (hγ := rfl) (hΛ := rfl) i p p' μ α β hε hMp).1
  have ekk : kkB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β = fun ℓ =>
      restB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β ℓ -
        (-1) * sB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β ℓ :=
    funext fun ℓ => by rw [restB_eq]; ring
  have hKi := (jointEnergyFirstIntegrable_sub_mul hR hSi (-1)).1
  rw [← ekk] at hKi
  have erest : restB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β =
      fun ℓ => kkB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β ℓ -
        1 * sB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β ℓ :=
    funext fun ℓ => by rw [restB_eq]; ring
  rw [erest, (jointEnergyFirstIntegrable_sub_mul hKi hSi 1).2]

/-- **The limit link of `repB i` from the longitudinal dispersive link.** -/
theorem setCClassLim_inl_of_kk {i : Fin 12} (hK : MainBKKLink P₀ i) :
    SetCClassLim mainFam P₀ (.inl i) :=
  setCClassLim_inl_of (mainBOuterLink P₀ i) (mainBRestLink_of_kk hK)

end QED.ChainProof.SetCMainB

end
