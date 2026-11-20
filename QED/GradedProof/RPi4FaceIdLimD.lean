/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdClassEq

/-!
# (R-Π₄) step L6d3: the limit of the one-loop classes at `faceIdD₀`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. At the
counterterms `faceIdD₀` the gauge parts of `F0`, `F1` cancel the two bubbles `G` up to `iε`
(`fBubble_ctD₂_F0/F1`), leaving the mass-derivative block `dBlock`, whose integral converges to
`fLim(e, 3e²)`:

* `faceId_bubbles_eq`: `F0 + F1 + 2G = dBlock + iε R` at `faceIdD₀`;
* `faceId_tendsto_eps_vpf`: `iε ∫ F → 0` for a `VPF` family;
* **`faceId_tendsto_bubbles`**.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

omit [DecidableEq F] in
/-- **The gauge parts cancel the bubbles**: at `faceIdD₀`, `F0 + F1 + 2G = dBlock + iε R`. -/
theorem faceId_bubbles_eq (P : Params) {ε : ℝ} (hε : ε ≠ 0) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    fBubble P Φ (faceIdD₀ F) rep true true false ε k q μ ν +
        fBubble P Φ (faceIdD₀ F) rep false false true ε k q μ ν +
        2 * gBubble { P with ε := ε } Φ (faceIdD₀ F) rep k q μ ν =
      dBlock P Φ (faceIdD₀ F) rep ε k q μ ν + ε * I *
        (remBlock Φ rep (dR P (faceIdD₀ F)) true true false ε k q μ ν +
          remBlock Φ rep (dR P (faceIdD₀ F)) false false true ε k q μ ν +
          (-1) * remMBlock P Φ (faceIdD₀ F) rep ε k q μ ν) := by
  have hd : ∀ f, (faceIdD₀ F).d₁ f 0 = (faceIdD₀ F).d₂ f 0 := fun _ => rfl
  rw [fBubble_split P Φ (faceIdD₀ F) rep true, fBubble_split P Φ (faceIdD₀ F) rep false,
    fBubble_ctD₂_F0 P Φ (faceIdD₀ F) rep hd hε, fBubble_ctD₂_F1 P Φ (faceIdD₀ F) rep hd hε,
    dBlock_eq P Φ (faceIdD₀ F) rep hε]
  ring

/-- `iε ∫ F → 0` for a `VPF` family. -/
theorem faceId_tendsto_eps_vpf {T : ℝ}
    {G : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hG : VPF T G) {k : Fin 4 → ℝ}
    (hk : -T ^ 2 < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * I * QED.OneLoop.energyFirstIntegral fun q => G ε k q μ ν)
      (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_limT_of_hasVPLim (hG.1 (fun _ => 1) 1 tendsto_const_nhds) hk μ ν
  simp only [one_mul] at h
  have h2 := tendsto_epsI.mul h
  rwa [zero_mul] at h2

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
include hm₀ hmass hrep hPV₁ hPV₂

/-- **The one-loop classes at `faceIdD₀` converge to `fLim(e, 3e²)`** (`e ≠ 0`). -/
theorem faceId_tendsto_bubbles {e : ℝ} (he : e ≠ 0) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun x =>
        fBubble (faceIdParams e) Φ (faceIdD₀ F) rep true true false ε k x μ ν +
        fBubble (faceIdParams e) Φ (faceIdD₀ F) rep false false true ε k x μ ν +
        2 * gBubble { faceIdParams e with ε := ε } Φ (faceIdD₀ F) rep k x μ ν)
      (𝓝[>] 0) (𝓝 (fLim Φ rep e (fun _ => 3 * e ^ 2) k μ ν)) := by
  set P := faceIdParams e
  have hD : ∀ f, (faceIdD₀ F).d₂ f 0 = (faceIdD₀ F).d₂ (rep f) 0 ∧
      (faceIdD₀ F).dm f 0 = (faceIdD₀ F).dm (rep f) 0 := fun _ => ⟨rfl, rfl⟩
  have h1 := tendsto_dBlock P Φ (faceIdD₀ F) rep hm₀ hmass hrep hPV₁ hPV₂ hD hk μ ν
  rw [wCl_F_eq_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he (faceIdD₀ F) hD hk μ ν] at h1
  have hR := ((vpf_remBlock Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (dR P (faceIdD₀ F)) true true
    false).add (vpf_remBlock Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (dR P (faceIdD₀ F)) false false
    true)).add ((vpf_remMBlock hm₀ P Φ (faceIdD₀ F) rep hmass).const_mul (-1))
  have hk' : -(m₀ + m₀) ^ 2 < Minkowski.dot k k := by nlinarith
  have h2 := h1.add (faceId_tendsto_eps_vpf hR hk' μ ν)
  rw [add_zero, show (fun _ : F => P.e ^ 2 * ((faceIdD₀ F).dm _ 0 - (faceIdD₀ F).d₂ _ 0)) =
    fun _ => 3 * e ^ 2 by funext; simp only [P, faceIdParams, faceIdD₀]; ring] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have i1 := (vpf_dBlock Φ rep hm₀ hmass hrep hPV₁ hPV₂ P (faceIdD₀ F)).2 ε hε k μ ν
  have i2 := hR.2 ε hε k μ ν
  rw [← QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul, ← efi_add i1 (i2.const_mul _)]
  exact congrArg _ (funext fun q => (faceId_bubbles_eq Φ rep P hε.ne' k q μ ν).symm)

end QED.GradedProof.RPi4

end
