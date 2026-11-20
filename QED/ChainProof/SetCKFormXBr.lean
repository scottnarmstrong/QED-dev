/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXFub
public import QED.ChainProof.SetCKCoordInt

/-!
# Set (c), Stage K, closed forms: `I(X)` in threshold coordinates, branch by branch

Helper level (no frozen statement). Step 4 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
sessions 19+, 22+, 24+), first part. The integrand `S(Y, y₃, s)` of `I(X)` (`formXS`) switches at
`s = x* = (1 - Y)/(1 - y₃)`; in the coordinates `(u, s)`, `u = Y - s y₃`, of the shared layer
(`SetCKCoordMaps`) the switch is `s = 1 - u`, the boundary between the two regions:
`formXS = formXS1` on branch 1 (`s ≤ 1 - u`, **`formXS_psi1`**) and `formXS = formXS2` on
branch 2 (`s > 1 - u`, **`formXS_psi2`**). With `coord_integral_square`, `coord_integral_thr`
and `ae_integrable_formXIin`:

On branch 2 the order is swapped (`formX_setIntegral_R2`): the triangle `0 < u < X`,
`1 - u < s < 1` is `1 - X < s < 1`, `1 - s < u < X`, and at fixed `s` the branch-2 integrand
has simpler partial fractions in `u`. Hence

**`formXI_ae_eq_br`**: for almost every `X ∈ (0, 1)`,
`I(X) = ∫₀^X du ∫_{(s_lo(u), 1-u]} J₁ S₁(Ψ₁(u, s), s) ds +
  ∫_{1-X}^1 ds ∫_{(1-s, X)} J₂ S₂(Ψ₂(u, s), s) du`, both outer integrands integrable.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The branch-1 integrand `J₁ S₁(Ψ₁(u, s), s)`. -/
noncomputable def formXKin1 (X u s : ℝ) : ℝ :=
  coordJ1 X u s * formXS1 (coordPsi1 X (u, s)).1 (coordPsi1 X (u, s)).2 s

/-- The branch-2 integrand `J₂ S₂(Ψ₂(u, s), s)`. -/
noncomputable def formXKin2 (X u s : ℝ) : ℝ :=
  coordJ2 X u s * formXS2 (coordPsi2 X (u, s)).1 (coordPsi2 X (u, s)).2 s

/-- The swapped branch-2 region `s ∈ (1 - X, 1)`, `u ∈ (1 - s, X)` (pairs `(s, u)`). -/
def formXR2s (X : ℝ) : Set (ℝ × ℝ) := {q | q.1 ∈ Ioo (1 - X) 1 ∧ q.2 ∈ Ioo (1 - q.1) X}

section

variable {X : ℝ}

/-- On branch 1 the threshold lies below the switch: `formXS = formXS1`. -/
theorem formXS_psi1 (hX : X ∈ Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ coordR1 X) :
    formXS (coordPsi1 X p).1 (coordPsi1 X p).2 p.2 =
      formXS1 (coordPsi1 X p).1 (coordPsi1 X p).2 p.2 := by
  obtain ⟨⟨⟨-, hYX⟩, -, hzY⟩, -, -, hu⟩ := coordPsi1_spec hX hp
  have hsu := hp.2.2
  unfold formXS cornInXs
  rw [ite_eq_left]
  rw [le_div_iff₀ (by linarith [hX.2])]
  nlinarith

/-- On branch 2 the threshold lies above the switch: `formXS = formXS2`. -/
theorem formXS_psi2 (hX : X ∈ Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ coordR2 X) :
    formXS (coordPsi2 X p).1 (coordPsi2 X p).2 p.2 =
      formXS2 (coordPsi2 X p).1 (coordPsi2 X p).2 p.2 := by
  obtain ⟨⟨⟨-, hYX⟩, -, hzY⟩, -, -, hu⟩ := coordPsi2_spec hX hp
  have hsu := hp.2.1
  unfold formXS cornInXs
  rw [ite_eq_right]
  rw [not_le, div_lt_iff₀ (by linarith [hX.2])]
  nlinarith

theorem formX_mem_swap (z : ℝ × ℝ) :
    z.swap ∈ coordR2 X ↔ z ∈ formXR2s X := by
  obtain ⟨s, u⟩ := z
  simp only [Prod.swap_prod_mk, coordR2, formXR2s, mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, h4⟩, by linarith, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, h4⟩, by linarith, h2⟩

/-- **Fubini on the branch-2 triangle with `u` inside.** -/
theorem formX_setIntegral_R2 {F : ℝ × ℝ → ℝ}
    (hF : IntegrableOn F (coordR2 X)) :
    IntegrableOn (fun s => ∫ u in Ioo (1 - s) X, F (u, s)) (Ioo (1 - X) 1) ∧
      ∫ p in coordR2 X, F p = ∫ s in Ioo (1 - X) 1, ∫ u in Ioo (1 - s) X, F (u, s) := by
  have hR2 : MeasurableSet (formXR2s X) :=
    (measurableSet_Ioo.preimage measurable_fst).inter
      ((measurableSet_lt (by fun_prop) measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  have hsw : (fun z : ℝ × ℝ => (coordR2 X).indicator F z.swap) =
      (formXR2s X).indicator (F ∘ Prod.swap) := by
    funext z
    by_cases h : z ∈ formXR2s X
    · rw [indicator_of_mem ((formX_mem_swap z).2 h), indicator_of_mem h]
      rfl
    · rw [indicator_of_notMem (fun h' => h ((formX_mem_swap z).1 h')),
        indicator_of_notMem h]
  have hI : Integrable ((coordR2 X).indicator F) ((volume : Measure ℝ).prod volume) :=
    (integrable_indicator_iff (measurableSet_coordR2 X)).2 hF
  have hI' : IntegrableOn (F ∘ Prod.swap) (formXR2s X) := by
    rw [← integrable_indicator_iff hR2, Measure.volume_eq_prod, ← hsw]
    exact hI.swap
  obtain ⟨hi, he⟩ := coord_setIntegral_prod (A := Ioo (1 - X) 1) (B := fun s => Ioo (1 - s) X)
    measurableSet_Ioo (fun _ => measurableSet_Ioo) hR2 hI'
  refine ⟨hi, ?_⟩
  rw [← integral_indicator (measurableSet_coordR2 X), Measure.volume_eq_prod,
    ← integral_prod_swap, hsw, integral_indicator hR2, ← Measure.volume_eq_prod]
  exact he

/-- **`I(X)` as iterated integrals**, `s` inside on branch 1 and `u` inside on branch 2, for
almost every `X`. -/
theorem formXI_ae_eq_br :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      IntegrableOn (fun u => ∫ s in Ioc (coordSLo X u) (1 - u), formXKin1 X u s) (Ioo 0 X) ∧
      IntegrableOn (fun s => ∫ u in Ioo (1 - s) X, formXKin2 X u s) (Ioo (1 - X) 1) ∧
      formXI X = (∫ u in Ioo 0 X, ∫ s in Ioc (coordSLo X u) (1 - u), formXKin1 X u s) +
        ∫ s in Ioo (1 - X) 1, ∫ u in Ioo (1 - s) X, formXKin2 X u s := by
  filter_upwards [ae_integrable_formXIin, ae_restrict_mem measurableSet_Ioo] with X hI hX
  obtain ⟨hsq, heq⟩ := coord_integral_square hX (fun q => formXSw q.1 q.2 X)
  have hg := hsq.1 hI
  have e1 : EqOn (fun p : ℝ × ℝ => coordJ1 X p.1 p.2 * formXSw (coordPsi1 X p).1
      (coordPsi1 X p).2 X) (fun p => formXKin1 X p.1 p.2) (coordR1 X) := by
    intro p hp
    simp only [formXKin1, formXSw, coord_thr1 hX hp, formXS_psi1 hX hp]
  have e2 : EqOn (fun p : ℝ × ℝ => coordJ2 X p.1 p.2 * formXSw (coordPsi2 X p).1
      (coordPsi2 X p).2 X) (fun p => formXKin2 X p.1 p.2) (coordR2 X) := by
    intro p hp
    simp only [formXKin2, formXSw, coord_thr2 hX hp, formXS_psi2 hX hp]
  obtain ⟨h1, h2⟩ := (coord_integrableOn_iff hX _).1 hg
  have h1' := h1.congr_fun e1 (measurableSet_coordR1 X)
  have h2' := h2.congr_fun e2 (measurableSet_coordR2 X)
  obtain ⟨i1, f1⟩ := coord_setIntegral_prod (A := Ioo 0 X)
    (B := fun u => Ioc (coordSLo X u) (1 - u)) measurableSet_Ioo (fun _ => measurableSet_Ioc)
    (measurableSet_coordR1 X) h1'
  obtain ⟨i2, f2⟩ := formX_setIntegral_R2 h2'
  refine ⟨i1, i2, ?_⟩
  have h0 : formXI X = ∫ q in coordT X, formXSw q.1 q.2 X := heq
  rw [h0, coord_setIntegral_eq hX hg, setIntegral_congr_fun (measurableSet_coordR1 X) e1,
    setIntegral_congr_fun (measurableSet_coordR2 X) e2, ← f2]
  erw [f1]

end

end QED.ChainProof.SetCK

end
