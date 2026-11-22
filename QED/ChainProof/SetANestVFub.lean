/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestSum

/-!
# Set (a), obligation (N): the three-loop Fubini step for the classes `VA`, `VB`, `VC`

Helper level for the set (a) headline (HA₆), obligation (N) of
`QED.ChainProof.SetAPauli.SetALimitLink`, step NL.3 for the loop classes with a two-loop inner
insertion. The joint energy-first integral (T₉) of three loop momenta integrates the three
energies first and then the nine spatial components. The nested form of
`QED.ChainProof.SetANest.LoopNested` applies the one-loop energy-first integral (D) in the outer
momentum `k = ℓ 2` to the joint two-loop integral (T₉) in the inner momenta `(ℓ 0, ℓ 1)`:

`∫ d³w ∫ dt₃ (∫ d³v₁ d³v₂ ∫ dt₁ dt₂ F)`.

* `jointEnergyFirstIntegral_three_eq_outer`: the two agree when both stages of the joint
  prescription are integrable (`jointEnergyFirstIntegrable 3`, the form of (HA₀)) and, for
  almost every spatial outer momentum `w`, the inner energy integral `∫ dt₁ dt₂ F` is integrable
  jointly in the outer energy `t₃` and the six inner spatial components (`hK`).
* `efInt_outer_of_joint`: with `hK` at every `w`, the outer integrand
  `k ↦ ∫∫ F(·, k)` is integrable in both stages (`EFInt`).
* **`loopNested_of_joint`**: the nested form `LoopNested` of a class from its value as a joint
  three-loop integral (`hval`, the routing and Wick steps), the joint integrability (`hF`), the
  condition `hK` at every `w` and the identification of the inner joint integral with the outer
  integrand of the photon tensor (`hX`).

The energies `t₁, t₂` are always integrated first and never exchanged with a spatial component.
The condition `hK` is the analytic core of step NL.3: a bound on `∫ d⁶v |∫ dt₁ dt₂ F|`, polynomial
in the outer energy against the decay of the outer factor. Neither the spectral form T★ᵤ (which
controls only the signed integral `∫ d⁶v ∫ dt₁ dt₂`) nor (HA₀) (joint integrability only) gives it.
-/

@[expose] public section

open MeasureTheory

namespace QED.ChainProof.SetANestV

/-! ### Splitting off the last loop momentum -/

section Split

variable {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]

/-- An integral over `Fin 3 → α` is an integral over `α × (Fin 2 → α)`, the first factor being
the entry `2`. -/
theorem integral_fin3_last (g : (Fin 3 → α) → ℂ) :
    ∫ x, g x = ∫ p : α × (Fin 2 → α), g (Fin.insertNth 2 p.1 p.2) := by
  rw [← (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => α) 2).symm.integral_comp' (g := g)]
  rfl

/-- Integrability over `Fin 3 → α` is integrability over `α × (Fin 2 → α)`. -/
theorem integrable_fin3_last_iff (g : (Fin 3 → α) → ℂ) :
    Integrable g ↔ Integrable fun p : α × (Fin 2 → α) => g (Fin.insertNth 2 p.1 p.2) := by
  rw [← (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => α) 2).symm.integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  rfl

end Split

/-- The family of three loop momenta with energies `insertNth 2 t₃ t` and spatial momenta
`insertNth 2 w v`. -/
theorem cons_insertNth (t₃ : ℝ) (t : Fin 2 → ℝ) (w : Fin 3 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    (fun s => (Fin.cons (Fin.insertNth (α := fun _ => ℝ) 2 t₃ t s)
      (Fin.insertNth (α := fun _ => Fin 3 → ℝ) 2 w v s) : Fin 4 → ℝ)) =
      Fin.insertNth 2 (Fin.cons t₃ w : Fin 4 → ℝ) fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) := by
  funext s
  refine Fin.succAboveCases 2 ?_ (fun j => ?_) s
  · simp only [Fin.insertNth_apply_same]
  · simp only [Fin.insertNth_apply_succAbove]

theorem insertNth_two_eq {β : Type*} (k : β) (q : Fin 2 → β) :
    (Fin.insertNth 2 k q : Fin 3 → β) = ![q 0, q 1, k] := by
  funext s
  fin_cases s <;> rfl

/-- The inner energy integral at the outer energy `t₃`, the outer spatial momentum `w` and the
inner spatial momenta `v`. -/
noncomputable def innerT (F : (Fin 3 → Fin 4 → ℝ) → ℂ) (t₃ : ℝ) (w : Fin 3 → ℝ)
    (v : Fin 2 → Fin 3 → ℝ) : ℂ :=
  ∫ t : Fin 2 → ℝ, F (Fin.insertNth 2 (Fin.cons t₃ w : Fin 4 → ℝ)
    fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))

/-- The inner joint integral at the outer momentum `k`. -/
noncomputable def innerJ (F : (Fin 3 → Fin 4 → ℝ) → ℂ) (k : Fin 4 → ℝ) : ℂ :=
  QED.TwoLoop.jointEnergyFirstIntegral 2 fun q => F (Fin.insertNth 2 k q)

theorem innerJ_cons (F : (Fin 3 → Fin 4 → ℝ) → ℂ) (t₃ : ℝ) (w : Fin 3 → ℝ) :
    innerJ F (Fin.cons t₃ w) = ∫ v : Fin 2 → Fin 3 → ℝ, innerT F t₃ w v := rfl

/-- The two stages of (T₉) at three loops, with the last loop momentum split off. -/
theorem joint3_split (F : (Fin 3 → Fin 4 → ℝ) → ℂ)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 F) :
    (∀ w v, ∫ t : Fin 3 → ℝ, F (fun s => (Fin.cons (t s)
      (Fin.insertNth (α := fun _ => Fin 3 → ℝ) 2 w v s) : Fin 4 → ℝ)) =
      ∫ t₃ : ℝ, innerT F t₃ w v) ∧
    Integrable fun p : (Fin 3 → ℝ) × (Fin 2 → Fin 3 → ℝ) => ∫ t₃ : ℝ, innerT F t₃ p.1 p.2 := by
  obtain ⟨hF₁, hF₂⟩ := hF
  have hin : ∀ w v, ∫ t : Fin 3 → ℝ,
      F (fun s => (Fin.cons (t s) (Fin.insertNth (α := fun _ => Fin 3 → ℝ) 2 w v s) :
        Fin 4 → ℝ)) = ∫ t₃ : ℝ, innerT F t₃ w v := by
    intro w v
    have hint := (integrable_fin3_last_iff _).mp (hF₁ (Fin.insertNth 2 w v))
    rw [integral_fin3_last]
    simp only [cons_insertNth] at hint ⊢
    exact integral_prod _ hint
  refine ⟨hin, ?_⟩
  have hout := (integrable_fin3_last_iff _).mp hF₂
  simp only [hin] at hout
  exact hout

/-- **Nested equals joint at three loops, inner two-loop insertion.** If both stages of the joint
energy-first integral (T₉) of `F` are integrable and, for almost every outer spatial momentum `w`,
the inner energy integral is integrable jointly in the outer energy and the inner spatial momenta
(`hK`), then the joint integral is the energy-first integral (D) in `k = ℓ 2` of the joint
two-loop integral in `(ℓ 0, ℓ 1)`. -/
theorem jointEnergyFirstIntegral_three_eq_outer (F : (Fin 3 → Fin 4 → ℝ) → ℂ)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 F)
    (hK : ∀ᵐ w : Fin 3 → ℝ, Integrable fun p : ℝ × (Fin 2 → Fin 3 → ℝ) => innerT F p.1 w p.2) :
    QED.TwoLoop.jointEnergyFirstIntegral 3 F = QED.OneLoop.energyFirstIntegral (innerJ F) := by
  obtain ⟨hin, hout⟩ := joint3_split F hF
  unfold QED.TwoLoop.jointEnergyFirstIntegral QED.OneLoop.energyFirstIntegral
  rw [integral_fin3_last]
  simp only [hin]
  refine (integral_prod _ hout).trans (integral_congr_ae (hK.mono fun w hw => ?_))
  simp only [innerJ_cons]
  exact integral_integral_swap (f := fun (v : Fin 2 → Fin 3 → ℝ) (t₃ : ℝ) => innerT F t₃ w v)
    hw.swap

/-- **The outer integrand is integrable in both stages**, given both stages of the joint
prescription and the condition `hK` at every outer spatial momentum. -/
theorem efInt_outer_of_joint (F : (Fin 3 → Fin 4 → ℝ) → ℂ)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 F)
    (hK : ∀ w : Fin 3 → ℝ, Integrable fun p : ℝ × (Fin 2 → Fin 3 → ℝ) => innerT F p.1 w p.2) :
    QED.TwoLoop.VPUnitNested.EFInt (innerJ F) := by
  obtain ⟨-, hout⟩ := joint3_split F hF
  refine ⟨fun w => ?_, ?_⟩
  · simp only [innerJ_cons]
    exact (hK w).integral_prod_left
  · refine hout.integral_prod_left.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [innerJ_cons]
    exact integral_integral_swap (f := fun (v : Fin 2 → Fin 3 → ℝ) (t₃ : ℝ) =>
      innerT F t₃ w v) (hK w).swap

/-! ### The nested form of a class -/

open QED.ChainProof.SetANest QED.WickModel in
/-- **The nested form of a loop class from its joint three-loop form.** If every entry of the
value (G₅) of `C` is the joint three-loop integral of `F μ i j` (`hval`: the routing change and
the Wick factorization), that integrand is integrable in both stages (`hF`: (HA₀) in the nested
routing), satisfies the Fubini condition `hK` at every outer spatial momentum, and its inner joint
integral at the outer momentum `k` is the outer integrand of the photon tensor `X` (`hX`), then
`C` is in nested form with tensor `X`. -/
theorem loopNested_of_joint (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) (X : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (p' p : Fin 4 → ℝ)
    (G : Fin 4 → Fin 4 → Fin 4 → (Fin 3 → Fin 4 → ℝ) → ℂ)
    (hval : ∀ μ i j, Graded.contractionValue P Φ D C 0 (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 3 (G μ i j))
    (hF : ∀ μ i j, QED.TwoLoop.jointEnergyFirstIntegrable 3 (G μ i j))
    (hK : ∀ μ i j (w : Fin 3 → ℝ), Integrable fun q : ℝ × (Fin 2 → Fin 3 → ℝ) =>
      innerT (G μ i j) q.1 w q.2)
    (hX : ∀ μ i j k, innerJ (G μ i j) k =
      nestInt P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p X μ i j k) :
    LoopNested P Φ D C X p' p := by
  intro μ i j
  have he : innerJ (G μ i j) = nestInt P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p X μ i j :=
    funext (hX μ i j)
  refine ⟨he ▸ efInt_outer_of_joint _ (hF μ i j) (hK μ i j), ?_⟩
  rw [hval, jointEnergyFirstIntegral_three_eq_outer _ (hF μ i j)
    (Filter.Eventually.of_forall (hK μ i j)), he]

end QED.ChainProof.SetANestV

end
