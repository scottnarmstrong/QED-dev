/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntKind
public import QED.GradedProof.X0NsCheck

/-!
# The class obligations of (HA₀) for the `gaugeCt` classes

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58): `classIntA_repGW`, `classIntA_repGU`, the class obligations `ClassIntA repGW 0`
and `ClassIntA repGU 0` for the two-loop representatives with a level-`0` `δ₁` vertex on the
closed fermion loop.

## Proof

The `gaugeCt` vertex `t₀` lies on the only closed fermion loop, through `x₀`. Changing it into a
`gauge` vertex (`QED.ChainProof.SetALink.toG`) gives a two-loop contraction of five `gauge`
vertices with a closed fermion loop; at a preserved flavouring with loop flavour `f`, the factor
`e² d₁ f 0` of the `gaugeCt` vertex goes into the loop coefficient: `c'_f = c_f e² d₁ f 0`. The
level-`0` counterterm data are constant on the Pauli–Villars blocks (hypothesis `hD`), so `c'`
satisfies both block conditions, and (X₀)'s two-loop goal
(`QED.GradedProof.X0.twoLoopClosedGoal_of_std`, `QED.GradedProof.X0.twoLoopStdGoal`) gives
(T₉′) for the changed contraction at the coefficients `c'`; it passes back to the class
(`jointEnergyFirstIntegrable_of_toG`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetALink

open QED.WickModel QED.ChainProof.Enum
open QED.TwoLoop.Enumeration (gauges)

variable {F : Type} [Fintype F] [DecidableEq F]

/-- The twisted loop coefficients satisfy the first block condition. -/
theorem twist_pv₁ (Φ : Lepton.Flavors F) (w : F → ℝ) (rep : F → F)
    (hw : ∀ f, w f = w (rep f))
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0) :
    ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * w f = 0 := by
  intro b hb
  rw [Finset.sum_congr rfl fun f hf => by
    rw [hw f, (Finset.mem_filter.mp hf).2], ← Finset.sum_mul, hPV₁ b hb, zero_mul]

/-- The twisted loop coefficients satisfy the second block condition. -/
theorem twist_pv₂ (Φ : Lepton.Flavors F) (w : F → ℝ) (rep : F → F)
    (hw : ∀ f, w f = w (rep f))
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) :
    ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * w f * Φ.mass f ^ 2 = 0 := by
  intro b hb
  rw [Finset.sum_congr rfl fun f hf => by
    rw [hw f, (Finset.mem_filter.mp hf).2, mul_right_comm], ← Finset.sum_mul, hPV₂ b hb,
    zero_mul]

/-- **The class obligation for a two-loop contraction with one `gaugeCt` vertex on its only
closed fermion loop.** -/
theorem classIntA_of_toG {κ : Fin 5 → Wick.VertexKind} (hκ : ∀ t, κ t = .gauge ∨ κ t = .gaugeCt)
    (C : Contraction 1 1 κ) (t₀ : Fin 5) (ht₀ : ∀ t, κ t = .gaugeCt ↔ t = t₀)
    (x₀ : Wick.FermionVertex κ) (hx : C.1.1.SameCycle (.inr (fvOfG hκ t₀)) (.inr x₀))
    (h₀ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr x₀))
    (hall : ∀ x, (∃ i, C.1.1.SameCycle x (.inl i)) ∨ C.1.1.SameCycle x (.inr x₀))
    (h₀' : ∀ i, ¬ (toG hκ C).1.1.SameCycle (.inl i) (.inr (fvG hκ x₀)))
    (hall' : ∀ x, (∃ i, (toG hκ C).1.1.SameCycle x (.inl i)) ∨
      (toG hκ C).1.1.SameCycle x (.inr (fvG hκ x₀)))
    (hC : IsOnePI C) (hC' : IsOnePI (toG hκ C))
    (hcyc : ¬ ∀ x, Equiv.Perm.SameCycle (toG hκ C).1.1 x (.inl 0))
    (hL : loopCount (toG hκ C) = loopCount C) : ClassIntA C 0 := by
  intro P F _ _ Φ D rep hH pOut pIn kIn hmom αOut βIn μ
  set w : F → ℝ := fun f => P.e ^ 2 * D.d₁ f 0 with hw_def
  have hw : ∀ f, w f = w (rep f) := fun f => by simp only [hw_def, (hH.hD f).1]
  set Φ' := twistΦ Φ fun f => Φ.coeff f * w f
  have hG := QED.GradedProof.X0.twoLoopClosedGoal_of_std P Φ' D
    (QED.GradedProof.X0.twoLoopStdGoal P Φ' D rep hH.hε hH.hrep
      (twist_pv₁ Φ w rep hw hH.hPV₁) (twist_pv₂ Φ w rep hw hH.hPV₂))
    (toG hκ C) hC'.1 hC'.2.1 hcyc pOut pIn kIn hmom αOut βIn μ
  unfold QED.GradedProof.X0.integrand at hG
  refine jointEnergyFirstIntegrable_of_toG hκ Φ C P D _ hC.1 hC.2.1 hC'.2.1 hL ?_
    (by simpa using hmom) αOut βIn μ hG
  intro φ hφ
  have hφ' := (preserves_toG_iff hκ Φ' C φ).mpr hφ
  rw [loopWeight_eq_of_one_loop Φ hφ x₀ h₀ hall,
    loopWeight_eq_of_one_loop Φ' hφ' (fvG hκ x₀) h₀' hall', ctW,
    Fintype.prod_eq_single t₀ fun t ht => by
      simp only [show ¬ κ t = .gaugeCt from fun h => ht ((ht₀ t).mp h), ↓reduceIte]]
  have hf : φ (fvOfG hκ t₀) = φ x₀ :=
    QED.GradedProof.VP2.fermionFlavor_eq_of_sameCycle Φ hφ hx
  simp only [(ht₀ t₀).mpr rfl, ↓reduceIte, hf, flavG_apply, Equiv.symm_apply_apply]
  simp only [Φ', twistΦ, w]
  push_cast
  ring

/-! ### `GW`: `δ₁` at the vertex `w = 4` -/

theorem kGW_kinds : ∀ t, kGW t = .gauge ∨ kGW t = .gaugeCt := by decide

theorem kGW_ct : ∀ t, kGW t = .gaugeCt ↔ t = 4 := by decide

theorem gw_cycle : repGW.1.1.SameCycle (.inr (fvOfG kGW_kinds 4)) (.inr (fv kGW 3)) := by
  decide +kernel

theorem gw_open : ∀ i, ¬ repGW.1.1.SameCycle (.inl i) (.inr (fv kGW 3)) := by decide +kernel

theorem gw_all : ∀ x, (∃ i, repGW.1.1.SameCycle x (.inl i)) ∨
    repGW.1.1.SameCycle x (.inr (fv kGW 3)) := by
  decide +kernel

theorem gw_open' : ∀ i, ¬ (toG kGW_kinds repGW).1.1.SameCycle (.inl i)
    (.inr (fvG kGW_kinds (fv kGW 3))) := by
  decide +kernel

theorem gw_all' : ∀ x, (∃ i, (toG kGW_kinds repGW).1.1.SameCycle x (.inl i)) ∨
    (toG kGW_kinds repGW).1.1.SameCycle x (.inr (fvG kGW_kinds (fv kGW 3))) := by
  decide +kernel

open QED.TwoLoop.Enumeration in
theorem isOnePI_toG_repGW : IsOnePI (toG kGW_kinds repGW) := by decide +kernel

theorem gw_cyc : ¬ ∀ x, Equiv.Perm.SameCycle (toG kGW_kinds repGW).1.1 x (.inl 0) := by
  decide +kernel

theorem loopCount_toG_repGW : loopCount (toG kGW_kinds repGW) = loopCount repGW := by
  rw [loopCount_repGW, QED.TwoLoop.Enumeration.loopCount_eq_card]
  decide +kernel

/-- **The class obligation for `GW`.** -/
theorem classIntA_repGW : ClassIntA repGW 0 :=
  classIntA_of_toG kGW_kinds repGW 4 kGW_ct (fv kGW 3) gw_cycle gw_open gw_all gw_open' gw_all'
    isOnePI_repGW isOnePI_toG_repGW gw_cyc loopCount_toG_repGW

/-! ### `GU`: `δ₁` at the vertex `u = 3` -/

theorem kGU_kinds : ∀ t, kGU t = .gauge ∨ kGU t = .gaugeCt := by decide

theorem kGU_ct : ∀ t, kGU t = .gaugeCt ↔ t = 3 := by decide

theorem gu_cycle : repGU.1.1.SameCycle (.inr (fvOfG kGU_kinds 3)) (.inr (fv kGU 3)) := by
  decide +kernel

theorem gu_open : ∀ i, ¬ repGU.1.1.SameCycle (.inl i) (.inr (fv kGU 3)) := by decide +kernel

theorem gu_all : ∀ x, (∃ i, repGU.1.1.SameCycle x (.inl i)) ∨
    repGU.1.1.SameCycle x (.inr (fv kGU 3)) := by
  decide +kernel

theorem gu_open' : ∀ i, ¬ (toG kGU_kinds repGU).1.1.SameCycle (.inl i)
    (.inr (fvG kGU_kinds (fv kGU 3))) := by
  decide +kernel

theorem gu_all' : ∀ x, (∃ i, (toG kGU_kinds repGU).1.1.SameCycle x (.inl i)) ∨
    (toG kGU_kinds repGU).1.1.SameCycle x (.inr (fvG kGU_kinds (fv kGU 3))) := by
  decide +kernel

open QED.TwoLoop.Enumeration in
theorem isOnePI_toG_repGU : IsOnePI (toG kGU_kinds repGU) := by decide +kernel

theorem gu_cyc : ¬ ∀ x, Equiv.Perm.SameCycle (toG kGU_kinds repGU).1.1 x (.inl 0) := by
  decide +kernel

theorem loopCount_toG_repGU : loopCount (toG kGU_kinds repGU) = loopCount repGU := by
  rw [loopCount_repGU, QED.TwoLoop.Enumeration.loopCount_eq_card]
  decide +kernel

/-- **The class obligation for `GU`.** -/
theorem classIntA_repGU : ClassIntA repGU 0 :=
  classIntA_of_toG kGU_kinds repGU 3 kGU_ct (fv kGU 3) gu_cycle gu_open gu_all gu_open' gu_all'
    isOnePI_repGU isOnePI_toG_repGU gu_cyc loopCount_toG_repGU

end QED.ChainProof.SetALink

end
