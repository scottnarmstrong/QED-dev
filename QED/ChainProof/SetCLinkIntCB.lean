/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkInt
public import QED.ChainProof.SetALinkIntG
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# The class obligations of (HS₀) for the classes `CB2`–`CB4`

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58): `classIntA_repCB2`, `classIntA_repCB3`, `classIntA_repCB4`, the class
obligations for the two-loop representatives with a level-`0` `gaugeCt` vertex on the open line
of the one-loop vertex and the bubble on its photon line.

## Proof

The `gaugeCt` vertex `t₀` lies on the open line. Changing it into a `gauge` vertex
(`QED.ChainProof.SetALink.toG`) gives the two-loop contraction of five `gauge` vertices with the
bubble on the photon line of the one-loop vertex. At a preserved flavouring the flavour of `t₀`
is the open-line flavour, so the factor of the `gaugeCt` vertex is the constant
`w = e² d₁(openLine, 0)`, which goes into the loop coefficients: `c'_f = c_f w`. A constant
multiple satisfies both block conditions, and (X₀)'s two-loop goal
(`QED.GradedProof.X0.twoLoopClosedGoal_of_std`, `QED.GradedProof.X0.twoLoopStdGoal`) gives
(T₉′) for the changed contraction at the coefficients `c'`; it passes back to the class
(`QED.ChainProof.SetALink.jointEnergyFirstIntegrable_of_toG`): `classIntA_of_toG_open`.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.ChainProof.Enum QED.ChainProof.SetALink
open QED.TwoLoop.Enumeration (gauges)

/-- **The class obligation for a two-loop contraction with one `gaugeCt` vertex on its open
line and one closed fermion loop.** -/
theorem classIntA_of_toG_open {κ : Fin 5 → Wick.VertexKind}
    (hκ : ∀ t, κ t = .gauge ∨ κ t = .gaugeCt) (C : Contraction 1 1 κ) (t₀ : Fin 5)
    (ht₀ : ∀ t, κ t = .gaugeCt ↔ t = t₀)
    (hx : C.1.1.SameCycle (.inr (fvOfG hκ t₀)) (.inl 0)) (x₀ : Wick.FermionVertex κ)
    (h₀ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr x₀))
    (hall : ∀ x, (∃ i, C.1.1.SameCycle x (.inl i)) ∨ C.1.1.SameCycle x (.inr x₀))
    (h₀' : ∀ i, ¬ (toG hκ C).1.1.SameCycle (.inl i) (.inr (fvG hκ x₀)))
    (hall' : ∀ x, (∃ i, (toG hκ C).1.1.SameCycle x (.inl i)) ∨
      (toG hκ C).1.1.SameCycle x (.inr (fvG hκ x₀)))
    (hC : IsOnePI C) (hC' : IsOnePI (toG hκ C))
    (hcyc : ¬ ∀ x, Equiv.Perm.SameCycle (toG hκ C).1.1 x (.inl 0))
    (hL : loopCount (toG hκ C) = loopCount C) : ClassIntA C 0 := by
  intro P F _ _ Φ D rep hH pOut pIn kIn hmom αOut βIn μ
  set w : F → ℝ := fun _ => P.e ^ 2 * D.d₁ Φ.openLine 0 with hw_def
  have hw : ∀ f, w f = w (rep f) := fun _ => rfl
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
  have hf : φ (fvOfG hκ t₀) = Φ.openLine :=
    QED.GradedProof.VP2.fermionFlavor_eq_of_sameCycle Φ hφ hx
  simp only [(ht₀ t₀).mpr rfl, ↓reduceIte, hf, flavG_apply, Equiv.symm_apply_apply]
  simp only [Φ', twistΦ, w]
  push_cast
  ring

/-! ### `CB2`: `δ₁` at the end `0` -/

theorem kCB2_kinds : ∀ t, kCB2 t = .gauge ∨ kCB2 t = .gaugeCt := by decide

theorem kCB2_ct : ∀ t, kCB2 t = .gaugeCt ↔ t = 0 := by decide

theorem cb2_cycle : repCB2.1.1.SameCycle (.inr (fvOfG kCB2_kinds 0)) (.inl 0) := by
  decide +kernel

theorem cb2_open : ∀ i, ¬ repCB2.1.1.SameCycle (.inl i) (.inr (fv kCB2 3)) := by decide +kernel

theorem cb2_all : ∀ x, (∃ i, repCB2.1.1.SameCycle x (.inl i)) ∨
    repCB2.1.1.SameCycle x (.inr (fv kCB2 3)) := by
  decide +kernel

theorem cb2_open' : ∀ i, ¬ (toG kCB2_kinds repCB2).1.1.SameCycle (.inl i)
    (.inr (fvG kCB2_kinds (fv kCB2 3))) := by
  decide +kernel

theorem cb2_all' : ∀ x, (∃ i, (toG kCB2_kinds repCB2).1.1.SameCycle x (.inl i)) ∨
    (toG kCB2_kinds repCB2).1.1.SameCycle x (.inr (fvG kCB2_kinds (fv kCB2 3))) := by
  decide +kernel

open QED.TwoLoop.Enumeration in
theorem isOnePI_toG_repCB2 : IsOnePI (toG kCB2_kinds repCB2) := by decide +kernel

theorem cb2_cyc : ¬ ∀ x, Equiv.Perm.SameCycle (toG kCB2_kinds repCB2).1.1 x (.inl 0) := by
  decide +kernel

theorem loopCount_toG_repCB2 : loopCount (toG kCB2_kinds repCB2) = loopCount repCB2 := by
  rw [QED.TwoLoop.Enumeration.loopCount_eq_card, QED.TwoLoop.Enumeration.loopCount_eq_card]
  decide +kernel

/-- **The class obligation for `CB2`.** -/
theorem classIntA_repCB2 : ClassIntA repCB2 0 :=
  classIntA_of_toG_open kCB2_kinds repCB2 0 kCB2_ct cb2_cycle (fv kCB2 3) cb2_open cb2_all
    cb2_open' cb2_all' isOnePI_repCB2 isOnePI_toG_repCB2 cb2_cyc loopCount_toG_repCB2

/-! ### `CB3`: `δ₁` in the middle -/

theorem kCB3_kinds : ∀ t, kCB3 t = .gauge ∨ kCB3 t = .gaugeCt := by decide

theorem kCB3_ct : ∀ t, kCB3 t = .gaugeCt ↔ t = 1 := by decide

theorem cb3_cycle : repCB3.1.1.SameCycle (.inr (fvOfG kCB3_kinds 1)) (.inl 0) := by
  decide +kernel

theorem cb3_open : ∀ i, ¬ repCB3.1.1.SameCycle (.inl i) (.inr (fv kCB3 3)) := by decide +kernel

theorem cb3_all : ∀ x, (∃ i, repCB3.1.1.SameCycle x (.inl i)) ∨
    repCB3.1.1.SameCycle x (.inr (fv kCB3 3)) := by
  decide +kernel

theorem cb3_open' : ∀ i, ¬ (toG kCB3_kinds repCB3).1.1.SameCycle (.inl i)
    (.inr (fvG kCB3_kinds (fv kCB3 3))) := by
  decide +kernel

theorem cb3_all' : ∀ x, (∃ i, (toG kCB3_kinds repCB3).1.1.SameCycle x (.inl i)) ∨
    (toG kCB3_kinds repCB3).1.1.SameCycle x (.inr (fvG kCB3_kinds (fv kCB3 3))) := by
  decide +kernel

open QED.TwoLoop.Enumeration in
theorem isOnePI_toG_repCB3 : IsOnePI (toG kCB3_kinds repCB3) := by decide +kernel

theorem cb3_cyc : ¬ ∀ x, Equiv.Perm.SameCycle (toG kCB3_kinds repCB3).1.1 x (.inl 0) := by
  decide +kernel

theorem loopCount_toG_repCB3 : loopCount (toG kCB3_kinds repCB3) = loopCount repCB3 := by
  rw [QED.TwoLoop.Enumeration.loopCount_eq_card, QED.TwoLoop.Enumeration.loopCount_eq_card]
  decide +kernel

/-- **The class obligation for `CB3`.** -/
theorem classIntA_repCB3 : ClassIntA repCB3 0 :=
  classIntA_of_toG_open kCB3_kinds repCB3 1 kCB3_ct cb3_cycle (fv kCB3 3) cb3_open cb3_all
    cb3_open' cb3_all' isOnePI_repCB3 isOnePI_toG_repCB3 cb3_cyc loopCount_toG_repCB3

/-! ### `CB4`: `δ₁` at the end `2` -/

theorem kCB4_kinds : ∀ t, kCB4 t = .gauge ∨ kCB4 t = .gaugeCt := by decide

theorem kCB4_ct : ∀ t, kCB4 t = .gaugeCt ↔ t = 2 := by decide

theorem cb4_cycle : repCB4.1.1.SameCycle (.inr (fvOfG kCB4_kinds 2)) (.inl 0) := by
  decide +kernel

theorem cb4_open : ∀ i, ¬ repCB4.1.1.SameCycle (.inl i) (.inr (fv kCB4 3)) := by decide +kernel

theorem cb4_all : ∀ x, (∃ i, repCB4.1.1.SameCycle x (.inl i)) ∨
    repCB4.1.1.SameCycle x (.inr (fv kCB4 3)) := by
  decide +kernel

theorem cb4_open' : ∀ i, ¬ (toG kCB4_kinds repCB4).1.1.SameCycle (.inl i)
    (.inr (fvG kCB4_kinds (fv kCB4 3))) := by
  decide +kernel

theorem cb4_all' : ∀ x, (∃ i, (toG kCB4_kinds repCB4).1.1.SameCycle x (.inl i)) ∨
    (toG kCB4_kinds repCB4).1.1.SameCycle x (.inr (fvG kCB4_kinds (fv kCB4 3))) := by
  decide +kernel

open QED.TwoLoop.Enumeration in
theorem isOnePI_toG_repCB4 : IsOnePI (toG kCB4_kinds repCB4) := by decide +kernel

theorem cb4_cyc : ¬ ∀ x, Equiv.Perm.SameCycle (toG kCB4_kinds repCB4).1.1 x (.inl 0) := by
  decide +kernel

theorem loopCount_toG_repCB4 : loopCount (toG kCB4_kinds repCB4) = loopCount repCB4 := by
  rw [QED.TwoLoop.Enumeration.loopCount_eq_card, QED.TwoLoop.Enumeration.loopCount_eq_card]
  decide +kernel

/-- **The class obligation for `CB4`.** -/
theorem classIntA_repCB4 : ClassIntA repCB4 0 :=
  classIntA_of_toG_open kCB4_kinds repCB4 2 kCB4_ct cb4_cycle (fv kCB4 3) cb4_open cb4_all
    cb4_open' cb4_all' isOnePI_repCB4 isOnePI_toG_repCB4 cb4_cyc loopCount_toG_repCB4

end QED.ChainProof.SetCLink

end
