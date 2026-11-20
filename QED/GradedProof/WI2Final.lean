/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Core
public import QED.GradedProof.SE2RealFinal
public import QED.GradedProof.LevelZeroWard

/-!
# The level-`1` Ward identity `d₁ = d₂`

Helper proof of the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57), as
`QED.GradedProof.WI2.d₁_eq_d₂_one'`.

Let `D₀ = D.withLevel 1 0 0`. By the order-`4` on-shell conditions (`GEx2.isOnShellAt_two_iff`),
`e⁴ d₂ f 1 = σ₁`, the shell slope of the order-`4` self-energy of `D₀`; by the order-`4` charge
normalization (`GEx2.isChargeNormalizedAt_two_iff`), `c + e⁵ d₁ f 1 = 0`, where `c γ^μ` is the
order-`5` vertex of `D₀` at `q = 0` between on-shell spinors. The level-`0` Ward identity
(`d₁_eq_d₂_zero'`, from the order-`2` conditions) and the two-loop Ward identity per T1 parameter
set give `c = -e σ₁` (`charge_eq_neg_e_mul_slope`), so `e⁵ d₁ f 1 = e⁵ d₂ f 1`.
-/

@[expose] public section

namespace QED.GradedProof.WI2

open QED.Graded
open QED.WickModel (Params)

/-- **(WI₂)**: the level-`1` counterterms of a flavour on shell and charge normalized at orders
`e²` and `e⁴` obey `d₁ f 1 = d₂ f 1`. -/
theorem d₁_eq_d₂_one' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (he : P.e ≠ 0)
    (hmass : ∀ g, 0 < Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0)
    (hon₁ : IsOnShellAt P Φ D f 1) (hK₁ : IsChargeNormalizedAt P Φ D f 1)
    (hon₂ : IsOnShellAt P Φ D f 2) (hK₂ : IsChargeNormalizedAt P Φ D f 2) :
    D.d₁ f 1 = D.d₂ f 1 := by
  classical
  obtain ⟨g₀, -, hg₀⟩ := Finset.exists_min_image Finset.univ Φ.mass ⟨f, Finset.mem_univ f⟩
  have hm₀ : 0 < Φ.mass g₀ := hmass g₀
  have hmass' : ∀ g, Φ.mass g₀ ≤ Φ.mass g := fun g => hg₀ g (Finset.mem_univ g)
  set D₀ := D.withLevel 1 (fun _ => (0, 0, 0)) 0 with hD₀
  have hδ := QED.GradedProof.d₁_eq_d₂_zero' P Φ D f he (hmass f) hmγ hΛ hon₁ hK₁
  obtain ⟨r, hr, A, B, hlim, σ₀, σ₁, hσ₀, hσ₁⟩ := GEx2.exists_seData P Φ D₀ f hm₀ hmass' hmγ hΛ
    hPV₁ hPV₂ (SE2Real.seReal P Φ D₀ f _ hm₀ hmass' hmγ hΛ hPV₁ hPV₂)
  obtain ⟨c, hc⟩ := V5Zero.vertexZeroInput P Φ D₀ f _ hm₀ hmass' hmγ hΛ hPV₁ hPV₂
  have l0 : ∀ g, D.d₁ g 0 = D₀.d₁ g 0 ∧ D.d₂ g 0 = D₀.d₂ g 0 ∧ D.dm g 0 = D₀.dm g 0 :=
    fun g => by simp [hD₀, Counterterms.withLevel]
  have l3 : D.d₃ 0 = D₀.d₃ 0 := by simp [hD₀, Counterterms.withLevel]
  have z : D₀.d₁ f 1 = 0 ∧ D₀.d₂ f 1 = 0 ∧ D₀.dm f 1 = 0 := by
    simp [hD₀, Counterterms.withLevel]
  have hS := (GEx2.isOnShellAt_two_iff P Φ D D₀ f (fun g => (l0 g).1) (fun g => (l0 g).2.1)
    (fun g => (l0 g).2.2) l3 z.2.1 z.2.2 (hmass f) hr hlim hσ₀ hσ₁).1 hon₂
  have hV := (GEx2.isChargeNormalizedAt_two_iff P Φ D D₀ f (l0 f).1 (l0 f).2.1 (l0 f).2.2 l3
    z.1 (hmass f) hc).1 hK₂
  have hδ₀ : D₀.d₁ f 0 = D₀.d₂ f 0 := by rw [← (l0 f).1, ← (l0 f).2.1]; exact hδ
  have hcore := charge_eq_neg_e_mul_slope P Φ D₀ f hm₀ hmass' hmγ hΛ hPV₁ hPV₂ he hδ₀ z.1 z.2.1
    z.2.2 hr hlim hσ₁ hc
  have h5 : P.e ^ 5 * (D.d₁ f 1 - D.d₂ f 1) = 0 := by
    rw [hcore, ← hS.1] at hV
    linear_combination hV
  exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_left (pow_ne_zero 5 he))

end QED.GradedProof.WI2

end
