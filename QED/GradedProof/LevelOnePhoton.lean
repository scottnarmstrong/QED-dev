/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsPhotonOnShellAt
public import QED.Frozen.Lepton.IsPhotonOnShell
public import QED.GradedProof.Embed
import QED.WickModel.TwoPointClassificationTree
import QED.WickModel.TwoPointClassificationGauge2
import QED.ChainProof.QuickOrder

/-!
# The order-`e²` photon condition of the graded model

Helper proof of the Phase 5 Stage 2 goal (E-G₂ₚ) `QED.Graded.isPhotonOnShellAt_one_iff`
(decision D-57), as `QED.GradedProof.isPhotonOnShellAt_one_iff'`.

The 1PI two-photon contractions of order at most `2` are the `photonCt` tree and the
flavour-summed loop on two `gauge` vertices (packet 6a's classification): no vertex sequence of
order `0` or `1` has one, and a single `fermionCt` vertex has none. So the order-`2` part (G₆′)
has no fermion counterterm vertex, its photon counterterm is `e² d₃ 0`, and it is the whole
order-`≤ 2` function (F₈) with `δ₃ = e² d₃ 0` (`onePIPart_two_photon`).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params Contraction IsOnePI)
open QED.Graded

namespace QED.GradedProof

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- A 1PI two-photon contraction of order exactly `2` has only `gauge` and `photonCt`
vertices. -/
theorem gauge_or_photonCt_of_two_photon (h2 : ∑ t, (κ t).order = 2) (C : Contraction 0 2 κ)
    (hC : IsOnePI C) (t : Fin N) : κ t = .gauge ∨ κ t = .photonCt := by
  have hN := QED.ChainProof.Quick.le_sum_order κ
  obtain _ | _ | _ | N := N
  · exact t.elim0
  · obtain ⟨k, rfl⟩ : ∃ k, κ = QED.WickModel.oneVertex k := ⟨κ 0, QED.WickModel.eq_oneVertex κ⟩
    by_cases hk : k = .photonCt
    · exact Or.inr hk
    · exact absurd hC (QED.WickModel.not_isOnePI_oneVertex_polarization hk C)
  · obtain rfl := QED.WickModel.eq_gauge2_of_sum_order_le h2.le
    exact Or.inl rfl
  · omega

/-- No two-photon contraction of order at most `1` is 1PI. -/
theorem not_isOnePI_two_photon_of_lt (h : ∑ t, (κ t).order < 2) (C : Contraction 0 2 κ) :
    ¬ IsOnePI C := by
  have hN := QED.ChainProof.Quick.le_sum_order κ
  obtain _ | _ | N := N
  · exact QED.WickModel.not_isOnePI_of_fin_zero_right C
  · obtain ⟨k, rfl⟩ : ∃ k, κ = QED.WickModel.oneVertex k := ⟨κ 0, QED.WickModel.eq_oneVertex κ⟩
    refine QED.WickModel.not_isOnePI_oneVertex_polarization (fun hk => ?_) C
    subst hk
    simp [Wick.VertexKind.order] at h
  · omega

open scoped Classical in
/-- **The order-`2` two-photon part is (F₈) at order `≤ 2`** with `δ₃ = e² d₃ 0`. -/
theorem onePIPart_two_photon (Q : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (pOut pIn : Fin 0 → Fin 4 → ℝ)
    (kIn : Fin 2 → Fin 4 → ℝ) (αOut βIn : Fin 0 → Fin 4) (μ : Fin 2 → Fin 4) :
    onePIPart Q Φ D 0 2 2 pOut pIn kIn αOut βIn μ =
      Lepton.onePIFunction₂ { Q with δ₃ := Q.e ^ 2 * D.d₃ 0 } Φ 0 2 2 pOut pIn kIn αOut βIn
        μ := by
  unfold onePIPart
  rw [selectedPart_eq_sum_order_of_le_three Q Φ D 0 2 (fun C => IsOnePI C) 2 (by norm_num)]
  unfold Lepton.onePIFunction₂
  refine Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ hκ => ?_)
  by_cases h2 : ∑ t, (κ t).order = 2
  · rw [ite_eq_left h2]
    refine Finset.sum_congr rfl fun C hC => ?_
    have hC' := (Finset.mem_filter.1 hC).2
    have hcl := gauge_or_photonCt_of_two_photon h2 C hC'
    have hR : CtReaches C := fun t ht => by
      rcases hcl t.1 with h' | h'
      · exact absurd h' ht
      · exact absurd h' t.2
    have hv := contractionValue_zero_eq Q { Q with δ₃ := Q.e ^ 2 * D.d₃ 0 } Φ D C hR rfl rfl rfl
      rfl (fun t h => absurd h (by rcases hcl t with h' | h' <;> rw [h'] <;> decide))
      (fun t h => absurd h (by rcases hcl t with h' | h' <;> rw [h'] <;> decide))
      (fun _ _ => rfl) pOut pIn kIn αOut βIn μ
    rw [hv]
  · rw [ite_eq_right h2]
    have hlt : ∑ t, (κ t).order < 2 := lt_of_le_of_ne (Finset.mem_filter.1 hκ).2 h2
    exact (Finset.sum_eq_zero fun C hC =>
      absurd (Finset.mem_filter.1 hC).2 (not_isOnePI_two_photon_of_lt hlt C)).symm

/-- (E-G₂ₚ) **The order-`e²` photon condition is (F₁₁)** with `δ₃ = e² d₃ 0`. -/
theorem isPhotonOnShellAt_one_iff' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) :
    IsPhotonOnShellAt P Φ D 1 ↔ Lepton.IsPhotonOnShell { P with δ₃ := P.e ^ 2 * D.d₃ 0 } Φ := by
  unfold IsPhotonOnShellAt Lepton.IsPhotonOnShell vacuumPolarizationPart
  have key : ∀ (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4),
      onePIPart { P with ε := ε } Φ D 0 2 (2 * 1) ![] ![] ![k, -k] ![] ![] ![μ, ν] =
        Lepton.onePIFunction₂ { P with δ₃ := P.e ^ 2 * D.d₃ 0, ε := ε } Φ 0 2 2 ![] ![]
          ![k, -k] ![] ![] ![μ, ν] :=
    fun ε k μ ν => onePIPart_two_photon { P with ε := ε } Φ D _ _ _ _ _ _
  simp only [key]

end QED.GradedProof

end
