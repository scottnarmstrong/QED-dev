/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2WeightsZero
public import QED.ChainProof.QuickOrder
public import QED.GradedProof.VertexTwo
public import QED.GradedProof.LevelOneElectron
public import QED.GradedProof.LevelOneCharge
public import QED.TwoLoop.OneLoopEmbedding
public import QED.TwoLoop.LoopBound
public import QED.WickModel.TwoPointClassificationTree
public import QED.WickModel.TwoPointClassificationGauge2
public import QED.Frozen.Graded.VacuumPolarizationPart

/-!
# The order-four vacuum polarization as a sum of seven class values

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, step L0.

`vacuumPolarizationPart_two_eq`: at every parameter set,
`Π^{(4) μν}(k) = -e⁴ d₃(1) (k² g^{μν} - k^μ k^ν) + i ∑_X v_X`, the sum over the seven
representatives `X` of `QED/GradedProof/VP2Classes.lean` of their values (G₅) at the zero
grading.

## Proof

Split the graded sum (G₆) into the zero grading and the nonzero gradings
(`selectedPart_split`).

* **Nonzero gradings.** The vertex orders sum to at most `2` and a counterterm vertex is present,
  so there is one vertex, a `photonCt` vertex at level `1` (`eq_photonCt_of_grading_ne_zero`), and
  the two `photonCt` trees give `-i e⁴ d₃(1) (k² g - k k)`
  (`QED.WickModel.sum_isOnePI_polarizationTree`).
* **Zero grading.** `QED/GradedProof/VP2WeightsZero.lean`: the kind sequences of order `4` and
  their 1PI contractions, `1/2! · 2 (G0 + G1) + 1/3! · 6 (F0 + F1) + 1/4! · 24 (VA + VB + VC)`, each
  with sign `-1`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Relabel QED.TwoLoop.Enumeration QED.GradedProof.SE2
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂ fermionSign)

/-! ### Splitting off the zero grading -/

open scoped Classical in
/-- **The graded sum (G₆) split at the zero grading.** -/
theorem selectedPart_split (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (nf nA : ℕ)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Prop) (K : ℕ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    selectedPart P Φ D nf nA (fun C _ => Sel C) K pOut pIn kIn αOut βIn μ =
      (∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ : Fin N → Wick.VertexKind,
          ∑ g ∈ (Fintype.piFinset fun _ : CtVertex κ => Finset.range (K + 1)).filter
              (fun g => gradedOrder κ g = K ∧ g ≠ 0),
            ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter (fun C => Sel C),
              ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ D C g pOut pIn kIn αOut βIn μ) +
      ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
            (fun κ => ∑ t, (κ t).order = K),
          ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter (fun C => Sel C),
            ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ D C 0 pOut pIn kIn αOut βIn μ := by
  unfold selectedPart
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [← mul_add, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun κ _ => ?_)
  set s := (Fintype.piFinset fun _ : CtVertex κ => Finset.range (K + 1)).filter
    (fun g => gradedOrder κ g = K)
  set T : Grading κ → ℂ := fun g =>
    ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter (fun C => Sel C),
      ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ D C g pOut pIn kIn αOut βIn μ
  change ∑ g ∈ s, T g = _
  rw [← Finset.sum_filter_add_sum_filter_not s (fun g => g = 0), add_comm]
  congr 1
  · simp only [s, Finset.filter_filter]
  by_cases hK : ∑ t, (κ t).order = K
  · rw [ite_eq_left hK]
    have h0 : s.filter (fun g => g = 0) = {0} := by
      ext g
      simp only [s, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl
        exact ⟨⟨fun _ => by simp, by rw [gradedOrder_zero, hK]⟩, rfl⟩
    rw [h0, Finset.sum_singleton]
  · rw [ite_eq_right hK]
    refine Finset.sum_eq_zero fun g hg => ?_
    obtain ⟨hg1, rfl⟩ := Finset.mem_filter.1 hg
    exact absurd ((gradedOrder_zero κ).symm.trans (Finset.mem_filter.1 hg1).2) hK

/-! ### The nonzero gradings: the `photonCt` tree -/

/-- A nonzero grading of graded order `4` with a 1PI two-photon contraction has one vertex. -/
theorem eq_one_of_grading_ne_zero {N : ℕ} {κ : Fin N → Wick.VertexKind} {g : Grading κ}
    (hg0 : g ≠ 0) (hg : gradedOrder κ g = 4) (C : Contraction 0 2 κ) (hC : IsOnePI C) :
    N = 1 := by
  obtain ⟨t, ht⟩ : ∃ t : CtVertex κ, 1 ≤ g t := by
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hg0
    exact ⟨t, Nat.one_le_iff_ne_zero.2 ht⟩
  have h2 := Finset.single_le_sum (f := fun t : CtVertex κ => 2 * g t)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  have h4 := hg
  unfold gradedOrder at h4
  have hle : ∑ s, (κ s).order ≤ 2 := by omega
  have hN := QED.ChainProof.Quick.le_sum_order κ
  obtain _ | _ | _ | N := N
  · exact t.1.elim0
  · rfl
  · obtain rfl := QED.WickModel.eq_gauge2_of_sum_order_le hle
    exact (t.2 rfl).elim
  · omega

/-- The single vertex is a `photonCt` vertex. -/
theorem eq_photonCt_of_isOnePI {k : Wick.VertexKind}
    (C : Contraction 0 2 (QED.WickModel.oneVertex k)) (hC : IsOnePI C) : k = .photonCt := by
  by_contra hk
  exact QED.WickModel.not_isOnePI_oneVertex_polarization hk C hC

/-- The parameters of the level-`1` `photonCt` tree. -/
def treeParamsP (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) : Params :=
  { P with δ₃ := P.e ^ 4 * D.d₃ 1, m := Φ.mass Φ.openLine }

/-- The grading `1` of the single `photonCt` vertex. -/
def gOne : Grading (QED.WickModel.oneVertex .photonCt) := fun _ => 1

theorem eq_gOne {g : Grading (QED.WickModel.oneVertex .photonCt)}
    (hg : gradedOrder (QED.WickModel.oneVertex .photonCt) g = 4) : g = gOne := by
  have hsub : ∀ s t : CtVertex (QED.WickModel.oneVertex .photonCt), s = t :=
    fun s t => Subtype.ext (Subsingleton.elim (α := Fin 1) _ _)
  have hord : ∑ s, (QED.WickModel.oneVertex Wick.VertexKind.photonCt s).order = 2 := by decide
  unfold gradedOrder at hg
  rw [hord] at hg
  funext t
  have : ∑ s : CtVertex (QED.WickModel.oneVertex .photonCt), 2 * g s = 2 * g t := by
    rw [Fintype.sum_eq_single t fun s hs => absurd (hsub s t) hs]
  simp only [gOne]
  omega

open scoped Classical in
/-- **The nonzero gradings: the level-`1` `photonCt` tree.** -/
theorem treeSum_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 0 2 κ → Prop)
    (hSel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 0 2 κ), Sel C ↔ IsOnePI C) :
    (∑ N ∈ Finset.range (4 + 1), (N.factorial : ℂ)⁻¹ *
      ∑ κ : Fin N → Wick.VertexKind,
        ∑ g ∈ (Fintype.piFinset fun _ : CtVertex κ => Finset.range (4 + 1)).filter
            (fun g => gradedOrder κ g = 4 ∧ g ≠ 0),
          ∑ C ∈ (Finset.univ : Finset (Contraction 0 2 κ)).filter (fun C => Sel C),
            ((fermionSign C : ℤ) : ℂ) *
              contractionValue P Φ D C g ![] ![] ![k, -k] ![] ![] ![μ, ν]) =
      -I * ((P.e ^ 4 * D.d₃ 1 * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ) :
        ℂ) := by
  have hzero : ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ),
      (g ∈ (Fintype.piFinset fun _ : CtVertex κ => Finset.range (4 + 1)).filter
        (fun g => gradedOrder κ g = 4 ∧ g ≠ 0)) →
      ∀ C ∈ (Finset.univ : Finset (Contraction 0 2 κ)).filter (fun C => Sel C),
        N = 1 ∧ ∀ h : N = 1, κ = h ▸ QED.WickModel.oneVertex .photonCt := by
    intro N κ g hg C hC
    obtain ⟨-, hg4, hg0⟩ := Finset.mem_filter.1 hg
    have hC' := (hSel C).1 (Finset.mem_filter.1 hC).2
    have h1 := eq_one_of_grading_ne_zero hg0 hg4 C hC'
    refine ⟨h1, fun h => ?_⟩
    subst h
    obtain ⟨k0, rfl⟩ : ∃ k0, κ = QED.WickModel.oneVertex k0 :=
      ⟨κ 0, QED.WickModel.eq_oneVertex κ⟩
    obtain rfl := eq_photonCt_of_isOnePI _ hC'
    rfl
  rw [Finset.sum_eq_single 1]
  · rw [Finset.sum_eq_single (QED.WickModel.oneVertex .photonCt)]
    · rw [Finset.sum_eq_single gOne]
      · simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul]
        have hv : ∀ C : Contraction 0 2 (QED.WickModel.oneVertex .photonCt), IsOnePI C →
            contractionValue P Φ D C gOne ![] ![] ![k, -k] ![] ![] ![μ, ν] =
              QED.WickModel.contractionValue (treeParamsP P Φ D) C ![] ![] ![k, -k] ![] ![]
                ![μ, ν] := by
          intro C hC
          have hR : QED.Lepton.Proof.Reaches C := fun t =>
            (t.2 (by simp [QED.WickModel.oneVertex])).elim
          rw [contractionValue_eq_of_grading P (treeParamsP P Φ D) Φ D C (ctReaches_of_reaches hR)
            gOne rfl rfl rfl rfl
            (fun t h => absurd h (by simp [QED.WickModel.oneVertex]))
            (fun t h => absurd h (by simp [QED.WickModel.oneVertex]))
            (fun t _ => by simp [treeParamsP, gOne])]
          rw [lepton_contractionValue₂_eq_of_reaches (treeParamsP P Φ D) Φ rfl C hR,
            QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one
              (treeParamsP P Φ D) _
              (QED.TwoLoop.LoopBound.loopCount_le_one_of_order (K := 2) (by decide)
                (by norm_num) _ hC)]
        rw [Finset.sum_congr rfl fun C hC => by rw [hv C ((hSel C).1 (Finset.mem_filter.1 hC).2)]]
        convert QED.WickModel.sum_isOnePI_polarizationTree (treeParamsP P Φ D) ![] ![] ![] ![] k
          μ ν using 1
        all_goals first
          | rfl
          | exact Finset.sum_congr (Finset.ext fun C => by simp [hSel C]) fun _ _ => rfl
      · intro g hg hne
        exact absurd (eq_gOne (Finset.mem_filter.1 hg).2.1) hne
      · intro h
        refine absurd (Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun _ => by simp [gOne],
          by decide, fun h0 => ?_⟩) h
        have := congrFun h0 ⟨0, by simp [QED.WickModel.oneVertex]⟩
        simp [gOne] at this
    · intro κ _ hκ
      refine Finset.sum_eq_zero fun g hg => Finset.sum_eq_zero fun C hC => ?_
      exact absurd ((hzero 1 κ g hg C hC).2 rfl) hκ
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro N _ hN
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun κ _ => Finset.sum_eq_zero fun g hg =>
      Finset.sum_eq_zero fun C hC => ?_)
    exact absurd (hzero N κ g hg C hC).1 hN
  · intro h
    simp at h

/-! ### The zero grading and the total -/

theorem sval_eq_neg {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 0 2 κ}
    (h : fermionSign C = -1) (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    sval P Φ D k μ ν C = -val0 P Φ D k μ ν C := by
  simp [sval, h]

open scoped Classical in
/-- **The zero grading**: minus the sum of the seven class values. -/
theorem zeroSum_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 0 2 κ → Prop)
    (hSel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 0 2 κ), Sel C ↔ IsOnePI C) :
    (∑ N ∈ Finset.range (4 + 1), (N.factorial : ℂ)⁻¹ *
      ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
          (fun κ => ∑ t, (κ t).order = 4),
        ∑ C ∈ (Finset.univ : Finset (Contraction 0 2 κ)).filter (fun C => Sel C),
          ((fermionSign C : ℤ) : ℂ) *
            contractionValue P Φ D C 0 ![] ![] ![k, -k] ![] ![] ![μ, ν]) =
      -(val0 P Φ D k μ ν repVA + val0 P Φ D k μ ν repVB + val0 P Φ D k μ ν repVC +
        val0 P Φ D k μ ν repG0 + val0 P Φ D k μ ν repG1 + val0 P Φ D k μ ν repF0 +
        val0 P Φ D k μ ν repF1) := by
  have hz : ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind),
      ∑ C ∈ (Finset.univ : Finset (Contraction 0 2 κ)).filter (fun C => Sel C),
          ((fermionSign C : ℤ) : ℂ) *
            contractionValue P Φ D C 0 ![] ![] ![k, -k] ![] ![] ![μ, ν] =
        zsum P Φ D k μ ν κ (fun C => Sel C) := fun _ _ => rfl
  have hnil : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (l : List (Contraction 0 2 κ)),
      l = [] → (∀ C, IsOnePI C ↔ C ∈ l) → zsum P Φ D k μ ν κ (fun C => Sel C) = 0 := by
    intro N κ l hl h
    subst hl
    exact zsum_nil hSel h
  simp only [hz, Finset.sum_range_succ, Finset.sum_range_zero, filter_order_eq_four_zero,
    filter_order_eq_four_one, filter_order_eq_four_four, Finset.sum_empty, Finset.sum_singleton]
  rw [filter_order_eq_four_two, filter_order_eq_four_three, List.sum_toFinset _ (by decide),
    List.sum_toFinset _ (by decide)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [zsum_gC hSel, zsum_Cg hSel, zsum_ggf hSel,
    zsum_gfg hSel, zsum_fgg hSel, zsum_gggg hSel,
    hnil onePI2_ff rfl isOnePI2_iff_ff, hnil onePI2_fp rfl isOnePI2_iff_fp,
    hnil onePI2_pf rfl isOnePI2_iff_pf, hnil onePI2_pp rfl isOnePI2_iff_pp,
    hnil onePI2_ggp rfl isOnePI2_iff_ggp, hnil onePI2_gpg rfl isOnePI2_iff_gpg,
    hnil onePI2_pgg rfl isOnePI2_iff_pgg]
  simp only [sval_eq_neg fermionSign_repVA, sval_eq_neg fermionSign_repVB,
    sval_eq_neg fermionSign_repVC, sval_eq_neg fermionSign_repG0, sval_eq_neg fermionSign_repG1,
    sval_eq_neg fermionSign_repF0, sval_eq_neg fermionSign_repF1]
  simp only [Nat.factorial, Nat.succ_eq_add_one]
  push_cast
  ring

/-- **The order-four vacuum polarization as a sum of seven class values** and the
level-`1` photon counterterm. -/
theorem vacuumPolarizationPart_two_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    vacuumPolarizationPart P Φ D 2 k μ ν =
      -((P.e ^ 4 * D.d₃ 1 * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ) : ℂ) +
        I * (val0 P Φ D k μ ν repVA + val0 P Φ D k μ ν repVB + val0 P Φ D k μ ν repVC +
          val0 P Φ D k μ ν repG0 + val0 P Φ D k μ ν repG1 + val0 P Φ D k μ ν repF0 +
          val0 P Φ D k μ ν repF1) := by
  unfold vacuumPolarizationPart onePIPart
  rw [show 2 * 2 = 4 from rfl, selectedPart_split P Φ D 0 2 (fun C => IsOnePI C) 4,
    treeSum_eq P Φ D k μ ν (fun C => IsOnePI C) (fun _ => Iff.rfl),
    zeroSum_eq P Φ D k μ ν (fun C => IsOnePI C) (fun _ => Iff.rfl)]
  rw [one_div, Complex.inv_I]
  ring_nf
  rw [Complex.I_sq]
  ring

end QED.GradedProof.VP2

end
