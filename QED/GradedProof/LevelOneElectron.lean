/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsOnShellAt
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.WickModel.OnePIFunction
public import QED.Frozen.TwoLoop.ContractionValue
public import QED.GradedProof.Embed
public import QED.LeptonProof.EmbedOneZero
import QED.Frozen.TwoLoop.OnePIFunctionEqOnePIFunction
import QED.WickModel.TwoPointClassificationTree
import QED.WickModel.TwoPointClassificationGauge2
import QED.WickModel.ElectronOnShell
import QED.TwoLoop.CountertermScaling
import QED.ChainProof.QuickOrder
import QED.ChainProof.QuickMeaning

/-!
# The order-`e²` on-shell conditions of the graded model

Helper proof of the Phase 5 Stage 2 goal (E-G₂ₛ) `QED.Graded.isOnShellAt_one_iff`
(decision D-57), as `QED.GradedProof.isOnShellAt_one_iff'`.

* `onePIPart_two_selfEnergy`: the 1PI one-electron contractions of order `2` are the `fermionCt`
  tree and the self-energy loop, with no closed fermion line (theorem (E₅)'s classification), so
  the order-`2` part (G₆′) is packet 6a's (X₂₈) at order `≤ 2`, with the open-line level-`0` data
  `e² d₂`, `e² d_m` as counterterms and the open-line mass as `m`.
* The limit of (X₂₈) has the explicit form factors `A_loop - δ₂`, `B_loop - δ_m` on the region of
  (Z₁); any form factors with the limit property on a region `p² > -(M + r)²` agree with them
  near the mass shell (the test momenta of (Z₁)'s uniqueness), so the conditions of (G₉) are those
  of (Z₅) for the explicit form factors, and these are (Z₅) itself.
-/

@[expose] public section

open Complex Filter Topology Set
open QED.WickModel (Params Contraction IsOnePI fermionSign)
open QED.Graded

namespace QED.GradedProof

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### The one-electron contractions of order two -/

/-- A 1PI one-electron contraction of order exactly `2` has only `gauge` and `fermionCt`
vertices. -/
theorem gauge_or_fermionCt_of_selfEnergy (h2 : ∑ t, (κ t).order = 2) (C : Contraction 1 0 κ)
    (hC : IsOnePI C) (t : Fin N) : κ t = .gauge ∨ κ t = .fermionCt := by
  have hN := QED.ChainProof.Quick.le_sum_order κ
  obtain _ | _ | _ | N := N
  · exact t.elim0
  · obtain ⟨k, rfl⟩ : ∃ k, κ = QED.WickModel.oneVertex k := ⟨κ 0, QED.WickModel.eq_oneVertex κ⟩
    by_cases hk : k = .fermionCt
    · exact Or.inr hk
    · exact absurd hC (QED.WickModel.not_isOnePI_oneVertex_selfEnergy hk C)
  · obtain rfl := QED.WickModel.eq_gauge2_of_sum_order_le h2.le
    exact Or.inl rfl
  · omega

/-- No one-electron contraction of order at most `1` is 1PI. -/
theorem not_isOnePI_selfEnergy_of_lt (h : ∑ t, (κ t).order < 2) (C : Contraction 1 0 κ) :
    ¬ IsOnePI C := by
  have hN := QED.ChainProof.Quick.le_sum_order κ
  obtain _ | _ | N := N
  · exact QED.WickModel.not_isOnePI_of_fin_zero_left C
  · obtain ⟨k, rfl⟩ : ∃ k, κ = QED.WickModel.oneVertex k := ⟨κ 0, QED.WickModel.eq_oneVertex κ⟩
    refine QED.WickModel.not_isOnePI_oneVertex_selfEnergy (fun hk => ?_) C
    subst hk
    simp [Wick.VertexKind.order] at h
  · omega

open scoped Classical in
/-- Without closed fermion lines, the value (F₇) is the value (T₁₀) when the open-line mass is
`P.m`. -/
theorem lepton_contractionValue₂_eq_of_reaches (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (hmass : Φ.mass Φ.openLine = P.m) {nf nA : ℕ}
    (C : Contraction nf nA κ) (hC : QED.Lepton.Proof.Reaches C) :
    Lepton.contractionValue₂ P Φ C = QED.WickModel.contractionValue₂ P C := by
  funext pOut pIn kIn αOut βIn μ
  rw [← QED.ChainProof.contractionValue₂_params']
  unfold Lepton.contractionValue₂
  rw [QED.Lepton.Proof.regulatedAmplitude₂_eq_of_reaches P Φ ⟨P.mass, P.loopCoeff, 0⟩ hmass hC]

/-- The parameters with the open-line level-`0` field counterterms of `D` and the open-line
mass. -/
def seParams (Q : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) : Params :=
  { Q with
    m := Φ.mass Φ.openLine
    δ₂ := Q.e ^ 2 * D.d₂ Φ.openLine 0
    δm := Q.e ^ 2 * D.dm Φ.openLine 0 }

open scoped Classical in
/-- **The order-`2` one-electron part is (X₂₈) at order `≤ 2`** at the parameters `seParams`. -/
theorem onePIPart_two_selfEnergy (Q : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 0 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    onePIPart Q Φ D 1 0 2 pOut pIn kIn αOut βIn μ =
      QED.WickModel.onePIFunction (seParams Q Φ D) 1 0 2 pOut pIn kIn αOut βIn μ := by
  rw [← QED.WickModel.onePIFunction₂_eq_onePIFunction _ 1 0 2 (by norm_num)]
  unfold onePIPart
  rw [selectedPart_eq_sum_order_of_le_three Q Φ D 1 0 (fun C => IsOnePI C) 2 (by norm_num)]
  unfold QED.WickModel.onePIFunction₂
  refine Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ hκ => ?_)
  by_cases h2 : ∑ t, (κ t).order = 2
  · rw [ite_eq_left h2]
    refine Finset.sum_congr rfl fun C hC => ?_
    have hC' := (Finset.mem_filter.1 hC).2
    have hcl := gauge_or_fermionCt_of_selfEnergy h2 C hC'
    have hr := QED.Lepton.Proof.reaches_of_one_zero (h2.trans_le (by norm_num)) C hC'
    have hv := contractionValue_zero_eq Q (seParams Q Φ D) Φ D C (fun t _ => hr t) rfl rfl rfl
      rfl (fun t h => absurd h (by rcases hcl t with h' | h' <;> rw [h'] <;> decide))
      (fun _ _ => ⟨rfl, rfl, rfl⟩)
      (fun t h => absurd h (by rcases hcl t with h' | h' <;> rw [h'] <;> decide))
      pOut pIn kIn αOut βIn μ
    rw [hv, lepton_contractionValue₂_eq_of_reaches (seParams Q Φ D) Φ rfl C hr]
  · rw [ite_eq_right h2]
    have hlt : ∑ t, (κ t).order < 2 := lt_of_le_of_ne (Finset.mem_filter.1 hκ).2 h2
    exact (Finset.sum_eq_zero fun C hC =>
      absurd (Finset.mem_filter.1 hC).2 (not_isOnePI_selfEnergy_of_lt hlt C)).symm

/-- The order-`e²` self-energy (G₈ₛ) of flavour `f` is `(1/i)` times (X₂₈) at order `≤ 2` with
mass `M_f` and counterterms `δ₂ = e² d₂ f 0`, `δ_m = e² d_m f 0`. -/
theorem selfEnergyPart_one_apply (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (ε : ℝ) (p : Fin 4 → ℝ) (α β : Fin 4) :
    selfEnergyPart { P with ε := ε } Φ D f 1 p α β = (1 / I) *
      QED.WickModel.onePIFunction
        { { P with m := Φ.mass f, δ₂ := P.e ^ 2 * D.d₂ f 0, δm := P.e ^ 2 * D.dm f 0 } with
          ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![] := by
  simp only [selfEnergyPart, Matrix.of_apply]
  rw [onePIPart_two_selfEnergy]
  rfl

/-! ### The on-shell conditions -/

/-- **Form factors agree near the mass shell.** Two pairs of form factors with the limit property
on regions around `-M²` agree on a neighbourhood of `-M²`. -/
theorem eventuallyEq_of_tendsto {M r r' : ℝ} (hM : 0 < M) (hr : 0 < r) (hr' : 0 < r')
    {S : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} {A B A' B' : ℝ → ℂ}
    (h : ∀ p : Fin 4 → ℝ, -(M + r) ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε => S ε p α β) (𝓝[>] 0)
        (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
          + (B (Minkowski.dot p p) * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)))
    (h' : ∀ p : Fin 4 → ℝ, -(M + r') ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε => S ε p α β) (𝓝[>] 0)
        (𝓝 ((A' (Minkowski.dot p p) • Dirac.slash p
          + (B' (Minkowski.dot p p) * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) :
    ∀ᶠ s in 𝓝 (-M ^ 2), A s = A' s ∧ B s = B' s := by
  have hmem : Ioi (-(M + r) ^ 2) ∩ Ioi (-(M + r') ^ 2) ∈ 𝓝 (-M ^ 2) := by
    refine inter_mem (Ioi_mem_nhds ?_) (Ioi_mem_nhds ?_) <;> nlinarith
  filter_upwards [hmem] with s hs
  have hdot := QED.WickModel.dot_selfEnergyTestMomentum s
  set p := QED.WickModel.selfEnergyTestMomentum s
  have key : ∀ α β : Fin 4, (A s • Dirac.slash p + (B s * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
      α β = (A' s • Dirac.slash p + (B' s * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β := by
    intro α β
    have h1 := h p (hdot ▸ hs.1) α β
    have h2 := h' p (hdot ▸ hs.2) α β
    rw [hdot] at h1 h2
    exact tendsto_nhds_unique h1 h2
  have := QED.WickModel.eq_of_smul_slash_add_apply hM.ne' s key
  exact ⟨(Prod.ext_iff.1 this).1, (Prod.ext_iff.1 this).2⟩

/-- **The on-shell conditions transfer between form factors that agree near the shell.** -/
theorem onShell_congr {M : ℝ} {A B A' B' : ℝ → ℂ}
    (h : ∀ᶠ s in 𝓝 (-M ^ 2), A s = A' s ∧ B s = B' s) :
    (A (-M ^ 2) * ((-M : ℝ) : ℂ) + B (-M ^ 2) * M = 0 ∧
        HasDerivAt (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * M) 0 (-M)) ↔
      (A' (-M ^ 2) * ((-M : ℝ) : ℂ) + B' (-M ^ 2) * M = 0 ∧
        HasDerivAt (fun z : ℝ => A' (-z ^ 2) * (z : ℂ) + B' (-z ^ 2) * M) 0 (-M)) := by
  have h0 := h.self_of_nhds
  have hz : ∀ᶠ z in 𝓝 (-M), A (-z ^ 2) = A' (-z ^ 2) ∧ B (-z ^ 2) = B' (-z ^ 2) := by
    have hc : Tendsto (fun z : ℝ => -z ^ 2) (𝓝 (-M)) (𝓝 (-M ^ 2)) := by
      have h := ((continuous_pow 2).tendsto (-M)).neg
      rw [neg_sq] at h
      exact h
    exact hc.eventually h
  have heq : (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * M) =ᶠ[𝓝 (-M)]
      fun z : ℝ => A' (-z ^ 2) * (z : ℂ) + B' (-z ^ 2) * M := by
    filter_upwards [hz] with z hz
    rw [hz.1, hz.2]
  rw [h0.1, h0.2, heq.hasDerivAt_iff]

/-- (E-G₂ₛ) **The order-`e²` on-shell conditions of flavour `f` are (Z₅) at mass `M_f`** with
`δ₂ = e² d₂ f 0`, `δ_m = e² d_m f 0`. -/
theorem isOnShellAt_one_iff' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (hf : 0 < Φ.mass f)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    IsOnShellAt P Φ D f 1 ↔
      QED.WickModel.IsElectronOnShell
        { P with m := Φ.mass f, δ₂ := P.e ^ 2 * D.d₂ f 0, δm := P.e ^ 2 * D.dm f 0 }
        hf hmγ hΛ := by
  set P' : Params :=
    { P with m := Φ.mass f, δ₂ := P.e ^ 2 * D.d₂ f 0, δm := P.e ^ 2 * D.dm f 0 } with hP'
  set M := Φ.mass f with hM
  set A₀ : ℝ → ℂ := fun s => QED.WickModel.selfEnergyLoopA P' s - P'.δ₂ with hA₀
  set B₀ : ℝ → ℂ := fun s => QED.WickModel.selfEnergyLoopB P' s - P'.δm with hB₀
  have hμ : 0 < min P.mγ P.Λ := lt_min hmγ hΛ
  have hlim₀ : ∀ p : Fin 4 → ℝ, -(M + min P.mγ P.Λ) ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 1 p α β) (𝓝[>] 0)
        (𝓝 ((A₀ (Minkowski.dot p p) • Dirac.slash p
          + (B₀ (Minkowski.dot p p) * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) := by
    intro p hp α β
    simp only [selfEnergyPart_one_apply]
    exact QED.WickModel.tendsto_onePIFunction_selfEnergyLoop P' hf hmγ hΛ p hp α β
  have hZ : QED.WickModel.IsElectronOnShell P' hf hmγ hΛ ↔
      (A₀ (-M ^ 2) * ((-M : ℝ) : ℂ) + B₀ (-M ^ 2) * M = 0 ∧
        HasDerivAt (fun z : ℝ => A₀ (-z ^ 2) * (z : ℂ) + B₀ (-z ^ 2) * M) 0 (-M)) := by
    rw [QED.TwoLoop.Scaling.isElectronOnShell_iff P' hf hmγ hΛ,
      ← QED.WickModel.selfEnergyLoop_onShell_iff P' hf hmγ hΛ, neg_sq]
  rw [hZ]
  unfold IsOnShellAt
  constructor
  · rintro ⟨r, hr, A, B, hlim, hval, hder⟩
    exact (onShell_congr (eventuallyEq_of_tendsto hf hr hμ hlim hlim₀)).1 ⟨hval, hder⟩
  · intro h
    exact ⟨min P.mγ P.Λ, hμ, A₀, B₀, hlim₀, h⟩

end QED.GradedProof

end
