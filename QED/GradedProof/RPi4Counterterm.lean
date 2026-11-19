/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Setup
public import QED.Frozen.Graded.WardIdentityZero
public import QED.Frozen.Graded.IsOnShellAtOneIff
public import QED.TwoLoop.CountertermScaling

/-!
# (R-Π₄): the level-`0` fermion counterterms in closed form

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), lemma L4 of the plan. The
order-`e⁴` vacuum polarization reads the level-`0` fermion counterterms on the closed loop of each
flavour `f` as the `fermionCt` vertex `d₂ p̸ + d_m M_f` and the `gaugeCt` vertex `d₁ γ^μ`.

* `d₁_eq_d₂_of_renormalized`: through order `e²` and with `e ≠ 0`, `d₁ = d₂` at level `0` on
  every flavour (the sealed `QED.Graded.d₁_eq_d₂_zero` at each representative, transported along
  the block).
* `polG_eq_polBlock_d₂`: hence the limit coefficient of the classes `G0`, `G1` is the block bubble
  with coupling `e² d₂`.
* `numerator_fermionCt_numerator`: `N (d₂ y̸ + d_m M) N = d₂ (y² + M²) N + (d_m - d₂) M N²` for
  `N = M - y̸`; so the `d₂` part of an insertion contracts one propagator (`insG_eq`), and only
  the mass insertion `δ = e² (d_m - d₂)` survives, up to an `iε` remainder.
* `onShellδm_sub_onShellδ₂`, `onShellδm_sub_onShellδ₂_eq_integral`: on shell,
  `δ = (B - A)(-m²) = -(e²/4π²) ∫ L + (e²/8π²) ∫ (1 - x) L` with
  `L(x) = log (D_Λ / D_{m_γ})`, `D_μ = x² m² + (1 - x) μ²` (`onShellL`,
  `selfEnergyFeynmanMass_neg_sq`).
* `sq_mul_dm_sub_d₂`: at an on-shell flavour `f`, `e² (d_m - d₂)(f) = (B - A)(-M_f²)` computed at
  the mass `M_f`.
-/

@[expose] public section

open Complex
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

/-! ### The Ward step: `d₁ = d₂` at level `0` -/

section Ward

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) {rep : F → F}

/-- **`d₁ = d₂` at level `0` on every flavour**, from the on-shell and charge conditions at the
representatives and the block constancy of the level-`0` counterterms. -/
theorem d₁_eq_d₂_of_renormalized {n : ℕ} (hn : 1 ≤ n) (he : P.e ≠ 0)
    (hpos : ∀ g, 0 < Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f) (h : IsRenormalizedThrough P Φ D rep n) (f : F) :
    D.d₁ f 0 = D.d₂ f 0 := by
  obtain ⟨h₁, h₂, -⟩ := h.1 f 0 (by omega)
  obtain ⟨hon, hK⟩ := (h.2 1 le_rfl hn).1 (rep f) (hrep f)
  rw [h₁, h₂]
  exact d₁_eq_d₂_zero P Φ D (rep f) he (hpos _) hmγ hΛ hon hK

omit [DecidableEq F] in
/-- **The classes `G0`, `G1` carry the block bubble with coupling `e² d₂`** once `d₁ = d₂`. -/
theorem polG_eq_polBlock_d₂ (h : ∀ f, D.d₁ f 0 = D.d₂ f 0) (s : ℝ) :
    QED.GradedProof.VP2.polG P Φ D rep s =
      QED.GradedProof.VP2.polBlock P Φ rep (fun b => ((P.e ^ 2 * D.d₂ b 0 : ℝ) : ℂ)) s := by
  simp only [QED.GradedProof.VP2.polG, h]

end Ward

/-! ### The insertion contracts a propagator -/

section Insertion

open QED.TwoLoop.Bridge (electronNumerator propDenom)
open QED.TwoLoop.Insertion (fermionCtMatrix)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- **The `fermionCt` insertion between two numerators**:
`N (d₂ y̸ + d_m M) N = d₂ (y² + M²) N + (d_m - d₂) M N²` for `N = M - y̸`. -/
theorem numerator_fermionCt_numerator (d₂ dm M : ℝ) (y : Fin 4 → ℝ) :
    electronNumerator M y * fermionCtMatrix d₂ dm M y * electronNumerator M y =
      ((d₂ : ℂ) * ((Minkowski.dot y y + M ^ 2 : ℝ) : ℂ)) • electronNumerator M y +
        (((dm - d₂) * M : ℝ) : ℂ) • (electronNumerator M y * electronNumerator M y) := by
  have hs := QED.Dirac.slash_mul_slash y
  simp only [electronNumerator, fermionCtMatrix]
  have e : ((d₂ : ℂ) • Dirac.slash y + ((dm * M : ℝ) : ℂ) • (1 : Mat)) =
      (d₂ : ℂ) • (Dirac.slash y + (M : ℂ) • (1 : Mat)) + (((dm - d₂) * M : ℝ) : ℂ) • (1 : Mat) := by
    rw [smul_add, add_assoc, smul_smul, ← add_smul]
    push_cast
    ring_nf
  rw [e]
  have hN : ((M : ℂ) • (1 : Mat) - Dirac.slash y) * (Dirac.slash y + (M : ℂ) • (1 : Mat)) =
      ((Minkowski.dot y y + M ^ 2 : ℝ) : ℂ) • (1 : Mat) := by
    rw [sub_mul, mul_add, mul_add, hs]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    push_cast
    module
  rw [mul_add, mul_smul_comm, hN, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul,
    mul_smul_comm, mul_one, smul_smul, smul_mul_assoc]

/-- The trace of a bubble with numerators `N_x`, `N_y`. -/
noncomputable def bubTr (A B : Mat) (M : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  (A * electronNumerator M x * B * electronNumerator M y).trace

/-- The trace of a bubble with a doubled numerator `N_y²` (the mass insertion). -/
noncomputable def massTr (A B : Mat) (M : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  (A * electronNumerator M x * B * (electronNumerator M y * electronNumerator M y)).trace

/-- **The inserted bubble splits** into the `d₂` bubble (one propagator contracted, with the
remainder `iε D_y⁻¹`) and the mass insertion with `δ = d_m - d₂`. -/
theorem insG_eq {A B : Mat} (d₂ dm M : ℝ) {ε : ℝ} (hε : ε ≠ 0) (x y : Fin 4 → ℝ) :
    QED.GradedProof.VP2.insG A B d₂ dm M ε x y =
      (d₂ : ℂ) * (1 + (ε : ℂ) * I * (propDenom M ε y)⁻¹) *
          (bubTr A B M x y * (propDenom M ε x)⁻¹ * (propDenom M ε y)⁻¹) +
        (((dm - d₂) * M : ℝ) : ℂ) *
          (massTr A B M x y * (propDenom M ε x)⁻¹ * ((propDenom M ε y)⁻¹) ^ 2) := by
  have hD : propDenom M ε y ≠ 0 := QED.TwoLoop.Bridge.propDenom_ne_zero hε y
  have hDy : ((Minkowski.dot y y + M ^ 2 : ℝ) : ℂ) = propDenom M ε y + (ε : ℂ) * I := by
    simp only [propDenom]
    ring
  simp only [QED.GradedProof.VP2.insG, QED.GradedProof.VP2.insTr, bubTr, massTr]
  have e : A * electronNumerator M x * B * electronNumerator M y *
        fermionCtMatrix d₂ dm M y * electronNumerator M y =
      A * electronNumerator M x * B *
        (electronNumerator M y * fermionCtMatrix d₂ dm M y * electronNumerator M y) := by
    simp only [Matrix.mul_assoc]
  rw [e, numerator_fermionCt_numerator, mul_add, Matrix.trace_add, mul_smul_comm,
    mul_smul_comm, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, hDy]
  field_simp

end Insertion

/-! ### The on-shell mass insertion in closed form -/

section OnShell

open QED.WickModel (selfEnergyLoopA selfEnergyLoopB selfEnergyFeynmanMass onShellδ₂ onShellδm)

/-- On shell, `D_μ(-m², x) = x² m² + (1 - x) μ²`. -/
theorem selfEnergyFeynmanMass_neg_sq (m μ x : ℝ) :
    selfEnergyFeynmanMass m μ (-m ^ 2) x = x ^ 2 * m ^ 2 + (1 - x) * μ ^ 2 := by
  simp only [selfEnergyFeynmanMass]
  ring

/-- **The surviving mass insertion is `(B - A)(-m²)`.** -/
theorem onShellδm_sub_onShellδ₂ (P : Params) :
    onShellδm P - onShellδ₂ P =
      (selfEnergyLoopB P (-P.m ^ 2)).re - (selfEnergyLoopA P (-P.m ^ 2)).re := by
  simp only [onShellδm, onShellδ₂]
  ring

/-- The on-shell logarithm `L(x) = log (D_Λ / D_{m_γ})`, `D_μ = x² m² + (1 - x) μ²`. -/
noncomputable def onShellL (m mγ Λ x : ℝ) : ℝ :=
  Real.log ((x ^ 2 * m ^ 2 + (1 - x) * Λ ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * mγ ^ 2))

/-- **`(B - A)(-m²)` in closed form**:
`-(e²/4π²) ∫₀¹ L + (e²/8π²) ∫₀¹ (1 - x) L` with `L = onShellL m m_γ Λ`. -/
theorem onShellδm_sub_onShellδ₂_eq_integral (P : Params) :
    onShellδm P - onShellδ₂ P =
      -(P.e ^ 2 / (4 * Real.pi ^ 2)) * (∫ x in (0 : ℝ)..1, onShellL P.m P.mγ P.Λ x) +
        P.e ^ 2 / (8 * Real.pi ^ 2) * ∫ x in (0 : ℝ)..1, (1 - x) * onShellL P.m P.mγ P.Λ x := by
  have hL : (fun x => Real.log (selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x /
      selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x)) = onShellL P.m P.mγ P.Λ := by
    funext x
    rw [selfEnergyFeynmanMass_neg_sq, selfEnergyFeynmanMass_neg_sq, onShellL]
  have hL' : (fun x => (1 - x) * Real.log (selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x /
      selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x)) =
      fun x => (1 - x) * onShellL P.m P.mγ P.Λ x := by
    funext x
    rw [selfEnergyFeynmanMass_neg_sq, selfEnergyFeynmanMass_neg_sq, onShellL]
  rw [onShellδm_sub_onShellδ₂]
  simp only [selfEnergyLoopA, selfEnergyLoopB, ofReal_re]
  rw [hL, hL']
  ring

variable {P : Params} {F : Type} [Fintype F] [DecidableEq F] {Φ : Lepton.Flavors F}
  {D : Counterterms F}

/-- **The level-`0` mass insertion at an on-shell flavour**:
`e² (d_m - d₂)(f) = (B - A)(-M_f²)`, with `A`, `B` at the mass `M_f`. -/
theorem sq_mul_dm_sub_d₂ {f : F} (hf : 0 < Φ.mass f) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hon : IsOnShellAt P Φ D f 1) :
    P.e ^ 2 * (D.dm f 0 - D.d₂ f 0) =
      onShellδm { P with m := Φ.mass f } - onShellδ₂ { P with m := Φ.mass f } := by
  have hE := (isOnShellAt_one_iff P Φ D f hf hmγ hΛ).1 hon
  obtain ⟨h₂, hm⟩ := (QED.TwoLoop.Scaling.isElectronOnShell_iff _ _ _ _).1 hE
  rw [mul_sub]
  exact congrArg₂ (· - ·) hm h₂

end OnShell

end QED.GradedProof.RPi4

end
