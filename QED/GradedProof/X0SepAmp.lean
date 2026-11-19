/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0SepTerm
public import QED.GradedProof.X0ClosedOne

/-!
# (X₀): (T₉′) of a two-loop contraction with closed loops whose loops share no line

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57). Let `C` be a
contraction of `gauge` vertices with two loops sharing no line (`SepLines C`). Three shapes:

* the lines along `ℓ₀` are a closed loop (`grpZ C 0`), the lines along `ℓ₁` open-line and photon
  lines (`jointEnergyFirstIntegrable_sepClosed₀`);
* the same with `ℓ₀` and `ℓ₁` exchanged (`jointEnergyFirstIntegrable_sepClosed₁`);
* both groups are closed loops (`jointEnergyFirstIntegrable_sepClosed₂`).

In each, the integrand of (X₀) at the zero grading satisfies (T₉′) at any masses, under the
block hypotheses of (X₀): flavour sum (`regulatedAmplitude_eq_closed`, `_closed₂`), index terms
(`ampTerm_sep`), groups (`jointEnergyFirstIntegrable_closedGrp`, `_openGrp`), Fubini.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type} [Fintype F] [DecidableEq F]
  {C : Contraction 1 nA κ}

/-- No line carries both loop momenta. -/
def SepLines (C : Contraction 1 nA κ) : Prop :=
  ∀ l : Line C, loopCoeff C l 0 = 0 ∨ loopCoeff C l 1 = 0

instance (C : Contraction 1 nA κ) : Decidable (SepLines C) := by
  unfold SepLines; infer_instance

omit [Fintype F] [DecidableEq F] in
theorem sepConst_congr (P : Params) (Φ : Lepton.Flavors F) {φ ψ : Flavoring F κ}
    (h : ∀ f ∈ treeF C, φ f.1 = ψ f.1) (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) :
    sepConst P Φ C φ pOut pIn kIn αOut βIn μ α β lor =
      sepConst P Φ C ψ pOut pIn kIn αOut βIn μ α β lor := by
  unfold sepConst
  rw [fProd_congr P Φ α β h]

omit [Fintype F] [DecidableEq F] in
theorem sepConst_eq_zero (P : Params) (Φ : Lepton.Flavors F) (φ : Flavoring F κ)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (h : ∏ t, Wick.vertexFactor P.e 0 0 0 0 0 α β lor 0 0 t = 0) :
    sepConst P Φ C φ pOut pIn kIn αOut βIn μ α β lor = 0 := by
  unfold sepConst
  rw [h]
  ring

omit [Fintype F] [DecidableEq F] in
theorem gProd_empty (P : Params) (lor : Wick.PhotonSlot κ → Fin 4) {j : ℕ}
    (hG : ∀ g : PhotonLine C, loopCoeff C (.inr g) j = 0) (k : PhotonLine C → Fin 4 → ℝ) :
    gProd P lor (grpG C j) k = 1 := by
  have : grpG C j = ∅ := Finset.filter_eq_empty_iff.mpr fun g _ => by simp [hG g]
  rw [this, gProd, Finset.prod_empty]

theorem not_grpZ_of_eq_zero {j : ℕ} {f : FermionLine C} (h : loopCoeff C (.inl f) j = 0) :
    ¬ grpZ C j f.1 := fun h' => (grpZ_iff j f).mp h' h

/-- The open-line flavouring. -/
def openFl (Φ : Lepton.Flavors F) : Flavoring F κ := fun _ => Φ.openLine

/-- **One index term, closed loop along `ℓ₀`**, summed over the flavours. -/
theorem jointEnergyFirstIntegrable_sepTerm₀ (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (hF : SepLines C)
    (hZ : ∀ x, isZ (grpZ C 0) (C.1.1 x) = isZ (grpZ C 0) x)
    (hG : ∀ g : PhotonLine C, loopCoeff C (.inr g) 0 = 0)
    (h1 : 1 ≤ Fintype.card (ZLine C (grpZ C 0))) (h4 : Fintype.card (ZLine C (grpZ C 0)) ≤ 4)
    (o3 : (grpF C 1).card ≤ 3) (o4 : 4 < (grpF C 1).card + 4 * (grpG C 1).card)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * (z * ampTerm P Φ D C (closedFlavoring Φ (grpZ C 0) f) pIn kIn
        (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ α β lor) := by
  classical
  simp only [ampTerm_sep P Φ D hκ hF]
  have hT : ∀ f, ∀ x ∈ treeF C, closedFlavoring Φ (grpZ C 0) f x.1 = openFl Φ x.1 :=
    fun f x hx => by
      simp [closedFlavoring, openFl, not_grpZ_of_eq_zero (Finset.mem_filter.mp hx).2.1]
  have hO : ∀ f, ∀ x ∈ grpF C 1, closedFlavoring Φ (grpZ C 0) f x.1 = openFl Φ x.1 :=
    fun f x hx => by
      have h0 : loopCoeff C (.inl x) 0 = 0 :=
        (hF _).resolve_right (Finset.mem_filter.mp hx).2
      simp [closedFlavoring, openFl, not_grpZ_of_eq_zero h0]
  simp only [sepConst_congr P Φ (hT _), fProd_congr P Φ α β (S := grpF C 1) (hO _),
    gProd_empty P lor hG, mul_one]
  by_cases hΓ : ∏ t, Wick.vertexFactor P.e 0 0 0 0 0 α β lor 0 0 t = 0
  · simp only [sepConst_eq_zero P Φ _ pOut pIn kIn αOut βIn μ α β lor hΓ, zero_mul, mul_zero,
      Finset.sum_const_zero]
    exact jointEnergyFirstIntegrable_zero_fun'
  have hA := jointEnergyFirstIntegrable_closedGrp P Φ rep hrep hPV₁ hPV₂ hε 0 hZ α β
    (not_blk_of_prod_ne_zero P.e hκ α β lor hΓ) pOut pIn kIn h1 h4
  have hB := jointEnergyFirstIntegrable_openGrp P Φ hε (openFl Φ) α β lor 1 pOut pIn kIn o3 o4
  have h := jointEnergyFirstIntegrable_two_mul
    (A := fun x => ∑ f, (Φ.coeff f : ℂ) * fProd P Φ (closedFlavoring Φ (grpZ C 0) f) α β (grpF C 0)
      (kF C 0 pOut pIn kIn x))
    (B := (fun x => fProd P Φ (openFl Φ) α β (grpF C 1) (kF C 1 pOut pIn kIn x) *
      gProd P lor (grpG C 1) (kG C 1 pOut pIn kIn x))) hA hB
    (z * sepConst P Φ C (openFl Φ) pOut pIn kIn αOut βIn μ α β lor)
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun f _ => by ring

/-- **One index term, closed loop along `ℓ₁`**, summed over the flavours. -/
theorem jointEnergyFirstIntegrable_sepTerm₁ (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (hF : SepLines C)
    (hZ : ∀ x, isZ (grpZ C 1) (C.1.1 x) = isZ (grpZ C 1) x)
    (hG : ∀ g : PhotonLine C, loopCoeff C (.inr g) 1 = 0)
    (h1 : 1 ≤ Fintype.card (ZLine C (grpZ C 1))) (h4 : Fintype.card (ZLine C (grpZ C 1)) ≤ 4)
    (o3 : (grpF C 0).card ≤ 3) (o4 : 4 < (grpF C 0).card + 4 * (grpG C 0).card)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * (z * ampTerm P Φ D C (closedFlavoring Φ (grpZ C 1) f) pIn kIn
        (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ α β lor) := by
  classical
  simp only [ampTerm_sep P Φ D hκ hF]
  have hT : ∀ f, ∀ x ∈ treeF C, closedFlavoring Φ (grpZ C 1) f x.1 = openFl Φ x.1 :=
    fun f x hx => by
      simp [closedFlavoring, openFl, not_grpZ_of_eq_zero (Finset.mem_filter.mp hx).2.2]
  have hO : ∀ f, ∀ x ∈ grpF C 0, closedFlavoring Φ (grpZ C 1) f x.1 = openFl Φ x.1 :=
    fun f x hx => by
      have h0 : loopCoeff C (.inl x) 1 = 0 :=
        (hF _).resolve_left (Finset.mem_filter.mp hx).2
      simp [closedFlavoring, openFl, not_grpZ_of_eq_zero h0]
  simp only [sepConst_congr P Φ (hT _), fProd_congr P Φ α β (S := grpF C 0) (hO _),
    gProd_empty P lor hG, mul_one]
  by_cases hΓ : ∏ t, Wick.vertexFactor P.e 0 0 0 0 0 α β lor 0 0 t = 0
  · simp only [sepConst_eq_zero P Φ _ pOut pIn kIn αOut βIn μ α β lor hΓ, zero_mul, mul_zero,
      Finset.sum_const_zero]
    exact jointEnergyFirstIntegrable_zero_fun'
  have hA := jointEnergyFirstIntegrable_openGrp P Φ hε (openFl Φ) α β lor 0 pOut pIn kIn o3 o4
  have hB := jointEnergyFirstIntegrable_closedGrp P Φ rep hrep hPV₁ hPV₂ hε 1 hZ α β
    (not_blk_of_prod_ne_zero P.e hκ α β lor hΓ) pOut pIn kIn h1 h4
  have h := jointEnergyFirstIntegrable_two_mul
    (A := (fun x => fProd P Φ (openFl Φ) α β (grpF C 0) (kF C 0 pOut pIn kIn x) *
      gProd P lor (grpG C 0) (kG C 0 pOut pIn kIn x)))
    (B := fun x => ∑ f, (Φ.coeff f : ℂ) * fProd P Φ (closedFlavoring Φ (grpZ C 1) f) α β (grpF C 1)
      (kF C 1 pOut pIn kIn x)) hA hB
    (z * sepConst P Φ C (openFl Φ) pOut pIn kIn αOut βIn μ α β lor)
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun f _ => by ring

/-- **One index term, two closed loops**, summed over the flavours of both loops. -/
theorem jointEnergyFirstIntegrable_sepTerm₂ (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (hF : SepLines C)
    (hZ₀ : ∀ x, isZ (grpZ C 0) (C.1.1 x) = isZ (grpZ C 0) x)
    (hZ₁ : ∀ x, isZ (grpZ C 1) (C.1.1 x) = isZ (grpZ C 1) x)
    (hG₀ : ∀ g : PhotonLine C, loopCoeff C (.inr g) 0 = 0)
    (hG₁ : ∀ g : PhotonLine C, loopCoeff C (.inr g) 1 = 0)
    (h1₀ : 1 ≤ Fintype.card (ZLine C (grpZ C 0))) (h4₀ : Fintype.card (ZLine C (grpZ C 0)) ≤ 4)
    (h1₁ : 1 ≤ Fintype.card (ZLine C (grpZ C 1))) (h4₁ : Fintype.card (ZLine C (grpZ C 1)) ≤ 4)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      ∑ x : F × F, (Φ.coeff x.1 : ℂ) * (Φ.coeff x.2 : ℂ) * (z * ampTerm P Φ D C
        (closedFlavoring₂ Φ (grpZ C 0) (grpZ C 1) x.1 x.2) pIn kIn
        (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ α β lor) := by
  classical
  simp only [ampTerm_sep P Φ D hκ hF]
  have hT : ∀ x : F × F, ∀ y ∈ treeF C,
      closedFlavoring₂ Φ (grpZ C 0) (grpZ C 1) x.1 x.2 y.1 = openFl Φ y.1 := fun x y hy => by
    simp [closedFlavoring₂, openFl, not_grpZ_of_eq_zero (Finset.mem_filter.mp hy).2.1,
      not_grpZ_of_eq_zero (Finset.mem_filter.mp hy).2.2]
  have hO₀ : ∀ x : F × F, ∀ y ∈ grpF C 0, closedFlavoring₂ Φ (grpZ C 0) (grpZ C 1) x.1 x.2 y.1 =
      closedFlavoring Φ (grpZ C 0) x.1 y.1 := fun x y hy => by
    have h0 : grpZ C 0 y.1 := (grpZ_iff 0 y).mpr (Finset.mem_filter.mp hy).2
    simp [closedFlavoring₂, closedFlavoring, h0]
  have hO₁ : ∀ x : F × F, ∀ y ∈ grpF C 1, closedFlavoring₂ Φ (grpZ C 0) (grpZ C 1) x.1 x.2 y.1 =
      closedFlavoring Φ (grpZ C 1) x.2 y.1 := fun x y hy => by
    have h1 : grpZ C 1 y.1 := (grpZ_iff 1 y).mpr (Finset.mem_filter.mp hy).2
    have h0 : loopCoeff C (.inl y) 0 = 0 := (hF _).resolve_right (Finset.mem_filter.mp hy).2
    simp [closedFlavoring₂, closedFlavoring, h1, not_grpZ_of_eq_zero h0]
  simp only [sepConst_congr P Φ (hT _), fProd_congr P Φ α β (S := grpF C 0) (hO₀ _),
    fProd_congr P Φ α β (S := grpF C 1) (hO₁ _), gProd_empty P lor hG₀, gProd_empty P lor hG₁,
    mul_one]
  by_cases hΓ : ∏ t, Wick.vertexFactor P.e 0 0 0 0 0 α β lor 0 0 t = 0
  · simp only [sepConst_eq_zero P Φ _ pOut pIn kIn αOut βIn μ α β lor hΓ, zero_mul, mul_zero,
      Finset.sum_const_zero]
    exact jointEnergyFirstIntegrable_zero_fun'
  have hd := not_blk_of_prod_ne_zero P.e hκ α β lor hΓ
  have hA := jointEnergyFirstIntegrable_closedGrp P Φ rep hrep hPV₁ hPV₂ hε 0 hZ₀ α β hd pOut
    pIn kIn h1₀ h4₀
  have hB := jointEnergyFirstIntegrable_closedGrp P Φ rep hrep hPV₁ hPV₂ hε 1 hZ₁ α β hd pOut
    pIn kIn h1₁ h4₁
  have h := jointEnergyFirstIntegrable_two_mul
    (A := fun x => ∑ f, (Φ.coeff f : ℂ) * fProd P Φ (closedFlavoring Φ (grpZ C 0) f) α β (grpF C 0)
      (kF C 0 pOut pIn kIn x))
    (B := fun x => ∑ f, (Φ.coeff f : ℂ) * fProd P Φ (closedFlavoring Φ (grpZ C 1) f) α β (grpF C 1)
      (kF C 1 pOut pIn kIn x)) hA hB
    (z * sepConst P Φ C (openFl Φ) pOut pIn kIn αOut βIn μ α β lor)
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun f' _ => by ring

/-! ### The contraction level -/

/-- **(X₀) for a separated two-loop contraction with a closed loop along `ℓ₀`.** -/
theorem jointEnergyFirstIntegrable_sepClosed₀ (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (C : Contraction 1 1 κ) (hL : loopCount C = 2)
    (hF : SepLines C) (hC : ClosedShape C (grpZ C 0))
    (hG : ∀ g : PhotonLine C, loopCoeff C (.inr g) 0 = 0)
    (h1 : 1 ≤ Fintype.card (ZLine C (grpZ C 0))) (h4 : Fintype.card (ZLine C (grpZ C 0)) ≤ 4)
    (o3 : (grpF C 1).card ≤ 3) (o4 : 4 < (grpF C 1).card + 4 * (grpG C 1).card)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) := by
  unfold integrand
  rw [hL]
  simp only [regulatedAmplitude_eq_closed Φ P D hC, contractionAmplitude_zero_eq]
  have h := jointEnergyFirstIntegrable_sum' Finset.univ fun α _ =>
    jointEnergyFirstIntegrable_sum' Finset.univ fun β _ =>
      jointEnergyFirstIntegrable_sum' Finset.univ fun lor _ =>
        jointEnergyFirstIntegrable_sepTerm₀ P Φ D rep hrep hPV₁ hPV₂ hε hκ hF hC.inv hG h1 h4 o3
          o4 pOut pIn kIn αOut βIn μ α β lor (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [sum_comm_four, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  ring

/-- **(X₀) for a separated two-loop contraction with a closed loop along `ℓ₁`.** -/
theorem jointEnergyFirstIntegrable_sepClosed₁ (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (C : Contraction 1 1 κ) (hL : loopCount C = 2)
    (hF : SepLines C) (hC : ClosedShape C (grpZ C 1))
    (hG : ∀ g : PhotonLine C, loopCoeff C (.inr g) 1 = 0)
    (h1 : 1 ≤ Fintype.card (ZLine C (grpZ C 1))) (h4 : Fintype.card (ZLine C (grpZ C 1)) ≤ 4)
    (o3 : (grpF C 0).card ≤ 3) (o4 : 4 < (grpF C 0).card + 4 * (grpG C 0).card)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) := by
  unfold integrand
  rw [hL]
  simp only [regulatedAmplitude_eq_closed Φ P D hC, contractionAmplitude_zero_eq]
  have h := jointEnergyFirstIntegrable_sum' Finset.univ fun α _ =>
    jointEnergyFirstIntegrable_sum' Finset.univ fun β _ =>
      jointEnergyFirstIntegrable_sum' Finset.univ fun lor _ =>
        jointEnergyFirstIntegrable_sepTerm₁ P Φ D rep hrep hPV₁ hPV₂ hε hκ hF hC.inv hG h1 h4 o3
          o4 pOut pIn kIn αOut βIn μ α β lor (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [sum_comm_four, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  ring

/-- **(X₀) for a separated two-loop contraction with two closed loops.** -/
theorem jointEnergyFirstIntegrable_sepClosed₂ (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (C : Contraction 1 1 κ) (hL : loopCount C = 2)
    (hF : SepLines C) (hC : ClosedShape₂ C (grpZ C 0) (grpZ C 1))
    (hG₀ : ∀ g : PhotonLine C, loopCoeff C (.inr g) 0 = 0)
    (hG₁ : ∀ g : PhotonLine C, loopCoeff C (.inr g) 1 = 0)
    (h1₀ : 1 ≤ Fintype.card (ZLine C (grpZ C 0))) (h4₀ : Fintype.card (ZLine C (grpZ C 0)) ≤ 4)
    (h1₁ : 1 ≤ Fintype.card (ZLine C (grpZ C 1))) (h4₁ : Fintype.card (ZLine C (grpZ C 1)) ≤ 4)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) := by
  unfold integrand
  rw [hL]
  simp only [regulatedAmplitude_eq_closed₂ Φ P D hC, contractionAmplitude_zero_eq]
  have h := jointEnergyFirstIntegrable_sum' Finset.univ fun α _ =>
    jointEnergyFirstIntegrable_sum' Finset.univ fun β _ =>
      jointEnergyFirstIntegrable_sum' Finset.univ fun lor _ =>
        jointEnergyFirstIntegrable_sepTerm₂ P Φ D rep hrep hPV₁ hPV₂ hε hκ hF hC.inv₁ hC.inv₂
          hG₀ hG₁ h1₀ h4₀ h1₁ h4₁ pOut pIn kIn αOut βIn μ α β lor
          (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [sum_comm_four, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f₂ _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  ring

end QED.GradedProof.X0

end
