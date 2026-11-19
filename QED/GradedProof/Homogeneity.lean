/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelectedPart
import Mathlib.Tactic.Ring

/-!
# Homogeneity and locality of the graded order part

Helper proofs of the Phase 5 Stage 2 theorem goals (G-hom) and (G-loc) (decision D-57):

* `QED.GradedProof.selectedPart_eq_pow_mul'`: (G₆) at charge `e` is `e^K` times (G₆) at `e = 1`.
* `QED.GradedProof.selectedPart_congr'`: (G₆) at order `K` reads only the levels `k` with
  `2 k + 2 ≤ K`.

Both are termwise: every graded vertex sequence `(κ, g)` in the sum has `gradedOrder κ g = K`.
For (G-hom), the factor of a vertex of level `k` (the placeholder level `0` for a `gauge` vertex)
is `e ^ (order + 2 k)` times its factor at `e = 1`, and these exponents add up to the graded order.
For (G-loc), a counterterm vertex of level `k` has `order + 2 k ≤ K` with `order ≥ 2`.
-/

@[expose] public section

open Complex MeasureTheory Filter
open QED.WickModel (Params Contraction Line lineMomentum₂ loopCount fermionSign psiMomentum₂
  photonMomentum₂)
open QED.Graded

namespace QED.GradedProof

/-! ### Counting over the counterterm vertices -/

/-- A sum over the counterterm vertices is the sum over all vertices of the function extended by
zero on the `gauge` vertices. -/
theorem sum_ctVertex_eq {N : ℕ} {κ : Fin N → Wick.VertexKind} (f : CtVertex κ → ℕ) :
    ∑ t, (if h : κ t = .gauge then 0 else f ⟨t, h⟩) = ∑ t : CtVertex κ, f t := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun t => κ t = .gauge)]
  have h0 : ∑ t : {t // κ t = .gauge}, (if h : κ t.1 = .gauge then 0 else f ⟨t.1, h⟩) = 0 :=
    Finset.sum_eq_zero fun t _ => by simp [t.2]
  rw [h0, zero_add]
  exact Finset.sum_congr rfl fun t _ => by simp [t.2]

/-- The level of vertex `t` read by (G₃): the grading on counterterm vertices, `0` on `gauge`
vertices. -/
def level {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Grading κ) (t : Fin N) : ℕ :=
  if h : κ t = .gauge then 0 else g ⟨t, h⟩

/-- The graded order is the sum over the vertices of the order plus twice the level. -/
theorem sum_order_add_level {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Grading κ) :
    ∑ t, ((κ t).order + 2 * level g t) = gradedOrder κ g := by
  rw [Finset.sum_add_distrib, gradedOrder, ← sum_ctVertex_eq]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold level
  split <;> simp

/-- A counterterm vertex has order at least `2`. -/
theorem two_le_order_of_ne_gauge {k : Wick.VertexKind} (h : k ≠ .gauge) : 2 ≤ k.order := by
  cases k <;> simp_all [Wick.VertexKind.order]

/-- In a graded vertex sequence of order `K`, a counterterm vertex of level `k` has
`2 k + 2 ≤ K`. -/
theorem two_mul_add_two_le {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Grading κ)
    (t : CtVertex κ) : 2 * g t + 2 ≤ gradedOrder κ g := by
  have h₁ : (κ t.1).order ≤ ∑ s, (κ s).order :=
    Finset.single_le_sum (f := fun s => (κ s).order) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t.1)
  have h₂ : 2 * g t ≤ ∑ s : CtVertex κ, 2 * g s :=
    Finset.single_le_sum (f := fun s => 2 * g s) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t)
  have h₃ := two_le_order_of_ne_gauge t.2
  unfold gradedOrder
  omega

/-! ### Homogeneity (G-hom) -/

/-- The factor (V₁₉) of a vertex of level `lv` with coefficients `e^{2(lv+1)} d` is
`e ^ (order + 2 lv)` times its factor at `e = 1`; a `gauge` vertex must have level `0`. -/
theorem vertexFactor_graded_scale (e a b c d m : ℝ) (lv : ℕ) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) (hlv : κ t = .gauge → lv = 0) :
    Wick.vertexFactor e (e ^ (2 * (lv + 1)) * a) (e ^ (2 * (lv + 1)) * b)
        (e ^ (2 * (lv + 1)) * c) (e ^ (2 * (lv + 1)) * d) m α β lor kψ kA t =
      (e : ℂ) ^ ((κ t).order + 2 * lv) *
        Wick.vertexFactor 1 ((1 : ℝ) ^ (2 * (lv + 1)) * a) ((1 : ℝ) ^ (2 * (lv + 1)) * b)
          ((1 : ℝ) ^ (2 * (lv + 1)) * c) ((1 : ℝ) ^ (2 * (lv + 1)) * d) m α β lor kψ kA t := by
  unfold Wick.vertexFactor
  split <;> rename_i h
  · obtain rfl := hlv h
    simp only [h, Wick.VertexKind.order]
    push_cast
    ring
  all_goals
    simp only [h, Wick.VertexKind.order, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      one_pow, one_mul]
    push_cast
    ring

/-- (G₃) at charge `e` is `e` to the graded order times (G₃) at `e = 1`. -/
theorem contractionAmplitude_scale (P : Params) {F : Type} (Φ : Lepton.Flavors F)
    (D : Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (φ : Flavoring F κ) (g : Grading κ) (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude P Φ D C φ g pIn kIn k αOut βIn μ = (P.e : ℂ) ^ gradedOrder κ g *
      contractionAmplitude { P with e := 1 } Φ D C φ g pIn kIn k αOut βIn μ := by
  unfold contractionAmplitude
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun lor _ => ?_
  have hv : ∀ t, (κ t = .gauge → level g t = 0) := fun t h => by simp [level, h]
  have hprod := Finset.prod_congr (s₁ := Finset.univ) rfl fun t (_ : t ∈ Finset.univ) =>
    vertexFactor_graded_scale P.e (D.d₁ (if h : κ t = .photonCt then Φ.openLine else φ ⟨t, h⟩)
      (level g t)) (D.d₂ (if h : κ t = .photonCt then Φ.openLine else φ ⟨t, h⟩) (level g t))
      (D.dm (if h : κ t = .photonCt then Φ.openLine else φ ⟨t, h⟩) (level g t))
      (D.d₃ (level g t))
      (Φ.mass (if h : κ t = .photonCt then Φ.openLine else φ ⟨t, h⟩)) (level g t) α β lor
      (psiMomentum₂ C pIn k) (photonMomentum₂ C kIn k) t (hv t)
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_order_add_level] at hprod
  simp only [level] at hprod
  simp only
  rw [hprod]
  ring

/-- (G₄) at charge `e` is `e` to the graded order times (G₄) at `e = 1`. -/
theorem regulatedAmplitude_scale (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (g : Grading κ) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D C g pIn kIn k αOut βIn μ = (P.e : ℂ) ^ gradedOrder κ g *
      regulatedAmplitude { P with e := 1 } Φ D C g pIn kIn k αOut βIn μ := by
  unfold regulatedAmplitude
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun φ _ => ?_
  rw [contractionAmplitude_scale P Φ D C φ g]
  ring

/-- (G₅) at charge `e` is `e` to the graded order times (G₅) at `e = 1`. -/
theorem contractionValue_scale (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (g : Grading κ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue P Φ D C g pOut pIn kIn αOut βIn μ = (P.e : ℂ) ^ gradedOrder κ g *
      contractionValue { P with e := 1 } Φ D C g pOut pIn kIn αOut βIn μ := by
  unfold contractionValue QED.TwoLoop.jointEnergyFirstIntegral
  simp_rw [regulatedAmplitude_scale P Φ D C g]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  ring

/-- (G-hom) **Homogeneity of the graded order part**: (G₆) at charge `e` is `e^K` times (G₆) at
`e = 1`. -/
theorem selectedPart_eq_pow_mul' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (nf nA : ℕ)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Grading κ → Prop)
    (K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    selectedPart P Φ D nf nA Sel K pOut pIn kIn αOut βIn μ =
      (P.e : ℂ) ^ K * selectedPart { P with e := 1 } Φ D nf nA Sel K pOut pIn kIn αOut βIn μ := by
  unfold selectedPart
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun N _ => ?_
  rw [mul_left_comm]; congr 1
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun g hg => ?_
  have hK : gradedOrder κ g = K := (Finset.mem_filter.1 hg).2
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun C _ => ?_
  rw [contractionValue_scale P Φ D C g, hK]
  ring

/-! ### Locality (G-loc) -/

/-- The factor (V₁₉) of a `gauge` vertex reads no counterterm and no mass. -/
theorem vertexFactor_of_gauge (e a b c d m a' b' c' d' m' : ℝ) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) (h : κ t = .gauge) :
    Wick.vertexFactor e a b c d m α β lor kψ kA t =
      Wick.vertexFactor e a' b' c' d' m' α β lor kψ kA t := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> simp_all

/-- (G₃) at a graded vertex sequence of order `K` reads only the levels `k` with
`2 k + 2 ≤ K`. -/
theorem contractionAmplitude_congr (P : Params) {F : Type} (Φ : Lepton.Flavors F)
    (D D' : Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (φ : Flavoring F κ) (g : Grading κ)
    (h : ∀ f k, 2 * k + 2 ≤ gradedOrder κ g →
      D.d₁ f k = D'.d₁ f k ∧ D.d₂ f k = D'.d₂ f k ∧ D.dm f k = D'.dm f k)
    (h₃ : ∀ k, 2 * k + 2 ≤ gradedOrder κ g → D.d₃ k = D'.d₃ k)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude P Φ D C φ g pIn kIn k αOut βIn μ =
      contractionAmplitude P Φ D' C φ g pIn kIn k αOut βIn μ := by
  unfold contractionAmplitude
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  congr 3
  refine Finset.prod_congr rfl fun t _ => ?_
  by_cases hg : κ t = .gauge
  · exact vertexFactor_of_gauge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t hg
  · have hb := two_mul_add_two_le g ⟨t, hg⟩
    simp only [hg, ↓reduceDIte]
    rw [(h _ _ hb).1, (h _ _ hb).2.1, (h _ _ hb).2.2, h₃ _ hb]

/-- (G₅) at a graded vertex sequence of order `K` reads only the levels `k` with
`2 k + 2 ≤ K`. -/
theorem contractionValue_congr (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D' : Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (g : Grading κ)
    (h : ∀ f k, 2 * k + 2 ≤ gradedOrder κ g →
      D.d₁ f k = D'.d₁ f k ∧ D.d₂ f k = D'.d₂ f k ∧ D.dm f k = D'.dm f k)
    (h₃ : ∀ k, 2 * k + 2 ≤ gradedOrder κ g → D.d₃ k = D'.d₃ k)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue P Φ D C g pOut pIn kIn αOut βIn μ =
      contractionValue P Φ D' C g pOut pIn kIn αOut βIn μ := by
  have hr : ∀ k, regulatedAmplitude P Φ D C g pIn kIn k αOut βIn μ =
      regulatedAmplitude P Φ D' C g pIn kIn k αOut βIn μ := fun k =>
    Finset.sum_congr rfl fun φ _ => by
      rw [contractionAmplitude_congr P Φ D D' C φ g h h₃]
  unfold contractionValue
  simp only [hr]

/-- (G-loc) **Locality of the graded order part**: (G₆) at order `K` does not read the levels
`k` with `2 k + 2 > K`. -/
theorem selectedPart_congr' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D' : Counterterms F) (nf nA : ℕ)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Grading κ → Prop)
    (K : ℕ)
    (h : ∀ f k, 2 * k + 2 ≤ K →
      D.d₁ f k = D'.d₁ f k ∧ D.d₂ f k = D'.d₂ f k ∧ D.dm f k = D'.dm f k)
    (h₃ : ∀ k, 2 * k + 2 ≤ K → D.d₃ k = D'.d₃ k)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    selectedPart P Φ D nf nA Sel K pOut pIn kIn αOut βIn μ =
      selectedPart P Φ D' nf nA Sel K pOut pIn kIn αOut βIn μ := by
  unfold selectedPart
  refine Finset.sum_congr rfl fun N _ => congrArg _ ?_
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun g hg => ?_
  have hK : gradedOrder κ g = K := (Finset.mem_filter.1 hg).2
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [contractionValue_congr P Φ D D' C g (hK ▸ h) (hK ▸ h₃)]

end QED.GradedProof

end
