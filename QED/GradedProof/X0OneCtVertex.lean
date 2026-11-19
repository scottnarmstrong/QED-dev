/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0AffPoly
public import QED.GradedProof.X0Entry

/-!
# (X₀): the vertex factors at one loop

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), for the one-loop
contractions with a counterterm vertex. With one loop momentum `ℓ`, let every line carry
`k_l = c_l ℓ + e_l` (`oneMom`, integer `c_l`). Then the momentum of a fermion field is
`psiCoeff · ℓ + const` and that of a photon slot is `slotCoeff · ℓ + const`, and the vertex factor
(V₁₉) of vertex `t` is an `AffPoly` of degree `vDeg t` in `ℓ`: `0` for `gauge` and `gaugeCt`;
for `fermionCt`, `1` if its fermion momentum depends on `ℓ` and `0` otherwise; for `photonCt`,
`2` if its photon momentum depends on `ℓ` and `0` otherwise (`affPoly_vertexFactor`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.WickModel
open QED.TwoLoop.Bridge (electronNumerator)

/-! ### Affine and quadratic functions of an affine momentum -/

theorem AffPoly.coord (s : ℝ) (b : Fin 4 → ℝ) (ν : Fin 4) :
    AffPoly 1 fun ℓ => (((s • ℓ + b) ν : ℝ) : ℂ) := by
  have h := AffPoly.aff (b ν : ℂ) fun ν' => if ν' = ν then (s : ℂ) else 0
  refine (congrArg (AffPoly 1) (funext fun ℓ => ?_)).mp h
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem AffPoly.dot (s : ℝ) (b : Fin 4 → ℝ) :
    AffPoly 2 fun ℓ => ((Minkowski.dot (s • ℓ + b) (s • ℓ + b) : ℝ) : ℂ) := by
  have h := AffPoly.sum (d := 1 + 1) Finset.univ fun μ _ => AffPoly.sum Finset.univ fun ν _ =>
    ((AffPoly.coord s b μ).mul (AffPoly.coord s b ν)).const_mul
      ((Minkowski.metric μ ν : ℝ) : ℂ)
  refine (congrArg (AffPoly 2) (funext fun ℓ => ?_)).mp h
  simp only [Minkowski.dot]
  push_cast
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- An affine function, scaled and shifted, is affine. -/
theorem affine_mul_add {G : (Fin 4 → ℝ) → ℂ}
    (hG : ∃ u : ℂ, ∃ w : Fin 4 → ℂ, ∀ k, G k = u + ∑ ν, w ν * (k ν : ℂ)) (z y : ℂ) :
    ∃ u : ℂ, ∃ w : Fin 4 → ℂ, ∀ k, z * G k + y = u + ∑ ν, w ν * (k ν : ℂ) := by
  obtain ⟨u, w, hG⟩ := hG
  refine ⟨z * u + y, fun ν => z * w ν, fun k => ?_⟩
  rw [hG k, mul_add, Finset.mul_sum]
  simp only [mul_assoc]
  ring

/-- The `fermionCt` vertex factor is affine in the fermion momentum. -/
theorem affine_fermionCt (δ₂ r : ℝ) (a b : Fin 4) :
    ∃ u : ℂ, ∃ w : Fin 4 → ℂ, ∀ k : Fin 4 → ℝ,
      -I * (((δ₂ : ℂ) • Dirac.slash k + (r : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b) =
        u + ∑ ν, w ν * (k ν : ℂ) := by
  obtain ⟨u, w, h⟩ := affine_mul_add (electronNumerator_affine 0 a b) (I * δ₂)
    (-I * (r * (1 : Matrix (Fin 4) (Fin 4) ℂ) a b))
  refine ⟨u, w, fun k => ?_⟩
  rw [← h k]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, electronNumerator,
    Matrix.sub_apply, ofReal_zero, zero_smul, Matrix.zero_apply, zero_sub]
  ring

/-! ### One-loop momenta -/

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

/-- The one-loop line momenta `k_l = c_l ℓ + e_l`. -/
def oneMom (c : Line C → ℤ) (e : Line C → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) : Line C → Fin 4 → ℝ :=
  fun l => (c l : ℝ) • ℓ + e l

/-- The loop coefficient of the momentum of a fermion field. -/
def psiCoeff (c : Line C → ℤ) (s : Wick.FermionVertex κ) : ℤ :=
  match h : C.1.1 (.inr s) with
  | .inl _ => 0
  | .inr _ => c (.inl ⟨s, by simp [h]⟩)

/-- The loop coefficient of the momentum of a photon slot. -/
def slotCoeff (c : Line C → ℤ) (a : Wick.PhotonSlot κ) : ℤ :=
  ∑ g : PhotonLine C, ((if g.head = a then c (.inr g) else 0) - (if g.1 = a then c (.inr g) else 0))

theorem psiMomentum₂_oneMom (c : Line C → ℤ) (e : Line C → Fin 4 → ℝ)
    (pIn : Fin nf → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) (s : Wick.FermionVertex κ) :
    psiMomentum₂ C pIn (oneMom c e ℓ) s =
      (psiCoeff c s : ℝ) • ℓ + psiMomentum₂ C pIn e s := by
  unfold psiMomentum₂ psiCoeff
  repeat' split
  all_goals simp_all [oneMom]

theorem photonMomentum₂_oneMom (c : Line C → ℤ) (e : Line C → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) (a : Wick.PhotonSlot κ) :
    photonMomentum₂ C kIn (oneMom c e ℓ) a =
      (slotCoeff c a : ℝ) • ℓ + photonMomentum₂ C kIn e a := by
  funext μ
  simp only [photonMomentum₂, oneMom, slotCoeff, Pi.add_apply, Finset.sum_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, apply_ite (fun x : Fin 4 → ℝ => x μ), Pi.zero_apply,
    Int.cast_sum, Int.cast_sub, Int.cast_ite, Int.cast_zero, Finset.sum_mul]
  rw [add_left_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs <;> ring

/-- The degree of the vertex factor of `t` in the loop momentum. -/
def vDeg (c : Line C → ℤ) (t : Fin N) : ℕ :=
  if h : κ t = .fermionCt then (if psiCoeff c ⟨t, by rw [h]; decide⟩ = 0 then 0 else 1)
  else if h' : κ t = .photonCt then
    (if slotCoeff c ⟨t, ⟨0, by rw [h']; decide⟩⟩ = 0 then 0 else 2)
  else 0

/-- **The vertex factor is an `AffPoly` of degree `vDeg`.** -/
theorem affPoly_vertexFactor (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (t : Fin N) :
    AffPoly (vDeg c t) fun ℓ => Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor
      (psiMomentum₂ C pIn (oneMom c ext ℓ)) (photonMomentum₂ C kIn (oneMom c ext ℓ)) t := by
  unfold Wick.vertexFactor
  split
  next h =>
    rw [show vDeg c t = 0 by
      unfold vDeg; split_ifs <;> simp_all]
    exact AffPoly.const' 0 _
  next h =>
    rw [show vDeg c t = 0 by
      unfold vDeg; split_ifs <;> simp_all]
    exact AffPoly.const' 0 _
  next h =>
    simp only [psiMomentum₂_oneMom c ext pIn]
    by_cases h0 : psiCoeff c ⟨t, by rw [h]; decide⟩ = 0
    · rw [show vDeg c t = 0 by simp [vDeg, h, h0]]
      simp only [h0, Int.cast_zero, zero_smul, zero_add]
      exact AffPoly.const' 0 _
    · rw [show vDeg c t = 1 by simp [vDeg, h, h0]]
      exact AffPoly.comp_affine (affine_fermionCt δ₂ (δm * m) _ _) _ _
  next h =>
    simp only [photonMomentum₂_oneMom c ext kIn]
    by_cases h0 : slotCoeff c ⟨t, ⟨0, by rw [h]; decide⟩⟩ = 0
    · rw [show vDeg c t = 2 * 0 by simp [vDeg, h, h0]]
      simp only [h0, Int.cast_zero, zero_smul, zero_add]
      exact AffPoly.const' _ _
    · rw [show vDeg c t = 2 by simp [vDeg, h, h0]]
      set s : ℝ := (slotCoeff c ⟨t, ⟨0, by rw [h]; decide⟩⟩ : ℝ)
      set b := photonMomentum₂ C kIn ext ⟨t, ⟨0, by rw [h]; decide⟩⟩
      set μ' := lor ⟨t, ⟨0, by rw [h]; decide⟩⟩
      set ν' := lor ⟨t, ⟨1, by rw [h]; decide⟩⟩
      have hq := (((AffPoly.dot s b).mul (AffPoly.const ((Minkowski.metric μ' ν' : ℝ) : ℂ))).add
        (((AffPoly.coord s b μ').mul (AffPoly.coord s b ν')).const_mul (-1))).const_mul
        (-(I / 2) * (δ₃ : ℂ))
      refine (congrArg (AffPoly 2) (funext fun ℓ => ?_)).mp hq
      push_cast
      ring

end QED.GradedProof.X0

end
