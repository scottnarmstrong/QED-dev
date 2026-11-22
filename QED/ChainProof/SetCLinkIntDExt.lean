/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkIntDWard

/-!
# Set (c), family `D`: the `k_μ k_ν` part by Ward identities at both ends

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58), family `D` of set (c): `QED.ChainProof.SetCLink.repD i s`, two loops, a
`photonCt` vertex `5` on a photon line of a two-loop vertex skeleton, grading `0`.

`jointEnergyFirstIntegrable_ctK_ext`: when both counterterm photon lines end on the end
vertices of the open line, both factors `k` contract there and the one-sided forms
`(k₀ - k₁)̸ A(k₁)` and `A(k₁) (k₁ - k₀)̸` cancel a fermion denominator at each end; the nine
resulting terms pass the test `ExtCrit`.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.GradedProof.X0 QED.Graded QED.WickModel QED.ChainProof.SetALink
open QED.ChainProof.Enum (fv pc)
open QED.TwoLoop.Enumeration (lineData)
open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero electronNumerator electronPropagator_apply
  photonPropagator_eq_mul)

variable {F : Type}

/-! ### The `k_μ k_ν` part with one-sided Ward identities at both ends -/

/-- **Resummation at the outgoing end**: the spinor index `β s` and two photon fields. -/
theorem sum_resum_endβ {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (s : V) {p q : W} (hpq : p ≠ q)
    (Ψ : (V → Fin 4) → (V → Fin 4) → (W → Fin 4) → Fin 4 → Fin 4 → Fin 4 → ℂ)
    (hβ : ∀ α β lor b, Ψ α (Function.update β s b) lor = Ψ α β lor)
    (hp : ∀ α β lor x, Ψ α β (Function.update lor p x) = Ψ α β lor)
    (hq : ∀ α β lor x, Ψ α β (Function.update lor q x) = Ψ α β lor) :
    ∑ α, ∑ β, ∑ lor, Ψ α β lor (β s) (lor p) (lor q) =
      ∑ α, ∑ β, ∑ lor, (1 / 64 : ℂ) * ∑ b, ∑ x, ∑ y, Ψ α β lor b x y := by
  refine Finset.sum_congr rfl fun α _ => ?_
  have h1 : ∀ β, ∑ lor, Ψ α β lor (β s) (lor p) (lor q) =
      ∑ lor, (1 / 16 : ℂ) * ∑ x, ∑ y, Ψ α β lor (β s) x y := fun β =>
    sum_resum_pair hpq (fun lor x y => Ψ α β lor (β s) x y)
      (fun lor x => by simp only [hp]) (fun lor x => by simp only [hq])
  simp only [h1]
  rw [sum_resum_one s (fun β b => ∑ lor, (1 / 16 : ℂ) * ∑ x, ∑ y, Ψ α β lor b x y)
    fun β b => by simp only [hβ]]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lor _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **Resummation at the incoming end**: the spinor index `α t` and two photon fields. -/
theorem sum_resum_endα {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (t : V) {p q : W} (hpq : p ≠ q)
    (Ψ : (V → Fin 4) → (V → Fin 4) → (W → Fin 4) → Fin 4 → Fin 4 → Fin 4 → ℂ)
    (hα : ∀ α β lor a, Ψ (Function.update α t a) β lor = Ψ α β lor)
    (hp : ∀ α β lor x, Ψ α β (Function.update lor p x) = Ψ α β lor)
    (hq : ∀ α β lor x, Ψ α β (Function.update lor q x) = Ψ α β lor) :
    ∑ α, ∑ β, ∑ lor, Ψ α β lor (α t) (lor p) (lor q) =
      ∑ α, ∑ β, ∑ lor, (1 / 64 : ℂ) * ∑ a, ∑ x, ∑ y, Ψ α β lor a x y := by
  have h1 : ∀ α β, ∑ lor, Ψ α β lor (α t) (lor p) (lor q) =
      ∑ lor, (1 / 16 : ℂ) * ∑ x, ∑ y, Ψ α β lor (α t) x y := fun α β =>
    sum_resum_pair hpq (fun lor x y => Ψ α β lor (α t) x y)
      (fun lor x => by simp only [hp]) (fun lor x => by simp only [hq])
  simp only [h1]
  rw [sum_resum_one t (fun α a => ∑ β, ∑ lor, (1 / 16 : ℂ) * ∑ x, ∑ y, Ψ α β lor a x y)
    fun α a => by simp only [hα]]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lor _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- The index-carrying factor at the outgoing end. -/
noncomputable def extL (M : ℝ) (X Y : Fin 4) (p q : Fin 4 → ℝ) (b x y : Fin 4) : ℂ :=
  Dirac.gamma x X b * (((Minkowski.metric x y : ℝ) : ℂ) * (q y : ℂ)) * electronNumerator M p b Y

/-- The index-carrying factor at the incoming end. -/
noncomputable def extR (M : ℝ) (X Y : Fin 4) (p q : Fin 4 → ℝ) (a x y : Fin 4) : ℂ :=
  electronNumerator M p X a * (Dirac.gamma x a Y * (((Minkowski.metric x y : ℝ) : ℂ) *
    (q y : ℂ)))

theorem sum_gamma_metric' (q : Fin 4 → ℝ) (a b : Fin 4) :
    ∑ x, ∑ y, Dirac.gamma x a b * (((Minkowski.metric x y : ℝ) : ℂ) * (q y : ℂ)) =
      Dirac.slash q a b := by
  rw [← QED.GradedProof.X0Deg6.sum_gamma_metric q a b]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem sum_extL (M ε σ : ℝ) (p₀ p q : Fin 4 → ℝ) (hq : q = σ • (p₀ - p)) (X Y : Fin 4) :
    ∑ b, ∑ x, ∑ y, extL M X Y p q b x y =
      σ * ((2 * (M : ℂ)) * electronNumerator M p X Y -
        (propDenom M ε p + (ε : ℂ) * I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) X Y -
          (electronNumerator M p₀ * electronNumerator M p) X Y) := by
  have h1 : ∑ b, ∑ x, ∑ y, extL M X Y p q b x y =
      (Dirac.slash q * electronNumerator M p) X Y := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sum_gamma_metric', Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    rfl
  rw [h1, hq, Dirac.slash_smul, Matrix.smul_mul,
    QED.GradedProof.X0Deg6.slash_sub_mul_electronNumerator M ε]
  simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

theorem sum_extR (M ε τ : ℝ) (p₀ p q : Fin 4 → ℝ) (hq : q = τ • (p - p₀)) (X Y : Fin 4) :
    ∑ a, ∑ x, ∑ y, extR M X Y p q a x y =
      τ * ((electronNumerator M p * electronNumerator M p₀) X Y -
        (2 * (M : ℂ)) * electronNumerator M p X Y +
          (propDenom M ε p + (ε : ℂ) * I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) X Y) := by
  have h1 : ∑ a, ∑ x, ∑ y, extR M X Y p q a x y =
      (electronNumerator M p * Dirac.slash q) X Y := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← sum_gamma_metric', Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    rfl
  rw [h1, hq, Dirac.slash_smul, Matrix.mul_smul,
    QED.GradedProof.X0Deg6.electronNumerator_mul_slash_sub M ε]
  simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

section Ext

variable (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) {C : Contraction 1 1 kD}
  (αOut βIn μ : Fin 1 → Fin 4) (f0 f3 : FermionLine C) (gW gK : PhotonLine C)

/-- The four lines of the two one-sided Ward identities. -/
def extLines : Finset (Line C) := {.inl f0, .inl f3, .inr gW, .inr gK}

/-- The constant prefactor of a term with Ward identities at both ends. -/
noncomputable def extZ (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4) :
    ℂ :=
  extI C αOut βIn μ α β lor * ((I / 2) * (δ₃ : ℂ)) * (I * (P.e : ℂ)) ^ 2 *
    gVx {f3.tail.1, f0.1.1, 5} P.e α β lor * ((1 / I) ^ 4 * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2)

/-- The index-free part of a term with Ward identities at both ends. -/
noncomputable def extKc (k : Line C → Fin 4 → ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) : ℂ :=
  extZ P δ₃ αOut βIn μ f0 f3 α β lor *
    rest (extLines f0 f3 gW gK) P.ε (dNum P Φ α β lor) (dMs P Φ) k

/-- The denominators of the four lines. -/
noncomputable def extC0 (k : Line C → Fin 4 → ℝ) : ℂ :=
  (propDenom (Φ.mass Φ.openLine) P.ε (k (.inl f0)))⁻¹ *
    (propDenom (Φ.mass Φ.openLine) P.ε (k (.inl f3)))⁻¹ *
      dProd P.ε [P.mγ, P.Λ] (k (.inr gW)) * dProd P.ε [P.mγ, P.Λ] (k (.inr gK))

end Ext

theorem ext_decomp (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) {C : Contraction 1 1 kD}
    (αOut βIn μ : Fin 1 → Fin 4) (f0 f3 : FermionLine C) (gW gK : PhotonLine C) (sW : Fin 2)
    (hv : f0.1 ≠ f3.tail) (hf : f0 ≠ f3) (hgg : gW ≠ gK)
    (hW : (gW.1 = slD f0.1 ∧ gW.head = pc kD 5 sW) ∨ (gW.1 = pc kD 5 sW ∧ gW.head = slD f0.1))
    (hK : (gK.1 = slD f3.tail ∧ gK.head = pc kD 5 sW.rev) ∨
      (gK.1 = pc kD 5 sW.rev ∧ gK.head = slD f3.tail))
    (q : Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) :
    extI C αOut βIn μ α β lor * (ctKD δ₃ lor q *
        (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k)) =
      extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK k α β lor * extC0 P Φ f0 f3 gW gK k *
        extL (Φ.mass Φ.openLine) (α f0.1) (α f0.tail) (k (.inl f0)) q (β f0.1)
          (lor (slD f0.1)) (lor (pc kD 5 sW)) *
        extR (Φ.mass Φ.openLine) (β f3.1) (β f3.tail) (k (.inl f3)) q (α f3.tail)
          (lor (slD f3.tail)) (lor (pc kD 5 sW.rev)) := by
  have hne : (Sum.inl f0 : Line C) ≠ Sum.inl f3 := fun h => hf (Sum.inl_injective h)
  have hv' : f3.tail.1 ∉ insert f0.1.1 ({5} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hv (Subtype.ext h).symm, ne_five _⟩
  rw [ctKD_eq δ₃ lor q sW, gV_eq_gVx, gVx_split {5} _ _ _ _ f0.1 (by simpa using ne_five f0.1),
    gVx_split _ _ _ _ _ f3.tail hv',
    lineProd_four P.ε hne Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr
      (fun h => hgg (Sum.inr_injective h)), dNum_inl, dNum_inl, dNum_inr P Φ α β lor gW,
    dNum_inr P Φ α β lor gK]
  have hm : Minkowski.metric (lor gW.1) (lor gW.head) =
      Minkowski.metric (lor (slD f0.1)) (lor (pc kD 5 sW)) := by
    rcases hW with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Minkowski.metric_symm]
  have hm' : Minkowski.metric (lor gK.1) (lor gK.head) =
      Minkowski.metric (lor (slD f3.tail)) (lor (pc kD 5 sW.rev)) := by
    rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Minkowski.metric_symm]
  rw [hm, hm']
  simp only [extKc, extZ, extC0, extL, extR, extLines, dMs, dProd_single]
  ring

section ExtInv

variable (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) {C : Contraction 1 1 kD}
  (αOut βIn μ : Fin 1 → Fin 4) (f0 f3 : FermionLine C) (gW gK : PhotonLine C)
  (k : Line C → Fin 4 → ℝ) (α β : Wick.FermionVertex kD → Fin 4)
  (lor : Wick.PhotonSlot kD → Fin 4)

theorem extKc_update_α (hxα : ∀ i, C.1.1 (.inl i) ≠ .inr f3.tail) (a : Fin 4) :
    extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK k (Function.update α f3.tail a) β lor =
      extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK k α β lor := by
  simp only [extKc, extZ, extI_update_α C αOut βIn μ α β lor f3.tail hxα,
    gVx_update_α {f3.tail.1, f0.1.1, 5} P.e α β lor f3.tail (by simp) a,
    rest_update_α P Φ (extLines f0 f3 gW gK) α β lor k f3.tail (fun f hf => by
      rw [QED.GradedProof.X0Deg6.eq_of_tail_eq hf]
      simp [extLines]) a]

theorem extKc_update_β (b : Fin 4) :
    extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK k α (Function.update β f0.1 b) lor =
      extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK k α β lor := by
  have hw : ∀ i, C.1.1 (.inr f0.1) ≠ .inl i := fun i h => by
    have := f0.2
    rw [h] at this
    simp at this
  simp only [extKc, extZ, extI_update_β C αOut βIn μ α β lor f0.1 hw,
    gVx_update_β {f3.tail.1, f0.1.1, 5} P.e α β lor f0.1 (by simp) b,
    rest_update_β P Φ (extLines f0 f3 gW gK) α β lor k f0.1 (fun f hf => by
      rw [show f = f0 from Subtype.ext hf]
      simp [extLines]) b]

theorem extKc_update_lor (r : Wick.PhotonSlot kD)
    (hr : r.1 ∈ ({f3.tail.1, f0.1.1, 5} : Finset (Fin 6)))
    (hxr : ∀ j, C.1.2 (.inl j) ≠ .inr r)
    (hgr : ∀ g : PhotonLine C, (g.1 = r ∨ g.head = r) → g = gW ∨ g = gK) (x : Fin 4) :
    extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK k α β (Function.update lor r x) =
      extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK k α β lor := by
  simp only [extKc, extZ, extI_update_lor C αOut βIn μ α β lor r hxr,
    gVx_update_lor {f3.tail.1, f0.1.1, 5} (by simp) P.e α β lor r hr x,
    rest_update_lor P Φ (extLines f0 f3 gW gK) α β lor k r (fun g hg => by
      rcases hgr g hg with h | h <;> rw [h] <;> simp [extLines]) x]

end ExtInv

section ExtVar

variable (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
  (f0 f3 : FermionLine C) (gW gK : PhotonLine C)

/-- The numerator on the outgoing line in the variant `u`. -/
noncomputable def eNL (M : ℝ) (p₀ : Fin 4 → ℝ) (X Y : Fin 4) (u : Fin 3) : (Fin 4 → ℝ) → ℂ :=
  if u = 0 then fun k => 2 * (M : ℂ) * electronNumerator M k X Y -
    (electronNumerator M p₀ * electronNumerator M k) X Y
  else fun _ => (1 : Matrix (Fin 4) (Fin 4) ℂ) X Y

/-- The numerator on the incoming line in the variant `u`. -/
noncomputable def eNR (M : ℝ) (p₀ : Fin 4 → ℝ) (X Y : Fin 4) (u : Fin 3) : (Fin 4 → ℝ) → ℂ :=
  if u = 0 then fun k => (electronNumerator M k * electronNumerator M p₀) X Y -
    2 * (M : ℂ) * electronNumerator M k X Y
  else fun _ => (1 : Matrix (Fin 4) (Fin 4) ℂ) X Y

/-- The coefficient at the outgoing end. -/
noncomputable def eCL (ε : ℝ) (u : Fin 3) : ℂ :=
  if u = 0 then 1 else if u = 1 then -1 else -((ε : ℂ) * I)

/-- The coefficient at the incoming end. -/
noncomputable def eCR (ε : ℝ) (u : Fin 3) : ℂ :=
  if u = 0 then 1 else if u = 1 then 1 else (ε : ℂ) * I

/-- The numerator factors of the variant `(u, u')`. -/
noncomputable def eNum (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4)
    (pOut pIn : Fin 4 → ℝ) (u u' : Fin 3) : Line C → (Fin 4 → ℝ) → ℂ :=
  mod4 (.inl f0) (.inl f3) (.inr gW) (.inr gK)
    (eNL (Φ.mass Φ.openLine) pOut (α f0.1) (α f0.tail) u)
    (eNR (Φ.mass Φ.openLine) pIn (β f3.1) (β f3.tail) u') (fun _ => 1) (fun _ => 1)
    (dNum P Φ α β lor)

/-- The masses of the variant `(u, u')`. -/
def eMs (u u' : Fin 3) : Line C → List ℝ :=
  mod4 (.inl f0) (.inl f3) (.inr gW) (.inr gK)
    (if u = 1 then [] else [Φ.mass Φ.openLine]) (if u' = 1 then [] else [Φ.mass Φ.openLine])
    [P.mγ, P.Λ] [P.mγ, P.Λ] (dMs P Φ)

/-- The numbers of denominators of the variant `(u, u')`. -/
def extN (u u' : Fin 3) : Line C → ℕ :=
  mod4 (.inl f0) (.inl f3) (.inr gW) (.inr gK) (if u = 1 then 0 else 1)
    (if u' = 1 then 0 else 1) 2 2 dN

/-- The numerator degrees of the variant `(u, u')`. -/
def extD (u u' : Fin 3) : Line C → ℕ :=
  mod4 (.inl f0) (.inl f3) (.inr gW) (.inr gK) (if u = 0 then 1 else 0)
    (if u' = 0 then 1 else 0) 0 0 dD

end ExtVar

/-- **The test after one-sided Ward identities at both ends.** -/
def ExtCrit (C : Contraction 1 1 kD) (f0 f3 : FermionLine C) (gW gK : PhotonLine C) : Prop :=
  ∀ u u' : Fin 3, PadCrit (rowOf C) (extN f0 f3 gW gK u u') (extD f0 f3 gW gK u u')

instance (C : Contraction 1 1 kD) (f0 f3 : FermionLine C) (gW gK : PhotonLine C) :
    Decidable (ExtCrit C f0 f3 gW gK) := by
  unfold ExtCrit; infer_instance

theorem length_eMs (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (f0 f3 : FermionLine C) (gW gK : PhotonLine C) (u u' : Fin 3) :
    (fun l => (eMs P Φ f0 f3 gW gK u u' l).length) = extN f0 f3 gW gK u u' := by
  rw [eMs, length_mod4, extN]
  congr 1 <;> split_ifs <;> rfl

theorem affPoly_mul_left (B : Matrix (Fin 4) (Fin 4) ℂ) (M : ℝ) (X Y : Fin 4) :
    AffPoly 1 fun k => (B * electronNumerator M k) X Y := by
  have hc : ∀ c, AffPoly 1 fun k => B X c * electronNumerator M k c Y := fun c => by
    have := (AffPoly.const (B X c)).mul (affPoly_of_affine (electronNumerator_affine M c Y))
    rwa [zero_add] at this
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  exact (((hc 0).add (hc 1)).add (hc 2)).add (hc 3)

theorem affPoly_mul_right (B : Matrix (Fin 4) (Fin 4) ℂ) (M : ℝ) (X Y : Fin 4) :
    AffPoly 1 fun k => (electronNumerator M k * B) X Y := by
  have hc : ∀ c, AffPoly 1 fun k => electronNumerator M k X c * B c Y := fun c => by
    have := (affPoly_of_affine (electronNumerator_affine M X c)).mul (AffPoly.const (B c Y))
    rwa [add_zero] at this
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  exact (((hc 0).add (hc 1)).add (hc 2)).add (hc 3)

theorem affPoly_eNum (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (f0 f3 : FermionLine C) (gW gK : PhotonLine C) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (pOut pIn : Fin 4 → ℝ) (u u' : Fin 3) (l : Line C) :
    AffPoly (extD f0 f3 gW gK u u' l) (eNum P Φ f0 f3 gW gK α β lor pOut pIn u u' l) := by
  have hA : ∀ X Y, AffPoly 1 fun k => 2 * ((Φ.mass Φ.openLine : ℝ) : ℂ) *
      electronNumerator (Φ.mass Φ.openLine) k X Y := fun X Y => by
    have := (AffPoly.const (2 * ((Φ.mass Φ.openLine : ℝ) : ℂ))).mul
      (affPoly_of_affine (electronNumerator_affine (Φ.mass Φ.openLine) X Y))
    rwa [zero_add] at this
  refine affPoly_mod4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ (AffPoly.const 1) (AffPoly.const 1)
    (affPoly_dNum P Φ C α β lor) l
  · unfold eNL
    split_ifs
    · have h := (hA (α f0.1) (α f0.tail)).add
        ((affPoly_mul_left (electronNumerator (Φ.mass Φ.openLine) pOut) (Φ.mass Φ.openLine)
          (α f0.1) (α f0.tail)).mul
          (AffPoly.const (-1)))
      refine (congrArg (AffPoly 1) (funext fun k => ?_)).mp h
      ring
    · exact AffPoly.const _
  · unfold eNR
    split_ifs
    · have h := (affPoly_mul_right (electronNumerator (Φ.mass Φ.openLine) pIn) (Φ.mass Φ.openLine)
        (β f3.1) (β f3.tail)).add
        ((hA (β f3.1) (β f3.tail)).mul (AffPoly.const (-1)))
      refine (congrArg (AffPoly 1) (funext fun k => ?_)).mp h
      ring
    · exact AffPoly.const _

/-- **The resummed term with Ward identities at both ends** as the nine variants. -/
theorem ext_resummed (P : Params) (Φ : Lepton.Flavors F) (hε : P.ε ≠ 0) (δ₃ : ℝ)
    {C : Contraction 1 1 kD} (αOut βIn μ : Fin 1 → Fin 4) (f0 f3 : FermionLine C)
    (gW gK : PhotonLine C) (hf : f0 ≠ f3) (hgg : gW ≠ gK) (σ τ : ℝ) (pOut pIn q : Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (hσ : q = σ • (pOut - k (.inl f0)))
    (hτ : q = τ • (k (.inl f3) - pIn)) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) :
    (1 / 64 : ℂ) * ∑ a, ∑ x', ∑ y', (1 / 64 : ℂ) * ∑ b, ∑ x, ∑ y,
      extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK k α β lor * extC0 P Φ f0 f3 gW gK k *
        extL (Φ.mass Φ.openLine) (α f0.1) (α f0.tail) (k (.inl f0)) q b x y *
        extR (Φ.mass Φ.openLine) (β f3.1) (β f3.tail) (k (.inl f3)) q a x' y' =
      ∑ u : Fin 3, ∑ u' : Fin 3, (1 / 4096 : ℂ) * extZ P δ₃ αOut βIn μ f0 f3 α β lor *
        (σ : ℂ) * (τ : ℂ) * eCL P.ε u * eCR P.ε u' *
          lineProd P.ε (eNum P Φ f0 f3 gW gK α β lor pOut pIn u u') (eMs P Φ f0 f3 gW gK u u')
            k := by
  have hne : (Sum.inl f0 : Line C) ≠ Sum.inl f3 := fun h => hf (Sum.inl_injective h)
  have hgg' : (Sum.inr gW : Line C) ≠ Sum.inr gK := fun h => hgg (Sum.inr_injective h)
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  rw [sum_extL _ P.ε σ pOut _ q hσ, sum_extR _ P.ε τ pIn _ q hτ]
  simp only [Fin.sum_univ_three, eNum, eMs, eCL, eCR, eNL, eNR,
    lineProd_mod4 P.ε hne Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr hgg']
  simp only [extKc, extC0, extLines, Fin.isValue, Fin.reduceEq, ↓reduceIte, dProd_single,
    dProd_nil]
  have h1 := propDenom_ne_zero (M := Φ.mass Φ.openLine) hε (k (.inl f0))
  have h2 := propDenom_ne_zero (M := Φ.mass Φ.openLine) hε (k (.inl f3))
  generalize rest {Sum.inl f0, Sum.inl f3, Sum.inr gW, Sum.inr gK} P.ε (dNum P Φ α β lor)
    (dMs P Φ) k = R
  generalize extZ P δ₃ αOut βIn μ f0 f3 α β lor = Z
  generalize dProd P.ε [P.mγ, P.Λ] (k (Sum.inr gK)) = DK
  generalize dProd P.ε [P.mγ, P.Λ] (k (Sum.inr gW)) = DW
  generalize electronNumerator (Φ.mass Φ.openLine) (k (Sum.inl f0)) (α f0.1) (α f0.tail) = A0
  generalize electronNumerator (Φ.mass Φ.openLine) (k (Sum.inl f3)) (β f3.1) (β f3.tail) = A3
  generalize (electronNumerator (Φ.mass Φ.openLine) pOut *
    electronNumerator (Φ.mass Φ.openLine) (k (Sum.inl f0))) (α f0.1) (α f0.tail) = B0
  generalize (electronNumerator (Φ.mass Φ.openLine) (k (Sum.inl f3)) *
    electronNumerator (Φ.mass Φ.openLine) pIn) (β f3.1) (β f3.tail) = B3
  generalize (1 : Matrix (Fin 4) (Fin 4) ℂ) (α f0.1) (α f0.tail) = O0
  generalize (1 : Matrix (Fin 4) (Fin 4) ℂ) (β f3.1) (β f3.tail) = O3
  generalize propDenom (Φ.mass Φ.openLine) P.ε (k (Sum.inl f0)) = D0 at h1 ⊢
  generalize propDenom (Φ.mass Φ.openLine) P.ε (k (Sum.inl f3)) = D3 at h2 ⊢
  have e0 := mul_inv_cancel₀ h1
  have e3 := mul_inv_cancel₀ h2
  set M : ℂ := ((Φ.mass Φ.openLine : ℝ) : ℂ)
  set iε : ℂ := (P.ε : ℂ) * I
  linear_combination (1 / 4096 * Z * σ * τ * R * DW * DK) *
    ((-O0 * ((B3 - 2 * M * A3) * D3⁻¹ + D3 * D3⁻¹ * O3 + iε * O3 * D3⁻¹) +
      O0 * O3 * (D3 * D3⁻¹ - 1)) * e0 +
      ((2 * M * A0 - B0) * D0⁻¹ - D0 * D0⁻¹ * O0 - iε * O0 * D0⁻¹) * O3 * e3)

/-- The slots of the two counterterm photon lines at the open ends. -/
def ExtSlots (C : Contraction 1 1 kD) (gW gK : PhotonLine C) (r : Wick.PhotonSlot kD) : Prop :=
  (∀ j, C.1.2 (.inl j) ≠ .inr r) ∧ ∀ g : PhotonLine C, (g.1 = r ∨ g.head = r) → g = gW ∨ g = gK

instance (C : Contraction 1 1 kD) (gW gK : PhotonLine C) (r : Wick.PhotonSlot kD) :
    Decidable (ExtSlots C gW gK r) := by
  unfold ExtSlots; infer_instance

/-- **(T₉′) of the `k_μ k_ν` part, by one-sided Ward identities at both ends** of the open line:
the photon line `gW` from the field `sW` to the outgoing vertex `f0.1`, and `gK` from the other
field to the incoming vertex `f3.tail`. -/
theorem jointEnergyFirstIntegrable_ctK_ext (P : Params) (Φ : Lepton.Flavors F) (hε : 0 < P.ε)
    (δ₃ : ℝ) (C : Contraction 1 1 kD) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) (f0 f3 : FermionLine C)
    (gW gK : PhotonLine C) (sW : Fin 2) (hv : f0.1 ≠ f3.tail) (hf : f0 ≠ f3) (hgg : gW ≠ gK)
    (hW : (gW.1 = slD f0.1 ∧ gW.head = pc kD 5 sW) ∨ (gW.1 = pc kD 5 sW ∧ gW.head = slD f0.1))
    (hK : (gK.1 = slD f3.tail ∧ gK.head = pc kD 5 sW.rev) ∨
      (gK.1 = pc kD 5 sW.rev ∧ gK.head = slD f3.tail))
    (hxα : ∀ i, C.1.1 (.inl i) ≠ .inr f3.tail)
    (hS : ExtSlots C gW gK (slD f0.1) ∧ ExtSlots C gW gK (pc kD 5 sW) ∧
      ExtSlots C gW gK (slD f3.tail) ∧ ExtSlots C gW gK (pc kD 5 sW.rev))
    (hσ : pmv C (pc kD 5 0) = ![0, 0, 1, 1] - mv C (.inl f0) ∨
      pmv C (pc kD 5 0) = -(![0, 0, 1, 1] - mv C (.inl f0)))
    (hτ : pmv C (pc kD 5 0) = mv C (.inl f3) - ![0, 0, 1, 0] ∨
      pmv C (pc kD 5 0) = -(mv C (.inl f3) - ![0, 0, 1, 0]))
    (hcrit : ExtCrit C f0 f3 gW gK) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => ∑ α, ∑ β, ∑ lor,
      extI C αOut βIn μ α β lor *
        (ctKD δ₃ lor (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)) *
          (gV P.e α β lor *
            lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (lineMomentum₂ C pOut pIn kIn ℓ))) := by
  set k := lineMomentum₂ C pOut pIn kIn with hk
  set q := fun ℓ => photonMomentum₂ C kIn (k ℓ) (pc kD 5 0) with hq
  obtain ⟨σ, hσ'⟩ := exists_sign pIn kIn _ _ hσ q (fun ℓ => pOut 0 - k ℓ (.inl f0))
    (fun ℓ => photonMomentum₂_eq_pmv C pOut pIn kIn hmom ℓ _)
    (fun ℓ => by
      simp only [hk, lineMomentum₂_eq_mv C pOut pIn kIn hmom, map_sub, hmom]
      congr 1
      simp [mvReal])
  obtain ⟨τ, hτ'⟩ := exists_sign pIn kIn _ _ hτ q (fun ℓ => k ℓ (.inl f3) - pIn 0)
    (fun ℓ => photonMomentum₂_eq_pmv C pOut pIn kIn hmom ℓ _)
    (fun ℓ => by
      simp only [hk, lineMomentum₂_eq_mv C pOut pIn kIn hmom, map_sub]
      congr 1
      simp [mvReal])
  have hT : ∀ r, (r = slD f0.1 ∨ r = pc kD 5 sW ∨ r = slD f3.tail ∨ r = pc kD 5 sW.rev) →
      r.1 ∈ ({f3.tail.1, f0.1.1, 5} : Finset (Fin 6)) := by
    rintro r (rfl | rfl | rfl | rfl) <;> simp [slD, pc]
  have hS' : ∀ r, (r = slD f0.1 ∨ r = pc kD 5 sW ∨ r = slD f3.tail ∨ r = pc kD 5 sW.rev) →
      ExtSlots C gW gK r := by
    rintro r (rfl | rfl | rfl | rfl)
    exacts [hS.1, hS.2.1, hS.2.2.1, hS.2.2.2]
  have hlor : ∀ r, (r = slD f0.1 ∨ r = pc kD 5 sW ∨ r = slD f3.tail ∨ r = pc kD 5 sW.rev) →
      ∀ ℓ α β lor x, extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK (k ℓ) α β (Function.update lor r x) =
        extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK (k ℓ) α β lor := fun r hr ℓ α β lor x =>
    extKc_update_lor P Φ δ₃ αOut βIn μ f0 f3 gW gK (k ℓ) α β lor r (hT r hr) (hS' r hr).1
      (hS' r hr).2 x
  have hv4 : ∀ v : Wick.FermionVertex kD, v ≠ f0.1 → slD v ≠ slD f0.1 := fun v h e =>
    h (Subtype.ext (congrArg Sigma.fst e))
  have h5 : ∀ (v : Wick.FermionVertex kD) (t : Fin 2), slD v ≠ pc kD 5 t := fun v t e =>
    ne_five v (congrArg Sigma.fst e)
  have hrev : pc kD 5 sW.rev ≠ pc kD 5 sW := by fin_cases sW <;> decide
  have h30 : slD f3.tail ≠ slD f0.1 := hv4 _ (Ne.symm hv)
  have hf31 : f3.1 ≠ f0.1 := fun h => hf (Subtype.ext h.symm)
  have hf0t : f0.tail ≠ f3.tail := fun h => hf (QED.GradedProof.X0Deg6.eq_of_tail_eq h)
  have hkey : ∀ ℓ, ∑ α, ∑ β, ∑ lor, extI C αOut βIn μ α β lor * (ctKD δ₃ lor (q ℓ) *
      (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (k ℓ))) =
      ∑ α, ∑ β, ∑ lor, ∑ u : Fin 3, ∑ u' : Fin 3, (1 / 4096 : ℂ) *
        extZ P δ₃ αOut βIn μ f0 f3 α β lor * (σ : ℂ) * (τ : ℂ) * eCL P.ε u * eCR P.ε u' *
          lineProd P.ε (eNum P Φ f0 f3 gW gK α β lor (pOut 0) (pIn 0) u u')
            (eMs P Φ f0 f3 gW gK u u') (k ℓ) := by
    intro ℓ
    simp only [ext_decomp P Φ δ₃ αOut βIn μ f0 f3 gW gK sW hv hf hgg hW hK (q ℓ) (k ℓ)]
    have hB := sum_resum_endβ f0.1 (h5 f0.1 sW) (fun α β lor b x y =>
      extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK (k ℓ) α β lor * extC0 P Φ f0 f3 gW gK (k ℓ) *
        extL (Φ.mass Φ.openLine) (α f0.1) (α f0.tail) (k ℓ (.inl f0)) (q ℓ) b x y *
        extR (Φ.mass Φ.openLine) (β f3.1) (β f3.tail) (k ℓ (.inl f3)) (q ℓ) (α f3.tail)
          (lor (slD f3.tail)) (lor (pc kD 5 sW.rev)))
      (fun α β lor b => by
        funext b' x y
        simp only [extKc_update_β, Function.update_of_ne hf31, Function.update_of_ne hv.symm])
      (fun α β lor x => by
        funext b' x' y
        simp only [hlor _ (Or.inl rfl), Function.update_of_ne h30,
          Function.update_of_ne (h5 f0.1 sW.rev).symm])
      (fun α β lor x => by
        funext b' x' y
        simp only [hlor _ (Or.inr (Or.inl rfl)), Function.update_of_ne (h5 f3.tail sW),
          Function.update_of_ne hrev])
    rw [hB]
    have hA := sum_resum_endα f3.tail (h5 f3.tail sW.rev) (fun α β lor a x' y' =>
      (1 / 64 : ℂ) * ∑ b, ∑ x, ∑ y,
      extKc P Φ δ₃ αOut βIn μ f0 f3 gW gK (k ℓ) α β lor * extC0 P Φ f0 f3 gW gK (k ℓ) *
        extL (Φ.mass Φ.openLine) (α f0.1) (α f0.tail) (k ℓ (.inl f0)) (q ℓ) b x y *
        extR (Φ.mass Φ.openLine) (β f3.1) (β f3.tail) (k ℓ (.inl f3)) (q ℓ) a x' y')
      (fun α β lor a => by
        funext a' x y
        simp only [extKc_update_α P Φ δ₃ αOut βIn μ f0 f3 gW gK _ α β lor hxα,
          Function.update_of_ne hv, Function.update_of_ne hf0t])
      (fun α β lor x => by
        funext a' x' y
        simp only [hlor _ (Or.inr (Or.inr (Or.inl rfl)))])
      (fun α β lor x => by
        funext a' x' y
        simp only [hlor _ (Or.inr (Or.inr (Or.inr rfl)))])
    rw [hA]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun lor _ => ?_
    exact ext_resummed P Φ hε.ne' δ₃ αOut βIn μ f0 f3 gW gK hf hgg σ τ (pOut 0) (pIn 0) (q ℓ)
      (k ℓ) (hσ' ℓ) (hτ' ℓ) α β lor
  refine (congrArg _ (funext hkey)).mpr ?_
  refine jointEnergyFirstIntegrable_sum' _ fun α _ => jointEnergyFirstIntegrable_sum' _ fun β _ =>
    jointEnergyFirstIntegrable_sum' _ fun lor _ => jointEnergyFirstIntegrable_sum' _ fun u _ =>
      jointEnergyFirstIntegrable_sum' _ fun u' _ => ?_
  exact jointEnergyFirstIntegrable_lineProd C pOut pIn kIn hε _ _ _ (extD f0 f3 gW gK u u')
    (affPoly_eNum P Φ f0 f3 gW gK α β lor (pOut 0) (pIn 0) u u')
    (by rw [length_eMs]; exact hcrit u u')

end QED.ChainProof.SetCLink

end
