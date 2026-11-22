/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkIntDRes

/-!
# Set (c), family `D`: the `k_μ k_ν` part by a Ward identity at an internal vertex

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58), family `D` of set (c): `QED.ChainProof.SetCLink.repD i s`, two loops, a
`photonCt` vertex `5` on a photon line of a two-loop vertex skeleton, grading `0`.

`jointEnergyFirstIntegrable_ctK_ward`: one factor `k` of the `k_μ k_ν` part contracts through a
counterterm photon line into an internal vertex of the open line, where the Ward identity
`A(k₁) (k₁ - k₂)̸ A(k₂) = (D(k₁) + iε) A(k₂) - (D(k₂) + iε) A(k₁)` cancels one fermion
denominator; the four resulting terms pass the test `WardCrit`.
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

/-! ### The `k_μ k_ν` part with a Ward identity at an internal vertex -/

section Ward

variable (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) {C : Contraction 1 1 kD}
  (αOut βIn μ : Fin 1 → Fin 4) (fa fb : FermionLine C) (gW gK : PhotonLine C) (sW : Fin 2)

/-- The four lines of the Ward identity. -/
def wardL : Finset (Line C) := {.inl fa, .inl fb, .inr gW, .inr gK}

/-- The index-free part of a term with the Ward vertex `fb.1`, except the line factors of `fa`,
`fb`, `gW`. -/
noncomputable def wardKc (q : Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4) : ℂ :=
  extI C αOut βIn μ α β lor * ((I / 2) * (δ₃ : ℂ) * (q (lor (pc kD 5 sW.rev)) : ℂ)) *
    (I * (P.e : ℂ)) * gVx {fb.1.1, 5} P.e α β lor *
      (dNum P Φ α β lor (.inr gK) (k (.inr gK)) * dProd P.ε (dMs P Φ (.inr gK)) (k (.inr gK))) *
        rest (wardL fa fb gW gK) P.ε (dNum P Φ α β lor) (dMs P Φ) k

/-- The denominators of `fa`, `fb`, `gW`. -/
noncomputable def wardC0 (k : Line C → Fin 4 → ℝ) : ℂ :=
  (1 / I) ^ 3 * (propDenom (Φ.mass Φ.openLine) P.ε (k (.inl fa)))⁻¹ *
    (propDenom (Φ.mass Φ.openLine) P.ε (k (.inl fb)))⁻¹ * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) *
      dProd P.ε (dMs P Φ (.inr gW)) (k (.inr gW))

end Ward

/-- The index-carrying part of a term with a Ward vertex. -/
noncomputable def wardW (M : ℝ) (X Y : Fin 4) (p₁ p₂ q : Fin 4 → ℝ) (a b x y : Fin 4) : ℂ :=
  electronNumerator M p₁ X a * (Dirac.gamma x a b * (((Minkowski.metric x y : ℝ) : ℂ) *
    (q y : ℂ))) * electronNumerator M p₂ b Y

theorem ward_decomp (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) {C : Contraction 1 1 kD}
    (αOut βIn μ : Fin 1 → Fin 4) (fa fb : FermionLine C) (gW gK : PhotonLine C) (sW : Fin 2)
    (hab : fa.tail = fb.1) (hfa : fa.1 ≠ fb.1) (hgg : gW ≠ gK)
    (hW : (gW.1 = slD fb.1 ∧ gW.head = pc kD 5 sW) ∨ (gW.1 = pc kD 5 sW ∧ gW.head = slD fb.1))
    (q : Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) :
    extI C αOut βIn μ α β lor * (ctKD δ₃ lor q *
        (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k)) =
      wardKc P Φ δ₃ αOut βIn μ fa fb gW gK sW q k α β lor * wardC0 P Φ fa fb gW k *
        wardW (Φ.mass Φ.openLine) (β fa.1) (α fb.tail) (k (.inl fa)) (k (.inl fb)) q (α fb.1)
          (β fb.1) (lor (slD fb.1)) (lor (pc kD 5 sW)) := by
  have hne : (Sum.inl fa : Line C) ≠ Sum.inl fb := fun h => hfa (by rw [Sum.inl_injective h])
  rw [ctKD_eq δ₃ lor q sW, gV_eq_gVx, gVx_split {5} _ _ _ _ fb.1 (by simpa using ne_five fb.1),
    lineProd_four P.ε hne Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr
      (fun h => hgg (Sum.inr_injective h)), dNum_inl, dNum_inl, dNum_inr P Φ α β lor gW]
  have hm : Minkowski.metric (lor gW.1) (lor gW.head) =
      Minkowski.metric (lor (slD fb.1)) (lor (pc kD 5 sW)) := by
    rcases hW with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Minkowski.metric_symm]
  rw [hm, hab]
  simp only [wardKc, wardC0, wardW, wardL, dMs, dProd_single]
  ring

section WardVar

variable (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
  (fa fb : FermionLine C) (gW gK : PhotonLine C)

/-- The numerator factors of the variant `w` after the Ward identity at `fb.1`. -/
noncomputable def wNum (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4)
    (sW : Fin 2) (τ : ℝ) (w : Fin 4) : Line C → (Fin 4 → ℝ) → ℂ :=
  mod4 (.inl fa) (.inl fb) (.inr gW) (.inr gK)
    (if w.val < 2 then fun _ => 1 else
      fun k => electronNumerator (Φ.mass Φ.openLine) k (β fa.1) (α fb.tail))
    (if w.val < 2 then fun k => electronNumerator (Φ.mass Φ.openLine) k (β fa.1) (α fb.tail)
      else fun _ => 1)
    (fun _ => 1)
    (fun k => dNum P Φ α β lor (.inr gK) k * ((τ * k (lor (pc kD 5 sW.rev)) : ℝ) : ℂ))
    (dNum P Φ α β lor)

/-- The masses of the variant `w`. -/
def wMs (w : Fin 4) : Line C → List ℝ :=
  mod4 (.inl fa) (.inl fb) (.inr gW) (.inr gK)
    (if w = 0 then [] else [Φ.mass Φ.openLine]) (if w = 2 then [] else [Φ.mass Φ.openLine])
    [P.mγ, P.Λ] [P.mγ, P.Λ] (dMs P Φ)

/-- The numbers of denominators of the variant `w`. -/
def wardN (w : Fin 4) : Line C → ℕ :=
  mod4 (.inl fa) (.inl fb) (.inr gW) (.inr gK) (if w = 0 then 0 else 1) (if w = 2 then 0 else 1)
    2 2 dN

/-- The numerator degrees of the variant `w`. -/
def wardD (w : Fin 4) : Line C → ℕ :=
  mod4 (.inl fa) (.inl fb) (.inr gW) (.inr gK) (if w.val < 2 then 0 else 1)
    (if w.val < 2 then 1 else 0) 0 1 dD

end WardVar

/-- **The test after a Ward identity at an internal vertex.** -/
def WardCrit (C : Contraction 1 1 kD) (fa fb : FermionLine C) (gW gK : PhotonLine C) : Prop :=
  ∀ w : Fin 4, PadCrit (rowOf C) (wardN fa fb gW gK w) (wardD fa fb gW gK w)

instance (C : Contraction 1 1 kD) (fa fb : FermionLine C) (gW gK : PhotonLine C) :
    Decidable (WardCrit C fa fb gW gK) := by
  unfold WardCrit; infer_instance

/-- The coefficient of the variant `w`. -/
noncomputable def wCoef (ε : ℝ) (w : Fin 4) : ℂ :=
  if w = 0 then 1 else if w = 1 then (ε : ℂ) * I else if w = 2 then -1 else -((ε : ℂ) * I)

theorem length_wMs (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (fa fb : FermionLine C) (gW gK : PhotonLine C) (w : Fin 4) :
    (fun l => (wMs P Φ fa fb gW gK w l).length) = wardN fa fb gW gK w := by
  rw [wMs, length_mod4, wardN]
  congr 1 <;> split_ifs <;> rfl

theorem affPoly_wNum (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (fa fb : FermionLine C) (gW gK : PhotonLine C) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (sW : Fin 2) (τ : ℝ) (w : Fin 4) (l : Line C) :
    AffPoly (wardD fa fb gW gK w l) (wNum P Φ fa fb gW gK α β lor sW τ w l) := by
  have hA : AffPoly 1 fun k => electronNumerator (Φ.mass Φ.openLine) k (β fa.1) (α fb.tail) :=
    affPoly_of_affine (electronNumerator_affine _ _ _)
  refine affPoly_mod4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ (AffPoly.const 1) ?_
    (affPoly_dNum P Φ C α β lor) l
  · split_ifs
    · exact AffPoly.const 1
    · exact hA
  · split_ifs
    · exact hA
    · exact AffPoly.const 1
  · exact (affPoly_dNum P Φ C α β lor (.inr gK)).mul (affPoly_coord τ (lor (pc kD 5 sW.rev)))

/-- **The resummed term with a Ward vertex** as the four variants. -/
theorem ward_resummed (P : Params) (Φ : Lepton.Flavors F) (hε : P.ε ≠ 0) (δ₃ : ℝ)
    {C : Contraction 1 1 kD} (αOut βIn μ : Fin 1 → Fin 4) (fa fb : FermionLine C)
    (gW gK : PhotonLine C) (sW : Fin 2) (hfa : fa.1 ≠ fb.1) (hgg : gW ≠ gK) (σ τ : ℝ)
    (q : Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (hσ : q = σ • (k (.inl fa) - k (.inl fb)))
    (hτ : q = τ • k (.inr gK)) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) :
    (1 / 256 : ℂ) * ∑ a, ∑ b, ∑ x, ∑ y, wardKc P Φ δ₃ αOut βIn μ fa fb gW gK sW q k α β lor *
        wardC0 P Φ fa fb gW k * wardW (Φ.mass Φ.openLine) (β fa.1) (α fb.tail) (k (.inl fa))
          (k (.inl fb)) q a b x y =
      ∑ w : Fin 4, (1 / 256 : ℂ) * extI C αOut βIn μ α β lor * ((I / 2) * (δ₃ : ℂ)) *
        (I * (P.e : ℂ)) * gVx {fb.1.1, 5} P.e α β lor * (1 / I) ^ 3 *
          ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * (σ : ℂ) * wCoef P.ε w *
            lineProd P.ε (wNum P Φ fa fb gW gK α β lor sW τ w) (wMs P Φ fa fb gW gK w) k := by
  have hne : (Sum.inl fa : Line C) ≠ Sum.inl fb := fun h => hfa (by rw [Sum.inl_injective h])
  have hgg' : (Sum.inr gW : Line C) ≠ Sum.inr gK := fun h => hgg (Sum.inr_injective h)
  simp only [← Finset.mul_sum]
  rw [show ∑ a, ∑ b, ∑ x, ∑ y, wardW (Φ.mass Φ.openLine) (β fa.1) (α fb.tail) (k (.inl fa))
      (k (.inl fb)) q a b x y = _ from ward_sum_D _ P.ε σ _ _ q hσ _ _]
  simp only [Fin.sum_univ_four, wNum, wMs, wCoef,
    lineProd_mod4 P.ε hne Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr hgg']
  have hq : (q (lor (pc kD 5 sW.rev)) : ℂ) =
      ((τ * k (.inr gK) (lor (pc kD 5 sW.rev)) : ℝ) : ℂ) := by
    rw [hτ]; rfl
  simp only [wardKc, wardC0, wardL, hq, dMs_inr]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.val_zero, Fin.val_one, Fin.val_two,
    show (0 : ℕ) < 2 from by decide, show (1 : ℕ) < 2 from by decide,
    show ¬ (2 : ℕ) < 2 from by decide, dProd_single,
    dProd_nil, show ¬ ((3 : Fin 4) : ℕ) < 2 from by decide]
  have h1 := propDenom_ne_zero (M := Φ.mass Φ.openLine) hε (k (.inl fa))
  have h2 := propDenom_ne_zero (M := Φ.mass Φ.openLine) hε (k (.inl fb))
  generalize rest {Sum.inl fa, Sum.inl fb, Sum.inr gW, Sum.inr gK} P.ε (dNum P Φ α β lor)
    (dMs P Φ) k = R
  generalize gVx {fb.1.1, 5} P.e α β lor = G
  generalize extI C αOut βIn μ α β lor = E
  generalize dNum P Φ α β lor (Sum.inr gK) (k (Sum.inr gK)) = NK
  generalize dProd P.ε [P.mγ, P.Λ] (k (Sum.inr gK)) = DK
  generalize dProd P.ε [P.mγ, P.Λ] (k (Sum.inr gW)) = DW
  generalize ((τ * k (Sum.inr gK) (lor (pc kD 5 sW.rev)) : ℝ) : ℂ) = Q
  generalize electronNumerator (Φ.mass Φ.openLine) (k (Sum.inl fa)) (β fa.1) (α fb.tail) = A1
  generalize electronNumerator (Φ.mass Φ.openLine) (k (Sum.inl fb)) (β fa.1) (α fb.tail) = A2
  generalize propDenom (Φ.mass Φ.openLine) P.ε (k (Sum.inl fa)) = D1 at h1 ⊢
  generalize propDenom (Φ.mass Φ.openLine) P.ε (k (Sum.inl fb)) = D2 at h2 ⊢
  have h1' := mul_inv_cancel₀ h1
  have h2' := mul_inv_cancel₀ h2
  linear_combination ((1 / 256 : ℂ) * E * (I / 2 * δ₃ * Q) * (I * P.e) * G * (NK * DK) * R *
    ((1 / I) ^ 3 * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * DW) * σ) * (A2 * D2⁻¹ * h1' - A1 * D1⁻¹ * h2')

section WardInv

variable (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) {C : Contraction 1 1 kD}
  (αOut βIn μ : Fin 1 → Fin 4) (fa fb : FermionLine C) (gW gK : PhotonLine C) (sW : Fin 2)
  (q : Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (α β : Wick.FermionVertex kD → Fin 4)
  (lor : Wick.PhotonSlot kD → Fin 4)

theorem wardKc_update_α (hab : fa.tail = fb.1) (hxF : ∀ i, C.1.1 (.inl i) ≠ .inr fb.1)
    (a : Fin 4) :
    wardKc P Φ δ₃ αOut βIn μ fa fb gW gK sW q k (Function.update α fb.1 a) β lor =
      wardKc P Φ δ₃ αOut βIn μ fa fb gW gK sW q k α β lor := by
  simp only [wardKc, extI_update_α C αOut βIn μ α β lor fb.1 hxF,
    gVx_update_α {fb.1.1, 5} P.e α β lor fb.1 (by simp) a, dNum_inr,
    rest_update_α P Φ (wardL fa fb gW gK) α β lor k fb.1 (fun f hf => by
      have := QED.GradedProof.X0Deg6.eq_of_tail_eq (hf.trans hab.symm)
      rw [this]
      simp [wardL]) a]

theorem wardKc_update_β (b : Fin 4) :
    wardKc P Φ δ₃ αOut βIn μ fa fb gW gK sW q k α (Function.update β fb.1 b) lor =
      wardKc P Φ δ₃ αOut βIn μ fa fb gW gK sW q k α β lor := by
  have hw : ∀ i, C.1.1 (.inr fb.1) ≠ .inl i := fun i h => by
    have := fb.2
    rw [h] at this
    simp at this
  simp only [wardKc, extI_update_β C αOut βIn μ α β lor fb.1 hw,
    gVx_update_β {fb.1.1, 5} P.e α β lor fb.1 (by simp) b, dNum_inr,
    rest_update_β P Φ (wardL fa fb gW gK) α β lor k fb.1 (fun f hf => by
      have : f = fb := Subtype.ext hf
      rw [this]
      simp [wardL]) b]

theorem wardKc_update_lor (hgg : gW ≠ gK)
    (hgo : ∀ g : PhotonLine C, g ≠ gW → g.1 ≠ slD fb.1 ∧ g.head ≠ slD fb.1 ∧
      g.1 ≠ pc kD 5 sW ∧ g.head ≠ pc kD 5 sW)
    (hxA : ∀ j, C.1.2 (.inl j) ≠ .inr (slD fb.1) ∧ C.1.2 (.inl j) ≠ .inr (pc kD 5 sW))
    (r : Wick.PhotonSlot kD) (hr : r = slD fb.1 ∨ r = pc kD 5 sW) (x : Fin 4) :
    wardKc P Φ δ₃ αOut βIn μ fa fb gW gK sW q k α β (Function.update lor r x) =
      wardKc P Φ δ₃ αOut βIn μ fa fb gW gK sW q k α β lor := by
  have hK := hgo gK (Ne.symm hgg)
  have hcK : pc kD 5 sW.rev ≠ r := by
    rcases hr with rfl | rfl
    · intro h
      exact ne_five fb.1 (congrArg Sigma.fst h).symm
    · fin_cases sW <;> decide
  have hr5 : r.1 ∈ ({fb.1.1, 5} : Finset (Fin 6)) := by
    rcases hr with rfl | rfl
    · simp [slD]
    · simp [pc]
  simp only [wardKc, extI_update_lor C αOut βIn μ α β lor r (fun j => by
      rcases hr with rfl | rfl
      exacts [(hxA j).1, (hxA j).2]),
    gVx_update_lor {fb.1.1, 5} (by simp) P.e α β lor r hr5 x, dNum_inr, Function.update_of_ne hcK,
    rest_update_lor P Φ (wardL fa fb gW gK) α β lor k r (fun g hg => by
      by_cases h : g = gW
      · rw [h]; simp [wardL]
      · exfalso
        rcases hr with rfl | rfl <;> rcases hg with hg | hg
        exacts [(hgo g h).1 hg, (hgo g h).2.1 hg, (hgo g h).2.2.1 hg, (hgo g h).2.2.2 hg]) x]
  have h1 : gK.1 ≠ r := by rcases hr with rfl | rfl; exacts [hK.1, hK.2.2.1]
  have h2 : gK.head ≠ r := by rcases hr with rfl | rfl; exacts [hK.2.1, hK.2.2.2]
  rw [Function.update_of_ne h1, Function.update_of_ne h2]

end WardInv

/-- The sign relation of two momenta read off integer vectors. -/
theorem exists_sign (pIn kIn : Fin 1 → Fin 4 → ℝ) (v w : Fin 4 → ℤ) (hv : v = w ∨ v = -w)
    (Q K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ)
    (hQ : ∀ ℓ, Q ℓ = mvReal ℓ (pIn 0) (kIn 0) v) (hK : ∀ ℓ, K ℓ = mvReal ℓ (pIn 0) (kIn 0) w) :
    ∃ σ : ℝ, ∀ ℓ, Q ℓ = σ • K ℓ := by
  rcases hv with h | h
  · exact ⟨1, fun ℓ => by rw [hQ, hK, h, one_smul]⟩
  · exact ⟨-1, fun ℓ => by rw [hQ, hK, h, map_neg, neg_one_smul]⟩

/-- **(T₉′) of the `k_μ k_ν` part, by the Ward identity at the internal vertex `fb.1`** on the
photon line `gW` from the counterterm field `sW`, the other factor `k` kept on `gK`. -/
theorem jointEnergyFirstIntegrable_ctK_ward (P : Params) (Φ : Lepton.Flavors F) (hε : 0 < P.ε)
    (δ₃ : ℝ) (C : Contraction 1 1 kD) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) (fa fb : FermionLine C)
    (gW gK : PhotonLine C) (sW : Fin 2) (hab : fa.tail = fb.1) (hfa : fa.1 ≠ fb.1)
    (hfb : fb.tail ≠ fb.1) (hgg : gW ≠ gK)
    (hW : (gW.1 = slD fb.1 ∧ gW.head = pc kD 5 sW) ∨ (gW.1 = pc kD 5 sW ∧ gW.head = slD fb.1))
    (hgo : ∀ g : PhotonLine C, g ≠ gW → g.1 ≠ slD fb.1 ∧ g.head ≠ slD fb.1 ∧
      g.1 ≠ pc kD 5 sW ∧ g.head ≠ pc kD 5 sW)
    (hxF : ∀ i, C.1.1 (.inl i) ≠ .inr fb.1)
    (hxA : ∀ j, C.1.2 (.inl j) ≠ .inr (slD fb.1) ∧ C.1.2 (.inl j) ≠ .inr (pc kD 5 sW))
    (hσ : pmv C (pc kD 5 0) = mv C (.inl fa) - mv C (.inl fb) ∨
      pmv C (pc kD 5 0) = -(mv C (.inl fa) - mv C (.inl fb)))
    (hτ : pmv C (pc kD 5 0) = mv C (.inr gK) ∨ pmv C (pc kD 5 0) = -mv C (.inr gK))
    (hcrit : WardCrit C fa fb gW gK) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => ∑ α, ∑ β, ∑ lor,
      extI C αOut βIn μ α β lor *
        (ctKD δ₃ lor (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)) *
          (gV P.e α β lor *
            lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (lineMomentum₂ C pOut pIn kIn ℓ))) := by
  set k := lineMomentum₂ C pOut pIn kIn with hk
  set q := fun ℓ => photonMomentum₂ C kIn (k ℓ) (pc kD 5 0) with hq
  obtain ⟨σ, hσ'⟩ := exists_sign pIn kIn _ _ hσ q
    (fun ℓ => k ℓ (.inl fa) - k ℓ (.inl fb))
    (fun ℓ => photonMomentum₂_eq_pmv C pOut pIn kIn hmom ℓ _)
    (fun ℓ => by simp only [hk, lineMomentum₂_eq_mv C pOut pIn kIn hmom, map_sub])
  obtain ⟨τ, hτ'⟩ := exists_sign pIn kIn _ _ hτ q (fun ℓ => k ℓ (.inr gK))
    (fun ℓ => photonMomentum₂_eq_pmv C pOut pIn kIn hmom ℓ _)
    (fun ℓ => lineMomentum₂_eq_mv C pOut pIn kIn hmom ℓ _)
  have hpq : slD fb.1 ≠ pc kD 5 sW := fun h => ne_five fb.1 (congrArg Sigma.fst h)
  have hkey : ∀ ℓ, ∑ α, ∑ β, ∑ lor, extI C αOut βIn μ α β lor * (ctKD δ₃ lor (q ℓ) *
      (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (k ℓ))) =
      ∑ α, ∑ β, ∑ lor, ∑ w : Fin 4, (1 / 256 : ℂ) * extI C αOut βIn μ α β lor *
        ((I / 2) * (δ₃ : ℂ)) * (I * (P.e : ℂ)) * gVx {fb.1.1, 5} P.e α β lor * (1 / I) ^ 3 *
          ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * (σ : ℂ) * wCoef P.ε w *
            lineProd P.ε (wNum P Φ fa fb gW gK α β lor sW τ w) (wMs P Φ fa fb gW gK w)
              (k ℓ) := by
    intro ℓ
    simp only [ward_decomp P Φ δ₃ αOut βIn μ fa fb gW gK sW hab hfa hgg hW (q ℓ) (k ℓ)]
    have h4 := sum_resum_four fb.1 hpq (fun α β lor a b x y =>
      wardKc P Φ δ₃ αOut βIn μ fa fb gW gK sW (q ℓ) (k ℓ) α β lor * wardC0 P Φ fa fb gW (k ℓ) *
        wardW (Φ.mass Φ.openLine) (β fa.1) (α fb.tail) (k ℓ (.inl fa)) (k ℓ (.inl fb)) (q ℓ)
          a b x y)
      (fun α β lor a => by
        funext a' b' x y
        simp only [wardKc_update_α P Φ δ₃ αOut βIn μ fa fb gW gK sW _ _ α β lor hab hxF,
          Function.update_of_ne hfb])
      (fun α β lor b => by
        funext a' b' x y
        simp only [wardKc_update_β, Function.update_of_ne hfa])
      (fun α β lor x => by
        funext a' b' x' y
        simp only [wardKc_update_lor P Φ δ₃ αOut βIn μ fa fb gW gK sW _ _ α β lor hgg hgo hxA _
          (Or.inl rfl)])
      (fun α β lor x => by
        funext a' b' x' y
        simp only [wardKc_update_lor P Φ δ₃ αOut βIn μ fa fb gW gK sW _ _ α β lor hgg hgo hxA _
          (Or.inr rfl)])
    rw [h4]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun lor _ => ?_
    exact ward_resummed P Φ hε.ne' δ₃ αOut βIn μ fa fb gW gK sW hfa hgg σ τ (q ℓ) (k ℓ) (hσ' ℓ)
      (hτ' ℓ) α β lor
  refine (congrArg _ (funext hkey)).mpr ?_
  refine jointEnergyFirstIntegrable_sum' _ fun α _ => jointEnergyFirstIntegrable_sum' _ fun β _ =>
    jointEnergyFirstIntegrable_sum' _ fun lor _ => jointEnergyFirstIntegrable_sum' _ fun w _ => ?_
  exact jointEnergyFirstIntegrable_lineProd C pOut pIn kIn hε _ _ _ (wardD fa fb gW gK w)
    (affPoly_wNum P Φ fa fb gW gK α β lor sW τ w) (by rw [length_wMs]; exact hcrit w)

end QED.ChainProof.SetCLink

end
