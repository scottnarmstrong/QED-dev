/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBWick

/-!
# Set (c), the bubble classes: the Wick step

Helper level for set (c), the bubble classes `QED.ChainProof.SetCLink.repB i`, at any parameters
with `ε ≠ 0`. With the dictionary of `QED/ChainProof/SetCMainBWick.lean`, the integrand of
`repB i` is that of `QED.ChainProof.SetCLink.repD i 0` with the `photonCt` factor replaced by
the one-loop vacuum polarization integrand of the bubble:

* `insD X C`: the two-loop integrand of a `kD` contraction with the `photonCt` factor replaced by
  an insertion `X(lor, k)` at the photon momentum `k` of the field `(5, 0)`; the transverse part
  of `repD` is the insertion `ctGD δ₃` (`dGIntegrand_eq_insD`, by definition);
* `sum_insD`: contracting the open insertion `δ^{ρ}_{a} δ^{σ}_{b}` with `Y ρ σ` is the insertion
  `Y`;
* `outerBW i`, `kBW i`: the outer factor (minus the open insertion of `repD i 0`) and the photon
  momentum through the bubble (that of `repD i 0` at `(5, 0)`);
* **`integrand_repB`** (the Wick step, twelve orbits): for flavours whose loop sums are those of
  `P` (`FlavorsLoop`), in the nested routing `ℓ ↦ (ℓ 1, ℓ 2, ℓ 0)` (bubble momentum `ℓ 0`),
  `(2π)⁻¹²` times the graded regulated amplitude of `repB i` is
  `QED.ChainProof.SetCMainB.nestB P (outerBW i) (kBW i)`;
* **`contractionValue_repB_eq`**: the graded value of `repB i` is the joint energy-first integral
  at three loops of `nestB P (outerBW i) (kBW i)`;
* **`outerBub_outerBW`**: with the bubble in closed form, the outer integrand is the insertion
  `-T(k)^{ab}` into `repD i 0`, `T = i Π̂_ε(k²)(k² g - k k) + ε S_ε(k²) g`.
-/

@[expose] public section

open Complex
open QED.WickModel (Params Contraction FermionLine PhotonLine Line lineMomentum₂
  photonMomentum₂)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCLink QED.ChainProof.SetALink QED.GradedProof.X0
open QED.ChainProof.SetCMain (fvD lineRD lineRD_tail photD dGIntegrand)
open QED.ChainProof.Enum (pc)
open QED.TwoLoop.Bridge (electronPropagator_apply photonPropagator_eq_mul)

variable {F : Type}

/-! ### Insertions into a `kD` contraction -/

/-- The two-loop integrand of a `kD` contraction with the `photonCt` factor replaced by the
insertion `X lor k` at the photon momentum `k` of the field `(5, 0)`, with the loop measure
`(2π)⁻⁸`. -/
noncomputable def insD (P : Params) (Φ : Lepton.Flavors F)
    (X : (Wick.PhotonSlot kD → Fin 4) → (Fin 4 → ℝ) → ℂ) (C : Contraction 1 1 kD)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ℂ :=
  (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * ∑ α, ∑ β, ∑ lor,
    extI C αOut βIn μ α β lor *
      (X lor (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)) *
        (gV P.e α β lor *
          lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (lineMomentum₂ C pOut pIn kIn ℓ)))

/-- The transverse part of a `kD` contraction is the insertion `ctGD δ₃`. -/
theorem dGIntegrand_eq_insD (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) (C : Contraction 1 1 kD)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    dGIntegrand P Φ δ₃ C pOut pIn kIn αOut βIn μ = insD P Φ (ctGD δ₃) C pOut pIn kIn αOut βIn μ :=
  rfl

/-- The open insertion `δ^{ρ}_{a} δ^{σ}_{b}`. -/
def openIns (ρ σ : Fin 4) (lor : Wick.PhotonSlot kD → Fin 4) (_k : Fin 4 → ℝ) : ℂ :=
  if lor (pc kD 5 0) = ρ ∧ lor (pc kD 5 1) = σ then 1 else 0

theorem sum_openIns (Y : Fin 4 → Fin 4 → ℂ) (lor : Wick.PhotonSlot kD → Fin 4)
    (k : Fin 4 → ℝ) :
    ∑ ρ, ∑ σ, openIns ρ σ lor k * Y ρ σ = Y (lor (pc kD 5 0)) (lor (pc kD 5 1)) := by
  simp [openIns, ite_and, Finset.sum_ite_eq]

/-- Moving a sum inside three nested sums. -/
theorem sum_comm_three_out {ι A B C : Type*} [Fintype ι] [Fintype A] [Fintype B] [Fintype C]
    (f : ι → A → B → C → ℂ) :
    ∑ x, ∑ a, ∑ b, ∑ c, f x a b c = ∑ a, ∑ b, ∑ c, ∑ x, f x a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

/-- **Contracting the open insertion** with `Y ρ σ` gives the insertion `Y`. -/
theorem sum_insD (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 1 kD)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ)
    (Y : Fin 4 → Fin 4 → ℂ) :
    ∑ ρ, ∑ σ, insD P Φ (openIns ρ σ) C pOut pIn kIn αOut βIn μ ℓ * Y ρ σ =
      insD P Φ (fun lor _ => Y (lor (pc kD 5 0)) (lor (pc kD 5 1))) C pOut pIn kIn αOut βIn μ
        ℓ := by
  unfold insD
  set k := photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)
  have h : ∀ ρ σ, (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (∑ α, ∑ β, ∑ lor,
      extI C αOut βIn μ α β lor * (openIns ρ σ lor k * (gV P.e α β lor *
        lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (lineMomentum₂ C pOut pIn kIn ℓ)))) * Y ρ σ =
      (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * ∑ α, ∑ β, ∑ lor,
        extI C αOut βIn μ α β lor * (gV P.e α β lor *
          lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (lineMomentum₂ C pOut pIn kIn ℓ)) *
            (openIns ρ σ lor k * Y ρ σ) := by
    intro ρ σ
    simp only [Finset.sum_mul, mul_assoc]
    refine congrArg _ (Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun lor _ => ?_)
    ring
  simp only [h, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl fun ρ _ => sum_comm_three_out _, sum_comm_three_out]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  simp only [← Finset.mul_sum, sum_openIns]
  ring

/-! ### The outer factor of `repB i` -/

/-- The photon momentum through the bubble of `repB i`: that of `repD i 0` at the field
`(5, 0)`. -/
noncomputable def kBW (i : Fin 12) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Fin 4 → ℝ :=
  photonMomentum₂ (repD i 0) kIn (lineMomentum₂ (repD i 0) pOut pIn kIn ℓ) (pc kD 5 0)

/-- **The outer factor of `repB i`**: minus the open insertion into `repD i 0`. -/
noncomputable def outerBW (P : Params) (Φ : Lepton.Flavors F) (i : Fin 12)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ)
    (ρ σ : Fin 4) : ℂ :=
  -insD P Φ (openIns ρ σ) (repD i 0) pOut pIn kIn αOut βIn μ ℓ

/-! ### Index terms -/

variable (P : Params) (Φ : Lepton.Flavors F)

/-- The line factors of a `kD` contraction as propagators. -/
theorem lineProd_eq_props (hε : P.ε ≠ 0) {C : Contraction 1 1 kD}
    (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4)
    (k : Line C → Fin 4 → ℝ) :
    lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k =
      (∏ f : FermionLine C, (1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε
        (k (.inl f)) (β f.1) (α f.tail)) *
      ∏ g : PhotonLine C, (1 / I) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr g)) (lor g.1) (lor g.head) := by
  unfold lineProd
  rw [Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun f _ => ?_
    simp only [dNum, dMs, QED.GradedProof.X0.dProd, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, electronPropagator_apply]
    ring
  · refine Finset.prod_congr rfl fun g _ => ?_
    rw [photonPropagator_eq_mul P.mγ P.Λ hε]
    simp only [dNum, dMs, QED.GradedProof.X0.dProd, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    ring

/-- The `gauge` vertex factors of `kD`. -/
theorem gV_eq_prod (e : ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) :
    gV e α β lor =
      ∏ t : Fin 5, I * (e : ℂ) * Dirac.gamma (lor (plD t)) (α (fvD t)) (β (fvD t)) := by
  unfold gV
  rw [Fin.prod_univ_castSucc]
  simp only [show Fin.last 5 = (5 : Fin 6) from rfl, ite_true, mul_one]
  refine Finset.prod_congr rfl fun t _ => ?_
  have ht : Fin.castSucc t ≠ (5 : Fin 6) := by fin_cases t <;> decide
  simp only [ht, ite_false]
  exact vertexFactor_kD_gauge e 0 0 1 0 1 α β lor 0 0 (fvD t)

/-- The vertex factors of `kB` on glued indices. -/
theorem prod_vf0_glue (D : Graded.Counterterms F) (x : Fin 7 → F) (M : Fin 7 → ℝ)
    (α β : Wick.FermionVertex kD → Fin 4) (a b : Fin 2 → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (kψ : Wick.FermionVertex kB → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot kB → Fin 4 → ℝ) :
    ∏ t, vf0 P D (x t) (M t) (glue α a) (glue β b) (lor ∘ slotKB) kψ kA t =
      (∏ t : Fin 5, I * (P.e : ℂ) * Dirac.gamma (lor (plD t)) (α (fvD t)) (β (fvD t))) *
        ((I * (P.e : ℂ) * Dirac.gamma (lor (pc kD 5 0)) (a 0) (b 0)) *
          (I * (P.e : ℂ) * Dirac.gamma (lor (pc kD 5 1)) (a 1) (b 1))) := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
  congr 1

/-- The external constraints of `repB i` on glued indices are those of `repD i 0`. -/
theorem extI_eq_of {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 1 κ}
    {tO tI : Wick.FermionVertex κ} {aK : Wick.PhotonSlot κ} (h1 : C.1.1 (.inl 0) = .inr tO)
    (h2 : C.1.1 (.inr tI) = .inl 0) (h3 : C.1.2 (.inl 0) = .inr aK) (αOut βIn μ : Fin 1 → Fin 4)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) :
    extI C αOut βIn μ α β lor =
      if α tO = αOut 0 ∧ β tI = βIn 0 ∧ lor aK = μ 0 then 1 else 0 := by
  unfold extI
  refine if_congr ⟨fun ⟨e1, e2, e3⟩ => ⟨e1 0 tO h1, e2 tI 0 h2, e3 0 aK h3⟩,
    fun ⟨e1, e2, e3⟩ => ⟨fun j t ht => ?_, fun t j ht => ?_, fun j a ha => ?_⟩⟩ rfl rfl
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    obtain rfl := Sum.inr_injective (h1.symm.trans ht)
    exact e1
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    obtain rfl := Sum.inr_injective (C.1.1.injective (ht.trans h2.symm))
    exact e2
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    obtain rfl := Sum.inr_injective (h3.symm.trans ha)
    exact e3

theorem slotB_plB : ∀ t : Fin 5, slotKB (plB t) = plD t := by decide

theorem extI_glue (i : Fin 12) (αOut βIn μ : Fin 1 → Fin 4) (α β : Wick.FermionVertex kD → Fin 4)
    (a b : Fin 2 → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4) :
    extI (repB i) αOut βIn μ (glue α a) (glue β b) (lor ∘ slotKB) =
      extI (repD i 0) αOut βIn μ α β lor := by
  obtain ⟨h1, h2, h3⟩ := ext_repB i
  obtain ⟨g1, g2, g3⟩ := ext_repD0 i
  rw [extI_eq_of h1 h2 h3, extI_eq_of g1 g2 g3, Function.comp_apply, slotB_plB]
  rfl

/-! ### Line momenta in the nested routing -/

variable {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}

theorem mom_lineBO (hmom : pOut 0 = pIn 0 + kIn 0) (i : Fin 12) (j : Fin 4)
    (ℓ : Fin 3 → Fin 4 → ℝ) :
    lineMomentum₂ (repB i) pOut pIn kIn (rot ℓ) (.inl (lineBO i j)) =
      lineMomentum₂ (repD i 0) pOut pIn kIn (Fin.tail ℓ) (.inl (lineRD i 0 j)) := by
  rw [lineMomentum₂_eq_mv3 _ _ _ _ hmom, lineMomentum₂_eq_mv _ _ _ _ hmom, mv3_lineBO,
    mvReal3_rot_ext3]

theorem mom_photB (hmom : pOut 0 = pIn 0 + kIn 0) (i : Fin 12) (r : Fin 3)
    (ℓ : Fin 3 → Fin 4 → ℝ) :
    lineMomentum₂ (repB i) pOut pIn kIn (rot ℓ) (.inr (photB i r)) =
      lineMomentum₂ (repD i 0) pOut pIn kIn (Fin.tail ℓ) (.inr (photD i 0 r)) := by
  rw [lineMomentum₂_eq_mv3 _ _ _ _ hmom, lineMomentum₂_eq_mv _ _ _ _ hmom, mv3_photB,
    mvReal3_rot_ext3]

theorem mom_lineBb (hmom : pOut 0 = pIn 0 + kIn 0) (i : Fin 12) (ℓ : Fin 3 → Fin 4 → ℝ) :
    lineMomentum₂ (repB i) pOut pIn kIn (rot ℓ) (.inl (lineBb i 0)) = ℓ 0 ∧
      lineMomentum₂ (repB i) pOut pIn kIn (rot ℓ) (.inl (lineBb i 1)) =
        ℓ 0 + kBW i pOut pIn kIn (Fin.tail ℓ) := by
  refine ⟨?_, ?_⟩
  · rw [lineMomentum₂_eq_mv3 _ _ _ _ hmom, (mv3_lineBb i).1, mvReal3_rot_bub3]
  · rw [lineMomentum₂_eq_mv3 _ _ _ _ hmom, (mv3_lineBb i).2, mvReal3_rot_bub, kBW,
      photonMomentum₂_eq_pmv _ _ _ _ hmom, add_comm]

/-! ### The bubble -/

/-- The bubble index term: the two bubble vertices and the two bubble lines, with the photon
indices `ρ` (field `5`) and `σ` (field `6`). -/
noncomputable def bubT (e M ε : ℝ) (q K : Fin 4 → ℝ) (a b : Fin 2 → Fin 4) (ρ σ : Fin 4) : ℂ :=
  (I * (e : ℂ) * Dirac.gamma ρ (a 0) (b 0)) * (I * (e : ℂ) * Dirac.gamma σ (a 1) (b 1)) *
    ((1 / I) * QED.OneLoop.electronPropagator M ε q (b 0) (a 1)) *
      ((1 / I) * QED.OneLoop.electronPropagator M ε (q + K) (b 1) (a 0))

theorem sum_fin_two_arrow (G : (Fin 2 → Fin 4) → ℂ) :
    ∑ a, G a = ∑ x, ∑ y, G ![x, y] := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 4) _ _ fun a =>
    congrArg G (funext fun s => by fin_cases s <;> rfl)

/-- **The bubble sum**: the trace of the closed loop. -/
theorem sum_bubT (e M ε : ℝ) (q K : Fin 4 → ℝ) (ρ σ : Fin 4) :
    ∑ a, ∑ b, bubT e M ε q K a b ρ σ = (I * (e : ℂ)) ^ 2 * (1 / I) ^ 2 *
      Matrix.trace (QED.OneLoop.electronPropagator M ε (q + K) * Dirac.gamma ρ *
        QED.OneLoop.electronPropagator M ε q * Dirac.gamma σ) := by
  rw [sum_fin_two_arrow]
  simp only [sum_fin_two_arrow (fun b => bubT e M ε q K _ b ρ σ)]
  simp only [bubT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm_three_out]
  conv_lhs => enter [2, a1]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-! ### The Wick step -/

open scoped Classical in
/-- **One index term** of `repB i` on glued indices, in the nested routing: the index term of
the open insertion into `repD i 0` times the bubble index term. -/
theorem ampTerm_glue (D : Graded.Counterterms F) (hε : P.ε ≠ 0) (hmom : pOut 0 = pIn 0 + kIn 0)
    (i : Fin 12) (f : F) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 3 → Fin 4 → ℝ)
    (α β : Wick.FermionVertex kD → Fin 4) (a b : Fin 2 → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) :
    ampTerm P Φ D (repB i) (closedFlavoring Φ (zOf (repB i)) f) pIn kIn
        (lineMomentum₂ (repB i) pOut pIn kIn (rot ℓ)) αOut βIn μ (glue α a) (glue β b)
        (lor ∘ slotKB) =
      extI (repD i 0) αOut βIn μ α β lor *
        (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ)
          (lineMomentum₂ (repD i 0) pOut pIn kIn (Fin.tail ℓ))) *
        bubT P.e (Φ.mass f) P.ε (ℓ 0) (kBW i pOut pIn kIn (Fin.tail ℓ)) a b
          (lor (pc kD 5 0)) (lor (pc kD 5 1)) := by
  unfold ampTerm
  change extI (repB i) αOut βIn μ (glue α a) (glue β b) (lor ∘ slotKB) * _ = _
  rw [extI_glue, prod_vf0_glue, lineProd_eq_props P Φ hε, gV_eq_prod, prod_lineB, prod_photB,
    prod_lineRD0, prod_photD0]
  have hO : ∀ j, (1 / I) * QED.OneLoop.electronPropagator
      (Φ.mass (closedFlavoring Φ (zOf (repB i)) f (lineBO i j).1)) P.ε
      (lineMomentum₂ (repB i) pOut pIn kIn (rot ℓ) (.inl (lineBO i j)))
      (glue β b (lineBO i j).1) (glue α a (lineBO i j).tail) =
      (1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε
        (lineMomentum₂ (repD i 0) pOut pIn kIn (Fin.tail ℓ) (.inl (lineRD i 0 j)))
        (β (lineRD i 0 j).1) (α (lineRD i 0 j).tail) := by
    intro j
    simp only [closedFlavoring, zOf_lineBO i j, ite_false, glue, (vB_lineBO i j).1,
      (vB_lineBO i j).2, Sum.elim_inl, mom_lineBO hmom i j ℓ]
  have hP : ∀ r, (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
      (lineMomentum₂ (repB i) pOut pIn kIn (rot ℓ) (.inr (photB i r)))
      ((lor ∘ slotKB) (photB i r).1) ((lor ∘ slotKB) (photB i r).head) =
      (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
        (lineMomentum₂ (repD i 0) pOut pIn kIn (Fin.tail ℓ) (.inr (photD i 0 r)))
        (lor (photD i 0 r).1) (lor (photD i 0 r).head) := by
    intro r
    simp only [Function.comp_apply, (slotB_photB i r).1, (slotB_photB i r).2,
      mom_photB hmom i r ℓ]
  simp only [hO, hP]
  obtain ⟨hb0, hb1⟩ := mom_lineBb hmom i ℓ
  obtain ⟨v1, v2, v3, v4⟩ := vB_lineBb i
  simp only [closedFlavoring, zOf_lineBb, ite_true, glue, v1, v2, v3, v4, Sum.elim_inr, hb0, hb1]
  unfold bubT
  ring

open scoped Classical in
/-- The index sum of `repB i` at one bubble flavour, in the nested routing. -/
theorem sum_ampTerm_repB (D : Graded.Counterterms F) (hε : P.ε ≠ 0)
    (hmom : pOut 0 = pIn 0 + kIn 0) (i : Fin 12) (f : F) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 3 → Fin 4 → ℝ) :
    ∑ α, ∑ β, ∑ lor, ampTerm P Φ D (repB i) (closedFlavoring Φ (zOf (repB i)) f) pIn kIn
        (lineMomentum₂ (repB i) pOut pIn kIn (rot ℓ)) αOut βIn μ α β lor =
      ∑ α, ∑ β, ∑ lor, extI (repD i 0) αOut βIn μ α β lor *
        (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ)
          (lineMomentum₂ (repD i 0) pOut pIn kIn (Fin.tail ℓ))) *
        ((I * (P.e : ℂ)) ^ 2 * (1 / I) ^ 2 * Matrix.trace
          (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (ℓ 0 + kBW i pOut pIn kIn (Fin.tail ℓ)) *
            Dirac.gamma (lor (pc kD 5 0)) * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (ℓ 0) *
              Dirac.gamma (lor (pc kD 5 1)))) := by
  simp only [sum_glue, sum_slotB, ampTerm_glue P Φ D hε hmom i f αOut βIn μ ℓ]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lor _ => ?_
  rw [← sum_bubT]
  simp only [Finset.mul_sum]

theorem sum_coeff_comm {ι A B C : Type*} [Fintype ι] [Fintype A] [Fintype B] [Fintype C]
    (c : ι → ℂ) (O : A → B → C → ℂ) (G : ι → C → ℂ) :
    ∑ f, c f * ∑ a, ∑ b, ∑ x, O a b x * G f x = ∑ a, ∑ b, ∑ x, O a b x * ∑ f, c f * G f x := by
  simp only [Finset.mul_sum]
  rw [sum_comm_three_out]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun f _ => ?_
  ring

/-- The loop sums of the flavours are those of `P`: `∑_f c_f g(M_f) = ∑_{i < 3} c_i g(M_i)`. -/
def FlavorsLoop [Fintype F] (P : Params) (Φ : Lepton.Flavors F) : Prop :=
  ∀ g : ℝ → ℂ, ∑ f, (Φ.coeff f : ℂ) * g (Φ.mass f) = ∑ f : Fin 3, (P.loopCoeff f : ℂ) * g (P.mass f)

theorem flavorsLoop_lepton (P : Params) :
    FlavorsLoop P (Lepton.leptonFlavors P (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) := by
  intro g
  simp [Fintype.sum_sum_type, Lepton.leptonFlavors]

/-- **The Wick step for the bubble classes** (twelve orbits, any parameters with `ε ≠ 0`): in
the nested routing, `(2π)⁻¹²` times the graded regulated amplitude of `repB i` is
`nestB P (outerBW i) (kBW i)`. -/
theorem integrand_repB [Fintype F] [DecidableEq F] (D : Graded.Counterterms F) (hε : P.ε ≠ 0)
    (hΦ : FlavorsLoop P Φ) (i : Fin 12) (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 3 → Fin 4 → ℝ) :
    (((2 * Real.pi) ^ (4 * 3) : ℝ) : ℂ)⁻¹ * Graded.regulatedAmplitude P Φ D (repB i) 0 pIn kIn
        (lineMomentum₂ (repB i) pOut pIn kIn (rot ℓ)) αOut βIn μ =
      nestB P (outerBW P Φ i pOut pIn kIn αOut βIn μ) (kBW i pOut pIn kIn) ℓ := by
  have hC : ClosedShape (repB i) (zOf (repB i)) := by
    obtain ⟨s1, s2, s3⟩ := shapeOK_repB i
    exact ⟨s1, fun t ht => s2 t ht not_false, s3⟩
  rw [regulatedAmplitude_eq_closed Φ P D hC 0]
  simp only [contractionAmplitude_zero_eq, sum_ampTerm_repB P Φ D hε hmom i]
  rw [sum_coeff_comm]
  set K := kBW i pOut pIn kIn (Fin.tail ℓ)
  have hB : ∀ lor : Wick.PhotonSlot kD → Fin 4, ∑ f, (Φ.coeff f : ℂ) *
      ((I * (P.e : ℂ)) ^ 2 * (1 / I) ^ 2 * Matrix.trace
        (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (ℓ 0 + K) * Dirac.gamma (lor (pc kD 5 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (ℓ 0) * Dirac.gamma (lor (pc kD 5 1)))) =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        ((I * (P.e : ℂ)) ^ 2 * (1 / I) ^ 2 * Matrix.trace
          (QED.OneLoop.electronPropagator (P.mass f) P.ε (ℓ 0 + K) *
            Dirac.gamma (lor (pc kD 5 0)) * QED.OneLoop.electronPropagator (P.mass f) P.ε (ℓ 0) *
              Dirac.gamma (lor (pc kD 5 1)))) := fun lor =>
    hΦ fun M => (I * (P.e : ℂ)) ^ 2 * (1 / I) ^ 2 * Matrix.trace
      (QED.OneLoop.electronPropagator M P.ε (ℓ 0 + K) * Dirac.gamma (lor (pc kD 5 0)) *
        QED.OneLoop.electronPropagator M P.ε (ℓ 0) * Dirac.gamma (lor (pc kD 5 1)))
  simp only [hB]
  unfold nestB outerBW
  simp only [neg_mul, Finset.sum_neg_distrib]
  rw [sum_insD]
  unfold insD QED.WickModel.vacuumPolarizationIntegrand
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => Finset.sum_congr rfl fun f _ => ?_
  push_cast
  ring

/-- **The value of the bubble classes in the nested routing** (any parameters with `ε ≠ 0`,
flavours with the loop sums of `P`, momentum conservation): the graded value of `repB i` is the
joint energy-first integral at three loops of `nestB P (outerBW i) (kBW i)`. -/
theorem contractionValue_repB_eq [Fintype F] [DecidableEq F] (D : Graded.Counterterms F)
    (hε : P.ε ≠ 0) (hΦ : FlavorsLoop P Φ) (i : Fin 12) (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.contractionValue P Φ D (repB i) 0 pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 3
        (nestB P (outerBW P Φ i pOut pIn kIn αOut βIn μ) (kBW i pOut pIn kIn)) := by
  unfold Graded.contractionValue
  rw [loopCount_repB]
  rw [← QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 3 _ rotM
    isUnit_det_rotM 0]
  refine congrArg _ (funext fun ℓ => ?_)
  rw [← rot_eq, integrand_repB P Φ D hε hΦ i hmom]

/-- **The outer integrand with the bubble in closed form** is the insertion `-T(k)^{ab}` into
`repD i 0`, `T = i Π̂_ε(k²)(k² g - k k) + ε S_ε(k²) g`. -/
theorem outerBub_outerBW (i : Fin 12) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    outerBub P (outerBW P Φ i pOut pIn kIn αOut βIn μ) (kBW i pOut pIn kIn) ℓ =
      insD P Φ (fun lor k => -QED.TwoLoop.VPHalfAtAssembly.vpT
        (I * QED.TwoLoop.VPHalfAt.vpLoopEps P P.ε (Minkowski.dot k k))
        ((P.ε : ℂ) * QED.TwoLoop.VPHalfAt.vpExtraEps P P.ε (Minkowski.dot k k)) k
        (lor (pc kD 5 0)) (lor (pc kD 5 1))) (repD i 0) pOut pIn kIn αOut βIn μ ℓ := by
  unfold outerBub QED.ChainProof.HCSide.outerF outerBW
  simp only [neg_mul, Finset.sum_neg_distrib]
  rw [sum_insD]
  unfold insD
  simp only [neg_mul, mul_neg, Finset.sum_neg_distrib]
  rfl

end QED.ChainProof.SetCMainB

end
