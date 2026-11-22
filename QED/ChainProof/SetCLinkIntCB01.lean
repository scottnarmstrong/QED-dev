/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkIntOCTerm
public import QED.ChainProof.SetALinkIntFAmp
public import QED.ChainProof.SetCLinkReps
public import QED.ChainProof.SetCLinkIntDeg6

/-!
# The class obligations of (HS₀) for the classes `CB0` and `CB1`

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58): `classIntA_repCB0`, `classIntA_repCB1`, the class obligations for the two-loop
representatives with a level-`0` `fermionCt` vertex on an internal line of the open line of the
one-loop vertex and the bubble on its photon line.

## Proof

The numerator degree is `5 + 1 = 6` (five loop fermion lines and the counterterm), beyond the
degree `4` of the two-loop theorems. The counterterm vertex sits between two open-line lines
`fi`, `fo` of the same momentum. After the double resummation at the counterterm
(`sum_sum_ampTerm_oc`), each term of variant `j` is `M_f^p` times a product of line factors with
the denominators `D_{M_f}⁻¹` of the closed loop (`prod_ocFac`); `fo` carries no factor and `fi`
an affine entry with `j + 1` denominators, so the degree drops to `4`. If the constant is
non-zero the number `p` of same-block loop entries is even (`even_nsP_of_ne`, the vertices of the
loop being `gauge` vertices). With the multiplicities of the decidable test `OCrit`, the flavour
sum of each term satisfies (T₉′) (`jointEnergyFirstIntegrable_ocTerm`, by
`QED.ChainProof.SetALink.jointEnergyFirstIntegrable_blockLines`), hence the class obligation
(`classIntA_of_oc`). Its hypotheses on `repCB0`, `repCB1` hold by kernel evaluation.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.GradedProof.X0 QED.Graded QED.WickModel QED.ChainProof.SetALink
open QED.ChainProof.Enum (fv)
open QED.GradedProof.X0Deg6 (affNum)
open QED.TwoLoop.Bridge (propDenom)
open QED.TwoLoop.FurryIntegrable (sgn)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type}

/-! ### The decidable test -/

/-- The denominators of the lines in variant `j`. -/
def ocN (C : Contraction 1 nA κ) (fi fo : FermionLine C) (j : Fin 2) : Line C → ℕ :=
  fun l => if l = .inl fo then 0 else if l = .inl fi then j.val + 1 else baseN C l

/-- The numerator degrees of the lines, `E'` the different-block loop lines. -/
def ocD (C : Contraction 1 nA κ) (fi fo : FermionLine C) (E' : Finset (Line C)) : Line C → ℕ :=
  fun l => if l = .inl fo then 0 else if l = .inl fi then 1 else baseD C E' l

/-- **The test for a doubled open line at a fermion counterterm**: for every admissible pattern
`E'` of different-block loop lines and both variants, the multiplicities pass `BlockCrit` at
the mass order `(|loop| - |E'|) / 2`. -/
def OCrit (C : Contraction 1 nA κ) (fi fo : FermionLine C) : Prop :=
  ∀ E' ∈ (zSet C).powerset, ((zSet C).card - E'.card) % 2 = 0 → ∀ j : Fin 2,
    BlockCrit (rowOf C) (ocN C fi fo j) (ocD C fi fo E') (zSet C)
      (((zSet C).card - E'.card) / 2)

instance (C : Contraction 1 nA κ) (fi fo : FermionLine C) : Decidable (OCrit C fi fo) := by
  unfold OCrit; infer_instance

/-! ### Parity and degrees -/

/-- **Parity**: with a non-zero constant, an even number of loop entries are same-block. -/
theorem even_nsP_of_ne (e : ℝ) {C : Contraction 1 nA κ} (fo : FermionLine C)
    (hκ : ∀ t, t ≠ fo.1.1 → κ t = .gauge) (hzo : ¬ zOf C fo.1)
    (hZ : ∀ x, isZ (zOf C) (C.1.1 x) = isZ (zOf C) x) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4)
    (hΓ : ∏ t, (if t = fo.1.1 then 1 else Wick.vertexFactor e 0 0 1 0 1 α β lor 0 0 t) ≠ 0) :
    Even (nsP α β C) := by
  classical
  have hd : ∀ s : {s // zOf C s}, ¬ blk (α s.1) = blk (β s.1) := fun s hb => by
    have hs : s.1.1 ≠ fo.1.1 := fun h => hzo (by
      have : s.1 = fo.1 := Subtype.ext h
      rw [← this]; exact s.2)
    have hne := (Finset.prod_ne_zero_iff.mp hΓ) s.1.1 (Finset.mem_univ _)
    simp only [hs, ↓reduceIte] at hne
    have hg : κ s.1.1 = .gauge := hκ _ hs
    exact hne (by
      rw [← vertexFactor_gauge_eq e 0 0 0 0 0 α β lor 0 0 _ hg]
      exact vertexFactor_gauge_eq_zero_of_blk e α β lor s.1 hg hb)
  have h := even_card_blk_of_prod (fun f : ZLine C (zOf C) => β f.1.1)
    (fun f => α f.1.tail) (prod_sgn_zLine hZ α β hd)
  have hc : (Finset.univ.filter fun f : ZLine C (zOf C) => blk (β f.1.1) = blk (α f.1.tail)).card
      = nsP α β C := by
    rw [nsP, card_zSet_filter]
    congr 1
  rw [← hc]
  exact h

theorem length_ocMs (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ)
    (fi fo : FermionLine C) (hzi : ¬ zOf C fi.1) (hzo : ¬ zOf C fo.1) (j : Fin 2) :
    (fun l => (ocMs P Φ C fi fo j l).length + if l ∈ zSet C then 1 else 0) = ocN C fi fo j := by
  funext l
  have hz : l ∈ zSet C ↔ isZL C l = true := by simp [zSet]
  by_cases h1 : l = .inl fo
  · subst h1
    simp [ocMs, ocN, hz, hzo]
  · by_cases h2 : l = .inl fi
    · subst h2
      simp [ocMs, ocN, hz, hzi, h1]
    · simp only [ocMs, ocN, h1, h2, ↓reduceIte, length_nsMs]
      rcases l with fl | g
      · by_cases hzl : isZL C (.inl fl) = true
        · simp [hz, hzl, baseN]
        · simp [hz, hzl]
      · simp [zSet]

theorem affPoly_ocNum (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (C : Contraction 1 nA κ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (fi fo : FermionLine C) (j : Fin 2) (l : Line C) :
    AffPoly (ocD C fi fo (nsE α β C) l) (ocNum P Φ D C α β lor fi fo j l) ∨ rowOf C l = 0 := by
  by_cases h1 : l = .inl fo
  · refine Or.inl ?_
    simp only [ocD, ocNum, h1, ↓reduceIte]
    exact AffPoly.const 1
  · by_cases h2 : l = .inl fi
    · refine Or.inl ?_
      subst h2
      simp only [ocD, ocNum, h1, ↓reduceIte]
      obtain ⟨u, w, hw⟩ := electronNumerator_affine (Φ.mass Φ.openLine) (β fi.1) (α fo.tail)
      refine (congrArg (AffPoly 1) (funext fun k => ?_)).mp
        ((((AffPoly.aff u w).const_mul (QED.GradedProof.X0Deg6.mergeU
          (P.e ^ 2 * D.d₂ Φ.openLine 0) (P.e ^ 2 * D.dm Φ.openLine 0) (Φ.mass Φ.openLine)
          (Φ.mass Φ.openLine) P.ε j)).add (AffPoly.mono zero_le_one (AffPoly.const
            (QED.GradedProof.X0Deg6.mergeV (P.e ^ 2 * D.d₂ Φ.openLine 0)
              (P.e ^ 2 * D.dm Φ.openLine 0) (Φ.mass Φ.openLine) (Φ.mass Φ.openLine) P.ε j *
              (1 : Matrix (Fin 4) (Fin 4) ℂ) (β fi.1) (α fo.tail))))).const_mul I)
      simp only [ocY, affNum, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hw]
    · simp only [ocD, ocNum, h1, h2, ↓reduceIte]
      exact affPoly_nsNum P Φ α β lor l

/-! ### One resummed term, summed over the flavours -/

variable [Fintype F] [DecidableEq F]

/-- **(T₉′) of one resummed term, summed over the flavours.** -/
theorem jointEnergyFirstIntegrable_ocTerm (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (C : Contraction 1 nA κ) (fi fo : FermionLine C)
    (hκ : ∀ t, t ≠ fo.1.1 → κ t = .gauge) (hzi : ¬ zOf C fi.1) (hzo : ¬ zOf C fo.1)
    (hZ : ∀ x, isZ (zOf C) (C.1.1 x) = isZ (zOf C) x) (hcrit : OCrit C fi fo)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (j : Fin 2) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * (z * ocTerm P Φ D C αOut βIn μ fi fo j f α β lor
        (lineMomentum₂ C pOut pIn kIn ℓ)) := by
  classical
  by_cases hΓ : ∏ t, (if t = fo.1.1 then 1 else
      Wick.vertexFactor P.e 0 0 1 0 1 α β lor 0 0 t) = 0
  · simp only [ocTerm, ocConst, hΓ, mul_zero, zero_mul, Finset.sum_const_zero]
    exact jointEnergyFirstIntegrable_zero_fun'
  have hev := even_nsP_of_ne P.e fo hκ hzo hZ α β lor hΓ
  have hc := card_zSet_eq (C := C) α β
  have hp : (zSet C).card - (nsE α β C).card = nsP α β C := by omega
  obtain ⟨q, hq⟩ := hev
  have hB := hcrit (nsE α β C) (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
    (by rw [hp, hq]; omega) j
  rw [hp] at hB
  obtain ⟨m, hm⟩ : ∃ m, nsP α β C = 2 * m := ⟨q, by omega⟩
  rw [show nsP α β C / 2 = m by omega] at hB
  have h := jointEnergyFirstIntegrable_blockLines Φ rep hrep hPV₁ hPV₂ (rowOf C)
    (extPart C pOut pIn kIn) (ocMs P Φ C fi fo j) (ocD C fi fo (nsE α β C))
    (ocNum P Φ D C α β lor fi fo j) (affPoly_ocNum P Φ D C α β lor fi fo j) (zSet C)
    m (by rw [length_ocMs P Φ C fi fo hzi hzo j]; exact hB) hε
    (fun _ => z * ocConst P C αOut βIn μ fo α β lor * (1 / 16 : ℂ)) (fun _ => rfl)
  refine (congrArg _ (funext fun ℓ => Finset.sum_congr rfl fun f _ => ?_)).mp h
  simp only [← lineMomentum₂_eq_rowMom]
  rw [ocTerm, prod_ocFac P Φ D hε.ne' C α β lor fi fo hzi hzo j (Φ.mass f),
    hm, pow_mul]
  ring

/-! ### The class obligation -/

/-- **The class obligation for a two-loop contraction with one `fermionCt` vertex between two
open-line lines of the same momentum, beside a closed fermion loop**, from the decidable test
`OCrit`. -/
theorem classIntA_of_oc {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (fi fo : FermionLine C) (hs : fi.tail = fo.1) (hct : κ fo.1.1 = .fermionCt)
    (hκ : ∀ t, t ≠ fo.1.1 → κ t = .gauge) (hfi : fi.1 ≠ fo.1) (hfo : fo.tail ≠ fo.1)
    (hzi : ¬ zOf C fi.1) (hzo : ¬ zOf C fo.1) (hrow : rowOf C (.inl fi) = rowOf C (.inl fo))
    (hext : ∀ pOut pIn kIn : Fin 1 → Fin 4 → ℝ, pOut 0 = pIn 0 + kIn 0 →
      extPart C pOut pIn kIn (.inl fi) = extPart C pOut pIn kIn (.inl fo))
    (hC : ClosedShape C (zOf C)) (hL : loopCount C = 2) (hcrit : OCrit C fi fo) :
    ClassIntA C 0 := by
  intro P F _ _ Φ D rep hH pOut pIn kIn hmom αOut βIn μ
  rw [hL]
  simp only [regulatedAmplitude_eq_closed Φ P D hC, contractionAmplitude_zero_eq]
  set z : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹
  have h := jointEnergyFirstIntegrable_sum' Finset.univ fun α _ =>
    jointEnergyFirstIntegrable_sum' Finset.univ fun β _ =>
      jointEnergyFirstIntegrable_sum' Finset.univ fun lor _ =>
        jointEnergyFirstIntegrable_sum' Finset.univ fun j _ =>
          jointEnergyFirstIntegrable_ocTerm P Φ D rep hH.hrep hH.hPV₁ hH.hPV₂ hH.hε C fi fo hκ
            hzi hzo hC.inv hcrit pOut pIn kIn αOut βIn μ α β lor j z
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [sum_comm_five_fc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hk : lineMomentum₂ C pOut pIn kIn ℓ (.inl fi) =
      lineMomentum₂ C pOut pIn kIn ℓ (.inl fo) := by
    rw [lineMomentum₂_eq_rowMom, lineMomentum₂_eq_rowMom, hrow, hext pOut pIn kIn hmom]
  rw [sum_sum_ampTerm_oc P Φ D hH.hε.ne' C fi fo hs hct hκ hfi hfo hzi hzo f pIn kIn _ hk]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### `CB0`: the counterterm on the line from `0` -/

open QED.ChainProof.SetCLinkDeg6 (extPart_of_chord extPart_of_not_chord)
open QED.TwoLoop.Enumeration (lineData loopCount_eq_card)

theorem kCB0_gauge : ∀ t, t ≠ (fv kCB0 1).1 → kCB0 t = .gauge := by decide

/-- The line `0 → 1` into the counterterm vertex `1`. -/
def fiCB0 : FermionLine repCB0 := ⟨fv kCB0 0, by decide +kernel⟩

/-- The line `1 → 2` out of the counterterm vertex `1`. -/
def foCB0 : FermionLine repCB0 := ⟨fv kCB0 1, by decide +kernel⟩

theorem data_CB0 : fiCB0.tail = foCB0.1 ∧ fiCB0.1 ≠ foCB0.1 ∧ foCB0.tail ≠ foCB0.1 ∧
    ¬ zOf repCB0 fiCB0.1 ∧ ¬ zOf repCB0 foCB0.1 ∧
    rowOf repCB0 (.inl fiCB0) = rowOf repCB0 (.inl foCB0) := by
  decide +kernel

theorem chord_CB0 : edgeChord (lineData repCB0) (edgeOf (.inl fiCB0)) = true ∧
    edgeChord (lineData repCB0) (edgeOf (.inl foCB0)) = false ∧
    edgeSide (lineData repCB0) (edgeOf (.inl foCB0)) = {0, 2, 3, 4, 5} := by
  decide +kernel

theorem ext_CB0 : ∀ v,
    ((∃ t : Wick.FermionVertex kCB0, t.1 = v ∧ repCB0.1.1 (.inr t) = .inl 0) ↔ v = 3) ∧
    ((∃ a : Wick.PhotonSlot kCB0, a.1 = v ∧ repCB0.1.2 (.inl 0) = .inr a) ↔ v = 2) ∧
    ((∃ t : Wick.FermionVertex kCB0, t.1 = v ∧ repCB0.1.1 (.inl 0) = .inr t) ↔ v = 0) := by
  decide +kernel

theorem extPart_CB0 (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0) :
    extPart repCB0 pOut pIn kIn (.inl fiCB0) = extPart repCB0 pOut pIn kIn (.inl foCB0) := by
  rw [extPart_of_chord _ _ _ _ chord_CB0.1, extPart_of_not_chord _ _ _ _ chord_CB0.2.1,
    chord_CB0.2.2]
  simp only [Finset.sum_insert (by decide : (0 : Fin 6) ∉ ({2, 3, 4, 5} : Finset (Fin 6))),
    Finset.sum_insert (by decide : (2 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6))),
    Finset.sum_insert (by decide : (3 : Fin 6) ∉ ({4, 5} : Finset (Fin 6))),
    Finset.sum_insert (by decide : (4 : Fin 6) ∉ ({5} : Finset (Fin 6))), Finset.sum_singleton,
    QED.TwoLoop.Insertion.externalMomentum_one_one, (ext_CB0 _).1, (ext_CB0 _).2.1,
    (ext_CB0 _).2.2]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, hmom]
  abel

theorem closedShape_repCB0 : ClosedShape repCB0 (zOf repCB0) :=
  ⟨isZ_zOf_apply repCB0, fun _ ht => not_not.mp ht, ⟨fv kCB0 4, by decide +kernel,
    by decide +kernel⟩⟩

theorem loopCount_repCB0 : loopCount repCB0 = 2 := by
  rw [loopCount_eq_card]
  decide +kernel

theorem oCrit_repCB0 : OCrit repCB0 fiCB0 foCB0 := by decide +kernel

/-- **The class obligation for `CB0`.** -/
theorem classIntA_repCB0 : ClassIntA repCB0 0 := by
  obtain ⟨hs, hfi, hfo, hzi, hzo, hrow⟩ := data_CB0
  exact classIntA_of_oc repCB0 fiCB0 foCB0 hs rfl kCB0_gauge hfi hfo hzi hzo hrow extPart_CB0
    closedShape_repCB0 loopCount_repCB0 oCrit_repCB0

/-! ### `CB1`: the counterterm on the line towards `3` -/

theorem kCB1_gauge : ∀ t, t ≠ (fv kCB1 2).1 → kCB1 t = .gauge := by decide

/-- The line `1 → 2` into the counterterm vertex `2`. -/
def fiCB1 : FermionLine repCB1 := ⟨fv kCB1 1, by decide +kernel⟩

/-- The line `2 → 3` out of the counterterm vertex `2`. -/
def foCB1 : FermionLine repCB1 := ⟨fv kCB1 2, by decide +kernel⟩

theorem data_CB1 : fiCB1.tail = foCB1.1 ∧ fiCB1.1 ≠ foCB1.1 ∧ foCB1.tail ≠ foCB1.1 ∧
    ¬ zOf repCB1 fiCB1.1 ∧ ¬ zOf repCB1 foCB1.1 ∧
    rowOf repCB1 (.inl fiCB1) = rowOf repCB1 (.inl foCB1) := by
  decide +kernel

theorem chord_CB1 : edgeChord (lineData repCB1) (edgeOf (.inl fiCB1)) = false ∧
    edgeChord (lineData repCB1) (edgeOf (.inl foCB1)) = false ∧
    edgeSide (lineData repCB1) (edgeOf (.inl fiCB1)) = {0, 2, 3, 4, 5} ∧
    edgeSide (lineData repCB1) (edgeOf (.inl foCB1)) = {0, 3, 4, 5} := by
  decide +kernel

theorem ext_CB1 :
    ((∃ t : Wick.FermionVertex kCB1, t.1 = 2 ∧ repCB1.1.1 (.inr t) = .inl 0) ↔ False) ∧
    ((∃ a : Wick.PhotonSlot kCB1, a.1 = 2 ∧ repCB1.1.2 (.inl 0) = .inr a) ↔ False) ∧
    ((∃ t : Wick.FermionVertex kCB1, t.1 = 2 ∧ repCB1.1.1 (.inl 0) = .inr t) ↔ False) := by
  decide +kernel

theorem extPart_CB1 (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (_ : pOut 0 = pIn 0 + kIn 0) :
    extPart repCB1 pOut pIn kIn (.inl fiCB1) = extPart repCB1 pOut pIn kIn (.inl foCB1) := by
  rw [extPart_of_not_chord _ _ _ _ chord_CB1.1, extPart_of_not_chord _ _ _ _ chord_CB1.2.1,
    chord_CB1.2.2.1, chord_CB1.2.2.2,
    Finset.sum_insert (by decide : (0 : Fin 6) ∉ ({2, 3, 4, 5} : Finset (Fin 6))),
    Finset.sum_insert (by decide : (2 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6))),
    Finset.sum_insert (by decide : (0 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6))),
    QED.TwoLoop.Insertion.externalMomentum_one_one (C := repCB1) pOut pIn kIn 2]
  simp only [ext_CB1.1, ext_CB1.2.1, ext_CB1.2.2, ite_false, sub_zero, add_zero, zero_add]

theorem closedShape_repCB1 : ClosedShape repCB1 (zOf repCB1) :=
  ⟨isZ_zOf_apply repCB1, fun _ ht => not_not.mp ht, ⟨fv kCB1 4, by decide +kernel,
    by decide +kernel⟩⟩

theorem loopCount_repCB1 : loopCount repCB1 = 2 := by
  rw [loopCount_eq_card]
  decide +kernel

theorem oCrit_repCB1 : OCrit repCB1 fiCB1 foCB1 := by decide +kernel

/-- **The class obligation for `CB1`.** -/
theorem classIntA_repCB1 : ClassIntA repCB1 0 := by
  obtain ⟨hs, hfi, hfo, hzi, hzo, hrow⟩ := data_CB1
  exact classIntA_of_oc repCB1 fiCB1 foCB1 hs rfl kCB1_gauge hfi hfo hzi hzo hrow extPart_CB1
    closedShape_repCB1 loopCount_repCB1 oCrit_repCB1

end QED.ChainProof.SetCLink

end
