/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntFTerm
public import QED.Integration.X0Deg6One

/-!
# A fermion counterterm on the open line beside a closed loop, resummed

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58), for the classes `CB0`, `CB1`. Let `C` be a contraction whose vertices are
`gauge` vertices except one `fermionCt` vertex `t₀` on the open line, with a closed fermion loop
`zOf C`, and let `fi` (ending at `t₀`) and `fo` (leaving `t₀`) be open-line fermion lines of the
same momentum `k`: a doubled line. In an index term of the amplitude at the zero grading with
flavour `f` on the closed loop, the spinor indices `α t₀`, `β t₀` occur only in the propagator
entries of `fi`, `fo` and in the counterterm factor, all at the open-line flavour. The double
sum over them is `i (Y₁ D⁻¹ + Y₂ D⁻²)` at the entry `(β fi.1, α fo.tail)`
(`QED.GradedProof.X0Deg6.sum_sum_ct_entry`), with `Y₁`, `Y₂` affine in `k`: the two variants
`j = 0, 1` of `ocTerm`, products of line factors in which `fo` carries the factor `1` and `fi`
the affine entry with `j + 1` denominators (`sum_sum_ampTerm_oc`). `prod_ocFac` splits the
line factors as `M_f^p` times a product with the denominators `D_{M_f}⁻¹` of the closed loop.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.GradedProof.X0 QED.Graded QED.WickModel QED.ChainProof.SetALink
open QED.GradedProof.X0Deg6 (affNum mergeU mergeV sum_sum_ct_entry sum_sum_resum prod_split_one
  prod_split_two tail_spec eq_of_tail_eq vertexFactor_congr₂)
open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero electronNumerator electronPropagator_apply)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type}

/-! ### The data of the resummed terms -/

/-- `Y₁` (`j = 0`) and `Y₂` (`j = 1`) at the open-line counterterm. -/
noncomputable def ocY (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F) (j : Fin 2)
    (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  affNum (Φ.mass Φ.openLine) k
    (mergeU (P.e ^ 2 * D.d₂ Φ.openLine 0) (P.e ^ 2 * D.dm Φ.openLine 0) (Φ.mass Φ.openLine)
      (Φ.mass Φ.openLine) P.ε j)
    (mergeV (P.e ^ 2 * D.d₂ Φ.openLine 0) (P.e ^ 2 * D.dm Φ.openLine 0) (Φ.mass Φ.openLine)
      (Φ.mass Φ.openLine) P.ε j)

/-- The numerator factor of a line in variant `j`. -/
noncomputable def ocNum (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (C : Contraction 1 nA κ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (fi fo : FermionLine C) (j : Fin 2) (l : Line C) :
    (Fin 4 → ℝ) → ℂ :=
  if l = .inl fo then fun _ => 1
  else if l = .inl fi then fun k => I * ocY P Φ D j k (β fi.1) (α fo.tail)
  else nsNum P Φ C α β lor l

/-- The masses of the denominators of a line off the closed loop in variant `j`. -/
def ocMs (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ) (fi fo : FermionLine C)
    (j : Fin 2) (l : Line C) : List ℝ :=
  if l = .inl fo then [] else if l = .inl fi then List.replicate (j.val + 1) (Φ.mass Φ.openLine)
  else nsMs P Φ C l

/-- The line factor of variant `j`, mass `M` on the closed loop. -/
noncomputable def ocFac (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (C : Contraction 1 nA κ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (fi fo : FermionLine C) (j : Fin 2) (M : ℝ) (l : Line C)
    (k : Fin 4 → ℝ) : ℂ :=
  if l = .inl fo then 1
  else if l = .inl fi then I * ocY P Φ D j k (β fi.1) (α fo.tail) *
    dProd P.ε (List.replicate (j.val + 1) (Φ.mass Φ.openLine)) k
  else nsFac P Φ C α β lor M l k

/-- The constant part of a resummed term: the constraints and the `gauge` vertex factors. -/
noncomputable def ocConst (P : Params) (C : Contraction 1 nA κ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) (fo : FermionLine C) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) : ℂ :=
  extI C αOut βIn μ α β lor *
    ∏ t, if t = fo.1.1 then 1 else Wick.vertexFactor P.e 0 0 1 0 1 α β lor 0 0 t

/-- **A resummed term**: variant `j`, flavour `f` on the closed loop. -/
noncomputable def ocTerm (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (C : Contraction 1 nA κ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4)
    (fi fo : FermionLine C) (j : Fin 2) (f : F) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (k : Line C → Fin 4 → ℝ) : ℂ :=
  ocConst P C αOut βIn μ fo α β lor *
    ((1 / 16 : ℂ) * ∏ l, ocFac P Φ D C α β lor fi fo j (Φ.mass f) l (k l))

/-! ### The resummation -/

theorem flOf_open (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ) (fo : FermionLine C)
    (hz : ¬ zOf C fo.1) (f : F) : flOf Φ (closedFlavoring Φ (zOf C) f) fo.1.1 = Φ.openLine := by
  unfold flOf
  simp [fo.1.2, closedFlavoring, hz]

/-- The merged entry is the sum of the two variants at the line `fi`. -/
theorem sum_ocFac_fi (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (C : Contraction 1 nA κ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (fi fo : FermionLine C) (hne : fi ≠ fo) (M : ℝ)
    (k : Fin 4 → ℝ) :
    ∑ j : Fin 2, ocFac P Φ D C α β lor fi fo j M (.inl fi) k =
      I * (ocY P Φ D 0 k (β fi.1) (α fo.tail) * (propDenom (Φ.mass Φ.openLine) P.ε k)⁻¹ +
        ocY P Φ D 1 k (β fi.1) (α fo.tail) * ((propDenom (Φ.mass Φ.openLine) P.ε k)⁻¹ *
          (propDenom (Φ.mass Φ.openLine) P.ε k)⁻¹)) := by
  have h : (Sum.inl fi : Line C) ≠ .inl fo := fun h => hne (Sum.inl_injective h)
  simp only [ocFac, h, ↓reduceIte, Fin.sum_univ_two, List.replicate, dProd,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

/-- **The resummation at the open-line counterterm.** -/
theorem sum_sum_ampTerm_oc (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (hε : P.ε ≠ 0) (C : Contraction 1 nA κ) (fi fo : FermionLine C) (hs : fi.tail = fo.1)
    (hct : κ fo.1.1 = .fermionCt) (hκ : ∀ t, t ≠ fo.1.1 → κ t = .gauge) (hfi : fi.1 ≠ fo.1)
    (hfo : fo.tail ≠ fo.1) (hzi : ¬ zOf C fi.1) (hzo : ¬ zOf C fo.1) (f : F)
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (hk : k (.inl fi) = k (.inl fo)) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    ∑ α, ∑ β, ∑ lor, ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn k αOut βIn μ α β lor =
      ∑ α, ∑ β, ∑ lor, ∑ j : Fin 2, ocTerm P Φ D C αOut βIn μ fi fo j f α β lor k := by
  classical
  have hne : fi ≠ fo := fun h => hfi (by rw [h])
  have hne' : (Sum.inl fi : Line C) ≠ .inl fo := fun h => hne (Sum.inl_injective h)
  set t₀ := fo.1.1 with ht₀
  set Mo := Φ.mass Φ.openLine with hMo
  set δ₂ := P.e ^ 2 * D.d₂ Φ.openLine 0 with hδ₂
  set δm := P.e ^ 2 * D.dm Φ.openLine 0 with hδm
  set kf := k (.inl fo) with hkf
  set X := (δ₂ : ℂ) • Dirac.slash kf + ((δm * Mo : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
    with hX
  set Q : (Wick.FermionVertex κ → Fin 4) → (Wick.FermionVertex κ → Fin 4) →
      (Wick.PhotonSlot κ → Fin 4) → ℂ := fun α β lor => extI C αOut βIn μ α β lor *
    ((∏ t, if t = t₀ then 1 else Wick.vertexFactor P.e 0 0 1 0 1 α β lor 0 0 t) *
      ∏ l, if l = .inl fo then 1 else if l = .inl fi then 1 else
        nsFac P Φ C α β lor (Φ.mass f) l (k l)) with hQ
  set G : (Wick.FermionVertex κ → Fin 4) → (Wick.FermionVertex κ → Fin 4) → Fin 4 → Fin 4 → ℂ :=
    fun α β a b => (1 / I) * QED.OneLoop.electronPropagator Mo P.ε kf (β fi.1) a *
      (-I * X a b) * ((1 / I) * QED.OneLoop.electronPropagator Mo P.ε kf b (α fo.tail)) with hG
  set Mrg : (Wick.FermionVertex κ → Fin 4) → (Wick.FermionVertex κ → Fin 4) → ℂ :=
    fun α β => I * (ocY P Φ D 0 kf (β fi.1) (α fo.tail) * (propDenom Mo P.ε kf)⁻¹ +
      ocY P Φ D 1 kf (β fi.1) (α fo.tail) * ((propDenom Mo P.ε kf)⁻¹ *
        (propDenom Mo P.ε kf)⁻¹)) with hMrg
  have hzl : ∀ fl : FermionLine C, ¬ zOf C fl.1 → isZL C (.inl fl) = false := fun fl h => by
    simp [isZL, h]
  -- the index term as `Q · G`
  have hterm : ∀ α β lor, ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn k αOut βIn μ
      α β lor = Q α β lor * G α β (α fo.1) (β fo.1) := fun α β lor => by
    rw [ampTerm_eq_fac, prod_split_one _ t₀, prod_split_two _ hne']
    have hv : vf0 P D (flOf Φ (closedFlavoring Φ (zOf C) f) t₀)
        (Φ.mass (flOf Φ (closedFlavoring Φ (zOf C) f) t₀)) α β lor (psiMomentum₂ C pIn k)
        (photonMomentum₂ C kIn k) t₀ = -I * X (α fo.1) (β fo.1) := by
      unfold vf0
      rw [ht₀, vertexFactor_ct_eq _ _ _ _ _ _ _ _ _ _ _ fo.1 hct, psiMomentum₂_fo,
        flOf_open Φ C fo hzo f]
    have hv' : ∀ t, (if t = t₀ then 1 else vf0 P D (flOf Φ (closedFlavoring Φ (zOf C) f) t)
        (Φ.mass (flOf Φ (closedFlavoring Φ (zOf C) f) t)) α β lor (psiMomentum₂ C pIn k)
        (photonMomentum₂ C kIn k) t) =
        if t = t₀ then 1 else Wick.vertexFactor P.e 0 0 1 0 1 α β lor 0 0 t := fun t => by
      split_ifs with h
      · rfl
      · unfold vf0
        exact vertexFactor_gauge_eq _ _ _ _ _ _ _ _ _ _ _ t (hκ t h)
    have h1 : nsFac P Φ C α β lor (Φ.mass f) (.inl fi) (k (.inl fi)) =
        (1 / I) * QED.OneLoop.electronPropagator Mo P.ε kf (β fi.1) (α fo.1) := by
      simp only [nsFac, hzl fi hzi, Bool.false_eq_true, ↓reduceIte, hk, hs, hkf, hMo]
    have h2 : nsFac P Φ C α β lor (Φ.mass f) (.inl fo) (k (.inl fo)) =
        (1 / I) * QED.OneLoop.electronPropagator Mo P.ε kf (β fo.1) (α fo.tail) := by
      simp only [nsFac, hzl fo hzo, Bool.false_eq_true, ↓reduceIte, hkf, hMo]
    rw [hv, h1, h2, Finset.prod_congr rfl fun t _ => hv' t]
    simp only [hQ, hG]
    ring
  -- invariance under the indices of `fo.1`
  have hfo1 : ∀ fl : FermionLine C, fl ≠ fo → fl.1 ≠ fo.1 := fun fl hf h => hf (Subtype.ext h)
  have hfo2 : ∀ fl : FermionLine C, fl ≠ fi → fl.tail ≠ fo.1 := fun fl hf h =>
    hf (eq_of_tail_eq (h.trans hs.symm))
  have hQu : ∀ α β lor a b, Q (Function.update α fo.1 a) (Function.update β fo.1 b) lor =
      Q α β lor := fun α β lor a b => by
    have hA : ∀ i t, C.1.1 (.inl i) = .inr t → t ≠ fo.1 := fun i t h ht => by
      have := (tail_spec fi).trans (by rw [hs, ← ht, ← h])
      exact absurd (C.1.1.injective this) (by simp)
    have hB : ∀ t i, C.1.1 (.inr t) = .inl i → t ≠ fo.1 := fun t i h ht => by
      have := tail_spec fo
      rw [← ht, h] at this
      exact absurd this (by simp)
    have hi : extI C αOut βIn μ (Function.update α fo.1 a) (Function.update β fo.1 b) lor =
        extI C αOut βIn μ α β lor := by
      unfold extI
      congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun i t h => ?_, fun t i h => ?_, h3⟩
        · simpa [Function.update_of_ne (hA i t h)] using h1 i t h
        · simpa [Function.update_of_ne (hB t i h)] using h2 t i h
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun i t h => ?_, fun t i h => ?_, h3⟩
        · simpa [Function.update_of_ne (hA i t h)] using h1 i t h
        · simpa [Function.update_of_ne (hB t i h)] using h2 t i h
    simp only [hQ, hi]
    congr 2
    · refine Finset.prod_congr rfl fun t _ => ?_
      split_ifs with ht
      · rfl
      · refine vertexFactor_congr₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun p => ?_) (fun p => ?_)
        · exact Function.update_of_ne (fun h => ht (by rw [ht₀, ← h])) _ _
        · exact Function.update_of_ne (fun h => ht (by rw [ht₀, ← h])) _ _
    · refine Finset.prod_congr rfl fun l _ => ?_
      split_ifs with h1 h2
      · rfl
      · rfl
      · rcases l with fl | g
        · have h1' : fl ≠ fo := fun h => h1 (by rw [h])
          have h2' : fl ≠ fi := fun h => h2 (by rw [h])
          simp only [nsFac, Function.update_of_ne (hfo1 fl h1'),
            Function.update_of_ne (hfo2 fl h2')]
        · rfl
  have hGu : ∀ α β a b, G (Function.update α fo.1 a) (Function.update β fo.1 b) = G α β :=
    fun α β a b => by
      simp only [hG, Function.update_of_ne hfi, Function.update_of_ne hfo]
  have hMu : ∀ α β a b, Mrg (Function.update α fo.1 a) (Function.update β fo.1 b) = Mrg α β :=
    fun α β a b => by
      simp only [hMrg, Function.update_of_ne hfi, Function.update_of_ne hfo]
  -- the resummed sum
  have h0 : ∑ α, ∑ β, ∑ lor, ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn k αOut βIn μ
      α β lor = ∑ α, ∑ β, (∑ lor, Q α β lor) * G α β (α fo.1) (β fo.1) := by
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun lor _ => hterm α β lor
  have h1 := sum_sum_resum fo.1 (fun α β a b => (∑ lor, Q α β lor) * G α β a b)
    (fun α β _ _ => (∑ lor, Q α β lor) * ((1 / 16 : ℂ) * Mrg α β))
    (fun α β a b => by funext a' b'; simp only [hQu, hGu])
    (fun α β a b => by funext a' b'; simp only [hQu, hMu])
    (fun α β => by
      simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      have h := sum_sum_ct_entry δ₂ δm Mo Mo P.ε hε kf (β fi.1) (α fo.tail)
      simp only [hG, hMrg, ocY]
      rw [h]
      simp only [nsmul_eq_mul]
      push_cast
      ring)
  rw [h0, h1]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun lor _ => ?_
  have hl : ∀ j, ∏ l, ocFac P Φ D C α β lor fi fo j (Φ.mass f) l (k l) =
      ocFac P Φ D C α β lor fi fo j (Φ.mass f) (.inl fi) (k (.inl fi)) *
        ∏ l, if l = .inl fo then 1 else if l = .inl fi then 1 else
          nsFac P Φ C α β lor (Φ.mass f) l (k l) := fun j => by
    rw [prod_split_two _ hne']
    simp only [ocFac, ↓reduceIte, mul_one]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    split_ifs <;> rfl
  have hM : Mrg α β = ∑ j : Fin 2, ocFac P Φ D C α β lor fi fo j (Φ.mass f) (.inl fi)
      (k (.inl fi)) := by
    rw [sum_ocFac_fi P Φ D C α β lor fi fo hne, hk]
  simp only [ocTerm, ocConst, hl, hQ, hM, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### The line factors -/

/-- **A line factor of a variant, split.** -/
theorem ocFac_eq (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F) (hε : P.ε ≠ 0)
    (C : Contraction 1 nA κ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (fi fo : FermionLine C) (hzi : ¬ zOf C fi.1)
    (hzo : ¬ zOf C fo.1) (j : Fin 2) (M : ℝ) (l : Line C) (k : Fin 4 → ℝ) :
    ocFac P Φ D C α β lor fi fo j M l k =
      (if isZL C l = true ∧ sameB α β l = true then (M : ℂ) else 1) *
        (ocNum P Φ D C α β lor fi fo j l k * dProd P.ε (ocMs P Φ C fi fo j l) k) *
        (if isZL C l = true then (propDenom M P.ε k)⁻¹ else 1) := by
  by_cases h1 : l = .inl fo
  · subst h1
    simp [ocFac, ocNum, ocMs, isZL, hzo, dProd]
  · by_cases h2 : l = .inl fi
    · subst h2
      simp [ocFac, ocNum, ocMs, isZL, hzi, h1]
    · simp only [ocFac, ocNum, ocMs, h1, h2, ↓reduceIte]
      exact nsFac_eq P Φ hε α β lor M l k

/-- **The product of the line factors of a variant.** -/
theorem prod_ocFac (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F) (hε : P.ε ≠ 0)
    (C : Contraction 1 nA κ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (fi fo : FermionLine C) (hzi : ¬ zOf C fi.1)
    (hzo : ¬ zOf C fo.1) (j : Fin 2) (M : ℝ) (k : Line C → Fin 4 → ℝ) :
    ∏ l, ocFac P Φ D C α β lor fi fo j M l (k l) =
      (M : ℂ) ^ nsP α β C *
        ((∏ l, ocNum P Φ D C α β lor fi fo j l (k l) * dProd P.ε (ocMs P Φ C fi fo j l) (k l)) *
          ∏ l ∈ zSet C, (propDenom M P.ε (k l))⁻¹) := by
  classical
  simp only [ocFac_eq P Φ D hε C α β lor fi fo hzi hzo j M _ (k _), Finset.prod_mul_distrib]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Finset.prod_ite,
    Finset.prod_const_one, mul_one]
  have hc : (Finset.univ.filter fun l : Line C => isZL C l = true ∧ sameB α β l = true).card =
      nsP α β C := by
    rw [nsP, zSet, Finset.filter_filter]
  rw [hc]
  simp only [zSet]
  ring

end QED.ChainProof.SetCLink

end
