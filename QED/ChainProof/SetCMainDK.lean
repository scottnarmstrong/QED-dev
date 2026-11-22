/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainDUnit

/-!
# Set (c), the `δ₃` classes: the longitudinal part as a chain in the class routing

Helper level for the open links `QED.ChainProof.SetCMain.DKLimLink`, `DKCovLink` of the
longitudinal (`k^a k^b`) part `QED.ChainProof.SetCMain.dKIntegrand` of the 24 classes
`repD i s`. As for the transverse part (`QED/ChainProof/SetCMainDChain.lean`), the index sum is
evaluated as an open-line chain of the class representative of `repB i`; the two `photonCt`
slots now contract the element momentum `q` into the vertices `ctEndA`, `ctEndB` through the
Pauli–Villars photon factors, `∑ₓ η_{ux} qₓ = (1/i)(Λ² - m_γ²) q_u` (`lowD`, `sum_eta_mul`):

`∑ extI · ctKD · gV · lineProd = (i/2) δ₃ ((1/i)(Λ² - m_γ²))² · (ie)⁵ (1/i)⁴ · ∏ dProd ·
  ∑_l [l_e = μ] q_{l_a} q_{l_b} η_{l_c l_d} (γ^{l₄} E₃ γ^{l₃} E₂ γ^{l₂} E₁ γ^{l₁} E₀ γ^{l₀})`.

* `dKTerm`, `dK_term_eq`, `sum_dKTerm`; **`dK_repD_chain`**: the twenty-four orbits;
* `kChainD`, `dKUnitIntegrandD`, `wKD`; **`dKIntegrand_repD_eq_unit`**: with the change of loop
  momenta of `QED/ChainProof/SetCMainDUnit.lean`, the integrand is `wKD` times the chain
  `kChainD` (element momentum `elemMom` of the unit) over the ten denominators of the unit with
  two unscaled extra lines `m_γ`, `Λ`; **`dK_repD_value`**: the same for the values.

The numerator has degree six (four electron numerators and `q_{l_a} q_{l_b}`); the Ward
reductions to the parametric engine (degree at most four) are not in this file.
-/

@[expose] public section
open Complex Matrix
open QED.WickModel (Params Contraction FermionLine PhotonLine Line)

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.Enumeration QED.ChainProof.SetCLink QED.ChainProof.SetALink
open QED.GradedProof.X0 QED.TwoLoop.LimitCovariance
open QED.TwoLoop.Bridge (electronNumerator extMomenta)
open QED.ChainProof.Enum (pc)
open QED.ChainProof.SetCUnitM
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix pvLines)
open QED.WickModel (lineMomentum₂ photonMomentum₂)

variable {F : Type}

/-- The lowered components `q_u = g_{uu} q^u` of a momentum, as complex numbers. -/
noncomputable def lowD (q : Fin 4 → ℝ) (u : Fin 4) : ℂ := ((Minkowski.metric u u * q u : ℝ) : ℂ)

theorem sum_eta_mul (P : Params) (q : Fin 4 → ℝ) (u : Fin 4) :
    ∑ x, pvEta P u x * (q x : ℂ) = (1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * lowD q u := by
  simp only [pvEta, lowD, Minkowski.metric, Fin.sum_univ_four]
  fin_cases u <;> simp
  ring

/-- The summand of the longitudinal part after the change of index variables. -/
noncomputable def dKTerm (P : Params) (m δ₃ : ℝ) (q : Fin 4 → ℝ) (K : Fin 4 → Fin 4 → ℝ)
    (Dens : ℂ) (a b c d e : Fin 5) (αOut βIn μ : Fin 1 → Fin 4)
    (α β : Wick.FermionVertex (gauges 5) → Fin 4) (L : Fin 5 ⊕ Fin 2 → Fin 4) : ℂ :=
  (if α (fv5 4) = αOut 0 ∧ β (fv5 0) = βIn 0 ∧ L (.inl e) = μ 0 then 1 else 0) *
    ((I / 2) * (δ₃ : ℂ) * ((q (L (.inr 0)) : ℂ) * (q (L (.inr 1)) : ℂ))) *
    ((∏ u : Fin 5, I * P.e * Dirac.gamma (L (.inl u)) (α (fv5 u)) (β (fv5 u))) *
      ((∏ i : Fin 4, (1 / I) * electronNumerator m (K i) (β (fv5 i.succ)) (α (fv5 i.castSucc))) *
        (pvEta P (L (.inl a)) (L (.inr 0)) * pvEta P (L (.inr 1)) (L (.inl b)) *
          pvEta P (L (.inl c)) (L (.inl d))) * Dens))

theorem dK_term_eq (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) (C : Contraction 1 1 kD)
    (αOut βIn μ : Fin 1 → Fin 4) (q : Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (line : Fin 4 → FermionLine C)
    (hfl : ∀ g : FermionLine C → ℂ, ∏ f, g f = g (line 0) * g (line 1) * g (line 2) * g (line 3))
    (hval : ∀ i, (line i).1 = fvD (Fin.rev i.succ))
    (htail : ∀ i, (line i).tail = fvD (Fin.rev i.castSucc))
    (gA gB gC : PhotonLine C) (hph : ∀ h : PhotonLine C → ℂ, ∏ g, h g = h gA * h gB * h gC)
    (a b c d e : Fin 5)
    (hA : (gA.1 = plD (Fin.rev a) ∧ gA.head = pc kD 5 0) ∨
      (gA.1 = pc kD 5 0 ∧ gA.head = plD (Fin.rev a)))
    (hB : (gB.1 = pc kD 5 1 ∧ gB.head = plD (Fin.rev b)) ∨
      (gB.1 = plD (Fin.rev b) ∧ gB.head = pc kD 5 1))
    (hC : (gC.1 = plD (Fin.rev c) ∧ gC.head = plD (Fin.rev d)) ∨
      (gC.1 = plD (Fin.rev d) ∧ gC.head = plD (Fin.rev c)))
    (hout : ∀ (i : Fin 1) t, C.1.1 (.inl i) = .inr t ↔ t = fvD 0)
    (hin : ∀ t (i : Fin 1), C.1.1 (.inr t) = .inl i ↔ t = fvD 4)
    (hext : ∀ (j : Fin 1) x, C.1.2 (.inl j) = .inr x ↔ x = plD (Fin.rev e))
    (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4) :
    extI C αOut βIn μ α β lor * (ctKD δ₃ lor q *
        (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k)) =
      dKTerm P (Φ.mass Φ.openLine) δ₃ q (fun i => k (.inl (line i)))
        (∏ l, dProd P.ε (dMs P Φ l) (k l)) a b c d e αOut βIn μ (α ∘ eFV.symm) (β ∘ eFV.symm)
        (lor ∘ ePS.symm) := by
  have hPA : pvEta P (lor gA.1) (lor gA.head) =
      pvEta P (lor (plD (Fin.rev a))) (lor (pc kD 5 0)) := by
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]; exact pvEta_symm _ _ _
  have hPB : pvEta P (lor gB.1) (lor gB.head) =
      pvEta P (lor (pc kD 5 1)) (lor (plD (Fin.rev b))) := by
    rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]; exact pvEta_symm _ _ _
  have hPC : pvEta P (lor gC.1) (lor gC.head) =
      pvEta P (lor (plD (Fin.rev c))) (lor (plD (Fin.rev d))) := by
    rcases hC with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]; exact pvEta_symm _ _ _
  have hx : extI C αOut βIn μ α β lor =
      if α (fvD 0) = αOut 0 ∧ β (fvD 4) = βIn 0 ∧ lor (plD (Fin.rev e)) = μ 0 then 1 else 0 := by
    unfold extI
    simp only [hout, hin, hext, forall_eq, Fin.forall_fin_one]
  have hL : lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k =
      (∏ i : Fin 4, (1 / I) * electronNumerator (Φ.mass Φ.openLine) (k (.inl (line i)))
          (β (fvD (Fin.rev i.succ))) (α (fvD (Fin.rev i.castSucc)))) *
        (pvEta P (lor (plD (Fin.rev a))) (lor (pc kD 5 0)) *
          pvEta P (lor (pc kD 5 1)) (lor (plD (Fin.rev b))) *
          pvEta P (lor (plD (Fin.rev c))) (lor (plD (Fin.rev d)))) *
        ∏ l, dProd P.ε (dMs P Φ l) (k l) := by
    unfold lineProd
    rw [Finset.prod_mul_distrib, Fintype.prod_sum_type]
    rw [hfl (fun f => dNum P Φ α β lor (.inl f) (k (.inl f))),
      hph (fun g => dNum P Φ α β lor (.inr g) (k (.inr g)))]
    simp only [dNum, Fin.prod_univ_four, hval, htail]
    rw [← hPA, ← hPB, ← hPC]
    rfl
  rw [hx, hL, gV_eq]
  obtain ⟨r0, r1, r2, r3, r4⟩ := rev_five
  obtain ⟨s0, s1, s2, s3, c0, c1, c2, c3⟩ := succ_cast_four
  unfold dKTerm ctKD
  simp only [Function.comp_apply, Fin.prod_univ_five, Fin.prod_univ_four, eFV_symm_apply,
    ePS_symm_inl, ePS_symm_inr, fv5_val_D, r0, r1, r2, r3, r4, s0, s1, s2, s3, c0, c1, c2, c3]
  ring

theorem sum_dKTerm (P : Params) (m δ₃ : ℝ) (q : Fin 4 → ℝ) (K : Fin 4 → Fin 4 → ℝ)
    (Dens : ℂ) (a b c d e : Fin 5) (αOut βIn μ : Fin 1 → Fin 4) :
    ∑ α, ∑ β, ∑ L, dKTerm P m δ₃ q K Dens a b c d e αOut βIn μ α β L =
      ((I / 2) * (δ₃ : ℂ) * ((1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) ^ 2) *
        ((I * P.e) ^ 5 * (1 / I) ^ 4) * Dens *
        ∑ l : Fin 5 → Fin 4, kron (μ 0) (l e) * lowD q (l a) * lowD q (l b) *
          pvEta P (l c) (l d) *
          openChain (fun u => Dirac.gamma (l u)) (fun i => electronNumerator m (K i))
            (αOut 0) (βIn 0) := by
  set G : (Fin 5 → Fin 4) → Fin 5 → Matrix (Fin 4) (Fin 4) ℂ := fun l u => Dirac.gamma (l u)
  set E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun i => electronNumerator m (K i)
  have hfac : ∀ α β l x y, dKTerm P m δ₃ q K Dens a b c d e αOut βIn μ α β (Sum.elim l ![x, y]) =
      (kron (μ 0) (l e) * ((I / 2) * (δ₃ : ℂ)) * (pvEta P (l a) x * (q x : ℂ)) *
        ((q y : ℂ) * pvEta P y (l b)) * pvEta P (l c) (l d) * ((I * P.e) ^ 5 * (1 / I) ^ 4) *
          Dens) *
        ((if α (fv5 4) = αOut 0 ∧ β (fv5 0) = βIn 0 then (1 : ℂ) else 0) *
          (G l 0 (α (fv5 0)) (β (fv5 0)) * G l 1 (α (fv5 1)) (β (fv5 1)) *
            G l 2 (α (fv5 2)) (β (fv5 2)) * G l 3 (α (fv5 3)) (β (fv5 3)) *
            G l 4 (α (fv5 4)) (β (fv5 4)) *
            (E 0 (β (fv5 1)) (α (fv5 0)) * E 1 (β (fv5 2)) (α (fv5 1)) *
              E 2 (β (fv5 3)) (α (fv5 2)) * E 3 (β (fv5 4)) (α (fv5 3))))) := by
    intro α β l x y
    obtain ⟨s0, s1, s2, s3, c0, c1, c2, c3⟩ := succ_cast_four
    unfold dKTerm
    rw [ite_and_three]
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_five, Fin.prod_univ_four, kron, G, E,
      Matrix.cons_val_zero, Matrix.cons_val_one, s0, s1, s2, s3, c0, c1, c2, c3]
    by_cases h : l e = μ 0 <;> simp only [h, ite_true, ite_false] <;> ring
  set B : (Wick.FermionVertex (gauges 5) → Fin 4) → (Wick.FermionVertex (gauges 5) → Fin 4) →
      (Fin 5 → Fin 4) → ℂ := fun α β l =>
    (if α (fv5 4) = αOut 0 ∧ β (fv5 0) = βIn 0 then (1 : ℂ) else 0) *
      (G l 0 (α (fv5 0)) (β (fv5 0)) * G l 1 (α (fv5 1)) (β (fv5 1)) *
        G l 2 (α (fv5 2)) (β (fv5 2)) * G l 3 (α (fv5 3)) (β (fv5 3)) *
        G l 4 (α (fv5 4)) (β (fv5 4)) *
        (E 0 (β (fv5 1)) (α (fv5 0)) * E 1 (β (fv5 2)) (α (fv5 1)) *
          E 2 (β (fv5 3)) (α (fv5 2)) * E 3 (β (fv5 4)) (α (fv5 3)))) with hB
  set A : (Fin 5 → Fin 4) → ℂ := fun l => ∑ x : Fin 4, ∑ y : Fin 4,
    kron (μ 0) (l e) * ((I / 2) * (δ₃ : ℂ)) * (pvEta P (l a) x * (q x : ℂ)) *
      ((q y : ℂ) * pvEta P y (l b)) * pvEta P (l c) (l d) * ((I * P.e) ^ 5 * (1 / I) ^ 4) *
        Dens with hA
  have h1 : ∀ α β, ∑ L, dKTerm P m δ₃ q K Dens a b c d e αOut βIn μ α β L =
      ∑ l, A l * B α β l := fun α β => by
    rw [sum_sumArrow]
    simp only [hfac, hA, hB, Finset.sum_mul]
  have h2 : ∀ l, ∑ α, ∑ β, B α β l = openChain (G l) E (αOut 0) (βIn 0) := fun l =>
    openSpinSum (G l) E (αOut 0) (βIn 0)
  have h3 : ∀ l, A l = ((I / 2) * (δ₃ : ℂ) * ((1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) ^ 2) *
      ((I * P.e) ^ 5 * (1 / I) ^ 4) * Dens *
        (kron (μ 0) (l e) * lowD q (l a) * lowD q (l b) * pvEta P (l c) (l d)) := fun l => by
    have h : A l = (kron (μ 0) (l e) * ((I / 2) * (δ₃ : ℂ)) * pvEta P (l c) (l d) *
        ((I * P.e) ^ 5 * (1 / I) ^ 4) * Dens) *
        ((∑ x, pvEta P (l a) x * (q x : ℂ)) * ∑ y, pvEta P (l b) y * (q y : ℂ)) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [pvEta_symm P y (l b)]
      ring
    rw [h, sum_eta_mul, sum_eta_mul]
    ring
  calc ∑ α, ∑ β, ∑ L, dKTerm P m δ₃ q K Dens a b c d e αOut βIn μ α β L
      = ∑ α, ∑ l, ∑ β, A l * B α β l := Finset.sum_congr rfl fun α _ => by
        simp only [h1]
        exact Finset.sum_comm
    _ = ∑ l, A l * ∑ α, ∑ β, B α β l := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = _ := by
        simp only [h2, h3, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [G, E]
        ring

/-- **The longitudinal part of `repD i s` as an open-line chain** in the class labels: the
`photonCt` slots contract the element momentum into the vertices `ctEndA`, `ctEndB`. -/
theorem dK_repD_chain (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) (i : Fin 12) (s : Fin 2)
    (αOut βIn μ : Fin 1 → Fin 4) (q : Fin 4 → ℝ) (k : Line (repD i s) → Fin 4 → ℝ) :
    ∑ α, ∑ β, ∑ lor, extI (repD i s) αOut βIn μ α β lor * (ctKD δ₃ lor q *
        (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k)) =
      ((I / 2) * (δ₃ : ℂ) * ((1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) ^ 2) *
        ((I * P.e) ^ 5 * (1 / I) ^ 4) * (∏ l, dProd P.ε (dMs P Φ l) (k l)) *
        ∑ l : Fin 5 → Fin 4, kron (μ 0) (l (Fin.rev (skE i))) * lowD q (l (ctEndA i s)) *
          lowD q (l (ctEndB i s)) * pvEta P (l (Fin.rev (skR i))) (l (Fin.rev (skT i))) *
          openChain (fun u => Dirac.gamma (l u))
            (fun j => electronNumerator (Φ.mass Φ.openLine) (k (.inl (lineRD i s j))))
            (αOut 0) (βIn 0) := by
  obtain ⟨hA, hB, hC⟩ := photD_ends i s
  obtain ⟨hout, hin, hext⟩ := repD_ext i s
  simp only [dK_term_eq P Φ δ₃ (repD i s) αOut βIn μ q k (lineRD i s) (prod_lineRD i s)
    (fun _ => rfl) (lineRD_tail i s) _ _ _ (prod_photD i s) _ _ _ _ _ hA hB hC hout hin hext]
  rw [← sum_dKTerm]
  refine Fintype.sum_equiv (Equiv.arrowCongr eFV (Equiv.refl _)) _ _ fun α => ?_
  refine Fintype.sum_equiv (Equiv.arrowCongr eFV (Equiv.refl _)) _ _ fun β => ?_
  exact Fintype.sum_equiv (Equiv.arrowCongr ePS (Equiv.refl _)) _ _ fun lor => rfl


/-! ### The longitudinal part in the class routing -/

theorem lowD_neg (q : Fin 4 → ℝ) (u : Fin 4) : lowD (-q) u = -lowD q u := by
  simp [lowD]

/-- The longitudinal chain in the class routing: the element momentum contracted into the
vertices `a`, `b`, the photon line `c — d`, the external photon at `e`. -/
noncomputable def kChainD (c : Class5) (P : Params) (σ : Fin 8) (e a b c' d : Fin 5)
    (p p' : Fin 4 → ℝ) (μ α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ l : Fin 5 → Fin 4, kron μ (l e) * lowD (elemMom c σ p p' ℓ) (l a) *
    lowD (elemMom c σ p p' ℓ) (l b) * pvEta P (l c') (l d) *
    openChain (fun u => Dirac.gamma (l u)) (fun j => electronNumerator P.m
      (lineMomentum (castLoopMatrix (class5LoopMatrix c)) (extMomenta c p p')
        (Fin.castLE (by omega) j) ℓ)) α β

/-- The integrand of the longitudinal part of `repD i s` in the class routing, without the
constant `wKD`: the chain `kChainD` over the ten denominators of the unit. -/
noncomputable def dKUnitIntegrandD (i : Fin 12) (s : Fin 2) (P : Params) (M : Fin (2 + 8) → ℝ)
    (ε : ℝ) (p p' : Fin 4 → ℝ) (μ α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  QED.TwoLoop.ClassLimit.twoLoopNorm * ((I * P.e) ^ 5 * (1 / I) ^ 4) *
    kChainD (repBClass i) P (repBSlot i) (Fin.rev (skE i)) (ctEndA i s) (ctEndB i s)
      (Fin.rev (skR i)) (Fin.rev (skT i)) p p' μ α β ℓ *
    ∏ k, (lineDenom (unitMMatrix (repBClass i) (repBSlot i) ![1, 1])
      (unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p') M ε k ℓ)⁻¹

/-- The constant of the longitudinal part: `(i/2) δ₃ ((1/i)(Λ² - m_γ²))²`. -/
noncomputable def wKD (P : Params) (δ₃ : ℝ) : ℂ :=
  (I / 2) * (δ₃ : ℂ) * ((1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) ^ 2

theorem photonMomentum₂_repD_pm (i : Fin 12) (s : Fin 2) (p p' : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    photonMomentum₂ (repD i s) (fun _ => p' - p)
        (lineMomentum₂ (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ) (pc kD 5 0) =
        elemMom (repBClass i) (repBSlot i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) ∨
      photonMomentum₂ (repD i s) (fun _ => p' - p)
        (lineMomentum₂ (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ) (pc kD 5 0) =
        -elemMom (repBClass i) (repBSlot i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) := by
  have he : elemMom (repBClass i) (repBSlot i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) =
      mvReal ℓ p (p' - p) (classVecD (repBClass i) (chgMD i) (chgAD i) (pvLines (repBSlot i))) :=
    lineMomentum_chgD _ _ _ p p' _ ℓ
  rw [photonMomentum₂_eq_pmv _ _ _ _ (by simp), he]
  rcases (mv_repD_photon i s).2.2.2 with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, map_neg])

/-- **The longitudinal part of `repD i s` in the class routing**: at every loop momentum, the
integrand is `wKD` times `dKUnitIntegrandD` at the changed loop momenta. -/
theorem dKIntegrand_repD_eq_unit (Q P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (hm : Φ.mass Φ.openLine = P.m) (he : P.e = Q.e) (hγ : P.mγ = Q.mγ)
    (hΛ : P.Λ = Q.Λ) (δ₃ : ℝ) (i : Fin 12) (s : Fin 2) (p p' : Fin 4 → ℝ) (μ α β : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    dKIntegrand Q Φ δ₃ (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
        (fun _ => β) (fun _ => μ) ℓ =
      wKD Q δ₃ * dKUnitIntegrandD i s P (unitMMasses P.m Q.mγ Q.Λ Q.mγ Q.Λ ![Q.mγ, Q.Λ]) Q.ε
        p p' μ α β (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) := by
  unfold dKIntegrand
  rw [dK_repD_chain, prod_dProd_repD]
  unfold dKUnitIntegrandD kChainD
  rw [prod_lineDenom_unitM_two]
  have hE : (fun j => electronNumerator P.m (lineMomentum (castLoopMatrix
      (class5LoopMatrix (repBClass i))) (extMomenta (repBClass i) p p') (Fin.castLE (by omega) j)
        (chgD (chgMD i) (chgAD i) p (p' - p) ℓ))) =
      fun j => electronNumerator (Φ.mass Φ.openLine) (lineMomentum₂ (repD i s) (fun _ => p')
        (fun _ => p) (fun _ => p' - p) ℓ (.inl (lineRD i s j))) := by
    funext j
    rw [hm, lineMomentum₂_repD_fermion]
  have hη : pvEta P = pvEta Q := by
    funext x y
    simp only [pvEta, hγ, hΛ]
  simp only [hE, hη, he, hm]
  rcases photonMomentum₂_repD_pm i s p p' ℓ with hq | hq <;> rw [hq] <;>
    (try simp only [lowD_neg, neg_mul, mul_neg, neg_neg]) <;>
    rcases slotD_cases i with ⟨h4, h5⟩ | ⟨h5, h4⟩ <;> rw [h4, h5] <;> unfold wKD <;> ring

/-- **The longitudinal value of `repD i s` in the class routing** (every `ε`). -/
theorem dK_repD_value (Q P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (hm : Φ.mass Φ.openLine = P.m) (he : P.e = Q.e) (hγ : P.mγ = Q.mγ)
    (hΛ : P.Λ = Q.Λ) (δ₃ : ℝ) (i : Fin 12) (s : Fin 2) (p p' : Fin 4 → ℝ) (μ α β : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (dKIntegrand Q Φ δ₃ (repD i s) (fun _ => p')
        (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)) =
      wKD Q δ₃ * QED.TwoLoop.jointEnergyFirstIntegral 2 (dKUnitIntegrandD i s P
        (unitMMasses P.m Q.mγ Q.Λ Q.mγ Q.Λ ![Q.mγ, Q.Λ]) Q.ε p p' μ α β) := by
  rw [← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
  exact QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_eq_of_comp (chgMD i) (isUnit_det_chgMD i)
    _ fun ℓ => dKIntegrand_repD_eq_unit Q P Φ hm he hγ hΛ δ₃ i s p p' μ α β ℓ

end QED.ChainProof.SetCMain

end
