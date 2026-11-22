/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainRel

/-!
# Set (c), the `δ₃` classes: the transverse part as an open-line chain

Helper level for the per-class links of the 24 classes `repD i s` of set (c)
(`QED.ChainProof.SetCPauli.mainVal (.inr (i, s))`). The transverse (`k² g^{ab}`) part of the
integrand, `QED.ChainProof.SetCMain.dGIntegrand`, is an index sum over the spinor indices of the
five fermion vertices of `kD` and the Lorentz indices of its seven photon fields. This file
evaluates that sum as the open-line chain of the class representative, at arbitrary line momenta:

`∑ extI · ctGD · gV · lineProd = -(i/2) δ₃ q² · (1/i)(Λ² - m_γ²) · (ie)⁵ (1/i)⁴ · ∏ dProd ·
  ∑_l [l_e = μ] η_{l_a l_b} η_{l_c l_d} (γ^{l₄} E₃ γ^{l₃} E₂ γ^{l₂} E₁ γ^{l₁} E₀ γ^{l₀})`,

with `η = QED.TwoLoop.LimitCovariance.pvEta` and `E_j` the electron numerators of the lines, in
the class labels (vertex `t` of the class is vertex `4 - t` of `kD`, `eFV`, `ePS`). The two
`photonCt` slots contract to `(1/i)(Λ² - m_γ²) η_{l_a l_b}` (`sum_eta_metric_eta`), the element
line of the class representative.

* `eFV`, `ePS`: the fermion vertices and photon fields of `kD` in the class labels;
* `dGTerm`, `dG_term_eq`, `sum_dGTerm`: the summand after the change of index variables and its
  sum;
* **`dG_sum_chain`**: the chain form for any `kD` contraction with the stated line facts;
* `lineRD`, `photD`, `ctEndA`, `ctEndB` and the kernel-checked facts (`prod_lineRD`, `prod_photD`,
  `photD_ends`, `repD_ext`); **`dG_repD_chain`**: the twenty-four orbits.

The chain is `QED.TwoLoop.LimitCovariance.chainNum` of the class representative of `repB i`
once the photon pairing is matched; the line momenta in the class routing and the denominators
of the multi-denominator unit are separate steps.
-/

@[expose] public section

open Complex Matrix
open QED.WickModel (Params Contraction FermionLine PhotonLine Line)

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.Enumeration QED.ChainProof.SetCLink QED.ChainProof.SetALink
open QED.GradedProof.X0 QED.TwoLoop.LimitCovariance
open QED.TwoLoop.Bridge (electronNumerator)
open QED.ChainProof.Enum (pc)

/-- The fermion vertices of `kD` are the five open-line vertices. -/
theorem kD_fv_lt : ∀ v : Wick.FermionVertex kD, v.1.val < 5 := by decide

/-- The fermion vertices of `kD` as those of five gauge vertices, vertex `t` as `4 - t`. -/
def eFV : Wick.FermionVertex kD ≃ Wick.FermionVertex (gauges 5) where
  toFun v := fv5 (Fin.rev ⟨v.1.val, kD_fv_lt v⟩)
  invFun u := fvD (Fin.rev u.1)
  left_inv := by decide
  right_inv := by decide

theorem kD_slots_le : ∀ (t : Fin 6) (j : Fin (kD t).photonSlots), j.val < 2 := by decide

/-- The photon fields of `kD`: the open-line ones (vertex `t` as `4 - t`) and the two
`photonCt` ones. -/
def ePS : Wick.PhotonSlot kD ≃ Fin 5 ⊕ Fin 2 where
  toFun x := if h : x.1.val < 5 then .inl (Fin.rev ⟨x.1.val, h⟩) else
    .inr ⟨x.2.val, kD_slots_le _ _⟩
  invFun
    | .inl u => plD (Fin.rev u)
    | .inr s => pc kD 5 s
  left_inv := by decide
  right_inv := by decide

variable {F : Type}

theorem eFV_symm_apply (u : Wick.FermionVertex (gauges 5)) : eFV.symm u = fvD (Fin.rev u.1) :=
  rfl

theorem ePS_symm_inl (u : Fin 5) : ePS.symm (.inl u) = plD (Fin.rev u) := rfl

theorem ePS_symm_inr (s : Fin 2) : ePS.symm (.inr s) = pc kD 5 s := rfl

theorem fv5_val_D (u : Fin 5) : (fv5 u).1 = u := rfl

theorem rev_five : Fin.rev (0 : Fin 5) = 4 ∧ Fin.rev (1 : Fin 5) = 3 ∧ Fin.rev (2 : Fin 5) = 2 ∧
    Fin.rev (3 : Fin 5) = 1 ∧ Fin.rev (4 : Fin 5) = 0 := by decide

theorem succ_cast_four : Fin.succ (0 : Fin 4) = 1 ∧ Fin.succ (1 : Fin 4) = 2 ∧
    Fin.succ (2 : Fin 4) = 3 ∧ Fin.succ (3 : Fin 4) = 4 ∧ Fin.castSucc (0 : Fin 4) = 0 ∧
    Fin.castSucc (1 : Fin 4) = 1 ∧ Fin.castSucc (2 : Fin 4) = 2 ∧ Fin.castSucc (3 : Fin 4) = 3 := by
  decide

theorem gV_eq (e : ℝ) (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4) :
    gV e α β lor = ∏ t : Fin 5, I * e * Dirac.gamma (lor (plD t)) (α (fvD t)) (β (fvD t)) := by
  simp only [gV, Fin.prod_univ_six, Fin.prod_univ_five]
  simp only [show ((0 : Fin 6) = 5) = False by decide, show ((1 : Fin 6) = 5) = False by decide,
    show ((2 : Fin 6) = 5) = False by decide, show ((3 : Fin 6) = 5) = False by decide,
    show ((4 : Fin 6) = 5) = False by decide, ite_false, ite_true, mul_one]
  rfl

theorem pvEta_symm (P : Params) (x y : Fin 4) : pvEta P x y = pvEta P y x := by
  simp only [pvEta, QED.Minkowski.metric_symm x y]

theorem sum_eta_metric_eta (P : Params) (u v : Fin 4) :
    ∑ x, ∑ y, pvEta P u x * ((Minkowski.metric x y : ℝ) : ℂ) * pvEta P y v =
      (1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * pvEta P u v := by
  simp only [pvEta, Minkowski.metric, Fin.sum_univ_four]
  fin_cases u <;> fin_cases v <;> simp
  all_goals ring


/-- The summand of the transverse part after the change of index variables. -/
noncomputable def dGTerm (P : Params) (m δ₃ : ℝ) (q : Fin 4 → ℝ) (K : Fin 4 → Fin 4 → ℝ)
    (Dens : ℂ) (a b c d e : Fin 5) (αOut βIn μ : Fin 1 → Fin 4)
    (α β : Wick.FermionVertex (gauges 5) → Fin 4) (L : Fin 5 ⊕ Fin 2 → Fin 4) : ℂ :=
  (if α (fv5 4) = αOut 0 ∧ β (fv5 0) = βIn 0 ∧ L (.inl e) = μ 0 then 1 else 0) *
    (-(I / 2) * ((δ₃ * Minkowski.metric (L (.inr 0)) (L (.inr 1)) : ℝ) : ℂ) *
      ((Minkowski.dot q q : ℝ) : ℂ)) *
    ((∏ u : Fin 5, I * P.e * Dirac.gamma (L (.inl u)) (α (fv5 u)) (β (fv5 u))) *
      ((∏ i : Fin 4, (1 / I) * electronNumerator m (K i) (β (fv5 i.succ)) (α (fv5 i.castSucc))) *
        (pvEta P (L (.inl a)) (L (.inr 0)) * pvEta P (L (.inr 1)) (L (.inl b)) *
          pvEta P (L (.inl c)) (L (.inl d))) * Dens))

theorem dG_term_eq (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) (C : Contraction 1 1 kD)
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
    extI C αOut βIn μ α β lor * (ctGD δ₃ lor q *
        (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k)) =
      dGTerm P (Φ.mass Φ.openLine) δ₃ q (fun i => k (.inl (line i)))
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
  unfold dGTerm ctGD
  simp only [Function.comp_apply, Fin.prod_univ_five, Fin.prod_univ_four, eFV_symm_apply,
    ePS_symm_inl, ePS_symm_inr, fv5_val_D, r0, r1, r2, r3, r4, s0, s1, s2, s3, c0, c1, c2, c3]
  ring


theorem sum_sumArrow (g : (Fin 5 ⊕ Fin 2 → Fin 4) → ℂ) :
    ∑ L, g L = ∑ l : Fin 5 → Fin 4, ∑ x : Fin 4, ∑ y : Fin 4, g (Sum.elim l ![x, y]) := by
  rw [← (Equiv.sumArrowEquivProdArrow (Fin 5) (Fin 2) (Fin 4)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← (piFinTwoEquiv fun _ => Fin 4).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  congr 1

theorem sum_dGTerm (P : Params) (m δ₃ : ℝ) (q : Fin 4 → ℝ) (K : Fin 4 → Fin 4 → ℝ)
    (Dens : ℂ) (a b c d e : Fin 5) (αOut βIn μ : Fin 1 → Fin 4) :
    ∑ α, ∑ β, ∑ L, dGTerm P m δ₃ q K Dens a b c d e αOut βIn μ α β L =
      (-(I / 2) * (δ₃ : ℂ) * ((Minkowski.dot q q : ℝ) : ℂ) *
        ((1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ))) * ((I * P.e) ^ 5 * (1 / I) ^ 4) * Dens *
        ∑ l : Fin 5 → Fin 4, kron (μ 0) (l e) * pvEta P (l a) (l b) * pvEta P (l c) (l d) *
          openChain (fun u => Dirac.gamma (l u)) (fun i => electronNumerator m (K i))
            (αOut 0) (βIn 0) := by
  set G : (Fin 5 → Fin 4) → Fin 5 → Matrix (Fin 4) (Fin 4) ℂ := fun l u => Dirac.gamma (l u)
  set E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun i => electronNumerator m (K i)
  set W : ℂ := -(I / 2) * (δ₃ : ℂ) * ((Minkowski.dot q q : ℝ) : ℂ)
  have hfac : ∀ α β l x y, dGTerm P m δ₃ q K Dens a b c d e αOut βIn μ α β (Sum.elim l ![x, y]) =
      (kron (μ 0) (l e) * (-(I / 2) * ((δ₃ * Minkowski.metric x y : ℝ) : ℂ) *
        ((Minkowski.dot q q : ℝ) : ℂ)) * (pvEta P (l a) x * pvEta P y (l b) *
          pvEta P (l c) (l d)) * ((I * P.e) ^ 5 * (1 / I) ^ 4) * Dens) *
        ((if α (fv5 4) = αOut 0 ∧ β (fv5 0) = βIn 0 then (1 : ℂ) else 0) *
          (G l 0 (α (fv5 0)) (β (fv5 0)) * G l 1 (α (fv5 1)) (β (fv5 1)) *
            G l 2 (α (fv5 2)) (β (fv5 2)) * G l 3 (α (fv5 3)) (β (fv5 3)) *
            G l 4 (α (fv5 4)) (β (fv5 4)) *
            (E 0 (β (fv5 1)) (α (fv5 0)) * E 1 (β (fv5 2)) (α (fv5 1)) *
              E 2 (β (fv5 3)) (α (fv5 2)) * E 3 (β (fv5 4)) (α (fv5 3))))) := by
    intro α β l x y
    obtain ⟨s0, s1, s2, s3, c0, c1, c2, c3⟩ := succ_cast_four
    unfold dGTerm
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
    kron (μ 0) (l e) * (-(I / 2) * ((δ₃ * Minkowski.metric x y : ℝ) : ℂ) *
      ((Minkowski.dot q q : ℝ) : ℂ)) * (pvEta P (l a) x * pvEta P y (l b) *
        pvEta P (l c) (l d)) * ((I * P.e) ^ 5 * (1 / I) ^ 4) * Dens with hA
  have h1 : ∀ α β, ∑ L, dGTerm P m δ₃ q K Dens a b c d e αOut βIn μ α β L =
      ∑ l, A l * B α β l := fun α β => by
    rw [sum_sumArrow]
    simp only [hfac, hA, hB, Finset.sum_mul]
  have h2 : ∀ l, ∑ α, ∑ β, B α β l = openChain (G l) E (αOut 0) (βIn 0) := fun l =>
    openSpinSum (G l) E (αOut 0) (βIn 0)
  have h3 : ∀ l, A l = (-(I / 2) * (δ₃ : ℂ) * ((Minkowski.dot q q : ℝ) : ℂ) *
      ((1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ))) * ((I * P.e) ^ 5 * (1 / I) ^ 4) * Dens *
        (kron (μ 0) (l e) * pvEta P (l a) (l b) * pvEta P (l c) (l d)) := fun l => by
    have h : A l = (kron (μ 0) (l e) * (-(I / 2) * (δ₃ : ℂ) * ((Minkowski.dot q q : ℝ) : ℂ)) *
        pvEta P (l c) (l d) * ((I * P.e) ^ 5 * (1 / I) ^ 4) * Dens) *
        ∑ x, ∑ y, pvEta P (l a) x * ((Minkowski.metric x y : ℝ) : ℂ) * pvEta P y (l b) := by
      simp only [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      push_cast
      ring
    rw [h, sum_eta_metric_eta]
    ring
  calc ∑ α, ∑ β, ∑ L, dGTerm P m δ₃ q K Dens a b c d e αOut βIn μ α β L
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


/-- **The transverse part of a `kD` contraction as an open-line chain.** -/
theorem dG_sum_chain (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) (C : Contraction 1 1 kD)
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
    (hext : ∀ (j : Fin 1) x, C.1.2 (.inl j) = .inr x ↔ x = plD (Fin.rev e)) :
    ∑ α, ∑ β, ∑ lor, extI C αOut βIn μ α β lor * (ctGD δ₃ lor q *
        (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k)) =
      (-(I / 2) * (δ₃ : ℂ) * ((Minkowski.dot q q : ℝ) : ℂ) *
        ((1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ))) * ((I * P.e) ^ 5 * (1 / I) ^ 4) *
        (∏ l, dProd P.ε (dMs P Φ l) (k l)) *
        ∑ l : Fin 5 → Fin 4, kron (μ 0) (l e) * pvEta P (l a) (l b) * pvEta P (l c) (l d) *
          openChain (fun u => Dirac.gamma (l u))
            (fun i => electronNumerator (Φ.mass Φ.openLine) (k (.inl (line i))))
            (αOut 0) (βIn 0) := by
  simp only [dG_term_eq P Φ δ₃ C αOut βIn μ q k line hfl hval htail gA gB gC hph a b c d e hA hB hC
    hout hin hext]
  rw [← sum_dGTerm]
  refine Fintype.sum_equiv (Equiv.arrowCongr eFV (Equiv.refl _)) _ _ fun α => ?_
  refine Fintype.sum_equiv (Equiv.arrowCongr eFV (Equiv.refl _)) _ _ fun β => ?_
  exact Fintype.sum_equiv (Equiv.arrowCongr ePS (Equiv.refl _)) _ _ fun lor => rfl


/-! ### The twenty-four orbits -/

theorem lineRD_spec : ∀ (i : Fin 12) (s : Fin 2) (j : Fin 4),
    ((repD i s).1.1 (.inr (fvD (Fin.rev j.succ)))).isRight := by
  decide +kernel

/-- The fermion line of `repD i s` that is the class line `j` (from class vertex `j + 1` to `j`). -/
def lineRD (i : Fin 12) (s : Fin 2) (j : Fin 4) : FermionLine (repD i s) :=
  ⟨fvD (Fin.rev j.succ), lineRD_spec i s j⟩

theorem lineRD_bijective : ∀ i s, Function.Bijective (lineRD i s) := by
  decide +kernel

theorem lineRD_tail : ∀ i s (j : Fin 4), (lineRD i s j).tail = fvD (Fin.rev j.castSucc) := by
  decide +kernel

theorem prod_lineRD {M : Type*} [CommMonoid M] (i : Fin 12) (s : Fin 2)
    (g : FermionLine (repD i s) → M) :
    ∏ f, g f = g (lineRD i s 0) * g (lineRD i s 1) * g (lineRD i s 2) * g (lineRD i s 3) := by
  rw [← (Equiv.ofBijective _ (lineRD_bijective i s)).prod_comp, Fin.prod_univ_four]
  rfl

/-- The lower end (in `photonKey`) of the photon line through a photon field. -/
def lowEnd {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (x : Wick.PhotonSlot κ) :
    Wick.PhotonSlot κ :=
  match C.1.2 (.inr x) with
  | .inr y => if Wick.photonKey x < Wick.photonKey y then x else y
  | .inl _ => x

/-- The photon fields of the three photon lines of `repD i s`, by one end: the `photonCt`
fields `0`, `1` and the other photon line. -/
def photEnd (i : Fin 12) : Fin 3 → Wick.PhotonSlot kD :=
  ![pc kD 5 0, pc kD 5 1, plD (skR i)]

theorem photD_spec : ∀ (i : Fin 12) (s : Fin 2) (r : Fin 3), ∃ b,
    (repD i s).1.2 (.inr (lowEnd (repD i s) (photEnd i r))) = .inr b ∧
      Wick.photonKey (lowEnd (repD i s) (photEnd i r)) < Wick.photonKey b := by
  decide +kernel

/-- The three photon lines of `repD i s`. -/
def photD (i : Fin 12) (s : Fin 2) (r : Fin 3) : PhotonLine (repD i s) :=
  ⟨lowEnd (repD i s) (photEnd i r), photD_spec i s r⟩

theorem photD_bijective : ∀ i s, Function.Bijective (photD i s) := by
  decide +kernel

theorem prod_photD {M : Type*} [CommMonoid M] (i : Fin 12) (s : Fin 2)
    (g : PhotonLine (repD i s) → M) :
    ∏ f, g f = g (photD i s 0) * g (photD i s 1) * g (photD i s 2) := by
  rw [← (Equiv.ofBijective _ (photD_bijective i s)).prod_comp, Fin.prod_univ_three]
  rfl

/-- The class vertex of the open-line end of the `photonCt` field `0`. -/
def ctEndA (i : Fin 12) (s : Fin 2) : Fin 5 := Fin.rev (if s = 0 then skP i else skQ i)

/-- The class vertex of the open-line end of the `photonCt` field `1`. -/
def ctEndB (i : Fin 12) (s : Fin 2) : Fin 5 := Fin.rev (if s = 0 then skQ i else skP i)

theorem photD_ends : ∀ i s,
    (((photD i s 0).1 = plD (Fin.rev (ctEndA i s)) ∧ (photD i s 0).head = pc kD 5 0) ∨
      ((photD i s 0).1 = pc kD 5 0 ∧ (photD i s 0).head = plD (Fin.rev (ctEndA i s)))) ∧
    (((photD i s 1).1 = pc kD 5 1 ∧ (photD i s 1).head = plD (Fin.rev (ctEndB i s))) ∨
      ((photD i s 1).1 = plD (Fin.rev (ctEndB i s)) ∧ (photD i s 1).head = pc kD 5 1)) ∧
    (((photD i s 2).1 = plD (Fin.rev (Fin.rev (skR i))) ∧
        (photD i s 2).head = plD (Fin.rev (Fin.rev (skT i)))) ∨
      ((photD i s 2).1 = plD (Fin.rev (Fin.rev (skT i))) ∧
        (photD i s 2).head = plD (Fin.rev (Fin.rev (skR i))))) := by
  decide +kernel

theorem repD_ext : ∀ i s,
    (∀ (j : Fin 1) t, (repD i s).1.1 (.inl j) = .inr t ↔ t = fvD 0) ∧
    (∀ t (j : Fin 1), (repD i s).1.1 (.inr t) = .inl j ↔ t = fvD 4) ∧
    (∀ (j : Fin 1) x, (repD i s).1.2 (.inl j) = .inr x ↔ x = plD (Fin.rev (Fin.rev (skE i)))) := by
  decide +kernel

/-- **The transverse part of `repD i s` as an open-line chain** in the class labels. -/
theorem dG_repD_chain (P : Params) (Φ : Lepton.Flavors F) (δ₃ : ℝ) (i : Fin 12) (s : Fin 2)
    (αOut βIn μ : Fin 1 → Fin 4) (q : Fin 4 → ℝ) (k : Line (repD i s) → Fin 4 → ℝ) :
    ∑ α, ∑ β, ∑ lor, extI (repD i s) αOut βIn μ α β lor * (ctGD δ₃ lor q *
        (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k)) =
      (-(I / 2) * (δ₃ : ℂ) * ((Minkowski.dot q q : ℝ) : ℂ) *
        ((1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ))) * ((I * P.e) ^ 5 * (1 / I) ^ 4) *
        (∏ l, dProd P.ε (dMs P Φ l) (k l)) *
        ∑ l : Fin 5 → Fin 4, kron (μ 0) (l (Fin.rev (skE i))) *
          pvEta P (l (ctEndA i s)) (l (ctEndB i s)) *
          pvEta P (l (Fin.rev (skR i))) (l (Fin.rev (skT i))) *
          openChain (fun u => Dirac.gamma (l u))
            (fun j => electronNumerator (Φ.mass Φ.openLine) (k (.inl (lineRD i s j))))
            (αOut 0) (βIn 0) := by
  obtain ⟨hA, hB, hC⟩ := photD_ends i s
  obtain ⟨hout, hin, hext⟩ := repD_ext i s
  exact dG_sum_chain P Φ δ₃ (repD i s) αOut βIn μ q k (lineRD i s) (prod_lineRD i s)
    (fun _ => rfl) (lineRD_tail i s) _ _ _ (prod_photD i s) _ _ _ _ _ hA hB hC hout hin hext

end QED.ChainProof.SetCMain

end
