/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0NsAmp

/-!
# The fermion counterterm vertex on a closed loop, resummed

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58), for the classes `FA`, `FB`. Let `C` be a contraction whose vertices are `gauge`
vertices except one `fermionCt` vertex `t₀` on the closed fermion loop, `fo` the loop line leaving
`t₀` (momentum `k`, the momentum read by the counterterm). In an index term of the amplitude at
the zero grading, the spinor index `b = β(t₀)` occurs only in the counterterm factor
`-i (δ₂ k̸ + δm M)_{ab}` and in the propagator entry `S(k)_{by}` of `fo`. With
`(δ₂ k̸ + δm M)(M - k̸) = δ₂ (D_M(k) + iε) + (δm - δ₂) M (M - k̸)` (`k̸ k̸ = -k·k`), the sum over
`b` is `∑_b -i 1_{ab} (δ₂ 1_{by}/i + δ₂ iε 1_{by} D_M(k)⁻¹/i + (δm - δ₂) M S(k)_{by}/i)`
(`sum_ct_entry`): the three variants `v = 0, 1, 2` of `fcTerm`, each a product of line factors
with numerator degree at most one per line (`sum_ampTerm_eq`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetALink

open QED.GradedProof.X0 QED.Graded QED.WickModel
open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero electronNumerator electronPropagator_apply)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type}

/-! ### Vertex factors -/

theorem vertexFactor_congrβ (e δ₁ δ₂ δm δ₃ m : ℝ) (α β β' : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) (hβ : ∀ p, β ⟨t, p⟩ = β' ⟨t, p⟩) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β' lor kψ kA t := by
  unfold Wick.vertexFactor
  split <;> simp only [hβ]

theorem vertexFactor_gauge_eq (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) (h : κ t = .gauge) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      Wick.vertexFactor e 0 0 1 0 1 α β lor 0 0 t := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> simp_all

theorem vertexFactor_ct_eq (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (s : Wick.FermionVertex κ) (h : κ s.1 = .fermionCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA s.1 =
      -I * (((δ₂ : ℂ) • Dirac.slash (kψ s) + ((δm * m : ℝ) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ)) (α s) (β s)) := by
  obtain ⟨t, ht⟩ := s
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> simp_all

/-! ### The counterterm entry -/

/-- `(δ₂ k̸ + δm M)(M - k̸) = δ₂ (D_M(k) + iε) + (δm - δ₂) M (M - k̸)`. -/
theorem ct_mul_numerator (δ₂ δm M ε : ℝ) (k : Fin 4 → ℝ) :
    ((δ₂ : ℂ) • Dirac.slash k + ((δm * M : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) *
        electronNumerator M k =
      ((δ₂ : ℂ) * (propDenom M ε k + (ε : ℂ) * I)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
        (((δm - δ₂ : ℝ) : ℂ) * (M : ℂ)) • electronNumerator M k := by
  have hs := Dirac.slash_mul_slash k
  simp only [electronNumerator, propDenom, Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hs, smul_smul]
  push_cast
  module

/-- **The sum over the spinor index at the counterterm vertex.** -/
theorem sum_ct_entry (δ₂ δm M ε : ℝ) (hε : ε ≠ 0) (k : Fin 4 → ℝ) (a y : Fin 4) :
    ∑ b, (-I * (((δ₂ : ℂ) • Dirac.slash k + ((δm * M : ℝ) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b)) *
      ((1 / I) * QED.OneLoop.electronPropagator M ε k b y) =
    ∑ b, (-I * (1 : Matrix (Fin 4) (Fin 4) ℂ) a b) *
      ((δ₂ : ℂ) * ((1 / I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) b y) +
        ((δ₂ : ℂ) * ((ε : ℂ) * I)) * ((1 / I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) b y *
          (propDenom M ε k)⁻¹) +
        (((δm - δ₂ : ℝ) : ℂ) * (M : ℂ)) *
          ((1 / I) * QED.OneLoop.electronPropagator M ε k b y)) := by
  have hD := propDenom_ne_zero (M := M) hε k
  have hX := congrFun (congrFun (ct_mul_numerator δ₂ δm M ε k) a) y
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hX
  simp only [electronPropagator_apply]
  have h1 : ∀ b, (-I * (1 : Matrix (Fin 4) (Fin 4) ℂ) a b) *
      ((δ₂ : ℂ) * ((1 / I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) b y) +
        ((δ₂ : ℂ) * ((ε : ℂ) * I)) * ((1 / I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) b y *
          (propDenom M ε k)⁻¹) +
        (((δm - δ₂ : ℝ) : ℂ) * (M : ℂ)) * ((1 / I) * (electronNumerator M k b y *
          (propDenom M ε k)⁻¹))) =
      if a = b then -I * ((δ₂ : ℂ) * ((1 / I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) a y) +
        ((δ₂ : ℂ) * ((ε : ℂ) * I)) * ((1 / I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) a y *
          (propDenom M ε k)⁻¹) +
        (((δm - δ₂ : ℝ) : ℂ) * (M : ℂ)) * ((1 / I) * (electronNumerator M k a y *
          (propDenom M ε k)⁻¹))) else 0 := fun b => by
    rw [Matrix.one_apply]
    split_ifs with h
    · subst h; ring
    · ring
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  have h2 : ∑ b, (-I * (((δ₂ : ℂ) • Dirac.slash k + ((δm * M : ℝ) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b)) *
      ((1 / I) * (electronNumerator M k b y * (propDenom M ε k)⁻¹)) =
      -((∑ b, ((δ₂ : ℂ) • Dirac.slash k + ((δm * M : ℝ) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b * electronNumerator M k b y) *
        (propDenom M ε k)⁻¹) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp
  rw [h2]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hX ⊢
  rw [hX]
  field_simp

/-! ### Resummation over one index -/

/-- Resummation over the value of `β s` when the rest of the term does not read it. -/
theorem sum_resum {V : Type*} [Fintype V] [DecidableEq V] (s : V) (Q : (V → Fin 4) → ℂ)
    (hQ : ∀ β b, Q (Function.update β s b) = Q β) (g g' : Fin 4 → ℂ)
    (h : ∑ b, g b = ∑ b, g' b) : ∑ β, Q β * g (β s) = ∑ β, Q β * g' (β s) := by
  set e := Equiv.piSplitAt s (fun _ : V => Fin 4)
  have hsymm : ∀ b r, e.symm (b, r) = Function.update (e.symm (0, r)) s b := fun b r => by
    funext j
    by_cases hj : j = s
    · subst hj; simp [e, Equiv.piSplitAt_symm_apply]
    · simp [e, Equiv.piSplitAt_symm_apply, hj]
  have key : ∀ g : Fin 4 → ℂ, ∑ β, Q β * g (β s) =
      ∑ r : {j // j ≠ s} → Fin 4, Q (e.symm (0, r)) * ∑ b, g b := fun g => by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsymm b r, hQ, Function.update_self]
  rw [key g, key g', h]

/-! ### The terms -/

open scoped Classical in
/-- The external index constraints of an index term. -/
noncomputable def extI (C : Contraction 1 nA κ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) : ℂ :=
  if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0

/-- The constant part of a resummed term: the constraints, the `gauge` vertex factors and `-i`
times the identity entry at the counterterm vertex. -/
noncomputable def fcConst (P : Params) (C : Contraction 1 nA κ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) :
    ℂ :=
  extI C αOut βIn μ α β lor * ∏ t, Wick.vertexFactor P.e 0 0 1 0 1 α β lor 0 0 t

/-- The weight of a variant: `δ₂`, `δ₂ iε`, `(δm - δ₂) M`. -/
noncomputable def fcW (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) :
    Fin 3 → ℂ
  | 0 => ((P.e ^ 2 * D.d₂ f 0 : ℝ) : ℂ)
  | 1 => ((P.e ^ 2 * D.d₂ f 0 : ℝ) : ℂ) * ((P.ε : ℂ) * I)
  | 2 => ((P.e ^ 2 * D.dm f 0 - P.e ^ 2 * D.d₂ f 0 : ℝ) : ℂ) * (Φ.mass f : ℂ)

/-- The factor of the line `fo` in a variant. -/
noncomputable def foFac (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (fo : FermionLine C)
    (M : ℝ) (k : Fin 4 → ℝ) : Fin 3 → ℂ
  | 0 => (1 / I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) (β fo.1) (α fo.tail)
  | 1 => (1 / I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) (β fo.1) (α fo.tail) * (propDenom M P.ε k)⁻¹
  | 2 => nsFac P Φ C α β lor M (.inl fo) k

/-- The line factors of a variant. -/
noncomputable def fcFac (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (fo : FermionLine C)
    (v : Fin 3) (M : ℝ) (l : Line C) (k : Fin 4 → ℝ) : ℂ :=
  if l = .inl fo then foFac P Φ C α β lor fo M k v else nsFac P Φ C α β lor M l k

/-- **A resummed term**: variant `v`, flavour `f` on the loop. -/
noncomputable def fcTerm (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (C : Contraction 1 nA κ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4)
    (fo : FermionLine C) (v : Fin 3) (f : F) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (k : Line C → Fin 4 → ℝ) : ℂ :=
  fcConst P C αOut βIn μ α β lor *
    (fcW P Φ D f v * ∏ l, fcFac P Φ C α β lor fo v (Φ.mass f) l (k l))

/-! ### The resummation -/

theorem psiMomentum₂_fo (C : Contraction 1 nA κ) (pIn : Fin 1 → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (fo : FermionLine C) : psiMomentum₂ C pIn k fo.1 = k (.inl fo) := by
  unfold psiMomentum₂
  split
  · rename_i h
    have := fo.2
    rw [h] at this
    exact absurd this (by simp)
  · rfl

/-- An index term as the constraints, the vertex factors and the line factors. -/
theorem ampTerm_eq_fac (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (C : Contraction 1 nA κ) (f : F) (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) :
    ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn k αOut βIn μ α β lor =
      extI C αOut βIn μ α β lor * ((∏ t, vf0 P D (flOf Φ (closedFlavoring Φ (zOf C) f) t)
        (Φ.mass (flOf Φ (closedFlavoring Φ (zOf C) f) t)) α β lor (psiMomentum₂ C pIn k)
        (photonMomentum₂ C kIn k) t) * ∏ l, nsFac P Φ C α β lor (Φ.mass f) l (k l)) := by
  have hm : ∀ fl : FermionLine C, Φ.mass (closedFlavoring Φ (zOf C) f fl.1) =
      if isZL C (.inl fl) = true then Φ.mass f else Φ.mass Φ.openLine := fun fl => by
    by_cases h : zOf C fl.1 <;> simp [closedFlavoring, isZL, h]
  unfold ampTerm extI
  rw [Fintype.prod_sum_type]
  simp only [hm, nsFac]
  ring

theorem flOf_fo (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ) (fo : FermionLine C)
    (hz : zOf C fo.1) (f : F) : flOf Φ (closedFlavoring Φ (zOf C) f) fo.1.1 = f := by
  unfold flOf
  simp [fo.1.2, closedFlavoring, hz]

theorem nsFac_update (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (fo : FermionLine C)
    (b : Fin 4) (M : ℝ) (l : Line C) (hl : l ≠ .inl fo) (k : Fin 4 → ℝ) :
    nsFac P Φ C α (Function.update β fo.1 b) lor M l k = nsFac P Φ C α β lor M l k := by
  rcases l with fl | g
  · have hne : fl.1 ≠ fo.1 := fun h => hl (congrArg Sum.inl (Subtype.ext h))
    simp only [nsFac, Function.update_of_ne hne]
  · rfl

theorem extI_update (C : Contraction 1 nA κ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (fo : FermionLine C)
    (b : Fin 4) :
    extI C αOut βIn μ α (Function.update β fo.1 b) lor = extI C αOut βIn μ α β lor := by
  have hne : ∀ t i, C.1.1 (.inr t) = .inl i → t ≠ fo.1 := fun t i h ht => by
    have := fo.2
    rw [← ht, h] at this
    exact absurd this (by simp)
  have hiff : (∀ t i, C.1.1 (.inr t) = .inl i → Function.update β fo.1 b t = βIn i) ↔
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) := by
    constructor <;> intro h t i hti <;> have := h t i hti <;>
      simpa [Function.update_of_ne (hne t i hti)] using this
  unfold extI
  simp only [hiff]

/-- **The resummation at the counterterm vertex.** -/
theorem sum_ampTerm_eq (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F) (hε : P.ε ≠ 0)
    (C : Contraction 1 nA κ) (fo : FermionLine C) (hct : κ fo.1.1 = .fermionCt)
    (hκ : ∀ t, t ≠ fo.1.1 → κ t = .gauge) (hz : zOf C fo.1) (f : F)
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) (α : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) :
    ∑ β, ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn k αOut βIn μ α β lor =
      ∑ β, ∑ v : Fin 3, fcTerm P Φ D C αOut βIn μ fo v f α β lor k := by
  classical
  set t₀ := fo.1.1 with ht₀
  set Q : (Wick.FermionVertex κ → Fin 4) → ℂ := fun β => extI C αOut βIn μ α β lor *
    ((∏ t ∈ ({t₀} : Finset (Fin N))ᶜ, Wick.vertexFactor P.e 0 0 1 0 1 α β lor 0 0 t) *
      ∏ l ∈ ({.inl fo} : Finset (Line C))ᶜ, nsFac P Φ C α β lor (Φ.mass f) l (k l)) with hQ
  set X := ((P.e ^ 2 * D.d₂ f 0 : ℝ) : ℂ) • Dirac.slash (k (.inl fo)) +
    (((P.e ^ 2 * D.dm f 0) * Φ.mass f : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) with hX
  set g : Fin 4 → ℂ := fun b => (-I * X (α fo.1) b) *
    ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (k (.inl fo)) b (α fo.tail)) with hg
  set g' : Fin 4 → ℂ := fun b => (-I * (1 : Matrix (Fin 4) (Fin 4) ℂ) (α fo.1) b) *
    ∑ v : Fin 3, fcW P Φ D f v * foFac P Φ C α (fun _ => b) lor fo (Φ.mass f) (k (.inl fo)) v
    with hg'
  have hzl : isZL C (.inl fo) = true := by simp [isZL, hz]
  have hfac0 : ∀ β, nsFac P Φ C α β lor (Φ.mass f) (.inl fo) (k (.inl fo)) =
      (1 / I) * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (k (.inl fo)) (β fo.1)
        (α fo.tail) := fun β => by
    simp only [nsFac, isZL, hz, decide_true, ↓reduceIte]
  have hamp : ∀ β, ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn k αOut βIn μ α β lor =
      Q β * g (β fo.1) := fun β => by
    rw [ampTerm_eq_fac, Fintype.prod_eq_mul_prod_compl t₀,
      Fintype.prod_eq_mul_prod_compl (Sum.inl fo : Line C),
      hfac0]
    have hv : ∏ t ∈ ({t₀} : Finset (Fin N))ᶜ, vf0 P D (flOf Φ (closedFlavoring Φ (zOf C) f) t)
        (Φ.mass (flOf Φ (closedFlavoring Φ (zOf C) f) t)) α β lor (psiMomentum₂ C pIn k)
        (photonMomentum₂ C kIn k) t =
        ∏ t ∈ ({t₀} : Finset (Fin N))ᶜ, Wick.vertexFactor P.e 0 0 1 0 1 α β lor 0 0 t :=
      Finset.prod_congr rfl fun t ht => by
        unfold vf0
        exact vertexFactor_gauge_eq _ _ _ _ _ _ _ _ _ _ _ t
          (hκ t (by simpa using ht))
    have hct' : vf0 P D (flOf Φ (closedFlavoring Φ (zOf C) f) t₀)
        (Φ.mass (flOf Φ (closedFlavoring Φ (zOf C) f) t₀)) α β lor (psiMomentum₂ C pIn k)
        (photonMomentum₂ C kIn k) t₀ = -I * X (α fo.1) (β fo.1) := by
      unfold vf0
      rw [ht₀, vertexFactor_ct_eq _ _ _ _ _ _ _ _ _ _ _ fo.1 hct, psiMomentum₂_fo,
        flOf_fo Φ C fo hz f]
    rw [hv, hct']
    simp only [hQ, hg]
    ring
  have hct : ∀ β, ∑ v : Fin 3, fcTerm P Φ D C αOut βIn μ fo v f α β lor k =
      Q β * g' (β fo.1) := fun β => by
    have hv : Wick.vertexFactor P.e 0 0 1 0 1 α β lor 0 0 t₀ =
        -I * (1 : Matrix (Fin 4) (Fin 4) ℂ) (α fo.1) (β fo.1) := by
      rw [ht₀, vertexFactor_ct_eq _ _ _ _ _ _ _ _ _ _ _ fo.1 hct]
      simp
    have hl : ∀ v, ∏ l, fcFac P Φ C α β lor fo v (Φ.mass f) l (k l) =
        foFac P Φ C α (fun _ => β fo.1) lor fo (Φ.mass f) (k (.inl fo)) v *
          ∏ l ∈ ({.inl fo} : Finset (Line C))ᶜ, nsFac P Φ C α β lor (Φ.mass f) l (k l) :=
        fun v => by
      rw [Fintype.prod_eq_mul_prod_compl (Sum.inl fo : Line C)]
      congr 1
      · simp only [fcFac, ↓reduceIte]
        fin_cases v <;> rfl
      · refine Finset.prod_congr rfl fun l hl => ?_
        have : l ≠ .inl fo := by simpa using hl
        simp only [fcFac, this, ↓reduceIte]
    simp only [fcTerm, fcConst, hl, Fintype.prod_eq_mul_prod_compl t₀, hv, hQ, hg',
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  have hQu : ∀ β b, Q (Function.update β fo.1 b) = Q β := fun β b => by
    simp only [hQ, extI_update]
    congr 2
    · refine Finset.prod_congr rfl fun t ht => vertexFactor_congrβ _ _ _ _ _ _ _ _ _ _ _ _ _
        fun p => Function.update_of_ne (fun h => ?_) _ _
      have : t ≠ t₀ := by simpa using ht
      exact this (by rw [ht₀, ← h])
    · exact Finset.prod_congr rfl fun l hl =>
        nsFac_update P Φ C α β lor fo b (Φ.mass f) l (by simpa using hl) _
  have hsum : ∑ b, g b = ∑ b, g' b := by
    have h := sum_ct_entry (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0) (Φ.mass f) P.ε hε
      (k (.inl fo)) (α fo.1) (α fo.tail)
    simp only [hg, hg', Fin.sum_univ_three]
    refine h.trans (Finset.sum_congr rfl fun b _ => ?_)
    have h2 : foFac P Φ C α (fun _ => b) lor fo (Φ.mass f) (k (.inl fo)) 2 =
        (1 / I) * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (k (.inl fo)) b (α fo.tail) :=
      by simp only [foFac]; exact hfac0 _
    rw [h2]
    simp only [foFac, fcW]
  simp only [hamp, hct]
  exact sum_resum fo.1 Q hQu g g' hsum

end QED.ChainProof.SetALink

end
