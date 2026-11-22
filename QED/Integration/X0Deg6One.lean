/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.X0Deg6Merge

/-!
# (T₉′) at one loop with a doubled fermion line at a fermion counterterm vertex

Helper level for the Phase 5 Stage 3 goals (HA₀) and (HS₀) (decision D-58). Let a one-loop
contraction amplitude carry the line momenta `c_l ℓ + e_l` (`oneMom`), and let a `fermionCt`
vertex `t₀` sit between two fermion lines `fi` (ending at `t₀`) and `fo` (starting at `t₀`) of
the same momentum `c ℓ + e`, `c ≠ 0`, and the same mass: a doubled line. With `n = L_f + 2 L_g`
loop denominators and the numerator degree `oneDeg = L_f + ∑_t vDeg t` of
`QED.GradedProof.X0.jointEnergyFirstIntegrable_oneCt`, the **doubled-line criterion**
`oneDeg ≤ 6`, `4 + oneDeg < 2 n` gives (T₉′) for `ε > 0` and any masses
(`jointEnergyFirstIntegrable_oneCtDbl`): the doubled pair buys back two degrees.

## Proof

Resum each index term over the two spinor indices of `t₀` (`sum_sum_resum`): the pair
`S(k) (-i X) S(k)` becomes `i (Y₁ D⁻¹ + Y₂ D⁻²)` with `Y₁, Y₂` affine in `k`
(`sum_sum_ct_entry`). Each of the two pieces is a one-loop integrand with numerator degree
`oneDeg - 2 ≤ 4`, with all `n` loop denominators (`Y₂`) or all but that of `fo` (`Y₁`); the
X₀ one-loop theorem applies (`jointEnergyFirstIntegrable_oneLines`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0Deg6

open QED.WickModel QED.GradedProof.X0
open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero electronNumerator electronPropagator_apply)

/-! ### Splitting products and sums -/

theorem prod_split_one {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℂ) (a : T) :
    ∏ t, f t = f a * ∏ t, (if t = a then 1 else f t) := by
  have h : ∏ t, (if t = a then 1 else f t) = ∏ t ∈ {a}ᶜ, f t := by
    rw [Fintype.prod_eq_mul_prod_compl a, ite_eq_left rfl, one_mul]
    exact Finset.prod_congr rfl fun t ht => ite_eq_right (by simpa using ht)
  rw [h, Fintype.prod_eq_mul_prod_compl a]

theorem prod_split_two {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℂ) {a b : T}
    (hab : a ≠ b) :
    ∏ t, f t = f a * f b * ∏ t, (if t = b then 1 else if t = a then 1 else f t) := by
  rw [prod_split_one f a, prod_split_one (fun t => if t = a then 1 else f t) b,
    ite_eq_right hab.symm, mul_assoc]

theorem sum_split_one {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℕ) (a : T) :
    ∑ t, f t = f a + ∑ t, (if t = a then 0 else f t) := by
  have h : ∑ t, (if t = a then 0 else f t) = ∑ t ∈ {a}ᶜ, f t := by
    rw [Fintype.sum_eq_add_sum_compl a, ite_eq_left rfl, zero_add]
    exact Finset.sum_congr rfl fun t ht => ite_eq_right (by simpa using ht)
  rw [h, Fintype.sum_eq_add_sum_compl a]

theorem sum_split_two {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℕ) {a b : T}
    (hab : a ≠ b) :
    ∑ t, f t = f a + f b + ∑ t, (if t = b then 0 else if t = a then 0 else f t) := by
  rw [sum_split_one f a, sum_split_one (fun t => if t = a then 0 else f t) b,
    ite_eq_right hab.symm, add_assoc]

/-! ### The lines and the vertex factors -/

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

theorem tail_spec {C : Contraction nf nA κ} (f : FermionLine C) :
    C.1.1 (.inr f.1) = .inr f.tail :=
  (Sum.inr_getRight _ f.2).symm

theorem eq_of_tail_eq {C : Contraction nf nA κ} {f g : FermionLine C} (h : f.tail = g.tail) :
    f = g :=
  Subtype.ext (Sum.inr.inj (C.1.1.injective (by rw [tail_spec, tail_spec, h])))

theorem psiMomentum₂_line (C : Contraction nf nA κ) (pIn : Fin nf → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (fo : FermionLine C) : psiMomentum₂ C pIn k fo.1 = k (.inl fo) := by
  unfold psiMomentum₂
  split
  · rename_i h
    have := fo.2
    rw [h] at this
    exact absurd this (by simp)
  · rfl

theorem psiCoeff_line {C : Contraction nf nA κ} (c : Line C → ℤ) (fo : FermionLine C) :
    psiCoeff c fo.1 = c (.inl fo) := by
  unfold psiCoeff
  split
  · rename_i h
    have := fo.2
    rw [h] at this
    exact absurd this (by simp)
  · rfl

theorem vertexFactor_congr₂ (e δ₁ δ₂ δm δ₃ m : ℝ) (α α' β β' : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) (hα : ∀ p, α ⟨t, p⟩ = α' ⟨t, p⟩)
    (hβ : ∀ p, β ⟨t, p⟩ = β' ⟨t, p⟩) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α' β' lor kψ kA t := by
  unfold Wick.vertexFactor
  split <;> simp only [hα, hβ]

theorem vertexFactor_ctLine (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (s : Wick.FermionVertex κ) (h : κ s.1 = .fermionCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA s.1 =
      -I * (((δ₂ : ℂ) • Dirac.slash (kψ s) + ((δm * m : ℝ) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ)) (α s) (β s)) := by
  obtain ⟨t, ht⟩ := s
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> simp_all

theorem vDeg_line {C : Contraction nf nA κ} (c : Line C → ℤ) (fo : FermionLine C)
    (hct : κ fo.1.1 = .fermionCt) (hc0 : c (.inl fo) ≠ 0) : vDeg c fo.1.1 = 1 := by
  have h := psiCoeff_line c fo
  unfold vDeg
  rw [dite_eq_left hct]
  exact ite_eq_right (by rw [h]; exact hc0)

/-! ### The one-loop theorem with a predicate on the fermion denominators -/

/-- **(T₉′) of a one-loop line product**: numerator `AffPoly d`, the denominators of the fermion
lines with `pF` (loop lines) and of the loop photon lines (two each). -/
theorem jointEnergyFirstIntegrable_oneLines {ε : ℝ} (hε : 0 < ε) (C : Contraction nf nA κ)
    (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ) (Mf : FermionLine C → ℝ) (mγ Λ : ℝ)
    (pF : FermionLine C → Prop) [DecidablePred pF] (hpF : ∀ f, pF f → c (.inl f) ≠ 0) {d : ℕ}
    (hd : d ≤ 4) (hn : 4 + d < 2 * (Fintype.card {f // pF f} + 2 * loopPhotonCount c))
    {Nm : (Fin 4 → ℝ) → ℂ} (hN : AffPoly d Nm) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => Nm (ℓ 0) *
      ((∏ f, if pF f then
          (propDenom (Mf f) ε ((c (.inl f) : ℝ) • ℓ 0 + ext (.inl f)))⁻¹ else 1) *
        ∏ g : PhotonLine C, if c (.inr g) ≠ 0 then
          (propDenom mγ ε ((c (.inr g) : ℝ) • ℓ 0 + ext (.inr g)))⁻¹ *
            (propDenom Λ ε ((c (.inr g) : ℝ) • ℓ 0 + ext (.inr g)))⁻¹ else 1) := by
  classical
  have hcard : Fintype.card ({f // pF f} ⊕ ({g : PhotonLine C // c (.inr g) ≠ 0} × Fin 2)) =
      Fintype.card {f // pF f} + 2 * loopPhotonCount c := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, loopPhotonCount,
      Fintype.card_subtype]
    ring
  have h := jointEnergyFirstIntegrable_oneLoop_affPoly'
    (ι := {f // pF f} ⊕ ({g : PhotonLine C // c (.inr g) ≠ 0} × Fin 2))
    (Sum.elim (fun f => (c (.inl f.1) : ℝ)) fun x => (c (.inr x.1.1) : ℝ))
    (fun i => match i with
      | .inl f => by simpa using hpF _ f.2
      | .inr x => by simpa using x.1.2)
    (Sum.elim (fun f => ext (.inl f.1)) fun x => ext (.inr x.1.1))
    (Sum.elim (fun f => Mf f.1) fun x => if x.2 = 0 then mγ else Λ) hε hd
    (by rw [hcard]; exact hn) hN
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fin.prod_univ_two, Sum.elim_inl,
    Sum.elim_inr, Fin.isValue, ite_true, one_ne_zero, ite_false]
  rw [← prod_ite_one_eq_subtype pF
      (fun f => (propDenom (Mf f) ε ((c (.inl f) : ℝ) • ℓ 0 + ext (.inl f)))⁻¹),
    ← prod_ite_one_eq_subtype (fun g : PhotonLine C => c (.inr g) ≠ 0)
      (fun g => (propDenom mγ ε ((c (.inr g) : ℝ) • ℓ 0 + ext (.inr g)))⁻¹ *
        (propDenom Λ ε ((c (.inr g) : ℝ) • ℓ 0 + ext (.inr g)))⁻¹)]

/-! ### The doubled-line theorem -/

/-- The index term with the doubled pair (the lines `fi`, `fo` and the vertex `fo.1`) removed. -/
noncomputable def dblQ (P : Params) (C : Contraction nf nA κ) (φ : Flavoring κ) (c : Line C → ℤ)
    (ext : Line C → Fin 4 → ℝ) (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) (fi fo : FermionLine C)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (k : Fin 4 → ℝ) : ℂ :=
  (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
    ((∏ t, if t = fo.1.1 then 1 else Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
        (psiMomentum₂ C pIn (oneMom c ext k)) (photonMomentum₂ C kIn (oneMom c ext k)) t) *
      (∏ f, if f = fo then 1 else if f = fi then 1 else (1 / I) *
        QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε (oneMom c ext k (.inl f))
          (β f.1) (α f.tail)) *
      ∏ g, (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
        (oneMom c ext k (.inr g)) (lor g.1) (lor g.head))

/-- The merged pair `i (Y₁ D⁻¹ + Y₂ D⁻²)` at the entry `(β fi.1, α fo.tail)`. -/
noncomputable def dblMrg (P : Params) {C : Contraction nf nA κ} (φ : Flavoring κ)
    (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ) (fi fo : FermionLine C)
    (α β : Wick.FermionVertex κ → Fin 4) (k : Fin 4 → ℝ) : ℂ :=
  I * (affNum (P.mass (φ.1 fo.1)) ((c (.inl fo) : ℝ) • k + ext (.inl fo))
      (mergeU P.δ₂ P.δm P.m (P.mass (φ.1 fo.1)) P.ε 0)
      (mergeV P.δ₂ P.δm P.m (P.mass (φ.1 fo.1)) P.ε 0) (β fi.1) (α fo.tail) *
      (propDenom (P.mass (φ.1 fo.1)) P.ε ((c (.inl fo) : ℝ) • k + ext (.inl fo)))⁻¹ +
    affNum (P.mass (φ.1 fo.1)) ((c (.inl fo) : ℝ) • k + ext (.inl fo))
      (mergeU P.δ₂ P.δm P.m (P.mass (φ.1 fo.1)) P.ε 1)
      (mergeV P.δ₂ P.δm P.m (P.mass (φ.1 fo.1)) P.ε 1) (β fi.1) (α fo.tail) *
      ((propDenom (P.mass (φ.1 fo.1)) P.ε ((c (.inl fo) : ℝ) • k + ext (.inl fo)))⁻¹ *
        (propDenom (P.mass (φ.1 fo.1)) P.ε ((c (.inl fo) : ℝ) • k + ext (.inl fo)))⁻¹))

/-- **The resummed amplitude**: each index term with the doubled pair replaced by the merged
entry (`sum_sum_resum`, `sum_sum_ct_entry`). -/
theorem contractionAmplitude₂_eq_dbl (P : Params) (hε' : P.ε ≠ 0)
    (C : Contraction nf nA κ) (φ : Flavoring κ) (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ)
    (fi fo : FermionLine C) (hs : fi.tail = fo.1) (hct : κ fo.1.1 = .fermionCt)
    (hfi : fi.1 ≠ fo.1) (hfo : fo.tail ≠ fo.1) (hc : c (.inl fi) = c (.inl fo))
    (he : ext (.inl fi) = ext (.inl fo)) (hM : P.mass (φ.1 fi.1) = P.mass (φ.1 fo.1))
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) (k : Fin 4 → ℝ) :
    contractionAmplitude₂ P C φ pIn kIn (oneMom c ext k) αOut βIn μ =
      ∑ α, ∑ β, ∑ lor, dblQ P C φ c ext pIn kIn αOut βIn μ fi fo α β lor k *
        ((1 / 16 : ℂ) * dblMrg P φ c ext fi fo α β k) := by
  classical
  have hne : fi ≠ fo := fun h => hfi (by rw [h])
  set M := P.mass (φ.1 fo.1) with hM_def
  set kf : (Fin 4 → ℝ) → Fin 4 → ℝ := fun k => (c (.inl fo) : ℝ) • k + ext (.inl fo) with hkf
  set X : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ := fun k => (P.δ₂ : ℂ) • Dirac.slash (kf k) +
    ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) with hX
  -- the index-term pieces
  obtain ⟨ind, hind⟩ : ∃ ind : (Wick.FermionVertex κ → Fin 4) → (Wick.FermionVertex κ → Fin 4) →
      (Wick.PhotonSlot κ → Fin 4) → ℂ, ind = fun α β lor =>
        if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
          (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
          (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : (Wick.FermionVertex κ → Fin 4) → (Wick.FermionVertex κ → Fin 4) →
      (Wick.PhotonSlot κ → Fin 4) → (Fin 4 → ℝ) → Fin N → ℂ, V = fun α β lor k t =>
        Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
          (psiMomentum₂ C pIn (oneMom c ext k)) (photonMomentum₂ C kIn (oneMom c ext k)) t :=
    ⟨_, rfl⟩
  obtain ⟨Sf, hSf⟩ : ∃ Sf : (Wick.FermionVertex κ → Fin 4) → (Wick.FermionVertex κ → Fin 4) →
      (Fin 4 → ℝ) → FermionLine C → ℂ, Sf = fun α β k f => (1 / I) *
        QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε (oneMom c ext k (.inl f))
          (β f.1) (α f.tail) := ⟨_, rfl⟩
  obtain ⟨Pg, hPg⟩ : ∃ Pg : (Wick.PhotonSlot κ → Fin 4) → (Fin 4 → ℝ) → PhotonLine C → ℂ,
      Pg = fun lor k g => (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
        (oneMom c ext k (.inr g)) (lor g.1) (lor g.head) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : (Wick.FermionVertex κ → Fin 4) → (Wick.FermionVertex κ → Fin 4) →
      (Wick.PhotonSlot κ → Fin 4) → (Fin 4 → ℝ) → ℂ, Q = fun α β lor k => ind α β lor *
        ((∏ t, if t = fo.1.1 then 1 else V α β lor k t) *
          (∏ f, if f = fo then 1 else if f = fi then 1 else Sf α β k f) *
          ∏ g, Pg lor k g) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : (Wick.FermionVertex κ → Fin 4) → (Wick.FermionVertex κ → Fin 4) →
      (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ, G = fun α β k a b =>
        (1 / I) * QED.OneLoop.electronPropagator M P.ε (kf k) (β fi.1) a * (-I * X k a b) *
          ((1 / I) * QED.OneLoop.electronPropagator M P.ε (kf k) b (α fo.tail)) := ⟨_, rfl⟩
  obtain ⟨Mrg, hMrg⟩ : ∃ Mrg : (Wick.FermionVertex κ → Fin 4) → (Wick.FermionVertex κ → Fin 4) →
      (Fin 4 → ℝ) → ℂ, Mrg = fun α β k =>
        I * (affNum M (kf k) (mergeU P.δ₂ P.δm P.m M P.ε 0) (mergeV P.δ₂ P.δm P.m M P.ε 0)
            (β fi.1) (α fo.tail) * (propDenom M P.ε (kf k))⁻¹ +
          affNum M (kf k) (mergeU P.δ₂ P.δm P.m M P.ε 1) (mergeV P.δ₂ P.δm P.m M P.ε 1)
            (β fi.1) (α fo.tail) * ((propDenom M P.ε (kf k))⁻¹ * (propDenom M P.ε (kf k))⁻¹))
    := ⟨_, rfl⟩
  -- momenta of the pair
  have hkfi : ∀ k, oneMom c ext k (.inl fi) = kf k := fun k => by
    simp only [oneMom, hkf, hc, he]
  -- the index term as `Q · G`
  have hterm : ∀ α β lor k, ind α β lor * ((∏ t, V α β lor k t) * (∏ f, Sf α β k f) *
      ∏ g, Pg lor k g) = Q α β lor k * G α β k (α fo.1) (β fo.1) := fun α β lor k => by
    rw [prod_split_one (V α β lor k) fo.1.1, prod_split_two (Sf α β k) hne]
    have hv : V α β lor k fo.1.1 = -I * X k (α fo.1) (β fo.1) := by
      rw [hV]
      dsimp only
      rw [vertexFactor_ctLine _ _ _ _ _ _ _ _ _ _ _ fo.1 hct, psiMomentum₂_line]
      rfl
    have h1 : Sf α β k fi = (1 / I) * QED.OneLoop.electronPropagator M P.ε (kf k) (β fi.1)
        (α fo.1) := by
      rw [hSf]
      simp only [hkfi, hM, hs]
    have h2 : Sf α β k fo = (1 / I) * QED.OneLoop.electronPropagator M P.ε (kf k) (β fo.1)
        (α fo.tail) := by
      rw [hSf]
      rfl
    rw [hv, h1, h2, hQ, hG]
    ring
  -- invariance under the indices of `s`
  have hfo1 : ∀ f : FermionLine C, f ≠ fo → f.1 ≠ fo.1 := fun f hf h => hf (Subtype.ext h)
  have hfo2 : ∀ f : FermionLine C, f ≠ fi → f.tail ≠ fo.1 := fun f hf h =>
    hf (eq_of_tail_eq (h.trans hs.symm))
  have hQu : ∀ α β lor k a b, Q (Function.update α fo.1 a) (Function.update β fo.1 b) lor k =
      Q α β lor k := fun α β lor k a b => by
    have hi : ind (Function.update α fo.1 a) (Function.update β fo.1 b) lor = ind α β lor := by
      have hA : ∀ i t, C.1.1 (.inl i) = .inr t → t ≠ fo.1 := fun i t h ht => by
        have := (tail_spec fi).trans (by rw [hs, ← ht, ← h])
        exact absurd (C.1.1.injective this) (by simp)
      have hB : ∀ t i, C.1.1 (.inr t) = .inl i → t ≠ fo.1 := fun t i h ht => by
        have := tail_spec fo
        rw [← ht, h] at this
        exact absurd this (by simp)
      rw [hind]
      simp only
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
    rw [hQ]
    simp only [hi]
    congr 3
    · refine Finset.prod_congr rfl fun t _ => ?_
      split_ifs with ht
      · rfl
      · rw [hV]
        refine vertexFactor_congr₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun p => ?_) (fun p => ?_)
        · exact Function.update_of_ne (fun h => ht (by rw [← h])) _ _
        · exact Function.update_of_ne (fun h => ht (by rw [← h])) _ _
    · refine Finset.prod_congr rfl fun f _ => ?_
      split_ifs with h1 h2
      · rfl
      · rfl
      · rw [hSf]
        simp only [Function.update_of_ne (hfo1 f h1), Function.update_of_ne (hfo2 f h2)]
  have hGu : ∀ α β k a b, G (Function.update α fo.1 a) (Function.update β fo.1 b) k = G α β k :=
    fun α β k a b => by
      rw [hG]
      simp only [Function.update_of_ne hfi, Function.update_of_ne hfo]
  have hMu : ∀ α β k a b, Mrg (Function.update α fo.1 a) (Function.update β fo.1 b) k = Mrg α β k :=
    fun α β k a b => by
      rw [hMrg]
      simp only [Function.update_of_ne hfi, Function.update_of_ne hfo]
  -- the resummed amplitude
  have hamp : ∀ k, contractionAmplitude₂ P C φ pIn kIn (oneMom c ext k) αOut βIn μ =
      ∑ α, ∑ β, ∑ lor, Q α β lor k * ((1 / 16 : ℂ) * Mrg α β k) := fun k => by
    have h0 : contractionAmplitude₂ P C φ pIn kIn (oneMom c ext k) αOut βIn μ =
        ∑ α, ∑ β, (∑ lor, Q α β lor k) * G α β k (α fo.1) (β fo.1) := by
      unfold contractionAmplitude₂
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun lor _ => ?_
      have := hterm α β lor k
      rw [hind, hV, hSf, hPg] at this
      exact this
    rw [h0]
    have h1 := sum_sum_resum fo.1 (fun α β a b => (∑ lor, Q α β lor k) * G α β k a b)
      (fun α β _ _ => (∑ lor, Q α β lor k) * ((1 / 16 : ℂ) * Mrg α β k))
      (fun α β a b => by funext a' b'; simp only [hQu, hGu])
      (fun α β a b => by funext a' b'; simp only [hQu, hMu])
      (fun α β => by
        simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        congr 1
        rw [hG, hMrg]
        simp only
        rw [sum_sum_ct_entry P.δ₂ P.δm P.m M P.ε hε' (kf k)]
        simp only [nsmul_eq_mul]
        push_cast
        ring)
    rw [h1]
    simp only [Finset.sum_mul]
  rw [hamp k]
  subst hQ hMrg hind hV hSf hPg
  rfl

/-! ### One resummed index term -/

/-- The numerator of a fermion line off the doubled pair (`1` on the pair). -/
noncomputable def dblFe (P : Params) {C : Contraction nf nA κ} (φ : Flavoring κ) (c : Line C → ℤ)
    (ext : Line C → Fin 4 → ℝ) (fi fo : FermionLine C) (α β : Wick.FermionVertex κ → Fin 4)
    (f : FermionLine C) (k : Fin 4 → ℝ) : ℂ :=
  if f = fo then 1 else if f = fi then 1 else
    if c (.inl f) ≠ 0 then (1 / I) * electronNumerator (P.mass (φ.1 f.1))
        ((c (.inl f) : ℝ) • k + ext (.inl f)) (β f.1) (α f.tail)
      else (1 / I) * QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε (ext (.inl f))
        (β f.1) (α f.tail)

/-- The denominator of a fermion line off the doubled pair (`1` on the pair). -/
noncomputable def dblDe (P : Params) {C : Contraction nf nA κ} (φ : Flavoring κ) (c : Line C → ℤ)
    (ext : Line C → Fin 4 → ℝ) (fi fo f : FermionLine C) (k : Fin 4 → ℝ) : ℂ :=
  if f = fo then 1 else if f = fi then 1 else
    if c (.inl f) ≠ 0 then
      (propDenom (P.mass (φ.1 f.1)) P.ε ((c (.inl f) : ℝ) • k + ext (.inl f)))⁻¹ else 1

/-- The numerator of a photon line. -/
noncomputable def dblFg (P : Params) {C : Contraction nf nA κ} (c : Line C → ℤ)
    (ext : Line C → Fin 4 → ℝ) (lor : Wick.PhotonSlot κ → Fin 4) (g : PhotonLine C) : ℂ :=
  if c (.inr g) ≠ 0 then
    (1 / I) * ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)
  else (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ext (.inr g)) (lor g.1)
    (lor g.head)

/-- The photon denominators. -/
noncomputable def dblDg (P : Params) (C : Contraction nf nA κ) (c : Line C → ℤ)
    (ext : Line C → Fin 4 → ℝ) (k : Fin 4 → ℝ) : ℂ :=
  ∏ g : PhotonLine C, if c (.inr g) ≠ 0 then
    (propDenom P.mγ P.ε ((c (.inr g) : ℝ) • k + ext (.inr g)))⁻¹ *
      (propDenom P.Λ P.ε ((c (.inr g) : ℝ) • k + ext (.inr g)))⁻¹ else 1

/-- The fermion denominators of the lines with `p`. -/
noncomputable def dblDF (P : Params) {C : Contraction nf nA κ} (φ : Flavoring κ)
    (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ) (p : FermionLine C → Prop) [DecidablePred p]
    (k : Fin 4 → ℝ) : ℂ :=
  ∏ f, if p f then (propDenom (P.mass (φ.1 f.1)) P.ε ((c (.inl f) : ℝ) • k + ext (.inl f)))⁻¹
    else 1

/-- The entry of `Y₁` (`j = 0`) or `Y₂` (`j = 1`). -/
noncomputable def dblY (P : Params) {C : Contraction nf nA κ} (φ : Flavoring κ) (c : Line C → ℤ)
    (ext : Line C → Fin 4 → ℝ) (fi fo : FermionLine C) (α β : Wick.FermionVertex κ → Fin 4)
    (j : Fin 2) (k : Fin 4 → ℝ) : ℂ :=
  affNum (P.mass (φ.1 fo.1)) ((c (.inl fo) : ℝ) • k + ext (.inl fo))
    (mergeU P.δ₂ P.δm P.m (P.mass (φ.1 fo.1)) P.ε j)
    (mergeV P.δ₂ P.δm P.m (P.mass (φ.1 fo.1)) P.ε j) (β fi.1) (α fo.tail)

/-- The numerator of a resummed index term, without the merged entry. -/
noncomputable def dblNum (P : Params) (C : Contraction nf nA κ) (φ : Flavoring κ)
    (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (fi fo : FermionLine C) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (k : Fin 4 → ℝ) : ℂ :=
  (∏ t, if t = fo.1.1 then 1 else Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
      (psiMomentum₂ C pIn (oneMom c ext k)) (photonMomentum₂ C kIn (oneMom c ext k)) t) *
    (∏ f, dblFe P φ c ext fi fo α β f k) * ∏ g, dblFg P c ext lor g

theorem prod_fermion_dbl (P : Params) {C : Contraction nf nA κ} (φ : Flavoring κ)
    (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ) (fi fo : FermionLine C) (hne : fi ≠ fo)
    (α β : Wick.FermionVertex κ → Fin 4) (k : Fin 4 → ℝ) :
    (∏ f, if f = fo then 1 else if f = fi then 1 else (1 / I) *
        QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε (oneMom c ext k (.inl f))
          (β f.1) (α f.tail)) =
      (∏ f, dblFe P φ c ext fi fo α β f k) * ∏ f, dblDe P φ c ext fi fo f k := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun f _ => ?_
  unfold dblFe dblDe
  by_cases h1 : f = fo
  · simp only [h1, ite_true, mul_one]
  by_cases h2 : f = fi
  · simp only [h2, hne, ite_true, ite_false, mul_one]
  simp only [h1, h2, ite_false]
  exact oneCt_fermion_factor _ _ _ _ _ _ _

theorem prod_photon_dbl (P : Params) (hε : P.ε ≠ 0) (C : Contraction nf nA κ) (c : Line C → ℤ)
    (ext : Line C → Fin 4 → ℝ) (lor : Wick.PhotonSlot κ → Fin 4) (k : Fin 4 → ℝ) :
    (∏ g : PhotonLine C, (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
        (oneMom c ext k (.inr g)) (lor g.1) (lor g.head)) =
      (∏ g, dblFg P c ext lor g) * dblDg P C c ext k := by
  rw [dblDg, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun g _ => oneCt_photon_factor _ _ hε _ _ _ _ _

theorem dblDF_two (P : Params) {C : Contraction nf nA κ} (φ : Flavoring κ) (c : Line C → ℤ)
    (ext : Line C → Fin 4 → ℝ) (fi fo : FermionLine C) (hne : fi ≠ fo)
    (hc : c (.inl fi) = c (.inl fo)) (hc0 : c (.inl fo) ≠ 0) (he : ext (.inl fi) = ext (.inl fo))
    (hM : P.mass (φ.1 fi.1) = P.mass (φ.1 fo.1)) (k : Fin 4 → ℝ) :
    dblDF P φ c ext (fun f => c (.inl f) ≠ 0) k =
      (propDenom (P.mass (φ.1 fo.1)) P.ε ((c (.inl fo) : ℝ) • k + ext (.inl fo)))⁻¹ *
        (propDenom (P.mass (φ.1 fo.1)) P.ε ((c (.inl fo) : ℝ) • k + ext (.inl fo)))⁻¹ *
          ∏ f, dblDe P φ c ext fi fo f k := by
  unfold dblDF
  rw [prod_split_two _ hne]
  dsimp only
  rw [ite_eq_left (show c (.inl fi) ≠ 0 from hc ▸ hc0), ite_eq_left hc0, hc, he, hM]
  rfl

theorem dblDF_one (P : Params) {C : Contraction nf nA κ} (φ : Flavoring κ) (c : Line C → ℤ)
    (ext : Line C → Fin 4 → ℝ) (fi fo : FermionLine C) (hne : fi ≠ fo)
    (hc : c (.inl fi) = c (.inl fo)) (hc0 : c (.inl fo) ≠ 0) (he : ext (.inl fi) = ext (.inl fo))
    (hM : P.mass (φ.1 fi.1) = P.mass (φ.1 fo.1)) (k : Fin 4 → ℝ) :
    dblDF P φ c ext (fun f => c (.inl f) ≠ 0 ∧ f ≠ fo) k =
      (propDenom (P.mass (φ.1 fo.1)) P.ε ((c (.inl fo) : ℝ) • k + ext (.inl fo)))⁻¹ *
          ∏ f, dblDe P φ c ext fi fo f k := by
  unfold dblDF
  rw [prod_split_two _ hne]
  dsimp only
  rw [ite_eq_left (show c (.inl fi) ≠ 0 ∧ fi ≠ fo from ⟨hc ▸ hc0, hne⟩),
    ite_eq_right (show ¬(c (.inl fo) ≠ 0 ∧ fo ≠ fo) from fun h => h.2 rfl), mul_one, hc, he,
    hM]
  congr 1
  refine Finset.prod_congr rfl fun f _ => ?_
  unfold dblDe
  split_ifs <;> simp_all

/-- **A resummed index term in two pieces.** -/
theorem dblTerm_eq (P : Params) (hε : P.ε ≠ 0) (C : Contraction nf nA κ) (φ : Flavoring κ)
    (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ) (fi fo : FermionLine C) (hne : fi ≠ fo)
    (hc : c (.inl fi) = c (.inl fo)) (hc0 : c (.inl fo) ≠ 0) (he : ext (.inl fi) = ext (.inl fo))
    (hM : P.mass (φ.1 fi.1) = P.mass (φ.1 fo.1)) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) (z : ℂ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (k : Fin 4 → ℝ) :
    z * (dblQ P C φ c ext pIn kIn αOut βIn μ fi fo α β lor k *
        ((1 / 16 : ℂ) * dblMrg P φ c ext fi fo α β k)) =
      (z * (1 / 16) * I * (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
          (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
          (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
          (dblNum P C φ c ext pIn kIn fi fo α β lor k * dblY P φ c ext fi fo α β 0 k)) *
          (dblDF P φ c ext (fun f => c (.inl f) ≠ 0 ∧ f ≠ fo) k * dblDg P C c ext k) +
        (z * (1 / 16) * I * (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
          (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
          (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
          (dblNum P C φ c ext pIn kIn fi fo α β lor k * dblY P φ c ext fi fo α β 1 k)) *
          (dblDF P φ c ext (fun f => c (.inl f) ≠ 0) k * dblDg P C c ext k) := by
  rw [dblDF_one P φ c ext fi fo hne hc hc0 he hM, dblDF_two P φ c ext fi fo hne hc hc0 he hM]
  unfold dblQ dblMrg dblNum dblY
  rw [prod_fermion_dbl P φ c ext fi fo hne, prod_photon_dbl P hε]
  ring

/-- The numerator of a piece is an `AffPoly` of degree `oneDeg - 2`. -/
theorem affPoly_dblNum (P : Params) (C : Contraction nf nA κ) (φ : Flavoring κ)
    (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ) (fi fo : FermionLine C) (hne : fi ≠ fo)
    (hct : κ fo.1.1 = .fermionCt) (hc : c (.inl fi) = c (.inl fo)) (hc0 : c (.inl fo) ≠ 0)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (w : ℂ) (j : Fin 2) :
    AffPoly (oneDeg c - 2) fun k =>
      w * (dblNum P C φ c ext pIn kIn fi fo α β lor k * dblY P φ c ext fi fo α β j k) := by
  classical
  have hSV : ∑ t, vDeg c t = 1 + ∑ t, (if t = fo.1.1 then 0 else vDeg c t) := by
    rw [sum_split_one _ fo.1.1, vDeg_line c fo hct hc0]
  have hLF : loopFermionCount c = 2 + ∑ f : FermionLine C,
      (if f = fo then 0 else if f = fi then 0 else if c (.inl f) ≠ 0 then 1 else 0) := by
    unfold loopFermionCount
    rw [Finset.card_filter, sum_split_two _ hne]
    simp only [hc, hc0, ne_eq, not_false_eq_true, ite_true]
  have hVp : AffPoly (∑ t, if t = fo.1.1 then 0 else vDeg c t)
      fun k => ∏ t, if t = fo.1.1 then 1 else Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β
        lor (psiMomentum₂ C pIn (oneMom c ext k)) (photonMomentum₂ C kIn (oneMom c ext k)) t := by
    refine AffPoly.prod _ _ fun t _ => ?_
    by_cases ht : t = fo.1.1
    · simp only [ht, ite_true]
      exact AffPoly.const 1
    · simp only [ht, ite_false]
      exact affPoly_vertexFactor _ _ _ _ _ _ α β lor c ext pIn kIn t
  have hFep : AffPoly (∑ f : FermionLine C,
      (if f = fo then 0 else if f = fi then 0 else if c (.inl f) ≠ 0 then 1 else 0))
      fun k => ∏ f, dblFe P φ c ext fi fo α β f k := by
    refine AffPoly.prod _ _ fun f _ => ?_
    unfold dblFe
    by_cases h1 : f = fo
    · simp only [h1, ite_true]
      exact AffPoly.const 1
    by_cases h2 : f = fi
    · simp only [h2, hne, ite_true, ite_false]
      exact AffPoly.const 1
    by_cases h3 : c (.inl f) = 0
    · simp only [h1, h2, h3, ne_eq, not_true_eq_false, ite_false]
      exact AffPoly.const _
    · simp only [h1, h2, h3, ne_eq, not_false_eq_true, ite_true, ite_false]
      exact (AffPoly.comp_affine (electronNumerator_affine _ _ _) _ _).const_mul _
  have hFgp : AffPoly (∑ _g : PhotonLine C, 0) fun _ => ∏ g, dblFg P c ext lor g :=
    AffPoly.prod _ _ fun g _ => AffPoly.const _
  have hYp : AffPoly 1 (dblY P φ c ext fi fo α β j) := by
    have h := ((AffPoly.comp_affine (electronNumerator_affine (P.mass (φ.1 fo.1)) (β fi.1)
      (α fo.tail)) (c (.inl fo) : ℝ) (ext (.inl fo))).const_mul
        (mergeU P.δ₂ P.δm P.m (P.mass (φ.1 fo.1)) P.ε j)).add
      (AffPoly.const' 1 (mergeV P.δ₂ P.δm P.m (P.mass (φ.1 fo.1)) P.ε j *
        (1 : Matrix (Fin 4) (Fin 4) ℂ) (β fi.1) (α fo.tail)))
    refine (congrArg _ (funext fun k => ?_)).mp h
    simp only [dblY, affNum, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hdeg : 0 + ((∑ t, (if t = fo.1.1 then 0 else vDeg c t)) +
      (∑ f : FermionLine C,
        (if f = fo then 0 else if f = fi then 0 else if c (.inl f) ≠ 0 then 1 else 0)) +
      ∑ _g : PhotonLine C, 0 + 1) ≤ oneDeg c - 2 := by
    have h0 : ∑ _g : PhotonLine C, (0 : ℕ) = 0 := Finset.sum_const_zero
    rw [h0]
    unfold oneDeg
    omega
  have h := ((AffPoly.const w).mul (((hVp.mul hFep).mul hFgp).mul hYp)).mono hdeg
  refine (congrArg _ (funext fun k => ?_)).mp h
  rfl

theorem three_le_oneDeg {C : Contraction nf nA κ} (c : Line C → ℤ) (fi fo : FermionLine C)
    (hne : fi ≠ fo) (hct : κ fo.1.1 = .fermionCt) (hc : c (.inl fi) = c (.inl fo))
    (hc0 : c (.inl fo) ≠ 0) : 3 ≤ oneDeg c ∧ 2 ≤ loopFermionCount c := by
  classical
  have hSV : ∑ t, vDeg c t = 1 + ∑ t, (if t = fo.1.1 then 0 else vDeg c t) := by
    rw [sum_split_one _ fo.1.1, vDeg_line c fo hct hc0]
  have hLF : loopFermionCount c = 2 + ∑ f : FermionLine C,
      (if f = fo then 0 else if f = fi then 0 else if c (.inl f) ≠ 0 then 1 else 0) := by
    unfold loopFermionCount
    rw [Finset.card_filter, sum_split_two _ hne]
    simp only [hc, hc0, ne_eq, not_false_eq_true, ite_true]
  unfold oneDeg
  omega

theorem card_dbl_one {C : Contraction nf nA κ} (c : Line C → ℤ) (fo : FermionLine C)
    (hc0 : c (.inl fo) ≠ 0) :
    Fintype.card {f : FermionLine C // c (.inl f) ≠ 0 ∧ f ≠ fo} + 1 = loopFermionCount c := by
  classical
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun f : FermionLine C => c (.inl f) ≠ 0 ∧ f ≠ fo) =
      (Finset.univ.filter fun f : FermionLine C => c (.inl f) ≠ 0).erase fo := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    exact and_comm
  have hmem : fo ∈ Finset.univ.filter fun f : FermionLine C => c (.inl f) ≠ 0 := by
    simp [hc0]
  rw [h, Finset.card_erase_of_mem hmem, loopFermionCount]
  have := Finset.card_pos.mpr ⟨fo, hmem⟩
  omega

/-- **(T₉′) of one resummed index term** under the doubled-line criterion. -/
theorem jointEnergyFirstIntegrable_dblTerm (P : Params) (hε : 0 < P.ε)
    (C : Contraction nf nA κ) (φ : Flavoring κ) (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ)
    (fi fo : FermionLine C) (hct : κ fo.1.1 = .fermionCt) (hfi : fi.1 ≠ fo.1)
    (hc : c (.inl fi) = c (.inl fo)) (hc0 : c (.inl fo) ≠ 0) (he : ext (.inl fi) = ext (.inl fo))
    (hM : P.mass (φ.1 fi.1) = P.mass (φ.1 fo.1)) (hd : oneDeg c ≤ 6)
    (hn : 4 + oneDeg c < 2 * (loopFermionCount c + 2 * loopPhotonCount c))
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) (z : ℂ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      z * (dblQ P C φ c ext pIn kIn αOut βIn μ fi fo α β lor (ℓ 0) *
        ((1 / 16 : ℂ) * dblMrg P φ c ext fi fo α β (ℓ 0))) := by
  classical
  have hne : fi ≠ fo := fun h => hfi (by rw [h])
  obtain ⟨h3, -⟩ := three_le_oneDeg c fi fo hne hct hc hc0
  have hc₁ := card_dbl_one c fo hc0
  have hc₂ : Fintype.card {f : FermionLine C // c (.inl f) ≠ 0} = loopFermionCount c := by
    rw [Fintype.card_subtype]
    rfl
  set w : ℂ := z * (1 / 16) * I * (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
    (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
    (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) with hw
  have h₁ := jointEnergyFirstIntegrable_oneLines hε C c ext (fun f => P.mass (φ.1 f.1)) P.mγ P.Λ
    (fun f => c (.inl f) ≠ 0 ∧ f ≠ fo) (fun f h => h.1) (by omega) (by omega)
    (affPoly_dblNum P C φ c ext fi fo hne hct hc hc0 pIn kIn α β lor w 0)
  have h₂ := jointEnergyFirstIntegrable_oneLines hε C c ext (fun f => P.mass (φ.1 f.1)) P.mγ P.Λ
    (fun f => c (.inl f) ≠ 0) (fun f h => h) (by omega) (by omega)
    (affPoly_dblNum P C φ c ext fi fo hne hct hc hc0 pIn kIn α β lor w 1)
  refine (congrArg _ (funext fun ℓ => ?_)).mp
    (QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add h₁ h₂)
  rw [dblTerm_eq P hε.ne' C φ c ext fi fo hne hc hc0 he hM]
  simp only [dblDF, dblDg, hw]


/-- **(T₉′) of a one-loop contraction amplitude with a doubled fermion line** at a `fermionCt`
vertex (any vertex kinds and masses, `ε > 0`): `oneDeg ≤ 6` and `4 + oneDeg < 2 n`. -/
theorem jointEnergyFirstIntegrable_oneCtDbl (P : Params) (hε : 0 < P.ε)
    (C : Contraction nf nA κ) (φ : Flavoring κ) (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ)
    (fi fo : FermionLine C) (hs : fi.tail = fo.1) (hct : κ fo.1.1 = .fermionCt)
    (hfi : fi.1 ≠ fo.1) (hfo : fo.tail ≠ fo.1) (hc : c (.inl fi) = c (.inl fo))
    (hc0 : c (.inl fo) ≠ 0) (he : ext (.inl fi) = ext (.inl fo))
    (hM : P.mass (φ.1 fi.1) = P.mass (φ.1 fo.1)) (hd : oneDeg c ≤ 6)
    (hn : 4 + oneDeg c < 2 * (loopFermionCount c + 2 * loopPhotonCount c))
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      z * contractionAmplitude₂ P C φ pIn kIn (oneMom c ext (ℓ 0)) αOut βIn μ := by
  simp only [contractionAmplitude₂_eq_dbl P hε.ne' C φ c ext fi fo hs hct hfi hfo hc he hM,
    Finset.mul_sum]
  exact jointEnergyFirstIntegrable_sum' _ fun α _ => jointEnergyFirstIntegrable_sum' _
    fun β _ => jointEnergyFirstIntegrable_sum' _ fun lor _ =>
      jointEnergyFirstIntegrable_dblTerm P hε C φ c ext fi fo hct hfi hc hc0 he hM hd hn pIn kIn
        αOut βIn μ z α β lor

end QED.GradedProof.X0Deg6

end
