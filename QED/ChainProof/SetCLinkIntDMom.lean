/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkIntCB01
public import QED.Integration.X0Deg6Ward

/-!
# Set (c), family `D`: momenta, the integrand and the `k·k g` part

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58), family `D` of set (c): `QED.ChainProof.SetCLink.repD i s`, two loops, a
`photonCt` vertex `5` on a photon line of a two-loop vertex skeleton, grading `0`.

* `lineMomentum₂_eq_mv`, `photonMomentum₂_eq_pmv`: line and counterterm momenta as integer
  vectors in the loop momenta, `p_in` and `k_in`, decidable by kernel evaluation.
* `regulatedAmplitude_kD`: the integrand as a sum of index terms, with the `photonCt` factor
  `ctF = ctGD + ctKD` split into its `k·k g_{μν}` and `k_μ k_ν` parts.
* `jointEnergyFirstIntegrable_ctG`: (T₉′) of the `k·k g` part, by the scalar merge on a
  counterterm photon line.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.GradedProof.X0 QED.Graded QED.WickModel QED.ChainProof.SetALink
open QED.ChainProof.Enum (fv pc)
open QED.TwoLoop.Enumeration (lineData)

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Integer momentum vectors -/

/-- The momentum `v₀ ℓ₀ + v₁ ℓ₁ + v₂ p + v₃ q` of an integer vector. -/
def mvReal (ℓ : Fin 2 → Fin 4 → ℝ) (p q : Fin 4 → ℝ) : (Fin 4 → ℤ) →+ (Fin 4 → ℝ) where
  toFun v := ((v 0 : ℤ) : ℝ) • ℓ 0 + ((v 1 : ℤ) : ℝ) • ℓ 1 + ((v 2 : ℤ) : ℝ) • p +
    ((v 3 : ℤ) : ℝ) • q
  map_zero' := by simp
  map_add' v w := by
    simp only [Pi.add_apply, Int.cast_add, add_smul]
    abel

/-- The number of vertices of `S` with the incoming external fermion. -/
def cIn (C : Contraction 1 1 κ) (S : Finset (Fin N)) : ℤ :=
  (S.filter fun v => ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inr t) = .inl 0).card

/-- The number of vertices of `S` with the outgoing external fermion. -/
def cOut (C : Contraction 1 1 κ) (S : Finset (Fin N)) : ℤ :=
  (S.filter fun v => ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inl 0) = .inr t).card

/-- The number of vertices of `S` with the external photon. -/
def cK (C : Contraction 1 1 κ) (S : Finset (Fin N)) : ℤ :=
  (S.filter fun v => ∃ a : Wick.PhotonSlot κ, a.1 = v ∧ C.1.2 (.inl 0) = .inr a).card

/-- **The integer momentum vector of a line**: the loop row and, with `p_out = p_in + k_in`, the
coefficients of `p_in` and `k_in`. -/
def mv (C : Contraction 1 1 κ) (l : Line C) : Fin 4 → ℤ :=
  ![rowOf C l 0, rowOf C l 1,
    if edgeChord (lineData C) (edgeOf l) then 0 else
      cIn C (edgeSide (lineData C) (edgeOf l)) - cOut C (edgeSide (lineData C) (edgeOf l)),
    if edgeChord (lineData C) (edgeOf l) then 0 else
      cK C (edgeSide (lineData C) (edgeOf l)) - cOut C (edgeSide (lineData C) (edgeOf l))]

theorem sum_externalMomentum_D (C : Contraction 1 1 κ) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (hmom : pOut 0 = pIn 0 + kIn 0) (S : Finset (Fin N)) :
    ∑ v ∈ S, externalMomentum C pOut pIn kIn v =
      (((cIn C S - cOut C S : ℤ) : ℝ) • pIn 0 + ((cK C S - cOut C S : ℤ) : ℝ) • kIn 0) := by
  simp only [QED.TwoLoop.Insertion.externalMomentum_one_one, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    hmom, cIn, cOut, cK, Int.cast_sub, Int.cast_natCast, sub_smul, ← Nat.cast_smul_eq_nsmul ℝ]
  abel

/-- **A line momentum as its integer vector**, under momentum conservation. -/
theorem lineMomentum₂_eq_mv (C : Contraction 1 1 κ) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) (l : Line C) :
    lineMomentum₂ C pOut pIn kIn ℓ l = mvReal ℓ (pIn 0) (kIn 0) (mv C l) := by
  rw [lineMomentum₂_eq_rowMom, extPart]
  split_ifs with h
  · simp [mvReal, rowMom, rowOf, mv, h]
  · rw [sum_externalMomentum_D C pOut pIn kIn hmom]
    simp [mvReal, rowMom, rowOf, mv, h]
    abel

/-- **The integer momentum vector at a photon field** (`photonMomentum₂`). -/
def pmv (C : Contraction 1 1 κ) (a : Wick.PhotonSlot κ) : Fin 4 → ℤ :=
  (if C.1.2 (.inl 0) = .inr a then ![0, 0, 0, 1] else 0) +
    ∑ g : PhotonLine C, ((if g.head = a then 1 else 0) - (if g.1 = a then 1 else 0) : ℤ) •
      mv C (.inr g)

theorem photonMomentum₂_eq_pmv (C : Contraction 1 1 κ) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) (a : Wick.PhotonSlot κ) :
    photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) a =
      mvReal ℓ (pIn 0) (kIn 0) (pmv C a) := by
  unfold photonMomentum₂ pmv
  rw [map_add, map_sum, Fin.sum_univ_one]
  congr 1
  · split_ifs <;> simp [mvReal]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_zsmul, lineMomentum₂_eq_mv C pOut pIn kIn hmom]
    split_ifs <;> simp

/-- The `photonCt` factor at the momentum `q`. -/
noncomputable def ctF (δ₃ : ℝ) (lor : Wick.PhotonSlot kD → Fin 4) (q : Fin 4 → ℝ) : ℂ :=
  -(I / 2) * ((δ₃ * (Minkowski.dot q q * Minkowski.metric (lor (pc kD 5 0)) (lor (pc kD 5 1)) -
    q (lor (pc kD 5 0)) * q (lor (pc kD 5 1))) : ℝ) : ℂ)

theorem vertexFactor_kD_five (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (kψ : Wick.FermionVertex kD → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot kD → Fin 4 → ℝ) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA 5 = ctF δ₃ lor (kA (pc kD 5 0)) := rfl

theorem kD_pos : ∀ t : Fin 6, kD t ≠ .photonCt → 0 < (kD t).photonSlots := by decide

/-- The photon field of a fermion vertex of `kD`. -/
def slD (v : Wick.FermionVertex kD) : Wick.PhotonSlot kD := ⟨v.1, ⟨0, kD_pos v.1 v.2⟩⟩

theorem vertexFactor_kD_gauge (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (kψ : Wick.FermionVertex kD → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot kD → Fin 4 → ℝ) (v : Wick.FermionVertex kD) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA v.1 =
      I * e * Dirac.gamma (lor (slD v)) (α v) (β v) := by
  obtain ⟨t, ht⟩ := v
  fin_cases t
  all_goals first | rfl | exact absurd rfl ht


/-! ### The line factors -/

variable {F : Type}

open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero electronNumerator electronPropagator_apply
  photonPropagator_eq_mul)

/-- The numerator factor of a line of a `kD` contraction without closed loop. -/
noncomputable def dNum (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4) :
    Line C → (Fin 4 → ℝ) → ℂ
  | .inl f, k => (1 / I) * electronNumerator (Φ.mass Φ.openLine) k (β f.1) (α f.tail)
  | .inr g, _ => (1 / I) *
      ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)

/-- The masses of the denominators of a line. -/
def dMs (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD} : Line C → List ℝ
  | .inl _ => [Φ.mass Φ.openLine]
  | .inr _ => [P.mγ, P.Λ]

/-- The base number of denominators of a line. -/
def dN {C : Contraction 1 1 kD} : Line C → ℕ
  | .inl _ => 1
  | .inr _ => 2

/-- The base numerator degree of a line. -/
def dD {C : Contraction 1 1 kD} : Line C → ℕ
  | .inl _ => 1
  | .inr _ => 0

theorem length_dMs (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 1 kD) :
    (fun l : Line C => (dMs P Φ l).length) = dN := by
  funext l
  rcases l with f | g <;> rfl

/-- The `gauge` vertex factors. -/
noncomputable def gV (e : ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) : ℂ :=
  ∏ t : Fin 6, if t = 5 then 1 else Wick.vertexFactor e 0 0 1 0 1 α β lor 0 0 t

/-- A product of line factors. -/
noncomputable def lineProd {C : Contraction 1 1 kD} (ε : ℝ) (Nf : Line C → (Fin 4 → ℝ) → ℂ)
    (ms : Line C → List ℝ) (k : Line C → Fin 4 → ℝ) : ℂ :=
  ∏ l, Nf l (k l) * dProd ε (ms l) (k l)

theorem affPoly_dNum (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 1 kD)
    (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4) (l : Line C) :
    AffPoly (dD l) (dNum P Φ α β lor l) := by
  rcases l with f | g
  · exact (affPoly_of_affine (electronNumerator_affine _ (β f.1) (α f.tail))).const_mul _
  · exact AffPoly.const _

/-! ### The integrand -/

open scoped Classical in
/-- **The graded integrand of a `kD` contraction without closed loop** as a sum of index terms:
the external constraints, the `photonCt` factor, the `gauge` vertex factors and the line
factors. -/
theorem regulatedAmplitude_kD (P : Params) [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (hε : P.ε ≠ 0) (C : Contraction 1 1 kD)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude P Φ D C 0 pIn kIn k αOut βIn μ =
      ∑ α, ∑ β, ∑ lor, extI C αOut βIn μ α β lor *
        (ctF (P.e ^ 2 * D.d₃ 0) lor (photonMomentum₂ C kIn k (pc kD 5 0)) *
          (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k)) := by
  rw [regulatedAmplitude_zero_eq_openCt P Φ D C hcyc]
  unfold contractionAmplitude₂
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  have hv : ∏ t, Wick.vertexFactor (openCtParams P Φ D).e (openCtParams P Φ D).δ₁
      (openCtParams P Φ D).δ₂ (openCtParams P Φ D).δm (openCtParams P Φ D).δ₃
      (openCtParams P Φ D).m α β lor (psiMomentum₂ C pIn k) (photonMomentum₂ C kIn k) t =
      ctF (P.e ^ 2 * D.d₃ 0) lor (photonMomentum₂ C kIn k (pc kD 5 0)) * gV P.e α β lor := by
    rw [QED.GradedProof.X0Deg6.prod_split_one _ 5, vertexFactor_kD_five]
    congr 1
  have hl : (∏ f : FermionLine C, (1 / I) * QED.OneLoop.electronPropagator
      ((openCtParams P Φ D).mass ((QED.TwoLoop.Insertion.zeroFlavoring kD).1 f.1))
        (openCtParams P Φ D).ε (k (.inl f)) (β f.1) (α f.tail)) *
      (∏ g : PhotonLine C, (1 / I) * QED.OneLoop.photonPropagator (openCtParams P Φ D).mγ
        (openCtParams P Φ D).Λ (openCtParams P Φ D).ε (k (.inr g)) (lor g.1) (lor g.head)) =
      lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k := by
    unfold lineProd
    rw [Fintype.prod_sum_type]
    congr 1
    · refine Finset.prod_congr rfl fun f _ => ?_
      simp only [dNum, dMs, dProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, electronPropagator_apply]
      rw [show (openCtParams P Φ D).mass ((QED.TwoLoop.Insertion.zeroFlavoring kD).1 f.1) =
        Φ.mass Φ.openLine from rfl, show (openCtParams P Φ D).ε = P.ε from rfl]
      ring
    · refine Finset.prod_congr rfl fun g _ => ?_
      rw [show (openCtParams P Φ D).ε = P.ε from rfl, show (openCtParams P Φ D).mγ = P.mγ from rfl,
        show (openCtParams P Φ D).Λ = P.Λ from rfl, photonPropagator_eq_mul P.mγ P.Λ hε]
      simp only [dNum, dMs, dProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      ring
  rw [hv, mul_assoc (ctF _ _ _ * gV _ _ _ _), hl]
  unfold extI
  ring

/-! ### Integrability of a product of line factors -/

/-- **(T₉′) of a product of line factors** passing `PadCrit`. -/
theorem jointEnergyFirstIntegrable_lineProd (C : Contraction 1 1 kD)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε) (z : ℂ)
    (Nf : Line C → (Fin 4 → ℝ) → ℂ) (ms : Line C → List ℝ) (d : Line C → ℕ)
    (hN : ∀ l, AffPoly (d l) (Nf l)) (hcrit : PadCrit (rowOf C) (fun l => (ms l).length) d) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      z * lineProd ε Nf ms (lineMomentum₂ C pOut pIn kIn ℓ) := by
  have h := jointEnergyFirstIntegrable_lines_pad (rowOf C) (extPart C pOut pIn kIn) ms d Nf
    (fun l => Or.inl (hN l)) hcrit hε z
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  simp only [lineProd, dProd, lineMomentum₂_eq_rowMom]

/-! ### The `k·k g` part -/

/-- The `k·k g_{μν}` part of the `photonCt` factor. -/
noncomputable def ctGD (δ₃ : ℝ) (lor : Wick.PhotonSlot kD → Fin 4) (q : Fin 4 → ℝ) : ℂ :=
  -(I / 2) * ((δ₃ * Minkowski.metric (lor (pc kD 5 0)) (lor (pc kD 5 1)) : ℝ) : ℂ) *
    ((Minkowski.dot q q : ℝ) : ℂ)

/-- The `k_μ k_ν` part of the `photonCt` factor. -/
noncomputable def ctKD (δ₃ : ℝ) (lor : Wick.PhotonSlot kD → Fin 4) (q : Fin 4 → ℝ) : ℂ :=
  (I / 2) * (δ₃ : ℂ) * ((q (lor (pc kD 5 0)) : ℂ) * (q (lor (pc kD 5 1)) : ℂ))

theorem ctF_eq (δ₃ : ℝ) (lor : Wick.PhotonSlot kD → Fin 4) (q : Fin 4 → ℝ) :
    ctF δ₃ lor q = ctGD δ₃ lor q + ctKD δ₃ lor q := by
  unfold ctF ctGD ctKD
  push_cast
  ring

theorem dot_neg_neg_D (q : Fin 4 → ℝ) : Minkowski.dot (-q) (-q) = Minkowski.dot q q := by
  simp [Minkowski.dot]

theorem prod_update_split {C : Contraction 1 1 kD} (e : Line C) (f : Line C → ℂ) :
    ∏ l, f l = f e * ∏ l, (if l = e then 1 else f l) :=
  QED.GradedProof.X0Deg6.prod_split_one f e

/-- **The scalar merge on a photon line**: `k·k` times the line factors is the line factors with
the denominator `D_{mγ}` of the line removed, plus `(iε - mγ²)` times the line factors. -/
theorem dot_mul_lineProd (P : Params) (Φ : Lepton.Flavors F) (hε : P.ε ≠ 0)
    {C : Contraction 1 1 kD} (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (g : PhotonLine C) (k : Line C → Fin 4 → ℝ) :
    ((Minkowski.dot (k (.inr g)) (k (.inr g)) : ℝ) : ℂ) *
        lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k =
      lineProd P.ε (dNum P Φ α β lor) (Function.update (dMs P Φ) (.inr g) [P.Λ]) k +
        ((P.ε : ℂ) * I - (P.mγ : ℂ) ^ 2) * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) k := by
  unfold lineProd
  rw [prod_update_split (.inr g), prod_update_split (.inr g) (fun l => dNum P Φ α β lor l (k l) *
    dProd P.ε (Function.update (dMs P Φ) (.inr g) [P.Λ] l) (k l))]
  have hR : ∏ l, (if l = Sum.inr g then 1 else dNum P Φ α β lor l (k l) *
      dProd P.ε (Function.update (dMs P Φ) (.inr g) [P.Λ] l) (k l)) =
      ∏ l, (if l = Sum.inr g then 1 else dNum P Φ α β lor l (k l) *
        dProd P.ε (dMs P Φ l) (k l)) :=
    Finset.prod_congr rfl fun l _ => by
      split_ifs with h
      · rfl
      · rw [Function.update_of_ne h]
  rw [hR, Function.update_self]
  have hm := QED.GradedProof.X0Deg6.dot_mul_propDenom_inv P.mγ hε (k (.inr g))
  generalize (∏ l, (if l = Sum.inr g then 1 else
    dNum P Φ α β lor l (k l) * dProd P.ε (dMs P Φ l) (k l))) = R
  rw [show dMs P Φ (Sum.inr g : Line C) = [P.mγ, P.Λ] from rfl]
  simp only [dProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  linear_combination (dNum P Φ α β lor (.inr g) (k (.inr g)) *
    (propDenom P.Λ P.ε (k (.inr g)))⁻¹ * R) * hm

theorem length_update_dMs (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (e : Line C) (ms : List ℝ) :
    (fun l => (Function.update (dMs P Φ) e ms l).length) = Function.update dN e ms.length := by
  funext l
  by_cases h : l = e
  · subst h; simp
  · simp only [Function.update_of_ne h]
    exact congrFun (length_dMs P Φ C) l

theorem dot_kct (C : Contraction 1 1 kD) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (hmom : pOut 0 = pIn 0 + kIn 0) (g : PhotonLine C)
    (hρ : pmv C (pc kD 5 0) = mv C (.inr g) ∨ pmv C (pc kD 5 0) = -mv C (.inr g))
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    Minkowski.dot (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0))
        (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)) =
      Minkowski.dot (lineMomentum₂ C pOut pIn kIn ℓ (.inr g))
        (lineMomentum₂ C pOut pIn kIn ℓ (.inr g)) := by
  rw [photonMomentum₂_eq_pmv C pOut pIn kIn hmom, lineMomentum₂_eq_mv C pOut pIn kIn hmom]
  rcases hρ with h | h
  · rw [h]
  · rw [h, map_neg, dot_neg_neg_D]

/-- **(T₉′) of the `k·k g` part**, from the merge on the photon line `g` and two tests. -/
theorem jointEnergyFirstIntegrable_ctG (P : Params) (Φ : Lepton.Flavors F) (hε : 0 < P.ε)
    (δ₃ : ℝ) (C : Contraction 1 1 kD) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) (g : PhotonLine C)
    (hρ : pmv C (pc kD 5 0) = mv C (.inr g) ∨ pmv C (pc kD 5 0) = -mv C (.inr g))
    (h₀ : PadCrit (rowOf C) (Function.update dN (.inr g) 1) dD) (h₁ : PadCrit (rowOf C) dN dD) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => ∑ α, ∑ β, ∑ lor,
      extI C αOut βIn μ α β lor *
        (ctGD δ₃ lor (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)) *
          (gV P.e α β lor *
            lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (lineMomentum₂ C pOut pIn kIn ℓ))) := by
  refine jointEnergyFirstIntegrable_sum' _ fun α _ => jointEnergyFirstIntegrable_sum' _ fun β _ =>
    jointEnergyFirstIntegrable_sum' _ fun lor _ => ?_
  set z : ℂ := extI C αOut βIn μ α β lor *
    (-(I / 2) * ((δ₃ * Minkowski.metric (lor (pc kD 5 0)) (lor (pc kD 5 1)) : ℝ) : ℂ)) *
      gV P.e α β lor with hz
  have hA := jointEnergyFirstIntegrable_lineProd C pOut pIn kIn hε z (dNum P Φ α β lor)
    (Function.update (dMs P Φ) (.inr g) [P.Λ]) dD (affPoly_dNum P Φ C α β lor)
    (by rw [length_update_dMs]; exact h₀)
  have hB := jointEnergyFirstIntegrable_lineProd C pOut pIn kIn hε
    (z * ((P.ε : ℂ) * I - (P.mγ : ℂ) ^ 2)) (dNum P Φ α β lor) (dMs P Φ) dD
    (affPoly_dNum P Φ C α β lor) (by rw [length_dMs]; exact h₁)
  refine (congrArg _ (funext fun ℓ => ?_)).mp
    (QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add hA hB)
  simp only [ctGD, dot_kct C pOut pIn kIn hmom g hρ]
  have h := dot_mul_lineProd P Φ hε.ne' α β lor g (lineMomentum₂ C pOut pIn kIn ℓ)
  linear_combination (-z) * h

end QED.ChainProof.SetCLink

end
