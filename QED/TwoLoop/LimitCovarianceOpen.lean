/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParametricBridgeC
public import QED.TwoLoop.ParametricBridgeS
public import QED.TwoLoop.ClassIntegrable
public import QED.TwoLoop.LimitCovarianceLorentz
import Mathlib.Tactic.Ring

/-!
# The open-line class numerators as chains, and their covariance

Part of obligation O2-20 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). The six classes
`L, X, C±, S±` of five gauge vertices share the open fermion line `0 → 1 → 2 → 3 → 4`; they
differ in the photon pairing `photonPerm e [(a, b), (c, d)]`. For such a contraction the
numerator `QED.TwoLoop.Bridge.amplitudeNumerator` is the chain

`(ie)⁵ (1/i)⁴ ∑_l [l_e = μ] η'_{l_a l_b} η'_{l_c l_d} (γ^{l₄} E₃ γ^{l₃} E₂ γ^{l₂} E₁ γ^{l₁} E₀ γ^{l₀})_{αβ}`

with `E_k = m_k - k̸_k` the propagator numerators and `η'_{xy} = (1/i) g_{xy} (Λ² - m_γ²)`
(`amplitudeNumerator_eq_chain`, with the class facts as hypotheses). From the chain form, the
numerator is covariant (`classNumM_cov`): for a spinor lift `(S, T)` of `L` with `L` fixing
`p, p'`, `S N^μ(L ℓ) T = L^μ_ν N^ν(ℓ)` as matrices in the external spinor indices.
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.LimitCovariance

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.Dirac

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The photon fields of the five gauge vertices. -/
local notation "PS" => Wick.PhotonSlot (gauges 5)

/-! ### The spinor sum of the open line -/

/-- The open-line chain `G₄ E₃ G₃ E₂ G₂ E₁ G₁ E₀ G₀`. -/
def openChain (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ) (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  G 4 * E 3 * G 3 * E 2 * G 2 * E 1 * G 1 * E 0 * G 0

/-- The two spinor index families as ten values, the two fixed by the external fields last. -/
def openSpinEquiv :
    (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (FV → Fin 4) × (FV → Fin 4) where
  toFun := fun ⟨a0, b1, a1, b2, a2, b3, a3, b4, a4, b0⟩ =>
    (fun t => ![a0, a1, a2, a3, a4] t.1, fun t => ![b0, b1, b2, b3, b4] t.1)
  invFun p := (p.1 (fv5 0), p.2 (fv5 1), p.1 (fv5 1), p.2 (fv5 2), p.1 (fv5 2), p.2 (fv5 3),
    p.1 (fv5 3), p.2 (fv5 4), p.1 (fv5 4), p.2 (fv5 0))
  left_inv x := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := x
    rfl
  right_inv p := by
    obtain ⟨α, β⟩ := p
    refine Prod.ext (funext fun t => ?_) (funext fun t => ?_) <;>
      · obtain ⟨j, hj⟩ := t
        fin_cases j <;> rfl

theorem openSpinEquiv_apply (a0 b1 a1 b2 a2 b3 a3 b4 a4 b0 : Fin 4) :
    (openSpinEquiv (a0, b1, a1, b2, a2, b3, a3, b4, a4, b0)).1 (fv5 0) = a0 ∧
    (openSpinEquiv (a0, b1, a1, b2, a2, b3, a3, b4, a4, b0)).1 (fv5 1) = a1 ∧
    (openSpinEquiv (a0, b1, a1, b2, a2, b3, a3, b4, a4, b0)).1 (fv5 2) = a2 ∧
    (openSpinEquiv (a0, b1, a1, b2, a2, b3, a3, b4, a4, b0)).1 (fv5 3) = a3 ∧
    (openSpinEquiv (a0, b1, a1, b2, a2, b3, a3, b4, a4, b0)).1 (fv5 4) = a4 ∧
    (openSpinEquiv (a0, b1, a1, b2, a2, b3, a3, b4, a4, b0)).2 (fv5 0) = b0 ∧
    (openSpinEquiv (a0, b1, a1, b2, a2, b3, a3, b4, a4, b0)).2 (fv5 1) = b1 ∧
    (openSpinEquiv (a0, b1, a1, b2, a2, b3, a3, b4, a4, b0)).2 (fv5 2) = b2 ∧
    (openSpinEquiv (a0, b1, a1, b2, a2, b3, a3, b4, a4, b0)).2 (fv5 3) = b3 ∧
    (openSpinEquiv (a0, b1, a1, b2, a2, b3, a3, b4, a4, b0)).2 (fv5 4) = b4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The spinor sum of the open line** `0 → 1 → 2 → 3 → 4`, the index `αe` of the `Ψ̄` of
vertex `4` and `βe` of the `Ψ` of vertex `0` fixed. -/
theorem openSpinSum (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ) (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (αe βe : Fin 4) :
    ∑ α : FV → Fin 4, ∑ β : FV → Fin 4,
      (if α (fv5 4) = αe ∧ β (fv5 0) = βe then (1 : ℂ) else 0) *
        (G 0 (α (fv5 0)) (β (fv5 0)) * G 1 (α (fv5 1)) (β (fv5 1)) *
          G 2 (α (fv5 2)) (β (fv5 2)) * G 3 (α (fv5 3)) (β (fv5 3)) *
          G 4 (α (fv5 4)) (β (fv5 4)) *
          (E 0 (β (fv5 1)) (α (fv5 0)) * E 1 (β (fv5 2)) (α (fv5 1)) *
            E 2 (β (fv5 3)) (α (fv5 2)) * E 3 (β (fv5 4)) (α (fv5 3)))) =
      openChain G E αe βe := by
  rw [← Fintype.sum_prod_type', ← openSpinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp only [openSpinEquiv_apply]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [openChain, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring


theorem openSpinSum_flat (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (αe βe : Fin 4) :
    ∑ α : FV → Fin 4, ∑ β : FV → Fin 4,
      (if α (fv5 4) = αe ∧ β (fv5 0) = βe then (1 : ℂ) else 0) *
        G 0 (α (fv5 0)) (β (fv5 0)) * G 1 (α (fv5 1)) (β (fv5 1)) *
          G 2 (α (fv5 2)) (β (fv5 2)) * G 3 (α (fv5 3)) (β (fv5 3)) *
          G 4 (α (fv5 4)) (β (fv5 4)) *
          E 0 (β (fv5 1)) (α (fv5 0)) * E 1 (β (fv5 2)) (α (fv5 1)) *
            E 2 (β (fv5 3)) (α (fv5 2)) * E 3 (β (fv5 4)) (α (fv5 3)) =
      openChain G E αe βe := by
  rw [← openSpinSum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ### The chain form of the numerator -/

/-- The Kronecker delta `[x = μ]`. -/
def kron (μ x : Fin 4) : ℂ := if x = μ then 1 else 0

theorem sum_kron_mul {M : Type*} [AddCommMonoid M] [Module ℂ M] (μ : Fin 4) (f : Fin 4 → M) :
    ∑ x, kron μ x • f x = f μ := by
  simp [kron]

/-- The combined Pauli–Villars photon factor `(1/i) g_{xy} (Λ² - m_γ²)`. -/
noncomputable def pvEta (P : Params) (x y : Fin 4) : ℂ :=
  (1 / I) * ((Minkowski.metric x y * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)

theorem vertexFactor_gauge5 (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : FV → Fin 4) (lor : PS → Fin 4)
    (kψ : FV → Fin 4 → ℝ) (kA : PS → Fin 4 → ℝ) (t : Fin 5) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * gamma (lor (ps5 t)) (α (fv5 t)) (β (fv5 t)) :=
  rfl

theorem ite_and_three (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    (if A ∧ B ∧ C then (1 : ℂ) else 0) =
      (if A ∧ B then (1 : ℂ) else 0) * (if C then (1 : ℂ) else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC]

/-- Sums over the functions on the photon fields are sums over functions on the vertices. -/
theorem sum_ps5_fun {M : Type*} [AddCommMonoid M] (g : (PS → Fin 4) → M) :
    ∑ lor, g lor = ∑ l : Fin 5 → Fin 4, g (fun s => l s.1) := by
  let e : (Fin 5 → Fin 4) ≃ (PS → Fin 4) :=
    { toFun := fun l s => l s.1
      invFun := fun lor t => lor (ps5 t)
      left_inv := fun _ => rfl
      right_inv := fun lor => by
        funext s
        obtain ⟨j, b⟩ := s
        have hb : b = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.mp b.2)
        subst hb
        rfl }
  exact (e.sum_comp g).symm

/-- **The numerator of a contraction with the open line `0 → ⋯ → 4` as a chain**, given the
facts about its lines: the fermion lines `line i` from `i` to `i + 1`, the photon lines `a b`
and `c d`, and the external photon at `e`. -/
theorem amplitudeNumerator_eq_chain (P : Params) (C : Contraction 1 1 (gauges 5))
    (φ : Flavoring (gauges 5)) (pIn kIn : Fin 1 → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (line : Fin 4 → FermionLine C)
    (hfl : ∀ [Fintype (FermionLine C)] (g : FermionLine C → ℂ),
      ∏ f, g f = g (line 0) * g (line 1) * g (line 2) * g (line 3))
    (hval : (line 0).1 = fv5 1 ∧ (line 1).1 = fv5 2 ∧ (line 2).1 = fv5 3 ∧ (line 3).1 = fv5 4)
    (htail : (line 0).tail = fv5 0 ∧ (line 1).tail = fv5 1 ∧ (line 2).tail = fv5 2 ∧
      (line 3).tail = fv5 3)
    (e a b c d : Fin 5)
    (hph : ∀ [Fintype (PhotonLine C)] (h : PS → PS → ℂ),
      ∏ g : PhotonLine C, h g.1 g.head = h (ps5 a) (ps5 b) * h (ps5 c) (ps5 d))
    (hout : ∀ (i : Fin 1) (t : FV), C.1.1 (.inl i) = .inr t ↔ t = fv5 4)
    (hin : ∀ (t : FV) (i : Fin 1), C.1.1 (.inr t) = .inl i ↔ t = fv5 0)
    (hA : ∀ (j : Fin 1) (s : PS), C.1.2 (.inl j) = .inr s ↔ s = ps5 e) :
    amplitudeNumerator P C φ pIn kIn k αOut βIn μ =
      (I * P.e) ^ 5 * (1 / I) ^ 4 * ∑ l : Fin 5 → Fin 4,
        kron (μ 0) (l e) * pvEta P (l a) (l b) * pvEta P (l c) (l d) *
          openChain (fun t => gamma (l t))
            (fun i => electronNumerator (P.mass (φ.1 (line i).1)) (k (.inl (line i))))
            (αOut 0) (βIn 0) := by
  classical
  obtain ⟨v0, v1, v2, v3⟩ := hval
  obtain ⟨t0, t1, t2, t3⟩ := htail
  unfold amplitudeNumerator
  simp only [hout, hin, hA, forall_eq, Fin.forall_fin_one]
  simp only [vertexFactor_gauge5, Fin.prod_univ_five, hfl, v0, v1, v2, v3, t0, t1, t2, t3]
  have hph' : ∀ lor : PS → Fin 4, ∏ g : PhotonLine C,
      (1 / I * ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)) =
        pvEta P (lor (ps5 a)) (lor (ps5 b)) * pvEta P (lor (ps5 c)) (lor (ps5 d)) :=
    fun lor => hph (fun x y => pvEta P (lor x) (lor y))
  simp only [hph']
  rw [(Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  have hterm : ∀ (lor : PS → Fin 4) (α β : FV → Fin 4),
      (if α (fv5 4) = αOut 0 ∧ β (fv5 0) = βIn 0 ∧ lor (ps5 e) = μ 0 then (1 : ℂ) else 0) *
        (I * P.e * gamma (lor (ps5 0)) (α (fv5 0)) (β (fv5 0)) *
          (I * P.e * gamma (lor (ps5 1)) (α (fv5 1)) (β (fv5 1))) *
          (I * P.e * gamma (lor (ps5 2)) (α (fv5 2)) (β (fv5 2))) *
          (I * P.e * gamma (lor (ps5 3)) (α (fv5 3)) (β (fv5 3))) *
          (I * P.e * gamma (lor (ps5 4)) (α (fv5 4)) (β (fv5 4))) *
          (1 / I * electronNumerator (P.mass (φ.1 (fv5 1))) (k (.inl (line 0)))
              (β (fv5 1)) (α (fv5 0)) *
            (1 / I * electronNumerator (P.mass (φ.1 (fv5 2))) (k (.inl (line 1)))
              (β (fv5 2)) (α (fv5 1))) *
            (1 / I * electronNumerator (P.mass (φ.1 (fv5 3))) (k (.inl (line 2)))
              (β (fv5 3)) (α (fv5 2))) *
            (1 / I * electronNumerator (P.mass (φ.1 (fv5 4))) (k (.inl (line 3)))
              (β (fv5 4)) (α (fv5 3)))) *
          (pvEta P (lor (ps5 a)) (lor (ps5 b)) * pvEta P (lor (ps5 c)) (lor (ps5 d)))) =
      ((if lor (ps5 e) = μ 0 then (1 : ℂ) else 0) * ((I * P.e) ^ 5 * (1 / I) ^ 4 *
          (pvEta P (lor (ps5 a)) (lor (ps5 b)) * pvEta P (lor (ps5 c)) (lor (ps5 d))))) *
        ((if α (fv5 4) = αOut 0 ∧ β (fv5 0) = βIn 0 then (1 : ℂ) else 0) *
          ((fun t => gamma (lor (ps5 t))) 0 (α (fv5 0)) (β (fv5 0)) *
            (fun t => gamma (lor (ps5 t))) 1 (α (fv5 1)) (β (fv5 1)) *
            (fun t => gamma (lor (ps5 t))) 2 (α (fv5 2)) (β (fv5 2)) *
            (fun t => gamma (lor (ps5 t))) 3 (α (fv5 3)) (β (fv5 3)) *
            (fun t => gamma (lor (ps5 t))) 4 (α (fv5 4)) (β (fv5 4)) *
            ((fun i => electronNumerator (P.mass (φ.1 (line i).1)) (k (.inl (line i)))) 0
                (β (fv5 1)) (α (fv5 0)) *
              (fun i => electronNumerator (P.mass (φ.1 (line i).1)) (k (.inl (line i)))) 1
                (β (fv5 2)) (α (fv5 1)) *
              (fun i => electronNumerator (P.mass (φ.1 (line i).1)) (k (.inl (line i)))) 2
                (β (fv5 3)) (α (fv5 2)) *
              (fun i => electronNumerator (P.mass (φ.1 (line i).1)) (k (.inl (line i)))) 3
                (β (fv5 4)) (α (fv5 3))))) := by
    intro lor α β
    simp only [v0, v1, v2, v3]
    rw [ite_and_three]
    ring
  simp only [hterm, ← Finset.mul_sum]
  rw [sum_ps5_fun, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [ps5]
  rw [openSpinSum (fun t => gamma (l t))
    (fun i => electronNumerator (P.mass (φ.1 (line i).1)) (k (.inl (line i))))]
  by_cases h : l e = μ 0 <;> simp only [h, kron, ite_true, ite_false] <;> ring


/-! ### Covariance of the chain form -/

/-- Sums over functions `Fin 5 → Fin 4` are five nested sums. -/
theorem sum_fin5_fun {M : Type*} [AddCommMonoid M] (g : (Fin 5 → Fin 4) → M) :
    ∑ l, g l = ∑ a₀, ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, g ![a₀, a₁, a₂, a₃, a₄] := by
  let e : (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃ (Fin 5 → Fin 4) :=
    { toFun := fun a => ![a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2]
      invFun := fun l => (l 0, l 1, l 2, l 3, l 4)
      left_inv := fun _ => rfl
      right_inv := fun l => by
        funext t
        fin_cases t <;> rfl }
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-- The chain is multilinear in the five vertex matrices. -/
theorem openChain_sum (a : Fin 5 → Fin 4 → ℂ) (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    openChain (fun t => ∑ z, a t z • X z) E =
      ∑ l : Fin 5 → Fin 4, (∏ t, a t (l t)) • openChain (fun t => X (l t)) E := by
  rw [sum_fin5_fun]
  simp only [openChain, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Fin.prod_univ_five]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  simp only [mul_assoc]
  rfl


section Cov

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

theorem pvEta_pair (h : IsSpinLift L S T) (P : Params) (u v : Fin 4) :
    ∑ x, ∑ y, pvEta P x y * (((L x u : ℝ) : ℂ) * ((L y v : ℝ) : ℂ)) = pvEta P u v := by
  have hr := h.lorentz_right u v
  have hc : ((∑ a, ∑ b, L a u * L b v * Minkowski.metric a b : ℝ) : ℂ) =
      ((Minkowski.metric u v : ℝ) : ℂ) := by rw [hr]
  simp only [pvEta, ofReal_mul, ofReal_sum] at hc ⊢
  simp only [← hc, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem five_sum (μ : Fin 4) (w Lc : Fin 4 → Fin 4 → ℂ) (A : Fin 5 → Fin 4) :
    ∑ a₀, ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, kron μ a₀ * w a₁ a₂ * w a₃ a₄ *
        (Lc a₀ (A 0) * Lc a₁ (A 1) * Lc a₂ (A 2) * Lc a₃ (A 3) * Lc a₄ (A 4)) =
      Lc μ (A 0) * (∑ a₃, ∑ a₄, w a₃ a₄ * (Lc a₃ (A 3) * Lc a₄ (A 4))) *
        (∑ a₁, ∑ a₂, w a₁ a₂ * (Lc a₁ (A 1) * Lc a₂ (A 2))) := by
  have e : ∀ a₀, ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, kron μ a₀ * w a₁ a₂ * w a₃ a₄ *
      (Lc a₀ (A 0) * Lc a₁ (A 1) * Lc a₂ (A 2) * Lc a₃ (A 3) * Lc a₄ (A 4)) =
      kron μ a₀ • (Lc a₀ (A 0) * (∑ a₃, ∑ a₄, w a₃ a₄ * (Lc a₃ (A 3) * Lc a₄ (A 4))) *
        (∑ a₁, ∑ a₂, w a₁ a₂ * (Lc a₁ (A 1) * Lc a₂ (A 2)))) := fun a₀ => by
    simp only [smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [e]
  exact sum_kron_mul μ _

/-- **The photon weight**: contracting the photon factors and the external constraint with
`L` on every vertex index gives the same structure at the new indices. -/
theorem photonWeight (h : IsSpinLift L S T) (P : Params) (π : Equiv.Perm (Fin 5)) (μ : Fin 4)
    (z : Fin 5 → Fin 4) :
    ∑ l : Fin 5 → Fin 4, kron μ (l (π 0)) * pvEta P (l (π 1)) (l (π 2)) *
        pvEta P (l (π 3)) (l (π 4)) * ∏ t, ((L (l t) (z t) : ℝ) : ℂ) =
      ((L μ (z (π 0)) : ℝ) : ℂ) * pvEta P (z (π 1)) (z (π 2)) * pvEta P (z (π 3)) (z (π 4)) := by
  have hsum : ∑ l : Fin 5 → Fin 4, kron μ (l (π 0)) * pvEta P (l (π 1)) (l (π 2)) *
        pvEta P (l (π 3)) (l (π 4)) * ∏ t, ((L (l t) (z t) : ℝ) : ℂ) =
      ∑ l : Fin 5 → Fin 4, kron μ (l 0) * pvEta P (l 1) (l 2) * pvEta P (l 3) (l 4) *
        ∏ s, ((L (l s) (z (π s)) : ℝ) : ℂ) := by
    refine Fintype.sum_equiv (Equiv.arrowCongr π.symm (Equiv.refl (Fin 4))) _ _ fun l => ?_
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, Equiv.symm_symm]
    congr 1
    exact (Equiv.prod_comp π fun t => ((L (l t) (z t) : ℝ) : ℂ)).symm
  rw [hsum, sum_fin5_fun]
  simp only [Fin.prod_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  rw [five_sum μ (pvEta P) (fun x y => ((L x y : ℝ) : ℂ)) (fun s => z (π s)), pvEta_pair h,
    pvEta_pair h]
  ring

theorem mul_openChain_mul (h : IsSpinLift L S T) (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    S * openChain G E * T = openChain (fun t => S * G t * T) (fun i => S * E i * T) := by
  simp only [openChain, h.mul_mul_mul]

/-- The chain form of a class numerator, for the photon pairing given by `π`: external photon
at `π 0`, internal photons `π 1 π 2` and `π 3 π 4`. -/
noncomputable def chainNum (P : Params) (π : Equiv.Perm (Fin 5))
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ l : Fin 5 → Fin 4, (kron μ (l (π 0)) * pvEta P (l (π 1)) (l (π 2)) *
    pvEta P (l (π 3)) (l (π 4))) • openChain (fun t => gamma (l t)) E

/-- **Covariance of the chain form.** -/
theorem mul_chainNum_mul (h : IsSpinLift L S T) (P : Params) (π : Equiv.Perm (Fin 5))
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    S * chainNum P π E μ * T = vecAct L (chainNum P π (fun i => S * E i * T)) μ := by
  simp only [chainNum, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_openChain_mul h, h.mul_gamma_mul, openChain_sum, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [vecAct, chainNum, Finset.smul_sum, smul_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [← Finset.sum_smul, ← Finset.sum_smul]
  congr 1
  have hw := photonWeight h P π μ l'
  simp only [← mul_assoc] at hw ⊢
  rw [hw]
  simp [kron, mul_assoc]

end Cov


/-! ### The class numerators -/

/-- The class numerator in the chain form, from the facts about the class lines. -/
theorem classNumeratorE_eq_chainNum {c : Class5} (π : Equiv.Perm (Fin 5))
    (line : Fin 4 → FermionLine c.rep)
    (hfl : ∀ [Fintype (FermionLine c.rep)] (g : FermionLine c.rep → ℂ),
      ∏ f, g f = g (line 0) * g (line 1) * g (line 2) * g (line 3))
    (hval : (line 0).1 = fv5 1 ∧ (line 1).1 = fv5 2 ∧ (line 2).1 = fv5 3 ∧ (line 3).1 = fv5 4)
    (htail : (line 0).tail = fv5 0 ∧ (line 1).tail = fv5 1 ∧ (line 2).tail = fv5 2 ∧
      (line 3).tail = fv5 3)
    (hph : ∀ [Fintype (PhotonLine c.rep)] (h : PS → PS → ℂ),
      ∏ g : PhotonLine c.rep, h g.1 g.head = h (ps5 (π 1)) (ps5 (π 2)) * h (ps5 (π 3)) (ps5 (π 4)))
    (hout : ∀ (i : Fin 1) (t : FV), c.rep.1.1 (.inl i) = .inr t ↔ t = fv5 4)
    (hin : ∀ (t : FV) (i : Fin 1), c.rep.1.1 (.inr t) = .inl i ↔ t = fv5 0)
    (hA : ∀ (j : Fin 1) (s : PS), c.rep.1.2 (.inl j) = .inr s ↔ s = ps5 (π 0))
    (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
      chainNum P π (fun i => electronNumerator P.m
        (classMomE c (pIn 0) (pOut 0) ℓ (.inl (line i)))) (μ 0) (αOut 0) (βIn 0) := by
  rw [classNumeratorE, amplitudeNumerator_eq_chain P c.rep zeroFlavoring pIn kIn _ αOut βIn μ line
    hfl hval htail (π 0) (π 1) (π 2) (π 3) (π 4) hph hout hin hA]
  simp only [chainNum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rfl

/-- The external momenta of an open class are fixed by `L` when `p, p'` are. -/
theorem mulVec_extMomenta {L : Matrix (Fin 4) (Fin 4) ℝ} {p p' : Fin 4 → ℝ}
    (hp : L *ᵥ p = p) (hp' : L *ᵥ p' = p') (c : Class5) (i : Fin 6) :
    L *ᵥ extMomenta c p p' i = extMomenta c p p' i := by
  cases c <;> fin_cases i <;>
    simp [extMomenta, QED.Integration.TwoLoop.classLXMomenta,
      QED.Integration.TwoLoop.classCpSpMomenta, QED.Integration.TwoLoop.classCmSmMomenta,
      QED.Integration.TwoLoop.classVPMomenta, hp, hp']

theorem lineMomentum_loopAct {m : ℕ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → Fin 4 → ℝ) (i : Fin (m + 1))
    (hq : L *ᵥ q i = q i) (ℓ : Fin 2 → Fin 4 → ℝ) :
    QED.Integration.TwoLoop.lineMomentum α q i (loopAct L ℓ) =
      L *ᵥ QED.Integration.TwoLoop.lineMomentum α q i ℓ := by
  funext μ
  have h := congrFun hq μ
  simp only [Matrix.mulVec, dotProduct] at h
  simp only [QED.Integration.TwoLoop.lineMomentum, loopAct, Matrix.mulVec, dotProduct,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [h, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem classMomE_loopAct {L : Matrix (Fin 4) (Fin 4) ℝ} {p p' : Fin 4 → ℝ}
    (hp : L *ᵥ p = p) (hp' : L *ᵥ p' = p') (c : Class5) (ℓ : Fin 2 → Fin 4 → ℝ)
    (f : Line c.rep) : classMomE c p p' (loopAct L ℓ) f = L *ᵥ classMomE c p p' ℓ f :=
  lineMomentum_loopAct _ _ _ (mulVec_extMomenta hp hp' c _) ℓ

/-- The class numerator as a matrix in the external spinor indices, at on-shell external
momenta `p, p'` and photon momentum `p' - p`. -/
noncomputable def classNumM (c : Class5) (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => classNumeratorE c P (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (fun _ => i) (fun _ => j) (fun _ => μ) ℓ

theorem classNumM_cov_of_chain {c : Class5} (π : Equiv.Perm (Fin 5))
    (line : Fin 4 → FermionLine c.rep)
    (heq : ∀ (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
      (ℓ : Fin 2 → Fin 4 → ℝ),
      classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
        chainNum P π (fun i => electronNumerator P.m
          (classMomE c (pIn 0) (pOut 0) ℓ (.inl (line i)))) (μ 0) (αOut 0) (βIn 0))
    {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ} (h : IsSpinLift L S T)
    {p p' : Fin 4 → ℝ} (hp : L *ᵥ p = p) (hp' : L *ᵥ p' = p') (P : Params) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * classNumM c P p p' μ (loopAct L ℓ) * T = vecAct L (fun ν => classNumM c P p p' ν ℓ) μ := by
  have hM : ∀ ν ℓ', classNumM c P p p' ν ℓ' = ((I * P.e) ^ 5 * (1 / I) ^ 4) •
      chainNum P π (fun i => electronNumerator P.m (classMomE c p p' ℓ' (.inl (line i)))) ν := by
    intro ν ℓ'
    ext i j
    simp only [classNumM, Matrix.of_apply, heq, Matrix.smul_apply, smul_eq_mul]
  simp only [hM, Matrix.mul_smul, Matrix.smul_mul, mul_chainNum_mul h, classMomE_loopAct hp hp',
    h.mul_electronNumerator_mul]
  rw [vecAct_smul L _ _ μ]


/-! ### The six open classes -/

/-- The photon pairing of `L` as a permutation. -/
noncomputable def permL : Equiv.Perm (Fin 5) := Equiv.ofBijective (![2, 0, 4, 1, 3] : Fin 5 → Fin 5) (by decide)

theorem chain_L (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    classNumeratorE .L P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
      chainNum P permL (fun i => electronNumerator P.m
        (classMomE .L (pIn 0) (pOut 0) ℓ (.inl (lineL i)))) (μ 0) (αOut 0) (βIn 0) := by
  have hhead : (photL 0).head = ps5 4 ∧ (photL 1).head = ps5 3 := by decide +kernel
  refine classNumeratorE_eq_chainNum permL lineL (fun g => prod_fermionLine_L g) ⟨rfl, rfl, rfl, rfl⟩
    (by decide +kernel) (fun h => ?_) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    P pOut pIn kIn αOut βIn μ ℓ
  rw [prod_photonLine_L (fun g => h g.1 g.head), hhead.1, hhead.2]
  rfl

/-- The photon pairing of `X` as a permutation. -/
noncomputable def permX : Equiv.Perm (Fin 5) := Equiv.ofBijective (![2, 0, 3, 1, 4] : Fin 5 → Fin 5) (by decide)

theorem chain_X (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    classNumeratorE .X P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
      chainNum P permX (fun i => electronNumerator P.m
        (classMomE .X (pIn 0) (pOut 0) ℓ (.inl (lineX i)))) (μ 0) (αOut 0) (βIn 0) := by
  have hhead : (photX 0).head = ps5 3 ∧ (photX 1).head = ps5 4 := by decide +kernel
  refine classNumeratorE_eq_chainNum permX lineX (fun g => prod_fermionLine_X g) ⟨rfl, rfl, rfl, rfl⟩
    (by decide +kernel) (fun h => ?_) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    P pOut pIn kIn αOut βIn μ ℓ
  rw [prod_photonLine_X (fun g => h g.1 g.head), hhead.1, hhead.2]
  rfl

/-- The photon pairing of `Cp` as a permutation. -/
noncomputable def permCp : Equiv.Perm (Fin 5) := Equiv.ofBijective (![1, 0, 3, 2, 4] : Fin 5 → Fin 5) (by decide)

theorem chain_Cp (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    classNumeratorE .Cp P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
      chainNum P permCp (fun i => electronNumerator P.m
        (classMomE .Cp (pIn 0) (pOut 0) ℓ (.inl (lineCp i)))) (μ 0) (αOut 0) (βIn 0) := by
  have hhead : (photCp 0).head = ps5 3 ∧ (photCp 1).head = ps5 4 := by decide +kernel
  refine classNumeratorE_eq_chainNum permCp lineCp (fun g => prod_fermionLine_Cp g) ⟨rfl, rfl, rfl, rfl⟩
    (by decide +kernel) (fun h => ?_) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    P pOut pIn kIn αOut βIn μ ℓ
  rw [prod_photonLine_Cp (fun g => h g.1 g.head), hhead.1, hhead.2]
  rfl

/-- The photon pairing of `Cm` as a permutation. -/
noncomputable def permCm : Equiv.Perm (Fin 5) := Equiv.ofBijective (![3, 0, 2, 1, 4] : Fin 5 → Fin 5) (by decide)

theorem chain_Cm (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    classNumeratorE .Cm P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
      chainNum P permCm (fun i => electronNumerator P.m
        (classMomE .Cm (pIn 0) (pOut 0) ℓ (.inl (lineCm i)))) (μ 0) (αOut 0) (βIn 0) := by
  have hhead : (photCm 0).head = ps5 2 ∧ (photCm 1).head = ps5 4 := by decide +kernel
  refine classNumeratorE_eq_chainNum permCm lineCm (fun g => prod_fermionLine_Cm g) ⟨rfl, rfl, rfl, rfl⟩
    (by decide +kernel) (fun h => ?_) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    P pOut pIn kIn αOut βIn μ ℓ
  rw [prod_photonLine_Cm (fun g => h g.1 g.head), hhead.1, hhead.2]
  rfl

/-- The photon pairing of `Sp` as a permutation. -/
noncomputable def permSp : Equiv.Perm (Fin 5) := Equiv.ofBijective (![1, 0, 4, 2, 3] : Fin 5 → Fin 5) (by decide)

theorem chain_Sp (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    classNumeratorE .Sp P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
      chainNum P permSp (fun i => electronNumerator P.m
        (classMomE .Sp (pIn 0) (pOut 0) ℓ (.inl (lineSp i)))) (μ 0) (αOut 0) (βIn 0) := by
  have hhead : (photSp 0).head = ps5 4 ∧ (photSp 1).head = ps5 3 := by decide +kernel
  refine classNumeratorE_eq_chainNum permSp lineSp (fun g => prod_fermionLine_Sp g) ⟨rfl, rfl, rfl, rfl⟩
    (by decide +kernel) (fun h => ?_) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    P pOut pIn kIn αOut βIn μ ℓ
  rw [prod_photonLine_Sp (fun g => h g.1 g.head), hhead.1, hhead.2]
  rfl

/-- The photon pairing of `Sm` as a permutation. -/
noncomputable def permSm : Equiv.Perm (Fin 5) := Equiv.ofBijective (![3, 0, 4, 1, 2] : Fin 5 → Fin 5) (by decide)

theorem chain_Sm (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    classNumeratorE .Sm P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
      chainNum P permSm (fun i => electronNumerator P.m
        (classMomE .Sm (pIn 0) (pOut 0) ℓ (.inl (lineSm i)))) (μ 0) (αOut 0) (βIn 0) := by
  have hhead : (photSm 0).head = ps5 4 ∧ (photSm 1).head = ps5 2 := by decide +kernel
  refine classNumeratorE_eq_chainNum permSm lineSm (fun g => prod_fermionLine_Sm g) ⟨rfl, rfl, rfl, rfl⟩
    (by decide +kernel) (fun h => ?_) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    P pOut pIn kIn αOut βIn μ ℓ
  rw [prod_photonLine_Sm (fun g => h g.1 g.head), hhead.1, hhead.2]
  rfl

/-- **Covariance of the open-class numerators**: for a spinor lift `(S, T)` of `L` with
`L p = p`, `L p' = p'`, `S N^μ(L ℓ) T = L^μ_ν N^ν(ℓ)`. -/
theorem classNumM_cov {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ} (h : IsSpinLift L S T)
    {p p' : Fin 4 → ℝ} (hp : L *ᵥ p = p) (hp' : L *ᵥ p' = p') (P : Params) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * classNumM c P p p' μ (loopAct L ℓ) * T = vecAct L (fun ν => classNumM c P p p' ν ℓ) μ := by
  simp only [QED.TwoLoop.ClassIntegrable.openClasses, Finset.mem_insert,
    Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact classNumM_cov_of_chain permL lineL chain_L h hp hp' P μ ℓ
  · exact classNumM_cov_of_chain permX lineX chain_X h hp hp' P μ ℓ
  · exact classNumM_cov_of_chain permCp lineCp chain_Cp h hp hp' P μ ℓ
  · exact classNumM_cov_of_chain permCm lineCm chain_Cm h hp hp' P μ ℓ
  · exact classNumM_cov_of_chain permSp lineSp chain_Sp h hp hp' P μ ℓ
  · exact classNumM_cov_of_chain permSm lineSm chain_Sm h hp hp' P μ ℓ

end QED.TwoLoop.LimitCovariance

end
