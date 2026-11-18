/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.RegulatedAmplitude
public import QED.Integration.TwoLoopParametricAlgebra
public import QED.TwoLoop.EnumerationRelabel
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The algebraic bridge from the model's amplitudes to the parametric integrands

Part of obligations O2-7 and O2-10 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.1–4.4). The
parametric machinery (`QED/Integration/TwoLoopParametric*.lean`) integrates products of the
denominators `QED.Integration.TwoLoop.lineDenom` (`kᵢ·kᵢ + Mᵢ² - iε`, mostly-plus metric, `ε·I`
subtracted) times polynomial numerators in the loop momenta. This file rewrites the frozen
propagators and the frozen amplitude (T₇) in that form, for every contraction.

* `propDenom M ε k = ((k·k + M² : ℝ) : ℂ) - ε·I`; `lineDenom_eq_propDenom`: `lineDenom` is
  `propDenom` at the line momentum and mass (by `rfl`).
* **Electron propagator** (`electronPropagator_apply`): each entry of the frozen
  `QED.OneLoop.electronPropagator m ε p` is `(m - p̸)_{ab} · (propDenom m ε p)⁻¹`, and
  `(m - p̸)_{ab}` is affine in `p` (`electronNumerator_apply`).
* **Photon propagator**: the frozen Pauli–Villars difference is
  `g_{μν} ((propDenom m_γ ε k)⁻¹ - (propDenom Λ ε k)⁻¹)` (`photonPropagator_eq_sub`, by `rfl`),
  and, for `ε ≠ 0`, with the pair combined,
  `g_{μν} (Λ² - m_γ²) · (propDenom m_γ ε k)⁻¹ (propDenom Λ ε k)⁻¹` (`photonPropagator_eq_mul`).
  The `lineDenom` forms are `electronPropagator_lineMomentum`, `photonPropagator_lineMomentum`.
* **The amplitude** (`contractionAmplitude₂_eq`): for `ε ≠ 0`, for every contraction, flavoring
  and line momenta `k`, the amplitude (T₇) is `amplitudeNumerator … * amplitudeDenominator …`:
  the same index sum with the propagators replaced by their numerators, times the product of
  `(propDenom)⁻¹` over the fermion lines and of the combined photon pairs over the photon lines.
* **Degree** (`isLoopPoly_amplitudeNumerator`): for contractions of `gauge` vertices (whose
  vertex factors are constants) and line momenta affine in `L` loop momenta, the numerator is a
  polynomial in the loop momenta (`IsLoopPoly`, via `MvPolynomial`) of total degree at most the
  number of fermion lines.

These are identities at fixed parameters; no integrability is involved.
-/

@[expose] public section

open Complex QED.WickModel
open QED.Integration.TwoLoop (lineDenom lineMomentum)

namespace QED.TwoLoop.Bridge

/-! ### Denominators and propagators -/

/-- The scalar propagator denominator `k·k + M² - iε` (mostly-plus metric), the convention of the
frozen propagators and of `QED.Integration.TwoLoop.lineDenom`. -/
noncomputable def propDenom (M ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot k k + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I

theorem lineDenom_eq_propDenom {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (ε : ℝ) (i : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom α p M ε i ℓ = propDenom (M i) ε (lineMomentum α p i ℓ) :=
  rfl

theorem im_propDenom (M ε : ℝ) (k : Fin 4 → ℝ) : (propDenom M ε k).im = -ε := by
  simp only [propDenom, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one,
    add_zero, zero_sub]

theorem propDenom_ne_zero {M ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) : propDenom M ε k ≠ 0 := by
  intro h
  have := im_propDenom M ε k
  rw [h, zero_im] at this
  exact hε (by linarith)

/-- The numerator `m - p̸` of the electron propagator. -/
noncomputable def electronNumerator (m : ℝ) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p

/-- **The electron propagator in denominator form**: `S̃_{ab}(p) = (m - p̸)_{ab} (p·p + m² - iε)⁻¹`,
for every `ε`. -/
theorem electronPropagator_apply (m ε : ℝ) (p : Fin 4 → ℝ) (a b : Fin 4) :
    QED.OneLoop.electronPropagator m ε p a b = electronNumerator m p a b * (propDenom m ε p)⁻¹ := by
  simp only [QED.OneLoop.electronPropagator, Matrix.smul_apply, smul_eq_mul, electronNumerator,
    propDenom]
  ring

/-- The entries of `m - p̸`: `m δ_{ab} - ∑_μ p_μ γ^μ_{ab}`, with `p_μ = ∑_ν g_{μν} p^ν`. -/
theorem electronNumerator_apply (m : ℝ) (p : Fin 4 → ℝ) (a b : Fin 4) :
    electronNumerator m p a b =
      (if a = b then (m : ℂ) else 0) -
        ∑ μ, ∑ ν, ((Minkowski.metric μ ν : ℝ) : ℂ) * (p ν : ℂ) * Dirac.gamma μ a b := by
  simp only [electronNumerator, Dirac.slash, Minkowski.lower, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, Matrix.sum_apply, ofReal_sum, ofReal_mul, Finset.sum_mul]
  split_ifs <;> simp

/-- The frozen Pauli–Villars photon propagator as a difference of two scalar inverses (`rfl`). -/
theorem photonPropagator_eq_sub (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε k μ ν =
      ((Minkowski.metric μ ν : ℝ) : ℂ) * ((propDenom mγ ε k)⁻¹ - (propDenom Λ ε k)⁻¹) :=
  rfl

/-- **The Pauli–Villars pair combined**: for `ε ≠ 0`,
`Δ̃_{μν}(k) = g_{μν} (Λ² - m_γ²) (k² + m_γ² - iε)⁻¹ (k² + Λ² - iε)⁻¹`. -/
theorem photonPropagator_eq_mul (mγ Λ : ℝ) {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε k μ ν =
      ((Minkowski.metric μ ν * (Λ ^ 2 - mγ ^ 2) : ℝ) : ℂ) *
        ((propDenom mγ ε k)⁻¹ * (propDenom Λ ε k)⁻¹) := by
  rw [photonPropagator_eq_sub]
  have h1 := propDenom_ne_zero (M := mγ) hε k
  have h2 := propDenom_ne_zero (M := Λ) hε k
  field_simp
  simp only [propDenom]
  push_cast
  ring

/-- The electron propagator at a line of the parametric data, with the `lineDenom` of that line. -/
theorem electronPropagator_lineMomentum {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (ε : ℝ) (i : Fin (m + 1))
    (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) :
    QED.OneLoop.electronPropagator (M i) ε (lineMomentum α p i ℓ) a b =
      electronNumerator (M i) (lineMomentum α p i ℓ) a b * (lineDenom α p M ε i ℓ)⁻¹ :=
  electronPropagator_apply _ _ _ _ _

/-- The photon propagator at a line `i` of the parametric data whose momentum is repeated by line
`j` (the squared-line form): for `ε ≠ 0`, with masses `M i = m_γ`, `M j = Λ`. -/
theorem photonPropagator_lineMomentum {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) {ε : ℝ} (hε : ε ≠ 0) (i j : Fin (m + 1))
    (ℓ : Fin 2 → Fin 4 → ℝ) (hij : lineMomentum α p j ℓ = lineMomentum α p i ℓ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator (M i) (M j) ε (lineMomentum α p i ℓ) μ ν =
      ((Minkowski.metric μ ν * (M j ^ 2 - M i ^ 2) : ℝ) : ℂ) *
        ((lineDenom α p M ε i ℓ)⁻¹ * (lineDenom α p M ε j ℓ)⁻¹) := by
  rw [photonPropagator_eq_mul _ _ hε, lineDenom_eq_propDenom, lineDenom_eq_propDenom, hij]

/-! ### The amplitude as numerator times denominators -/

open scoped Classical in
/-- The numerator of the amplitude (T₇): its index sum with each electron propagator replaced by
`(1/i)(m_f - k̸)` and each photon propagator by `(1/i) g_{μν} (Λ² - m_γ²)`. -/
noncomputable def amplitudeNumerator (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (φ : Flavoring κ) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) : ℂ :=
  ∑ α : Wick.FermionVertex κ → Fin 4, ∑ β : Wick.FermionVertex κ → Fin 4,
    ∑ lor : Wick.PhotonSlot κ → Fin 4,
      (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
          (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
          (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
        ((∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
            (psiMomentum₂ C pIn k) (photonMomentum₂ C kIn k) t) *
          (∏ f : FermionLine C, (1 / I) *
            electronNumerator (P.mass (φ.1 f.1)) (k (.inl f)) (β f.1) (α f.tail)) *
          ∏ g : PhotonLine C, (1 / I) *
            ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ))

open scoped Classical in
/-- The denominators of the amplitude (T₇): `(k_f² + m_f² - iε)⁻¹` for each fermion line of flavor
`f`, and `(k² + m_γ² - iε)⁻¹ (k² + Λ² - iε)⁻¹` for each photon line. -/
noncomputable def amplitudeDenominator (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (φ : Flavoring κ) (k : Line C → Fin 4 → ℝ) : ℂ :=
  (∏ f : FermionLine C, (propDenom (P.mass (φ.1 f.1)) P.ε (k (.inl f)))⁻¹) *
    ∏ g : PhotonLine C, ((propDenom P.mγ P.ε (k (.inr g)))⁻¹ * (propDenom P.Λ P.ε (k (.inr g)))⁻¹)

/-- **The amplitude (T₇) as numerator times denominators**, for every contraction, flavoring and
line momenta, with the Pauli–Villars photon pairs combined (`ε ≠ 0`). -/
theorem contractionAmplitude₂_eq (P : Params) (hε : P.ε ≠ 0) {nf nA N : ℕ}
    {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (φ : Flavoring κ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude₂ P C φ pIn kIn k αOut βIn μ =
      amplitudeNumerator P C φ pIn kIn k αOut βIn μ * amplitudeDenominator P C φ k := by
  classical
  unfold contractionAmplitude₂ amplitudeNumerator amplitudeDenominator
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  simp only [electronPropagator_apply, photonPropagator_eq_mul _ _ hε]
  have hf : ∀ f : FermionLine C, (1 / I) * (electronNumerator (P.mass (φ.1 f.1)) (k (.inl f))
      (β f.1) (α f.tail) * (propDenom (P.mass (φ.1 f.1)) P.ε (k (.inl f)))⁻¹) =
      ((1 / I) * electronNumerator (P.mass (φ.1 f.1)) (k (.inl f)) (β f.1) (α f.tail)) *
        (propDenom (P.mass (φ.1 f.1)) P.ε (k (.inl f)))⁻¹ := fun _ => by ring
  have hg : ∀ g : PhotonLine C, (1 / I) *
      (((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) *
        ((propDenom P.mγ P.ε (k (.inr g)))⁻¹ * (propDenom P.Λ P.ε (k (.inr g)))⁻¹)) =
      ((1 / I) * ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)) *
        ((propDenom P.mγ P.ε (k (.inr g)))⁻¹ * (propDenom P.Λ P.ε (k (.inr g)))⁻¹) :=
    fun _ => by ring
  simp only [hf, hg, Finset.prod_mul_distrib]
  ring

/-! ### Polynomials in the loop momenta -/

/-- `F` is a polynomial of total degree at most `n` in the `4L` real coordinates `ℓₛ^μ` of the
loop momenta, with complex coefficients. -/
def IsLoopPoly (L n : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ Q : MvPolynomial (Fin L × Fin 4) ℂ, Q.totalDegree ≤ n ∧
    ∀ ℓ, F ℓ = MvPolynomial.eval (fun x => ((ℓ x.1 x.2 : ℝ) : ℂ)) Q

namespace IsLoopPoly

variable {L n n' : ℕ} {F G : (Fin L → Fin 4 → ℝ) → ℂ}

theorem mono (h : IsLoopPoly L n F) (hn : n ≤ n') : IsLoopPoly L n' F := by
  obtain ⟨Q, hQ, hF⟩ := h
  exact ⟨Q, hQ.trans hn, hF⟩

theorem const (c : ℂ) : IsLoopPoly L n fun _ => c :=
  ⟨MvPolynomial.C c, by rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _, fun _ => by simp⟩

theorem coord (s : Fin L) (ν : Fin 4) (hn : 1 ≤ n) : IsLoopPoly L n fun ℓ => ((ℓ s ν : ℝ) : ℂ) :=
  ⟨MvPolynomial.X (s, ν), by rw [MvPolynomial.totalDegree_X]; exact hn, fun _ => by simp⟩

theorem add (hF : IsLoopPoly L n F) (hG : IsLoopPoly L n G) :
    IsLoopPoly L n fun ℓ => F ℓ + G ℓ := by
  obtain ⟨Q, hQ, hF⟩ := hF
  obtain ⟨R, hR, hG⟩ := hG
  exact ⟨Q + R, (MvPolynomial.totalDegree_add Q R).trans (max_le hQ hR), fun ℓ => by
    simp [hF, hG]⟩

theorem sub (hF : IsLoopPoly L n F) (hG : IsLoopPoly L n G) :
    IsLoopPoly L n fun ℓ => F ℓ - G ℓ := by
  obtain ⟨Q, hQ, hF⟩ := hF
  obtain ⟨R, hR, hG⟩ := hG
  exact ⟨Q - R, (MvPolynomial.totalDegree_sub Q R).trans (max_le hQ hR), fun ℓ => by
    simp [hF, hG]⟩

theorem mul (hF : IsLoopPoly L n F) (hG : IsLoopPoly L n' G) :
    IsLoopPoly L (n + n') fun ℓ => F ℓ * G ℓ := by
  obtain ⟨Q, hQ, hF⟩ := hF
  obtain ⟨R, hR, hG⟩ := hG
  exact ⟨Q * R, (MvPolynomial.totalDegree_mul Q R).trans (Nat.add_le_add hQ hR), fun ℓ => by
    simp [hF, hG]⟩

theorem const_mul (c : ℂ) (hF : IsLoopPoly L n F) : IsLoopPoly L n fun ℓ => c * F ℓ := by
  simpa using (const (n := 0) c).mul hF

theorem sum {ι : Type*} (s : Finset ι) {F : ι → (Fin L → Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, IsLoopPoly L n (F i)) : IsLoopPoly L n fun ℓ => ∑ i ∈ s, F i ℓ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (L := L) (n := n) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem prod {ι : Type*} (s : Finset ι) {F : ι → (Fin L → Fin 4 → ℝ) → ℂ} (d : ι → ℕ)
    (h : ∀ i ∈ s, IsLoopPoly L (d i) (F i)) :
    IsLoopPoly L (∑ i ∈ s, d i) fun ℓ => ∏ i ∈ s, F i ℓ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (L := L) (n := 0) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end IsLoopPoly

/-- A four-vector depending affinely on the loop momenta: `F(ℓ) = ∑ₛ aₛ ℓₛ + b`. -/
def IsLoopAffine {L : ℕ} (F : (Fin L → Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∃ a : Fin L → ℝ, ∃ b : Fin 4 → ℝ, ∀ ℓ, F ℓ = ∑ s, a s • ℓ s + b

/-- The line momentum `∑ₛ αᵢₛ ℓₛ + pᵢ` of the parametric data is affine in the loop momenta. -/
theorem isLoopAffine_lineMomentum {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (i : Fin (m + 1)) :
    IsLoopAffine (lineMomentum α p i) :=
  ⟨α i, p i, fun ℓ => by
    funext μ
    simp [lineMomentum]⟩

theorem IsLoopAffine.isLoopPoly_coord {L : ℕ} {F : (Fin L → Fin 4 → ℝ) → Fin 4 → ℝ}
    (hF : IsLoopAffine F) (ν : Fin 4) : IsLoopPoly L 1 fun ℓ => ((F ℓ ν : ℝ) : ℂ) := by
  obtain ⟨a, b, hF⟩ := hF
  have h : (fun ℓ => ((F ℓ ν : ℝ) : ℂ)) =
      fun ℓ => (∑ s ∈ Finset.univ, (a s : ℂ) * ((ℓ s ν : ℝ) : ℂ)) + (b ν : ℂ) := by
    funext ℓ
    rw [hF ℓ]
    simp [Finset.sum_apply]
  rw [h]
  exact (IsLoopPoly.sum _ fun s _ => (IsLoopPoly.coord s ν le_rfl).const_mul _).add
    (IsLoopPoly.const _)

/-- An entry of `m - k̸` at a momentum affine in the loop momenta has degree at most one. -/
theorem IsLoopAffine.isLoopPoly_electronNumerator {L : ℕ} {F : (Fin L → Fin 4 → ℝ) → Fin 4 → ℝ}
    (hF : IsLoopAffine F) (m : ℝ) (a b : Fin 4) :
    IsLoopPoly L 1 fun ℓ => electronNumerator m (F ℓ) a b := by
  simp only [electronNumerator_apply]
  refine (IsLoopPoly.const _).sub (IsLoopPoly.sum _ fun μ _ => IsLoopPoly.sum _ fun ν _ => ?_)
  have h : (fun ℓ => ((Minkowski.metric μ ν : ℝ) : ℂ) * ((F ℓ ν : ℝ) : ℂ) * Dirac.gamma μ a b) =
      fun ℓ => (((Minkowski.metric μ ν : ℝ) : ℂ) * Dirac.gamma μ a b) * ((F ℓ ν : ℝ) : ℂ) := by
    funext ℓ; ring
  rw [h]
  exact (hF.isLoopPoly_coord ν).const_mul _

/-- The vertex factor of a `gauge` vertex does not depend on the momenta. -/
theorem vertexFactor_gauges (e δ₁ δ₂ δm δ₃ m : ℝ) {N : ℕ}
    (α β : Wick.FermionVertex (Enumeration.gauges N) → Fin 4)
    (lor : Wick.PhotonSlot (Enumeration.gauges N) → Fin 4)
    (kψ kψ' : Wick.FermionVertex (Enumeration.gauges N) → Fin 4 → ℝ)
    (kA kA' : Wick.PhotonSlot (Enumeration.gauges N) → Fin 4 → ℝ) (t : Fin N) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ' kA' t :=
  rfl

/-- **Degree of the numerator.** For a contraction of `gauge` vertices and fermion-line momenta
affine in `L` loop momenta, the numerator of the amplitude is a polynomial in the loop momenta of
total degree at most the number of fermion lines. -/
theorem isLoopPoly_amplitudeNumerator (P : Params) {nf nA N L : ℕ}
    (C : Contraction nf nA (Enumeration.gauges N)) (φ : Flavoring (Enumeration.gauges N))
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : (Fin L → Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hk : ∀ f : FermionLine C, IsLoopAffine fun ℓ => k ℓ (.inl f))
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    IsLoopPoly L (Fintype.card (FermionLine C))
      fun ℓ => amplitudeNumerator P C φ pIn kIn (k ℓ) αOut βIn μ := by
  classical
  unfold amplitudeNumerator
  refine IsLoopPoly.sum _ fun α _ => IsLoopPoly.sum _ fun β _ => IsLoopPoly.sum _ fun lor _ => ?_
  refine IsLoopPoly.const_mul _ ?_
  have hv : ∀ ℓ, (∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
      (psiMomentum₂ C pIn (k ℓ)) (photonMomentum₂ C kIn (k ℓ)) t) =
      ∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor 0 0 t := fun ℓ =>
    Finset.prod_congr rfl fun t _ => vertexFactor_gauges _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp only [hv]
  have hfer := IsLoopPoly.prod (L := L) (Finset.univ : Finset (FermionLine C)) (fun _ => 1)
    (F := fun f ℓ => (1 / I) *
      electronNumerator (P.mass (φ.1 f.1)) (k ℓ (.inl f)) (β f.1) (α f.tail))
    fun f _ => ((hk f).isLoopPoly_electronNumerator _ _ _).const_mul _
  have hcard : (∑ _f ∈ (Finset.univ : Finset (FermionLine C)), 1) =
      Fintype.card (FermionLine C) := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ]
  rw [hcard] at hfer
  have h := ((IsLoopPoly.const (L := L) (n := 0) (∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃
    P.m α β lor 0 0 t)).mul hfer).mul (IsLoopPoly.const (L := L) (n := 0)
      (∏ g : PhotonLine C, (1 / I) *
        ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)))
  simpa using h

end QED.TwoLoop.Bridge

end
