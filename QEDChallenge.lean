/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Logic.Relation
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Order.Basic

/-!
# Challenge: the one-loop anomalous magnetic moment of the electron

A standalone statement, importing only Mathlib, of the headline theorem
`QED.WickModel.lszAmplitude_pauli_landeFactor_limit` (H) of the `QED` library: in the regulated,
Pauli–Villars-extended spinor electrodynamics truncated at order `e³`, the Pauli form factor of
the model's own LSZ amplitude tends to `α/(2π)`, and both magnetic-moment definitions give a Landé
factor tending to `2 (1 + α/(2π))`, as the photon mass tends to `0` and the Pauli–Villars photon
mass to `∞`.

Every definition below is copied from the author-frozen declaration of the same name in
`QED/Frozen/`, with the same body (docstrings shortened), in dependency order. They are exactly
the definitions that the statement reaches.

* The types `QED.WickModel.Params` and `QED.Wick.VertexKind`, with the instances and functions
  `VertexKind.instFintype`, `VertexKind.order`, `VertexKind.photonSlots`, `Params.mass` and
  `Params.loopCoeff`, keep their library names, so the statements are about the library's own
  types.
* Every other declaration is copied under the namespace prefix `QEDChallenge`: for example,
  `QEDChallenge.QED.WickModel.lszAmplitude` is the copy of `QED.WickModel.lszAmplitude`. Within
  one module Lean shares identical auxiliary proofs and matchers between declarations, so copies
  in a single file cannot carry the library's per-file auxiliary constants under the library's
  own names; the Solution therefore repeats these copies and proves them equal to the library's.

The theorems, stated with `sorry`, are the headline and the four theorems that the copied
definitions use: (Z₁) `selfEnergy_existsUnique`, from which `selfEnergyAB` is chosen; (L₁)
`lszAmplitude_existsUnique`, from which `lszAmplitude` is chosen; and the on-shell condition and
positive energy of the one-electron momentum, which `lszPacketCurrentDensity` passes to the LSZ
amplitude.

Conventions: the metric is mostly plus, `diag(-1, 1, 1, 1)`; index `0` of `Fin 4` is time;
equation numbers refer to the primary source (Srednicki, *Quantum Field Theory*).
-/

@[expose] public section

namespace QED.Wick

/-- (V₀) The interaction vertices with counterterms, (62.2)–(62.3) (decision D-19): `e Ψ̄ A̸ Ψ`, its
counterterm `(Z₁ - 1) e Ψ̄ A̸ Ψ`, the fermion counterterm and the photon counterterm. -/
inductive VertexKind where
  | gauge
  | gaugeCt
  | fermionCt
  | photonCt
  deriving DecidableEq

/-- (V₀′) The four vertex kinds form a finite type. -/
instance VertexKind.instFintype : Fintype VertexKind :=
  ⟨{.gauge, .gaugeCt, .fermionCt, .photonCt}, fun x => by cases x <;> simp⟩

/-- (V₁) The order of a vertex in the charge `e`; the counterterm coefficients count as order `e²`
(decision D-19). -/
def VertexKind.order : VertexKind → ℕ
  | .gauge => 1
  | .gaugeCt => 3
  | .fermionCt => 2
  | .photonCt => 2

-- `order` and `photonSlots` have the same pattern match, and Lean reuses an identical
-- matcher within a module. This option, which only skips compiled code for the matcher,
-- keeps `photonSlots` from reusing the matcher of `order`, so that its matcher is the
-- library's own constant `photonSlots.match_1`. The definition is unchanged.
set_option bootstrap.genMatcherCode false in
/-- (V₂) The number of photon fields `A` of a vertex. -/
def VertexKind.photonSlots : VertexKind → ℕ
  | .gauge => 1
  | .gaugeCt => 1
  | .fermionCt => 0
  | .photonCt => 2

end QED.Wick

namespace QED.WickModel
open Complex

/-- (X₀) The parameters of the regulated model (decisions D-5, D-19, D-22). -/
structure Params where
  /-- The electron charge `e` (negative, D-7). -/
  e : ℝ
  /-- The vertex counterterm coefficient `δ₁ = Z₁ - 1` of (62.2), of order `e²` (D-19). -/
  δ₁ : ℝ
  /-- The counterterm coefficient `δ₂ = Z₂ - 1` of (62.3), of order `e²` (D-19). -/
  δ₂ : ℝ
  /-- The counterterm coefficient `δ_m = Z_m - 1` of (62.3), of order `e²` (D-19). -/
  δm : ℝ
  /-- The counterterm coefficient `δ₃ = Z₃ - 1` of (62.3), of order `e²` (D-19). -/
  δ₃ : ℝ
  /-- The electron mass `m`. -/
  m : ℝ
  /-- The photon mass `m_γ`, the infrared regulator (D-5). -/
  mγ : ℝ
  /-- The Pauli–Villars photon mass `Λ` (D-5). -/
  Λ : ℝ
  /-- The Feynman prescription `ε` of the propagators; only `ε > 0` is source-facing. -/
  ε : ℝ
  /-- The mass `M₁` of the regulator fermion of flavor `1` (D-22). -/
  M₁ : ℝ
  /-- The mass `M₂` of the regulator fermion of flavor `2` (D-22). -/
  M₂ : ℝ
  /-- The coefficient `c₁` of a closed loop of the regulator fermion of flavor `1` (D-22). -/
  c₁ : ℝ
  /-- The coefficient `c₂` of a closed loop of the regulator fermion of flavor `2` (D-22). -/
  c₂ : ℝ

/-- (X₀′) The mass of the fermion of flavor `f` (decision D-22). -/
def Params.mass (P : Params) : Fin 3 → ℝ :=
  ![P.m, P.M₁, P.M₂]

/-- (X₀″) The coefficient `c_f` of a closed fermion loop of flavor `f` (decision D-22). -/
def Params.loopCoeff (P : Params) : Fin 3 → ℝ :=
  ![1, P.c₁, P.c₂]

end QED.WickModel

namespace QEDChallenge.QED.Minkowski

/-- The Minkowski metric `g_{μν} = diag(-1, 1, 1, 1)` (mostly plus). -/
def metric (μ ν : Fin 4) : ℝ :=
  if μ = ν then (if μ = 0 then -1 else 1) else 0

/-- The Minkowski bilinear form `p·k = g_{μν} p^μ k^ν`. -/
def dot (p k : Fin 4 → ℝ) : ℝ :=
  ∑ μ, ∑ ν, metric μ ν * p μ * k ν

/-- Covariant components `p_μ = g_{μν} p^ν`. -/
def lower (p : Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  ∑ ν, metric μ ν * p ν

end QEDChallenge.QED.Minkowski

namespace QEDChallenge.QED.Dirac
open Matrix Complex

/-- The gamma matrices `γ^μ` (upper index) in the Weyl representation of eq. (36.7). -/
def gamma : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  | 0 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | 1 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  | 2 => !![0, 0, 0, -I; 0, 0, I, 0; 0, I, 0, 0; -I, 0, 0, 0]
  | 3 => !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]

/-- Feynman slash `p̸ = γ^μ p_μ` of a real four-vector (mostly-plus metric). -/
def slash (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ μ, ((Minkowski.lower p μ : ℝ) : ℂ) • gamma μ

end QEDChallenge.QED.Dirac

namespace QEDChallenge.QED.OneLoop
open Matrix Complex

/-- (A) The free electron propagator `S̃(p̸) = (-p̸ + m) / (p² + m² - iε)` (rule 9); only `ε > 0` is
source-facing. -/
noncomputable def electronPropagator (m ε : ℝ) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (((Minkowski.dot p p + m ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ •
    ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p)

end QEDChallenge.QED.OneLoop

namespace QEDChallenge.QED.OneLoop
open Complex

/-- (B) The regulated Feynman-gauge photon propagator
`g_{μν} [1 / (k² + m_γ² - iε) - 1 / (k² + Λ² - iε)]` (decision D-5). -/
noncomputable def photonPropagator (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ((Minkowski.metric μ ν : ℝ) : ℂ) *
    ((((Minkowski.dot k k + mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹
      - (((Minkowski.dot k k + Λ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹)

end QEDChallenge.QED.OneLoop

namespace QEDChallenge.QED.OneLoop
open MeasureTheory

/-- (D) The energy-first iterated integral `∫ d³ℓ (∫ dℓ⁰ F(ℓ⁰, ℓ⃗))` of prescription M1 (index `0`
is time); like the Bochner integral, it is `0` on non-integrable data. -/
noncomputable def energyFirstIntegral (F : (Fin 4 → ℝ) → ℂ) : ℂ :=
  ∫ v : Fin 3 → ℝ, ∫ t : ℝ, F (Fin.cons t v : Fin 4 → ℝ)

end QEDChallenge.QED.OneLoop

namespace QEDChallenge.QED.Dirac
open Matrix Complex

/-- The Lorentz generators `S^{μν} = (i/4) [γ^μ, γ^ν]` (eq. (40.3)). -/
noncomputable def lorentzGen (μ ν : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (I / 4) • (gamma μ * gamma ν - gamma ν * gamma μ)

/-- The matrix `β` of the Dirac adjoint `Ψ̄ = Ψ† β` (eq. (38.8)). -/
def beta : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

/-- The Dirac adjoint `ū = u† β` of a column spinor, as a row vector (eq. (38.7)). -/
def bar (u : Fin 4 → ℂ) : Fin 4 → ℂ := star u ᵥ* beta

/-- Rest spinors `u_±(0)` of eq. (38.6), for `m > 0`; spin label `0 ↦ +` (spin up along `z`),
`1 ↦ -`. -/
noncomputable def restSpinor (m : ℝ) : Fin 2 → Fin 4 → ℂ
  | 0 => ![(Real.sqrt m : ℂ), 0, (Real.sqrt m : ℂ), 0]
  | 1 => ![0, (Real.sqrt m : ℂ), 0, (Real.sqrt m : ℂ)]

/-- The on-shell spinor `u_s(p) = (m - p̸) u_s(0) / √(2m(m + p⁰))` of eq. (38.12); meaningful for
`m > 0` and on-shell `p` with `p⁰ > 0`. -/
noncomputable def spinor (m : ℝ) (p : Fin 4 → ℝ) (s : Fin 2) : Fin 4 → ℂ :=
  (((Real.sqrt (2 * m * (m + p 0)))⁻¹ : ℝ) : ℂ) •
    ((((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) - slash p) *ᵥ restSpinor m s)

end QEDChallenge.QED.Dirac

namespace QEDChallenge.QED.OneLoop

/-- (W₀) The on-shell four-momentum `(ω, k⃗)` of a one-electron state with spatial momentum `k⃗`,
`ω = √(m² + |k⃗|²)` (3.11). -/
noncomputable def oneParticleMomentum (m : ℝ) (k : Fin 3 → ℝ) : Fin 4 → ℝ :=
  Fin.cons (Real.sqrt (m ^ 2 + ∑ j, k j ^ 2)) k

/-- The momentum (W₀) is on shell: `p·p = -m²`. -/
theorem dot_oneParticleMomentum (m : ℝ) (k : Fin 3 → ℝ) :
    Minkowski.dot (oneParticleMomentum m k) (oneParticleMomentum m k) = -m ^ 2 :=
  sorry

/-- The momentum (W₀) has positive energy for `m > 0`. -/
theorem oneParticleMomentum_pos {m : ℝ} (hm : 0 < m) (k : Fin 3 → ℝ) :
    0 < oneParticleMomentum m k 0 :=
  sorry

end QEDChallenge.QED.OneLoop

namespace QEDChallenge.QED.OneLoop
open MeasureTheory

/-- (W₂) The squared norm `⟨e|e⟩ = ∫ d̃k f(k⃗)²` of the wave packet (W₁), with the one-particle
normalization (41.5). -/
noncomputable def packetNormSq (m : ℝ) (φ : ℝ → ℝ) (lam : ℝ) : ℝ :=
  ∫ k : Fin 3 → ℝ, φ ((∑ j, k j ^ 2) / lam ^ 2) ^ 2
    / ((2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m k 0))

end QEDChallenge.QED.OneLoop

namespace QEDChallenge.QED.Wick
open _root_.QED.Wick

/-- (V₃) The vertices of a labelled vertex sequence `κ` that carry a `Ψ̄ Ψ` pair. -/
abbrev FermionVertex {N : ℕ} (κ : Fin N → VertexKind) : Type :=
  {t : Fin N // κ t ≠ .photonCt}

/-- (V₄) The photon fields of the vertices of `κ`: `⟨t, k⟩` is the `k`-th photon field of vertex
`t`. -/
abbrev PhotonSlot {N : ℕ} (κ : Fin N → VertexKind) : Type :=
  Σ t : Fin N, Fin (κ t).photonSlots

/-- (V₈) A numbering of photon fields, used only to orient photon lines and to order lines. -/
def photonKey {N : ℕ} {κ : Fin N → VertexKind} (a : PhotonSlot κ) : ℕ :=
  2 * a.1.val + a.2.val

end QEDChallenge.QED.Wick

namespace QEDChallenge.QED.Wick
open Complex
open _root_.QED.Wick

/-- (V₁₉) The factor of vertex `t`, `i` times its Lagrangian term in momentum space ((62.2)–(62.3),
(62.12), (62.28)), for spinor indices `α`, `β` and Lorentz indices `lor`. -/
noncomputable def vertexFactor (e δ₁ δ₂ δm δ₃ m : ℝ) {N : ℕ} {κ : Fin N → VertexKind}
    (α β : FermionVertex κ → Fin 4) (lor : PhotonSlot κ → Fin 4)
    (kψ : FermionVertex κ → Fin 4 → ℝ) (kA : PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) : ℂ :=
  match h : κ t with
  | .gauge => I * e * Dirac.gamma (lor ⟨t, ⟨0, by simp [h, VertexKind.photonSlots]⟩⟩)
      (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩)
  | .gaugeCt => I * ((δ₁ * e : ℝ) : ℂ) *
      Dirac.gamma (lor ⟨t, ⟨0, by simp [h, VertexKind.photonSlots]⟩⟩)
        (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩)
  | .fermionCt => -I * (((δ₂ : ℂ) • Dirac.slash (kψ ⟨t, by simp [h]⟩)
      + ((δm * m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
        (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩))
  | .photonCt =>
      let k := kA ⟨t, ⟨0, by simp [h, VertexKind.photonSlots]⟩⟩;
      let μ := lor ⟨t, ⟨0, by simp [h, VertexKind.photonSlots]⟩⟩;
      let ν := lor ⟨t, ⟨1, by simp [h, VertexKind.photonSlots]⟩⟩;
      -(I / 2) * ((δ₃ * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ) : ℂ)

end QEDChallenge.QED.Wick

namespace QEDChallenge.QED.WickModel
open Complex
open _root_.QED _root_.QED.WickModel

/-- (X₁) A flavoring of `κ`: the flavor (`0` the electron, `1`, `2` the regulator fermions) of the
fermion fields of each vertex; counterterm vertices have flavor `0` (decision D-22). -/
abbrev Flavoring {N : ℕ} (κ : Fin N → Wick.VertexKind) : Type :=
  {φ : Wick.FermionVertex κ → Fin 3 // ∀ t, κ t.1 ≠ .gauge → φ t = 0}

/-- (X₂) The flavor of a fermion field under the flavoring `φ`. -/
def fermionFlavor {nf N : ℕ} {κ : Fin N → Wick.VertexKind} (φ : Flavoring κ) :
    Fin nf ⊕ Wick.FermionVertex κ → Fin 3
  | .inl _ => 0
  | .inr t => φ.1 t

/-- (X₃) The Wick contractions of `⟨Ψ(x₁) Ψ̄(y₁) ⋯ Ψ(x_nf) Ψ̄(y_nf) A(z₁) ⋯ A(z_nA)⟩` with vertices
`κ`: a pairing of the `Ψ` with the `Ψ̄` fields (`inl` external, `inr` vertex fields) and a
fixed-point-free involution of the photon fields (decision D-23.2). -/
abbrev Contraction (nf nA : ℕ) {N : ℕ} (κ : Fin N → Wick.VertexKind) : Type :=
  {c : Equiv.Perm (Fin nf ⊕ Wick.FermionVertex κ) × Equiv.Perm (Fin nA ⊕ Wick.PhotonSlot κ) //
    ∀ b, c.2 (c.2 b) = b ∧ c.2 b ≠ b}

/-- (X₄) The contraction `C` preserves the flavoring `φ` (the free propagator is flavor-diagonal;
decision D-22). -/
def Preserves {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (φ : Flavoring κ) : Prop :=
  ∀ a, fermionFlavor φ (C.1.1 a) = fermionFlavor φ a

/-- (X₅) The fermionic (Grassmann) sign of a contraction. -/
def fermionSign {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) : ℤ :=
  (-1) ^ Fintype.card (Wick.FermionVertex κ) * (Equiv.Perm.sign C.1.1 : ℤ)

/-- (X₆) The closed fermion loops of a contraction: the cycles of its fermion pairing that contain
no external field. -/
abbrev ClosedLoop {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) : Type :=
  {q : Quotient (Equiv.Perm.SameCycle.setoid C.1.1) //
    ∀ i : Fin nf, Quotient.mk _ (Sum.inl i) ≠ q}

open scoped Classical in
/-- (X₇) The regulator weight of `(C, φ)`: the product over the closed fermion loops of the
coefficient `c_f` of the loop's flavor (decision D-22). -/
noncomputable def loopWeight (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (φ : Flavoring κ) : ℝ :=
  ∏ q : ClosedLoop C, P.loopCoeff (fermionFlavor φ q.1.out)

/-- (X₈) The internal fermion lines of a contraction, indexed by the vertex whose `Ψ` is contracted
with the `Ψ̄` of a vertex. -/
abbrev FermionLine {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) : Type :=
  {t : Wick.FermionVertex κ // (C.1.1 (.inr t)).isRight}

/-- (X₉) The vertex `s` whose `Ψ̄` is contracted with the `Ψ` of the internal fermion line. -/
def FermionLine.tail {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (f : FermionLine C) : Wick.FermionVertex κ :=
  (C.1.1 (.inr f.1)).getRight f.2

/-- (X₁₀) The internal photon lines of a contraction, indexed by the photon field with the smaller
key. -/
abbrev PhotonLine {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) : Type :=
  {a : Wick.PhotonSlot κ // ∃ b, C.1.2 (.inr a) = .inr b ∧ Wick.photonKey a < Wick.photonKey b}

/-- (X₁₁) The vertex photon field contracted with the indexing field of an internal photon line. -/
def PhotonLine.head {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (g : PhotonLine C) : Wick.PhotonSlot κ :=
  (C.1.2 (.inr g.1)).getRight (Sum.isRight_iff.mpr (g.2.imp fun _ h => h.1))

/-- (X₁₂) The internal lines of a contraction. -/
abbrev Line {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) : Type :=
  FermionLine C ⊕ PhotonLine C

/-- (X₁₃) The end vertices `(tail, head)` of an internal line; momentum flows from tail to head. -/
def Line.ends {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ} :
    Line C → Fin N × Fin N
  | .inl f => (f.tail.1, f.1.1)
  | .inr g => (g.1.1, g.head.1)

/-- (X₁₄) Vertices `u` and `w` are joined by an internal line of `C` outside the set `S`. -/
def Joined {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (S : Set (Line C)) (u w : Fin N) : Prop :=
  ∃ f : Line C, f ∉ S ∧ (f.ends = (u, w) ∨ f.ends = (w, u))

/-- (X₁₅) The internal line `f` is a bridge: deleting it disconnects its two ends. -/
def IsBridge {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (f : Line C) : Prop :=
  ¬ Relation.ReflTransGen (Joined C {f}) f.ends.1 f.ends.2

/-- (X₁₆) Every external field is contracted with a vertex field. -/
def ExternalsAttached {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) :
    Prop :=
  (∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) ∧ ∀ i j : Fin nA, C.1.2 (.inl i) ≠ .inl j

/-- (X₁₇) The vertices of `C` are connected by its internal lines. -/
def VerticesConnected {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) :
    Prop :=
  ∀ u w : Fin N, Relation.ReflTransGen (Joined C ∅) u w

/-- (X₁₈) **One-particle irreducibility**: the externals are attached, the vertices are connected,
and no internal line is a bridge. -/
def IsOnePI {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) : Prop :=
  ExternalsAttached C ∧ VerticesConnected C ∧ ∀ f : Line C, ¬ IsBridge f

open scoped Classical in
/-- (X₁₉) The external momentum flowing into vertex `v` (rules 1, 2, 5). -/
noncomputable def externalMomentum {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (v : Fin N) : Fin 4 → ℝ :=
  (∑ i, if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inr t) = .inl i then pIn i else 0)
    + (∑ j, if ∃ a : Wick.PhotonSlot κ, a.1 = v ∧ C.1.2 (.inl j) = .inr a then kIn j else 0)
    - (∑ i, if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inl i) = .inr t then pOut i else 0)

/-- (X₂₀) The label of an internal line, used to choose the loop line. -/
def Line.label {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ} :
    Line C → ℕ
  | .inl f => f.1.1.val
  | .inr g => N + Wick.photonKey g.1

/-- (X₂₁) The loop line: the internal line that is not a bridge and has the smallest label among the
lines that are not bridges (decision D-19). -/
def IsLoopLine {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (f : Line C) : Prop :=
  ¬ IsBridge f ∧ ∀ g : Line C, ¬ IsBridge g → f.label ≤ g.label

open scoped Classical in
/-- (X₂₂) **Canonical one-loop routing** (rule 8; decision D-19): the loop line carries `ℓ`; any
other line carries the momentum injected into the side of its tail. -/
noncomputable def lineMomentum {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (f : Line C) : Fin 4 → ℝ :=
  if IsLoopLine f then ℓ else
    ∑ v ∈ Finset.univ.filter (fun v => Relation.ReflTransGen
        (Joined C {g | g = f ∨ IsLoopLine g}) f.ends.1 v),
      (externalMomentum C pOut pIn kIn v
        + ∑ g ∈ Finset.univ.filter (fun g : Line C => IsLoopLine g),
          ((if g.ends.2 = v then ℓ else 0) - (if g.ends.1 = v then ℓ else 0)))

/-- (X₂₃) The momentum flowing into vertex `t` through its `Ψ` field. -/
noncomputable def psiMomentum {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (t : Wick.FermionVertex κ) : Fin 4 → ℝ :=
  match h : C.1.1 (.inr t) with
  | .inl i => pIn i
  | .inr _ => lineMomentum C pOut pIn kIn ℓ (.inl ⟨t, by simp [h]⟩)

open scoped Classical in
/-- (X₂₄) The momentum flowing into the vertex of the photon field `a` through `a`. -/
noncomputable def photonMomentum {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (a : Wick.PhotonSlot κ) : Fin 4 → ℝ :=
  (∑ j, if C.1.2 (.inl j) = .inr a then kIn j else 0) +
    ∑ g : PhotonLine C, ((if g.head = a then lineMomentum C pOut pIn kIn ℓ (.inr g) else 0)
      - (if g.1 = a then lineMomentum C pOut pIn kIn ℓ (.inr g) else 0))

open scoped Classical in
/-- (X₂₅) The amplitude of the flavored contraction `(C, φ)` at loop momentum `ℓ`: the sum over the
internal spinor and Lorentz indices of the product of the vertex factors, `(1/i) S̃` per internal
fermion line (with the mass of its flavor) and `(1/i) Δ̃` per internal photon line; the external
legs are amputated. -/
noncomputable def contractionAmplitude (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (φ : Flavoring κ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) : ℂ :=
  ∑ α : Wick.FermionVertex κ → Fin 4, ∑ β : Wick.FermionVertex κ → Fin 4,
    ∑ lor : Wick.PhotonSlot κ → Fin 4,
      (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
          (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
          (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
        ((∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
            (psiMomentum C pOut pIn kIn ℓ) (photonMomentum C pOut pIn kIn ℓ) t) *
          (∏ f : FermionLine C, (1 / I) *
            QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε
              (lineMomentum C pOut pIn kIn ℓ (.inl f)) (β f.1) (α f.tail)) *
          ∏ g : PhotonLine C, (1 / I) *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (lineMomentum C pOut pIn kIn ℓ (.inr g))
              (lor g.1) (lor g.head))

open scoped Classical in
/-- (X₂₆) **The Pauli–Villars regulated amplitude** of a contraction at loop momentum `ℓ`: the sum
over the flavorings it preserves of the regulator weight times the amplitude (decision D-22). -/
noncomputable def regulatedAmplitude (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ φ ∈ (Finset.univ : Finset (Flavoring κ)).filter (Preserves C),
    (loopWeight P C φ : ℂ) * contractionAmplitude P C φ pOut pIn kIn ℓ αOut βIn μ

open scoped Classical in
/-- (X₂₇) The value of a contraction: if it has a loop line, the regulated amplitude times `(2π)⁻⁴`,
integrated over the loop momentum with prescription M1 at fixed `ε`; otherwise the regulated
amplitude. -/
noncomputable def contractionValue (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  if ∃ f : Line C, IsLoopLine f then
    QED.OneLoop.energyFirstIntegral fun ℓ =>
      (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * regulatedAmplitude P C pOut pIn kIn ℓ αOut βIn μ
  else regulatedAmplitude P C pOut pIn kIn 0 αOut βIn μ

open scoped Classical in
/-- (X₂₈) **The 1PI function from the Wick expansion** (decisions D-8, D-19, D-22, D-23.2): the sum
over the 1PI contractions of the terms of `exp(i ∫ L₁)` of total order at most `K` in `e`, with the
fermionic signs and the factor `1/N!`. -/
noncomputable def onePIFunction (P : Params) (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K),
      ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter IsOnePI,
        ((fermionSign C : ℤ) : ℂ) * contractionValue P C pOut pIn kIn αOut βIn μ

open scoped Classical in
/-- (X₂₉) **The connected function from the Wick expansion** (decision D-23.1): as (X₂₈), summed
over the contractions whose externals are attached and whose vertices are connected. -/
noncomputable def connectedFunction (P : Params) (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K),
      ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter
          (fun C => ExternalsAttached C ∧ VerticesConnected C),
        ((fermionSign C : ℤ) : ℂ) * contractionValue P C pOut pIn kIn αOut βIn μ

end QEDChallenge.QED.WickModel

namespace QEDChallenge.QED.WickModel
open Complex Filter Topology MeasureTheory
open _root_.QED _root_.QED.WickModel

/-- (Z₁) **The electron self-energy is well defined and covariant** (decision D-25). For
`m, m_γ, Λ > 0`, the loop integrand of every one-loop 1PI contraction of the one-electron function
at order `e²` is integrable in both stages of prescription M1, and there is a unique pair `(A, B)`
of functions of `s = p² > -(m + min(m_γ, Λ))²` such that `(1/i)` times the one-electron 1PI function
tends, as `ε → 0⁺`, to `A(p²) p̸ + B(p²) m`, entry by entry. -/
theorem selfEnergy_existsUnique (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 2 →
      ∀ C : Contraction 1 0 κ, IsOnePI C → (∃ f : Line C, IsLoopLine f) →
      ∀ (p : Fin 4 → ℝ) (α β : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![p] ![p] ![] (Fin.cons t v) ![α] ![β] ![]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![p] ![p] ![] (Fin.cons t v) ![α] ![β] ![]) ∧
    ∃! AB : {s : ℝ // -(P.m + min P.mγ P.Λ) ^ 2 < s} → ℂ × ℂ,
      ∀ (p : Fin 4 → ℝ) (hp : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot p p) (α β : Fin 4),
        Tendsto (fun ε : ℝ => (1 / I) *
            onePIFunction { P with ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![])
          (𝓝[>] 0)
          (𝓝 (((AB ⟨_, hp⟩).1 • Dirac.slash p
            + ((AB ⟨_, hp⟩).2 * P.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) :=
  sorry

/-- (Z₃) **The self-energy form factors** `(A, B)` (decision D-25), chosen from (Z₁). -/
noncomputable def selfEnergyAB (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    {s : ℝ // -(P.m + min P.mγ P.Λ) ^ 2 < s} → ℂ × ℂ :=
  (selfEnergy_existsUnique P hm hmγ hΛ).2.exists.choose

/-- (Z₄) **The self-energy as a function of `p̸`** ((62.27), decision D-25):
`Σ(z) = A(-z²) z + B(-z²) m` for real `z` with `|z| < m + min(m_γ, Λ)`. -/
noncomputable def selfEnergySlash (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (z : ℝ) (hz : |z| < P.m + min P.mγ P.Λ) : ℂ :=
  have hs : -(P.m + min P.mγ P.Λ) ^ 2 < -z ^ 2 :=
    neg_lt_neg ((sq_abs z).symm.trans_lt (pow_lt_pow_left₀ hz (abs_nonneg z) two_ne_zero))
  (selfEnergyAB P hm hmγ hΛ ⟨-z ^ 2, hs⟩).1 * z + (selfEnergyAB P hm hmγ hΛ ⟨-z ^ 2, hs⟩).2 * P.m

/-- (Z₅) **The on-shell conditions for the electron** (62.27), (62.36)–(62.38): `Σ(-m) = 0` and
`Σ'(-m) = 0`, the derivative taken through the clamp onto an interval around `-m` inside the domain
of `Σ`. -/
def IsElectronOnShell (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) : Prop :=
  selfEnergySlash P hm hmγ hΛ (-P.m) (by
      rw [abs_neg, abs_of_pos hm]
      exact lt_add_of_pos_right _ (lt_min hmγ hΛ)) = 0 ∧
    HasDerivAt (fun z : ℝ => selfEnergySlash P hm hmγ hΛ
        (Set.projIcc (-P.m - min P.mγ P.Λ / 2) (-P.m + min P.mγ P.Λ / 2)
          (by linarith [lt_min hmγ hΛ]) z)
        (by
          have hμ := lt_min hmγ hΛ
          have h1 := (Set.projIcc (-P.m - min P.mγ P.Λ / 2) (-P.m + min P.mγ P.Λ / 2)
            (by linarith) z).2
          rw [abs_lt]
          constructor <;> linarith [h1.1, h1.2]))
      0 (-P.m)

end QEDChallenge.QED.WickModel

namespace QEDChallenge.QED.WickModel
open Matrix Complex Filter Topology MeasureTheory
open _root_.QED _root_.QED.WickModel

/-- (L₁) **The LSZ amplitude of the electron current exists and is unique** (decisions D-23, D-29).
For `m, m_γ, Λ > 0`, Pauli–Villars regulator fermions and electron counterterms on shell (Z₅): every
one-loop connected contraction of the three-point function at order `e³` is integrable in both
stages of M1, and for on-shell positive-energy `p'`, `p`, spins `s'`, `s` and index `μ` there is a
unique `M` that is the iterated limit, first `ε → 0⁺` at off-shell `r'`, `r`, then
`(r', r) → (p', p)`, of `(1/i) ū_{s'}(p') G^μ_ε(r', r) u_s(p)`, with `G` the connected function
(X₂₉). -/
theorem lszAmplitude_existsUnique (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 3 →
      ∀ C : Contraction 1 1 κ, ExternalsAttached C → VerticesConnected C →
      (∃ f : Line C, IsLoopLine f) →
      ∀ (r' r : Fin 4 → ℝ) (α β μ : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![r'] ![r] ![r' - r] (Fin.cons t v) ![α] ![β]
            ![μ]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![r'] ![r] ![r' - r] (Fin.cons t v) ![α] ![β]
            ![μ]) ∧
    ∀ (p' p : Fin 4 → ℝ), Minkowski.dot p' p' = -P.m ^ 2 → Minkowski.dot p p = -P.m ^ 2 →
      0 < p' 0 → 0 < p 0 → ∀ (s' s : Fin 2) (μ : Fin 4),
      ∃! M : ℂ, ∀ η > 0, ∃ δ > 0, ∀ r' r : Fin 4 → ℝ,
        Minkowski.dot r' r' ≠ -P.m ^ 2 → Minkowski.dot r r ≠ -P.m ^ 2 →
        dist r' p' < δ → dist r p < δ →
        ∃ G : ℂ, Tendsto (fun ε : ℝ => (1 / I) *
            (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
              (Matrix.of (fun α β => connectedFunction { P with ε := ε } 1 1 3 ![r'] ![r]
                ![r' - r] ![α] ![β] ![μ]) *ᵥ Dirac.spinor P.m p s)))
          (𝓝[>] 0) (𝓝 G) ∧ ‖G - M‖ < η :=
  sorry

end QEDChallenge.QED.WickModel

namespace QEDChallenge.QED.WickModel
open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff
open _root_.QED _root_.QED.WickModel

/-- (L₂) **The LSZ amplitude of the electron current** `M^μ_{s's}(p', p)` (decisions D-23, D-29),
chosen from (L₁). -/
noncomputable def lszAmplitude (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (s' s : Fin 2)
    (μ : Fin 4) : ℂ :=
  ((lszAmplitude_existsUnique P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon).2 p' p hp' hp hp0' hp0 s' s
    μ).exists.choose

/-- (L₄) **The charge condition, LSZ form** ((63.1)–(63.2); decision D-29): at `p' = p`, the LSZ
amplitude is `e ū_{s'}(p) γ^μ u_s(p)`. -/
def IsLSZChargeNormalized (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) : Prop :=
  ∀ (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -P.m ^ 2) (hp0 : 0 < p 0) (s' s : Fin 2)
    (μ : Fin 4), lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p p hp hp hp0 hp0 s' s μ
      = (P.e : ℂ) * (Dirac.bar (Dirac.spinor P.m p s') ⬝ᵥ (Dirac.gamma μ *ᵥ Dirac.spinor P.m p s))

/-- (L₅) **The magnetic moment, response definition, LSZ form** (rulings D-9, D-29): for Breit-frame
momenta `p = (E, -q/2, 0, 0)`, `p' = (E, q/2, 0, 0)`, the spin-up LSZ amplitude `M²_{++}(p', p)` is
`2 i m μ q + o(q)` as `q → 0⁺`. -/
def IsLSZResponseMagneticMoment (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (μ : ℝ) : Prop :=
  ∀ η > 0, ∃ δ > 0, ∀ (q : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
    0 < q → q < δ → p' 1 = q / 2 → p 1 = -(q / 2) → p' 2 = 0 → p 2 = 0 → p' 3 = 0 →
    p 3 = 0 →
    ‖lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 0 0 2
      - 2 * I * P.m * μ * q‖ ≤ η * q

/-- (L₆) The current density `⟨e|J²(x)|e⟩` at time `0` of the spin-up wave packet with profile
`f(k⃗) = φ(|k⃗|²/λ²)` (decision D-17), with the LSZ amplitude `M²_{++}` as the one-electron matrix
element (decision D-29). -/
noncomputable def lszPacketCurrentDensity (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (φ : ℝ → ℝ) (lam : ℝ) (x : Fin 3 → ℝ) : ℂ :=
  ∫ k : Fin 3 → ℝ, ∫ k' : Fin 3 → ℝ,
    ((φ ((∑ j, k' j ^ 2) / lam ^ 2) * φ ((∑ j, k j ^ 2) / lam ^ 2)
      / ((2 * Real.pi) ^ 3 * (2 * QED.OneLoop.oneParticleMomentum P.m k 0)
        * ((2 * Real.pi) ^ 3 * (2 * QED.OneLoop.oneParticleMomentum P.m k' 0))) : ℝ) : ℂ)
    * Complex.exp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ))
    * lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon (QED.OneLoop.oneParticleMomentum P.m k')
        (QED.OneLoop.oneParticleMomentum P.m k) (QED.OneLoop.dot_oneParticleMomentum P.m k')
        (QED.OneLoop.dot_oneParticleMomentum P.m k) (QED.OneLoop.oneParticleMomentum_pos hm k')
        (QED.OneLoop.oneParticleMomentum_pos hm k) 0 0 2

/-- (L₇) **The magnetic moment, source definition, LSZ form** (64.4)–(64.7) (rulings D-9, D-29):
`μ = ∫ d³x x¹ ⟨e|J²(x)|e⟩ / ⟨e|e⟩`. -/
noncomputable def lszSourceMagneticMoment (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (φ : ℝ → ℝ) (lam : ℝ) : ℂ :=
  (∫ x : Fin 3 → ℝ, (x 0 : ℂ) * lszPacketCurrentDensity P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam x)
    / (QED.OneLoop.packetNormSq P.m φ lam : ℂ)

/-- (H₀) **The on-shell form-factor decomposition (63.18) of the LSZ amplitude** (decisions D-29,
D-32): `M^μ_{s's}(p', p) = e ū_{s'}(p') [A γ^μ - (i/m) B S^{μν} q_ν] u_s(p)` for all spins and every
`μ`, with `q = p' - p`. -/
def IsLSZFormFactorPair (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (F : ℂ × ℂ) : Prop :=
  ∀ (s' s : Fin 2) (μ : Fin 4),
    lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ =
      (P.e : ℂ) * (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
        ((F.1 • Dirac.gamma μ - (I / (P.m : ℂ) * F.2) •
          ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ
            Dirac.spinor P.m p s))

/-- (H) **The one-loop anomalous magnetic moment of the electron, from the model's own LSZ
amplitude (headline theorem; decisions D-21, D-32).** Fix the model data `P₀` with `e ≠ 0`,
`m > 0`, and regulator fermions heavier than the electron satisfying the Pauli–Villars
conditions. The photon regulators `m_γ`, `Λ` and the counterterms `δ₁`, `δ₂`, `δ_m` of `P₀` are
replaced; its `ε` plays no role, and its `δ₃` is arbitrary: no photon on-shell condition (Z₈) is
assumed. Fix a wave-packet profile `φ` as in (W₄) and (L₇′). Then, jointly as `m_γ → 0⁺` and
`Λ → ∞`:
* counterterms exist with the electron on shell (Z₅), the LSZ charge condition (L₄) holding, and
  an LSZ response magnetic moment (L₅);
* for every such choice of counterterms: at on-shell positive-energy pairs with small `q² > 0`,
  the LSZ amplitude has a form-factor pair (H₀), and every such pair has its Pauli component
  within `η` of `e²/(8π²) = α/(2π)` ((63.22), (64.2)); every LSZ response magnetic moment gives
  a Landé factor `g = 4 m μ / e` within `η` of `2 (1 + α/(2π))` (64.16)–(64.17); and the LSZ
  source magnetic moment (L₇) of every sufficiently narrow packet does too.
The model is truncated at order `e³`, so the limits are exact for it, with no `O(α²)` term. As in
(I), `q² → 0⁺` is taken jointly with the regulator limit and uniformly over the pairs (one `δ`
bounds both `q²` and `m_γ`); this implies the iterated order of decision D-5. As in (R′), the
response definition (L₅) takes `q → 0⁺` at fixed regulators. As in (W₅), the packet limit
`λ → 0⁺` is taken first, at fixed regulators and counterterms (decision D-17). -/
theorem lszAmplitude_pauli_landeFactor_limit (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hM₁ : P₀.m < P₀.M₁) (hM₂ : P₀.m < P₀.M₂) (hPV₁ : 1 + P₀.c₁ + P₀.c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + P₀.c₁ * P₀.M₁ ^ 2 + P₀.c₂ * P₀.M₂ ^ 2 = 0)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
      (∃ (d₁ d₂ dm : ℝ) (hon : IsElectronOnShell
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } hm hmγ hΛ),
        IsLSZChargeNormalized { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon ∧
        ∃ μ : ℝ, IsLSZResponseMagneticMoment
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ) ∧
      ∀ (d₁ d₂ dm : ℝ) (hon : IsElectronOnShell
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } hm hmγ hΛ),
        IsLSZChargeNormalized { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon →
        (∀ (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P₀.m ^ 2)
            (hp : Minkowski.dot p p = -P₀.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
          0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < δ →
          (∃ F : ℂ × ℂ, IsLSZFormFactorPair
            { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
            hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F) ∧
          ∀ F : ℂ × ℂ, IsLSZFormFactorPair
            { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
            hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F →
            ‖F.2 - ((P₀.e ^ 2 / (8 * Real.pi ^ 2) : ℝ) : ℂ)‖ < η) ∧
        (∀ μ : ℝ, IsLSZResponseMagneticMoment
            { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
            hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ →
          |4 * P₀.m * μ / P₀.e - 2 * (1 + P₀.e ^ 2 / (8 * Real.pi ^ 2))| < η) ∧
        ∃ lam₀ > 0, ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          ‖4 * (P₀.m : ℂ) * lszSourceMagneticMoment
              { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
              hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam / P₀.e
            - 2 * (1 + P₀.e ^ 2 / (8 * Real.pi ^ 2))‖ < η :=
  sorry

end QEDChallenge.QED.WickModel

end
