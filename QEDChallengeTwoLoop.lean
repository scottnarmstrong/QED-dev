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
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Challenge: the fourth-order anomalous magnetic moment of the electron

A standalone statement, importing only Mathlib, of the two-loop headline theorem
`QED.TwoLoop.isFormFactorPair_vertexOrderFive_pauli_limit` (HV₃) of the `QED` library: in the
regulated, Pauli–Villars-extended spinor electrodynamics with the one-loop on-shell counterterms,
every form-factor pair of the order-`e⁵` 1PI vertex has `16 π⁴ F₂ / e⁴` within `η` of
`A₁⁽⁴⁾ = 197/144 + π²/12 - (π²/2) ln 2 + (3/4) ζ(3)`, the coefficient of `(α/π)²` in the
anomalous magnetic moment, `α = e²/(4π)`. The limits are taken in the order `ε → 0⁺`, then
`q² → 0⁺`, then jointly `m_γ → 0⁺` and `Λ → ∞`, then `M₁, M₂ → ∞`. The model is its
momentum-space Wick expansion, with loop integrals taken energy-first; the path integral, the
Hilbert space and the LSZ formula are not formalized, and the statement is about the 1PI vertex.

Every definition below is copied from the declaration of the same name in the library's
`QED/Frozen/` directory, with the same body (docstrings shortened), in dependency order. They are
exactly the definitions that the statements reach.

* The types `QED.WickModel.Params` and `QED.Wick.VertexKind`, with the instances and functions
  `VertexKind.instFintype`, `VertexKind.order`, `VertexKind.photonSlots`, `Params.mass` and
  `Params.loopCoeff`, keep their library names, so the statements are about the library's own
  types.
* Every other declaration is copied under the namespace prefix `QEDChallenge`: for example,
  `QEDChallenge.QED.TwoLoop.vertexOrderFive` is the copy of `QED.TwoLoop.vertexOrderFive`. Within
  one module Lean shares identical auxiliary proofs and matchers between declarations, so copies
  in a single file cannot carry the library's per-file auxiliary constants under the library's
  own names; the Solution therefore repeats these copies and proves them equal to the library's.

The theorems, stated with `sorry`, are the headline (HV₃); (HV₀)
`jointEnergyFirstIntegrable_vertexOrderFive`, that every term of the order-`e⁵` vertex is a genuine
integral at `ε > 0`; (U₂) `a1Four_bounds`, the numerical value of `A₁⁽⁴⁾`;
`exists_pauliVillars_regulators`, which shows that the regulator fermions of (HV₃) exist above
every bound; and the three theorems from which the copied definitions choose their objects: (Z₁)
`selfEnergy_existsUnique` for `selfEnergyAB`, (Z₂) `vacuumPolarization_existsUnique` for
`vacuumPolarization`, and (E) `vertexLimit_existsUnique` for `vertexOneLoop`. Because these are
compared too, the Solution must prove them from the standard axioms, so the chosen objects are the
unique objects they characterize.

The module `Mathlib.Analysis.CStarAlgebra.Classes` is imported only so that instance search on `ℂ`
takes the same path as in the library, which imports it: the comparison is of elaborated terms.

Conventions: the metric is mostly plus, `diag(-1, 1, 1, 1)`; index `0` of `Fin 4` is time;
equation numbers refer to the primary source (Srednicki, *Quantum Field Theory*).
-/

@[expose] public section

namespace QED.Wick

/-- (V₀) The interaction vertices with counterterms, (62.2)–(62.3): `e Ψ̄ A̸ Ψ`, its
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

/-- (V₁) The order of a vertex in the charge `e`; the counterterm coefficients count as order
`e²`. -/
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

/-- (X₀) The parameters of the regulated model. -/
structure Params where
  /-- The charge `e` (negative for the physical electron; the theorems assume only `e ≠ 0`).
  The regulator fermions couple with the same charge. -/
  e : ℝ
  /-- The vertex counterterm coefficient `δ₁ = Z₁ - 1` of (62.2), of order `e²`. -/
  δ₁ : ℝ
  /-- The counterterm coefficient `δ₂ = Z₂ - 1` of (62.3), of order `e²`. -/
  δ₂ : ℝ
  /-- The counterterm coefficient `δ_m = Z_m - 1` of (62.3), of order `e²`. -/
  δm : ℝ
  /-- The counterterm coefficient `δ₃ = Z₃ - 1` of (62.3), of order `e²`. -/
  δ₃ : ℝ
  /-- The electron mass `m`. -/
  m : ℝ
  /-- The photon mass `m_γ`, the infrared regulator. -/
  mγ : ℝ
  /-- The Pauli–Villars photon mass `Λ`. -/
  Λ : ℝ
  /-- The Feynman prescription `ε` of the propagators; only `ε > 0` is meaningful. -/
  ε : ℝ
  /-- The mass `M₁` of the regulator fermion of flavor `1`. -/
  M₁ : ℝ
  /-- The mass `M₂` of the regulator fermion of flavor `2`. -/
  M₂ : ℝ
  /-- The coefficient `c₁` of a closed loop of the regulator fermion of flavor `1`. -/
  c₁ : ℝ
  /-- The coefficient `c₂` of a closed loop of the regulator fermion of flavor `2`. -/
  c₂ : ℝ

/-- (X₀′) The mass of the fermion of flavor `f`. -/
def Params.mass (P : Params) : Fin 3 → ℝ :=
  ![P.m, P.M₁, P.M₂]

/-- (X₀″) The coefficient `c_f` of a closed fermion loop of flavor `f`. -/
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
meaningful. -/
noncomputable def electronPropagator (m ε : ℝ) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (((Minkowski.dot p p + m ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ •
    ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p)

end QEDChallenge.QED.OneLoop

namespace QEDChallenge.QED.OneLoop
open Complex

/-- (B) The regulated Feynman-gauge photon propagator
`g_{μν} [1 / (k² + m_γ² - iε) - 1 / (k² + Λ² - iε)]`. -/
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

end QEDChallenge.QED.Dirac

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
(62.12), (62.28)), for spinor indices `α`, `β` and Lorentz indices `lor`. The two photon fields of
`photonCt` are distinguishable slots, so its factor is half the rule
`-i (Z₃ - 1)(k² g^{μν} - k^μ k^ν)` of (62.12), which counts both pairings; `g^{μν} = g_{μν}` in the
mostly-plus metric. -/
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
fermion fields of each vertex; counterterm vertices have flavor `0`. -/
abbrev Flavoring {N : ℕ} (κ : Fin N → Wick.VertexKind) : Type :=
  {φ : Wick.FermionVertex κ → Fin 3 // ∀ t, κ t.1 ≠ .gauge → φ t = 0}

/-- (X₂) The flavor of a fermion field under the flavoring `φ`. -/
def fermionFlavor {nf N : ℕ} {κ : Fin N → Wick.VertexKind} (φ : Flavoring κ) :
    Fin nf ⊕ Wick.FermionVertex κ → Fin 3
  | .inl _ => 0
  | .inr t => φ.1 t

/-- (X₃) The Wick contractions of `⟨Ψ(x₁) Ψ̄(y₁) ⋯ Ψ(x_nf) Ψ̄(y_nf) A(z₁) ⋯ A(z_nA)⟩` with vertices
`κ`: a pairing of the `Ψ` with the `Ψ̄` fields (`inl` external, `inr` vertex fields) and a
fixed-point-free involution of the photon fields. -/
abbrev Contraction (nf nA : ℕ) {N : ℕ} (κ : Fin N → Wick.VertexKind) : Type :=
  {c : Equiv.Perm (Fin nf ⊕ Wick.FermionVertex κ) × Equiv.Perm (Fin nA ⊕ Wick.PhotonSlot κ) //
    ∀ b, c.2 (c.2 b) = b ∧ c.2 b ≠ b}

/-- (X₄) The contraction `C` preserves the flavoring `φ` (the free propagator is
flavor-diagonal). -/
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
coefficient `c_f` of the loop's flavor. -/
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
lines that are not bridges. -/
def IsLoopLine {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (f : Line C) : Prop :=
  ¬ IsBridge f ∧ ∀ g : Line C, ¬ IsBridge g → f.label ≤ g.label

open scoped Classical in
/-- (X₂₂) **Canonical one-loop routing** (rule 8): the loop line carries `ℓ`; any
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
over the flavorings it preserves of the regulator weight times the amplitude. -/
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
/-- (X₂₈) **The 1PI function from the Wick expansion**: the sum
over the 1PI contractions of the terms of `exp(i ∫ L₁)` of total order at most `K` in `e`, with the
fermionic signs and the factor `1/N!`. -/
noncomputable def onePIFunction (P : Params) (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K),
      ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter IsOnePI,
        ((fermionSign C : ℤ) : ℂ) * contractionValue P C pOut pIn kIn αOut βIn μ

end QEDChallenge.QED.WickModel

namespace QEDChallenge.QED.WickModel
open Complex Filter Topology MeasureTheory
open _root_.QED _root_.QED.WickModel

/-- (Z₁) **The electron self-energy is well defined and covariant**. For
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

/-- (Z₃) **The self-energy form factors** `(A, B)`, chosen from (Z₁). -/
noncomputable def selfEnergyAB (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    {s : ℝ // -(P.m + min P.mγ P.Λ) ^ 2 < s} → ℂ × ℂ :=
  (selfEnergy_existsUnique P hm hmγ hΛ).2.exists.choose

/-- (Z₄) **The self-energy as a function of `p̸`** ((62.27)):
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
open Complex Filter Topology MeasureTheory
open _root_.QED _root_.QED.WickModel

/-- (Z₂) **The vacuum polarization is well defined and transverse**. For `m > 0` and regulator
fermions heavier than the electron satisfying the Pauli–Villars conditions, the loop integrand of
every one-loop 1PI contraction of the two-photon function at order `e²` is integrable in both
stages of prescription M1, and there is a unique function `Π` of `s = k² > -4m²` such that `(1/i)`
times the two-photon 1PI function, with `k` flowing in through the first photon and out through
the second, tends, as `ε → 0⁺`, to `Π(k²) (k² g^{μν} - k^μ k^ν)`, entry by entry. -/
theorem vacuumPolarization_existsUnique (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 2 →
      ∀ C : Contraction 0 2 κ, IsOnePI C → (∃ f : Line C, IsLoopLine f) →
      ∀ (k : Fin 4 → ℝ) (μ ν : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![] ![] ![k, -k] (Fin.cons t v) ![] ![] ![μ, ν]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![] ![] ![k, -k] (Fin.cons t v) ![] ![] ![μ, ν]) ∧
    ∃! Pol : {s : ℝ // -(4 * P.m ^ 2) < s} → ℂ,
      ∀ (k : Fin 4 → ℝ) (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
        Tendsto (fun ε : ℝ => (1 / I) *
            onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν])
          (𝓝[>] 0)
          (𝓝 (Pol ⟨_, hk⟩ *
            ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))) :=
  sorry

/-- (Z₇) **The vacuum polarization function** `Π`, chosen from (Z₂). -/
noncomputable def vacuumPolarization (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    {s : ℝ // -(4 * P.m ^ 2) < s} → ℂ :=
  (vacuumPolarization_existsUnique P hm hM₁ hM₂ hPV₁ hPV₂).2.exists.choose

/-- (Z₈) **The on-shell condition for the photon** (62.11): `Π(0) = 0`. -/
def IsPhotonOnShell (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    Prop :=
  vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂
    ⟨0, neg_lt_zero.mpr (mul_pos four_pos (pow_pos hm 2))⟩ = 0

end QEDChallenge.QED.WickModel

namespace QEDChallenge.QED.OneLoop
open Matrix Complex Filter Topology MeasureTheory

/-- (C) The integrand of `i V^μ_{1 loop}(p', p)` in (62.40), with the measure factor `(2π)⁻⁴`:
`(ie)³ (1/i)³ (2π)⁻⁴ [γ^ρ S̃(p̸' + ℓ̸) γ^μ S̃(p̸ + ℓ̸) γ^ν] Δ̃_{νρ}(ℓ)`. -/
noncomputable def vertexIntegrand (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) •
    ∑ ν, ∑ ρ, photonPropagator mγ Λ ε ℓ ν ρ •
      (Dirac.gamma ρ * electronPropagator m ε (p' + ℓ) * Dirac.gamma μ *
        electronPropagator m ε (p + ℓ) * Dirac.gamma ν)

/-- (E) **The regulated one-loop vertex is well defined.** For `m, m_γ, Λ > 0` and on-shell
positive-energy `p`, `p'`, each entry of the integrand (C) is integrable in both stages of
prescription M1 for every `ε > 0`, and its energy-first integral has a unique limit as
`ε → 0⁺`. -/
theorem vertexLimit_existsUnique (e m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) :
    (∀ ε > 0,
      (∀ v : Fin 3 → ℝ,
        Integrable fun t : ℝ => vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons t v : Fin 4 → ℝ) i j) ∧
      Integrable fun v : Fin 3 → ℝ =>
        ∫ t : ℝ, vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons t v : Fin 4 → ℝ) i j) ∧
    ∃! V : ℂ, Tendsto
      (fun ε : ℝ => energyFirstIntegral fun ℓ => vertexIntegrand e m mγ Λ ε p' p μ ℓ i j)
      (𝓝[>] 0) (𝓝 V) :=
  sorry

/-- (F) The regulated one-loop vertex `V^μ_{1 loop}(p', p)` of (62.39)–(62.40): `1/i` times the
limit of (E), entry by entry. -/
noncomputable def vertexOneLoop (e m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => (1 / I) *
    (vertexLimit_existsUnique e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j).2.exists.choose

end QEDChallenge.QED.OneLoop

namespace QEDChallenge.QED.OneLoop
open Matrix Complex

/-- (J) The regulated vertex function `V^μ(p', p)` of (62.39) through order `e³`: the tree vertex
`Z₁ e γ^μ` plus the one-loop vertex (F). -/
noncomputable def vertexFunction (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((Z₁ * e : ℝ) : ℂ) • Dirac.gamma μ + vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ

/-- (K₀) The charge condition (63.1)–(63.2): `ū V^μ(p, p) u = e ū γ^μ u` for every on-shell
positive-energy `p`, every `μ`, every column `u` with `(p̸ + m) u = 0` and every row `ū` with
`ū (p̸ + m) = 0`. -/
def IsChargeNormalized (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) : Prop :=
  ∀ (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) (μ : Fin 4)
    (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((m : ℂ) • u) →
    w ᵥ* Dirac.slash p = -((m : ℂ) • w) →
    w ⬝ᵥ (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p p hp hp hp0 hp0 μ *ᵥ u)
      = (e : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))

/-- (G₀) The on-shell form-factor decomposition (63.18): `ū' V^μ u =
e ū' [A γ^μ - (i/m) B S^{μν} q_ν] u`, `q = p' - p`, for every `μ`, every column `u` with
`(p̸ + m) u = 0` and every row `ū'` with `ū' (p̸' + m) = 0`. -/
def IsFormFactorPair (e m : ℝ) (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (F : ℂ × ℂ) : Prop :=
  ∀ (μ : Fin 4) (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((m : ℂ) • u) →
    w ᵥ* Dirac.slash p' = -((m : ℂ) • w) →
    w ⬝ᵥ (V μ *ᵥ u) = (e : ℂ) * (w ⬝ᵥ ((F.1 • Dirac.gamma μ - (I / (m : ℂ) * F.2) •
      ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ u))

end QEDChallenge.QED.OneLoop

namespace QEDChallenge.QED.WickModel
open Complex
open _root_.QED _root_.QED.WickModel

/-- (T₅) The momentum flowing into vertex `t` through its `Ψ` field, for the line momenta `k`. -/
noncomputable def psiMomentum₂ {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pIn : Fin nf → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (t : Wick.FermionVertex κ) : Fin 4 → ℝ :=
  match h : C.1.1 (.inr t) with
  | .inl i => pIn i
  | .inr _ => k (.inl ⟨t, by simp [h]⟩)

open scoped Classical in
/-- (T₆) The momentum flowing into the vertex of the photon field `a` through `a`, for the line
momenta `k`. -/
noncomputable def photonMomentum₂ {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (a : Wick.PhotonSlot κ) : Fin 4 → ℝ :=
  (∑ j, if C.1.2 (.inl j) = .inr a then kIn j else 0) +
    ∑ g : PhotonLine C, ((if g.head = a then k (.inr g) else 0)
      - (if g.1 = a then k (.inr g) else 0))

open scoped Classical in
/-- (T₇) The amplitude (X₂₅) of the flavored contraction `(C, φ)`, with the momentum of each
internal line `f` given by `k f`. -/
noncomputable def contractionAmplitude₂ (P : Params) {nf nA N : ℕ}
    {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (φ : Flavoring κ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ α : Wick.FermionVertex κ → Fin 4, ∑ β : Wick.FermionVertex κ → Fin 4,
    ∑ lor : Wick.PhotonSlot κ → Fin 4,
      (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
          (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
          (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
        ((∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
            (psiMomentum₂ C pIn k) (photonMomentum₂ C kIn k) t) *
          (∏ f : FermionLine C, (1 / I) *
            QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε (k (.inl f))
              (β f.1) (α f.tail)) *
          ∏ g : PhotonLine C, (1 / I) *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr g)) (lor g.1) (lor g.head))

open scoped Classical in
/-- (T₈) The Pauli–Villars regulated amplitude (X₂₆) of a contraction for the line momenta `k`. -/
noncomputable def regulatedAmplitude₂ (P : Params) {nf nA N : ℕ}
    {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) : ℂ :=
  ∑ φ ∈ (Finset.univ : Finset (Flavoring κ)).filter (Preserves C),
    (loopWeight P C φ : ℂ) * contractionAmplitude₂ P C φ pIn kIn k αOut βIn μ

/-- (T₁) **The loop lines (chords)**: the internal line `f` is a chord when its two ends are
joined by a path of internal lines whose labels (X₂₀) are all larger than `f`'s. -/
def IsChord {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (f : Line C) : Prop :=
  Relation.ReflTransGen (Joined C {g | g.label ≤ f.label}) f.ends.1 f.ends.2

open scoped Classical in
/-- (T₃) The loop momentum carried by a chord: the chord numbered `r` by increasing label carries
`ℓ r`. -/
noncomputable def chordMomentum {nf nA N L : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : Contraction nf nA κ} (ℓ : Fin L → Fin 4 → ℝ) (f : Line C) : Fin 4 → ℝ :=
  if h : (Finset.univ.filter fun g : Line C => IsChord g ∧ g.label < f.label).card < L then
    ℓ ⟨_, h⟩
  else 0

open scoped Classical in
/-- (T₄) **Canonical routing with several loop momenta** (rule 8): each chord carries its loop
momentum; any other line carries the momentum injected into the side of its tail. -/
noncomputable def lineMomentum₂ {nf nA N L : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin L → Fin 4 → ℝ) (f : Line C) : Fin 4 → ℝ :=
  if IsChord f then chordMomentum ℓ f else
    ∑ v ∈ Finset.univ.filter (fun v => Relation.ReflTransGen
        (Joined C {g | g = f ∨ IsChord g}) f.ends.1 v),
      (externalMomentum C pOut pIn kIn v
        + ∑ g ∈ Finset.univ.filter (fun g : Line C => IsChord g),
          ((if g.ends.2 = v then chordMomentum ℓ g else 0)
            - (if g.ends.1 = v then chordMomentum ℓ g else 0)))

open scoped Classical in
/-- (T₂) The number of independent loops of a contraction: the number of chords (T₁). -/
noncomputable def loopCount {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) : ℕ :=
  (Finset.univ.filter fun f : Line C => IsChord f).card

end QEDChallenge.QED.WickModel

namespace QEDChallenge.QED.TwoLoop
open Complex

/-- (T₉) **The joint energy-first integral** for `L` loop momenta: all loop energies innermost,
then all spatial components; like the Bochner integral, it is `0` on non-integrable data. -/
noncomputable def jointEnergyFirstIntegral (L : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ) : ℂ :=
  ∫ v : Fin L → Fin 3 → ℝ, ∫ t : Fin L → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)

/-- (T₉′) **Integrability of both stages of the joint energy-first integral** (T₉). -/
def jointEnergyFirstIntegrable (L : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ) : Prop :=
  (∀ v : Fin L → Fin 3 → ℝ, MeasureTheory.Integrable fun t : Fin L → ℝ =>
      F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) ∧
    MeasureTheory.Integrable fun v : Fin L → Fin 3 → ℝ =>
      ∫ t : Fin L → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)

end QEDChallenge.QED.TwoLoop

namespace QEDChallenge.QED.WickModel
open Complex
open _root_.QED _root_.QED.WickModel

/-- (T₁₀) **The value of a contraction with any number of loops**: with `L = loopCount C` loop
momenta routed by (T₄), the regulated amplitude (T₈) times `(2π)^{-4L}`, integrated with the joint
energy-first prescription (T₉) at fixed `ε`. -/
noncomputable def contractionValue₂ (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  QED.TwoLoop.jointEnergyFirstIntegral (loopCount C) fun ℓ =>
    (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ

open scoped Classical in
/-- (T₁₁) **The 1PI function from the Wick expansion, up to two loops**: (X₂₈) with the value
(T₁₀). -/
noncomputable def onePIFunction₂ (P : Params) (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K),
      ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter IsOnePI,
        ((fermionSign C : ℤ) : ℂ) * contractionValue₂ P C pOut pIn kIn αOut βIn μ

end QEDChallenge.QED.WickModel

namespace QEDChallenge.QED.TwoLoop
open Matrix Complex Filter Topology
open _root_.QED.WickModel (Params)

/-- (HV₁) **The order-`e⁵` 1PI vertex at fixed `ε`**: `(1/i)` times the part of total order
exactly `5` in `e` of the 1PI function (T₁₁) with one external fermion pair and one external
photon, at outgoing momentum `p'`, incoming momentum `p` and photon momentum `p' - p`. -/
noncomputable def vertexOrderFive (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => (1 / I) *
    (WickModel.onePIFunction₂ P 1 1 5 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ) -
      WickModel.onePIFunction₂ P 1 1 4 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ))

/-- (HV₂) **The order-`e⁵` vertex as `ε → 0⁺`**: `V` is the limit of (HV₁) as `ε → 0⁺`, entry by
entry, for every `μ`, with all other parameters of `P` fixed. -/
def IsVertexOrderFiveLimit (P : Params) (p' p : Fin 4 → ℝ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ μ i j, Tendsto (fun ε => vertexOrderFive { P with ε := ε } p' p μ i j) (𝓝[>] 0)
    (𝓝 (V μ i j))

/-- (U₁) **The mass-independent fourth-order coefficient** of the electron's anomalous magnetic
moment, `A₁⁽⁴⁾ = 197/144 + π²/12 - (π²/2) ln 2 + (3/4) ζ(3)` (Passera (2007) eq. (9);
Barbieri–Mignaco–Remiddi (1972) eq. (1.7)), with `ζ(3) = ∑_{n ≥ 1} n⁻³`. -/
noncomputable def a1Four : ℝ :=
  197 / 144 + Real.pi ^ 2 / 12 - Real.pi ^ 2 / 2 * Real.log 2 +
    3 / 4 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3

/-- (U₂) **`A₁⁽⁴⁾` to four decimal places**: `-0.3285 < A₁⁽⁴⁾ < -0.3284`. -/
theorem a1Four_bounds : -0.3285 < a1Four ∧ a1Four < -0.3284 :=
  sorry

end QEDChallenge.QED.TwoLoop

namespace QEDChallenge.QED.TwoLoop
open _root_.QED.WickModel (Params)
open QEDChallenge.QED.WickModel (Contraction IsOnePI loopCount regulatedAmplitude₂ lineMomentum₂)

/-- (HV₀) **Every term of the order-`e⁵` vertex is a genuine integral.** For `ε > 0` and regulator
fermions satisfying the Pauli–Villars conditions, for every 1PI contraction `C` with one external
fermion pair and one external photon whose vertices have total order exactly `5` in `e`, at all
external momenta with momentum conservation and all external indices, the integrand of its value
(T₁₀) satisfies (T₉′): both stages of the joint energy-first integral converge absolutely. -/
theorem jointEnergyFirstIntegrable_vertexOrderFive (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {N : ℕ} {κ : Fin N → _root_.QED.Wick.VertexKind} (hκ : ∑ t, (κ t).order = 5)
    (C : Contraction 1 1 κ) (hC : IsOnePI C) {pOut pIn : Fin 1 → Fin 4 → ℝ}
    {kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  sorry

end QEDChallenge.QED.TwoLoop

namespace QEDChallenge.QED.TwoLoop
open Matrix Complex Filter Topology
open _root_.QED.WickModel (Params)
open QEDChallenge.QED.WickModel (IsElectronOnShell IsPhotonOnShell)

/-- (HV₃) **The fourth-order mass-independent coefficient of the electron's anomalous magnetic
moment, from the order-`e⁵` 1PI vertex (headline theorem).** Fix the model data `P₀` with
`e ≠ 0` and `m > 0`. Its regulators `M₁, M₂, c₁, c₂, m_γ, Λ` and its counterterms
`δ₁, δ₂, δ_m, δ₃` are replaced; its `ε` plays no role. For every `η > 0` there is `R_M` such that
for all regulator fermions heavier than the electron and than `R_M` and satisfying the
Pauli–Villars conditions there are `δ > 0` and `R` such that for `0 < m_γ < δ` and `Λ > R`
counterterms with the three conditions below exist, and for every choice of counterterms with
* the electron on shell (Z₅),
* the charge condition (K₀) for the one-loop vertex function (J) with `Z₁ = 1 + δ₁`,
* the photon on shell (Z₈),

there is `q₀ > 0` such that at every on-shell positive-energy pair `(p', p)` with
`0 < q² < q₀`, `q = p' - p`:
* the order-`e⁵` vertex (HV₁) has an `ε → 0⁺` limit (HV₂);
* every such limit has a form-factor pair (G₀), with the charge `e` factored out, and every such
  pair has its Pauli component within `η` of `A₁⁽⁴⁾ (α/π)²`, `α = e²/(4π)`:
  `|16 π⁴ F₂ / e⁴ - A₁⁽⁴⁾| < η`, with `A₁⁽⁴⁾` the constant (U₁).

So the limits are taken in the order `ε → 0⁺`, then `q² → 0⁺` at fixed regulators and
counterterms, then jointly `m_γ → 0⁺` and `Λ → ∞` at fixed regulator-fermion masses, then
`M₁, M₂ → ∞`. The conditions (Z₅), (K₀), (Z₈) are the order-`e²` conditions of the one-loop model
(the counterterms are single real numbers and the expansion is truncated). They make the
counterterms `e²` times numbers independent of `e`, so (HV₁) is `e⁵` times a matrix independent of
`e` and `F₂ / e⁴` is the coefficient of `e⁴` in `F₂`, not a limit in `e`. -/
theorem isFormFactorPair_vertexOrderFive_pauli_limit (P₀ : Params) (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ (M₁ M₂ c₁ c₂ : ℝ) (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂), RM < M₁ → RM < M₂ →
      ∀ (hPV₁ : 1 + c₁ + c₂ = 0) (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0),
      ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
        (∃ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ ∧
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ ∧
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hM₁ hM₂ hPV₁ hPV₂) ∧
        ∀ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ →
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ →
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hM₁ hM₂ hPV₁ hPV₂ →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ } p' p V) ∧
            ∀ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ } p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖16 * (Real.pi : ℂ) ^ 4 * F.2 / (P₀.e : ℂ) ^ 4 - (a1Four : ℂ)‖ < η :=
  sorry

/-- **The regulator fermions of (HV₃) exist above every bound**: for every electron mass `m` and
every `R_M` there are masses `M₁, M₂` above `m` and `R_M` and coefficients `c₁, c₂` satisfying the
Pauli–Villars conditions `1 + c₁ + c₂ = 0` and `m² + c₁ M₁² + c₂ M₂² = 0`. -/
theorem exists_pauliVillars_regulators (m RM : ℝ) :
    ∃ M₁ M₂ c₁ c₂ : ℝ, m < M₁ ∧ m < M₂ ∧ RM < M₁ ∧ RM < M₂ ∧ 1 + c₁ + c₂ = 0 ∧
      m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 :=
  sorry

end QEDChallenge.QED.TwoLoop

end
