/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntDD
public import QED.TwoLoop.ClassIntegrableVP
public import QED.TwoLoop.NestedVPAmplitude
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Tools for the two-loop set (b) representatives

Helpers for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53), used for the
bubble–`δ₃` and `δ₃`–bubble representatives `repBD s`, `repDB s`:

* **One closed fermion loop** (`regulatedAmplitude₂_eq_sum_loopFlavour`): for a contraction whose
  fermion fields lie either on the cycle of the external field or on one closed loop `L` of gauge
  vertices, the regulated amplitude (T₈) is `∑_f c_f` times the amplitude (T₇) of the flavoring
  with flavour `f` on `L` and `0` elsewhere.
* **The spinor sum of an open chain through three vertices and a loop through two**
  (`sum_spinor_chain3_loop2`): the open-line matrix entry times the loop trace.
* **The Ward identity of the loop** (`trace_ward`): `Tr[γ^σ S̃(P) k̸ S̃(Q)]` with `k = P - Q`, in
  terms of `Q^σ`, `P^σ` and the two denominators; it lowers the numerator degree of a loop
  contracted with its photon momentum.
* **The single-denominator flavour sum** (`flavourSum_single`): under the two Pauli–Villars
  conditions, `∑_f c_f (A + x_f)⁻¹ = (x₁ - x₀)(x₂ - x₀) ∏_f (A + x_f)⁻¹`.
* **Transfer of the pointwise bound** to a loop matrix with more lines
  (`RefinedBound.map_rows`), and the bound for chains of four electron numerators
  (`refinedBound_chain4`).
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.RepsInt

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix RefinedBound lineWeight
  refinedBound_lineMomentum)

/-! ### One closed fermion loop -/

section LoopFlavour

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The flavoring with flavour `f` on the fermion fields of `L` and `0` elsewhere. -/
def flavL (L : Wick.FermionVertex κ → Bool) (hL : ∀ t, L t = true → κ t.1 = .gauge) (f : Fin 3) :
    Flavoring κ :=
  ⟨fun t => if L t then f else 0, fun t ht => by
    by_cases h : L t = true
    · exact absurd (hL t h) ht
    · simp [h]⟩

open scoped Classical in
/-- **A contraction with one closed loop**: if the fermion fields of the vertices in `L` (all
gauge vertices, `t₀ ∈ L`) lie on the cycle of `σ` through `t₀`, the others on the cycle through the
external field, and these two cycles differ, then the regulated amplitude (T₈) is the sum over the
loop flavour `f` of `c_f` times the amplitude (T₇) of `flavL L f`. -/
theorem regulatedAmplitude₂_eq_sum_loopFlavour (P : Params) (C : Contraction 1 nA κ)
    (L : Wick.FermionVertex κ → Bool) (hL : ∀ t, L t = true → κ t.1 = .gauge)
    (t₀ : Wick.FermionVertex κ) (ht₀ : L t₀ = true)
    (hpres : ∀ f, Preserves C (flavL L hL f))
    (hin : ∀ t, L t = true → Equiv.Perm.SameCycle C.1.1 (.inr t) (.inr t₀))
    (hout : ∀ x, (∀ t, x = .inr t → L t = false) → Equiv.Perm.SameCycle C.1.1 x (.inl 0))
    (hsep : ¬ Equiv.Perm.SameCycle C.1.1 (.inl 0) (.inr t₀))
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude₂ P C pIn kIn k αOut βIn μ =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude₂ P C (flavL L hL f) pIn kIn k αOut βIn μ := by
  have hflav : ∀ f, (flavL L hL f).1 t₀ = f := fun f => by simp [flavL, ht₀]
  have hiff : ∀ φ, Preserves C φ ↔ φ = flavL L hL (φ.1 t₀) := by
    intro φ
    refine ⟨fun hφ => Subtype.ext (funext fun t => ?_), fun h => h ▸ hpres _⟩
    by_cases ht : L t = true
    · have := QED.TwoLoop.Relabel.fermionFlavor_eq_of_sameCycle hφ (hin t ht)
      simpa [fermionFlavor, flavL, ht] using this
    · have := QED.TwoLoop.Relabel.fermionFlavor_eq_of_sameCycle hφ
        (hout (.inr t) fun t' h => by cases h; simpa using ht)
      simpa [fermionFlavor, flavL, ht] using this
  have hsum : ∑ φ ∈ (Finset.univ : Finset (Flavoring κ)).filter (Preserves C),
      (loopWeight P C φ : ℂ) * contractionAmplitude₂ P C φ pIn kIn k αOut βIn μ =
      ∑ f : Fin 3, (loopWeight P C (flavL L hL f) : ℂ) *
        contractionAmplitude₂ P C (flavL L hL f) pIn kIn k αOut βIn μ :=
    Finset.sum_nbij' (fun φ => φ.1 t₀) (flavL L hL) (fun _ _ => Finset.mem_univ _)
      (fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpres f⟩)
      (fun φ hφ => ((hiff φ).mp (Finset.mem_filter.mp hφ).2).symm)
      (fun f _ => hflav f)
      (fun φ hφ => by rw [← (hiff φ).mp (Finset.mem_filter.mp hφ).2])
  -- the closed loops
  let loop0 : ClosedLoop C := ⟨Quotient.mk _ (.inr t₀), fun i h => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hsep (Quotient.exact h)⟩
  have hloop : ∀ q : ClosedLoop C, q = loop0 := by
    rintro ⟨q, hq⟩
    apply Subtype.ext
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    by_cases hx : ∃ t, x = .inr t ∧ L t = true
    · obtain ⟨t, rfl, ht⟩ := hx
      exact Quotient.sound (hin t ht)
    · refine absurd (Quotient.sound (hout x fun t h => ?_).symm) (hq 0)
      by_contra h'
      exact hx ⟨t, h, by simpa using h'⟩
  have hw : ∀ f, loopWeight P C (flavL L hL f) = P.loopCoeff f := by
    intro f
    rw [loopWeight, Fintype.prod_eq_single loop0 fun q hq => absurd (hloop q) hq]
    have hq : (Quotient.mk _ loop0.1.out : Quotient (Equiv.Perm.SameCycle.setoid C.1.1)) =
        Quotient.mk _ (.inr t₀) := Quotient.out_eq _
    have hsc : Equiv.Perm.SameCycle C.1.1 loop0.1.out (.inr t₀) := Quotient.exact hq
    rw [QED.TwoLoop.Relabel.fermionFlavor_eq_of_sameCycle (hpres f) hsc]
    simp only [fermionFlavor, hflav]
  rw [regulatedAmplitude₂, hsum]
  simp only [hw]

end LoopFlavour

/-! ### The spinor sum of an open chain and a loop -/

section Spinor

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The two spinor index families on five points as ten values, in the order of the loop
`a(y₁) b(y₂) a(y₂) b(y₁)`, the open line `a(x₃) b(x₂) a(x₂) b(x₁)`, and last `a(x₁) b(x₃)`. -/
def spinEquiv5 {x₁ x₂ x₃ y₁ y₂ : X} (hd : [x₁, x₂, x₃, y₁, y₂].Nodup)
    (hX : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃ ∨ x = y₁ ∨ x = y₂) :
    (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (X → Fin 4) × (X → Fin 4) where
  toFun := fun ⟨a3, b4, a4, b3, a0, b1, a1, b2, a2, b0⟩ =>
    (fun t => if t = x₃ then a0 else if t = x₂ then a1 else if t = x₁ then a2 else
      if t = y₁ then a3 else a4,
     fun t => if t = x₃ then b0 else if t = x₂ then b1 else if t = x₁ then b2 else
      if t = y₁ then b3 else b4)
  invFun p := (p.1 y₁, p.2 y₂, p.1 y₂, p.2 y₁, p.1 x₃, p.2 x₂, p.1 x₂, p.2 x₁, p.1 x₁, p.2 x₃)
  left_inv x := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true] at hd
    obtain ⟨⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45⟩ := hd
    obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := x
    have := Ne.symm h12; have := Ne.symm h13; have := Ne.symm h14; have := Ne.symm h15
    have := Ne.symm h23; have := Ne.symm h24; have := Ne.symm h25; have := Ne.symm h34
    have := Ne.symm h35; have := Ne.symm h45
    clear hX
    simp [*]
  right_inv p := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true] at hd
    obtain ⟨⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45⟩ := hd
    obtain ⟨α, β⟩ := p
    have := Ne.symm h12; have := Ne.symm h13; have := Ne.symm h14; have := Ne.symm h15
    have := Ne.symm h23; have := Ne.symm h24; have := Ne.symm h25; have := Ne.symm h34
    have := Ne.symm h35; have := Ne.symm h45
    refine Prod.ext (funext fun t => ?_) (funext fun t => ?_) <;>
      rcases hX t with rfl | rfl | rfl | rfl | rfl <;> clear hX <;> simp [*]

/-- **The spinor sum of an open chain through `x₁, x₂, x₃` (outgoing first) and a loop through
`y₁, y₂`**: the entry of the open-line matrix times the trace of the loop. -/
theorem sum_spinor_chain3_loop2 {x₁ x₂ x₃ y₁ y₂ : X} (hd : [x₁, x₂, x₃, y₁, y₂].Nodup)
    (hX : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃ ∨ x = y₁ ∨ x = y₂)
    (A₁ A₂ A₃ S₁ S₂ B₁ B₂ T₁ T₂ : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4,
      (if α x₁ = a ∧ β x₃ = b then (1 : ℂ) else 0) *
        (A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
          A₃ (α x₃) (β x₃) *
          (B₁ (α y₁) (β y₁) * T₁ (β y₁) (α y₂) * B₂ (α y₂) (β y₂) * T₂ (β y₂) (α y₁))) =
      (A₁ * S₁ * A₂ * S₂ * A₃) a b * Matrix.trace (B₁ * T₁ * B₂ * T₂) := by
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hd'
  obtain ⟨⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45⟩ := hd'
  rw [← Fintype.sum_prod_type', ← (spinEquiv5 hd hX).sum_comp]
  simp only [Fintype.sum_prod_type, spinEquiv5, Equiv.coe_fn_mk]
  simp only [Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h23, Ne.symm h24,
    Ne.symm h25, Ne.symm h34, Ne.symm h35, Ne.symm h45, h12, h13, h14, h23, h24, h34,
    ite_true, ite_false]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]

end Spinor

/-! ### The Ward identity of the loop -/

section Ward

theorem slash_sub (P Q : Fin 4 → ℝ) : Dirac.slash (P - Q) = Dirac.slash P - Dirac.slash Q := by
  simp only [Dirac.slash, Minkowski.lower, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    ofReal_sub, sub_smul]

/-- `Tr[γ^σ (M - X̸)] = 4 X^σ`. -/
theorem trace_gamma_mul_electronNumerator (M : ℝ) (X : Fin 4 → ℝ) (σ : Fin 4) :
    (Dirac.gamma σ * electronNumerator M X).trace = 4 * ((X σ : ℝ) : ℂ) := by
  simp only [electronNumerator, Dirac.slash, Minkowski.lower, Minkowski.metric, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  fin_cases σ <;> simp [Dirac.gamma]
  all_goals ring_nf
  all_goals simp only [I_sq]
  all_goals ring

/-- **The Ward identity** at the numerator level: with `k = P - Q`,
`(M - P̸) k̸ (M - Q̸) = (P² + M²)(M - Q̸) - (Q² + M²)(M - P̸)`. -/
theorem electronNumerator_ward (M : ℝ) (P Q : Fin 4 → ℝ) :
    electronNumerator M P * Dirac.slash (P - Q) * electronNumerator M Q =
      (((Minkowski.dot P P + M ^ 2 : ℝ) : ℂ)) • electronNumerator M Q -
        (((Minkowski.dot Q Q + M ^ 2 : ℝ) : ℂ)) • electronNumerator M P := by
  rw [slash_sub]
  have hP := Dirac.slash_mul_slash P
  have hQ := Dirac.slash_mul_slash Q
  set A := Dirac.slash P
  set B := Dirac.slash Q
  simp only [electronNumerator]
  have e1 : ((M : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - A) * (A - B) *
      ((M : ℂ) • 1 - B) = ((M : ℂ) * M) • A - ((M : ℂ) * M) • B +
        (M : ℂ) • (B * B) - (M : ℂ) • (A * A) + (A * A) * B - A * (B * B) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, smul_sub, smul_smul]
    abel
  rw [e1, hP, hQ]
  simp only [smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one, smul_smul]
  push_cast
  module

/-- **The Ward identity of a loop trace**: `Tr[γ^σ (M - P̸) k̸ (M - Q̸)]` with `k = P - Q` is
`4 (P² + M²) Q^σ - 4 (Q² + M²) P^σ`. -/
theorem trace_ward (M : ℝ) (P Q : Fin 4 → ℝ) (σ : Fin 4) :
    (Dirac.gamma σ * (electronNumerator M P * Dirac.slash (P - Q) * electronNumerator M Q)).trace =
      4 * ((Minkowski.dot P P + M ^ 2 : ℝ) : ℂ) * ((Q σ : ℝ) : ℂ) -
        4 * ((Minkowski.dot Q Q + M ^ 2 : ℝ) : ℂ) * ((P σ : ℝ) : ℂ) := by
  rw [electronNumerator_ward, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul, trace_gamma_mul_electronNumerator,
    trace_gamma_mul_electronNumerator, smul_eq_mul, smul_eq_mul]
  ring

end Ward

/-! ### The single-denominator flavour sum -/

/-- **The regulator-fermion sum of a single denominator**: under `1 + c₁ + c₂ = 0` and
`x₀ + c₁ x₁ + c₂ x₂ = 0`, `∑_f c_f (A + x_f)⁻¹ = (x₁ - x₀)(x₂ - x₀) ∏_f (A + x_f)⁻¹`. -/
theorem flavourSum_single {A x0 x1 x2 c1 c2 : ℂ} (h1 : 1 + c1 + c2 = 0)
    (h2 : x0 + c1 * x1 + c2 * x2 = 0) (hA0 : A + x0 ≠ 0) (hA1 : A + x1 ≠ 0) (hA2 : A + x2 ≠ 0) :
    (A + x0)⁻¹ + c1 * (A + x1)⁻¹ + c2 * (A + x2)⁻¹ =
      (x1 - x0) * (x2 - x0) * ((A + x0)⁻¹ * (A + x1)⁻¹ * (A + x2)⁻¹) := by
  have key : (A + x0)⁻¹ + c1 * (A + x1)⁻¹ + c2 * (A + x2)⁻¹ -
      (x1 - x0) * (x2 - x0) * ((A + x0)⁻¹ * (A + x1)⁻¹ * (A + x2)⁻¹) =
      ((A + x0) * (A + x1 + x2) * (1 + c1 + c2) - (A + x0) * (x0 + c1 * x1 + c2 * x2)) *
        ((A + x0)⁻¹ * (A + x1)⁻¹ * (A + x2)⁻¹) := by
    field_simp
    ring
  rw [h1, h2] at key
  linear_combination key

/-- The single-denominator flavour sum for propagator denominators. -/
theorem flavourSum_single_propDenom {ε : ℝ} (hε : ε ≠ 0) (u : Fin 4 → ℝ) {m M₁ M₂ c₁ c₂ : ℝ}
    (h1 : 1 + c₁ + c₂ = 0) (h2 : m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) :
    (propDenom m ε u)⁻¹ + (c₁ : ℂ) * (propDenom M₁ ε u)⁻¹ + (c₂ : ℂ) * (propDenom M₂ ε u)⁻¹ =
      ((((M₁ ^ 2 - m ^ 2) * (M₂ ^ 2 - m ^ 2)) : ℝ) : ℂ) *
        ((propDenom m ε u)⁻¹ * (propDenom M₁ ε u)⁻¹ * (propDenom M₂ ε u)⁻¹) := by
  have hd : ∀ (M : ℝ), propDenom M ε u =
      (((Minkowski.dot u u : ℝ) : ℂ) - (ε : ℂ) * I) + ((M ^ 2 : ℝ) : ℂ) := by
    intro M
    simp only [propDenom]
    push_cast
    ring
  have hne : ∀ (M : ℝ), (((Minkowski.dot u u : ℝ) : ℂ) - (ε : ℂ) * I) + ((M ^ 2 : ℝ) : ℂ) ≠ 0 :=
    fun M => hd M ▸ propDenom_ne_zero hε u
  have h1' : (1 : ℂ) + c₁ + c₂ = 0 := by exact_mod_cast h1
  have h2' : ((m ^ 2 : ℝ) : ℂ) + c₁ * ((M₁ ^ 2 : ℝ) : ℂ) + c₂ * ((M₂ ^ 2 : ℝ) : ℂ) = 0 := by
    exact_mod_cast h2
  simp only [hd]
  rw [flavourSum_single h1' h2' (hne m) (hne M₁) (hne M₂)]
  push_cast
  ring

/-! ### Pointwise bounds -/

open QED.TwoLoop.ClassIntegrable (RefinedBoundMat)

/-- **Transfer of the pointwise bound** to a loop matrix containing the rows of `α`. -/
theorem RefinedBound.map_rows {m m' : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ}
    {α' : Fin (m' + 1) → Fin 2 → ℝ} (f : Fin (m + 1) ↪ Fin (m' + 1)) (hf : ∀ i, α' (f i) = α i)
    {E : Finset (Fin (m + 1))} {k : ℕ} {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h : RefinedBound α E k F) : RefinedBound α' (E.map f) k F := by
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨C, hC, fun A hA ℓ => ?_⟩
  have : lineWeight α' (E.map f) A = lineWeight α E A := by
    simp only [lineWeight, Finset.prod_map, hf]
  rw [this]
  exact hF A hA ℓ

/-- The electron numerator at a line momentum, as a matrix bound by its line. -/
theorem refinedBoundMat_electronNumerator' {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (e : Fin (m + 1)) (mass : ℝ) :
    RefinedBoundMat al {e} 1 fun ℓ => electronNumerator mass (lineMomentum al p e ℓ) :=
  fun i j => QED.TwoLoop.ClassIntegrable.refinedBound_electronNumerator al p e mass i j

/-- **The bound for a chain of four electron numerators** at the momenta of four distinct lines,
with a constant matrix in the middle. -/
theorem refinedBound_chain4 {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    {e₁ e₂ e₃ e₄ : Fin (m + 1)} (hd : [e₁, e₂, e₃, e₄].Nodup) (m₁ m₂ m₃ m₄ : ℝ)
    (C : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    RefinedBound al {e₁, e₂, e₃, e₄} 4 fun ℓ =>
      (electronNumerator m₁ (lineMomentum al p e₁ ℓ) * electronNumerator m₂ (lineMomentum al p e₂ ℓ) *
        C * electronNumerator m₃ (lineMomentum al p e₃ ℓ) *
          electronNumerator m₄ (lineMomentum al p e₄ ℓ)) a b := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hd
  obtain ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hd
  have h := ((((refinedBoundMat_electronNumerator' al p e₁ m₁).mul
    (refinedBoundMat_electronNumerator' al p e₂ m₂) (by simpa using h12)).mul
      (RefinedBoundMat.const C) (by simp)).mul
        (refinedBoundMat_electronNumerator' al p e₃ m₃)
          (by simp [Ne.symm h13, Ne.symm h23])).mul
          (refinedBoundMat_electronNumerator' al p e₄ m₄)
            (by simp [Ne.symm h14, Ne.symm h24, Ne.symm h34])
  refine (h a b).mono ?_ (by norm_num)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, or_false] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

end QED.ChainProof.RepsInt

end
