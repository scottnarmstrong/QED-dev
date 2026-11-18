/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.RegulatedAmplitude

/-!
# The flavour sum of a contraction with at most one closed loop

Helper level, Phase 5 Stage 0 (decision D-50), for the flavour-block split of the headline (HM₂).

For a Wick contraction `C` with fermion permutation `σ = C.1.1`, a vertex `t` is **on the open
line** (`OnOpen C t`) when `Ψ_t` lies in the `σ`-cycle of an external field. The contraction is
**simple** (`IsSimple C`) when every vertex off the open lines is a gauge vertex and all of them lie
in one `σ`-cycle: `C` has at most one closed fermion loop, made of gauge vertices. For a simple
contraction and any flavour data `Φ`:

* the flavourings preserved by `C` are the `loopFlavoring Φ C f`, `f : F`, that put the open-line
  flavour on the open lines and `f` on the loop (`preserves_iff`);
* their regulator weight is `Φ.coeff f` when `C` has a loop, `1` otherwise
  (`loopWeight_loopFlavoring`);
* the amplitude depends on `Φ` and `f` only through the open-line mass and the loop mass
  (`contractionAmplitude₂_loopFlavoring`);

so (`regulatedAmplitude₂_of_hasLoop`, `regulatedAmplitude₂_of_not_hasLoop`)

`regulatedAmplitude₂ P Φ C = ∑_f Φ.coeff f · A(m_open, Φ.mass f)` (with a loop),
`regulatedAmplitude₂ P Φ C = A(m_open, m_open)` (without),

with `A(a, b) = loopAmp P C hS a b` a single amplitude of a two-flavour model. Both are affine in
the flavour data `(mass, coeff)` regarded as the measure `∑_f coeff f δ_{mass f}`; this is what lets
the multi-lepton vertex be written through T1's vertices.
-/

@[expose] public section

open Complex
open QED.WickModel (Params Contraction FermionLine ClosedLoop)

namespace QED.Lepton.Proof.HM

open scoped Classical

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The vertex `t` lies on an open fermion line: `Ψ_t` is in the `σ`-cycle of an external field. -/
def OnOpen (C : Contraction nf nA κ) (t : Wick.FermionVertex κ) : Prop :=
  ∃ i : Fin nf, Equiv.Perm.SameCycle C.1.1 (.inr t) (.inl i)

/-- The fermion field `a` lies on an open line. -/
def FieldOnOpen (C : Contraction nf nA κ) (a : Fin nf ⊕ Wick.FermionVertex κ) : Prop :=
  ∃ i : Fin nf, Equiv.Perm.SameCycle C.1.1 a (.inl i)

/-- **Simple contractions**: every vertex off the open lines is a gauge vertex, and all such
vertices lie in one `σ`-cycle (at most one closed loop). -/
def IsSimple (C : Contraction nf nA κ) : Prop :=
  (∀ t, ¬ OnOpen C t → κ t.1 = .gauge) ∧
    ∀ t s, ¬ OnOpen C t → ¬ OnOpen C s → Equiv.Perm.SameCycle C.1.1 (.inr t) (.inr s)

/-- The contraction has a closed fermion loop. -/
def HasLoop (C : Contraction nf nA κ) : Prop :=
  ∃ t, ¬ OnOpen C t

theorem fieldOnOpen_inl (C : Contraction nf nA κ) (i : Fin nf) : FieldOnOpen C (.inl i) :=
  ⟨i, Equiv.Perm.SameCycle.refl _ _⟩

theorem fieldOnOpen_apply (C : Contraction nf nA κ) (a : Fin nf ⊕ Wick.FermionVertex κ) :
    FieldOnOpen C (C.1.1 a) ↔ FieldOnOpen C a := by
  simp only [FieldOnOpen, Equiv.Perm.sameCycle_apply_left]

variable {F : Type} (Φ : Flavors F)

/-- A preserved flavouring is constant on `σ`-cycles. -/
theorem fermionFlavor_eq_of_sameCycle {C : Contraction nf nA κ} {φ : Flavoring Φ κ}
    (hφ : Preserves Φ C φ) {a b : Fin nf ⊕ Wick.FermionVertex κ}
    (h : Equiv.Perm.SameCycle C.1.1 a b) :
    fermionFlavor Φ φ a = fermionFlavor Φ φ b := by
  have h1 : ∀ x, fermionFlavor Φ φ (C.1.1 x) = fermionFlavor Φ φ x := hφ
  have h2 : ∀ x, fermionFlavor Φ φ (C.1.1⁻¹ x) = fermionFlavor Φ φ x := fun x => by
    rw [← h1 (C.1.1⁻¹ x)]
    simp
  obtain ⟨n, rfl⟩ := h
  induction n using Int.induction_on generalizing a with
  | zero => simp
  | succ k ih => rw [zpow_add_one, Equiv.Perm.mul_apply, ← ih, h1]
  | pred k ih => rw [zpow_sub_one, Equiv.Perm.mul_apply, ← ih, h2]

/-- A preserved flavouring has the open-line flavour on the open lines. -/
theorem flavor_eq_openLine {C : Contraction nf nA κ} {φ : Flavoring Φ κ} (hφ : Preserves Φ C φ)
    {t : Wick.FermionVertex κ} (ht : OnOpen C t) : φ.1 t = Φ.openLine := by
  obtain ⟨i, hi⟩ := ht
  exact fermionFlavor_eq_of_sameCycle Φ hφ hi

/-- **The flavouring with loop flavour `f`**: the open-line flavour on the open lines, `f` on the
closed loop. -/
noncomputable def loopFlavoring {C : Contraction nf nA κ} (hS : IsSimple C) (f : F) :
    Flavoring Φ κ :=
  ⟨fun t => if OnOpen C t then Φ.openLine else f, fun t ht => by
    have : OnOpen C t := by
      by_contra h
      exact ht (hS.1 t h)
    simp [this]⟩

theorem loopFlavoring_apply {C : Contraction nf nA κ} (hS : IsSimple C) (f : F)
    (t : Wick.FermionVertex κ) :
    (loopFlavoring Φ hS f).1 t = if OnOpen C t then Φ.openLine else f :=
  rfl

theorem fermionFlavor_loopFlavoring {C : Contraction nf nA κ} (hS : IsSimple C) (f : F)
    (a : Fin nf ⊕ Wick.FermionVertex κ) :
    fermionFlavor Φ (loopFlavoring Φ hS f) a =
      if FieldOnOpen C a then Φ.openLine else f := by
  rcases a with i | t
  · simp [fermionFlavor, fieldOnOpen_inl]
  · rfl

theorem preserves_loopFlavoring {C : Contraction nf nA κ} (hS : IsSimple C) (f : F) :
    Preserves Φ C (loopFlavoring Φ hS f) := by
  intro a
  rw [fermionFlavor_loopFlavoring, fermionFlavor_loopFlavoring]
  simp only [fieldOnOpen_apply]

/-- With a loop vertex `t₀`, a flavouring is preserved iff it is `loopFlavoring (φ t₀)`. -/
theorem eq_loopFlavoring {C : Contraction nf nA κ} (hS : IsSimple C) {φ : Flavoring Φ κ}
    (hφ : Preserves Φ C φ) {t₀ : Wick.FermionVertex κ} (h₀ : ¬ OnOpen C t₀) :
    φ = loopFlavoring Φ hS (φ.1 t₀) := by
  refine Subtype.ext (funext fun t => ?_)
  rw [loopFlavoring_apply]
  by_cases ht : OnOpen C t
  · simp only [ht, ↓reduceIte, flavor_eq_openLine Φ hφ ht]
  · simp only [ht, ↓reduceIte]
    exact (fermionFlavor_eq_of_sameCycle Φ hφ (hS.2 t₀ t h₀ ht)).symm

/-- Without a loop, the only preserved flavouring is the open-line one. -/
theorem eq_loopFlavoring_of_not_hasLoop {C : Contraction nf nA κ} (hS : IsSimple C)
    (hL : ¬ HasLoop C) {φ : Flavoring Φ κ} (hφ : Preserves Φ C φ) (f : F) :
    φ = loopFlavoring Φ hS f := by
  refine Subtype.ext (funext fun t => ?_)
  have ht : OnOpen C t := by
    by_contra h
    exact hL ⟨t, h⟩
  simp only [loopFlavoring_apply, ht, ↓reduceIte, flavor_eq_openLine Φ hφ ht]

theorem loopFlavoring_injective {C : Contraction nf nA κ} (hS : IsSimple C) (hL : HasLoop C) :
    Function.Injective (loopFlavoring Φ hS) := by
  obtain ⟨t₀, h₀⟩ := hL
  intro f g hfg
  have := congrArg (fun φ : Flavoring Φ κ => φ.1 t₀) hfg
  simpa only [loopFlavoring_apply, h₀, ↓reduceIte] using this

/-! ### The closed loops and the weight -/

/-- The representative of a closed loop is a vertex field off the open lines. -/
theorem closedLoop_out {C : Contraction nf nA κ} (q : ClosedLoop C) :
    ¬ FieldOnOpen C q.1.out := by
  rintro ⟨i, hi⟩
  apply q.2 i
  rw [← Quotient.out_eq q.1]
  exact (Quotient.sound hi).symm

theorem fermionFlavor_closedLoop {C : Contraction nf nA κ} (hS : IsSimple C) (f : F)
    (q : ClosedLoop C) : fermionFlavor Φ (loopFlavoring Φ hS f) q.1.out = f := by
  simp only [fermionFlavor_loopFlavoring, closedLoop_out q, ↓reduceIte]

theorem closedLoop_subsingleton {C : Contraction nf nA κ} (hS : IsSimple C) :
    Subsingleton (ClosedLoop C) := by
  refine ⟨fun q q' => Subtype.ext ?_⟩
  have h1 := closedLoop_out q
  have h2 := closedLoop_out q'
  rw [← Quotient.out_eq q.1, ← Quotient.out_eq q'.1]
  refine Quotient.sound ?_
  rcases hq : q.1.out with i | t
  · exact absurd (hq ▸ fieldOnOpen_inl C i) h1
  rcases hq' : q'.1.out with i' | t'
  · exact absurd (hq' ▸ fieldOnOpen_inl C i') h2
  rw [hq] at h1
  rw [hq'] at h2
  exact hS.2 t t' (fun ⟨i, hi⟩ => h1 ⟨i, hi⟩) (fun ⟨i, hi⟩ => h2 ⟨i, hi⟩)

theorem closedLoop_isEmpty {C : Contraction nf nA κ} (hL : ¬ HasLoop C) :
    IsEmpty (ClosedLoop C) := by
  refine ⟨fun q => ?_⟩
  have h1 := closedLoop_out q
  rcases hq : q.1.out with i | t
  · exact absurd (hq ▸ fieldOnOpen_inl C i) h1
  · rw [hq] at h1
    exact hL ⟨t, fun ⟨i, hi⟩ => h1 ⟨i, hi⟩⟩

theorem closedLoop_nonempty {C : Contraction nf nA κ} (hL : HasLoop C) :
    Nonempty (ClosedLoop C) := by
  obtain ⟨t, ht⟩ := hL
  refine ⟨⟨Quotient.mk _ (.inr t), fun i h => ht ⟨i, ?_⟩⟩⟩
  exact (Quotient.exact h).symm

/-- **The weight of the loop flavouring**: `Φ.coeff f` with a loop, `1` without. -/
theorem loopWeight_loopFlavoring_of_hasLoop {C : Contraction nf nA κ} (hS : IsSimple C)
    (hL : HasLoop C) (f : F) : loopWeight Φ C (loopFlavoring Φ hS f) = Φ.coeff f := by
  classical
  have hsub := closedLoop_subsingleton hS
  obtain ⟨q₀⟩ := closedLoop_nonempty hL
  unfold loopWeight
  rw [Fintype.prod_eq_single q₀ fun q hq => absurd (Subsingleton.elim q q₀) hq,
    fermionFlavor_closedLoop]

theorem loopWeight_loopFlavoring_of_not_hasLoop {C : Contraction nf nA κ} (hS : IsSimple C)
    (hL : ¬ HasLoop C) (f : F) : loopWeight Φ C (loopFlavoring Φ hS f) = 1 := by
  classical
  have := closedLoop_isEmpty hL
  unfold loopWeight
  exact Finset.prod_of_isEmpty _

/-! ### The amplitude -/

/-- The amplitude depends on the flavour data and the flavouring only through the masses of the
internal fermion lines. -/
theorem contractionAmplitude₂_congr {F' : Type} (Ψ : Flavors F') (P : Params)
    (C : Contraction nf nA κ) (φ : Flavoring Φ κ) (ψ : Flavoring Ψ κ)
    (h : ∀ f : FermionLine C, Φ.mass (φ.1 f.1) = Ψ.mass (ψ.1 f.1))
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : QED.WickModel.Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude₂ P Φ C φ pIn kIn k αOut βIn μ =
      contractionAmplitude₂ P Ψ C ψ pIn kIn k αOut βIn μ := by
  unfold contractionAmplitude₂
  simp only [h]

/-- The two-flavour data with masses `a` (open line, `false`) and `b` (loop, `true`). -/
def biFlavors (a b : ℝ) : Flavors Bool where
  mass x := if x then b else a
  coeff _ := 1
  openLine := false

/-- **The amplitude with open-line mass `a` and loop mass `b`.** -/
noncomputable def loopAmp (P : Params) {C : Contraction nf nA κ} (hS : IsSimple C) (a b : ℝ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : QED.WickModel.Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  contractionAmplitude₂ P (biFlavors a b) C (loopFlavoring (biFlavors a b) hS true) pIn kIn k
    αOut βIn μ

theorem contractionAmplitude₂_loopFlavoring (P : Params) {C : Contraction nf nA κ}
    (hS : IsSimple C) (f : F) (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : QED.WickModel.Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude₂ P Φ C (loopFlavoring Φ hS f) pIn kIn k αOut βIn μ =
      loopAmp P hS (Φ.mass Φ.openLine) (Φ.mass f) pIn kIn k αOut βIn μ := by
  refine contractionAmplitude₂_congr Φ _ P C _ _ (fun l => ?_) pIn kIn k αOut βIn μ
  rw [loopFlavoring_apply, loopFlavoring_apply]
  by_cases h : OnOpen C l.1
  · simp [h, biFlavors]
  · simp [h, biFlavors]

/-! ### The regulated amplitude -/

/-- **With a loop**: `regulatedAmplitude₂ P Φ C = ∑_f Φ.coeff f · A(m_open, Φ.mass f)`. -/
theorem regulatedAmplitude₂_of_hasLoop [Fintype F] [DecidableEq F] (P : Params)
    {C : Contraction nf nA κ} (hS : IsSimple C) (hL : HasLoop C) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : QED.WickModel.Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude₂ P Φ C pIn kIn k αOut βIn μ =
      ∑ f, (Φ.coeff f : ℂ) * loopAmp P hS (Φ.mass Φ.openLine) (Φ.mass f) pIn kIn k αOut βIn μ := by
  classical
  obtain ⟨t₀, h₀⟩ := hL
  unfold regulatedAmplitude₂
  have hfil : (Finset.univ : Finset (Flavoring Φ κ)).filter (Preserves Φ C) =
      Finset.univ.image (loopFlavoring Φ hS) := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    refine ⟨fun hφ => ⟨φ.1 t₀, (eq_loopFlavoring Φ hS hφ h₀).symm⟩, ?_⟩
    rintro ⟨f, rfl⟩
    exact preserves_loopFlavoring Φ hS f
  rw [hfil, Finset.sum_image fun f _ g _ h => loopFlavoring_injective Φ hS ⟨t₀, h₀⟩ h]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [loopWeight_loopFlavoring_of_hasLoop Φ hS ⟨t₀, h₀⟩,
    contractionAmplitude₂_loopFlavoring]

/-- **Without a loop**: `regulatedAmplitude₂ P Φ C = A(m_open, m_open)`. -/
theorem regulatedAmplitude₂_of_not_hasLoop [Fintype F] [DecidableEq F] (P : Params)
    {C : Contraction nf nA κ} (hS : IsSimple C) (hL : ¬ HasLoop C) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : QED.WickModel.Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude₂ P Φ C pIn kIn k αOut βIn μ =
      loopAmp P hS (Φ.mass Φ.openLine) (Φ.mass Φ.openLine) pIn kIn k αOut βIn μ := by
  classical
  unfold regulatedAmplitude₂
  have hfil : (Finset.univ : Finset (Flavoring Φ κ)).filter (Preserves Φ C) =
      {loopFlavoring Φ hS Φ.openLine} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun hφ => eq_loopFlavoring_of_not_hasLoop Φ hS hL hφ _, ?_⟩
    rintro rfl
    exact preserves_loopFlavoring Φ hS _
  rw [hfil, Finset.sum_singleton, loopWeight_loopFlavoring_of_not_hasLoop Φ hS hL,
    contractionAmplitude₂_loopFlavoring]
  simp

end QED.Lepton.Proof.HM

end
