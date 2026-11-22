/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.IBPCertFamily

/-!
# Seed-local and label-local hypotheses for IBP certificates (layer L2)

`QED.Algebra.IBPCert.Cert.sound` assumes the IBP relations for all index vectors
(`Family.IBPHolds`) and the vanishing of every integral in a zero sector (`Family.ZeroSectors`).
For dimensionally regularized integrals each label has its own poles in `d`, so these global
hypotheses can hold only off a countable set. This module states the hypotheses locally:

* `QED.Algebra.IBPCert.Family.IBPHoldsAt F I d i j ν`: the single relation `(i, j)` at `ν`.
* `QED.Algebra.IBPCert.ZCert`: a certificate with an explicit finite list `zeros` of the labels
  it treats as vanishing. The checker `QED.Algebra.IBPCert.ZCert.check` verifies that every
  surviving term with a nonzero coefficient has a label in `zeros`, and that every label in
  `zeros` lies in a declared scaleless sector.

## Main statements

* `QED.Algebra.IBPCert.ZCert.sound`: soundness with the relations only at the certificate's
  seeds and the vanishing only at the labels in `zeros`.
* `QED.Algebra.IBPCert.Family.IBPHolds.at`, `QED.Algebra.IBPCert.Family.ZeroSectors.at`: the
  global hypotheses imply the local ones.
-/

@[expose] public section

namespace QED.Algebra.IBPCert

namespace Family

variable (F : Family)

/-- The single IBP relation `(i, j)` at the index vector `ν` holds for `I` at `d`. -/
def IBPHoldsAt {K : Type*} [Ring K] (I : (Fin F.nProp → ℤ) → K → K) (d : K) (i j : ℕ)
    (ν : Fin F.nProp → ℤ) : Prop :=
  ((F.template i j).map fun t => t.coeff d ν * I (ν + toVec F.nProp t.shift) d).sum = 0

variable {F}

theorem IBPHolds.at {K : Type*} [Ring K] {I : (Fin F.nProp → ℤ) → K → K} {d : K}
    (h : F.IBPHolds I d) {i j : ℕ} (hi : i < F.nLoop) (hj : j < F.nMom) (ν : Fin F.nProp → ℤ) :
    F.IBPHoldsAt I d i j ν :=
  h i hi j hj ν

theorem ZeroSectors.at {K : Type*} [Ring K] {I : (Fin F.nProp → ℤ) → K → K} {d : K}
    (h : F.ZeroSectors I d) {l : List ℤ} (hl : F.zeroPred l = true) :
    I (toVec F.nProp l) d = 0 :=
  zeroPred_sound F I d h l hl

end Family

/-- The relation of an admissible seed vanishes if the relation holds at that seed. -/
theorem Seed.eval_rel_of_at {K : Type*} [Field K] (F : Family) (I : (Fin F.nProp → ℤ) → K → K)
    (d : K) (ht : F.tmplOk = true) {s : Seed} (hs : s.ok F = true)
    (hI : F.IBPHoldsAt I d s.i s.j (toVec F.nProp s.nu)) :
    LinComb.eval (fun l => I (toVec F.nProp l) d) d (s.rel F) = 0 := by
  simp only [Seed.ok, Bool.and_eq_true, Nat.blt_eq] at hs
  obtain ⟨⟨hi, hj⟩, hl⟩ := hs
  have hl : s.nu.length = F.nProp := Nat.eq_of_beq_eq_true hl
  rw [Seed.rel, F.tmplAt_eq_template ht hi hj, LinComb.eval_ofTerms, LinComb.eval_eq_sum,
    ← hI, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Poly.eval_cons, Poly.eval_nil, toVec_polyAdd, Term.coeff,
    vecGet_toVec hl]
  push_cast; ring

/-- Membership of a label in a list, decided by `labelCmp`. -/
def labelMem (l : List ℤ) (ls : List (List ℤ)) : Bool := ls.any fun m => labelCmp l m == .eq

theorem mem_of_labelMem {l : List ℤ} {ls : List (List ℤ)} (h : labelMem l ls = true) :
    l ∈ ls := by
  simp only [labelMem, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨m, hm, h⟩ := h
  rwa [eq_of_labelCmp_eq h]

/-- A certificate with an explicit list of labels treated as vanishing. -/
structure ZCert where
  /-- The underlying certificate. -/
  cert : Cert
  /-- The labels of the integrals the certificate treats as `0`. -/
  zeros : List (List ℤ)

/-- The checker: the `Cert` check with zero predicate `· ∈ zeros`, and every label of `zeros`
in a declared scaleless sector. -/
def ZCert.check (F : Family) (c : ZCert) : Bool :=
  F.tmplOk && c.cert.seeds.all (Seed.ok F) && c.zeros.all F.zeroPred &&
    checkCombo (labelMem · c.zeros) (c.cert.seeds.map fun s => (s.rel F, s.mult)) c.cert.target
      c.cert.den c.cert.masters

/-- **Soundness with local hypotheses.** If the check passes, the IBP relations hold at the
certificate's seeds, the integrals of `zeros` vanish, and the denominator does not vanish at
`d`, then the target is the claimed combination of the masters at `d`. -/
theorem ZCert.sound {K : Type*} [Field K] {F : Family} {c : ZCert} (h : c.check F = true)
    (I : (Fin F.nProp → ℤ) → K → K) (d : K)
    (hI : ∀ s ∈ c.cert.seeds, F.IBPHoldsAt I d s.i s.j (toVec F.nProp s.nu))
    (hz : ∀ l ∈ c.zeros, I (toVec F.nProp l) d = 0)
    (hden : Poly.eval d c.cert.den ≠ 0) :
    I (toVec F.nProp c.cert.target) d =
      (c.cert.masters.map fun m =>
        Poly.eval d m.2 / Poly.eval d c.cert.den * I (toVec F.nProp m.1) d).sum := by
  simp only [ZCert.check, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨ht, hs⟩, -⟩, hc⟩ := h
  refine checkCombo_sound (fun l => I (toVec F.nProp l) d) d hc ?_
    (fun l hl => hz l (mem_of_labelMem hl)) hden
  intro r hr
  obtain ⟨s, hs', rfl⟩ := List.mem_map.1 hr
  exact Seed.eval_rel_of_at F I d ht (hs s hs') (hI s hs')

/-- The global hypotheses give the local ones: `ZCert.sound` under `IBPHolds` and
`ZeroSectors`. -/
theorem ZCert.sound_of_global {K : Type*} [Field K] {F : Family} {c : ZCert}
    (h : c.check F = true) (I : (Fin F.nProp → ℤ) → K → K) (d : K) (hI : F.IBPHolds I d)
    (hz : F.ZeroSectors I d) (hden : Poly.eval d c.cert.den ≠ 0) :
    I (toVec F.nProp c.cert.target) d =
      (c.cert.masters.map fun m =>
        Poly.eval d m.2 / Poly.eval d c.cert.den * I (toVec F.nProp m.1) d).sum := by
  have h' := h
  simp only [ZCert.check, Bool.and_eq_true, List.all_eq_true] at h'
  obtain ⟨⟨⟨_, hs⟩, hzs⟩, _⟩ := h'
  refine ZCert.sound h I d (fun s hs' => ?_) (fun l hl => hz.at (hzs l hl)) hden
  have := hs s hs'
  simp only [Seed.ok, Bool.and_eq_true, Nat.blt_eq] at this
  exact hI.at this.1.1 this.1.2 _

end QED.Algebra.IBPCert
