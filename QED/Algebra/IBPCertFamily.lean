/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.IBPCertPoly
import Mathlib.Tactic.Ring

/-!
# Symbolic IBP relations of an integral family and reduction certificates (layer L2)

An integral family is given by `L` loop momenta `k₁, …, k_L`, `E` external momenta
`p₁, …, p_E` (together `q₀, …, q_{M-1}` with `M = L + E`, loop momenta first) and `N`
propagators

  `D_a = Σ_{u,v < M} A_a[u][v] (q_u · q_v) + c_a`,

with integer matrices `A_a` (not necessarily symmetric) and constants `c_a`, the external scalar
products being the integers `G[e][f] = p_e · p_f` (masses and invariants are fixed numbers, e.g.
`m = 1`). The family also records how each scalar product involving a loop momentum is written
in terms of the propagators,

  `δ (q_u · q_v) = Σ_b B_{uv}[b] D_b + β_{uv}`  for `u < L`, `v < M`,

with one integer `δ > 0`. `QED.Algebra.IBPCert.Family.wellFormed` checks these decompositions as
identities of polynomials in the scalar products (the external ones replaced by `G`).

## The IBP relation

For `i < L` and `j < M`, the integrand identity `∂/∂k_i · (q_j ∏_a D_a^{-ν_a}) = …` gives, after
multiplication by `δ`, the symbolic relation (`QED.Algebra.IBPCert.Family.template`)

  `δ d [i = j] I(ν) - Σ_{a, w} 2ν_a Â_a[i][w] (Σ_b B_{jw}[b] I(ν + e_a - e_b) + β_{jw} I(ν + e_a))
    = 0`,

with `2Â_a[i][w] = A_a[i][w] + A_a[w][i]` and the decomposition of `q_j · q_w` (by `G` when
both are external). Every coefficient is affine in `d` and in one `ν_a`; a relation is stored
as a list of terms (shift, coefficient), terms with coefficient `0` omitted. For speed the
family also carries the relations precomputed (`tmpl`); the checker compares them once with
`template` (`QED.Algebra.IBPCert.Family.tmplOk`). This module proves nothing analytic about it:
`QED.Algebra.IBPCert.Family.IBPHolds` and `QED.Algebra.IBPCert.Family.ZeroSectors` are the
statements that a family of values `I : (Fin N → ℤ) → K → K` satisfies all IBP relations and
vanishes on the declared scaleless sectors; for dimensionally regularized integrals they are
obligations of layer L1.

## Main definitions and statements

* `QED.Algebra.IBPCert.Cert`: a reduction certificate (target, common denominator, master
  numerators, seeds `(i, j, ν)` with polynomial multipliers).
* `QED.Algebra.IBPCert.Cert.check`: the computable checker, to be run by `decide +kernel`.
* `QED.Algebra.IBPCert.Cert.sound`: if the check passes and `I` satisfies the IBP relations and
  the zero sectors at `d`, then `I(T)(d) = Σ (nⱼ(d) / q(d)) · I(Mⱼ)(d)` whenever `q(d) ≠ 0`.
* `QED.Algebra.IBPCert.Cert.exists_finset_sound`: in characteristic `0` the exceptional set
  `{q = 0}` is finite.
-/

@[expose] public section

namespace QED.Algebra.IBPCert

/-! ### Index vectors -/

/-- The index vector of length `n` read from a list (missing entries are `0`). -/
def toVec (n : ℕ) (l : List ℤ) : Fin n → ℤ := fun i => l.getD i 0

/-- The entry `ν_i` of an index vector, `0` out of range. -/
def vecGet {n : ℕ} (ν : Fin n → ℤ) (i : ℕ) : ℤ := if h : i < n then ν ⟨i, h⟩ else 0

theorem getD_polyAdd : ∀ (l m : List ℤ) (i : ℕ),
    (Poly.add l m).getD i 0 = l.getD i 0 + m.getD i 0
  | [], m, i => by simp [Poly.add]
  | a :: l, [], i => by simp [Poly.add]
  | a :: l, b :: m, 0 => by simp only [Poly.add, List.getD_cons_zero, Poly.int_add_eq]
  | a :: l, b :: m, i + 1 => by
    simp only [Poly.add, List.getD_cons_succ]; exact getD_polyAdd l m i

theorem toVec_polyAdd (n : ℕ) (l m : List ℤ) :
    toVec n (Poly.add l m) = toVec n l + toVec n m := by
  funext i; simp only [toVec, getD_polyAdd, Pi.add_apply]

theorem vecGet_toVec {n : ℕ} {l : List ℤ} (hl : l.length = n) (i : ℕ) :
    vecGet (toVec n l) i = l.getD i 0 := by
  unfold vecGet toVec
  split_ifs with h
  · rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]

/-- `ν_a ≤ 0` read from a list implies it for the index vector. -/
theorem vecGet_toVec_nonpos {n : ℕ} {l : List ℤ} {a : ℕ} (h : l.getD a 0 ≤ 0) :
    vecGet (toVec n l) a ≤ 0 := by
  unfold vecGet toVec
  split_ifs
  · exact h
  · exact le_rfl

/-! ### Families and their IBP relations -/

/-- The entry `m[u][v]` of a matrix stored as a list of rows, `0` out of range. -/
def get2 (m : List (List ℤ)) (u v : ℕ) : ℤ := (m.getD u []).getD v 0

/-- A term of a symbolic IBP relation: the integral `I(ν + shift)` with coefficient
`c0 + cd · d + cnu · ν_idx`. -/
structure Term where
  /-- The shift of the index vector. -/
  shift : List ℤ
  /-- Constant part of the coefficient. -/
  c0 : ℤ
  /-- Coefficient of `d`. -/
  cd : ℤ
  /-- The index `a` whose `ν_a` enters the coefficient. -/
  idx : ℕ
  /-- Coefficient of `ν_idx`. -/
  cnu : ℤ

/-- An integral family (see the module docstring for the meaning of the fields). -/
structure Family where
  /-- Number `L` of loop momenta. -/
  nLoop : ℕ
  /-- Number `E` of external momenta. -/
  nExt : ℕ
  /-- Number `N` of propagators. -/
  nProp : ℕ
  /-- The matrices `A_a` of the propagators, `M × M`, momenta indexed loop-first. -/
  quad : List (List (List ℤ))
  /-- The constants `c_a` of the propagators. -/
  const : List ℤ
  /-- The external scalar products `G[e][f] = p_e · p_f`. -/
  gram : List (List ℤ)
  /-- The common denominator `δ` of the scalar-product decompositions. -/
  spDen : ℤ
  /-- `sp[u][v] = (B_{uv}, β_{uv})` with `δ q_u · q_v = Σ_b B_{uv}[b] D_b + β_{uv}`, for `u < L`
  and `v < M`. -/
  sp : List (List (List ℤ × ℤ))
  /-- The IBP relations `template i j`, precomputed (checked by `tmplOk`). -/
  tmpl : List (List (List Term))
  /-- Scaleless sectors: for each listed set `S` of propagators, `I(ν) = 0` whenever `ν_a ≤ 0`
  for all `a ∈ S`. -/
  zeroSectors : List (List ℕ)

/-- The value of the coefficient of a term at dimension `d` and index vector `ν`. -/
def Term.coeff {K : Type*} [Ring K] {n : ℕ} (t : Term) (d : K) (ν : Fin n → ℤ) : K :=
  (t.c0 : K) + (t.cd : K) * d + ((t.cnu * vecGet ν t.idx : ℤ) : K)

namespace Family

variable (F : Family)

/-- Number `M = L + E` of momenta. -/
def nMom : ℕ := F.nLoop + F.nExt

/-- The decomposition `(B, β)` of `δ q_j · q_w`; for two external momenta it is the constant
`δ G`. -/
def spOf (j w : ℕ) : List ℤ × ℤ :=
  bif Nat.blt j F.nLoop then (F.sp.getD j []).getD w ([], 0)
  else bif Nat.blt w F.nLoop then (F.sp.getD w []).getD j ([], 0)
  else ([], F.spDen * get2 F.gram (j - F.nLoop) (w - F.nLoop))

/-- The shift `e_a - e_b` as a list of length `n` (`e_a` alone when `b ≥ n`). -/
def shiftVec (n a b : ℕ) : List ℤ :=
  (List.range n).map fun c => (bif Nat.beq c a then 1 else 0) - (bif Nat.beq c b then 1 else 0)

/-- The term `c ν_a I(ν + shift)`, omitted when `c = 0`. -/
def nzTerm (shift : List ℤ) (a : ℕ) (c : ℤ) : List Term :=
  bif intIsZero c then [] else [⟨shift, 0, 0, a, c⟩]

/-- The symbolic IBP relation `δ ∂/∂k_i · (q_j ∏ D_a^{-ν_a}) = 0`, as a list of terms. -/
def template (i j : ℕ) : List Term :=
  (bif Nat.beq i j then [⟨[], 0, F.spDen, 0, 0⟩] else []) ++
  (List.range F.nProp).flatMap fun a =>
    (List.range F.nMom).flatMap fun w =>
      let g := get2 (F.quad.getD a []) i w + get2 (F.quad.getD a []) w i
      bif intIsZero g then [] else
        let s := F.spOf j w
        nzTerm (shiftVec F.nProp a F.nProp) a (-(g * s.2)) ++
          (List.range F.nProp).flatMap fun b =>
            nzTerm (shiftVec F.nProp a b) a (-(g * s.1.getD b 0))

/-- The IBP relations hold for `I` at the point `d`: for every `i < L`, `j < M` and `ν`,
`Σ_t coeff_t(d, ν) · I(ν + shift_t)(d) = 0` over the terms of `template i j`. -/
def IBPHolds {K : Type*} [Ring K] (I : (Fin F.nProp → ℤ) → K → K) (d : K) : Prop :=
  ∀ i < F.nLoop, ∀ j < F.nMom, ∀ ν : Fin F.nProp → ℤ,
    ((F.template i j).map fun t => t.coeff d ν * I (ν + toVec F.nProp t.shift) d).sum = 0

/-- `I` vanishes at `d` on the declared scaleless sectors. -/
def ZeroSectors {K : Type*} [Ring K] (I : (Fin F.nProp → ℤ) → K → K) (d : K) : Prop :=
  ∀ S ∈ F.zeroSectors, ∀ ν : Fin F.nProp → ℤ, (∀ a ∈ S, vecGet ν a ≤ 0) → I ν d = 0

/-- The checker's zero predicate on labels: some declared sector has `ν_a ≤ 0` throughout. -/
def zeroPred (l : List ℤ) : Bool :=
  F.zeroSectors.any fun S => S.all fun a => intNonpos (l.getD a 0)

/-- Coefficient of the monomial `q_u · q_v` (`u ≤ v`) in `D_b`. -/
def mono (b u v : ℕ) : ℤ :=
  bif Nat.beq u v then get2 (F.quad.getD b []) u u
  else get2 (F.quad.getD b []) u v + get2 (F.quad.getD b []) v u

/-- The constant of `D_b` after the external scalar products are replaced by `G`. -/
def reducedConst (b : ℕ) : ℤ :=
  F.const.getD b 0 + ((List.range F.nExt).flatMap fun e => (List.range F.nExt).map fun f =>
    get2 (F.quad.getD b []) (F.nLoop + e) (F.nLoop + f) * get2 F.gram e f).sum

/-- The decomposition of `δ q_u · q_v` is an identity of polynomials in the scalar products
involving a loop momentum, the external ones replaced by `G`. -/
def spCorrect (u v : ℕ) : Bool :=
  let s := (F.sp.getD u []).getD v ([], 0)
  let lo := min u v
  let hi := max u v
  ((List.range F.nMom).all fun u' => (List.range F.nMom).all fun v' =>
    !Nat.ble u' v' || !Nat.blt u' F.nLoop ||
      intIsZero (((List.range F.nProp).map fun b => s.1.getD b 0 * F.mono b u' v').sum -
        bif Nat.beq u' lo && Nat.beq v' hi then F.spDen else 0)) &&
  intIsZero (((List.range F.nProp).map fun b => s.1.getD b 0 * F.reducedConst b).sum + s.2)

/-- Well-formedness of a family: positive `δ`, and every stored scalar-product decomposition
is correct. -/
def wellFormed : Bool :=
  Nat.beq F.quad.length F.nProp && Nat.beq F.const.length F.nProp && decide (0 < F.spDen) &&
  (List.range F.nLoop).all fun u => (List.range F.nMom).all fun v => F.spCorrect u v

end Family

/-! ### Certificates -/

/-- Equality of terms, by `labelCmp`, `intCmp` and `Nat.beq`. -/
def Term.beq (t u : Term) : Bool :=
  (labelCmp t.shift u.shift == .eq) && (intCmp t.c0 u.c0 == .eq) && (intCmp t.cd u.cd == .eq) &&
    Nat.beq t.idx u.idx && (intCmp t.cnu u.cnu == .eq)

theorem Term.eq_of_beq {t u : Term} (h : t.beq u = true) : t = u := by
  obtain ⟨s, c0, cd, i, c⟩ := t
  obtain ⟨s', c0', cd', i', c'⟩ := u
  simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [eq_of_labelCmp_eq h1, eq_of_intCmp_eq h2, eq_of_intCmp_eq h3, Nat.eq_of_beq_eq_true h4,
    eq_of_intCmp_eq h5]

/-- Equality of term lists. -/
def termsEq : List Term → List Term → Bool
  | [], [] => true
  | t :: ts, u :: us => t.beq u && termsEq ts us
  | _, _ => false

theorem eq_of_termsEq : ∀ {ts us : List Term}, termsEq ts us = true → ts = us
  | [], [], _ => rfl
  | t :: ts, u :: us, h => by
    simp only [termsEq, Bool.and_eq_true] at h
    rw [Term.eq_of_beq h.1, eq_of_termsEq h.2]
  | [], _ :: _, h => by simp [termsEq] at h
  | _ :: _, [], h => by simp [termsEq] at h

namespace Family

variable (F : Family)

/-- The precomputed relation `(i, j)`. -/
def tmplAt (i j : ℕ) : List Term := (F.tmpl.getD i []).getD j []

/-- The precomputed relations are the generated ones. -/
def tmplOk : Bool :=
  (List.range F.nLoop).all fun i => (List.range F.nMom).all fun j =>
    termsEq (F.tmplAt i j) (F.template i j)

theorem tmplAt_eq_template {F : Family} (h : F.tmplOk = true) {i j : ℕ} (hi : i < F.nLoop)
    (hj : j < F.nMom) : F.tmplAt i j = F.template i j := by
  simp only [tmplOk, List.all_eq_true, List.mem_range] at h
  exact eq_of_termsEq (h i hi j hj)

end Family

/-- A seed of a certificate: the IBP relation `(i, j)` at the index vector `nu`, with a
polynomial multiplier. -/
structure Seed where
  /-- The loop momentum differentiated. -/
  i : ℕ
  /-- The momentum in the numerator. -/
  j : ℕ
  /-- The seed index vector. -/
  nu : List ℤ
  /-- The multiplier in `ℤ[d]`. -/
  mult : Poly

/-- The instantiated relation of a seed, as a sorted linear combination. -/
def Seed.rel (F : Family) (s : Seed) : LinComb :=
  LinComb.ofTerms ((F.tmplAt s.i s.j).map fun t =>
    (Poly.add s.nu t.shift, [t.c0 + t.cnu * s.nu.getD t.idx 0, t.cd]))

/-- A seed is admissible: `i < L`, `j < M` and `ν` has length `N`. -/
def Seed.ok (F : Family) (s : Seed) : Bool :=
  Nat.blt s.i F.nLoop && Nat.blt s.j F.nMom && Nat.beq s.nu.length F.nProp

/-- A reduction certificate: `q · I(T) = Σ nⱼ I(Mⱼ) + Σ cₖ Rₖ`. -/
structure Cert where
  /-- The target integral. -/
  target : List ℤ
  /-- The common denominator `q ∈ ℤ[d]`. -/
  den : Poly
  /-- The masters with their numerators `nⱼ ∈ ℤ[d]`. -/
  masters : List (List ℤ × Poly)
  /-- The seeds with their multipliers. -/
  seeds : List Seed

/-- The certificate checker. -/
def Cert.check (F : Family) (c : Cert) : Bool :=
  F.tmplOk && c.seeds.all (Seed.ok F) &&
    checkCombo F.zeroPred (c.seeds.map fun s => (s.rel F, s.mult)) c.target c.den c.masters

theorem LinComb.eval_eq_sum {K : Type*} [CommRing K] (J : List ℤ → K) (d : K) :
    ∀ ts : LinComb, LinComb.eval J d ts = (ts.map fun t => Poly.eval d t.2 * J t.1).sum
  | [] => rfl
  | t :: ts => by simp [LinComb.eval_eq_sum J d ts]

theorem Seed.eval_rel {K : Type*} [Field K] (F : Family) (I : (Fin F.nProp → ℤ) → K → K)
    (d : K) (hI : F.IBPHolds I d) (ht : F.tmplOk = true) {s : Seed} (hs : s.ok F = true) :
    LinComb.eval (fun l => I (toVec F.nProp l) d) d (s.rel F) = 0 := by
  simp only [Seed.ok, Bool.and_eq_true, Nat.blt_eq] at hs
  obtain ⟨⟨hi, hj⟩, hl⟩ := hs
  have hl : s.nu.length = F.nProp := Nat.eq_of_beq_eq_true hl
  rw [Seed.rel, F.tmplAt_eq_template ht hi hj, LinComb.eval_ofTerms, LinComb.eval_eq_sum,
    ← hI s.i hi s.j hj (toVec _ s.nu), List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Poly.eval_cons, Poly.eval_nil, toVec_polyAdd, Term.coeff,
    vecGet_toVec hl]
  push_cast; ring

theorem zeroPred_sound {K : Type*} [Ring K] (F : Family) (I : (Fin F.nProp → ℤ) → K → K)
    (d : K) (hz : F.ZeroSectors I d) (l : List ℤ) (h : F.zeroPred l = true) :
    I (toVec F.nProp l) d = 0 := by
  simp only [Family.zeroPred, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨S, hS, hall⟩ := h
  exact hz S hS _ fun a ha => vecGet_toVec_nonpos (nonpos_of_intNonpos (hall a ha))

/-- Soundness of the certificate checker. If `c.check F` holds, `I` satisfies the IBP relations
of `F` and vanishes on its zero sectors at `d`, and the denominator does not vanish at `d`,
then the target is the claimed combination of the masters at `d`. -/
theorem Cert.sound {K : Type*} [Field K] {F : Family} {c : Cert} (h : c.check F = true)
    (I : (Fin F.nProp → ℤ) → K → K) (d : K) (hI : F.IBPHolds I d) (hz : F.ZeroSectors I d)
    (hden : Poly.eval d c.den ≠ 0) :
    I (toVec F.nProp c.target) d =
      (c.masters.map fun m =>
        Poly.eval d m.2 / Poly.eval d c.den * I (toVec F.nProp m.1) d).sum := by
  simp only [Cert.check, Bool.and_eq_true, List.all_eq_true] at h
  refine checkCombo_sound (fun l => I (toVec F.nProp l) d) d h.2 ?_
    (zeroPred_sound F I d hz) hden
  intro r hr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
  exact Seed.eval_rel F I d hI h.1.1 (h.1.2 s hs)

/-- The certificate's denominator is a nonzero polynomial, so in characteristic `0` the
reduction holds for all `d` outside a finite set, for every `I` satisfying the IBP relations
and the zero sectors there. -/
theorem Cert.exists_finset_sound {K : Type*} [Field K] [CharZero K] {F : Family} {c : Cert}
    (h : c.check F = true) :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d c.den ≠ 0 ∧
      ∀ I : (Fin F.nProp → ℤ) → K → K, F.IBPHolds I d → F.ZeroSectors I d →
        I (toVec F.nProp c.target) d =
          (c.masters.map fun m =>
            Poly.eval d m.2 / Poly.eval d c.den * I (toVec F.nProp m.1) d).sum := by
  have hq : Poly.isZero c.den = false := by
    simp only [Cert.check, Bool.and_eq_true] at h
    exact isZero_den_of_checkCombo h.2
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) hq
  exact ⟨s, fun d hd => ⟨hs d hd, fun I hI hz => Cert.sound h I d hI hz (hs d hd)⟩⟩

end QED.Algebra.IBPCert
