/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.IBPCertSector
public import QED.Algebra.IBPCertKron
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Label-split IBP certificates: soundness (layer L2)

The checks of `QED.Algebra.IBPCertSector` are composed into a reduction.

* Each part `p` cancels label by label at `x₀`. Its entries are the values at `x₀` of explicit
  polynomials (`QED.Algebra.IBPCert.Sector.partPolys`), whose norms are bounded by the global
  bound, so the part vanishes as a combination over `ℤ[d]`
  (`QED.Algebra.IBPCert.kron_sum_eq_zero`).
* Summed over the parts, the target and masters slices give `-q T + Σ nⱼ Mⱼ`, and the groups of
  each seed give the groups assigned to some part. The others vanish (zero coefficient or a label
  in a scaleless sector), so they give the whole merged relation of the seed, which is its IBP
  relation (`QED.Algebra.IBPCert.Sector.mtOk`) and vanishes.

## Main statements

* `QED.Algebra.IBPCert.Sector.gcert_reduction`: if all checks pass, then for every family of
  values `I` satisfying the IBP relations and the zero sectors of `F` at `d` with `q(d) ≠ 0`,
  `Σ tₗ(d) I(l) = Σ (nⱼ(d) / q(d)) I(Mⱼ)`.
-/

@[expose] public section

namespace QED.Algebra.IBPCert.Sector

open QED.Algebra.IBPCert Finset

/-! ### The recursor-based functions -/

section Rec

variable {α β : Type*}

theorem rApp_eq : ∀ l m : List α, rApp l m = l ++ m
  | [], _ => rfl
  | a :: l, m => by
    change a :: rApp l m = a :: l ++ m
    rw [rApp_eq l m]; rfl

theorem rCat_eq (f : α → List β) : ∀ l : List α, rCat f l = l.flatMap f
  | [] => rfl
  | a :: l => by
    change rApp (f a) (rCat f l) = (a :: l).flatMap f
    rw [rApp_eq, rCat_eq f l, List.flatMap_cons]

theorem rGetL_eq : ∀ (l : List (List α)) (n : ℕ), rGetL l n = l.getD n []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: l, n + 1 => by
    change rGetL l n = (a :: l).getD (n + 1) []
    rw [rGetL_eq l n, List.getD_cons_succ]

theorem rDrop_eq : ∀ (n : ℕ) (l : List α), rDrop n l = l.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: l => by change rDrop n l = _; rw [rDrop_eq n l]; rfl

theorem rTake_eq : ∀ (n : ℕ) (l : List α), rTake n l = l.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: l => by change a :: rTake n l = _; rw [rTake_eq n l]; rfl

theorem chunks_flatten : ∀ (ls : List ℕ) (T : List α), (chunks ls T).flatten = T
  | [], T => by simp [chunks]
  | n :: ls, T => by
    change (rTake n T :: chunks ls (rDrop n T)).flatten = T
    rw [List.flatten_cons, chunks_flatten ls, rTake_eq, rDrop_eq, List.take_append_drop]

theorem chunks_length : ∀ (ls : List ℕ) (T : List α), (chunks ls T).length = ls.length + 1
  | [], T => rfl
  | n :: ls, T => by
    change (rTake n T :: chunks ls (rDrop n T)).length = _
    rw [List.length_cons, chunks_length ls]; rfl

theorem isNil_eq (l : List α) : isNil l = true ↔ l = [] := by
  cases l <;> simp [isNil]

end Rec

theorem eq_zero_of_izero {a : ℤ} (h : izero a = true) : a = 0 := by
  cases a with
  | ofNat n => simp only [izero] at h; rw [Nat.eq_of_beq_eq_true h]; rfl
  | negSucc n => simp [izero] at h

theorem hornerZ_eq (x : ℤ) : ∀ p : List ℤ, hornerZ x p = evalZ x p
  | [] => rfl
  | a :: p => by
    change Int.add a (Int.mul x (hornerZ x p)) = _
    rw [hornerZ_eq x p]; rfl

theorem norm1_eq : ∀ p : List ℤ, norm1 p = Poly.norm1 p
  | [] => rfl
  | a :: p => by change a.natAbs + norm1 p = _; rw [norm1_eq p]; rfl

theorem packC_eq (B o : ℕ) : ∀ l : List ℤ, packC B o l = pack B o l
  | [] => rfl
  | x :: l => by change Int.toNat (x + o) + B * packC B o l = _; rw [packC_eq B o l]; rfl

/-! ### Merging -/

namespace Ent

variable {R : Type*} [CommRing R] (W : ℕ → R)

/-- `Σ v W(l)`. -/
def eval (l : Ent) : R := (l.map fun t => (t.2 : R) * W t.1).sum

@[simp] theorem eval_nil : eval W [] = 0 := rfl

@[simp] theorem eval_cons (t : ℕ × ℤ) (l : Ent) :
    eval W (t :: l) = (t.2 : R) * W t.1 + eval W l := by simp [eval]

theorem eval_addC (t : ℕ × ℤ) (ts : Ent) (rec : Ent → Ent)
    (hrec : ∀ m, eval W (rec m) = eval W ts + eval W m) :
    ∀ m, eval W (addC t rec ts m) = eval W (t :: ts) + eval W m
  | [] => by simp [addC]
  | u :: us => by
    change eval W (bif Nat.blt t.1 u.1 then t :: rec (u :: us)
      else bif Nat.blt u.1 t.1 then u :: addC t rec ts us
      else bif izero (Int.add t.2 u.2) then rec us else (t.1, Int.add t.2 u.2) :: rec us) = _
    cases h1 : Nat.blt t.1 u.1
    · cases h2 : Nat.blt u.1 t.1
      · have hl : t.1 = u.1 := by
          have a : ¬ t.1 < u.1 := fun h => by
            rw [show Nat.blt t.1 u.1 = true from Nat.blt_eq ▸ h] at h1
            exact Bool.noConfusion h1
          have b : ¬ u.1 < t.1 := fun h => by
            rw [show Nat.blt u.1 t.1 = true from Nat.blt_eq ▸ h] at h2
            exact Bool.noConfusion h2
          omega
        cases hz : izero (Int.add t.2 u.2)
        · simp only [Bool.cond_false, eval_cons, hrec, Poly.int_add_eq, Int.cast_add, hl]; ring
        · have h0 := eq_zero_of_izero hz
          rw [Poly.int_add_eq] at h0
          have h0' : ((t.2 : ℤ) : R) + ((u.2 : ℤ) : R) = 0 := by
            rw [← Int.cast_add, h0, Int.cast_zero]
          simp only [Bool.cond_true, Bool.cond_false, hrec, eval_cons, hl]
          linear_combination (-W u.1) * h0'
      · simp only [Bool.cond_false, Bool.cond_true, eval_cons, eval_addC t ts rec hrec us]; ring
    · simp only [Bool.cond_true, eval_cons, hrec]; ring

theorem eval_addE : ∀ l m : Ent, eval W (addE l m) = eval W l + eval W m
  | [], m => by simp [addE]
  | t :: ts, m => eval_addC W t ts (addE ts) (eval_addE ts) m

theorem eval_pairsF : ∀ (ls : List Ent) (p : Option Ent),
    ((pairsF ls p).map (eval W)).sum = (ls.map (eval W)).sum + (p.map (eval W)).getD 0
  | [], none => by simp [pairsF]
  | [], some b => by simp [pairsF]
  | a :: ls, none => by
    change ((pairsF ls (some a)).map (eval W)).sum = _
    rw [eval_pairsF ls (some a)]; simp; ring
  | a :: ls, some b => by
    change ((addE b a :: pairsF ls none).map (eval W)).sum = _
    rw [List.map_cons, List.sum_cons, eval_pairsF ls none, eval_addE]; simp; ring

theorem eval_fold : ∀ ls : List Ent,
    eval W (List.rec [] (fun a _ ih => addE a ih) ls) = (ls.map (eval W)).sum
  | [] => rfl
  | a :: ls => by
    change eval W (addE a (List.rec [] (fun a _ ih => addE a ih) ls)) = _
    rw [eval_addE, eval_fold ls]; simp

theorem eval_tree : ∀ (k : ℕ) (ls : List Ent), eval W (tree k ls) = (ls.map (eval W)).sum
  | 0, ls => eval_fold W ls
  | _ + 1, [] => rfl
  | _ + 1, [a] => by simp [tree]
  | k + 1, a :: b :: rest => by
    change eval W (tree k (pairsF (a :: b :: rest) none)) = _
    rw [eval_tree k, eval_pairsF]; simp

end Ent

/-! ### Packed labels -/

/-- The first `n` base-`B` digits of `c`, minus `o`: the index vector packed as `c`. -/
def digL (B o : ℕ) : ℕ → ℕ → List ℤ
  | 0, _ => []
  | n + 1, c => (((c % B : ℕ) : ℤ) - o) :: digL B o n (c / B)

theorem digL_length (B o : ℕ) : ∀ n c, (digL B o n c).length = n
  | 0, _ => rfl
  | n + 1, c => by simp [digL, digL_length B o n]

theorem innerC_succ (B n c : ℕ) : innerC B (n + 1) c =
    (Nat.blt 0 (c % B) && Nat.blt (c % B + 1) B && innerC B n (c / B)) := rfl

theorem innerC_spec {B o : ℕ} : ∀ {n c : ℕ}, innerC B n c = true →
    pack B o (digL B o n c) = c ∧ ∀ x ∈ digL B o n c, 1 ≤ x + o ∧ x + o + 2 ≤ B
  | 0, c, h => by
    change Nat.beq c 0 = true at h
    simp [digL, pack, Nat.eq_of_beq_eq_true h]
  | n + 1, c, h => by
    rw [innerC_succ] at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := innerC_spec (o := o) h3
    refine ⟨?_, fun x hx => ?_⟩
    · simp only [digL, pack, Poly.int_add_eq, Int.ofNat_eq_natCast, sub_add_cancel,
        Int.toNat_natCast, ih1]
      exact Nat.mod_add_div c B
    · simp only [digL, List.mem_cons] at hx
      rcases hx with rfl | hx
      · constructor <;> omega
      · exact ih2 x hx

theorem digL_getD (B o : ℕ) : ∀ (n c a : ℕ), a < n →
    (digL B o n c).getD a 0 = ((c / B ^ a % B : ℕ) : ℤ) - o
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, c, 0, _ => by simp [digL]
  | n + 1, c, a + 1, h => by
    simp only [digL, List.getD_cons_succ]
    rw [digL_getD B o n (c / B) a (by omega), Nat.div_div_eq_div_mul, pow_succ, mul_comm]

theorem packC_one_cons (B : ℕ) (x : ℤ) (l : List ℤ) :
    packC B 1 (x :: l) = Int.toNat (x + 1) + B * packC B 1 l := rfl

/-- **Packing a shifted label.** -/
theorem pack_shift {B o : ℕ} : ∀ {ν s : List ℤ}, ν.length = s.length →
    (∀ x ∈ ν, 1 ≤ x + o ∧ x + o + 2 ≤ B) → (∀ y ∈ s, y.natAbs ≤ 1) →
    pack B o (Poly.add ν s) + packC B 1 (List.replicate s.length 0) =
      pack B o ν + packC B 1 s ∧ inRange B o ν.length (Poly.add ν s) = true
  | [], [], _, _, _ => by simp [Poly.add, pack, packC, inRange]
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | x :: ν, y :: s, hl, hν, hs => by
    obtain ⟨ih1, ih2⟩ := pack_shift (ν := ν) (s := s) (by simpa using hl)
      (fun z hz => hν z (by simp [hz])) (fun z hz => hs z (by simp [hz]))
    have hx := hν x (by simp)
    have hy := hs y (by simp)
    simp only [inRange, Bool.and_eq_true, List.all_eq_true] at ih2
    have hlen : (Poly.add ν s).length = ν.length := Nat.eq_of_beq_eq_true ih2.1
    have hd : inDigit B o (x + y) = true := by
      simp only [inDigit, Poly.int_add_eq]
      have : 0 ≤ x + y + o := by omega
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le this
      rw [show x + y + Int.ofNat o = Int.ofNat k by simpa using hk]
      simp only [Nat.blt_eq]
      omega
    refine ⟨?_, ?_⟩
    · simp only [Poly.add, pack, List.length_cons, List.replicate_succ, packC_one_cons,
        Poly.int_add_eq, Int.ofNat_eq_natCast]
      have e1 : (x + y + o).toNat + 1 = (x + o).toNat + (y + 1).toNat := by omega
      have e2 : ((0 : ℤ) + 1).toNat = 1 := rfl
      have e3 : B * pack B o (Poly.add ν s) + B * packC B 1 (List.replicate s.length 0) =
          B * pack B o ν + B * packC B 1 s := by rw [← mul_add, ← mul_add, ih1]
      rw [e2]
      omega
    · simp only [inRange, Poly.add, List.length_cons, hlen, List.all_cons, Poly.int_add_eq, hd,
        Bool.true_and, Bool.and_eq_true, List.all_eq_true]
      exact ⟨Nat.beq_refl _, ih2.2⟩

theorem zeroLab_spec {B o : ℕ} {zs : List (List (ℕ × ℕ))} {l : ℕ} (h : zeroLab B o zs l = true) :
    ∃ S ∈ zs, ∀ t ∈ S, l / t.2 % B ≤ o := by
  induction zs with
  | nil => exact absurd h (by simp [zeroLab])
  | cons S zs ih =>
    change (List.rec true (fun t _ ih' => Nat.ble (Nat.mod (Nat.div l t.2) B) o && ih') S ||
      zeroLab B o zs l) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · refine ⟨S, by simp, fun t ht => ?_⟩
      induction S with
      | nil => simp at ht
      | cons u S ihS =>
        change (Nat.ble (Nat.mod (Nat.div l u.2) B) o && _) = true at h
        rw [Bool.and_eq_true, Nat.ble_eq] at h
        rcases List.mem_cons.1 ht with rfl | ht
        · exact h.1
        · exact ihS h.2 ht
    · obtain ⟨S', hS', h'⟩ := ih h
      exact ⟨S', by simp [hS'], h'⟩

/-! ### Factored multipliers -/

/-- `Π fₐ ^ eₐ` over the base-`8` digits `eₐ` of `e` (`QED.Algebra.IBPCert.Sector.powDig` without
the early stop). -/
def pd : List ℕ → ℕ → ℕ
  | [], _ => 1
  | f :: fs, e => f ^ (e % 8) * pd fs (e / 8)

theorem pd_zero : ∀ fv : List ℕ, pd fv 0 = 1
  | [] => rfl
  | f :: fs => by simp [pd, pd_zero fs]

theorem powDig_eq : ∀ (fv : List ℕ) (e : ℕ), powDig fv e = pd fv e
  | [], _ => rfl
  | f :: fs, e => by
    change (bif Nat.beq e 0 then 1 else Nat.mul (Nat.pow f (Nat.mod e 8)) (powDig fs (Nat.div e 8)))
      = _
    cases h : Nat.beq e 0
    · simp only [Bool.cond_false, powDig_eq fs]; rfl
    · rw [Nat.eq_of_beq_eq_true h, pd_zero]; rfl

theorem digLe_succ (n q e : ℕ) :
    digLe (n + 1) q e = (Nat.ble (e % 8) (q % 8) && digLe n (q / 8) (e / 8)) := rfl

theorem le_of_digLe : ∀ {n q e : ℕ}, digLe n q e = true → e ≤ q
  | 0, q, e, h => by
    change Nat.beq e 0 = true at h
    rw [Nat.eq_of_beq_eq_true h]; exact Nat.zero_le _
  | n + 1, q, e, h => by
    rw [digLe_succ, Bool.and_eq_true, Nat.ble_eq] at h
    have := le_of_digLe h.2
    have h1 := Nat.mod_add_div e 8
    have h2 := Nat.mod_add_div q 8
    omega

theorem pd_sub : ∀ (fv : List ℕ) {n q e : ℕ}, digLe n q e = true →
    pd fv q = pd fv (q - e) * pd fv e
  | [], _, _, _, _ => rfl
  | f :: fs, 0, q, e, h => by
    change Nat.beq e 0 = true at h
    rw [Nat.eq_of_beq_eq_true h, pd_zero, Nat.sub_zero, mul_one]
  | f :: fs, n + 1, q, e, h => by
    rw [digLe_succ, Bool.and_eq_true, Nat.ble_eq] at h
    have hle := le_of_digLe h.2
    have h1 := Nat.mod_add_div e 8
    have h2 := Nat.mod_add_div q 8
    have e1 : (q - e) % 8 = q % 8 - e % 8 := by omega
    have e2 : (q - e) / 8 = q / 8 - e / 8 := by omega
    simp only [pd, e1, e2]
    rw [pd_sub fs h.2]
    have : f ^ (q % 8) = f ^ (q % 8 - e % 8) * f ^ (e % 8) := by
      rw [← pow_add, Nat.sub_add_cancel h.1]
    rw [this]; ring

theorem pd_pos : ∀ {fv : List ℕ}, (∀ f ∈ fv, 0 < f) → ∀ e, 0 < pd fv e
  | [], _, _ => Nat.one_pos
  | f :: fs, h, e => Nat.mul_pos (Nat.pow_pos (h f (by simp)))
      (pd_pos (fun g hg => h g (by simp [hg])) _)

/-- `p ^ m`. -/
def ppow (p : Poly) : ℕ → Poly
  | 0 => [1]
  | m + 1 => Poly.mul p (ppow p m)

/-- `Π fₐ ^ eₐ` over the base-`8` digits of `e`, as a polynomial. -/
def prodPoly : List Poly → ℕ → Poly
  | [], _ => [1]
  | f :: fs, e => Poly.mul (ppow f (e % 8)) (prodPoly fs (e / 8))

theorem eval_ppow {K : Type*} [CommRing K] (x : K) (p : Poly) :
    ∀ m, Poly.eval x (ppow p m) = Poly.eval x p ^ m
  | 0 => by simp [ppow]
  | m + 1 => by rw [ppow, Poly.eval_mul, eval_ppow x p m, pow_succ, mul_comm]

theorem norm1_ppow (p : Poly) : ∀ m, Poly.norm1 (ppow p m) ≤ Poly.norm1 p ^ m
  | 0 => by simp [ppow]
  | m + 1 => by
    rw [ppow, pow_succ, mul_comm]
    exact (Poly.norm1_mul _ _).trans (Nat.mul_le_mul_left _ (norm1_ppow p m))

theorem evalZ_prodPoly {x : ℤ} : ∀ {fs : List Poly}, (∀ f ∈ fs, 0 < evalZ x f) → ∀ e : ℕ,
    evalZ x (prodPoly fs e) = (pd (fs.map fun f => (evalZ x f).toNat) e : ℤ)
  | [], _, _ => by simp [prodPoly, pd, evalZ]
  | f :: fs, h, e => by
    have hf := h f (by simp)
    have ih := evalZ_prodPoly (fs := fs) (fun g hg => h g (by simp [hg])) (e / 8)
    simp only [Poly.evalZ_eq_eval] at ih hf ⊢
    simp only [prodPoly, pd, List.map_cons, Poly.eval_mul, eval_ppow, ih]
    push_cast
    rw [Int.toNat_of_nonneg hf.le]

theorem norm1_prodPoly : ∀ (fs : List Poly) (e : ℕ),
    Poly.norm1 (prodPoly fs e) ≤ pd (fs.map Poly.norm1) e
  | [], _ => by simp [prodPoly, pd]
  | f :: fs, e => by
    simp only [prodPoly, pd, List.map_cons]
    exact (Poly.norm1_mul _ _).trans (Nat.mul_le_mul (norm1_ppow f _) (norm1_prodPoly fs _))

/-- The polynomial factor `num` of a seed. -/
noncomputable def GSeed.num (s : GSeed) : Poly := digitsPoly s.w s.len (joinL s.n)

/-- The multiplier `sc · num · Π fₐ^{qₐ - eₐ}` of a seed. -/
noncomputable def GSeed.mult (fac : List Poly) (qe : ℕ) (s : GSeed) : Poly :=
  Poly.smul s.sc (Poly.mul s.num (prodPoly fac (qe - s.e)))

/-- The factors `fac` of `q`: their values at `x₀` are positive and listed in `fv`, `qv` is
`q(x₀)` for the exponents `qe`, and `nf` lists their norms. -/
noncomputable def facOk (C : Ctx) (fac : List Poly) (qe : ℕ) (nf : List ℕ) : Bool :=
  decide (C.fv = fac.map fun f => (evalZ C.x0 f).toNat) &&
    fac.all (fun f => decide (0 < evalZ C.x0 f)) && decide (C.qv = powDig C.fv qe) &&
    decide (nf = fac.map Poly.norm1)

theorem yv_eq {C : Ctx} {fac : List Poly} {qe : ℕ} {nf : List ℕ} (hf : facOk C fac qe nf = true)
    {n : ℕ} (s : GSeed) (hs : digLe n qe s.e = true) :
    s.yv C = evalZ C.x0 (s.mult fac qe) := by
  simp only [facOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hf
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := hf
  have hpos : ∀ f ∈ C.fv, 0 < f := by
    rw [h1]; intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    have := h2 g hg; omega
  have hq : C.qv / powDig C.fv s.e = pd C.fv (qe - s.e) := by
    rw [h3, powDig_eq, powDig_eq, pd_sub C.fv hs]
    exact Nat.mul_div_cancel _ (pd_pos hpos _)
  change Int.mul s.sc (Int.mul (hornerZ (Int.ofNat C.x0) s.num)
    (Int.ofNat (Nat.div C.qv (powDig C.fv s.e)))) = _
  rw [show Nat.div C.qv (powDig C.fv s.e) = C.qv / powDig C.fv s.e from rfl, hq, hornerZ_eq]
  simp only [GSeed.mult, Poly.evalZ_eq_eval, Poly.eval_smul, Poly.eval_mul, Poly.int_mul_eq,
    Int.cast_id]
  rw [← Poly.evalZ_eq_eval (C.x0 : ℤ) (prodPoly fac _), evalZ_prodPoly (fun f hf => h2 f hf), h1]
  rfl

theorem norm1_mult (fac : List Poly) (qe : ℕ) (s : GSeed) :
    Poly.norm1 (s.mult fac qe) ≤ s.sc.natAbs * (Poly.norm1 s.num * pd (fac.map Poly.norm1)
      (qe - s.e)) := by
  simp only [GSeed.mult, Poly.norm1_smul]
  exact Nat.mul_le_mul_left _ ((Poly.norm1_mul _ _).trans
    (Nat.mul_le_mul_left _ (norm1_prodPoly _ _)))

/-! ### Sums by parts -/

theorem sum_parts {α M : Type*} [AddCommMonoid M] (key : α → ℕ) (P : ℕ) (f : α → M) :
    ∀ T : List α, (∀ t ∈ T, key t < P) →
      (T.map f).sum = ∑ p ∈ range P, ((T.filter fun t => decide (key t = p)).map f).sum
  | [], _ => by simp
  | t :: T, h => by
    have e : ∀ p, (((t :: T).filter fun t => decide (key t = p)).map f).sum =
        (if key t = p then f t else 0) + ((T.filter fun t => decide (key t = p)).map f).sum := by
      intro p
      by_cases hp : key t = p <;> simp [hp]
    rw [Finset.sum_congr rfl fun p _ => e p, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_range.2 (h t (by simp)), ↓reduceIte, List.map_cons, List.sum_cons]
    rw [sum_parts key P f T (fun u hu => h u (by simp [hu]))]

theorem sum_range_getD {α M : Type*} [AddCommMonoid M] (F : α → M) (x : α) :
    ∀ L : List α, ∑ k ∈ range L.length, F (L.getD k x) = (L.map F).sum
  | [] => by simp
  | a :: L => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [sum_range_getD F x L]

theorem sum_range_getD_le {α M : Type*} [AddCommMonoid M] (F : α → M) (x : α) (hx : F x = 0)
    (L : List α) {P : ℕ} (hP : L.length ≤ P) :
    ∑ k ∈ range P, F (L.getD k x) = (L.map F).sum := by
  rw [← sum_range_getD F x L, ← Finset.sum_range_add_sum_Ico _ hP]
  have : ∑ k ∈ Finset.Ico L.length P, F (L.getD k x) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [List.getD_eq_default _ _ (Finset.mem_Ico.1 hk).1, hx]
  rw [this, add_zero]

/-! ### Merged templates -/

/-- The coefficient `c0 + cd d + Σ c νₐ` of a group at dimension `d` and index vector `ν`. -/
def MTerm.coeff {K : Type*} [Ring K] {n : ℕ} (g : MTerm) (d : K) (ν : Fin n → ℤ) : K :=
  (g.c0 : K) + (g.cd : K) * d + (((g.nu.map fun t => t.2.2 * vecGet ν t.1).sum : ℤ) : K)

/-- The shifts `s` and `s'` agree in their first `n` entries. -/
def shEq (n : ℕ) (s s' : List ℤ) : Bool :=
  (List.range n).all fun a => decide (s.getD a 0 = s'.getD a 0)

theorem toVec_eq_of_shEq {n : ℕ} {s s' : List ℤ} (h : shEq n s s' = true) :
    toVec n s = toVec n s' := by
  funext a
  simp only [shEq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h a a.2

/-- The default group. -/
def mdflt : MTerm := ⟨[], 0, 0, 0, []⟩

/-- The index of the first group whose shift agrees with `s`. -/
def findG (n : ℕ) (s : List ℤ) : List MTerm → ℕ
  | [] => 0
  | g :: gs => if shEq n s g.sh then 0 else findG n s gs + 1

theorem findG_spec {n : ℕ} {s : List ℤ} : ∀ {gs : List MTerm}, findG n s gs < gs.length →
    shEq n s (gs.getD (findG n s gs) mdflt).sh = true
  | [], h => absurd h (by simp)
  | g :: gs, h => by
    by_cases hg : shEq n s g.sh = true
    · simp only [findG, hg, ↓reduceIte, List.getD_cons_zero]
    · simp only [findG, hg, Bool.false_eq_true, ↓reduceIte, List.getD_cons_succ] at h ⊢
      exact findG_spec (by simpa using h)

/-- The terms of `ts` sent to group `k`. -/
def fiber (n : ℕ) (gs : List MTerm) (ts : List Term) (k : ℕ) : List Term :=
  ts.filter fun t => decide (findG n t.shift gs = k)

/-- Group `k` has the summed coefficient of its fiber. -/
def groupOk (n : ℕ) (ts : List Term) (gs : List MTerm) (k : ℕ) (g : MTerm) : Bool :=
  decide (((fiber n gs ts k).map Term.c0).sum = g.c0) &&
    decide (((fiber n gs ts k).map Term.cd).sum = g.cd) &&
    (List.range n).all fun a =>
      decide ((((fiber n gs ts k).filter fun t => decide (t.idx = a)).map Term.cnu).sum =
        ((g.nu.filter fun t => decide (t.1 = a)).map fun t => t.2.2).sum)

/-- The groups `gs` are the template `ts` merged by shift. -/
def mergedOk (n : ℕ) (ts : List Term) (gs : List MTerm) : Bool :=
  ts.all (fun t => decide (findG n t.shift gs < gs.length) && decide (t.idx < n)) &&
    (List.range gs.length).all (fun k => groupOk n ts gs k (gs.getD k mdflt)) &&
    gs.all fun g => g.nu.all fun t => decide (t.1 < n)

theorem sum_cnu {K : Type*} [CommRing K] {n : ℕ} (ν : Fin n → ℤ) (L : List Term)
    (h : ∀ t ∈ L, t.idx < n) :
    (((L.map fun t => t.cnu * vecGet ν t.idx).sum : ℤ) : K) =
      ∑ a ∈ range n, ((((L.filter fun t => decide (t.idx = a)).map Term.cnu).sum : ℤ) : K) *
        (vecGet ν a : K) := by
  rw [sum_parts (fun t => t.idx) n _ L h, Int.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Int.cast_mul, ← List.sum_map_mul_right]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  rw [of_decide_eq_true (List.mem_filter.1 ht).2]

theorem sum_nu {K : Type*} [CommRing K] {n : ℕ} (ν : Fin n → ℤ) (L : List (ℕ × ℕ × ℤ))
    (h : ∀ t ∈ L, t.1 < n) :
    (((L.map fun t => t.2.2 * vecGet ν t.1).sum : ℤ) : K) =
      ∑ a ∈ range n, ((((L.filter fun t => decide (t.1 = a)).map fun t => t.2.2).sum : ℤ) : K) *
        (vecGet ν a : K) := by
  rw [sum_parts (fun t => t.1) n _ L h, Int.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Int.cast_mul, ← List.sum_map_mul_right]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  rw [of_decide_eq_true (List.mem_filter.1 ht).2]

theorem sum_coeff {K : Type*} [CommRing K] {n : ℕ} (d : K) (ν : Fin n → ℤ) (L : List Term) :
    (L.map fun t => t.coeff d ν).sum = (((L.map Term.c0).sum : ℤ) : K) +
      (((L.map Term.cd).sum : ℤ) : K) * d +
        (((L.map fun t => t.cnu * vecGet ν t.idx).sum : ℤ) : K) := by
  induction L with
  | nil => simp
  | cons t L ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.map_cons, List.sum_cons, Term.coeff]; push_cast; ring

/-- **Merging a template.** -/
theorem merged_sum {n : ℕ} {ts : List Term} {gs : List MTerm} (h : mergedOk n ts gs = true)
    {K : Type*} [CommRing K] (d : K) (ν : Fin n → ℤ) (J : (Fin n → ℤ) → K) :
    (ts.map fun t => t.coeff d ν * J (ν + toVec n t.shift)).sum =
      (gs.map fun g => g.coeff d ν * J (ν + toVec n g.sh)).sum := by
  simp only [mergedOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [sum_parts (fun t => findG n t.shift gs) gs.length _ ts (fun t ht => (h1 t ht).1),
    ← sum_range_getD (fun g => g.coeff d ν * J (ν + toVec n g.sh)) mdflt gs]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk := Finset.mem_range.1 hk
  have hg := h2 k hk
  simp only [groupOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at hg
  obtain ⟨⟨hc0, hcd⟩, hnu⟩ := hg
  set g := gs.getD k mdflt
  have e : ∀ t ∈ fiber n gs ts k, t.coeff d ν * J (ν + toVec n t.shift) =
      t.coeff d ν * J (ν + toVec n g.sh) := by
    intro t ht
    have hf := of_decide_eq_true (List.mem_filter.1 ht).2
    have := findG_spec (n := n) (s := t.shift) (gs := gs) (by rw [hf]; exact hk)
    rw [hf] at this
    rw [toVec_eq_of_shEq this]
  change ((fiber n gs ts k).map _).sum = _
  rw [List.map_congr_left e, List.sum_map_mul_right, sum_coeff, MTerm.coeff, hc0, hcd,
    sum_cnu ν (fiber n gs ts k) (fun t ht => (h1 t (List.mem_filter.1 ht).1).2),
    sum_nu ν g.nu (fun t ht => h3 g (by
      show gs.getD k mdflt ∈ gs
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk) t ht)]
  congr 2
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hnu a (Finset.mem_range.1 ha)]

/-! ### The groups of a seed -/

/-- The label of group `g` for the seed packed as `c`. -/
def lab (C : Ctx) (c : ℕ) (g : MTerm) : ℕ := c + g.dl - C.off

/-- The entries `(label, y · (k0 + cd d))` of the groups whose digit satisfies `D`. -/
noncomputable def gP (C : Ctx) (D : ℕ → Bool) (c : ℕ) (y : Poly) :
    List MTerm → ℕ → List (ℕ × Poly)
  | [], _ => []
  | g :: gs, a => if D (a % C.R) then (lab C c g, Poly.mul y [g.k0 C.B C.o c, g.cd]) ::
      gP C D c y gs (a / C.R) else gP C D c y gs (a / C.R)

theorem gP_zero (C : Ctx) {D : ℕ → Bool} (hD : D 0 = false) (c : ℕ) (y : Poly) :
    ∀ gs : List MTerm, gP C D c y gs 0 = []
  | [] => rfl
  | g :: gs => by simp [gP, hD, gP_zero C hD c y gs]

theorem gP_length (C : Ctx) (D : ℕ → Bool) (c : ℕ) (y : Poly) :
    ∀ (gs : List MTerm) (a : ℕ), (gP C D c y gs a).length ≤ gs.length
  | [], _ => le_rfl
  | g :: gs, a => by
    have := gP_length C D c y gs (a / C.R)
    by_cases h : D (a % C.R) <;> simp [gP, h] <;> omega

/-- The value `(label, p(x₀))` of an entry. -/
def ev (x : ℤ) (e : ℕ × Poly) : ℕ × ℤ := (e.1, evalZ x e.2)

theorem evalZ_mul_pair (x : ℤ) (m : Poly) (a b : ℤ) :
    evalZ x (Poly.mul m [a, b]) = Int.mul (evalZ x m) (Int.add a (Int.mul b x)) := by
  simp only [Poly.evalZ_eq_eval, Poly.eval_mul, Poly.eval_cons, Poly.eval_nil, Int.cast_id,
    Poly.int_add_eq, Poly.int_mul_eq]
  ring

theorem gEnt_eq (C : Ctx) (q c : ℕ) (hq : q ≠ 0) (y : Poly) :
    ∀ (gs : List MTerm) (a : ℕ), gEnt C q c (evalZ C.x0 y) gs a =
      (gP C (fun d => decide (d = q)) c y gs a).map (ev C.x0)
  | [], _ => rfl
  | g :: gs, a => by
    change (bif Nat.beq a 0 then [] else
      bif Nat.beq (Nat.mod a C.R) q then
        (Nat.sub (Nat.add c g.dl) C.off,
          Int.mul (evalZ C.x0 y) (Int.add (g.k0 C.B C.o c) (Int.mul g.cd (Int.ofNat C.x0)))) ::
          gEnt C q c (evalZ C.x0 y) gs (Nat.div a C.R)
      else gEnt C q c (evalZ C.x0 y) gs (Nat.div a C.R)) = _
    cases ha : Nat.beq a 0
    · cases hd : Nat.beq (Nat.mod a C.R) q
      · have : ¬ a % C.R = q := fun h => by
          rw [show Nat.mod a C.R = a % C.R from rfl, h, Nat.beq_refl] at hd
          exact Bool.noConfusion hd
        simp only [Bool.cond_false, gP, this, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact gEnt_eq C q c hq y gs _
      · have : a % C.R = q := Nat.eq_of_beq_eq_true hd
        simp only [Bool.cond_false, Bool.cond_true, gP, this, decide_true, ↓reduceIte,
          List.map_cons]
        rw [gEnt_eq C q c hq y gs]
        simp only [ev, lab, evalZ_mul_pair]; rfl
    · rw [Nat.eq_of_beq_eq_true ha, gP_zero C (by simpa using hq.symm)]; rfl

/-- The entries of a seed in part `p`, as polynomials. -/
noncomputable def seedP (C : Ctx) (fac : List Poly) (qe p : ℕ) (s : GSeed) : List (ℕ × Poly) :=
  gP C (fun d => decide (d = p + 1)) s.c (s.mult fac qe) (rGetL (rGetL C.mt s.i) s.j) s.a

theorem sum_gP_parts {M : Type*} [AddCommMonoid M] (C : Ctx) (P c : ℕ) (y : Poly)
    (f : ℕ × Poly → M) : ∀ (gs : List MTerm) (a : ℕ),
    ∑ p ∈ range P, ((gP C (fun d => decide (d = p + 1)) c y gs a).map f).sum =
      ((gP C (fun d => decide (1 ≤ d ∧ d ≤ P)) c y gs a).map f).sum
  | [], _ => by simp [gP]
  | g :: gs, a => by
    have e : ∀ p, ((gP C (fun d => decide (d = p + 1)) c y (g :: gs) a).map f).sum =
        (if a % C.R - 1 = p ∧ 1 ≤ a % C.R then f (lab C c g, Poly.mul y [g.k0 C.B C.o c, g.cd])
          else 0) + ((gP C (fun d => decide (d = p + 1)) c y gs (a / C.R)).map f).sum := by
      intro p
      by_cases h : a % C.R = p + 1
      · simp [gP, h]
      · have : ¬ (a % C.R - 1 = p ∧ 1 ≤ a % C.R) := by omega
        simp [gP, h, this]
    rw [Finset.sum_congr rfl fun p _ => e p, Finset.sum_add_distrib, sum_gP_parts C P c y f gs]
    by_cases h : 1 ≤ a % C.R ∧ a % C.R ≤ P
    · have : ∑ p ∈ range P, (if a % C.R - 1 = p ∧ 1 ≤ a % C.R then
          f (lab C c g, Poly.mul y [g.k0 C.B C.o c, g.cd]) else 0) =
          f (lab C c g, Poly.mul y [g.k0 C.B C.o c, g.cd]) := by
        simp only [h.1, and_true]
        rw [Finset.sum_ite_eq]; simp only [Finset.mem_range]; rw [ite_eq_left (by omega)]
      rw [this]; simp [gP, h]
    · have : ∑ p ∈ range P, (if a % C.R - 1 = p ∧ 1 ≤ a % C.R then
          f (lab C c g, Poly.mul y [g.k0 C.B C.o c, g.cd]) else 0) = 0 :=
        Finset.sum_eq_zero fun p hp => ite_eq_right (by
          have := Finset.mem_range.1 hp; omega)
      rw [this, zero_add]; simp [gP, h]

theorem coverOk_cons (C : Ctx) (P mask : ℕ) (zs : List (List (ℕ × ℕ))) (c : ℕ) (g : MTerm)
    (gs : List MTerm) (a : ℕ) : coverOk C P mask zs c (g :: gs) a =
    ((bif Nat.beq (a % C.R) 0 || Nat.blt P (a % C.R) then
      (izero (g.k0 C.B C.o c) && izero g.cd) || zeroLab C.B C.o zs (lab C c g)
     else bitOf mask (a % C.R - 1)) && coverOk C P mask zs c gs (a / C.R)) := rfl

theorem gP_skip {C : Ctx} {P mask : ℕ} {zs : List (List (ℕ × ℕ))} {c : ℕ} {y : Poly} {p : ℕ}
    (hp : p < P) (hb : bitOf mask p = false) : ∀ {gs : List MTerm} {a : ℕ},
    coverOk C P mask zs c gs a = true → gP C (fun d => decide (d = p + 1)) c y gs a = []
  | [], _, _ => rfl
  | g :: gs, a, h => by
    rw [coverOk_cons, Bool.and_eq_true] at h
    have ih := gP_skip (y := y) hp hb h.2
    by_cases hd : a % C.R = p + 1
    · exfalso
      have h1 : (Nat.beq (a % C.R) 0 || Nat.blt P (a % C.R)) = false := by
        rw [hd, Bool.or_eq_false_iff]
        exact ⟨rfl, by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega⟩
      have := h.1
      rw [h1, Bool.cond_false, hd, Nat.add_sub_cancel, hb] at this
      exact Bool.noConfusion this
    · simp [gP, hd, ih]

/-- **The cover of a seed.** If `J` vanishes on the scaleless labels, the groups assigned to
parts give the whole merged relation. -/
theorem gP_cover {K : Type*} [CommRing K] {C : Ctx} {P mask : ℕ} {zs : List (List (ℕ × ℕ))}
    {c : ℕ} (y : Poly) (d : K) (J : ℕ → K) (hJ : ∀ l, zeroLab C.B C.o zs l = true → J l = 0) :
    ∀ {gs : List MTerm} {a : ℕ}, coverOk C P mask zs c gs a = true →
    ((gP C (fun d => decide (1 ≤ d ∧ d ≤ P)) c y gs a).map fun e => Poly.eval d e.2 * J e.1).sum =
      (gs.map fun g => Poly.eval d (Poly.mul y [g.k0 C.B C.o c, g.cd]) * J (lab C c g)).sum
  | [], _, _ => rfl
  | g :: gs, a, h => by
    rw [coverOk_cons, Bool.and_eq_true] at h
    have ih := gP_cover y d J hJ h.2
    by_cases hd : 1 ≤ a % C.R ∧ a % C.R ≤ P
    · have hd' : decide (1 ≤ a % C.R ∧ a % C.R ≤ P) = true := decide_eq_true hd
      simp only [gP, hd', ↓reduceIte, List.map_cons, List.sum_cons, ih]
    · have h1 : (Nat.beq (a % C.R) 0 || Nat.blt P (a % C.R)) = true := by
        simp only [Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq]; omega
      have h0 := h.1
      rw [h1, Bool.cond_true, Bool.or_eq_true, Bool.and_eq_true] at h0
      have hz : Poly.eval d (Poly.mul y [g.k0 C.B C.o c, g.cd]) * J (lab C c g) = 0 := by
        rcases h0 with ⟨h2, h3⟩ | h2
        · rw [eq_zero_of_izero h2, eq_zero_of_izero h3]; simp [Poly.eval_mul]
        · rw [hJ _ h2, mul_zero]
      simp only [gP, decide_eq_true_eq, hd, ↓reduceIte, List.map_cons, List.sum_cons, hz, zero_add]
      exact ih

/-! ### The relation of a seed -/

/-- The merged template `C.mt` is the template of `F` merged by shift, with packed shifts `dl`,
`C.off = Σₐ Bᵃ`, at most `Gmax` groups per relation and coefficients of norm at most `Kmax` on
the range of the digits. -/
noncomputable def mtOk (F : Family) (C : Ctx) (Kmax Gmax : ℕ) : Bool :=
  decide (0 < C.B) && decide (C.off = packC C.B 1 (List.replicate F.nProp 0)) &&
    (List.range F.nLoop).all fun i => (List.range F.nMom).all fun j =>
      decide ((rGetL (rGetL C.mt i) j).length ≤ Gmax) &&
      mergedOk F.nProp (F.template i j) (rGetL (rGetL C.mt i) j) &&
      (rGetL (rGetL C.mt i) j).all fun g =>
        decide (g.sh.length = F.nProp) && g.sh.all (fun x => decide (x.natAbs ≤ 1)) &&
        decide (g.dl = packC C.B 1 g.sh) && g.nu.all (fun t => decide (t.2.1 = C.B ^ t.1)) &&
        decide (g.c0.natAbs + g.cd.natAbs + (C.B + C.o) * (g.nu.map fun t => t.2.2.natAbs).sum ≤
          Kmax)

theorem mtOk_spec {F : Family} {C : Ctx} {Kmax Gmax : ℕ} (h : mtOk F C Kmax Gmax = true)
    {i j : ℕ} (hi : i < F.nLoop) (hj : j < F.nMom) :
    0 < C.B ∧ C.off = packC C.B 1 (List.replicate F.nProp 0) ∧
      (rGetL (rGetL C.mt i) j).length ≤ Gmax ∧
      mergedOk F.nProp (F.template i j) (rGetL (rGetL C.mt i) j) = true ∧
      ∀ g ∈ rGetL (rGetL C.mt i) j, g.sh.length = F.nProp ∧ (∀ x ∈ g.sh, x.natAbs ≤ 1) ∧
        g.dl = packC C.B 1 g.sh ∧ (∀ t ∈ g.nu, t.2.1 = C.B ^ t.1) ∧
        g.c0.natAbs + g.cd.natAbs + (C.B + C.o) * (g.nu.map fun t => t.2.2.natAbs).sum ≤
          Kmax := by
  simp only [mtOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  obtain ⟨⟨h3, h4⟩, h5⟩ := h2 i hi j hj
  refine ⟨h0, h1, h3, h4, fun g hg => ?_⟩
  obtain ⟨⟨⟨⟨h6, h7⟩, h8⟩, h9⟩, h10⟩ := h5 g hg
  exact ⟨h6, h7, h8, h9, h10⟩

theorem k0_aux (B o c : ℕ) (c0 : ℤ) : ∀ l : List (ℕ × ℕ × ℤ),
    (List.rec c0 (fun t _ ih =>
      Int.add (Int.mul t.2.2 (Int.subNatNat (Nat.mod (Nat.div c t.2.1) B) o)) ih) l : ℤ) =
      c0 + (l.map fun t => t.2.2 * (((c / t.2.1 % B : ℕ) : ℤ) - o)).sum
  | [] => by simp
  | t :: l => by
    change Int.add (Int.mul t.2.2 (Int.subNatNat (Nat.mod (Nat.div c t.2.1) B) o)) _ = _
    rw [k0_aux B o c c0 l, Poly.int_add_eq, Poly.int_mul_eq, Int.subNatNat_eq_coe]
    simp only [List.map_cons, List.sum_cons]
    change t.2.2 * ((c / t.2.1 % B : ℕ) - (o : ℤ)) + _ = _
    ring

theorem k0_eq (B o c : ℕ) (g : MTerm) :
    g.k0 B o c = g.c0 + (g.nu.map fun t => t.2.2 * (((c / t.2.1 % B : ℕ) : ℤ) - o)).sum :=
  k0_aux B o c g.c0 g.nu

theorem natAbs_k0_le {B : ℕ} (hB : 0 < B) (o c : ℕ) (g : MTerm) :
    (g.k0 B o c).natAbs ≤ g.c0.natAbs + (B + o) * (g.nu.map fun t => t.2.2.natAbs).sum := by
  rw [k0_eq]
  refine (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ?_ _)
  induction g.nu with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (Int.natAbs_add_le _ _).trans ?_
    rw [Int.natAbs_mul, mul_add]
    have : ((((c / t.2.1 % B : ℕ) : ℤ) - o)).natAbs ≤ B + o := by
      have := Nat.mod_lt (c / t.2.1) hB
      omega
    have := Nat.mul_le_mul_left t.2.2.natAbs this
    nlinarith [ih]

/-- **The merged relation of a seed vanishes.** -/
theorem seed_rel {F : Family} {C : Ctx} {Kmax Gmax : ℕ} (hmt : mtOk F C Kmax Gmax = true)
    {i j c : ℕ} (hi : i < F.nLoop) (hj : j < F.nMom) (hc : innerC C.B F.nProp c = true)
    {K : Type*} [CommRing K] (I : (Fin F.nProp → ℤ) → K → K) (d : K) (hI : F.IBPHolds I d)
    (y : Poly) :
    ((rGetL (rGetL C.mt i) j).map fun g => Poly.eval d (Poly.mul y [g.k0 C.B C.o c, g.cd]) *
      I (decodeVec F.nProp C.B C.o (lab C c g)) d).sum = 0 := by
  obtain ⟨-, hoff, -, hmg, hg⟩ := mtOk_spec hmt hi hj
  obtain ⟨hpk, hin⟩ := innerC_spec (o := C.o) hc
  set ν := digL C.B C.o F.nProp c
  have hνl : ν.length = F.nProp := digL_length _ _ _ _
  have e : ∀ g ∈ rGetL (rGetL C.mt i) j,
      Poly.eval d (Poly.mul y [g.k0 C.B C.o c, g.cd]) *
        I (decodeVec F.nProp C.B C.o (lab C c g)) d =
      Poly.eval d y * (g.coeff d (toVec F.nProp ν) *
        I (toVec F.nProp ν + toVec F.nProp g.sh) d) := by
    intro g hgm
    obtain ⟨h1, h2, h3, h4, -⟩ := hg g hgm
    obtain ⟨hp1, hp2⟩ := pack_shift (B := C.B) (o := C.o) (ν := ν) (s := g.sh)
      (by rw [hνl, h1]) hin h2
    have hlab : lab C c g = pack C.B C.o (Poly.add ν g.sh) := by
      simp only [lab]
      rw [h1] at hp1
      rw [hoff, h3, ← hpk]; omega
    rw [hνl] at hp2
    rw [hlab, decodeVec_pack hp2, toVec_polyAdd]
    have hk : (g.k0 C.B C.o c : K) + d * g.cd =
        g.coeff d (toVec F.nProp ν) := by
      have hmg' := hmg
      simp only [mergedOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hmg'
      have hnu := hmg'.2 g hgm
      rw [k0_eq, MTerm.coeff]
      have : (g.nu.map fun t => t.2.2 * (((c / t.2.1 % C.B : ℕ) : ℤ) - C.o)) =
          g.nu.map fun t => t.2.2 * vecGet (toVec F.nProp ν) t.1 := by
        refine List.map_congr_left fun t ht => ?_
        rw [vecGet_toVec hνl, digL_getD _ _ _ _ _ (hnu t ht), h4 t ht]
      rw [this]; push_cast; ring
    simp only [Poly.eval_mul, Poly.eval_cons, Poly.eval_nil, mul_zero, add_zero, hk]
    ring
  rw [List.map_congr_left e, List.sum_map_mul_left,
    ← merged_sum hmg d (toVec F.nProp ν) (fun v => I v d), hI i hi j hj _, mul_zero]

/-! ### Parts -/

section Parts

variable (C : Ctx) (fac : List Poly) (qe : ℕ)

/-- The target entries `(packed label, -q t)`. -/
def tgtP (den : Poly) (T : List (List ℤ × Poly)) : List (ℕ × Poly) :=
  T.map fun t => (pack C.B C.o t.1, Poly.neg (Poly.mul den t.2))

/-- The master entries `(packed label, n)`. -/
def msP (Ms : List (List ℤ × Poly)) : List (ℕ × Poly) := Ms.map fun t => (pack C.B C.o t.1, t.2)

/-- The seed entries of part `p`. -/
noncomputable def blockP (p : ℕ) (bs : List GBlock) : List (ℕ × Poly) :=
  bs.flatMap fun b => if bitOf b.mask p then b.seeds.flatMap (seedP C fac qe p) else []

end Parts

theorem GSeed.ok_spec {C : Ctx} {L M N P qe Yb : ℕ} {nf : List ℕ} {zs : List (List (ℕ × ℕ))}
    {mask : ℕ} {s : GSeed} (h : s.ok C L M N P qe Yb nf zs mask = true) :
    s.i < L ∧ s.j < M ∧ innerC C.B N s.c = true ∧ digLe 24 qe s.e = true ∧
      s.sc.natAbs * (Poly.norm1 s.num * pd nf (qe - s.e)) ≤ Yb ∧
      coverOk C P mask zs s.c (rGetL (rGetL C.mt s.i) s.j) s.a = true := by
  simp only [GSeed.ok, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, h6⟩
  rw [← powDig_eq, ← norm1_eq]; exact h5

theorem GBlock.ok_spec {C : Ctx} {L M N P qe Yb : ℕ} {nf : List ℕ} {zs : List (List (ℕ × ℕ))}
    {b : GBlock} (h : b.ok C L M N P qe Yb nf zs = true) :
    ∀ s ∈ b.seeds, s.ok C L M N P qe Yb nf zs b.mask = true := by
  have key : ∀ l : List GSeed, (List.rec true (fun s _ ih =>
      s.ok C L M N P qe Yb nf zs b.mask && ih) l : Bool) = true →
      ∀ s ∈ l, s.ok C L M N P qe Yb nf zs b.mask = true := by
    intro l hl
    induction l with
    | nil => simp
    | cons s l ih =>
      change (s.ok C L M N P qe Yb nf zs b.mask && _) = true at hl
      rw [Bool.and_eq_true] at hl
      intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact hl.1
      · exact ih hl.2 t ht
  exact key b.seeds h

theorem Ent.eval_map_ev {R : Type*} [CommRing R] (W : ℕ → R) (x : ℤ) (L : List (ℕ × Poly)) :
    Ent.eval W (L.map (ev x)) = (L.map fun e => (evalZ x e.2 : R) * W e.1).sum := by
  simp only [Ent.eval, List.map_map]; rfl

theorem run_eq {C : Ctx} {fac : List Poly} {qe : ℕ} {nf : List ℕ} (hf : facOk C fac qe nf = true)
    {s : GSeed} (hs : digLe 24 qe s.e = true) (p : ℕ) :
    s.run C p = (seedP C fac qe p s).map (ev C.x0) := by
  unfold GSeed.run seedP
  rw [yv_eq hf s hs]
  exact gEnt_eq C (p + 1) s.c (Nat.succ_ne_zero p) _ _ _

theorem blockRuns_sum {R : Type*} [CommRing R] (W : ℕ → R) {C : Ctx} {fac : List Poly}
    {qe : ℕ} {nf : List ℕ} (hf : facOk C fac qe nf = true) (p : ℕ) :
    ∀ bs : List GBlock, (∀ b ∈ bs, ∀ s ∈ b.seeds, digLe 24 qe s.e = true) →
      ((blockRuns C p bs).map (Ent.eval W)).sum =
        ((blockP C fac qe p bs).map fun e => (evalZ C.x0 e.2 : R) * W e.1).sum
  | [], _ => rfl
  | b :: bs, h => by
    have ih := blockRuns_sum W hf p bs (fun b' hb' => h b' (by simp [hb']))
    have hseeds : ∀ l : List GSeed, (∀ s ∈ l, digLe 24 qe s.e = true) →
        ((List.rec (blockRuns C p bs) (fun s _ ih' => s.run C p :: ih') l : List Ent).map
          (Ent.eval W)).sum = ((l.flatMap (seedP C fac qe p)).map
            fun e => (evalZ C.x0 e.2 : R) * W e.1).sum +
              ((blockRuns C p bs).map (Ent.eval W)).sum := by
      intro l hl
      induction l with
      | nil => simp
      | cons s l ihl =>
        change ((s.run C p :: _).map (Ent.eval W)).sum = _
        rw [List.map_cons, List.sum_cons, ihl (fun t ht => hl t (by simp [ht])),
          run_eq hf (hl s (by simp)), Ent.eval_map_ev]
        simp only [List.flatMap_cons, List.map_append, List.sum_append]; ring
    change ((bif bitOf b.mask p then List.rec (blockRuns C p bs)
      (fun s _ ih' => s.run C p :: ih') b.seeds else blockRuns C p bs).map (Ent.eval W)).sum = _
    simp only [blockP, List.flatMap_cons, List.map_append, List.sum_append] at ih ⊢
    cases hb : bitOf b.mask p
    · simp only [Bool.cond_false, ih, Bool.false_eq_true, ↓reduceIte, List.map_nil,
        List.sum_nil, zero_add]
    · simp only [Bool.cond_true, ↓reduceIte]
      rw [hseeds b.seeds (h b (by simp)), ih]

theorem tgt_run (C : Ctx) (den : Poly) : ∀ T : List (List ℤ × Poly),
    (List.rec [] (fun t _ ih => (packC C.B C.o t.1, Int.neg (Int.mul
      (hornerZ (Int.ofNat C.x0) den) (hornerZ (Int.ofNat C.x0) t.2))) :: ih) T : Ent) =
      (tgtP C den T).map (ev C.x0)
  | [] => rfl
  | t :: T => by
    change (packC C.B C.o t.1, Int.neg (Int.mul (hornerZ (Int.ofNat C.x0) den)
      (hornerZ (Int.ofNat C.x0) t.2))) :: _ = _
    rw [tgt_run C den T]
    simp only [tgtP, List.map_cons, ev, packC_eq, hornerZ_eq, Poly.evalZ_eq_eval, Poly.eval_neg,
      Poly.eval_mul]
    rfl

theorem ms_run (C : Ctx) : ∀ T : List (List ℤ × Poly),
    (List.rec [] (fun t _ ih => (packC C.B C.o t.1, hornerZ (Int.ofNat C.x0) t.2) :: ih) T : Ent) =
      (msP C T).map (ev C.x0)
  | [] => rfl
  | t :: T => by
    change (packC C.B C.o t.1, hornerZ (Int.ofNat C.x0) t.2) :: _ = _
    rw [ms_run C T]
    simp only [msP, List.map_cons, ev, packC_eq, hornerZ_eq]
    rfl

/-- **A part cancels at `x₀`.** -/
theorem part_sum {C : Ctx} {fac : List Poly} {qe : ℕ} {nf : List ℕ} (hf : facOk C fac qe nf = true)
    {den : Poly} {tgt ms : List (List ℤ × Poly)} {bs : List GBlock} {p : ℕ}
    (hb : ∀ b ∈ bs, ∀ s ∈ b.seeds, digLe 24 qe s.e = true)
    (h : partOk C den tgt ms bs p = true) (W : ℕ → ℤ) :
    ((tgtP C den tgt ++ msP C ms ++ blockP C fac qe p bs).map
      fun e => evalZ C.x0 e.2 * W e.1).sum = 0 := by
  unfold partOk at h
  rw [isNil_eq] at h
  have h0 := congrArg (Ent.eval W) h
  rw [Ent.eval_tree, Ent.eval_nil, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
    tgt_run, ms_run, blockRuns_sum W hf p bs hb, Ent.eval_map_ev, Ent.eval_map_ev] at h0
  simp only [List.map_append, List.sum_append, Int.cast_id] at h0 ⊢
  rw [← h0]; ring

theorem norm1_mul_pair (m : Poly) (a b : ℤ) :
    Poly.norm1 (Poly.mul m [a, b]) ≤ Poly.norm1 m * (a.natAbs + b.natAbs) := by
  simpa using Poly.norm1_mul m [a, b]

theorem gP_norm {C : Ctx} {D : ℕ → Bool} {c : ℕ} {y : Poly} {Kmax : ℕ} :
    ∀ {gs : List MTerm}, (∀ g ∈ gs, (g.k0 C.B C.o c).natAbs + g.cd.natAbs ≤ Kmax) → ∀ a,
      ((gP C D c y gs a).map fun e => Poly.norm1 e.2).sum ≤ gs.length * (Poly.norm1 y * Kmax)
  | [], _, _ => by simp [gP]
  | g :: gs, h, a => by
    have ih := gP_norm (D := D) (c := c) (y := y) (gs := gs)
      (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) (a / C.R)
    have hg : Poly.norm1 (Poly.mul y [g.k0 C.B C.o c, g.cd]) ≤ Poly.norm1 y * Kmax :=
      (norm1_mul_pair _ _ _).trans (Nat.mul_le_mul_left _ (h g (by simp)))
    by_cases hd : D (a % C.R) = true
    · simp only [gP, hd, ↓reduceIte, List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
    · simp only [gP, hd, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      nlinarith


/-! ### Soundness -/

theorem sum_flatten_map {α M : Type*} [AddCommMonoid M] (f : α → M) :
    ∀ L : List (List α), ((L.map fun l => (l.map f).sum)).sum = (L.flatten.map f).sum
  | [] => rfl
  | l :: L => by simp [sum_flatten_map f L]

theorem sum_chunks {α M : Type*} [AddCommMonoid M] (f : α → M) (ls : List ℕ) (T : List α) {P : ℕ}
    (hP : ls.length < P) :
    ∑ p ∈ range P, ((rGetL (chunks ls T) p).map f).sum = (T.map f).sum := by
  simp only [rGetL_eq]
  rw [sum_range_getD_le (fun l => (l.map f).sum) [] rfl (chunks ls T)
    (by rw [chunks_length]; omega), sum_flatten_map, chunks_flatten]

theorem sum_getD_le {α : Type*} (f : α → ℕ) : ∀ (L : List (List α)) (p : ℕ),
    ((L.getD p []).map f).sum ≤ (L.flatten.map f).sum
  | [], _ => by simp
  | l :: L, 0 => by simp
  | l :: L, p + 1 => by
    simp only [List.getD_cons_succ, List.flatten_cons, List.map_append, List.sum_append]
    exact (sum_getD_le f L p).trans (Nat.le_add_left _ _)

theorem sum_chunk_le {α : Type*} (f : α → ℕ) (ls : List ℕ) (T : List α) (p : ℕ) :
    ((rGetL (chunks ls T) p).map f).sum ≤ (T.map f).sum := by
  rw [rGetL_eq]
  calc _ ≤ ((chunks ls T).flatten.map f).sum := sum_getD_le f _ p
    _ = _ := by rw [chunks_flatten]

theorem sum_flatMap' {α β M : Type*} [AddCommMonoid M] (g : α → List β) (f : β → M) :
    ∀ l : List α, ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum
  | [] => rfl
  | a :: l => by simp [sum_flatMap' g f l]

/-- **The seeds of all parts sum to zero.** -/
theorem blockP_total {F : Family} {C : Ctx} {fac : List Poly} {qe Yb Kmax Gmax P : ℕ}
    {nf : List ℕ} {zs : List (List (ℕ × ℕ))} (hmt : mtOk F C Kmax Gmax = true)
    {K : Type*} [CommRing K] (I : (Fin F.nProp → ℤ) → K → K) (d : K) (hI : F.IBPHolds I d)
    (hJ : ∀ l, zeroLab C.B C.o zs l = true → I (decodeVec F.nProp C.B C.o l) d = 0) :
    ∀ bs : List GBlock, (∀ b ∈ bs, b.ok C F.nLoop F.nMom F.nProp P qe Yb nf zs = true) →
      ∑ p ∈ range P, ((blockP C fac qe p bs).map fun e =>
        Poly.eval d e.2 * I (decodeVec F.nProp C.B C.o e.1) d).sum = 0
  | [], _ => by simp [blockP]
  | b :: bs, h => by
    set f : ℕ × Poly → K := fun e => Poly.eval d e.2 * I (decodeVec F.nProp C.B C.o e.1) d
    have ih := blockP_total (fac := fac) hmt I d hI hJ bs (fun b' hb' => h b' (by simp [hb']))
    have hs := GBlock.ok_spec (h b (by simp))
    have e : ∀ p ∈ range P, ((blockP C fac qe p (b :: bs)).map f).sum =
        (b.seeds.map fun s => ((seedP C fac qe p s).map f).sum).sum +
          ((blockP C fac qe p bs).map f).sum := by
      intro p hp
      have hp := Finset.mem_range.1 hp
      simp only [blockP, List.flatMap_cons, List.map_append, List.sum_append]
      congr 1
      cases hb : bitOf b.mask p
      · simp only [Bool.false_eq_true, ↓reduceIte, List.map_nil, List.sum_nil]
        symm
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
        obtain ⟨-, -, -, -, -, hc⟩ := GSeed.ok_spec (hs t ht)
        rw [seedP, gP_skip (y := t.mult fac qe) hp hb hc]; rfl
      · simp only [↓reduceIte, sum_flatMap']
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih, add_zero]
    have key : ∀ l : List GSeed, (∀ s ∈ l, s.ok C F.nLoop F.nMom F.nProp P qe Yb nf zs b.mask
        = true) → ∑ p ∈ range P, (l.map fun s => ((seedP C fac qe p s).map f).sum).sum = 0 := by
      intro l hl
      induction l with
      | nil => simp
      | cons s l ihl =>
        simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib,
          ihl (fun t ht => hl t (by simp [ht])), add_zero]
        obtain ⟨hi, hj, hc, -, -, hcv⟩ := GSeed.ok_spec (hl s (by simp))
        simp only [seedP]
        rw [sum_gP_parts, gP_cover (s.mult fac qe) d _ hJ hcv]
        exact seed_rel hmt hi hj hc I d hI _
    exact key b.seeds hs

theorem seedP_norm {F : Family} {C : Ctx} {fac : List Poly} {qe Yb Kmax Gmax P : ℕ}
    {nf : List ℕ} {zs : List (List (ℕ × ℕ))} {mask : ℕ} (hmt : mtOk F C Kmax Gmax = true)
    (hnf : nf = fac.map Poly.norm1) {s : GSeed}
    (hs : s.ok C F.nLoop F.nMom F.nProp P qe Yb nf zs mask = true) (p : ℕ) :
    ((seedP C fac qe p s).map fun e => Poly.norm1 e.2).sum ≤ Gmax * (Yb * Kmax) := by
  obtain ⟨hi, hj, -, -, hy, -⟩ := GSeed.ok_spec hs
  obtain ⟨hB, -, hG, -, hg⟩ := mtOk_spec hmt hi hj
  have hK : ∀ g ∈ rGetL (rGetL C.mt s.i) s.j, (g.k0 C.B C.o s.c).natAbs + g.cd.natAbs ≤ Kmax :=
    fun g hgm => by
      have := (hg g hgm).2.2.2.2
      have := natAbs_k0_le hB C.o s.c g
      omega
  have hY : Poly.norm1 (s.mult fac qe) ≤ Yb := (norm1_mult fac qe s).trans (hnf ▸ hy)
  refine (gP_norm hK _).trans ?_
  exact Nat.mul_le_mul hG (Nat.mul_le_mul_right _ hY)

theorem blockP_norm {F : Family} {C : Ctx} {fac : List Poly} {qe Yb Kmax Gmax P : ℕ}
    {nf : List ℕ} {zs : List (List (ℕ × ℕ))} (hmt : mtOk F C Kmax Gmax = true)
    (hnf : nf = fac.map Poly.norm1) (p : ℕ) : ∀ bs : List GBlock,
    (∀ b ∈ bs, b.ok C F.nLoop F.nMom F.nProp P qe Yb nf zs = true) →
    ((blockP C fac qe p bs).map fun e => Poly.norm1 e.2).sum ≤
      (bs.map fun b => b.seeds.length).sum * (Gmax * (Yb * Kmax))
  | [], _ => by simp [blockP]
  | b :: bs, h => by
    have ih := blockP_norm hmt hnf p bs (fun b' hb' => h b' (by simp [hb']))
    have hs := GBlock.ok_spec (h b (by simp))
    have hb : ((if bitOf b.mask p then b.seeds.flatMap (seedP C fac qe p) else []).map
        fun e => Poly.norm1 e.2).sum ≤ b.seeds.length * (Gmax * (Yb * Kmax)) := by
      split_ifs
      · rw [sum_flatMap']
        have : ∀ l : List GSeed, (∀ s ∈ l, s.ok C F.nLoop F.nMom F.nProp P qe Yb nf zs b.mask
            = true) → (l.map fun s => ((seedP C fac qe p s).map fun e => Poly.norm1 e.2).sum).sum
              ≤ l.length * (Gmax * (Yb * Kmax)) := by
          intro l hl
          induction l with
          | nil => simp
          | cons s l ihl =>
            simp only [List.map_cons, List.sum_cons, List.length_cons, add_mul, one_mul]
            have := seedP_norm hmt hnf (hl s (by simp)) p
            have := ihl (fun t ht => hl t (by simp [ht]))
            omega
        exact this _ hs
      · simp
    simp only [blockP, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, add_mul] at ih ⊢
    exact Nat.add_le_add hb ih

theorem tgtP_norm (C : Ctx) (den : Poly) (T : List (List ℤ × Poly)) :
    ((tgtP C den T).map fun e => Poly.norm1 e.2).sum ≤
      Poly.norm1 den * (T.map fun t => Poly.norm1 t.2).sum := by
  induction T with
  | nil => simp [tgtP]
  | cons t T ih =>
    simp only [tgtP, List.map_cons, List.sum_cons, Poly.norm1_neg, mul_add] at ih ⊢
    exact Nat.add_le_add (Poly.norm1_mul _ _) ih

theorem sum_map_neg' {α R : Type*} [AddCommGroup R] (f : α → R) :
    ∀ L : List α, (L.map fun x => -f x).sum = -(L.map f).sum
  | [] => by simp
  | a :: L => by simp [sum_map_neg' f L, add_comm]

/-- **Soundness of a label-split certificate.** -/
theorem gcert_sound {F : Family} {C : Ctx} {fac : List Poly} {qe Yb Kmax Gmax P : ℕ}
    {nf : List ℕ} {zs : List (List (ℕ × ℕ))} {den : Poly} {T Ms : List (List ℤ × Poly)}
    {tl ml : List ℕ} {bs : List GBlock}
    (hmt : mtOk F C Kmax Gmax = true) (hf : facOk C fac qe nf = true)
    (hzs : zs = F.zeroSectors.map fun S => S.map fun a => (a, C.B ^ a))
    (hblk : ∀ b ∈ bs, b.ok C F.nLoop F.nMom F.nProp P qe Yb nf zs = true)
    (hcl : ∀ t ∈ T ++ Ms, inRange C.B C.o F.nProp t.1 = true)
    (htl : tl.length < P) (hml : ml.length < P)
    (hG : (bs.map fun b => b.seeds.length).sum * (Gmax * (Yb * Kmax)) +
      Poly.norm1 den * (T.map fun t => Poly.norm1 t.2).sum + (Ms.map fun t => Poly.norm1 t.2).sum
        < C.x0)
    (hpart : ∀ p < P, partOk C den (rGetL (chunks tl T) p) (rGetL (chunks ml Ms) p) bs p = true)
    {K : Type*} [Field K] (I : (Fin F.nProp → ℤ) → K → K) (d : K) (hI : F.IBPHolds I d)
    (hz : F.ZeroSectors I d) :
    LinComb.eval (fun l => I (toVec F.nProp l) d) d
      (LinComb.smul den T ++ Ms.map fun m => (m.1, Poly.neg m.2)) = 0 := by
  set J : ℕ → K := fun l => I (decodeVec F.nProp C.B C.o l) d with hJdef
  have hnf : nf = fac.map Poly.norm1 := by
    simp only [facOk, Bool.and_eq_true, decide_eq_true_eq] at hf; exact hf.2
  have hdig : ∀ b ∈ bs, ∀ s ∈ b.seeds, digLe 24 qe s.e = true := fun b hb s hs =>
    (GSeed.ok_spec (GBlock.ok_spec (hblk b hb) s hs)).2.2.2.1
  have hJ : ∀ l, zeroLab C.B C.o zs l = true → J l = 0 := by
    intro l hl
    obtain ⟨S', hS', h'⟩ := zeroLab_spec hl
    rw [hzs] at hS'
    obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hS'
    refine hz S hS _ fun a ha => ?_
    have := h' (a, C.B ^ a) (List.mem_map.2 ⟨a, ha, rfl⟩)
    simp only at this
    simp only [vecGet, decodeVec, digit]
    split_ifs <;> omega
  -- every part vanishes over `K`
  set Tp : ℕ → List (ℕ × Poly) := fun p => tgtP C den (rGetL (chunks tl T) p) ++
    msP C (rGetL (chunks ml Ms) p) ++ blockP C fac qe p bs with hTp
  have hpk : ∀ p < P, ((Tp p).map fun e => Poly.eval d e.2 * J e.1).sum = 0 := by
    intro p hp
    refine kron_sum_eq_zero (fun _ => false) (C.x0 : ℤ) _ (Tp p) le_rfl ?_
      (fun W _ => part_sum hf hdig (hpart p hp) W) d J (fun _ h => absurd h (by simp))
    have h1 := tgtP_norm C den (rGetL (chunks tl T) p)
    have h2 := sum_chunk_le (fun t : List ℤ × Poly => Poly.norm1 t.2) tl T p
    have h3 := sum_chunk_le (fun t : List ℤ × Poly => Poly.norm1 t.2) ml Ms p
    have h4 := blockP_norm hmt hnf p bs hblk
    have h5 : ((msP C (rGetL (chunks ml Ms) p)).map fun e => Poly.norm1 e.2).sum =
        ((rGetL (chunks ml Ms) p).map fun t => Poly.norm1 t.2).sum := by
      simp [msP, Function.comp_def]
    have h6 := Nat.mul_le_mul_left (Poly.norm1 den) h2
    have hb : ((Tp p).map fun e => Poly.norm1 e.2).sum < C.x0 := by
      simp only [hTp, List.map_append, List.sum_append]
      omega
    exact_mod_cast hb
  have htot : ∑ p ∈ range P, ((Tp p).map fun e => Poly.eval d e.2 * J e.1).sum = 0 :=
    Finset.sum_eq_zero fun p hp => hpk p (Finset.mem_range.1 hp)
  simp only [hTp, List.map_append, List.sum_append, Finset.sum_add_distrib] at htot
  rw [blockP_total hmt I d hI hJ bs hblk, add_zero] at htot
  have et := sum_chunks (fun e => Poly.eval d e.2 * J (pack C.B C.o e.1) *
    (-(Poly.eval d den))) tl T htl
  have em := sum_chunks (fun e => Poly.eval d e.2 * J (pack C.B C.o e.1)) ml Ms hml
  have et' : ∀ L : List (List ℤ × Poly), ((tgtP C den L).map fun e => Poly.eval d e.2 * J e.1).sum
      = (L.map fun e => Poly.eval d e.2 * J (pack C.B C.o e.1) * (-(Poly.eval d den))).sum := by
    intro L; simp only [tgtP, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
    simp only [Function.comp_apply, Poly.eval_neg, Poly.eval_mul]; ring
  have em' : ∀ L : List (List ℤ × Poly), ((msP C L).map fun e => Poly.eval d e.2 * J e.1).sum
      = (L.map fun e => Poly.eval d e.2 * J (pack C.B C.o e.1)).sum := by
    intro L; simp only [msP, List.map_map]; rfl
  simp only [et', em', et, em] at htot
  rw [LinComb.eval_eq_sum, List.map_append, List.sum_append]
  have hT : (T.map fun e => Poly.eval d e.2 * J (pack C.B C.o e.1) * (-(Poly.eval d den))).sum =
      -(((LinComb.smul den T).map fun t => Poly.eval d t.2 * I (toVec F.nProp t.1) d).sum) := by
    rw [← sum_map_neg']
    simp only [LinComb.smul, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    simp only [Function.comp_apply, Poly.eval_mul, hJdef,
      decodeVec_pack (hcl e (List.mem_append_left _ he))]
    ring
  have hM : (Ms.map fun e => Poly.eval d e.2 * J (pack C.B C.o e.1)).sum =
      -(((Ms.map fun m => (m.1, Poly.neg m.2)).map
        fun t => Poly.eval d t.2 * I (toVec F.nProp t.1) d).sum) := by
    rw [← sum_map_neg']
    simp only [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    simp only [Function.comp_apply, Poly.eval_neg, hJdef,
      decodeVec_pack (hcl e (List.mem_append_right _ he))]
    ring
  rw [hT, hM] at htot
  linear_combination -htot

/-- **The reduction from a label-split certificate.** If all checks pass, then for every family
of values `I` satisfying the IBP relations and the zero sectors of `F` at `d` with `q(d) ≠ 0`,
`Σ tₗ(d) I(l) = Σ (nⱼ(d) / q(d)) I(Mⱼ)`. -/
theorem gcert_reduction {F : Family} {C : Ctx} {fac : List Poly} {qe Yb Kmax Gmax P : ℕ}
    {nf : List ℕ} {zs : List (List (ℕ × ℕ))} {den : Poly} {T Ms : List (List ℤ × Poly)}
    {tl ml : List ℕ} {bs : List GBlock}
    (hmt : mtOk F C Kmax Gmax = true) (hf : facOk C fac qe nf = true)
    (hzs : zs = F.zeroSectors.map fun S => S.map fun a => (a, C.B ^ a))
    (hblk : bs.all (GBlock.ok C F.nLoop F.nMom F.nProp P qe Yb nf zs) = true)
    (hcl : (T ++ Ms).all (fun t => inRange C.B C.o F.nProp t.1) = true)
    (htl : tl.length < P) (hml : ml.length < P)
    (hG : (bs.map fun b => b.seeds.length).sum * (Gmax * (Yb * Kmax)) +
      Poly.norm1 den * (T.map fun t => Poly.norm1 t.2).sum + (Ms.map fun t => Poly.norm1 t.2).sum
        < C.x0)
    (hpart : ∀ p < P, partOk C den (rGetL (chunks tl T) p) (rGetL (chunks ml Ms) p) bs p = true)
    {K : Type*} [Field K] (I : (Fin F.nProp → ℤ) → K → K) (d : K) (hI : F.IBPHolds I d)
    (hz : F.ZeroSectors I d) (hq : Poly.eval d den ≠ 0) :
    (T.map fun t => Poly.eval d t.2 * I (toVec F.nProp t.1) d).sum =
      (Ms.map fun m => Poly.eval d m.2 / Poly.eval d den * I (toVec F.nProp m.1) d).sum := by
  rw [List.all_eq_true] at hblk hcl
  exact Step.reduction_combo (fun l => I (toVec F.nProp l) d) d den T Ms
    (gcert_sound hmt hf hzs hblk hcl htl hml hG hpart I d hI hz) hq

end QED.Algebra.IBPCert.Sector
