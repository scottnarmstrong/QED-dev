/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

/-!
# Label-split IBP certificates: kernel evaluation (layer L2)

A reduction certificate `Σₖ yₖ Rₖ = q T - Σⱼ nⱼ Mⱼ` (seeds `Rₖ`, multipliers `yₖ ∈ ℤ[d]`) is
checked by evaluation at one large integer point `x₀`, as in `QED.Algebra.IBPCert.KStep`. This
module holds the functions the kernel evaluates; they use only the core library, so that the
certificate data and the checks of its parts load fast. `QED.Algebra.IBPCertSectorSound` proves
the soundness.

* **Merged template.** The terms of an IBP relation with the same shift are merged into one
  group `QED.Algebra.IBPCert.Sector.MTerm`, with coefficient `c0 + cd d + Σ cₐ νₐ`.
* **Factored multipliers.** A seed (`QED.Algebra.IBPCert.Sector.GSeed`) stores its index vector
  packed, and its multiplier as `sc · num · q / den`, where `q = Π fₐ^{qₐ}` is a product of fixed
  factors, `den = Π fₐ^{eₐ}` divides it and `num` is a polynomial with coefficients in a few bits.
  The value at `x₀` costs one Horner evaluation, a few powers and one exact division.
* **Label split.** The labels are split into parts; a seed assigns each of its groups to a part
  (a digit of `a` in base `R`, `0` for none). Each part is checked separately: its entries must
  cancel label by label. A group assigned to no part must have a vanishing coefficient or a label
  in a scaleless sector (`QED.Algebra.IBPCert.Sector.GSeed.ok`, checked once per seed). Seeds come
  in blocks with the mask of the parts they reach, so the check of a part skips the other blocks.

The functions are written with the recursors `List.rec` and `Nat.rec` and with the primitive
operations of `Nat` and `Int`, which the kernel reduces directly; they are `noncomputable` since
they are only ever evaluated by the kernel (`decide +kernel`).
-/

@[expose] public section

namespace QED.Algebra.IBPCert.Sector

universe u v

/-! ### Recursor-based list functions -/

section Rec

variable {α : Type u} {β : Type v}

/-- `l ++ m`, by the recursor. -/
noncomputable def rApp (l m : List α) : List α := List.rec m (fun a _ ih => a :: ih) l

/-- `l.flatMap f`, by the recursor. -/
noncomputable def rCat (f : α → List β) (l : List α) : List β :=
  List.rec [] (fun a _ ih => rApp (f a) ih) l

/-- `l.getD n []` for a list of lists, by the recursors. -/
noncomputable def rGetL (l : List (List α)) (n : Nat) : List α :=
  List.rec (motive := fun _ => Nat → List α) (fun _ => [])
    (fun a _ ih n => Nat.rec (motive := fun _ => List α) a (fun m _ => ih m) n) l n

/-- `l.drop n`, by the recursors. -/
noncomputable def rDrop (n : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun l => l)
    (fun _ ih l => List.rec (motive := fun _ => List α) [] (fun _ t _ => ih t) l) n l

/-- `l.take n`, by the recursors. -/
noncomputable def rTake (n : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun _ => [])
    (fun _ ih l => List.rec (motive := fun _ => List α) [] (fun a t _ => a :: ih t) l) n l

/-- The slice of `l` of length `n` starting at `s`. -/
noncomputable def slice (s n : Nat) (l : List α) : List α := rTake n (rDrop s l)

/-- `T` cut into pieces of the lengths `ls`, the rest forming a last piece. -/
noncomputable def chunks (ls : List Nat) (T : List α) : List (List α) :=
  List.rec (motive := fun _ => List α → List (List α)) (fun T => [T])
    (fun n _ ih T => rTake n T :: ih (rDrop n T)) ls T

/-- `l = []`. -/
noncomputable def isNil (l : List α) : Bool := List.rec true (fun _ _ _ => false) l

end Rec

/-! ### Integers and polynomials -/

/-- `a = 0`. -/
noncomputable def izero (a : Int) : Bool := Int.rec (fun n => Nat.beq n 0) (fun _ => false) a

/-- Horner evaluation `Σ pₐ xᵃ` of a polynomial stored constant first. -/
noncomputable def hornerZ (x : Int) (p : List Int) : Int :=
  List.rec (Int.ofNat 0) (fun a _ ih => Int.add a (Int.mul x ih)) p

/-- The `ℓ¹` norm of a polynomial. -/
noncomputable def norm1 (p : List Int) : Nat := List.rec 0 (fun a _ ih => Nat.add a.natAbs ih) p

/-- The packed label `Σₐ (lₐ + o) Bᵃ`. -/
noncomputable def packC (B o : Nat) (l : List Int) : Nat :=
  List.rec 0 (fun x _ ih => Nat.add (Int.toNat (Int.add x (Int.ofNat o))) (Nat.mul B ih)) l

/-- The inverse of the zigzag map `c ↦ 2c` (`c ≥ 0`), `c ↦ -2c - 1` (`c < 0`). -/
noncomputable def unzig (k : Nat) : Int :=
  bif Nat.beq (Nat.mod k 2) 0 then Int.ofNat (Nat.div k 2) else Int.negSucc (Nat.div k 2)

/-- The polynomial of `len` coefficients stored in `n`, `w` bits each (zigzag), constant
lowest. -/
noncomputable def digitsPoly (w len n : Nat) : List Int :=
  Nat.rec (motive := fun _ => Nat → List Int) (fun _ => [])
    (fun _ ih n => unzig (Nat.mod n (Nat.pow 2 w)) :: ih (Nat.shiftRight n w)) len n

/-- The number with the base-`2²⁸⁰` digits `ns`, lowest first. -/
noncomputable def joinL (ns : List Nat) : Nat :=
  List.rec 0 (fun l _ ih => Nat.add l (Nat.shiftLeft ih 280)) ns

/-- `Π fₐ ^ eₐ` over the base-`8` digits `eₐ` of `e`, stopping when the remaining digits
vanish. -/
noncomputable def powDig (fv : List Nat) (e : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 1)
    (fun f _ ih e => bif Nat.beq e 0 then 1 else
      Nat.mul (Nat.pow f (Nat.mod e 8)) (ih (Nat.div e 8))) fv e

/-- Every base-`8` digit of `e` is at most the corresponding digit of `q`, over `n` digits, and
`e` has no further digits. -/
noncomputable def digLe (n q e : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ e => Nat.beq e 0)
    (fun _ ih q e => Nat.ble (Nat.mod e 8) (Nat.mod q 8) && ih (Nat.div q 8) (Nat.div e 8))
    n q e

/-! ### Value lists and their merging -/

/-- Entries `(packed label, value)`. -/
abbrev Ent := List (Nat × Int)

/-- Merge step: insert `t` (followed by `ts`, merged by `rec`) into a sorted list. -/
noncomputable def addC (t : Nat × Int) (rec : Ent → Ent) (ts : Ent) : Ent → Ent :=
  List.rec (t :: ts) fun u us ih =>
    bif Nat.blt t.1 u.1 then t :: rec (u :: us)
    else bif Nat.blt u.1 t.1 then u :: ih
    else bif izero (Int.add t.2 u.2) then rec us else (t.1, Int.add t.2 u.2) :: rec us

/-- Merge of two lists sorted by label, adding the values of equal labels and dropping zeros. -/
noncomputable def addE (l : Ent) : Ent → Ent :=
  List.rec (fun m => m) (fun t ts recl => addC t recl ts) l

/-- One round of pairwise merging, with a pending list. -/
noncomputable def pairsF (ls : List Ent) : Option Ent → List Ent :=
  List.rec (motive := fun _ => Option Ent → List Ent) (fun p => Option.rec [] (fun b => [b]) p)
    (fun a _ ih p => Option.rec (ih (some a)) (fun b => addE b a :: ih none) p) ls

/-- Balanced merging, `k` rounds, then a fold. -/
noncomputable def tree (k : Nat) : List Ent → Ent :=
  Nat.rec (motive := fun _ => List Ent → Ent)
    (fun ls => List.rec [] (fun a _ ih => addE a ih) ls)
    (fun _ ih ls => List.rec [] (fun a rest _ =>
      List.rec a (fun _ _ _ => ih (pairsF ls none)) rest) ls) k

/-! ### Merged templates, seeds and blocks -/

/-- A group of a merged IBP template: the integral `I(ν + sh)` with coefficient
`c0 + cd d + Σ c νₐ` over the triples `(a, Bᵃ, c)` of `nu`; `dl` is the packed shift
`Σ (shₐ + 1) Bᵃ`. -/
structure MTerm where
  /-- The shift. -/
  sh : List Int
  /-- The packed shift, offset by one in every digit. -/
  dl : Nat
  /-- The constant part of the coefficient. -/
  c0 : Int
  /-- The coefficient of `d`. -/
  cd : Int
  /-- The coefficients of the entries `νₐ`, as triples `(a, Bᵃ, c)`. -/
  nu : List (Nat × Nat × Int)

/-- The coefficient of a group at the index vector packed as `c`, without its `d` part. -/
noncomputable def MTerm.k0 (B o c : Nat) (g : MTerm) : Int :=
  List.rec g.c0 (fun t _ ih =>
    Int.add (Int.mul t.2.2 (Int.subNatNat (Nat.mod (Nat.div c t.2.1) B) o)) ih) g.nu

/-- A seed: the IBP relation `(i, j)` at the index vector packed as `c`, with multiplier
`sc · num · q / den`, where `num = digitsPoly w len (joinL n)` and `den` has the factor
exponents given by the base-`8` digits of `e`. The base-`R` digit `g` of `a` is `p + 1` if
group `g` of the template belongs to part `p`, and `0` if it belongs to none. -/
structure GSeed where
  /-- The loop momentum differentiated. -/
  i : Nat
  /-- The momentum in the numerator. -/
  j : Nat
  /-- The packed index vector. -/
  c : Nat
  /-- The integer factor of the multiplier. -/
  sc : Int
  /-- The bits per coefficient of `num`. -/
  w : Nat
  /-- The number of coefficients of `num`. -/
  len : Nat
  /-- The coefficients of `num`, in limbs of `280` bits (`QED.Algebra.IBPCert.Sector.joinL`). -/
  n : List Nat
  /-- The factor exponents of the denominator. -/
  e : Nat
  /-- The parts of the groups. -/
  a : Nat

/-- A block of seeds, with a mask containing the parts of all their groups. -/
structure GBlock where
  /-- Bit `p` is set if some group of some seed belongs to part `p`. -/
  mask : Nat
  /-- The seeds. -/
  seeds : List GSeed

/-- The constants of a certificate. -/
structure Ctx where
  /-- The base of the packed labels. -/
  B : Nat
  /-- The offset of the packed labels. -/
  o : Nat
  /-- `Σₐ Bᵃ` over the `N` digits. -/
  off : Nat
  /-- The radix of the part assignments. -/
  R : Nat
  /-- The evaluation point. -/
  x0 : Nat
  /-- The values `fₐ(x₀)` of the factors. -/
  fv : List Nat
  /-- The value `q(x₀) = Π fₐ(x₀)^{qₐ}`. -/
  qv : Nat
  /-- The merged template. -/
  mt : List (List (List MTerm))

/-- Bit `p` of `m`. -/
noncomputable def bitOf (m p : Nat) : Bool := Nat.beq (Nat.mod (Nat.shiftRight m p) 2) 1

/-- The value of the multiplier of a seed at `x₀`. -/
noncomputable def GSeed.yv (C : Ctx) (s : GSeed) : Int :=
  Int.mul s.sc (Int.mul (hornerZ (Int.ofNat C.x0) (digitsPoly s.w s.len (joinL s.n)))
    (Int.ofNat (Nat.div C.qv (powDig C.fv s.e))))

/-- The entries of the groups assigned the digit `q`, for a seed packed as `c` with multiplier
value `y`. -/
noncomputable def gEnt (C : Ctx) (q c : Nat) (y : Int) : List MTerm → Nat → Ent :=
  List.rec (fun _ => []) fun g _ ih a =>
    bif Nat.beq a 0 then [] else
    bif Nat.beq (Nat.mod a C.R) q then
      (Nat.sub (Nat.add c g.dl) C.off,
        Int.mul y (Int.add (g.k0 C.B C.o c) (Int.mul g.cd (Int.ofNat C.x0)))) ::
        ih (Nat.div a C.R)
    else ih (Nat.div a C.R)

/-- The entries of a seed in part `p`. -/
noncomputable def GSeed.run (C : Ctx) (p : Nat) (s : GSeed) : Ent :=
  gEnt C (Nat.succ p) s.c (s.yv C) (rGetL (rGetL C.mt s.i) s.j) s.a

/-- The runs of entries of the seeds of the blocks whose mask contains `p`. -/
noncomputable def blockRuns (C : Ctx) (p : Nat) (bs : List GBlock) : List Ent :=
  List.rec [] (fun b _ ih => bif bitOf b.mask p then
    List.rec ih (fun s _ ih' => s.run C p :: ih') b.seeds else ih) bs

/-- The check of part `p`: the target slice `tgt` (as `-den · t`), the master slice `ms` and the
seeds cancel label by label. -/
noncomputable def partOk (C : Ctx) (den : List Int) (tgt ms : List (List Int × List Int))
    (bs : List GBlock) (p : Nat) : Bool :=
  isNil (tree 64
    (List.rec [] (fun t _ ih => (packC C.B C.o t.1, Int.neg (Int.mul
      (hornerZ (Int.ofNat C.x0) den) (hornerZ (Int.ofNat C.x0) t.2))) :: ih) tgt ::
     List.rec [] (fun t _ ih => (packC C.B C.o t.1, hornerZ (Int.ofNat C.x0) t.2) :: ih) ms ::
     blockRuns C p bs))

/-! ### The checks of a seed -/

/-- The `n` base-`B` digits of `c` lie in `[1, B - 2]` and `c < Bⁿ`. -/
noncomputable def innerC (B n c : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun c => Nat.beq c 0)
    (fun _ ih c => Nat.blt 0 (Nat.mod c B) && Nat.blt (Nat.succ (Nat.mod c B)) B &&
      ih (Nat.div c B)) n c

/-- The label packed as `l` lies in a scaleless sector: for some listed sector, every listed
digit `(a, Bᵃ)` is at most `o` (that is, `νₐ ≤ 0`). -/
noncomputable def zeroLab (B o : Nat) (zs : List (List (Nat × Nat))) (l : Nat) : Bool :=
  List.rec false (fun S _ ih =>
    List.rec true (fun t _ ih' => Nat.ble (Nat.mod (Nat.div l t.2) B) o && ih') S || ih) zs

/-- Every group of a seed packed as `c` with assignment `a` either belongs to a part `p < P`
whose bit is set in `mask`, or has a vanishing coefficient, or has its label in a scaleless
sector. -/
noncomputable def coverOk (C : Ctx) (P mask : Nat) (zs : List (List (Nat × Nat))) (c : Nat) :
    List MTerm → Nat → Bool :=
  List.rec (fun _ => true) fun g _ ih a =>
    (bif Nat.beq (Nat.mod a C.R) 0 || Nat.blt P (Nat.mod a C.R) then
      (izero (g.k0 C.B C.o c) && izero g.cd) ||
        zeroLab C.B C.o zs (Nat.sub (Nat.add c g.dl) C.off)
     else bitOf mask (Nat.pred (Nat.mod a C.R))) && ih (Nat.div a C.R)

/-- The check of a seed: admissible indices, an index vector in the inner range, a denominator
dividing `q` (exponents `qe`), the bound `|sc| · ‖num‖ · Π ‖fₐ‖^{qₐ - eₐ} ≤ Yb` (norms `nf`), and
the cover of its groups. -/
noncomputable def GSeed.ok (C : Ctx) (L M N P : Nat) (qe Yb : Nat) (nf : List Nat)
    (zs : List (List (Nat × Nat))) (mask : Nat) (s : GSeed) : Bool :=
  Nat.blt s.i L && Nat.blt s.j M && innerC C.B N s.c && digLe 24 qe s.e &&
  Nat.ble (Nat.mul s.sc.natAbs (Nat.mul (norm1 (digitsPoly s.w s.len (joinL s.n)))
    (powDig nf (Nat.sub qe s.e)))) Yb &&
  coverOk C P mask zs s.c (rGetL (rGetL C.mt s.i) s.j) s.a

/-- The check of a block. -/
noncomputable def GBlock.ok (C : Ctx) (L M N P : Nat) (qe Yb : Nat) (nf : List Nat)
    (zs : List (List (Nat × Nat))) (b : GBlock) : Bool :=
  List.rec true (fun s _ ih => s.ok C L M N P qe Yb nf zs b.mask && ih) b.seeds

end QED.Algebra.IBPCert.Sector
