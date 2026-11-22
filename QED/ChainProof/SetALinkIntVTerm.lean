/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntVRot
public import QED.GradedProof.X0NsEnum

/-!
# Three-loop closed-loop contractions: the index terms

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58), classes `VA`, `VB`, `VC`. The three-loop analogue of
`QED.GradedProof.X0.jointEnergyFirstIntegrable_nsClosed`: a contraction `C` of `gauge` vertices
with three loops and one closed fermion loop `zOf C` sharing lines with the other loops. Every
line off the loop is assumed to carry loop momentum on `ℓ₀` or `ℓ₁` (`isTree C l = false`), so
the line factors `nsNum`, `nsMs` of (X₀) apply verbatim.

The expansion terms of `QED.GradedProof.X0.jointEnergyFirstIntegrable_blockSumGen` are integrands
of `jef_lines3` (`jef_nsLines3`), with the line rows `row3 C l` merged into the classes `cls`
with rows `a'`. Their merged exponents are checked against a list `Es` of exponent vectors each
passing the basis criterion (`Pad3`, `PatOK3`, `AllPatOK3`): by monotonicity in the exponents
(`QED.ChainProof.SetALinkV.BasisCrit.mono_e`) it suffices that every term dominates one vector
of `Es`. **`jef_nsClosed3`**: (T₉′) of the integrand of `C` at grading `0`, at any masses.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetALinkV

open QED.Graded QED.WickModel QED.GradedProof.X0
open QED.TwoLoop.Bridge (propDenom)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type} {C : Contraction 1 nA κ}

/-! ### Rows and the criterion -/

/-- The integer row of a line at three loops. -/
def row3 (C : Contraction 1 nA κ) (l : Line C) : Fin 3 → ℤ :=
  ![loopCoeff C l 0, loopCoeff C l 1, loopCoeff C l 2]

theorem lineMomentum₂_eq_rowMom3 (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 3 → Fin 4 → ℝ) (l : Line C) :
    lineMomentum₂ C pOut pIn kIn ℓ l = rowMom3 (row3 C l) (extPart C pOut pIn kIn l) ℓ := by
  rw [lineMomentum₂_eq_loopCoeff, Fin.sum_univ_three]
  simp [rowMom3, row3, Fin.sum_univ_three]

/-- The class of a row: the first index whose row agrees with it up to sign. -/
def clsOf {m : ℕ} (a' : Fin (m + 1) → Fin 3 → ℤ) (r : Fin 3 → ℤ) : Fin (m + 1) :=
  ((List.finRange (m + 1)).find? fun c => decide (a' c = r ∨ a' c = -r)).getD 0

/-- The merged exponents of the line classes. -/
def mergedE {m : ℕ} (cls : Line C → Fin m) (e : Line C → ℕ) (c : Fin m) : ℕ :=
  ∑ l ∈ Finset.univ.filter (fun l => cls l = c), e l

/-- The exponents `2 n - d` dominate one of the vectors `Es`. -/
def Pad3 {m : ℕ} (cls : Line C → Fin m) (Es : List (Fin m → ℕ)) (n d : Line C → ℕ) : Prop :=
  ∃ E ∈ Es, ∀ c, E c ≤ mergedE cls (fun l => 2 * n l - d l) c

instance {m : ℕ} (cls : Line C → Fin m) (Es : List (Fin m → ℕ)) (n d : Line C → ℕ) :
    Decidable (Pad3 cls Es n d) := by
  unfold Pad3; infer_instance

theorem basisCrit_of_pad3 {m : ℕ} {a' : Fin m → Fin 3 → ℤ} {cls : Line C → Fin m}
    {Es : List (Fin m → ℕ)} (hEs : ∀ E ∈ Es, BasisCrit a' E 5) {n d : Line C → ℕ}
    (h : Pad3 cls Es n d) : BasisCrit a' (mergedE cls fun l => 2 * n l - d l) 5 := by
  obtain ⟨E, hE, hle⟩ := h
  exact (hEs E hE).mono_e hle

variable {m : ℕ}

/-- The terms with two extra lines parallel to one loop line. -/
def TwoOK3 (C : Contraction 1 nA κ) (cls : Line C → Fin m) (Es : List (Fin m → ℕ))
    (E' : Finset (Line C)) : Prop :=
  ∀ l ∈ zSet C, Pad3 cls Es (bump (baseN C) l 2) (baseD C E')

instance (C : Contraction 1 nA κ) (cls : Line C → Fin m) (Es : List (Fin m → ℕ))
    (E' : Finset (Line C)) : Decidable (TwoOK3 C cls Es E') := by
  unfold TwoOK3; infer_instance

/-- The terms with one extra line parallel to each loop line of `S`, `|S| ≥ 2`. -/
def SetOK3 (C : Contraction 1 nA κ) (cls : Line C → Fin m) (Es : List (Fin m → ℕ))
    (E' : Finset (Line C)) : Prop :=
  ∀ S ∈ (zSet C).powerset, 2 ≤ S.card → Pad3 cls Es (addSet (baseN C) S) (baseD C E')

instance (C : Contraction 1 nA κ) (cls : Line C → Fin m) (Es : List (Fin m → ℕ))
    (E' : Finset (Line C)) : Decidable (SetOK3 C cls Es E') := by
  unfold SetOK3; infer_instance

/-- The terms with one extra massless line. -/
def OneOK3 (C : Contraction 1 nA κ) (cls : Line C → Fin m) (Es : List (Fin m → ℕ))
    (E' : Finset (Line C)) : Prop :=
  ∀ l ∈ zSet C, Pad3 cls Es (bump (baseN C) l 1) (baseD C E')

instance (C : Contraction 1 nA κ) (cls : Line C → Fin m) (Es : List (Fin m → ℕ))
    (E' : Finset (Line C)) : Decidable (OneOK3 C cls Es E') := by
  unfold OneOK3; infer_instance

/-- The criterion for one pattern. -/
def PatOK3 (C : Contraction 1 nA κ) (cls : Line C → Fin m) (Es : List (Fin m → ℕ))
    (E' : Finset (Line C)) : Prop :=
  ((zSet C).card - E'.card = 4 → Pad3 cls Es (baseN C) (baseD C E')) ∧
    ((zSet C).card - E'.card = 2 → OneOK3 C cls Es E' ∧ TwoOK3 C cls Es E' ∧
      SetOK3 C cls Es E') ∧
    ((zSet C).card - E'.card = 0 → TwoOK3 C cls Es E' ∧ SetOK3 C cls Es E')

instance (C : Contraction 1 nA κ) (cls : Line C → Fin m) (Es : List (Fin m → ℕ))
    (E' : Finset (Line C)) : Decidable (PatOK3 C cls Es E') := by
  unfold PatOK3; infer_instance

/-- All patterns. -/
def AllPatOK3 (C : Contraction 1 nA κ) (cls : Line C → Fin m) (Es : List (Fin m → ℕ)) :
    Prop :=
  ∀ E' ∈ (zSet C).powerset, PatOK3 C cls Es E'

instance (C : Contraction 1 nA κ) (cls : Line C → Fin m) (Es : List (Fin m → ℕ)) :
    Decidable (AllPatOK3 C cls Es) := by
  unfold AllPatOK3; infer_instance

/-! ### The expansion terms -/

theorem affPoly_nsNum3 (P : Params) (Φ : Lepton.Flavors F)
    (hT : ∀ l, isZL C l = false → isTree C l = false)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (l : Line C) :
    AffPoly (baseD C (nsE α β C) l) (nsNum P Φ C α β lor l) := by
  have off : isZL C l = false → AffPoly (baseD C (nsE α β C) l) (nsNum P Φ C α β lor l) :=
    fun hz => by
      rcases affPoly_nsNum P Φ α β lor l with h | h
      · exact h
      · have h0 := congrFun h 0
        have h1 := congrFun h 1
        have := hT l hz
        simp only [rowOf, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
        simp [isTree, h0, h1] at this
  rcases l with f | g
  · by_cases hz : isZL C (.inl f) = true
    · by_cases hb : blk (β f.1) = blk (α f.tail)
      · have hE : (Sum.inl f : Line C) ∉ nsE α β C := by
          simp only [nsE, Finset.mem_filter, sameB_inl, hb, decide_true, Bool.true_eq_false,
            and_false, not_false_eq_true]
        simp only [baseD, hz, hE, ↓reduceIte]
        refine (congrArg (AffPoly 0) (funext fun k => ?_)).mp (AffPoly.const ((1 / I) *
          (1 : Matrix (Fin 4) (Fin 4) ℂ) (β f.1) (α f.tail)))
        simp [nsNum, hz, hb]
      · have hE : (Sum.inl f : Line C) ∈ nsE α β C := by
          simp only [nsE, zSet, Finset.mem_filter, Finset.mem_univ, true_and, sameB_inl, hb,
            decide_false, and_true]
          exact hz
        simp only [baseD, hz, hE, ↓reduceIte]
        refine (congrArg (AffPoly 1) (funext fun k => ?_)).mp
          ((affPoly_of_affine (electronNumerator_affine 0 (β f.1) (α f.tail))).const_mul (1 / I))
        simp [nsNum, hz, hb, QED.TwoLoop.Bridge.electronNumerator]
    · exact off (by simpa using hz)
  · exact off rfl

theorem baseD_le (hT : ∀ l, isZL C l = false → isTree C l = false) (E' : Finset (Line C))
    (l : Line C) : baseD C E' l ≤ 1 ∧ 1 ≤ baseN C l := by
  rcases l with f | g
  · by_cases hz : isZL C (.inl f) = true
    · simp only [baseD, baseN, hz, ↓reduceIte]
      split_ifs <;> omega
    · have hz' : isZL C (.inl f) = false := by simpa using hz
      have ht := hT _ hz'
      simp only [baseD, baseN, hz', ht, Bool.false_eq_true, ↓reduceIte]
      omega
  · simp only [baseD, baseN, hT (.inr g) rfl, Bool.false_eq_true, ↓reduceIte]
    omega

/-- **The expansion terms at three loops.** -/
theorem jef_nsLines3 (P : Params) (Φ : Lepton.Flavors F) (hε : 0 < P.ε)
    (hT : ∀ l, isZL C l = false → isTree C l = false) (cls : Line C → Fin m)
    (Es : List (Fin m → ℕ))
    (a' : Fin m → Fin 3 → ℤ) (hs : ∀ l, row3 C l = a' (cls l) ∨ row3 C l = -a' (cls l))
    (hEs : ∀ E ∈ Es, BasisCrit a' E 5)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (G : ZL C → List ℝ)
    (g : Line C → ℕ) (hG : ∀ x, (G x).length = 1 + g x.1)
    (hg : ∀ l, isZL C l = false → g l = 0)
    (hcrit : Pad3 cls Es (fun l => baseN C l + g l) (baseD C (nsE α β C))) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 3 fun ℓ =>
      z * ((∏ l, (nsNum P Φ C α β lor l (lineMomentum₂ C pOut pIn kIn ℓ l) *
        dProd P.ε (nsMs P Φ C l) (lineMomentum₂ C pOut pIn kIn ℓ l))) *
        ∏ x : ZL C, dProd P.ε (G x) (lineMomentum₂ C pOut pIn kIn ℓ x.1)) := by
  classical
  have hlen := congrFun (length_nsMs_zExt P Φ G g hG hg)
  have hc := basisCrit_of_pad3 hEs hcrit
  unfold mergedE at hc
  simp only [← hlen] at hc
  have h := jef_lines3 (row3 C) (extPart C pOut pIn kIn)
    (fun l => nsMs P Φ C l ++ zExt G l) (baseD C (nsE α β C)) (nsNum P Φ C α β lor)
    (affPoly_nsNum3 P Φ hT α β lor)
    (fun l => by
      rw [hlen]
      have := baseD_le hT (nsE α β C) l
      omega) a' cls hs hc hε z
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [← prod_nsNum_zExt P Φ α β lor G (fun l => lineMomentum₂ C pOut pIn kIn ℓ l)]
  simp only [lineMomentum₂_eq_rowMom3]

variable [Fintype F] [DecidableEq F]

/-- **One index term at three loops**, summed over the flavours of the closed loop. -/
theorem jef_nsTerm3 (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (hZ : ∀ x, isZ (zOf C) (C.1.1 x) = isZ (zOf C) x)
    (hr : (zSet C).card ≤ 4) (hT : ∀ l, isZL C l = false → isTree C l = false)
    (cls : Line C → Fin m)
    (Es : List (Fin m → ℕ)) (a' : Fin m → Fin 3 → ℤ)
    (hs : ∀ l, row3 C l = a' (cls l) ∨ row3 C l = -a' (cls l))
    (hEs : ∀ E ∈ Es, BasisCrit a' E 5) (hpat : AllPatOK3 C cls Es)
    (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 3 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * (z * ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn
        (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ α β lor) := by
  classical
  simp only [ampTerm_ns P Φ D hκ]
  set K := nsConst P C αOut βIn μ α β lor with hK
  by_cases hΓ : ∏ t, Wick.vertexFactor P.e 0 0 0 0 0 α β lor 0 0 t = 0
  · have h0 : K = 0 := by rw [hK, nsConst, hΓ, mul_zero]
    simp only [h0, zero_mul, mul_zero, Finset.sum_const_zero]
    exact jointEnergyFirstIntegrable_zero_fun'
  have hd := not_blk_of_prod_ne_zero P.e hκ α β lor hΓ
  obtain ⟨j, hj⟩ := even_nsP α β hZ hd
  have hcard := card_zSet_eq (C := C) α β
  have hpE : (zSet C).card - (nsE α β C).card = nsP α β C := by omega
  have hpat' := hpat (nsE α β C) (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
  unfold PatOK3 at hpat'
  rw [hpE] at hpat'
  obtain ⟨h4, h2, h0⟩ := hpat'
  have multi : ∀ i, (i = 0 ∨ i = 1) → j = i →
      TwoOK3 C cls Es (nsE α β C) ∧ SetOK3 C cls Es (nsE α β C) := by
    rintro i (rfl | rfl) rfl
    · exact h0 (by omega)
    · exact (h2 (by omega)).2
  set k : ZL C → (Fin 3 → Fin 4 → ℝ) → Fin 4 → ℝ :=
    fun x ℓ => lineMomentum₂ C pOut pIn kIn ℓ x.1 with hk
  set W : (Fin 3 → Fin 4 → ℝ) → ℂ := fun ℓ =>
    ∏ l, (nsNum P Φ C α β lor l (lineMomentum₂ C pOut pIn kIn ℓ l) *
      dProd P.ε (nsMs P Φ C l) (lineMomentum₂ C pOut pIn kIn ℓ l)) with hW
  set E : ℕ → F → (Fin 3 → Fin 4 → ℝ) → ℂ := fun i _ ℓ => if j = i then z * K * W ℓ else 0
    with hE
  have hL := fun G g hG hg hcrit z' =>
    jef_nsLines3 P Φ hε hT cls Es a' hs hEs α β lor pOut pIn kIn (C := C) G g hG hg hcrit z'
  have hzero : ∀ i, ¬ j = i → ∀ X : (Fin 3 → Fin 4 → ℝ) → ℂ, ∀ b (z' : ℂ),
      QED.TwoLoop.jointEnergyFirstIntegrable 3 fun ℓ => z' * (E i b ℓ * X ℓ) := by
    intro i hi X b z'
    simp only [hE, hi, ↓reduceIte, zero_mul, mul_zero]
    exact jointEnergyFirstIntegrable_zero_fun'
  have hmemZ : ∀ x : ZL C, x.1 ∈ zSet C := fun x => by
    simp only [zSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.2
  have hgZ : ∀ (x : ZL C) (c : ℕ) (l : Line C), isZL C l = false →
      (if l = x.1 then c else 0) = 0 := fun x c l hl => by
    refine ite_eq_right_iff.mpr fun h => ?_
    rw [h, x.2] at hl
    exact Bool.noConfusion hl
  -- two extra lines on one loop line
  have key₀₁ : ∀ i, (j = i → TwoOK3 C cls Es (nsE α β C) ∧ SetOK3 C cls Es (nsE α β C)) →
      ∀ b (M : ℝ) (z' : ℂ) (l : ZL C),
      QED.TwoLoop.jointEnergyFirstIntegrable 3 fun ℓ =>
        z' * (E i b ℓ * ((∏ l', (propDenom 0 P.ε (k l' ℓ))⁻¹) * (propDenom 0 P.ε (k l ℓ))⁻¹ *
          (propDenom M P.ε (k l ℓ))⁻¹)) := by
    intro i hi b M z' l
    by_cases hji : j = i
    · have h := hL (fun x => 0 :: (if x = l then [0, M] else []))
        (fun l' => if l' = l.1 then 2 else 0)
        (fun x => by
          by_cases hx : x = l
          · subst hx
            simp
          · have hx' : x.1 ≠ l.1 := fun h => hx (Subtype.ext h)
            simp [hx, hx'])
        (hgZ l 2) ((hi hji).1 l.1 (hmemZ l)) (z' * (z * K))
      refine (congrArg _ (funext fun ℓ => ?_)).mp h
      rw [prod_dProd_one P.ε (fun x => k x ℓ) l [0, M]]
      simp only [hE, hji, ↓reduceIte, dProd_cons, dProd_nil, mul_one, hk]
      ring
    · exact hzero i hji _ b z'
  -- one extra line on each loop line of `S`
  have keyS : ∀ i, (j = i → TwoOK3 C cls Es (nsE α β C) ∧ SetOK3 C cls Es (nsE α β C)) →
      ∀ b (M : ℝ) (z' : ℂ) (S : Finset (ZL C)),
      2 ≤ S.card → QED.TwoLoop.jointEnergyFirstIntegrable 3 fun ℓ =>
        z' * (E i b ℓ * ((∏ l', (propDenom 0 P.ε (k l' ℓ))⁻¹) *
          ∏ l ∈ S, (propDenom M P.ε (k l ℓ))⁻¹)) := by
    intro i hi b M z' S hS
    by_cases hji : j = i
    · set S' := S.map (Function.Embedding.subtype fun l => isZL C l = true) with hS'
      have hmem : ∀ x : ZL C, x.1 ∈ S' ↔ x ∈ S := fun x =>
        Finset.mem_map' (Function.Embedding.subtype fun l => isZL C l = true)
      have h := hL (fun x => 0 :: (if x ∈ S then [M] else []))
        (fun l' => if l' ∈ S' then 1 else 0)
        (fun x => by by_cases hx : x ∈ S <;> simp [hx, hmem])
        (fun l' hl' => by
          refine ite_eq_right_iff.mpr fun hm => ?_
          obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hm
          simp only [Function.Embedding.coe_subtype, x.2, Bool.true_eq_false] at hl')
        ((hi hji).2 S' (Finset.mem_powerset.mpr fun l hl => by
            obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hl
            exact hmemZ x)
          (by rw [hS', Finset.card_map]; exact hS)) (z' * (z * K))
      refine (congrArg _ (funext fun ℓ => ?_)).mp h
      rw [prod_dProd_set P.ε M (fun x => k x ℓ) S]
      simp only [hE, hji, ↓reduceIte, hk]
      ring
    · exact hzero i hji _ b z'
  have h := jointEnergyFirstIntegrable_blockSumGen Φ rep hrep hPV₁ hPV₂ k hε (E 0) (E 1) (E 2)
    (fun b M z' => by
      by_cases hj2 : j = 2
      · have h := hL (fun _ => [M]) (fun _ => 0) (fun _ => rfl) (fun _ _ => rfl)
          (by simp only [add_zero]; exact h4 (by omega)) (z' * (z * K))
        refine (congrArg _ (funext fun ℓ => ?_)).mp h
        simp only [hE, hj2, ↓reduceIte, dProd_cons, dProd_nil, mul_one, hk]
        ring
      · exact hzero 2 hj2 _ b z')
    (fun b z' l => by
      by_cases hj1 : j = 1
      · have h := hL (fun x => 0 :: (if x = l then [0] else []))
          (fun l' => if l' = l.1 then 1 else 0)
          (fun x => by
            by_cases hx : x = l
            · subst hx
              simp
            · have hx' : x.1 ≠ l.1 := fun h => hx (Subtype.ext h)
              simp [hx, hx'])
          (hgZ l 1) ((h2 (by omega)).1 l.1 (hmemZ l)) (z' * (z * K))
        refine (congrArg _ (funext fun ℓ => ?_)).mp h
        rw [prod_dProd_one P.ε (fun x => k x ℓ) l [0]]
        simp only [hE, hj1, ↓reduceIte, dProd_cons, dProd_nil, mul_one, hk]
        ring
      · exact hzero 1 hj1 _ b z')
    (fun E' hE' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hE'
      rcases hE' with rfl | rfl
      · exact key₀₁ 0 (multi 0 (Or.inl rfl))
      · exact key₀₁ 1 (multi 1 (Or.inr rfl)))
    (fun E' hE' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hE'
      rcases hE' with rfl | rfl
      · exact keyS 0 (multi 0 (Or.inl rfl))
      · exact keyS 1 (multi 1 (Or.inr rfl)))
  have hj2 : j ≤ 2 := by omega
  refine (congrArg _ (funext fun ℓ => Finset.sum_congr rfl fun f _ => ?_)).mp h
  rw [prod_nsFac P Φ hε.ne' α β lor (Φ.mass f) (fun l => lineMomentum₂ C pOut pIn kIn ℓ l), hj]
  interval_cases j <;> simp +decide only [hE, hk, hW, ↓reduceIte] <;> ring

/-- **(T₉′) for a three-loop contraction with one closed loop sharing lines with the other
loops**, at any masses. -/
theorem jef_nsClosed3 (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (C : Contraction 1 1 κ) (hL : loopCount C = 3)
    (hC : ClosedShape C (zOf C)) (hr : (zSet C).card ≤ 4)
    (hT : ∀ l, isZL C l = false → isTree C l = false)
    (cls : Line C → Fin m) (Es : List (Fin m → ℕ)) (a' : Fin m → Fin 3 → ℤ)
    (hs : ∀ l, row3 C l = a' (cls l) ∨ row3 C l = -a' (cls l))
    (hEs : ∀ E ∈ Es, BasisCrit a' E 5) (hpat : AllPatOK3 C cls Es)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) := by
  unfold integrand
  rw [hL]
  simp only [regulatedAmplitude_eq_closed Φ P D hC, contractionAmplitude_zero_eq]
  have h := jointEnergyFirstIntegrable_sum' Finset.univ fun α _ =>
    jointEnergyFirstIntegrable_sum' Finset.univ fun β _ =>
      jointEnergyFirstIntegrable_sum' Finset.univ fun lor _ =>
        jef_nsTerm3 P Φ D rep hrep hPV₁ hPV₂ hε hκ hC.inv hr hT cls Es a' hs hEs hpat pOut
          pIn kIn αOut βIn μ α β lor (((2 * Real.pi) ^ (4 * 3) : ℝ) : ℂ)⁻¹
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [sum_comm_four, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  ring

end QED.ChainProof.SetALinkV

end
