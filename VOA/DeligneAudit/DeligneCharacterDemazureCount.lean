/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterDemazure

/-!
# The `q = 1` Demazure count: `C_m(q = 1) = C_1(q = 1)^m`

At `q = 1` the affine Demazure operators of `demazureChar` become string operators on the group ring
`ℤ[ℤ^r]` of the root lattice:

* `D_i` (finite, `α_i`, pairing `⟨·, α_i^∨⟩`), and
* `D_0` (level one: `n = 1 - ⟨μ, θ^∨⟩`, string direction `+θ`, i.e. `α = -θ`).

Each satisfies the division formula `(1 - e^{-α}) D f = f - e^{-α} s^aff(f)` with an affine reflection
`s^aff` that is a twisted ring map over the linear reflection `s`: `s^aff(f g) = s(f) s^aff(g)`.  Since
`ℤ[ℤ^r]` is a domain, `D(f g) = f D(g)` whenever `s(f) = f` (`DR_mul_of_inv`).  Hence if
`χ = C_1(q = 1)` is invariant under all reflections of the word and under `s_θ`, then
`C_m(q = 1) = χ^m` (`toR1_demazureChar_pow`), and the total multiplicity is `(χ(1))^m`.

This is the character-level form of the Fourier–Littelmann factorisation
`D(1, mθ) ≅ D(1, θ)^{⊗m}` as `g`-modules, proved here from the Demazure algorithm itself.
-/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open AddMonoidAlgebra Finset

noncomputable section

variable {r : ℕ}

/-- Weights in simple-root coordinates. -/
abbrev Wt (r : ℕ) := Fin r → ℤ

/-- The group ring `ℤ[ℤ^r]` (characters at `q = 1`). -/
abbrev R1 (r : ℕ) := AddMonoidAlgebra ℤ (Wt r)

/-- `e^v`. -/
def mono (v : Wt r) : R1 r := single v 1

theorem mono_mul_mono (u v : Wt r) : mono u * mono v = mono (u + v) := by
  simp [mono, single_mul_single]

theorem mono_zero : (mono (0 : Wt r)) = 1 := rfl

/-- Reflection data: direction `α`, linear functional `p`, level shift `ℓ`;
the string length on `e^v` is `n(v) = ℓ + p v`. -/
structure RData (r : ℕ) where
  α : Wt r
  p : Wt r →+ ℤ
  ℓ : ℤ

namespace RData

variable (ρ : RData r)

def n (v : Wt r) : ℤ := ρ.ℓ + ρ.p v

/-- The linear reflection `v ↦ v - p(v) α`. -/
def lin : Wt r →+ Wt r where
  toFun v := v - ρ.p v • ρ.α
  map_zero' := by simp
  map_add' u v := by simp only [map_add, add_smul]; abel

theorem lin_apply (v : Wt r) : ρ.lin v = v - ρ.p v • ρ.α := rfl

/-- The affine reflection `v ↦ v - n(v) α`. -/
def aff (v : Wt r) : Wt r := v - ρ.n v • ρ.α

theorem aff_add (u v : Wt r) : ρ.aff (u + v) = ρ.lin u + ρ.aff v := by
  simp only [aff, lin_apply, n, map_add, add_smul]; abel

/-- The string formula on `e^v`. -/
def strD (v : Wt r) : R1 r :=
  if 0 ≤ ρ.n v then ∑ k ∈ range ((ρ.n v).toNat + 1), mono (v - (k : ℤ) • ρ.α)
  else -∑ k ∈ range ((-ρ.n v).toNat - 1), mono (v + ((k : ℤ) + 1) • ρ.α)

/-- The Demazure operator, extended linearly. -/
def DR : R1 r →ₗ[ℤ] R1 r := Finsupp.linearCombination ℤ ρ.strD

/-- The affine reflection on the group ring. -/
def sAff : R1 r →ₗ[ℤ] R1 r := Finsupp.lmapDomain ℤ ℤ ρ.aff

/-- The linear reflection as a ring map. -/
def sLin : R1 r →+* R1 r := AddMonoidAlgebra.mapDomainRingHom ℤ ρ.lin

theorem DR_single (v : Wt r) (c : ℤ) : ρ.DR (single v c) = c • ρ.strD v :=
  Finsupp.linearCombination_single ℤ c v

theorem sAff_single (v : Wt r) (c : ℤ) : ρ.sAff (single v c) = single (ρ.aff v) c :=
  Finsupp.mapDomain_single

theorem sLin_single (v : Wt r) (c : ℤ) : ρ.sLin (single v c) = single (ρ.lin v) c := by
  simp [sLin, AddMonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]

/-- Division formula on one monomial. -/
theorem div_strD (v : Wt r) :
    (1 - mono (-ρ.α)) * ρ.strD v = mono v - mono (-ρ.α) * mono (ρ.aff v) := by
  rw [mono_mul_mono, aff]
  unfold strD
  split_ifs with h
  · set N := (ρ.n v).toNat with hN
    have hn : ρ.n v = N := (Int.toNat_of_nonneg h).symm
    have key : ∀ M : ℕ, (1 - mono (-ρ.α)) * ∑ k ∈ range (M + 1), mono (v - (k : ℤ) • ρ.α) =
        mono v - mono (v - ((M : ℤ) + 1) • ρ.α) := by
      intro M
      induction M with
      | zero => simp [sub_mul, mono_mul_mono]; congr 1; abel_nf
      | succ M ih =>
        rw [sum_range_succ, mul_add, ih, sub_mul, one_mul, mono_mul_mono]
        push_cast
        have : -ρ.α + (v - ((M : ℤ) + 1) • ρ.α) = v - ((M : ℤ) + 1 + 1) • ρ.α := by
          simp only [add_smul, one_smul]; abel
        rw [this]; abel
    rw [key, hn]; congr 2; simp only [add_smul, one_smul, neg_smul]; abel
  · push_neg at h
    set M := (-ρ.n v).toNat - 1 with hM
    have hn : ρ.n v = -((M : ℤ) + 1) := by
      have h1 : ((-ρ.n v).toNat : ℤ) = -ρ.n v := Int.toNat_of_nonneg (by omega)
      have h2 : 1 ≤ (-ρ.n v).toNat := by omega
      rw [hM, Nat.cast_sub h2, h1]; push_cast; ring
    have key : ∀ K : ℕ, (1 - mono (-ρ.α)) * -∑ k ∈ range K, mono (v + ((k : ℤ) + 1) • ρ.α) =
        mono v - mono (v + (K : ℤ) • ρ.α) := by
      intro K
      induction K with
      | zero => simp
      | succ K ih =>
        rw [sum_range_succ, neg_add, mul_add, ih, mul_neg, sub_mul, one_mul, mono_mul_mono]
        push_cast
        have : -ρ.α + (v + ((K : ℤ) + 1) • ρ.α) = v + (K : ℤ) • ρ.α := by
          simp only [add_smul, one_smul]; abel
        rw [this]; abel
    rw [key, hn]; congr 2; simp only [add_smul, one_smul, neg_smul, neg_add, neg_neg]; abel

/-- **Division formula**: `(1 - e^{-α}) D f = f - e^{-α} s^aff(f)`. -/
theorem div_formula (f : R1 r) :
    (1 - mono (-ρ.α)) * ρ.DR f = f - mono (-ρ.α) * ρ.sAff f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, mul_add, hf, hg, map_add, mul_add]; abel
  | single v c =>
    rw [DR_single, sAff_single, mul_smul_comm, div_strD]
    have e1 : (single v c : R1 r) = c • mono v := by
      rw [mono]; exact (Finsupp.smul_single_one _ c).symm
    have e2 : (single (ρ.aff v) c : R1 r) = c • mono (ρ.aff v) := by
      rw [mono]; exact (Finsupp.smul_single_one _ c).symm
    rw [e1, e2]
    simp only [zsmul_eq_mul]
    ring

/-- `s^aff(f g) = s(f) s^aff(g)`. -/
theorem sAff_mul (f g : R1 r) : ρ.sAff (f * g) = ρ.sLin f * ρ.sAff g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
  | single u a =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
    | single w b =>
      rw [single_mul_single, sAff_single, sLin_single, sAff_single, single_mul_single, aff_add]

theorem one_sub_mono_ne_zero (hα : ρ.α ≠ 0) : (1 - mono (-ρ.α) : R1 r) ≠ 0 := by
  intro h
  have h1 : mono (-ρ.α) = (mono 0 : R1 r) := by rw [mono_zero]; exact (sub_eq_zero.mp h).symm
  have : -ρ.α = 0 := Finsupp.single_left_injective one_ne_zero h1
  exact hα (neg_eq_zero.mp this)

/-- **Twisted Leibniz**: `D(f g) = f D(g)` when `s(f) = f`. -/
theorem DR_mul_of_inv (hα : ρ.α ≠ 0) (f g : R1 r) (hf : ρ.sLin f = f) :
    ρ.DR (f * g) = f * ρ.DR g := by
  apply mul_left_cancel₀ (ρ.one_sub_mono_ne_zero hα)
  rw [div_formula, sAff_mul, hf, mul_left_comm (1 - mono (-ρ.α)) f, div_formula]
  ring

end RData

/-! ## Iteration -/

/-- One step `D_{i₁} ⋯ D_{i_L} D_0` (the `foldr` shape of `demazureStep`). -/
def stepR (ρs : List (RData r)) (ρ0 : RData r) (f : R1 r) : R1 r :=
  ρs.foldr (fun ρ g => ρ.DR g) (ρ0.DR f)

theorem stepR_mul_of_inv (ρs : List (RData r)) (ρ0 : RData r) (f g : R1 r)
    (hα : ∀ ρ ∈ ρ0 :: ρs, ρ.α ≠ 0)
    (hf : ∀ ρ ∈ ρ0 :: ρs, ρ.sLin f = f) : stepR ρs ρ0 (f * g) = f * stepR ρs ρ0 g := by
  induction ρs with
  | nil => exact ρ0.DR_mul_of_inv (hα ρ0 (by simp)) f g (hf ρ0 (by simp))
  | cons ρ ρs ih =>
    simp only [stepR, List.foldr_cons] at ih ⊢
    rw [ih (fun σ hσ => hα σ (by simp at hσ ⊢; tauto)) (fun σ hσ => hf σ (by simp at hσ ⊢; tauto))]
    exact ρ.DR_mul_of_inv (hα ρ (by simp)) f _ (hf ρ (by simp))

/-- **The `q = 1` factorisation**: `step^m(1) = (step 1)^m` when `step 1` is invariant. -/
theorem stepR_iterate (ρs : List (RData r)) (ρ0 : RData r)
    (hα : ∀ ρ ∈ ρ0 :: ρs, ρ.α ≠ 0)
    (hinv : ∀ ρ ∈ ρ0 :: ρs, ρ.sLin (stepR ρs ρ0 1) = stepR ρs ρ0 1) (m : ℕ) :
    (stepR ρs ρ0)^[m] 1 = (stepR ρs ρ0 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    have h := stepR_mul_of_inv ρs ρ0 ((stepR ρs ρ0 1) ^ m) 1 hα
      (fun ρ hρ => by rw [map_pow, hinv ρ hρ])
    rw [mul_one] at h
    rw [h, pow_succ]

/-! ## Bridge from the list algorithm `demazureChar` -/

open VOA.DeligneAudit.DeligneCharacter (Term LPoly addTerm normalize pairCoroot shiftAt shiftTheta
  demazureFinTerm demazureZeroTerm demazureFin demazureZero demazureStep demazureChar)

/-- Root coordinates of a weight list. -/
def vec (r : ℕ) (l : List ℤ) : Wt r := fun j => l.getD j 0

/-- `q = 1` specialisation of a term list. -/
def toR1 (r : ℕ) (f : LPoly) : R1 r := (f.map fun t => single (vec r t.1.1) t.2).sum

theorem single_eq_smul_mono (v : Wt r) (c : ℤ) : (single v c : R1 r) = c • mono v := by
  rw [mono]; exact (Finsupp.smul_single_one _ c).symm

theorem toR1_nil : toR1 r [] = 0 := rfl

theorem toR1_cons (t : Term) (f : LPoly) :
    toR1 r (t :: f) = single (vec r t.1.1) t.2 + toR1 r f := by
  simp [toR1]

theorem toR1_append (f g : LPoly) : toR1 r (f ++ g) = toR1 r f + toR1 r g := by
  simp [toR1]

theorem toR1_flatMap (f : LPoly) (g : Term → LPoly) :
    toR1 r (f.flatMap g) = (f.map fun t => toR1 r (g t)).sum := by
  induction f with
  | nil => rfl
  | cons t f ih => rw [List.flatMap_cons, toR1_append, ih, List.map_cons, List.sum_cons]

theorem toR1_addTerm (t : Term) (g : LPoly) :
    toR1 r (addTerm t g) = single (vec r t.1.1) t.2 + toR1 r g := by
  induction g with
  | nil => simp [addTerm, toR1]
  | cons s g ih =>
    unfold addTerm
    split_ifs with h
    · rw [toR1_cons, toR1_cons, h]
      simp only
      rw [single_eq_smul_mono, single_eq_smul_mono, single_eq_smul_mono, add_smul]; abel
    · rw [toR1_cons, ih, toR1_cons]; abel

theorem toR1_foldr (f : LPoly) : toR1 r (f.foldr addTerm []) = toR1 r f := by
  induction f with
  | nil => rfl
  | cons t f ih => rw [List.foldr_cons, toR1_addTerm, ih, toR1_cons]

theorem toR1_filter (g : LPoly) : toR1 r (g.filter fun t => t.2 ≠ 0) = toR1 r g := by
  induction g with
  | nil => rfl
  | cons t g ih =>
    rw [List.filter_cons]
    split_ifs with h
    · rw [toR1_cons, ih, toR1_cons]
    · simp only [decide_eq_true_eq, not_not] at h
      rw [ih, toR1_cons, h, single_eq_smul_mono, zero_smul, zero_add]

theorem toR1_normalize (f : LPoly) : toR1 r (normalize f) = toR1 r f := by
  rw [normalize, toR1_filter, toR1_foldr]

theorem toR1_map_range (N : ℕ) (g : ℕ → Term) :
    toR1 r ((List.range N).map g) = ∑ k ∈ range N, single (vec r (g k).1.1) (g k).2 := by
  induction N with
  | zero => rfl
  | succ N ih => rw [List.range_succ, List.map_append, toR1_append, ih, sum_range_succ]; simp [toR1]

/-! ### Lists of the right length -/

/-- All weights have length `r`. -/
def Good (r : ℕ) (f : LPoly) : Prop := ∀ t ∈ f, t.1.1.length = r

theorem mem_addTerm (t : Term) (g : LPoly) (x : Term) (hx : x ∈ addTerm t g) :
    x.1 = t.1 ∨ x ∈ g := by
  induction g with
  | nil => simp [addTerm] at hx; left; rw [hx]
  | cons s g ih =>
    unfold addTerm at hx
    split_ifs at hx with h
    · rcases List.mem_cons.mp hx with rfl | hx
      · left; rfl
      · right; exact List.mem_cons_of_mem _ hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · right; exact List.mem_cons_self
      · rcases ih hx with h' | h'
        · left; exact h'
        · right; exact List.mem_cons_of_mem _ h'

theorem Good_normalize (f : LPoly) (hf : Good r f) : Good r (normalize f) := by
  have key : ∀ f : LPoly, Good r f → Good r (f.foldr addTerm []) := by
    intro f hf
    induction f with
    | nil => intro t ht; simp at ht
    | cons s f ih =>
      intro x hx
      rw [List.foldr_cons] at hx
      rcases mem_addTerm _ _ _ hx with h | h
      · rw [h]; exact hf s List.mem_cons_self
      · exact ih (fun t ht => hf t (List.mem_cons_of_mem _ ht)) x h
  intro t ht
  exact key f hf t (List.mem_filter.mp ht).1

theorem vec_injective (l l' : List ℤ) (hl : l.length = r) (hl' : l'.length = r)
    (h : vec r l = vec r l') : l = l' := by
  apply List.ext_getElem (hl.trans hl'.symm)
  intro j h1 h2
  have := congrFun h ⟨j, hl ▸ h1⟩
  simp only [vec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at this
  exact this

/-! ### The operators on lists -/

theorem sum_zipWith_mul (l1 l2 : List ℤ) :
    (List.zipWith (· * ·) l1 l2).sum = ∑ j ∈ range l2.length, l1.getD j 0 * l2.getD j 0 := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons a l1 ih =>
    cases l2 with
    | nil => simp
    | cons b l2 => rw [List.zipWith_cons_cons, List.sum_cons, ih, List.length_cons,
        sum_range_succ']; simp; ring

theorem sum_range_eq_fin (l1 l2 : List ℤ) (hl : l2.length = r) :
    ∑ j ∈ range l2.length, l1.getD j 0 * l2.getD j 0 = ∑ j : Fin r, l1.getD j 0 * vec r l2 j := by
  rw [hl, ← Fin.sum_univ_eq_sum_range]; rfl

/-- `⟨·, α_i^∨⟩` from the Cartan row. -/
def pFin (A : List (List ℤ)) (i : ℕ) : Wt r →+ ℤ where
  toFun v := ∑ j : Fin r, (A.getD i []).getD j 0 * v j
  map_zero' := by simp
  map_add' u v := by simp [mul_add, sum_add_distrib]

/-- `e_i` (zero if `i ≥ r`). -/
def eAt (r i : ℕ) : Wt r := fun j => if (j : ℕ) = i then 1 else 0

/-- The finite reflection data `D_i`. -/
def ρFin (A : List (List ℤ)) (i : ℕ) : RData r := ⟨eAt r i, pFin A i, 0⟩

/-- `Aθ` as in `demazureZeroTerm`. -/
def aTheta (A : List (List ℤ)) (θ : List ℤ) : List ℤ :=
  (List.range θ.length).map fun i => pairCoroot A i θ

/-- The level-one affine data `D_0`: `α = -θ`, `p = -⟨·, θ∨⟩`, `ℓ = 1`. -/
def ρZero (A : List (List ℤ)) (θ : List ℤ) : RData r where
  α := -vec r θ
  p := -{ toFun := fun v => ∑ j : Fin r, (aTheta A θ).getD j 0 * v j
          map_zero' := by simp
          map_add' := fun u v => by simp [mul_add, sum_add_distrib] }
  ℓ := 1

theorem pairCoroot_eq (A : List (List ℤ)) (i : ℕ) (μ : List ℤ) (hμ : μ.length = r) :
    pairCoroot A i μ = pFin A i (vec r μ) := by
  rw [pairCoroot, sum_zipWith_mul, sum_range_eq_fin _ _ hμ]; rfl

theorem vec_shiftAt (μ : List ℤ) (hμ : μ.length = r) (i : ℕ) (c : ℤ) :
    vec r (shiftAt μ i c) = vec r μ + c • eAt r i := by
  funext j
  have hj : (j : ℕ) < μ.length := hμ ▸ j.2
  simp only [vec, shiftAt, eAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    List.getD_eq_getElem?_getD, List.getElem?_mapIdx, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some]
  split_ifs <;> ring

theorem vec_shiftTheta (μ θ : List ℤ) (hμ : μ.length = r) (hθ : θ.length = r) (c : ℤ) :
    vec r (shiftTheta μ θ c) = vec r μ + c • vec r θ := by
  funext j
  have hj : (j : ℕ) < μ.length := hμ ▸ j.2
  have hj' : (j : ℕ) < θ.length := hθ ▸ j.2
  simp only [vec, shiftTheta, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hj', Option.map₂_some_some, Option.getD_some]

theorem toR1_demazureFinTerm (A : List (List ℤ)) (i : ℕ) (t : Term) (ht : t.1.1.length = r) :
    toR1 r (demazureFinTerm A i t) = (ρFin A i).DR (single (vec r t.1.1) t.2) := by
  rw [RData.DR_single]
  unfold demazureFinTerm RData.strD
  simp only [RData.n, ρFin, zero_add, ← pairCoroot_eq A i _ ht]
  split_ifs with h
  · rw [toR1_map_range]
    simp only [zsmul_eq_mul, Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [vec_shiftAt _ ht, single_eq_smul_mono, zsmul_eq_mul]
    congr 2; simp [sub_eq_add_neg, neg_smul]
  · rw [toR1_map_range]
    simp only [zsmul_eq_mul, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [vec_shiftAt _ ht, single_eq_smul_mono, zsmul_eq_mul, Int.cast_neg, neg_mul]
    simp [zsmul_eq_mul]

theorem toR1_demazureZeroTerm (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r) (t : Term)
    (ht : t.1.1.length = r) :
    toR1 r (demazureZeroTerm A θ t) = (ρZero A θ).DR (single (vec r t.1.1) t.2) := by
  rw [RData.DR_single]
  unfold demazureZeroTerm RData.strD
  have hn : 1 - (List.zipWith (· * ·) ((List.range θ.length).map fun i => pairCoroot A i θ)
      t.1.1).sum = (ρZero A θ).n (vec r t.1.1) := by
    rw [RData.n, sum_zipWith_mul, sum_range_eq_fin _ _ ht]
    simp [ρZero, aTheta, sub_eq_add_neg]
  simp only [hn]
  split_ifs with h
  · rw [toR1_map_range]
    simp only [zsmul_eq_mul, Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [vec_shiftTheta _ _ ht hθ, single_eq_smul_mono, zsmul_eq_mul]
    congr 2; simp [ρZero, sub_eq_add_neg]
  · rw [toR1_map_range]
    simp only [zsmul_eq_mul, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [vec_shiftTheta _ _ ht hθ, single_eq_smul_mono, zsmul_eq_mul, Int.cast_neg, neg_mul]
    congr 3; simp [ρZero, sub_eq_add_neg]; ring

theorem toR1_single_eq (f : LPoly) :
    toR1 r f = (f.map fun t => (single (vec r t.1.1) t.2 : R1 r)).sum := rfl

theorem Good_flatMap_fin (A : List (List ℤ)) (i : ℕ) (f : LPoly) (hf : Good r f) :
    Good r (f.flatMap (demazureFinTerm A i)) := by
  intro x hx
  obtain ⟨t, ht, hx⟩ := List.mem_flatMap.mp hx
  unfold demazureFinTerm at hx
  dsimp only at hx
  split_ifs at hx <;>
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    simp [shiftAt, hf t ht]

theorem Good_flatMap_zero (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r) (f : LPoly)
    (hf : Good r f) : Good r (f.flatMap (demazureZeroTerm A θ)) := by
  intro x hx
  obtain ⟨t, ht, hx⟩ := List.mem_flatMap.mp hx
  unfold demazureZeroTerm at hx
  dsimp only at hx
  split_ifs at hx <;>
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    simp [shiftTheta, hf t ht, hθ]

theorem toR1_eq_sum_single (f : LPoly) :
    toR1 r f = (f.map fun t => (single (vec r t.1.1) t.2 : R1 r)).sum := rfl

theorem toR1_demazureFin (A : List (List ℤ)) (i : ℕ) (f : LPoly) (hf : Good r f) :
    toR1 r (demazureFin A i f) = (ρFin A i).DR (toR1 r f) ∧ Good r (demazureFin A i f) := by
  refine ⟨?_, Good_normalize _ (Good_flatMap_fin A i f hf)⟩
  rw [demazureFin, toR1_normalize, toR1_flatMap, toR1_eq_sum_single f, map_list_sum,
    List.map_map]
  congr 1
  exact List.map_congr_left fun t ht => toR1_demazureFinTerm A i t (hf t ht)

theorem toR1_demazureZero (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r) (f : LPoly)
    (hf : Good r f) :
    toR1 r (demazureZero A θ f) = (ρZero A θ).DR (toR1 r f) ∧ Good r (demazureZero A θ f) := by
  refine ⟨?_, Good_normalize _ (Good_flatMap_zero A θ hθ f hf)⟩
  rw [demazureZero, toR1_normalize, toR1_flatMap, toR1_eq_sum_single f, map_list_sum,
    List.map_map]
  congr 1
  exact List.map_congr_left fun t ht => toR1_demazureZeroTerm A θ hθ t (hf t ht)

theorem toR1_demazureStep (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r) (word : List ℕ)
    (f : LPoly) (hf : Good r f) :
    toR1 r (demazureStep A θ word f) = stepR (word.map (ρFin A)) (ρZero A θ) (toR1 r f) ∧
      Good r (demazureStep A θ word f) := by
  unfold demazureStep stepR
  induction word with
  | nil => simpa using toR1_demazureZero A θ hθ f hf
  | cons i word ih =>
    simp only [List.foldr_cons, List.map_cons]
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := toR1_demazureFin A i _ h2
    exact ⟨h3.trans (by rw [h1]), h4⟩

theorem toR1_demazureChar (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r) (word : List ℕ)
    (m : ℕ) :
    toR1 r (demazureChar A θ word m) = (stepR (word.map (ρFin A)) (ρZero A θ))^[m] 1 ∧
      Good r (demazureChar A θ word m) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [demazureChar, Function.iterate_zero, id, toR1_cons, toR1_nil, add_zero]
      have : vec r (List.replicate θ.length 0) = 0 := by
        funext j; simp [vec, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> rfl
      rw [this]; rfl
    · intro t ht; simp [demazureChar] at ht; rw [ht]; simp [hθ]
  | succ m ih =>
    have e : demazureChar A θ word (m + 1) = demazureStep A θ word (demazureChar A θ word m) := by
      simp only [demazureChar, Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := toR1_demazureStep A θ hθ word _ ih.2
    rw [e]
    exact ⟨h1.trans (by rw [ih.1, Function.iterate_succ_apply']), h2⟩

/-! ## The count -/

/-- Augmentation `e^v ↦ 1`. -/
def aug : R1 r →+* ℤ := (AddMonoidAlgebra.lift ℤ ℤ (Wt r) 1).toRingHom

theorem aug_single (v : Wt r) (c : ℤ) : aug (single v c : R1 r) = c := by
  simp [aug, AddMonoidAlgebra.lift_single]

theorem aug_toR1 (f : LPoly) : aug (toR1 r f) = (f.map (·.2)).sum := by
  induction f with
  | nil => simp [toR1_nil]
  | cons t f ih => rw [toR1_cons, map_add, aug_single, ih, List.map_cons, List.sum_cons]

/-- **Generic `q = 1` factorisation of `demazureChar`.** -/
theorem toR1_demazureChar_pow (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r)
    (word : List ℕ)
    (hα : ∀ ρ ∈ ρZero (r := r) A θ :: word.map (ρFin A), ρ.α ≠ 0)
    (hinv : ∀ ρ ∈ ρZero (r := r) A θ :: word.map (ρFin A),
      ρ.sLin (toR1 r (demazureChar A θ word 1)) = toR1 r (demazureChar A θ word 1)) (m : ℕ) :
    toR1 r (demazureChar A θ word m) = (toR1 r (demazureChar A θ word 1)) ^ m := by
  have h1 := (toR1_demazureChar A θ hθ word 1).1
  simp only [Function.iterate_one] at h1
  rw [(toR1_demazureChar A θ hθ word m).1, h1]
  rw [h1] at hinv
  exact stepR_iterate _ _ hα hinv m

/-- **The total multiplicity** `C_m(1) = C_1(1)^m`. -/
theorem demazureChar_total (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r)
    (word : List ℕ)
    (hα : ∀ ρ ∈ ρZero (r := r) A θ :: word.map (ρFin A), ρ.α ≠ 0)
    (hinv : ∀ ρ ∈ ρZero (r := r) A θ :: word.map (ρFin A),
      ρ.sLin (toR1 r (demazureChar A θ word 1)) = toR1 r (demazureChar A θ word 1)) (m : ℕ) :
    ((demazureChar A θ word m).map (·.2)).sum = (((demazureChar A θ word 1).map (·.2)).sum) ^ m := by
  rw [← aug_toR1, ← aug_toR1, toR1_demazureChar_pow A θ hθ word hα hinv m, map_pow]

/-! ## A computable invariance criterion -/

theorem toR1_apply (f : LPoly) (w : Wt r) :
    (toR1 r f : Wt r →₀ ℤ) w = ((f.filter fun s => decide (vec r s.1.1 = w)).map (·.2)).sum := by
  induction f with
  | nil => rfl
  | cons t f ih =>
    rw [toR1_cons]
    erw [Finsupp.add_apply]
    rw [ih, List.filter_cons]
    by_cases h : vec r t.1.1 = w
    · simp [h, AddMonoidAlgebra.single, Finsupp.single_apply]
    · simp [h, AddMonoidAlgebra.single, Finsupp.single_apply]

/-- `∑` of the coefficients of `f` at the weight list `μ`. -/
def cnt (f : LPoly) (μ : List ℤ) : ℤ := ((f.filter fun s => decide (s.1.1 = μ)).map (·.2)).sum

/-- The decidable check `toR1 f = toR1 g`. -/
def sameChar (f g : LPoly) : Bool := (f ++ g).all fun t => decide (cnt f t.1.1 = cnt g t.1.1)

theorem cnt_eq_apply (f : LPoly) (hf : Good r f) (μ : List ℤ) (hμ : μ.length = r) :
    cnt f μ = (toR1 r f : Wt r →₀ ℤ) (vec r μ) := by
  rw [toR1_apply, cnt]
  congr 2
  apply List.filter_congr
  intro s hs
  simp only [decide_eq_decide]
  exact ⟨fun h => h ▸ rfl, fun h => vec_injective _ _ (hf s hs) hμ h⟩

theorem toR1_eq_of_sameChar (f g : LPoly) (hf : Good r f) (hg : Good r g)
    (h : sameChar f g = true) : toR1 r f = toR1 r g := by
  apply Finsupp.ext
  intro w
  by_cases hw : ∃ t ∈ f ++ g, vec r t.1.1 = w
  · obtain ⟨t, ht, rfl⟩ := hw
    have hlen : t.1.1.length = r := by
      rcases List.mem_append.mp ht with ht | ht
      · exact hf t ht
      · exact hg t ht
    have := List.all_eq_true.mp h t ht
    simp only [decide_eq_true_eq] at this
    rw [← cnt_eq_apply f hf _ hlen, ← cnt_eq_apply g hg _ hlen, this]
  · push_neg at hw
    rw [toR1_apply, toR1_apply]
    rw [List.filter_eq_nil_iff.mpr, List.filter_eq_nil_iff.mpr]
    · intro s hs; simpa using hw s (List.mem_append_right _ hs)
    · intro s hs; simpa using hw s (List.mem_append_left _ hs)

/-- The reflection `lin` of `ρFin A i` on weight lists. -/
def reflFin (A : List (List ℤ)) (i : ℕ) (μ : List ℤ) : List ℤ := shiftAt μ i (-pairCoroot A i μ)

/-- The reflection `lin` of `ρZero A θ` on weight lists. -/
def reflZero (A : List (List ℤ)) (θ : List ℤ) (μ : List ℤ) : List ℤ :=
  shiftTheta μ θ (-(List.zipWith (· * ·) (aTheta A θ) μ).sum)

def mapW (g : List ℤ → List ℤ) (f : LPoly) : LPoly := f.map fun t => ((g t.1.1, t.1.2), t.2)

theorem sLin_toR1 (ρ : RData r) (g : List ℤ → List ℤ) (f : LPoly) (hf : Good r f)
    (hg : ∀ μ : List ℤ, μ.length = r → vec r (g μ) = ρ.lin (vec r μ)) :
    ρ.sLin (toR1 r f) = toR1 r (mapW g f) := by
  rw [toR1_eq_sum_single, map_list_sum, List.map_map, mapW, toR1_eq_sum_single, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp, RData.sLin_single, hg _ (hf t ht)]

theorem vec_reflFin (A : List (List ℤ)) (i : ℕ) (μ : List ℤ) (hμ : μ.length = r) :
    vec r (reflFin A i μ) = (ρFin A i).lin (vec r μ) := by
  rw [reflFin, vec_shiftAt _ hμ, RData.lin_apply, pairCoroot_eq A i μ hμ]
  simp [ρFin, sub_eq_add_neg, neg_smul]

theorem vec_reflZero (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r) (μ : List ℤ)
    (hμ : μ.length = r) :
    vec r (reflZero A θ μ) = (ρZero A θ).lin (vec r μ) := by
  rw [reflZero, vec_shiftTheta _ _ hμ hθ, RData.lin_apply, sum_zipWith_mul,
    sum_range_eq_fin _ _ hμ]
  simp [ρZero, sub_eq_add_neg, neg_smul, smul_neg]

theorem Good_mapW (g : List ℤ → List ℤ) (f : LPoly) (hg : ∀ μ : List ℤ, μ.length = r → (g μ).length = r)
    (hf : Good r f) : Good r (mapW g f) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hg _ (hf s hs)

/-- **Decidable form of the invariance hypothesis.** -/
def invCheck (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ) (f : LPoly) : Bool :=
  sameChar (mapW (reflZero A θ) f) f && word.all fun i => sameChar (mapW (reflFin A i) f) f

theorem inv_of_invCheck (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r) (word : List ℕ)
    (f : LPoly) (hf : Good r f) (h : invCheck A θ word f = true) :
    ∀ ρ ∈ ρZero (r := r) A θ :: word.map (ρFin A), ρ.sLin (toR1 r f) = toR1 r f := by
  simp only [invCheck, Bool.and_eq_true, List.all_eq_true] at h
  have hlenF : ∀ i (μ : List ℤ), μ.length = r → (reflFin A i μ).length = r := by
    intro i μ hμ; simp [reflFin, shiftAt, hμ]
  have hlenZ : ∀ μ : List ℤ, μ.length = r → (reflZero A θ μ).length = r := by
    intro μ hμ; simp [reflZero, shiftTheta, hμ, hθ]
  intro ρ hρ
  rcases List.mem_cons.mp hρ with rfl | hρ
  · rw [sLin_toR1 _ _ f hf (fun μ hμ => vec_reflZero A θ hθ μ hμ)]
    exact toR1_eq_of_sameChar _ _ (Good_mapW _ _ hlenZ hf) hf h.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hρ
    rw [sLin_toR1 _ _ f hf (fun μ hμ => vec_reflFin A i μ hμ)]
    exact toR1_eq_of_sameChar _ _ (Good_mapW _ _ (hlenF i) hf) hf (h.2 i hi)

/-- `α ≠ 0` for the data, decidably. -/
theorem alpha_ne_zero_of (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ)
    (hw : ∀ i ∈ word, i < r) (hθ0 : ∃ j : Fin r, θ.getD j 0 ≠ 0) :
    ∀ ρ ∈ ρZero (r := r) A θ :: word.map (ρFin A), ρ.α ≠ 0 := by
  intro ρ hρ
  rcases List.mem_cons.mp hρ with rfl | hρ
  · obtain ⟨j, hj⟩ := hθ0
    intro h
    have := congrFun h j
    simp [ρZero, vec] at this
    exact hj this
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hρ
    intro h
    have := congrFun h ⟨i, hw i hi⟩
    simp [ρFin, eAt] at this

/-! ## From the total to the graded count -/

/-- `[q^N]` of `q^{m²} C_m|_{z=1}` over `ℤ` (unclamped). -/
def hilbIntG (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ) (m : ℕ) (N : ℤ) : ℤ :=
  (((demazureChar A θ word m).filter fun (t : Term) => decide (t.1.2 + (m : ℤ) * m = N)).map
    fun (t : Term) => t.2).sum

theorem levelOneDemazureHilb_eq (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ) (m N : ℕ) :
    DeligneCharacter.levelOneDemazureHilb A θ word m N = (hilbIntG A θ word m N).toNat := rfl

theorem sum_filter_energy (L : LPoly) (e : Term → ℤ) (B : ℕ)
    (he : ∀ t ∈ L, 0 ≤ e t ∧ e t < B) :
    ∑ N ∈ range B, ((L.filter fun t => decide (e t = N)).map (·.2)).sum = (L.map (·.2)).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have ih' := ih (fun s hs => he s (List.mem_cons_of_mem _ hs))
    obtain ⟨h0, h1⟩ := he t List.mem_cons_self
    have hsplit : ∀ N : ℕ, ((List.filter (fun s => decide (e s = N)) (t :: L)).map (·.2)).sum =
        (if (e t).toNat = N then t.2 else 0) +
          ((L.filter fun s => decide (e s = N)).map (·.2)).sum := by
      intro N
      have hiff : (e t = (N : ℤ)) ↔ (e t).toNat = N := by omega
      by_cases h : (e t).toNat = N
      · rw [List.filter_cons_of_pos (by simpa [hiff] using h), List.map_cons, List.sum_cons,
          if_pos h]
      · rw [List.filter_cons_of_neg (by simpa [hiff] using h), if_neg h, zero_add]
    rw [sum_congr rfl fun N _ => hsplit N, sum_add_distrib, ih', sum_ite_eq, if_pos (by
      rw [mem_range]; omega), List.map_cons, List.sum_cons]

/-- **Graded count from the total** (`hilbIntG` summed over `N`), given nonnegative energies. -/
theorem hilbIntG_count (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ) (m : ℕ)
    (henergy : ∀ t ∈ demazureChar A θ word m, 0 ≤ t.1.2 + (m : ℤ) * m) :
    ∃ B, (∀ N : ℕ, B ≤ N → hilbIntG A θ word m N = 0) ∧
      ∑ N ∈ range B, hilbIntG A θ word m N = ((demazureChar A θ word m).map (·.2)).sum := by
  set L := demazureChar A θ word m
  let B := (L.map fun t => (t.1.2 + (m : ℤ) * m).toNat + 1).sum
  have hB : ∀ t ∈ L, (t.1.2 + (m : ℤ) * m) < B := by
    intro t ht
    have : (t.1.2 + (m : ℤ) * m).toNat + 1 ≤ B :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩)
    have h0 := henergy t ht
    omega
  refine ⟨B, fun N hN => ?_, ?_⟩
  · rw [hilbIntG, List.filter_eq_nil_iff.mpr]
    · rfl
    · intro t ht
      have := hB t ht
      simp only [decide_eq_true_eq]
      omega
  · exact sum_filter_energy L _ B fun t ht => ⟨henergy t ht, hB t ht⟩

/-- **The clamped count** from the total, given nonnegative energies and graded pieces. -/
theorem levelOneDemazureHilb_count (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ) (m : ℕ)
    (henergy : ∀ t ∈ demazureChar A θ word m, 0 ≤ t.1.2 + (m : ℤ) * m)
    (hpos : ∀ N : ℕ, 0 ≤ hilbIntG A θ word m N) (d : ℕ)
    (htot : ((demazureChar A θ word m).map (·.2)).sum = (d : ℤ)) :
    ∃ B, (∀ N, B ≤ N → DeligneCharacter.levelOneDemazureHilb A θ word m N = 0) ∧
      ∑ N ∈ range B, DeligneCharacter.levelOneDemazureHilb A θ word m N = d := by
  obtain ⟨B, hB0, hsum⟩ := hilbIntG_count A θ word m henergy
  refine ⟨B, fun N hN => by rw [levelOneDemazureHilb_eq, hB0 N hN]; rfl, ?_⟩
  have : ((∑ N ∈ range B, DeligneCharacter.levelOneDemazureHilb A θ word m N : ℕ) : ℤ) = d := by
    push_cast
    rw [← htot, ← hsum]
    refine sum_congr rfl fun N _ => ?_
    rw [levelOneDemazureHilb_eq, Int.toNat_of_nonneg (hpos N)]
  exact_mod_cast this

/-! ## A cheaper invariance criterion: reflections permute the terms of `C_1` -/

theorem RData.lin_lin (ρ : RData r) (h : ρ.p ρ.α = 2) (v : Wt r) : ρ.lin (ρ.lin v) = v := by
  simp only [RData.lin_apply, map_sub, map_zsmul, h]
  module

theorem reflFin_reflFin (A : List (List ℤ)) (i : ℕ) (hi : i < r) (hA : (A.getD i []).getD i 0 = 2)
    (μ : List ℤ) (hμ : μ.length = r) : reflFin A i (reflFin A i μ) = μ := by
  have hl : (reflFin A i μ).length = r := by simp [reflFin, shiftAt, hμ]
  have hl2 : (reflFin A i (reflFin A i μ)).length = r := by simp [reflFin, shiftAt, hμ]
  apply vec_injective _ _ hl2 hμ
  rw [vec_reflFin A i _ hl, vec_reflFin A i _ hμ, RData.lin_lin]
  show pFin A i (eAt r i) = 2
  simp only [pFin, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [sum_eq_single ⟨i, hi⟩]
  · simp only [eAt, if_true, mul_one]; exact hA
  · intro j _ hj
    have : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
    simp [eAt, this]
  · simp

theorem reflZero_reflZero (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r)
    (hθθ : (List.zipWith (· * ·) (aTheta A θ) θ).sum = 2)
    (μ : List ℤ) (hμ : μ.length = r) : reflZero A θ (reflZero A θ μ) = μ := by
  have hl : (reflZero A θ μ).length = r := by simp [reflZero, shiftTheta, hμ, hθ]
  have hl2 : (reflZero A θ (reflZero A θ μ)).length = r := by simp [reflZero, shiftTheta, hμ, hθ]
  apply vec_injective _ _ hl2 hμ
  rw [vec_reflZero A θ hθ _ hl, vec_reflZero A θ hθ _ hμ, RData.lin_lin]
  rw [sum_zipWith_mul, sum_range_eq_fin _ _ hθ] at hθθ
  simp only [ρZero, map_neg, AddMonoidHom.neg_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  simp only [Pi.neg_apply, mul_neg, sum_neg_distrib, neg_neg]
  exact hθθ

/-- The image of every term under `g` is a term of `f`. -/
def memCheck (g : List ℤ → List ℤ) (f : LPoly) : Bool :=
  f.all fun t => decide (((g t.1.1, t.1.2), t.2) ∈ f)

theorem toR1_mapW_eq (g : List ℤ → List ℤ) (f : LPoly) (hf : Good r f)
    (hinv : ∀ μ : List ℤ, μ.length = r → g (g μ) = μ) (hnd : f.Nodup)
    (hmem : memCheck g f = true) : toR1 r (mapW g f) = toR1 r f := by
  simp only [memCheck, List.all_eq_true, decide_eq_true_eq] at hmem
  have hnd' : (mapW g f).Nodup := by
    apply hnd.map_on
    intro s hs t ht h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have : s.1.1 = t.1.1 := by rw [← hinv _ (hf s hs), h1, hinv _ (hf t ht)]
    exact Prod.ext (Prod.ext this h2) h3
  have hsub : mapW g f ⊆ f := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact hmem t ht
  have hperm := (hnd'.subperm hsub).perm_of_length_le (by simp [mapW])
  rw [toR1_eq_sum_single, toR1_eq_sum_single]
  exact (hperm.map _).sum_eq

/-- **Invariance from per-letter membership checks.** -/
theorem inv_of_memChecks (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r) (word : List ℕ)
    (f : LPoly) (hf : Good r f) (hnd : f.Nodup)
    (hw : ∀ i ∈ word, i < r ∧ (A.getD i []).getD i 0 = 2)
    (hθθ : (List.zipWith (· * ·) (aTheta A θ) θ).sum = 2)
    (hZ : memCheck (reflZero A θ) f = true) (hF : ∀ i ∈ word, memCheck (reflFin A i) f = true) :
    ∀ ρ ∈ ρZero (r := r) A θ :: word.map (ρFin A), ρ.sLin (toR1 r f) = toR1 r f := by
  intro ρ hρ
  rcases List.mem_cons.mp hρ with rfl | hρ
  · rw [sLin_toR1 _ _ f hf (fun μ hμ => vec_reflZero A θ hθ μ hμ)]
    exact toR1_mapW_eq _ f hf (fun μ hμ => reflZero_reflZero A θ hθ hθθ μ hμ) hnd hZ
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hρ
    rw [sLin_toR1 _ _ f hf (fun μ hμ => vec_reflFin A i μ hμ)]
    exact toR1_mapW_eq _ f hf (fun μ hμ => reflFin_reflFin A i (hw i hi).1 (hw i hi).2 μ hμ) hnd
      (hF i hi)

/-! ## Chaining pinned Demazure steps -/

theorem foldr_step (A : List (List ℤ)) (i : ℕ) (w : List ℕ) (z P Q : LPoly)
    (h1 : w.foldr (fun i g => demazureFin A i g) z = P) (h2 : demazureFin A i P = Q) :
    (i :: w).foldr (fun i g => demazureFin A i g) z = Q := by
  rw [List.foldr_cons, h1, h2]

theorem demazureChar_one (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ) :
    demazureChar A θ word 1 = word.foldr (fun i g => demazureFin A i g)
      (demazureZero A θ [((List.replicate θ.length 0, 0), 1)]) := rfl

end

end VOA.DeligneAudit.DeligneCharacter.DemCount
