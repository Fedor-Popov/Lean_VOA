/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusC2M1Ring
import VOA.Examples.TripletWpTwoAMProof
import VOA.Core.SparseRational

/-!
# An executable evaluator for word states on the neutral sector

Rank-`r` Heisenberg Fock space, one fixed orthonormal direction `a`, variables
`x_i = X(i,a) = h_a(−i−1)`.  A *raw polynomial* `P : RawPoly ℕ` (list of `(coefficient, word)`)
denotes `Σ c·x_{i₁}⋯x_{i_k}` (`evR`).  This file defines kernel-reducible list operations and proves
that they compute

* the oscillators `h_a(n)` (`annR`), the derivative currents `Y(x_i, z)` (`fAct`),
* the vertex operators of word states `Y(x_{i₁}⋯x_{i_k}𝟙, z)` (`wordAct`, `polyAct`),

and finally (`V2m_smul_evR`) the products `u₍ₙ₎v` of charge-`0` states of the lattice VOA
`V_{2m}` — for every `m`, since on the charge-`0` sector the lattice vertex operators are the
orthonormal Heisenberg ones (`YfullGen_neutralFieldLift`).  Every operation is structurally
recursive and avoids well-founded merges, so identities between evaluated polynomials can be
checked by `decide`.  Adapted from the `W(2)` certificate machinery
(`Examples/TripletWpTwoAMClose.lean`, `…SparseBridge.lean`), but in orthonormal coordinates,
which makes it independent of the lattice normalization `⟨α,α⟩ = 2m`.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne.PlusC2Eval

open VOA HeisenbergN MvPolynomial VOA.SparseRational VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice

/-! ## §1  The executable layer -/

/-- Multiply every word by `x_i`. -/
def prependR (i : ℕ) (P : RawPoly ℕ) : RawPoly ℕ := P.map fun t => (t.1, i :: t.2)

/-- Scale by a rational. -/
def scaleR (q : ℚ) (P : RawPoly ℕ) : RawPoly ℕ := P.map fun t => (q * t.1, t.2)

/-- `h(n) = n·∂/∂x_{n−1}` on one word (`n ≥ 1`). -/
def annR (n : ℕ) : List ℕ → RawPoly ℕ
  | [] => []
  | i :: is => (if n = i + 1 then [((n : ℚ), is)] else []) ++ prependR i (annR n is)

/-- `∏_{l < i} (s + 1 + l)`. -/
def riseProd (s : ℤ) : ℕ → ℤ
  | 0 => 1
  | i + 1 => riseProd s i * (s + 1 + i)

/-- The coefficient of `Y(x_i, z)_s`. -/
def fCoeff (i : ℕ) (s : ℤ) : ℚ := (riseProd s i : ℚ) / (i.factorial : ℚ)

/-- The oscillator mode occurring in `Y(x_i, z)_s`. -/
def fMode (i : ℕ) (s : ℤ) : ℤ := -(s + i) - 1

/-- `Y(x_i, z)_s` on one word. -/
def fActW (i : ℕ) (s : ℤ) (w : List ℕ) : RawPoly ℕ :=
  if fMode i s < 0 then [(fCoeff i s, (-fMode i s - 1).toNat :: w)]
  else if fMode i s = 0 then []
  else scaleR (fCoeff i s) (annR (fMode i s).toNat w)

/-- `Y(x_i, z)_s` on a raw polynomial. -/
def fAct (i : ℕ) (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.flatMap fun t => scaleR t.1 (fActW i s t.2)

/-- The conformal weight of a word. -/
def wWt : List ℕ → ℕ
  | [] => 0
  | i :: is => i + 1 + wWt is

/-- `[lo, lo + n)` as a list. -/
def intRange (lo : ℤ) : ℕ → List ℤ
  | 0 => []
  | n + 1 => lo :: intRange (lo + 1) n

/-- `Y(x_{i₁}⋯x_{i_k}𝟙, z)_s` on a raw polynomial `P` all of whose words have weight `w`. -/
def wordAct : List ℕ → ℤ → ℕ → RawPoly ℕ → RawPoly ℕ
  | [], s, _, P => if s = 0 then P else []
  | i :: is, s, w, P =>
      (intRange (-((i + 1 + w : ℕ) : ℤ))
          ((max (-1) (((wWt is + w : ℕ) : ℤ) + s)) + ((i + 1 + w : ℕ) : ℤ) + 1).toNat).flatMap
        fun m =>
          if 0 ≤ m then fAct i m (wordAct is (s - m) w P)
          else wordAct is (s - m) ((((i + 1 + w : ℕ) : ℤ) + m).toNat) (fAct i m P)

/-- `Y(Q, z)_s P` for a raw polynomial state `Q`. -/
def polyAct (Q : RawPoly ℕ) (s : ℤ) (w : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  Q.flatMap fun t => scaleR t.1 (wordAct t.2 s w P)

/-- Normal form (merging equal monomials). -/
def normR (P : RawPoly ℕ) : RawPoly ℕ := toRaw (normalizeQ P)

/-! ## §2  Semantics: polynomials -/

variable {r : ℕ} (a : Fin r)

/-- The variables `x_i = X(i,a)`. -/
noncomputable abbrev xv (i : ℕ) : FockN r := X (i, a)

/-- The value of a raw polynomial. -/
noncomputable abbrev evR (P : RawPoly ℕ) : FockN r := evalRaw (xv a) P

theorem algebraMap_rat_mul (q : ℚ) (x : FockN r) :
    algebraMap ℚ (FockN r) q * x = ((q : ℂ)) • x := by
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℚ ℂ (FockN r)]
  congr 2

theorem evalWord_cons (i : ℕ) (w : List ℕ) :
    evalWord (xv a) (i :: w) = X (i, a) * evalWord (xv a) w := by
  simp [evalWord]

theorem evalWord_nil : evalWord (xv a) [] = (1 : FockN r) := by simp [evalWord]

theorem evR_nil : evR a ([] : RawPoly ℕ) = 0 := by simp [evalRaw]

theorem evR_cons (c : ℚ) (w : List ℕ) (P : RawPoly ℕ) :
    evR a ((c, w) :: P) = ((c : ℂ)) • evalWord (xv a) w + evR a P := by
  simp [evalRaw, MvPolynomial.smul_eq_C_mul]

theorem evR_append (P Q : RawPoly ℕ) : evR a (P ++ Q) = evR a P + evR a Q :=
  evalRaw_append _ P Q

theorem evR_flatMap {ι : Type*} (l : List ι) (f : ι → RawPoly ℕ) :
    evR a (l.flatMap f) = (l.map fun x => evR a (f x)).sum := by
  induction l with
  | nil => simp [evalRaw]
  | cons x xs ih => rw [List.flatMap_cons, evR_append, ih, List.map_cons, List.sum_cons]

theorem evR_scaleR (q : ℚ) (P : RawPoly ℕ) : evR a (scaleR q P) = ((q : ℂ)) • evR a P := by
  rw [scaleR, evR, evalRaw_scale, algebraMap_rat_mul]

theorem evR_prependR (i : ℕ) : ∀ P : RawPoly ℕ, evR a (prependR i P) = X (i, a) * evR a P
  | [] => by simp [prependR, evalRaw]
  | (c, w) :: P => by
    change evR a ((c, i :: w) :: prependR i P) = _
    rw [evR_cons, evR_cons, evR_prependR i P, mul_add, mul_smul_comm, evalWord_cons]

theorem evR_normR (P : RawPoly ℕ) : evR a (normR P) = evR a P := by
  rw [normR, evR, evalRaw_toRaw, evalSparse_normalizeQ]

/-! ## §3  Semantics: the oscillators and the currents -/

theorem pderiv_X_self_ne (i j : ℕ) (hij : i ≠ j) : pderiv (i, a) (X (j, a) : FockN r) = 0 := by
  rw [pderiv_X, Pi.single_apply, if_neg]
  intro h; exact hij (congrArg Prod.fst h).symm

theorem oscN_pos_X_mul (n : ℕ) (hn : 1 ≤ n) (i : ℕ) (q : FockN r) :
    oscN r 1 a (n : ℤ) (X (i, a) * q) =
      (if n = i + 1 then ((n : ℂ)) • q else 0) + X (i, a) * oscN r 1 a (n : ℤ) q := by
  rw [oscN_pos _ _ _ (by omega : (0 : ℤ) < n)]
  simp only [LinearMap.smul_apply, pderivLMN_apply, one_smul, Derivation.leibniz, smul_eq_mul]
  have hn' : ((n : ℤ) - 1).toNat = n - 1 := by omega
  rw [hn']
  by_cases h : n = i + 1
  · subst h
    rw [if_pos rfl, show i + 1 - 1 = i by omega, pderiv_X_self]
    simp only [MvPolynomial.smul_eq_C_mul]
    push_cast
    ring
  · rw [if_neg h, pderiv_X_self_ne a _ _ (by omega)]
    simp only [MvPolynomial.smul_eq_C_mul, mul_zero, add_zero, zero_add]
    ring

theorem oscN_pos_one (n : ℕ) (hn : 1 ≤ n) : oscN r 1 a (n : ℤ) (1 : FockN r) = 0 := by
  rw [oscN_pos _ _ _ (by omega : (0 : ℤ) < n)]
  simp [pderivLMN_apply]

theorem evR_annR (n : ℕ) (hn : 1 ≤ n) : ∀ w : List ℕ,
    evR a (annR n w) = oscN r 1 a (n : ℤ) (evalWord (xv a) w)
  | [] => by rw [annR, evR_nil, evalWord_nil, oscN_pos_one a n hn]
  | i :: is => by
    rw [annR, evR_append, evR_prependR, evR_annR n hn is, evalWord_cons, oscN_pos_X_mul a n hn]
    by_cases h : n = i + 1
    · rw [if_pos h, if_pos h, evR_cons, evR_nil, add_zero]
      congr 2
    · rw [if_neg h, if_neg h, evR_nil, zero_add]

theorem riseProd_eq (s : ℤ) : ∀ i : ℕ, riseProd s i = ∏ l ∈ Finset.range i, (s + 1 + l)
  | 0 => by simp [riseProd]
  | i + 1 => by rw [riseProd, riseProd_eq s i, Finset.prod_range_succ]

theorem fCoeff_cast (i : ℕ) (s : ℤ) :
    ((fCoeff i s : ℚ) : ℂ) = (((∏ l ∈ Finset.range i, (s + 1 + l) : ℤ) : ℂ)) * (i.factorial : ℂ)⁻¹ := by
  rw [fCoeff, ← riseProd_eq]
  push_cast
  rw [div_eq_mul_inv]

theorem evR_fActW (i : ℕ) (s : ℤ) (w : List ℕ) :
    evR a (fActW i s w) = genFieldN r 1 a i s (evalWord (xv a) w) := by
  rw [genFieldN_coeff, LinearMap.smul_apply, ← fCoeff_cast]
  change evR a (fActW i s w) = ((fCoeff i s : ℚ) : ℂ) • oscN r 1 a (fMode i s) (evalWord (xv a) w)
  rw [fActW]
  by_cases hneg : fMode i s < 0
  · rw [if_pos hneg, evR_cons, evR_nil, add_zero, oscN_apply_neg _ _ _ hneg, evalWord_cons]
  · rw [if_neg hneg]
    by_cases hzero : fMode i s = 0
    · rw [if_pos hzero, evR_nil, hzero, oscN_zero, LinearMap.zero_apply, smul_zero]
    · rw [if_neg hzero, evR_scaleR, evR_annR a (fMode i s).toNat (by omega),
        show (((fMode i s).toNat : ℕ) : ℤ) = fMode i s by omega]

theorem evR_fAct (i : ℕ) (s : ℤ) : ∀ P : RawPoly ℕ,
    evR a (fAct i s P) = genFieldN r 1 a i s (evR a P)
  | [] => by simp [fAct, evalRaw]
  | (c, w) :: P => by
    change evR a (scaleR c (fActW i s w) ++ fAct i s P) = _
    rw [evR_append, evR_scaleR, evR_fActW, evR_fAct i s P, evR_cons, map_add, map_smul]

/-! ## §4  Semantics: word fields -/

/-- The right-nested normal-ordered product `:Y(x_{i₁})(⋯Y(x_{i_k})):`. -/
noncomputable def wordFF : List ℕ → {f : FormalDist (Module.End ℂ (FockN r)) // IsField f}
  | [] => ⟨idFieldN r, idFieldN_isField r⟩
  | i :: is => ⟨nprod (genFieldN_isField r 1 a i) (wordFF is).2,
      (genFieldN_isField r 1 a i).nprod (wordFF is).2⟩

/-- The field of a word state. -/
noncomputable def wordF (is : List ℕ) : FormalDist (Module.End ℂ (FockN r)) := (wordFF a is).1

theorem wordF_isField (is : List ℕ) : IsField (wordF a is) := (wordFF a is).2

theorem YN_X' (i : ℕ) : YN r 1 (X (i, a)) = genFieldN r 1 a i := by
  rw [MvPolynomial.X, YN_monomial_one, YmonN]
  have hword : monoWordN (Finsupp.single (i, a) 1) = [(i, a)] := by
    unfold monoWordN
    rw [show (Finsupp.single (i, a) 1 : (ℕ × Fin r) →₀ ℕ).support = {(i, a)} from
      Finsupp.support_single (i, a) (by norm_num : (1 : ℕ) ≠ 0)]
    simp
  rw [hword, YwordN_cons]
  exact nprod_idFieldN (genFieldN_isField r 1 a i)

/-- The `(−1)`-product by `x_i` is multiplication. -/
theorem heis_smul_X_neg_one (i : ℕ) (q : FockN r) :
    (heisenbergNVOA r 1 (by norm_num)).smul (X (i, a)) (-1) q = X (i, a) * q := by
  rw [PreVertexAlgebra.smul_def, mode_apply]
  change (YN r 1 (X (i, a))) 0 q = X (i, a) * q
  rw [YN_X', genFieldN_coeff]
  have hprod : ∏ x ∈ Finset.range i, ((0 : ℤ) + 1 + (x : ℤ)) = (i.factorial : ℤ) :=
    prod_range_zero_eq_factorialN i
  rw [LinearMap.smul_apply, hprod]
  rw [show -((0 : ℤ) + (i : ℤ)) - 1 < 0 by omega |> fun h => oscN_apply_neg r 1 a h q]
  rw [show (-(-((0 : ℤ) + (i : ℤ)) - 1) - 1).toNat = i by omega]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i), one_smul]

theorem YN_mul_X (i : ℕ) (q : FockN r) :
    YN r 1 (X (i, a) * q) = nprod (genFieldN_isField r 1 a i) (YN_isField r 1 q) := by
  let W := heisenbergNVOA r 1 (by norm_num)
  have h := W.assoc_neg (X (i, a)) q 0
  dsimp [W] at h
  norm_num at h
  rw [heis_smul_X_neg_one] at h
  change YN r 1 (X (i, a) * q) = _ at h
  rw [negProd] at h
  norm_num at h
  change YN r 1 (X (i, a) * q) = nprod (YN_isField r 1 (X (i, a))) (YN_isField r 1 q) at h
  exact h.trans (nprodN_eq_nprodN (YN_isField r 1 (X (i, a))) (YN_isField r 1 q)
    (genFieldN_isField r 1 a i) (YN_isField r 1 q) (YN_X' a i) rfl)

theorem YN_evalWord : ∀ is : List ℕ, YN r 1 (evalWord (xv a) is) = wordF a is
  | [] => by rw [evalWord_nil, ← vacuumN, YN_vacuum]; rfl
  | i :: is => by
    rw [evalWord_cons, YN_mul_X]
    exact nprodN_eq_nprodN (genFieldN_isField r 1 a i) (YN_isField r 1 _)
      (genFieldN_isField r 1 a i) (wordF_isField a is) rfl (YN_evalWord is)

theorem evalWord_mem_grading : ∀ is : List ℕ, evalWord (xv a) is ∈ gradingWN r (wWt is)
  | [] => by rw [evalWord_nil, wWt]; exact vacuumN_mem_gradingWN r
  | i :: is => by
    rw [evalWord_cons, wWt, mem_gradingWN]
    have hi := wordStateN_mem_gradingWN [(i, a)]
    simp only [wordStateN_cons, wordStateN_nil, mul_one, VOA.LatGen.wordWt_cons,
      VOA.LatGen.wordWt_nil] at hi
    have his := evalWord_mem_grading is
    rw [mem_gradingWN] at hi his
    exact hi.mul his

theorem wordF_graded (is : List ℕ) : GradedFieldN r (wordF a is) (wWt is : ℤ) := by
  rw [← YN_evalWord]
  exact YN_gradedField_of_mem r 1 (evalWord_mem_grading a is)

/-- A raw polynomial all of whose words have weight `w` has weight `w`. -/
theorem evR_mem_grading {w : ℕ} : ∀ P : RawPoly ℕ, (∀ t ∈ P, wWt t.2 = w) →
    evR a P ∈ gradingWN r w
  | [], _ => by rw [evR_nil]; exact Submodule.zero_mem _
  | (c, v) :: P, h => by
    rw [evR_cons]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (evR_mem_grading P fun t ht => h t
      (List.mem_cons_of_mem _ ht))
    have := h (c, v) List.mem_cons_self
    rw [← this]
    exact evalWord_mem_grading a v

theorem sum_Icc_intRange {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∀ (n : ℕ) (lo : ℤ), ∑ m ∈ Finset.Icc lo (lo + n - 1), f m = ((intRange lo n).map f).sum
  | 0, lo => by
    rw [intRange, List.map_nil, List.sum_nil, Finset.Icc_eq_empty (by push_cast; omega),
      Finset.sum_empty]
  | n + 1, lo => by
    rw [intRange, List.map_cons, List.sum_cons, ← sum_Icc_intRange f n (lo + 1)]
    have hset : Finset.Icc lo (lo + ((n + 1 : ℕ) : ℤ) - 1) =
        insert lo (Finset.Icc (lo + 1) (lo + 1 + (n : ℤ) - 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hset, Finset.sum_insert (by simp)]

/-- **The word-field evaluator is correct.** -/
theorem evR_wordAct : ∀ (is : List ℕ) (s : ℤ) (w : ℕ) (P : RawPoly ℕ),
    evR a P ∈ gradingWN r w → evR a (wordAct is s w P) = wordF a is s (evR a P)
  | [], s, w, P, _ => by
    rw [wordAct]
    change evR a (if s = 0 then P else []) = idFieldN r s (evR a P)
    rw [idFieldN_apply]
    by_cases hs : s = 0
    · rw [if_pos hs, if_pos hs, LinearMap.id_apply]
    · rw [if_neg hs, if_neg hs, evR_nil, LinearMap.zero_apply]
  | i :: is, s, w, P, hP => by
    have hnp : wordF a (i :: is) = nprod (genFieldN_isField r 1 a i) (wordF_isField a is) := rfl
    rw [wordAct, evR_flatMap, hnp,
      WpTwoAMProof.nprod_apply_grading_bounded (genFieldN_isField r 1 a i) (wordF_isField a is)
        (i + 1) (wWt is) (by exact_mod_cast genFieldN_gradedField r 1 a i) (wordF_graded a is) s hP]
    have hN : (-((i + 1 + w : ℕ) : ℤ)) +
        ((((max (-1) (((wWt is + w : ℕ) : ℤ) + s)) + ((i + 1 + w : ℕ) : ℤ) + 1).toNat : ℕ) : ℤ) - 1 =
          max (-1) (((wWt is + w : ℕ) : ℤ) + s) := by
      have h0 := le_max_left (-1 : ℤ) (((wWt is + w : ℕ) : ℤ) + s)
      rw [Int.toNat_of_nonneg (by push_cast at h0 ⊢; omega)]; ring
    rw [show Finset.Icc (-((i + 1 + w : ℕ) : ℤ)) (max (-1) (((wWt is + w : ℕ) : ℤ) + s)) =
        Finset.Icc (-((i + 1 + w : ℕ) : ℤ)) ((-((i + 1 + w : ℕ) : ℤ)) +
          ((((max (-1) (((wWt is + w : ℕ) : ℤ) + s)) + ((i + 1 + w : ℕ) : ℤ) + 1).toNat : ℕ) : ℤ) - 1)
        from by rw [hN],
      sum_Icc_intRange]
    congr 1
    apply List.map_congr_left
    intro m _
    rw [normalOrdered_apply]
    by_cases hm0 : 0 ≤ m
    · rw [if_pos hm0, if_pos hm0, Module.End.mul_apply, evR_fAct, evR_wordAct is (s - m) w P hP]
    · rw [if_neg hm0, if_neg hm0, Module.End.mul_apply]
      have hgrade := (genFieldN_gradedField r 1 a i).mem_gradingZN m (w : ℤ)
        (mem_gradingZN_of_gradingWN hP)
      have hnext : evR a (fAct i m P) ∈ gradingWN r ((((i + 1 + w : ℕ) : ℤ) + m).toNat) := by
        rw [evR_fAct]
        by_cases hd : 0 ≤ ((i + 1 + w : ℕ) : ℤ) + m
        · rw [show ((i : ℤ) + 1 + (w : ℤ) + m) = ((i + 1 + w : ℕ) : ℤ) + m by push_cast; ring,
            gradingZN_of_nonneg hd] at hgrade
          exact hgrade
        · have hd' : (i : ℤ) + 1 + (w : ℤ) + m < 0 := by push_cast at hd; omega
          rw [gradingZN_of_neg hd', Submodule.mem_bot] at hgrade
          rw [hgrade]; exact Submodule.zero_mem _
      rw [evR_wordAct is (s - m) _ (fAct i m P) hnext, evR_fAct]

/-- **The vertex operator of a polynomial state.** -/
theorem evR_polyAct (Q : RawPoly ℕ) (s : ℤ) (w : ℕ) (P : RawPoly ℕ)
    (hP : evR a P ∈ gradingWN r w) :
    evR a (polyAct Q s w P) = YN r 1 (evR a Q) s (evR a P) := by
  induction Q with
  | nil => simp [polyAct, evalRaw]
  | cons t Q ih =>
    rcases t with ⟨c, v⟩
    change evR a (scaleR c (wordAct v s w P) ++ polyAct Q s w P) = _
    rw [evR_append, evR_scaleR, evR_wordAct a v s w P hP, ih, evR_cons, map_add, map_smul,
      YN_evalWord]
    rfl

/-! ## §5  The lattice VOA on the charge-`0` sector -/

/-- On the charge-`0` sector the lattice products are the Heisenberg ones. -/
theorem V2m_smul_sec0 (m : ℕ) (hm : 1 ≤ m) (p q : FockN (rank (latP m))) (n : ℤ) :
    (V2m m hm).smul (latStateGen (latP m) p 0) n (latStateGen (latP m) q 0) =
      latStateGen (latP m) ((YN (rank (latP m)) 1 p) (-n - 1) q) 0 := by
  rw [PreVertexAlgebra.smul_def, mode_apply]
  exact WpTwoAMCoords.YfullGen_neutralFieldLift (latP_even m) (latP_posDef m hm) p (-n - 1) q

/-- **The evaluator computes `V_{2m}` products of charge-`0` polynomial states.** -/
theorem V2m_smul_evR (m : ℕ) (hm : 1 ≤ m) (Q P : RawPoly ℕ) (n : ℤ) (w : ℕ)
    (hP : ∀ t ∈ P, wWt t.2 = w) :
    (V2m m hm).smul (latStateGen (latP m) (evR (LatMod.a0 m) Q) 0) n
        (latStateGen (latP m) (evR (LatMod.a0 m) P) 0) =
      latStateGen (latP m) (evR (LatMod.a0 m) (polyAct Q (-n - 1) w P)) 0 := by
  rw [V2m_smul_sec0, evR_polyAct _ Q (-n - 1) w P (evR_mem_grading _ P hP)]

end VOA.Classification.COne.PlusC2Eval
