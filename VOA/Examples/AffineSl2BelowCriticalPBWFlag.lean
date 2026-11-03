/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BelowCriticalFlag
import Mathlib.Algebra.Order.Group.Multiset

/-!
# The ordinary flag is spanned by ordered PBW monomials of bounded length

**Filtered PBW straightening.**  Every current creation word of length `L` is a linear
combination of *ordered* PBW monomials of length at most `L` (`wordStateA_mem_pbwSpan`): an
adjacent swap keeps the length and decreases the inversion count, and its commutator term is one
letter shorter.  Consequently each piece of the ordinary flag is the span of the PBW basis vectors
of bounded length (`ordinaryPiece_eq_pbwSpan`), and in every weight space the ordered PBW
monomials of that energy form a basis (`energyBasis`) adapted to the flag
(`mem_ordinaryFlag_iff_repr`).

The straightening argument is the one of `AffineSl2UniversalC2PBW` (whose helper lemmas are
private there), re-run with the word length tracked.
-/

namespace VOA

namespace AffineSl2BelowCritical

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity AffineSl2PBWWakimotoReduction

noncomputable section

/-! ## Sorted words -/

/-- Lexicographically ordered affine PBW letters. -/
abbrev LexLetter := Fin 3 ×ₗ ℕ

/-- The canonical ordered list attached to a PBW exponent. -/
def lexExponentWord (mu : LexLetter →₀ ℕ) : List LexLetter :=
  (mu.support.sort (fun a b => a ≤ b)).flatMap fun q => List.replicate (mu q) q

theorem orderedPBWColorWord_eq (mu : LexLetter →₀ ℕ) :
    orderedPBWColorWord mu = (lexExponentWord mu).map ofLex := by
  simp [orderedPBWColorWord, lexExponentWord, List.map_flatMap]

theorem lexExponentWord_toMultiset (mu : LexLetter →₀ ℕ) :
    (lexExponentWord mu : Multiset LexLetter) = Finsupp.toMultiset mu := by
  classical
  rw [lexExponentWord, Finsupp.toMultiset_apply, Finsupp.sum]
  have hcoe : ∀ l : List LexLetter,
      ((l.flatMap fun q => List.replicate (mu q) q : List LexLetter) : Multiset LexLetter) =
        (l.map fun q => mu q • ({q} : Multiset LexLetter)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons q l ih =>
        change (List.replicate (mu q) q : Multiset LexLetter) +
            (List.flatMap (fun q => List.replicate (mu q) q) l : Multiset LexLetter) = _
        rw [Multiset.coe_replicate, ih]
        simp [Multiset.nsmul_singleton]
  rw [hcoe]
  have hs := congrArg Multiset.sum (congrArg (Multiset.map fun q : LexLetter =>
      mu q • ({q} : Multiset LexLetter))
    (mu.support.sort_eq (fun a b => a ≤ b)))
  exact hs

theorem lexExponentWord_pairwise (mu : LexLetter →₀ ℕ) :
    (lexExponentWord mu).Pairwise (fun a b => a ≤ b) := by
  classical
  have haux : ∀ l : List LexLetter, l.Pairwise (fun a b => a ≤ b) →
      (l.flatMap fun q => List.replicate (mu q) q).Pairwise (fun a b => a ≤ b) := by
    intro l hl
    induction l with
    | nil => simp
    | cons q l ih =>
        rw [List.pairwise_cons] at hl
        simp only [List.flatMap_cons]
        rw [List.pairwise_append]
        refine ⟨List.pairwise_replicate_of_refl, ih hl.2, ?_⟩
        intro a ha b hb
        have ha' : a = q := List.eq_of_mem_replicate ha
        subst a
        simp only [List.mem_flatMap] at hb
        obtain ⟨r, hr, hbr⟩ := hb
        have hbr' : b = r := List.eq_of_mem_replicate hbr
        subst b
        exact hl.1 r hr
  exact haux _ (Finset.pairwise_sort _ _)

/-- A sorted list is the canonical exponent word of its multiplicity function. -/
theorem eq_lexExponentWord_toFinsupp (l : List LexLetter)
    (hl : l.Pairwise (fun a b => a ≤ b)) :
    l = lexExponentWord (Multiset.toFinsupp (l : Multiset LexLetter)) := by
  classical
  have hcoe : (l : Multiset LexLetter) =
      (lexExponentWord (Multiset.toFinsupp (l : Multiset LexLetter)) : Multiset LexLetter) := by
    rw [lexExponentWord_toMultiset, Multiset.toFinsupp_toMultiset]
  exact (Multiset.coe_eq_coe.mp hcoe).eq_of_pairwise' hl
    (lexExponentWord_pairwise (Multiset.toFinsupp (l : Multiset LexLetter)))

/-- Number of inverted pairs in a list. -/
def inversionCount : List LexLetter → ℕ
  | [] => 0
  | q :: l => (l.filter fun r => r < q).length + inversionCount l

theorem inversionCount_swap (pre post : List LexLetter) (a b : LexLetter) (hba : b < a) :
    inversionCount (pre ++ b :: a :: post) < inversionCount (pre ++ a :: b :: post) := by
  induction pre with
  | nil =>
      have hab : ¬a < b := not_lt_of_ge hba.le
      simp only [List.nil_append, inversionCount, List.filter_cons]
      simp [hba, hab]
      omega
  | cons q pre ih =>
      simp only [List.cons_append, inversionCount, List.filter_append, List.length_append,
        List.filter_cons]
      split_ifs <;> simp only [List.length_cons] at ih ⊢ <;> omega

/-- A non-sorted list contains an adjacent inverted pair. -/
theorem exists_adjacent_inversion_of_not_pairwise :
    ∀ l : List LexLetter, ¬l.Pairwise (fun a b => a ≤ b) →
      ∃ (pre : List LexLetter) (a b : LexLetter) (post : List LexLetter),
        b < a ∧ l = pre ++ a :: b :: post
  | [], h => by simp at h
  | [_], h => by simp at h
  | a :: b :: l, h => by
      by_cases hab : a ≤ b
      · have ht : ¬(b :: l).Pairwise (fun x y => x ≤ y) := by
          intro ht
          exact h ((List.pairwise_cons_cons_iff_of_trans).mpr ⟨hab, ht⟩)
        obtain ⟨pre, c, d, post, hdc, heq⟩ :=
          exists_adjacent_inversion_of_not_pairwise (b :: l) ht
        exact ⟨a :: pre, c, d, post, hdc, by simp [heq]⟩
      · exact ⟨[], a, b, l, lt_of_not_ge hab, rfl⟩

variable (k : ℂ)

/-- The creation state of a list of lexicographic letters. -/
def lexState (l : List LexLetter) : WakModule k := wordStateA k (l.map ofLex)

theorem lexState_cons (q : LexLetter) (l : List LexLetter) :
    lexState k (q :: l) = J k (ofLex q).1 (-((ofLex q).2 : ℤ) - 1) (lexState k l) := by
  simp [lexState, wordStateA_cons]

/-- Swapping two adjacent negative current modes produces the bracket term. -/
theorem lexState_adjacent_swap (pre post : List LexLetter) (a b : LexLetter) :
    lexState k (pre ++ a :: b :: post) =
      lexState k (pre ++ b :: a :: post) +
        ∑ c : Fin 3, fabc (ofLex a).1 (ofLex b).1 c •
          lexState k (pre ++ toLex (c, (ofLex a).2 + (ofLex b).2 + 1) :: post) := by
  induction pre with
  | nil =>
      simp only [List.nil_append]
      have h := congrArg (fun T : Module.End ℂ (WakModule k) => T (lexState k post))
        (current_comm k (ofLex a).1 (ofLex b).1
          (-((ofLex a).2 : ℤ) - 1) (-((ofLex b).2 : ℤ) - 1))
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.sum_apply, LinearMap.smul_apply] at h
      rw [sub_eq_iff_eq_add] at h
      have hnz : -((ofLex a).2 : ℤ) - 1 + (-((ofLex b).2 : ℤ) - 1) ≠ 0 := by omega
      rw [if_neg hnz] at h
      simp only [LinearMap.zero_apply, add_zero] at h
      have hm : -((ofLex a).2 : ℤ) - 1 + (-((ofLex b).2 : ℤ) - 1) =
          (-(((ofLex a).2 + (ofLex b).2 + 1 : ℕ) : ℤ) - 1) := by omega
      rw [hm] at h
      rw [add_comm (∑ c : Fin 3, fabc (ofLex a).1 (ofLex b).1 c •
        J k c (-↑((ofLex a).2 + (ofLex b).2 + 1) - 1) (lexState k post))] at h
      simpa only [lexState_cons, ofLex_toLex] using h
  | cons q pre ih =>
      simp only [List.cons_append, lexState_cons]
      rw [ih, map_add, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      rw [map_smul]

/-- The PBW length of an exponent: the number of letters of its ordered word. -/
def pbwLength (mu : CurrentIndex) : ℕ := (orderedPBWColorWord mu).length

variable (hk : k + 2 ≠ 0)

/-- The span of the ordered PBW monomials of length at most `p`. -/
def pbwSpan (p : ℕ) : Submodule ℂ (WakModule k) :=
  Submodule.span ℂ (currentPBWBasis k hk '' {mu | pbwLength mu ≤ p})

theorem pbwSpan_mono {p q : ℕ} (h : p ≤ q) : pbwSpan k hk p ≤ pbwSpan k hk q :=
  Submodule.span_mono (Set.image_mono fun _ hm => le_trans hm h)

/-- **Filtered PBW straightening.** -/
theorem lexState_mem_pbwSpan (l : List LexLetter) : lexState k l ∈ pbwSpan k hk l.length := by
  by_cases hsort : l.Pairwise (fun a b => a ≤ b)
  · let mu : CurrentIndex := Multiset.toFinsupp (l : Multiset LexLetter)
    have hl : l = lexExponentWord mu := eq_lexExponentWord_toFinsupp l hsort
    apply Submodule.subset_span
    refine ⟨mu, ?_, ?_⟩
    · change (orderedPBWColorWord mu).length ≤ l.length
      rw [orderedPBWColorWord_eq, List.length_map, ← hl]
    · rw [currentPBWBasis_apply, orderedPBWColorWord_eq, lexState, ← hl]
  · obtain ⟨pre, a, b, post, hba, heq⟩ :=
      exists_adjacent_inversion_of_not_pairwise l hsort
    subst l
    have hswap := lexState_mem_pbwSpan (pre ++ b :: a :: post)
    have hbracket : ∀ c : Fin 3,
        lexState k (pre ++ toLex (c, (ofLex a).2 + (ofLex b).2 + 1) :: post) ∈
          pbwSpan k hk (pre ++ a :: b :: post).length := by
      intro c
      exact pbwSpan_mono k hk (by simp)
        (lexState_mem_pbwSpan (pre ++ toLex (c, (ofLex a).2 + (ofLex b).2 + 1) :: post))
    rw [lexState_adjacent_swap k]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (hbracket c))
    simpa using hswap
termination_by (l.length, inversionCount l)
decreasing_by
  · rw [heq]
    rw [show (pre ++ b :: a :: post).length = (pre ++ a :: b :: post).length by simp]
    apply Prod.Lex.right
    exact inversionCount_swap pre post a b hba
  · rw [heq]
    apply Prod.Lex.left
    simp

theorem wordStateA_mem_pbwSpan (w : List (Fin 3 × ℕ)) :
    wordStateA k w ∈ pbwSpan k hk w.length := by
  have h := lexState_mem_pbwSpan k hk (w.map toLex)
  have hw : (w.map toLex).map ofLex = w := by
    rw [List.map_map]
    exact List.map_id'' (fun _ => rfl) w
  rw [lexState, hw, List.length_map] at h
  exact h

/-- **Each ordinary piece is spanned by ordered PBW monomials of bounded length.** -/
theorem ordinaryPiece_eq_pbwSpan (p : ℕ) : ordinaryPiece k p = pbwSpan k hk p := by
  apply le_antisymm
  · rw [ordinaryPiece, Submodule.span_le]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact pbwSpan_mono k hk hw (wordStateA_mem_pbwSpan k hk w)
  · rw [pbwSpan, Submodule.span_le]
    rintro _ ⟨mu, hmu, rfl⟩
    rw [currentPBWBasis_apply]
    exact wordStateA_mem_ordinaryPiece hmu

/-- Membership in an ordinary piece is a support condition on PBW coordinates. -/
theorem mem_ordinaryPiece_iff_repr (p : ℕ) (x : WakModule k) :
    x ∈ ordinaryPiece k p ↔ ∀ mu, p < pbwLength mu → (currentPBWBasis k hk).repr x mu = 0 := by
  rw [ordinaryPiece_eq_pbwSpan k hk, pbwSpan, Module.Basis.mem_span_image]
  constructor
  · intro h mu hmu
    by_contra hne
    exact absurd (h (Finsupp.mem_support_iff.mpr hne)) (by simp; omega)
  · intro h mu hmu
    by_contra hle
    exact (Finsupp.mem_support_iff.mp hmu) (h mu (by simp at hle; omega))

end

end AffineSl2BelowCritical

end VOA
