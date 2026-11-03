/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2WakimotoLiLeading

/-!
# The `(f, h, e)`-ordered PBW basis of `V^k(sl₂)`

The Drinfeld–Sokolov slice map needs a PBW basis of the universal affine vacuum module in which
all `f`-modes stand to the **left**, then all `h`-modes, then all `e`-modes:
`f^λ h^ν e^μ |0⟩`.  The library basis `AffineSl2WakimotoLiLeading.affineSl2PBWBasis` uses the
colour order `(e, f, h)`, which is not suitable (the `e`-modes are leftmost).

We re-order the alphabet by a *rank*: `f ↦ 0`, `h ↦ 1`, `e ↦ 2`, and prove

* `rword_swap` — the adjacent straightening identity for rank letters;
* `straighten` — a general induction principle: a predicate on creation words that holds on
  sorted words and is propagated by adjacent swaps (with their commutator letters) holds on all
  words (measure: length, then inversion count);
* `Fvec_span_eq_top` — the rank-ordered creation states span `V^k(sl₂)`;
* `Fvec_linearIndependent` — they are linearly independent at every non-critical level.  The proof
  is the Wakimoto leading-term argument of `AffineSl2WakimotoLiLeading`: the lowest free-Li
  component of a Wakimoto current word is the *commutative* product of classical symbols, which
  does not see the order of the letters;
* `Fbasis` — the resulting basis.

Everything is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA VOA.AffineSl2PBWWakimotoReduction VOA.AffineSl2WakimotoLiLeading

noncomputable section

/-! ## §1  Rank letters -/

/-- A rank letter `(r, d)`: rank `r` (`0 = f`, `1 = h`, `2 = e`) and depth `d` (mode `-d-1`). -/
abbrev RLetter : Type := Fin 3 ×ₗ ℕ

/-- The colour of a rank: `0 ↦ f = 1`, `1 ↦ h = 2`, `2 ↦ e = 0`. -/
def rankColor : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- The rank of a colour (inverse of `rankColor`). -/
def colorRank : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 0
  | 2 => 1

@[simp] theorem rankColor_colorRank (c : Fin 3) : rankColor (colorRank c) = c := by
  fin_cases c <;> rfl

@[simp] theorem colorRank_rankColor (r : Fin 3) : colorRank (rankColor r) = r := by
  fin_cases r <;> rfl

theorem rankColor_injective : Function.Injective rankColor := by
  intro a b h
  simpa using congrArg colorRank h

/-- Colour of a rank letter. -/
def col (q : RLetter) : Fin 3 := rankColor (ofLex q).1

/-- Depth of a rank letter. -/
def dep (q : RLetter) : ℕ := (ofLex q).2

@[simp] theorem col_toLex (r : Fin 3) (d : ℕ) : col (toLex (r, d)) = rankColor r := rfl

@[simp] theorem dep_toLex (r : Fin 3) (d : ℕ) : dep (toLex (r, d)) = d := rfl

/-- The colour-and-depth pair of a rank letter. -/
def letterPair (q : RLetter) : Fin 3 × ℕ := (col q, dep q)

/-- The creation state of a list of rank letters. -/
def rword (k : ℂ) (l : List RLetter) : WakModule k :=
  wordStateA k (l.map letterPair)

variable (k : ℂ)

@[simp] theorem rword_nil : rword k [] = vacuumA k := rfl

theorem rword_cons (q : RLetter) (l : List RLetter) :
    rword k (q :: l) = J k (col q) (-(dep q : ℤ) - 1) (rword k l) := rfl

/-- **Adjacent straightening.**  Swapping two adjacent creation letters costs the bracket
letters; the central term is absent since both modes are negative. -/
theorem rword_swap (pre post : List RLetter) (a b : RLetter) :
    rword k (pre ++ a :: b :: post) =
      rword k (pre ++ b :: a :: post) +
        ∑ c : Fin 3, fabc (col a) (col b) c •
          rword k (pre ++ toLex (colorRank c, dep a + dep b + 1) :: post) := by
  induction pre with
  | nil =>
      simp only [List.nil_append]
      have h := congrArg (fun T : Module.End ℂ (WakModule k) => T (rword k post))
        (current_comm k (col a) (col b) (-(dep a : ℤ) - 1) (-(dep b : ℤ) - 1))
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.sum_apply, LinearMap.smul_apply] at h
      rw [sub_eq_iff_eq_add] at h
      have hnz : -(dep a : ℤ) - 1 + (-(dep b : ℤ) - 1) ≠ 0 := by omega
      rw [if_neg hnz] at h
      simp only [LinearMap.zero_apply, add_zero] at h
      have hm : -(dep a : ℤ) - 1 + (-(dep b : ℤ) - 1) =
          (-((dep a + dep b + 1 : ℕ) : ℤ) - 1) := by push_cast; ring
      rw [hm] at h
      rw [rword_cons, rword_cons, rword_cons, rword_cons, h, add_comm]
      congr 1
  | cons q pre ih =>
      simp only [List.cons_append, rword_cons]
      rw [ih, map_add, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smul]

/-! ## §2  The straightening induction principle -/

/-- Number of inverted pairs in a list. -/
def inversionCount : List RLetter → ℕ
  | [] => 0
  | q :: l => (l.filter fun r => r < q).length + inversionCount l

theorem inversionCount_swap (pre post : List RLetter) (a b : RLetter) (hba : b < a) :
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

theorem exists_adjacent_inversion_of_not_pairwise :
    ∀ l : List RLetter, ¬l.Pairwise (fun a b => a ≤ b) →
      ∃ (pre : List RLetter) (a b : RLetter) (post : List RLetter),
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

/-- **The straightening induction principle.**  A predicate on rank-letter lists that holds on
sorted lists, and holds on `pre ++ a :: b :: post` (with `b < a`) whenever it holds on the swapped
list and on every bracket list with a nonzero structure constant, holds on every list. -/
theorem straighten {P : List RLetter → Prop}
    (hsort : ∀ l : List RLetter, l.Pairwise (fun a b => a ≤ b) → P l)
    (hstep : ∀ (pre : List RLetter) (a b : RLetter) (post : List RLetter), b < a →
      P (pre ++ b :: a :: post) →
      (∀ c : Fin 3, fabc (col a) (col b) c ≠ 0 →
        P (pre ++ toLex (colorRank c, dep a + dep b + 1) :: post)) →
      P (pre ++ a :: b :: post))
    (l : List RLetter) : P l := by
  by_cases hs : l.Pairwise (fun a b => a ≤ b)
  · exact hsort l hs
  · obtain ⟨pre, a, b, post, hba, heq⟩ := exists_adjacent_inversion_of_not_pairwise l hs
    subst l
    exact hstep pre a b post hba (straighten hsort hstep (pre ++ b :: a :: post))
      (fun c _ => straighten hsort hstep
        (pre ++ toLex (colorRank c, dep a + dep b + 1) :: post))
termination_by (l.length, inversionCount l)
decreasing_by
  · rw [heq]
    rw [show (pre ++ b :: a :: post).length = (pre ++ a :: b :: post).length by simp]
    apply Prod.Lex.right
    exact inversionCount_swap pre post a b hba
  · rw [heq]
    apply Prod.Lex.left
    simp

/-! ## §3  Exponent words -/

/-- The sorted word of an exponent function on rank letters. -/
def expWord (μ : RLetter →₀ ℕ) : List RLetter :=
  (μ.support.sort (fun a b => a ≤ b)).flatMap fun q => List.replicate (μ q) q

/-- A generic multiset identity for sorted `flatMap`-`replicate` words. -/
theorem flatMap_replicate_coe {α β : Type*} [LinearOrder α] (ν : α →₀ ℕ) (f : α → β) :
    (((ν.support.sort (fun a b => a ≤ b)).flatMap fun q => List.replicate (ν q) (f q) :
        List β) : Multiset β) = (Finsupp.toMultiset ν).map f := by
  classical
  have hcoe : ∀ l : List α,
      ((l.flatMap fun q => List.replicate (ν q) (f q) : List β) : Multiset β) =
        (l.map fun q => ν q • ({f q} : Multiset β)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons q l ih =>
        change (List.replicate (ν q) (f q) : Multiset β) +
            (List.flatMap (fun q => List.replicate (ν q) (f q)) l : Multiset β) = _
        rw [Multiset.coe_replicate, ih]
        simp [Multiset.nsmul_singleton]
  rw [hcoe]
  have hs := congrArg Multiset.sum (congrArg (Multiset.map fun q : α =>
      ν q • ({f q} : Multiset β)) (ν.support.sort_eq (fun a b => a ≤ b)))
  rw [Multiset.map_coe, Multiset.sum_coe] at hs
  rw [hs, Finsupp.toMultiset_map, Finsupp.mapDomain, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finsupp.toMultiset_single]

theorem expWord_toMultiset (μ : RLetter →₀ ℕ) :
    (expWord μ : Multiset RLetter) = Finsupp.toMultiset μ := by
  have h := flatMap_replicate_coe μ id
  simpa [expWord] using h

theorem expWord_pairwise (μ : RLetter →₀ ℕ) :
    (expWord μ).Pairwise (fun a b => a ≤ b) := by
  classical
  have haux : ∀ l : List RLetter, l.Pairwise (fun a b => a ≤ b) →
      (l.flatMap fun q => List.replicate (μ q) q).Pairwise (fun a b => a ≤ b) := by
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

/-- Two sorted lists with the same multiset are equal. -/
theorem eq_of_sorted_of_coe_eq {l l' : List RLetter} (hl : l.Pairwise (fun a b => a ≤ b))
    (hl' : l'.Pairwise (fun a b => a ≤ b)) (h : (l : Multiset RLetter) = l') : l = l' :=
  (Multiset.coe_eq_coe.mp h).eq_of_pairwise' hl hl'

/-- A sorted list is the exponent word of its multiplicity function. -/
theorem eq_expWord_toFinsupp (l : List RLetter) (hl : l.Pairwise (fun a b => a ≤ b)) :
    l = expWord (Multiset.toFinsupp (l : Multiset RLetter)) := by
  classical
  apply eq_of_sorted_of_coe_eq hl (expWord_pairwise _)
  rw [expWord_toMultiset, Multiset.toFinsupp_toMultiset]

/-- Inserting one letter into an exponent word. -/
theorem expWord_add_single (μ : RLetter →₀ ℕ) (q : RLetter) :
    expWord (μ + Finsupp.single q 1) = (expWord μ).orderedInsert (fun a b => a ≤ b) q := by
  classical
  apply eq_of_sorted_of_coe_eq (expWord_pairwise _)
  · exact List.Pairwise.orderedInsert q _ (expWord_pairwise μ)
  · rw [Multiset.coe_eq_coe.mpr (List.perm_orderedInsert (fun a b => a ≤ b) q (expWord μ)),
      ← Multiset.cons_coe, expWord_toMultiset, expWord_toMultiset, map_add,
      Finsupp.toMultiset_single, one_smul, add_comm, Multiset.singleton_add]

/-! ## §4  The rank-ordered creation states -/

/-- The rank-ordered creation state `f^λ h^ν e^μ |0⟩` of an exponent function. -/
def Fvec (μ : RLetter →₀ ℕ) : WakModule k := rword k (expWord μ)

/-- A sorted word is a rank-ordered creation state. -/
theorem rword_sorted (l : List RLetter) (hl : l.Pairwise (fun a b => a ≤ b)) :
    rword k l = Fvec k (Multiset.toFinsupp (l : Multiset RLetter)) := by
  rw [Fvec, ← eq_expWord_toFinsupp l hl]

/-- Every rank word lies in the span of the rank-ordered states. -/
theorem rword_mem_span_Fvec (l : List RLetter) :
    rword k l ∈ Submodule.span ℂ (Set.range (Fvec k)) := by
  refine straighten (P := fun l => rword k l ∈ Submodule.span ℂ (Set.range (Fvec k)))
    (fun l hl => ?_) (fun pre a b post _ hswap hbr => ?_) l
  · dsimp only
    rw [rword_sorted k l hl]
    exact Submodule.subset_span ⟨_, rfl⟩
  · dsimp only at hswap hbr ⊢
    rw [rword_swap]
    refine Submodule.add_mem _ hswap (Submodule.sum_mem _ fun c _ => ?_)
    by_cases hc : fabc (col a) (col b) c = 0
    · rw [hc, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (hbr c hc)

/-- The colour-and-depth letter as a rank letter. -/
def toRank (p : Fin 3 × ℕ) : RLetter := toLex (colorRank p.1, p.2)

@[simp] theorem letterPair_toRank (p : Fin 3 × ℕ) : letterPair (toRank p) = p := by
  obtain ⟨a, n⟩ := p
  simp [letterPair, toRank]

/-- **Spanning.** -/
theorem Fvec_span_eq_top : Submodule.span ℂ (Set.range (Fvec k)) = ⊤ := by
  rw [eq_top_iff, ← wordStateA_span k, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  have h := rword_mem_span_Fvec k (l.map toRank)
  have hl : (l.map toRank).map letterPair = l := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id l]
    congr 1
    funext p
    exact letterPair_toRank p
  rwa [rword, hl] at h

/-! ## §5  Linear independence via the Wakimoto leading term -/

theorem classicalWordState_eq_prod (l : List (Fin 3 × ℕ)) :
    classicalWordState k l = (l.map fun p => currentClassical k p.1 p.2).prod := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      obtain ⟨a, n⟩ := p
      rw [classicalWordState_cons, ih]
      rfl

theorem classicalWordState_perm {l l' : List (Fin 3 × ℕ)} (h : l.Perm l') :
    classicalWordState k l = classicalWordState k l' := by
  rw [classicalWordState_eq_prod, classicalWordState_eq_prod]
  exact (h.map _).prod_eq

/-- The colour-ordered letter of a rank letter. -/
def toColorLetter (q : RLetter) : Fin 3 ×ₗ ℕ := toLex (col q, dep q)

theorem toColorLetter_injective : Function.Injective toColorLetter := by
  intro p q h
  have h1 := congrArg (fun x => (ofLex x).1) h
  have h2 := congrArg (fun x => (ofLex x).2) h
  simp only [toColorLetter, ofLex_toLex, col, dep] at h1 h2
  have h1' := rankColor_injective h1
  exact (ofLex.injective (Prod.ext h1' h2))

/-- Relabel a rank exponent as a colour exponent. -/
def relabel (μ : RLetter →₀ ℕ) : (Fin 3 ×ₗ ℕ) →₀ ℕ := Finsupp.mapDomain toColorLetter μ

theorem relabel_injective : Function.Injective relabel :=
  Finsupp.mapDomain_injective toColorLetter_injective

theorem expWord_map_perm (μ : RLetter →₀ ℕ) :
    ((expWord μ).map letterPair).Perm (orderedPBWColorWord (relabel μ)) := by
  rw [← Multiset.coe_eq_coe]
  have h1 : (((expWord μ).map letterPair : List (Fin 3 × ℕ)) : Multiset (Fin 3 × ℕ)) =
      (Finsupp.toMultiset μ).map letterPair := by
    rw [← Multiset.map_coe, expWord_toMultiset]
  have h2 := flatMap_replicate_coe (relabel μ) (fun q => ((ofLex q).1, (ofLex q).2))
  rw [h1, orderedPBWColorWord, h2, relabel, ← Finsupp.toMultiset_map μ toColorLetter,
    Multiset.map_map]
  rfl

/-- **Linear independence** of the rank-ordered creation states (`k + 2 ≠ 0`). -/
theorem Fvec_linearIndependent (hk : k + 2 ≠ 0) : LinearIndependent ℂ (Fvec k) := by
  apply LinearIndependent.of_comp (vacuumToWak k hk)
  have hf : ⇑(vacuumToWak k hk) ∘ Fvec k =
      fun μ => wakimotoWordState k ((expWord μ).map letterPair) := by
    funext μ
    exact vacuumToWak_wordStateA k hk _
  rw [hf]
  apply linearIndependent_of_lowerLeading
    (fun μ => wordFreeLiDegree ((expWord μ).map letterPair))
    (fun μ => wakimotoWordState k ((expWord μ).map letterPair))
    (fun μ => classicalWordState k ((expWord μ).map letterPair))
    (fun n => MvPolynomial.weightedHomogeneousComponent freeLiWeight n)
  · intro μ
    exact weightedComponent_wakimotoWordState_min k _
  · intro μ n hn
    exact weightedComponent_wakimotoWordState_eq_zero k _ n hn
  · have hlead : (fun μ => classicalWordState k ((expWord μ).map letterPair)) =
        classicalOrderedCreationState k ∘ relabel := by
      funext μ
      exact classicalWordState_perm k (expWord_map_perm μ)
    rw [hlead]
    exact (classicalOrderedCreationState_linearIndependent k).comp _ relabel_injective

/-- **The `(f, h, e)`-ordered PBW basis** of `V^k(sl₂)`. -/
def Fbasis (hk : k + 2 ≠ 0) : Module.Basis (RLetter →₀ ℕ) ℂ (WakModule k) :=
  Module.Basis.mk (Fvec_linearIndependent k hk) (Fvec_span_eq_top k).ge

@[simp] theorem Fbasis_apply (hk : k + 2 ≠ 0) (μ : RLetter →₀ ℕ) :
    Fbasis k hk μ = Fvec k μ :=
  Module.Basis.mk_apply _ _ _

end

end VOA.TwoSeries.SliceMap
