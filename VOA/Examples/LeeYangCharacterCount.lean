import VOA.Examples.LeeYangCharacterSpanning
import VOA.Examples.LeeYangTransferAssemblyCharacter

/-!
# Counting gap-two words: the explicit bijection with `gapTwoCoefficient`

`LeeYangTransferAssembly.gapTwoCoefficient n r` counts tuples `a : Fin r → Fin (n+1)` with
`r(r+1) + Σ_j (j+1) a_j = n` (coefficient of `z^{r(r+1)} / Π_{j ≤ r} (1 - z^j)`).  Here it is
identified with the number of gap-two creation words of energy `n` and length `r`:

* `decGap` sends the multiplicity list `[a₀, …, a_{r-1}]` to the word whose bottom entry is
  `a_{r-1}` and whose consecutive differences are `2 + a_j`; `encGap` inverts it on gap-two words;
* `card_gapWords : (gapWords N r).card = gapTwoCoefficient N r`;
* `sum_leadingCoefficient_eq` — the Kähler-coordinate sum `Σ_{j ∈ [0,2p]} leadingCoefficient n j`
  equals `Σ_{r ≤ p} gapTwoCoefficient n r` (odd `j` contribute zero).

All proved.
-/

namespace VOA.LeeYangCharacter

open VOA.VirModule VOA.LeeYangTransferAssembly
open scoped BigOperators

/-! ## §1  The gap encoding -/

/-- `0` on the empty word, `x + 2` on a word with top entry `x`. -/
def shiftTop : List ℕ → ℕ
  | [] => 0
  | x :: _ => x + 2

/-- From multiplicities to the gap-two word. -/
def decGap : List ℕ → List ℕ
  | [] => []
  | g :: gs => (g + shiftTop (decGap gs)) :: decGap gs

/-- From a gap-two word back to the multiplicities. -/
def encGap : List ℕ → List ℕ
  | [] => []
  | [x] => [x]
  | x :: y :: rest => (x - y - 2) :: encGap (y :: rest)

/-- The weight `Σ_j (j+1) g_j` of a multiplicity list. -/
def gwt : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + gwt xs + xs.sum

theorem length_decGap (g : List ℕ) : (decGap g).length = g.length := by
  induction g with
  | nil => rfl
  | cons a g ih => simp [decGap, ih]

theorem gapTwo_decGap (g : List ℕ) : GapTwo (decGap g) := by
  induction g with
  | nil => exact List.IsChain.nil
  | cons a g ih =>
      unfold decGap
      cases h : decGap g with
      | nil => exact List.IsChain.singleton _
      | cons x t =>
          rw [h] at ih
          exact List.IsChain.cons_cons (by simp only [shiftTop]; omega) ih

theorem encGap_decGap (g : List ℕ) : encGap (decGap g) = g := by
  induction g with
  | nil => rfl
  | cons a g ih =>
      unfold decGap
      cases h : decGap g with
      | nil =>
          have : g = [] := by
            have := length_decGap g; rw [h] at this; exact List.length_eq_zero_iff.mp this.symm
          subst this
          simp [shiftTop, encGap]
      | cons x t =>
          rw [h] at ih
          simp only [shiftTop, encGap]
          rw [ih]
          congr 1
          omega

theorem decGap_encGap : ∀ {u : List ℕ}, GapTwo u → decGap (encGap u) = u
  | [], _ => rfl
  | [x], _ => by simp [encGap, decGap, shiftTop]
  | x :: y :: rest, h => by
      rw [GapTwo, List.isChain_cons_cons] at h
      have ih := decGap_encGap (u := y :: rest) h.2
      simp only [encGap, decGap]
      rw [show decGap (encGap (y :: rest)) = y :: rest from ih]
      simp only [shiftTop]
      congr 1
      omega

theorem length_encGap : ∀ (u : List ℕ), (encGap u).length = u.length
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by simp [encGap, length_encGap (y :: rest)]

theorem shiftTop_decGap (g : List ℕ) : shiftTop (decGap g) = g.sum + 2 * g.length := by
  induction g with
  | nil => rfl
  | cons a g ih =>
      show a + shiftTop (decGap g) + 2 = (a :: g).sum + 2 * (a :: g).length
      rw [ih]; simp only [List.sum_cons, List.length_cons]; ring

theorem energyVir_decGap (g : List ℕ) :
    energyVir (decGap g) = gwt g + g.length * (g.length + 1) := by
  induction g with
  | nil => rfl
  | cons a g ih =>
      simp only [decGap, energyVir_cons, ih, shiftTop_decGap, gwt, List.length_cons]
      ring

theorem le_gwt : ∀ (g : List ℕ), ∀ x ∈ g, x ≤ gwt g
  | [], _, h => absurd h (by simp)
  | a :: g, x, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp only [gwt]; omega
      · have := le_gwt g x h; simp only [gwt]; omega

theorem gwt_ofFn : ∀ {r : ℕ} (f : Fin r → ℕ),
    gwt (List.ofFn f) = ∑ j : Fin r, (j.val + 1) * f j
  | 0, f => by simp [gwt]
  | r + 1, f => by
      rw [List.ofFn_succ, gwt, gwt_ofFn, Fin.sum_univ_succ, List.sum_ofFn]
      simp only [Fin.val_zero, Fin.val_succ, zero_add, one_mul]
      rw [add_assoc, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

/-! ## §2  The finite set of gap-two words and its cardinality -/

/-- The weight condition of `gapTwoCoefficient`, over `ℕ`. -/
def WeightCond (N r : ℕ) (a : Fin r → Fin (N + 1)) : Prop :=
  r * (r + 1) + ∑ j : Fin r, (j.val + 1) * (a j).val = N

instance (N r : ℕ) : DecidablePred (WeightCond N r) := fun _ => by
  unfold WeightCond; infer_instance

/-- The word attached to a multiplicity tuple. -/
def tupleWord {N r : ℕ} (a : Fin r → Fin (N + 1)) : List ℕ :=
  decGap (List.ofFn fun j => (a j).val)

theorem tupleWord_injective {N r : ℕ} : Function.Injective (@tupleWord N r) := by
  intro a b h
  have h1 := congrArg encGap h
  simp only [tupleWord, encGap_decGap] at h1
  have h2 := List.ofFn_injective h1
  funext j
  exact Fin.ext (congrFun h2 j)

/-- Gap-two words of energy `N` and length exactly `r`. -/
def gapWords (N r : ℕ) : Finset (List ℕ) :=
  ((Finset.univ : Finset (Fin r → Fin (N + 1))).filter (WeightCond N r)).image tupleWord

theorem mem_gapWords {N r : ℕ} {u : List ℕ} :
    u ∈ gapWords N r ↔ GapTwo u ∧ energyVir u = N ∧ u.length = r := by
  constructor
  · rintro hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    rw [Finset.mem_filter] at ha
    refine ⟨gapTwo_decGap _, ?_, ?_⟩
    · rw [tupleWord, energyVir_decGap, gwt_ofFn, List.length_ofFn]
      have := ha.2; unfold WeightCond at this; omega
    · rw [tupleWord, length_decGap, List.length_ofFn]
  · rintro ⟨hg, hE, hl⟩
    set g := encGap u with hgdef
    have hgl : g.length = r := by rw [hgdef, length_encGap, hl]
    have hdec : decGap g = u := decGap_encGap hg
    have hEg : gwt g + r * (r + 1) = N := by
      rw [← hE, ← hdec, energyVir_decGap, hgl]
    have hbound : ∀ j : Fin r, g.get ⟨j.val, by omega⟩ < N + 1 := by
      intro j
      have := le_gwt g _ (List.get_mem g ⟨j.val, by omega⟩)
      omega
    let a : Fin r → Fin (N + 1) := fun j => ⟨g.get ⟨j.val, by omega⟩, hbound j⟩
    have hofFn : (List.ofFn fun j => (a j).val) = g := by
      apply List.ext_get (by simp [hgl])
      intro i h1 h2
      simp [a]
    refine Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · unfold WeightCond
      have := gwt_ofFn (fun j => (a j).val)
      rw [hofFn] at this
      omega
    · rw [tupleWord, hofFn, hdec]

theorem card_gapWords (N r : ℕ) : (gapWords N r).card = gapTwoCoefficient (N : ℤ) r := by
  classical
  rw [gapWords, Finset.card_image_of_injective _ tupleWord_injective, gapTwoCoefficient]
  rw [Fintype.card_subtype]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro a _
  unfold WeightCond
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- Gap-two words of energy `N` and length `≤ p`. -/
def gapWordsLe (N p : ℕ) : Finset (List ℕ) :=
  (Finset.range (p + 1)).biUnion (gapWords N)

theorem mem_gapWordsLe {N p : ℕ} {u : List ℕ} :
    u ∈ gapWordsLe N p ↔ GapTwo u ∧ energyVir u = N ∧ u.length ≤ p := by
  simp only [gapWordsLe, Finset.mem_biUnion, Finset.mem_range, mem_gapWords]
  constructor
  · rintro ⟨r, hr, hg, hE, hl⟩; exact ⟨hg, hE, by omega⟩
  · rintro ⟨hg, hE, hl⟩; exact ⟨u.length, by omega, hg, hE, rfl⟩

theorem card_gapWordsLe (N p : ℕ) :
    (gapWordsLe N p).card = ∑ r ∈ Finset.range (p + 1), gapTwoCoefficient (N : ℤ) r := by
  rw [gapWordsLe, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun r _ => card_gapWords N r
  · intro r _ s _ hrs
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hs
    rw [mem_gapWords] at hu hs
    exact hrs (hu.2.2.symm.trans hs.2.2)

/-- Words of energy `N` have length at most `N`, so the length bound `N` is no restriction. -/
theorem gapWordsLe_subset (N p : ℕ) : gapWordsLe N p ⊆ gapWordsLe N N := by
  intro u hu
  rw [mem_gapWordsLe] at hu ⊢
  refine ⟨hu.1, hu.2.1, ?_⟩
  have := VirGoodFil.length_le_energyVir u
  omega

/-! ## §3  The Kähler-coordinate reindexing -/

theorem gapTwoCoefficient_neg {n : ℤ} (hn : n < 0) (r : ℕ) : gapTwoCoefficient n r = 0 := by
  classical
  unfold gapTwoCoefficient
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨a, ha⟩ => ?_⟩
  have : (0 : ℤ) ≤ ((r * (r + 1) + ∑ j : Fin r, (j.val + 1) * (a j).val : ℕ) : ℤ) :=
    Int.natCast_nonneg _
  omega

theorem leadingCoefficient_even (n : ℤ) (r : ℕ) :
    leadingCoefficient n (2 * (r : ℤ)) = gapTwoCoefficient n r := by
  unfold leadingCoefficient
  rw [if_pos (by omega)]
  congr 1
  omega

theorem Icc_two_succ (p : ℕ) :
    Finset.Icc (0 : ℤ) (2 * ((p + 1 : ℕ) : ℤ)) =
      insert (2 * ((p + 1 : ℕ) : ℤ)) (insert (2 * (p : ℤ) + 1) (Finset.Icc 0 (2 * (p : ℤ)))) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_insert]
  push_cast
  omega

/-- The `2R` coordinate sum is the length-`≤ p` gap-two count. -/
theorem sum_leadingCoefficient_eq (n : ℤ) (p : ℕ) :
    ∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), leadingCoefficient n j =
      ∑ r ∈ Finset.range (p + 1), gapTwoCoefficient n r := by
  induction p with
  | zero =>
      simp only [Nat.cast_zero, mul_zero, Finset.Icc_self, Finset.sum_singleton, zero_add,
        Finset.range_one]
      exact leadingCoefficient_even n 0
  | succ p ih =>
      rw [Icc_two_succ, Finset.sum_insert, Finset.sum_insert, ih, leadingCoefficient_odd,
        leadingCoefficient_even, Finset.sum_range_succ _ (p + 1)]
      · ring
      · simp only [Finset.mem_Icc]; omega
      · simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega

end VOA.LeeYangCharacter
