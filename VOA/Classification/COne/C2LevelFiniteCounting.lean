import VOA.Classification.COne.C2LevelFiniteNormal

/-!
# Finitely many bounded-repetition words of a fixed level shift

Positive generator weights and the bound on repetitions imply finiteness at
fixed degree once the modes are bounded above. Sorting is not needed for this
counting result. The nonnegative-mode tail has bounded length; its possible
negative degree bounds the total magnitude of the negative modes.
-/
namespace VOA.Classification.COne.C2LevelFinite

open VOA.Huang.BuhlSpanning

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱}

/-- Actual change of admissible level, distinct from Buhl's weight filtration. -/
def degree (D : GenData W) (l : List (Ltr D)) : ℤ :=
  (l.map (fun a => (D.wt a.1 : ℤ) - a.2 - 1)).sum

@[simp] theorem degree_nil (D : GenData W) : degree D [] = 0 := rfl

@[simp] theorem degree_cons (D : GenData W) (a : Ltr D) (l : List (Ltr D)) :
    degree D (a :: l) = ((D.wt a.1 : ℤ) - a.2 - 1) + degree D l := by
  simp [degree]

/-- Lists over a finite alphabet with bounded multiplicities form a finite set. -/
theorem finite_lists_count_lt {α : Type*} [BEq α] [LawfulBEq α] (Al : Finset α) (Q : ℕ) :
    {l : List α | (∀ e ∈ l, e ∈ Al) ∧ ∀ a, l.count a < Q}.Finite := by
  classical
  set L := Al.card * Q
  have hsub : {l : List α | (∀ e ∈ l, e ∈ Al) ∧ ∀ a, l.count a < Q} ⊆
      {l | l.length ≤ L ∧ ∀ e ∈ l, e ∈ Al} := by
    intro m ⟨hAlm, hcount⟩
    refine ⟨?_, hAlm⟩
    rw [← List.sum_map_count_dedup_eq_length]
    have h1 : (m.dedup.map fun x => m.count x).sum ≤ m.dedup.length • Q := by
      have := List.sum_le_card_nsmul (m.dedup.map fun x => m.count x) Q (fun y hy => by
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
        exact le_of_lt (hcount x))
      simpa using this
    have h2 : m.dedup.length ≤ Al.card := by
      rw [← List.toFinset_card_of_nodup (List.nodup_dedup m)]
      refine Finset.card_le_card ?_
      intro e he
      rw [List.mem_toFinset, List.mem_dedup] at he
      exact hAlm e he
    have h3 : (m.dedup.map fun x => m.count x).sum ≤ Al.card * Q :=
      le_trans (by simpa using h1) (Nat.mul_le_mul_right Q h2)
    convert h3 using 4
    congr 1
    apply lawful_beq_subsingleton
  refine Set.Finite.subset ?_ hsub
  have hfin := (List.finite_length_le (↥Al) L).image (List.map Subtype.val)
  refine hfin.subset ?_
  rintro m ⟨hlen, hmem⟩
  refine ⟨m.pmap (fun e he => (⟨e, he⟩ : ↥Al)) hmem, ?_, ?_⟩
  · simpa [Set.mem_setOf_eq, List.length_pmap] using hlen
  · simp [List.map_pmap]

/-- Total magnitude of the negative modes. -/
def negativeCost (D : GenData W) (l : List (Ltr D)) : ℤ :=
  (l.map (fun a => max 0 (-a.2))).sum

/-- Nonnegative-mode letters of a word. -/
def nonnegativePart (D : GenData W) (l : List (Ltr D)) : List (Ltr D) :=
  l.filter (fun a => decide (0 ≤ a.2))

theorem negativeCost_nonneg (D : GenData W) (l : List (Ltr D)) :
    0 ≤ negativeCost D l := by
  exact List.sum_nonneg (fun a ha => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
    exact le_max_left _ _)

/-- Upper modes can offset only bounded negative-mode cost. -/
theorem negativeCost_le (D : GenData W) (Bm : ℕ) (l : List (Ltr D))
    (hlt : ∀ e ∈ l, e.2 < (Bm : ℤ)) :
    negativeCost D l ≤ degree D l + Bm * ((nonnegativePart D l).length : ℤ) := by
  induction l with
  | nil => simp [negativeCost, nonnegativePart]
  | cons a l ih =>
    have ih' := ih (fun e he => hlt e (List.mem_cons_of_mem a he))
    have ha := hlt a (List.mem_cons_self ..)
    have hw : (1 : ℤ) ≤ D.wt a.1 := by exact_mod_cast D.wt_pos a.1
    change max 0 (-a.2) + negativeCost D l ≤
      ((D.wt a.1 : ℤ) - a.2 - 1) + degree D l +
        Bm * ((nonnegativePart D (a :: l)).length : ℤ)
    by_cases hn : 0 ≤ a.2
    · have hp : (nonnegativePart D (a :: l)).length =
          (nonnegativePart D l).length + 1 := by simp [nonnegativePart, hn]
      rw [hp, Nat.cast_add, Nat.cast_one, max_eq_left (by omega : -a.2 ≤ 0)]
      nlinarith
    · have hp : nonnegativePart D (a :: l) = nonnegativePart D l := by
        simp [nonnegativePart, hn]
      rw [hp, max_eq_right (by omega : 0 ≤ -a.2)]
      omega

/-- Finitely many words have bounded repetitions, bounded upper modes, and fixed degree. -/
theorem fixedDegreeWords_finite (D : GenData W) (Q Bm : ℕ) (d : ℤ) :
    {l : List (Ltr D) | (∀ a, l.count a < Q) ∧
      (∀ e ∈ l, e.2 < (Bm : ℤ)) ∧ degree D l = d}.Finite := by
  classical
  let T := (innerSet_finite D Q Bm).toFinset
  let L := T.sup List.length
  have hinner : ∀ l : List (Ltr D), (∀ a, l.count a < Q) →
      (∀ e ∈ l, e.2 < (Bm : ℤ)) → (nonnegativePart D l).length ≤ L := by
    intro l hc hm
    apply Finset.le_sup (f := List.length)
    change nonnegativePart D l ∈ (innerSet_finite D Q Bm).toFinset
    rw [Set.Finite.mem_toFinset]
    constructor
    · intro e he
      have he' := List.mem_filter.mp he
      exact ⟨of_decide_eq_true he'.2, hm e he'.1⟩
    · intro a
      exact lt_of_le_of_lt (List.filter_sublist.count_le a) (hc a)
  let Al : Finset (Ltr D) := Finset.univ ×ˢ Finset.Icc (-(d + Bm * L)) (Bm : ℤ)
  apply (finite_lists_count_lt Al Q).subset
  rintro l ⟨hc, hm, hd⟩
  refine ⟨?_, hc⟩
  intro e he
  have hcost := negativeCost_le D Bm l hm
  have hlen : ((nonnegativePart D l).length : ℤ) ≤ L := by
    exact_mod_cast hinner l hc hm
  have hecost : max 0 (-e.2) ≤ negativeCost D l := by
    unfold negativeCost
    apply List.single_le_sum (fun a ha => ?_) _ (List.mem_map.mpr ⟨e, he, rfl⟩)
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
    exact le_max_left _ _
  have hmul := mul_le_mul_of_nonneg_left hlen (show (0 : ℤ) ≤ Bm by positivity)
  have hlo : -(d + (Bm : ℤ) * L) ≤ e.2 := by
    rw [hd] at hcost
    have := le_max_right 0 (-e.2)
    omega
  simpa only [Al, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
    using And.intro hlo (le_of_lt (hm e he))

end VOA.Classification.COne.C2LevelFinite
