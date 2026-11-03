/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.LiFiltration

/-!
# Ordered generator words, and the straightening theorem

Building on `Modularity.LiFiltration` (Li's `C₂`-filtration `Gfil` and the three estimates
KEY-1/2/3), this file performs the **straightening** step of Karel–Li / Gaberdiel–Neitzke /
Buhl: modulo one level of the filtration, every word can be rewritten as a **sorted** word in
the finitely many generators.

## Contents

* `genWord gen wt l` — the admissible `Letter`-word attached to a list of *pairs*
  `l : List (Fin g × ℕ)`, the pair `(i, m)` meaning the mode `(gen i)₍₋m₋₁₎`.
* `OrdPairs l` — the list of pairs is sorted for the **lexicographic** order on `Fin g × ℕ`
  (generator index major, mode depth minor) — exactly the normal form of
  `Modularity.GrowthBound.orderedMonomial`.
* `ordSpan A B gen wt π p` — the span of sorted generator words of level `≥ p`, all of whose
  pairs are `≥ π`, applied to `B`; `ordSpanAll` drops the `π` constraint.
* **`reorder`** (the straightening lemma): for any generator mode `(gen i₀)₍₋m₀₋₁₎` and any
  sorted word `l`,
  `(gen i₀)₍₋m₀₋₁₎ · wordAct (genWord l) w ∈ ordSpan π (level l + m₀) ⊔ Gfil (level l + m₀ + 1)`.
  Bubble-sort by induction on `l`: the out-of-order case swaps two adjacent modes, and KEY-3
  says the commutator error costs exactly one filtration level.
* **`master`**: `Gfil p ≤ ordSpanAll p ⊔ Gfil (p+1)` — granted only that `𝒱` is spanned by
  the generators, the vacuum, and `O₂ W` (`hdec`).  Induction on the word: each letter splits
  into its generator part (handled by `reorder`), its vacuum part (a mode of `𝟙`, which is
  either the identity or `0`), and its `C₂` part (killed one level up by KEY-2).

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Ordered

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-! ## Generator words -/

/-- The admissible `Letter`-word of a list of pairs: `(i, m) ↦ (gen i)₍₋m₋₁₎`. -/
def genWord {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (l : List (Fin g × ℕ)) :
    List (Letter 𝒱) :=
  l.map (fun q => (gen q.1, wt q.1, q.2))

@[simp] theorem genWord_nil {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ) :
    genWord gen wt [] = [] := rfl

@[simp] theorem genWord_cons {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (q : Fin g × ℕ)
    (l : List (Fin g × ℕ)) :
    genWord gen wt (q :: l) = (gen q.1, wt q.1, q.2) :: genWord gen wt l := rfl

/-- The **level** of a list of pairs: `Σ mᵢ`. -/
def pairsLevel {g : ℕ} (l : List (Fin g × ℕ)) : ℕ := (l.map Prod.snd).sum

@[simp] theorem pairsLevel_nil {g : ℕ} : pairsLevel ([] : List (Fin g × ℕ)) = 0 := rfl

@[simp] theorem pairsLevel_cons {g : ℕ} (q : Fin g × ℕ) (l : List (Fin g × ℕ)) :
    pairsLevel (q :: l) = q.2 + pairsLevel l := rfl

theorem wordLevel_genWord {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (l : List (Fin g × ℕ)) :
    wordLevel (genWord gen wt l) = pairsLevel l := by
  induction l with
  | nil => rfl
  | cons q t ih => simp only [genWord_cons, wordLevel_cons, pairsLevel_cons, ih]

theorem genWord_ok {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) (l : List (Fin g × ℕ)) :
    WordOK W (genWord gen wt l) := by
  intro p hp
  rw [genWord, List.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  exact hgen q.1

/-- A generator word lies in the corresponding filtration piece. -/
theorem genWord_mem_Gfil (A : WeakModule W M) (B : Set M) {g : ℕ} {gen : Fin g → 𝒱}
    {wt : Fin g → ℕ} (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) (l : List (Fin g × ℕ))
    {w : M} (hw : w ∈ B) {p : ℤ} (hp : p ≤ (pairsLevel l : ℤ)) :
    wordAct A (genWord gen wt l) w ∈ Gfil A B p :=
  wordAct_mem_Gfil A B (genWord_ok hgen l) hw (by rwa [wordLevel_genWord])

/-! ## Sorted words -/

/-- The list of pairs is **sorted** for the lexicographic order (generator index major). -/
def OrdPairs {g : ℕ} (l : List (Fin g × ℕ)) : Prop :=
  List.Pairwise (fun a b : Fin g × ℕ => toLex a ≤ toLex b) l

theorem OrdPairs_nil {g : ℕ} : OrdPairs ([] : List (Fin g × ℕ)) := List.Pairwise.nil

theorem OrdPairs_cons {g : ℕ} {q : Fin g × ℕ} {l : List (Fin g × ℕ)}
    (hq : ∀ r ∈ l, toLex q ≤ toLex r) (hl : OrdPairs l) : OrdPairs (q :: l) :=
  List.pairwise_cons.mpr ⟨hq, hl⟩

theorem OrdPairs_of_cons {g : ℕ} {q : Fin g × ℕ} {l : List (Fin g × ℕ)}
    (h : OrdPairs (q :: l)) : (∀ r ∈ l, toLex q ≤ toLex r) ∧ OrdPairs l :=
  List.pairwise_cons.mp h

/-! ## The ordered span -/

/-- The span of the **sorted** generator words of level `≥ p` all of whose pairs are `≥ π`,
applied to the bottom set `B`. -/
def ordSpan (A : WeakModule W M) (B : Set M) {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (π : Lex (Fin g × ℕ)) (p : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ (l : List (Fin g × ℕ)) (w : M), OrdPairs l ∧
    (∀ q ∈ l, π ≤ toLex q) ∧ p ≤ pairsLevel l ∧ w ∈ B ∧ x = wordAct A (genWord gen wt l) w}

/-- The span of all sorted generator words of level `≥ p` applied to `B`. -/
def ordSpanAll (A : WeakModule W M) (B : Set M) {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (p : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ (l : List (Fin g × ℕ)) (w : M), OrdPairs l ∧
    p ≤ pairsLevel l ∧ w ∈ B ∧ x = wordAct A (genWord gen wt l) w}

theorem ordSpan_le_ordSpanAll (A : WeakModule W M) (B : Set M) {g : ℕ} (gen : Fin g → 𝒱)
    (wt : Fin g → ℕ) (π : Lex (Fin g × ℕ)) (p : ℕ) :
    ordSpan A B gen wt π p ≤ ordSpanAll A B gen wt p := by
  refine Submodule.span_mono ?_
  rintro x ⟨l, w, hl, _, hp, hw, rfl⟩
  exact ⟨l, w, hl, hp, hw, rfl⟩

theorem ordSpan_antitone (A : WeakModule W M) (B : Set M) {g : ℕ} (gen : Fin g → 𝒱)
    (wt : Fin g → ℕ) {π π' : Lex (Fin g × ℕ)} (hππ : π ≤ π') {p p' : ℕ} (hp : p ≤ p') :
    ordSpan A B gen wt π' p' ≤ ordSpan A B gen wt π p := by
  refine Submodule.span_mono ?_
  rintro x ⟨l, w, hl, hπ', hp', hw, rfl⟩
  exact ⟨l, w, hl, fun q hq => le_trans hππ (hπ' q hq), le_trans hp hp', hw, rfl⟩

theorem ordSpanAll_antitone (A : WeakModule W M) (B : Set M) {g : ℕ} (gen : Fin g → 𝒱)
    (wt : Fin g → ℕ) {p p' : ℕ} (hp : p ≤ p') :
    ordSpanAll A B gen wt p' ≤ ordSpanAll A B gen wt p := by
  refine Submodule.span_mono ?_
  rintro x ⟨l, w, hl, hp', hw, rfl⟩
  exact ⟨l, w, hl, le_trans hp hp', hw, rfl⟩

theorem mem_ordSpan_of_word (A : WeakModule W M) (B : Set M) {g : ℕ} (gen : Fin g → 𝒱)
    (wt : Fin g → ℕ) {π : Lex (Fin g × ℕ)} {p : ℕ} {l : List (Fin g × ℕ)} {w : M}
    (hl : OrdPairs l) (hπ : ∀ q ∈ l, π ≤ toLex q) (hp : p ≤ pairsLevel l) (hw : w ∈ B) :
    wordAct A (genWord gen wt l) w ∈ ordSpan A B gen wt π p :=
  Submodule.subset_span ⟨l, w, hl, hπ, hp, hw, rfl⟩

/-- **Prepending a minimal pair to the ordered span.**  If `(i₁, m₁)` is `≥ π` and `π'` is the
bound `toLex (i₁, m₁)`, then `(gen i₁)₍₋m₁₋₁₎ · ordSpan π' p ⊆ ordSpan π (p + m₁)`. -/
theorem ordSpan_prepend (A : WeakModule W M) (B : Set M) {g : ℕ} (gen : Fin g → 𝒱)
    (wt : Fin g → ℕ) {π : Lex (Fin g × ℕ)} (i₁ : Fin g) (m₁ : ℕ)
    (hπ : π ≤ toLex (i₁, m₁)) {p : ℕ} {x : M} (hx : x ∈ ordSpan A B gen wt (toLex (i₁, m₁)) p) :
    mode (A.YM (gen i₁)) (-(m₁ : ℤ) - 1) x ∈ ordSpan A B gen wt π (p + m₁) := by
  refine Submodule.span_induction (p := fun x _ => mode (A.YM (gen i₁)) (-(m₁ : ℤ) - 1) x
      ∈ ordSpan A B gen wt π (p + m₁)) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, w, hl, hlπ, hp, hw, rfl⟩
    have hstep : mode (A.YM (gen i₁)) (-(m₁ : ℤ) - 1) (wordAct A (genWord gen wt l) w)
        = wordAct A (genWord gen wt ((i₁, m₁) :: l)) w := rfl
    rw [hstep]
    refine mem_ordSpan_of_word A B gen wt (OrdPairs_cons hlπ hl) ?_ ?_ hw
    · intro q hq
      rcases List.mem_cons.mp hq with h | h
      · exact h ▸ hπ
      · exact le_trans hπ (hlπ q h)
    · rw [pairsLevel_cons]; omega
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz; rw [map_add]; exact Submodule.add_mem _ hy hz
  · intro a y _ hy; rw [map_smul]; exact Submodule.smul_mem _ a hy

/-! ## A lower bound for a pair together with a list -/

/-- A pair-order lower bound for `(i₀, m₀)` and every entry of `l`. -/
def lowBound {g : ℕ} (i₀ : Fin g) (m₀ : ℕ) (l : List (Fin g × ℕ)) : Lex (Fin g × ℕ) :=
  l.foldr (fun q acc => min (toLex q) acc) (toLex (i₀, m₀))

theorem lowBound_le_head {g : ℕ} (i₀ : Fin g) (m₀ : ℕ) (l : List (Fin g × ℕ)) :
    lowBound i₀ m₀ l ≤ toLex (i₀, m₀) := by
  induction l with
  | nil => exact le_rfl
  | cons q t ih => exact le_trans (min_le_right _ _) ih

theorem lowBound_le_mem {g : ℕ} (i₀ : Fin g) (m₀ : ℕ) {l : List (Fin g × ℕ)} {q : Fin g × ℕ}
    (hq : q ∈ l) : lowBound i₀ m₀ l ≤ toLex q := by
  induction l with
  | nil => exact absurd hq (List.not_mem_nil)
  | cons r t ih =>
      rcases List.mem_cons.mp hq with h | h
      · exact h ▸ (min_le_left _ _)
      · exact le_trans (min_le_right _ _) (ih h)

/-! ## Pushing a linear map through a sup -/

theorem map_mem_sup' {P Q R : Submodule ℂ M} (F : Module.End ℂ M)
    (hP : ∀ x ∈ P, F x ∈ R) (hQ : ∀ x ∈ Q, F x ∈ R) {x : M} (hx : x ∈ P ⊔ Q) : F x ∈ R := by
  rw [Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [map_add]
  exact Submodule.add_mem _ (hP a ha) (hQ b hb)

theorem map_mem_sup {P Q P' Q' : Submodule ℂ M} (F : Module.End ℂ M)
    (hP : ∀ x ∈ P, F x ∈ P') (hQ : ∀ x ∈ Q, F x ∈ Q') {x : M} (hx : x ∈ P ⊔ Q) :
    F x ∈ P' ⊔ Q' := by
  rw [Submodule.mem_sup] at hx ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨F a, hP a ha, F b, hQ b hb, by rw [map_add]⟩

/-! ## The straightening (bubble-sort) lemma -/

/-- **Straightening.**  Applying one more generator mode `(gen i₀)₍₋m₀₋₁₎` to a *sorted*
generator word lands, **modulo one filtration level**, back in the ordered span.

Induction on the word.  If the new pair `(i₀, m₀)` already precedes the head, prepend it.
Otherwise swap it past the head: KEY-3 (`smul_comm_mem_Gfil`) says the commutator error costs
exactly one level, and the inductive hypothesis — applied with the head as the new lower bound
— straightens the rest; prepending the head afterwards is then legal. -/
theorem reorder (A : WeakModule W M) (B : Set M) (hLW : LWGenerated A B) {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    {w : M} (hw : w ∈ B) :
    ∀ (l : List (Fin g × ℕ)), OrdPairs l → ∀ (π : Lex (Fin g × ℕ)) (i₀ : Fin g) (m₀ : ℕ),
      π ≤ toLex (i₀, m₀) → (∀ q ∈ l, π ≤ toLex q) →
      mode (A.YM (gen i₀)) (-(m₀ : ℤ) - 1) (wordAct A (genWord gen wt l) w)
        ∈ ordSpan A B gen wt π (pairsLevel l + m₀)
            ⊔ Gfil A B ((pairsLevel l + m₀ : ℕ) + 1 : ℤ) := by
  intro l
  induction l with
  | nil =>
      intro _ π i₀ m₀ hπ _
      refine Submodule.mem_sup_left ?_
      have hstep : mode (A.YM (gen i₀)) (-(m₀ : ℤ) - 1) (wordAct A (genWord gen wt []) w)
          = wordAct A (genWord gen wt [(i₀, m₀)]) w := rfl
      rw [hstep]
      refine mem_ordSpan_of_word A B gen wt (OrdPairs_cons (by simp) OrdPairs_nil) ?_ ?_ hw
      · intro q hq
        rcases List.mem_cons.mp hq with h | h
        · exact h ▸ hπ
        · exact absurd h (List.not_mem_nil)
      · simp
  | cons q1 t ih =>
      intro hl π i₀ m₀ hπ hlπ
      obtain ⟨hq1t, ht⟩ := OrdPairs_of_cons hl
      have hq1π : π ≤ toLex q1 := hlπ q1 (List.mem_cons_self ..)
      rcases le_or_gt (toLex (i₀, m₀)) (toLex q1) with hle | hgt
      · -- already in order: prepend `(i₀, m₀)` in front
        refine Submodule.mem_sup_left ?_
        have hstep : mode (A.YM (gen i₀)) (-(m₀ : ℤ) - 1) (wordAct A (genWord gen wt (q1 :: t)) w)
            = wordAct A (genWord gen wt ((i₀, m₀) :: q1 :: t)) w := rfl
        rw [hstep]
        refine mem_ordSpan_of_word A B gen wt (OrdPairs_cons ?_ hl) ?_ ?_ hw
        · intro r hr
          rcases List.mem_cons.mp hr with h | h
          · exact h ▸ hle
          · exact le_trans hle (hq1t r h)
        · intro q hq
          rcases List.mem_cons.mp hq with h | h
          · exact h ▸ hπ
          · exact hlπ q h
        · simp only [pairsLevel_cons]; omega
      · -- out of order: swap past the head
        have hy : wordAct A (genWord gen wt t) w ∈ Gfil A B ((pairsLevel t : ℤ)) :=
          genWord_mem_Gfil A B hgen t hw le_rfl
        have hcomm := smul_comm_mem_Gfil A B hLW (hgen i₀) (hgen q1.1) m₀ q1.2 hy
        -- the swapped term, straightened by the inductive hypothesis
        have hih := ih ht (toLex q1) i₀ m₀ (le_of_lt hgt) hq1t
        have hpush : mode (A.YM (gen q1.1)) (-(q1.2 : ℤ) - 1)
            (mode (A.YM (gen i₀)) (-(m₀ : ℤ) - 1) (wordAct A (genWord gen wt t) w))
            ∈ ordSpan A B gen wt π (pairsLevel (q1 :: t) + m₀)
                ⊔ Gfil A B ((pairsLevel (q1 :: t) + m₀ : ℕ) + 1 : ℤ) := by
          refine map_mem_sup (mode (A.YM (gen q1.1)) (-(q1.2 : ℤ) - 1)) ?_ ?_ hih
          · intro x hx
            have := ordSpan_prepend A B gen wt (π := π) q1.1 q1.2 (by simpa using hq1π) hx
            refine (ordSpan_antitone A B gen wt (le_refl π) ?_) this
            simp only [pairsLevel_cons]; omega
          · intro x hx
            have := Gfil_prepend A B (b := wt q1.1) (n := q1.2) (hgen q1.1) hx
            refine (Gfil_antitone A B ?_) this
            simp only [pairsLevel_cons]; push_cast; omega
        -- assemble: `f₀ f₁ y = f₁ f₀ y + [f₀, f₁] y`
        have hsplit : mode (A.YM (gen i₀)) (-(m₀ : ℤ) - 1)
              (wordAct A (genWord gen wt (q1 :: t)) w)
            = mode (A.YM (gen q1.1)) (-(q1.2 : ℤ) - 1)
                (mode (A.YM (gen i₀)) (-(m₀ : ℤ) - 1) (wordAct A (genWord gen wt t) w))
              + (mode (A.YM (gen i₀)) (-(m₀ : ℤ) - 1)
                  (mode (A.YM (gen q1.1)) (-(q1.2 : ℤ) - 1) (wordAct A (genWord gen wt t) w))
                - mode (A.YM (gen q1.1)) (-(q1.2 : ℤ) - 1)
                    (mode (A.YM (gen i₀)) (-(m₀ : ℤ) - 1) (wordAct A (genWord gen wt t) w))) := by
          show _ = _
          abel
        rw [hsplit]
        refine Submodule.add_mem _ hpush (Submodule.mem_sup_right ?_)
        refine (Gfil_antitone A B ?_) hcomm
        simp only [pairsLevel_cons]; push_cast; omega

/-- `reorder`, spread over the whole ordered span. -/
theorem reorder_span (A : WeakModule W M) (B : Set M) (hLW : LWGenerated A B) {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (i₀ : Fin g) (m₀ : ℕ) {p : ℕ} {x : M} (hx : x ∈ ordSpanAll A B gen wt p) :
    mode (A.YM (gen i₀)) (-(m₀ : ℤ) - 1) x
      ∈ ordSpanAll A B gen wt (p + m₀) ⊔ Gfil A B ((p + m₀ : ℕ) + 1 : ℤ) := by
  refine Submodule.span_induction (p := fun x _ => mode (A.YM (gen i₀)) (-(m₀ : ℤ) - 1) x
      ∈ ordSpanAll A B gen wt (p + m₀) ⊔ Gfil A B ((p + m₀ : ℕ) + 1 : ℤ)) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, w, hl, hp, hw, rfl⟩
    have h := reorder A B hLW hgen hw l hl (lowBound i₀ m₀ l) i₀ m₀
      (lowBound_le_head i₀ m₀ l) (fun q hq => lowBound_le_mem i₀ m₀ hq)
    refine SetLike.le_def.mp (sup_le_sup ?_ ?_) h
    · exact le_trans (ordSpan_le_ordSpanAll A B gen wt _ _)
        (ordSpanAll_antitone A B gen wt (by omega))
    · exact Gfil_antitone A B (by push_cast; omega)
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz; rw [map_add]; exact Submodule.add_mem _ hy hz
  · intro a y _ hy; rw [map_smul]; exact Submodule.smul_mem _ a hy

/-! ## The master lemma -/

/-- **Master lemma, on word generators.**  Every admissible word on `B` is, modulo one
filtration level, a combination of **sorted generator words** of the same level.

Induction on the word.  The outermost letter `c` splits (by `hdec`) into a generator part — put
in place by `reorder_span` — a vacuum part (whose modes are `id` or `0`), and a `C₂` part, which
KEY-2 (`O₂_act_mem_Gfil`) sends one level up and hence into the error term. -/
theorem master_word (A : WeakModule W M) (B : Set M) (hLW : LWGenerated A B) {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hdec : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W) :
    ∀ (l : List (Letter 𝒱)), WordOK W l → ∀ {w : M}, w ∈ B →
      wordAct A l w ∈ ordSpanAll A B gen wt (wordLevel l)
        ⊔ Gfil A B ((wordLevel l : ℕ) + 1 : ℤ) := by
  intro l
  induction l with
  | nil =>
      intro _ w hw
      refine Submodule.mem_sup_left ?_
      exact Submodule.subset_span
        ⟨([] : List (Fin g × ℕ)), w, OrdPairs_nil, by simp, hw, rfl⟩
  | cons pc t ih =>
      intro hl w hw
      obtain ⟨hpc, ht⟩ := WordOK_of_cons hl
      have hIH := ih ht hw
      have hyG : wordAct A t w ∈ Gfil A B ((wordLevel t : ℤ)) :=
        wordAct_mem_Gfil A B ht hw le_rfl
      -- split the outermost letter `c = cS + cO`
      have hctop : pc.1 ∈ Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W :=
        hdec ▸ Submodule.mem_top
      rw [Submodule.mem_sup] at hctop
      obtain ⟨cS, hcS, cO, hcO, hcsum⟩ := hctop
      have hsplit : wordAct A (pc :: t) w
          = mode (A.YM cS) (-(pc.2.2 : ℤ) - 1) (wordAct A t w)
            + mode (A.YM cO) (-(pc.2.2 : ℤ) - 1) (wordAct A t w) := by
        rw [wordAct_cons, ← hcsum, map_add, mode_add, LinearMap.add_apply]
      rw [hsplit]
      refine Submodule.add_mem _ ?_ ?_
      · -- the `span (gen ∪ {𝟙})` part
        refine Submodule.span_induction
          (p := fun cS _ => mode (A.YM cS) (-(pc.2.2 : ℤ) - 1) (wordAct A t w)
            ∈ ordSpanAll A B gen wt (wordLevel (pc :: t))
              ⊔ Gfil A B ((wordLevel (pc :: t) : ℕ) + 1 : ℤ)) ?_ ?_ ?_ ?_ hcS
        · rintro c (⟨i, rfl⟩ | rfl)
          · -- a generator: straighten
            refine map_mem_sup' (mode (A.YM (gen i)) (-(pc.2.2 : ℤ) - 1)) ?_ ?_ hIH
            · intro x hx
              have h := reorder_span A B hLW hgen i pc.2.2 hx
              refine SetLike.le_def.mp (sup_le_sup ?_ ?_) h
              · exact ordSpanAll_antitone A B gen wt (by simp only [wordLevel_cons]; omega)
              · exact Gfil_antitone A B (by simp only [wordLevel_cons]; push_cast; omega)
            · intro x hx
              refine Submodule.mem_sup_right ?_
              have h := Gfil_prepend A B (b := wt i) (n := pc.2.2) (hgen i) hx
              refine (Gfil_antitone A B ?_) h
              simp only [wordLevel_cons]; push_cast; omega
          · -- the vacuum: `𝟙₍₋n₋₁₎` is the identity for `n = 0` and `0` otherwise
            have hvac : mode (A.YM W.vacuum) (-(pc.2.2 : ℤ) - 1) (wordAct A t w)
                = if (-(pc.2.2 : ℤ) - 1) = -1 then wordAct A t w else 0 :=
              A.act_vacuum _ _
            rw [hvac]
            by_cases hn : (-(pc.2.2 : ℤ) - 1) = -1
            · rw [if_pos hn]
              have hn0 : pc.2.2 = 0 := by omega
              refine SetLike.le_def.mp (sup_le_sup ?_ ?_) hIH
              · exact ordSpanAll_antitone A B gen wt (by simp only [wordLevel_cons, hn0]; omega)
              · exact Gfil_antitone A B (by simp only [wordLevel_cons, hn0]; push_cast; omega)
            · rw [if_neg hn]; exact Submodule.zero_mem _
        · simp only [map_zero, mode_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
        · intro c₁ c₂ _ _ h1 h2
          rw [map_add, mode_add, LinearMap.add_apply]
          exact Submodule.add_mem _ h1 h2
        · intro a c₁ _ h1
          rw [map_smul, mode_smul, LinearMap.smul_apply]
          exact Submodule.smul_mem _ a h1
      · -- the `C₂` part: KEY-2 sends it a level up
        refine Submodule.mem_sup_right ?_
        have h := O₂_act_mem_Gfil A B hLW hcO (-(pc.2.2 : ℤ) - 1) hyG
        refine (Gfil_antitone A B ?_) h
        simp only [wordLevel_cons]; push_cast; omega

/-- **The master lemma.**  Modulo one filtration level, the level-`p` piece of Li's
filtration is spanned by **sorted generator words** of level `≥ p`:

  `Gfil p ≤ ordSpanAll p ⊔ Gfil (p+1)`. -/
theorem master (A : WeakModule W M) (B : Set M) (hLW : LWGenerated A B) {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hdec : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    (p : ℕ) :
    Gfil A B (p : ℤ) ≤ ordSpanAll A B gen wt p ⊔ Gfil A B ((p : ℤ) + 1) := by
  rw [Gfil, Submodule.span_le]
  rintro x ⟨l, w, hl, hw, hlev, rfl⟩
  have h := master_word A B hLW hgen hdec l hl hw
  have hp : p ≤ wordLevel l := by simpa using hlev
  refine SetLike.le_def.mp (sup_le_sup ?_ ?_) h
  · exact ordSpanAll_antitone A B gen wt hp
  · exact Gfil_antitone A B (by omega)

end Ordered

end VOA
