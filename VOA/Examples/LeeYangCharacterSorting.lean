import VOA.Examples.VirasoroGoodFiltration

/-!
# Length-controlled sorting of Virasoro creation words

The repository's sorting lemma `VirModule.negWordVir_mem_sortedSpanVir` tracks only the
energy.  Here the same straightening is redone while tracking the **PBW length**:

* `negWordVir_mem_virFil_length` — every creation word (in any order) lies in the length
  filtration step `virFil c w.length (energyVir w)`;
* `negWordVir_sub_insertionSort_mem` — a word and its sorted rearrangement differ by an element
  of the strictly smaller step `virFil c (w.length - 1)`.

So the associated graded of the length filtration on `V(c,0)` is commutative, for every `c`.
Everything here is proved; no hypothesis is introduced.
-/

namespace VOA.LeeYangCharacter

open VOA.VirModule VOA.VirGoodFil

variable (c : ℂ)

/-- Energy is the sum of the entries plus twice the length. -/
theorem energyVir_eq_sum (w : List ℕ) : energyVir w = w.sum + 2 * w.length := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [energyVir_cons, List.sum_cons, List.length_cons, ih]; ring

/-- Energy is invariant under rearrangement. -/
theorem energyVir_perm {w w' : List ℕ} (h : w.Perm w') : energyVir w = energyVir w' := by
  rw [energyVir_eq_sum, energyVir_eq_sum, h.sum_eq, h.length_eq]

/-- A sorted word of length at most `ℓ` and energy `N` lies in `virFil c ℓ N`. -/
theorem negWordVir_mem_virFil_of_sorted {u : List ℕ} (hu : SortedWord u) {ℓ N : ℕ}
    (hl : u.length ≤ ℓ) (hN : energyVir u = N) :
    negWordVir c u ∈ virFil c ℓ (N : ℤ) :=
  Submodule.subset_span ⟨u, hu, by exact_mod_cast hN, hl, rfl⟩

/-- Transport of a length-raising insertion property from generators to the whole step. -/
theorem virFil_stable {ℓ N : ℕ}
    (H : ∀ w : List ℕ, energyVir w = N → SortedWord w → w.length ≤ ℓ → ∀ n : ℕ,
      Lop c (-(n : ℤ) - 2) (negWordVir c w) ∈ virFil c (ℓ + 1) ((N + n + 2 : ℕ) : ℤ))
    (n : ℕ) {v : VirUniv c} (hv : v ∈ virFil c ℓ (N : ℤ)) :
    Lop c (-(n : ℤ) - 2) v ∈ virFil c (ℓ + 1) ((N + n + 2 : ℕ) : ℤ) := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨u, hu, hen, hlen, rfl⟩ := hy
      exact H u (by exact_mod_cast hen) hu hlen n
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- **Length-tracked insertion.**  One more creation mode applied to a sorted word of length
`≤ ℓ` lands in the sorted span of length `≤ ℓ + 1`. -/
theorem Lop_insert_virFil (N : ℕ) :
    ∀ w : List ℕ, energyVir w = N → SortedWord w → ∀ ℓ : ℕ, w.length ≤ ℓ → ∀ n : ℕ,
      Lop c (-(n : ℤ) - 2) (negWordVir c w) ∈ virFil c (ℓ + 1) ((N + n + 2 : ℕ) : ℤ) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w hw hsort ℓ hℓ n
    match w with
    | [] =>
        have hN : N = 0 := by rw [← hw]; rfl
        subst hN
        exact negWordVir_mem_virFil_of_sorted c (sortedWord_singleton n) (by simp)
          (by simp only [energyVir_cons, energyVir_nil]; omega)
    | (j :: rest) =>
        have hw' : (j + 2) + energyVir rest = N := by rw [← hw, energyVir_cons]
        have hlen : rest.length + 1 ≤ ℓ := by simpa using hℓ
        have hstep : Lop c (-(n : ℤ) - 2) (negWordVir c (j :: rest))
            = negWordVir c (n :: j :: rest) := rfl
        rw [hstep]
        rcases Nat.lt_or_ge n j with hnj | hjn
        · rw [negWordVir_swap]
          refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
          · have h1 : Lop c (-(n : ℤ) - 2) (negWordVir c rest)
                ∈ virFil c (rest.length + 1) ((energyVir rest + n + 2 : ℕ) : ℤ) :=
              ih _ (by omega) rest rfl hsort.tail rest.length le_rfl n
            have h2 := virFil_stable c
              (fun w hw hs hl m => ih _ (by omega) w hw hs _ hl m) j h1
            have hrw : energyVir rest + n + 2 + j + 2 = N + n + 2 := by omega
            rw [hrw] at h2
            exact virFil_mono c _ (by omega) h2
          · refine negWordVir_mem_virFil_of_sorted c (SortedWord.cons hsort.tail ?_) ?_ ?_
            · intro b hb
              exact le_trans (hsort.head_ge b hb) (by omega)
            · simp only [List.length_cons]; omega
            · simp only [energyVir_cons]; omega
        · refine negWordVir_mem_virFil_of_sorted c (SortedWord.cons hsort ?_) ?_ ?_
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact hjn
            · exact le_trans (hsort.head_ge b hb') hjn
          · simp only [List.length_cons]; omega
          · simp only [energyVir_cons]; omega

/-- Creation modes raise the length filtration by at most one. -/
theorem Lop_mem_virFil_succ {ℓ N : ℕ} (n : ℕ) {v : VirUniv c} (hv : v ∈ virFil c ℓ (N : ℤ)) :
    Lop c (-(n : ℤ) - 2) v ∈ virFil c (ℓ + 1) ((N + n + 2 : ℕ) : ℤ) :=
  virFil_stable c (fun w hw hs hl m => Lop_insert_virFil c N w hw hs ℓ hl m) n hv

/-- Every creation word, in any order, lies in the step of its own length and energy. -/
theorem negWordVir_mem_virFil_length (w : List ℕ) :
    negWordVir c w ∈ virFil c w.length (energyVir w : ℤ) := by
  induction w with
  | nil => exact negWordVir_mem_virFil_of_sorted c sortedWord_nil le_rfl rfl
  | cons a w ih =>
      have h := Lop_mem_virFil_succ c a ih
      rw [show energyVir w + a + 2 = energyVir (a :: w) by rw [energyVir_cons]; omega] at h
      simpa using h

/-- A word of length at most `ℓ` lies in `virFil c ℓ` at its energy. -/
theorem negWordVir_mem_virFil {w : List ℕ} {ℓ N : ℕ} (hl : w.length ≤ ℓ)
    (hN : energyVir w = N) : negWordVir c w ∈ virFil c ℓ (N : ℤ) := by
  subst hN
  exact virFil_mono c _ hl (negWordVir_mem_virFil_length c w)

/-- **Refined insertion.**  Prepending a mode to a sorted word differs from inserting it in sorted
position by an element of the step of the *old* length (one less than the new length). -/
theorem negWordVir_cons_sub_orderedInsert (N : ℕ) :
    ∀ w : List ℕ, energyVir w = N → SortedWord w → ∀ n : ℕ,
      negWordVir c (n :: w) - negWordVir c (w.orderedInsert (· ≥ ·) n)
        ∈ virFil c w.length ((N + n + 2 : ℕ) : ℤ) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w hw hsort n
    match w with
    | [] => simp
    | (j :: rest) =>
        have hw' : (j + 2) + energyVir rest = N := by rw [← hw, energyVir_cons]
        rcases Nat.lt_or_ge n j with hnj | hjn
        · have hins : (j :: rest).orderedInsert (· ≥ ·) n = j :: rest.orderedInsert (· ≥ ·) n := by
            simp [List.orderedInsert_cons, show ¬ (n ≥ j) by omega]
          rw [hins, negWordVir_swap]
          have hd := ih _ (by omega) rest rfl hsort.tail n
          have h2 := Lop_mem_virFil_succ c j hd
          have hrw : energyVir rest + n + 2 + j + 2 = N + n + 2 := by omega
          rw [hrw] at h2
          have hm : negWordVir c ((n + j + 2) :: rest)
              ∈ virFil c (j :: rest).length ((N + n + 2 : ℕ) : ℤ) :=
            negWordVir_mem_virFil c (by simp) (by simp only [energyVir_cons]; omega)
          have hcalc : negWordVir c (j :: n :: rest) + ((j : ℂ) - (n : ℂ)) •
                negWordVir c ((n + j + 2) :: rest) -
              negWordVir c (j :: rest.orderedInsert (· ≥ ·) n) =
              Lop c (-(j : ℤ) - 2) (negWordVir c (n :: rest) -
                negWordVir c (rest.orderedInsert (· ≥ ·) n)) +
              ((j : ℂ) - (n : ℂ)) • negWordVir c ((n + j + 2) :: rest) := by
            rw [map_sub]; simp only [negWordVir_cons]; abel
          rw [hcalc]
          refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hm)
          simpa using h2
        · have hins : (j :: rest).orderedInsert (· ≥ ·) n = n :: j :: rest := by
            simp [List.orderedInsert_cons, hjn]
          rw [hins, sub_self]
          exact Submodule.zero_mem _

/-- The sorted rearrangement of a word. -/
def sortDesc (w : List ℕ) : List ℕ := w.insertionSort (· ≥ ·)

theorem sortDesc_perm (w : List ℕ) : (sortDesc w).Perm w := List.perm_insertionSort _ w

theorem sortDesc_sorted (w : List ℕ) : SortedWord (sortDesc w) := by
  unfold SortedWord sortDesc
  exact List.pairwise_insertionSort _ _

theorem energyVir_sortDesc (w : List ℕ) : energyVir (sortDesc w) = energyVir w :=
  energyVir_perm (sortDesc_perm w)

theorem length_sortDesc (w : List ℕ) : (sortDesc w).length = w.length :=
  (sortDesc_perm w).length_eq

/-- **Commutativity of the associated graded.**  Any creation word and its sorted
rearrangement differ by an element of the length step one below. -/
theorem negWordVir_sub_sortDesc_mem (w : List ℕ) :
    negWordVir c w - negWordVir c (sortDesc w)
      ∈ virFil c (w.length - 1) (energyVir w : ℤ) := by
  induction w with
  | nil => simp [sortDesc]
  | cons a ws ih =>
      have hsort : sortDesc (a :: ws) = (sortDesc ws).orderedInsert (· ≥ ·) a := rfl
      have h1 := negWordVir_cons_sub_orderedInsert c (energyVir ws) (sortDesc ws)
        (energyVir_sortDesc ws) (sortDesc_sorted ws) a
      rw [length_sortDesc] at h1
      have hE : energyVir ws + a + 2 = energyVir (a :: ws) := by rw [energyVir_cons]; omega
      rw [hE] at h1
      have hcalc : negWordVir c (a :: ws) - negWordVir c (sortDesc (a :: ws)) =
          Lop c (-(a : ℤ) - 2) (negWordVir c ws - negWordVir c (sortDesc ws)) +
          (negWordVir c (a :: sortDesc ws) -
            negWordVir c ((sortDesc ws).orderedInsert (· ≥ ·) a)) := by
        rw [hsort, map_sub]; simp only [negWordVir_cons]; abel
      rw [hcalc, List.length_cons, Nat.add_sub_cancel]
      refine Submodule.add_mem _ ?_ h1
      rcases ws with _ | ⟨b, ws'⟩
      · simp [sortDesc]
      · have h2 := Lop_mem_virFil_succ c a ih
        rw [hE] at h2
        simpa using h2

end VOA.LeeYangCharacter
