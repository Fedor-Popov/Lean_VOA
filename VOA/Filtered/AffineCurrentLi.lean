/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Filtered.LiGeneratorWords
import VOA.Examples.AffineSl2Strong

/-!
# Current-word comparison for the affine Li filtration

For the universal affine `sl2` VOA, let `C_p` be the span of current creation words

`J^{a_1}_{-r_1-1} ... J^{a_s}_{-r_s-1} vacuum`

whose total derivative level `r_1 + ... + r_s` is at least `p`.  This file isolates the exact
comparison between `C_p` and Li's filtration `F^p`.

What is proved without a PBW basis or classical freeness:

* every current word is literally the corresponding generic generator word;
* `C_p = F^p` for every `p` in the universal noncritical affine `sl2` VOA;
* `C_0` is the whole universal affine vacuum module, using only the already proved spanning
  theorem `wordStateA_span`;
* Li filtration commutes with arbitrary graded VOA quotients;
* consequently, the intrinsic Li filtration of every graded affine quotient equals the image
  of the universal current-word filtration.

The main affine calculation is an all-integer normal-ordering estimate: a current-word mode
acting on `C_q` lands in the piece predicted by Li degree.  Its negative-mode case proves the
reverse inclusion `F^p <= C_p`.  This remains a spanning/straightening theorem, not PBW
independence and not classical freeness.
-/

namespace VOA
namespace AffineVOA
namespace CurrentLi

open VOA.AffineVOA.Inst

noncomputable section

/-- Total derivative level of an affine current creation word. -/
abbrev currentWordLevel (w : List (Fin 3 × ℕ)) : ℕ := pairsLevel w

/-- The span of current creation words of total derivative level at least `p`. -/
def currentWordPiece (k : ℂ) (p : ℕ) : Submodule ℂ (WakModule k) :=
  Submodule.span ℂ
    {x | ∃ w : List (Fin 3 × ℕ), p ≤ currentWordLevel w ∧ wordStateA k w = x}

/-- A displayed current word belongs to every current-word piece allowed by its level. -/
theorem wordStateA_mem_currentWordPiece (k : ℂ) (p : ℕ)
    (w : List (Fin 3 × ℕ)) (hp : p ≤ currentWordLevel w) :
    wordStateA k w ∈ currentWordPiece k p :=
  Submodule.subset_span ⟨w, hp, rfl⟩

/-- The current-word pieces form a decreasing filtration. -/
theorem currentWordPiece_antitone (k : ℂ) {p q : ℕ} (hpq : p ≤ q) :
    currentWordPiece k q ≤ currentWordPiece k p := by
  rw [currentWordPiece, currentWordPiece, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  exact wordStateA_mem_currentWordPiece k p w (hpq.trans hw)

/-- Affine current words are exactly the generic negative-mode generator words for the three
weight-one current states. -/
theorem wordStateA_eq_generatorWord (k : ℂ) (hk : k + 2 ≠ 0) :
    ∀ w : List (Fin 3 × ℕ),
      wordStateA k w =
        wordAct (adjointWeakModule (affineSl2VOA_closed k hk))
          (genWord (currentState k) (fun _ : Fin 3 => 1) w)
          (affineSl2VOA_closed k hk).vacuum := by
  intro w
  induction w with
  | nil => rfl
  | cons an rest ih =>
      rw [wordStateA_cons, genWord_cons, wordAct_cons, ← ih]
      exact (smul_currentState_eq_J k hk an.1 (-(an.2 : ℤ) - 1)
        (wordStateA k rest)).symm

/-- The current-word filtration is contained in the universal affine Li filtration.

This is the easy direction: each current is homogeneous of weight one, and the word itself has
the displayed total mode depth.  No current-word independence is used. -/
theorem currentWordPiece_le_liFiltration (k : ℂ) (hk : k + 2 ≠ 0) (p : ℕ) :
    currentWordPiece k p ≤ liFiltration (affineSl2VOA_closed k hk) p := by
  rw [currentWordPiece, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  rw [wordStateA_eq_generatorWord k hk w]
  exact genWord_mem_Gfil
    (adjointWeakModule (affineSl2VOA_closed k hk))
    ({(affineSl2VOA_closed k hk).vacuum} : Set (WakModule k))
    (fun a => currentState_mem_grading k hk a) w
    (Set.mem_singleton (affineSl2VOA_closed k hk).vacuum)
    (by exact_mod_cast hw)

/-- At level zero the current words already span the whole universal affine vacuum module.
This is only a spanning statement; it does not assert linear independence. -/
theorem currentWordPiece_zero_eq_top (k : ℂ) : currentWordPiece k 0 = ⊤ := by
  apply le_antisymm
  · exact le_top
  · rw [← wordStateA_span k, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact wordStateA_mem_currentWordPiece k 0 w (Nat.zero_le _)

/-- At filtration level zero the desired comparison is already an unconditional equality. -/
theorem liFiltration_zero_eq_currentWordPiece (k : ℂ) (hk : k + 2 ≠ 0) :
    liFiltration (affineSl2VOA_closed k hk) 0 = currentWordPiece k 0 := by
  rw [liFiltration_zero_eq_top, currentWordPiece_zero_eq_top]

/-- The missing strict strong-generation statement: every Li-filtration vector can be
straightened into current creation words without decreasing total derivative level.

This predicate contains no independence assertion.  It is strictly weaker than a PBW basis and
logically prior to classical freeness. -/
def CurrentWordsSpanLiFiltration (k : ℂ) (hk : k + 2 ≠ 0) : Prop :=
  ∀ p : ℕ, liFiltration (affineSl2VOA_closed k hk) p ≤ currentWordPiece k p

/-- The local strictness lemma which is sufficient for current-word spanning: every negative
mode of depth `n` maps the `q`-th current-word piece into the `(q+n)`-th piece.

The left state is arbitrary.  This is legitimate because `currentWordPiece k 0 = top`.
For a proof from strong generation, it is enough to establish this first for current-word left
states and then extend linearly using `wordStateA_span`. -/
def CurrentWordNegativeModeClosed (k : ℂ) (hk : k + 2 ≠ 0) : Prop :=
  ∀ (q n : ℕ) (u v : WakModule k), v ∈ currentWordPiece k q →
    (affineSl2VOA_closed k hk).smul u (-(n : ℤ) - 1) v ∈
      currentWordPiece k (q + n)

/-- A still more concrete form of the missing lemma, restricted to current-word left states.
The already proved spanning theorem `wordStateA_span` extends this statement to arbitrary left
states, so this is the smallest affine-specific mode calculation needed below. -/
def CurrentWordLeftNegativeModeClosed (k : ℂ) (hk : k + 2 ≠ 0) : Prop :=
  ∀ (left : List (Fin 3 × ℕ)) (q n : ℕ) (v : WakModule k),
    v ∈ currentWordPiece k q →
      (affineSl2VOA_closed k hk).smul (wordStateA k left) (-(n : ℤ) - 1) v ∈
        currentWordPiece k (q + n)

/-- The fully concrete two-word mode calculation.  For fixed current words on the left and
right, a negative mode of depth `n` must preserve the right word's total derivative level and
add `n`.  Linear extension and antitonicity recover the preceding closure predicate. -/
def CurrentWordPairNegativeModeClosed (k : ℂ) (hk : k + 2 ≠ 0) : Prop :=
  ∀ (left right : List (Fin 3 × ℕ)) (n : ℕ),
    (affineSl2VOA_closed k hk).smul (wordStateA k left) (-(n : ℤ) - 1)
        (wordStateA k right) ∈
      currentWordPiece k (currentWordLevel right + n)

/-- Natural-number target of the all-integer Li mode estimate for a degree-zero left state:
mode `m` sends level `q` to level `max(q-m-1,0)`. -/
def currentModeTarget (q : ℕ) (m : ℤ) : ℕ := ((q : ℤ) - m - 1).toNat

/-- A negative current creation mode prepends its letter and therefore adds its depth to the
current-word filtration. -/
theorem J_negSucc_mem_currentWordPiece_add (k : ℂ) (a : Fin 3) (r q : ℕ)
    {v : WakModule k} (hv : v ∈ currentWordPiece k q) :
    J k a (-(r : ℤ) - 1) v ∈ currentWordPiece k (q + r) := by
  rw [currentWordPiece] at hv
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨right, hright, rfl⟩ := hz
      change wordStateA k ((a, r) :: right) ∈ currentWordPiece k (q + r)
      exact wordStateA_mem_currentWordPiece k (q + r) ((a, r) :: right) (by
        simp only [currentWordLevel, pairsLevel_cons] at hright ⊢
        omega)
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ihx

/-- **Tracked affine-current commutation.**  A current mode `J^a_m` acting on a current
creation word lies in the current-word piece predicted by the all-integer Li estimate.

For negative `m` this simply prepends a creation operator.  For nonnegative `m`, commute it
through the first creation operator.  The swapped term uses the induction hypothesis, the
bracket term gains one extra unit of depth, and the central term is no worse than the requested
bound.  No independence of current words is used. -/
theorem J_wordStateA_mem_currentWordPiece (k : ℂ) :
    ∀ (right : List (Fin 3 × ℕ)) (a : Fin 3) (m : ℤ),
      J k a m (wordStateA k right) ∈
        currentWordPiece k (currentModeTarget (currentWordLevel right) m) := by
  intro right
  induction right with
  | nil =>
      intro a m
      by_cases hm : 0 ≤ m
      · rw [wordStateA_nil, J_vacuum_nonneg k a hm]
        exact Submodule.zero_mem _
      · obtain ⟨r, hr⟩ : ∃ r : ℕ, m = -(r : ℤ) - 1 :=
          ⟨(-m - 1).toNat, by omega⟩
        subst m
        have ht : currentModeTarget (currentWordLevel ([] : List (Fin 3 × ℕ)))
            (-(r : ℤ) - 1) = r := by
          simp [currentModeTarget, currentWordLevel, pairsLevel]
        rw [ht, wordStateA_nil]
        change wordStateA k [(a, r)] ∈ currentWordPiece k r
        exact wordStateA_mem_currentWordPiece k r [(a, r)] (by
          simp [currentWordLevel])
  | cons br rest ih =>
      obtain ⟨b, r⟩ := br
      intro a m
      by_cases hm : m < 0
      · obtain ⟨s, hs⟩ : ∃ s : ℕ, m = -(s : ℤ) - 1 :=
          ⟨(-m - 1).toNat, by omega⟩
        subst m
        have ht : currentModeTarget (currentWordLevel ((b, r) :: rest))
              (-(s : ℤ) - 1) = currentWordLevel ((a, s) :: (b, r) :: rest) := by
          simp only [currentModeTarget, currentWordLevel, pairsLevel_cons]
          omega
        rw [ht]
        change wordStateA k ((a, s) :: (b, r) :: rest) ∈
          currentWordPiece k (currentWordLevel ((a, s) :: (b, r) :: rest))
        exact wordStateA_mem_currentWordPiece k
          (currentWordLevel ((a, s) :: (b, r) :: rest))
          ((a, s) :: (b, r) :: rest) le_rfl
      · have hm0 : 0 ≤ m := le_of_not_gt hm
        rw [wordStateA_cons]
        have hcomm := current_comm k a b m (-(r : ℤ) - 1)
        have happ := congrArg (fun T : Module.End ℂ (WakModule k) =>
          T (wordStateA k rest)) hcomm
        simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
          LinearMap.sum_apply, LinearMap.smul_apply] at happ
        rw [sub_eq_iff_eq_add] at happ
        rw [happ]
        apply Submodule.add_mem
        · apply Submodule.add_mem
          · exact Submodule.sum_mem _ (fun c _ =>
              Submodule.smul_mem _ _ (currentWordPiece_antitone k (by
                simp only [currentModeTarget, currentWordLevel, pairsLevel_cons]
                omega) (ih c (m + (-(r : ℤ) - 1)))))
          · split_ifs with hzero
            · apply Submodule.smul_mem
              exact currentWordPiece_antitone k
                (p := currentModeTarget (currentWordLevel ((b, r) :: rest)) m)
                (q := currentWordLevel rest) (by
                  simp only [currentModeTarget, currentWordLevel, pairsLevel_cons] at hzero ⊢
                  omega)
                (wordStateA_mem_currentWordPiece k (currentWordLevel rest) rest le_rfl)
            · exact Submodule.zero_mem _
        · exact currentWordPiece_antitone k
            (p := currentModeTarget (currentWordLevel ((b, r) :: rest)) m)
            (q := currentModeTarget (currentWordLevel rest) m + r) (by
              simp only [currentModeTarget, currentWordLevel, pairsLevel_cons]
              omega)
            (J_negSucc_mem_currentWordPiece_add k b r
              (currentModeTarget (currentWordLevel rest) m) (ih a m))

/-- The tracked current-mode estimate extends linearly from current words to an arbitrary
current-word filtration piece. -/
theorem J_mem_currentWordPiece (k : ℂ) (a : Fin 3) (m : ℤ) (q : ℕ)
    {v : WakModule k} (hv : v ∈ currentWordPiece k q) :
    J k a m v ∈ currentWordPiece k (currentModeTarget q m) := by
  rw [currentWordPiece] at hv
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨right, hright, rfl⟩ := hz
      exact currentWordPiece_antitone k (p := currentModeTarget q m)
        (q := currentModeTarget (currentWordLevel right) m) (by
          simp only [currentModeTarget, currentWordLevel] at hright ⊢
          omega) (J_wordStateA_mem_currentWordPiece k right a m)
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ihx

/-- **All-mode normal-ordering estimate for current words.**  A mode `N` of any affine current
word maps the `q`-th current-word piece into level `max(q-N-1,0)`.

The induction is on the left word and uses the all-integer Borcherds iterate formula.  Its two
families are controlled by the tracked one-current estimate above and the induction hypothesis;
the nested truncations satisfy the required inequalities by integer arithmetic. -/
theorem wordStateA_mode_mem_currentWordPiece (k : ℂ) (hk : k + 2 ≠ 0) :
    ∀ (left : List (Fin 3 × ℕ)) (q : ℕ) (v : WakModule k),
      v ∈ currentWordPiece k q → ∀ N : ℤ,
        (affineSl2VOA_closed k hk).smul (wordStateA k left) N v ∈
          currentWordPiece k (currentModeTarget q N) := by
  intro left
  induction left with
  | nil =>
      intro q v hv N
      rw [wordStateA_nil]
      change (affineSl2VOA_closed k hk).smul
        (affineSl2VOA_closed k hk).vacuum N v ∈ _
      rw [PreVertexAlgebra.smul_vacuum_left]
      split_ifs with hN
      · subst N
        simpa [currentModeTarget] using hv
      · exact Submodule.zero_mem _
  | cons ar rest ih =>
      obtain ⟨a, r⟩ := ar
      intro q v hv N
      rw [wordStateA_cons,
        ← smul_currentState_eq_J k hk a (-(r : ℤ) - 1) (wordStateA k rest),
        VertexOperatorAlgebra.mode_iterate]
      apply QuotVOA.finsum_mem_submodule
      intro i
      apply Submodule.smul_mem
      apply Submodule.sub_mem
      · apply currentWordPiece_antitone k
          (p := currentModeTarget q N)
          (q := currentModeTarget (currentModeTarget q (N + (i : ℤ)))
            (-(r : ℤ) - 1 - (i : ℤ)))
        · simp only [currentModeTarget]
          omega
        · rw [smul_currentState_eq_J]
          exact J_mem_currentWordPiece k a (-(r : ℤ) - 1 - (i : ℤ))
            (currentModeTarget q (N + (i : ℤ))) (ih q v hv (N + (i : ℤ)))
      · apply Submodule.smul_mem
        apply currentWordPiece_antitone k
          (p := currentModeTarget q N)
          (q := currentModeTarget (currentModeTarget q (i : ℤ))
            ((-(r : ℤ) - 1) + N - (i : ℤ)))
        · simp only [currentModeTarget]
          omega
        · exact ih (currentModeTarget q (i : ℤ)) _
            (by
              rw [smul_currentState_eq_J]
              exact J_mem_currentWordPiece k a (i : ℤ) q hv)
            ((-(r : ℤ) - 1) + N - (i : ℤ))

/-- The concrete two-current-word negative-mode closure theorem. -/
theorem currentWordPairNegativeModeClosed (k : ℂ) (hk : k + 2 ≠ 0) :
    CurrentWordPairNegativeModeClosed k hk := by
  intro left right n
  have h := wordStateA_mode_mem_currentWordPiece k hk left
    (currentWordLevel right) (wordStateA k right)
    (wordStateA_mem_currentWordPiece k (currentWordLevel right) right le_rfl)
    (-(n : ℤ) - 1)
  have ht : currentModeTarget (currentWordLevel right) (-(n : ℤ) - 1) =
      currentWordLevel right + n := by
    simp only [currentModeTarget]
    omega
  rwa [ht] at h

/-- The two-word calculation extends to the whole right current-word span. -/
theorem currentWordLeftNegativeModeClosed_of_pair
    (k : ℂ) (hk : k + 2 ≠ 0) (hpair : CurrentWordPairNegativeModeClosed k hk) :
    CurrentWordLeftNegativeModeClosed k hk := by
  intro left q n v hv
  rw [currentWordPiece] at hv
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨right, hright, rfl⟩ := hz
      apply currentWordPiece_antitone k (Nat.add_le_add_right hright n)
      exact hpair left right n
  | zero =>
      rw [PreVertexAlgebra.smul_zero_right]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [PreVertexAlgebra.smul_add_right]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx =>
      rw [PreVertexAlgebra.smul_smul_right]
      exact Submodule.smul_mem _ c ihx

/-- The current-word-left closure statement contains the two-word calculation as its generator
case. -/
theorem currentWordPairNegativeModeClosed_of_left
    (k : ℂ) (hk : k + 2 ≠ 0) (hleft : CurrentWordLeftNegativeModeClosed k hk) :
    CurrentWordPairNegativeModeClosed k hk := by
  intro left right n
  exact hleft left (currentWordLevel right) n (wordStateA k right)
    (wordStateA_mem_currentWordPiece k (currentWordLevel right) right le_rfl)

/-- The global strict Li-spanning problem is therefore reduced to the concrete mode of one
current word on another. -/
theorem currentWordLeftNegativeModeClosed_iff_pair
    (k : ℂ) (hk : k + 2 ≠ 0) :
    CurrentWordLeftNegativeModeClosed k hk ↔ CurrentWordPairNegativeModeClosed k hk :=
  ⟨currentWordPairNegativeModeClosed_of_left k hk,
    currentWordLeftNegativeModeClosed_of_pair k hk⟩

/-- Closure for current-word left states extends linearly to arbitrary left states because the
current words span the universal affine vacuum module. -/
theorem currentWordNegativeModeClosed_of_wordLeft
    (k : ℂ) (hk : k + 2 ≠ 0) (hleft : CurrentWordLeftNegativeModeClosed k hk) :
    CurrentWordNegativeModeClosed k hk := by
  intro q n u v hv
  have hu : u ∈ Submodule.span ℂ (Set.range (wordStateA k)) := by
    rw [wordStateA_span k]
    exact Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨left, rfl⟩ := hz
      exact hleft left q n v hv
  | zero =>
      rw [PreVertexAlgebra.smul_zero_left]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [PreVertexAlgebra.smul_add_left]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx =>
      rw [PreVertexAlgebra.smul_smul_left]
      exact Submodule.smul_mem _ c ihx

/-- Arbitrary-left closure trivially implies the current-word-left specialization. -/
theorem currentWordLeftNegativeModeClosed_of_all
    (k : ℂ) (hk : k + 2 ≠ 0) (hall : CurrentWordNegativeModeClosed k hk) :
    CurrentWordLeftNegativeModeClosed k hk := by
  intro left q n v hv
  exact hall q n (wordStateA k left) v hv

/-- The abstract and current-word-left closure formulations are equivalent. -/
theorem currentWordNegativeModeClosed_iff_wordLeft
    (k : ℂ) (hk : k + 2 ≠ 0) :
    CurrentWordNegativeModeClosed k hk ↔ CurrentWordLeftNegativeModeClosed k hk :=
  ⟨currentWordLeftNegativeModeClosed_of_all k hk,
    currentWordNegativeModeClosed_of_wordLeft k hk⟩

/-- Under negative-mode closure, every homogeneous Li word of its exact total depth belongs to
the matching current-word piece. -/
private theorem wordAct_mem_currentWordPiece_of_negativeModeClosed
    (k : ℂ) (hk : k + 2 ≠ 0) (hclosed : CurrentWordNegativeModeClosed k hk) :
    ∀ l : List (Letter (WakModule k)),
      wordAct (adjointWeakModule (affineSl2VOA_closed k hk)) l
          (affineSl2VOA_closed k hk).vacuum ∈ currentWordPiece k (wordLevel l) := by
  intro l
  induction l with
  | nil =>
      change (affineSl2VOA_closed k hk).vacuum ∈ currentWordPiece k 0
      simpa only [closed_vacuum, wordStateA_nil] using
        wordStateA_mem_currentWordPiece k 0 [] (Nat.zero_le _)
  | cons a rest ih =>
      rw [wordAct_cons, wordLevel_cons]
      simpa only [PreVertexAlgebra.smul_def, Nat.add_comm] using
        hclosed (wordLevel rest) a.2.2 a.1
          (wordAct (adjointWeakModule (affineSl2VOA_closed k hk)) rest
            (affineSl2VOA_closed k hk).vacuum) ih

/-- The local negative-mode closure lemma implies strict current-word spanning of every Li
piece. -/
theorem currentWordsSpanLiFiltration_of_negativeModeClosed
    (k : ℂ) (hk : k + 2 ≠ 0) (hclosed : CurrentWordNegativeModeClosed k hk) :
    CurrentWordsSpanLiFiltration k hk := by
  intro p
  change Gfil (adjointWeakModule (affineSl2VOA_closed k hk))
      ({(affineSl2VOA_closed k hk).vacuum} : Set (WakModule k)) (p : ℤ) ≤
    currentWordPiece k p
  rw [Gfil, Submodule.span_le]
  rintro _ ⟨l, w, _hl, hw, hlevel, rfl⟩
  have hw' : w = (affineSl2VOA_closed k hk).vacuum := Set.mem_singleton_iff.mp hw
  subst w
  apply currentWordPiece_antitone k hlevel
  exact wordAct_mem_currentWordPiece_of_negativeModeClosed k hk hclosed l

/-- Conversely, strict current-word spanning forces negative-mode closure, by the already proved
Li-filtration mode estimate. -/
theorem currentWordNegativeModeClosed_of_span
    (k : ℂ) (hk : k + 2 ≠ 0) (hspan : CurrentWordsSpanLiFiltration k hk) :
    CurrentWordNegativeModeClosed k hk := by
  intro q n u v hv
  have hu : u ∈ liFiltration (affineSl2VOA_closed k hk) 0 := by
    rw [liFiltration_zero_eq_top]
    exact Submodule.mem_top
  have hv' : v ∈ liFiltration (affineSl2VOA_closed k hk) q :=
    currentWordPiece_le_liFiltration k hk q hv
  have hmode := liFiltration_smul_negSucc_mem
    (affineSl2VOA_closed k hk) n hu hv'
  have hmode' :
      (affineSl2VOA_closed k hk).smul u (-(n : ℤ) - 1) v ∈
        liFiltration (affineSl2VOA_closed k hk) (q + n) := by
    simpa only [Nat.zero_add] using hmode
  exact hspan (q + n) hmode'

/-- The global reverse inclusion is equivalent to one local negative-mode closure theorem. -/
theorem currentWordsSpanLiFiltration_iff_negativeModeClosed
    (k : ℂ) (hk : k + 2 ≠ 0) :
    CurrentWordsSpanLiFiltration k hk ↔ CurrentWordNegativeModeClosed k hk :=
  ⟨currentWordNegativeModeClosed_of_span k hk,
    currentWordsSpanLiFiltration_of_negativeModeClosed k hk⟩

/-- **Exact reduction of affine Li strictness.**  The reverse inclusion `F^p <= C_p` for all
`p` is equivalent to the concrete assertion that a negative mode of one current word acting on
another lands in the current-word piece with the predicted total derivative level. -/
theorem currentWordsSpanLiFiltration_iff_pairNegativeModeClosed
    (k : ℂ) (hk : k + 2 ≠ 0) :
    CurrentWordsSpanLiFiltration k hk ↔ CurrentWordPairNegativeModeClosed k hk :=
  (currentWordsSpanLiFiltration_iff_negativeModeClosed k hk).trans
    ((currentWordNegativeModeClosed_iff_wordLeft k hk).trans
      (currentWordLeftNegativeModeClosed_iff_pair k hk))

/-- **Strict current-PBW spanning of the universal affine Li filtration.**  Every element of
Li level `p` is a linear combination of current creation words whose total derivative level is
at least `p`.  This is a spanning theorem only; it neither asserts current-word independence nor
uses classical freeness. -/
theorem currentWordsSpanLiFiltration (k : ℂ) (hk : k + 2 ≠ 0) :
    CurrentWordsSpanLiFiltration k hk :=
  (currentWordsSpanLiFiltration_iff_pairNegativeModeClosed k hk).mpr
    (currentWordPairNegativeModeClosed k hk)

/-- **Current-word description of the universal affine Li filtration.** -/
theorem liFiltration_eq_currentWordPiece (k : ℂ) (hk : k + 2 ≠ 0) (p : ℕ) :
    liFiltration (affineSl2VOA_closed k hk) p = currentWordPiece k p :=
  le_antisymm ((currentWordsSpanLiFiltration k hk) p)
    (currentWordPiece_le_liFiltration k hk p)

/-- Strict current-word spanning, together with the unconditional easy inclusion, identifies
the current-word filtration with Li's filtration. -/
theorem liFiltration_eq_currentWordPiece_of_span
    (k : ℂ) (hk : k + 2 ≠ 0) (hspan : CurrentWordsSpanLiFiltration k hk) (p : ℕ) :
    liFiltration (affineSl2VOA_closed k hk) p = currentWordPiece k p :=
  le_antisymm (hspan p) (currentWordPiece_le_liFiltration k hk p)

/-- Equality with the current-word filtration is equivalent to the named reverse-inclusion
hypothesis.  This prevents later developments from silently treating inclusion as equality. -/
theorem currentWordsSpanLiFiltration_iff_eq (k : ℂ) (hk : k + 2 ≠ 0) :
    CurrentWordsSpanLiFiltration k hk ↔
      ∀ p : ℕ, liFiltration (affineSl2VOA_closed k hk) p = currentWordPiece k p := by
  constructor
  · intro h p
    exact liFiltration_eq_currentWordPiece_of_span k hk h p
  · intro h p
    rw [h p]

/-! ## A generic graded-quotient lemma for Li filtrations -/

section GenericQuotient

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (W : VertexOperatorAlgebra V) (I : Submodule ℂ V)
variable (hI : W.IsIdeal I) (hgr : QuotVOA.IsGradedIdeal W I)

/-- Map a homogeneous source word letterwise to a quotient word, retaining weights and mode
depths. -/
private def mapQuotientWord (l : List (Letter V)) : List (Letter (V ⧸ I)) :=
  l.map fun a => (I.mkQ a.1, a.2.1, a.2.2)

@[simp] private theorem wordLevel_mapQuotientWord (l : List (Letter V)) :
    wordLevel (mapQuotientWord I l) = wordLevel l := by
  simp only [mapQuotientWord, wordLevel, List.map_map]
  rfl

/-- Letterwise quotient projection preserves word homogeneity. -/
private theorem wordOK_mapQuotientWord : ∀ l : List (Letter V),
    WordOK W l → WordOK (QuotVOA.quotientVOA W I hI hgr) (mapQuotientWord I l) := by
  intro l hl
  induction l with
  | nil => exact WordOK_nil _
  | cons a rest ih =>
      obtain ⟨ha, hrest⟩ := WordOK_of_cons hl
      exact WordOK_cons (QuotVOA.quotientVOA_mkQ_grading hI hgr ha) (ih hrest)

/-- Quotient projection intertwines a whole negative-mode word with its letterwise image. -/
private theorem mkQ_wordAct_eq_mapQuotientWord : ∀ l : List (Letter V),
    I.mkQ (wordAct (adjointWeakModule W) l W.vacuum) =
      wordAct (adjointWeakModule (QuotVOA.quotientVOA W I hI hgr))
        (mapQuotientWord I l) (QuotVOA.quotientVOA W I hI hgr).vacuum := by
  intro l
  induction l with
  | nil => rfl
  | cons a rest ih =>
      rw [wordAct_cons, mapQuotientWord, List.map_cons, wordAct_cons]
      change I.mkQ (W.smul a.1 (-(a.2.2 : ℤ) - 1)
          (wordAct (adjointWeakModule W) rest W.vacuum)) = _
      rw [← QuotVOA.quotientVOA_mkQ_smul hI hgr, ih]
      rfl

/-- Every homogeneous negative-mode word in a graded VOA quotient lifts to a homogeneous word
upstairs, with identical mode depths and with the same value after quotient projection. -/
private theorem exists_lift_quotient_word :
    ∀ l : List (Letter (V ⧸ I)),
      WordOK (QuotVOA.quotientVOA W I hI hgr) l →
      ∃ l₀ : List (Letter V),
        WordOK W l₀ ∧ wordLevel l₀ = wordLevel l ∧
          I.mkQ (wordAct (adjointWeakModule W) l₀ W.vacuum) =
            wordAct (adjointWeakModule (QuotVOA.quotientVOA W I hI hgr)) l
              (QuotVOA.quotientVOA W I hI hgr).vacuum := by
  intro l hl
  induction l with
  | nil =>
      exact ⟨[], WordOK_nil W, rfl, rfl⟩
  | cons a rest ih =>
      obtain ⟨ha, hrest⟩ := WordOK_of_cons hl
      change a.1 ∈ (W.grading (a.2.1 : ℤ)).map I.mkQ at ha
      obtain ⟨c, hc, hca⟩ := Submodule.mem_map.mp ha
      obtain ⟨rest₀, hrest₀, hlevel, hvalue⟩ := ih hrest
      refine ⟨(c, a.2.1, a.2.2) :: rest₀, WordOK_cons hc hrest₀, ?_, ?_⟩
      · simp only [wordLevel_cons, hlevel]
      · rw [wordAct_cons, wordAct_cons]
        change I.mkQ (W.smul c (-(a.2.2 : ℤ) - 1)
            (wordAct (adjointWeakModule W) rest₀ W.vacuum)) = _
        rw [← QuotVOA.quotientVOA_mkQ_smul hI hgr, hca, hvalue]
        rfl

/-- The intrinsic Li filtration of a graded VOA quotient is contained in the image of the Li
filtration upstairs.  This is the direction needed to transport current-word spanning.

The proof lifts each homogeneous letter separately.  It uses neither finite-dimensionality nor
PBW independence. -/
theorem quotientLiFiltration_le_map (p : ℕ) :
    liFiltration (QuotVOA.quotientVOA W I hI hgr) p ≤
      (liFiltration W p).map I.mkQ := by
  change Gfil
      (adjointWeakModule (QuotVOA.quotientVOA W I hI hgr))
      ({(QuotVOA.quotientVOA W I hI hgr).vacuum} : Set (V ⧸ I)) (p : ℤ) ≤
    (Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (p : ℤ)).map I.mkQ
  rw [Gfil, Submodule.span_le]
  rintro z ⟨l, w, hl, hw, hlevel, rfl⟩
  have hw' : w = (QuotVOA.quotientVOA W I hI hgr).vacuum := Set.mem_singleton_iff.mp hw
  subst w
  obtain ⟨l₀, hl₀, hlevels, hvalue⟩ := exists_lift_quotient_word W I hI hgr l hl
  refine Submodule.mem_map.mpr ⟨wordAct (adjointWeakModule W) l₀ W.vacuum, ?_, hvalue⟩
  exact wordAct_mem_Gfil (adjointWeakModule W) ({W.vacuum} : Set V) hl₀
    (Set.mem_singleton W.vacuum) (by rw [hlevels]; exact_mod_cast hlevel)

/-- The image of the Li filtration upstairs is contained in the intrinsic Li filtration of the
quotient. -/
theorem map_liFiltration_le_quotient (p : ℕ) :
    (liFiltration W p).map I.mkQ ≤
      liFiltration (QuotVOA.quotientVOA W I hI hgr) p := by
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  clear hy
  change x ∈ Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (p : ℤ) at hx
  rw [Gfil] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, w, hl, hw, hlevel, rfl⟩ := hz
      have hw' : w = W.vacuum := Set.mem_singleton_iff.mp hw
      subst w
      rw [mkQ_wordAct_eq_mapQuotientWord W I hI hgr l]
      exact wordAct_mem_Gfil
        (adjointWeakModule (QuotVOA.quotientVOA W I hI hgr))
        ({(QuotVOA.quotientVOA W I hI hgr).vacuum} : Set (V ⧸ I))
        (wordOK_mapQuotientWord W I hI hgr l hl)
        (Set.mem_singleton (QuotVOA.quotientVOA W I hI hgr).vacuum)
        (by rw [wordLevel_mapQuotientWord]; exact_mod_cast hlevel)
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ihx

/-- **Li filtration commutes with graded VOA quotients.**  The intrinsic quotient filtration is
exactly the image filtration.  This is a pure quotient/word-lifting theorem and uses no affine
input. -/
theorem quotientLiFiltration_eq_map (p : ℕ) :
    liFiltration (QuotVOA.quotientVOA W I hI hgr) p =
      (liFiltration W p).map I.mkQ :=
  le_antisymm (quotientLiFiltration_le_map W I hI hgr p)
    (map_liFiltration_le_quotient W I hI hgr p)

end GenericQuotient

/-! ## Graded quotients -/

section Quotient

variable (k : ℂ) (hk : k + 2 ≠ 0)
variable (I : Submodule ℂ (WakModule k))
variable (hI : (affineSl2VOA_closed k hk).IsIdeal I)
variable (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) I)

/-- The current-word piece induced on a graded affine VOA quotient.  This is an image
filtration; no assertion about the kernel of the quotient map is built into the definition. -/
def quotientCurrentWordPiece (p : ℕ) : Submodule ℂ (WakModule k ⧸ I) :=
  (currentWordPiece k p).map I.mkQ

/-- The level-zero quotient current-word piece is the whole quotient. -/
theorem quotientCurrentWordPiece_zero_eq_top : quotientCurrentWordPiece k I 0 = ⊤ := by
  rw [quotientCurrentWordPiece, currentWordPiece_zero_eq_top, Submodule.map_top,
    LinearMap.range_eq_top.mpr I.mkQ_surjective]

/-- Thus the intrinsic and current-word quotient filtrations agree unconditionally at level
zero. -/
theorem quotientLiFiltration_zero_eq_currentWordPiece :
    liFiltration (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr) 0 =
      quotientCurrentWordPiece k I 0 := by
  rw [liFiltration_zero_eq_top, quotientCurrentWordPiece_zero_eq_top]

/-- The image of a universal current word is exactly the corresponding current word in the
quotient VOA. -/
theorem mkQ_wordStateA_eq_generatorWord : ∀ w : List (Fin 3 × ℕ),
    I.mkQ (wordStateA k w) =
      wordAct
        (adjointWeakModule
          (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr))
        (genWord (fun a => I.mkQ (currentState k a)) (fun _ : Fin 3 => 1) w)
        (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr).vacuum := by
  intro w
  induction w with
  | nil => rfl
  | cons an rest ih =>
      rw [wordStateA_cons,
        ← smul_currentState_eq_J k hk an.1 (-(an.2 : ℤ) - 1) (wordStateA k rest),
        ← QuotVOA.quotientVOA_mkQ_smul hI hgr, genWord_cons, wordAct_cons, ← ih]
      rfl

/-- Every induced quotient current-word piece is contained in the quotient's intrinsic Li
filtration.  This direction is unconditional for every graded ideal. -/
theorem quotientCurrentWordPiece_le_liFiltration (p : ℕ) :
    quotientCurrentWordPiece k I p ≤
      liFiltration (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr) p := by
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  clear hy
  rw [currentWordPiece] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      rw [mkQ_wordStateA_eq_generatorWord k hk I hI hgr w]
      exact genWord_mem_Gfil
        (adjointWeakModule
          (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr))
        ({(QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr).vacuum} :
          Set (WakModule k ⧸ I))
        (fun a => QuotVOA.quotientVOA_mkQ_grading hI hgr
          (currentState_mem_grading k hk a)) w
        (Set.mem_singleton
          (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr).vacuum)
        (by exact_mod_cast hw)
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ihx

/-- The quotient analogue of strict current-word spanning.  It is kept separate from the
universal statement because equality of an intrinsic filtration with an image filtration is a
strictness assertion about the quotient map. -/
def QuotientCurrentWordsSpanLiFiltration : Prop :=
  ∀ p : ℕ,
    liFiltration (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr) p ≤
      quotientCurrentWordPiece k I p

/-- Under the explicitly named quotient strictness hypothesis, the intrinsic quotient Li
filtration equals the image current-word filtration. -/
theorem quotientLiFiltration_eq_currentWordPiece_of_span
    (hspan : QuotientCurrentWordsSpanLiFiltration k hk I hI hgr) (p : ℕ) :
    liFiltration (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr) p =
      quotientCurrentWordPiece k I p :=
  le_antisymm (hspan p) (quotientCurrentWordPiece_le_liFiltration k hk I hI hgr p)

/-- Universal strict current-word spanning transports to every graded affine quotient.  The
additional quotient hypothesis above is therefore not independent once the universal
strong-generation theorem has been proved. -/
theorem quotientCurrentWordsSpanLiFiltration_of_universal
    (hspan : CurrentWordsSpanLiFiltration k hk) :
    QuotientCurrentWordsSpanLiFiltration k hk I hI hgr := by
  intro p y hy
  have hymap := quotientLiFiltration_le_map
    (affineSl2VOA_closed k hk) I hI hgr p hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hymap
  exact Submodule.mem_map_of_mem (hspan p hx)

/-- Consequently, the universal strict spanning theorem identifies the intrinsic Li filtration
of every graded affine quotient with the image of the current-word filtration. -/
theorem quotientLiFiltration_eq_currentWordPiece_of_universal
    (hspan : CurrentWordsSpanLiFiltration k hk) (p : ℕ) :
    liFiltration (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr) p =
      quotientCurrentWordPiece k I p :=
  quotientLiFiltration_eq_currentWordPiece_of_span k hk I hI hgr
    (quotientCurrentWordsSpanLiFiltration_of_universal k hk I hI hgr hspan) p

/-- **Current-word description of every graded affine quotient Li filtration.**  This is the
unconditional quotient form of `liFiltration_eq_currentWordPiece`: universal strict spanning
has already been proved above, so no quotient-specific PBW or strictness hypothesis remains. -/
theorem quotientLiFiltration_eq_currentWordPiece (p : ℕ) :
    liFiltration (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr) p =
      quotientCurrentWordPiece k I p :=
  quotientLiFiltration_eq_currentWordPiece_of_universal k hk I hI hgr
    (currentWordsSpanLiFiltration k hk) p

end Quotient

end

end CurrentLi
end AffineVOA
end VOA
