/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNLemma7

/-!
# Gaberdiel–Neitzke Prop. 8, layer 1: mode words, the grade filtration, and the order
predicates

Toward GN Prop. 8 (`hep-th/0009235`) — the last input to residual **(b)**.  The three VOA
identities its proof needs are banked (Lemma 5 = `Core.Reconstruction.mode_commutator`, Lemma 6 =
`Core.BorcherdsIdentity.VertexOperatorAlgebra.mode_iterate`, Lemma 7 =
`Modularity.GNLemma7.gn_lemma7`); what remains is GN's bookkeeping, and this file is its first
layer.

**The induction invariant, from the source.**  GN's proof is a lexicographic induction on
`(g, N)` where `g = ∑ h_{ψᵢ}` is the total conformal weight and — in the paper's own words —
**"`N` bounds the allowed repetition of mode indices"**.  So the two order predicates below are the
ones the induction moves between: `GNWeakDec` (modes weakly decreasing, which the Li-filtration
ordering already gives) and `GNNoRepeatLE N` (no two letters share a mode index `≤ N`).  At
`N ≥ every index` the two together are exactly strict decrease — `gnStrictDec_of_noRepeat` — which is
Prop. 8's conclusion.

## Main results

* `word`, `GNWordOK`, `gnWordGrade` — mode words over homogeneous letters;
* `gnWord_isHomog` — a word on the vacuum is homogeneous;
* `gnGradeFil` — GN's filtration `ℋ^{(g)}`, with `gnGradeFil_mono` and `gnGradeFil_iSup_eq_top`;
* `GNWeakDec`, `GNNoRepeatLE`, `gnStrictDec_of_noRepeat` — the order layer.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  This is layer 1 of Prop. 8; the induction itself is
not here.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Mode words -/

/-- A **letter** `(ψ, h, n)` — a vector `ψ`, its conformal weight `h`, and a positive mode index
`n`.  It acts as `V₍₋n₎(ψ) = ψ₍₋n₎`. -/
abbrev GNLetter (𝒱 : Type u) : Type u := 𝒱 × ℕ × ℕ

/-- The mode word `ψ₁₍₋n₁₎ ⋯ ψ_k₍₋n_k₎ x`, outermost letter first. -/
noncomputable def gnWord (W : VertexOperatorAlgebra 𝒱) : List (GNLetter 𝒱) → 𝒱 → 𝒱
  | [], x => x
  | p :: l, x => W.smul p.1 (-(p.2.2 : ℤ)) (gnWord W l x)

@[simp] theorem gnWord_nil (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) : gnWord W [] x = x := rfl

@[simp] theorem gnWord_cons (W : VertexOperatorAlgebra 𝒱) (p : GNLetter 𝒱)
    (l : List (GNLetter 𝒱)) (x : 𝒱) :
    gnWord W (p :: l) x = W.smul p.1 (-(p.2.2 : ℤ)) (gnWord W l x) := rfl

/-- A word is **admissible**: every letter is homogeneous of its declared weight, and every mode
index is positive. -/
def GNWordOK (W : VertexOperatorAlgebra 𝒱) (l : List (GNLetter 𝒱)) : Prop :=
  (∀ p ∈ l, p.1 ∈ W.grading (p.2.1 : ℤ)) ∧ (∀ p ∈ l, 1 ≤ p.2.2)

theorem GNWordOK.nil (W : VertexOperatorAlgebra 𝒱) : GNWordOK W ([] : List (GNLetter 𝒱)) :=
  ⟨by simp, by simp⟩

theorem GNWordOK.tail {W : VertexOperatorAlgebra 𝒱} {p : GNLetter 𝒱} {l : List (GNLetter 𝒱)}
    (h : GNWordOK W (p :: l)) : GNWordOK W l :=
  ⟨fun q hq => h.1 q (List.mem_cons_of_mem _ hq), fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

theorem GNWordOK.head_mem {W : VertexOperatorAlgebra 𝒱} {p : GNLetter 𝒱} {l : List (GNLetter 𝒱)}
    (h : GNWordOK W (p :: l)) : p.1 ∈ W.grading (p.2.1 : ℤ) :=
  h.1 p (List.mem_cons_self ..)

/-- The **grade** of a word: the total conformal weight `∑ h_{ψᵢ}`. -/
def gnWordGrade (l : List (GNLetter 𝒱)) : ℕ := (l.map (fun p => p.2.1)).sum

@[simp] theorem gnWordGrade_nil : gnWordGrade ([] : List (GNLetter 𝒱)) = 0 := rfl

@[simp] theorem gnWordGrade_cons (p : GNLetter 𝒱) (l : List (GNLetter 𝒱)) :
    gnWordGrade (p :: l) = p.2.1 + gnWordGrade l := rfl

/-- A word on the vacuum is homogeneous. -/
theorem gnWord_isHomog (W : VertexOperatorAlgebra 𝒱) {l : List (GNLetter 𝒱)} (h : GNWordOK W l) :
    IsHomog W (gnWord W l W.vacuum) := by
  induction l with
  | nil => exact ⟨0, W.vacuum_mem_grading_zero⟩
  | cons p l ih =>
      obtain ⟨d, hd⟩ := ih h.tail
      exact ⟨(p.2.1 : ℤ) + d + (p.2.2 : ℤ) - 1, step_mem_grading W h.head_mem hd⟩

/-! ## The grade filtration `ℋ^{(g)}` -/

/-- The words of grade at most `g`, evaluated on the vacuum. -/
def gnGradeWords (W : VertexOperatorAlgebra 𝒱) (g : ℕ) : Set 𝒱 :=
  {x | ∃ l : List (GNLetter 𝒱), GNWordOK W l ∧ gnWordGrade l ≤ g ∧ x = gnWord W l W.vacuum}

/-- **GN's filtration** `ℋ^{(g)}`. -/
noncomputable def gnGradeFil (W : VertexOperatorAlgebra 𝒱) (g : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ (gnGradeWords W g)

theorem word_mem_gnGradeFil (W : VertexOperatorAlgebra 𝒱) {l : List (GNLetter 𝒱)} (h : GNWordOK W l)
    {g : ℕ} (hg : gnWordGrade l ≤ g) : gnWord W l W.vacuum ∈ gnGradeFil W g :=
  Submodule.subset_span ⟨l, h, hg, rfl⟩

theorem vacuum_mem_gnGradeFil (W : VertexOperatorAlgebra 𝒱) (g : ℕ) :
    W.vacuum ∈ gnGradeFil W g :=
  word_mem_gnGradeFil W (GNWordOK.nil W) (by simp)

/-- The filtration is monotone. -/
theorem gnGradeFil_mono (W : VertexOperatorAlgebra 𝒱) {g g' : ℕ} (h : g ≤ g') :
    gnGradeFil W g ≤ gnGradeFil W g' := by
  rw [gnGradeFil, Submodule.span_le]
  rintro x ⟨l, hOK, hg, rfl⟩
  exact word_mem_gnGradeFil W hOK (le_trans hg h)

/-- Every homogeneous vector of weight `n` is a one-letter word of grade `n`, by the creation
axiom `ψ₍₋₁₎𝟙 = ψ`. -/
theorem homog_mem_gnGradeFil (W : VertexOperatorAlgebra 𝒱) {n : ℕ} {x : 𝒱}
    (hx : x ∈ W.grading (n : ℤ)) : x ∈ gnGradeFil W n := by
  refine Submodule.subset_span ⟨[(x, n, 1)], ⟨?_, ?_⟩, ?_, ?_⟩
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact hx
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact le_refl 1
  · simp [gnWordGrade]
  · rw [gnWord_cons, gnWord_nil]
    exact (W.toPreVertexAlgebra.smul_vacuum_neg_one x).symm

/-- **The filtration exhausts `𝒱`.** -/
theorem gnGradeFil_iSup_eq_top (W : VertexOperatorAlgebra 𝒱) :
    (⨆ g : ℕ, gnGradeFil W g) = ⊤ := by
  rw [eq_top_iff, ← span_homog_eq_top W, Submodule.span_le]
  rintro x ⟨d, hx⟩
  rcases lt_or_ge d 0 with hd | hd
  · rw [W.positivity d hd, Submodule.mem_bot] at hx
    subst hx
    exact Submodule.zero_mem _
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = (n : ℤ) := ⟨d.toNat, by omega⟩
    exact Submodule.mem_iSup_of_mem n (homog_mem_gnGradeFil W hx)

/-! ## The order layer -/

/-- Mode indices **weakly** decreasing along the word. -/
def GNWeakDec (l : List (GNLetter 𝒱)) : Prop :=
  List.Pairwise (fun a b : GNLetter 𝒱 => b.2.2 ≤ a.2.2) l

/-- **No repeated mode index at or below `N`** — the parameter GN's induction moves on. -/
def GNNoRepeatLE (N : ℕ) (l : List (GNLetter 𝒱)) : Prop :=
  List.Pairwise (fun a b : GNLetter 𝒱 => a.2.2 ≤ N → b.2.2 ≤ N → a.2.2 ≠ b.2.2) l

theorem GNWeakDec.tail {p : GNLetter 𝒱} {l : List (GNLetter 𝒱)} (h : GNWeakDec (p :: l)) :
    GNWeakDec l := (List.pairwise_cons.mp h).2

theorem GNNoRepeatLE.tail {N : ℕ} {p : GNLetter 𝒱} {l : List (GNLetter 𝒱)}
    (h : GNNoRepeatLE N (p :: l)) : GNNoRepeatLE N l := (List.pairwise_cons.mp h).2

/-- **Weak decrease + no repeats below `N` + all indices `≤ N` ⟹ strict decrease.**  This is
the step that turns GN's induction hypothesis at a large `N` into Prop. 8's conclusion. -/
theorem gnStrictDec_of_noRepeat {N : ℕ} :
    ∀ l : List (GNLetter 𝒱), GNWeakDec l → GNNoRepeatLE N l → (∀ p ∈ l, p.2.2 ≤ N) →
      List.Pairwise (fun a b : GNLetter 𝒱 => b.2.2 < a.2.2) l := by
  intro l
  induction l with
  | nil => intro _ _ _; exact List.Pairwise.nil
  | cons p l ih =>
      intro hwd hnr hle
      obtain ⟨hwdh, hwdt⟩ := List.pairwise_cons.mp hwd
      obtain ⟨hnrh, hnrt⟩ := List.pairwise_cons.mp hnr
      refine List.pairwise_cons.mpr ⟨fun q hq => ?_, ?_⟩
      · have h1 : q.2.2 ≤ p.2.2 := hwdh q hq
        have h2 : p.2.2 ≠ q.2.2 :=
          hnrh q hq (hle p (List.mem_cons_self ..)) (hle q (List.mem_cons_of_mem _ hq))
        omega
      · exact ih hwdt hnrt (fun q hq => hle q (List.mem_cons_of_mem _ hq))

end VOA
