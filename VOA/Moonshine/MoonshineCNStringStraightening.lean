import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! # Negative Virasoro straightening for arbitrary operator families

Structural port of `negWord_mem_sortedSpan`, with no Verma module or
highest-weight vector. An index `i` means a mode of energy `i+1`.
Only the negative-negative commutator is assumed.
-/

namespace VOA.Moonshine.ConwayNorton

universe u
variable {H : Type u} [AddCommGroup H] [Module ℂ H]

def stringNegativeWord (D : ℕ → Module.End ℂ H) (x : H) : List ℕ → H
  | [] => x
  | i :: w => D i (stringNegativeWord D x w)

def stringWordEnergy (w : List ℕ) : ℕ := (w.map fun i => i + 1).sum

abbrev stringSortedWord (w : List ℕ) : Prop := w.Pairwise (· ≥ ·)

@[simp] theorem stringWordEnergy_nil : stringWordEnergy [] = 0 := rfl

@[simp] theorem stringWordEnergy_cons (i : ℕ) (w : List ℕ) :
    stringWordEnergy (i :: w) = i + 1 + stringWordEnergy w := by simp [stringWordEnergy]

def stringSortedSpan (D : ℕ → Module.End ℂ H) (x : H) (N : ℕ) : Submodule ℂ H :=
  Submodule.span ℂ {y | ∃ w : List ℕ,
    stringSortedWord w ∧ stringWordEnergy w = N ∧ stringNegativeWord D x w = y}

theorem stringNegativeWord_sorted (D : ℕ → Module.End ℂ H) (x : H) {w : List ℕ}
    (hw : stringSortedWord w) {N : ℕ} (hN : stringWordEnergy w = N) :
    stringNegativeWord D x w ∈ stringSortedSpan D x N :=
  Submodule.subset_span ⟨w, hw, hN, rfl⟩

theorem stringSortedSpan_stable (D : ℕ → Module.End ℂ H) (x : H) {N : ℕ}
    (hinsert : ∀ w, stringWordEnergy w = N → stringSortedWord w → ∀ i,
      D i (stringNegativeWord D x w) ∈ stringSortedSpan D x (N + i + 1))
    (i : ℕ) {y : H} (hy : y ∈ stringSortedSpan D x N) :
    D i y ∈ stringSortedSpan D x (N + i + 1) := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨w, hw, he, rfl⟩ := hy; exact hinsert w he hw i
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

theorem stringNegativeWord_swap (D : ℕ → Module.End ℂ H)
    (hcomm : ∀ i j, D i * D j - D j * D i = ((j : ℂ) - i) • D (i + j + 1))
    (x : H) (i j : ℕ) (w : List ℕ) :
    stringNegativeWord D x (i :: j :: w) = stringNegativeWord D x (j :: i :: w) +
      ((j : ℂ) - i) • stringNegativeWord D x ((i + j + 1) :: w) := by
  have he := LinearMap.congr_fun (hcomm i j) (stringNegativeWord D x w)
  change D i (D j _) - D j (D i _) = ((j : ℂ) - i) • D (i + j + 1) _ at he
  simpa only [stringNegativeWord, add_comm] using sub_eq_iff_eq_add.mp he

theorem stringNegativeMode_sorted_insert (D : ℕ → Module.End ℂ H)
    (hcomm : ∀ i j, D i * D j - D j * D i = ((j : ℂ) - i) • D (i + j + 1))
    (x : H) (N : ℕ) :
    ∀ w, stringWordEnergy w = N → stringSortedWord w → ∀ i,
      D i (stringNegativeWord D x w) ∈ stringSortedSpan D x (N + i + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w hw hsort i
    match w with
    | [] =>
        have hN : N = 0 := by rw [← hw]; rfl
        subst hN
        change stringNegativeWord D x [i] ∈ stringSortedSpan D x (0 + i + 1)
        exact stringNegativeWord_sorted D x (by simp) (by simp)
    | j :: rest =>
        have hw' : j + 1 + stringWordEnergy rest = N := by rw [← hw, stringWordEnergy_cons]
        have hs := List.pairwise_cons.mp hsort
        change stringNegativeWord D x (i :: j :: rest) ∈ stringSortedSpan D x (N + i + 1)
        rcases Nat.lt_or_ge i j with hij | hji
        · rw [stringNegativeWord_swap D hcomm]
          refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
          · have hrest : stringWordEnergy rest < N := by omega
            have h1 := ih _ hrest rest rfl hs.2 i
            have hmiddle : stringWordEnergy rest + i + 1 < N := by omega
            have h2 := stringSortedSpan_stable D x (ih _ hmiddle) j h1
            have he : stringWordEnergy rest + i + 1 + j + 1 = N + i + 1 := by omega
            rw [he] at h2
            exact h2
          · refine stringNegativeWord_sorted D x (List.pairwise_cons.mpr ⟨?_, hs.2⟩) ?_
            · intro b hb
              exact le_trans (hs.1 b hb) (by omega)
            · simp only [stringWordEnergy_cons]; omega
        · refine stringNegativeWord_sorted D x (List.pairwise_cons.mpr ⟨?_, hsort⟩) ?_
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact hji
            · exact le_trans (hs.1 b hb') hji
          · simp only [stringWordEnergy_cons]; omega

/-- Every negative word straightens at the same energy, for an arbitrary base vector. -/
theorem stringNegativeWord_mem_sortedSpan (D : ℕ → Module.End ℂ H)
    (hcomm : ∀ i j, D i * D j - D j * D i = ((j : ℂ) - i) • D (i + j + 1))
    (x : H) (w : List ℕ) :
    stringNegativeWord D x w ∈ stringSortedSpan D x (stringWordEnergy w) := by
  induction w with
  | nil => exact stringNegativeWord_sorted D x (by simp) rfl
  | cons i rest ih =>
      have h := stringSortedSpan_stable D x
        (stringNegativeMode_sorted_insert D hcomm x (stringWordEnergy rest)) i ih
      simpa only [stringWordEnergy_cons, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using h

/-- Nonempty words straighten using only nonempty words; no vacuum term is introduced. -/
theorem stringNegativeWord_mem_nonempty_sortedSpan (D : ℕ → Module.End ℂ H)
    (hcomm : ∀ i j, D i * D j - D j * D i = ((j : ℂ) - i) • D (i + j + 1))
    (x : H) (w : List ℕ) (hw : w ≠ []) :
    stringNegativeWord D x w ∈ Submodule.span ℂ {y | ∃ v : List ℕ,
      v ≠ [] ∧ stringSortedWord v ∧ stringWordEnergy v = stringWordEnergy w ∧
        stringNegativeWord D x v = y} := by
  have hpos : 0 < stringWordEnergy w := by
    cases w with
    | nil => exact (hw rfl).elim
    | cons i rest => simp only [stringWordEnergy_cons]; omega
  apply (show stringSortedSpan D x (stringWordEnergy w) ≤ _ from ?_)
    (stringNegativeWord_mem_sortedSpan D hcomm x w)
  apply Submodule.span_le.mpr
  rintro y ⟨v, hv, he, rfl⟩
  refine Submodule.subset_span ⟨v, ?_, hv, he, rfl⟩
  intro hn
  subst v
  simp only [stringWordEnergy_nil] at he
  omega

end VOA.Moonshine.ConwayNorton
