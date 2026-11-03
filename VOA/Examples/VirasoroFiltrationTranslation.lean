/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroGoodFiltration

/-!
# Translation preserves the Virasoro creation-word-length filtration

This is often called the PBW-length filtration, but no PBW theorem or linear-independence
statement is used here.  The filtration is defined as a span of sorted creation words, and the
proof uses only the Virasoro commutator, elementary straightening, and induction.

For the Virasoro length filtration, `L₋₁` differentiates a creation word: it increments one
creation-mode index but does not add a mode.  Consequently

`L₋₁ G_p V_n ⊆ G_p V_{n+1}`.

This file proves the statement first on the universal vacuum module and then transports it to the
simple quotient.  The only extra straightening needed is a length-refined form of the existing
creation-mode insertion argument.

## References

* T. Gannon, *Moonshine Beyond the Monster* (2006), §5.2.
* Arabi Ardehali--Beem--Lemos--Rastelli, eq. (3.11).
-/

set_option linter.style.longLine false

namespace VOA

namespace VirGoodFil

open VOA.VirModule VOA.VirSimple VOA.VirQuotForm
open VOA.VertexOperatorAlgebra

variable (c : ℂ)

/-! ## Length-refined creation-mode insertion -/

/-- Transport a length-exact insertion statement from the sorted generators to an arbitrary
element of `virFil`.  The new creation mode raises the allowed word length by one. -/
theorem Lop_virFil_of_sorted_exact {N p : ℕ}
    (H : ∀ w : List ℕ, energyVir w = N → SortedWord w → ∀ i : ℕ,
      Lop c (-(i : ℤ) - 2) (negWordVir c w) ∈
        virFil c (w.length + 1) ((N + i + 2 : ℕ) : ℤ))
    (i : ℕ) {v : VirUniv c} (hv : v ∈ virFil c p (N : ℤ)) :
    Lop c (-(i : ℤ) - 2) v ∈ virFil c (p + 1) ((N + i + 2 : ℕ) : ℤ) := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨w, hw, henergy, hlength, rfl⟩ := hy
      have henergy' : energyVir w = N := by exact_mod_cast henergy
      exact virFil_mono c _ (by omega : w.length + 1 ≤ p + 1) (H w henergy' hw i)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- **Length-refined insertion.**  If `w` is sorted, inserting one creation mode and
straightening produces only sorted words of length at most `w.length + 1`.

This refines `VirModule.Lop_sorted_insert`, whose target remembers energy but not word length. -/
theorem Lop_sorted_insert_virFil (N : ℕ) :
    ∀ w : List ℕ, energyVir w = N → SortedWord w → ∀ i : ℕ,
      Lop c (-(i : ℤ) - 2) (negWordVir c w) ∈
        virFil c (w.length + 1) ((N + i + 2 : ℕ) : ℤ) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w hw hsort i
    match w with
    | [] =>
        have hN : N = 0 := by rw [← hw]; rfl
        subst hN
        apply Submodule.subset_span
        refine ⟨[i], sortedWord_singleton i, ?_, by simp, rfl⟩
        simp [energyVir]
    | (j :: rest) =>
        have hw' : (j + 2) + energyVir rest = N := by rw [← hw, energyVir_cons]
        have hstep : Lop c (-(i : ℤ) - 2) (negWordVir c (j :: rest)) =
            negWordVir c (i :: j :: rest) := rfl
        rw [hstep]
        rcases Nat.lt_or_ge i j with hij | hji
        · rw [negWordVir_swap]
          refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
          · have hrest : energyVir rest < N := by omega
            have h1 := ih _ hrest rest rfl hsort.tail i
            have hmid : energyVir rest + i + 2 < N := by omega
            have h2 := Lop_virFil_of_sorted_exact c (ih _ hmid) j h1
            have henergy : energyVir rest + i + 2 + j + 2 = N + i + 2 := by omega
            have hlength : (rest.length + 1) + 1 = (j :: rest).length + 1 := by simp
            rwa [henergy, hlength] at h2
          · have hmerged : SortedWord ((i + j + 2) :: rest) := by
              apply SortedWord.cons hsort.tail
              intro b hb
              exact le_trans (hsort.head_ge b hb) (by omega)
            have henergy : energyVir ((i + j + 2) :: rest) = N + i + 2 := by
              simp only [energyVir_cons]
              omega
            apply Submodule.subset_span
            refine ⟨(i + j + 2) :: rest, hmerged, ?_, by simp, rfl⟩
            exact_mod_cast henergy
        · have hins : SortedWord (i :: j :: rest) := by
            apply SortedWord.cons hsort
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact hji
            · exact le_trans (hsort.head_ge b hb') hji
          have henergy : energyVir (i :: j :: rest) = N + i + 2 := by
            simp only [energyVir_cons]
            omega
          apply Submodule.subset_span
          refine ⟨i :: j :: rest, hins, ?_, by simp, rfl⟩
          exact_mod_cast henergy

/-- A creation mode sends the length-`p` filtered piece in weight `N` into the length-`p+1`
piece in the shifted weight. -/
theorem Lop_creation_virFil (N p i : ℕ) {v : VirUniv c} (hv : v ∈ virFil c p (N : ℤ)) :
    Lop c (-(i : ℤ) - 2) v ∈ virFil c (p + 1) ((N + i + 2 : ℕ) : ℤ) :=
  Lop_virFil_of_sorted_exact c (Lop_sorted_insert_virFil c N) i hv

/-! ## `L₋₁` differentiates a creation word -/

/-- Translation kills the empty creation word, i.e. the vacuum. -/
theorem Lop_neg_one_negWordVir_nil : Lop c (-1) (negWordVir c []) = 0 := by
  rw [negWordVir_nil, Lop_vacuum c (by omega)]

/-- **The word-level translation identity.**  Commuting `L₋₁` through the first creation mode
increments that mode's index with coefficient `i+1`, then continues recursively on the tail:

`L₋₁ L₋ᵢ₋₂ w = L₋ᵢ₋₂ L₋₁ w + (i+1)L₋ᵢ₋₃ w`. -/
theorem Lop_neg_one_negWordVir_cons (i : ℕ) (w : List ℕ) :
    Lop c (-1) (negWordVir c (i :: w)) =
      Lop c (-(i : ℤ) - 2) (Lop c (-1) (negWordVir c w)) +
        ((i : ℂ) + 1) • negWordVir c ((i + 1) :: w) := by
  have h := Lop_apply_bracket c (-1) (-(i : ℤ) - 2) (negWordVir c w)
  rw [if_neg (by omega : ¬((-1 : ℤ) + (-(i : ℤ) - 2) = 0)), zero_smul, add_zero,
    show (-1 : ℤ) + (-(i : ℤ) - 2) = -((i + 1 : ℕ) : ℤ) - 2 from by
      push_cast; ring,
    show ((-1 : ℤ) : ℂ) - ((-(i : ℤ) - 2 : ℤ) : ℂ) = (i : ℂ) + 1 from by
      push_cast; ring] at h
  simpa only [negWordVir_cons] using h

/-- On a sorted creation word, `L₋₁` raises energy by one while preserving the exact PBW-length
bound. -/
theorem Lop_neg_one_negWordVir_mem_virFil {w : List ℕ} (hw : SortedWord w) :
    Lop c (-1) (negWordVir c w) ∈
      virFil c w.length (((energyVir w + 1 : ℕ)) : ℤ) := by
  induction w with
  | nil =>
      rw [Lop_neg_one_negWordVir_nil]
      exact Submodule.zero_mem _
  | cons i rest ih =>
      rw [Lop_neg_one_negWordVir_cons]
      apply Submodule.add_mem
      · have htail := ih hw.tail
        have h := Lop_creation_virFil c (energyVir rest + 1) rest.length i htail
        have henergy : energyVir rest + 1 + i + 2 = energyVir (i :: rest) + 1 := by
          rw [energyVir_cons]
          omega
        simpa only [List.length_cons, henergy] using h
      · apply Submodule.smul_mem
        apply Submodule.subset_span
        refine ⟨(i + 1) :: rest, SortedWord.cons hw.tail ?_, ?_, by simp, rfl⟩
        · intro b hb
          exact le_trans (hw.head_ge b hb) (by omega)
        · have henergy : energyVir ((i + 1) :: rest) = energyVir (i :: rest) + 1 := by
            simp only [energyVir_cons]
            omega
          exact_mod_cast henergy

/-! ## Preservation of the universal and simple length filtrations -/

/-- **Universal filtration preservation.**  Translation preserves PBW length and raises weight
by one: `L₋₁ virFil(p,n) ⊆ virFil(p,n+1)`. -/
theorem Lop_neg_one_virFil {p : ℕ} {n : ℤ} {v : VirUniv c} (hv : v ∈ virFil c p n) :
    Lop c (-1) v ∈ virFil c p (n + 1) := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨w, hw, henergy, hlength, rfl⟩ := hy
      have h := Lop_neg_one_negWordVir_mem_virFil c hw
      have hweight : ((energyVir w + 1 : ℕ) : ℤ) = n + 1 := by
        push_cast
        omega
      rw [hweight] at h
      exact virFil_mono c _ hlength h
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- **Simple-quotient filtration preservation.**  On `L(c,0)`, `L₋₁` preserves the filtration
degree and raises conformal weight by one. -/
theorem L_neg_one_goodFil {p : ℕ} {n : ℤ} {v : VirUniv c ⧸ maxIdealVir c}
    (hv : v ∈ goodFil c p n) :
    (virasoroSimple c).L (-1) v ∈ goodFil c p (n + 1) := by
  rw [goodFil] at hv ⊢
  obtain ⟨x, hx, rfl⟩ := hv
  rw [← mkQ_L]
  refine ⟨(virasoroVOA c).L (-1) x, ?_, rfl⟩
  rw [virasoroVOA_L_eq_Lop]
  exact Lop_neg_one_virFil c hx

/-- The packaged `GradedFlag` version of `L_neg_one_goodFil`. -/
theorem L_neg_one_virGradedFlag {p : ℕ} {n : ℤ} {v : VirUniv c ⧸ maxIdealVir c}
    (hv : v ∈ (virGradedFlag c).piece p n) :
    (virasoroSimple c).L (-1) v ∈ (virGradedFlag c).piece p (n + 1) :=
  L_neg_one_goodFil c hv

/-- Every power of `L₋₁` preserves PBW length; the `r`-th power raises weight by `r`. -/
theorem L_neg_one_pow_goodFil {p : ℕ} {n : ℤ} {v : VirUniv c ⧸ maxIdealVir c}
    (hv : v ∈ goodFil c p n) (r : ℕ) :
    ((virasoroSimple c).L (-1) ^ r) v ∈ goodFil c p (n + r) := by
  induction r with
  | zero => simpa using hv
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply]
      have h := L_neg_one_goodFil c ih
      rwa [show n + (r : ℤ) + 1 = n + ((r + 1 : ℕ) : ℤ) by push_cast; ring] at h

end VirGoodFil

end VOA
