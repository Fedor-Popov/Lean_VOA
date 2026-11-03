/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaWardSpecialization

/-!
# Charge-independent straightening of negative Verma words

All Verma modules are placed in one product. Negative-mode commutators have
no central or highest-weight term, so insertion sorting works simultaneously
at every (c,h). Faithful PBW coordinates then identify the same constant
straightening coefficients at every charge and highest weight.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangWardClosure

/-- A family contains one actual state at every charge and highest weight. -/
abbrev VermaFamily := ∀ c h : ℂ, Verma c h

/-- Apply the same mode separately in every member of the family. -/
noncomputable def familyMode (m : ℤ) : VermaFamily →ₗ[ℂ] VermaFamily where
  toFun v c h := vermaMode c h m (v c h)
  map_add' _ _ := by ext c h; exact map_add _ _ _
  map_smul' r v := by
    funext c h
    exact (vermaMode c h m).map_smul r (v c h)

/-- The same creation word interpreted at every (c,h). -/
noncomputable def familyWord (w : List ℕ) : VermaFamily := fun c h => negWord c h w

/-- Prefixing a creation word commutes with its simultaneous interpretation. -/
@[simp] theorem familyWord_cons (i : ℕ) (w : List ℕ) :
    familyWord (i::w)=familyMode (-(i:ℤ)-1) (familyWord w) := rfl

/-- Negative-mode straightening has constant coefficients, independently of
central charge and highest weight. This is equality in the whole family. -/
theorem familyWord_swap (i j : ℕ) (w : List ℕ) :
    familyWord (i::j::w)=familyWord (j::i::w)+
      ((j:ℂ)-(i:ℂ)) • familyWord ((i+j+1)::w) := by
  funext c h
  exact negWord_swap c h i j w

/-- Span of ordered negative-mode words at one Verma level. -/
noncomputable def familySortedSpan (N : ℕ) : Submodule ℂ (VermaFamily) :=
  Submodule.span ℂ {x | ∃ w : List ℕ,
    SortedWord w ∧ energyHW w = N ∧ familyWord w = x}

/-- An already ordered word is one of the defining generators of the sorted span at its own energy. -/
theorem familyWord_mem_sortedSpan_of_sorted {w : List ℕ}
    (hw : SortedWord w) {N : ℕ} (hN : energyHW w = N) :
    familyWord w ∈ familySortedSpan N :=
  Submodule.subset_span ⟨w, hw, hN, rfl⟩

/-- Transport one creation-mode insertion from ordered generators to their span. -/
theorem familySortedSpan_stable {N : ℕ}
    (H : ∀ w : List ℕ, energyHW w = N → SortedWord w → ∀ i : ℕ,
      familyMode (-(i : ℤ) - 1) (familyWord w) ∈ familySortedSpan (N + i + 1))
    (i : ℕ) {v : VermaFamily} (hv : v ∈ familySortedSpan N) :
    familyMode (-(i : ℤ) - 1) v ∈ familySortedSpan (N + i + 1) := by
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨w, hw, he, rfl⟩ := hy; exact H w he hw i
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- Insertion sorting for Verma creation words. -/
theorem familyMode_sorted_insert (N : ℕ) :
    ∀ w : List ℕ, energyHW w = N → SortedWord w → ∀ i : ℕ,
      familyMode (-(i : ℤ) - 1) (familyWord w) ∈
        familySortedSpan (N + i + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w hw hsort i
    match w with
    | [] =>
        have hN : N = 0 := by rw [← hw]; rfl
        subst hN
        change familyWord [i] ∈ familySortedSpan (0 + i + 1)
        exact familyWord_mem_sortedSpan_of_sorted (sortedWord_singleton i)
          (by simp only [energyHW_cons, energyHW_nil]; omega)
    | (j :: rest) =>
        have hw' : j + 1 + energyHW rest = N := by rw [← hw, energyHW_cons]
        change familyWord (i :: j :: rest) ∈ familySortedSpan (N + i + 1)
        rcases Nat.lt_or_ge i j with hij | hji
        · rw [familyWord_swap]
          refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
          · have hrest : energyHW rest < N := by omega
            have h1 : familyMode (-(i : ℤ) - 1) (familyWord rest) ∈
                familySortedSpan (energyHW rest + i + 1) :=
              ih _ hrest rest rfl hsort.tail i
            have hmiddle : energyHW rest + i + 1 < N := by omega
            have h2 := familySortedSpan_stable (ih _ hmiddle) j h1
            have hreindex : energyHW rest + i + 1 + j + 1 = N + i + 1 := by omega
            rw [hreindex] at h2
            exact h2
          · refine familyWord_mem_sortedSpan_of_sorted (SortedWord.cons hsort.tail ?_) ?_
            · intro b hb
              exact le_trans (hsort.head_ge b hb) (by omega)
            · simp only [energyHW_cons]
              omega
        · refine familyWord_mem_sortedSpan_of_sorted (SortedWord.cons hsort ?_) ?_
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact hji
            · exact le_trans (hsort.head_ge b hb') hji
          · simp only [energyHW_cons]
            omega

/-- Every negative-mode creation word straightens into ordered PBW words of the same level. -/
theorem familyWord_mem_sortedSpan (w : List ℕ) :
    familyWord w ∈ familySortedSpan (energyHW w) := by
  induction w with
  | nil => exact familyWord_mem_sortedSpan_of_sorted sortedWord_nil rfl
  | cons i rest ih =>
      have h := familySortedSpan_stable
        (familyMode_sorted_insert (energyHW rest)) i ih
      have hreindex : energyHW rest + i + 1 = energyHW (i :: rest) := by
        rw [energyHW_cons]
        omega
      rw [hreindex] at h
      exact h



/-- Take the actual PBW coordinates of one member of a Verma family. -/
noncomputable def familyCoordinates (c h : ℂ) :
    VermaFamily →ₗ[ℂ] ({w : List ℕ // SortedWord w} →₀ ℂ) where
  toFun v := (vermaSortedBasis c h).repr (v c h)
  map_add' _ _ := map_add _ _ _
  map_smul' r v := (vermaSortedBasis c h).repr.map_smul r (v c h)

/-- An ordered family word has one coordinate equal to one at every (c,h). -/
theorem familyCoordinates_sorted (c h : ℂ) (w : {w : List ℕ // SortedWord w}) :
    familyCoordinates c h (familyWord w.val)=Finsupp.single w 1 := by
  change (vermaSortedBasis c h).repr (negWord c h w.val)=_
  rw [← vermaSortedBasis_apply]
  exact (vermaSortedBasis c h).repr_self w

/-- Straightening coefficients of any negative word are the same in every
Verma module. The simultaneous span proof is what makes this uniform; separate
spanning statements at each charge would not suffice. -/
theorem verma_negWord_coordinates_independent (c h c' h' : ℂ) (w : List ℕ) :
    (vermaSortedBasis c h).repr (negWord c h w)=
      (vermaSortedBasis c' h').repr (negWord c' h' w) := by
  have hm := familyWord_mem_sortedSpan w
  change familyCoordinates c h (familyWord w)=familyCoordinates c' h' (familyWord w)
  generalize he : familyWord w = v at hm ⊢
  clear he
  induction hm using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u,hu,he,rfl⟩ := hv
    exact (familyCoordinates_sorted c h ⟨u,hu⟩).trans
      (familyCoordinates_sorted c' h' ⟨u,hu⟩).symm
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add,ha,hb]
  | smul r a _ ha => simp only [map_smul,ha]

end VOA.InverseDS.VirasoroVerma
