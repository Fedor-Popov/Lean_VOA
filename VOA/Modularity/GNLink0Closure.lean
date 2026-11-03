/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNReach
import VOA.Modularity.StrictSpanning

/-!
# Gaberdiel--Neitzke Proposition 8: closure of `GNReach`

This file converts the all-parameter induction conclusion `GNReach` into the strict-decrease
spanning datum.  Homogeneous projection removes terms of the wrong conformal degree; on the
remaining terms, positivity of the generator weights bounds every mode index by that degree.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- An `OverGens` word is literally the image of a list of generator indices and mode indices. -/
theorem overGens_eq_map {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ} :
    ∀ {l : List (GNLetter 𝒱)}, OverGens gen wt l →
      ∃ L : List (Fin g × ℕ),
        l = L.map (fun p : Fin g × ℕ => (gen p.1, wt p.1, p.2)) := by
  intro l h
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons p l ih =>
      obtain ⟨i, hgen, hwt⟩ := h p (List.mem_cons_self ..)
      obtain ⟨L, hL⟩ := ih h.tail
      refine ⟨(i, p.2.2) :: L, ?_⟩
      rw [List.map_cons, ← hL]
      congr 1
      exact Prod.ext hgen (Prod.ext hwt rfl)

/-- Mapping an indexed generator word into `GNLetter` format does not change its value. -/
theorem gnWord_map_generators (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (L : List (Fin g × ℕ)) (x : 𝒱) :
    gnWord W (L.map (fun p : Fin g × ℕ => (gen p.1, wt p.1, p.2))) x =
      modeWord W gen L x := by
  induction L with
  | nil => rfl
  | cons p L ih =>
      simp only [List.map_cons, gnWord_cons, modeWord]
      rw [ih]

/-- **GN Proposition 8, closure step.**  If the GN induction statement holds at every grade and
index bound, then positive-weight homogeneous generators give strict-decrease spanning. -/
noncomputable def strictSpanning_of_GNReach (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hwt : ∀ i, 1 ≤ wt i)
    (hReach : ∀ gr N, GNReach W gen wt gr N) :
    StrictSpanning W := by
  classical
  refine
    { g := g
      gen := gen
      wt := wt
      gen_mem := hgen
      spans := ?_ }
  apply le_antisymm
  · rw [← span_homog_eq_top W, Submodule.span_le]
    rintro x ⟨d, hxd⟩
    by_cases hd : d < 0
    · rw [W.positivity d hd, Submodule.mem_bot] at hxd
      subst x
      exact Submodule.zero_mem _
    · have hd0 : 0 ≤ d := le_of_not_gt hd
      let n : ℕ := d.toNat
      have hnd : (n : ℤ) = d := by
        exact Int.toNat_of_nonneg hd0
      have hxFil : x ∈ gnGradeFil W n := by
        apply homog_mem_gnGradeFil W
        rwa [hnd]
      have hxSpan : x ∈ gnSpan W gen wt n := (hReach n n) hxFil
      rw [← piHom_of_mem W hxd]
      rw [gnSpan] at hxSpan
      refine Submodule.span_induction
        (p := fun y _ => piHom W d y ∈ Submodule.span ℂ
          {z | ∃ L : List (Fin g × ℕ), StrictDec L ∧
            z = modeWord W gen L W.vacuum}) ?_ ?_ ?_ ?_ hxSpan
      · rintro y ⟨l, hOK, hweak, hrepeat, hover, rfl⟩
        have hdegree := gnWord_mem_grading W l hOK
        by_cases heq : gnWordDeg l = d
        · rw [piHom_of_mem W (by simpa [heq] using hdegree)]
          have hletterWt : ∀ p ∈ l, 1 ≤ p.2.1 := by
            intro p hp
            obtain ⟨i, _, hiwt⟩ := hover p hp
            rw [hiwt]
            exact hwt i
          have hindexZ := gnWordDeg_idx_le l hletterWt hOK.2
          have hindex : ∀ p ∈ l, p.2.2 ≤ n := by
            intro p hp
            have hz : (p.2.2 : ℤ) ≤ (n : ℤ) := by
              calc
                (p.2.2 : ℤ) ≤ gnWordDeg l := hindexZ p hp
                _ = d := heq
                _ = (n : ℤ) := hnd.symm
            exact_mod_cast hz
          have hstrict := gnStrictDec_of_noRepeat l hweak hrepeat hindex
          obtain ⟨L, hL⟩ := overGens_eq_map hover
          apply Submodule.subset_span
          refine ⟨L, ?_, ?_⟩
          · constructor
            · rw [hL] at hstrict
              simpa only [List.pairwise_map] using hstrict
            · intro p hp
              rw [hL] at hOK
              exact hOK.2 (gen p.1, wt p.1, p.2) (List.mem_map_of_mem hp)
          · rw [hL]
            exact gnWord_map_generators W gen wt L W.vacuum
        · rw [piHom_of_mem_ne W heq hdegree]
          exact Submodule.zero_mem _
      · simp only [map_zero]
        exact Submodule.zero_mem _
      · intro y z _ _ hy hz
        rw [map_add]
        exact Submodule.add_mem _ hy hz
      · intro c y _ hy
        rw [map_smul]
        exact Submodule.smul_mem _ c hy
  · exact le_top

end VOA
