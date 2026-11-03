import VOA.DeligneAudit.D4LevelCoreGenerationAudit

/-! Distinct central-slot assignments in arbitrary middle-raising words. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Each raising letter selects a previously unselected central slot. -/
def centralRaisingChoices : (shape : σ → Fin 6) → (j : ℕ) →
    List ((Fin j → σ) × (σ → Fin 6))
  | shape, 0 => [(Fin.elim0, shape)]
  | shape, j + 1 =>
      (Finset.univ.toList.filter fun t => shape t = 5).flatMap fun t =>
        (centralRaisingChoices (Function.update shape t 4) j).map fun q =>
          (Fin.cons t q.1, q.2)

/-- Selected slots are distinct and belonged to the original central alphabet. -/
theorem centralRaisingChoices_injective (j : ℕ) (shape : σ → Fin 6)
    (q : (Fin j → σ) × (σ → Fin 6)) (hq : q ∈ centralRaisingChoices shape j) :
    Function.Injective q.1 ∧ ∀ i, shape (q.1 i) = 5 := by
  induction j generalizing shape with
  | zero => exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ j ih =>
      obtain ⟨t, ht, hmap⟩ := List.mem_flatMap.mp hq
      obtain ⟨q, hchoice, rfl⟩ := List.mem_map.mp hmap
      have ht : shape t = 5 := by simpa using (List.mem_filter.mp ht).2
      obtain ⟨hinj, hcol⟩ := ih _ q hchoice
      have hne (i : Fin j) : q.1 i ≠ t := by
        intro he
        have hh := hcol i
        rw [he] at hh
        simp only [Function.update_self] at hh
        exact (by decide : (4 : Fin 6) ≠ 5) hh
      constructor
      · intro i k he
        cases i using Fin.cases <;> cases k using Fin.cases
        · rfl
        · exact False.elim (hne _ (by simpa using he.symm))
        · exact False.elim (hne _ (by simpa using he))
        · exact congrArg Fin.succ (hinj (by simpa using he))
      · intro i
        cases i using Fin.cases with
        | zero => exact ht
        | succ i => simpa [Function.update_of_ne (hne i)] using hcol i

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The iterated conversion is a sum over distinct assignments of the raising positions. -/
theorem centralRaisingIteratedEvaluation_choices (j : ℕ) (shape : σ → Fin 6)
    (u : Fin j → ℕ) (P : MvPolynomial σ ℂ) :
    centralRaisingIteratedEvaluation ρ w (List.ofFn u) shape P =
      ((centralRaisingChoices shape j).map fun q =>
        xyzEvaluation ρ w q.2 ((∏ i, X (q.1 i) ^ u i) * P)).sum := by
  induction j generalizing shape P with
  | zero => simp [centralRaisingIteratedEvaluation, centralRaisingChoices]
  | succ j ih =>
      simp only [List.ofFn_succ, centralRaisingIteratedEvaluation, centralRaisingChoices,
        List.flatMap, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro t ht
      rw [ih]
      congr 1
      apply List.map_congr_left
      intro q hq
      congr 1
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring

/-- Exact raising conversion with every positional multiplicity retained. -/
theorem middleRaisingProduct_choices (m j : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (shape : σ → Fin 6) (hc : ∀ i, shape i = 1 ∨ shape i = 4 ∨ shape i = 5)
    (u : Fin j → ℕ) (P : MvPolynomial σ ℂ) :
    middleRaisingProduct ρ (List.ofFn u).reverse (xyzEvaluation ρ w shape P) =
      ((centralRaisingChoices shape j).map fun q =>
        xyzEvaluation ρ w q.2 ((∏ i, X (q.1 i) ^ u i) * P)).sum := by
  rw [middleRaising_polynomial_iterated ρ w m h _ shape hc,
    centralRaisingIteratedEvaluation_choices]

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.centralRaisingChoices_injective
#print axioms VOA.DeligneAudit.D4LevelReduction.centralRaisingIteratedEvaluation_choices
#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaisingProduct_choices
