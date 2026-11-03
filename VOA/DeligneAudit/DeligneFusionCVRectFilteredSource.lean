import VOA.DeligneAudit.DeligneFusionCVRectFilteredPolynomial
import VOA.DeligneAudit.DeligneFusionPBW

/-!
# From the actual PBW polynomial quotient to the full current cyclic source

Highest-weight current relations supply PBW reduction to lowering words.
Consequently the finite polynomial quotient bound controls the full original
cyclic representation. This requires neither original finite-dimensionality
nor independence of current-degree pieces.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V}

theorem negativeCyclic_op (a : Fin 3) (r : ℕ) :
    negativeCyclic R w ≤ (negativeCyclic R w).comap (R.op (negRoot a) r) := by
  rw [negativeCyclic, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact Submodule.subset_span ⟨(a, r) :: l, rfl⟩

theorem lower_word_mem_negative (l : List (Fin 8 × ℕ))
    (hlow : ∀ x ∈ l, lowSl3 x.1) : wordOp R l w ∈ negativeCyclic R w := by
  induction l with
  | nil => exact Submodule.subset_span ⟨[], rfl⟩
  | cons x l ih =>
      have hi := ih (fun y hy => hlow y (by simp [hy]))
      have hx := hlow x (by simp)
      have hd : x.1 = 3 ∨ x.1 = 4 ∨ x.1 = 5 := by
        unfold lowSl3 at hx
        omega
      rcases hd with hd | hd | hd
      · change R.op x.1 x.2 (wordOp R l w) ∈ negativeCyclic R w
        rw [hd]
        exact negativeCyclic_op (R := R) (w := w) 0 x.2 hi
      · change R.op x.1 x.2 (wordOp R l w) ∈ negativeCyclic R w
        rw [hd]
        exact negativeCyclic_op (R := R) (w := w) 2 x.2 hi
      · change R.op x.1 x.2 (wordOp R l w) ∈ negativeCyclic R w
        rw [hd]
        exact negativeCyclic_op (R := R) (w := w) 1 x.2 hi

theorem cv_nonlow_hw {ε ν ϱ : Weight} {j : ℕ} (h : CV3Rel R w ε ν ϱ j) :
    ∀ a r, ¬ lowSl3 a → R.op a r w ∈ ℂ ∙ w ∧ (1 ≤ r → R.op a r w = 0) := by
  intro a r ha
  unfold lowSl3 at ha
  by_cases he : a.val < 3
  · rw [h.raising a he r]
    exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
  · have h6 : 6 ≤ a.val := by omega
    refine ⟨?_, fun hr => h.cartan_pos a h6 r hr⟩
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have hh : a = 6 ∨ a = 7 := by omega
      rcases hh with rfl | rfl
      · rw [h.cartan_first]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [h.cartan_second]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    · rw [h.cartan_pos a h6 r hr]
      exact Submodule.zero_mem _

def currentCyclic (R : CurrentModule bracketTable V) (w : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun l : List (Fin 8 × ℕ) => wordOp R l w)

theorem currentCyclic_eq_negative {ε ν ϱ : Weight} {j : ℕ} (h : CV3Rel R w ε ν ϱ j) :
    currentCyclic R w = negativeCyclic R w := by
  apply le_antisymm
  · rw [currentCyclic, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    have hc : wordOp R l w ∈ cycDeg R w (SectorGraded.wordDeg l) :=
      Submodule.subset_span ⟨l, rfl, rfl⟩
    have hp := cycDeg_le_sortedLow keySl3 lowSl3 R keySl3_low (cv_nonlow_hw h) _ hc
    apply Submodule.span_le.mpr ?_ hp
    rintro _ ⟨l', _, hl, _, rfl⟩
    exact lower_word_mem_negative l' hl
  · rw [negativeCyclic, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact Submodule.subset_span ⟨negWord l, rfl⟩

theorem currentCyclic_bound_of_polynomial {ε ν ϱ : Weight} {j : ℕ}
    (h : CV3Rel R w ε ν ϱ j) {ι : Type} (letter : ι → NegLtr)
    (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.restrictScalars ℂ ≤ LinearMap.ker (polyEval R w letter))
    (hcover : ∀ a r, (∃ i, letter i = (a, r)) ∨ R.op (negRoot a) r w = 0)
    [FiniteDimensional ℂ (MvPolynomial ι ℂ ⧸ I.restrictScalars ℂ)] :
    FiniteDimensional ℂ (currentCyclic R w) ∧
      Module.finrank ℂ (currentCyclic R w) ≤
        Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I.restrictScalars ℂ) := by
  rw [currentCyclic_eq_negative h]
  exact negativeCyclic_bound_of_polynomial R w letter I hI hcover

/-- An actual cyclic source inherits the finite polynomial quotient bound.
The cyclicity premise is word-spanning, not a dimension statement. -/
theorem source_bound_of_polynomial {ε ν ϱ : Weight} {j : ℕ}
    (h : CV3Rel R w ε ν ϱ j) (hspan : currentCyclic R w = ⊤)
    {ι : Type} (letter : ι → NegLtr) (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.restrictScalars ℂ ≤ LinearMap.ker (polyEval R w letter))
    (hcover : ∀ a r, (∃ i, letter i = (a, r)) ∨ R.op (negRoot a) r w = 0)
    [FiniteDimensional ℂ (MvPolynomial ι ℂ ⧸ I.restrictScalars ℂ)] :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤
      Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I.restrictScalars ℂ) := by
  obtain ⟨hFD, hdim⟩ := currentCyclic_bound_of_polynomial h letter I hI hcover
  have hs : Function.Surjective (currentCyclic R w).subtype := by
    intro v
    exact ⟨⟨v, hspan ▸ Submodule.mem_top⟩, rfl⟩
  haveI := hFD
  haveI := Module.Finite.of_surjective (currentCyclic R w).subtype hs
  exact ⟨inferInstance, (LinearMap.finrank_le_finrank_of_surjective hs).trans hdim⟩

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.currentCyclic_eq_negative
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.source_bound_of_polynomial
