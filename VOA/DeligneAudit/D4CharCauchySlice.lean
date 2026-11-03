import VOA.DeligneAudit.D4CharCauchySupport

/-! Finitely supported homogeneous slices of the actual two-row Cauchy sum. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- The finite set of possible rows at bidegree (r,s). -/
def gtCauchySliceRows (N r s : ℕ) : Finset (Fin (N + 2) → ℤ) :=
  (Finset.range (min r s + 1)).image fun b => gtTwoRow N (r + s - b) b

/-- A homogeneous Cauchy slice before evaluating its GT basis vectors. -/
def gtCauchySlice (q : R) (h : PochhammerUnits q) (N r s : ℕ) :
    (Fin (N + 2) → ℤ) →₀ R :=
  Finsupp.onFinset (gtCauchySliceRows N r s)
    (fun lam => if (∑ i, lam i) = (r + s : ℕ) then gtCauchyWeight q h r lam else 0)
    (by
      intro lam hn
      dsimp only at hn
      split_ifs at hn with hd
      · obtain ⟨hb, he⟩ := gtCauchyWeight_shape q h r s lam hn hd
        exact Finset.mem_image.mpr ⟨(lam 1).toNat, by simpa using hb, he.symm⟩
      · exact (hn rfl).elim)

@[simp] theorem gtCauchySlice_apply (q : R) (h : PochhammerUnits q) (N r s : ℕ)
    (lam : Fin (N + 2) → ℤ) :
    gtCauchySlice q h N r s lam =
      if (∑ i, lam i) = (r + s : ℕ) then gtCauchyWeight q h r lam else 0 := rfl

theorem gtCauchySlice_mem_support (q : R) (h : PochhammerUnits q) (N r s : ℕ)
    (lam : Fin (N + 2) → ℤ) :
    lam ∈ (gtCauchySlice q h N r s).support ↔
      (∑ i, lam i) = (r + s : ℕ) ∧ gtCauchyWeight q h r lam ≠ 0 := by
  rw [Finsupp.mem_support_iff, gtCauchySlice_apply]
  split_ifs <;> simp_all

/-- Every basis vector that will be multiplied by e_r is dominant. -/
theorem gtCauchySlice_dominant (q : R) (h : PochhammerUnits q) (N r s : ℕ)
    (lam : Fin (N + 2) → ℤ) (hm : lam ∈ (gtCauchySlice q h N r s).support) :
    Antitone lam :=
  gtCauchyWeight_dominant q h r lam ((gtCauchySlice_mem_support q h N r s lam).mp hm).2

theorem gtTwoRow_second_injective (N d : ℕ) :
    Function.Injective (fun b => gtTwoRow N (d - b) b) := by
  intro b c he
  have hh := congrFun he 1
  simp only [gtTwoRow, Fin.cons_one, Fin.cons_zero] at hh
  exact_mod_cast hh

/-- Evaluation of the free slice is precisely the existing C(2,N+2) coefficient. -/
theorem gtCauchySlice_eval (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N r s : ℕ) :
    Finsupp.linearCombination R (gtEval q u (N + 2)) (gtCauchySlice q h N r s) =
      gtCauchyTwoCoeff q h u N r s := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  calc
    _ = ∑ lam ∈ gtCauchySliceRows N r s,
        gtCauchySlice q h N r s lam • gtEval q u (N + 2) lam := by
      apply Finset.sum_subset Finsupp.support_onFinset_subset
      intro lam _ hn
      change lam ∉ (gtCauchySlice q h N r s).support at hn
      rw [Finsupp.notMem_support_iff.mp hn, zero_smul]
    _ = _ := by
      rw [gtCauchySliceRows, Finset.sum_image
        (fun _ _ _ _ he => gtTwoRow_second_injective N (r + s) he)]
      apply Finset.sum_congr rfl
      intro b hb
      have hb : b ≤ min r s := by simpa using hb
      have ht : (∑ i, gtTwoRow N (r + s - b) b i) = (r + s : ℕ) := by
        rw [gtTwoRow_sum]
        have := hb.trans (min_le_left _ _)
        omega
      rw [gtCauchySlice_apply, if_pos ht, gtCauchyWeight_twoRow q h N r s b hb]
      rfl

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtCauchySlice_mem_support
#print axioms VOA.DeligneAudit.D4Char.gtCauchySlice_dominant
#print axioms VOA.DeligneAudit.D4Char.gtTwoRow_second_injective
#print axioms VOA.DeligneAudit.D4Char.gtCauchySlice_eval
