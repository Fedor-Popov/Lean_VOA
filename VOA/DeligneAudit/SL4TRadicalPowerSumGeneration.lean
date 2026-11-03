import VOA.DeligneAudit.SL4TRadicalPowerSumKernel
import VOA.DeligneAudit.D4LeviKSRzOrbit

/-! Positive power sums generate all separately symmetric radical mode polynomials. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

-- Use the standard finite-index instances in the presence of simplex-category imports.
attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- Inclusion of one alphabet into the three labelled radical alphabets. -/
def radicalSlotEmbedding (d : Fin 3 → ℕ) (j : Fin 3) : Fin (d j) → RadicalModeSlot d :=
  match j with
  | 0 => Sum.inl
  | 1 => fun i => .inr (.inl i)
  | 2 => fun i => .inr (.inr i)

/-- The positional and usual symmetric-function conventions for power sums agree. -/
theorem radicalModePowerSum_eq_rename (d : Fin 3 → ℕ) (j : Fin 3) (r : ℕ) :
    radicalModePowerSum d j r =
      rename (radicalSlotEmbedding d j) (psum (Fin (d j)) ℂ r) := by
  classical
  have he : rename (radicalSlotEmbedding d j) (psum (Fin (d j)) ℂ r) =
      ∑ i, (X (radicalSlotEmbedding d j i) : RadicalModePolynomial d) ^ r := by
    simp only [psum, map_sum, map_pow, rename_X]
  rw [he]
  fin_cases j <;>
    simp [radicalModePowerSum, radicalSlotList, radicalSlotColour, radicalSlotEmbedding,
      List.map_ofFn, List.sum_ofFn, Function.comp_def]
  all_goals rfl

/-- Every symmetric polynomial on one alphabet belongs to the positive power-sum algebra. -/
theorem radicalAlphabet_symmetric_mem_powerSumAlgebra (d : Fin 3 → ℕ) (j : Fin 3)
    (P : MvPolynomial (Fin (d j)) ℂ) (hP : P ∈ symmetricSubalgebra (Fin (d j)) ℂ) :
    rename (radicalSlotEmbedding d j) P ∈ radicalPowerSumAlgebra d := by
  apply D4Levi.symmetric_image_mem_of_power_sums (Fin (d j))
    (RadicalModePolynomial d) (rename (radicalSlotEmbedding d j))
    (radicalPowerSumAlgebra d) _ P hP
  intro r
  cases r with
  | zero => simp [psum_zero]
  | succ r =>
    rw [← radicalModePowerSum_eq_rename]
    exact Algebra.subset_adjoin ⟨(j, r), rfl⟩

/-- An orbit sum of a monomial factors into three independent symmetric orbit sums. -/
theorem radicalModeOrbitSum_monomial (d : Fin 3 → ℕ) (u : RadicalModeSlot d →₀ ℕ) :
    radicalModeOrbitSum d (monomial u 1) =
      ∏ j : Fin 3, rename (radicalSlotEmbedding d j)
        (D4Levi.rzOrbitSum (Fin (d j)) (∏ i, X i ^ u (radicalSlotEmbedding d j i))) := by
  classical
  have hm : (monomial u 1 : RadicalModePolynomial d) = ∏ i, X i ^ u i := by
    rw [monomial_eq, map_one, one_mul]
    exact u.prod_fintype _ (fun i => pow_zero _)
  simp only [radicalModeOrbitSum, D4Levi.rzOrbitSum, map_sum]
  trans ∑ e : (j : Fin 3) → Equiv.Perm (Fin (d j)),
    ∏ j : Fin 3, rename (radicalSlotEmbedding d j)
      (rename (e j) (∏ i, X i ^ u (radicalSlotEmbedding d j i)))
  · apply Finset.sum_congr rfl
    intro e he
    rw [hm]
    simp only [map_prod, map_pow, rename_X]
    rw [Fin.prod_univ_three]
    simp only [Fintype.prod_sum_type, radicalSlotPermutation,
      radicalSlotEmbedding, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
    let A : RadicalModePolynomial d :=
      ∏ i : Fin (d 0), X (.inl (e 0 i)) ^ u (.inl i)
    let B : RadicalModePolynomial d :=
      ∏ i : Fin (d 1), X (.inr (.inl (e 1 i))) ^ u (.inr (.inl i))
    let C : RadicalModePolynomial d :=
      ∏ i : Fin (d 2), X (.inr (.inr (e 2 i))) ^ u (.inr (.inr i))
    change A * (B * C) = A * B * C
    exact (mul_assoc A B C).symm
  · let g : (j : Fin 3) → Equiv.Perm (Fin (d j)) → RadicalModePolynomial d :=
      fun j e => rename (radicalSlotEmbedding d j)
        (rename e (∏ i, X i ^ u (radicalSlotEmbedding d j i)))
    have hdist : (∑ e : (j : Fin 3) → Equiv.Perm (Fin (d j)), ∏ j, g j (e j)) =
        ∏ j : Fin 3, ∑ e : Equiv.Perm (Fin (d j)), g j e :=
      (Fintype.prod_sum g).symm
    refine Eq.trans ?_ (hdist.trans ?_)
    · apply Finset.sum_congr
      · ext e; simp
      · intro e he
        apply Finset.prod_congr
        · ext j; simp
        · intro j hj; rfl
    · apply Finset.prod_congr
      · ext j; simp
      · intro j hj
        apply Finset.sum_congr
        · ext e; simp
        · intro e he; rfl

/-- Orbit averaging lands in the algebra of positive power sums. -/
theorem radicalModeOrbitSum_mem_powerSumAlgebra (d : Fin 3 → ℕ)
    (P : RadicalModePolynomial d) : radicalModeOrbitSum d P ∈ radicalPowerSumAlgebra d := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u z =>
    have he : (monomial u z : RadicalModePolynomial d) = z • monomial u 1 := by
      simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [he]
    have hs : radicalModeOrbitSum d (z • monomial u 1) =
        z • radicalModeOrbitSum d (monomial u 1) := by
      simp [radicalModeOrbitSum, Finset.smul_sum]
    rw [hs]
    apply Subalgebra.smul_mem
    rw [radicalModeOrbitSum_monomial]
    apply Subalgebra.prod_mem
    intro j hj
    exact radicalAlphabet_symmetric_mem_powerSumAlgebra d j _
      (D4Levi.rzOrbitSum_symmetric _ _)
  | add P Q hP hQ =>
    have he : radicalModeOrbitSum d (P + Q) =
        radicalModeOrbitSum d P + radicalModeOrbitSum d Q := by
      simp [radicalModeOrbitSum, Finset.sum_add_distrib]
    rw [he]
    exact (radicalPowerSumAlgebra d).add_mem hP hQ

/-- Separate symmetry is sufficient for positive power-sum generation. -/
theorem radicalSymmetricModes_le_powerSumAlgebra (d : Fin 3 → ℕ) :
    radicalSymmetricModes d ≤ radicalPowerSumAlgebra d := by
  classical
  intro P hP
  have he : radicalModeOrbitSum d P =
      (Fintype.card ((j : Fin 3) → Equiv.Perm (Fin (d j))) : ℂ) • P := by
    simp only [radicalModeOrbitSum, show ∀ e,
      rename (radicalSlotPermutation d e) P = P from hP]
    rw [Finset.sum_const, Finset.card_univ]
    exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm
  let n := Fintype.card ((j : Fin 3) → Equiv.Perm (Fin (d j)))
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm := (radicalPowerSumAlgebra d).smul_mem
    (radicalModeOrbitSum_mem_powerSumAlgebra d P) (n : ℂ)⁻¹
  rw [he] at hm
  change (n : ℂ)⁻¹ • ((n : ℂ) • P) ∈ radicalPowerSumAlgebra d at hm
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hm

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.radicalModePowerSum_eq_rename
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabet_symmetric_mem_powerSumAlgebra
#print axioms VOA.DeligneAudit.SL4T.radicalModeOrbitSum_monomial
#print axioms VOA.DeligneAudit.SL4T.radicalModeOrbitSum_mem_powerSumAlgebra
#print axioms VOA.DeligneAudit.SL4T.radicalSymmetricModes_le_powerSumAlgebra
