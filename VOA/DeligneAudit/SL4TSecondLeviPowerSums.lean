import VOA.DeligneAudit.SL4TSecondLeviRelativeRelations
import VOA.DeligneAudit.SL4TTwoCartanKernel

/-! Power-sum generation over the coefficient algebra for the second Levi source. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {B : Type} [CommRing B] [Algebra ℂ B]

/-- The coefficient algebra and both positive power-sum families generate the source. -/
def secondLeviPowerSumAlgebra (e₁ e₂ : ℕ) :
    Subalgebra ℂ (MvPolynomial (SecondLeviModeSlot e₁ e₂) B) :=
  Algebra.adjoin ℂ (Set.range MvPolynomial.C ∪
    Set.range (fun s => secondLeviModePowerSum e₁ e₂ 0 (s + 1)) ∪
    Set.range (fun s => secondLeviModePowerSum e₁ e₂ 1 (s + 1)))

/-- A monomial orbit factors into a coefficient and two independent alphabet orbit sums. -/
theorem secondLeviModeOrbitSum_monomial (e₁ e₂ : ℕ)
    (u : SecondLeviModeSlot e₁ e₂ →₀ ℕ) (b : B) :
    secondLeviModeOrbitSum e₁ e₂ (monomial u b) =
      MvPolynomial.C b *
        aeval (fun i : Fin e₁ => (X (.inl i) : MvPolynomial _ B))
          (D4Levi.rzOrbitSum (Fin e₁) (∏ i, X i ^ u (.inl i))) *
        aeval (fun i : Fin e₂ => (X (.inr i) : MvPolynomial _ B))
          (D4Levi.rzOrbitSum (Fin e₂) (∏ i, X i ^ u (.inr i))) := by
  classical
  have hm : (monomial u b : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) =
      MvPolynomial.C b * ∏ i, X i ^ u i := by
    rw [monomial_eq]
    congr 1
    exact u.prod_fintype _ (fun i => pow_zero _)
  simp only [secondLeviModeOrbitSum, hm, map_mul, rename_C, map_prod, map_pow,
    rename_X, Fintype.prod_sum_type, Fintype.sum_prod_type,
    secondLeviSlotPermutation, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    D4Levi.rzOrbitSum, map_sum, aeval_X, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (by ext e; simp)
  intro e he
  apply Finset.sum_congr (by ext f; simp)
  intro f hf
  congr 2

/-- A symmetric polynomial in the first alphabet lies in the coefficient power-sum algebra. -/
theorem secondLeviFirstAlphabet_mem_powerSumAlgebra (e₁ e₂ : ℕ)
    (P : MvPolynomial (Fin e₁) ℂ) (hP : P ∈ symmetricSubalgebra (Fin e₁) ℂ) :
    aeval (fun i => (X (.inl i) : MvPolynomial (SecondLeviModeSlot e₁ e₂) B)) P ∈
      secondLeviPowerSumAlgebra e₁ e₂ := by
  apply D4Levi.symmetric_image_mem_of_power_sums _ _ _ _ _ P hP
  intro s
  cases s with
  | zero => simp [psum_zero]
  | succ s =>
    have hm : secondLeviModePowerSum (B := B) e₁ e₂ 0 (s + 1) ∈
        secondLeviPowerSumAlgebra e₁ e₂ :=
      Algebra.subset_adjoin (Or.inl (Or.inr ⟨s, rfl⟩))
    simpa [psum, map_sum, map_pow, aeval_X, secondLeviModePowerSum] using hm

/-- A symmetric polynomial in the second alphabet lies in the coefficient power-sum algebra. -/
theorem secondLeviSecondAlphabet_mem_powerSumAlgebra (e₁ e₂ : ℕ)
    (P : MvPolynomial (Fin e₂) ℂ) (hP : P ∈ symmetricSubalgebra (Fin e₂) ℂ) :
    aeval (fun i => (X (.inr i) : MvPolynomial (SecondLeviModeSlot e₁ e₂) B)) P ∈
      secondLeviPowerSumAlgebra e₁ e₂ := by
  apply D4Levi.symmetric_image_mem_of_power_sums _ _ _ _ _ P hP
  intro s
  cases s with
  | zero => simp [psum_zero]
  | succ s =>
    have hm : secondLeviModePowerSum (B := B) e₁ e₂ 1 (s + 1) ∈
        secondLeviPowerSumAlgebra e₁ e₂ :=
      Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)
    simpa [psum, map_sum, map_pow, aeval_X, secondLeviModePowerSum] using hm

theorem secondLeviModeOrbitSum_mem_powerSumAlgebra (e₁ e₂ : ℕ)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) :
    secondLeviModeOrbitSum e₁ e₂ P ∈ secondLeviPowerSumAlgebra e₁ e₂ := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [secondLeviModeOrbitSum_monomial]
    apply Subalgebra.mul_mem
    · apply Subalgebra.mul_mem
      · exact Algebra.subset_adjoin (Or.inl (Or.inl ⟨b, rfl⟩))
      · exact secondLeviFirstAlphabet_mem_powerSumAlgebra e₁ e₂ _
          (D4Levi.rzOrbitSum_symmetric _ _)
    · exact secondLeviSecondAlphabet_mem_powerSumAlgebra e₁ e₂ _
        (D4Levi.rzOrbitSum_symmetric _ _)
  | add P R hP hR =>
    have he : secondLeviModeOrbitSum e₁ e₂ (P + R) =
        secondLeviModeOrbitSum e₁ e₂ P + secondLeviModeOrbitSum e₁ e₂ R := by
      simp [secondLeviModeOrbitSum, Finset.sum_add_distrib]
    rw [he]
    exact Subalgebra.add_mem _ hP hR

/-- Power-sum degree induction covers every separately symmetric coefficient polynomial. -/
theorem secondLeviSymmetricModes_le_powerSumAlgebra (e₁ e₂ : ℕ) :
    secondLeviSymmetricModes (B := B) e₁ e₂ ≤ secondLeviPowerSumAlgebra e₁ e₂ := by
  classical
  intro P hP
  have he : secondLeviModeOrbitSum e₁ e₂ P =
      (Fintype.card (Equiv.Perm (Fin e₁) × Equiv.Perm (Fin e₂)) : ℂ) • P := by
    simp only [secondLeviModeOrbitSum, show ∀ e,
      rename (secondLeviSlotPermutation e₁ e₂ e) P = P from hP]
    rw [Finset.sum_const, Finset.card_univ]
    exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm
  let n := Fintype.card (Equiv.Perm (Fin e₁) × Equiv.Perm (Fin e₂))
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm := (secondLeviPowerSumAlgebra e₁ e₂).smul_mem
    (secondLeviModeOrbitSum_mem_powerSumAlgebra e₁ e₂ P) (n : ℂ)⁻¹
  rw [he] at hm
  change (n : ℂ)⁻¹ • ((n : ℂ) • P) ∈ secondLeviPowerSumAlgebra e₁ e₂ at hm
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hm

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviModeOrbitSum_monomial
#print axioms VOA.DeligneAudit.SL4T.secondLeviFirstAlphabet_mem_powerSumAlgebra
#print axioms VOA.DeligneAudit.SL4T.secondLeviSecondAlphabet_mem_powerSumAlgebra
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeOrbitSum_mem_powerSumAlgebra
#print axioms VOA.DeligneAudit.SL4T.secondLeviSymmetricModes_le_powerSumAlgebra
