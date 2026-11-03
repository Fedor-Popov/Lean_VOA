import VOA.DeligneAudit.D4CharCauchyOne

/-! The explicit two-variable Q expansion used to state C(2,N) coefficientwise. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

theorem sum_gtRows_two_nat {A : Type*} [AddCommMonoid A] (a b : ℕ)
    (f : (Fin 1 → ℤ) → A) :
    (∑ μ ∈ gtRows ![(a : ℤ), (b : ℤ)], f μ) =
      ∑ r ∈ Finset.Icc b a, f ![(r : ℤ)] := by
  classical
  refine Finset.sum_bij' (fun μ _ => (μ 0).toNat) (fun r _ => ![(r : ℤ)])
    ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    have hm := (mem_gtRows _ _).mp hμ 0
    change (b : ℤ) ≤ μ 0 ∧ μ 0 ≤ a at hm
    change (μ 0).toNat ∈ Finset.Icc b a
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro r hr
    have hr := Finset.mem_Icc.mp hr
    apply (mem_gtRows _ _).mpr
    intro i
    fin_cases i
    simp
    omega
  · intro μ hμ
    have hm := (mem_gtRows _ _).mp hμ 0
    change (b : ℤ) ≤ μ 0 ∧ μ 0 ≤ a at hm
    ext i
    fin_cases i
    simp
    omega
  · intro r _
    simp
  · intro μ hμ
    have hm := (mem_gtRows _ _).mp hμ 0
    change (b : ℤ) ≤ μ 0 ∧ μ 0 ≤ a at hm
    congr 1
    ext i
    fin_cases i
    simp
    omega

/-- Q_(a,b)(x,y), with every denominator and both variable degrees explicit. -/
theorem gtQ_two_expansion (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (a b : ℕ) :
    gtQ q h u 2 ![(a : ℤ), (b : ℤ)] = ∑ r ∈ Finset.Icc b a,
      gtInvPoch q h (a - r : ℕ) * gtInvPoch q h (r - b : ℕ) * gtInvPoch q h b *
        (u 0 : R) ^ r * (u 1 : R) ^ (a + b - r) := by
  rw [gtQ_branching_product q h u 1 _ (by simp), sum_gtRows_two_nat]
  apply Finset.sum_congr rfl
  intro r hr
  have hr := Finset.mem_Icc.mp hr
  rw [gtQCoeff_two]
  have hg : gtQ q h u 1 ![(r : ℤ)] = gtInvPoch q h r * (u 0 : R) ^ r := by
    simpa [gtOneRow] using gtQ_oneRow_one q h u r
  rw [hg]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_succ,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, Int.toNat_natCast]
  have hpow : (a : ℤ) + b - r = ((a + b - r : ℕ) : ℤ) := by omega
  rw [← Int.natCast_sub hr.2, ← Int.natCast_sub hr.1, hpow, zpow_natCast, Units.val_pow_eq_pow_val]
  calc
    _ = (CarrierChain.qpochGen q r * gtInvPoch q h r) *
        (gtInvPoch q h (a - r : ℕ) * gtInvPoch q h (r - b : ℕ) *
          gtInvPoch q h b * (u 0 : R) ^ r * (u 1 : R) ^ (a + b - r)) := by ring
    _ = _ := by rw [gtPoch_mul_invPoch, one_mul]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.sum_gtRows_two_nat
#print axioms VOA.DeligneAudit.D4Char.gtQ_two_expansion
