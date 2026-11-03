import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticProductVanishingBase
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring

/-! Filtered ordinary-jet moments at arbitrary total current budgets.
The X-power and the k<=M filter retain the exact small-budget boundary. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section

/-- The literal finite falling-factorial moment, valid without a relation
between the source cutoff m and the total-current budget M. -/
theorem coeff_X_pow_jet_truncated_mul_eq_filtered_sum {R : Type*} [CommSemiring R]
    (f Q : PowerSeries R) (m M j : ℕ)
    (hf : ∀ k, m ≤ k → PowerSeries.coeff k f = 0) :
    PowerSeries.coeff M (PowerSeries.X ^ j * (jetDerivative j f * Q)) =
      ∑ k ∈ (Finset.univ : Finset (Fin m)).filter (fun k => k.val ≤ M),
        k.val.descFactorial j •
          (PowerSeries.coeff k.val f * PowerSeries.coeff (M - k.val) Q) := by
  classical
  by_cases hj : j ≤ M
  · rw [PowerSeries.coeff_X_pow_mul',if_pos hj]
    let F : ℕ → R := fun n => PowerSeries.coeff (n + j) f *
      ((n + 1).ascFactorial j : R) * PowerSeries.coeff (M - j - n) Q
    let G : Fin m → R := fun k => k.val.descFactorial j •
      (PowerSeries.coeff k.val f * PowerSeries.coeff (M - k.val) Q)
    have hFG (n : ℕ) (hn : n + j < m) : F n = G ⟨n + j,hn⟩ := by
      dsimp [F,G]
      rw [← Nat.add_descFactorial_eq_ascFactorial n j,← Nat.cast_smul_eq_nsmul R,
        smul_eq_mul]
      have he : M - j - n = M - (n + j) := by omega
      rw [he]
      ring
    let idx : ∀ n ∈ Finset.range (M - j + 1), F n ≠ 0 → Fin m := fun n _ hz =>
      ⟨n + j,by
        by_contra h
        have hn : m ≤ n + j := by omega
        apply hz
        simp only [F,hf _ hn,zero_mul]⟩
    rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp_rw [coeff_jetDerivative]
    change (∑ n ∈ Finset.range (M - j + 1), F n) =
      ∑ k ∈ (Finset.univ : Finset (Fin m)).filter (fun k => k.val ≤ M), G k
    apply Finset.sum_bij_ne_zero idx
    · intro n hn hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have hnr := Finset.mem_range.mp hn
      change n + j ≤ M
      omega
    · intro a ha hza b hb hzb he
      have hv := congrArg Fin.val he
      change a+j = b+j at hv
      omega
    · intro k hk hknz
      have hkM := (Finset.mem_filter.mp hk).2
      have hkj : j ≤ k.val := by
        by_contra hh
        have hfac : k.val.descFactorial j = 0 := Nat.descFactorial_of_lt (by omega)
        apply hknz
        simp only [G,hfac,zero_smul]
      let n := k.val-j
      have hn : n ∈ Finset.range (M - j + 1) := by
        apply Finset.mem_range.mpr
        dsimp [n]
        omega
      have hbound : n + j < m := by
        have hklt := k.isLt
        dsimp [n]
        omega
      have hindex : (⟨n + j,hbound⟩ : Fin m) = k := by
        apply Fin.ext
        dsimp [n]
        omega
      have heq : F n = G k := by
        simpa only [hindex] using hFG n hbound
      have hne : F n ≠ 0 := by rw [heq]; exact hknz
      refine ⟨n,hn,hne,?_⟩
      apply Fin.ext
      change n + j = k.val
      dsimp [n]
      omega
    · intro n hn hz
      exact hFG n (idx n hn hz).isLt
  · rw [PowerSeries.coeff_X_pow_mul',if_neg hj]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hkM := (Finset.mem_filter.mp hk).2
    rw [Nat.descFactorial_of_lt (show k.val < j by omega),zero_smul]

/-- Dropping the filter is justified only when every actual source mode
lies inside the total-current budget. -/
theorem coeff_X_pow_jet_truncated_mul_eq_sum_of_mode_bound
    {R : Type*} [CommSemiring R] (f Q : PowerSeries R) (m M j : ℕ)
    (hf : ∀ k, m ≤ k → PowerSeries.coeff k f = 0) (hm : m ≤ M + 1) :
    PowerSeries.coeff M (PowerSeries.X ^ j * (jetDerivative j f * Q)) =
      ∑ k : Fin m, k.val.descFactorial j •
        (PowerSeries.coeff k.val f * PowerSeries.coeff (M - k.val) Q) := by
  classical
  rw [coeff_X_pow_jet_truncated_mul_eq_filtered_sum f Q m M j hf]
  have hs : (Finset.univ : Finset (Fin m)).filter (fun k => k.val ≤ M) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro k _
    have hk := k.isLt
    omega
  rw [hs]

end
#print axioms coeff_X_pow_jet_truncated_mul_eq_filtered_sum
#print axioms coeff_X_pow_jet_truncated_mul_eq_sum_of_mode_bound
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
