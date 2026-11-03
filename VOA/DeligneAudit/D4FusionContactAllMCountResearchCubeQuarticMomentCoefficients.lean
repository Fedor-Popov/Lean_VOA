import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticProductVanishingBase
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrent
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! Exact finite falling-factorial moments of whole current coefficients.
Ordinary derivatives retain their factorials; high source modes vanish. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- An ordinary jet coefficient convolution is an explicit finite moment.
The source cutoff lies inside the total-current budget; no derivative-order
bound is needed because every higher falling factorial is zero. -/
theorem coeff_jet_truncated_mul_eq_sum {R : Type*} [CommSemiring R]
    (f Q : PowerSeries R) (m M j : ℕ)
    (hf : ∀ k, m ≤ k → PowerSeries.coeff k f = 0) (hm : m ≤ M + 1) :
    PowerSeries.coeff (M-j) (jetDerivative j f * Q) =
      ∑ k : Fin m, k.val.descFactorial j •
        (PowerSeries.coeff k.val f * PowerSeries.coeff (M-k.val) Q) := by
  classical
  let F : ℕ → R := fun n => PowerSeries.coeff (n+j) f *
    ((n+1).ascFactorial j : R) * PowerSeries.coeff (M-j-n) Q
  let G : Fin m → R := fun k => k.val.descFactorial j •
    (PowerSeries.coeff k.val f * PowerSeries.coeff (M-k.val) Q)
  have hFG (n : ℕ) (hn : n+j < m) : F n = G ⟨n+j,hn⟩ := by
    dsimp [F,G]
    rw [← Nat.add_descFactorial_eq_ascFactorial n j,← Nat.cast_smul_eq_nsmul R,smul_eq_mul]
    have he : M-j-n = M-(n+j) := by omega
    rw [he]
    ring
  let idx : ∀ n ∈ Finset.range (M-j+1), F n ≠ 0 → Fin m := fun n _ hz =>
    ⟨n+j,by
      by_contra h
      have hn : m ≤ n+j := by omega
      apply hz
      simp only [F,hf _ hn,zero_mul]⟩
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [coeff_jetDerivative]
  change (∑ n ∈ Finset.range (M-j+1), F n) = ∑ k : Fin m, G k
  apply Finset.sum_bij_ne_zero idx (fun _ _ _ => Finset.mem_univ _)
  · intro a ha hza b hb hzb he
    have hv := congrArg Fin.val he
    change a+j = b+j at hv
    omega
  · intro k _ hk
    have hkj : j ≤ k.val := by
      by_contra hh
      have hfac : k.val.descFactorial j = 0 := Nat.descFactorial_of_lt (by omega)
      apply hk
      simp only [G,hfac,zero_smul]
    let n := k.val-j
    have hn : n ∈ Finset.range (M-j+1) := by
      apply Finset.mem_range.mpr
      have hklt := k.isLt
      dsimp [n]
      omega
    have hbound : n+j < m := by
      have hklt := k.isLt
      dsimp [n]
      omega
    have hindex : (⟨n+j,hbound⟩ : Fin m) = k := by
      apply Fin.ext
      dsimp [n]
      omega
    have heq : F n = G k := by
      simpa only [hindex] using hFG n hbound
    have hne : F n ≠ 0 := by rw [heq]; exact hk
    refine ⟨n,hn,hne,?_⟩
    apply Fin.ext
    change n+j = k.val
    dsimp [n]
    omega
  · intro n hn hz
    exact hFG n (idx n hn hz).isLt

/-- Every normalized current coefficient above the actual mode cutoff is zero. -/
theorem actualCurrent_coeff_high (m k : ℕ) (c : Fin 8) (hk : m ≤ k) :
    PowerSeries.coeff k (actualCurrent m c) = 0 := by
  rw [actualCurrent_coeff]
  have hnot : ¬k < m := by omega
  simp only [actualMode,modeX,dif_neg hnot,smul_zero]

/-- Explicit finite moment of the actual whole normalized D4 current. -/
theorem coeff_jet_actualCurrent_mul_eq_sum (m M j : ℕ) (hm : m ≤ M + 1)
    (c : Fin 8) (Q : PowerSeries (MvPolynomial (Vars m) ℂ)) :
    PowerSeries.coeff (M-j) (jetDerivative j (actualCurrent m c) * Q) =
      ∑ k : Fin m, k.val.descFactorial j •
        (actualMode m k.val c * PowerSeries.coeff (M-k.val) Q) := by
  simpa only [actualCurrent_coeff] using
    coeff_jet_truncated_mul_eq_sum (actualCurrent m c) Q m M j
      (fun k hk => actualCurrent_coeff_high m k c hk) hm

/-- The quintic-current budget contains every actual multiplier mode.
This also handles small cutoffs using the same Nat subtraction convention. -/
theorem quintic_current_mode_bound (m : ℕ) : m ≤ 2*m-3+1 := by omega

theorem coeff_jet_actualCurrent_mul_quintic (m j : ℕ) (c : Fin 8)
    (Q : PowerSeries (MvPolynomial (Vars m) ℂ)) :
    PowerSeries.coeff (2*m-3-j) (jetDerivative j (actualCurrent m c) * Q) =
      ∑ k : Fin m, k.val.descFactorial j •
        (actualMode m k.val c * PowerSeries.coeff (2*m-3-k.val) Q) :=
  coeff_jet_actualCurrent_mul_eq_sum m (2*m-3) j (quintic_current_mode_bound m) c Q

end
#print axioms coeff_jet_truncated_mul_eq_sum
#print axioms coeff_jet_actualCurrent_mul_eq_sum
#print axioms coeff_jet_actualCurrent_mul_quintic
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
