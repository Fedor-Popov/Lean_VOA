import VOA.DeligneAudit.D4FusionContactAllMCountResearchCartanQuadratic

/-! # Exact Cartan isolation for mixed-color quadratic coefficients -/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

variable {m : ℕ} (b : BoundaryPair m)

/-- Only two ordered pairs survive the positive Cartan shift. -/
theorem shifted_mixed_sum (a c : Fin 9) :
    (∑ x ∈ Finset.antidiagonal (b.lower.val+b.top.val),
      modeX m a (b.top.val-b.lower.val-1+x.1) * modeX m c x.2) =
      modeX m a (b.top.val-1) * modeX m c b.top.val +
        modeX m a b.top.val * modeX m c (b.top.val-1) := by
  let S := Finset.antidiagonal (b.lower.val+b.top.val)
  let f := fun x : ℕ × ℕ =>
    modeX m a (b.top.val-b.lower.val-1+x.1) * modeX m c x.2
  have hlt := b.lt
  have hlast := b.last
  have hq : 0 < b.top.val := by omega
  have h0 : (b.lower.val,b.top.val) ∈ S := by simp [S]
  have h1 : (b.lower.val+1,b.top.val-1) ∈ S.erase (b.lower.val,b.top.val) := by
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      have := congrArg Prod.fst he
      omega
    · simp only [S,Finset.mem_antidiagonal]
      omega
  have hs0 := Finset.add_sum_erase S f h0
  have hs1 := Finset.add_sum_erase (S.erase (b.lower.val,b.top.val)) f h1
  have hzero : ∑ x ∈ (S.erase (b.lower.val,b.top.val)).erase
      (b.lower.val+1,b.top.val-1), f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_erase,S,Finset.mem_antidiagonal] at hx
    have hn0 : ¬ (x.1=b.lower.val ∧ x.2=b.top.val) := by
      intro he
      exact hx.2.1 (Prod.ext he.1 he.2)
    have hn1 : ¬ (x.1=b.lower.val+1 ∧ x.2=b.top.val-1) := by
      intro he
      exact hx.1 (Prod.ext he.1 he.2)
    by_cases hi : b.top.val-b.lower.val-1+x.1 < m
    · have hj : ¬ x.2 < m := by omega
      simp only [f,modeX,dif_neg hj,mul_zero]
    · simp only [f,modeX,dif_neg hi,zero_mul]
  change (∑ x ∈ S, f x) = _
  rw [← hs0,← hs1,hzero,add_zero]
  have ha : b.top.val-b.lower.val-1+b.lower.val = b.top.val-1 := by omega
  have hb : b.top.val-b.lower.val-1+(b.lower.val+1) = b.top.val := by omega
  simp only [f,ha,hb]

/-- Full mixed coefficient identity, with both Leibniz weights and all
ordered coefficient multiplicities retained. -/
theorem h0Deriv_mixed_coefficient (a c : Fin 9) :
    g0Deriv m 0 (refinementMode b).val
      (PowerSeries.coeff (b.lower.val+b.top.val)
        (Polynomial.AllM.current m a * Polynomial.AllM.current m c)) =
      ((h0Weight a : ℂ)+(h0Weight c : ℂ)) •
        (modeX m a (b.top.val-1) * modeX m c b.top.val +
         modeX m a b.top.val * modeX m c (b.top.val-1)) := by
  let k := (refinementMode b).val
  let S := Finset.antidiagonal (b.lower.val+b.top.val)
  let Q := modeX m a (b.top.val-1) * modeX m c b.top.val +
    modeX m a b.top.val * modeX m c (b.top.val-1)
  have hfirst : (∑ x ∈ S, modeX m a x.1 * modeX m c (k+x.2)) = Q := by
    have hs : (∑ x ∈ S, modeX m a x.1 * modeX m c (k+x.2)) =
        ∑ x ∈ S, modeX m c (k+x.1) * modeX m a x.2 := by
      have hh := Finset.Nat.sum_antidiagonal_swap
        (n := b.lower.val+b.top.val)
        (f := fun x : ℕ × ℕ => modeX m a x.1 * modeX m c (k+x.2))
      simpa only [S,Prod.swap,mul_comm] using hh.symm
    rw [hs]
    change (∑ x ∈ Finset.antidiagonal (b.lower.val+b.top.val),
      modeX m c (b.top.val-b.lower.val-1+x.1) * modeX m a x.2) = Q
    rw [shifted_mixed_sum]
    dsimp [Q]
    ring
  have hsecond : (∑ x ∈ S, modeX m c x.2 * modeX m a (k+x.1)) = Q := by
    calc
      _ = ∑ x ∈ S, modeX m a (k+x.1) * modeX m c x.2 := by
        apply Finset.sum_congr rfl
        intro x _
        exact mul_comm _ _
      _ = Q := shifted_mixed_sum b a c
  simp only [PowerSeries.coeff_mul,Polynomial.AllM.current,PowerSeries.coeff_mk,
    map_sum,Derivation.leibniz,h0Deriv_modeX,smul_eq_mul,mul_smul_comm,
    Finset.sum_add_distrib,← Finset.smul_sum]
  change (h0Weight c : ℂ) • (∑ x ∈ S, modeX m a x.1 * modeX m c (k+x.2)) +
    (h0Weight a : ℂ) • (∑ x ∈ S, modeX m c x.2 * modeX m a (k+x.1)) = _
  rw [hfirst,hsecond,← add_smul]
  congr 1
  exact add_comm _ _

end

#print axioms shifted_mixed_sum
#print axioms h0Deriv_mixed_coefficient

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
