import VOA.DeligneAudit.SL4TGrassmannianBoundary
import VOA.DeligneAudit.SL4TFiniteExtension

/-!
# Finiteness and the binomial upper bound

These results do not assert that the spanning bound is an equality. Independence of a
rectangle basis, and consequently the exact annihilator statements, remain separate tasks.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

theorem grass_convolution (d T n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.range (n + 1),
      (-1 : GrassRing d T) ^ i * eClass d T i * hClass d T (n - i) = 0 := by
  have h := congrArg (Ideal.Quotient.mk (grassIdeal d T)) (complete_relation n hn)
  simpa only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero, eClass, hClass]
    using h

theorem eClass_width_zero (d j : ℕ) (hj : 0 < j) : eClass d 0 j = 0 := by
  have h := grass_convolution d 0 j hj
  rw [Finset.sum_eq_single j] at h
  · simp only [Nat.sub_self, hClass, complete_zero, map_one, mul_one] at h
    exact (IsUnit.mul_right_eq_zero (isUnit_neg_one.pow j)).mp h
  · intro i hi hne
    rw [hClass_eq_zero d 0 (j - i) (by have := Finset.mem_range.mp hi; omega), mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

/-- Vanishing of the positive elementary generators makes the ring a scalar image. -/
theorem grass_finite_of_e_zero (d T : ℕ) (he : ∀ i, eClass d T (i + 1) = 0) :
    FiniteDimensional ℂ (GrassRing d T) ∧ Module.finrank ℂ (GrassRing d T) ≤ 1 := by
  let f := Algebra.linearMap ℂ (GrassRing d T)
  have hf : Function.Surjective f := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro p
    change ∃ c, algebraMap ℂ (GrassRing d T) c = Ideal.Quotient.mk _ p
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨c, rfl⟩
    | add p q hp hq =>
        obtain ⟨a, ha⟩ := hp
        obtain ⟨b, hb⟩ := hq
        exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
    | mul_X p i _ =>
        refine ⟨0, ?_⟩
        rw [map_zero, map_mul]
        change 0 = Ideal.Quotient.mk _ p * eClass d T (i + 1)
        rw [he, mul_zero]
  haveI : FiniteDimensional ℂ (GrassRing d T) := Module.Finite.of_surjective f hf
  exact ⟨inferInstance, by simpa using LinearMap.finrank_le_finrank_of_surjective hf⟩

/-- The Grassmannian ring is finite-dimensional, with the expected binomial upper bound.
This theorem makes no independence or exact-dimension claim. -/
theorem grass_finite_rank_le (d T : ℕ) :
    FiniteDimensional ℂ (GrassRing d T) ∧
      Module.finrank ℂ (GrassRing d T) ≤ (d + T).choose d := by
  induction d generalizing T with
  | zero =>
      simpa using grass_finite_of_e_zero 0 T (fun i => eClass_eq_zero 0 T (i + 1) (by omega))
  | succ d ihd =>
      induction T with
      | zero =>
          simpa using grass_finite_of_e_zero (d + 1) 0
            (fun i => eClass_width_zero (d + 1) (i + 1) (by omega))
      | succ T ihT =>
          obtain ⟨fdE, bdE⟩ := ihd (T + 1)
          obtain ⟨fdH, bdH⟩ := ihT
          let e := grassQuotE d (T + 1)
          let h := grassQuotH (d + 1) T
          letI := fdE
          letI := fdH
          have fqe : FiniteDimensional ℂ
              (GrassRing (d + 1) (T + 1) ⧸ Ideal.span {eClass (d + 1) (T + 1) (d + 1)}) :=
            FiniteDimensional.of_injective e.toLinearMap e.injective
          have fqh : FiniteDimensional ℂ
              (GrassRing (d + 1) (T + 1) ⧸ Ideal.span {hClass (d + 1) (T + 1) (T + 1)}) :=
            FiniteDimensional.of_injective h.toLinearMap h.injective
          obtain ⟨fd, bd⟩ := finite_of_annihilating_pair
            (eClass (d + 1) (T + 1) (d + 1)) (hClass (d + 1) (T + 1) (T + 1))
            (grass_boundary_product (d + 1) (T + 1) (by omega)) fqe fqh
          refine ⟨fd, bd.trans ?_⟩
          rw [e.toLinearEquiv.finrank_eq, h.toLinearEquiv.finrank_eq]
          have hn : d + 1 + T = d + (T + 1) := by omega
          rw [hn] at bdH
          calc
            Module.finrank ℂ (GrassRing d (T + 1)) +
                Module.finrank ℂ (GrassRing (d + 1) T) ≤
                (d + (T + 1)).choose d + (d + (T + 1)).choose (d + 1) :=
              Nat.add_le_add bdE bdH
            _ = ((d + 1) + (T + 1)).choose (d + 1) := by
              rw [show d + 1 + (T + 1) = (d + (T + 1)) + 1 by omega,
                Nat.choose_succ_succ]

/-- The all-`M` finiteness and binomial upper bound in the original coordinates. -/
theorem H_finite_rank_le (d M : ℕ) (hdM : d ≤ M) :
    FiniteDimensional ℂ (H d M) ∧ Module.finrank ℂ (H d M) ≤ M.choose d := by
  simpa only [H, Nat.add_sub_of_le hdM] using grass_finite_rank_le d (M - d)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.grass_convolution
#print axioms VOA.DeligneAudit.SL4T.eClass_width_zero
#print axioms VOA.DeligneAudit.SL4T.grass_finite_of_e_zero
#print axioms VOA.DeligneAudit.SL4T.grass_finite_rank_le
#print axioms VOA.DeligneAudit.SL4T.H_finite_rank_le
