import VOA.DeligneAudit.SL4TConfigurationInitialRelations
import VOA.DeligneAudit.SL4TRemainderHomogeneity

/-! Highest homogeneous components of remainder minors under a monic scalar deformation. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

variable {σ : Type*}

/-- Integer weight one records the usual total degree of a monomial. -/
theorem monomial_integerWeight (a : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) a = (a.degree : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.degree, Finsupp.sum]

/-- An integer-homogeneous polynomial of negative degree vanishes. -/
theorem integerHomogeneous_eq_zero (p : MvPolynomial σ ℂ) (d : ℤ)
    (hp : p.IsWeightedHomogeneous (fun _ => (1 : ℤ)) d) (hd : d < 0) : p = 0 := by
  apply MvPolynomial.ext
  intro a
  rw [coeff_zero]
  by_contra h
  have ha := hp h
  rw [monomial_integerWeight] at ha
  omega

/-- Integer and natural homogeneous degrees agree in nonnegative degrees. -/
theorem integerHomogeneous_nat (p : MvPolynomial σ ℂ) (n : ℕ)
    (hp : p.IsWeightedHomogeneous (fun _ => (1 : ℤ)) n) : p.IsHomogeneous n := by
  intro a ha
  have he := hp ha
  rw [monomial_integerWeight] at he
  change Finsupp.weight (fun _ : σ => (1 : ℕ)) a = n
  rw [← Finsupp.degree_eq_weight_one]
  exact_mod_cast he

/-- An integer-homogeneous polynomial has bounded total degree, including the zero case. -/
theorem integerHomogeneous_totalDegree_le (p : MvPolynomial σ ℂ) (d : ℤ) (n : ℕ)
    (hp : p.IsWeightedHomogeneous (fun _ => (1 : ℤ)) d) (hd : d ≤ n) :
    p.totalDegree ≤ n := by
  by_cases hneg : d < 0
  · rw [integerHomogeneous_eq_zero p d hp hneg]
    simp
  · have he : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (by omega)
    have hn := integerHomogeneous_nat p d.toNat (he.symm ▸ hp)
    exact hn.totalDegree_le.trans (by omega)

/-- Components above an integer homogeneous degree vanish. -/
theorem integerHomogeneous_component_eq_zero (p : MvPolynomial σ ℂ) (d : ℤ) (n : ℕ)
    (hp : p.IsWeightedHomogeneous (fun _ => (1 : ℤ)) d) (hd : d < n) :
    homogeneousComponent n p = 0 := by
  by_cases hneg : d < 0
  · rw [integerHomogeneous_eq_zero p d hp hneg, map_zero]
  · have he : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (by omega)
    rw [homogeneousComponent_of_mem (integerHomogeneous_nat p d.toNat (he.symm ▸ hp)),
      if_neg (by omega)]

/-- Expand a determinant of finite column sums without dividing by any scalar. -/
theorem determinant_column_sum {j n : ℕ} {A : Type*} [CommRing A]
    (v : Fin j → Fin n → Fin j → A) :
    Matrix.det (fun a b => ∑ l, v b l a) =
      ∑ f : Fin j → Fin n, Matrix.det (fun a b => v b (f b) a) := by
  classical
  rw [← Matrix.det_transpose]
  have he : (fun b a => ∑ l, v b l a) = fun b => ∑ l, v b l := by
    ext b a
    simp
  change Matrix.det (fun b a => ∑ l, v b l a) = _
  rw [he]
  change Matrix.detRowAlternating.toMultilinearMap _ = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact Matrix.det_transpose _

/-- A scalar polynomial deforms each remainder column by its lower powers. -/
def deformedRemainderMinor (xs : List (MvPolynomial σ ℂ)) (N j : ℕ)
    (q : Polynomial ℂ) (rows cols : Fin j → ℕ) : MvPolynomial σ ℂ :=
  Matrix.det fun a b => ∑ l : Fin (N + 1),
    MvPolynomial.C (q.coeff l.val) * alphabetPowerRemainder xs (l.val + cols b) (rows a)

/-- Columnwise expansion of the deformed minor. -/
theorem deformedRemainderMinor_expansion (xs : List (MvPolynomial σ ℂ)) (N j : ℕ)
    (q : Polynomial ℂ) (rows cols : Fin j → ℕ) :
    deformedRemainderMinor xs N j q rows cols =
      ∑ f : Fin j → Fin (N + 1),
        (∏ b, MvPolynomial.C (q.coeff (f b).val)) *
          Matrix.det (fun a b => alphabetPowerRemainder xs
            ((f b).val + cols b) (rows a)) := by
  classical
  rw [deformedRemainderMinor, determinant_column_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact Matrix.det_mul_row (fun b => MvPolynomial.C (q.coeff (f b).val)) _

/-- The degree of each term in the columnwise deformation expansion. -/
theorem deformedRemainderMinor_term_homogeneous (xs : List (MvPolynomial σ ℂ))
    (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous (fun _ => (1 : ℤ)) 1)
    (N j : ℕ) (q : Polynomial ℂ) (rows cols : Fin j → ℕ)
    (f : Fin j → Fin (N + 1)) :
    ((∏ b, MvPolynomial.C (q.coeff (f b).val)) *
      Matrix.det (fun a b =>
        alphabetPowerRemainder xs ((f b).val + cols b) (rows a))).IsWeightedHomogeneous
        (fun _ => (1 : ℤ))
        ((∑ b, (((f b).val + cols b : ℕ) : ℤ)) - ∑ a, (rows a : ℤ)) := by
  have hc : (∏ b, MvPolynomial.C (q.coeff (f b).val) : MvPolynomial σ ℂ).IsWeightedHomogeneous
      (fun _ => (1 : ℤ)) 0 := by
    rw [← map_prod]
    exact isWeightedHomogeneous_C _ _
  simpa only [zero_add] using hc.mul
    (determinant_homogeneous_row_column (fun _ => (1 : ℤ)) _
      (fun a => (rows a : ℤ)) (fun b => (((f b).val + cols b : ℕ) : ℤ))
      (fun a b => alphabetPowerRemainder_homogeneous _ xs hxs _ _))

/-- Replacing the cutoff power by a monic scalar polynomial preserves the highest minor. -/
theorem deformedRemainderMinor_top (xs : List (MvPolynomial σ ℂ))
    (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous (fun _ => (1 : ℤ)) 1)
    (N j : ℕ) (q : Polynomial ℂ) (hq : q.coeff N = 1)
    (rows cols : Fin j → ℕ) (d : ℕ) (hd : remainderMinorDegree N j rows cols = d) :
    (deformedRemainderMinor xs N j q rows cols).totalDegree ≤ d ∧
      homogeneousComponent d (deformedRemainderMinor xs N j q rows cols) =
        remainderRowMinor xs N j rows cols := by
  classical
  let top : Fin j → Fin (N + 1) := fun _ => ⟨N, by omega⟩
  let degree : (Fin j → Fin (N + 1)) → ℤ := fun f =>
    (∑ b, (((f b).val + cols b : ℕ) : ℤ)) - ∑ a, (rows a : ℤ)
  have hle (f : Fin j → Fin (N + 1)) : degree f ≤ d := by
    rw [← hd]
    apply sub_le_sub_right
    exact Finset.sum_le_sum fun b _ => by exact_mod_cast (Nat.add_le_add_right
      (Nat.le_of_lt_succ (f b).isLt) (cols b))
  have hlt (f : Fin j → Fin (N + 1)) (hf : f ≠ top) : degree f < d := by
    rw [← hd]
    apply sub_lt_sub_right
    apply Finset.sum_lt_sum
    · intro b hb
      exact_mod_cast (Nat.add_le_add_right (Nat.le_of_lt_succ (f b).isLt) (cols b))
    · have hex : ∃ b, f b ≠ top b := Function.ne_iff.mp hf
      obtain ⟨b, hb⟩ := hex
      refine ⟨b, Finset.mem_univ b, ?_⟩
      have hv : (f b).val ≠ N := fun h => hb (Fin.ext h)
      have hi := (f b).isLt
      dsimp [top] at *
      exact_mod_cast (show (f b).val + cols b < N + cols b by omega)
  rw [deformedRemainderMinor_expansion]
  constructor
  · apply (MvPolynomial.totalDegree_finsetSum _ _).trans
    apply Finset.sup_le
    intro f hf
    exact integerHomogeneous_totalDegree_le _ (degree f) d
      (deformedRemainderMinor_term_homogeneous xs hxs N j q rows cols f) (hle f)
  · rw [map_sum, Finset.sum_eq_single top]
    · simp only [top, hq, map_one, Finset.prod_const_one, one_mul]
      rw [homogeneousComponent_of_mem (integerHomogeneous_nat _ d
        (hd ▸ remainderRowMinor_homogeneous _ xs hxs N j rows cols)), if_pos rfl]
      rfl
    · intro f hf hft
      exact integerHomogeneous_component_eq_zero _ (degree f) d
        (deformedRemainderMinor_term_homogeneous xs hxs N j q rows cols f) (hlt f hft)
    · simp

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.monomial_integerWeight
#print axioms VOA.DeligneAudit.SL4T.integerHomogeneous_eq_zero
#print axioms VOA.DeligneAudit.SL4T.integerHomogeneous_nat
#print axioms VOA.DeligneAudit.SL4T.integerHomogeneous_totalDegree_le
#print axioms VOA.DeligneAudit.SL4T.integerHomogeneous_component_eq_zero
#print axioms VOA.DeligneAudit.SL4T.determinant_column_sum
#print axioms VOA.DeligneAudit.SL4T.deformedRemainderMinor_expansion
#print axioms VOA.DeligneAudit.SL4T.deformedRemainderMinor_term_homogeneous
#print axioms VOA.DeligneAudit.SL4T.deformedRemainderMinor_top
