import VOA.DeligneAudit.SL4TStableSubmoduleMinors

/-! # Remainder minors and Cramer corrections in the top-row ideal -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A : Type*} [CommRing A]

/-- Polynomial tails are stable under multiplication by the variable. -/
theorem polynomial_tail_span_variable_mem (N : ℕ) (p : Polynomial A)
    (hp : p ∈ Submodule.span A (Set.range fun c => (Polynomial.X : Polynomial A) ^ (N + c))) :
    Polynomial.X * p ∈
      Submodule.span A (Set.range fun c => (Polynomial.X : Polynomial A) ^ (N + c)) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨c, rfl⟩ := hp
      rw [← pow_succ', show N + c + 1 = N + (c + 1) by omega]
      exact Submodule.subset_span ⟨c + 1, rfl⟩
  | zero => simpa only [mul_zero] using Submodule.zero_mem _
  | add p q hp hq ihp ihq => simpa only [mul_add] using Submodule.add_mem _ ihp ihq
  | smul a p hp ih => simpa only [mul_smul_comm] using Submodule.smul_mem _ a ih

/-- Taking linear combinations of tail powers preserves the top-row remainder ideal. -/
theorem polynomial_tail_topIdeal_le (xs : List A) (N j : ℕ) :
    polynomialSubmoduleTopIdeal (alphabetCharacteristic xs) xs.length j
      (Submodule.span A (Set.range fun c => (Polynomial.X : Polynomial A) ^ (N + c))) ≤
        remainderTopIdeal xs N j := by
  classical
  apply Ideal.span_le.mpr
  rintro a ⟨p, rfl⟩
  let L : Polynomial A →ₗ[A] (Fin j → A) :=
    LinearMap.pi fun i => (Polynomial.lcoeff A (xs.length - j + i.val)).comp
      (Polynomial.modByMonicHom (alphabetCharacteristic xs))
  apply determinant_columns_span_mem (remainderTopIdeal xs N j)
    (fun c i => alphabetPowerRemainder xs (N + c) (xs.length - j + i.val))
    (fun cols => remainderTopMinor_mem xs N j cols)
    (fun b => L (p b).val)
  intro b
  have h := Submodule.mem_map_of_mem (f := L) (p b).property
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

/-- Every arbitrary-row remainder minor belongs to the top-row ideal. -/
theorem remainderRowMinor_mem_topIdeal (xs : List A) (N j : ℕ)
    (hj : j ≤ xs.length) (rows cols : Fin j → ℕ) :
    remainderRowMinor xs N j rows cols ∈ remainderTopIdeal xs N j := by
  classical
  by_cases hrows : ∀ a, rows a < xs.length
  · let U := Submodule.span A
      (Set.range fun c => (Polynomial.X : Polynomial A) ^ (N + c))
    let p : Fin j → U := fun b =>
      ⟨Polynomial.X ^ (N + cols b), Submodule.subset_span ⟨cols b, rfl⟩⟩
    apply polynomial_tail_topIdeal_le xs N j
    nontriviality A
    exact stableSubmodule_coefficient_minor_mem (alphabetCharacteristic xs) xs.length j
      (alphabetCharacteristic_monic xs) (alphabetCharacteristic_natDegree xs) hj U
      (fun p hp => polynomial_tail_span_variable_mem N p hp) p
      (fun a => ⟨rows a, hrows a⟩)
  · obtain ⟨a, ha⟩ := not_forall.mp hrows
    have hz : remainderRowMinor xs N j rows cols = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero a
      intro b
      nontriviality A
      apply Polynomial.coeff_eq_zero_of_degree_lt
      have hd := Polynomial.degree_modByMonic_lt (Polynomial.X ^ (N + cols b))
        (alphabetCharacteristic_monic xs)
      rw [Polynomial.degree_eq_natDegree (alphabetCharacteristic_monic xs).ne_zero,
        alphabetCharacteristic_natDegree] at hd
      exact lt_of_lt_of_le hd (by exact_mod_cast (show xs.length ≤ rows a by omega))
    rw [hz]
    exact Ideal.zero_mem _

/-- All-row and top-row remainder determinantal ideals agree over every commutative ring. -/
theorem remainderAllIdeal_eq_topIdeal (xs : List A) (N j : ℕ) (hj : j ≤ xs.length) :
    remainderAllIdeal xs N j = remainderTopIdeal xs N j := by
  apply le_antisymm _ (remainderTopIdeal_le_allIdeal xs N j)
  apply Ideal.span_le.mpr
  rintro a ⟨rows, cols, rfl⟩
  exact remainderRowMinor_mem_topIdeal xs N j hj rows cols

/-- Cramer corrections have coefficients in the original top-row ideal. -/
theorem remainderTopMinor_topIdeal_certificate (xs : List A) (N j : ℕ)
    (cols : Fin j → ℕ) (hj : 0 < j) (hjr : j ≤ xs.length) :
    ∃ p : Polynomial A,
      p.degree < (xs.length - j : WithBot ℕ) ∧
      (∀ l, p.coeff l ∈ remainderTopIdeal xs N j) ∧
      Polynomial.C (remainderTopMinor xs N j cols) * Polynomial.X ^ (xs.length - j) + p ∈
        Ideal.span {alphabetCharacteristic xs, Polynomial.X ^ N} := by
  simpa only [remainderAllIdeal_eq_topIdeal xs N j hjr] using
    remainderTopMinor_cramer_certificate xs N j cols hj hjr

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.polynomial_tail_span_variable_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_tail_topIdeal_le
#print axioms VOA.DeligneAudit.SL4T.remainderRowMinor_mem_topIdeal
#print axioms VOA.DeligneAudit.SL4T.remainderAllIdeal_eq_topIdeal
#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_topIdeal_certificate
