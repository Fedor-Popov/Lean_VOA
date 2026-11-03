import VOA.DeligneAudit.D4CharPieriSubsets

/-! Extracting each elementary degree from the generating e-Pieri identity. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable section

theorem pieriCoeff_map (φ : R →+* S) (q : R) {N : ℕ} (lam : Fin N → ℤ)
    (s : Finset (Fin N)) : φ (pieriCoeff q lam s) = pieriCoeff (φ q) lam s := by
  simp only [pieriCoeff, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

theorem pieriElementary_map (φ : R →+* S) (u : ℕ → Rˣ) (N r : ℕ) :
    φ (pieriElementary u N r) = pieriElementary (fun i => Units.map φ (u i)) N r := by
  simp [pieriElementary, map_sum, map_prod]

theorem pieriRHS_map (φ : R →+* S) (q : R) (u : ℕ → Rˣ) (N : ℕ)
    (lam : Fin N → ℤ) (r : ℕ) :
    φ (pieriRHS q u N lam r) = pieriRHS (φ q) (fun i => Units.map φ (u i)) N lam r := by
  simp only [pieriRHS, map_sum, map_mul, pieriCoeff_map, gtEval_map]

theorem pieri_coeff_subset_sum {N : ℕ} (f : Finset (Fin N) → R) (r : ℕ) :
    (∑ s ∈ (Finset.univ : Finset (Fin N)).powerset,
      Polynomial.C (f s) * Polynomial.X ^ s.card).coeff r =
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard r, f s := by
  classical
  simp [Polynomial.finsetSum_coeff,
    Finset.powersetCard_eq_filter, Finset.sum_filter, eq_comm]

theorem pieri_elementary_polynomial (u : ℕ → Rˣ) (N : ℕ) :
    (∏ i : Fin N, (1 + Polynomial.X * Polynomial.C (u i : R))) =
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powerset,
        Polynomial.C (∏ i ∈ s, (u i : R)) * Polynomial.X ^ s.card := by
  classical
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod]
  exact mul_comm _ _

theorem pieri_elementary_polynomial_coeff (u : ℕ → Rˣ) (N r : ℕ) :
    (∏ i : Fin N, (1 + Polynomial.X * Polynomial.C (u i : R))).coeff r =
      pieriElementary u N r := by
  rw [pieri_elementary_polynomial, pieri_coeff_subset_sum]
  rfl

/-- Full Lemma E for a unit q, with the exact existing `EPieri` statement. -/
theorem ePieri_unit (q : Rˣ) (u : ℕ → Rˣ) : EPieri (q : R) u := by
  classical
  intro N lam hlam r
  have h := gtEval_pieri_subsets (Units.map (Polynomial.C : R →+* Polynomial R).toMonoidHom q)
    (fun i => Units.map (Polynomial.C : R →+* Polynomial R).toMonoidHom (u i))
    Polynomial.X N lam hlam
  simp only [Units.coe_map] at h
  have hp : (∏ i : Fin N, (1 + Polynomial.X * Polynomial.C (u i : R))) *
      Polynomial.C (gtEval (q : R) u N lam) =
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powerset,
        Polynomial.C (pieriCoeff (q : R) lam s *
          gtEval (q : R) u N (pieriWeight lam s)) * Polynomial.X ^ s.card := by
    rw [gtEval_map (Polynomial.C : R →+* Polynomial R) (q : R) u N lam]
    convert h.trans ?_ using 1
    apply Finset.sum_congr rfl
    intro s _
    rw [map_mul, pieriCoeff_map, gtEval_map]
    ring_nf
    rfl
  have hc := congrArg (fun p : Polynomial R => p.coeff r) hp
  simpa only [Polynomial.coeff_mul_C, pieri_elementary_polynomial_coeff,
    pieri_coeff_subset_sum, pieriRHS] using hc

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pieriCoeff_map
#print axioms VOA.DeligneAudit.D4Char.pieriElementary_map
#print axioms VOA.DeligneAudit.D4Char.pieriRHS_map
#print axioms VOA.DeligneAudit.D4Char.pieri_coeff_subset_sum
#print axioms VOA.DeligneAudit.D4Char.pieri_elementary_polynomial_coeff
#print axioms VOA.DeligneAudit.D4Char.ePieri_unit
