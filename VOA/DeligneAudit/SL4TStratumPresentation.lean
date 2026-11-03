import VOA.DeligneAudit.SL4TRemainderMinorTransport

/-! # Universal maps from full-flag stratum quotients -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A D : Type*} [CommRing A] [CommRing D]

theorem alphabetElementary_perm {xs ys : List A} (h : xs.Perm ys) :
    D4Levi.ksEPoly xs = D4Levi.ksEPoly ys :=
  (h.map (fun a => 1 - Polynomial.C a * Polynomial.X)).prod_eq

theorem alphabetCharacteristic_perm {xs ys : List A} (h : xs.Perm ys) :
    alphabetCharacteristic xs = alphabetCharacteristic ys := by
  rw [alphabetCharacteristic_product, alphabetCharacteristic_product]
  exact (h.map (fun a => Polynomial.X - Polynomial.C a)).prod_eq

theorem remainderTopMinor_perm {xs ys : List A} (h : xs.Perm ys)
    (N j : ℕ) (cols : Fin j → ℕ) :
    remainderTopMinor xs N j cols = remainderTopMinor ys N j cols := by
  simp only [remainderTopMinor, alphabetPowerRemainder, alphabetCharacteristic_perm h,
    h.length_eq]

theorem remainderTopIdeal_perm {xs ys : List A} (h : xs.Perm ys) (N j : ℕ) :
    remainderTopIdeal xs N j = remainderTopIdeal ys N j := by
  unfold remainderTopIdeal
  congr 2
  funext cols
  exact remainderTopMinor_perm h N j cols

/-- Evaluating the polynomial subalphabet gives the selected list of roots. -/
theorem fullFlagSubalphabet_aeval [Algebra ℂ A] {B : ℕ} (Y : Finset (Fin B))
    (x : Fin B → A) :
    (fullFlagSubalphabet Y).map (MvPolynomial.aeval x) = Y.toList.map x := by
  simp only [fullFlagSubalphabet, List.map_map, Function.comp_def, MvPolynomial.aeval_X]

variable [Algebra ℂ A]

/-- The stratum presentation maps to any generating alphabet satisfying its relations. -/
def fullFlagStratumLift (B N j : ℕ) (Y : Finset (Fin B)) (x : Fin B → A)
    (he : D4Levi.ksEPoly (List.ofFn x) = 1) (hx : ∀ i, x i ^ N = 0)
    (hm : ∀ cols : Fin j → ℕ, remainderTopMinor (Y.toList.map x) N j cols = 0) :
    FullFlagStratumRing B N j Y →ₐ[ℂ] A :=
  Ideal.Quotient.liftₐ
    (fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j)
    (MvPolynomial.aeval x) (by
    change fullFlagTruncationIdeal B N ⊔
      remainderTopIdeal (fullFlagSubalphabet Y) N j ≤
        RingHom.ker (MvPolynomial.aeval x).toRingHom
    refine sup_le ?_ ?_
    · refine sup_le (fullFlagSymmetricIdeal_le_ker B x he) ?_
      apply Ideal.span_le.mpr
      rintro p ⟨i, rfl⟩
      change MvPolynomial.aeval x (MvPolynomial.X i ^ N : MvPolynomial (Fin B) ℂ) = 0
      simpa only [map_pow, MvPolynomial.aeval_X] using hx i
    · apply Ideal.span_le.mpr
      rintro p ⟨cols, rfl⟩
      change (MvPolynomial.aeval x).toRingHom
        (remainderTopMinor (fullFlagSubalphabet Y) N j cols) = 0
      rw [remainderTopMinor_map]
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        fullFlagSubalphabet_aeval] using hm cols)

theorem fullFlagStratumLift_surjective (B N j : ℕ) (Y : Finset (Fin B)) (x : Fin B → A)
    (he : D4Levi.ksEPoly (List.ofFn x) = 1) (hx : ∀ i, x i ^ N = 0)
    (hm : ∀ cols : Fin j → ℕ, remainderTopMinor (Y.toList.map x) N j cols = 0)
    (hg : Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin B) ℂ →ₐ[ℂ] A)) :
    Function.Surjective (fullFlagStratumLift B N j Y x he hx hm) := by
  intro a
  obtain ⟨p, rfl⟩ := hg a
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

/-- Every algebra with the stratum relations is bounded by the concrete stratum quotient. -/
theorem fullFlagStratum_rank_le_of_relations (B N j : ℕ) (Y : Finset (Fin B))
    (x : Fin B → A) (he : D4Levi.ksEPoly (List.ofFn x) = 1) (hx : ∀ i, x i ^ N = 0)
    (hm : ∀ cols : Fin j → ℕ, remainderTopMinor (Y.toList.map x) N j cols = 0)
    (hg : Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin B) ℂ →ₐ[ℂ] A)) :
    Module.finrank ℂ A ≤ Module.finrank ℂ (FullFlagStratumRing B N j Y) := by
  letI := fullFlagStratum_finite B N j Y
  exact LinearMap.finrank_le_finrank_of_surjective
    (f := (fullFlagStratumLift B N j Y x he hx hm).toLinearMap)
    (fullFlagStratumLift_surjective B N j Y x he hx hm hg)

/-- The polynomial quotient roots of a full-flag stratum. -/
def fullFlagStratumRoot (B N j : ℕ) (Y : Finset (Fin B)) (i : Fin B) :
    FullFlagStratumRing B N j Y := Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem fullFlagStratum_aeval (B N j : ℕ) (Y : Finset (Fin B)) :
    MvPolynomial.aeval (fullFlagStratumRoot B N j Y) =
      Ideal.Quotient.mkₐ ℂ
        (fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [MvPolynomial.aeval_X]
  rfl

theorem fullFlagStratum_elementary (B N j : ℕ) (Y : Finset (Fin B)) :
    D4Levi.ksEPoly (List.ofFn (fullFlagStratumRoot B N j Y)) = 1 := by
  let q := Ideal.Quotient.factorₐ ℂ
    (show fullFlagTruncationIdeal B N ≤
      fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j from
        le_sup_left)
  have h := congrArg (Polynomial.map q.toRingHom) (fullFlag_elementaryPolynomial B N)
  simpa only [alphabetElementary_map, List.map_ofFn, Polynomial.map_one] using h

theorem fullFlagStratumRoot_pow (B N j : ℕ) (Y : Finset (Fin B)) (i : Fin B) :
    fullFlagStratumRoot B N j Y i ^ N = 0 := by
  rw [fullFlagStratumRoot, ← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (show fullFlagTruncationIdeal B N ≤
    fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j from
      le_sup_left)
  exact (show Ideal.span _ ≤ fullFlagTruncationIdeal B N from le_sup_right)
    (Ideal.subset_span ⟨i, rfl⟩)

theorem fullFlagStratum_minor_zero (B N j : ℕ) (Y : Finset (Fin B))
    (cols : Fin j → ℕ) :
    remainderTopMinor (Y.toList.map (fullFlagStratumRoot B N j Y)) N j cols = 0 := by
  let q := Ideal.Quotient.mk
    (fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j)
  have hm : (fullFlagSubalphabet Y).map q =
      Y.toList.map (fullFlagStratumRoot B N j Y) := by
    simp only [fullFlagSubalphabet, List.map_map]
    rfl
  rw [← hm, ← remainderTopMinor_map]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (show remainderTopIdeal (fullFlagSubalphabet Y) N j ≤
    fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j from
      le_sup_right) (remainderTopMinor_mem _ _ _ _)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.alphabetElementary_perm
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_perm
#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_perm
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_perm
#print axioms VOA.DeligneAudit.SL4T.fullFlagSubalphabet_aeval
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumLift_surjective
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_rank_le_of_relations
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_aeval
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_elementary
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumRoot_pow
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_minor_zero
