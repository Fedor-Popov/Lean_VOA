import VOA.DeligneAudit.SL4TTopIdealGradedBoundary

/-! # Graded remainder certificates in homogeneous polynomial quotients -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {σ A : Type*} [CommRing A]

/-- A homogeneous degree piece of a polynomial quotient, expressed by homogeneous lifts. -/
def quotientHomogeneousPiece (w : σ → ℤ) (J : Ideal (MvPolynomial σ A)) (d : ℤ) :
    Submodule A (MvPolynomial σ A ⧸ J) :=
  (MvPolynomial.weightedHomogeneousSubmodule A w d).map (Ideal.Quotient.mkₐ A J).toLinearMap

/-- A homogeneous element in the image of a homogeneous ideal has a homogeneous lift
belonging to that ideal. -/
theorem homogeneous_ideal_quotient_lift {ι : Type*} (w : σ → ℤ)
    (g : ι → MvPolynomial σ A) (degree : ι → ℤ)
    (hg : ∀ i, (g i).IsWeightedHomogeneous w (degree i))
    (J : Ideal (MvPolynomial σ A))
    (hJ : ∀ d p, p ∈ J → MvPolynomial.weightedHomogeneousComponent w d p ∈ J)
    (a : MvPolynomial σ A ⧸ J) (d : ℤ) (ha : a ∈ quotientHomogeneousPiece w J d)
    (hmem : a ∈ (Ideal.span (Set.range g)).map (Ideal.Quotient.mk J)) :
    ∃ p : MvPolynomial σ A, p.IsWeightedHomogeneous w d ∧
      p ∈ Ideal.span (Set.range g) ∧ Ideal.Quotient.mk J p = a := by
  obtain ⟨p, hp, hpa⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective).mp hmem
  obtain ⟨q, hq, hqa⟩ := ha
  change q.IsWeightedHomogeneous w d at hq
  change Ideal.Quotient.mk J q = a at hqa
  refine ⟨MvPolynomial.weightedHomogeneousComponent w d p,
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _,
    homogeneous_span_component_mem w g degree hg p hp d, ?_⟩
  have hpq : p - q ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hpa, hqa, sub_self]
  have hc := hJ d (p - q) hpq
  rw [map_sub, hq.weightedHomogeneousComponent_same] at hc
  have he := Ideal.Quotient.eq_zero_iff_mem.mpr hc
  rw [map_sub, hqa, sub_eq_zero] at he
  exact he

/-- The top-row graded certificate survives every homogeneous polynomial quotient. -/
theorem remainderTopIdeal_quotient_graded_certificate (w : σ → ℤ)
    (J : Ideal (MvPolynomial σ A))
    (hJ : ∀ d p, p ∈ J → MvPolynomial.weightedHomogeneousComponent w d p ∈ J)
    (xs : List (MvPolynomial σ A)) (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous w 1)
    (N j : ℕ) (hjr : j ≤ xs.length)
    (a : MvPolynomial σ A ⧸ J) (d : ℤ) (ha : a ∈ quotientHomogeneousPiece w J d)
    (hmem : a ∈ remainderTopIdeal (xs.map (Ideal.Quotient.mk J)) N j) :
    ∃ p : Polynomial (MvPolynomial σ A ⧸ J),
      p.degree < (xs.length - j : WithBot ℕ) ∧
      (∀ l, p.coeff l ∈ remainderTopIdeal (xs.map (Ideal.Quotient.mk J)) N j) ∧
      (∀ l : ℕ, p.coeff l ∈ quotientHomogeneousPiece w J (d + (xs.length - j : ℕ) - l)) ∧
      Polynomial.C a * Polynomial.X ^ (xs.length - j) + p ∈
        Ideal.span {alphabetCharacteristic (xs.map (Ideal.Quotient.mk J)),
          Polynomial.X ^ N} := by
  let f := Ideal.Quotient.mk J
  have hg (cols : Fin j → ℕ) := remainderRowMinor_homogeneous w xs hxs N j
    (fun b => xs.length - j + b.val) cols
  rw [← remainderTopIdeal_map f xs N j] at hmem
  obtain ⟨b, hbdegree, hbmem, hba⟩ := homogeneous_ideal_quotient_lift w
    (remainderTopMinor xs N j)
    (fun cols => remainderMinorDegree N j (fun b => xs.length - j + b.val) cols)
    hg J hJ a d ha hmem
  obtain ⟨p, hpdegree, hpmem, hphom, hprel⟩ :=
    remainderTopIdeal_all_sizes_graded_certificate w xs hxs N j hjr b d hbdegree hbmem
  refine ⟨p.map f, lt_of_le_of_lt Polynomial.degree_map_le hpdegree, ?_, ?_, ?_⟩
  · intro l
    rw [Polynomial.coeff_map, ← remainderTopIdeal_map f xs N j]
    exact Ideal.mem_map_of_mem f (hpmem l)
  · intro l
    rw [Polynomial.coeff_map]
    exact Submodule.mem_map_of_mem (hphom l)
  · have hmap := Ideal.mem_map_of_mem (Polynomial.mapRingHom f) hprel
    have hle : (Ideal.span {alphabetCharacteristic xs, Polynomial.X ^ N}).map
        (Polynomial.mapRingHom f) ≤
        Ideal.span {alphabetCharacteristic (xs.map f), Polynomial.X ^ N} := by
      rw [Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro x ⟨y, hy, rfl⟩
      rcases hy with rfl | hy
      · change (alphabetCharacteristic xs).map f ∈ _
        rw [alphabetCharacteristic_map]
        exact Ideal.subset_span (Set.mem_insert _ _)
      · rcases hy with rfl
        change (Polynomial.X ^ N).map f ∈ _
        rw [Polynomial.map_pow, Polynomial.map_X]
        exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have h := hle hmap
    change (Polynomial.C b * Polynomial.X ^ (xs.length - j) + p).map f ∈ _ at h
    simpa only [Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hba, f] using h

/-- All nonzero quotient correction coefficients lie in strictly larger homogeneous pieces. -/
theorem remainderTopIdeal_quotient_strict_certificate (w : σ → ℤ)
    (J : Ideal (MvPolynomial σ A))
    (hJ : ∀ d p, p ∈ J → MvPolynomial.weightedHomogeneousComponent w d p ∈ J)
    (xs : List (MvPolynomial σ A)) (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous w 1)
    (N j : ℕ) (hjr : j ≤ xs.length)
    (a : MvPolynomial σ A ⧸ J) (d : ℤ) (ha : a ∈ quotientHomogeneousPiece w J d)
    (hmem : a ∈ remainderTopIdeal (xs.map (Ideal.Quotient.mk J)) N j) :
    ∃ p : Polynomial (MvPolynomial σ A ⧸ J),
      (∀ l, p.coeff l ∈ remainderTopIdeal (xs.map (Ideal.Quotient.mk J)) N j) ∧
      (∀ l, p.coeff l ≠ 0 → ∃ e : ℤ, d < e ∧ p.coeff l ∈ quotientHomogeneousPiece w J e) ∧
      Polynomial.C a * Polynomial.X ^ (xs.length - j) + p ∈
        Ideal.span {alphabetCharacteristic (xs.map (Ideal.Quotient.mk J)),
          Polynomial.X ^ N} := by
  obtain ⟨p, hpdegree, hpmem, hphom, hprel⟩ :=
    remainderTopIdeal_quotient_graded_certificate w J hJ xs hxs N j hjr a d ha hmem
  refine ⟨p, hpmem, ?_, hprel⟩
  intro l hl
  refine ⟨d + (xs.length - j : ℕ) - l, ?_, hphom l⟩
  have hlt : l < xs.length - j := by
    exact_mod_cast lt_of_le_of_lt (Polynomial.le_degree_of_ne_zero hl) hpdegree
  omega

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.homogeneous_ideal_quotient_lift
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_quotient_graded_certificate
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_quotient_strict_certificate
