import VOA.DeligneAudit.SL4TQuotientGradedLevel
import VOA.DeligneAudit.SL4TFullFlagStratumRank

/-! Graded determinantal level certificates in the concrete truncated full-flag quotient. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Homogeneous generators with individually specified degrees generate a homogeneous ideal. -/
theorem homogeneous_set_span_component_mem {σ A : Type*} [CommRing A]
    (w : σ → ℤ) (S : Set (MvPolynomial σ A))
    (hS : ∀ p ∈ S, ∃ d, p.IsWeightedHomogeneous w d)
    (p : MvPolynomial σ A) (hp : p ∈ Ideal.span S) (d : ℤ) :
    MvPolynomial.weightedHomogeneousComponent w d p ∈ Ideal.span S := by
  classical
  let degree (a : S) : ℤ := Classical.choose (hS a.val a.property)
  have he : Set.range (fun a : S => a.val) = S := by ext a; simp
  rw [← he] at hp ⊢
  exact homogeneous_span_component_mem w (fun a : S => a.val) degree
    (fun a => Classical.choose_spec (hS a.val a.property)) p hp d

/-- An elementary symmetric function has its ordinary degree for integer-valued weights. -/
theorem elementarySymmetric_standardWeight {σ A : Type*} [Fintype σ] [CommRing A]
    (s : ℕ) :
    (MvPolynomial.esymm σ A s).IsWeightedHomogeneous (fun _ => (1 : ℤ)) s := by
  classical
  unfold MvPolynomial.esymm
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro t ht
  have hc : t.card = s := (Finset.mem_powersetCard.mp ht).2
  have h := MvPolynomial.IsWeightedHomogeneous.prod t
    (fun i => (MvPolynomial.X i : MvPolynomial σ A)) (fun _ => (1 : ℤ))
    (fun i _ => MvPolynomial.isWeightedHomogeneous_X A (fun _ => (1 : ℤ)) i)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, hc] using h

/-- The elementary and root-power relations of the full flag are homogeneous. -/
theorem fullFlagTruncationIdeal_component_mem (B N : ℕ) (d : ℤ)
    (p : MvPolynomial (Fin B) ℂ) (hp : p ∈ fullFlagTruncationIdeal B N) :
    MvPolynomial.weightedHomogeneousComponent (fun _ => (1 : ℤ)) d p ∈
      fullFlagTruncationIdeal B N := by
  unfold fullFlagTruncationIdeal fullFlagSymmetricIdeal at hp ⊢
  rw [← Ideal.span_union] at hp ⊢
  apply homogeneous_set_span_component_mem _ _ ?_ p hp d
  intro g hg
  rcases hg with hg | hg
  · obtain ⟨s, _, rfl⟩ := hg
    exact ⟨s, elementarySymmetric_standardWeight s⟩
  · obtain ⟨i, rfl⟩ := hg
    refine ⟨N, ?_⟩
    simpa only [nsmul_eq_mul, mul_one] using
      (MvPolynomial.isWeightedHomogeneous_X ℂ (fun _ => (1 : ℤ)) i).pow N

/-- Every subalphabet of the full flag has a homogeneous top-ideal correction certificate. -/
theorem fullFlag_remainderTopIdeal_strict_certificate (B N j : ℕ)
    (positions : List (Fin B)) (hj : j ≤ positions.length)
    (a : FullFlagRing B N) (d : ℤ)
    (ha : a ∈ quotientHomogeneousPiece (fun _ => (1 : ℤ))
      (fullFlagTruncationIdeal B N) d)
    (hmem : a ∈ remainderTopIdeal (positions.map (fullFlagRoot B N)) N j) :
    ∃ p : Polynomial (FullFlagRing B N),
      (∀ l, p.coeff l ∈ remainderTopIdeal (positions.map (fullFlagRoot B N)) N j) ∧
      (∀ l, p.coeff l ≠ 0 → ∃ e : ℤ, d < e ∧ p.coeff l ∈
        quotientHomogeneousPiece (fun _ => (1 : ℤ)) (fullFlagTruncationIdeal B N) e) ∧
      Polynomial.C a * Polynomial.X ^ (positions.length - j) + p ∈
        Ideal.span {alphabetCharacteristic (positions.map (fullFlagRoot B N)),
          Polynomial.X ^ N} := by
  let xs := positions.map (fun i => (MvPolynomial.X i : MvPolynomial (Fin B) ℂ))
  have hx : ∀ x ∈ xs, x.IsWeightedHomogeneous (fun _ => (1 : ℤ)) 1 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact MvPolynomial.isWeightedHomogeneous_X ℂ _ i
  have he : xs.map (Ideal.Quotient.mk (fullFlagTruncationIdeal B N)) =
      positions.map (fullFlagRoot B N) := by simp [xs, List.map_map, fullFlagRoot]
  have h := remainderTopIdeal_quotient_strict_certificate (fun _ => (1 : ℤ))
    (fullFlagTruncationIdeal B N) (fullFlagTruncationIdeal_component_mem B N)
    xs hx N j (by simpa [xs] using hj) a d ha (by rwa [he])
  simpa only [he, xs, List.length_map] using h

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.homogeneous_set_span_component_mem
#print axioms VOA.DeligneAudit.SL4T.elementarySymmetric_standardWeight
#print axioms VOA.DeligneAudit.SL4T.fullFlagTruncationIdeal_component_mem
#print axioms VOA.DeligneAudit.SL4T.fullFlag_remainderTopIdeal_strict_certificate
