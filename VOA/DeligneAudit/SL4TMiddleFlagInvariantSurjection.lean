import VOA.DeligneAudit.SL4TMiddleFlagInvariantEvaluation

/-! Surjectivity of the invariant specialization and a canonical colouring of the middle flag. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- With zero outer labels the second ambient elementary sequence is the middle base sequence. -/
theorem middleFlag_secondAmbient_elementary (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (n : ℕ) :
    mixedEvaluation q (mixedV n) = mixedEvaluation q (mixedE 1 n) := by
  have hd := (middleFlag_outer_lengths q hq hA).2
  simp only [mixedV, mixedConv, map_sum, map_mul, map_pow, map_neg, map_one]
  rw [Finset.sum_eq_single n]
  · simp [mixedH]
  · intro j hj hne
    have hj' := Finset.mem_range.mp hj
    rw [mixedComplete_zero_of_empty q hq 2 (by simp [mixedLengths, hd])
      (n - j) (by omega), mul_zero, mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

/-- The four finite middle-flag elementary sequences generate the actual mixed ring. -/
theorem middleFlagElementary_generates (q : MixedParams) (hq : MixedValid q) (hA : q.A = 0)
    (S : Subalgebra ℂ (MixedRing q))
    (hS : ∀ c n, mixedEvaluation q (middleFlagElementary c n) ∈ S)
    (x : MixedRing q) : x ∈ S := by
  obtain ⟨hd1, hd3⟩ := middleFlag_outer_lengths q hq hA
  have hbase (n : ℕ) : mixedEvaluation q (mixedE 1 n) ∈ S := by
    rw [← middleFlag_secondAmbient_elementary q hq hA n, ← mixedG2prime_convolution]
    simp only [mixedConv, map_sum, map_mul]
    apply S.sum_mem
    intro i _
    exact S.mul_mem (hS 2 i) (hS 3 (n - i))
  have hgen (i : Fin 5) (n : ℕ) : mixedEvaluation q (mixedE i (n + 1)) ∈ S := by
    fin_cases i
    · change mixedEvaluation q (mixedE 0 (n + 1)) ∈ S
      rw [mixedElementary_tail q hq 0 (n + 1) (by simp [mixedLengths, hd1])]
      exact S.zero_mem
    · exact hbase (n + 1)
    · change mixedEvaluation q (mixedE 2 (n + 1)) ∈ S
      rw [mixedElementary_tail q hq 2 (n + 1) (by simp [mixedLengths, hd3])]
      exact S.zero_mem
    · exact hS 1 (n + 1)
    · exact hS 2 (n + 1)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (mixedIdeal q) x
  change mixedEvaluation q p ∈ S
  induction p using MvPolynomial.induction_on with
  | C c => exact S.algebraMap_mem c
  | add p r hp hr => rw [map_add]; exact S.add_mem hp hr
  | mul_X p v hp =>
    rcases v with ⟨i, n⟩
    rw [map_mul]
    apply S.mul_mem hp
    simpa only [mixedE, mixedAlphabet, elementary_succ, MvPolynomial.rename_X] using hgen i n

/-- Finite block elementary coordinates surject onto the concrete middle multiplicity ring. -/
theorem middleFlagCoordinateEvaluation_surjective (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) : Function.Surjective (middleFlagCoordinateEvaluation q) := by
  intro x
  apply middleFlagElementary_generates q hq hA (middleFlagCoordinateEvaluation q).range
  intro c n
  exact ⟨colourElementaryCoordinate (middleFlagLength q) c n,
    middleFlagCoordinateEvaluation_elementary q hq c n⟩

/-- The actual Young-invariant polynomial algebra surjects onto the middle multiplicity ring. -/
theorem middleFlagInvariantEvaluation_surjective (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) {B : ℕ} (colour : Fin B → Fin 4)
    (fibres : ∀ c, Fin (middleFlagLength q c) ≃ {i // colour i = c}) :
    Function.Surjective (middleFlagInvariantEvaluation q colour fibres) :=
  (middleFlagCoordinateEvaluation_surjective q hq hA).comp
    (colourElementaryPresentation colour (middleFlagLength q) fibres).symm.surjective

/-- Enumerate the disjoint middle-flag blocks by the actual number of positions. -/
def middleFlagPositionEquiv (q : MixedParams) (hq : MixedValid q) (hA : q.A = 0) :
    (Σ c : Fin 4, Fin (middleFlagLength q c)) ≃ Fin q.B.toNat :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_sigma, Fintype.card_fin]
    exact middleFlagLength_sum q hq hA)

/-- A canonical four-colouring of the positions with the actual flag block lengths. -/
def middleFlagPositionColour (q : MixedParams) (hq : MixedValid q) (hA : q.A = 0)
    (i : Fin q.B.toNat) : Fin 4 :=
  ((middleFlagPositionEquiv q hq hA).symm i).1

/-- Each colour fibre is explicitly equivalent to its prescribed middle-flag block. -/
def middleFlagPositionFibre (q : MixedParams) (hq : MixedValid q) (hA : q.A = 0) (c : Fin 4) :
    Fin (middleFlagLength q c) ≃ {i // middleFlagPositionColour q hq hA i = c} :=
  (Equiv.sigmaSubtype c).symm.trans
    ((middleFlagPositionEquiv q hq hA).subtypeEquiv (fun i => by
      simp [middleFlagPositionColour]))

/-- For every valid middle tuple the canonical contracted tail maps to its actual tail ideal. -/
theorem middleFlagPosition_contractedCoordinateIdeal (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (N : ℕ) (hN : 0 < N) :
    let colour := middleFlagPositionColour q hq hA
    let f := middleFlagInvariantEvaluation q colour (middleFlagPositionFibre q hq hA)
    ((Ideal.span (Set.range fun i : Fin q.B.toNat =>
      (MvPolynomial.X i : MvPolynomial (Fin q.B.toNat) ℂ) ^ N)).comap
        (ColourPolynomialRing colour).val.toRingHom).map f.toRingHom =
          middleFlagAllTailIdeal q N :=
  middleFlagInvariantEvaluation_contractedCoordinateIdeal q
    (middleFlagPositionColour q hq hA) (middleFlagPositionFibre q hq hA) hq hA N hN

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.middleFlag_secondAmbient_elementary
#print axioms VOA.DeligneAudit.SL4T.middleFlagElementary_generates
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoordinateEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.middleFlagInvariantEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.middleFlagPositionEquiv
#print axioms VOA.DeligneAudit.SL4T.middleFlagPositionColour
#print axioms VOA.DeligneAudit.SL4T.middleFlagPositionFibre
#print axioms VOA.DeligneAudit.SL4T.middleFlagPosition_contractedCoordinateIdeal
