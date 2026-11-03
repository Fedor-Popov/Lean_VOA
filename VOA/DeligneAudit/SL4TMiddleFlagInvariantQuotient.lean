import VOA.DeligneAudit.SL4TMiddleFlagInvariantSurjection
import VOA.DeligneAudit.SL4TColourFlagTailQuotient

/-! Descent of the actual middle-flag specialization through elementary and all-tail relations. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Summed colour power sums reconstruct the full-alphabet elementary coefficients. -/
theorem colourFullElementary_newton {C : Type*} [Fintype C] [DecidableEq C]
    {B : ℕ} (colour : Fin B → C) (n : ℕ) :
    newtonCoeff (fun s => ∑ c, colourPolynomialPowerSum colour c s) n =
      (-1) ^ n * colourFullElementary colour n := by
  classical
  have hsum (s : ℕ) :
      (ColourPolynomialRing colour).val (∑ c, colourPolynomialPowerSum colour c s) =
        MvPolynomial.psum (Fin B) ℂ s := by
    rw [map_sum]
    change (∑ c, ∑ i ∈ Finset.univ.filter (fun i => colour i = c),
      (MvPolynomial.X i : MvPolynomial (Fin B) ℂ) ^ s) = _
    exact Finset.sum_fiberwise Finset.univ colour _
  apply Subtype.ext
  change (ColourPolynomialRing colour).val (newtonCoeff _ n) =
    (ColourPolynomialRing colour).val ((-1) ^ n * colourFullElementary colour n)
  rw [← newtonCoeff_map]
  simp only [hsum, map_mul, map_pow, map_neg, map_one]
  exact newtonCoeff_psum (Fin B) n

variable (q : MixedParams) (hq : MixedValid q) (hA : q.A = 0)
variable {B : ℕ} (colour : Fin B → Fin 4)
variable (fibres : ∀ c, Fin (middleFlagLength q c) ≃ {i // colour i = c})

include hq hA

/-- All positive full-alphabet elementary relations vanish in the actual middle ring. -/
theorem middleFlagInvariantEvaluation_elementary_zero (n : ℕ) (hn : 0 < n) :
    middleFlagInvariantEvaluation q colour fibres (colourFullElementary colour n) = 0 := by
  let f := middleFlagInvariantEvaluation q colour fibres
  have h := congrArg f (colourFullElementary_newton colour n)
  rw [← newtonCoeff_map, map_mul, map_pow, map_neg, map_one] at h
  have hp (s : ℕ) (hs : 0 < s) : f (∑ c, colourPolynomialPowerSum colour c s) = 0 := by
    rw [map_sum]
    simp only [f, middleFlagInvariantEvaluation_powerSum q colour fibres hq hA _ s hs]
    simp [Fin.sum_univ_succ, middleFlagTailSymbols]
    ring
  have hc := newtonCoeff_congr_positive
    (fun s => f (∑ c, colourPolynomialPowerSum colour c s)) (fun _ => 0) hp n
  have hz : newtonCoeff (fun _ => (0 : MixedRing q)) n = 0 := by
    have he := congrArg (PowerSeries.coeff n)
      (newtonCoefficientSeries_zero (R := MixedRing q))
    simpa [newtonCoefficientSeries, Nat.ne_of_gt hn] using he
  exact (IsUnit.mul_right_eq_zero (isUnit_neg_one.pow n)).mp (h.symm.trans (hc.trans hz))

/-- The elementary coinvariant ideal is killed by the concrete invariant specialization. -/
theorem colourSymmetricIdeal_le_middleFlagKernel :
    colourSymmetricIdeal colour ≤
      RingHom.ker (middleFlagInvariantEvaluation q colour fibres).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p ⟨n, hn, rfl⟩
  exact middleFlagInvariantEvaluation_elementary_zero q hq hA colour fibres n hn

/-- The genuine partial-flag invariant ring maps to the existing mixed multiplicity ring. -/
def middleFlagPartialInvariantEvaluation : ColourFlagRing colour →ₐ[ℂ] MixedRing q :=
  Ideal.Quotient.liftₐ (colourSymmetricIdeal colour)
    (middleFlagInvariantEvaluation q colour fibres)
    (colourSymmetricIdeal_le_middleFlagKernel q hq hA colour fibres)

/-- The elementary quotient still surjects onto the actual mixed multiplicity ring. -/
theorem middleFlagPartialInvariantEvaluation_surjective :
    Function.Surjective (middleFlagPartialInvariantEvaluation q hq hA colour fibres) := by
  intro x
  obtain ⟨p, hp⟩ := middleFlagInvariantEvaluation_surjective q hq hA colour fibres x
  exact ⟨Ideal.Quotient.mk _ p, hp⟩

/-- Partial-flag power-sum tails map exactly onto the actual all-tail ideal. -/
theorem middleFlagPartialInvariantEvaluation_tailIdeal (N : ℕ) (hN : 0 < N) :
    (colourFlagTailIdeal colour N).map
      (middleFlagPartialInvariantEvaluation q hq hA colour fibres).toRingHom =
        middleFlagAllTailIdeal q N := by
  rw [colourFlagTailIdeal, Ideal.map_map]
  exact middleFlagInvariantEvaluation_tailIdeal q colour fibres hq hA N hN

/-- The invariant partial-flag tail quotient specializes to the actual all-tail quotient. -/
def middleFlagTailQuotientEvaluation (N : ℕ) (hN : 0 < N) :
    (ColourFlagRing colour ⧸ colourFlagTailIdeal colour N) →ₐ[ℂ]
      (MixedRing q ⧸ middleFlagAllTailIdeal q N) :=
  Ideal.Quotient.liftₐ (colourFlagTailIdeal colour N)
    ((Ideal.Quotient.mkₐ ℂ (middleFlagAllTailIdeal q N)).comp
      (middleFlagPartialInvariantEvaluation q hq hA colour fibres)) (by
        intro p hp
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [← middleFlagPartialInvariantEvaluation_tailIdeal q hq hA colour fibres N hN]
        exact Ideal.mem_map_of_mem _ hp)

/-- Every actual all-tail coefficient class has an invariant partial-flag representative. -/
theorem middleFlagTailQuotientEvaluation_surjective (N : ℕ) (hN : 0 < N) :
    Function.Surjective (middleFlagTailQuotientEvaluation q hq hA colour fibres N hN) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (middleFlagAllTailIdeal q N) x
  obtain ⟨p, hp⟩ := middleFlagPartialInvariantEvaluation_surjective q hq hA colour fibres a
  refine ⟨Ideal.Quotient.mk _ p, ?_⟩
  change Ideal.Quotient.mk _
    (middleFlagPartialInvariantEvaluation q hq hA colour fibres p) = _
  rw [hp]
  rfl

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.colourFullElementary_newton
#print axioms VOA.DeligneAudit.SL4T.middleFlagInvariantEvaluation_elementary_zero
#print axioms VOA.DeligneAudit.SL4T.colourSymmetricIdeal_le_middleFlagKernel
#print axioms VOA.DeligneAudit.SL4T.middleFlagPartialInvariantEvaluation
#print axioms VOA.DeligneAudit.SL4T.middleFlagPartialInvariantEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.middleFlagPartialInvariantEvaluation_tailIdeal
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailQuotientEvaluation
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailQuotientEvaluation_surjective
