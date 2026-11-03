import VOA.DeligneAudit.SL4TTruncatedMultiplicity

/-! Ideal factorization of the mixed-ring multiplicity map at an independent current cutoff. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

/-- The ideal of fixed-mode power sums in all five mixed alphabets. -/
def mixedAlphabetTailIdeal (q : MixedParams) (N : ℕ) : Ideal (MixedRing q) :=
  Ideal.span (Set.range (fun i : Fin 5 =>
    mixedAlphabetPowerSum (mixedEvaluation q) i (mixedLengths q i) N))

/-- The four positive-mode flag-block symbols at zero outer highest-weight labels. -/
def middleFlagTailSymbols (q : MixedParams) (N : ℕ) : Fin 4 → MixedRing q :=
  let x := mixedAlphabetPowerSum (mixedEvaluation q) 1 (mixedLengths q 1) N
  let g₁ := mixedAlphabetPowerSum (mixedEvaluation q) 3 (mixedLengths q 3) N
  let g₂ := mixedAlphabetPowerSum (mixedEvaluation q) 4 (mixedLengths q 4) N
  ![-x - g₁, g₁, g₂, x - g₂]

/-- The four flag-block symbols have zero total positive power sum. -/
theorem middleFlagTailSymbols_sum (q : MixedParams) (N : ℕ) :
    middleFlagTailSymbols q N 0 + middleFlagTailSymbols q N 1 +
      middleFlagTailSymbols q N 2 + middleFlagTailSymbols q N 3 = 0 := by
  dsimp [middleFlagTailSymbols]
  ring

/-- The four block-tail relations are consequences of the five alphabet-tail relations. -/
theorem middleFlagTailSymbols_mem (q : MixedParams) (N : ℕ) (i : Fin 4) :
    middleFlagTailSymbols q N i ∈ mixedAlphabetTailIdeal q N := by
  have hg (j : Fin 5) : mixedAlphabetPowerSum (mixedEvaluation q) j (mixedLengths q j) N ∈
      mixedAlphabetTailIdeal q N := Ideal.subset_span ⟨j, rfl⟩
  fin_cases i
  · exact (mixedAlphabetTailIdeal q N).sub_mem
      ((mixedAlphabetTailIdeal q N).neg_mem (hg 1)) (hg 3)
  · exact hg 3
  · exact hg 4
  · exact (mixedAlphabetTailIdeal q N).sub_mem (hg 1) (hg 4)

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V) (a b : ℕ)
variable (h : LocalWeylRel ρ w (weightABC a b a))
variable (M : ℕ) (ht : ∀ i s v, M ≤ s → ρ.op i s v = 0)
variable (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
variable (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂))

include ht

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity source includes nested quotient and tensor-product instances.
/-- The full alphabet-tail ideal lies in the kernel of the actual second Levi map. -/
theorem mixedAlphabetTailIdeal_le_kernel (N : ℕ) (hN : M ≤ N) (hpos : 0 < N) :
    (mixedAlphabetTailIdeal (mixedLabelBlockParams a b d e₁ e₂) N).restrictScalars ℂ ≤
      LinearMap.ker (mixedSecondLeviEvaluation ρ w a b h d e₁ e₂ hv) := by
  let π := mixedSecondLeviEvaluation ρ w a b h d e₁ e₂ hv
  have hle : mixedAlphabetTailIdeal (mixedLabelBlockParams a b d e₁ e₂) N ≤
      evaluationAnnihilator π := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩ φ
    exact mixedSecondLeviEvaluation_alphabetPowerSum_tail
      ρ w a b M ht h d e₁ e₂ hv i N hN hpos φ
  exact fun x hx => evaluationAnnihilator_le_kernel π (hle hx)

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity source includes nested quotient and tensor-product instances.
/-- In particular, all four positive flag-block tails lie in the multiplicity kernel. -/
theorem middleFlagTailIdeal_le_kernel (N : ℕ) (hN : M ≤ N) (hpos : 0 < N) :
    (Ideal.span (Set.range (middleFlagTailSymbols
      (mixedLabelBlockParams a b d e₁ e₂) N))).restrictScalars ℂ ≤
        LinearMap.ker (mixedSecondLeviEvaluation ρ w a b h d e₁ e₂ hv) := by
  have hle : Ideal.span (Set.range (middleFlagTailSymbols
      (mixedLabelBlockParams a b d e₁ e₂) N)) ≤
      mixedAlphabetTailIdeal (mixedLabelBlockParams a b d e₁ e₂) N := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact middleFlagTailSymbols_mem _ N i
  exact fun x hx => mixedAlphabetTailIdeal_le_kernel
    ρ w a b h M ht d e₁ e₂ hv N hN hpos (hle hx)

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity source includes nested quotient and tensor-product instances.
/-- The actual second multiplicity evaluation after imposing the four block-tail relations. -/
def middleFlagQuotientEvaluation (hM : 0 < M) :
    (MixedRing (mixedLabelBlockParams a b d e₁ e₂) ⧸
      Ideal.span (Set.range (middleFlagTailSymbols (mixedLabelBlockParams a b d e₁ e₂) M)))
      →ₗ[ℂ] secondLeviMultiplicity (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b a h d) e₁ e₂ :=
  multiplicityQuotientEvaluation (mixedSecondLeviEvaluation ρ w a b h d e₁ e₂ hv) _
    (middleFlagTailIdeal_le_kernel ρ w a b h M ht d e₁ e₂ hv M le_rfl hM)

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity source includes nested quotient and tensor-product instances.
/-- Passing to the flag-tail quotient preserves surjectivity onto the actual multiplicity. -/
theorem middleFlagQuotientEvaluation_surjective (hM : 0 < M) :
    Function.Surjective (middleFlagQuotientEvaluation ρ w a b h M ht d e₁ e₂ hv hM) :=
  multiplicityQuotientEvaluation_surjective _ _ _
    (mixedSecondLeviEvaluation_surjective ρ w a b h d e₁ e₂ hv)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.middleFlagTailSymbols_sum
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailSymbols_mem
#print axioms VOA.DeligneAudit.SL4T.mixedAlphabetTailIdeal_le_kernel
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailIdeal_le_kernel
#print axioms VOA.DeligneAudit.SL4T.middleFlagQuotientEvaluation_surjective
