import VOA.DeligneAudit.SL4TDoubledSiteRingImage

/-! The full positive-mode tail ideal of the four-colour multiplicity ring. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

/-- All four block power sums in every mode at least the cutoff. -/
def middleFlagAllTailIdeal (q : MixedParams) (N : ℕ) : Ideal (MixedRing q) :=
  ⨆ s : {s : ℕ // N ≤ s}, middleFlagTailIdeal q s.val

/-- Every fixed-mode block ideal is contained in the full tail ideal. -/
theorem middleFlagTailIdeal_le_allTail (q : MixedParams) (N s : ℕ) (hs : N ≤ s) :
    middleFlagTailIdeal q s ≤ middleFlagAllTailIdeal q N :=
  le_iSup_of_le ⟨s, hs⟩ le_rfl

/-- Increasing the cutoff removes relations from the full block-tail ideal. -/
theorem middleFlagAllTailIdeal_antitone (q : MixedParams) :
    Antitone (middleFlagAllTailIdeal q) := by
  intro N M hNM
  apply iSup_le
  intro s
  exact middleFlagTailIdeal_le_allTail q N s.val (hNM.trans s.property)

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V) (a b : ℕ)
variable (h : LocalWeylRel ρ w (weightABC a b a))
variable (N : ℕ) (ht : ∀ i s v, N ≤ s → ρ.op i s v = 0)
variable (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
variable (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂))

include ht

set_option synthInstance.maxHeartbeats 100000 in
/-- Truncated Cartan currents kill every multiple of every block-tail relation. -/
theorem middleFlagAllTailIdeal_le_annihilator (hN : 0 < N) :
    middleFlagAllTailIdeal (mixedLabelBlockParams a b d e₁ e₂) N ≤
      evaluationAnnihilator (mixedSecondLeviEvaluation ρ w a b h d e₁ e₂ hv) := by
  apply iSup_le
  intro s
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩ φ
  apply LinearMap.mem_ker.mp
  apply middleFlagTailIdeal_le_kernel ρ w a b h N ht d e₁ e₂ hv s.val s.property
    (lt_of_lt_of_le hN s.property)
  exact (middleFlagTailIdeal _ s.val).mul_mem_right φ (Ideal.subset_span ⟨i, rfl⟩)

set_option synthInstance.maxHeartbeats 100000 in
/-- The actual second Levi evaluation factors through all modes of the tail ideal. -/
theorem middleFlagAllTailIdeal_le_kernel (hN : 0 < N) :
    (middleFlagAllTailIdeal (mixedLabelBlockParams a b d e₁ e₂) N).restrictScalars ℂ ≤
      LinearMap.ker (mixedSecondLeviEvaluation ρ w a b h d e₁ e₂ hv) := by
  intro x hx
  exact evaluationAnnihilator_le_kernel _
    (middleFlagAllTailIdeal_le_annihilator ρ w a b h N ht d e₁ e₂ hv hN hx)

set_option synthInstance.maxHeartbeats 100000 in
/-- The concrete multiplicity evaluation on the quotient by the entire tail ideal. -/
def middleFlagAllTailEvaluation (hN : 0 < N) :
    (MixedRing (mixedLabelBlockParams a b d e₁ e₂) ⧸
      middleFlagAllTailIdeal (mixedLabelBlockParams a b d e₁ e₂) N) →ₗ[ℂ]
        secondLeviMultiplicity (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w a b a h d) e₁ e₂ :=
  multiplicityQuotientEvaluation (mixedSecondLeviEvaluation ρ w a b h d e₁ e₂ hv) _
    (middleFlagAllTailIdeal_le_kernel ρ w a b h N ht d e₁ e₂ hv hN)

set_option synthInstance.maxHeartbeats 100000 in
/-- Imposing all block-tail modes retains the entire second Levi multiplicity image. -/
theorem middleFlagAllTailEvaluation_surjective (hN : 0 < N) :
    Function.Surjective (middleFlagAllTailEvaluation ρ w a b h N ht d e₁ e₂ hv hN) :=
  multiplicityQuotientEvaluation_surjective _ _ _
    (mixedSecondLeviEvaluation_surjective ρ w a b h d e₁ e₂ hv)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailIdeal
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailIdeal_le_allTail
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailIdeal_antitone
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailIdeal_le_annihilator
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailIdeal_le_kernel
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailEvaluation
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailEvaluation_surjective
