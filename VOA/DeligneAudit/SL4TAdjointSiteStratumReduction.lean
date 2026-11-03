import VOA.DeligneAudit.SL4TMarkedFlagEquivariantAudit
import VOA.DeligneAudit.SL4TAdjointSiteFlatTopRelation
import VOA.DeligneAudit.SL4TAdjointSiteGrading

/-!
# The one-adjoint-site stratum count reduces to the low strata

A site word with `k` doubled sites has at most `k + 1` T-states, and at most `k` unless both roots
of the adjoint site are present, i.e. unless the block has `(d₁, d₃) = (1, 0)`
(`adjointSiteWordTCount_le`, `adjointSiteWordTCount_le_of_block`). So `w_j = 0` above that bound
(`adjointSiteWordCount_eq_zero_of_lt`), and the stratum inequality `dim A/G_j ≤ w₀ - w_j` there
follows from `dim A ≤ w₀`, because `A/G_j` is a quotient of the finite-dimensional ring `A`. The
joint-ideal equation is `adjointSiteJointTopIdeal_eq_sup`. Hence `OneAdjointStratumCount B k`
follows from `dim A ≤ w₀` and the strata `1 ≤ j ≤ k + [(d₁, d₃) = (1, 0)]`
(`oneAdjointStratumCount_of_low_strata`); for `k = 1` these are `j = 1` on every block and `j = 2`
on the doubly marked blocks. With `adjointSiteLawB_of_stratumCount` this gives Law B at one
adjoint site from the same data (`adjointSiteLawB_of_low_strata`).

Above the number of selected roots the joint ideal vanishes: a top-row `j`-minor ideal modulo a
monic polynomial of degree `r < j` is zero (`polynomialSubmoduleTopIdeal_eq_bot_of_lt`,
`adjointSiteJointTopIdeal_eq_bot_of_lt`).
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- There are no nonzero top-row `j`-minors modulo a monic polynomial of degree `r < j`. -/
theorem polynomialSubmoduleTopIdeal_eq_bot_of_lt {A : Type*} [CommRing A] (P : A[X]) (r j : ℕ)
    (hP : P.Monic) (hr : P.natDegree = r) (hj : r < j) (U : Submodule A A[X]) :
    polynomialSubmoduleTopIdeal P r j U = ⊥ := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [eq_bot_iff]
    intro x _
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  rw [polynomialSubmoduleTopIdeal, Ideal.span_eq_bot]
  rintro a ⟨p, rfl⟩
  apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last j')
  intro b
  have hlt := degree_modByMonic_lt (p b).val hP
  rw [degree_eq_natDegree hP.ne_zero, hr] at hlt
  change (((p b).val %ₘ P).coeff (r - (j' + 1) + (Fin.last j').val)) = 0
  rw [Fin.val_last, show r - (j' + 1) + j' = j' by omega]
  exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hlt (by exact_mod_cast (by omega : r ≤ j')))

/-- The joint ideal of a valid block vanishes above its number of selected roots. -/
theorem adjointSiteJointTopIdeal_eq_bot_of_lt (q : MixedParams) (hq : MixedValid q) (h j : ℕ)
    (hj : (mixedWeight q).toNat < j) : adjointSiteJointTopIdeal q h j = ⊥ := by
  rcases subsingleton_or_nontrivial (AdjointSiteCoefficientRing q h) with hA | hA
  · rw [eq_bot_iff]
    intro x _
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  obtain ⟨hmonic, hdeg⟩ := adjointSiteCharacteristic_monic q hq h
  exact polynomialSubmoduleTopIdeal_eq_bot_of_lt _ _ _ hmonic hdeg hj _

/-! ### T-states of site words -/

/-- A word with `k` doubled sites has at most `k + 1` T-states. -/
theorem adjointSiteWordTCount_le {B k : ℕ} (u : AdjointSiteWord B k) :
    adjointSiteWordTCount u ≤ k + 1 := by
  unfold adjointSiteWordTCount
  have h1 : (if adjointSiteStateYCount u.1 = 2 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have h2 : ∑ i : Fin k, (if doubledSiteStateYCount (u.2.1 i) = 2 then 1 else 0) ≤ k := by
    calc ∑ i : Fin k, (if doubledSiteStateYCount (u.2.1 i) = 2 then 1 else 0)
        ≤ ∑ _i : Fin k, 1 := Finset.sum_le_sum fun i _ => by split_ifs <;> omega
      _ = k := by simp
  omega

/-- Unless both roots of the adjoint site are present, a word has at most `k` T-states. -/
theorem adjointSiteWordTCount_le_of_block {B k : ℕ} (u : AdjointSiteWord B k) (q : MixedParams)
    (hu : adjointSiteWordBlock u = q) (hq : ¬ (q.d1 = 1 ∧ q.d3 = 0)) :
    adjointSiteWordTCount u ≤ k := by
  have hadj : adjointSiteStateYCount u.1 ≠ 2 := by
    intro h2
    apply hq
    subst hu
    rcases u with ⟨⟨a, b⟩, w⟩
    cases a <;> cases b
    · simp [adjointSiteStateYCount] at h2
    · simp only [adjointSiteStateYCount] at h2
      split_ifs at h2 <;> simp_all
    · simp only [adjointSiteStateYCount] at h2
      split_ifs at h2 <;> simp_all
    · simp [adjointSiteWordBlock]
  unfold adjointSiteWordTCount
  rw [if_neg hadj, zero_add]
  calc ∑ i : Fin k, (if doubledSiteStateYCount (u.2.1 i) = 2 then 1 else 0)
      ≤ ∑ _i : Fin k, 1 := Finset.sum_le_sum fun i _ => by split_ifs <;> omega
    _ = k := by simp

/-- The bound on the number of T-states of the words of a block. -/
def adjointSiteTBound (k : ℕ) (q : MixedParams) : ℕ :=
  k + if q.d1 = 1 ∧ q.d3 = 0 then 1 else 0

theorem adjointSiteWordTCount_le_bound {B k : ℕ} (u : AdjointSiteWord B k) (q : MixedParams)
    (hu : adjointSiteWordBlock u = q) : adjointSiteWordTCount u ≤ adjointSiteTBound k q := by
  unfold adjointSiteTBound
  split_ifs with hq
  · exact adjointSiteWordTCount_le u
  · rw [add_zero]
    exact adjointSiteWordTCount_le_of_block u q hu hq

/-- No word of a block has more T-states than the bound. -/
theorem adjointSiteWordCount_eq_zero_of_lt (B k : ℕ) (q : MixedParams) (j : ℕ)
    (hj : adjointSiteTBound k q < j) : adjointSiteWordCount B k q j = 0 := by
  unfold adjointSiteWordCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro u - ⟨hu, hju⟩
  have := adjointSiteWordTCount_le_bound u q hu
  omega

/-! ### The reduction -/

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient quotients are nested ring quotients of a polynomial algebra.
/-- A quotient of a finite-dimensional ring by an ideal has at most its dimension. -/
theorem adjointSiteQuotient_finrank_le (q : MixedParams) (hq : MixedValid q) (h : ℕ)
    (I : Ideal (AdjointSiteCoefficientRing q h)) :
    Module.finrank ℂ (AdjointSiteCoefficientRing q h ⧸ I) ≤
      Module.finrank ℂ (AdjointSiteCoefficientRing q h) := by
  haveI := adjointSiteCoefficientRing_finiteDimensional q hq h
  rw [← (Submodule.Quotient.restrictScalarsEquiv ℂ I).finrank_eq]
  exact Submodule.finrank_quotient_le (I.restrictScalars ℂ)

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient quotients are nested ring quotients of a polynomial algebra.
/-- **Reduction to the low strata.** `OneAdjointStratumCount B k` follows from `dim A ≤ w₀` and
the stratum inequalities for `1 ≤ j ≤ k + [(d₁, d₃) = (1, 0)]`. -/
theorem oneAdjointStratumCount_of_low_strata (B k : ℕ)
    (hlow : ∀ (d : Fin 3 → ℕ) (e₁ e₂ : ℕ), MixedValid (mixedLabelBlockParams 1 B d e₁ e₂) →
      Module.finrank ℂ (AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂) (B - k)) ≤
          adjointSiteWordCount B k (mixedLabelBlockParams 1 B d e₁ e₂) 0 ∧
        ∀ j, 1 ≤ j → j ≤ adjointSiteTBound k (mixedLabelBlockParams 1 B d e₁ e₂) →
          Module.finrank ℂ
              (AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) ⧸
                adjointSiteJointTopIdeal (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) j) ≤
            adjointSiteWordCount B k (mixedLabelBlockParams 1 B d e₁ e₂) 0 -
              adjointSiteWordCount B k (mixedLabelBlockParams 1 B d e₁ e₂) j) :
    OneAdjointStratumCount B k := by
  intro d e₁ e₂ hv
  obtain ⟨h0, hj⟩ := hlow d e₁ e₂ hv
  refine ⟨h0, fun j hj1 => ⟨?_, adjointSiteJointTopIdeal_eq_sup _ _ _⟩⟩
  by_cases hjb : j ≤ adjointSiteTBound k (mixedLabelBlockParams 1 B d e₁ e₂)
  · exact hj j hj1 hjb
  · rw [adjointSiteWordCount_eq_zero_of_lt B k _ j (by omega), Nat.sub_zero]
    exact (adjointSiteQuotient_finrank_le _ hv _ _).trans h0

/-- **Law B at one adjoint site from the low strata.** -/
theorem adjointSiteLawB_of_low_strata (B k : ℕ) (hk : 1 ≤ k) (hkB : 2 * k ≤ B)
    (hlow : ∀ (d : Fin 3 → ℕ) (e₁ e₂ : ℕ), MixedValid (mixedLabelBlockParams 1 B d e₁ e₂) →
      Module.finrank ℂ (AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂) (B - k)) ≤
          adjointSiteWordCount B k (mixedLabelBlockParams 1 B d e₁ e₂) 0 ∧
        ∀ j, 1 ≤ j → j ≤ adjointSiteTBound k (mixedLabelBlockParams 1 B d e₁ e₂) →
          Module.finrank ℂ
              (AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) ⧸
                adjointSiteJointTopIdeal (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) j) ≤
            adjointSiteWordCount B k (mixedLabelBlockParams 1 B d e₁ e₂) 0 -
              adjointSiteWordCount B k (mixedLabelBlockParams 1 B d e₁ e₂) j) :
    AdjointSiteLawB B k :=
  adjointSiteLawB_of_stratumCount B k hk hkB (oneAdjointStratumCount_of_low_strata B k hlow)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.polynomialSubmoduleTopIdeal_eq_bot_of_lt
#print axioms VOA.DeligneAudit.SL4T.adjointSiteJointTopIdeal_eq_bot_of_lt
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordTCount_le
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordTCount_le_of_block
#print axioms VOA.DeligneAudit.SL4T.adjointSiteTBound
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordTCount_le_bound
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordCount_eq_zero_of_lt
#print axioms VOA.DeligneAudit.SL4T.adjointSiteQuotient_finrank_le
#print axioms VOA.DeligneAudit.SL4T.oneAdjointStratumCount_of_low_strata
#print axioms VOA.DeligneAudit.SL4T.adjointSiteLawB_of_low_strata
