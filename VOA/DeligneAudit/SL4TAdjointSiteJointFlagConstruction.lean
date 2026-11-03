import VOA.DeligneAudit.SL4TAdjointSiteGrading
import VOA.DeligneAudit.SL4TAdjointSiteWordStrata

/-!
# The joint relation flags of one adjoint site from the stratum count

This file proves the ring statement `AdjointSiteJointFlagConstruction B k` for `2k ≤ B`: the
one-adjoint-site stratum count S_A(B, k) produces, on every valid block `q`, a power-sum-stable
relation flag of `A = R / I_J(h)` (`h = B - k`) with level relations in the joint ideal
`(P_y, t^(h+1), s t^h)` and cost at most the block word weight `Σ 3^T 2^D`.

Route: `A` is graded and finite dimensional (`SL4TAdjointSiteGrading`); `P_y` is monic and
homogeneous of degree `r`, the generators `t^(h+1)` and `s t^h` are homogeneous, and the power
sums have positive degree. The graded level theorem (`gradedJointRelationLineFlag`) then gives a
flag of cost `Σ_j (dim G_j - dim G_(j+1)) · cost(L_j)` with `L_j = r - min(j, ⌊r/2⌋)`.
Only the upper bounds `dim A/G_j ≤ w_0 - w_j` of S_A enter, through summation by parts
(`stratumCost_le_of_codimension_le`), and the block cost is
`Σ_j (w_j - w_(j+1)) · cost(L_j)` (`adjointSiteBlockBound_eq_strata`). The third clause of
S_A (`G_j = G_j(h+1) + s G_j(h)`) is not used.

Consequence: `adjointSiteLawB_of_residuals`, i.e. `AdjointSiteLawBFromResiduals B k` for
`1 ≤ k` and `2k ≤ B`: S_A(B, k) and L₂(B - k) imply Law B at one adjoint site.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- Every valid block with one adjoint site is a label block. -/
theorem mixedValidBlock_eq_label (B : ℕ) (q : MixedParams) (hq : q ∈ mixedValidBlocks 1 B) :
    ∃ (d : Fin 3 → ℕ) (e₁ e₂ : ℕ), q = mixedLabelBlockParams 1 B d e₁ e₂ := by
  obtain ⟨hv, hA, hB⟩ := (mem_mixedValidBlocks 1 B q).mp hq
  obtain ⟨A', B', d1, d2, d3, e1, e2⟩ := q
  simp only [MixedValid] at hv
  simp only at hA hB
  subst hA hB
  obtain ⟨_, _, h1, _, h2, _, h3, _, h4, _, h5, _⟩ := hv
  refine ⟨![d1.toNat, d2.toNat, d3.toNat], e1.toNat, e2.toNat, ?_⟩
  change (⟨((1 : ℕ) : ℤ), (B : ℤ), d1, d2, d3, e1, e2⟩ : MixedParams) =
    ⟨((1 : ℕ) : ℤ), (B : ℤ), ((d1.toNat : ℕ) : ℤ), ((d2.toNat : ℕ) : ℤ), ((d3.toNat : ℕ) : ℤ),
      ((e1.toNat : ℕ) : ℤ), ((e2.toNat : ℕ) : ℤ)⟩
  congr 1 <;> omega

set_option maxHeartbeats 400000 in
-- The coefficient ring is a nested quotient carrying a constructed grading.
set_option synthInstance.maxHeartbeats 100000 in
/-- **The joint relation flag of one label block from the stratum count.** -/
theorem adjointSiteJointFlag_of_stratumCount (B k : ℕ) (hkB : 2 * k ≤ B)
    (hS : OneAdjointStratumCount B k) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams 1 B d e₁ e₂)) :
    AdjointSiteJointFlag B k (mixedLabelBlockParams 1 B d e₁ e₂) := by
  obtain ⟨hdim, hstrata⟩ := hS d e₁ e₂ hv
  haveI := adjointSiteCoefficientRing_finiteDimensional (mixedLabelBlockParams 1 B d e₁ e₂) hv
    (B - k)
  rcases subsingleton_or_nontrivial
      (AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂) (B - k)) with hsub | hnt
  · apply mixedQuotientRelationFlag_of_relationLineFlag
    have htop : (⊥ : Submodule ℂ
        (AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂) (B - k))) = ⊤ :=
      Subsingleton.elim _ _
    rw [htop]
    exact relationLineFlagFrom_mono relationLineFlagFrom_top (Nat.zero_le _)
  letI := adjointSiteGradedAlgebra (mixedLabelBlockParams 1 B d e₁ e₂) (B - k)
  obtain ⟨hPm, hPr⟩ := adjointSiteCharacteristic_monic (mixedLabelBlockParams 1 B d e₁ e₂) hv
    (B - k)
  have hPh := adjointSiteCharacteristic_homogeneous (mixedLabelBlockParams 1 B d e₁ e₂) hv
    (B - k)
  have hgens : ∀ g ∈ ({(X : (AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂)
      (B - k))[X]) ^ (B - k + 1), Polynomial.C (Ideal.Quotient.mk
        (adjointSiteKernelIdeal (mixedLabelBlockParams 1 B d e₁ e₂) (B - k))
        (adjointSiteJointSymbol (mixedLabelBlockParams 1 B d e₁ e₂))) * X ^ (B - k)} :
          Set _), ∃ δ : ℤ, PolynomialHomogeneous
            (adjointSiteGrading (mixedLabelBlockParams 1 B d e₁ e₂) (B - k)) δ g := by
    rintro g (rfl | rfl)
    · exact ⟨_, polynomialHomogeneous_X_pow (B - k + 1)⟩
    · obtain ⟨e, he⟩ := adjointSiteJointSymbol_homogeneous (mixedLabelBlockParams 1 B d e₁ e₂)
        (B - k)
      exact ⟨_, (polynomialHomogeneous_C he).mul (polynomialHomogeneous_X_pow (B - k))⟩
  have hflag := gradedJointRelationLineFlag
    (𝒜 := adjointSiteGrading (mixedLabelBlockParams 1 B d e₁ e₂) (B - k)) _
    (adjointSiteGrading_neg (mixedLabelBlockParams 1 B d e₁ e₂) (B - k))
    (fun s => Ideal.Quotient.mk (adjointSiteKernelIdeal (mixedLabelBlockParams 1 B d e₁ e₂)
      (B - k)) (mixedPowerSum (mixedLabelBlockParams 1 B d e₁ e₂) s))
    (fun s _ => adjointSitePowerSum_mem_grading (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) s)
    hPm hPr hPh hgens
    (jointStratumLevel (mixedWeight (mixedLabelBlockParams 1 B d e₁ e₂)).toNat)
    (fun j _ => jointStratumLevel_ge _ j)
  have hrel : adjointSiteJointRelationIdeal (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) =
      Ideal.span {adjointSiteCharacteristic (mixedLabelBlockParams 1 B d e₁ e₂) (B - k)} ⊔
        Ideal.span {(X : (AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂)
          (B - k))[X]) ^ (B - k + 1), Polynomial.C (Ideal.Quotient.mk
            (adjointSiteKernelIdeal (mixedLabelBlockParams 1 B d e₁ e₂) (B - k))
            (adjointSiteJointSymbol (mixedLabelBlockParams 1 B d e₁ e₂))) * X ^ (B - k)} := by
    rw [adjointSiteJointRelationIdeal, sup_assoc, Ideal.span_insert]
  rw [← hrel] at hflag
  apply mixedQuotientRelationFlag_of_relationLineFlag
  apply relationLineFlagFrom_mono hflag
  rw [adjointSiteBlockBound_eq_strata hkB]
  -- Summation by parts against the upper bounds of the stratum count.
  have hnest (j : ℕ) (hj : j < (mixedWeight (mixedLabelBlockParams 1 B d e₁ e₂)).toNat + 1) :
      adjointSiteJointTopIdeal (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) (j + 1) ≤
        adjointSiteJointTopIdeal (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) j := by
    unfold adjointSiteJointTopIdeal
    by_cases hjr : j + 1 ≤ (mixedWeight (mixedLabelBlockParams 1 B d e₁ e₂)).toNat
    · exact polynomialSubmoduleTopIdeal_succ_le _ j hjr
    · have hj' : j = (mixedWeight (mixedLabelBlockParams 1 B d e₁ e₂)).toNat := by omega
      rw [hj', polynomialSubmoduleTopIdeal_succ_eq_bot hPm hPr]
      exact bot_le
  have hquot (j : ℕ) : Module.finrank ℂ
      (AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂) (B - k)) -
        Module.finrank ℂ ((adjointSiteJointTopIdeal (mixedLabelBlockParams 1 B d e₁ e₂) (B - k)
          j).restrictScalars ℂ) =
      Module.finrank ℂ
        (AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) ⧸
          adjointSiteJointTopIdeal (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) j) := by
    have h₁ := ((adjointSiteJointTopIdeal (mixedLabelBlockParams 1 B d e₁ e₂) (B - k)
      j).restrictScalars ℂ).finrank_quotient_add_finrank
    have h₂ := (Submodule.Quotient.restrictScalarsEquiv ℂ
      (adjointSiteJointTopIdeal (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) j)).finrank_eq
    omega
  refine stratumCost_le_of_codimension_le _
    (fun j => Module.finrank ℂ ((adjointSiteJointTopIdeal (mixedLabelBlockParams 1 B d e₁ e₂)
      (B - k) j).restrictScalars ℂ))
    (fun j => adjointSiteWordCount B k (mixedLabelBlockParams 1 B d e₁ e₂) j)
    (fun j => lineLevelCost (mixedWeight (mixedLabelBlockParams 1 B d e₁ e₂)).toNat
      (jointStratumLevel (mixedWeight (mixedLabelBlockParams 1 B d e₁ e₂)).toNat j))
    (fun j hj => Submodule.finrank_mono (fun x hx => hnest j hj hx))
    (fun j _ => adjointSiteWordCount_succ_le B k _ j)
    (fun j => lineLevelCost_jointStratumLevel_succ_le _ j) ?_
  intro j _
  have hg0 : Module.finrank ℂ ((adjointSiteJointTopIdeal (mixedLabelBlockParams 1 B d e₁ e₂)
      (B - k) 0).restrictScalars ℂ) = Module.finrank ℂ
        (AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂) (B - k)) := by
    unfold adjointSiteJointTopIdeal
    rw [polynomialSubmoduleTopIdeal_zero_eq_top, Submodule.restrictScalars_top, finrank_top]
  change Module.finrank ℂ ((adjointSiteJointTopIdeal (mixedLabelBlockParams 1 B d e₁ e₂)
      (B - k) 0).restrictScalars ℂ) - Module.finrank ℂ ((adjointSiteJointTopIdeal
        (mixedLabelBlockParams 1 B d e₁ e₂) (B - k) j).restrictScalars ℂ) ≤
    adjointSiteWordCount B k (mixedLabelBlockParams 1 B d e₁ e₂) 0 -
      adjointSiteWordCount B k (mixedLabelBlockParams 1 B d e₁ e₂) j
  rw [hg0, hquot]
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    have h₁ := hquot 0
    rw [← hg0] at h₁
    omega
  · exact (hstrata j hj1).1

/-- **The joint flag construction.** For `2k ≤ B`, the one-adjoint-site stratum count produces
a joint relation flag of the word cost on every valid block. -/
theorem adjointSiteJointFlagConstruction_of_le (B k : ℕ) (hkB : 2 * k ≤ B) :
    AdjointSiteJointFlagConstruction B k := by
  intro hS q hq
  obtain ⟨hv, -, -⟩ := (mem_mixedValidBlocks 1 B q).mp hq
  obtain ⟨d, e₁, e₂, rfl⟩ := mixedValidBlock_eq_label B q hq
  exact adjointSiteJointFlag_of_stratumCount B k hkB hS d e₁ e₂ hv

/-- **Law B at one adjoint site from its two residuals.** For `1 ≤ k` and `2k ≤ B`, the
stratum count S_A(B, k) and the flat level relation L₂(B - k) imply
`dim W(θ + Bω₂, B - k + 1)/⟨f₂(B - k)v⟩ ≤ 15 · 20^k · 6^(B - 2k)`. -/
theorem adjointSiteLawB_of_residuals (B k : ℕ) (hk : 1 ≤ k) (hkB : 2 * k ≤ B) :
    AdjointSiteLawBFromResiduals B k :=
  adjointSiteLawB_of_residuals_of_jointFlagConstruction B k hk hkB
    (adjointSiteJointFlagConstruction_of_le B k hkB)

end

end VOA.DeligneAudit.SL4T
