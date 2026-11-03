import VOA.DeligneAudit.D4LeviKSRzBilinearPolynomial

/-! The arbitrary symmetric X factor and Z spectator Rz family. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rz_gen_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b k l s d : ℕ)
    (F : MvPolynomial (Fin b ⊕ Fin a) ℂ)
    (R : MvPolynomial (Fin l) ℂ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b (k + l) d)
    (hF : F ∈ symmetricSubalgebra (Fin b ⊕ Fin a) ℂ)
    (hdegree : ∀ p ∈ F.support, ∀ q ∈ R.support,
      ((Finset.univ.toList : List (Fin b ⊕ Fin a)).map
          (fun i => p i)).sum +
        ((Finset.univ.toList : List (Fin l)).map
          (fun j => q j)).sum + s = d) :
    ∃ T : pairTargetSymmetric a b (k + l),
      (T : MvPolynomial (PairTarget a b (k + l)) ℂ) =
        rename (rzXTarget a b (k + l)) F *
          rename (fun z : Fin (k + l) =>
            (Sum.inr (Sum.inr z) : PairTarget a b (k + l)))
            (rzOrbitSum _
              (rename (Fin.castAdd l) (hsymm (Fin k) ℂ s) *
                rename (Fin.natAdd k) R)) ∧
      T ∈ (pairTargetQuotientEvaluation ρ w m i a b (k + l)
        (pairKernelPrefix_of_sat ρ w m i a b (k + l)
          d h hi hkey)).ker := by
  classical
  let card : ℂ := Nat.card (Equiv.Perm (Fin b ⊕ Fin a))
  have hc : card ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  let T : pairTargetSymmetric a b (k + l) :=
    card⁻¹ • rzBilinearTarget a b k l s F R
  refine ⟨T, ?_, ?_⟩
  · change card⁻¹ •
        (rzBilinearTarget a b k l s F R :
          MvPolynomial (PairTarget a b (k + l)) ℂ) = _
    rw [rzBilinearTarget_polynomial,
      rzOrbitSum_eq_card_smul_of_symmetric _ F hF]
    simp [map_smul, smul_mul_assoc, smul_smul,
      inv_mul_cancel₀ hc, mul_smul_comm]
    have hcard : card =
        (Fintype.card (Equiv.Perm (Fin b ⊕ Fin a)) : ℂ) := by
      simp [card, Nat.card_eq_fintype_card]
    rw [← hcard, inv_mul_cancel₀ hc, one_smul]
  · exact (pairTargetQuotientEvaluation ρ w m i a b (k + l)
      (pairKernelPrefix_of_sat ρ w m i a b (k + l)
        d h hi hkey)).ker.smul_mem card⁻¹
      (rzBilinearTarget_mem_ker ρ w m i a b k l s d
        F R h hk hks hi hkey hdegree)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_gen_mem_ker
