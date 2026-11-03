import VOA.DeligneAudit.D4LeviKSBlockThetaGraded

/-! Garland generators under the one-block function model, with spectators. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.CLAssembly
open VOA.DeligneAudit.LeviConversion

theorem ksBlockTheta_mono_ofFn (n : ℕ) (v : Fin n → ℕ) :
    ksBlockTheta n (mono (List.ofFn v)) =
      rzOrbitSum (Fin n) (∏ i, X i ^ v i) := by
  rw [mono_eq]
  exact ksBlockTheta_occupation n v

theorem ks_xx_eq_mode_vectors (k s : ℕ) :
    xx k s = ∑ e : {e : Fin k → ℕ // ∑ i, e i = s},
      mono (List.ofFn e.1) := by
  have hb : bWord (fun r => (X r : R)) (List.replicate k 0) = Zs ^ k := by
    simp [bWord, bTail, Zs, z]
  rw [xx, ← hb, ← shiftedWordCoeff_eq_coeff,
    shiftedWordCoeff_eq_allocations]
  exact rz_zero_alloc_sum_eq_vector_sum k s mono

theorem ksOrbitSum_sum {ι : Type*} (n : ℕ) (S : Finset ι)
    (P : ι → MvPolynomial (Fin n) ℂ) :
    rzOrbitSum (Fin n) (∑ i ∈ S, P i) = ∑ i ∈ S, rzOrbitSum (Fin n) (P i) := by
  classical
  simp only [rzOrbitSum, map_sum]
  exact Finset.sum_comm

/-- The exact factorial normalization in the function model. -/
theorem ksBlockTheta_xx (k s : ℕ) :
    ksBlockTheta k (xx k s) = (k.factorial : ℂ) • hsymm (Fin k) ℂ s := by
  classical
  rw [ks_xx_eq_mode_vectors, map_sum]
  simp_rw [ksBlockTheta_mono_ofFn]
  rw [← ksOrbitSum_sum, ← rz_hsymm_eq_sum_vectors]
  rw [rzOrbitSum_eq_card_smul_of_symmetric _ _ (hsymm_isSymmetric _ _ _)]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem ks_mono_append (l t : List ℕ) : mono (l ++ t) = mono l * mono t := by
  simp [mono]

theorem ksBlockTheta_mono_mul (k l : ℕ) (α : Fin k → ℕ) (β : Fin l → ℕ) :
    ksBlockTheta (k + l) (mono (List.ofFn α) * mono (List.ofFn β)) =
      rzOrbitSum (Fin (k + l))
        ((∏ i : Fin k, X (Fin.castAdd l i) ^ α i) *
          ∏ j : Fin l, X (Fin.natAdd k j) ^ β j) := by
  have hl : List.ofFn (Fin.addCases α β) = List.ofFn α ++ List.ofFn β := by
    rw [List.ofFn_add]
    congr 1
    · congr 1
      funext i
      change Fin.addCases α β (Fin.castAdd l i) = α i
      simp
    · simp
  rw [← ks_mono_append, ← hl, ksBlockTheta_mono_ofFn]
  congr 1
  simp [Fin.prod_univ_add]

/-- A Garland relation times any spectator monomial is the full orbit sum
    of a complete homogeneous factor times that spectator monomial. -/
theorem ksBlockTheta_xx_mul_mono (k l s : ℕ) (β : Fin l → ℕ) :
    ksBlockTheta (k + l) (xx k s * mono (List.ofFn β)) =
      rzOrbitSum (Fin (k + l))
        (rename (Fin.castAdd l) (hsymm (Fin k) ℂ s) *
          ∏ j : Fin l, X (Fin.natAdd k j) ^ β j) := by
  classical
  rw [ks_xx_eq_mode_vectors, Finset.sum_mul, map_sum]
  simp_rw [ksBlockTheta_mono_mul]
  rw [← ksOrbitSum_sum, ← Finset.sum_mul]
  congr 2
  rw [rz_hsymm_eq_sum_vectors, map_sum]
  simp only [map_prod, map_pow, rename_X]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_mono_ofFn
#print axioms VOA.DeligneAudit.D4Levi.ks_xx_eq_mode_vectors
#print axioms VOA.DeligneAudit.D4Levi.ksOrbitSum_sum
#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_xx
#print axioms VOA.DeligneAudit.D4Levi.ks_mono_append
#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_mono_mul
#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_xx_mul_mono
