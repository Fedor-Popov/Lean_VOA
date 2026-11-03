import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleActualData
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleRepresentation
import VOA.DeligneAudit.D4FusionContactAllMNormalIdeal

/-! Every operator in the finite current representation is exactly the
original D4 Levi/contact derivation, on the whole polynomial ring. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)
noncomputable section

theorem actual_g0_coeff (g : Fin 10) (i j : Fin 9) :
    contactF (zeroIndex g) (radIndex i) (radIndex j) =
      if j = target (Fin.castAdd 8 g) i then (coeff (Fin.castAdd 8 g) i:ℂ) else 0 := by
  change (fZ br (zeroIndex g) (radIndex i) (radIndex j):ℂ) = _
  rw [show zeroIndex g = derivRoot g from rfl,root_images_Z]
  have h := actual_g0_check g i j
  by_cases hj : j = target (Fin.castAdd 8 g) i
  · simp only [if_pos hj] at h ⊢
    exact_mod_cast h
  · simp only [if_neg hj] at h ⊢
    exact_mod_cast h

theorem deriv_g0 (m : ℕ) (g : Fin 10) (k : ℕ) :
    deriv ℂ m (Fin.castAdd 8 g) k = g0Deriv m g k := by
  apply MvPolynomial.derivation_ext
  intro x
  rw [deriv_X]
  change coeff (Fin.castAdd 8 g) x.1 • modeX m (target (Fin.castAdd 8 g) x.1) (k+x.2.val) = _
  simp only [g0Deriv,MvPolynomial.mkDerivation_X,g0Image]
  simp_rw [actual_g0_coeff]
  simp only [ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Int.cast_smul_eq_zsmul]

theorem deriv_contact (m : ℕ) (e : Fin 8) (k : ℕ) :
    deriv ℂ m (Fin.natAdd 10 e) k = eDeriv m e k := by
  apply MvPolynomial.derivation_ext
  intro x
  rw [deriv_X,actual_contact_coeff]
  change (if x.1=8 then (1:ℤ) else 0) •
    modeX m (target (Fin.natAdd 10 e) x.1) (k+x.2.val) = _
  simp only [eDeriv,MvPolynomial.mkDerivation_X,eImage]
  by_cases hx : x.1=8
  · rw [if_pos hx,one_zsmul,hx,actual_contact_target,if_pos rfl]
  · rw [if_neg hx,zero_zsmul,if_neg hx]

/-- All modes, including modes beyond the truncation, preserve the actual ideal. -/
theorem deriv_closed (m : ℕ) (a : Fin 18) (k : ℕ) {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ AllM.candidateIdeal m) : deriv ℂ m a k p ∈ AllM.candidateIdeal m := by
  by_cases ha : a.val < 10
  · let g : Fin 10 := ⟨a.val,ha⟩
    have he : Fin.castAdd 8 g = a := Fin.ext rfl
    rw [← he,deriv_g0]
    exact AllMNormal.g0_closed m k g hp
  · let e : Fin 8 := ⟨a.val-10,by omega⟩
    have he : Fin.natAdd 10 e = a := by
      apply Fin.ext
      change 10+(a.val-10) = a.val
      omega
    rw [← he,deriv_contact]
    exact AllMNormal.e_closed m k e hp

end
#print axioms deriv_g0
#print axioms deriv_contact
#print axioms deriv_closed
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
