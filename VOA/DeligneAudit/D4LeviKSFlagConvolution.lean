import VOA.DeligneAudit.D4LeviKSFlagCoefficients

/-! Maximal flag generators as complete-series convolutions. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

noncomputable def ksTargetXAlphabet (a b c : ℕ) :
    List (MvPolynomial (PairTarget a b c) ℂ) :=
  List.ofFn fun x : Fin a => X (Sum.inl x)

noncomputable def ksTargetYAlphabet (a b c : ℕ) :
    List (MvPolynomial (PairTarget a b c) ℂ) :=
  List.ofFn fun y : Fin b => X (Sum.inr (Sum.inl y))

noncomputable def ksTargetZAlphabet (a b c : ℕ) :
    List (MvPolynomial (PairTarget a b c) ℂ) :=
  List.ofFn fun z : Fin c => X (Sum.inr (Sum.inr z))

theorem ksTargetXAlphabet_coeff (a b c s : ℕ) :
    PowerSeries.coeff s (ksHSeries (ksTargetXAlphabet a b c)) =
      ksTargetXMap a b c (hsymm (Fin a) ℂ s) :=
  ksHSeries_coeff_aeval a s _

theorem ksTargetYAlphabet_coeff (a b c s : ℕ) :
    PowerSeries.coeff s (ksHSeries (ksTargetYAlphabet a b c)) =
      ksTargetYMap a b c (hsymm (Fin b) ℂ s) :=
  ksHSeries_coeff_aeval b s _

theorem ksTargetZAlphabet_coeff (a b c s : ℕ) :
    PowerSeries.coeff s (ksHSeries (ksTargetZAlphabet a b c)) =
      ksTargetZMap a b c (hsymm (Fin c) ℂ s) :=
  ksHSeries_coeff_aeval c s _

theorem ksTargetYZAlphabet_coeff (a b c s : ℕ) :
    PowerSeries.coeff s
        (ksHSeries (ksTargetYAlphabet a b c ++ ksTargetZAlphabet a b c)) =
      (ryMixedTarget a b c s : MvPolynomial (PairTarget a b c) ℂ) := by
  rw [ksHSeries_perm (vs := ksTargetYAlphabet a b c ++ ksTargetZAlphabet a b c)
    (ws := ksTargetZAlphabet a b c ++ ksTargetYAlphabet a b c) List.perm_append_comm,
    ryMixedTarget_polynomial]
  have he : rename (ryMixedTargetSlot a b c) =
      aeval (Sum.elim
        (fun z => (X (Sum.inr (Sum.inr z)) : MvPolynomial (PairTarget a b c) ℂ))
        (fun y => X (Sum.inr (Sum.inl y)))) := by
    ext t
    rcases t with z | y <;> simp [ryMixedTargetSlot]
  rw [he]
  exact ksHSeries_coeff_two_blocks c b s
    (fun z => (X (Sum.inr (Sum.inr z)) : MvPolynomial (PairTarget a b c) ℂ))
    (fun y => X (Sum.inr (Sum.inl y)))

def ksTargetEnumeration (a b c : ℕ) : Fin (a + (b + c)) ≃ PairTarget a b c :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm)

theorem ksTargetEnumeration_list (a b c : ℕ) :
    List.ofFn (fun i => (X (ksTargetEnumeration a b c i) :
      MvPolynomial (PairTarget a b c) ℂ)) =
    ksTargetXAlphabet a b c ++ (ksTargetYAlphabet a b c ++ ksTargetZAlphabet a b c) := by
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    change X (ksTargetEnumeration a b c (Fin.castAdd (b + c) i)) = X (Sum.inl i)
    simp [ksTargetEnumeration]
  · rw [List.ofFn_add]
    congr 1
    · congr 1
      funext i
      change X (ksTargetEnumeration a b c
        (Fin.natAdd a (Fin.castAdd c i))) = X (Sum.inr (Sum.inl i))
      simp [ksTargetEnumeration]
    · congr 1
      funext i
      change X (ksTargetEnumeration a b c
        (Fin.natAdd a (Fin.natAdd b i))) = X (Sum.inr (Sum.inr i))
      simp [ksTargetEnumeration]

theorem ksTargetXYZAlphabet_coeff (a b c s : ℕ) :
    PowerSeries.coeff s (ksHSeries
        (ksTargetXAlphabet a b c ++
          (ksTargetYAlphabet a b c ++ ksTargetZAlphabet a b c))) =
      (rxMixedTarget a b c s : MvPolynomial (PairTarget a b c) ℂ) := by
  rw [← ksTargetEnumeration_list, rxMixedTarget_eq_hsymm]
  simpa only [aeval_X_left_apply] using
    ksHSeries_coeff_equiv (a + (b + c)) s (ksTargetEnumeration a b c) (X (R := ℂ))

theorem ksFlagY_convolution (a b c s : ℕ) :
    (ryMixedTarget a b c s : MvPolynomial (PairTarget a b c) ℂ) =
      ksTargetYMap a b c (hsymm (Fin b) ℂ s) +
        ∑ t ∈ Finset.range s,
          ksTargetZMap a b c (hsymm (Fin c) ℂ (s - t)) *
            ksTargetYMap a b c (hsymm (Fin b) ℂ t) := by
  rw [← ksTargetYZAlphabet_coeff, ksHSeries_append_coeff_relative]
  simp only [ksTargetYAlphabet_coeff, ksTargetZAlphabet_coeff]

theorem ksFlagX_convolution (a b c s : ℕ) :
    (rxMixedTarget a b c s : MvPolynomial (PairTarget a b c) ℂ) =
      ksTargetXMap a b c (hsymm (Fin a) ℂ s) +
        ∑ t ∈ Finset.range s,
          (ryMixedTarget a b c (s - t) : MvPolynomial (PairTarget a b c) ℂ) *
            ksTargetXMap a b c (hsymm (Fin a) ℂ t) := by
  rw [← ksTargetXYZAlphabet_coeff, ksHSeries_append_coeff_relative]
  simp only [ksTargetXAlphabet_coeff, ksTargetYZAlphabet_coeff]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksTargetXAlphabet_coeff
#print axioms VOA.DeligneAudit.D4Levi.ksTargetYAlphabet_coeff
#print axioms VOA.DeligneAudit.D4Levi.ksTargetZAlphabet_coeff
#print axioms VOA.DeligneAudit.D4Levi.ksTargetYZAlphabet_coeff
#print axioms VOA.DeligneAudit.D4Levi.ksTargetEnumeration_list
#print axioms VOA.DeligneAudit.D4Levi.ksTargetXYZAlphabet_coeff
#print axioms VOA.DeligneAudit.D4Levi.ksFlagY_convolution
#print axioms VOA.DeligneAudit.D4Levi.ksFlagX_convolution
