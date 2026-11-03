import VOA.DeligneAudit.D4LeviKSMixedHsymmPrefix
import VOA.DeligneAudit.D4LeviKSPairSymmetricEmbeds

/-! The maximal-active mixed complete homogeneous seeds belong to the PAIR source. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

def rxMixedSlot (a b c : ℕ) :
    Fin c ⊕ (Fin b ⊕ Fin a) → PairSource a b c
  | Sum.inl z => Sum.inr (Sum.inr z)
  | Sum.inr x => Sum.inl x

def ryMixedSlot (a b c : ℕ) : Fin c ⊕ Fin b → PairSource a b c
  | Sum.inl z => Sum.inr (Sum.inr z)
  | Sum.inr y => Sum.inr (Sum.inl y)

noncomputable def rxMixedSeed (a b c s : ℕ) :
    MvPolynomial (PairSource a b c) ℂ :=
  rename (rxMixedSlot a b c)
    (hsymm (Fin c ⊕ (Fin b ⊕ Fin a)) ℂ s)

noncomputable def ryMixedSeed (a b c s : ℕ) :
    MvPolynomial (PairSource a b c) ℂ :=
  rename (ryMixedSlot a b c) (hsymm (Fin c ⊕ Fin b) ℂ s)

theorem rxMixedSlot_psum (a b c r : ℕ) :
    rename (rxMixedSlot a b c)
        (psum (Fin c ⊕ (Fin b ⊕ Fin a)) ℂ r) =
      pairSourceZPsum a b c r + pairSourceXPsum a b c r := by
  simp [psum, rxMixedSlot, pairSourceZPsum, pairSourceXPsum,
    Fintype.sum_sum_type]

theorem ryMixedSlot_psum (a b c r : ℕ) :
    rename (ryMixedSlot a b c) (psum (Fin c ⊕ Fin b) ℂ r) =
      pairSourceZPsum a b c r + sourceYPsum a b c r := by
  simp [psum, ryMixedSlot, pairSourceZPsum, sourceYPsum,
    Fintype.sum_sum_type]

theorem rxMixedSeed_mem (a b c s : ℕ) :
    rxMixedSeed a b c s ∈ pairSourceSymmetric a b c := by
  unfold rxMixedSeed
  apply symmetric_image_mem_of_power_sums _ _
    (rename (rxMixedSlot a b c)) (pairSourceSymmetric a b c)
  · intro r
    rw [rxMixedSlot_psum]
    exact (pairSourceSymmetric a b c).add_mem
      (by simpa [pairSourcePower] using pairSourcePower_mem a b c 2 r)
      (by simpa [pairSourcePower] using pairSourcePower_mem a b c 0 r)
  · exact hsymm_isSymmetric (Fin c ⊕ (Fin b ⊕ Fin a)) ℂ s

theorem ryMixedSeed_mem (a b c s : ℕ) :
    ryMixedSeed a b c s ∈ pairSourceSymmetric a b c := by
  unfold ryMixedSeed
  apply symmetric_image_mem_of_power_sums _ _
    (rename (ryMixedSlot a b c)) (pairSourceSymmetric a b c)
  · intro r
    rw [ryMixedSlot_psum]
    exact (pairSourceSymmetric a b c).add_mem
      (by simpa [pairSourcePower] using pairSourcePower_mem a b c 2 r)
      (by simpa [pairSourcePower] using pairSourcePower_mem a b c 1 r)
  · exact hsymm_isSymmetric (Fin c ⊕ Fin b) ℂ s

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rxMixedSlot_psum
#print axioms VOA.DeligneAudit.D4Levi.ryMixedSlot_psum
#print axioms VOA.DeligneAudit.D4Levi.rxMixedSeed_mem
#print axioms VOA.DeligneAudit.D4Levi.ryMixedSeed_mem
