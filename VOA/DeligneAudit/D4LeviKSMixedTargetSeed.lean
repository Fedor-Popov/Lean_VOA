import VOA.DeligneAudit.D4LeviKSMixedSymmetricSeed
import VOA.DeligneAudit.D4LeviKSTargetKernel

/-! Exact PAIR images of the maximal-active mixed Garland seeds. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

def rxMixedTargetSlot (a b c : ℕ) :
    Fin c ⊕ (Fin b ⊕ Fin a) → PairTarget a b c
  | Sum.inl z => Sum.inr (Sum.inr z)
  | Sum.inr (Sum.inl y) => Sum.inr (Sum.inl y)
  | Sum.inr (Sum.inr x) => Sum.inl x

def ryMixedTargetSlot (a b c : ℕ) :
    Fin c ⊕ Fin b → PairTarget a b c
  | Sum.inl z => Sum.inr (Sum.inr z)
  | Sum.inr y => Sum.inr (Sum.inl y)

theorem rxMixedSeed_restriction (a b c s : ℕ) :
    pairRestriction a b c (rxMixedSeed a b c s) =
      rename (rxMixedTargetSlot a b c)
        (hsymm (Fin c ⊕ (Fin b ⊕ Fin a)) ℂ s) := by
  simp only [rxMixedSeed, pairRestriction, rename_rename]
  have hslot : pairVariable a b c ∘ rxMixedSlot a b c =
      rxMixedTargetSlot a b c := by
    funext t
    rcases t with z | (y | x) <;>
      rfl
  rw [hslot]

theorem ryMixedSeed_restriction (a b c s : ℕ) :
    pairRestriction a b c (ryMixedSeed a b c s) =
      rename (ryMixedTargetSlot a b c) (hsymm (Fin c ⊕ Fin b) ℂ s) := by
  simp only [ryMixedSeed, pairRestriction, rename_rename]
  have hslot : pairVariable a b c ∘ ryMixedSlot a b c =
      ryMixedTargetSlot a b c := by
    funext t
    rcases t with z | y <;>
      rfl
  rw [hslot]

noncomputable def rxMixedTarget (a b c s : ℕ) :
    pairTargetSymmetric a b c :=
  pairSymmetricRestriction a b c
    ⟨rxMixedSeed a b c s, rxMixedSeed_mem a b c s⟩

noncomputable def ryMixedTarget (a b c s : ℕ) :
    pairTargetSymmetric a b c :=
  pairSymmetricRestriction a b c
    ⟨ryMixedSeed a b c s, ryMixedSeed_mem a b c s⟩

theorem rxMixedTarget_polynomial (a b c s : ℕ) :
    (rxMixedTarget a b c s : MvPolynomial (PairTarget a b c) ℂ) =
      rename (rxMixedTargetSlot a b c)
        (hsymm (Fin c ⊕ (Fin b ⊕ Fin a)) ℂ s) := by
  exact rxMixedSeed_restriction a b c s

theorem ryMixedTarget_polynomial (a b c s : ℕ) :
    (ryMixedTarget a b c s : MvPolynomial (PairTarget a b c) ℂ) =
      rename (ryMixedTargetSlot a b c) (hsymm (Fin c ⊕ Fin b) ℂ s) := by
  exact ryMixedSeed_restriction a b c s

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rxMixedTarget_mem_ker_of_evaluation
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c s)
    (heval : xyzEvaluation ρ w (pairSourceShape a b c)
      (rxMixedSeed a b c s) ∈ keyPrefix ρ w m i) :
    rxMixedTarget a b c s ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c s h hi hkey)).ker := by
  apply pairTargetQuotientEvaluation_mem_ker_of_sat
    ρ w m i a b c s h hi hkey _
    ⟨rxMixedSeed a b c s, rxMixedSeed_mem a b c s⟩
  · rfl
  · exact heval

theorem ryMixedTarget_mem_ker_of_evaluation
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c s)
    (heval : xyzEvaluation ρ w (pairSourceShape a b c)
      (ryMixedSeed a b c s) ∈ keyPrefix ρ w m i) :
    ryMixedTarget a b c s ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c s h hi hkey)).ker := by
  apply pairTargetQuotientEvaluation_mem_ker_of_sat
    ρ w m i a b c s h hi hkey _
    ⟨ryMixedSeed a b c s, ryMixedSeed_mem a b c s⟩
  · rfl
  · exact heval

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rxMixedSeed_restriction
#print axioms VOA.DeligneAudit.D4Levi.ryMixedSeed_restriction
#print axioms VOA.DeligneAudit.D4Levi.rxMixedTarget_polynomial
#print axioms VOA.DeligneAudit.D4Levi.ryMixedTarget_polynomial
#print axioms VOA.DeligneAudit.D4Levi.rxMixedTarget_mem_ker_of_evaluation
#print axioms VOA.DeligneAudit.D4Levi.ryMixedTarget_mem_ker_of_evaluation
