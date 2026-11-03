import VOA.DeligneAudit.D4LeviKSRzShiftedKernel
import VOA.DeligneAudit.D4LeviKSRzOrbitSpanAlgebra
import VOA.DeligneAudit.D4LeviKSTargetSymmetricEmbeds

/-! The maximal Rz orbit relation is the complete homogeneous Z generator. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

noncomputable def rzMaximalTarget (a b c s : ℕ) :
    pairTargetSymmetric a b c :=
  pairSymmetricRestriction a b c
    ⟨rzSourceGenerator a b c 0 s (fun _ => 0) (fun z : Fin 0 => z.elim0),
      rzSourceGenerator_mem a b c 0 s (fun _ => 0) (fun z : Fin 0 => z.elim0)⟩

theorem rzMaximalTarget_polynomial (a b c s : ℕ) :
    (rzMaximalTarget a b c s : MvPolynomial (PairTarget a b c) ℂ) =
      ((Nat.card (Equiv.Perm (Fin b ⊕ Fin a)) *
        Nat.card (Equiv.Perm (Fin c)) : ℕ) : ℂ) •
        rename (fun z : Fin c =>
          (Sum.inr (Sum.inr z) : PairTarget a b c))
          (hsymm (Fin c) ℂ s) := by
  classical
  change (rzTargetGenerator a b c 0 s (fun _ => 0)
    (fun z : Fin 0 => z.elim0) :
      MvPolynomial (PairTarget a b c) ℂ) = _
  rw [rzTargetGenerator_polynomial]
  have hx : rzXSeed a b (fun _ => 0) = 1 := by
    simp [rzXSeed]
  have hz : rzZSeed c 0 s (fun z : Fin 0 => z.elim0) =
      hsymm (Fin c) ℂ s := by
    simp [rzZSeed]
  rw [hx, hz]
  rw [rzOrbitSum_eq_card_smul_of_symmetric _ 1 (by simp)]
  simp only [Nat.add_zero]
  rw [rzOrbitSum_eq_card_smul_of_symmetric _ (hsymm (Fin c) ℂ s)
    (hsymm_isSymmetric (Fin c) ℂ s)]
  simp [map_smul, smul_smul, mul_comm]

noncomputable def rzFullHSymm (a b c s : ℕ) :
    pairTargetSymmetric a b c :=
  ⟨rename (fun z : Fin c =>
      (Sum.inr (Sum.inr z) : PairTarget a b c))
      (hsymm (Fin c) ℂ s),
    pairTarget_symmetric_Z_mem a b c (hsymm (Fin c) ℂ s)
      (hsymm_isSymmetric (Fin c) ℂ s)⟩

theorem rzMaximalTarget_eq_smul_hsymm (a b c s : ℕ) :
    rzMaximalTarget a b c s =
      ((Nat.card (Equiv.Perm (Fin b ⊕ Fin a)) *
        Nat.card (Equiv.Perm (Fin c)) : ℕ) : ℂ) •
        rzFullHSymm a b c s := by
  apply Subtype.ext
  simpa [rzFullHSymm] using rzMaximalTarget_polynomial a b c s

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rzMaximalTarget_mul_shifted_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s r : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hc : 1 ≤ c) (hks : m + 1 ≤ c + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c (s + r))
    (U : pairTargetSymmetric a b c) :
    U * rzMaximalTarget a b c s ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c (s + r) h hi hkey)).ker := by
  simpa only [rzMaximalTarget, add_zero] using
    rzTargetGenerator_mul_shifted_mem_ker ρ w m i a b c 0 s r
      (fun _ => 0) (fun z : Fin 0 => z.elim0)
      h hc hks hi (by simpa using hkey) U

theorem rzFullHSymm_mul_shifted_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s r : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hc : 1 ≤ c) (hks : m + 1 ≤ c + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c (s + r))
    (U : pairTargetSymmetric a b c) :
    U * rzFullHSymm a b c s ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c (s + r) h hi hkey)).ker := by
  let C : ℂ := (Nat.card (Equiv.Perm (Fin b ⊕ Fin a)) *
    Nat.card (Equiv.Perm (Fin c)) : ℕ)
  have hC : C ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero
      (Nat.ne_of_gt Nat.card_pos) (Nat.ne_of_gt Nat.card_pos))
  have hrel := rzMaximalTarget_mul_shifted_mem_ker ρ w m i a b c s r
    h hc hks hi hkey U
  rw [rzMaximalTarget_eq_smul_hsymm] at hrel
  have hsmul : C • (U * rzFullHSymm a b c s) ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c (s + r) h hi hkey)).ker := by
    simpa only [C, mul_smul_comm] using hrel
  exact (Submodule.smul_mem_iff _ hC).mp hsmul

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzMaximalTarget_mul_shifted_mem_ker
#print axioms VOA.DeligneAudit.D4Levi.rzMaximalTarget_polynomial
#print axioms VOA.DeligneAudit.D4Levi.rzMaximalTarget_eq_smul_hsymm
#print axioms VOA.DeligneAudit.D4Levi.rzFullHSymm_mul_shifted_mem_ker
