import VOA.DeligneAudit.D4LeviKSRzOrbitEvaluation
import VOA.DeligneAudit.D4LeviKSTargetKernel

/-! The general Rz target-kernel reduction to one raw word relation. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rzSourceGenerator_prefix_of_raw
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b k l s : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ)
    (hraw : xyzEvaluation ρ w (pairSourceShape a b (k + l))
      (rzRawSourceGenerator a b k l s α β) ∈ keyPrefix ρ w m i) :
    xyzEvaluation ρ w (pairSourceShape a b (k + l))
        (rzSourceGenerator a b k l s α β) ∈ keyPrefix ρ w m i := by
  rw [rzSourceGenerator_evaluation]
  exact (keyPrefix ρ w m i).nsmul_mem hraw _

noncomputable def rzTargetGenerator (a b k l s : ℕ)
    (α : Fin b ⊕ Fin a → ℕ) (β : Fin l → ℕ) :
    pairTargetSymmetric a b (k + l) :=
  pairSymmetricRestriction a b (k + l)
    ⟨rzSourceGenerator a b k l s α β,
      rzSourceGenerator_mem a b k l s α β⟩

theorem rzTargetGenerator_polynomial (a b k l s : ℕ)
    (α : Fin b ⊕ Fin a → ℕ) (β : Fin l → ℕ) :
    (rzTargetGenerator a b k l s α β :
      MvPolynomial (PairTarget a b (k + l)) ℂ) =
      MvPolynomial.rename (rzXTarget a b (k + l))
          (rzOrbitSum _ (rzXSeed a b α)) *
        MvPolynomial.rename (fun z : Fin (k + l) =>
          (Sum.inr (Sum.inr z) : PairTarget a b (k + l)))
          (rzOrbitSum _ (rzZSeed k l s β)) := by
  exact rzSourceGenerator_restriction a b k l s α β

theorem rzTargetGenerator_mem_ker_of_raw
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b k l s deg : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b (k + l) deg)
    (hraw : xyzEvaluation ρ w (pairSourceShape a b (k + l))
      (rzRawSourceGenerator a b k l s α β) ∈ keyPrefix ρ w m i) :
    rzTargetGenerator a b k l s α β ∈
      (pairTargetQuotientEvaluation ρ w m i a b (k + l)
        (pairKernelPrefix_of_sat ρ w m i a b (k + l) deg h hi hkey)).ker := by
  apply pairTargetQuotientEvaluation_mem_ker_of_sat
    ρ w m i a b (k + l) deg h hi hkey _
    ⟨rzSourceGenerator a b k l s α β,
      rzSourceGenerator_mem a b k l s α β⟩
  · rfl
  · exact rzSourceGenerator_prefix_of_raw ρ w m i a b k l s α β hraw

/-- The sole remaining Rz bridge is the explicit evaluation of the
    complete homogeneous Z seed against the zero-mode word sum. -/
theorem rzTargetGenerator_mem_ker_of_word_bridge
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b k l s : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ) (xs zs : List ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hx : xs.length = a + b) (hz : zs.length = l)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      pairFinalKey a b (k + l) (xs.sum + zs.sum + s))
    (hbridge :
      xyzEvaluation ρ w (pairSourceShape a b (k + l))
          (rzRawSourceGenerator a b k l s α β) =
        ((yOp ρ 0) ^ b *
          ((modeAllocations (List.replicate k 0) s).map fun modes =>
            (modes.map (zOp ρ)).prod).sum) •
          (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w)) :
    rzTargetGenerator a b k l s α β ∈
      (pairTargetQuotientEvaluation ρ w m i a b (k + l)
        (pairKernelPrefix_of_sat ρ w m i a b (k + l)
          (xs.sum + zs.sum + s) h hi hkey)).ker := by
  apply rzTargetGenerator_mem_ker_of_raw ρ w m i a b k l s
    (xs.sum + zs.sum + s) α β h hi hkey
  rw [hbridge]
  apply rz_zero_pair_words_prefix ρ w m i a b (k + l) k s xs zs
    h hk hks hx _ hi hkey
  omega

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzSourceGenerator_prefix_of_raw
#print axioms VOA.DeligneAudit.D4Levi.rzTargetGenerator_polynomial
#print axioms VOA.DeligneAudit.D4Levi.rzTargetGenerator_mem_ker_of_raw
#print axioms VOA.DeligneAudit.D4Levi.rzTargetGenerator_mem_ker_of_word_bridge
