import VOA.DeligneAudit.D4LeviKSMixedMaximalKernel
import VOA.DeligneAudit.D4LeviKSTargetKernelIdeal

/-! Separately symmetric target factors preserve the maximal mixed relations. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rx_gen_maximal_mul_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ a + b) (hks : m + 1 ≤ c + a + b + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c s)
    (U : pairTargetSymmetric a b c) :
    U * rxMixedTarget a b c s ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c s h hi hkey)).ker := by
  exact pairTargetQuotientEvaluation_mul_mem_ker ρ w m i a b c h hi
    (pairKernelPrefix_of_sat ρ w m i a b c s h hi hkey)
    (rxMixedTarget a b c s) U
    (rx_gen_maximal_mem_ker ρ w m i a b c s h hK hks hi hkey)

theorem ry_gen_maximal_mul_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ b) (hks : m + 1 ≤ c + b + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c s)
    (U : pairTargetSymmetric a b c) :
    U * ryMixedTarget a b c s ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c s h hi hkey)).ker := by
  exact pairTargetQuotientEvaluation_mul_mem_ker ρ w m i a b c h hi
    (pairKernelPrefix_of_sat ρ w m i a b c s h hi hkey)
    (ryMixedTarget a b c s) U
    (ry_gen_maximal_mem_ker ρ w m i a b c s h hK hks hi hkey)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rx_gen_maximal_mul_mem_ker
#print axioms VOA.DeligneAudit.D4Levi.ry_gen_maximal_mul_mem_ker
