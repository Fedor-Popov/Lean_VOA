import VOA.DeligneAudit.D4LeviKSDegreeShiftAlgebra

/-! Mixed Garland generators generate target relations at later degrees. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pairTarget_mul_height_mem_shifted_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s r : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c (s + r))
    (T U : pairTargetSymmetric a b c)
    (P : pairSourceSymmetric a b c)
    (hPT : pairSymmetricRestriction a b c P = T)
    (hP : xyzEvaluation ρ w (pairSourceShape a b c) P ∈
      heightHigherOrbit ρ w m (pairFinalKey a b c s)) :
    U * T ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c (s + r) h hi hkey)).ker := by
  obtain ⟨Q, hQU⟩ := pairSymmetricRestriction_surjective a b c U
  have hheight := pairSourceSymmetric_mul_height ρ w m a b c h
    (pairFinalKey a b c s) P Q hP
  have hshift : heightHigherOrbit ρ w m (pairFinalKey a b c s) ≤
      higherOrbit ρ w m (pairFinalKey a b c (s + r)) := by
    simpa [keyShift, pairFinalKey] using
      (heightHigherOrbit_le_higher_shift ρ w m (pairFinalKey a b c s) r)
  have hprefix : xyzEvaluation ρ w (pairSourceShape a b c)
      (Q * P : pairSourceSymmetric a b c) ∈ keyPrefix ρ w m i := by
    rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
    exact hshift hheight
  apply pairTargetQuotientEvaluation_mem_ker_of_sat
    ρ w m i a b c (s + r) h hi hkey _ (Q * P)
  · rw [map_mul, hQU, hPT]
  · exact hprefix

theorem rx_gen_maximal_mul_shifted_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s r : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ a + b) (hks : m + 1 ≤ c + a + b + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c (s + r))
    (U : pairTargetSymmetric a b c) :
    U * rxMixedTarget a b c s ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c (s + r) h hi hkey)).ker := by
  exact pairTarget_mul_height_mem_shifted_ker ρ w m i a b c s r h hi hkey
    (rxMixedTarget a b c s) U
    ⟨rxMixedSeed a b c s, rxMixedSeed_mem a b c s⟩ rfl
    (rxMixedSeed_height ρ w m a b c s h hK hks)

theorem ry_gen_maximal_mul_shifted_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s r : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ b) (hks : m + 1 ≤ c + b + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c (s + r))
    (U : pairTargetSymmetric a b c) :
    U * ryMixedTarget a b c s ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c (s + r) h hi hkey)).ker := by
  exact pairTarget_mul_height_mem_shifted_ker ρ w m i a b c s r h hi hkey
    (ryMixedTarget a b c s) U
    ⟨ryMixedSeed a b c s, ryMixedSeed_mem a b c s⟩ rfl
    (ryMixedSeed_height ρ w m a b c s h hK hks)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairTarget_mul_height_mem_shifted_ker
#print axioms VOA.DeligneAudit.D4Levi.rx_gen_maximal_mul_shifted_mem_ker
#print axioms VOA.DeligneAudit.D4Levi.ry_gen_maximal_mul_shifted_mem_ker
