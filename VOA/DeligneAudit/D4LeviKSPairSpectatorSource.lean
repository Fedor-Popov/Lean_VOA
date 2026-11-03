import VOA.DeligneAudit.D4LeviKSPairSpectatorTransfer

/-! Initial higher-key source for the U-spectator transfer. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

/-- Appending zero-mode U letters does not change the height of an XZ word.
    The final XY key is lower by two for each expected Y letter. -/
theorem pairXZ_uZero_source_higher (m a b c deg : ℕ) (hb : 0 < b)
    (d : PairXZ a b c →₀ ℕ) :
    keyLess m (pairFinalKey a b c deg)
      (wordKey (shapedModes (pairXZRecolourShape a b c 0)
        Finset.univ.toList d ++ uZeroWord b)) := by
  left
  simp only [keyHeight, pairFinalKey, wordKey, List.countP_append]
  rw [pairXZShape_zero_x_count, pairXZShape_zero_y_count,
    pairXZShape_zero_z_count, pairXZShape_zero_e_count]
  simp [uZeroWord, List.countP_replicate]
  omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A pure XZ polynomial followed by the full U spectator begins above
    the final symmetric key. -/
theorem pairXZ_uZero_source_prefix
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c deg : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c deg)
    (hb : 0 < b) (Q : MvPolynomial (PairXZ a b c) ℂ) :
    pairXZRecolourOperator ρ a b c 0 Q
        (pairRadicalOp ρ (uZeroWord b) w) ∈
      keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  induction Q using MvPolynomial.induction_on' with
  | monomial d z =>
      have hm : (monomial d z : MvPolynomial (PairXZ a b c) ℂ) =
          z • modeMonomial (PairXZ a b c) d := by
        simp [modeMonomial, smul_monomial]
      rw [hm, map_smul, LinearMap.smul_apply]
      apply (higherOrbit ρ w m (pairFinalKey a b c deg)).smul_mem
      change pairWordOpEvaluation ρ
          (pairPolynomialWords (pairXZRecolourShape a b c 0)
            (modeMonomial (PairXZ a b c) d))
          (pairRadicalOp ρ (uZeroWord b) w) ∈ _
      rw [pairPolynomialWords_monomial, pairWordOpEvaluation_single]
      rw [← Module.End.mul_apply, ← pairRadicalOp_append,
        pairRadicalOp_apply]
      exact keyOrbit_le_higher ρ w m _ _
        (pairXZ_uZero_source_higher m a b c deg hb d)
        (keyLayer_le_orbit ρ w _ (radicalWord_mem_key ρ w _))
  | add P Q ihP ihQ =>
      simpa only [map_add, LinearMap.add_apply] using
        (higherOrbit ρ w m (pairFinalKey a b c deg)).add_mem ihP ihQ

/-- The complete single-mode spectator transfer for a Y multiplicity of
    one, with its higher-key source discharged. -/
theorem pairXZ_one_spectator_transfer
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a c deg r : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a 1 c deg)
    (Q : MvPolynomial (PairXZ a 1 c) ℂ) :
    pairXZRecolourOperator ρ a 1 c 0 Q
        (pairRadicalOp ρ (yModeWord [r]) w) -
      pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairXZRecolourOperator ρ a 1 c 0 Q)
        (pairRadicalOp ρ (uZeroWord 1) w) ∈
      keyPrefix ρ w m i := by
  have hsource : pairTransferSources (keyPrefix ρ w m i)
      (ρ.op (17 : Fin 28))
      (pairRadicalOp ρ (uZeroWord 1) w) [r]
      (pairXZRecolourOperator ρ a 1 c 0 Q) := by
    change pairXZRecolourOperator ρ a 1 c 0 Q
        (pairRadicalOp ρ (uZeroWord 1) w) ∈
          keyPrefix ρ w m i ∧ True
    exact ⟨pairXZ_uZero_source_prefix ρ w m i a 1 c deg h hi
      hkey (by omega) Q, trivial⟩
  simpa using pairSpectator_transfer_of_sources ρ w m i h hi [r]
    (pairXZRecolourOperator ρ a 1 c 0 Q) hsource

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairXZ_uZero_source_higher
#print axioms VOA.DeligneAudit.D4Levi.pairXZ_uZero_source_prefix
#print axioms VOA.DeligneAudit.D4Levi.pairXZ_one_spectator_transfer
