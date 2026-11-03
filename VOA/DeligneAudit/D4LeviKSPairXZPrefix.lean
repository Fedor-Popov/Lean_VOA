import VOA.DeligneAudit.D4LeviKSPairXZEndpoint
import VOA.DeligneAudit.D4LeviKSPairXZSource

/-! The XZ evaluation used in PAIR begins strictly above the final key. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

theorem pairXZShape_zero_x_count (a b c : ℕ) (d : PairXZ a b c →₀ ℕ) :
    (shapedModes (pairXZRecolourShape a b c 0)
      Finset.univ.toList d).countP (fun p => p.1 = 1) = a + b := by
  simp only [shapedModes, List.countP_map, Function.comp_def]
  rw [List.countP_eq_length_filter]
  simpa [Nat.add_comm] using pairXZRemainingX_length a b c 0

theorem pairXZShape_zero_y_count (a b c : ℕ) (d : PairXZ a b c →₀ ℕ) :
    (shapedModes (pairXZRecolourShape a b c 0)
      Finset.univ.toList d).countP (fun p => p.1 = 4) = 0 := by
  simp [shapedModes, List.countP_map, Function.comp_def,
    pairXZRecolourShape_zero]

theorem pairXZShape_zero_z_count (a b c : ℕ) (d : PairXZ a b c →₀ ℕ) :
    (shapedModes (pairXZRecolourShape a b c 0)
      Finset.univ.toList d).countP (fun p => p.1 = 5) = c := by
  classical
  simp only [shapedModes, List.countP_map, Function.comp_def]
  rw [List.countP_eq_length_filter]
  have hn : (Finset.univ.toList.filter fun t : PairXZ a b c =>
      pairXZRecolourShape a b c 0 t = 5).Nodup :=
    (Finset.nodup_toList _).filter _
  have heq : (Finset.univ.toList.filter fun t : PairXZ a b c =>
      pairXZRecolourShape a b c 0 t = 5).toFinset =
      Finset.univ.filter fun t => pairXZRecolourShape a b c 0 t = 5 := by
    ext t
    simp
  calc
    _ = (Finset.univ.toList.filter fun t : PairXZ a b c =>
        pairXZRecolourShape a b c 0 t = 5).toFinset.card :=
          (List.toFinset_card_of_nodup hn).symm
    _ = (Finset.univ.filter fun t : PairXZ a b c =>
        pairXZRecolourShape a b c 0 t = 5).card := by rw [heq]
    _ = ∑ t : PairXZ a b c,
        if pairXZRecolourShape a b c 0 t = 5 then 1 else 0 := by
          exact (Finset.sum_boole
            (fun t : PairXZ a b c => pairXZRecolourShape a b c 0 t = 5)
            Finset.univ).symm
    _ = c := by
          rw [Fintype.sum_sum_type]
          simp [pairXZRecolourShape, pairRecolourShape, pairXZSource]

theorem pairXZShape_zero_e_count (a b c : ℕ) (d : PairXZ a b c →₀ ℕ) :
    (shapedModes (pairXZRecolourShape a b c 0)
      Finset.univ.toList d).countP (fun p => p.1 = 0) = 0 := by
  simp [shapedModes, List.countP_map, Function.comp_def,
    pairXZRecolourShape_zero]

theorem pairXZShape_zero_higher (m a b c deg : ℕ) (hb : 0 < b)
    (d : PairXZ a b c →₀ ℕ) :
    keyLess m (pairFinalKey a b c deg)
      (wordKey (shapedModes (pairXZRecolourShape a b c 0)
        Finset.univ.toList d)) := by
  left
  simp only [keyHeight, pairFinalKey, wordKey]
  rw [pairXZShape_zero_x_count, pairXZShape_zero_y_count,
    pairXZShape_zero_z_count, pairXZShape_zero_e_count]
  omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Every pure XZ polynomial is a source in the higher prefix when the
    final symmetric key contains at least one Y letter. -/
theorem pairXZPolynomial_prefix
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c deg : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c deg)
    (hb : 0 < b) (Q : MvPolynomial (PairXZ a b c) ℂ) :
    pairXZRecolourOperator ρ a b c 0 Q w ∈ keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  rw [pairXZRecolourOperator_apply]
  induction Q using MvPolynomial.induction_on' with
  | monomial d z =>
      have hm : (monomial d z : MvPolynomial (PairXZ a b c) ℂ) =
          z • modeMonomial (PairXZ a b c) d := by
        simp [modeMonomial, smul_monomial]
      rw [hm, map_smul]
      apply (higherOrbit ρ w m (pairFinalKey a b c deg)).smul_mem
      rw [xyzEvaluation, modeWordEvaluation_monomial]
      exact keyOrbit_le_higher ρ w m _ _
        (pairXZShape_zero_higher m a b c deg hb d)
        (keyLayer_le_orbit ρ w _
          (radicalWord_mem_key ρ w _))
  | add P Q ihP ihQ =>
      simpa only [map_add] using
        (higherOrbit ρ w m (pairFinalKey a b c deg)).add_mem ihP ihQ

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairXZShape_zero_x_count
#print axioms VOA.DeligneAudit.D4Levi.pairXZShape_zero_y_count
#print axioms VOA.DeligneAudit.D4Levi.pairXZShape_zero_z_count
#print axioms VOA.DeligneAudit.D4Levi.pairXZShape_zero_e_count
#print axioms VOA.DeligneAudit.D4Levi.pairXZShape_zero_higher
#print axioms VOA.DeligneAudit.D4Levi.pairXZPolynomial_prefix
