import VOA.DeligneAudit.SL4TRadicalGrassmannianPowerSums

/-! Corrected Garland relations on the Grassmannian image in the first Levi quotient. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.CVsl2

/-- Either simple-root current triple of the rank-two Levi satisfies the rank-one table. -/
theorem leviSimple_currentRelations {W : Type} [AddCommGroup W] [Module ℂ W]
    (Q : CurrentModule VOA.AffineSl3.bracketTable W) (i : Fin 2) :
    SL2 (fun s => Q.op (if i = 0 then 0 else 1) s)
      (fun s => Q.op (if i = 0 then 6 else 7) s)
      (fun s => Q.op (if i = 0 then 3 else 4) s) := by
  by_cases hi : i = 0 <;> simp only [hi, if_true, if_false] <;>
    refine ⟨fun s k => ?_, fun s k => ?_, fun s k => ?_,
      fun s k => ?_, fun s k => ?_⟩
  all_goals
    first
    | (rw [op_comm_end]; simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable])
    | (apply sub_eq_zero.mp; rw [op_comm_end]
       simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable])

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))

/-- The first Levi evaluator considered in its ambient quotient current module. -/
def radicalGrassmannianAmbientEvaluation (d : Fin 3 → ℕ) :
    RadicalGrassmannianRing a b c d →ₗ[ℂ] V ⧸ higherRadicalCountClosure ρ w d :=
  (radicalCountMultiplicity ρ w d).subtype.comp
    (radicalGrassmannianEvaluation ρ w a b c h d)

/-- The two Levi Cartan symbols are differences of adjacent Grassmannian power sums. -/
def radicalLeviPowerSum (d : Fin 3 → ℕ) (i : Fin 2) (s : ℕ) :
    RadicalGrassmannianRing a b c d :=
  if i = 0 then
    radicalGrassmannianPowerSum a b c d 0 s - radicalGrassmannianPowerSum a b c d 1 s
  else
    radicalGrassmannianPowerSum a b c d 1 s - radicalGrassmannianPowerSum a b c d 2 s

/-- The adjacent-alphabet Cartan identities descend to the merged Levi quotient. -/
theorem radicalCountQuot_cartan_difference (d : Fin 3 → ℕ) (s : ℕ) :
    (radicalCountQuotCurrent ρ w d).op 6 s =
        radicalAlphabetQuotCurrent ρ w a b c h d 0 s -
          radicalAlphabetQuotCurrent ρ w a b c h d 1 s ∧
      (radicalCountQuotCurrent ρ w d).op 7 s =
        radicalAlphabetQuotCurrent ρ w a b c h d 1 s -
          radicalAlphabetQuotCurrent ρ w a b c h d 2 s := by
  constructor
  · apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := (higherRadicalCountClosure ρ w d).mkQ_surjective x
    change (higherRadicalCountClosure ρ w d).mkQ (ρ.op 13 s v) = _
    rw [(leviCartan_eq_alphabet_difference ρ s).1, LinearMap.sub_apply, map_sub]
    rfl
  · apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := (higherRadicalCountClosure ρ w d).mkQ_surjective x
    change (higherRadicalCountClosure ρ w d).mkQ (ρ.op 14 s v) = _
    rw [(leviCartan_eq_alphabet_difference ρ s).2, LinearMap.sub_apply, map_sub]
    rfl

/-- Every Grassmannian source vector is a highest vector for both Levi simple roots. -/
theorem radicalGrassmannianAmbientEvaluation_raising (d : Fin 3 → ℕ)
    (i : Fin 2) (s : ℕ) (φ : RadicalGrassmannianRing a b c d) :
    (radicalCountQuotCurrent ρ w d).op (if i = 0 then 0 else 1) s
      (radicalGrassmannianAmbientEvaluation ρ w a b c h d φ) = 0 := by
  obtain ⟨v, hv, he⟩ := (radicalGrassmannianEvaluation ρ w a b c h d φ).property
  change (radicalCountQuotCurrent ρ w d).op _ s
    (radicalGrassmannianEvaluation ρ w a b c h d φ).val = 0
  rw [← he]
  fin_cases i
  · exact radicalCountQuot_raising ρ w a b c h d 0 s hv
  · exact radicalCountQuot_raising ρ w a b c h d 2 s hv

set_option synthInstance.maxHeartbeats 100000 in
-- Nested tensor-product ring instances exceed the default synthesis budget during rewriting.
/-- Positive Levi Cartan currents are the relative-alphabet power sums on the source. -/
theorem radicalGrassmannianAmbientEvaluation_cartan (d : Fin 3 → ℕ)
    (i : Fin 2) (s : ℕ) (hs : 1 ≤ s) (φ : RadicalGrassmannianRing a b c d) :
    (radicalCountQuotCurrent ρ w d).op (if i = 0 then 6 else 7) s
      (radicalGrassmannianAmbientEvaluation ρ w a b c h d φ) =
        radicalGrassmannianAmbientEvaluation ρ w a b c h d
          (radicalLeviPowerSum a b c d i s * φ) := by
  obtain ⟨hfirst, hlast⟩ := radicalCountQuot_cartan_difference ρ w a b c h d s
  by_cases hi : i = 0
  · simp only [hi, if_true, radicalLeviPowerSum]
    rw [hfirst]
    simp only [LinearMap.sub_apply, radicalGrassmannianAmbientEvaluation,
      LinearMap.comp_apply, Submodule.subtype_apply,
      sub_mul, map_sub]
    rw [radicalGrassmannianEvaluation_powerSum ρ w a b c h d 0 s hs,
      radicalGrassmannianEvaluation_powerSum ρ w a b c h d 1 s hs]
  · simp only [hi, if_false, radicalLeviPowerSum]
    rw [hlast]
    simp only [LinearMap.sub_apply, radicalGrassmannianAmbientEvaluation,
      LinearMap.comp_apply, Submodule.subtype_apply,
      sub_mul, map_sub]
    rw [radicalGrassmannianEvaluation_powerSum ρ w a b c h d 1 s hs,
      radicalGrassmannianEvaluation_powerSum ρ w a b c h d 2 s hs]

/-- Sharp lowering nilpotence holds at every vector in the Grassmannian image. -/
theorem radicalGrassmannianAmbientEvaluation_lowering (d : Fin 3 → ℕ) (i : Fin 2)
    (hm : 0 ≤ a3KeyLabelInt b c i ⟨d 0, d 1, d 2, 0⟩)
    (φ : RadicalGrassmannianRing a b c d) :
    ((radicalCountQuotCurrent ρ w d).op (if i = 0 then 3 else 4) 0 ^
      ((a3KeyLabelInt b c i ⟨d 0, d 1, d 2, 0⟩).toNat + 1))
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d φ) = 0 := by
  obtain ⟨v, hv, he⟩ := (radicalGrassmannianEvaluation ρ w a b c h d φ).property
  change ((radicalCountQuotCurrent ρ w d).op _ 0 ^ _)
    (radicalGrassmannianEvaluation ρ w a b c h d φ).val = 0
  rw [← he, Module.End.pow_apply]
  exact (radicalCountQuot_lowering_sharp ρ w a b c h d i hv).2 hm

/-- Full corrected Garland coefficients vanish at all first Levi multiplicity vectors. -/
theorem radicalGrassmannianAmbientEvaluation_garland (d : Fin 3 → ℕ) (i : Fin 2)
    (hm : 0 ≤ a3KeyLabelInt b c i ⟨d 0, d 1, d 2, 0⟩)
    (k s : ℕ) (hk : 1 ≤ k)
    (hs : (a3KeyLabelInt b c i ⟨d 0, d 1, d 2, 0⟩).toNat + 1 ≤ k + s)
    (φ : RadicalGrassmannianRing a b c d) :
    (PowerSeries.coeff s
      (Garland.Fs (fun t => (radicalCountQuotCurrent ρ w d).op
        (if i = 0 then 3 else 4) t) ^ k *
        newtonSeries (fun t => (radicalCountQuotCurrent ρ w d).op
          (if i = 0 then 6 else 7) t)))
      (radicalGrassmannianAmbientEvaluation ρ w a b c h d φ) = 0 :=
  garland_pi_coeff (leviSimple_currentRelations (radicalCountQuotCurrent ρ w d) i)
    (radicalGrassmannianAmbientEvaluation ρ w a b c h d) (radicalLeviPowerSum a b c d i)
    (radicalGrassmannianAmbientEvaluation_raising ρ w a b c h d i)
    (radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d i)
    _ (radicalGrassmannianAmbientEvaluation_lowering ρ w a b c h d i hm) k s hk hs φ

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.leviSimple_currentRelations
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_cartan_difference
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_raising
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_cartan
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_lowering
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_garland
