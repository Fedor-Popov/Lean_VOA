import VOA.DeligneAudit.D4LevelReductionAdjointHighest
import VOA.DeligneAudit.SL4TMixedLabelRank

/-! Transfer of the mixed truncated sl₄ bound to quotients of D4 adjoint-key vectors. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- Highest-weight integrability gives the sharp simple lowering powers on the edge. -/
theorem adjointKey_simple_lower_sharp (a b d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b) 0))
    (i : Fin 3) {v : V} (hv : v ∈ keyLayer ρ w (adjointLetterKey a d)) :
    ((leviCurrent ρ).op (A3Sector.simpleF i) 0)^[A3Sector.weightABC a b a i + 1] v = 0 := by
  let Q := leviCurrent ρ
  let E := Q.op (A3Sector.simpleE i) 0
  let F := Q.op (A3Sector.simpleF i) 0
  let H := Q.op (A3Sector.simpleH i) 0
  have hEF : ∀ u, E (F u) - F (E u) = H u := by
    intro u
    dsimp [E, F, H]
    rw [Q.comm]
    simp [A3Sector.simple_ef_table]
  have hHF : ∀ u, H (F u) - F (H u) = (-2 : ℂ) • F u := by
    intro u
    dsimp [E, F, H]
    rw [Q.comm]
    simp [A3Sector.simple_hf_table]
  have he : E v = 0 := adjointKey_all_raise_zero ρ w (a + b) a d h hv
    (A3Sector.simpleE i) (by fin_cases i <;> decide) 0
  have hh' : H v = (((A3Sector.weightABC a b a i : ℕ) : ℤ) : ℂ) • v := by
    simpa using adjointKey_cartan_weight ρ w a b d h i hv
  let K := lowerBaseExponent (a + b) i + 2 * keyDepth (adjointLetterKey a d)
  have hn : F^[K] v = 0 := by
    rw [← Module.End.pow_apply]
    exact key_simple_lower_nil_levi ρ w (a + b) h i (adjointLetterKey a d) hv
  have hs := (CLFilt.hw_pow E F H hEF hHF he hh' K hn).2 (Int.natCast_nonneg _)
  simpa only [Int.toNat_natCast] using hs

/-- An invariant quotient killing positive Cartan modes has the edge local Weyl relations. -/
theorem adjointKey_localWeyl_quotient (a b d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b) 0)) (N : Submodule ℂ V)
    (hN : ∀ e r, N ≤ N.comap ((leviCurrent ρ).op e r))
    {v : V} (hv : v ∈ keyLayer ρ w (adjointLetterKey a d))
    (hpos : ∀ i s, 0 < s → (leviCurrent ρ).op (A3Sector.simpleH i) s v ∈ N) :
    A3Sector.LocalWeylRel (quotRepG (leviCurrent ρ) N hN) (N.mkQ v)
      (A3Sector.weightABC a b a) := by
  let Q := quotRepG (leviCurrent ρ) N hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he r
    change N.mkQ ((leviCurrent ρ).op e r v) = 0
    rw [adjointKey_all_raise_zero ρ w (a + b) a d h hv e he r, map_zero]
  · intro i r hr
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hpos i r hr)
  · intro i
    change N.mkQ ((leviCurrent ρ).op (A3Sector.simpleH i) 0 v) = _
    rw [adjointKey_cartan_weight ρ w a b d h i hv, map_smul]
  · intro i
    have hiter : ∀ n (u : V), (Q.op (A3Sector.simpleF i) 0)^[n] (N.mkQ u) =
        N.mkQ (((leviCurrent ρ).op (A3Sector.simpleF i) 0)^[n] u) := by
      intro n
      induction n with
      | zero => intro u; rfl
      | succ n ih =>
          intro u
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
          rfl
    change (Q.op (A3Sector.simpleF i) 0)^[A3Sector.weightABC a b a i + 1] (N.mkQ v) = 0
    rw [hiter, adjointKey_simple_lower_sharp ρ w a b d h i hv, map_zero]

/-- The proved mixed sl₄ bound applies to each edge cyclic quotient with the required cutoff. -/
theorem adjointKey_truncated_quotient_rank_le (a b d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b) 0)) (N : Submodule ℂ V)
    (hN : ∀ e r, N ≤ N.comap ((leviCurrent ρ).op e r))
    {v : V} (hv : v ∈ keyLayer ρ w (adjointLetterKey a d))
    (hpos : ∀ i s, 0 < s → (leviCurrent ρ).op (A3Sector.simpleH i) s v ∈ N)
    (hhigh : ∀ e s, a + b ≤ s → (leviCurrent ρ).op e s v ∈ N) :
    FiniteDimensional ℂ (cycSubG (quotRepG (leviCurrent ρ) N hN) (N.mkQ v)) ∧
      Module.finrank ℂ (cycSubG (quotRepG (leviCurrent ρ) N hN) (N.mkQ v)) ≤
        15 ^ a * 6 ^ b := by
  apply (SL4T.mixedLabelTruncatedRank_iff_cyclic.mp SL4T.mixedLabelTruncatedRank)
    a b _ (quotRepG (leviCurrent ρ) N hN) (N.mkQ v)
    (adjointKey_localWeyl_quotient ρ w a b d h N hN hv hpos)
  intro e s hs
  exact (Submodule.Quotient.mk_eq_zero N).mpr (hhigh e s hs)

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_simple_lower_sharp
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_localWeyl_quotient
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_truncated_quotient_rank_le
