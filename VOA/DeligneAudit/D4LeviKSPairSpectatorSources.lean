import VOA.DeligneAudit.D4LeviKSPairSpectatorPaths

/-! All recursive source conditions for the U-spectator PAIR transfer. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pairAntipode_append (F : ℕ → Module.End ℂ V)
    (xs ys : List ℕ) (A : Module.End ℂ V) :
    pairAntipode F (xs ++ ys) A =
      pairAntipode F ys (pairAntipode F xs A) := by
  induction xs generalizing A with
  | nil => rfl
  | cons r xs ih =>
      simpa only [List.cons_append, pairAntipode] using
        ih (A * F r - F r * A)

/-- At every recursive antipode stage, the source has undergone exactly
    one fewer conversion than the final XY key. -/
theorem pairXZ_spectator_sources_iter
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c deg : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c deg)
    (Q : MvPolynomial (PairXZ a b c) ℂ)
    (xs rs : List ℕ) (hlen : xs.length + rs.length = b) :
    pairTransferSources (keyPrefix ρ w m i)
      (ρ.op (17 : Fin 28))
      (pairRadicalOp ρ (uZeroWord b) w) rs
      (pairAntipode (ρ.op (17 : Fin 28)) xs
        (pairXZRecolourOperator ρ a b c 0 Q)) := by
  induction rs generalizing xs with
  | nil => trivial
  | cons r rs ih =>
      let F := ρ.op (17 : Fin 28)
      let A := pairXZRecolourOperator ρ a b c 0 Q
      have hn : xs.length + rs.length < b := by
        simp only [List.length_cons] at hlen
        omega
      have hsource :
          pairAntipode F xs A
            (pairModeWord F rs (pairRadicalOp ρ (uZeroWord b) w)) ∈
              keyPrefix ρ w m i := by
        rw [pairAntipode_eq_sign]
        exact (keyPrefix ρ w m i).smul_mem _
          (pairXZ_split_adjoint_prefix ρ w m i a b c deg
            h hi hkey Q xs rs hn)
      have hnext :
          pairTransferSources (keyPrefix ρ w m i) F
            (pairRadicalOp ρ (uZeroWord b) w) rs
            (pairAntipode F xs A * F r - F r * pairAntipode F xs A) := by
        have hlen' : (xs ++ [r]).length + rs.length = b := by
          simpa [List.length_append, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hlen
        have hh := ih (xs ++ [r]) hlen'
        simpa only [pairAntipode_append, pairAntipode] using hh
      exact ⟨hsource, hnext⟩

/-- The `pairTransferSources` hypothesis is automatic for every XZ
    coefficient and every mode list of length `b`. -/
theorem pairXZ_spectator_sources
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c deg : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c deg)
    (Q : MvPolynomial (PairXZ a b c) ℂ)
    (rs : List ℕ) (hlen : rs.length = b) :
    pairTransferSources (keyPrefix ρ w m i)
      (ρ.op (17 : Fin 28))
      (pairRadicalOp ρ (uZeroWord b) w) rs
      (pairXZRecolourOperator ρ a b c 0 Q) := by
  simpa only [pairAntipode, List.length_nil, zero_add] using
    pairXZ_spectator_sources_iter ρ w m i a b c deg h hi hkey
      Q [] rs (by simpa using hlen)

/-- All-m, all-b transfer of the U spectator across a pure XZ polynomial,
    under the stated saturation and final-key hypotheses. -/
theorem pairXZ_spectator_transfer
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c deg : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c deg)
    (Q : MvPolynomial (PairXZ a b c) ℂ)
    (rs : List ℕ) (hlen : rs.length = b) :
    (Nat.factorial b : ℂ) •
        pairXZRecolourOperator ρ a b c 0 Q
          (pairRadicalOp ρ (yModeWord rs) w) -
      pairAdjoint (ρ.op (17 : Fin 28)) rs
        (pairXZRecolourOperator ρ a b c 0 Q)
        (pairRadicalOp ρ (uZeroWord b) w) ∈
      keyPrefix ρ w m i := by
  subst b
  have hh := pairSpectator_transfer_of_sources ρ w m i h hi rs
    (pairXZRecolourOperator ρ a rs.length c 0 Q)
    (pairXZ_spectator_sources ρ w m i a rs.length c deg
      h hi hkey Q rs rfl)
  exact hh

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairAntipode_append
#print axioms VOA.DeligneAudit.D4Levi.pairXZ_spectator_sources_iter
#print axioms VOA.DeligneAudit.D4Levi.pairXZ_spectator_sources
#print axioms VOA.DeligneAudit.D4Levi.pairXZ_spectator_transfer
