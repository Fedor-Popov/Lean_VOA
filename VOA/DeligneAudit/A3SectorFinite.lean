import VOA.DeligneAudit.A3SectorBasic
import VOA.DeligneAudit.LeviTypeAFinite

/-!
The node-1 radical layer is finite once the three simple-root cutoff
relations have been supplied.  The cutoffs are the remaining sl₂ input.
-/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The three radical colours as endomorphisms. -/
def radicalOp (ρ : CurrentModule bracketTable V) (i : Fin 3) (s : ℕ) : Module.End ℂ V :=
  ρ.op (F i) s

/-- High modes of the radical letters kill the cyclic vector. -/
theorem radical_mode_zero (ρ : CurrentModule bracketTable V) (w : V)
    (a b c : ℕ)
    (h₀ : ∀ s, a ≤ s → ρ.op (simpleF 0) s w = 0)
    (h₁ : ∀ s, b ≤ s → ρ.op (simpleF 1) s w = 0)
    (h₂ : ∀ s, c ≤ s → ρ.op (simpleF 2) s w = 0)
    (i : Fin 3) (s : ℕ) :
    (if i = 0 then a else if i = 1 then a + b else a + b + c) ≤ s →
      ρ.op (F i) s w = 0 := by
  have hmid (t : ℕ) (ht : a + b ≤ t) : ρ.op (F 1) t w = 0 := by
    have hprev : a ≤ t - b := by omega
    have hz₀ : ρ.op (F 0) (t - b) w = 0 := by
      simpa [simpleF_zero] using h₀ (t - b) hprev
    have hz₁ : ρ.op (leviF 0) b w = 0 := by
      simpa [simpleF_levi_one] using h₁ b (le_refl b)
    have hbr := levi_comm_one ρ b (t - b) w
    simpa [hz₀, hz₁, Nat.add_sub_of_le (by omega : b ≤ t)] using hbr.symm
  intro hs
  fin_cases i
  · exact h₀ s (by simpa [F, simpleF] using hs)
  · exact hmid s (by simpa using hs)
  · have hs' : a + b + c ≤ s := by simpa using hs
    have hprev : a + b ≤ s - c := by omega
    have hz₂ : ρ.op (leviF 1) c w = 0 := by
      simpa [simpleF_levi_two] using h₂ c (le_refl c)
    have hbr := levi_comm_two ρ c (s - c) w
    simpa [hmid (s - c) hprev, hz₂,
      Nat.add_sub_of_le (by omega : c ≤ s)] using hbr.symm

/-- The radical current operators commute as elements of the endomorphism ring. -/
theorem radicalOp_comm (ρ : CurrentModule bracketTable V)
    (i : Fin 3) (s : ℕ) (j : Fin 3) (t : ℕ) :
    radicalOp ρ i s * radicalOp ρ j t =
      radicalOp ρ j t * radicalOp ρ i s := by
  apply LinearMap.ext
  intro v
  exact sub_eq_zero.mp (radical_comm ρ i j s t v)

/-- Every fixed radical-letter depth is finite-dimensional. -/
theorem radical_layer_finite (ρ : CurrentModule bracketTable V) (w : V)
    (a b c j : ℕ)
    (h₀ : ∀ s, a ≤ s → ρ.op (simpleF 0) s w = 0)
    (h₁ : ∀ s, b ≤ s → ρ.op (simpleF 1) s w = 0)
    (h₂ : ∀ s, c ≤ s → ρ.op (simpleF 2) s w = 0) :
    FiniteDimensional ℂ (LeviTypeA.radicalLayer (radicalOp ρ) w j) := by
  apply LeviTypeA.radicalLayer_finite (B := a + b + c) (radicalOp ρ) w
  · exact radicalOp_comm ρ
  · intro i s hs
    apply radical_mode_zero ρ w a b c h₀ h₁ h₂ i s
    fin_cases i <;> simp_all <;> omega

#print axioms radical_mode_zero
#print axioms radicalOp_comm
#print axioms radical_layer_finite

end VOA.DeligneAudit.A3Sector
