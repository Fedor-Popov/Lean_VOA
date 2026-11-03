import VOA.DeligneAudit.LeviTypeA3FirstBoxGraded
import VOA.DeligneAudit.LeviTypeA2CertGradedConversion

/-! Garland vanishing for the simple currents used in the two conversions. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The coefficient of a simple lowering current vanishes above its local
Weyl weight line. Nodes two and three supply the two KS conversions. -/
theorem a3_simple_conversion_kill (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (i : Fin 3)
    (r s : ℕ) (hr : 1 ≤ r)
    (hrs : (weightABC a b c) i + 1 ≤ r + s) :
    PowerSeries.coeff s
      (VOA.DeligneAudit.LeviConversion.fCurrent
        (fun t => ρ.op (simpleF i) t) ^ r) • w = 0 := by
  let Fm : ℕ → Module.End ℂ V := fun t => ρ.op (simpleF i) t
  let Hm : ℕ → Module.End ℂ V := fun t => ρ.op (simpleH i) t
  let E1 : Module.End ℂ V := ρ.op (simpleE i) 1
  have hEF : ∀ k, E1 * Fm k - Fm k * E1 = Hm (k + 1) := by
    intro k
    apply LinearMap.ext
    intro v
    change ρ.op (simpleE i) 1 (ρ.op (simpleF i) k v) -
      ρ.op (simpleF i) k (ρ.op (simpleE i) 1 v) = _
    rw [ρ.comm]
    simp [simple_ef_table, Hm, Nat.add_comm]
  have hHF : ∀ m k, Hm (m + 1) * Fm k - Fm k * Hm (m + 1) =
      (-2 : ℂ) • Fm (m + 1 + k) := by
    intro m k
    apply LinearMap.ext
    intro v
    change ρ.op (simpleH i) (m + 1) (ρ.op (simpleF i) k v) -
      ρ.op (simpleF i) k (ρ.op (simpleH i) (m + 1) v) = _
    rw [ρ.comm]
    simp [simple_hf_table, Fm]
  have hFF : ∀ j k, Fm j * Fm k = Fm k * Fm j := by
    intro j k
    apply sub_eq_zero.mp
    apply LinearMap.ext
    intro v
    change ρ.op (simpleF i) j (ρ.op (simpleF i) k v) -
      ρ.op (simpleF i) k (ρ.op (simpleF i) j v) = 0
    rw [ρ.comm]
    simp [simple_ff_table]
  have hN : (Fm 0 ^ ((weightABC a b c) i + 1)) w = 0 := by
    simpa [Fm, Module.End.pow_apply] using h.lowering i
  have hk := VOA.DeligneAudit.Garland.garland hEF hHF hFF
    (h.raising (simpleE i) (simpleE_raising i) 1)
    (fun m => h.cartan_pos i (m + 1) (by omega))
    r hr hN s hrs
  simpa [VOA.DeligneAudit.LeviConversion.fCurrent,
    VOA.DeligneAudit.Garland.Fs, Fm] using hk

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_simple_conversion_kill
