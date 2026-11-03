import VOA.DeligneAudit.A3SectorSl2Table
import VOA.DeligneAudit.A3SectorFinite

/-! Garland gives the three simple-root mode cutoffs at every weight. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

private theorem simple_ef_comm (i : Fin 3) (k : ℕ) :
    ρ.op (simpleE i) 1 * ρ.op (simpleF i) k -
      ρ.op (simpleF i) k * ρ.op (simpleE i) 1 =
        ρ.op (simpleH i) (k + 1) := by
  apply LinearMap.ext
  intro v
  change ρ.op (simpleE i) 1 (ρ.op (simpleF i) k v) -
    ρ.op (simpleF i) k (ρ.op (simpleE i) 1 v) = _
  rw [ρ.comm]
  simp [simple_ef_table, Nat.add_comm]

private theorem simple_hf_comm (i : Fin 3) (m k : ℕ) :
    ρ.op (simpleH i) (m + 1) * ρ.op (simpleF i) k -
      ρ.op (simpleF i) k * ρ.op (simpleH i) (m + 1) =
        (-2 : ℂ) • ρ.op (simpleF i) (m + 1 + k) := by
  apply LinearMap.ext
  intro v
  change ρ.op (simpleH i) (m + 1) (ρ.op (simpleF i) k v) -
    ρ.op (simpleF i) k (ρ.op (simpleH i) (m + 1) v) = _
  rw [ρ.comm]
  simp [simple_hf_table]

private theorem simple_ff_comm (i : Fin 3) (r s : ℕ) :
    ρ.op (simpleF i) r * ρ.op (simpleF i) s =
      ρ.op (simpleF i) s * ρ.op (simpleF i) r := by
  apply LinearMap.ext
  intro v
  have h := ρ.comm (simpleF i) (simpleF i) r s v
  simp only [simple_ff_table, zero_smul, Finset.sum_const_zero] at h
  exact sub_eq_zero.mp h

/-- At every simple node, modes at or above the fundamental-weight
coefficient kill the local Weyl generator. -/
theorem simple_mode_zero (w : V) (weight : Fin 3 → ℕ)
    (h : LocalWeylRel ρ w weight) (i : Fin 3) (s : ℕ)
    (hs : weight i ≤ s) : ρ.op (simpleF i) s w = 0 := by
  let Fm : ℕ → Module.End ℂ V := fun r => ρ.op (simpleF i) r
  let Hm : ℕ → Module.End ℂ V := fun r => ρ.op (simpleH i) r
  let E1 : Module.End ℂ V := ρ.op (simpleE i) 1
  have hEF : ∀ k, E1 * Fm k - Fm k * E1 = Hm (k + 1) :=
    fun k => simple_ef_comm ρ i k
  have hHF : ∀ m k, Hm (m + 1) * Fm k - Fm k * Hm (m + 1) =
      (-2 : ℂ) • Fm (m + 1 + k) := fun m k => simple_hf_comm ρ i m k
  have hFF : ∀ r t, Fm r * Fm t = Fm t * Fm r :=
    fun r t => simple_ff_comm ρ i r t
  have hE : E1 w = 0 := h.raising (simpleE i) (simpleE_raising i) 1
  have hH : ∀ m, Hm (m + 1) w = 0 :=
    fun m => h.cartan_pos i (m + 1) (by omega)
  have hN : (Fm 0 ^ (weight i + 1)) w = 0 := by
    simpa only [Module.End.pow_apply] using h.lowering i
  have hg := VOA.DeligneAudit.Garland.garland hEF hHF hFF hE hH
    1 (by omega) hN s (by omega)
  simpa [VOA.DeligneAudit.Garland.Fs, Fm] using hg

/-- Every fixed node-1 radical depth is finite for an arbitrary local Weyl
weight `(a,b,c)`. -/
theorem radical_layer_finite_of_localWeyl (w : V) (weight : Fin 3 → ℕ)
    (h : LocalWeylRel ρ w weight) (j : ℕ) :
    FiniteDimensional ℂ (LeviTypeA.radicalLayer (radicalOp ρ) w j) := by
  apply radical_layer_finite ρ w (weight 0) (weight 1) (weight 2) j
  · exact simple_mode_zero ρ w weight h 0
  · exact simple_mode_zero ρ w weight h 1
  · exact simple_mode_zero ρ w weight h 2

#print axioms simple_mode_zero
#print axioms radical_layer_finite_of_localWeyl

end VOA.DeligneAudit.A3Sector
