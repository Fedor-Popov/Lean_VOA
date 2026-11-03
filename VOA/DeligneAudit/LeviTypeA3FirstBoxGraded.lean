import VOA.DeligneAudit.LeviTypeA3TerminalFinite
import VOA.DeligneAudit.LeviTypeA2CertSpectatorBoxGraded

/-! The node-one graded Garland box with arbitrary commuting radical spectators. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_first_comm (i j : ℕ) :
    ρ.op (F 0) i * ρ.op (F 0) j = ρ.op (F 0) j * ρ.op (F 0) i := by
  simpa [radicalOp] using radicalOp_comm ρ 0 i 0 j

/-- At fixed first-colour length and mode degree, every radical spectator word
may be carried through the node-one Garland box. -/
theorem a3_first_box_graded_with_spectators (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (ys : List (Fin 3 × ℕ)) {P : R} {n : ℕ × ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous om P n) :
    let Fm : ℕ → Module.End ℂ V := fun s => ρ.op (F 0) s
    let B : Module.End ℂ V := (ys.map fun x => radicalOp ρ x.1 x.2).prod
    Sl2Weyl.evAlg Fm (a3_first_comm ρ) P (B w) ∈
      Submodule.span ℂ {v | ∃ f, BoxP a f ∧ Finsupp.weight om f = n ∧
        v = Sl2Weyl.evAlg Fm (a3_first_comm ρ)
          (MvPolynomial.monomial f 1) (B w)} := by
  let Fm : ℕ → Module.End ℂ V := fun s => ρ.op (F 0) s
  let B : Module.End ℂ V := (ys.map fun x => radicalOp ρ x.1 x.2).prod
  have hFF : ∀ i j, Fm i * Fm j = Fm j * Fm i := by
    intro i j
    simpa [Fm, radicalOp] using radicalOp_comm ρ 0 i 0 j
  have hBF : ∀ i, B * Fm i = Fm i * B := by
    intro i
    induction ys with
    | nil => simp [B]
    | cons x xs ih =>
        simp only [B, List.map_cons, List.prod_cons] at *
        have hc : radicalOp ρ x.1 x.2 * Fm i =
            Fm i * radicalOp ρ x.1 x.2 := by
          simpa [Fm, radicalOp] using radicalOp_comm ρ x.1 x.2 0 i
        calc
          (radicalOp ρ x.1 x.2 * (xs.map fun y => radicalOp ρ y.1 y.2).prod) * Fm i =
              radicalOp ρ x.1 x.2 *
                ((xs.map fun y => radicalOp ρ y.1 y.2).prod * Fm i) := by rw [mul_assoc]
          _ = radicalOp ρ x.1 x.2 *
                (Fm i * (xs.map fun y => radicalOp ρ y.1 y.2).prod) := by rw [ih]
          _ = Fm i *
                (radicalOp ρ x.1 x.2 * (xs.map fun y => radicalOp ρ y.1 y.2).prod) := by
            rw [← mul_assoc, hc, mul_assoc]
  have hEF : ∀ k, ρ.op (simpleE 0) 1 * Fm k -
      Fm k * ρ.op (simpleE 0) 1 = ρ.op (simpleH 0) (k + 1) := by
    intro k
    apply LinearMap.ext
    intro v
    change ρ.op (simpleE 0) 1 (ρ.op (simpleF 0) k v) -
      ρ.op (simpleF 0) k (ρ.op (simpleE 0) 1 v) = _
    rw [ρ.comm]
    simp [show F 0 = simpleF 0 from rfl, simple_ef_table, Nat.add_comm]
  have hHF : ∀ m k, ρ.op (simpleH 0) (m + 1) * Fm k -
      Fm k * ρ.op (simpleH 0) (m + 1) = (-2 : ℂ) • Fm (m + 1 + k) := by
    intro m k
    apply LinearMap.ext
    intro v
    change ρ.op (simpleH 0) (m + 1) (ρ.op (simpleF 0) k v) -
      ρ.op (simpleF 0) k (ρ.op (simpleH 0) (m + 1) v) = _
    rw [ρ.comm]
    change (∑ x, bracketTable (simpleH 0) (simpleF 0) x •
      ρ.op x (m + 1 + k) v) = (-2 : ℂ) • ρ.op (simpleF 0) (m + 1 + k) v
    simp [simple_hf_table]
  have hN : (Fm 0 ^ (a + 1)) w = 0 := by
    simpa [Fm, simpleF_zero, weightABC, Module.End.pow_apply] using h.lowering 0
  have hk : ∀ r s, 1 ≤ r → a + 1 ≤ r + s →
      (PowerSeries.coeff s (VOA.DeligneAudit.Garland.Fs Fm ^ r)) w = 0 := by
    intro r s hr hrs
    exact VOA.DeligneAudit.Garland.garland hEF hHF hFF
      (h.raising (simpleE 0) (simpleE_raising 0) 1)
      (fun m => h.cartan_pos 0 (m + 1) (by omega)) r hr hN s hrs
  exact a2_span_box_graded_spectator Fm hFF B hBF w a hk hp

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_first_box_graded_with_spectators
#print axioms VOA.DeligneAudit.A3Sector.a3_first_comm
