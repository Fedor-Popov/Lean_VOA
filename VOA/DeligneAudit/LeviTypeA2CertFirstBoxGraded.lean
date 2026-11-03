import VOA.DeligneAudit.LeviTypeA2CertSpectatorBoxGraded
import VOA.DeligneAudit.DeligneFusionCVRoots

/-! The graded first-colour box with all second-colour spectators. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- At fixed first-colour length and degree, the box rewriting commutes
with every second-colour word on the right. -/
theorem a2_first_box_graded_with_spectators (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (ys : List ℕ)
    {P : R} {n : ℕ × ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous om P n) :
    let F : ℕ → Module.End ℂ V := fun s => ρ.op 3 s
    let B : Module.End ℂ V := (ys.map fun s => ρ.op 5 s).prod
    Sl2Weyl.evAlg F (VOA.DeligneAudit.A2.CVRoots.sl2_first ρ).hFF P (B w) ∈
      Submodule.span ℂ {v | ∃ f, BoxP p f ∧ Finsupp.weight om f = n ∧
        v = Sl2Weyl.evAlg F (VOA.DeligneAudit.A2.CVRoots.sl2_first ρ).hFF
          (MvPolynomial.monomial f 1) (B w)} := by
  let F : ℕ → Module.End ℂ V := fun s => ρ.op 3 s
  let B : Module.End ℂ V := (ys.map fun s => ρ.op 5 s).prod
  have hS : VOA.DeligneAudit.CVsl2.SL2 (ρ.op 0) (ρ.op 6) (ρ.op 3) :=
    VOA.DeligneAudit.A2.CVRoots.sl2_first ρ
  have hBF : ∀ i, B * F i = F i * B := by
    intro i
    induction ys with
    | nil => simp [B]
    | cons s ys ih =>
        simp only [B, List.map_cons, List.prod_cons] at *
        have hc : ρ.op 5 s * F i = F i * ρ.op 5 s := by
          simpa [F, a2RadicalOp] using
            a2RadicalOp_comm ρ (1 : Fin 2) (0 : Fin 2) s i
        calc
          (ρ.op 5 s * (ys.map fun t => ρ.op 5 t).prod) * F i =
              ρ.op 5 s * ((ys.map fun t => ρ.op 5 t).prod * F i) := by rw [mul_assoc]
          _ = ρ.op 5 s * (F i * (ys.map fun t => ρ.op 5 t).prod) := by rw [ih]
          _ = (ρ.op 5 s * F i) * (ys.map fun t => ρ.op 5 t).prod := by rw [mul_assoc]
          _ = (F i * ρ.op 5 s) * (ys.map fun t => ρ.op 5 t).prod := by rw [hc]
          _ = F i * (ρ.op 5 s * (ys.map fun t => ρ.op 5 t).prod) := by rw [mul_assoc]
  have hEF : ∀ k, ρ.op 0 1 * F k - F k * ρ.op 0 1 = ρ.op 6 (k + 1) := by
    intro k
    simpa [F, Nat.add_comm] using hS.hEF 1 k
  have hHF : ∀ m k, ρ.op 6 (m + 1) * F k - F k * ρ.op 6 (m + 1) =
      (-2 : ℂ) • F (m + 1 + k) := by
    intro m k
    exact hS.hHF (m + 1) k
  have hE : ρ.op 0 1 w = 0 := h.raising 0 (by decide) 1
  have hH : ∀ m, ρ.op 6 (m + 1) w = 0 := by
    intro m
    exact h.cartan_pos 6 (by decide) _ (by omega)
  have hN : (F 0 ^ (p + 1)) w = 0 := by
    simpa [F, Module.End.pow_apply] using h.lowering_first
  have hk : ∀ r s, 1 ≤ r → p + 1 ≤ r + s →
      (PowerSeries.coeff s (VOA.DeligneAudit.Garland.Fs F ^ r)) w = 0 := by
    intro r s hr hrs
    exact VOA.DeligneAudit.Garland.garland hEF hHF hS.hFF hE hH r hr hN s hrs
  exact a2_span_box_graded_spectator F hS.hFF B hBF w p hk hp

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_first_box_graded_with_spectators
