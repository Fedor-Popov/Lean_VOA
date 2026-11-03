import VOA.DeligneAudit.LeviTypeA2CertSimpleCount
import VOA.DeligneAudit.DeligneFusionSl2Module

/-! The first-colour box theorem survives commuting radical spectators. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A commuting spectator intertwines evaluation of every lowering polynomial. -/
theorem a2_evAlg_comm_spectator (F : ℕ → Module.End ℂ V)
    (hFF : ∀ i j, F i * F j = F j * F i)
    (B : Module.End ℂ V) (hBF : ∀ i, B * F i = F i * B)
    (P : R) :
    B * Sl2Weyl.evAlg F hFF P = Sl2Weyl.evAlg F hFF P * B := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.C_eq_smul_one, map_smul, map_one]
      simp only [Algebra.smul_def, mul_one]
      exact (Algebra.commutes c B).symm
  | add P Q hP hQ =>
      simp only [map_add, mul_add, add_mul, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, Sl2Weyl.evAlg_z]
      calc
        B * (Sl2Weyl.evAlg F hFF P * F i) =
            (B * Sl2Weyl.evAlg F hFF P) * F i := by rw [mul_assoc]
        _ = (Sl2Weyl.evAlg F hFF P * B) * F i := by rw [hP]
        _ = Sl2Weyl.evAlg F hFF P * (B * F i) := by rw [mul_assoc]
        _ = Sl2Weyl.evAlg F hFF P * (F i * B) := by rw [hBF]

/-- If the Garland relations hold on `w`, a commuting spectator may be placed
after any polynomial and the first-colour box still spans its orbit. -/
theorem a2_span_box_spectator (F : ℕ → Module.End ℂ V)
    (hFF : ∀ i j, F i * F j = F j * F i)
    (B : Module.End ℂ V) (hBF : ∀ i, B * F i = F i * B)
    (w : V) (m : ℕ)
    (hk : ∀ r s, 1 ≤ r → m + 1 ≤ r + s →
      (PowerSeries.coeff s (VOA.DeligneAudit.Garland.Fs F ^ r)) w = 0)
    (P : R) :
    Sl2Weyl.evAlg F hFF P (B w) ∈
      Submodule.span ℂ {v | ∃ f, BoxP m f ∧
        v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) (B w)} := by
  let S : Submodule ℂ V :=
    Submodule.span ℂ {v | ∃ f, BoxP m f ∧
      v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) (B w)}
  have hmap : ∀ v ∈ Submodule.span ℂ {v | ∃ f, BoxP m f ∧
      v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) w}, B v ∈ S := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨f, hf, rfl⟩ := hv
        have hc := a2_evAlg_comm_spectator F hFF B hBF
          (MvPolynomial.monomial f 1)
        rw [← Module.End.mul_apply, hc, Module.End.mul_apply]
        exact Submodule.subset_span ⟨f, hf, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using S.add_mem hx hy
    | smul c x _ hx => simpa only [map_smul] using S.smul_mem c hx
  have h := hmap _ (span_box F hFF w m hk P)
  have hc := a2_evAlg_comm_spectator F hFF B hBF P
  rwa [← Module.End.mul_apply, hc, Module.End.mul_apply] at h

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviTypeA

variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- Every first-colour polynomial, with an arbitrary second-colour word on
its right, is spanned by first-colour box monomials with that same word. -/
theorem a2_first_box_with_spectators (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (ys : List ℕ) (P : R) :
    let F : ℕ → Module.End ℂ V := fun s => ρ.op 3 s
    let B : Module.End ℂ V := (ys.map fun s => ρ.op 5 s).prod
    Sl2Weyl.evAlg F (fun i j => by
      simpa [F, a2RadicalOp] using
        a2RadicalOp_comm ρ (0 : Fin 2) (0 : Fin 2) i j) P (B w) ∈
      Submodule.span ℂ {v | ∃ f, BoxP p f ∧
        v = Sl2Weyl.evAlg F (fun i j => by
          simpa [F, a2RadicalOp] using
            a2RadicalOp_comm ρ (0 : Fin 2) (0 : Fin 2) i j)
          (MvPolynomial.monomial f 1) (B w)} := by
  let F : ℕ → Module.End ℂ V := fun s => ρ.op 3 s
  let B : Module.End ℂ V := (ys.map fun s => ρ.op 5 s).prod
  have hFF : ∀ i j, F i * F j = F j * F i := by
    intro i j
    simpa [F, a2RadicalOp] using
      a2RadicalOp_comm ρ (0 : Fin 2) (0 : Fin 2) i j
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
  let H : ℕ → Module.End ℂ V := fun s => ρ.op 6 s
  let E : Module.End ℂ V := ρ.op 0 1
  have hEF : ∀ k, E * F k - F k * E = H (k + 1) := by
    intro k
    rw [op_comm_end]
    simp [H, Fin.sum_univ_eight, VOA.AffineSl3.bracketTable, Nat.add_comm]
  have hHF : ∀ m k, H (m + 1) * F k - F k * H (m + 1) =
      (-2 : ℂ) • F (m + 1 + k) := by
    intro m k
    rw [op_comm_end]
    simp [F, Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  have hE : E w = 0 := h.raising 0 (by decide) 1
  have hH : ∀ m, H (m + 1) w = 0 := by
    intro m
    exact h.cartan_pos 6 (by decide) _ (by omega)
  have hN : (F 0 ^ (p + 1)) w = 0 := by
    simpa [F, Module.End.pow_apply] using h.lowering_first
  have hk : ∀ r s, 1 ≤ r → p + 1 ≤ r + s →
      (PowerSeries.coeff s (VOA.DeligneAudit.Garland.Fs F ^ r)) w = 0 := by
    intro r s hr hrs
    exact VOA.DeligneAudit.Garland.garland hEF hHF hFF hE hH r hr hN s hrs
  exact a2_span_box_spectator F hFF B hBF w p hk P

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_evAlg_comm_spectator
#print axioms VOA.DeligneAudit.A3Sector.a2_span_box_spectator
#print axioms VOA.DeligneAudit.A3Sector.a2_first_box_with_spectators
