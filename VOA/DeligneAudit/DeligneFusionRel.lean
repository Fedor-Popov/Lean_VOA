/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionPBW

/-!
# Ravinder's modules `M_{a,b}` and the F4 interface (for the graded squeeze F6)

`MabRel ρ w a b` (`sl₃`, `k = a + b`): the relations of
`M_{a,b} = D(1,θ)^{*a} * V(θ)^{*b} ≅ D(1,kθ)/⟨(f_θ ⊗ t^{2a+b}) w⟩` (Ravinder Prop. 1, Cor. 2,
simply laced):
`n⁺[t] w = 0`, `(h ⊗ t^s) w = δ_{s0} kθ(h) w`, `f_i^{k+1} w = 0`, `(f_i ⊗ t^k) w = 0` (`i = 1, 2`), and
`(f_θ ⊗ t^{2a+b}) w = 0`.  For `a = 0` these are exactly `LocalWeylRel` (`mabRel_zero_iff`).

Named statements (targets):
* `FusionTotalBound` (**F4**): `∑_b dim (M_{0,m})_b ≤ 8^m` for every module with `LocalWeylRel`
  (= the `total` field of U5);
* `RavinderKernelRel` (**F4′**): for `a ≥ 1`, the vector `v = (f_θ ⊗ t^{2a+b-1}) w` satisfies the
  relations of `M_{a-1,b}` (the kernel of `M_{a,b} ↠ M_{a-1,b+1}` is a quotient of `τ M_{a-1,b}`;
  Ravinder Thm. 1).  The quotient relations are automatic: `M_{a-1,b+1}` is `M_{a,b}/⟨v⟩`.
-/

namespace VOA.DeligneAudit.SectorWeyl

open VOA.AffineSl3

/-- The relations of Ravinder's `M_{a,b}` for `sl₃` (`f₁ = 3`, `f₂ = 4`, `f_θ = f₁₂ = 5`). -/
structure MabRel {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule (bracketTable) V) (w : V) (a b : ℕ) : Prop where
  raising : ∀ (e : Fin 8), e.val < 3 → ∀ r, ρ.op e r w = 0
  cartan_pos : ∀ (h : Fin 8), 6 ≤ h.val → ∀ r, 1 ≤ r → ρ.op h r w = 0
  cartan_zero : ∀ (h : Fin 8), 6 ≤ h.val → ρ.op h 0 w = ((a + b : ℕ) : ℂ) • w
  lowering_f1 : (ρ.op 3 0)^[a + b + 1] w = 0
  lowering_f2 : (ρ.op 4 0)^[a + b + 1] w = 0
  trunc_f1 : ρ.op 3 (a + b) w = 0
  trunc_f2 : ρ.op 4 (a + b) w = 0
  trunc_theta : ρ.op 5 (2 * a + b) w = 0

theorem mabRel_zero_iff {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule (bracketTable) V) (w : V) (m : ℕ) :
    MabRel ρ w 0 m ↔ LocalWeylRel ρ w m := by
  constructor
  · intro h
    refine ⟨h.raising, h.cartan_pos, by simpa using h.cartan_zero, by simpa using h.lowering_f1,
      by simpa using h.lowering_f2, fun fα h3 h6 => ?_⟩
    have : fα = 3 ∨ fα = 4 ∨ fα = 5 := by omega
    rcases this with rfl | rfl | rfl
    · simpa using h.trunc_f1
    · simpa using h.trunc_f2
    · simpa using h.trunc_theta
  · intro h
    exact ⟨h.raising, h.cartan_pos, by simpa using h.cartan_zero, by simpa using h.lowering_f1,
      by simpa using h.lowering_f2, by simpa using h.fusion 3 (by decide) (by decide),
      by simpa using h.fusion 4 (by decide) (by decide), by simpa using h.fusion 5 (by decide) (by decide)⟩

/-- **F4 (target; named literature input: Feigin, Fourier–Littelmann, Ravinder Prop. 1)**: the
degree pieces of a fusion module are finite-dimensional and its total dimension is at most `8^m`.
(The finiteness clause is needed because `Module.finrank` is `0` on infinite-dimensional spaces.) -/
def FusionTotalBound : Prop :=
  ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V) (w : V),
    LocalWeylRel ρ w m → (∀ b, FiniteDimensional ℂ (cycDeg ρ w b)) ∧
      ∀ B : ℕ, ∑ b ∈ Finset.range B, Module.finrank ℂ (cycDeg ρ w b) ≤ 8 ^ m

/-- **F4′ (target)**: Ravinder's kernel vector satisfies the relations of `M_{a-1,b}`. -/
def RavinderKernelRel : Prop :=
  ∀ (a b : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V) (w : V),
    1 ≤ a → MabRel ρ w a b → MabRel ρ (ρ.op 5 (2 * a + b - 1) w) (a - 1) b

end VOA.DeligneAudit.SectorWeyl

section AxiomAudit
#print axioms VOA.DeligneAudit.SectorWeyl.mabRel_zero_iff
end AxiomAudit
