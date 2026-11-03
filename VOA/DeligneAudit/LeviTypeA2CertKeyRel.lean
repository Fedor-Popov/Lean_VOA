import VOA.DeligneAudit.LeviTypeA2CertKeyHW

/-! All node-two local Weyl relations for a key vector modulo higher keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The precise relations in a Levi-stable quotient for one radical key vector. -/
def A2KeyLocalWeylRelModulo (q : ℕ) (k : A2RadicalKey)
    (N : Submodule ℂ V) (v : V) : Prop :=
  (∀ r : ℕ, ρ.op 1 r v ∈ N) ∧
  (∀ r : ℕ, 0 < r → ρ.op 7 r v ∈ N) ∧
  ρ.op 7 0 v = (a2KeyHeight q k : ℂ) • v ∧
  (a2KeyHeight q k < 0 → v ∈ N) ∧
  (0 ≤ a2KeyHeight q k →
    (ρ.op 4 0 ^ ((a2KeyHeight q k).toNat + 1)) v ∈ N)

/-- Key vectors satisfy every node-two local Weyl relation in a quotient
containing higher keys and stable under the node-two currents. -/
theorem a2_key_local_weyl_rel_mod (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    (N : Submodule ℂ V)
    (hHigher : a2HigherKeySpan ρ w q k ≤ N)
    (hStable : ∀ r, ∀ a : Fin 8, a = 1 ∨ a = 4 ∨ a = 7 →
      N ≤ N.comap (ρ.op a r))
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    A2KeyLocalWeylRelModulo ρ q k N v := by
  have hSharp := a2_key_lowering_sharp_mod ρ w p q h k N hHigher
    (hStable 0 1 (Or.inl rfl))
    (hStable 0 4 (Or.inr (Or.inl rfl)))
    (hStable 0 7 (Or.inr (Or.inr rfl))) hv
  refine ⟨?_, ?_, ?_, hSharp.1, hSharp.2⟩
  · intro r
    exact hHigher (a2_raising_mem_higher ρ w p q h r k hv)
  · intro r hr
    exact hHigher (a2_cartan_pos_mem_higher ρ w p q h r hr k hv)
  · have hw := a2_node2_weight_key ρ w q k h.cartan_second hv
    simpa [a2KeyHeight] using hw

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_key_local_weyl_rel_mod
