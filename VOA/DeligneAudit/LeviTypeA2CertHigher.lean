import VOA.DeligneAudit.LeviTypeA2CertKeyRaiseWord

/-! Positive Levi modes of a key layer land in strictly higher radical keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The sum of radical key layers strictly higher than `k`. -/
def a2HigherKeySpan (q : ℕ) (k : A2RadicalKey) : Submodule ℂ V :=
  ⨆ (j : A2RadicalKey) (_ : a2KeyLess q k j), a2KeyLayer ρ w j

private theorem keyLayer_le_higher (q : ℕ) (k j : A2RadicalKey)
    (hj : a2KeyLess q k j) :
    a2KeyLayer ρ w j ≤ a2HigherKeySpan ρ w q k := by
  unfold a2HigherKeySpan
  exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)

/-- A positive node-two Cartan mode lands in a higher key layer. -/
theorem a2_cartan_pos_mem_higher (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (r : ℕ) (hr : 0 < r) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    ρ.op 7 r v ∈ a2HigherKeySpan ρ w q k := by
  apply keyLayer_le_higher ρ w q k (a2KeyShift r k)
  · exact a2KeyLess_degree q k r hr
  · exact a2_cartan_pos_maps_key ρ w p q h r hr k hv

private theorem raising_zero_if_no_compound (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (r : ℕ) (k : A2RadicalKey)
    (hk : k.d₂ = 0) {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    ρ.op 1 r v = 0 := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, _, hd₂, _, _, rfl⟩ := hz
      exact a2_raising_word_zero_no_compound ρ w p q h r l (hd₂.trans hk)
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul c x _ hx => simp [map_smul, hx]

/-- Every node-two raising mode lands in a higher key, or vanishes. -/
theorem a2_raising_mem_higher (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (r : ℕ) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    ρ.op 1 r v ∈ a2HigherKeySpan ρ w q k := by
  by_cases hk : k.d₂ = 0
  · rw [raising_zero_if_no_compound ρ w p q h r k hk hv]
    exact (a2HigherKeySpan ρ w q k).zero_mem
  · have hpos : 0 < k.d₂ := by omega
    apply keyLayer_le_higher ρ w q k (a2KeyRaised r k)
    · exact a2KeyLess_raised q r k hpos
    · exact a2_raising_maps_key ρ w p q h r k hv

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_cartan_pos_mem_higher
#print axioms VOA.DeligneAudit.A3Sector.a2_raising_mem_higher
