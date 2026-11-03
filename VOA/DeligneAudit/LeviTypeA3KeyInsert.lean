import VOA.DeligneAudit.LeviTypeA3Quotient
import VOA.DeligneAudit.LeviTypeA3Depth

/-! Exact key bookkeeping for the three abelian radical colours. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule bracketTable V) (w : V)

/-- The key of a concrete radical word. -/
def a3WordKey (l : List (Fin 3 × ℕ)) : A3RadicalKey :=
  ⟨l.countP (fun x => x.1 = 0), l.countP (fun x => x.1 = 1),
    l.countP (fun x => x.1 = 2), (l.map Prod.snd).sum⟩

/-- The key change from adding one radical current. -/
def a3KeyInsert (i : Fin 3) (s : ℕ) (k : A3RadicalKey) : A3RadicalKey :=
  ⟨k.d₁ + if i = 0 then 1 else 0,
    k.d₂ + if i = 1 then 1 else 0,
    k.d₃ + if i = 2 then 1 else 0, k.degree + s⟩

theorem a3WordKey_cons (i : Fin 3) (s : ℕ) (l : List (Fin 3 × ℕ)) :
    a3WordKey ((i, s) :: l) = a3KeyInsert i s (a3WordKey l) := by
  fin_cases i <;> simp [a3WordKey, a3KeyInsert, Nat.add_comm]

/-- A radical word belongs to its exact count and mode-degree layer. -/
theorem a3_radicalWord_mem_own_key (l : List (Fin 3 × ℕ)) :
    radicalWord (radicalOp ρ) l • w ∈ a3KeyLayer ρ w (a3WordKey l) := by
  apply Submodule.subset_span
  refine ⟨l, rfl, rfl, rfl, rfl, ?_, rfl⟩
  exact (a3_radical_counts_sum l).symm

/-- One radical current inserts its count and mode degree into a key. -/
theorem a3RadicalOp_maps_key (i : Fin 3) (s : ℕ) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    radicalOp ρ i s v ∈ a3KeyLayer ρ w (a3KeyInsert i s k) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, hd₃, hdeg, hlen, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨(i, s) :: l, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · fin_cases i <;> simp [a3KeyInsert, hd₁, Nat.add_comm]
      · fin_cases i <;> simp [a3KeyInsert, hd₂, Nat.add_comm]
      · fin_cases i <;> simp [a3KeyInsert, hd₃, Nat.add_comm]
      · simp [a3KeyInsert, hdeg, Nat.add_comm]
      · fin_cases i <;> simp [a3KeyInsert, hlen,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  | zero => simp
  | add x y _ _ hx hy =>
      simpa using (a3KeyLayer ρ w (a3KeyInsert i s k)).add_mem hx hy
  | smul c x _ hx =>
      simpa using (a3KeyLayer ρ w (a3KeyInsert i s k)).smul_mem c hx

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3WordKey_cons
#print axioms VOA.DeligneAudit.A3Sector.a3_radicalWord_mem_own_key
#print axioms VOA.DeligneAudit.A3Sector.a3RadicalOp_maps_key
