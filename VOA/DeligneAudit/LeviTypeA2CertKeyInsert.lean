import VOA.DeligneAudit.LeviTypeA2CertKeyWeight

/-! Bookkeeping for inserting one radical current into a key layer. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule
    VOA.AffineSl3.bracketTable V) (w : V)

/-- The key of a concrete radical word. -/
def a2WordKey (l : List (Fin 2 × ℕ)) : A2RadicalKey :=
  ⟨l.countP (fun x => x.1 = 0), l.countP (fun x => x.1 = 1),
    (l.map Prod.snd).sum⟩

/-- The effect of prepending a radical letter. -/
def a2KeyInsert (i : Fin 2) (s : ℕ) (k : A2RadicalKey) : A2RadicalKey :=
  ⟨k.d₁ + if i = 0 then 1 else 0,
    k.d₂ + if i = 1 then 1 else 0, k.degree + s⟩

theorem a2WordKey_cons (i : Fin 2) (s : ℕ) (l : List (Fin 2 × ℕ)) :
    a2WordKey ((i, s) :: l) = a2KeyInsert i s (a2WordKey l) := by
  fin_cases i <;> simp [a2WordKey, a2KeyInsert,
    Nat.add_comm]

/-- A word lies in its own key layer. -/
theorem radicalWord_mem_own_key (l : List (Fin 2 × ℕ)) :
    radicalWord (a2RadicalOp ρ) l • w ∈ a2KeyLayer ρ w (a2WordKey l) := by
  apply Submodule.subset_span
  refine ⟨l, rfl, rfl, rfl, ?_, rfl⟩
  have hcount : l.countP (fun x => x.1 = 0) +
      l.countP (fun x => x.1 = 1) = l.length := by
    induction l with
    | nil => simp
    | cons x l ih =>
        rcases x with ⟨i, s⟩
        fin_cases i <;> simp_all [Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
  exact hcount.symm

/-- Applying a radical current inserts its colour and mode into the key. -/
theorem a2RadicalOp_maps_key (i : Fin 2) (s : ℕ) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    a2RadicalOp ρ i s v ∈ a2KeyLayer ρ w (a2KeyInsert i s k) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, hdeg, hlen, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨(i, s) :: l, ?_, ?_, ?_, ?_, ?_⟩
      · fin_cases i <;> simp [a2KeyInsert, hd₁,
          Nat.add_comm]
      · fin_cases i <;> simp [a2KeyInsert, hd₂,
          Nat.add_comm]
      · simp [a2KeyInsert, hdeg, Nat.add_comm]
      · fin_cases i <;> simp [a2KeyInsert, hlen,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      · rfl
  | zero => simp
  | add x y _ _ hx hy => simpa using
      (a2KeyLayer ρ w (a2KeyInsert i s k)).add_mem hx hy
  | smul c x _ hx => simpa using
      (a2KeyLayer ρ w (a2KeyInsert i s k)).smul_mem c hx

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2WordKey_cons
#print axioms VOA.DeligneAudit.A3Sector.radicalWord_mem_own_key
#print axioms VOA.DeligneAudit.A3Sector.a2RadicalOp_maps_key
