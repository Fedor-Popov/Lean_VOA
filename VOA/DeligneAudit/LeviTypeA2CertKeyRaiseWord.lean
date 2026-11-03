import VOA.DeligneAudit.LeviTypeA2CertKeyRaiseZero

/-! A node-two raising mode sends a radical word to its raised key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

private theorem raised_insert_simple (r s : ℕ) (k : A2RadicalKey) :
    a2KeyRaised r (a2KeyInsert 0 s k) =
      a2KeyInsert 0 s (a2KeyRaised r k) := by
  cases k
  simp [a2KeyRaised, a2KeyInsert, Nat.add_comm,
    Nat.add_left_comm]

private theorem raised_insert_compound (r s : ℕ) (k : A2RadicalKey)
    (hk : 0 < k.d₂) :
    a2KeyRaised r (a2KeyInsert 1 s k) =
      a2KeyInsert 1 s (a2KeyRaised r k) := by
  rcases k with ⟨d₁, d₂, degree⟩
  have hd : 1 ≤ d₂ := by simpa using hk
  simp [a2KeyRaised, a2KeyInsert, Nat.sub_add_cancel hd,
    Nat.add_comm, Nat.add_left_comm]

private theorem raised_compound_to_simple (r s : ℕ) (k : A2RadicalKey) :
    a2KeyRaised r (a2KeyInsert 1 s k) = a2KeyInsert 0 (r + s) k := by
  cases k
  simp [a2KeyRaised, a2KeyInsert, Nat.add_comm,
    Nat.add_left_comm]

/-- Raising any radical word lies in the key obtained by replacing one
compound radical with a simple radical. With no compound letter, it is zero. -/
theorem a2_raising_word_key (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (r : ℕ) (l : List (Fin 2 × ℕ)) :
    ρ.op 1 r (radicalWord (a2RadicalOp ρ) l • w) ∈
      a2KeyLayer ρ w (a2KeyRaised r (a2WordKey l)) := by
  induction l with
  | nil =>
      simp [radicalWord, h.raising 1 (by decide) r]
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      let u := radicalWord (a2RadicalOp ρ) l • w
      fin_cases i
      · have hc := a2_raising_simple_comm ρ r s
        have happ := congrArg (fun T : Module.End ℂ V => T u) hc
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at happ
        have hmap : a2RadicalOp ρ 0 s (ρ.op 1 r u) ∈
            a2KeyLayer ρ w (a2KeyRaised r (a2WordKey ((0, s) :: l))) := by
          rw [a2WordKey_cons, raised_insert_simple]
          exact a2RadicalOp_maps_key ρ w 0 s (a2KeyRaised r (a2WordKey l)) ih
        change ρ.op 1 r (a2RadicalOp ρ 0 s u) ∈ _
        rw [sub_eq_iff_eq_add.mp happ]
        simpa using hmap
      · have hc := a2_raising_compound_comm ρ r s
        have happ := congrArg (fun T : Module.End ℂ V => T u) hc
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at happ
        have hfirst : a2RadicalOp ρ 1 s (ρ.op 1 r u) ∈
            a2KeyLayer ρ w (a2KeyRaised r (a2WordKey ((1, s) :: l))) := by
          by_cases hz : (a2WordKey l).d₂ = 0
          · have hzero : ρ.op 1 r u = 0 :=
              a2_raising_word_zero_no_compound ρ w p q h r l hz
            rw [hzero, map_zero]
            exact (a2KeyLayer ρ w _).zero_mem
          · have hpos : 0 < (a2WordKey l).d₂ := by omega
            rw [a2WordKey_cons, raised_insert_compound r s _ hpos]
            exact a2RadicalOp_maps_key ρ w 1 s (a2KeyRaised r (a2WordKey l)) ih
        have hsecond : a2RadicalOp ρ 0 (r + s) u ∈
            a2KeyLayer ρ w (a2KeyRaised r (a2WordKey ((1, s) :: l))) := by
          rw [a2WordKey_cons, raised_compound_to_simple]
          exact a2RadicalOp_maps_key ρ w 0 (r + s) (a2WordKey l)
            (radicalWord_mem_own_key ρ w l)
        change ρ.op 1 r (a2RadicalOp ρ 1 s u) ∈ _
        rw [sub_eq_iff_eq_add.mp happ]
        exact (a2KeyLayer ρ w _).add_mem hsecond hfirst

/-- A node-two raising mode sends the entire key layer into the raised key layer. -/
theorem a2_raising_maps_key (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (r : ℕ) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    ρ.op 1 r v ∈ a2KeyLayer ρ w (a2KeyRaised r k) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, hdeg, _, rfl⟩ := hz
      have hk : a2WordKey l = k := by
        cases k
        simp [a2WordKey, hd₁, hd₂, hdeg]
      rw [← hk]
      exact a2_raising_word_key ρ w p q h r l
  | zero => simp
  | add x y _ _ hx hy => simpa using
      (a2KeyLayer ρ w (a2KeyRaised r k)).add_mem hx hy
  | smul c x _ hx => simpa using
      (a2KeyLayer ρ w (a2KeyRaised r k)).smul_mem c hx

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_raising_word_key
#print axioms VOA.DeligneAudit.A3Sector.a2_raising_maps_key
