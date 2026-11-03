import VOA.DeligneAudit.LeviTypeA2CertSl2Key

/-! The second Cartan current also raises the degree of a radical key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

theorem other_cartan_radical_comm (i : Fin 2) (r s : ℕ) :
    ρ.op 6 r * a2RadicalOp ρ i s -
      a2RadicalOp ρ i s * ρ.op 6 r =
        (if i = 0 then (-2 : ℂ) else -1) • a2RadicalOp ρ i (r + s) := by
  fin_cases i <;>
    simp [a2RadicalOp, op_comm_end, Fin.sum_univ_eight,
      VOA.AffineSl3.bracketTable]

private theorem shift_insert (r : ℕ) (i : Fin 2) (s : ℕ)
    (k : A2RadicalKey) :
    a2KeyShift r (a2KeyInsert i s k) =
      a2KeyInsert i s (a2KeyShift r k) := by
  cases k
  fin_cases i <;> simp [a2KeyShift, a2KeyInsert,
    Nat.add_comm, Nat.add_left_comm]

private theorem shift_insert_mode (r : ℕ) (i : Fin 2) (s : ℕ)
    (k : A2RadicalKey) :
    a2KeyShift r (a2KeyInsert i s k) = a2KeyInsert i (r + s) k := by
  cases k
  fin_cases i <;> simp [a2KeyShift, a2KeyInsert,
    Nat.add_comm, Nat.add_left_comm]

/-- A positive `h₁` mode sends a radical word to the same counts and
higher mode degree. -/
theorem a2_other_cartan_pos_word_key (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (r : ℕ) (hr : 0 < r) (l : List (Fin 2 × ℕ)) :
    ρ.op 6 r (radicalWord (a2RadicalOp ρ) l • w) ∈
      a2KeyLayer ρ w (a2KeyShift r (a2WordKey l)) := by
  induction l with
  | nil =>
      simp [radicalWord, h.cartan_pos 6 (by decide) r hr]
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      let u := radicalWord (a2RadicalOp ρ) l • w
      have hc := other_cartan_radical_comm ρ i r s
      have happ := congrArg (fun T : Module.End ℂ V => T u) hc
      simp only [LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply] at happ
      have hfirst : a2RadicalOp ρ i s (ρ.op 6 r u) ∈
          a2KeyLayer ρ w (a2KeyShift r (a2WordKey ((i, s) :: l))) := by
        rw [a2WordKey_cons, shift_insert]
        exact a2RadicalOp_maps_key ρ w i s (a2KeyShift r (a2WordKey l)) ih
      have hsecond : a2RadicalOp ρ i (r + s) u ∈
          a2KeyLayer ρ w (a2KeyShift r (a2WordKey ((i, s) :: l))) := by
        rw [a2WordKey_cons, shift_insert_mode]
        exact a2RadicalOp_maps_key ρ w i (r + s) (a2WordKey l)
          (radicalWord_mem_own_key ρ w l)
      change ρ.op 6 r (a2RadicalOp ρ i s u) ∈ _
      rw [sub_eq_iff_eq_add.mp happ]
      exact (a2KeyLayer ρ w _).add_mem
        ((a2KeyLayer ρ w _).smul_mem _ hsecond) hfirst

/-- A positive `h₁` mode raises degree on a whole key layer. -/
theorem a2_other_cartan_pos_maps_key (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (r : ℕ) (hr : 0 < r) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    ρ.op 6 r v ∈ a2KeyLayer ρ w (a2KeyShift r k) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, hdeg, _, rfl⟩ := hz
      have hk : a2WordKey l = k := by
        cases k
        simp [a2WordKey, hd₁, hd₂, hdeg]
      rw [← hk]
      exact a2_other_cartan_pos_word_key ρ w p q h r hr l
  | zero => simp
  | add x y _ _ hx hy => simpa using
      (a2KeyLayer ρ w (a2KeyShift r k)).add_mem hx hy
  | smul c x _ hx => simpa using
      (a2KeyLayer ρ w (a2KeyShift r k)).smul_mem c hx

/-- Positive `h₁` modes vanish modulo all higher keys. -/
theorem a2_other_cartan_pos_mem_higher (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (r : ℕ) (hr : 0 < r) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    ρ.op 6 r v ∈ a2HigherKeySpan ρ w q k := by
  have hle : a2KeyLayer ρ w (a2KeyShift r k) ≤
      a2HigherKeySpan ρ w q k := by
    unfold a2HigherKeySpan
    exact le_iSup_of_le (a2KeyShift r k)
      (le_iSup_of_le (a2KeyLess_degree q k r hr) le_rfl)
  exact hle (a2_other_cartan_pos_maps_key ρ w p q h r hr k hv)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.other_cartan_radical_comm
#print axioms VOA.DeligneAudit.A3Sector.a2_other_cartan_pos_word_key
#print axioms VOA.DeligneAudit.A3Sector.a2_other_cartan_pos_maps_key
#print axioms VOA.DeligneAudit.A3Sector.a2_other_cartan_pos_mem_higher
