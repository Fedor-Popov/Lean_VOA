import VOA.DeligneAudit.LeviTypeA2CertKeyInsert

/-! Positive node-two Cartan modes raise only the degree of a radical key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- Raise the total mode degree without changing radical counts. -/
def a2KeyShift (r : ℕ) (k : A2RadicalKey) : A2RadicalKey :=
  { k with degree := k.degree + r }

private theorem keyShift_insert (r : ℕ) (i : Fin 2) (s : ℕ)
    (k : A2RadicalKey) :
    a2KeyShift r (a2KeyInsert i s k) =
      a2KeyInsert i s (a2KeyShift r k) := by
  cases k
  fin_cases i <;> simp [a2KeyShift, a2KeyInsert,
    Nat.add_comm, Nat.add_left_comm]

private theorem keyShift_insert_mode (r : ℕ) (i : Fin 2) (s : ℕ)
    (k : A2RadicalKey) :
    a2KeyShift r (a2KeyInsert i s k) = a2KeyInsert i (r + s) k := by
  cases k
  fin_cases i <;> simp [a2KeyShift, a2KeyInsert,
    Nat.add_comm, Nat.add_left_comm]

private theorem node2_cartan_radical_comm (i : Fin 2) (r s : ℕ) :
    ρ.op 7 r * a2RadicalOp ρ i s -
      a2RadicalOp ρ i s * ρ.op 7 r =
        (if i = 0 then (1 : ℂ) else -1) • a2RadicalOp ρ i (r + s) := by
  fin_cases i <;>
    simp [a2RadicalOp, op_comm_end, Fin.sum_univ_eight,
      VOA.AffineSl3.bracketTable]

/-- A positive Cartan mode sends a radical word to the same counts and higher degree. -/
theorem a2_cartan_pos_word_key (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (r : ℕ) (hr : 0 < r) (l : List (Fin 2 × ℕ)) :
    ρ.op 7 r (radicalWord (a2RadicalOp ρ) l • w) ∈
      a2KeyLayer ρ w (a2KeyShift r (a2WordKey l)) := by
  induction l with
  | nil =>
      simp [radicalWord, h.cartan_pos 7 (by decide) r hr]
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      let u := radicalWord (a2RadicalOp ρ) l • w
      have hc := node2_cartan_radical_comm ρ i r s
      have happ := congrArg (fun T : Module.End ℂ V => T u) hc
      simp only [LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply] at happ
      have hfirst : a2RadicalOp ρ i s (ρ.op 7 r u) ∈
          a2KeyLayer ρ w (a2KeyShift r (a2WordKey ((i, s) :: l))) := by
        rw [a2WordKey_cons, keyShift_insert]
        exact a2RadicalOp_maps_key ρ w i s (a2KeyShift r (a2WordKey l)) ih
      have hsecond : a2RadicalOp ρ i (r + s) u ∈
          a2KeyLayer ρ w (a2KeyShift r (a2WordKey ((i, s) :: l))) := by
        rw [a2WordKey_cons, keyShift_insert_mode]
        exact a2RadicalOp_maps_key ρ w i (r + s) (a2WordKey l)
          (radicalWord_mem_own_key ρ w l)
      change ρ.op 7 r (a2RadicalOp ρ i s u) ∈ _
      rw [sub_eq_iff_eq_add.mp happ]
      exact (a2KeyLayer ρ w _).add_mem
        ((a2KeyLayer ρ w _).smul_mem _ hsecond) hfirst

/-- Positive node-two Cartan modes raise the degree on the entire key layer. -/
theorem a2_cartan_pos_maps_key (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (r : ℕ) (hr : 0 < r) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    ρ.op 7 r v ∈ a2KeyLayer ρ w (a2KeyShift r k) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, hdeg, _, rfl⟩ := hz
      have hk : a2WordKey l = k := by
        cases k
        simp [a2WordKey, hd₁, hd₂, hdeg]
      rw [← hk]
      exact a2_cartan_pos_word_key ρ w p q h r hr l
  | zero => simp
  | add x y _ _ hx hy => simpa using
      (a2KeyLayer ρ w (a2KeyShift r k)).add_mem hx hy
  | smul c x _ hx => simpa using
      (a2KeyLayer ρ w (a2KeyShift r k)).smul_mem c hx

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_cartan_pos_word_key
#print axioms VOA.DeligneAudit.A3Sector.a2_cartan_pos_maps_key
