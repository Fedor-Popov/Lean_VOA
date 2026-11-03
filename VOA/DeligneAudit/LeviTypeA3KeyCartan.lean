import VOA.DeligneAudit.LeviTypeA3KeyWeight

/-! Positive Levi Cartan modes raise only the mode degree of a radical key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

private theorem keyShift_insert (r : ℕ) (i : Fin 3) (s : ℕ)
    (k : A3RadicalKey) :
    a3KeyShift r (a3KeyInsert i s k) =
      a3KeyInsert i s (a3KeyShift r k) := by
  cases k
  fin_cases i <;> simp [a3KeyShift, a3KeyInsert,
    Nat.add_comm, Nat.add_left_comm]

private theorem keyShift_insert_mode (r : ℕ) (i : Fin 3) (s : ℕ)
    (k : A3RadicalKey) :
    a3KeyShift r (a3KeyInsert i s k) = a3KeyInsert i (r + s) k := by
  cases k
  fin_cases i <;> simp [a3KeyShift, a3KeyInsert,
    Nat.add_comm, Nat.add_left_comm]

theorem a3_cartan_pos_word_key (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 2) (r : ℕ) (hr : 0 < r) (l : List (Fin 3 × ℕ)) :
    ρ.op (leviH i) r (radicalWord (radicalOp ρ) l • w) ∈
      a3KeyLayer ρ w (a3KeyShift r (a3WordKey l)) := by
  induction l with
  | nil =>
      have hzero : ρ.op (leviH i) r w = 0 := by
        fin_cases i
        · simpa [leviH, simpleH] using h.cartan_pos 1 r hr
        · simpa [leviH, simpleH] using h.cartan_pos 2 r hr
      simp [radicalWord, hzero]
  | cons x l ih =>
      rcases x with ⟨j, s⟩
      let u := radicalWord (radicalOp ρ) l • w
      have hc := levi_cartan_comm ρ i j r s u
      have hfirst : radicalOp ρ j s (ρ.op (leviH i) r u) ∈
          a3KeyLayer ρ w (a3KeyShift r (a3WordKey ((j, s) :: l))) := by
        rw [a3WordKey_cons, keyShift_insert]
        exact a3RadicalOp_maps_key ρ w j s (a3KeyShift r (a3WordKey l)) ih
      have hsecond : radicalOp ρ j (r + s) u ∈
          a3KeyLayer ρ w (a3KeyShift r (a3WordKey ((j, s) :: l))) := by
        rw [a3WordKey_cons, keyShift_insert_mode]
        exact a3RadicalOp_maps_key ρ w j (r + s) (a3WordKey l)
          (a3_radicalWord_mem_own_key ρ w l)
      have hcons : radicalWord (radicalOp ρ) ((j, s) :: l) • w =
          radicalOp ρ j s u := by
        simp [u, radicalWord, radicalOp, mul_smul]
      rw [hcons]
      have heq : ρ.op (leviH i) r (radicalOp ρ j s u) =
          (leviWeight i j : ℂ) • radicalOp ρ j (r + s) u +
            radicalOp ρ j s (ρ.op (leviH i) r u) := by
        have hc' := (sub_eq_iff_eq_add.mp hc)
        simpa only [radicalOp, add_comm] using hc'
      rw [heq]
      exact (a3KeyLayer ρ w _).add_mem
        ((a3KeyLayer ρ w _).smul_mem _ hsecond) hfirst

theorem a3_cartan_pos_maps_key (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 2) (r : ℕ) (hr : 0 < r) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    ρ.op (leviH i) r v ∈ a3KeyLayer ρ w (a3KeyShift r k) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, hd₃, hdeg, _, rfl⟩ := hz
      have hk : a3WordKey l = k := by
        cases k
        simp [a3WordKey, hd₁, hd₂, hd₃, hdeg]
      rw [← hk]
      exact a3_cartan_pos_word_key ρ w a b c h i r hr l
  | zero => simp
  | add x y _ _ hx hy =>
      simpa using (a3KeyLayer ρ w (a3KeyShift r k)).add_mem hx hy
  | smul d x _ hx =>
      simpa using (a3KeyLayer ρ w (a3KeyShift r k)).smul_mem d hx

theorem a3_cartan_pos_mem_higher (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 2) (r : ℕ) (hr : 0 < r) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    ρ.op (leviH i) r v ∈ a3HigherKeySpan ρ w b c k := by
  exact a3KeyLayer_le_higher ρ w b c k (a3KeyShift r k)
    (a3KeyLess_degree b c k r hr)
    (a3_cartan_pos_maps_key ρ w a b c h i r hr k hv)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_cartan_pos_word_key
#print axioms VOA.DeligneAudit.A3Sector.a3_cartan_pos_maps_key
#print axioms VOA.DeligneAudit.A3Sector.a3_cartan_pos_mem_higher
