import VOA.DeligneAudit.LeviTypeA3KeyRaiseBook

/-! Positive Levi modes send each radical word to its raised key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

private theorem source_count (i : Fin 3) (l : List (Fin 3 × ℕ)) :
    l.countP (fun x => x.1 = a3RaiseSource i) =
      if i = 0 then (a3WordKey l).d₂ else (a3WordKey l).d₃ := by
  fin_cases i <;> rfl

theorem a3_raising_word_key (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 3) (r : ℕ) (l : List (Fin 3 × ℕ)) :
    ρ.op (leviE i) r (radicalWord (radicalOp ρ) l • w) ∈
      a3KeyLayer ρ w (a3RaiseKey i r (a3WordKey l)) := by
  induction l with
  | nil =>
      simp [radicalWord, h.raising (leviE i)
        (by fin_cases i <;> decide) r]
  | cons x l ih =>
      rcases x with ⟨j, s⟩
      let u := radicalWord (radicalOp ρ) l • w
      have hc := a3_raising_comm ρ i j r s u
      rw [a3RaiseTarget_eq] at hc
      by_cases hj : j = a3RaiseSource i
      · subst j
        rw [if_pos rfl] at hc
        have hfirst : radicalOp ρ (a3RaiseSource i) s (ρ.op (leviE i) r u) ∈
            a3KeyLayer ρ w
              (a3RaiseKey i r (a3WordKey ((a3RaiseSource i, s) :: l))) := by
          by_cases hz : l.countP (fun x => x.1 = a3RaiseSource i) = 0
          · have hzero : ρ.op (leviE i) r u = 0 :=
              a3_raising_word_zero_no_source ρ w a b c h i r l hz
            rw [hzero, map_zero]
            exact (a3KeyLayer ρ w _).zero_mem
          · have hp : 0 < (if i = 0 then (a3WordKey l).d₂
                else (a3WordKey l).d₃) := by
              rw [← source_count i l]
              omega
            rw [a3WordKey_cons, a3RaiseKey_insert_source i r s _ hp]
            exact a3RadicalOp_maps_key ρ w (a3RaiseSource i) s _ ih
        have hsecond : radicalOp ρ (a3RaiseDest i) (r + s) u ∈
            a3KeyLayer ρ w
              (a3RaiseKey i r (a3WordKey ((a3RaiseSource i, s) :: l))) := by
          rw [a3WordKey_cons, a3RaiseKey_replace]
          exact a3RadicalOp_maps_key ρ w (a3RaiseDest i) (r + s) _
            (a3_radicalWord_mem_own_key ρ w l)
        change ρ.op (leviE i) r (radicalOp ρ (a3RaiseSource i) s u) ∈ _
        rw [sub_eq_iff_eq_add.mp hc]
        exact (a3KeyLayer ρ w _).add_mem hsecond hfirst
      · rw [if_neg hj] at hc
        have hfirst : radicalOp ρ j s (ρ.op (leviE i) r u) ∈
            a3KeyLayer ρ w (a3RaiseKey i r (a3WordKey ((j, s) :: l))) := by
          rw [a3WordKey_cons, a3RaiseKey_insert_other i j r s _ hj]
          exact a3RadicalOp_maps_key ρ w j s _ ih
        change ρ.op (leviE i) r (radicalOp ρ j s u) ∈ _
        rw [sub_eq_zero.mp hc]
        exact hfirst

theorem a3_raising_maps_key (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 3) (r : ℕ) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    ρ.op (leviE i) r v ∈ a3KeyLayer ρ w (a3RaiseKey i r k) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, hd₃, hdeg, _, rfl⟩ := hz
      have hk : a3WordKey l = k := by
        cases k
        simp [a3WordKey, hd₁, hd₂, hd₃, hdeg]
      rw [← hk]
      exact a3_raising_word_key ρ w a b c h i r l
  | zero => simp
  | add x y _ _ hx hy =>
      simpa using (a3KeyLayer ρ w (a3RaiseKey i r k)).add_mem hx hy
  | smul d x _ hx =>
      simpa using (a3KeyLayer ρ w (a3RaiseKey i r k)).smul_mem d hx

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_raising_word_key
#print axioms VOA.DeligneAudit.A3Sector.a3_raising_maps_key
