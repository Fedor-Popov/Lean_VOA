import VOA.DeligneAudit.LeviTypeA3OrderedStepRank

/-! The omitted node-one Cartan zero mode is scalar on every radical key layer. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

/-- The node-one Cartan weights of the three radical colours. -/
def a3ExtraWeight : Fin 3 → ℤ
  | 0 => -2
  | 1 => -1
  | 2 => -1

theorem a3_extra_cartan_table (j : Fin 3) (x : Fin 15) :
    bracketTable 12 (F j) x =
      if x = F j then (a3ExtraWeight j : ℂ) else 0 := by
  have ht : bracketInt 12 (F j) x =
      if x = F j then a3ExtraWeight j else 0 := by
    fin_cases j <;> fin_cases x <;> decide
  simp [bracketTable, ht]

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_extra_cartan_comm (j : Fin 3) (r s : ℕ) (v : V) :
    ρ.op 12 r (radicalOp ρ j s v) -
      radicalOp ρ j s (ρ.op 12 r v) =
        (a3ExtraWeight j : ℂ) • radicalOp ρ j (r + s) v := by
  rw [radicalOp, ρ.comm]
  simp [a3_extra_cartan_table, radicalOp]

/-- The node-one Cartan scalar on a fixed radical key. -/
def a3ExtraKeyLabel (a : ℕ) (k : A3RadicalKey) : ℂ :=
  (a : ℂ) - 2 * k.d₁ - k.d₂ - k.d₃

theorem a3ExtraKeyLabel_insert (a : ℕ) (j : Fin 3) (s : ℕ)
    (k : A3RadicalKey) :
    a3ExtraKeyLabel a (a3KeyInsert j s k) =
      a3ExtraKeyLabel a k + (a3ExtraWeight j : ℂ) := by
  fin_cases j <;> simp [a3ExtraKeyLabel, a3KeyInsert, a3ExtraWeight] <;> ring

theorem a3_extra_cartan_weight_word (a : ℕ)
    (hw : ρ.op 12 0 w = (a : ℂ) • w)
    (l : List (Fin 3 × ℕ)) :
    ρ.op 12 0 (radicalWord (radicalOp ρ) l • w) =
      a3ExtraKeyLabel a (a3WordKey l) •
        (radicalWord (radicalOp ρ) l • w) := by
  induction l with
  | nil => simpa [radicalWord, a3WordKey, a3ExtraKeyLabel] using hw
  | cons x l ih =>
      rcases x with ⟨j, s⟩
      have hc := a3_extra_cartan_comm ρ j 0 s
        (radicalWord (radicalOp ρ) l • w)
      change ρ.op 12 0
        (radicalOp ρ j s (radicalWord (radicalOp ρ) l • w)) = _
      rw [sub_eq_iff_eq_add.mp hc, ih, a3WordKey_cons,
        a3ExtraKeyLabel_insert]
      simp only [map_smul, add_smul]
      have hcons : radicalWord (radicalOp ρ) ((j, s) :: l) • w =
          radicalOp ρ j s (radicalWord (radicalOp ρ) l • w) := by
        simp [radicalWord, radicalOp, mul_smul]
      rw [hcons]
      simp only [Nat.zero_add]
      abel

theorem a3_extra_cartan_weight_key (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (k : A3RadicalKey) {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    ρ.op 12 0 v = a3ExtraKeyLabel a k • v := by
  have hw : ρ.op 12 0 w = (a : ℂ) • w := by
    simpa [simpleH, weightABC] using h.cartan_zero 0
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, hd₃, hdeg, _, rfl⟩ := hz
      have hk : a3WordKey l = k := by
        cases k
        simp [a3WordKey, hd₁, hd₂, hd₃, hdeg]
      rw [← hk]
      exact a3_extra_cartan_weight_word ρ w a hw l
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy, smul_add]
  | smul d x _ hx =>
      rw [map_smul, hx]
      exact smul_comm d (a3ExtraKeyLabel a k) x

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_extra_cartan_table
#print axioms VOA.DeligneAudit.A3Sector.a3_extra_cartan_comm
#print axioms VOA.DeligneAudit.A3Sector.a3ExtraKeyLabel_insert
#print axioms VOA.DeligneAudit.A3Sector.a3_extra_cartan_weight_word
#print axioms VOA.DeligneAudit.A3Sector.a3_extra_cartan_weight_key
