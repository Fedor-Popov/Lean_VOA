import VOA.DeligneAudit.LeviTypeA2CertF2Conversion

/-! Radical count spans, ignoring mode degree. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA
open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The span of all radical keys with fixed colour counts. -/
def a2CountSpan (a b : ℕ) : Submodule ℂ V :=
  ⨆ d : ℕ, a2KeyLayer ρ w ⟨a, b, d⟩

theorem a2CountSpan_first (a b s : ℕ) {v : V}
    (hv : v ∈ a2CountSpan ρ w a b) :
    ρ.op 3 s v ∈ a2CountSpan ρ w (a + 1) b := by
  refine Submodule.iSup_induction
    (p := fun d : ℕ => a2KeyLayer ρ w ⟨a, b, d⟩)
    (motive := fun v => ρ.op 3 s v ∈ a2CountSpan ρ w (a + 1) b)
    hv ?_ ?_ ?_
  · intro d v hvd
    have h := a2RadicalOp_maps_key ρ w 0 s ⟨a, b, d⟩ hvd
    simpa [a2CountSpan, a2RadicalOp, a2KeyInsert, Nat.add_comm] using
      (le_iSup (fun d : ℕ => a2KeyLayer ρ w ⟨a + 1, b, d⟩) (d + s) h)
  · simp
  · intro x y hx hy
    simpa only [map_add] using (a2CountSpan ρ w (a + 1) b).add_mem hx hy

theorem a2CountSpan_second (a b s : ℕ) {v : V}
    (hv : v ∈ a2CountSpan ρ w a b) :
    ρ.op 5 s v ∈ a2CountSpan ρ w a (b + 1) := by
  refine Submodule.iSup_induction
    (p := fun d : ℕ => a2KeyLayer ρ w ⟨a, b, d⟩)
    (motive := fun v => ρ.op 5 s v ∈ a2CountSpan ρ w a (b + 1))
    hv ?_ ?_ ?_
  · intro d v hvd
    have h := a2RadicalOp_maps_key ρ w 1 s ⟨a, b, d⟩ hvd
    simpa [a2CountSpan, a2RadicalOp, a2KeyInsert, Nat.add_comm] using
      (le_iSup (fun d : ℕ => a2KeyLayer ρ w ⟨a, b + 1, d⟩) (d + s) h)
  · simp
  · intro x y hx hy
    simpa only [map_add] using (a2CountSpan ρ w a (b + 1)).add_mem hx hy

theorem a2CountSpan_zero : w ∈ a2CountSpan ρ w 0 0 := by
  have h := radicalWord_mem_own_key ρ w ([] : List (Fin 2 × ℕ))
  exact (le_iSup (fun d : ℕ => a2KeyLayer ρ w ⟨0, 0, d⟩) 0
    (by simpa [a2WordKey, radicalWord] using h))

theorem a2CountSpan_second_word (ys : List ℕ) (a b : ℕ) {v : V}
    (hv : v ∈ a2CountSpan ρ w a b) :
    (ys.map fun i => ρ.op 5 i).prod v ∈
      a2CountSpan ρ w a (b + ys.length) := by
  induction ys with
  | nil => simpa using hv
  | cons y ys ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    have h := a2CountSpan_second ρ w a (b + ys.length) y ih
    simpa only [List.length_cons] using (show
      ρ.op 5 y ((ys.map fun i => ρ.op 5 i).prod v) ∈
        a2CountSpan ρ w a (b + (ys.length + 1)) by
      convert h using 1)

theorem a2CountSpan_first_word (xs : List ℕ) (a b : ℕ) {v : V}
    (hv : v ∈ a2CountSpan ρ w a b) :
    (xs.map fun i => ρ.op 3 i).prod v ∈
      a2CountSpan ρ w (a + xs.length) b := by
  induction xs with
  | nil => simpa using hv
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    have h := a2CountSpan_first ρ w (a + xs.length) b x ih
    convert h using 1

theorem a2CountSpan_le_higher (q : ℕ) (k : A2RadicalKey)
    (a b : ℕ) (h : a2KeyHeight q k < (q : ℤ) + a - b) :
    a2CountSpan ρ w a b ≤ a2HigherKeySpan ρ w q k := by
  rw [a2CountSpan, iSup_le_iff]
  intro d
  exact le_iSup_of_le ⟨a, b, d⟩
    (le_iSup_of_le (Or.inl (by simpa [a2KeyHeight] using h)) le_rfl)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2CountSpan_first
#print axioms VOA.DeligneAudit.A3Sector.a2CountSpan_second
#print axioms VOA.DeligneAudit.A3Sector.a2CountSpan_zero
#print axioms VOA.DeligneAudit.A3Sector.a2CountSpan_second_word
#print axioms VOA.DeligneAudit.A3Sector.a2CountSpan_first_word
#print axioms VOA.DeligneAudit.A3Sector.a2CountSpan_le_higher
