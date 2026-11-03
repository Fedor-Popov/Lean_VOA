import VOA.DeligneAudit.LeviTypeA3ConversionGraded
import VOA.DeligneAudit.LeviTypeA3Higher

/-! Radical count spans used to absorb lower Wick terms. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

def a3CountSpan (d₁ d₂ d₃ : ℕ) : Submodule ℂ V :=
  ⨆ degree : ℕ, a3KeyLayer ρ w ⟨d₁, d₂, d₃, degree⟩

theorem a3KeyLayer_le_count (d₁ d₂ d₃ degree : ℕ) :
    a3KeyLayer ρ w ⟨d₁, d₂, d₃, degree⟩ ≤
      a3CountSpan ρ w d₁ d₂ d₃ := by
  exact le_iSup_of_le degree le_rfl

theorem a3CountSpan_zero : w ∈ a3CountSpan ρ w 0 0 0 := by
  apply a3KeyLayer_le_count ρ w 0 0 0 0
  simpa [radicalWord] using
    a3_radicalWord_mem_own_key ρ w ([] : List (Fin 3 × ℕ))

theorem a3CountSpan_op (i : Fin 3) (s d₁ d₂ d₃ : ℕ)
    {v : V} (hv : v ∈ a3CountSpan ρ w d₁ d₂ d₃) :
    ρ.op (F i) s v ∈
      a3CountSpan ρ w
        (d₁ + if i = 0 then 1 else 0)
        (d₂ + if i = 1 then 1 else 0)
        (d₃ + if i = 2 then 1 else 0) := by
  have hop : a3CountSpan ρ w d₁ d₂ d₃ ≤
      (a3CountSpan ρ w
        (d₁ + if i = 0 then 1 else 0)
        (d₂ + if i = 1 then 1 else 0)
        (d₃ + if i = 2 then 1 else 0)).comap (ρ.op (F i) s) := by
    rw [a3CountSpan, iSup_le_iff]
    intro degree v hdegree
    apply a3KeyLayer_le_count ρ w _ _ _ (degree + s)
    simpa [a3KeyInsert, radicalOp] using
      a3RadicalOp_maps_key ρ w i s ⟨d₁, d₂, d₃, degree⟩ hdegree
  exact hop hv

theorem a3CountSpan_word (i : Fin 3) (xs : List ℕ)
    (d₁ d₂ d₃ : ℕ) {v : V}
    (hv : v ∈ a3CountSpan ρ w d₁ d₂ d₃) :
    (xs.map fun s => ρ.op (F i) s).prod v ∈
      a3CountSpan ρ w
        (d₁ + if i = 0 then xs.length else 0)
        (d₂ + if i = 1 then xs.length else 0)
        (d₃ + if i = 2 then xs.length else 0) := by
  induction xs generalizing d₁ d₂ d₃ v with
  | nil => simpa using hv
  | cons s xs ih =>
      have h := a3CountSpan_op ρ w i s _ _ _ (ih d₁ d₂ d₃ hv)
      fin_cases i <;>
        simpa [List.map_cons, List.prod_cons, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using h

theorem a3CountSpan_le_higher (b c : ℕ) (k : A3RadicalKey)
    (d₁ d₂ d₃ : ℕ)
    (hheight : a3KeyHeight b c k <
      (b : ℤ) + c + d₁ - d₃) :
    a3CountSpan ρ w d₁ d₂ d₃ ≤
      a3HigherLeviClosure ρ w b c k := by
  rw [a3CountSpan, iSup_le_iff]
  intro degree
  apply (a3HigherLeviClosure_contains ρ w b c k).trans'
  exact a3KeyLayer_le_higher ρ w b c k ⟨d₁, d₂, d₃, degree⟩
    (Or.inl hheight)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3CountSpan_zero
#print axioms VOA.DeligneAudit.A3Sector.a3CountSpan_op
#print axioms VOA.DeligneAudit.A3Sector.a3CountSpan_word
#print axioms VOA.DeligneAudit.A3Sector.a3CountSpan_le_higher
