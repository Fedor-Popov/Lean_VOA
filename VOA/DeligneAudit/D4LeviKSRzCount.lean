import VOA.DeligneAudit.D4LeviKSRzSingle

/-! Exact XYZ count spans for absorption of lower Rz Wick contractions. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The span of radical XYZ words with fixed letter counts and unrestricted mode degree. -/
def xyzCountSpan (x y z : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ l : List (Fin 6 × ℕ),
    l.countP (fun p => p.1 = 0) = 0 ∧
    l.countP (fun p => p.1 = 1) = x ∧
    l.countP (fun p => p.1 = 2) = 0 ∧
    l.countP (fun p => p.1 = 3) = 0 ∧
    l.countP (fun p => p.1 = 4) = y ∧
    l.countP (fun p => p.1 = 5) = z ∧
    v = radicalWord ρ w l}

theorem xyzCountSpan_zero : w ∈ xyzCountSpan ρ w 0 0 0 := by
  apply Submodule.subset_span
  exact ⟨[], by simp, by simp, by simp, by simp, by simp, by simp, rfl⟩

theorem xyzCountSpan_op (j : Fin 6) (r x y z : ℕ)
    (hj : j = 1 ∨ j = 4 ∨ j = 5)
    {v : V} (hv : v ∈ xyzCountSpan ρ w x y z) :
    ρ.op (radicalColour j) r v ∈
      xyzCountSpan ρ w (x + if j = 1 then 1 else 0)
        (y + if j = 4 then 1 else 0)
        (z + if j = 5 then 1 else 0) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, he, hx, hu, hup, hy, hz, rfl⟩ := hv
      apply Submodule.subset_span
      refine ⟨(j, r) :: l, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals rcases hj with h | h | h
      all_goals subst j
      all_goals simp [he, hx, hu, hup, hy, hz, radicalWord, wordOp]
  | zero => simp
  | add a b _ _ ha hb => simpa using
      (xyzCountSpan ρ w _ _ _).add_mem ha hb
  | smul c a _ ha => simpa using
      (xyzCountSpan ρ w _ _ _).smul_mem c ha

/-- A fixed XYZ count with greater Levi height lies in the higher-key orbit. -/
theorem xyzCountSpan_le_higher (x y z : ℕ) (k : RadicalKey)
    (hh : keyHeight m k < 4 * (m : ℤ) + 2 * x - 2 * y - 4 * z) :
    xyzCountSpan ρ w x y z ≤ higherOrbit ρ w m k := by
  rw [xyzCountSpan, Submodule.span_le]
  rintro v ⟨l, he, hx, hu, hup, hy, hz, rfl⟩
  have hless : keyLess m k (wordKey l) := by
    left
    simpa [keyHeight, wordKey, he, hx, hu, hup, hy, hz] using hh
  exact keyOrbit_le_higher ρ w m k (wordKey l) hless
    (keyLayer_le_orbit ρ w (wordKey l) (radicalWord_mem_key ρ w l))

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyzCountSpan_zero
#print axioms VOA.DeligneAudit.D4Levi.xyzCountSpan_op
#print axioms VOA.DeligneAudit.D4Levi.xyzCountSpan_le_higher
