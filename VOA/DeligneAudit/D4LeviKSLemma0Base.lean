import VOA.DeligneAudit.D4LeviKSLemma0Deriv

/-! The XYZ target and the zero-U base of the D4 Lemma 0 induction. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- Exact-key words using only X, Y, and Z, expressed by zero excluded counts. -/
def xyzSpan (k : RadicalKey) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ l : List (Fin 6 × ℕ),
    wordKey l = k ∧
    l.countP (fun p => p.1 = 0) = 0 ∧
    l.countP (fun p => p.1 = 2) = 0 ∧
    l.countP (fun p => p.1 = 3) = 0 ∧
    v = radicalWord ρ w l}

theorem xyzSpan_le_keyLayer (k : RadicalKey) :
    xyzSpan ρ w k ≤ keyLayer ρ w k := by
  rw [xyzSpan, Submodule.span_le]
  rintro v ⟨l, hk, _, _, _, rfl⟩
  exact Submodule.subset_span ⟨l, hk, rfl⟩

/-- If the key has no E, U, or U', every word of the key is an XYZ word. -/
theorem keyLayer_le_xyzSpan_of_no_excluded (k : RadicalKey)
    (he : k.e = 0) (hu : k.u = 0) (hup : k.up = 0) :
    keyLayer ρ w k ≤ xyzSpan ρ w k := by
  rw [keyLayer, Submodule.span_le]
  rintro v ⟨l, hk, rfl⟩
  apply Submodule.subset_span
  refine ⟨l, hk, ?_, ?_, ?_, rfl⟩
  · simpa [← hk, wordKey] using he
  · simpa [← hk, wordKey] using hu
  · simpa [← hk, wordKey] using hup

/-- The zero-U, zero-U' base: any E letters annihilate the source. -/
theorem keyLayer_le_xyzSpan_of_no_U
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hu : k.u = 0) (hup : k.up = 0) :
    keyLayer ρ w k ≤ xyzSpan ρ w k := by
  by_cases he : k.e = 0
  · exact keyLayer_le_xyzSpan_of_no_excluded ρ w k he hu hup
  · have hpos : 0 < k.e := Nat.pos_of_ne_zero he
    rw [keyLayer_eq_bot_of_E ρ w m h k hpos]
    exact bot_le

/-- The first and third sl4 labels agree precisely at a symmetric U/U' key. -/
theorem keyLabel_symmetric_iff (k : RadicalKey) :
    keyLabel m 0 k = keyLabel m 2 k ↔ k.u = k.up := by
  simp [keyLabel]
  omega

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyzSpan_le_keyLayer
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_le_xyzSpan_of_no_excluded
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_le_xyzSpan_of_no_U
#print axioms VOA.DeligneAudit.D4Levi.keyLabel_symmetric_iff
