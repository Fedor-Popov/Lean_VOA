import VOA.DeligneAudit.LeviTypeA2CertKeyRaising

/-! The node-two raising current kills radical words containing only `F₁`. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- If there is no compound radical letter, every node-two raising mode kills the word. -/
theorem a2_raising_word_zero_no_compound (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (r : ℕ) (l : List (Fin 2 × ℕ))
    (hl : l.countP (fun x => x.1 = 1) = 0) :
    ρ.op 1 r (radicalWord (a2RadicalOp ρ) l • w) = 0 := by
  induction l with
  | nil => simpa [radicalWord] using h.raising 1 (by decide) r
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      have hi : i = 0 := by
        fin_cases i
        · rfl
        · simp at hl
      subst i
      have ht : l.countP (fun x => x.1 = 1) = 0 := by
        simpa using hl
      have hc := a2_raising_simple_comm ρ r s
      have happ := congrArg (fun T : Module.End ℂ V =>
        T (radicalWord (a2RadicalOp ρ) l • w)) hc
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at happ
      change ρ.op 1 r (a2RadicalOp ρ 0 s
        (radicalWord (a2RadicalOp ρ) l • w)) = 0
      rw [sub_eq_iff_eq_add.mp happ, ih ht]
      simp

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_raising_word_zero_no_compound
