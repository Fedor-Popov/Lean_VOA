import VOA.DeligneAudit.LeviTypeA3KeySharp

/-! Negative Levi labels vanish; nonnegative labels give sharp lowering powers. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_key_lowering_sharp_quot (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 2) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    let N := a3HigherLeviClosure ρ w b c k
    let Q := a3KeyLeviQuotCurrent ρ w b c k
    let m := a3KeyLabelInt b c i k
    (m < 0 → N.mkQ v = 0) ∧
      (0 ≤ m → (Q.op (if i = 0 then 3 else 4) 0)^[m.toNat + 1]
        (N.mkQ v) = 0) := by
  dsimp
  let N := a3HigherLeviClosure ρ w b c k
  let Q := a3KeyLeviQuotCurrent ρ w b c k
  let m := a3KeyLabelInt b c i k
  have he : Q.op (if i = 0 then 0 else 1) 0 (N.mkQ v) = 0 := by
    fin_cases i
    · exact a3_key_raising_quot ρ w a b c h 0 0 k hv
    · exact a3_key_raising_quot ρ w a b c h 2 0 k hv
  have hh : Q.op (if i = 0 then 6 else 7) 0 (N.mkQ v) =
      (m : ℂ) • N.mkQ v := by
    rw [a3_key_cartan_zero_quot ρ w a b c h i k hv]
    exact congrArg (fun x : ℂ => x • N.mkQ v)
      (a3KeyLabel_eq_int b c i k)
  have hiter : ∀ j (u : V),
      (Q.op (if i = 0 then 3 else 4) 0)^[j] (N.mkQ u) =
        N.mkQ ((ρ.op (leviF i) 0)^[j] u) := by
    intro j
    induction j with
    | zero => intro u; rfl
    | succ j ih =>
        intro u
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        fin_cases i <;> rfl
  let K := (if i = 0 then b else c) + 1 + 2 * (k.d₁ + k.d₂ + k.d₃)
  have hn : (Q.op (if i = 0 then 3 else 4) 0)^[K] (N.mkQ v) = 0 := by
    rw [hiter, ← Module.End.pow_apply,
      a3_key_lowering_nilpotent ρ w a b c h i k hv]
    exact map_zero _
  exact a3_sl3_simple_hw_pow Q i (N.mkQ v) m K he hh hn

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_key_lowering_sharp_quot
