import VOA.DeligneAudit.LeviTypeA2CertOtherCartan

/-! The zero mode of the other Cartan current is scalar on a key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

private def otherWeight (p : ℕ) (l : List (Fin 2 × ℕ)) : ℂ :=
  (p : ℂ) - 2 * (l.countP fun x => x.1 = 0 : ℕ) -
    (l.countP fun x => x.1 = 1 : ℕ)

private theorem otherWeight_cons (p : ℕ) (i : Fin 2) (s : ℕ)
    (l : List (Fin 2 × ℕ)) :
    otherWeight p ((i, s) :: l) =
      (if i = 0 then (-2 : ℂ) else -1) + otherWeight p l := by
  fin_cases i <;> simp [otherWeight] <;> ring

/-- A radical word has the prescribed `h₁` weight. -/
theorem a2_other_cartan_weight_word (p : ℕ)
    (h : ρ.op 6 0 w = (p : ℂ) • w)
    (l : List (Fin 2 × ℕ)) :
    ρ.op 6 0 (radicalWord (a2RadicalOp ρ) l • w) =
      otherWeight p l • (radicalWord (a2RadicalOp ρ) l • w) := by
  induction l with
  | nil => simpa [radicalWord, otherWeight] using h
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      have hc := other_cartan_radical_comm ρ i 0 s
      have happ := congrArg (fun T : Module.End ℂ V =>
        T (radicalWord (a2RadicalOp ρ) l • w)) hc
      simp only [LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply] at happ
      change ρ.op 6 0 (a2RadicalOp ρ i s
        (radicalWord (a2RadicalOp ρ) l • w)) = _
      rw [sub_eq_iff_eq_add.mp happ, ih]
      rw [otherWeight_cons]
      simp only [map_smul, add_smul]
      simp only [radicalWord, Nat.zero_add]
      abel

/-- The whole key layer is an `h₁` eigenspace. -/
theorem a2_other_cartan_weight_key (p : ℕ) (k : A2RadicalKey)
    (h : ρ.op 6 0 w = (p : ℂ) • w)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    ρ.op 6 0 v =
      ((p : ℂ) - 2 * (k.d₁ : ℂ) - (k.d₂ : ℂ)) • v := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, _, _, rfl⟩ := hz
      simpa only [otherWeight, hd₁, hd₂] using
        a2_other_cartan_weight_word ρ w p h l
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy, smul_add]
  | smul c x _ hx =>
      rw [map_smul, hx]
      exact smul_comm c ((p : ℂ) - 2 * (k.d₁ : ℂ) - (k.d₂ : ℂ)) x

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_other_cartan_weight_word
#print axioms VOA.DeligneAudit.A3Sector.a2_other_cartan_weight_key
