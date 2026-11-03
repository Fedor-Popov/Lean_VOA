import VOA.DeligneAudit.LeviTypeA2CertCompoundNil

/-! Node-two Cartan eigenvalues of individual radical words. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

private theorem node2_radical_comm (i : Fin 2) (s : ℕ) :
    ρ.op 7 0 * a2RadicalOp ρ i s -
      a2RadicalOp ρ i s * ρ.op 7 0 =
        (if i = 0 then (1 : ℂ) else -1) • a2RadicalOp ρ i s := by
  fin_cases i <;>
    simp [a2RadicalOp, op_comm_end, Fin.sum_univ_eight,
      VOA.AffineSl3.bracketTable]

private def radicalWeight (q : ℕ) (l : List (Fin 2 × ℕ)) : ℂ :=
  (q : ℂ) + (l.countP fun x => x.1 = 0 : ℕ) -
    (l.countP fun x => x.1 = 1 : ℕ)

private theorem radicalWeight_cons (q : ℕ) (i : Fin 2) (s : ℕ)
    (l : List (Fin 2 × ℕ)) :
    radicalWeight q ((i, s) :: l) =
      (if i = 0 then (1 : ℂ) else -1) + radicalWeight q l := by
  fin_cases i <;> simp [radicalWeight] <;> ring

/-- A radical word has node-two weight `q + d₁ - d₂`. -/
theorem a2_node2_weight_word (q : ℕ)
    (h : ρ.op 7 0 w = (q : ℂ) • w)
    (l : List (Fin 2 × ℕ)) :
    ρ.op 7 0 (radicalWord (a2RadicalOp ρ) l • w) =
      radicalWeight q l • (radicalWord (a2RadicalOp ρ) l • w) := by
  induction l with
  | nil => simpa [radicalWord, radicalWeight] using h
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      have hc := node2_radical_comm ρ i s
      have happ := congrArg (fun T : Module.End ℂ V =>
        T (radicalWord (a2RadicalOp ρ) l • w)) hc
      simp only [LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply] at happ
      change ρ.op 7 0 (a2RadicalOp ρ i s
        (radicalWord (a2RadicalOp ρ) l • w)) = _
      rw [sub_eq_iff_eq_add.mp happ, ih]
      rw [radicalWeight_cons]
      simp only [map_smul, add_smul]
      abel

/-- Every generator of a fixed key layer has the prescribed Cartan weight. -/
theorem a2_node2_weight_key_generator (q : ℕ) (k : A2RadicalKey)
    (h : ρ.op 7 0 w = (q : ℂ) • w)
    (l : List (Fin 2 × ℕ))
    (hd₁ : l.countP (fun x => x.1 = 0) = k.d₁)
    (hd₂ : l.countP (fun x => x.1 = 1) = k.d₂) :
    ρ.op 7 0 (radicalWord (a2RadicalOp ρ) l • w) =
      ((q : ℂ) + (k.d₁ : ℂ) - (k.d₂ : ℂ)) •
        (radicalWord (a2RadicalOp ρ) l • w) := by
  simpa only [radicalWeight, hd₁, hd₂] using
    a2_node2_weight_word ρ w q h l

/-- The whole key layer is a node-two Cartan eigenspace. -/
theorem a2_node2_weight_key (q : ℕ) (k : A2RadicalKey)
    (h : ρ.op 7 0 w = (q : ℂ) • w)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    ρ.op 7 0 v = ((q : ℂ) + (k.d₁ : ℂ) - (k.d₂ : ℂ)) • v := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, _, _, rfl⟩ := hz
      exact a2_node2_weight_key_generator ρ w q k h l hd₁ hd₂
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy, smul_add]
  | smul c x _ hx =>
      rw [map_smul, hx]
      exact smul_comm c ((q : ℂ) + (k.d₁ : ℂ) - (k.d₂ : ℂ)) x

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_node2_weight_word
#print axioms VOA.DeligneAudit.A3Sector.a2_node2_weight_key_generator
#print axioms VOA.DeligneAudit.A3Sector.a2_node2_weight_key
