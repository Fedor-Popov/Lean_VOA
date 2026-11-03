import VOA.DeligneAudit.LeviTypeA3Higher

/-! Both simple Cartan eigenvalues of a radical key layer. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

/-- The two `sl₃` labels, expressed in the scalar field. -/
def a3KeyLabel (b c : ℕ) (i : Fin 2) (k : A3RadicalKey) : ℂ :=
  if i = 0 then (b : ℂ) + k.d₁ - k.d₂ else (c : ℂ) + k.d₂ - k.d₃

theorem a3KeyLabel_insert (b c : ℕ) (i : Fin 2) (j : Fin 3)
    (s : ℕ) (k : A3RadicalKey) :
    a3KeyLabel b c i (a3KeyInsert j s k) =
      a3KeyLabel b c i k + (leviWeight i j : ℂ) := by
  fin_cases i <;> fin_cases j <;>
    simp [a3KeyLabel, a3KeyInsert, leviWeight] <;> ring

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- A radical word is an eigenvector of both Levi simple Cartan modes. -/
theorem a3_cartan_weight_word (b c : ℕ)
    (h : ∀ i : Fin 2, ρ.op (leviH i) 0 w =
      (if i = 0 then (b : ℂ) else c) • w)
    (i : Fin 2) (l : List (Fin 3 × ℕ)) :
    ρ.op (leviH i) 0 (radicalWord (radicalOp ρ) l • w) =
      a3KeyLabel b c i (a3WordKey l) •
        (radicalWord (radicalOp ρ) l • w) := by
  induction l with
  | nil =>
      simpa [radicalWord, a3WordKey, a3KeyLabel] using h i
  | cons x l ih =>
      rcases x with ⟨j, s⟩
      have hc := levi_cartan_comm ρ i j 0 s
        (radicalWord (radicalOp ρ) l • w)
      change ρ.op (leviH i) 0
        (ρ.op (F j) s (radicalWord (radicalOp ρ) l • w)) = _
      rw [sub_eq_iff_eq_add.mp hc, ih, a3WordKey_cons,
        a3KeyLabel_insert]
      simp only [map_smul, add_smul]
      have hcons : radicalWord (radicalOp ρ) ((j, s) :: l) • w =
          ρ.op (F j) s (radicalWord (radicalOp ρ) l • w) := by
        simp [radicalWord, radicalOp, mul_smul]
      rw [hcons]
      simp only [zero_add]
      abel

/-- Every vector of one key layer has its two prescribed Cartan weights. -/
theorem a3_cartan_weight_key (b c : ℕ)
    (h : ∀ i : Fin 2, ρ.op (leviH i) 0 w =
      (if i = 0 then (b : ℂ) else c) • w)
    (i : Fin 2) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    ρ.op (leviH i) 0 v = a3KeyLabel b c i k • v := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, hd₃, hdeg, _, rfl⟩ := hz
      have hk : a3WordKey l = k := by
        cases k
        simp [a3WordKey, hd₁, hd₂, hd₃, hdeg]
      rw [← hk]
      exact a3_cartan_weight_word ρ w b c h i l
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy, smul_add]
  | smul d x _ hx =>
      rw [map_smul, hx]
      exact smul_comm d (a3KeyLabel b c i k) x

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3KeyLabel_insert
#print axioms VOA.DeligneAudit.A3Sector.a3_cartan_weight_word
#print axioms VOA.DeligneAudit.A3Sector.a3_cartan_weight_key
