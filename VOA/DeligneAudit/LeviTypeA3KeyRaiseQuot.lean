import VOA.DeligneAudit.LeviTypeA3KeyRaiseWord

/-! Every positive Levi mode kills a key vector modulo higher keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_raising_zero_no_source (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 3) (r : ℕ) (k : A3RadicalKey)
    (hk : (if i = 0 then k.d₂ else k.d₃) = 0)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    ρ.op (leviE i) r v = 0 := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, hd₃, _, _, rfl⟩ := hz
      apply a3_raising_word_zero_no_source ρ w a b c h i r l
      fin_cases i
      · change l.countP (fun x => x.1 = (1 : Fin 3)) = 0
        exact hd₂.trans (by simpa using hk)
      · change l.countP (fun x => x.1 = (2 : Fin 3)) = 0
        exact hd₃.trans (by simpa using hk)
      · change l.countP (fun x => x.1 = (2 : Fin 3)) = 0
        exact hd₃.trans (by simpa using hk)
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul d x _ hx => simp [map_smul, hx]

theorem a3_raising_mem_higher (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 3) (r : ℕ) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    ρ.op (leviE i) r v ∈ a3HigherKeySpan ρ w b c k := by
  by_cases hk : (if i = 0 then k.d₂ else k.d₃) = 0
  · rw [a3_raising_zero_no_source ρ w a b c h i r k hk hv]
    exact (a3HigherKeySpan ρ w b c k).zero_mem
  · have hp : 0 < (if i = 0 then k.d₂ else k.d₃) := by omega
    exact a3KeyLayer_le_higher ρ w b c k (a3RaiseKey i r k)
      (a3RaiseKey_less b c i r k hp)
      (a3_raising_maps_key ρ w a b c h i r k hv)

theorem a3_key_raising_quot (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 3) (r : ℕ) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    (a3KeyLeviQuotCurrent ρ w b c k).op
      (if i = 0 then 0 else if i = 1 then 2 else 1) r
      ((a3HigherLeviClosure ρ w b c k).mkQ v) = 0 := by
  have hmem := a3HigherLeviClosure_contains ρ w b c k
    (a3_raising_mem_higher ρ w a b c h i r k hv)
  fin_cases i <;>
    exact (Submodule.Quotient.mk_eq_zero _).mpr hmem

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_raising_zero_no_source
#print axioms VOA.DeligneAudit.A3Sector.a3_raising_mem_higher
#print axioms VOA.DeligneAudit.A3Sector.a3_key_raising_quot
