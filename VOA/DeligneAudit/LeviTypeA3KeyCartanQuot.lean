import VOA.DeligneAudit.LeviTypeA3KeyCartan

/-! Cartan relations of each radical key vector in its Levi quotient. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_cartan_weight_key_local (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 2) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    ρ.op (leviH i) 0 v = a3KeyLabel b c i k • v := by
  apply a3_cartan_weight_key ρ w b c
  · intro j
    fin_cases j
    · simpa [leviH, simpleH, weightABC] using h.cartan_zero 1
    · simpa [leviH, simpleH, weightABC] using h.cartan_zero 2
  · exact hv

theorem a3_key_cartan_pos_quot (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 2) (r : ℕ) (hr : 0 < r) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    (a3KeyLeviQuotCurrent ρ w b c k).op (if i = 0 then 6 else 7) r
      ((a3HigherLeviClosure ρ w b c k).mkQ v) = 0 := by
  let N := a3HigherLeviClosure ρ w b c k
  have hmem := a3HigherLeviClosure_contains ρ w b c k
    (a3_cartan_pos_mem_higher ρ w a b c h i r hr k hv)
  fin_cases i <;>
    exact (Submodule.Quotient.mk_eq_zero N).mpr hmem

theorem a3_key_cartan_zero_quot (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 2) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    (a3KeyLeviQuotCurrent ρ w b c k).op (if i = 0 then 6 else 7) 0
      ((a3HigherLeviClosure ρ w b c k).mkQ v) =
        a3KeyLabel b c i k • (a3HigherLeviClosure ρ w b c k).mkQ v := by
  have hw := a3_cartan_weight_key_local ρ w a b c h i k hv
  fin_cases i <;>
    simpa [a3KeyLeviQuotCurrent, a3LeviQuotCurrent,
      a3LeviCurrent, a3LeviColour, leviH, map_smul] using
      congrArg (a3HigherLeviClosure ρ w b c k).mkQ hw

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_cartan_weight_key_local
#print axioms VOA.DeligneAudit.A3Sector.a3_key_cartan_pos_quot
#print axioms VOA.DeligneAudit.A3Sector.a3_key_cartan_zero_quot
