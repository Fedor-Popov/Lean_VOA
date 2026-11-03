import VOA.DeligneAudit.D4LeviKSMixedCartan

/-! Iterated selective Cartan shifts of the graded XZG and YZG relations. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- Choice of one of the three Cartan directions separating X, Y and Z. -/
noncomputable def selectiveCartan (i : Fin 3) (r : ℕ) : Module.End ℂ V :=
  if i = 0 then xShiftCartan ρ r else
    if i = 1 then yShiftCartan ρ r else zShiftCartan ρ r

/-- The action of an ordered list of selected Cartan modes. -/
noncomputable def selectiveCartanWord : List (Fin 3 × ℕ) → V → V
  | [], v => v
  | p :: ps, v => selectiveCartan ρ p.1 p.2 (selectiveCartanWord ps v)

private theorem cartanBlend_higher (a b c : ℂ) (r : ℕ) (k : RadicalKey)
    {v : V} (hv : v ∈ higherOrbit ρ w m k) :
    cartanBlend ρ a b c r v ∈ higherOrbit ρ w m k := by
  let N := higherOrbit ρ w m k
  have h0 := higherOrbit_full_levi_inv ρ w m k
    (leviColour (VOA.DeligneAudit.A3Sector.simpleH 0))
    (leviColour_isLevi _) r hv
  have h1 := higherOrbit_full_levi_inv ρ w m k
    (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1))
    (leviColour_isLevi _) r hv
  have he := higherOrbit_extra_inv ρ w m k r hv
  change a • ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 0)) r v +
      b • ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r v +
      c • ρ.op (0 : Fin 28) r v ∈ N
  exact N.add_mem (N.add_mem (N.smul_mem a h0) (N.smul_mem b h1))
    (N.smul_mem c he)

theorem selectiveCartan_higher (i : Fin 3) (r : ℕ) (k : RadicalKey)
    {v : V} (hv : v ∈ higherOrbit ρ w m k) :
    selectiveCartan ρ i r v ∈ higherOrbit ρ w m k := by
  fin_cases i
  · exact cartanBlend_higher ρ w m 1 0 (-1) r k hv
  · exact cartanBlend_higher ρ w m (-1) 0 (-1) r k hv
  · exact cartanBlend_higher ρ w m (-1) (-1) 0 r k hv

theorem selectiveCartanWord_higher (ps : List (Fin 3 × ℕ))
    (k : RadicalKey) {v : V} (hv : v ∈ higherOrbit ρ w m k) :
    selectiveCartanWord ρ ps v ∈ higherOrbit ρ w m k := by
  induction ps with
  | nil => exact hv
  | cons p ps ih =>
      exact selectiveCartan_higher ρ w m p.1 p.2 k ih

/-- Every ordered sequence of Cartan power-sum shifts preserves XZG(b). -/
theorem xz_cartan_shifted_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs ys : List ℕ) (c s i : ℕ) (ps : List (Fin 3 × ℕ))
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey (List.replicate rs.length 0) ys [] c
        (rs.sum + ys.sum + s)) :
    selectiveCartanWord ρ ps
      (mixedTop (yOp ρ) (zOp ρ) c s (ys ++ List.replicate c 0)
        (rs.map (transportCurrent (xOp ρ))).prod w) ∈
      keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  exact selectiveCartanWord_higher ρ w m ps _
    (xz_full_contractions_higher ρ w m h rs ys c s hK hks)

/-- Every ordered sequence of Cartan power-sum shifts preserves YZG(b). -/
theorem yz_cartan_shifted_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs xs : List ℕ) (c s i : ℕ) (ps : List (Fin 3 × ℕ))
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs (List.replicate rs.length 0) [] c
        (rs.sum + xs.sum + s)) :
    selectiveCartanWord ρ ps
      (mixedTop (xOp ρ) (zOp ρ) c s (xs ++ List.replicate c 0)
        (rs.map (transportCurrent (yOp ρ))).prod w) ∈
      keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  exact selectiveCartanWord_higher ρ w m ps _
    (yz_full_contractions_higher ρ w m h rs xs c s hK hks)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.selectiveCartan_higher
#print axioms VOA.DeligneAudit.D4Levi.selectiveCartanWord_higher
#print axioms VOA.DeligneAudit.D4Levi.xz_cartan_shifted_prefix
#print axioms VOA.DeligneAudit.D4Levi.yz_cartan_shifted_prefix
