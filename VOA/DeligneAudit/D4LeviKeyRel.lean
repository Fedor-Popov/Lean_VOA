import VOA.DeligneAudit.D4LeviKeySharp

/-! Each dominant key vector obeys the full sl4 local Weyl relations. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

def keyWeight (m : ℕ) (k : RadicalKey) (i : Fin 3) : ℕ :=
  (keyLabel m i k).toNat

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem key_localWeyl_quot
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hdom : ∀ i : Fin 3, 0 ≤ keyLabel m i k)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    VOA.DeligneAudit.A3Sector.LocalWeylRel
      (keyQuotCurrent ρ w m k) ((higherOrbit ρ w m k).mkQ v)
      (keyWeight m k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he r
    exact key_all_raise_quot ρ w m h k hv e he r
  · intro i r hr
    exact key_cartan_pos_quot ρ w m h i r hr k hv
  · intro i
    have hh := key_cartan_zero_quot ρ w m h i k hv
    have heq : ((keyLabel m i k).toNat : ℂ) =
        (keyLabel m i k : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg (hdom i))
    change (keyQuotCurrent ρ w m k).op
      (VOA.DeligneAudit.A3Sector.simpleH i) 0
        ((higherOrbit ρ w m k).mkQ v) =
          ((keyLabel m i k).toNat : ℂ) • (higherOrbit ρ w m k).mkQ v
    rw [heq]
    exact hh
  · intro i
    have hh := (key_simple_sharp_quot ρ w m h i k hv).2 (hdom i)
    simpa [keyWeight] using hh

theorem key_vector_rank
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hdom : ∀ i : Fin 3, 0 ≤ keyLabel m i k)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    let Q := keyQuotCurrent ρ w m k
    let x := (higherOrbit ρ w m k).mkQ v
    FiniteDimensional ℂ (cycSubG Q x) ∧
      Module.finrank ℂ (cycSubG Q x) ≤
        4 ^ keyWeight m k 0 * 6 ^ keyWeight m k 1 *
          4 ^ keyWeight m k 2 := by
  dsimp
  let a := keyWeight m k 0
  let b := keyWeight m k 1
  let c := keyWeight m k 2
  have hw : keyWeight m k = VOA.DeligneAudit.A3Sector.weightABC a b c := by
    funext i
    fin_cases i <;> rfl
  have hrel := key_localWeyl_quot ρ w m h k hdom hv
  rw [hw] at hrel
  simpa [a, b, c] using VOA.DeligneAudit.A3Sector.a3_all_weight_rank
    (keyQuotCurrent ρ w m k) ((higherOrbit ρ w m k).mkQ v)
    a b c hrel

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.key_localWeyl_quot
#print axioms VOA.DeligneAudit.D4Levi.key_vector_rank
