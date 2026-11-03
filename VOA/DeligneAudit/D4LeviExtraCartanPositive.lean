import VOA.DeligneAudit.D4LeviExtraCartanWeight

/-! Positive modes of the extra Cartan colour move a key to higher degree. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem source_extra_pos
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (hr : 0 < r) : ρ.op (0 : Fin 28) r w = 0 := by
  have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
    simpa [ravFam] using h
  exact rs_cartan_pos hs
    (by change (0 : Fin 28).val < 4; decide : D4sector.cartan (0 : Fin 28))
    r hr

theorem extra_pos_word
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (hr : 0 < r) (l : List (Fin 6 × ℕ)) :
    ρ.op (0 : Fin 28) r (radicalWord ρ w l) ∈
      keyLayer ρ w (keyShift r (wordKey l)) := by
  induction l with
  | nil =>
      change ρ.op (0 : Fin 28) r w ∈ _
      rw [source_extra_pos ρ w m h r hr]
      exact Submodule.zero_mem _
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      let u := radicalWord ρ w l
      have hc := extra_comm ρ j r s u
      have hfirst : ρ.op (radicalColour j) s (ρ.op (0 : Fin 28) r u) ∈
          keyLayer ρ w (keyShift r (wordKey ((j, s) :: l))) := by
        rw [wordKey_cons, keyShift_insert]
        exact radical_op_maps_key ρ w j s (keyShift r (wordKey l)) ih
      have hsecond : ρ.op (radicalColour j) (r + s) u ∈
          keyLayer ρ w (keyShift r (wordKey ((j, s) :: l))) := by
        rw [wordKey_cons, keyShift_insert_mode]
        exact radical_op_maps_key ρ w j (r + s) (wordKey l)
          (radicalWord_mem_key ρ w l)
      change ρ.op (0 : Fin 28) r (ρ.op (radicalColour j) s u) ∈ _
      rw [sub_eq_iff_eq_add.mp hc]
      exact (keyLayer ρ w _).add_mem
        ((keyLayer ρ w _).smul_mem _ hsecond) hfirst

theorem extra_pos_key
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (hr : 0 < r) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    ρ.op (0 : Fin 28) r v ∈ keyLayer ρ w (keyShift r k) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hkey, rfl⟩ := hz
      rw [← hkey]
      exact extra_pos_word ρ w m h r hr l
  | zero => simp
  | add x y _ _ hx hy =>
      simpa using (keyLayer ρ w (keyShift r k)).add_mem hx hy
  | smul c x _ hx =>
      simpa using (keyLayer ρ w (keyShift r k)).smul_mem c hx

theorem extra_pos_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (hr : 0 < r) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    ρ.op (0 : Fin 28) r v ∈ higherOrbit ρ w m k := by
  apply keyOrbit_le_higher ρ w m k (keyShift r k)
    (keyLess_degree m k r hr)
  exact keyLayer_le_orbit ρ w (keyShift r k)
    (extra_pos_key ρ w m h r hr k hv)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.source_extra_pos
#print axioms VOA.DeligneAudit.D4Levi.extra_pos_word
#print axioms VOA.DeligneAudit.D4Levi.extra_pos_key
#print axioms VOA.DeligneAudit.D4Levi.extra_pos_higher
