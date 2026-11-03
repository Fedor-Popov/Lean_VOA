import VOA.DeligneAudit.D4LeviExtraCartan

/-! The extra Cartan zero mode has a fixed eigenvalue on each radical key. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem extra_comm (j : Fin 6) (r s : ℕ) (v : V) :
    ρ.op (0 : Fin 28) r (ρ.op (radicalColour j) s v) -
      ρ.op (radicalColour j) s (ρ.op (0 : Fin 28) r v) =
        (extraWeight j : ℂ) • ρ.op (radicalColour j) (r + s) v := by
  rw [ρ.comm]
  have hc : ∀ z : Fin 28,
      D4sector.f (0 : Fin 28) (radicalColour j) z =
        if z = radicalColour j then (extraWeight j : ℂ) else 0 :=
    extra_coefficient j
  simp_rw [hc]
  simp only [ite_smul, zero_smul]
  change (Finset.univ : Finset (Fin 28)).sum
    (fun z => if z = radicalColour j then
      (extraWeight j : ℂ) • ρ.op z (r + s) v else 0) = _
  rw [Finset.sum_ite_eq']
  simp

theorem source_extra_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    ρ.op (0 : Fin 28) 0 w = 0 := by
  have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
    simpa [ravFam] using h
  have hh := rs_cartan_zero hs
    (by change (0 : Fin 28).val < 4; decide : D4sector.cartan (0 : Fin 28))
  simpa [D4sector, thetaD4] using hh

theorem extra_weight_word
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (l : List (Fin 6 × ℕ)) :
    ρ.op (0 : Fin 28) 0 (radicalWord ρ w l) =
      (extraLabel (wordKey l) : ℂ) • radicalWord ρ w l := by
  induction l with
  | nil =>
      simpa [radicalWord, wordKey, extraLabel] using source_extra_zero ρ w m h
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      have hc := extra_comm ρ j 0 s (radicalWord ρ w l)
      have heq : radicalWord ρ w ((j, s) :: l) =
          ρ.op (radicalColour j) s (radicalWord ρ w l) := rfl
      rw [heq, sub_eq_iff_eq_add.mp hc, ih, extraLabel_cons]
      simp only [Int.cast_add, add_smul, map_smul, zero_add]
      abel

theorem extra_weight_key
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) {v : V} (hv : v ∈ keyLayer ρ w k) :
    ρ.op (0 : Fin 28) 0 v = (extraLabel k : ℂ) • v := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hkey, rfl⟩ := hz
      simpa [← hkey] using extra_weight_word ρ w m h l
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy, smul_add]
  | smul c x _ hx =>
      rw [map_smul, hx]
      exact smul_comm c (extraLabel k : ℂ) x

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.extra_comm
#print axioms VOA.DeligneAudit.D4Levi.source_extra_zero
#print axioms VOA.DeligneAudit.D4Levi.extra_weight_word
#print axioms VOA.DeligneAudit.D4Levi.extra_weight_key
