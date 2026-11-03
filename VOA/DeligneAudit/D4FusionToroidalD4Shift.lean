import VOA.DeligneAudit.D4FusionToroidalGr
import VOA.DeligneAudit.D4FusionToroidalD4Pairs
import VOA.DeligneAudit.DeligneSectorD4
import VOA.DeligneAudit.D4FusionKernelGeneric

/-! Perfectness of the D4 bracket upgrades high-letter count to mode-block degree. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl

noncomputable section

private theorem highModeShift_of_pairs {n : ℕ}
    (f : Fin n → Fin n → Fin n → ℂ) (R : RelSpec n) (m : ℕ)
    (pair : Fin n → Fin n × Fin n)
    (hnz : ∀ c, f (pair c).1 (pair c).2 c ≠ 0)
    (hoff : ∀ c e, e ≠ c → f (pair c).1 (pair c).2 e = 0) :
    HighModeShift f R m := by
  intro c i s j hs x hx
  induction i using Nat.strong_induction_on generalizing c j x with
  | h i ih =>
    cases i with
    | zero => exact shift_zero f R m c s j hs hx
    | succ k =>
      cases k with
      | zero => simpa using shift_one f R m c s j hx
      | succ k =>
        let a := (pair c).1
        let b := (pair c).2
        have hprev (d : Fin n) (q : ℕ) (v : UModG f R)
            (hv : v ∈ TU f R m q) :
            (univRepG f R).op d ((k + 1) * m + s) v ∈
              TU f R m (q + (k + 1)) := by
          exact ih (k + 1) (by omega) d q hv
        have hb := hprev b j x hx
        have ha : (univRepG f R).op a m
            ((univRepG f R).op b ((k + 1) * m + s) x) ∈
            TU f R m (j + (k + 2)) := by
          have h := shift_one f R m a 0 (j + (k + 1)) hb
          simpa only [one_mul, add_zero, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using h
        have hax : (univRepG f R).op a m x ∈ TU f R m (j + 1) := by
          simpa only [one_mul, add_zero] using shift_one f R m a 0 j hx
        have hab : (univRepG f R).op b ((k + 1) * m + s)
            ((univRepG f R).op a m x) ∈ TU f R m (j + (k + 2)) := by
          have h := hprev b (j + 1) _ hax
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
        have hsum (r : ℕ) (v : UModG f R) :
            (∑ e, f a b e • (univRepG f R).op e r v) =
              f a b c • (univRepG f R).op c r v := by
          classical
          apply Finset.sum_eq_single c
          · intro e _ he
            rw [hoff c e he, zero_smul]
          · simp
        have hcomm := (univRepG f R).comm a b m ((k + 1) * m + s) x
        rw [hsum] at hcomm
        have hmode : m + ((k + 1) * m + s) = (k + 2) * m + s := by ring
        rw [hmode] at hcomm
        have hscaled : f a b c • (univRepG f R).op c ((k + 2) * m + s) x ∈
            TU f R m (j + (k + 2)) := by
          rw [← hcomm]
          exact Submodule.sub_mem _ ha hab
        have h := Submodule.smul_mem (TU f R m (j + (k + 2)))
          (f a b c)⁻¹ hscaled
        have hnon : f a b c ≠ 0 := hnz c
        rw [smul_smul, inv_mul_cancel₀ hnon, one_smul] at h
        change (univRepG f R).op c ((k + 2) * m + s) x ∈
          TU f R m (j + (k + 2))
        exact h

/-- Every D4 current mode shifts by its number of complete mode blocks. -/
theorem highModeShift_D4 (R : RelSpec 28) (m : ℕ) (_hm : 1 ≤ m) :
    HighModeShift VOA.DeligneAudit.DeligneSector.D4.D4sector.f R m := by
  let pair := D4.bracketPair
  have hnz : ∀ c, VOA.DeligneAudit.DeligneSector.D4.D4sector.f
      (pair c).1 (pair c).2 c ≠ 0 := by
    intro c
    change ((VOA.DeligneAudit.DeligneSector.Sparse.fZ
      VOA.DeligneAudit.DeligneSector.D4.br (pair c).1 (pair c).2 c : ℤ) : ℂ) ≠ 0
    exact_mod_cast D4.bracketPair_nonzero c
  have hoff : ∀ c e, e ≠ c → VOA.DeligneAudit.DeligneSector.D4.D4sector.f
      (pair c).1 (pair c).2 e = 0 := by
    intro c e he
    change ((VOA.DeligneAudit.DeligneSector.Sparse.fZ
      VOA.DeligneAudit.DeligneSector.D4.br (pair c).1 (pair c).2 e : ℤ) : ℂ) = 0
    exact_mod_cast D4.bracketPair_off c e he
  exact highModeShift_of_pairs _ R m pair hnz hoff

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.highModeShift_D4
