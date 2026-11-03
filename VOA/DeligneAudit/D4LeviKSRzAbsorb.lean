import VOA.DeligneAudit.D4LeviKSRzCount

/-! Lower Wick contractions for f₂ are absorbed by the higher D4 key orbit. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

noncomputable def xOp (r : ℕ) : Module.End ℂ V := ρ.op (22 : Fin 28) r
noncomputable def yOp (r : ℕ) : Module.End ℂ V := ρ.op (26 : Fin 28) r
noncomputable def zOp (r : ℕ) : Module.End ℂ V := ρ.op (27 : Fin 28) r
noncomputable def fOp (r : ℕ) : Module.End ℂ V := ρ.op (18 : Fin 28) r

theorem xyzCountSpan_x_word (ls : List ℕ) (x y z : ℕ)
    {v : V} (hv : v ∈ xyzCountSpan ρ w x y z) :
    (ls.map (xOp ρ)).prod v ∈ xyzCountSpan ρ w (x + ls.length) y z := by
  induction ls generalizing x y z v with
  | nil => simpa using hv
  | cons r ls ih =>
      have hh := xyzCountSpan_op ρ w 1 r (x + ls.length) y z
        (Or.inl rfl) (ih x y z hv)
      simpa [xOp, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem xyzCountSpan_y_word (ls : List ℕ) (x y z : ℕ)
    {v : V} (hv : v ∈ xyzCountSpan ρ w x y z) :
    (ls.map (yOp ρ)).prod v ∈ xyzCountSpan ρ w x (y + ls.length) z := by
  induction ls generalizing x y z v with
  | nil => simpa using hv
  | cons r ls ih =>
      have hh := xyzCountSpan_op ρ w 4 r x (y + ls.length) z
        (Or.inr (Or.inl rfl)) (ih x y z hv)
      simpa [yOp, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem xyzCountSpan_z_word (ls : List ℕ) (x y z : ℕ)
    {v : V} (hv : v ∈ xyzCountSpan ρ w x y z) :
    (ls.map (zOp ρ)).prod v ∈ xyzCountSpan ρ w x y (z + ls.length) := by
  induction ls generalizing x y z v with
  | nil => simpa using hv
  | cons r ls ih =>
      have hh := xyzCountSpan_op ρ w 5 r x y (z + ls.length)
        (Or.inr (Or.inr rfl)) (ih x y z hv)
      simpa [zOp, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem xyzCountSpan_z_coeff (ls : List ℕ) (s x y z : ℕ)
    {v : V} (hv : v ∈ xyzCountSpan ρ w x y z) :
    PowerSeries.coeff s (bWord (zOp ρ) ls) v ∈
      xyzCountSpan ρ w x y (z + ls.length) := by
  induction ls generalizing s x y z v with
  | nil =>
      by_cases hs : s = 0
      · subst s
        simpa [bWord] using hv
      · simp [bWord, hs]
  | cons r ls ih =>
      change PowerSeries.coeff s
        (bTail (zOp ρ) r * bWord (zOp ρ) ls) v ∈ _
      rw [PowerSeries.coeff_mul]
      change (∑ q ∈ Finset.antidiagonal s,
        PowerSeries.coeff q.1 (bTail (zOp ρ) r) *
          PowerSeries.coeff q.2 (bWord (zOp ρ) ls)) • v ∈ _
      rw [Finset.sum_smul]
      apply (xyzCountSpan ρ w x y (z + (r :: ls).length)).sum_mem
      intro q hq
      have ht := ih q.2 x y z hv
      have hz := xyzCountSpan_op ρ w 5 (r + q.1) x y
        (z + ls.length) (Or.inr (Or.inr rfl)) ht
      simpa [bTail, mul_smul, zOp, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hz

theorem fOp_coeff_preserves_higher (k : RadicalKey) (n s : ℕ)
    {v : V} (hv : v ∈ higherOrbit ρ w m k) :
    PowerSeries.coeff s (fCurrent (fOp ρ) ^ n) v ∈
      higherOrbit ρ w m k := by
  induction n generalizing s v with
  | zero =>
      by_cases hs : s = 0
      · subst s
        simpa [fCurrent] using hv
      · simp [hs]
  | succ n ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      change (∑ q ∈ Finset.antidiagonal s,
        PowerSeries.coeff q.1 (fCurrent (fOp ρ) ^ n) *
          PowerSeries.coeff q.2 (fCurrent (fOp ρ))) • v ∈ _
      rw [Finset.sum_smul]
      apply (higherOrbit ρ w m k).sum_mem
      intro q hq
      have hf : fOp ρ q.2 v ∈ higherOrbit ρ w m k := by
        exact higherOrbit_full_levi_inv ρ w m k (18 : Fin 28)
          ⟨10, rfl⟩ q.2 hv
      simpa [fCurrent, fOp, mul_smul] using ih q.1 hf

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyzCountSpan_x_word
#print axioms VOA.DeligneAudit.D4Levi.xyzCountSpan_y_word
#print axioms VOA.DeligneAudit.D4Levi.xyzCountSpan_z_word
#print axioms VOA.DeligneAudit.D4Levi.xyzCountSpan_z_coeff
#print axioms VOA.DeligneAudit.D4Levi.fOp_coeff_preserves_higher
