import VOA.DeligneAudit.D4LeviKSDegreeShiftOrder
import VOA.DeligneAudit.D4LeviHigherPrefix

/-! Strict height is the part of the key prefix stable across degree shifts. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- Levi orbits whose height is strictly above that of the specified key. -/
def heightHigherOrbit (k : RadicalKey) : Submodule ℂ V :=
  ⨆ j : {j : RadicalKey // keyHeight m k < keyHeight m j},
    keyOrbit ρ w j.val

theorem xyzCountSpan_le_heightHigher (x y z : ℕ) (k : RadicalKey)
    (hh : keyHeight m k < 4 * (m : ℤ) + 2 * x - 2 * y - 4 * z) :
    xyzCountSpan ρ w x y z ≤ heightHigherOrbit ρ w m k := by
  rw [xyzCountSpan, Submodule.span_le]
  rintro v ⟨l, he, hx, hu, hup, hy, hz, rfl⟩
  have hheight : keyHeight m k < keyHeight m (wordKey l) := by
    simpa [keyHeight, wordKey, he, hx, hu, hup, hy, hz] using hh
  apply Submodule.mem_iSup_of_mem ⟨wordKey l, hheight⟩
  exact keyLayer_le_orbit ρ w (wordKey l) (radicalWord_mem_key ρ w l)

theorem heightHigherOrbit_le_higher_shift (k : RadicalKey) (r : ℕ) :
    heightHigherOrbit ρ w m k ≤
      higherOrbit ρ w m (keyShift r k) := by
  rw [heightHigherOrbit, iSup_le_iff]
  intro j
  apply keyOrbit_le_higher
  exact Or.inl (by simpa [keyHeight_shift] using j.property)

theorem heightHigherOrbit_full_levi_inv (k : RadicalKey)
    (a : Fin 28) (ha : IsLevi a) (r : ℕ) :
    heightHigherOrbit ρ w m k ≤
      (heightHigherOrbit ρ w m k).comap (ρ.op a r) := by
  intro v hv
  have hm : (heightHigherOrbit ρ w m k).map (ρ.op a r) ≤
      heightHigherOrbit ρ w m k := by
    rw [heightHigherOrbit, Submodule.map_iSup]
    apply iSup_le
    intro j
    apply Submodule.map_le_iff_le_comap.mpr
    intro x hx
    exact Submodule.mem_iSup_of_mem j
      (levi_op_orbit ρ w j.val a r ha hx)
  exact hm (Submodule.mem_map_of_mem hv)

theorem fOp_coeff_preserves_heightHigher (k : RadicalKey) (n s : ℕ)
    {v : V} (hv : v ∈ heightHigherOrbit ρ w m k) :
    PowerSeries.coeff s (fCurrent (fOp ρ) ^ n) v ∈
      heightHigherOrbit ρ w m k := by
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
      apply (heightHigherOrbit ρ w m k).sum_mem
      intro q hq
      have hf : fOp ρ q.2 v ∈ heightHigherOrbit ρ w m k :=
        heightHigherOrbit_full_levi_inv ρ w m k 18 ⟨10, rfl⟩ q.2 hv
      simpa [fCurrent, fOp, mul_smul] using ih q.1 hf

theorem fTop_coeff_preserves_heightHigher (k : RadicalKey) (n s : ℕ)
    {v : V} (hv : v ∈ heightHigherOrbit ρ w m k) :
    PowerSeries.coeff s (fCurrent (fTopOp ρ) ^ n) v ∈
      heightHigherOrbit ρ w m k := by
  induction n generalizing s v with
  | zero =>
      by_cases hs : s = 0
      · subst s
        simpa [fCurrent] using hv
      · simp [hs]
  | succ n ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      change (∑ q ∈ Finset.antidiagonal s,
        PowerSeries.coeff q.1 (fCurrent (fTopOp ρ) ^ n) *
          PowerSeries.coeff q.2 (fCurrent (fTopOp ρ))) • v ∈ _
      rw [Finset.sum_smul]
      apply (heightHigherOrbit ρ w m k).sum_mem
      intro q hq
      have hf : fTopOp ρ q.2 v ∈ heightHigherOrbit ρ w m k := by
        have hh := heightHigherOrbit_full_levi_inv ρ w m k 23
          ⟨9, rfl⟩ q.2 hv
        simpa [fTopOp] using (heightHigherOrbit ρ w m k).neg_mem hh
      simpa [fCurrent, fTopOp, mul_smul] using ih q.1 hf

theorem heightHigherOrbit_selectiveCartan_inv
    (k : RadicalKey) (q : Fin 3) (r : ℕ)
    {v : V} (hv : v ∈ heightHigherOrbit ρ w m k) :
    selectiveCartan ρ q r v ∈ heightHigherOrbit ρ w m k := by
  let N := heightHigherOrbit ρ w m k
  have h0 := heightHigherOrbit_full_levi_inv ρ w m k
    (leviColour (VOA.DeligneAudit.A3Sector.simpleH 0))
    (leviColour_isLevi _) r hv
  have h1 := heightHigherOrbit_full_levi_inv ρ w m k
    (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1))
    (leviColour_isLevi _) r hv
  have he := heightHigherOrbit_full_levi_inv ρ w m k 0 ⟨0, rfl⟩ r hv
  fin_cases q
  · change (1 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 0)) r v +
      (0 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r v +
      (-1 : ℂ) • ρ.op (0 : Fin 28) r v ∈ N
    exact N.add_mem (N.add_mem (N.smul_mem _ h0) (N.smul_mem _ h1))
      (N.smul_mem _ he)
  · change (-1 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 0)) r v +
      (0 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r v +
      (-1 : ℂ) • ρ.op (0 : Fin 28) r v ∈ N
    exact N.add_mem (N.add_mem (N.smul_mem _ h0) (N.smul_mem _ h1))
      (N.smul_mem _ he)
  · change (-1 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 0)) r v +
      (-1 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r v +
      (0 : ℂ) • ρ.op (0 : Fin 28) r v ∈ N
    exact N.add_mem (N.add_mem (N.smul_mem _ h0) (N.smul_mem _ h1))
      (N.smul_mem _ he)

theorem heightHigherOrbit_selectiveCartanWord_inv
    (k : RadicalKey) (ps : List (Fin 3 × ℕ))
    {v : V} (hv : v ∈ heightHigherOrbit ρ w m k) :
    selectiveCartanWord ρ ps v ∈ heightHigherOrbit ρ w m k := by
  induction ps with
  | nil => exact hv
  | cons p ps ih =>
      exact heightHigherOrbit_selectiveCartan_inv ρ w m k p.1 p.2 ih

/-- A strict-height relation survives every positive Cartan shift at the
    prefix indexed by the correspondingly shifted key. -/
theorem heightHigherOrbit_shifted_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (r i : ℕ)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = keyShift r k)
    (ps : List (Fin 3 × ℕ))
    {v : V} (hv : v ∈ heightHigherOrbit ρ w m k) :
    selectiveCartanWord ρ ps v ∈ keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  exact heightHigherOrbit_le_higher_shift ρ w m k r
    (heightHigherOrbit_selectiveCartanWord_inv ρ w m k ps hv)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.heightHigherOrbit_le_higher_shift
#print axioms VOA.DeligneAudit.D4Levi.xyzCountSpan_le_heightHigher
#print axioms VOA.DeligneAudit.D4Levi.heightHigherOrbit_full_levi_inv
#print axioms VOA.DeligneAudit.D4Levi.fOp_coeff_preserves_heightHigher
#print axioms VOA.DeligneAudit.D4Levi.fTop_coeff_preserves_heightHigher
#print axioms VOA.DeligneAudit.D4Levi.heightHigherOrbit_selectiveCartan_inv
#print axioms VOA.DeligneAudit.D4Levi.heightHigherOrbit_selectiveCartanWord_inv
#print axioms VOA.DeligneAudit.D4Levi.heightHigherOrbit_shifted_prefix
