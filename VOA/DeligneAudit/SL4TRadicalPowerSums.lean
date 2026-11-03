import VOA.DeligneAudit.SL4TRadicalCountLayers

/-!
The three radical alphabets are separated by linear combinations of Cartan currents.
Their positive modes act by power-sum shifts on radical words, before and after merging degrees.
-/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviTypeA

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- A positive mode selects shifts in exactly one of the three radical alphabets. -/
def radicalAlphabetCurrent (j : Fin 3) (s : ℕ) : Module.End ℂ V :=
  (1 / 4 : ℂ) • (-ρ.op 12 s +
    (if j = 0 then (2 : ℂ) else -2) • ρ.op 13 s +
      (if j = 2 then (-3 : ℂ) else 1) • ρ.op 14 s)

/-- The inverse Cartan matrix separates the three commuting radical letters. -/
theorem radicalAlphabetCurrent_comm (i j : Fin 3) (r s : ℕ) (v : V) :
    radicalAlphabetCurrent ρ i r (radicalOp ρ j s v) -
      radicalOp ρ j s (radicalAlphabetCurrent ρ i r v) =
        (if i = j then (1 : ℂ) else 0) • radicalOp ρ j (r + s) v := by
  have h₀ := sub_eq_iff_eq_add.mp (a3_extra_cartan_comm ρ j r s v)
  have h₁ := sub_eq_iff_eq_add.mp (levi_cartan_comm ρ 0 j r s v)
  have h₂ := sub_eq_iff_eq_add.mp (levi_cartan_comm ρ 1 j r s v)
  change ρ.op 13 r (radicalOp ρ j s v) = _ at h₁
  change ρ.op 14 r (radicalOp ρ j s v) = _ at h₂
  simp only [radicalAlphabetCurrent, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.neg_apply, map_smul, map_add, map_neg]
  rw [h₀, h₁, h₂]
  fin_cases i <;> fin_cases j <;> simp [a3ExtraWeight, leviWeight, leviH,
    radicalOp, Fin.reduceEq] <;> module

/-- All positive alphabet currents kill the local Weyl generator. -/
theorem radicalAlphabetCurrent_source_zero (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (j : Fin 3) (s : ℕ) (hs : 0 < s) : radicalAlphabetCurrent ρ j s w = 0 := by
  have h₀ := h.cartan_pos 0 s hs
  have h₁ := h.cartan_pos 1 s hs
  have h₂ := h.cartan_pos 2 s hs
  simp only [simpleH] at h₀ h₁ h₂
  fin_cases j <;> simp [radicalAlphabetCurrent, h₀, h₁, h₂]

/-- Multiplication by a power sum shifts one matching letter at a time. -/
def radicalPowerSumWord (j : Fin 3) (r : ℕ) : List (Fin 3 × ℕ) → V
  | [] => 0
  | (i, s) :: l =>
      (if j = i then (1 : ℂ) else 0) •
        (radicalWord (radicalOp ρ) ((i, r + s) :: l) • w) +
          radicalOp ρ i s (radicalPowerSumWord j r l)

/-- The Cartan realization of every positive power-sum shift, for arbitrary mode words. -/
theorem radicalAlphabetCurrent_word (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (j : Fin 3) (r : ℕ) (hr : 0 < r) (l : List (Fin 3 × ℕ)) :
    radicalAlphabetCurrent ρ j r (radicalWord (radicalOp ρ) l • w) =
      radicalPowerSumWord ρ w j r l := by
  induction l with
  | nil => exact radicalAlphabetCurrent_source_zero ρ w a b c h j r hr
  | cons x l ih =>
    rcases x with ⟨i, s⟩
    change radicalAlphabetCurrent ρ j r
      (radicalOp ρ i s (radicalWord (radicalOp ρ) l • w)) = _
    rw [sub_eq_iff_eq_add.mp (radicalAlphabetCurrent_comm ρ j i r s _), ih]
    rfl

/-- The two Levi Cartan currents are the differences of adjacent alphabet power sums. -/
theorem leviCartan_eq_alphabet_difference (s : ℕ) :
    ρ.op 13 s = radicalAlphabetCurrent ρ 0 s - radicalAlphabetCurrent ρ 1 s ∧
      ρ.op 14 s = radicalAlphabetCurrent ρ 1 s - radicalAlphabetCurrent ρ 2 s := by
  constructor <;> ext v <;> simp [radicalAlphabetCurrent] <;> module

/-- Positive Levi Cartan currents act by the two differences of power-sum shifts. -/
theorem leviCartan_word_powerSum (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (r : ℕ) (hr : 0 < r) (l : List (Fin 3 × ℕ)) :
    ρ.op 13 r (radicalWord (radicalOp ρ) l • w) =
      radicalPowerSumWord ρ w 0 r l - radicalPowerSumWord ρ w 1 r l ∧
    ρ.op 14 r (radicalWord (radicalOp ρ) l • w) =
      radicalPowerSumWord ρ w 1 r l - radicalPowerSumWord ρ w 2 r l := by
  obtain ⟨h₁, h₂⟩ := leviCartan_eq_alphabet_difference ρ r
  constructor
  · rw [h₁, LinearMap.sub_apply, radicalAlphabetCurrent_word ρ w a b c h 0 r hr,
      radicalAlphabetCurrent_word ρ w a b c h 1 r hr]
  · rw [h₂, LinearMap.sub_apply, radicalAlphabetCurrent_word ρ w a b c h 1 r hr,
      radicalAlphabetCurrent_word ρ w a b c h 2 r hr]

/-- The node-one Cartan also preserves each merged radical count layer. -/
theorem radicalCountLayer_extra_cartan_positive (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (s : ℕ) (hs : 0 < s) :
    radicalCountLayer ρ w d ≤ (radicalCountLayer ρ w d).comap (ρ.op 12 s) := by
  apply iSup_le
  intro degree v hv
  change ρ.op 12 s v ∈ radicalCountLayer ρ w d
  have hm := a3_extra_cartan_pos_maps_key ρ w a b c h s hs
    ⟨d 0, d 1, d 2, degree⟩ hv
  exact (le_iSup (fun t => a3KeyLayer ρ w ⟨d 0, d 1, d 2, t⟩) (degree + s)) hm

/-- Each individual alphabet power-sum current acts within a merged radical count layer. -/
theorem radicalCountLayer_alphabet_current (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (j : Fin 3) (s : ℕ) (hs : 0 < s) :
    radicalCountLayer ρ w d ≤
      (radicalCountLayer ρ w d).comap (radicalAlphabetCurrent ρ j s) := by
  intro v hv
  let P := radicalCountLayer ρ w d
  have h₀ := radicalCountLayer_extra_cartan_positive ρ w a b c h d s hs hv
  have h₁ := radicalCountLayer_cartan_positive ρ w a b c h d 0 s hs hv
  have h₂ := radicalCountLayer_cartan_positive ρ w a b c h d 1 s hs hv
  exact P.smul_mem _ (P.add_mem (P.add_mem (P.neg_mem h₀) (P.smul_mem _ h₁))
    (P.smul_mem _ h₂))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetCurrent_comm
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetCurrent_source_zero
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetCurrent_word
#print axioms VOA.DeligneAudit.SL4T.leviCartan_eq_alphabet_difference
#print axioms VOA.DeligneAudit.SL4T.leviCartan_word_powerSum
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_extra_cartan_positive
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_alphabet_current
