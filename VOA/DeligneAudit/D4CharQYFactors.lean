import VOA.DeligneAudit.D4CharQXB

/-! Local factors for identity Y, with integer gaps and a final zero appended. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- An integer gap, before the naturalization in `gtGap`. -/
def gtGapInt {N : ℕ} (lam : Fin N → ℤ) (i : Fin N) : ℤ :=
  Fin.snoc (α := fun _ => ℤ) lam 0 i.castSucc - Fin.snoc (α := fun _ => ℤ) lam 0 i.succ

/-- The subset indicator with a final absent position. -/
def gtPadBits {N : ℕ} (S : Finset (Fin N)) : Fin (N + 1) → Bool :=
  Fin.snoc (pieriIndicator S) false

def gtEnterFactor (q : R) (d : ℤ) (s t : Bool) : R :=
  if !s && t then 1 - q ^ d.toNat else 1

def gtExitFactor (q : R) (d : ℤ) (s t : Bool) : R :=
  if s && !t then 1 - q ^ d.toNat else 1

/-- The local cancellation underlying Y, with no omitted zero or negative gaps. -/
theorem gtY_local (q : R) (h : PochhammerUnits q) (d : ℤ) (s t : Bool) :
    gtEnterFactor q d s t * gtInvPoch q h d =
      gtExitFactor q (d + pieriBit s - pieriBit t) s t *
        gtInvPoch q h (d + pieriBit s - pieriBit t) := by
  cases s <;> cases t <;> simp [gtEnterFactor, gtExitFactor, pieriBit]
  · exact (gtInvPoch_lower q h d).symm
  · exact (gtInvPoch_raise q h d).symm

theorem gtGapInt_nonneg {N : ℕ} (lam : Fin N → ℤ) (hlam : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (i : Fin N) : 0 ≤ gtGapInt lam i := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ N =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [gtGapInt] using hpos (Fin.last N)
      · have hj := hlam (show j.castSucc ≤ j.succ by
          change j.val ≤ j.val + 1
          omega)
        simpa [gtGapInt, ← Fin.castSucc_succ] using sub_nonneg.mpr hj

theorem gtPad_pieriWeight {N : ℕ} (lam : Fin N → ℤ) (S : Finset (Fin N))
    (i : Fin (N + 1)) :
    Fin.snoc (α := fun _ => ℤ) (pieriWeight lam S) 0 i =
      Fin.snoc (α := fun _ => ℤ) lam 0 i + pieriBit (gtPadBits S i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [gtPadBits, pieriBit]
  · simp [gtPadBits, pieriWeight, pieriBit, pieriIndicator]

theorem gtGapInt_pieriWeight {N : ℕ} (lam : Fin N → ℤ) (S : Finset (Fin N))
    (i : Fin N) :
    gtGapInt (pieriWeight lam S) i = gtGapInt lam i +
      pieriBit (gtPadBits S i.castSucc) - pieriBit (gtPadBits S i.succ) := by
  simp only [gtGapInt, gtPad_pieriWeight]
  ring

/-- Normalization as an integer reciprocal product, for a nonnegative partition. -/
theorem gtNormUnit_product (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin N → ℤ) (hlam : Antitone lam) (hpos : ∀ i, 0 ≤ lam i) :
    (gtNormUnit q h lam : R) = ∏ i, gtInvPoch q h (gtGapInt lam i) := by
  rw [gtNormUnit, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [gtInvPoch, if_pos (gtGapInt_nonneg lam hlam hpos i)]
  rfl

/-- e-Pieri written as the product of entering-edge factors, with the final zero edge. -/
theorem pieriCoeff_enter_product (q : R) {N : ℕ}
    (lam : Fin N → ℤ) (S : Finset (Fin N)) :
    pieriCoeff q lam S = ∏ i : Fin N,
      gtEnterFactor q (gtGapInt lam i) (gtPadBits S i.castSucc) (gtPadBits S i.succ) := by
  classical
  unfold pieriCoeff
  rw [← Fintype.prod_extend_by_one S]
  cases N with
  | zero => simp
  | succ N =>
      rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
      simp only [Fin.val_zero, true_or, if_true, ite_self, one_mul]
      have ht : gtEnterFactor q (gtGapInt lam (Fin.last N))
          (gtPadBits S (Fin.last N).castSucc) (gtPadBits S (Fin.last N).succ) = 1 := by
        simp [gtPadBits, gtEnterFactor]
      rw [ht, mul_one]
      apply Finset.prod_congr rfl
      intro i _
      have hp : pieriPrevious i.succ = i.castSucc := by
        ext
        simp [pieriPrevious]
      by_cases hs : i.castSucc ∈ S <;> by_cases ht : i.succ ∈ S <;>
        simp [hp, hs, ht, gtPadBits, gtGapInt, gtEnterFactor, pieriIndicator,
          ← Fin.castSucc_succ]

/-- The product over exiting edges on the left side of identity Y. -/
def gtExitCoeff (q : R) {N : ℕ} (lam : Fin N → ℤ) (S : Finset (Fin N)) : R :=
  ∏ i : Fin N, gtExitFactor q (gtGapInt lam i)
    (gtPadBits S i.castSucc) (gtPadBits S i.succ)

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtY_local
#print axioms VOA.DeligneAudit.D4Char.gtGapInt_nonneg
#print axioms VOA.DeligneAudit.D4Char.gtPad_pieriWeight
#print axioms VOA.DeligneAudit.D4Char.gtGapInt_pieriWeight
#print axioms VOA.DeligneAudit.D4Char.gtNormUnit_product
#print axioms VOA.DeligneAudit.D4Char.pieriCoeff_enter_product
