import VOA.DeligneAudit.SL4TRadicalMultiplicityAction

/-!
Garland coefficients and adjacent-letter conversion in the quotient by earlier radical counts.
All mode degrees are retained. Lower contractions have strictly greater Levi height at the
same radical depth, so their absorption does not use a mode-degree quotient.
-/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviConversion

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- A strictly higher count layer at the same depth lies in the merged relations. -/
theorem radicalCountSpan_le_higher (d : Fin 3 → ℕ) (u v z : ℕ)
    (hdepth : u + v + z = d 0 + d 1 + d 2)
    (hheight : (d 0 : ℤ) - d 2 < (u : ℤ) - z) :
    a3CountSpan ρ w u v z ≤ higherRadicalCountClosure ρ w d := by
  apply iSup_le
  intro degree
  apply (a3LeviClosure_contains ρ _).trans'
  exact le_iSup_of_le ⟨u, v, z, degree⟩
    (le_iSup_of_le ⟨hdepth, Or.inl hheight⟩ le_rfl)

/-- The count triple of an adjacent-letter conversion, independent of mode degree. -/
def radicalConversionCounts (j : Fin 2) (k : ℕ) (xs ys zs : List ℕ) : Fin 3 → ℕ :=
  if j = 0 then ![xs.length, ys.length + k, zs.length]
  else ![zs.length, xs.length, ys.length + k]

/-- Every lower contraction is absorbed by earlier counts at the same depth. -/
theorem radicalConversion_lower_summand (k : ℕ)
    (j : Fin 2) (xs ys zs : List ℕ)
    (p : List ℕ × List ℕ)
    (hp : p ∈ choices (xs ++ List.replicate k 0))
    (hshort : p.2.length < k) (z : ℕ × ℕ) :
    let f : ℕ → Module.End ℂ V := fun i => ρ.op (leviF j) i
    let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
    let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
    let R : Module.End ℂ V :=
      (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
    ((PowerSeries.coeff z.1 (fCurrent f ^ (k - p.2.length)) *
        aWord A p.1) * PowerSeries.coeff z.2 (bWord B p.2)) •
      (((ys.map B).prod * R) • w) ∈
        higherRadicalCountClosure ρ w (radicalConversionCounts j k xs ys zs) := by
  have hlen := choices_length (xs ++ List.replicate k 0) p hp
  simp only [List.length_append, List.length_replicate] at hlen
  fin_cases j
  · let D : Fin 3 → ℕ := ![xs.length, ys.length + k, zs.length]
    let N := higherRadicalCountClosure ρ w D
    have hspec : (zs.map fun i => ρ.op (F 2) i).prod w ∈
        a3CountSpan ρ w 0 0 zs.length := by
      simpa using a3CountSpan_word ρ w 2 zs 0 0 0
        (a3CountSpan_zero ρ w)
    have hys : (ys.map fun i => ρ.op (F 1) i).prod
        ((zs.map fun i => ρ.op (F 2) i).prod w) ∈
        a3CountSpan ρ w 0 ys.length zs.length := by
      simpa using a3CountSpan_word ρ w 1 ys 0 0 zs.length hspec
    have hb := a3_bWord_coeff_count ρ w 1 p.2 z.2 0 ys.length
      zs.length hys
    have ha := a3CountSpan_word ρ w 0 p.1 0
      (ys.length + p.2.length) zs.length hb
    have hheight : (D 0 : ℤ) - D 2 <
        (p.1.length : ℤ) - zs.length := by
      dsimp [D]
      omega
    have hbase : (aWord (fun i => ρ.op (F (a3ConvA 0)) i) p.1 *
        PowerSeries.coeff z.2
          (bWord (fun i => ρ.op (F (a3ConvB 0)) i) p.2)) •
        (((ys.map fun i => ρ.op (F (a3ConvB 0)) i).prod *
          (zs.map fun i => ρ.op (F (a3ConvSpectator 0)) i).prod) • w) ∈ N := by
      apply radicalCountSpan_le_higher ρ w D p.1.length
        (ys.length + p.2.length) zs.length (by dsimp [D]; omega) hheight
      simpa [aWord, a3ConvA, a3ConvB, a3ConvSpectator,
        mul_smul] using ha
    have hf := a3_fCurrent_pow_preserves ρ 0
      (⨆ t, ⨆ (_ : higherRadicalCounts D t), a3KeyLayer ρ w t) (k - p.2.length) z.1 hbase
    simpa [N, D, radicalConversionCounts, a3ConvA, a3ConvB,
      a3ConvSpectator, mul_assoc, mul_smul] using hf
  · let D : Fin 3 → ℕ := ![zs.length, xs.length, ys.length + k]
    let N := higherRadicalCountClosure ρ w D
    have hspec : (zs.map fun i => ρ.op (F 0) i).prod w ∈
        a3CountSpan ρ w zs.length 0 0 := by
      simpa using a3CountSpan_word ρ w 0 zs 0 0 0
        (a3CountSpan_zero ρ w)
    have hys : (ys.map fun i => ρ.op (F 2) i).prod
        ((zs.map fun i => ρ.op (F 0) i).prod w) ∈
        a3CountSpan ρ w zs.length 0 ys.length := by
      simpa using a3CountSpan_word ρ w 2 ys zs.length 0 0 hspec
    have hb := a3_bWord_coeff_count ρ w 2 p.2 z.2 zs.length 0
      ys.length hys
    have ha := a3CountSpan_word ρ w 1 p.1 zs.length 0
      (ys.length + p.2.length) hb
    have hheight : (D 0 : ℤ) - D 2 <
        (zs.length : ℤ) - (ys.length + p.2.length : ℕ) := by
      dsimp [D]
      omega
    have hbase : (aWord (fun i => ρ.op (F (a3ConvA 1)) i) p.1 *
        PowerSeries.coeff z.2
          (bWord (fun i => ρ.op (F (a3ConvB 1)) i) p.2)) •
        (((ys.map fun i => ρ.op (F (a3ConvB 1)) i).prod *
          (zs.map fun i => ρ.op (F (a3ConvSpectator 1)) i).prod) • w) ∈ N := by
      apply radicalCountSpan_le_higher ρ w D zs.length
        p.1.length (ys.length + p.2.length) (by dsimp [D]; omega) hheight
      simpa [aWord, a3ConvA, a3ConvB, a3ConvSpectator,
        mul_smul] using ha
    have hf := a3_fCurrent_pow_preserves ρ 1
      (⨆ t, ⨆ (_ : higherRadicalCounts D t), a3KeyLayer ρ w t) (k - p.2.length) z.1 hbase
    simpa [N, D, radicalConversionCounts, a3ConvA, a3ConvB,
      a3ConvSpectator, mul_assoc, mul_smul] using hf
/-- The full lower Wick term is absorbed in the merged quotient. -/
theorem radicalConversion_lower_term (k s : ℕ)
    (j : Fin 2) (xs ys zs : List ℕ)
    (p : List ℕ × List ℕ)
    (hp : p ∈ choices (xs ++ List.replicate k 0))
    (hshort : p.2.length < k) :
    let f : ℕ → Module.End ℂ V := fun i => ρ.op (leviF j) i
    let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
    let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
    let R : Module.End ℂ V :=
      (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
    conversionTerm f A B k s p • (((ys.map B).prod * R) • w) ∈
      higherRadicalCountClosure ρ w (radicalConversionCounts j k xs ys zs) := by
  let N := higherRadicalCountClosure ρ w (radicalConversionCounts j k xs ys zs)
  let f : ℕ → Module.End ℂ V := fun i => ρ.op (leviF j) i
  let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
  let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
  let R : Module.End ℂ V :=
    (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
  have hsum :
      (∑ z ∈ Finset.antidiagonal s,
        (PowerSeries.coeff z.1 (fCurrent f ^ (k - p.2.length)) *
          aWord A p.1) * PowerSeries.coeff z.2 (bWord B p.2)) •
        (((ys.map B).prod * R) • w) ∈ N := by
    rw [Finset.sum_smul]
    apply N.sum_mem
    intro z hz
    exact radicalConversion_lower_summand ρ w k j xs ys zs p hp hshort z
  have hscalar (z : ℂ) :
      (algebraMap ℂ (Module.End ℂ V) z) •
        ((∑ x ∈ Finset.antidiagonal s,
          (PowerSeries.coeff x.1 (fCurrent f ^ (k - p.2.length)) *
            aWord A p.1) * PowerSeries.coeff x.2 (bWord B p.2)) •
          (((ys.map B).prod * R) • w)) ∈ N := by
    simpa using N.smul_mem z hsum
  have hcast : ((-1 : Module.End ℂ V) ^ p.2.length *
      (k.descFactorial p.2.length : Module.End ℂ V)) =
      algebraMap ℂ (Module.End ℂ V)
        ((-1 : ℂ) ^ p.2.length * (k.descFactorial p.2.length : ℂ)) := by
    simp
  unfold conversionTerm
  rw [hcast]
  simpa only [mul_smul] using
    hscalar ((-1 : ℂ) ^ p.2.length * (k.descFactorial p.2.length : ℂ))

/-- The converted complete-function relation with zero preceding-letter modes. -/
theorem radicalConversion_zero_modes (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (j : Fin 2) (n k s : ℕ) (hk : 1 ≤ k)
    (hks : (weightABC a b c) (Fin.succ j) + 1 ≤ k + s)
    (ys zs : List ℕ) :
    boxTarget (fun i => ρ.op (F (a3ConvA j)) i)
      (fun i => ρ.op (F (a3ConvB j)) i) k s (List.replicate n 0) ys
      (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod w ∈
        higherRadicalCountClosure ρ w
          (radicalConversionCounts j k (List.replicate n 0) ys zs) := by
  have ht := a3_box_conversion_graded_of_higher ρ w a b c h j k s hk hks
    (List.replicate n 0) ys zs
    (higherRadicalCountClosure ρ w
      (radicalConversionCounts j k (List.replicate n 0) ys zs))
    (fun p hp hs => radicalConversion_lower_term ρ w k s j _ ys zs p hp hs)
  have hz : gradedLowerModeSpan
      (fun i => ρ.op (F (a3ConvA j)) i)
      (fun i => ρ.op (F (a3ConvB j)) i) (List.replicate n 0) ys k
      ((List.replicate n 0).sum + ys.sum + s)
      (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod w = ⊥ := by
    apply le_antisymm _ bot_le
    rw [gradedLowerModeSpan, Submodule.span_le]
    rintro v ⟨us, vs, hu, hv, hd, hs, rfl⟩
    simp at hs
  simpa only [hz, bot_sup_eq] using ht

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.radicalCountSpan_le_higher
#print axioms VOA.DeligneAudit.SL4T.radicalConversion_lower_summand
#print axioms VOA.DeligneAudit.SL4T.radicalConversion_lower_term
#print axioms VOA.DeligneAudit.SL4T.radicalConversion_zero_modes
