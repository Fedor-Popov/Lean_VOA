import VOA.DeligneAudit.LeviTypeA3ConvCoeff

/-! Lower Wick summands are absorbed by strictly higher radical keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

def a3ConvKey (j : Fin 2) (k d : ℕ)
    (xs ys zs : List ℕ) : A3RadicalKey :=
  if j = 0 then ⟨xs.length, ys.length + k, zs.length, d⟩
  else ⟨zs.length, xs.length, ys.length + k, d⟩

theorem a3_lower_wick_summand (b c k d : ℕ)
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
        a3HigherLeviClosure ρ w b c (a3ConvKey j k d xs ys zs) := by
  have hlen := choices_length (xs ++ List.replicate k 0) p hp
  simp only [List.length_append, List.length_replicate] at hlen
  fin_cases j
  · let K : A3RadicalKey := ⟨xs.length, ys.length + k, zs.length, d⟩
    let N := a3HigherLeviClosure ρ w b c K
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
    have hheight : a3KeyHeight b c K <
        (b : ℤ) + c + p.1.length - zs.length := by
      dsimp [a3KeyHeight, K]
      omega
    have hbase : (aWord (fun i => ρ.op (F (a3ConvA 0)) i) p.1 *
        PowerSeries.coeff z.2
          (bWord (fun i => ρ.op (F (a3ConvB 0)) i) p.2)) •
        (((ys.map fun i => ρ.op (F (a3ConvB 0)) i).prod *
          (zs.map fun i => ρ.op (F (a3ConvSpectator 0)) i).prod) • w) ∈ N := by
      apply a3CountSpan_le_higher ρ w b c K p.1.length
        (ys.length + p.2.length) zs.length hheight
      simpa [aWord, a3ConvA, a3ConvB, a3ConvSpectator,
        mul_smul] using ha
    have hf := a3_fCurrent_pow_preserves ρ 0
      (a3HigherKeySpan ρ w b c K) (k - p.2.length) z.1 hbase
    simpa [N, K, a3ConvKey, a3ConvA, a3ConvB,
      a3ConvSpectator, mul_assoc, mul_smul] using hf
  · let K : A3RadicalKey := ⟨zs.length, xs.length, ys.length + k, d⟩
    let N := a3HigherLeviClosure ρ w b c K
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
    have hheight : a3KeyHeight b c K <
        (b : ℤ) + c + zs.length - (ys.length + p.2.length : ℕ) := by
      dsimp [a3KeyHeight, K]
      omega
    have hbase : (aWord (fun i => ρ.op (F (a3ConvA 1)) i) p.1 *
        PowerSeries.coeff z.2
          (bWord (fun i => ρ.op (F (a3ConvB 1)) i) p.2)) •
        (((ys.map fun i => ρ.op (F (a3ConvB 1)) i).prod *
          (zs.map fun i => ρ.op (F (a3ConvSpectator 1)) i).prod) • w) ∈ N := by
      apply a3CountSpan_le_higher ρ w b c K zs.length
        p.1.length (ys.length + p.2.length) hheight
      simpa [aWord, a3ConvA, a3ConvB, a3ConvSpectator,
        mul_smul] using ha
    have hf := a3_fCurrent_pow_preserves ρ 1
      (a3HigherKeySpan ρ w b c K) (k - p.2.length) z.1 hbase
    simpa [N, K, a3ConvKey, a3ConvA, a3ConvB,
      a3ConvSpectator, mul_assoc, mul_smul] using hf

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_lower_wick_summand
