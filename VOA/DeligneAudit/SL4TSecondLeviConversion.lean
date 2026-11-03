import VOA.DeligneAudit.SL4TSecondLeviCompleteRelations

/-! Adjacent-letter conversion modulo the merged second Levi count filtration. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviTypeA VOA.DeligneAudit.LeviConversion

variable {B V : Type} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable V) (β : B →ₗ[ℂ] V)

/-- Counts with more simple letters at the same depth lie in the earlier Levi closure. -/
theorem secondLeviCountLayer_le_higher (n k u v : ℕ)
    (hd : u + v = n + k) (hh : n < u) :
    secondLeviCountLayer Q β u v ≤ higherSecondLeviCountClosure Q β n k := by
  apply (a2LeviClosure_contains Q _).trans'
  exact le_iSup_of_le u (le_iSup_of_le v (le_iSup_of_le ⟨hd, hh⟩ le_rfl))

/-- Every lower contraction has strictly greater second Levi height. -/
theorem secondLeviConversion_lower_summand (n k : ℕ)
    (t : List ℕ × List ℕ) (ht : t ∈ choices (List.replicate n 0 ++ List.replicate k 0))
    (hlt : t.2.length < k) (z : ℕ × ℕ) (φ : B) :
    ((PowerSeries.coeff z.1 (fCurrent (fun i => Q.op 4 i) ^ (k - t.2.length)) *
      aWord (fun i => Q.op 3 i) t.1) *
        PowerSeries.coeff z.2 (bWord (fun i => Q.op 5 i) t.2)) (β φ) ∈
          higherSecondLeviCountClosure Q β n k := by
  have hlen := choices_length (List.replicate n 0 ++ List.replicate k 0) t ht
  simp only [List.length_append, List.length_replicate] at hlen
  have hb := a2_bWord_coeff_count Q (β φ) t.2 z.2 0 0 (a2CountSpan_zero Q (β φ))
  have ha := a2CountSpan_first_word Q (β φ) t.1 0 t.2.length (by simpa using hb)
  have hbase : (aWord (fun i => Q.op 3 i) t.1 *
      PowerSeries.coeff z.2 (bWord (fun i => Q.op 5 i) t.2)) (β φ) ∈
        higherSecondLeviCountClosure Q β n k := by
    apply secondLeviCountLayer_le_higher Q β n k t.1.length t.2.length hlen (by omega)
    apply Submodule.mem_iSup_of_mem φ
    simpa [aWord, Module.End.mul_apply] using ha
  have hf := a2_fCurrent_pow_preserves Q _ (k - t.2.length) z.1 hbase
  simpa only [Module.End.smul_def, Module.End.mul_apply] using hf

theorem secondLeviConversion_lower_term (n k s : ℕ)
    (t : List ℕ × List ℕ) (ht : t ∈ choices (List.replicate n 0 ++ List.replicate k 0))
    (hlt : t.2.length < k) (φ : B) :
    conversionTerm (fun i => Q.op 4 i) (fun i => Q.op 3 i) (fun i => Q.op 5 i)
      k s t (β φ) ∈ higherSecondLeviCountClosure Q β n k := by
  let N := higherSecondLeviCountClosure Q β n k
  have hm : (∑ z ∈ Finset.antidiagonal s,
      (PowerSeries.coeff z.1 (fCurrent (fun i => Q.op 4 i) ^ (k - t.2.length)) *
        aWord (fun i => Q.op 3 i) t.1) *
          PowerSeries.coeff z.2 (bWord (fun i => Q.op 5 i) t.2)) (β φ) ∈ N := by
    rw [LinearMap.sum_apply]
    exact N.sum_mem fun z hz => secondLeviConversion_lower_summand Q β n k t ht hlt z φ
  have hcast : (-1 : Module.End ℂ V) ^ t.2.length *
      (k.descFactorial t.2.length : Module.End ℂ V) =
        algebraMap ℂ (Module.End ℂ V)
          ((-1 : ℂ) ^ t.2.length * (k.descFactorial t.2.length : ℂ)) := by simp
  unfold conversionTerm
  rw [hcast, Module.End.mul_apply, Module.algebraMap_end_apply]
  exact N.smul_mem ((-1 : ℂ) ^ t.2.length * (k.descFactorial t.2.length : ℂ)) hm

/-- The entire lower Wick sum vanishes in the quotient by earlier counts. -/
theorem secondLeviConversion_lowerSum (n k s : ℕ) (φ : B) :
    lowerSum (fun i => Q.op 4 i) (fun i => Q.op 3 i) (fun i => Q.op 5 i)
      k s (List.replicate n 0 ++ List.replicate k 0) (β φ) ∈
        higherSecondLeviCountClosure Q β n k := by
  unfold lowerSum
  change (_ : Module.End ℂ V) • β φ ∈ _
  rw [List.sum_smul]
  simp only [List.map_map, Function.comp_def]
  apply list_sum_mem
  intro v hv
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
  by_cases hlt : t.2.length < k
  · simpa only [if_pos hlt] using secondLeviConversion_lower_term Q β n k s t ht hlt φ
  · simp [hlt]

/-- With zero simple modes, every top contraction has the same coefficient. -/
theorem secondLeviConversion_topSum (n k s : ℕ) (v : V) :
    topSum (fun i => Q.op 3 i) (fun i => Q.op 5 i) k s
      (List.replicate n 0 ++ List.replicate k 0) v =
        ((n + k).choose k : ℂ) •
          (Q.op 3 0 ^ n * PowerSeries.coeff s (fCurrent (fun i => Q.op 5 i) ^ k)) v := by
  have ht := box_top_decomposition (fun i => Q.op 3 i) (fun i => Q.op 5 i)
    (fun i j => a2RadicalOp_comm Q 0 0 i j) k s (List.replicate n 0) []
    (1 : Module.End ℂ V) v
  have hz : lowerModeSpan (fun i => Q.op 3 i) (fun i => Q.op 5 i)
      (List.replicate n 0) (1 : Module.End ℂ V) v = ⊥ := by
    apply le_antisymm _ bot_le
    rw [lowerModeSpan, Submodule.span_le]
    rintro x ⟨xs, ys, hs, rfl⟩
    simp at hs
  rw [BoxTopDecomposition, hz, Submodule.mem_bot] at ht
  simpa [boxTarget, aWord, sub_eq_zero] using ht

/-- Conversion of a current coefficient, retaining its nonzero source term. -/
theorem secondLeviConversion_coefficient (n k s : ℕ) (φ : B) :
    let N := higherSecondLeviCountClosure Q β n k
    N.mkQ ((Q.op 3 0 ^ (n + k))
      ((PowerSeries.coeff s (fCurrent (fun i => Q.op 4 i) ^ k)) (β φ))) =
        (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ((n + k).choose k : ℂ)) •
          N.mkQ ((Q.op 3 0 ^ n)
            ((PowerSeries.coeff s (fCurrent (fun i => Q.op 5 i) ^ k)) (β φ))) := by
  let N := higherSecondLeviCountClosure Q β n k
  have he := congrArg (PowerSeries.coeff s)
    (wick_series (fun i => Q.op 4 i) (fun i => Q.op 3 i) (fun i => Q.op 5 i)
      (fun i j => by
        rw [op_comm_end]; simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable])
      (fun i j => by
        apply sub_eq_zero.mp
        rw [op_comm_end]; simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable])
      (fun i j => a2RadicalOp_comm Q 0 1 i j) k
      (List.replicate n 0 ++ List.replicate k 0))
  rw [aConst_word, PowerSeries.coeff_C_mul, coeff_wickSum, conversion_sum_split] at he
  have hcast : (-1 : Module.End ℂ V) ^ k * (k.factorial : Module.End ℂ V) =
      algebraMap ℂ (Module.End ℂ V) ((-1 : ℂ) ^ k * (k.factorial : ℂ)) := by simp
  have hz : N.mkQ (lowerSum (fun i => Q.op 4 i) (fun i => Q.op 3 i)
      (fun i => Q.op 5 i) k s (List.replicate n 0 ++ List.replicate k 0) (β φ)) = 0 :=
    (Submodule.Quotient.mk_eq_zero N).mpr (secondLeviConversion_lowerSum Q β n k s φ)
  have hv := congrArg (fun T : Module.End ℂ V => N.mkQ (T (β φ))) he
  dsimp only at hv
  rw [hcast, LinearMap.add_apply, Module.End.mul_apply, map_add, hz, add_zero] at hv
  simp only [aWord, List.map_append, List.prod_append, List.map_replicate,
    List.prod_replicate, ← pow_add, Module.End.mul_apply] at hv
  simpa only [Module.algebraMap_end_apply, map_smul, secondLeviConversion_topSum,
    Module.End.mul_apply, smul_smul, mul_comm] using hv

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_le_higher
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_lower_summand
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_lower_term
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_lowerSum
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_topSum
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_coefficient
