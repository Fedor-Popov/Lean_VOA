import VOA.DeligneAudit.D4LeviKSRzTargetTwo
import VOA.DeligneAudit.D4LeviKSTargetSymmetricEmbeds

/-! Complete homogeneous two-letter modes for the Rz relation. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def rzTwoComplete (s : ℕ) : MvPolynomial (Fin 2) ℂ :=
  ∑ p ∈ Finset.antidiagonal s, X (0 : Fin 2) ^ p.1 * X (1 : Fin 2) ^ p.2

theorem rzTwoComplete_symmetric (s : ℕ) :
    rzTwoComplete s ∈ symmetricSubalgebra (Fin 2) ℂ := by
  change (rzTwoComplete s).IsSymmetric
  intro e
  have he : e = Equiv.refl (Fin 2) ∨ e = Equiv.swap 0 1 := by
    fin_cases e <;> decide
  rcases he with rfl | rfl
  · simp
  · simp only [rzTwoComplete, map_sum, map_pow, map_mul, rename_X]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [← Finset.Nat.sum_antidiagonal_swap]
    apply Finset.sum_congr rfl
    intro p hp
    simp [Prod.swap, mul_comm]

theorem rz_two_topSum (ρ : CurrentModule D4sector.f V) (s : ℕ) :
    topSum (yOp ρ) (zOp ρ) 2 s [0, 0] =
      ∑ p ∈ Finset.antidiagonal s, zOp ρ p.1 * zOp ρ p.2 := by
  simp [topSum, choices, aWord, bWord, bTail, PowerSeries.coeff_mul]

theorem rzTwoComplete_source_eval
    (ρ : CurrentModule D4sector.f V) (w : V) (s : ℕ) :
    xyzEvaluation ρ w (pairSourceShape 0 0 2)
        (rename (fun z : Fin 2 =>
          (Sum.inr (Sum.inr z) : PairSource 0 0 2)) (rzTwoComplete s)) =
      ∑ p ∈ Finset.antidiagonal s, zOp ρ p.1 (zOp ρ p.2 w) := by
  rw [rzTwoComplete, map_sum]
  simp only [map_mul, map_pow, rename_X, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul]
  simp only [one_mul]
  change xyzEvaluation ρ w (pairSourceShape 0 0 2)
    (modeMonomial (PairSource 0 0 2)
      (Finsupp.single (Sum.inr (Sum.inr (0 : Fin 2))) p.1 +
        Finsupp.single (Sum.inr (Sum.inr (1 : Fin 2))) p.2)) = _
  unfold xyzEvaluation
  rw [modeWordEvaluation_monomial]
  have hset : (Finset.univ : Finset (PairSource 0 0 2)) =
      {Sum.inr (Sum.inr (0 : Fin 2)),
        Sum.inr (Sum.inr (1 : Fin 2))} := by
    ext t
    rcases t with (x | x) | (y | z)
    · exact Fin.elim0 x
    · exact Fin.elim0 x
    · exact Fin.elim0 y
    · fin_cases z <;> simp
  have hperm : (Finset.univ.toList : List (PairSource 0 0 2)).Perm
      [Sum.inr (Sum.inr (0 : Fin 2)),
        Sum.inr (Sum.inr (1 : Fin 2))] := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (by simp)).2
    intro t
    rw [Finset.mem_toList, hset]
    simp
  let d : PairSource 0 0 2 →₀ ℕ :=
    Finsupp.single (Sum.inr (Sum.inr (0 : Fin 2))) p.1 +
      Finsupp.single (Sum.inr (Sum.inr (1 : Fin 2))) p.2
  have hword : (shapedModes (pairSourceShape 0 0 2)
      Finset.univ.toList d).Perm
      [(5, p.1), (5, p.2)] := by
    simpa [shapedModes, pairSourceShape, d] using
      hperm.map (fun t : PairSource 0 0 2 => (pairSourceShape 0 0 2 t, d t))
  exact (radicalWord_perm ρ w hword).trans (by
    simp [radicalWord, wordOp, zOp, radicalColour])

theorem rz_target_two_complete_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V) (m i s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey 0 0 2 s)
    (hs : m + 1 ≤ 2 + s) :
    (⟨rename (fun z : Fin 2 =>
        (Sum.inr (Sum.inr z) : PairTarget 0 0 2)) (rzTwoComplete s),
      pairTarget_symmetric_Z_mem 0 0 2 (rzTwoComplete s)
        (rzTwoComplete_symmetric s)⟩ : pairTargetSymmetric 0 0 2) ∈
      (pairTargetQuotientEvaluation ρ w m i 0 0 2
        (pairKernelPrefix_of_sat ρ w m i 0 0 2 s h hi hkey)).ker := by
  let P : pairSourceSymmetric 0 0 2 :=
    ⟨rename (fun z : Fin 2 =>
        (Sum.inr (Sum.inr z) : PairSource 0 0 2)) (rzTwoComplete s),
      pairSource_symmetric_Z_mem 0 0 2 (rzTwoComplete s)
        (rzTwoComplete_symmetric s)⟩
  apply pairTargetQuotientEvaluation_mem_ker_of_sat
    ρ w m i 0 0 2 s h hi hkey _ P
  · apply Subtype.ext
    exact pairRestriction_Z_embedding 0 0 2 (rzTwoComplete s)
  · have hk : keyEnum m ⟨i, hi⟩ = rzKey [] [] [] 2 s := by
      simpa [pairFinalKey, rzKey] using hkey
    have hr := rz_top_prefix ρ w m h [] [] [] 2 s i
      (by omega) hs hi (by simpa using hk)
    rw [rzTwoComplete_source_eval]
    simpa [rz_two_topSum, Finset.sum_smul, Module.End.mul_apply] using hr

theorem rz_target_two_complete_mul_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V) (m i s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey 0 0 2 s)
    (hs : m + 1 ≤ 2 + s) (U : pairTargetSymmetric 0 0 2) :
    U * (⟨rename (fun z : Fin 2 =>
        (Sum.inr (Sum.inr z) : PairTarget 0 0 2)) (rzTwoComplete s),
      pairTarget_symmetric_Z_mem 0 0 2 (rzTwoComplete s)
        (rzTwoComplete_symmetric s)⟩ : pairTargetSymmetric 0 0 2) ∈
      (pairTargetQuotientEvaluation ρ w m i 0 0 2
        (pairKernelPrefix_of_sat ρ w m i 0 0 2 s h hi hkey)).ker := by
  exact pairTargetQuotientEvaluation_mul_mem_ker ρ w m i 0 0 2
    h hi (pairKernelPrefix_of_sat ρ w m i 0 0 2 s h hi hkey)
    _ U (rz_target_two_complete_mem_ker ρ w m i s h hi hkey hs)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzTwoComplete_symmetric
#print axioms VOA.DeligneAudit.D4Levi.rz_two_topSum
#print axioms VOA.DeligneAudit.D4Levi.rzTwoComplete_source_eval
#print axioms VOA.DeligneAudit.D4Levi.rz_target_two_complete_mem_ker
#print axioms VOA.DeligneAudit.D4Levi.rz_target_two_complete_mul_mem_ker
