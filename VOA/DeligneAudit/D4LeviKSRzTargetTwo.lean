import VOA.DeligneAudit.D4LeviKSRzTargetBase

/-! The first two-Z target relation, valid for every Demazure weight. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rz_target_two_power_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V) (m i s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey 0 0 2 s)
    (hs : m ≤ s) :
    (⟨pairTargetPower 0 0 2 2 s, pairTargetPower_mem 0 0 2 2 s⟩ :
      pairTargetSymmetric 0 0 2) ∈
      (pairTargetQuotientEvaluation ρ w m i 0 0 2
        (pairKernelPrefix_of_sat ρ w m i 0 0 2 s h hi hkey)).ker := by
  let P : pairSourceSymmetric 0 0 2 :=
    ⟨pairSourcePower 0 0 2 2 s, pairSourcePower_mem 0 0 2 2 s⟩
  apply pairTargetQuotientEvaluation_mem_ker_of_sat
    ρ w m i 0 0 2 s h hi hkey _ P
  · apply Subtype.ext
    simpa [P, pairSourcePower, pairTargetPower] using
      (pairRestriction_ZPsum 0 0 2 s)
  · have hz : zOp ρ s (zOp ρ 0 w) ∈ keyPrefix ρ w m i := by
      have hk : keyEnum m ⟨i, hi⟩ = rzKey [] [] [0] 1 s := by
        simpa [pairFinalKey, rzKey] using hkey
      have hr := rz_top_prefix ρ w m h [] [] [0] 1 s i
        (by omega) (by omega) hi (by simpa using hk)
      simpa [rz_single_topSum, yOp, zOp] using hr
    have hp : (P : MvPolynomial (PairSource 0 0 2) ℂ) =
        X (Sum.inr (Sum.inr (0 : Fin 2))) ^ s +
          X (Sum.inr (Sum.inr (1 : Fin 2))) ^ s := by
      simp [P, pairSourcePower, pairSourceZPsum, Fin.sum_univ_two]
    rw [hp, map_add]
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
    -- Both placements give the same radical word since the radical is abelian.
    have h0 : xyzEvaluation ρ w (pairSourceShape 0 0 2)
        (X (Sum.inr (Sum.inr (0 : Fin 2))) ^ s) =
        zOp ρ s (zOp ρ 0 w) := by
      rw [X_pow_eq_monomial]
      change modeWordEvaluation (PairSource 0 0 2) _
        (modeMonomial (PairSource 0 0 2)
          (Finsupp.single (Sum.inr (Sum.inr (0 : Fin 2))) s)) = _
      rw [modeWordEvaluation_monomial]
      have hword : (shapedModes (pairSourceShape 0 0 2)
          Finset.univ.toList
          (Finsupp.single (Sum.inr (Sum.inr (0 : Fin 2))) s)).Perm
          [(5, s), (5, 0)] := by
        simpa [shapedModes, pairSourceShape] using
          hperm.map (fun t => (pairSourceShape 0 0 2 t,
            (Finsupp.single (Sum.inr (Sum.inr (0 : Fin 2))) s) t))
      exact (radicalWord_perm ρ w hword).trans (by
        simp [radicalWord, wordOp, zOp, radicalColour])
    have h1 : xyzEvaluation ρ w (pairSourceShape 0 0 2)
        (X (Sum.inr (Sum.inr (1 : Fin 2))) ^ s) =
        zOp ρ 0 (zOp ρ s w) := by
      rw [X_pow_eq_monomial]
      change modeWordEvaluation (PairSource 0 0 2) _
        (modeMonomial (PairSource 0 0 2)
          (Finsupp.single (Sum.inr (Sum.inr (1 : Fin 2))) s)) = _
      rw [modeWordEvaluation_monomial]
      have hword : (shapedModes (pairSourceShape 0 0 2)
          Finset.univ.toList
          (Finsupp.single (Sum.inr (Sum.inr (1 : Fin 2))) s)).Perm
          [(5, 0), (5, s)] := by
        simpa [shapedModes, pairSourceShape] using
          hperm.map (fun t => (pairSourceShape 0 0 2 t,
            (Finsupp.single (Sum.inr (Sum.inr (1 : Fin 2))) s) t))
      exact (radicalWord_perm ρ w hword).trans (by
        simp [radicalWord, wordOp, zOp, radicalColour])
    rw [h0, h1]
    have hcomm : zOp ρ 0 (zOp ρ s w) = zOp ρ s (zOp ρ 0 w) := by
      simpa [zOp, radicalColour] using (radical_ops_comm ρ 5 5 0 s w)
    rw [hcomm]
    exact (keyPrefix ρ w m i).add_mem hz hz

theorem rz_target_two_mul_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V) (m i s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey 0 0 2 s)
    (hs : m ≤ s) (U : pairTargetSymmetric 0 0 2) :
    U * (⟨pairTargetPower 0 0 2 2 s,
      pairTargetPower_mem 0 0 2 2 s⟩ : pairTargetSymmetric 0 0 2) ∈
      (pairTargetQuotientEvaluation ρ w m i 0 0 2
        (pairKernelPrefix_of_sat ρ w m i 0 0 2 s h hi hkey)).ker := by
  exact pairTargetQuotientEvaluation_mul_mem_ker ρ w m i 0 0 2
    h hi (pairKernelPrefix_of_sat ρ w m i 0 0 2 s h hi hkey)
    _ U (rz_target_two_power_mem_ker ρ w m i s h hi hkey hs)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_target_two_power_mem_ker
#print axioms VOA.DeligneAudit.D4Levi.rz_target_two_mul_mem_ker
