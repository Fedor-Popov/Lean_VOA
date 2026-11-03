import VOA.DeligneAudit.D4LeviKSTargetKernelIdeal
import VOA.DeligneAudit.D4LeviKSRzSinglePresentation

/-! The one-Z Rz relation in the PAIR target quotient. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rz_target_single_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V) (m i s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey 0 0 1 s)
    (hs : m ≤ s) :
    (⟨pairTargetPower 0 0 1 2 s, pairTargetPower_mem 0 0 1 2 s⟩ :
      pairTargetSymmetric 0 0 1) ∈
      (pairTargetQuotientEvaluation ρ w m i 0 0 1
        (pairKernelPrefix_of_sat ρ w m i 0 0 1 s h hi hkey)).ker := by
  let P : pairSourceSymmetric 0 0 1 :=
    ⟨pairSourcePower 0 0 1 2 s, pairSourcePower_mem 0 0 1 2 s⟩
  apply pairTargetQuotientEvaluation_mem_ker_of_sat
    ρ w m i 0 0 1 s h hi hkey _ P
  · apply Subtype.ext
    simpa [P, pairSourcePower, pairTargetPower] using
      (pairRestriction_ZPsum 0 0 1 s)
  · have hz : ρ.op (27 : Fin 28) s w ∈ keyPrefix ρ w m i := by
      have hk : keyEnum m ⟨i, hi⟩ = rzKey [] [] [] 1 s := by
        simpa [pairFinalKey, rzKey] using hkey
      have hr := rz_top_prefix ρ w m h [] [] [] 1 s i
        (by omega) (by omega) hi (by simpa using hk)
      simpa [rz_single_topSum, yOp, zOp] using hr
    have hp : (P : MvPolynomial (PairSource 0 0 1) ℂ) =
        X (Sum.inr (Sum.inr (0 : Fin 1))) ^ s := by
      simp [P, pairSourcePower, pairSourceZPsum]
    rw [hp, X_pow_eq_monomial]
    change (modeWordEvaluation (PairSource 0 0 1) fun a =>
      radicalWord ρ w
        (shapedModes (pairSourceShape 0 0 1) Finset.univ.toList a))
      (modeMonomial (PairSource 0 0 1)
        (Finsupp.single (Sum.inr (Sum.inr (0 : Fin 1))) s)) ∈
        keyPrefix ρ w m i
    rw [modeWordEvaluation_monomial]
    have hset : (Finset.univ : Finset (PairSource 0 0 1)) =
        {Sum.inr (Sum.inr (0 : Fin 1))} := by
      ext t
      rcases t with (x | yz)
      · rcases x with (x | x)
        · exact Fin.elim0 x
        · exact Fin.elim0 x
      · rcases yz with (y | z)
        · exact Fin.elim0 y
        · fin_cases z
          simp
    have huniv : (Finset.univ.toList : List (PairSource 0 0 1)) =
        [Sum.inr (Sum.inr (0 : Fin 1))] := by
      rw [hset]
      simp
    simpa [huniv, shapedModes, radicalWord, wordOp, pairSourceShape,
      radicalColour] using hz

/-- Every separately symmetric spectator shift of the one-Z Rz relation
    remains in the target kernel at the same descending key. -/
theorem rz_target_single_mul_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V) (m i s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey 0 0 1 s)
    (hs : m ≤ s) (U : pairTargetSymmetric 0 0 1) :
    U * (⟨pairTargetPower 0 0 1 2 s,
      pairTargetPower_mem 0 0 1 2 s⟩ : pairTargetSymmetric 0 0 1) ∈
      (pairTargetQuotientEvaluation ρ w m i 0 0 1
        (pairKernelPrefix_of_sat ρ w m i 0 0 1 s h hi hkey)).ker := by
  exact pairTargetQuotientEvaluation_mul_mem_ker ρ w m i 0 0 1
    h hi (pairKernelPrefix_of_sat ρ w m i 0 0 1 s h hi hkey)
    _ U (rz_target_single_mem_ker ρ w m i s h hi hkey hs)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_target_single_mem_ker
#print axioms VOA.DeligneAudit.D4Levi.rz_target_single_mul_mem_ker
