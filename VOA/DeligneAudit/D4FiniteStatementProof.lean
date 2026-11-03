/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FiniteIdentity
import VOA.DeligneAudit.DeligneCharacterD4FiniteStatement

/-!
# `D4F.D4FiniteIdentity`, discharged

Matches the `d4FiniteIdentity` / `d4Q_spec` (`D4FiniteIdentity.lean`) with the published
statement `VOA.DeligneAudit.DeligneCharacter.D4F.D4FiniteIdentity`
(`DeligneCharacterD4FiniteStatement.lean`): same ring, same monomials
(`D4F.mono (D4F.ev l) = mo l`), the products agree up to reordering of the sixteen linear factors
(`List.Perm`, checked by `decide`),
and the `demazurePi` (`Finsupp.linearCombination` of the string formula) equals the `demazure`.
-/

namespace VOA.DeligneAudit.D4Finite

open scoped BigOperators
open Gen

namespace Bridge

open VOA.DeligneAudit.DeligneCharacter

noncomputable section

theorem mono_ev (l : List ℤ) : D4F.mono (D4F.ev l) = mo l := rfl

theorem oneSub_eq (l : List ℤ) : D4F.oneSub l = 1 - mo l := rfl

theorem prod_pairs (ws : List (List ℤ)) (g h : List ℤ → List ℤ) :
    (ws.map fun a => (1 - mo (g a)) * (1 - mo (h a))).prod =
      ((ws.flatMap fun a => [g a, h a]).map fun l => 1 - mo l).prod := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
      rw [List.map_cons, List.prod_cons, ih, List.flatMap_cons, List.map_append, List.prod_append]
      simp [mul_assoc]

theorem prodOneSub_eq (fs : List (List ℤ)) : D4F.prodOneSub fs = (fs.map fun l => 1 - mo l).prod :=
  rfl

theorem P0_eq : D4F.P0 = d4P0 := by
  rw [D4F.P0, prodOneSub_eq, d4P0]
  unfold fA
  rw [prod_pairs]
  apply List.Perm.prod_eq
  apply List.Perm.map
  decide

theorem Ptheta_eq : D4F.Ptheta = d4Ptheta := by
  rw [D4F.Ptheta, prodOneSub_eq, d4Ptheta]
  unfold fA
  rw [prod_pairs]
  apply List.Perm.prod_eq
  apply List.Perm.map
  decide

theorem Pplus_eq : D4F.Pplus = d4Pplus := by
  rw [D4F.Pplus, prodOneSub_eq, d4Pplus,
    show (wtsQZ.map fun a => 1 - mo (addE [0, 1, 1] (embL a))) =
      (wtsQZ.map fun a => addE [0, 1, 1] (embL a)).map (fun l => 1 - mo l) by
        rw [List.map_map]; rfl]
  apply List.Perm.prod_eq
  apply List.Perm.map
  decide

theorem Pminus_eq : D4F.Pminus = d4Pminus := by
  rw [D4F.Pminus, prodOneSub_eq, d4Pminus,
    show (wtsQZ.map fun a => 1 - mo (addE [0, 1, -1] (embL a))) =
      (wtsQZ.map fun a => addE [0, 1, -1] (embL a)).map (fun l => 1 - mo l) by
        rw [List.map_map]; rfl]
  apply List.Perm.prod_eq
  apply List.Perm.map
  decide

theorem demazurePi_eq (i : Fin 4) (f : L7) :
    D4F.demazurePi i f = demazure (d4Roots.getD i []) f := by
  have hpair : ∀ v : Mon, D4F.zPair v (D4F.d4Root i) = pairZ v (d4Roots.getD i []) := by
    intro v
    fin_cases i <;> simp [D4F.zPair, pairZ, D4F.d4Root, d4Roots, Fin.sum_univ_four]
  have hroot : D4F.zEmbed (D4F.d4Root i) = rootZ (d4Roots.getD i []) := by
    fin_cases i <;> funext k <;> fin_cases k <;> rfl
  conv_lhs => rw [← f.sum_single]
  rw [Finsupp.sum, map_sum]
  conv_rhs => rw [← f.sum_single, Finsupp.sum, demazure, demazureG_finset_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [D4F.demazurePi]
  change Finsupp.linearCombination ℤ (D4F.demazureString i) (Finsupp.single v (f v)) =
    demazureG _ _ (AddMonoidAlgebra.single v (f v))
  rw [Finsupp.linearCombination_single]
  rw [demazureG_single]
  unfold D4F.demazureString demMonoG
  simp only [hpair, hroot]
  split_ifs
  · erw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [D4F.mono, shZ, neg_smul, sub_eq_add_neg]
    erw [Finsupp.smul_single, smul_eq_mul, mul_one]
  · erw [smul_neg, Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [D4F.mono, shZ]
    erw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem demazureTheta_eq (f : L7) : D4F.demazureTheta f = piSTheta f := by
  simp only [D4F.demazureTheta, D4F.wordTheta, piSTheta, d4Word, List.foldl_cons, List.foldl_nil,
    demazurePi_eq]
  rfl

end

end Bridge

open VOA.DeligneAudit.DeligneCharacter Bridge in
/-- **the `D4FiniteIdentity`, proved** (with `G₀ = d4Q`). -/
theorem d4FiniteIdentity_holds : D4F.D4FiniteIdentity := by
  refine ⟨d4Q, ?_, ?_⟩
  · rw [oneSub_eq, D4F.Nnum, P0_eq, Ptheta_eq, mono_ev,
      show mo [-1, 0, 0, 1, 1, 0, 0] = mo [-1, 0, 0, 1, 1] from
        mo_congr (by funext i; fin_cases i <;> rfl),
      show mo [-2, 0, 0, 2, 2, 0, 0] = mo [-2, 0, 0, 2, 2] from
        mo_congr (by funext i; fin_cases i <;> rfl)]
    exact d4Q_spec
  · have h := d4FiniteIdentity
    rw [d4LHS, d4RHS, d4F] at h
    simp only [oneSub_eq, mono_ev, demazureTheta_eq, D4F.Dplus, D4F.Dminus, Pplus_eq, Pminus_eq]
    rw [
      show mo [0, 0, 2, 0, 0, 0, 0] = mo [0, 0, 2] from
        mo_congr (by funext i; fin_cases i <;> rfl),
      show mo [1, 2, 0, 0, 0, 0, 0] = mo [1, 2] from
        mo_congr (by funext i; fin_cases i <;> rfl),
      show mo [0, 2, 0, 0, 0, 0, 0] = mo [0, 2] from
        mo_congr (by funext i; fin_cases i <;> rfl),
      show mo [0, 2, 2, 0, 0, 0, 0] = mo [0, 2, 2] from
        mo_congr (by funext i; fin_cases i <;> rfl),
      show mo [1, 2, 2, 0, 0, 0, 0] = mo [1, 2, 2] from
        mo_congr (by funext i; fin_cases i <;> rfl),
      show mo [0, 2, -2, 0, 0, 0, 0] = mo [0, 2, -2] from
        mo_congr (by funext i; fin_cases i <;> rfl),
      show mo [1, 2, -2, 0, 0, 0, 0] = mo [1, 2, -2] from
        mo_congr (by funext i; fin_cases i <;> rfl)]
    rw [d4Dplus, d4Dminus] at h
    linear_combination h

end VOA.DeligneAudit.D4Finite

section AxiomAudit
#print axioms VOA.DeligneAudit.D4Finite.d4FiniteIdentity_holds
end AxiomAudit
