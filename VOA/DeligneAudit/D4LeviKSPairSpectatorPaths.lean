import VOA.DeligneAudit.D4LeviKSPairSpectatorHeight

/-! Polynomial XZ paths and U-spectator paths before the last f₃ mode. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem list_sum_mem (N : Submodule ℂ V)
    {α : Type*} (ls : List α) (f : α → V)
    (h : ∀ x ∈ ls, f x ∈ N) : (ls.map f).sum ∈ N := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact N.add_mem (h x (by simp))
        (ih (fun y hy => h y (by simp [hy])))

/-- A product of an XZ derivative and a U derivative remains in the
    higher prefix when fewer than `b` modes have transferred in total. -/
theorem pairXZ_split_adjoint_prefix_monomial
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c deg : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c deg)
    (d : PairXZ a b c →₀ ℕ) (xs us : List ℕ)
    (hn : xs.length + us.length < b) :
    pairAdjoint (ρ.op (17 : Fin 28)) xs
        (pairRadicalOp ρ
          (shapedModes (pairXZRecolourShape a b c 0)
            Finset.univ.toList d))
        (pairModeWord (ρ.op (17 : Fin 28)) us
          (pairRadicalOp ρ (uZeroWord b) w)) ∈
      keyPrefix ρ w m i := by
  let N := keyPrefix ρ w m i
  have hterm (qx qu : List (Fin 6 × ℕ))
      (hx : qx ∈ threeWordsIter xs
        (shapedModes (pairXZRecolourShape a b c 0)
          Finset.univ.toList d))
      (hu : qu ∈ threeWordsIter us.reverse (uZeroWord b)) :
      pairRadicalOp ρ qx (radicalWord ρ w qu) ∈ N := by
    rw [← pairRadicalOp_apply, ← Module.End.mul_apply,
      ← pairRadicalOp_append, pairRadicalOp_apply]
    change radicalWord ρ w (qx ++ qu) ∈ keyPrefix ρ w m i
    rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
    exact keyOrbit_le_higher ρ w m _ _
      (pairXZ_uZero_split_higher m a b c deg d xs us.reverse
        (by simpa using hn) hx hu)
      (keyLayer_le_orbit ρ w _ (radicalWord_mem_key ρ w _))
  rw [pairModeWord_spectator_adjoint _ w
    (fThree_source_mode_zero ρ w m h)]
  rw [fThree_adjoint_iter_radicalOp ρ xs]
  rw [fThree_adjoint_iter_radicalOp ρ us.reverse]
  simp only [LinearMap.smul_apply, map_smul, smul_smul]
  apply N.smul_mem
  rw [pairRadicalOp_sum_apply]
  apply list_sum_mem N
  intro qx hqx
  rw [← pairRadicalOp_apply]
  rw [pairRadicalOp_sum_apply]
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def]
  apply list_sum_mem N
  intro qu hqu
  exact hterm qx qu (by simpa using hqx) (by simpa using hqu)

/-- The higher-prefix source statement extends linearly to every XZ
    mode polynomial. -/
theorem pairXZ_split_adjoint_prefix
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c deg : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c deg)
    (Q : MvPolynomial (PairXZ a b c) ℂ)
    (xs us : List ℕ) (hn : xs.length + us.length < b) :
    pairAdjoint (ρ.op (17 : Fin 28)) xs
        (pairXZRecolourOperator ρ a b c 0 Q)
        (pairModeWord (ρ.op (17 : Fin 28)) us
          (pairRadicalOp ρ (uZeroWord b) w)) ∈
      keyPrefix ρ w m i := by
  induction Q using MvPolynomial.induction_on' with
  | monomial d z =>
      have hm : (monomial d z : MvPolynomial (PairXZ a b c) ℂ) =
          z • modeMonomial (PairXZ a b c) d := by
        simp [modeMonomial, smul_monomial]
      rw [hm, map_smul, pairAdjoint_smul, LinearMap.smul_apply]
      apply (keyPrefix ρ w m i).smul_mem
      change pairAdjoint (ρ.op (17 : Fin 28)) xs
          (pairWordOpEvaluation ρ
            (pairPolynomialWords (pairXZRecolourShape a b c 0)
              (modeMonomial (PairXZ a b c) d))) _ ∈ _
      rw [pairPolynomialWords_monomial, pairWordOpEvaluation_single]
      exact pairXZ_split_adjoint_prefix_monomial ρ w m i a b c deg
        h hi hkey d xs us hn
  | add P Q ihP ihQ =>
      simpa only [map_add, pairAdjoint_add, LinearMap.add_apply] using
        (keyPrefix ρ w m i).add_mem ihP ihQ

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairXZ_split_adjoint_prefix_monomial
#print axioms VOA.DeligneAudit.D4Levi.pairXZ_split_adjoint_prefix
