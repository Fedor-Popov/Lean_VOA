import VOA.Classification.COne.OrbOctaZCZeroMode

/-! The positive polynomial annihilates the weight-sixteen seed. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA VertexOperatorAlgebra OrbOdd OrbZhu OrbOctaR OrbC2c OrbSpan
  OrbC2b OrbOctaRC VOA.LatGen VOA.LatGen.Triplet PlusUnitary

private def topProbe : (orbifold octa).carrier →ₗ[ℂ] ℂ :=
  (ambientProbe 1).comp (orbifold octa).carrier.subtype

private theorem topProbe_Lneg (k : ℕ) (v : (orbifold octa).carrier) :
    topProbe (W.L (-(k : ℤ) - 1) v) = 0 := by
  change (v2mVirUnitary 1 le_rfl).form
    ((V2m 1 le_rfl).L (-(k : ℤ) - 1) (v : LatModuleGen (latP 1)))
    (latChargeGen (latP 1) (4 : ℤ)) = 0
  rw [(v2mVirUnitary 1 le_rfl).adjoint,
    show -(-(k : ℤ) - 1) = (k : ℤ) + 1 by omega,
    OrbPrim.chargeGen_primary 4 k, map_zero]

private theorem q24_vacWord (ks : List ℕ) (hne : ks ≠ []) :
    q24L (mk W (virWord W ks W.vacuum)) = 0 := by
  induction ks with
  | nil => exact (hne rfl).elim
  | cons k ks ih =>
    rw [virWord, show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by omega,
      mk_L_neg W (virWord_grading W W.vacuum_mem ks) (k + 1) (by omega)]
    simp only [map_smul, map_add, q24L_omega, smul_zero, zero_add]
    cases ks with
    | nil => simp [OrbOctaR.wordWeight]
    | cons j js => rw [ih (by simp), smul_zero, smul_zero]

private def seed16Kernel : Submodule ℂ (orbifold octa).carrier :=
  LinearMap.ker (q24L.comp (mk W)) ⊓ LinearMap.ker topProbe

private theorem mode15_mem : W.smul X 15 X ∈
    seed16Kernel ⊔ Submodule.span ℂ {X} := by
  have hg : W.smul X 15 X ∈ W.grading 16 := by
    convert W.grading_mode _ X_grading _ X_grading 15 using 2
  have hs := grading_lt_36 16 (by norm_num) hg
  have hp : ∀ z ∈ twoSeedSpan,
      piHom W 16 z ∈ seed16Kernel ⊔ Submodule.span ℂ {X} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨ks, rfl | rfl⟩ := hz
      · have hw := virWord_grading W W.vacuum_mem ks
        by_cases he : 0 + (OrbOctaR.wordWeight ks : ℤ) = 16
        · rw [piHom_of_mem W (he ▸ hw)]
          apply Submodule.mem_sup_left
          refine ⟨q24_vacWord ks ?_, ?_⟩
          · intro h; simp [h, OrbOctaR.wordWeight] at he
          · cases ks with
            | nil => simp [OrbOctaR.wordWeight] at he
            | cons k ks => exact topProbe_Lneg k _
        · rw [piHom_of_mem_ne W he hw]; exact Submodule.zero_mem _
      · cases ks with
        | nil =>
          rw [virWord, piHom_of_mem W X_grading]
          exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
        | cons k ks =>
          have hw := virWord_grading W X_grading (k :: ks)
          have he : (16 : ℤ) + OrbOctaR.wordWeight (k :: ks) ≠ 16 := by
            simp only [OrbOctaR.wordWeight, List.map_cons, List.sum_cons, Nat.cast_add,
              Nat.cast_one]
            omega
          rw [piHom_of_mem_ne W he hw]; exact Submodule.zero_mem _
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  simpa only [piHom_of_mem W hg] using hp _ hs

/-- The first of the four requested non-vacuum seed identities. -/
theorem q24_seed16 : q24L (mk W X) = 0 := by
  obtain ⟨z, hz, y, hy, he⟩ := Submodule.mem_sup.mp mode15_mem
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hzq : q24L (mk W z) = 0 := hz.1
  have hzp : topProbe z = 0 := hz.2
  have hb : b ≠ 0 := by
    intro hb
    have hh := congrArg topProbe he
    rw [map_add, map_smul, hzp, hb, zero_smul, add_zero] at hh
    have hv : topProbe (W.smul X 15 X) = (1862784 / 5 : ℂ) :=
      primary_ground_coupling
    rw [hv] at hh
    norm_num at hh
  have hh := congrArg (fun z => q24L (mk W z)) he
  change q24L (mk W (z + b • X)) = q24L (selfMode 15) at hh
  rw [map_add, map_smul, map_add, map_smul, hzq, zero_add] at hh
  change b • q24L (mk W X) = q24L (selfMode 15) at hh
  rw [q24_selfMode15] at hh
  exact (smul_eq_zero.mp hh).resolve_left hb

end VOA.Classification.COne.OrbOctaZC
