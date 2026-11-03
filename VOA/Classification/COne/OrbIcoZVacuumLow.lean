import VOA.Classification.COne.OrbIcoZLow
import VOA.Classification.COne.OrbB5Vacuum

/-! Actual lower Virasoro descendants vanish on the A5 zero conformal fiber. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu OrbSpan OrbPrim OrbIco OrbIcoS OrbOctaR OrbC2c

section
variable {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0)
include hf

theorem zeroFiber_vacWord (ks : List ℕ) (hne : ks ≠ []) :
    f (mk Wi (virWord Wi ks Wi.vacuum)) = 0 := by
  induction ks with
  | nil => exact (hne rfl).elim
  | cons k ks ih =>
    rw [virWord, show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by omega,
      mk_L_neg Wi (virWord_grading Wi Wi.vacuum_mem ks) (k + 1) (by omega)]
    simp only [map_smul, map_add, hf, smul_zero, zero_add]
    cases ks with
    | nil => simp [OrbOctaR.wordWeight]
    | cons j js => rw [ih (by simp), smul_zero, smul_zero]

/-- Every positive-weight state below the first icosahedral primary vanishes on the zero fiber. -/
theorem zeroFiber_grading_lt36 {N : ℤ} (hpos : 0 < N) (hN : N < 36)
    {y : (orbifold ico).carrier} (hy : y ∈ Wi.grading N) :
    f (mk Wi y) = 0 := by
  let K := LinearMap.ker (f.comp (mk Wi))
  have hp : ∀ z ∈ OrbIcoS.twoSeedSpan, piHom Wi N z ∈ K := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨ks, rfl | rfl⟩ := hz
      · have hw := virWord_grading Wi Wi.vacuum_mem ks
        by_cases he : 0 + (OrbOctaR.wordWeight ks : ℤ) = N
        · rw [piHom_of_mem Wi (he ▸ hw)]
          change f (mk Wi (virWord Wi ks Wi.vacuum)) = 0
          apply zeroFiber_vacWord f hf
          intro h
          simp [h, OrbOctaR.wordWeight] at he
          omega
        · rw [piHom_of_mem_ne Wi he hw]
          exact Submodule.zero_mem _
      · have hw := virWord_grading Wi Xico_grading ks
        rw [piHom_of_mem_ne Wi (by omega : (36 : ℤ) + OrbOctaR.wordWeight ks ≠ N) hw]
        exact Submodule.zero_mem _
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have h := hp y (grading_lt_100 N (by omega) hy)
  simpa only [piHom_of_mem Wi hy, LinearMap.mem_ker, LinearMap.comp_apply] using h

theorem zeroFiber_lowerDesc36 {y : (orbifold ico).carrier}
    (hy : y ∈ lowerDesc Wi 36) : f (mk Wi y) = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, x, hx, rfl⟩ := hy
    by_cases hn : 36 - (m : ℤ) - 1 < 0
    · rw [Wi.positivity _ hn, Submodule.mem_bot] at hx
      rw [hx, map_zero, map_zero, map_zero]
    by_cases h0 : 36 - (m : ℤ) - 1 = 0
    · rw [h0, Wi.vacuum_grade, Submodule.mem_span_singleton] at hx
      obtain ⟨c, hc⟩ := hx
      rw [← hc, map_smul, map_smul, map_smul]
      have h := zeroFiber_vacWord f hf [m] (by simp)
      simpa only [virWord, map_zero, smul_zero] using congrArg (fun z => c • z) h
    · rw [show -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) by omega,
        mk_L_neg Wi hx (m + 1) (by omega)]
      simp only [map_smul, map_add, hf, zeroFiber_grading_lt36 f hf (by omega) (by omega) hx,
        smul_zero, add_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, map_smul, ha, smul_zero]

end
end VOA.Classification.COne.OrbIcoZ
