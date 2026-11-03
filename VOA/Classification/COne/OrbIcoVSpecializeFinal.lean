import VOA.Classification.COne.OrbIcoVSpecializeGeneric
import VOA.Classification.COne.OrbIcoVActualSpecializationWard

/-! Genuine normalized finite Fock Ward solutions at c=1 with the certified Xu coefficients. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.VirasoroScreening
  InverseDS.VirasoroVerma Filter Topology
open scoped Classical

/-- The actual Ward sequence, actual local image bases, descended scalar rows,
and actual channel ground injectivity together specialize to the c=1 fiber. -/
theorem exists_specialized_finite_Fock (self : Bool) (N : ℕ)
    (hN : OrbIcoW.channelBound self≤N)
    (hR : 2*N < (if self then 64 else 100))
    (indices : Fin 2 → ℕ) (hn : ∀ r, indices r≤OrbIcoW.channelBound self) :
    ∃ a : FiniteFockPBW self (2*N),
      ∃ v : FiniteFockColumns self (2*N) → ℂ,
        (∀ n : Fin (2*N+1), LinearIndependent ℂ (symbolColumns self n.val (a n) 1)) ∧
        finiteBlockProbe self (2*N) a ⟨0,by omega⟩ v=1 ∧
        finiteWardRowMap self (2*N) a 1 v=0 ∧
        ∀ r, (2:ℂ)^(indices r) *
          finiteBlockProbe self (2*N) a
            (finiteEvenPositions N indices (fun r => (hn r).trans hN) r) v =
              ((((OrbIcoW.valueJets self (indices r))[0]?).getD 0 : ℚ) : ℂ) := by
  let hle : ∀ r, indices r≤N := fun r => (hn r).trans hN
  obtain ⟨a,hLI,hker⟩ := exists_generic_finite_kernel self N indices hle
  let values : ℂ → Fin 2 → ℂ := fun s r =>
    genericSymbolCoefficient self N (s^2) (indices r)/(2:ℂ)^(indices r)
  let value : Fin 2 → ℂ := fun r =>
    ((((OrbIcoW.valueJets self (indices r))[0]?).getD 0 : ℚ) : ℂ)/(2:ℂ)^(indices r)
  have hv (r : Fin 2) : Tendsto (fun s => values s r) OrbIcoW.nonrealNhdsOne (𝓝 (value r)) :=
    (OrbIcoW.genericSymbolCoefficient_square_tendsto self N (indices r) hN (hn r)).div_const _
  obtain ⟨v,hv0,hvw,hvs⟩ := finiteFock_normalized_specialization self (2*N) a
    (finiteEvenPositions N indices hle) (fun s : ℂ => s) values value
    (tendsto_id.mono_right nhdsWithin_le_nhds) hv hker
    (finiteWard_ground_injective self (2*N) hR a hLI)
  refine ⟨a,v,hLI,hv0,hvw,fun r => ?_⟩
  rw [hvs r]
  change (2:ℂ)^(indices r) *
    (((((OrbIcoW.valueJets self (indices r))[0]?).getD 0 : ℚ) : ℂ)/(2:ℂ)^(indices r)) = _
  rw [mul_comm,div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num : (2:ℂ)≠0))]

/-- Both vacuum Xu coefficients occur in one genuine normalized c=1 Ward solution. -/
theorem exists_specialized_vacuum_Xu :
    ∃ a : FiniteFockPBW false 76,
      ∃ v : FiniteFockColumns false 76 → ℂ,
        finiteBlockProbe false 76 a ⟨0,by omega⟩ v=1 ∧
        finiteWardRowMap false 76 a 1 v=0 ∧
        (2:ℂ)^37*finiteBlockProbe false 76 a ⟨74,by omega⟩ v=(xuU37:ℂ) ∧
        (2:ℂ)^38*finiteBlockProbe false 76 a ⟨76,by omega⟩ v=(xuU38:ℂ) := by
  obtain ⟨a,v,hLI,hv0,hvw,hvs⟩ := exists_specialized_finite_Fock false 38 (by decide)
    (by decide) (fun r => if r=0 then 37 else 38) (by intro r; dsimp only; split_ifs <;> decide)
  refine ⟨a,v,hv0,hvw,?_,?_⟩
  · simpa only [Fin.val_zero,if_pos rfl,finiteEvenPositions,OrbIcoW.vac37_value] using hvs 0
  · simpa only [show (1:Fin 2)≠0 by decide,if_neg,finiteEvenPositions,OrbIcoW.vac38_value] using hvs 1

/-- Both self-channel Xu coefficients occur in one genuine normalized c=1 Ward solution. -/
theorem exists_specialized_self_Xu :
    ∃ a : FiniteFockPBW true 40,
      ∃ v : FiniteFockColumns true 40 → ℂ,
        finiteBlockProbe true 40 a ⟨0,by omega⟩ v=1 ∧
        finiteWardRowMap true 40 a 1 v=0 ∧
        (2:ℂ)^19*finiteBlockProbe true 40 a ⟨38,by omega⟩ v=(xuV19:ℂ) ∧
        (2:ℂ)^20*finiteBlockProbe true 40 a ⟨40,by omega⟩ v=(xuV20:ℂ) := by
  obtain ⟨a,v,hLI,hv0,hvw,hvs⟩ := exists_specialized_finite_Fock true 20 (by decide)
    (by decide) (fun r => if r=0 then 19 else 20) (by intro r; dsimp only; split_ifs <;> decide)
  refine ⟨a,v,hv0,hvw,?_,?_⟩
  · simpa only [Fin.val_zero,if_pos rfl,finiteEvenPositions,OrbIcoW.self19_value] using hvs 0
  · simpa only [show (1:Fin 2)≠0 by decide,if_neg,finiteEvenPositions,OrbIcoW.self20_value] using hvs 1

end VOA.Classification.COne.OrbIcoV
