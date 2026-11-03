import VOA.Classification.COne.OrbIcoVCoefficients
import VOA.Classification.COne.OrbIcoZTop

/-! Actual nonzero initial scalars of the vacuum and spin-six channel sequences. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco OrbIcoS OrbIcoT OrbXu OrbC2c
  VOA.LatGen VOA.LatGen.Triplet

theorem vacuumCoefficient_zero_ne_zero : vacuumCoefficient 0 ≠ 0 := by
  obtain ⟨c, hc, he⟩ := OrbIcoZ.self_top_nonzero
  unfold vacuumCoefficient
  norm_num only [Nat.cast_zero, mul_zero, sub_zero, pow_zero, one_mul]
  rw [he, map_smul, vacuumProbe_vacuum]
  simpa only [smul_eq_mul, mul_one] using hc

private theorem Xico_L (k : ℕ) (hk : 0 < k) : V2v.L (k : ℤ) (Xico : Sp) = 0 := by
  have he := ((mem_prim _).mp Xico_ambient_primary).2 (k - 1)
  rwa [show ((k - 1 : ℕ) : ℤ) + 1 = k by omega] at he

private theorem chargedProbe_vacuum_tower :
    chargedProbe (Xico : Sp) ((Wi.L (-2) ^ 18) Wi.vacuum) = 0 := by
  rw [show 18 = 1 + 17 by omega, pow_add, pow_one, Module.End.mul_apply,
    chargedProbe_L, neg_neg]
  have hz : (V2m 1 le_rfl).L 2 (Xico : Sp) = 0 := by
    simpa using Xico_L 2 (by omega)
  rw [hz, map_zero]

/-- The canonical self coefficient at its lowest level is the certified sixth coupling. -/
theorem sixthCoefficient_eighteen : sixthCoefficient 18 = icoSixthCoupling := by
  have he := chargedProbe_errors (Xico : Sp) (Xico_L 1 (by omega))
    (Xico_L 3 (by omega)) (canonical_mode_remainder 18 (by omega) (by omega))
  change chargedProbe (Xico : Sp)
    (modeSymbol Wi Xico (71 - 2 * 18) 18 (18 - 18)
      (vacuumCoefficient 18) (sixthCoefficient 18)) = 0 at he
  norm_num only [Nat.cast_ofNat, Nat.sub_self, Int.cast_ofNat] at he
  rw [modeSymbol, map_sub, map_sub, map_smul, map_smul,
    chargedProbe_vacuum_tower, smul_zero, sub_zero, pow_zero, Module.End.one_apply] at he
  have hg := ico_ground_coupling
  change chargedProbe (Xico : Sp) (Wi.smul Xico 35 Xico) =
    icoSixthCoupling * chargedProbe (Xico : Sp) Xico at hg
  rw [hg] at he
  have hn : chargedProbe (Xico : Sp) Xico ≠ 0 := Xico_norm_ne_zero
  change icoSixthCoupling * chargedProbe (Xico : Sp) Xico -
    sixthCoefficient 18 * chargedProbe (Xico : Sp) Xico = 0 at he
  exact (mul_right_cancel₀ hn (sub_eq_zero.mp he)).symm

theorem sixthCoefficient_eighteen_ne_zero : sixthCoefficient 18 ≠ 0 := by
  rw [sixthCoefficient_eighteen]
  exact icoSixthCoupling_ne_zero

end VOA.Classification.COne.OrbIcoV
