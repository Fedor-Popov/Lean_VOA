import VOA.Classification.COne.OrbOctaRCVirWords

/-! Blockwise assembly of rational Virasoro descendants. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2e LatMod

theorem comboScale_sound (cs : List (ℚ × List ℕ)) (Ps : List (RawPoly ℕ))
    (hs : List.Forall₂ (fun t P => sector 4 (evRc (a0 1) (cα 1) P) =
      virDesc (V2m 1 le_rfl) t.2 (latChargeGen (latP 1) (4 : ℤ))) cs Ps) :
    sector 4 (evRc (a0 1) (cα 1)
      ((List.zipWith (fun t P => scaleR t.1 P) cs Ps).flatten)) =
        virCombo (V2m 1 le_rfl) (latChargeGen (latP 1) (4 : ℤ)) cs := by
  induction hs with
  | nil => simp [evRc_nil, virCombo]
  | cons h hs ih =>
    simp only [List.zipWith_cons_cons, List.flatten_cons, evRc_append,
      evRc_scaleR, map_add, map_smul, h, ih, virCombo, List.map_cons, List.sum_cons]

theorem combo_merge (P Q : RawPoly ℕ) (cs ds : List (ℚ × List ℕ))
    (hP : sector 4 (evRc (a0 1) (cα 1) P) =
      virCombo (V2m 1 le_rfl) (latChargeGen (latP 1) (4 : ℤ)) cs)
    (hQ : sector 4 (evRc (a0 1) (cα 1) Q) =
      virCombo (V2m 1 le_rfl) (latChargeGen (latP 1) (4 : ℤ)) ds) :
    sector 4 (evRc (a0 1) (cα 1) (reduceTwo (P ++ Q))) =
      virCombo (V2m 1 le_rfl) (latChargeGen (latP 1) (4 : ℤ)) (cs ++ ds) := by
  rw [evRc_reduceTwo_of_sq _ _ charge_square_two, evRc_append, map_add, hP, hQ,
    virCombo_append]

end VOA.Classification.COne.OrbOctaRC
