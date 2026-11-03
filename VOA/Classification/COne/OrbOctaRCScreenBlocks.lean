import VOA.Classification.COne.OrbOctaRCScreen

/-! Linear assembly of the small screening certificates. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2e OrbC2g OrbC2h LatMod OrbRat6

theorem screenBlocks_sound (d : ℤ) (Ps Qs : List (RawPoly ℕ))
    (h : List.Forall₂ (fun P Q =>
      fo (sector d (evRc (a0 1) (cα 1) P)) =
        sector (d - 1) (evRc (a0 1) (cα 1) Q)) Ps Qs) :
    fo (sector d (evRc (a0 1) (cα 1) Ps.flatten)) =
      sector (d - 1) (evRc (a0 1) (cα 1) Qs.flatten) := by
  induction h with
  | nil => simp [evRc_nil]
  | cons hp _ ih =>
    simp only [List.flatten_cons, evRc_append, map_add]
    rw [hp, ih]

theorem screenBlocks_reduce (d : ℤ) (Ps Qs : List (RawPoly ℕ))
    (h : List.Forall₂ (fun P Q =>
      fo (sector d (evRc (a0 1) (cα 1) P)) =
        sector (d - 1) (evRc (a0 1) (cα 1) Q)) Ps Qs)
    (R : RawPoly ℕ) (hr : reduceTwo Qs.flatten = R) :
    fo (sector d (evRc (a0 1) (cα 1) Ps.flatten)) =
      sector (d - 1) (evRc (a0 1) (cα 1) R) := by
  rw [screenBlocks_sound d Ps Qs h, ← hr, evRc_reduceTwo_of_sq _ _ charge_square_two]

end VOA.Classification.COne.OrbOctaRC
