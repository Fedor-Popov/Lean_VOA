import VOA.Classification.COne.OrbOctaRCExp

/-! Assemble shared exponential descendants into actual screening identities. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2g OrbC2h LatMod OrbPrim OrbRat6

def screenTerm (t : ℚ × List ℕ) (Q : RawPoly ℕ) : RawPoly ℕ :=
  reduceTwo (scaleR t.1 (chargePower (t.2.count 0) (chargeScale (-1) Q)))

theorem screenTerm_sound (d : ℤ) (t : ℚ × List ℕ) (Q : RawPoly ℕ)
    (hQ : ∀ c : ℂ, c * c = ((2 : ℚ) : ℂ) →
      evRc (a0 1) c Q =
        evRc (a0 1) c (expWordR ((oscillators t.2).map (· + 1)) (2 * d - 1))) :
    fo (sector d (evRc (a0 1) (cα 1) [t])) =
      sector (d - 1) (evRc (a0 1) (cα 1) (screenTerm t Q)) := by
  rw [fo_eq]
  change (V2m 1 le_rfl).smul (latChargeGen (latP 1) (-1 : ℤ)) 0 _ = _
  rw [exponentialActionOne_sound]
  have hd : (-1 : ℤ) + d = d - 1 := by ring
  rw [hd]
  congr 1
  rw [exponentialActionOne, evRc_reduce_two, screenTerm,
    evRc_reduceTwo_of_sq _ _ charge_square_two]
  simp only [onOscillators, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    evRc_scaleR, evRc_chargePower]
  congr 1
  congr 1
  rw [evRc_chargeScale, evRc_chargeScale]
  simp only [liftR, List.map_cons, List.map_nil, expPolyR, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, evRc_normR, evRc_scaleR]
  have hs : -(0 : ℤ) - 1 - 2 * (-1) * d = 2 * d - 1 := by ring
  rw [hs]
  simpa using (hQ (-cα 1) (by simpa using charge_square_two)).symm

theorem screenRows_sound (d : ℤ) (P : RawPoly ℕ) (Qs : List (RawPoly ℕ))
    (h : List.Forall₂ (fun t Q =>
      fo (sector d (evRc (a0 1) (cα 1) [t])) =
        sector (d - 1) (evRc (a0 1) (cα 1) Q)) P Qs) :
    fo (sector d (evRc (a0 1) (cα 1) P)) =
      sector (d - 1) (evRc (a0 1) (cα 1) Qs.flatten) := by
  induction h with
  | nil => simp [evRc_nil]
  | @cons t Q P Qs hp _ ih =>
    rw [show t :: P = [t] ++ P from rfl, evRc_append, map_add, map_add, hp, ih,
      List.flatten_cons, evRc_append, map_add]

theorem screenRows_reduce (d : ℤ) (P : RawPoly ℕ) (Qs : List (RawPoly ℕ))
    (h : List.Forall₂ (fun t Q =>
      fo (sector d (evRc (a0 1) (cα 1) [t])) =
        sector (d - 1) (evRc (a0 1) (cα 1) Q)) P Qs)
    (R : RawPoly ℕ) (hr : reduceTwo Qs.flatten = R) :
    fo (sector d (evRc (a0 1) (cα 1) P)) =
      sector (d - 1) (evRc (a0 1) (cα 1) R) := by
  rw [screenRows_sound d P Qs h, ← hr, evRc_reduceTwo_of_sq _ _ charge_square_two]

end VOA.Classification.COne.OrbOctaRC
