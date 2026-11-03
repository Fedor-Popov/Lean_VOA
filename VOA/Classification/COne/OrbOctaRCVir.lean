import VOA.Classification.COne.OrbOctaRCExp
import VOA.Classification.COne.OrbOctaRCAdjoint

/-! Finite oscillator evaluation of lattice Virasoro modes. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2g OrbC2h LatMod

def neutralQuickOne (Q : RawPoly ℕ) (n d : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  reduceTwo (onOscillators
    (fun R => chargeScale d (polyQuick Q (-n - 1) (liftR R))) P)

theorem neutralQuickOne_sound (Q P : RawPoly ℕ) (n d : ℤ) :
    evRc (a0 1) (cα 1) (neutralQuickOne Q n d P) =
      evRc (a0 1) (cα 1) (neutralActionOne Q n d P) := by
  rw [neutralQuickOne, neutralActionOne, evRc_reduceTwo_of_sq _ _ charge_square_two,
    evRc_reduce_two]
  simp only [onOscillators, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [evRc_scaleR, evRc_scaleR, evRc_chargePower, evRc_chargePower,
    evRc_chargeScale, evRc_chargeScale, evRc_polyQuick]

theorem virOne_sound (m d : ℤ) (P : RawPoly ℕ) :
    (V2m 1 le_rfl).L m (sector d (evRc (a0 1) (cα 1) P)) =
      sector d (evRc (a0 1) (cα 1) (neutralQuickOne omR (m + 1) d P)) := by
  rw [neutralQuickOne_sound]
  have ho : ls 1 omR = (V2m 1 le_rfl).conformalVector := (omega_coe 1 le_rfl).symm
  rw [← neutralActionOne_sound, ho]
  rfl

theorem virOne_blocks (m d : ℤ) (Ps Qs : List (RawPoly ℕ))
    (h : List.Forall₂ (fun P Q => neutralQuickOne omR (m + 1) d P = Q) Ps Qs) :
    (V2m 1 le_rfl).L m (sector d (evRc (a0 1) (cα 1) Ps.flatten)) =
      sector d (evRc (a0 1) (cα 1) Qs.flatten) := by
  induction h with
  | nil => simp [evRc_nil]
  | cons hp _ ih =>
    simp only [List.flatten_cons, evRc_append, map_add]
    rw [virOne_sound, hp, ih]

end VOA.Classification.COne.OrbOctaRC
