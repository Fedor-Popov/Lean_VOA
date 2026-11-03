import VOA.Classification.COne.OrbIcoUVir

/-! Exact rational pairings of Virasoro words. Zero norm certificates give
actual state equalities by positivity, including in reducible Verma realizations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbIcoU
open VOA VertexOperatorAlgebra OrbOctaRC OrbSpan

def seedPair (h : ℚ) : List ℕ → ℚ
  | [] => 1
  | k :: ks => if k = 0 then h * seedPair h ks else 0

def pairWords (c h : ℚ) : List ℕ → List ℕ → ℚ
  | [], ls => seedPair h ls
  | k :: ks, ls =>
      ((wordCollect (virWordAction c h k ls)).map fun t => t.1 * pairWords c h ks t.2).sum

def pairCombos (c h : ℚ) (cs ds : List (ℚ × List ℕ)) : ℚ :=
  (cs.map fun s => (ds.map fun t => s.1 * t.1 * pairWords c h s.2 t.2).sum).sum

def virComboAction (c h : ℚ) (m : ℤ) (cs : List (ℚ × List ℕ)) : List (ℚ × List ℕ) :=
  cs.flatMap fun t => wordScale t.1 (virWordAction c h m t.2)

theorem pairCombos_append_left (c h : ℚ) (cs ds es : List (ℚ × List ℕ)) :
    pairCombos c h (cs ++ ds) es = pairCombos c h cs es + pairCombos c h ds es := by
  simp [pairCombos]

theorem pairCombos_flatten_left (c h : ℚ) (blocks : List (List (ℚ × List ℕ)))
    (ds : List (ℚ × List ℕ)) :
    pairCombos c h blocks.flatten ds = (blocks.map fun cs => pairCombos c h cs ds).sum := by
  induction blocks with
  | nil => simp [pairCombos]
  | cons cs blocks ih => simp only [List.flatten_cons, pairCombos_append_left, ih,
      List.map_cons, List.sum_cons]

section Soundness
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (A : VertexOperatorAlgebra V) (U : VirUnitaryForm A) (q : V)
  (c h : ℚ) (hc : A.centralCharge = (c : ℂ))
  (hzero : A.L 0 q = (h : ℂ) • q)
  (hpos : ∀ m : ℤ, 0 < m → A.L m q = 0)

include hzero hpos in
theorem seedPair_sound (ls : List ℕ) :
    U.form q (virDesc A ls q) = (seedPair h ls : ℂ) * U.form q q := by
  induction ls with
  | nil => simp [virDesc, seedPair]
  | cons k ks ih =>
    rw [virDesc, ← U.adjoint]
    by_cases hk : k = 0
    · subst k
      rw [Nat.cast_zero, hzero, map_smul, LinearMap.smul_apply, ih]
      simp [seedPair, Rat.cast_mul, smul_eq_mul, mul_assoc]
    · rw [hpos k (by exact_mod_cast Nat.pos_of_ne_zero hk), map_zero,
        LinearMap.zero_apply]
      simp [seedPair, hk]

theorem form_combo_right (y : V) (ds : List (ℚ × List ℕ)) :
    U.form y (virCombo A q ds) =
      (ds.map fun t => (t.1 : ℂ) * U.form y (virDesc A t.2 q)).sum := by
  induction ds with
  | nil => simp [virCombo]
  | cons t ds ih =>
    rw [show virCombo A q (t :: ds) = (t.1 : ℂ) • virDesc A t.2 q + virCombo A q ds from rfl,
      map_add, LinearMap.map_smulₛₗ, map_ratCast, ih]
    rfl

include hc hzero hpos in
theorem pairWords_sound (ks ls : List ℕ) :
    U.form (virDesc A ks q) (virDesc A ls q) =
      (pairWords c h ks ls : ℂ) * U.form q q := by
  induction ks generalizing ls with
  | nil => exact seedPair_sound A U q h hzero hpos ls
  | cons k ks ih =>
    rw [virDesc, U.adjoint]
    simp only [neg_neg]
    rw [← virWordAction_sound A q c h hc hzero hpos,
      ← virCombo_collect, form_combo_right]
    simp only [ih, pairWords, Rat.cast_list_sum, List.map_map, Function.comp_def,
      Rat.cast_mul, ← mul_assoc, List.sum_map_mul_right]

include hc hzero hpos in
theorem pairCombos_sound (cs ds : List (ℚ × List ℕ)) :
    U.form (virCombo A q cs) (virCombo A q ds) =
      (pairCombos c h cs ds : ℂ) * U.form q q := by
  induction cs with
  | nil => simp [virCombo, pairCombos]
  | cons s cs ih =>
    rw [show virCombo A q (s :: cs) = (s.1 : ℂ) • virDesc A s.2 q + virCombo A q cs from rfl,
      map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, ih, form_combo_right]
    simp only [pairWords_sound A U q c h hc hzero hpos, pairCombos, List.map_cons,
      List.sum_cons, Rat.cast_add, Rat.cast_list_sum, List.map_map, Function.comp_def,
      Rat.cast_mul, smul_eq_mul, add_mul, ← mul_assoc, List.sum_map_mul_right]
    simp only [mul_assoc, List.sum_map_mul_left]

include hc hzero hpos in
theorem form_tower_pairWords (r : ℕ) :
    U.form (((A.L (-2)) ^ r) q) (((A.L (-2)) ^ r) q) =
      (pairWords c h (List.replicate r 2) (List.replicate r 2) : ℂ) * U.form q q := by
  simpa only [virDesc_replicate, Nat.cast_ofNat] using
    pairWords_sound A U q c h hc hzero hpos (List.replicate r 2) (List.replicate r 2)

include hc hzero hpos in
theorem virComboAction_sound (m : ℤ) (cs : List (ℚ × List ℕ)) :
    virCombo A q (virComboAction c h m cs) = A.L m (virCombo A q cs) := by
  induction cs with
  | nil => simp [virComboAction, virCombo]
  | cons t cs ih =>
    rw [virComboAction, List.flatMap_cons, virCombo_append, virCombo_scale,
      virWordAction_sound A q c h hc hzero hpos]
    change _ + virCombo A q (virComboAction c h m cs) = _
    rw [ih]
    simp [virCombo, map_add, map_smul]

include U hc hzero hpos in
/-- A rational zero norm is a genuine state equality in any positive realization. -/
theorem virCombo_eq_zero_of_pair (cs : List (ℚ × List ℕ))
    (hz : pairCombos c h cs cs = 0) : virCombo A q cs = 0 := by
  apply U.self_eq_zero
  rw [pairCombos_sound A U q c h hc hzero hpos, hz, Rat.cast_zero, zero_mul]

include U hc hzero hpos in
/-- This certificate tolerates null descendants at the resonant weights. -/
theorem mode_combo_eq_zero_of_pair (m : ℤ) (cs : List (ℚ × List ℕ))
    (hz : pairCombos c h (virComboAction c h m cs) (virComboAction c h m cs) = 0) :
    A.L m (virCombo A q cs) = 0 := by
  rw [← virComboAction_sound A q c h hc hzero hpos]
  exact virCombo_eq_zero_of_pair A U q c h hc hzero hpos _ hz

end Soundness
end VOA.Classification.COne.OrbIcoU
