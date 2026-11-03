import VOA.Classification.COne.OrbC2hMergeFuel

/-! Normalizing intermediate oscillator polynomials, with the original semantics. -/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e OrbC2g

/-- Fixed structural fuel avoids re-evaluating lengths of intermediate lists. -/
def mergeManyFuel : ℕ → List (RawPoly ℕ) → RawPoly ℕ
  | 0, S => S.flatten
  | _+1, [] => []
  | _+1, [P] => P
  | n+1, P::Q::S => mergeManyFuel n (mergePairsFuel 100000 (P::Q::S))

theorem evRc_mergeManyFuel {r : ℕ} (a : Fin r) (c : ℂ) (n : ℕ)
    (S : List (RawPoly ℕ)) :
    evRc a c (mergeManyFuel n S) = (S.map (evRc a c)).sum := by
  induction n generalizing S with
  | zero => exact evRc_flatten a c S
  | succ n ih =>
    cases S with
    | nil => simp [mergeManyFuel, evRc_nil]
    | cons P S =>
      cases S with
      | nil => simp [mergeManyFuel]
      | cons Q S => rw [mergeManyFuel, ih, evRc_mergePairsFuel]

def fastNormFuel (P : RawPoly ℕ) : RawPoly ℕ :=
  mergeManyFuel 100000 (P.map fun t => if t.1 = 0 then [] else [(t.1, sortWord t.2)])

theorem evRc_fastNormFuel {r : ℕ} (a : Fin r) (c : ℂ) (P : RawPoly ℕ) :
    evRc a c (fastNormFuel P) = evRc a c P := by
  rw [fastNormFuel, evRc_mergeManyFuel, List.map_map]
  induction P with
  | nil => simp [evRc_nil]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    simp only [List.map_cons, List.sum_cons, evRc_cons]
    rw [ih]
    by_cases hq : q = 0
    · simp [hq, evRc_nil]
    · simp [hq, evRc_cons, evRc_nil, evalWord_sortWord]

/-- Charge reduction using the certified structural merge normalizer. -/
def fastReduce (P : RawPoly ℕ) : RawPoly ℕ :=
  fastNormFuel ((fastNormFuel P).flatMap fun t => scaleR t.1 (reduceWordR 8 t.2))

theorem evRc_fastReduce (P : RawPoly ℕ) :
    evRc (LatMod.a0 4) (PlusC2.cα 4) (fastReduce P) =
      evRc (LatMod.a0 4) (PlusC2.cα 4) P := by
  have hc : PlusC2.cα 4 * PlusC2.cα 4 = ((8:ℚ):ℂ) := by
    convert PlusC2.cα_sq 4 OrbC2e.four_ge_one using 1
    norm_num
  rw [fastReduce, evRc_fastNormFuel, evRc_flatMap]
  have h : ∀ Q : RawPoly ℕ,
      (Q.map fun t => evRc (LatMod.a0 4) (PlusC2.cα 4)
        (scaleR t.1 (reduceWordR 8 t.2))).sum =
        evRc (LatMod.a0 4) (PlusC2.cα 4) Q := by
    intro Q
    induction Q with
    | nil => simp [evRc_nil]
    | cons t Q ih =>
      rcases t with ⟨q,w⟩
      rw [List.map_cons, List.sum_cons, evRc_scaleR,
        evRc_reduceWordR _ _ _ hc, ih, evRc_cons]
  rw [h, evRc_fastNormFuel]

theorem evRc_fastReduce_of_sq {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (P : RawPoly ℕ) :
    evRc a c (fastReduce P) =
      evRc a c P := by
  rw [fastReduce, evRc_fastNormFuel, evRc_flatMap]
  have h : ∀ Q : RawPoly ℕ,
      (Q.map fun t => evRc a c
        (scaleR t.1 (reduceWordR 8 t.2))).sum =
        evRc a c Q := by
    intro Q
    induction Q with
    | nil => simp [evRc_nil]
    | cons t Q ih =>
      rcases t with ⟨q,w⟩
      rw [List.map_cons, List.sum_cons, evRc_scaleR,
        evRc_reduceWordR _ _ _ hc, ih, evRc_cons]
  rw [h, evRc_fastNormFuel]

def wordQuick : List ℕ → ℤ → ℕ → RawPoly ℕ → RawPoly ℕ
  | [], s, _, P => if s = 0 then P else []
  | i :: is, s, w, P => if P = [] then [] else
    fastNormFuel ((intRange (-((i+1+w : ℕ) : ℤ))
      ((max (-1) (((wWt is+w : ℕ) : ℤ)+s))+((i+1+w : ℕ) : ℤ)+1).toNat).flatMap
      fun m => if 0 ≤ m then fastNormFuel (fActC i m (wordQuick is (s-m) w P))
        else wordQuick is (s-m) ((((i+1+w : ℕ) : ℤ)+m).toNat) (fastNormFuel (fActC i m P)))

theorem evRc_wordQuick {r : ℕ} (a : Fin r) (c : ℂ)
    (is : List ℕ) (s : ℤ) (w : ℕ) (P Q : RawPoly ℕ)
    (h : evRc a c P = evRc a c Q) :
    evRc a c (wordQuick is s w P) = evRc a c (wordActC is s w Q) := by
  induction is generalizing s w P Q with
  | nil =>
    simp only [wordQuick, wordActC]
    split_ifs
    · exact h
    · rfl
  | cons i is ih =>
    rw [wordQuick]
    split_ifs with hp
    · have hz : evRc a c Q = 0 := by rw [← h, hp, evRc_nil]
      rw [evRc_nil, evRc_wordActC a c _ _ _ Q (hz ▸ Submodule.zero_mem _), hz, map_zero]
    · rw [evRc_fastNormFuel, wordActC, evRc_flatMap, evRc_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro m hm
      split_ifs with hm0
      · rw [evRc_fastNormFuel, evRc_fActC, evRc_fActC, ih _ _ P Q h]
      · apply ih
        rw [evRc_fastNormFuel, evRc_fActC, evRc_fActC, h]

def polyQuick (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  fastNormFuel (P.flatMap fun t => Q.flatMap fun u =>
    scaleR u.1 (wordQuick u.2 s (wWtC t.2) [t]))

theorem evRc_polyQuick {r : ℕ} (a : Fin r) (c : ℂ)
    (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) :
    evRc a c (polyQuick Q s P) = evRc a c (polyActWC Q s P) := by
  rw [polyQuick, evRc_fastNormFuel, polyActWC, evRc_flatMap, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [polyActC, evRc_flatMap, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  rw [evRc_scaleR, evRc_scaleR, evRc_wordQuick a c _ _ _ _ _ rfl]

def neutralQuick (Q : RawPoly ℕ) (n d : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  fastReduce (onOscillators
    (fun R => chargeScale d (polyQuick Q (-n-1) (liftR R))) P)

theorem neutralQuick_sound (Q P : RawPoly ℕ) (n d : ℤ) :
    evRc (LatMod.a0 4) (PlusC2.cα 4) (neutralQuick Q n d P) =
      evRc (LatMod.a0 4) (PlusC2.cα 4) (neutralAction Q n d P) := by
  rw [neutralQuick, neutralAction, evRc_fastReduce, evRc_reduce_eight]
  simp only [onOscillators, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [evRc_scaleR, evRc_scaleR, evRc_chargePower, evRc_chargePower,
    evRc_chargeScale, evRc_chargeScale, evRc_polyQuick]

end VOA.Classification.COne.OrbC2h
