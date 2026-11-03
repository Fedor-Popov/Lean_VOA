import VOA.Classification.COne.OrbOctaRCEval

/-! Shared-descendant exponential certificates at charge square two. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e OrbC2g OrbC2h

def reduceTwo (P : RawPoly ℕ) : RawPoly ℕ :=
  fastNormFuel ((fastNormFuel P).flatMap fun t => scaleR t.1 (reduceWordR 2 t.2))

theorem evRc_reduceTwo_of_sq {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) (P : RawPoly ℕ) :
    evRc a c (reduceTwo P) =
      evRc a c P := by
  rw [reduceTwo, evRc_fastNormFuel, evRc_flatMap]
  have h : ∀ Q : RawPoly ℕ,
      (Q.map fun t => evRc a c
        (scaleR t.1 (reduceWordR 2 t.2))).sum =
        evRc a c Q := by
    intro Q
    induction Q with
    | nil => simp [evRc_nil]
    | cons t Q ih =>
      rcases t with ⟨q,w⟩
      rw [List.map_cons, List.sum_cons, evRc_scaleR,
        evRc_reduceWordR _ _ _ hc, ih, evRc_cons]
  rw [h, evRc_fastNormFuel]


def expTwo : List ℕ → ℤ → RawPoly ℕ
  | [], s => if 0 ≤ s then reduceTwo (schurMemo s.toNat) else []
  | 0 :: w, s => prependC 0 (expTwo w s)
  | (i+1) :: w, s => reduceTwo (prependC (i+1) (expTwo w s) ++
      scaleR (-1) (prependC 0 (expTwo w (s + i + 1))))

theorem expTwo_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) (w : List ℕ) (s : ℤ) :
    evRc a c (expTwo w s) = evRc a c (expWordR w s) := by
  induction w generalizing s with
  | nil =>
    simp only [expTwo, expWordR]
    split_ifs <;> simp only [evRc_reduceTwo_of_sq _ _ hc, schurMemo_sound]
  | cons i w ih =>
    cases i <;> simp only [expTwo, expWordR, evRc_normR,
      evRc_reduceTwo_of_sq _ _ hc, evRc_append, evRc_scaleR, evRc_prependC, ih]

/-- One recurrence step using already certified child polynomials. -/
theorem expTwo_step {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) (i : ℕ) (w : List ℕ) (s : ℤ)
    (P Q : RawPoly ℕ)
    (hP : evRc a c P = evRc a c (expWordR w s))
    (hQ : evRc a c Q = evRc a c (expWordR w (s + i + 1))) :
    evRc a c (reduceTwo (prependC (i+1) P ++ scaleR (-1) (prependC 0 Q))) =
      evRc a c (expWordR ((i + 1) :: w) s) := by
  simp only [expWordR, evRc_normR, evRc_reduceTwo_of_sq _ _ hc,
    evRc_append, evRc_scaleR, evRc_prependC, hP, hQ]

theorem charge_square_two : PlusC2.cα 1 * PlusC2.cα 1 = ((2 : ℚ) : ℂ) := by
  convert PlusC2.cα_sq 1 le_rfl using 1
  norm_num

end VOA.Classification.COne.OrbOctaRC
