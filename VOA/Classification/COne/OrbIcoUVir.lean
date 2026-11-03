import VOA.Classification.COne.OrbOctaRCWard

/-! Rational Virasoro word computations, without oscillator coordinates.
The evaluator retains the order of negative modes. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbIcoU
open VOA VertexOperatorAlgebra OrbOctaRC

def wordScale (a : ℚ) (cs : List (ℚ × List ℕ)) : List (ℚ × List ℕ) :=
  cs.map fun t => (a * t.1, t.2)

def wordPrefix (k : ℕ) (cs : List (ℚ × List ℕ)) : List (ℚ × List ℕ) :=
  cs.map fun t => (t.1, k :: t.2)

/-- Combine equal ordered words; no commutation of modes is performed. -/
def wordInsert (a : ℚ) (ks : List ℕ) : List (ℚ × List ℕ) → List (ℚ × List ℕ)
  | [] => [(a, ks)]
  | (b, ls) :: cs => if ks = ls then (a + b, ls) :: cs else
      (b, ls) :: wordInsert a ks cs

def wordCollect : List (ℚ × List ℕ) → List (ℚ × List ℕ)
  | [] => []
  | (a, ks) :: cs => wordInsert a ks (wordCollect cs)

/-- One Virasoro mode acting on a negative word with charge `c` and seed weight `h`. -/
def virWordAction (c h : ℚ) (m : ℤ) : List ℕ → List (ℚ × List ℕ)
  | [] => if m < 0 then [(1, [(-m).toNat])] else
      if m = 0 then [(h, [])] else []
  | k :: ks => if m < 0 then [(1, (-m).toNat :: k :: ks)] else
      wordPrefix k (virWordAction c h m ks) ++
      wordScale ((m : ℚ) + k) (virWordAction c h (m - k) ks) ++
      if m - k = 0 then [((((m : ℚ)^3 - m) / 12 * c), ks)] else []

section Soundness
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (A : VertexOperatorAlgebra V) (q : V)

theorem virCombo_insert (a : ℚ) (ks : List ℕ) (cs : List (ℚ × List ℕ)) :
    virCombo A q (wordInsert a ks cs) =
      (a : ℂ) • virDesc A ks q + virCombo A q cs := by
  induction cs with
  | nil => simp [wordInsert, virCombo]
  | cons t cs ih =>
    rcases t with ⟨b, ls⟩
    by_cases he : ks = ls
    · subst ls
      simp [wordInsert, virCombo, Rat.cast_add, add_smul, add_assoc]
    · simp only [wordInsert, if_neg he]
      change (b : ℂ) • virDesc A ls q + virCombo A q (wordInsert a ks cs) = _
      rw [ih]
      simp only [virCombo, List.map_cons, List.sum_cons]
      abel

theorem virCombo_collect (cs : List (ℚ × List ℕ)) :
    virCombo A q (wordCollect cs) = virCombo A q cs := by
  induction cs with
  | nil => rfl
  | cons t cs ih =>
    rcases t with ⟨a, ks⟩
    rw [wordCollect, virCombo_insert, ih]
    rfl

theorem virCombo_scale (a : ℚ) (cs : List (ℚ × List ℕ)) :
    virCombo A q (wordScale a cs) = (a : ℂ) • virCombo A q cs := by
  induction cs with
  | nil => simp [wordScale, virCombo]
  | cons t cs ih =>
    simpa [wordScale, virCombo, List.map_cons, List.sum_cons,
      Rat.cast_mul, smul_add, mul_smul] using congrArg
        (fun v => ((a * t.1 : ℚ) : ℂ) • virDesc A t.2 q + v) ih

theorem virCombo_prefix (k : ℕ) (cs : List (ℚ × List ℕ)) :
    virCombo A q (wordPrefix k cs) = A.L (-(k : ℤ)) (virCombo A q cs) := by
  induction cs with
  | nil => simp [wordPrefix, virCombo]
  | cons t cs ih =>
    simpa [wordPrefix, virCombo, virDesc, List.map_cons, List.sum_cons,
      map_add, map_smul] using congrArg
        (fun v => (t.1 : ℂ) • A.L (-(k : ℤ)) (virDesc A t.2 q) + v) ih

theorem L_commute_negative (m : ℤ) (k : ℕ) (v : V) :
    A.L m (A.L (-(k : ℤ)) v) =
      A.L (-(k : ℤ)) (A.L m v) + ((m : ℂ) + k) • A.L (m - k) v +
      (if m - k = 0 then (((m : ℂ)^3 - m) / 12 * A.centralCharge) • v else 0) := by
  have h := DFunLike.congr_fun (A.L_virasoro m (-(k : ℤ))) v
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, Int.cast_neg, Int.cast_natCast,
    sub_neg_eq_add, ← sub_eq_add_neg] at h
  split_ifs at h ⊢ <;> simp_all only [LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.zero_apply] <;> linear_combination (norm := module) h

set_option maxHeartbeats 800000 in
-- Allow the rational casts and mode commutator to normalize together.
/-- Every rational word-action certificate evaluates in the actual VOA. -/
theorem virWordAction_sound (c h : ℚ) (hc : A.centralCharge = (c : ℂ))
    (hzero : A.L 0 q = (h : ℂ) • q)
    (hpos : ∀ m : ℤ, 0 < m → A.L m q = 0) (m : ℤ) (ks : List ℕ) :
    virCombo A q (virWordAction c h m ks) = A.L m (virDesc A ks q) := by
  induction ks generalizing m with
  | nil =>
    by_cases hm : m < 0
    · simp [virWordAction, hm, virCombo, virDesc, Int.toNat_of_nonneg (by omega : 0 ≤ -m)]
    · by_cases hz : m = 0
      · subst m; simpa [virWordAction, virCombo, virDesc] using hzero.symm
      · simp [virWordAction, hm, hz, virCombo, virDesc, hpos m (by omega)]
  | cons k ks ih =>
    by_cases hm : m < 0
    · simp [virWordAction, hm, virCombo, virDesc, Int.toNat_of_nonneg (by omega : 0 ≤ -m)]
    · rw [virWordAction, if_neg hm, virCombo_append, virCombo_append,
        virCombo_prefix, virCombo_scale, ih, ih, virDesc, L_commute_negative, hc]
      by_cases hz : m - k = 0 <;>
        simp [hz, virCombo, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_pow,
          Rat.cast_intCast, Rat.cast_add, Rat.cast_natCast]

end Soundness
end VOA.Classification.COne.OrbIcoU
