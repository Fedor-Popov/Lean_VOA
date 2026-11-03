import VOA.Classification.COne.PlusSplitGenerators

/-!
# Separation of the rank-one plus top-character table

The table is Dong--Nagatomo, arXiv:math/9807168, Section 5.1, expressed
using the library's quadratic generator W rather than the primary J.
The change of coordinates is J = 4 h² + (4/5) h - (9/10) W.
This file proves numerical separation; existence of characters with these
values is a separate input, not a consequence of numerical separation.
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.PlusCharacterTable

/-- Charged sectors r=1,...,m-1, followed by vacuum, sign, half-lattice ±,
and the four twisted sectors T1+, T1-, T2+, T2-. -/
abbrev Label (m : ℕ) := Fin (m - 1) ⊕ Fin 8

/-- Values of (omega, W, E); `a` is the nonzero twisted E normalization. -/
noncomputable def exceptional (m : ℕ) (a : ℝ) : Fin 8 → ℝ × ℝ × ℝ :=
  ![(0, 0, 0), (1, 12, 0), ((m : ℝ)/4, (m : ℝ)/2, 1),
    ((m : ℝ)/4, (m : ℝ)/2, -1), (1/16, 3/64, a),
    (9/16, 147/64, -a*(4*m-1)), (1/16, 3/64, -a),
    (9/16, 147/64, a*(4*m-1))]

noncomputable def values (m : ℕ) (a : ℝ) : Label m → ℝ × ℝ × ℝ
  | .inl r => let h := ((r.val : ℝ) + 1)^2 / (4*m); (h, 2*h, 0)
  | .inr i => exceptional m a i

theorem card_label (m : ℕ) (hm : 1 ≤ m) : Fintype.card (Label m) = m + 7 := by
  simp only [Label, Fintype.card_sum, Fintype.card_fin]
  omega

theorem exceptional_injective (m : ℕ) (hm : 2 ≤ m) (a : ℝ) (ha : a ≠ 0) :
    Function.Injective (exceptional m a) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  intro i j hij
  have h := congrArg Prod.fst hij
  have w := congrArg (fun x => x.2.1) hij
  have e := congrArg (fun x => x.2.2) hij
  fin_cases i <;> fin_cases j <;>
    norm_num [exceptional] at h <;> norm_num [exceptional] at w <;>
    norm_num [exceptional] at e
  all_goals first | rfl | nlinarith | (exfalso; apply ha; nlinarith)

theorem values_injective (m : ℕ) (hm : 2 ≤ m) (a : ℝ) (ha : a ≠ 0) :
    Function.Injective (values m a) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  intro i j hij
  rcases i with r | i <;> rcases j with s | j
  · have hh := congrArg Prod.fst hij
    simp only [values] at hh
    have hsquare := (div_left_inj' (show (4 : ℝ)*m ≠ 0 by positivity)).mp hh
    have hr : (0 : ℝ) ≤ r.val := Nat.cast_nonneg _
    have hs : (0 : ℝ) ≤ s.val := Nat.cast_nonneg _
    have heq : (r.val : ℝ) = s.val := by nlinarith
    exact congrArg Sum.inl (Fin.ext (by exact_mod_cast heq))
  · have hr : (0 : ℝ) < ((r.val : ℝ)+1)^2/(4*m) := by positivity
    have h := congrArg Prod.fst hij
    have w := congrArg (fun x => x.2.1) hij
    have e := congrArg (fun x => x.2.2) hij
    fin_cases j <;> norm_num [values, exceptional] at h w e <;>
      (first | nlinarith | (rcases h with h | h <;> nlinarith))
  · have hs : (0 : ℝ) < ((s.val : ℝ)+1)^2/(4*m) := by positivity
    have h := congrArg Prod.fst hij
    have w := congrArg (fun x => x.2.1) hij
    have e := congrArg (fun x => x.2.2) hij
    fin_cases i <;> norm_num [values, exceptional] at h w e <;>
      nlinarith
  · exact congrArg Sum.inr (exceptional_injective m hm a ha hij)

/-- The E eigenvalue on T1+. -/
noncomputable def twistedScale (m : ℕ) : ℝ := 2 / (2 : ℝ)^(2*m)

theorem twistedScale_ne_zero (m : ℕ) : twistedScale m ≠ 0 := by
  unfold twistedScale
  positivity

/-- Change the library's W coordinate to Dong--Nagatomo's J coordinate. -/
noncomputable def primary (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (v.1, 4*v.1^2 + (4/5)*v.1 - (9/10)*v.2.1, v.2.2)

theorem primary_injective : Function.Injective primary := by
  rintro ⟨h, w, e⟩ ⟨h', w', e'⟩ heq
  have hh := congrArg Prod.fst heq
  have hw := congrArg (fun x => x.2.1) heq
  have he := congrArg (fun x => x.2.2) heq
  dsimp [primary] at hh hw he
  have hww : w = w' := by rw [hh] at hw; linarith
  exact Prod.ext hh (Prod.ext hww he)

theorem primary_values_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (primary ∘ values m (twistedScale m)) :=
  primary_injective.comp (values_injective m hm _ (twistedScale_ne_zero m))

/-- Explicit primary-J values, including the sign weight 1 and both twisted pairs. -/
theorem primary_exceptional (m : ℕ) (a : ℝ) (i : Fin 8) :
    primary (exceptional m a i) =
      (![(0, 0, 0), (1, -6, 0), ((m : ℝ)/4, ((m : ℝ)^2-m)/4, 1),
        ((m : ℝ)/4, ((m : ℝ)^2-m)/4, -1), (1/16, 3/128, a),
        (9/16, -45/128, -a*(4*m-1)), (1/16, 3/128, -a),
        (9/16, -45/128, a*(4*m-1))] : Fin 8 → ℝ × ℝ × ℝ) i := by
  fin_cases i <;> norm_num [primary, exceptional, Prod.mk.injEq] <;> ring

end VOA.Classification.COne.PlusCharacterTable
