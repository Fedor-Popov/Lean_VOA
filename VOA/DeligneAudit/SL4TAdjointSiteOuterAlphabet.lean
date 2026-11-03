import VOA.DeligneAudit.SL4TAdjointSiteRingKernel

/-!
# The outer alphabet current on the second Levi quotient

The first Levi quotient `V ⧸ M_{>d}` carries the eight currents of the rank-two Levi `sl₃` and,
in addition, the three radical alphabet currents. The alphabet current of the outer radical
alphabet `x₁` is `E₁₁ - ¼` in the `0`-based matrix units of `A3Sector.bracketTable`. On the
Levi colours it has the weights

    E₁₂ : 1,  E₂₃ : 0,  E₁₃ : 1,  g = E₂₁ : -1,  F = E₃₂ : 0,  q = E₃₁ : -1,

and it commutes with both Levi Cartan currents. Hence it commutes with the whole final `gl₂`
(the colours `E₂₃`, `E₃₂` and the Cartan currents), and it shifts every `g`- and every
`q`-letter with weight `-1`. On the first Levi multiplicity it is multiplication by the
Grassmannian power sum `p_s(x₁)`.

Consequences proved here, for every block of the second Levi filtration:
* the mode-evaluation formula `radicalAlphabetQuotCurrent_outer_secondLeviModeEvaluation`;
* the outer current preserves every second Levi count layer and every higher second Levi
  closure (`higherSecondLeviCountClosure_outerAlphabet`), so it descends to the second Levi
  quotient.
-/

namespace VOA.DeligneAudit.SL4T

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

noncomputable section

/-! ### Weights of the Cartan colours on the Levi colours -/

/-- The three Cartan colours `E₀₀ - E₁₁`, `E₁₁ - E₂₂`, `E₂₂ - E₃₃`. -/
def cartanColourOf : Fin 3 → Fin 15
  | 0 => 12
  | 1 => 13
  | 2 => 14

/-- The weight of a Cartan colour on a Levi colour (in the order of `a3LeviColour`). -/
def cartanLeviWeight : Fin 3 → Fin 8 → ℤ
  | 0, 0 => -1 | 0, 1 => 0 | 0, 2 => -1 | 0, 3 => 1 | 0, 4 => 0 | 0, 5 => 1
  | 1, 0 => 2 | 1, 1 => -1 | 1, 2 => 1 | 1, 3 => -2 | 1, 4 => 1 | 1, 5 => -1
  | 2, 0 => -1 | 2, 1 => 2 | 2, 2 => 1 | 2, 3 => 1 | 2, 4 => -2 | 2, 5 => -1
  | _, _ => 0

/-- Every Cartan colour brackets a Levi colour to a multiple of itself. -/
theorem cartan_levi_bracket (i : Fin 3) (j : Fin 8) (e : Fin 15) :
    bracketInt (cartanColourOf i) (a3LeviColour j) e =
      if e = a3LeviColour j then cartanLeviWeight i j else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases e <;> decide

/-- The weight of the outer alphabet current `E₁₁ - ¼` on the Levi colours. -/
def outerAlphabetLeviWeight : Fin 8 → ℤ
  | 0 => 1 | 1 => 0 | 2 => 1 | 3 => -1 | 4 => 0 | 5 => -1 | 6 => 0 | 7 => 0

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- Commutation of a Cartan current with a Levi current. -/
theorem cartan_levi_comm (i : Fin 3) (j : Fin 8) (r s : ℕ) (v : V) :
    ρ.op (cartanColourOf i) r (ρ.op (a3LeviColour j) s v) =
      ρ.op (a3LeviColour j) s (ρ.op (cartanColourOf i) r v) +
        (cartanLeviWeight i j : ℂ) • ρ.op (a3LeviColour j) (r + s) v :=
  op_comm_of_single_bracket ρ (cartan_levi_bracket i j) r s v

/-- The outer alphabet current shifts each Levi current with its weight. -/
theorem radicalAlphabetCurrent_outer_levi_comm (j : Fin 8) (r s : ℕ) (v : V) :
    radicalAlphabetCurrent ρ 0 r (ρ.op (a3LeviColour j) s v) =
      ρ.op (a3LeviColour j) s (radicalAlphabetCurrent ρ 0 r v) +
        (outerAlphabetLeviWeight j : ℂ) • ρ.op (a3LeviColour j) (r + s) v := by
  have h₀ := cartan_levi_comm ρ 0 j r s v
  have h₁ := cartan_levi_comm ρ 1 j r s v
  have h₂ := cartan_levi_comm ρ 2 j r s v
  simp only [cartanColourOf] at h₀ h₁ h₂
  simp only [radicalAlphabetCurrent, show (0 : Fin 3) ≠ 2 by decide, if_false,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.neg_apply, map_smul, map_add,
    map_neg]
  rw [h₀, h₁, h₂]
  fin_cases j <;> simp [cartanLeviWeight, outerAlphabetLeviWeight] <;> module

variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))

/-- On the first Levi quotient, the outer alphabet current shifts each Levi current with its
weight. -/
theorem radicalAlphabetQuotCurrent_outer_levi_comm (d : Fin 3 → ℕ) (j : Fin 8) (r s : ℕ)
    (x : V ⧸ higherRadicalCountClosure ρ w d) :
    radicalAlphabetQuotCurrent ρ w a b c h d 0 r ((radicalCountQuotCurrent ρ w d).op j s x) =
      (radicalCountQuotCurrent ρ w d).op j s (radicalAlphabetQuotCurrent ρ w a b c h d 0 r x) +
        (outerAlphabetLeviWeight j : ℂ) • (radicalCountQuotCurrent ρ w d).op j (r + s) x := by
  obtain ⟨v, rfl⟩ := (higherRadicalCountClosure ρ w d).mkQ_surjective x
  change (higherRadicalCountClosure ρ w d).mkQ
      (radicalAlphabetCurrent ρ 0 r (ρ.op (a3LeviColour j) s v)) =
    (higherRadicalCountClosure ρ w d).mkQ
        (ρ.op (a3LeviColour j) s (radicalAlphabetCurrent ρ 0 r v)) +
      (outerAlphabetLeviWeight j : ℂ) •
        (higherRadicalCountClosure ρ w d).mkQ (ρ.op (a3LeviColour j) (r + s) v)
  rw [radicalAlphabetCurrent_outer_levi_comm, map_add, map_smul]

/-- The outer alphabet current commutes with every current of the final `gl₂`. -/
theorem radicalAlphabetQuotCurrent_outer_commute_finalLevi (d : Fin 3 → ℕ) (j : Fin 8)
    (hj : a2Levi j) (r s : ℕ) :
    Commute (radicalAlphabetQuotCurrent ρ w a b c h d 0 r)
      ((radicalCountQuotCurrent ρ w d).op j s) := by
  apply LinearMap.ext
  intro x
  change radicalAlphabetQuotCurrent ρ w a b c h d 0 r
      ((radicalCountQuotCurrent ρ w d).op j s x) =
    (radicalCountQuotCurrent ρ w d).op j s (radicalAlphabetQuotCurrent ρ w a b c h d 0 r x)
  rw [radicalAlphabetQuotCurrent_outer_levi_comm]
  have hw : outerAlphabetLeviWeight j = 0 := by
    rcases hj with rfl | rfl | rfl | rfl <;> rfl
  rw [hw, Int.cast_zero, zero_smul, add_zero]

/-- On the first Levi multiplicity, the outer alphabet current is multiplication by the outer
Grassmannian power sum. -/
theorem radicalAlphabetQuotCurrent_outer_ambient (d : Fin 3 → ℕ) (s : ℕ) (hs : 0 < s)
    (φ : RadicalGrassmannianRing a b c d) :
    radicalAlphabetQuotCurrent ρ w a b c h d 0 s
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d φ) =
      radicalGrassmannianAmbientEvaluation ρ w a b c h d
        (radicalGrassmannianPowerSum a b c d 0 s * φ) :=
  radicalGrassmannianEvaluation_powerSum ρ w a b c h d 0 s hs φ

/-- The weight `-1` on both second Levi lowering alphabets. -/
theorem secondLeviPositionOperator_outerAlphabet (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) (s n : ℕ)
    (j : SecondLeviModeSlot e₁ e₂) :
    radicalAlphabetQuotCurrent ρ w a b c h d 0 s *
        secondLeviPositionOperator (radicalCountQuotCurrent ρ w d) e₁ e₂ j n -
      secondLeviPositionOperator (radicalCountQuotCurrent ρ w d) e₁ e₂ j n *
        radicalAlphabetQuotCurrent ρ w a b c h d 0 s =
      (-1 : ℂ) • secondLeviPositionOperator (radicalCountQuotCurrent ρ w d) e₁ e₂ j (s + n) := by
  apply LinearMap.ext
  intro x
  rcases j with j | j
  · change radicalAlphabetQuotCurrent ρ w a b c h d 0 s
        ((radicalCountQuotCurrent ρ w d).op 3 n x) -
      (radicalCountQuotCurrent ρ w d).op 3 n (radicalAlphabetQuotCurrent ρ w a b c h d 0 s x) =
        (-1 : ℂ) • (radicalCountQuotCurrent ρ w d).op 3 (s + n) x
    rw [radicalAlphabetQuotCurrent_outer_levi_comm]
    simp [outerAlphabetLeviWeight]
  · change radicalAlphabetQuotCurrent ρ w a b c h d 0 s
        ((radicalCountQuotCurrent ρ w d).op 5 n x) -
      (radicalCountQuotCurrent ρ w d).op 5 n (radicalAlphabetQuotCurrent ρ w a b c h d 0 s x) =
        (-1 : ℂ) • (radicalCountQuotCurrent ρ w d).op 5 (s + n) x
    rw [radicalAlphabetQuotCurrent_outer_levi_comm]
    simp [outerAlphabetLeviWeight]

theorem secondLeviModePowerSum_outerAlphabet {B : Type} [CommRing B] [Algebra ℂ B]
    (e₁ e₂ s : ℕ) :
    positionModePowerSum (B := B) (secondLeviModePositions e₁ e₂) (fun _ => (-1 : ℂ)) s =
      -secondLeviModePowerSum e₁ e₂ 0 s - secondLeviModePowerSum e₁ e₂ 1 s := by
  simp [positionModePowerSum, secondLeviModePositions, secondLeviModePowerSum,
    List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    Finset.sum_neg_distrib, sub_eq_add_neg]

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient algebra is a tensor product of three Grassmannian quotient rings.
/-- **The outer alphabet current on second Levi words.** It shifts the base by `p_s(x₁)` and
every `g`- and `q`-letter with weight `-1`. -/
theorem radicalAlphabetQuotCurrent_outer_secondLeviModeEvaluation (d : Fin 3 → ℕ)
    (e₁ e₂ s : ℕ) (hs : 0 < s)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) (RadicalGrassmannianRing a b c d)) :
    radicalAlphabetQuotCurrent ρ w a b c h d 0 s
        (secondLeviModeEvaluation (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ P) =
      secondLeviModeEvaluation (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂
        ((MvPolynomial.C (radicalGrassmannianPowerSum a b c d 0 s) -
          secondLeviModePowerSum e₁ e₂ 0 s - secondLeviModePowerSum e₁ e₂ 1 s) * P) := by
  rw [secondLeviModeEvaluation, positionModeEvaluation_cartan
    _ _ (secondLeviModePositions_nodup e₁ e₂) _ _ (radicalGrassmannianPowerSum a b c d 0 s)
    (fun _ => (-1 : ℂ)) s
    (fun j n => secondLeviPositionOperator_outerAlphabet ρ w a b c h d e₁ e₂ s n j)
    (radicalAlphabetQuotCurrent_outer_ambient ρ w a b c h d s hs),
    secondLeviModePowerSum_outerAlphabet]
  congr 2
  ring

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient algebra is a tensor product of three Grassmannian quotient rings.
/-- The outer alphabet current preserves every second Levi count layer. -/
theorem secondLeviCountLayer_outerAlphabet (d : Fin 3 → ℕ) (u v s : ℕ) (hs : 0 < s) :
    secondLeviCountLayer (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) u v ≤
      (secondLeviCountLayer (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) u v).comap
          (radicalAlphabetQuotCurrent ρ w a b c h d 0 s) := by
  intro x hx
  rw [← secondLeviModeEvaluation_range] at hx ⊢
  obtain ⟨P, rfl⟩ := hx
  rw [Submodule.mem_comap, radicalAlphabetQuotCurrent_outer_secondLeviModeEvaluation
    ρ w a b c h d u v s hs P]
  exact ⟨_, rfl⟩

/-- An operator commuting with the final `gl₂` preserves the Levi closure of any subspace that
it preserves. -/
theorem a2LeviClosure_le_comap_of_commute {W : Type} [AddCommGroup W] [Module ℂ W]
    (Q : CurrentModule VOA.AffineSl3.bracketTable W) (T : Module.End ℂ W)
    (hT : ∀ j r, a2Levi j → Commute T (Q.op j r)) (S : Submodule ℂ W)
    (hS : S ≤ S.comap T) : a2LeviClosure Q S ≤ (a2LeviClosure Q S).comap T := by
  rw [a2LeviClosure, Submodule.span_le]
  rintro z ⟨l, v, hl, hv, rfl⟩
  change T (wordOp Q l v) ∈ a2LeviClosure Q S
  induction l with
  | nil => exact a2LeviClosure_contains Q S (hS hv)
  | cons x l ih =>
    rcases x with ⟨j, r⟩
    simp only [List.forall_cons] at hl
    change T (Q.op j r (wordOp Q l v)) ∈ a2LeviClosure Q S
    rw [← Module.End.mul_apply, (hT j r hl.1).eq, Module.End.mul_apply]
    exact a2LeviClosure_inv Q S j r hl.1 (ih hl.2)

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient algebra is a tensor product of three Grassmannian quotient rings.
/-- The outer alphabet current preserves every higher second Levi closure. -/
theorem higherSecondLeviCountClosure_outerAlphabet (d : Fin 3 → ℕ) (e₁ e₂ s : ℕ)
    (hs : 0 < s) :
    higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ ≤
      (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂).comap
          (radicalAlphabetQuotCurrent ρ w a b c h d 0 s) := by
  apply a2LeviClosure_le_comap_of_commute
  · intro j r hj
    exact radicalAlphabetQuotCurrent_outer_commute_finalLevi ρ w a b c h d j hj s r
  · apply iSup_le
    intro u
    apply iSup_le
    intro v
    apply iSup_le
    intro huv
    exact (secondLeviCountLayer_outerAlphabet ρ w a b c h d u v s hs).trans
      (Submodule.comap_mono (le_iSup_of_le u (le_iSup_of_le v (le_iSup_of_le huv le_rfl))))

end

end VOA.DeligneAudit.SL4T
