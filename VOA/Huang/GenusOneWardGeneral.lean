import VOA.Huang.GenusOneWardEval

/-!
# The two-point minus-two Ward identities for arbitrary states and insertions

The identities of `GenusOneWardNegTwo` and `GenusOneWardSwap` are additive in
the state and in both insertions; a common cutoff is obtained by taking
maxima. The state enters through Zhu's linear square modes `sqMode`.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.QEquation (TailBound exists_tailBound)
open VOA.Huang.GenusOne (sqAct)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

section General
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

/-- The left minus-two Ward expression. -/
def leftLHS (b : V) (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) : R2 :=
  Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod (-2) b x) y +
    ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
      (eis (m + 2) * Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod ((2 * m + 2 : ℕ) : ℤ) b x) y) +
    ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • piK (m + 1) - if m = 0 then eis 1 else 0) *
      Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) b y)

/-- The right minus-two Ward expression. -/
def rightLHS (b : V) (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) : R2 :=
  Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod (-2) b y) +
    ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
      (eis (m + 2) * Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod ((2 * m + 2 : ℕ) : ℤ) b y)) +
    ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
        if m = 0 then eis 1 else 0) *
      Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod (m : ℤ) b x) y

theorem leftLHS_add_state (b b' : V) (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) :
    leftLHS Y₁ Y₂ (b + b') x y K = leftLHS Y₁ Y₂ b x y K + leftLHS Y₁ Y₂ b' x y K := by
  simp only [leftLHS, map_add, LinearMap.add_apply, mul_add, smul_add, Finset.sum_add_distrib]
  abel

theorem leftLHS_add_left (b : V) (x x' : P₁.carrier) (y : P₂.carrier) (K : ℕ) :
    leftLHS Y₁ Y₂ b (x + x') y K = leftLHS Y₁ Y₂ b x y K + leftLHS Y₁ Y₂ b x' y K := by
  simp only [leftLHS, map_add, LinearMap.add_apply, mul_add, smul_add, Finset.sum_add_distrib]
  abel

theorem leftLHS_add_right (b : V) (x : P₁.carrier) (y y' : P₂.carrier) (K : ℕ) :
    leftLHS Y₁ Y₂ b x (y + y') K = leftLHS Y₁ Y₂ b x y K + leftLHS Y₁ Y₂ b x y' K := by
  simp only [leftLHS, map_add, LinearMap.add_apply, mul_add, smul_add, Finset.sum_add_distrib]
  abel

theorem rightLHS_add_state (b b' : V) (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) :
    rightLHS Y₁ Y₂ (b + b') x y K = rightLHS Y₁ Y₂ b x y K + rightLHS Y₁ Y₂ b' x y K := by
  simp only [rightLHS, map_add, LinearMap.add_apply, mul_add, smul_add, Finset.sum_add_distrib]
  abel

theorem rightLHS_add_left (b : V) (x x' : P₁.carrier) (y : P₂.carrier) (K : ℕ) :
    rightLHS Y₁ Y₂ b (x + x') y K = rightLHS Y₁ Y₂ b x y K + rightLHS Y₁ Y₂ b x' y K := by
  simp only [rightLHS, map_add, LinearMap.add_apply, mul_add, smul_add, Finset.sum_add_distrib]
  abel

theorem rightLHS_add_right (b : V) (x : P₁.carrier) (y y' : P₂.carrier) (K : ℕ) :
    rightLHS Y₁ Y₂ b x (y + y') K = rightLHS Y₁ Y₂ b x y K + rightLHS Y₁ Y₂ b x y' K := by
  simp only [rightLHS, map_add, LinearMap.add_apply, mul_add, smul_add, Finset.sum_add_distrib]
  abel

/-- An eventually-zero predicate closed under addition. -/
def EvZero (F : ℕ → R2) : Prop := ∃ K₀, ∀ K, K₀ ≤ K → F K = 0

theorem EvZero.add {F G : ℕ → R2} (hF : EvZero F) (hG : EvZero G) :
    EvZero fun K => F K + G K := by
  obtain ⟨A, hA⟩ := hF
  obtain ⟨B, hB⟩ := hG
  exact ⟨max A B, fun K hK => by
    show F K + G K = 0
    rw [hA K (le_trans (le_max_left _ _) hK), hB K (le_trans (le_max_right _ _) hK), add_zero]⟩

theorem evZero_of_eq_zero {F : ℕ → R2} (h : ∀ K, F K = 0) : EvZero F := ⟨0, fun K _ => h K⟩

theorem homog_state_cases {b : V} {i : ℤ} (hb : b ∈ W.grading i) :
    b = 0 ∨ ∃ kb : ℕ, i = kb := by
  by_cases hi : i < 0
  · left
    rw [W.positivity i hi, Submodule.mem_bot] at hb
    exact hb
  · right
    exact ⟨i.toNat, by omega⟩

theorem leftLHS_zero_state (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) :
    leftLHS Y₁ Y₂ 0 x y K = 0 := by
  simp [leftLHS]

theorem rightLHS_zero_state (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) :
    rightLHS Y₁ Y₂ 0 x y K = 0 := by
  simp [rightLHS]

theorem leftLHS_homog {b : V} {kb : ℕ} (hb : b ∈ W.grading (kb : ℤ)) {α₁ α₂ : ℂ}
    {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) :
    EvZero (leftLHS Y₁ Y₂ b x y) := by
  obtain ⟨T, hT⟩ := exists_tailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule b x y
  refine ⟨max 1 T, fun K hK => ?_⟩
  have h := ward_neg_two_phi Y₁ Y₂ hb hx hy K (le_trans (le_max_left _ _) hK)
    (tailBound_mono (le_trans (le_max_right _ _) hK) hT)
  simp only [leftLHS, GenusOne.SquareModule.sqMode_of_mem_grading _ hb, Int.toNat_natCast]
  exact h

theorem rightLHS_homog {b : V} {kb : ℕ} (hb : b ∈ W.grading (kb : ℤ)) {α₁ α₂ : ℂ}
    {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) :
    EvZero (rightLHS Y₁ Y₂ b x y) := by
  obtain ⟨T, hT⟩ := exists_tailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule b x y
  refine ⟨max 1 T, fun K hK => ?_⟩
  have h := ward_neg_two_phi_right Y₁ Y₂ hb hx hy K (le_trans (le_max_left _ _) hK)
    (tailBound_mono (le_trans (le_max_right _ _) hK) hT)
  simp only [rightLHS, GenusOne.SquareModule.sqMode_of_mem_grading _ hb, Int.toNat_natCast]
  exact h

/-- Induction over the grading of `V`. -/
theorem state_induction {C : V → Prop} (b : V) (zero : C 0)
    (homog : ∀ (i : ℤ) (b : V), b ∈ W.grading i → C b)
    (add : ∀ b b', C b → C b' → C (b + b')) : C b := by
  have hb : b ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  exact Submodule.iSup_induction W.grading (motive := C) hb homog zero add

/-- **Left minus-two identity, general form.** -/
theorem leftLHS_evZero (b : V) (x : P₁.carrier) (y : P₂.carrier) :
    EvZero (leftLHS Y₁ Y₂ b x y) := by
  induction b using state_induction (W := W) generalizing x y with
  | zero => exact evZero_of_eq_zero (leftLHS_zero_state Y₁ Y₂ x y)
  | homog i b hb =>
    rcases homog_state_cases hb with h0 | ⟨kb, rfl⟩
    · subst h0; exact evZero_of_eq_zero (leftLHS_zero_state Y₁ Y₂ x y)
    · refine FusionTop.induction_weight P₁.isMod x
        (evZero_of_eq_zero fun K => by simp [leftLHS]) (fun a a' ha ha' => ?_) ?_
      · rw [show leftLHS Y₁ Y₂ b (a + a') y = fun K => leftLHS Y₁ Y₂ b a y K + leftLHS Y₁ Y₂ b a' y K
          from funext fun K => leftLHS_add_left Y₁ Y₂ b a a' y K]
        exact ha.add ha'
      · intro α₁ x hx
        refine FusionTop.induction_weight P₂.isMod y
          (evZero_of_eq_zero fun K => by simp [leftLHS]) (fun a a' ha ha' => ?_) ?_
        · rw [show leftLHS Y₁ Y₂ b x (a + a') = fun K => leftLHS Y₁ Y₂ b x a K + leftLHS Y₁ Y₂ b x a' K
            from funext fun K => leftLHS_add_right Y₁ Y₂ b x a a' K]
          exact ha.add ha'
        · intro α₂ y hy
          exact leftLHS_homog Y₁ Y₂ hb hx hy
  | add b b' hb hb' =>
    rw [show leftLHS Y₁ Y₂ (b + b') x y = fun K => leftLHS Y₁ Y₂ b x y K + leftLHS Y₁ Y₂ b' x y K
      from funext fun K => leftLHS_add_state Y₁ Y₂ b b' x y K]
    exact (hb x y).add (hb' x y)

/-- **Right minus-two identity, general form.** -/
theorem rightLHS_evZero (b : V) (x : P₁.carrier) (y : P₂.carrier) :
    EvZero (rightLHS Y₁ Y₂ b x y) := by
  induction b using state_induction (W := W) generalizing x y with
  | zero => exact evZero_of_eq_zero (rightLHS_zero_state Y₁ Y₂ x y)
  | homog i b hb =>
    rcases homog_state_cases hb with h0 | ⟨kb, rfl⟩
    · subst h0; exact evZero_of_eq_zero (rightLHS_zero_state Y₁ Y₂ x y)
    · refine FusionTop.induction_weight P₁.isMod x
        (evZero_of_eq_zero fun K => by simp [rightLHS]) (fun a a' ha ha' => ?_) ?_
      · rw [show rightLHS Y₁ Y₂ b (a + a') y = fun K => rightLHS Y₁ Y₂ b a y K + rightLHS Y₁ Y₂ b a' y K
          from funext fun K => rightLHS_add_left Y₁ Y₂ b a a' y K]
        exact ha.add ha'
      · intro α₁ x hx
        refine FusionTop.induction_weight P₂.isMod y
          (evZero_of_eq_zero fun K => by simp [rightLHS]) (fun a a' ha ha' => ?_) ?_
        · rw [show rightLHS Y₁ Y₂ b x (a + a') = fun K => rightLHS Y₁ Y₂ b x a K + rightLHS Y₁ Y₂ b x a' K
            from funext fun K => rightLHS_add_right Y₁ Y₂ b x a a' K]
          exact ha.add ha'
        · intro α₂ y hy
          exact rightLHS_homog Y₁ Y₂ hb hx hy
  | add b b' hb hb' =>
    rw [show rightLHS Y₁ Y₂ (b + b') x y = fun K => rightLHS Y₁ Y₂ b x y K + rightLHS Y₁ Y₂ b' x y K
      from funext fun K => rightLHS_add_state Y₁ Y₂ b b' x y K]
    exact (hb x y).add (hb' x y)

end General

end VOA.Huang.GenusOneWard
