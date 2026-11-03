import VOA.Huang.GenusOneWardSquare

/-!
# The two-point minus-two Ward identity (left slot) in `ℂ⟦u⟧⟦t⟧`

From the minus-one identity for `L₋₁b` and `b` and the translation identity
`(L₋₁b + k b)[m] = −m b[m−1]`, the zero-mode term cancels and the collected
minus-two identity follows:

`Φ(b[−2]x, y) + Σ (2m+3) G_{2m+4} Φ(b[2m+2]x, y)
  + Σ ((m+1) Π_{m+1} − δ_{m0} G₂) Φ(x, b[m]y) = 0`.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.QEquation (TailBound)
open VOA.Huang.GenusOne (sqAct)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

section NegOne
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
  {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}

theorem Phi_sq_left_nonneg {c : V} {kc : ℕ} (hc : c ∈ W.grading (kc : ℤ))
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) (m : ℕ) :
    Phi Y₁ Y₂ (sqAct P₁.isMod c kc m x) y =
      ∑ j ∈ Finset.range K, sqBracketCoeff kc m j • famF Y₁ Y₂ c kc x y α₁ α₂ j := by
  rw [sqAct_nonneg_eq P₁.isMod c kc m x K (fun j hj => (hK j hj).1), map_sum,
    LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, LinearMap.smul_apply, Phi_homog Y₁ Y₂ (mode_mem_weight P₁.isMod hc hx j) hy]
  rfl

theorem Phi_sq_right_nonneg {c : V} {kc : ℕ} (hc : c ∈ W.grading (kc : ℤ))
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) (m : ℕ) :
    Phi Y₁ Y₂ x (sqAct P₂.isMod c kc m y) =
      ∑ j ∈ Finset.range K, sqBracketCoeff kc m j • famG Y₁ Y₂ c kc x y α₁ α₂ j := by
  rw [sqAct_nonneg_eq P₂.isMod c kc m y K (fun j hj => (hK j hj).2), map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, Phi_homog Y₁ Y₂ hx (mode_mem_weight P₂.isMod hc hy j)]
  rfl

theorem Phi_sq_left_neg_one {c : V} {kc : ℕ} (hc : c ∈ W.grading (kc : ℤ))
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) :
    Phi Y₁ Y₂ (sqAct P₁.isMod c kc (-1) x) y =
      famF Y₁ Y₂ c kc x y α₁ α₂ (-1) +
        ∑ j ∈ Finset.range K, sqBracketCoeffZ kc (-1) j • famF Y₁ Y₂ c kc x y α₁ α₂ j := by
  rw [sqAct_neg_one_eq P₁.isMod c kc x K (fun j hj => (hK j hj).1), map_add, map_sum,
    LinearMap.add_apply, LinearMap.sum_apply,
    Phi_homog Y₁ Y₂ (mode_mem_weight P₁.isMod hc hx (-1)) hy]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, LinearMap.smul_apply, Phi_homog Y₁ Y₂ (mode_mem_weight P₁.isMod hc hx j) hy]
  rfl

/-- **Minus-one identity in square-mode form**, for a homogeneous state of
positive weight and homogeneous insertions. -/
theorem ward_neg_one_phi {c : V} {kc : ℕ} (hk : 1 ≤ kc) (hc : c ∈ W.grading (kc : ℤ))
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) :
    Phi Y₁ Y₂ (sqAct P₁.isMod c kc (-1) x) y =
      Om Y₁ Y₂ c x y +
      ∑ m ∈ Finset.range K, eis (m + 1) *
        Phi Y₁ Y₂ (sqAct P₁.isMod c kc ((2 * m + 1 : ℕ) : ℤ) x) y +
      ∑ m ∈ Finset.range K, (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
        Phi Y₁ Y₂ x (sqAct P₂.isMod c kc (m : ℤ) y) := by
  rw [Phi_sq_left_neg_one Y₁ Y₂ hc hx hy K hK, ward_neg_one_trace Y₁ Y₂ hk hc hx hy K hK,
    famA_zero_mode Y₁ Y₂ hc hx hy]
  simp only [Phi_sq_left_nonneg Y₁ Y₂ hc hx hy K hK, Phi_sq_right_nonneg Y₁ Y₂ hc hx hy K hK]

end NegOne

/-! ## The translation identity on module square modes -/

theorem support_finite_of_Ico {M : Type*} [AddCommGroup M] (f : ℤ → M) (lo hi : ℤ)
    (h : ∀ i, (i < lo ∨ hi ≤ i) → f i = 0) : (Function.support f).Finite := by
  refine (Set.finite_Ico lo hi).subset fun i hi' => ?_
  simp only [Function.mem_support] at hi'
  simp only [Set.mem_Ico]
  by_contra hc
  exact hi' (h i (by omega))

/-- `(L₋₁b + k b)[m] = −m b[m−1]` on any module, for `b ∈ V_k`. -/
theorem sqAct_translation {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)
    (b : V) (kb : ℕ) (m : ℤ) (w : M) :
    sqAct A (W.L (-1) b) (kb + 1) m w + (kb : ℂ) • sqAct A b kb m w =
      (-(m : ℂ)) • sqAct A b kb (m - 1) w := by
  obtain ⟨T, hT⟩ := A.truncation b w
  have hL : ∀ i : ℤ, mode (A.YM (W.L (-1) b)) i w = (-(i : ℂ)) • mode (A.YM b) (i - 1) w := by
    intro i
    have h := act_T_covariance A.toWeakModule b i w
    simpa only [WeakModule.act_def] using h
  simp only [GenusOne.sqAct_apply]
  have hshift : (∑ᶠ i : ℤ, sqBracketCoeffZ (kb + 1) m i • mode (A.YM (W.L (-1) b)) i w) =
      ∑ᶠ i : ℤ, sqBracketCoeffZ (kb + 1) m (i + 1) • mode (A.YM (W.L (-1) b)) (i + 1) w :=
    (finsum_comp (fun i : ℤ => i + 1) (Equiv.addRight (1 : ℤ)).bijective).symm
  rw [hshift]
  simp only [hL, add_sub_cancel_right, smul_smul]
  have hsub : ∀ (f : ℤ → M), (∀ i, (i < m - 1 ∨ T ≤ i) → f i = 0) →
      ∑ᶠ i, f i = ∑ i ∈ Finset.Ico (m - 1) T, f i := by
    intro f hf
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_Ico, Set.mem_Ico]
    by_contra hc
    exact hi (hf i (by omega))
  rw [hsub _ (fun i hi => by
      rcases hi with hi | hi
      · rw [sqBracketCoeffZ_of_lt (kb + 1) (by omega), zero_mul, zero_smul]
      · rw [hT i hi, smul_zero]),
    hsub _ (fun i hi => by
      rcases hi with hi | hi
      · rw [sqBracketCoeffZ_of_lt kb (by omega), zero_smul]
      · rw [hT i hi, smul_zero]),
    hsub _ (fun i hi => by
      rcases hi with hi | hi
      · rw [sqBracketCoeffZ_of_lt kb (by omega), zero_smul]
      · rw [hT i hi, smul_zero]),
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, ← add_smul, smul_smul]
  congr 1
  have h := sqBracketCoeffZ_translation kb m i
  push_cast at h ⊢
  linear_combination h

/-- The zero-mode insertion of `L[−1]b = L₋₁b + k b` vanishes. -/
theorem Om_translation (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {b : V} {kb : ℕ} (hb : b ∈ W.grading (kb : ℤ)) (x : P₁.carrier) (y : P₂.carrier) :
    Om Y₁ Y₂ (W.L (-1) b) x y + (kb : ℂ) • Om Y₁ Y₂ b x y = 0 := by
  have hLb : W.L (-1) b ∈ W.grading ((kb : ℤ) + 1) := VertexOperatorAlgebra.L_neg_one_raise W hb
  have ho : oMod N.isMod (W.L (-1) b) + (kb : ℂ) • oMod N.isMod b = 0 := by
    rw [oMod_of_mem_grading N.isMod hLb, oMod_of_mem_grading N.isMod hb,
      show (kb : ℤ) + 1 - 1 = kb by ring]
    ext v
    have h := act_T_covariance N.isMod.toWeakModule b kb v
    simp only [WeakModule.act_def] at h
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply, h]
    push_cast
    rw [← add_smul]
    simp
  rw [← Om_smul, ← Om_add]
  refine FusionTop.induction_weight P₁.isMod x (by simp) (fun a c ha hc => ?_) ?_
  · simp only [map_add, LinearMap.add_apply, ha, hc, add_zero]
  · intro α₁ x hx
    refine FusionTop.induction_weight P₂.isMod y (by simp) (fun a c ha hc => ?_) ?_
    · simp only [map_add, ha, hc, add_zero]
    · intro α₂ y hy
      rw [Om_homog Y₁ Y₂ _ hx hy]
      apply ext2
      intro n k
      simp only [ofZ, omZ, c2_mk2, c2_zero, map_add, map_smul, ho, zero_mul]
      unfold lvl
      have := gradedTraceOp_smul N.isMod 0 (0 : Module.End ℂ N.carrier)
      rw [zero_smul] at this
      rw [this]
      simp

section NegTwo
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
  {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}

/-- Square modes of a vacuum-weight state vanish in nonnegative degree. -/
theorem sqAct_weight_zero_nonneg {M : Type u} [AddCommGroup M] [Module ℂ M]
    (A : OrdVModule W M) {b : V} (hb : b ∈ W.grading 0) (m : ℕ) (w : M) :
    sqAct A b 0 m w = 0 := by
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at hb
  obtain ⟨a, rfl⟩ := hb
  obtain ⟨T, hT⟩ := A.truncation (a • W.vacuum) w
  rw [sqAct_nonneg_eq A _ 0 m w T.toNat (fun j hj => hT j (by omega))]
  apply Finset.sum_eq_zero
  intro j _
  have h := A.toWeakModule.act_vacuum (j : ℤ) w
  simp only [WeakModule.act_def] at h
  rw [map_smul, mode_smul, LinearMap.smul_apply, h, if_neg (by omega), smul_zero, smul_zero]

/-- The zero-mode relation `Φ(b[0]x,y) + Φ(x,b[0]y) = 0`. -/
theorem Phi_zero_mode {b : V} {kb : ℕ} (hb : b ∈ W.grading (kb : ℤ))
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule b x y K) :
    Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((0 : ℕ) : ℤ) x) y +
      Phi Y₁ Y₂ x (sqAct P₂.isMod b kb ((0 : ℕ) : ℤ) y) = 0 := by
  rcases Nat.eq_zero_or_pos kb with h0 | hpos
  · subst h0
    rw [sqAct_weight_zero_nonneg P₁.isMod hb 0 x, sqAct_weight_zero_nonneg P₂.isMod hb 0 y,
      map_zero, map_zero, LinearMap.zero_apply, add_zero]
  · rw [Phi_sq_left_nonneg Y₁ Y₂ hb hx hy K hK, Phi_sq_right_nonneg Y₁ Y₂ hb hx hy K hK]
    have h0 : ∀ j : ℕ, sqBracketCoeff kb 0 j = cbz ((kb : ℤ) - 1) (j : ℤ) := by
      intro j
      rw [cbz_eq_sqBracketCoeffZ_zero kb hpos, ← sqBracketCoeffZ_of_nonneg, Nat.cast_zero]
    simp only [h0]
    exact fam_zero Y₁ Y₂ hb hx hy K hK

theorem tailBound_Lneg1 {b : V} {K : ℕ}
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule b x y K) :
    TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule (W.L (-1) b) x y (K + 1) := by
  intro j hj
  have h1 := act_T_covariance P₁.isMod.toWeakModule b j x
  have h2 := act_T_covariance P₂.isMod.toWeakModule b j y
  simp only [WeakModule.act_def] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [h1, (hK (j - 1) (by push_cast at hj; omega)).1, smul_zero]
  · rw [h2, (hK (j - 1) (by push_cast at hj; omega)).2, smul_zero]

theorem tailBound_mono {c : V} {K K' : ℕ} (h : K ≤ K')
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) :
    TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K' :=
  fun j hj => hK j (by omega)

/-- **The two-point minus-two Ward identity, left slot**, in `ℂ⟦u⟧⟦t⟧`, for a
homogeneous state and homogeneous insertions. -/
theorem ward_neg_two_phi {b : V} {kb : ℕ} (hb : b ∈ W.grading (kb : ℤ))
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ) (hK1 : 1 ≤ K)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule b x y K) :
    Phi Y₁ Y₂ (sqAct P₁.isMod b kb (-2) x) y +
      ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
        (eis (m + 2) * Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((2 * m + 2 : ℕ) : ℤ) x) y) +
      ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • piK (m + 1) - if m = 0 then eis 1 else 0) *
        Phi Y₁ Y₂ x (sqAct P₂.isMod b kb (m : ℤ) y) = 0 := by
  set c := W.L (-1) b with hcdef
  have hc : c ∈ W.grading ((kb + 1 : ℕ) : ℤ) := by
    rw [hcdef]; push_cast; exact VertexOperatorAlgebra.L_neg_one_raise W hb
  have hKc := tailBound_Lneg1 hK
  have hKb := tailBound_mono (show K ≤ K + 1 by omega) hK
  have h1 := ward_neg_one_phi Y₁ Y₂ (kc := kb + 1) (by omega) hc hx hy (K + 1) hKc
  -- the kb-multiple of the identity for b
  have h2 : (kb : ℂ) • Phi Y₁ Y₂ (sqAct P₁.isMod b kb (-1) x) y =
      (kb : ℂ) • (Om Y₁ Y₂ b x y +
        ∑ m ∈ Finset.range (K + 1), eis (m + 1) *
          Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((2 * m + 1 : ℕ) : ℤ) x) y +
        ∑ m ∈ Finset.range (K + 1),
          (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
            Phi Y₁ Y₂ x (sqAct P₂.isMod b kb (m : ℤ) y)) := by
    rcases Nat.eq_zero_or_pos kb with h0 | hpos
    · subst h0; simp
    · rw [ward_neg_one_phi Y₁ Y₂ hpos hb hx hy (K + 1) hKb]
  -- translation in both slots
  have hTl : ∀ m : ℤ, Phi Y₁ Y₂ (sqAct P₁.isMod c (kb + 1) m x) y +
      (kb : ℂ) • Phi Y₁ Y₂ (sqAct P₁.isMod b kb m x) y =
      (-(m : ℂ)) • Phi Y₁ Y₂ (sqAct P₁.isMod b kb (m - 1) x) y := by
    intro m
    rw [← LinearMap.smul_apply, ← map_smul, ← LinearMap.add_apply, ← map_add,
      sqAct_translation, map_smul, LinearMap.smul_apply]
  have hTr : ∀ m : ℤ, Phi Y₁ Y₂ x (sqAct P₂.isMod c (kb + 1) m y) +
      (kb : ℂ) • Phi Y₁ Y₂ x (sqAct P₂.isMod b kb m y) =
      (-(m : ℂ)) • Phi Y₁ Y₂ x (sqAct P₂.isMod b kb (m - 1) y) := by
    intro m
    rw [← map_smul, ← map_add, sqAct_translation, map_smul]
  have hOm := Om_translation Y₁ Y₂ hb x y
  have hz := Phi_zero_mode Y₁ Y₂ hb hx hy K hK
  -- the Eisenstein sum
  have hE : ∑ m ∈ Finset.range (K + 1), eis (m + 1) *
        Phi Y₁ Y₂ (sqAct P₁.isMod c (kb + 1) ((2 * m + 1 : ℕ) : ℤ) x) y +
      (kb : ℂ) • ∑ m ∈ Finset.range (K + 1), eis (m + 1) *
        Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((2 * m + 1 : ℕ) : ℤ) x) y =
      -(eis 1 * Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((0 : ℕ) : ℤ) x) y) -
        ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
          (eis (m + 2) * Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((2 * m + 2 : ℕ) : ℤ) x) y) := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    have hterm : ∀ m : ℕ, eis (m + 1) *
        Phi Y₁ Y₂ (sqAct P₁.isMod c (kb + 1) ((2 * m + 1 : ℕ) : ℤ) x) y +
        (kb : ℂ) • (eis (m + 1) * Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((2 * m + 1 : ℕ) : ℤ) x) y) =
        -(((2 * m + 1 : ℕ) : ℂ) • (eis (m + 1) *
          Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((2 * m : ℕ) : ℤ) x) y)) := by
      intro m
      rw [← mul_smul_comm, ← mul_add, hTl, show (((2 * m + 1 : ℕ) : ℤ) - 1) = ((2 * m : ℕ) : ℤ) by
        push_cast; ring, mul_smul_comm, neg_smul]
      norm_cast
    rw [Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_range_succ', Finset.sum_neg_distrib]
    have e0 : (((2 * 0 + 1 : ℕ) : ℂ) • (eis (0 + 1) *
        Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((2 * 0 : ℕ) : ℤ) x) y)) =
        eis 1 * Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((0 : ℕ) : ℤ) x) y := by
      rw [show 2 * 0 + 1 = 1 by rfl, Nat.cast_one, one_smul]
    have e1 : ∀ m : ℕ, (((2 * (m + 1) + 1 : ℕ) : ℂ) • (eis (m + 1 + 1) *
        Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((2 * (m + 1) : ℕ) : ℤ) x) y)) =
        ((2 * m + 3 : ℕ) : ℂ) • (eis (m + 2) *
          Phi Y₁ Y₂ (sqAct P₁.isMod b kb ((2 * m + 2 : ℕ) : ℤ) x) y) := fun m => rfl
    rw [e0]
    simp only [e1]
    abel
  -- the spatial sum
  have hP : ∑ m ∈ Finset.range (K + 1),
        (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
          Phi Y₁ Y₂ x (sqAct P₂.isMod c (kb + 1) (m : ℤ) y) +
      (kb : ℂ) • ∑ m ∈ Finset.range (K + 1),
        (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
          Phi Y₁ Y₂ x (sqAct P₂.isMod b kb (m : ℤ) y) =
      -∑ m ∈ Finset.range K, ((m + 1 : ℕ) : ℂ) • (piK (m + 1) *
        Phi Y₁ Y₂ x (sqAct P₂.isMod b kb (m : ℤ) y)) := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    have hterm : ∀ m : ℕ, (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
          Phi Y₁ Y₂ x (sqAct P₂.isMod c (kb + 1) (m : ℤ) y) +
        (kb : ℂ) • ((piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
          Phi Y₁ Y₂ x (sqAct P₂.isMod b kb (m : ℤ) y)) =
        (-(m : ℂ)) • ((piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
          Phi Y₁ Y₂ x (sqAct P₂.isMod b kb ((m : ℤ) - 1) y)) := by
      intro m
      rw [← mul_smul_comm, ← mul_add, hTr, mul_smul_comm]
      norm_cast
    rw [Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_range_succ', ← Finset.sum_neg_distrib]
    simp only [Nat.cast_zero, neg_zero, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro m _
    rw [if_neg (by omega), add_zero, show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) by push_cast; ring,
      neg_smul]
  -- assemble
  have hsum := congrArg₂ (· + ·) h1 h2
  simp only at hsum
  rw [hTl (-1), show ((-1 : ℤ) - 1) = -2 by norm_num, Int.cast_neg, Int.cast_one, neg_neg,
    one_smul, smul_add, smul_add] at hsum
  rw [← hcdef] at hOm
  have hδ : ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • piK (m + 1) -
        if m = 0 then eis 1 else 0) * Phi Y₁ Y₂ x (sqAct P₂.isMod b kb (m : ℤ) y) =
      ∑ m ∈ Finset.range K, ((m + 1 : ℕ) : ℂ) • (piK (m + 1) *
        Phi Y₁ Y₂ x (sqAct P₂.isMod b kb (m : ℤ) y)) -
        eis 1 * Phi Y₁ Y₂ x (sqAct P₂.isMod b kb ((0 : ℕ) : ℤ) y) := by
    rw [Finset.sum_congr rfl (fun m _ => by rw [sub_mul, smul_mul_assoc]), Finset.sum_sub_distrib]
    congr 1
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]
    rw [if_pos (by omega)]
  rw [hδ]
  linear_combination hsum + hE + hP + hOm - eis 1 * hz

end NegTwo

end VOA.Huang.GenusOneWard
