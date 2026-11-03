import VOA.Huang.LiConverseFinal
import VOA.Huang.LiFusionJacobi
import VOA.Huang.LiFusionTop

/-! # Extracting the scalar modes of the intertwiner

From the numeric Jacobi identity at `x = 1` (`numeric_jacobi`) we extract scalar mode
coefficients by weight bookkeeping: for homogeneous `w ∈ M_α`, `y ∈ (P₂)_β` and a test functional
`f` on `P₃`,

  `C(n, w, y, f) = G(w, y, ι_γ f)`,  `γ = α + β − n − 1`,

where `ι_γ f ∈ P₃'` is the restriction of `f` to the weight-`γ` space.  The opposite modes of
`P₃'` are the transposed ordinary modes of `P₃` (`dualPairing_oppB_contra`, a consequence of
`(Y°)° = Y`).

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiFusion VOA.Huang.HuangODEContra VOA.FZ
  FusionTop LaurentPolynomial VHat VHat.DLM3
open scoped BigOperators Polynomial

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

section Weights

variable {E : Type u} [AddCommGroup E] [Module ℂ E] (N : OrdVModule W E)

theorem weightProjection_of_mem_ne {β γ : ℂ} {v : E} (hv : v ∈ N.weight β) (h : γ ≠ β) :
    weightProjection N γ v = 0 := by
  rw [weightProjection, LinearMap.comp_apply, internalProjTo_eq_zero_of_ne N hv h]; rfl

/-- Weight projections commute with homogeneous modes, up to the weight shift. -/
theorem weightProjection_mode {k : ℤ} {a : V} (ha : a ∈ W.grading k) (q : ℤ) (γ : ℂ) (p : E) :
    weightProjection N (γ + ((k : ℂ) - q - 1)) (mode (N.YM a) q p)
      = mode (N.YM a) q (weightProjection N γ p) := by
  have hp : p ∈ ⨆ β : ℂ, N.weight β := by
    rw [N.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  induction hp using Submodule.iSup_induction' with
  | mem β p hp =>
    have hm := mode_mem_weight N ha hp q
    by_cases h : γ = β
    · subst h
      rw [weightProjection_of_mem N hp, weightProjection_of_mem N (by convert hm using 2; ring)]
    · rw [weightProjection_of_mem_ne N hp h, map_zero,
        weightProjection_of_mem_ne N hm (by intro h'; apply h; linear_combination h')]
  | zero => simp
  | add p p' _ _ hp hp' => rw [map_add, map_add, map_add, hp, hp', map_add]

/-- The weight-`γ` restriction `ι_γ f ∈ N'` of a functional on `N`. -/
noncomputable def iota (γ : ℂ) : Module.Dual ℂ E →ₗ[ℂ] RestrictedDual N :=
  (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ).comp (restrictToWeight N γ)

theorem dualPairing_iota (γ : ℂ) (f : Module.Dual ℂ E) (p : E) :
    dualPairing N p (iota N γ f) = f (weightProjection N γ p) := by
  change dualPairing N p (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ
    (restrictToWeight N γ f)) = _
  rw [dualPairing_lof]; rfl

theorem iota_comp_weightProjection (γ : ℂ) (f : Module.Dual ℂ E) :
    iota N γ (f.comp (weightProjection N γ)) = iota N γ f := by
  change DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ
    (restrictToWeight N γ (f.comp (weightProjection N γ)))
    = DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ (restrictToWeight N γ f)
  congr 1
  ext v
  simp only [restrictToWeight, LinearMap.lcomp_apply, LinearMap.comp_apply,
    Submodule.subtype_apply]
  rw [weightProjection_of_mem N v.2]

theorem restrictedDual_ext {φ ψ : RestrictedDual N} (h : ∀ p : E, dualPairing N p φ = dualPairing N p ψ) :
    φ = ψ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_dualPairing N fun p => ?_
  rw [map_sub, h, sub_self]

/-- **The opposite modes of `N'` are the transposed modes of `N`.** -/
theorem dualPairing_oppB_contra (a : V) (q : ℤ) (g : RestrictedDual N) (p : E) :
    dualPairing N p (oppB (contragredientModule N) a q g) = dualPairing N (mode (N.YM a) q p) g := by
  refine reduce_homogeneous W (P := fun a => dualPairing N p (oppB (contragredientModule N) a q g)
    = dualPairing N (mode (N.YM a) q p) g) ?_ ?_ ?_ a
  · intro k a ha
    rw [oppB_homog _ ha, mode_eq_oppB_twist N ha]
    simp only [LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply, map_smul, map_sum,
      smul_eq_mul]
    change _ = dpx N g _
    simp only [map_smul, map_sum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact dualPairing_contra_mode N _ _ p g
  · simp only [map_zero, mode_zero, LinearMap.zero_apply, Pi.zero_apply, dualPairing_zero_x]
  · intro a b ha hb
    simp only [map_add, mode_add, LinearMap.add_apply, Pi.add_apply] at ha hb ⊢
    rw [ha, hb, dualPairing_add_x]

/-- The opposite modes of `N'` on a restricted functional. -/
theorem oppB_contra_iota {k : ℤ} {a : V} (ha : a ∈ W.grading k) (q : ℤ) (γ : ℂ)
    (f : Module.Dual ℂ E) :
    oppB (contragredientModule N) a q (iota N (γ + ((k : ℂ) - q - 1)) f)
      = iota N γ (f.comp (mode (N.YM a) q)) := by
  refine restrictedDual_ext N fun p => ?_
  rw [dualPairing_oppB_contra, dualPairing_iota, dualPairing_iota, weightProjection_mode N ha]
  rfl

end Weights

end VOA.Huang.LiRegular

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiFusion VOA.Huang.HuangODEContra VOA.FZ
  FusionTop LaurentPolynomial VHat VHat.DLM3
open scoped BigOperators Polynomial

universe u'

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

section Additivity

variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
  {A₃ : OrdVModule W M₃} {Y : IntertwiningModes M₁ M₂ M₃}

/-- `ModeJacobiAt` for all states and vectors from the homogeneous case. -/
theorem modeJacobiAt_of_homog
    (htr : ∀ (w₁ : M₁) (w₂ : M₂) (n : ℂ), ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y (n + k) w₁ w₂ = 0)
    (l m : ℤ) (n : ℂ)
    (hhom : ∀ (k : ℤ) (a : V), a ∈ W.grading k → ∀ (α β : ℂ) (x : M₁), x ∈ A₁.weight α →
      ∀ y : M₂, y ∈ A₂.weight β → ModeJacobiAt A₁ A₂ A₃ Y a x y l m n)
    (a : V) (x : M₁) (y : M₂) : ModeJacobiAt A₁ A₂ A₃ Y a x y l m n := by
  have hL := fun a x y => IsIntertwiningOperator.jacL_support_finite (A₂ := A₂) (A₃ := A₃) htr a x y l m n
  have hR := fun a x y => IsIntertwiningOperator.jacR_support_finite (A₁ := A₁) Y a x y l m n
  -- additivity in each slot
  have addx : ∀ a x x' y, ModeJacobiAt A₁ A₂ A₃ Y a x y l m n →
      ModeJacobiAt A₁ A₂ A₃ Y a x' y l m n → ModeJacobiAt A₁ A₂ A₃ Y a (x + x') y l m n := by
    intro a x x' y h h'
    unfold ModeJacobiAt at *
    have e1 : IsIntertwiningOperator.jacL A₂ A₃ Y a (x + x') y l m n
        = IsIntertwiningOperator.jacL A₂ A₃ Y a x y l m n
          + IsIntertwiningOperator.jacL A₂ A₃ Y a x' y l m n := by
      funext i; simp only [IsIntertwiningOperator.jacL, map_add, LinearMap.add_apply, Pi.add_apply]
      module
    have e2 : IsIntertwiningOperator.jacR A₁ Y a (x + x') y l m n
        = IsIntertwiningOperator.jacR A₁ Y a x y l m n
          + IsIntertwiningOperator.jacR A₁ Y a x' y l m n := by
      funext i; simp only [IsIntertwiningOperator.jacR, map_add, LinearMap.add_apply, Pi.add_apply,
        smul_add]
    rw [e1, e2]
    simp only [Pi.add_apply]
    rw [finsum_add_distrib (hL a x y) (hL a x' y), finsum_add_distrib (hR a x y) (hR a x' y),
      h, h']
  have addy : ∀ a x y y', ModeJacobiAt A₁ A₂ A₃ Y a x y l m n →
      ModeJacobiAt A₁ A₂ A₃ Y a x y' l m n → ModeJacobiAt A₁ A₂ A₃ Y a x (y + y') l m n := by
    intro a x y y' h h'
    unfold ModeJacobiAt at *
    have e1 : IsIntertwiningOperator.jacL A₂ A₃ Y a x (y + y') l m n
        = IsIntertwiningOperator.jacL A₂ A₃ Y a x y l m n
          + IsIntertwiningOperator.jacL A₂ A₃ Y a x y' l m n := by
      funext i; simp only [IsIntertwiningOperator.jacL, map_add, LinearMap.add_apply, Pi.add_apply]
      module
    have e2 : IsIntertwiningOperator.jacR A₁ Y a x (y + y') l m n
        = IsIntertwiningOperator.jacR A₁ Y a x y l m n
          + IsIntertwiningOperator.jacR A₁ Y a x y' l m n := by
      funext i; simp only [IsIntertwiningOperator.jacR, map_add, LinearMap.add_apply, Pi.add_apply,
        smul_add]
    rw [e1, e2]
    simp only [Pi.add_apply]
    rw [finsum_add_distrib (hL a x y) (hL a x y'), finsum_add_distrib (hR a x y) (hR a x y'),
      h, h']
  have adda : ∀ a b x y, ModeJacobiAt A₁ A₂ A₃ Y a x y l m n →
      ModeJacobiAt A₁ A₂ A₃ Y b x y l m n → ModeJacobiAt A₁ A₂ A₃ Y (a + b) x y l m n := by
    intro a b x y h h'
    unfold ModeJacobiAt at *
    have e1 : IsIntertwiningOperator.jacL A₂ A₃ Y (a + b) x y l m n
        = IsIntertwiningOperator.jacL A₂ A₃ Y a x y l m n
          + IsIntertwiningOperator.jacL A₂ A₃ Y b x y l m n := by
      funext i; simp only [IsIntertwiningOperator.jacL, map_add, mode_add, LinearMap.add_apply,
        Pi.add_apply]
      module
    have e2 : IsIntertwiningOperator.jacR A₁ Y (a + b) x y l m n
        = IsIntertwiningOperator.jacR A₁ Y a x y l m n
          + IsIntertwiningOperator.jacR A₁ Y b x y l m n := by
      funext i; simp only [IsIntertwiningOperator.jacR, map_add, mode_add, LinearMap.add_apply,
        Pi.add_apply, smul_add]
    rw [e1, e2]
    simp only [Pi.add_apply]
    rw [finsum_add_distrib (hL a x y) (hL b x y), finsum_add_distrib (hR a x y) (hR b x y),
      h, h']
  have zero_x : ∀ a y, ModeJacobiAt A₁ A₂ A₃ Y a 0 y l m n := by
    intro a y
    unfold ModeJacobiAt
    simp [IsIntertwiningOperator.jacL, IsIntertwiningOperator.jacR]
  have zero_y : ∀ a x, ModeJacobiAt A₁ A₂ A₃ Y a x 0 l m n := by
    intro a x
    unfold ModeJacobiAt
    simp [IsIntertwiningOperator.jacL, IsIntertwiningOperator.jacR]
  have zero_a : ∀ x y, ModeJacobiAt A₁ A₂ A₃ Y 0 x y l m n := by
    intro x y
    unfold ModeJacobiAt
    simp [IsIntertwiningOperator.jacL, IsIntertwiningOperator.jacR]
  refine reduce_homogeneous W (P := fun a => ModeJacobiAt A₁ A₂ A₃ Y a x y l m n) ?_
    (zero_a x y) (fun a b ha hb => adda a b x y ha hb) a
  intro k a ha
  induction x using FusionTop.induction_weight (A₁ := A₁) with
  | h0 => exact zero_x a y
  | hadd x x' hx hx' => exact addx a x x' y hx hx'
  | hhom α x hx =>
    induction y using FusionTop.induction_weight (A₁ := A₂) with
    | h0 => exact zero_y a x
    | hadd y y' hy hy' => exact addy a x y y' hy hy'
    | hhom β y hy => exact hhom k a ha α β x hx y hy

end Additivity

section Extract

variable (A : OrdVModule W M) {P₂ P₃ : LWModule W} (T : fzSpace A P₂ P₃)
  (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
  (hrat : AdmissiblyRational W) (hP₃ : P₃.IsIrreducibleLW) (hP₂ : P₂.IsIrreducibleLW)

/-- The trilinear form `G`, bundled. -/
noncomputable def GtL : M →ₗ[ℂ] P₂.carrier →ₗ[ℂ] (Q₃ P₃).carrier →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun w y => (((oppBase (Qm P₃)).Dsub (-1)).subtype
      (PhiT A T Pr hrat hP₃ hP₂ w y)).comp (expOp (XQ_locNil P₃) zT))
    (fun w w' y => by ext g; simp [PhiT_add])
    (fun c w y => by ext g; simp [PhiT_smul])
    (fun w y y' => by ext g; simp)
    (fun c w y => by ext g; simp)

theorem GtL_apply (w : M) (y : P₂.carrier) (g : (Q₃ P₃).carrier) :
    GtL A T Pr hrat hP₃ hP₂ w y g = Gt A T Pr hrat hP₃ hP₂ w y g := rfl

/-- The `(α, β)`-component of the scalar modes. -/
noncomputable def innermost (n : ℂ) (α β : ℂ) :
    A.weight α →ₗ[ℂ] P₂.isMod.weight β →ₗ[ℂ] Module.Dual ℂ (Module.Dual ℂ P₃.carrier) :=
  LinearMap.mk₂ ℂ (fun w y => (GtL A T Pr hrat hP₃ hP₂ (w : M) (y : P₂.carrier)).comp
      (iota P₃.isMod (α + β - n - 1)))
    (fun w w' y => by ext f; simp)
    (fun c w y => by ext f; simp)
    (fun w y y' => by ext f; simp)
    (fun c w y => by ext f; simp)

/-- Summing over the weights of `P₂`. -/
noncomputable def innerFlip (n α : ℂ) :
    P₂.carrier →ₗ[ℂ] A.weight α →ₗ[ℂ] Module.Dual ℂ (Module.Dual ℂ P₃.carrier) :=
  letI := DirectSum.IsInternal.chooseDecomposition P₂.isMod.weight P₂.isMod.isInternal
  (DirectSum.toModule ℂ ℂ _ (fun β => (innermost A T Pr hrat hP₃ hP₂ n α β).flip)).comp
    (DirectSum.decomposeLinearEquiv P₂.isMod.weight).toLinearMap

/-- **The scalar modes of the reconstructed intertwiner.** -/
noncomputable def Cmodes : ScalarModes M P₂.carrier P₃.carrier := fun n =>
  letI := DirectSum.IsInternal.chooseDecomposition A.weight A.isInternal
  (DirectSum.toModule ℂ ℂ _ (fun α => (innerFlip A T Pr hrat hP₃ hP₂ n α).flip)).comp
    (DirectSum.decomposeLinearEquiv A.weight).toLinearMap

theorem Cmodes_homog {α β : ℂ} {x : M} (hx : x ∈ A.weight α) {y : P₂.carrier}
    (hy : y ∈ P₂.isMod.weight β) (n : ℂ) (f : Module.Dual ℂ P₃.carrier) :
    Cmodes A T Pr hrat hP₃ hP₂ n x y f
      = Gt A T Pr hrat hP₃ hP₂ x y (iota P₃.isMod (α + β - n - 1) f) := by
  letI := DirectSum.IsInternal.chooseDecomposition A.weight A.isInternal
  letI := DirectSum.IsInternal.chooseDecomposition P₂.isMod.weight P₂.isMod.isInternal
  have h1 : Cmodes A T Pr hrat hP₃ hP₂ n x
      = (innerFlip A T Pr hrat hP₃ hP₂ n α).flip ⟨x, hx⟩ := by
    change (DirectSum.toModule ℂ ℂ _ _) (DirectSum.decompose A.weight x) = _
    rw [DirectSum.decompose_of_mem A.weight hx, ← DirectSum.lof_eq_of ℂ,
      DirectSum.toModule_lof]
  have h2 : innerFlip A T Pr hrat hP₃ hP₂ n α y
      = (innermost A T Pr hrat hP₃ hP₂ n α β).flip ⟨y, hy⟩ := by
    change (DirectSum.toModule ℂ ℂ _ _) (DirectSum.decompose P₂.isMod.weight y) = _
    rw [DirectSum.decompose_of_mem P₂.isMod.weight hy, ← DirectSum.lof_eq_of ℂ,
      DirectSum.toModule_lof]
  rw [h1, LinearMap.flip_apply, h2, LinearMap.flip_apply]
  rfl

/-- **Weight compatibility** of the reconstructed scalar modes. -/
theorem Cmodes_weightCompatible :
    ScalarWeightCompatible A P₂.isMod P₃.isMod (Cmodes A T Pr hrat hP₃ hP₂) := by
  intro α β x y hx hy n f
  rw [Cmodes_homog A T Pr hrat hP₃ hP₂ hx hy, Cmodes_homog A T Pr hrat hP₃ hP₂ hx hy,
    iota_comp_weightProjection]

theorem negOnePow_eq_zpow (n : ℤ) : negOnePow n = (-1 : ℂ) ^ n := by
  rw [negOnePow]
  split_ifs with h
  · rw [h.neg_one_zpow]
  · rw [(Int.not_even_iff_odd.1 h).neg_one_zpow]

theorem Gt_zero_g (x : M) (y : P₂.carrier) : Gt A T Pr hrat hP₃ hP₂ x y 0 = 0 := by
  rw [← GtL_apply, map_zero]

theorem Gt_zero_y (x : M) (g : (Q₃ P₃).carrier) : Gt A T Pr hrat hP₃ hP₂ x 0 g = 0 := by
  rw [← GtL_apply, map_zero, LinearMap.zero_apply]

theorem Gt_zero_x (y : P₂.carrier) (g : (Q₃ P₃).carrier) : Gt A T Pr hrat hP₃ hP₂ 0 y g = 0 := by
  rw [← GtL_apply, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]

/-- **The Jacobi identity of the scalar modes, homogeneous case.** -/
theorem Cmodes_jacobiAt_homog {k : ℤ} {a : V} (ha : a ∈ W.grading k) {α β : ℂ} {x : M}
    (hx : x ∈ A.weight α) {y : P₂.carrier} (hy : y ∈ P₂.isMod.weight β) (l m : ℤ) (n : ℂ) :
    ScalarJacobiAt A P₂.isMod P₃.isMod (Cmodes A T Pr hrat hP₃ hP₂) a x y l m n := by
  intro f
  set γs : ℂ := α + β + k - n - l - m - 2
  set gs : (Q₃ P₃).carrier := iota P₃.isMod γs f
  have hX : ∀ i : ℤ, Cmodes A T Pr hrat hP₃ hP₂ (n + i) x y (f.comp (mode (P₃.isMod.YM a) (l + m - i)))
      = Gt A T Pr hrat hP₃ hP₂ x y (oppB (Qm P₃) a (l + m - i) gs) := by
    intro i
    rw [Cmodes_homog A T Pr hrat hP₃ hP₂ hx hy, ← oppB_contra_iota P₃.isMod ha]
    congr 4
    simp only [γs]; push_cast; ring
  have hY : ∀ i : ℤ, Cmodes A T Pr hrat hP₃ hP₂ ((l : ℂ) + n - i) x (mode (P₂.isMod.YM a) (m + i) y) f
      = Gt A T Pr hrat hP₃ hP₂ x (mode (P₂.isMod.YM a) (m + i) y) gs := by
    intro i
    rw [Cmodes_homog A T Pr hrat hP₃ hP₂ hx (mode_mem_weight P₂.isMod ha hy (m + i))]
    congr 3
    simp only [γs]; push_cast; ring
  have hZ : ∀ i : ℤ, Cmodes A T Pr hrat hP₃ hP₂ ((m : ℂ) + n - i) (mode (A.YM a) (l + i) x) y f
      = Gt A T Pr hrat hP₃ hP₂ (mode (A.YM a) (l + i) x) y gs := by
    intro i
    rw [Cmodes_homog A T Pr hrat hP₃ hP₂ (mode_mem_weight A ha hx (l + i)) hy]
    congr 3
    simp only [γs]; push_cast; ring
  simp only [hX, hY, hZ]
  obtain ⟨J₀, hJ₀⟩ := numeric_jacobi A T Pr hrat hP₃ hP₂ a l m x y gs
  obtain ⟨K₁, hK₁⟩ := oppB_trunc (Qm P₃) a gs
  obtain ⟨N₂, hN₂⟩ := P₂.isMod.toWeakModule.truncation a y
  obtain ⟨N₃, hN₃⟩ := A.toWeakModule.truncation a x
  set J : ℕ := J₀ + (l + m - K₁).toNat + (N₂ - m).toNat + (N₃ - l).toNat
  have hJ := hJ₀ J (by omega)
  have hsuppL : ∀ i : ℤ, i ∉ (Finset.range J).map Nat.castEmbedding →
      (negOnePow i * cbz l i) * (Gt A T Pr hrat hP₃ hP₂ x y (oppB (Qm P₃) a (l + m - i) gs)
        - negOnePow l * Gt A T Pr hrat hP₃ hP₂ x (mode (P₂.isMod.YM a) (m + i) y) gs) = 0 := by
    intro i hi
    simp only [Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply] at hi
    rcases lt_or_ge i 0 with hneg | hpos
    · rw [cbz_apply_neg l hneg, mul_zero, zero_mul]
    · have hiJ : (J : ℤ) ≤ i := by
        by_contra h
        exact hi ⟨i.toNat, by omega, by omega⟩
      rw [hK₁ _ (by omega), hN₂ _ (by omega), Gt_zero_g, Gt_zero_y, mul_zero, sub_zero, mul_zero]
  have hsuppR : ∀ i : ℤ, i ∉ (Finset.range J).map Nat.castEmbedding →
      cbz m i * Gt A T Pr hrat hP₃ hP₂ (mode (A.YM a) (l + i) x) y gs = 0 := by
    intro i hi
    simp only [Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply] at hi
    rcases lt_or_ge i 0 with hneg | hpos
    · rw [cbz_apply_neg m hneg, zero_mul]
    · have hiJ : (J : ℤ) ≤ i := by
        by_contra h
        exact hi ⟨i.toNat, by omega, by omega⟩
      rw [hN₃ _ (by omega), Gt_zero_x, mul_zero]
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range J).map Nat.castEmbedding)
      (fun i hi => by
        by_contra h
        exact (Function.mem_support.1 hi) (hsuppL i h)),
    finsum_eq_sum_of_support_subset _ (s := (Finset.range J).map Nat.castEmbedding)
      (fun i hi => by
        by_contra h
        exact (Function.mem_support.1 hi) (hsuppR i h)),
    Finset.sum_map, Finset.sum_map]
  simp only [Nat.castEmbedding_apply]
  rw [← hJ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [negOnePow_natCast, negOnePow_eq_zpow l,
    show ((-1 : ℂ) ^ (l - (i : ℤ))) = (-1 : ℂ) ^ l * (-1 : ℂ) ^ i by
      rw [zpow_sub₀ (by norm_num), zpow_natCast, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]]
  ring

/-- **The Jacobi identity of the reconstructed scalar modes.** -/
theorem Cmodes_jacobi : ScalarJacobi A P₂.isMod P₃.isMod (Cmodes A T Pr hrat hP₃ hP₂) := by
  have hw := Cmodes_weightCompatible A T Pr hrat hP₃ hP₂
  intro a x y l m n f
  have hMJ : ModeJacobiAt A P₂.isMod P₃.isMod (recoveredModes hw) a x y l m n :=
    modeJacobiAt_of_homog (truncation_of_weightCompatible (recoveredModes_weightCompatible hw))
      l m n (fun k a ha α β x hx y hy => (modeJacobiAt_recovered_iff hw a x y l m n).2
        (Cmodes_jacobiAt_homog A T Pr hrat hP₃ hP₂ ha hx hy l m n)) a x y
  exact (modeJacobiAt_recovered_iff hw a x y l m n).1 hMJ f

/-- **The reconstructed scalar modes extend the top datum `T`.** -/
theorem Cmodes_extendsTop : ExtendsTop A P₂ P₃ (Cmodes A T Pr hrat hP₃ hP₂) T := by
  intro α x hx y f
  rw [Cmodes_homog A T Pr hrat hP₃ hP₂ hx y.2,
    show α + P₂.h - (α + P₂.h - P₃.h - 1) - 1 = P₃.h by ring]
  set g := iota P₃.isMod P₃.h f
  have hg : g ∈ (Qm P₃).weight P₃.h := ⟨restrictToWeight P₃.isMod P₃.h f, rfl⟩
  have hXg : XQ P₃ g = 0 := by
    have h1 := L1m_pow_mem (Qm P₃) hg 1
    have hbot : (Qm P₃).weight (P₃.h - ((1 : ℕ) : ℂ)) = ⊥ := by
      by_contra hne
      obtain ⟨k, hk⟩ := (Q₃ P₃).isLow _ hne
      rw [show (Q₃ P₃).h = P₃.h from rfl] at hk
      have := congrArg Complex.re hk
      simp at this
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    rw [hbot, pow_one] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  rw [Gt, expOp_fix (XQ_locNil P₃) zT hXg]
  have hy : (y : P₂.carrier) = pBotIncl P₂ y := rfl
  rw [hy, PhiT_bot, phiT_coe, lamT_apply, Hs, LinearMap.comp_apply, Submodule.subtype_apply]
  have hgu : g = pBotIncl (Q₃ P₃) ⟨g, hg⟩ := rfl
  rw [hgu, Psi_bot, phiTop_coe, lamTop_apply, ← hgu, dualPairing_iota,
    weightProjection_of_mem P₃.isMod (T.val x y).2]

end Extract

end VOA.Huang.LiRegular
