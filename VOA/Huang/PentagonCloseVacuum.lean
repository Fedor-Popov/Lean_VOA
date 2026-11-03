import VOA.Huang.PentagonCloseEdges

/-! # Vacuum creation for the evaluation associator

The associator produced by `naturalReassociationOfEvaluation` satisfies the
creation-slice normalization `VacuumCreationCompatibility`. With a vacuum
middle input, the product side of the defining four-point identity collapses
to the single intermediate weight of `Y` (vacuum modes act by `δ_{n,-1}`), while
the iterate side is a convergent power series in the real coordinate (creation
for the right unit intertwiner). Its constant term, extracted by dominated
convergence as the coordinate tends to `0⁺`, is the inner mode `-1`.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff VOA.Huang.BraidingSkew
open Filter Topology
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Vacuum modes of the module vertex operator, at every complex mode. -/
theorem moduleIntertwiner_vacuum (X : Ordinary W) (m : ℂ) (y : X.carrier) :
    (moduleIntertwiner X.isMod).val m W.vacuum y = if m = -1 then y else 0 := by
  by_cases hm : ∃ k : ℤ, (k : ℂ) = m
  · obtain ⟨k, rfl⟩ := hm
    change moduleModes X.isMod (k : ℂ) W.vacuum y = _
    rw [moduleModes_apply_intCast, ← WeakModule.act_def, WeakModule.act_vacuum]
    by_cases hk : k = -1
    · subst hk; simp
    · rw [if_neg hk, if_neg]
      exact fun h => hk (by exact_mod_cast h)
  · change moduleModes X.isMod m W.vacuum y = _
    rw [moduleModes_of_not_int X.isMod (fun k hk => hm ⟨k, hk⟩), if_neg]
    · rfl
    · rintro rfl; exact hm ⟨-1, by simp⟩

/-- Creation for the right unit intertwiner: only modes `-1-j`, `j ∈ ℕ`, survive. -/
theorem skew_moduleIntertwiner_vacuum_eq_zero (X : Ordinary W) (x : X.carrier) {n : ℂ}
    (hn : ∀ j : ℕ, n ≠ -1 - j) :
    (skew vacuumObject X X (moduleIntertwiner X.isMod)).val n x W.vacuum = 0 := by
  change skewModes X.isMod.Lm1 omegaPhase (moduleIntertwiner X.isMod).val
    n x W.vacuum = 0
  rw [skewModes_apply (trunc_of_isIntertwining (moduleIntertwiner X.isMod).property)]
  rw [sSum, finsum_eq_zero_of_forall_eq_zero, smul_zero]
  intro j
  have h0 : (moduleIntertwiner X.isMod).val (n + j) W.vacuum x = 0 := by
    rw [moduleIntertwiner_vacuum, if_neg]
    intro h; exact hn j (by linear_combination h)
  change sc j • (X.isMod.Lm1 ^ j) ((moduleIntertwiner X.isMod).val (n + j) W.vacuum x) = 0
  rw [h0, map_zero, smul_zero]

variable (F : FusionChoice W)

theorem rightMode_vacuum_eq_zero (X : Ordinary W) (x : X.carrier) {n : ℂ}
    (hn : ∀ j : ℕ, n ≠ -1 - j) :
    (F X vacuumObject).intertwiner.val n x W.vacuum = 0 := by
  have h := congrArg (fun f : tensorObj F X vacuumObject ⟶ tensorObj F X vacuumObject =>
    f.val ((F X vacuumObject).intertwiner.val n x W.vacuum)) (rightUnitor F X).hom_inv_id
  simp only [Ordinary.comp_apply, rightUnitor_intertwiner, Ordinary.id_apply,
    skew_moduleIntertwiner_vacuum_eq_zero X x hn, map_zero] at h
  exact h.symm

theorem vacuum_mem_weight_zero : (W.vacuum : V) ∈ (vacuumObject (W := W)).isMod.weight 0 := by
  change W.vacuum ∈ adjWeight W 0
  rw [show (0 : ℂ) = ((0 : ℤ) : ℂ) by simp, adjWeight_cast]
  exact W.vacuum_mem_grading_zero

/-- A homogeneous vector killed by every functional supported at its weight is zero. -/
theorem ordinary_eq_zero_of_supported (X : Ordinary W) {δ : ℂ} {u : X.carrier}
    (hu : u ∈ X.isMod.weight δ)
    (h : ∀ f : X.carrier →ₗ[ℂ] ℂ, SupportedAt X.isMod f δ → f u = 0) : u = 0 := by
  by_contra hne
  have hu' : (⟨u, hu⟩ : X.isMod.weight δ) ≠ 0 := fun h0 => hne (congrArg Subtype.val h0)
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℂ (X.isMod.weight δ), g ⟨u, hu⟩ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu' ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp hcon)
  apply hg
  have hf : SupportedAt X.isMod (g ∘ₗ internalProjTo X.isMod.isInternal δ) δ := by
    intro α hα y hy
    simp only [LinearMap.comp_apply]
    rw [internalProjTo_eq_zero_of_ne X.isMod hy (Ne.symm hα), map_zero]
  have hh := h _ hf
  simp only [LinearMap.comp_apply] at hh
  rw [← hh]
  congr 1
  exact (Subtype.ext (internalProjTo_coe_mem X.isMod hu)).symm


/-- Additive in both variables and zero on homogeneous pairs: zero. -/
theorem ordinary_eq_zero_of_homog (X Y : Ordinary W) {N : Type*} [AddCommGroup N]
    (f : X.carrier → Y.carrier → N)
    (h1 : ∀ x x' y, f (x + x') y = f x y + f x' y) (h2 : ∀ x y y', f x (y + y') = f x y + f x y')
    (h : ∀ α γ x y, x ∈ X.isMod.weight α → y ∈ Y.isMod.weight γ → f x y = 0) :
    ∀ x y, f x y = 0 := by
  have h10 : ∀ y, f 0 y = 0 := fun y => by
    have := h1 0 0 y; rw [add_zero] at this; exact left_eq_add.mp this
  have h20 : ∀ x, f x 0 = 0 := fun x => by
    have := h2 x 0 0; rw [add_zero] at this; exact left_eq_add.mp this
  intro x y
  have hx : x ∈ ⨆ α, X.isMod.weight α := by
    rw [X.isMod.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  have hy : y ∈ ⨆ α, Y.isMod.weight α := by
    rw [Y.isMod.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction X.isMod.weight (motive := fun x => f x y = 0) hx ?_ (h10 y) ?_
  · intro α x hx
    refine Submodule.iSup_induction Y.isMod.weight (motive := fun y => f x y = 0) hy ?_
      (h20 x) ?_
    · intro γ y hy; exact h α γ x y hx hy
    · intro y y' hy hy'; rw [h2, hy, hy', add_zero]
  · intro x x' hx hx'; rw [h1, hx, hx', add_zero]

/-- Two biadditive maps agreeing on homogeneous pairs agree. -/
theorem ordinary_eq_of_homog (X Y : Ordinary W) {N : Type*} [AddCommGroup N]
    (f g : X.carrier → Y.carrier → N)
    (hf1 : ∀ x x' y, f (x + x') y = f x y + f x' y) (hf2 : ∀ x y y', f x (y + y') = f x y + f x y')
    (hg1 : ∀ x x' y, g (x + x') y = g x y + g x' y) (hg2 : ∀ x y y', g x (y + y') = g x y + g x y')
    (h : ∀ α γ x y, x ∈ X.isMod.weight α → y ∈ Y.isMod.weight γ → f x y = g x y) :
    ∀ x y, f x y = g x y := by
  intro x y
  rw [← sub_eq_zero]
  refine ordinary_eq_zero_of_homog X Y (fun x y => f x y - g x y) ?_ ?_ ?_ x y
  · intro x x' y; simp only [hf1, hg1]; abel
  · intro x y y'; simp only [hf2, hg2]; abel
  · intro α γ x y hx hy; simp only [h α γ x y hx hy, sub_self]

variable (H : OrdinaryFourPointInput F)

/-- The scalar creation identity, by extracting the constant term of the iterate
side of the defining four-point identity as the real coordinate tends to `0⁺`. -/
theorem evalAssoc_vacuum_scalar (X Y : Ordinary W) {α γ δ : ℂ} {x : X.carrier} {y : Y.carrier}
    (hx : x ∈ X.isMod.weight α) (hy : y ∈ Y.isMod.weight γ)
    {φ : (tensorObj F X Y).carrier →ₗ[ℂ] ℂ} (hφ : SupportedAt (tensorObj F X Y).isMod φ δ) :
    φ (((evalAssoc F H X vacuumObject Y).hom ≫ tensorHom F (𝟙 X) (leftUnitor F Y).hom).val
      (tripleMode F X vacuumObject Y (-1) (α + γ - δ - 1) x W.vacuum y)) =
      φ ((F X Y).intertwiner.val (α + γ - δ - 1) x y) := by
  let g : tensorObj F X (tensorObj F vacuumObject Y) ⟶ tensorObj F X Y :=
    tensorHom F (𝟙 X) (leftUnitor F Y).hom
  let I := postcompose (F (tensorObj F X vacuumObject) Y).intertwiner (tensorObj F X Y).isMod
    ((evalAssoc F H X vacuumObject Y).hom ≫ g)
  let J := postcompose (F X (tensorObj F vacuumObject Y)).intertwiner (tensorObj F X Y).isMod g
  let dc : ∀ c : ℝ, 0 < c → c < 1 → FourPointTest X vacuumObject Y (tensorObj F X Y) :=
    fun c h0 h1 =>
    { α := α, β := 0, γ := γ, δ := δ, x := x, y := W.vacuum, z := y, functional := φ
      hx := hx, hy := vacuum_mem_weight_zero (W := W), hz := hy, supported := hφ
      coordinate := c, positive := h0, less_one := h1 }
  let A : ℕ → ℂ := fun j => φ (((evalAssoc F H X vacuumObject Y).hom ≫ g).val
    ((F (tensorObj F X vacuumObject) Y).intertwiner.val (α + j + γ - δ - 1)
      ((F X vacuumObject).intertwiner.val (-1 - j) x W.vacuum) y))
  let P : ℂ := φ ((F X Y).intertwiner.val (α + γ - δ - 1) x y)
  have h4 := evalAssoc_fourPoint F H X vacuumObject Y (tensorObj F X Y) g
  have hterm (c : ℝ) (h0 : 0 < c) (h1 : c < 1) (j : ℕ) :
      iterateWeightTerm F I (dc c h0 h1) (α + j) = A j * (c : ℂ) ^ j := by
    simp only [iterateWeightTerm, dc, A, I]
    rw [show α + 0 - (α + (j : ℂ)) - 1 = -1 - j by ring,
      show α + (j : ℂ) - α - 0 = (j : ℂ) by ring, Complex.cpow_natCast]
    rfl
  have hinj : Function.Injective (fun j : ℕ => α + (j : ℂ)) := by
    intro i j hij
    exact_mod_cast add_left_cancel hij
  have hsupp (c : ℝ) (h0 : 0 < c) (h1 : c < 1) :
      Function.support (iterateWeightTerm F I (dc c h0 h1)) ⊆
        Set.range (fun j : ℕ => α + (j : ℂ)) := by
    intro w hw
    by_contra hr
    apply hw
    have hz : (F X vacuumObject).intertwiner.val (α + 0 - w - 1) x W.vacuum = 0 := by
      apply rightMode_vacuum_eq_zero
      intro j hj
      exact hr ⟨j, by linear_combination hj⟩
    simp only [iterateWeightTerm, dc]
    rw [hz]
    simp
  have hiter (c : ℝ) (h0 : 0 < c) (h1 : c < 1) :
      iterateEvaluation F I (dc c h0 h1) = ∑' j : ℕ, A j * (c : ℂ) ^ j := by
    rw [iterateEvaluation, ← hinj.tsum_eq (hsupp c h0 h1)]
    exact tsum_congr (hterm c h0 h1)
  have hJ (n m : ℂ) : J.val n x ((F vacuumObject Y).intertwiner.val m W.vacuum y) =
      (F X Y).intertwiner.val n x (if m = -1 then y else 0) := by
    change g.val _ = _
    erw [tensorHom_intertwiner]
    rw [leftUnitor_intertwiner, moduleIntertwiner_vacuum]
    rfl
  have hprod (c : ℝ) (h0 : 0 < c) (h1 : c < 1) :
      productEvaluation F J (dc c h0 h1) = P * (1 + (c : ℂ)) ^ (δ - α - γ) := by
    rw [productEvaluation, tsum_eq_single γ]
    · simp only [productWeightTerm, dc]
      erw [hJ]; rw [if_pos (by ring)]
    · intro w hw
      simp only [productWeightTerm, dc]
      erw [hJ]; rw [if_neg (fun h => hw (by linear_combination -h))]
      rw [LinearMap.map_zero]
      erw [map_zero φ]
      rw [zero_mul]
  have hsum (c : ℝ) (h0 : 0 < c) (h1 : c < 1) : Summable (fun j : ℕ => A j * (c : ℂ) ^ j) := by
    have hs := ((H.summability X vacuumObject Y (tensorObj F X Y) (dc c h0 h1)).1 I).comp_injective
      hinj
    exact hs.congr (hterm c h0 h1)
  have hlimL : Tendsto (fun c : ℝ => ∑' j : ℕ, A j * (c : ℂ) ^ j) (𝓝[>] 0) (𝓝 (A 0)) := by
    have hb : Summable (fun j : ℕ => ‖A j‖ * (1 / 2 : ℝ) ^ j) := by
      have := (hsum (1 / 2) (by norm_num) (by norm_num)).norm
      refine this.congr fun j => ?_
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    have hpt (j : ℕ) : Tendsto (fun c : ℝ => A j * (c : ℂ) ^ j) (𝓝[>] 0)
        (𝓝 (A j * (0 : ℂ) ^ j)) := by
      have hc : Continuous (fun c : ℝ => A j * (c : ℂ) ^ j) := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rw [Complex.ofReal_zero] at this
      exact this
    have ht := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun (c : ℝ) (j : ℕ) => A j * (c : ℂ) ^ j) (g := fun j => A j * (0 : ℂ) ^ j) hb
      hpt
      (by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with c hc j
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc.1.le]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.1.le hc.2.le j) (norm_nonneg _))
    rwa [tsum_eq_single 0 (fun j hj => by simp [zero_pow hj]), pow_zero, mul_one] at ht
  have hlimR : Tendsto (fun c : ℝ => P * (1 + (c : ℂ)) ^ (δ - α - γ)) (𝓝[>] 0) (𝓝 P) := by
    have hc : ContinuousAt (fun c : ℝ => P * (1 + (c : ℂ)) ^ (δ - α - γ)) 0 := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.comp (g := fun z : ℂ => z ^ (δ - α - γ))
        (f := fun c : ℝ => 1 + (c : ℂ))
      · simp only [Complex.ofReal_zero, add_zero]
        exact continuousAt_cpow_const (by simp [Complex.slitPlane])
      · fun_prop
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have heq : (fun c : ℝ => ∑' j : ℕ, A j * (c : ℂ) ^ j) =ᶠ[𝓝[>] 0]
      (fun c : ℝ => P * (1 + (c : ℂ)) ^ (δ - α - γ)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with c hc
    rw [← hiter c hc.1 hc.2, congrFun h4 (dc c hc.1 hc.2), hprod c hc.1 hc.2]
  have hA := tendsto_nhds_unique (hlimL.congr' heq) hlimR
  simp only [A, Nat.cast_zero, add_zero, sub_zero] at hA
  exact hA


/-- **Vacuum creation compatibility** for the associator produced by the evaluation
construction, for any ordinary four-point input. -/
theorem evalAssoc_vacuumCreation : VacuumCreationCompatibility F (evalAssoc F H) := by
  intro X Y q x y
  refine ordinary_eq_of_homog X Y (N := (tensorObj F X Y).carrier)
    (fun x y => ((evalAssoc F H X vacuumObject Y).hom ≫
      tensorHom F (𝟙 X) (leftUnitor F Y).hom).val
        (tripleMode F X vacuumObject Y (-1) q x W.vacuum y))
    (fun x y => (F X Y).intertwiner.val q x y) ?_ ?_ ?_ ?_ ?_ x y
  · intro x x' y
    simp only [tripleMode, map_add, LinearMap.add_apply]
    erw [map_add, LinearMap.add_apply, map_add]
  · intro x y y'
    simp only [tripleMode, map_add]
    erw [map_add]
  · intro x x' y
    simp only [map_add, LinearMap.add_apply]
    rfl
  · intro x y y'
    simp only [map_add]
    rfl
  intro α γ x y hx hy
  set δ : ℂ := α + γ - q - 1 with hδ
  have hq : α + γ - δ - 1 = q := by rw [hδ]; ring
  have h1 : (F X vacuumObject).intertwiner.val (-1) x W.vacuum ∈
      (tensorObj F X vacuumObject).isMod.weight α := by
    have := FusionTop.mem_weight (F X vacuumObject).intertwiner.property hx
      (vacuum_mem_weight_zero (W := W)) (-1)
    convert this using 2; ring
  have h2 : tripleMode F X vacuumObject Y (-1) q x W.vacuum y ∈
      (tensorObj F (tensorObj F X vacuumObject) Y).isMod.weight δ :=
    FusionTop.mem_weight (F (tensorObj F X vacuumObject) Y).intertwiner.property h1 hy q
  have hA := hom_mem_weight
    ((evalAssoc F H X vacuumObject Y).hom ≫ tensorHom F (𝟙 X) (leftUnitor F Y).hom).property h2
  have hB := FusionTop.mem_weight (F X Y).intertwiner.property hx hy q
  rw [← sub_eq_zero]
  apply ordinary_eq_zero_of_supported (tensorObj F X Y) (Submodule.sub_mem _ hA hB)
  intro f hf
  have hs := evalAssoc_vacuum_scalar F H X Y hx hy hf
  rw [hq] at hs
  rw [map_sub, sub_eq_zero]
  exact hs

/-- The strongly rational instance, for the associator of
`monoidalCategoryOfStronglyRationalSewing`. -/
theorem vacuumCreationCompatibility_pbw (hV : StronglyRational W) :
    VacuumCreationCompatibility F
      (naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators :=
  evalAssoc_vacuumCreation F (ordinaryFourPointInput_pbw F hV)

/-- Hence the triangle on modes, for the same associator. -/
theorem triangleOnModes_pbw (hV : StronglyRational W) :
    TriangleOnModes F
      (naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators :=
  triangleOnModes_of_vacuumCreation F _ (vacuumCreationCompatibility_pbw F hV)

end VOA.Huang.TensorCat
