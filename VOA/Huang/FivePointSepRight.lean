import VOA.Huang.FivePointSepProduct
import VOA.Huang.TensorCatJointGrowth

/-!
# Coefficient growth of the right (product) five-point expansion

The right pentagon vertex `X ⊠ (Y ⊠ (Z ⊠ T))` evaluates the actual product of three
fusion intertwiners at `z₁ = 1+s+r`, `z₂ = 1+s`, `z₃ = 1`. Its chart variables are
`x = z₂/z₁ = (1+s)/(1+s+r)` (second internal weight) and `y = z₃/z₂ = 1/(1+s)` (first
internal weight).

* `fivePointTerm_right_eq_sum` — finite simple presentations of the four inputs and of the
  output split the actual term into products of three intertwiners among IRREDUCIBLE
  external modules (intermediate modules unchanged);
* `norm_fivePointFactor_right` — the chart factor is exactly geometric in both levels;
* `fivePointCoefficientGrowth_right` — `LocalJointGrowth` of the actual right-tree
  array at every base weight, for strongly rational `W`, from the inner regular equation
  (`productCoeff_geometric`) and the proved four-point slice convergence (rows, at a
  smaller chart radius `r' = r/2`).
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.FusionTop VOA.Huang.HuangODEThree VOA.Huang.HuangODEProduct
open VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open Filter
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-! ## The chart factor -/

/-- The right-tree chart factor is geometric in both levels. -/
theorem fivePointFactor_right_shift {X Y Z T U : Ordinary W} (d : FivePointTest X Y Z T U)
    (w v : ℂ) (m n : ℕ) :
    fivePointFactor .right d (w + m, v + n) =
      fivePointFactor .right d (w, v) *
        ((((1 + d.s : ℝ) : ℂ) ^ n / ((1 + d.s + d.r : ℝ) : ℂ) ^ n) *
          (1 / ((1 + d.s : ℝ) : ℂ) ^ m)) := by
  have hs : (0 : ℝ) < 1 + d.s := by linarith [d.positive, d.smaller]
  have hsr : (0 : ℝ) < 1 + d.s + d.r := by linarith [d.positive, d.smaller]
  have hP : ((1 + d.s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hQ : ((1 + d.s + d.r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsr.ne'
  change ((1 + d.s : ℝ) : ℂ) ^ ((v + n) - d.β - (w + m)) *
      ((1 + d.s + d.r : ℝ) : ℂ) ^ (d.ε - d.α - (v + n)) =
    ((1 + d.s : ℝ) : ℂ) ^ (v - d.β - w) * ((1 + d.s + d.r : ℝ) : ℂ) ^ (d.ε - d.α - v) * _
  rw [show (v + n) - d.β - (w + m) = (v - d.β - w) + ((n : ℂ) - m) by ring,
    show d.ε - d.α - (v + n) = (d.ε - d.α - v) - (n : ℂ) by ring,
    Complex.cpow_add (v - d.β - w) ((n : ℂ) - m) hP, Complex.cpow_sub (n : ℂ) (m : ℂ) hP,
    Complex.cpow_sub (d.ε - d.α - v) (n : ℂ) hQ,
    Complex.cpow_natCast, Complex.cpow_natCast, Complex.cpow_natCast]
  have hPm : ((1 + d.s : ℝ) : ℂ) ^ m ≠ 0 := pow_ne_zero _ hP
  have hQn : ((1 + d.s + d.r : ℝ) : ℂ) ^ n ≠ 0 := pow_ne_zero _ hQ
  field_simp

theorem norm_fivePointFactor_right_pos {X Y Z T U : Ordinary W}
    (d : FivePointTest X Y Z T U) (w v : ℂ) : 0 < ‖fivePointFactor .right d (w, v)‖ := by
  have hs : (0 : ℝ) < 1 + d.s := by linarith [d.positive, d.smaller]
  have hsr : (0 : ℝ) < 1 + d.s + d.r := by linarith [d.positive, d.smaller]
  change 0 < ‖((1 + d.s : ℝ) : ℂ) ^ (v - d.β - w) * ((1 + d.s + d.r : ℝ) : ℂ) ^ (d.ε - d.α - v)‖
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hs,
    Complex.norm_cpow_eq_rpow_re_of_pos hsr]
  positivity

/-- The norm of the chart factor: `‖factor(w+m, v+n)‖ = ‖factor(w,v)‖ x₀ⁿ y₀ᵐ`. -/
theorem norm_fivePointFactor_right {X Y Z T U : Ordinary W} (d : FivePointTest X Y Z T U)
    (w v : ℂ) (m n : ℕ) :
    ‖fivePointFactor .right d (w + m, v + n)‖ =
      ‖fivePointFactor .right d (w, v)‖ * ((1 + d.s) / (1 + d.s + d.r)) ^ n *
        (1 / (1 + d.s)) ^ m := by
  have hs : (0 : ℝ) < 1 + d.s := by linarith [d.positive, d.smaller]
  have hsr : (0 : ℝ) < 1 + d.s + d.r := by linarith [d.positive, d.smaller]
  rw [fivePointFactor_right_shift, norm_mul, norm_mul, norm_div, norm_div, norm_pow, norm_pow,
    norm_pow, norm_one, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hs.le,
    Real.norm_of_nonneg hsr.le, div_pow, one_div_pow, one_div]
  ring

/-! ## Changing the vectors and the chart radius of a five-point test -/

variable {X Y Z T U : Ordinary W}

/-- Replace the four test vectors by homogeneous vectors of the same weights. -/
def testWithVectors (d : FivePointTest X Y Z T U) (x : X.carrier) (y : Y.carrier)
    (z : Z.carrier) (t : T.carrier) (hx : x ∈ X.isMod.weight d.α)
    (hy : y ∈ Y.isMod.weight d.β) (hz : z ∈ Z.isMod.weight d.γ)
    (ht : t ∈ T.isMod.weight d.δ) : FivePointTest X Y Z T U where
  α := d.α
  β := d.β
  γ := d.γ
  δ := d.δ
  ε := d.ε
  x := x
  y := y
  z := z
  t := t
  functional := d.functional
  hx := hx
  hy := hy
  hz := hz
  ht := ht
  supported := d.supported
  s := d.s
  r := d.r
  positive := d.positive
  smaller := d.smaller
  sum_lt := d.sum_lt

/-- Replace the second chart radius `r` by a smaller positive one. -/
def testWithR (d : FivePointTest X Y Z T U) (r' : ℝ) (h0 : 0 < r')
    (h1 : r' ≤ d.r) : FivePointTest X Y Z T U where
  α := d.α
  β := d.β
  γ := d.γ
  δ := d.δ
  ε := d.ε
  x := d.x
  y := d.y
  z := d.z
  t := d.t
  functional := d.functional
  hx := d.hx
  hy := d.hy
  hz := d.hz
  ht := d.ht
  supported := d.supported
  s := d.s
  r := r'
  positive := h0
  smaller := lt_of_le_of_lt h1 d.smaller
  sum_lt := by linarith [d.sum_lt]

/-! ## Splitting into irreducible external components -/

variable (F : FusionChoice W)

/-- The three intertwiners of the right tree. -/
abbrev rightY₁ (X Y Z T : Ordinary W) :=
  (F X (tensorObj F Y (tensorObj F Z T))).intertwiner
abbrev rightY₂ (Y Z T : Ordinary W) := (F Y (tensorObj F Z T)).intertwiner
abbrev rightY₃ (Z T : Ordinary W) := (F Z T).intertwiner

/-- Component data: simple presentations of the four inputs and the output. -/
structure RightPresentations (X Y Z T : Ordinary W) where
  PX : SimplePresentation X
  PY : SimplePresentation Y
  PZ : SimplePresentation Z
  PT : SimplePresentation T
  PO : SimplePresentation (fiveObj F X Y Z T .right)

variable {F}

/-- The component index. -/
abbrev RightPresentations.Idx (P : RightPresentations F X Y Z T) :=
  Fin P.PO.size × Fin P.PT.size × Fin P.PZ.size × Fin P.PY.size × Fin P.PX.size

/-- The component scalar coefficient (a product of three intertwiners among irreducible
external modules). -/
def RightPresentations.comp (P : RightPresentations F X Y Z T) (j : P.Idx)
    (k : fiveObj F X Y Z T .right ⟶ U) (d : FivePointTest X Y Z T U) (p q r : ℂ) : ℂ :=
  d.functional (k.val ((P.PO.inc j.1).val ((P.PO.proj j.1).val
    ((rightY₁ F X Y Z T).val p ((P.PX.inc j.2.2.2.2).val ((P.PX.proj j.2.2.2.2).val d.x))
      ((rightY₂ F Y Z T).val q ((P.PY.inc j.2.2.2.1).val ((P.PY.proj j.2.2.2.1).val d.y))
        ((rightY₃ F Z T).val r ((P.PZ.inc j.2.2.1).val ((P.PZ.proj j.2.2.1).val d.z))
          ((P.PT.inc j.2.1).val ((P.PT.proj j.2.1).val d.t))))))))

theorem fivePointTerm_right_def (k : fiveObj F X Y Z T .right ⟶ U)
    (d : FivePointTest X Y Z T U) (w v : ℂ) :
    fivePointTerm F .right k d (w, v) =
      d.functional (k.val ((rightY₁ F X Y Z T).val (d.α + v - d.ε - 1) d.x
        ((rightY₂ F Y Z T).val (d.β + w - v - 1) d.y
          ((rightY₃ F Z T).val (d.γ + d.δ - w - 1) d.z d.t)))) *
      fivePointFactor .right d (w, v) := rfl

/-- Finite decompositions of the identity in all five slots split a product of three
intertwiners (generic types; no carrier-instance bookkeeping). -/
theorem prod3_sum_decomp {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type*}
    [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
    [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
    [AddCommGroup M₆] [Module ℂ M₆]
    {ιo ι₁ ι₂ ι₃ ι₄ : Type*} [Fintype ιo] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (f : M₀ →ₗ[ℂ] ℂ) (Y₁ : ℂ → M₁ →ₗ[ℂ] M₆ →ₗ[ℂ] M₀)
    (Y₂ : ℂ → M₂ →ₗ[ℂ] M₅ →ₗ[ℂ] M₆) (Y₃ : ℂ → M₃ →ₗ[ℂ] M₄ →ₗ[ℂ] M₅)
    (πo : ιo → M₀ →ₗ[ℂ] M₀) (π₁ : ι₁ → M₁ →ₗ[ℂ] M₁) (π₂ : ι₂ → M₂ →ₗ[ℂ] M₂)
    (π₃ : ι₃ → M₃ →ₗ[ℂ] M₃) (π₄ : ι₄ → M₄ →ₗ[ℂ] M₄)
    (ho : ∀ v, ∑ o, πo o v = v) (h₁ : ∀ x, ∑ a, π₁ a x = x) (h₂ : ∀ y, ∑ b, π₂ b y = y)
    (h₃ : ∀ z, ∑ c, π₃ c z = z) (h₄ : ∀ t, ∑ g, π₄ g t = t)
    (p q r : ℂ) (x : M₁) (y : M₂) (z : M₃) (t : M₄) :
    f (Y₁ p x (Y₂ q y (Y₃ r z t))) =
      ∑ j : ιo × ι₄ × ι₃ × ι₂ × ι₁, f (πo j.1 (Y₁ p (π₁ j.2.2.2.2 x)
        (Y₂ q (π₂ j.2.2.2.1 y) (Y₃ r (π₃ j.2.2.1 z) (π₄ j.2.1 t))))) := by
  conv_lhs => rw [← h₁ x, ← h₂ y, ← h₃ z, ← h₄ t]
  conv_lhs => rw [← ho (Y₁ p _ _)]
  simp only [map_sum, LinearMap.sum_apply, Fintype.sum_prod_type]

/-- The actual right-tree coefficient is the finite sum of its irreducible components. -/
theorem right_eq_sum_comp (P : RightPresentations F X Y Z T)
    (k : fiveObj F X Y Z T .right ⟶ U) (d : FivePointTest X Y Z T U) (p q r : ℂ) :
    d.functional (k.val ((rightY₁ F X Y Z T).val p d.x
        ((rightY₂ F Y Z T).val q d.y ((rightY₃ F Z T).val r d.z d.t)))) =
      ∑ j : P.Idx, P.comp j k d p q r :=
  prod3_sum_decomp (d.functional ∘ₗ k.val) (rightY₁ F X Y Z T).val (rightY₂ F Y Z T).val
    (rightY₃ F Z T).val (fun o => (P.PO.proj o ≫ P.PO.inc o).val)
    (fun a => (P.PX.proj a ≫ P.PX.inc a).val) (fun b => (P.PY.proj b ≫ P.PY.inc b).val)
    (fun c => (P.PZ.proj c ≫ P.PZ.inc c).val) (fun g => (P.PT.proj g ≫ P.PT.inc g).val)
    P.PO.total P.PX.total P.PY.total P.PZ.total P.PT.total p q r d.x d.y d.z d.t

theorem norm_fivePointFactor_right_row {X Y Z T U : Ordinary W}
    (d : FivePointTest X Y Z T U) (w v : ℂ) (n : ℕ) :
    ‖fivePointFactor .right d (w, v + n)‖ =
      ‖fivePointFactor .right d (w, v)‖ * ((1 + d.s) / (1 + d.s + d.r)) ^ n := by
  have h := norm_fivePointFactor_right d w v 0 n
  simp only [Nat.cast_zero, add_zero, pow_zero, mul_one] at h
  exact h

/-! ## The component intertwiners -/

section Components
variable (P : RightPresentations F X Y Z T) (j : P.Idx)

/-- First component intertwiner (input and output restricted to simple summands). -/
def RightPresentations.Y₁ : IntertwiningModes (P.PX.part j.2.2.2.2).carrier
    (tensorObj F Y (tensorObj F Z T)).carrier (P.PO.part j.1).carrier :=
  fun p => (((rightY₁ F X Y Z T).val p).comp (P.PX.inc j.2.2.2.2).val).compr₂
    (P.PO.proj j.1).val

def RightPresentations.Y₂ : IntertwiningModes (P.PY.part j.2.2.2.1).carrier
    (tensorObj F Z T).carrier (tensorObj F Y (tensorObj F Z T)).carrier :=
  fun q => ((rightY₂ F Y Z T).val q).comp (P.PY.inc j.2.2.2.1).val

def RightPresentations.Y₃ : IntertwiningModes (P.PZ.part j.2.2.1).carrier
    (P.PT.part j.2.1).carrier (tensorObj F Z T).carrier :=
  fun r => (((rightY₃ F Z T).val r).comp (P.PZ.inc j.2.2.1).val).compl₂ (P.PT.inc j.2.1).val

theorem RightPresentations.isY₁ : IsIntertwiningOperator (P.PX.part j.2.2.2.2).isMod
    (tensorObj F Y (tensorObj F Z T)).isMod (P.PO.part j.1).isMod (P.Y₁ j) :=
  isIntertwiningOperator_compHom
    (isIntertwiningOperator_precomp (rightY₁ F X Y Z T).property (P.PX.inc j.2.2.2.2).property)
    (P.PO.proj j.1).property

theorem RightPresentations.isY₂ : IsIntertwiningOperator (P.PY.part j.2.2.2.1).isMod
    (tensorObj F Z T).isMod (tensorObj F Y (tensorObj F Z T)).isMod (P.Y₂ j) :=
  isIntertwiningOperator_precomp (rightY₂ F Y Z T).property (P.PY.inc j.2.2.2.1).property

theorem RightPresentations.isY₃ : IsIntertwiningOperator (P.PZ.part j.2.2.1).isMod
    (P.PT.part j.2.1).isMod (tensorObj F Z T).isMod (P.Y₃ j) :=
  precomp_right ⟨_, isIntertwiningOperator_precomp (rightY₃ F Z T).property
    (P.PZ.inc j.2.2.1).property⟩ (P.PT.inc j.2.1)

theorem RightPresentations.comp_eq (k : fiveObj F X Y Z T .right ⟶ U)
    (d : FivePointTest X Y Z T U) (p q r : ℂ) :
    P.comp j k d p q r = productCoeff (P.Y₁ j) (P.Y₂ j) (P.Y₃ j)
      (d.functional ∘ₗ k.val ∘ₗ (P.PO.inc j.1).val)
      ((P.PX.proj j.2.2.2.2).val d.x) ((P.PY.proj j.2.2.2.1).val d.y)
      ((P.PZ.proj j.2.2.1).val d.z) ((P.PT.proj j.2.1).val d.t) p q r := rfl

/-- The component as an actual five-point term of a modified test and output morphism. -/
def RightPresentations.test (d : FivePointTest X Y Z T U) : FivePointTest X Y Z T U :=
  testWithVectors d ((P.PX.inc j.2.2.2.2).val ((P.PX.proj j.2.2.2.2).val d.x))
    ((P.PY.inc j.2.2.2.1).val ((P.PY.proj j.2.2.2.1).val d.y))
    ((P.PZ.inc j.2.2.1).val ((P.PZ.proj j.2.2.1).val d.z))
    ((P.PT.inc j.2.1).val ((P.PT.proj j.2.1).val d.t))
    (hom_mem_weight (P.PX.inc _).property (hom_mem_weight (P.PX.proj _).property d.hx))
    (hom_mem_weight (P.PY.inc _).property (hom_mem_weight (P.PY.proj _).property d.hy))
    (hom_mem_weight (P.PZ.inc _).property (hom_mem_weight (P.PZ.proj _).property d.hz))
    (hom_mem_weight (P.PT.inc _).property (hom_mem_weight (P.PT.proj _).property d.ht))

theorem RightPresentations.term_eq (k : fiveObj F X Y Z T .right ⟶ U)
    (d : FivePointTest X Y Z T U) (r' : ℝ) (h0 : 0 < r') (h1 : r' ≤ d.r) (w v : ℂ) :
    fivePointTerm F .right (P.PO.proj j.1 ≫ P.PO.inc j.1 ≫ k)
        (testWithR (P.test j d) r' h0 h1) (w, v) =
      P.comp j k d (d.α + v - d.ε - 1) (d.β + w - v - 1) (d.γ + d.δ - w - 1) *
        fivePointFactor .right (testWithR d r' h0 h1) (w, v) := rfl

/-- Rows of the component arrays, from the proved slice convergence at the smaller chart
radius `r/2`. -/
theorem RightPresentations.rowBound (hs : OrdinaryFourPointSummability F)
    (k : fiveObj F X Y Z T .right ⟶ U) (d : FivePointTest X Y Z T U) (h h' : ℂ) :
    ProductRowBound (P.Y₁ j) (P.Y₂ j) (P.Y₃ j)
      (d.functional ∘ₗ k.val ∘ₗ (P.PO.inc j.1).val)
      ((P.PX.proj j.2.2.2.2).val d.x) ((P.PY.proj j.2.2.2.1).val d.y)
      ((P.PZ.proj j.2.2.1).val d.z) ((P.PT.proj j.2.1).val d.t)
      (d.α + h' - d.ε - 1) (d.β + h - h' - 1) (d.γ + d.δ - h - 1)
      ((1 + d.s + d.r / 2) / (1 + d.s)) := by
  intro k₀ j₀
  have hr0 : 0 < d.r / 2 := by linarith [d.positive]
  have hr1 : d.r / 2 ≤ d.r := by linarith [d.positive]
  set d' := testWithR (P.test j d) (d.r / 2) hr0 hr1 with hd'
  have hsl := fivePoint_slice_summable F hs .right (P.PO.proj j.1 ≫ P.PO.inc j.1 ≫ k) d'
    (h + j₀)
  have hinj : Function.Injective (fun m : ℕ => (h' - k₀) + (m : ℂ)) := by
    intro a b hab
    have : (a : ℂ) = b := by simpa using hab
    exact_mod_cast this
  have hsum := hsl.comp_injective hinj
  obtain ⟨K, hK⟩ := (hsum.tendsto_atTop_zero.norm).bddAbove_range
  have hs0 : (0 : ℝ) < 1 + d.s := by linarith [d.positive, d.smaller]
  have hs1 : (0 : ℝ) < 1 + d.s + d.r / 2 := by linarith [d.positive, d.smaller]
  set B := ‖fivePointFactor .right (testWithR d (d.r / 2) hr0 hr1) (h + j₀, h' - k₀)‖ with hB
  have hBpos : 0 < B := norm_fivePointFactor_right_pos _ _ _
  refine ⟨K / B, fun m => ?_⟩
  have hm : ‖fivePointTerm F .right (P.PO.proj j.1 ≫ P.PO.inc j.1 ≫ k) d'
      (h + j₀, (h' - k₀) + m)‖ ≤ K := hK ⟨m, rfl⟩
  rw [hd', P.term_eq j k d (d.r / 2) hr0 hr1, norm_mul,
    norm_fivePointFactor_right_row] at hm
  rw [← P.comp_eq j k d]
  have e : P.comp j k d (d.α + (h' - k₀ + m) - d.ε - 1) (d.β + (h + j₀) - (h' - k₀ + m) - 1)
      (d.γ + d.δ - (h + j₀) - 1) = P.comp j k d (d.α + h' - d.ε - 1 - k₀ + m)
        (d.β + h - h' - 1 + k₀ - m + j₀) (d.γ + d.δ - h - 1 - j₀) := by
    congr 1 <;> ring
  rw [e] at hm
  set x₁ : ℝ := (1 + d.s) / (1 + d.s + d.r / 2) with hx₁
  have hx₁0 : 0 < x₁ := by positivity
  change ‖_‖ * (B * ((1 + d.s) / (1 + d.s + d.r / 2)) ^ m) ≤ K at hm
  have hρ : (1 + d.s + d.r / 2) / (1 + d.s) = 1 / x₁ := by rw [hx₁]; field_simp
  rw [hρ, one_div_pow, show K / B * (1 / x₁ ^ m) = K / (B * x₁ ^ m) by field_simp,
    le_div_iff₀ (by positivity)]
  calc _ = ‖P.comp j k d (d.α + h' - d.ε - 1 - k₀ + m) (d.β + h - h' - 1 + k₀ - m + j₀)
        (d.γ + d.δ - h - 1 - j₀)‖ * (B * x₁ ^ m) := by ring
    _ ≤ K := hm

end Components

/-- Each irreducible component of the right-tree array has local joint growth. -/
theorem RightPresentations.comp_localJointGrowth (hV : StronglyRational W)
    (hs : OrdinaryFourPointSummability F) (P : RightPresentations F X Y Z T) (j : P.Idx)
    (k : fiveObj F X Y Z T .right ⟶ U) (d : FivePointTest X Y Z T U) (h h' : ℂ) :
    LocalJointGrowth (fun m n => P.comp j k d (d.α + (h' + n) - d.ε - 1)
      (d.β + (h + m) - (h' + n) - 1) (d.γ + d.δ - (h + m) - 1) *
        fivePointFactor .right d (h + m, h' + n)) := by
  have hC := moduleC1Data_of_stronglyRational hV
  obtain ⟨B₀, hD₀⟩ := (hC (P.PO.part j.1) (P.PO.irreducible j.1)).2
  obtain ⟨B₁, hC₁⟩ := (hC (P.PX.part j.2.2.2.2) (P.PX.irreducible j.2.2.2.2)).1
  obtain ⟨B₂, hC₂⟩ := (hC (P.PY.part j.2.2.2.1) (P.PY.irreducible j.2.2.2.1)).1
  obtain ⟨B₃, hC₃⟩ := (hC (P.PZ.part j.2.2.1) (P.PZ.irreducible j.2.2.1)).1
  obtain ⟨B₄, hC₄⟩ := (hC (P.PT.part j.2.1) (P.PT.irreducible j.2.1)).1
  have hs0 : (0 : ℝ) < 1 + d.s := by linarith [d.positive, d.smaller]
  have hsr : (0 : ℝ) < 1 + d.s + d.r := by linarith [d.positive, d.smaller]
  set ρ₁ : ℝ := (1 + d.s + d.r / 2) / (1 + d.s) with hρ₁
  set ρ₂ : ℝ := 1 + d.s / 2 with hρ₂
  have hρ₁1 : 1 < ρ₁ := by
    rw [hρ₁, one_lt_div hs0]; linarith [d.positive]
  have hρ₂1 : 1 < ρ₂ := by rw [hρ₂]; linarith [d.positive, d.smaller]
  obtain ⟨K, hK⟩ := productCoeff_geometric (P.isY₁ j) (P.isY₂ j) (P.isY₃ j)
    (P.PO.part j.1).isLow (P.PX.part j.2.2.2.2).isLow (P.PY.part j.2.2.2.1).isLow
    (P.PZ.part j.2.2.1).isLow (P.PT.part j.2.1).isLow hD₀ hC₁ hC₂ hC₃ hC₄
    (hom_mem_weight (P.PX.proj _).property d.hx) (hom_mem_weight (P.PY.proj _).property d.hy)
    (hom_mem_weight (P.PZ.proj _).property d.hz) (hom_mem_weight (P.PT.proj _).property d.ht)
    (d.functional ∘ₗ k.val ∘ₗ (P.PO.inc j.1).val)
    (d.α + h' - d.ε - 1) (d.β + h - h' - 1) (d.γ + d.δ - h - 1) hρ₁1 hρ₂1
    (P.rowBound j hs k d h h')
  set B := ‖fivePointFactor .right d (h, h')‖
  have hB0 : 0 ≤ B := norm_nonneg _
  refine localJointGrowth_of_geometric (K := K * B) (a := ρ₂ * (1 / (1 + d.s)))
    (b := ρ₁ * ((1 + d.s) / (1 + d.s + d.r))) (by positivity) ?_ (by positivity) ?_
    fun m n => ?_
  · rw [hρ₂, mul_one_div, div_lt_one hs0]; linarith [d.positive]
  · rw [hρ₁, div_mul_div_comm, div_lt_one (by positivity)]
    nlinarith [d.positive]
  · rw [norm_mul, norm_fivePointFactor_right d h h' m n, P.comp_eq]
    have e : productCoeff (P.Y₁ j) (P.Y₂ j) (P.Y₃ j)
        (d.functional ∘ₗ k.val ∘ₗ (P.PO.inc j.1).val)
        ((P.PX.proj j.2.2.2.2).val d.x) ((P.PY.proj j.2.2.2.1).val d.y)
        ((P.PZ.proj j.2.2.1).val d.z) ((P.PT.proj j.2.1).val d.t)
        (d.α + (h' + n) - d.ε - 1) (d.β + (h + m) - (h' + n) - 1) (d.γ + d.δ - (h + m) - 1) =
      productCoeff (P.Y₁ j) (P.Y₂ j) (P.Y₃ j)
        (d.functional ∘ₗ k.val ∘ₗ (P.PO.inc j.1).val)
        ((P.PX.proj j.2.2.2.2).val d.x) ((P.PY.proj j.2.2.2.1).val d.y)
        ((P.PZ.proj j.2.2.1).val d.z) ((P.PT.proj j.2.1).val d.t)
        (d.α + h' - d.ε - 1 + n) (d.β + h - h' - 1 - n + m) (d.γ + d.δ - h - 1 - m) := by
      congr 1 <;> ring
    rw [e]
    have h1 := hK n m
    have hx : 0 ≤ ((1 + d.s) / (1 + d.s + d.r)) ^ n := by positivity
    have hy : 0 ≤ (1 / (1 + d.s)) ^ m := by positivity
    calc _ ≤ (K * ρ₁ ^ n * ρ₂ ^ m) *
          (B * ((1 + d.s) / (1 + d.s + d.r)) ^ n * (1 / (1 + d.s)) ^ m) := by
          gcongr
      _ = K * B * (ρ₂ * (1 / (1 + d.s))) ^ m * (ρ₁ * ((1 + d.s) / (1 + d.s + d.r))) ^ n := by
          rw [mul_pow, mul_pow]; ring

/-- **Coefficient growth of the right (product) five-point expansion**, for a strongly
rational VOA (given finiteness of the irreducibles and the proved four-point summability). -/
theorem fivePointCoefficientGrowth_right (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (hs : OrdinaryFourPointSummability F) (k : fiveObj F X Y Z T .right ⟶ U)
    (d : FivePointTest X Y Z T U) (h h' : ℂ) :
    LocalJointGrowth (fun m n => fivePointTerm F .right k d (h + m, h' + n)) := by
  obtain ⟨PX⟩ := simplePresentation_nonempty hV hΦ X
  obtain ⟨PY⟩ := simplePresentation_nonempty hV hΦ Y
  obtain ⟨PZ⟩ := simplePresentation_nonempty hV hΦ Z
  obtain ⟨PT⟩ := simplePresentation_nonempty hV hΦ T
  obtain ⟨PO⟩ := simplePresentation_nonempty hV hΦ (fiveObj F X Y Z T .right)
  let P : RightPresentations F X Y Z T := ⟨PX, PY, PZ, PT, PO⟩
  refine LocalJointGrowth.congr (LocalJointGrowth.sum Finset.univ (fun j _ =>
    P.comp_localJointGrowth hV hs j k d h h')) fun m n => ?_
  rw [fivePointTerm_right_def, right_eq_sum_comp P, Finset.sum_mul]

end VOA.Huang.FivePointSep
