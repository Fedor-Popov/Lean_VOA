import VOA.Huang.LiFusionTop
import VOA.Core.Borcherds

/-! # Two boundary identities suffice for Li's scalar Jacobi verification

The finite Pascal argument is independent of an induced-module construction.
It applies on each complex mode coset. Weight support supplies the required
truncation; both the commutator and iterate boundaries are retained.
No existence of coefficients extending a top datum is asserted here.
-/
namespace VOA.Huang.LiFusion
open VOA
open scoped BigOperators

namespace Boundary
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Ordered composition sum, with integer indices on one fixed mode coset. -/
noncomputable def prod (F : ℤ → ℤ → E) (l m n : ℤ) : E :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz l i) • F (l + m - i) (n + i)

/-- Iterate sum. -/
noncomputable def iter (H : ℤ → ℤ → E) (l m n : ℤ) : E :=
  ∑ᶠ i : ℤ, cbz m i • H (l + i) (m + n - i)

/-- One argument is uniformly truncated; no truncation in the other is needed. -/
def TruncSecond (F : ℤ → ℤ → E) : Prop :=
  ∃ N : ℤ, ∀ p q, N ≤ q → F p q = 0

theorem prod_fin {F : ℤ → ℤ → E} (hF : TruncSecond F) (l m n d : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz l (i - d)) • F (l + m - i) (n + i)).Finite := by
  obtain ⟨N, hN⟩ := hF
  apply (Set.finite_Icc d (N - n)).subset
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg l (by omega), mul_zero, zero_smul]
  · rw [hN _ _ (by omega), smul_zero]

theorem prod_rec {F : ℤ → ℤ → E} (hF : TruncSecond F) (l m n : ℤ) :
    prod F l (m + 1) n = prod F l m (n + 1) + prod F (l + 1) m n := by
  have h1 : prod F (l + 1) m n = prod F l (m + 1) n +
      ∑ᶠ i : ℤ, (negOnePow i * cbz l (i - 1)) • F (l + 1 + m - i) (n + i) := by
    unfold prod
    rw [show (∑ᶠ i : ℤ, (negOnePow i * cbz (l + 1) i) • F (l + 1 + m - i) (n + i)) =
        ∑ᶠ i : ℤ, ((negOnePow i * cbz l i) • F (l + (m + 1) - i) (n + i) +
          (negOnePow i * cbz l (i - 1)) • F (l + 1 + m - i) (n + i)) from
      finsum_congr fun i => by
        rw [cbz_pascal_up, mul_add, add_smul,
          show l + 1 + m - i = l + (m + 1) - i by ring]]
    exact finsum_add_distrib
      (by simpa using prod_fin hF l (m + 1) n 0)
      (by simpa only [show l + (m + 1) = l + 1 + m by ring] using
        prod_fin hF l (m + 1) n 1)
  have h2 : (∑ᶠ i : ℤ, (negOnePow i * cbz l (i - 1)) • F (l + 1 + m - i) (n + i)) =
      -prod F l m (n + 1) := by
    rw [← finsum_int_succ_shift
      (fun i : ℤ => (negOnePow i * cbz l (i - 1)) • F (l + 1 + m - i) (n + i))]
    rw [show (∑ᶠ i : ℤ, (negOnePow (i + 1) * cbz l (i + 1 - 1)) •
          F (l + 1 + m - (i + 1)) (n + (i + 1))) =
        ∑ᶠ i : ℤ, -((negOnePow i * cbz l i) • F (l + m - i) (n + 1 + i)) from
      finsum_congr fun i => by
        rw [negOnePow_succ, neg_mul, neg_smul]
        rw [show i + 1 - 1 = i by ring,
          show l + 1 + m - (i + 1) = l + m - i by ring,
          show n + (i + 1) = n + 1 + i by ring]]
    exact finsum_neg_distrib _
  rw [h2] at h1
  rw [h1]
  abel

theorem iter_fin {H : ℤ → ℤ → E} (hH : TruncSecond (fun p q => H q p))
    (l m n d : ℤ) :
    (Function.support fun i : ℤ => cbz m (i - d) • H (l + i) (m + n - i)).Finite := by
  obtain ⟨N, hN⟩ := hH
  dsimp only at hN
  apply (Set.finite_Icc d (N - l)).subset
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg m (by omega), zero_smul]
  · rw [hN _ _ (by omega), smul_zero]

theorem iter_rec {H : ℤ → ℤ → E} (hH : TruncSecond (fun p q => H q p))
    (l m n : ℤ) :
    iter H l (m + 1) n = iter H l m (n + 1) + iter H (l + 1) m n := by
  unfold iter
  rw [show (∑ᶠ i : ℤ, cbz (m + 1) i • H (l + i) (m + 1 + n - i)) =
      ∑ᶠ i : ℤ, (cbz m i • H (l + i) (m + (n + 1) - i) +
        cbz m (i - 1) • H (l + i) (m + (n + 1) - i)) from
    finsum_congr fun i => by
      rw [cbz_pascal_up, add_smul, show m + 1 + n = m + (n + 1) by ring],
    finsum_add_distrib (by simpa using iter_fin hH l m (n + 1) 0)
      (iter_fin hH l m (n + 1) 1)]
  congr 1
  rw [← finsum_int_succ_shift
    (fun i : ℤ => cbz m (i - 1) • H (l + i) (m + (n + 1) - i))]
  exact finsum_congr fun i => by congr 2 <;> ring

/-- The discrepancy between the ordered products and the iterate. -/
noncomputable def defect (F G H : ℤ → ℤ → E) (l m n : ℤ) : E :=
  prod F l m n - negOnePow l • prod G l n m - iter H l m n

theorem defect_rec {F G H : ℤ → ℤ → E}
    (hF : TruncSecond F) (hG : TruncSecond G)
    (hH : TruncSecond (fun p q => H q p)) (l m n : ℤ) :
    defect F G H l (m + 1) n =
      defect F G H l m (n + 1) + defect F G H (l + 1) m n := by
  have hg := prod_rec hG l n m
  unfold defect
  rw [prod_rec hF, iter_rec hH, negOnePow_succ, hg]
  module

/-- Finite Pascal propagation: the two coordinate boundaries determine Jacobi. -/
theorem defect_eq_zero_of_boundaries {F G H : ℤ → ℤ → E}
    (hF : TruncSecond F) (hG : TruncSecond G)
    (hH : TruncSecond (fun p q => H q p))
    (hb : ∀ l n, defect F G H l 0 n = 0)
    (hc : ∀ m n, defect F G H 0 m n = 0) (l m n : ℤ) :
    defect F G H l m n = 0 := by
  induction m using Int.induction_on generalizing l n with
  | zero => exact hb l n
  | succ k ih => rw [defect_rec hF hG hH, ih, ih, add_zero]
  | pred k ih =>
    apply antidiag_pin (fun l n => defect F G H l (-(k : ℤ) - 1) n) ?_ (hc _) l n
    intro l n
    have he := defect_rec hF hG hH l (-(k : ℤ) - 1) n
    rw [show -(k : ℤ) - 1 + 1 = -k by ring, ih] at he
    exact eq_neg_of_add_eq_zero_left he.symm

theorem defect_eq_sub {F G H : ℤ → ℤ → E}
    (hF : TruncSecond F) (hG : TruncSecond G) (l m n : ℤ) :
    defect F G H l m n =
      (∑ᶠ i : ℤ, (negOnePow i * cbz l i) •
        (F (l + m - i) (n + i) - negOnePow l • G (l + n - i) (m + i))) -
      ∑ᶠ i : ℤ, cbz m i • H (l + i) (m + n - i) := by
  have hf := prod_fin hF l m n 0
  have hg := prod_fin hG l n m 0
  simp only [sub_zero] at hf hg
  unfold defect prod iter
  rw [smul_finsum' _ hg, ← finsum_sub_distrib hf
    (hg.subset (fun i hi hz => hi (by dsimp only at hz; rw [hz, smul_zero])))]
  congr 1
  exact finsum_congr fun i => by rw [smul_sub, smul_comm (negOnePow l)]

end Boundary

universe u
variable {V M₁ M₂ M₃ : Type u}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  {W : VertexOperatorAlgebra V}
  {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}

/-- A single full Jacobi equation, before any intertwiner has been constructed. -/
def ModeJacobiAt (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) (Y : IntertwiningModes M₁ M₂ M₃)
    (a : V) (x : M₁) (y : M₂) (l m : ℤ) (n : ℂ) : Prop :=
  (∑ᶠ i : ℤ, IsIntertwiningOperator.jacL A₂ A₃ Y a x y l m n i) =
    ∑ᶠ i : ℤ, IsIntertwiningOperator.jacR A₁ Y a x y l m n i

/-- The two boundaries suffice for every complex mode index. This is a
verification theorem; it does not produce the boundary equations. -/
theorem modeJacobi_of_boundaries {Y : IntertwiningModes M₁ M₂ M₃}
    (htr : ∀ x y n, ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y (n + k) x y = 0)
    (hb : ∀ a x y l n, ModeJacobiAt A₁ A₂ A₃ Y a x y l 0 n)
    (hc : ∀ a x y m n, ModeJacobiAt A₁ A₂ A₃ Y a x y 0 m n) :
    ModeJacobi A₁ A₂ A₃ Y := by
  intro a x y l m c
  let F : ℤ → ℤ → M₃ := fun p q => mode (A₃.YM a) p (Y (c + q) x y)
  let G : ℤ → ℤ → M₃ := fun p q => Y (c + p) x (mode (A₂.YM a) q y)
  let H : ℤ → ℤ → M₃ := fun p q => Y (c + q) (mode (A₁.YM a) p x) y
  have hF : Boundary.TruncSecond F := by
    obtain ⟨N, hN⟩ := htr x y c
    exact ⟨N, fun p q hq => by dsimp only [F]; rw [hN q hq, map_zero]⟩
  have hG : Boundary.TruncSecond G := by
    obtain ⟨N, hN⟩ := A₂.truncation a y
    exact ⟨N, fun p q hq => by dsimp only [G]; rw [hN q hq, map_zero]⟩
  have hH : Boundary.TruncSecond (fun p q => H q p) := by
    obtain ⟨N, hN⟩ := A₁.truncation a x
    exact ⟨N, fun p q hq => by dsimp only [H]; rw [hN q hq, map_zero, LinearMap.zero_apply]⟩
  have he (l m n : ℤ) : Boundary.defect F G H l m n = 0 ↔
      ModeJacobiAt A₁ A₂ A₃ Y a x y l m (c + n) := by
    rw [Boundary.defect_eq_sub hF hG, sub_eq_zero]
    unfold ModeJacobiAt IsIntertwiningOperator.jacL IsIntertwiningOperator.jacR
    dsimp [F, G, H]
    have e1 (i : ℤ) : c + ↑(n + i) = c + n + i := by push_cast; ring
    have e2 (i : ℤ) : c + ↑(l + n - i) = (l : ℂ) + (c + n) - i := by push_cast; ring
    have e3 (i : ℤ) : c + ↑(m + n - i) = (m : ℂ) + (c + n) - i := by push_cast; ring
    simp only [e1, e2, e3]
  have hz := Boundary.defect_eq_zero_of_boundaries hF hG hH
    (fun l n => (he l 0 n).mpr (hb a x y l (c + n)))
    (fun m n => (he 0 m n).mpr (hc a x y m (c + n))) l m 0
  simpa only [Int.cast_zero, add_zero] using (he l m 0).mp hz

/-- Reconstruction needs only weight support and the two Jacobi boundaries. -/
theorem isIntertwiningOperator_of_weight_boundaries {Y : IntertwiningModes M₁ M₂ M₃}
    (hw : WeightCompatible A₁ A₂ A₃ Y)
    (hb : ∀ a x y l n, ModeJacobiAt A₁ A₂ A₃ Y a x y l 0 n)
    (hc : ∀ a x y m n, ModeJacobiAt A₁ A₂ A₃ Y a x y 0 m n) :
    IsIntertwiningOperator A₁ A₂ A₃ Y :=
  isIntertwiningOperator_of_weightCompatible_jacobi hw
    (modeJacobi_of_boundaries (truncation_of_weightCompatible hw) hb hc)

/-- One scalar Jacobi equation; target modes act by precomposition on the test dual. -/
def ScalarJacobiAt (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) (C : ScalarModes M₁ M₂ M₃)
    (a : V) (x : M₁) (y : M₂) (l m : ℤ) (n : ℂ) : Prop :=
  ∀ f : Module.Dual ℂ M₃,
    (∑ᶠ i : ℤ, (negOnePow i * cbz l i) *
      (C (n + i) x y (f.comp (mode (A₃.YM a) (l + m - i))) -
        negOnePow l * C ((l : ℂ) + n - i) x (mode (A₂.YM a) (m + i) y) f)) =
      ∑ᶠ i : ℤ, cbz m i * C ((m : ℂ) + n - i) (mode (A₁.YM a) (l + i) x) y f

theorem modeJacobiAt_recovered_iff {C : ScalarModes M₁ M₂ M₃}
    (hw : ScalarWeightCompatible A₁ A₂ A₃ C) (a : V) (x : M₁) (y : M₂)
    (l m : ℤ) (n : ℂ) :
    ModeJacobiAt A₁ A₂ A₃ (recoveredModes hw) a x y l m n ↔
      ScalarJacobiAt A₁ A₂ A₃ C a x y l m n := by
  have he (f : Module.Dual ℂ M₃) :
      f (∑ᶠ i : ℤ, IsIntertwiningOperator.jacL A₂ A₃ (recoveredModes hw) a x y l m n i) =
        ∑ᶠ i : ℤ, (negOnePow i * cbz l i) *
          (C (n + i) x y (f.comp (mode (A₃.YM a) (l + m - i))) -
            negOnePow l * C ((l : ℂ) + n - i) x (mode (A₂.YM a) (m + i) y) f) := by
    rw [map_finsum f (IsIntertwiningOperator.jacL_support_finite
      (truncation_of_weightCompatible (recoveredModes_weightCompatible hw)) a x y l m n)]
    apply finsum_congr
    intro i
    simp only [IsIntertwiningOperator.jacL, map_smul, map_sub, smul_eq_mul,
      recoveredModes_pairing]
    rw [show f (mode (A₃.YM a) (l + m - i) (recoveredModes hw (n + i) x y)) =
        C (n + i) x y (f.comp (mode (A₃.YM a) (l + m - i))) from
      recoveredModes_pairing hw (n + i) x y (f.comp (mode (A₃.YM a) (l + m - i)))]
  have hr (f : Module.Dual ℂ M₃) :
      f (∑ᶠ i : ℤ, IsIntertwiningOperator.jacR A₁ (recoveredModes hw) a x y l m n i) =
        ∑ᶠ i : ℤ, cbz m i * C ((m : ℂ) + n - i) (mode (A₁.YM a) (l + i) x) y f := by
    rw [map_finsum f (IsIntertwiningOperator.jacR_support_finite
      (A₁ := A₁) (recoveredModes hw) a x y l m n)]
    exact finsum_congr fun i => by
      simp only [IsIntertwiningOperator.jacR, map_smul, smul_eq_mul, recoveredModes_pairing]
  constructor
  · intro hj f
    exact (he f).symm.trans ((congrArg f hj).trans (hr f))
  · intro hj
    exact dual_ext fun f => (he f).trans ((hj f).trans (hr f).symm)

/-- Full scalar Jacobi follows from its commutator and iterate boundaries. -/
theorem scalarJacobi_of_boundaries {C : ScalarModes M₁ M₂ M₃}
    (hw : ScalarWeightCompatible A₁ A₂ A₃ C)
    (hb : ∀ a x y l n, ScalarJacobiAt A₁ A₂ A₃ C a x y l 0 n)
    (hc : ∀ a x y m n, ScalarJacobiAt A₁ A₂ A₃ C a x y 0 m n) :
    ScalarJacobi A₁ A₂ A₃ C := by
  have hj := modeJacobi_of_boundaries
    (truncation_of_weightCompatible (recoveredModes_weightCompatible hw))
    (fun a x y l n => (modeJacobiAt_recovered_iff hw a x y l 0 n).mpr (hb a x y l n))
    (fun a x y m n => (modeJacobiAt_recovered_iff hw a x y 0 m n).mpr (hc a x y m n))
  intro a x y l m n
  exact (modeJacobiAt_recovered_iff hw a x y l m n).mp (hj a x y l m n)

/-- Boundary-only extension target. Constructing these coefficients under
rationality remains open; the implication to the original target is proved. -/
def ScalarBoundaryExtension {M : Type u} [AddCommGroup M] [Module ℂ M]
    (A : OrdVModule W M) (P₂ P₃ : LWModule W) : Prop :=
  ∀ T : FusionTop.fzSpace A P₂ P₃, ∃ C : ScalarModes M P₂.carrier P₃.carrier,
    ScalarWeightCompatible A P₂.isMod P₃.isMod C ∧
    (∀ a x y l n, ScalarJacobiAt A P₂.isMod P₃.isMod C a x y l 0 n) ∧
    (∀ a x y m n, ScalarJacobiAt A P₂.isMod P₃.isMod C a x y 0 m n) ∧
    ExtendsTop A P₂ P₃ C T

theorem scalarTopExtension_of_boundaryExtension
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    {A : OrdVModule W M} {P₂ P₃ : LWModule W}
    (hext : ScalarBoundaryExtension A P₂ P₃) : ScalarTopExtension A P₂ P₃ := by
  intro T
  obtain ⟨C, hw, hb, hc, ht⟩ := hext T
  exact ⟨C, hw, scalarJacobi_of_boundaries hw hb hc, ht⟩

/-- Boundary reduction preserves the original extension target exactly. -/
theorem scalarBoundaryExtension_iff_scalarTopExtension
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    {A : OrdVModule W M} {P₂ P₃ : LWModule W} :
    ScalarBoundaryExtension A P₂ P₃ ↔ ScalarTopExtension A P₂ P₃ := by
  refine ⟨scalarTopExtension_of_boundaryExtension, fun h T => ?_⟩
  obtain ⟨C, hw, hj, ht⟩ := h T
  exact ⟨C, hw, fun a x y l n => hj a x y l 0 n,
    fun a x y m n => hj a x y 0 m n, ht⟩

end VOA.Huang.LiFusion
