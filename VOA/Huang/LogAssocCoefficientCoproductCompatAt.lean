import VOA.Huang.LogAssocCoefficientCoproductStable
import VOA.Huang.LogAssocCoefficientCoproductLeft
import VOA.Huang.LogAssocOutsideLinearity
import VOA.Modules.LogTensorPzMaximal

/-! Genuine P(1) compatibility of the actual all-logarithmic collision
coefficient span, and its inclusion in the true maximal compatible module. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientCoproduct
open VOA VOA.LogTensor VOA.LogTensor.Pz PowerSeries
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules VOA.Huang.LogAssocCoefficients
open VOA.Huang.PzTensorRho VOA.Huang.AssocAssociator
open VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.PzTensorCompatProof (Xpart Ypart)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

section InputLinearity
variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}

theorem defect_add_left {B : BilinearDual (M₁ := M₁) (M₂ := M₂)} {u : V}
    (htr : TruncAt A₁ A₂ u B) (m L : ℤ) (x x' : M₁) (y : M₂) :
    Dsl A₁ A₂ u m L B (x+x') y=Dsl A₁ A₂ u m L B x y+Dsl A₁ A₂ u m L B x' y := by
  unfold Dsl Out InL InR
  simp only [map_add,LinearMap.add_apply,mul_add]
  rw [finsum_add_distrib (Out_fin _ _ htr m L x y) (Out_fin _ _ htr m L x' y),
    finsum_add_distrib (InL_fin _ u m L B x y) (InL_fin _ u m L B x' y),
    finsum_add_distrib (InR_fin _ u m L B x y) (InR_fin _ u m L B x' y)]
  ring

theorem defect_add_right {B : BilinearDual (M₁ := M₁) (M₂ := M₂)} {u : V}
    (htr : TruncAt A₁ A₂ u B) (m L : ℤ) (x : M₁) (y y' : M₂) :
    Dsl A₁ A₂ u m L B x (y+y')=Dsl A₁ A₂ u m L B x y+Dsl A₁ A₂ u m L B x y' := by
  unfold Dsl Out InL InR
  simp only [map_add,mul_add]
  rw [finsum_add_distrib (Out_fin _ _ htr m L x y) (Out_fin _ _ htr m L x y'),
    finsum_add_distrib (InL_fin _ u m L B x y) (InL_fin _ u m L B x y'),
    finsum_add_distrib (InR_fin _ u m L B x y) (InR_fin _ u m L B x y')]
  ring

/-- True generalized homogeneous decompositions extend compatibility to
all actual module inputs. -/
theorem compatible_of_homogeneous (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    {B : BilinearDual (M₁ := M₁) (M₂ := M₂)} {u : V}
    (htr : TruncAt N₁.toWeakModule N₂.toWeakModule u B)
    (hc : ∀ (L : ℤ) (a b : ℂ) (x : M₁) (y : M₂),x∈N₁.weight a → y∈N₂.weight b →
      Dsl N₁.toWeakModule N₂.toWeakModule u 0 L B x y=0) :
    CompatAt N₁.toWeakModule N₂.toWeakModule u B := by
  intro L x y
  refine LogFin.induction_on N₁
    (C := fun x => Dsl N₁.toWeakModule N₂.toWeakModule u 0 L B x y=0) x ?_ ?_ ?_
  · intro a x hx
    refine LogFin.induction_on N₂
      (C := fun y => Dsl N₁.toWeakModule N₂.toWeakModule u 0 L B x y=0) y
      (fun b y hy => hc L a b x y hx hy) ?_ ?_
    · simp [Dsl,Out,InL,InR]
    · intro y y' hy hy'
      rw [defect_add_right htr _ _ _ _ _,hy,hy',add_zero]
  · simp [Dsl,Out,InL,InR]
  · intro x x' hx hx'
    rw [defect_add_left htr _ _ _ _ _,hx,hx',add_zero]
end InputLinearity

variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅


/-- Zero outside functional gives the actual zero collision coefficient. -/
theorem coefficient_zero_f (z : M₃) (c β γ : ℂ) (k : ℕ) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ 0 z c β γ k=0 := by
  change outsideCoefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ c β γ k 0 z=0
  rw [map_zero,LinearMap.zero_apply]

/-- The genuine m=0 compatibility slice holds on every true generalized
homogeneous input pair. -/
theorem coefficient_compatible_homogeneous (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c) {d : ℤ} {u : V} (hu : u∈W.grading d)
    (ell : ℤ) {a b : ℂ} {x : M₁} {y : M₂} (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) :
    Dsl N₁.toWeakModule N₂.toWeakModule u 0 ell
      (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k) x y=0 := by
  let C := coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k
  obtain ⟨Pt,hPt⟩ := coefficient_truncated hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f z c β γ k hf hz hu
  obtain ⟨QA,hQA⟩ := exists_comp_mode_vanish_below hf hu
  obtain ⟨NZ,hZ⟩ := exists_nat_truncation N₃ u z
  obtain ⟨NY,hY⟩ := exists_nat_truncation N₂ u y
  obtain ⟨Kb,M,hB⟩ := exists_coefficient_bounds hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  let Nf := (ell-QA).toNat
  have hNf (p : ℤ) (hp : p ≤ ell) (i : ℕ) (hi : Nf ≤ i) :
      f ∘ₗ mode (N₄.YM u) (p-i)=0 := hQA _ (by dsimp [Nf] at hi; omega)
  obtain ⟨Sw,hSw⟩ : ∃ Sw : ℕ,∀ s : ℕ,Sw ≤ s → ∀ i : ℕ,
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        f (mode (N₃.YM u) i z) (c+d-i-1) β (γ-d+ell+1-s) k=0 := by
    obtain ⟨S0,hS0⟩ := exists_nat_gt (γ.re+(ell : ℝ)-M+c.re+β.re)
    refine ⟨S0,fun s hs i => hB _ _ _ f ?_ hf _ k (Or.inr ?_)⟩
    · simpa only [Int.cast_natCast] using N₃.mode_mem_weight hu hz (i : ℤ)
    · have hs' : (S0 : ℝ) ≤ s := by exact_mod_cast hs
      have hi' : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      simp only [Complex.add_re,Complex.sub_re,Complex.intCast_re,Complex.one_re,Complex.natCast_re]
      linarith
  let K := max (max Nf Sw) (ell-Pt).toNat
  have hNK : Nf ≤ K := le_trans (le_max_left Nf Sw) (le_max_left _ _)
  have hSK : Sw ≤ K := le_trans (le_max_right Nf Sw) (le_max_left _ _)
  have hPK : (ell-Pt).toNat ≤ K := le_max_right _ _
  have hL := coefficient_assoc_left_homogeneous hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hu ell f z c β γ k hx hy
    (hNf ell le_rfl) hY hZ
  have hR (s : ℕ) : rhoL N₁.toWeakModule N₂.toWeakModule u (ell-s) C x y=
      (∑ i∈Finset.range Nf,negOnePow i*cbz (ell-s) i*
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          (f ∘ₗ mode (N₄.YM u) (ell-s-i)) z c (β-d+(ell-s-i : ℤ)+1) (γ-d+ell+1-s) k x y)
      - negOnePow (ell-s)*(∑ i∈Finset.range NZ,negOnePow i*cbz (ell-s) i*
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          f (mode (N₃.YM u) i z) (c+d-i-1) β (γ-d+ell+1-s) k x y) := by
    have he := congrArg (fun B : BilinearDual (M₁ := M₁) (M₂ := M₂) => B x y)
      (coefficient_coproduct hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ hu (ell-s) f z c β γ k (hNf _ (by omega)) hZ)
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.sum_apply,
      LinearMap.coe_sum,Finset.sum_apply,smul_eq_mul] at he
    rw [show γ-(d : ℂ)+((ell-s : ℤ) : ℂ)+1=γ-d+ell+1-s by push_cast; ring] at he
    exact he
  have hOut : Out N₁.toWeakModule N₂.toWeakModule u 0 ell C x y=
      ∑ s∈Finset.range K,cbz ell s*negOnePow s*rhoL N₁.toWeakModule N₂.toWeakModule u (ell-s) C x y := by
    unfold Out
    simp only [zero_add]
    rw [finsum_eq_sum_range (R := K) (fun s hs => by rw [cbz_apply_neg _ hs,mul_zero,zero_mul])
      (fun s hs => by
        have hv := hPt (ell-s) (by omega)
        rw [hv,LinearMap.zero_apply,LinearMap.zero_apply,mul_zero])]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hInL : InL N₁.toWeakModule u 0 ell C x y=C (mode (N₁.YM u) ell x) y := by
    unfold InL
    rw [finsum_eq_single (f := fun r : ℤ => cbz 0 r*C (mode (N₁.YM u) (ell+r) x) y) 0
      (fun r hr => by dsimp only; rw [cbz_zero_left,if_neg hr,zero_mul])]
    simp only [cbz_zero,add_zero,one_mul]
  have hInR : InR N₂.toWeakModule u 0 ell C x y=
      negOnePow ell*∑ j∈Finset.range NY,negOnePow j*cbz ell j*C x (mode (N₂.YM u) j y) := by
    unfold InR
    simp only [zero_add]
    rw [finsum_eq_sum_range (R := NY) (fun j hj => by rw [cbz_apply_neg _ hj,zero_mul,zero_mul])
      (fun j hj => by
        obtain ⟨i,rfl⟩ : ∃ i : ℕ,j=(i : ℤ) := ⟨j.toNat,by omega⟩
        rw [hY i (by exact_mod_cast hj),map_zero,mul_zero])]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PzTensorCompatProof.negOnePow_sub]
    ring
  have cX := Xpart (fun s q => coefficient hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ (f ∘ₗ mode (N₄.YM u) q) z c
      (β-d+q+1) (γ-d+ell+1-s) k x y) ell (Nf := Nf) (K := K) hNK
    (fun s i hi => by
      dsimp only
      rw [hNf ell le_rfl i hi,coefficient_zero_f hC2 N₁ N₂ N₃ N₄ N₅
        hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂,LinearMap.zero_apply,LinearMap.zero_apply])
  have cY := Ypart (fun s i => coefficient hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f (mode (N₃.YM u) i z) (c+d-i-1)
      β (γ-d+ell+1-s) k x y) ell (N₃ := NZ) (K := K)
    (fun s hs i => by dsimp only; rw [hSw s (le_trans hSK hs) i,LinearMap.zero_apply,LinearMap.zero_apply])
  change Dsl N₁.toWeakModule N₂.toWeakModule u 0 ell C x y=0
  unfold Dsl
  rw [hOut,hInL,hInR]
  change _-(coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    f z c β γ k (mode (N₁.YM u) ell x) y)-_=0
  rw [hL]
  simp only [hR,mul_sub,Finset.sum_sub_distrib]
  rw [← cX,← cY]
  dsimp only [C]
  ring


/-- Every literal all-logarithmic collision coefficient is genuinely
P(1)-compatible on the actual inside modules. -/
theorem coefficient_compatible (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c) {d : ℤ} {u : V} (hu : u∈W.grading d) :
    CompatAt N₁.toWeakModule N₂.toWeakModule u
      (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k) :=
  compatible_of_homogeneous N₁ N₂
    (coefficient_truncated hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f z c β γ k hf hz hu)
    (fun L a b x y hx hy => coefficient_compatible_homogeneous hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu L hx hy)

/-- All actual coefficient generators lie in the genuine regular-form
submodule, so compatibility survives their finite linear span. -/
theorem coefficientSpan_le_regular :
    coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ ≤
      regularForms N₁.toWeakModule N₂.toWeakModule := by
  apply Submodule.span_le.mpr
  rintro B ⟨f,z,c,β,γ,k,hf,hz,rfl⟩ d u hu
  exact ⟨coefficient_truncated hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f z c β γ k hf hz hu,
    coefficient_compatible hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f z c β γ k hf hz hu⟩

theorem coefficientSpan_compatible {d : ℤ} {u : V} (hu : u∈W.grading d)
    {B : BilinearDual (M₁ := M₁) (M₂ := M₂)}
    (hB : B∈coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) :
    CompatAt N₁.toWeakModule N₂.toWeakModule u B :=
  (coefficientSpan_le_regular hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hB d u hu).2

/-- The actual all-logarithmic coefficients form a genuine compatible
P(1) space, with all stability, truncation, and compatibility proved. -/
noncomputable def coefficientCompatibleSpace : CompatibleSpace N₁.toWeakModule N₂.toWeakModule where
  carrier := coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  stable d u hu n B hB := coefficientSpan_tau_stable hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hu n hB
  truncated B hB d u hu := coefficientSpan_truncated hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hu hB
  compatible B hB d u hu := coefficientSpan_compatible hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hu hB

/-- Inclusion in the actual maximal compatible carrier. -/
theorem coefficientSpan_le_maximal :
    coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ ≤
      maximalCarrier N₁.toWeakModule N₂.toWeakModule :=
  compatibleSpace_le_maximal N₁.toWeakModule N₂.toWeakModule
    (coefficientCompatibleSpace hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)

theorem coefficient_mem_maximal (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k ∈
      maximalCarrier N₁.toWeakModule N₂.toWeakModule :=
  coefficientSpan_le_maximal hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    (coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f z c β γ k hf hz)

/-- The actual coefficient span therefore carries its genuine weak VOA
module structure, including full Jacobi, without rationality premises. -/
noncomputable def coefficientWeakModule : WeakModule W
    (coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) :=
  (coefficientCompatibleSpace hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).weakModule

end VOA.Huang.LogAssocCoefficientCoproduct
