import VOA.Huang.LogAssocCoefficientCompatibility

/-! The genuine all-logarithmic right associator on the complete intermediate
spectrum. Integer-row invariance is proved directly from the actual sums. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientCoproduct
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules VOA.Huang.AssocCommutator
open VOA.Huang.LogAssocJacobi VOA.Huang.LogAssocAssociator
open VOA.Huang.LogHuangODEModes
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

theorem fullCoset_shift (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b : ℂ) (d : ℤ) (t : ℂ) :
    logProductFullCosetFun Y₁ Y₂ f x y z (a-d) (b+d) t =
      logProductFullCosetFun Y₁ Y₂ f x y z a b t := by
  unfold logProductFullCosetFun
  apply tsum_congr
  intro k
  unfold logProductIntegerCosetFun
  rw [show a-(d : ℂ)+(b+d)=a+b by ring,prodFunZ_shift]

variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅

theorem fullCoset_assoc_right (u : V) (p : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) {NA NX NZ : ℕ}
    (hA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (N₄.YM u) (p-i)=0)
    (hX : ∀ i : ℕ, NX ≤ i → mode (N₁.YM u) i x=0)
    (hZ : ∀ i : ℕ, NZ ≤ i → mode (N₃.YM u) i z=0)
    (a b : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductFullCosetFun Y₁.1 Y₂.1 f x (mode (N₂.YM u) p y) z a b t =
      ∑ i∈Finset.range NA,negOnePow i*cbz p i*
        logProductFullCosetFun Y₁.1 Y₂.1 (f ∘ₗ mode (N₄.YM u) (p-i)) x y z a (b+i) t
      - negOnePow p*∑ i∈Finset.range NZ,negOnePow i*cbz p i*
        logProductFullCosetFun Y₁.1 Y₂.1 f x y (mode (N₃.YM u) i z) a (b+(p-i : ℤ)) t
      - ∑ r∈Finset.range NX,cbz p r*Complex.exp (((p-r : ℤ) : ℂ)*t)*
        logProductFullCosetFun Y₁.1 Y₂.1 f (mode (N₁.YM u) r x) y z (a+(p-r : ℤ)) b t := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  have hz : 1<‖1+Complex.exp t‖ := one_lt_norm ht
  have hconv (g : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (S ν : ℂ) (k : ℕ) :
      Summable (prodTermZ (fun n => Y₁.1 n k) (fun n => Y₂.1 n 0)
        g w₁ w₂ w₃ S ν (1+Complex.exp t) 1) :=
    summable_log_product_integerCoset hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ g w₁ w₂ w₃ S ν k 0 one_ne_zero (by simpa only [norm_one] using hz)
  have hk (k : ℕ) :
      logProductIntegerCosetFun Y₁.1 Y₂.1 f x (mode (N₂.YM u) p y) z a b k 0 t =
        ∑ i∈Finset.range NA,negOnePow i*cbz p i*
          logProductIntegerCosetFun Y₁.1 Y₂.1 (f ∘ₗ mode (N₄.YM u) (p-i)) x y z a (b+i) k 0 t
        - negOnePow p*∑ i∈Finset.range NZ,negOnePow i*cbz p i*
          logProductIntegerCosetFun Y₁.1 Y₂.1 f x y (mode (N₃.YM u) i z) a (b+(p-i : ℤ)) k 0 t
        - ∑ r∈Finset.range NX,cbz p r*Complex.exp (((p-r : ℤ) : ℂ)*t)*
          logProductIntegerCosetFun Y₁.1 Y₂.1 f (mode (N₁.YM u) r x) y z (a+(p-r : ℤ)) b k 0 t := by
    dsimp only [logProductIntegerCosetFun,prodFunZ]
    rw [prodValueZ_assoc_right (logCoefficient_isJacobi Y₁.2 k)
      (logCoefficient_isJacobi Y₂.2 0) u p f x y z hA hX hZ (a+b) b _ hz
      (fun i => hconv _ _ _ _ _ _ k) (fun i => hconv _ _ _ _ _ _ k)
      (fun i => hconv _ _ _ _ _ _ k)]
    simp only [Int.cast_natCast,mul_sub,Finset.mul_sum]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [show a+b+(i : ℂ)=a+(b+i) by push_cast; ring]
        ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [show a+b+((p-i : ℤ) : ℂ)=a+(b+(p-i : ℤ)) by ring]
        ring
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [show a+b+((p-r : ℤ) : ℂ)=a+(p-r : ℤ)+b by ring,
        add_sub_cancel_left,← Complex.exp_int_mul]
      ring
  simp only [fullCoset_eq_sum_log Y₂.1 (fun n k hk => hK Y₁ n k hk)]
  rw [Finset.sum_congr rfl (fun k _ => hk k),Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := Finset.range K)]


/-- The right associator with the true weight-indexed complete spectrum.
All inner row shifts are actual integer reindexings, and all original log
powers are retained. -/
theorem spectrum_assoc_right (u : V) (d p : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) {NA NX NZ : ℕ}
    (hA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (N₄.YM u) (p-i)=0)
    (hX : ∀ i : ℕ, NX ≤ i → mode (N₁.YM u) i x=0)
    (hZ : ∀ i : ℕ, NZ ≤ i → mode (N₃.YM u) i z=0)
    (a b c β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x (mode (N₂.YM u) p y) z
        a (b+d-p-1) c β t =
      ∑ i∈Finset.range NA,negOnePow i*cbz p i*
        logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
          (f ∘ₗ mode (N₄.YM u) (p-i)) x y z a b c (β-d+(p-i : ℤ)+1) t
      - negOnePow p*∑ i∈Finset.range NZ,negOnePow i*cbz p i*
        logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y (mode (N₃.YM u) i z)
          a b (c+d-i-1) β t
      - ∑ r∈Finset.range NX,cbz p r*Complex.exp (((p-r : ℤ) : ℂ)*t)*
        logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f (mode (N₁.YM u) r x) y z
          (a+d-r-1) b c β t := by
  classical
  have hmu (h : ℂ) :
      logProductFullCosetFun Y₁.1 Y₂.1 f x (mode (N₂.YM u) p y) z
          (a+h-β-1) ((b+d-p-1)+c-h-1) t =
        ∑ i∈Finset.range NA,negOnePow i*cbz p i*
          logProductFullCosetFun Y₁.1 Y₂.1 (f ∘ₗ mode (N₄.YM u) (p-i)) x y z
            (a+h-(β-d+(p-i : ℤ)+1)-1) (b+c-h-1) t
        - negOnePow p*∑ i∈Finset.range NZ,negOnePow i*cbz p i*
          logProductFullCosetFun Y₁.1 Y₂.1 f x y (mode (N₃.YM u) i z)
            (a+h-β-1) (b+(c+d-i-1)-h-1) t
        - ∑ r∈Finset.range NX,cbz p r*Complex.exp (((p-r : ℤ) : ℂ)*t)*
          logProductFullCosetFun Y₁.1 Y₂.1 f (mode (N₁.YM u) r x) y z
            ((a+d-r-1)+h-β-1) (b+c-h-1) t := by
    let A := a+h-β-1
    let B := b+c-h-1
    let δ : ℤ := d-p-1
    have eL := fullCoset_shift Y₁.1 Y₂.1 f x (mode (N₂.YM u) p y) z (A+δ) B δ t
    have eLa : A+((δ : ℤ) : ℂ)-δ=a+h-β-1 := by dsimp [A]; ring
    have eLb : B+δ=(b+d-p-1)+c-h-1 := by dsimp [B,δ]; push_cast; ring
    rw [eLa,eLb] at eL
    rw [eL,fullCoset_assoc_right hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ u p f x y z hA hX hZ (A+δ) B ht]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        have e := fullCoset_shift Y₁.1 Y₂.1 (f ∘ₗ mode (N₄.YM u) (p-i)) x y z
          (A+δ+i) B (i : ℤ) t
        simp only [Int.cast_natCast] at e
        rw [show A+(δ : ℂ)+(i : ℂ)-i=A+δ by ring] at e
        rw [e]
        congr 1
        dsimp [A,δ]
        push_cast
        ring
      · congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        have e := fullCoset_shift Y₁.1 Y₂.1 f x y (mode (N₃.YM u) i z)
          (A+δ) (B+(p-i : ℤ)) δ t
        rw [show A+(δ : ℂ)-δ=A by ring] at e
        rw [← e]
        congr 1
        dsimp [A,B,δ]
        push_cast
        ring
    · refine Finset.sum_congr rfl fun r _ => ?_
      congr 1
      congr 1
      dsimp [A,δ]
      push_cast
      ring
  unfold logProductSpectrumFun
  rw [Finset.sum_congr rfl (fun mu _ => hmu (spectrumCosetRep hC2 N₅ hfg₅ mu)),
    Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := spectrumCosets hC2 N₅ hfg₅)]

end VOA.Huang.LogAssocCoefficientCoproduct
