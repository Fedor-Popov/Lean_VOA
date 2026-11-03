import VOA.Huang.LogAssocCoefficientCoproductFunctions

/-! Actual all-log outside commutator on the full generalized intermediate spectrum. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocOutsideJacobi
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

variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅

theorem fullCoset_commutator (u : V) (m : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) {R : ℤ}
    (hX : ∀ i : ℤ, R ≤ i → mode (N₁.YM u) i x=0)
    (hY : ∀ i : ℤ, R ≤ i → mode (N₂.YM u) i y=0)
    (a b : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductFullCosetFun Y₁.1 Y₂.1 (f ∘ₗ mode (N₄.YM u) m) x y z a b t=
      logProductFullCosetFun Y₁.1 Y₂.1 f x y (mode (N₃.YM u) m z) a b t+
      ∑ i∈Finset.Ico 0 R,cbz m i*(1+Complex.exp t)^((m-i : ℤ) : ℂ)*
        logProductFullCosetFun Y₁.1 Y₂.1 f (mode (N₁.YM u) i x) y z (a+(m-i : ℤ)) b t+
      ∑ i∈Finset.Ico 0 R,cbz m i*
        logProductFullCosetFun Y₁.1 Y₂.1 f x (mode (N₂.YM u) i y) z a (b+(m-i : ℤ)) t := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  have hz : 1<‖1+Complex.exp t‖ := one_lt_norm ht
  have hconv (g : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (S ν : ℂ) (k : ℕ) :
      Summable (prodTermZ (fun n => Y₁.1 n k) (fun n => Y₂.1 n 0)
        g w₁ w₂ w₃ S ν (1+Complex.exp t) 1) :=
    summable_log_product_integerCoset hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ g w₁ w₂ w₃ S ν k 0 one_ne_zero (by simpa only [norm_one] using hz)
  have hk (k : ℕ) :
      logProductIntegerCosetFun Y₁.1 Y₂.1 (f ∘ₗ mode (N₄.YM u) m) x y z a b k 0 t=
        logProductIntegerCosetFun Y₁.1 Y₂.1 f x y (mode (N₃.YM u) m z) a b k 0 t+
        ∑ i∈Finset.Ico 0 R,cbz m i*(1+Complex.exp t)^((m-i : ℤ) : ℂ)*
          logProductIntegerCosetFun Y₁.1 Y₂.1 f (mode (N₁.YM u) i x) y z (a+(m-i : ℤ)) b k 0 t+
        ∑ i∈Finset.Ico 0 R,cbz m i*
          logProductIntegerCosetFun Y₁.1 Y₂.1 f x (mode (N₂.YM u) i y) z a (b+(m-i : ℤ)) k 0 t := by
    dsimp only [logProductIntegerCosetFun,prodFunZ]
    rw [prodValueZ_commutator (logCoefficient_isJacobi Y₁.2 k)
      (logCoefficient_isJacobi Y₂.2 0) u m f x y z hX hY (a+b) b
      (one_add_exp_ne_zero ht) one_ne_zero
      (hconv _ _ _ _ _ _ k) (fun i hi => hconv _ _ _ _ _ _ k)
      (fun i hi => hconv _ _ _ _ _ _ k)]
    simp only [mul_add,Finset.mul_sum,Complex.one_cpow,mul_one]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [show a+b+((m-i : ℤ) : ℂ)=a+(m-i : ℤ)+b by ring]
      ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [show a+b+((m-i : ℤ) : ℂ)=a+(b+(m-i : ℤ)) by ring]
      ring
  simp only [fullCoset_eq_sum_log Y₂.1 (fun n k hk => hK Y₁ n k hk)]
  rw [Finset.sum_congr rfl (fun k _ => hk k),Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := Finset.range K)]

/-- The outside commutator on the actual full generalized intermediate spectrum. -/
theorem spectrum_commutator (u : V) (d m : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) {R : ℤ}
    (hX : ∀ i : ℤ, R ≤ i → mode (N₁.YM u) i x=0)
    (hY : ∀ i : ℤ, R ≤ i → mode (N₂.YM u) i y=0)
    (a b c β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 (f ∘ₗ mode (N₄.YM u) m) x y z
        a b c (β-d+m+1) t=
      logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y (mode (N₃.YM u) m z)
        a b (c+d-m-1) β t+
      ∑ i∈Finset.Ico 0 R,cbz m i*(1+Complex.exp t)^((m-i : ℤ) : ℂ)*
        logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f (mode (N₁.YM u) i x) y z
          (a+d-i-1) b c β t+
      ∑ i∈Finset.Ico 0 R,cbz m i*
        logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x (mode (N₂.YM u) i y) z
          a (b+d-i-1) c β t := by
  classical
  have hmu (h : ℂ) :
      logProductFullCosetFun Y₁.1 Y₂.1 (f ∘ₗ mode (N₄.YM u) m) x y z
          (a+h-(β-d+m+1)-1) (b+c-h-1) t=
        logProductFullCosetFun Y₁.1 Y₂.1 f x y (mode (N₃.YM u) m z)
          (a+h-β-1) (b+(c+d-m-1)-h-1) t+
        ∑ i∈Finset.Ico 0 R,cbz m i*(1+Complex.exp t)^((m-i : ℤ) : ℂ)*
          logProductFullCosetFun Y₁.1 Y₂.1 f (mode (N₁.YM u) i x) y z
            ((a+d-i-1)+h-β-1) (b+c-h-1) t+
        ∑ i∈Finset.Ico 0 R,cbz m i*
          logProductFullCosetFun Y₁.1 Y₂.1 f x (mode (N₂.YM u) i y) z
            (a+h-β-1) ((b+d-i-1)+c-h-1) t := by
    let A := a+h-β-1
    let B := b+c-h-1
    let δ : ℤ := d-m-1
    rw [show a+h-(β-d+m+1)-1=A+δ by dsimp [A,δ]; push_cast; ring]
    rw [fullCoset_commutator hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ u m f x y z hX hY (A+δ) B ht]
    congr 1
    · congr 1
      · have he := LogAssocCoefficientCoproduct.fullCoset_shift Y₁.1 Y₂.1 f x y
          (mode (N₃.YM u) m z) (A+δ) B δ t
        rw [show A+(δ : ℂ)-δ=A by ring] at he
        rw [← he]
        congr 1
        dsimp [A,B,δ]
        push_cast
        ring
      · refine Finset.sum_congr rfl fun i hi => ?_
        congr 2
        dsimp [A,δ]
        push_cast
        ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      congr 1
      have he := LogAssocCoefficientCoproduct.fullCoset_shift Y₁.1 Y₂.1 f x
        (mode (N₂.YM u) i y) z (A+δ) (B+(m-i : ℤ)) δ t
      rw [show A+(δ : ℂ)-δ=A by ring] at he
      rw [← he]
      congr 1
      dsimp [A,B,δ]
      push_cast
      ring
  unfold logProductSpectrumFun
  rw [Finset.sum_congr rfl (fun mu _ => hmu (spectrumCosetRep hC2 N₅ hfg₅ mu)),
    Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := spectrumCosets hC2 N₅ hfg₅)]

end VOA.Huang.LogAssocOutsideJacobi
