import VOA.DeligneAudit.LeviConversionBoxCore

/-! The box target and the exact combinatorial residue of Corollary C'. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V]

/-- Vectors whose remaining `a` modes have strictly smaller total mode. -/
def lowerModeSpan (a b : ℕ → A) (xs : List ℕ) (R : A) (v : V) :
    Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ zs bs : List ℕ, zs.sum < xs.sum ∧
    w = (aWord a zs * (bs.map b).prod) • (R • v)}

/-- The monomial selected from the top Wick contraction. -/
def boxTarget (a b : ℕ → A) (k s : ℕ) (xs ys : List ℕ)
    (R : A) (v : V) : V :=
  (aWord a xs * PowerSeries.coeff s (fCurrent b ^ k) * (ys.map b).prod) • (R • v)

/-- The remaining finite combinatorial identity needed for full box conversion.
It accounts for the `choose (xs.count 0 + k) k` identical zero contractions. -/
def BoxTopDecomposition (a b : ℕ → A) (k s : ℕ)
    (xs ys : List ℕ) (R : A) (v : V) : Prop :=
  let c : ℂ := (Nat.choose (xs.count 0 + k) k : ℂ)
  topSum a b k s (xs ++ List.replicate k 0) • (((ys.map b).prod * R) • v) -
    c • boxTarget a b k s xs ys R v ∈ lowerModeSpan a b xs R v

private theorem bProd_comm_f (f b : ℕ → A)
    (hfb : ∀ i j, f i * b j = b j * f i) (ys : List ℕ) (i : ℕ) :
    (ys.map b).prod * f i = f i * (ys.map b).prod := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.prod_cons]
    calc
      (b y * (ys.map b).prod) * f i = b y * ((ys.map b).prod * f i) :=
        mul_assoc _ _ _
      _ = b y * (f i * (ys.map b).prod) := by rw [ih]
      _ = f i * (b y * (ys.map b).prod) := by rw [← mul_assoc, ← hfb i y, mul_assoc]

/-- Corollary C' follows from the finite zero-contraction decomposition. -/
theorem box_conversion_of_decomposition (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k s : ℕ) (xs ys : List ℕ) (R : A) (v : V)
    (hRf : ∀ i, R * f i = f i * R)
    (hkill : PowerSeries.coeff s (fCurrent f ^ k) • v = 0)
    (hscalar : ∀ c : ℂ, ∀ w : V, (algebraMap ℂ A c) • w = c • w)
    (N : Submodule ℂ V)
    (hlower : lowerSum f a b k s (xs ++ List.replicate k 0) •
      (((ys.map b).prod * R) • v) ∈ N)
    (hdecomp : BoxTopDecomposition a b k s xs ys R v) :
    boxTarget a b k s xs ys R v ∈ lowerModeSpan a b xs R v ⊔ N := by
  let B : A := (ys.map b).prod
  have hbcomm (i : ℕ) : B * f i = f i * B := bProd_comm_f f b hfb ys i
  have hBR (i : ℕ) : (B * R) * f i = f i * (B * R) := by
    calc
      (B * R) * f i = B * (R * f i) := mul_assoc _ _ _
      _ = B * (f i * R) := by rw [hRf i]
      _ = f i * (B * R) := by rw [← mul_assoc, hbcomm i, mul_assoc]
  let topV := topSum a b k s (xs ++ List.replicate k 0) • ((B * R) • v)
  let target := boxTarget a b k s xs ys R v
  let L := lowerModeSpan a b xs R v
  let c : ℂ := (Nat.choose (xs.count 0 + k) k : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  have ht : topV ∈ N :=
    topSum_mem_higher_linear f a b hfa hfb hab k s
      (xs ++ List.replicate k 0) (B * R) v hBR hkill hscalar N hlower
  have hd : topV - c • target ∈ L := by
    simpa only [BoxTopDecomposition, topV, c, target, L, B] using hdecomp
  have hct : c • target ∈ L ⊔ N := by
    have h₁ : topV ∈ L ⊔ N := (le_sup_right : N ≤ L ⊔ N) ht
    have h₂ : topV - c • target ∈ L ⊔ N :=
      (le_sup_left : L ≤ L ⊔ N) hd
    have h₃ := (L ⊔ N).sub_mem h₁ h₂
    convert h₃ using 1 <;> abel
  have htarget := (L ⊔ N).smul_mem c⁻¹ hct
  simpa [smul_smul, inv_mul_cancel₀ hc] using htarget

/-- A termwise higher-weight hypothesis gives the same box reduction. -/
theorem box_conversion_of_higher_terms (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k s : ℕ) (xs ys : List ℕ) (R : A) (v : V)
    (hRf : ∀ i, R * f i = f i * R)
    (hkill : PowerSeries.coeff s (fCurrent f ^ k) • v = 0)
    (hscalar : ∀ c : ℂ, ∀ w : V, (algebraMap ℂ A c) • w = c • w)
    (N : Submodule ℂ V)
    (hHigher : ∀ p ∈ choices (xs ++ List.replicate k 0), p.2.length < k →
      conversionTerm f a b k s p • (((ys.map b).prod * R) • v) ∈ N)
    (hdecomp : BoxTopDecomposition a b k s xs ys R v) :
    boxTarget a b k s xs ys R v ∈ lowerModeSpan a b xs R v ⊔ N := by
  apply box_conversion_of_decomposition f a b hfa hfb hab k s xs ys R v hRf hkill
    hscalar N
  · exact lowerSum_mem_of_higher_terms f a b k s
      (xs ++ List.replicate k 0) ((ys.map b).prod * R) v N hHigher
  · exact hdecomp

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.box_conversion_of_decomposition
#print axioms VOA.DeligneAudit.LeviConversion.box_conversion_of_higher_terms
