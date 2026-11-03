import VOA.DeligneAudit.LeviTypeA2CertGradedTop

/-! Corollary C' with a graded lower-mode remainder. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V]

theorem box_conversion_graded (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (haa : ∀ i j, a i * a j = a j * a i)
    (k s : ℕ) (xs ys : List ℕ) (R : A) (v : V)
    (hRf : ∀ i, R * f i = f i * R)
    (hkill : PowerSeries.coeff s (fCurrent f ^ k) • v = 0)
    (hscalar : ∀ c : ℂ, ∀ w : V, (algebraMap ℂ A c) • w = c • w)
    (N : Submodule ℂ V)
    (hHigher : ∀ p ∈ choices (xs ++ List.replicate k 0), p.2.length < k →
      conversionTerm f a b k s p • (((ys.map b).prod * R) • v) ∈ N) :
    boxTarget a b k s xs ys R v ∈
      gradedLowerModeSpan a b xs ys k (xs.sum + ys.sum + s) R v ⊔ N := by
  let B : A := (ys.map b).prod
  have hbcomm (i : ℕ) : B * f i = f i * B := by
    clear hHigher
    induction ys with
    | nil => simp [B]
    | cons y ys ih =>
        simp only [B, List.map_cons, List.prod_cons] at *
        calc
          (b y * (ys.map b).prod) * f i =
              b y * ((ys.map b).prod * f i) := mul_assoc _ _ _
          _ = b y * (f i * (ys.map b).prod) := by rw [ih]
          _ = f i * (b y * (ys.map b).prod) := by
            rw [← mul_assoc, ← hfb i y, mul_assoc]
  have hBR (i : ℕ) : (B * R) * f i = f i * (B * R) := by
    calc
      (B * R) * f i = B * (R * f i) := mul_assoc _ _ _
      _ = B * (f i * R) := by rw [hRf i]
      _ = f i * (B * R) := by rw [← mul_assoc, hbcomm i, mul_assoc]
  let topV := topSum a b k s (xs ++ List.replicate k 0) • ((B * R) • v)
  let target := boxTarget a b k s xs ys R v
  let G := gradedLowerModeSpan a b xs ys k (xs.sum + ys.sum + s) R v
  let c : ℂ := (Nat.choose (xs.count 0 + k) k : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  have hlower : lowerSum f a b k s (xs ++ List.replicate k 0) •
      (((ys.map b).prod * R) • v) ∈ N :=
    lowerSum_mem_of_higher_terms f a b k s
      (xs ++ List.replicate k 0) ((ys.map b).prod * R) v N hHigher
  have ht : topV ∈ N :=
    topSum_mem_higher_linear f a b hfa hfb hab k s
      (xs ++ List.replicate k 0) (B * R) v hBR hkill hscalar N hlower
  have hd : topV - c • target ∈ G := by
    simpa only [GradedBoxTopDecomposition, topV, c, target, G, B] using
      box_top_decomposition_graded a b haa k s xs ys R v
  have hct : c • target ∈ G ⊔ N := by
    have h₁ : topV ∈ G ⊔ N := (le_sup_right : N ≤ G ⊔ N) ht
    have h₂ : topV - c • target ∈ G ⊔ N :=
      (le_sup_left : G ≤ G ⊔ N) hd
    have h₃ := (G ⊔ N).sub_mem h₁ h₂
    convert h₃ using 1 <;> abel
  have htarget := (G ⊔ N).smul_mem c⁻¹ hct
  simpa [smul_smul, inv_mul_cancel₀ hc] using htarget

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.box_conversion_graded
