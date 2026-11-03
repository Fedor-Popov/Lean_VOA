import VOA.Huang.GenusOneWardNegTwo

/-!
# The right-slot Ward identity by trace cyclicity

`Tr_N Y₁(x) Y₂(y) q^{L₀} = Tr_Q Y₂(y) Y₁(x) q^{L₀}` level by level: the
`N`-level and the `Q`-level exchange roles. In `ℂ⟦u⟧⟦t⟧` this is the swap
`u ↔ t`, a ring automorphism fixing `q = u t`. Applying the left-slot identity
to the cyclically rotated trace and swapping gives the right-slot identity,
with the kernel parity `swap (piK m) = (−1)^{m+1} piK m`.
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

/-! ## The swap automorphism -/

/-- `u ↔ t`. -/
def swapFun (f : R2) : R2 := mk2 fun n k => c2 f k n

@[simp] theorem c2_swapFun (f : R2) (n k : ℕ) : c2 (swapFun f) n k = c2 f k n := by
  simp [swapFun]

/-- The swap as a ring homomorphism. -/
def swap2 : R2 →+* R2 where
  toFun := swapFun
  map_one' := ext2 fun n k => by
    rw [c2_swapFun, c2_one, c2_one]
    simp only [and_comm]
  map_mul' f g := ext2 fun n k => by
    rw [c2_swapFun, c2_mul, c2_mul, Finset.sum_comm]
    simp only [c2_swapFun]
  map_zero' := ext2 fun n k => by simp
  map_add' f g := ext2 fun n k => by simp

@[simp] theorem c2_swap2 (f : R2) (n k : ℕ) : c2 (swap2 f) n k = c2 f k n := c2_swapFun f n k

theorem swap2_smul (a : ℂ) (f : R2) : swap2 (a • f) = a • swap2 f :=
  ext2 fun n k => by simp

theorem swap2_eis (j : ℕ) : swap2 (eis j) = eis j := by
  apply ext2
  intro n k
  simp only [c2_swap2, eis, c2_mk2]
  split_ifs with h1 h2 h2 <;> first | rfl | (subst h1; rfl) | omega

theorem c2_piK (m n k : ℕ) : c2 (piK m) n k =
    (if n < k ∧ (k - n) ∣ n then (((k - n : ℕ) : ℂ) ^ m / (m.factorial : ℂ)) else 0) -
    (if k < n ∧ (n - k) ∣ k then ((-((n - k : ℕ) : ℂ)) ^ m / (m.factorial : ℂ)) else 0) := by
  rw [piK, c2_lsum_eq_sum (B := n + k + 1) (fun i hi => by
    rw [c2_sub, c2_smul, c2_smul, c2_tt_pow_mul, c2_uu_pow_mul, if_neg (by omega),
      if_neg (by omega)]; ring)]
  simp only [c2_sub, c2_smul, c2_tt_pow_mul, c2_uu_pow_mul, c2_geo, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single (k - n - 1)]
    · by_cases h : n < k ∧ (k - n) ∣ n
      · rw [if_pos h, if_pos (by omega), if_pos ⟨by omega, by
          rw [show k - n - 1 + 1 = k - n by omega]; exact h.2⟩]
        rw [show k - n - 1 + 1 = k - n by omega, mul_one]
      · rw [if_neg h]
        split_ifs with h1 h2
        · exfalso
          apply h
          refine ⟨by omega, ?_⟩
          have := h2.2
          rwa [show k - n - 1 + 1 = k - n by omega] at this
        · rw [mul_zero]
        · rw [mul_zero]
    · intro i _ hi
      split_ifs with h1 h2
      · exfalso; apply hi; omega
      · rw [mul_zero]
      · rw [mul_zero]
    · intro h
      rw [Finset.mem_range] at h
      split_ifs with h1 h2
      · exfalso; omega
      · rw [mul_zero]
      · rw [mul_zero]
  · rw [Finset.sum_eq_single (n - k - 1)]
    · by_cases h : k < n ∧ (n - k) ∣ k
      · rw [if_pos h, if_pos (by omega), if_pos ⟨by omega, by
          rw [show n - k - 1 + 1 = n - k by omega, show n - (n - k) = k by omega]; exact h.2⟩]
        rw [show n - k - 1 + 1 = n - k by omega, mul_one]
      · rw [if_neg h]
        split_ifs with h1 h2
        · exfalso
          apply h
          refine ⟨by omega, ?_⟩
          have := h2.2
          rwa [show n - k - 1 + 1 = n - k by omega, show n - (n - k) = k by omega] at this
        · rw [mul_zero]
        · rw [mul_zero]
    · intro i _ hi
      split_ifs with h1 h2
      · exfalso; apply hi; omega
      · rw [mul_zero]
      · rw [mul_zero]
    · intro h
      rw [Finset.mem_range] at h
      split_ifs with h1 h2
      · exfalso; omega
      · rw [mul_zero]
      · rw [mul_zero]

/-- Kernel parity under the swap. -/
theorem swap2_piK (m : ℕ) : swap2 (piK m) = ((-1 : ℂ) ^ (m + 1)) • piK m := by
  apply ext2
  intro n k
  rw [c2_swap2, c2_smul, c2_piK, c2_piK]
  have hsq : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by
    rw [← mul_pow]; norm_num
  by_cases h1 : n < k ∧ (k - n) ∣ n
  · have h2 : ¬(k < n ∧ (n - k) ∣ k) := fun h => by omega
    simp only [h1, h2, and_self, if_true, if_false]
    rw [neg_pow (((k - n : ℕ) : ℂ))]
    ring
  · by_cases h2 : k < n ∧ (n - k) ∣ k
    · simp only [h1, h2, and_self, if_true, if_false]
      rw [neg_pow (((n - k : ℕ) : ℂ)), pow_succ]
      linear_combination (-(((n - k : ℕ) : ℂ) ^ m / (m.factorial : ℂ))) * hsq
    · simp only [h1, h2, if_false]
      simp

/-! ## Cross-module trace cyclicity -/

theorem weightBlock_comp_cross {E F : Type u} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (A : OrdVModule W E) (B : OrdVModule W F)
    (f : F →ₗ[ℂ] E) (g : E →ₗ[ℂ] F) (α β : ℂ)
    (hf : ∀ v ∈ B.weight β, f v ∈ A.weight α) (hg : ∀ v ∈ A.weight α, g v ∈ B.weight β) :
    weightBlock A (f ∘ₗ g) α = (f.restrict hf) ∘ₗ (g.restrict hg) := by
  refine LinearMap.ext (fun v => Subtype.ext ?_)
  have hmem : f (g (v : E)) ∈ A.weight α := hf _ (hg _ v.2)
  change ((internalProjTo A.isInternal α) (f (g (v : E))) : E) = _
  rw [show ((internalProjTo A.isInternal α) (f (g (v : E))) : E) = f (g (v : E)) from
    congrArg Subtype.val (internalProjTo_coe A.isInternal α ⟨f (g (v : E)), hmem⟩)]
  rfl

theorem trace_weightBlock_cross {E F : Type u} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (A : OrdVModule W E) (B : OrdVModule W F)
    (f : F →ₗ[ℂ] E) (g : E →ₗ[ℂ] F) (α β : ℂ)
    (hf : ∀ v ∈ B.weight β, f v ∈ A.weight α) (hg : ∀ v ∈ A.weight α, g v ∈ B.weight β) :
    haveI := A.finrank α
    haveI := B.finrank β
    LinearMap.trace ℂ _ (weightBlock A (f ∘ₗ g) α) =
      LinearMap.trace ℂ _ (weightBlock B (g ∘ₗ f) β) := by
  haveI := A.finrank α
  haveI := B.finrank β
  rw [weightBlock_comp_cross A B f g α β hf hg, weightBlock_comp_cross B A g f β α hg hf,
    LinearMap.trace_comp_comm']

theorem swap2_swap2 (f : R2) : swap2 (swap2 f) = f := ext2 fun n k => by simp

/-! ## The rotated trace -/

section Rot
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

theorem tauZ_swap {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (n k : ℕ) :
    tauZ Y₂ Y₁ y x α₂ α₁ n k = tauZ Y₁ Y₂ x y α₁ α₂ k n := by
  unfold tauZ lvl gradedTraceOp
  have hf : ∀ v ∈ Q.isMod.weight (Q.h - W.centralCharge / 24 + ((n : ℤ) : ℂ) +
      W.centralCharge / 24), Y₁.val (rMode Q N α₁ n k) x v ∈
        N.isMod.weight (N.h - W.centralCharge / 24 + ((k : ℤ) : ℂ) + W.centralCharge / 24) := by
    intro v hv
    have h := FusionTop.mem_weight Y₁.property hx hv (rMode Q N α₁ n k)
    convert h using 2
    unfold rMode
    ring
  have hg : ∀ v ∈ N.isMod.weight (N.h - W.centralCharge / 24 + ((k : ℤ) : ℂ) +
      W.centralCharge / 24), Y₂.val (sMode Q N α₂ n k) y v ∈
        Q.isMod.weight (Q.h - W.centralCharge / 24 + ((n : ℤ) : ℂ) + W.centralCharge / 24) := by
    intro v hv
    have h := FusionTop.mem_weight Y₂.property hy hv (sMode Q N α₂ n k)
    convert h using 2
    unfold sMode
    ring
  have := trace_weightBlock_cross Q.isMod N.isMod (Y₂.val (sMode Q N α₂ n k) y)
    (Y₁.val (rMode Q N α₁ n k) x) _ _ hg hf
  convert this using 2

/-- The rotated trace is the swapped series. -/
theorem Phi_swap (x : P₁.carrier) (y : P₂.carrier) :
    Phi Y₂ Y₁ y x = swap2 (Phi Y₁ Y₂ x y) := by
  refine FusionTop.induction_weight P₁.isMod x (by simp) (fun a b ha hb => ?_) ?_
  · simp only [map_add, LinearMap.add_apply, ha, hb]
  · intro α₁ x hx
    refine FusionTop.induction_weight P₂.isMod y (by simp) (fun a b ha hb => ?_) ?_
    · simp only [map_add, LinearMap.add_apply, ha, hb]
    · intro α₂ y hy
      rw [Phi_homog Y₂ Y₁ hy hx, Phi_homog Y₁ Y₂ hx hy]
      apply ext2
      intro n k
      rw [c2_swap2]
      simp only [phiH, c2_mk2]
      exact tauZ_swap Y₁ Y₂ hx hy n k

theorem swap2_Phi (x : P₁.carrier) (y : P₂.carrier) :
    swap2 (Phi Y₂ Y₁ y x) = Phi Y₁ Y₂ x y := by
  rw [Phi_swap Y₁ Y₂, swap2_swap2]

end Rot

/-- **The two-point minus-two Ward identity, right slot**, in `ℂ⟦u⟧⟦t⟧`. -/
theorem ward_neg_two_phi_right (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    {b : V} {kb : ℕ} (hb : b ∈ W.grading (kb : ℤ))
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ) (hK1 : 1 ≤ K)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule b x y K) :
    Phi Y₁ Y₂ x (sqAct P₂.isMod b kb (-2) y) +
      ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
        (eis (m + 2) * Phi Y₁ Y₂ x (sqAct P₂.isMod b kb ((2 * m + 2 : ℕ) : ℤ) y)) +
      ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
          if m = 0 then eis 1 else 0) *
        Phi Y₁ Y₂ (sqAct P₁.isMod b kb (m : ℤ) x) y = 0 := by
  have hK' : TailBound P₂.isMod.toWeakModule P₁.isMod.toWeakModule b y x K :=
    fun j hj => ⟨(hK j hj).2, (hK j hj).1⟩
  have h := ward_neg_two_phi Y₂ Y₁ hb hy hx K hK1 hK'
  have h2 := congrArg swap2 h
  simp only [map_add, map_sum, map_mul, map_sub, map_zero, swap2_smul, swap2_eis, swap2_piK,
    apply_ite swap2, swap2_Phi Y₁ Y₂] at h2
  exact h2

end VOA.Huang.GenusOneWard
