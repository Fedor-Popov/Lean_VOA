import VOA.Classification.COne.PlusRat4Transfer

/-! # The direct sum of two weak modules, and degree-zero words on top vectors (general VOA)

* `prodModule A B : WeakModule W (M × N)`, modes act componentwise.
* `word_zero_scalar`: if `x ∈ A` and `e ∈ B` are top vectors on which zero modes act through the
  same function `χ` (and `L(0) = h` on both), then every homogeneous mode word of total degree `0`
  acts on `x` and on `e` by the **same** scalar.  Proof: in `A × B`, `(x, e)` is such a top vector,
  and Li's single-mode spanning (`degreeSpan_le`) puts every degree-zero word on `(x, e)` into the
  span of the zero modes, i.e. into `ℂ (x, e)`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VertexOperatorAlgebra PlusSplitting PlusRatTelescope VOA.Huang.LogRemovalAdmissible
  ABDWeakAdmissible PlusRatSign PlusRat3
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {W : VertexOperatorAlgebra V}

/-! ## §1  Finite sums of pairs -/

theorem finite_support_of_vanish {P : Type*} [AddCommMonoid P] (f : ℤ → P) (K : ℤ)
    (h1 : ∀ i, i < 0 → f i = 0) (h2 : ∀ i, K ≤ i → f i = 0) : (Function.support f).Finite := by
  apply (Finset.Ico 0 K).finite_toSet.subset
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Finset.coe_Ico, Set.mem_Ico]
  constructor
  · by_contra h; exact hi (h1 i (by omega))
  · by_contra h; exact hi (h2 i (by omega))

theorem finsum_pair {P Q : Type*} [AddCommMonoid P] [AddCommMonoid Q] (f : ℤ → P) (g : ℤ → Q)
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    ∑ᶠ i, (f i, g i) = (∑ᶠ i, f i, ∑ᶠ i, g i) := by
  classical
  set s := hf.toFinset ∪ hg.toFinset
  have hsf : Function.support f ⊆ s := fun i hi => by
    simp only [s, Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inl hi
  have hsg : Function.support g ⊆ s := fun i hi => by
    simp only [s, Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hi
  have hsp : Function.support (fun i => (f i, g i)) ⊆ s := by
    intro i hi
    rw [Function.mem_support] at hi
    by_cases h : f i = 0
    · have : g i ≠ 0 := fun h' => hi (by rw [h, h']; rfl)
      exact hsg this
    · exact hsf h
  rw [finsum_eq_sum_of_support_subset _ hsp, finsum_eq_sum_of_support_subset _ hsf,
    finsum_eq_sum_of_support_subset _ hsg]
  ext
  · rw [Prod.fst_sum]
  · rw [Prod.snd_sum]

/-! ## §2  The product module -/

/-- The state–field map of `A × B`. -/
def prodYM (A : WeakModule W M) (B : WeakModule W N) : V →ₗ[ℂ] (Module.End ℂ (M × N))⟦z^±⟧ where
  toFun u := fun k => (A.YM u k).prodMap (B.YM u k)
  map_add' u v := by
    funext k
    refine LinearMap.ext fun q => ?_
    change ((A.YM (u + v)) k q.1, (B.YM (u + v)) k q.2) =
      ((A.YM u) k q.1, (B.YM u) k q.2) + ((A.YM v) k q.1, (B.YM v) k q.2)
    rw [map_add, map_add]
    rfl
  map_smul' c u := by
    funext k
    refine LinearMap.ext fun q => ?_
    change ((A.YM (c • u)) k q.1, (B.YM (c • u)) k q.2) = c • ((A.YM u) k q.1, (B.YM u) k q.2)
    rw [map_smul, map_smul]
    rfl

theorem prodYM_mode (A : WeakModule W M) (B : WeakModule W N) (u : V) (n : ℤ) (p : M × N) :
    mode (prodYM A B u) n p = (mode (A.YM u) n p.1, mode (B.YM u) n p.2) := rfl

/-- The direct sum of two weak modules. -/
def prodModule (A : WeakModule W M) (B : WeakModule W N) : WeakModule W (M × N) where
  YM := prodYM A B
  vacuum_YM := by
    funext k
    refine LinearMap.ext fun q => ?_
    change ((A.YM W.vacuum) k q.1, (B.YM W.vacuum) k q.2) =
      ((1 : FormalDist (Module.End ℂ (M × N))) k) q
    rw [A.vacuum_YM, B.vacuum_YM]
    simp only [FormalDist.one_apply]
    split_ifs <;> rfl
  truncation u p := by
    obtain ⟨N1, h1⟩ := A.truncation u p.1
    obtain ⟨N2, h2⟩ := B.truncation u p.2
    refine ⟨max N1 N2, fun n hn => ?_⟩
    rw [prodYM_mode, h1 n (le_of_max_le_left hn), h2 n (le_of_max_le_right hn)]
    rfl
  jacobi u v p ℓ m n := by
    simp only [prodYM_mode]
    obtain ⟨Nv1, hv1⟩ := A.truncation v p.1
    obtain ⟨Nu1, hu1⟩ := A.truncation u p.1
    obtain ⟨Nv2, hv2⟩ := B.truncation v p.2
    obtain ⟨Nu2, hu2⟩ := B.truncation u p.2
    obtain ⟨Nw, hw⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
    have hL : ∀ (P : Type u) [AddCommGroup P] [Module ℂ P] (C : WeakModule W P) (y : P) (Nv Nu : ℤ),
        (∀ k, Nv ≤ k → mode (C.YM v) k y = 0) → (∀ k, Nu ≤ k → mode (C.YM u) k y = 0) →
        (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
          (mode (C.YM u) (ℓ + m - i) (mode (C.YM v) (n + i) y)
            - negOnePow ℓ • mode (C.YM v) (ℓ + n - i) (mode (C.YM u) (m + i) y))).Finite := by
      intro P _ _ C y Nv Nu hv hu
      apply finite_support_of_vanish _ (max (Nv - n) (Nu - m))
      · intro i hi; rw [cbz_apply_neg _ hi, mul_zero, zero_smul]
      · intro i hi
        rw [hv (n + i) (by omega), hu (m + i) (by omega), map_zero, map_zero, smul_zero, sub_zero,
          smul_zero]
    have hR : ∀ (P : Type u) [AddCommGroup P] [Module ℂ P] (C : WeakModule W P) (y : P),
        (Function.support fun i : ℤ =>
          cbz m i • mode (C.YM (W.smul u (ℓ + i) v)) (m + n - i) y).Finite := by
      intro P _ _ C y
      apply finite_support_of_vanish _ (Nw - ℓ)
      · intro i hi; rw [cbz_apply_neg _ hi, zero_smul]
      · intro i hi
        rw [hw (ℓ + i) (by omega), map_zero, mode_zero, LinearMap.zero_apply, smul_zero]
    have e1 := A.jacobi u v p.1 ℓ m n
    have e2 := B.jacobi u v p.2 ℓ m n
    have hLHS : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        ((mode (A.YM u) (ℓ + m - i) (mode (A.YM v) (n + i) p.1),
            mode (B.YM u) (ℓ + m - i) (mode (B.YM v) (n + i) p.2)) -
          negOnePow ℓ • (mode (A.YM v) (ℓ + n - i) (mode (A.YM u) (m + i) p.1),
            mode (B.YM v) (ℓ + n - i) (mode (B.YM u) (m + i) p.2)))) =
        (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (mode (A.YM u) (ℓ + m - i) (mode (A.YM v) (n + i) p.1)
            - negOnePow ℓ • mode (A.YM v) (ℓ + n - i) (mode (A.YM u) (m + i) p.1)),
         ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (mode (B.YM u) (ℓ + m - i) (mode (B.YM v) (n + i) p.2)
            - negOnePow ℓ • mode (B.YM v) (ℓ + n - i) (mode (B.YM u) (m + i) p.2))) := by
      rw [← finsum_pair _ _ (hL M A p.1 Nv1 Nu1 hv1 hu1) (hL N B p.2 Nv2 Nu2 hv2 hu2)]
      rfl
    have hRHS : (∑ᶠ i : ℤ, cbz m i •
        (mode (A.YM (W.smul u (ℓ + i) v)) (m + n - i) p.1,
          mode (B.YM (W.smul u (ℓ + i) v)) (m + n - i) p.2)) =
        (∑ᶠ i : ℤ, cbz m i • mode (A.YM (W.smul u (ℓ + i) v)) (m + n - i) p.1,
         ∑ᶠ i : ℤ, cbz m i • mode (B.YM (W.smul u (ℓ + i) v)) (m + n - i) p.2) := by
      rw [← finsum_pair _ _ (hR M A p.1) (hR N B p.2)]
      rfl
    change (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        ((mode (A.YM u) (ℓ + m - i) (mode (A.YM v) (n + i) p.1),
            mode (B.YM u) (ℓ + m - i) (mode (B.YM v) (n + i) p.2)) -
          negOnePow ℓ • (mode (A.YM v) (ℓ + n - i) (mode (A.YM u) (m + i) p.1),
            mode (B.YM v) (ℓ + n - i) (mode (B.YM u) (m + i) p.2)))) =
      (∑ᶠ i : ℤ, cbz m i •
        (mode (A.YM (W.smul u (ℓ + i) v)) (m + n - i) p.1,
          mode (B.YM (W.smul u (ℓ + i) v)) (m + n - i) p.2))
    rw [hLHS, hRHS, e1, e2]

theorem prod_mode (A : WeakModule W M) (B : WeakModule W N) (u : V) (n : ℤ) (x : M) (y : N) :
    mode ((prodModule A B).YM u) n (x, y) = (mode (A.YM u) n x, mode (B.YM u) n y) := rfl

theorem prod_word (A : WeakModule W M) (B : WeakModule W N) (x : M) (y : N) :
    ∀ l : List (HomogeneousLetter W),
      homogeneousWord (prodModule A B) l (x, y) = (homogeneousWord A l x, homogeneousWord B l y)
  | [] => rfl
  | a :: l => by
    simp only [homogeneousWord, LinearMap.comp_apply]
    rw [prod_word A B x y l, prod_mode]

theorem prod_L0 (A : WeakModule W M) (B : WeakModule W N) (x : M) (y : N) :
    L0 (prodModule A B) (x, y) = (L0 A x, L0 B y) := rfl

theorem prod_Omega (A : WeakModule W M) (B : WeakModule W N) {x : M} {y : N}
    (hx : x ∈ Omega A) (hy : y ∈ Omega B) : (x, y) ∈ Omega (prodModule A B) := by
  intro β v hv n hn
  rw [prod_mode, hx β v hv n hn, hy β v hv n hn]
  rfl

/-! ## §3  Degree-zero words act by the same scalar -/

/-- **Degree-zero words on two top vectors with the same zero-mode character.** -/
theorem word_zero_scalar (A : WeakModule W M) (B : WeakModule W N) (χ : VOA.A W → ℂ) {h : ℂ}
    {x : M} {e : N} (hx : x ∈ Omega A) (he : e ∈ Omega B)
    (hχx : ∀ r, topEvaluation A x hx r = χ r • x) (hχe : ∀ r, topEvaluation B e he r = χ r • e)
    (hxL : L0 A x = h • x) (heL : L0 B e = h • e) (l : List (HomogeneousLetter W))
    (hl : homogeneousDegree l = 0) :
    ∃ c : ℂ, homogeneousWord A l x = c • x ∧ homogeneousWord B l e = c • e := by
  set C := prodModule A B
  have hzL : L0 C (x, e) = h • (x, e) := by rw [prod_L0, hxL, heL]; rfl
  have hw : homogeneousWord C l (x, e) ∈ homogeneousDegreeSpan C (x, e) 0 :=
    Submodule.subset_span ⟨l, hl, rfl⟩
  have hD := degreeSpan_le C hzL 0 hw
  have hline : degSpan C (x, e) 0 ≤ Submodule.span ℂ {(x, e)} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨β, a, ha, rfl⟩
    have h1 := hχx (VOA.mk W a)
    have h2 := hχe (VOA.mk W a)
    rw [topEvaluation_mk, oLevW_homogeneous A 0 ha, add_zero] at h1
    rw [topEvaluation_mk, oLevW_homogeneous B 0 ha, add_zero] at h2
    rw [show β - 1 - 0 = β - 1 by ring, prod_mode, h1, h2]
    exact Submodule.mem_span_singleton.mpr ⟨χ (VOA.mk W a), rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hline hD)
  rw [prod_word] at hc
  exact ⟨c, (congrArg Prod.fst hc).symm, (congrArg Prod.snd hc).symm⟩

end VOA.Classification.COne.PlusRat4
