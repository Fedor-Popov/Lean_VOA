import VOA.Moonshine.MoonshineCNTwistedBases
import VOA.Moonshine.MoonshineCNTwistedCombinatorics

/-!
# The twisted denominator identity for Borcherds data

Let `D` be Borcherds data with a symmetry `σ`, eigenbases `b γ` of all root spaces (eigenvalues
`μ γ i`), and suppose the power sums of the eigenvalues on the positive root spaces are given by a
coefficient family: `Σ_i μ_{γ,i}^k = c_k(γ₁ γ₂)` for `γ = (γ₁, γ₂)` in the positive cone.

In height coordinates `(γ₁, γ₁ + γ₂)` the basis of `U` (`generatorBasis`) and the basis of `𝔲⁺`
(`positiveBasis`) are graded letters (`generatorLetters`, `positiveLetters`).  The isomorphism
`T(U) ≅ U(𝔲⁺)` in word and PBW coordinates intertwines `σ` and two torus elements recording the
bidegree, so the weighted word and multiset counts agree degree by degree
(`generatorLetters_wordCount_eq`).  With the two character identities this gives
`D ũ = (1 − ũ) P̃` (`twistedDenominatorIdentity_of_eigenbasis`).
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open Module Finset

/-! ### Height coordinates and sigma-indexed letters -/

/-- Height coordinates `(m, n) ↦ (m, m + n)`. -/
def borcherdsHeightDegree (γ : ℤ × ℤ) : ℕ × ℕ := (γ.1.toNat, (γ.1 + γ.2).toNat)

theorem borcherdsHeightDegree_injOn {γ δ : ℤ × ℤ} (hγ : borcherdsPositiveCone γ)
    (hδ : borcherdsPositiveCone δ) (h : borcherdsHeightDegree γ = borcherdsHeightDegree δ) :
    γ = δ := by
  simp only [borcherdsHeightDegree, Prod.ext_iff, borcherdsPositiveCone] at *
  obtain ⟨h1, h2⟩ := h
  constructor <;> omega

theorem borcherdsStringDegree_cone (s : borcherdsStringIndex) :
    borcherdsPositiveCone (borcherdsStringDegree s) := by
  have := s.2
  simp only [borcherdsPositiveCone, borcherdsStringDegree]
  omega

/-- Letters indexed by a sigma type over an injectively graded base. -/
def sigmaGradedLetters {κ : Type*} (ι : κ → Type*) [∀ s, Finite (ι s)] (d : κ → ℕ × ℕ)
    (hd : Function.Injective d) (hpos : ∀ s, 1 ≤ (d s).1) : GradedLetters (Σ s, ι s) where
  deg x := d x.1
  deg_pos x := hpos x.1
  finite_fiber δ := by
    by_cases h : ∃ s, d s = δ
    · obtain ⟨s0, rfl⟩ := h
      refine (Set.finite_range (fun i : ι s0 => (⟨s0, i⟩ : Σ s, ι s))).subset ?_
      rintro ⟨s, i⟩ hx
      have hs : s = s0 := hd hx
      subst hs
      exact ⟨i, rfl⟩
    · convert Set.finite_empty
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hx => h ⟨x.1, hx⟩

theorem sum_sigma_fiber {κ : Type*} {ι : κ → Type*} (d : κ → ℕ × ℕ) (hd : Function.Injective d)
    (F : (Σ s, ι s) → ℂ) (s0 : κ) [Fintype (ι s0)] (S : Finset (Σ s, ι s))
    (hS : ∀ i : ι s0, (⟨s0, i⟩ : Σ s, ι s) ∈ S) :
    ∑ x ∈ S, (if d x.1 = d s0 then F x else 0) = ∑ i : ι s0, F ⟨s0, i⟩ := by
  classical
  rw [← sum_filter]
  symm
  refine sum_bij (fun i _ => ⟨s0, i⟩) (fun i _ => mem_filter.mpr ⟨hS i, rfl⟩)
    (fun i _ j _ h => sigma_mk_injective h) (fun x hx => ?_) (fun i _ => rfl)
  obtain ⟨s, i⟩ := x
  have hs : s = s0 := hd (mem_filter.mp hx).2
  subst hs
  exact ⟨i, mem_univ _, rfl⟩

/-! ### Torus characters -/

/-- `γ ↦ 2^{γ₁}`. -/
def heightCharFirst (γ : ℤ × ℤ) : ℂ := (2 : ℂ) ^ γ.1

/-- `γ ↦ 2^{γ₁ + γ₂}`. -/
def heightCharTotal (γ : ℤ × ℤ) : ℂ := (2 : ℂ) ^ (γ.1 + γ.2)

theorem heightCharFirst_add (γ δ : ℤ × ℤ) :
    heightCharFirst (γ + δ) = heightCharFirst γ * heightCharFirst δ := by
  simp [heightCharFirst, zpow_add₀ (two_ne_zero (α := ℂ))]

theorem heightCharTotal_add (γ δ : ℤ × ℤ) :
    heightCharTotal (γ + δ) = heightCharTotal γ * heightCharTotal δ := by
  simp only [heightCharTotal, Prod.fst_add, Prod.snd_add]
  rw [← zpow_add₀ (two_ne_zero (α := ℂ))]
  congr 1
  ring

theorem heightCharFirst_of_cone {γ : ℤ × ℤ} (hγ : borcherdsPositiveCone γ) :
    heightCharFirst γ = 2 ^ (borcherdsHeightDegree γ).1 := by
  simp only [heightCharFirst, borcherdsHeightDegree]
  rw [← zpow_natCast, Int.toNat_of_nonneg (by have := hγ.1; omega)]

theorem heightCharTotal_of_cone {γ : ℤ × ℤ} (hγ : borcherdsPositiveCone γ) :
    heightCharTotal γ = 2 ^ (borcherdsHeightDegree γ).2 := by
  simp only [heightCharTotal, borcherdsHeightDegree]
  rw [← zpow_natCast, Int.toNat_of_nonneg (by have := hγ.1; have := hγ.2; omega)]

theorem list_prod_two_pow {α : Type*} (w : List α) (f : α → ℕ) :
    (w.map fun x => (2 : ℂ) ^ f x).prod = 2 ^ (w.map f).sum := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih, pow_add]

theorem multiset_prod_two_pow {α : Type*} (m : Multiset α) (f : α → ℕ) :
    (m.map fun x => (2 : ℂ) ^ f x).prod = 2 ^ (m.map f).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp [ih, pow_add]

theorem two_pow_inj {a b : ℕ} : (2 : ℂ) ^ a = 2 ^ b ↔ a = b := by
  constructor
  · intro h
    have h' : ((2 ^ a : ℕ) : ℂ) = ((2 ^ b : ℕ) : ℂ) := by push_cast; exact h
    exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h')
  · rintro rfl
    rfl

namespace GradedLetters

variable {ι : Type*} (L : GradedLetters ι)

theorem listDeg_fst (w : List ι) : (L.listDeg w).1 = (w.map fun x => (L.deg x).1).sum := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

theorem listDeg_snd (w : List ι) : (L.listDeg w).2 = (w.map fun x => (L.deg x).2).sum := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

theorem msetDeg_fst (m : Multiset ι) : (L.msetDeg m).1 = (m.map fun x => (L.deg x).1).sum := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons a m ih => simp [ih]

theorem msetDeg_snd (m : Multiset ι) : (L.msetDeg m).2 = (m.map fun x => (L.deg x).2).sum := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons a m ih => simp [ih]

end GradedLetters

namespace BorcherdsData

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)
variable (ι : ℤ × ℤ → Type*) [∀ γ, Fintype (ι γ)]

/-- The graded letters of the basis of `𝔲⁺`, in height coordinates. -/
def positiveLetters : GradedLetters (Σ γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ}, ι γ.1) :=
  sigmaGradedLetters (fun γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ} => ι γ.1)
    (fun γ => borcherdsHeightDegree γ.1)
    (fun γ δ h => Subtype.ext (borcherdsHeightDegree_injOn γ.2 δ.2 h))
    (fun γ => by have := γ.2.1; simp only [borcherdsHeightDegree]; omega)

/-- The graded letters of the basis of `U`, in height coordinates. -/
def generatorLetters :
    GradedLetters (Σ s : borcherdsStringIndex, ι (borcherdsImaginaryRoot s.val.1)) :=
  sigmaGradedLetters (fun s : borcherdsStringIndex => ι (borcherdsImaginaryRoot s.val.1))
    (fun s => borcherdsHeightDegree (borcherdsStringDegree s))
    (fun s t h => borcherdsStringDegree_injective (borcherdsHeightDegree_injOn
      (borcherdsStringDegree_cone s) (borcherdsStringDegree_cone t) h))
    (fun s => by
      have := (borcherdsStringDegree_cone s).1
      simp only [borcherdsHeightDegree]
      omega)

variable (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
  (f : g) (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)
  (b : ∀ γ, Basis (ι γ) ℂ (D.weightSpace γ)) (μ : ∀ γ, ι γ → ℂ)
  {G : Type*} [Group G] (A : D.GAction G)

include he hf hef in
/-- **Degree-by-degree equality of the word and multiset counts** weighted by the eigenvalues of a
symmetry: the trace of `σ` on `T(U)` equals its trace on `U(𝔲⁺)` in every bidegree. -/
theorem generatorLetters_wordCount_eq (σ : G)
    (hb : ∀ γ i, D.weightAction A σ γ (b γ i) = μ γ i • b γ i) (γ : ℕ × ℕ) :
    (generatorLetters ι).wordCount (fun x => μ _ x.2) γ =
      (positiveLetters ι).msetCount (fun x => μ x.1.1 x.2) γ := by
  classical
  letI : LinearOrder (Σ γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ}, ι γ.1) :=
    IsWellOrder.linearOrder WellOrderingRel
  set Y := D.positiveBasis ι b
  set Z := D.generatorBasis ι b e he f hf hef
  set Ψ := wordPBWEquiv (D.positiveGeneratorSpace e)
    (D.positiveTensorGeneratorToEnveloping_bijective e f he hf hef) Y Z
  let νs : Fin 3 → (Σ s : borcherdsStringIndex, ι (borcherdsImaginaryRoot s.val.1)) → ℂ :=
    ![fun x => μ _ x.2, fun x => heightCharFirst (borcherdsStringDegree x.1),
      fun x => heightCharTotal (borcherdsStringDegree x.1)]
  let κs : Fin 3 → (Σ γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ}, ι γ.1) → ℂ :=
    ![fun x => μ x.1.1 x.2, fun x => heightCharFirst x.1.1, fun x => heightCharTotal x.1.1]
  have hκ : ∀ j v, Ψ (finsuppDiag (fun w => (w.map (νs j)).prod) v) =
      finsuppDiag (fun m => (m.map (κs j)).prod) (Ψ v) := by
    intro j v
    fin_cases j
    · exact wordPBWEquiv_diag _ _ Y Z (D.positivePartAction A σ)
        (D.positiveGenerator_action_mem e he A σ) _ _
        (D.positivePartAction_positiveBasis ι b A μ σ hb)
        (D.positivePartAction_generatorBasis ι b e he f hf hef A μ σ hb) v
    · exact wordPBWEquiv_diag _ _ Y Z (D.positiveTorus heightCharFirst heightCharFirst_add)
        (D.positiveTorus_generator_mem e he _ _) _ _
        (D.positiveTorus_positiveBasis ι b _ _)
        (D.positiveTorus_generatorBasis ι b e he f hf hef _ _) v
    · exact wordPBWEquiv_diag _ _ Y Z (D.positiveTorus heightCharTotal heightCharTotal_add)
        (D.positiveTorus_generator_mem e he _ _) _ _
        (D.positiveTorus_positiveBasis ι b _ _)
        (D.positiveTorus_generatorBasis ι b e he f hf hef _ _) v
  have hfirstU : ∀ w : List (Σ s : borcherdsStringIndex, ι (borcherdsImaginaryRoot s.val.1)),
      (w.map (νs 1)).prod = 2 ^ ((generatorLetters ι).listDeg w).1 := by
    intro w
    rw [GradedLetters.listDeg_fst, ← list_prod_two_pow]
    exact congrArg List.prod (List.map_congr_left fun x _ =>
      heightCharFirst_of_cone (borcherdsStringDegree_cone x.1))
  have hsecondU : ∀ w : List (Σ s : borcherdsStringIndex, ι (borcherdsImaginaryRoot s.val.1)),
      (w.map (νs 2)).prod = 2 ^ ((generatorLetters ι).listDeg w).2 := by
    intro w
    rw [GradedLetters.listDeg_snd, ← list_prod_two_pow]
    exact congrArg List.prod (List.map_congr_left fun x _ =>
      heightCharTotal_of_cone (borcherdsStringDegree_cone x.1))
  have hfirstN : ∀ m : Multiset (Σ γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ}, ι γ.1),
      (m.map (κs 1)).prod = 2 ^ ((positiveLetters ι).msetDeg m).1 := by
    intro m
    rw [GradedLetters.msetDeg_fst, ← multiset_prod_two_pow]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => heightCharFirst_of_cone x.1.2)
  have hsecondN : ∀ m : Multiset (Σ γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ}, ι γ.1),
      (m.map (κs 2)).prod = 2 ^ ((positiveLetters ι).msetDeg m).2 := by
    intro m
    rw [GradedLetters.msetDeg_snd, ← multiset_prod_two_pow]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => heightCharTotal_of_cone x.1.2)
  have h := sum_eq_sum_of_diag_equiv Ψ (fun j w => (w.map (νs j)).prod)
    (fun j m => (m.map (κs j)).prod) hκ
    (fun σ' => σ' 1 = 2 ^ γ.1 ∧ σ' 2 = 2 ^ γ.2)
    ((generatorLetters ι).wordFiber γ) ((positiveLetters ι).msetFiber γ)
    (fun w => by
      rw [GradedLetters.mem_wordFiber]
      change _ ↔ (w.map (νs 1)).prod = _ ∧ (w.map (νs 2)).prod = _
      rw [hfirstU, hsecondU, two_pow_inj, two_pow_inj, Prod.ext_iff])
    (fun m => by
      rw [GradedLetters.mem_msetFiber]
      change _ ↔ (m.map (κs 1)).prod = _ ∧ (m.map (κs 2)).prod = _
      rw [hfirstN, hsecondN, two_pow_inj, two_pow_inj, Prod.ext_iff]) 0
  exact h

include he hf hef in
/-- **The twisted denominator identity** for Borcherds data with a symmetry diagonal in the bases
`b γ`, when the power sums of its eigenvalues on the positive root spaces are `c_k(γ₁ γ₂)`. -/
theorem twistedDenominatorIdentity_of_eigenbasis (σ : G)
    (hb : ∀ γ i, D.weightAction A σ γ (b γ i) = μ γ i • b γ i) (c : ℕ → ℕ → ℂ)
    (htr : ∀ k : ℕ, 1 ≤ k → ∀ γ : ℤ × ℤ, borcherdsPositiveCone γ →
      ∑ i, μ γ i ^ k = c k (γ.1 * γ.2).toNat) :
    TwistedDenominatorIdentity c := by
  classical
  set L1 := generatorLetters ι
  set L2 := positiveLetters ι
  set μU : (Σ s : borcherdsStringIndex, ι (borcherdsImaginaryRoot s.val.1)) → ℂ :=
    fun x => μ _ x.2
  set μN : (Σ γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ}, ι γ.1) → ℂ := fun x => μ x.1.1 x.2
  have hWM : L2.msetSeries μN = L1.wordSeries μU := by
    unfold GradedLetters.msetSeries GradedLetters.wordSeries
    congr 1
    funext γ
    exact (D.generatorLetters_wordCount_eq ι e he f hf hef b μ A σ hb γ).symm
  have h1 : L2.msetSeries μN * (1 - L1.letterSeries μU) = 1 := by
    rw [hWM]
    exact L1.wordSeries_mul_one_sub_letterSeries μU
  have h3 := eulerDeriv_eq_of_inverse h1 (L2.eulerDeriv_msetSeries μN)
  -- the letter series is `ũ`
  have hU : L1.letterSeries μU = twistedUnitSeries (c 1) := by
    refine bigradedSeries_ext fun A N => ?_
    rw [GradedLetters.letterSeries, coeff_bigradedSeries]
    simp only [twistedUnitSeries, PowerSeries.coeff_mk]
    unfold GradedLetters.letterCount
    by_cases hAN : 1 ≤ A ∧ A < N
    · rw [if_pos hAN]
      let s0 : borcherdsStringIndex :=
        (⟨((N : ℤ) - 1, A - 1), by dsimp only; omega, by dsimp only; omega⟩ :
          {jk : ℤ × ℕ // 1 ≤ jk.1 ∧ (jk.2 : ℤ) < jk.1})
      have hd : (A, N) = borcherdsHeightDegree (borcherdsStringDegree s0) := by
        simp only [borcherdsHeightDegree, borcherdsStringDegree, s0, Prod.ext_iff]
        omega
      rw [hd]
      have hfib := sum_sigma_fiber (ι := fun s : borcherdsStringIndex =>
        ι (borcherdsImaginaryRoot s.val.1))
        (fun s => borcherdsHeightDegree (borcherdsStringDegree s))
        (fun s t h => borcherdsStringDegree_injective (borcherdsHeightDegree_injOn
          (borcherdsStringDegree_cone s) (borcherdsStringDegree_cone t) h)) μU s0
        (L1.lowerLetters (borcherdsHeightDegree (borcherdsStringDegree s0)))
        (fun i => L1.mem_lowerLetters.mpr ⟨le_rfl, le_rfl⟩)
      refine hfib.trans ?_
      have ht := htr 1 le_rfl (borcherdsImaginaryRoot s0.val.1)
        (by simp only [borcherdsPositiveCone, borcherdsImaginaryRoot, s0]; omega)
      simp only [pow_one] at ht
      refine ht.trans ?_
      congr 1
      simp only [borcherdsImaginaryRoot, s0, one_mul]
      omega
    · rw [if_neg hAN]
      refine sum_eq_zero fun x _ => if_neg fun hx => hAN ?_
      have hs := (borcherdsStringDegree_cone x.1)
      have hx2 := x.1.2
      change borcherdsHeightDegree (borcherdsStringDegree x.1) = (A, N) at hx
      simp only [borcherdsHeightDegree, borcherdsStringDegree, Prod.ext_iff] at hx
      omega
  -- the power-sum series is `P̃`
  have hP : L2.powerSumSeries μN = twistedPowerSum c := by
    refine bigradedSeries_ext fun A N => ?_
    rw [GradedLetters.powerSumSeries, coeff_bigradedSeries]
    simp only [twistedPowerSum, PowerSeries.coeff_mk]
    unfold GradedLetters.powerSumCount
    rw [sum_product_right]
    have hdiv : A.divisors = (Icc 1 A).filter (· ∣ A) := by
      ext k
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨hk, hA⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hk (Nat.pos_of_ne_zero hA), Nat.le_of_dvd
          (Nat.pos_of_ne_zero hA) hk⟩, hk⟩
      · rintro ⟨⟨h1, h2⟩, hk⟩
        exact ⟨hk, by omega⟩
    rw [hdiv, sum_filter]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Icc] at hk
    by_cases hcond : k ∣ A ∧ k ∣ N ∧ A < N
    · obtain ⟨hkA, hkN, hAN⟩ := hcond
      rw [if_pos hkA, if_pos ⟨hkN, hAN⟩]
      obtain ⟨a, rfl⟩ := hkA
      obtain ⟨n, rfl⟩ := hkN
      have hk0 : 0 < k := by omega
      have ha1 : 1 ≤ a := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; omega)
      have han : a < n := Nat.lt_of_mul_lt_mul_left hAN
      rw [Nat.mul_div_cancel_left a hk0, ← mul_tsub, Nat.mul_div_cancel_left _ hk0]
      let γ0 : ℤ × ℤ := ((a : ℤ), ((n - a : ℕ) : ℤ))
      have hγ0 : borcherdsPositiveCone γ0 := by
        simp only [borcherdsPositiveCone, γ0]
        omega
      let s0 : {γ : ℤ × ℤ // borcherdsPositiveCone γ} := ⟨γ0, hγ0⟩
      have hd0 : borcherdsHeightDegree s0.1 = (a, n) := by
        simp only [borcherdsHeightDegree, s0, γ0, Prod.ext_iff]
        omega
      have hterm : ∀ x ∈ L2.lowerLetters (k * a, k * n),
          (if k • L2.deg x = (k * a, k * n) then ((L2.deg x).1 : ℂ) * μN x ^ k else 0) =
            if borcherdsHeightDegree x.1.1 = borcherdsHeightDegree s0.1 then
              (a : ℂ) * μN x ^ k else 0 := by
        intro x _
        change (if k • borcherdsHeightDegree x.1.1 = (k * a, k * n) then
          ((borcherdsHeightDegree x.1.1).1 : ℂ) * μN x ^ k else 0) = _
        rw [hd0]
        by_cases hx : borcherdsHeightDegree x.1.1 = (a, n)
        · rw [if_pos hx, hx, if_pos]
          simp [Prod.smul_mk]
        · rw [if_neg hx, if_neg]
          intro h
          apply hx
          simp only [Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h ⊢
          exact ⟨Nat.eq_of_mul_eq_mul_left hk0 h.1, Nat.eq_of_mul_eq_mul_left hk0 h.2⟩
      rw [sum_congr rfl hterm]
      have hfib := sum_sigma_fiber (ι := fun γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ} => ι γ.1)
        (fun γ => borcherdsHeightDegree γ.1)
        (fun γ δ h => Subtype.ext (borcherdsHeightDegree_injOn γ.2 δ.2 h))
        (fun x => (a : ℂ) * μN x ^ k) s0 (L2.lowerLetters (k * a, k * n)) (fun i => by
          rw [L2.mem_lowerLetters]
          change (borcherdsHeightDegree s0.1).1 ≤ k * a ∧ (borcherdsHeightDegree s0.1).2 ≤ k * n
          rw [hd0]
          exact ⟨Nat.le_mul_of_pos_left _ hk0, Nat.le_mul_of_pos_left _ hk0⟩)
      rw [hfib, ← mul_sum]
      congr 1
      refine (htr k (by omega) γ0 hγ0).trans ?_
      exact congrArg (c k) (by
        change ((a : ℤ) * ((n - a : ℕ) : ℤ)).toNat = a * (n - a)
        rw [← Nat.cast_mul, Int.toNat_natCast])
    · have hR : (if k ∣ A then (if k ∣ N ∧ A < N then
          ((A / k : ℕ) : ℂ) * c k (A / k * ((N - A) / k)) else 0) else 0) = 0 := by
        split_ifs with h1 h2
        · exact absurd ⟨h1, h2⟩ hcond
        · rfl
        · rfl
      rw [hR]
      refine sum_eq_zero fun x _ => if_neg fun h => hcond ?_
      change k • borcherdsHeightDegree x.1.1 = (A, N) at h
      have hc := x.1.2
      simp only [borcherdsPositiveCone] at hc
      simp only [Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        borcherdsHeightDegree] at h
      have hlt : (x.1.1.1).toNat < (x.1.1.1 + x.1.1.2).toNat := by omega
      refine ⟨Dvd.intro _ h.1, Dvd.intro _ h.2, ?_⟩
      rw [← h.1, ← h.2]
      exact Nat.mul_lt_mul_of_pos_left hlt (by omega)
  rw [hU, hP] at h3
  exact h3

end BorcherdsData

end VOA.Moonshine.ConwayNorton
