import VOA.Huang.PentagonCloseUniq
import VOA.Huang.PentagonCloseVacuum
import VOA.Huang.FivePointSepMain

/-! # Left five-point faithfulness

The left five-point evaluation is injective. Fixing the outer coordinate `s`,
the left five-point function is the generalized power series in `r` whose
coefficients are four-point iterate evaluations of the root intertwiner
`𝒴_{(XY)Z,T} ∘ k` on the homogeneous vectors `𝒴_{XY}(α+β-w-1) x y`.
Uniqueness of generalized power series (`gps_coeff_zero`) kills each
coefficient; these vectors span every weight space of `X ⊠ Y`, so all iterate
evaluations of the root vanish; ordinary four-point faithfulness and the
universal property of `(X ⊠ Y) ⊠ Z` then give `k = 0`.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff VOA.Huang.PentagonClose
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W)

/-- Replace the first test vector by another of the same weight. -/
def FourPointTest.withX {A B C D : Ordinary W} (d : FourPointTest A B C D) (u : A.carrier)
    (hu : u ∈ A.isMod.weight d.α) : FourPointTest A B C D :=
  { d with x := u, hx := hu }

variable {A B C D : Ordinary W}

theorem iterateEvaluation_withX_add (hs : OrdinaryFourPointSummability F)
    (I : IterateSpace F A B C D) (d : FourPointTest A B C D) {u u' : A.carrier}
    (hu : u ∈ A.isMod.weight d.α) (hu' : u' ∈ A.isMod.weight d.α) :
    iterateEvaluation F I (d.withX (u + u') (Submodule.add_mem _ hu hu')) =
      iterateEvaluation F I (d.withX u hu) + iterateEvaluation F I (d.withX u' hu') := by
  rw [iterateEvaluation, iterateEvaluation, iterateEvaluation,
    ← ((hs A B C D (d.withX u hu)).1 I).tsum_add ((hs A B C D (d.withX u' hu')).1 I)]
  apply tsum_congr
  intro w
  simp only [iterateWeightTerm, FourPointTest.withX, map_add, LinearMap.add_apply, add_mul]

theorem iterateEvaluation_withX_smul (I : IterateSpace F A B C D) (d : FourPointTest A B C D)
    (c : ℂ) {u : A.carrier} (hu : u ∈ A.isMod.weight d.α) :
    iterateEvaluation F I (d.withX (c • u) (Submodule.smul_mem _ c hu)) =
      c * iterateEvaluation F I (d.withX u hu) := by
  rw [iterateEvaluation, iterateEvaluation, ← tsum_mul_left]
  apply tsum_congr
  intro w
  simp only [iterateWeightTerm, FourPointTest.withX, map_smul, LinearMap.smul_apply,
    smul_eq_mul, mul_assoc]

theorem iterateEvaluation_withX_zero (I : IterateSpace F A B C D) (d : FourPointTest A B C D) :
    iterateEvaluation F I (d.withX 0 (Submodule.zero_mem _)) = 0 := by
  rw [iterateEvaluation]
  convert tsum_zero with w
  simp only [iterateWeightTerm, FourPointTest.withX, map_zero, LinearMap.zero_apply, zero_mul]

/-- The iterate evaluation as a linear functional of the first test vector,
through the projection to the test weight. -/
def iterateFirstFunctional (hs : OrdinaryFourPointSummability F)
    (I : IterateSpace F A B C D) (d : FourPointTest A B C D) : A.carrier →ₗ[ℂ] ℂ where
  toFun u := iterateEvaluation F I
    (d.withX (internalProjTo A.isMod.isInternal d.α u : A.carrier)
      (internalProjTo A.isMod.isInternal d.α u).property)
  map_add' u u' := by
    simp only [map_add, Submodule.coe_add]
    exact iterateEvaluation_withX_add F hs I d _ _
  map_smul' c u := by
    simp only [map_smul, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    exact iterateEvaluation_withX_smul F I d c _


theorem product_mode_mem {X Y : Ordinary W} (P : Product X.isMod Y.isMod)
    {α β : ℂ} {x : X.carrier} {y : Y.carrier}
    (hx : x ∈ X.isMod.weight α) (hy : y ∈ Y.isMod.weight β) (w : ℂ) :
    P.intertwiner.val (α + β - w - 1) x y ∈ P.isMod.weight w := by
  have h := FusionTop.mem_weight P.intertwiner.property hx hy (α + β - w - 1)
  convert h using 2
  ring

variable {X Y Z T U : Ordinary W}

/-- Step A: vanishing of the left five-point function kills the iterate evaluations
of the root intertwiner on the vectors `𝒴_{XY}(α+β-w-1) x y`. -/
theorem left_root_iterate_zero (hs5 : FivePointSummability F)
    (hspec : ∃ S : Finset ℂ, ∀ w, (tensorObj F X Y).isMod.weight w ≠ ⊥ →
      ∃ h ∈ S, ∃ n : ℕ, w = h + n)
    (k : fiveObj F X Y Z T .left ⟶ U) (hk : ∀ d, fivePointEvaluation F .left k d = 0)
    (d' : FourPointTest (tensorObj F X Y) Z T U) {α β : ℂ} {x : X.carrier} {y : Y.carrier}
    (hx : x ∈ X.isMod.weight α) (hy : y ∈ Y.isMod.weight β) :
    iterateEvaluation F
      (postcompose (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner U.isMod k)
      (d'.withX ((F X Y).intertwiner.val (α + β - d'.α - 1) x y)
        (product_mode_mem (F X Y) hx hy d'.α)) = 0 := by
  obtain ⟨S, hS⟩ := hspec
  set s : ℝ := d'.coordinate with hs
  let K := postcompose (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner U.isMod k
  let u : ℂ → (tensorObj F X Y).carrier := fun w => (F X Y).intertwiner.val (α + β - w - 1) x y
  have hu (w : ℂ) : u w ∈ (tensorObj F X Y).isMod.weight w := product_mode_mem (F X Y) hx hy w
  let dd : ℂ → FourPointTest (tensorObj F X Y) Z T U := fun w =>
    { d' with α := w, x := u w, hx := hu w }
  let a : ℂ → ℂ := fun w => iterateEvaluation F K (dd w)
  set R : ℝ := min s (1 - s) with hRdef
  have hR : 0 < R := lt_min d'.positive (by linarith [d'.less_one])
  let d5 : ∀ r : ℝ, 0 < r → r < R → FivePointTest X Y Z T U := fun r h0 h1 =>
    { α := α, β := β, γ := d'.β, δ := d'.γ, ε := d'.δ, x := x, y := y, z := d'.y, t := d'.z
      functional := d'.functional, hx := hx, hy := hy, hz := d'.hy, ht := d'.hz
      supported := d'.supported, s := s, r := r, positive := h0
      smaller := lt_of_lt_of_le h1 (min_le_left _ _)
      sum_lt := by have := lt_of_lt_of_le h1 (min_le_right _ _); linarith }
  have hterm (r : ℝ) (h0 : 0 < r) (h1 : r < R) (w v : ℂ) :
      fivePointTerm F .left k (d5 r h0 h1) (w, v) =
        iterateWeightTerm F K (dd w) v * (r : ℂ) ^ (w - (α + β)) := by
    simp only [fivePointTerm, fivePointVector, fivePointFactor, iterateWeightTerm, d5, dd, u]
    rw [show w - (α + β) = w - α - β by ring, mul_assoc, mul_comm ((r : ℂ) ^ (w - α - β))]
    rfl
  have hsumw (r : ℝ) (h0 : 0 < r) (h1 : r < R) :
      Summable (fun w => a w * (r : ℂ) ^ (w - (α + β))) := by
    have := (hs5 X Y Z T U .left k (d5 r h0 h1)).prod
    refine this.congr (fun w => ?_)
    simp_rw [hterm r h0 h1]
    rw [tsum_mul_right]
    rfl
  have hzero (r : ℝ) (h0 : 0 < r) (h1 : r < R) :
      ∑' w, a w * (r : ℂ) ^ (w - (α + β)) = 0 := by
    have := hk (d5 r h0 h1)
    rw [fivePointEvaluation_fubini F .left k _ (hs5 X Y Z T U .left k (d5 r h0 h1))] at this
    simp_rw [hterm r h0 h1, tsum_mul_right] at this
    exact this
  have hsupp (w : ℂ) (hw : a w ≠ 0) : ∃ h ∈ S, ∃ n : ℕ, w = h + n := by
    apply hS
    intro hb
    apply hw
    have h0 : u w = 0 := by
      have := hu w
      rw [hb, Submodule.mem_bot] at this
      exact this
    have he : dd w = (dd w).withX 0 (Submodule.zero_mem _) := by
      simp only [dd, FourPointTest.withX, h0]
    change iterateEvaluation F K (dd w) = 0
    rw [he]
    exact iterateEvaluation_withX_zero F K (dd w)
  exact gps_coeff_zero S (α + β) a hsupp hR hsumw hzero d'.α


theorem FourPointTest.withX_congr {A B C D : Ordinary W} (d : FourPointTest A B C D)
    {u u' : A.carrier} (h : u = u') (hu : u ∈ A.isMod.weight d.α)
    (hu' : u' ∈ A.isMod.weight d.α) : d.withX u hu = d.withX u' hu' := by
  subst h; rfl

/-- Step B: all iterate evaluations of the root intertwiner vanish. -/
theorem left_root_iterate_zero_all (hs4 : OrdinaryFourPointSummability F)
    (hs5 : FivePointSummability F)
    (hspec : ∃ S : Finset ℂ, ∀ w, (tensorObj F X Y).isMod.weight w ≠ ⊥ →
      ∃ h ∈ S, ∃ n : ℕ, w = h + n)
    (k : fiveObj F X Y Z T .left ⟶ U) (hk : ∀ d, fivePointEvaluation F .left k d = 0)
    (d' : FourPointTest (tensorObj F X Y) Z T U) :
    iterateEvaluation F
      (postcompose (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner U.isMod k) d' = 0 := by
  let K := postcompose (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner U.isMod k
  let Λ := iterateFirstFunctional F hs4 K d'
  have hΛ : Λ = 0 := by
    apply tensor_linear_ext (F X Y)
    intro p x y
    refine ordinary_eq_of_homog X Y (N := ℂ) (fun x y => Λ ((F X Y).intertwiner.val p x y))
      (fun x y => (0 : (tensorObj F X Y).carrier →ₗ[ℂ] ℂ) ((F X Y).intertwiner.val p x y))
      ?_ ?_ ?_ ?_ ?_ x y
    · intro x x' y; simp only [map_add, LinearMap.add_apply]; erw [map_add]
    · intro x y y'; simp only [map_add]; erw [map_add]
    · intro x x' y; simp
    · intro x y y'; simp
    intro α β x y hx hy
    simp only [LinearMap.zero_apply]
    have hm := FusionTop.mem_weight (F X Y).intertwiner.property hx hy p
    by_cases hw : α + β - p - 1 = d'.α
    · obtain rfl : p = α + β - d'.α - 1 := by linear_combination -hw
      change iterateEvaluation F K (d'.withX _ _) = 0
      rw [FourPointTest.withX_congr d' (internalProjTo_coe_mem (tensorObj F X Y).isMod
        (product_mode_mem (F X Y) hx hy d'.α)) _ (product_mode_mem (F X Y) hx hy d'.α)]
      exact left_root_iterate_zero F hs5 hspec k hk d' hx hy
    · change iterateEvaluation F K (d'.withX _ _) = 0
      have h0 : ((internalProjTo (tensorObj F X Y).isMod.isInternal d'.α
          ((F X Y).intertwiner.val p x y) : (tensorObj F X Y).isMod.weight d'.α) :
            (tensorObj F X Y).carrier) = 0 := by
        rw [internalProjTo_eq_zero_of_ne (tensorObj F X Y).isMod hm (Ne.symm hw)]
        rfl
      rw [FourPointTest.withX_congr d' h0 _ (Submodule.zero_mem _)]
      exact iterateEvaluation_withX_zero F K d'
  have hx' : Λ d'.x = iterateEvaluation F K d' := by
    change iterateEvaluation F K (d'.withX _ _) = _
    rw [FourPointTest.withX_congr d' (internalProjTo_coe_mem (tensorObj F X Y).isMod d'.hx) _
      d'.hx]
    rfl
  rw [← hx', hΛ]
  rfl

/-- **Left five-point faithfulness**, from ordinary four-point input, joint five-point
summability, and finite weight spectra. -/
theorem fivePointLeftFaithfulness_of (H : OrdinaryFourPointInput F)
    (hs5 : FivePointSummability F)
    (hspec : ∀ X : Ordinary W, ∃ S : Finset ℂ, ∀ w, X.isMod.weight w ≠ ⊥ →
      ∃ h ∈ S, ∃ n : ℕ, w = h + n) :
    FivePointLeftFaithfulness F := by
  intro X Y Z T U k₁ k₂ heq
  have hlin (d : FivePointTest X Y Z T U) : fivePointEvaluation F .left (k₁ - k₂) d =
      fivePointEvaluation F .left k₁ d - fivePointEvaluation F .left k₂ d := by
    rw [fivePointEvaluation, fivePointEvaluation, fivePointEvaluation,
      ← (hs5 X Y Z T U .left k₁ d).tsum_sub (hs5 X Y Z T U .left k₂ d)]
    apply tsum_congr
    intro w
    simp only [fivePointTerm]
    rw [← sub_mul, ← map_sub]
    rfl
  have hk (d : FivePointTest X Y Z T U) : fivePointEvaluation F .left (k₁ - k₂) d = 0 := by
    rw [hlin, congrFun heq d, sub_self]
  have hK : postcompose (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner U.isMod
      (k₁ - k₂) = 0 := by
    apply (H.faithfulness (tensorObj F X Y) Z T U).1
    funext d'
    rw [left_root_iterate_zero_all F H.summability hs5 (hspec _) (k₁ - k₂) hk d']
    symm
    rw [iterateEvaluation]
    convert tsum_zero with w
    simp only [iterateWeightTerm]
    have hz (m : ℂ) (a : (tensorObj F (tensorObj F X Y) Z).carrier) (b : T.carrier) :
        (0 : IterateSpace F (tensorObj F X Y) Z T U).val m a b = 0 := rfl
    erw [hz]
    simp
  have h0 : k₁ - k₂ = 0 := by
    apply ((F (tensorObj F (tensorObj F X Y) Z) T).universal U.carrier U.isMod).1
    rw [hK]
    exact (LinearMap.map_zero _).symm
  exact sub_eq_zero.mp h0

/-- **Left five-point faithfulness for strongly rational `W`** (PBW datum from the theorem
`VOA.pbw`). -/
theorem fivePointLeftFaithfulness_pbw (hV : StronglyRational W) : FivePointLeftFaithfulness F :=
  fivePointLeftFaithfulness_of F (ordinaryFourPointInput_pbw F hV)
    (FivePointSep.fivePointSummability_pbw F hV)
    (finite_weight_spectrum hV (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV))

end VOA.Huang.TensorCat
