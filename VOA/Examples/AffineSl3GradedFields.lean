import VOA.Examples.AffineSl3Assembly

/-!
# Homogeneous reconstruction for the sl3 vacuum

Current creation words span each energy eigenspace. Their normal-ordered
fields have the expected weight shifts, giving an actual graded vertex
algebra with finite-dimensional homogeneous pieces.
-/
namespace VOA.AffineSl3
open Module (End)
open VOA.AffineLie
open scoped BigOperators

/-! ## VA1 grading: the graded-field machine -/

/-- A **graded field of weight `D`**: each coefficient `a j` shifts the `gradingZA`-degree by `D+j`. -/
def GradedFieldA (k : ℂ) (a : FormalDist (End ℂ (Vacuum k))) (D : ℤ) : Prop :=
  ∀ (j w : ℤ) (p : Vacuum k), p ∈ gradingZA k w → a j p ∈ gradingZA k (D + w + j)

/-- A finite-support finsum of submodule elements lies in the submodule. -/
theorem finsumA_mem_submodule {k : ℂ} {ι : Type*} (S : Submodule ℂ (Vacuum k))
    (g : ι → Vacuum k) (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) :
    (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)

/-- The identity field is a graded field of weight `0`. -/
theorem idFieldA_gradedField (k : ℂ) : GradedFieldA k (idFieldA k) 0 := by
  intro j w p hp
  show (if j = 0 then (LinearMap.id : End ℂ (Vacuum k)) else 0) p ∈ gradingZA k (0 + w + j)
  by_cases hj : j = 0
  · rw [if_pos hj, LinearMap.id_apply, hj, show (0 : ℤ) + w + 0 = w from by ring]; exact hp
  · rw [if_neg hj, LinearMap.zero_apply]; exact Submodule.zero_mem _

/-- The `zʲ`-coefficient of `genFieldA a i`. -/
theorem genFieldA_coeff (k : ℂ) (a : Fin 8) (i : ℕ) (j : ℤ) :
    (genFieldA k a i) j
      = (i.factorial : ℂ)⁻¹ • ((∏ q ∈ Finset.range i, (j + 1 + (q : ℤ))) • J k a (-j - i - 1)) := by
  have h : (genFieldA k a i) j = (i.factorial : ℂ)⁻¹ • ((VOA.deriv^[i] (Jfield k a)) j) := rfl
  rw [h, VertexOperatorAlgebra.deriv_pow_apply, Jfield_apply,
    show (-(j + (i : ℤ)) - 1 : ℤ) = -j - i - 1 from by ring]

/-- The generator field `genFieldA a i` is a graded field of weight `i+1`. -/
theorem genFieldA_gradedField (k : ℂ) (a : Fin 8) (i : ℕ) :
    GradedFieldA k (genFieldA k a i) ((i : ℤ) + 1) := by
  intro j w p hp
  rw [genFieldA_coeff, LinearMap.smul_apply,
    show ((i : ℤ) + 1 + w + j) = w - (-j - (i : ℤ) - 1) from by ring]
  refine Submodule.smul_mem _ _ ?_
  show ((∏ q ∈ Finset.range i, (j + 1 + (q : ℤ))) • J k a (-j - (i : ℤ) - 1)) p ∈ _
  rw [← Int.cast_smul_eq_zsmul ℂ, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (J_mem_gradingZA k a (-j - (i : ℤ) - 1) w hp)

/-- The normal-ordered product of graded fields is graded, weights adding. -/
theorem GradedFieldA.nprod {k : ℂ} {a b : FormalDist (End ℂ (Vacuum k))} (ha : IsField a)
    (hb : IsField b) {Da Db : ℤ} (hga : GradedFieldA k a Da) (hgb : GradedFieldA k b Db) :
    GradedFieldA k (VOA.nprod ha hb) (Da + Db) := by
  intro s w p hp
  rw [nprod_apply]
  refine finsumA_mem_submodule _ _ (normalOrdered_diag_support_finite ha hb s p) (fun m => ?_)
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    show a m (b (s - m) p) ∈ gradingZA k (Da + Db + w + s)
    have hb' := hgb (s - m) w p hp
    have ha' := hga m (Db + w + (s - m)) _ hb'
    rwa [show Da + (Db + w + (s - m)) + m = Da + Db + w + s from by ring] at ha'
  · rw [if_neg h0]
    show b (s - m) (a m p) ∈ gradingZA k (Da + Db + w + s)
    have ha' := hga m w p hp
    have hb' := hgb (s - m) (Da + w + m) _ ha'
    rwa [show Db + (Da + w + m) + (s - m) = Da + Db + w + s from by ring] at hb'

/-- The integer weight of a (basis) word `l`: `∑ (iₜ+1)`. -/
def wordDegA : List (Fin 8 × ℕ) → ℤ
  | [] => 0
  | (ai :: rest) => ((ai.2 : ℤ) + 1) + wordDegA rest

/-- The empty creation word has degree zero. -/
@[simp] theorem wordDegA_nil : wordDegA ([] : List (Fin 8 × ℕ)) = 0 := rfl

/-- Adding a current of mode minus i minus one raises the word degree by i plus one. -/
theorem wordDegA_cons (ai : Fin 8 × ℕ) (rest : List (Fin 8 × ℕ)) :
    wordDegA (ai :: rest) = ((ai.2 : ℤ) + 1) + wordDegA rest := rfl

/-- Each word field `YwordA k l` is a graded field of weight `wordDegA l`. -/
theorem YwordA_gradedField (k : ℂ) :
    ∀ l : List (Fin 8 × ℕ), GradedFieldA k (YwordA k l) (wordDegA l)
  | [] => by rw [YwordA_nil, wordDegA_nil]; exact idFieldA_gradedField k
  | (ai :: rest) => by
      rw [YwordA_cons, wordDegA_cons]
      exact GradedFieldA.nprod (genFieldA_isField k ai.1 ai.2) (YwordA_isField k rest)
        (genFieldA_gradedField k ai.1 ai.2) (YwordA_gradedField k rest)

/-- `GradedFieldA` is closed under addition (same weight). -/
theorem GradedFieldA.add {k : ℂ} {a b : FormalDist (End ℂ (Vacuum k))} {D : ℤ}
    (ha : GradedFieldA k a D) (hb : GradedFieldA k b D) : GradedFieldA k (a + b) D := by
  intro j w p hp
  show (a j + b j) p ∈ _
  rw [LinearMap.add_apply]
  exact Submodule.add_mem _ (ha j w p hp) (hb j w p hp)

/-- `GradedFieldA` is closed under scaling. -/
theorem GradedFieldA.smul' {k : ℂ} {a : FormalDist (End ℂ (Vacuum k))} {D : ℤ} (c : ℂ)
    (ha : GradedFieldA k a D) : GradedFieldA k (c • a) D := by
  intro j w p hp
  show (c • a j) p ∈ _
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ c (ha j w p hp)

/-- The zero field obeys the homogeneous degree-shift condition at any weight. -/
theorem GradedFieldA.zero {k : ℂ} {D : ℤ} :
    GradedFieldA k (0 : FormalDist (End ℂ (Vacuum k))) D := by
  intro j w p hp
  show (0 : End ℂ (Vacuum k)) p ∈ _
  rw [LinearMap.zero_apply]
  exact Submodule.zero_mem _

/-! ### Homogeneous spanning of `gradingZA` by basis word states -/

/-- The span of the weight-`p` basis word states. -/
noncomputable def HSpan (k : ℂ) (p : ℤ) : Submodule ℂ (Vacuum k) :=
  Submodule.span ℂ {x | ∃ l : List (Fin 8 × ℕ), wordDegA l = p ∧ wordStateA k l = x}

/-- `Jᵃ_{-n-1}` maps the weight-`d` span into the weight-`d+(n+1)` span. -/
theorem J_mem_hspan (k : ℂ) (a : Fin 8) (n : ℕ) (d : ℤ) {y : Vacuum k}
    (hy : y ∈ HSpan k d) : J k a (-(n : ℤ) - 1) y ∈ HSpan k (d + ((n : ℤ) + 1)) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      refine Submodule.subset_span ⟨(a, n) :: l, ?_, ?_⟩
      · rw [wordDegA_cons, hl]; ring
      · rw [wordStateA_cons]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add p q _ _ ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
  | smul c p _ ihp => rw [map_smul]; exact Submodule.smul_mem _ c ihp

/-- Each creation monomial `negWord L` lies in the weight-`wordDeg L` span. -/
theorem negWord_mem_hspan (k : ℂ) (L : List (Sl3 × ℕ)) :
    negWord form form_invariant k L ∈ HSpan k (wordDeg L : ℤ) := by
  induction L with
  | nil =>
      refine Submodule.subset_span ⟨[], ?_, ?_⟩
      · rw [wordDegA_nil, wordDeg_nil, Nat.cast_zero]
      · rfl
  | cons xn L' ih =>
      obtain ⟨x, n⟩ := xn
      rw [negWord_cons]
      have heq : vacuumRho form form_invariant k
            (ofLoop form form_invariant x (-(n : ℤ) - 1))
            (negWord form form_invariant k L')
          = ∑ c : Fin 8, coordinates x c • (J k c (-(n : ℤ) - 1)
              (negWord form form_invariant k L')) := by
        rw [← loopMul_apply]
        conv_lhs => rw [basis_decomp x]
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [map_smul, LinearMap.smul_apply]
        rfl
      rw [heq, show (wordDeg ((x, n) :: L') : ℤ) = (wordDeg L' : ℤ) + ((n : ℤ) + 1) from by
        simp only [wordDeg]; push_cast; ring]
      exact Submodule.sum_mem _ (fun c _ =>
        Submodule.smul_mem _ _ (J_mem_hspan k c n (wordDeg L' : ℤ) ih))

/-- **Homogeneous spanning**: `gradingZA k p ≤ HSpan k p` (each energy eigenspace is spanned by the
weight-`p` basis word states; via `eigenspace_eq_degSpan` + the degree-tracked basis decomposition). -/
theorem gradingZA_le_hspan (k : ℂ) (p : ℤ) : gradingZA k p ≤ HSpan k p := by
  rw [gradingZA_def, ell0OpA, eigenspace_eq_degSpan, degSpan, Submodule.span_le]
  rintro _ ⟨L, hL, rfl⟩
  have hp : (wordDeg L : ℤ) = p := by
    simp only [Set.mem_setOf_eq, neg_inj] at hL
    exact_mod_cast hL
  rw [SetLike.mem_coe, ← hp]
  exact negWord_mem_hspan k L

/-! ### VA1 -/

/-- `YA u` is a graded field of weight `p` whenever `u ∈ HSpan k p`. -/
theorem YA_gradedField_of_hspan (k : ℂ) (hk : k + 3 ≠ 0) (p : ℤ) {u : Vacuum k}
    (hu : u ∈ HSpan k p) : GradedFieldA k (YA k hk u) p := by
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      rw [YA_wordState, ← hl]; exact YwordA_gradedField k l
  | zero => rw [map_zero]; exact GradedFieldA.zero
  | add x y _ _ ihx ihy => rw [map_add]; exact GradedFieldA.add ihx ihy
  | smul c x _ ihx => rw [map_smul]; exact GradedFieldA.smul' c ihx

/-- `YA u` is a graded field of weight `p` whenever `u ∈ gradingZA k p`. -/
theorem YA_gradedField_of_mem (k : ℂ) (hk : k + 3 ≠ 0) (p : ℤ) {u : Vacuum k}
    (hu : u ∈ gradingZA k p) : GradedFieldA k (YA k hk u) p :=
  YA_gradedField_of_hspan k hk p (gradingZA_le_hspan k p hu)

/-- **VA1** (`hYA_grading`): `mode (YA u) n v ∈ gradingZA k (p + q - n - 1)`. -/
theorem hYA_grading (k : ℂ) (hk : k + 3 ≠ 0) {p q : ℤ} (u : Vacuum k)
    (hu : u ∈ gradingZA k p) (v : Vacuum k) (hv : v ∈ gradingZA k q) (n : ℤ) :
    mode (YA k hk u) n v ∈ gradingZA k (p + q - n - 1) := by
  rw [mode_apply]
  have := YA_gradedField_of_mem k hk p hu (-n - 1) q v hv
  rwa [show p + q + (-n - 1) = p + q - n - 1 from by ring] at this

/-- The actual universal sl3 vacuum is an internally graded vertex algebra
with finite-dimensional pieces at every noncritical level. -/
noncomputable def affineVertexAlgebra (k : ℂ) (hk : k+3 ≠ 0) :
    PreVertexAlgebra (Vacuum k) where
  grading := gradingZA k
  isInternal := gradingZA_isInternal k
  finrank := gradingZA_finiteDimensional k
  Y := YA k hk
  vacuum := vacuumA k
  vacuum_mem := vacuumA_mem_gradingZA_zero k
  grading_mode := hYA_grading k hk
  vacuum_Y := YA_vacuum k hk
  creation := YA_creation k hk
  locality := YA_local k hk
  regularity := YA_regularity k hk

end VOA.AffineSl3
