import VOA.Classification.COne.OrbPos9Algebra
import VOA.Huang.HKLRationalAssoc

/-!
# Associativity of the actual orbifold extension multiplication

The coefficient and convergence argument is adapted from
`VOA.Huang.HKLRationalAssoc`: use the ambient VOA's Jacobi identity directly,
then Huang's four-point faithfulness over the strongly rational fixed algebra.
No positivity or rigidity is assumed for the fixed algebra.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbPos9.Assoc
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct VOA.Huang.TensorCat
open VOA.Huang.HKLRational CategoryTheory Module
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (G : Subgroup (Aut W)) (F : FusionChoice (orbifoldVOA G))
local notation "A" => ambient G
local notation "μ" => ambientMultiplication G F

@[simp] theorem ambientIntertwiner_val (n : ℂ) (a b : V) :
    (ambientIntertwiner G).val n a b = moduleModes (adjointModule W) n a b := rfl

@[simp] theorem ambientIntertwiner_int (n : ℤ) (a b : V) :
    (ambientIntertwiner G).val (n : ℂ) a b = W.smul a n b :=
  moduleModes_apply_intCast (adjointModule W) n a b

section Terms


/-- The iterate summand of `(m ⊠ 1) ≫ act`. -/
theorem iterTerm_eq (d : FourPointTest A A A A) (w : ℂ) :
    iterateWeightTerm F (postcompose (F (tensorObj F A A) A).intertwiner
      (ambient G).isMod (tensorHom F μ (𝟙 A) ≫ μ)) d w =
      d.functional (moduleModes (adjointModule W) (w + d.γ - d.δ - 1)
        ((ambientIntertwiner G).val (d.α + d.β - w - 1) d.x d.y) d.z) *
        (d.coordinate : ℂ) ^ (w - d.α - d.β) := by
  unfold iterateWeightTerm
  congr 2
  change (μ).val ((tensorHom F μ (𝟙 A)).val
    ((F (tensorObj F A A) A).intertwiner.val _ _ d.z)) = _
  rw [tensorHom_intertwiner, Ordinary.id_apply, ambientMultiplication_intertwiner, ambientMultiplication_intertwiner, ambientIntertwiner_val]

/-- The product summand of `(1 ⊠ act) ≫ act`. -/
theorem prodTerm_eq (d : FourPointTest A A A A) (w : ℂ) :
    productWeightTerm F (postcompose (F A (tensorObj F A A)).intertwiner
      (ambient G).isMod (tensorHom F (𝟙 A) (μ) ≫ μ)) d w =
      d.functional (moduleModes (adjointModule W) (d.α + w - d.δ - 1) d.x
        (moduleModes (adjointModule W) (d.β + d.γ - w - 1) d.y d.z)) *
        (1 + (d.coordinate : ℂ)) ^ (d.δ - d.α - w) := by
  unfold productWeightTerm
  congr 2
  change (μ).val ((tensorHom F (𝟙 A) (μ)).val
    ((F A (tensorObj F A A)).intertwiner.val _ d.x _)) = _
  rw [tensorHom_intertwiner, Ordinary.id_apply, ambientMultiplication_intertwiner, ambientMultiplication_intertwiner]

/-- **The associator relation from the Jacobi identity of `Y_N`** (Jacobi at `m = K`, with
`a_{K+i} x = 0` for `i ≥ 0`), after applying a functional. -/
theorem assoc_rel (a b : (ambient G).carrier) (x : V) (f : V →ₗ[ℂ] ℂ) (D : ℤ) (K : ℕ)
    (hK : ∀ i : ℤ, 0 ≤ i → mode ((adjointModule W).YM a) (K + i) x = 0) (k1 : ℤ)
    (hk1 : ∀ k, k1 ≤ k → mode ((adjointModule W).YM b) k x = 0) (ℓ : ℤ) :
    ∑ i ∈ Finset.range (K + 1), (K.choose i : ℂ) *
        f (mode ((adjointModule W).YM ((ambientIntertwiner G).val ((ℓ + i : ℤ) : ℂ) a b)) (D - (ℓ + i)) x) =
      ∑' i : ℕ, cbz ((i : ℤ) - ℓ - 1) i *
        f (mode ((adjointModule W).YM a) (D - (D - K - ℓ + i)) (mode ((adjointModule W).YM b) (D - K - ℓ + i) x)) := by
  classical
  have hj := (adjointModule W).jacobi a b x ℓ (K : ℤ) (D - K - ℓ)
  set n1 : ℕ := (k1 - (D - K - ℓ)).toNat with hn1
  let ι : ℕ ↪ ℤ := ⟨Nat.cast, Nat.cast_injective⟩
  -- the left side of Jacobi is supported on `[0, n1)`
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range n1).map ι) ?hL,
    finsum_eq_sum_of_support_subset _ (s := (Finset.range (K + 1)).map ι) ?hR,
    Finset.sum_map, Finset.sum_map] at hj
  case hL =>
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_map, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    by_cases hi0 : i < 0
    · exact absurd (by rw [cbz_apply_neg ℓ hi0, mul_zero, zero_smul]) hi
    · refine ⟨i.toNat, ?_, by simp [ι]; omega⟩
      by_contra hlt
      apply hi
      rw [hK i (by omega), map_zero, smul_zero, sub_zero, hk1 _ (by omega), map_zero, smul_zero]
  case hR =>
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_map, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    by_cases hi0 : i < 0
    · exact absurd (by rw [cbz_apply_neg _ hi0, zero_smul]) hi
    · refine ⟨i.toNat, ?_, by simp [ι]; omega⟩
      by_contra hlt
      apply hi
      rw [cbz_lt (by positivity) (by omega), zero_smul]
  have hf := congrArg f hj
  simp only [map_sum, map_smul, map_sub, smul_eq_mul] at hf
  -- right side of the goal
  have hR : ∑' i : ℕ, cbz ((i : ℤ) - ℓ - 1) i *
        f (mode ((adjointModule W).YM a) (D - (D - K - ℓ + i)) (mode ((adjointModule W).YM b) (D - K - ℓ + i) x)) =
      ∑ i ∈ Finset.range n1, negOnePow (ι i) * cbz ℓ (ι i) *
        f (mode ((adjointModule W).YM a) (ℓ + K - ι i) (mode ((adjointModule W).YM b) (D - K - ℓ + ι i) x)) := by
    rw [tsum_eq_sum (s := Finset.range n1)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ι, Function.Embedding.coeFn_mk]
      rw [negOnePow_mul_cbz, show D - (D - K - ℓ + (i : ℤ)) = ℓ + K - i by ring]
    · intro i hi
      rw [Finset.mem_range, not_lt] at hi
      rw [hk1 _ (by omega), map_zero, map_zero, mul_zero]
  rw [hR]
  have hL : ∀ i ∈ Finset.range n1, negOnePow (ι i) * cbz ℓ (ι i) *
        f (mode ((adjointModule W).YM a) (ℓ + K - ι i) (mode ((adjointModule W).YM b) (D - K - ℓ + ι i) x)) =
      negOnePow (ι i) * cbz ℓ (ι i) *
        (f (mode ((adjointModule W).YM a) (ℓ + K - ι i) (mode ((adjointModule W).YM b) (D - K - ℓ + ι i) x)) -
          negOnePow ℓ * f (mode ((adjointModule W).YM b) (ℓ + (D - K - ℓ) - ι i) (mode ((adjointModule W).YM a) (K + ι i) x))) := by
    intro i _
    rw [hK _ (by simp [ι]), map_zero, map_zero, mul_zero, sub_zero]
  rw [Finset.sum_congr rfl hL, hf]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [ι, Function.Embedding.coeFn_mk]
  rw [cbz_apply_nonneg _ (by positivity), show ((i : ℤ)).toNat = i from by simp,
    VOA.Huang.AssocAssociator.gBinom_natCast, ambientIntertwiner_int,
    show (K : ℤ) + (D - K - ℓ) - i = D - (ℓ + i) by ring]

/-- The iterate summand on the integral lattice `w = α' + β' - 1 - r`. -/
theorem iterTerm_int (d : FourPointTest A A A A) {α' β' g : ℤ}
    (hα : d.α = α') (hβ : d.β = β') (hg : d.γ - d.δ = g) (r : ℤ) :
    d.functional (moduleModes (adjointModule W) ((((α' + β' - 1 : ℤ) : ℂ) - r) + d.γ - d.δ - 1)
        ((ambientIntertwiner G).val (d.α + d.β - (((α' + β' - 1 : ℤ) : ℂ) - r) - 1) d.x d.y) d.z) *
        (d.coordinate : ℂ) ^ ((((α' + β' - 1 : ℤ) : ℂ) - r) - d.α - d.β) =
      d.functional (mode ((adjointModule W).YM ((ambientIntertwiner G).val ((r : ℤ) : ℂ) d.x d.y))
        ((α' + β' + g - 2) - r) d.z) * (d.coordinate : ℂ) ^ (-r - 1) := by
  have e1 : d.α + d.β - (((α' + β' - 1 : ℤ) : ℂ) - r) - 1 = ((r : ℤ) : ℂ) := by
    rw [hα, hβ]; push_cast; ring
  have e2 : (((α' + β' - 1 : ℤ) : ℂ) - r) + d.γ - d.δ - 1 = (((α' + β' + g - 2) - r : ℤ) : ℂ) := by
    rw [show (((α' + β' - 1 : ℤ) : ℂ) - r) + d.γ - d.δ - 1 =
      (((α' + β' - 1 : ℤ) : ℂ) - r) + (d.γ - d.δ) - 1 by ring, hg]; push_cast; ring
  have e3 : (((α' + β' - 1 : ℤ) : ℂ) - r) - d.α - d.β = ((-r - 1 : ℤ) : ℂ) := by
    rw [hα, hβ]; push_cast; ring
  rw [e1, e2, e3, moduleModes_apply_intCast, Complex.cpow_intCast]

/-- The product summand on the lattice `w = β + γ - 1 - k`. -/
theorem prodTerm_int (d : FourPointTest A A A A) {α' β' g : ℤ}
    (hα : d.α = α') (hβ : d.β = β') (hg : d.γ - d.δ = g) (k : ℤ) :
    d.functional (moduleModes (adjointModule W) (d.α + (d.β + d.γ - 1 - k) - d.δ - 1) d.x
        (moduleModes (adjointModule W) (d.β + d.γ - (d.β + d.γ - 1 - k) - 1) d.y d.z)) *
        (1 + (d.coordinate : ℂ)) ^ (d.δ - d.α - (d.β + d.γ - 1 - k)) =
      d.functional (mode ((adjointModule W).YM d.x) ((α' + β' + g - 2) - k) (mode ((adjointModule W).YM d.y) k d.z)) *
        (1 + (d.coordinate : ℂ)) ^ (k - (α' + β' + g - 2) - 1) := by
  have e1 : d.β + d.γ - (d.β + d.γ - 1 - k) - 1 = ((k : ℤ) : ℂ) := by ring
  have e2 : d.α + (d.β + d.γ - 1 - k) - d.δ - 1 = (((α' + β' + g - 2) - k : ℤ) : ℂ) := by
    rw [show d.α + (d.β + d.γ - 1 - k) - d.δ - 1 = d.α + d.β + (d.γ - d.δ) - 2 - k by ring,
      hα, hβ, hg]; push_cast; ring
  have e3 : d.δ - d.α - (d.β + d.γ - 1 - k) = ((k - (α' + β' + g - 2) - 1 : ℤ) : ℂ) := by
    rw [show d.δ - d.α - (d.β + d.γ - 1 - k) = k + 1 - d.α - d.β - (d.γ - d.δ) by ring,
      hα, hβ, hg]; push_cast; ring
  rw [e1, e2, e3, moduleModes_apply_intCast, moduleModes_apply_intCast, Complex.cpow_intCast]

/-- Support of the iterate summand. -/
theorem iterTerm_support (d : FourPointTest A A A A) (w : ℂ)
    (hw : d.functional (moduleModes (adjointModule W) (w + d.γ - d.δ - 1)
        ((ambientIntertwiner G).val (d.α + d.β - w - 1) d.x d.y) d.z) *
        (d.coordinate : ℂ) ^ (w - d.α - d.β) ≠ 0) :
    (∃ r : ℤ, (r : ℂ) = d.α + d.β - w - 1) ∧ (∃ n : ℤ, (n : ℂ) = w + d.γ - d.δ - 1) := by
  constructor
  · by_contra h
    push Not at h
    apply hw
    rw [ambientIntertwiner_val, moduleModes_of_not_int (adjointModule W) h, LinearMap.zero_apply, LinearMap.zero_apply]
    have hz : moduleModes (adjointModule W) (w + d.γ - d.δ - 1) (0 : V) d.z = 0 := by
      simp only [map_zero, LinearMap.zero_apply]
    rw [hz]
    exact (congrArg (fun z : ℂ => z * _) d.functional.map_zero).trans (zero_mul _)
  · by_contra h
    push Not at h
    apply hw
    rw [moduleModes_of_not_int (adjointModule W) h, LinearMap.zero_apply, LinearMap.zero_apply]
    erw [LinearMap.map_zero, zero_mul]

/-- Support of the product summand. -/
theorem prodTerm_support (d : FourPointTest A A A A) (w : ℂ)
    (hw : d.functional (moduleModes (adjointModule W) (d.α + w - d.δ - 1) d.x
        (moduleModes (adjointModule W) (d.β + d.γ - w - 1) d.y d.z)) *
        (1 + (d.coordinate : ℂ)) ^ (d.δ - d.α - w) ≠ 0) :
    (∃ k : ℤ, (k : ℂ) = d.β + d.γ - w - 1) ∧ (∃ j : ℤ, (j : ℂ) = d.α + w - d.δ - 1) := by
  constructor
  · by_contra h
    push Not at h
    apply hw
    rw [moduleModes_of_not_int (adjointModule W) h, LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.map_zero]
    erw [LinearMap.map_zero, zero_mul]
  · by_contra h
    push Not at h
    apply hw
    rw [moduleModes_of_not_int (adjointModule W) h, LinearMap.zero_apply, LinearMap.zero_apply]
    erw [LinearMap.map_zero, zero_mul]

end Terms

/-! ## The per-test identity and associativity -/

section Main


/-- A nonzero vector of `A` has integral weight. -/
theorem int_of_ne_zero {α : ℂ} {a : (ambient G).carrier}
    (ha : a ∈ (ambient G).isMod.weight α) (ha0 : a ≠ 0) : ∃ k : ℤ, α = k := by
  by_contra h
  push Not at h
  have hz := adjWeight_eq_bot W (fun k hk => h k hk.symm)
  change a ∈ adjWeight W α at ha
  rw [hz] at ha
  exact ha0 ha

/-- **Iterate evaluation of `(m ⊠ 1) ≫ act` = product evaluation of `(1 ⊠ act) ≫ act`.** -/
theorem iter_eq_prod (hV : StronglyRational (orbifoldVOA G)) (d : FourPointTest A A A A) :
    iterateEvaluation F (postcompose (F (tensorObj F A A) A).intertwiner
      (ambient G).isMod (tensorHom F μ (𝟙 A) ≫ μ)) d =
    productEvaluation F (postcompose (F A (tensorObj F A A)).intertwiner
      (ambient G).isMod (tensorHom F (𝟙 A) (μ) ≫ μ)) d := by
  classical
  set H := ordinaryFourPointInput_pbw F hV
  unfold iterateEvaluation productEvaluation
  simp only [iterTerm_eq G F d, prodTerm_eq G F d]
  by_cases hall : (∃ α' : ℤ, d.α = α') ∧ (∃ β' : ℤ, d.β = β') ∧ (∃ g : ℤ, d.γ - d.δ = g)
  · obtain ⟨⟨α', hα⟩, ⟨β', hβ⟩, ⟨g, hg⟩⟩ := hall
    rw [tsum_eq_tsum_int (((α' + β' - 1 : ℤ) : ℂ)) ?s1, tsum_eq_tsum_int (d.β + d.γ - 1) ?s2]
    case s1 =>
      intro w hw
      obtain ⟨⟨r, hr⟩, -⟩ := iterTerm_support G d w hw
      refine ⟨r, ?_⟩
      rw [hα, hβ] at hr
      push_cast
      linear_combination hr
    case s2 =>
      intro w hw
      obtain ⟨⟨k, hk⟩, -⟩ := prodTerm_support G d w hw
      exact ⟨k, by linear_combination hk⟩
    simp only [iterTerm_int G d hα hβ hg, prodTerm_int G d hα hβ hg]
    -- truncations
    obtain ⟨N0, hN0⟩ := (adjointModule W).truncation d.x d.z
    obtain ⟨k1, hk1⟩ := (adjointModule W).truncation d.y d.z
    obtain ⟨r0, hr0⟩ := (ambientIntertwiner G).property.truncation d.x d.y 0
    set K : ℕ := N0.toNat
    have hK : ∀ i : ℤ, 0 ≤ i → mode ((adjointModule W).YM d.x) (K + i) d.z = 0 := fun i hi =>
      hN0 _ (by simp only [K]; omega)
    set D : ℤ := α' + β' + g - 2
    refine assoc_series_eq
      (fun k => d.functional (mode ((adjointModule W).YM d.x) (D - k) (mode ((adjointModule W).YM d.y) k d.z)))
      (fun r => d.functional (mode ((adjointModule W).YM ((ambientIntertwiner G).val ((r : ℤ) : ℂ) d.x d.y))
        (D - r) d.z)) D K k1 r0 ?hP ?hQ (assoc_rel G d.x d.y d.z d.functional D K hK k1 hk1)
      ?hProd ?hIt d.positive d.less_one
    case hP =>
      intro k hk
      simp only
      rw [hk1 k hk, LinearMap.map_zero]
      erw [LinearMap.map_zero]
    case hQ =>
      intro r hr
      simp only
      have h0 := hr0 r hr
      rw [zero_add] at h0
      erw [h0, map_zero, mode_zero, LinearMap.zero_apply]
      erw [LinearMap.map_zero]
    case hProd =>
      intro s hs0 hs1
      let d' : FourPointTest A A A A :=
        { d with coordinate := s, positive := hs0, less_one := hs1 }
      have hsum := (H.summability A A A A d').2
        (postcompose (F A (tensorObj F A A)).intertwiner (ambient G).isMod
          (tensorHom F (𝟙 A) (μ) ≫ μ))
      have hinj : Function.Injective fun k : ℤ => d.β + d.γ - 1 - (k : ℂ) := fun a b h => by
        simpa using h
      refine (hsum.comp_injective hinj).congr fun k => ?_
      simp only [Function.comp]
      rw [prodTerm_eq G F d', prodTerm_int G d' hα hβ hg]
    case hIt =>
      intro s hs0 hs1
      let d' : FourPointTest A A A A :=
        { d with coordinate := s, positive := hs0, less_one := hs1 }
      have hsum := (H.summability A A A A d').1
        (postcompose (F (tensorObj F A A) A).intertwiner (ambient G).isMod
          (tensorHom F μ (𝟙 A) ≫ μ))
      have hinj : Function.Injective fun r : ℤ => (((α' + β' - 1 : ℤ) : ℂ)) - (r : ℂ) :=
        fun a b h => by simpa using h
      refine (hsum.comp_injective hinj).congr fun r => ?_
      simp only [Function.comp]
      rw [iterTerm_eq G F d', iterTerm_int G d' hα hβ hg]
  · -- non-integral data: both sides vanish termwise
    have hx : ∀ w, d.functional (moduleModes (adjointModule W) (w + d.γ - d.δ - 1)
        ((ambientIntertwiner G).val (d.α + d.β - w - 1) d.x d.y) d.z) *
        (d.coordinate : ℂ) ^ (w - d.α - d.β) = 0 := by
      intro w
      by_contra hw
      obtain ⟨⟨r, hr⟩, ⟨n, hn⟩⟩ := iterTerm_support G d w hw
      have hx0 : d.x ≠ 0 := fun h0 => hw (by
        erw [h0, LinearMap.map_zero, LinearMap.zero_apply, LinearMap.map_zero,
          LinearMap.zero_apply]
        erw [LinearMap.map_zero, zero_mul])
      have hy0 : d.y ≠ 0 := fun h0 => hw (by
        erw [h0, LinearMap.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
        erw [LinearMap.map_zero, zero_mul])
      obtain ⟨α', hα⟩ := int_of_ne_zero G d.hx hx0
      obtain ⟨β', hβ⟩ := int_of_ne_zero G d.hy hy0
      exact hall ⟨⟨α', hα⟩, ⟨β', hβ⟩, ⟨n - (α' + β' - 1 - r) + 1, by
        push_cast; rw [hn, hr, hα, hβ]; ring⟩⟩
    have hy : ∀ w, d.functional (moduleModes (adjointModule W) (d.α + w - d.δ - 1) d.x
        (moduleModes (adjointModule W) (d.β + d.γ - w - 1) d.y d.z)) *
        (1 + (d.coordinate : ℂ)) ^ (d.δ - d.α - w) = 0 := by
      intro w
      by_contra hw
      obtain ⟨⟨k, hk⟩, ⟨j, hj⟩⟩ := prodTerm_support G d w hw
      have hx0 : d.x ≠ 0 := fun h0 => hw (by
        erw [h0, LinearMap.map_zero, LinearMap.zero_apply]
        erw [LinearMap.map_zero, zero_mul])
      have hy0 : d.y ≠ 0 := fun h0 => hw (by
        erw [h0, LinearMap.map_zero, LinearMap.zero_apply, LinearMap.map_zero]
        erw [LinearMap.map_zero, zero_mul])
      obtain ⟨α', hα⟩ := int_of_ne_zero G d.hx hx0
      obtain ⟨β', hβ⟩ := int_of_ne_zero G d.hy hy0
      exact hall ⟨⟨α', hα⟩, ⟨β', hβ⟩, ⟨j + k + 2 - α' - β', by
        push_cast; rw [hj, hk, hα, hβ]; ring⟩⟩
    rw [tsum_congr hx, tsum_congr hy]

/-- **HKL 2015 Thm 3.4: the `A`-action of an ordinary `W`-module is associative**, for the
library's analytic associator `evalAssoc`. -/
theorem act_assoc (hV : StronglyRational (orbifoldVOA G)) :
    tensorHom F μ (𝟙 A) ≫ μ =
      (evalAssoc F (ordinaryFourPointInput_pbw F hV) A A A).hom ≫
        tensorHom F (𝟙 A) (μ) ≫ μ := by
  apply ((F (tensorObj F A A) A).universal (ambient G).carrier (ambient G).isMod).1
  apply ((ordinaryFourPointInput_pbw F hV).faithfulness A A A A).1
  rw [evalAssoc_fourPoint F _ A A A A]
  funext d
  exact iter_eq_prod G F hV d

end Main

end VOA.Classification.COne.OrbPos9.Assoc
