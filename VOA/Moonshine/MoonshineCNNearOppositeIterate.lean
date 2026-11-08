import VOA.Moonshine.MoonshineCNNearOppositeRight

/-! The opposite Borcherds identity for every near-VOA whose `L₁` is locally nilpotent,
and its consequence `OppositeIterateIdentity`. The proof equates both sides with one
block sum of ordinary iterates (`oppositePair_borcherds_eq_blocks`,
`oppositeProduct_borcherds_eq_blocks`). Homogeneity is required only of the first state,
for the `L₁`-commutator; general states follow by linearity over the weight
decomposition. Consequently adjointness of all fields follows from adjointness of
generators, with no remaining hypothesis on the opposite modes. -/

noncomputable section
namespace VOA.NearVOA

open Module (End)
open scoped BigOperators

variable {H : Type*} [AddCommGroup H] [Module ℂ H] (V : NearVOA H)

/-- **Opposite Borcherds identity** at fixed weights. Only `u` is assumed homogeneous;
`q` is a free parameter for the second opposite mode. -/
theorem oppositeModeAtWeight_borcherds (hNil : ∀ w : H, ∃ k : ℕ, (V.L 1 ^ k) w = 0)
    {p q : ℤ} {u : H} (hu : u ∈ V.grading p) (v : H) (ℓ m n : ℤ) (y : H) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (V.oppositeModeAtWeight q (n + i) v (V.oppositeModeAtWeight p (ℓ + m - i) u y)
          - negOnePow ℓ • V.oppositeModeAtWeight p (m + i) u
              (V.oppositeModeAtWeight q (ℓ + n - i) v y)))
      = ∑ᶠ i : ℤ, cbz m i •
          V.oppositeModeAtWeight (p + q - (ℓ + i) - 1) (m + n - i) (V.smul u (ℓ + i) v) y := by
  obtain ⟨A₀, hA⟩ := hNil u
  obtain ⟨B₀, hB⟩ := hNil v
  rw [V.oppositePair_borcherds_eq_blocks hA hB,
    V.oppositeProduct_borcherds_eq_blocks hu hA hB hNil]

/-- The opposite iterate formula at fixed weights. -/
theorem oppositeModeAtWeight_iterate (hNil : ∀ w : H, ∃ k : ℕ, (V.L 1 ^ k) w = 0)
    {p q : ℤ} {u : H} (hu : u ∈ V.grading p) (v : H) (ℓ n : ℤ) (y : H) :
    V.oppositeModeAtWeight (p + q - ℓ - 1) n (V.smul u ℓ v) y =
      ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom ℓ i) •
        (V.oppositeModeAtWeight q (n + i) v (V.oppositeModeAtWeight p (ℓ - i) u y) -
          (-1 : ℂ) ^ ℓ • V.oppositeModeAtWeight p i u
            (V.oppositeModeAtWeight q (ℓ + n - i) v y)) := by
  have h := V.oppositeModeAtWeight_borcherds hNil (q := q) hu v ℓ 0 n y
  have hR : (∑ᶠ i : ℤ, cbz 0 i • V.oppositeModeAtWeight (p + q - (ℓ + i) - 1) (0 + n - i)
      (V.smul u (ℓ + i) v) y) = V.oppositeModeAtWeight (p + q - ℓ - 1) n (V.smul u ℓ v) y := by
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul]),
      cbz_zero_left, if_pos rfl, one_smul]
    simp only [add_zero, sub_zero, zero_add]
  rw [hR] at h
  simp only [add_zero, zero_add] at h
  rw [← h]
  symm
  apply VertexOperatorAlgebra.finsum_nat_to_int
  · intro t ht
    rw [cbz_apply_neg ℓ ht, mul_zero, zero_smul]
  · intro j
    rw [VertexOperatorAlgebra.negOnePow_eq_zpow, VertexOperatorAlgebra.negOnePow_eq_zpow,
      cbz_apply_nonneg ℓ (Int.natCast_nonneg j), Int.toNat_natCast, zpow_natCast]

/-- The right-hand side of the opposite iterate identity. -/
def oppositeIterateSum (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0) (u v y : H) (ℓ n : ℤ) : H :=
  ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom ℓ i) •
    (V.oppositeModes hNil (n + i) v (V.oppositeModes hNil (ℓ - i) u y) -
      (-1 : ℂ) ^ ℓ • V.oppositeModes hNil i u (V.oppositeModes hNil (ℓ + n - i) v y))

theorem oppositeIterateSum_zero_left (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    (v y : H) (ℓ n : ℤ) : V.oppositeIterateSum hNil 0 v y ℓ n = 0 := by
  simp [oppositeIterateSum]

theorem oppositeIterateSum_zero_right (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    (u y : H) (ℓ n : ℤ) : V.oppositeIterateSum hNil u 0 y ℓ n = 0 := by
  simp [oppositeIterateSum]

theorem oppositeIterateSum_add_left (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    (u u' v y : H) (ℓ n : ℤ) :
    V.oppositeIterateSum hNil (u + u') v y ℓ n
      = V.oppositeIterateSum hNil u v y ℓ n + V.oppositeIterateSum hNil u' v y ℓ n := by
  unfold oppositeIterateSum
  rw [← finsum_add_distrib (V.oppositeIterate_terms_finite hNil u v y ℓ n)
    (V.oppositeIterate_terms_finite hNil u' v y ℓ n)]
  refine finsum_congr (fun i => ?_)
  simp only [map_add, LinearMap.add_apply]
  module

theorem oppositeIterateSum_add_right (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    (u v v' y : H) (ℓ n : ℤ) :
    V.oppositeIterateSum hNil u (v + v') y ℓ n
      = V.oppositeIterateSum hNil u v y ℓ n + V.oppositeIterateSum hNil u v' y ℓ n := by
  unfold oppositeIterateSum
  rw [← finsum_add_distrib (V.oppositeIterate_terms_finite hNil u v y ℓ n)
    (V.oppositeIterate_terms_finite hNil u v' y ℓ n)]
  refine finsum_congr (fun i => ?_)
  simp only [map_add, LinearMap.add_apply]
  module

/-- **The opposite iterate identity holds** for every near-VOA with locally nilpotent `L₁`. -/
theorem oppositeIterateIdentity_of_locallyNilpotent
    (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0) : V.OppositeIterateIdentity hNil := by
  classical
  letI := V.isInternal.chooseDecomposition
  intro u v y ℓ n
  change V.oppositeModes hNil n (V.smul u ℓ v) y = V.oppositeIterateSum hNil u v y ℓ n
  induction u using DirectSum.Decomposition.inductionOn V.grading with
  | zero =>
      rw [V.smul_zero_left, map_zero, LinearMap.zero_apply, V.oppositeIterateSum_zero_left]
  | homogeneous u =>
      rename_i p
      induction v using DirectSum.Decomposition.inductionOn V.grading with
      | zero =>
          rw [V.smul_zero_right, map_zero, LinearMap.zero_apply,
            V.oppositeIterateSum_zero_right]
      | homogeneous v =>
          rename_i q
          have huv : V.smul (u : H) ℓ (v : H) ∈ V.grading (p + q - ℓ - 1) :=
            V.grading_mode _ u.property _ v.property ℓ
          rw [V.oppositeModes_homogeneous hNil huv]
          unfold oppositeIterateSum
          simp only [V.oppositeModes_homogeneous hNil u.property,
            V.oppositeModes_homogeneous hNil v.property]
          exact V.oppositeModeAtWeight_iterate hNil u.property (v : H) ℓ n y
      | add v v' hv hv' =>
          rw [show V.smul (u : H) ℓ (v + v') = V.smul (u : H) ℓ v + V.smul (u : H) ℓ v' from by
              simp only [smul_def, map_add],
            map_add, LinearMap.add_apply, hv, hv', V.oppositeIterateSum_add_right]
  | add u u' hu hu' =>
      rw [show V.smul (u + u') ℓ v = V.smul u ℓ v + V.smul u' ℓ v from by
          simp only [smul_def, map_add, mode_add, LinearMap.add_apply],
        map_add, LinearMap.add_apply, hu, hu', V.oppositeIterateSum_add_left]

/-- Adjointness of all fields from adjointness of generators, for every near-VOA with
locally nilpotent `L₁`. The opposite iterate law is now proved, not assumed. -/
theorem adjoint_of_locallyNilpotent_generators
    (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0) (B : LinearMap.BilinForm ℂ H) (G : Set H)
    (hGen : ∀ S : Submodule ℂ H, G ⊆ S →
      (∀ u ∈ S, ∀ v ∈ S, ∀ ℓ : ℤ, V.smul u ℓ v ∈ S) → S = ⊤)
    (hAdj : ∀ u ∈ G, ∀ (n : ℤ) (x y : H),
      B (mode (V.Y u) n x) y = B x (V.oppositeModes hNil n u y))
    (u : H) (n : ℤ) (x y : H) :
    B (mode (V.Y u) n x) y = B x (V.oppositeModes hNil n u y) :=
  V.adjoint_of_oppositeIterate_generators hNil (V.oppositeIterateIdentity_of_locallyNilpotent hNil)
    B G hGen hAdj u n x y

end VOA.NearVOA
