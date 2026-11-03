import VOA.Huang.GenusOneG1fScalar
import VOA.Huang.GenusOneIntCoordSubstitution
import VOA.Huang.GenusTwoPointSepIntertwinerFlow

/-!
# The energy commutator of the explicit bracket intertwiner

For ANY intertwining operator `Y` among lowest-weight modules, the explicit (independently
defined) bracket field `bracketModes Y` of `GenusOneIntCoordSubstitution`,
`Y[w, z] = Y(e^{z L(0)} w, e^z − 1)`, satisfies the square energy commutator

  `L[0] Y[w]_n x − Y[w]_n L[0] x = Y[L[0] w]_n x − (n + 1) Y[w]_n x`

(`bracketModes_energy`), the statement that `[L[0], Y[w, z]] = Y[L[0]w, z] + z ∂_z Y[w, z]`.
Proof: `L[0] = Σ_k cc k L(k)` (Zhu), the intertwiner commutator
`[L(k), Y_m(w)] = Σ_j C(k+1, j) Y_{k+1+m−j}(L(j−1) w)` (`intertwiner_virasoro_comm`), a finite
Cauchy regrouping (`cauchy_regroup`) and the two scalar convolution identities
`energy_scalar_J` (the `L(j−1)`, `j ≥ 2`, terms) and `energy_scalar_K` (the `L(−1)`, `L(0)`
terms) of `GenusOneG1fScalar`. No coordinate transport, flow or analysis is used.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1f

open VOA
open VOA.Huang.GenusOne (sqL)
open VOA.Huang.GenusOne.SquareModule (roundL)
open VOA.Huang.GenusOne.IntCoord (bracketModes bracketCoeff bracketModes_eq_sum_range)
open scoped BigOperators

/-! ## §1 A finite Cauchy regrouping -/

theorem cauchy_regroup {M : Type*} [AddCommGroup M] [Module ℂ M] (A b : ℕ → ℂ) (g : ℕ → M)
    (T I R : ℕ) (hg : ∀ t, T ≤ t → g t = 0) (hI : T ≤ I) (hR : T ≤ R) :
    ∑ i ∈ Finset.range I, ∑ r ∈ Finset.range R, (A i * b r) • g (r + i) =
      ∑ t ∈ Finset.range T, (∑ i ∈ Finset.range (t + 1), A i * b (t - i)) • g t := by
  have h1 : ∑ t ∈ Finset.range T, (∑ i ∈ Finset.range (t + 1), A i * b (t - i)) • g t =
      ∑ i ∈ Finset.range T, ∑ t ∈ Finset.Ico i T, (A i * b (t - i)) • g t := by
    simp only [Finset.sum_smul]
    rw [Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.range_eq_Ico]
  rw [h1]
  have h2 : ∀ i ∈ Finset.range T, ∑ t ∈ Finset.Ico i T, (A i * b (t - i)) • g t =
      ∑ r ∈ Finset.range R, (A i * b r) • g (r + i) := by
    intro i hi
    have hiT : i ≤ T := le_of_lt (Finset.mem_range.mp hi)
    rw [Finset.sum_Ico_eq_sum_range]
    have hs : ∑ r ∈ Finset.range (T - i), (A i * b (i + r - i)) • g (i + r) =
        ∑ r ∈ Finset.range (T - i), (A i * b r) • g (r + i) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Nat.add_sub_cancel_left, add_comm i r]
    rw [hs]
    apply Finset.sum_subset
    · intro r hr
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hr) (by omega))
    · intro r _ hr
      rw [hg _ (by simp only [Finset.mem_range, not_lt] at hr; omega), smul_zero]
  rw [Finset.sum_congr rfl h2]
  symm
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hI)
  · intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    exact Finset.sum_eq_zero fun r _ => by rw [hg _ (by omega), smul_zero]

/-- A uniform truncation bound for finitely many sequences. -/
theorem exists_uniform_bound {M : Type*} [AddCommGroup M] (f : ℕ → ℕ → M)
    (hf : ∀ j, ∃ S : ℕ, ∀ s, S ≤ s → f j s = 0) (J : ℕ) :
    ∃ S : ℕ, ∀ j < J, ∀ s, S ≤ s → f j s = 0 := by
  induction J with
  | zero => exact ⟨0, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ J ih =>
    obtain ⟨S₁, h₁⟩ := ih
    obtain ⟨S₂, h₂⟩ := hf J
    refine ⟨max S₁ S₂, fun j hj s hs => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact h₁ j hj s (le_trans (le_max_left _ _) hs)
    · exact h₂ s (le_trans (le_max_right _ _) hs)

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P Q N : LWModule W}

/-- Intertwiner truncation in natural shifts. -/
theorem intertwiner_nat_bound (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) (n : ℂ)
    (w : P.carrier) (x : Q.carrier) : ∃ S : ℕ, ∀ s, S ≤ s → Y.val (n + s) w x = 0 := by
  obtain ⟨K, hK⟩ := Y.property.truncation w x n
  refine ⟨K.toNat, fun s hs => ?_⟩
  have := hK (s : ℤ) (by omega)
  simpa using this

theorem module_nat_bound {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)
    (a : V) (x : M) : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → mode (A.YM a) (k : ℤ) x = 0 := by
  obtain ⟨K, hK⟩ := A.truncation a x
  exact ⟨K.toNat, fun k hk => hK _ (by omega)⟩

/-- `L[0] v = Σ_{r < K} cc r · L(r) v` once `L(r) v` vanishes for `r ≥ K`. -/
theorem sqL_zero_eq_sum {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M) (v : M)
    (K : ℕ) (hK : ∀ k : ℕ, K ≤ k → mode (A.YM W.conformalVector) (k : ℤ) v = 0) :
    sqL A 0 v = ∑ r ∈ Finset.range K, cc r • roundL A (r : ℤ) v := by
  rw [VOA.Huang.GenusOne.SquareModule.Lsq_zero_eq_nat_finsum,
    finsum_eq_sum_of_support_subset _ (s := Finset.range K)]
  · exact Finset.sum_congr rfl fun r _ => by rw [cc_eq_sqBracketCoeffZ]
  · intro r hr
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hr
    have : roundL A (r : ℤ) v = 0 := by
      rw [roundL, show ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) by push_cast; ring]
      exact hK _ (by omega)
    simp [this]

/-- The commutator of `L(k)` with the explicit bracket mode, expanded. -/
theorem comm_expand (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) {α : ℂ} {w : P.carrier}
    (hw : w ∈ P.isMod.weight α) (n : ℂ) (x : Q.carrier) (k S : ℕ)
    (hS1 : ∀ s : ℕ, S ≤ s → Y.val (n + s) w x = 0)
    (hS2 : ∀ s : ℕ, S ≤ s → Y.val (n + s) w (roundL Q.isMod (k : ℤ) x) = 0) :
    roundL N.isMod (k : ℤ) (bracketModes Y n w x) -
        bracketModes Y n w (roundL Q.isMod (k : ℤ) x) =
      ∑ r ∈ Finset.range S, ∑ j ∈ Finset.range (k + 2),
        (bracketCoeff α n r * ((k + 1).choose j : ℂ)) •
          Y.val (n + ((r + k + 1 - j : ℕ) : ℂ)) (mode (P.isMod.YM W.conformalVector) j w) x := by
  rw [bracketModes_eq_sum_range Y hw n x S hS1, bracketModes_eq_sum_range Y hw n _ S hS2,
    map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, ← smul_sub]
  have h := VOA.Huang.GenusTwoPoint.Separate.intertwiner_virasoro_comm Y k (n + r) w x
  rw [h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [smul_smul]
  congr 2
  push_cast [Nat.cast_sub (show j ≤ r + k + 1 by omega)]
  ring_nf

/-! ## §2 Generic regrouping by the descendant index `j` -/

section Generic

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The `j`-th descendant block. -/
def Gblock (cK b : ℕ → ℂ) (Z : ℕ → ℕ → M) (K S j : ℕ) : M :=
  ∑ k ∈ Finset.range K, ∑ r ∈ Finset.range S,
    (cK k * (b r * ((k + 1).choose j : ℂ))) • Z j (r + k + 1 - j)

theorem regroup_j (cK b : ℕ → ℂ) (Z : ℕ → ℕ → M) (K S : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ Finset.range K, cK k • ∑ r ∈ Finset.range S, ∑ j ∈ Finset.range (k + 2),
        (b r * ((k + 1).choose j : ℂ)) • Z j (r + k + 1 - j) =
      ∑ p ∈ Finset.range (K - 1), Gblock cK b Z K S (p + 2) + Gblock cK b Z K S 1 +
        Gblock cK b Z K S 0 := by
  have h1 : ∀ k ∈ Finset.range K, cK k • ∑ r ∈ Finset.range S, ∑ j ∈ Finset.range (k + 2),
      (b r * ((k + 1).choose j : ℂ)) • Z j (r + k + 1 - j) =
      ∑ r ∈ Finset.range S, ∑ j ∈ Finset.range (K + 1),
        (cK k * (b r * ((k + 1).choose j : ℂ))) • Z j (r + k + 1 - j) := by
    intro k hk
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.smul_sum]
    simp only [smul_smul]
    apply Finset.sum_subset
    · intro j hj
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj)
        (by have := Finset.mem_range.mp hk; omega))
    · intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  have hK1 : K + 1 = (K - 1) + 2 := by omega
  rw [hK1, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Gblock]

theorem Gblock_zero (cK b : ℕ → ℂ) (Z : ℕ → ℕ → M) (y : ℕ → M) (n : ℂ) (K S : ℕ)
    (hZ0 : ∀ m : ℕ, Z 0 (m + 1) = (-(n + m + 1)) • y m) (hy : ∀ t, S ≤ t → y t = 0)
    (hKS : S ≤ K) :
    Gblock cK b Z K S 0 = ∑ t ∈ Finset.range S,
      (∑ i ∈ Finset.range (t + 1), cK i * b (t - i)) • ((-(n + t + 1)) • y t) := by
  rw [← cauchy_regroup cK b (fun t => (-(n + t + 1)) • y t) S K S
    (fun t ht => by simp only [hy t ht, smul_zero]) hKS le_rfl, Gblock]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ => ?_
  rw [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero,
    show r + k + 1 = (r + k) + 1 by ring, hZ0]

theorem Gblock_one (cK b : ℕ → ℂ) (Z : ℕ → ℕ → M) (y : ℕ → M) (α : ℂ) (K S : ℕ)
    (hZ1 : ∀ m : ℕ, Z 1 m = α • y m) (hy : ∀ t, S ≤ t → y t = 0) (hKS : S ≤ K) :
    Gblock cK b Z K S 1 = ∑ t ∈ Finset.range S,
      (∑ i ∈ Finset.range (t + 1), (cK i * ((i : ℂ) + 1)) * b (t - i)) • (α • y t) := by
  rw [← cauchy_regroup (fun i => cK i * ((i : ℂ) + 1)) b (fun t => α • y t) S K S
    (fun t ht => by simp only [hy t ht, smul_zero]) hKS le_rfl, Gblock]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ => ?_
  rw [Nat.choose_one_right, Nat.add_sub_cancel, hZ1]
  push_cast
  congr 1
  ring

theorem Gblock_two (cK b : ℕ → ℂ) (Z : ℕ → ℕ → M) (p K S : ℕ)
    (hz : ∀ t, S ≤ t → Z (p + 2) t = 0) (hKS : S + p + 1 ≤ K) :
    Gblock cK b Z K S (p + 2) = ∑ t ∈ Finset.range S,
      (∑ i ∈ Finset.range (t + 1), (cK (i + p + 1) * ((i + p + 2).choose (p + 2) : ℂ)) *
        b (t - i)) • Z (p + 2) t := by
  rw [← cauchy_regroup (fun i => cK (i + p + 1) * ((i + p + 2).choose (p + 2) : ℂ)) b
    (Z (p + 2)) S (K - (p + 1)) S hz (by omega) le_rfl, Gblock]
  have hK : K = (p + 1) + (K - (p + 1)) := by omega
  rw [hK, Finset.sum_range_add, Nat.add_sub_cancel_left]
  have hz0 : ∑ k ∈ Finset.range (p + 1), ∑ r ∈ Finset.range S,
      (cK k * (b r * ((k + 1).choose (p + 2) : ℂ))) • Z (p + 2) (r + k + 1 - (p + 2)) = 0 := by
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun r _ => ?_
    rw [Nat.choose_eq_zero_of_lt (by have := Finset.mem_range.mp hk; omega)]
    simp
  rw [hz0, zero_add]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
  rw [show p + 1 + i + 1 = i + p + 2 by ring, show r + (p + 1 + i) + 1 - (p + 2) = r + i by omega,
    show p + 1 + i = i + p + 1 by ring]
  congr 1
  ring

end Generic

/-! ## §3 The bracket energy commutator -/

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P Q N : LWModule W}

/-- **The bracket energy commutator on an ordinary-homogeneous insertion.** -/
theorem bracketModes_energy_of_weight (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    {α : ℂ} {w : P.carrier} (hw : w ∈ P.isMod.weight α) (n : ℂ) (x : Q.carrier) :
    sqL N.isMod 0 (bracketModes Y n w x) - bracketModes Y n w (sqL Q.isMod 0 x) =
      bracketModes Y n (sqL P.isMod 0 w) x - (n + 1) • bracketModes Y n w x := by
  obtain ⟨KP, hKP⟩ := module_nat_bound P.isMod W.conformalVector w
  obtain ⟨KQ, hKQ⟩ := module_nat_bound Q.isMod W.conformalVector x
  obtain ⟨KN, hKN⟩ := module_nat_bound N.isMod W.conformalVector (bracketModes Y n w x)
  obtain ⟨S1, hS1⟩ := exists_uniform_bound
    (fun j s => Y.val (n + s) (mode (P.isMod.YM W.conformalVector) (j : ℤ) w) x)
    (fun j => intertwiner_nat_bound Y n _ x) KP
  obtain ⟨S2, hS2⟩ := exists_uniform_bound
    (fun k s => Y.val (n + s) w (roundL Q.isMod (k : ℤ) x))
    (fun k => intertwiner_nat_bound Y n w _) KQ
  obtain ⟨S3, hS3⟩ := intertwiner_nat_bound Y n w x
  have hSu : ∀ j : ℕ, ∀ s : ℕ, S1 + S2 + S3 ≤ s →
      Y.val (n + s) (mode (P.isMod.YM W.conformalVector) (j : ℤ) w) x = 0 := by
    intro j s hs
    by_cases hj : j < KP
    · exact hS1 j hj s (by omega)
    · rw [hKP j (by omega), map_zero, LinearMap.zero_apply]
  have hSw : ∀ s : ℕ, S1 + S2 + S3 ≤ s → Y.val (n + s) w x = 0 :=
    fun s hs => hS3 s (by omega)
  have hSq : ∀ k : ℕ, ∀ s : ℕ, S1 + S2 + S3 ≤ s →
      Y.val (n + s) w (roundL Q.isMod (k : ℤ) x) = 0 := by
    intro k s hs
    by_cases hk : k < KQ
    · exact hS2 k hk s (by omega)
    · have h0 : roundL Q.isMod (k : ℤ) x = 0 := by
        rw [roundL, show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring]
        exact hKQ _ (by omega)
      rw [h0, map_zero]
  -- the cutoffs
  have hL := sqL_zero_eq_sum N.isMod (bracketModes Y n w x) (KN + KQ + KP + (S1 + S2 + S3) + 1)
    (fun k hk => hKN k (by omega))
  have hQ := sqL_zero_eq_sum Q.isMod x (KN + KQ + KP + (S1 + S2 + S3) + 1)
    (fun k hk => hKQ k (by omega))
  have hP := sqL_zero_eq_sum P.isMod w (KN + KQ + KP + (S1 + S2 + S3) + 1)
    (fun k hk => hKP k (by omega))
  generalize hS : S1 + S2 + S3 = S at hSu hSw hSq hL hQ hP
  generalize hK : KN + KQ + KP + S + 1 = K at hL hQ hP
  have hK1 : 1 ≤ K := by omega
  have hKS : S ≤ K := by omega
  -- the left side
  have hLHS : sqL N.isMod 0 (bracketModes Y n w x) - bracketModes Y n w (sqL Q.isMod 0 x) =
      ∑ k ∈ Finset.range K, cc k • ∑ r ∈ Finset.range S, ∑ j ∈ Finset.range (k + 2),
        (bracketCoeff α n r * ((k + 1).choose j : ℂ)) •
          Y.val (n + ((r + k + 1 - j : ℕ) : ℂ))
            (mode (P.isMod.YM W.conformalVector) (j : ℤ) w) x := by
    rw [hL, hQ, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← smul_sub, comm_expand Y hw n x k S hSw (hSq k)]
  rw [hLHS]
  refine (regroup_j cc (bracketCoeff α n)
    (fun j m => Y.val (n + (m : ℂ)) (mode (P.isMod.YM W.conformalVector) (j : ℤ) w) x)
    K S hK1).trans ?_
  -- the `j = 0` and `j = 1` blocks
  have hZ0 : ∀ m : ℕ, Y.val (n + ((m + 1 : ℕ) : ℂ))
      (mode (P.isMod.YM W.conformalVector) ((0 : ℕ) : ℤ) w) x =
        (-(n + m + 1)) • Y.val (n + (m : ℂ)) w x := by
    intro m
    have h := Y.property.L_neg_one w (n + ((m + 1 : ℕ) : ℂ))
    have e : ((0 : ℕ) : ℤ) = 0 := rfl
    rw [e]
    change Y.val _ (P.isMod.Lm1 w) x = _
    rw [h, LinearMap.smul_apply]
    push_cast
    congr 1
    · ring
    · congr 1; ring_nf
  have hZ1 : ∀ m : ℕ, Y.val (n + (m : ℂ))
      (mode (P.isMod.YM W.conformalVector) ((1 : ℕ) : ℤ) w) x =
        α • Y.val (n + (m : ℂ)) w x := by
    intro m
    rw [show ((1 : ℕ) : ℤ) = 1 from rfl, P.isMod.L0_weight α w hw, map_smul,
      LinearMap.smul_apply]
  rw [Gblock_zero cc (bracketCoeff α n) _ (fun t => Y.val (n + (t : ℂ)) w x) n K S hZ0
      hSw hKS,
    Gblock_one cc (bracketCoeff α n) _ (fun t => Y.val (n + (t : ℂ)) w x) α K S hZ1 hSw hKS]
  have h01 : ∑ t ∈ Finset.range S,
        (∑ i ∈ Finset.range (t + 1), (cc i * ((i : ℂ) + 1)) * bracketCoeff α n (t - i)) •
          (α • Y.val (n + (t : ℂ)) w x) +
      ∑ t ∈ Finset.range S,
        (∑ i ∈ Finset.range (t + 1), cc i * bracketCoeff α n (t - i)) •
          ((-(n + t + 1)) • Y.val (n + (t : ℂ)) w x) =
      (α - n - 1) • bracketModes Y n w x := by
    rw [bracketModes_eq_sum_range Y hw n x S hSw, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_smul, smul_smul, ← add_smul, smul_smul]
    congr 1
    have hK := energy_scalar_K α n t
    simp only [mul_assoc] at hK ⊢
    linear_combination hK
  -- the `j = p + 2` blocks
  have hblock : ∀ p ∈ Finset.range (K - 1), Gblock cc (bracketCoeff α n)
      (fun j m => Y.val (n + (m : ℂ)) (mode (P.isMod.YM W.conformalVector) (j : ℤ) w) x)
      K S (p + 2) = cc (p + 1) •
        bracketModes Y n (mode (P.isMod.YM W.conformalVector) ((p + 2 : ℕ) : ℤ) w) x := by
    intro p _
    by_cases hp : p + 2 < KP
    · rw [Gblock_two cc (bracketCoeff α n) _ p K S (fun t ht => hSu (p + 2) t ht) (by omega)]
      have hwt : mode (P.isMod.YM W.conformalVector) ((p + 2 : ℕ) : ℤ) w ∈
          P.isMod.weight (α - (p + 1)) := by
        have := VOA.mode_mem_weight P.isMod W.conformal_mem hw ((p + 2 : ℕ) : ℤ)
        convert this using 2
        push_cast; ring
      rw [bracketModes_eq_sum_range Y hwt n x S (fun s hs => hSu (p + 2) s hs),
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [smul_smul]
      congr 1
      have hJ := energy_scalar_J α n p t
      push_cast at hJ ⊢
      rw [hJ]
    · have h0 : mode (P.isMod.YM W.conformalVector) ((p + 2 : ℕ) : ℤ) w = 0 :=
        hKP (p + 2) (by omega)
      rw [h0, map_zero, LinearMap.zero_apply, smul_zero, Gblock]
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun r _ => ?_
      rw [h0, map_zero, LinearMap.zero_apply, smul_zero]
  rw [Finset.sum_congr rfl hblock, add_assoc, h01]
  -- the right side
  rw [hP, map_sum, LinearMap.sum_apply]
  have hK' : K = (K - 1) + 1 := by omega
  rw [hK', Finset.sum_range_succ', ← hK']
  simp only [map_smul, LinearMap.smul_apply]
  rw [cc_zero, one_smul]
  have hr0 : roundL P.isMod ((0 : ℕ) : ℤ) w = α • w := by
    rw [roundL]; exact P.isMod.L0_weight α w hw
  rw [hr0, map_smul, LinearMap.smul_apply]
  have hr : ∀ p : ℕ, roundL P.isMod ((p + 1 : ℕ) : ℤ) w =
      mode (P.isMod.YM W.conformalVector) ((p + 2 : ℕ) : ℤ) w := by
    intro p; rw [roundL]; congr 1
  simp only [hr]
  module

end VOA.Huang.GenusOneG1f
