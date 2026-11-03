import VOA.Huang.DLNSmallThreeAvg
import VOA.Huang.DLNSchur3Relations

/-!
# `SL₂(ℤ/3^k)` is Schur-trivial for every `k ≥ 1`

This proves `DLNSchur.ThreePowerSchur` (Beyl, Math. Z. 191 (1986), Thm 3.9 at `p = 3`),
in the homology-free form `SchurTrivial`.

Proof. The base case `SL₂(ℤ/3)` is `schurTrivial_SL_three`. For the step
`SL₂(ℤ/3^{k+1}) → SL₂(ℤ/3^k)` with layer `N`, the layer reduction
(`schurTrivial_of_layerTrivial`) leaves `⁅E, π⁻¹N⁆ ∩ ker π = 1`, proved by the averaging
criterion `layer_eq_one_of_averaging` with the quaternion group `Q₈ ⊂ SL₂(ℤ/3)`, `|Q₈| = 8`,
and `N` of exponent 3. Its key hypothesis — lifts of the level-one kernel `K₁` centralize
`π⁻¹N` — is proved with the commutator pairing of lifts, using conjugation by `x(1)` and
`y(1)` on the generators `x(3), y(3), t₄` of `K₁` and `n_e, n_f, n_h` of `N`.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

/-! ## Commutation propagates through generated subgroups -/

theorem commute_of_mem_closure {G E : Type*} [Group G] [Group E] (π : E →* G)
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E) (A B : Set G)
    (h : ∀ a ∈ A, ∀ b ∈ B, ∀ e m : E, π e = a → π m = b → Commute e m) :
    ∀ e m : E, π e ∈ Subgroup.closure A → π m ∈ Subgroup.closure B → Commute e m := by
  -- First propagate in the second argument.
  have hB : ∀ a ∈ A, ∀ b ∈ Subgroup.closure B, ∀ e m : E, π e = a → π m = b → Commute e m := by
    intro a ha b hb
    induction hb using Subgroup.closure_induction with
    | mem b hb => exact h a ha b hb
    | one =>
      intro e m _ hm
      exact (Subgroup.mem_center_iff.mp (hc hm) e)
    | mul b b' _ _ ih ih' =>
      intro e m he hm
      obtain ⟨m₁, hm₁⟩ := hs b
      have hm₂ : π (m₁⁻¹ * m) = b' := by rw [map_mul, map_inv, hm₁, hm]; group
      have : m = m₁ * (m₁⁻¹ * m) := by group
      rw [this]
      exact (ih e m₁ he hm₁).mul_right (ih' e _ he hm₂)
    | inv b _ ih =>
      intro e m he hm
      have := ih e m⁻¹ he (by rw [map_inv, hm, inv_inv])
      simpa using this.inv_right
  intro e m he hm
  revert e m
  suffices ∀ a ∈ Subgroup.closure A, ∀ e m : E, π e = a → π m ∈ Subgroup.closure B →
      Commute e m by
    intro e m he hm; exact this _ he e m rfl hm
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem a ha => intro e m he hm; exact hB a ha _ hm e m he rfl
  | one =>
    intro e m he _
    exact (Subgroup.mem_center_iff.mp (hc he) m).symm
  | mul a a' _ _ ih ih' =>
    intro e m he hm
    obtain ⟨e₁, he₁⟩ := hs a
    have he₂ : π (e₁⁻¹ * e) = a' := by rw [map_mul, map_inv, he₁, he]; group
    have : e = e₁ * (e₁⁻¹ * e) := by group
    rw [this]
    exact (ih e₁ m he₁ hm).mul_left (ih' _ m he₂ hm)
  | inv a _ ih =>
    intro e m he hm
    have := ih e⁻¹ m (by rw [map_inv, he, inv_inv]) hm
    simpa using this.inv_left

/-! ## Conjugation identities at level `3^{k+1}` -/

section Three

variable {k : ℕ}

theorem u_conj_nF (hk : 1 ≤ k) :
    upperRoot 1 * nF k * (upperRoot 1)⁻¹ = (nE k)⁻¹ * nF k * nH k :=
  layer_conj_upper_lower _ (three_pow_mul_self hk) _ (fourU_pow_val hk)

theorem u_conj_nH (hk : 1 ≤ k) : upperRoot 1 * nH k * (upperRoot 1)⁻¹ = nE k * nH k :=
  layer_conj_upper_torus _ (three_pow_mul_self hk) (three_mul_three_pow k) _ (fourU_pow_val hk)

theorem v_conj_nE (hk : 1 ≤ k) :
    lowerRoot 1 * nE k * (lowerRoot 1)⁻¹ = nE k * (nF k)⁻¹ * (nH k)⁻¹ := by
  rw [layer_conj_lower_upper _ (three_pow_mul_self hk) _ (fourU_pow_val hk)]

theorem v_conj_nH (hk : 1 ≤ k) : lowerRoot 1 * nH k * (lowerRoot 1)⁻¹ = (nF k)⁻¹ * nH k :=
  layer_conj_lower_torus _ (three_pow_mul_self hk) (three_mul_three_pow k) _ (fourU_pow_val hk)

/-- The unit `-5 · 4⁻²`. -/
noncomputable def wU (k : ℕ) : (ZMod (3 ^ (k + 1)))ˣ := -(fiveU k) * (fourU k)⁻¹ ^ 2

theorem u_conj_t4 :
    upperRoot 1 * t4 k * (upperRoot 1)⁻¹ =
      t4 k * upperRoot (3 * ((wU k : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1)))) := by
  rw [conj_upper_one_torus]
  congr 2
  set i : ZMod (3 ^ (k + 1)) := ((((fourU k)⁻¹ : (ZMod (3 ^ (k + 1)))ˣ)) : ZMod (3 ^ (k + 1)))
    with hi
  have h4i : 4 * i = 1 := by rw [hi, ← fourU_val (k := k)]; simp
  simp only [wU, Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val, fiveU_val, ← hi]
  linear_combination (4 * i + 1) * h4i

theorem v_conj_t4 :
    lowerRoot 1 * t4 k * (lowerRoot 1)⁻¹ = t4 k * lowerRoot (3 * 5) := by
  rw [conj_lower_one_torus, fourU_val]
  norm_num

theorem x3_eq_pow : x3 k = upperRoot (3 * ((wU k : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1)))) ^
    (((wU k)⁻¹ : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))).val := by
  show (upperRoot (3 : ZMod (3 ^ (k + 1))) : SLL k) = _
  rw [upperRoot_pow, ZMod.natCast_zmod_val]
  congr 1
  rw [mul_left_comm, Units.inv_mul, mul_one]

theorem xc_eq_pow : upperRoot (3 * ((wU k : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1)))) =
    x3 k ^ ((wU k : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))).val := by
  rw [upperRoot_pow, ZMod.natCast_zmod_val, mul_comm]

theorem y3_eq_pow : y3 k = lowerRoot (3 * 5 : ZMod (3 ^ (k + 1))) ^
    (((fiveU k)⁻¹ : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))).val := by
  show (lowerRoot (3 : ZMod (3 ^ (k + 1))) : SLL k) = _
  rw [lowerRoot_pow, ZMod.natCast_zmod_val]
  congr 1
  have : (((fiveU k)⁻¹ : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))) * 5 = 1 := by
    rw [← fiveU_val (k := k)]; simp
  linear_combination (-3) * this

theorem yc_eq_pow : (lowerRoot ((3 : ZMod (3 ^ (k + 1))) * 5) : SLL k) = y3 k ^ 5 := by
  rw [lowerRoot_pow]; congr 1; push_cast; ring

/-! ## Lifts of the level-one kernel centralize the layer -/

theorem levelOne_lifts_centralize (hk : 1 ≤ k) {E : Type*} [Group E] (π : E →* SLL k)
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E) :
    ∀ e m : E, rhoOne k (π e) = 1 → π m ∈ layerN k → Commute e m := by
  intro e m he hm
  refine commute_of_mem_closure π hs hc {x3 k, y3 k, t4 k} {nE k, nF k, nH k} ?_ e m
    (levelOne_le_closure hk he) (layerN_le_closure hk hm)
  have hcm : ∀ a ∈ levelOne k, ∀ b ∈ layerN k, Commute a b :=
    fun a ha b hb => levelOne_commute_layerN ha hb
  have hof : ∀ a b : SLL k, (∀ x y : E, π x = a → π y = b → Commute x y) → liftPair π hs a b = 1 :=
    fun a b h => liftPair_eq_one_of_commute hc (Function.surjInv_eq hs a)
      (Function.surjInv_eq hs b) (h _ _ (Function.surjInv_eq hs a) (Function.surjInv_eq hs b))
  -- Members.
  set X := x3 k
  set Y := y3 k
  set T := t4 k
  set NE := nE k
  set NF := nF k
  set NH := nH k
  set Xc := upperRoot (3 * ((wU k : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))))
  set Yc := lowerRoot (3 * 5 : ZMod (3 ^ (k + 1)))
  have hX : X ∈ levelOne k := x3_mem_levelOne
  have hY : Y ∈ levelOne k := y3_mem_levelOne
  have hT : T ∈ levelOne k := t4_mem_levelOne
  have hXc : Xc ∈ levelOne k := upperRoot_three_mul_mem_levelOne _
  have hYc : Yc ∈ levelOne k := lowerRoot_three_mul_mem_levelOne _
  have hNE : NE ∈ layerN k := nE_mem_layerN
  have hNF : NF ∈ layerN k := nF_mem_layerN
  have hNH : NH ∈ layerN k := nH_mem_layerN hk
  have hNEi : NE⁻¹ ∈ layerN k := inv_mem hNE
  have hNFi : NF⁻¹ ∈ layerN k := inv_mem hNF
  have hNHi : NH⁻¹ ∈ layerN k := inv_mem hNH
  -- s1, s2, s3: commuting lifts.
  have s1 : liftPair π hs X NE = 1 := hof _ _ (fun x y hx hy => upper_lifts_commute π hs hc hx hy)
  have s2 : liftPair π hs Y NF = 1 := hof _ _ (fun x y hx hy => lower_lifts_commute π hs hc hx hy)
  have s3 : liftPair π hs T NH = 1 := hof _ _ (fun x y hx hy =>
    commute_of_images_powers π hc x y (Function.surjInv hs T) 1 (3 ^ (k - 1))
      (by rw [hx, Function.surjInv_eq hs, pow_one])
      (by rw [hy, Function.surjInv_eq hs]; exact nH_eq_pow))
  have hXcNE : liftPair π hs Xc NE = 1 := hof _ _ (fun x y hx hy => upper_lifts_commute π hs hc hx hy)
  have hYcNF : liftPair π hs Yc NF = 1 := hof _ _ (fun x y hx hy => lower_lifts_commute π hs hc hx hy)
  -- s4: `x(3)` against `n_h`.
  have s4 : liftPair π hs X NH = 1 := by
    have h := liftPair_conj (hs := hs) hc (hcm X hX NF hNF) (upperRoot 1)
    rw [upperRoot_conj_upperRoot, u_conj_nF hk, liftPair_mul_right hc (hcm X hX NH hNH),
      liftPair_mul_right hc (hcm X hX NF hNF), liftPair_inv_right hc (hcm X hX NE hNE), s1,
      inv_one, one_mul, mul_eq_left] at h
    exact h
  have hXcNH : liftPair π hs Xc NH = 1 := by
    rw [show Xc = X ^ _ from xc_eq_pow, liftPair_pow_left hc (hcm X hX NH hNH), s4, one_pow]
  -- s5: `t₄` against `n_e`.
  have s5 : liftPair π hs T NE = 1 := by
    have h := liftPair_conj (hs := hs) hc (hcm T hT NH hNH) (upperRoot 1)
    rw [u_conj_t4, u_conj_nH hk, s3,
      liftPair_mul_left hc (hcm Xc hXc _ (mul_mem hNE hNH)),
      liftPair_mul_right hc (hcm T hT NH hNH), liftPair_mul_right hc (hcm Xc hXc NH hNH),
      s3, hXcNE, hXcNH, mul_one, mul_one, mul_one] at h
    exact h
  -- s6: `x(3)` against `n_f`.
  have s6 : liftPair π hs X NF = 1 := by
    have h := liftPair_conj (hs := hs) hc (hcm T hT NF hNF) (upperRoot 1)
    rw [u_conj_t4, u_conj_nF hk,
      liftPair_mul_left hc (hcm Xc hXc _ (mul_mem (mul_mem hNEi hNF) hNH)),
      liftPair_mul_right hc (hcm T hT NH hNH), liftPair_mul_right hc (hcm T hT NF hNF),
      liftPair_inv_right hc (hcm T hT NE hNE),
      liftPair_mul_right hc (hcm Xc hXc NH hNH), liftPair_mul_right hc (hcm Xc hXc NF hNF),
      liftPair_inv_right hc (hcm Xc hXc NE hNE), s5, s3, hXcNE, hXcNH,
      inv_one, one_mul, mul_one, one_mul, mul_one, mul_eq_left] at h
    rw [show X = Xc ^ _ from x3_eq_pow, liftPair_pow_left hc (hcm Xc hXc NF hNF), h, one_pow]
  -- s7: `y(3)` against `n_h`.
  have s7 : liftPair π hs Y NH = 1 := by
    have h := liftPair_conj (hs := hs) hc (hcm Y hY NE hNE) (lowerRoot 1)
    rw [lowerRoot_conj_lowerRoot, v_conj_nE hk, liftPair_mul_right hc (hcm Y hY _ hNHi),
      liftPair_mul_right hc (hcm Y hY _ hNFi), liftPair_inv_right hc (hcm Y hY NF hNF),
      liftPair_inv_right hc (hcm Y hY NH hNH), s2, inv_one, mul_one, mul_eq_left,
      inv_eq_one] at h
    exact h
  have hYcNH : liftPair π hs Yc NH = 1 := by
    rw [show Yc = Y ^ 5 from yc_eq_pow, liftPair_pow_left hc (hcm Y hY NH hNH), s7, one_pow]
  -- s8: `t₄` against `n_f`.
  have s8 : liftPair π hs T NF = 1 := by
    have h := liftPair_conj (hs := hs) hc (hcm T hT NH hNH) (lowerRoot 1)
    rw [v_conj_t4, v_conj_nH hk, s3,
      liftPair_mul_left hc (hcm Yc hYc _ (mul_mem hNFi hNH)),
      liftPair_mul_right hc (hcm T hT NH hNH), liftPair_mul_right hc (hcm Yc hYc NH hNH),
      liftPair_inv_right hc (hcm T hT NF hNF), liftPair_inv_right hc (hcm Yc hYc NF hNF),
      s3, hYcNF, hYcNH, inv_one, mul_one, mul_one, mul_one, inv_eq_one] at h
    exact h
  -- s9: `y(3)` against `n_e`.
  have s9 : liftPair π hs Y NE = 1 := by
    have h := liftPair_conj (hs := hs) hc (hcm T hT NE hNE) (lowerRoot 1)
    rw [v_conj_t4, v_conj_nE hk, s5,
      liftPair_mul_left hc (hcm Yc hYc _ (mul_mem (mul_mem hNE hNFi) hNHi)),
      liftPair_mul_right hc (hcm T hT _ hNHi), liftPair_mul_right hc (hcm T hT _ hNFi),
      liftPair_inv_right hc (hcm T hT NF hNF), liftPair_inv_right hc (hcm T hT NH hNH),
      liftPair_mul_right hc (hcm Yc hYc _ hNHi), liftPair_mul_right hc (hcm Yc hYc _ hNFi),
      liftPair_inv_right hc (hcm Yc hYc NF hNF), liftPair_inv_right hc (hcm Yc hYc NH hNH),
      s5, s8, s3, hYcNF, hYcNH, inv_one, mul_one, mul_one, one_mul, mul_one, mul_one] at h
    rw [show Y = Yc ^ _ from y3_eq_pow, liftPair_pow_left hc (hcm Yc hYc NE hNE), h, one_pow]
  -- Conclude on generators.
  have key : ∀ a ∈ ({X, Y, T} : Set (SLL k)), ∀ b ∈ ({NE, NF, NH} : Set (SLL k)), liftPair π hs a b = 1 := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> assumption
  intro a ha b hb x y hx hy
  exact commute_of_liftPair_eq_one hc (key a ha b hb) hx hy

theorem rhoOne_surjective (k : ℕ) : Function.Surjective (rhoOne k) := by
  intro g
  obtain ⟨γ, rfl⟩ := reduction_surjective 3 g
  refine ⟨VOA.Huang.DLN.reduction (3 ^ (k + 1)) γ, ?_⟩
  have := congrArg (fun f => f γ) (reductionMod_comp_reduction (3 ^ (k + 1)) 3
    (dvd_pow_self 3 (Nat.succ_ne_zero k)))
  exact this

theorem rhoTop_surjective (k : ℕ) : Function.Surjective (rhoTop k) := by
  intro g
  obtain ⟨γ, rfl⟩ := reduction_surjective (3 ^ k) g
  refine ⟨VOA.Huang.DLN.reduction (3 ^ (k + 1)) γ, ?_⟩
  have := congrArg (fun f => f γ) (reductionMod_comp_reduction (3 ^ (k + 1)) (3 ^ k)
    (pow_dvd_pow 3 (Nat.le_succ k)))
  exact this

/-- **The layer condition for `SL₂(ℤ/3^{k+1}) → SL₂(ℤ/3^k)`, `k ≥ 1`.** -/
theorem layerTrivial_three (hk : 1 ≤ k) : LayerTrivial (rhoTop k) := by
  intro E _ π hs hc x hx hπx
  exact layer_eq_one_of_averaging π hs hc (layerN k) (rhoOne k) (rhoOne_surjective k)
    (layerN_le_levelOne hk) (levelOne_lifts_centralize hk π hs hc) quatFinset quatFinset_conj 3
    (fun n hn => layerN_pow_three hk hn) (by rw [quatFinset_card]; norm_num)
    (fun g hg n hn => layer_quat_average hk g hg n hn) x hx hπx

end Three

/-- **Beyl's theorem at `p = 3`.** `SL₂(ℤ/3^k)` has trivial Schur multiplier, in the
homology-free form `SchurTrivial`, for every `k ≥ 1`. -/
theorem threePowerSchur : ThreePowerSchur := by
  have key : ∀ k : ℕ, 1 ≤ k →
      SchurTrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod (3 ^ k))) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simpa using schurTrivial_SL_three
    | succ k hk ih =>
      exact schurTrivial_of_layerTrivial (rhoTop k) (rhoTop_surjective k) ih
        (layerTrivial_three hk)
  intro k hk
  exact key k hk

end VOA.Huang.DLNSchur
