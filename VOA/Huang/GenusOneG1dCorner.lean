import VOA.Huang.GenusOneG1dInputs

/-!
# The three corners of the period cell, for insertions

Step (4c) of the proof of (G1). The proved genus-one theorems of
`GenusOneG1c*` (stated for one pair of `L(0)`-homogeneous insertions and the collision variable
`z₀`) are summed over the components of an `Insertion` and rewritten in the torus coordinate
`u = log(1 + z₀)` of the normalised product channel `prodN` (translation invariance
`exp_mul_prodLift`):

* `prodN_eq_vacF` (corner `0`, overlap): `prodN c x ins τ u = vacF c ins x τ u`;
* `prodN_acorner` (corner `−2πi`, Huang (4.10)):
  `prodN c x ins τ (u − 2πi) = e^{2πi h_b} (Ω_x vacF c ins x τ u + Σ_k aRem_k(u))`,
  `aRem_k` the `(a,b)`-orthogonal channels of the A-cycle remainder (`aRemChannel`);
* `prodN_bcorner` (corner `−2πiτ`, Huang (4.11)):
  `prodN c y ins τ (−u − 2πiτ) = Σ_z transferMatrix c β y z · revF π ins z τ u
   + Σ_{j,k} bRem_{jk}(u)`,
  `bRem` the `(b,a)`-orthogonal channels of the B-cycle remainder (`bRemChannel`).

All three hold for every insertion, every `τ`, and all small `u` with `Re(e^u − 1) > 0`.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1d

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.FusionProduct VOA.Huang.FusionUnit
  VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion VOA.Huang.GenusOneG1c CategoryTheory
  Complex
open VOA.Huang.GenusTwoPoint (vacuumLW)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## §1 Elementary bookkeeping -/

/-- One radius for finitely many components, in the torus coordinate. -/
theorem exists_delta_fin2 {m n : ℕ} (P : Fin m → Fin n → ℂ → Prop)
    (h : ∀ i j, ∃ δ : ℝ, 0 < δ ∧ ∀ z₀ : ℂ, 0 < z₀.re → ‖z₀‖ < δ → P i j z₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re → ∀ i j, P i j (exp u - 1) := by
  choose δ hδ hP using h
  have hrow : ∀ i, ∃ d : ℝ, 0 < d ∧ ∀ j, d ≤ δ i j := fun i => exists_pos_le_fin _ (hδ i)
  choose d hd hdle using hrow
  obtain ⟨e, he, hele⟩ := exists_pos_le_fin d hd
  refine ⟨min 1 (e / 2), lt_min one_pos (by positivity), min_le_left _ _, fun u hu hre i j => ?_⟩
  refine hP i j _ hre ?_
  have hu1 : ‖u‖ ≤ 1 := (lt_of_lt_of_le hu (min_le_left _ _)).le
  have hb := Complex.norm_exp_sub_one_le hu1
  have hu2 : ‖u‖ < e / 2 := lt_of_lt_of_le hu (min_le_right _ _)
  calc ‖exp u - 1‖ ≤ 2 * ‖u‖ := hb
    _ < e := by linarith
    _ ≤ d i := hele i
    _ ≤ δ i j := hdle i j

theorem log_exp_of_norm_lt_one {u : ℂ} (hu : ‖u‖ < 1) : log (exp u) = u := by
  have him : |u.im| < 1 := lt_of_le_of_lt (Complex.abs_im_le_norm u) hu
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  apply Complex.log_exp
  · linarith [neg_abs_le u.im]
  · linarith [le_abs_self u.im]

theorem one_add_exp_sub_one (u : ℂ) : 1 + (exp u - 1) = exp u := by ring

theorem sum3_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ x, ∑ y, f x y z := by
  calc ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ z, ∑ y, f x y z :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, f x y z := Finset.sum_comm

theorem sum4_comm {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ x, ∑ y, ∑ z, ∑ t, f x y z t = ∑ z, ∑ t, ∑ x, ∑ y, f x y z t := by
  calc ∑ x, ∑ y, ∑ z, ∑ t, f x y z t = ∑ x, ∑ z, ∑ y, ∑ t, f x y z t :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ z, ∑ t, ∑ y, f x y z t :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ t, ∑ y, f x y z t := Finset.sum_comm
    _ = ∑ z, ∑ t, ∑ x, ∑ y, f x y z t := Finset.sum_congr rfl fun z _ => Finset.sum_comm

theorem exp_two_pi_I_add_nat (h : ℂ) (n : ℕ) :
    exp (2 * (Real.pi : ℂ) * I * (h + n)) = exp (2 * (Real.pi : ℂ) * I * h) := by
  rw [mul_add, exp_add]
  have : exp (2 * (Real.pi : ℂ) * I * (n : ℂ)) = 1 := by
    rw [show 2 * (Real.pi : ℂ) * I * (n : ℂ) = ((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  rw [this, mul_one]

variable (F : FusionChoice W) (H : OrdinaryFourPointInput F) {D : VOA.ModularData W ι} {a b : ι}

/-- The A-cycle phase only depends on `γ` modulo `ℤ`. -/
theorem aPhase_add_nat (c : TransferChoice F D a b) (γ : ℂ) (n : ℕ) (x : ι) (j : Fin (c.r x)) :
    aPhase F c (γ + n) x j = aPhase F c γ x j := by
  unfold aPhase
  have : D.h (c.lab x j) - D.h x - (γ + n) =
      (D.h (c.lab x j) - D.h x - γ) + ((-(n : ℤ) : ℤ) : ℂ) := by
    push_cast; ring
  rw [this, mul_add, exp_add, show 2 * (Real.pi : ℂ) * I * ((-(n : ℤ) : ℤ) : ℂ) =
    ((-(n : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by ring, Complex.exp_int_mul_two_pi_mul_I,
    mul_one]

theorem aHom_add_nat (c : TransferChoice F D a b) (γ : ℂ) (n : ℕ) (x : ι) :
    aHom F H c (γ + n) x = aHom F H c γ x := by
  unfold aHom aTwist
  simp only [aPhase_add_nat]

/-! ## §2 The remainder channels -/

/-- The A-cycle remainder channel `k` (traced over `M_x`), `(a,b)`-orthogonal. -/
def aRemChannel (c : TransferChoice F D a b)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (hη' : η' ≫ c.ε = 𝟙 _) (γ : ℂ) (x : ι) {r : ℕ} (lab' : Fin r → ι)
    (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D a) (famObj D b))
    (p : ∀ k, tensorObj F (famObj D a) (famObj D b) ⟶ famObj D (lab' k)) (k : Fin r) :
    ABChannel F D a b η' where
  k := lab' k
  y := x
  q := aNonVac F c η' ≫ p k
  hq := eta_aRemInner F c hη' lab' p k
  Yout := aRemOuter F H c γ x lab' i k

/-- The B-cycle remainder channel `(j, k)` (traced over `M_{lab j}`), `(b,a)`-orthogonal. -/
def bRemChannel (c : TransferChoice F D a b)
    {π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject} (hπ : c.η ≫ π = 𝟙 _)
    (y : ι) {r : ℕ} (lab' : Fin r → ι)
    (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D b) (famObj D a))
    (p : ∀ k, tensorObj F (famObj D b) (famObj D a) ⟶ famObj D (lab' k))
    (j : Fin (c.r y)) (k : Fin r) : BAChannel F D a b c.η where
  k := lab' k
  y := c.lab y j
  q := nonVac F c π ≫ p k
  hq := eta_remInner F c hπ lab' p k
  Yout := remOuter F H c y j lab' i k

/-! ## §3 Corner `0`: the overlap -/

/-- **Corner `0`**: the product expansion equals the vacuum channel near the collision. -/
theorem prodN_eq_vacF (hV : StronglyRational W) (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
    (x : ι) (ins : Insertion D a b) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re →
      prodN F H c x ins τ u = vacF F hv c ins x τ u := by
  obtain ⟨δ, hδ, hδ1, h⟩ := exists_delta_fin2 (fun i j z₀ =>
    iterF (Q := vacuumLW W hv) (N := lwOf D x) (moduleIntertwiner (lwOf D x).isMod)
        (epsInt F c) (ins.wa i) (ins.wb j) (ins.αa i) (ins.αb j) τ z₀ =
      ∑ k, prodF (Q := lwOf D (c.lab x k)) (muInt F H c x k) (nuInt F c x k) (ins.wa i)
        (ins.wb j) (ins.αa i) (ins.αb j) τ (1 + z₀))
    (fun i j => by
      obtain ⟨δ, hδ, h⟩ := vacuumChannel_eq_product F H hV hv c x (ins.hwa i) (ins.hwb j) τ
      exact ⟨δ, hδ, fun z₀ hre hn => (h z₀ hre hn).2.2⟩)
  refine ⟨δ, hδ, fun u hu hre => ?_⟩
  have hlog : log (exp u) = u := log_exp_of_norm_lt_one (lt_of_lt_of_le hu hδ1)
  have hexp : exp u ≠ 0 := exp_ne_zero u
  unfold prodN vacF
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h u hu hre i j, one_add_exp_sub_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold cellF
  rw [← prodLift_log_one _ _ _ _ _ _ τ hexp, hlog]

/-! ## §4 Corner `−2πi`: the A-cycle -/

/-- **Corner `−2πi`** (Huang Lemma 4.2 (4.10)) for insertions. -/
theorem prodN_acorner (hV : StronglyRational W) (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (hη' : η' ≫ c.ε = 𝟙 _) {Ω : ι → ℂ} (hΩ : IsACycleScalar F H c η' (D.h b) Ω)
    {r : ℕ} (lab' : Fin r → ι)
    (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D a) (famObj D b))
    (p : ∀ k, tensorObj F (famObj D a) (famObj D b) ⟶ famObj D (lab' k))
    (htot : ∑ k, p k ≫ i k = 𝟙 _) (x : ι) (ins : Insertion D a b) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re →
      prodN F H c x ins τ (u - 2 * (Real.pi : ℂ) * I) =
        exp (2 * (Real.pi : ℂ) * I * D.h b) * (Ω x * vacF F hv c ins x τ u +
          ∑ k, (aRemChannel F H c hη' (D.h b) x lab' i p k).eval ins τ u) := by
  -- the per-component A-cycle theorem, with `γ = α_{b,j}` rewritten to `h_b`
  have hcomp : ∀ i' j', ∃ δ : ℝ, 0 < δ ∧ ∀ z₀ : ℂ, 0 < z₀.re → ‖z₀‖ < δ →
      ∑ k, GenusOneWard.prodLift (Q := lwOf D (c.lab x k)) (N := lwOf D x)
          (muInt F H c x k) (nuInt F c x k) (ins.wa i') (ins.wb j') (ins.αa i') (ins.αb j')
          (log (1 + z₀)) (2 * (Real.pi : ℂ) * I) τ =
        Ω x * iterF (Q := vacuumLW W hv) (N := lwOf D x) (moduleIntertwiner (lwOf D x).isMod)
          (epsInt F c) (ins.wa i') (ins.wb j') (ins.αa i') (ins.αb j') τ z₀ +
        ∑ k, iterF (Q := lwOf D (lab' k)) (N := lwOf D x) (aRemOuter F H c (D.h b) x lab' i k)
          (aRemInner F c η' lab' p k) (ins.wa i') (ins.wb j') (ins.αa i') (ins.αb j') τ z₀ := by
    intro i' j'
    obtain ⟨n, hn⟩ := ins.hlev j'
    have hΩ' : IsACycleScalar F H c η' (ins.αb j') Ω := by
      intro y
      rw [hn, aHom_add_nat]
      exact hΩ y
    have hR : ∀ k, aRemOuter F H c (ins.αb j') x lab' i k = aRemOuter F H c (D.h b) x lab' i k := by
      intro k
      unfold aRemOuter
      rw [hn, aHom_add_nat]
    obtain ⟨δ, hδ, h⟩ := acycle_vacuumChannel_complex F H hV hv c hΩ' lab' i p htot x
      (ins.hwa i') (ins.hwb j') τ
    refine ⟨δ, hδ, fun z₀ hre hnz => ?_⟩
    rw [h z₀ hre hnz]
    simp only [hR]
  obtain ⟨δ, hδ, hδ1, h⟩ := exists_delta_fin2 _ hcomp
  refine ⟨δ, hδ, fun u hu hre => ?_⟩
  have hlog : log (1 + (exp u - 1)) = u := by
    rw [one_add_exp_sub_one]; exact log_exp_of_norm_lt_one (lt_of_lt_of_le hu hδ1)
  have hcell : ∀ i' j' k, cellF (Q := lwOf D (c.lab x k)) (N := lwOf D x) (muInt F H c x k)
      (nuInt F c x k) (ins.wa i') (ins.wb j') (ins.αa i') (ins.αb j') τ
      (u - 2 * (Real.pi : ℂ) * I) =
      exp (ins.αa i' * u) * exp (2 * (Real.pi : ℂ) * I * D.h b) *
        GenusOneWard.prodLift (Q := lwOf D (c.lab x k)) (N := lwOf D x)
          (muInt F H c x k) (nuInt F c x k) (ins.wa i') (ins.wb j') (ins.αa i') (ins.αb j')
          (log (1 + (exp u - 1))) (2 * (Real.pi : ℂ) * I) τ := by
    intro i' j' k
    rw [hlog, ← exp_mul_prodLift]
    obtain ⟨n, hn⟩ := ins.hlev j'
    rw [exp_add]
    congr 2
    rw [hn, show ((D.h b + n : ℂ)) * (2 * (Real.pi : ℂ) * I) =
      2 * (Real.pi : ℂ) * I * (D.h b + n) by ring, exp_two_pi_I_add_nat]
  unfold prodN vacF ABChannel.eval
  simp only [hcell]
  have hsum : ∀ i' j', ∑ k, exp (ins.αa i' * u) * exp (2 * (Real.pi : ℂ) * I * D.h b) *
      GenusOneWard.prodLift (Q := lwOf D (c.lab x k)) (N := lwOf D x)
        (muInt F H c x k) (nuInt F c x k) (ins.wa i') (ins.wb j') (ins.αa i') (ins.αb j')
        (log (1 + (exp u - 1))) (2 * (Real.pi : ℂ) * I) τ =
      exp (2 * (Real.pi : ℂ) * I * D.h b) * (Ω x * (exp (ins.αa i' * u) *
        iterF (Q := vacuumLW W hv) (N := lwOf D x) (moduleIntertwiner (lwOf D x).isMod)
          (epsInt F c) (ins.wa i') (ins.wb j') (ins.αa i') (ins.αb j') τ (exp u - 1)) +
        ∑ k, exp (ins.αa i' * u) * iterF (Q := lwOf D (lab' k)) (N := lwOf D x)
          (aRemOuter F H c (D.h b) x lab' i k) (aRemInner F c η' lab' p k) (ins.wa i')
          (ins.wb j') (ins.αa i') (ins.αb j') τ (exp u - 1)) := by
    intro i' j'
    rw [← Finset.mul_sum, h u hu hre i' j', mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => hsum i' j']
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1
  exact sum3_comm _

/-! ## §5 Corner `−2πiτ`: the B-cycle -/

/-- **Corner `−2πiτ`** (Huang Lemma 4.2 (4.11)) for insertions: the reflected B-translate of
the near-collision point. -/
theorem prodN_bcorner (hV : StronglyRational W) (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
    {β : ∀ x, Fin (c.r x) → ℂ} (hβ : IsTransferScalar F H c β)
    {π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject} (hπ : c.η ≫ π = 𝟙 _)
    {r : ℕ} (lab' : Fin r → ι)
    (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D b) (famObj D a))
    (p : ∀ k, tensorObj F (famObj D b) (famObj D a) ⟶ famObj D (lab' k))
    (htot : ∑ k, p k ≫ i k = 𝟙 _) (y : ι) (ins : Insertion D a b) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re →
      prodN F H c y ins τ (-u - 2 * (Real.pi : ℂ) * I * τ) =
        ∑ z, transferMatrix c β y z * revF F hv π ins z τ u +
          ∑ j, ∑ k, (bRemChannel F H c hπ y lab' i p j k).eval ins τ u := by
  obtain ⟨δ, hδ, hδ1, h⟩ := exists_delta_fin2 _ (fun i' j' => by
    obtain ⟨δ, hδ, h⟩ := bcycle_vacuumChannel_complex F H hV hv c hβ π lab' i p htot y
      (ins.hwa i') (ins.hwb j') τ
    exact ⟨δ, hδ, fun z₀ hre hn => (h z₀ hre hn).2⟩)
  refine ⟨δ, hδ, fun u hu hre => ?_⟩
  have hlog : log (1 + (exp u - 1)) = u := by
    rw [one_add_exp_sub_one]; exact log_exp_of_norm_lt_one (lt_of_lt_of_le hu hδ1)
  have hcell : ∀ i' j' k, cellF (Q := lwOf D (c.lab y k)) (N := lwOf D y) (muInt F H c y k)
      (nuInt F c y k) (ins.wa i') (ins.wb j') (ins.αa i') (ins.αb j') τ
      (-u - 2 * (Real.pi : ℂ) * I * τ) =
      exp (ins.αb j' * u) * (exp (-(2 * (Real.pi : ℂ) * I * τ * ins.αa i')) *
        GenusOneWard.prodLift (Q := lwOf D (c.lab y k)) (N := lwOf D y)
          (muInt F H c y k) (nuInt F c y k) (ins.wa i') (ins.wb j') (ins.αa i') (ins.αb j')
          (-(2 * (Real.pi : ℂ) * I * τ)) (log (1 + (exp u - 1))) τ) := by
    intro i' j' k
    rw [hlog, show -u - 2 * (Real.pi : ℂ) * I * τ = -(2 * (Real.pi : ℂ) * I * τ) - u by ring,
      ← exp_mul_prodLift, ← mul_assoc, ← exp_add]
    congr 2
    ring
  unfold prodN revF BAChannel.eval
  simp only [hcell]
  have hsum : ∀ i' j', ∑ k, exp (ins.αb j' * u) * (exp (-(2 * (Real.pi : ℂ) * I * τ * ins.αa i')) *
      GenusOneWard.prodLift (Q := lwOf D (c.lab y k)) (N := lwOf D y)
        (muInt F H c y k) (nuInt F c y k) (ins.wa i') (ins.wb j') (ins.αa i') (ins.αb j')
        (-(2 * (Real.pi : ℂ) * I * τ)) (log (1 + (exp u - 1))) τ) =
      ∑ z, transferMatrix c β y z * (exp (ins.αb j' * u) *
        iterF (Q := vacuumLW W hv) (N := lwOf D z) (moduleIntertwiner (lwOf D z).isMod)
          (piInt F π) (ins.wb j') (ins.wa i') (ins.αb j') (ins.αa i') τ (exp u - 1)) +
      ∑ j, ∑ k, exp (ins.αb j' * u) * iterF (Q := lwOf D (lab' k)) (N := lwOf D (c.lab y j))
          (remOuter F H c y j lab' i k) (remInner F c π lab' p k) (ins.wb j') (ins.wa i')
          (ins.αb j') (ins.αa i') τ (exp u - 1) := by
    intro i' j'
    rw [← Finset.mul_sum, ← Finset.mul_sum, h u hu hre i' j', mul_add, Finset.mul_sum,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun z _ => by ring
    · exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => hsum i' j']
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · exact sum3_comm _
  · exact sum4_comm _

end VOA.Huang.GenusOneG1d
