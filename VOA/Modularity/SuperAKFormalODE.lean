import VOA.Modularity.SuperFormalBlock
import VOA.Modularity.AKUniformODE

namespace VOA

namespace SuperAK

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## (A)  The Virasoro tower over a primary vector, with the **exact** scalar -/

/-- **The exact scalar of AK's Virasoro relation.**  `towerScalar Δ c j n` is the `γ` in
`L[2j] L[−2]^n a = γ · L[−2]^{n−j} a` for `a` square-bracket primary of weight `Δ` in a VOA of
central charge `c`.  Translating to AK's indices (`j = k − 1`, `n = i − 1`), `c_k =
towerScalar Δ c (k−1) (i−1)`.

The recursion is read off the Virasoro relation `⁅L[m],L[n]⁆ = (m−n)L[m+n] +
δ_{m+n,0}((m³−m)/12)c`:

* `γ(0, 0) = Δ` and `γ(j, 0) = 0` for `j ≥ 1`  (that is `L[0]a = Δa`, `L[2j]a = 0`);
* `γ(0, n+1) = γ(0, n) + 2`  (that is: `L[−2]^n a` has square weight `Δ + 2n`);
* `γ(j+1, n+1) = (2j+4)·γ(j, n) + δ_{j,0}·c/2 + γ(j+1, n)`.

⚠ Note that `c_k` depends on `i` as well as on `k`; AK suppress that.  Sanity check: at `Δ = 0`,
`i = 2`, `k = 2` this gives `L[2]L[−2]|0⟩ = (c/2)|0⟩`. -/
noncomputable def towerScalar (Δ c : ℂ) : ℕ → ℕ → ℂ
  | j, 0 => if j = 0 then Δ else 0
  | 0, (n + 1) => towerScalar Δ c 0 n + 2
  | (j + 1), (n + 1) =>
      (2 * (j : ℂ) + 4) * towerScalar Δ c j n
        + (if j = 0 then c / 2 else 0) + towerScalar Δ c (j + 1) n

@[simp] theorem towerScalar_zero_right (Δ c : ℂ) (j : ℕ) :
    towerScalar Δ c j 0 = if j = 0 then Δ else 0 := by
  cases j <;> rw [towerScalar]

@[simp] theorem towerScalar_zero_succ (Δ c : ℂ) (n : ℕ) :
    towerScalar Δ c 0 (n + 1) = towerScalar Δ c 0 n + 2 := by rw [towerScalar]

@[simp] theorem towerScalar_succ_succ (Δ c : ℂ) (j n : ℕ) :
    towerScalar Δ c (j + 1) (n + 1)
      = (2 * (j : ℂ) + 4) * towerScalar Δ c j n
        + (if j = 0 then c / 2 else 0) + towerScalar Δ c (j + 1) n := by rw [towerScalar]

/-- **The vanishing clause** — AK's "`L[2k−2]L[−2]^{i−1}a = 0` if `k ≥ i + 1`".  Carrying it as
part of the induction is *required*: without it the step breaks at `n = 0`, `j = 1`, where
`ℕ`-subtraction makes `n − j + 1 ≠ n + 1 − j`. -/
theorem towerScalar_eq_zero_of_lt (Δ c : ℂ) : ∀ {n j : ℕ}, n < j → towerScalar Δ c j n = 0 := by
  intro n
  induction n with
  | zero =>
      intro j hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [towerScalar_zero_right, if_neg (by omega)]
  | succ n ih =>
      intro j hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [towerScalar_succ_succ, ih (by omega : n < j'), ih (by omega : n < j' + 1),
        if_neg (by omega : ¬ j' = 0)]
      ring

/-! ### Closed forms — the scalar is *computed*, not guessed

Three checks against the Virasoro algebra, each of them a theorem below. -/

/-- `γ(0, n) = Δ + 2n`: the vector `L[−2]^n a` has square-bracket `L[0]`-weight `Δ + 2n`. -/
theorem towerScalar_zero_left (Δ c : ℂ) (n : ℕ) : towerScalar Δ c 0 n = Δ + 2 * (n : ℂ) := by
  induction n with
  | zero => simp
  | succ k ih => rw [towerScalar_zero_succ, ih]; push_cast; ring

/-- `γ(1, n) = n·(4Δ + 4n − 4 + c/2)`.  In AK's indices this is the closed form of `c_2`, the
scalar of `L[2]L[−2]^{i−1}a = c_2 · L[−2]^{i−2}a`: with `n = i − 1`,
`c_2 = (i−1)(4Δ + 4(i−2) + c/2)`.  ⚠ It depends on `i` as well as on `k`; AK suppress that. -/
theorem towerScalar_one_left (Δ c : ℂ) (n : ℕ) :
    towerScalar Δ c 1 n = (n : ℂ) * (4 * Δ + 4 * (n : ℂ) - 4 + c / 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [towerScalar_succ_succ, towerScalar_zero_left, ih]
      push_cast
      ring

/-- The base check: `L[2]L[−2]a = (4Δ + c/2)·a`, which is `⁅L[2],L[−2]⁆a = 4L[0]a + (c/2)a` since
`L[2]a = 0`.  At `Δ = 0` — the vacuum — this is the familiar `L[2]L[−2]|0⟩ = (c/2)|0⟩`. -/
theorem towerScalar_one_one (Δ c : ℂ) : towerScalar Δ c 1 1 = 4 * Δ + c / 2 := by
  rw [towerScalar_one_left]; push_cast; ring

/-- **AK's Virasoro-tower relation, with the exact scalar.**  For `a` square-bracket primary of
weight `Δ`,

  `L[2j] L[−2]^n a = towerScalar Δ c j n · L[−2]^{n−j} a`,

which for `j > n` reads `= 0` by `towerScalar_eq_zero_of_lt`.  In AK's indexing (`j = k − 1`,
`n = i − 1`) this is exactly "`L[2k−2]L[−2]^{i−1}a = c_k · L[−2]^{i−k}a` for `2 ≤ k ≤ i`, and `0`
for `k ≥ i+1`".

This is the technical heart of Lemma 5.5, and it is where **primarity is used**: the tail of the
`ω`-law lands back in the *same* `L[−2]`-tower.  For a non-primary `v` it does not — which is the
content of `Modularity.UniCollapse`. -/
theorem Lsq_tower (W : SuperVertexOperatorAlgebra 𝒱) {a : 𝒱} {Δ : ℂ} (ha : W.toSuperNearVOA.IsSuperSqPrimary a Δ) :
    ∀ (n j : ℕ), W.toSuperNearVOA.superLsq (2 * (j : ℤ)) ((⇑(W.toSuperNearVOA.superLsq (-2)))^[n] a)
      = towerScalar Δ W.centralCharge j n • ((⇑(W.toSuperNearVOA.superLsq (-2)))^[n - j] a) := by
  obtain ⟨h0, hp⟩ := ha
  intro n
  induction n with
  | zero =>
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa using h0
      · rw [towerScalar_zero_right, if_neg (by omega), zero_smul]
        exact hp (2 * (j : ℤ)) (by omega)
  | succ n ih =>
      intro j
      set y : 𝒱 := (⇑(W.toSuperNearVOA.superLsq (-2)))^[n] a with hy
      have hsucc : (⇑(W.toSuperNearVOA.superLsq (-2)))^[n + 1] a = W.toSuperNearVOA.superLsq (-2) y := by
        rw [hy, Function.iterate_succ_apply']
      have hγa := ih j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · -- `j = 0`: the `L[0]`-weight step, `γ ↦ γ + 2`
        have hv := W.toSuperNearVOA.superLsq_virasoro_apply 0 (-2) y
        rw [if_neg (by omega : ¬((0 : ℤ) + (-2) = 0)), zero_smul, add_zero,
          show ((0 : ℤ) + (-2)) = -2 from by ring, sub_eq_iff_eq_add] at hv
        simp only [Nat.cast_zero, mul_zero, Nat.sub_zero] at hγa ⊢
        rw [hsucc, hv, hγa, map_smul, ← hsucc, towerScalar_zero_succ]
        push_cast
        module
      · -- `j ≥ 1`
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hγb := ih j'
        have hLidx : W.toSuperNearVOA.superLsq (2 * ((j' + 1 : ℕ) : ℤ) + (-2)) = W.toSuperNearVOA.superLsq (2 * (j' : ℤ)) := by
          congr 1; push_cast; ring
        have hidx2 : n - j' = n + 1 - (j' + 1) := by omega
        have hv := W.toSuperNearVOA.superLsq_virasoro_apply (2 * ((j' + 1 : ℕ) : ℤ)) (-2) y
        rw [sub_eq_iff_eq_add, hLidx, hγb, hidx2] at hv
        have hA : W.toSuperNearVOA.superLsq (-2) (W.toSuperNearVOA.superLsq (2 * ((j' + 1 : ℕ) : ℤ)) y)
            = towerScalar Δ W.centralCharge (j' + 1) n
                • ((⇑(W.toSuperNearVOA.superLsq (-2)))^[n + 1 - (j' + 1)] a) := by
          rw [hγa, map_smul]
          rcases Nat.lt_or_ge n (j' + 1) with hjn | hjn
          · rw [towerScalar_eq_zero_of_lt Δ W.centralCharge hjn, zero_smul, zero_smul]
          · rw [show n + 1 - (j' + 1) = (n - (j' + 1)) + 1 from by omega,
              Function.iterate_succ_apply']
        rw [hA] at hv
        have hδ : (if 2 * ((j' + 1 : ℕ) : ℤ) + (-2) = 0 then
              (((2 * ((j' + 1 : ℕ) : ℤ) : ℤ) : ℂ) ^ 3 - ((2 * ((j' + 1 : ℕ) : ℤ) : ℤ) : ℂ)) / 12
                * W.toSuperNearVOA.centralCharge else 0) • y
            = (if j' = 0 then W.centralCharge / 2 else 0)
                • ((⇑(W.toSuperNearVOA.superLsq (-2)))^[n + 1 - (j' + 1)] a) := by
          rcases Nat.eq_zero_or_pos j' with rfl | hj'
          · rw [if_pos (by norm_num), if_pos rfl, hy,
              show n + 1 - (0 + 1) = n from by omega]
            push_cast
            norm_num
            module
          · rw [if_neg (by push_cast; omega), if_neg (by omega), zero_smul, zero_smul]
        rw [hsucc, hv, hδ, towerScalar_succ_succ]
        push_cast
        module

/-! ## (C)  AK Lemma 5.5 — the unitriangular conversion, for a primary vector

The proof runs inside `QSeriesAt hbase`, where `psSMul` is a genuine module action, and it is
organised as a **span** statement rather than an explicit coefficient recursion: writing `d j` for
the `j`-th `q d/dq`-iterate of `S a` and `Sp i` for the `SubexpPS`-span of `d 0, …, d (i−1)`, the
whole of Lemma 5.5 is

  `S(L[−2]^i a) − d i ∈ Sp i`.

Unitriangularity (`hc i = 1`, `hc j = 0` for `j > i`) is then automatic from the shape, and the
explicit coefficient list is read off at the very end. -/

/-- The `q d/dq`-tower over a block value: `qTower hsupp a j` is `(q d/dq)^j (S a)`, as an element
of `QSeriesAt hbase`. -/
noncomputable def qTower {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (a : 𝒱) (j : ℕ) : ↥(QSeriesAt hbase) :=
  (qD hbase)^[j] (blockRestrict hsupp a)

theorem qTower_zero {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (a : 𝒱) :
    qTower hsupp a 0 = blockRestrict hsupp a := rfl

theorem qTower_succ {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (a : 𝒱) (j : ℕ) :
    qTower hsupp a (j + 1) = qD hbase (qTower hsupp a j) :=
  Function.iterate_succ_apply' _ _ _

theorem qTower_coe {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (a : 𝒱) (j : ℕ) :
    ((qTower hsupp a j : ↥(QSeriesAt hbase)) : FormalQSeries) = qDeriv^[j] (S a) := by
  induction j with
  | zero => rfl
  | succ k ih => rw [qTower_succ, qD_coe, ih, Function.iterate_succ_apply']

/-- The `SubexpPS`-span of the first `i` rungs `d 0, …, d (i−1)` of the `q d/dq`-tower. -/
noncomputable def qTowerSpan {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (a : 𝒱) (i : ℕ) :
    Submodule (↥SubexpPS) ↥(QSeriesAt hbase) :=
  Submodule.span (↥SubexpPS) (Set.range (fun j : Fin i => qTower hsupp a (j : ℕ)))

theorem qTower_mem_qTowerSpan {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (a : 𝒱) {i j : ℕ} (h : j < i) :
    qTower hsupp a j ∈ qTowerSpan hsupp a i :=
  Submodule.subset_span ⟨⟨j, h⟩, rfl⟩

theorem qTowerSpan_mono {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (a : 𝒱) {i i' : ℕ} (h : i ≤ i') :
    qTowerSpan hsupp a i ≤ qTowerSpan hsupp a i' := by
  rw [qTowerSpan, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact qTower_mem_qTowerSpan hsupp a (by omega : (j : ℕ) < i')

/-- A `SubexpPS`-submodule of `QSeriesAt hbase` is closed under the ambient `ℂ`-action, because
`ℂ → SubexpPS` and the scalar tower `IsScalarTower ℂ SubexpPS (QSeriesAt hbase)` holds. -/
theorem complex_smul_mem_span_subexpPS {hbase : ℂ} (c : ℂ) {X : Set ↥(QSeriesAt hbase)}
    {x : ↥(QSeriesAt hbase)} (hx : x ∈ Submodule.span (↥SubexpPS) X) :
    c • x ∈ Submodule.span (↥SubexpPS) X := by
  have hrw : c • x = ((c • (1 : ↥SubexpPS)) : ↥SubexpPS) • x := by rw [smul_assoc, one_smul]
  rw [hrw]
  exact Submodule.smul_mem _ _ hx

/-- **`q d/dq` raises the tower span by one rung.**  On a generator this is
`qD (d j) = d (j+1)`; on a `SubexpPS`-multiple it is the product rule
`qD (F ⋆ z) = F ⋆ qD z + (θF) ⋆ z` together with `θ`-stability of `SubexpPS`
(`Modularity.QDerivProductRule.theta_mem_subexpPS`). -/
theorem qD_mem_qTowerSpan {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (a : 𝒱) (i : ℕ)
    {z : ↥(QSeriesAt hbase)} (hz : z ∈ qTowerSpan hsupp a i) :
    qD hbase z ∈ qTowerSpan hsupp a (i + 1) := by
  refine Submodule.span_induction
    (p := fun z _ => qD hbase z ∈ qTowerSpan hsupp a (i + 1)) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨j, rfl⟩
    rw [← qTower_succ]
    exact qTower_mem_qTowerSpan hsupp a (by omega : (j : ℕ) + 1 < i + 1)
  · simp only [map_zero]
    exact Submodule.zero_mem (qTowerSpan hsupp a (i + 1))
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro F y hymem hy
    have hprod : qD hbase ((F : ↥SubexpPS) • y)
        = F • qD hbase y
          + (⟨theta (F : PowerSeries ℂ), theta_mem_subexpPS F.2⟩ : ↥SubexpPS) • y := by
      refine Subtype.ext ?_
      rw [qD_coe, Submodule.coe_add]
      change qDeriv (psSMul ((F : ↥SubexpPS) : PowerSeries ℂ) (y : FormalQSeries))
        = psSMul ((F : ↥SubexpPS) : PowerSeries ℂ) (qDeriv (y : FormalQSeries))
          + psSMul (theta ((F : ↥SubexpPS) : PowerSeries ℂ)) (y : FormalQSeries)
      exact qDeriv_psSMul _ y.2
    rw [hprod]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hy)
      (Submodule.smul_mem _ _ (qTowerSpan_mono hsupp a (by omega) hymem))

set_option maxHeartbeats 1000000 in
-- the strong induction elaborates a long chain of `Submodule` membership goals
/-- **Arakawa–Kawasetsu Lemma 5.5, span form.**  For `a` square-bracket primary and any
formal block `S`,

  `S(L[−2]^i a) − (q d/dq)^i (S a) ∈ span_SubexpPS { (q d/dq)^j (S a) : j < i }`.

The induction is AK's, in their order: apply the `ω`-law (Lemma 5.4) at `v = L[−2]^{i−1}a`, use
`Lsq_tower` to rewrite each tail term `S(L[2m]L[−2]^{i−1}a)` as a scalar times
`S(L[−2]^{i−1−m}a)`, use the vanishing clause to cut the `∑ᶠ` down to `Finset.range i`, and feed
the strong induction hypothesis to every rung `≤ i−1`. -/
theorem blockRestrict_Lsq_pow_sub_qTower_mem (W : SuperVertexOperatorAlgebra 𝒱)
    {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ} (hsupp : ∀ v, S v ∈ QSeriesAt hbase)
    (hS : SuperNearVOA.IsSuperFormalBlock W S) {a : 𝒱} {Δ : ℂ}
    (ha : W.toSuperNearVOA.IsSuperSqPrimary a Δ) (i : ℕ) :
    blockRestrict hsupp ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] a) - qTower hsupp a i
      ∈ qTowerSpan hsupp a i := by
  classical
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 =>
        rw [Function.iterate_zero_apply, qTower_zero, sub_self]
        exact Submodule.zero_mem _
    | (k + 1) =>
        set v : 𝒱 := (⇑(W.toSuperNearVOA.superLsq (-2)))^[k] a with hv
        have hIHk : blockRestrict hsupp v - qTower hsupp a k ∈ qTowerSpan hsupp a k :=
          ih k (by omega)
        have hmemk : ∀ m : ℕ, m ≤ k →
            blockRestrict hsupp ((⇑(W.toSuperNearVOA.superLsq (-2)))^[m] a) ∈ qTowerSpan hsupp a (k + 1) := by
          intro m hm
          have h1 : blockRestrict hsupp ((⇑(W.toSuperNearVOA.superLsq (-2)))^[m] a) - qTower hsupp a m
              ∈ qTowerSpan hsupp a (k + 1) :=
            qTowerSpan_mono hsupp a (by omega) (ih m (by omega))
          have h2 : qTower hsupp a m ∈ qTowerSpan hsupp a (k + 1) :=
            qTower_mem_qTowerSpan hsupp a (by omega)
          have h3 : blockRestrict hsupp ((⇑(W.toSuperNearVOA.superLsq (-2)))^[m] a)
              = (blockRestrict hsupp ((⇑(W.toSuperNearVOA.superLsq (-2)))^[m] a) - qTower hsupp a m)
                + qTower hsupp a m := by abel
          rw [h3]
          exact Submodule.add_mem _ h1 h2
        -- the `ω`-law tail, rewritten by `Lsq_tower`
        have htower : ∀ m : ℕ, W.toSuperNearVOA.superLsq (2 * (m + 1) - 2 : ℤ) v
            = towerScalar Δ W.centralCharge m k • ((⇑(W.toSuperNearVOA.superLsq (-2)))^[k - m] a) := by
          intro m
          rw [show (2 * ((m : ℤ) + 1) - 2 : ℤ) = 2 * (m : ℤ) from by ring]
          exact Lsq_tower W ha k m
        have hzeroterm : ∀ m : ℕ, k < m → S (W.toSuperNearVOA.superLsq (2 * (m + 1) - 2 : ℤ) v) = 0 := by
          intro m hm
          rw [htower m, towerScalar_eq_zero_of_lt Δ W.centralCharge hm, zero_smul, map_zero]
        have hfinsum : (∑ᶠ m : ℕ, qConv (zhuG (m + 1)) (S (W.toSuperNearVOA.superLsq (2 * (m + 1) - 2 : ℤ) v)))
            = ∑ m ∈ Finset.range (k + 1),
                qConv (zhuG (m + 1)) (S (W.toSuperNearVOA.superLsq (2 * (m + 1) - 2 : ℤ) v)) := by
          refine finsum_eq_sum_of_support_subset _ ?_
          intro m hm
          simp only [Function.mem_support, ne_eq] at hm
          rw [Finset.coe_range, Set.mem_Iio]
          by_contra hc
          exact hm (by rw [hzeroterm m (by omega), qConv_zero_right])
        set F : ℕ → ↥SubexpPS :=
          fun m => ⟨PowerSeries.mk (zhuG (m + 1)), mk_zhuG_mem_subexpPS (m + 1)⟩ with hF
        set B : ℕ → ↥(QSeriesAt hbase) :=
          fun m => F m • blockRestrict hsupp (W.toSuperNearVOA.superLsq (2 * (m + 1) - 2 : ℤ) v) with hB
        have hkey : blockRestrict hsupp ((⇑(W.toSuperNearVOA.superLsq (-2)))^[k + 1] a)
            = qD hbase (blockRestrict hsupp v) + ∑ m ∈ Finset.range (k + 1), B m := by
          refine Subtype.ext ?_
          rw [Submodule.coe_add, Submodule.coe_sum, blockRestrict_coe, qD_coe, blockRestrict_coe,
            Function.iterate_succ_apply', ← hv, hS.omega v, hfinsum]
          refine congrArg _ (Finset.sum_congr rfl (fun m _ => ?_))
          exact (psSMul_mk (zhuG (m + 1)) (S (W.toSuperNearVOA.superLsq (2 * (m + 1) - 2 : ℤ) v))).symm
        have hBmem : ∀ m ∈ Finset.range (k + 1), B m ∈ qTowerSpan hsupp a (k + 1) := by
          intro m hm
          rw [Finset.mem_range] at hm
          refine Submodule.smul_mem _ _ ?_
          rw [htower m, map_smul]
          exact complex_smul_mem_span_subexpPS _ (hmemk (k - m) (by omega))
        have hqD : qD hbase (blockRestrict hsupp v) - qTower hsupp a (k + 1)
            ∈ qTowerSpan hsupp a (k + 1) := by
          have h1 : qD hbase (blockRestrict hsupp v) - qTower hsupp a (k + 1)
              = qD hbase (blockRestrict hsupp v - qTower hsupp a k) := by
            rw [map_sub, qTower_succ]
          rw [h1]
          exact qD_mem_qTowerSpan hsupp a k hIHk
        have hsplit : blockRestrict hsupp ((⇑(W.toSuperNearVOA.superLsq (-2)))^[k + 1] a) - qTower hsupp a (k + 1)
            = (qD hbase (blockRestrict hsupp v) - qTower hsupp a (k + 1))
              + ∑ m ∈ Finset.range (k + 1), B m := by
          rw [hkey]; abel
        rw [hsplit]
        exact Submodule.add_mem _ hqD (Submodule.sum_mem _ hBmem)

set_option maxHeartbeats 1000000 in
-- unfolding the `SubexpPS`-coefficient list through `Fin`/`Finset.range` reindexing is slow
/-- **Arakawa–Kawasetsu Lemma 5.5.**  For a square-bracket primary `a` and any formal block
`S`, the `L[−2]`-tower converts **unitriangularly** into the `q d/dq`-tower with subexponential
coefficients:

  `S(L[−2]^i a) = Σ_{j ≤ i} hc_j ⋆ (q d/dq)^j (S a)`,  `hc_i = 1`,  `hc_j = 0` for `j > i`.

This is exactly the `huni` hypothesis of `Modularity.ZhuODEAssembly.formalODE_of_unitriangular`,
**for one fixed vector** `a`.

⚠ Two deviations from AK, both recorded in the file header: the basis is `(q d/dq)^j`, not the
iterated Serre derivative `∂^j`; and the coefficients lie in `SubexpPS`, not in AK's
`A = ℂ[G̃₄,G̃₆]`.  AK's assertion `f_j(q) ∈ A` uses `θ`-stability of the Eisenstein ring, i.e.
Ramanujan's identities, which are not available here.

⚠ The hypothesis `IsSqPrimary` is **essential**, not decorative: `Modularity.UniCollapse` refutes
the same conclusion quantified over all `v`. -/
theorem huni_of_sqPrimary (W : SuperVertexOperatorAlgebra 𝒱)
    {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ} (hsupp : ∀ v, S v ∈ QSeriesAt hbase)
    (hS : SuperNearVOA.IsSuperFormalBlock W S) {a : 𝒱} {Δ : ℂ}
    (ha : W.toSuperNearVOA.IsSuperSqPrimary a Δ) (i : ℕ) :
    ∃ hc : ℕ → PowerSeries ℂ, (∀ j, hc j ∈ SubexpPS) ∧ hc i = 1 ∧ (∀ j, i < j → hc j = 0) ∧
      S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] a)
        = ∑ j ∈ Finset.range (i + 1), psSMul (hc j) (qDeriv^[j] (S a)) := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (↥SubexpPS)).mp
    (blockRestrict_Lsq_pow_sub_qTower_mem W hsupp hS ha i)
  set hcf : ℕ → PowerSeries ℂ := fun j =>
    if j = i then 1 else (if h : j < i then ((c ⟨j, h⟩ : ↥SubexpPS) : PowerSeries ℂ) else 0)
    with hcfdef
  have hmem : ∀ j, hcf j ∈ SubexpPS := by
    intro j
    rw [hcfdef]
    dsimp only
    split_ifs with h1 h2
    · exact Subalgebra.one_mem _
    · exact (c ⟨j, h2⟩).2
    · exact Subalgebra.zero_mem _
  have hone : hcf i = 1 := by rw [hcfdef]; dsimp only; rw [if_pos rfl]
  have hvan : ∀ j, i < j → hcf j = 0 := by
    intro j hj
    rw [hcfdef]
    dsimp only
    rw [if_neg (by omega), dif_neg (by omega)]
  refine ⟨hcf, hmem, hone, hvan, ?_⟩
  have hlow : ∑ j ∈ Finset.range i, hcf j • qTower hsupp a j
      = blockRestrict hsupp ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] a) - qTower hsupp a i := by
    rw [← hc, ← Fin.sum_univ_eq_sum_range (fun j => hcf j • qTower hsupp a j) i]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hji : ((j : ℕ)) ≠ i := by omega
    have hcj : hcf (j : ℕ) = ((c j : ↥SubexpPS) : PowerSeries ℂ) := by
      rw [hcfdef]
      dsimp only
      rw [if_neg hji, dif_pos j.2]
    rw [hcj]
    rfl
  have hsum : ∑ j ∈ Finset.range (i + 1), hcf j • qTower hsupp a j
      = blockRestrict hsupp ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] a) := by
    rw [Finset.sum_range_succ, hlow, hone, one_smul, sub_add_cancel]
  have hcoe := congrArg (fun z : ↥(QSeriesAt hbase) => (z : FormalQSeries)) hsum
  simp only [Submodule.coe_sum] at hcoe
  rw [blockRestrict_coe] at hcoe
  rw [← hcoe]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change psSMul (hcf j) ((qTower hsupp a j : ↥(QSeriesAt hbase)) : FormalQSeries) = _
  rw [qTower_coe]

/-! ## (D)  AK Lemma 5.3 under the Etingof–Schedler hypothesis -/

section Block

variable (W : SuperVertexOperatorAlgebra 𝒱)

set_option synthInstance.maxHeartbeats 1000000 in
-- as in `Modularity.FormalBlockFinite.exists_monic_Lsq_relation`: the Noetherian-chain argument
-- forces repeated `Module (↥GSeries) ↥(QSeriesAt hbase)` instance synthesis
set_option maxHeartbeats 1000000 in
-- and the chain-stabilisation `obtain` is itself a long elaboration
/-- **Arakawa–Kawasetsu Lemma 5.3.**  `A = GSeries` is Noetherian and, by AK Proposition 5.2
(`Modules.QuasiLisseFinite.fg_blockSpan_of_etingofFinite`), the block span is a finitely generated
`A`-module; hence the ascending chain `⟨S v, …, S(L[−2]^r v)⟩` stabilises and the resulting relation
is **monic** of some order `s ≥ 1`.

This is `Modularity.FormalBlockFinite.exists_monic_Lsq_relation` with `C2Cofinite W` weakened to
`SuperEtingofFinite W` — the only line of the proof that changes is the appeal to Proposition 5.2.

⚠ **This statement is NOT uniform in the block**, and it therefore does not deliver the closing
sentence of AK Theorem 5.7.  The chain is run inside
`Submodule.span (↥GSeries) (Set.range (blockRestrict hsupp))`, a submodule of `↥(QSeriesAt hbase)`,
so `S` and `hbase` are bound *before* `s` and `G`.  AK's Lemma 5.3 produces one relation in `V_A`,
independent of the module.

The uniform repair is `Modularity.AKUniformODE.exists_uniform_monic_Lsq_relation_of_etingofFinite`
(and `…_of_C2Cofinite` for the Zhu twin), which runs the Noetherian argument in `𝒱G 𝒱` modulo
`blockRelSpanG W` and pushes the single resulting relation along every block at once.  This theorem
is kept as-is because `formalODE_of_etingofFinite_of_sqPrimary` below consumes it in this form. -/
theorem exists_monic_Lsq_relation_of_etingofFinite {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : SuperNearVOA.IsSuperFormalBlock W S)
    (hV : W.toSuperNearVOA.IntegralWeights) (hE : SuperEtingofFinite W) (v : 𝒱) :
    ∃ (s : ℕ) (G : ℕ → PowerSeries ℂ), 1 ≤ s ∧ (∀ i, G i ∈ GSeries) ∧
      S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[s] v)
        = ∑ i ∈ Finset.range s, psSMul (G i) (S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] v)) := by
  classical
  set 𝔐 : Submodule (↥GSeries) ↥(QSeriesAt hbase) :=
    Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase))) with h𝔐
  haveI : IsNoetherianRing (↥GSeries) := isNoetherianRing_GSeries
  haveI hnoe : IsNoetherian (↥GSeries) ↥𝔐 :=
    isNoetherian_of_fg_of_noetherian _
      (SuperNearVOA.fg_superBlockSpan_of_superEtingofFinite W hV hsupp hS hE)
  set x : ℕ → ↥𝔐 := fun i =>
    ⟨blockRestrict hsupp ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] v), Submodule.subset_span ⟨_, rfl⟩⟩ with hxdef
  have hmono : Monotone (fun r : ℕ =>
      Submodule.span (↥GSeries) (Set.range (fun i : Fin (r + 1) => x i))) := by
    intro r r' hrr
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.1, by omega⟩, rfl⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr hnoe ⟨_, hmono⟩
  have hmem : x (n + 1) ∈ Submodule.span (↥GSeries)
      (Set.range (fun i : Fin (n + 1) => x i)) := by
    have := hn (n + 1) (by omega)
    change Submodule.span (↥GSeries) (Set.range (fun i : Fin (n + 1) => x i))
      = Submodule.span (↥GSeries) (Set.range (fun i : Fin (n + 1 + 1) => x i)) at this
    rw [this]
    exact Submodule.subset_span ⟨⟨n + 1, by omega⟩, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (↥GSeries)).mp hmem
  refine ⟨n + 1, fun i => if h : i < n + 1 then ((c ⟨i, h⟩ : ↥GSeries) : PowerSeries ℂ) else 0,
    by omega, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i < n + 1
    · rw [dif_pos h]; exact (c ⟨i, h⟩).2
    · rw [dif_neg h]; exact zero_mem _
  · set φ : ↥𝔐 →+ FormalQSeries :=
      ((QSeriesAt hbase).subtype.toAddMonoidHom).comp (𝔐.subtype.toAddMonoidHom) with hφ
    have hφsmul : ∀ (g : ↥GSeries) (i : ℕ),
        φ ((g • x i : ↥𝔐)) = psSMul ((g : PowerSeries ℂ)) (S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] v)) :=
      fun _ _ => rfl
    have hφx : ∀ i : ℕ, φ (x i) = S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] v) := fun _ => rfl
    have hL := congrArg φ hc
    rw [map_sum, hφx] at hL
    rw [← hL]
    dsimp only
    have hterm : ∀ i : Fin (n + 1),
        φ ((c i • x (i : ℕ) : ↥𝔐))
          = psSMul (if h : (i : ℕ) < n + 1 then ((c ⟨(i : ℕ), h⟩ : ↥GSeries) : PowerSeries ℂ)
              else 0) (S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[(i : ℕ)] v)) := by
      intro i
      rw [hφsmul (c i) (i : ℕ), dif_pos i.2]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i)]
    exact Fin.sum_univ_eq_sum_range
      (fun i : ℕ => psSMul (if h : i < n + 1 then ((c ⟨i, h⟩ : ↥GSeries) : PowerSeries ℂ) else 0)
        (S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] v))) (n + 1)

/-! ## (E)  AK Theorem 5.7, equation (2) — the formal ODE -/

set_option maxHeartbeats 1000000 in
-- the double sum swap over `Finset.range s` in a `PowerSeries ℂ`-module is slow to elaborate
/-- **The substitution step of AK Theorem 5.7, isolated from its finiteness input.**  Given

* a **monic** relation among the `S(L[−2]^i v)` with `GSeries` coefficients (AK Lemma 5.3), and
* the **unitriangular** conversion `huni` of the `L[−2]`-tower into the `q d/dq`-tower (AK
  Lemma 5.5),

substituting one into the other gives a monic linear ODE in `q d/dq` with subexponential
coefficients.  Monicity survives precisely because `hc i = 1`.

This is `Modularity.ZhuODEAssembly.formalODE_of_unitriangular` with its finiteness hypotheses
replaced by the relation they produce, so that both the `C2Cofinite` and the `EtingofFinite` routes
can feed it. -/
theorem formalODE_of_monic_of_unitriangular {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (v : 𝒱)
    (hmonic : ∃ (s : ℕ) (G : ℕ → PowerSeries ℂ), 1 ≤ s ∧ (∀ i, G i ∈ GSeries) ∧
      S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[s] v)
        = ∑ i ∈ Finset.range s, psSMul (G i) (S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] v)))
    (huni : ∀ i : ℕ, ∃ hc : ℕ → PowerSeries ℂ,
      (∀ j, hc j ∈ SubexpPS) ∧ hc i = 1 ∧ (∀ j, i < j → hc j = 0) ∧
      S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] v)
        = ∑ j ∈ Finset.range (i + 1), psSMul (hc j) (qDeriv^[j] (S v))) :
    ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧ (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
      ∀ e : ℂ, (qDeriv^[s] (S v)) e
        + ∑ i ∈ Finset.range s, qConv (g i) (qDeriv^[i] (S v)) e = 0 := by
  classical
  obtain ⟨s, G, hs1, hGmem, hGrel⟩ := hmonic
  choose hc hcmem hcone hczero hceq using huni
  set d : ℕ → ↥(QSeriesAt hbase) := fun j =>
    ⟨qDeriv^[j] (S v), qDeriv_iterate_mem_QSeriesAt (hsupp v) j⟩ with hd
  set L : ℕ → ↥(QSeriesAt hbase) := fun i =>
    ⟨S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] v), hsupp _⟩ with hLdef
  set π : ↥(QSeriesAt hbase) →+ FormalQSeries :=
    (QSeriesAt hbase).subtype.toAddMonoidHom with hπ
  have hπd : ∀ j : ℕ, π (d j) = qDeriv^[j] (S v) := fun _ => rfl
  have hπL : ∀ i : ℕ, π (L i) = S ((⇑(W.toSuperNearVOA.superLsq (-2)))^[i] v) := fun _ => rfl
  have hπsmul : ∀ (F : PowerSeries ℂ) (y : ↥(QSeriesAt hbase)),
      π (F • y) = psSMul F (π y) := fun _ _ => rfl
  have hinj : Function.Injective π := fun a b hab => Subtype.ext hab
  have hL : ∀ i : ℕ, L i = ∑ j ∈ Finset.range (i + 1), (hc i j) • d j := by
    intro i
    refine hinj ?_
    rw [hπL, map_sum, hceq i]
    exact Finset.sum_congr rfl (fun j _ => by rw [hπsmul, hπd])
  have hLext : ∀ i : ℕ, i < s → L i = ∑ j ∈ Finset.range s, (hc i j) • d j := by
    intro i his
    rw [hL i]
    have hsub : Finset.range (i + 1) ⊆ Finset.range s := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    refine Finset.sum_subset hsub ?_
    intro j hjs hj
    rw [Finset.mem_range] at hjs
    rw [Finset.mem_range] at hj
    have hij : i < j := by omega
    rw [hczero i j hij, zero_smul]
  have hrel : L s = ∑ i ∈ Finset.range s, (G i) • L i := by
    refine hinj ?_
    rw [hπL, map_sum, hGrel]
    exact Finset.sum_congr rfl (fun i _ => by rw [hπsmul, hπL])
  have hLHS : L s = d s + ∑ j ∈ Finset.range s, (hc s j) • d j := by
    rw [hL s, Finset.sum_range_succ, hcone s, one_smul, add_comm]
  have hRHS : ∑ i ∈ Finset.range s, (G i) • L i
      = ∑ j ∈ Finset.range s, (∑ i ∈ Finset.range s, G i * hc i j) • d j := by
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [hLext i (Finset.mem_range.mp hi), Finset.smul_sum])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl (fun i _ => (mul_smul (G i) (hc i j) (d j)).symm)
  set g' : ℕ → PowerSeries ℂ :=
    fun j => hc s j - ∑ i ∈ Finset.range s, G i * hc i j with hg'
  have hzeroSum : d s + ∑ j ∈ Finset.range s, (g' j) • d j = 0 := by
    have hkey : d s + ∑ j ∈ Finset.range s, (hc s j) • d j
        = ∑ j ∈ Finset.range s, (∑ i ∈ Finset.range s, G i * hc i j) • d j := by
      rw [← hLHS, hrel, hRHS]
    have hsplit : ∑ j ∈ Finset.range s, (g' j) • d j
        = (∑ j ∈ Finset.range s, (hc s j) • d j)
          - ∑ j ∈ Finset.range s, (∑ i ∈ Finset.range s, G i * hc i j) • d j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact sub_smul (hc s j) (∑ i ∈ Finset.range s, G i * hc i j) (d j)
    rw [hsplit, ← add_sub_assoc, hkey, sub_self]
  have hg'mem : ∀ j, g' j ∈ SubexpPS := by
    intro j
    refine Subalgebra.sub_mem _ (hcmem s j) (Subalgebra.sum_mem _ (fun i _ => ?_))
    exact Subalgebra.mul_mem _ (GSeries_le_subexpPS (hGmem i)) (hcmem i j)
  refine ⟨s, fun i k => PowerSeries.coeff k (g' i), hs1, fun i => hg'mem i, fun e => ?_⟩
  have hcoe := congrArg π hzeroSum
  rw [map_add, map_sum, map_zero, hπd] at hcoe
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range s) => by
    rw [hπsmul, hπd])] at hcoe
  have hfun := congrFun hcoe e
  simpa [psSMul] using hfun

/-- **Arakawa–Kawasetsu Theorem 5.7, equation (2) — formal form.**  For a VOA satisfying the
Etingof–Schedler hypothesis, a **square-bracket primary** vector `a`, and any formal block `S`,
there are an order `s ≥ 1` and subexponential coefficient sequences `g_i` with

  `(q d/dq)^s (S a) + Σ_{i<s} g_i ⋆ (q d/dq)^i (S a) = 0`.

The proof is AK's own paragraph: Lemma 5.3 gives the monic relation, Lemma 5.6 says the block kills
`[V_A,V_A] + O_q(V)` (that is `IsFormalBlock`, already used to prove Lemma 5.3), and Lemma 5.5
rewrites the result in the derivative tower.

⚠ **This is a formal `q`-series identity, not a modular linear differential equation.**  See the
file header: the basis is `(q d/dq)^i` and the coefficients are subexponential series, not elements
of `ℂ[G̃₄,G̃₆]`; nothing about modularity is proved. -/
theorem formalODE_of_etingofFinite_of_sqPrimary {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : SuperNearVOA.IsSuperFormalBlock W S)
    (hV : W.toSuperNearVOA.IntegralWeights) (hE : SuperEtingofFinite W) {a : 𝒱} {Δ : ℂ}
    (ha : W.toSuperNearVOA.IsSuperSqPrimary a Δ) :
    ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧ (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
      ∀ e : ℂ, (qDeriv^[s] (S a)) e
        + ∑ i ∈ Finset.range s, qConv (g i) (qDeriv^[i] (S a)) e = 0 :=
  formalODE_of_monic_of_unitriangular W hsupp a
    (exists_monic_Lsq_relation_of_etingofFinite W hsupp hS hV hE a)
    (huni_of_sqPrimary W hsupp hS ha)

end Block

end SuperAK

end VOA
