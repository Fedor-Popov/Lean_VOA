/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroLocal
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# Genus zero on the abstract interface: the overlap construction

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`. A local symmetry `α` of a
replicable member `f` on a disc `B′ = D(z₀, η)` (closure in `ℍ`) which is not a real affine map
satisfies an **intertwining sequence**: real affine maps `C n z = a n z + b n → id`, `C n ≠ id`,
and real affine maps `C′ n` with `α ∘ C n = C′ n ∘ α` on `D(z₀, η/2)`.

The proof has two parts.

* `exists_intertwining_of_relations` (no Hecke input): from a sequence of relations
  `f (δ i z + τ i) = f (μ i α z + ν i)` on `B′` whose right sides lie above `topHeight`, with
  dilations `δ i` bounded below and pairwise distinct, compactness of the normalised data
  `(δ i, τ i mod 1)` and top injectivity on the overlaps give the intertwining sequence. The
  dilations are bounded above because a relation reaching the top would make `α` real affine
  (`exists_affC_eqOn_of_top`).
* `exists_intertwining_of_not_realAffine`: the relations come from the iterated pairing on connected
  domains (`exists_iterate_heckeAffine_partner`) at two distinct admissible primes `p ≠ q`: first
  `f (p^{w+ℓ+1} α z) = f (p^e z + b)`, then `f (q^i (p^e z + b)) = f (q^{e′} p^{w+ℓ+1} α z + b′)`,
  with `ℓ = log_p (q^i)`. The dilations `q^i p^e` are pairwise distinct by unique factorisation.

The prime Hecke identity enters only as the hypothesis `hB1 : PrimeHeckeIdentity F k`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set
open scoped Real

/-! ### Elementary facts -/

lemma im_pos_of_mem_ball {z₀ z : ℂ} {η : ℝ} (hηz : η ≤ z₀.im) (hz : z ∈ Metric.ball z₀ η) :
    0 < z.im := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h1 := Complex.abs_im_le_norm (z - z₀)
  rw [Complex.sub_im] at h1
  have h2 := (abs_lt.mp (h1.trans_lt hz)).1
  linarith

/-- Powers of distinct primes: `p ^ e ≠ q ^ d` for `e ∈ ℤ`, `d ≥ 1`. -/
lemma zpow_ne_pow_of_prime_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e : ℤ)
    {d : ℕ} (hd : d ≠ 0) : (p : ℝ) ^ e ≠ (q : ℝ) ^ d := by
  intro h
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  rcases le_or_gt e 0 with he | he
  · have h1 : (p : ℝ) ^ e ≤ 1 := zpow_le_one_of_nonpos₀ hp1 he
    have h2 : 1 < (q : ℝ) ^ d := one_lt_pow₀ hq1 hd
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, e = m := ⟨e.toNat, (Int.toNat_of_nonneg he.le).symm⟩
    rw [zpow_natCast] at h
    have h' : p ^ m = q ^ d := by exact_mod_cast h
    have hqd : q ∣ p ^ m := by
      rw [h']
      exact dvd_pow_self q hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqd)).symm

/-! ### From relations to an intertwining sequence -/

/-- **Overlap construction, abstract part.** Let `α` be holomorphic on `B′ = D(z₀, η)` with
`η < Im z₀`, not a real affine map on `B′`, and let `f (δ i z + τ i) = f (μ i α(z) + ν i)` on `B′`
for all `i`, where `δ i ≥ lo > 0` are pairwise distinct, `μ i > 0`, and the right sides lie above
`topHeight`. Then there are real affine `C n z = a n z + b n` with `a n > 0`, `a n ≠ 1`,
`(a n, b n) → (1, 0)`, and real affine `C′ n` with positive dilation, such that `C n` maps
`D(z₀, η/2)` into `B′` and `α ∘ C n = C′ n ∘ α` on `D(z₀, η/2)`. -/
theorem exists_intertwining_of_relations {c : ℕ → ℂ} (hc : IsJDominated c) {z₀ : ℂ} {η : ℝ}
    (hη : 0 < η) (hηz : η < z₀.im) {α : ℂ → ℂ} (hα : DifferentiableOn ℂ α (Metric.ball z₀ η))
    (hna : ¬ ∃ a b : ℝ, 0 < a ∧ ∀ z ∈ Metric.ball z₀ η, α z = affC a b z)
    {δ τ μ ν : ℕ → ℝ} (hδ : ∀ i, 0 < δ i) (hμ : ∀ i, 0 < μ i) {lo : ℝ} (hlo : 0 < lo)
    (hδlo : ∀ i, lo ≤ δ i) (hδne : ∀ i j, i < j → δ i ≠ δ j)
    (hrel : ∀ i, ∀ z ∈ Metric.ball z₀ η,
      qSeriesExt c (affC (δ i) (τ i) z) = qSeriesExt c (affC (μ i) (ν i) (α z)))
    (htop : ∀ i, ∀ z ∈ Metric.ball z₀ η, topHeight ≤ (affC (μ i) (ν i) (α z)).im) :
    ∃ a b a' b' : ℕ → ℝ, (∀ n, 0 < a n) ∧ (∀ n, a n ≠ 1) ∧ (∀ n, 0 < a' n) ∧
      Tendsto a atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 0) ∧
      ∀ n, ∀ z ∈ Metric.ball z₀ (η / 2), affC (a n) (b n) z ∈ Metric.ball z₀ η ∧
        α (affC (a n) (b n) z) = affC (a' n) (b' n) (α z) := by
  have hBo : IsOpen (Metric.ball z₀ η) := Metric.isOpen_ball
  have hBc : IsPreconnected (Metric.ball z₀ η) := (convex_ball z₀ η).isPreconnected
  have hz₀B : z₀ ∈ Metric.ball z₀ η := Metric.mem_ball_self hη
  have hBU : ∀ z ∈ Metric.ball z₀ η, 0 < z.im := fun z hz => im_pos_of_mem_ball hηz.le hz
  have hz₀im : 0 < z₀.im := hη.trans hηz
  -- the dilations are bounded above: a relation reaching the top makes `α` real affine
  have hδhi : ∀ i, δ i ≤ topHeight / z₀.im := by
    intro i
    by_contra hcon
    have hcon' := lt_of_not_ge hcon
    have hz₁top : topHeight < (affC (δ i) (τ i) z₀).im := by
      rw [affC_im]
      rwa [div_lt_iff₀ hz₀im] at hcon'
    exact hna (exists_affC_eqOn_of_top hc hBo hBc hα (hδ i) (hμ i) (hrel i) (htop i) hz₀B
      hz₁top)
  -- normalise the translations into `[0, 1]`
  obtain ⟨τ', hτ'⟩ : ∃ τ' : ℕ → ℝ, τ' = fun i => τ i - ⌊τ i⌋ := ⟨_, rfl⟩
  have hτ'i : ∀ i, τ' i = τ i - ⌊τ i⌋ := fun i => by rw [hτ']
  have hτ'mem : ∀ i, τ' i ∈ Icc (0 : ℝ) 1 := fun i => by
    rw [hτ'i]
    have h1 := Int.floor_le (τ i)
    have h2 := Int.lt_floor_add_one (τ i)
    constructor <;> linarith
  have hrel' : ∀ i, ∀ z ∈ Metric.ball z₀ η,
      qSeriesExt c (affC (δ i) (τ' i) z) = qSeriesExt c (affC (μ i) (ν i) (α z)) := by
    intro i z hz
    have h1 : affC (δ i) (τ' i) z = affC (δ i) (τ i) z + ((-⌊τ i⌋ : ℤ) : ℂ) := by
      rw [hτ'i]
      simp only [affC]
      push_cast
      ring
    rw [h1, qSeriesExt_add_intCast c (affC_im_pos (hδ i) _ (hBU z hz)), hrel i z hz]
  -- a convergent subsequence of the normalised data
  obtain ⟨L, hLmem, φ, hφ, hlim⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq
    (x := fun i => ((δ i, τ' i) : ℝ × ℝ)) (fun i => ⟨⟨hδlo i, hδhi i⟩, hτ'mem i⟩)
  have hL1 : 0 < L.1 := hlo.trans_le hLmem.1.1
  have hδlim : Tendsto (fun n => δ (φ n)) atTop (𝓝 L.1) :=
    (continuous_fst.tendsto L).comp hlim
  have hτlim : Tendsto (fun n => τ' (φ n)) atTop (𝓝 L.2) :=
    (continuous_snd.tendsto L).comp hlim
  have hδlim' : Tendsto (fun n => δ (φ (n + 1))) atTop (𝓝 L.1) :=
    hδlim.comp (tendsto_add_atTop_nat 1)
  have hτlim' : Tendsto (fun n => τ' (φ (n + 1))) atTop (𝓝 L.2) :=
    hτlim.comp (tendsto_add_atTop_nat 1)
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun n => δ (φ n) / δ (φ (n + 1)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun n => (τ' (φ n) - τ' (φ (n + 1))) / δ (φ (n + 1)) :=
    ⟨_, rfl⟩
  have hai : ∀ n, a n = δ (φ n) / δ (φ (n + 1)) := fun n => by rw [ha]
  have hbi : ∀ n, b n = (τ' (φ n) - τ' (φ (n + 1))) / δ (φ (n + 1)) := fun n => by rw [hb]
  have halim : Tendsto a atTop (𝓝 1) := by
    have h := hδlim.div hδlim' hL1.ne'
    rw [div_self hL1.ne'] at h
    rwa [ha]
  have hblim : Tendsto b atTop (𝓝 0) := by
    have h := (hτlim.sub hτlim').div hδlim' hL1.ne'
    rw [sub_self, zero_div] at h
    rwa [hb]
  have hapos : ∀ n, 0 < a n := fun n => by
    rw [hai]
    exact div_pos (hδ _) (hδ _)
  have hane : ∀ n, a n ≠ 1 := by
    intro n h
    rw [hai] at h
    exact hδne _ _ (hφ (Nat.lt_succ_self n)) ((div_eq_one_iff_eq (hδ (φ (n + 1))).ne').mp h)
  have hcomp : ∀ n z, affC (δ (φ (n + 1))) (τ' (φ (n + 1))) (affC (a n) (b n) z) =
      affC (δ (φ n)) (τ' (φ n)) z := by
    intro n z
    have hd : (δ (φ (n + 1)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hδ _).ne'
    rw [hai, hbi]
    simp only [affC]
    push_cast
    field_simp
    ring
  -- eventually `C n` maps the half disc into `B′`
  set R : ℝ := ‖z₀‖ + η with hR
  have hsmall : Tendsto (fun n => |a n - 1| * R + |b n|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => |a n - 1|) atTop (𝓝 0) := by
      have h := (halim.sub_const 1).abs
      rwa [sub_self, abs_zero] at h
    have h2 : Tendsto (fun n => |b n|) atTop (𝓝 0) := by
      have h := hblim.abs
      rwa [abs_zero] at h
    have h3 := (h1.mul_const R).add h2
    rwa [zero_mul, zero_add] at h3
  have hev1 : ∀ᶠ n in atTop, |a n - 1| * R + |b n| < η / 2 :=
    hsmall.eventually (gt_mem_nhds (half_pos hη))
  have hS : IsPreconnected (Metric.ball z₀ (η / 2)) := (convex_ball _ _).isPreconnected
  have hSB : Metric.ball z₀ (η / 2) ⊆ Metric.ball z₀ η :=
    Metric.ball_subset_ball (by linarith)
  have hev : ∀ᶠ n in atTop,
      (∀ z ∈ Metric.ball z₀ (η / 2), affC (a n) (b n) z ∈ Metric.ball z₀ η) ∧
      ∃ a' b' : ℝ, 0 < a' ∧ ∀ z ∈ Metric.ball z₀ (η / 2),
        α (affC (a n) (b n) z) = affC a' b' (α z) := by
    filter_upwards [hev1] with n hn
    have hmaps : ∀ z ∈ Metric.ball z₀ (η / 2), affC (a n) (b n) z ∈ Metric.ball z₀ η := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have hzR : ‖z‖ ≤ R := by
        have := norm_sub_norm_le z z₀
        rw [hR]
        linarith
      have h1 := norm_affC_sub_le (a n) (b n) z
      have h2 : |a n - 1| * ‖z‖ ≤ |a n - 1| * R :=
        mul_le_mul_of_nonneg_left hzR (abs_nonneg _)
      have h3 := norm_sub_le_norm_sub_add_norm_sub (affC (a n) (b n) z) z z₀
      linarith
    refine ⟨hmaps, ?_⟩
    obtain ⟨kk, hkk⟩ := exists_int_eq_add_of_top hc hS
      (u := fun z => affC (μ (φ n)) (ν (φ n)) (α z))
      (v := fun z => affC (μ (φ (n + 1))) (ν (φ (n + 1))) (α (affC (a n) (b n) z)))
      ((continuous_affC _ _).comp_continuousOn (hα.continuousOn.mono hSB))
      ((continuous_affC _ _).comp_continuousOn
        (hα.continuousOn.comp (continuous_affC _ _).continuousOn fun z hz => hmaps z hz))
      (fun z hz => htop _ z (hSB hz)) (fun z hz => htop _ _ (hmaps z hz))
      (fun z hz => by
        rw [← hrel' _ z (hSB hz), ← hrel' _ _ (hmaps z hz), hcomp])
    refine ⟨μ (φ n) / μ (φ (n + 1)), (ν (φ n) - kk - ν (φ (n + 1))) / μ (φ (n + 1)),
      div_pos (hμ _) (hμ _), fun z hz => ?_⟩
    have h1 := hkk z hz
    have hμj : (μ (φ (n + 1)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hμ _).ne'
    simp only [affC] at h1 ⊢
    have h2 : (μ (φ (n + 1)) : ℂ) * α (↑(a n) * z + ↑(b n)) =
        μ (φ n) * α z + ν (φ n) - ν (φ (n + 1)) - kk := by
      linear_combination -h1
    rw [← inv_mul_cancel_left₀ hμj (α (↑(a n) * z + ↑(b n))), h2]
    push_cast
    ring
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  have hex : ∀ n, ∃ a' b' : ℝ, 0 < a' ∧ ∀ z ∈ Metric.ball z₀ (η / 2),
      α (affC (a (n + n₀)) (b (n + n₀)) z) = affC a' b' (α z) := fun n =>
    (hn₀ (n + n₀) (Nat.le_add_left n₀ n)).2
  choose a' b' ha' hab' using hex
  refine ⟨fun n => a (n + n₀), fun n => b (n + n₀), a', b', fun n => hapos _, fun n => hane _,
    ha', (tendsto_add_atTop_iff_nat n₀).mpr halim, (tendsto_add_atTop_iff_nat n₀).mpr hblim,
    fun n z hz => ⟨(hn₀ (n + n₀) (Nat.le_add_left n₀ n)).1 z hz, hab' n z hz⟩⟩

/-! ### The Hecke relations at two admissible primes -/

/-- **Overlap construction**. Let `F` be a replicable family of period `N > 0` satisfying the
prime Hecke identity (`hB1`), `f = qSeriesFun (F.c k)`, and let `α` be holomorphic on
`B′ = D(z₀, η)` (`η < Im z₀`) with `Im α ≥ m > 0` and `f ∘ α = f` on `B′`. If `α` is not a real
affine map on `B′`, there are real affine `C n z = a n z + b n` with `a n > 0`, `a n ≠ 1`,
`(a n, b n) → (1, 0)`, and real affine `C′ n` of positive dilation, with `C n (D(z₀, η/2)) ⊆ B′`
and `α ∘ C n = C′ n ∘ α` on `D(z₀, η/2)`. -/
theorem exists_intertwining_of_not_realAffine {N : ℕ} (hN : 0 < N) (F : ReplicableFamily N)
    (k : ℕ) (hB1 : PrimeHeckeIdentity F k) {z₀ : ℂ} {η : ℝ} (hη : 0 < η) (hηz : η < z₀.im)
    {α : ℂ → ℂ} (hα : DifferentiableOn ℂ α (Metric.ball z₀ η)) {m : ℝ} (hm : 0 < m)
    (hαm : ∀ z ∈ Metric.ball z₀ η, m ≤ (α z).im)
    (hαf : ∀ z ∈ Metric.ball z₀ η, qSeriesExt (F.c k) (α z) = qSeriesExt (F.c k) z)
    (hna : ¬ ∃ a b : ℝ, 0 < a ∧ ∀ z ∈ Metric.ball z₀ η, α z = affC a b z) :
    ∃ a b a' b' : ℕ → ℝ, (∀ n, 0 < a n) ∧ (∀ n, a n ≠ 1) ∧ (∀ n, 0 < a' n) ∧
      Tendsto a atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 0) ∧
      ∀ n, ∀ z ∈ Metric.ball z₀ (η / 2), affC (a n) (b n) z ∈ Metric.ball z₀ η ∧
        α (affC (a n) (b n) z) = affC (a' n) (b' n) (α z) := by
  have hc := F.isJDominated k
  have hBo : IsOpen (Metric.ball z₀ η) := Metric.isOpen_ball
  have hBc : IsPreconnected (Metric.ball z₀ η) := (convex_ball z₀ η).isPreconnected
  have hBn : (Metric.ball z₀ η).Nonempty := ⟨z₀, Metric.mem_ball_self hη⟩
  have hBU : ∀ z ∈ Metric.ball z₀ η, 0 < z.im := fun z hz => im_pos_of_mem_ball hηz.le hz
  have hαU : ∀ z ∈ Metric.ball z₀ η, 0 < (α z).im := fun z hz => hm.trans_le (hαm z hz)
  -- two distinct admissible primes `p < q`
  obtain ⟨p, hpp, hp1, hpN⟩ := Nat.exists_prime_gt_modEq_one 1 hN.ne'
  obtain ⟨q, hqp, hpq, hqN⟩ := Nat.exists_prime_gt_modEq_one p hN.ne'
  have hBp := hB1 p hpp hpN
  have hBq := hB1 q hqp hqN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hp1' : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hqp.one_lt.le
  -- the height exponent `w` with `topHeight < p ^ w * m`
  set w : ℕ := ⌈topHeight / m⌉₊ with hw
  have hwtop : topHeight < (p : ℝ) ^ w * m := by
    have h1 : topHeight / m ≤ w := Nat.le_ceil _
    have h2 : (w : ℝ) < (p : ℝ) ^ w := by exact_mod_cast Nat.lt_pow_self hpp.one_lt
    rw [div_le_iff₀ hm] at h1
    nlinarith
  -- `ℓ i = log_p (q ^ i)`: `p ^ ℓ ≤ q ^ i < p ^ (ℓ + 1)`
  set ℓ : ℕ → ℕ := fun i => Nat.log p (q ^ i) with hℓ
  have hℓlo : ∀ i, (p : ℝ) ^ ℓ i ≤ (q : ℝ) ^ i := fun i => by
    exact_mod_cast Nat.pow_log_le_self p (pow_ne_zero i hqp.ne_zero)
  have hℓhi : ∀ i, (q : ℝ) ^ i ≤ (p : ℝ) ^ (ℓ i + 1) := fun i => by
    exact_mod_cast (Nat.lt_pow_succ_log_self hpp.one_lt (q ^ i)).le
  set nn : ℕ → ℕ := fun i => w + ℓ i + 1 with hnn
  -- step A: `f (p ^ (nn i) α z) = f (p ^ (e i) z + b i)`
  have hA : ∀ i : ℕ, ∃ (e : ℤ) (b : ℝ), |e| ≤ (nn i : ℤ) ∧ ∀ z ∈ Metric.ball z₀ η,
      qSeriesExt (F.c k) (affC ((p : ℝ) ^ nn i) 0 (α z)) =
        qSeriesExt (F.c k) (affC ((p : ℝ) ^ e) b z) := fun i =>
    exists_iterate_heckeAffine_partner F k p hpp.pos hBp hBo hBc hBn (u := α) (v := fun z => z)
      hα differentiableOn_id hαU hBU hαf (nn i)
  choose e b he hrelA using hA
  -- step B: `f (q ^ i (p ^ (e i) z + b i)) = f (q ^ (e' i) p ^ (nn i) α z + b' i)`
  have hB : ∀ i : ℕ, ∃ (e' : ℤ) (b' : ℝ), |e'| ≤ (i : ℤ) ∧ ∀ z ∈ Metric.ball z₀ η,
      qSeriesExt (F.c k) (affC ((q : ℝ) ^ i) 0 (affC ((p : ℝ) ^ e i) (b i) z)) =
        qSeriesExt (F.c k) (affC ((q : ℝ) ^ e') b' (affC ((p : ℝ) ^ nn i) 0 (α z))) := fun i =>
    exists_iterate_heckeAffine_partner F k q hqp.pos hBq hBo hBc hBn
      (u := affC ((p : ℝ) ^ e i) (b i)) (v := fun z => affC ((p : ℝ) ^ nn i) 0 (α z))
      (differentiable_affC _ _).differentiableOn
      ((differentiable_affC _ _).comp_differentiableOn hα)
      (fun z hz => affC_im_pos (zpow_pos hp0 _) _ (hBU z hz))
      (fun z hz => affC_im_pos (pow_pos hp0 _) _ (hαU z hz))
      (fun z hz => (hrelA i z hz).symm) i
  choose e' b' he' hrelB using hB
  -- the relations
  have hrel : ∀ i : ℕ, ∀ z ∈ Metric.ball z₀ η,
      qSeriesExt (F.c k) (affC ((q : ℝ) ^ i * (p : ℝ) ^ e i) ((q : ℝ) ^ i * b i) z) =
        qSeriesExt (F.c k) (affC ((q : ℝ) ^ e' i * (p : ℝ) ^ nn i) (b' i) (α z)) := by
    intro i z hz
    have h := hrelB i z hz
    simp only [affC_affC, mul_zero, add_zero, zero_add] at h
    exact h
  -- the right sides lie in the top
  have hμge : ∀ i : ℕ, (p : ℝ) ^ w ≤ (q : ℝ) ^ e' i * (p : ℝ) ^ nn i := by
    intro i
    have hei : -(i : ℤ) ≤ e' i := by
      have h1 := he' i
      have h2 := neg_abs_le (e' i)
      linarith
    have h1 : ((q : ℝ) ^ i)⁻¹ ≤ (q : ℝ) ^ e' i := by
      rw [← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ hq1' hei
    have hqi : (0 : ℝ) < (q : ℝ) ^ i := pow_pos hq0 i
    have h2 : 1 ≤ ((q : ℝ) ^ i)⁻¹ * (p : ℝ) ^ (ℓ i + 1) := by
      rw [inv_mul_eq_div, le_div_iff₀ hqi, one_mul]
      exact hℓhi i
    have h3 : (p : ℝ) ^ nn i = (p : ℝ) ^ w * (p : ℝ) ^ (ℓ i + 1) := by
      simp only [hnn]
      ring
    calc (p : ℝ) ^ w = (p : ℝ) ^ w * 1 := (mul_one _).symm
      _ ≤ (p : ℝ) ^ w * (((q : ℝ) ^ i)⁻¹ * (p : ℝ) ^ (ℓ i + 1)) :=
          mul_le_mul_of_nonneg_left h2 (pow_pos hp0 w).le
      _ = ((q : ℝ) ^ i)⁻¹ * (p : ℝ) ^ nn i := by rw [h3]; ring
      _ ≤ (q : ℝ) ^ e' i * (p : ℝ) ^ nn i :=
          mul_le_mul_of_nonneg_right h1 (pow_pos hp0 _).le
  have htop : ∀ i : ℕ, ∀ z ∈ Metric.ball z₀ η,
      topHeight ≤ (affC ((q : ℝ) ^ e' i * (p : ℝ) ^ nn i) (b' i) (α z)).im := by
    intro i z hz
    rw [affC_im]
    have h1 := hμge i
    have h2 := hαm z hz
    have h3 : (p : ℝ) ^ w * m ≤ ((q : ℝ) ^ e' i * (p : ℝ) ^ nn i) * (α z).im :=
      mul_le_mul h1 h2 hm.le ((pow_pos hp0 w).le.trans h1)
    linarith
  -- the dilations of the left sides are bounded below and pairwise distinct
  have hδlo : ∀ i : ℕ, (p : ℝ) ^ (-((w : ℤ) + 1)) ≤ (q : ℝ) ^ i * (p : ℝ) ^ e i := by
    intro i
    have hei : -(nn i : ℤ) ≤ e i := by
      have h1 := he i
      have h2 := neg_abs_le (e i)
      linarith
    have h1 : (p : ℝ) ^ (-(nn i : ℤ)) ≤ (p : ℝ) ^ e i := zpow_le_zpow_right₀ hp1' hei
    have h2 : (p : ℝ) ^ (-((w : ℤ) + 1)) = (p : ℝ) ^ ((ℓ i : ℕ) : ℤ) * (p : ℝ) ^ (-(nn i : ℤ)) := by
      rw [← zpow_add₀ hp0.ne']
      congr 1
      simp only [hnn]
      push_cast
      ring
    rw [h2, zpow_natCast]
    exact mul_le_mul (hℓlo i) h1 (zpow_pos hp0 _).le (pow_pos hq0 i).le
  have hδne : ∀ i j : ℕ, i < j → (q : ℝ) ^ i * (p : ℝ) ^ e i ≠ (q : ℝ) ^ j * (p : ℝ) ^ e j := by
    intro i j hij h
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    have hd : d ≠ 0 := by omega
    have hqi : (q : ℝ) ^ i ≠ 0 := (pow_pos hq0 i).ne'
    rw [pow_add, mul_assoc] at h
    have h1 : (p : ℝ) ^ e i = (q : ℝ) ^ d * (p : ℝ) ^ e (i + d) := mul_left_cancel₀ hqi h
    have h2 : (p : ℝ) ^ (e i - e (i + d)) = (q : ℝ) ^ d := by
      rw [zpow_sub₀ hp0.ne', h1]
      field_simp
    exact zpow_ne_pow_of_prime_ne hpp hqp (by omega) _ hd h2
  exact exists_intertwining_of_relations hc hη hηz hα hna
    (fun i => mul_pos (pow_pos hq0 i) (zpow_pos hp0 _))
    (fun i => mul_pos (zpow_pos hq0 _) (pow_pos hp0 _)) (zpow_pos hp0 _) hδlo hδne hrel htop

end VOA.Moonshine.ConwayNorton
