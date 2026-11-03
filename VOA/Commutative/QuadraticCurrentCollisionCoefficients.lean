/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QuadraticCurrentCoefficientReindexing

/-!
# Quadratic mode convolutions and current collision kernels

This file compares the explicit ordered convolution equations in the finite jet
presentation with the polynomial diagonal equations of the current carrier.
-/

namespace VOA.QuadraticCurrentCollisionCoefficients

open VOA.FiniteJet VOA.ModeParticlePairing
open VOA.ModeParticlePolynomial VOA.QuadraticJetCoefficientPairing
open VOA.QuadraticCurrentFunctionalCarrier VOA.DeligneAuxiliaryCollision
open VOA.QuadraticCurrentCoefficientReindexing VOA.CollisionCommonFactors
open scoped BigOperators

noncomputable section

variable {K σ ρ : Type*} [Field K]

/-- The particle slots left after removing the active pair. -/
abbrev Passive {m : ℕ} (i j : Fin m) := {k : Fin m // k ≠ i ∧ k ≠ j}

/-- Separate two distinct labels from their spectators. -/
def indexEquiv {m : ℕ} (i j : Fin m) (hji : j ≠ i) :
    Fin m ≃ Bool ⊕ Passive i j where
  toFun k := if hi : k = i then Sum.inl false else
    if hj : k = j then Sum.inl true else Sum.inr ⟨k, hi, hj⟩
  invFun
    | Sum.inl false => i
    | Sum.inl true => j
    | Sum.inr k => k.1
  left_inv k := by
    by_cases hi : k = i
    · simp [hi]
    · by_cases hj : k = j <;> simp [hi, hj, hji]
  right_inv k := by
    rcases k with (b | k)
    · cases b <;> simp [hji]
    · simp [k.2.1, k.2.2]

/-- Sum over labels as the two active terms followed by the passive labels. -/
theorem sum_active_passive {A : Type*} [AddCommMonoid A] {m : ℕ}
    (i j : Fin m) (hji : j ≠ i) (f : Fin m → A) :
    ∑ k, f k = f i + f j + ∑ k : Passive i j, f k.1 := by
  classical
  calc
    (∑ k, f k) = ∑ k : Bool ⊕ Passive i j, f ((indexEquiv i j hji).symm k) :=
      (Equiv.sum_comp (indexEquiv i j hji).symm f).symm
    _ = _ := by simp [Fintype.sum_sum_type, indexEquiv, add_comm]

/-- A tuple separates into its ordered pair of active entries and all spectators. -/
def tupleEquiv {A : Type*} {m : ℕ} (i j : Fin m) (hji : j ≠ i) :
    (Fin m → A) ≃ (A × A) × (Passive i j → A) where
  toFun a := ((a i, a j), fun k => a k.1)
  invFun z k := if hi : k = i then z.1.1 else
    if hj : k = j then z.1.2 else z.2 ⟨k, hi, hj⟩
  left_inv a := by
    funext k
    by_cases hi : k = i
    · simp [hi]
    · by_cases hj : k = j <;> simp [hi, hj, hji]
  right_inv z := by
    rcases z with ⟨⟨a, b⟩, p⟩
    apply Prod.ext
    · apply Prod.ext <;> simp [hji]
    · funext k
      simp [k.2.1, k.2.2]

@[simp] theorem tupleEquiv_symm_left {A : Type*} {m : ℕ}
    (i j : Fin m) (hji : j ≠ i) (z : (A × A) × (Passive i j → A)) :
    (tupleEquiv i j hji).symm z i = z.1.1 := by simp [tupleEquiv]

@[simp] theorem tupleEquiv_symm_right {A : Type*} {m : ℕ}
    (i j : Fin m) (hji : j ≠ i) (z : (A × A) × (Passive i j → A)) :
    (tupleEquiv i j hji).symm z j = z.1.2 := by simp [tupleEquiv, hji]

@[simp] theorem tupleEquiv_symm_passive {A : Type*} {m : ℕ}
    (i j : Fin m) (hji : j ≠ i) (z : (A × A) × (Passive i j → A)) (k : Passive i j) :
    (tupleEquiv i j hji).symm z k.1 = z.2 k := by simp [tupleEquiv, k.2.1, k.2.2]

/-- Collision exponents add the two active mode orders. -/
theorem mapDomain_collision_active {m : ℕ} (i j : Fin m) (hji : j ≠ i)
    (e : Fin m →₀ ℕ) :
    Finsupp.mapDomain (collisionIndex i j hji) e ⟨j, hji⟩ = e i + e j := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add k n e hk hn ih =>
    rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
      Finsupp.mapDomain_single, ih]
    by_cases hi : k = i
    · subst k
      simp [hji]
      omega
    · by_cases hj : k = j
      · subst k
        simp [hji, collisionIndex]
        omega
      · have hne : collisionIndex i j hji k ≠ ⟨j, hji⟩ := by
          simpa [collisionIndex, hi] using hj
        simp [hi, hj]

/-- Collision exponents retain every passive mode unchanged. -/
theorem mapDomain_collision_passive {m : ℕ} (i j : Fin m) (hji : j ≠ i)
    (e : Fin m →₀ ℕ) (k : Passive i j) :
    Finsupp.mapDomain (collisionIndex i j hji) e ⟨k.1, k.2.1⟩ = e k.1 := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add a n e ha hn ih =>
    rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.add_apply,
      Finsupp.mapDomain_single, ih]
    by_cases hi : a = i
    · subst a
      simp [k.2.1, k.2.2]
    · have heq : collisionIndex i j hji a = ⟨k.1, k.2.1⟩ ↔ a = k.1 := by
        simp [collisionIndex, hi, Subtype.ext_iff]
      simp only [Finsupp.single_apply, heq]

/-- A diagonal monomial: active power `q`, and one fixed mode at every spectator. -/
def diagonalExponent {N m : ℕ} (i j : Fin m) (_hji : j ≠ i) (q : ℕ)
    (b : Passive i j → Fin (N + 1)) : {k : Fin m // k ≠ i} →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k =>
    if hj : k.1 = j then q else (b ⟨k.1, k.2, hj⟩).val)

@[simp] theorem diagonalExponent_active {N m : ℕ}
    (i j : Fin m) (hji : j ≠ i) (q : ℕ) (b : Passive i j → Fin (N + 1)) :
    diagonalExponent i j hji q b ⟨j, hji⟩ = q := by simp [diagonalExponent]

@[simp] theorem diagonalExponent_passive {N m : ℕ}
    (i j : Fin m) (hji : j ≠ i) (q : ℕ) (b : Passive i j → Fin (N + 1))
    (k : Passive i j) : diagonalExponent i j hji q b ⟨k.1, k.2.1⟩ = (b k).val := by
  simp [diagonalExponent, k.2.2]

/-- Complete finite fiber description for an active-pair collision. -/
theorem mapDomain_collision_eq_iff {N m : ℕ} (i j : Fin m) (hji : j ≠ i)
    (a : Fin m → Fin (N + 1)) (q : ℕ) (b : Passive i j → Fin (N + 1)) :
    Finsupp.mapDomain (collisionIndex i j hji) (labelledExponent a) =
        diagonalExponent i j hji q b ↔
      (a i).val + (a j).val = q ∧ (fun k : Passive i j => a k.1) = b := by
  constructor
  · intro h
    constructor
    · have hc := congrArg (fun e => e ⟨j, hji⟩) h
      simpa only [mapDomain_collision_active, labelledExponent_apply,
        diagonalExponent_active] using hc
    · funext k
      apply Fin.ext
      have hc := congrArg (fun e => e ⟨k.1, k.2.1⟩) h
      simpa only [mapDomain_collision_passive i j hji _ k, labelledExponent_apply,
        diagonalExponent_passive] using hc
  · rintro ⟨hq, hb⟩
    ext k
    by_cases hj : k.1 = j
    · have hk : k = ⟨j, hji⟩ := Subtype.ext hj
      subst k
      simpa only [mapDomain_collision_active, labelledExponent_apply,
        diagonalExponent_active] using hq
    · let l : Passive i j := ⟨k.1, k.2, hj⟩
      have hl := congrFun hb l
      change Finsupp.mapDomain (collisionIndex i j hji) (labelledExponent a) ⟨l.1, l.2.1⟩ =
        diagonalExponent i j hji q b ⟨l.1, l.2.1⟩
      rw [mapDomain_collision_passive, labelledExponent_apply, diagonalExponent_passive]
      exact congrArg Fin.val hl

/-- The commutative monomial of the spectator particles. -/
def spectatorExponent {N m : ℕ} (i j : Fin m) (t : Fin m → σ)
    (b : Passive i j → Fin (N + 1)) : JetVar σ N →₀ ℕ :=
  ∑ k : Passive i j, Finsupp.single ⟨t k.1, b k⟩ 1

/-- Inserted tensor colors and an ordered pair of modes give precisely a quadratic
jet-monomial insertion into the spectator exponent. -/
theorem coloredExponent_insertPair {N m : ℕ} (ij : IncreasingPair (Fin m))
    (t : Fin m → σ) (xy : σ × σ) (ab : Fin (N + 1) × Fin (N + 1))
    (b : Passive ij.1.1 ij.1.2 → Fin (N + 1)) :
    coloredExponent (insertPair ij t xy)
      ((tupleEquiv ij.1.1 ij.1.2 (ne_of_gt ij.2)).symm (ab, b)) =
      insertExponent N (spectatorExponent ij.1.1 ij.1.2 t b) xy ab := by
  rw [coloredExponent, sum_active_passive ij.1.1 ij.1.2 (ne_of_gt ij.2)]
  simp only [tupleEquiv_symm_left, tupleEquiv_symm_right, tupleEquiv_symm_passive]
  have hi : insertPair ij t xy ij.1.1 = xy.1 := by
    simp [insertPair, ne_of_lt ij.2]
  have hj : insertPair ij t xy ij.1.2 = xy.2 := by simp [insertPair]
  have hk (k : Passive ij.1.1 ij.1.2) : insertPair ij t xy k.1 = t k.1 := by
    simp [insertPair, k.2.1, k.2.2]
  simp only [hi, hj, hk, insertExponent, spectatorExponent]
  abel

/-- A collision coefficient is an ordered convolution, with all spectator modes fixed. -/
theorem coeff_collision_tensorPolynomial {N m : ℕ}
    (F : (JetVar σ N →₀ ℕ) → K) (t : Fin m → σ)
    (i j : Fin m) (hji : j ≠ i) (q : ℕ) (b : Passive i j → Fin (N + 1)) :
    MvPolynomial.coeff (diagonalExponent i j hji q b)
        (collisionMap i j hji (tensorPolynomial F t)) =
      ∑ ab ∈ coefficientPairs N q,
        F (coloredExponent t ((tupleEquiv i j hji).symm (ab, b))) := by
  classical
  rw [tensorPolynomial, map_sum, MvPolynomial.coeff_sum]
  simp only [collisionMap, MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial]
  simp_rw [mapDomain_collision_eq_iff]
  let H := fun a : Fin m → Fin (N + 1) =>
    if (a i).val + (a j).val = q ∧ (fun k : Passive i j => a k.1) = b then
      F (coloredExponent t a) else 0
  change (∑ a, H a) = _
  calc
    (∑ a, H a) = ∑ z : (Fin (N + 1) × Fin (N + 1)) × (Passive i j → Fin (N + 1)),
        H ((tupleEquiv i j hji).symm z) :=
      (Equiv.sum_comp (tupleEquiv i j hji).symm H).symm
    _ = ∑ ab : Fin (N + 1) × Fin (N + 1),
        ∑ c : Passive i j → Fin (N + 1), H ((tupleEquiv i j hji).symm (ab, c)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ ab : Fin (N + 1) × Fin (N + 1),
        if ab.1.val + ab.2.val = q then
          F (coloredExponent t ((tupleEquiv i j hji).symm (ab, b))) else 0 := by
      apply Fintype.sum_congr
      intro ab
      have hc (c : Passive i j → Fin (N + 1)) :
          (fun k : Passive i j => (tupleEquiv i j hji).symm (ab, c) k.1) = c := by
        funext k
        exact tupleEquiv_symm_passive i j hji (ab, c) k
      by_cases hab : ab.1.val + ab.2.val = q
      · simp only [H, tupleEquiv_symm_left, tupleEquiv_symm_right, hc, hab, true_and,
          if_true]
        exact Fintype.sum_ite_eq' b _
      · simp only [H, tupleEquiv_symm_left, tupleEquiv_symm_right, hab, false_and,
          if_false, Finset.sum_const_zero]
    _ = _ := by rw [coefficientPairs, Finset.sum_filter]

variable [Fintype σ]

/-- Exact tensor-projected collision coefficient in terms of the independently defined
quadratic jet convolution. -/
theorem coeff_currentReadback {N m : ℕ} (F : (JetVar σ N →₀ ℕ) → K)
    (Q : σ × σ → K) (ij : IncreasingPair (Fin m)) (t : Fin m → σ)
    (q : ℕ) (b : Passive ij.1.1 ij.1.2 → Fin (N + 1)) :
    MvPolynomial.coeff (diagonalExponent ij.1.1 ij.1.2 (ne_of_gt ij.2) q b)
        (currentReadback Q ij t (tensorPolynomial F)) =
      ∑ xy, ∑ ab ∈ coefficientPairs N q,
        Q xy * F (insertExponent N (spectatorExponent ij.1.1 ij.1.2 t b) xy ab) := by
  classical
  change MvPolynomial.coeff (diagonalExponent ij.1.1 ij.1.2 (ne_of_gt ij.2) q b)
    (∑ xy, (MvPolynomial.C (Q xy) : MvPolynomial {k : Fin m // k ≠ ij.1.1} K) *
      collisionMap ij.1.1 ij.1.2 (ne_of_gt ij.2) (tensorPolynomial F (insertPair ij t xy))) = _
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_C_mul, coeff_collision_tensorPolynomial,
    Finset.mul_sum, coloredExponent_insertPair]

/-- Every coefficient that can occur in a readback has a bounded passive tuple. The
active exponent is the sum of two modes and need not itself lie in the jet box. -/
theorem exists_diagonalExponent_of_readback_coeff_ne_zero {N m : ℕ}
    (F : (JetVar σ N →₀ ℕ) → K) (Q : σ × σ → K)
    (ij : IncreasingPair (Fin m)) (t : Fin m → σ)
    (e : {k : Fin m // k ≠ ij.1.1} →₀ ℕ)
    (he : MvPolynomial.coeff e (currentReadback Q ij t (tensorPolynomial F)) ≠ 0) :
    ∃ (q : ℕ) (b : Passive ij.1.1 ij.1.2 → Fin (N + 1)),
      e = diagonalExponent ij.1.1 ij.1.2 (ne_of_gt ij.2) q b := by
  classical
  change MvPolynomial.coeff e
    (∑ xy, (MvPolynomial.C (Q xy) : MvPolynomial {k : Fin m // k ≠ ij.1.1} K) *
      collisionMap ij.1.1 ij.1.2 (ne_of_gt ij.2)
        (tensorPolynomial F (insertPair ij t xy))) ≠ 0 at he
  rw [MvPolynomial.coeff_sum] at he
  obtain ⟨xy, _, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [MvPolynomial.coeff_C_mul] at hxy
  have hcoeff := (mul_ne_zero_iff.mp hxy).2
  rw [tensorPolynomial, map_sum, MvPolynomial.coeff_sum] at hcoeff
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  simp only [collisionMap, MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial] at ha
  split at ha
  · rename_i h
    refine ⟨(a ij.1.1).val + (a ij.1.2).val, fun k => a k.1, h.symm.trans ?_⟩
    exact (mapDomain_collision_eq_iff _ _ _ a _ _).mpr ⟨rfl, rfl⟩
  · exact False.elim (ha rfl)

/-- All polynomial diagonal equations are captured by the explicit convolution tests. -/
theorem currentReadback_eq_zero_iff {N m : ℕ} (F : (JetVar σ N →₀ ℕ) → K)
    (Q : σ × σ → K) (ij : IncreasingPair (Fin m)) (t : Fin m → σ) :
    currentReadback Q ij t (tensorPolynomial F) = 0 ↔
      ∀ (q : ℕ) (b : Passive ij.1.1 ij.1.2 → Fin (N + 1)),
        (∑ xy, ∑ ab ∈ coefficientPairs N q,
          Q xy * F (insertExponent N (spectatorExponent ij.1.1 ij.1.2 t b) xy ab)) = 0 := by
  constructor
  · intro h q b
    rw [← coeff_currentReadback, h]
    exact MvPolynomial.coeff_zero _
  · intro h
    apply MvPolynomial.ext
    intro e
    rw [MvPolynomial.coeff_zero]
    by_contra he
    obtain ⟨q, b, rfl⟩ := exists_diagonalExponent_of_readback_coeff_ne_zero F Q ij t e he
    exact he ((coeff_currentReadback F Q ij t q b).trans (h q b))

omit [Fintype σ] in
/-- The exact particle count after inserting the two modes of a quadratic relation. -/
theorem insertExponent_particleDegree {N : ℕ} (e : JetVar σ N →₀ ℕ)
    (xy : σ × σ) (ab : Fin (N + 1) × Fin (N + 1)) :
    Finsupp.weight (fun _ : JetVar σ N => 1) (insertExponent N e xy ab) =
      Finsupp.weight (fun _ : JetVar σ N => 1) e + 2 := by
  simp [insertExponent, map_add, Finsupp.weight_single]

omit [Fintype σ] in
/-- The exact derivative count after inserting a quadratic relation's two modes. -/
theorem insertExponent_derivativeDegree {N : ℕ} (e : JetVar σ N →₀ ℕ)
    (xy : σ × σ) (ab : Fin (N + 1) × Fin (N + 1)) :
    Finsupp.weight (fun v : JetVar σ N => v.order.val) (insertExponent N e xy ab) =
      Finsupp.weight (fun v : JetVar σ N => v.order.val) e + ab.1.val + ab.2.val := by
  simp [insertExponent, map_add, Finsupp.weight_single]

/-- Fixed-degree support kills quadratic convolutions whose active order exceeds the
derivative degree. This deals with the unretained diagonal powers explicitly. -/
theorem convolution_zero_of_degree_lt {N m r : ℕ} (F : (JetVar σ N →₀ ℕ) → K)
    (hF : SupportedBidegree N m r F) (Q : σ × σ → K)
    (q : ℕ) (hq : r < q) (e : JetVar σ N →₀ ℕ) :
    (∑ xy, ∑ ab ∈ coefficientPairs N q, Q xy * F (insertExponent N e xy ab)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro xy _
  apply Finset.sum_eq_zero
  intro ab hab
  have hz : F (insertExponent N e xy ab) = 0 := by
    by_contra hn
    have hd := (hF _ hn).2
    rw [insertExponent_derivativeDegree] at hd
    have hs := (mem_coefficientPairs ab.1 ab.2).mp hab
    omega
  rw [hz, mul_zero]

/-- The full finite-jet convolution equations imply the literal current collisions. -/
theorem currentEquations_of_coefficientEquations {N m r : ℕ}
    (Q : ρ → σ × σ → K) (F : (JetVar σ N →₀ ℕ) → K)
    (hF : SupportedBidegree N m r F) (hr : r ≤ N) (hQ : CoefficientEquations Q N F) :
    CurrentEquations Q (tensorPolynomial (m := m) F) := by
  intro s ij t
  apply (currentReadback_eq_zero_iff F (Q s) ij t).mpr
  intro q b
  by_cases hq : q ≤ N
  · exact hQ s ⟨q, Nat.lt_succ_iff.mpr hq⟩ (spectatorExponent ij.1.1 ij.1.2 t b)
  · exact convolution_zero_of_degree_lt F hF (Q s) q (by omega) _

/-- Removing the two active labels reduces particle number by precisely two. -/
theorem passive_card {m : ℕ} (i j : Fin m) (hji : j ≠ i) :
    Fintype.card (Passive i j) + 2 = m := by
  have h := sum_active_passive i j hji (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  omega

omit [Fintype σ] in
/-- Every commutative spectator exponent is represented by a passive color/mode tuple.
The supplied color fills the two irrelevant active entries of the tensor label. -/
theorem exists_spectatorExponent {N m : ℕ} (x : σ) (ij : IncreasingPair (Fin m))
    (e : JetVar σ N →₀ ℕ)
    (he : Finsupp.weight (fun _ : JetVar σ N => 1) e = Fintype.card (Passive ij.1.1 ij.1.2)) :
    ∃ (t : Fin m → σ) (b : Passive ij.1.1 ij.1.2 → Fin (N + 1)),
      spectatorExponent ij.1.1 ij.1.2 t b = e := by
  classical
  obtain ⟨u, a, hua⟩ := exists_coloredExponent e he
  let g := Fintype.equivFin (Passive ij.1.1 ij.1.2)
  let t := (tupleEquiv ij.1.1 ij.1.2 (ne_of_gt ij.2)).symm ((x, x), u ∘ g)
  refine ⟨t, a ∘ g, ?_⟩
  unfold spectatorExponent
  simp only [t, tupleEquiv_symm_passive, Function.comp_apply]
  rw [g.sum_comp (fun k => Finsupp.single (⟨u k, a k⟩ : JetVar σ N) 1)]
  exact hua

/-- Conversely, literal current collisions imply all finite-jet coefficient equations,
including arbitrary spectators. Off-sector spectators vanish by particle count. -/
theorem coefficientEquations_of_currentEquations {N m r : ℕ}
    (Q : ρ → σ × σ → K) (F : (JetVar σ N →₀ ℕ) → K)
    (hF : SupportedBidegree N m r F) (hQ : CurrentEquations Q (tensorPolynomial (m := m) F)) :
    CoefficientEquations Q N F := by
  classical
  intro s n e
  by_contra hneq
  obtain ⟨xy, _, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hneq
  obtain ⟨ab, hab, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxy
  have hm := (hF _ (mul_ne_zero_iff.mp hterm).2).1
  rw [insertExponent_particleDegree] at hm
  have hm2 : 2 ≤ m := by omega
  let ij : IncreasingPair (Fin m) :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), Nat.zero_lt_one⟩
  have hecard : Finsupp.weight (fun _ : JetVar σ N => 1) e =
      Fintype.card (Passive ij.1.1 ij.1.2) := by
    have hc := passive_card ij.1.1 ij.1.2 (ne_of_gt ij.2)
    omega
  obtain ⟨t, b, hb⟩ := exists_spectatorExponent xy.1 ij e hecard
  have hz := (currentReadback_eq_zero_iff F (Q s) ij t).mp (hQ s ij t) n b
  rw [hb] at hz
  exact hneq hz

/-- Exact kernel comparison: in the stable fixed degree, the independently presented
quadratic coefficient equations are equivalent to the literal current collision equations. -/
theorem coefficientEquations_iff_currentEquations {N m r : ℕ}
    (Q : ρ → σ × σ → K) (F : (JetVar σ N →₀ ℕ) → K)
    (hF : SupportedBidegree N m r F) (hr : r ≤ N) :
    CoefficientEquations Q N F ↔ CurrentEquations Q (tensorPolynomial (m := m) F) :=
  ⟨currentEquations_of_coefficientEquations Q F hF hr,
    coefficientEquations_of_currentEquations Q F hF⟩

/-- Membership in the independently defined current carrier is exactly the finite-jet
convolution condition, since simultaneous symmetry was already proved by reindexing. -/
theorem mem_currentCarrier_iff_coefficientEquations {N m r : ℕ}
    (Q : ρ → σ × σ → K) (F : (JetVar σ N →₀ ℕ) → K)
    (hF : SupportedBidegree N m r F) (hr : r ≤ N) :
    tensorPolynomial F ∈ currentCarrier Q m 0 ↔ CoefficientEquations Q N F := by
  change (Symmetric (tensorPolynomial F) ∧ CurrentEquations Q (tensorPolynomial F)) ↔ _
  rw [and_iff_right (tensorPolynomial_symmetric F)]
  exact (coefficientEquations_iff_currentEquations Q F hF hr).symm

/-- Simultaneous fixed-bidegree support and the complete quadratic convolution equations. -/
def fixedQuadraticCoefficientSpace (Q : ρ → σ × σ → K) (N m r : ℕ) :
    Submodule K ((JetVar σ N →₀ ℕ) → K) :=
  fixedCoefficientSpace N m r ⊓ coefficientCarrier Q N

/-- Restrict the concrete reindexing to the two exact quadratic kernels. -/
def fixedQuadraticReindexingMap (Q : ρ → σ × σ → K) (N m r : ℕ) (hr : r ≤ N) :
    fixedQuadraticCoefficientSpace Q N m r →ₗ[K] degreePiece (currentCarrier Q m 0) r where
  toFun F := ⟨⟨tensorPolynomial F.1,
    (mem_currentCarrier_iff_coefficientEquations Q F.1 F.2.1 hr).mpr F.2.2⟩,
      tensorPolynomial_homogeneous F.1 F.2.1⟩
  map_add' F G := by
    apply Subtype.ext
    apply Subtype.ext
    funext t
    simp only [tensorPolynomial, Submodule.coe_add, Pi.add_apply, map_add,
      Finset.sum_add_distrib]
  map_smul' a F := by
    apply Subtype.ext
    apply Subtype.ext
    funext t
    simp only [tensorPolynomial, Submodule.coe_smul, Pi.smul_apply,
      MvPolynomial.smul_monomial, Finset.smul_sum, RingHom.id_apply]

theorem fixedQuadraticReindexingMap_bijective
    (Q : ρ → σ × σ → K) (N m r : ℕ) (hr : r ≤ N) :
    Function.Bijective (fixedQuadraticReindexingMap Q N m r hr) := by
  constructor
  · intro F G h
    apply Subtype.ext
    apply tensorPolynomial_injective_on_particleSector F.1 G.1
    · intro e he
      by_contra hn
      exact he (F.2.1 e hn).1
    · intro e he
      by_contra hn
      exact he (G.2.1 e hn).1
    · exact congrArg (fun p => p.1.1) h
  · intro p
    let p' : homogeneousSymmetricSpace (K := K) (σ := σ) m r :=
      ⟨p.1.1, p.1.2.1, p.2⟩
    obtain ⟨F, hF⟩ := (fixedReindexingMap_bijective (K := K) (σ := σ) N m r hr).2 p'
    have hpoly : tensorPolynomial F.1 = p.1.1 := congrArg Subtype.val hF
    have hcoeff : CoefficientEquations Q N F.1 := by
      apply (coefficientEquations_iff_currentEquations Q F.1 F.2 hr).mpr
      rw [hpoly]
      exact p.1.2.2
    refine ⟨⟨F.1, F.2, hcoeff⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hpoly

/-- Exact fixed-degree identification of the quadratic coefficient carrier with the
polynomial current carrier. Both sides are independently defined and the map is explicit. -/
def fixedQuadraticReindexingEquiv (Q : ρ → σ × σ → K) (N m r : ℕ) (hr : r ≤ N) :
    fixedQuadraticCoefficientSpace Q N m r ≃ₗ[K] degreePiece (currentCarrier Q m 0) r :=
  LinearEquiv.ofBijective (fixedQuadraticReindexingMap Q N m r hr)
    (fixedQuadraticReindexingMap_bijective Q N m r hr)

end

end VOA.QuadraticCurrentCollisionCoefficients

section AxiomAudit
open VOA.QuadraticCurrentCollisionCoefficients in
#print axioms coeff_currentReadback
open VOA.QuadraticCurrentCollisionCoefficients in
#print axioms coefficientEquations_iff_currentEquations
open VOA.QuadraticCurrentCollisionCoefficients in
#print axioms fixedQuadraticReindexingEquiv
end AxiomAudit
