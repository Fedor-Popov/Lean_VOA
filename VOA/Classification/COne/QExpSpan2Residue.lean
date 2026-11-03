/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpSpan2Units

/-!
# Residue parts of power series and the Cramer frame algebra

`resPart N r f` keeps the coefficients of `f` at exponents `≡ r (mod N)`.

* `resPart_zero_mul`: `[f g]^{(0)} = Σ_{s<N} f^{(-s)} g^{(s)}`;
* `resPart_eq_X_pow_mul`: `f^{(s)} = X^s · resShift`, with constant term `coeff s f`;
* `isUnit_det_of_triangular`: a matrix that is triangular for an injective rank function and
  has unit diagonal has unit determinant;
* `frame_cramer_awaySat`: if `Σ_j (X^{e j} B'_{ij}) Y_j = G_i` with `B'` over a finite
  `ℤ[1/M]`-algebra `A`, `det (B'(0))` a unit of `A`, and every `G_i` with a finite integer
  coefficient lattice, then every `Y_j` has coefficients in `awaySat M` of a finite lattice.
-/

open PowerSeries

noncomputable section

namespace VOA.Classification.COne.SSHecke

variable {R : Type*} [CommRing R]

/-- The exponents `≡ r (mod N)` part of a power series. -/
def resPart (N r : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => if n % N = r % N then coeff n f else 0

theorem coeff_resPart (N r : ℕ) (f : PowerSeries R) (n : ℕ) :
    coeff n (resPart N r f) = if n % N = r % N then coeff n f else 0 := by
  simp [resPart]

theorem coeff_resPart_self (N : ℕ) (f : PowerSeries R) (n : ℕ) :
    coeff n (resPart N n f) = coeff n f := by
  simp [coeff_resPart]

theorem resPart_map {S : Type*} [CommRing S] (φ : R →+* S) (N r : ℕ) (f : PowerSeries R) :
    PowerSeries.map φ (resPart N r f) = resPart N r (PowerSeries.map φ f) := by
  ext n
  simp only [coeff_map, coeff_resPart]
  split_ifs <;> simp

/-- If `(a + b) % N = 0` then `a % N = (N - b % N) % N`. -/
theorem mod_eq_sub_mod_of_add {N a b : ℕ} (hN : 0 < N) (h : (a + b) % N = 0) :
    a % N = (N - b % N) % N := by
  have ha : a % N < N := Nat.mod_lt _ hN
  have hb : b % N < N := Nat.mod_lt _ hN
  have hab : (a % N + b % N) % N = 0 := by rw [← Nat.add_mod]; exact h
  by_cases hb0 : b % N = 0
  · rw [hb0, Nat.add_zero, Nat.mod_eq_of_lt ha] at hab
    rw [hb0, hab, Nat.sub_zero, Nat.mod_self]
  · have hge : N ≤ a % N + b % N := by
      by_contra hlt
      rw [Nat.mod_eq_of_lt (by omega)] at hab
      omega
    rw [← Nat.sub_add_cancel hge, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at hab
    rw [Nat.mod_eq_of_lt (by omega : N - b % N < N)]
    omega

/-- `[f g]^{(0)} = Σ_{s<N} f^{(-s)} g^{(s)}`. -/
theorem resPart_zero_mul {N : ℕ} (hN : 0 < N) (f g : PowerSeries R) :
    resPart N 0 (f * g) =
      ∑ s ∈ Finset.range N, resPart N ((N - s) % N) f * resPart N s g := by
  ext n
  rw [coeff_resPart, map_sum, coeff_mul]
  simp only [coeff_mul, coeff_resPart]
  rw [Finset.sum_comm]
  by_cases hn : n % N = 0 % N
  · rw [if_pos hn]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    rw [Finset.sum_eq_single (x.2 % N)]
    · have h2 : x.2 % N = x.2 % N % N := (Nat.mod_mod _ _).symm
      have h1 : x.1 % N = (N - x.2 % N) % N % N := by
        rw [Nat.mod_mod]
        have hsum : (x.1 + x.2) % N = 0 := by rw [hx]; simpa using hn
        exact mod_eq_sub_mod_of_add hN hsum
      rw [if_pos h1, if_pos h2]
    · intro b hb hne
      have : ¬ x.2 % N = b % N := by
        rw [Finset.mem_range] at hb
        rw [Nat.mod_eq_of_lt hb]
        exact fun h => hne h.symm
      rw [if_neg this, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.mod_lt _ hN)) h
  · rw [if_neg hn]
    symm
    refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun s hs => ?_
    rw [Finset.mem_antidiagonal] at hx
    rw [Finset.mem_range] at hs
    by_cases h1 : x.1 % N = (N - s) % N % N
    · by_cases h2 : x.2 % N = s % N
      · exfalso
        apply hn
        have key : ((N - s) % N + s % N) % N = 0 := by
          rcases Nat.eq_zero_or_pos s with rfl | hs0
          · simp
          · rw [Nat.mod_eq_of_lt (by omega : N - s < N), Nat.mod_eq_of_lt hs,
              Nat.sub_add_cancel hs.le, Nat.mod_self]
        rw [← hx, Nat.zero_mod, Nat.add_mod, h1, h2, Nat.mod_mod]
        exact key
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

/-- The shifted residue part `X^{-s} f^{(s)}`. -/
def resShift (N s : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => coeff (n + s) (resPart N s f)

theorem resPart_eq_X_pow_mul {N s : ℕ} (hs : s < N) (f : PowerSeries R) :
    resPart N s f = X ^ s * resShift N s f := by
  ext n
  rw [coeff_X_pow_mul']
  split_ifs with h
  · simp [resShift, Nat.sub_add_cancel h]
  · rw [coeff_resPart, if_neg]
    rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (by omega)]
    omega

theorem constantCoeff_resShift {N s : ℕ} (_hs : s < N) (f : PowerSeries R) :
    constantCoeff (resShift N s f) = coeff s f := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [resShift, coeff_resPart]

theorem resShift_map {S : Type*} [CommRing S] (φ : R →+* S) (N s : ℕ) (f : PowerSeries R) :
    PowerSeries.map φ (resShift N s f) = resShift N s (PowerSeries.map φ f) := by
  ext n
  simp only [resShift, coeff_map, coeff_mk, ← resPart_map]

/-- Triangular matrices with unit diagonal have unit determinant. -/
theorem isUnit_det_of_triangular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι R) (ρ : ι → ℕ) (hρ : Function.Injective ρ)
    (hzero : ∀ i j, ρ j < ρ i → J i j = 0) (hdiag : ∀ i, IsUnit (J i i)) :
    IsUnit J.det := by
  letI : LinearOrder ι := LinearOrder.lift' ρ hρ
  have hT : J.BlockTriangular id := fun i j hij => hzero i j hij
  rw [Matrix.det_of_upperTriangular hT]
  exact IsUnit.prod_univ_iff.mpr hdiag

/-- **The Cramer step.** All coefficient arithmetic of the frame route. -/
theorem frame_cramer_awaySat {M : ℕ} (hM : M ≠ 0) (A : Subalgebra (zInv M) ℂ)
    (hA : A.toSubmodule.FG) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B' : Matrix ι ι (PowerSeries A)) (e : ι → ℕ)
    (hdet : IsUnit (Matrix.det (fun i j => constantCoeff (B' i j))))
    (Y G : ι → PowerSeries ℂ)
    (hG : ∀ i, ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, coeff n (G i) ∈ L)
    (heq : ∀ i, ∑ j, PowerSeries.map (algebraMap A ℂ) (X ^ e j * B' i j) * Y j = G i)
    (j : ι) : ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, coeff n (Y j) ∈ awaySat M L := by
  classical
  choose L hL hLc using hG
  let LA : Submodule A ℂ := ⨆ i, Submodule.span A (L i : Set ℂ)
  have hLA : LA.FG := Submodule.fg_iSup _ fun i => (hL i).span
  have hGA : ∀ i n, coeff n (G i) ∈ LA :=
    fun i n => Submodule.mem_iSup_of_mem i (Submodule.subset_span (hLc i n))
  obtain ⟨K, hK, hKL⟩ := fg_extension_exists_lattice hM A hA hLA
  refine ⟨K, hK, fun n => hKL _ ?_⟩
  let φ : PowerSeries A →+* PowerSeries ℂ := PowerSeries.map (algebraMap A ℂ)
  let B : Matrix ι ι (PowerSeries A) := Matrix.of fun i j => X ^ e j * B' i j
  let t : PowerSeries A := Matrix.det B'
  have ht : IsUnit (constantCoeff t) := by
    have := RingHom.map_det (constantCoeff (R := A)) B'
    simp only [t, this]
    exact hdet
  have hdetB : Matrix.det B = X ^ (∑ i, e i) * t := by
    simp only [B, t, Matrix.det_mul_row, Finset.prod_pow_eq_pow_sum]
  have hmul : Matrix.mulVec (φ.mapMatrix B) Y = G := by
    funext i
    simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, B,
      Matrix.of_apply]
    exact heq i
  have hcr : (φ.mapMatrix B).det • Y = Matrix.mulVec (φ.mapMatrix B).adjugate G := by
    rw [← hmul, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hj := congrFun hcr j
  simp only [Pi.smul_apply, smul_eq_mul] at hj
  rw [← RingHom.map_det, hdetB, ← RingHom.map_adjugate] at hj
  apply coeff_mem_of_mul_shift_unit (∑ i, e i) t ht
  intro m
  have hX : (X ^ (∑ i, e i) * PowerSeries.map (algebraMap A ℂ) t) =
      φ (X ^ (∑ i, e i) * t) := by simp [φ]
  rw [hX, hj]
  simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mul_comm]
  exact coeff_mul_map_mem _ (hGA i) m

end VOA.Classification.COne.SSHecke
