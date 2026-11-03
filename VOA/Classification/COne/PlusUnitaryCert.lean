/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusUnitaryZhu
import VOA.Classification.COne.PlusC2M1Cert

/-!
# Zhu products in `M(1)⁺` as executable polynomials

Notation of `PlusC2M1Cert.lean`: a state of `M1P = M(1)⁺` is described by a raw polynomial in the
orthonormal oscillators `x_i = h(−i−1)` (`HasPoly`).  This file extends the product evaluator to
**inhomogeneous** polynomial states (`polyActW`) and computes

* the Zhu product `s ∗ y = Σ_i C(k,i) s₍ᵢ₋₁₎y` (`zhuR`, `hasPoly_zhuMul`), and
* the Frenkel–Zhu residues `Pres s y n = Σ_i C(k+n,i) s₍ᵢ₋₂₋ₙ₎y ∈ O(M1P)` (`presR`,
  `hasPoly_Pres`),

so that a membership `y ∈ O(M1P)` can be certified by a polynomial identity checked with
`decide +kernel` (`mem_O_of_cert`).  It also records that the inclusion `M(1)⁺ ↪ V_{2m}⁺` is a
graded VOA homomorphism (`incl_gradedHom`).
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne.PlusUnitary

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-! ## §1  The inclusion `M(1)⁺ ↪ V⁺` -/

theorem incl_gradedHom : GradedHom (M1P m hm) (V2mPlus m hm) (incl m hm) where
  map_vacuum := rfl
  map_smul a n b := Subtype.ext (by rw [V2mPlus_smul_coe, incl_coe, incl_coe, incl_coe, M1P_smul_coe])
  map_grading {n a} ha := ha

theorem incl_omega : incl m hm (ωM m hm) = (V2mPlus m hm).conformalVector := rfl

/-! ## §2  Products with inhomogeneous polynomial states -/

/-- `Y(Q,z)_s P` for a raw polynomial `P` whose words may have different weights. -/
def polyActW (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.flatMap fun t => polyAct Q s (wWt t.2) [t]

theorem evR_singleton (t : ℚ × List ℕ) :
    evR (a0 m) [t] = ((t.1 : ℚ) : ℂ) • evalWord (xv (a0 m)) t.2 := by
  rw [evR_cons, evR_nil, add_zero]

theorem V2m_smul_evR_W (Q : RawPoly ℕ) (n : ℤ) :
    ∀ P : RawPoly ℕ, (V2m m hm).smul (latStateGen (latP m) (evR (a0 m) Q) 0) n
        (latStateGen (latP m) (evR (a0 m) P) 0) =
      latStateGen (latP m) (evR (a0 m) (polyActW Q (-n - 1) P)) 0
  | [] => by
    rw [polyActW, List.flatMap_nil, evR_nil]
    simp [latStateGen]
  | t :: P => by
    have hsplit : evR (a0 m) (t :: P) = evR (a0 m) [t] + evR (a0 m) P := by
      rw [evR_cons, evR_singleton]
    rw [hsplit, latStateGen_add_boson, PreVertexAlgebra.smul_add_right,
      V2m_smul_evR m hm Q [t] n (wWt t.2) (by simp), V2m_smul_evR_W Q n P,
      show polyActW Q (-n - 1) (t :: P) = polyAct Q (-n - 1) (wWt t.2) [t] ++ polyActW Q (-n - 1) P
        from rfl, evR_append, latStateGen_add_boson]

/-- **Products of (inhomogeneous) polynomial states.** -/
theorem M1P_smul_polyW {u v : (m1Sub m hm).carrier} {Q P : RawPoly ℕ} (hu : HasPoly m hm u Q)
    (hv : HasPoly m hm v P) (n : ℤ) :
    HasPoly m hm ((M1P m hm).smul u n v) (polyActW Q (-n - 1) P) := by
  rw [HasPoly, M1P_smul_coe, hu, hv, V2m_smul_evR_W]

theorem hasPoly_add {u v : (m1Sub m hm).carrier} {P Q : RawPoly ℕ} (hu : HasPoly m hm u P)
    (hv : HasPoly m hm v Q) : HasPoly m hm (u + v) (P ++ Q) := by
  rw [HasPoly, Submodule.coe_add, hu, hv, evR_append, latStateGen_add_boson]

theorem hasPoly_smul {u : (m1Sub m hm).carrier} {P : RawPoly ℕ} (hu : HasPoly m hm u P) (c : ℚ) :
    HasPoly m hm (((c : ℚ) : ℂ) • u) (scaleR c P) := by
  rw [HasPoly, Submodule.coe_smul, hu, evR_scaleR, latStateGen_csmul]

theorem hasPoly_zero : HasPoly m hm 0 ([] : RawPoly ℕ) := by
  rw [HasPoly, evR_nil]; simp [latStateGen]

/-- `Σ_{i ∈ L} f i` as a raw polynomial, with the matching `HasPoly`. -/
theorem hasPoly_sum_range (n : ℕ) (f : ℕ → (m1Sub m hm).carrier) (F : ℕ → RawPoly ℕ)
    (hf : ∀ i, HasPoly m hm (f i) (F i)) :
    HasPoly m hm (∑ i ∈ Finset.range n, f i) ((List.range n).flatMap F) := by
  induction n with
  | zero => simpa using hasPoly_zero m hm
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact hasPoly_add m hm ih (hf n)

/-! ## §3  The Zhu product and the Frenkel–Zhu residues -/

theorem cbz_nat_eq_zero {a i : ℕ} (h : a < i) : cbz (a : ℤ) (i : ℤ) = 0 := by
  rw [cbz_apply_nonneg _ (by positivity), show ((i : ℤ)).toNat = i by simp]
  simp only [gBinom]
  rw [Finset.prod_eq_zero (i := a) (Finset.mem_range.mpr h) (by simp)]
  simp

/-- The polynomial of `s ∗ y` for `s` of weight `k`. -/
def zhuR (k : ℕ) (Q P : RawPoly ℕ) : RawPoly ℕ :=
  (List.range (k + 1)).flatMap fun i => scaleR (k.choose i : ℚ) (polyActW Q (-(i : ℤ)) P)

/-- The polynomial of `Pres s y n` for `s` of weight `k`. -/
def presR (k : ℕ) (Q P : RawPoly ℕ) (n : ℕ) : RawPoly ℕ :=
  (List.range (k + n + 1)).flatMap fun i =>
    scaleR ((k + n).choose i : ℚ) (polyActW Q ((n : ℤ) + 1 - i) P)

theorem hasPoly_zhuMul {s y : (m1Sub m hm).carrier} {k : ℕ} (hs : s ∈ (M1P m hm).grading (k : ℤ))
    {Q P : RawPoly ℕ} (hQ : HasPoly m hm s Q) (hP : HasPoly m hm y P) :
    HasPoly m hm (zhuMul (M1P m hm) s y) (zhuR k Q P) := by
  rw [zhuMul_homogeneous _ hs, show ((k : ℤ)).toNat = k by simp, zhuR]
  refine hasPoly_sum_range m hm _ _ _ fun i => ?_
  by_cases hi : i ≤ k
  · rw [cbz_natCast_eq_choose hi, show ((k.choose i : ℕ) : ℂ) = (((k.choose i : ℚ)) : ℂ) by push_cast; rfl]
    have := M1P_smul_polyW m hm hQ hP ((i : ℤ) - 1)
    rw [show -((i : ℤ) - 1) - 1 = -(i : ℤ) by ring] at this
    exact hasPoly_smul m hm this _
  · rw [cbz_nat_eq_zero (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    have := hasPoly_smul m hm (M1P_smul_polyW m hm hQ hP ((i : ℤ) - 1)) 0
    rwa [show -((i : ℤ) - 1) - 1 = -(i : ℤ) by ring, Rat.cast_zero] at this

theorem hasPoly_Pres {s y : (m1Sub m hm).carrier} (k : ℕ) {Q P : RawPoly ℕ}
    (hQ : HasPoly m hm s Q) (hP : HasPoly m hm y P) (n : ℕ) :
    HasPoly m hm (Pres (M1P m hm) k s y n) (presR k Q P n) := by
  rw [Pres, presR]
  refine hasPoly_sum_range m hm _ _ _ fun i => ?_
  by_cases hi : i ≤ k + n
  · rw [show ((k : ℤ) + n) = (((k + n : ℕ)) : ℤ) by push_cast; ring, cbz_natCast_eq_choose hi,
      show (((k + n).choose i : ℕ) : ℂ) = ((((k + n).choose i : ℚ)) : ℂ) by push_cast; rfl]
    have := M1P_smul_polyW m hm hQ hP ((i : ℤ) - 2 - n)
    rw [show -((i : ℤ) - 2 - n) - 1 = (n : ℤ) + 1 - i by ring] at this
    exact hasPoly_smul m hm this _
  · rw [show ((k : ℤ) + n) = (((k + n : ℕ)) : ℤ) by push_cast; ring, cbz_nat_eq_zero (by omega),
      Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    have := hasPoly_smul m hm (M1P_smul_polyW m hm hQ hP ((i : ℤ) - 2 - n)) 0
    rwa [show -((i : ℤ) - 2 - n) - 1 = (n : ℤ) + 1 - i by ring, Rat.cast_zero] at this

/-- Word states lie in their grading piece. -/
theorem mkW_mem_grading (b : List ℕ) (hb : Even b.length) :
    mkW m hm b hb ∈ (M1P m hm).grading (wWt b : ℤ) := by
  rw [M1P_mem_grading_iff]
  exact latStateGen_mem_grading m hm (evR_mem_grading (a0 m) [(1, b)] (by simp))

/-! ## §4  `O(M1P)` certificates -/

/-- A certificate entry: `c · Pres(x_a, x_b, n)`. -/
abbrev OEntry := ℚ × List ℕ × List ℕ × ℕ

/-- The polynomial combination of a certificate. -/
def ocert (L : List OEntry) : List (ℚ × RawPoly ℕ) :=
  L.map fun t => (t.1, presR (wWt t.2.1) [(1, t.2.1)] [(1, t.2.2.1)] t.2.2.2)

theorem ocert_mem (L : List OEntry) (hL : ∀ t ∈ L, Even t.2.1.length ∧ Even t.2.2.1.length) :
    ∀ t ∈ ocert L, ∃ x ∈ O (M1P m hm), HasPoly m hm x t.2 := by
  intro t ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  obtain ⟨ha, hb⟩ := hL e he
  exact ⟨Pres (M1P m hm) (wWt e.2.1) (mkW m hm e.2.1 ha) (mkW m hm e.2.2.1 hb) e.2.2.2,
    Pres_mem_O _ (mkW_mem_grading m hm _ ha) _ _,
    hasPoly_Pres m hm _ (hasPoly_mkW m hm _ ha) (hasPoly_mkW m hm _ hb) _⟩

/-- **`O(M1P)`-membership from a kernel-checked polynomial identity.** -/
theorem mem_O_of_cert {y : (m1Sub m hm).carrier} {A : RawPoly ℕ} (hy : HasPoly m hm y A)
    (L : List OEntry) (hL : ∀ t ∈ L, Even t.2.1.length ∧ Even t.2.2.1.length)
    (h : normR A = normR (lc (ocert L))) : y ∈ O (M1P m hm) :=
  mem_of_cert m hm _ hy _ (ocert_mem m hm L hL) h

/-! ## §5  Monomials in `ω` and `W` under the Zhu product -/

/-- `W^{∗j} ∗ ω^{∗i} ∗ 𝟙`. -/
noncomputable def monoE (i j : ℕ) : (m1Sub m hm).carrier :=
  (fun y => zhuMul (M1P m hm) (WM m hm) y)^[j]
    ((fun y => zhuMul (M1P m hm) (ωM m hm) y)^[i] (M1P m hm).vacuum)

/-- Its polynomial. -/
def monoR (i j : ℕ) : RawPoly ℕ :=
  (fun P => normR (zhuR 4 WR P))^[j] ((fun P => normR (zhuR 2 omR P))^[i] vacR)

theorem hasPoly_monoE (i j : ℕ) : HasPoly m hm (monoE m hm i j) (monoR i j) := by
  have hω : ∀ k : ℕ, HasPoly m hm ((fun y => zhuMul (M1P m hm) (ωM m hm) y)^[k] (M1P m hm).vacuum)
      ((fun P => normR (zhuR 2 omR P))^[k] vacR) := by
    intro k
    induction k with
    | zero => exact hasPoly_vacuum m hm
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hasPoly_normR m hm (hasPoly_zhuMul m hm (ωM_mem_grading m hm) (hasPoly_omega m hm) ih)
  rw [monoE, monoR]
  induction j with
  | zero => exact hω i
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hasPoly_normR m hm (hasPoly_zhuMul m hm (WM_mem_grading m hm) (hasPoly_W m hm) ih)

/-- The zero mode of a monomial on a top vector. -/
theorem oMod_monoE {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2mPlus m hm) M)
    {h w : ℂ} (hcw : IsLowestWeight N h) {x : M} (hx : x ∈ N.weight h)
    (hW : oMod N (incl m hm (WM m hm)) x = w • x) (i j : ℕ) :
    oMod N (incl m hm (monoE m hm i j)) x = (h ^ i * w ^ j) • x := by
  have hφ := incl_gradedHom m hm
  have hω : oMod N (incl m hm (ωM m hm)) x = h • x := by
    rw [incl_omega, oMod_homogeneous N (V2mPlus m hm).conformal_mem]
    exact N.L0_weight h x hx
  have hωi : ∀ k : ℕ, oMod N (incl m hm ((fun y => zhuMul (M1P m hm) (ωM m hm) y)^[k]
      (M1P m hm).vacuum)) x = (h ^ k) • x := by
    intro k
    induction k with
    | zero => simp [hφ.map_vacuum, oMod_vacuum]
    | succ k ih =>
      rw [Function.iterate_succ_apply', hφ.map_zhuMul (ωM_mem_grading m hm),
        oMod_zhuMul_lowest_all N hcw _ _ hx, ih, map_smul, hω, smul_smul, pow_succ, mul_comm]
  rw [monoE]
  induction j with
  | zero => simpa using hωi i
  | succ j ih =>
    rw [Function.iterate_succ_apply', hφ.map_zhuMul (WM_mem_grading m hm),
      oMod_zhuMul_lowest_all N hcw _ _ hx, ih, map_smul, hW, smul_smul, pow_succ]
    ring_nf

end VOA.Classification.COne.PlusUnitary
