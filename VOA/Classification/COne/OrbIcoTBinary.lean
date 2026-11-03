import VOA.Classification.COne.OrbIcoTChannel
import VOA.Classification.COne.OrbIcoSBinary

/-! The sixth-channel bilinear map on binary forms and the icosahedral coupling. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoT
open VOA VertexOperatorAlgebra OrbSpan OrbIco OrbPrim OrbRat6 MvPolynomial

def B6 : P2 →ₗ[ℂ] P2 →ₗ[ℂ] P2 :=
  (basisMonomials (Fin 2) ℂ).constr ℂ fun e => (basisMonomials (Fin 2) ℂ).constr ℂ fun f =>
    (sixthCoeff (e 1) (f 1) : ℂ) • (X 0 ^ (18 - (e 1 + f 1)) * X 1 ^ (e 1 + f 1 - 6))

theorem B6_monomial (e f : Fin 2 →₀ ℕ) :
    B6 (monomial e 1) (monomial f 1) =
      (sixthCoeff (e 1) (f 1) : ℂ) • (X 0 ^ (18 - (e 1 + f 1)) * X 1 ^ (e 1 + f 1 - 6)) := by
  have he : (monomial e (1 : ℂ) : P2) = basisMonomials (Fin 2) ℂ e := by
    rw [coe_basisMonomials]
  have hf : (monomial f (1 : ℂ) : P2) = basisMonomials (Fin 2) ℂ f := by
    rw [coe_basisMonomials]
  rw [he, hf, B6, (basisMonomials (Fin 2) ℂ).constr_basis, (basisMonomials (Fin 2) ℂ).constr_basis]

theorem Tb_B6_monomial {e f : Fin 2 →₀ ℕ} (he : e 0 + e 1 = 12) (hf : f 0 + f 1 = 12) :
    Tb (B6 (monomial e 1) (monomial f 1)) =
      (sixthCoeff (e 1) (f 1) : ℂ) • wv 6 (e 1 + f 1 - 6) := by
  rw [B6_monomial, map_smul]
  by_cases h1 : e 1 + f 1 < 6
  · rw [sixthCoeff_support _ _ (by omega) (by omega) (Or.inl h1), Rat.cast_zero, zero_smul,
    zero_smul]
  by_cases h2 : 18 < e 1 + f 1
  · rw [sixthCoeff_support _ _ (by omega) (by omega) (Or.inr h2), Rat.cast_zero, zero_smul,
    zero_smul]
  rw [Tb_xy _ _ 6 (by omega)]

/-- **The sixth channel on binary forms**: `Tb(P)₍₃₅₎Tb(Q) ≡ K Tb(B6 P Q)`. -/
theorem sixth_bin {P Q : P2} (hP : P ∈ binDeg 12) (hQ : Q ∈ binDeg 12) :
    V2v.smul (Tb P) 35 (Tb Q) - (-33604986844 / 21 : ℂ) • Tb (B6 P Q) ∈ lowerDesc V2v 36 := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    induction hQ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      simp only [Set.mem_setOf_eq] at he hf
      rw [Tb_B6_monomial he hf, Tb_monomial, Tb_monomial, one_smul, one_smul,
        tbm_of_deg (n := 6) (by omega), tbm_of_deg (n := 6) (by omega), smul_smul]
      exact sixth_wv_all (e 1) (f 1) (by omega) (by omega)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, PreVertexAlgebra.smul_add_right, map_add, map_add, smul_add]
      convert Submodule.add_mem _ hy hz using 1; abel
    | smul c y _ hy =>
      rw [map_smul, PreVertexAlgebra.smul_smul_right, map_smul, map_smul, smul_comm, ← smul_sub]
      exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, PreVertexAlgebra.smul_add_left, map_add, LinearMap.add_apply, map_add, smul_add]
    convert Submodule.add_mem _ hx hy using 1; abel
  | smul c x _ hx =>
    rw [map_smul, PreVertexAlgebra.smul_smul_left, map_smul, LinearMap.smul_apply, map_smul,
      smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ _ hx

theorem B6_xy (a b c d : ℕ) :
    B6 (X 0 ^ a * X 1 ^ b) (X 0 ^ c * X 1 ^ d) =
      (sixthCoeff b d : ℂ) • (X 0 ^ (18 - (b + d)) * X 1 ^ (b + d - 6)) := by
  simp only [X_pow_eq_monomial, monomial_mul, mul_one, B6_monomial,
    Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠
      0),
    zero_add]

set_option maxHeartbeats 2000000 in
-- Compute the finite bilinear form and reduce the golden-ratio coefficients.
set_option maxRecDepth 4096 in
theorem B6_fpoly : B6 fpoly fpoly = (OrbIcoS.sixthScalar / 479001600) • fpoly := by
  simp only [fpoly_eq, ← MvPolynomial.smul_eq_C_mul, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, B6_xy]
  norm_num [sixthCoeff, sixthRow0, sixthRow2, sixthRow4, sixthRow6,
    sixthRow8, sixthRow10, sixthRow12, List.getD]
  apply MvPolynomial.funext
  intro x
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_mul, map_pow, eval_C, eval_X, map_neg]
  simp only [OrbIcoS.sixthScalar, f0, f2, f4, f6]
  ring_nf
  simp only [gp_sq']
  ring

/-- The sixth-channel coupling of the actual icosahedral binary form. -/
theorem sixth_ico : V2v.smul (Tb fpoly) 35 (Tb fpoly) -
    (mu6 * OrbIcoS.sixthScalar) • Tb fpoly ∈ lowerDesc V2v 36 := by
  have h := sixth_bin fpoly_mem fpoly_mem
  rw [B6_fpoly, map_smul, smul_smul] at h
  have he : (-33604986844 / 21 : ℂ) * (OrbIcoS.sixthScalar / 479001600) =
      mu6 * OrbIcoS.sixthScalar := by
    rw [← mu6_base]
    ring
  rwa [he] at h

end VOA.Classification.COne.OrbIcoT
