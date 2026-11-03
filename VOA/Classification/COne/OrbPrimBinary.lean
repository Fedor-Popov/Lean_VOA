import VOA.Classification.COne.OrbPrimTop
import VOA.Classification.COne.OrbPrimMain

/-! # OrbPrim: the polynomial model `T₂` of the primaries of `V₂`, constructed

* `Tb : ℂ[x,y] → V₂`, `x^{2n-k} y^k ↦ w_{n,k}` (binary forms of degree `2n` ↦ `Prim_{n²}`).
* `psi : ℂ[X₀,X₁,X₂] → ℂ[x,y]`, `X₀ ↦ x² - y²`, `X₁ ↦ i(x² + y²)`, `X₂ ↦ -2ε xy` (the `sl₂`
  identification `Sym(V₁) → ⊕ Sym^{2n}(ℂ²)`; it kills `r² = X₀² + X₁² + X₂²`).
* `T2 = Tb ∘ psi`.

Proved for `T2` (fields of `V2TModel`): `vac`, `grad`, `primVal`, `rank`, `top` (from the Cartan
product `top_wv`), `r2`. What remains is the equivariance under `A₄` and the second channel
`six` (`T2Residual`).

`tetraPrimaryReduction_of_T2Residual`, `tetra_c2Cofinite_of_T2Residual`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbPrim
open VOA VertexOperatorAlgebra OrbSpan VOA.LatGen VOA.LatGen.Triplet HeisenbergN
  OrbRat6 VOA.IntegralLattice MvPolynomial OrbC2b OrbC2c OrbC2Fix

/-- `ℂ[x, y]`. -/
abbrev P2 := MvPolynomial (Fin 2) ℂ

/-- The image of a binary monomial. -/
def tbm (e : Fin 2 →₀ ℕ) : Sp :=
  if (e 0 + e 1) % 2 = 0 then wv ((e 0 + e 1) / 2) (e 1) else 0

/-- `Tb : ℂ[x,y] → V₂`. -/
def Tb : P2 →ₗ[ℂ] Sp := (basisMonomials (Fin 2) ℂ).constr ℂ tbm

theorem Tb_monomial (e : Fin 2 →₀ ℕ) (c : ℂ) : Tb (monomial e c) = c • tbm e := by
  have h : monomial e c = c • (basisMonomials (Fin 2) ℂ e) := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Tb, (basisMonomials (Fin 2) ℂ).constr_basis]

theorem deg2 (e : Fin 2 →₀ ℕ) : e.degree = e 0 + e 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem tbm_of_deg {e : Fin 2 →₀ ℕ} {n : ℕ} (h : e 0 + e 1 = 2 * n) : tbm e = wv n (e 1) := by
  rw [tbm, if_pos (by omega), h, Nat.mul_div_cancel_left _ (by norm_num)]

/-- Binary forms of degree `d`. -/
def binDeg (d : ℕ) : Submodule ℂ P2 :=
  Submodule.span ℂ ((fun e => monomial e (1 : ℂ)) '' {e : Fin 2 →₀ ℕ | e 0 + e 1 = d})

theorem mem_binDeg_of_hom {P : P2} {d : ℕ} (hP : P.IsHomogeneous d) : P ∈ binDeg d := by
  rw [P.as_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  have hd : e 0 + e 1 = d := by
    by_contra hne
    exact (mem_support_iff.mp he) (hP.coeff_eq_zero (by rw [deg2]; exact hne))
  rw [show monomial e (coeff e P) = coeff e P • monomial e (1 : ℂ) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, hd, rfl⟩)

theorem Tb_prim_of_binDeg {n : ℕ} {P : P2} (hP : P ∈ binDeg (2 * n)) :
    Tb P ∈ prim V2v ((n : ℤ) ^ 2) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    rw [Tb_monomial, one_smul, tbm_of_deg he]
    exact wv_prim n _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem binDeg_mul {a b : ℕ} {P Q : P2} (hP : P ∈ binDeg a) (hQ : Q ∈ binDeg b) :
    P * Q ∈ binDeg (a + b) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    induction hQ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      simp only [Set.mem_setOf_eq] at he hf
      rw [monomial_mul, one_mul]
      exact Submodule.subset_span ⟨e + f, by
        show (e + f) 0 + (e + f) 1 = a + b
        simp only [Finsupp.add_apply]; omega, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

/-- **The top channel on binary forms**: `Tb(P)₍₋₂ₛₘ₋₁₎Tb(Q) ≡ ε Tb(PQ)`. -/
theorem top_bin (s m : ℕ) {P Q : P2} (hP : P ∈ binDeg (2 * s)) (hQ : Q ∈ binDeg (2 * m)) :
    V2v.smul (Tb P) (topIdx s m) (Tb Q) - topSign s m • Tb (P * Q) ∈
      lowerDesc V2v (((s + m : ℕ) : ℤ) ^ 2) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    induction hQ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      simp only [Set.mem_setOf_eq] at he hf
      rw [monomial_mul, one_mul, Tb_monomial, Tb_monomial, Tb_monomial, one_smul, one_smul,
        one_smul, tbm_of_deg he, tbm_of_deg hf,
        tbm_of_deg (show (e + f) 0 + (e + f) 1 = 2 * (s + m) by
          simp only [Finsupp.add_apply]; omega)]
      have := top_wv s m _ (e 1) (f 1) rfl (by omega) (by omega)
      simpa only [Finsupp.add_apply] using this
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, PreVertexAlgebra.smul_add_right, mul_add, map_add, smul_add]
      convert Submodule.add_mem _ hy hz using 1; abel
    | smul c y _ hy =>
      rw [map_smul, PreVertexAlgebra.smul_smul_right, mul_smul_comm, map_smul, smul_comm, ← smul_sub]
      exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, PreVertexAlgebra.smul_add_left, add_mul, map_add, smul_add]
    convert Submodule.add_mem _ hx hy using 1; abel
  | smul c x _ hx =>
    rw [map_smul, PreVertexAlgebra.smul_smul_left, smul_mul_assoc, map_smul, smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ _ hx

/-! ## The ternary model -/

/-- `X₀ ↦ x² - y²`, `X₁ ↦ i(x² + y²)`, `X₂ ↦ -2ε xy`. -/
def psi : P3 →ₐ[ℂ] P2 :=
  aeval ![X 0 ^ 2 - X 1 ^ 2, MvPolynomial.C Complex.I * (X 0 ^ 2 + X 1 ^ 2), MvPolynomial.C (-2 * eps1) * (X 0 * X 1)]

/-- The polynomial model of the primaries of `V₂`. -/
def T2 : P3 →ₗ[ℂ] Sp := Tb ∘ₗ psi.toLinearMap

theorem T2_apply (F : P3) : T2 F = Tb (psi F) := rfl

theorem psi_gen_hom (i : Fin 3) :
    (![X 0 ^ 2 - X 1 ^ 2, MvPolynomial.C Complex.I * (X 0 ^ 2 + X 1 ^ 2),
      MvPolynomial.C (-2 * eps1) * (X 0 * X 1)] i : P2).IsHomogeneous 2 := by
  fin_cases i
  · exact (isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _)
  · simpa using ((isHomogeneous_X_pow (R := ℂ) (0 : Fin 2) 2).add
      (isHomogeneous_X_pow _ _)).C_mul Complex.I
  · simpa using ((isHomogeneous_X ℂ (0 : Fin 2)).mul (isHomogeneous_X ℂ (1 : Fin 2))).C_mul
      (-2 * eps1)

theorem psi_hom {F : P3} {n : ℕ} (hF : F.IsHomogeneous n) : (psi F).IsHomogeneous (2 * n) :=
  hF.aeval _ psi_gen_hom

theorem T2_prim {F : P3} {n : ℕ} (hF : F.IsHomogeneous n) : T2 F ∈ prim V2v ((n : ℤ) ^ 2) :=
  Tb_prim_of_binDeg (mem_binDeg_of_hom (psi_hom hF))

theorem psi_r2 : psi r2 = 0 := by
  have h : psi r2 = MvPolynomial.C (4 * eps1 * eps1 - 4) * (X 0 ^ 2 * X 1 ^ 2) := by
    simp only [r2, psi, map_add, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [map_sub, map_mul, map_neg, map_ofNat]
    have hI : (MvPolynomial.C Complex.I : P2) ^ 2 = -1 := by rw [← C_pow, Complex.I_sq, map_neg, map_one]
    linear_combination (X 0 ^ 2 + X 1 ^ 2) ^ 2 * hI
  rw [h, eps1_sq', sub_self, map_zero, zero_mul]
where eps1_sq' : 4 * eps1 * eps1 = 4 := by rw [mul_assoc, eps1_sq, mul_one]

theorem topSign_ne_zero (s m : ℕ) : topSign s m ≠ 0 := by
  intro h
  have := latticeCocycle_sq (latP 1) (s : ℤ) (m : ℤ)
  rw [← topSign, h, zero_mul] at this
  exact zero_ne_one this

/-! ## The fields of `V2TModel` for `T2` -/

theorem T2_vac : T2 1 = V2v.vacuum := by
  rw [T2_apply, map_one, ← C_1, ← monomial_zero', Tb_monomial, one_smul,
    tbm_of_deg (n := 0) (by simp), show (0 : Fin 2 →₀ ℕ) 1 = 0 from rfl, wv_zero]
  rfl

theorem T2_grad {F : P3} {n : ℕ} (hF : F.IsHomogeneous n) :
    T2 F ∈ V2v.grading ((n : ℤ) ^ 2) := ((mem_prim V2v).mp (T2_prim hF)).1

theorem T2_top (G H : P3) (s m : ℕ) (hG : G.IsHomogeneous s) (hH : H.IsHomogeneous m) :
    ∃ c : ℂ, T2 (G * H) - c • V2v.smul (T2 G) (-((2 * s * m : ℕ) : ℤ) - 1) (T2 H) ∈
      lowerDesc V2v (((s + m : ℕ) : ℤ) ^ 2) := by
  refine ⟨(topSign s m)⁻¹, ?_⟩
  have h := top_bin s m (mem_binDeg_of_hom (psi_hom hG)) (mem_binDeg_of_hom (psi_hom hH))
  have key : T2 (G * H) - (topSign s m)⁻¹ • V2v.smul (T2 G) (-((2 * s * m : ℕ) : ℤ) - 1) (T2 H) =
      (-(topSign s m)⁻¹) • (V2v.smul (Tb (psi G)) (topIdx s m) (Tb (psi H)) -
        topSign s m • Tb (psi G * psi H)) := by
    rw [T2_apply, T2_apply, T2_apply, map_mul, topIdx, smul_sub, smul_smul,
      neg_mul, inv_mul_cancel₀ (topSign_ne_zero s m), neg_smul, neg_smul, one_smul]
    abel
  rw [key]
  exact Submodule.smul_mem _ _ h

theorem T2_r2 : T2 r2 ∈ lowerDesc V2v 4 := by
  rw [T2_apply, psi_r2, map_zero]; exact Submodule.zero_mem _

/-- Preimages of the binary monomials: `u ↦ x²`, `v ↦ y²`, `w ↦ xy`. -/
def uP : P3 := MvPolynomial.C (1 / 2 : ℂ) * (X 0 - MvPolynomial.C Complex.I * X 1)
def vP : P3 := MvPolynomial.C (1 / 2 : ℂ) * (-X 0 - MvPolynomial.C Complex.I * X 1)
def wP : P3 := MvPolynomial.C (-(1 / 2 : ℂ) * eps1) * X 2

theorem C_I_sq : (MvPolynomial.C Complex.I : P2) * MvPolynomial.C Complex.I = -1 := by
  rw [← C_mul, Complex.I_mul_I, map_neg, map_one]

theorem C_half_two : (MvPolynomial.C (1 / 2 : ℂ) : P2) * 2 = 1 := by
  rw [show (2 : P2) = MvPolynomial.C 2 from (map_ofNat MvPolynomial.C 2).symm, ← C_mul]
  norm_num

theorem psi_uP : psi uP = X 0 ^ 2 := by
  have h : psi uP = MvPolynomial.C (1 / 2 : ℂ) * ((X 0 ^ 2 - X 1 ^ 2) -
      MvPolynomial.C Complex.I * (MvPolynomial.C Complex.I * (X 0 ^ 2 + X 1 ^ 2))) := by
    simp only [uP, psi, map_mul, map_sub, algHom_C, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, algebraMap_eq]
  rw [h]
  linear_combination (-(MvPolynomial.C (1 / 2 : ℂ)) * (X 0 ^ 2 + X 1 ^ 2)) * C_I_sq +
    X 0 ^ 2 * C_half_two

theorem psi_vP : psi vP = X 1 ^ 2 := by
  have h : psi vP = MvPolynomial.C (1 / 2 : ℂ) * (-(X 0 ^ 2 - X 1 ^ 2) -
      MvPolynomial.C Complex.I * (MvPolynomial.C Complex.I * (X 0 ^ 2 + X 1 ^ 2))) := by
    simp only [vP, psi, map_mul, map_sub, map_neg, algHom_C, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, algebraMap_eq]
  rw [h]
  linear_combination (-(MvPolynomial.C (1 / 2 : ℂ)) * (X 0 ^ 2 + X 1 ^ 2)) * C_I_sq +
    X 1 ^ 2 * C_half_two

theorem psi_wP : psi wP = X 0 * X 1 := by
  have h : psi wP = MvPolynomial.C (-(1 / 2 : ℂ) * eps1) *
      (MvPolynomial.C (-2 * eps1) * (X 0 * X 1)) := by
    have h2 : psi (X 2) = MvPolynomial.C (-2 * eps1) * (X 0 * X 1) := by
      rw [psi, aeval_X]; rfl
    rw [wP, map_mul, algHom_C, algebraMap_eq, h2]
  rw [h, ← mul_assoc, ← C_mul, show -(1 / 2 : ℂ) * eps1 * (-2 * eps1) = eps1 * eps1 by ring,
    eps1_sq, C_1, one_mul]

theorem uP_hom : uP.IsHomogeneous 1 := by
  unfold uP
  simpa using ((isHomogeneous_X ℂ (0 : Fin 3)).sub
    ((isHomogeneous_X ℂ (1 : Fin 3)).C_mul Complex.I)).C_mul (1 / 2 : ℂ)

theorem vP_hom : vP.IsHomogeneous 1 := by
  unfold vP
  simpa using ((isHomogeneous_X ℂ (0 : Fin 3)).neg.sub
    ((isHomogeneous_X ℂ (1 : Fin 3)).C_mul Complex.I)).C_mul (1 / 2 : ℂ)

theorem wP_hom : wP.IsHomogeneous 1 := by
  unfold wP
  simpa using (isHomogeneous_X ℂ (2 : Fin 3)).C_mul (-(1 / 2 : ℂ) * eps1)

theorem binMono_eq (a b : ℕ) :
    (X 0 ^ a * X 1 ^ b : P2) = monomial (Finsupp.single 0 a + Finsupp.single 1 b) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]

theorem wv_mem_span_T2 (n k : ℕ) (hk : k ≤ 2 * n) :
    wv n k ∈ Submodule.span ℂ (T2 '' {F | F.IsHomogeneous n}) := by
  rcases Nat.even_or_odd k with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · -- `x^{2n-2b} y^{2b} = ψ(u^{n-b} v^b)`
    refine Submodule.subset_span ⟨uP ^ (n - b) * vP ^ b, ?_, ?_⟩
    · have := (uP_hom.pow (n - b)).mul (vP_hom.pow b)
      simp only [one_mul] at this
      rwa [show n - b + b = n by omega] at this
    · have hp : psi (uP ^ (n - b) * vP ^ b) = X 0 ^ (2 * (n - b)) * X 1 ^ (2 * b) := by
        rw [map_mul, map_pow, map_pow, psi_uP, psi_vP, ← pow_mul, ← pow_mul]
      rw [T2_apply, hp, binMono_eq, Tb_monomial, one_smul, tbm_of_deg (n := n) (by simp; omega)]
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      norm_num
      congr 1; omega
  · refine Submodule.subset_span ⟨uP ^ (n - b - 1) * vP ^ b * wP, ?_, ?_⟩
    · have := ((uP_hom.pow (n - b - 1)).mul (vP_hom.pow b)).mul wP_hom
      simp only [one_mul] at this
      rwa [show n - b - 1 + b + 1 = n by omega] at this
    · have hp : psi (uP ^ (n - b - 1) * vP ^ b * wP) =
          X 0 ^ (2 * (n - b - 1) + 1) * X 1 ^ (2 * b + 1) := by
        rw [map_mul, map_mul, map_pow, map_pow, psi_uP, psi_vP, psi_wP]; ring
      rw [T2_apply, hp, binMono_eq, Tb_monomial, one_smul, tbm_of_deg (n := n) (by simp; omega)]
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      norm_num

theorem cnk_ne_zero (n k : ℕ) : cnk n k ≠ 0 :=
  div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _) (by exact_mod_cast Nat.factorial_ne_zero _)

theorem T2_rank (n : ℕ) : 2 * n + 1 ≤
    Module.finrank ℂ (Submodule.span ℂ (T2 '' {F | F.IsHomogeneous n})) := by
  have hle : Submodule.span ℂ (T2 '' {F | F.IsHomogeneous n}) ≤ V2v.grading ((n : ℤ) ^ 2) :=
    Submodule.span_le.mpr (by rintro _ ⟨F, hF, rfl⟩; exact T2_grad hF)
  haveI : FiniteDimensional ℂ (V2v.grading ((n : ℤ) ^ 2)) := V2v.finrank _
  haveI := Submodule.finiteDimensional_of_le hle
  have hli : LinearIndependent ℂ (fun k : Fin (2 * n + 1) => wv n k) := by
    have := (vn_linearIndependent n).units_smul (fun k => Units.mk0 (cnk n k) (cnk_ne_zero n k))
    convert this using 1
  have hsp : Submodule.span ℂ (Set.range fun k : Fin (2 * n + 1) => wv n k) ≤
      Submodule.span ℂ (T2 '' {F | F.IsHomogeneous n}) :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact wv_mem_span_T2 n k (by omega))
  have := Submodule.finrank_mono hsp
  rwa [finrank_span_eq_card hli, Fintype.card_fin] at this

/-! ## The residual and the headline -/

/-- What remains of B2 for the constructed model `T2`: `A₄`-equivariance and the second channel. -/
structure T2Residual (φ : tetra →* (P3 ≃ₐ[ℂ] P3)) : Prop where
  eqv : ∀ (g : tetra) (F : P3), (g : Aut (V2m 1 le_rfl)) (T2 F) = T2 (φ g F)
  fix : ∀ (g : tetra) (F : P3), IsA4Inv F → φ g F = F
  gen1 : ∃ g : tetra, ∀ F, φ g F = s1 F
  gen2 : ∃ g : tetra, ∀ F, φ g F = s2 F
  gen3 : ∃ g : tetra, ∀ F, φ g F = rename cyc F
  hom : ∀ (g : tetra) (F : P3) (n : ℕ), F.IsHomogeneous n → (φ g F).IsHomogeneous n
  six : ∃ c d : ℂ, c ≠ 0 ∧ (V2m 1 le_rfl).smul (T2 I4) (-12) (T2 I3) - c • T2 I6 -
    d • T2 (I3 * I3) ∈ lowerDesc (V2m 1 le_rfl) 36

theorem v2TModel_of_T2Residual {φ : tetra →* (P3 ≃ₐ[ℂ] P3)} (h : T2Residual φ) :
    V2TModel tetra T2 φ where
  eqv := h.eqv
  fix := h.fix
  gen1 := h.gen1
  gen2 := h.gen2
  gen3 := h.gen3
  hom := h.hom
  vac := T2_vac
  grad := fun _ _ hF => T2_grad hF
  primVal := fun _ _ _ hF => T2_prim hF
  rank := T2_rank
  top := fun G H s m hG hH _ _ => T2_top G H s m hG hH
  r2 := T2_r2
  six := h.six

/-- **B2 primary reduction from the residual of the constructed model.** -/
theorem tetraPrimaryReduction_of_T2Residual {φ : tetra →* (P3 ≃ₐ[ℂ] P3)}
    (h : T2Residual φ) : TetraPrimaryReduction :=
  tetraPrimaryReduction_of_v2TModel (v2TModel_of_T2Residual h)

/-- `C₂` for `V₂^{A₄}` from the residual and the corrected Dong--Jiang relations. -/
theorem tetra_c2Cofinite_of_T2Residual {φ : tetra →* (P3 ≃ₐ[ℂ] P3)} (h : T2Residual φ)
    (hr : TetrahedralDongJiangRelationsCorrected) : C2Cofinite (orbifoldVOA tetra) :=
  tetra_c2Cofinite_of_v2TModel (v2TModel_of_T2Residual h) hr

end VOA.Classification.COne.OrbPrim
