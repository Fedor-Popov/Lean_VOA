/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Lagrangian.lean
  CFSG/Monster/Code/Loop.lean
  CFSG/Monster/Spin/Pairing.lean
  CFSG/Monster/Spin/SignedPerm.lean
  CFSG/Monster/Spin/Defs.lean
  CFSG/Monster/Spin/Coords.lean
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.MinimalVectors
import VOA.Moonshine.MonsterGriess.SpinMatrixLaws
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.FieldTheory.Finiteness

/-!
# Axiom's Monster port (parity-centralizer closure): the Parker loop and the group `Q ⊂ GL₄₀₉₆(ℚ)`

* `Parker` — the Parker loop `C × ZMod 2` with product `(a, s)(b, t) = (a + b, s + t + θ a b)`;
* the signed permutation matrices `XmatR e` (`e : Parker`), `DmatR δ` (`δ : Cocode`), `TmatR a`
  on `SpinIdx = ZMod 2 × C₀`, their rational versions `Xmat`, `Dmat`, `Tmat`, `zmat = -1`, and
  the units `XU e`, `DU δ`;
* ⭐ `Q : Subgroup (GL SpinIdx ℚ)` — Axiom's extraspecial group `2^{1+24}`, the subgroup generated
  by all `XU e` and `DU δ`;
* `XmatR_eq_qmatR`, `DmatR_eq_qmatR`, `TmatR_eq_qmatR`, `neg_one_eq_qmatR` — every generator is a
  spin matrix `qmatR R s a δ`; `qmatR_injective` (over a ring with `2 ≠ 0`);
* `θ_ΩC_left`, `θ_ΩC_right`, `θ_π₀`, `π₀_ΩC`, cardinalities `card_C`, `card_C₀`, `card_cocode`,
  `card_spinIdx`, the trace and injectivity of signed permutation matrices.

## Port notes
* Namespaces `CFSG.Monster`, `CFSG.Monster.Code`, `CFSG.Monster.Spin` ↦
  `VOA.Moonshine.MonsterGriess`, `….Code`, `….Spin`.  Module-system syntax dropped; the source's
  `public noncomputable section` of `Spin/Defs.lean`/`Spin/Coords.lean` becomes the named
  `noncomputable section SpinGroup`.  Bodies verbatim.
* Already ported and used, not repeated: `sgn`, `sgnR`, `spm`, `spm_apply`, `spm_congr`,
  `spm_transpose_mul_self`, `spm_mul_transpose_self`, `qmatR` and its product laws
  (`Spin.lean`, `SpinMatrixLaws.lean`), `θ`, `θ_add_θ_swap`, `pair_*` (`CodeCocycle.lean`),
  `θ_Ω` (`MinimalVectors.lean`).
* Omitted (not reached from the target): the Moufang identities and the loop constants
  `negOne`, `omega`, `negOmega`, `mul_def`, `one_def` of `Parker`; the Lagrangian/Fourier lemmas
  of `Lagrangian.lean` other than `sgn_add`, `sgn_zero`; the `Parker`-presentation identities of
  `Spin/Coords.lean` beyond the `…_eq_qmatR` dictionary.
* Drift: `spm_injective` — the source's `ite_eq_left h`/`ite_eq_right h` (absent in Mathlib v4.30)
  ↦ `if_pos h`/`if_neg h`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/Lagrangian.lean` -/

theorem sgn_add (s t : ZMod 2) : sgn (s + t) = sgn s * sgn t := by
  fin_cases s <;> fin_cases t <;> simp [sgn] <;> decide

theorem sgn_zero : sgn 0 = 1 := rfl

end VOA.Moonshine.MonsterGriess

namespace VOA.Moonshine.MonsterGriess.Code

/-! ### From `CFSG/Monster/Code/Loop.lean` -/

@[ext] structure Parker where
  code : C
  sign : ZMod 2

namespace Parker

def equivProd : Parker ≃ C × ZMod 2 where
  toFun x := (x.code, x.sign)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Finite Parker := Finite.of_equiv _ equivProd.symm

noncomputable instance : Mul Parker :=
  ⟨fun x y => ⟨x.code + y.code, x.sign + y.sign + θ x.code y.code⟩⟩

instance : One Parker := ⟨⟨0, 0⟩⟩

@[simp] theorem mul_code (x y : Parker) : (x * y).code = x.code + y.code := rfl

@[simp] theorem mul_sign (x y : Parker) : (x * y).sign = x.sign + y.sign + θ x.code y.code := rfl

@[simp] theorem one_code : (1 : Parker).code = 0 := rfl

@[simp] theorem one_sign : (1 : Parker).sign = 0 := rfl

end Parker

end VOA.Moonshine.MonsterGriess.Code

namespace VOA.Moonshine.MonsterGriess.Spin

open VOA.Moonshine.MonsterGriess.Code

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

/-! ### From `CFSG/Monster/Spin/Pairing.lean` -/

@[simp] theorem π₀_ΩC : π₀ ΩC = 0 := by
  apply Subtype.ext
  rw [coe_π₀, μ₀_ΩC, one_smul, add_self_C]
  rfl

theorem π₀_add_μ₀ (u : C) : (π₀ u : C) + μ₀ u • ΩC = u := by
  rw [coe_π₀, add_assoc, ← two_smul (ZMod 2), smul_smul, two_eq_zero', zero_mul, zero_smul,
    add_zero]

theorem eq_of_π₀_μ₀ {u v : C} (h₁ : π₀ u = π₀ v) (h₂ : μ₀ u = μ₀ v) : u = v := by
  rw [← π₀_add_μ₀ u, ← π₀_add_μ₀ v, h₁, h₂]

def splitC : C ≃ₗ[ZMod 2] C₀ × ZMod 2 where
  toFun u := (π₀ u, μ₀ u)
  invFun p := (p.1 : C) + p.2 • ΩC
  map_add' u v := by simp only [map_add, Prod.mk_add_mk]
  map_smul' c u := by simp only [map_smul, RingHom.id_apply, Prod.smul_mk]
  left_inv u := π₀_add_μ₀ u
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp only [map_add, map_smul, π₀_coe, π₀_ΩC, smul_zero, add_zero]
    · simp only [map_add, map_smul, μ₀_coe, μ₀_ΩC, smul_eq_mul, mul_one, zero_add]

theorem natCard_C : Nat.card C = 2 ^ 12 := by
  rw [Nat.card_congr basisC.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem natCard_C₀ : Nat.card C₀ = 2 ^ 11 := by
  have h := natCard_C
  rw [Nat.card_congr splitC.toEquiv, Nat.card_prod, Nat.card_zmod] at h
  omega

theorem card_C : Fintype.card C = 4096 := by
  rw [Fintype.card_eq_nat_card, natCard_C]; rfl

theorem card_C₀ : Fintype.card C₀ = 2048 := by
  rw [Fintype.card_eq_nat_card, natCard_C₀]; rfl

noncomputable instance : DecidableEq Cocode := Classical.decEq _

theorem natCard_cocode : Nat.card Cocode = 2 ^ 12 := by
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), finrank_cocode,
    ZMod.card]

theorem card_cocode : Fintype.card Cocode = 4096 := by
  rw [Fintype.card_eq_nat_card, natCard_cocode]; rfl

theorem pair_ΩC_mk_single : pair ΩC (Submodule.Quotient.mk (Pi.single 0 1)) = 1 := by
  rw [pair_mk, dotProduct_single, mul_one]
  rfl

private theorem K_Ω (a : C) : K a Ω = 0 := by
  have h : (a : Fin 24 → ZMod 2) * Ω = a := by
    funext i; simp [Ω]
  rw [K_eq, h]
  obtain ⟨m, hm⟩ := four_dvd_wt a.2
  rw [hm, show 4 * m / 2 = 2 * m by omega, Nat.cast_mul, Nat.cast_ofNat, two_eq_zero', zero_mul]

@[simp] theorem θ_ΩC_left (u : C) : θ ΩC u = 0 := θ_Ω u

@[simp] theorem θ_ΩC_right (a : C) : θ a ΩC = 0 := by
  have h := θ_add_θ_swap a ΩC
  rw [θ_ΩC_left, add_zero, coe_ΩC, K_Ω] at h
  exact h

theorem P_Ω : P Ω = 0 := by decide

@[simp] theorem θ_π₀ (a u : C) : θ a (π₀ u) = θ a u := by
  rw [coe_π₀, θ_add_right, θ_smul_right, θ_ΩC_right, mul_zero, add_zero]

@[simp] theorem pair_ΩC_thetaD (a : C) : pair ΩC (thetaD a) = 0 := by
  rw [pair_thetaD, θ_ΩC_right]

@[simp] theorem pair_ΩC_Acocode (a b : C) : pair ΩC (Acocode a b) = 0 := by
  rw [pair_Acocode, A_comm₂₃, A_comm₁₂]
  calc A Ω a b = ∑ i, (a : Fin 24 → ZMod 2) i * (b : Fin 24 → ZMod 2) i := by
        rw [A_eq_sum]
        exact Finset.sum_congr rfl fun i _ => by simp [Ω]
    _ = (a : Fin 24 → ZMod 2) ⬝ᵥ b := rfl
    _ = 0 := dotProduct_eq_zero a.2 b.2

/-! ### From `CFSG/Monster/Spin/SignedPerm.lean` -/

section SignedPermExtra

open Matrix

variable {R : Type*} [CommRing R]

theorem sgnR_ne_zero [Nontrivial R] (t : ZMod 2) : sgnR R t ≠ 0 := by
  intro h
  have := sgnR_mul_self (R := R) t
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem sgnR_injective (h2 : (2 : R) ≠ 0) : Function.Injective (sgnR R) := by
  have h : (1 : R) ≠ -1 := by
    intro h
    apply h2
    calc (2 : R) = 1 + 1 := one_add_one_eq_two.symm
      _ = -1 + 1 := by rw [← h]
      _ = 0 := neg_add_cancel 1
  intro s t hst
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
  · rfl
  · exact absurd hst h
  · exact absurd hst.symm h
  · rfl

theorem sgnR_add_one (t : ZMod 2) : sgnR R (t + 1) = -sgnR R t := by
  rw [sgnR_add, sgnR_one, mul_neg_one]

theorem sum_sgnR_add (c : ZMod 2) : ∑ t : ZMod 2, sgnR R (t + c) = 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide),
    zero_add, add_comm (1 : ZMod 2) c, sgnR_add_one, add_neg_cancel]

variable {ι : Type*} [DecidableEq ι]

theorem spm_apply_mem (σ : ι → ι) (ε : ι → ZMod 2) (i j : ι) :
    spm R σ ε i j = 0 ∨ spm R σ ε i j = 1 ∨ spm R σ ε i j = -1 := by
  rw [spm_apply]
  split_ifs
  · rcases zmod2_cases (ε i) with h | h <;> rw [h] <;> simp
  · exact Or.inl rfl

theorem spm_injective [Nontrivial R] (h2 : (2 : R) ≠ 0) {σ σ' : ι → ι} {ε ε' : ι → ZMod 2}
    (h : spm R σ ε = spm R σ' ε') : σ = σ' ∧ ε = ε' := by
  have hσ : ∀ i, σ i = σ' i := by
    intro i
    have := congrFun (congrFun h i) (σ i)
    rw [spm_apply, spm_apply, if_pos rfl] at this
    by_contra hne
    rw [if_neg hne] at this
    exact sgnR_ne_zero _ this
  refine ⟨funext hσ, funext fun i => ?_⟩
  have := congrFun (congrFun h i) (σ i)
  rw [spm_apply, spm_apply, if_pos rfl, if_pos (hσ i)] at this
  exact sgnR_injective h2 this

variable [Fintype ι]

theorem trace_spm (σ : ι → ι) (ε : ι → ZMod 2) :
    trace (spm R σ ε) = ∑ i, if σ i = i then sgnR R (ε i) else 0 := by
  simp only [trace, diag_apply, spm_apply, eq_comm]

end SignedPermExtra

/-! ### From `CFSG/Monster/Spin/Defs.lean` -/

noncomputable section SpinGroup

open Matrix

theorem card_spinIdx : Fintype.card SpinIdx = 4096 := by
  rw [Fintype.card_eq_nat_card, Nat.card_prod, Nat.card_zmod, natCard_C₀]
  rfl

def E (η : ZMod 2) (c : C₀) : SpinIdx → ℚ := Pi.single (η, c) 1

theorem E_dotProduct_E (η η' : ZMod 2) (c c' : C₀) :
    E η c ⬝ᵥ E η' c' = if (η, c) = (η', c') then 1 else 0 := by
  rw [E, E, single_dotProduct, one_mul, Pi.single_apply]

theorem add_self_C' (a : C) : a + a = 0 := add_self_C a

theorem shift_eq_self_iff (a : C) (c : C₀) : shift a c = c ↔ π₀ a = 0 := by
  rw [shift, map_add, π₀_coe, add_eq_left]

theorem θ_shift (b a : C) (c : C₀) : θ b (shift a c) = θ b c + θ b a := by
  rw [coe_shift, θ_add_right, θ_add_right, θ_smul_right, θ_ΩC_right, mul_zero, add_zero]

variable (R : Type*) [CommRing R]

def xPerm (a : C) (i : SpinIdx) : SpinIdx := (i.1, shift a i.2)

def xSign (e : Parker) (i : SpinIdx) : ZMod 2 :=
  e.sign + P e.code + θ e.code i.2 + i.1 * μ₀ e.code

def dPerm (δ : Cocode) (i : SpinIdx) : SpinIdx := (i.1 + pair ΩC δ, i.2)

def dSign (δ : Cocode) (i : SpinIdx) : ZMod 2 := pair i.2 δ

def XmatR (e : Parker) : Matrix SpinIdx SpinIdx R := spm R (xPerm e.code) (xSign e)

def DmatR (δ : Cocode) : Matrix SpinIdx SpinIdx R := spm R (dPerm δ) (dSign δ)

def TmatR (a : C) : Matrix SpinIdx SpinIdx R :=
  XmatR R ⟨a, 0⟩ * DmatR R (thetaD a)

theorem xPerm_involutive (a : C) : Function.Involutive (xPerm a) := fun i => by
  simp only [xPerm, shift_shift]

theorem dPerm_involutive (δ : Cocode) : Function.Involutive (dPerm δ) := fun i => by
  simp only [dPerm, add_assoc, ← two_mul, two_eq_zero', zero_mul, add_zero]

variable {R}

theorem XmatR_transpose_mul_self (e : Parker) : (XmatR R e)ᵀ * XmatR R e = 1 :=
  spm_transpose_mul_self (xPerm_involutive _) _

theorem XmatR_mul_transpose_self (e : Parker) : XmatR R e * (XmatR R e)ᵀ = 1 :=
  spm_mul_transpose_self (xPerm_involutive _) _

theorem DmatR_transpose_mul_self (δ : Cocode) : (DmatR R δ)ᵀ * DmatR R δ = 1 :=
  spm_transpose_mul_self (dPerm_involutive _) _

theorem DmatR_mul_transpose_self (δ : Cocode) : DmatR R δ * (DmatR R δ)ᵀ = 1 :=
  spm_mul_transpose_self (dPerm_involutive _) _

def Xmat (e : Parker) : Matrix SpinIdx SpinIdx ℚ := XmatR ℚ e

def Dmat (δ : Cocode) : Matrix SpinIdx SpinIdx ℚ := DmatR ℚ δ

def zmat : Matrix SpinIdx SpinIdx ℚ := -1

def Tmat (a : C) : Matrix SpinIdx SpinIdx ℚ := Xmat ⟨a, 0⟩ * Dmat (thetaD a)

theorem Xmat_transpose_mul_self (e : Parker) : (Xmat e)ᵀ * Xmat e = 1 :=
  XmatR_transpose_mul_self e

theorem Xmat_mul_transpose_self (e : Parker) : Xmat e * (Xmat e)ᵀ = 1 :=
  XmatR_mul_transpose_self e

theorem Dmat_transpose_mul_self (δ : Cocode) : (Dmat δ)ᵀ * Dmat δ = 1 :=
  DmatR_transpose_mul_self δ

theorem Dmat_mul_transpose_self (δ : Cocode) : Dmat δ * (Dmat δ)ᵀ = 1 :=
  DmatR_mul_transpose_self δ

def XU (e : Parker) : GL SpinIdx ℚ :=
  ⟨Xmat e, (Xmat e)ᵀ, Xmat_mul_transpose_self e, Xmat_transpose_mul_self e⟩

def DU (δ : Cocode) : GL SpinIdx ℚ :=
  ⟨Dmat δ, (Dmat δ)ᵀ, Dmat_mul_transpose_self δ, Dmat_transpose_mul_self δ⟩

@[simp] theorem coe_XU (e : Parker) : (XU e : Matrix SpinIdx SpinIdx ℚ) = Xmat e := rfl

@[simp] theorem coe_DU (δ : Cocode) : (DU δ : Matrix SpinIdx SpinIdx ℚ) = Dmat δ := rfl

/-- ⭐ **Axiom's extraspecial group** `Q = 2^{1+24} ⊂ GL₄₀₉₆(ℚ)`, generated by the `XU e`
(`e` in the Parker loop) and the `DU δ` (`δ` in the cocode). -/
def Q : Subgroup (GL SpinIdx ℚ) := Subgroup.closure (Set.range XU ∪ Set.range DU)

theorem XU_mem_Q (e : Parker) : XU e ∈ Q :=
  Subgroup.subset_closure (Or.inl ⟨e, rfl⟩)

theorem DU_mem_Q (δ : Cocode) : DU δ ∈ Q :=
  Subgroup.subset_closure (Or.inr ⟨δ, rfl⟩)

/-! ### From `CFSG/Monster/Spin/Coords.lean` -/

@[simp] theorem pair_ΩC_zero : pair ΩC 0 = 0 := pair_zero_right _

theorem neg_one_eq_qmatR : (-1 : Matrix SpinIdx SpinIdx R) = qmatR R 1 0 0 := by
  rw [← qmatR_zero, ← neg_one_smul R, ← sgnR_one, sgnR_smul_qmatR, add_zero]

theorem XmatR_eq_qmatR (e : Parker) : XmatR R e = qmatR R e.sign e.code (thetaD e.code) := by
  refine spm_congr (fun i => ?_) (fun i => ?_)
  · simp only [xPerm, qPerm, pair_ΩC_thetaD, add_zero]
  · simp only [xSign, qSign, pair_thetaD, θ_shift, θ_self]
    ring

theorem DmatR_eq_qmatR (δ : Cocode) : DmatR R δ = qmatR R 0 0 δ := by
  refine spm_congr (fun i => ?_) (fun i => ?_)
  · simp only [dPerm, qPerm, shift_zero]
  · simp only [dSign, qSign, shift_zero, map_zero, mul_zero, zero_add]

theorem TmatR_eq_qmatR (a : C) : TmatR R a = qmatR R 0 a 0 := by
  rw [TmatR, XmatR_eq_qmatR, DmatR_eq_qmatR, qmatR_mul, add_self_cocode, pair_zero_left]
  simp only [add_zero]

theorem qmatR_apply_mem (s : ZMod 2) (a : C) (δ : Cocode) (i j : SpinIdx) :
    qmatR R s a δ i j = 0 ∨ qmatR R s a δ i j = 1 ∨ qmatR R s a δ i j = -1 :=
  spm_apply_mem _ _ _ _

theorem qmatR_injective [Nontrivial R] (h2 : (2 : R) ≠ 0) {s t : ZMod 2} {a b : C}
    {δ ε : Cocode} (h : qmatR R s a δ = qmatR R t b ε) : s = t ∧ a = b ∧ δ = ε := by
  obtain ⟨hσ, hε⟩ := spm_injective h2 h
  have hp : ∀ i, qPerm a δ i = qPerm b ε i := fun i => congrFun hσ i
  have hs : ∀ i, qSign s a δ i = qSign t b ε i := fun i => congrFun hε i
  have hΩ : pair ΩC δ = pair ΩC ε := by
    have := congrArg Prod.fst (hp (0, 0))
    simpa [qPerm] using this
  have hπ : π₀ a = π₀ b := by
    have := congrArg Prod.snd (hp (0, 0))
    simpa [qPerm, shift] using this
  have hμ : μ₀ a = μ₀ b := by
    have h0 := hs (0, 0)
    have h1 := hs (1, 0)
    have hsh : shift a 0 = shift b 0 := by simpa [shift] using hπ
    simp only [qSign, zero_mul, add_zero, one_mul, hsh] at h0 h1
    linear_combination h1 - h0
  have hab : a = b := eq_of_π₀_μ₀ hπ hμ
  subst hab
  have hc : ∀ c : C₀, s + pair c δ = t + pair c ε := by
    intro c
    have := hs (0, shift a c)
    simpa [qSign, shift_shift] using this
  have hst : s = t := by simpa using hc 0
  subst hst
  refine ⟨rfl, rfl, ext_pair fun u => ?_⟩
  have hu := π₀_add_μ₀ u
  have h1 : pair (π₀ u) δ = pair (π₀ u) ε := by
    have := hc (π₀ u)
    linear_combination this
  rw [← hu, pair_add_left, pair_add_left, pair_smul_left, pair_smul_left, h1, hΩ]

theorem Xmat_eq_qmatR (e : Parker) : Xmat e = qmatR ℚ e.sign e.code (thetaD e.code) :=
  XmatR_eq_qmatR e

theorem Dmat_eq_qmatR (δ : Cocode) : Dmat δ = qmatR ℚ 0 0 δ := DmatR_eq_qmatR δ

theorem Tmat_eq_qmatR (a : C) : Tmat a = qmatR ℚ 0 a 0 := TmatR_eq_qmatR a

theorem zmat_eq_qmatR : zmat = qmatR ℚ 1 0 0 := neg_one_eq_qmatR

end SpinGroup

end VOA.Moonshine.MonsterGriess.Spin
