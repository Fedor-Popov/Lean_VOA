/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean
v4.35.0-rc3 with the module system), files:
  CFSG/Monster/Code/Cocycle.lean
  CFSG/Monster/Code/Weights.lean
  CFSG/Monster/Code/Basis.lean
  CFSG/Monster/Code/LoopIdentities.lean
  CFSG/Monster/Spin/Pairing.lean
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
import VOA.Moonshine.MonsterGriess.Spin
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Axiom's Monster port: the theta cocycle identities and the cocode pairing

The identities of the Parker-loop cocycle `θ : C × C → ZMod 2` of the Golay code `C` and of the
pairing `pair : C → Cocode →ₗ ZMod 2` that the bundling of Axiom Math's coordinate map
`phi0 : C × Cocode → Λ/2Λ` rests on:

* `θ_add_left` — `θ (d + e) f = θ d f + θ e f + A d e f` (the defect is the triple intersection
  count `A`); `θ_add_θ_swap` — `θ d e + θ e d = K d e`; `θ_self` — `θ d d = P d`;
* `P_add`, `K_add_left` — the weight forms `P` (weight/4) and `K` (overlap/2) under addition;
* `mem_C_iff_forall_dotProduct` — the Golay code is self-dual;
* the pairing: bilinearity, nondegeneracy on both sides (`eq_zero_of_forall_pair`,
  `eq_zero_of_forall_pair_left`), `finrank_cocode`;
* `thetaD_add` — `thetaD (a + b) = thetaD a + thetaD b + Acocode a b`, the cocycle identity behind
  the additivity of `lamT` (`LatticeQuadratic.lean`).

## Port notes
* Namespaces `CFSG.Monster.Code`, `CFSG.Monster.Spin` ↦ `VOA.Moonshine.MonsterGriess.Code`,
  `….Spin`.  Module-system syntax (`module`, `public import`, `public section`, `@[expose]`)
  dropped.
* Bodies verbatim, except: `θc_eq`, `θc_add_right`, `θc_smul_right`, `θ_add_right`,
  `θ_smul_right`, `hammingNorm_add_add`, `lt01`, `Ab` were already ported in `Golay.lean`, and
  `ΩC`, `μ₀`, `C₀`, `π₀`, `Cocode`, `dotL`, `pair`, `pair_mk`, `θL`, `exists_pair_eq`, `thetaD` in
  `Spin.lean`; they are used, not repeated.
* Omitted: the weight enumerators, the hexacode layer, `splitC`, cardinality lemmas, `cocodeDual`,
  and the `Ω`-identities resting on the grey/hexacode decomposition (`θ_Ω`, `θ_ΩC_left`, …), none of
  which is needed here.
-/

namespace VOA.Moonshine.MonsterGriess.Code

open scoped Finset

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

/-! ### From `CFSG/Monster/Code/Basis.lean` -/
theorem finrank_C : Module.finrank (ZMod 2) C = 12 := by
  rw [Module.finrank_eq_card_basis basisC, Fintype.card_fin]

/-! ### From `CFSG/Monster/Code/LoopIdentities.lean` -/
theorem add_self_C (d : C) : d + d = 0 := by
  apply Subtype.ext
  funext i
  simp only [Submodule.coe_add, Pi.add_apply, Submodule.coe_zero, Pi.zero_apply]
  rcases zmod2_cases ((d : Fin 24 → ZMod 2) i) with h | h <;> rw [h] <;> rfl

/-! ### From `CFSG/Monster/Code/Weights.lean` -/
def Umask (k : ℕ) : ℕ :=
  [0xe, 0x1f, 0x10f, 0x100f, 0x1000f, 0x11111, 0xa, 0xc, 0x5f, 0x3f, 0x50f, 0x30f].getD k 0

private theorem B_dot_U : ∀ i k : Fin 12, B i ⬝ᵥ bvec 24 (Umask k) = if i = k then 1 else 0 := by
  intro i k
  rw [B_eq_bvec, bvec_dotProduct]
  revert i k; decide

private noncomputable def dotB : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
  (Matrix.of B).mulVecLin

private theorem dotB_apply (x : Fin 24 → ZMod 2) (i : Fin 12) : dotB x i = B i ⬝ᵥ x := rfl

private theorem dotB_surjective : Function.Surjective dotB := by
  intro c
  refine ⟨∑ k, c k • bvec 24 (Umask k), funext fun i => ?_⟩
  simp [dotB_apply, dotProduct_sum, dotProduct_smul, B_dot_U]

private theorem C_eq_ker_dotB : C = LinearMap.ker dotB := by
  have hle : C ≤ LinearMap.ker dotB := fun y hy =>
    funext fun i => by rw [dotB_apply]; exact dotProduct_eq_zero (B_mem_C i) hy
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h := LinearMap.finrank_range_add_finrank_ker dotB
  rw [LinearMap.range_eq_top.2 dotB_surjective, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h
  rw [finrank_C]
  omega

/-- The Golay code is self-dual. -/
theorem mem_C_iff_forall_dotProduct (x : Fin 24 → ZMod 2) :
    x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0 := by
  refine ⟨fun hx y hy => dotProduct_eq_zero hx hy, fun h => ?_⟩
  rw [C_eq_ker_dotB]
  exact funext fun i => by rw [dotB_apply, dotProduct_comm]; exact h _ (B_mem_C i)

/-! ### From `CFSG/Monster/Code/Cocycle.lean` -/
theorem supp_inter (d e : Fin 24 → ZMod 2) : supp d ∩ supp e = supp (d * e) := by
  ext i
  simp only [supp, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Pi.mul_apply]
  exact (mul_ne_zero_iff).symm

theorem card_supp (d : Fin 24 → ZMod 2) : (supp d).card = hammingNorm d := rfl

theorem A_eq_sum (d e f : Fin 24 → ZMod 2) : A d e f = ∑ i, d i * e i * f i := by
  rw [A, supp_inter, supp_inter, card_supp, ← sum_eq_hammingNorm]
  rfl

theorem K_eq (d e : Fin 24 → ZMod 2) : K d e = ((hammingNorm (d * e) / 2 : ℕ) : ZMod 2) := by
  rw [K, supp_inter, card_supp]

theorem K_comm (d e : Fin 24 → ZMod 2) : K d e = K e d := by
  rw [K, K, Finset.inter_comm]

theorem A_comm₁₂ (d e f : Fin 24 → ZMod 2) : A d e f = A e d f := by
  simp only [A_eq_sum, mul_comm (d _)]

theorem A_comm₂₃ (d e f : Fin 24 → ZMod 2) : A d e f = A d f e := by
  simp only [A_eq_sum, mul_assoc, mul_comm (e _)]

theorem A_add_right (d e f f' : Fin 24 → ZMod 2) : A d e (f + f') = A d e f + A d e f' := by
  simp only [A_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem A_sum_left {ι : Type*} [Fintype ι] (c : ι → ZMod 2) (b : ι → Fin 24 → ZMod 2)
    (y z : Fin 24 → ZMod 2) : A (∑ i, c i • b i) y z = ∑ i, c i * A (b i) y z := by
  simp only [A_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

theorem A_sum_mid {ι : Type*} [Fintype ι] (c : ι → ZMod 2) (b : ι → Fin 24 → ZMod 2)
    (x z : Fin 24 → ZMod 2) : A x (∑ i, c i • b i) z = ∑ i, c i * A x (b i) z := by
  rw [A_comm₁₂, A_sum_left]
  exact Finset.sum_congr rfl fun i _ => by rw [A_comm₁₂]

theorem A_sum_right {ι : Type*} [Fintype ι] (c : ι → ZMod 2) (b : ι → Fin 24 → ZMod 2)
    (x y : Fin 24 → ZMod 2) : A x y (∑ i, c i • b i) = ∑ i, c i * A x y (b i) := by
  rw [A_comm₂₃, A_sum_mid]
  exact Finset.sum_congr rfl fun i _ => by rw [A_comm₂₃]

theorem two_dvd_hammingNorm_mul {d e : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) :
    2 ∣ hammingNorm (d * e) := by
  have h := dotProduct_eq_zero hd he
  rw [dotProduct_eq_hammingNorm] at h
  exact (ZMod.natCast_eq_zero_iff _ _).1 h

private theorem key_cast : ∀ a b c k : ZMod 2, c + k = a + b → c = a + b + k := by decide

theorem P_add {d e : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) :
    P (d + e) = P d + P e + K d e := by
  have h := hammingNorm_add_add d e
  have h1 := four_dvd_wt hd
  have h2 := four_dvd_wt he
  have h3 := four_dvd_wt (C.add_mem hd he)
  have h4 := two_dvd_hammingNorm_mul hd he
  have hn : hammingNorm (d + e) / 4 + hammingNorm (d * e) / 2 =
      hammingNorm d / 4 + hammingNorm e / 4 := by omega
  rw [P, P, P, K_eq]
  apply key_cast
  exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 2) hn

private theorem mul_self' (f : Fin 24 → ZMod 2) : f * f = f := by
  funext i
  simp only [Pi.mul_apply]
  rcases zmod2_cases (f i) with h | h <;> rw [h] <;> rfl

theorem K_add_left {d e f : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) (hf : f ∈ C) :
    K (d + e) f = K d f + K e f + A d e f := by
  have h := hammingNorm_add_add (d * f) (e * f)
  have hde : d * f + e * f = (d + e) * f := (add_mul d e f).symm
  have hdef : d * f * (e * f) = d * e * f := by
    funext i
    simp only [Pi.mul_apply]
    generalize d i = a, e i = b, f i = c
    revert a b c; decide
  rw [hde, hdef] at h
  have h1 := two_dvd_hammingNorm_mul hd hf
  have h2 := two_dvd_hammingNorm_mul he hf
  have h3 := two_dvd_hammingNorm_mul (C.add_mem hd he) hf
  have hn : hammingNorm ((d + e) * f) / 2 + hammingNorm (d * e * f) =
      hammingNorm (d * f) / 2 + hammingNorm (e * f) / 2 := by omega
  rw [K_eq, K_eq, K_eq, A, supp_inter, supp_inter, card_supp]
  apply key_cast
  exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 2) hn

theorem K_self {d : Fin 24 → ZMod 2} (hd : d ∈ C) : K d d = 0 := by
  rw [K_eq, mul_self']
  obtain ⟨m, hm⟩ := four_dvd_wt hd
  rw [hm, show 4 * m / 2 = 2 * m by omega, Nat.cast_mul, Nat.cast_ofNat, two_eq_zero', zero_mul]

theorem A_self_left {d e : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) : A d d e = 0 := by
  calc A d d e = ∑ i, d i * e i := by
        rw [A_eq_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [← Pi.mul_apply d d i, mul_self']
    _ = d ⬝ᵥ e := rfl
    _ = 0 := dotProduct_eq_zero hd he

theorem A_self_mid {d e : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) : A d e d = 0 := by
  rw [A_comm₂₃, A_self_left hd he]

theorem A_self_right {d e : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) : A d e e = 0 := by
  rw [A_comm₁₂, A_comm₂₃, A_self_left he hd]

theorem θc_zero_left (ν : Fin 12 → ZMod 2) : θc 0 ν = 0 := by
  simp [θc_eq]

theorem θc_zero_right (μ : Fin 12 → ZMod 2) : θc μ 0 = 0 := by
  simp [θc_eq]

theorem Ab_comm (i j k : Fin 12) : Ab i j k = Ab j i k := A_comm₁₂ _ _ _

theorem Ab_self (i k : Fin 12) : Ab i i k = 0 := A_self_left (B_mem_C i) (B_mem_C k)

private theorem lt01_add_mul (i j k : Fin 12) : (lt01 i j + lt01 j i) * Ab i j k = Ab i j k := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [lt01, h, not_lt_of_gt h]
  · simp [Ab_self]
  · simp [lt01, h, not_lt_of_gt h]

def Atri (μ μ' ν : Fin 12 → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, ∑ k, μ i * μ' j * ν k * Ab i j k

theorem θc_add_left (μ μ' ν : Fin 12 → ZMod 2) :
    θc (μ + μ') ν = θc μ ν + θc μ' ν + Atri μ μ' ν := by
  have hpol : Atri μ μ' ν = ∑ i, ∑ j, ∑ k, lt01 i j * μ i * μ' j * ν k * Ab i j k +
      ∑ i, ∑ j, ∑ k, lt01 i j * μ' i * μ j * ν k * Ab i j k := by
    rw [Finset.sum_comm (f := fun i j => ∑ k, lt01 i j * μ' i * μ j * ν k * Ab i j k),
      ← Finset.sum_add_distrib, Atri]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Ab_comm j i k]
    linear_combination (μ i * μ' j * ν k) * (lt01_add_mul i j k).symm
  rw [hpol]
  simp only [θc_eq, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem θc_single (i j : Fin 12) : θc (Pi.single i 1) (Pi.single j 1) = β i j := by
  simp [θc_eq, Pi.single_apply, ite_mul, mul_ite, lt01, Finset.sum_ite_eq']

theorem repr_apply (d : C) (i : Fin 12) : basisC.repr d i = ψ d i := by
  have h : basisC.equivFun.symm (ψ d) = d := by
    apply Subtype.ext
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    simp only [Submodule.coe_smul, basisC_apply]
    exact (eq_comb_of_mem_C d.2).symm
  have h' := congrArg (fun x => basisC.equivFun x i) h
  simp only [LinearEquiv.apply_symm_apply] at h'
  rw [h', Module.Basis.equivFun_apply]

theorem coe_eq_sum (d : C) : (d : Fin 24 → ZMod 2) = ∑ i, basisC.repr d i • B i := by
  conv_lhs => rw [← basisC.sum_repr d]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, basisC_apply]

theorem Atri_repr (d e f : C) :
    Atri (basisC.repr d) (basisC.repr e) (basisC.repr f) = A d e f := by
  rw [coe_eq_sum d, coe_eq_sum e, coe_eq_sum f, A_sum_left, Atri]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [A_sum_mid, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [A_sum_right, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Ab]
  ring

theorem θ_add_left (d e f : C) : θ (d + e) f = θ d f + θ e f + A d e f := by
  rw [θ, θ, θ, map_add, Finsupp.coe_add, θc_add_left, Atri_repr]

@[simp] theorem θ_zero_left (e : C) : θ 0 e = 0 := by
  rw [θ, map_zero, Finsupp.coe_zero, θc_zero_left]

@[simp] theorem θ_zero_right (d : C) : θ d 0 = 0 := by
  rw [θ, map_zero, Finsupp.coe_zero, θc_zero_right]

theorem θ_basis (i j : Fin 12) : θ (basisC i) (basisC j) = β i j := by
  rw [θ, basisC.repr_self, basisC.repr_self, Finsupp.single_eq_pi_single,
    Finsupp.single_eq_pi_single, θc_single]

theorem eq_zero_of_additive (f : C → ZMod 2) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hB : ∀ i, f (basisC i) = 0) (x : C) : f x = 0 := by
  let F : C →+ ZMod 2 := AddMonoidHom.mk' f hadd
  change F x = 0
  rw [← basisC.sum_repr x, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases zmod2_cases (basisC.repr x i) with h | h <;> rw [h]
  · rw [zero_smul, map_zero]
  · rw [one_smul]; exact hB i

theorem θ_add_θ_swap (d e : C) : θ d e + θ e d = K d e := by
  let S : C → C → ZMod 2 := fun d e => θ d e + θ e d + K d e
  have hS : ∀ d d' e, S (d + d') e = S d e + S d' e := by
    intro d d' e
    simp only [S, θ_add_left, θ_add_right, Submodule.coe_add,
      K_add_left d.2 d'.2 e.2]
    linear_combination (A d d' e) * two_eq_zero'
  have hsymm : ∀ d e, S d e = S e d := by
    intro d e
    simp only [S, K_comm (d : Fin 24 → ZMod 2)]
    ring
  have hbasis : ∀ i j, S (basisC i) (basisC j) = 0 := by
    intro i j
    simp only [S, θ_basis, basisC_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · have h1 : β i j = 0 := by simp [β, h]
      have h2 : β j i = K (B j) (B i) := by simp [β, not_lt_of_gt h, (ne_of_lt h).symm]
      rw [h1, h2, K_comm (B j), zero_add]
      linear_combination (K (B i) (B j)) * two_eq_zero'
    · have h1 : β i i = P (B i) := by simp [β]
      rw [h1, K_self (B_mem_C i)]
      linear_combination (P (B i)) * two_eq_zero'
    · have h1 : β j i = 0 := by simp [β, h]
      have h2 : β i j = K (B i) (B j) := by simp [β, not_lt_of_gt h, (ne_of_lt h).symm]
      rw [h1, h2, K_comm (B i), add_zero]
      linear_combination (K (B j) (B i)) * two_eq_zero'
  have h1 : ∀ i e, S (basisC i) e = 0 := by
    intro i e
    rw [hsymm]
    exact eq_zero_of_additive (fun e => S e (basisC i)) (fun x y => hS x y _)
      (fun j => hbasis j i) e
  have h2 : S d e = 0 :=
    eq_zero_of_additive (fun d => S d e) (fun x y => hS x y _) (fun i => h1 i e) d
  linear_combination h2 - (K d e) * two_eq_zero'

theorem θ_self (d : C) : θ d d = P d := by
  let D : C → ZMod 2 := fun d => θ d d + P d
  have hD : ∀ x y, D (x + y) = D x + D y := by
    intro x y
    simp only [D, θ_add_left, θ_add_right, Submodule.coe_add, P_add x.2 y.2,
      A_self_mid x.2 y.2, A_self_right x.2 y.2]
    have := θ_add_θ_swap x y
    linear_combination this + (K x y) * two_eq_zero'
  have hB : ∀ i, D (basisC i) = 0 := by
    intro i
    have h1 : β i i = P (B i) := by simp [β]
    simp only [D, θ_basis, basisC_apply, h1]
    linear_combination (P (B i)) * two_eq_zero'
  have h := eq_zero_of_additive D hD hB d
  linear_combination h - (P d) * two_eq_zero'

end VOA.Moonshine.MonsterGriess.Code

namespace VOA.Moonshine.MonsterGriess.Spin

open VOA.Moonshine.MonsterGriess.Code

/-! ### From `CFSG/Monster/Spin/Pairing.lean` -/
theorem pair_add_left (a b : C) (δ : Cocode) : pair (a + b) δ = pair a δ + pair b δ := by
  induction δ using Submodule.Quotient.induction_on with
  | H x => simp only [pair_mk, Submodule.coe_add, add_dotProduct]

theorem pair_smul_left (c : ZMod 2) (a : C) (δ : Cocode) : pair (c • a) δ = c * pair a δ := by
  induction δ using Submodule.Quotient.induction_on with
  | H x => simp only [pair_mk, Submodule.coe_smul, smul_dotProduct, smul_eq_mul]

@[simp] theorem pair_zero_left (δ : Cocode) : pair 0 δ = 0 := by
  induction δ using Submodule.Quotient.induction_on with
  | H x => simp only [pair_mk, Submodule.coe_zero, zero_dotProduct]

theorem pair_add_right (a : C) (δ ε : Cocode) : pair a (δ + ε) = pair a δ + pair a ε :=
  map_add _ _ _

@[simp] theorem pair_zero_right (a : C) : pair a 0 = 0 := map_zero _

theorem eq_zero_of_forall_pair {δ : Cocode} (h : ∀ u : C, pair u δ = 0) : δ = 0 := by
  induction δ using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.Quotient.mk_eq_zero, mem_C_iff_forall_dotProduct]
    intro y hy
    rw [dotProduct_comm]
    exact h ⟨y, hy⟩

theorem ext_pair {δ ε : Cocode} (h : ∀ u : C, pair u δ = pair u ε) : δ = ε := by
  rw [← sub_eq_zero]
  exact eq_zero_of_forall_pair fun u => by rw [map_sub, h u, sub_self]

theorem eq_zero_of_forall_pair_left {a : C} (h : ∀ δ : Cocode, pair a δ = 0) : a = 0 := by
  apply Subtype.ext
  funext i
  have := h (Submodule.Quotient.mk (Pi.single i 1))
  rw [pair_mk, dotProduct_single, mul_one] at this
  exact this

theorem finrank_cocode : Module.finrank (ZMod 2) Cocode = 12 := by
  have h : Module.finrank (ZMod 2) Cocode + Module.finrank (ZMod 2) C = 24 := by
    have := Submodule.finrank_quotient_add_finrank C
    rwa [Module.finrank_fin_fun] at this
  rw [finrank_C] at h
  omega

theorem pair_thetaD (a u : C) : pair u (thetaD a) = θ a u :=
  (exists_pair_eq (θL a)).choose_spec u

theorem thetaD_unique {a : C} {δ : Cocode} (h : ∀ u : C, pair u δ = θ a u) : δ = thetaD a :=
  ext_pair fun u => by rw [h u, pair_thetaD]

theorem pair_self_thetaD (a : C) : pair a (thetaD a) = P a := by
  rw [pair_thetaD, θ_self]

@[simp] theorem thetaD_zero : thetaD 0 = 0 :=
  (thetaD_unique fun u => by rw [pair_zero_right, θ_zero_left]).symm

def Acocode (a b : C) : Cocode :=
  Submodule.Quotient.mk ((a : Fin 24 → ZMod 2) * b)

theorem pair_Acocode (a b u : C) : pair u (Acocode a b) = A a b u := by
  rw [Acocode, pair_mk, A_eq_sum, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.mul_apply]; ring

/-- `thetaD (a + b) = thetaD a + thetaD b + Acocode a b`: the cocode class of the cocycle `θ` is
additive up to the triple-intersection class. -/
theorem thetaD_add (a b : C) : thetaD (a + b) = thetaD a + thetaD b + Acocode a b :=
  (thetaD_unique fun u => by
    rw [pair_add_right, pair_add_right, pair_thetaD, pair_thetaD, pair_Acocode,
      θ_add_left]).symm

end VOA.Moonshine.MonsterGriess.Spin
