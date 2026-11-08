/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Lagrangian.lean (`fourier`, `signOp`, `lagrangianFun`, `sum_sgn_of_perp`,
    `fourier_lagrangianFun`, `signOp_lagrangianFun`; the rest was ported in
    `OctadEvenSubset.lean`)
  CFSG/Monster/Griess/Invariance/ThreeOctad.lean
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
import VOA.Moonshine.MonsterGriess.InvarianceOctadBasic

/-!
# Axiom's Monster port: triality invariance on (octad, octad, octad) triples

On the octad sector `tauB = octDop ∘ octHop` (`tauB_eq_octDop_octHop`), where `octHop`, `octDop`
act on the 64 vectors of each octad by the Fourier matrix `octH d` and the sign matrix `octD d`.
For three octads `d₁ + d₂ + d₃ = 0`, the values of `T` on octad vectors form the Lagrangian
function of the 9-dimensional Lagrangian `K` of `three_octad_lagrangian_correspondence`
(`T_oct3_of_sum_zero`), which is fixed by the Fourier transform (`fourier_lagrangianFun`) and by
the sign operator (`signOp_lagrangianFun`); otherwise `T` vanishes (`T_oct3_eq_zero`).  Hence
`T` is invariant under `octHop`, `octDop`, and so under `tauB`, on `octSpan³`.  Summary:
`triality_Griess_three_octad_invariance`.

## Port notes
* Namespace `CFSG.Monster`, `CFSG.Monster.Griess` ↦ `VOA.Moonshine.MonsterGriess` (as in the
  earlier ports).  Module-system syntax, `@[expose]` and the source's `attribute [-instance] …`
  line dropped.  Bodies verbatim except as listed.
* From `Lagrangian.lean`: `fourier`, `signOp`, `lagrangianFun`, `sum_sgn_of_perp`,
  `fourier_lagrangianFun`, `signOp_lagrangianFun` added here (not ported earlier; the rest of
  that file is in `OctadEvenSubset.lean`).  In `fourier_lagrangianFun`, Mathlib drift
  `ite_eq_left h` ↦ `if_pos h`, `ite_eq_right h` ↦ `if_neg h`.
* Short name also declared elsewhere in `VOA/` in another namespace (no clash, not renamed):
  `tv` (`Classification/COne/OrbPrimEquiv.lean`).
-/

set_option linter.style.longLine false
set_option linter.style.show false

/-! ### From `CFSG/Monster/Lagrangian.lean` -/

namespace VOA.Moonshine.MonsterGriess

open Module

section LagrangianFun

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Fintype E]

def fourier (b : LinearMap.BilinForm (ZMod 2) E) (m : ℕ) (f : E → ℚ) (u : E) : ℚ :=
  ((2 : ℚ) ^ m)⁻¹ * ∑ v, sgn (b u v) * f v

def signOp (q : E → ZMod 2) (f : E → ℚ) (v : E) : ℚ := sgn (q v) * f v

def lagrangianFun (b : LinearMap.BilinForm (ZMod 2) E) (K : Submodule (ZMod 2) E)
    (a : E) [DecidablePred (· ∈ K)] (v : E) : ℚ :=
  if v - a ∈ K then sgn (b a v) else 0

theorem sum_sgn_of_perp (b : LinearMap.BilinForm (ZMod 2) E) (K : Submodule (ZMod 2) E)
    [DecidablePred (· ∈ K)] {w : E} (h : ∀ k ∈ K, b w k = 0) :
    ∑ k : K, sgn (b w k) = (Fintype.card K : ℚ) := by
  simp [h, sgn]

theorem fourier_lagrangianFun (b : LinearMap.BilinForm (ZMod 2) E) (hb : b.Nondegenerate)
    (halt : ∀ v, b v v = 0) {m : ℕ} (hE : finrank (ZMod 2) E = 2 * m)
    (K : Submodule (ZMod 2) E) [DecidablePred (· ∈ K)] (hK : finrank (ZMod 2) K = m)
    (hKK : ∀ x ∈ K, ∀ y ∈ K, b x y = 0) (a : E) :
    fourier b m (lagrangianFun b K a) = lagrangianFun b K a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsymm := symm_of_alternating halt
  have hKperp : b.orthogonal K = K := by
    symm
    have hle : K ≤ b.orthogonal K := fun x hx =>
      (LinearMap.BilinForm.mem_orthogonal_iff).2 fun n hn => hKK n hn x hx
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [LinearMap.BilinForm.finrank_orthogonal hb, hE, hK]
    omega
  have hmemperp : ∀ w : E, (∀ k ∈ K, b w k = 0) ↔ w ∈ K := by
    intro w
    constructor
    · intro h
      have hw : w ∈ b.orthogonal K := (LinearMap.BilinForm.mem_orthogonal_iff).2 fun n hn => by
        change b n w = 0
        rw [hsymm]
        exact h n hn
      rwa [hKperp] at hw
    · intro hw k hk
      exact hKK w hw k hk
  have hcardK : (Fintype.card K : ℚ) = 2 ^ m := by
    rw [← FiniteField.pow_finrank_eq_card 2 K, hK]
    push_cast
    rfl
  funext u
  simp only [fourier, lagrangianFun]
  have hre : ∑ v, sgn (b u v) * (if v - a ∈ K then sgn (b a v) else 0) =
      ∑ k : K, sgn (b u (a + k)) * sgn (b a (a + k)) := by
    rw [← Fintype.sum_equiv (Equiv.addLeft a) (fun w => sgn (b u (a + w)) *
      (if a + w - a ∈ K then sgn (b a (a + w)) else 0)) _ (fun w => rfl)]
    simp only [add_sub_cancel_left, mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun x => by simp) (fun x => sgn (b u (a + x)) * sgn (b a (a + x)))
  rw [hre]
  have hterm : ∀ k : K, sgn (b u (a + k)) * sgn (b a (a + k)) =
      sgn (b u a) * sgn (b (u + a) k) := by
    intro k
    simp only [map_add, LinearMap.add_apply, halt a, zero_add, sgn_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sub_eq_add_zmod_two]
  by_cases h : u + a ∈ K
  · rw [if_pos h, sum_sgn_of_perp b K ((hmemperp _).2 h), hcardK, hsymm u a]
    field_simp
  · rw [if_neg h]
    have : ¬ ∀ k ∈ K, b (u + a) k = 0 := fun h' => h ((hmemperp _).1 h')
    simp only [not_forall] at this
    obtain ⟨k₀, hk₀, hne⟩ := this
    rw [sum_sgn_of_not_perp b K hk₀ hne]
    simp

omit [Fintype E] in
theorem signOp_lagrangianFun (b : LinearMap.BilinForm (ZMod 2) E) (K : Submodule (ZMod 2) E)
    [DecidablePred (· ∈ K)] (a : E) (q : E → ZMod 2) (hq : ∀ v, v - a ∈ K → q v = 0) :
    signOp q (lagrangianFun b K a) = lagrangianFun b K a := by
  funext v
  simp only [signOp, lagrangianFun]
  split_ifs with h
  · rw [hq v h, sgn_zero, one_mul]
  · rw [mul_zero]

end LagrangianFun

end VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/Griess/Invariance/ThreeOctad.lean` -/

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin VOA.Moonshine.MonsterGriess.SpinLattice Matrix Module

namespace OctadInv

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem zmod2_aux3 : ∀ a b c : ZMod 2, a + b = c + (a + b + c) := by decide

noncomputable def octOpFun
    (M : ∀ d : OctadWord, Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ) :
    TIdx → SpaceB
  | .inr (.inr (.inr o)) => ∑ w, M o.1 o.2 w • octVec ⟨o.1, w⟩
  | x => tbasis x

noncomputable def octOp
    (M : ∀ d : OctadWord, Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ) :
    SpaceB →ₗ[ℚ] SpaceB :=
  tbasis.constr ℚ (octOpFun M)

theorem octOp_octVec
    (M : ∀ d : OctadWord, Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ)
    (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    octOp M (octVec ⟨d, v⟩) = ∑ w, M d v w • octVec ⟨d, w⟩ := by
  rw [octOp, octVec, Module.Basis.constr_basis]
  rfl

noncomputable abbrev octHop : SpaceB →ₗ[ℚ] SpaceB := octOp octH

noncomputable abbrev octDop : SpaceB →ₗ[ℚ] SpaceB := octOp octD

theorem octOp_mem_octSpan
    (M : ∀ d : OctadWord, Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ)
    {u : SpaceB} (hu : u ∈ octSpan) : octOp M u ∈ octSpan := by
  refine map_mem_span (octOp M) ?_ hu
  rintro _ ⟨⟨d, v⟩, rfl⟩
  rw [octOp_octVec]
  exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (octVec_mem_octSpan _)

theorem tauB_eq_octDop_octHop {u : SpaceB} (hu : u ∈ octSpan) : tauB u = octDop (octHop u) := by
  have key : Set.EqOn (tauB : SpaceB →ₗ[ℚ] SpaceB) (octDop ∘ₗ octHop) (Set.range octVec) := by
    rintro _ ⟨⟨d, v⟩, rfl⟩
    show tauB (octVec ⟨d, v⟩) = octDop (octHop (octVec ⟨d, v⟩))
    rw [tauB_octVec, octOp_octVec, map_sum]
    simp only [map_smul, octOp_octVec, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_smul, octHD, Matrix.mul_apply]
  exact LinearMap.eqOn_span key hu

theorem octD_apply' (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) :
    octD d v w = if v = w then sgn (qd d v) else 0 := by
  rw [octD, signMatrix, diagonal_apply]

theorem octH_apply (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) :
    octH d v w = (8 : ℚ)⁻¹ * sgn (bd d v w) := by
  rw [octH, fourierMatrix]
  norm_num

theorem T_oct3 (o1 o2 o3 : OctIdx) :
    T (octVec o1) (octVec o2) (octVec o3) = tau (octLab o2) (octLab o1) (octLab o3) := by
  rw [T_swap12, octVec_eq, octVec_eq, octVec_eq, T_sgl3]

theorem fst3_iff (d1 d2 d3 : C) (n1 n2 n3 : ZMod 2) :
    d3 + n3 • ΩC = d2 + n2 • ΩC + (d1 + n1 • ΩC) ↔ d1 + d2 + d3 = (n1 + n2 + n3) • ΩC := by
  have e : d3 + n3 • ΩC + (d2 + n2 • ΩC + (d1 + n1 • ΩC)) =
      d1 + d2 + d3 + (n1 + n2 + n3) • ΩC := by
    rw [add_smul, add_smul]
    abel
  rw [eq_iff_add_eq_zero_F2 (d3 + n3 • ΩC), e, add_eq_zero_iff', eq_comm]

theorem snd3_iff_of_sum_zero {d1 d2 d3 : C} (hs : d1 + d2 + d3 = 0) (x1 x2 x3 : Cocode) :
    thetaD d3 + x3 = thetaD d2 + x2 + (thetaD d1 + x1) ↔ x1 + x2 + x3 = Acocode d1 d2 := by
  have h3 : d3 = d1 + d2 := add_eq_zero_iff'.1 hs
  have e : thetaD d3 + x3 + (thetaD d2 + x2 + (thetaD d1 + x1)) =
      Acocode d1 d2 + (x1 + x2 + x3) := by
    rw [h3, thetaD_add]
    have e' : thetaD d1 + thetaD d2 + Acocode d1 d2 + x3 + (thetaD d2 + x2 + (thetaD d1 + x1)) =
        (thetaD d1 + thetaD d1) + (thetaD d2 + thetaD d2) + (Acocode d1 d2 + (x1 + x2 + x3)) := by
      abel
    rw [e', add_self_F2, add_self_F2, zero_add, zero_add]
  rw [eq_iff_add_eq_zero_F2 (thetaD d3 + x3), e, add_eq_zero_iff']

theorem snd3_iff_of_sum_Ω {d1 d2 d3 : C} (hs : d1 + d2 + d3 = ΩC)
    (hd : (d1 : Fin 24 → ZMod 2) * d2 = 0) (x1 x2 x3 : Cocode) :
    thetaD d3 + x3 = thetaD d2 + x2 + (thetaD d1 + x1) ↔ x1 + x2 + x3 = 0 := by
  have h3 : d3 = d1 + d2 + (1 : ZMod 2) • ΩC := by
    calc d3 = ((d1 + d2) + (d1 + d2)) + d3 := by rw [add_self_F2, zero_add]
      _ = (d1 + d2) + ((d1 + d2) + d3) := by abel
      _ = d1 + d2 + (1 : ZMod 2) • ΩC := by rw [hs, one_smul]
  have hA : Acocode d1 d2 = 0 := by
    rw [Acocode, hd, Submodule.Quotient.mk_zero]
  have hθ : thetaD d3 = thetaD d1 + thetaD d2 := by
    rw [h3, thetaD_add_smul_ΩC, thetaD_add, hA, add_zero]
  have e : thetaD d3 + x3 + (thetaD d2 + x2 + (thetaD d1 + x1)) = x1 + x2 + x3 := by
    rw [hθ]
    have e' : thetaD d1 + thetaD d2 + x3 + (thetaD d2 + x2 + (thetaD d1 + x1)) =
        (thetaD d1 + thetaD d1) + (thetaD d2 + thetaD d2) + (x1 + x2 + x3) := by
      abel
    rw [e', add_self_F2, add_self_F2, zero_add, zero_add]
  rw [eq_iff_add_eq_zero_F2 (thetaD d3 + x3), e]

theorem mul_eq_zero_of_sum_Ω {d1 d2 d3 : OctadWord} (hs : (d1 : C) + d2 + d3 = ΩC) :
    ((d1 : C) : Fin 24 → ZMod 2) * (d2 : C) = 0 := by
  have hv : ((d1 : C) : Fin 24 → ZMod 2) + (d2 : C) = ((d3 : C) : Fin 24 → ZMod 2) + Ω := by
    have h := congrArg (fun x : C => (x : Fin 24 → ZMod 2)) hs
    simp only [Submodule.coe_add, coe_ΩC] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply] at hi ⊢
    rw [← hi]
    exact zmod2_aux3 _ _ _
  have h1 := Code.hammingNorm_add_add ((d1 : C) : Fin 24 → ZMod 2) (d2 : C)
  rw [hv, d1.2, d2.2] at h1
  have h2 := hammingNorm_add_Ω ((d3 : C) : Fin 24 → ZMod 2)
  rw [d3.2] at h2
  exact hammingNorm_eq_zero.1 (by omega)

theorem ind_mul_ind_eq_zero {d d' : OctadWord}
    (hdd : ((d : C) : Fin 24 → ZMod 2) * (d' : C) = 0) {δ δ' : Finset (Fin 24)}
    (hδ : δ ⊆ octSupp d) (hδ' : δ' ⊆ octSupp d') : Octad.ind δ * Octad.ind δ' = 0 := by
  funext i
  by_cases h : i ∈ δ ∧ i ∈ δ'
  · exfalso
    have := congrFun hdd i
    rw [Pi.mul_apply, coe_apply_eq_one (hδ h.1), coe_apply_eq_one (hδ' h.2), one_mul] at this
    exact one_ne_zero this
  · rw [Pi.mul_apply, Pi.zero_apply, Octad.ind_apply, Octad.ind_apply]
    by_cases h1 : i ∈ δ
    · rw [if_pos h1, if_neg (fun h2 => h ⟨h1, h2⟩), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem hammingNorm_ind3 {δ1 δ2 δ3 : Finset (Fin 24)} (h12 : Octad.ind δ1 * Octad.ind δ2 = 0)
    (h13 : Octad.ind δ1 * Octad.ind δ3 = 0) (h23 : Octad.ind δ2 * Octad.ind δ3 = 0) :
    hammingNorm (Octad.ind δ1 + Octad.ind δ2 + Octad.ind δ3) = δ1.card + δ2.card + δ3.card := by
  have e1 := Code.hammingNorm_add_add (Octad.ind δ1) (Octad.ind δ2)
  have e2 := Code.hammingNorm_add_add (Octad.ind δ1 + Octad.ind δ2) (Octad.ind δ3)
  rw [h12, hammingNorm_zero, hammingNorm_ind, hammingNorm_ind] at e1
  rw [add_mul, h13, h23, add_zero, hammingNorm_zero, hammingNorm_ind] at e2
  omega

theorem nOct_sum_eq_zero {δ1 δ2 δ3 : Finset (Fin 24)} (h1 : Even δ1.card) (h2 : Even δ2.card)
    (h3 : Even δ3.card) (h4 : 4 ∣ δ1.card + δ2.card + δ3.card) :
    nOct δ1 + nOct δ2 + nOct δ3 = 0 := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  obtain ⟨c, hc⟩ := h3
  obtain ⟨m, hm⟩ := h4
  have e : δ1.card / 2 + δ2.card / 2 + δ3.card / 2 = 2 * m := by omega
  unfold nOct
  rw [← Nat.cast_add, ← Nat.cast_add, e, Nat.cast_mul, Nat.cast_ofNat,
    show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem T_oct3_eq_zero {d1 d2 d3 : OctadWord} (hs : (d1 : C) + d2 + d3 ≠ 0)
    (v1 : Octad.EvenQuot (octSupp d1)) (v2 : Octad.EvenQuot (octSupp d2))
    (v3 : Octad.EvenQuot (octSupp d3)) :
    T (octVec ⟨d1, v1⟩) (octVec ⟨d2, v2⟩) (octVec ⟨d3, v3⟩) = 0 := by
  rw [T_oct3, tau_eq, if_neg]
  intro h
  rw [octLab_fst, octLab_fst, octLab_fst, Prod.mk_add_mk, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [fst3_iff] at h1
  rcases zmod2_cases (nOct (octRep d1 v1) + nOct (octRep d2 v2) + nOct (octRep d3 v3)) with
    hn | hn
  · rw [hn, zero_smul] at h1
    exact hs h1
  · rw [hn, one_smul] at h1
    have h12 := mul_eq_zero_of_sum_Ω h1
    have h13 := mul_eq_zero_of_sum_Ω (d1 := d1) (d2 := d3) (d3 := d2)
      (by rw [add_right_comm]; exact h1)
    have h23 := mul_eq_zero_of_sum_Ω (d1 := d2) (d2 := d3) (d3 := d1)
      (by rw [← h1]; abel)
    rw [snd3_iff_of_sum_Ω h1 h12] at h2
    have hmem : Octad.ind (octRep d1 v1) + Octad.ind (octRep d2 v2) + Octad.ind (octRep d3 v3) ∈
        C := by
      rw [← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add,
        Submodule.Quotient.mk_eq_zero] at h2
      exact h2
    have hw := four_dvd_wt hmem
    rw [hammingNorm_ind3 (ind_mul_ind_eq_zero h12 (octRep_subset d1 v1) (octRep_subset d2 v2))
      (ind_mul_ind_eq_zero h13 (octRep_subset d1 v1) (octRep_subset d3 v3))
      (ind_mul_ind_eq_zero h23 (octRep_subset d2 v2) (octRep_subset d3 v3))] at hw
    have h0 := nOct_sum_eq_zero (octRep_even d1 v1) (octRep_even d2 v2) (octRep_even d3 v3) hw
    rw [hn] at h0
    exact one_ne_zero h0

theorem octadTriple_of {d1 d2 d3 : OctadWord} (hs : (d1 : C) + d2 + d3 = 0) :
    Octad.OctadTriple C ((d1 : C) : Fin 24 → ZMod 2) ((d2 : C) : Fin 24 → ZMod 2)
      ((d3 : C) : Fin 24 → ZMod 2) :=
  ⟨fun _ hc => four_dvd_wt hc, fun _ hc h0 => eight_le_wt hc h0, (d1 : C).2, (d2 : C).2,
    (d3 : C).2, d1.2, d2.2, d3.2, by
      have h := congrArg (fun x : C => (x : Fin 24 → ZMod 2)) hs
      simpa only [Submodule.coe_add, Submodule.coe_zero] using h⟩

theorem ind_mul_ind' (A B : Finset (Fin 24)) (i : Fin 24) :
    Octad.ind A i * Octad.ind B i = Octad.ind (A ∩ B) i := by
  simp only [Octad.ind, ite_zero_mul_ite_zero, mul_one, Finset.mem_inter]

theorem dotProduct_ind (x : Fin 24 → ZMod 2) (δ : Finset (Fin 24)) :
    x ⬝ᵥ Octad.ind δ = ((Octad.wordSupport x ∩ δ).card : ZMod 2) := by
  conv_lhs => rw [← Octad.ind_wordSupport x]
  rw [dotProduct]
  simp only [ind_mul_ind']
  exact Octad.sum_ind (Finset.subset_univ _)

theorem pair_oct_ind_card (d : OctadWord) (δ : Finset (Fin 24)) :
    pair (d : C) (Submodule.Quotient.mk (Octad.ind δ)) =
      ((Octad.wordSupport ((d : C) : Fin 24 → ZMod 2) ∩ δ).card : ZMod 2) := by
  rw [pair_mk]
  exact dotProduct_ind _ _

abbrev ow (d : OctadWord) : Fin 24 → ZMod 2 := ((d : C) : Fin 24 → ZMod 2)

abbrev oTS (d1 d2 d3 : OctadWord) : Type := Octad.TripleSpace (ow d1) (ow d2) (ow d3)

noncomputable abbrev oK (d1 d2 d3 : OctadWord) : Submodule (ZMod 2) (oTS d1 d2 d3) :=
  LinearMap.ker (Octad.tripleCocode C (ow d1) (ow d2) (ow d3))

noncomputable abbrev ob (d1 d2 d3 : OctadWord) : LinearMap.BilinForm (ZMod 2) (oTS d1 d2 d3) :=
  QuadraticMap.polarBilin (Octad.tripleQuad (ow d1) (ow d2) (ow d3))

noncomputable def oa₀ (d1 d2 d3 : OctadWord) : oTS d1 d2 d3 :=
  (0, Octad.cls (Octad.wordSupport (ow d2)) (Octad.wordSupport (ow d1) ∩ Octad.wordSupport (ow d2)),
    0)

noncomputable def tv {d1 d2 d3 : OctadWord} (v1 : Octad.EvenQuot (octSupp d1))
    (v2 : Octad.EvenQuot (octSupp d2)) (v3 : Octad.EvenQuot (octSupp d3)) : oTS d1 d2 d3 :=
  (v1, v2, v3)

theorem ob_tv {d1 d2 d3 : OctadWord} (v1 w1 : Octad.EvenQuot (octSupp d1))
    (v2 w2 : Octad.EvenQuot (octSupp d2)) (v3 w3 : Octad.EvenQuot (octSupp d3)) :
    ob d1 d2 d3 (tv v1 v2 v3) (tv w1 w2 w3) = bd d1 v1 w1 + (bd d2 v2 w2 + bd d3 v3 w3) :=
  Octad.polarBilin_tripleQuad _ _

theorem tq_tv {d1 d2 d3 : OctadWord} (v1 : Octad.EvenQuot (octSupp d1))
    (v2 : Octad.EvenQuot (octSupp d2)) (v3 : Octad.EvenQuot (octSupp d3)) :
    Octad.tripleQuad (ow d1) (ow d2) (ow d3) (tv v1 v2 v3) = qd d1 v1 + qd d2 v2 + qd d3 v3 :=
  Octad.tripleQuad_apply _ _ _

theorem tv_eq_cls {d1 d2 d3 : OctadWord} (v1 : Octad.EvenQuot (octSupp d1))
    (v2 : Octad.EvenQuot (octSupp d2)) (v3 : Octad.EvenQuot (octSupp d3)) :
    tv v1 v2 v3 = (Octad.cls (Octad.wordSupport (ow d1)) (octRep d1 v1),
      Octad.cls (Octad.wordSupport (ow d2)) (octRep d2 v2),
      Octad.cls (Octad.wordSupport (ow d3)) (octRep d3 v3)) :=
  Prod.ext (cls_octRep d1 v1).symm (Prod.ext (cls_octRep d2 v2).symm (cls_octRep d3 v3).symm)

theorem sum_oTS {d1 d2 d3 : OctadWord} (G : oTS d1 d2 d3 → ℚ) :
    ∑ w, G w = ∑ w1 : Octad.EvenQuot (octSupp d1), ∑ w2 : Octad.EvenQuot (octSupp d2),
      ∑ w3 : Octad.EvenQuot (octSupp d3), G (tv w1 w2 w3) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w1 _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

theorem tripleCocode_tv {d1 d2 d3 : OctadWord} (v1 : Octad.EvenQuot (octSupp d1))
    (v2 : Octad.EvenQuot (octSupp d2)) (v3 : Octad.EvenQuot (octSupp d3)) :
    Octad.tripleCocode C (ow d1) (ow d2) (ow d3) (tv v1 v2 v3) =
      Submodule.Quotient.mk (Octad.ind (octRep d1 v1) + Octad.ind (octRep d2 v2) +
        Octad.ind (octRep d3 v3)) := by
  have hc : ∀ (d : OctadWord) (v : Octad.EvenQuot (octSupp d)),
      Octad.cocodeMap C (octSupp d) v = Submodule.Quotient.mk (Octad.ind (octRep d v)) := by
    intro d v
    have h := Octad.cocodeMap_cls (C := C) (by rw [ind_octSupp]; exact (d : C).2)
      (octRep_subset d v) (octRep_even d v)
    rwa [cls_octRep] at h
  rw [Octad.tripleCocode_apply]
  show Octad.cocodeMap C (octSupp d1) v1 +
    (Octad.cocodeMap C (octSupp d2) v2 + Octad.cocodeMap C (octSupp d3) v3) = _
  rw [hc, hc, hc, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, add_assoc]

theorem lagrangian_facts {d1 d2 d3 : OctadWord} (hs : (d1 : C) + d2 + d3 = 0) :
    Module.finrank (ZMod 2) (oTS d1 d2 d3) = 18 ∧ Module.finrank (ZMod 2) (oK d1 d2 d3) = 9 ∧
    LinearMap.BilinForm.orthogonal (ob d1 d2 d3) (oK d1 d2 d3) = oK d1 d2 d3 ∧
    Octad.tripleCocode C (ow d1) (ow d2) (ow d3) (oa₀ d1 d2 d3) =
      Submodule.Quotient.mk (ow d1 * ow d2) ∧
    (∀ k ∈ oK d1 d2 d3, Octad.tripleQuad (ow d1) (ow d2) (ow d3) (oa₀ d1 d2 d3 + k) = 0) ∧
    (∀ (v1 : Octad.EvenQuot (octSupp d1)) (v2 : Octad.EvenQuot (octSupp d2))
      (v3 : Octad.EvenQuot (octSupp d3)), ob d1 d2 d3 (oa₀ d1 d2 d3) (tv v1 v2 v3) =
        ((Octad.wordSupport (ow d1) ∩ octRep d2 v2).card : ZMod 2)) ∧
    (ob d1 d2 d3).Nondegenerate := by
  have hT := octadTriple_of hs
  obtain ⟨-, -, hdim, hK, hperp, hja, hqa, hb, -, -⟩ :=
    Octad.three_octad_lagrangian_correspondence C
    (d := ow d1) (e := ow d2) (f := ow d3) (fun _ hc => four_dvd_wt hc)
    (fun _ hc h0 => eight_le_wt hc h0) (d1 : C).2 (d2 : C).2 (d3 : C).2 d1.2 d2.2 d3.2 hT.sum_eq
  refine ⟨hdim, hK, hperp, ?_, hqa, fun v1 v2 v3 => ?_, hT.polarBilin_tripleQuad_nondegenerate⟩
  · have hω : Octad.ind (Octad.wordSupport (ow d1) ∩ Octad.wordSupport (ow d2)) =
        ow d1 * ow d2 := by
      rw [← Octad.wordSupport_mul, Octad.ind_wordSupport]
    rw [← hω]
    exact hja
  · rw [tv_eq_cls]
    exact hb _ _ _ (octRep_subset d1 v1) (octRep_even d1 v1) (octRep_subset d2 v2)
      (octRep_even d2 v2) (octRep_subset d3 v3) (octRep_even d3 v3)

theorem T_oct3_of_sum_zero {d1 d2 d3 : OctadWord} (hs : (d1 : C) + d2 + d3 = 0)
    [DecidablePred (· ∈ oK d1 d2 d3)]
    (v1 : Octad.EvenQuot (octSupp d1)) (v2 : Octad.EvenQuot (octSupp d2))
    (v3 : Octad.EvenQuot (octSupp d3)) :
    T (octVec ⟨d1, v1⟩) (octVec ⟨d2, v2⟩) (octVec ⟨d3, v3⟩) =
      sgn (θ d2 d1) * lagrangianFun (ob d1 d2 d3) (oK d1 d2 d3) (oa₀ d1 d2 d3) (tv v1 v2 v3) := by
  obtain ⟨-, -, -, hja, hqa, hb, -⟩ := lagrangian_facts hs
  have hmem : tv v1 v2 v3 - oa₀ d1 d2 d3 ∈ oK d1 d2 d3 ↔
      Submodule.Quotient.mk (Octad.ind (octRep d1 v1)) +
        Submodule.Quotient.mk (Octad.ind (octRep d2 v2)) +
        Submodule.Quotient.mk (Octad.ind (octRep d3 v3)) = Acocode d1 d2 := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero, tripleCocode_tv, hja,
      ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add]
    rfl
  have key : (octLab ⟨d3, v3⟩).1 = (octLab ⟨d2, v2⟩).1 + (octLab ⟨d1, v1⟩).1 ↔
      tv v1 v2 v3 - oa₀ d1 d2 d3 ∈ oK d1 d2 d3 := by
    rw [octLab_fst, octLab_fst, octLab_fst, Prod.mk_add_mk, Prod.mk.injEq, fst3_iff, hs,
      snd3_iff_of_sum_zero hs, ← hmem]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have h0 := hqa _ h
      rw [add_sub_cancel, tq_tv, ← nOct_octRep, ← nOct_octRep, ← nOct_octRep] at h0
      rw [h0, zero_smul]
  have hsign : pair (octLab ⟨d1, v1⟩).1.1 (octLab ⟨d2, v2⟩).1.2 =
      θ d2 d1 + ob d1 d2 d3 (oa₀ d1 d2 d3) (tv v1 v2 v3) := by
    simp only [octLab_fst]
    rw [pair_add_smul_ΩC_thetaD, pair_ΩC_ind (octRep_even d2 v2), mul_zero, add_zero, hb,
      pair_oct_ind_card]
  rw [T_oct3, tau_eq, lagrangianFun]
  by_cases h : tv v1 v2 v3 - oa₀ d1 d2 d3 ∈ oK d1 d2 d3
  · rw [if_pos (key.2 h), if_pos h, hsign, sgn_add]
  · rw [if_neg (fun h' => h (key.1 h')), if_neg h, mul_zero]

theorem sum_octH3 {d1 d2 d3 : OctadWord} (hs : (d1 : C) + d2 + d3 = 0)
    [DecidablePred (· ∈ oK d1 d2 d3)]
    (v1 : Octad.EvenQuot (octSupp d1)) (v2 : Octad.EvenQuot (octSupp d2))
    (v3 : Octad.EvenQuot (octSupp d3)) :
    ∑ w1, ∑ w2, ∑ w3, octH d1 v1 w1 * octH d2 v2 w2 * octH d3 v3 w3 *
        lagrangianFun (ob d1 d2 d3) (oK d1 d2 d3) (oa₀ d1 d2 d3) (tv w1 w2 w3) =
      lagrangianFun (ob d1 d2 d3) (oK d1 d2 d3) (oa₀ d1 d2 d3) (tv v1 v2 v3) := by
  obtain ⟨hdim, hK, hperp, -, -, -, hnd⟩ := lagrangian_facts hs
  have hKK : ∀ x ∈ oK d1 d2 d3, ∀ y ∈ oK d1 d2 d3, ob d1 d2 d3 x y = 0 := by
    intro x hx y hy
    have hy' : y ∈ LinearMap.BilinForm.orthogonal (ob d1 d2 d3) (oK d1 d2 d3) := by
      rw [hperp]
      exact hy
    exact LinearMap.BilinForm.mem_orthogonal_iff.1 hy' x hx
  have hF := fourier_lagrangianFun (ob d1 d2 d3) hnd (polarBilin_self _) (m := 9)
    (hdim.trans (by norm_num)) (oK d1 d2 d3) hK hKK (oa₀ d1 d2 d3)
  have hv := congrFun hF (tv v1 v2 v3)
  rw [fourier, sum_oTS] at hv
  rw [← hv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w1 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w2 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w3 _ => ?_
  rw [octH_apply, octH_apply, octH_apply, ob_tv, sgn_add, sgn_add]
  ring

private theorem sum_ite_mul' {E : Type*} [Fintype E] [DecidableEq E] (v : E) (s : ℚ)
    (f : E → ℚ) : ∑ w, (if v = w then s else 0) * f w = s * f v := by
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem sum_octD3 {d1 d2 d3 : OctadWord} (v1 : Octad.EvenQuot (octSupp d1))
    (v2 : Octad.EvenQuot (octSupp d2)) (v3 : Octad.EvenQuot (octSupp d3))
    (g : Octad.EvenQuot (octSupp d1) → Octad.EvenQuot (octSupp d2) →
      Octad.EvenQuot (octSupp d3) → ℚ) :
    ∑ w1, ∑ w2, ∑ w3, octD d1 v1 w1 * octD d2 v2 w2 * octD d3 v3 w3 * g w1 w2 w3 =
      sgn (qd d1 v1) * (sgn (qd d2 v2) * (sgn (qd d3 v3) * g v1 v2 v3)) := by
  calc ∑ w1, ∑ w2, ∑ w3, octD d1 v1 w1 * octD d2 v2 w2 * octD d3 v3 w3 * g w1 w2 w3 =
        ∑ w1, octD d1 v1 w1 * ∑ w2, octD d2 v2 w2 * ∑ w3, octD d3 v3 w3 * g w1 w2 w3 := by
        simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by simp only [octD_apply', sum_ite_mul']

theorem T_octHop3 (o1 o2 o3 : OctIdx) :
    T (octHop (octVec o1)) (octHop (octVec o2)) (octHop (octVec o3)) =
      T (octVec o1) (octVec o2) (octVec o3) := by
  classical
  obtain ⟨d1, v1⟩ := o1
  obtain ⟨d2, v2⟩ := o2
  obtain ⟨d3, v3⟩ := o3
  rw [octOp_octVec, octOp_octVec, octOp_octVec, T_sum_sum_sum]
  by_cases hs : (d1 : C) + d2 + d3 = 0
  · simp only [T_oct3_of_sum_zero hs]
    rw [← sum_octH3 hs v1 v2 v3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w1 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w2 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w3 _ => ?_
    ring
  · simp only [T_oct3_eq_zero hs, mul_zero, Finset.sum_const_zero]

theorem T_octDop3 (o1 o2 o3 : OctIdx) :
    T (octDop (octVec o1)) (octDop (octVec o2)) (octDop (octVec o3)) =
      T (octVec o1) (octVec o2) (octVec o3) := by
  classical
  obtain ⟨d1, v1⟩ := o1
  obtain ⟨d2, v2⟩ := o2
  obtain ⟨d3, v3⟩ := o3
  rw [octOp_octVec, octOp_octVec, octOp_octVec, T_sum_sum_sum,
    sum_octD3 v1 v2 v3 fun w1 w2 w3 => T (octVec ⟨d1, w1⟩) (octVec ⟨d2, w2⟩) (octVec ⟨d3, w3⟩)]
  by_cases hs : (d1 : C) + d2 + d3 = 0
  · obtain ⟨-, -, -, -, hqa, -, -⟩ := lagrangian_facts hs
    have hD := congrFun (signOp_lagrangianFun (ob d1 d2 d3) (oK d1 d2 d3) (oa₀ d1 d2 d3)
      (Octad.tripleQuad (ow d1) (ow d2) (ow d3)) (fun v hv => by
        have h0 := hqa (v - oa₀ d1 d2 d3) hv
        rwa [add_sub_cancel] at h0)) (tv v1 v2 v3)
    rw [signOp, tq_tv, sgn_add, sgn_add] at hD
    rw [T_oct3_of_sum_zero hs]
    linear_combination (sgn (θ d2 d1)) * hD
  · rw [T_oct3_eq_zero hs, mul_zero, mul_zero, mul_zero]

end OctadInv

open OctadInv

theorem triality_Griess_three_octad_invariance :
    (∀ (d : OctadWord) (v : Octad.EvenQuot (octSupp d)),
      octHop (octVec ⟨d, v⟩) = ∑ w, octH d v w • octVec ⟨d, w⟩ ∧
        octDop (octVec ⟨d, v⟩) = ∑ w, octD d v w • octVec ⟨d, w⟩) ∧
    (∀ u ∈ octSpan, octHop u ∈ octSpan ∧ octDop u ∈ octSpan ∧ tauB u = octDop (octHop u)) ∧
    (∀ u ∈ octSpan, ∀ v ∈ octSpan, ∀ w ∈ octSpan,
      T (octHop u) (octHop v) (octHop w) = T u v w ∧
        T (octDop u) (octDop v) (octDop w) = T u v w) ∧
    (∀ u ∈ octSpan, ∀ v ∈ octSpan, ∀ w ∈ octSpan,
      T (tauB u) (tauB v) (tauB w) = T u v w ∧
        T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w) := by
  have hH : ∀ u ∈ octSpan, ∀ v ∈ octSpan, ∀ w ∈ octSpan,
      T (octHop u) (octHop v) (octHop w) = T u v w := by
    intro u hu v hv w hw
    refine T_comp_eq_of_span octHop ?_ hu hv hw
    rintro _ ⟨o1, rfl⟩ _ ⟨o2, rfl⟩ _ ⟨o3, rfl⟩
    exact T_octHop3 o1 o2 o3
  have hD : ∀ u ∈ octSpan, ∀ v ∈ octSpan, ∀ w ∈ octSpan,
      T (octDop u) (octDop v) (octDop w) = T u v w := by
    intro u hu v hv w hw
    refine T_comp_eq_of_span octDop ?_ hu hv hw
    rintro _ ⟨o1, rfl⟩ _ ⟨o2, rfl⟩ _ ⟨o3, rfl⟩
    exact T_octDop3 o1 o2 o3
  have hτ : ∀ u ∈ octSpan, ∀ v ∈ octSpan, ∀ w ∈ octSpan,
      T (tauB u) (tauB v) (tauB w) = T u v w := by
    intro u hu v hv w hw
    rw [tauB_eq_octDop_octHop hu, tauB_eq_octDop_octHop hv, tauB_eq_octDop_octHop hw,
      hD _ (octOp_mem_octSpan _ hu) _ (octOp_mem_octSpan _ hv) _ (octOp_mem_octSpan _ hw),
      hH u hu v hv w hw]
  exact ⟨fun d v => ⟨octOp_octVec _ d v, octOp_octVec _ d v⟩,
    fun u hu => ⟨octOp_mem_octSpan _ hu, octOp_mem_octSpan _ hu, tauB_eq_octDop_octHop hu⟩,
    fun u hu v hv w hw => ⟨hH u hu v hv w hw, hD u hu v hv w hw⟩,
    fun u hu v hv w hw => ⟨hτ u hu v hv w hw,
      T_tauB_symm_of_tauB (fun _ h => tauB_symm_mem_octSpan h)
        (fun _ h => tauB_symm_mem_octSpan h) (fun _ h => tauB_symm_mem_octSpan h) hτ hu hv hw⟩⟩

end VOA.Moonshine.MonsterGriess
