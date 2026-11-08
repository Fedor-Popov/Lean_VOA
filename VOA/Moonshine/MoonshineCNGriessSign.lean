/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGriessShortClasses
import VOA.Moonshine.MonsterGriess.LatticeQuadratic
import VOA.Moonshine.ExtraspecialModule

/-!
# The sign map of the Griess dictionary, and the untwisted dictionary without hypotheses

The untwisted half of the Griess dictionary (`MoonshineCNGriessUntwisted`) needs phases
`ζ : ShortIdx → ℂ` with `ShortSignDictionary ζ`.  This file constructs one.

**The construction.**  On `V = C × Cocode` (Axiom's coordinates of `Λ/2Λ`, `phi0Equiv`) there are
two `ZMod 2`-bilinear forms:

* `E(p, q)` — the exponent of our lattice cocycle: `ε(α, β) = (−1)^{E(p,q)}` whenever `α, β` are
  vectors of our Leech lattice in the classes `phi0 p`, `phi0 q` (`latticeCocycle_eq_coc`, read
  through `leechEquiv`);
* `τ(p, q) = pair(q.a, p.δ)` — Axiom's structure constant of `SpaceX · SpaceX`.

Both have commutator `⟨α, β⟩ mod 2`: for `E` this is the commutator property of the cocycle, for `τ`
it is Axiom's `bL_phi0` (the polar form of `qL` in `phi0`-coordinates).  So `B = E + τ` is
symmetric, and every symmetric `ZMod 2`-bilinear form on a finite-dimensional space has a
`ℂ`-valued refinement `Z(x + y) = Z(x) Z(y) (−1)^{B(x,y)}` (`exists_sign_refinement`, built on a
basis with factors `i^{B(bᵢ,bᵢ)}`).  The phases `ζ_c = Z(c)` satisfy the product conditions of
`ShortSignDictionary` directly, and the norm condition because short coordinates are isotropic
(`pair_eq_zero_of_isShortCoord`).

## Main results
* ⭐ `exists_sign_refinement` — sign refinements of symmetric forms over `ZMod 2`.
* `latRedLin` — `V → (ZMod 2)^{rank}`, Axiom's coordinates to the reduction of our lattice mod 2;
  `latRedLin_shortIdx` (`= red α_c` on short coordinates).
* `signForm` (`= E + τ`), ⭐ `signForm_symm`.
* `griessShortSign : ShortIdx → ℂ`, ⭐ `shortSignDictionary_griessShortSign`.
* ⭐ `untwistedGriessNat_gmul`, ⭐ `untwistedGriessNat_form` — the untwisted half of the Griess
  dictionary in `V♮`, with no hypothesis.
* `card_shortIdx` — `|ShortIdx| = 98280`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.GriessDictionary

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.AutMonster
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin
  VOA.Moonshine.MonsterGriess.SpinLattice
open VOA.Moonshine.MonsterGriess.LeechMatch (leechEquiv classOf_of_mem leechEquiv_dotProduct)
open Matrix

/-! ## §1  Sign refinements of symmetric forms over `ZMod 2` -/

theorem sgn_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    Extraspecial.sgn (∑ i ∈ s, f i) = ∏ i ∈ s, Extraspecial.sgn (f i) := by
  classical
  refine Finset.induction_on s (by simp [Extraspecial.sgn_zero]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, Extraspecial.sgn_add, ih]

theorem sgn_injective : Function.Injective Extraspecial.sgn := by
  intro a b h
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · rw [Extraspecial.sgn_zero, Extraspecial.sgn_one] at h; norm_num at h
  · rw [Extraspecial.sgn_zero, Extraspecial.sgn_one] at h; norm_num at h
  · rfl

/-- Axiom's rational sign `sgn : ZMod 2 → ℚ`, read in `ℂ`, is the sign character. -/
theorem ratSgn_cast (t : ZMod 2) : ((MonsterGriess.sgn t : ℚ) : ℂ) = Extraspecial.sgn t := by
  rcases zmod_two_cases t with rfl | rfl
  · simp [MonsterGriess.sgn, Extraspecial.sgn_zero]
  · simp [MonsterGriess.sgn, Extraspecial.sgn_one]

/-- A double sum over `Fin n` splits into its diagonal and its symmetrised upper triangle. -/
theorem sum_sum_eq_diag_add_upper {n : ℕ} {R : Type*} [AddCommMonoid R] (f : Fin n → Fin n → R) :
    ∑ i, ∑ j, f i j = ∑ i, f i i + ∑ i, ∑ j, if i < j then f i j + f j i else 0 := by
  have h1 : ∀ i j, f i j = (if i < j then f i j else 0) + (if i = j then f i j else 0) +
      (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h, if_neg h.ne, if_neg (not_lt_of_gt h), add_zero, add_zero]
    · rw [if_neg (lt_irrefl _), if_pos rfl, zero_add, add_zero]
    · rw [if_neg (not_lt_of_gt h), if_neg h.ne', if_pos h, zero_add, zero_add]
  have h2 : ∑ i, ∑ j, f i j = ∑ i, ∑ j, ((if i < j then f i j else 0) +
      (if i = j then f i j else 0) + (if j < i then f i j else 0)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
  have h3 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f j i else 0) :=
    Finset.sum_comm
  have h4 : ∑ i, ∑ j, (if i = j then f i j else 0) = ∑ i, f i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have h5 : ∑ i, ∑ j, (if i < j then f i j + f j i else 0) =
      ∑ i, ∑ j, (if i < j then f i j else 0) + ∑ i, ∑ j, (if i < j then f j i else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [h2]
  simp only [Finset.sum_add_distrib]
  rw [h3, h4, h5]
  abel

/-- The phase factor of one coordinate: with `z² = (−1)^t`,
`z^{[a+a'=1]} = z^{[a=1]} z^{[a'=1]} (−1)^{a a' t}`. -/
theorem coordPhase_mul (z : ℂ) (t : ZMod 2) (hz : z * z = Extraspecial.sgn t) (a a' : ZMod 2) :
    (if a + a' = 1 then z else 1) =
      (if a = 1 then z else 1) * (if a' = 1 then z else 1) * Extraspecial.sgn (a * a' * t) := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases a' with rfl | rfl
  · simp [Extraspecial.sgn_zero]
  · simp [Extraspecial.sgn_zero]
  · simp [Extraspecial.sgn_zero]
  · have h11 : (1 : ZMod 2) + 1 = 0 := rfl
    rw [h11, if_neg zero_ne_one, if_pos rfl, one_mul, one_mul, hz,
      Extraspecial.sgn_mul_self]

/-- ⭐ **Sign refinements exist.**  Every symmetric `ZMod 2`-bilinear form `B` on a
finite-dimensional `ZMod 2`-space has a refinement `Z : V → ℂ` with `Z 0 = 1` and
`Z(x + y) = Z(x) Z(y) (−1)^{B(x,y)}`.  (In a basis `bᵢ`:
`Z(x) = ∏ᵢ (i^{B(bᵢ,bᵢ)})^{xᵢ} · (−1)^{Σ_{i<j} xᵢxⱼB(bᵢ,bⱼ)}`.) -/
theorem exists_sign_refinement {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ x y, B x y = B y x) :
    ∃ Z : V → ℂ, Z 0 = 1 ∧ ∀ x y, Z (x + y) = Z x * Z y * Extraspecial.sgn (B x y) := by
  classical
  let b := Module.finBasis (ZMod 2) V
  let c : V → Fin (Module.finrank (ZMod 2) V) → ZMod 2 := fun x i => b.repr x i
  let M : Fin (Module.finrank (ZMod 2) V) → Fin (Module.finrank (ZMod 2) V) → ZMod 2 :=
    fun i j => B (b i) (b j)
  have hM : ∀ i j, M i j = M j i := fun i j => hB _ _
  let z : Fin (Module.finrank (ZMod 2) V) → ℂ := fun i => if M i i = 0 then 1 else Complex.I
  have hz : ∀ i, z i * z i = Extraspecial.sgn (M i i) := by
    intro i
    simp only [z]
    rcases zmod_two_cases (M i i) with h | h <;> rw [h]
    · simp [Extraspecial.sgn_zero]
    · simp [Extraspecial.sgn_one]
  let q : V → ZMod 2 := fun x => ∑ i, ∑ j, if i < j then c x i * c x j * M i j else 0
  let w : V → ℂ := fun x => ∏ i, if c x i = 1 then z i else 1
  refine ⟨fun x => w x * Extraspecial.sgn (q x), ?_, ?_⟩
  · simp [w, q, c, Extraspecial.sgn_zero]
  · intro x y
    have hc : ∀ i, c (x + y) i = c x i + c y i := fun i => by simp [c]
    have hBxy : B x y = ∑ i, ∑ j, c x i * c y j * M i j := by
      conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_comm.trans ?_
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [c, M]
      ring
    have hsplit : ∑ i, ∑ j, c x i * c y j * M i j = ∑ i, c x i * c y i * M i i +
        ∑ i, ∑ j, (if i < j then c x i * c y j * M i j + c x j * c y i * M j i else 0) :=
      sum_sum_eq_diag_add_upper (fun i j => c x i * c y j * M i j)
    have hupper : (∑ i, ∑ j, (if i < j then c x i * c y j * M i j + c x j * c y i * M j i
        else 0)) = ∑ i, ∑ j, (if i < j then (c x i * c y j + c y i * c x j) * M i j else 0) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · rw [hM j i]; ring
      · rfl
    have hq : q (x + y) = q x + q y +
        ∑ i, ∑ j, (if i < j then (c x i * c y j + c y i * c x j) * M i j else 0) := by
      simp only [q, hc]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · ring
      · simp
    have hw : w (x + y) = w x * w y * Extraspecial.sgn (∑ i, c x i * c y i * M i i) := by
      simp only [w, hc]
      rw [sgn_finset_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact coordPhase_mul (z i) (M i i) (hz i) (c x i) (c y i)
    change w (x + y) * Extraspecial.sgn (q (x + y))
      = w x * Extraspecial.sgn (q x) * (w y * Extraspecial.sgn (q y)) * Extraspecial.sgn (B x y)
    rw [hw, hq, hBxy, hsplit, hupper]
    simp only [Extraspecial.sgn_add]
    ring

/-! ## §2  The cocycle of our lattice in Axiom's coordinates -/

/-- `Λ → (ZMod 2)^{rank}` on Axiom's integer vectors: `u ↦ red(leechEquiv⁻¹ u)`. -/
noncomputable def axiomRedLin :
    ↥(codeLatticeSubgroup MonsterGriess.Code.allOnes_mem_C) →ₗ[ℤ] (Fin leech.bRank → ZMod 2) :=
  (red leech).toIntLinearMap ∘ₗ (leechEquiv.symm.toIntLinearEquiv).toLinearMap

/-- The reduction of our lattice mod 2, on Axiom's `Λ/2Λ`. -/
noncomputable def axiomRed : SpinLattice.L2 →ₗ[ℤ] (Fin leech.bRank → ZMod 2) :=
  Submodule.liftQ _ axiomRedLin (by
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply, map_smul]
    ext i
    simp only [Pi.smul_apply, Pi.zero_apply, zsmul_eq_mul]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul])

theorem axiomRed_mk (u : ↥(codeLatticeSubgroup MonsterGriess.Code.allOnes_mem_C)) :
    axiomRed (Submodule.Quotient.mk u) = red leech (leechEquiv.symm u) := rfl

/-- Axiom's coordinates `C × Cocode` to the reduction mod 2 of our Leech lattice
(`(ZMod 2)^{rank}` in the canonical basis): `p ↦ red(α)` for any `α` in the class `phi0 p`. -/
noncomputable def latRedLin :
    (MonsterGriess.Code.C × Cocode) →ₗ[ZMod 2] (Fin leech.bRank → ZMod 2) :=
  AddMonoidHom.toZModLinearMap 2
    ((axiomRed : SpinLattice.L2 →ₗ[ℤ] _).toAddMonoidHom.comp
      (phi0Lin : (MonsterGriess.Code.C × Cocode) →ₗ[ZMod 2] SpinLattice.L2).toAddMonoidHom)

theorem latRedLin_apply (p : MonsterGriess.Code.C × Cocode) :
    latRedLin p = axiomRed (phi0 p) := rfl

/-- On a short coordinate, `latRedLin` is the reduction of the minimal vector `α_c`. -/
theorem latRedLin_shortIdx (c : ShortIdx) : latRedLin c.1 = red leech (shortVec c) := by
  rw [latRedLin_apply, ← classOf_uvec, classOf_of_mem (uvec_mem_minVecs c).1]
  rfl

/-- `hInt` of two Axiom vectors is our form of their preimages. -/
theorem hInt_leechEquiv (x y : leech.carrier) :
    hInt (leechEquiv x : Fin 24 → ℤ) (leechEquiv y : Fin 24 → ℤ) = leech.form x y := by
  have h := leechEquiv_dotProduct x y
  unfold hInt
  change (leechEquiv x : Fin 24 → ℤ) ⬝ᵥ (leechEquiv y : Fin 24 → ℤ) / 8 = _
  rw [h]
  omega

/-- The exponent `E(p,q) = red α ⬝ (cocMat · red β)` of our cocycle in Axiom's coordinates. -/
noncomputable def cocycleExp (p q : MonsterGriess.Code.C × Cocode) : ZMod 2 :=
  latRedLin p ⬝ᵥ (cocMat leech *ᵥ latRedLin q)

theorem latticeCocycle_shortVec (d e : ShortIdx) :
    latticeCocycle leech (shortVec d) (shortVec e) = Extraspecial.sgn (cocycleExp d.1 e.1) := by
  rw [latticeCocycle_eq_coc, Extraspecial.coc, cocycleExp, latRedLin_shortIdx,
    latRedLin_shortIdx]

/-- **Both commutators are the lattice form mod 2**: `E(p,q) + E(q,p) = τ(p,q) + τ(q,p)`. -/
theorem cocycleExp_add_swap (p q : MonsterGriess.Code.C × Cocode) :
    cocycleExp p q + cocycleExp q p = pair q.1 p.2 + pair p.1 q.2 := by
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (phi0 p)
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (phi0 q)
  set α := leechEquiv.symm u
  set β := leechEquiv.symm v
  have hp : latRedLin p = red leech α := by rw [latRedLin_apply, ← hu]; rfl
  have hq : latRedLin q = red leech β := by rw [latRedLin_apply, ← hv]; rfl
  have hform : ((leech.form α β : ℤ) : ZMod 2) = pair q.1 p.2 + pair p.1 q.2 := by
    have h := bL_phi0 p.1 q.1 p.2 q.2
    rw [Prod.mk.eta, Prod.mk.eta, ← hu, ← hv, polarBilin_codeQuadForm_mk] at h
    rw [add_comm, ← h]
    have hu' : (u : Fin 24 → ℤ) = (leechEquiv α : Fin 24 → ℤ) := by
      rw [AddEquiv.apply_symm_apply]
    have hv' : (v : Fin 24 → ℤ) = (leechEquiv β : Fin 24 → ℤ) := by
      rw [AddEquiv.apply_symm_apply]
    rw [hu', hv', hInt_leechEquiv]
  have hE : Extraspecial.sgn (cocycleExp p q + cocycleExp q p)
      = Extraspecial.sgn ((leech.form α β : ℤ) : ZMod 2) := by
    have h1 := latticeCocycle_comm leech leech_even α β
    rw [latticeCocycle_eq_coc, latticeCocycle_eq_coc, Extraspecial.coc, Extraspecial.coc,
      Extraspecial.neg_one_zpow_eq_sgn, ← hp, ← hq] at h1
    rw [Extraspecial.sgn_add, cocycleExp, cocycleExp]
    exact h1
  rw [sgn_injective hE, hform]

/-- The symmetric form `B = E + τ` on `C × Cocode`. -/
noncomputable def signForm :
    (MonsterGriess.Code.C × Cocode) →ₗ[ZMod 2] (MonsterGriess.Code.C × Cocode) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun p q => cocycleExp p q + pair q.1 p.2)
    (fun p p' q => by
      simp only [cocycleExp, map_add, add_dotProduct, Prod.snd_add]
      ring)
    (fun a p q => by
      simp only [cocycleExp, map_smul, smul_dotProduct, Prod.smul_snd, smul_eq_mul]
      ring)
    (fun p q q' => by
      simp only [cocycleExp, map_add, mulVec_add, dotProduct_add, Prod.fst_add, pair_add_left]
      ring)
    (fun a p q => by
      simp only [cocycleExp, map_smul, mulVec_smul, dotProduct_smul, Prod.smul_fst,
        pair_smul_left, smul_eq_mul]
      ring)

theorem signForm_apply (p q : MonsterGriess.Code.C × Cocode) :
    signForm p q = cocycleExp p q + pair q.1 p.2 := rfl

/-- ⭐ **`B = E + τ` is symmetric.** -/
theorem signForm_symm (p q : MonsterGriess.Code.C × Cocode) : signForm p q = signForm q p := by
  rw [signForm_apply, signForm_apply]
  have h := cocycleExp_add_swap p q
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination h + (pair q.1 p.2 - cocycleExp q p) * h2

/-! ## §3  The phases -/

/-- A sign refinement of `B = E + τ` on `C × Cocode`. -/
noncomputable def signRefinement : MonsterGriess.Code.C × Cocode → ℂ :=
  (exists_sign_refinement signForm signForm_symm).choose

theorem signRefinement_zero : signRefinement 0 = 1 :=
  (exists_sign_refinement signForm signForm_symm).choose_spec.1

theorem signRefinement_add (p q : MonsterGriess.Code.C × Cocode) :
    signRefinement (p + q) = signRefinement p * signRefinement q * Extraspecial.sgn (signForm p q) :=
  (exists_sign_refinement signForm signForm_symm).choose_spec.2 p q

/-- **The sign map of the Griess dictionary**: `ζ_c = Z(c)` for the sign refinement `Z` of
`E + τ`. -/
noncomputable def griessShortSign (c : ShortIdx) : ℂ := signRefinement c.1

theorem griessShortSign_sq (c : ShortIdx) :
    griessShortSign c ^ 2 * latticeCocycle leech (shortVec c) (shortVec c) = 1 := by
  have h := signRefinement_add c.1 c.1
  have h0 : c.1 + c.1 = 0 := by
    rw [← two_smul (ZMod 2) c.1, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rw [h0, signRefinement_zero, signForm_apply, Extraspecial.sgn_add,
    pair_eq_zero_of_isShortCoord c.2, Extraspecial.sgn_zero, mul_one] at h
  rw [latticeCocycle_shortVec, griessShortSign, sq]
  exact h.symm

theorem griessShortSign_sign (d e c : ShortIdx) (h : c.1 = d.1 + e.1) :
    (MonsterGriess.sgn (pair e.1.1 d.1.2) : ℂ) * griessShortSign c
      = griessShortSign d * griessShortSign e * latticeCocycle leech (shortVec d) (shortVec e) := by
  rw [griessShortSign, griessShortSign, griessShortSign, h, signRefinement_add, signForm_apply,
    ratSgn_cast, latticeCocycle_shortVec, Extraspecial.sgn_add]
  have hs := Extraspecial.sgn_mul_self (pair e.1.1 d.1.2)
  linear_combination
    (signRefinement d.1 * signRefinement e.1 * Extraspecial.sgn (cocycleExp d.1 e.1)) * hs

/-- ⭐ **The sign dictionary holds for `griessShortSign`**, with no hypothesis. -/
theorem shortSignDictionary_griessShortSign : ShortSignDictionary griessShortSign :=
  ShortSignDictionary.of_phi0 phi0_add phi0_injective griessShortSign_sq
    (fun d e c h _ => griessShortSign_sign d e c h)
    (fun d e c h _ => by
      rw [latticeCocycle_neg_right]
      exact griessShortSign_sign d e c h)

/-! ## §4  The untwisted dictionary, unconditionally -/

/-- ⭐ **The untwisted Griess dictionary is multiplicative** (no hypothesis): for `u, v ∈ SpaceB`
with zero `SpaceW` part, the dictionary with phases `griessShortSign` carries Axiom's product
`gmul u v` to the Griess product `u₍₁₎v` of `VnatVOA`. -/
theorem untwistedGriessNat_gmul {u v : SpaceB} (hu : u.2.2 = 0) (hv : v.2.2 = 0) :
    untwistedDictNat griessShortSign (gmul u v)
      = VnatVOA.griessMul (untwistedDictNat griessShortSign u)
          (untwistedDictNat griessShortSign v) :=
  untwistedDictNat_gmul shortSignDictionary_griessShortSign hu hv

/-- ⭐ **The untwisted Griess dictionary is an isometry up to `2`** (no hypothesis):
`natForm (Φu) (Φv) = 2·bform u v` for `u, v` with zero `SpaceW` part. -/
theorem untwistedGriessNat_form {u v : SpaceB} (hu : u.2.2 = 0) (hv : v.2.2 = 0) :
    SimpleNat.natForm (untwistedDictNat griessShortSign u : Vnat)
        (untwistedDictNat griessShortSign v : Vnat) = 2 * (bform u v : ℂ) :=
  untwistedDictNat_form shortSignDictionary_griessShortSign hu hv

/-- `|ShortIdx| = 98280` (from bijectivity of `phi0`). -/
theorem card_shortIdx : Nat.card ShortIdx = 98280 :=
  LeechMatch.card_shortIdx_of_bijective phi0_bijective

end VOA.Moonshine.GriessDictionary
