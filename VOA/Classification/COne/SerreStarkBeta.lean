/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkDrazin
import VOA.Classification.COne.SerreStarkBoundedEigen

/-!
# Serre–Stark S5-4b: the operator algebra of a class-form space

For a class-form space `V = classSpace N r ψ t` (`24 ∣ N`, `t` squarefree, `t ∣ N`, `r ∣ N`):

* `ClassSetup.U p` (`p ∣ N` prime): `U(p²)` on `V`; they commute (`U_comm`);
* `ClassSetup.coeffL n`: the `n`-th coefficient as a linear functional on `V`;
  `coeffL_U_pow`: `a_{U^k g}(n) = a_g(p^{2k} n)`;
* `eq_zero_of_A_eq_zero`: a class form whose coefficients `A(S) = a(t S²)` vanish at all
  `N`-smooth `S` is zero.
-/

open Complex Polynomial
open scoped UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-- The data of a class-form space. -/
structure ClassSetup where
  N : ℕ
  r : ℕ
  t : ℕ
  ψ : DirichletCharacter ℂ r
  hN : 0 < N
  h24 : 24 ∣ N
  hrN : r ∣ N
  ht : Squarefree t
  htN : t ∣ N

namespace ClassSetup

variable (S : ClassSetup)

/-- The space of class forms. -/
abbrev V : Submodule ℂ (ℍ → ℂ) := classSpace S.N S.r S.ψ S.t

theorem h4 : 4 ∣ S.N := (show 4 ∣ 24 by norm_num).trans S.h24

instance : NeZero S.N := ⟨S.hN.ne'⟩

instance : FiniteDimensional ℂ S.V := finiteDimensional_classSpace S.h4 S.ψ S.t

/-- The primes dividing `N`. -/
abbrev ι : Type := {p // p ∈ S.N.primeFactors}

theorem prime (p : S.ι) : p.1.Prime := Nat.prime_of_mem_primeFactors p.2

theorem dvd (p : S.ι) : p.1 ∣ S.N := Nat.dvd_of_mem_primeFactors p.2

/-- `U(p²)` on class forms. -/
def U (p : S.ι) : Module.End ℂ S.V :=
  haveI : Fact p.1.Prime := ⟨S.prime p⟩
  upEnd S.ψ S.hN S.h24 (S.dvd p) S.ht

/-- `ψ(p)`. -/
def ψp (p : S.ι) : ℂ := S.ψ (p.1 : ZMod S.r)

/-- The `n`-th coefficient, as a linear functional on class forms. -/
def coeffL (n : ℕ) : S.V →ₗ[ℂ] ℂ :=
  (LinearMap.proj (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))) ∘ₗ thetaTypeCoeffMap S.N (n + 1) ∘ₗ
    Submodule.inclusion (classSpace_le S.ψ S.t)

theorem coeffL_apply (n : ℕ) (g : S.V) :
    S.coeffL n g = (UpperHalfPlane.qExpansion 1 (g : ℍ → ℂ)).coeff n := rfl

theorem coeffL_eq {g : S.V} {f : ℂ → ℂ} (hfg : restrictUpper f = g) (n : ℕ) :
    S.coeffL n g = thetaTypeCoeff f n := by
  rw [coeffL_apply, ← hfg]; rfl

/-- Elements of `V` are determined by their coefficients. -/
theorem ext_coeffL {g h : S.V} (H : ∀ n, S.coeffL n g = S.coeffL n h) : g = h := by
  obtain ⟨f, hf, hfg⟩ := g.2
  obtain ⟨f', hf', hfh⟩ := h.2
  apply Subtype.ext
  funext τ
  rw [← hfg, ← hfh, restrictUpper_apply, restrictUpper_apply]
  have h1 := hf.1.hasSum_coeff τ.2
  have h2 := hf'.1.hasSum_coeff τ.2
  have hc : ∀ n, thetaTypeCoeff f n = thetaTypeCoeff f' n := fun n => by
    rw [← S.coeffL_eq hfg, ← S.coeffL_eq hfh]; exact H n
  simp_rw [hc] at h1
  exact h1.unique h2

theorem U_apply_coe (p : S.ι) {g : S.V} {f : ℂ → ℂ} (hfg : restrictUpper f = g) :
    ((S.U p g : S.V) : ℍ → ℂ) = restrictUpper (upOp p.1 f) := by
  haveI : Fact p.1.Prime := ⟨S.prime p⟩
  simp only [U, upEnd, LinearMap.restrict_apply]
  rw [← hfg]
  exact upH_restrictUpper f

theorem coeffL_U (p : S.ι) (n : ℕ) (g : S.V) :
    S.coeffL n (S.U p g) = S.coeffL (p.1 ^ 2 * n) g := by
  haveI : Fact p.1.Prime := ⟨S.prime p⟩
  obtain ⟨f, hf, hfg⟩ := g.2
  rw [S.coeffL_eq (S.U_apply_coe p hfg).symm, S.coeffL_eq hfg]
  exact coeff_upOp S.hN S.h24 (S.dvd p) hf.1 n

theorem coeffL_U_pow (p : S.ι) (k n : ℕ) (g : S.V) :
    S.coeffL n ((S.U p ^ k) g) = S.coeffL (p.1 ^ (2 * k) * n) g := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, coeffL_U, ih]
    congr 1; ring_nf

theorem U_comm (p q : S.ι) : Commute (S.U p) (S.U q) := by
  refine LinearMap.ext fun g => S.ext_coeffL fun n => ?_
  simp only [Module.End.mul_apply, coeffL_U]
  congr 1; ring_nf

/-! ## Smooth parts -/

/-- `x = (∏_{p ∈ P} p^{v_p(x)}) · v` with `v` prime to every `p ∈ P`. -/
theorem exists_smooth_decomp {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {x : ℕ} (hx : x ≠ 0) :
    ∃ v, x = (∏ p ∈ P, p ^ x.factorization p) * v ∧ ∀ p ∈ P, ¬ p ∣ v := by
  classical
  set s := ∏ p ∈ P, p ^ x.factorization p with hs
  have hs0 : s ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hP p hp).ne_zero
  have hsx : s ∣ x := by
    rw [← Nat.factorization_le_iff_dvd hs0 hx]
    rw [hs, Nat.factorization_prod fun p hp => pow_ne_zero _ (hP p hp).ne_zero]
    intro q
    rw [Finsupp.finsetSum_apply]
    have e : ∀ p ∈ P, (p ^ x.factorization p).factorization q =
        if p = q then x.factorization q else 0 := by
      intro p hp
      rw [(hP p hp).factorization_pow, Finsupp.single_apply]
      split_ifs with h
      · rw [h]
      · rfl
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq']
    split_ifs <;> simp
  obtain ⟨v, hv⟩ := hsx
  refine ⟨v, hv, fun p hp hpv => ?_⟩
  have h1 : p ^ x.factorization p ∣ s := Finset.dvd_prod_of_mem _ hp
  have h2 : p ^ (x.factorization p + 1) ∣ x := by
    rw [pow_succ]; nth_rewrite 2 [hv]; exact mul_dvd_mul h1 hpv
  have := ((hP p hp).pow_dvd_iff_le_factorization hx).1 h2
  omega

/-- A class form whose coefficients `a(t S²)` vanish at every `N`-smooth `S` is zero. -/
theorem eq_zero_of_A_eq_zero {g : S.V}
    (h : ∀ k : S.ι → ℕ, S.coeffL (S.t * ∏ p, p.1 ^ (2 * k p)) g = 0) : g = 0 := by
  classical
  obtain ⟨f, hf, hfg⟩ := g.2
  have hpos : ∀ n, 0 < n → thetaTypeCoeff f n = 0 := by
    intro n hn
    by_contra hne
    obtain ⟨x, hx⟩ := hf.2.1 n hn hne
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx; omega
    obtain ⟨v, hxv, hv⟩ := exists_smooth_decomp (P := S.N.primeFactors)
      (fun p hp => Nat.prime_of_mem_primeFactors hp) hx0
    set s := ∏ p ∈ S.N.primeFactors, p ^ x.factorization p with hs
    have hvN : v.Coprime S.N := by
      refine Nat.coprime_of_dvd fun k hk hkv hkN => ?_
      exact hv k (Nat.mem_primeFactors.2 ⟨hk, hkN, S.hN.ne'⟩) hkv
    have ht0 : 0 < S.t := Nat.pos_of_ne_zero S.ht.ne_zero
    have hs0 : 0 < s := Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
    have hn' : n = S.t * s ^ 2 * v ^ 2 := by rw [hx, hxv]; ring
    have hA : thetaTypeCoeff f (S.t * s ^ 2) = 0 := by
      have := h (fun p => x.factorization p.1)
      rw [S.coeffL_eq hfg] at this
      have e : ∏ p : S.ι, p.1 ^ (2 * x.factorization p.1) = s ^ 2 := by
        rw [hs, ← Finset.prod_pow]
        rw [← Finset.prod_coe_sort S.N.primeFactors]
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [← pow_mul, mul_comm]
      rwa [e] at this
    apply hne
    rw [hn', hf.2.2 _ v (by positivity) hvN, hA, mul_zero]
  have hz := thetaType_eq_zero_of_coeff_pos S.hN S.h4 hf.1 hpos
  apply Subtype.ext
  funext τ
  rw [← hfg, restrictUpper_apply, hz τ τ.2]
  rfl

end ClassSetup

/-! ## A commutative product lemma for spans -/

section ProdSpan

variable {R : Type*} [CommRing R] [Algebra ℂ R] {κ ι' : Type*} [Inhabited κ]

/-- Products of elements of spans lie in the span of products. -/
theorem prod_mem_span_prod (s : Finset ι') (x : ι' → R) (y : ι' → κ → R)
    (hx : ∀ i ∈ s, x i ∈ Submodule.span ℂ (Set.range (y i))) :
    ∏ i ∈ s, x i ∈ Submodule.span ℂ {z | ∃ m : ι' → κ, z = ∏ i ∈ s, y i (m i)} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact Submodule.subset_span ⟨fun _ => default, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := hx a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have h3 := Submodule.mul_mem_mul h1 h2
    rw [Submodule.span_mul_span] at h3
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨u, ⟨c, rfl⟩, v, ⟨m, rfl⟩, rfl⟩
    refine ⟨Function.update m a c, ?_⟩
    rw [Finset.prod_insert ha, Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (by rintro rfl; exact ha hi)]

/-- A linear functional vanishing on a set vanishes on its span. -/
theorem eq_zero_of_mem_span {M : Type*} [AddCommGroup M] [Module ℂ M] (φ : M →ₗ[ℂ] ℂ)
    {T : Set M} (hT : ∀ z ∈ T, φ z = 0) {z : M} (hz : z ∈ Submodule.span ℂ T) : φ z = 0 := by
  have : Submodule.span ℂ T ≤ LinearMap.ker φ := Submodule.span_le.2 fun z hz => hT z hz
  exact this hz

end ProdSpan

namespace ClassSetup

variable (S : ClassSetup)

/-! ## The commutative operator algebra -/

/-- The algebra generated by the `U(p²)`, `p ∣ N`. -/
def opAlg : Subalgebra ℂ (Module.End ℂ S.V) := Algebra.adjoin ℂ (Set.range S.U)

theorem opAlg_comm {a b : Module.End ℂ S.V} (ha : a ∈ S.opAlg) (hb : b ∈ S.opAlg) :
    Commute a b := by
  have hU : ∀ x ∈ Set.range S.U, Commute x b := by
    rintro _ ⟨p, rfl⟩
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb ?_
    rintro _ ⟨q, rfl⟩
    exact S.U_comm p q
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha fun x hx => (hU x hx).symm).symm

instance opAlgCommRing : CommRing S.opAlg :=
  { S.opAlg.toRing with
    mul_comm := fun a b => Subtype.ext (S.opAlg_comm a.2 b.2).eq }

theorem U_mem (p : S.ι) : S.U p ∈ S.opAlg := Algebra.subset_adjoin ⟨p, rfl⟩

theorem aeval_mem (p : S.ι) (P : ℂ[X]) : aeval (S.U p) P ∈ S.opAlg :=
  (Algebra.adjoin_le (Set.singleton_subset_iff.2 (S.U_mem p)))
    (Polynomial.aeval_mem_adjoin_singleton ℂ (S.U p))

/-- The Drazin data of `U(p²)`. -/
def Dp (p : S.ι) : DrazinData (S.U p) := drazinData (S.U p)

theorem πK_mem (p : S.ι) : (S.Dp p).πK ∈ S.opAlg := S.aeval_mem p _
theorem πI_mem (p : S.ι) : (S.Dp p).πI ∈ S.opAlg := S.aeval_mem p _
theorem TD_mem (p : S.ι) : (S.Dp p).TD ∈ S.opAlg := S.aeval_mem p _

theorem eta_mem (p : S.ι) (m : ℤ) : (S.Dp p).eta (S.ψp p) p.1 m ∈ S.opAlg := by
  have hU := S.U_mem p
  have hK := S.πK_mem p
  have hI := S.πI_mem p
  have hD := S.TD_mem p
  unfold DrazinData.eta
  split_ifs
  · exact S.opAlg.smul_mem (S.opAlg.mul_mem (S.opAlg.mul_mem (S.opAlg.pow_mem hD _)
      (S.opAlg.sub_mem hU (S.opAlg.smul_mem S.opAlg.one_mem _))) hI) _
  · exact S.opAlg.add_mem hK (S.opAlg.smul_mem hD _)
  · exact S.opAlg.smul_mem (S.opAlg.mul_mem (S.opAlg.sub_mem (S.opAlg.pow_mem hU _)
      (S.opAlg.smul_mem (S.opAlg.pow_mem hU _) _)) hK) _

/-- `U(p²)` in the operator algebra. -/
def Ua (p : S.ι) : S.opAlg := ⟨S.U p, S.U_mem p⟩
/-- `πK` in the operator algebra. -/
def πKa (p : S.ι) : S.opAlg := ⟨(S.Dp p).πK, S.πK_mem p⟩
/-- `πI` in the operator algebra. -/
def πIa (p : S.ι) : S.opAlg := ⟨(S.Dp p).πI, S.πI_mem p⟩
/-- `TD` in the operator algebra. -/
def TDa (p : S.ι) : S.opAlg := ⟨(S.Dp p).TD, S.TD_mem p⟩
/-- `Η_p(m)` in the operator algebra. -/
def etaA (p : S.ι) (m : ℤ) : S.opAlg := ⟨(S.Dp p).eta (S.ψp p) p.1 m, S.eta_mem p m⟩

theorem coe_etaA (p : S.ι) (m : ℤ) :
    ((S.etaA p m : S.opAlg) : Module.End ℂ S.V) = (S.Dp p).eta (S.ψp p) p.1 m := rfl

/-- The Fricke expansion coefficients `β_g(m) = a_{∏_p Η_p(m_p) g}(t)`. -/
def beta (g : S.V) (m : S.ι → ℤ) : ℂ :=
  S.coeffL S.t (((∏ p, S.etaA p (m p) : S.opAlg) : Module.End ℂ S.V) g)

/-- The `G`-operators `E_p(0) = 1`, `E_p(j) = U^j − ψ(p) U^{j−1}`. -/
def Ea (p : S.ι) (j : ℕ) : S.opAlg :=
  if j = 0 then 1 else S.Ua p ^ j - S.ψp p • S.Ua p ^ (j - 1)

/-- The coefficients of `G_g = D_g · E`: `g_g(j) = a_{∏_p E_p(j_p) g}(t)`. -/
def gco (g : S.V) (j : S.ι → ℕ) : ℂ :=
  S.coeffL S.t (((∏ p, S.Ea p (j p) : S.opAlg) : Module.End ℂ S.V) g)

/-- The coefficients `A_g(k) = a_g(t ∏ p^{2k_p})`. -/
def Aco (g : S.V) (k : S.ι → ℕ) : ℂ := S.coeffL (S.t * ∏ p, p.1 ^ (2 * k p)) g

theorem coeffL_prod_U_pow (s : Finset S.ι) (k : S.ι → ℕ) (n : ℕ) (g : S.V) :
    S.coeffL n (((∏ p ∈ s, S.Ua p ^ k p : S.opAlg) : Module.End ℂ S.V) g) =
      S.coeffL (n * ∏ p ∈ s, p.1 ^ (2 * k p)) g := by
  classical
  induction s using Finset.induction_on generalizing g with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_comm (S.Ua a ^ k a),
      Subalgebra.coe_mul, Module.End.mul_apply, ih]
    have : ((S.Ua a ^ k a : S.opAlg) : Module.End ℂ S.V) = S.U a ^ k a := by
      rw [SubmonoidClass.coe_pow]; rfl
    rw [this, coeffL_U_pow]
    congr 1; ring_nf

theorem Aco_eq (g : S.V) (k : S.ι → ℕ) :
    S.Aco g k = S.coeffL S.t (((∏ p, S.Ua p ^ k p : S.opAlg) : Module.End ℂ S.V) g) := by
  rw [coeffL_prod_U_pow]; rfl

/-! ## Step 1: the growth bound forces `U(p²) = ψ(p)` on the invertible part -/

/-- The Fricke-expansion bound (output of the analytic part, route C step 3). -/
def BetaBound (g : S.V) : Prop :=
  ∃ C : ℝ, ∀ m : S.ι → ℤ, ‖S.beta g m‖ ≤ C * ∏ p, Real.sqrt p.1 ^ (m p)

/-- Vanishing of the Fricke expansion at non-integral frequencies. -/
def BetaIntegral (g : S.V) : Prop :=
  ∀ m : S.ι → ℤ, (∃ p : S.ι, (padicValNat p.1 S.N : ℤ) <
    padicValNat p.1 (4 * S.t * S.r ^ 2) - 2 * m p) → S.beta g m = 0

theorem coe_Ua_pow (p : S.ι) (k : ℕ) :
    ((S.Ua p ^ k : S.opAlg) : Module.End ℂ S.V) = S.U p ^ k := by
  rw [SubmonoidClass.coe_pow]; rfl

theorem Ua_pow_mem_span (p : S.ι) (k : ℕ) :
    S.Ua p ^ k ∈ Submodule.span ℂ (Set.range (S.etaA p)) := by
  have h := (S.Dp p).pow_mem_span_eta (S.ψp p) (S.prime p).ne_zero k
  set L : S.opAlg →ₗ[ℂ] Module.End ℂ S.V := S.opAlg.val.toLinearMap
  have hrange : Set.range ((S.Dp p).eta (S.ψp p) p.1) = L '' Set.range (S.etaA p) := by
    ext z; constructor
    · rintro ⟨m, rfl⟩; exact ⟨S.etaA p m, ⟨m, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩; exact ⟨m, rfl⟩
  rw [hrange, ← Submodule.map_span] at h
  obtain ⟨z, hz, hzL⟩ := h
  have : z = S.Ua p ^ k := by
    apply Subtype.ext
    rw [coe_Ua_pow]
    exact hzL
  rw [← this]; exact hz

/-- The functional `Z ↦ a_{Z v}(n)` on the operator algebra. -/
def evalL (n : ℕ) (v : S.V) : S.opAlg →ₗ[ℂ] ℂ :=
  S.coeffL n ∘ₗ LinearMap.applyₗ v ∘ₗ S.opAlg.val.toLinearMap

theorem evalL_apply (n : ℕ) (v : S.V) (Z : S.opAlg) :
    S.evalL n v Z = S.coeffL n ((Z : Module.End ℂ S.V) v) := rfl

/-- **Step 1.** Under the Fricke bound, `U(p²) πI = ψ(p) πI`. -/
theorem U_πI_eq (hB : ∀ g, S.BetaBound g) (p : S.ι) (x : S.V) :
    S.U p ((S.Dp p).πI x) = S.ψp p • (S.Dp p).πI x := by
  classical
  set D := S.Dp p with hD
  set w : S.V := (S.U p - S.ψp p • 1) (D.πI x) with hw
  suffices hw0 : w = 0 by
    rw [hw, LinearMap.sub_apply, sub_eq_zero] at hw0
    simpa using hw0
  have hp := S.prime p
  have hpR : (1 : ℝ) < p.1 := by exact_mod_cast hp.one_lt
  set sp := Real.sqrt p.1 with hsp_def
  have hsp : 0 < sp := Real.sqrt_pos.2 (by linarith)
  have hsp1 : 1 ≤ sp := by rw [hsp_def, Real.one_le_sqrt]; linarith
  have hsp2 : sp * sp = p.1 := Real.mul_self_sqrt (by linarith)
  set s' := Finset.univ.erase p with hs'
  have hcK : Commute (S.U p) D.πK := D.commute_πK (Commute.refl _)
  have hcI : Commute (S.U p) D.πI := D.commute_πI (Commute.refl _)
  have hwI : D.πI w = w := by
    have hc : Commute D.πI (S.U p - S.ψp p • 1) :=
      hcI.symm.sub_right (Commute.smul_right (Commute.one_right _) _)
    have key : D.πI * ((S.U p - S.ψp p • 1) * D.πI) = (S.U p - S.ψp p • 1) * D.πI := by
      rw [← mul_assoc, hc.eq, mul_assoc, D.πI_idem]
    have := congrArg (fun A : Module.End ℂ S.V => A x) key
    simpa only [Module.End.mul_apply, hw] using this
  -- Claim A
  have hA : ∀ (m' : S.ι → ℤ) (j : ℕ),
      S.evalL S.t ((S.U p ^ j) w) (∏ q ∈ s', S.etaA q (m' q)) = 0 := by
    intro m'
    set Pr : S.opAlg := ∏ q ∈ s', S.etaA q (m' q) with hPr
    set ℓ : S.V →ₗ[ℂ] ℂ := S.coeffL S.t ∘ₗ (Pr : Module.End ℂ S.V) with hℓ
    obtain ⟨C0, hC0⟩ := hB x
    set K' := ∏ q ∈ s', Real.sqrt q.1 ^ (m' q) with hK'
    -- the expansion coefficients along `p`
    have hβ : ∀ n : ℕ, 1 ≤ n →
        S.beta x (Function.update m' p n) = -((p.1 : ℂ) ^ n) * ℓ ((D.TD ^ (n + 1)) w) := by
      intro n hn
      obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le' hn
      rw [beta, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p),
        Function.update_self]
      have hrest : ∏ q ∈ Finset.univ.erase p, S.etaA q (Function.update m' p
          ((n' + 1 : ℕ) : ℤ) q) = Pr := by
        refine Finset.prod_congr rfl fun q hq => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
      rw [hrest, mul_comm, Subalgebra.coe_mul, Module.End.mul_apply]
      have he : ((S.etaA p ((n' + 1 : ℕ) : ℤ) : S.opAlg) : Module.End ℂ S.V) =
          -((p.1 : ℂ) ^ (n' + 1)) • (D.TD ^ (n' + 2) * (S.U p - S.ψp p • 1) * D.πI) := by
        change D.eta (S.ψp p) p.1 ((n' + 1 : ℕ) : ℤ) = _
        push_cast
        exact D.eta_pos (S.ψp p) p.1 n'
      rw [he, LinearMap.smul_apply, map_smul, map_smul, smul_eq_mul]
      congr 1
    -- the growth bound
    set c1 := ‖ℓ (D.TD w)‖
    refine fun j => growth_vanish (S.U p) D ℓ (ρ := sp) (σ := sp⁻¹) ?_ (by positivity)
      (inv_le_one_of_one_le₀ hsp1) (by rw [inv_mul_cancel₀ hsp.ne']) hwI
      (C := max (C0 * K' * sp) (c1 * sp)) ?_ j
    · intro c hc
      have := upEnd_eigenvalue_norm_sq_lt (p := p.1) (hpf := ⟨hp⟩) S.ψ S.hN S.h24 (S.dvd p)
        S.hrN S.ht hc
      rw [hsp_def, Real.lt_sqrt (norm_nonneg _)]
      exact this
    · intro m hm
      have hσ : ∀ k : ℕ, sp⁻¹ ^ k * sp ^ k = 1 := fun k => by
        rw [← mul_pow, inv_mul_cancel₀ hsp.ne', one_pow]
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · have : m = 1 := by omega
        subst this
        calc ‖ℓ ((D.TD ^ 1) w)‖ = c1 * sp * sp⁻¹ := by
              rw [pow_one, mul_assoc, mul_inv_cancel₀ hsp.ne', mul_one]
          _ ≤ max (C0 * K' * sp) (c1 * sp) * sp⁻¹ :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
          _ = max (C0 * K' * sp) (c1 * sp) * sp⁻¹ ^ 1 := by rw [pow_one]
      · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        have hn : 1 ≤ n := by omega
        have h1 := hβ n hn
        have h2 := hC0 (Function.update m' p n)
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p), Function.update_self]
          at h2
        have hrest : ∏ q ∈ Finset.univ.erase p, Real.sqrt q.1 ^ (Function.update m' p
            (n : ℤ) q) = K' := by
          refine Finset.prod_congr rfl fun q hq => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
        rw [hrest, zpow_natCast, h1, norm_mul, norm_neg, norm_pow, Complex.norm_natCast] at h2
        -- `p^n ‖ℓ(TD^{n+1} w)‖ ≤ C0 sp^n K'`
        have hpn : (p.1 : ℝ) ^ n = sp ^ n * sp ^ n := by rw [← mul_pow, hsp2]
        rw [hpn] at h2
        have hspn : 0 < sp ^ n := by positivity
        have h3 : ‖ℓ ((D.TD ^ (n + 1)) w)‖ ≤ C0 * K' * sp⁻¹ ^ n := by
          have h4 : sp ^ n * (sp ^ n * ‖ℓ ((D.TD ^ (n + 1)) w)‖) ≤
              sp ^ n * (C0 * K') := by nlinarith
          have h5 := le_of_mul_le_mul_left h4 hspn
          have h6 : ‖ℓ ((D.TD ^ (n + 1)) w)‖ = sp⁻¹ ^ n * (sp ^ n *
              ‖ℓ ((D.TD ^ (n + 1)) w)‖) := by
            rw [← mul_assoc, hσ, one_mul]
          rw [h6]
          calc sp⁻¹ ^ n * (sp ^ n * ‖ℓ ((D.TD ^ (n + 1)) w)‖) ≤ sp⁻¹ ^ n * (C0 * K') :=
                mul_le_mul_of_nonneg_left h5 (by positivity)
            _ = C0 * K' * sp⁻¹ ^ n := by ring
        calc ‖ℓ ((D.TD ^ (n + 1)) w)‖ ≤ C0 * K' * sp⁻¹ ^ n := h3
          _ = C0 * K' * sp * sp⁻¹ ^ (n + 1) := by
              rw [pow_succ]; field_simp
          _ ≤ max (C0 * K' * sp) (c1 * sp) * sp⁻¹ ^ (n + 1) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  -- Claim B: all `A`-coefficients of `w` vanish
  apply S.eq_zero_of_A_eq_zero
  intro k
  have e1 := S.Aco_eq w k
  rw [Aco] at e1
  rw [e1, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p), mul_comm,
    Subalgebra.coe_mul, Module.End.mul_apply, coe_Ua_pow]
  -- the functional `Z ↦ a_{Z U^{k_p} w}(t)` kills the span of the `Η`-products
  have hspan := prod_mem_span_prod s' (fun q => S.Ua q ^ k q) (S.etaA)
    (fun q _ => S.Ua_pow_mem_span q (k q))
  have := eq_zero_of_mem_span (S.evalL S.t ((S.U p ^ k p) w)) (T := {z | ∃ m' : S.ι → ℤ,
    z = ∏ q ∈ s', S.etaA q (m' q)}) (by rintro _ ⟨m', rfl⟩; exact hA m' (k p)) hspan
  rw [evalL_apply] at this
  exact this

/-! ## Step 2: the subset decomposition; `G` is supported in the level box -/

theorem U_πI_op (hB : ∀ g, S.BetaBound g) (p : S.ι) :
    S.U p * (S.Dp p).πI = S.ψp p • (S.Dp p).πI :=
  LinearMap.ext fun x => S.U_πI_eq hB p x

/-- `P_p = πI` (`p ∈ T`) or `πK` (`p ∉ T`). -/
def Pa (T : Finset S.ι) (p : S.ι) : S.opAlg := if p ∈ T then S.πIa p else S.πKa p

/-- `Π_T = ∏_{p ∈ T} πI_p ∏_{p ∉ T} πK_p`. -/
def PiS (T : Finset S.ι) : S.opAlg := ∏ p, S.Pa T p

theorem sum_PiS : ∑ T ∈ (Finset.univ : Finset S.ι).powerset, S.PiS T = 1 := by
  classical
  have h1 : ∀ p, S.πIa p + S.πKa p = 1 := fun p => by
    apply Subtype.ext
    change (S.Dp p).πI + (S.Dp p).πK = 1
    rw [add_comm]; exact (S.Dp p).sum'
  have : (∏ p : S.ι, (S.πIa p + S.πKa p)) = 1 := by simp [h1]
  rw [← this, Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [PiS]
  simp only [Pa]
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext p; simp
  · congr 1; ext p; simp

theorem coe_Ea_succ (p : S.ι) (n : ℕ) :
    ((S.Ea p (n + 1) : S.opAlg) : Module.End ℂ S.V) =
      S.U p ^ (n + 1) - S.ψp p • S.U p ^ n := by
  rw [Ea, if_neg (by omega), Subalgebra.coe_sub, Subalgebra.coe_smul, coe_Ua_pow, coe_Ua_pow,
    Nat.add_sub_cancel]

theorem coe_Ea_zero (p : S.ι) : ((S.Ea p 0 : S.opAlg) : Module.End ℂ S.V) = 1 := by
  rw [Ea, if_pos rfl]; rfl

/-- The per-prime identity `Η_p(−j) P_p = p^{−j} E_p(j) P_p`. -/
theorem etaA_neg_mul_Pa (hB : ∀ g, S.BetaBound g) (T : Finset S.ι) (p : S.ι) (j : ℕ) :
    S.etaA p (-(j : ℤ)) * S.Pa T p = ((p.1 : ℂ) ^ j)⁻¹ • (S.Ea p j * S.Pa T p) := by
  set D := S.Dp p with hD
  have hUI := S.U_πI_op hB p
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_smul, Subalgebra.coe_mul]
  have hP : ((S.Pa T p : S.opAlg) : Module.End ℂ S.V) = if p ∈ T then D.πI else D.πK := by
    unfold Pa; split_ifs <;> rfl
  rw [hP]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have he : ((S.etaA p (-((0 : ℕ) : ℤ)) : S.opAlg) : Module.End ℂ S.V) =
        D.πK + S.ψp p • D.TD := by
      rw [coe_etaA]
      simpa using D.eta_zero (S.ψp p) p.1
    rw [he, coe_Ea_zero, pow_zero, inv_one, one_smul, one_mul]
    split_ifs
    · rw [add_mul, D.KI', zero_add, smul_mul_assoc, D.TDI']
      -- `ψ TD = πI`
      have e1 : D.TD * (S.U p * D.πI) = D.πI := by rw [← mul_assoc, D.TDT', D.πI_idem]
      rw [hUI, mul_smul_comm, D.TDI'] at e1
      exact e1
    · rw [add_mul, D.πK_idem, smul_mul_assoc, D.TD_πK, smul_zero, add_zero]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
    have he : ((S.etaA p (-((n + 1 : ℕ) : ℤ)) : S.opAlg) : Module.End ℂ S.V) =
        ((p.1 : ℂ) ^ (n + 1))⁻¹ • ((S.U p ^ (n + 1) - S.ψp p • S.U p ^ n) * D.πK) := by
      rw [coe_etaA]
      have := D.eta_neg (S.ψp p) p.1 n
      push_cast
      exact this
    rw [he, coe_Ea_succ]
    split_ifs
    · rw [smul_mul_assoc, mul_assoc, D.KI', mul_zero, smul_zero]
      have : (S.U p ^ (n + 1) - S.ψp p • S.U p ^ n) * D.πI = 0 := by
        rw [sub_mul, pow_succ, mul_assoc, hUI, smul_mul_assoc, mul_smul_comm, sub_self]
      rw [this, smul_zero]
    · rw [smul_mul_assoc, mul_assoc, D.πK_idem]

theorem gco_PiS (hB : ∀ g, S.BetaBound g) (T : Finset S.ι) (g : S.V) (j : S.ι → ℕ) :
    S.gco (((S.PiS T : S.opAlg) : Module.End ℂ S.V) g) j =
      (∏ p, (p.1 : ℂ) ^ j p) * S.beta (((S.PiS T : S.opAlg) : Module.End ℂ S.V) g)
        (fun p => -(j p : ℤ)) := by
  have hprod : (∏ p, S.etaA p (-(j p : ℤ))) * S.PiS T =
      (∏ p, ((p.1 : ℂ) ^ j p)⁻¹) • ((∏ p, S.Ea p (j p)) * S.PiS T) := by
    rw [PiS, ← Finset.prod_mul_distrib]
    simp_rw [S.etaA_neg_mul_Pa hB T]
    simp_rw [Algebra.smul_def]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, map_prod]
  have hne : (∏ p : S.ι, (p.1 : ℂ) ^ j p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p _ => pow_ne_zero _ (Nat.cast_ne_zero.2 (S.prime p).ne_zero)
  rw [beta, ← Module.End.mul_apply, ← Subalgebra.coe_mul, hprod, Subalgebra.coe_smul,
    LinearMap.smul_apply, map_smul, Subalgebra.coe_mul, Module.End.mul_apply, smul_eq_mul,
    ← mul_assoc, Finset.prod_inv_distrib, mul_inv_cancel₀ hne, one_mul]
  rfl

theorem gco_add (g h : S.V) (j : S.ι → ℕ) : S.gco (g + h) j = S.gco g j + S.gco h j := by
  simp [gco, map_add]

theorem gco_sum {α : Type*} (s : Finset α) (g : α → S.V) (j : S.ι → ℕ) :
    S.gco (∑ a ∈ s, g a) j = ∑ a ∈ s, S.gco (g a) j := by
  simp [gco, map_sum]

/-- **Step 2.** Under the Fricke bound and integrality, `g_g(j) = 0` off the level box. -/
theorem gco_eq_zero_of_not_box (hB : ∀ g, S.BetaBound g) (hI : ∀ g, S.BetaIntegral g)
    (g : S.V) (j : S.ι → ℕ)
    (hj : ∃ p : S.ι, (padicValNat p.1 S.N : ℤ) < padicValNat p.1 (4 * S.t * S.r ^ 2) + 2 * j p) :
    S.gco g j = 0 := by
  have hg : g = ∑ T ∈ (Finset.univ : Finset S.ι).powerset,
      ((S.PiS T : S.opAlg) : Module.End ℂ S.V) g := by
    rw [← LinearMap.sum_apply, ← AddSubmonoidClass.coe_finsetSum, S.sum_PiS]; rfl
  rw [hg, gco_sum]
  refine Finset.sum_eq_zero fun T _ => ?_
  rw [S.gco_PiS hB T g j, hI _ (fun p => -(j p : ℤ)) ?_, mul_zero]
  obtain ⟨p, hp⟩ := hj
  refine ⟨p, ?_⟩
  simp only
  omega

/-! ## Step 3: the box hypothesis kills `G`, hence `A` -/

theorem Ea_mem_span (p : S.ι) (j : ℕ) :
    S.Ea p j ∈ Submodule.span ℂ (Set.range fun i : ℕ => if i ≤ j then S.Ua p ^ i else 0) := by
  have hmem : ∀ i ≤ j, S.Ua p ^ i ∈
      Submodule.span ℂ (Set.range fun i : ℕ => if i ≤ j then S.Ua p ^ i else 0) := by
    intro i hi
    exact Submodule.subset_span ⟨i, by simp [hi]⟩
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rw [Ea, if_pos rfl, ← pow_zero (S.Ua p)]
    exact hmem 0 le_rfl
  · rw [Ea, if_neg hj.ne']
    exact Submodule.sub_mem _ (hmem j le_rfl) (Submodule.smul_mem _ _ (hmem _ (by omega)))

theorem Ua_pow_eq_sum_Ea (p : S.ι) (k : ℕ) :
    S.Ua p ^ k = ∑ i ∈ Finset.range (k + 1), S.ψp p ^ (k - i) • S.Ea p i := by
  induction k with
  | zero => simp [Ea]
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_smul]
    have e : ∑ i ∈ Finset.range (k + 1), S.ψp p ^ (k + 1 - i) • S.Ea p i =
        S.ψp p • ∑ i ∈ Finset.range (k + 1), S.ψp p ^ (k - i) • S.Ea p i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [smul_smul, ← pow_succ']
      congr 2
      have := Finset.mem_range.1 hi
      omega
    rw [e, ← ih, Ea, if_neg (by omega), Nat.add_sub_cancel]
    abel

theorem Ua_pow_mem_span_Ea (p : S.ι) (k : ℕ) :
    S.Ua p ^ k ∈ Submodule.span ℂ (Set.range (S.Ea p)) := by
  rw [Ua_pow_eq_sum_Ea]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem gco_eq_zero_of_Aco (g : S.V) (j : S.ι → ℕ)
    (h : ∀ k : S.ι → ℕ, k ≤ j → S.Aco g k = 0) : S.gco g j = 0 := by
  classical
  have hspan := prod_mem_span_prod Finset.univ (fun p => S.Ea p (j p))
    (fun p (i : ℕ) => if i ≤ j p then S.Ua p ^ i else 0) (fun p _ => S.Ea_mem_span p (j p))
  refine eq_zero_of_mem_span (S.evalL S.t g) ?_ hspan
  rintro _ ⟨m, rfl⟩
  by_cases hm : m ≤ j
  · have e : (∏ i, if m i ≤ j i then S.Ua i ^ m i else 0) = ∏ i, S.Ua i ^ m i :=
      Finset.prod_congr rfl fun i _ => by rw [if_pos (hm i)]
    rw [e, evalL_apply, ← Aco_eq]
    exact h m hm
  · have : ∃ i, ¬ m i ≤ j i := by
      by_contra hc; push Not at hc; exact hm hc
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [if_neg hi]), map_zero]

theorem Aco_eq_zero_of_gco (g : S.V) (h : ∀ j, S.gco g j = 0) (k : S.ι → ℕ) :
    S.Aco g k = 0 := by
  classical
  have hspan := prod_mem_span_prod Finset.univ (fun p => S.Ua p ^ k p) S.Ea
    (fun p _ => S.Ua_pow_mem_span_Ea p (k p))
  rw [Aco_eq, ← evalL_apply]
  refine eq_zero_of_mem_span (S.evalL S.t g) ?_ hspan
  rintro _ ⟨m, rfl⟩
  exact h m

/-! ## The level box -/

/-- `k` lies in the level box: `4 t r² ∏ p^{2k_p} ∣ N`. -/
def InBoxK (k : S.ι → ℕ) : Prop := 4 * S.t * S.r ^ 2 * ∏ p, p.1 ^ (2 * k p) ∣ S.N

theorem inBoxK_mono {k j : S.ι → ℕ} (hkj : k ≤ j) (hj : S.InBoxK j) : S.InBoxK k := by
  refine Nat.dvd_trans (Nat.mul_dvd_mul_left _ ?_) hj
  exact Finset.prod_dvd_prod_of_dvd _ _ fun p _ => Nat.pow_dvd_pow _
    (Nat.mul_le_mul_left 2 (hkj p))

theorem exists_bad_of_not_inBoxK {j : S.ι → ℕ} (hj : ¬ S.InBoxK j) :
    ∃ p : S.ι, (padicValNat p.1 S.N : ℤ) < padicValNat p.1 (4 * S.t * S.r ^ 2) + 2 * j p := by
  classical
  by_contra hcon
  push Not at hcon
  apply hj
  have ht0 : S.t ≠ 0 := S.ht.ne_zero
  have hr0 : S.r ≠ 0 := fun h => by
    have := S.hrN; rw [h] at this; exact S.hN.ne' (Nat.eq_zero_of_zero_dvd this)
  have hP0 : (∏ p : S.ι, p.1 ^ (2 * j p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p _ => pow_ne_zero _ (S.prime p).ne_zero
  have hX0 : 4 * S.t * S.r ^ 2 ≠ 0 := by positivity
  unfold InBoxK
  rw [← Nat.factorization_le_iff_dvd (mul_ne_zero hX0 hP0) S.hN.ne']
  intro q
  rw [Nat.factorization_mul hX0 hP0, Finsupp.add_apply]
  -- the factorization of the smooth product
  have hprod : (∏ p : S.ι, p.1 ^ (2 * j p)).factorization q =
      if hq : q ∈ S.N.primeFactors then 2 * j ⟨q, hq⟩ else 0 := by
    rw [Nat.factorization_prod fun p _ => pow_ne_zero _ (S.prime p).ne_zero,
      Finsupp.finsetSum_apply]
    simp_rw [(S.prime _).factorization_pow, Finsupp.single_apply]
    split_ifs with hq
    · rw [Finset.sum_eq_single ⟨q, hq⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h; apply hb; exact Subtype.ext h
      · simp
    · refine Finset.sum_eq_zero fun p _ => ?_
      rw [if_neg]
      intro h; apply hq; rw [← h]; exact p.2
  rw [hprod]
  split_ifs with hq
  · have := hcon ⟨q, hq⟩
    have hqp := Nat.prime_of_mem_primeFactors hq
    rw [Nat.factorization_def _ hqp, Nat.factorization_def _ hqp]
    simp only at this
    omega
  · -- `q ∤ N`, so `q ∤ 4 t r²`
    rw [add_zero]
    by_cases hqp : q.Prime
    · have hqN : ¬ q ∣ S.N := fun h => hq (Nat.mem_primeFactors.2 ⟨hqp, h, S.hN.ne'⟩)
      have hq4 : ¬ q ∣ 4 * S.t * S.r ^ 2 := by
        intro h
        rcases (Nat.Prime.dvd_mul hqp).1 h with h1 | h1
        · rcases (Nat.Prime.dvd_mul hqp).1 h1 with h2 | h2
          · exact hqN (h2.trans S.h4)
          · exact hqN (h2.trans S.htN)
        · exact hqN ((hqp.dvd_of_dvd_pow h1).trans S.hrN)
      rw [Nat.factorization_eq_zero_of_not_dvd hq4]
      exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hqp]
      exact Nat.zero_le _

/-- **Steps 1–3.** Under the Fricke bound and integrality, a class form whose `A`-coefficients
vanish on the level box has all `A`-coefficients zero. -/
theorem Aco_eq_zero_of_box (hB : ∀ g, S.BetaBound g) (hI : ∀ g, S.BetaIntegral g) (g : S.V)
    (hbox : ∀ k, S.InBoxK k → S.Aco g k = 0) (k : S.ι → ℕ) : S.Aco g k = 0 := by
  refine S.Aco_eq_zero_of_gco g (fun j => ?_) k
  by_cases hj : S.InBoxK j
  · exact S.gco_eq_zero_of_Aco g j fun k hk => hbox k (S.inBoxK_mono hk hj)
  · exact S.gco_eq_zero_of_not_box hB hI g j (S.exists_bad_of_not_inBoxK hj)

end ClassSetup

/-! ## The level box from the Fricke expansion -/

/-- **Residual (route C, analytic part, ψ even).** For every class-form space with `ψ` primitive
and even, and every class form `g`, the Fricke-expansion coefficients `β_g(m)` (the coefficients
of `W g` at `N/(4 t r²) ∏ p^{2 m_p}`, up to a nonzero constant, computed from the resolvents of
the `U(p²)`) satisfy the growth bound `|β_g(m)| ≤ C ∏ p^{m_p/2}` (from `|b(n)| = O(n^{1/4})`
for `W g`) and vanish at non-integral frequencies. TRUE: it is what the Hecke functional equation
(`fePair_functional_equation`), the Dirichlet functional equation and uniqueness of Dirichlet
coefficients give. -/
def SerreStarkFrickeBeta24 : Prop :=
  ∀ S : ClassSetup, S.ψ.IsPrimitive → S.ψ.Even → ∀ g : S.V, S.BetaBound g ∧ S.BetaIntegral g

/-- **Residual (route C, ψ odd).** A class form for an odd primitive character vanishes. TRUE
(Serre–Stark; via the functional equation: `L(1 − 2k, ψ) = 0` at the trivial zeros forces
`L(k, W f) = 0` for all large integers `k`). -/
def SerreStarkOddVanish24 : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (_h24 : 24 ∣ N) (r : ℕ) (ψ : DirichletCharacter ℂ r) (t : ℕ)
    (f : ℂ → ℂ), ψ.IsPrimitive → r ∣ N → Squarefree t → t ∣ N → ψ.Odd →
    IsClassForm N r ψ t f → ∀ n, 0 < n → thetaTypeCoeff f n = 0

/-- **The level box from the Fricke expansion.** -/
theorem levelBox24_of_frickeBeta (hB : SerreStarkFrickeBeta24) (hO : SerreStarkOddVanish24) :
    SerreStarkLevelBox24 := by
  intro N hN h24 r ψ t f hprim hrN ht htN hf hbox n hn
  rcases ψ.even_or_odd with hev | hodd
  swap
  · exact hO N hN h24 r ψ t f hprim hrN ht htN hodd hf n hn
  let S : ClassSetup := ⟨N, r, t, ψ, hN, h24, hrN, ht, htN⟩
  let g : S.V := ⟨restrictUpper f, f, hf, rfl⟩
  have hfg : restrictUpper f = (g : ℍ → ℂ) := rfl
  have hA := S.Aco_eq_zero_of_box (fun g => (hB S hprim hev g).1) (fun g => (hB S hprim hev g).2)
    g (fun k hk => ?_)
  · have hg0 : g = 0 := S.eq_zero_of_A_eq_zero fun k => hA k
    have := S.coeffL_eq hfg n
    rw [← this, hg0, map_zero]
  · -- the box hypothesis at `S₀ = ∏ p^{k_p}`
    set S₀ := ∏ p : S.ι, p.1 ^ k p with hS₀
    have hS₀1 : 1 ≤ S₀ := Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun p _ =>
      pow_ne_zero _ (S.prime p).ne_zero)
    have hsq : ∏ p : S.ι, p.1 ^ (2 * k p) = S₀ ^ 2 := by
      rw [hS₀, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← pow_mul, mul_comm]
    have hInBox : InBox N r ψ t S₀ := by
      refine ⟨hev, ?_⟩
      have := hk
      unfold ClassSetup.InBoxK at this
      rw [hsq] at this
      have e : 4 * t * S₀ ^ 2 * r ^ 2 = 4 * t * r ^ 2 * S₀ ^ 2 := by ring
      rw [e]; exact this
    rw [ClassSetup.Aco, S.coeffL_eq hfg, hsq]
    exact hbox S₀ hS₀1 hInBox

end SSHecke

end VOA.Classification.COne
