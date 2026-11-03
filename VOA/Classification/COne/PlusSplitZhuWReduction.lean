import VOA.Classification.COne.PlusSplitZhuEReduction
import VOA.Modularity.OmegaCentral

/-! Genuine W relations in the Zhu quotient, descended from O(V) certificates. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuNormalForms
open PlusUnitary PlusC2
variable (m : ℕ) (hm : 1 ≤ m)
@[reducible] local instance zhuWRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuWAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

theorem omega_commute (x : VOA.A (V2mPlus m hm)) : Commute (generator m hm 0) x :=
  omega_central (V2mPlus m hm) x

theorem mk_incl_monoE (i j : ℕ) :
    VOA.mk (V2mPlus m hm) (incl m hm (monoE m hm i j)) =
      generator m hm 0 ^ i * generator m hm 1 ^ j := by
  have hφ := incl_gradedHom m hm
  have hω : ∀ k : ℕ, VOA.mk (V2mPlus m hm)
      (incl m hm ((fun y => zhuMul (M1P m hm) (ωM m hm) y)^[k]
        (M1P m hm).vacuum)) = generator m hm 0 ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', hφ.map_zhuMul (ωM_mem_grading m hm),
        mk_zhuMul, ih, pow_succ']
      rfl
  rw [monoE]
  induction j with
  | zero => simpa using hω i
  | succ j ih =>
    rw [Function.iterate_succ_apply', hφ.map_zhuMul (WM_mem_grading m hm),
      mk_zhuMul, ih]
    change generator m hm 1 * (generator m hm 0 ^ i * generator m hm 1 ^ j) = _
    rw [← mul_assoc, ((omega_commute m hm (generator m hm 1)).pow_left i).eq.symm,
      mul_assoc, ← pow_succ']

def evalZhuML (L : MonoList) : VOA.A (V2mPlus m hm) :=
  (L.map fun t => (t.1 : ℂ) • (generator m hm 0 ^ t.2.1 * generator m hm 1 ^ t.2.2)).sum

theorem mk_incl_lcE (L : MonoList) :
    VOA.mk (V2mPlus m hm) (incl m hm (lcE m hm L)) = evalZhuML m hm L := by
  induction L with
  | nil => simp [lcE, evalZhuML]
  | cons t L ih =>
    simpa only [lcE, evalZhuML, List.map_cons, List.sum_cons, map_add, map_smul,
      mk_incl_monoE] using congrArg (fun z => (t.1 : ℂ) •
        (generator m hm 0 ^ t.2.1 * generator m hm 1 ^ t.2.2) + z) ih

/-- Both certified Heisenberg relations hold in the actual quotient, not
merely after evaluation on simple tops. -/
theorem zhu_r1_r2 : evalZhuML m hm r1T = 0 ∧ evalZhuML m hm r2T = 0 := by
  have hc (L : MonoList) (C : List OEntry)
      (he : ∀ t ∈ C, Even t.2.1.length ∧ Even t.2.2.1.length)
      (hcert : PlusC2Eval.normR (PlusC2.lc (lcR L)) =
        PlusC2Eval.normR (PlusC2.lc (ocert C))) :
      evalZhuML m hm L = 0 := by
    rw [← mk_incl_lcE]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact mem_of_cert m hm _ (hasPoly_lcE m hm L) _ (ocert_mem_OPlus m hm C he) hcert
  exact ⟨hc r1T r1L (by decide) r1_cert, hc r2T r2L (by decide) r2_cert⟩

/-- Quadratic W reduction, valid uniformly for every positive m. -/
theorem W_squared :
    generator m hm 1 ^ 2 =
      (-264/7 : ℂ) • generator m hm 0 ^ 3 +
      (3/7 : ℂ) • generator m hm 1 - (6/7 : ℂ) • generator m hm 0 -
      (37/7 : ℂ) • (generator m hm 0 * generator m hm 1) +
      (102/7 : ℂ) • generator m hm 0 ^ 2 +
      (132/7 : ℂ) • (generator m hm 0 ^ 2 * generator m hm 1) := by
  have h := (zhu_r1_r2 m hm).1
  norm_num [evalZhuML, r1T] at h
  have he := congrArg (fun z : VOA.A (V2mPlus m hm) => (-3/7 : ℂ) • z) h
  simp only [smul_zero] at he
  apply sub_eq_zero.mp
  convert he using 1
  module

/-- Highest W-column reduction needed when the normal-form list has three
W columns. It is an identity in the full Zhu quotient. -/
theorem omega_cubed_W :
    generator m hm 0 ^ 3 * generator m hm 1 =
      (2 : ℂ) • generator m hm 0 ^ 4 -
      (13/4 : ℂ) • generator m hm 0 ^ 3 +
      (169/128 : ℂ) • generator m hm 0 ^ 2 -
      (9/128 : ℂ) • generator m hm 0 +
      (9/256 : ℂ) • generator m hm 1 -
      (169/256 : ℂ) • (generator m hm 0 * generator m hm 1) +
      (13/8 : ℂ) • (generator m hm 0 ^ 2 * generator m hm 1) := by
  have h := (zhu_r1_r2 m hm).2
  norm_num [evalZhuML, r2T] at h
  rw [W_squared] at h
  have he := congrArg (fun z : VOA.A (V2mPlus m hm) => (-21/256 : ℂ) • z) h
  simp only [smul_zero] at he
  apply sub_eq_zero.mp
  simp only [pow_succ, pow_zero, one_mul, mul_add, mul_sub, mul_smul_comm,
    mul_assoc] at he ⊢
  convert he using 1
  module

theorem omega_power_mem (i : ℕ) (hi : i < omegaCount m) :
    generator m hm 0 ^ i ∈ Submodule.span ℂ (Set.range (monomial m hm)) :=
  Submodule.subset_span ⟨.inl ⟨i, hi⟩, rfl⟩

theorem omega_power_W_mem (i : ℕ) (hi : i < wCount m) :
    generator m hm 0 ^ i * generator m hm 1 ∈
      Submodule.span ℂ (Set.range (monomial m hm)) :=
  Submodule.subset_span ⟨.inr (.inl ⟨i, hi⟩), rfl⟩

/-- W squared is already in normal form whenever the list contains three
W columns and at least four pure omega powers. -/
theorem W_squared_mem (hw : 3 ≤ wCount m) (ho : 4 ≤ omegaCount m) :
    generator m hm 1 ^ 2 ∈ Submodule.span ℂ (Set.range (monomial m hm)) := by
  rw [W_squared]
  have hW : generator m hm 1 ∈ Submodule.span ℂ (Set.range (monomial m hm)) := by
    simpa using omega_power_W_mem m hm 0 (by omega)
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (omega_power_mem m hm 3 (by omega)))
      (Submodule.smul_mem _ _ hW))
      (Submodule.smul_mem _ _ (by simpa using omega_power_mem m hm 1 (by omega))))
      (Submodule.smul_mem _ _ (by simpa using omega_power_W_mem m hm 1 (by omega))))
    (Submodule.smul_mem _ _ (omega_power_mem m hm 2 (by omega))))
    (Submodule.smul_mem _ _ (omega_power_W_mem m hm 2 (by omega)))

theorem omega_cubed_W_mem (hw : 3 ≤ wCount m) (ho : 5 ≤ omegaCount m) :
    generator m hm 0 ^ 3 * generator m hm 1 ∈
      Submodule.span ℂ (Set.range (monomial m hm)) := by
  rw [omega_cubed_W]
  have hW : generator m hm 1 ∈ Submodule.span ℂ (Set.range (monomial m hm)) := by
    simpa using omega_power_W_mem m hm 0 (by omega)
  have hw1 := omega_power_W_mem m hm 1 (by omega)
  have hw2 := omega_power_W_mem m hm 2 (by omega)
  have h1 := omega_power_mem m hm 1 (by omega)
  have h2 := omega_power_mem m hm 2 (by omega)
  have h3 := omega_power_mem m hm 3 (by omega)
  have h4 := omega_power_mem m hm 4 (by omega)
  simp only [pow_one] at h1 hw1
  repeat first
    | apply Submodule.add_mem
    | apply Submodule.sub_mem
    | apply Submodule.smul_mem
    | assumption

/-- Every omega-times-W-column obligation, including the boundary, in the
three-W-column case. The numerical list bounds are explicit. -/
theorem omega_mul_W_monomial_mem (hw : wCount m = 3) (ho : 5 ≤ omegaCount m)
    (i : Fin (wCount m)) :
    generator m hm 0 * monomial m hm (.inr (.inl i)) ∈
      Submodule.span ℂ (Set.range (monomial m hm)) := by
  by_cases hi : i.val + 1 < wCount m
  · simpa only [monomial, pow_succ', mul_assoc] using omega_power_W_mem m hm (i.val + 1) hi
  · have he : i.val = 2 := by have := i.isLt; omega
    simpa only [monomial, he, pow_succ', mul_assoc] using
      omega_cubed_W_mem m hm (by omega) ho

/-- All omega powers times E reduce to its three columns. -/
theorem omega_power_E_mem (hm2 : 2 ≤ m) (n : ℕ) :
    generator m hm 0 ^ n * generator m hm 2 ∈
      Submodule.span ℂ (Set.range (monomial m hm)) := by
  let f : Fin 3 → VOA.A (V2mPlus m hm) := fun i =>
    generator m hm 0 ^ i.val * generator m hm 2
  let S := Submodule.span ℂ (Set.range f)
  have hf (i : Fin 3) : f i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  have h3 : generator m hm 0 ^ 3 * generator m hm 2 ∈ S := by
    rw [omega_cubed_E m hm hm2]
    have h0 : generator m hm 2 ∈ S := by simpa [f] using hf 0
    have h1 : generator m hm 0 * generator m hm 2 ∈ S := by simpa [f] using hf 1
    have h2 : generator m hm 0 ^ 2 * generator m hm 2 ∈ S := hf 2
    exact S.add_mem (S.sub_mem (S.smul_mem _ h2) (S.smul_mem _ h1)) (S.smul_mem _ h0)
  have hs : ∀ x ∈ S, generator m hm 0 * x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · simpa [f] using hf 1
      · simpa [f, pow_succ', mul_assoc] using hf 2
      · simpa [f, pow_succ', mul_assoc] using h3
    | zero => simp
    | add x y _ _ hx hy => simpa only [mul_add] using S.add_mem hx hy
    | smul c x _ hx => simpa only [mul_smul_comm] using S.smul_mem c hx
  have hn : generator m hm 0 ^ n * generator m hm 2 ∈ S := by
    induction n with
    | zero => exact hf 0
    | succ n ih => simpa only [pow_succ', mul_assoc] using hs _ ih
  have hle : S ≤ Submodule.span ℂ (Set.range (monomial m hm)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨.inr (.inr i), rfl⟩
  exact hle hn

/-- Every E-times-pure-omega-column obligation is unconditional. -/
theorem E_mul_omega_monomial_mem (hm2 : 2 ≤ m) (i : Fin (omegaCount m)) :
    generator m hm 2 * monomial m hm (.inl i) ∈
      Submodule.span ℂ (Set.range (monomial m hm)) := by
  change generator m hm 2 * generator m hm 0 ^ i.val ∈ _
  rw [((omega_commute m hm (generator m hm 2)).pow_left i.val).eq.symm]
  exact omega_power_E_mem m hm hm2 i.val

end VOA.Classification.COne.PlusZhuNormalForms
