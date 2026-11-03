/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# A graded Nakayama bound

Let `R` be a commutative `K`-algebra with `K`-subspaces `Rdeg n` (a grading-like filtration:
`1 ∈ Rdeg 0`, `Rdeg n · Rdeg k ⊆ Rdeg (n+k)`), acting on a `K`-module `N` with `K`-subspaces
`Mdeg a` such that `Rdeg n · Mdeg a ⊆ Mdeg (n+a)`.  Put

  `plus a = Σ_{1 ≤ n ≤ a} Rdeg n · Mdeg (a-n) ⊆ Mdeg a`,   `fiberDim a = dim (Mdeg a / plus a)`.

Then, with all pieces finite dimensional,

  `dim Mdeg a ≤ Σ_{b ≤ a} fiberDim b · dim Rdeg (a-b)`.

Proof: choose complements `C b` of `plus b` in `Mdeg b`; by strong induction every `Mdeg a` lies in
the span of `Rdeg (a-b) · C b`, which is the image of `⊕_b Rdeg (a-b) ⊗ C b`.
-/

namespace VOA.DeligneAudit.SectorNakayama

open Module TensorProduct

noncomputable section

variable {K R N : Type*} [Field K] [CommRing R] [Algebra K R] [AddCommGroup N] [Module K N]
  [Module R N] [IsScalarTower K R N]
variable (Rdeg : ℕ → Submodule K R) (Mdeg : ℕ → Submodule K N)

/-- The degree-`a` part of the augmentation submodule `R₊ · M`. -/
def plus (a : ℕ) : Submodule K N :=
  Submodule.span K {x | ∃ n, 1 ≤ n ∧ n ≤ a ∧ ∃ r ∈ Rdeg n, ∃ y ∈ Mdeg (a - n), x = r • y}

/-- The graded action hypotheses. -/
structure GradedAction : Prop where
  one_mem : (1 : R) ∈ Rdeg 0
  mul_mem : ∀ {n k : ℕ} {r r' : R}, r ∈ Rdeg n → r' ∈ Rdeg k → r * r' ∈ Rdeg (n + k)
  smul_mem : ∀ {n a : ℕ} {r : R} {x : N}, r ∈ Rdeg n → x ∈ Mdeg a → r • x ∈ Mdeg (n + a)

/-- Dimension of the fibre `Mdeg a / plus a`. -/
def fiberDim (a : ℕ) : ℕ :=
  finrank K (Mdeg a ⧸ (plus Rdeg Mdeg a).comap (Mdeg a).subtype)

theorem k_smul_r_smul (k : K) (r : R) (x : N) : r • (k • x) = k • (r • x) := by
  rw [← algebraMap_smul R k x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]

/-- The span of `Rdeg (a-b) · C b`, `b ≤ a`. -/
def spanS (C : ∀ b, Submodule K (Mdeg b)) (a : ℕ) : Submodule K N :=
  Submodule.span K {x | ∃ b, b ≤ a ∧ ∃ r ∈ Rdeg (a - b), ∃ v ∈ C b, x = r • (v : N)}

variable {Rdeg Mdeg}

theorem smul_mem_spanS (h : GradedAction Rdeg Mdeg) (C : ∀ b, Submodule K (Mdeg b))
    {n c : ℕ} {r : R} (hr : r ∈ Rdeg n) {w : N} (hw : w ∈ spanS Rdeg Mdeg C c) :
    r • w ∈ spanS Rdeg Mdeg C (n + c) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b, hb, r', hr', v, hv, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨b, by omega, r * r', ?_, v, hv, by rw [smul_smul]⟩
      have := h.mul_mem hr hr'
      rwa [show n + (c - b) = n + c - b by omega] at this
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul k x _ hx => rw [k_smul_r_smul]; exact Submodule.smul_mem _ k hx

omit [IsScalarTower K R N] in
theorem mem_sup_of_compl (C : ∀ b, Submodule K (Mdeg b))
    (hC : ∀ b, IsCompl ((plus Rdeg Mdeg b).comap (Mdeg b).subtype) (C b)) {a : ℕ} {x : N}
    (hx : x ∈ Mdeg a) : ∃ y ∈ plus Rdeg Mdeg a, ∃ v ∈ C a, x = y + (v : N) := by
  have htop : (⟨x, hx⟩ : Mdeg a) ∈ (plus Rdeg Mdeg a).comap (Mdeg a).subtype ⊔ C a := by
    rw [(hC a).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, v, hv, hyv⟩ := Submodule.mem_sup.mp htop
  refine ⟨y, hy, v, hv, ?_⟩
  have := congrArg Subtype.val hyv
  simpa using this.symm

theorem le_spanS (h : GradedAction Rdeg Mdeg) (C : ∀ b, Submodule K (Mdeg b))
    (hC : ∀ b, IsCompl ((plus Rdeg Mdeg b).comap (Mdeg b).subtype) (C b)) (a : ℕ) :
    Mdeg a ≤ spanS Rdeg Mdeg C a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
      intro x hx
      obtain ⟨y, hy, v, hv, rfl⟩ := mem_sup_of_compl C hC hx
      clear hx
      refine Submodule.add_mem _ ?_ ?_
      · induction hy using Submodule.span_induction with
        | mem z hz =>
            obtain ⟨n, hn1, hna, r, hr, w, hw, rfl⟩ := hz
            have hw' := ih (a - n) (by omega) hw
            have := smul_mem_spanS h C hr hw'
            rwa [show n + (a - n) = a by omega] at this
        | zero => exact Submodule.zero_mem _
        | add z z' _ _ hz hz' => exact Submodule.add_mem _ hz hz'
        | smul k z _ hz => exact Submodule.smul_mem _ k hz
      · apply Submodule.subset_span
        exact ⟨a, le_rfl, 1, by rw [Nat.sub_self]; exact h.one_mem, v, hv, by rw [one_smul]⟩

/-- The bilinear action map on chosen pieces. -/
def actBil (A : Submodule K R) (V : Submodule K N) : A →ₗ[K] V →ₗ[K] N :=
  LinearMap.mk₂ K (fun r v => (r : R) • (v : N))
    (fun r r' v => by simp [add_smul])
    (fun k r v => by simp [smul_assoc])
    (fun r v v' => by simp [smul_add])
    (fun k r v => by simp [k_smul_r_smul])

variable [∀ a, FiniteDimensional K (Mdeg a)] [∀ n, FiniteDimensional K (Rdeg n)]

/-- **Graded Nakayama bound.** -/
theorem finrank_le_sum_fiberDim (h : GradedAction Rdeg Mdeg) (a : ℕ) :
    finrank K (Mdeg a) ≤
      ∑ b ∈ Finset.range (a + 1), fiberDim Rdeg Mdeg b * finrank K (Rdeg (a - b)) := by
  classical
  choose C hC using fun b => Submodule.exists_isCompl ((plus Rdeg Mdeg b).comap (Mdeg b).subtype)
  have hCdim : ∀ b, finrank K (C b) = fiberDim Rdeg Mdeg b := fun b =>
    (Submodule.quotientEquivOfIsCompl _ _ (hC b)).finrank_eq.symm
  -- the covering map
  let Ψ : (∀ b : Fin (a + 1), Rdeg (a - b) ⊗[K] (C b).map (Mdeg b).subtype) →ₗ[K] N :=
    ∑ b : Fin (a + 1), (TensorProduct.lift (actBil (Rdeg (a - b)) ((C b).map (Mdeg b).subtype)))
      ∘ₗ LinearMap.proj b
  have hS : spanS Rdeg Mdeg C a ≤ LinearMap.range Ψ := by
    rw [spanS, Submodule.span_le]
    rintro x ⟨b, hb, r, hr, v, hv, rfl⟩
    let bb : Fin (a + 1) := ⟨b, by omega⟩
    refine ⟨Pi.single bb ((⟨r, hr⟩ : Rdeg (a - bb)) ⊗ₜ
      (⟨(v : N), ⟨v, hv, rfl⟩⟩ : (C bb).map (Mdeg bb).subtype)), ?_⟩
    simp only [Ψ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_proj, Function.eval]
    rw [Finset.sum_eq_single bb]
    · simp [actBil]
    · intro b' _ hb'
      rw [Pi.single_eq_of_ne hb', map_zero]
    · simp
  have hle := (le_spanS h C hC a).trans hS
  have h1 : finrank K (Mdeg a) ≤ finrank K (LinearMap.range Ψ) := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_le Ψ
  rw [Module.finrank_pi_fintype] at h2
  simp only [Module.finrank_tensorProduct] at h2
  refine h1.trans (h2.trans (le_of_eq ?_))
  rw [Fin.sum_univ_eq_sum_range (fun b => finrank K (Rdeg (a - b)) *
    finrank K ((C b).map (Mdeg b).subtype)) (a + 1)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm, ← hCdim b]
  congr 1
  exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) (C b)).finrank_eq.symm

end

end VOA.DeligneAudit.SectorNakayama

section AxiomAudit
#print axioms VOA.DeligneAudit.SectorNakayama.finrank_le_sum_fiberDim
end AxiomAudit
