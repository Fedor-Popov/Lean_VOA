import VOA.DeligneAudit.DeligneFusionD1TensorGRank
import VOA.DeligneAudit.DeligneFusionD1SiteGCyclic

/-!
# Actual cyclicity of shifted D1 tensor sites

Hermite interpolation makes the current cyclic subspace invariant under
each separate local mode. Multilinearity and the proved single-site word
spanning then place every pure tensor in that subspace. No character or
finite-dimensionality premise occurs in this argument.
-/

namespace VOA.DeligneAudit.D1TensorG

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorLoop
open VOA.DeligneAudit.DeligneSector

noncomputable section

variable {n N : ℕ} (f : Fin n → Fin n → Fin n → ℂ)
variable (hJ : JacobiCoord f) (hskew : ∀ a b c, f a b c = -f b a c)

/-- Tensor product of the actual single-site cyclic generators. -/
def generator (c₀ : Fin n) : Space n N :=
  PiTensorProduct.tprod ℂ (fun _ : Fin N => D1SiteG.w c₀)

/-- The actual current-word cyclic subspace of the shifted tensor model. -/
def cyclic (z : Fin N → ℂ) (c₀ : Fin n) : Submodule ℂ (Space n N) :=
  Submodule.span ℂ (Set.range fun l : List (Fin n × ℕ) =>
    wordOp (rep f hJ hskew z) l (generator c₀))

theorem generator_mem (z : Fin N → ℂ) (c₀ : Fin n) :
    generator c₀ ∈ cyclic f hJ hskew z c₀ := Submodule.subset_span ⟨[], rfl⟩

theorem cyclic_op (z : Fin N → ℂ) (c₀ : Fin n) (c : Fin n) (k : ℕ) :
    cyclic f hJ hskew z c₀ ≤ (cyclic f hJ hskew z c₀).comap ((rep f hJ hskew z).op c k) := by
  rw [cyclic, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact Submodule.subset_span ⟨(c, k) :: l, rfl⟩

/-- The actual current cyclic subspace is invariant under every individual
local site mode, by the checked two-jet interpolation identities. -/
theorem cyclic_local_mode (z : Fin N → ℂ) (hz : Function.Injective z)
    (c₀ : Fin n) (j : Fin N) (c : Fin n) (r : ℕ) :
    cyclic f hJ hskew z c₀ ≤ (cyclic f hJ hskew z c₀).comap
      (localOp j ((D1SiteG.rep f hJ hskew).op c r)) := by
  let A : Fin N → Module.End ℂ (Space n N) := fun i => localOp i (D1SiteG.zeroOp f c)
  let B : Fin N → Module.End ℂ (Space n N) := fun i => localOp i (D1SiteG.oneOp c)
  have hinv : ∀ k, cyclic f hJ hskew z c₀ ≤
      (cyclic f hJ hskew z c₀).comap (JetInterpolation.jetOp z A B k) := by
    intro k
    change cyclic f hJ hskew z c₀ ≤ (cyclic f hJ hskew z c₀).comap
      (JetInterpolation.jetOp z (fun i => localOp i (D1SiteG.zeroOp f c))
        (fun i => localOp i (D1SiteG.oneOp c)) k)
    rw [← op_eq_jetOp f hJ hskew z c k]
    exact cyclic_op f hJ hskew z c₀ c k
  obtain ⟨hA, hB⟩ := (JetInterpolation.invariant_jetOp_iff z hz A B
    (cyclic f hJ hskew z c₀)).mp hinv
  rcases r with _ | r
  · exact hA j
  · rcases r with _ | r
    · exact hB j
    · change cyclic f hJ hskew z c₀ ≤ (cyclic f hJ hskew z c₀).comap
        (localOp j (0 : Module.End ℂ (D1SiteG.Space n)))
      rw [localOp_zero]
      intro v _
      change (0 : Space n N) ∈ cyclic f hJ hskew z c₀
      exact Submodule.zero_mem _

private theorem localOp_insert (j : Fin N) (A : Module.End ℂ (D1SiteG.Space n))
    (v : Fin N → D1SiteG.Space n) (x : D1SiteG.Space n) :
    localOp j A ((PiTensorProduct.tprod ℂ).toLinearMap v j x) =
      (PiTensorProduct.tprod ℂ).toLinearMap v j (A x) := by
  change localOp j A (PiTensorProduct.tprod ℂ (Function.update v j x)) = _
  rw [localOp_tprod]
  simp only [Function.update_self, Function.update_idem, MultilinearMap.toLinearMap_apply]

/-- Single-site spanning and separate local invariance force the full tensor
space, by finite-site multilinearity. -/
private theorem top_of_local_invariant (c₀ : Fin n) (depth : ℕ)
    (hcyc : ∀ c, (Pi.single c 1 : D1SiteG.Co n) ∈ slotWords f c₀ depth)
    (P : Submodule ℂ (Space n N)) (hw : generator c₀ ∈ P)
    (hlocal : ∀ j c r, P ≤ P.comap (localOp j ((D1SiteG.rep f hJ hskew).op c r))) :
    P = ⊤ := by
  have hsite := D1SiteG.cyclic_top f hJ hskew c₀ depth hcyc
  have hpartial : ∀ T : Finset (Fin N), ∀ v : Fin N → D1SiteG.Space n,
      PiTensorProduct.tprod ℂ (fun i => if i ∈ T then v i else D1SiteG.w c₀) ∈ P := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro v
        simpa only [Finset.notMem_empty, if_false] using hw
    | @insert j T hj ih =>
        intro v
        let base : Fin N → D1SiteG.Space n := fun i => if i ∈ T then v i else D1SiteG.w c₀
        let E : D1SiteG.Space n →ₗ[ℂ] Space n N := (PiTensorProduct.tprod ℂ).toLinearMap base j
        have hbase : base j = D1SiteG.w c₀ := by simp only [base, if_neg hj]
        have hword : ∀ l : List (Fin n × ℕ),
            E (wordOp (D1SiteG.rep f hJ hskew) l (D1SiteG.w c₀)) ∈ P := by
          intro l
          induction l with
          | nil =>
              change PiTensorProduct.tprod ℂ (Function.update base j (D1SiteG.w c₀)) ∈ P
              rw [← hbase, Function.update_eq_self]
              exact ih v
          | cons a l ihl =>
              change E ((D1SiteG.rep f hJ hskew).op a.1 a.2
                (wordOp (D1SiteG.rep f hJ hskew) l (D1SiteG.w c₀))) ∈ P
              rw [← localOp_insert]
              exact hlocal j a.1 a.2 ihl
        have hmap : D1SiteG.cyclic f hJ hskew c₀ ≤ P.comap E := by
          rw [D1SiteG.cyclic, Submodule.span_le]
          rintro _ ⟨l, rfl⟩
          exact hword l
        have hx : E (v j) ∈ P := hmap (hsite ▸ Submodule.mem_top)
        have he : (fun i => if i ∈ insert j T then v i else D1SiteG.w c₀) =
            Function.update base j (v j) := by
          funext i
          by_cases hij : i = j
          · subst i
            simp only [Finset.mem_insert_self, if_true, Function.update_self]
          · simp only [Finset.mem_insert, hij, false_or, base, Function.update_of_ne hij]
        rw [he]
        exact hx
  apply top_unique
  rw [← PiTensorProduct.span_tprod_eq_top]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, rfl⟩
  simpa only [Finset.mem_univ, if_true] using hpartial Finset.univ v

/-- The actual tensor generator is cyclic for any distinct shifted sites. -/
theorem cyclic_top (z : Fin N → ℂ) (hz : Function.Injective z) (c₀ : Fin n) (depth : ℕ)
    (hcyc : ∀ c, (Pi.single c 1 : D1SiteG.Co n) ∈ slotWords f c₀ depth) :
    cyclic f hJ hskew z c₀ = ⊤ :=
  top_of_local_invariant f hJ hskew c₀ depth hcyc (cyclic f hJ hskew z c₀)
    (generator_mem f hJ hskew z c₀) (cyclic_local_mode f hJ hskew z hz c₀)

/-- The already checked sector word certificate supplies tensor cyclicity. -/
theorem sector_cyclic_top (S : DeligneSectorData)
    (hskew : ∀ a b c, S.f a b c = -S.f b a c) (z : Fin N → ℂ)
    (hz : Function.Injective z) : cyclic S.f S.jacobi hskew z S.c₀ = ⊤ :=
  cyclic_top S.f S.jacobi hskew z hz S.c₀ S.depth S.cyclic

/-- Explicit pairwise distinct sites, including the empty family. -/
def points (N : ℕ) (i : Fin N) : ℂ := (i.val : ℂ)

theorem points_injective (N : ℕ) : Function.Injective (points N) := by
  intro i j hij
  apply Fin.ext
  change (i.val : ℂ) = (j.val : ℂ) at hij
  exact_mod_cast hij

/-- The constructed canonical shifted tensor generator is genuinely cyclic. -/
theorem sector_model_cyclic (S : DeligneSectorData)
    (hskew : ∀ a b c, S.f a b c = -S.f b a c) (N : ℕ) :
    cyclic S.f S.jacobi hskew (points N) S.c₀ = ⊤ :=
  sector_cyclic_top S hskew (points N) (points_injective N)

/-- Its exact total rank is the product of the actual site ranks. -/
theorem sector_model_rank (S : DeligneSectorData) (N : ℕ) :
    Module.finrank ℂ (Space S.n N) = (S.n + 1) ^ N := finrank_space S.n N

end
end VOA.DeligneAudit.D1TensorG

#print axioms VOA.DeligneAudit.D1TensorG.cyclic_top
#print axioms VOA.DeligneAudit.D1TensorG.sector_cyclic_top

#print axioms VOA.DeligneAudit.D1TensorG.sector_model_cyclic
#print axioms VOA.DeligneAudit.D1TensorG.sector_model_rank
