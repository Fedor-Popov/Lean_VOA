import VOA.Classification.COne.C2LevelFinite
import VOA.Huang.LogRemovalAdmissible
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Irreducible admissible modules: finite levels and a single conformal shift

C₂-cofiniteness gives finite levels after irreducibility makes a homogeneous
cyclic submodule the whole module. An eigenvector in one such level generates
the module; the conformal commutator and fixed-degree spanning then make every
level an eigenspace with the same shift. No rationality is assumed.
-/

namespace VOA.Classification.COne.AdmissibleOrdinary

open PlusRational PlusFiniteLength C2LevelFinite
open VOA.Huang.BuhlSpanning VOA.Huang.LogRemovalAdmissible

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Every nonzero vector generates an irreducible admissible module. -/
theorem cyclic_eq_top (N : AdmissibleModule W M) (hirr : N.IsIrreducible)
    {x : M} (hx : x ≠ 0) : cyclic N.toWeakModule x = ⊤ := by
  rcases hirr.2 (ofR N.toWeakModule (cyclic N.toWeakModule x)) with h | h
  · have hm : x ∈ (ofR N.toWeakModule (cyclic N.toWeakModule x)).carrier :=
      Submodule.mem_span_singleton_self x
    rw [h] at hm
    exact (hx hm).elim
  · apply top_unique
    intro y _
    have hm : y ∈ (ofR N.toWeakModule (cyclic N.toWeakModule x)).carrier := by
      rw [h]; exact Submodule.mem_top
    exact hm

/-- A nonzero admissible module has a nonzero homogeneous vector. -/
theorem exists_nonzero_homogeneous (N : AdmissibleModule W M) [Nontrivial M] :
    ∃ k : ℤ, ∃ x : M, x ∈ N.lev k ∧ x ≠ 0 := by
  by_contra h
  push Not at h
  have hb : ∀ k, N.lev k = ⊥ := fun k => le_antisymm (fun x hx => h k x hx) bot_le
  have ht := N.lev_iSup_eq_top
  simp only [hb, iSup_bot] at ht
  exact bot_ne_top ht

/-- All admissible levels of an irreducible C₂-cofinite module are finite-dimensional. -/
theorem finiteDimensional_level (hC2 : C2Cofinite W)
    (N : AdmissibleModule W M) (hirr : N.IsIrreducible) (j : ℤ) :
    FiniteDimensional ℂ (N.lev j) := by
  letI := hirr.1
  obtain ⟨k, x, hx, hx0⟩ := exists_nonzero_homogeneous N
  have htop := cyclic_eq_top N hirr hx0
  letI := finiteDimensional_cyclicLevel W hC2 N k x hx j
  let f : cyclicLevel N x j →ₗ[ℂ] N.lev j :=
    { toFun := fun y => ⟨y.val.val, y.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_surjective f
  intro y
  refine ⟨⟨⟨y.val, ?_⟩, y.property⟩, rfl⟩
  rw [htop]; exact Submodule.mem_top

/-- There is a nonzero conformal eigenvector homogeneous for the admissible grading. -/
theorem exists_homogeneous_eigenvector (hC2 : C2Cofinite W)
    (N : AdmissibleModule W M) (hirr : N.IsIrreducible) :
    ∃ (k : ℤ) (c : ℂ) (x : M), x ∈ N.lev k ∧ x ≠ 0 ∧
      L0 N.toWeakModule x = c • x := by
  letI := hirr.1
  obtain ⟨k, x, hx, hx0⟩ := exists_nonzero_homogeneous N
  letI := finiteDimensional_level hC2 N hirr k
  haveI : Nontrivial (N.lev k) :=
    ⟨⟨⟨x, hx⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
  have hpres : ∀ y ∈ N.lev k, L0 N.toWeakModule y ∈ N.lev k := by
    intro y hy
    simpa using N.act_lev W.conformal_mem hy (p := 1)
  let f : Module.End ℂ (N.lev k) := (L0 N.toWeakModule).restrict hpres
  obtain ⟨c, hc⟩ := f.exists_eigenvalue
  obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
  refine ⟨k, c, y.val, y.property, ?_, ?_⟩
  · intro h; exact hy.2 (Subtype.ext h)
  · exact congrArg Subtype.val hy.apply_eq_smul

/-- A generator word shifts a conformal eigenvalue by its admissible degree. -/
theorem wordL_eigenvalue (D : GenData W) (N : AdmissibleModule W M)
    {c : ℂ} {x : M} (hx : L0 N.toWeakModule x = c • x) (l : List (Ltr D)) :
    L0 N.toWeakModule (wordL D N.toWeakModule l x) =
      (c + (degree D l : ℂ)) • wordL D N.toWeakModule l x := by
  induction l with
  | nil => simpa using hx
  | cons a l ih =>
    rw [wordL_cons, L0_commutator_weak N.toWeakModule (D.gen_mem a.1), ih,
      map_smul, ← add_smul, degree_cons]
    congr 1
    push_cast
    ring

/-- Every level has one eigenvalue, with a common complex shift. -/
theorem exists_level_scalar (hC2 : C2Cofinite W)
    (N : AdmissibleModule W M) (hirr : N.IsIrreducible) :
    ∃ h : ℂ, ∀ (j : ℤ) (y : M), y ∈ N.lev j →
      L0 N.toWeakModule y = (h + (j : ℂ)) • y := by
  classical
  obtain ⟨k, c, x, hx, hx0, heig⟩ := exists_homogeneous_eigenvector hC2 N hirr
  have htop := cyclic_eq_top N hirr hx0
  obtain ⟨D⟩ := exists_genData hC2
  obtain ⟨N₀, hN₀⟩ := exists_grading_le_O₂ W hC2
  let Bm := k.toNat + Finset.univ.sup D.wt
  have hBm : ∀ i, k + (D.wt i : ℤ) ≤ Bm := by
    intro i
    have h := Finset.le_sup (f := D.wt) (Finset.mem_univ i)
    dsimp [Bm]
    omega
  refine ⟨c - (k : ℂ), ?_⟩
  intro j y hy
  have hcyc : y ∈ cyclic N.toWeakModule x := by rw [htop]; exact Submodule.mem_top
  have hs := cyclic_level_le_fixedDegreeSpan D N hN₀ hx hBm j hcyc hy
  have hle : Submodule.span ℂ ((fun l => wordL D N.toWeakModule l x) ''
      {l : List (Ltr D) | (∀ a, l.count a < N₀ + 1) ∧
        (∀ e ∈ l, e.2 < (Bm : ℤ)) ∧ degree D l = j - k}) ≤
      (L0 N.toWeakModule).eigenspace (c - (k : ℂ) + (j : ℂ)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, ⟨_, _, hd⟩, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    rw [wordL_eigenvalue D N heig, hd]
    congr 1
    push_cast
    ring
  exact Module.End.mem_eigenspace_iff.mp (hle hs)

end VOA.Classification.COne.AdmissibleOrdinary
