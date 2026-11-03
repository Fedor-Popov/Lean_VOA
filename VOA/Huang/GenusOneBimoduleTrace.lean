import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Trace
import VOA.Modularity.SemisimpleTrace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Symmetric functionals on semisimple bimodules

The algebraic mechanism of Miyamoto, math/0010180, Lemma 4.10.
A nondegenerate associative trace pairing identifies a balanced functional on
any bimodule with a bimodule map into the algebra. No finite-dimensionality
of the bimodule is required. Artin–Wedderburn supplies the pairing.
-/
namespace VOA.Huang.GenusOne.BimoduleTrace
open scoped BigOperators

variable {R E : Type*} [Ring R] [Algebra ℂ R]
  [AddCommGroup E] [Module ℂ E]

/-- Bilinear left and right actions, with the usual unital bimodule laws.
Keeping the actions explicit avoids competing module instances. -/
structure Actions (R E : Type*) [Ring R] [Algebra ℂ R]
    [AddCommGroup E] [Module ℂ E] where
  left : R →ₗ[ℂ] Module.End ℂ E
  right : R →ₗ[ℂ] Module.End ℂ E
  left_one : ∀ x, left 1 x = x
  right_one : ∀ x, right 1 x = x
  left_mul : ∀ a b x, left (a * b) x = left a (left b x)
  right_mul : ∀ a b x, right (a * b) x = right b (right a x)
  commute : ∀ a b x, left a (right b x) = right b (left a x)

/-- The associative pairing associated to a linear trace. -/
noncomputable def pairing (t : R →ₗ[ℂ] ℂ) : R →ₗ[ℂ] Module.Dual ℂ R where
  toFun x :=
    { toFun := fun a => t (a * x)
      map_add' := fun a b => by simp [add_mul]
      map_smul' := fun c a => by simp }
  map_add' x y := by ext a; simp [mul_add]
  map_smul' c x := by ext a; simp

@[simp] theorem pairing_apply (t : R →ₗ[ℂ] ℂ) (x a : R) :
    pairing t x a = t (a * x) := rfl

/-- A balanced functional is the trace of a map respecting both actions. -/
theorem exists_bimodule_map (B : Actions R E) (t : R →ₗ[ℂ] ℂ)
    (ht : ∀ a b, t (a * b) = t (b * a))
    (hpair : Function.Bijective (pairing t)) (f : E →ₗ[ℂ] ℂ)
    (hf : ∀ a x, f (B.left a x) = f (B.right a x)) :
    ∃ T : E →ₗ[ℂ] R,
      (∀ a x, T (B.left a x) = a * T x) ∧
      (∀ a x, T (B.right a x) = T x * a) ∧ ∀ x, t (T x) = f x := by
  let e := LinearEquiv.ofBijective (pairing t) hpair
  let g : E →ₗ[ℂ] Module.Dual ℂ R :=
    { toFun := fun x =>
        { toFun := fun a => f (B.left a x)
          map_add' := fun a b => by simp
          map_smul' := fun c a => by simp }
      map_add' := fun x y => by ext a; simp
      map_smul' := fun c x => by ext a; simp }
  let T := e.symm.toLinearMap.comp g
  have hT (x : E) (a : R) : t (a * T x) = f (B.left a x) :=
    congrArg (fun h : Module.Dual ℂ R => h a) (e.apply_symm_apply (g x))
  have hext (x y : R) (h : ∀ a, t (a * x) = t (a * y)) : x = y :=
    hpair.1 (LinearMap.ext h)
  refine ⟨T, ?_, ?_, ?_⟩
  · intro a x
    apply hext
    intro b
    rw [hT, ← B.left_mul, ← mul_assoc, hT]
  · intro a x
    apply hext
    intro b
    rw [hT, B.commute, ← hf, ← B.left_mul,
      ← mul_assoc, ht (b * T x) a, ← mul_assoc, hT]
  · intro x
    simpa [B.left_one] using hT x 1

section Matrices
variable {ι : Type*} [Fintype ι] (d : ι → ℕ)

/-- Sum of ordinary traces of the simple matrix blocks. -/
noncomputable def matrixTrace : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ] ℂ :=
  ∑ i, (Matrix.traceLinearMap (Fin (d i)) ℂ ℂ).comp (LinearMap.proj i)

@[simp] theorem matrixTrace_apply (x : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    matrixTrace d x = ∑ i, Matrix.trace (x i) := by
  simp [matrixTrace]

theorem matrixTrace_comm (a b : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    matrixTrace d (a * b) = matrixTrace d (b * a) := by
  simp only [matrixTrace_apply, Pi.mul_apply]
  exact Finset.sum_congr rfl fun i _ => Matrix.trace_mul_comm _ _

theorem matrixTrace_pairing_injective : Function.Injective (pairing (matrixTrace d)) := by
  classical
  intro x y h
  funext i
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro a
  have he := congrArg (fun f => f (Pi.single i a)) h
  have hs (z : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
      matrixTrace d (Pi.single i a * z) = Matrix.trace (a * z i) := by
    rw [matrixTrace_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  simpa only [pairing_apply, hs] using he

/-- Nondegeneracy of the trace pairing, including products with empty blocks. -/
theorem matrixTrace_pairing_bijective : Function.Bijective (pairing (matrixTrace d)) := by
  refine ⟨matrixTrace_pairing_injective d, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank _).mp
    (matrixTrace_pairing_injective d)
  exact Subspace.dual_finrank_eq.symm

/-- Trace realization with explicit simple matrix blocks (unweighted Lemma 4.10). -/
theorem exists_matrix_bimodule_map
    (B : Actions (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) E)
    (f : E →ₗ[ℂ] ℂ) (hf : ∀ a x, f (B.left a x) = f (B.right a x)) :
    ∃ T : E →ₗ[ℂ] (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ),
      (∀ a x, T (B.left a x) = a * T x) ∧
      (∀ a x, T (B.right a x) = T x * a) ∧
      ∀ x, f x = ∑ i, Matrix.trace (T x i) := by
  obtain ⟨T, hL, hR, hT⟩ := exists_bimodule_map B (matrixTrace d)
    (matrixTrace_comm d) (matrixTrace_pairing_bijective d) f hf
  exact ⟨T, hL, hR, fun x => by simpa using (hT x).symm⟩

end Matrices

/-- A finite-dimensional semisimple complex algebra admits a symmetric,
nondegenerate associative trace pairing. -/
theorem exists_trace_pairing [FiniteDimensional ℂ R] [IsSemisimpleRing R] :
    ∃ t : R →ₗ[ℂ] ℂ, (∀ a b, t (a * b) = t (b * a)) ∧
      Function.Bijective (pairing t) := by
  obtain ⟨n, d, _, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ R
  let t := (matrixTrace d).comp e.toLinearMap
  have hinj : Function.Injective (pairing t) := by
    intro x y h
    apply e.injective
    apply matrixTrace_pairing_injective d
    apply LinearMap.ext
    intro a
    have he := congrArg (fun f => f (e.symm a)) h
    simpa only [pairing_apply, t, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      map_mul, AlgEquiv.apply_symm_apply] using he
  refine ⟨t, ?_, hinj, ?_⟩
  · intro a b
    change matrixTrace d (e (a * b)) = matrixTrace d (e (b * a))
    simp only [map_mul]
    exact matrixTrace_comm d (e a) (e b)
  · exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp hinj

/-- The algebraic realization mechanism holds for every semisimple complex
algebra and every bimodule; no assumption on the size of the latter. -/
theorem exists_semisimple_bimodule_map [FiniteDimensional ℂ R] [IsSemisimpleRing R]
    (B : Actions R E) (f : E →ₗ[ℂ] ℂ)
    (hf : ∀ a x, f (B.left a x) = f (B.right a x)) :
    ∃ (t : R →ₗ[ℂ] ℂ) (T : E →ₗ[ℂ] R),
      (∀ a b, t (a * b) = t (b * a)) ∧
      (∀ a x, T (B.left a x) = a * T x) ∧
      (∀ a x, T (B.right a x) = T x * a) ∧ ∀ x, t (T x) = f x := by
  obtain ⟨t, ht, hp⟩ := exists_trace_pairing (R := R)
  obtain ⟨T, hL, hR, hT⟩ := exists_bimodule_map B t ht hp f hf
  exact ⟨t, T, ht, hL, hR, hT⟩

section Endomorphisms
variable {ι : Type*} [Fintype ι] (U : ι → Type*)
  [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
  [∀ i, FiniteDimensional ℂ (U i)]

/-- The trace used when the simple modules, rather than matrix bases, are fixed. -/
noncomputable def endTrace : (∀ i, Module.End ℂ (U i)) →ₗ[ℂ] ℂ :=
  ∑ i, (LinearMap.trace ℂ (U i)).comp (LinearMap.proj i)

omit [∀ i, FiniteDimensional ℂ (U i)] in
@[simp] theorem endTrace_apply (x : ∀ i, Module.End ℂ (U i)) :
    endTrace U x = ∑ i, LinearMap.trace ℂ (U i) (x i) := by
  simp [endTrace]

omit [∀ i, FiniteDimensional ℂ (U i)] in
theorem endTrace_comm (a b : ∀ i, Module.End ℂ (U i)) :
    endTrace U (a * b) = endTrace U (b * a) := by
  simp only [endTrace_apply, Pi.mul_apply]
  exact Finset.sum_congr rfl fun i _ => LinearMap.trace_mul_comm ℂ _ _

/-- The sum of the simple-module traces gives a nondegenerate pairing on
 their full product of endomorphism algebras. -/
theorem endTrace_pairing_bijective : Function.Bijective (pairing (endTrace U)) := by
  classical
  have hinj : Function.Injective (pairing (endTrace U)) := by
    intro x y h
    funext i
    have hi (c : Module.End ℂ (U i)) :
        LinearMap.trace ℂ (U i) (c * x i) = LinearMap.trace ℂ (U i) (c * y i) := by
      have hs (z : ∀ i, Module.End ℂ (U i)) :
          endTrace U (Pi.single i c * z) = LinearMap.trace ℂ (U i) (c * z i) := by
        rw [endTrace_apply, Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [Pi.single_eq_of_ne hji]
        · simp
      simpa only [pairing_apply, hs] using
        congrArg (fun f => f (Pi.single i c)) h
    let b := Module.finBasis ℂ (U i)
    apply (LinearMap.toMatrix b b).injective
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro a
    obtain ⟨c, rfl⟩ := (LinearMap.toMatrix b b).surjective a
    simpa only [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.toMatrix_mul] using hi c
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    Subspace.dual_finrank_eq.symm).mp hinj⟩

end Endomorphisms

end VOA.Huang.GenusOne.BimoduleTrace
