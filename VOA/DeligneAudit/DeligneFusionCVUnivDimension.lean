import VOA.DeligneAudit.DeligneFusionCVUnivQuotient
import VOA.DeligneAudit.DeligneFusionCVKernelSecond
import VOA.DeligneAudit.DeligneFusionCVKernelFundamental
import VOA.DeligneAudit.DeligneFusionCVKernelFundamentalSecond
import VOA.DeligneAudit.DeligneFusionCVUnivSymmetry

/-!
# The actual zero and fundamental-epsilon three-term dimension steps

The two checked kernel presentations give maps from smaller universal CV
modules onto the first cyclic kernel and the second cyclic kernel modulo the
first. Finite generation and rank--nullity then give the dimension inequality
for the actual universal modules. Only finite-dimensionality of the three
smaller modules is assumed; no dimension inequality or recurrence is an input.
-/

namespace VOA.DeligneAudit.A2.CVUniv

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ε ν ϱ : Weight} {j : ℕ}

/-- The universal map has exactly the cyclic submodule as its range. -/
theorem cvMap_range (h : CV3Rel R w ε ν ϱ j) :
    LinearMap.range (cvMap h) = cycSub R w := by
  rw [← Submodule.map_top, ← cv_span_top ε ν ϱ j, Submodule.map_span,
    ← Set.range_comp]
  simp only [Function.comp_def, cvMap_wordOp, cycSub]

/-- Every invariant quotient preserves the actual CV relations. -/
theorem cv3Rel_quotient (h : CV3Rel R w ε ν ϱ j) (S : Submodule ℂ V)
    (hS : ∀ c r, S ≤ S.comap (R.op c r)) :
    CV3Rel (quotRep R S hS) (S.mkQ w) ε ν ϱ j := by
  apply sat_cvSpec_iff.mp
  have hs := sat_cvSpec_iff.mpr h
  refine ⟨?_, ?_⟩
  · intro t ht
    rw [quot_wordOp, hs.tail t ht, map_zero]
  · intro p hp
    rw [quotRep_op, hs.eig p hp, map_smul]

/-- Cyclic submodules commute with the canonical invariant quotient map. -/
theorem map_cycSub_quotient (S : Submodule ℂ V)
    (hS : ∀ c r, S ≤ S.comap (R.op c r)) (v : V) :
    (cycSub R v).map S.mkQ = cycSub (quotRep R S hS) (S.mkQ v) := by
  rw [cycSub, Submodule.map_span, ← Set.range_comp, cycSub]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_def, quot_wordOp]

/-- The first cyclic kernel, before taking the second quotient. -/
def cvFirstKernelSpan (ε ν ϱ : Weight) (k : ℕ) :
    Submodule ℂ (CVMod ε ν ϱ (k + 2)) :=
  cycSub (cvUnivRep ε ν ϱ (k + 2)) (cvTopFirst ε ν ϱ k)

/-- The actual quotient action after killing the first cyclic kernel. -/
def cvFirstQuotientRep (ε ν ϱ : Weight) (k : ℕ) :
    CurrentModule bracketTable
      (CVMod ε ν ϱ (k + 2) ⧸ cvFirstKernelSpan ε ν ϱ k) :=
  quotRep (cvUnivRep ε ν ϱ (k + 2)) (cvFirstKernelSpan ε ν ϱ k)
    (cycSub_inv _ _)

/-- The first top vector satisfies the smaller first-kernel presentation. -/
theorem cvTopFirst_rel_zero (ν ϱ : Weight) (k : ℕ) :
    CV3Rel (cvUnivRep (0, 0) ν ϱ (k + 2)) (cvTopFirst (0, 0) ν ϱ k)
      (0, 1) (ν + (0, 1)) ϱ k := by
  have hi : ν.1 + ϱ.1 + (k + 2) - 1 = ν.1 + ϱ.1 + k + 1 := by omega
  simpa only [cvTopFirst, Nat.zero_add, hi, Nat.add_sub_cancel] using
    first_kernel_rel_zero (cvUniv_rel (0, 0) ν ϱ (k + 2)) (by omega)

/-- In the actual quotient by the first cyclic kernel, the second top vector
satisfies the smaller second-kernel presentation. -/
theorem cvTopSecond_quotient_rel_zero (ν ϱ : Weight) (k : ℕ) :
    CV3Rel (cvFirstQuotientRep (0, 0) ν ϱ k)
      ((cvFirstKernelSpan (0, 0) ν ϱ k).mkQ (cvTopSecond (0, 0) ν ϱ k))
      (0, 0) ν (ϱ + (1, 0)) k := by
  have hs := cv3Rel_quotient (cvUniv_rel (0, 0) ν ϱ (k + 2))
    (cvFirstKernelSpan (0, 0) ν ϱ k) (cycSub_inv _ _)
  have hi : ν.1 + ϱ.1 + (k + 2) - 1 = ν.1 + ϱ.1 + k + 1 := by omega
  have hi' : ν.2 + ϱ.2 + (k + 2) - 1 = ν.2 + ϱ.2 + k + 1 := by omega
  have hz : (quotRep (cvUnivRep (0, 0) ν ϱ (k + 2))
      (cvFirstKernelSpan (0, 0) ν ϱ k) (cycSub_inv _ _)).op 3
        (ν.1 + ϱ.1 + (k + 2) - 1)
        ((cvFirstKernelSpan (0, 0) ν ϱ k).mkQ (cv_wU (0, 0) ν ϱ (k + 2))) = 0 := by
    rw [quotRep_op]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    simpa only [hi, cvFirstKernelSpan, cvTopFirst, Nat.zero_add] using
      wordOp_mem_cycSub (cvUnivRep (0, 0) ν ϱ (k + 2))
        (cvTopFirst (0, 0) ν ϱ k) []
  have ht := second_kernel_rel_zero hs (by omega) hz
  simpa only [cvFirstQuotientRep, quotRep_op, cvTopSecond, Nat.zero_add, hi',
    Nat.add_sub_cancel] using ht

/-- A linear-algebra step for two successive cyclic kernel images. Its
finiteness conclusion does not assume the ambient source is finite. -/
theorem finite_dimensional_three_term
    {U T A B : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup T] [Module ℂ T] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B]
    (π : U →ₗ[ℂ] T) (P Q : Submodule ℂ U)
    (f : A →ₗ[ℂ] U) (g : B →ₗ[ℂ] (U ⧸ P))
    (hπ : Function.Surjective π) (hker : LinearMap.ker π = P ⊔ Q)
    (hf : LinearMap.range f = P) (hg : LinearMap.range g = Q.map P.mkQ)
    [FiniteDimensional ℂ T] [FiniteDimensional ℂ A] [FiniteDimensional ℂ B] :
    FiniteDimensional ℂ U ∧
      Module.finrank ℂ U ≤ Module.finrank ℂ T + Module.finrank ℂ A + Module.finrank ℂ B := by
  let K := P ⊔ Q
  haveI : FiniteDimensional ℂ P := by
    rw [← hf]
    infer_instance
  have hmap : K.map P.mkQ = LinearMap.range g := by
    rw [show K = P ⊔ Q from rfl, Submodule.map_sup, Submodule.mkQ_map_self,
      bot_sup_eq, hg]
  have hinf : K ⊓ LinearMap.ker P.mkQ = P := by
    rw [Submodule.ker_mkQ]
    exact inf_eq_right.mpr le_sup_left
  haveI : FiniteDimensional ℂ K := by
    apply Module.Finite.iff_fg.mpr
    refine Submodule.fg_of_fg_map_of_fg_inf_ker P.mkQ ?_ ?_
    · rw [hmap]
      exact Submodule.fg_range g
    · rw [hinf]
      exact Module.Finite.iff_fg.mp inferInstance
  haveI : FiniteDimensional ℂ U :=
    Module.Finite.of_exact (f := K.subtype) (g := π)
      (LinearMap.exact_iff.mpr (by rw [Submodule.range_subtype, hker])) hπ
  refine ⟨inferInstance, ?_⟩
  have hk := CVsl2.finrank_le_map_add_inf' P.mkQ K
  rw [hmap, hinf] at hk
  have hf' := LinearMap.finrank_range_le f
  rw [hf] at hf'
  have hg' := LinearMap.finrank_range_le g
  have he := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, hker] at he
  change Module.finrank ℂ T + Module.finrank ℂ K = Module.finrank ℂ U at he
  omega

/-- The actual universal zero-epsilon module obeys the three-term dimension
step, provided its three smaller universal modules are finite-dimensional. -/
theorem cvUniv_zero_dimension_step (ν ϱ : Weight) (k : ℕ)
    [FiniteDimensional ℂ (CVMod (0, 0) (ν + (1, 1)) ϱ k)]
    [FiniteDimensional ℂ (CVMod (0, 1) (ν + (0, 1)) ϱ k)]
    [FiniteDimensional ℂ (CVMod (0, 0) ν (ϱ + (1, 0)) k)] :
    FiniteDimensional ℂ (CVMod (0, 0) ν ϱ (k + 2)) ∧
      Module.finrank ℂ (CVMod (0, 0) ν ϱ (k + 2)) ≤
        Module.finrank ℂ (CVMod (0, 0) (ν + (1, 1)) ϱ k) +
        Module.finrank ℂ (CVMod (0, 1) (ν + (0, 1)) ϱ k) +
        Module.finrank ℂ (CVMod (0, 0) ν (ϱ + (1, 0)) k) := by
  apply finite_dimensional_three_term (cvQuotientMap (0, 0) ν ϱ k)
    (cvFirstKernelSpan (0, 0) ν ϱ k)
    (cycSub (cvUnivRep (0, 0) ν ϱ (k + 2)) (cvTopSecond (0, 0) ν ϱ k))
    (cvMap (cvTopFirst_rel_zero ν ϱ k))
    (cvMap (cvTopSecond_quotient_rel_zero ν ϱ k))
  · exact cvQuotientMap_surjective (0, 0) ν ϱ k
  · exact cvQuotientMap_ker (0, 0) ν ϱ k
  · exact cvMap_range _
  · rw [cvMap_range]
    exact (map_cycSub_quotient _ (cycSub_inv _ _) _).symm

/-- The fundamental source's first top vector satisfies its actual smaller
zero-epsilon presentation. -/
theorem cvTopFirst_rel_fundamental (ν ϱ : Weight) (k : ℕ) :
    CV3Rel (cvUnivRep (1, 0) ν ϱ (k + 2)) (cvTopFirst (1, 0) ν ϱ k)
      (0, 0) (ν + (0, 1)) ϱ (k + 1) := by
  have hi : 1 + ν.1 + ϱ.1 + k + 1 = ν.1 + ϱ.1 + (k + 2) := by omega
  simpa only [cvTopFirst, hi, Nat.add_sub_cancel] using
    CVKernelFundamental.first_kernel_rel_fundamental
      (cvUniv_rel (1, 0) ν ϱ (k + 2)) (by omega)

/-- After killing the first cyclic kernel of the fundamental source, its
second top vector satisfies the actual smaller zero-epsilon presentation. -/
theorem cvTopSecond_quotient_rel_fundamental (ν ϱ : Weight) (k : ℕ) :
    CV3Rel (cvFirstQuotientRep (1, 0) ν ϱ k)
      ((cvFirstKernelSpan (1, 0) ν ϱ k).mkQ (cvTopSecond (1, 0) ν ϱ k))
      (0, 0) (ν + (2, 0)) ϱ k := by
  have hs := cv3Rel_quotient (cvUniv_rel (1, 0) ν ϱ (k + 2))
    (cvFirstKernelSpan (1, 0) ν ϱ k) (cycSub_inv _ _)
  have hi : ν.1 + ϱ.1 + (k + 2) = 1 + ν.1 + ϱ.1 + k + 1 := by omega
  have hi' : ν.2 + ϱ.2 + (k + 2) - 1 = ν.2 + ϱ.2 + k + 1 := by omega
  have hz : (quotRep (cvUnivRep (1, 0) ν ϱ (k + 2))
      (cvFirstKernelSpan (1, 0) ν ϱ k) (cycSub_inv _ _)).op 3
        (ν.1 + ϱ.1 + (k + 2))
        ((cvFirstKernelSpan (1, 0) ν ϱ k).mkQ (cv_wU (1, 0) ν ϱ (k + 2))) = 0 := by
    rw [quotRep_op]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    simpa only [hi, cvFirstKernelSpan, cvTopFirst] using
      wordOp_mem_cycSub (cvUnivRep (1, 0) ν ϱ (k + 2))
        (cvTopFirst (1, 0) ν ϱ k) []
  have ht := CVKernelFundamentalSecond.rel hs (by omega) hz
  simpa only [cvFirstQuotientRep, quotRep_op, cvTopSecond, Nat.zero_add, hi',
    Nat.add_sub_cancel] using ht

/-- The actual fundamental-epsilon universal module obeys the three-term
dimension step, with only finite-dimensionality of its smaller modules as input. -/
theorem cvUniv_fundamental_dimension_step (ν ϱ : Weight) (k : ℕ)
    [FiniteDimensional ℂ (CVMod (1, 0) (ν + (1, 1)) ϱ k)]
    [FiniteDimensional ℂ (CVMod (0, 0) (ν + (0, 1)) ϱ (k + 1))]
    [FiniteDimensional ℂ (CVMod (0, 0) (ν + (2, 0)) ϱ k)] :
    FiniteDimensional ℂ (CVMod (1, 0) ν ϱ (k + 2)) ∧
      Module.finrank ℂ (CVMod (1, 0) ν ϱ (k + 2)) ≤
        Module.finrank ℂ (CVMod (1, 0) (ν + (1, 1)) ϱ k) +
        Module.finrank ℂ (CVMod (0, 0) (ν + (0, 1)) ϱ (k + 1)) +
        Module.finrank ℂ (CVMod (0, 0) (ν + (2, 0)) ϱ k) := by
  apply finite_dimensional_three_term (cvQuotientMap (1, 0) ν ϱ k)
    (cvFirstKernelSpan (1, 0) ν ϱ k)
    (cycSub (cvUnivRep (1, 0) ν ϱ (k + 2)) (cvTopSecond (1, 0) ν ϱ k))
    (cvMap (cvTopFirst_rel_fundamental ν ϱ k))
    (cvMap (cvTopSecond_quotient_rel_fundamental ν ϱ k))
  · exact cvQuotientMap_surjective (1, 0) ν ϱ k
  · exact cvQuotientMap_ker (1, 0) ν ϱ k
  · exact cvMap_range _
  · rw [cvMap_range]
    exact (map_cycSub_quotient _ (cycSub_inv _ _) _).symm

/-- The second-fundamental dimension step follows from the actual universal
Dynkin equivalence and the first-fundamental step. -/
theorem cvUniv_second_fundamental_dimension_step (ν ϱ : Weight) (k : ℕ)
    [hT : FiniteDimensional ℂ (CVMod (0, 1) (ν + (1, 1)) ϱ k)]
    [hA : FiniteDimensional ℂ (CVMod (0, 0) (ν + (1, 0)) ϱ (k + 1))]
    [hB : FiniteDimensional ℂ (CVMod (0, 0) (ν + (0, 2)) ϱ k)] :
    FiniteDimensional ℂ (CVMod (0, 1) ν ϱ (k + 2)) ∧
      Module.finrank ℂ (CVMod (0, 1) ν ϱ (k + 2)) ≤
        Module.finrank ℂ (CVMod (0, 1) (ν + (1, 1)) ϱ k) +
        Module.finrank ℂ (CVMod (0, 0) (ν + (1, 0)) ϱ (k + 1)) +
        Module.finrank ℂ (CVMod (0, 0) (ν + (0, 2)) ϱ k) := by
  have hT' : FiniteDimensional ℂ
      (CVMod (1, 0) ((ν.2, ν.1) + (1, 1)) (ϱ.2, ϱ.1) k) := by
    rw [show (ν.2, ν.1) + (1, 1) = ((ν + (1, 1)).2, (ν + (1, 1)).1) by
      ext <;> simp only [Prod.fst_add, Prod.snd_add]]
    exact @cvSwap_finiteDimensional (0, 1) (ν + (1, 1)) ϱ k hT
  have hA' : FiniteDimensional ℂ
      (CVMod (0, 0) ((ν.2, ν.1) + (0, 1)) (ϱ.2, ϱ.1) (k + 1)) := by
    rw [show (ν.2, ν.1) + (0, 1) = ((ν + (1, 0)).2, (ν + (1, 0)).1) by
      ext <;> simp only [Prod.fst_add, Prod.snd_add]]
    exact @cvSwap_finiteDimensional (0, 0) (ν + (1, 0)) ϱ (k + 1) hA
  have hB' : FiniteDimensional ℂ
      (CVMod (0, 0) ((ν.2, ν.1) + (2, 0)) (ϱ.2, ϱ.1) k) := by
    rw [show (ν.2, ν.1) + (2, 0) = ((ν + (0, 2)).2, (ν + (0, 2)).1) by
      ext <;> simp only [Prod.fst_add, Prod.snd_add]]
    exact @cvSwap_finiteDimensional (0, 0) (ν + (0, 2)) ϱ k hB
  obtain ⟨hs, hb⟩ := @cvUniv_fundamental_dimension_step
    (ν.2, ν.1) (ϱ.2, ϱ.1) k hT' hA' hB'
  have hfd : FiniteDimensional ℂ (CVMod (0, 1) ν ϱ (k + 2)) :=
    @cvSwap_finiteDimensional (1, 0) (ν.2, ν.1) (ϱ.2, ϱ.1) (k + 2) hs
  refine ⟨hfd, ?_⟩
  rw [cvSwap_finrank (0, 1) ν ϱ (k + 2),
    cvSwap_finrank (0, 1) (ν + (1, 1)) ϱ k,
    cvSwap_finrank (0, 0) (ν + (1, 0)) ϱ (k + 1),
    cvSwap_finrank (0, 0) (ν + (0, 2)) ϱ k]
  exact hb

end

end VOA.DeligneAudit.A2.CVUniv

#print axioms VOA.DeligneAudit.A2.CVUniv.cvMap_range
#print axioms VOA.DeligneAudit.A2.CVUniv.cvTopSecond_quotient_rel_zero
#print axioms VOA.DeligneAudit.A2.CVUniv.finite_dimensional_three_term
#print axioms VOA.DeligneAudit.A2.CVUniv.cvUniv_zero_dimension_step
#print axioms VOA.DeligneAudit.A2.CVUniv.cvTopSecond_quotient_rel_fundamental
#print axioms VOA.DeligneAudit.A2.CVUniv.cvUniv_fundamental_dimension_step
#print axioms VOA.DeligneAudit.A2.CVUniv.cvUniv_second_fundamental_dimension_step
