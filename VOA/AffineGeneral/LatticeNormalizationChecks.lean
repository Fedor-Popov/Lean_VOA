import VOA.AffineGeneral.LatticeNormalizationEnumA2
import VOA.AffineGeneral.LatticeNormalizationCheckA200
import VOA.AffineGeneral.LatticeNormalizationEnumD4
import VOA.AffineGeneral.LatticeNormalizationCheckD400
import VOA.AffineGeneral.LatticeNormalizationCheckD401
import VOA.AffineGeneral.LatticeNormalizationEnumE6
import VOA.AffineGeneral.LatticeNormalizationCheckE600
import VOA.AffineGeneral.LatticeNormalizationCheckE601
import VOA.AffineGeneral.LatticeNormalizationCheckE602
import VOA.AffineGeneral.LatticeNormalizationCheckE603
import VOA.AffineGeneral.LatticeNormalizationEnumE7
import VOA.AffineGeneral.LatticeNormalizationCheckE700
import VOA.AffineGeneral.LatticeNormalizationCheckE701
import VOA.AffineGeneral.LatticeNormalizationCheckE702
import VOA.AffineGeneral.LatticeNormalizationCheckE703
import VOA.AffineGeneral.LatticeNormalizationCheckE704
import VOA.AffineGeneral.LatticeNormalizationCheckE705
import VOA.AffineGeneral.LatticeNormalizationCheckE706
import VOA.AffineGeneral.LatticeNormalizationEnumE8
import VOA.AffineGeneral.LatticeNormalizationCheckE800
import VOA.AffineGeneral.LatticeNormalizationCheckE801
import VOA.AffineGeneral.LatticeNormalizationCheckE802
import VOA.AffineGeneral.LatticeNormalizationCheckE803
import VOA.AffineGeneral.LatticeNormalizationCheckE804
import VOA.AffineGeneral.LatticeNormalizationCheckE805
import VOA.AffineGeneral.LatticeNormalizationCheckE806
import VOA.AffineGeneral.LatticeNormalizationCheckE807
import VOA.AffineGeneral.LatticeNormalizationCheckE808
import VOA.AffineGeneral.LatticeNormalizationCheckE809
import VOA.AffineGeneral.LatticeNormalizationCheckE810
import VOA.AffineGeneral.LatticeNormalizationCheckE811

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000

theorem a2_literal_sumsq :
    ∀ s ∈ a2Roots, ((a2Roots.map fun t => formL a2GL s t ^ 2).sum) = 12 := by
  have h0 := a2_chunk_00
  exact List.forall_iff_forall_mem.mp h0

theorem d4_literal_sumsq :
    ∀ s ∈ d4Roots, ((d4Roots.map fun t => formL d4GL s t ^ 2).sum) = 24 := by
  have h0 := d4_chunk_00
  have h1 := List.forall_append.mpr ⟨h0, d4_chunk_01⟩
  exact List.forall_iff_forall_mem.mp h1

theorem e6_literal_sumsq :
    ∀ s ∈ e6Roots, ((e6Roots.map fun t => formL e6GL s t ^ 2).sum) = 48 := by
  have h0 := e6_chunk_00
  have h1 := List.forall_append.mpr ⟨h0, e6_chunk_01⟩
  have h2 := List.forall_append.mpr ⟨h1, e6_chunk_02⟩
  have h3 := List.forall_append.mpr ⟨h2, e6_chunk_03⟩
  exact List.forall_iff_forall_mem.mp h3

theorem e7_literal_sumsq :
    ∀ s ∈ e7Roots, ((e7Roots.map fun t => formL e7GL s t ^ 2).sum) = 72 := by
  have h0 := e7_chunk_00
  have h1 := List.forall_append.mpr ⟨h0, e7_chunk_01⟩
  have h2 := List.forall_append.mpr ⟨h1, e7_chunk_02⟩
  have h3 := List.forall_append.mpr ⟨h2, e7_chunk_03⟩
  have h4 := List.forall_append.mpr ⟨h3, e7_chunk_04⟩
  have h5 := List.forall_append.mpr ⟨h4, e7_chunk_05⟩
  have h6 := List.forall_append.mpr ⟨h5, e7_chunk_06⟩
  exact List.forall_iff_forall_mem.mp h6

theorem e8_literal_sumsq :
    ∀ s ∈ e8Roots, ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120 := by
  have h0 := e8_chunk_00
  have h1 := List.forall_append.mpr ⟨h0, e8_chunk_01⟩
  have h2 := List.forall_append.mpr ⟨h1, e8_chunk_02⟩
  have h3 := List.forall_append.mpr ⟨h2, e8_chunk_03⟩
  have h4 := List.forall_append.mpr ⟨h3, e8_chunk_04⟩
  have h5 := List.forall_append.mpr ⟨h4, e8_chunk_05⟩
  have h6 := List.forall_append.mpr ⟨h5, e8_chunk_06⟩
  have h7 := List.forall_append.mpr ⟨h6, e8_chunk_07⟩
  have h8 := List.forall_append.mpr ⟨h7, e8_chunk_08⟩
  have h9 := List.forall_append.mpr ⟨h8, e8_chunk_09⟩
  have h10 := List.forall_append.mpr ⟨h9, e8_chunk_10⟩
  have h11 := List.forall_append.mpr ⟨h10, e8_chunk_11⟩
  exact List.forall_iff_forall_mem.mp h11

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.a2_literal_sumsq
#print axioms VOA.AffineGeneral.Normalization.Certificate.d4_literal_sumsq
#print axioms VOA.AffineGeneral.Normalization.Certificate.e6_literal_sumsq
#print axioms VOA.AffineGeneral.Normalization.Certificate.e7_literal_sumsq
#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_literal_sumsq
