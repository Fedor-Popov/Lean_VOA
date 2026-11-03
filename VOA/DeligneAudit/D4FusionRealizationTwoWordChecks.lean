/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateAssembly
import VOA.DeligneAudit.D4FusionRealizationTwoWordCheck000N128
import VOA.DeligneAudit.D4FusionRealizationTwoWordCheck128N128
import VOA.DeligneAudit.D4FusionRealizationTwoWordCheck256N128
import VOA.DeligneAudit.D4FusionRealizationTwoWordCheck384N128
import VOA.DeligneAudit.D4FusionRealizationTwoWordCheck512N128
import VOA.DeligneAudit.D4FusionRealizationTwoWordCheck640N128
import VOA.DeligneAudit.D4FusionRealizationTwoWordCheck768N073
import VOA.DeligneAudit.D4FusionRealizationTwoColumnCheck000N004
import VOA.DeligneAudit.D4FusionRealizationTwoColumnCheck004N004
import VOA.DeligneAudit.D4FusionRealizationTwoColumnCheck008N004
import VOA.DeligneAudit.D4FusionRealizationTwoColumnCheck012N004
import VOA.DeligneAudit.D4FusionRealizationTwoColumnCheck016N004
import VOA.DeligneAudit.D4FusionRealizationTwoColumnCheck020N004
import VOA.DeligneAudit.D4FusionRealizationTwoColumnCheck024N004

namespace VOA.DeligneAudit.D4Two.Certificate

theorem word_checks_all :
    (List.range' 0 841).all (fun i => wordMetaCheck i && wordStepCheck i) = true :=
  (cert_range_join 0 384 384 457 841 rfl rfl
      (cert_range_join 0 128 128 256 384 rfl rfl
      sionrealizationtwowordcheck_000_128
      (cert_range_join 128 128 256 128 256 rfl rfl
      sionrealizationtwowordcheck_128_128
      sionrealizationtwowordcheck_256_128))
      (cert_range_join 384 256 640 201 457 rfl rfl
      (cert_range_join 384 128 512 128 256 rfl rfl
      sionrealizationtwowordcheck_384_128
      sionrealizationtwowordcheck_512_128)
      (cert_range_join 640 128 768 73 201 rfl rfl
      sionrealizationtwowordcheck_640_128
      sionrealizationtwowordcheck_768_073)))

theorem column_checks_all : (List.range' 0 28).all columnCheck = true :=
  (cert_range_join 0 12 12 16 28 rfl rfl
      (cert_range_join 0 4 4 8 12 rfl rfl
      sionrealizationtwocolumncheck_000_004
      (cert_range_join 4 4 8 4 8 rfl rfl
      sionrealizationtwocolumncheck_004_004
      sionrealizationtwocolumncheck_008_004))
      (cert_range_join 12 8 20 8 16 rfl rfl
      (cert_range_join 12 4 16 4 8 rfl rfl
      sionrealizationtwocolumncheck_012_004
      sionrealizationtwocolumncheck_016_004)
      (cert_range_join 20 4 24 4 8 rfl rfl
      sionrealizationtwocolumncheck_020_004
      sionrealizationtwocolumncheck_024_004)))

end VOA.DeligneAudit.D4Two.Certificate

#print axioms VOA.DeligneAudit.D4Two.Certificate.word_checks_all
#print axioms VOA.DeligneAudit.D4Two.Certificate.column_checks_all
