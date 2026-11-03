import VOA.Classification.COne.OrbIcoWRecVac06
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
namespace VOA.Classification.COne.OrbIcoW
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac29_jet_recurrence : JetRecurrence false 29 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac29_jet_pivot : JetPivot false 29 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac30_jet_recurrence : JetRecurrence false 30 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac30_jet_pivot : JetPivot false 30 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac31_jet_recurrence : JetRecurrence false 31 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac31_jet_pivot : JetPivot false 31 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac32_jet_recurrence : JetRecurrence false 32 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac32_jet_pivot : JetPivot false 32 := by decide +kernel
end VOA.Classification.COne.OrbIcoW
