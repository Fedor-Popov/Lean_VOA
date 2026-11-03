import VOA.Classification.COne.OrbIcoWJetData
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
namespace VOA.Classification.COne.OrbIcoW
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac01_jet_recurrence : JetRecurrence false 1 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac01_jet_pivot : JetPivot false 1 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac02_jet_recurrence : JetRecurrence false 2 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac02_jet_pivot : JetPivot false 2 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac03_jet_recurrence : JetRecurrence false 3 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac03_jet_pivot : JetPivot false 3 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac04_jet_recurrence : JetRecurrence false 4 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac04_jet_pivot : JetPivot false 4 := by decide +kernel
end VOA.Classification.COne.OrbIcoW
