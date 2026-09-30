import ThetaFinite
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace Nanuq.Theta
#eval checkTemplate ⟨1,1,1,1⟩
theorem probe_six : checkTemplate ⟨1,1,1,1⟩ = true := by decide +kernel
#print axioms probe_six
end Nanuq.Theta
