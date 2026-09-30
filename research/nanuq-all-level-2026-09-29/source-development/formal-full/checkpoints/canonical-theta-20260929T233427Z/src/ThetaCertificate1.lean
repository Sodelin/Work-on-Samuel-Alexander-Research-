import ThetaFiniteSoundness

set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Nanuq.Theta

/- Each assertion is checked by kernel reduction of the executable
switching/quartet evaluator. This generator supplies no metric answers. -/

theorem checked_0_0_0_1 : checkTemplate ⟨0,0,0,1⟩ = true := by decide +kernel
theorem checked_0_0_1_0 : checkTemplate ⟨0,0,1,0⟩ = true := by decide +kernel
theorem checked_0_1_0_0 : checkTemplate ⟨0,1,0,0⟩ = true := by decide +kernel
theorem checked_1_0_0_0 : checkTemplate ⟨1,0,0,0⟩ = true := by decide +kernel
#check checked_1_0_0_0

#print axioms checked_1_0_0_0
end Nanuq.Theta
