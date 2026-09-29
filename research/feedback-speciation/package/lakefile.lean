import Lake
open Lake DSL

package feedback_speciation

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib SamuelAlexanderResearch where
  srcDir := "vendor"
  roots := #[`SamuelAlexanderResearch.SpeciesGlobalIAP]

@[default_target] lean_lib AncestryMixing
@[default_target] lean_lib AncestryExamples
@[default_target] lean_lib FeedbackDynamics
@[default_target] lean_lib FogartyAffinity
@[default_target] lean_lib FogartyAffinityFixation
