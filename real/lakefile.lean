import Lake
open Lake DSL

package samuel_alexander_real

require samuel_alexander_research from ".."
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib RealBridges

@[default_target]
lean_lib PortEncoding

@[default_target]
lean_lib StatefulCAReal
