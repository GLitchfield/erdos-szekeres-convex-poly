import Mathlib
import Hammer

namespace ErdosSzekeres

/--
Build-gated check that the pinned LeanHammer stack is operational without
contacting the remote premise selector. The suggested replacement proof is
expected to be an ordinary Lean tactic script checked by the kernel.
-/
theorem hammerOfflineSmoke (n : ℕ) : n + 0 = n := by
  hammer {aesopPremises := 0, autoPremises := 0}

end ErdosSzekeres
