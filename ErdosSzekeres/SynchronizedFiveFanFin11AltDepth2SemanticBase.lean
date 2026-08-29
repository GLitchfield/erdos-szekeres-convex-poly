module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticInterface

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

def Fin11AltDepth2StrongQuad
    (chi : TripleColoring 11) (a b c d : Fin 11)
    (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=
  chi ⟨a, b, c, hab, hbc⟩ = chi ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
    chi ⟨a, c, d, hab.trans hbc, hcd⟩ = chi ⟨b, c, d, hbc, hcd⟩

end ErdosSzekeres

end
