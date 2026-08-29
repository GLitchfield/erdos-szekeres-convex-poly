module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 031. -/

def SynchronizedFiveFanFin11OriginalAtom1824 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {2, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1825 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 9, 10} ∧
    ¬IsCapSet chi {2, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1826 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 7} ∧
    ¬IsCapSet chi {3, 4, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1827 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 8} ∧
    ¬IsCapSet chi {3, 4, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1828 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 9} ∧
    ¬IsCapSet chi {3, 4, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1829 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 10} ∧
    ¬IsCapSet chi {3, 4, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1830 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 8} ∧
    ¬IsCapSet chi {3, 4, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1831 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 9} ∧
    ¬IsCapSet chi {3, 4, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1832 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 10} ∧
    ¬IsCapSet chi {3, 4, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1833 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 9} ∧
    ¬IsCapSet chi {3, 4, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1834 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 10} ∧
    ¬IsCapSet chi {3, 4, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1835 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 10} ∧
    ¬IsCapSet chi {3, 4, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1836 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 8} ∧
    ¬IsCapSet chi {3, 4, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1837 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 9} ∧
    ¬IsCapSet chi {3, 4, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1838 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 10} ∧
    ¬IsCapSet chi {3, 4, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1839 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 9} ∧
    ¬IsCapSet chi {3, 4, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1840 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 10} ∧
    ¬IsCapSet chi {3, 4, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1841 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 10} ∧
    ¬IsCapSet chi {3, 4, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1842 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 9} ∧
    ¬IsCapSet chi {3, 4, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1843 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 10} ∧
    ¬IsCapSet chi {3, 4, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1844 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 10} ∧
    ¬IsCapSet chi {3, 4, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1845 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 10} ∧
    ¬IsCapSet chi {3, 4, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1846 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 8} ∧
    ¬IsCapSet chi {3, 5, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1847 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 9} ∧
    ¬IsCapSet chi {3, 5, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1848 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 10} ∧
    ¬IsCapSet chi {3, 5, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1849 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 9} ∧
    ¬IsCapSet chi {3, 5, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1850 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 10} ∧
    ¬IsCapSet chi {3, 5, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1851 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 10} ∧
    ¬IsCapSet chi {3, 5, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1852 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 9} ∧
    ¬IsCapSet chi {3, 5, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1853 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 10} ∧
    ¬IsCapSet chi {3, 5, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1854 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 10} ∧
    ¬IsCapSet chi {3, 5, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1855 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 10} ∧
    ¬IsCapSet chi {3, 5, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1856 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 9} ∧
    ¬IsCapSet chi {3, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1857 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 10} ∧
    ¬IsCapSet chi {3, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1858 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {3, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1859 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {3, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1860 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 9, 10} ∧
    ¬IsCapSet chi {3, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1861 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 8} ∧
    ¬IsCapSet chi {4, 5, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1862 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 9} ∧
    ¬IsCapSet chi {4, 5, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1863 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 10} ∧
    ¬IsCapSet chi {4, 5, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1864 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 9} ∧
    ¬IsCapSet chi {4, 5, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1865 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 10} ∧
    ¬IsCapSet chi {4, 5, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1866 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 10} ∧
    ¬IsCapSet chi {4, 5, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1867 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 9} ∧
    ¬IsCapSet chi {4, 5, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1868 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 10} ∧
    ¬IsCapSet chi {4, 5, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1869 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 10} ∧
    ¬IsCapSet chi {4, 5, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1870 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 10} ∧
    ¬IsCapSet chi {4, 5, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1871 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 9} ∧
    ¬IsCapSet chi {4, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1872 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 10} ∧
    ¬IsCapSet chi {4, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1873 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {4, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1874 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {4, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1875 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 10} ∧
    ¬IsCapSet chi {4, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1876 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 9} ∧
    ¬IsCapSet chi {5, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1877 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 10} ∧
    ¬IsCapSet chi {5, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1878 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {5, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1879 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {5, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1880 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 10} ∧
    ¬IsCapSet chi {5, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1881 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 10} ∧
    ¬IsCapSet chi {6, 7, 8, 9, 10}

end ErdosSzekeres

end
