module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk078
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk079

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 102. -/

theorem predecessorHalfFin13_rejectSemanticSegment102
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) ∨
      ((PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) ∨
      (PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi))) ∨
      ((PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) ∨
      ((¬PredecessorHalfFin13Atom2005 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      (PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi)))) ∨
      (((PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) ∨
      ((PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) ∨
      (PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi))) ∨
      ((PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) ∨
      ((¬PredecessorHalfFin13Atom2006 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0971 chi) ∨
      (PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi))))) ∨
      ((((PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) ∨
      ((PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi) ∨
      (PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi))) ∨
      ((PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) ∨
      ((PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) ∨
      (PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi)))) ∨
      (((PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) ∨
      ((PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) ∨
      (PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi))) ∨
      ((¬PredecessorHalfFin13Atom2008 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0973 chi) ∨
      ((PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) ∨
      (PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi) ∨
      ((PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) ∨
      (PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi))) ∨
      ((¬PredecessorHalfFin13Atom2009 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0760 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0974 chi) ∨
      ((PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) ∨
      (PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi)))) ∨
      (((PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) ∨
      ((PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) ∨
      (PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi))) ∨
      ((¬PredecessorHalfFin13Atom2010 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0975 chi) ∨
      ((PredecessorHalfFin13Atom2011 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) ∨
      (PredecessorHalfFin13Atom2011 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi))))) ∨
      ((((PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) ∨
      ((PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) ∨
      (PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi))) ∨
      ((PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) ∨
      ((PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) ∨
      (¬PredecessorHalfFin13Atom2012 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0977 chi)))) ∨
      (((PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) ∨
      ((PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi) ∨
      (PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi))) ∨
      (((PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) ∨
      (PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi)) ∨
      ((PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) ∨
      (PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) ∨
      ((PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) ∨
      (PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi))) ∨
      ((¬PredecessorHalfFin13Atom2014 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0979 chi) ∨
      ((PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) ∨
      (PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi)))) ∨
      (((PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi) ∨
      ((PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) ∨
      (PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi))) ∨
      ((PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) ∨
      ((PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) ∨
      (PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi))))) ∨
      ((((PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) ∨
      ((PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) ∨
      (¬PredecessorHalfFin13Atom2016 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0981 chi))) ∨
      ((PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) ∨
      ((PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom0787 chi) ∨
      (PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi)))) ∨
      (((PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) ∨
      ((PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi) ∨
      (PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi))) ∨
      ((PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) ∨
      ((PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) ∨
      (PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) ∨
      ((PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) ∨
      (PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi))) ∨
      ((PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) ∨
      ((¬PredecessorHalfFin13Atom2019 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0984 chi) ∨
      (PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi)))) ∨
      (((PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) ∨
      ((PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) ∨
      (PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi))) ∨
      ((PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) ∨
      ((PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) ∨
      (PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi))))) ∨
      ((((PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) ∨
      ((PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) ∨
      (PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi))) ∨
      ((PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) ∨
      ((¬PredecessorHalfFin13Atom2022 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      (PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi)))) ∨
      (((PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi) ∨
      ((PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi) ∨
      (PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi))) ∨
      (((PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) ∨
      (PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi)) ∨
      ((PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) ∨
      (PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi))))))))) := by
  intro hbad
  rcases hbad with hbad | hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23180 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23181 chi hbad
              ·
                exact predecessorHalfFin13_clause23182 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23183 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23184 chi hbad
              ·
                exact predecessorHalfFin13_clause23185 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23186 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23187 chi hbad
              ·
                exact predecessorHalfFin13_clause23188 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23189 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23190 chi hbad
              ·
                exact predecessorHalfFin13_clause23191 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23192 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23193 chi hbad
              ·
                exact predecessorHalfFin13_clause23194 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23195 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23197 chi hbad
              ·
                exact predecessorHalfFin13_clause23198 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23199 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23200 chi hbad
              ·
                exact predecessorHalfFin13_clause23201 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23202 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23203 chi hbad
              ·
                exact predecessorHalfFin13_clause23204 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23205 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23206 chi hbad
              ·
                exact predecessorHalfFin13_clause23207 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23208 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23209 chi hbad
              ·
                exact predecessorHalfFin13_clause23210 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23211 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23212 chi hbad
              ·
                exact predecessorHalfFin13_clause23213 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23214 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23215 chi hbad
              ·
                exact predecessorHalfFin13_clause23216 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23221 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23222 chi hbad
              ·
                exact predecessorHalfFin13_clause23223 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23224 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23225 chi hbad
              ·
                exact predecessorHalfFin13_clause23226 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23227 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23228 chi hbad
              ·
                exact predecessorHalfFin13_clause23229 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23230 chi hbad
              ·
                exact predecessorHalfFin13_clause23231 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23233 chi hbad
              ·
                exact predecessorHalfFin13_clause23234 chi hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23235 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23236 chi hbad
              ·
                exact predecessorHalfFin13_clause23237 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23238 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23239 chi hbad
              ·
                exact predecessorHalfFin13_clause23240 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23241 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23242 chi hbad
              ·
                exact predecessorHalfFin13_clause23243 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23245 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23246 chi hbad
              ·
                exact predecessorHalfFin13_clause23247 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23248 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23249 chi hbad
              ·
                exact predecessorHalfFin13_clause23250 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23252 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23254 chi hbad
              ·
                exact predecessorHalfFin13_clause23255 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23257 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23258 chi hbad
              ·
                exact predecessorHalfFin13_clause23259 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23260 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23261 chi hbad
              ·
                exact predecessorHalfFin13_clause23263 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23264 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23265 chi hbad
              ·
                exact predecessorHalfFin13_clause23266 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23267 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23268 chi hbad
              ·
                exact predecessorHalfFin13_clause23270 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23272 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23273 chi hbad
              ·
                exact predecessorHalfFin13_clause23276 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23278 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23279 chi hbad
              ·
                exact predecessorHalfFin13_clause23281 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23282 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23283 chi hbad
              ·
                exact predecessorHalfFin13_clause23284 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23285 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23286 chi hbad
              ·
                exact predecessorHalfFin13_clause23287 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23288 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23289 chi hbad
              ·
                exact predecessorHalfFin13_clause23290 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23291 chi hbad
              ·
                exact predecessorHalfFin13_clause23293 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23294 chi hbad
              ·
                exact predecessorHalfFin13_clause23295 chi hbad

end ErdosSzekeres

end
