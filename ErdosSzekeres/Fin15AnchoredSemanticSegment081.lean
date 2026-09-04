module

public import ErdosSzekeres.Fin15AnchoredClauseChunk159
public import ErdosSzekeres.Fin15AnchoredClauseChunk160
public import ErdosSzekeres.Fin15AnchoredClauseChunk161

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 081. -/

theorem fin15Anchored_rejectSemanticSegment081
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom1131 chi) ∨
      ((¬Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom1131 chi) ∨
      (Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom0822 chi))) ∨
      (((Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom0830 chi) ∨
      (Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom0857 chi)) ∨
      ((Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom0912 chi) ∨
      (Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom1132 chi)))) ∨
      ((((¬Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom1132 chi) ∨
      (Fin15AnchoredAtom2849 chi ∧
      ¬Fin15AnchoredAtom0823 chi)) ∨
      ((¬Fin15AnchoredAtom2849 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0824 chi ∧
      Fin15AnchoredAtom0858 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom1133 chi) ∨
      (Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom0823 chi))) ∨
      (((Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom0825 chi) ∨
      (Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom0859 chi)) ∨
      ((Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom0914 chi) ∨
      (Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom1134 chi))))) ∨
      (((((¬Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom1134 chi) ∨
      (Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom0823 chi)) ∨
      ((Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom0826 chi) ∨
      (Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom0860 chi))) ∨
      (((Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom0915 chi) ∨
      (Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom1135 chi)) ∨
      ((¬Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom1135 chi) ∨
      (Fin15AnchoredAtom2852 chi ∧
      ¬Fin15AnchoredAtom0823 chi)))) ∨
      ((((Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom0823 chi) ∨
      (Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom0828 chi)) ∨
      ((Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom0862 chi) ∨
      (Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom0917 chi))) ∨
      (((Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom1137 chi) ∨
      (¬Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom1137 chi)) ∨
      ((Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom0823 chi) ∨
      (Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom0829 chi)))))) ∨
      ((((((Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom0863 chi) ∨
      (Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom0918 chi)) ∨
      ((Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom1138 chi) ∨
      (¬Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom1138 chi))) ∨
      (((Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom0823 chi) ∨
      (Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom0830 chi)) ∨
      ((Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom0864 chi) ∨
      (Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom0919 chi)))) ∨
      ((((Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom1139 chi) ∨
      (¬Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom1139 chi)) ∨
      ((Fin15AnchoredAtom2857 chi ∧
      ¬Fin15AnchoredAtom0826 chi) ∨
      (¬Fin15AnchoredAtom2857 chi ∧
      Fin15AnchoredAtom0824 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0866 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom1141 chi))) ∨
      (((Fin15AnchoredAtom2859 chi ∧
      ¬Fin15AnchoredAtom0828 chi) ∨
      (¬Fin15AnchoredAtom2859 chi ∧
      Fin15AnchoredAtom0824 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0868 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom1143 chi)) ∨
      ((Fin15AnchoredAtom2860 chi ∧
      ¬Fin15AnchoredAtom0829 chi) ∨
      (Fin15AnchoredAtom2861 chi ∧
      ¬Fin15AnchoredAtom0830 chi))))) ∨
      (((((Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom0825 chi) ∨
      (Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom0826 chi)) ∨
      ((Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom0871 chi) ∨
      (Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom0926 chi))) ∨
      (((Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom1146 chi) ∨
      (¬Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom1146 chi)) ∨
      ((Fin15AnchoredAtom2863 chi ∧
      ¬Fin15AnchoredAtom0825 chi) ∨
      (Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom0825 chi)))) ∨
      ((((Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom0828 chi) ∨
      (Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom0873 chi)) ∨
      ((Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom0928 chi) ∨
      (Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom1148 chi))) ∨
      (((¬Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom1148 chi) ∨
      (Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom0825 chi)) ∨
      ((Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom0829 chi) ∨
      (Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom0874 chi))))))) ∨
      ((((((Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom0929 chi) ∨
      ((Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom1149 chi) ∨
      (¬Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom1149 chi))) ∨
      (((Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom0825 chi) ∨
      (Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom0830 chi)) ∨
      ((Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom0875 chi) ∨
      (Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom0930 chi)))) ∨
      ((((Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom1150 chi) ∨
      (¬Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom1150 chi)) ∨
      ((Fin15AnchoredAtom2867 chi ∧
      ¬Fin15AnchoredAtom1151 chi) ∨
      (¬Fin15AnchoredAtom2867 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0827 chi ∧
      Fin15AnchoredAtom0876 chi ∧
      Fin15AnchoredAtom0931 chi ∧
      Fin15AnchoredAtom1151 chi))) ∨
      (((Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom0826 chi) ∨
      (Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom0828 chi)) ∨
      ((Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom0877 chi) ∨
      (Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom0932 chi))))) ∨
      (((((Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom1152 chi) ∨
      (¬Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1152 chi)) ∨
      ((Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom0826 chi) ∨
      (Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom0829 chi))) ∨
      (((Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom0878 chi) ∨
      (Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom0933 chi)) ∨
      ((Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom1153 chi) ∨
      (¬Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1153 chi)))) ∨
      ((((Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom0826 chi) ∨
      (Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom0830 chi)) ∨
      ((Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom0879 chi) ∨
      (Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom0934 chi))) ∨
      (((Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom1154 chi) ∨
      (¬Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1154 chi)) ∨
      ((¬Fin15AnchoredAtom2872 chi ∧
      Fin15AnchoredAtom0827 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0881 chi ∧
      Fin15AnchoredAtom0936 chi ∧
      Fin15AnchoredAtom1156 chi) ∨
      (Fin15AnchoredAtom2873 chi ∧
      ¬Fin15AnchoredAtom0827 chi)))))) ∨
      ((((((Fin15AnchoredAtom2873 chi ∧
      ¬Fin15AnchoredAtom0830 chi) ∨
      (Fin15AnchoredAtom2873 chi ∧
      ¬Fin15AnchoredAtom0882 chi)) ∨
      ((¬Fin15AnchoredAtom2873 chi ∧
      Fin15AnchoredAtom0827 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0882 chi ∧
      Fin15AnchoredAtom0937 chi ∧
      Fin15AnchoredAtom1157 chi) ∨
      (Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom0828 chi))) ∨
      (((Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom0829 chi) ∨
      (Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom0883 chi)) ∨
      ((Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom0938 chi) ∨
      (Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom1158 chi)))) ∨
      ((((¬Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1158 chi) ∨
      (Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom0828 chi)) ∨
      ((Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom0830 chi) ∨
      (Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom0884 chi))) ∨
      (((Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom0939 chi) ∨
      (Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom1159 chi)) ∨
      ((¬Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1159 chi) ∨
      (Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom0829 chi))))) ∨
      (((((Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom0830 chi) ∨
      (Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom0885 chi)) ∨
      ((Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom0940 chi) ∨
      (Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom1160 chi))) ∨
      (((¬Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1160 chi) ∨
      (Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom0831 chi)) ∨
      ((Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom0832 chi) ∨
      (Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom0841 chi)))) ∨
      ((((Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom0941 chi) ∨
      (Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom1161 chi)) ∨
      ((¬Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom1161 chi) ∨
      (Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom0831 chi))) ∨
      (((Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom0833 chi) ∨
      (Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom0842 chi)) ∨
      ((Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom0942 chi) ∨
      (Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom1162 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom1162 chi) ∨
      ((Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom0831 chi) ∨
      (Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom0835 chi))) ∨
      (((Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom0844 chi) ∨
      (Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom0944 chi)) ∨
      ((Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom1164 chi) ∨
      (¬Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom1164 chi)))) ∨
      ((((Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom0831 chi) ∨
      (Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom0836 chi)) ∨
      ((Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom0845 chi) ∨
      (Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom0945 chi))) ∨
      (((Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom1165 chi) ∨
      (¬Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom1165 chi)) ∨
      ((Fin15AnchoredAtom2882 chi ∧
      ¬Fin15AnchoredAtom0831 chi) ∨
      (Fin15AnchoredAtom2882 chi ∧
      ¬Fin15AnchoredAtom0846 chi))))) ∨
      (((((Fin15AnchoredAtom2882 chi ∧
      ¬Fin15AnchoredAtom0946 chi) ∨
      (Fin15AnchoredAtom2882 chi ∧
      ¬Fin15AnchoredAtom1166 chi)) ∨
      ((¬Fin15AnchoredAtom2882 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0846 chi ∧
      Fin15AnchoredAtom0946 chi ∧
      Fin15AnchoredAtom1166 chi) ∨
      (Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom0831 chi))) ∨
      (((Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom0838 chi) ∨
      (Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom0847 chi)) ∨
      ((Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom0947 chi) ∨
      (Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom1167 chi)))) ∨
      ((((¬Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom1167 chi) ∨
      (Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom0831 chi)) ∨
      ((Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom0839 chi) ∨
      (Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom0848 chi))) ∨
      (((Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      (Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom1168 chi)) ∨
      ((¬Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom1168 chi) ∨
      (Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom0831 chi)))))) ∨
      ((((((Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom0840 chi) ∨
      (Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom0849 chi)) ∨
      ((Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom0949 chi) ∨
      (Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom1169 chi))) ∨
      (((¬Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom1169 chi) ∨
      (Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom0832 chi)) ∨
      ((Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom0833 chi) ∨
      (Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom0850 chi)))) ∨
      ((((Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom0950 chi) ∨
      (Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom1170 chi)) ∨
      ((¬Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom1170 chi) ∨
      (Fin15AnchoredAtom2887 chi ∧
      ¬Fin15AnchoredAtom0951 chi))) ∨
      (((Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom0832 chi) ∨
      (Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom0835 chi)) ∨
      ((Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom0852 chi) ∨
      (Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom0952 chi))))) ∨
      (((((Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom1172 chi) ∨
      (¬Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom1172 chi)) ∨
      ((Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom0832 chi) ∨
      (Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom0836 chi))) ∨
      (((Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom0853 chi) ∨
      (Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom0953 chi)) ∨
      ((Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom1173 chi) ∨
      (¬Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom1173 chi)))) ∨
      ((((Fin15AnchoredAtom2890 chi ∧
      ¬Fin15AnchoredAtom0832 chi) ∨
      (Fin15AnchoredAtom2890 chi ∧
      ¬Fin15AnchoredAtom0854 chi)) ∨
      ((¬Fin15AnchoredAtom2890 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0854 chi ∧
      Fin15AnchoredAtom0954 chi ∧
      Fin15AnchoredAtom1174 chi) ∨
      (Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom0832 chi))) ∨
      (((Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom0838 chi) ∨
      (Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom0855 chi)) ∨
      ((Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom1175 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom1175 chi) ∨
      ((Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom0832 chi) ∨
      (Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom0839 chi))) ∨
      (((Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom0856 chi) ∨
      (Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom0956 chi)) ∨
      ((Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom1176 chi) ∨
      (¬Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom1176 chi)))) ∨
      ((((Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom0832 chi) ∨
      (Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom0840 chi)) ∨
      ((Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom0857 chi) ∨
      (Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom0957 chi))) ∨
      (((Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom1177 chi) ∨
      (¬Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom1177 chi)) ∨
      ((Fin15AnchoredAtom2894 chi ∧
      ¬Fin15AnchoredAtom0833 chi) ∨
      (Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom0833 chi))))) ∨
      (((((Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom0835 chi) ∨
      (Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom0859 chi)) ∨
      ((Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom0959 chi) ∨
      (Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom1179 chi))) ∨
      (((¬Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom1179 chi) ∨
      (Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom0833 chi)) ∨
      ((Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom0836 chi) ∨
      (Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom0860 chi)))) ∨
      ((((Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom0960 chi) ∨
      (Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom1180 chi)) ∨
      ((¬Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom1180 chi) ∨
      (Fin15AnchoredAtom2897 chi ∧
      ¬Fin15AnchoredAtom0833 chi))) ∨
      (((Fin15AnchoredAtom2897 chi ∧
      ¬Fin15AnchoredAtom0961 chi) ∨
      (Fin15AnchoredAtom2897 chi ∧
      ¬Fin15AnchoredAtom1181 chi)) ∨
      ((Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom0833 chi) ∨
      (Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom0838 chi)))))) ∨
      ((((((Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom0862 chi) ∨
      (Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom0962 chi)) ∨
      ((Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (¬Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom1182 chi))) ∨
      (((Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom0833 chi) ∨
      (Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom0839 chi)) ∨
      ((Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom0863 chi) ∨
      (Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom0963 chi)))) ∨
      ((((Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom1183 chi) ∨
      (¬Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom1183 chi)) ∨
      ((Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom0833 chi) ∨
      (Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom0840 chi))) ∨
      (((Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom0864 chi) ∨
      (Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom0964 chi)) ∨
      ((Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom1184 chi) ∨
      (¬Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom1184 chi))))) ∨
      (((((¬Fin15AnchoredAtom2901 chi ∧
      Fin15AnchoredAtom0834 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0865 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom1185 chi) ∨
      (Fin15AnchoredAtom2906 chi ∧
      ¬Fin15AnchoredAtom0840 chi)) ∨
      ((¬Fin15AnchoredAtom2906 chi ∧
      Fin15AnchoredAtom0834 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0870 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom1190 chi) ∨
      (Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom0835 chi))) ∨
      (((Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom0836 chi) ∨
      (Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom0871 chi)) ∨
      ((Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom0971 chi) ∨
      (Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom1191 chi)))) ∨
      ((((¬Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1191 chi) ∨
      (Fin15AnchoredAtom2908 chi ∧
      ¬Fin15AnchoredAtom0835 chi)) ∨
      ((Fin15AnchoredAtom2908 chi ∧
      ¬Fin15AnchoredAtom0972 chi) ∨
      (¬Fin15AnchoredAtom2908 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0872 chi ∧
      Fin15AnchoredAtom0972 chi ∧
      Fin15AnchoredAtom1192 chi))) ∨
      (((Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom0835 chi) ∨
      (Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom0838 chi)) ∨
      ((Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom0873 chi) ∨
      (Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom0973 chi)))))))))) := by
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
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause20444 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20445 chi hbad
                ·
                  exact fin15Anchored_clause20446 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20447 chi hbad
                ·
                  exact fin15Anchored_clause20448 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20449 chi hbad
                ·
                  exact fin15Anchored_clause20450 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20451 chi hbad
                ·
                  exact fin15Anchored_clause20452 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20453 chi hbad
                ·
                  exact fin15Anchored_clause20454 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20455 chi hbad
                ·
                  exact fin15Anchored_clause20456 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20457 chi hbad
                ·
                  exact fin15Anchored_clause20458 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20459 chi hbad
                ·
                  exact fin15Anchored_clause20460 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20461 chi hbad
                ·
                  exact fin15Anchored_clause20462 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20463 chi hbad
                ·
                  exact fin15Anchored_clause20464 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20465 chi hbad
                ·
                  exact fin15Anchored_clause20466 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20467 chi hbad
                ·
                  exact fin15Anchored_clause20468 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20469 chi hbad
                ·
                  exact fin15Anchored_clause20470 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20471 chi hbad
                ·
                  exact fin15Anchored_clause20472 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20473 chi hbad
                ·
                  exact fin15Anchored_clause20474 chi hbad
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
                  exact fin15Anchored_clause20475 chi hbad
                ·
                  exact fin15Anchored_clause20476 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20477 chi hbad
                ·
                  exact fin15Anchored_clause20478 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20479 chi hbad
                ·
                  exact fin15Anchored_clause20480 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20481 chi hbad
                ·
                  exact fin15Anchored_clause20482 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20483 chi hbad
                ·
                  exact fin15Anchored_clause20484 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20485 chi hbad
                ·
                  exact fin15Anchored_clause20486 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20487 chi hbad
                ·
                  exact fin15Anchored_clause20488 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20489 chi hbad
                ·
                  exact fin15Anchored_clause20490 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20491 chi hbad
                ·
                  exact fin15Anchored_clause20492 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20493 chi hbad
                ·
                  exact fin15Anchored_clause20494 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20495 chi hbad
                ·
                  exact fin15Anchored_clause20496 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20497 chi hbad
                ·
                  exact fin15Anchored_clause20498 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20499 chi hbad
                ·
                  exact fin15Anchored_clause20500 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20501 chi hbad
                ·
                  exact fin15Anchored_clause20502 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20503 chi hbad
                ·
                  exact fin15Anchored_clause20504 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20505 chi hbad
                ·
                  exact fin15Anchored_clause20506 chi hbad
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
                exact fin15Anchored_clause20507 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20508 chi hbad
                ·
                  exact fin15Anchored_clause20509 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20510 chi hbad
                ·
                  exact fin15Anchored_clause20511 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20512 chi hbad
                ·
                  exact fin15Anchored_clause20513 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20514 chi hbad
                ·
                  exact fin15Anchored_clause20515 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20516 chi hbad
                ·
                  exact fin15Anchored_clause20517 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20518 chi hbad
                ·
                  exact fin15Anchored_clause20519 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20520 chi hbad
                ·
                  exact fin15Anchored_clause20521 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20522 chi hbad
                ·
                  exact fin15Anchored_clause20523 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20524 chi hbad
                ·
                  exact fin15Anchored_clause20525 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20526 chi hbad
                ·
                  exact fin15Anchored_clause20527 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20528 chi hbad
                ·
                  exact fin15Anchored_clause20529 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20530 chi hbad
                ·
                  exact fin15Anchored_clause20531 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20532 chi hbad
                ·
                  exact fin15Anchored_clause20533 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20534 chi hbad
                ·
                  exact fin15Anchored_clause20535 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20536 chi hbad
                ·
                  exact fin15Anchored_clause20537 chi hbad
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
                  exact fin15Anchored_clause20538 chi hbad
                ·
                  exact fin15Anchored_clause20539 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20540 chi hbad
                ·
                  exact fin15Anchored_clause20541 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20542 chi hbad
                ·
                  exact fin15Anchored_clause20543 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20544 chi hbad
                ·
                  exact fin15Anchored_clause20545 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20546 chi hbad
                ·
                  exact fin15Anchored_clause20547 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20548 chi hbad
                ·
                  exact fin15Anchored_clause20549 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20550 chi hbad
                ·
                  exact fin15Anchored_clause20551 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20552 chi hbad
                ·
                  exact fin15Anchored_clause20553 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20554 chi hbad
                ·
                  exact fin15Anchored_clause20555 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20556 chi hbad
                ·
                  exact fin15Anchored_clause20557 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20558 chi hbad
                ·
                  exact fin15Anchored_clause20559 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20560 chi hbad
                ·
                  exact fin15Anchored_clause20561 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20562 chi hbad
                ·
                  exact fin15Anchored_clause20563 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20564 chi hbad
                ·
                  exact fin15Anchored_clause20565 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20566 chi hbad
                ·
                  exact fin15Anchored_clause20567 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20568 chi hbad
                ·
                  exact fin15Anchored_clause20569 chi hbad
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
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause20570 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20571 chi hbad
                ·
                  exact fin15Anchored_clause20572 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20573 chi hbad
                ·
                  exact fin15Anchored_clause20574 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20575 chi hbad
                ·
                  exact fin15Anchored_clause20576 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20577 chi hbad
                ·
                  exact fin15Anchored_clause20578 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20579 chi hbad
                ·
                  exact fin15Anchored_clause20580 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20581 chi hbad
                ·
                  exact fin15Anchored_clause20582 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20583 chi hbad
                ·
                  exact fin15Anchored_clause20584 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20585 chi hbad
                ·
                  exact fin15Anchored_clause20586 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20587 chi hbad
                ·
                  exact fin15Anchored_clause20588 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20589 chi hbad
                ·
                  exact fin15Anchored_clause20590 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20591 chi hbad
                ·
                  exact fin15Anchored_clause20592 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20593 chi hbad
                ·
                  exact fin15Anchored_clause20594 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20595 chi hbad
                ·
                  exact fin15Anchored_clause20596 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20597 chi hbad
                ·
                  exact fin15Anchored_clause20598 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20599 chi hbad
                ·
                  exact fin15Anchored_clause20600 chi hbad
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
                  exact fin15Anchored_clause20601 chi hbad
                ·
                  exact fin15Anchored_clause20602 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20603 chi hbad
                ·
                  exact fin15Anchored_clause20604 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20605 chi hbad
                ·
                  exact fin15Anchored_clause20606 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20607 chi hbad
                ·
                  exact fin15Anchored_clause20608 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20609 chi hbad
                ·
                  exact fin15Anchored_clause20610 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20611 chi hbad
                ·
                  exact fin15Anchored_clause20612 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20613 chi hbad
                ·
                  exact fin15Anchored_clause20614 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20615 chi hbad
                ·
                  exact fin15Anchored_clause20616 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20617 chi hbad
                ·
                  exact fin15Anchored_clause20618 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20619 chi hbad
                ·
                  exact fin15Anchored_clause20620 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20621 chi hbad
                ·
                  exact fin15Anchored_clause20622 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20623 chi hbad
                ·
                  exact fin15Anchored_clause20624 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20625 chi hbad
                ·
                  exact fin15Anchored_clause20626 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20627 chi hbad
                ·
                  exact fin15Anchored_clause20628 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20629 chi hbad
                ·
                  exact fin15Anchored_clause20630 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20631 chi hbad
                ·
                  exact fin15Anchored_clause20632 chi hbad
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
                exact fin15Anchored_clause20633 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20634 chi hbad
                ·
                  exact fin15Anchored_clause20635 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20636 chi hbad
                ·
                  exact fin15Anchored_clause20637 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20638 chi hbad
                ·
                  exact fin15Anchored_clause20639 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20640 chi hbad
                ·
                  exact fin15Anchored_clause20641 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20642 chi hbad
                ·
                  exact fin15Anchored_clause20643 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20644 chi hbad
                ·
                  exact fin15Anchored_clause20645 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20646 chi hbad
                ·
                  exact fin15Anchored_clause20647 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20648 chi hbad
                ·
                  exact fin15Anchored_clause20649 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20650 chi hbad
                ·
                  exact fin15Anchored_clause20651 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20652 chi hbad
                ·
                  exact fin15Anchored_clause20653 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20654 chi hbad
                ·
                  exact fin15Anchored_clause20655 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20656 chi hbad
                ·
                  exact fin15Anchored_clause20657 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20658 chi hbad
                ·
                  exact fin15Anchored_clause20659 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20660 chi hbad
                ·
                  exact fin15Anchored_clause20661 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20662 chi hbad
                ·
                  exact fin15Anchored_clause20663 chi hbad
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
                  exact fin15Anchored_clause20664 chi hbad
                ·
                  exact fin15Anchored_clause20665 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20666 chi hbad
                ·
                  exact fin15Anchored_clause20667 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20668 chi hbad
                ·
                  exact fin15Anchored_clause20669 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20670 chi hbad
                ·
                  exact fin15Anchored_clause20671 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20672 chi hbad
                ·
                  exact fin15Anchored_clause20673 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20674 chi hbad
                ·
                  exact fin15Anchored_clause20675 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20676 chi hbad
                ·
                  exact fin15Anchored_clause20677 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20678 chi hbad
                ·
                  exact fin15Anchored_clause20679 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20680 chi hbad
                ·
                  exact fin15Anchored_clause20681 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20682 chi hbad
                ·
                  exact fin15Anchored_clause20683 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20684 chi hbad
                ·
                  exact fin15Anchored_clause20685 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20686 chi hbad
                ·
                  exact fin15Anchored_clause20687 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20688 chi hbad
                ·
                  exact fin15Anchored_clause20689 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20690 chi hbad
                ·
                  exact fin15Anchored_clause20691 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20692 chi hbad
                ·
                  exact fin15Anchored_clause20693 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20694 chi hbad
                ·
                  exact fin15Anchored_clause20695 chi hbad

end ErdosSzekeres

end
