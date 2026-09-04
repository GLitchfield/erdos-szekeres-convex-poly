module

public import ErdosSzekeres.Fin15AnchoredClauseChunk161
public import ErdosSzekeres.Fin15AnchoredClauseChunk162
public import ErdosSzekeres.Fin15AnchoredClauseChunk163

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 082. -/

theorem fin15Anchored_rejectSemanticSegment082
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom1193 chi) ∨
      ((¬Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1193 chi) ∨
      (Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom0835 chi))) ∨
      (((Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom0839 chi) ∨
      (Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom0874 chi)) ∨
      ((Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom0974 chi) ∨
      (Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom1194 chi)))) ∨
      ((((¬Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1194 chi) ∨
      (Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom0835 chi)) ∨
      ((Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom0840 chi) ∨
      (Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom0875 chi))) ∨
      (((Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom1195 chi)) ∨
      ((¬Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1195 chi) ∨
      (Fin15AnchoredAtom2912 chi ∧
      ¬Fin15AnchoredAtom0836 chi))))) ∨
      (((((Fin15AnchoredAtom2912 chi ∧
      ¬Fin15AnchoredAtom0837 chi) ∨
      (Fin15AnchoredAtom2912 chi ∧
      ¬Fin15AnchoredAtom1196 chi)) ∨
      ((¬Fin15AnchoredAtom2912 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0876 chi ∧
      Fin15AnchoredAtom0976 chi ∧
      Fin15AnchoredAtom1196 chi) ∨
      (Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom0836 chi))) ∨
      (((Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom0838 chi) ∨
      (Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom0877 chi)) ∨
      ((Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom0977 chi) ∨
      (Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom1197 chi)))) ∨
      ((((¬Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1197 chi) ∨
      (Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom0836 chi)) ∨
      ((Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom0839 chi) ∨
      (Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom0878 chi))) ∨
      (((Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom0978 chi) ∨
      (Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom1198 chi)) ∨
      ((¬Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1198 chi) ∨
      (Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom0836 chi)))))) ∨
      ((((((Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom0840 chi) ∨
      (Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom0879 chi)) ∨
      ((Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom0979 chi) ∨
      (Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom1199 chi))) ∨
      (((¬Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1199 chi) ∨
      (Fin15AnchoredAtom2916 chi ∧
      ¬Fin15AnchoredAtom0838 chi)) ∨
      ((Fin15AnchoredAtom2916 chi ∧
      ¬Fin15AnchoredAtom0880 chi) ∨
      (¬Fin15AnchoredAtom2916 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0880 chi ∧
      Fin15AnchoredAtom0980 chi ∧
      Fin15AnchoredAtom1200 chi)))) ∨
      ((((Fin15AnchoredAtom2917 chi ∧
      ¬Fin15AnchoredAtom0881 chi) ∨
      (¬Fin15AnchoredAtom2917 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0881 chi ∧
      Fin15AnchoredAtom0981 chi ∧
      Fin15AnchoredAtom1201 chi)) ∨
      ((Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom0838 chi) ∨
      (Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom0839 chi))) ∨
      (((Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom0883 chi) ∨
      (Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom0983 chi)) ∨
      ((Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom1203 chi) ∨
      (¬Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1203 chi))))) ∨
      (((((Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom0838 chi) ∨
      (Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom0840 chi)) ∨
      ((Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom0884 chi) ∨
      (Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom0984 chi))) ∨
      (((Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom1204 chi) ∨
      (¬Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1204 chi)) ∨
      ((Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom0839 chi) ∨
      (Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom0840 chi)))) ∨
      ((((Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom0885 chi) ∨
      (Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom0985 chi)) ∨
      ((Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom1205 chi) ∨
      (¬Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1205 chi))) ∨
      (((Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom0841 chi) ∨
      (Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom0842 chi)) ∨
      ((Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom0850 chi) ∨
      (Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom0986 chi))))))) ∨
      ((((((Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom1206 chi) ∨
      ((¬Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom1206 chi) ∨
      (Fin15AnchoredAtom2923 chi ∧
      ¬Fin15AnchoredAtom0843 chi))) ∨
      (((¬Fin15AnchoredAtom2923 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0843 chi ∧
      Fin15AnchoredAtom0851 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom1207 chi) ∨
      (Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom0841 chi)) ∨
      ((Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom0844 chi) ∨
      (Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom0852 chi)))) ∨
      ((((Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom0988 chi) ∨
      (Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom1208 chi)) ∨
      ((¬Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom1208 chi) ∨
      (Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom0841 chi))) ∨
      (((Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom0845 chi) ∨
      (Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom0853 chi)) ∨
      ((Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom1209 chi))))) ∨
      (((((¬Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom1209 chi) ∨
      (Fin15AnchoredAtom2926 chi ∧
      ¬Fin15AnchoredAtom0841 chi)) ∨
      ((Fin15AnchoredAtom2926 chi ∧
      ¬Fin15AnchoredAtom1210 chi) ∨
      (¬Fin15AnchoredAtom2926 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0846 chi ∧
      Fin15AnchoredAtom0854 chi ∧
      Fin15AnchoredAtom0990 chi ∧
      Fin15AnchoredAtom1210 chi))) ∨
      (((Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom0841 chi) ∨
      (Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom0847 chi)) ∨
      ((Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom0855 chi) ∨
      (Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom0991 chi)))) ∨
      ((((Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom1211 chi) ∨
      (¬Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1211 chi)) ∨
      ((Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom0841 chi) ∨
      (Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom0848 chi))) ∨
      (((Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom0856 chi) ∨
      (Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom0992 chi)) ∨
      ((Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom1212 chi) ∨
      (¬Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1212 chi)))))) ∨
      ((((((Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom0841 chi) ∨
      (Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom0849 chi)) ∨
      ((Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom0857 chi) ∨
      (Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom0993 chi))) ∨
      (((Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom1213 chi) ∨
      (¬Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1213 chi)) ∨
      ((¬Fin15AnchoredAtom2930 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0843 chi ∧
      Fin15AnchoredAtom0858 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom1214 chi) ∨
      (Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom0842 chi)))) ∨
      ((((Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom0844 chi) ∨
      (Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom0859 chi)) ∨
      ((Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom0995 chi) ∨
      (Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom1215 chi))) ∨
      (((¬Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1215 chi) ∨
      (Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom0842 chi)) ∨
      ((Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom0845 chi) ∨
      (Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom0860 chi))))) ∨
      (((((Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom0996 chi) ∨
      (Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom1216 chi)) ∨
      ((¬Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1216 chi) ∨
      (Fin15AnchoredAtom2933 chi ∧
      ¬Fin15AnchoredAtom0842 chi))) ∨
      (((Fin15AnchoredAtom2933 chi ∧
      ¬Fin15AnchoredAtom1217 chi) ∨
      (Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom0842 chi)) ∨
      ((Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom0847 chi) ∨
      (Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom0862 chi)))) ∨
      ((((Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom0998 chi) ∨
      (Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom1218 chi)) ∨
      ((¬Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1218 chi) ∨
      (Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom0842 chi))) ∨
      (((Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom0848 chi) ∨
      (Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom0863 chi)) ∨
      ((Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom0999 chi) ∨
      (Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom1219 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1219 chi) ∨
      ((Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom0842 chi) ∨
      (Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom0849 chi))) ∨
      (((Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom0864 chi) ∨
      (Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom1000 chi)) ∨
      ((Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom1220 chi) ∨
      (¬Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1220 chi)))) ∨
      ((((¬Fin15AnchoredAtom2937 chi ∧
      Fin15AnchoredAtom0843 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0865 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1221 chi) ∨
      (Fin15AnchoredAtom2938 chi ∧
      ¬Fin15AnchoredAtom1222 chi)) ∨
      ((¬Fin15AnchoredAtom2938 chi ∧
      Fin15AnchoredAtom0843 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0866 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1222 chi) ∨
      (Fin15AnchoredAtom2940 chi ∧
      ¬Fin15AnchoredAtom0847 chi))) ∨
      (((Fin15AnchoredAtom2941 chi ∧
      ¬Fin15AnchoredAtom0848 chi) ∨
      (Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom0844 chi)) ∨
      ((Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom0845 chi) ∨
      (Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom0871 chi))))) ∨
      (((((Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom1227 chi)) ∨
      ((¬Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1227 chi) ∨
      (Fin15AnchoredAtom2944 chi ∧
      ¬Fin15AnchoredAtom0844 chi))) ∨
      (((Fin15AnchoredAtom2944 chi ∧
      ¬Fin15AnchoredAtom1008 chi) ∨
      (Fin15AnchoredAtom2944 chi ∧
      ¬Fin15AnchoredAtom1228 chi)) ∨
      ((¬Fin15AnchoredAtom2944 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0846 chi ∧
      Fin15AnchoredAtom0872 chi ∧
      Fin15AnchoredAtom1008 chi ∧
      Fin15AnchoredAtom1228 chi) ∨
      (Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom0844 chi)))) ∨
      ((((Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom0847 chi) ∨
      (Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom0873 chi)) ∨
      ((Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom1009 chi) ∨
      (Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom1229 chi))) ∨
      (((¬Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1229 chi) ∨
      (Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom0844 chi)) ∨
      ((Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom0848 chi) ∨
      (Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom0874 chi)))))) ∨
      ((((((Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom1010 chi) ∨
      (Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom1230 chi)) ∨
      ((¬Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1230 chi) ∨
      (Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom0844 chi))) ∨
      (((Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom0849 chi) ∨
      (Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom0875 chi)) ∨
      ((Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom1011 chi) ∨
      (Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom1231 chi)))) ∨
      ((((¬Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1231 chi) ∨
      (Fin15AnchoredAtom2948 chi ∧
      ¬Fin15AnchoredAtom0846 chi)) ∨
      ((Fin15AnchoredAtom2948 chi ∧
      ¬Fin15AnchoredAtom1232 chi) ∨
      (Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom0845 chi))) ∨
      (((Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom0847 chi) ∨
      (Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom0877 chi)) ∨
      ((Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom1013 chi) ∨
      (Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom1233 chi))))) ∨
      (((((¬Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1233 chi) ∨
      (Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom0845 chi)) ∨
      ((Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom0848 chi) ∨
      (Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom0878 chi))) ∨
      (((Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom1014 chi) ∨
      (Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom1234 chi)) ∨
      ((¬Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1234 chi) ∨
      (Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom0845 chi)))) ∨
      ((((Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom0849 chi) ∨
      (Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom0879 chi)) ∨
      ((Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom1015 chi) ∨
      (Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom1235 chi))) ∨
      (((¬Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1235 chi) ∨
      (Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom0847 chi)) ∨
      ((Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom0848 chi) ∨
      (Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom0883 chi))))))) ∨
      ((((((Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom1019 chi) ∨
      ((Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom1239 chi) ∨
      (¬Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1239 chi))) ∨
      (((Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom0847 chi) ∨
      (Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom0849 chi)) ∨
      ((Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom0884 chi) ∨
      (Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom1020 chi)))) ∨
      ((((Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom1240 chi) ∨
      (¬Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1240 chi)) ∨
      ((Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom0848 chi) ∨
      (Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom0849 chi))) ∨
      (((Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom0885 chi) ∨
      (Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom1021 chi)) ∨
      ((Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom1241 chi) ∨
      (¬Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1241 chi))))) ∨
      (((((Fin15AnchoredAtom2958 chi ∧
      ¬Fin15AnchoredAtom0850 chi) ∨
      (Fin15AnchoredAtom2958 chi ∧
      ¬Fin15AnchoredAtom1022 chi)) ∨
      ((¬Fin15AnchoredAtom2958 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0851 chi ∧
      Fin15AnchoredAtom0858 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1242 chi) ∨
      (Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom0850 chi))) ∨
      (((Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom0852 chi) ∨
      (Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom0859 chi)) ∨
      ((Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom1023 chi) ∨
      (Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom1243 chi)))) ∨
      ((((¬Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1243 chi) ∨
      (Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom0850 chi)) ∨
      ((Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom0853 chi) ∨
      (Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom0860 chi))) ∨
      (((Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom1024 chi) ∨
      (Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom1244 chi)) ∨
      ((¬Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1244 chi) ∨
      (Fin15AnchoredAtom2961 chi ∧
      ¬Fin15AnchoredAtom0850 chi)))))) ∨
      ((((((Fin15AnchoredAtom2961 chi ∧
      ¬Fin15AnchoredAtom1025 chi) ∨
      (Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom0850 chi)) ∨
      ((Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom0855 chi) ∨
      (Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom0862 chi))) ∨
      (((Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom1026 chi) ∨
      (Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom1246 chi)) ∨
      ((¬Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1246 chi) ∨
      (Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom0850 chi)))) ∨
      ((((Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom0856 chi) ∨
      (Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom0863 chi)) ∨
      ((Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom1027 chi) ∨
      (Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom1247 chi))) ∨
      (((¬Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1247 chi) ∨
      (Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom0850 chi)) ∨
      ((Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom0857 chi) ∨
      (Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom0864 chi))))) ∨
      (((((Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom1028 chi) ∨
      (Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom1248 chi)) ∨
      ((¬Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1248 chi) ∨
      (Fin15AnchoredAtom2965 chi ∧
      ¬Fin15AnchoredAtom0852 chi))) ∨
      (((¬Fin15AnchoredAtom2965 chi ∧
      Fin15AnchoredAtom0851 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0865 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1249 chi) ∨
      (Fin15AnchoredAtom2966 chi ∧
      ¬Fin15AnchoredAtom0853 chi)) ∨
      ((Fin15AnchoredAtom2966 chi ∧
      ¬Fin15AnchoredAtom0866 chi) ∨
      (¬Fin15AnchoredAtom2966 chi ∧
      Fin15AnchoredAtom0851 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0866 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1250 chi)))) ∨
      ((((Fin15AnchoredAtom2970 chi ∧
      ¬Fin15AnchoredAtom0857 chi) ∨
      (Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom0852 chi)) ∨
      ((Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom0853 chi) ∨
      (Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom0871 chi))) ∨
      (((Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom1035 chi) ∨
      (Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom1255 chi)) ∨
      ((¬Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1255 chi) ∨
      (Fin15AnchoredAtom2972 chi ∧
      ¬Fin15AnchoredAtom1036 chi)))))))))) := by
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
                exact fin15Anchored_clause20696 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20697 chi hbad
                ·
                  exact fin15Anchored_clause20698 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20699 chi hbad
                ·
                  exact fin15Anchored_clause20700 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20701 chi hbad
                ·
                  exact fin15Anchored_clause20702 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20703 chi hbad
                ·
                  exact fin15Anchored_clause20704 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20705 chi hbad
                ·
                  exact fin15Anchored_clause20706 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20707 chi hbad
                ·
                  exact fin15Anchored_clause20708 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20709 chi hbad
                ·
                  exact fin15Anchored_clause20710 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20711 chi hbad
                ·
                  exact fin15Anchored_clause20712 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20713 chi hbad
                ·
                  exact fin15Anchored_clause20714 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20715 chi hbad
                ·
                  exact fin15Anchored_clause20716 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20717 chi hbad
                ·
                  exact fin15Anchored_clause20718 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20719 chi hbad
                ·
                  exact fin15Anchored_clause20720 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20721 chi hbad
                ·
                  exact fin15Anchored_clause20722 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20723 chi hbad
                ·
                  exact fin15Anchored_clause20724 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20725 chi hbad
                ·
                  exact fin15Anchored_clause20726 chi hbad
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
                  exact fin15Anchored_clause20727 chi hbad
                ·
                  exact fin15Anchored_clause20728 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20729 chi hbad
                ·
                  exact fin15Anchored_clause20730 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20731 chi hbad
                ·
                  exact fin15Anchored_clause20732 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20733 chi hbad
                ·
                  exact fin15Anchored_clause20734 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20735 chi hbad
                ·
                  exact fin15Anchored_clause20736 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20737 chi hbad
                ·
                  exact fin15Anchored_clause20738 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20739 chi hbad
                ·
                  exact fin15Anchored_clause20740 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20741 chi hbad
                ·
                  exact fin15Anchored_clause20742 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20743 chi hbad
                ·
                  exact fin15Anchored_clause20744 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20745 chi hbad
                ·
                  exact fin15Anchored_clause20746 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20747 chi hbad
                ·
                  exact fin15Anchored_clause20748 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20749 chi hbad
                ·
                  exact fin15Anchored_clause20750 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20751 chi hbad
                ·
                  exact fin15Anchored_clause20752 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20753 chi hbad
                ·
                  exact fin15Anchored_clause20754 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20755 chi hbad
                ·
                  exact fin15Anchored_clause20756 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20757 chi hbad
                ·
                  exact fin15Anchored_clause20758 chi hbad
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
                exact fin15Anchored_clause20759 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20760 chi hbad
                ·
                  exact fin15Anchored_clause20761 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20762 chi hbad
                ·
                  exact fin15Anchored_clause20763 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20764 chi hbad
                ·
                  exact fin15Anchored_clause20765 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20766 chi hbad
                ·
                  exact fin15Anchored_clause20767 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20768 chi hbad
                ·
                  exact fin15Anchored_clause20769 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20770 chi hbad
                ·
                  exact fin15Anchored_clause20771 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20772 chi hbad
                ·
                  exact fin15Anchored_clause20773 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20774 chi hbad
                ·
                  exact fin15Anchored_clause20775 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20776 chi hbad
                ·
                  exact fin15Anchored_clause20777 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20778 chi hbad
                ·
                  exact fin15Anchored_clause20779 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20780 chi hbad
                ·
                  exact fin15Anchored_clause20781 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20782 chi hbad
                ·
                  exact fin15Anchored_clause20783 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20784 chi hbad
                ·
                  exact fin15Anchored_clause20785 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20786 chi hbad
                ·
                  exact fin15Anchored_clause20787 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20788 chi hbad
                ·
                  exact fin15Anchored_clause20789 chi hbad
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
                  exact fin15Anchored_clause20790 chi hbad
                ·
                  exact fin15Anchored_clause20791 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20792 chi hbad
                ·
                  exact fin15Anchored_clause20793 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20794 chi hbad
                ·
                  exact fin15Anchored_clause20795 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20796 chi hbad
                ·
                  exact fin15Anchored_clause20797 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20798 chi hbad
                ·
                  exact fin15Anchored_clause20799 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20800 chi hbad
                ·
                  exact fin15Anchored_clause20801 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20802 chi hbad
                ·
                  exact fin15Anchored_clause20803 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20804 chi hbad
                ·
                  exact fin15Anchored_clause20805 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20806 chi hbad
                ·
                  exact fin15Anchored_clause20807 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20808 chi hbad
                ·
                  exact fin15Anchored_clause20809 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20810 chi hbad
                ·
                  exact fin15Anchored_clause20811 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20812 chi hbad
                ·
                  exact fin15Anchored_clause20813 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20814 chi hbad
                ·
                  exact fin15Anchored_clause20815 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20816 chi hbad
                ·
                  exact fin15Anchored_clause20817 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20818 chi hbad
                ·
                  exact fin15Anchored_clause20819 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20820 chi hbad
                ·
                  exact fin15Anchored_clause20821 chi hbad
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
                exact fin15Anchored_clause20822 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20823 chi hbad
                ·
                  exact fin15Anchored_clause20824 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20825 chi hbad
                ·
                  exact fin15Anchored_clause20826 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20827 chi hbad
                ·
                  exact fin15Anchored_clause20828 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20829 chi hbad
                ·
                  exact fin15Anchored_clause20830 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20831 chi hbad
                ·
                  exact fin15Anchored_clause20832 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20833 chi hbad
                ·
                  exact fin15Anchored_clause20834 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20835 chi hbad
                ·
                  exact fin15Anchored_clause20836 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20837 chi hbad
                ·
                  exact fin15Anchored_clause20838 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20839 chi hbad
                ·
                  exact fin15Anchored_clause20840 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20841 chi hbad
                ·
                  exact fin15Anchored_clause20842 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20843 chi hbad
                ·
                  exact fin15Anchored_clause20844 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20845 chi hbad
                ·
                  exact fin15Anchored_clause20846 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20847 chi hbad
                ·
                  exact fin15Anchored_clause20848 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20849 chi hbad
                ·
                  exact fin15Anchored_clause20850 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20851 chi hbad
                ·
                  exact fin15Anchored_clause20852 chi hbad
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
                  exact fin15Anchored_clause20853 chi hbad
                ·
                  exact fin15Anchored_clause20854 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20855 chi hbad
                ·
                  exact fin15Anchored_clause20856 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20857 chi hbad
                ·
                  exact fin15Anchored_clause20858 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20859 chi hbad
                ·
                  exact fin15Anchored_clause20860 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20861 chi hbad
                ·
                  exact fin15Anchored_clause20862 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20863 chi hbad
                ·
                  exact fin15Anchored_clause20864 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20865 chi hbad
                ·
                  exact fin15Anchored_clause20866 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20867 chi hbad
                ·
                  exact fin15Anchored_clause20868 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20869 chi hbad
                ·
                  exact fin15Anchored_clause20870 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20871 chi hbad
                ·
                  exact fin15Anchored_clause20872 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20873 chi hbad
                ·
                  exact fin15Anchored_clause20874 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20875 chi hbad
                ·
                  exact fin15Anchored_clause20876 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20877 chi hbad
                ·
                  exact fin15Anchored_clause20878 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20879 chi hbad
                ·
                  exact fin15Anchored_clause20880 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20881 chi hbad
                ·
                  exact fin15Anchored_clause20882 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20883 chi hbad
                ·
                  exact fin15Anchored_clause20884 chi hbad
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
                exact fin15Anchored_clause20885 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20886 chi hbad
                ·
                  exact fin15Anchored_clause20887 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20888 chi hbad
                ·
                  exact fin15Anchored_clause20889 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20890 chi hbad
                ·
                  exact fin15Anchored_clause20891 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20892 chi hbad
                ·
                  exact fin15Anchored_clause20893 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20894 chi hbad
                ·
                  exact fin15Anchored_clause20895 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20896 chi hbad
                ·
                  exact fin15Anchored_clause20897 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20898 chi hbad
                ·
                  exact fin15Anchored_clause20899 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20900 chi hbad
                ·
                  exact fin15Anchored_clause20901 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20902 chi hbad
                ·
                  exact fin15Anchored_clause20903 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20904 chi hbad
                ·
                  exact fin15Anchored_clause20905 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20906 chi hbad
                ·
                  exact fin15Anchored_clause20907 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20908 chi hbad
                ·
                  exact fin15Anchored_clause20909 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20910 chi hbad
                ·
                  exact fin15Anchored_clause20911 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20912 chi hbad
                ·
                  exact fin15Anchored_clause20913 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20914 chi hbad
                ·
                  exact fin15Anchored_clause20915 chi hbad
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
                  exact fin15Anchored_clause20916 chi hbad
                ·
                  exact fin15Anchored_clause20917 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20918 chi hbad
                ·
                  exact fin15Anchored_clause20919 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20920 chi hbad
                ·
                  exact fin15Anchored_clause20921 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20922 chi hbad
                ·
                  exact fin15Anchored_clause20923 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20924 chi hbad
                ·
                  exact fin15Anchored_clause20925 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20926 chi hbad
                ·
                  exact fin15Anchored_clause20927 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20928 chi hbad
                ·
                  exact fin15Anchored_clause20929 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20930 chi hbad
                ·
                  exact fin15Anchored_clause20931 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20932 chi hbad
                ·
                  exact fin15Anchored_clause20933 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20934 chi hbad
                ·
                  exact fin15Anchored_clause20935 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20936 chi hbad
                ·
                  exact fin15Anchored_clause20937 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20938 chi hbad
                ·
                  exact fin15Anchored_clause20939 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20940 chi hbad
                ·
                  exact fin15Anchored_clause20941 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20942 chi hbad
                ·
                  exact fin15Anchored_clause20943 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20944 chi hbad
                ·
                  exact fin15Anchored_clause20945 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20946 chi hbad
                ·
                  exact fin15Anchored_clause20947 chi hbad

end ErdosSzekeres

end
