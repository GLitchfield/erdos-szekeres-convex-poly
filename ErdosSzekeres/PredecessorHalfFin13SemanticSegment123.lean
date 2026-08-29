module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk094
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk095

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 123. -/

theorem predecessorHalfFin13_rejectSemanticSegment123
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0994 chi) ∨
      ((PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0997 chi) ∨
      (PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0998 chi))) ∨
      ((PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0998 chi) ∨
      ((PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      (PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0989 chi)))) ∨
      (((PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0990 chi) ∨
      ((PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0991 chi) ∨
      (PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0993 chi))) ∨
      ((PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0994 chi) ∨
      ((PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0997 chi) ∨
      (PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0998 chi))))) ∨
      ((((PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0988 chi ∧
      PredecessorHalfFin13Atom0990 chi ∧
      PredecessorHalfFin13Atom0993 chi ∧
      PredecessorHalfFin13Atom0997 chi) ∨
      ((PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0998 chi) ∨
      (PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0988 chi ∧
      PredecessorHalfFin13Atom0990 chi ∧
      PredecessorHalfFin13Atom0993 chi ∧
      PredecessorHalfFin13Atom0997 chi))) ∨
      ((PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0998 chi) ∨
      ((PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0976 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0982 chi ∧
      PredecessorHalfFin13Atom0985 chi ∧
      PredecessorHalfFin13Atom0988 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0992 chi ∧
      PredecessorHalfFin13Atom0995 chi ∧
      PredecessorHalfFin13Atom0999 chi) ∨
      (PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0976 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0982 chi ∧
      PredecessorHalfFin13Atom0986 chi ∧
      PredecessorHalfFin13Atom0990 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0992 chi ∧
      PredecessorHalfFin13Atom0996 chi ∧
      PredecessorHalfFin13Atom1000 chi)))) ∨
      (((PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0976 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0985 chi ∧
      PredecessorHalfFin13Atom0986 chi ∧
      PredecessorHalfFin13Atom0993 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0995 chi ∧
      PredecessorHalfFin13Atom0996 chi ∧
      PredecessorHalfFin13Atom1001 chi) ∨
      ((¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi) ∨
      (¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi))) ∨
      ((¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi) ∨
      ((¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi) ∨
      (¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi) ∨
      ((¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi) ∨
      (¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi))) ∨
      ((¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi) ∨
      ((¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi) ∨
      (¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi) ∨
      ((¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi) ∨
      (¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi))) ∨
      ((¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi) ∨
      ((¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi) ∨
      (¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi) ∨
      ((¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi) ∨
      (¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi))) ∨
      ((¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi) ∨
      ((¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi) ∨
      (¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi) ∨
      ((¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi) ∨
      (¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi))) ∨
      (((¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi) ∨
      (¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi)) ∨
      ((¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi) ∨
      (¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi) ∨
      ((¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi) ∨
      (¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi))) ∨
      ((¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi) ∨
      ((¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi) ∨
      (¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi) ∨
      ((¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi) ∨
      (¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi))) ∨
      ((¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi) ∨
      ((¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi) ∨
      (¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi) ∨
      ((¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi) ∨
      (¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi))) ∨
      ((¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi) ∨
      ((¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi) ∨
      (¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi) ∨
      ((¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi) ∨
      (¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi))) ∨
      (((¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi) ∨
      (¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi)) ∨
      ((¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi) ∨
      (¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi) ∨
      ((¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi) ∨
      (¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi))) ∨
      ((¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi) ∨
      ((¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi) ∨
      (¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi) ∨
      ((¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi) ∨
      (¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi))) ∨
      ((¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi) ∨
      ((¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi) ∨
      (¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi) ∨
      ((¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi) ∨
      (¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi))) ∨
      ((¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi) ∨
      ((¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi) ∨
      (¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi) ∨
      ((¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi) ∨
      (¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi))) ∨
      (((¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi) ∨
      (¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi)) ∨
      ((¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi) ∨
      (¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi))))))))) := by
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
              exact predecessorHalfFin13_clause26557 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26560 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26561 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26566 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26571 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26573 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26574 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26575 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26577 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26578 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26581 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26582 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26586 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26587 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26592 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26593 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26594 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26595 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26596 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27061 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27062 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27063 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27064 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27066 chi hno hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27067 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27068 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27069 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27071 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27072 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27073 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27075 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27076 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27078 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27080 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27082 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27083 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27084 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27086 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27087 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27088 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27090 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27091 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27093 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27095 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27097 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27098 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27100 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27101 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27103 chi hno hbad
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
              exact predecessorHalfFin13_clause27105 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27107 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27109 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27111 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27114 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27117 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27118 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27119 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27121 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27122 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27123 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27125 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27126 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27128 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27130 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27132 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27133 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27135 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27136 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27138 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27140 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27142 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27144 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27146 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27149 chi hno hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27152 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27153 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27155 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27156 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27158 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27160 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27162 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27164 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27166 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27169 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27172 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27174 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27176 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27179 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27183 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27187 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27188 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27189 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27191 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27192 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27193 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27195 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27196 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27198 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27200 chi hno hbad

end ErdosSzekeres

end
