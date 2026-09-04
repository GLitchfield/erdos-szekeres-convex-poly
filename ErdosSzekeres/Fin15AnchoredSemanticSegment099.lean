module

public import ErdosSzekeres.Fin15AnchoredClauseChunk195
public import ErdosSzekeres.Fin15AnchoredClauseChunk196
public import ErdosSzekeres.Fin15AnchoredClauseChunk197

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 099. -/

theorem fin15Anchored_rejectSemanticSegment099
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom4028 chi ∧
      ¬Fin15AnchoredAtom1320 chi) ∨
      ((Fin15AnchoredAtom4029 chi ∧
      ¬Fin15AnchoredAtom1317 chi) ∨
      (¬Fin15AnchoredAtom4029 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1318 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1324 chi ∧
      Fin15AnchoredAtom1818 chi))) ∨
      (((Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom1319 chi) ∨
      (Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom1320 chi)) ∨
      ((Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom1321 chi) ∨
      (Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom1325 chi)))) ∨
      ((((Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom1819 chi) ∨
      (¬Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1819 chi)) ∨
      ((Fin15AnchoredAtom4031 chi ∧
      ¬Fin15AnchoredAtom1323 chi) ∨
      (Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom1326 chi))) ∨
      (((Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom1327 chi) ∨
      (Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom1335 chi)) ∨
      ((Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom1371 chi) ∨
      (Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom1491 chi))))) ∨
      (((((¬Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1491 chi) ∨
      (Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom1326 chi)) ∨
      ((Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom1328 chi) ∨
      (Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom1336 chi))) ∨
      (((Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom1372 chi) ∨
      (Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom1492 chi)) ∨
      ((¬Fin15AnchoredAtom4033 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1492 chi) ∨
      (Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom1326 chi)))) ∨
      ((((Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom1329 chi) ∨
      (Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom1337 chi)) ∨
      ((Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom1373 chi) ∨
      (Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom1493 chi))) ∨
      (((¬Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1493 chi) ∨
      (Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom1326 chi)) ∨
      ((Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom1338 chi)))))) ∨
      ((((((Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom1494 chi)) ∨
      ((¬Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1494 chi) ∨
      (Fin15AnchoredAtom4036 chi ∧
      ¬Fin15AnchoredAtom1495 chi))) ∨
      (((¬Fin15AnchoredAtom4036 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1331 chi ∧
      Fin15AnchoredAtom1339 chi ∧
      Fin15AnchoredAtom1375 chi ∧
      Fin15AnchoredAtom1495 chi) ∨
      (Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom1326 chi)) ∨
      ((Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom1332 chi) ∨
      (Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom1340 chi)))) ∨
      ((((Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom1376 chi) ∨
      (Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom1496 chi)) ∨
      ((¬Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1496 chi) ∨
      (Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom1326 chi))) ∨
      (((Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom1333 chi) ∨
      (Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom1341 chi)) ∨
      ((Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom1377 chi) ∨
      (Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom1497 chi))))) ∨
      (((((¬Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1497 chi) ∨
      (Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom1326 chi)) ∨
      ((Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom1334 chi) ∨
      (Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom1342 chi))) ∨
      (((Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom1378 chi) ∨
      (Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom1498 chi)) ∨
      ((¬Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1498 chi) ∨
      (Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom1327 chi)))) ∨
      ((((Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom1328 chi) ∨
      (Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom1343 chi)) ∨
      ((Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom1499 chi) ∨
      (¬Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1499 chi))) ∨
      (((Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom1327 chi) ∨
      (Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom1329 chi)) ∨
      ((Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom1344 chi) ∨
      (Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom1380 chi))))))) ∨
      ((((((Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom1500 chi) ∨
      ((¬Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1500 chi) ∨
      (Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom1327 chi))) ∨
      (((Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom1345 chi)) ∨
      ((Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom1381 chi) ∨
      (Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom1501 chi)))) ∨
      ((((¬Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1501 chi) ∨
      (Fin15AnchoredAtom4043 chi ∧
      ¬Fin15AnchoredAtom1502 chi)) ∨
      ((Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom1327 chi) ∨
      (Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom1332 chi))) ∨
      (((Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom1347 chi) ∨
      (Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom1383 chi)) ∨
      ((Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom1503 chi) ∨
      (¬Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1503 chi))))) ∨
      (((((Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom1327 chi) ∨
      (Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom1333 chi)) ∨
      ((Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom1348 chi) ∨
      (Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom1384 chi))) ∨
      (((Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom1504 chi) ∨
      (¬Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1504 chi)) ∨
      ((Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom1327 chi) ∨
      (Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom1334 chi)))) ∨
      ((((Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom1349 chi) ∨
      (Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom1385 chi)) ∨
      ((Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (¬Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1505 chi))) ∨
      (((Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom1328 chi) ∨
      (Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom1329 chi)) ∨
      ((Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom1350 chi) ∨
      (Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom1506 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom4047 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1506 chi) ∨
      (Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom1328 chi)) ∨
      ((Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom1351 chi))) ∨
      (((Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom1387 chi) ∨
      (Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom1507 chi)) ∨
      ((¬Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1507 chi) ∨
      (Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom1328 chi)))) ∨
      ((((Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom1332 chi) ∨
      (Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom1353 chi)) ∨
      ((Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom1389 chi) ∨
      (Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom1509 chi))) ∨
      (((¬Fin15AnchoredAtom4050 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1509 chi) ∨
      (Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom1328 chi)) ∨
      ((Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom1333 chi) ∨
      (Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom1354 chi))))) ∨
      (((((Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom1390 chi) ∨
      (Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom1510 chi)) ∨
      ((¬Fin15AnchoredAtom4051 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1510 chi) ∨
      (Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom1328 chi))) ∨
      (((Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom1334 chi) ∨
      (Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom1355 chi)) ∨
      ((Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom1391 chi) ∨
      (Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom1511 chi)))) ∨
      ((((¬Fin15AnchoredAtom4052 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1511 chi) ∨
      (Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom1329 chi)) ∨
      ((Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom1356 chi))) ∨
      (((Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom1512 chi)) ∨
      ((¬Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1512 chi) ∨
      (Fin15AnchoredAtom4054 chi ∧
      ¬Fin15AnchoredAtom1329 chi)))))))) ∨
      (((((((Fin15AnchoredAtom4054 chi ∧
      ¬Fin15AnchoredAtom1357 chi) ∨
      ((Fin15AnchoredAtom4054 chi ∧
      ¬Fin15AnchoredAtom1513 chi) ∨
      (¬Fin15AnchoredAtom4054 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1331 chi ∧
      Fin15AnchoredAtom1357 chi ∧
      Fin15AnchoredAtom1393 chi ∧
      Fin15AnchoredAtom1513 chi))) ∨
      (((Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom1329 chi) ∨
      (Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom1332 chi)) ∨
      ((Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom1358 chi) ∨
      (Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom1394 chi)))) ∨
      ((((Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom1514 chi) ∨
      (¬Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1514 chi)) ∨
      ((Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom1329 chi) ∨
      (Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom1333 chi))) ∨
      (((Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom1359 chi) ∨
      (Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom1395 chi)) ∨
      ((Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom1515 chi) ∨
      (¬Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1515 chi))))) ∨
      (((((Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom1329 chi) ∨
      (Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom1334 chi)) ∨
      ((Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom1360 chi) ∨
      (Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom1396 chi))) ∨
      (((Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom1516 chi) ∨
      (¬Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1516 chi)) ∨
      ((Fin15AnchoredAtom4058 chi ∧
      ¬Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom4058 chi ∧
      ¬Fin15AnchoredAtom1397 chi)))) ∨
      ((((Fin15AnchoredAtom4058 chi ∧
      ¬Fin15AnchoredAtom1517 chi) ∨
      (¬Fin15AnchoredAtom4058 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1331 chi ∧
      Fin15AnchoredAtom1361 chi ∧
      Fin15AnchoredAtom1397 chi ∧
      Fin15AnchoredAtom1517 chi)) ∨
      ((Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom1332 chi))) ∨
      (((Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom1398 chi)) ∨
      ((Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom1518 chi) ∨
      (¬Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1518 chi)))))) ∨
      ((((((Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom1333 chi)) ∨
      ((Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom1363 chi) ∨
      (Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom1399 chi))) ∨
      (((Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom1519 chi) ∨
      (¬Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1519 chi)) ∨
      ((Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom1334 chi)))) ∨
      ((((Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom1364 chi) ∨
      (Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom1400 chi)) ∨
      ((Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom1520 chi) ∨
      (¬Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1520 chi))) ∨
      (((Fin15AnchoredAtom4062 chi ∧
      ¬Fin15AnchoredAtom1332 chi) ∨
      (Fin15AnchoredAtom4063 chi ∧
      ¬Fin15AnchoredAtom1333 chi)) ∨
      ((Fin15AnchoredAtom4064 chi ∧
      ¬Fin15AnchoredAtom1334 chi) ∨
      (Fin15AnchoredAtom4064 chi ∧
      ¬Fin15AnchoredAtom1367 chi))))) ∨
      (((((Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom1332 chi) ∨
      (Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom1333 chi)) ∨
      ((Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom1368 chi) ∨
      (Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom1404 chi))) ∨
      (((Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom1524 chi) ∨
      (¬Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1524 chi)) ∨
      ((Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom1332 chi) ∨
      (Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom1334 chi)))) ∨
      ((((Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom1369 chi) ∨
      (Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom1405 chi)) ∨
      ((Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom1525 chi) ∨
      (¬Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1525 chi))) ∨
      (((Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom1333 chi) ∨
      (Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom1334 chi)) ∨
      ((Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom1370 chi) ∨
      (Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom1406 chi))))))) ∨
      (((((((Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom1526 chi) ∨
      (¬Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1526 chi)) ∨
      ((Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom1335 chi) ∨
      (Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom1336 chi))) ∨
      (((Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom1343 chi) ∨
      (Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom1407 chi)) ∨
      ((Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom1527 chi) ∨
      (¬Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1527 chi)))) ∨
      ((((Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom1335 chi) ∨
      (Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom1337 chi)) ∨
      ((Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom1344 chi) ∨
      (Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom1408 chi))) ∨
      (((Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom1528 chi) ∨
      (¬Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1528 chi)) ∨
      ((Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom1335 chi) ∨
      (Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom1338 chi))))) ∨
      (((((Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom1345 chi) ∨
      (Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom1409 chi)) ∨
      ((Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom1529 chi) ∨
      (¬Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1529 chi))) ∨
      (((Fin15AnchoredAtom4071 chi ∧
      ¬Fin15AnchoredAtom1530 chi) ∨
      (Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom1335 chi)) ∨
      ((Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom1340 chi) ∨
      (Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom1347 chi)))) ∨
      ((((Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom1411 chi) ∨
      (Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom1531 chi)) ∨
      ((¬Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1531 chi) ∨
      (Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom1335 chi))) ∨
      (((Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom1341 chi) ∨
      (Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom1348 chi)) ∨
      ((Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom1412 chi) ∨
      (Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom1532 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1532 chi) ∨
      (Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom1335 chi)) ∨
      ((Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom1342 chi) ∨
      (Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom1349 chi))) ∨
      (((Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom1413 chi) ∨
      (Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom1533 chi)) ∨
      ((¬Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1533 chi) ∨
      (Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom1336 chi)))) ∨
      ((((Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom1337 chi) ∨
      (Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom1350 chi)) ∨
      ((Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom1414 chi) ∨
      (Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom1534 chi))) ∨
      (((¬Fin15AnchoredAtom4075 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1534 chi) ∨
      (Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom1336 chi)) ∨
      ((Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom1338 chi) ∨
      (Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom1351 chi))))) ∨
      (((((Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom1415 chi) ∨
      (Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom1535 chi)) ∨
      ((¬Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1535 chi) ∨
      (Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom1336 chi))) ∨
      (((Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom1340 chi) ∨
      (Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom1353 chi)) ∨
      ((Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom1417 chi) ∨
      (Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom1537 chi)))) ∨
      ((((¬Fin15AnchoredAtom4078 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1537 chi) ∨
      (Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom1336 chi)) ∨
      ((Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom1341 chi) ∨
      (Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom1354 chi))) ∨
      (((Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom1418 chi) ∨
      (Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom1538 chi)) ∨
      ((¬Fin15AnchoredAtom4079 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1538 chi) ∨
      (Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom1336 chi)))))))))) := by
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
                exact fin15Anchored_clause24987 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24988 chi hbad
                ·
                  exact fin15Anchored_clause24989 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24990 chi hbad
                ·
                  exact fin15Anchored_clause24991 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24992 chi hbad
                ·
                  exact fin15Anchored_clause24993 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24994 chi hbad
                ·
                  exact fin15Anchored_clause24995 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24996 chi hbad
                ·
                  exact fin15Anchored_clause24997 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24998 chi hbad
                ·
                  exact fin15Anchored_clause24999 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25000 chi hbad
                ·
                  exact fin15Anchored_clause25001 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25002 chi hbad
                ·
                  exact fin15Anchored_clause25003 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25004 chi hbad
                ·
                  exact fin15Anchored_clause25005 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25006 chi hbad
                ·
                  exact fin15Anchored_clause25007 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25008 chi hbad
                ·
                  exact fin15Anchored_clause25009 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25010 chi hbad
                ·
                  exact fin15Anchored_clause25011 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25012 chi hbad
                ·
                  exact fin15Anchored_clause25013 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25014 chi hbad
                ·
                  exact fin15Anchored_clause25015 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25016 chi hbad
                ·
                  exact fin15Anchored_clause25017 chi hbad
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
                  exact fin15Anchored_clause25018 chi hbad
                ·
                  exact fin15Anchored_clause25019 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25020 chi hbad
                ·
                  exact fin15Anchored_clause25021 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25022 chi hbad
                ·
                  exact fin15Anchored_clause25023 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25024 chi hbad
                ·
                  exact fin15Anchored_clause25025 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25026 chi hbad
                ·
                  exact fin15Anchored_clause25027 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25028 chi hbad
                ·
                  exact fin15Anchored_clause25029 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25030 chi hbad
                ·
                  exact fin15Anchored_clause25031 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25032 chi hbad
                ·
                  exact fin15Anchored_clause25033 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25034 chi hbad
                ·
                  exact fin15Anchored_clause25035 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25036 chi hbad
                ·
                  exact fin15Anchored_clause25037 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25038 chi hbad
                ·
                  exact fin15Anchored_clause25039 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25040 chi hbad
                ·
                  exact fin15Anchored_clause25041 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25042 chi hbad
                ·
                  exact fin15Anchored_clause25043 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25044 chi hbad
                ·
                  exact fin15Anchored_clause25045 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25046 chi hbad
                ·
                  exact fin15Anchored_clause25047 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25048 chi hbad
                ·
                  exact fin15Anchored_clause25049 chi hbad
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
                exact fin15Anchored_clause25050 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25051 chi hbad
                ·
                  exact fin15Anchored_clause25052 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25053 chi hbad
                ·
                  exact fin15Anchored_clause25054 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25055 chi hbad
                ·
                  exact fin15Anchored_clause25056 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25057 chi hbad
                ·
                  exact fin15Anchored_clause25058 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25059 chi hbad
                ·
                  exact fin15Anchored_clause25060 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25061 chi hbad
                ·
                  exact fin15Anchored_clause25062 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25063 chi hbad
                ·
                  exact fin15Anchored_clause25064 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25065 chi hbad
                ·
                  exact fin15Anchored_clause25066 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25067 chi hbad
                ·
                  exact fin15Anchored_clause25068 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25069 chi hbad
                ·
                  exact fin15Anchored_clause25070 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25071 chi hbad
                ·
                  exact fin15Anchored_clause25072 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25073 chi hbad
                ·
                  exact fin15Anchored_clause25074 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25075 chi hbad
                ·
                  exact fin15Anchored_clause25076 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25077 chi hbad
                ·
                  exact fin15Anchored_clause25078 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25079 chi hbad
                ·
                  exact fin15Anchored_clause25080 chi hbad
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
                  exact fin15Anchored_clause25081 chi hbad
                ·
                  exact fin15Anchored_clause25082 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25083 chi hbad
                ·
                  exact fin15Anchored_clause25084 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25085 chi hbad
                ·
                  exact fin15Anchored_clause25086 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25087 chi hbad
                ·
                  exact fin15Anchored_clause25088 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25089 chi hbad
                ·
                  exact fin15Anchored_clause25090 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25091 chi hbad
                ·
                  exact fin15Anchored_clause25092 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25093 chi hbad
                ·
                  exact fin15Anchored_clause25094 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25095 chi hbad
                ·
                  exact fin15Anchored_clause25096 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25097 chi hbad
                ·
                  exact fin15Anchored_clause25098 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25099 chi hbad
                ·
                  exact fin15Anchored_clause25100 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25101 chi hbad
                ·
                  exact fin15Anchored_clause25102 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25103 chi hbad
                ·
                  exact fin15Anchored_clause25104 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25105 chi hbad
                ·
                  exact fin15Anchored_clause25106 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25107 chi hbad
                ·
                  exact fin15Anchored_clause25108 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25109 chi hbad
                ·
                  exact fin15Anchored_clause25110 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25111 chi hbad
                ·
                  exact fin15Anchored_clause25112 chi hbad
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
                exact fin15Anchored_clause25113 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25114 chi hbad
                ·
                  exact fin15Anchored_clause25115 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25116 chi hbad
                ·
                  exact fin15Anchored_clause25117 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25118 chi hbad
                ·
                  exact fin15Anchored_clause25119 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25120 chi hbad
                ·
                  exact fin15Anchored_clause25121 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25122 chi hbad
                ·
                  exact fin15Anchored_clause25123 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25124 chi hbad
                ·
                  exact fin15Anchored_clause25125 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25126 chi hbad
                ·
                  exact fin15Anchored_clause25127 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25128 chi hbad
                ·
                  exact fin15Anchored_clause25129 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25130 chi hbad
                ·
                  exact fin15Anchored_clause25131 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25132 chi hbad
                ·
                  exact fin15Anchored_clause25133 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25134 chi hbad
                ·
                  exact fin15Anchored_clause25135 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25136 chi hbad
                ·
                  exact fin15Anchored_clause25137 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25138 chi hbad
                ·
                  exact fin15Anchored_clause25139 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25140 chi hbad
                ·
                  exact fin15Anchored_clause25141 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25142 chi hbad
                ·
                  exact fin15Anchored_clause25143 chi hbad
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
                  exact fin15Anchored_clause25144 chi hbad
                ·
                  exact fin15Anchored_clause25145 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25146 chi hbad
                ·
                  exact fin15Anchored_clause25147 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25148 chi hbad
                ·
                  exact fin15Anchored_clause25149 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25150 chi hbad
                ·
                  exact fin15Anchored_clause25151 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25152 chi hbad
                ·
                  exact fin15Anchored_clause25153 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25154 chi hbad
                ·
                  exact fin15Anchored_clause25155 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25156 chi hbad
                ·
                  exact fin15Anchored_clause25157 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25158 chi hbad
                ·
                  exact fin15Anchored_clause25159 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25160 chi hbad
                ·
                  exact fin15Anchored_clause25161 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25162 chi hbad
                ·
                  exact fin15Anchored_clause25163 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25164 chi hbad
                ·
                  exact fin15Anchored_clause25165 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25166 chi hbad
                ·
                  exact fin15Anchored_clause25167 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25168 chi hbad
                ·
                  exact fin15Anchored_clause25169 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25170 chi hbad
                ·
                  exact fin15Anchored_clause25171 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25172 chi hbad
                ·
                  exact fin15Anchored_clause25173 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25174 chi hbad
                ·
                  exact fin15Anchored_clause25175 chi hbad
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
                  exact fin15Anchored_clause25176 chi hbad
                ·
                  exact fin15Anchored_clause25177 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25178 chi hbad
                ·
                  exact fin15Anchored_clause25179 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25180 chi hbad
                ·
                  exact fin15Anchored_clause25181 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25182 chi hbad
                ·
                  exact fin15Anchored_clause25183 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25184 chi hbad
                ·
                  exact fin15Anchored_clause25185 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25186 chi hbad
                ·
                  exact fin15Anchored_clause25187 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25188 chi hbad
                ·
                  exact fin15Anchored_clause25189 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25190 chi hbad
                ·
                  exact fin15Anchored_clause25191 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25192 chi hbad
                ·
                  exact fin15Anchored_clause25193 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25194 chi hbad
                ·
                  exact fin15Anchored_clause25195 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25196 chi hbad
                ·
                  exact fin15Anchored_clause25197 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25198 chi hbad
                ·
                  exact fin15Anchored_clause25199 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25200 chi hbad
                ·
                  exact fin15Anchored_clause25201 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25202 chi hbad
                ·
                  exact fin15Anchored_clause25203 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25204 chi hbad
                ·
                  exact fin15Anchored_clause25205 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25206 chi hbad
                ·
                  exact fin15Anchored_clause25207 chi hbad
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
                  exact fin15Anchored_clause25208 chi hbad
                ·
                  exact fin15Anchored_clause25209 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25210 chi hbad
                ·
                  exact fin15Anchored_clause25211 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25212 chi hbad
                ·
                  exact fin15Anchored_clause25213 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25214 chi hbad
                ·
                  exact fin15Anchored_clause25215 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25216 chi hbad
                ·
                  exact fin15Anchored_clause25217 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25218 chi hbad
                ·
                  exact fin15Anchored_clause25219 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25220 chi hbad
                ·
                  exact fin15Anchored_clause25221 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25222 chi hbad
                ·
                  exact fin15Anchored_clause25223 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25224 chi hbad
                ·
                  exact fin15Anchored_clause25225 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25226 chi hbad
                ·
                  exact fin15Anchored_clause25227 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25228 chi hbad
                ·
                  exact fin15Anchored_clause25229 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25230 chi hbad
                ·
                  exact fin15Anchored_clause25231 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25232 chi hbad
                ·
                  exact fin15Anchored_clause25233 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25234 chi hbad
                ·
                  exact fin15Anchored_clause25235 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25236 chi hbad
                ·
                  exact fin15Anchored_clause25237 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25238 chi hbad
                ·
                  exact fin15Anchored_clause25239 chi hbad

end ErdosSzekeres

end
