The 24-hour proof pilot is complete.

Scheduled deadline: 2026-09-09T18:23:10.000Z. Final handoff: 2026-09-09T18:23:59.251897+00:00.

70 additional Lean theorem commits and their complete harness index refreshes were checked and pushed to their node branches. The deadline checkpoint verified each proof commit against the remote branch and checked its saved axiom and statement-lock audit.

The strongest completed capacity result is full interval/complement additivity inside one ancestor child run when the selected outer-side capacity is at most three. It allows arbitrary nonempty block lengths, both sides, positive old histories, and coupled maxima. The unrestricted singleton-end sandwich and the full Erdos-Szekeres conjecture remain open.

Final compiled harness counts after releasing the parent claim: {'closed': 114, 'open': 12, 'refuted': 1}. Index stale reasons: [].

Resource policy: shared 30 GiB job budget; full refreshes capped at 28 GiB and serialized with Lean work; proof jobs capped at 3 GiB; finite diagnostics sharded where applicable. Maximum recorded proof-build peak in the result manifest: 899 MiB. Full-refresh wrapper peaks are not extractor memory measurements. Finite probes are diagnostic evidence, not Lean theorems.

The actual-marker rank-pair potential theorem is compiled and pushed. It bounds every fuel and the full context by the union of ordered opposite-rank pairs at active children, for positive histories with an actual chosen marker and chosen global at most four. Its proof groups ranks using prefix counts of missing adjacent pairs. The final recursive-part theorem applies this bound after a cut: removed active children at the two ends reserve rows and columns of the source rank-pair set, leaving a smaller budget for the retained part. It requires a preserved actual marker on the opposite side with chosen global at most four. Next work: extend the support-sensitive pair bound beyond the actual-marker case, and use the resulting reservation drops in coupled recursive-cut comparisons. Larger selected capacities and the unrestricted sandwich theorem remain open. Conditional rank-band drafts are retained as fallback, not counted as proof progress.

Prepared but unregistered or unfinished sequence entries: []. Next-round prepared proof drafts: [{'suggested_number': 71, 'node': 'ctx_one_level_arbitrary_cut_rank_bound', 'stem': 'general-cut-rank-budget', 'registration_guard': 'after actual70 index publication; do not run after pilot deadline'}].

Checked theorem additions:

| Number | Theorem | Proof commit | Full-index commit |
| --- | --- | --- | --- |
| 1 | ctx_reverse_extension_transport | a91a23691b9f15bcf831e472a02ae678e88c2c69 | 291eab3bac8f9bbb04eca8043a7f9ff6b171efc5 |
| 2 | ctx_single_run_part_limits_exact | 601f5c1f2400065f73786843ad9f411a8b3d3e9f | ca3e564f1dfc159e20fd48a8fe385e19b4b45f85 |
| 3 | ctx_single_run_descendant_limits_normalize | 9523c014bb3617d747e8a5e7292387b655cf7773 | 9f934f26c348f5d5e2edebf316ac8755bf128ab8 |
| 4 | ctx_single_run_descendant_bound_normalize | 748ad6e4f02c52227f0af3e527b7ba91b546b7e1 | 15bad2ef9a6a875909759a909c7b1572a76e0aa8 |
| 5 | ctx_part_capacity_drop_in_clear_interval | 1e9321d8de83d3208b12677c1db3ac22025e48d2 | b0566b9e7fc9b054f61f8aa1a2e6d6c171ca6a76 |
| 6 | ctx_bound_le_numRuns_of_unit_axis_limit | ba0b6b82a2da47943f6122d4d62d866738decda6 | 8d90e95fdc1fe990d5e97a9fb38dda4aea675c42 |
| 7 | ctx_unit_axis_active_region_potential | abf32d88edcc026b0dcca117fd3d39edfc4e67b4 | 44f80467efa03c73e2a8651802e8ec38f7574df3 |
| 8 | ctx_bound_le_one_of_large_sibling_maximum | 7a84da04da07113fc0a52b4d40ab578470f93cf9 | 70ddb136dfc4b260578190b1ed47e2891b38ffe1 |
| 9 | ctx_bound_additive_saturated_interval_complement | ca0ba576fe1001cc73fe02ad77d4d7ab568704bb | 33d11a5e3e390452d7b262365bf2ed1e9fda0360 |
| 10 | ctx_bound_le_one_of_clear_unit_axis | fd297977d57572e15358b73ecc57c27f905c02a2 | 23bd7b6dd8b51d6d08e6316211bbf7edb20789be |
| 11 | ctx_bound_additive_interval_complement_small_outer_axis | 7f360a55fe9ea497bffafaacc52a1ea063d9cee4 | 222b3b8518ed088b4a4dab9f7e84a8679e46822f |
| 12 | ctx_unit_axis_region_potential_additive | 8ff0c30841724b413ca0d5a1725c24106f5a8266 | 04e481625b8bfbf779483277b3c264f305e17410 |
| 13 | ctx_small_global_axis_rank_region_potential | 072151cf6ce3f0254aceed3bc35634709ce4a4a3 | 13ef0f53ddb2dfad36cc83129db68ac5e039606b |
| 14 | ctx_bound_additive_disjoint_single_run_small_axis | c8d3344942f8994526b1f2612ad2714bce76f48f | 9f49a59bccceb241c2b47c73115e18a3df2229a5 |
| 15 | ctx_sibling_maximum_upper_normalize | ce19bac7267a6ae56b2f7d0adc6e67942b674769 | 33751f43a0cdd885f0e3eb04278006224c64a286 |
| 16 | ctx_bound_additive_near_saturated_interval_complement | 8a19b1447e89352a3c0545412c4cf124a6bee5b1 | 12f2f05fbd759785fea58a89291cbb27b7def0b2 |
| 17 | ctx_erase_level_bound_mono | 8736821ca1879e97382c769ae22b56166d0d3e37 | 211e7de101646b5efc8a3ee855883d5e050c2da2 |
| 18 | ctx_boundary_marker_upper_normalize | 14f27a01d63ade8ec4f6714dc3e5634d1d50c415 | 84d73e697a69d9920eaf52979dcc8642b066d4dd |
| 19 | ctx_boundary_marker_rank_budget | d00f37d020932ecb816bf80ad3b6f6feb8bc5394 | d2ca14b7585304734d6fa88ea85ee4071ea85669 |
| 20 | ctx_one_sided_part_boundary_budget | d6ef86afdb569a2fadc37890a0d62bb0544c2efe | b1732e35bdfab520bad83d05c2d6f5c90315f92a |
| 21 | ctx_bound_mono_of_marker_inclusion | d21ef6f6c6ddfd8754fb21874c1119c3abe9a34a | 450686e2af907f7e675dbad3c9c3efe379d88865 |
| 22 | ctx_straddling_removed_marker_unit | a92b960dae4a7c0955ea85e22db2b7eea1956c2b | 401315fe3e03c97398a9d2e111d4a9a06c62f72e |
| 23 | ctx_boundary_marker_erase_normalize | 95cf5c3a7923c6d0e4532ab2a82a111327264613 | 674f82d41204f9577117e05cd90f53d7d37ca54b |
| 24 | ctx_boundary_marker_full_rank_budget | 89ab270642323c32d57ebc22c573a39d3bf4ebdc | 3ce6a589bdb9d354a99b0fb075e550d44438fc66 |
| 25 | ctx_boundary_marker_rank_budget_all_history | 4a87f606ec458433ddc8beb0a31d935552a450f9 | ab8c4c9252bb0acbd0a08f8bc93b5c7e5adf7d4b |
| 26 | ctx_bound_mono_of_zero_capacity_marker_inclusion | f738a1e445f5f4103e015410cbc4f3676fe52c08 | c37f25170fd90e41c53d768507d94b0931ac8304 |
| 27 | ctx_active_boundary_marker_rank_budget | 3abc446b957ce476f57463354f067b8f7fc6b72a | 01129c61daf21e4eb4034e1a463c7a21a9ab581a |
| 28 | ctx_bracketed_children_unit_bound | bbb79ecdd037f89dbd1337d5eed876b62dd51ef6 | 289da1a3f17dd7c456c79f1e01c89edd3dd44346 |
| 29 | ctx_active_unit_axis_three_zone_potential | e598ec44622b20b0f39e520c559e2c1ad1cd8568 | ccff833494aaa85bfb761e6f2115095d49bc558d |
| 30 | ctx_nonunit_children_exterior_of_two_levels | 3d2ec33de754ed4371129dd6588e2baf36df07ea | e4b07ea1a721afe2d7a735dcc79ccca055b0bc4d |
| 31 | ctx_bound_le_one_of_common_singleton_rank | 8a262caf46dea1106389db18789e13452ac21117 | 6c6d6a7d9cef30fa5f0dd27caf03fd092d046bab |
| 32 | ctx_active_boundary_marker_rank_union_bound | a940d34738eb5cec7ae18a79a9ace054457dff95 | c500e54c8b5b598a84e78ed060e3a72388959834 |
| 33 | ctx_cut_rank_budget_of_nonunit_part | 35a152e7134f4d71a81cbbc05f953a78890141e9 | 743521a7afb63fe73fff803b28f57e93c3e79b7f |
| 34 | ctx_mixed_axis_clear_unit_cover_potential | d3b73cf437e260a2c8d91c59ae460bf470532efa | 5bd25bc173f76188ce38a17ae1dcc6c53be21d12 |
| 35 | ctx_nonunit_part_unit_rank_potential_drop | 6583b38e4d564091766484cebe4cc2dda140e1f6 | 9ffbd8612d0cf432814ede042eb3c023db85d243 |
| 36 | ctx_part_tracked_rank_reservation | 9142292b6f333580d9dd1acc217fe262fef2e310 | c5e7b48ba22c6ee84373becf0182a9c59200d225 |
| 37 | ctx_mixed_clear_or_singleton_rank_cover_potential | 425159d8410341d86c25ea1e62a5fc2f321b8caa | 563976b60030b0bf1eb1a3650d67bd6dda0275df |
| 38 | ctx_cut_potential_drop_of_nonunit_companion | a4fe4a82d9c6b55adaa14324a5f804735d40692b | ae3bb340833a5c3bf3b4851279e7708d1c7a01f3 |
| 39 | ctx_both_unit_parts_zone_budget | a6f58f11c85d8b2ec348c0977b383fdc23eb7998 | c359dab25484cfac616dc0222392af4e565f0703 |
| 40 | ctx_two_level_unit_rank_potential_bound | 01bf4eefa2f1f1e36866f49008fe33a8929980d6 | b9b4df25fbb91fd060bdd3c22fb9d362e700fcb9 |
| 41 | ctx_nonunit_part_companion_exterior_rank_bound | d822b0402aea21592effe3264a0ca07d26fba642 | 84c53a5dbc5838439de2e6020ee443bf4a5153f5 |
| 42 | ctx_nonunit_part_active_companion_exterior_potential_drop | a2d332ffce600cf098ca87731f4486694596fce4 | 56f9ee9a14e3bcfd32dd7eb37b871a6351f6ae6a |
| 43 | ctx_nonunit_part_active_companion_cut_potential_bound | d66db90c940b95d740a0c462d4e3c4a37ecb866b | 0003190e53beccc21911d97343e4f349d355b064 |
| 44 | ctx_unit_part_exterior_potential_charge | 252760b2242c6a78b8682b7392b394abd4d343d1 | aca98d0608c332ae455c5f21a768a0250832626a |
| 45 | ctx_part_pruning_history_transport | 697b4a86474f79012fbf5248a4a022d8b75136ec | 43563b5d0c995bcf6b9f866716a54919ff7805da |
| 46 | ctx_one_level_exterior_potential_bound | 4493257907b4dab598492382eaedf2b9269ddea4 | 4c2a16e60ce4ff56127b98139e80664d1ea62cee |
| 47 | ctx_uniform_rank_unit_part_exterior_charge | 4a396de47b58cae2b4cb41cb75d5adb7a0167ccd | 79b5e86ce8aa4727c1238d38455dcff3bace973c |
| 48 | ctx_uniform_rank_exterior_bound | e71d990fea6aa83d11599ed6c3d69abdd3a6d995 | 04ba2b43a261de14aeb173235bbda8a6e9300605 |
| 49 | ctx_active_uniform_rank_exterior_bound | ccb5eb632e03c96d43953ebf94550e567f0c0aa2 | 01d7b9a9682a340d3f21e4f5052919a4c60fa02b |
| 50 | ctx_unit_part_refined_exterior_charge | ad23003c514a816457963e8dd57f03e683d746f8 | 1018c0862f1cac70ac5c17f91b79e57f6350839f |
| 51 | ctx_one_level_refined_potential_bound | d9bd8a1172bfac304f686557225a0b30bccf9e87 | 4a185d1181ac2601fc5d0ba53ca45c265be798f1 |
| 52 | ctx_bound_additive_interval_complement_capacity_three | 8384d3f5fe4b8cfb2b0e035f8d48b2db8d35a838 | 1654af80e62cb5b44df5504a6057859879d0df94 |
| 53 | ctx_bound_additive_capacity_three_low_outer_maximum | e08dc35a529eb81b8f71495866497bbfcda48ba9 | 87dd5c4bccb53548c84a0ab9399f2bb2bf79d64f |
| 54 | ctx_oldest_axis_maximum_erase_normalize | e388ed789c593a6adb95de44d513e79e79f2a43f | 22ec662be70e943bb8ecf744049537ce7ba1be97 |
| 55 | ctx_single_level_companion_maximum_bound | b995e16d77b891e2748273cee7cc401ef3e10cba | f6bf70872b88cb24de80b461d562b1a872c5ab7c |
| 56 | ctx_single_level_saturated_linear_bound | 6d01362dfb34549b901c2d69d9cc0534e0ace8c2 | 71c931a88adb03a0322773a0f843474f4375c7c5 |
| 57 | ctx_bound_additive_interval_complement_capacity_three_full | 90c9e7b210b7cf9cea4ee21352210a5c2dd64363 | 2ca0b5f758b717d3adeb41d9fcc43599f9d1566d |
| 58 | ctx_part_tracked_rank_pair_reservation | 0ce55ee4f2f3c5a092c320387a2703f6fba756ac | bfcc4c43b3fe097133e62f200a6c522448176561 |
| 59 | ctx_part_tracked_rank_pair_end_reservations | ddf204c37950dd9e3bd6a7cb00d0b6c357d0f5bf | 94a4a8be23452ccdce1b7f636bc71755b8d33208 |
| 60 | ctx_part_equal_endpoint_interior_ranks | 015e83a8f46facc07961fcf42af86141e7a7cdee | b7a56b68cf30e3d5ae6502d1ad420b824b71b04f |
| 61 | ctx_nonunit_straddling_unique_axis_level | f9985129b0f50c659b6abdb233d99b64a3bd72bd | eb3432e6d06e7e8a4d7dbcf10cb94e92fd0cc05b |
| 62 | ctx_axis_region_limits_exact | d319c6204b867eee13adc9bad0d21b3b6b8da8c8 | f0c8b2787ca46fc1e35f8b3fa9ef1e3418156cad |
| 63 | ctx_nonunit_straddling_capacity_profile | dd6777f7843647346df9dc51215515d26b054f34 | d2fac2027e37b858b03a26b1603be6e13ba2b1ac |
| 64 | ctx_axis_capacity_interval_lower_bound | 071267d915e7a5fa1203627b096412db81b2dc26 | 23d37dcaeb73f560961c4e5b803acc89d8ad9768 |
| 65 | ctx_prune_part_projection_of_removed_witness | 832d4863c9c6f4434e5c1714cfd111a76401f392 | 057024dbf6f2693923ce0b45c640b56c15816e0f |
| 66 | ctx_prune_part_bound_of_all_tracked_retained | a5efa166903f1c0b62d91cb381c6a045f9636fe0 | d5b20a44bbc44f5d8afb5c14131d41e03d427017 |
| 67 | ctx_bound_le_sum_run_group_prunings | 57e63c7f89a0a535c30e4e8b0200632019005cc4 | 48a6ba447719f95de88317c0da4c7f645088a380 |
| 68 | rank_pair_card_ge_sum_disjoint_group_charges | 0d488b07ecb253026016c5f798424010f5b2f2ad | 3e5adeb96dc745446a9badf793b79bce36902e1e |
| 69 | ctx_one_level_rank_pair_potential_bound | b152b8755537c0ddaff45712f650fcebf3f6a45f | 25b906a63b311687ec40284aed258e2a25219995 |
| 70 | ctx_part_bound_rank_pair_end_reservations | 22b42088a3f607a77bc99f40d3e850c969aec8c0 | 6a7d0eefd92c90378c11d98d31e0f51c000d901c |

Detailed statements, build jobs, audit artifacts and scope notes are recorded in run.json. The final remote verification is in checkpoint-12.json. No new research was started after the deadline; final verification and handoff were completed afterward as needed.
