# Theorem Catalog (Lean Mechanization)

This appendix lists theorem declarations in `paper/lean/UadfU0` for traceability.
The file sections below are an exhaustive listing of `.lean` files under `paper/lean/UadfU0` at this snapshot.

- Total theorem declarations: `74`
- Count scope: this count includes declarations using the `theorem` keyword.
- Typecheck scope: files with only `example` declarations (for example `Examples/TwoLayer.lean`) are still fully typechecked by `lake build`; they are excluded from the theorem-keyword count by definition.

Role-group counts used in the manuscript (§4.6):
- Primary theorem interfaces (`RQ3`-`RQ5`): `15`
- Supporting lemmas: `34`
- Example-level theorem declarations: `25`

Primary-theorem set used for the `15` count:
- `U0On_monotone`
- `UAndOn_antitone`
- `UAndOn_subset_U0On`
- `UAndOn_empty_eq_univ`
- `consistent_iff_exists_UAndOn_pair`
- `U0_least_upper_bound_iff`
- `UAndOn_greatest_lower_bound_iff`
- `lifted_transfer`
- `preimage_compose`
- `preimage_subset_semanticPullback_of_sound`
- `semanticPullback_subset_preimage_of_complete`
- `preimage_eq_semanticPullback`
- `preimageMay_subset_semanticPullbackMay_of_sound`
- `semanticPullbackMay_subset_preimageMay_of_complete`
- `preimageMay_eq_semanticPullbackMay`

Example-level set used for the `25` count:
- all theorem declarations under `paper/lean/UadfU0/Examples/*.lean` (21 total)
- all theorem declarations under `paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean` (4 total)

Supporting-lemma count (`34`) is the remainder:
- `74 - 15 - 25 = 34`

Supporting-lemma examples discussed in the manuscript:
- `UAndOn_subset_UAndMayOn`
- `consistent_transport_left`
- `no_left_adjoint_of_partial`
- all six `UStar_*` theorems in `U0Spec/IdealRoot.lean`

## `paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean`

- theorem count: `4`

- `req_projection_adequacy`
- `checkConsistent_true_implies_allThree`
- `allThree_implies_checkConsistent_true`
- `checkConsistent_iff_allThree`

## `paper/lean/UadfU0/Definitions/Model.lean`

- theorem count: `3`

- `subset_refl`
- `subset_trans`
- `set_ext`

## `paper/lean/UadfU0/Examples/ArtifactBundleExample.lean`

- theorem count: `4`

- `proj_bind_decomposition`
- `Eextract_sound`
- `Eextract_complete`
- `preimage_eq_semanticPullback_Eextract`

## `paper/lean/UadfU0/Examples/AdequacyCounterexample.lean`

- theorem count: `4`

- `EPlus1_sound`
- `EPlus1_not_complete`
- `preimage_subset_semanticPullback_EPlus1`
- `semanticPullback_not_subset_preimage_EPlus1`

## `paper/lean/UadfU0/Examples/CompositionExample.lean`

- theorem count: `1`

- `proj_compose_holds`

## `paper/lean/UadfU0/Examples/ContradictoryLayers.lean`

- theorem count: `3`

- `contradictoryModel_is_contradictory`
- `contradictoryModel_uand_empty_univ`
- `contradictoryModel_empty_active_has_spurious_witness`

## `paper/lean/UadfU0/Examples/TransferChainExample.lean`

- theorem count: `2`

- `transfer_code_to_api`
- `transfer_api_to_req`

## `paper/lean/UadfU0/Examples/TransferCounterexample.lean`

- theorem count: `4`

- `hA_trivial`
- `zero_in_lifted_j`
- `zero_not_in_lifted_i`
- `transfer_fails_without_hproj`

## `paper/lean/UadfU0/Examples/HeterogeneousTransferWitness.lean`

- theorem count: `1`

- `heterogeneous_lifted_transfer`

## `paper/lean/UadfU0/Examples/TransferExample.lean`

- theorem count: `1`

- `transfer_false_to_true`

## `paper/lean/UadfU0/Examples/TwoLayer.lean`

- theorem count: `0` (`example` declarations only; no `theorem` keyword)

## `paper/lean/UadfU0/Examples/TotalizationCounterexample.lean`

- theorem count: `1`

- `naive_totalization_adds_spurious_witness`

## `paper/lean/UadfU0/InterLayer/Adequacy.lean`

- theorem count: `6`

- `preimage_subset_semanticPullback_of_sound`
- `semanticPullback_subset_preimage_of_complete`
- `preimage_eq_semanticPullback`
- `preimageMay_subset_semanticPullbackMay_of_sound`
- `semanticPullbackMay_subset_preimageMay_of_complete`
- `preimageMay_eq_semanticPullbackMay`

## `paper/lean/UadfU0/InterLayer/Composition.lean`

- theorem count: `2`

- `preimage_compose`
- `lifted_subset_of_compose`

## `paper/lean/UadfU0/InterLayer/Consistency.lean`

- theorem count: `3`

- `contradictory_iff_not_consistent`
- `consistent_implies_U0_nonempty`
- `contradictory_implies_no_shared_witness`

## `paper/lean/UadfU0/InterLayer/Transfer.lean`

- theorem count: `2`

- `lifted_transfer`
- `consistent_transport_left`

## `paper/lean/UadfU0/RelatedWork/Galois.lean`

- theorem count: `1`

- `no_left_adjoint_of_partial`

## `paper/lean/UadfU0/U0Spec/Construction.lean`

- theorem count: `19`

- `mem_preimage_iff`
- `preimage_monotone`
- `preimage_union`
- `preimage_subset_preimageMay`
- `lifted_subset_liftedMay`
- `lifted_subset_preimage_domain`
- `mem_U0_iff`
- `U0On_monotone`
- `U0_eq_U0On_all`
- `UAnd_eq_UAndOn_all`
- `UAndOn_antitone`
- `UAndOn_subset_UAndMayOn`
- `UAndMayOn_empty_implies_UAndOn_empty`
- `UAndOn_empty_eq_univ`
- `UAndOn_subset_U0On`
- `consistent_iff_exists_UAndOn_pair`
- `lifted_subset_U0`
- `U0_nonempty_of_exists_layer_nonempty`
- `U0_witness_projects_to_some_domain`

## `paper/lean/UadfU0/U0Spec/IdealRoot.lean`

- theorem count: `6`

- `UStar_subset_UAndOn`
- `UStar_inter_projDomOn_subset_UAndOn`
- `UStar_subset_U0On_of_nonempty_active`
- `UStar_inter_projDomOn_subset_U0On_of_nonempty_active`
- `UStar_subset_UAndMayOn`
- `UStar_subset_UAnd`

## `paper/lean/UadfU0/U0Spec/Minimality.lean`

- theorem count: `7`

- `U0_upper_bound`
- `U0_below_every_upper_bound`
- `U0_least_upper_bound_iff`
- `U0_is_supremum`
- `UAndOn_lower_bound`
- `below_UAndOn_of_lower_bounds`
- `UAndOn_greatest_lower_bound_iff`
