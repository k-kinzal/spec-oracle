// Lean compiler output
// Module: UadfU0
// Imports: public import Init public import UadfU0.Definitions.Model public import UadfU0.U0Spec.Construction public import UadfU0.U0Spec.Minimality public import UadfU0.InterLayer.Consistency public import UadfU0.InterLayer.Transfer public import UadfU0.InterLayer.Composition public import UadfU0.CaseStudy.PasswordPolicy public import UadfU0.Examples.TwoLayer public import UadfU0.Examples.ContradictoryLayers public import UadfU0.Examples.TransferExample public import UadfU0.Examples.CompositionExample
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_Definitions_Model(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_U0Spec_Construction(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_U0Spec_Minimality(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_InterLayer_Consistency(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_InterLayer_Transfer(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_InterLayer_Composition(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_CaseStudy_PasswordPolicy(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_Examples_TwoLayer(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_Examples_ContradictoryLayers(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_Examples_TransferExample(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_Examples_CompositionExample(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_UadfU0Paper_UadfU0(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_Definitions_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_U0Spec_Construction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_U0Spec_Minimality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_InterLayer_Consistency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_InterLayer_Transfer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_InterLayer_Composition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_CaseStudy_PasswordPolicy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_Examples_TwoLayer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_Examples_ContradictoryLayers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_Examples_TransferExample(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_Examples_CompositionExample(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
