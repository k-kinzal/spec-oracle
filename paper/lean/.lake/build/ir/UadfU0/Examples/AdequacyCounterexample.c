// Lean compiler output
// Module: UadfU0.Examples.AdequacyCounterexample
// Imports: public import Init public import UadfU0.InterLayer.Adequacy
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
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_onlyOne;
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_oneLayerNatModel___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_oneLayerNatModel;
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_oneLayerNatModel___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_oneLayerNatModel___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_oneLayerNatModel___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_lp_UadfU0Paper_UadfU0_Examples_oneLayerNatModel() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(lp_UadfU0Paper_UadfU0_Examples_oneLayerNatModel___lam__0), 1, 0);
x_2 = lean_alloc_closure((void*)(lp_UadfU0Paper_UadfU0_Examples_oneLayerNatModel___lam__1), 2, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_lp_UadfU0Paper_UadfU0_Examples_onlyOne() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_InterLayer_Adequacy(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_UadfU0Paper_UadfU0_Examples_AdequacyCounterexample(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_InterLayer_Adequacy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_UadfU0Paper_UadfU0_Examples_oneLayerNatModel = _init_lp_UadfU0Paper_UadfU0_Examples_oneLayerNatModel();
lean_mark_persistent(lp_UadfU0Paper_UadfU0_Examples_oneLayerNatModel);
lp_UadfU0Paper_UadfU0_Examples_onlyOne = _init_lp_UadfU0Paper_UadfU0_Examples_onlyOne();
lean_mark_persistent(lp_UadfU0Paper_UadfU0_Examples_onlyOne);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
