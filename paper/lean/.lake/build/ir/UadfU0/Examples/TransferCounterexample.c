// Lean compiler output
// Module: UadfU0.Examples.TransferCounterexample
// Imports: public import Init public import UadfU0.U0Spec.Construction
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
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_UadfU0Paper_UadfU0_Examples_iLayer;
LEAN_EXPORT uint8_t lp_UadfU0Paper_UadfU0_Examples_jLayer;
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1(uint8_t, lean_object*);
static lean_object* lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_transferCounterModel;
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__0(uint8_t);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1___closed__0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_lp_UadfU0Paper_UadfU0_Examples_transferCounterModel() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1___boxed), 2, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static uint8_t _init_lp_UadfU0Paper_UadfU0_Examples_iLayer() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_lp_UadfU0Paper_UadfU0_Examples_jLayer() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_U0Spec_Construction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_UadfU0Paper_UadfU0_Examples_TransferCounterexample(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_U0Spec_Construction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1___closed__0 = _init_lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1___closed__0();
lean_mark_persistent(lp_UadfU0Paper_UadfU0_Examples_transferCounterModel___lam__1___closed__0);
lp_UadfU0Paper_UadfU0_Examples_transferCounterModel = _init_lp_UadfU0Paper_UadfU0_Examples_transferCounterModel();
lean_mark_persistent(lp_UadfU0Paper_UadfU0_Examples_transferCounterModel);
lp_UadfU0Paper_UadfU0_Examples_iLayer = _init_lp_UadfU0Paper_UadfU0_Examples_iLayer();
lp_UadfU0Paper_UadfU0_Examples_jLayer = _init_lp_UadfU0Paper_UadfU0_Examples_jLayer();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
