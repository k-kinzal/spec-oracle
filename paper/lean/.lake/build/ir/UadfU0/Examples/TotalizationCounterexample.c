// Lean compiler output
// Module: UadfU0.Examples.TotalizationCounterexample
// Imports: public import Init public import UadfU0.Definitions.Model
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
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_totalizedProj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_One_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_partialModel___lam__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_UadfU0Paper_UadfU0_Examples_instDecidableEqOne(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_partialModel___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_totalizedProj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_One_toCtorIdx(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_One_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_instDecidableEqOne___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_partialModel;
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_One_toCtorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_One_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_One_ofNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_UadfU0Paper_UadfU0_Examples_One_ofNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_UadfU0Paper_UadfU0_Examples_instDecidableEqOne(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_instDecidableEqOne___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_UadfU0Paper_UadfU0_Examples_instDecidableEqOne(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_partialModel___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_partialModel___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
}
}
static lean_object* _init_lp_UadfU0Paper_UadfU0_Examples_partialModel() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(lp_UadfU0Paper_UadfU0_Examples_partialModel___lam__0), 1, 0);
x_2 = lean_alloc_closure((void*)(lp_UadfU0Paper_UadfU0_Examples_partialModel___lam__1), 2, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_totalizedProj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_totalizedProj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_UadfU0Paper_UadfU0_Examples_totalizedProj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_Definitions_Model(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_UadfU0Paper_UadfU0_Examples_TotalizationCounterexample(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_Definitions_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_UadfU0Paper_UadfU0_Examples_partialModel = _init_lp_UadfU0Paper_UadfU0_Examples_partialModel();
lean_mark_persistent(lp_UadfU0Paper_UadfU0_Examples_partialModel);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
