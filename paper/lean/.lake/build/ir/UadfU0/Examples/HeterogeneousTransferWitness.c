// Lean compiler output
// Module: UadfU0.Examples.HeterogeneousTransferWitness
// Imports: public import Init public import UadfU0.InterLayer.Transfer
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
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_natL_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__1(uint8_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_isEven___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_boolL_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_instDecidableEqHLayer___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__0(uint8_t);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_natL_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_natL_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorIdx___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_boolL_elim___redArg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_boolL_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_UadfU0Paper_UadfU0_Examples_HLayer_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel;
LEAN_EXPORT uint8_t lp_UadfU0Paper_UadfU0_Examples_instDecidableEqHLayer(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_boolL_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_UadfU0Paper_UadfU0_Examples_isEven(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_natL_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_UadfU0Paper_UadfU0_Examples_isEven(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_isEven___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_UadfU0Paper_UadfU0_Examples_isEven(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_UadfU0Paper_UadfU0_Examples_HLayer_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_natL_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_natL_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_natL_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_UadfU0Paper_UadfU0_Examples_HLayer_natL_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_natL_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_UadfU0Paper_UadfU0_Examples_HLayer_natL_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_boolL_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_boolL_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_boolL_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_UadfU0Paper_UadfU0_Examples_HLayer_boolL_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_boolL_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_UadfU0Paper_UadfU0_Examples_HLayer_boolL_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_UadfU0Paper_UadfU0_Examples_HLayer_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_HLayer_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_UadfU0Paper_UadfU0_Examples_HLayer_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_UadfU0Paper_UadfU0_Examples_instDecidableEqHLayer(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorIdx(x_1);
x_4 = lp_UadfU0Paper_UadfU0_Examples_HLayer_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_instDecidableEqHLayer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lp_UadfU0Paper_UadfU0_Examples_instDecidableEqHLayer(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lp_UadfU0Paper_UadfU0_Examples_isEven(x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel___lam__1___boxed), 2, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_UadfU0Paper_UadfU0_InterLayer_Transfer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_UadfU0Paper_UadfU0_Examples_HeterogeneousTransferWitness(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UadfU0Paper_UadfU0_InterLayer_Transfer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel = _init_lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel();
lean_mark_persistent(lp_UadfU0Paper_UadfU0_Examples_heteroTransferModel);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
