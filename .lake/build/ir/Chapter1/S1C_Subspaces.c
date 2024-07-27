// Lean compiler output
// Module: Chapter1.S1C_Subspaces
// Imports: Init Mathlib.Tactic Mathlib.Analysis.Calculus.FDeriv.Add Mathlib.Algebra.Module.Basic Aesop Mathlib.Algebra.Group.Basic Mathlib.Algebra.Group.Defs Mathlib.Data.Real.Basic Mathlib.Data.Fin.VecNotation
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
lean_object* l_Pi_addMonoid___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ex1__41__U___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ex1__41__V___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ex1__41__V___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ex1__41__U(lean_object*);
extern lean_object* l_Real_instAddCommMonoidReal;
LEAN_EXPORT lean_object* l_ex1__41__U___rarg___boxed(lean_object*);
static lean_object* l_subspace__ex1__33___closed__1;
LEAN_EXPORT lean_object* l_subsdpace__ex1__37__V;
LEAN_EXPORT lean_object* l_ex1__41__U___rarg(lean_object*);
lean_object* l_Ring_toNonAssocRing___rarg(lean_object*);
LEAN_EXPORT lean_object* l_subspace__ex1__33___lambda__1___boxed(lean_object*);
lean_object* l_AddMonoid_toAddZeroClass___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ex1__41__V(lean_object*);
LEAN_EXPORT lean_object* l_subspace__ex1__38__W;
LEAN_EXPORT lean_object* l_subspace__ex1__33___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_subspace__ex1__33;
LEAN_EXPORT lean_object* l_subspace__ex1__37__U;
static lean_object* l_subspace__ex1__33___closed__2;
lean_object* l_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___rarg(lean_object*);
LEAN_EXPORT lean_object* l_subspace__ex1__38__U;
LEAN_EXPORT lean_object* l_ex1__41__U___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_subspace__ex1__33___closed__3;
static lean_object* l_subspace__ex1__33___closed__4;
LEAN_EXPORT lean_object* l_subspace__ex1__33___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Real_instAddCommMonoidReal;
return x_2;
}
}
static lean_object* _init_l_subspace__ex1__33___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_subspace__ex1__33___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_subspace__ex1__33___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_subspace__ex1__33___closed__1;
x_2 = l_Pi_addMonoid___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_subspace__ex1__33___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_subspace__ex1__33___closed__2;
x_2 = l_AddMonoid_toAddZeroClass___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_subspace__ex1__33___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_subspace__ex1__33() {
_start:
{
lean_object* x_1; 
x_1 = l_subspace__ex1__33___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_subspace__ex1__33___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_subspace__ex1__33___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_subspace__ex1__37__U() {
_start:
{
lean_object* x_1; 
x_1 = l_subspace__ex1__33___closed__4;
return x_1;
}
}
static lean_object* _init_l_subsdpace__ex1__37__V() {
_start:
{
lean_object* x_1; 
x_1 = l_subspace__ex1__33___closed__4;
return x_1;
}
}
static lean_object* _init_l_subspace__ex1__38__U() {
_start:
{
lean_object* x_1; 
x_1 = l_subspace__ex1__33___closed__4;
return x_1;
}
}
static lean_object* _init_l_subspace__ex1__38__W() {
_start:
{
lean_object* x_1; 
x_1 = l_subspace__ex1__33___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ex1__41__U___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Ring_toNonAssocRing___rarg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___rarg(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ex1__41__U___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_ex1__41__U(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ex1__41__U___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ex1__41__U___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ex1__41__U___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ex1__41__U___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ex1__41__U___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ex1__41__V___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_ex1__41__V(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ex1__41__V___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ex1__41__V___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ex1__41__V___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_FDeriv_Add(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Module_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Aesop(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Group_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Group_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fin_VecNotation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Chapter1_S1C__Subspaces(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_FDeriv_Add(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Module_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Aesop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Group_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Group_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fin_VecNotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_subspace__ex1__33___closed__1 = _init_l_subspace__ex1__33___closed__1();
lean_mark_persistent(l_subspace__ex1__33___closed__1);
l_subspace__ex1__33___closed__2 = _init_l_subspace__ex1__33___closed__2();
lean_mark_persistent(l_subspace__ex1__33___closed__2);
l_subspace__ex1__33___closed__3 = _init_l_subspace__ex1__33___closed__3();
lean_mark_persistent(l_subspace__ex1__33___closed__3);
l_subspace__ex1__33___closed__4 = _init_l_subspace__ex1__33___closed__4();
lean_mark_persistent(l_subspace__ex1__33___closed__4);
l_subspace__ex1__33 = _init_l_subspace__ex1__33();
lean_mark_persistent(l_subspace__ex1__33);
l_subspace__ex1__37__U = _init_l_subspace__ex1__37__U();
lean_mark_persistent(l_subspace__ex1__37__U);
l_subsdpace__ex1__37__V = _init_l_subsdpace__ex1__37__V();
lean_mark_persistent(l_subsdpace__ex1__37__V);
l_subspace__ex1__38__U = _init_l_subspace__ex1__38__U();
lean_mark_persistent(l_subspace__ex1__38__U);
l_subspace__ex1__38__W = _init_l_subspace__ex1__38__W();
lean_mark_persistent(l_subspace__ex1__38__W);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
