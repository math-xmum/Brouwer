// Lean compiler output
// Module: Gametheory.Simplex
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_funlike___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_Gametheory_stdSimplex_funlike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Gametheory_stdSimplex_funlike___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Gametheory_stdSimplex_funlike___closed__0 = (const lean_object*)&lp_Gametheory_stdSimplex_funlike___closed__0_value;
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_funlike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_funlike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_pure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_pure___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_funlike___lam__0(lean_object* v_self_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_self_1_, v___y_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_funlike(lean_object* v_k_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_00_u03b1_8_, lean_object* v_inst_9_, lean_object* v_inst_10_){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = ((lean_object*)(lp_Gametheory_stdSimplex_funlike___closed__0));
return v___f_11_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_funlike___boxed(lean_object* v_k_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_Gametheory_stdSimplex_funlike(v_k_12_, v_inst_13_, v_inst_14_, v_00_u03b1_15_, v_inst_16_, v_inst_17_);
lean_dec_ref(v_inst_17_);
lean_dec(v_inst_16_);
lean_dec_ref(v_inst_14_);
lean_dec_ref(v_inst_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_pure___redArg___lam__0(lean_object* v_inst_19_, lean_object* v_i_20_, lean_object* v_inst_21_, lean_object* v_j_22_){
_start:
{
lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_apply_2(v_inst_19_, v_i_20_, v_j_22_);
v___x_24_ = lean_unbox(v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v_toSemiring_25_; lean_object* v___x_26_; lean_object* v_toZero_27_; 
v_toSemiring_25_ = lean_ctor_get(v_inst_21_, 0);
lean_inc_ref(v_toSemiring_25_);
lean_dec_ref(v_inst_21_);
v___x_26_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_25_);
v_toZero_27_ = lean_ctor_get(v___x_26_, 1);
lean_inc(v_toZero_27_);
lean_dec_ref(v___x_26_);
return v_toZero_27_;
}
else
{
lean_object* v___x_28_; lean_object* v_toAddMonoidWithOne_29_; lean_object* v_toOne_30_; 
v___x_28_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_21_);
v_toAddMonoidWithOne_29_ = lean_ctor_get(v___x_28_, 1);
lean_inc_ref(v_toAddMonoidWithOne_29_);
lean_dec_ref(v___x_28_);
v_toOne_30_ = lean_ctor_get(v_toAddMonoidWithOne_29_, 2);
lean_inc(v_toOne_30_);
lean_dec_ref(v_toAddMonoidWithOne_29_);
return v_toOne_30_;
}
}
}
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_pure___redArg(lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_i_33_){
_start:
{
lean_object* v___f_34_; 
v___f_34_ = lean_alloc_closure((void*)(lp_Gametheory_stdSimplex_pure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_34_, 0, v_inst_32_);
lean_closure_set(v___f_34_, 1, v_i_33_);
lean_closure_set(v___f_34_, 2, v_inst_31_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_pure(lean_object* v_k_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_00_u03b1_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_i_42_){
_start:
{
lean_object* v___f_43_; 
v___f_43_ = lean_alloc_closure((void*)(lp_Gametheory_stdSimplex_pure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_43_, 0, v_inst_41_);
lean_closure_set(v___f_43_, 1, v_i_42_);
lean_closure_set(v___f_43_, 2, v_inst_36_);
return v___f_43_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_stdSimplex_pure___boxed(lean_object* v_k_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_00_u03b1_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_i_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_Gametheory_stdSimplex_pure(v_k_44_, v_inst_45_, v_inst_46_, v_inst_47_, v_00_u03b1_48_, v_inst_49_, v_inst_50_, v_i_51_);
lean_dec(v_inst_49_);
lean_dec_ref(v_inst_46_);
return v_res_52_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gametheory_Gametheory_Simplex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
