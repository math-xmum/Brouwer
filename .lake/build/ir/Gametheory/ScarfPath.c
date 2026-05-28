// Lean compiler output
// Module: Gametheory.ScarfPath
// Imports: public import Init public meta import Init public import Gametheory.Scarf
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
LEAN_EXPORT lean_object* lp_Gametheory_IndexedLOrder_GiGraph(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_IndexedLOrder_GiGraph___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_IndexedLOrder_GiGraph(lean_object* v_T_1_, lean_object* v_I_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_IST_5_, lean_object* v_c_6_, lean_object* v_i_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_IndexedLOrder_GiGraph___boxed(lean_object* v_T_9_, lean_object* v_I_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_IST_13_, lean_object* v_c_14_, lean_object* v_i_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_Gametheory_IndexedLOrder_GiGraph(v_T_9_, v_I_10_, v_inst_11_, v_inst_12_, v_IST_13_, v_c_14_, v_i_15_);
lean_dec(v_i_15_);
lean_dec(v_c_14_);
lean_dec_ref(v_IST_13_);
lean_dec_ref(v_inst_12_);
lean_dec_ref(v_inst_11_);
return v_res_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Gametheory_Gametheory_Scarf(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gametheory_Gametheory_ScarfPath(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gametheory_Gametheory_Scarf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
