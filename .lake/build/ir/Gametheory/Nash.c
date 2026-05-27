// Lean compiler output
// Module: Gametheory.Nash
// Imports: public import Init public meta import Init public import Gametheory.Brouwer_product public import Gametheory.Simplex
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_Game_instInhabitedSS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_FinGame_instFintypeI(lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_FinGame_instFintypeI___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_FinGame_instFintypeSS(lean_object*, lean_object*);
static const lean_string_object lp_Gametheory_FinGame_term_u03bc___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "FinGame"};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__0 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__0_value;
static const lean_string_object lp_Gametheory_FinGame_term_u03bc___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 6, .m_data = "termμ_"};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__1 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__1_value;
static const lean_ctor_object lp_Gametheory_FinGame_term_u03bc___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 167, 159, 228, 182, 3, 142, 233)}};
static const lean_ctor_object lp_Gametheory_FinGame_term_u03bc___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__2_value_aux_0),((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(153, 189, 53, 166, 219, 58, 58, 119)}};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__2 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__2_value;
static const lean_string_object lp_Gametheory_FinGame_term_u03bc___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__3 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__3_value;
static const lean_ctor_object lp_Gametheory_FinGame_term_u03bc___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__4 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__4_value;
static const lean_string_object lp_Gametheory_FinGame_term_u03bc___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "μ"};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__5 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__5_value;
static const lean_ctor_object lp_Gametheory_FinGame_term_u03bc___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__5_value)}};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__6 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__6_value;
static const lean_string_object lp_Gametheory_FinGame_term_u03bc___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__7 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__7_value;
static const lean_ctor_object lp_Gametheory_FinGame_term_u03bc___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__8 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__8_value;
static const lean_ctor_object lp_Gametheory_FinGame_term_u03bc___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__8_value),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__9 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__9_value;
static const lean_ctor_object lp_Gametheory_FinGame_term_u03bc___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__4_value),((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__6_value),((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__9_value)}};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__10 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__10_value;
static const lean_ctor_object lp_Gametheory_FinGame_term_u03bc___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__2_value),((lean_object*)(((size_t)(999) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__10_value)}};
static const lean_object* lp_Gametheory_FinGame_term_u03bc___00__closed__11 = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__11_value;
LEAN_EXPORT const lean_object* lp_Gametheory_FinGame_term_u03bc__ = (const lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__11_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__0 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__0_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__1 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__1_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__2 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__2_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__3 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__3_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__4_value_aux_0),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__4_value_aux_1),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__4_value_aux_2),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__4 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__4_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__5 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__5_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__6_value_aux_0),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__6_value_aux_1),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__6_value_aux_2),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__6 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__6_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__7 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__7_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__8 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__8_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__9 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__9_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__10 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__10_value;
static lean_once_cell_t lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__11;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 167, 159, 228, 182, 3, 142, 233)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__12 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__12_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__12_value)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__13 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__13_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Game"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__14 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__14_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(231, 58, 144, 190, 196, 48, 252, 69)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__15 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__15_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__15_value)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__16 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__16_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Function"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__17 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__17_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(225, 8, 186, 189, 152, 89, 197, 12)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__18 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__18_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__18_value)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__19 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__19_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "BigOperators"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__20 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__20_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(107, 249, 74, 90, 68, 148, 111, 165)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__21 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__21_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__21_value)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__22 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__22_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__23 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__23_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__24 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__24_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__24_value)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__25 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__25_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__26 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__26_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__22_value),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__26_value)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__27 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__27_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__19_value),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__27_value)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__28 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__28_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__16_value),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__28_value)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__29 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__29_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__13_value),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__29_value)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__30 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__30_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__31 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__31_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__32_value_aux_0),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__32_value_aux_1),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__32_value_aux_2),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__32 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__32_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "FinGame2MixedGame"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__33 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__33_value;
static lean_once_cell_t lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__34;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(136, 217, 24, 240, 163, 96, 222, 90)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__35 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__35_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame_term_u03bc___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 167, 159, 228, 182, 3, 142, 233)}};
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__36_value_aux_0),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(249, 152, 209, 2, 134, 87, 115, 50)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__36 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__36_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__37 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__37_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__38 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__38_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__39 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__39_value;
static const lean_ctor_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__40 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__40_value;
static const lean_string_object lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__41 = (const lean_object*)&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__41_value;
LEAN_EXPORT lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_reindex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_reindex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_reindex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_reindex__inv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_reindex__inv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_reindex__inv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex__equiv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex__equiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_Fintype_card___at___00map__mixedS__equiv_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__mixedS__equiv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__mixedS__equiv___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__mixedS__equiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_map__mixedS__equiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Gametheory_Game_instInhabitedSS(lean_object* v_G_1_, lean_object* v_i_2_){
_start:
{
lean_object* v_HSS_3_; lean_object* v___x_4_; 
v_HSS_3_ = lean_ctor_get(v_G_1_, 1);
lean_inc(v_HSS_3_);
lean_dec_ref(v_G_1_);
v___x_4_ = lean_apply_1(v_HSS_3_, v_i_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_FinGame_instFintypeI(lean_object* v_G_5_){
_start:
{
lean_object* v_FinI_6_; 
v_FinI_6_ = lean_ctor_get(v_G_5_, 1);
lean_inc(v_FinI_6_);
return v_FinI_6_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_FinGame_instFintypeI___boxed(lean_object* v_G_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_Gametheory_FinGame_instFintypeI(v_G_7_);
lean_dec_ref(v_G_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_FinGame_instFintypeSS(lean_object* v_G_9_, lean_object* v_i_10_){
_start:
{
lean_object* v_FinSS_11_; lean_object* v___x_12_; 
v_FinSS_11_ = lean_ctor_get(v_G_9_, 2);
lean_inc(v_FinSS_11_);
lean_dec_ref(v_G_9_);
v___x_12_ = lean_apply_1(v_FinSS_11_, v_i_10_);
return v___x_12_;
}
}
static lean_object* _init_lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__11(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__10));
v___x_60_ = l_String_toRawSubstring_x27(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__34(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__33));
v___x_108_ = l_String_toRawSubstring_x27(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1(lean_object* v_x_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = ((lean_object*)(lp_Gametheory_FinGame_term_u03bc___00__closed__2));
lean_inc(v_x_124_);
v___x_128_ = l_Lean_Syntax_isOfKind(v_x_124_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v_x_124_);
v___x_129_ = lean_box(1);
v___x_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v_a_126_);
return v___x_130_;
}
else
{
lean_object* v_quotContext_131_; lean_object* v_currMacroScope_132_; lean_object* v_ref_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_quotContext_131_ = lean_ctor_get(v_a_125_, 1);
v_currMacroScope_132_ = lean_ctor_get(v_a_125_, 2);
v_ref_133_ = lean_ctor_get(v_a_125_, 5);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = l_Lean_Syntax_getArg(v_x_124_, v___x_134_);
lean_dec(v_x_124_);
v___x_136_ = 0;
v___x_137_ = l_Lean_SourceInfo_fromRef(v_ref_133_, v___x_136_);
v___x_138_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__4));
v___x_139_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__6));
v___x_140_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__7));
lean_inc_n(v___x_137_, 8);
v___x_141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_137_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__9));
v___x_143_ = lean_obj_once(&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__11, &lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__11_once, _init_lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__11);
v___x_144_ = lean_box(0);
lean_inc_n(v_currMacroScope_132_, 2);
lean_inc_n(v_quotContext_131_, 2);
v___x_145_ = l_Lean_addMacroScope(v_quotContext_131_, v___x_144_, v_currMacroScope_132_);
v___x_146_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__30));
v___x_147_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_147_, 0, v___x_137_);
lean_ctor_set(v___x_147_, 1, v___x_143_);
lean_ctor_set(v___x_147_, 2, v___x_145_);
lean_ctor_set(v___x_147_, 3, v___x_146_);
v___x_148_ = l_Lean_Syntax_node1(v___x_137_, v___x_142_, v___x_147_);
v___x_149_ = l_Lean_Syntax_node2(v___x_137_, v___x_139_, v___x_141_, v___x_148_);
v___x_150_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__32));
v___x_151_ = lean_obj_once(&lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__34, &lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__34_once, _init_lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__34);
v___x_152_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__35));
v___x_153_ = l_Lean_addMacroScope(v_quotContext_131_, v___x_152_, v_currMacroScope_132_);
v___x_154_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__38));
v___x_155_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_155_, 0, v___x_137_);
lean_ctor_set(v___x_155_, 1, v___x_151_);
lean_ctor_set(v___x_155_, 2, v___x_153_);
lean_ctor_set(v___x_155_, 3, v___x_154_);
v___x_156_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__40));
v___x_157_ = l_Lean_Syntax_node1(v___x_137_, v___x_156_, v___x_135_);
v___x_158_ = l_Lean_Syntax_node2(v___x_137_, v___x_150_, v___x_155_, v___x_157_);
v___x_159_ = ((lean_object*)(lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___closed__41));
v___x_160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_137_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = l_Lean_Syntax_node3(v___x_137_, v___x_138_, v___x_149_, v___x_158_, v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_a_126_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1___boxed(lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lp_Gametheory_FinGame___aux__Gametheory__Nash______macroRules__FinGame__term_u03bc____1(v_x_163_, v_a_164_, v_a_165_);
lean_dec_ref(v_a_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_reindex___redArg(lean_object* v_eI_167_, lean_object* v_x_168_, lean_object* v_k_169_){
_start:
{
lean_object* v___x_170_; lean_object* v_toFun_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lp_mathlib_Equiv_symm___redArg(v_eI_167_);
v_toFun_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_toFun_171_);
lean_dec_ref(v___x_170_);
v___x_172_ = lean_apply_1(v_toFun_171_, v_k_169_);
v___x_173_ = lean_apply_1(v_x_168_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_reindex(lean_object* v_G_174_, lean_object* v_n_175_, lean_object* v_eI_176_, lean_object* v_x_177_, lean_object* v_k_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lp_Gametheory_reindex___redArg(v_eI_176_, v_x_177_, v_k_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_reindex___boxed(lean_object* v_G_180_, lean_object* v_n_181_, lean_object* v_eI_182_, lean_object* v_x_183_, lean_object* v_k_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = lp_Gametheory_reindex(v_G_180_, v_n_181_, v_eI_182_, v_x_183_, v_k_184_);
lean_dec(v_n_181_);
lean_dec_ref(v_G_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_reindex__inv___redArg(lean_object* v_eI_186_, lean_object* v_z_187_, lean_object* v_i_188_){
_start:
{
lean_object* v_toFun_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_toFun_189_ = lean_ctor_get(v_eI_186_, 0);
lean_inc(v_toFun_189_);
lean_dec_ref(v_eI_186_);
v___x_190_ = lean_apply_1(v_toFun_189_, v_i_188_);
v___x_191_ = lean_apply_1(v_z_187_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_reindex__inv(lean_object* v_G_192_, lean_object* v_n_193_, lean_object* v_eI_194_, lean_object* v_z_195_, lean_object* v_i_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lp_Gametheory_reindex__inv___redArg(v_eI_194_, v_z_195_, v_i_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_reindex__inv___boxed(lean_object* v_G_198_, lean_object* v_n_199_, lean_object* v_eI_200_, lean_object* v_z_201_, lean_object* v_i_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = lp_Gametheory_reindex__inv(v_G_198_, v_n_199_, v_eI_200_, v_z_201_, v_i_202_);
lean_dec(v_n_199_);
lean_dec_ref(v_G_198_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___redArg___lam__0(lean_object* v_e_204_, lean_object* v_x_205_, lean_object* v_i_206_){
_start:
{
lean_object* v___x_207_; lean_object* v_toFun_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_207_ = lp_mathlib_Equiv_symm___redArg(v_e_204_);
v_toFun_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_toFun_208_);
lean_dec_ref(v___x_207_);
v___x_209_ = lean_apply_1(v_toFun_208_, v_i_206_);
v___x_210_ = lean_apply_1(v_x_205_, v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___redArg(lean_object* v_e_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = lean_alloc_closure((void*)(lp_Gametheory_map__simplex___redArg___lam__0), 3, 2);
lean_closure_set(v___f_213_, 0, v_e_211_);
lean_closure_set(v___f_213_, 1, v_x_212_);
return v___f_213_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex(lean_object* v_n_214_, lean_object* v_m_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_e_218_, lean_object* v_x_219_){
_start:
{
lean_object* v___f_220_; 
v___f_220_ = lean_alloc_closure((void*)(lp_Gametheory_map__simplex___redArg___lam__0), 3, 2);
lean_closure_set(v___f_220_, 0, v_e_218_);
lean_closure_set(v___f_220_, 1, v_x_219_);
return v___f_220_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___boxed(lean_object* v_n_221_, lean_object* v_m_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_e_225_, lean_object* v_x_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = lp_Gametheory_map__simplex(v_n_221_, v_m_222_, v_inst_223_, v_inst_224_, v_e_225_, v_x_226_);
lean_dec(v_inst_224_);
lean_dec(v_inst_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex__equiv___redArg(lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_e_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
lean_inc_ref(v_e_230_);
lean_inc(v_inst_229_);
lean_inc(v_inst_228_);
v___x_231_ = lean_alloc_closure((void*)(lp_Gametheory_map__simplex___boxed), 6, 5);
lean_closure_set(v___x_231_, 0, lean_box(0));
lean_closure_set(v___x_231_, 1, lean_box(0));
lean_closure_set(v___x_231_, 2, v_inst_228_);
lean_closure_set(v___x_231_, 3, v_inst_229_);
lean_closure_set(v___x_231_, 4, v_e_230_);
v___x_232_ = lp_mathlib_Equiv_symm___redArg(v_e_230_);
v___x_233_ = lean_alloc_closure((void*)(lp_Gametheory_map__simplex___boxed), 6, 5);
lean_closure_set(v___x_233_, 0, lean_box(0));
lean_closure_set(v___x_233_, 1, lean_box(0));
lean_closure_set(v___x_233_, 2, v_inst_229_);
lean_closure_set(v___x_233_, 3, v_inst_228_);
lean_closure_set(v___x_233_, 4, v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_231_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex__equiv(lean_object* v_n_235_, lean_object* v_m_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_e_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lp_Gametheory_map__simplex__equiv___redArg(v_inst_237_, v_inst_238_, v_e_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_Fintype_card___at___00map__mixedS__equiv_spec__0(lean_object* v_G_241_, lean_object* v_i_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lp_Gametheory_FinGame_instFintypeSS(v_G_241_, v_i_242_);
v___x_244_ = l_List_lengthTR___redArg(v___x_243_);
lean_dec(v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1___redArg___lam__0(lean_object* v_e_245_, lean_object* v_x_246_, lean_object* v_i_247_){
_start:
{
lean_object* v___x_248_; lean_object* v_toFun_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_248_ = lp_mathlib_Equiv_symm___redArg(v_e_245_);
v_toFun_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_toFun_249_);
lean_dec_ref(v___x_248_);
v___x_250_ = lean_apply_1(v_toFun_249_, v_i_247_);
v___x_251_ = lean_apply_1(v_x_246_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1___redArg(lean_object* v_e_252_, lean_object* v_x_253_){
_start:
{
lean_object* v___f_254_; 
v___f_254_ = lean_alloc_closure((void*)(lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_254_, 0, v_e_252_);
lean_closure_set(v___f_254_, 1, v_x_253_);
return v___f_254_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1(lean_object* v_G_255_, lean_object* v_i_256_, lean_object* v___x_257_, lean_object* v_e_258_, lean_object* v_x_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = lean_alloc_closure((void*)(lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_260_, 0, v_e_258_);
lean_closure_set(v___f_260_, 1, v_x_259_);
return v___f_260_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1___boxed(lean_object* v_G_261_, lean_object* v_i_262_, lean_object* v___x_263_, lean_object* v_e_264_, lean_object* v_x_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1(v_G_261_, v_i_262_, v___x_263_, v_e_264_, v_x_265_);
lean_dec(v___x_263_);
lean_dec(v_i_262_);
lean_dec_ref(v_G_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2___redArg___lam__0(lean_object* v_e_267_, lean_object* v_x_268_, lean_object* v_i_269_){
_start:
{
lean_object* v___x_270_; lean_object* v_toFun_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_270_ = lp_mathlib_Equiv_symm___redArg(v_e_267_);
v_toFun_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_toFun_271_);
lean_dec_ref(v___x_270_);
v___x_272_ = lean_apply_1(v_toFun_271_, v_i_269_);
v___x_273_ = lean_apply_1(v_x_268_, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2___redArg(lean_object* v_e_274_, lean_object* v_x_275_){
_start:
{
lean_object* v___f_276_; 
v___f_276_ = lean_alloc_closure((void*)(lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2___redArg___lam__0), 3, 2);
lean_closure_set(v___f_276_, 0, v_e_274_);
lean_closure_set(v___f_276_, 1, v_x_275_);
return v___f_276_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2(lean_object* v___x_277_, lean_object* v_G_278_, lean_object* v_i_279_, lean_object* v_e_280_, lean_object* v_x_281_){
_start:
{
lean_object* v___f_282_; 
v___f_282_ = lean_alloc_closure((void*)(lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2___redArg___lam__0), 3, 2);
lean_closure_set(v___f_282_, 0, v_e_280_);
lean_closure_set(v___f_282_, 1, v_x_281_);
return v___f_282_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2___boxed(lean_object* v___x_283_, lean_object* v_G_284_, lean_object* v_i_285_, lean_object* v_e_286_, lean_object* v_x_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2(v___x_283_, v_G_284_, v_i_285_, v_e_286_, v_x_287_);
lean_dec(v_i_285_);
lean_dec_ref(v_G_284_);
lean_dec(v___x_283_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__mixedS__equiv___lam__0(lean_object* v_e_289_, lean_object* v_x_290_, lean_object* v_i_291_, lean_object* v___y_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_inc(v_i_291_);
v___x_293_ = lean_apply_1(v_e_289_, v_i_291_);
v___x_294_ = lean_apply_1(v_x_290_, v_i_291_);
v___x_295_ = lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__1___redArg___lam__0(v___x_293_, v___x_294_, v___y_292_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__mixedS__equiv___lam__1(lean_object* v_e_296_, lean_object* v_x_297_, lean_object* v_i_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_inc(v_i_298_);
v___x_300_ = lean_apply_1(v_e_296_, v_i_298_);
v___x_301_ = lp_mathlib_Equiv_symm___redArg(v___x_300_);
v___x_302_ = lean_apply_1(v_x_297_, v_i_298_);
v___x_303_ = lp_Gametheory_map__simplex___at___00map__mixedS__equiv_spec__2___redArg___lam__0(v___x_301_, v___x_302_, v___y_299_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__mixedS__equiv(lean_object* v_G_304_, lean_object* v_e_305_){
_start:
{
lean_object* v___f_306_; lean_object* v___f_307_; lean_object* v___x_308_; 
lean_inc_ref(v_e_305_);
v___f_306_ = lean_alloc_closure((void*)(lp_Gametheory_map__mixedS__equiv___lam__0), 4, 1);
lean_closure_set(v___f_306_, 0, v_e_305_);
v___f_307_ = lean_alloc_closure((void*)(lp_Gametheory_map__mixedS__equiv___lam__1), 4, 1);
lean_closure_set(v___f_307_, 0, v_e_305_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___f_306_);
lean_ctor_set(v___x_308_, 1, v___f_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* lp_Gametheory_map__mixedS__equiv___boxed(lean_object* v_G_309_, lean_object* v_e_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = lp_Gametheory_map__mixedS__equiv(v_G_309_, v_e_310_);
lean_dec_ref(v_G_309_);
return v_res_311_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Gametheory_Gametheory_Brouwer__product(uint8_t builtin);
lean_object* initialize_Gametheory_Gametheory_Simplex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gametheory_Gametheory_Nash(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gametheory_Gametheory_Brouwer__product(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gametheory_Gametheory_Simplex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
