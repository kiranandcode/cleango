#include "lean/lean.h"
#include <stdio.h>
#include "clingo.h"

#define REGISTER_LEAN_CLASS(NAME, FINALISER, FOREACH) \
  static lean_external_class * g_ ## NAME ## _class; \
  static lean_external_class * get_ ## NAME ## _class() { \
     if(g_ ## NAME ## _class == NULL) { g_ ## NAME ## _class = lean_register_external_class(&FINALISER,&FOREACH); } \
     return g_ ## NAME ## _class; \
  }


/* * Utilities
 ============================================================
*/ 
inline static void noop_foreach(void *mod, b_lean_obj_arg fn) {}

/**
 * Prod.mk a b
 */
static inline lean_object * lean_mk_tuple(lean_object * a, lean_object * b) {
  lean_object* tuple = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(tuple, 0, a);
  lean_ctor_set(tuple, 1, b);
  return tuple;
}

/**
 * Except.ok a
 */
static inline lean_object * lean_mk_except_ok(lean_object * a) {
  lean_object* tuple = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(tuple, 0, a);
  return tuple;
}


/**
 * Except.err a
 */
static inline lean_object * lean_mk_except_err(lean_object * a) {
  lean_object* tuple = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(tuple, 0, a);
  return tuple;
}


/**
 * Option.some a
 */
static inline lean_object * lean_mk_option_some(lean_object * a) {
  lean_object* tuple = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(tuple, 0, a);
  return tuple;
}

/**
 * Option.none.
 * Note that this is the same value for Unit and other constant constructors of inductives.
 */
static inline lean_object * lean_mk_option_none() {
  return lean_box(0);
}

/**
 * Clingo.Location
 */
lean_object * lean_clingo_location_to_location(clingo_location_t *loc) {
  lean_object *tuple =
    lean_alloc_ctor(0, 6, 0);

  lean_object *beginFileObj = lean_mk_string(loc->begin_file);
  lean_object *endFileObj = lean_mk_string(loc->end_file);
  lean_object *beginLineObj = lean_int_to_int(loc->begin_line);
  lean_object *endLineObj = lean_int_to_int(loc->end_line);
  lean_object *beginColumnObj = lean_int_to_int(loc->begin_column);
  lean_object *endColumnObj = lean_int_to_int(loc->end_column);

  lean_ctor_set(tuple, 0, beginFileObj);
  lean_ctor_set(tuple, 1, endFileObj);
  lean_ctor_set(tuple, 2, beginLineObj);
  lean_ctor_set(tuple, 3, endLineObj);
  lean_ctor_set(tuple, 4, beginColumnObj);
  lean_ctor_set(tuple, 5, endColumnObj);

  return tuple;
}

lean_object *lean_clingo_solve_result_to_solve_result(clingo_solve_result_bitset_t result) {
  lean_object *resultObj = lean_alloc_ctor(0, 0, 4);
  uint8_t *scalarPtr =  lean_ctor_scalar_cptr(resultObj);
  scalarPtr[0] = (result & clingo_solve_result_satisfiable);
  scalarPtr[1] = (result & clingo_solve_result_unsatisfiable);
  scalarPtr[2] = (result & clingo_solve_result_exhausted);
  scalarPtr[3] = (result & clingo_solve_result_interrupted);
  return resultObj;
}

/* * Clingo Utilities
 ============================================================
*/ 

lean_obj_res lean_mk_clingo_error() {
  clingo_error_t code = clingo_error_code();
  char const *str = clingo_error_message();
  if(str == NULL) { str = ""; }
  lean_object *err_code = lean_box(code);
  lean_object *err_message = lean_mk_string(str);
  lean_object *tuple = lean_mk_tuple(err_code, err_message);

  return (lean_mk_except_err(tuple));
}


/* Clingo.version : IO (Int × Int × Int)  */
lean_obj_res lean_clingo_version() {
  int major = 0;
  int minor = 0;
  int revision = 0;
  clingo_version(&major, &minor, &revision);
  lean_object *major_obj = lean_int_to_int(major);
  lean_object *minor_obj = lean_int_to_int(minor);
  lean_object *revision_obj = lean_int_to_int(revision);

  lean_object *tuple =
    lean_alloc_ctor(0, 3, 0);
  lean_ctor_set(tuple, 0, major_obj);
  lean_ctor_set(tuple, 1, minor_obj);
  lean_ctor_set(tuple, 2, revision_obj);

  return lean_io_result_mk_ok(tuple);
}



/* Clingo.error_code : IO Clingo.Error */
lean_obj_res lean_clingo_error_code() {
  return lean_io_result_mk_ok(lean_box(clingo_error_code()));
}

/* Clingo.error_message : IO (Option String) */
lean_obj_res lean_clingo_error_message() {
  char const *str = clingo_error_message();
  if(str == NULL) {
    return lean_io_result_mk_ok(lean_mk_option_none());
  }
  return lean_io_result_mk_ok(lean_mk_option_some(lean_mk_string(str)));
}

lean_obj_res lean_clingo_mk_io_error() {
  char const *str = clingo_error_message();
  if(str == NULL) { str = "no further details"; }
  switch (clingo_error_code()) {
      case clingo_error_success:
        return lean_mk_io_error_other_error(0, lean_mk_string(str));
      case clingo_error_logic:
      case clingo_error_runtime:
        return lean_mk_io_user_error(lean_mk_string(str));
      case clingo_error_bad_alloc:
        return lean_mk_io_error_resource_exhausted(0, lean_mk_string(str));
      case clingo_error_unknown:
      default:
        return lean_mk_io_error_other_error(1, lean_mk_string(str));
  }
}



/* * Logger */
static void lean_clingo_logger_callback_wrapper(clingo_warning_t code, char const *message, void *data) {
  lean_object *userCallback = (lean_object *)data;
  lean_object *result = lean_apply_3(userCallback, lean_box(code), lean_mk_string(message), lean_io_mk_world());
  if(lean_ptr_tag(result) == 1) {
      lean_io_result_show_error(result);
  }
  lean_dec_ref(result);
  return;

}

/* * Signature
 ============================================================
*/ 


/* Clingo.Signature.mk : String -> Int -> Bool -> Except String Signature */
lean_obj_res lean_clingo_signature_mk(lean_object *str, uint32_t arity, uint8_t is_positive) {
  uint64_t sig;
  bool success = clingo_signature_create(lean_string_cstr(str), arity, is_positive, &sig);
  if(success) {
    return lean_io_result_mk_ok(lean_mk_except_ok(lean_box_uint64(sig)));
  } else {
    char const *err_str = clingo_error_message();
    return lean_io_result_mk_ok(lean_mk_except_err(lean_mk_string(err_str)));
  }
}

/* Clingo.Signature.name : Signature -> String */
lean_object *lean_clingo_signature_name(uint64_t sig) {
  char const *str = clingo_signature_name(sig);
  return (lean_mk_string(str));
}

/* Clingo.Signature.arity : Signature -> UInt32 */
uint32_t lean_clingo_signature_arity(uint64_t sig) {
  uint32_t arity = clingo_signature_arity(sig);
  return (arity);
}

/* Clingo.Signature.isPositive : Signature -> Bool */
uint8_t lean_clingo_signature_is_positive(uint64_t sig) {
  bool is_positive = clingo_signature_is_positive(sig);
  return ((is_positive));
}

/* Clingo.Signature.isNegative : Signature -> Bool */
uint8_t lean_clingo_signature_is_negative(uint64_t sig) {
  bool is_negative = clingo_signature_is_negative(sig);
  return is_negative;
}

/* Clingo.Signature.beq : Signature -> Signature -> Bool */
uint8_t lean_clingo_signature_beq(uint64_t a, uint64_t b) {
  bool equal = clingo_signature_is_equal_to(a, b);
  return equal;
}

/* Clingo.Signature.blt : Signature -> Signature -> Bool */
uint8_t lean_clingo_signature_blt(uint64_t a, uint64_t b) {
  bool equal = clingo_signature_is_less_than(a, b);
  return equal;
}

/* Clingo.Signature.hash : Signature -> Uint64 */
uint64_t lean_clingo_signature_hash(uint64_t a) {
  size_t hash = clingo_signature_hash(a);
  return hash;
}

/* * Symbol
 ============================================================
*/ 

/* Clingo.Symbol.mk_number : Int -> IO Symbol  */
lean_obj_res lean_clingo_symbol_mk_number(lean_object *number) {
  clingo_symbol_t symbol;
  clingo_symbol_create_number(lean_scalar_to_int(number), &symbol);
  return lean_io_result_mk_ok(lean_box_uint64(symbol));
}

/* Clingo.Symbol.mk_supremum : IO Symbol  */
lean_obj_res lean_clingo_symbol_mk_supremum() {
  clingo_symbol_t symbol;
  clingo_symbol_create_supremum(&symbol);
  return lean_io_result_mk_ok(lean_box_uint64(symbol));
}

/* Clingo.Symbol.mk_infimum : IO Symbol  */
lean_obj_res lean_clingo_symbol_mk_infimum() {
  clingo_symbol_t symbol;
  clingo_symbol_create_infimum(&symbol);
  return lean_io_result_mk_ok(lean_box_uint64(symbol));
}

/* Clingo.Symbol.mk_string : @& String -> IO Symbol  */
lean_obj_res lean_clingo_symbol_mk_string(lean_object *str) {
  clingo_symbol_t symbol;
  clingo_symbol_create_string(lean_string_cstr(str), &symbol);
  return lean_io_result_mk_ok(lean_box_uint64(symbol));
}

/* Clingo.Symbol.mk_id : @& String -> Bool -> IO Symbol  */
lean_obj_res lean_clingo_symbol_mk_id(lean_object *str, uint8_t is_positive) {
  clingo_symbol_t symbol;
  clingo_symbol_create_id(lean_string_cstr(str), is_positive, &symbol);
  return lean_io_result_mk_ok(lean_box_uint64(symbol));
}

/* Clingo.Symbol.mk_fun : @& String -> Array Symbol -> Bool -> IO Symbol  */
lean_obj_res lean_clingo_symbol_mk_fun(lean_object *str, lean_object *args, uint8_t is_positive) {
  clingo_symbol_t symbol;

  lean_array_object *argsObj = lean_to_array(args);
  size_t c_args_size = argsObj->m_size;
  clingo_symbol_t *c_args = malloc(sizeof(*c_args) * c_args_size);
  for(size_t i = 0; i < c_args_size; i++) { c_args[i] = lean_unbox_uint64(argsObj->m_data[i]); };
  clingo_symbol_create_function(lean_string_cstr(str), c_args, c_args_size, is_positive, &symbol);
  free(c_args);
  return lean_io_result_mk_ok(lean_box_uint64(symbol));
}

/* Clingo.Symbol.number? : Symbol -> Option Int  */
lean_obj_res lean_clingo_symbol_number(uint64_t symbol) {
  int number;
  bool success = clingo_symbol_number(symbol, &number);
  if (success) {
    return lean_mk_option_some(lean_int_to_int(number));
  } else {
    return lean_mk_option_none();
  }
}

/* Clingo.Symbol.name? : Symbol -> Option Int  */
lean_obj_res lean_clingo_symbol_name(uint64_t symbol) {
  const char *name;
  bool success = clingo_symbol_name(symbol, &name);
  if (success) {
    return lean_mk_option_some(lean_mk_string(name));
  } else {
    return lean_mk_option_none();
  }
}

/* Clingo.Symbol.string? : Symbol -> Option Int  */
lean_obj_res lean_clingo_symbol_string(uint64_t symbol) {
  const char *name;
  bool success = clingo_symbol_string(symbol, &name);
  if (success) {
    return lean_mk_option_some(lean_mk_string(name));
  } else {
    return lean_mk_option_none();
  }
}

/* Clingo.Symbol.isPositive? : Symbol -> Option Bool  */
lean_obj_res lean_clingo_symbol_positive(uint64_t symbol) {
  bool positive;
  bool success = clingo_symbol_is_positive(symbol, &positive);
  if (success) {
    return lean_mk_option_some(lean_box(positive));
  } else {
    return lean_mk_option_none();
  }
}


/* Clingo.Symbol.isNegative? : Symbol -> Option Bool  */
lean_obj_res lean_clingo_symbol_negative(uint64_t symbol) {
  bool negative;
  bool success = clingo_symbol_is_negative(symbol, &negative);
  if (success) {
    return lean_mk_option_some(lean_box(negative));
  } else {
    return lean_mk_option_none();
  }
}

/* Clingo.Symbol.arguments? : Symbol -> Option (Array Symbol)  */
lean_obj_res lean_clingo_symbol_arguments(uint64_t symbol) {
  const clingo_symbol_t *arguments;
  size_t arguments_size;
  bool success = clingo_symbol_arguments(symbol, &arguments, &arguments_size);
  if (success) {
    lean_object *array = lean_alloc_array(arguments_size, arguments_size);
    lean_object **array_ptr = lean_array_cptr(array);
    for(size_t i = 0; i < arguments_size; i++) {
      array_ptr[i] = lean_box_uint64(arguments[i]);
    }
    return lean_mk_option_some(array);
  } else {
    return lean_mk_option_none();
  }
}

static inline uint8_t clingo_symbol_to_lean_symbol(int symbol) {
  switch(symbol) {
  case clingo_symbol_type_infimum: return 0;
  case clingo_symbol_type_number: return 1;
  case clingo_symbol_type_string: return 2;
  case clingo_symbol_type_function: return 3;
  case clingo_symbol_type_supremum: return 4;
  }
}

static inline int lean_symbol_to_clingo_symbol(uint8_t symbol) {
  switch(symbol) {
  case 0: return clingo_symbol_type_infimum;
  case 1: return clingo_symbol_type_number;
  case 2: return clingo_symbol_type_string;
  case 3: return clingo_symbol_type_function;
  case 4: return clingo_symbol_type_supremum;
  }
}

/* Clingo.Symbol.type : Symbol -> SymbolType  */
uint8_t lean_clingo_symbol_type(uint64_t symbol) {
  bool negative;
  int type = clingo_symbol_type(symbol);
  return clingo_symbol_to_lean_symbol(type);
}

/* Clingo.Symbol.toString : Symbol -> String  */
lean_obj_res lean_clingo_symbol_to_string(uint64_t symbol) {
  size_t strSize;
  char *str;
  clingo_symbol_to_string_size(symbol, &strSize);
  str = malloc(sizeof(*str) * strSize);
  clingo_symbol_to_string(symbol, str, strSize);
  lean_object *strObj = lean_mk_string(str);
  free(str);
  return strObj;
}

/* Clingo.Symbol.beq : Symbol -> Symbol -> Bool */
uint8_t lean_clingo_symbol_beq(uint64_t a, uint64_t b) {
  bool equal = clingo_symbol_is_equal_to(a, b);
  return equal;
}

/* Clingo.Symbol.blt : Symbol -> Symbol -> Bool */
uint8_t lean_clingo_symbol_blt(uint64_t a, uint64_t b) {
  bool equal = clingo_symbol_is_less_than(a, b);
  return equal;
}

/* Clingo.Symbol.hash : Symbol -> Uint64 */
uint64_t lean_clingo_symbol_hash(uint64_t a) {
  size_t hash = clingo_symbol_hash(a);
  return hash;
}


/* * Statistics
 ============================================================ */
static void clingo_statistics_finaliser(void *_obj) {  }
REGISTER_LEAN_CLASS(clingo_statistics, clingo_statistics_finaliser, noop_foreach)

/* root: @& Statistics -> UInt64 */
uint64_t lean_clingo_statistics_root(lean_object *obj) {
  clingo_statistics_t *stats = lean_get_external_data(obj);
  uint64_t key = 0;

  bool success = clingo_statistics_root(stats, &key);
  assert(success);

  return key;
}

/* type: @& Statistics -> UInt64 -> StatisticsType */
uint8_t lean_clingo_statistics_type(lean_object *obj, uint64_t key) {
  clingo_statistics_t *stats = lean_get_external_data(obj);
  clingo_statistics_type_t ty = 0;

  bool success = clingo_statistics_type(stats, key, &ty);
  assert(success);

  return ty;
}

/* arraySize: @& Statistics -> UInt64 -> USize */
size_t lean_clingo_statistics_array_size(lean_object *obj, uint64_t key) {
  clingo_statistics_t *stats = lean_get_external_data(obj);
  size_t size = 0;

  bool success = clingo_statistics_array_size(stats, key, &size);
  assert(success);

  return size;
}

/* arrayRef: @& Statistics -> (key: UInt64) -> (offset: USize) -> UInt64 */
uint64_t lean_clingo_statistics_array_ref(lean_object *obj, uint64_t key, size_t offset) {
  clingo_statistics_t *stats = lean_get_external_data(obj);  
  uint64_t res = 0;

  bool success = clingo_statistics_array_at(stats, key, offset, &res);
  assert(success);

  return res;
}

/* mapSize: @& Statistics -> USize */
size_t lean_clingo_statistics_map_size(lean_object *obj, uint64_t key) {
  clingo_statistics_t *stats = lean_get_external_data(obj);  
  size_t size = 0;

  bool success = clingo_statistics_map_size(stats, key, &size);
  assert(success);

  return size;
}

/* mapHasKey?: @& Statistics -> (key: UInt64) -> (name : @& String) -> Bool */
uint8_t lean_clingo_statistics_map_has_key(lean_object *obj, uint64_t key, lean_object *str) {
  clingo_statistics_t *stats = lean_get_external_data(obj);  
  bool has_key = 0;

  bool success = clingo_statistics_map_has_subkey(stats, key, lean_string_cstr(str), &has_key);
  assert(success);

  return has_key;
}

/* mapRef: @& Statistics -> (key: UInt64) -> (name : @& String) -> UInt64 */
uint64_t lean_clingo_statistics_map_ref(lean_object *obj, uint64_t key, lean_object *name) {
  clingo_statistics_t *stats = lean_get_external_data(obj);  
  uint64_t res = 0;

  bool success = clingo_statistics_map_at(stats, key, lean_string_cstr(name), &res);
  assert(success);

  return res;
}

/* valueGet: @& Statistics -> (key: UInt64) -> Float */
lean_obj_res lean_clingo_statistics_value_get(lean_object *obj, uint64_t key) {
  clingo_statistics_t *stats = lean_get_external_data(obj);  
  double res = 0.0;

  bool success = clingo_statistics_value_get(stats, key, &res);
  assert(success);

  return lean_box_float(res);  
}


/* * Model
 ============================================================ */
static void clingo_model_finaliser(void *_obj) {  }
REGISTER_LEAN_CLASS(clingo_model, clingo_model_finaliser, noop_foreach)

/* type: @& Model -> ModelType */
uint8_t lean_clingo_model_type(lean_object *modelObj) {
  clingo_model_t *model = lean_get_external_data(modelObj);
  clingo_model_type_t type;
  bool success = clingo_model_type(model, &type);
  assert(success);
  return type;
}

/* id: @& Model -> UInt64 */
uint64_t lean_clingo_model_number(lean_object *modelObj) {
  clingo_model_t *model = lean_get_external_data(modelObj);
  uint64_t number = 0;
  bool success = clingo_model_number(model, &number);
  assert(success);
  return number;
}

clingo_show_type_bitset_t lean_clingo_calculate_flags(lean_object *filterFlags) {
  clingo_show_type_bitset_t show = 0;
  uint8_t *flags = lean_ctor_scalar_cptr(filterFlags);
  if(flags[0]) show |= clingo_show_type_csp;
  if(flags[1]) show |= clingo_show_type_shown;
  if(flags[2]) show |= clingo_show_type_atoms;
  if(flags[3]) show |= clingo_show_type_terms;
  if(flags[4]) show |= clingo_show_type_all;
  if(flags[5]) show |= clingo_show_type_complement;
  return show;
}

/* size: @& Model -> @& FilterFlags -> USize */
size_t lean_clingo_model_size(lean_object *modelObj, lean_object *filterFlags) {
  clingo_model_t *model = lean_get_external_data(modelObj);
  size_t size = 0;
  clingo_show_type_bitset_t show = lean_clingo_calculate_flags(filterFlags);
  bool success = clingo_model_symbols_size(model, show, &size);
  assert(success);
  return size;
}

/* symbols: @& Model -> @& FilterFlags -> Array Symbol */
lean_obj_res lean_clingo_model_symbols(lean_object *modelObj, lean_object *filterFlags) {
  clingo_model_t *model = NULL;
  size_t size = 0;
  bool success = true;
  clingo_show_type_bitset_t show = 0;
  clingo_symbol_t *symbols = NULL;

  model = lean_get_external_data(modelObj);
  show = lean_clingo_calculate_flags(filterFlags);

  success = clingo_model_symbols_size(model, show, &size);
  assert(success);

  symbols = malloc(sizeof(*symbols) * size);
  assert(symbols != NULL);
  
  success = clingo_model_symbols(model, show, symbols, size);
  assert(success);

  lean_object *res = lean_alloc_array(size, size);
  lean_object **res_ptr = lean_array_cptr(res);
  for(size_t i = 0; i < size; i ++) {
    res_ptr[i] = lean_box_uint64(symbols[i]);
  }
  free(symbols);

  return res;
}

/* contains?: @& Model -> Atom -> Bool */
uint8_t lean_clingo_model_contains(lean_object *modelObj, uint32_t atom) {
  clingo_model_t *model = lean_get_external_data(modelObj);
  bool contained = false;
  bool success = clingo_model_contains(model, atom, &contained);
  assert(success);
  return contained;
}

/* is_true?: @& Model -> Literal -> Bool */
uint8_t lean_clingo_model_is_true(lean_object *modelObj, int32_t literal) {
  clingo_model_t *model = lean_get_external_data(modelObj);
  bool is_true = false;
  bool success = clingo_model_is_true(model, literal, &is_true);
  assert(success);
  return is_true;
}

/* costs: @& Model -> Array Int */
lean_obj_res lean_clingo_model_costs(lean_object *modelObj) {
  clingo_model_t *model = NULL;
  bool success = true;
  size_t size = 0;
  int64_t *costs = NULL;

  model = lean_get_external_data(modelObj);
  success = clingo_model_cost_size(model, &size);
  assert(success);

  costs = malloc(sizeof(*costs) * size);
  assert(costs != NULL);
  
  success = clingo_model_cost(model, costs, size);
  assert(success);
  
  lean_object *res = lean_alloc_array(size, size);
  lean_object **res_ptr = lean_array_cptr(res);
  for(size_t i = 0; i < size; i ++) {
    res_ptr[i] = lean_int_to_int(costs[i]);
  }
  free(costs);

  return res;
}

/* optimal?: @& Model -> Bool */
uint8_t lean_clingo_model_optimality_proven(lean_object *modelObj) {
  clingo_model_t *model = lean_get_external_data(modelObj);
  bool is_optimal = false;
  bool success = clingo_model_optimality_proven(model, &is_optimal);
  assert(success);
  return is_optimal;  
}


/* * Solve Handle
 ============================================================ */
static void clingo_solve_handle_finaliser(void *_obj) {  }
REGISTER_LEAN_CLASS(clingo_solve_handle, clingo_solve_handle_finaliser, noop_foreach)

/* Clingo.SolveHandle.get: @& SolveHandle -> IO (Except (Error × String) SolveResult) */
lean_obj_res lean_clingo_solve_handle_get(lean_object *solveHandleObj) {
  clingo_solve_handle_t *solveHandle = lean_get_external_data(solveHandleObj);
  clingo_solve_result_bitset_t result;

  bool success = clingo_solve_handle_get(solveHandle, &result);
  if(success) {
    lean_object *solveResultObj = lean_clingo_solve_result_to_solve_result(result);
    return lean_io_result_mk_ok(lean_mk_except_ok(solveResultObj));
  } else {
    return lean_io_result_mk_ok(lean_mk_except_err(lean_box(clingo_error_code())));
  }
}
/* Clingo.SolveHandle.wait: @& SolveHandle -> Float -> IO Bool */
lean_obj_res lean_clingo_solve_handle_wait(lean_object *solveHandleObj, double timeout) {
  clingo_solve_handle_t *solveHandle = lean_get_external_data(solveHandleObj);
  bool result;
  clingo_solve_handle_wait(solveHandle, timeout, &result);
  return lean_io_result_mk_ok(lean_box(result));
}

/* Clingo.SolveHandle.model: @& SolveHandle -> IO (Except (Error × String) (Option Model)) */
lean_obj_res lean_clingo_solve_handle_model(lean_object *solveHandleObj) {
  clingo_solve_handle_t *solveHandle = lean_get_external_data(solveHandleObj);  
  const clingo_model_t *model;
  bool success = clingo_solve_handle_model(solveHandle, &model);
  if(success) {
    if(model == NULL) {
      return lean_io_result_mk_ok(lean_mk_except_ok(lean_box(0)));
    } else {
      lean_object *modelObj = lean_alloc_external(get_clingo_model_class(), (void *)model);
      return lean_io_result_mk_ok(lean_mk_except_ok(lean_mk_option_some(modelObj)));
    }
  } else {
    return lean_io_result_mk_ok(lean_mk_except_err(lean_box(clingo_error_code())));
  }
}

/* Clingo.SolveHandle.resume: @& SolveHandle -> IO (Except (Error × String) Unit) */
lean_obj_res lean_clingo_solve_handle_resume(lean_object *solveHandleObj) {
  clingo_solve_handle_t *solveHandle = lean_get_external_data(solveHandleObj);  

  bool success = clingo_solve_handle_resume(solveHandle);
  if(success) {
    return lean_io_result_mk_ok(lean_mk_except_ok(lean_box(0)));
  } else {
    return lean_io_result_mk_ok(lean_mk_except_err(lean_box(clingo_error_code())));
  }  
}
/* Clingo.SolveHandle.cancel: @& SolveHandle -> IO (Except (Error × String) Unit) */
lean_obj_res lean_clingo_solve_handle_cancel(lean_object *solveHandleObj) {
  clingo_solve_handle_t *solveHandle = lean_get_external_data(solveHandleObj);  

  bool success = clingo_solve_handle_cancel(solveHandle);
  if(success) {
    return lean_io_result_mk_ok(lean_mk_except_ok(lean_box(0)));
  } else {
    return lean_io_result_mk_ok(lean_mk_except_err(lean_box(clingo_error_code())));
  }  
}

/* Clingo.SolveHandle.close: SolveHandle -> IO (Except (Error × String) Unit) */
lean_obj_res lean_clingo_solve_handle_close(lean_object *solveHandleObj) {
  clingo_solve_handle_t *solveHandle = lean_get_external_data(solveHandleObj);  

  bool success = clingo_solve_handle_close(solveHandle);
  if(success) {
    return lean_io_result_mk_ok(lean_mk_except_ok(lean_box(0)));
  } else {
    return lean_io_result_mk_ok(lean_mk_except_err(lean_box(clingo_error_code())));
  }  
}
/* * Solve Event
 ============================================================ */
lean_object *lean_clingo_mk_solve_event_model(clingo_model_t *model) {
  lean_object *evtObj = lean_alloc_ctor(0, 1, 0);

  if(model == NULL) {
    lean_ctor_set(evtObj, 0, lean_mk_option_none());    
  } else {
    lean_object *modelObj = lean_alloc_external(get_clingo_model_class(), model);
    lean_ctor_set(evtObj, 0, lean_mk_option_some(modelObj));    
  }

  return evtObj;
}
lean_object *lean_clingo_mk_solve_event_stats(clingo_statistics_t **stats) {
  lean_object *perStepObj = lean_alloc_external(get_clingo_model_class(), stats[0]);
  lean_object *accumObj = lean_alloc_external(get_clingo_model_class(), stats[1]);
  lean_object *evtObj = lean_alloc_ctor(1, 2, 0);
  lean_ctor_set(evtObj, 0, perStepObj);
  lean_ctor_set(evtObj, 1, accumObj);
  return evtObj;
}
lean_object *lean_clingo_mk_solve_event_finish(clingo_solve_result_bitset_t *result) {
  lean_object *resultObj = lean_clingo_solve_result_to_solve_result(*result);
  lean_object *evtObj = lean_alloc_ctor(2, 1, 0);
  lean_ctor_set(evtObj, 0, resultObj);
  return resultObj;
}


static bool lean_clingo_solve_event_callback_wrapper(clingo_solve_event_type_t type, void *event, void *data, bool *goon) {

  lean_object *userCallback = (lean_object *)data;

  /* lean_object *result = lean_apply_3(userCallback, lean_box(code), lean_mk_string(message), lean_io_mk_world()); */
  lean_object *eventObj = NULL;
  switch (type) {
  case clingo_solve_event_type_model: 
    eventObj = lean_clingo_mk_solve_event_model((clingo_model_t *)event);
    break;
  case clingo_solve_event_type_statistics: 
    eventObj = lean_clingo_mk_solve_event_stats(((clingo_statistics_t **)event));
    break;
  case clingo_solve_event_type_finish: 

    eventObj = lean_clingo_mk_solve_event_finish((clingo_solve_result_bitset_t *)event);
    break;
  }
  assert(eventObj != NULL);
  lean_object *result = lean_apply_2(userCallback, eventObj, lean_io_mk_world());
  if(lean_ptr_tag(result) == 1) {
      lean_io_result_show_error(result);
  } else {
    bool should_continue = lean_unbox(lean_io_result_get_value(result));
    *goon = should_continue;
  }
  lean_dec_ref(result);
  return true;
}
/* * Control
 ============================================================
*/ 
static void clingo_control_finaliser(void *obj) { clingo_control_free((clingo_control_t *) obj); }
REGISTER_LEAN_CLASS(clingo_control, clingo_control_finaliser, noop_foreach)


/* Clingo.Control.mk_unsafe : @& Array String -> Logger -> UInt64 ->  IO Control */
lean_obj_res lean_clingo_control_mk_unsafe(lean_object *args, lean_object *logger, uint64_t message_limit) {
  clingo_control_t *control = NULL;
  lean_array_object *argsObj = lean_to_array(args);
  size_t c_args_size = argsObj->m_size;
  const char **c_args = malloc(sizeof(*c_args) * c_args_size);
  for(size_t i = 0; i < c_args_size; i++) { c_args[i] = lean_string_cstr(argsObj->m_data[i]); };
  lean_inc_ref(logger);
  bool success =
    clingo_control_new(
         (const char * const*)c_args,
         c_args_size,
         &lean_clingo_logger_callback_wrapper,
         (void *)logger,
         message_limit,
         &control
    );
  free((void *)c_args);
  if(success) {
    lean_object *result = lean_alloc_external(get_clingo_control_class(), control);    
    return lean_io_result_mk_ok(result);
  } else {
    return lean_io_result_mk_error(lean_clingo_mk_io_error());
  }
}

/* Clingo.Control.mk_safe : @& Array String -> Logger -> UInt64 ->  IO (Except Error Control) */
lean_obj_res lean_clingo_control_mk_safe(lean_object *args, lean_object *logger, uint64_t message_limit) {
  clingo_control_t *control = NULL;
  lean_array_object *argsObj = lean_to_array(args);
  size_t c_args_size = argsObj->m_size;
  const char **c_args = malloc(sizeof(*c_args) * c_args_size);
  for(size_t i = 0; i < c_args_size; i++) { c_args[i] = lean_string_cstr(argsObj->m_data[i]); };
  lean_inc_ref(logger);
  bool success =
    clingo_control_new(
         (const char * const*)c_args,
         c_args_size,
         &lean_clingo_logger_callback_wrapper,
         (void *)logger,
         message_limit,
         &control
    );
  free((void *)c_args);
  if(success) {
    lean_object *result = lean_alloc_external(get_clingo_control_class(), control);    
    return lean_io_result_mk_ok(lean_mk_except_ok(result));
  } else {
    return lean_io_result_mk_ok(lean_mk_except_err(lean_box(clingo_error_code())));
  }
}


/* load: @& Control -> String -> IO (Except Error Unit) */
lean_obj_res lean_clingo_control_load(lean_object *controlObj, lean_object *fileObj) {
  clingo_control_t *control = lean_get_external_data(controlObj);
  const char *file = lean_string_cstr(fileObj);
  bool success = clingo_control_load(control, file);

  if(success) {
    return lean_io_result_mk_ok(lean_mk_except_ok(lean_box(0)));
  } else {
    return lean_io_result_mk_ok(lean_mk_clingo_error());
  }
}

/* Clingo.Control.add : @& Control -> (name : @& String) -> (params: @& Array String) -> (program: @& String) -> IO (Except Error Unit) */
lean_obj_res lean_clingo_control_add(lean_object *controlObj, lean_object *nameObj, lean_object* paramsObj, lean_object* contentsObj) {
  clingo_control_t *control = lean_get_external_data(controlObj);
  const char *name = lean_string_cstr(nameObj);
  const char *contents = lean_string_cstr(contentsObj);

  lean_array_object *paramsArrayObj = lean_to_array(paramsObj);
  size_t c_params_size = paramsArrayObj->m_size;
  const char **c_params = malloc(sizeof(*c_params) * c_params_size);
  for(size_t i = 0; i < c_params_size; i++) { c_params[i] = lean_string_cstr(paramsArrayObj->m_data[i]); };

  bool success = clingo_control_add(control, name, (char const * const *)c_params, c_params_size, contents);
  free((void *)c_params);

  if(success) {
    return lean_io_result_mk_ok(lean_mk_except_ok(lean_box(0)));
  } else {
    return lean_io_result_mk_ok(lean_mk_clingo_error());
  }
}


/* Clingo.Control.statistics : @& Control -> IO (Except Error Statistics) */
lean_obj_res lean_clingo_control_statistics(lean_object *controlObj) {
  clingo_control_t *control = lean_get_external_data(controlObj);
  const clingo_statistics_t *stats = NULL;

  bool success = clingo_control_statistics(control, &stats);

  if(success) {
    lean_object *result = lean_alloc_external(get_clingo_statistics_class(), (void *)stats);    
    return lean_io_result_mk_ok(lean_mk_except_ok(result));
  } else {
    return lean_io_result_mk_ok(lean_mk_clingo_error());
  }
}


/* Clingo.Control.interrupt : @& Control -> IO Unit */
lean_obj_res lean_clingo_control_interrupt(lean_object *controlObj) {
  clingo_control_t *control = lean_get_external_data(controlObj);

  clingo_control_interrupt(control);

  return lean_io_result_mk_ok(lean_mk_except_ok(lean_box(0)));
}


/* Clingo.Control.solve:
    @& Control -> SolveMode -> (assumptions : @& Array (@& Literal)) -> SolveEventCallback -> IO (Except Error SolveHandle) */
lean_obj_res lean_clingo_solve(lean_object *controlObj, uint8_t solve_mode, lean_object *assumptionsObj, lean_object *solveCallbackObj) {
  clingo_control_t *control = lean_get_external_data(controlObj);

  clingo_solve_handle_t *handle= NULL;
  lean_array_object *assumptionsArrayObj = lean_to_array(assumptionsObj);

  size_t c_assumptions_size = assumptionsArrayObj->m_size;
  clingo_literal_t *c_assumptions=malloc(sizeof(*c_assumptions) * c_assumptions_size);
  assert(c_assumptions != NULL);

  for(size_t i = 0; i < c_assumptions_size; i ++) {
    c_assumptions[i] = lean_unbox(assumptionsArrayObj->m_data[i]);
  }
  bool success =
    clingo_control_solve(control, solve_mode, (const clingo_literal_t *)c_assumptions, c_assumptions_size, &lean_clingo_solve_event_callback_wrapper, solveCallbackObj, &handle);

  free((void *)c_assumptions);

  if(success) {
    lean_object *result = lean_alloc_external(get_clingo_solve_handle_class(), (void *)handle);
    return lean_io_result_mk_ok(lean_mk_except_ok(result));
  } else {
    return lean_io_result_mk_ok(lean_mk_clingo_error());
  }
}

/* lean_obj_res lean_test(lean_object *obj) { */
/*   printf("calling lean test!\n"); */
/*   lean_clingo_logger_callback_wrapper(clingo_warning_runtime_error, "hello", obj); */
/*   return lean_io_result_mk_ok(lean_box(0)); */
/* } */

