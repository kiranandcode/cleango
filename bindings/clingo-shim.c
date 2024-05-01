#include "lean/lean.h"
#include <stdio.h>
#include "clingo.h"

#define REGISTER_LEAN_CLASS(NAME, FINALISER, FOREACH) \
  static lean_external_class * g_ ## NAME ## _class; \
  static lean_external_class * get_ ## NAME ## _class() { \
     if(g_ ## NAME ## _class == NULL) { g_ ## NAME ## _class = lean_register_external_class(&FINALISER,&FOREACH); } \
     return g_ ## NAME ## _class; \
  }

#define CLINGO_CONV_ARRAY_SIZED(TY, RESULT, DEST, OBJ, SIZE) do {       \
    RESULT->SIZE = lean_array_size(OBJ);                                \
    RESULT->DEST = malloc(sizeof(*RESULT->DEST) * RESULT->SIZE);        \
    lean_object **arrayObj = lean_array_cptr(OBJ);                      \
    for(size_t i = 0; i<RESULT->SIZE; i++) { lean_clingo_## TY ##_to_ ## TY (arrayObj[i], (clingo_ast_ ## TY ## _t *)&RESULT->DEST[i]); } \
  } while(0)

#define CLINGO_FREE_ARRAY_SIZED(TY, RESULT, DEST, SIZE) do {            \
    for(size_t i = 0; i<RESULT->SIZE; i++) {                            \
      lean_clingo_free_ ## TY ((clingo_ast_ ## TY ## _t *)&RESULT->DEST[i]); \
    }                                                                   \
    free((void *)RESULT->DEST);                                         \
  } while(0)


#define CLINGO_CONV_ARRAY(TY, RESULT, DEST, OBJ) CLINGO_CONV_ARRAY_SIZED(TY, RESULT, DEST, OBJ, size)

#define CLINGO_FREE_ARRAY(TY, RESULT, DEST) CLINGO_FREE_ARRAY_SIZED(TY, RESULT, DEST, size)

#define CLINGO_CONV_OBJ(TY, RESULT, DEST, OBJ) do { \
    RESULT->DEST = malloc(sizeof(*RESULT->DEST));   \
    lean_clingo_ ## TY ## _to_ ## TY(OBJ, (clingo_ast_## TY ##_t *)RESULT->DEST); \
  } while(0)

#define CLINGO_FREE_OBJ(TY, RESULT, DEST) do {                          \
  lean_clingo_free_ ## TY((clingo_ast_ ## TY ## _t *)RESULT->DEST);     \
  free((void *)RESULT->DEST);                                           \
  } while(0)



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
lean_object * lean_clingo_location_to_location(const clingo_location_t *loc) {
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

clingo_location_t clingo_lean_location_to_location(lean_object *obj) {
   clingo_location_t result;
   result.begin_file = lean_string_cstr(lean_ctor_get(obj, 0));
   result.end_file = lean_string_cstr(lean_ctor_get(obj, 1));
   result.begin_line = lean_unbox(lean_ctor_get(obj, 2));
   result.end_line = lean_unbox(lean_ctor_get(obj, 3));
   result.begin_column = lean_unbox(lean_ctor_get(obj, 4));
   result.end_column = lean_unbox(lean_ctor_get(obj, 5));

  return result;
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

typedef const char * clingo_ast_string_t;

static inline void lean_clingo_string_to_string(lean_object *obj, clingo_ast_string_t *result) { *result = lean_string_cstr(obj);}

static inline void lean_clingo_free_string(clingo_ast_string_t *result) { }

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

/* Clingo.Symbol.mk_number : Int -> Symbol  */
uint64_t lean_clingo_symbol_mk_number(lean_object *number) {
  clingo_symbol_t symbol;
  clingo_symbol_create_number(lean_scalar_to_int(number), &symbol);
  return ((symbol));
}

/* Clingo.Symbol.mk_supremum : Unit -> Symbol  */
uint64_t lean_clingo_symbol_mk_supremum(lean_object *_tt) {
  clingo_symbol_t symbol;
  clingo_symbol_create_supremum(&symbol);
  return ((symbol));
}

/* Clingo.Symbol.mk_infimum : Unit -> Symbol  */
uint64_t lean_clingo_symbol_mk_infimum(lean_object *_tt) {
  clingo_symbol_t symbol;
  clingo_symbol_create_infimum(&symbol);
  return ((symbol));
}

/* Clingo.Symbol.mk_string : @& String -> Symbol  */
uint64_t lean_clingo_symbol_mk_string(lean_object *str) {
  clingo_symbol_t symbol;
  clingo_symbol_create_string(lean_string_cstr(str), &symbol);
  return (symbol);
}

/* Clingo.Symbol.mk_id : @& String -> Bool -> Symbol  */
uint64_t lean_clingo_symbol_mk_id(lean_object *str, uint8_t is_positive) {
  clingo_symbol_t symbol;
  clingo_symbol_create_id(lean_string_cstr(str), is_positive, &symbol);
  return (symbol);
}

/* Clingo.Symbol.mk_fun : @& String -> Array Symbol -> Bool -> Symbol  */
uint64_t lean_clingo_symbol_mk_fun(lean_object *str, lean_object *args, uint8_t is_positive) {
  clingo_symbol_t symbol;

  lean_array_object *argsObj = lean_to_array(args);
  size_t c_args_size = argsObj->m_size;
  clingo_symbol_t *c_args = malloc(sizeof(*c_args) * c_args_size);
  if(c_args_size > 0) assert(c_args != NULL);
  for(size_t i = 0; i < c_args_size; i++) { c_args[i] = lean_unbox_uint64(argsObj->m_data[i]); };
  clingo_symbol_create_function(lean_string_cstr(str), c_args, c_args_size, is_positive, &symbol);
  free(c_args);
  return (symbol);
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

/* Clingo.Symbol.name? : Symbol -> Option String  */
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

/* Clingo.Symbol.repr : (s1 : Symbol) -> Repr */
lean_object *lean_clingo_repr(uint64_t symbol) {
  clingo_symbol_type_t ty; 

  lean_object *result = NULL;
  int number;
  const char *name;
  bool success;

  lean_object *array = NULL; 
  lean_object **array_ptr = NULL;

  const clingo_symbol_t *arguments = NULL;
  size_t arguments_size = 0;

  bool positive;
 
  ty = clingo_symbol_type(symbol);
  switch (ty) {
  case clingo_symbol_type_infimum:
    result = lean_alloc_ctor(0, 0, 0);
    break;
  case clingo_symbol_type_number:
    success = clingo_symbol_number(symbol, &number);
    assert(success);
    result = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(result, 0, lean_int_to_int(number));
    break;
  case clingo_symbol_type_string:
    success = clingo_symbol_string(symbol, &name);
    assert(success);
    result = lean_alloc_ctor(2, 1, 0);
    lean_ctor_set(result, 0, lean_mk_string(name));
    break;
  case clingo_symbol_type_function:
    result = lean_alloc_ctor(3, 2, 1);

    success = clingo_symbol_name(symbol, &name);
    assert(success);
    lean_ctor_set(result, 0, lean_mk_string(name));

    success = clingo_symbol_arguments(symbol, &arguments, &arguments_size);
    assert(success);
    array = lean_alloc_array(arguments_size, arguments_size);
    array_ptr = lean_array_cptr(array);
    for(size_t i = 0; i < arguments_size; i++) { array_ptr[i] = lean_clingo_repr(arguments[i]); }
    lean_ctor_set(result, 1, array);

    success = clingo_symbol_is_positive(symbol, &positive);
    assert(success);
    *lean_ctor_scalar_cptr(result) = positive;

    break;
  case clingo_symbol_type_supremum:
    result = lean_alloc_ctor(4, 0, 0);
    break;
  }
  assert(result != NULL);
  return result;
}

/* Clingo.Symbol.mk : (s1 : Repr) -> Symbol */
uint64_t lean_clingo_mk(lean_object *obj) {
  uint64_t symbol;
  lean_object **arrayObj;
  size_t c_args_size;
  clingo_symbol_t *c_args = NULL;

  switch (lean_ptr_tag(obj)) {
  case 0:
    clingo_symbol_create_infimum(&symbol);
    return symbol;
  case 1:
    return lean_clingo_symbol_mk_number((lean_ctor_get(obj, 0)));
  case 2:
    return lean_clingo_symbol_mk_string(lean_ctor_get(obj, 0));
  case 3:
    c_args_size = lean_array_size(lean_ctor_get(obj,1));
    c_args = malloc(sizeof(*c_args) * c_args_size);
    arrayObj = lean_array_cptr(lean_ctor_get(obj,1));
    for(size_t i = 0; i < c_args_size; i++) { c_args[i] = lean_clingo_mk(arrayObj[i]); }
    clingo_symbol_create_function(
         lean_string_cstr(lean_ctor_get(obj, 0)),
         c_args,
         c_args_size,
         *lean_ctor_scalar_cptr(obj),
         &symbol
     );
    free((void *)c_args);
    return symbol;
  case 4:
    clingo_symbol_create_supremum(&symbol);
    return symbol;
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


/* * Ast */
/* ** Term */
/* *** To Term */
void lean_clingo_term_to_term(lean_object *obj, clingo_ast_term_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj, 0));
  lean_object *data = lean_ctor_get(obj, 1);
  result->type = lean_ptr_tag(data);

  clingo_ast_term_t *arguments = NULL;
  lean_object **argumentsArrayObj = NULL;
  
  switch(lean_ptr_tag(data)) {
  case clingo_ast_term_type_symbol:
    result->symbol = *((uint64_t *)lean_ctor_scalar_cptr(data));
    break;
  case clingo_ast_term_type_variable:
     result->variable = lean_string_cstr(lean_ctor_get(data, 0));
    break;
  case clingo_ast_term_type_unary_operation:
    result->unary_operation = malloc(sizeof(*(result->unary_operation)));
    ((clingo_ast_unary_operation_t *)result->unary_operation)->unary_operator = *(lean_ctor_scalar_cptr(data));
    lean_clingo_term_to_term(lean_ctor_get(data, 0), (clingo_ast_term_t *)&result->unary_operation->argument);
    break;
  case clingo_ast_term_type_binary_operation:
    result->binary_operation = malloc(sizeof(*(result->binary_operation)));
    ((clingo_ast_binary_operation_t *)result->binary_operation)->binary_operator = *(lean_ctor_scalar_cptr(data));
    lean_clingo_term_to_term(lean_ctor_get(data, 0), (clingo_ast_term_t *)&result->binary_operation->left);
    lean_clingo_term_to_term(lean_ctor_get(data, 1), (clingo_ast_term_t *)&result->binary_operation->right);
    break;
  case clingo_ast_term_type_interval:
    result->interval = malloc(sizeof(*(result->interval)));
    lean_clingo_term_to_term(lean_ctor_get(data, 0), (clingo_ast_term_t *)&result->interval->left);
    lean_clingo_term_to_term(lean_ctor_get(data, 1), (clingo_ast_term_t *)&result->interval->right);
    break;
  case clingo_ast_term_type_function:
    result->function = malloc(sizeof(*(result->function)));
    ((clingo_ast_function_t *)result->function)->name = lean_string_cstr(lean_ctor_get(data, 0));

    ((clingo_ast_function_t *)result->function)->size = lean_array_size(lean_ctor_get(data,1));
    ((clingo_ast_function_t *)result->function)->arguments = malloc(sizeof(*(result->function->arguments)) * ((clingo_ast_function_t *)result->function)->size);

    argumentsArrayObj = lean_array_cptr(lean_ctor_get(data,1));
    for(size_t i = 0; i<result->function->size;i++){ lean_clingo_term_to_term(argumentsArrayObj[i], (clingo_ast_term_t *) &result->function->arguments[i]); }
    break;
  case clingo_ast_term_type_external_function:
    result->external_function = malloc(sizeof(*(result->external_function)));

    ((clingo_ast_function_t *)result->external_function)->name = lean_string_cstr(lean_ctor_get(data, 0));

    ((clingo_ast_function_t *)result->external_function)->size = lean_array_size(lean_ctor_get(data,1));
    ((clingo_ast_function_t *)result->external_function)->arguments = malloc(sizeof(*(result->external_function->arguments)) * ((clingo_ast_function_t *)result->external_function)->size);

    argumentsArrayObj = lean_array_cptr(lean_ctor_get(data,1));
    for(size_t i = 0; i<result->external_function->size;i++){ lean_clingo_term_to_term(argumentsArrayObj[i], (clingo_ast_term_t *)&result->external_function->arguments[i]); }

    break;
  case clingo_ast_term_type_pool:
    result->pool = malloc(sizeof(*result->pool));

    ((clingo_ast_pool_t *)result->pool)->size = lean_array_size(lean_ctor_get(data, 0));
    ((clingo_ast_pool_t *)result->pool)->arguments = malloc(sizeof(*(result->pool->arguments)) * result->pool->size);

    argumentsArrayObj = lean_array_cptr(lean_ctor_get(data,0));
    for(size_t i = 0; i<result->pool->size;i++){ lean_clingo_term_to_term(argumentsArrayObj[i], (clingo_ast_term_t *)&result->pool->arguments[i]); }

    break;
  }
  return;
}
/* *** Free */
void lean_clingo_free_term(clingo_ast_term_t *result) {
  switch(result->type) {
  case clingo_ast_term_type_symbol:
    break;
  case clingo_ast_term_type_variable:
    break;
  case clingo_ast_term_type_unary_operation:
    lean_clingo_free_term((clingo_ast_term_t *)&result->unary_operation->argument);
     free((void *)result->unary_operation);
    break;
  case clingo_ast_term_type_binary_operation:
    lean_clingo_free_term((clingo_ast_term_t *)&result->binary_operation->left);
    lean_clingo_free_term((clingo_ast_term_t *)&result->binary_operation->right);
    free((void *)result->binary_operation);
    break;
  case clingo_ast_term_type_interval:
    lean_clingo_free_term((clingo_ast_term_t *)&result->interval->left);
    lean_clingo_free_term((clingo_ast_term_t *)&result->interval->right);
    free((void *)result->interval);
    break;
  case clingo_ast_term_type_function:
    for(size_t i = 0; i<result->function->size;i++){ lean_clingo_free_term((clingo_ast_term_t *) &result->function->arguments[i]); }
    free((void *)result->function->arguments);
    free((void *)result->function);
    break;
  case clingo_ast_term_type_external_function:
    for(size_t i = 0; i<result->external_function->size;i++){ lean_clingo_free_term((clingo_ast_term_t *) &result->external_function->arguments[i]); }
    free((void *)result->external_function->arguments);
    free((void *)result->external_function);
    break;
  case clingo_ast_term_type_pool:

    for(size_t i = 0; i<result->pool->size;i++){ lean_clingo_free_term((clingo_ast_term_t *)&result->pool->arguments[i]); }
    free((void *)result->pool->arguments);
    free((void *)result->pool);

    break;
  }
}

/* ** Comparison */
void lean_clingo_comparison_to_comparison(lean_object *obj, clingo_ast_comparison_t *result) {
  result->comparison = *lean_ctor_scalar_cptr(obj);
  lean_clingo_term_to_term(lean_ctor_get(obj, 0), &result->left);
  lean_clingo_term_to_term(lean_ctor_get(obj, 1), &result->right);
}

void lean_clingo_free_comparison(clingo_ast_comparison_t *result) {
  lean_clingo_free_term(&result->left);
  lean_clingo_free_term(&result->right);
}
/* ** CSPProductTerm */
void lean_clingo_csp_product_term_to_csp_product_term(lean_object *obj, clingo_ast_csp_product_term_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj,0));
  lean_clingo_term_to_term(lean_ctor_get(obj,1), &result->coefficient);
  CLINGO_CONV_OBJ(term, result, variable, lean_ctor_get(obj,2));
}

void lean_clingo_free_csp_product_term(clingo_ast_csp_product_term_t *result) {
  lean_clingo_free_term((clingo_ast_term_t *) &result->coefficient);
  CLINGO_FREE_OBJ(term, result, variable);
}
/*  ** CSPSumTerm */  
void lean_clingo_csp_sum_term_to_csp_sum_term(lean_object *obj, clingo_ast_csp_sum_term_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj,0));
  CLINGO_CONV_ARRAY(term, result, terms, lean_ctor_get(obj, 1));
}

void lean_clingo_free_csp_sum_term(clingo_ast_csp_sum_term_t *result) {
  CLINGO_FREE_ARRAY(term, result, terms);
}
/* ** CSPGuard */
void lean_clingo_csp_guard_to_csp_guard(lean_object *obj, clingo_ast_csp_guard_t *result) {
  result->comparison = *(lean_ctor_scalar_cptr(obj));
  lean_clingo_csp_sum_term_to_csp_sum_term(lean_ctor_get(obj, 0), &result->term);
}

void lean_clingo_free_csp_guard(clingo_ast_csp_guard_t *result) {
  lean_clingo_free_csp_sum_term(&result->term);
}
/* ** CSPLiteral */
void lean_clingo_csp_literal_to_csp_literal(lean_object *obj, clingo_ast_csp_literal_t *result) {
  lean_clingo_csp_sum_term_to_csp_sum_term(lean_ctor_get(obj, 0), &result->term);
  CLINGO_CONV_ARRAY(csp_guard, result, guards, lean_ctor_get(obj,1));
}

void lean_clingo_free_csp_literal(clingo_ast_csp_literal_t *result) {
  lean_clingo_free_csp_sum_term(&result->term);
  CLINGO_FREE_ARRAY(csp_guard, result, guards);
}
/* ** Literal */
void lean_clingo_literal_to_literal(lean_object *obj, clingo_ast_literal_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj, 0));
  result->sign = *(lean_ctor_scalar_cptr(obj));
  lean_object *data = lean_ctor_get(obj, 1);
  result->type = lean_ptr_tag(data);
  switch (result->type) {
  case clingo_ast_literal_type_boolean:
    result->boolean = *(lean_ctor_scalar_cptr(data));
    break;
  case clingo_ast_literal_type_symbolic:
    CLINGO_CONV_OBJ(term, result, symbol, lean_ctor_get(data,0));
    break;
  case clingo_ast_literal_type_comparison:
    CLINGO_CONV_OBJ(comparison, result, comparison, lean_ctor_get(data,0));
    break;
  case clingo_ast_literal_type_csp:
    CLINGO_CONV_OBJ(csp_literal, result, csp_literal, lean_ctor_get(data,0));
    break;
  }
}

void lean_clingo_free_literal(clingo_ast_literal_t *result) {
  switch (result->type) {
  case clingo_ast_literal_type_boolean:
    break;
  case clingo_ast_literal_type_symbolic:
    CLINGO_FREE_OBJ(term, result, symbol);
    break;
  case clingo_ast_literal_type_comparison:
    CLINGO_FREE_OBJ(comparison, result, comparison);
    break;
  case clingo_ast_literal_type_csp:
    CLINGO_FREE_OBJ(csp_literal, result, csp_literal);
    break;
  }
}
/* ** ConditionalLiteral */
void lean_clingo_conditional_literal_to_conditional_literal(lean_object *obj, clingo_ast_conditional_literal_t *result) {
  lean_clingo_literal_to_literal(lean_ctor_get(obj, 0), &result->literal);
  CLINGO_CONV_ARRAY(literal, result, condition, lean_ctor_get(obj,1));
}

void lean_clingo_free_conditional_literal(clingo_ast_conditional_literal_t *result) {
  lean_clingo_free_literal(&result->literal);
  CLINGO_FREE_ARRAY(literal, result, condition);
}
/* ** AggregateGuard */
void lean_clingo_aggregate_guard_to_aggregate_guard(lean_object *obj, clingo_ast_aggregate_guard_t *result) {
  result->comparison = *(lean_ctor_scalar_cptr(obj));
  lean_clingo_term_to_term(lean_ctor_get(obj,0), &result->term);
}

void lean_clingo_free_aggregate_guard(clingo_ast_aggregate_guard_t *result) {
  lean_clingo_free_term(&result->term);
}
/* ** Aggregate */
void lean_clingo_aggregate_to_aggregate(lean_object *obj, clingo_ast_aggregate_t *result) {
  CLINGO_CONV_ARRAY(conditional_literal, result, elements, lean_ctor_get(obj,0));
  CLINGO_CONV_OBJ(aggregate_guard, result, left_guard, lean_ctor_get(obj,1));
  CLINGO_CONV_OBJ(aggregate_guard, result, right_guard, lean_ctor_get(obj,2));
}

void lean_clingo_free_aggregate(clingo_ast_aggregate_t *result) {
  CLINGO_FREE_ARRAY(conditional_literal, result, elements);
  CLINGO_FREE_OBJ(aggregate_guard, result, left_guard);
  CLINGO_FREE_OBJ(aggregate_guard, result, right_guard);
}
/* ** Aggregate Head Element */
void lean_clingo_head_aggregate_element_to_head_aggregate_element(lean_object *obj, clingo_ast_head_aggregate_element_t *result) {
  CLINGO_CONV_ARRAY_SIZED(term, result, tuple, lean_ctor_get(obj,0), tuple_size);
  lean_clingo_conditional_literal_to_conditional_literal(lean_ctor_get(obj,1), &result->conditional_literal);
}

void lean_clingo_free_head_aggregate_element(clingo_ast_head_aggregate_element_t *result) {
  CLINGO_FREE_ARRAY_SIZED(term, result, tuple, tuple_size);
  lean_clingo_free_conditional_literal(&result->conditional_literal);
}
/* ** Aggregate Body Element */
void lean_clingo_body_aggregate_element_to_body_aggregate_element(lean_object *obj, clingo_ast_body_aggregate_element_t *result) {
  CLINGO_CONV_ARRAY_SIZED(term, result, tuple, lean_ctor_get(obj,0), tuple_size);
  CLINGO_CONV_ARRAY_SIZED(literal, result, condition, lean_ctor_get(obj,1), condition_size);
}

void lean_clingo_free_body_aggregate_element(clingo_ast_body_aggregate_element_t *result) {
  CLINGO_FREE_ARRAY_SIZED(term, result, tuple, tuple_size);
  CLINGO_FREE_ARRAY_SIZED(literal, result, condition, condition_size);
}
/* ** Aggregate Head */
void lean_clingo_head_aggregate_to_head_aggregate(lean_object *obj, clingo_ast_head_aggregate_t *result) {
  result->function = *(lean_ctor_scalar_cptr(obj));
  CLINGO_CONV_ARRAY(head_aggregate_element, result, elements, lean_ctor_get(obj, 0));
  CLINGO_CONV_OBJ(aggregate_guard, result, left_guard, lean_ctor_get(obj,1));
  CLINGO_CONV_OBJ(aggregate_guard, result, right_guard, lean_ctor_get(obj,2));
}

void lean_clingo_free_head_aggregate(clingo_ast_head_aggregate_t *result) {
  CLINGO_FREE_ARRAY(head_aggregate_element, result, elements);
  CLINGO_FREE_OBJ(aggregate_guard, result, left_guard);
  CLINGO_FREE_OBJ(aggregate_guard, result, right_guard);
}

/* ** Aggregate Body */
void lean_clingo_body_aggregate_to_body_aggregate(lean_object *obj, clingo_ast_body_aggregate_t *result) {
  result->function = *(lean_ctor_scalar_cptr(obj));
  CLINGO_CONV_ARRAY(body_aggregate_element, result, elements, lean_ctor_get(obj, 0));
  CLINGO_CONV_OBJ(aggregate_guard, result, left_guard, lean_ctor_get(obj,1));
  CLINGO_CONV_OBJ(aggregate_guard, result, right_guard, lean_ctor_get(obj,2));
}

void lean_clingo_free_body_aggregate(clingo_ast_body_aggregate_t *result) {
  CLINGO_FREE_ARRAY(body_aggregate_element, result, elements);
  CLINGO_FREE_OBJ(aggregate_guard, result, left_guard);
  CLINGO_FREE_OBJ(aggregate_guard, result, right_guard);
}

/* ** Theory Term */
void lean_clingo_theory_term_to_theory_term(lean_object *obj, clingo_ast_theory_term_t *result);
void lean_clingo_free_theory_term(clingo_ast_theory_term_t *result);

void lean_clingo_theory_term_array_to_theory_term_array(lean_object *obj, clingo_ast_theory_term_array_t *result);
void lean_clingo_free_theory_term_array(clingo_ast_theory_term_array_t *result);

void lean_clingo_theory_function_to_theory_function(lean_object *obj, clingo_ast_theory_function_t *result);
void lean_clingo_free_theory_function(clingo_ast_theory_function_t *result);

void lean_clingo_theory_unparsed_term_to_theory_unparsed_term(lean_object *obj, clingo_ast_theory_unparsed_term_t *result);
void lean_clingo_free_theory_unparsed_term(clingo_ast_theory_unparsed_term_t *result);
/* *** Theory Term Array */
void lean_clingo_theory_term_array_to_theory_term_array(lean_object *obj, clingo_ast_theory_term_array_t *result) {
  CLINGO_CONV_ARRAY(theory_term, result, terms, obj);
}

void lean_clingo_free_theory_term_array(clingo_ast_theory_term_array_t *result) {
  CLINGO_FREE_ARRAY(theory_term, result, terms);
}

/* *** Function */
void lean_clingo_theory_function_to_theory_function(lean_object *obj, clingo_ast_theory_function_t *result) {
  result->name = lean_string_cstr(lean_ctor_get(obj, 0));
  CLINGO_CONV_ARRAY(theory_term, result, arguments, lean_ctor_get(obj,1));
}
void lean_clingo_free_theory_function(clingo_ast_theory_function_t *result) {
    CLINGO_FREE_ARRAY(theory_term, result, arguments);
}

/* *** Unparsed Term */
void lean_clingo_theory_unparsed_term_element_to_theory_unparsed_term_element(lean_object *obj, clingo_ast_theory_unparsed_term_element_t *result) {
  CLINGO_CONV_ARRAY(string, result, operators, lean_ctor_get(obj, 0));
  lean_clingo_theory_term_to_theory_term(lean_ctor_get(obj,1), &result->term);
}

void lean_clingo_free_theory_unparsed_term_element(clingo_ast_theory_unparsed_term_element_t *result) {
  CLINGO_FREE_ARRAY(string, result, operators);
  lean_clingo_free_theory_term(&result->term);
}

void lean_clingo_theory_unparsed_term_to_theory_unparsed_term(lean_object *obj, clingo_ast_theory_unparsed_term_t *result) {
  CLINGO_CONV_ARRAY(theory_unparsed_term_element, result, elements, obj);
}

void lean_clingo_free_theory_unparsed_term(clingo_ast_theory_unparsed_term_t *result) {
    CLINGO_FREE_ARRAY(theory_unparsed_term_element, result, elements);
}


/* *** Term */
void lean_clingo_theory_term_to_theory_term(lean_object *obj, clingo_ast_theory_term_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj, 0));
  lean_object *data = lean_ctor_get(obj, 1);
  result->type = lean_ptr_tag(data);
  switch (result->type) {
  case clingo_ast_theory_term_type_symbol:
    result->symbol = *((uint64_t *)lean_ctor_scalar_cptr(data));
    break;
  case clingo_ast_theory_term_type_variable:
    result->variable = lean_string_cstr(lean_ctor_get(data, 0));
    break;
  case clingo_ast_theory_term_type_tuple:
    CLINGO_CONV_OBJ(theory_term_array, result, tuple, lean_ctor_get(data,0));
    break;
  case clingo_ast_theory_term_type_list:
    CLINGO_CONV_OBJ(theory_term_array, result, list, lean_ctor_get(data,0));
    break;
  case clingo_ast_theory_term_type_set:
    CLINGO_CONV_OBJ(theory_term_array, result, set, lean_ctor_get(data,0));
    break;
  case clingo_ast_theory_term_type_function:
    CLINGO_CONV_OBJ(theory_function, result, function, lean_ctor_get(data,0));
    break;
  case clingo_ast_theory_term_type_unparsed_term:
    CLINGO_CONV_OBJ(theory_unparsed_term, result, unparsed_term, lean_ctor_get(data,0));
    break;
  }
}

void lean_clingo_free_theory_term(clingo_ast_theory_term_t *result) {
  switch (result->type) {
  case clingo_ast_theory_term_type_symbol:
    break;
  case clingo_ast_theory_term_type_variable:
    break;
  case clingo_ast_theory_term_type_tuple:
    CLINGO_FREE_OBJ(theory_term_array, result, tuple);
    break;
  case clingo_ast_theory_term_type_list:
    CLINGO_FREE_OBJ(theory_term_array, result, list);
    break;
  case clingo_ast_theory_term_type_set:
    CLINGO_FREE_OBJ(theory_term_array, result, set);
    break;
  case clingo_ast_theory_term_type_function:
    CLINGO_FREE_OBJ(theory_function, result, function);
    break;
  case clingo_ast_theory_term_type_unparsed_term:
    CLINGO_FREE_OBJ(theory_unparsed_term, result, unparsed_term);
    break;
  }
}
/* ** Theory Atom Element */

void lean_clingo_theory_atom_element_to_theory_atom_element(lean_object *obj, clingo_ast_theory_atom_element_t *result) {
  CLINGO_CONV_ARRAY_SIZED(theory_term, result, tuple, lean_ctor_get(obj, 0), tuple_size);
  CLINGO_CONV_ARRAY_SIZED(literal, result, condition, lean_ctor_get(obj, 1), condition_size);
}

void lean_clingo_free_theory_atom_element(clingo_ast_theory_atom_element_t *result) {
  CLINGO_FREE_ARRAY_SIZED(theory_term, result, tuple, tuple_size);
  CLINGO_FREE_ARRAY_SIZED(literal, result, condition, condition_size);
}

/* ** Theory Guard */
void lean_clingo_theory_guard_to_theory_guard(lean_object *obj, clingo_ast_theory_guard_t *result) {
  result->operator_name = lean_string_cstr(lean_ctor_get(obj, 0));
  lean_clingo_theory_term_to_theory_term(lean_ctor_get(obj, 1), &result->term);
}

void lean_clingo_free_theory_guard(clingo_ast_theory_guard_t *result) {
  lean_clingo_free_theory_term(&result->term);
}

/* ** Theory Atom */
void lean_clingo_theory_atom_to_theory_atom(lean_object *obj, clingo_ast_theory_atom_t *result) {
  lean_clingo_term_to_term(lean_ctor_get(obj, 0), &result->term);
  CLINGO_CONV_ARRAY(theory_atom_element, result, elements, lean_ctor_get(obj, 1));
  CLINGO_CONV_OBJ(theory_guard, result, guard, lean_ctor_get(obj, 2));
}

void lean_clingo_free_theory_atom(clingo_ast_theory_atom_t *result) {
  lean_clingo_free_term(&result->term);
  CLINGO_FREE_ARRAY(theory_atom_element, result, elements);
  CLINGO_FREE_OBJ(theory_guard, result, guard);
}

/* ** Theory Operator Definition */
void lean_clingo_theory_operator_definition_to_theory_operator_definition(lean_object *obj, clingo_ast_theory_operator_definition_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj, 0));
  result->name = lean_string_cstr(lean_ctor_get(obj, 1));
  result->priority = *((uint64_t *)lean_ctor_scalar_cptr(obj));
  result->type = *((uint8_t *)(((uint64_t *)lean_ctor_scalar_cptr(obj)) + 1));
}

void lean_clingo_free_theory_operator_definition(clingo_ast_theory_operator_definition_t *result) {
}

/* ** Theory Term Definition */
void lean_clingo_theory_term_definition_to_theory_term_definition(lean_object *obj, clingo_ast_theory_term_definition_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj, 0));
  result->name = lean_string_cstr(lean_ctor_get(obj, 1));
  CLINGO_CONV_ARRAY(theory_operator_definition, result, operators, lean_ctor_get(obj, 2));
}

void lean_clingo_free_theory_term_definition(clingo_ast_theory_term_definition_t *result) {
  CLINGO_FREE_ARRAY(theory_operator_definition, result, operators);
}

/* ** Theory Guard Definition */
void lean_clingo_theory_guard_definition_to_theory_guard_definition(lean_object *obj, clingo_ast_theory_guard_definition_t *result) {
  result->term = lean_string_cstr(lean_ctor_get(obj, 0));
  CLINGO_CONV_ARRAY(string, result, operators, lean_ctor_get(obj, 1));
}

void lean_clingo_free_theory_guard_definition(clingo_ast_theory_guard_definition_t *result) {
  CLINGO_FREE_ARRAY(string, result, operators);
}

/* ** Theory Atom Definition */
void lean_clingo_theory_atom_definition_to_theory_atom_definition(lean_object *obj, clingo_ast_theory_atom_definition_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj, 0));
  result->type = *((uint8_t *)(((uint64_t *)lean_ctor_scalar_cptr(obj)) + 1));
  result->name = lean_string_cstr(lean_ctor_get(obj, 1));
  result->arity = *((uint64_t *)lean_ctor_scalar_cptr(obj));
  result->elements = lean_string_cstr(lean_ctor_get(obj, 2));
  CLINGO_CONV_OBJ(theory_guard_definition, result, guard, lean_ctor_get(obj, 3));
}

void lean_clingo_free_theory_atom_definition(clingo_ast_theory_atom_definition_t *result) {
  CLINGO_FREE_OBJ(theory_guard_definition, result, guard);
}

/* ** Disjoint Element */
void lean_clingo_disjoint_element_to_disjoint_element(lean_object *obj, clingo_ast_disjoint_element_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj, 0));
  CLINGO_CONV_ARRAY_SIZED(term, result, tuple, lean_ctor_get(obj,1), tuple_size);
  lean_clingo_csp_sum_term_to_csp_sum_term(lean_ctor_get(obj,2), &result->term);
  CLINGO_CONV_ARRAY_SIZED(literal, result, condition, lean_ctor_get(obj,3), condition_size);
}

void lean_clingo_free_disjoint_element(clingo_ast_disjoint_element_t *result) {
  CLINGO_FREE_ARRAY_SIZED(term, result, tuple, tuple_size);
  lean_clingo_free_csp_sum_term(&result->term);
  CLINGO_FREE_ARRAY_SIZED(literal, result, condition, condition_size);
}
/* ** Disjunction */
void lean_clingo_disjunction_to_disjunction(lean_object *obj, clingo_ast_disjunction_t *result) {
  CLINGO_CONV_ARRAY(conditional_literal, result, elements, obj);
}
void lean_clingo_free_disjunction(clingo_ast_disjunction_t *result) {
  CLINGO_FREE_ARRAY(conditional_literal, result, elements);
}

/* ** Head Literal */
void lean_clingo_head_literal_to_head_literal(lean_object *obj, clingo_ast_head_literal_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj, 0));
  lean_object *data = lean_ctor_get(obj, 1);
  result->type = lean_ptr_tag(data);
  switch (result->type) {
  case clingo_ast_head_literal_type_literal:
    CLINGO_CONV_OBJ(literal, result, literal, lean_ctor_get(data,0));
    break;
  case clingo_ast_head_literal_type_disjunction:
    CLINGO_CONV_OBJ(disjunction, result, disjunction, lean_ctor_get(data,0));
    break;
  case clingo_ast_head_literal_type_aggregate:
    CLINGO_CONV_OBJ(aggregate, result, aggregate, lean_ctor_get(data,0));
    break;
  case clingo_ast_head_literal_type_head_aggregate:
    CLINGO_CONV_OBJ(head_aggregate, result, head_aggregate, lean_ctor_get(data,0));
    break;
  case clingo_ast_head_literal_type_theory_atom:
    CLINGO_CONV_OBJ(theory_atom, result, theory_atom, lean_ctor_get(data,0));
    break;
  }
}

void lean_clingo_free_head_literal(clingo_ast_head_literal_t *result) {
  switch (result->type) {
  case clingo_ast_head_literal_type_literal:
    CLINGO_FREE_OBJ(literal, result, literal);
    break;
  case clingo_ast_head_literal_type_disjunction:
    CLINGO_FREE_OBJ(disjunction, result, disjunction);
    break;
  case clingo_ast_head_literal_type_aggregate:
    CLINGO_FREE_OBJ(aggregate, result, aggregate);
    break;
  case clingo_ast_head_literal_type_head_aggregate:
    CLINGO_FREE_OBJ(head_aggregate, result, head_aggregate);
    break;
  case clingo_ast_head_literal_type_theory_atom:
    CLINGO_FREE_OBJ(theory_atom, result, theory_atom);
    break;
  }
}

/* ** Disjoint */
void lean_clingo_disjoint_to_disjoint(lean_object *obj, clingo_ast_disjoint_t *result) {
  CLINGO_CONV_ARRAY(disjoint_element, result, elements, obj);
}

void lean_clingo_free_disjoint(clingo_ast_disjoint_t *result) {
  CLINGO_FREE_ARRAY(disjoint_element, result, elements);
}

/* ** Body Literal */
void lean_clingo_body_literal_to_body_literal(lean_object *obj, clingo_ast_body_literal_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj, 0));
  result->sign = *((uint8_t *)lean_ctor_scalar_cptr(obj));
  lean_object *data = lean_ctor_get(obj, 1);
  result->type = lean_ptr_tag(data);
  switch (result->type) {
  case clingo_ast_body_literal_type_literal:
    CLINGO_CONV_OBJ(literal, result, literal, lean_ctor_get(data,0));
    break;
  case clingo_ast_body_literal_type_conditional:
    CLINGO_CONV_OBJ(conditional_literal, result, conditional, lean_ctor_get(data,0));
    break;
  case clingo_ast_body_literal_type_aggregate:
    CLINGO_CONV_OBJ(aggregate, result, aggregate, lean_ctor_get(data,0));
    break;
  case clingo_ast_body_literal_type_body_aggregate:
    CLINGO_CONV_OBJ(body_aggregate, result, body_aggregate, lean_ctor_get(data,0));
    break;
  case clingo_ast_body_literal_type_theory_atom:
    CLINGO_CONV_OBJ(theory_atom, result, theory_atom, lean_ctor_get(data,0));
    break;
  case clingo_ast_body_literal_type_disjoint:
    CLINGO_CONV_OBJ(disjoint, result, disjoint, lean_ctor_get(data,0));
    break;
  }
}

void lean_clingo_free_body_literal(clingo_ast_body_literal_t *result) {
  switch (result->type) {
  case clingo_ast_body_literal_type_literal:
    CLINGO_FREE_OBJ(literal, result, literal);
    break;
  case clingo_ast_body_literal_type_conditional:
    CLINGO_FREE_OBJ(conditional_literal, result, conditional);
    break;
  case clingo_ast_body_literal_type_aggregate:
    CLINGO_FREE_OBJ(aggregate, result, aggregate);
    break;
  case clingo_ast_body_literal_type_body_aggregate:
    CLINGO_FREE_OBJ(body_aggregate, result, body_aggregate);
    break;
  case clingo_ast_body_literal_type_theory_atom:
    CLINGO_FREE_OBJ(theory_atom, result, theory_atom);
    break;
  case clingo_ast_body_literal_type_disjoint:
    CLINGO_FREE_OBJ(disjoint, result, disjoint);
    break;
  }
}

/* ** Definition */
void lean_clingo_definition_to_definition(lean_object *obj, clingo_ast_definition_t *result) {
  result->name = lean_string_cstr(lean_ctor_get(obj, 0));
  lean_clingo_term_to_term(lean_ctor_get(obj, 1), &result->value);
  result->is_default = *((uint8_t *)lean_ctor_scalar_cptr(obj));
}

void lean_clingo_free_definition(clingo_ast_definition_t *result) {
  lean_clingo_free_term(&result->value);
}

/* ** Id */
void lean_clingo_id_to_id(lean_object *obj, clingo_ast_id_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj, 0));
  result->id = lean_string_cstr(lean_ctor_get(obj,1));
}

void lean_clingo_free_id(clingo_ast_id_t *result) {
}

/* ** Statement */
/* *** Theory Definition */
void lean_clingo_theory_definition_to_theory_definition(lean_object *obj, clingo_ast_theory_definition_t *result) {
  result->name = lean_string_cstr(lean_ctor_get(obj, 0));
  CLINGO_CONV_ARRAY_SIZED(theory_term_definition, result, terms, lean_ctor_get(obj, 1), terms_size);
  CLINGO_CONV_ARRAY_SIZED(theory_atom_definition, result, atoms, lean_ctor_get(obj, 2), atoms_size);
}

void lean_clingo_free_theory_definition(clingo_ast_theory_definition_t *result) {
  CLINGO_FREE_ARRAY_SIZED(theory_term_definition, result, terms, terms_size);
  CLINGO_FREE_ARRAY_SIZED(theory_atom_definition, result, atoms, atoms_size);
}

/* *** Rule */
void lean_clingo_rule_to_rule(lean_object *obj, clingo_ast_rule_t *result) {
  lean_clingo_head_literal_to_head_literal(lean_ctor_get(obj, 0), &result->head);
  CLINGO_CONV_ARRAY(body_literal, result, body, lean_ctor_get(obj, 1));
}

void lean_clingo_free_rule(clingo_ast_rule_t *result) {
  lean_clingo_free_head_literal(&result->head);
  CLINGO_FREE_ARRAY(body_literal, result, body);
}


/* *** Show Signature */
void lean_clingo_show_signature_to_show_signature(lean_object *obj, clingo_ast_show_signature_t *result) {
  result->signature = *((uint64_t *)lean_ctor_scalar_cptr(obj));
  result->csp = *((uint8_t *)(((uint64_t *)lean_ctor_scalar_cptr(obj)) + 1));
}

void lean_clingo_free_show_signature(clingo_ast_show_signature_t *result) {
}

/* *** Show Term */
void lean_clingo_show_term_to_show_term(lean_object *obj, clingo_ast_show_term_t *result) {
  lean_clingo_term_to_term(lean_ctor_get(obj, 0), &result->term);
  CLINGO_CONV_ARRAY(body_literal, result, body, lean_ctor_get(obj,1));
  result->csp = *((uint8_t *)(lean_ctor_scalar_cptr(obj)));
}

void lean_clingo_free_show_term(clingo_ast_show_term_t *result) {
  lean_clingo_free_term(&result->term);
  CLINGO_FREE_ARRAY(body_literal, result, body);
}

/* *** Minimize */
void lean_clingo_minimize_to_minimize(lean_object *obj, clingo_ast_minimize_t *result) {
  lean_clingo_term_to_term(lean_ctor_get(obj, 0), &result->weight);
  lean_clingo_term_to_term(lean_ctor_get(obj, 1), &result->priority);
  CLINGO_CONV_ARRAY_SIZED(term, result, tuple, lean_ctor_get(obj, 2), tuple_size);
  CLINGO_CONV_ARRAY_SIZED(body_literal, result, body, lean_ctor_get(obj, 3), body_size);
}

void lean_clingo_free_minimize(clingo_ast_minimize_t *result) {
  lean_clingo_free_term(&result->weight);
  lean_clingo_free_term(&result->priority);
  CLINGO_FREE_ARRAY_SIZED(term, result, tuple, tuple_size);
  CLINGO_FREE_ARRAY_SIZED(body_literal, result, body, body_size);
}

/* *** Script */
void lean_clingo_script_to_script(lean_object *obj, clingo_ast_script_t *result) {
  result->type = *((uint8_t *)lean_ctor_scalar_cptr(obj));
  result->code = lean_string_cstr(lean_ctor_get(obj, 0));
}

void lean_clingo_free_script(clingo_ast_script_t *result) {
}

/* *** Program */
void lean_clingo_program_to_program(lean_object *obj, clingo_ast_program_t *result) {
  result->name = lean_string_cstr(lean_ctor_get(obj, 0));
  CLINGO_CONV_ARRAY(id, result, parameters, lean_ctor_get(obj, 1));
}

void lean_clingo_free_program(clingo_ast_program_t *result) {
  CLINGO_FREE_ARRAY(id, result, parameters);
}

/* *** External */
void lean_clingo_external_to_external(lean_object *obj, clingo_ast_external_t *result) {
  lean_clingo_term_to_term(lean_ctor_get(obj, 0), &result->atom);
  CLINGO_CONV_ARRAY(body_literal, result, body, lean_ctor_get(obj, 1));
  lean_clingo_term_to_term(lean_ctor_get(obj, 2), &result->type);
}

void lean_clingo_free_external(clingo_ast_external_t *result) {
  lean_clingo_free_term(&result->atom);
  CLINGO_FREE_ARRAY(body_literal, result, body);
  lean_clingo_free_term(&result->type);
}

/* *** Edge */
void lean_clingo_edge_to_edge(lean_object *obj, clingo_ast_edge_t *result) {
  lean_clingo_term_to_term(lean_ctor_get(obj, 0), &result->u);
  lean_clingo_term_to_term(lean_ctor_get(obj, 1), &result->v);
  CLINGO_CONV_ARRAY(body_literal, result, body, lean_ctor_get(obj, 2));
}

void lean_clingo_free_edge(clingo_ast_edge_t *result) {
  lean_clingo_free_term(&result->u);
  lean_clingo_free_term(&result->v);
  CLINGO_FREE_ARRAY(body_literal, result, body);
}

/* *** Heuristic */
void lean_clingo_heuristic_to_heuristic(lean_object *obj, clingo_ast_heuristic_t *result) {
  lean_clingo_term_to_term(lean_ctor_get(obj, 0), &result->atom);
  CLINGO_CONV_ARRAY(body_literal, result, body, lean_ctor_get(obj, 1));
  lean_clingo_term_to_term(lean_ctor_get(obj, 2), &result->bias);
  lean_clingo_term_to_term(lean_ctor_get(obj, 3), &result->priority);
  lean_clingo_term_to_term(lean_ctor_get(obj, 4), &result->modifier);
}

void lean_clingo_free_heuristic(clingo_ast_heuristic_t *result) {
  lean_clingo_free_term(&result->atom);
  CLINGO_FREE_ARRAY(body_literal, result, body);
  lean_clingo_free_term(&result->bias);
  lean_clingo_free_term(&result->priority);
  lean_clingo_free_term(&result->modifier);
}

/* *** Project */
void lean_clingo_project_to_project(lean_object *obj, clingo_ast_project_t *result) {
  lean_clingo_term_to_term(lean_ctor_get(obj, 0), &result->atom);
  CLINGO_CONV_ARRAY(body_literal, result, body, lean_ctor_get(obj, 1));
}

void lean_clingo_free_project(clingo_ast_project_t *result) {
  lean_clingo_free_term(&result->atom);
  CLINGO_FREE_ARRAY(body_literal, result, body);
}

/* *** Defined */
void lean_clingo_defined_to_defined(lean_object *obj, clingo_ast_defined_t *result) {
  assert(lean_ctor_num_objs(obj) == 0);
  result->signature = *((uint64_t *)lean_ctor_scalar_cptr(obj));
}

void lean_clingo_free_defined(clingo_ast_defined_t *result) {
}


/* *** Statement */
void lean_clingo_statement_to_statement(lean_object *obj, clingo_ast_statement_t *result) {
  result->location = clingo_lean_location_to_location(lean_ctor_get(obj, 0));
  lean_object *data = lean_ctor_get(obj, 1);
  result->type = lean_ptr_tag(data);
  switch (result->type) {
  case clingo_ast_statement_type_rule:
    CLINGO_CONV_OBJ(rule, result, rule, data);
    break;
  case clingo_ast_statement_type_const:
    CLINGO_CONV_OBJ(definition, result, definition, lean_ctor_get(data,0));
    break;
  case clingo_ast_statement_type_show_signature:
    CLINGO_CONV_OBJ(show_signature, result, show_signature, data);
    break;
  case clingo_ast_statement_type_show_term:
    CLINGO_CONV_OBJ(show_term, result, show_term, data);
    break;
  case clingo_ast_statement_type_minimize:
    CLINGO_CONV_OBJ(minimize, result, minimize, data);
    break;
  case clingo_ast_statement_type_script:
    CLINGO_CONV_OBJ(script, result, script, data);
    break;
  case clingo_ast_statement_type_program:
    CLINGO_CONV_OBJ(program, result, program, data);
    break;
  case clingo_ast_statement_type_external:
    CLINGO_CONV_OBJ(external, result, external, data);
    break;
  case clingo_ast_statement_type_edge:
    CLINGO_CONV_OBJ(edge, result, edge, data);
    break;
  case clingo_ast_statement_type_heuristic:
    CLINGO_CONV_OBJ(heuristic, result, heuristic, data);
    break;
  case clingo_ast_statement_type_project_atom:
    CLINGO_CONV_OBJ(project, result, project_atom, data);
    break;
  case clingo_ast_statement_type_project_atom_signature:
    result->project_signature = *((uint64_t *)lean_ctor_scalar_cptr(data));
    break;
  case clingo_ast_statement_type_theory_definition:
    CLINGO_CONV_OBJ(theory_definition, result, theory_definition, data);
    break;
  case clingo_ast_statement_type_defined:
    CLINGO_CONV_OBJ(defined, result, defined, data);
    break;
  }
}

void lean_clingo_free_statement(clingo_ast_statement_t *result) {
  switch (result->type) {
  case clingo_ast_statement_type_rule:
    CLINGO_FREE_OBJ(rule, result, rule);
    break;
  case clingo_ast_statement_type_const:
    CLINGO_FREE_OBJ(definition, result, definition);
    break;
  case clingo_ast_statement_type_show_signature:
    CLINGO_FREE_OBJ(show_signature, result, show_signature);
    break;
  case clingo_ast_statement_type_show_term:
    CLINGO_FREE_OBJ(show_term, result, show_term);
    break;
  case clingo_ast_statement_type_minimize:
    CLINGO_FREE_OBJ(minimize, result, minimize);
    break;
  case clingo_ast_statement_type_script:
    CLINGO_FREE_OBJ(script, result, script);
    break;
  case clingo_ast_statement_type_program:
    CLINGO_FREE_OBJ(program, result, program);
    break;
  case clingo_ast_statement_type_external:
    CLINGO_FREE_OBJ(external, result, external);
    break;
  case clingo_ast_statement_type_edge:
    CLINGO_FREE_OBJ(edge, result, edge);
    break;
  case clingo_ast_statement_type_heuristic:
    CLINGO_FREE_OBJ(heuristic, result, heuristic);
    break;
  case clingo_ast_statement_type_project_atom:
    CLINGO_FREE_OBJ(project, result, project_atom);
    break;
  case clingo_ast_statement_type_project_atom_signature:
    break;
  case clingo_ast_statement_type_theory_definition:
    CLINGO_FREE_OBJ(theory_definition, result, theory_definition);
    break;
  case clingo_ast_statement_type_defined:
    CLINGO_FREE_OBJ(defined, result, defined);
    break;
  }
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

static void clingo_grounding_callback_finaliser(void *_obj) {  }
REGISTER_LEAN_CLASS(clingo_grounding_callback, clingo_grounding_callback_finaliser, noop_foreach)

static void clingo_grounding_callback_data_finaliser(void *_obj) {  }
REGISTER_LEAN_CLASS(clingo_grounding_callback_data, clingo_grounding_callback_data_finaliser, noop_foreach)


lean_obj_res lean_clingo_symbol_callback_wrapper(lean_object *symbolCallbackObj, lean_object *symbolCallbackDataObj, lean_object *symbolsArrayObj, lean_object *_world) {
  clingo_symbol_callback_t symbolCallback = lean_get_external_data(symbolCallbackObj);
  void *symbolCallbackData = lean_get_external_data(symbolCallbackDataObj);

  size_t c_symbols_size = lean_array_size(symbolsArrayObj);
  clingo_symbol_t *c_symbols = malloc(sizeof(*c_symbols) * c_symbols_size);

  lean_object **symbolsArrayPtr = lean_array_cptr(symbolsArrayObj);
  for(size_t i = 0; i < c_symbols_size; i++) { c_symbols[i] = lean_unbox_uint64(symbolsArrayPtr[i]); }

  bool success = symbolCallback(c_symbols, c_symbols_size, symbolCallbackData);
  free(c_symbols);

  if(success) {
    return lean_io_result_mk_ok(lean_box(0));
  } else {
    return lean_io_result_mk_error(lean_clingo_mk_io_error());
  }
}

bool lean_clingo_ground_event_callback_wrapper(clingo_location_t const *location, char const *name, clingo_symbol_t const *arguments, size_t arguments_size, void *data,
                                               clingo_symbol_callback_t symbol_callback, void *symbol_callback_data) {
    lean_object *locationObj = lean_clingo_location_to_location(location);
    lean_object *nameObj = lean_mk_string(name);
    lean_object *argsObj = lean_alloc_array(arguments_size, arguments_size);

    lean_object **argsObjPtr = lean_array_cptr(argsObj);
    for(size_t i = 0; i < arguments_size; i++) { argsObjPtr[i] = lean_box_uint64(arguments[i]); }

    lean_object *userCallbackObj = data;

    lean_object *symbolCallbackFuncObj = lean_alloc_closure(&lean_clingo_symbol_callback_wrapper, 4, 2);
    lean_object *symbolCallbackObj = lean_alloc_external(get_clingo_grounding_callback_class(), (void *) symbol_callback);
    lean_object *symbolCallbackDataObj = lean_alloc_external(get_clingo_grounding_callback_data_class(), (void *) symbol_callback_data);
    
    lean_closure_set(symbolCallbackFuncObj, 0, symbolCallbackObj);
    lean_closure_set(symbolCallbackFuncObj, 1, symbolCallbackDataObj);

    lean_object *result =  lean_apply_5(userCallbackObj, locationObj, nameObj, argsObj, symbolCallbackFuncObj, lean_io_mk_world());
    if(lean_ptr_tag(result) == 1) {
        lean_io_result_show_error(result);
        lean_dec_ref(result);
        clingo_set_error(clingo_error_runtime, "internal Lean error");
        return false;
    } else {
        bool success = lean_unbox(lean_io_result_get_value(result));
        lean_dec_ref(result);
        if(!success) clingo_set_error(clingo_error_runtime, "user error");
        return success;
    }
}
/* * Program Builder
  ============================================================ */
static void clingo_program_builder_finaliser(void *obj) {  }
REGISTER_LEAN_CLASS(clingo_program_builder, clingo_program_builder_finaliser, noop_foreach)

/* Clingo.ProgramBuilder.begin_modify: @& ProgramBuilder -> IO Unit */
lean_obj_res lean_clingo_program_builder_begin(lean_object *obj) {
  clingo_program_builder_t *pb = lean_get_external_data(obj);
  bool success = clingo_program_builder_begin(pb);
  if(success) {
    return lean_io_result_mk_ok(lean_box(0));
  } else {
    return lean_io_result_mk_error(lean_clingo_mk_io_error());
  }
}

/* Clingo.ProgramBuilder.end_modify: @& ProgramBuilder -> IO Unit */
lean_obj_res lean_clingo_program_builder_end(lean_object *obj) {
  clingo_program_builder_t *pb = lean_get_external_data(obj);
  bool success = clingo_program_builder_end(pb);
  if(success) {
    return lean_io_result_mk_ok(lean_box(0));
  } else {
    return lean_io_result_mk_error(lean_clingo_mk_io_error());
  }
}

/* Clingo.ProgramBuilder.add_stmt: @& ProgramBuilder -> @& Ast.Statement -> IO Unit */
lean_obj_res lean_clingo_program_builder_add(lean_object *obj, lean_object *stmtObj) {
  clingo_program_builder_t *pb = lean_get_external_data(obj);
  clingo_ast_statement_t *stmt = malloc(sizeof(*stmt));
  lean_clingo_statement_to_statement(stmtObj, stmt);
  bool success = clingo_program_builder_add(pb, (const clingo_ast_statement_t  *)stmt);
  lean_clingo_free_statement(stmt); free((void *)stmt);
  if(success) {
    return lean_io_result_mk_ok(lean_box(0));
  } else {
    return lean_io_result_mk_error(lean_clingo_mk_io_error());
  }
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


/* Clingo.Control.ground:
    @& Control -> (parts: @& Array (@& Part)) -> (callback: @& GroundCallback) -> IO (Except Error Unit) */
lean_obj_res lean_clingo_control_ground(lean_object *controlObj, lean_object *partsObj, lean_object *groundCallbackObj) {
  clingo_control_t *control = lean_get_external_data(controlObj);

  lean_array_object *partsArrayObj = lean_to_array(partsObj);

  size_t c_parts_size = partsArrayObj->m_size;
  clingo_part_t *c_parts=malloc(sizeof(*c_parts) * c_parts_size);
  assert(c_parts != NULL);

  for(size_t i = 0; i < c_parts_size; i ++) {
    lean_object *obj = partsArrayObj->m_data[i];
    c_parts[i].name = lean_string_cstr(lean_ctor_get(obj, 0));

    lean_array_object *paramsArrayObj = lean_to_array(lean_ctor_get(obj, 1));
    size_t c_params_size = paramsArrayObj->m_size;
    c_parts[i].size = c_params_size;

    clingo_symbol_t *c_params = malloc(sizeof(*c_params) * c_params_size);
    assert(c_params != NULL);
    for(size_t i = 0; i < c_params_size; i ++) { c_params[i] = lean_unbox_uint64(paramsArrayObj->m_data[i]);}
    c_parts[i].params = c_params;
  }

  bool success =
    clingo_control_ground(control, c_parts, c_parts_size, &lean_clingo_ground_event_callback_wrapper, groundCallbackObj);
  for(size_t i = 0; i < c_parts_size; i ++) {
    free((void *)c_parts[i].params);
  }
  free((void *)c_parts);

  if(success) {
    return lean_io_result_mk_ok(lean_mk_except_ok(lean_box(0)));
  } else {
    return lean_io_result_mk_ok(lean_mk_clingo_error());
  }
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

/* Clingo.Control.program_builder: @& Control -> IO (Except Error ProgramBuilder) */
lean_obj_res lean_clingo_control_program_builder(lean_object *controlObj) {
  clingo_control_t *control = lean_get_external_data(controlObj);
  clingo_program_builder_t *builder;
  bool success = clingo_control_program_builder(control, &builder);

  if(success) {
    lean_object *result = lean_alloc_external(get_clingo_program_builder_class(), (void *)builder);
    return lean_io_result_mk_ok(result);
  } else {
    return lean_io_result_mk_error(lean_clingo_mk_io_error());
  }
}


