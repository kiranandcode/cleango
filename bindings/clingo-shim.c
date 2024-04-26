#include "lean/lean.h"
#include <stdio.h>
#include "clingo.h"

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

lean_obj_res lean_test(lean_object *obj) {
  printf("tag of excpt is %u\n", obj->m_tag);
  printf("contents of excpt is %u\n", (uint32_t)lean_unbox(lean_ctor_get(obj, 0)));
  return lean_io_result_mk_ok(lean_box(0));
}

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
    for(int i = 0; i < arguments_size; i++) {
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
