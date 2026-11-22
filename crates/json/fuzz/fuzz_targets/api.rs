//! The cJSON API as a table of function pointers, filled in from vjson and
//! from upstream cJSON (linked with an `up_` prefix by build.rs), so a
//! fuzz target can run the same calls against both.
#![allow(dead_code)]
use std::os::raw::{c_char, c_int, c_void};
pub use verilith_json::ffi::cJSON;

unsafe extern "C" {
    fn up_cJSON_Parse(a0: *const c_char) -> *mut cJSON;
    fn up_cJSON_ParseWithLength(a0: *const c_char, a1: usize) -> *mut cJSON;
    fn up_cJSON_Print(a0: *const cJSON) -> *mut c_char;
    fn up_cJSON_PrintUnformatted(a0: *const cJSON) -> *mut c_char;
    fn up_cJSON_PrintBuffered(a0: *const cJSON, a1: c_int, a2: c_int) -> *mut c_char;
    fn up_cJSON_PrintPreallocated(a0: *mut cJSON, a1: *mut c_char, a2: c_int, a3: c_int) -> c_int;
    fn up_cJSON_Delete(a0: *mut cJSON);
    fn up_cJSON_free(a0: *mut c_void);
    fn up_cJSON_GetArraySize(a0: *const cJSON) -> c_int;
    fn up_cJSON_GetArrayItem(a0: *const cJSON, a1: c_int) -> *mut cJSON;
    fn up_cJSON_GetObjectItem(a0: *const cJSON, a1: *const c_char) -> *mut cJSON;
    fn up_cJSON_HasObjectItem(a0: *const cJSON, a1: *const c_char) -> c_int;
    fn up_cJSON_GetStringValue(a0: *const cJSON) -> *mut c_char;
    fn up_cJSON_GetNumberValue(a0: *const cJSON) -> f64;
    fn up_cJSON_IsBool(a0: *const cJSON) -> c_int;
    fn up_cJSON_Compare(a0: *const cJSON, a1: *const cJSON, a2: c_int) -> c_int;
    fn up_cJSON_CreateNull() -> *mut cJSON;
    fn up_cJSON_CreateTrue() -> *mut cJSON;
    fn up_cJSON_CreateFalse() -> *mut cJSON;
    fn up_cJSON_CreateBool(a0: c_int) -> *mut cJSON;
    fn up_cJSON_CreateNumber(a0: f64) -> *mut cJSON;
    fn up_cJSON_CreateString(a0: *const c_char) -> *mut cJSON;
    fn up_cJSON_CreateRaw(a0: *const c_char) -> *mut cJSON;
    fn up_cJSON_CreateArray() -> *mut cJSON;
    fn up_cJSON_CreateObject() -> *mut cJSON;
    fn up_cJSON_CreateIntArray(a0: *const c_int, a1: c_int) -> *mut cJSON;
    fn up_cJSON_CreateDoubleArray(a0: *const f64, a1: c_int) -> *mut cJSON;
    fn up_cJSON_CreateFloatArray(a0: *const f32, a1: c_int) -> *mut cJSON;
    fn up_cJSON_CreateStringArray(a0: *const *const c_char, a1: c_int) -> *mut cJSON;
    fn up_cJSON_AddItemToArray(a0: *mut cJSON, a1: *mut cJSON) -> c_int;
    fn up_cJSON_AddItemToObject(a0: *mut cJSON, a1: *const c_char, a2: *mut cJSON) -> c_int;
    fn up_cJSON_AddItemToObjectCS(a0: *mut cJSON, a1: *const c_char, a2: *mut cJSON) -> c_int;
    fn up_cJSON_DetachItemFromArray(a0: *mut cJSON, a1: c_int) -> *mut cJSON;
    fn up_cJSON_DeleteItemFromArray(a0: *mut cJSON, a1: c_int);
    fn up_cJSON_DetachItemFromObject(a0: *mut cJSON, a1: *const c_char) -> *mut cJSON;
    fn up_cJSON_DetachItemFromObjectCaseSensitive(a0: *mut cJSON, a1: *const c_char) -> *mut cJSON;
    fn up_cJSON_DeleteItemFromObject(a0: *mut cJSON, a1: *const c_char);
    fn up_cJSON_DeleteItemFromObjectCaseSensitive(a0: *mut cJSON, a1: *const c_char);
    fn up_cJSON_InsertItemInArray(a0: *mut cJSON, a1: c_int, a2: *mut cJSON) -> c_int;
    fn up_cJSON_ReplaceItemInArray(a0: *mut cJSON, a1: c_int, a2: *mut cJSON) -> c_int;
    fn up_cJSON_ReplaceItemInObject(a0: *mut cJSON, a1: *const c_char, a2: *mut cJSON) -> c_int;
    fn up_cJSON_ReplaceItemInObjectCaseSensitive(a0: *mut cJSON, a1: *const c_char, a2: *mut cJSON) -> c_int;
    fn up_cJSON_Duplicate(a0: *const cJSON, a1: c_int) -> *mut cJSON;
    fn up_cJSON_Minify(a0: *mut c_char);
    fn up_cJSON_SetNumberHelper(a0: *mut cJSON, a1: f64) -> f64;
    fn up_cJSON_SetValuestring(a0: *mut cJSON, a1: *const c_char) -> *mut c_char;
    fn up_cJSON_AddNullToObject(a0: *mut cJSON, a1: *const c_char) -> *mut cJSON;
    fn up_cJSON_AddBoolToObject(a0: *mut cJSON, a1: *const c_char, a2: c_int) -> *mut cJSON;
    fn up_cJSON_AddNumberToObject(a0: *mut cJSON, a1: *const c_char, a2: f64) -> *mut cJSON;
    fn up_cJSON_AddStringToObject(a0: *mut cJSON, a1: *const c_char, a2: *const c_char) -> *mut cJSON;
    fn up_cJSON_AddArrayToObject(a0: *mut cJSON, a1: *const c_char) -> *mut cJSON;
    fn up_cJSON_AddObjectToObject(a0: *mut cJSON, a1: *const c_char) -> *mut cJSON;
}

pub struct Lib {
    pub parse: unsafe extern "C" fn(*const c_char) -> *mut cJSON,
    pub parse_with_length: unsafe extern "C" fn(*const c_char, usize) -> *mut cJSON,
    pub print: unsafe extern "C" fn(*const cJSON) -> *mut c_char,
    pub print_unformatted: unsafe extern "C" fn(*const cJSON) -> *mut c_char,
    pub print_buffered: unsafe extern "C" fn(*const cJSON, c_int, c_int) -> *mut c_char,
    pub print_preallocated: unsafe extern "C" fn(*mut cJSON, *mut c_char, c_int, c_int) -> c_int,
    pub delete: unsafe extern "C" fn(*mut cJSON),
    pub free: unsafe extern "C" fn(*mut c_void),
    pub get_array_size: unsafe extern "C" fn(*const cJSON) -> c_int,
    pub get_array_item: unsafe extern "C" fn(*const cJSON, c_int) -> *mut cJSON,
    pub get_object_item: unsafe extern "C" fn(*const cJSON, *const c_char) -> *mut cJSON,
    pub has_object_item: unsafe extern "C" fn(*const cJSON, *const c_char) -> c_int,
    pub get_string_value: unsafe extern "C" fn(*const cJSON) -> *mut c_char,
    pub get_number_value: unsafe extern "C" fn(*const cJSON) -> f64,
    pub is_bool: unsafe extern "C" fn(*const cJSON) -> c_int,
    pub compare: unsafe extern "C" fn(*const cJSON, *const cJSON, c_int) -> c_int,
    pub create_null: unsafe extern "C" fn() -> *mut cJSON,
    pub create_true: unsafe extern "C" fn() -> *mut cJSON,
    pub create_false: unsafe extern "C" fn() -> *mut cJSON,
    pub create_bool: unsafe extern "C" fn(c_int) -> *mut cJSON,
    pub create_number: unsafe extern "C" fn(f64) -> *mut cJSON,
    pub create_string: unsafe extern "C" fn(*const c_char) -> *mut cJSON,
    pub create_raw: unsafe extern "C" fn(*const c_char) -> *mut cJSON,
    pub create_array: unsafe extern "C" fn() -> *mut cJSON,
    pub create_object: unsafe extern "C" fn() -> *mut cJSON,
    pub create_int_array: unsafe extern "C" fn(*const c_int, c_int) -> *mut cJSON,
    pub create_double_array: unsafe extern "C" fn(*const f64, c_int) -> *mut cJSON,
    pub create_float_array: unsafe extern "C" fn(*const f32, c_int) -> *mut cJSON,
    pub create_string_array: unsafe extern "C" fn(*const *const c_char, c_int) -> *mut cJSON,
    pub add_item_to_array: unsafe extern "C" fn(*mut cJSON, *mut cJSON) -> c_int,
    pub add_item_to_object: unsafe extern "C" fn(*mut cJSON, *const c_char, *mut cJSON) -> c_int,
    pub add_item_to_object_c_s: unsafe extern "C" fn(*mut cJSON, *const c_char, *mut cJSON) -> c_int,
    pub detach_item_from_array: unsafe extern "C" fn(*mut cJSON, c_int) -> *mut cJSON,
    pub delete_item_from_array: unsafe extern "C" fn(*mut cJSON, c_int),
    pub detach_item_from_object: unsafe extern "C" fn(*mut cJSON, *const c_char) -> *mut cJSON,
    pub detach_item_from_object_case_sensitive: unsafe extern "C" fn(*mut cJSON, *const c_char) -> *mut cJSON,
    pub delete_item_from_object: unsafe extern "C" fn(*mut cJSON, *const c_char),
    pub delete_item_from_object_case_sensitive: unsafe extern "C" fn(*mut cJSON, *const c_char),
    pub insert_item_in_array: unsafe extern "C" fn(*mut cJSON, c_int, *mut cJSON) -> c_int,
    pub replace_item_in_array: unsafe extern "C" fn(*mut cJSON, c_int, *mut cJSON) -> c_int,
    pub replace_item_in_object: unsafe extern "C" fn(*mut cJSON, *const c_char, *mut cJSON) -> c_int,
    pub replace_item_in_object_case_sensitive: unsafe extern "C" fn(*mut cJSON, *const c_char, *mut cJSON) -> c_int,
    pub duplicate: unsafe extern "C" fn(*const cJSON, c_int) -> *mut cJSON,
    pub minify: unsafe extern "C" fn(*mut c_char),
    pub set_number_helper: unsafe extern "C" fn(*mut cJSON, f64) -> f64,
    pub set_valuestring: unsafe extern "C" fn(*mut cJSON, *const c_char) -> *mut c_char,
    pub add_null_to_object: unsafe extern "C" fn(*mut cJSON, *const c_char) -> *mut cJSON,
    pub add_bool_to_object: unsafe extern "C" fn(*mut cJSON, *const c_char, c_int) -> *mut cJSON,
    pub add_number_to_object: unsafe extern "C" fn(*mut cJSON, *const c_char, f64) -> *mut cJSON,
    pub add_string_to_object: unsafe extern "C" fn(*mut cJSON, *const c_char, *const c_char) -> *mut cJSON,
    pub add_array_to_object: unsafe extern "C" fn(*mut cJSON, *const c_char) -> *mut cJSON,
    pub add_object_to_object: unsafe extern "C" fn(*mut cJSON, *const c_char) -> *mut cJSON,
}

pub static VJSON: Lib = Lib {
    parse: verilith_json::ffi::cJSON_Parse,
    parse_with_length: verilith_json::ffi::cJSON_ParseWithLength,
    print: verilith_json::ffi::cJSON_Print,
    print_unformatted: verilith_json::ffi::cJSON_PrintUnformatted,
    print_buffered: verilith_json::ffi::cJSON_PrintBuffered,
    print_preallocated: verilith_json::ffi::cJSON_PrintPreallocated,
    delete: verilith_json::ffi::cJSON_Delete,
    free: verilith_json::ffi::cJSON_free,
    get_array_size: verilith_json::ffi::cJSON_GetArraySize,
    get_array_item: verilith_json::ffi::cJSON_GetArrayItem,
    get_object_item: verilith_json::ffi::cJSON_GetObjectItem,
    has_object_item: verilith_json::ffi::cJSON_HasObjectItem,
    get_string_value: verilith_json::ffi::cJSON_GetStringValue,
    get_number_value: verilith_json::ffi::cJSON_GetNumberValue,
    is_bool: verilith_json::ffi::cJSON_IsBool,
    compare: verilith_json::ffi::cJSON_Compare,
    create_null: verilith_json::ffi::cJSON_CreateNull,
    create_true: verilith_json::ffi::cJSON_CreateTrue,
    create_false: verilith_json::ffi::cJSON_CreateFalse,
    create_bool: verilith_json::ffi::cJSON_CreateBool,
    create_number: verilith_json::ffi::cJSON_CreateNumber,
    create_string: verilith_json::ffi::cJSON_CreateString,
    create_raw: verilith_json::ffi::cJSON_CreateRaw,
    create_array: verilith_json::ffi::cJSON_CreateArray,
    create_object: verilith_json::ffi::cJSON_CreateObject,
    create_int_array: verilith_json::ffi::cJSON_CreateIntArray,
    create_double_array: verilith_json::ffi::cJSON_CreateDoubleArray,
    create_float_array: verilith_json::ffi::cJSON_CreateFloatArray,
    create_string_array: verilith_json::ffi::cJSON_CreateStringArray,
    add_item_to_array: verilith_json::ffi::cJSON_AddItemToArray,
    add_item_to_object: verilith_json::ffi::cJSON_AddItemToObject,
    add_item_to_object_c_s: verilith_json::ffi::cJSON_AddItemToObjectCS,
    detach_item_from_array: verilith_json::ffi::cJSON_DetachItemFromArray,
    delete_item_from_array: verilith_json::ffi::cJSON_DeleteItemFromArray,
    detach_item_from_object: verilith_json::ffi::cJSON_DetachItemFromObject,
    detach_item_from_object_case_sensitive: verilith_json::ffi::cJSON_DetachItemFromObjectCaseSensitive,
    delete_item_from_object: verilith_json::ffi::cJSON_DeleteItemFromObject,
    delete_item_from_object_case_sensitive: verilith_json::ffi::cJSON_DeleteItemFromObjectCaseSensitive,
    insert_item_in_array: verilith_json::ffi::cJSON_InsertItemInArray,
    replace_item_in_array: verilith_json::ffi::cJSON_ReplaceItemInArray,
    replace_item_in_object: verilith_json::ffi::cJSON_ReplaceItemInObject,
    replace_item_in_object_case_sensitive: verilith_json::ffi::cJSON_ReplaceItemInObjectCaseSensitive,
    duplicate: verilith_json::ffi::cJSON_Duplicate,
    minify: verilith_json::ffi::cJSON_Minify,
    set_number_helper: verilith_json::ffi::cJSON_SetNumberHelper,
    set_valuestring: verilith_json::ffi::cJSON_SetValuestring,
    add_null_to_object: verilith_json::ffi::cJSON_AddNullToObject,
    add_bool_to_object: verilith_json::ffi::cJSON_AddBoolToObject,
    add_number_to_object: verilith_json::ffi::cJSON_AddNumberToObject,
    add_string_to_object: verilith_json::ffi::cJSON_AddStringToObject,
    add_array_to_object: verilith_json::ffi::cJSON_AddArrayToObject,
    add_object_to_object: verilith_json::ffi::cJSON_AddObjectToObject,
};

pub static UPSTREAM: Lib = Lib {
    parse: up_cJSON_Parse,
    parse_with_length: up_cJSON_ParseWithLength,
    print: up_cJSON_Print,
    print_unformatted: up_cJSON_PrintUnformatted,
    print_buffered: up_cJSON_PrintBuffered,
    print_preallocated: up_cJSON_PrintPreallocated,
    delete: up_cJSON_Delete,
    free: up_cJSON_free,
    get_array_size: up_cJSON_GetArraySize,
    get_array_item: up_cJSON_GetArrayItem,
    get_object_item: up_cJSON_GetObjectItem,
    has_object_item: up_cJSON_HasObjectItem,
    get_string_value: up_cJSON_GetStringValue,
    get_number_value: up_cJSON_GetNumberValue,
    is_bool: up_cJSON_IsBool,
    compare: up_cJSON_Compare,
    create_null: up_cJSON_CreateNull,
    create_true: up_cJSON_CreateTrue,
    create_false: up_cJSON_CreateFalse,
    create_bool: up_cJSON_CreateBool,
    create_number: up_cJSON_CreateNumber,
    create_string: up_cJSON_CreateString,
    create_raw: up_cJSON_CreateRaw,
    create_array: up_cJSON_CreateArray,
    create_object: up_cJSON_CreateObject,
    create_int_array: up_cJSON_CreateIntArray,
    create_double_array: up_cJSON_CreateDoubleArray,
    create_float_array: up_cJSON_CreateFloatArray,
    create_string_array: up_cJSON_CreateStringArray,
    add_item_to_array: up_cJSON_AddItemToArray,
    add_item_to_object: up_cJSON_AddItemToObject,
    add_item_to_object_c_s: up_cJSON_AddItemToObjectCS,
    detach_item_from_array: up_cJSON_DetachItemFromArray,
    delete_item_from_array: up_cJSON_DeleteItemFromArray,
    detach_item_from_object: up_cJSON_DetachItemFromObject,
    detach_item_from_object_case_sensitive: up_cJSON_DetachItemFromObjectCaseSensitive,
    delete_item_from_object: up_cJSON_DeleteItemFromObject,
    delete_item_from_object_case_sensitive: up_cJSON_DeleteItemFromObjectCaseSensitive,
    insert_item_in_array: up_cJSON_InsertItemInArray,
    replace_item_in_array: up_cJSON_ReplaceItemInArray,
    replace_item_in_object: up_cJSON_ReplaceItemInObject,
    replace_item_in_object_case_sensitive: up_cJSON_ReplaceItemInObjectCaseSensitive,
    duplicate: up_cJSON_Duplicate,
    minify: up_cJSON_Minify,
    set_number_helper: up_cJSON_SetNumberHelper,
    set_valuestring: up_cJSON_SetValuestring,
    add_null_to_object: up_cJSON_AddNullToObject,
    add_bool_to_object: up_cJSON_AddBoolToObject,
    add_number_to_object: up_cJSON_AddNumberToObject,
    add_string_to_object: up_cJSON_AddStringToObject,
    add_array_to_object: up_cJSON_AddArrayToObject,
    add_object_to_object: up_cJSON_AddObjectToObject,
};
