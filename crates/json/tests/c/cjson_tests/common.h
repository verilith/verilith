/*
  Copyright (c) 2009-2017 Dave Gamble and cJSON contributors

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
  THE SOFTWARE.
*/

/*
  Adapted for vjson: upstream's common.h #includes cJSON.c so that tests can
  call cJSON's internal parse_* functions. vjson has no such internals, so
  this shim defines the few internal types the tests touch and implements
  parse_value/parse_array/parse_object/parse_string/parse_number on top of
  the public cJSON_ParseWithOpts. Each shim function checks that the input
  starts with the token kind the internal function expects, parses one value
  without requiring the input to end, and moves the result into `item`.
*/
#ifndef CJSON_TESTS_COMMON_H
#define CJSON_TESTS_COMMON_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include "cJSON.h"
#include "unity/examples/unity_config.h"
#include "unity/src/unity.h"

typedef struct internal_hooks
{
    void *(CJSON_CDECL *allocate)(size_t size);
    void (CJSON_CDECL *deallocate)(void *pointer);
    void *(CJSON_CDECL *reallocate)(void *pointer, size_t size);
} internal_hooks;

static internal_hooks global_hooks = { malloc, free, realloc };

typedef struct
{
    const unsigned char *content;
    size_t length;
    size_t offset;
    size_t depth;
    internal_hooks hooks;
} parse_buffer;

static cJSON_bool shim_parse(cJSON * const item, parse_buffer * const buffer, const char *first_chars)
{
    const char *start = (const char*)buffer->content + buffer->offset;
    const char *end = NULL;
    cJSON *parsed = NULL;
    if (first_chars != NULL && (*start == '\0' || strchr(first_chars, *start) == NULL))
    {
        return false;
    }
    parsed = cJSON_ParseWithOpts(start, &end, false);
    if (parsed == NULL)
    {
        return false;
    }
    item->child = parsed->child;
    item->type = parsed->type;
    item->valuestring = parsed->valuestring;
    item->valueint = parsed->valueint;
    item->valuedouble = parsed->valuedouble;
    cJSON_free(parsed);
    buffer->offset = (size_t)(end - (const char*)buffer->content);
    return true;
}

static cJSON_bool parse_value(cJSON * const item, parse_buffer * const buffer)
{
    return shim_parse(item, buffer, "\"-0123456789[{tfn");
}
static cJSON_bool parse_array(cJSON * const item, parse_buffer * const buffer)
{
    return shim_parse(item, buffer, "[");
}
static cJSON_bool parse_object(cJSON * const item, parse_buffer * const buffer)
{
    return shim_parse(item, buffer, "{");
}
static cJSON_bool parse_string(cJSON * const item, parse_buffer * const buffer)
{
    return shim_parse(item, buffer, "\"");
}
static cJSON_bool parse_number(cJSON * const item, parse_buffer * const buffer)
{
    return shim_parse(item, buffer, "-0123456789");
}


/* The printing tests call cJSON's internal print_* functions on a
   printbuffer. This shim prints through the public API and copies the text
   into the buffer at its offset. */
typedef struct
{
    unsigned char *buffer;
    size_t length;
    size_t offset;
    size_t depth;
    cJSON_bool noalloc;
    cJSON_bool format;
    internal_hooks hooks;
} printbuffer;

static cJSON_bool shim_print(const cJSON * const item, printbuffer * const p)
{
    char *text = p->format ? cJSON_Print(item) : cJSON_PrintUnformatted(item);
    size_t n = 0;
    if (text == NULL)
    {
        return false;
    }
    n = strlen(text);
    if (p->buffer == NULL || p->offset + n + 1 > p->length)
    {
        cJSON_free(text);
        return false;
    }
    memcpy(p->buffer + p->offset, text, n + 1);
    p->offset += n;
    cJSON_free(text);
    return true;
}

static cJSON_bool print_value(const cJSON * const item, printbuffer * const p) { return shim_print(item, p); }
static cJSON_bool print_array(const cJSON * const item, printbuffer * const p) { return shim_print(item, p); }
static cJSON_bool print_object(const cJSON * const item, printbuffer * const p) { return shim_print(item, p); }
/* cJSON's print_number ignores the item's type (the tests leave it 0). */
static cJSON_bool print_number(const cJSON * const item, printbuffer * const p)
{
    cJSON n = *item;
    n.type = cJSON_Number;
    return shim_print(&n, p);
}
static cJSON_bool print_string_ptr(const unsigned char * const input, printbuffer * const p)
{
    cJSON *s = cJSON_CreateStringReference(input == NULL ? "" : (const char*)input);
    cJSON_bool ok = shim_print(s, p);
    cJSON_Delete(s);
    return ok;
}

/* cJSON's internal add_item_to_array is the public one without the hooks. */
#define add_item_to_array(array, item) cJSON_AddItemToArray(array, item)

/* A test helper (cJSON's internal double comparison). */
#include <math.h>
#include <float.h>
static cJSON_bool compare_double(double a, double b)
{
    double maxVal = fabs(a) > fabs(b) ? fabs(a) : fabs(b);
    return (fabs(a - b) <= maxVal * DBL_EPSILON);
}

/* A test helper only (cJSON's internal strdup with hooks). */
static unsigned char *cJSON_strdup(const unsigned char *string, const internal_hooks * const hooks)
{
    size_t n = strlen((const char*)string) + 1;
    unsigned char *copy = (unsigned char*)hooks->allocate(n);
    if (copy != NULL)
    {
        memcpy(copy, string, n);
    }
    return copy;
}

void reset(cJSON *item);
void reset(cJSON *item) {
    if ((item != NULL) && (item->child != NULL))
    {
        cJSON_Delete(item->child);
    }
    if ((item->valuestring != NULL) && !(item->type & cJSON_IsReference))
    {
        global_hooks.deallocate(item->valuestring);
    }
    if ((item->string != NULL) && !(item->type & cJSON_StringIsConst))
    {
        global_hooks.deallocate(item->string);
    }

    memset(item, 0, sizeof(cJSON));
}

char* read_file(const char *filename);
char* read_file(const char *filename) {
    FILE *file = NULL;
    long length = 0;
    char *content = NULL;
    size_t read_chars = 0;

    /* open in read binary mode */
    file = fopen(filename, "rb");
    if (file == NULL)
    {
        goto cleanup;
    }

    /* get the length */
    if (fseek(file, 0, SEEK_END) != 0)
    {
        goto cleanup;
    }
    length = ftell(file);
    if (length < 0)
    {
        goto cleanup;
    }
    if (fseek(file, 0, SEEK_SET) != 0)
    {
        goto cleanup;
    }

    /* allocate content buffer */
    content = (char*)malloc((size_t)length + sizeof(""));
    if (content == NULL)
    {
        goto cleanup;
    }

    /* read the file into memory */
    read_chars = fread(content, sizeof(char), (size_t)length, file);
    if ((long)read_chars != length)
    {
        free(content);
        content = NULL;
        goto cleanup;
    }
    content[read_chars] = '\0';


cleanup:
    if (file != NULL)
    {
        fclose(file);
    }

    return content;
}

/* assertion helper macros */
#define assert_has_type(item, item_type) TEST_ASSERT_BITS_MESSAGE(0xFF, item_type, item->type, "Item doesn't have expected type.")
#define assert_has_no_reference(item) TEST_ASSERT_BITS_MESSAGE(cJSON_IsReference, 0, item->type, "Item should not have a string as reference.")
#define assert_has_no_const_string(item) TEST_ASSERT_BITS_MESSAGE(cJSON_StringIsConst, 0, item->type, "Item should not have a const string.")
#define assert_has_valuestring(item) TEST_ASSERT_NOT_NULL_MESSAGE(item->valuestring, "Valuestring is NULL.")
#define assert_has_no_valuestring(item) TEST_ASSERT_NULL_MESSAGE(item->valuestring, "Valuestring is not NULL.")
#define assert_has_string(item) TEST_ASSERT_NOT_NULL_MESSAGE(item->string, "String is NULL")
#define assert_has_no_string(item) TEST_ASSERT_NULL_MESSAGE(item->string, "String is not NULL.")
#define assert_not_in_list(item) \
	TEST_ASSERT_NULL_MESSAGE(item->next, "Linked list next pointer is not NULL.");\
	TEST_ASSERT_NULL_MESSAGE(item->prev, "Linked list previous pointer is not NULL.")
#define assert_has_child(item) TEST_ASSERT_NOT_NULL_MESSAGE(item->child, "Item doesn't have a child.")
#define assert_has_no_child(item) TEST_ASSERT_NULL_MESSAGE(item->child, "Item has a child.")
#define assert_is_invalid(item) \
	assert_has_type(item, cJSON_Invalid);\
	assert_not_in_list(item);\
	assert_has_no_child(item);\
	assert_has_no_string(item);\
	assert_has_no_valuestring(item)

#endif
