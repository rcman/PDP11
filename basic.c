/*
 *   ____   _____ _____  ____            _      
 *  |  _ \ / ____|  __ \|  _ \          (_)     
 *  | |_) | (___ | |  | | |_) | __ _ ___ _  ___ 
 *  |  _ < \___ \| |  | |  _ < / _` / __| |/ __|
 *  | |_) |____) | |__| | |_) | (_| \__ \ | (__ 
 *  |____/|_____/|_____/|____/ \__,_|___/_|\___|
 * 
 * Optimized BASIC Interpreter for PDP-11
 * Copyright (C) 2024  Davepl with various AI assists
 * 
 * Optimizations:
 * - Binary search for line lookups (O(log n) instead of O(n))
 * - Line lookup caching for repeated jumps
 * - Reduced memory footprint for 64KB systems
 * - Better error reporting with line numbers
 * - Memory cleanup on exit
 * - Stack usage reduction via static buffers
 * - Struct packing optimization
 * - Bounds checking on all inputs
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#if defined(__unix__) || defined(__APPLE__) || defined(__MACH__)
#include <unistd.h>
#endif

/* Reduced limits optimized for PDP-11 */
#define MAX_LINES 512
#define MAX_LINE_LEN 128
#define MAX_VARS 64
#define MAX_GOSUB 32
#define MAX_FOR 16
#define MAX_STR_LEN 128
#define DEFAULT_ARRAY_SIZE 11
#define PRINT_WIDTH 80

/* Static buffer to reduce stack usage */
static char temp_buffer[MAX_LINE_LEN];

enum value_type { VAL_NUM = 0, VAL_STR = 1 };

struct value {
    int type;
    double num;
    char str[MAX_STR_LEN];
};

struct line {
    int number;
    char *text;
};

/* Optimized struct packing - large members first */
struct var {
    struct value scalar;
    struct value *array;
    int size;
    char name1;
    char name2;
    char is_string;
    char is_array;
};

struct gosub_frame {
    char *position;
    int line_index;
};

struct for_frame {
    struct value *var;
    double end_value;
    double step;
    char *resume_pos;
    int line_index;
    char name1;
    char name2;
    char is_string;
};

static struct line *program_lines[MAX_LINES];
static int line_count = 0;

static struct var vars[MAX_VARS];
static int var_count = 0;

static struct gosub_frame gosub_stack[MAX_GOSUB];
static int gosub_top = 0;

static struct for_frame for_stack[MAX_FOR];
static int for_top = 0;

static int current_line = 0;
static char *statement_pos = NULL;
static int halted = 0;
static int print_col = 0;

/* Line lookup cache */
static int last_lookup_num = -1;
static int last_lookup_idx = -1;

/* Forward declarations */
static void runtime_error(const char *msg);
static void load_program(const char *path);
static int find_line_index(int number);
static int starts_with_kw(char *p, const char *kw);
static void skip_spaces(char **p);
static int parse_number_literal(char **p, double *out);
static int read_identifier(char **p, char *buf, int buf_size);
static char *dupstr_local(const char *s);
static struct value eval_expr(char **p);
static int eval_condition(char **p);
static void execute_statement(char **p);
static struct value *get_var_reference(char **p, int *is_array_out, int *is_string_out);
static struct value make_num(double v);
static struct value make_str(const char *s);
static struct var *find_or_create_var(char name1, char name2, int is_string, int want_array, int array_size);
static struct value eval_function(const char *name, char **p);
static void print_value(struct value *v);
static void print_spaces(int count);
static void cleanup_program(void);
static void statement_rem(char **p);
static void statement_print(char **p);
static void statement_input(char **p);
static void statement_let(char **p);
static void statement_goto(char **p);
static void statement_gosub(char **p);
static void statement_return(char **p);
static void statement_if(char **p);
static void statement_for(char **p);
static void statement_next(char **p);
static void statement_dim(char **p);
static void statement_end(char **p);

/* Error reporting with line number context */
static void runtime_error(const char *msg)
{
    if (current_line >= 0 && current_line < line_count && program_lines[current_line]) {
        fprintf(stderr, "Error at line %d: %s\n", program_lines[current_line]->number, msg);
    } else {
        fprintf(stderr, "Error: %s\n", msg);
    }
    halted = 1;
}

/* Cleanup all allocated memory */
static void cleanup_program(void)
{
    register int i;
    
    for (i = 0; i < line_count; i++) {
        if (program_lines[i]) {
            if (program_lines[i]->text) {
                free(program_lines[i]->text);
            }
            free(program_lines[i]);
            program_lines[i] = NULL;
        }
    }
    
    for (i = 0; i < var_count; i++) {
        if (vars[i].is_array && vars[i].array) {
            free(vars[i].array);
            vars[i].array = NULL;
        }
    }
    
    line_count = 0;
    var_count = 0;
}

static void trim_newline(char *s)
{
    register char *p = strchr(s, '\n');
    if (p) *p = '\0';
}

static void skip_spaces(char **p)
{
    register char *q = *p;
    while (*q == ' ' || *q == '\t') q++;
    *p = q;
}

static int parse_number_literal(char **p, double *out)
{
    register char *s = *p;
    register char *q = s;
    int len;
    
    if (*q == '+' || *q == '-') q++;
    if (!isdigit((unsigned char)*q)) return 0;
    
    while (isdigit((unsigned char)*q)) q++;
    
    if (*q == '.') {
        q++;
        while (isdigit((unsigned char)*q)) q++;
    }
    
    if (*q == 'e' || *q == 'E') {
        register char *e = q + 1;
        if (*e == '+' || *e == '-') e++;
        if (isdigit((unsigned char)*e)) {
            q = e;
            while (isdigit((unsigned char)*q)) q++;
        }
    }
    
    if (q == s || (s + 1 == q && (s[0] == '+' || s[0] == '-'))) {
        return 0;
    }
    
    len = q - s;
    if (len >= MAX_LINE_LEN) len = MAX_LINE_LEN - 1;
    
    strncpy(temp_buffer, s, len);
    temp_buffer[len] = '\0';
    *out = atof(temp_buffer);
    *p = q;
    return 1;
}

static char *dupstr_local(const char *s)
{
    size_t len = strlen(s);
    char *p;
    
    if (len >= MAX_LINE_LEN) {
        runtime_error("Line too long");
        return NULL;
    }
    
    p = (char *)malloc(len + 1);
    if (!p) {
        runtime_error("Out of memory");
        return NULL;
    }
    memcpy(p, s, len + 1);
    return p;
}

static int starts_with_kw(char *p, const char *kw)
{
    register int i;
    register char c;
    
    for (i = 0; kw[i]; i++) {
        c = toupper((unsigned char)p[i]);
        if (c != kw[i]) return 0;
    }
    
    c = p[i];
    return (c == '\0' || c == ' ' || c == '\t' || c == ':' || c == '(');
}

static struct value make_num(double v)
{
    struct value out;
    out.type = VAL_NUM;
    out.num = v;
    out.str[0] = '\0';
    return out;
}

static struct value make_str(const char *s)
{
    struct value out;
    out.type = VAL_STR;
    out.num = 0.0;
    strncpy(out.str, s, MAX_STR_LEN - 1);
    out.str[MAX_STR_LEN - 1] = '\0';
    return out;
}

static void ensure_num(struct value *v)
{
    if (v->type != VAL_NUM) {
        runtime_error("Numeric value required");
    }
}

static void ensure_str(struct value *v)
{
    if (v->type != VAL_STR) {
        runtime_error("String value required");
    }
}

static void print_spaces(int count)
{
    register int i;
    for (i = 0; i < count; i++) {
        fputc(' ', stdout);
        print_col++;
        if (print_col >= PRINT_WIDTH) {
            fputc('\n', stdout);
            print_col = 0;
        }
    }
}

static void print_value(struct value *v)
{
    if (v->type == VAL_STR) {
        register char *s = v->str;
        while (*s) {
            fputc(*s, stdout);
            if (*s == '\n') {
                print_col = 0;
            } else {
                print_col++;
                if (print_col >= PRINT_WIDTH) {
                    fputc('\n', stdout);
                    print_col = 0;
                }
            }
            s++;
        }
    } else {
        sprintf(temp_buffer, "%g", v->num);
        fputs(temp_buffer, stdout);
        print_col += strlen(temp_buffer);
    }
}

static int name_equals(const char *a, const char *b)
{
    while (*a && *b) {
        if (toupper((unsigned char)*a) != *b) return 0;
        a++;
        b++;
    }
    return *a == '\0' && *b == '\0';
}

static struct value eval_function(const char *name, char **p)
{
    char tmp[8];
    struct value arg;

    read_identifier(p, tmp, sizeof(tmp));
    skip_spaces(p);
    
    if (**p != '(') {
        runtime_error("Function requires '('");
        return make_num(0.0);
    }
    (*p)++;
    
    arg = eval_expr(p);
    skip_spaces(p);
    
    if (**p == ')') {
        (*p)++;
    } else {
        runtime_error("Missing ')'");
    }

    if (name_equals(name, "ABS")) {
        ensure_num(&arg);
        return make_num(fabs(arg.num));
    }
    if (name_equals(name, "INT")) {
        ensure_num(&arg);
        return make_num(floor(arg.num));
    }
    if (name_equals(name, "SQR")) {
        ensure_num(&arg);
        return make_num(sqrt(arg.num));
    }
    if (name_equals(name, "SGN")) {
        ensure_num(&arg);
        return make_num(arg.num > 0 ? 1.0 : (arg.num < 0 ? -1.0 : 0.0));
    }
    if (name_equals(name, "SIN")) {
        ensure_num(&arg);
        return make_num(sin(arg.num));
    }
    if (name_equals(name, "COS")) {
        ensure_num(&arg);
        return make_num(cos(arg.num));
    }
    if (name_equals(name, "TAN")) {
        ensure_num(&arg);
        return make_num(tan(arg.num));
    }
    if (name_equals(name, "EXP")) {
        ensure_num(&arg);
        return make_num(exp(arg.num));
    }
    if (name_equals(name, "LOG")) {
        ensure_num(&arg);
        return make_num(log(arg.num));
    }
    if (name_equals(name, "RND")) {
        ensure_num(&arg);
        if (arg.num < 0) srand((unsigned int)(-arg.num));
        return make_num((double)rand() / (double)RAND_MAX);
    }
    if (name_equals(name, "LEN")) {
        ensure_str(&arg);
        return make_num((double)strlen(arg.str));
    }
    if (name_equals(name, "VAL")) {
        ensure_str(&arg);
        return make_num(atof(arg.str));
    }
    if (name_equals(name, "STR") || name_equals(name, "STR$")) {
        ensure_num(&arg);
        sprintf(temp_buffer, "%g", arg.num);
        return make_str(temp_buffer);
    }
    if (name_equals(name, "CHR") || name_equals(name, "CHR$")) {
        ensure_num(&arg);
        temp_buffer[0] = (char)((int)arg.num & 0xff);
        temp_buffer[1] = '\0';
        return make_str(temp_buffer);
    }
    if (name_equals(name, "ASC")) {
        ensure_str(&arg);
        return make_num(arg.str[0] ? (unsigned char)arg.str[0] : 0.0);
    }
    if (name_equals(name, "TAB")) {
        register int target, cur;
        ensure_num(&arg);
        target = (int)arg.num % PRINT_WIDTH;
        if (target < 0) target += PRINT_WIDTH;
        cur = print_col;
        if (target < cur) {
            fputc('\n', stdout);
            cur = 0;
        }
        while (cur < target) {
            fputc(' ', stdout);
            cur++;
        }
        print_col = cur;
        return make_str("");
    }

    runtime_error("Unknown function");
    return make_num(0.0);
}

static void uppercase_name(const char *src, char *n1, char *n2, int *is_string)
{
    register int len = strlen(src);
    
    *is_string = 0;
    if (len > 0 && src[len - 1] == '$') {
        *is_string = 1;
        len--;
    }
    
    *n1 = (len > 0) ? toupper((unsigned char)src[0]) : ' ';
    *n2 = (len > 1) ? toupper((unsigned char)src[1]) : ' ';
}

static struct var *find_or_create_var(char name1, char name2, int is_string, int want_array, int array_size)
{
    register int i;
    struct var *v;
    
    for (i = 0; i < var_count; i++) {
        if (vars[i].name1 == name1 && vars[i].name2 == name2 && vars[i].is_string == is_string) {
            v = &vars[i];
            
            if (want_array && !v->is_array) {
                v->is_array = 1;
                v->size = array_size;
                v->array = (struct value *)calloc(array_size, sizeof(struct value));
                if (!v->array) {
                    runtime_error("Out of memory");
                }
            } else if (want_array && array_size > v->size) {
                struct value *new_arr = (struct value *)realloc(v->array, array_size * sizeof(struct value));
                if (new_arr) {
                    memset(new_arr + v->size, 0, (array_size - v->size) * sizeof(struct value));
                    v->array = new_arr;
                    v->size = array_size;
                } else {
                    runtime_error("Out of memory");
                }
            }
            return v;
        }
    }
    
    if (var_count >= MAX_VARS) {
        runtime_error("Variable table full");
        return NULL;
    }
    
    v = &vars[var_count++];
    v->name1 = name1;
    v->name2 = name2;
    v->is_string = is_string;
    v->is_array = want_array;
    v->size = want_array ? array_size : 0;
    v->array = NULL;
    v->scalar = is_string ? make_str("") : make_num(0.0);
    
    if (want_array) {
        v->array = (struct value *)calloc(array_size, sizeof(struct value));
        if (!v->array) {
            runtime_error("Out of memory");
        }
    }
    
    return v;
}

static int read_identifier(char **p, char *buf, int buf_size)
{
    register int i = 0;
    register char *q = *p;
    
    while ((isalpha((unsigned char)*q) || isdigit((unsigned char)*q) || *q == '$') && i < buf_size - 1) {
        buf[i++] = *q++;
    }
    buf[i] = '\0';
    *p = q;
    return i;
}

static struct value *get_var_reference(char **p, int *is_array_out, int *is_string_out)
{
    char namebuf[8];
    char n1, n2;
    int is_string, is_array = 0, array_size = 0, array_index = -1;
    struct var *v;
    struct value *valp, idx_val;

    skip_spaces(p);
    if (!isalpha((unsigned char)**p)) {
        runtime_error("Expected variable");
        return NULL;
    }
    
    read_identifier(p, namebuf, sizeof(namebuf));
    uppercase_name(namebuf, &n1, &n2, &is_string);
    
    if (is_string_out) *is_string_out = is_string;
    
    skip_spaces(p);
    if (**p == '(') {
        is_array = 1;
        (*p)++;
        idx_val = eval_expr(p);
        ensure_num(&idx_val);
        skip_spaces(p);
        
        if (**p != ')') {
            runtime_error("Missing ')'");
            return NULL;
        }
        (*p)++;
        
        array_index = (int)(idx_val.num + 0.00001);
        if (array_index < 0) {
            runtime_error("Negative array index");
            return NULL;
        }
        
        array_size = (array_index + 1 < DEFAULT_ARRAY_SIZE) ? DEFAULT_ARRAY_SIZE : array_index + 1;
    }
    
    if (is_array_out) *is_array_out = is_array;
    
    v = find_or_create_var(n1, n2, is_string, is_array, array_size);
    if (!v) return NULL;
    
    if (!is_array) {
        valp = &v->scalar;
    } else {
        if (array_index >= v->size) {
            struct value *new_arr = (struct value *)realloc(v->array, (array_index + 1) * sizeof(struct value));
            if (!new_arr) {
                runtime_error("Out of memory");
                return NULL;
            }
            memset(new_arr + v->size, 0, (array_index + 1 - v->size) * sizeof(struct value));
            v->array = new_arr;
            v->size = array_index + 1;
        }
        valp = &v->array[array_index];
    }
    
    if (is_string && valp->type != VAL_STR) {
        *valp = make_str("");
    } else if (!is_string && valp->type != VAL_NUM) {
        *valp = make_num(0.0);
    }
    
    return valp;
}

static struct value eval_factor(char **p);
static struct value eval_power(char **p);
static struct value eval_term(char **p);

static struct value eval_factor(char **p)
{
    struct value v;
    double num;
    register int i;
    
    skip_spaces(p);
    
    if (**p == '(') {
        (*p)++;
        v = eval_expr(p);
        skip_spaces(p);
        if (**p == ')') {
            (*p)++;
        } else {
            runtime_error("Missing ')'");
        }
        return v;
    }
    
    if (**p == '\"') {
        (*p)++;
        i = 0;
        while (**p && **p != '\"' && i < MAX_STR_LEN - 1) {
            temp_buffer[i++] = **p;
            (*p)++;
        }
        temp_buffer[i] = '\0';
        if (**p == '\"') {
            (*p)++;
        } else {
            runtime_error("Unterminated string");
        }
        return make_str(temp_buffer);
    }
    
    if (isalpha((unsigned char)**p)) {
        if (starts_with_kw(*p, "SIN") || starts_with_kw(*p, "COS") || starts_with_kw(*p, "TAN") ||
            starts_with_kw(*p, "ABS") || starts_with_kw(*p, "INT") || starts_with_kw(*p, "SQR") ||
            starts_with_kw(*p, "SGN") || starts_with_kw(*p, "EXP") || starts_with_kw(*p, "LOG") ||
            starts_with_kw(*p, "RND") || starts_with_kw(*p, "LEN") || starts_with_kw(*p, "VAL") ||
            starts_with_kw(*p, "STR") || starts_with_kw(*p, "CHR") || starts_with_kw(*p, "ASC") ||
            starts_with_kw(*p, "TAB")) {
            char namebuf[8];
            char *q = *p;
            read_identifier(&q, namebuf, sizeof(namebuf));
            return eval_function(namebuf, p);
        } else {
            struct value *vp = get_var_reference(p, NULL, NULL);
            return vp ? *vp : make_num(0.0);
        }
    }
    
    if (**p == '+' || **p == '-') {
        char sign = **p;
        struct value inner;
        (*p)++;
        inner = eval_factor(p);
        ensure_num(&inner);
        if (sign == '-') inner.num = -inner.num;
        return inner;
    }
    
    if (parse_number_literal(p, &num)) {
        return make_num(num);
    }
    
    runtime_error("Syntax error in expression");
    return make_num(0.0);
}

static struct value eval_power(char **p)
{
    struct value left, right;
    
    skip_spaces(p);
    left = eval_factor(p);
    skip_spaces(p);
    
    if (**p == '^') {
        (*p)++;
        right = eval_power(p);
        ensure_num(&left);
        ensure_num(&right);
        left.num = pow(left.num, right.num);
    }
    return left;
}

static struct value eval_term(char **p)
{
    struct value left, right;
    char op;
    
    skip_spaces(p);
    left = eval_power(p);
    
    for (;;) {
        skip_spaces(p);
        if (**p == '*' || **p == '/') {
            op = **p;
            (*p)++;
            right = eval_power(p);
            ensure_num(&left);
            ensure_num(&right);
            left.num = (op == '*') ? left.num * right.num : left.num / right.num;
        } else {
            break;
        }
    }
    return left;
}

static struct value eval_expr(char **p)
{
    struct value left, right;
    char op;
    
    skip_spaces(p);
    left = eval_term(p);
    
    for (;;) {
        skip_spaces(p);
        if (**p == '+' || **p == '-') {
            op = **p;
            (*p)++;
            right = eval_term(p);
            
            if (op == '+') {
                if (left.type == VAL_STR || right.type == VAL_STR) {
                    ensure_str(&left);
                    ensure_str(&right);
                    strncat(left.str, right.str, MAX_STR_LEN - strlen(left.str) - 1);
                } else {
                    left.num += right.num;
                }
            } else {
                ensure_num(&left);
                ensure_num(&right);
                left.num -= right.num;
            }
        } else {
            break;
        }
    }
    return left;
}

static int eval_condition(char **p)
{
    struct value left, right;
    char op1, op2;
    int result;
    
    skip_spaces(p);
    left = eval_expr(p);
    skip_spaces(p);
    
    op1 = **p;
    op2 = *(*p + 1);
    
    if (op1 == '<' && op2 == '>') {
        *p += 2;
        right = eval_expr(p);
        if (left.type == VAL_STR || right.type == VAL_STR) {
            ensure_str(&left);
            ensure_str(&right);
            return strcmp(left.str, right.str) != 0;
        }
        return left.num != right.num;
    }
    
    if (op1 == '<' && op2 == '=') {
        *p += 2;
        right = eval_expr(p);
        ensure_num(&left);
        ensure_num(&right);
        return left.num <= right.num;
    }
    
    if (op1 == '>' && op2 == '=') {
        *p += 2;
        right = eval_expr(p);
        ensure_num(&left);
        ensure_num(&right);
        return left.num >= right.num;
    }
    
    if (op1 == '<' || op1 == '>' || op1 == '=') {
        (*p)++;
        right = eval_expr(p);
        
        if (left.type == VAL_STR || right.type == VAL_STR) {
            ensure_str(&left);
            ensure_str(&right);
            result = strcmp(left.str, right.str);
            return (op1 == '<') ? (result < 0) : (op1 == '>') ? (result > 0) : (result == 0);
        }
        
        return (op1 == '<') ? (left.num < right.num) : 
               (op1 == '>') ? (left.num > right.num) : 
               (left.num == right.num);
    }
    
    return (left.type == VAL_STR) ? (strlen(left.str) > 0) : (left.num != 0.0);
}

static void statement_rem(char **p)
{
    *p += strlen(*p);
}

static void statement_print(char **p)
{
    int newline = 1;
    struct value v;
    
    for (;;) {
        skip_spaces(p);
        if (**p == '\0' || **p == ':') break;
        
        v = eval_expr(p);
        print_value(&v);
        skip_spaces(p);
        
        if (**p == ';') {
            newline = 0;
            (*p)++;
        } else if (**p == ',') {
            newline = 0;
            print_spaces(((print_col / 10) + 1) * 10 - print_col);
            (*p)++;
        } else {
            newline = 1;
            break;
        }
    }
    
    if (newline) {
        fputc('\n', stdout);
        print_col = 0;
    }
    fflush(stdout);
}

static void statement_input(char **p)
{
    char prompt[MAX_STR_LEN];
    char linebuf[MAX_LINE_LEN];
    int first_prompt = 1;
    struct value *vp;
    int is_array, is_string;

    prompt[0] = '\0';
    skip_spaces(p);
    
    if (**p == '\"') {
        struct value s = eval_factor(p);
        ensure_str(&s);
        strncpy(prompt, s.str, sizeof(prompt) - 1);
        prompt[sizeof(prompt) - 1] = '\0';
        skip_spaces(p);
        if (**p == ';' || **p == ',') (*p)++;
    }
    
    for (;;) {
        skip_spaces(p);
        if (**p == '\0' || **p == ':') break;
        if (!isalpha((unsigned char)**p)) {
            runtime_error("Expected variable in INPUT");
            return;
        }
        
        vp = get_var_reference(p, &is_array, &is_string);
        if (!vp) return;
        
        if (prompt[0] != '\0' && first_prompt) printf("%s", prompt);
        printf("? ");
        fflush(stdout);
        
        if (!fgets(linebuf, sizeof(linebuf), stdin)) {
            runtime_error("Unexpected end of input");
            return;
        }
        trim_newline(linebuf);
        
        if (is_string) {
            *vp = make_str(linebuf);
        } else {
            *vp = make_num(atof(linebuf));
        }
        
        skip_spaces(p);
        if (**p == ',') {
            (*p)++;
            first_prompt = 0;
            continue;
        }
        break;
    }
}

static void statement_let(char **p)
{
    struct value *vp;
    struct value rhs;
    int is_array, is_string;

    vp = get_var_reference(p, &is_array, &is_string);
    if (!vp) return;
    
    skip_spaces(p);
    if (**p != '=') {
        runtime_error("Expected '='");
        return;
    }
    (*p)++;
    
    rhs = eval_expr(p);
    if (is_string) {
        ensure_str(&rhs);
    } else {
        ensure_num(&rhs);
    }
    *vp = rhs;
}

static void statement_goto(char **p)
{
    int line_number;
    
    skip_spaces(p);
    line_number = atoi(*p);
    while (**p && isdigit((unsigned char)**p)) (*p)++;
    
    current_line = find_line_index(line_number);
    if (current_line < 0) {
        runtime_error("Target line not found");
        return;
    }
    statement_pos = NULL;
}

static void statement_gosub(char **p)
{
    int target;
    char *return_pos;

    if (gosub_top >= MAX_GOSUB) {
        runtime_error("GOSUB stack overflow");
        return;
    }
    
    skip_spaces(p);
    target = atoi(*p);
    while (**p && isdigit((unsigned char)**p)) (*p)++;
    
    return_pos = *p;
    gosub_stack[gosub_top].line_index = current_line;
    gosub_stack[gosub_top].position = return_pos;
    gosub_top++;
    
    current_line = find_line_index(target);
    if (current_line < 0) {
        runtime_error("Target line not found");
        return;
    }
    statement_pos = NULL;
}

static void statement_return(char **p)
{
    if (gosub_top <= 0) {
        runtime_error("RETURN without GOSUB");
        return;
    }
    
    gosub_top--;
    current_line = gosub_stack[gosub_top].line_index;
    statement_pos = gosub_stack[gosub_top].position;
}

static void statement_if(char **p)
{
    int cond_true;

    cond_true = eval_condition(p);
    skip_spaces(p);
    
    if (!starts_with_kw(*p, "THEN")) {
        runtime_error("Missing THEN");
        return;
    }
    *p += 4;
    skip_spaces(p);
    
    if (!cond_true) {
        *p += strlen(*p);
        return;
    }
    
    if (isdigit((unsigned char)**p)) {
        int target = atoi(*p);
        while (**p && isdigit((unsigned char)**p)) (*p)++;
        
        current_line = find_line_index(target);
        if (current_line < 0) {
            runtime_error("Target line not found");
            return;
        }
        statement_pos = NULL;
    } else {
        skip_spaces(p);
        statement_pos = *p;
    }
}

static void statement_for(char **p)
{
    struct value *vp;
    struct value startv, endv, stepv;
    int is_array, is_string, i;
    
    if (for_top >= MAX_FOR) {
        runtime_error("FOR stack overflow");
        return;
    }
    
    vp = get_var_reference(p, &is_array, &is_string);
    if (!vp) return;
    
    if (is_array) {
        runtime_error("FOR variable must be scalar");
        return;
    }
    if (is_string) {
        runtime_error("FOR variable must be numeric");
        return;
    }
    
    skip_spaces(p);
    if (**p != '=') {
        runtime_error("Expected '=' in FOR");
        return;
    }
    (*p)++;
    
    startv = eval_expr(p);
    ensure_num(&startv);
    
    skip_spaces(p);
    if (!starts_with_kw(*p, "TO")) {
        runtime_error("Expected TO in FOR");
        return;
    }
    *p += 2;
    
    endv = eval_expr(p);
    ensure_num(&endv);
    
    skip_spaces(p);
    if (starts_with_kw(*p, "STEP")) {
        *p += 4;
        stepv = eval_expr(p);
        ensure_num(&stepv);
    } else {
        stepv = make_num(1.0);
    }
    
    *vp = startv;
    
    for_stack[for_top].name1 = ' ';
    for_stack[for_top].name2 = ' ';
    
    for (i = 0; i < var_count; i++) {
        if (&vars[i].scalar == vp || (vars[i].is_array && vp >= vars[i].array && vp < vars[i].array + vars[i].size)) {
            for_stack[for_top].name1 = vars[i].name1;
            for_stack[for_top].name2 = vars[i].name2;
            break;
        }
    }
    
    for_stack[for_top].end_value = endv.num;
    for_stack[for_top].step = stepv.num;
    for_stack[for_top].line_index = current_line;
    for_stack[for_top].resume_pos = *p;
    for_stack[for_top].var = vp;
    for_stack[for_top].is_string = is_string;
    for_top++;
}

static void statement_next(char **p)
{
    char namebuf[8];
    char n1, n2;
    int i, is_string;
    struct value *vp;
    
    skip_spaces(p);
    if (isalpha((unsigned char)**p)) {
        read_identifier(p, namebuf, sizeof(namebuf));
    } else {
        namebuf[0] = '\0';
    }
    
    uppercase_name(namebuf, &n1, &n2, &is_string);
    
    for (i = for_top - 1; i >= 0; i--) {
        if (namebuf[0] == '\0' || (for_stack[i].name1 == n1 && for_stack[i].name2 == n2)) {
            break;
        }
    }
    
    if (i < 0) {
        runtime_error("NEXT without FOR");
        return;
    }
    
    for_top = i + 1;
    vp = for_stack[for_top - 1].var;
    if (!vp) {
        runtime_error("Loop variable missing");
        return;
    }
    
    vp->num += for_stack[for_top - 1].step;
    
    if ((for_stack[for_top - 1].step >= 0 && vp->num <= for_stack[for_top - 1].end_value) ||
        (for_stack[for_top - 1].step < 0 && vp->num >= for_stack[for_top - 1].end_value)) {
        current_line = for_stack[for_top - 1].line_index;
        statement_pos = for_stack[for_top - 1].resume_pos;
    } else {
        for_top--;
    }
}

static void statement_dim(char **p)
{
    for (;;) {
        char namebuf[8];
        char n1, n2;
        int is_string, size;
        struct var *v;
        struct value sizev;
        
        skip_spaces(p);
        if (!isalpha((unsigned char)**p)) {
            runtime_error("Expected array name");
            return;
        }
        
        read_identifier(p, namebuf, sizeof(namebuf));
        uppercase_name(namebuf, &n1, &n2, &is_string);
        
        skip_spaces(p);
        if (**p != '(') {
            runtime_error("DIM requires size");
            return;
        }
        (*p)++;
        
        sizev = eval_expr(p);
        ensure_num(&sizev);
        size = (int)sizev.num + 1;
        
        if (size <= 0) {
            runtime_error("Invalid array size");
            return;
        }
        
        skip_spaces(p);
        if (**p != ')') {
            runtime_error("Missing ')'");
            return;
        }
        (*p)++;
        
        v = find_or_create_var(n1, n2, is_string, 1, size);
        (void)v;
        
        skip_spaces(p);
        if (**p == ',') {
            (*p)++;
            continue;
        }
        break;
    }
}

static void statement_end(char **p)
{
    halted = 1;
    *p += strlen(*p);
}

static void execute_statement(char **p)
{
    skip_spaces(p);
    if (**p == '\0') return;
    
    if (starts_with_kw(*p, "REM") || **p == '\'') {
        statement_rem(p);
        return;
    }
    if (starts_with_kw(*p, "PRINT") || **p == '?') {
        if (**p == '?') {
            (*p)++;
        } else {
            *p += 5;
        }
        statement_print(p);
        return;
    }
    if (starts_with_kw(*p, "INPUT")) {
        *p += 5;
        statement_input(p);
        return;
    }
    if (starts_with_kw(*p, "LET")) {
        *p += 3;
        statement_let(p);
        return;
    }
    if (starts_with_kw(*p, "GOTO")) {
        *p += 4;
        statement_goto(p);
        return;
    }
    if (starts_with_kw(*p, "GOSUB")) {
        *p += 5;
        statement_gosub(p);
        return;
    }
    if (starts_with_kw(*p, "RETURN")) {
        *p += 6;
        statement_return(p);
        return;
    }
    if (starts_with_kw(*p, "IF")) {
        *p += 2;
        statement_if(p);
        return;
    }
    if (starts_with_kw(*p, "FOR")) {
        *p += 3;
        statement_for(p);
        return;
    }
    if (starts_with_kw(*p, "NEXT")) {
        *p += 4;
        statement_next(p);
        return;
    }
    if (starts_with_kw(*p, "DIM")) {
        *p += 3;
        statement_dim(p);
        return;
    }
    if (starts_with_kw(*p, "END") || starts_with_kw(*p, "STOP")) {
        statement_end(p);
        return;
    }
    
    if (isalpha((unsigned char)**p)) {
        statement_let(p);
        return;
    }
    
    runtime_error("Unknown statement");
}

static void sort_program(void)
{
    register int i, j;
    for (i = 0; i < line_count; i++) {
        for (j = i + 1; j < line_count; j++) {
            if (program_lines[j]->number < program_lines[i]->number) {
                struct line *tmp = program_lines[i];
                program_lines[i] = program_lines[j];
                program_lines[j] = tmp;
            }
        }
    }
}

/* Binary search for line index with caching */
static int find_line_index(int number)
{
    register int low, high, mid;
    
    if (number == last_lookup_num) {
        return last_lookup_idx;
    }
    
    low = 0;
    high = line_count - 1;
    
    while (low <= high) {
        mid = (low + high) / 2;
        
        if (program_lines[mid]->number == number) {
            last_lookup_num = number;
            last_lookup_idx = mid;
            return mid;
        }
        
        if (program_lines[mid]->number < number) {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    return -1;
}

static void add_or_replace_line(int number, const char *text)
{
    register int i;
    
    for (i = 0; i < line_count; i++) {
        if (program_lines[i] && program_lines[i]->number == number) {
            if (program_lines[i]->text) {
                free(program_lines[i]->text);
            }
            program_lines[i]->text = dupstr_local(text);
            return;
        }
    }
    
    if (line_count >= MAX_LINES) {
        runtime_error("Program too large");
        return;
    }
    
    program_lines[line_count] = (struct line *)malloc(sizeof(struct line));
    if (!program_lines[line_count]) {
        runtime_error("Out of memory");
        return;
    }
    
    program_lines[line_count]->number = number;
    program_lines[line_count]->text = dupstr_local(text);
    line_count++;
}

static void load_program(const char *path)
{
    FILE *f;
    char linebuf[MAX_LINE_LEN];
    
    f = fopen(path, "r");
    if (!f) {
        fprintf(stderr, "Cannot open %s\n", path);
        exit(1);
    }
    
    while (fgets(linebuf, sizeof(linebuf), f)) {
        char *p;
        int number;
        
        if (strlen(linebuf) >= MAX_LINE_LEN - 1 && linebuf[MAX_LINE_LEN - 2] != '\n') {
            fprintf(stderr, "Line too long (max %d chars)\n", MAX_LINE_LEN);
            fclose(f);
            exit(1);
        }
        
        trim_newline(linebuf);
        p = linebuf;
        
        while (*p == ' ' || *p == '\t') p++;
        
        if ((unsigned char)p[0] == 0xef && (unsigned char)p[1] == 0xbb && (unsigned char)p[2] == 0xbf) {
            p += 3;
        }
        
        if (*p == '\0') continue;
        
        if (!isdigit((unsigned char)*p)) {
            fprintf(stderr, "Line missing number: %s\n", linebuf);
            fclose(f);
            exit(1);
        }
        
        number = atoi(p);
        
        if (number < 0 || number > 65535) {
            fprintf(stderr, "Line number out of range: %d\n", number);
            fclose(f);
            exit(1);
        }
        
        while (*p && !isspace((unsigned char)*p)) p++;
        while (*p == ' ' || *p == '\t') p++;
        
        add_or_replace_line(number, p);
    }
    
    fclose(f);
    sort_program();
}

static void run_program(void)
{
    halted = 0;
    current_line = 0;
    statement_pos = NULL;
    print_col = 0;
    
    while (!halted && current_line >= 0 && current_line < line_count) {
        char *p;
        
        if (statement_pos == NULL) {
            statement_pos = program_lines[current_line]->text;
        }
        
        p = statement_pos;
        skip_spaces(&p);
        
        if (*p == '\0') {
            current_line++;
            statement_pos = NULL;
            continue;
        }
        
        statement_pos = p;
        execute_statement(&statement_pos);
        
        if (halted) break;
        if (statement_pos == NULL) continue;
        
        skip_spaces(&statement_pos);
        if (*statement_pos == ':') {
            statement_pos++;
            continue;
        }
        
        skip_spaces(&statement_pos);
        if (*statement_pos == '\0') {
            current_line++;
            statement_pos = NULL;
        }
    }
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <program.bas>\n", argv[0]);
        return 1;
    }
    
    load_program(argv[1]);
    run_program();
    cleanup_program();
    
    return 0;
}
