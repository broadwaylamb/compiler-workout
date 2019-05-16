/* Runtime library */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <alloca.h>
#include <stdlib.h>
#include <stddef.h>
#include <stdbool.h>

typedef ssize_t word;

enum {
  STRING_TAG = 0x00000000,
  ARRAY_TAG  = 0x01000000,
  SEXP_TAG   = 0x02000000,
};

typedef struct {
  word tag;
  char contents[0];
} data; 

typedef struct {
  word tag;
  data contents;
} sexp;

static word len(word x) {
  return x & 0x00FFFFFF;
}

static word tag(word x) {
  return x & 0xFF000000;
}

static data *to_data(void *x) {
  return (data*)((char*)x - sizeof(word));
}

static sexp *to_sexp(void *x) {
  return (sexp*)((char*)x - 2 * sizeof(word));
}

static bool unboxed(void *x) {
  return ((word)x) & 0x0001;
}

static word unbox(word x) {
  return ((word)x) >> 1;
}

static word box(word x) {
  return (((word)x) << 1) | 0x0001;
}

extern word Blength(void *p) {
  data *a = to_data(p);
  return box(len(a->tag));
}

static char* de_hash(word n) {
  static const char *chars =
  "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNJPQRSTUVWXYZ";
  static char buf[6];
  char *p = &buf[5];

  /*printf("tag: %d\n", n);*/
  
  *p-- = 0;

  while (n != 0) {
    /*printf("char: %c\n", chars [n & 0x003F]);*/
    *p-- = chars [n & 0x003F];
    n = n >> 6;
  }
  
  return ++p;
}

typedef struct {
  char *contents;
  word ptr;
  word len;
} StringBuf;

static StringBuf stringBuf;

const word STRINGBUF_INIT = 128;

static void createStringBuf() {
  stringBuf.contents = malloc(STRINGBUF_INIT);
  stringBuf.ptr      = 0;
  stringBuf.len      = STRINGBUF_INIT;
}

static void deleteStringBuf() {
  free(stringBuf.contents);
}

static void extendStringBuf() {
  word len = stringBuf.len << 1;

  stringBuf.contents = (char*) realloc(stringBuf.contents, len);
  stringBuf.len      = len;
}

static void printStringBuf(char *fmt, ...) {
  va_list args;
  word    written, rest;
  char   *buf;

again:
  va_start(args, fmt);
  buf     = &stringBuf.contents[stringBuf.ptr];
  rest    = stringBuf.len - stringBuf.ptr;
  written = vsnprintf(buf, rest, fmt, args);
  
  if (written >= rest) {
    extendStringBuf();
    goto again;
  }

  stringBuf.ptr += written;
}

static void printValue(void *p) {
  if (unboxed(p)) printStringBuf("%zd", unbox((word)p));
  else {
    data *a = to_data(p);

    switch (tag(a->tag)) {
      case STRING_TAG:
        printStringBuf("\"%s\"", a->contents);
        break;

      case ARRAY_TAG:
        printStringBuf("[");
        for (int i = 0; i < len(a->tag); i++) {
          printValue((void*)((word*)a->contents)[i]);
          if (i != len(a->tag) - 1) printStringBuf(", ");
        }
        printStringBuf("]");
        break;

      case SEXP_TAG:
        printStringBuf("`%s", de_hash(to_sexp(p)->tag));
        if (len(a->tag)) {
          printStringBuf(" (");
          for (int i = 0; i < len(a->tag); i++) {
            printValue((void*)((word*) a->contents)[i]);
            if (i != len(a->tag) - 1) printStringBuf(", ");
          }
          printStringBuf(")");
        }
        break;

      default:
        printStringBuf("*** invalid tag: %x ***", tag(a->tag));
    }
  }
}

extern void* Belem(word i, void *p) {
  data *a = to_data(p);
  i = unbox(i);
  
  // printf("elem %d = %p\n", i, (void*)((word*) a->contents)[i]);

  if (tag(a->tag) == STRING_TAG) {
    return (void*) box(a->contents[i]);
  }
  
  return (void*)((word*) a->contents)[i];
}

extern void* Bstring(const char *p) {
  word n = strlen(p);
  data *r = malloc(sizeof(data) + n + 1);

  r->tag = STRING_TAG | n;
  strncpy(r->contents, p, n + 1);
  
  return r->contents;
}

extern void* Bstringval(void *p) {
  
  createStringBuf();
  printValue(p);

  void *s = Bstring(stringBuf.contents);
  
  deleteStringBuf();

  return s;
}

extern void* Barray(word n, ...) {
  va_list args;
  data *r = malloc(sizeof(data) + sizeof(word) * n);

  r->tag = ARRAY_TAG | n;
  
  va_start(args, n);
  
  for (word i = 0; i < n; i++) {
    word ai = va_arg(args, word);
    ((word*)r->contents)[i] = ai;
  }
  
  va_end(args);

  return r->contents;
}

extern void* Bsexp(word n, word tag, ...) {
  va_list args;
  sexp *r = malloc(sizeof(sexp) + sizeof(word) * n);
  data *d = &(r->contents);

  d->tag = SEXP_TAG | n;
  
  va_start(args, tag);

  r->tag = tag;
  
  for (word i = 0; i < n; i++) {
    word ai = va_arg(args, word);
    // printf("arg %d = %x\n", i, ai);
    ((word*)d->contents)[i] = ai;
  }

  va_end(args);

  // printf("tag %d\n", r->tag);
  // printf("returning %p\n", d->contents);
  
  return d->contents;
}

extern word Btag(word t, void *d) {
  data *r = to_data(d);
  return box(tag(r->tag) == SEXP_TAG && to_sexp(d)->tag == t);
}

extern void Bsta(word n, void *s, word v, ...) {
  va_list args;
  word k;
  data *a;
  
  va_start(args, v);

  for (word i = 0; i < n - 1; i++) {
    k = unbox(va_arg(args, word));
    s = ((word**)s) [k];
  }

  k = unbox(va_arg(args, word));
  a = to_data(s);
  
  if (tag(a->tag) == STRING_TAG)((char*) s)[k] = (char)unbox(v);
  else ((word*)s)[k] = v;
}

extern word Lraw(word x) {
  return unbox(x);
}

extern void Lprintf(char *s, ...) {
  va_list args;

  va_start(args, s);
  vprintf(s, args); // vprintf(char *, va_list) <-> printf(char *, ...)
  va_end(args);
}

extern void* Lstrcat(void *a, void *b) {
  data *da = to_data(a);
  data *db = to_data(b);
  
  data *d  = malloc(sizeof(data) + len(da->tag) + len(db->tag) + 1);

  d->tag = len(da->tag) + len(db->tag);

  strcpy(d->contents, da->contents);
  strcat(d->contents, db->contents);

  return d->contents;
}

extern void Lfprintf(FILE *f, char *s, ...) {
  va_list args;

  va_start(args, s);
  vfprintf(f, s, args);
  va_end(args);
}

extern FILE* Lfopen(char *f, char *m) {
  return fopen(f, m);
}

extern void Lfclose(FILE *f) {
  fclose(f);
}

/* Lread is an implementation of the "read" construct */
extern word Lread() {
  word result;

  printf("> ");
  fflush(stdout);
  scanf ("%zd", &result);

  return box(result);
}

/* Lwrite is an implementation of the "write" construct */
extern word Lwrite(word n) {
  printf("%zd\n", unbox(n));
  fflush(stdout);

  return 0;
}

