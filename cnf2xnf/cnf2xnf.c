// Copyright (2021) Armin Biere, JKU LInz.

#define VERSION "0.3"

// *INDENT-OFF*

static const char * usage =
"usage: cnf2xnf [ <option> ... ] [ <input> [ <output> [ <extension> ] ] ]\n"
"\n"
"The '<option>' argument is one of the following:\n"
"\n"
"  --version        print version and exit\n"
"  -h | --help      print this command line option summary\n"
#ifndef LOGGING
"  -q | --quiet     do not print verbose message\n"
#endif
"  -n | --no-write  dry run only\n"
"\n"
"  --no-compact     do not compact variable range\n"
"  --no-eliminate   do not eliminate variables occurring in XORs only\n"
"  --no-gates       do not extract gates\n"
"\n"
"The input CNF in DIMACS format is specified as '<input-cnf>' and\n"
"the output file in XNF (CNF+XOR) format as '<output-xnf>'.  If these\n"
"are missing we read from '<stdin>' and write from '<stdout>'.  You can\n"
"also use the file '-' to force this.  Further if the file path is given\n"
"and it has a suffix '.xz', '.gz' or '.bz2' then the file is assumed to\n"
"be compressed and either compressed or decompressed with corresponding\n"
"compression utilities 'xz', 'gunzip', and 'bunzip2'.\n";

// *INDENT-ON*

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

struct constraint
{
  bool garbage;
  bool parity;
  bool xor;
  int size;
  int literals[];
};

struct constraints
{
  struct constraint **begin, **end, **allocated;
};

struct literals
{
  int *begin, *end, *allocated;
};

#define SWAP(A,B) \
do { \
  typeof(A) TMP = (A); \
  (A) = (B); \
  (B) = TMP; \
} while (0)

#define SIZE(S) ((int)((S).end - (S).begin))
#define FULL(S) ((S).end == (S).allocated)
#define EMPTY(S) ((S).begin == (S).end)
#define CLEAR(S) do { (S).end = (S).begin; } while (0)

#define RESET(S,N) \
do { \
  assert ((N) <= SIZE (S) ); \
  (S).end = (S).begin + (N); \
} while (0)

#define ENLARGE(S) \
do { \
  assert (FULL (S)); \
  size_t OLD_SIZE = SIZE (S); \
  size_t NEW_SIZE = OLD_SIZE ? 2*OLD_SIZE : 1; \
  size_t NEW_BYTES = NEW_SIZE * sizeof *(S).begin; \
  (S).begin = realloc ((S).begin, NEW_BYTES); \
  if (!(S).begin) \
    out_of_memory (); \
  (S).end = (S).begin + OLD_SIZE; \
  (S).allocated = (S).begin + NEW_SIZE; \
} while (0)

#define PUSH(S,E) \
do { \
  if (FULL (S)) \
    ENLARGE (S); \
  *(S).end++ = (E); \
} while (0)

#define REMOVE(S,E) \
do { \
  typeof ((S).begin) P = (S).begin, END = (S).end; \
  while (assert (P != END), *P != (E)) \
    P++; \
  while (++P != END) \
    P[-1] = P[0]; \
  (S).end = P - 1; \
} while (0)

#define POP(S) \
  (assert (!EMPTY (S)), *--(S).end)

#define all_literals_in_constraint(L,C) \
  int L, * L ## _PTR = (C)->literals, \
         * L ## _END = L ## _PTR + (C)->size; \
  (L ## _PTR != L ## _END) && (L = *L ## _PTR, true); \
  ++L ## _PTR

#define all_stack(T,E,S) \
  T E, * E ## _PTR = (S).begin, * E ## _END = (S).end; \
  (E ## _PTR != E ## _END) && (E = *E ## _PTR, true); \
  ++E ## _PTR

#define all_constraints(C,CS) \
  struct constraint * C, ** C ## _PTR = (CS).begin, ** C ## _END = (CS).end; \
  (C ## _PTR != C ## _END) && (C = *C ## _PTR, true); \
  ++C ## _PTR

#define all_literals(L) \
  int L = -vars; L <= vars; L++

#define all_variables(I) \
  int I = 1; I <= vars; I++ 

static int vars;
static int mapped;
static int reduced;
static signed char *mark;
static signed char *clausal;
static struct literals literals;
static struct literals schedule;
static struct constraints xors;
static struct constraints clauses;
static struct constraints *occs;
static struct constraints collect;
static int original;
static int * map;

#ifndef LOGGING
static bool quiet;
#endif
static bool extract_gates = true;
static bool eliminate_xors = true;
static bool compact_variables = true;

static const char *do_not_write_output;

static FILE *input_file;
static FILE *output_file;
static FILE *extend_file;
static const char *input_path;
static const char *output_path;
static const char *extend_path;
static int close_input;
static int close_output;
static int close_extend;

static bool inconsistent;
static int trivial;
static int eliminated;
static int substituted;
static int extracted;
static int equivalences;
static int direct;
static int gates;
static int kept;

static double
percent (double a, double b)
{
  return b ? 100.0 * a / b : 0;
}

#include <sys/time.h>
#include <sys/resource.h>

static double
timevoid (void)
{
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u))
    return 0;
  double res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

static double started = 0;

static void
start (void)
{
  started = timevoid ();
}

static double
stop (void)
{
  return timevoid () - started;
}

static void die (const char *, ...) __attribute__((format (printf, 1, 2)));
static void msg (const char *, ...) __attribute__((format (printf, 1, 2)));

#ifdef LOGGING
static void logging (const char *, ...)
  __attribute__((format (printf, 1, 2)));
static void logxor (struct constraint *, const char *, ...)
  __attribute__((format (printf, 2, 3)));
#endif

static void
die (const char *fmt, ...)
{
  fputs ("cnf2xnf: error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void
out_of_memory (void)
{
  die ("out-of-memory");
}

static void
msg (const char *fmt, ...)
{
#ifndef LOGGING
  if (quiet)
    return;
#endif
  fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

#ifdef LOGGING

static void
logging (const char *fmt, ...)
{
  fputs ("c LOG ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void
logxor (struct constraint *x, const char *fmt, ...)
{
  fputs ("c LOG ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  printf (" size %d XOR", x->size);
  bool first = true;
  for (all_literals_in_constraint (idx, x))
    printf ("%s%d", first ? " " : " + ", idx), first = false;
  printf (" = %d\n", x->parity);
  fflush (stdout);
}

#define LOG(...) do { logging(__VA_ARGS__); } while (0)
#define LOGXOR(...) do { logxor(__VA_ARGS__); } while (0)

#else

#define LOG(...) do { } while (0)
#define LOGXOR(...) do { } while (0)

#endif

static struct constraint *
new_constraint (bool xor, bool parity, int size, int *literals)
{
  size_t header_bytes = sizeof (struct constraint);
  size_t literals_bytes = size * sizeof (int);
  struct constraint *res = malloc (header_bytes + literals_bytes);
  if (!res)
    out_of_memory ();
  res->garbage = false;
  res->xor = xor;
  res->parity = parity;
  res->size = size;
  memcpy (res->literals, literals, literals_bytes);
  return res;
}

static struct constraint *
new_clause (int size, int *literals)
{
  return new_constraint (false, false, size, literals);
}

static struct constraint *
new_xor (bool parity, int size, int *literals)
{
  return new_constraint (true, parity, size, literals);
}

static void
connect_literal (int lit, struct constraint *c)
{
  PUSH (occs[lit], c);
}

static void
disconnect_literal (int idx, struct constraint * c)
{
  struct constraints * cs = occs + idx;
  REMOVE (*cs, c);
}

static void
connect_constraint (struct constraint *c)
{
  for (all_literals_in_constraint (lit, c))
    connect_literal (lit, c);
}

static void
disconnect_constraint (struct constraint * c, int except)
{
  for (all_literals_in_constraint (lit, c))
    if (lit != except)
      disconnect_literal (lit, c);
}

static void
parse (void)
{
  start ();
  msg ("reading '%s'", input_path);

  {
    int ch = getc (input_file);
    while ((ch == 'c'))
      {
	while ((ch = getc (input_file)) != '\n')
	  if (ch == EOF)
	    die ("unexpected end-of-file");
	ch = getc (input_file);
      }
    ungetc (ch, input_file);
  }

  if (fscanf (input_file, "p cnf %d %d", &vars, &original) != 2 ||
      vars < 0 || vars == INT_MAX || original < 0)
    die ("invalid header");
  msg ("parsed 'p cnf %d %d' header", vars, original);

  occs = calloc (2u * vars + 1, sizeof *occs);
  if (!occs)
    out_of_memory ();
  occs += vars;

  map = calloc (2u * vars + 1, sizeof *map);
  if (!map)
    out_of_memory ();
  map += vars;

  mark = calloc ((vars + 1u), sizeof *mark);
  if (!mark)
    out_of_memory ();

  clausal = calloc ((vars + 1u), sizeof *mark);
  if (!clausal)
    out_of_memory ();

  int lit = 0, parsed = 0;
  while (fscanf (input_file, "%d", &lit) == 1)
    {
      if (lit == INT_MIN || abs (lit) > vars)
	die ("invalid literal '%d'", lit);
      if (parsed == original)
	die ("too many clauses");
      if (lit)
	PUSH (literals, lit);
      else
	{
	  parsed++;
	  size_t size = SIZE (literals);
	  struct constraint *c = new_clause (size, literals.begin);
	  connect_constraint (c);
	  PUSH (clauses, c);
	  CLEAR (literals);
	}
    }
  if (lit)
    die ("zero missing");
  if (parsed != original)
    die ("clause missing");
  if (close_input == 1)
    fclose (input_file);
  if (close_input == 2)
    pclose (input_file);
  msg ("parsed %d clauses in %.2f seconds", parsed, stop ());
}

static bool
parity_of_word (unsigned signs)
{
  return __builtin_popcount (signs) & 1;
}

static void
mark_garbage (struct constraint * c)
{
  assert (!c->garbage);
  c->garbage = true;
  if (c->xor)
    return;
  assert (kept > 0);
  kept--;
}

static void
weaken_constraint (struct constraint * c)
{
  assert (c->size > 0);
  mark_garbage (c);
  if (!extend_file)
    return;
  fputc (c->xor ? 'x' : 'o', extend_file);
  fputc (' ', extend_file);
  if (c->xor && !c->parity)
    fputc ('-', extend_file);
  for (all_literals_in_constraint (lit, c))
    fprintf (extend_file, "%d ", lit);
  fputs ("0\n", extend_file);
}

static void
make_pivot_first_literal (struct constraint * c, int pivot)
{
  int * begin = c->literals;
#ifndef NDEBUG
  const int * end = begin + c->size;
#endif
  int * p =  begin;
  while (assert (p != end), *p != pivot)
    p++;
  if (p == begin)
    return;
  *p = begin[0];
  begin[0] = pivot;
}

static void
collect_constraint (struct constraint * c, int pivot)
{
  PUSH (collect, c);
}

static void
extract_direct_encoding_from_base_clause (struct constraint *c)
{
  assert (!c->xor);
  if (c->garbage)
    return;
  int size = c->size;
  if (size < 2)
    return;
  if (size > 29)
    return;
  bool failed = false;
  unsigned positive = 0;
  int required = 1 << (size - 2);
  assert (EMPTY (literals));
  assert (EMPTY (collect));
  for (all_literals_in_constraint (lit, c))
    {
      if (positive && lit > 0)
	failed = true;
      else
	{
	  int idx = abs (lit);
	  if (mark[idx])
	    failed = true;
	  else if (SIZE (occs[lit]) < required)
	    failed = true;
	  else if (SIZE (occs[-lit]) < required)
	    failed = true;
	  else
	    {
	      PUSH (literals, idx);
	      mark[idx] = 1;
	      if (lit > 0)
		positive++;
	    }
	}
      if (failed)
	break;
    }
  if (!failed)
    {
#ifdef LOGGING
      printf ("c LOG potential base size %d clause", size);
      for (all_literals_in_constraint (lit, c))
	printf (" %d", lit);
      printf ("\n");
#endif
      unsigned signs = positive;
      do
	{
	  unsigned bit = 1;
	  int min_lit = 0;
	  int min_lit_occs = INT_MAX;
	  for (all_stack (int, idx, literals))
	    {
	      int sign = (signs & bit) ? 1 : -1;
	      int lit = sign * idx;
	      int lit_occs = SIZE (occs[lit]);
	      if (lit_occs < min_lit_occs)
		{
		  min_lit = lit;
		  min_lit_occs = lit_occs;
		}
	      mark[idx] = sign;
	      bit <<= 1;
	    }
	  assert (min_lit);
	  assert (min_lit_occs < INT_MAX);
	  assert (required <= min_lit_occs);

	  bool found = false;
	  for (all_constraints (d, occs[min_lit]))
	    {
	      if (d->size != size)
		continue;
	      found = true;
	      for (all_literals_in_constraint (lit, d))
		{
		  int idx = abs (lit);
		  int tmp = mark[idx];
		  if (!tmp || (tmp > 0) != (lit > 0))
		    {
		      found = false;
		      break;
		    }
		}
	      if (found)
		{
#ifdef LOGGING
		  printf ("c LOG matching size %d clause", size);
		  for (all_literals_in_constraint (lit, d))
		    printf (" %d", lit);
		  printf ("\n");
		  fflush (stdout);
#endif
		  collect_constraint (d, min_lit);
		  break;
		}
	    }
	  if (!found)
	    {
#ifdef LOGGING
	      printf ("c LOG did not find matching size %d clause", size);
	      for (all_stack (int, idx, literals))
		{
		  int sign = (signs & bit) ? 1 : -1;
		  int lit = sign * idx;
		  printf (" %d", lit);
		}
	      printf ("\n");
	      fflush (stdout);
#endif
	      failed = true;
	      break;
	    }

	  do
	    signs++;
	  while (parity_of_word (signs) != positive);
	}
      while (!failed && signs < (1 << size));
    }
  if (!failed)
    {
      const bool parity = !positive ^ (size & 1);
      struct constraint *x = new_xor (parity, size, literals.begin);
      LOGXOR (x, "new");
      PUSH (xors, x);
      extracted++;
      if (size == 2)
	equivalences++;
      direct++;
      assert (SIZE (collect) == (1 << (size - 1)));
      for (all_constraints (d, collect))
	if (!d->garbage)
	  mark_garbage (d);
    }
  for (all_stack (int, idx, literals))
      mark[idx] = 0;
  CLEAR (literals);
  CLEAR (collect);
}

static bool
find_binary (int a, int b)
{
  for (all_constraints (c, occs[a]))
    {
      assert (!c->xor);
      if (c->garbage)
	continue;
      if (c->size != 2)
	continue;
      int *lits = c->literals;
      if (lits[0] != b && lits[1] != b)
	continue;
      collect_constraint (c, a);
      return true;
    }
  return false;
}

static bool
find_implications (int lhs, int rhs0, int rhs1)
{
  if (SIZE (occs[rhs0]) > SIZE (occs[rhs1]))
    SWAP (rhs0, rhs1);
  if (!find_binary (-lhs, rhs0))
    return false;
  if (!find_binary (-lhs, rhs1))
    {
      (void) POP (collect);
      return false;
    }
  return true;
}

static bool
find_ternary (int a, int b, int c)
{
  for (all_constraints (d, occs[a]))
    {
      if (d->garbage)
	continue;
      if (d->size != 3)
	continue;
      int *lits = d->literals;
      if ((lits[0] == b || lits[1] == b || lits[2] == b) &&
	  (lits[0] == c || lits[1] == c || lits[2] == c))
	{
	  collect_constraint (d, a);
	  return true;
	}
    }
  return false;
}

static bool
find_and_gate (int a, int b, int c)
{
  if (!find_ternary (a, -b, -c))
    return false;
  if (find_implications (a, b, c))
    return true;
  (void) POP (collect);
  return false;
}

static int gate[3];

static bool
find_xor_gate (int lhs, int rhs0, int rhs1)
{
  if (!find_binary (-lhs, rhs0))
    return false;
  if (!find_binary (-lhs, rhs1))
    return false;
  for (all_constraints (c, occs[-rhs0]))
    {
      assert (!c->xor);
      if (c->garbage)
	continue;
      if (c->size != 3)
	continue;
      int saved = SIZE (collect);
      int *lits = c->literals;
      if (-rhs0 == lits[0] &&
	  find_implications (-rhs0, -lits[1], -lits[2]) &&
	  find_and_gate (-rhs1, lits[1], lits[2]))
	{
	  gate[0] = lhs;
	  gate[1] = rhs0;
	  gate[2] = rhs1;
	  PUSH (literals, -lits[1]);
	  PUSH (literals, -lits[2]);
	  collect_constraint (c, -rhs0);
	  return true;
	}
      RESET (collect, saved);
    }
  CLEAR (collect);
  return false;
}

static void
extract_aig_encoding_from_base_clause (struct constraint *c)
{
  assert (!c->xor);
  if (c->garbage)
    return;
  if (c->size != 3)
    return;
  int *lits = c->literals;
  if (find_xor_gate (lits[0], -lits[1], -lits[2]) ||
      find_xor_gate (lits[1], -lits[0], -lits[2]) ||
      find_xor_gate (lits[2], -lits[0], -lits[1]))
    {
      LOG ("matched AND gate base clause %d %d %d",
	   lits[0], lits[1], lits[2]);
      LOG ("top AND gate %d = %d & %d", gate[0], gate[1], gate[2]);
      LOG ("2nd AND gate %d = %d & %d",
	   -gate[1], literals.begin[0], literals.begin[1]);
      LOG ("3rd AND gate %d = %d & %d",
	   -gate[2], -literals.begin[0], -literals.begin[1]);
      LOG ("found XOR gate %d = %d ^ %d",
	   gate[0], literals.begin[0], literals.begin[1]);
      if (SIZE (occs[gate[1]]) != 3)
	LOG ("too many occurrences of %d", gate[1]);
      else if (SIZE (occs[-gate[1]]) != 2)
	LOG ("too many occurrences of %d", -gate[1]);
      else if (SIZE (occs[gate[2]]) != 3)
	LOG ("too many occurrences of %d", gate[2]);
      else if (SIZE (occs[-gate[2]]) != 2)
	LOG ("too many occurrences of %d", -gate[2]);
      else
	{
	  LOG ("eliminating AND gate %d = %d & %d",
	       -gate[1], literals.begin[0], literals.begin[1]);
	  LOG ("eliminating AND gate %d = %d & %d",
	       -gate[2], -literals.begin[0], -literals.begin[1]);
	  collect_constraint (c, gate[0]);
	  PUSH (literals, gate[0]);
	  assert (SIZE (collect) == 9);
	  assert (SIZE (literals) == 3);
	  bool parity = 0;
	  lits = literals.begin;
	  SWAP (lits[0], lits[2]);
	  SWAP (lits[1], lits[2]);
	  for (int i = 0; i < 3; i++)
	    {
	      int lit = lits[i];
	      if (lit < 0)
		{
		  lits[i] = -lit;
		  parity = !parity;
		}
	    }
	  struct constraint *x = new_xor (parity, 3, lits);
	  LOGXOR (x, "new");
	  PUSH (xors, x);
	  extracted++;
	  gates++;
	  assert (SIZE (collect) == 9);
	  {
	    struct constraint ** cs = collect.begin;
	    weaken_constraint (cs[7]);
	    weaken_constraint (cs[2]);
	    weaken_constraint (cs[3]);
	    weaken_constraint (cs[4]);
	    weaken_constraint (cs[5]);
	    weaken_constraint (cs[6]);
	    mark_garbage (cs[0]);
	    mark_garbage (cs[1]);
	    mark_garbage (cs[8]);
	  }
	}
    }
  CLEAR (collect);
  CLEAR (literals);
}

static void
extract (void)
{
  start ();
  kept = SIZE (clauses);

  for (all_constraints (c, clauses))
    extract_direct_encoding_from_base_clause (c);
  msg ("found %d directly encoded XORs", direct);

  if (extract_gates)
    {
      for (all_constraints (c, clauses))
	extract_aig_encoding_from_base_clause (c);
      msg ("found %d gate encoded XORs", gates);
    }

  msg ("kept %d clauses %.0f%%", kept, percent (kept, original));
  msg ("XORs/variable %.0f%%", percent (extracted, vars));
  msg ("extracted %d XORs in %.2f seconds", extracted, stop ());
  msg ("including %d equivalences (binary XORs) %.0f%%",
       equivalences, percent (equivalences, extracted));
}

static int
cmp_occs (const void * p, const void * q)
{
  const int a = * (int*) p, b = * (int *) q;
  int res = SIZE (occs[b]) - SIZE (occs[a]);
  if (res)
    return res;
  return b - a;
}

static void
sort_schedule (void)
{
  qsort (schedule.begin, SIZE (schedule), sizeof (int), cmp_occs);
}

static void
substitute (int pivot, struct constraint * c, struct constraint * d)
{
  LOGXOR (c, "substituting");
  LOGXOR (d, "substituted");

  for (all_literals_in_constraint (idx, c))
    {
      assert (!mark [idx]);
      mark[idx] = 1;
    }

  for (all_literals_in_constraint (idx, d))
    mark[idx]++;

  assert (EMPTY (literals));
  assert (mark[pivot] == 2);

  for (all_literals_in_constraint (idx, c))
    if (mark[idx] == 1)
      PUSH (literals, idx);
    else
      assert (mark[idx] == 2);

  for (all_literals_in_constraint (idx, d))
    if (mark[idx] == 1)
      PUSH (literals, idx);
    else
      assert (mark[idx] == 2);

  {
    const bool parity = c->parity ^ d->parity;
    const int size = SIZE (literals);
    if (size > 0)
      {
	struct constraint *x = new_xor (parity, size, literals.begin);
	LOGXOR (x, "new");
	PUSH (xors, x);
	connect_constraint (x);
      }
    else if (parity)
      {
	assert (!inconsistent);
	inconsistent = true;
	msg ("derived inconsistent XOR constraint");
      }
    else
      LOG ("substitution yields trivial XOR constraints");
    CLEAR (literals);
  }

  for (all_literals_in_constraint (idx, c))
    mark[idx] = 0;
  for (all_literals_in_constraint (idx, d))
    mark[idx] = 0;

  LOGXOR (d, "disconnecting");
  disconnect_constraint (d, pivot);

  make_pivot_first_literal (d, pivot);
  weaken_constraint (d);
}

static void
eliminate_variable (int pivot)
{
  assert (!clausal[pivot]);

  struct constraints * cs = occs + pivot;
  if (EMPTY (*cs))
    return;

  LOG ("eliminating variable %d with %d occurrences", pivot, SIZE (*cs));
  eliminated++;

  struct constraint * c = 0;
  for (all_constraints (d, *cs))
    if (!c || c->size > d->size)
      c = d;
  assert (c);

  for (all_constraints (d, *cs))
    if (!inconsistent && c != d)
      substitute (pivot, c, d);

  disconnect_constraint (c, pivot);

  make_pivot_first_literal (c, pivot);
  weaken_constraint (c);

  substituted++;

  CLEAR (*cs);
}

static void
eliminate (void)
{
  start ();

  for (all_literals (lit))
    CLEAR (occs[lit]);

  for (all_constraints (c, clauses))
    if (!c->garbage)
      for (all_literals_in_constraint (lit, c))
	clausal[abs (lit)] = 1;

  for (all_constraints (c, xors))
    {
      assert (!c->garbage);
      for (all_literals_in_constraint (lit, c))
	PUSH (occs[abs (lit)], c);
    }

  for (all_variables (idx))
    if (!clausal[idx] && !EMPTY (occs[idx]))
      {
	LOG ("scheduling %d with %d occurrences", idx, SIZE (occs[idx]));
	PUSH (schedule, idx);
      }

  msg ("scheduled %d variable elimination candidates", SIZE (schedule));
  sort_schedule ();

  while (!EMPTY (schedule))
    eliminate_variable (POP (schedule));

  if (trivial)
    msg ("substitution yielded %d trivial XORs", trivial);

  msg ("eliminated %d variables in %.2f seconds", eliminated, stop ());
}

static void
compact (void)
{
  if (compact_variables)
    {
      for (all_variables (idx))
	assert (!mark[idx]);

      for (all_constraints (c, clauses))
	if (!c->garbage)
	  for (all_literals_in_constraint (lit, c))
	    mark[abs (lit)] = 1;

      for (all_constraints (c, xors))
	if (!c->garbage)
	  for (all_literals_in_constraint (lit, c))
	    mark[abs (lit)] = 1;

      for (all_variables (idx))
	if (mark[idx])
	  {
	    if (++reduced != idx)
	      {
		mapped++;
		LOG ("mapping original variable %d to %d", idx, reduced);
		if (extend_file)
		  fprintf (extend_file, "x -%d %d 0\n", idx, reduced);
	      }
	    map[idx] = reduced;
	    map[-idx] = -reduced;
	  }

      msg ("reduced %d original variables to %d variables %.0f%%",
	   vars, reduced, percent (reduced, vars));
      msg ("mapped %d variables of %d remaining variables %.0f%%",
	   mapped, reduced, percent (mapped, reduced));
    }
  else
    {
      msg ("keeping original variable indices");
      for (all_variables (idx))
	map[idx] = ++reduced, map[-idx] = -reduced;
    }
}

static const char *
header (void)
{
  static char buffer[80];
  sprintf (buffer, "p %cnf %d %d",
	   extracted ? 'x' : 'c', reduced,
	   kept + extracted - substituted - trivial);
  return buffer;
}

static void
write (void)
{
  start ();

  msg ("writing %cNF to '%s'", extracted ? 'X' : 'C', output_path);

  int wrote = 0;

  if (inconsistent)
    {
      msg ("writing 'p cnf 0 1' header");
      fputs ("p cnf 0 1\n0\n", output_file);
      wrote = 1;
    }
  else
    {
      const char * h = header ();
      msg ("writing '%s' header", h);
      fputs (h, output_file);
      fputc ('\n', output_file);

      for (all_constraints (c, clauses))
	if (!c->garbage)
	  {
	    assert (!c->xor);
	    for (all_literals_in_constraint (lit, c))
	      fprintf (output_file, "%d ", map[lit]);
	    fputs ("0\n", output_file);
	    wrote++;
	  }

      for (all_constraints (c, xors))
	if (!c->garbage)
	  {
	    assert (c->xor);
	    fputs ("x ", output_file);
	    if (!c->parity)
	      fputc ('-', output_file);
	    for (all_literals_in_constraint (lit, c))
	      fprintf (output_file, "%d ", map[lit]);
	    fputs ("0\n", output_file);
	    wrote++;
	  }
    }

  if (close_output == 1)
    fclose (output_file);
  if (close_output == 2)
    pclose (output_file);

  msg ("wrote %d constraints in %.02f seconds", wrote, stop ());
}

static void
release_constraints (struct constraints *cs)
{
  for (all_constraints (c, *cs))
    free (c);
  free (cs->begin);
}

static void
reset (void)
{
  free (literals.begin);
  free (collect.begin);
  free (schedule.begin);

  for (all_literals (lit))
    free (occs[lit].begin);
  occs -= vars;
  free (occs);

  map -= vars;
  free (map);

  free (mark);
  free (clausal);

  release_constraints (&clauses);
  release_constraints (&xors);
}

static bool
has_suffix (const char *str, const char *suffix)
{
  const size_t l = strlen (str), k = strlen (suffix);
  return l >= k && !strcmp (str + l - k, suffix);
}

static void
read_pipe (const char *fmt)
{
  char *cmd = malloc (strlen (fmt) + strlen (input_path));
  if (!cmd)
    out_of_memory ();
  sprintf (cmd, fmt, input_path);
  input_file = popen (cmd, "r");
  close_input = 2;
  free (cmd);
}

static FILE *
write_pipe (const char *fmt)
{
  char *cmd = malloc (strlen (fmt) + strlen (output_path));
  if (!cmd)
    out_of_memory ();
  sprintf (cmd, fmt, output_path);
  FILE * file = popen (cmd, "w");
  free (cmd);
  return file;
}

int
main (int argc, char **argv)
{
  for (int i = 1; i < argc; i++)
    {
      const char *arg = argv[i];
      if (!strcmp (arg, "--version"))
	fputs (VERSION "\n", stdout), exit (0);
      else if (!strcmp (arg, "-h") || !strcmp (arg, "--help"))
	fputs (usage, stdout), exit (0);
#ifndef LOGGING
      else if (!strcmp (arg, "-q") || !strcmp (arg, "--quiet"))
	quiet = true;
#endif
      else if (!strcmp (arg, "-n") || !strcmp (arg, "--no-write"))
	do_not_write_output = arg;
      else if (!strcmp (arg, "--no-gates"))
	extract_gates = false;
      else if (!strcmp (arg, "--no-eliminate"))
	eliminate_xors = false;
      else if (!strcmp (arg, "--no-compact"))
	compact_variables = false;
      else if (arg[0] == '-' && arg[1])
	die ("invalid option '%s' (try '-h')", arg);
      else if (extend_path)
	die ("too many files '%s', '%s' and '%s'",
	     input_path, output_path, arg);
      else if (output_path)
        extend_path = arg;
      else if (input_path)
	output_path = arg;
      else
	input_path = arg;
    }

  if (output_path && do_not_write_output)
    die ("can not use '%s' with output file '%s'",
	 do_not_write_output, output_path);

  if (input_path && output_path &&
      !strcmp (input_path, output_path) && strcmp (input_path, "-"))
    die ("identical input and output path '%s'", input_path);
  if (input_path && extend_path &&
      !strcmp (input_path, extend_path))
    die ("identical input and extension path '%s'", input_path);
  if (output_path && extend_path &&
      !strcmp (output_path, extend_path))
    die ("identical output and extension path '%s'", output_path);

  if (!input_path || !strcmp (input_path, "-"))
    input_path = "<stdin>", input_file = stdin, close_input = 0;
  else if (has_suffix (input_path, ".gz"))
    read_pipe ("gzip -c -d %s");
  else if (has_suffix (input_path, ".bz2"))
    read_pipe ("bzip2 -c -d %s");
  else if (has_suffix (input_path, ".xz"))
    read_pipe ("xz -c -d %s");
  else
    input_file = fopen (input_path, "r"), close_input = 1;
  if (!input_file)
    die ("can not read '%s'", input_path);

  msg ("CNF2XNF XOR Extractor Version " VERSION);

  parse ();

  if (extend_path)
    {
      if (!strcmp (extend_path, "-"))
	extend_path = "<stdout>", extend_file = stdout, close_extend = 0;
      else if (has_suffix (extend_path, ".gz"))
	extend_file = write_pipe ("gzip -c > %s"), close_extend = 2;
      else if (has_suffix (extend_path, ".bz2"))
	extend_file = write_pipe ("bzip2 -c > %s"), close_extend = 2;
      else if (has_suffix (extend_path, ".xz"))
	extend_file = write_pipe ("xz -c > %s"), close_extend = 2;
      else
	extend_file = fopen (extend_path, "w"), close_extend = 1;
      if (!extend_file)
	die ("can not write '%s'", extend_path);

      msg ("writing extension stack to '%s'", extend_path);
    }

  extract ();
  if (eliminate_xors && extracted)
    eliminate ();

  compact ();

  if (extend_file)
    {
      if (close_extend == 1)
	fclose (extend_file);
      if (close_extend == 2)
	pclose (extend_file);

      msg ("closed extension file '%s'", extend_path);
    }

  if (!do_not_write_output)
    {
      if (!output_path || !strcmp (output_path, "-"))
	output_path = "<stdout>", output_file = stdout, close_output = 0;
      else if (has_suffix (output_path, ".gz"))
	output_file = write_pipe ("gzip -c > %s"), close_output = 2;
      else if (has_suffix (output_path, ".bz2"))
	output_file = write_pipe ("bzip2 -c > %s"), close_output = 2;
      else if (has_suffix (output_path, ".xz"))
	output_file = write_pipe ("xz -c > %s"), close_output = 2;
      else
	output_file = fopen (output_path, "w"), close_output = 1;
      if (!output_file)
	die ("can not write '%s'", output_path);

      write ();
    }
  else if (!inconsistent)
    msg ("would write '%s'", header ());

  reset ();

  msg ("total running time of %.2f seconds", timevoid ());

  return 0;
}
