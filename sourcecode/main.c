/* The GOVOL LISP Interpreter  as described in the book
   Interpreting LISP by Gary D. Knott
   Along with the exercises that modify the textbook
   implementation Also, all the needlessly lengthy comments
   are written with the aim to make this adventure in implementing
   my first C implementation of LISP more understandable
   and useful for myself.
*/
#include "linuxenv.h"

#define int16 int16_t
#define int32 int32_t

#define NULL 0L
#define EOF  (-1)
#define EOS  (0)

#define EQ ==
/* The interpreter code in the book uses the following
   "helper definitions":
#define EQ ==
#define OR ||
#define AND &&
#define NOT !
   EQ is so useful for safety reasons that  it is the only one
   this version will use. Otherwise the philosophy here has been
   to stick to as "pure" C language as possible.
*/

#define n 1000  /* size of number table */
#define m 1000  /* size of atom table */
#define l 6000  /* size of list area */
/* In the book's interpreter code, atom table and number table are
   of equal size, and both thus use n to define their sizes.
   In this version the atom table and number table sizes are separated. */

jmp_buf env;    /* for handling errors, the top-level environment is stored here */
char *sout;     /* general output buffer pointer, used by swrite of the REPL */

/* The atom table:
    name   - the atom's name
    L      - the link to the (global) value of the atom
    bl     - the bind list link for the atom
    plist  - the property list link for the atom
*/
struct Atomtable {char name[16]; int32 L; int32 bl; int32 plist;} Atab[m];
/*
    In essence the interpreter uses shallow binding to resolve the most
    relevant binding for an atom: each atom has its own unique bind list bl,
    in contrast with deep binding where all the bound values for each
    atom appear in one single bind list. Shallow binding does require a
    bit more memory (each atom table node has to have an additional
    bind list link) but looking up atoms becomes faster in exchange since
    calculating a hash index for an atom is a relatively quick process.
*/

/* The number table:
    num     - the actual number, used only if the current node is used.
    nLink   - link to the next free number, used only if the current node is free.
*/
union Numbertabe {double num; int16 nlink;} Ntab[n];
/*
    Since Numbertable is a union, it can either store
    a number or a link to the next free Numbertable node
    but not both. So, either a Ntab cell belongs to the
    series of free Ntab nodes or it contains a number data.
*/

/* The number hash index table: */
int16 nx[n];
/*
    nx works as a hash table for stored numbers:
    For a number r, a hash(r) points to an index
    in nx. Ideally, then, nx[hash(r)] points
    to the index in Ntab where the number r is
    being stored, thus, either:
    r EQ Ntab[nx[hash(r)]]
    or then r isn't stored yet and can be stored in
    Ntab[nx[hash(r)]].

    Of course, since hashing from a limitless set
    to a very limited Ntab memory is, by default, an
    imprecise relation, "double" hits are bound to
    happen eventually, and r may not be found exactly
    at Ntab[nx[hash(r)]]. The LISP implementation
    promises to "pack" r as close to its hashing-index
    as possible, and it is the job of the garbage collector
    to make sure that it always stays as close to the hashing
    index as possible and no "holes in between" will occur.
*/

/* The number table free space list head pointer; */
int16 nf = -1;
/* nf holds the index of the first free
   number table node for whenever a new number
   needs to be stored into Ntab.
*/

/* EX 27.8 - nnum: The amount of numbers in the number table */
int16 nnums = 0;
/* helps to decide when to gc():
   we want the number table to be close to 80% full
   whenever possible since that will decrease the
   amount of hash collisions.

   the number table mark array: used in garbage collection
   to mark all the number table entries to be saved. */
char nmark[n];
/* It would be interesting and probably a good practice for embedded
   systems to try to create a truly 1-bit data type for each
   nmark entry.
*/

/* The list area */
struct Listarea {int32 car; int32 cdr;} *P;
/* each Listarea entry in P has two pointers:
   the first one, car, points to an arbitrary value
   (basically it can be an ordinary atom, a number atom,
    a function or another listarea entry in P).
    The cdr always points to either NIL or another
    Listarea entry.
*/

/* the list area free space list head pointer */
int16 fp = -1;

/* the put-back variable - needed for reading in user input */
int32 pb = 0;

/* the input string and related pointers */
char *g, *pg, *pge;

/* the input stream stack structure and head pointer */
struct Insave {struct Insave *link; char *pg, *pge; char g[202]; FILE *filep;};;
struct Insave *topInsave;

/* the input prompt character */
char prompt;

/* seval depth count and trace switch -
   used in traceprint. */
int16 ct=0, tracesw=0;

/* global ordinary atom typed pointers */
int32 nilptr, tptr, currentin, eaL, quoteptr, sk, traceptr;

/* number of free list-nodes */
int32 numf;

/* define global macros */
#define A(j)                P[j].car
#define B(j)                P[j].cdr
#define AL(j)               Atab[j].L
#define Abl(j)              Atab[j].bl

#define type(f)             (((f)>>28) & 0xf)
#define ptrv(f)             (0x0fffffff & (f))
#define sexp(t)             ((t) EQ 0 || (t) EQ 8 || (t) EQ 9)
#define fctform(t)          ((t)>9)
#define builtin(t)          ((t) EQ 10 || (t) EQ 11)
#define userdefd(t)         ((t) EQ 12 || (t) EQ 13)
#define dottedpair(t)       ((t) EQ 0)
#define fct(t)              ((t) EQ 10 || (t) EQ 12 || (t) EQ 14)
#define unnamedfsf(t)       ((t)>13)
#define namedfsf(t)         ((t)>9 && (t)<14)
#define tp(t,j)             ((t) | (j))
#define ud(j)               (0x10000000 | (j))
#define se(j)               (0x00000000 | (j))
#define oa(j)               (0x80000000 | (j))
#define nu(j)               (0x90000000 | (j))
#define bf(j)               (0xa0000000 | (j))
#define bs(j)               (0xb0000000 | (j))
#define uf(j)               (0xc0000000 | (j))
#define us(j)               (0xd0000000 | (j))
#define tf(j)               (0xe0000000 | (j))
#define ts(j)               (0xf0000000 | (j))
/* Every Govol LISP datatype-pointer is of the form:
        0xtppppppp
        where t stands for type and p stands for pointer
        So, an atom at atom table index 128 that points
        to itself will be:
        0x80000080
        (the type is 0x08 - ordinary atom
        and the value, 0x000080 - 128)
        The previous global macros help separate pointer
        types from their values and to check where a
        pointer is pointing at.
        A pointer's type can be one of the following:
        1  - undefined
        8  - variable (ordinary atom)
        9  - number (number atom)
        0  - dotted pair (non-atomic S-expression)
        10 - builtin function
        11 - builtin special form
        12 - user-defined function
        13 - user-defined special form
        14 - unnamed function
        15 - unnamed special form
*/

/* variables used in file operations */
FILE *filep;
FILE *logfilep;

int32 seval(int32 i);
void initlisp(void);
int32 sread(void);
void swrite(int32 i);
void check_arity(int32 p, uint8_t ar, int32 f); /* custom-made, to check the arity of builtin function applications */
int32 newloc(int32 x, int32 y);
int32 numatom(double r);
int32 ordatom(char *s);
void gc(void);
void gcmark(int32 p);
char getgchar(void);
char lookgchar(void);
void fillg(void);
int32 e(void);
void error(char *s);
int16 fgetline(char *s, int16 lim, FILE *stream);
void ourprint(char *s);

/* ============================================== */
void main(void)
/*----------------------------------------
  This is the main rea-eval-print loop
------------------------------------------*/
{
  initlisp();
  setjmp(env);

  for (;;) {
    ourprint("\n");
    prompt='*';
    swrite(seval(sread()));
  }
}

void error(char *msg)
/*---------------------------------------------------------------
  Type out the message in the string array msg and do a longjmp()
  to top level afterward to where setjmp was called.
---------------------------------------------------------------*/
{
    int32 i, t;

    /* discard all input S-expression and argument list stacks */
    Atab[currentin].L = nilptr;
    Atab[eaL].L       = nilptr;
    Atab[sk].L        = nilptr;
    /* reset all atoms to their top-level values */
    for (i=0; i<n; i++) {
        if ((t=Atab[i].bl) != nilptr) {
            while (t != nilptr) {
                t = B(t);
                Atab[i].L = A(t);
                Atab[i].bl = nilptr;
            }
        }
    }

    ct = 0;
    ourprint("::");
    ourprint(msg);
    ourprint("\n");
    longjmp(env, -1);
}/*
    For every atom in atom table, there exists a bind list that
    holds all the local bindings of the atom, in the proper order.
    When an error occurs, we have to traverse through all those atoms
    whose bind lists are not empty to set the L-value of the atom
    to the last binding in the bind listb- which
    will be the original global binding for the atom - as the global value
    of the atom.

    The current value of the atom (eg. Atab[45].L) will be
    the value of the latest binding for said atom.
        (check that this is true. It should be, because, if not, why even
         bother traversing through the bind list if the value Atab[i].L
         will always point to the global value of the atom stored at Atab[i]?
         Instead we could just set the bindlist of each Atab to nil,
         signal an error and let GC take care of the rest for us...)
*/

void ourprint(char *s) {
/*---------------------------------------------------------------
s: the message to be printed out and logged:
Print the string s in the log file and on the terminal.
---------------------------------------------------------------*/
    printf("%s", s);
    fprintf(logfilep, "%s", s);
    fflush(logfilep);
}

void initlisp(void)
/*---------------------------------------------------------------
  This procedure installs all built-in functions and special
  forms into the atom table. It also initializes the number table
  and the list area
---------------------------------------------------------------*/
{
    int32 i;

    static char *BI[] =
       {"CAR", "CDR", "CONS", "LAMBDA", "SPECIAL", "SETQ", "ATOM", "NUMBERP", "QUOTE",
        "LIST", "DO", "COND", "PLUS", "TIMES", "DIFFERENCE", "QUOTIENT", "POWER",
        "FLOOR", "MINUS", "LESSP", "GREATERP", "EVAL", "EQ", "AND", "OR", "SUM",
        "PRODUCT", "PUTPLIST", "GETPLIST", "READ", "PRINT", "PRINTCR", "MKATOM",
        "BODY", "RPLACA", "RPLACD", "TSETQ", "NULL", "SET", "EXIT"
       };

    static char BItype[] =
       { 10, 10, 10, 11, 11, 11, 10, 10, 11, 10,
         10, 11, 10, 10, 10, 10, 10, 10, 10, 10,
         10, 10, 10, 11, 11, 10, 10, 10, 10, 10,
         10, 10, 10, 10, 10, 10, 11, 10, 11, 11
       };

    /* number of built-ins in BI[~] and BItype[~] above */
    #define NBI 40

    /* allocate a global character array for messages: */
    sout=(char *)calloc(80, sizeof(char));

    /* allocate the input string */
    g = (char *)calloc(202, sizeof(char));

    /* allocate the list area */
    P = (struct Listarea *)calloc(l, sizeof(struct Listarea));

    /* initialize atom table names */
    for (i=0; i<m; i++)
         Atab[i].name[0] = '\0';

    /* initialize number table names */
    for (i=0; i<n; i++) {
         nmark[i] = 0;
         nx[i] = -1;
         Ntab[i].nlink = nf;
         nf = i;
    }

    /* install typed-case numbers for builtin functions
       and special forms into the atom table: */
    /*-------------------------------------------------
       for each new atom, ordatom creates new atom entry
       in the atomtable and returns a pointer to the
       entry. The value (link) of a newly created atom table
       entry is undefined. Therefore, we need to manually
       create a value for each built-in type. The value
       will be of the following form:
       t00000ii
       where t is either
       10 (builtin function) or
       11 (builtin special form)
       and 00000ii contains the order of the primitive
       as it appears in BI/BItype-tables.
    -------------------------------------------------*/
    for (i=0; i<NBI; i++) {
        Atab[ptrv(ordatom(BI[i]))].L = tp((((int32)BItype[i])<<28), (i+1));
    }

    /* NIL and T will point to themselves in the atom table,
       the value of QUOTE will be undefined: */
    nilptr = ordatom("NIL"); Atab[ptrv(nilptr)].L = nilptr;
    tptr = ordatom("T");     Atab[ptrv(tptr)].L = tptr;
    quoteptr = ordatom("QUOTE");

    /* Creating and using the list-valued atoms CURRENTIN, eaL, and sreadlist in the atom
       table is a means to ensure that we protect the list-nodes in these lists during garbage
       collection. We make these atom names lowercased to keep them private.*/
    currentin = ptrv(ordatom("currentin")); Atab[currentin].L = nilptr;
    eaL = ptrv(ordatom("eaL"));             Atab[eaL].L = nilptr;
    sk = ptrv(ordatom("sreadlist"));        Atab[sk].L = nilptr;

    #define cilp Atab[currentin].L
    #define eaLp Atab[eaL].L
    #define skp  Atab[sk].L

    /* initialize the bindlist (bl) and plist fields */
    for (i=0; i<m; i++)
        Atab[i].bl = Atab[i].plist = nilptr;

    /* set up the list area free space list */
    for (i=1; i<l; i++) {
        B(i) = fp;
        fp = i;
    }
    numf = l - 1;

    /* open the logfine */
    logfilep = fopen("lisp.log", "w");
    ourprint("ENTERING THE GOV LISP INTERPRETER\n");

    /* establish the input buffer g and the input stream stack topInsave and prepare to read-in
       predefined functions and special forms from the text file lispinit; these should include
       APPEND, REVERSE, EQUAL, APPLY, MEMBER, INTO, ONTO, NOT, ASSOC, NPROC, PUTPROP, GETPROP and
       REMPROP. */
    topInsave = NULL;
    strcpy(g, "@lispinit ");
    /* initialize start & end pointers to the string g: */
    pg = g;
    pge = g + strlen(g);
    filep = stdin;
}

int32 sread(void)
/*---------------------------------------------------------------------------------------------------------
  This procedure scans an input string g using a lexical token scanning routine, e(), where e() returns

    * 1 if the token is '('
    * 2 if the token is ''' (single quote)
    * 3 if the token is '.'
    * 4 if the token is ')'
    * or a typed pointer d to an atom or number stored in row ptrv(d) in the atom or number tables. Due
      to the typecode of d (8 or 9), d is a negative 32-bit integer. The token found by e() is stripped
      from the front of g.

  sread constructs an S-expression corresponding to the scanned input string and returns a typed-pointer
  to it as its result.

  There is occasion to "put back" open parentheses and single quote symbols onto g within sread. This is
  done by loading the global putback variable, pb, which is interrogated and reset as appropriate within E.
  ---------------------------------------------------------------------------------------------------------*/
{
    int32 j,k,t,c;

    if ((c=e())<= 0) return(c);
    /* skp is defined as Atab[sk].L */
    skp=newloc(nilptr, skp); /* push a new node on the skp list. */
    A(skp)=j=k=newloc(nilptr,nilptr);

    /* we will return k, but we will fill node j first. */
    if (c EQ 1)
    {
        scan:   A(j)=sread();   /* read in the first element of the list. */
        next:   if ((c=e())<=2)
                {
                    t=newloc(nilptr, nilptr);
                    B(j)=t;
                    j=t;
                    if (c<=0)
                    {
                        A(j)=c;
                        goto next;
                    }
                    pb=c;
                    goto scan;
                }

                if (c!=4)
                {
                    B(j)=sread();
                    if (e()!=4) error("syntax error");
                }

                skp=B(skp); /* pop the skp list. */
                return k;
    }
    if (c EQ 2)
    {
        A(j)=quoteptr;
        B(j)=t=newloc(nilptr, nilptr);
        A(t)=sread();
        skp=B(skp); /* pop the skp list. */
        return k;
    }
    error("bad syntax");
}

int32 e(void)
{
    double v,f,k,sign;
    int32 t,c;
    char nc[15], *np;
    struct Insave *tb;

    #define OPENP  '('
    #define CLOSEP ')'
    #define BLANK  ' '
    #define SINGLEQ '\''
    #define DOT     '.'
    #define PLUS    '+'
    #define MINUS   '-'
    #define CHVAL(c) (c-'0')
    #define DIGIT(c) ('0'<=(c) && (c)<= '9')
    #define TOUPPER(c) ((c) + 'A'-'a')
    #define ISLOWER(c)  ((c)>='a' && (c)<='z')

    /* if a token has been pushed back into the input,
       return the pushed back token. sread sometimes
       checks beforehand if a token following the
       current token is of "certain type". If it's

       not, sread commands e to push back the token
       to wait for it to be read properly. However
       the pushed-back token has, by then been transformed
       into a value that the sread recognizes and we
       can just return this value instead of having to
       compute it all over again: */
    if (pb!=0) {t=pb; pb=0; return(t);}

    start: while ((c=getgchar()) EQ BLANK);  /* remove all the blanks */

    if (c EQ OPENP)
    {
        while (lookgchar() EQ BLANK) getgchar();    /* remove all the blanks */
        if (lookgchar() EQ CLOSEP)
        {
            getgchar();                 // Answer to ex. 27.2: e() is responsible for recognizing NILs
            return nilptr;              // "()", "( )", "(  )" etc... are NILs and '(' with something other than
        }                               // ')'-character following it is the opening character for a non-NIL list.
        else return 1; // return 1 for the '(' token read.
    }
    if (c EQ EOS)
    {
        if (topInsave EQ NULL)
        {
            fclose(logfilep);
            exit(0);
        }
        /* restore the previous input stream. */
        fclose(filep);
        strcpy(g, topInsave->g);
        pg=topInsave->pg;
        pge=topInsave->pge;
        filep=topInsave->filep;
        topInsave=topInsave->link;
        if (prompt EQ '@') prompt='*';
        goto start;
    }
    if (c EQ SINGLEQ) return 2;
    if (c EQ CLOSEP)  return 4;
    if (c EQ DOT)
    { /* a DOT can appear either in a decimal number or as the DOTTED-LIST -marker */
        if (DIGIT(lookgchar()))
        {   /* Handle the decimal number case: */
            sign=1.0;
            v=0.0;
            goto fraction;
        }
        return 3;   /* return 3 for a DOTTED-LIST marker */
    }
    if (!(DIGIT(c) || ((c EQ PLUS || c EQ MINUS) &&                  /* if the token is not a number, it must be a symbol */
                       (DIGIT(lookgchar()) || lookgchar() EQ DOT))))
    {
        np=nc;
        *np++=c;    /* put c in nc[0] */
        for (c=lookgchar(); c != BLANK && c != DOT && c!= OPENP && c != CLOSEP; c=lookgchar())
            *np++ = getgchar(); /* add a character to nc */
        *np=EOS; /* nc is now a string */
        if (*nc EQ '@')
        { /* switch input streams: */
            /* first, save the current stream: */
            tb=(struct Insave *)calloc(1, sizeof(struct Insave));
            tb->link = topInsave;
            topInsave=tb;
            strcpy(tb->g, g);
            tb->pg=pg;
            tb->pge=pge;
            tb->filep=filep;

            /* set up the new input stream: */
            *g=EOS;
            pg=pge=g;
            prompt='@';
            filep=fopen(nc+1, "r"); /* skip over the @ */
            goto start;
        }
        /* convert the string nc to upper case */
        for (np=nc; *np!=EOS; np++)
            if (ISLOWER((int16)*np)) *np=(char)TOUPPER((int16)*np);
        return(ordatom(nc));
    }
    if (c EQ MINUS)
    {
        v=0.0;
        sign=-1.0;
    }
    else
    {
        v=CHVAL(c);
        sign=1.0;
    }
    while (DIGIT(lookgchar())) v=10.0*v+CHVAL(getgchar());
    if (lookgchar() EQ DOT)
    {
        getgchar();
        if (DIGIT(lookgchar()))
        {fraction:
            k=1.0;
            f=0.0;
            do
            {
                k=10.*k;
                f=10.*f+CHVAL(getgchar());
            } while (DIGIT(lookgchar()));
            v=v+f/k;
        }
    }
    return numatom(sign*v);
}

char getgchar(void)
/* get a character from g. */
{
    fillg();
    return (*pg++);
}

char lookgchar(void)
/* Look at the next character in g, but do not advance. */
{
    fillg();
    return (*pg);
}

void fillg(void)
/* read a line into g[]. A line starting with a "/" is a comment line to be discarded. */
{
    while (pg >= pge)
    {
    sprompt:
        if (filep EQ stdin)
        {
            sprintf(sout, "%c", prompt);
            ourprint(sout);
        }

        if (fgetline(g, 200, filep)<0)
        {
            *g = '\0';
            pg  = g;
            pge = g;
            return;
        }
        if (filep EQ stdin)
        {
            fprintf(logfilep, "%s\n", g);
            fflush(logfilep);
        }
        if (*g EQ '/') goto sprompt;

        pg=g;
        pge=g+strlen(g);
        *pge++=' ';
        *pge='\0';
        prompt='>';
    }
}

int16 fgetline(char *s, int16 lim, FILE *stream)
/*-------------------------------------------------
fgetline() gets a line (CRLF or just LF delimited) from stream and puts it into the string array
(i.e., the buffer) s (up to lim chars). The function returns the length of this string. If there
are no characters but just EOF, it returns -1 (EOF) as the length. There is no deblanking except
to drop any CRs, and if present, the LF(\n). TABS are mapped to blanks.

Note when the file being read is stdin,  an EOF will never be encountered, instead fgetc will
wait until a complete line is typed, and then return the net character of that line until all
the characters of that line have been consumed, whereupon fgetc blocks again, waiting for the
next line.
-------------------------------------------------*/
{
    int16 c, i;
    #define TAB 9

    for (i=0; i<lim && (c=fgetc(stream))!=EOF && c!='\n'; i++)
    {
        if (c EQ TAB) c=BLANK;
        s[i]=c;
    }
    s[i]='\0';

    if (c EQ EOF && i EQ 0)
        return -1;
    else
        return i;
}

int32 numatom(double r)
/*-------------------------------------------------
The number r atom is looked up in the number table
and stored there as a lazy number atom if it is not
already present. The typed-pointer to this number
atom is returned.
-------------------------------------------------*/
{
    int32 c, j;

    /* The hashnum is calculated from the last 4 bytes of the
       number r, scaled down to 0...n-1, to fit an index in
       number table
    */
    #define hashnum(r) ((*(1+(int32 *) (&r)) & 0x7fffffff) % n)
    c=j=hashnum(r);

	/* EX 27.8 - gc() whenever the number table grows too bit
	   (80% or more of the maximum size), a new vatiable for
	   remembering the amount of numbers in the number table
	   was added to make this possible. */
	if (nnums >= 0.8*n)
		gc();
	/* find either r or the first free index to store r in: */
	while (nx[j] != -1)
	{
		if (Ntab[nx[j]].num EQ r) {
			j = nx[j];
			goto ret;
		}
		else if (++j EQ n) j=0;

		if (j EQ c)
		{ /* The number table is full, the number wasn't found
		    in the number table and garbage colleciton has already
		    been performed - signal an error: */
            error("The number table is full");
		}
	}

    /* Here nx[j] = -1; get an Ntab node to store a new number in. */
    /* Set up the new Ntab entry: */
	nnums += 1;
    nx[j] = nf; // the new node will be stored in Ntab[nf]
    j = nf;
    nf = Ntab[nf].nlink; // set nf to point to the next free number.
    Ntab[j].num = r;
ret: return(nu(j));
}

int32 ordatom(char *s)
/*-------------------------------------------------
The ordinary atom whose name is given as the
argument string s is looked up in the atom table
and stored there as an atom with the value undefined
if it is not already present. The typed-pointer to
this ordinary atom is then returned.
-------------------------------------------------*/
{
    int32 j, c;
    /* The hashname is calculated from the first, the last character and
       the amount of characters in the atom's symbol and scaled down to
       fit an index of 0...m-1 */
    #define hashname(s) (labs((s[0]<<16)+(s[(j=strlen(s))-1]<<8)+j) % m)
    c=j=hashname(s);

    while (Atab[j].name[0] != EOS) {
        if (strcmp(Atab[j].name, s) EQ 0) goto ret;
        else if (++j EQ n)
            j = 0;

        if (j EQ c) error("atom table is full");
    }

    strcpy(Atab[j].name, s);
    Atab[j].L = ud(j);
ret: return(oa(j));
}

void swrite(int32 j)
/*-------------------------------------------------
  swrite handles the PRINT-phase of the GOVOL LISP
  READ-EVAL-PRINT loop.
-------------------------------------------------*/
{
    int32 i;
    int16 listsw;

    i=ptrv(j);
    switch(type(j))
    {
        case 0: /* check for a list */
            j=i;
            while (type(B(j)) EQ 0) j=B(j);
            listsw=(B(j) EQ nilptr);
            ourprint("(");
            while (listsw)
            {
                swrite(A(i));
                if ((i=B(i)) EQ nilptr) goto close; else ourprint(" ");
            }
            swrite(A(i)); ourprint(" . "); swrite(B(i));
close:      ourprint(")");
            break;

        case  8: ourprint(Atab[i].name); break;
        case  9: sprintf(sout, "%-g", Ntab[i].num); ourprint(sout); break;
        case 10: sprintf(sout, "{builtin function: %s}", Atab[i].name);
                 ourprint(sout); break;
        case 11: sprintf(sout, "{builtin special form: %s}", Atab[i].name);
                 ourprint(sout); break;
        case 12: sprintf(sout, "{user define function: %s}", Atab[i].name);
                 ourprint(sout); break;
        case 13: sprintf(sout, "{user defined special form: %s}", Atab[i].name);
                 ourprint(sout); break;
        case 14: ourprint("{unnamed function}"); break;
        case 15: ourprint("{unnamed special form}"); break;
    }
    /* There's naturally no need for case 1 check, because seval would have already
       signaled an error if we tried to print the value of an undefined variable. */
}


void traceprint(int32 v, int16 osw)
/*-------------------------------------------------
  v: the object to be printed
  osw: 1 for seval() output, 0 for seval() input
  ----------------------------------------------
  This function prints out the input and the result
  for each successive invocation of seval() when
    tracing is requested.
-------------------------------------------------*/
{
    if (tracesw > 0)
    {
        if (osw EQ 1)
            sprintf(sout, "%d result:", ct--);
        else
            sprintf(sout, "%d eval:", ++ct);
    }
}

int32 seval(int32 p)
/*-------------------------------------------------
Evaluate the S-expression pointed to by the
typed-pointer p; construct the result value as
necessary; return a typed-pointer to the result.
-------------------------------------------------*/
{
    int32 ty, t, v, f, fa, na, ar_ef;
    int32 *endeaL;
    static int32 j;
    static double s;

    #define U1 A(p)
    #define U2 A(B(p))
    #define E1 A(p)
    #define E2 A(B(p))
    #define Return(v) {traceprint(v,1); return(v);}

    traceprint(p, 0);

    if (type(p)!=0)
    { /* p does not point to a non-atomic S-expression.

        if p is a type-8 typed pointer to an ordinary atom whose value is a built-in or user-defined
        function or special form, then a typed pointer to that atom-table entry with typecode 10, 11,
        12, or 13, depending upon the value of the atom, is returned. This permits us to know the
        names of functions and special forms.

        If p is a type-8 typed-pointer to an ordinary atom whose value is not a built-in or user-defined
        function or special form, and thus has the typecode 8, 9, 14, or 15, then a typed-pointer
        corresponding to the value of this atom is returned.

        If p is a non-type-8 typed-pointer to a number atom or to a function or special form
        (named or unnamed), then the same pointer p is returned. */

        if ((t=type(p))!=8)
            Return(p);

        j=ptrv(p);

        /* The association list is implemented with shallow binding in the atom table, so  the current
           values of all atoms are found in the atom table. */

        if (Atab[j].name[0] EQ '!')
        {   /* "!TRACE" sets the traces, "![anything else]" unsets it. Afterwards, the control will be
               directed back at the top of evaluation. */
            tracesw=(strcmp(Atab[j].name, "!TRACE") EQ 0)? 1 : 0;
            longjmp(env, -1);
        }

        if ((t=type(Atab[j].L)) EQ 1)
        {   /* The capture of undefined variables: */
            sprintf(sout, "%s is undefined\n", Atab[j].name);
            error(sout);
        }

        if (namedfsf(t)) Return(tp(t<<28, j));

        return Atab[j].L;
    } /* end of if (type(p)!=0) */

    /* save the list p consisting of the current function and the supplied arguments as the top
       value of the currentin list of lists to protect it from garbage collection. The current list
       is a list of lists. (cilp is defined as Atab[currentin].L) */
    cilp=newloc(p, cilp);

    /* compute the function or special form to be applied: */
    tracesw--;
    ar_ef=A(p); /* get the builtin function's or special form's atom into ar_ef for arity checking */
    f=seval(A(p)); tracesw++; ty=type(f);
    if (!fctform(ty)) error(" invalid function or special form");
    f=ptrv(f);
    if (!unnamedfsf(ty)) f=ptrv(Atab[f].L);

    /* now let go of the supplied input function */
    A(cilp)=p=B(p);

    /* If f is a function (not a special form), build a new list of its evaluated arguments and add
       it to the eaL list of lists. Then let go of the list of supplied arguments, replacing it with
       the new list of evaluated arguments. */
    if (fct(ty))
    { /* Compute the actual arguments */
      /* First, make room for the values of the arguments in eaL: */
        eaLp=newloc(nilptr, eaLp);
      /* Then, evaluate the actual arguments and build a list by tail-consing: */
        endeaL=&A(eaLp);
        while (p != nilptr)
        {
            /* Evaluate an argument and reserve a new cell to the end of eaL for it. */
            *endeaL=newloc(seval(A(p)), nilptr);
             /* update the end of eaL to point to the end of the newly allocated cell. */
             endeaL=&B(*endeaL);
             /* move on to the next argument: */
             p=B(p);

             /* Exercise 27.13:
             a) &B(*endeaL) expanded:
                &B(*endeaL) <=> &B(newloc(seval(A(p)), nilptr))
                <=> &P[(newloc(seval(A(p)), nilptr)].cdr
                <=> &: "The address of..."
                    P[...].cdr: "the CDR pointer of..."
                    (newloc(seval(A(p)), nilptr): "the newly allocated list cell."
             b) At each iteration of the loop, endeaL is put to point to the
                address of the last CDR of the evaluated argument list (of course
                the value of this CDR will be nilptr until another argument gets
                evaluated). Therefore every argument gets evaluated and put into
                the list eaL in proper order.
             */
        }

        /* Set p to be the first node in the evaluated argument list. */
        p=A(eaLp);
        /* Throw away the current supplied argument list by popping the currentin list. */
        cilp=B(cilp);
    }

    /* At this point p points to the first node of the actual argument list. If p EQ nilptr, we have a
       function or special form with no arguments. */

    if (!builtin(ty))
    { /* f is a non-builtin function/special form. Do shallow binding of
         the arguments and evaluate the body of f by calling seval. */
         fa = A(f); /* fa points to the first node of the formal argument list */
         na = 0;    /* na counts the number of arguments */

      /* run through the arguments and place them as the top values of the formal argument atoms in the
         atom table. Push the old value of each formal argument on its binding list. */
        if (type(fa) EQ 8 && fa!=nilptr)
        { /* deal with a function/special form of the form (DEF* f lst-param (...)): */
            t=ptrv(fa);
            Atab[t].bl=newloc(Atab[t].L, Atab[t].bl);
            Atab[t].L=p;
            goto apply;
        }
        else
        {   /* deal with a function/special form of the form (DEF* f (param1 param2 ...) (...)): */
            while (p!=nilptr && dottedpair(type(fa)))
            {
                t=ptrv(A(fa));
                fa=B(fa);
                Atab[t].bl=newloc(Atab[t].L, Atab[t].bl);
                v=A(p);
                if (namedfsf(type(v)))
                    v=Atab[ptrv(v)].L;  /* get the pointer to the actual builtin or userdefined function/special form */
                Atab[t].L=v;
                ++na;
                p=B(p);
            }

            if (p!=nilptr)
                error("too many actual arguments");
            /* The following code would forbid some useful trickery.
            else if(fa!=nilptr) error("too few actual arguments"); */
        }

        /* Now apply the non-builtin special form or function */
apply:  v=seval(B(f));

        /* Next, unbind the parameter variables. */
        /* first, reset fa to point at the beginning of the f's parameter list: */
        fa=A(f);
        if (type(fa) EQ 8 && fa != nilptr)
        { /* handle the unbinding of a (DEF* f lst-param (...)) form: */
            t = ptrv(fa);
            Atab[t].L = A(Atab[t].bl);
            Atab[t].bl = B(Atab[t].bl);
        }
        else
        { /* handle the unbinding of a (DEF* f (param1 param2 ...) (...)) form: */
            while (na-->0)
            {
                t = ptrv(A(fa));
                Atab[t].L = A(Atab[t].bl);
                Atab[t].bl = B(Atab[t].bl);
                fa = B(fa);
            }
        }
    } /* end non-builtins */
    else
    { /* At this point we have a builtin function or special form. f is the pointer value of the
         atom in the atom table for the called function or special form and p is the pointer to
         the argument list. */
        v=nilptr;
        switch (f)
        {
            case 1:     /* CAR */
                    check_arity(p, 1, ar_ef);
                    if (!dottedpair(type(E1))) error("Illegal CAR argument");
                    v=A(E1);
                    break;
            case 2:     /* CDR */
                    check_arity(p, 1, ar_ef);
                    if (!dottedpair(type(E1))) error("Illegal CDR argument");
                    v=B(E1);
                    break;
            case 3:     /* CONS */
                    check_arity(p, 2, ar_ef);
                    if (sexp(type(E1)) && sexp(type(E2))) v=newloc(E1, E2);
                    else error("Illegal CONS arguments");
                    break;

            /* for LAMBDA and SPECIAL, we could check that U1 is either an ordinary atom
               or a list of ordinary atoms. */
            case 4:     /* LAMBDA */
                    check_arity(p, 2, ar_ef);
                    v=tf(newloc(U1,U2));
                    break;
            case 5:     /* SPECIAL */
                    check_arity(p, 2, ar_ef);
                    v=ts(newloc(U1,U2));
                    break;
            case 6:     /* SETQ */
                    check_arity(p, 2, ar_ef);
                    f=U1; if (!(type(f) EQ 8)) error("illegal assignment");
                    assign: v=ptrv(f); endeaL=&AL(v);
                    doit: t=seval(U2);
                    switch (type(t))
                    {
                        case 0:  /* dotted pair */
                        case 8:  /* ordinary atom */
                        case 9:  /* number atom */
                                 *endeaL=t; break;
                        case 10: /* builtin function */
                        case 11: /* builtin special form */
                        case 12: /* user-defined function */
                        case 13: /* user-defined special form */
                                 *endeaL=AL(ptrv(t)); break;
                        case 14: /* unnamed function */
                                 *endeaL=uf(ptrv(t)); break;
                        case 15: /* unnamed special form */
                                 *endeaL=us(ptrv(t)); break;
                    } /* end of type(t) switch cases */
                    tracesw--;
                    v=seval(f);
                    tracesw++;
                    break;

                    /* Ex. 27.15:
                        if the second argument to SETQ is an undefined atom (the atom's type is 1),
                        seval signals an error when we try to evaluate that undefined atom. In that
                        case, the entire evaluation of SETQ is stopped and the control is returned
                        to the top level. Thus, there is no need to check for the case 1. */


            case 7:     /* ATOM */
                    check_arity(p, 1, ar_ef);
                    if ((type(E1)) EQ 8 || (type(E1)) EQ 9)
                        v=tptr;
                    break;
            case 8:     /* NUMBERP */
                    check_arity(p, 1, ar_ef);
                    if ((type(E1)) EQ 9)
                        v=tptr;
                    break;
            case 9:     /* QUOTE */
                    check_arity(p, 1, ar_ef);
                    v = U1;
                    break;
            case 10:     /* LIST */
                    v=p;   /* could this be, under the right circumstances, GCd before
                              its actual use!? Ex.
                                               (LIST (LIST 1 2 3) 4)
                                               if the number table is over 80% full when the
                                               evaluation gets to 4, and 4 isn't already in the
                                               number table, then GC will get called. And because
                                               there is no reference to the newly created
                                               list (LIST 1 2 3), then it gets GCd before
                                               the outer (LIST ... 4) gets built...
                                               How do we eliminate this threat?
                             In case of garbage collecting only when the memory is completely full
                             it doesn't matter since in any case the computation would fail,
                             However if we GC at 80% we should have 20% space left to
                             for special cases like this... One way to fix it would be to add a
                             special flag in garbage collector for special cases when we want to
                             allow the system memory to get more than 80% filled.
                             This special flag could be set whenever a situation like this arises
                             and it would be reset at the top level, once the evaluation of an
                             expression has finished.
                           */
                    break;
            case 11:     /* DO */
                    while (p!=nilptr) {v=A(p); p=B(p);}
                    break;
            case 12:     /* COND */
                    while (p!=nilptr)
                    {
                        t=A(p);
                        if (seval(A(t))!=nilptr)
                        {
                            v=seval(A(B(t)));
                            break;
                        }
                        else
                            p=B(p);
                    }
                    break;
            case 13:     /* PLUS */
                    check_arity(p, 2, ar_ef);
                    v=numatom(Ntab[ptrv(E1)].num + Ntab[ptrv(E2)].num);
                    break;
            case 14:     /* TIMES */
                    check_arity(p, 2, ar_ef);
                    v=numatom(Ntab[ptrv(E1)].num * Ntab[ptrv(E2)].num);
                    break;
            case 15:     /* DIFFERENCE */
                    check_arity(p, 2, ar_ef);
                    v=numatom(Ntab[ptrv(E1)].num - Ntab[ptrv(E2)].num);
                    break;
            case 16:     /* QUOTIENT */
                    check_arity(p, 2, ar_ef);
                    v=numatom(Ntab[ptrv(E1)].num / Ntab[ptrv(E2)].num);
                    break;
            case 17:     /* POWER */
                    check_arity(p, 2, ar_ef);
                    v=numatom(pow(Ntab[ptrv(E1)].num, Ntab[ptrv(E2)].num));
                    break;
            case 18:     /* FLOOR */
                    check_arity(p, 1, ar_ef);
                    v=numatom(floor(Ntab[ptrv(E1)].num));
                    break;
            case 19:     /* MINUS */
                    check_arity(p, 1, ar_ef);
                    v=numatom(-Ntab[ptrv(E1)].num);
                    break;
            case 20:     /* LESSP */
                    check_arity(p, 2, ar_ef);
                    if(Ntab[ptrv(E1)].num < Ntab[ptrv(E2)].num) v=tptr;
                    break;
            case 21:     /* GREATERP */
                    check_arity(p, 2, ar_ef);
                    if(Ntab[ptrv(E1)].num > Ntab[ptrv(E2)].num) v=tptr;
                    break;
            case 22:     /* EVAL */
                    check_arity(p, 1, ar_ef);
                    v=seval(U1);
                    break;
            case 23:     /* EQ */
                    check_arity(p, 2, ar_ef);
                    v=(E1 EQ E2)? tptr: nilptr;
                    break;
            case 24:     /* AND */
                    while (p!=nilptr && seval(A(p))!=nilptr) p=B(p);
                    if (p EQ nilptr) v=tptr;
                    break;
            case 25:     /* OR */
                    while (p!=nilptr && seval(A(p))==nilptr) p=B(p);
                    if (p!=nilptr) v=tptr;
                    break;
            case 26:     /* SUM */
                    for(s=0.0; p!=nilptr; p=B(p))
                    {
                        v=A(p);
                        if (type(v)!= 9) error("SUM application: trying to sum a non-number value");
                        s += Ntab[ptrv(v)].num;
                    }
                    v=numatom(s);
                    break;
            case 27:     /* PRODUCT */
                for(s=1.0; p!=nilptr; p=B(p))
                    {
                        v=A(p);
                        if (type(v)!= 9) error("SUM application: trying to sum a non-number value");
                        s *= Ntab[ptrv(v)].num;
                    }
                    v=numatom(s);
                    break;
            case 28:     /* PUTPLIST */
                    check_arity(p, 2, ar_ef);

                    v=E1;
                    if (type(v)!=8) /* signal an error if A(p) is not an atom */
                        error("PUTPLIST application: the first argument is not an atom");
                    /* TODO: check whether E2 is a proper property list... */
                    Atab[ptrv(v)].plist=E2;
                    break;
            case 29:     /* GETPLIST */
                    check_arity(p, 1, ar_ef);
                    v=E1;
                    if (type(v)!=8) /* signal an error if A(p) is not an atom */
                        error("GETPLIST application: the first argument is not an atom");
                    v=Atab[ptrv(v)].plist;
                    break;
            case 30:     /* READ */
                    ourprint("n>"); prompt=EOS; v=sread();
                    break;
            case 31:     /* PRINT */
                    if (p EQ nilptr) ourprint(" ");
                    else while (p!=nilptr) {swrite(A(p)); ourprint(" "); p=B(p);}
                    break;
            case 32:     /* PRINTCR */
                    if (p EQ nilptr) ourprint("\n");
                    else while (p!=nilptr) {swrite(A(p)); ourprint("\n"); p=B(p);}
                    break;
            case 33:     /* MKATOM */
                    check_arity(p, 2, ar_ef);
                    strcpy(sout, Atab[ptrv(E1)].name); strcat(sout, Atab[ptrv(E2)].name);
                    v=ordatom(sout);
                    break;
            case 34:     /* BODY */
                    check_arity(p, 1, ar_ef);
                    if (unnamedfsf(type(E1))) v=ptrv(E1); /*ptrv(E1) EQ se(ptrv(E1)), which is the pointer value of E1 appended with the type 'dottedpair' (type 0).*/
                    else if (userdefd(type(E1))) v=ptrv(Atab[ptrv(E1)].L);
                    else error("BODY application: Illegal argument");
                    break;
            case 35:     /* RPLACA */
                    check_arity(p, 2, ar_ef);
                    v=E1;
                    if (!dottedpair(type(v))) error("illegal RPLACA argument");
                    A(v) = E2;
                    break;
            case 36:     /* RPLACD */
                    check_arity(p, 2, ar_ef);
                    v=E1;
                    if (!dottedpair(type(v))) error("illegal RPLACD argument");
                    B(v) = E2;
                    break;
            case 37:     /* TSETQ */
                    check_arity(p, 2, ar_ef);
                    f=U1;
                    if (type(f)!=8) error("TSETQ application: first argument given is not an atom");
                    f=ptrv(f);
                    if (Abl(f) EQ nilptr) goto assign;
                    v=Abl(f); while (B(v)!=nilptr) v=B(v);
                    endeaL=&A(v); goto doit;

            case 38:     /* NULL */
                    check_arity(p, 1, ar_ef);
                    if (E1 EQ nilptr) v=tptr;
                    break;
            case 39:     /* SET */
                    check_arity(p, 2, ar_ef);
                    f=seval(U1);
                    if (type(f)!=8) error("SET application: evaluated first argument is not an atom");
                    goto assign;
                    break;
            case 40:    /* EXIT */
                    check_arity(p, 0, ar_ef);
                    exit(0);
                    break;

            default:  error("dryrot: bad builtin case number");
        } /* end of switch cases */
    } /* end of builtins */
    /*pop the eaL list or pop the currentin list, whichever is active */
    if (fct(ty)) eaLp=B(eaLp);
    else cilp=B(cilp);

    Return(v);
}

void check_arity(int32 p, uint8_t ar, int32 f)
/*-------------------------------------------------
Checks whether the given argument list p contains
exactly ar arguments.
We do not check whether p is a dottedpair pointer.
Signals an error if:
  * p does not contain enough arguments
  * p contains too many arguments
-------------------------------------------------*/
{
    char msg[60];
    for (; ar>0 && p!=nilptr; ar--, p=B(p))
    { }
    if (ar EQ 0 && p EQ nilptr) return;
    else
    {   /* for the purposes of check_arity, strcat works perfectly as the string concatenator */
        strcpy(msg, Atab[ptrv(f)].name);
        strcat(msg, " application: ");

        if (ar>0)
            strcat(msg, "not enough arguments");
        else
            strcat(msg, "too many arguments");
        error(msg);
    }
}

int32 newloc(int32 x, int32 y)
/*-------------------------------------------------
Allocates and loads the fields of a new location in the list area. The car field is set to X
and the cdr filed is set to Y. The index of the new location is returned.
-------------------------------------------------*/
{
    int32 j;
    if (fp<0)
    {   /* GC if not enough space: */
        gcmark(x); gcmark(y);
        gc();
        if (fp<0) error("out of space");
    }

    /* fp points to the first free list node.
       For each free list node f, B(f) points to the next free list node: */
    j=fp;       /* allocate the first free list cell for the new values */
    fp=B(j);    /* update the free list pointer to point to the next free list cell */
    A(j)=x;     /* set the CAR of the newly allocated list cell to x */
    B(j)=y;     /* set the CDR of the newly allocated list cell to y */
    numf--;     /* update the number of free list cells */
    return(j);  /* return the pointer to the recently allocated list cell */
}

/* GARBAGE COLLECTOR: */
void gc(void)
/*-------------------------------------------------
  gc is the main garbage collection function that
  takes care of the actual GC process. it uses
  gcmark to mark all the numbers and list nodes that
  can be reached by the atoms established in the
  atom table before it handles the garbage collection
  process.
-------------------------------------------------*/
{
    int32 i, t;
    /* For marking list pointers to be saved, we set the 28th bit in their pointers to 1.
       Thus to see if a list pointer is marked, we check whether its 28th bit is set. */
    #define marked(p)   ((A(p) & 0x08000000)!=0)
    #define unmark(p)   (A(p) &= 0xf7ffffff)

    /* Mark everything reachable from the atom table */
    for (i=0; i<m; i++)
    {
        gcmark(Atab[i].L);      /* mark the atom value */
        gcmark(Atab[i].bl);     /* mark the bind list */
        gcmark(Atab[i].plist);  /* mark the property list */
        /* A list node is reachable if it can be reached from either the
           atom value, the bind-list  or the property list of any atom.
           All other list nodes are left unmarked. */
    }

    /* gcmark has set nmark[i] for every number Ntab[i].num reachable from the atom table
       or from a list-node. Now we garbage collect the number table by re-storing every
       reachable number, and claiming the rest for reuse. */
    for (i=0; i<n; i++)
        nx[i]=-1;

    /* EX 27.8 - we need to also recalculate the amount of numbers in the number table after
       the garbage colleciton has finished. First, reset nnums: */
       nnums = 0;

    for (nf=-1, i=0; i<n; i++)
    {
        if (nmark[i] EQ 0)
        {
            Ntab[i].nlink=nf;
            nf=i;
        }
        else /* restore num[i] */
        {
            t = hashnum(Ntab[i].num);
            while (nx[t] != -1) if ((++t) EQ n) t=0;

            nx[t]=i;
            nmark[i]=0;
            /* EX 27.8 - add one to nnums for each kept number in the number table.
               Another way to do this would be in gcmark, when marking the numbers,
               but then marknum would get a bit bloated... */
            nnums++;
        }

        /* build the new list-node free-space list and return.
           Naturally, both the free-space head pointer and the number of list nodes
           have to be recalculated as well. */
        fp=-1; numf=0;
        for (i=1; i<l; i++)
            if (!marked(i))
            {   /* We do not have to clear the CAR of any free lists, because they are
                   unreachable for as long as they are free. Once they become occupied,
                   the old CAR-value is replaced with a new value. */
                B(i)=fp;
                fp=i;
                numf++;
            }
            else unmark(i);
    }
}

void gcmark(int32 p)
/*-------------------------------------------------
  gcmark marks all those numbers and list nodes,
  that are reachable, from being GCd.
  It handles lists recursively in order to mark
  all its nodes and sublists (both gotos and
  functional recursion is used to achieve this)
-------------------------------------------------*/
{
static int32 s, t;
#define marknode(p)     (A(p) |= 0x08000000)            /* Marks the CAR of a list p */
#define marknum(t,p)    if ((t) EQ 9) nmark[ptrv(p)]=1  /* If p is a number, marks p */
#define listp(t)        ((t) EQ 0 || (t)>11)            /* checks whether t is a list */

start:
    t=type(p);
    if (listp(t))
    {
        p=ptrv(p);
        if (marked(p))
            return;
        /* If p isn't marked yet, we need to mark the list
           node p, and also both its CAR- and CDR-nodes
           recursively. */
        marknode(p);

        /* First handle the CAR of p: */
        t=A(p);
        if (!listp(type(t)))
        { /* If the CAR of p is not a list node, we can just mark
             it if necessary, proceed to handle the CDR of p and
             be done with this part of the original list. */
            marknum(type(t), t);
            p=B(p);
            goto start;
        }

        /* Next handle the CDR of p: */
        s=B(p);
        if (!listp(type(s)))
        { /* If the CDR of p is not a list node, we can just mark
             it if necessary and proceed to handle the CAR that
             was left unhandled: */
            marknum(type(s), s);
            p=t;
            goto start;
        }

        /* if the CAR and CRD of p are both lists, they
           also have to be marked: */
        gcmark(t);  /* marks the CAR */

        p=B(p);
        goto start; /* marks the CDR */
    }
    else marknum(t, p);
}
