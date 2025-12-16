# BSD BASIC Interpreter

A tiny BASIC interpreter targeting CBM BASIC v2 style programs, designed for portability including legacy systems like PDP-11 running 2.11BSD.

## Building

```sh
cc -o bsdbasic bsdbasic.c -lm
```

On modern systems with GCC:
```sh
gcc -o bsdbasic bsdbasic.c -lm -Wall
```

## Usage

```sh
./bsdbasic program.bas
```

## Language Reference

### Program Structure

Programs consist of numbered lines. Lines are executed in numeric order unless control flow statements redirect execution.

```basic
10 PRINT "HELLO"
20 GOTO 10
```

Multiple statements can appear on one line separated by colons:

```basic
10 X = 1 : Y = 2 : PRINT X + Y
```

### Variables

Variable names are one or two characters. String variables end with `$`.

```basic
A = 42
X1 = 3.14
N$ = "HELLO"
```

Arrays are created implicitly or with DIM (0-indexed, default size 11):

```basic
10 DIM A(100)
20 A(0) = 1
30 A(1) = 2
```

### Statements

| Statement | Description |
|-----------|-------------|
| `PRINT` | Output values. Use `;` for no newline, `,` for tab zones |
| `INPUT` | Read user input. Optional prompt: `INPUT "NAME";N$` |
| `LET` | Assignment (optional keyword): `LET X = 5` or just `X = 5` |
| `IF...THEN` | Conditional. THEN can be followed by line number or statements |
| `GOTO` | Jump to line number |
| `GOSUB` | Call subroutine at line number |
| `RETURN` | Return from subroutine |
| `FOR...TO...STEP` | Loop with counter |
| `NEXT` | End of FOR loop |
| `DIM` | Declare array size |
| `REM` or `'` | Comment |
| `END` | Stop execution |
| `STOP` | Stop execution |
| `SLEEP` | Pause for ticks (1/60 second units) |

### Operators

**Arithmetic:** `+`, `-`, `*`, `/`, `^` (power)

**Comparison:** `=`, `<`, `>`, `<=`, `>=`, `<>` (not equal)

**Logical:** `AND`, `OR`, `NOT()`

Comparisons return -1 for true, 0 for false (CBM BASIC compatible).

```basic
10 IF (X > 0) AND (Y > 0) THEN PRINT "BOTH POSITIVE"
20 IF (A = 1) OR (B = 1) THEN PRINT "AT LEAST ONE"
30 PRINT NOT(0)      : REM prints -1
40 PRINT 5 AND 3     : REM prints 1 (bitwise)
50 PRINT 5 OR 2      : REM prints 7 (bitwise)
```

### Math Functions

| Function | Description |
|----------|-------------|
| `SIN(x)` | Sine |
| `COS(x)` | Cosine |
| `TAN(x)` | Tangent |
| `ATN(x)` | Arctangent |
| `ABS(x)` | Absolute value |
| `INT(x)` | Floor (round down) |
| `SQR(x)` | Square root |
| `SGN(x)` | Sign (-1, 0, or 1) |
| `EXP(x)` | e^x |
| `LOG(x)` | Natural logarithm |
| `RND(x)` | Random number 0-1. Negative x seeds the generator |

### String Functions

| Function | Description |
|----------|-------------|
| `LEN(s$)` | Length of string |
| `LEFT$(s$, n)` | Leftmost n characters |
| `RIGHT$(s$, n)` | Rightmost n characters |
| `MID$(s$, start [, len])` | Substring (1-indexed) |
| `INSTR(s$, find$)` | Position of substring (0 if not found) |
| `ASC(s$)` | ASCII code of first character |
| `CHR$(n)` | Character from ASCII code |
| `VAL(s$)` | Convert string to number |
| `STR$(n)` | Convert number to string |

### Utility Functions

| Function | Description |
|----------|-------------|
| `TAB(n)` | Move print position to column n |
| `POS(x)` | Current print column (1-indexed) |
| `FRE(x)` | Free memory (returns 32768) |
| `NOT(x)` | Bitwise NOT |

### Examples

**Hello World:**
```basic
10 PRINT "HELLO, WORLD!"
```

**Count to 10:**
```basic
10 FOR I = 1 TO 10
20 PRINT I
30 NEXT I
```

**Fibonacci:**
```basic
10 A = 0 : B = 1
20 FOR I = 1 TO 20
30 PRINT A;
40 C = A + B
50 A = B : B = C
60 NEXT I
70 PRINT
```

**String manipulation:**
```basic
10 A$ = "HELLO WORLD"
20 PRINT LEFT$(A$, 5)       : REM "HELLO"
30 PRINT RIGHT$(A$, 5)      : REM "WORLD"
40 PRINT MID$(A$, 7, 5)     : REM "WORLD"
50 PRINT INSTR(A$, "O")     : REM 5
```

**Subroutines:**
```basic
10 X = 5 : GOSUB 100
20 X = 10 : GOSUB 100
30 END
100 PRINT "X IS"; X
110 RETURN
```

**Conditional logic:**
```basic
10 INPUT "ENTER A NUMBER"; N
20 IF N < 0 THEN PRINT "NEGATIVE" : GOTO 50
30 IF N = 0 THEN PRINT "ZERO" : GOTO 50
40 PRINT "POSITIVE"
50 END
```

## Limits

| Resource | Limit |
|----------|-------|
| Program lines | 1024 |
| Line length | 256 characters |
| Variables | 128 |
| String length | 256 characters |
| GOSUB depth | 64 |
| FOR loop depth | 32 |
| Default array size | 11 elements (0-10) |

## Portability Notes

The code is written in K&R-compatible C for maximum portability. It avoids modern C features and should compile on vintage Unix systems including 2.11BSD on PDP-11.

Sleep functionality uses `usleep()` where available, falling back to `select()` on older systems.

## License

GNU General Public License v2 or later.

Copyright (C) 2024 Davepl with various AI assists.
