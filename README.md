# rucc
rucc is a small C compiler written in Rust.

## Requirements
- Rust
- gcc

## Useage
```
rucc [ -o <path> ] <file>
```

## Test
```
make test
```

## Features
- Data types
    - Primitive
        - [x] char
        - [x] short
        - [x] int
        - [x] long
        - [x] long long
        - [ ] signed integer
        - [ ] float
        - [ ] double
        - [ ] long double
        - [ ] complex number
    - [x] enum
    - [x] union
    - [x] struct
    - [x] array
    - [x] pointer
    - [x] incomplete type
    - Type qualifiers
        - [ ] const
        - [ ] volatile
    - Storage class specifiers
        - [ ] auto
        - [ ] extern
        - [ ] register
        - [ ] static
- Expressions and Operators
    - [x] Assignment Operators (=, +=, -=, *=, /=, %=, <<=, >>=, &=, ^=, |=)
    - [x] Incrementing and Decrementing (++, --)
    - [x] Arithmetic Operators (+, -, *, %)
    - [x] Comparison Operators (==, !=, <, >, <=, >=)
    - [x] Logical Operators (&&, ||, !)
    - [x] Bit Shifting (<<, >>)
    - [x] Bitwise Logical Operators (&, |, ^, ~)
    - [x] Pointer Operators (*ptr, &var)
    - [x] sizeof
    - [x] Type Casts
    - [x] Array Subscripts
    - [x] Function Calls as Expressions
    - [x] The Comma Operator
    - [x] Member Access Expressions
    - [x] Conditional Expressions (?:)
    - [x] Statements and Declarations in Expressions
- Statements
    - [x] Labels
    - [x] The if Statements
    - [x] The switch Statements
    - [x] The while Statements
    - [ ] The do Statements
    - [x] The for Statements
    - [x] Blocks
    - [x] The Null Statements
    - [x] The goto Statements
    - [x] The break Statements
    - [x] The continue Statements
    - [x] The return Statements
    - [x] The goto Statements
    - [x] The typedef Statements
- Functions
    - [x] Function Declarations
    - [x] Function Definitions
    - [x] Calling Declarations
    - [x] Function Parameters (up to 6 arguments)
    - [ ] Variable Length Parameter Lists
    - [ ] Calling Functions Through Function Pointers
    - [x] Recursive Functions
    - [ ] Static Functions
- Program Structure and Scope
    - [x] Scope
- Ohter
    - [ ] Preprocessor directives

## References
Implementation
- [rui314/chibicc](https://github.com/rui314/chibicc)

Document
- [Intel® 64 and IA-32 Architectures Software Developer Manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
- [The GNU C Reference Manual](https://www.gnu.org/software/gnu-c-manual/)
- [Cリファレンスマニュアル 第5版](https://tatsu-zine.com/books/c-reference-manual-5ed)
- [エキスパートCプログラミング―知られざるCの深層](https://www.kadokawa.co.jp/product/200600002640/)

Other
- [Compiler Explorer](https://godbolt.org)