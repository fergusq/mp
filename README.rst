======================
 Mini-Pascal Compiler
======================

Introduction
============

This project is a Mini-Pascal Compiler (MPC).
It implements Mini-Pascal Spring 2018 as specified in https://www.cs.helsinki.fi/u/vihavain/k18/Code%20Generation/Mini-Pascal%20Syntax%202018.pdf.
In order to make implementing the language easier, the compiler actually implements a superset of the given language.
The superset includes local functions and other features.
The compiler will output a warning if the input program uses them.

The main components of the compiler are the scanner, the parser, the analyser and the code generator.
The following chapters will describe these components.

Lexical grammar
===============

::

	identifier = ([:alpha:]|_)+
	long_operator = ([:=<>]+|)
	integer = [0-9]+
	real = [0-9]+\.[0-9]+(e[0-9]+)?
	string = "(\\.|.)*"
	whitespace = \s+

	# all characters that do not match the above classes are short operators
	short_operator = .

The scanner scans tokens by matching the begining of the stream with the rules above, in that order.
For simplicitys sake, keywords have the same token class as identifiers.

Strings can contain escape codes that have form ``\.``, where ``.`` is any token.
Three escape codes have a special meaning: ``\\`` becomes ``\``, ``\"`` becomes ``"`` and ``\n`` becomes a newline.
All other escape codes become the character after the backslash.

Syntax and AST
==============

As the MPC actually implements a superset of Mini-Pascal Spring 2018, the syntax is different from the specification.
Specifically:

* There is no distinction between the top level block, function bodies or local blocks. It is possible to define variables and functions in all of them, and use other statements.
* Function body can be any statement, not just a block.
* Assignment is an expression, not a statement.
* Arrays can contain arrays. This feature is not fully supported. For example, it is not possible to index a variable twice, instead a temporary variable must be used.

::

	PROGRAM ::= "program" IDENTIFIER ";" BLOCK "."
	
	BLOCK ::= STATEMENT ";"? | STATEMENT ";" BLOCK
	
	STATEMENT ::= DEFINITION
	            | "begin" BLOCK "end"
	            | "return" EXPRESSION?
	            | "if" EXPRESSION "then" STATEMENT ("else" STATEMENT)?
	            | "while" EXPRESSION "do" STATEMENT
	            | EXPRESSION
	
	DEFINITION ::= "procedure" IDENTIFIER "(" (PARAMETER ("," PARAMETER)*)? ")" ";" STATEMENT
	             | "function" IDENTIFIER "(" (PARAMETER ("," PARAMETER)*)? ")" ":" TYPE ";" STATEMENT
	             | "var" IDENTIFIER ":" TYPE
	
	PARAMETER ::= "var"? IDENTIFIER ":" TYPE
	
	TYPE ::= "integer" | "real" | "string" | "array" ("[" INTEGER-TOKEN "]")? "of" TYPE
	
	EXPRESSION ::= SIMPLE-EXPR (RELATIONAL-OPERATOR SIMPLE-EXPR)*
	SIMPLE-EXPR ::= TERM (ADDITION-OPERATOR TERM)*
	TERM ::= FACTOR (MULTIPLICATION-OPERATOR FACTOR)*
	FACTOR ::= PRIMARY-EXPR ("." "size")?
	PRIMARY-EXPR ::= "(" EXPRESSION ")"
	               | UNARY-OPERATOR FACTOR
	               | IDENTIFIER ("[" EXPRESSION "]" | "(" (EXPRESSION ("," EXPRESSION)*)? ")")? (":=" EXPRESSION)?
	               | INTEGER-TOKEN
	               | REAL-TOKEN
	               | STRING-TOKEN
	
	RELATIONAL-OPERATOR ::= "=" | "<>" | "<" | ">" | "<=" | ">="
	ADDITION-OPERATOR ::= "+" | "-" | "or"
	MULTIPLICATION-OPERATOR ::= "*" | "/" | "%" | "and"
	UNARY-OPERATOR ::= "+" | "-" | "not"

The parser uses lookahead. It does not backtrack and parses in linear time.

During the parsing an abstract syntax tree (AST) is generated.
It is made of Rust enums. It is possible to think an enum as a C union.
It is a class that can have several different forms, each having different fields.

Below are simplified version of the enums used in the compiler. (For exact version, see line 286 of main.rs).

::

	Type { Boolean, Integer, Real, String, Array(Type, int), Void, Error }
	Definition { Function(String, Parameter[], Type, Statement), Variable(Parameter) }
	Parameter { String name, Type type, boolean is_ref }
	Statement { Definition(Definition), SimpleReturn, Return(Expression),
	            IfElse(Expression, Statement, Statement), While(Expression, Statement),
	            Block(Statement[]), Expression(Expression), Nop }
	Expression { Integer(int), Real(float), String(String), Assign(Expression, Expression),
                     BiOperator(BinaryOperator, Expression, Expression), UnOperator(UnaryOperator, Expression),
                     Call(String, Expression[]), Index(String, Expression), Variable(String, boolean) }
        BinaryOperator { Eq, Neq, Lt, Leq, Gt, Geq, Add, Sub, Mul, Div, Mod, And, Or }
        UnaryOperator { Plus, Minus, Not, Size }

``Parameter`` is not an enum but a struct. All enums have a list of forms (constructors), which contain a name and a list of types they contain.

Things to note:

* There is no separate If and If-Else. An If without an Else is an If-Else where the Else block is a nop.
* Assignment is an expression, and its left side is also an expression. The parser ensures that the left side is either a variable or an array subscript.
* There are both ``SimpleReturn`` (for procedures) and ``Return`` (for functions).
* Variables have a boolean field that is initially false and is changed to true during semantic analysis if the variable is a reference (var parameter).

Semantics
=========

Code generation
===============

Errors
======
