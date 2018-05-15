======================
 Mini-Pascal Compiler
======================

Introduction
============

This project is a Mini-Pascal Compiler (MPC).

Lexical grammar
===============

    identifier = ([:alpha:]|_)+
    long_operator = ([:=<>]+|)
    integer = [0-9]+
    floating = [0-9]+\.[0-9]+(e[0-9]+)?
    string = "(\\.|.)*"
    whitespace = \s+
    
    # all characters that do not match the above classes are short operators
    short_operator = .

MPC scans tokens by matching the begining of the stream with the rules above, in that order.
For simplicitys sake, keywords have the same token class as identifiers.

Syntax
======

Implementation decisions
========================

Code generation
===============

Errors
======
