# Balanced Parentheses Frama-c 

Frama-C code which proves the total correctness of a program which verifies if parentheses are balanced.<br><br>
University of Parma - Computer Science <br>
A.A. 2014/2015


Intuitively, a string of parentheses is balanced if each left parenthesis has a matching right parenthesis and the matched pairs are well nested. The set PAREN of balanced strings of parentheses [ ] is the prototypical context-free language and plays a pivotal role in the theory of CFLs.

* ACSL Specification

You can find the specifications of functions in the files. <br>
They can be verified using Frama-C with Jessie plugin.
```
  frama-c-gui parentesi.c
```

