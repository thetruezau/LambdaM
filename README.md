# LambdaM
The multiary lambda calculus, here Lambda-M, is an extension of the usual lambda calculus where a term is applied to a list of terms. 

Here we formalize some interesting properties of this system using the Rocq Proof Assistant and also the Autosubst Library.

## How to Run
$coq_makefile -f _CoqProject -o CoqMakefile$ (create CoqMakefile from _CoqProject)
$make -f CoqMakefile$ (compile various files in theories/ to be used as libraries to other files)

The user is supposed to be running Coq in some environment (such as ProofGeneral or CoqIde). 
