# LambdaM

The multiary lambda calculus is an extension of the ordinary lambda calculus where an applicative term has a list of terms as arguments.

## Meta

- Author(s):
  - Miguel Alves
- Compatible Coq versions: 8.14 or later
- Additional dependencies: rocq-community/autosubst (https://github.com/rocq-community/autosubst/)

## Documentation

### Workflow

The basic workflow for running our scripts is as follows:

1. The user creates a `CoqMakefile` file from the `_CoqProject` file by runnig
   `coq_makefile -f _CoqProject -o CoqMakefile`
2. The user compiles the various scripts in the `theories/` directory by running
   `make -f CoqMakefile` 
3. The user runs any script from the `theories/` directory using any Coq/Rocq environment
4. Optionally, the user may clean the `theories/` directory by running 
   `make clean -f CoqMakefile` 

### Files

The library consists of the following files:

- [LambdaM.v](theories/LambdaM.v)  
  The multiary lambda calculus definitions.
