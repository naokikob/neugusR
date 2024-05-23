This repository contains a tool is for NN-guided synthesis of recursive list predicates.
The technical background is found in the following paper.
```
Naoki Kobayashi, Minchao Wu,
"Neural Network-Guided Synthesis of Recursive List Functions", Proceedings of TACAS 2023, pp.227-245, 2023
```

# How to install the formula synthesizer
run
```
dune build learnMp.exe
```
You need to install dune and ocaml-torch (by running 'opam install torch') in advance.

# How to run the formula synthesizer
run
```
learn.sh <options> <datafile>
```
## options
* -epochs <number> : the number of epochs (default: 20000)
* -nodes <number> : the number of hidden nodes in the first (hidden) layer (default: 4)
* -nodes2 <number> : the number of hidden nodes in the second layer (default: 4)
* -rate: learning rate

### Example:
```
./learn.sh -nodes2 8 -rate 0.01 -epochs 10000 data/small/sorted0.dat
```

