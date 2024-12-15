
slows: implementation of SPDZ maliciously secure mpc


./slows -h <host file> -c <circ file> -p <preprocessed file>

host file: contains connections (every user needs to be connected to every other user)
circuit: an evaluation circuit (see tests for examples)
preprocess: a file containing beaver triples (doing the preprocessing step requires FHE so uh yeah i dont know enough about FHE)
