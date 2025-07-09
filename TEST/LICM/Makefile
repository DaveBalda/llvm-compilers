.PHONY: all clean

all: Assignment3.ll

LICM_O0.ll: LICM.c
	clang -O0 -Rpass=".*" -Xclang -disable-O0-optnone -emit-llvm -S -c $< -o $@

LICM_m2r.ll: LICM_O0.ll
	opt -passes="mem2reg" -S $< -o $@

Assignment3.ll: LICM_m2r.ll
	opt -passes="loop-walk" -S $< -o $@

clean:
	rm -f LICM_O0.ll LICM_m2r.ll Assignment3.ll
