.PHONY: all clean

all: LoopGuarded.ll LoopUnguarded.ll MultipleGuarded.ll MultipleUnguarded.ll

LoopGuarded_O0.ll: LoopGuarded.c
	clang -O0 -Rpass=".*" -Xclang -disable-O0-optnone -emit-llvm -S -c $< -o $@

LoopGuarded_m2r.ll: LoopGuarded_O0.ll
	opt -passes="mem2reg" -S $< -o $@

LoopGuarded.ll: LoopGuarded_m2r.ll
	opt -passes="loop-fusion" -S $< -o $@

LoopUnguarded_O0.ll: LoopUnguarded.c
	clang -O0 -Rpass=".*" -Xclang -disable-O0-optnone -emit-llvm -S -c $< -o $@

LoopUnguarded_m2r.ll: LoopUnguarded_O0.ll
	opt -passes="mem2reg" -S $< -o $@

LoopUnguarded.ll: LoopUnguarded_m2r.ll
	opt -passes="loop-fusion" -S $< -o $@

MultipleGuarded_O0.ll: MultipleGuarded.c
	clang -O0 -Rpass=".*" -Xclang -disable-O0-optnone -emit-llvm -S -c $< -o $@

MultipleGuarded_m2r.ll: MultipleGuarded_O0.ll
	opt -passes="mem2reg" -S $< -o $@

MultipleGuarded.ll: MultipleGuarded_m2r.ll
	opt -passes="loop-fusion" -S $< -o $@

MultipleUnguarded_O0.ll: MultipleUnguarded.c
	clang -O0 -Rpass=".*" -Xclang -disable-O0-optnone -emit-llvm -S -c $< -o $@

MultipleUnguarded_m2r.ll: MultipleUnguarded_O0.ll
	opt -passes="mem2reg" -S $< -o $@

MultipleUnguarded.ll: MultipleUnguarded_m2r.ll
	opt -passes="loop-fusion" -S $< -o $@

clean:
	rm -f *.ll