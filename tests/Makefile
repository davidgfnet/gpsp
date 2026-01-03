
X86PFX=
ARMV8PFX=/opt/buildroot-armv8el-uclibc/bin/aarch64-buildroot-linux-uclibc-
MIPS32PFX=/opt/buildroot-mipsel32-o32-uclibc/bin/mipsel-buildroot-linux-uclibc-

COVERAGE_FLAGS=-ftest-coverage -fprofile-arcs

all:
	g++ -o arm64gen.elf arm64gen.c -ggdb -I../arm/ -I.. $(COVERAGE_FLAGS)
	./arm64gen.elf > bytecode.bin
	lcov -c -d . -o arm64gen.info
	$(ARMV8PFX)as -o bytecoderef.o arm64gen.S
	$(ARMV8PFX)objcopy -O binary bytecoderef.o bytecoderef.bin
	@ cmp bytecoderef.bin bytecode.bin || echo "Bytecode mismatch"
	@ cmp bytecoderef.bin bytecode.bin && echo "Test passed!"
	
	g++ -o x86gen.elf x86gen.c -ggdb -I../x86/ -I.. $(COVERAGE_FLAGS)
	./x86gen.elf > bytecode.bin
	lcov -c -d . -o x86gen.info
	$(X86PFX)as -o bytecoderef.o x86gen.S
	$(X86PFX)objcopy -j .text -O binary bytecoderef.o bytecoderef.bin
	@ cmp bytecoderef.bin bytecode.bin || echo "Bytecode mismatch"
	@ cmp bytecoderef.bin bytecode.bin && echo "Test passed!"

	#gcc -o mipsgen mipsgen.c -ggdb -I../mips/
	#./mipsgen > bytecode.bin
	#$(MIPS32PFX)-as -EL -o bytecoderef.o mipsgen.S
	#$(MIPS32PFX)-objcopy -j .text -O binary bytecoderef.o bytecoderef.bin
	#@ cmp bytecoderef.bin bytecode.bin || echo "Bytecode mismatch"
	#@ cmp bytecoderef.bin bytecode.bin && echo "Test passed!"
	lcov -a arm64gen.info -a x86gen.info -o total.info
	rm -rf coverage/
	genhtml -o coverage/ total.info

clean:
	rm -rf *.info *.bin *.elf *.o *.gcda *.gcno coverage/

